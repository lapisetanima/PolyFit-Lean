import PolyFit.Search

/-!
# The fine and ultra-fine fits: local search for any `n ≥ 2`

Starting from a polygon (normally the best rough fit), two searches alternate:

* **Fine:** pattern search with a move set that grows linearly in `n`. At step size
  `s` the candidates are: for each edge (present or missing), moving its two endpoints
  by `s` times an offset in `{-1, 0, 1}²` each (80 moves per edge, which include moving
  just one of them); and, for `n ≥ 3`, translating the whole polygon by `s` times an
  offset (8 moves). The best candidate is taken if it strictly lowers `F²`; otherwise
  `s` is halved, down to 1.
* **Ultra-fine:** at step 1, every combination of offsets for all `n` vertices at once,
  the whole cube `{-1, 0, 1}^{2n}` (`9ⁿ - 1` candidates). If one is better, the best is
  taken and the fine search runs again.

When the ultra-fine search finds no better candidate, the result is **certified**: no
polygon in the unit cube around it has a lower `F²`. For `n = 2` the fine moves already
are the whole cube, so a converged segment search is certified without the ultra-fine
step. The ultra-fine step is skipped for `n > ultraMax` (default 7), and then the result
is not certified. Candidates with a zero-length edge are scored like any other (with
`L² := 1`); the caller checks the final polygon.

All moves share one fuel budget (accepted moves); running out means not certified.

Speed:
* An edge's pieces of `F²` depend only on its endpoints, so a candidate reuses the
  current polygon's pieces for every edge it does not change.
* Only a candidate strictly better than the best so far can be chosen, so scoring stops
  as soon as one is certain not to be (`objectiveBelow`).
* In the ultra-fine step each edge has only `9 × 9 = 81` versions, which are computed
  once, so each of the `9ⁿ - 1` candidates is assembled from table lookups.
-/

namespace PolyFit

/-- The pieces of `F²` for each edge of `q` (indexed by edge number; edges not in
`present` get a dummy value and are never used). -/
def edgeCache (pts : Array Pt) (q : Array Pt) (present : List Nat) : Array EdgeTerms :=
  let n := q.size
  (Array.range n).map fun e => if present.contains e then edgeTerms pts q[e]! q[(e + 1) % n]! else default

/-- The fine moves at step `s`: each candidate polygon with the vertices it changes.
For `n = 2` these are exactly the 80 moves of the segment search, in the same order. -/
def fineMoves (s : Int) (q : Array Pt) : List (Array Pt × List Nat) :=
  let n := q.size
  let edgeMoves := (List.range (if n == 2 then 1 else n)).flatMap fun e =>
    let a := e
    let b := (e + 1) % n
    unitOffsets.toList.flatMap fun d₀ =>
      (unitOffsets.toList.filter (d₀ != ⟨0, 0⟩ || · != ⟨0, 0⟩)).map fun d₁ =>
        ((q.set! a (q[a]! + d₀.scale s)).set! b (q[b]! + d₁.scale s), [a, b])
  let translations := if n ≤ 2 then [] else
    (unitOffsets.toList.filter (· != ⟨0, 0⟩)).map fun d => (q.map (· + d.scale s), List.range n)
  edgeMoves ++ translations

/-- The best fine move from `q` at step `s` that is strictly better than `f` (the first,
on ties), or `none`. -/
def bestFineMove (pts : Array Pt) (diam2 : Nat) (present : List Nat) (q : Array Pt) (f : Rat)
    (s : Int) : Option (Array Pt × Rat) :=
  let n := q.size
  let cache := edgeCache pts q present
  (fineMoves s q).foldl (init := none) fun best (cand, changed) =>
    let edges := present.toArray.map fun e =>
      if changed.contains e || changed.contains ((e + 1) % n) then edgeTerms pts cand[e]! cand[(e + 1) % n]!
      else cache[e]!
    let bound := (best.map (·.2)).getD f
    match objectiveBelow pts.size diam2 edges (some bound) with
    | some f' => some (cand, f')
    | none => best

/-- The fine search from `q` (with `F² = f`), using at most `fuel` moves. Returns the
polygon, its `F²`, the moves used, and whether it converged (no fine move of size 1
improves) rather than running out of fuel. Each round either accepts a move or halves
`s`, and `s` can be halved at most 64 times, so `fuel + 65` rounds suffice. -/
def fineSearch (pts : Array Pt) (diam2 : Nat) (present : List Nat) (q₀ : Array Pt) (f₀ : Rat)
    (fuel : Nat) : Array Pt × Rat × Nat × Bool := Id.run do
  let mut q := q₀
  let mut f := f₀
  let mut s := initialStep diam2
  let mut moves := 0
  let mut converged := false
  for _ in [0:fuel + 65] do
    match bestFineMove pts diam2 present q f s with
    | some (q', f') =>
      if moves == fuel then break
      q := q'
      f := f'
      moves := moves + 1
    | none =>
      if s > 1 then s := s / 2
      else
        converged := true
        break
  return (q, f, moves, converged)

/-- `⌊c · x⌋` and `⌈c · x⌉` for `x ≥ 0`, as natural numbers. -/
def floorScaled (x : Rat) (c : Nat) : Nat := (x.num * c / x.den).toNat
def ceilScaled (x : Rat) (c : Nat) : Nat := ((x.num * c + x.den - 1) / x.den).toNat

/-- The resolution of the whole-number lower bounds used to skip candidates. -/
def lbScale : Nat := 1024

/-- One version of an edge in the ultra-fine table: its exact pieces of `F²`, and
whole-number lower bounds for them. With `S = lbScale · 2|P| diam(P)²`, so that
`S · F² = lbScale · Σ_p d₁(p, Q)² + lbScale · 2|P| diam(P)² · Σ D₂² / (2m)`:
`pointLB[p] ≤ lbScale · d₁(p, ℓ)²` and `d2LB ≤ lbScale · 2|P| diam(P)² · D₂(ℓ)² / (2m)`. -/
structure TableEdge where
  terms : EdgeTerms
  pointLB : Array Nat
  d2LB : Nat
deriving Inhabited

/-- Whether the whole-number lower bound of `S · F²` for these edges reaches `limit`
(then the candidate's `F²` is certainly `≥ bound` when `limit = ⌈S · bound⌉`). -/
def lowerBoundReaches (numPts : Nat) (edges : Array TableEdge) (limit : Nat) : Bool := Id.run do
  let mut total := edges.foldl (init := 0) (· + ·.d2LB)
  if total ≥ limit then return true
  for p in [0:numPts] do
    let mut nearest := edges[0]!.pointLB[p]!
    for e in edges do
      if e.pointLB[p]! < nearest then nearest := e.pointLB[p]!
    total := total + nearest
    if total ≥ limit then return true
  return false

/-- The best polygon in the unit cube around `q` (all `n` vertices moved by offsets in
`{-1, 0, 1}²` at once, not all zero) that is strictly better than `f`, or `none`.

Each candidate is first checked with whole-number lower bounds; only if those cannot
rule it out is its exact `F²` computed. Since a lower bound never exceeds the true
value, a candidate ruled out is truly not better, so the result is the same as scoring
every candidate exactly. -/
def bestCubeMove (pts : Array Pt) (diam2 : Nat) (present : List Nat) (q : Array Pt) (f : Rat) :
    Option (Array Pt × Rat) := Id.run do
  let n := q.size
  let m := present.length
  let numPts := pts.size
  let weight : Rat := (2 * numPts * diam2 : Nat)          -- 2|P| diam(P)²
  let S : Rat := (lbScale : Rat) * weight
  -- table[e][9 * a + b]: edge `e` with its endpoints moved by offsets number `a` and `b`.
  let table := (Array.range n).map fun e =>
    if present.contains e then
      (Array.range 81).map fun ab =>
        let t := edgeTerms pts (q[e]! + unitOffsets[ab / 9]!) (q[(e + 1) % n]! + unitOffsets[ab % 9]!)
        ⟨t, t.distSqs.map (floorScaled · lbScale), floorScaled (t.d2 * weight / (2 * m : Nat)) lbScale⟩
    else #[]
  let stay := 4    -- unitOffsets[4] is (0, 0): the vertex does not move
  let mut best : Option (Array Pt × Rat) := none
  let mut limit := ceilScaled (f * S) 1
  -- `digits` counts through all 9ⁿ offset combinations like an odometer in base 9.
  let mut digits := Array.replicate n 0
  for _ in [0:9 ^ n] do
    if !digits.all (· == stay) then
      let edges := present.toArray.map fun e => table[e]![9 * digits[e]! + digits[(e + 1) % n]!]!
      if !lowerBoundReaches numPts edges limit then
        let bound := (best.map (·.2)).getD f
        if let some f' := objectiveBelow numPts diam2 (edges.map (·.terms)) (some bound) then
          best := some ((Array.range n).map (fun v => q[v]! + unitOffsets[digits[v]!]!), f')
          limit := ceilScaled (f' * S) 1
    -- advance the odometer
    let mut v := 0
    for _ in [0:n] do
      if digits[v]! < 8 then
        digits := digits.set! v (digits[v]! + 1)
        break
      digits := digits.set! v 0
      v := v + 1
  return best

/-- The result of the fine and ultra-fine searches. -/
structure Polished where
  vertices : Array Pt
  objectiveSq : Rat
  moves : Nat
  certified : Bool

/-- Fine search, then ultra-fine certification, repeated until certified (or the fuel
runs out, or `n > ultraMax`). Each round of the outer loop either returns or uses at
least one unit of fuel, so `fuel + 1` rounds suffice. -/
def polish (pts : Array Pt) (missing : List Nat) (start : Array Pt) (fuel : Nat := 1000)
    (ultraMax : Nat := 7) : Polished := Id.run do
  let n := start.size
  let diam2 := diamSq pts
  let present := presentEdges n missing
  let mut q := start
  let mut f := objectivePolygon pts diam2 start missing
  let mut used := 0
  for _ in [0:fuel + 1] do
    let (q', f', m, converged) := fineSearch pts diam2 present q f (fuel - used)
    q := q'
    f := f'
    used := used + m
    if !converged then return ⟨q, f, used, false⟩
    if n == 2 then return ⟨q, f, used, true⟩      -- the fine moves are the whole cube
    if n > ultraMax then return ⟨q, f, used, false⟩
    match bestCubeMove pts diam2 present q f with
    | none => return ⟨q, f, used, true⟩
    | some (q', f') =>
      if used ≥ fuel then return ⟨q, f, used, false⟩
      q := q'
      f := f'
      used := used + 1
  return ⟨q, f, used, false⟩

end PolyFit
