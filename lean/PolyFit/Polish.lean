import PolyFit.Search

/-!
# The fine and ultra-fine fits: local search for any `n ≥ 2`

Starting from a polygon (normally the best rough fit), two searches alternate. Both
only move vertices by offsets in `{-1, 0, 1}²`, so they descend within the basin the
rough fit chose rather than jumping to another one; choosing the basin is the rough
fit's job.

* **Fine:** best-improvement local search with a move set that grows linearly in `n`:
  for each edge (present or missing), moving its two endpoints by an offset each (80
  moves per edge, which include moving just one of them); and, for `n ≥ 3`, translating
  the whole polygon by an offset (8 moves). The best candidate is taken while it
  strictly lowers `F²`.
* **Ultra-fine:** every combination of offsets for all `n` vertices at once, the whole
  cube `{-1, 0, 1}^{2n}` (`9ⁿ - 1` candidates). If one is better, the best is taken and
  the fine search runs again.

When the ultra-fine search finds no better candidate, the result is **certified**: no
polygon in the unit cube around it has a lower `F²`. For `n = 2` the fine moves already
are the whole cube, so a converged fine search is certified without the ultra-fine
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

/-- The fine moves: each candidate polygon with the vertices it changes. For `n = 2`
these are the 80 ways of moving the two endpoints (not both by `(0, 0)`). -/
def fineMoves (q : Array Pt) : List (Array Pt × List Nat) :=
  let n := q.size
  let edgeMoves := (List.range (if n == 2 then 1 else n)).flatMap fun e =>
    let a := e
    let b := (e + 1) % n
    unitOffsets.toList.flatMap fun d₀ =>
      (unitOffsets.toList.filter (d₀ != ⟨0, 0⟩ || · != ⟨0, 0⟩)).map fun d₁ =>
        ((q.set! a (q[a]! + d₀)).set! b (q[b]! + d₁), [a, b])
  let translations := if n ≤ 2 then [] else
    (unitOffsets.toList.filter (· != ⟨0, 0⟩)).map fun d => (q.map (· + d), List.range n)
  edgeMoves ++ translations

/-- The best fine move from `q` that is strictly better than `f` (the first, on ties),
or `none`. -/
def bestFineMove (pts : Array Pt) (diam2 : Nat) (present : List Nat) (q : Array Pt) (f : Rat) :
    Option (Array Pt × Rat) :=
  let n := q.size
  let cache := edgeCache pts q present
  (fineMoves q).foldl (init := none) fun best (cand, changed) =>
    let edges := present.toArray.map fun e =>
      if changed.contains e || changed.contains ((e + 1) % n) then edgeTerms pts cand[e]! cand[(e + 1) % n]!
      else cache[e]!
    let bound := (best.map (·.2)).getD f
    match objectiveBelow pts.size diam2 edges (some bound) with
    | some f' => some (cand, f')
    | none => best

/-- The fine search from `q₀` (with `F² = f₀`), accepting at most `fuel` moves. Returns
the polygon, its `F²`, the moves used, and whether it converged (no fine move improves)
rather than running out of fuel. -/
def fineSearch (pts : Array Pt) (diam2 : Nat) (present : List Nat) (q₀ : Array Pt) (f₀ : Rat)
    (fuel : Nat) : Array Pt × Rat × Nat × Bool :=
  go fuel q₀ f₀
where
  /-- The search from `q` with `F² = f`, when `left` more moves may be accepted (so
  `fuel - left` have been). -/
  go (left : Nat) (q : Array Pt) (f : Rat) : Array Pt × Rat × Nat × Bool :=
    match bestFineMove pts diam2 present q f with
    | none => (q, f, fuel - left, true)                         -- no move helps
    | some (q', f') =>
      match left with
      | 0 => (q, f, fuel, false)                                -- out of fuel
      | left + 1 => go left q' f'

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
def lowerBoundReaches (numPts : Nat) (edges : Array TableEdge) (limit : Nat) : Bool :=
  go numPts 0 (edges.foldl (init := 0) (· + ·.d2LB))
where
  /-- Whether `total`, plus the point bounds for the `left` points numbered from `idx`
  on, reaches `limit` (stopping as soon as it does). -/
  go : Nat → Nat → Nat → Bool
    | 0, _, total => total ≥ limit
    | left + 1, idx, total =>
      total ≥ limit || go left (idx + 1)
        (total + edges.foldl (init := edges[0]!.pointLB[idx]!) fun m e => min m e.pointLB[idx]!)

/-- Fold `visit` over every list of offset numbers `[d₀, …, d_{v-1}]` (each `< 9`) that
ends with `ds`, in odometer order: `d₀` changes fastest. Called with `ds = []`, this
visits all `9ᵛ` lists. -/
def foldOffsetChoices (visit : Array Nat → σ → σ) : Nat → List Nat → σ → σ
  | 0, ds, st => visit ds.toArray st
  | v + 1, ds, st => (List.range 9).foldl (fun st a => foldOffsetChoices visit v (a :: ds) st) st

/-- The best polygon in the unit cube around `q` (all `n` vertices moved by offsets in
`{-1, 0, 1}²` at once, not all zero) that is strictly better than `f`, or `none`.

Each candidate is first checked with whole-number lower bounds; only if those cannot
rule it out is its exact `F²` computed. Since a lower bound never exceeds the true
value, a candidate ruled out is truly not better, so the result is the same as scoring
every candidate exactly. -/
def bestCubeMove (pts : Array Pt) (diam2 : Nat) (present : List Nat) (q : Array Pt) (f : Rat) :
    Option (Array Pt × Rat) :=
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
  -- The state is the best candidate so far and the whole-number limit it sets.
  let visit (digits : Array Nat) (st : Option (Array Pt × Rat) × Nat) :=
    let (best, limit) := st
    let edges := present.toArray.map fun e => table[e]![9 * digits[e]! + digits[(e + 1) % n]!]!
    if digits.all (· == stay) || lowerBoundReaches numPts edges limit then st
    else match objectiveBelow numPts diam2 (edges.map (·.terms)) (some ((best.map (·.2)).getD f)) with
      | some f' => (some ((Array.range n).map fun v => q[v]! + unitOffsets[digits[v]!]!, f'),
                    ceilScaled (f' * S) 1)
      | none => st
  (foldOffsetChoices visit n [] (none, ceilScaled (f * S) 1)).1

/-- The result of the fine and ultra-fine searches. -/
structure Polished where
  vertices : Array Pt
  objectiveSq : Rat
  moves : Nat
  certified : Bool

/-- Fine search, then ultra-fine certification, repeated until certified (or the fuel
runs out, or `n > ultraMax`). Each round either stops or uses at least one unit of
fuel, so `fuel + 1` rounds suffice. -/
def polish (pts : Array Pt) (missing : List Nat) (start : Array Pt) (fuel : Nat := 1000)
    (ultraMax : Nat := 7) : Polished :=
  let diam2 := diamSq pts
  go diam2 (presentEdges start.size missing) (fuel + 1) start (objectivePolygon pts diam2 start missing) 0
where
  /-- One round per call, with `rounds` rounds left: the polygon `q` with `F² = f`, after
  `used` moves. -/
  go (diam2 : Nat) (present : List Nat) : Nat → Array Pt → Rat → Nat → Polished
    | 0, q, f, used => ⟨q, f, used, false⟩
    | rounds + 1, q, f, used =>
      let (q, f, m, converged) := fineSearch pts diam2 present q f (fuel - used)
      let used := used + m
      if !converged then ⟨q, f, used, false⟩
      else if start.size == 2 then ⟨q, f, used, true⟩     -- the fine moves are the whole cube
      else if start.size > ultraMax then ⟨q, f, used, false⟩
      else match bestCubeMove pts diam2 present q f with
        | none => ⟨q, f, used, true⟩
        | some (q', f') =>
          if used ≥ fuel then ⟨q, f, used, false⟩
          else go diam2 present rounds q' f' (used + 1)

end PolyFit
