import PolyFit.Objective

/-!
# The rough fit: a coarse global search over candidate vertices

Given `m` candidate vertices in cyclic order (normally the reduced convex hull), every
`n`-element subset taken in that cyclic order is a candidate polygon. When edges are
missing, the labelling matters too (which edge gets which number), so each subset is
tried with all `n` rotations of its labels. Each candidate is scored with the exact
`F²`, and the best `k` distinct polygons are kept.

Speed: an edge's pieces of `F²` (see `EdgeTerms`) depend only on its two endpoints, so
they are computed once for each of the `m(m-1)/2` pairs of candidates and reused.
-/

namespace PolyFit

/-- All `k`-element sublists of `xs`, each in the order of `xs`, in lexicographic order
of positions. (Structural recursion on `xs`, so it always terminates.) -/
def combinations : Nat → List α → List (List α)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | k + 1, x :: xs => (combinations k xs).map (x :: ·) ++ combinations (k + 1) xs

/-- One scored candidate polygon. `key` lists its present edges as pairs of candidate
indices `(lo, hi)`, sorted: two labellings with the same key are the same polygon with
the same missing edges, so only one of them is kept. -/
structure Scored where
  vertices : Array Pt
  objectiveSq : Rat
  key : List (Nat × Nat)
deriving Inhabited

/-- Insert `c` into `best` (sorted by `F²`, at most `k` long) if it belongs there.
A candidate must be strictly better than the current `k`-th to enter, so on a tie the
one found first stays; a polygon already in the list (same key) is not added twice. -/
def insertBest (k : Nat) (best : Array Scored) (c : Scored) : Array Scored :=
  if best.any (·.key == c.key) then best
  else if best.size ≥ k && !(c.objectiveSq < best[best.size - 1]!.objectiveSq) then best
  else
    let pos := (best.findIdx? (c.objectiveSq < ·.objectiveSq)).getD best.size
    (best.insertIdx! pos c).extract 0 k

/-- The largest number of candidate polygons the rough fit will score. -/
def roughFitLimit : Nat := 2000000

/-- The `rough_fit` command: the best `k` polygons with `n` vertices chosen in cyclic
order from `cands` (distinct points), with the edges in `missing` absent. Requires
`2 ≤ n ≤ cands.size` and `k ≥ 1`. -/
def roughFit (pts : Array Pt) (n : Nat) (missing : List Nat) (cands : Array Pt) (k : Nat) :
    Except FitError (Array Scored) := do
  let m := cands.size
  if m < n then throw (.notEnoughCandidates m n)
  let subsets := combinations n (List.range m)
  let rotations := if missing.isEmpty || n ≤ 2 then [0] else List.range n
  if subsets.length * rotations.length > roughFitLimit then
    throw (.malformed s!"the rough fit would score {subsets.length * rotations.length} polygons (limit {roughFitLimit}); use fewer candidates")
  let diam2 := diamSq pts
  -- `terms[a * m + b]` holds the pieces of the edge from candidate `a` to candidate `b`.
  -- An edge's pieces do not depend on its direction, so only `a < b` is computed.
  let terms := (Array.range (m * m)).map fun ab =>
    let a := ab / m
    let b := ab % m
    if a < b then edgeTerms pts cands[a]! cands[b]! else default
  let edge (a b : Nat) := if a < b then terms[a * m + b]! else terms[b * m + a]!
  let present := presentEdges n missing
  return subsets.foldl (init := #[]) fun best sub =>
    let sub := sub.toArray
    rotations.foldl (init := best) fun best r =>
      -- Label `t` goes to candidate `sub[(t + r) % n]`.
      let label (t : Nat) := sub[(t + r) % n]!
      let pairs := present.map fun e => (label e, label ((e + 1) % n))
      -- Once the list is full, only a polygon strictly better than the k-th can enter,
      -- so scoring stops as soon as a polygon is certain not to be.
      let bound := if best.size ≥ k then some best[best.size - 1]!.objectiveSq else none
      match objectiveBelow pts.size diam2 (pairs.toArray.map fun (a, b) => edge a b) bound with
      | none => best
      | some f2 =>
        let key := (pairs.map fun (a, b) => (min a b, max a b)).mergeSort
          (fun x y => x.1 < y.1 || (x.1 == y.1 && x.2 ≤ y.2))
        insertBest k best ⟨(Array.range n).map fun t => cands[label t]!, f2, key⟩

end PolyFit
