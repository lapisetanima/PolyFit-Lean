import PolyFit.Polish

/-!
# The solver

The `fit` command searches only for `n = 1` (the rounded centre of mass). For `n ≥ 2`,
Python runs the pipeline one command at a time: `reduce_hull` (candidate vertices),
`rough_fit` (the best polygons on them), then `fine_fit` (the local search, here). In
evaluate mode, `fit` scores given vertices for any `n`.
-/

namespace PolyFit

/-- Some edge `qs[e] → qs[(e + 1) % n]` of the polygon has length 0. -/
def hasZeroLengthEdge (qs : Array Pt) : Bool :=
  (List.range qs.size).any fun e => qs[e]! == qs[(e + 1) % qs.size]!

/-- `n = 1`: the centre of mass, rounded half up to an integer point. Since
`D₁(P, {q})²` splits into an `i` part and a `j` part, each a quadratic minimised at
the mean, this is the integer point minimising `F²`. -/
def fitPoint (pts : Array Pt) : Fit :=
  let q := centreOfMassRounded pts
  { vertices := #[q], objectiveSq := objectivePoint pts (diamSq pts) q }

/-- The `fine_fit` command: the fine and ultra-fine searches from the polygon `start`
(`n ≥ 2`; see `Polish.lean`). A final zero-length edge is error 3. -/
def fineFit (prob : Problem) (start : Array Pt) : Except FitError Polished := do
  if prob.n < 2 then throw (.malformed "fine_fit needs n ≥ 2")
  if start.size != prob.n then throw (.malformed s!"expected {prob.n} start vertices, got {start.size}")
  let r := polish prob.points prob.missing start
  if hasZeroLengthEdge r.vertices then throw .zeroLengthEdge
  return r

/-- Solve a validated problem: only `n = 1` is searched here (see above). -/
def solve (prob : Problem) : Except FitError Fit :=
  if prob.n == 1 then pure (fitPoint prob.points)
  else throw (.malformed "fit searches only for n = 1; for n ≥ 2 use reduce_hull, rough_fit and fine_fit")

/-- Evaluate mode: score the given vertices (`verts.size = n`) without searching.
A zero-length edge is reported as error 3, as it would be at the end of a search. -/
def evaluate (prob : Problem) (verts : Array Pt) : Except FitError Fit := do
  let pts := prob.points
  let diam2 := diamSq pts
  match prob.n, verts with
  | 1, #[q₀] => return { vertices := verts, objectiveSq := objectivePoint pts diam2 q₀ }
  | 2, #[q₀, q₁] =>
    if q₀ == q₁ then throw .zeroLengthEdge
    return { vertices := verts, objectiveSq := objectiveSegment pts diam2 q₀ q₁ }
  | _, _ =>
    if verts.size != prob.n then throw (.malformed s!"expected {prob.n} vertices, got {verts.size}")
    if hasZeroLengthEdge verts then throw .zeroLengthEdge
    return { vertices := verts, objectiveSq := objectivePolygon pts diam2 verts prob.missing }

/-- Answer a validated request: evaluate the given vertices, or search for the best ones. -/
def answer (prob : Problem) : Except FitError Fit :=
  match prob.vertices with
  | some verts => evaluate prob verts
  | none       => solve prob

end PolyFit
