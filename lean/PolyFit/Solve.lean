import PolyFit.Polish

/-!
# The solver

`solve` splits on the polygon number `n`: a point, a segment, or a polygon with
`n ≥ 3` vertices (possibly with missing edges).

Done: `n = 1` and `n = 2`. The polygon branch still returns placeholder vertices (the
first `n` input points), but with their true `F²`.
-/

namespace PolyFit

/-- Placeholder vertices: the first `n` input points, wrapping around if there are fewer. -/
private def placeholderVertices (pts : Array Pt) (n : Nat) : Array Pt :=
  (Array.range n).map fun k => pts[k % pts.size]!

/-- Some edge `qs[e] → qs[(e + 1) % n]` of the polygon has length 0. -/
def hasZeroLengthEdge (qs : Array Pt) : Bool :=
  (List.range qs.size).any fun e => qs[e]! == qs[(e + 1) % qs.size]!

/-- `n = 1`: the centre of mass, rounded half up to an integer point. Since
`D₁(P, {q})²` splits into an `i` part and a `j` part, each a quadratic minimised at
the mean, this is the integer point minimising `F²`. -/
def fitPoint (pts : Array Pt) : Fit :=
  let q := centreOfMassRounded pts
  { vertices := #[q], objectiveSq := objectivePoint pts (diamSq pts) q }

/-- `n = 2`: pattern search starting from the farthest pair of points (see `Search.lean`).
A final segment of length 0 is error 3. -/
def fitSegment (pts : Array Pt) : Except FitError Fit := do
  let r := searchSegment pts (diamSq pts) (farthestPair pts)
  if r.q₀ == r.q₁ then throw .zeroLengthEdge
  return { vertices := #[r.q₀, r.q₁], objectiveSq := r.objectiveSq }

/-- The `fine_fit` command: the fine and ultra-fine searches from the polygon `start`
(`n ≥ 2`; see `Polish.lean`). A final zero-length edge is error 3. -/
def fineFit (prob : Problem) (start : Array Pt) : Except FitError Polished := do
  if prob.n < 2 then throw (.malformed "fine_fit needs n ≥ 2")
  if start.size != prob.n then throw (.malformed s!"expected {prob.n} start vertices, got {start.size}")
  let r := polish prob.points prob.missing start
  if hasZeroLengthEdge r.vertices then throw .zeroLengthEdge
  return r

/-- `n ≥ 3`: fit an `n`-gon whose edges listed in `missing` are absent.
TODO: the rough fit plus a local search. For now: placeholder vertices, scored honestly. -/
def fitPolygon (pts : Array Pt) (n : Nat) (missing : List Nat) : Except FitError Fit := do
  let qs := placeholderVertices pts n
  if hasZeroLengthEdge qs then throw .zeroLengthEdge
  return { vertices := qs, objectiveSq := objectivePolygon pts (diamSq pts) qs missing }

/-- Solve a validated problem. -/
def solve (prob : Problem) : Except FitError Fit :=
  match prob.n with
  | 0     => throw (.malformed "n must be at least 1")  -- already ruled out by `parseProblem`
  | 1     => pure (fitPoint prob.points)
  | 2     => fitSegment prob.points
  | k + 3 => fitPolygon prob.points (k + 3) prob.missing

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
