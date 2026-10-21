/-!
# Basic types shared by the solver

A point is `(i, j)` in matrix style: `i` is the row, counted downward from the top, and
`j` is the column, counted rightward from the left. Input pixels and polygon vertices
are both integer points. "Counterclockwise" means as seen on screen.
-/

namespace PolyFit

/-- An integer point `(i, j)`. -/
structure Pt where
  i : Int
  j : Int
deriving Repr, BEq, Inhabited

/-- A validated request.

* `points` is nonempty and its points are not all equal (so `diam(P) > 0`).
* `n ≥ 1` is the number of vertices: 1 = point, 2 = segment, `n ≥ 3` = polygon.
* `missing` is empty when `n ≤ 2`. When `n ≥ 3` it is sorted, duplicate-free,
  every entry is `< n`, and no two entries are cyclically consecutive.
* `vertices` is `some vs` (with `vs.size = n`) in evaluate mode: score these vertices
  instead of searching. It is `none` for a normal fit. -/
structure Problem where
  points  : Array Pt
  n       : Nat
  missing : List Nat
  vertices : Option (Array Pt) := none
deriving Repr

/-- A successful fit: the vertices `q₀, …, q_{n-1}` and the exact objective `F²`. -/
structure Fit where
  vertices : Array Pt
  objectiveSq : Rat
deriving Repr

/-- The fixed properties of a point set `P`, computed once by the `describe` command. -/
structure Description where
  /-- The centre of mass `(Σ i / k, Σ j / k)`, exactly. -/
  com : Rat × Rat
  /-- `diam(P)²`. -/
  diamSq : Nat
  /-- `min_p |p - com|²` and `max_p |p - com|²`. -/
  innerRadiusSq : Rat
  outerRadiusSq : Rat
  /-- The convex hull's vertices, counterclockwise on screen (see `Hull.lean`). -/
  hull : Array Pt
deriving Repr

/-- What Python asked for. -/
inductive Request where
  /-- Compute the `Description` of a point set. -/
  | describe (points : Array Pt)
  /-- Fit a polygon (or, in evaluate mode, score the given vertices). -/
  | fit (prob : Problem)
  /-- Trim the convex hull to at most `2n` candidate vertices (Visvalingam–Whyatt). -/
  | reduceHull (points : Array Pt) (n : Nat)
  /-- Score every cyclically ordered `n`-subset of the candidates (and every labelling,
  when edges are missing) and return the best `k` polygons. -/
  | roughFit (prob : Problem) (candidates : Array Pt) (k : Nat)
  /-- A local search from the polygon `start`. -/
  | fineFit (prob : Problem) (start : Array Pt)
deriving Repr

/-- Everything that can go wrong. Each has a numeric code that is sent to Python. -/
inductive FitError where
  /-- `diam(P) = 0`: all the points coincide. -/
  | zeroDiameter
  /-- Two cyclically consecutive edges are both listed as missing. -/
  | consecutiveMissing
  /-- The final polygon has an edge of length 0. -/
  | zeroLengthEdge
  /-- Bad JSON, `n < 1`, a missing-edge index out of range, a negative coordinate, ... -/
  | malformed (why : String)
  /-- Fewer than `n` candidate vertices (for example, a convex hull with fewer than
  `n` vertices). -/
  | notEnoughCandidates (found needed : Nat)
deriving Repr

def FitError.code : FitError → Nat
  | .zeroDiameter            => 1
  | .consecutiveMissing      => 2
  | .zeroLengthEdge          => 3
  | .malformed _             => 4
  | .notEnoughCandidates _ _ => 5

def FitError.message : FitError → String
  | .zeroDiameter       => "all points coincide, so diam(P) = 0"
  | .consecutiveMissing => "two cyclically consecutive edges are both missing"
  | .zeroLengthEdge     => "the best fit found has an edge of length 0"
  | .malformed why      => s!"malformed input: {why}"
  | .notEnoughCandidates found needed => s!"only {found} candidate vertices, but n = {needed}"

end PolyFit
