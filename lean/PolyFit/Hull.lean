import PolyFit.Geometry

/-!
# The fixed properties of a point set: centre of mass, radii, convex hull

"Counterclockwise" is as seen on screen, i.e. in the plane `(x, y) = (j, -i)`. The
`cross` product of `Geometry.lean`, computed in `(i, j)`, equals the usual cross product
in `(x, y)`, so `cross > 0` is a counterclockwise (left) turn on screen.
-/

namespace PolyFit

/-- The exact centre of mass `(Σ i / k, Σ j / k)`. Requires `pts` nonempty. -/
def centreOfMass (pts : Array Pt) : Rat × Rat :=
  let k : Rat := pts.size
  ((pts.foldl (· + ·.i) (0 : Int) : Rat) / k, (pts.foldl (· + ·.j) (0 : Int) : Rat) / k)

/-- `|p - c|²` for a point with rational coordinates `c`. -/
def distSqTo (p : Pt) (c : Rat × Rat) : Rat :=
  (p.i - c.1) ^ 2 + (p.j - c.2) ^ 2

/-- Twice the signed area of the triangle `o a b`: positive when `o → a → b` turns
counterclockwise on screen, zero when the three points are collinear. -/
def turn (o a b : Pt) : Int :=
  cross (a - o) (b - o)

/-- Push `p` onto a hull chain, first popping the points that would not make a strict
counterclockwise turn (so collinear points are dropped). Each round pops one point, so
`chain.size` rounds always suffice. -/
def pushTurningLeft (chain : Array Pt) (p : Pt) : Array Pt := Id.run do
  let mut c := chain
  for _ in [0:chain.size] do
    if c.size ≥ 2 && turn c[c.size - 2]! c[c.size - 1]! p ≤ 0 then c := c.pop else break
  return c.push p

/-- The convex hull's vertices, counterclockwise on screen, collinear points left out
(Andrew's monotone chain): sort by screen position `(x, y) = (j, -i)`, build the lower
chain left to right and the upper chain right to left. For collinear points the hull is
the two extreme points. Requires at least two distinct points. -/
def convexHullCCW (pts : Array Pt) : Array Pt :=
  let distinct := pts.toList.eraseDups.toArray
  let sorted := distinct.qsort fun p q => p.j < q.j || (p.j == q.j && p.i > q.i)
  let lower := sorted.foldl pushTurningLeft #[]
  let upper := sorted.reverse.foldl pushTurningLeft #[]
  lower.pop ++ upper.pop

/-- Whether `a` should come before `b` as the hull's starting vertex: the larger `j`
wins; on a tie (a vertical right-hand edge), the vertex at or just above the centre of
mass's row (the largest `i` with `i ≤ comI`), or, if both are below it, the higher one. -/
def startsBefore (comI : Rat) (a b : Pt) : Bool :=
  if a.j != b.j then a.j > b.j else
  let aAbove := (a.i : Rat) ≤ comI
  let bAbove := (b.i : Rat) ≤ comI
  if aAbove != bAbove then aAbove
  else if aAbove then a.i > b.i
  else a.i < b.i

/-- The convex hull, counterclockwise on screen, starting at the vertex chosen by
`startsBefore`. -/
def convexHull (pts : Array Pt) (com : Rat × Rat) : Array Pt :=
  let hull := convexHullCCW pts
  let start := (Array.range hull.size).foldl (init := 0) fun best k =>
    if startsBefore com.1 hull[k]! hull[best]! then k else best
  hull.extract start hull.size ++ hull.extract 0 start

/-- Twice the area of the triangle `a b c` (never negative). -/
def triangleArea2 (a b c : Pt) : Nat :=
  (turn a b c).natAbs

/-- Visvalingam–Whyatt: repeatedly delete the vertex of the closed polygon `poly` whose
triangle with its two neighbours has the least area (on a tie, the vertex earliest in
the current order) until at most `target` vertices remain. The survivors keep their
order. Each round deletes one vertex, so `poly.size` rounds always suffice. -/
def visvalingam (poly : Array Pt) (target : Nat) : Array Pt := Id.run do
  let mut cur := poly
  for _ in [0:poly.size] do
    if cur.size ≤ target then break
    let m := cur.size
    let area (k : Nat) := triangleArea2 cur[(k + m - 1) % m]! cur[k]! cur[(k + 1) % m]!
    let smallest := (List.range m).foldl (init := 0) fun best k => if area k < area best then k else best
    cur := cur.eraseIdx! smallest
  return cur

/-- The `reduce_hull` command: the convex hull, trimmed to at most `2n` candidate
vertices. With `h` hull vertices: `h < n` is error 5; `n ≤ h ≤ 2n` keeps them all;
`h > 2n` trims with Visvalingam–Whyatt down to `2n`. -/
def reduceHull (pts : Array Pt) (n : Nat) : Except FitError (Array Pt) := do
  let hull := convexHull pts (centreOfMass pts)
  if hull.size < n then throw (.notEnoughCandidates hull.size n)
  return visvalingam hull (2 * n)

/-- The `describe` command. Requires `pts` nonempty with `diam(P) > 0`. -/
def describe (pts : Array Pt) : Description :=
  let com := centreOfMass pts
  let radii := pts.map (distSqTo · com)
  { com
    diamSq := diamSq pts
    innerRadiusSq := radii.foldl min radii[0]!
    outerRadiusSq := radii.foldl max radii[0]!
    hull := convexHull pts com }

end PolyFit
