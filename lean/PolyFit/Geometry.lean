import PolyFit.Types

/-!
# Exact integer geometry

Everything here stays in `Int`/`Nat` (arbitrary precision, so nothing can overflow),
except where a division forces a `Rat`.
-/

namespace PolyFit

/-- Points double as vectors: `p - q` is the vector from `q` to `p`. -/
instance : Sub Pt := ⟨fun p q => ⟨p.i - q.i, p.j - q.j⟩⟩

/-- Dot product of two vectors. -/
def dot (u v : Pt) : Int :=
  u.i * v.i + u.j * v.j

/-- 2D cross product `u.i * v.j - u.j * v.i` (signed area of the parallelogram on `u`, `v`). -/
def cross (u v : Pt) : Int :=
  u.i * v.j - u.j * v.i

/-- Squared Euclidean distance `d(p, q)²`. -/
def distSq (p q : Pt) : Nat :=
  ((p.i - q.i) ^ 2 + (p.j - q.j) ^ 2).toNat

/-- `diam(P)²`: the largest squared distance between two points of `P`.
This compares every pair, which is fine for the point counts we expect. -/
def diamSq (pts : Array Pt) : Nat :=
  pts.foldl (init := 0) fun best p =>
    pts.foldl (init := best) fun best q => max best (distSq p q)

/-- The two points of `P` realising `diam(P)` (the first such pair found). -/
def farthestPair (pts : Array Pt) : Pt × Pt :=
  pts.foldl (init := (pts[0]!, pts[0]!)) fun best p =>
    pts.foldl (init := best) fun best q =>
      if distSq p q > distSq best.1 best.2 then (p, q) else best

/-- `d₁(p, ℓ)²` for the segment `ℓ` from `q₀` to `q₁`. With `v = q₁ - q₀` and
`w = p - q₀`, the projection of `p` onto the line has parameter `t = (w · v) / L²`:
if `t ≤ 0` the nearest point is `q₀`, if `t ≥ 1` it is `q₁`, and otherwise the
distance is the height of the parallelogram on `w`, `v`, i.e. `|w × v| / L`.
A zero-length segment has `w · v = 0`, so it falls into the first case. -/
def distSqToSegment (p q₀ q₁ : Pt) : Rat :=
  let v := q₁ - q₀
  let w := p - q₀
  let proj := dot w v
  if proj ≤ 0 then distSq p q₀
  else if proj ≥ dot v v then distSq p q₁
  else ((cross w v ^ 2 : Int) : Rat) / (dot v v : Rat)

/-- `⌊a / b + 1/2⌋`: round `a / b` to the nearest integer, with halves rounded up
(so `3.5 ↦ 4` and `-3.5 ↦ -3`). Requires `b > 0`. Lean's `Int` division rounds
down when the divisor is positive, which is what makes this formula correct. -/
def roundHalfUp (a : Int) (b : Nat) : Int :=
  (2 * a + b) / (2 * b)

/-- The centre of mass of `P`, each coordinate rounded half up. Requires `P` nonempty. -/
def centreOfMassRounded (pts : Array Pt) : Pt :=
  let k := pts.size
  let sumI := pts.foldl (init := 0) fun s p => s + p.i
  let sumJ := pts.foldl (init := 0) fun s p => s + p.j
  ⟨roundHalfUp sumI k, roundHalfUp sumJ k⟩

end PolyFit
