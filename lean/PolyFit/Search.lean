import PolyFit.Objective

/-!
# Local search

For a segment we search the 4-dimensional configuration space `(q₀, q₁) ∈ ℤ²×ℤ²` by
pattern search: at step size `s`, try moving each endpoint by `s` times one of the 9
offsets `{-1, 0, 1}²` (80 moves, since "neither endpoint moves" is excluded). Take the
best move if it strictly lowers `F²`; otherwise halve `s`. Stop when no move of size 1
helps, or when the fuel (a cap on accepted moves) runs out.
-/

namespace PolyFit

instance : Add Pt := ⟨fun p q => ⟨p.i + q.i, p.j + q.j⟩⟩

/-- The vector `d` scaled by `s`. -/
def Pt.scale (s : Int) (d : Pt) : Pt := ⟨s * d.i, s * d.j⟩

/-- The 9 offsets `{-1, 0, 1}²`, including `(0, 0)`. -/
def unitOffsets : Array Pt :=
  #[-1, 0, 1].flatMap fun a => #[-1, 0, 1].map fun b => ⟨a, b⟩

/-- The 80 segments obtained by moving `q₀` and `q₁` by `s` times an offset each,
excluding the move where neither endpoint changes. -/
def segmentMoves (s : Int) (q₀ q₁ : Pt) : Array (Pt × Pt) :=
  unitOffsets.flatMap fun d₀ =>
    (unitOffsets.filter (d₀ != ⟨0, 0⟩ || · != ⟨0, 0⟩)).map fun d₁ =>
      (q₀ + d₀.scale s, q₁ + d₁.scale s)

/-- The first step size: the largest power of 2 with `(4 s)² ≤ diam(P)²`, or 1.
So steps start around a quarter of the diameter. -/
def initialStep (diam2 : Nat) : Nat := Id.run do
  let mut s := 1
  for _ in [0:64] do
    if 16 * (2 * s) ^ 2 > diam2 then break
    s := 2 * s
  return s

/-- Among the 80 moves at step `s`, the one with the smallest `F²` (the first, on ties),
as `(q₀, q₁, F²)`. -/
def bestSegmentMove (pts : Array Pt) (diam2 : Nat) (s : Int) (q₀ q₁ : Pt) : Pt × Pt × Rat :=
  let moves := segmentMoves s q₀ q₁
  let score (m : Pt × Pt) := (m.1, m.2, objectiveSegment pts diam2 m.1 m.2)
  moves.foldl (init := score moves[0]!) fun best m =>
    let cand := score m
    if cand.2.2 < best.2.2 then cand else best

/-- Pattern search for the segment, from `start`, returning `(q₀, q₁, F²)`.
Each round of the loop either accepts a move (using one unit of fuel) or halves `s`,
and `s` can be halved at most 64 times, so `fuel + 65` rounds always suffice.

`converged` is true when the search stopped because no move of size 1 improves `F²`
(so the result is a local minimum over all 80 moves), and false when it ran out of fuel. -/
structure SegmentSearch where
  q₀ : Pt
  q₁ : Pt
  objectiveSq : Rat
  moves : Nat
  converged : Bool

def searchSegment (pts : Array Pt) (diam2 : Nat) (start : Pt × Pt) (fuel : Nat := 1000) :
    SegmentSearch := Id.run do
  let mut q₀ := start.1
  let mut q₁ := start.2
  let mut f := objectiveSegment pts diam2 q₀ q₁
  let mut s := initialStep diam2
  let mut moves := 0
  let mut converged := false
  for _ in [0:fuel + 65] do
    let (a, b, fNew) := bestSegmentMove pts diam2 s q₀ q₁
    if fNew < f then
      if moves == fuel then break
      q₀ := a
      q₁ := b
      f := fNew
      moves := moves + 1
    else if s > 1 then
      s := s / 2
    else
      converged := true
      break
  return ⟨q₀, q₁, f, moves, converged⟩

end PolyFit
