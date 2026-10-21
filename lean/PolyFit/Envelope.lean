/-!
# Integrating the lower envelope of lines

For the segment term `D₂` we need `∫₀¹ min_p (a_p t + b_p) dt`: the integral of the
pointwise minimum (the *lower envelope*) of finitely many lines with integer
coefficients. The result is an exact `Rat`.
-/

namespace PolyFit

/-- The line `t ↦ slope * t + icept`. -/
structure Line where
  slope : Int
  icept : Int
deriving Repr, Inhabited

/-- `∫ₛᵉ (slope * t + icept) dt`. -/
def Line.integral (ℓ : Line) (s e : Rat) : Rat :=
  ℓ.slope * (e * e - s * s) / 2 + ℓ.icept * (e - s)

/-- The `t` where `ℓ` and `m` meet. Requires different slopes. -/
def Line.crossing (ℓ m : Line) : Rat :=
  ((m.icept - ℓ.icept : Int) : Rat) / ((ℓ.slope - m.slope : Int) : Rat)

/-- `∫₀¹ min_ℓ ℓ(t) dt` for a nonempty array of lines.

Walk along `[0, 1]`, keeping the line that is currently lowest. After time `t`, only a
line with a *smaller* slope can overtake it, and the first to do so is the one whose
crossing comes earliest (on a tie, the one with the smallest slope, which is lowest
afterwards). Integrate up to that crossing and switch. Every switch strictly lowers
the slope, so there are fewer switches than lines and the loop never runs out. -/
def lowerEnvelopeIntegral (lines : Array Line) : Rat := Id.run do
  -- The lowest line at t = 0; on a tie, the smaller slope is lower just after 0.
  let mut cur := lines.foldl (init := lines[0]!) fun best ℓ =>
    if ℓ.icept < best.icept || (ℓ.icept == best.icept && ℓ.slope < best.slope) then ℓ else best
  let mut t : Rat := 0
  let mut total : Rat := 0
  for _ in [0:lines.size] do
    -- The smaller-slope line crossing `cur` first, as (crossing time, line).
    let next := lines.foldl (init := (none : Option (Rat × Line))) fun best ℓ =>
      if ℓ.slope ≥ cur.slope then best else
        let tc := cur.crossing ℓ
        match best with
        | some (tb, b) => if tc < tb || (tc == tb && ℓ.slope < b.slope) then some (tc, ℓ) else best
        | none => some (tc, ℓ)
    match next with
    | some (tc, ℓ) =>
      if tc ≥ 1 then break
      total := total + cur.integral t tc
      t := tc
      cur := ℓ
    | none => break
  return total + cur.integral t 1

end PolyFit
