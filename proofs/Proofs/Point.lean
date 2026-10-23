import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PolyFit.Objective

/-!
# n = 1: the rounded centre of mass is optimal

`F(q)² = D₁(P, {q})²` is `Σ_p d(p, q)²` divided by a constant `≥ 0`, and `Σ_p d(p, q)²` is
a sum over the `i` coordinates plus a sum over the `j` coordinates, each depending on
only one coordinate of `q`. In one coordinate, with `k` values `a` of sum `S`,
`Σ (a - x)² = Σ a² - 2 S x + k x²`: a parabola in `x` with its minimum at the mean `S / k`,
so over the integers it is smallest at the integer nearest to `S / k`.
-/

namespace PolyFit

/-- A sum written as a `foldl`, the way the solver writes it, is a `List.sum`. -/
theorem foldl_add_eq_sum {α β} [AddCommMonoid β] (l : List α) (f : α → β) (b : β) :
    l.foldl (fun s a => s + f a) b = b + (l.map f).sum := by
  induction l generalizing b <;> simp [*, add_assoc]

/-- `Σ (a - x)² = Σ a² - 2 x S + k x²`. -/
theorem sum_sq_sub (xs : List Int) (x : Int) :
    (xs.map fun a => (a - x) ^ 2).sum
      = (xs.map (· ^ 2)).sum - 2 * x * xs.sum + xs.length * x ^ 2 := by
  induction xs with
  | nil => simp
  | cons a as ih => simp [ih]; ring

/-- One coordinate: `roundHalfUp S k`, the integer nearest the mean, minimises
`Σ (a - x)²` over all integers `x`. -/
theorem sum_sq_sub_roundHalfUp_le (xs : List Int) (x : Int) :
    (xs.map fun a => (a - roundHalfUp xs.sum xs.length) ^ 2).sum
      ≤ (xs.map fun a => (a - x) ^ 2).sum := by
  by_cases hne : xs = []
  · simp [hne]
  have hd : (0 : Int) < 2 * xs.length := by have := List.length_pos_iff.2 hne; omega
  -- `r = ⌊n / d⌋` means `r d ≤ n < (r + 1) d`, which says `|r - S / k| ≤ 1/2`.
  have h₁ := Int.ediv_mul_le (2 * xs.sum + xs.length) hd.ne'
  have h₂ := Int.lt_ediv_add_one_mul_self (2 * xs.sum + xs.length) hd
  rw [sum_sq_sub, sum_sq_sub]
  unfold roundHalfUp
  generalize (2 * xs.sum + xs.length) / (2 * (xs.length : Int)) = r at *
  -- The goal is `(x - r) (k (x + r) - 2 S) ≥ 0`: both factors have the same sign.
  have hk : (0 : Int) ≤ xs.length := by positivity
  rcases lt_trichotomy x r with hx | rfl | hx
  · have : 0 ≤ 2 * xs.sum - xs.length * (x + r) := by
      nlinarith [mul_nonneg hk (by omega : (0 : Int) ≤ r - 1 - x)]
    nlinarith [mul_nonneg (sub_nonneg.2 hx.le) this]
  · rfl
  · have : 0 ≤ xs.length * (x + r) - 2 * xs.sum := by
      nlinarith [mul_nonneg hk (by omega : (0 : Int) ≤ x - r - 1)]
    nlinarith [mul_nonneg (sub_nonneg.2 hx.le) this]

/-- `d(p, q)²` as an integer: the `toNat` in `distSq` never cuts anything off. -/
theorem distSq_eq (p q : Pt) : (distSq p q : Int) = (p.i - q.i) ^ 2 + (p.j - q.j) ^ 2 :=
  Int.toNat_of_nonneg (by positivity)

/-- `Σ_p d(p, q)²` split into the two coordinates. -/
theorem sum_distSq (l : List Pt) (q : Pt) :
    (l.map fun p => (distSq p q : Rat)).sum
      = (((l.map Pt.i).map fun a => (a - q.i) ^ 2).sum
          + ((l.map Pt.j).map fun a => (a - q.j) ^ 2).sum : Int) := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    rw [← Int.cast_natCast, distSq_eq]
    push_cast; ring

/-- **The n = 1 theorem.** The rounded centre of mass minimises the objective over all
integer points `q`. No hypotheses are needed: if `P` is empty or `diam(P) = 0`, both
sides divide by 0 and are 0. -/
theorem objectivePoint_centreOfMassRounded_le (pts : Array Pt) (q : Pt) :
    objectivePoint pts (diamSq pts) (centreOfMassRounded pts)
      ≤ objectivePoint pts (diamSq pts) q := by
  -- The `i` and `j` coordinates of the points, and the rounded centre of mass `c`.
  let is := pts.toList.map Pt.i
  let js := pts.toList.map Pt.j
  let c : Pt := ⟨roundHalfUp is.sum is.length, roundHalfUp js.sum js.length⟩
  have hc : centreOfMassRounded pts = c := by
    simp [centreOfMassRounded, c, is, js, ← Array.foldl_toList, foldl_add_eq_sum]
  -- `F(x)² = (Σ (a - xᵢ)² + Σ (b - xⱼ)²) / (k D)` for every integer point `x`.
  have hF : ∀ x, objectivePoint pts (diamSq pts) x
      = ((is.map fun a => (a - x.i) ^ 2).sum + (js.map fun b => (b - x.j) ^ 2).sum : Int)
          / (pts.size * diamSq pts : Nat) := by
    intro x
    simp only [objectivePoint, d1SqToPoint, sumOver, ← Array.foldl_toList, foldl_add_eq_sum,
      zero_add, sum_distSq, is, js]
  calc objectivePoint pts (diamSq pts) (centreOfMassRounded pts)
      = ((is.map fun a => (a - c.i) ^ 2).sum + (js.map fun b => (b - c.j) ^ 2).sum : Int)
          / (pts.size * diamSq pts : Nat) := by rw [hc, hF]
    -- Same denominator; compare the numerators one coordinate at a time.
    _ ≤ ((is.map fun a => (a - q.i) ^ 2).sum + (js.map fun b => (b - q.j) ^ 2).sum : Int)
          / (pts.size * diamSq pts : Nat) := by
        gcongr ?_ / _
        exact_mod_cast add_le_add (sum_sq_sub_roundHalfUp_le is q.i)
          (sum_sq_sub_roundHalfUp_le js q.j)
    _ = objectivePoint pts (diamSq pts) q := (hF q).symm

end PolyFit
