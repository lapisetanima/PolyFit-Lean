import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Proofs.Polish

/-!
# The envelope walk computes the integral of the lower envelope

`lowerEnvelopeIntegral lines` walks along `[0, 1]` keeping the currently lowest line. This
file proves that it computes `∫₀¹ min_ℓ ℓ(t) dt` exactly (`lowerEnvelopeIntegral_eq_integral`).

**Proof outline.**
* `Lowest cur t`: `cur` is the lowest line at `t`, and on a tie it has the smallest slope
  (so it stays lowest just after `t`). The starting line is `Lowest` at 0 (`start_lowest`).
* The search for the next line (`nextStep_spec`) returns either nothing (no line has a
  smaller slope) or the line with the earliest crossing among those with a smaller slope,
  ties going to the smallest slope.
* Between `t` and that crossing, `cur` stays lowest (`lowest_until`): lines with a larger
  slope only rise relative to it, and lines with a smaller slope have not crossed yet. At
  the crossing, the new line is `Lowest` (by the tie-break). So `total` stays
  `∫₀ᵗ min_ℓ ℓ`, and each switch strictly lowers the slope, so the switch budget (the
  number of lines) never runs out (`go_correct`).
-/

namespace PolyFit

/-! ## Lines as real functions -/

/-- The line `ℓ` as a real function. -/
noncomputable def Line.ev (ℓ : Line) (t : ℝ) : ℝ := ℓ.slope * t + ℓ.icept

/-- `∫ₐᵇ ℓ(s) ds`, in closed form. -/
theorem Line.integral_ev (ℓ : Line) (a b : ℝ) :
    ∫ s in a..b, ℓ.ev s = ℓ.slope * (b * b - a * a) / 2 + ℓ.icept * (b - a) := by
  unfold Line.ev
  rw [intervalIntegral.integral_add (f := fun s => (ℓ.slope : ℝ) * s) (g := fun _ => (ℓ.icept : ℝ))
    (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- The code's `Line.integral` is the integral. -/
theorem Line.integral_eq (ℓ : Line) (a b : ℚ) : (ℓ.integral a b : ℝ) = ∫ s in (a : ℝ)..b, ℓ.ev s := by
  rw [Line.integral_ev, Line.integral]
  push_cast
  ring

/-- Where two lines with different slopes cross, and how they differ elsewhere:
`ℓ(s) − cur(s) = (ℓ.slope − cur.slope)(s − c)` with `c` the crossing. -/
theorem Line.ev_sub_ev (cur ℓ : Line) (h : cur.slope ≠ ℓ.slope) (s : ℝ) :
    ℓ.ev s - cur.ev s = (ℓ.slope - cur.slope) * (s - (cur.crossing ℓ : ℝ)) := by
  have h' : ((cur.slope : ℝ) - ℓ.slope) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast h)
  simp only [Line.ev, Line.crossing]
  push_cast
  field_simp
  ring

/-! ## The lower envelope -/

/-- The lower envelope `min_ℓ ℓ(t)` (for nonempty `lines`). -/
noncomputable def envR (lines : Array Line) (t : ℝ) : ℝ :=
  lines.toList.foldl (fun m ℓ => min m (ℓ.ev t)) (lines[0]!.ev t)

theorem continuous_envR (lines : Array Line) : Continuous (envR lines) := by
  have key : ∀ (l : List Line) (g : ℝ → ℝ), Continuous g →
      Continuous (fun t => l.foldl (fun m ℓ => min m (ℓ.ev t)) (g t)) := by
    intro l
    induction l with
    | nil => intro g hg; simpa using hg
    | cons x xs ih =>
      intro g hg
      simp only [List.foldl_cons]
      exact ih (fun t => min (g t) (x.ev t)) (hg.min (by unfold Line.ev; fun_prop))
  exact key lines.toList (fun t => lines[0]!.ev t) (by unfold Line.ev; fun_prop)

theorem integrable_envR (lines : Array Line) (a b : ℝ) : IntervalIntegrable (envR lines) MeasureTheory.volume a b :=
  (continuous_envR lines).intervalIntegrable a b

/-- Where one line is below all the others, it is the envelope. -/
theorem envR_eq (lines : Array Line) (cur : Line) (hcur : cur ∈ lines) (s : ℝ)
    (hlow : ∀ ℓ ∈ lines, cur.ev s ≤ ℓ.ev s) : envR lines s = cur.ev s := by
  have hle := foldl_min_le (fun ℓ : Line => ℓ.ev s) lines.toList (lines[0]!.ev s)
  have hne : 0 < lines.size := Array.size_pos_of_mem hcur
  have h0 : lines[0]! ∈ lines := by rw [getElem!_pos lines 0 hne]; exact Array.getElem_mem hne
  apply le_antisymm (hle.2 cur (by simpa using hcur))
  rcases foldl_min_cases (fun ℓ : Line => ℓ.ev s) lines.toList (lines[0]!.ev s) with h | ⟨ℓ, hℓ, h⟩
  · rw [h]; exact hlow _ h0
  · rw [h]; exact hlow ℓ (by simpa using hℓ)

/-! ## The walk -/

/-- `cur` is the lowest line at `t`, and on a tie it has the smallest slope. -/
def Lowest (lines : Array Line) (cur : Line) (t : ℝ) : Prop :=
  cur ∈ lines ∧ ∀ ℓ ∈ lines, cur.ev t ≤ ℓ.ev t ∧ (cur.ev t = ℓ.ev t → cur.slope ≤ ℓ.slope)

/-- The step of the search for the starting line (as in `lowerEnvelopeIntegral`). -/
def startStep (best ℓ : Line) : Line :=
  if ℓ.icept < best.icept || (ℓ.icept == best.icept && ℓ.slope < best.slope) then ℓ else best

/-- The step of the search for the next line (as in `lowerEnvelopeIntegral.go`). -/
def nextStep (cur : Line) (best : Option (Rat × Line)) (ℓ : Line) : Option (Rat × Line) :=
  if ℓ.slope ≥ cur.slope then best else
    let tc := cur.crossing ℓ
    match best with
    | some (tb, b) => if tc < tb || (tc == tb && ℓ.slope < b.slope) then some (tc, ℓ) else best
    | none => some (tc, ℓ)

theorem lowerEnvelopeIntegral_eq_go (lines : Array Line) :
    lowerEnvelopeIntegral lines
      = lowerEnvelopeIntegral.go lines lines.size (lines.foldl startStep lines[0]!) 0 0 := rfl

theorem go_succ (lines : Array Line) (k : Nat) (cur : Line) (t total : Rat) :
    lowerEnvelopeIntegral.go lines (k + 1) cur t total =
      match lines.foldl (nextStep cur) none with
      | some (tc, ℓ) =>
        if max t tc ≥ 1 then total + cur.integral t 1
        else lowerEnvelopeIntegral.go lines k ℓ (max t tc) (total + cur.integral t (max t tc))
      | none => total + cur.integral t 1 := rfl

theorem go_zero (lines : Array Line) (cur : Line) (t total : Rat) :
    lowerEnvelopeIntegral.go lines 0 cur t total = total + cur.integral t 1 := rfl

/-- A fold invariant that talks about the elements seen so far: if every step extends
it by one element, it holds for the whole list. -/
theorem foldl_prefix {α β : Type} (f : β → α → β) (P : β → List α → Prop) (l : List α)
    (hf : ∀ b S a, a ∈ l → P b S → P (f b a) (S ++ [a])) :
    ∀ init S, P init S → P (l.foldl f init) (S ++ l) := by
  induction l with
  | nil => intro init S h; simpa using h
  | cons x xs ih =>
    intro init S h
    have := ih (fun b S a ha hb => hf b S a (by simp [ha]) hb) (f init x) (S ++ [x])
      (hf init S x (by simp) h)
    simpa using this

/-- The starting line is lowest at 0 (smallest intercept, then smallest slope).

Proof: along the fold, the current line is one of the lines and is lexicographically
(intercept, then slope) at most every line seen so far. -/
theorem start_lowest (lines : Array Line) (hne : 0 < lines.size) :
    Lowest lines (lines.foldl startStep lines[0]!) 0 := by
  have h0 : lines[0]! ∈ lines := by rw [getElem!_pos lines 0 hne]; exact Array.getElem_mem hne
  have key := foldl_prefix startStep
    (fun best S => best ∈ lines ∧ ∀ ℓ ∈ S, best.icept < ℓ.icept ∨ (best.icept = ℓ.icept ∧ best.slope ≤ ℓ.slope))
    lines.toList ?_ lines[0]! [] ⟨h0, by simp⟩
  · rw [List.nil_append, Array.foldl_toList] at key
    refine ⟨key.1, fun ℓ hℓ => ?_⟩
    rcases key.2 ℓ (by simpa using hℓ) with h | ⟨h₁, h₂⟩
    · simp only [Line.ev, mul_zero, zero_add]
      exact ⟨by exact_mod_cast h.le, fun heq => absurd (by exact_mod_cast heq) h.ne⟩
    · simp only [Line.ev, mul_zero, zero_add]
      exact ⟨by exact_mod_cast h₁.le, fun _ => h₂⟩
  · rintro b S a ha ⟨hb, hS⟩
    simp only [startStep]
    split_ifs with hc
    · simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at hc
      refine ⟨by simpa using ha, fun ℓ hℓ => ?_⟩
      rcases List.mem_append.1 hℓ with hℓ | hℓ
      · rcases hS ℓ hℓ with h | ⟨h₁, h₂⟩ <;> rcases hc with hc | ⟨hc₁, hc₂⟩ <;> omega
      · simp at hℓ; subst hℓ; right; exact ⟨rfl, le_rfl⟩
    · simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq, not_or, not_and,
        not_lt] at hc
      refine ⟨hb, fun ℓ hℓ => ?_⟩
      rcases List.mem_append.1 hℓ with hℓ | hℓ
      · exact hS ℓ hℓ
      · simp at hℓ; subst hℓ
        rcases lt_or_eq_of_le hc.1 with h | h
        · left; exact h
        · right; exact ⟨h, hc.2 h.symm⟩

/-- What the search for the next line returns. -/
theorem nextStep_spec (lines : Array Line) (cur : Line) :
    (lines.foldl (nextStep cur) none = none → ∀ ℓ ∈ lines, cur.slope ≤ ℓ.slope) ∧
    ∀ tc b, lines.foldl (nextStep cur) none = some (tc, b) →
      b ∈ lines ∧ b.slope < cur.slope ∧ tc = cur.crossing b ∧
      ∀ ℓ ∈ lines, ℓ.slope < cur.slope →
        tc < cur.crossing ℓ ∨ (tc = cur.crossing ℓ ∧ b.slope ≤ ℓ.slope) := by
  have key := foldl_prefix (nextStep cur)
    (fun best S => (best = none → ∀ ℓ ∈ S, cur.slope ≤ ℓ.slope) ∧
      ∀ tc b, best = some (tc, b) → b ∈ lines ∧ b.slope < cur.slope ∧ tc = cur.crossing b ∧
        ∀ ℓ ∈ S, ℓ.slope < cur.slope → tc < cur.crossing ℓ ∨ (tc = cur.crossing ℓ ∧ b.slope ≤ ℓ.slope))
    lines.toList ?_ none [] ⟨by simp, by simp⟩
  · rw [List.nil_append, Array.foldl_toList] at key
    exact ⟨fun h ℓ hℓ => key.1 h ℓ (by simpa using hℓ),
      fun tc b h => by
        obtain ⟨h₁, h₂, h₃, h₄⟩ := key.2 tc b h
        exact ⟨h₁, h₂, h₃, fun ℓ hℓ => h₄ ℓ (by simpa using hℓ)⟩⟩
  · rintro best S a ha ⟨hnone, hsome⟩
    have ha' : a ∈ lines := by simpa using ha
    simp only [nextStep]
    split_ifs with hge
    · -- `a` does not have a smaller slope: nothing changes
      refine ⟨fun h ℓ hℓ => ?_, fun tc b h => ?_⟩
      · rcases List.mem_append.1 hℓ with hℓ | hℓ
        · exact hnone h ℓ hℓ
        · simp at hℓ; subst hℓ; exact hge
      · obtain ⟨h₁, h₂, h₃, h₄⟩ := hsome tc b h
        refine ⟨h₁, h₂, h₃, fun ℓ hℓ hlt => ?_⟩
        rcases List.mem_append.1 hℓ with hℓ | hℓ
        · exact h₄ ℓ hℓ hlt
        · simp at hℓ; subst hℓ; omega
    · have hlt : a.slope < cur.slope := lt_of_not_ge hge
      rcases best with _ | ⟨tb, b⟩
      · -- the first line with a smaller slope
        refine ⟨by simp, fun tc b h => ?_⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨ha', hlt, rfl, fun ℓ hℓ hℓlt => ?_⟩
        rcases List.mem_append.1 hℓ with hℓ | hℓ
        · exact absurd (hnone rfl ℓ hℓ) (not_le.2 hℓlt)
        · simp at hℓ; subst hℓ; exact Or.inr ⟨rfl, le_rfl⟩
      · obtain ⟨hb₁, hb₂, hb₃, hb₄⟩ := hsome tb b rfl
        simp only
        split_ifs with hc
        · -- `a` crosses earlier (or at the same time, with a smaller slope): it replaces `b`
          simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at hc
          refine ⟨by simp, fun tc c h => ?_⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨ha', hlt, rfl, fun ℓ hℓ hℓlt => ?_⟩
          rcases List.mem_append.1 hℓ with hℓ | hℓ
          · rcases hb₄ ℓ hℓ hℓlt with h | ⟨h₁, h₂⟩ <;> rcases hc with hc | ⟨hc₁, hc₂⟩
            · exact Or.inl (hc.trans h)
            · exact Or.inl (hc₁ ▸ h)
            · exact Or.inl (h₁ ▸ hc)
            · exact Or.inr ⟨hc₁.trans h₁, by omega⟩
          · simp at hℓ; subst hℓ; exact Or.inr ⟨rfl, le_rfl⟩
        · -- `b` stays
          simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq, not_or, not_and,
            not_lt] at hc
          refine ⟨by simp, fun tc c h => ?_⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨hb₁, hb₂, hb₃, fun ℓ hℓ hℓlt => ?_⟩
          rcases List.mem_append.1 hℓ with hℓ | hℓ
          · exact hb₄ ℓ hℓ hℓlt
          · simp at hℓ; subst hℓ
            rcases lt_or_eq_of_le hc.1 with h | h
            · exact Or.inl h
            · exact Or.inr ⟨h, hc.2 h.symm⟩

/-- The number of lines with a smaller slope than `cur`: an upper bound on the switches left. -/
def countLower (lines : Array Line) (cur : Line) : Nat :=
  lines.toList.countP fun ℓ => decide (ℓ.slope < cur.slope)

/-- `countP p < countP q` when `p` implies `q` and some element has `q` but not `p`. -/
theorem countP_lt_of_imp {α : Type} (l : List α) (p q : α → Bool)
    (himp : ∀ x ∈ l, p x = true → q x = true) (hx : ∃ x ∈ l, q x = true ∧ p x = false) :
    l.countP p < l.countP q := by
  induction l with
  | nil => obtain ⟨x, hx, -⟩ := hx; simp at hx
  | cons y ys ih =>
    have hmono : ys.countP p ≤ ys.countP q :=
      List.countP_mono_left fun x hx hp => himp x (by simp [hx]) hp
    simp only [List.countP_cons]
    obtain ⟨x, hxmem, hqx, hpx⟩ := hx
    rcases List.mem_cons.1 hxmem with rfl | hxs
    · simp only [hqx, hpx]; simp; omega
    · have := ih (fun z hz hp => himp z (by simp [hz]) hp) ⟨x, hxs, hqx, hpx⟩
      cases hp : p y <;> cases hq : q y <;> simp <;> try omega
      exact absurd (himp y (by simp) hp) (by simp [hq])

theorem countLower_lt (lines : Array Line) (cur b : Line) (hb : b ∈ lines) (hlt : b.slope < cur.slope) :
    countLower lines b < countLower lines cur :=
  countP_lt_of_imp _ _ _ (fun x _ hx => by simp at hx ⊢; omega) ⟨b, by simpa using hb, by simpa using hlt, by simp⟩

theorem countLower_lt_size (lines : Array Line) (cur : Line) (hcur : cur ∈ lines) :
    countLower lines cur < lines.size := by
  have := countP_lt_of_imp lines.toList (fun ℓ => decide (ℓ.slope < cur.slope)) (fun _ => true)
    (fun _ _ _ => rfl) ⟨cur, by simpa using hcur, rfl, by simp⟩
  simpa [countLower, List.countP_true] using this

/-- **The walk is correct.** From a line that is lowest at `t`, with `total = ∫₀ᵗ` of the
envelope and enough switches left, the walk returns `∫₀¹` of the envelope. -/
theorem go_correct (lines : Array Line) (k : Nat) :
    ∀ (cur : Line) (t total : Rat), Lowest lines cur t → 0 ≤ t → t < 1 →
      countLower lines cur < k → (total : ℝ) = ∫ s in (0 : ℝ)..t, envR lines s →
      (lowerEnvelopeIntegral.go lines k cur t total : ℝ) = ∫ s in (0 : ℝ)..1, envR lines s := by
  induction k with
  | zero => intro cur t total _ _ _ hk; omega
  | succ k ih =>
    intro cur t total hlow ht0 ht1 hk htot
    obtain ⟨hcur, hmin⟩ := hlow
    -- a line with at least `cur`'s slope stays above it after `t`
    have hrise : ∀ ℓ ∈ lines, cur.slope ≤ ℓ.slope → ∀ s : ℝ, (t : ℝ) ≤ s → cur.ev s ≤ ℓ.ev s := by
      intro ℓ hℓ hsl s hts
      have h1 := (hmin ℓ hℓ).1
      have h2 : (0 : ℝ) ≤ (ℓ.slope : ℝ) - cur.slope := sub_nonneg.2 (by exact_mod_cast hsl)
      have : ℓ.ev s - cur.ev s = (ℓ.ev t - cur.ev t) + ((ℓ.slope : ℝ) - cur.slope) * (s - t) := by
        simp only [Line.ev]; ring
      nlinarith [mul_nonneg h2 (sub_nonneg.2 hts)]
    -- where `cur` is lowest on `[a, b]`, its integral there is the envelope's
    have piece : ∀ a b : ℚ, a ≤ b → (∀ s : ℝ, (a : ℝ) ≤ s → s ≤ b → ∀ ℓ ∈ lines, cur.ev s ≤ ℓ.ev s) →
        (cur.integral a b : ℝ) = ∫ s in (a : ℝ)..b, envR lines s := by
      intro a b hab hlowab
      rw [Line.integral_eq]
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le (by exact_mod_cast hab)] at hs
      exact (envR_eq lines cur hcur s (hlowab s hs.1 hs.2)).symm
    -- finishing: `total + ∫ₜ¹ cur = ∫₀¹` of the envelope
    have finish : (∀ s : ℝ, (t : ℝ) ≤ s → s ≤ 1 → ∀ ℓ ∈ lines, cur.ev s ≤ ℓ.ev s) →
        ((total + cur.integral t 1 : ℚ) : ℝ) = ∫ s in (0 : ℝ)..1, envR lines s := by
      intro hseg
      rw [Rat.cast_add, htot, piece t 1 ht1.le (by simpa using hseg), Rat.cast_one,
        intervalIntegral.integral_add_adjacent_intervals (integrable_envR lines 0 t) (integrable_envR lines t 1)]
    obtain ⟨hnone, hsome⟩ := nextStep_spec lines cur
    rw [go_succ]
    split
    · rename_i tc b hnext
      obtain ⟨hb, hblt, htc, hfirst⟩ := hsome tc b hnext
      -- lines with a smaller slope are strictly above `cur` at `t`, so they cross later
      have hcross_gt : ∀ ℓ ∈ lines, ℓ.slope < cur.slope → (t : ℝ) < (cur.crossing ℓ : ℝ) := by
        intro ℓ hℓ hℓlt
        have hne : cur.slope ≠ ℓ.slope := by omega
        have hstrict : cur.ev t < ℓ.ev t := by
          rcases lt_or_eq_of_le (hmin ℓ hℓ).1 with h | h
          · exact h
          · exact absurd ((hmin ℓ hℓ).2 h) (by omega)
        have hdiff := Line.ev_sub_ev cur ℓ hne t
        have hsl : (ℓ.slope : ℝ) - cur.slope < 0 := sub_neg.2 (by exact_mod_cast hℓlt)
        by_contra hle
        rw [not_lt] at hle
        nlinarith [mul_nonneg (neg_nonneg.2 hsl.le) (sub_nonneg.2 hle)]
      have htlt : t < tc := by rw [htc]; exact_mod_cast hcross_gt b hb hblt
      -- `cur` stays lowest up to the first crossing
      have hseg : ∀ s : ℝ, (t : ℝ) ≤ s → s ≤ tc → ∀ ℓ ∈ lines, cur.ev s ≤ ℓ.ev s := by
        intro s hts hstc ℓ hℓ
        by_cases hsl : cur.slope ≤ ℓ.slope
        · exact hrise ℓ hℓ hsl s hts
        · have hℓlt : ℓ.slope < cur.slope := lt_of_not_ge hsl
          have hc : (tc : ℝ) ≤ cur.crossing ℓ := by
            rcases hfirst ℓ hℓ hℓlt with h | ⟨h, -⟩
            · exact_mod_cast h.le
            · exact_mod_cast h.le
          have hdiff := Line.ev_sub_ev cur ℓ (by omega) s
          have hsl' : (ℓ.slope : ℝ) - cur.slope ≤ 0 := sub_nonpos.2 (by exact_mod_cast hℓlt.le)
          nlinarith [mul_nonneg_of_nonpos_of_nonpos hsl' (by linarith : s - (cur.crossing ℓ : ℝ) ≤ 0)]
      rw [max_eq_right htlt.le]
      split_ifs with hge
      · exact finish fun s hts hs1 => hseg s hts (hs1.trans (by exact_mod_cast hge))
      · have htc1 : tc < 1 := lt_of_not_ge hge
        have htle : (t : ℝ) ≤ tc := by exact_mod_cast htlt.le
        refine ih b tc _ ⟨hb, fun ℓ hℓ => ?_⟩ (ht0.trans htlt.le) htc1 ?_ ?_
        · -- `b` is lowest at `tc`: it meets `cur` there, and wins the tie-break
          have hbeq : b.ev tc = cur.ev tc := by
            have h := Line.ev_sub_ev cur b (by omega) tc
            rw [← htc, sub_self, mul_zero] at h
            linarith
          have hle := hseg tc htle le_rfl ℓ hℓ
          refine ⟨hbeq ▸ hle, fun heq => ?_⟩
          by_cases hsl : cur.slope ≤ ℓ.slope
          · omega
          · have hℓlt : ℓ.slope < cur.slope := lt_of_not_ge hsl
            have h0 : (ℓ.slope : ℝ) - cur.slope ≠ 0 := sub_ne_zero.2 (by exact_mod_cast (show ℓ.slope ≠ cur.slope by omega))
            have hcℓ : (cur.crossing ℓ : ℝ) = tc := by
              have h1 := Line.ev_sub_ev cur ℓ (by omega) tc
              have hz : ((ℓ.slope : ℝ) - cur.slope) * (tc - cur.crossing ℓ) = 0 := by rw [← h1]; linarith
              rcases mul_eq_zero.1 hz with h | h
              · exact absurd h h0
              · linarith
            rcases hfirst ℓ hℓ hℓlt with h | ⟨-, h⟩
            · have : (tc : ℝ) < cur.crossing ℓ := by exact_mod_cast h
              linarith
            · exact h
        · have := countLower_lt lines cur b hb hblt
          omega
        · rw [Rat.cast_add, htot, piece t tc htlt.le hseg,
            intervalIntegral.integral_add_adjacent_intervals (integrable_envR lines 0 t) (integrable_envR lines t tc)]
    · rename_i hnext
      exact finish fun s hts _ ℓ hℓ => hrise ℓ hℓ (hnone hnext ℓ hℓ) s hts

/-- **The envelope walk computes the integral of the lower envelope.** -/
theorem lowerEnvelopeIntegral_eq_integral (lines : Array Line) (hne : 0 < lines.size) :
    (lowerEnvelopeIntegral lines : ℝ) = ∫ s in (0 : ℝ)..1, envR lines s := by
  rw [lowerEnvelopeIntegral_eq_go]
  have hstart := start_lowest lines hne
  refine go_correct lines lines.size _ 0 0 (by simpa using hstart) le_rfl (by norm_num)
    (countLower_lt_size lines _ hstart.1) (by simp)

end PolyFit
