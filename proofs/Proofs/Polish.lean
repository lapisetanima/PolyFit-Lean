import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PolyFit.Polish

/-!
# The local search `polish`: honest scores and the certificate

`polish` (the fine and ultra-fine searches, for every `n ≥ 2`) starts from a polygon and
only moves vertices by unit offsets. Write `F²(Q) = objectivePolygon pts (diamSq pts) Q
missing`, the *computed* objective (exact rationals; that it equals the true `F²` is a
separate, later theorem), and `r = polish pts missing start fuel ultraMax`.

**Theorems** (section E):
1. `polish_size`: `r.vertices` has as many vertices as `start`;
2. `polish_objectiveSq`: `r.objectiveSq = F²(r.vertices)`;
3. `polish_le_start`: `r.objectiveSq ≤ F²(start)`;
4. **`polish_certified`:** if `diam(P) > 0` and `r.certified`, then `r.objectiveSq ≤ F²(Q')`
   for every polygon `Q'` in the unit cube around `r.vertices`.

`diam(P) > 0` is needed: otherwise the `D₁` part divides by 0, `objectiveBelow` rejects
every candidate, and the search would "certify" any polygon. The neighbours `Q'` include
polygons with zero-length edges, scored with the stand-in `L² := 1`.

**Proof outline.**
* *A. Nothing is negative.* Every point-to-edge distance and every computed `D₂` is
  `≥ 0`, so `F² ≥ 0`. For `D₂` (`segmentIntegral_nonneg`): the envelope walk cuts
  `[0, 1]` into ordered pieces and integrates one line `ℓ_p` on each
  (`lowerEnvelopeIntegral_add_nonneg`), and `L² t² + ℓ_p(t) = |q₀ + t v − p|² ≥ 0`, so each
  piece adds `∫ |q₀ + t v − p|² dt ≥ 0` (`integral_sq_nonneg`). This is what makes the
  whole-number lower bounds of the ultra-fine step sound.
* *B. Early exits are exact* (`objectiveBelow_some`, `objectiveBelow_none`): a value is
  only returned when it is the exact objective and below the bound, and `none` only
  when the exact objective is `≥` the bound.
* *C. Each move picks the best candidate* (`bestFineMove_*`, `bestCubeMove_*`): cached
  and tabulated edge pieces equal recomputed ones, so every candidate is scored as
  `F²` of that candidate; `none` means no candidate beats `f`. The ultra-fine step
  visits all `9ⁿ` offset choices (`foldOffsetChoices`). For `n = 2` the fine moves are
  already the whole cube (`fineMoves_two`).
* *D. The fine search* (`fineSearch_spec`): by induction on the moves left, it keeps
  `f = F²(q)` and the vertex count, never increases `f`, and when it converges no fine
  move beats `f`.
* *E. `polish`*: by induction on the rounds left, from B–D; certification happens only
  when the last fine search converged and (for `n ≥ 3`) the ultra-fine step found
  nothing better, or (for `n = 2`) when the fine moves were already the whole cube.
-/

namespace PolyFit

/-! ## Vocabulary -/

/-- `δ ∈ {-1, 0, 1}²`. -/
def IsUnitOffset (δ : Pt) : Prop := |δ.i| ≤ 1 ∧ |δ.j| ≤ 1

/-- `q'` is in the unit cube around `q`: the same number of vertices, each moved by a
unit offset (possibly `(0, 0)`). -/
def InUnitCube (q q' : Array Pt) : Prop :=
  ∃ d : Array Pt, d.size = q.size ∧ (∀ δ ∈ d, IsUnitOffset δ) ∧ q' = Array.zipWith (· + ·) q d

/-! ## A. Nothing is negative -/

/-- `d₁(p, ℓ)² ≥ 0`.

Proof: the three branches of `distSqToSegment` are a `Nat` cast, a `Nat` cast,
and `(w × v)² / |v|²` with `|v|² > 0` in that branch. -/
theorem distSqToSegment_nonneg (p q₀ q₁ : Pt) : 0 ≤ distSqToSegment p q₀ q₁ := by
  simp only [distSqToSegment]
  split_ifs with h₁ h₂
  · positivity
  · positivity
  · -- the last branch has `0 < w · v < |v|²`
    exact div_nonneg (by positivity) (by exact_mod_cast (by omega : (0 : Int) ≤ dot (q₁ - q₀) (q₁ - q₀)))

/-- One piece of the `D₂` integral: for the line `t ↦ 2 (u · v) t + |u|²` coming from a
point `p` (with `u = q₀ - p`), adding `∫ₛᵉ |v|² t² dt` gives `∫ₛᵉ |u + t v|² dt ≥ 0`.

Proof: each coordinate contributes `∫ₛᵉ (a + b t)² dt = (e - s)(x² + x y + y²)/3`
with `x = a + b s`, `y = a + b e`, and `x² + x y + y² ≥ 0`; a polynomial identity (`ring`)
plus `nlinarith` for `x² + x y + y² ≥ 0`. -/
theorem integral_sq_nonneg (u v : Pt) (s e : Rat) (hse : s ≤ e) :
    0 ≤ (dot v v : Rat) * (e ^ 3 - s ^ 3) / 3 + (⟨2 * dot u v, dot u u⟩ : Line).integral s e := by
  -- One coordinate: `∫ₛᵉ (a + b t)² dt = (e - s)(x² + x y + y²)/3`, with `x² + x y + y² ≥ 0`.
  have one : ∀ a b : Rat, 0 ≤ b ^ 2 * (e ^ 3 - s ^ 3) / 3 + a * b * (e * e - s * s) + a ^ 2 * (e - s) := by
    intro a b
    have hxy : 0 ≤ (a + b * s) ^ 2 + (a + b * s) * (a + b * e) + (a + b * e) ^ 2 := by
      nlinarith [sq_nonneg (a + b * s + (a + b * e)), sq_nonneg (a + b * s), sq_nonneg (a + b * e)]
    have key : b ^ 2 * (e ^ 3 - s ^ 3) / 3 + a * b * (e * e - s * s) + a ^ 2 * (e - s)
        = (e - s) * ((a + b * s) ^ 2 + (a + b * s) * (a + b * e) + (a + b * e) ^ 2) / 3 := by
      ring
    rw [key]
    exact div_nonneg (mul_nonneg (sub_nonneg.2 hse) hxy) (by norm_num)
  -- The whole integrand is the `i` square plus the `j` square.
  convert add_nonneg (one u.i v.i) (one u.j v.j) using 1
  simp only [Line.integral, dot]
  push_cast
  ring

/-- A property kept by every step of a `foldl` holds for its result. -/
theorem foldl_preserves {α β : Type} (P : β → Prop) (f : β → α → β) (l : List α) (init : β)
    (h0 : P init) (hf : ∀ b a, a ∈ l → P b → P (f b a)) : P (l.foldl f init) := by
  induction l generalizing init with
  | nil => exact h0
  | cons x xs ih =>
    exact ih (f init x) (hf init x (by simp) h0) fun b a ha hb => hf b a (by simp [ha]) hb

/-- `foldl_preserves` for arrays. -/
theorem foldl_preserves' {α β : Type} (P : β → Prop) (f : β → α → β) (arr : Array α)
    (init : β) (h0 : P init) (hf : ∀ b a, a ∈ arr → P b → P (f b a)) : P (arr.foldl f init) := by
  rw [← Array.foldl_toList]
  exact PolyFit.foldl_preserves P f arr.toList init h0 fun b a ha hb => hf b a (by simpa using ha) hb

/-- The step of the envelope walk, with the invariant
"`total + A t³/3 ≥ 0`, `0 ≤ t ≤ 1`, and `cur` is one of the lines". -/
theorem lowerEnvelopeIntegral_go_nonneg (lines : Array Line) (A : Rat)
    (h : ∀ ℓ ∈ lines, ∀ s e : Rat, 0 ≤ s → s ≤ e → e ≤ 1 → 0 ≤ A * (e ^ 3 - s ^ 3) / 3 + ℓ.integral s e)
    (k : Nat) : ∀ (cur : Line) (t total : Rat), cur ∈ lines → 0 ≤ t → t ≤ 1 →
      0 ≤ total + A * t ^ 3 / 3 → 0 ≤ A / 3 + lowerEnvelopeIntegral.go lines k cur t total := by
  induction k with
  | zero =>
    intro cur t total hcur ht0 ht1 htot
    have last := h cur hcur t 1 ht0 ht1 le_rfl
    simp only [lowerEnvelopeIntegral.go]
    linarith
  | succ k ih =>
    intro cur t total hcur ht0 ht1 htot
    have last := h cur hcur t 1 ht0 ht1 le_rfl
    simp only [lowerEnvelopeIntegral.go]
    split
    · rename_i tc ℓ hnext
      -- The next line is one of the lines: the search only ever stores a line it scans.
      have hℓ : ℓ ∈ lines := by
        refine (foldl_preserves' (fun best : Option (Rat × Line) => ∀ x, best = some x → x.2 ∈ lines)
          _ lines none (by simp) ?_) (tc, ℓ) hnext
        intro b a ha hb x hx
        split_ifs at hx
        · exact hb x hx
        · split at hx
          · split_ifs at hx
            · cases hx; exact ha
            · exact hb x hx
          · cases hx; exact ha
      split_ifs with hge
      · linarith
      · -- integrate `cur` from `t` to the (clamped) switch time, then continue
        have hlt : max t tc < 1 := lt_of_not_ge hge
        have piece := h cur hcur t (max t tc) ht0 (le_max_left _ _) hlt.le
        exact ih ℓ (max t tc) _ hℓ (ht0.trans (le_max_left _ _)) hlt.le (by linarith)
    · linarith

/-- The envelope walk integrates one of its lines on each of a sequence of ordered pieces
`0 = t₀ ≤ … ≤ t_k = 1`. So if every line `ℓ`, together with the quadratic `A t²`, has a
nonnegative integral over every subinterval of `[0, 1]`, the total `A/3 + walk` is `≥ 0`
(whether or not the walk picked the lowest line).

Proof: induction on the switches left in `lowerEnvelopeIntegral.go`, with the
invariant "`total` plus `A t³/3` is `≥ 0`, `0 ≤ t ≤ 1`, and `cur` is one of the lines";
the `max t tc` clamp gives `t ≤ tc`. With no lines, the walk integrates the default line
`0`, which is why `A ≥ 0` is assumed. -/
theorem lowerEnvelopeIntegral_add_nonneg (lines : Array Line) (A : Rat) (hA : 0 ≤ A)
    (h : ∀ ℓ ∈ lines, ∀ s e : Rat, 0 ≤ s → s ≤ e → e ≤ 1 → 0 ≤ A * (e ^ 3 - s ^ 3) / 3 + ℓ.integral s e) :
    0 ≤ A / 3 + lowerEnvelopeIntegral lines := by
  unfold lowerEnvelopeIntegral
  by_cases hne : lines.size = 0
  · -- No lines: the walk integrates the default line `0`.
    obtain rfl : lines = #[] := Array.size_eq_zero_iff.1 hne
    have hd : (default : Line) = ⟨0, 0⟩ := rfl
    simp [lowerEnvelopeIntegral.go, Line.integral, hd]
    positivity
  · -- The starting line is one of the lines.
    have h0 : lines[0]! ∈ lines := by
      rw [getElem!_pos lines 0 (by omega)]
      exact Array.getElem_mem (by omega)
    refine lowerEnvelopeIntegral_go_nonneg lines A h _ _ 0 0 ?_ le_rfl (by norm_num) (by norm_num)
    refine foldl_preserves' (· ∈ lines) _ lines _ h0 ?_
    intro b a ha hb
    split_ifs
    · exact ha
    · exact hb

/-- `|v|² ≥ 0`. -/
theorem dot_self_nonneg (v : Pt) : 0 ≤ dot v v := by
  simp only [dot]
  nlinarith [mul_self_nonneg v.i, mul_self_nonneg v.j]

/-- The computed `∫₀¹ d₁(q₀ + t v, P)² dt` is `≥ 0`.

Proof: `lowerEnvelopeIntegral_add_nonneg` with `A = |v|²`, and `integral_sq_nonneg` for
each point's line. -/
theorem segmentIntegral_nonneg (pts : Array Pt) (q₀ q₁ : Pt) : 0 ≤ segmentIntegral pts q₀ q₁ := by
  unfold segmentIntegral
  refine lowerEnvelopeIntegral_add_nonneg _ _ (by exact_mod_cast dot_self_nonneg _) ?_
  intro ℓ hℓ s e _ hse _
  obtain ⟨p, -, rfl⟩ := Array.mem_map.1 hℓ
  exact integral_sq_nonneg (q₀ - p) (q₁ - q₀) s e hse

/-- `D₂(ℓ, P)² ≥ 0`.

Proof: `segmentIntegral_nonneg`, divided by `|v|² ≥ 0` (or by 1). -/
theorem d2Sq_nonneg (pts : Array Pt) (q₀ q₁ : Pt) : 0 ≤ d2Sq pts q₀ q₁ := by
  simp only [d2Sq]
  apply div_nonneg (segmentIntegral_nonneg pts q₀ q₁)
  have := dot_self_nonneg (q₁ - q₀)
  split_ifs
  · norm_num
  · exact_mod_cast this

/-- Edge pieces with nothing negative: every edge that `edgeTerms` builds, and the
default (empty) one. -/
def EdgeTerms.Nonneg (t : EdgeTerms) : Prop := (∀ x ∈ t.distSqs, 0 ≤ x) ∧ 0 ≤ t.d2

theorem edgeTerms_nonneg (pts : Array Pt) (a b : Pt) : (edgeTerms pts a b).Nonneg := by
  refine ⟨?_, d2Sq_nonneg pts a b⟩
  intro x hx
  obtain ⟨p, -, rfl⟩ := Array.mem_map.1 hx
  exact distSqToSegment_nonneg p a b

/-- An entry `arr[i]!` of an array with nothing negative is `≥ 0` (out of range it is 0). -/
theorem getElem!_nonneg (arr : Array Rat) (h : ∀ x ∈ arr, 0 ≤ x) (i : Nat) : 0 ≤ arr[i]! := by
  by_cases hi : i < arr.size
  · rw [getElem!_pos arr i hi]
    exact h _ (Array.getElem_mem hi)
  · rw [getElem!_neg arr i hi]
    rfl

/-- `edges[i]!` has nothing negative if no edge does (out of range it is the default). -/
theorem getElem!_edge_nonneg (edges : Array EdgeTerms) (h : ∀ e ∈ edges, e.Nonneg) (i : Nat) :
    edges[i]!.Nonneg := by
  by_cases hi : i < edges.size
  · rw [getElem!_pos edges i hi]
    exact h _ (Array.getElem_mem hi)
  · rw [getElem!_neg edges i hi]
    exact ⟨by simp [show (default : EdgeTerms).distSqs = #[] from rfl], le_rfl⟩

/-- `d₁(p, Q)² ≥ 0`: a minimum of terms that are `≥ 0`. -/
theorem nearestSq_nonneg (edges : Array EdgeTerms) (h : ∀ e ∈ edges, e.Nonneg) (idx : Nat) :
    0 ≤ nearestSq edges idx := by
  unfold nearestSq
  refine foldl_preserves' (0 ≤ ·) _ edges _ (getElem!_nonneg _ (getElem!_edge_nonneg edges h 0).1 idx) ?_
  intro b e he hb
  exact le_min hb (getElem!_nonneg _ (h e he).1 idx)

/-- `F² ≥ 0` from edge pieces with nothing negative. -/
theorem objectiveFromEdges_nonneg (numPts diam2 : Nat) (edges : Array EdgeTerms)
    (h : ∀ e ∈ edges, e.Nonneg) : 0 ≤ objectiveFromEdges numPts diam2 edges := by
  simp only [objectiveFromEdges]
  refine add_nonneg (div_nonneg (div_nonneg ?_ (Nat.cast_nonneg _)) (by norm_num))
    (div_nonneg ?_ (Nat.cast_nonneg _))
  · exact foldl_preserves (0 ≤ ·) _ _ _ le_rfl fun b idx _ hb => add_nonneg hb (nearestSq_nonneg edges h idx)
  · exact foldl_preserves' (0 ≤ ·) _ _ _ le_rfl fun b e he hb => add_nonneg hb (h e he).2

/-- The computed `F² ≥ 0`.

Proof: every edge piece comes from `edgeTerms`, so `objectiveFromEdges_nonneg` applies. -/
theorem objectivePolygon_nonneg (pts : Array Pt) (diam2 : Nat) (qs : Array Pt) (missing : List Nat) :
    0 ≤ objectivePolygon pts diam2 qs missing := by
  unfold objectivePolygon
  apply objectiveFromEdges_nonneg
  intro t ht
  obtain ⟨e, -, rfl⟩ := Array.mem_map.1 ht
  exact edgeTerms_nonneg _ _ _





/-! ## B. Early exits are exact -/

/-- The `D₁` sum over the points numbered `idx, …, idx + left - 1`, added to `total`, the way
`objectiveBelow` and `objectiveFromEdges` add it up. -/
abbrev d1Sum (edges : Array EdgeTerms) (left idx : Nat) (total : Rat) : Rat :=
  (List.range' idx left).foldl (fun s i => s + nearestSq edges i) total

/-- Adding terms that are `≥ 0` never lowers the total. -/
theorem le_d1Sum (edges : Array EdgeTerms) (h : ∀ e ∈ edges, e.Nonneg) (left idx : Nat) (total : Rat) :
    total ≤ d1Sum edges left idx total :=
  foldl_preserves (total ≤ ·) _ _ _ le_rfl fun _ i _ hb =>
    le_add_of_le_of_nonneg hb (nearestSq_nonneg edges h i)

/-- If the point-by-point sum runs to the end, it returns the whole sum, and that sum
stays below the limit (given that it starts below it). -/
theorem objectiveBelow_go_some (edges : Array EdgeTerms) (limit : Option Rat) (left : Nat) :
    ∀ (idx : Nat) (total v : Rat), (∀ l ∈ limit, total < l) →
      objectiveBelow.go edges limit left idx total = some v →
      v = d1Sum edges left idx total ∧ ∀ l ∈ limit, v < l := by
  induction left with
  | zero =>
    intro idx total v hlt h
    simp only [objectiveBelow.go, Option.some.injEq] at h
    subst h
    exact ⟨rfl, hlt⟩
  | succ left ih =>
    intro idx total v hlt h
    simp only [objectiveBelow.go] at h
    split_ifs at h with hreach
    -- not reached: the new total is still below the limit
    have hlt' : ∀ l ∈ limit, total + nearestSq edges idx < l := by
      intro l hl
      cases hl
      simpa using hreach
    obtain ⟨hv, hvl⟩ := ih (idx + 1) _ v hlt' h
    exact ⟨by rw [hv, d1Sum, d1Sum, List.range'_succ, List.foldl_cons], hvl⟩

/-- If the point-by-point sum gives up, the whole sum reaches the limit. -/
theorem objectiveBelow_go_none (edges : Array EdgeTerms) (h : ∀ e ∈ edges, e.Nonneg)
    (limit : Option Rat) (left : Nat) :
    ∀ (idx : Nat) (total : Rat), objectiveBelow.go edges limit left idx total = none →
      ∃ l ∈ limit, l ≤ d1Sum edges left idx total := by
  induction left with
  | zero =>
    intro idx total hnone
    simp [objectiveBelow.go] at hnone
  | succ left ih =>
    intro idx total hnone
    simp only [objectiveBelow.go] at hnone
    rw [d1Sum, List.range'_succ, List.foldl_cons]
    split_ifs at hnone with hreach
    · -- reached here; the rest of the sum only adds terms `≥ 0`
      cases limit with
      | none => simp at hreach
      | some l =>
        refine ⟨l, rfl, le_trans (by simpa using hreach) (le_d1Sum edges h left (idx + 1) _)⟩
    · exact ih (idx + 1) _ hnone

/-- `objectiveFromEdges` with its `D₁` sum written as `d1Sum`. -/
theorem objectiveFromEdges_eq (numPts diam2 : Nat) (edges : Array EdgeTerms) :
    objectiveFromEdges numPts diam2 edges
      = d1Sum edges numPts 0 0 / (numPts * diam2 : Nat) / 2
        + edges.foldl (init := (0 : Rat)) (· + ·.d2) / (2 * edges.size : Nat) := by
  simp only [objectiveFromEdges, d1Sum, List.range_eq_range']

/-- A value from `objectiveBelow` is the exact objective, and below the bound if there is one.

Proof: the value is `d1Total / (2 k D) + d2Part` with `d1Total` the whole `D₁` sum
(`objectiveBelow_go_some`), which is `objectiveFromEdges` rearranged; and `d1Total` is
below `(b - d2Part) · 2 k D`, which is positive, since otherwise `objectiveBelow` would
have given up at once. -/
theorem objectiveBelow_some (numPts diam2 : Nat) (edges : Array EdgeTerms) (bound : Option Rat)
    (v : Rat) (h : objectiveBelow numPts diam2 edges bound = some v) :
    v = objectiveFromEdges numPts diam2 edges ∧ ∀ b ∈ bound, v < b := by
  simp only [objectiveBelow] at h
  split_ifs at h with hzero
  obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.1 h
  -- the limit is positive (`hzero`), so the sum starts below it
  have hpos : ∀ l ∈ Option.map (fun b => (b - edges.foldl (init := (0 : Rat)) (· + ·.d2)
      / (2 * edges.size : Nat)) * (2 * numPts * diam2 : Nat)) bound, (0 : Rat) < l := by
    intro l hl
    cases bound with
    | none => cases hl
    | some b => cases hl; simpa using hzero
  obtain ⟨hw', hwl⟩ := objectiveBelow_go_some edges _ numPts 0 0 w hpos hw
  refine ⟨?_, ?_⟩
  · rw [hw', objectiveFromEdges_eq]
    push_cast
    ring
  · intro b hb
    cases hb
    have hl := hwl _ rfl
    have hl0 := hpos _ rfl
    beta_reduce at hl hl0
    -- `2 k D > 0`, as the limit `(b - d2Part) · 2 k D` is positive
    have hscale : (0 : Rat) < (2 * numPts * diam2 : Nat) := by
      rcases (Nat.cast_nonneg (α := Rat) (2 * numPts * diam2)).lt_or_eq with hs | hs
      · exact hs
      · rw [← hs, mul_zero] at hl0; exact absurd hl0 (lt_irrefl 0)
    rw [div_add' _ _ _ hscale.ne', div_lt_iff₀ hscale]
    linarith

/-- `objectiveBelow` gives up only when the exact objective is `≥` the bound.

Proof: either `(b - d2Part) · scale ≤ 0`, so `b ≤ d2Part ≤ F²` (the `D₁` part is `≥ 0`);
or a partial `D₁` sum reached the limit, and the remaining terms are `≥ 0`
(`objectiveBelow_go_none`). Both need `scale = 2 k D > 0`. -/
theorem objectiveBelow_none (numPts diam2 : Nat) (edges : Array EdgeTerms) (b : Rat)
    (hpos : 0 < numPts * diam2) (hnn : ∀ e ∈ edges, e.Nonneg)
    (h : objectiveBelow numPts diam2 edges (some b) = none) :
    b ≤ objectiveFromEdges numPts diam2 edges := by
  have hscale : (0 : Rat) < (2 * numPts * diam2 : Nat) := by
    exact_mod_cast (by rw [Nat.mul_assoc]; omega : 0 < 2 * numPts * diam2)
  have hd1 : 0 ≤ d1Sum edges numPts 0 0 := le_d1Sum edges hnn numPts 0 0
  rw [objectiveFromEdges_eq]
  have key : ∀ x : Rat, x / (numPts * diam2 : Nat) / 2 = x / (2 * numPts * diam2 : Nat) := by
    intro x; push_cast; ring
  rw [key]
  simp only [objectiveBelow] at h
  split_ifs at h with hzero
  · -- the `D₂` part alone reaches the bound
    simp only [Option.map_some, Option.any_some, decide_eq_true_eq] at hzero
    have : b ≤ edges.foldl (init := (0 : Rat)) (· + ·.d2) / (2 * edges.size : Nat) := by
      by_contra hlt
      have := mul_pos (sub_pos.2 (lt_of_not_ge hlt)) hscale
      linarith
    linarith [div_nonneg hd1 hscale.le]
  · -- the `D₁` sum reached the limit along the way
    obtain ⟨l, hl, hle⟩ := objectiveBelow_go_none edges hnn _ numPts 0 0 (Option.map_eq_none_iff.1 h)
    cases hl
    have :(b - edges.foldl (init := (0 : Rat)) (· + ·.d2) / (2 * edges.size : Nat))
        ≤ d1Sum edges numPts 0 0 / (2 * numPts * diam2 : Nat) := (le_div_iff₀ hscale).2 hle
    linarith

/-! ## C. Each move picks the best candidate -/

/-- Present edges are edges of the polygon: `e < n`. -/
theorem lt_of_mem_presentEdges {n : Nat} {missing : List Nat} {e : Nat}
    (h : e ∈ presentEdges n missing) : e < n := by
  unfold presentEdges at h
  split at h
  · rename_i hn
    simp at h hn
    omega
  · simp at h
    exact h.1

/-- A fine move keeps the vertex count and changes only the vertices it lists. -/
theorem fineMoves_spec (q : Array Pt) :
    ∀ c ∈ fineMoves q, c.1.size = q.size ∧ ∀ i, i ∉ c.2 → c.1[i]! = q[i]! := by
  intro c hc
  simp only [fineMoves] at hc
  rcases List.mem_append.1 hc with h | h
  · -- moving the two endpoints of one edge
    simp only [List.mem_flatMap, List.mem_map] at h
    obtain ⟨e, -, d₀, -, d₁, -, rfl⟩ := h
    refine ⟨by simp, fun i hi => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    have h₁ : e ≠ i := fun h => hi.1 h.symm
    have h₂ : (e + 1) % q.size ≠ i := fun h => hi.2 h.symm
    simp [Array.set!, getElem!_def, h₁, h₂]
  · -- translating the whole polygon
    split at h
    · simp at h
    · simp only [List.mem_map] at h
      obtain ⟨d, -, rfl⟩ := h
      refine ⟨by simp, fun i hi => ?_⟩
      have hi' : q.size ≤ i := by simpa using hi
      simp [getElem!_def, Array.getElem?_map, Array.getElem?_eq_none hi']

/-- The edges `bestFineMove` scores for a fine move, cached or recomputed, are exactly
`edgeTerms` of the candidate's present edges. -/
theorem fineMove_edges (pts : Array Pt) (missing : List Nat) (q : Array Pt)
    (c : Array Pt × List Nat) (hc : c ∈ fineMoves q) :
    (presentEdges q.size missing).toArray.map (fun e =>
      if c.2.contains e || c.2.contains ((e + 1) % q.size) then
        edgeTerms pts c.1[e]! c.1[(e + 1) % q.size]!
      else (edgeCache pts q (presentEdges q.size missing))[e]!)
    = (presentEdges c.1.size missing).toArray.map
        fun e => edgeTerms pts c.1[e]! c.1[(e + 1) % c.1.size]! := by
  obtain ⟨hsize, hsame⟩ := fineMoves_spec q c hc
  rw [hsize]
  apply Array.map_congr_left
  intro e he
  rw [List.mem_toArray] at he
  split
  · rfl
  · rename_i hch
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hch
    have hlt := lt_of_mem_presentEdges he
    rw [hsame e (by simpa using hch.1), hsame _ (by simpa using hch.2)]
    simp [edgeCache, getElem!_def, hlt]
    exact fun hnot => absurd he hnot

/-- A fine move is strictly better, keeps the vertex count, and is scored honestly.

Proof: along the fold, the current best is always a fine move, strictly better than `f`,
scored with `objectiveBelow` (`objectiveBelow_some`) on its own edges (`fineMove_edges`);
a new candidate must beat the current best, which is at most `f`. -/
theorem bestFineMove_some (pts : Array Pt) (diam2 : Nat) (missing : List Nat) (q q' : Array Pt)
    (f f' : Rat) (h : bestFineMove pts diam2 (presentEdges q.size missing) q f = some (q', f')) :
    f' < f ∧ q'.size = q.size ∧ f' = objectivePolygon pts diam2 q' missing := by
  unfold bestFineMove at h
  refine (foldl_preserves (fun best : Option (Array Pt × Rat) => ∀ c g, best = some (c, g) →
      g < f ∧ c.size = q.size ∧ g = objectivePolygon pts diam2 c missing)
    _ _ none (by simp) ?_) q' f' h
  rintro best ⟨cand, changed⟩ hmem hbest c g hcg
  obtain ⟨hsize, -⟩ := fineMoves_spec q _ hmem
  dsimp only at hcg
  split at hcg
  · rename_i g' hbelow
    cases hcg
    obtain ⟨hval, hlt⟩ := objectiveBelow_some _ _ _ _ _ hbelow
    have hbound : (best.map (·.2)).getD f ≤ f := by
      rcases best with _ | ⟨b, gb⟩
      · simp
      · exact (hbest b gb rfl).1.le
    refine ⟨lt_of_lt_of_le (hlt _ rfl) hbound, hsize, ?_⟩
    rw [hval, fineMove_edges pts missing q _ hmem]
    rfl
  · exact hbest c g hcg

/-- A fold that only ever returns `none` from `none`: if it ends with `none`, it started
with `none` and every step saw `Q`. -/
theorem foldl_eq_none {α β : Type} (step : Option β → α → Option β) (Q : α → Prop)
    (hstep : ∀ b a, step b a = none → b = none ∧ Q a) (l : List α) (init : Option β)
    (h : l.foldl step init = none) : init = none ∧ ∀ a ∈ l, Q a := by
  induction l generalizing init with
  | nil => exact ⟨h, by simp⟩
  | cons x xs ih =>
    obtain ⟨h₁, h₂⟩ := ih _ h
    obtain ⟨h₃, h₄⟩ := hstep init x h₁
    exact ⟨h₃, by simpa [h₄] using h₂⟩

/-- If no fine move is chosen, none beats `f`.

Proof: the fold can only end with `none` if every candidate was rejected against the
bound `f` itself (`foldl_eq_none`); a rejection means its objective is `≥ f`
(`objectiveBelow_none`, on its own edges by `fineMove_edges`). -/
theorem bestFineMove_none (pts : Array Pt) (diam2 : Nat) (missing : List Nat) (q : Array Pt)
    (f : Rat) (hpos : 0 < pts.size * diam2)
    (h : bestFineMove pts diam2 (presentEdges q.size missing) q f = none) :
    ∀ c ∈ fineMoves q, f ≤ objectivePolygon pts diam2 c.1 missing := by
  unfold bestFineMove at h
  have key := foldl_eq_none _ (fun c : Array Pt × List Nat =>
      c ∈ fineMoves q → f ≤ objectivePolygon pts diam2 c.1 missing) ?_ _ none h
  · exact fun c hc => key.2 c hc hc
  rintro best ⟨cand, changed⟩ hstep
  dsimp only at hstep
  split at hstep
  · cases hstep
  · rename_i hbelow
    subst hstep
    refine ⟨rfl, fun hmem => ?_⟩
    simp only [Option.map_none, Option.getD_none] at hbelow
    rw [fineMove_edges pts missing q _ hmem] at hbelow
    refine objectiveBelow_none _ _ _ _ hpos ?_ hbelow
    intro t ht
    obtain ⟨e, -, rfl⟩ := Array.mem_map.1 ht
    exact edgeTerms_nonneg _ _ _

/-- `p + q` on points, coordinate by coordinate. -/
theorem Pt.add_def (p q : Pt) : p + q = ⟨p.i + q.i, p.j + q.j⟩ := rfl

/-- An array of size 2 is `#[a, b]`. -/
theorem eq_pair {α : Type} (q : Array α) (hq : q.size = 2) : ∃ a b, q = #[a, b] := by
  rcases q with ⟨_ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩⟩ <;> change List.length _ = 2 at hq <;> simp at hq
  exact ⟨a, b, rfl⟩

/-- The code's `δ != (0, 0)` means `δ ≠ (0, 0)`. -/
theorem bne_zero (δ : Pt) : (δ != ⟨0, 0⟩) = true ↔ δ ≠ ⟨0, 0⟩ := by
  rcases δ with ⟨i, j⟩
  show (!(i == 0 && j == 0)) = true ↔ _
  simp only [Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq, Pt.mk.injEq, not_and]
  omega

/-- Every unit offset is one of the 9 `unitOffsets`. -/
theorem mem_unitOffsets (δ : Pt) (h : IsUnitOffset δ) : δ ∈ unitOffsets.toList := by
  obtain ⟨hi, hj⟩ := h
  rcases δ with ⟨i, j⟩
  simp only [abs_le] at hi hj
  have hi' : i = -1 ∨ i = 0 ∨ i = 1 := by omega
  have hj' : j = -1 ∨ j = 0 ∨ j = 1 := by omega
  rcases hi' with rfl | rfl | rfl <;> rcases hj' with rfl | rfl | rfl <;> simp [unitOffsets]

/-- For a segment, the fine moves are the whole unit cube (apart from not moving).

Proof: write `q = #[a, b]` and the offsets as `#[δ₀, δ₁]`. If both are `(0, 0)`, the
neighbour is `q`. Otherwise it is the edge-0 move with offsets `δ₀, δ₁`, which are among
`unitOffsets` (`mem_unitOffsets`) and pass the code's "not both `(0, 0)`" filter. -/
theorem fineMoves_two (q q' : Array Pt) (hq : q.size = 2) (h : InUnitCube q q') :
    q' = q ∨ ∃ c ∈ fineMoves q, c.1 = q' := by
  obtain ⟨d, hd, hunit, rfl⟩ := h
  obtain ⟨a, b, rfl⟩ := eq_pair q hq
  obtain ⟨δ₀, δ₁, rfl⟩ := eq_pair d (hd.trans hq)
  have h₀ := mem_unitOffsets δ₀ (hunit δ₀ (by simp))
  have h₁ := mem_unitOffsets δ₁ (hunit δ₁ (by simp))
  by_cases hz : δ₀ = ⟨0, 0⟩ ∧ δ₁ = ⟨0, 0⟩
  · left
    obtain ⟨rfl, rfl⟩ := hz
    simp [Pt.add_def]
  · right
    have hpass : (δ₀ != ⟨0, 0⟩ || δ₁ != ⟨0, 0⟩) = true := by
      rw [Bool.or_eq_true, bne_zero, bne_zero]
      exact not_and_or.1 hz
    refine ⟨((#[a, b].set! 0 (#[a, b][0]! + δ₀)).set! 1 (#[a, b][1]! + δ₁), [0, 1]), ?_, ?_⟩
    · apply List.mem_append_left
      simp only [List.mem_flatMap, List.mem_map, List.mem_filter]
      exact ⟨0, by simp, δ₀, h₀, δ₁, ⟨h₁, hpass⟩, rfl⟩
    · simp [Array.set!]

/-! ### The ultra-fine step: enumerating the cube -/

/-- `foldOffsetChoices` keeps any property that `visit` keeps on each list it visits
(lists of `v` offset numbers `< 9`, followed by `ds`). -/
theorem foldOffsetChoices_preserves {σ : Type} (visit : Array Nat → σ → σ) (P : σ → Prop) (v : Nat) :
    ∀ (ds : List Nat) (st : σ),
      (∀ (l : List Nat) (s : σ), l.length = v → (∀ x ∈ l, x < 9) → P s → P (visit (l ++ ds).toArray s)) →
      P st → P (foldOffsetChoices visit v ds st) := by
  induction v with
  | zero =>
    intro ds st hv hst
    simpa [foldOffsetChoices] using hv [] st rfl (by simp) hst
  | succ v ih =>
    intro ds st hv hst
    simp only [foldOffsetChoices]
    refine foldl_preserves P _ _ _ hst fun s a ha hs => ih (a :: ds) s ?_ hs
    intro l s' hl hl9 hs'
    have ha9 : a < 9 := by simpa using ha
    have := hv (l ++ [a]) s' (by simp [hl]) (by
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hl9 x hx
      · simp at hx; omega) hs'
    simpa using this

/-- A fold whose steps can only "stay put" while `P` holds: if `P` holds at the end, every
step stayed put. -/
theorem foldl_fixed {α σ : Type} (step : σ → α → σ) (P : σ → Prop) (l : List α)
    (hstep : ∀ s a, a ∈ l → P (step s a) → step s a = s) :
    ∀ init, P (l.foldl step init) → l.foldl step init = init ∧ ∀ a ∈ l, step init a = init := by
  induction l with
  | nil => intro init _; simp
  | cons x xs ih =>
    intro init h
    obtain ⟨h₁, h₂⟩ := ih (fun s a ha => hstep s a (by simp [ha])) (step init x) h
    have hx : step init x = init := hstep init x (by simp) (by rw [← h₁]; exact h)
    rw [hx] at h₁ h₂
    exact ⟨by simpa [hx] using h₁, by simpa [hx] using h₂⟩

/-- If `visit` can only "stay put" while `P` holds, and `P` holds after `foldOffsetChoices`,
then every visit stayed put. -/
theorem foldOffsetChoices_fixed {σ : Type} (visit : Array Nat → σ → σ) (P : σ → Prop)
    (hP : ∀ a s, P (visit a s) → visit a s = s) (v : Nat) :
    ∀ (ds : List Nat) (st : σ), P (foldOffsetChoices visit v ds st) →
      foldOffsetChoices visit v ds st = st ∧
        ∀ l : List Nat, l.length = v → (∀ x ∈ l, x < 9) → visit (l ++ ds).toArray st = st := by
  induction v with
  | zero =>
    intro ds st h
    simp only [foldOffsetChoices] at h ⊢
    have h₀ := hP _ _ h
    refine ⟨h₀, fun l hl _ => ?_⟩
    rw [List.length_eq_zero_iff.1 hl, List.nil_append, h₀]
  | succ v ih =>
    intro ds st h
    simp only [foldOffsetChoices] at h ⊢
    obtain ⟨h₁, h₂⟩ := foldl_fixed (fun st a => foldOffsetChoices visit v (a :: ds) st) P _
      (fun s a _ hs => (ih (a :: ds) s hs).1) st h
    have hP' : P st := by rw [← h₁]; exact h
    refine ⟨h₁, fun l hl hl9 => ?_⟩
    -- split `l` as `l' ++ [a]`: the last offset number was chosen first
    have hne : l ≠ [] := by intro h; simp [h] at hl
    rw [← List.dropLast_append_getLast hne, List.append_assoc, List.singleton_append]
    have ha : l.getLast hne < 9 := hl9 _ (List.getLast_mem hne)
    have hst := h₂ (l.getLast hne) (by simpa using ha)
    refine (ih _ st (by rw [hst]; exact hP')).2 _ (by simp [hl]) ?_
    exact fun x hx => hl9 x (List.mem_of_mem_dropLast hx)

/-! ### The ultra-fine step: naming its pieces

These restate the local definitions inside `bestCubeMove`, so that lemmas can talk about
them; `bestCubeMove_eq` checks (by `rfl`) that they are the same. -/

/-- `2 k D`, the factor turning `F²` into `Σ_p d₁(p, Q)² + 2 k D · Σ D₂² / (2m)`. -/
abbrev cubeWeight (pts : Array Pt) (diam2 : Nat) : Rat := (2 * pts.size * diam2 : Nat)

/-- The scale `S = lbScale · 2 k D` of the whole-number bounds. -/
abbrev cubeScale (pts : Array Pt) (diam2 : Nat) : Rat := (lbScale : Rat) * cubeWeight pts diam2

/-- An edge's table entry: its pieces of `F²` and whole-number lower bounds for them. -/
def tableEdge (weight : Rat) (m : Nat) (t : EdgeTerms) : TableEdge :=
  ⟨t, t.distSqs.map (floorScaled · lbScale), floorScaled (t.d2 * weight / (2 * m : Nat)) lbScale⟩

/-- `table[e][9 a + b]`: edge `e` with its endpoints moved by offsets number `a` and `b`. -/
def cubeTable (pts : Array Pt) (diam2 : Nat) (present : List Nat) (q : Array Pt) :
    Array (Array TableEdge) :=
  (Array.range q.size).map fun e =>
    if present.contains e then
      (Array.range 81).map fun ab =>
        tableEdge (cubeWeight pts diam2) present.length
          (edgeTerms pts (q[e]! + unitOffsets[ab / 9]!) (q[(e + 1) % q.size]! + unitOffsets[ab % 9]!))
    else #[]

/-- The table entries of the present edges for the offset numbers `digits`. -/
def cubeEdges (pts : Array Pt) (diam2 : Nat) (present : List Nat) (q : Array Pt)
    (digits : Array Nat) : Array TableEdge :=
  present.toArray.map fun e =>
    (cubeTable pts diam2 present q)[e]![9 * digits[e]! + digits[(e + 1) % q.size]!]!

/-- The candidate polygon for the offset numbers `digits`. -/
def cubeCandidate (q : Array Pt) (digits : Array Nat) : Array Pt :=
  (Array.range q.size).map fun v => q[v]! + unitOffsets[digits[v]!]!

/-- One step of the ultra-fine fold. -/
def cubeVisit (pts : Array Pt) (diam2 : Nat) (present : List Nat) (q : Array Pt) (f : Rat)
    (digits : Array Nat) (st : Option (Array Pt × Rat) × Nat) : Option (Array Pt × Rat) × Nat :=
  if digits.all (· == 4) || lowerBoundReaches pts.size (cubeEdges pts diam2 present q digits) st.2 then st
  else match objectiveBelow pts.size diam2 ((cubeEdges pts diam2 present q digits).map (·.terms))
      (some ((st.1.map (·.2)).getD f)) with
    | some f' => (some (cubeCandidate q digits, f'), ceilScaled (f' * cubeScale pts diam2) 1)
    | none => st

theorem bestCubeMove_eq (pts : Array Pt) (diam2 : Nat) (present : List Nat) (q : Array Pt) (f : Rat) :
    bestCubeMove pts diam2 present q f
      = (foldOffsetChoices (cubeVisit pts diam2 present q f) q.size []
          (none, ceilScaled (f * cubeScale pts diam2) 1)).1 := rfl

/-- Entry `i` of `(Array.range n).map g` is `g i`. -/
theorem getElem!_map_range {β : Type} [Inhabited β] (n i : Nat) (g : Nat → β) (hi : i < n) :
    ((Array.range n).map g)[i]! = g i := by
  rw [getElem!_pos ((Array.range n).map g) i (by simpa using hi)]
  simp

/-- The table lookup gives the moved edge: for offset numbers `< 9`, the entries for the
present edges are `tableEdge` of the candidate's edges. -/
theorem cubeEdges_eq (pts : Array Pt) (diam2 : Nat) (missing : List Nat) (q : Array Pt)
    (digits : Array Nat) (hd : ∀ v < q.size, digits[v]! < 9) :
    cubeEdges pts diam2 (presentEdges q.size missing) q digits
      = (presentEdges q.size missing).toArray.map fun e =>
          tableEdge (cubeWeight pts diam2) (presentEdges q.size missing).length
            (edgeTerms pts (cubeCandidate q digits)[e]! (cubeCandidate q digits)[(e + 1) % q.size]!) := by
  apply Array.map_congr_left
  intro e he
  rw [List.mem_toArray] at he
  have hlt := lt_of_mem_presentEdges he
  have hlt' : (e + 1) % q.size < q.size := Nat.mod_lt _ (by omega)
  have ha := hd e hlt
  have hb := hd _ hlt'
  have h81 : 9 * digits[e]! + digits[(e + 1) % q.size]! < 81 := by omega
  have hdiv : (9 * digits[e]! + digits[(e + 1) % q.size]!) / 9 = digits[e]! := by omega
  have hmod : (9 * digits[e]! + digits[(e + 1) % q.size]!) % 9 = digits[(e + 1) % q.size]! := by omega
  rw [cubeTable, getElem!_map_range _ _ _ hlt, ite_eq_left_of_eq_true _ _ (eq_true (List.contains_iff_mem.2 he)),
    getElem!_map_range _ _ _ h81, hdiv, hmod, cubeCandidate, getElem!_map_range _ _ _ hlt,
    getElem!_map_range _ _ _ hlt']

/-- The candidate's objective is `objectiveFromEdges` of the table entries' exact pieces. -/
theorem cubeEdges_terms (pts : Array Pt) (diam2 : Nat) (missing : List Nat) (q : Array Pt)
    (digits : Array Nat) (hd : ∀ v < q.size, digits[v]! < 9) :
    objectiveFromEdges pts.size diam2
        ((cubeEdges pts diam2 (presentEdges q.size missing) q digits).map (·.terms))
      = objectivePolygon pts diam2 (cubeCandidate q digits) missing := by
  rw [cubeEdges_eq pts diam2 missing q digits hd, Array.map_map]
  simp [objectivePolygon, cubeCandidate, tableEdge, Function.comp_def]


/-! ### The ultra-fine step: the whole-number bounds are sound -/

/-- `⌊c x⌋ ≤ c x` for `x ≥ 0`. -/
theorem floorScaled_le (x : Rat) (c : Nat) (hx : 0 ≤ x) : (floorScaled x c : Rat) ≤ x * c := by
  unfold floorScaled
  have hden : (0 : Int) < x.den := by exact_mod_cast x.den_pos
  have hN : 0 ≤ x.num * c := mul_nonneg (Rat.num_nonneg.2 hx) (Int.natCast_nonneg c)
  have hq : 0 ≤ x.num * c / x.den := Int.ediv_nonneg hN hden.le
  have hmul : (x.num * c / x.den) * x.den ≤ x.num * c := Int.ediv_mul_le _ hden.ne'
  have hcast : ((x.num * c / x.den).toNat : Rat) = ((x.num * c / x.den : Int) : Rat) := by
    exact_mod_cast Int.toNat_of_nonneg hq
  rw [hcast]
  have hxc : x * c = ((x.num * c : Int) : Rat) / (x.den : Rat) := by
    conv_lhs => rw [← Rat.num_div_den x]
    push_cast; ring
  rw [hxc, le_div_iff₀ (by exact_mod_cast x.den_pos)]
  exact_mod_cast hmul

/-- `c x ≤ ⌈c x⌉` for `x ≥ 0`. -/
theorem le_ceilScaled (x : Rat) (c : Nat) (hx : 0 ≤ x) : x * c ≤ (ceilScaled x c : Rat) := by
  unfold ceilScaled
  have hden : (0 : Int) < x.den := by exact_mod_cast x.den_pos
  have hN : 0 ≤ x.num * c := mul_nonneg (Rat.num_nonneg.2 hx) (Int.natCast_nonneg c)
  have hq : 0 ≤ (x.num * c + x.den - 1) / x.den := Int.ediv_nonneg (by omega) hden.le
  have hlt := Int.lt_ediv_add_one_mul_self (x.num * c + x.den - 1) hden
  have hmul : x.num * c ≤ (x.num * c + x.den - 1) / x.den * x.den := by
    rw [add_mul, one_mul] at hlt; omega
  have hcast : (((x.num * c + x.den - 1) / x.den).toNat : Rat)
      = (((x.num * c + x.den - 1) / x.den : Int) : Rat) := by
    exact_mod_cast Int.toNat_of_nonneg hq
  rw [hcast]
  have hxc : x * c = ((x.num * c : Int) : Rat) / (x.den : Rat) := by
    conv_lhs => rw [← Rat.num_div_den x]
    push_cast; ring
  rw [hxc, div_le_iff₀ (by exact_mod_cast x.den_pos)]
  exact_mod_cast hmul

/-- The nearest-edge point bound, as `lowerBoundReaches` computes it. -/
def nearestLB (tes : Array TableEdge) (i : Nat) : Nat :=
  tes.foldl (init := tes[0]!.pointLB[i]!) fun m e => min m e.pointLB[i]!

/-- The whole-number bound over the points numbered `idx, …, idx + left - 1`, added to `total`. -/
abbrev lbSum (tes : Array TableEdge) (left idx total : Nat) : Nat :=
  (List.range' idx left).foldl (fun s i => s + nearestLB tes i) total

theorem le_lbSum (tes : Array TableEdge) (left idx total : Nat) : total ≤ lbSum tes left idx total :=
  foldl_preserves (total ≤ ·) _ _ _ le_rfl fun _ _ _ hb => Nat.le_add_right_of_le hb

/-- If `lowerBoundReaches` says the bound reaches `limit`, the whole bound does. -/
theorem lowerBoundReaches_go_true (tes : Array TableEdge) (limit left : Nat) :
    ∀ idx total, lowerBoundReaches.go tes limit left idx total = true → limit ≤ lbSum tes left idx total := by
  induction left with
  | zero =>
    intro idx total h
    simp only [lowerBoundReaches.go, decide_eq_true_eq] at h
    exact h
  | succ left ih =>
    intro idx total h
    simp only [lowerBoundReaches.go, Bool.or_eq_true, decide_eq_true_eq] at h
    rw [lbSum, List.range'_succ, List.foldl_cons]
    rcases h with h | h
    · exact h.trans ((Nat.le_add_right _ _).trans (le_lbSum tes left (idx + 1) _))
    · exact ih (idx + 1) _ h

/-- A `min` fold is at most its start and at most every term. -/
theorem foldl_min_le {α β : Type} [LinearOrder β] (g : α → β) (l : List α) :
    ∀ init, l.foldl (fun m e => min m (g e)) init ≤ init ∧
      ∀ e ∈ l, l.foldl (fun m e => min m (g e)) init ≤ g e := by
  induction l with
  | nil => intro init; simp
  | cons x xs ih =>
    intro init
    obtain ⟨h₁, h₂⟩ := ih (min init (g x))
    refine ⟨h₁.trans (min_le_left _ _), ?_⟩
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · exact h₁.trans (min_le_right _ _)
    · exact h₂ e he

/-- A `min` fold ends at its start or at one of its terms. -/
theorem foldl_min_cases {α β : Type} [LinearOrder β] (g : α → β) (l : List α) (init : β) :
    l.foldl (fun m e => min m (g e)) init = init ∨ ∃ e ∈ l, l.foldl (fun m e => min m (g e)) init = g e :=
  foldl_preserves (fun r => r = init ∨ ∃ e ∈ l, r = g e) _ _ _ (Or.inl rfl) fun b a ha hb => by
    rcases min_choice b (g a) with h | h
    · rw [h]; exact hb
    · exact Or.inr ⟨a, ha, h⟩

/-- `(arr.map g)[i]! = g arr[i]` within range. -/
theorem getElem!_map_of_lt {α β : Type} [Inhabited α] [Inhabited β] (g : α → β) (arr : Array α) (i : Nat)
    (hi : i < arr.size) : (arr.map g)[i]! = g arr[i]! := by
  rw [getElem!_pos (arr.map g) i (by simpa using hi), getElem!_pos arr i hi]
  simp

/-- A table entry's point bound is at most `lbScale ·` the point's distance. -/
theorem tableEdge_pointLB_le (W : Rat) (m : Nat) (t : EdgeTerms) (ht : t.Nonneg) (i : Nat) :
    ((tableEdge W m t).pointLB[i]! : Rat) ≤ t.distSqs[i]! * lbScale := by
  simp only [tableEdge]
  rw [getElem!_def, getElem!_def t.distSqs, Array.getElem?_map]
  cases h : t.distSqs[i]? with
  | none => simp [show (default : Rat) = 0 from rfl]
  | some x =>
    obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.1 h
    simpa using floorScaled_le _ lbScale (ht.1 _ (Array.getElem_mem hi))

/-- The nearest-edge point bound is at most `lbScale ·` the nearest-edge distance. -/
theorem nearestLB_le (W : Rat) (m : Nat) (ts : Array EdgeTerms) (hnn : ∀ t ∈ ts, t.Nonneg) (i : Nat) :
    (nearestLB (ts.map (tableEdge W m)) i : Rat) ≤ nearestSq ts i * lbScale := by
  have hlow := foldl_min_le (fun e : TableEdge => e.pointLB[i]!) (ts.map (tableEdge W m)).toList
    ((ts.map (tableEdge W m))[0]!.pointLB[i]!)
  simp only [Array.foldl_toList] at hlow
  unfold nearestLB
  rcases foldl_min_cases (fun e : EdgeTerms => e.distSqs[i]!) ts.toList (ts[0]!.distSqs[i]!) with h | ⟨e, he, h⟩
  · rw [Array.foldl_toList] at h
    unfold nearestSq
    rw [h]
    by_cases hne : 0 < ts.size
    · rw [getElem!_map_of_lt _ _ 0 hne] at hlow ⊢
      exact (Nat.cast_le.2 hlow.1).trans (tableEdge_pointLB_le W m _ (hnn _ (by
        rw [getElem!_pos ts 0 hne]; exact Array.getElem_mem hne)) i)
    · obtain rfl : ts = #[] := Array.size_eq_zero_iff.1 (by omega)
      simp [show (default : TableEdge).pointLB = #[] from rfl, show (default : EdgeTerms).distSqs = #[] from rfl,
        show (default : Rat) = 0 from rfl]
  · rw [Array.foldl_toList] at h
    unfold nearestSq
    rw [h]
    have hmem : tableEdge W m e ∈ (ts.map (tableEdge W m)).toList := by
      simpa using ⟨e, by simpa using he, rfl⟩
    exact (Nat.cast_le.2 (hlow.2 _ hmem)).trans (tableEdge_pointLB_le W m e (hnn e (by simpa using he)) i)

/-- Termwise `f ≤ g` gives `Σ f ≤ Σ g` (with a `Nat` sum on the left). -/
theorem foldl_add_cast_le {α : Type} (l : List α) (f : α → Nat) (g : α → Rat)
    (h : ∀ x ∈ l, (f x : Rat) ≤ g x) :
    ∀ (a : Nat) (b : Rat), (a : Rat) ≤ b →
      ((l.foldl (fun s x => s + f x) a : Nat) : Rat) ≤ l.foldl (fun s x => s + g x) b := by
  induction l with
  | nil => intro a b hab; simpa using hab
  | cons x xs ih =>
    intro a b hab
    simp only [List.foldl_cons]
    exact ih (fun y hy => h y (by simp [hy])) _ _ (by push_cast; linarith [h x (by simp)])

/-- A sum started at `b` is `b` plus the sum started at 0. -/
theorem foldl_add_shift {α : Type} (l : List α) (g : α → Rat) :
    ∀ b, l.foldl (fun s x => s + g x) b = b + l.foldl (fun s x => s + g x) 0 := by
  induction l with
  | nil => intro b; simp
  | cons x xs ih => intro b; simp only [List.foldl_cons]; rw [ih (b + g x), ih (0 + g x)]; ring

/-- A constant factor comes out of a sum. -/
theorem foldl_add_mul {α : Type} (l : List α) (g : α → Rat) (K : Rat) :
    ∀ a, l.foldl (fun s x => s + g x * K) (a * K) = l.foldl (fun s x => s + g x) a * K := by
  induction l with
  | nil => intro a; simp
  | cons x xs ih => intro a; simp only [List.foldl_cons]; rw [← ih (a + g x)]; ring_nf

/-- The `D₂` bounds add up to at most `lbScale ·` the scaled `D₂` part (this uses `D₂ ≥ 0`). -/
theorem d2LB_sum_le (W : Rat) (hW : 0 ≤ W) (ts : Array EdgeTerms) (hnn : ∀ t ∈ ts, t.Nonneg) :
    (((ts.map (tableEdge W ts.size)).foldl (init := 0) (· + ·.d2LB) : Nat) : Rat)
      ≤ ts.foldl (init := (0 : Rat)) (· + ·.d2) * (W / (2 * ts.size : Nat) * lbScale) := by
  rw [Array.foldl_map, ← Array.foldl_toList, ← Array.foldl_toList, ← foldl_add_mul, zero_mul]
  refine foldl_add_cast_le _ _ _ (fun t ht => ?_) 0 0 le_rfl
  have hd := (hnn t (by simpa using ht)).2
  have := floorScaled_le (t.d2 * W / (2 * ts.size : Nat)) lbScale
    (div_nonneg (mul_nonneg hd hW) (Nat.cast_nonneg _))
  simp only [tableEdge]
  calc _ ≤ t.d2 * W / (2 * ts.size : Nat) * lbScale := this
    _ = _ := by ring

/-- **The whole-number bound is sound:** if it reaches `⌈g · S⌉`, then `F² ≥ g`. -/
theorem lowerBound_sound (pts : Array Pt) (diam2 : Nat) (ts : Array EdgeTerms)
    (hnn : ∀ t ∈ ts, t.Nonneg) (g : Rat) (hg : 0 ≤ g) (hpos : 0 < pts.size * diam2)
    (h : lowerBoundReaches pts.size (ts.map (tableEdge (cubeWeight pts diam2) ts.size))
      (ceilScaled (g * cubeScale pts diam2) 1) = true) :
    g ≤ objectiveFromEdges pts.size diam2 ts := by
  have hW : 0 < cubeWeight pts diam2 := by
    exact_mod_cast (by rw [Nat.mul_assoc]; omega : 0 < 2 * pts.size * diam2)
  have hc : (0 : Rat) < lbScale := by norm_num [lbScale]
  have hS : 0 < cubeScale pts diam2 := mul_pos hc hW
  unfold lowerBoundReaches at h
  have h1 := lowerBoundReaches_go_true _ _ pts.size 0 _ h
  have h2 := le_ceilScaled (g * cubeScale pts diam2) 1 (mul_nonneg hg hS.le)
  -- the whole bound is at most `lbScale ·` (the `D₁` sum plus the scaled `D₂` part)
  have h3 : (lbSum (ts.map (tableEdge (cubeWeight pts diam2) ts.size)) pts.size 0
        ((ts.map (tableEdge (cubeWeight pts diam2) ts.size)).foldl (init := 0) (· + ·.d2LB)) : Rat)
      ≤ d1Sum ts pts.size 0 0 * lbScale
        + ts.foldl (init := (0 : Rat)) (· + ·.d2) * (cubeWeight pts diam2 / (2 * ts.size : Nat) * lbScale) := by
    refine (foldl_add_cast_le _ _ (fun i => nearestSq ts i * lbScale)
      (fun i _ => nearestLB_le _ ts.size ts hnn i) _ _ (d2LB_sum_le _ hW.le ts hnn)).trans (le_of_eq ?_)
    rw [foldl_add_shift, add_comm, ← zero_mul (lbScale : Rat), foldl_add_mul, zero_mul]
  -- `S · F²` is that same quantity
  have hF : cubeScale pts diam2 * objectiveFromEdges pts.size diam2 ts
      = d1Sum ts pts.size 0 0 * lbScale
        + ts.foldl (init := (0 : Rat)) (· + ·.d2) * (cubeWeight pts diam2 / (2 * ts.size : Nat) * lbScale) := by
    have hk : (pts.size : Rat) ≠ 0 := by
      have : pts.size ≠ 0 := fun h0 => by simp [h0] at hpos
      exact_mod_cast this
    have hD : (diam2 : Rat) ≠ 0 := by
      have : diam2 ≠ 0 := fun h0 => by simp [h0] at hpos
      exact_mod_cast this
    rw [objectiveFromEdges_eq]
    simp only [cubeScale, cubeWeight]
    push_cast
    field_simp
  have key : g * cubeScale pts diam2 ≤ cubeScale pts diam2 * objectiveFromEdges pts.size diam2 ts := by
    calc g * cubeScale pts diam2 = g * cubeScale pts diam2 * (1 : Nat) := by simp
      _ ≤ (ceilScaled (g * cubeScale pts diam2) 1 : Rat) := h2
      _ ≤ _ := by exact_mod_cast h1
      _ ≤ _ := h3
      _ = _ := hF.symm
  rw [mul_comm] at key
  exact le_of_mul_le_mul_left key hS

/-! ### The ultra-fine step: the two theorems -/

/-- The number of a unit offset in `unitOffsets`: `3 (δ.i + 1) + (δ.j + 1)`. -/
def offsetIndex (δ : Pt) : Nat := (3 * (δ.i + 1) + (δ.j + 1)).toNat

/-- `offsetIndex δ` is a valid offset number, and it is the number of `δ`. -/
theorem offsetIndex_spec (δ : Pt) (h : IsUnitOffset δ) :
    offsetIndex δ < 9 ∧ unitOffsets[offsetIndex δ]! = δ := by
  obtain ⟨hi, hj⟩ := h
  rcases δ with ⟨i, j⟩
  simp only [abs_le] at hi hj
  have hi' : i = -1 ∨ i = 0 ∨ i = 1 := by omega
  have hj' : j = -1 ∨ j = 0 ∨ j = 1 := by omega
  rcases hi' with rfl | rfl | rfl <;> rcases hj' with rfl | rfl | rfl <;> simp [offsetIndex, unitOffsets]

/-- Every polygon in the unit cube around `q` is the candidate for some offset numbers,
and "every offset number is 4" means it is `q` itself. -/
theorem cube_cover (q q' : Array Pt) (h : InUnitCube q q') :
    ∃ l : List Nat, l.length = q.size ∧ (∀ x ∈ l, x < 9) ∧ cubeCandidate q l.toArray = q' ∧
      ((l.toArray.all (· == 4)) = true → q' = q) := by
  obtain ⟨d, hd, hunit, rfl⟩ := h
  have hspec : ∀ v (hv : v < d.size), offsetIndex d[v] < 9 ∧ unitOffsets[offsetIndex d[v]]! = d[v] :=
    fun v hv => offsetIndex_spec _ (hunit _ (Array.getElem_mem hv))
  refine ⟨d.toList.map offsetIndex, by simp [hd], ?_, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_map, Array.mem_toList_iff] at hx
    obtain ⟨δ, hδ, rfl⟩ := hx
    exact (offsetIndex_spec δ (hunit δ hδ)).1
  · apply Array.ext (by simp [cubeCandidate, hd])
    intro v h₁ h₂
    simp only [cubeCandidate, Array.size_map, Array.size_range] at h₁
    have hv : v < d.size := hd ▸ h₁
    simp [cubeCandidate, Array.getElem_zipWith, getElem!_pos q v h₁, (hspec v hv).2, hv]
  · intro hall
    simp only [List.all_toArray, List.all_eq_true, List.mem_map, Array.mem_toList_iff, beq_iff_eq] at hall
    apply Array.ext (by simp [hd])
    intro v h₁ h₂
    have hv : v < d.size := by simp at h₁; omega
    have h4 := hall _ ⟨d[v], Array.getElem_mem hv, rfl⟩
    have hz : d[v] = ⟨0, 0⟩ := by rw [← (hspec v hv).2, h4]; simp [unitOffsets]
    simp [Array.getElem_zipWith, hz, Pt.add_def]

/-- Offset numbers taken from a list of numbers `< 9` are `< 9`. -/
theorem digits_lt (l : List Nat) (hl9 : ∀ x ∈ l, x < 9) (v : Nat) (hv : v < l.length) :
    l.toArray[v]! < 9 := by
  rw [getElem!_pos l.toArray v (by simpa using hv)]
  exact hl9 _ (by simp)

/-- An ultra-fine move is strictly better, keeps the vertex count, and is scored honestly.

Proof: along `foldOffsetChoices`, the current best is always a candidate that beats `f`,
scored by `objectiveBelow` (`objectiveBelow_some`) on its table entries, whose exact pieces
are the candidate's own edges (`cubeEdges_terms`). -/
theorem bestCubeMove_some (pts : Array Pt) (diam2 : Nat) (missing : List Nat) (q q' : Array Pt)
    (f f' : Rat) (h : bestCubeMove pts diam2 (presentEdges q.size missing) q f = some (q', f')) :
    f' < f ∧ q'.size = q.size ∧ f' = objectivePolygon pts diam2 q' missing := by
  rw [bestCubeMove_eq] at h
  refine (foldOffsetChoices_preserves _ (fun st : Option (Array Pt × Rat) × Nat => ∀ c g, st.1 = some (c, g) →
      g < f ∧ c.size = q.size ∧ g = objectivePolygon pts diam2 c missing) q.size [] _ ?_ (by simp)) q' f' h
  intro l s hlen hl9 hs c g hcg
  rw [List.append_nil] at hcg
  unfold cubeVisit at hcg
  split_ifs at hcg
  · exact hs c g hcg
  · split at hcg
    · rename_i g' hbelow
      simp only [Option.some.injEq, Prod.mk.injEq] at hcg
      obtain ⟨hc, hg⟩ := hcg
      rw [← hc, ← hg]
      obtain ⟨hval, hlt⟩ := objectiveBelow_some _ _ _ _ _ hbelow
      have hbound : (s.1.map (·.2)).getD f ≤ f := by
        rcases hs1 : s.1 with _ | ⟨b, gb⟩
        · simp
        · exact (hs b gb hs1).1.le
      refine ⟨lt_of_lt_of_le (hlt _ rfl) hbound, by simp [cubeCandidate], ?_⟩
      rw [hval, cubeEdges_terms pts diam2 missing q _ fun v hv => digits_lt l hl9 v (hlen ▸ hv)]
    · exact hs c g hcg

/-- If no ultra-fine move is chosen, no polygon in the unit cube beats `f = F²(q)`.

Proof: "nothing chosen" means every visit left the state `(none, ⌈f S⌉)` unchanged
(`foldOffsetChoices_fixed`). A neighbour `Q'` is the candidate for some offset numbers
(`cube_cover`); its visit either skipped it because no vertex moves (then `Q' = q`),
or because the whole-number bound reached `⌈f S⌉` (`lowerBound_sound`), or because
`objectiveBelow` rejected it against `f` (`objectiveBelow_none`). -/
theorem bestCubeMove_none (pts : Array Pt) (diam2 : Nat) (missing : List Nat) (q : Array Pt)
    (f : Rat) (hpos : 0 < pts.size * diam2) (hf : f = objectivePolygon pts diam2 q missing)
    (h : bestCubeMove pts diam2 (presentEdges q.size missing) q f = none) :
    ∀ q', InUnitCube q q' → f ≤ objectivePolygon pts diam2 q' missing := by
  intro q' hq'
  obtain ⟨l, hlen, hl9, hcand, hstay⟩ := cube_cover q q' hq'
  have hd : ∀ v < q.size, l.toArray[v]! < 9 := fun v hv => digits_lt l hl9 v (hlen ▸ hv)
  rw [bestCubeMove_eq] at h
  obtain ⟨-, hall⟩ := foldOffsetChoices_fixed _ (fun st : Option (Array Pt × Rat) × Nat => st.1 = none)
    (fun a s hs => by
      unfold cubeVisit at hs ⊢
      split_ifs at hs ⊢
      · rfl
      · split
        · rename_i heq
          rw [heq] at hs
          simp at hs
        · rfl) q.size [] _ h
  have hv := hall l hlen hl9
  rw [List.append_nil] at hv
  -- the candidate's edges, as `edgeTerms`, and its objective
  set ts := (presentEdges q.size missing).toArray.map fun e =>
    edgeTerms pts (cubeCandidate q l.toArray)[e]! (cubeCandidate q l.toArray)[(e + 1) % q.size]! with hts
  have hts_size : ts.size = (presentEdges q.size missing).length := by simp [hts]
  have hnn : ∀ t ∈ ts, t.Nonneg := by
    intro t ht
    obtain ⟨e, -, rfl⟩ := Array.mem_map.1 ht
    exact edgeTerms_nonneg _ _ _
  have hedges : cubeEdges pts diam2 (presentEdges q.size missing) q l.toArray
      = ts.map (tableEdge (cubeWeight pts diam2) ts.size) := by
    rw [cubeEdges_eq pts diam2 missing q _ hd, hts_size, hts, Array.map_map]
    rfl
  have hobj : objectiveFromEdges pts.size diam2 ts = objectivePolygon pts diam2 q' missing := by
    rw [← hcand, ← cubeEdges_terms pts diam2 missing q _ hd, hedges, Array.map_map]
    simp [tableEdge, Function.comp_def]
  have hf0 : 0 ≤ f := hf ▸ objectivePolygon_nonneg _ _ _ _
  unfold cubeVisit at hv
  split_ifs at hv with hc
  · rw [Bool.or_eq_true] at hc
    rcases hc with hc | hc
    · rw [hstay hc]; exact hf.le
    · rw [hedges] at hc
      exact hobj ▸ lowerBound_sound pts diam2 ts hnn f hf0 hpos hc
  · split at hv
    · simp at hv
    · rename_i hbelow
      simp only [Option.map_none, Option.getD_none, hedges, Array.map_map] at hbelow
      rw [← hobj]
      refine objectiveBelow_none _ _ _ _ hpos hnn ?_
      simpa [tableEdge, Function.comp_def] using hbelow

/-! ## D. The fine search -/

/-- The invariant of the fine search's recursion: from any `q` with `f = F²(q)` and the
starting vertex count, the result keeps both, is no worse, and (when converged) no fine
move beats it. -/
theorem fineSearch_go_spec (pts : Array Pt) (diam2 : Nat) (missing : List Nat) (q₀ : Array Pt)
    (fuel left : Nat) :
    ∀ (q : Array Pt) (f : Rat), q.size = q₀.size → f = objectivePolygon pts diam2 q missing →
      let r := fineSearch.go pts diam2 (presentEdges q₀.size missing) fuel left q f
      r.1.size = q₀.size ∧ r.2.1 = objectivePolygon pts diam2 r.1 missing ∧ r.2.1 ≤ f ∧
        (r.2.2.2 = true → bestFineMove pts diam2 (presentEdges q₀.size missing) r.1 r.2.1 = none) := by
  induction left with
  | zero =>
    intro q f hq hf
    unfold fineSearch.go
    split
    · rename_i hnone
      exact ⟨hq, hf, le_rfl, fun _ => hnone⟩
    · exact ⟨hq, hf, le_rfl, by simp⟩
  | succ left ih =>
    intro q f hq hf
    unfold fineSearch.go
    split
    · rename_i hnone
      exact ⟨hq, hf, le_rfl, fun _ => hnone⟩
    · rename_i q' f' hsome
      rw [← hq] at hsome
      obtain ⟨hlt, hsize, hval⟩ := bestFineMove_some pts diam2 missing q q' f f' hsome
      obtain ⟨h₁, h₂, h₃, h₄⟩ := ih q' f' (hsize.trans hq) hval
      exact ⟨h₁, h₂, h₃.trans hlt.le, h₄⟩

/-- The fine search keeps `f = F²(q)` and the vertex count, never increases `f`, and when
it converges, no fine move beats the result.

Proof: `fineSearch_go_spec`, by induction on the moves left; each accepted move is
strictly better and scored honestly (`bestFineMove_some`). -/
theorem fineSearch_spec (pts : Array Pt) (diam2 : Nat) (missing : List Nat) (q₀ : Array Pt)
    (f₀ : Rat) (fuel : Nat) (hf : f₀ = objectivePolygon pts diam2 q₀ missing) :
    let r := fineSearch pts diam2 (presentEdges q₀.size missing) q₀ f₀ fuel
    r.1.size = q₀.size ∧ r.2.1 = objectivePolygon pts diam2 r.1 missing ∧ r.2.1 ≤ f₀ ∧
      (r.2.2.2 = true → bestFineMove pts diam2 (presentEdges q₀.size missing) r.1 r.2.1 = none) :=
  fineSearch_go_spec pts diam2 missing q₀ fuel fuel q₀ f₀ rfl hf

/-! ## E. `polish` -/

/-- `diam(P) > 0` needs a point. -/
theorem size_pos_of_diamSq_pos (pts : Array Pt) (h : 0 < diamSq pts) : 0 < pts.size := by
  rcases Nat.eq_zero_or_pos pts.size with h0 | h0
  · obtain rfl : pts = #[] := Array.size_eq_zero_iff.1 h0
    simp [diamSq] at h
  · exact h0

/-- The invariant of `polish`'s recursion, carrying all four properties at once. -/
theorem polish_go_spec (pts : Array Pt) (missing : List Nat) (start : Array Pt) (fuel ultraMax rounds : Nat) :
    ∀ (q : Array Pt) (f : Rat) (used : Nat), q.size = start.size →
      f = objectivePolygon pts (diamSq pts) q missing →
      let r := polish.go pts start fuel ultraMax (diamSq pts) (presentEdges start.size missing) rounds q f used
      r.vertices.size = start.size ∧ r.objectiveSq = objectivePolygon pts (diamSq pts) r.vertices missing ∧
        r.objectiveSq ≤ f ∧ (0 < diamSq pts → r.certified = true →
          ∀ q', InUnitCube r.vertices q' → r.objectiveSq ≤ objectivePolygon pts (diamSq pts) q' missing) := by
  induction rounds with
  | zero =>
    intro q f used hq hf
    simp only [polish.go]
    exact ⟨hq, hf, le_rfl, by simp⟩
  | succ rounds ih =>
    intro q f used hq hf
    have spec := fineSearch_spec pts (diamSq pts) missing q f (fuel - used) hf
    rw [hq] at spec
    simp only [polish.go]
    generalize fineSearch pts (diamSq pts) (presentEdges start.size missing) q f (fuel - used) = res at spec ⊢
    obtain ⟨q₁, f₁, m, conv⟩ := res
    obtain ⟨h₁, h₂, h₃, h₄⟩ := spec
    simp only at h₁ h₂ h₃ h₄ ⊢
    split
    · -- not converged: out of fuel
      exact ⟨h₁, h₂, h₃, by simp⟩
    · rename_i hconv
      split
      · -- a segment: the converged fine search already covered the whole cube
        rename_i h2
        refine ⟨h₁, h₂, h₃, fun hdiam _ q' hq' => ?_⟩
        have hpos : 0 < pts.size * diamSq pts := Nat.mul_pos (size_pos_of_diamSq_pos pts hdiam) hdiam
        have hnone := h₄ (by simpa using hconv)
        rw [← h₁] at hnone
        rcases fineMoves_two q₁ q' (h₁.trans (by simpa using h2)) hq' with rfl | ⟨c, hc, rfl⟩
        · exact h₂.le
        · exact bestFineMove_none pts _ missing q₁ f₁ hpos hnone c hc
      · split
        · -- too many vertices for the ultra-fine step: not certified
          exact ⟨h₁, h₂, h₃, by simp⟩
        · split
          · -- the ultra-fine step found nothing better: certified
            rename_i hnone
            refine ⟨h₁, h₂, h₃, fun hdiam _ q' hq' => ?_⟩
            have hpos : 0 < pts.size * diamSq pts := Nat.mul_pos (size_pos_of_diamSq_pos pts hdiam) hdiam
            rw [← h₁] at hnone
            exact bestCubeMove_none pts _ missing q₁ f₁ hpos h₂ hnone q' hq'
          · -- it found a better polygon: continue from there, if fuel is left
            rename_i q' f' hsome
            rw [← h₁] at hsome
            obtain ⟨hlt, hsize, hval⟩ := bestCubeMove_some pts _ missing q₁ q' f₁ f' hsome
            split
            · exact ⟨h₁, h₂, h₃, by simp⟩
            · obtain ⟨g₁, g₂, g₃, g₄⟩ := ih q' f' (used + m + 1) (hsize.trans h₁) hval
              exact ⟨g₁, g₂, g₃.trans (hlt.le.trans h₃), g₄⟩

/-- `polish` is its recursion started from `start`. -/
theorem polish_eq (pts : Array Pt) (missing : List Nat) (start : Array Pt) (fuel ultraMax : Nat) :
    polish pts missing start fuel ultraMax
      = polish.go pts start fuel ultraMax (diamSq pts) (presentEdges start.size missing) (fuel + 1) start
          (objectivePolygon pts (diamSq pts) start missing) 0 := rfl

/-- `polish` keeps the number of vertices.

Proof: `polish_go_spec`, by induction on the rounds left, with `fineSearch_spec` and
`bestCubeMove_some`. -/
theorem polish_size (pts : Array Pt) (missing : List Nat) (start : Array Pt) (fuel ultraMax : Nat) :
    (polish pts missing start fuel ultraMax).vertices.size = start.size := by
  rw [polish_eq]
  exact (polish_go_spec pts missing start fuel ultraMax _ start _ 0 rfl rfl).1

/-- The reported `F²` is the computed objective of the reported polygon.

Proof: `polish_go_spec`; the invariant `f = F²(q)` holds at the start by definition and is
kept by `fineSearch_spec` and `bestCubeMove_some`. -/
theorem polish_objectiveSq (pts : Array Pt) (missing : List Nat) (start : Array Pt) (fuel ultraMax : Nat) :
    let r := polish pts missing start fuel ultraMax
    r.objectiveSq = objectivePolygon pts (diamSq pts) r.vertices missing := by
  intro r
  rw [show r = _ from polish_eq pts missing start fuel ultraMax]
  exact (polish_go_spec pts missing start fuel ultraMax _ start _ 0 rfl rfl).2.1

/-- The search never ends worse than it started.

Proof: `polish_go_spec`; `f` only ever decreases. -/
theorem polish_le_start (pts : Array Pt) (missing : List Nat) (start : Array Pt) (fuel ultraMax : Nat) :
    (polish pts missing start fuel ultraMax).objectiveSq
      ≤ objectivePolygon pts (diamSq pts) start missing := by
  rw [polish_eq]
  exact (polish_go_spec pts missing start fuel ultraMax _ start _ 0 rfl rfl).2.2.1

/-- **The certificate.** If `diam(P) > 0` and the result is certified, no polygon in the
unit cube around it has a lower computed objective.

Proof: `polish_go_spec`. `certified` is reported only (a) for `n = 2`, when the last fine
search converged: `fineSearch_spec`, `bestFineMove_none` and `fineMoves_two`; or (b) when
the last fine search converged and `bestCubeMove` found nothing: `bestCubeMove_none`. In
both cases `Q' = r.vertices` is covered by `r.objectiveSq = F²(r.vertices)`. -/
theorem polish_certified (pts : Array Pt) (missing : List Nat) (start : Array Pt) (fuel ultraMax : Nat)
    (hdiam : 0 < diamSq pts) (hcert : (polish pts missing start fuel ultraMax).certified = true) :
    let r := polish pts missing start fuel ultraMax
    ∀ q', InUnitCube r.vertices q' → r.objectiveSq ≤ objectivePolygon pts (diamSq pts) q' missing := by
  intro r
  rw [show r = _ from polish_eq pts missing start fuel ultraMax] at *
  rw [polish_eq] at hcert
  exact (polish_go_spec pts missing start fuel ultraMax _ start _ 0 rfl rfl).2.2.2 hdiam hcert

end PolyFit
