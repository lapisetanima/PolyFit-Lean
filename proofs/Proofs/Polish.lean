import Mathlib.Data.Rat.Cast.Order
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

**Proof outline** (section A is proved; B–E are planned).
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

/-- A value from `objectiveBelow` is the exact objective, and below the bound if there is one.

Proof (planned): induction on the points left in `objectiveBelow.go`; the value returned
is `d1Total / (2 k D) + d2Part`, which is `objectiveFromEdges` rearranged. -/
theorem objectiveBelow_some (numPts diam2 : Nat) (edges : Array EdgeTerms) (bound : Option Rat)
    (v : Rat) (h : objectiveBelow numPts diam2 edges bound = some v) :
    v = objectiveFromEdges numPts diam2 edges ∧ ∀ b ∈ bound, v < b := by
  sorry

/-- `objectiveBelow` gives up only when the exact objective is `≥` the bound.

Proof (planned): either `(b - d2Part) · scale ≤ 0`, so `b ≤ d2Part ≤ F²` (the `D₁` part
is `≥ 0`); or a partial `D₁` sum reached the limit, and the remaining terms are `≥ 0`.
Both need `scale = 2 k D > 0`. -/
theorem objectiveBelow_none (numPts diam2 : Nat) (edges : Array EdgeTerms) (b : Rat)
    (hpos : 0 < numPts * diam2) (hnn : ∀ e ∈ edges, ∀ idx < numPts, 0 ≤ e.distSqs[idx]!)
    (h : objectiveBelow numPts diam2 edges (some b) = none) :
    b ≤ objectiveFromEdges numPts diam2 edges := by
  sorry





/-! ## C. Each move picks the best candidate -/

/-- A fine move is strictly better, keeps the vertex count, and is scored honestly.

Proof (planned): the fold only replaces its result with an `objectiveBelow` value
(`objectiveBelow_some`); the edges it scores are the cached ones for unchanged edges and
recomputed ones otherwise, and the cache holds exactly `edgeTerms` of the current
polygon, so the score is `objectivePolygon` of the candidate. -/
theorem bestFineMove_some (pts : Array Pt) (diam2 : Nat) (missing : List Nat) (q q' : Array Pt)
    (f f' : Rat) (h : bestFineMove pts diam2 (presentEdges q.size missing) q f = some (q', f')) :
    f' < f ∧ q'.size = q.size ∧ f' = objectivePolygon pts diam2 q' missing := by
  sorry

/-- If no fine move is chosen, none beats `f`.

Proof (planned): along the fold the bound only decreases from `f`; a candidate is passed
over only when `objectiveBelow` says it is `≥` the current bound (`objectiveBelow_none`). -/
theorem bestFineMove_none (pts : Array Pt) (diam2 : Nat) (missing : List Nat) (q : Array Pt)
    (f : Rat) (hpos : 0 < pts.size * diam2)
    (h : bestFineMove pts diam2 (presentEdges q.size missing) q f = none) :
    ∀ c ∈ fineMoves q, f ≤ objectivePolygon pts diam2 c.1 missing := by
  sorry

/-- For a segment, the fine moves are the whole unit cube (apart from not moving).

Proof (planned): `fineMoves` for `n = 2` lists `(q[0] + d₀, q[1] + d₁)` for all offsets
`d₀, d₁ ∈ unitOffsets` except both `(0, 0)`, and `unitOffsets` is `{-1, 0, 1}²`. -/
theorem fineMoves_two (q q' : Array Pt) (hq : q.size = 2) (h : InUnitCube q q') :
    q' = q ∨ ∃ c ∈ fineMoves q, c.1 = q' := by
  sorry

/-- An ultra-fine move is strictly better, keeps the vertex count, and is scored honestly.

Proof (planned): as `bestFineMove_some`, with the table entries equal to `edgeTerms` of
the moved endpoints. -/
theorem bestCubeMove_some (pts : Array Pt) (diam2 : Nat) (missing : List Nat) (q q' : Array Pt)
    (f f' : Rat) (h : bestCubeMove pts diam2 (presentEdges q.size missing) q f = some (q', f')) :
    f' < f ∧ q'.size = q.size ∧ f' = objectivePolygon pts diam2 q' missing := by
  sorry

/-- If no ultra-fine move is chosen, no polygon in the unit cube beats `f = F²(q)`.

Proof (planned): `foldOffsetChoices` visits every assignment of offsets to the
vertices. Each one other than "no vertex moves" is either ruled out by the whole-number
lower bound, which is sound because every term is `≥ 0` (section A) and
`⌊c x⌋ ≤ c x ≤ ⌈c x⌉`, or by `objectiveBelow_none`; with no candidate ever accepted, the
bound stays `f`. "No vertex moves" is `q` itself, scored `f`. -/
theorem bestCubeMove_none (pts : Array Pt) (diam2 : Nat) (missing : List Nat) (q : Array Pt)
    (f : Rat) (hpos : 0 < pts.size * diam2) (hf : f = objectivePolygon pts diam2 q missing)
    (h : bestCubeMove pts diam2 (presentEdges q.size missing) q f = none) :
    ∀ q', InUnitCube q q' → f ≤ objectivePolygon pts diam2 q' missing := by
  sorry





/-! ## D. The fine search -/

/-- The fine search keeps `f = F²(q)` and the vertex count, never increases `f`, and when
it converges, no fine move beats the result.

Proof (planned): induction on the moves left in `fineSearch.go`, using
`bestFineMove_some` for each accepted move. -/
theorem fineSearch_spec (pts : Array Pt) (diam2 : Nat) (missing : List Nat) (q₀ : Array Pt)
    (f₀ : Rat) (fuel : Nat) (hf : f₀ = objectivePolygon pts diam2 q₀ missing) :
    let r := fineSearch pts diam2 (presentEdges q₀.size missing) q₀ f₀ fuel
    r.1.size = q₀.size ∧ r.2.1 = objectivePolygon pts diam2 r.1 missing ∧ r.2.1 ≤ f₀ ∧
      (r.2.2.2 = true → bestFineMove pts diam2 (presentEdges q₀.size missing) r.1 r.2.1 = none) := by
  sorry

/-! ## E. `polish` -/

/-- `polish` keeps the number of vertices.

Proof (planned): induction on the rounds left in `polish.go`, with `fineSearch_spec` and
`bestCubeMove_some`. -/
theorem polish_size (pts : Array Pt) (missing : List Nat) (start : Array Pt) (fuel ultraMax : Nat) :
    (polish pts missing start fuel ultraMax).vertices.size = start.size := by
  sorry

/-- The reported `F²` is the computed objective of the reported polygon.

Proof (planned): the same induction; the invariant `f = F²(q)` holds at the start by
definition and is kept by `fineSearch_spec` and `bestCubeMove_some`. -/
theorem polish_objectiveSq (pts : Array Pt) (missing : List Nat) (start : Array Pt) (fuel ultraMax : Nat) :
    let r := polish pts missing start fuel ultraMax
    r.objectiveSq = objectivePolygon pts (diamSq pts) r.vertices missing := by
  sorry

/-- The search never ends worse than it started.

Proof (planned): the same induction; `f` only ever decreases. -/
theorem polish_le_start (pts : Array Pt) (missing : List Nat) (start : Array Pt) (fuel ultraMax : Nat) :
    (polish pts missing start fuel ultraMax).objectiveSq
      ≤ objectivePolygon pts (diamSq pts) start missing := by
  sorry

/-- **The certificate.** If `diam(P) > 0` and the result is certified, no polygon in the
unit cube around it has a lower computed objective.

Proof (planned): the same induction. `certified` is reported only (a) for `n = 2`, when
the last fine search converged: `fineSearch_spec`, `bestFineMove_none` and
`fineMoves_two`; or (b) when the last fine search converged and `bestCubeMove` found
nothing: `bestCubeMove_none`. In both cases `polish_objectiveSq` covers `Q' = r.vertices`. -/
theorem polish_certified (pts : Array Pt) (missing : List Nat) (start : Array Pt) (fuel ultraMax : Nat)
    (hdiam : 0 < diamSq pts) (hcert : (polish pts missing start fuel ultraMax).certified = true) :
    let r := polish pts missing start fuel ultraMax
    ∀ q', InUnitCube r.vertices q' → r.objectiveSq ≤ objectivePolygon pts (diamSq pts) q' missing := by
  sorry

end PolyFit
