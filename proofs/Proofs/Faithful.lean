import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Proofs.Point
import Proofs.Polish

/-!
# Faithfulness: the computed objective is the mathematical `F²`

The search theorems (`Polish.lean`) are about `objectivePolygon`, the objective as the
solver computes it in exact rationals. Here `F²` is defined again, directly from the
specification and independently of the solver's formulas: in the real plane, with
infima over the edges and an integral along each edge. The goal is
`objectivePolygon_eq_trueF2`: the two agree for every polygon without zero-length edges.

**Plan.**
1. *The definitions and the assembly* (this file's first part): `trueF2` from `D1Sq`,
   `D2Sq`, `infDistSq`; and `objectivePolygon_eq_trueF2` from the three facts below plus
   bookkeeping (the infimum over a union of edges is the minimum over the edges, sums
   and means).
2. *`D₁` for one segment* (`distSqToSegment_eq`): the code's three-branch formula is the
   infimum of the squared distance over the segment.
3. *`D₂` for one segment* (`segmentIntegral_eq`): the envelope walk computes the integral
   of the squared distance to `P` along the segment.
Also `diamSq_eq`: the solver's `diamSq` is the largest squared distance in `P`.

With these, `polish_certified_true`: a certified result is a local minimum of the true
`F²` among the polygons in its unit cube that have no zero-length edges.
-/

namespace PolyFit

/-! ## The mathematical objective, in the real plane -/

/-- A pixel as a point of the real plane. -/
def Pt.toR (p : Pt) : ℝ × ℝ := (p.i, p.j)

/-- The squared Euclidean distance `d(x, y)²`. (Mathlib's own distance on `ℝ × ℝ` is the
larger of the two coordinate distances, so it is not used here.) -/
def eDistSq (x y : ℝ × ℝ) : ℝ := (x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2

/-- The point `a + t (b - a)` of the line through `a` and `b`. -/
def segPt (a b : ℝ × ℝ) (t : ℝ) : ℝ × ℝ := (a.1 + t * (b.1 - a.1), a.2 + t * (b.2 - a.2))

/-- The segment from `a` to `b`, as a set of points. -/
def seg (a b : ℝ × ℝ) : Set (ℝ × ℝ) := segPt a b '' Set.Icc 0 1

/-- `d₁(x, A)² = inf_{y ∈ A} d(x, y)²`, the square of the distance from `x` to the set `A`. -/
noncomputable def infDistSq (x : ℝ × ℝ) (A : Set (ℝ × ℝ)) : ℝ := sInf (eDistSq x '' A)

/-- `P` as a set of points of the plane. -/
def ptSet (pts : Array Pt) : Set (ℝ × ℝ) := {x | ∃ p ∈ pts, x = p.toR}

/-- `diam(P)² = sup_{p, p' ∈ P} d(p, p')²`. -/
noncomputable def diamSqR (pts : Array Pt) : ℝ :=
  sSup {d | ∃ p ∈ pts, ∃ p' ∈ pts, d = eDistSq p.toR p'.toR}

/-- `D₁(P, A)² = (1 / diam(P)²) · mean_{p ∈ P} d₁(p, A)²`. -/
noncomputable def D1Sq (pts : Array Pt) (A : Set (ℝ × ℝ)) : ℝ :=
  (pts.toList.map fun p => infDistSq p.toR A).sum / pts.size / diamSqR pts

/-- `D₂(ℓ, P)² = (1 / L(ℓ)²) ∫₀¹ d₁(a + t (b − a), P)² dt` for the segment `ℓ` from `a` to `b`. -/
noncomputable def D2Sq (pts : Array Pt) (a b : ℝ × ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..1, infDistSq (segPt a b t) (ptSet pts)) / eDistSq a b

/-- The polygon `Q`: the union of its present edges, edge `e` joining `qs[e]` to
`qs[(e + 1) mod n]`. (`presentEdges n M` is `{0}` for `n = 2` and `{e < n | e ∉ M}`
otherwise, as in the specification.) -/
def polygonSet (qs : Array Pt) (missing : List Nat) : Set (ℝ × ℝ) :=
  ⋃ e ∈ presentEdges qs.size missing, seg qs[e]!.toR qs[(e + 1) % qs.size]!.toR

/-- `F² = ½ D₁(P, Q)² + (1 / (2m)) Σ_{present ℓ} D₂(ℓ, P)²`, with `m` present edges
(for `n = 2` this is `½ D₁(P, ℓ)² + ½ D₂(ℓ, P)²`). -/
noncomputable def trueF2 (pts : Array Pt) (qs : Array Pt) (missing : List Nat) : ℝ :=
  D1Sq pts (polygonSet qs missing) / 2
    + ((presentEdges qs.size missing).map fun e =>
        D2Sq pts qs[e]!.toR qs[(e + 1) % qs.size]!.toR).sum
      / (2 * (presentEdges qs.size missing).length)

/-! ## The three facts about single quantities -/

/-- `d(p, q)²` in the plane. -/
theorem distSq_toR (p q : Pt) : (distSq p q : ℝ) = eDistSq p.toR q.toR := by
  rw [← Int.cast_natCast, distSq_eq]
  simp only [eDistSq, Pt.toR]
  push_cast
  ring

/-- **Step 2.** The code's point-to-segment distance is the true one (also for a
zero-length segment, which is a single point).

Proof: with `w = p − q₀`, `v = q₁ − q₀`, `P = w · v` and `L = |v|²`, the squared distance
along the segment is the parabola `g(t) = L t² − 2 P t + |w|²`. The code's value is the least
`g(t)` on `[0, 1]`: at `t = 0` if `P ≤ 0` (`g(t) − g(0) = t (L t − 2P)`), at `t = 1` if
`P ≥ L` (`g(t) − g(1) = (1 − t)(2P − L (1 + t))`), and otherwise at `t* = P / L`, where
`g(t) = L (t − t*)² + (w × v)² / L` by Lagrange's identity
`|w|² |v|² − (w · v)² = (w × v)²`. A least element is the infimum. -/
theorem distSqToSegment_eq (p q₀ q₁ : Pt) :
    (distSqToSegment p q₀ q₁ : ℝ) = infDistSq p.toR (seg q₀.toR q₁.toR) := by
  -- the coordinates of `w = p − q₀` and `v = q₁ − q₀`, as reals
  set wi : ℝ := ((p.i - q₀.i : ℤ) : ℝ) with hwi
  set wj : ℝ := ((p.j - q₀.j : ℤ) : ℝ) with hwj
  set vi : ℝ := ((q₁.i - q₀.i : ℤ) : ℝ) with hvi
  set vj : ℝ := ((q₁.j - q₀.j : ℤ) : ℝ) with hvj
  have hg : ∀ t, eDistSq p.toR (segPt q₀.toR q₁.toR t) = (wi - t * vi) ^ 2 + (wj - t * vj) ^ 2 := by
    intro t
    simp only [eDistSq, segPt, Pt.toR, hwi, hwj, hvi, hvj]
    push_cast
    ring
  have hP : ((dot (p - q₀) (q₁ - q₀) : ℤ) : ℝ) = wi * vi + wj * vj := by
    simp only [dot, hwi, hwj, hvi, hvj]
    show (((p.i - q₀.i) * (q₁.i - q₀.i) + (p.j - q₀.j) * (q₁.j - q₀.j) : ℤ) : ℝ) = _
    push_cast; ring
  have hL : ((dot (q₁ - q₀) (q₁ - q₀) : ℤ) : ℝ) = vi ^ 2 + vj ^ 2 := by
    simp only [dot, hvi, hvj]
    show (((q₁.i - q₀.i) * (q₁.i - q₀.i) + (q₁.j - q₀.j) * (q₁.j - q₀.j) : ℤ) : ℝ) = _
    push_cast; ring
  have hX : ((cross (p - q₀) (q₁ - q₀) : ℤ) : ℝ) = wi * vj - wj * vi := by
    simp only [cross, hwi, hwj, hvi, hvj]
    show (((p.i - q₀.i) * (q₁.j - q₀.j) - (p.j - q₀.j) * (q₁.i - q₀.i) : ℤ) : ℝ) = _
    push_cast; ring
  have hd₀ : ((distSq p q₀ : ℚ) : ℝ) = wi ^ 2 + wj ^ 2 := by
    rw [Rat.cast_natCast, distSq_toR]
    simp only [eDistSq, Pt.toR, hwi, hwj]
    push_cast; ring
  have hd₁ : ((distSq p q₁ : ℚ) : ℝ) = (wi - vi) ^ 2 + (wj - vj) ^ 2 := by
    rw [Rat.cast_natCast, distSq_toR]
    simp only [eDistSq, Pt.toR, hwi, hwj, hvi, hvj]
    push_cast; ring
  have hL0 : 0 ≤ vi ^ 2 + vj ^ 2 := by positivity
  -- the code's value is the least squared distance along the segment
  unfold infDistSq seg
  rw [Set.image_image]
  symm
  apply IsLeast.csInf_eq
  simp only [distSqToSegment]
  split_ifs with h₁ h₂
  · -- `P ≤ 0`: the nearest point is `q₀`
    have hP0 : wi * vi + wj * vj ≤ 0 := by rw [← hP]; exact_mod_cast h₁
    refine ⟨⟨0, ⟨le_rfl, zero_le_one⟩, by beta_reduce; rw [hg, hd₀]; ring⟩, ?_⟩
    rintro _ ⟨t, ⟨ht0, -⟩, rfl⟩
    beta_reduce; rw [hg, hd₀]
    nlinarith [mul_nonneg ht0 (mul_nonneg ht0 hL0), mul_nonneg ht0 (neg_nonneg.2 hP0)]
  · -- `P ≥ L`: the nearest point is `q₁`
    have hPL : vi ^ 2 + vj ^ 2 ≤ wi * vi + wj * vj := by rw [← hP, ← hL]; exact_mod_cast h₂
    refine ⟨⟨1, ⟨zero_le_one, le_rfl⟩, by beta_reduce; rw [hg, hd₁]; ring⟩, ?_⟩
    rintro _ ⟨t, ⟨-, ht1⟩, rfl⟩
    beta_reduce; rw [hg, hd₁]
    have h1t : 0 ≤ 1 - t := sub_nonneg.2 ht1
    have hk : 0 ≤ 2 * (wi * vi + wj * vj) - (vi ^ 2 + vj ^ 2) * (1 + t) := by
      nlinarith [mul_nonneg h1t hL0]
    nlinarith [mul_nonneg h1t hk]
  · -- `0 < P < L`: the nearest point is at `t* = P / L`, inside the segment
    have hP0 : 0 < wi * vi + wj * vj := by rw [← hP]; exact_mod_cast lt_of_not_ge h₁
    have hPL : wi * vi + wj * vj < vi ^ 2 + vj ^ 2 := by rw [← hP, ← hL]; exact_mod_cast lt_of_not_ge h₂
    have hLpos : 0 < vi ^ 2 + vj ^ 2 := hP0.trans hPL
    set T := (wi * vi + wj * vj) / (vi ^ 2 + vj ^ 2) with hT
    have hval : (((((cross (p - q₀) (q₁ - q₀) ^ 2 : ℤ) : ℚ) / ((dot (q₁ - q₀) (q₁ - q₀) : ℤ) : ℚ) : ℚ)) : ℝ)
        = (wi * vj - wj * vi) ^ 2 / (vi ^ 2 + vj ^ 2) := by
      push_cast
      rw [hX, hL]
    -- `g(t) = L (t − t*)² + (w × v)² / L`
    have hform : ∀ t, (wi - t * vi) ^ 2 + (wj - t * vj) ^ 2
        = (vi ^ 2 + vj ^ 2) * (t - T) ^ 2 + (wi * vj - wj * vi) ^ 2 / (vi ^ 2 + vj ^ 2) := by
      intro t
      rw [hT]
      field_simp
      ring
    refine ⟨⟨T, ⟨div_nonneg hP0.le hLpos.le, (div_le_one hLpos).2 hPL.le⟩, ?_⟩, ?_⟩
    · beta_reduce; rw [hg, hval, hform]; ring
    · rintro _ ⟨t, -, rfl⟩
      beta_reduce; rw [hg, hval, hform]
      nlinarith [mul_nonneg hLpos.le (sq_nonneg (t - T))]

/-- **Step 3.** The code's segment integral is the true integral of the squared distance
to `P` along the segment (for nonempty `P`). -/
theorem segmentIntegral_eq (pts : Array Pt) (hP : pts.size ≠ 0) (q₀ q₁ : Pt) :
    (segmentIntegral pts q₀ q₁ : ℝ) = ∫ t in (0 : ℝ)..1, infDistSq (segPt q₀.toR q₁.toR t) (ptSet pts) := by
  sorry

/-- A fold whose steps never decrease the value: a property that holds right after the
step at `a` and is closed upwards holds at the end. -/
theorem foldl_mono_reach {α : Type} (f : Nat → α → Nat) (hf : ∀ b a, b ≤ f b a)
    (Q : α → Nat → Prop) (hQ : ∀ a b, Q a (f b a)) (hup : ∀ a x y, Q a x → x ≤ y → Q a y)
    (l : List α) : ∀ init, ∀ a ∈ l, Q a (l.foldl f init) := by
  have hge : ∀ (l : List α) init, init ≤ l.foldl f init := by
    intro l
    induction l with
    | nil => intro init; exact le_rfl
    | cons x xs ih => intro init; exact (hf init x).trans (ih _)
  induction l with
  | nil => intro init a ha; simp at ha
  | cons x xs ih =>
    intro init a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact hup _ _ _ (hQ a init) (hge xs _)
    · exact ih _ a ha

/-- The solver's `diamSq` is `diam(P)²`.

Proof: the double `max` fold is at least every `d(p, p')²` (`foldl_mono_reach`) and is
one of them, or 0 = `d(p, p)²`; so it is the largest, which is the supremum. -/
theorem diamSq_eq (pts : Array Pt) : (diamSq pts : ℝ) = diamSqR pts := by
  by_cases hP : pts.size = 0
  · obtain rfl : pts = #[] := Array.size_eq_zero_iff.1 hP
    simp [diamSq, diamSqR]
  obtain ⟨p₀, hp₀⟩ : ∃ p, p ∈ pts := ⟨pts[0], Array.getElem_mem (by omega)⟩
  unfold diamSqR
  -- every pair is at most the fold
  have hup : ∀ p ∈ pts, ∀ p' ∈ pts, distSq p p' ≤ diamSq pts := by
    intro p hp p' hp'
    unfold diamSq
    rw [← Array.foldl_toList]
    refine foldl_mono_reach _ (fun b q => ?_) (fun p x => ∀ p' ∈ pts, distSq p p' ≤ x) (fun q b => ?_)
      (fun _ _ _ hx hxy p' hp' => (hx p' hp').trans hxy) pts.toList 0 p (by simpa using hp) p' hp'
    · rw [← Array.foldl_toList]
      exact foldl_preserves (b ≤ ·) _ _ _ le_rfl fun c _ _ hc => hc.trans (le_max_left _ _)
    · intro p' hp'
      rw [← Array.foldl_toList]
      refine foldl_mono_reach (fun c r => max c (distSq q r)) (fun _ _ => le_max_left _ _)
        (fun r x => distSq q r ≤ x) (fun _ _ => le_max_right _ _) (fun _ _ _ hx hxy => hx.trans hxy)
        pts.toList b p' (by simpa using hp')
  -- the fold is one of the pairs (or 0)
  have hmem : diamSq pts = 0 ∨ ∃ p ∈ pts, ∃ p' ∈ pts, diamSq pts = distSq p p' := by
    unfold diamSq
    refine foldl_preserves' (fun b => b = 0 ∨ ∃ p ∈ pts, ∃ p' ∈ pts, b = distSq p p') _ pts 0 (Or.inl rfl) ?_
    intro b p hp hb
    refine foldl_preserves' (fun b => b = 0 ∨ ∃ p ∈ pts, ∃ p' ∈ pts, b = distSq p p') _ pts b hb ?_
    intro c p' hp' hc
    rcases max_choice c (distSq p p') with h | h
    · rw [h]; exact hc
    · exact Or.inr ⟨p, hp, p', hp', h⟩
  symm
  apply IsGreatest.csSup_eq
  refine ⟨?_, ?_⟩
  · rcases hmem with h | ⟨p, hp, p', hp', h⟩
    · refine ⟨p₀, hp₀, p₀, hp₀, ?_⟩
      rw [h, ← distSq_toR]
      simp [distSq]
    · exact ⟨p, hp, p', hp', by rw [h, distSq_toR]⟩
  · rintro _ ⟨p, hp, p', hp', rfl⟩
    rw [← distSq_toR]
    exact_mod_cast hup p hp p' hp' 

/-! ## Step 1: the assembly -/

theorem eDistSq_nonneg (x y : ℝ × ℝ) : 0 ≤ eDistSq x y := by
  unfold eDistSq; positivity

/-- A nonempty set of squared distances is bounded below (by 0). -/
theorem bddBelow_eDistSq (x : ℝ × ℝ) (A : Set (ℝ × ℝ)) : BddBelow (eDistSq x '' A) :=
  ⟨0, by rintro _ ⟨y, -, rfl⟩; exact eDistSq_nonneg x y⟩

theorem seg_nonempty (a b : ℝ × ℝ) : (seg a b).Nonempty :=
  ⟨segPt a b 0, 0, ⟨le_rfl, zero_le_one⟩, rfl⟩

/-- The squared distance to a union of sets: if `v` is the distance to one of them and at
most the distance to each, it is the distance to the union. -/
theorem infDistSq_biUnion_eq (x : ℝ × ℝ) (E : List Nat) (S : Nat → Set (ℝ × ℝ))
    (hS : ∀ e ∈ E, (S e).Nonempty) (v : ℝ) (e₀ : Nat) (he₀ : e₀ ∈ E) (hv : v = infDistSq x (S e₀))
    (hle : ∀ e ∈ E, v ≤ infDistSq x (S e)) :
    infDistSq x (⋃ e ∈ E, S e) = v := by
  unfold infDistSq at *
  apply le_antisymm
  · rw [hv]
    apply csInf_le_csInf (bddBelow_eDistSq x _) ((hS e₀ he₀).image _)
    exact Set.image_mono (Set.subset_biUnion_of_mem (u := S) he₀)
  · apply le_csInf
    · obtain ⟨y, hy⟩ := hS e₀ he₀
      exact ⟨eDistSq x y, y, Set.mem_biUnion he₀ hy, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨e, he, hye⟩ := Set.mem_iUnion₂.1 hy
      exact (hle e he).trans (csInf_le (bddBelow_eDistSq x _) ⟨y, hye, rfl⟩)

/-- A `ℚ` sum, read in `ℝ`. -/
theorem cast_foldl_add {α : Type} (l : List α) (f : α → ℚ) (a : ℚ) :
    ((l.foldl (fun s x => s + f x) a : ℚ) : ℝ) = l.foldl (fun s x => s + (f x : ℝ)) (a : ℝ) := by
  induction l generalizing a with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons, ih, Rat.cast_add]

/-- `|b − a|² = 0` only for `a = b`. -/
theorem eq_of_dot_self_eq_zero (a b : Pt) (h : dot (b - a) (b - a) = 0) : a = b := by
  have hi : b.i - a.i = 0 := by
    have : dot (b - a) (b - a) = (b.i - a.i) * (b.i - a.i) + (b.j - a.j) * (b.j - a.j) := rfl
    nlinarith [mul_self_nonneg (b.i - a.i), mul_self_nonneg (b.j - a.j)]
  have hj : b.j - a.j = 0 := by
    have : dot (b - a) (b - a) = (b.i - a.i) * (b.i - a.i) + (b.j - a.j) * (b.j - a.j) := rfl
    nlinarith [mul_self_nonneg (b.i - a.i), mul_self_nonneg (b.j - a.j)]
  rcases a with ⟨ai, aj⟩
  rcases b with ⟨bi, bj⟩
  simp only at hi hj
  congr 1 <;> omega

/-- `L(ℓ)² = |b − a|²` in the plane. -/
theorem eDistSq_toR (a b : Pt) : eDistSq a.toR b.toR = (dot (b - a) (b - a) : ℝ) := by
  simp only [eDistSq, Pt.toR, dot]
  show _ = ((((b.i - a.i) * (b.i - a.i) + (b.j - a.j) * (b.j - a.j) : Int)) : ℝ)
  push_cast
  ring

/-- `D₂` of an edge of positive length is the true `D₂`. -/
theorem d2Sq_eq (pts : Array Pt) (hP : pts.size ≠ 0) (a b : Pt) (hab : a ≠ b) :
    (d2Sq pts a b : ℝ) = D2Sq pts a.toR b.toR := by
  have hlen : dot (b - a) (b - a) ≠ 0 := fun h => hab (eq_of_dot_self_eq_zero a b h)
  simp only [d2Sq, D2Sq, beq_iff_eq, hlen, ite_false, Rat.cast_div, Rat.cast_intCast,
    segmentIntegral_eq pts hP, eDistSq_toR]

/-- Summing over the point numbers `0, …, k − 1` is summing over the points. -/
theorem map_range'_getElem! {β : Type} (pts : Array Pt) (g : Pt → β) :
    (List.range' 0 pts.size).map (fun i => g pts[i]!) = pts.toList.map g := by
  apply List.ext_getElem (by simp)
  intro j h₁ _
  simp only [List.length_map, List.length_range'] at h₁
  simp [getElem!_pos pts j h₁]

/-- **Faithfulness.** For a polygon whose present edges all have positive length, and a
nonempty `P`, the computed objective is the true `F²`.

Proof: per point, the code's nearest-edge distance is a minimum over the edges, which is
the infimum over their union (`infDistSq_biUnion_eq`, with `distSqToSegment_eq` per
edge); per edge, the code's `D₂` is the true `D₂` (`d2Sq_eq`); and `diamSq_eq`. The rest
is sums and normalisations. -/
theorem objectivePolygon_eq_trueF2 (pts : Array Pt) (qs : Array Pt) (missing : List Nat)
    (hP : pts.size ≠ 0)
    (hlen : ∀ e ∈ presentEdges qs.size missing, qs[e]! ≠ qs[(e + 1) % qs.size]!) :
    (objectivePolygon pts (diamSq pts) qs missing : ℝ) = trueF2 pts qs missing := by
  set E := presentEdges qs.size missing with hE
  set edges := E.toArray.map fun e => edgeTerms pts qs[e]! qs[(e + 1) % qs.size]! with hedges
  have hobj : objectivePolygon pts (diamSq pts) qs missing = objectiveFromEdges pts.size (diamSq pts) edges := rfl
  -- per point: the nearest-edge distance
  have hnear : ∀ i < pts.size,
      (nearestSq edges i : ℝ) = infDistSq pts[i]!.toR (polygonSet qs missing) := by
    intro i hi
    have hentry : ∀ t ∈ edges, ∃ e ∈ E, t = edgeTerms pts qs[e]! qs[(e + 1) % qs.size]! := by
      intro t ht
      obtain ⟨e, he, rfl⟩ := Array.mem_map.1 ht
      exact ⟨e, by simpa using he, rfl⟩
    have hval : ∀ e, (edgeTerms pts qs[e]! qs[(e + 1) % qs.size]!).distSqs[i]!
        = distSqToSegment pts[i]! qs[e]! qs[(e + 1) % qs.size]! := by
      intro e
      simp only [edgeTerms]
      rw [getElem!_map_of_lt _ _ i hi]
    by_cases hnil : E = []
    · -- no present edges: both are 0
      have : edges = #[] := by simp [hedges, hnil]
      simp only [polygonSet, ← hE, hnil, List.not_mem_nil, Set.iUnion_of_empty, Set.iUnion_empty,
        infDistSq, Set.image_empty, Real.sInf_empty, nearestSq, this]
      simp [show (default : EdgeTerms).distSqs = #[] from rfl, show (default : Rat) = 0 from rfl]
    · obtain ⟨e₀, he₀⟩ := List.exists_mem_of_ne_nil E hnil
      have hsize : 0 < edges.size := by
        simp [hedges]; exact List.length_pos_of_mem he₀
      -- the code's minimum: at most each edge's distance, and equal to one of them
      have hlow := foldl_min_le (fun t : EdgeTerms => t.distSqs[i]!) edges.toList (edges[0]!.distSqs[i]!)
      simp only [Array.foldl_toList] at hlow
      -- `v`: the code's minimum, which is one of the edge values and at most each of them
      have key : ∀ (v : ℚ) (t₀ : EdgeTerms), t₀ ∈ edges → v = t₀.distSqs[i]! →
          (∀ t ∈ edges, v ≤ t.distSqs[i]!) →
          (v : ℝ) = infDistSq pts[i]!.toR (polygonSet qs missing) := by
        intro v t₀ ht₀ hv hle
        obtain ⟨f₀, hf₀, rfl⟩ := hentry t₀ ht₀
        unfold polygonSet
        refine (infDistSq_biUnion_eq _ E _ (fun e _ => seg_nonempty _ _) _ f₀ hf₀ ?_ ?_).symm
        · rw [hv, hval, distSqToSegment_eq]
        · intro e he
          rw [← distSqToSegment_eq, ← hval]
          exact_mod_cast hle _ (by simpa [hedges] using ⟨e, he, rfl⟩)
      have hlow := foldl_min_le (fun t : EdgeTerms => t.distSqs[i]!) edges.toList (edges[0]!.distSqs[i]!)
      simp only [Array.foldl_toList] at hlow
      have h0mem : edges[0]! ∈ edges := by
        rw [getElem!_pos edges 0 hsize]; exact Array.getElem_mem hsize
      unfold nearestSq
      rcases foldl_min_cases (fun t : EdgeTerms => t.distSqs[i]!) edges.toList (edges[0]!.distSqs[i]!)
        with h | ⟨t, ht, h⟩ <;> rw [Array.foldl_toList] at h
      · exact key _ _ h0mem h fun t ht => hlow.2 t (by simpa using ht)
      · exact key _ t (by simpa using ht) h fun t ht => hlow.2 t (by simpa using ht)
  -- the `D₁` sum over the points
  have hd1 : (d1Sum edges pts.size 0 0 : ℝ) = (pts.toList.map fun p => infDistSq p.toR (polygonSet qs missing)).sum := by
    rw [d1Sum, cast_foldl_add, Rat.cast_zero, foldl_add_eq_sum, zero_add,
      ← map_range'_getElem! pts fun p => infDistSq p.toR (polygonSet qs missing)]
    congr 1
    apply List.map_congr_left
    intro i hi
    exact hnear i (by simp at hi; omega)
  -- the `D₂` sum over the edges
  have hd2 : (((edges.foldl (init := (0 : ℚ)) (· + ·.d2) : ℚ)) : ℝ)
      = (E.map fun e => D2Sq pts qs[e]!.toR qs[(e + 1) % qs.size]!.toR).sum := by
    rw [hedges, Array.foldl_map, List.foldl_toArray, cast_foldl_add, Rat.cast_zero, foldl_add_eq_sum, zero_add]
    congr 1
    apply List.map_congr_left
    intro e he
    exact d2Sq_eq pts hP _ _ (hlen e he)
  have hsz : edges.size = E.length := by simp [hedges]
  rw [hobj, objectiveFromEdges_eq]
  push_cast
  rw [hd1, hd2, hsz, diamSq_eq]
  unfold trueF2 D1Sq
  rw [← hE]
  ring

/-- **The certificate, for the true `F²`.** If `diam(P) > 0` and the result is certified,
it has no larger true `F²` than any polygon in its unit cube, as long as neither has a
zero-length edge. -/
theorem polish_certified_true (pts : Array Pt) (missing : List Nat) (start : Array Pt) (fuel ultraMax : Nat)
    (hdiam : 0 < diamSq pts) (hcert : (polish pts missing start fuel ultraMax).certified = true) :
    let r := polish pts missing start fuel ultraMax
    (∀ e ∈ presentEdges r.vertices.size missing, r.vertices[e]! ≠ r.vertices[(e + 1) % r.vertices.size]!) →
    ∀ q', InUnitCube r.vertices q' →
      (∀ e ∈ presentEdges q'.size missing, q'[e]! ≠ q'[(e + 1) % q'.size]!) →
      trueF2 pts r.vertices missing ≤ trueF2 pts q' missing := by
  intro r hr q' hq' hq'len
  have hP : pts.size ≠ 0 := (size_pos_of_diamSq_pos pts hdiam).ne'
  have h := polish_certified pts missing start fuel ultraMax hdiam hcert q' hq'
  rw [← objectivePolygon_eq_trueF2 pts _ missing hP hr, ← objectivePolygon_eq_trueF2 pts q' missing hP hq'len,
    ← polish_objectiveSq pts missing start fuel ultraMax]
  exact_mod_cast h

end PolyFit
