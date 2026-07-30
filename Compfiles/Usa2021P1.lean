/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 2021, Problem 1

Rectangles BCC₁B₂, CAA₁C₂, and ABB₁A₂ are erected outside an acute
triangle ABC. Suppose that

  ∠BC₁C + ∠CA₁A + ∠AB₁B = 180°.

Prove that lines B₁C₂, C₁A₂, and A₁B₂ are concurrent.
-/

namespace Usa2021P1

open scoped EuclideanGeometry RealInnerProductSpace

snip begin

/-- The plane is two-dimensional (used to build an orthonormal frame). -/
local instance planeFiniteDim :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- If `T₁ = T + h • n` where `n` is a unit vector perpendicular to `T - S`
(so that `STT₁` has a right angle at `T`), then the cosine of the angle at
`T₁` equals `h / sqrt (‖T - S‖² + h²)`. -/
lemma rect_angle_cos {h : ℝ} {n S T T₁ : V}
    (hh : 0 < h) (hn : ‖n‖ = 1) (hperp : ⟪n, T - S⟫ = 0) (hT₁ : T₁ = T + h • n) :
    Real.cos (∠ S T₁ T) = h / Real.sqrt (‖T - S‖ ^ 2 + h ^ 2) := by
  have hn2 : ⟪n, n⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, hn]; norm_num
  have hperp' : ⟪S - T, n⟫ = 0 := by
    have h1 : S - T = -(T - S) := by abel
    rw [h1, inner_neg_left, real_inner_comm n (T - S), hperp, neg_zero]
  have hTT₁ : T - T₁ = -(h • n) := by rw [hT₁]; abel
  have hST₁ : S - T₁ = (S - T) + -(h • n) := by rw [hT₁]; abel
  have h_inner : ⟪S - T₁, T - T₁⟫ = h ^ 2 := by
    rw [hST₁, hTT₁]
    simp only [inner_add_left, inner_neg_left, inner_neg_right, real_inner_smul_left,
      real_inner_smul_right, hperp', hn2]
    ring
  have h_norm₁ : ‖T - T₁‖ = h := by
    rw [hTT₁, norm_neg, norm_smul, hn, Real.norm_eq_abs, abs_of_pos hh, mul_one]
  have h_norm₂ : ‖S - T₁‖ = Real.sqrt (‖T - S‖ ^ 2 + h ^ 2) := by
    have h1 : ‖S - T₁‖ ^ 2 = ‖T - S‖ ^ 2 + h ^ 2 := by
      rw [hST₁, pow_two ‖S - T + -(h • n)‖, pow_two ‖T - S‖, pow_two h,
        norm_add_sq_eq_norm_sq_add_norm_sq_real]
      · congr 1
        · rw [norm_sub_rev]
        · rw [norm_neg, norm_smul, hn, Real.norm_eq_abs, abs_of_pos hh, mul_one]
      · rw [inner_neg_right, real_inner_smul_right, hperp', mul_zero, neg_zero]
    rw [← h1, Real.sqrt_sq (norm_nonneg _)]
  rw [EuclideanGeometry.angle, vsub_eq_sub, vsub_eq_sub, InnerProductGeometry.cos_angle,
    h_inner, h_norm₁, h_norm₂, pow_two h, mul_div_mul_right h _ (ne_of_gt hh)]

/-- The sine version of `rect_angle_cos`. -/
lemma rect_angle_sin {h : ℝ} {n S T T₁ : V}
    (hh : 0 < h) (hn : ‖n‖ = 1) (hperp : ⟪n, T - S⟫ = 0) (hT₁ : T₁ = T + h • n) :
    Real.sin (∠ S T₁ T) = ‖T - S‖ / Real.sqrt (‖T - S‖ ^ 2 + h ^ 2) := by
  have hcos := rect_angle_cos hh hn hperp hT₁
  have h0 : 0 ≤ ∠ S T₁ T := by
    rw [EuclideanGeometry.angle]; exact InnerProductGeometry.angle_nonneg _ _
  have hpi : ∠ S T₁ T ≤ Real.pi := by
    rw [EuclideanGeometry.angle]; exact InnerProductGeometry.angle_le_pi _ _
  have hX : (0:ℝ) < ‖T - S‖ ^ 2 + h ^ 2 := by
    have h1 : 0 < h ^ 2 := sq_pos_of_pos hh
    have h2 : 0 ≤ ‖T - S‖ ^ 2 := sq_nonneg _
    linarith
  rw [Real.sin_eq_sqrt_one_sub_cos_sq h0 hpi, hcos, div_pow, Real.sq_sqrt (le_of_lt hX)]
  have heq : (1:ℝ) - h ^ 2 / (‖T - S‖ ^ 2 + h ^ 2) =
      ‖T - S‖ ^ 2 / (‖T - S‖ ^ 2 + h ^ 2) := by
    rw [eq_div_iff (ne_of_gt hX), sub_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hX)]
    ring
  rw [heq, Real.sqrt_div (sq_nonneg _) _, Real.sqrt_sq (norm_nonneg _)]

/-- Scalar computation: a unit vector `(x, y)` perpendicular to `(g₁, g₂)` is
one of the two quarter-turns of `(g₁, g₂)`; the side conditions determine
which one. -/
lemma perp_solve {x y g₁ g₂ s₁ s₂ : ℝ} (hg : g₁ ^ 2 + g₂ ^ 2 ≠ 0)
    (hperp : x * g₁ + y * g₂ = 0) (hunit : x ^ 2 + y ^ 2 = 1)
    (hside : s₁ * x + s₂ * y < 0) (hw : s₁ * g₂ - s₂ * g₁ < 0) :
    x = g₂ / Real.sqrt (g₁ ^ 2 + g₂ ^ 2) ∧
      y = -g₁ / Real.sqrt (g₁ ^ 2 + g₂ ^ 2) := by
  set R := Real.sqrt (g₁ ^ 2 + g₂ ^ 2) with hR_def
  have hge : (0:ℝ) ≤ g₁ ^ 2 + g₂ ^ 2 := by positivity
  have hR : 0 < R := Real.sqrt_pos.mpr (lt_of_le_of_ne hge hg.symm)
  have hR2 : R ^ 2 = g₁ ^ 2 + g₂ ^ 2 := Real.sq_sqrt hge
  have h4 : (x * g₂ - y * g₁) ^ 2 = R ^ 2 := by
    linear_combination hunit * (g₁ ^ 2 + g₂ ^ 2) - hperp * (x * g₁ + y * g₂) - hR2
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h4 with hcase | hcase
  · have hx : x * R ^ 2 = g₂ * R := by
      linear_combination hperp * g₁ + hcase * g₂ + hR2 * x
    have hy : y * R ^ 2 = -g₁ * R := by
      linear_combination hperp * g₂ - hcase * g₁ + hR2 * y
    have hx' : x * R = g₂ := mul_right_cancel₀ hR.ne' (by rw [← hx]; ring)
    have hy' : y * R = -g₁ := mul_right_cancel₀ hR.ne' (by rw [← hy]; ring)
    exact ⟨(eq_div_iff hR.ne').mpr hx', (eq_div_iff hR.ne').mpr hy'⟩
  · have hx : x * R ^ 2 = -g₂ * R := by
      linear_combination hperp * g₁ + hcase * g₂ + hR2 * x
    have hy : y * R ^ 2 = g₁ * R := by
      linear_combination hperp * g₂ - hcase * g₁ + hR2 * y
    have hx' : x * R = -g₂ := mul_right_cancel₀ hR.ne' (by rw [← hx]; ring)
    have hy' : y * R = g₁ := mul_right_cancel₀ hR.ne' (by rw [← hy]; ring)
    have hcon : s₁ * x + s₂ * y = -(s₁ * g₂ - s₂ * g₁) / R := by
      rw [(eq_div_iff hR.ne').mpr hx', (eq_div_iff hR.ne').mpr hy']
      field_simp [hR.ne']
      ring
    have hpos : 0 < s₁ * x + s₂ * y := by
      rw [hcon]; exact div_pos (neg_pos.mpr hw) hR
    linarith

/-- Three points given in a two-vector coordinate system are collinear when
the cross product of their coordinate differences vanishes. -/
lemma collinear_of_frame {A P X Y e₁ e₂ : V} {p₁ p₂ x₁ x₂ y₁ y₂ : ℝ}
    (hP : P = A + p₁ • e₁ + p₂ • e₂) (hX : X = A + x₁ • e₁ + x₂ • e₂)
    (hY : Y = A + y₁ • e₁ + y₂ • e₂)
    (hcross : (x₁ - p₁) * (y₂ - p₂) = (x₂ - p₂) * (y₁ - p₁)) :
    Collinear ℝ {P, X, Y} := by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  by_cases hXP : X = P
  · refine ⟨P, Y - P, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨0, by simp [hXP]⟩
    · exact ⟨1, by simp⟩
  · have hd : X - P = (x₁ - p₁) • e₁ + (x₂ - p₂) • e₂ := by
      rw [hX, hP]; module
    have hdd : (x₁ - p₁) ≠ 0 ∨ (x₂ - p₂) ≠ 0 := by
      by_contra h
      push Not at h
      rw [h.1, h.2, zero_smul, zero_smul, add_zero, sub_eq_zero] at hd
      exact hXP hd
    have hY' : Y - P = (y₁ - p₁) • e₁ + (y₂ - p₂) • e₂ := by
      rw [hY, hP]; module
    rcases hdd with h1 | h1
    · have hcoef : y₂ - p₂ = (y₁ - p₁) / (x₁ - p₁) * (x₂ - p₂) := by
        rw [div_mul_eq_mul_div, eq_div_iff h1]
        linear_combination hcross
      have e1 : y₁ - p₁ = (y₁ - p₁) / (x₁ - p₁) * (x₁ - p₁) :=
        (div_mul_cancel₀ (y₁ - p₁) h1).symm
      have hfin : Y - P = ((y₁ - p₁) / (x₁ - p₁)) • (X - P) := by
        rw [hd, smul_add, smul_smul, smul_smul, hY', ← e1, ← hcoef]
      refine ⟨P, X - P, ?_⟩
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
      · refine ⟨(y₁ - p₁) / (x₁ - p₁), ?_⟩
        rw [vadd_eq_add, ← hfin, sub_add_cancel]
    · have hcoef : y₁ - p₁ = (y₂ - p₂) / (x₂ - p₂) * (x₁ - p₁) := by
        rw [div_mul_eq_mul_div, eq_div_iff h1]
        linear_combination -hcross
      have e2 : y₂ - p₂ = (y₂ - p₂) / (x₂ - p₂) * (x₂ - p₂) :=
        (div_mul_cancel₀ (y₂ - p₂) h1).symm
      have hfin : Y - P = ((y₂ - p₂) / (x₂ - p₂)) • (X - P) := by
        rw [hd, smul_add, smul_smul, smul_smul, hY', ← hcoef, ← e2]
      refine ⟨P, X - P, ?_⟩
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
      · refine ⟨(y₂ - p₂) / (x₂ - p₂), ?_⟩
        rw [vadd_eq_add, ← hfin, sub_add_cancel]

/-- Any non-collinear triple `A B C` in a two-dimensional inner product space
admits an adapted frame: orthonormal `e₁ e₂` with `B - A = ‖B - A‖ • e₁` and
`C - A = u • e₁ + v • e₂` with `v > 0`, and every vector is expressible in
the frame. -/
lemma exists_frame [FiniteDimensional ℝ V] [Fact (Module.finrank ℝ V = 2)]
    {A B C : V} (h : ¬Collinear ℝ {A, B, C}) :
    ∃ e₁ e₂ : V, ∃ u v : ℝ, 0 < v ∧ ⟪e₁, e₁⟫ = 1 ∧ ⟪e₂, e₂⟫ = 1 ∧ ⟪e₁, e₂⟫ = 0 ∧
      B - A = ‖B - A‖ • e₁ ∧ C - A = u • e₁ + v • e₂ ∧
      ∀ w : V, w = ⟪w, e₁⟫ • e₁ + ⟪w, e₂⟫ • e₂ := by
  have hAB : A ≠ B := by
    rintro rfl
    apply h
    have h1 : ({A, A, C} : Set V) = {A, C} := by simp
    rw [h1]
    exact collinear_pair ℝ A C
  have hc0 : (0:ℝ) < ‖B - A‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hAB))
  set c := ‖B - A‖ with hc_def
  set e₁ := c⁻¹ • (B - A) with he1_def
  have he1e1 : ⟪e₁, e₁⟫ = 1 := by
    rw [he1_def, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
      ← hc_def, ← mul_assoc, pow_two c, mul_assoc c⁻¹ c⁻¹ (c * c), ← mul_assoc c⁻¹ c c,
      inv_mul_cancel₀ hc0.ne', one_mul, inv_mul_cancel₀ hc0.ne']
  set u := ⟪e₁, C - A⟫ with hu_def
  set w := C - A - u • e₁ with hw_def
  have hw0 : w ≠ 0 := by
    rw [hw_def]
    intro hw0
    apply h
    have hCA : C - A = (u * c⁻¹) • (B - A) := by
      have h1 : C - A = u • e₁ := sub_eq_zero.mp hw0
      rw [h1, he1_def, smul_smul]
    rw [collinear_iff_exists_forall_eq_smul_vadd]
    refine ⟨A, B - A, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · refine ⟨u * c⁻¹, ?_⟩
      rw [vadd_eq_add, ← hCA]; abel
  set v := ‖w‖ with hv_def
  have hv : 0 < v := norm_pos_iff.mpr hw0
  set e₂ := v⁻¹ • w with he2_def
  have he12 : ⟪e₁, w⟫ = 0 := by
    rw [hw_def, inner_sub_right, real_inner_smul_right, he1e1, mul_one, sub_self]
  have he1e2 : ⟪e₁, e₂⟫ = 0 := by
    rw [he2_def, real_inner_smul_right, he12, mul_zero]
  have he2e1 : ⟪e₂, e₁⟫ = 0 := by
    rw [real_inner_comm]; exact he1e2
  have he2e2 : ⟪e₂, e₂⟫ = 1 := by
    rw [he2_def, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
      ← hv_def, ← mul_assoc, pow_two v, mul_assoc v⁻¹ v⁻¹ (v * v), ← mul_assoc v⁻¹ v v,
      inv_mul_cancel₀ hv.ne', one_mul, inv_mul_cancel₀ hv.ne']
  have hCA' : C - A = u • e₁ + v • e₂ := by
    rw [he2_def, smul_inv_smul₀ hv.ne', hw_def]
    abel
  refine ⟨e₁, e₂, u, v, hv, he1e1, he2e2, he1e2, ?_, hCA', ?_⟩
  · show B - A = c • e₁
    rw [he1_def, smul_inv_smul₀ hc0.ne']
  · intro w'
    have he1n : ‖e₁‖ = 1 := by
      have h1 : ‖e₁‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact he1e1
      rcases sq_eq_one_iff.mp h1 with h2 | h2
      · exact h2
      · have h3 := norm_nonneg e₁; linarith
    have he2n : ‖e₂‖ = 1 := by
      have h1 : ‖e₂‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact he2e2
      rcases sq_eq_one_iff.mp h1 with h2 | h2
      · exact h2
      · have h3 := norm_nonneg e₂; linarith
    have hon : Orthonormal ℝ ![e₁, e₂] := by
      refine ⟨?_, ?_⟩
      · intro i
        fin_cases i
        · simpa using he1n
        · simpa using he2n
      · intro i j hij
        fin_cases i <;> fin_cases j
        · exfalso; exact hij rfl
        · simpa using he1e2
        · simpa using he2e1
        · exfalso; exact hij rfl
    have hli := hon.linearIndependent
    have hfr : Module.finrank ℝ V = 2 := Fact.out
    have hspan : Submodule.span ℝ (Set.range ![e₁, e₂]) = ⊤ :=
      hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, hfr])
    have hmem : w' ∈ Submodule.span ℝ (Set.range ![e₁, e₂]) := by
      rw [hspan]; exact Submodule.mem_top
    obtain ⟨coef, hcoef⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
    rw [Fin.sum_univ_two] at hcoef
    have hcoef' : w' = coef 0 • e₁ + coef 1 • e₂ := by
      rw [← hcoef]; simp
    have h0 : ⟪w', e₁⟫ = coef 0 := by
      rw [hcoef']; simp [inner_add_left, real_inner_smul_left, he2e1, he1n]
    have h1 : ⟪w', e₂⟫ = coef 1 := by
      rw [hcoef']; simp [inner_add_left, real_inner_smul_left, he1e2, he2n]
    conv_lhs => rw [hcoef']
    rw [← h0, ← h1]

snip end

problem usa2021_p1
    (A B C C₁ B₂ A₁ C₂ B₁ A₂ : EuclideanSpace ℝ (Fin 2))
    (hABC : AffineIndependent ℝ ![A, B, C])
    (_hAcuteA : ∠ C A B < Real.pi / 2)
    (_hAcuteB : ∠ A B C < Real.pi / 2)
    (_hAcuteC : ∠ B C A < Real.pi / 2)
    (hRectA : ∃ h : ℝ, ∃ n : EuclideanSpace ℝ (Fin 2), 0 < h ∧ ‖n‖ = 1 ∧ ⟪n, C - B⟫ = 0 ∧
      ⟪A - B, n⟫ < 0 ∧ C₁ = C + h • n ∧ B₂ = B + h • n)
    (hRectB : ∃ h : ℝ, ∃ n : EuclideanSpace ℝ (Fin 2), 0 < h ∧ ‖n‖ = 1 ∧ ⟪n, A - C⟫ = 0 ∧
      ⟪B - C, n⟫ < 0 ∧ A₁ = A + h • n ∧ C₂ = C + h • n)
    (hRectC : ∃ h : ℝ, ∃ n : EuclideanSpace ℝ (Fin 2), 0 < h ∧ ‖n‖ = 1 ∧ ⟪n, B - A⟫ = 0 ∧
      ⟪C - A, n⟫ < 0 ∧ B₁ = B + h • n ∧ A₂ = A + h • n)
    (hAngle : ∠ B C₁ C + ∠ C A₁ A + ∠ A B₁ B = Real.pi) :
    ∃ P : EuclideanSpace ℝ (Fin 2),
      Collinear ℝ {P, B₁, C₂} ∧ Collinear ℝ {P, C₁, A₂} ∧ Collinear ℝ {P, A₁, B₂} := by
  obtain ⟨ha, na, hha, hna1, hnap, hnao, hC₁, hB₂⟩ := hRectA
  obtain ⟨hb, nb, hhb, hnb1, hnbp, hnbo, hA₁, hC₂⟩ := hRectB
  obtain ⟨hc, nc, hhc, hnc1, hncp, hnco, hB₁, hA₂⟩ := hRectC
  have hAB : A ≠ B := hABC.injective.ne (by decide : (0 : Fin 3) ≠ 1)
  have hAC : A ≠ C := hABC.injective.ne (by decide : (0 : Fin 3) ≠ 2)
  have hBC : B ≠ C := hABC.injective.ne (by decide : (1 : Fin 3) ≠ 2)
  set a := ‖C - B‖ with ha_def
  set b := ‖A - C‖ with hb_def
  set c := ‖B - A‖ with hc_def
  have ha0 : 0 < a := norm_pos_iff.mpr (sub_ne_zero.mpr hBC.symm)
  have hb0 : 0 < b := norm_pos_iff.mpr (sub_ne_zero.mpr hAC)
  have hc0 : 0 < c := norm_pos_iff.mpr (sub_ne_zero.mpr hAB.symm)
  -- The angles of the three rectangle corners.
  have hcosA := rect_angle_cos hha hna1 hnap hC₁
  have hsinA := rect_angle_sin hha hna1 hnap hC₁
  have hcosB := rect_angle_cos hhb hnb1 hnbp hA₁
  have hsinB := rect_angle_sin hhb hnb1 hnbp hA₁
  have hcosC := rect_angle_cos hhc hnc1 hncp hB₁
  have hsinC := rect_angle_sin hhc hnc1 hncp hB₁
  rw [← ha_def] at hcosA hsinA
  rw [← hb_def] at hcosB hsinB
  rw [← hc_def] at hcosC hsinC
  -- The angle condition, via `sin (α + β + γ) = 0`, becomes a polynomial equation.
  have hsin0 : Real.sin (∠ B C₁ C + ∠ C A₁ A + ∠ A B₁ B) = 0 := by
    rw [hAngle, Real.sin_pi]
  rw [Real.sin_add, Real.sin_add, Real.cos_add, hcosA, hsinA, hcosB, hsinB, hcosC,
    hsinC] at hsin0
  have hA0 : (0:ℝ) < a ^ 2 + ha ^ 2 := by
    have h1 := sq_pos_of_pos ha0; have h2 := sq_nonneg ha; linarith
  have hB0 : (0:ℝ) < b ^ 2 + hb ^ 2 := by
    have h1 := sq_pos_of_pos hb0; have h2 := sq_nonneg hb; linarith
  have hC0 : (0:ℝ) < c ^ 2 + hc ^ 2 := by
    have h1 := sq_pos_of_pos hc0; have h2 := sq_nonneg hc; linarith
  have hsA : √(a ^ 2 + ha ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hA0).ne'
  have hsB : √(b ^ 2 + hb ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hB0).ne'
  have hsC : √(c ^ 2 + hc ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hC0).ne'
  have hstar : a * hb * hc + ha * b * hc + ha * hb * c = a * b * c := by
    field_simp [hsA, hsB, hsC] at hsin0
    linear_combination hsin0
  -- The tangents of the three angles.
  set p := a / ha with hp_def
  set q := b / hb with hq_def
  set r := c / hc with hr_def
  have hp : 0 < p := div_pos ha0 hha
  have hq : 0 < q := div_pos hb0 hhb
  have hr : 0 < r := div_pos hc0 hhc
  have hpqr : p + q + r = p * q * r := by
    rw [hp_def, hq_def, hr_def]
    field_simp [hha.ne', hhb.ne', hhc.ne']
    linear_combination hstar
  have h7 : r * (p * q - 1) = p + q := by linear_combination -hpqr
  have hpq1 : 1 < p * q := by
    have h8 : p * q - 1 = (p + q) / r := by
      rw [eq_div_iff hr.ne']
      linear_combination h7
    have h9 : 0 < (p + q) / r := div_pos (add_pos hp hq) hr
    linarith [h8, h9]
  have hhc_eq : hc = c * (p * q - 1) / (p + q) := by
    rw [hr_def] at h7
    have h9 : (c / hc) * (p * q - 1) * hc = (p + q) * hc := by rw [h7]
    rw [mul_comm (c / hc) _, mul_assoc, div_mul_cancel₀ c hhc.ne'] at h9
    rw [eq_div_iff (add_pos hp hq).ne', mul_comm hc (p + q)]
    linear_combination -h9
  have hha_eq : ha = a / p := by
    rw [hp_def, div_div_eq_mul_div, mul_div_cancel_left₀ ha ha0.ne']
  have hhb_eq : hb = b / q := by
    rw [hq_def, div_div_eq_mul_div, mul_div_cancel_left₀ hb hb0.ne']
  -- The adapted frame.
  have hncoll : ¬Collinear ℝ {A, B, C} := affineIndependent_iff_not_collinear_set.mp hABC
  obtain ⟨e₁, e₂, u, v, hv, he1e1, he2e2, he1e2, hBf, hCf, hcomp⟩ := exists_frame hncoll
  rw [← hc_def] at hBf
  have he2e1 : ⟪e₂, e₁⟫ = 0 := by rw [real_inner_comm]; exact he1e2
  have he1n : ‖e₁‖ = 1 := by
    have h : ‖e₁‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact he1e1
    rcases sq_eq_one_iff.mp h with h1 | h1
    · exact h1
    · have h2 := norm_nonneg e₁; linarith
  have he2n : ‖e₂‖ = 1 := by
    have h : ‖e₂‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact he2e2
    rcases sq_eq_one_iff.mp h with h1 | h1
    · exact h1
    · have h2 := norm_nonneg e₂; linarith
  -- The outward normals in the frame.
  have hgC : C - B = (u - c) • e₁ + v • e₂ := by
    have h1 : C - B = (C - A) - (B - A) := by abel
    rw [h1, hCf, hBf]; module
  have ha2 : a ^ 2 = (u - c) ^ 2 + v ^ 2 := by
    have h1 : a = ‖(u - c) • e₁ + v • e₂‖ := by rw [ha_def, hgC]
    rw [h1, pow_two ‖(u - c) • e₁ + v • e₂‖, pow_two (u - c), pow_two v,
      norm_add_sq_eq_norm_sq_add_norm_sq_real]
    · congr 1
      · rw [norm_smul, he1n, mul_one, Real.norm_eq_abs, abs_mul_abs_self]
      · rw [norm_smul, he2n, mul_one, Real.norm_eq_abs, abs_mul_abs_self]
    · rw [real_inner_smul_left, real_inner_smul_right, he1e2, mul_zero, mul_zero]
  have ha_eq : a = Real.sqrt ((u - c) ^ 2 + v ^ 2) := by
    rw [← ha2]; exact (Real.sqrt_sq ha0.le).symm
  have hna_f : na = (v / a) • e₁ + ((c - u) / a) • e₂ := by
    have hna_eq := hcomp na
    set x := ⟪na, e₁⟫ with hx_def
    set y := ⟪na, e₂⟫ with hy_def
    have hperpx : x * (u - c) + y * v = 0 := by
      have h1 := hnap
      rw [hgC, hna_eq] at h1
      simp only [inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right, he1e1, he2e2, he1e2, he2e1] at h1
      linear_combination h1
    have hunitx : x ^ 2 + y ^ 2 = 1 := by
      have h1 : ⟪na, na⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hna1]; norm_num
      rw [hna_eq] at h1
      simp only [inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right, he1e1, he2e2, he1e2, he2e1] at h1
      linear_combination h1
    have hgAB : A - B = (-c) • e₁ + (0:ℝ) • e₂ := by
      have h1 : A - B = -(B - A) := by abel
      rw [h1, hBf]; module
    have hsidex : (-c) * x + (0:ℝ) * y < 0 := by
      have h1 := hnao
      rw [hgAB, hna_eq] at h1
      simp only [inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right, he1e1, he2e2, he1e2, he2e1] at h1
      linarith [h1]
    have hwx : (-c) * v - (0:ℝ) * (u - c) < 0 := by
      have h1 := mul_pos hc0 hv; linarith [h1]
    have hgx : (u - c) ^ 2 + v ^ 2 ≠ 0 := by
      have h1 := sq_pos_of_pos hv; have h2 := sq_nonneg (u - c)
      exact ne_of_gt (by linarith)
    obtain ⟨hxr, hyr⟩ := perp_solve hgx hperpx hunitx hsidex hwx
    rw [hna_eq, hxr, hyr, ← ha_eq, neg_sub u c]
  have hgA : A - C = (-u) • e₁ + (-v) • e₂ := by
    have h1 : A - C = -(C - A) := by abel
    rw [h1, hCf]; module
  have hb2 : b ^ 2 = u ^ 2 + v ^ 2 := by
    have h1 : b = ‖(-u) • e₁ + (-v) • e₂‖ := by rw [hb_def, hgA]
    rw [h1, pow_two ‖(-u) • e₁ + (-v) • e₂‖, pow_two u, pow_two v,
      norm_add_sq_eq_norm_sq_add_norm_sq_real]
    · congr 1
      · rw [norm_smul, he1n, mul_one, Real.norm_eq_abs, abs_mul_abs_self, neg_mul_neg]
      · rw [norm_smul, he2n, mul_one, Real.norm_eq_abs, abs_mul_abs_self, neg_mul_neg]
    · rw [real_inner_smul_left, real_inner_smul_right, he1e2, mul_zero, mul_zero]
  have hb_eq : b = Real.sqrt (u ^ 2 + v ^ 2) := by
    rw [← hb2]; exact (Real.sqrt_sq hb0.le).symm
  have hnb_f : nb = (-(v / b)) • e₁ + (u / b) • e₂ := by
    have hnb_eq := hcomp nb
    set x := ⟪nb, e₁⟫ with hx_def
    set y := ⟪nb, e₂⟫ with hy_def
    have hperpx : x * (-u) + y * (-v) = 0 := by
      have h1 := hnbp
      rw [hgA, hnb_eq] at h1
      simp only [inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right, he1e1, he2e2, he1e2, he2e1] at h1
      linear_combination h1
    have hunitx : x ^ 2 + y ^ 2 = 1 := by
      have h1 : ⟪nb, nb⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hnb1]; norm_num
      rw [hnb_eq] at h1
      simp only [inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right, he1e1, he2e2, he1e2, he2e1] at h1
      linear_combination h1
    have hgBC : B - C = (c - u) • e₁ + (-v) • e₂ := by
      have h1 : B - C = (B - A) - (C - A) := by abel
      rw [h1, hBf, hCf]; module
    have hsidex : (c - u) * x + (-v) * y < 0 := by
      have h1 := hnbo
      rw [hgBC, hnb_eq] at h1
      simp only [inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right, he1e1, he2e2, he1e2, he2e1] at h1
      linarith [h1]
    have hwx : (c - u) * (-v) - (-v) * (-u) < 0 := by
      have h1 := mul_pos hc0 hv; linarith [h1]
    have hgx : (-u) ^ 2 + (-v) ^ 2 ≠ 0 := by
      have h1 := sq_pos_of_pos hv; have h2 := sq_nonneg u
      exact ne_of_gt (by linarith)
    obtain ⟨hxr, hyr⟩ := perp_solve hgx hperpx hunitx hsidex hwx
    rw [hnb_eq, hxr, hyr, neg_sq, neg_sq, ← hb_eq, neg_neg, neg_div]
  have hgc : B - A = c • e₁ + (0:ℝ) • e₂ := by
    rw [hBf]; module
  have hnc_f : nc = -e₂ := by
    have hnc_eq := hcomp nc
    set x := ⟪nc, e₁⟫ with hx_def
    set y := ⟪nc, e₂⟫ with hy_def
    have hperpx : x * c + y * (0:ℝ) = 0 := by
      have h1 := hncp
      rw [hgc, hnc_eq] at h1
      simp only [inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right, he1e1, he2e2, he1e2, he2e1] at h1
      linear_combination h1
    have hunitx : x ^ 2 + y ^ 2 = 1 := by
      have h1 : ⟪nc, nc⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hnc1]; norm_num
      rw [hnc_eq] at h1
      simp only [inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right, he1e1, he2e2, he1e2, he2e1] at h1
      linear_combination h1
    have hsidex : u * x + v * y < 0 := by
      have h1 := hnco
      rw [hCf, hnc_eq] at h1
      simp only [inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right, he1e1, he2e2, he1e2, he2e1] at h1
      linarith [h1]
    have hwx : u * (0:ℝ) - v * c < 0 := by
      have h1 := mul_pos hv hc0; linarith [h1]
    have hgx : c ^ 2 + (0:ℝ) ^ 2 ≠ 0 := by
      have h1 : c ^ 2 + (0:ℝ) ^ 2 = c ^ 2 := by ring
      rw [h1]; exact pow_ne_zero 2 hc0.ne'
    obtain ⟨hxr, hyr⟩ := perp_solve hgx hperpx hunitx hsidex hwx
    have hRc : Real.sqrt (c ^ 2 + (0:ℝ) ^ 2) = c := by
      have h1 : c ^ 2 + (0:ℝ) ^ 2 = c ^ 2 := by ring
      rw [h1, Real.sqrt_sq hc0.le]
    rw [hnc_eq, hxr, hyr, hRc, zero_div, zero_smul, zero_add, neg_div, div_self hc0.ne',
      neg_smul, one_smul]
  -- Coordinates of the six rectangle vertices in the frame.
  have hC' : C = A + u • e₁ + v • e₂ := by
    have h1 : C = A + (C - A) := by abel
    rw [h1, hCf]; abel
  have hB' : B = A + c • e₁ := by
    have h1 : B = A + (B - A) := by abel
    rw [h1, hBf]
  have havp : ha * (v / a) = v / p := by
    rw [hha_eq, div_mul_div_comm, mul_comm (p) a, mul_div_mul_left v p ha0.ne']
  have hacup : ha * ((c - u) / a) = (c - u) / p := by
    rw [hha_eq, div_mul_div_comm, mul_comm (p) a, mul_div_mul_left (c - u) p ha0.ne']
  have hbv : hb * (-(v / b)) = -(v / q) := by
    rw [hhb_eq, ← neg_div, div_mul_div_comm, mul_comm (q) b, mul_div_mul_left (-v) q hb0.ne',
      neg_div]
  have hbu : hb * (u / b) = u / q := by
    rw [hhb_eq, div_mul_div_comm, mul_comm (q) b, mul_div_mul_left u q hb0.ne']
  have hC₁f : C₁ = A + (u + v / p) • e₁ + (v + (c - u) / p) • e₂ := by
    rw [hC₁, hC', hna_f, smul_add, smul_smul, smul_smul, havp, hacup]
    module
  have hB₂f : B₂ = A + (c + v / p) • e₁ + ((c - u) / p) • e₂ := by
    rw [hB₂, hB', hna_f, smul_add, smul_smul, smul_smul, havp, hacup]
    module
  have hA₁f : A₁ = A + (-(v / q)) • e₁ + (u / q) • e₂ := by
    rw [hA₁, hnb_f, smul_add, smul_smul, smul_smul, hbv, hbu]
    module
  have hC₂f : C₂ = A + (u - v / q) • e₁ + (v + u / q) • e₂ := by
    rw [hC₂, hC', hnb_f, smul_add, smul_smul, smul_smul, hbv, hbu]
    module
  have hB₁f : B₁ = A + c • e₁ + (-(c * (p * q - 1) / (p + q))) • e₂ := by
    rw [hB₁, hB', hnc_f, smul_neg, hhc_eq]
    module
  have hA₂f : A₂ = A + (0:ℝ) • e₁ + (-(c * (p * q - 1) / (p + q))) • e₂ := by
    rw [hA₂, hnc_f, smul_neg, hhc_eq]
    module
  -- The common point, found by intersecting two of the three lines.
  set D := (c * p * q + (p + q) * v) ^ 2 + (c * q - (p + q) * u) ^ 2 with hD_def
  have hD : 0 < D := by
    rw [hD_def]
    have h1 : 0 < c * p * q + (p + q) * v := by positivity
    have h2 : 0 < (c * p * q + (p + q) * v) ^ 2 := sq_pos_of_pos h1
    have h3 : 0 ≤ (c * q - (p + q) * u) ^ 2 := sq_nonneg _
    linarith
  set px := c * (p * u + v) * (c * p * q ^ 2 - c * q + p * q * v + p * u + q ^ 2 * v +
    q * u) / D with hpx
  set py := c * (p + q) * (p * u + v) * (c * q - q * u + v) / D with hpy
  set P := A + px • e₁ + py • e₂ with hP
  have hpq0 : p + q ≠ 0 := ne_of_gt (add_pos hp hq)
  have hcross1 : (c - px) * ((v + u / q) - py) =
      (-(c * (p * q - 1) / (p + q)) - py) * ((u - v / q) - px) := by
    rw [hpx, hpy]
    field_simp [hp.ne', hq.ne', hpq0, hD.ne']
    ring
  have hcross2 : ((u + v / p) - px) * ((-(c * (p * q - 1) / (p + q))) - py) =
      ((v + (c - u) / p) - py) * ((0:ℝ) - px) := by
    rw [hpx, hpy]
    field_simp [hp.ne', hq.ne', hpq0, hD.ne']
    ring
  have hcross3 : ((-(v / q)) - px) * (((c - u) / p) - py) =
      ((u / q) - py) * ((c + v / p) - px) := by
    rw [hpx, hpy]
    field_simp [hp.ne', hq.ne', hpq0, hD.ne']
    ring
  exact ⟨P, collinear_of_frame hP hB₁f hC₂f hcross1,
    collinear_of_frame hP hC₁f hA₂f hcross2,
    collinear_of_frame hP hA₁f hB₂f hcross3⟩

end Usa2021P1
