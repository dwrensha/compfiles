/-
Copyright (c) 2025 The Compfiles Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benpigchu
-/

import Mathlib

import ProblemExtraction

problem_file {
  tags := [.Geometry]
}

/-!
# International Mathematical Olympiad 1991, Problem 5

Let ABC be a triangle and P be an interior point of ABC.
Show that at least one of the angles ∠PAB, ∠PBC, ∠PCA is
less than or equal to 30°.

-/

namespace Imo1991P5

open scoped Affine EuclideanGeometry Real

snip begin

lemma mul3_le_add3_div_three_pow_three {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    : (a * b * c) ≤ ((a + b + c) / 3) ^ 3 := by
    have h := Real.geom_mean_le_arith_mean3_weighted
      (by norm_num : (0 : ℝ) ≤ 1 / 3)
      (by norm_num : (0 : ℝ) ≤ 1 / 3)
      (by norm_num : (0 : ℝ) ≤ 1 / 3)
      ha hb hc (by norm_num)
    rw [← Real.mul_rpow ha hb, ← Real.mul_rpow (by positivity) hc] at h
    nth_rw 1 [one_div] at h
    rw [Real.rpow_inv_le_iff_of_pos (by positivity) (by positivity) (by norm_num)] at h
    rw [← mul_add, ← mul_add, div_mul_comm, mul_one, Real.rpow_ofNat] at h
    exact h

lemma map_mean3_le_mean3_map_of_concaveOn
    {s : Set ℝ} {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ s f) {a b c : ℝ}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s)
    : (f a + f b + f c) / 3 ≤ f ((a + b + c) / 3) := by
  set w := fun i : Fin 3 ↦ (1 : ℝ) / 3 with hw
  set p := ![a, b, c] with hp
  have h₀ : ∀ i ∈ Finset.univ, 0 ≤ w i := by
    intro i hi
    rw [hw]
    dsimp
    norm_num
  have h₁ : ∑ i ∈ Finset.univ, w i = 1 := by
    rw [Fin.sum_univ_three, hw]
    dsimp
    norm_num
  have hmem : ∀ i ∈ Finset.univ, p i ∈ s := by
    intro i hi
    rw [hp]
    fin_cases i <;> dsimp
    · exact ha
    · exact hb
    · exact hc
  have h := ConcaveOn.le_map_sum hf h₀ h₁ hmem
  rw [Fin.sum_univ_three, Fin.sum_univ_three, hw, hp] at h
  dsimp at h
  rw [← mul_add, ← mul_add, ← mul_add, ← mul_add, div_mul_comm, mul_one, div_mul_comm, mul_one] at h
  exact h

lemma one_div_two_lt_sin {a : ℝ}
    (ha : π / 6 < a) (ha' : a < 5 * π / 6)
    : 1 / 2 < Real.sin a := by
    rw [← Real.sin_pi_div_six]
    by_cases! h : a < π / 2
    · apply Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) ha
    · nth_rw 2 [← Real.sin_pi_sub]
      apply Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) (by linarith)

theorem analytic_version {a₁ a₂ a₃ b₁ b₂ b₃ : ℝ}
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hb₃ : 0 ≤ b₃)
    (hab : a₁ + a₂ + a₃ + b₁ + b₂ + b₃ = π)
    (h : Real.sin a₁ * Real.sin a₂ * Real.sin a₃ = Real.sin b₁ * Real.sin b₂ * Real.sin b₃)
    : a₁ ≤ π / 6 ∨ a₂ ≤ π / 6 ∨ a₃ ≤ π / 6 := by
  contrapose! h
  rcases h with ⟨ha₁', ha₂', ha₃'⟩
  apply ne_of_gt
  trans (1 / 2) ^ 3
  · have hsinb₁ := Real.sin_nonneg_of_nonneg_of_le_pi hb₁ (by linarith)
    have hsinb₂ := Real.sin_nonneg_of_nonneg_of_le_pi hb₂ (by linarith)
    have hsinb₃ := Real.sin_nonneg_of_nonneg_of_le_pi hb₃ (by linarith)
    apply lt_of_le_of_lt (mul3_le_add3_div_three_pow_three hsinb₁ hsinb₂ hsinb₃)
    rw [pow_lt_pow_iff_left₀ (by positivity) (by norm_num) (by norm_num)]
    have hb₁' : b₁ ∈ Set.Icc 0 π := by
      rw [Set.mem_Icc]
      constructor <;> linarith
    have hb₂' : b₂ ∈ Set.Icc 0 π := by
      rw [Set.mem_Icc]
      constructor <;> linarith
    have hb₃' : b₃ ∈ Set.Icc 0 π := by
      rw [Set.mem_Icc]
      constructor <;> linarith
    apply lt_of_le_of_lt (map_mean3_le_mean3_map_of_concaveOn
      strictConcaveOn_sin_Icc.concaveOn hb₁' hb₂' hb₃')
    rw [← Real.sin_pi_div_six]
    apply Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
  · rw [pow_three']
    have ha₁'' : a₁ < 5 * π / 6 := by linarith
    have ha₂'' : a₂ < 5 * π / 6 := by linarith
    have ha₃'' : a₃ < 5 * π / 6 := by linarith
    apply mul_lt_mul'' _ (one_div_two_lt_sin ha₃' ha₃'') (by norm_num) (by norm_num)
    apply mul_lt_mul'' _ (one_div_two_lt_sin ha₂' ha₂'') (by norm_num) (by norm_num)
    apply one_div_two_lt_sin ha₁' ha₁''

-- Trigonometric Form of Ceva's Theorem
theorem trigonometric_ceva
    (A B C P : EuclideanSpace ℝ (Fin 2))
    (hABC : AffineIndependent ℝ ![A, B, C])
    : Real.sin (∠ P A B) * Real.sin (∠ P B C) * Real.sin (∠ P C A)
      = Real.sin (∠ A B P) * Real.sin (∠ B C P) * Real.sin (∠ C A P) := by
  have hAneB := (hABC.injective.ne (by decide : (0 : Fin 3) ≠ 1))
  have hBneC := (hABC.injective.ne (by decide : (1 : Fin 3) ≠ 2))
  have hCneA := (hABC.injective.ne (by decide : (2 : Fin 3) ≠ 0))
  dsimp [-ne_eq] at hAneB hBneC hCneA
  by_cases! h : P = A ∨ P = B ∨ P = C
  · casesm* _ ∨ _
    · rw [h]
      rw [EuclideanGeometry.angle_self_of_ne hAneB]
      rw [EuclideanGeometry.angle_self_of_ne hCneA.symm]
      rw [Real.sin_zero]
      ring
    · rw [h]
      rw [EuclideanGeometry.angle_self_of_ne hBneC]
      rw [EuclideanGeometry.angle_self_of_ne hAneB.symm]
      simp only [Real.sin_zero, mul_zero, zero_mul]
    · rw [h]
      rw [EuclideanGeometry.angle_self_of_ne hCneA]
      rw [EuclideanGeometry.angle_self_of_ne hBneC.symm]
      simp only [Real.sin_zero, mul_zero, zero_mul]
  · rcases h with ⟨hPA, hPB, hPC⟩
    have hAB := EuclideanGeometry.law_sin A B P
    have hBC := EuclideanGeometry.law_sin B C P
    have hCA := EuclideanGeometry.law_sin C A P
    rw [dist_comm] at hAB hBC hCA
    rw [← dist_ne_zero] at hPA hPB hPC
    rw [← eq_div_iff hPB] at hAB
    rw [← eq_div_iff hPC] at hBC
    rw [← eq_div_iff hPA] at hCA
    rw [hAB, hBC, hCA]
    field

lemma angle_eq_angle_add_angle_of_mem_interior
    {A B C P : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C}))
    : ∠ A B C = ∠ A B P + ∠ P B C := by
  have htot' : affineSpan ℝ (Set.range ![A, B, C]) = ⊤ := by
    rw [AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nontrivial]
    apply AffineIndependent.vectorSpan_eq_top_of_card_eq_finrank_add_one hABC
    rw [finrank_euclideanSpace]
    simp only [Nat.succ_eq_add_one, zero_add, Nat.reduceAdd, Fintype.card_fin]
  set basis := AffineBasis.mk _ hABC htot' with h_basis
  have h_range : {A, B, C} = Set.range basis := by
    rw [h_basis, DFunLike.coe, AffineBasis.instFunLike]
    simp
    rw [Set.pair_comm, Set.insert_comm, Set.pair_comm]
  rw [h_range, AffineBasis.interior_convexHull] at hP
  dsimp at hP
  repeat rw [EuclideanGeometry.angle]
  have hA : A = basis 0 := by
    rw [h_basis, DFunLike.coe, AffineBasis.instFunLike]
    simp
  have hB : B = basis 1 := by
    rw [h_basis, DFunLike.coe, AffineBasis.instFunLike]
    simp
  have hC : C = basis 2 := by
    rw [h_basis, DFunLike.coe, AffineBasis.instFunLike]
    simp
  have hPB : P -ᵥ B ≠ 0 := by
    rw [vsub_eq_zero_iff_eq.ne]
    contrapose! hP
    use 0
    rw [hP, hB, AffineBasis.coord_apply_ne basis (by norm_num)]
  rw [InnerProductGeometry.angle_eq_angle_add_angle_iff hPB]
  right
  rw [Submodule.mem_span_pair]
  have hsum := AffineBasis.linear_combination_coord_eq_self basis P
  have hsum' := AffineBasis.sum_coord_apply_eq_one basis P
  rw [Fin.sum_univ_three] at hsum hsum'
  use ⟨(basis.coord 0) P, le_of_lt (hP 0)⟩
  use ⟨(basis.coord 2) P, le_of_lt (hP 2)⟩
  rw [NNReal.smul_def, NNReal.smul_def, NNReal.toReal, Subtype.val, Subtype.val]
  dsimp
  nth_rw 3 [← hsum]
  rw [smul_sub, smul_sub]
  rw [← hA, ← hB, ← hC, ← sub_eq_zero]
  abel_nf
  rw [← add_assoc, ← add_assoc]
  rw [← smul_add, ← smul_add, ← add_smul, ← add_smul, add_right_comm]
  rw [hsum', one_smul, neg_smul, one_smul, neg_add_cancel]

lemma affineIndependent_rotate {A B C : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C])
    : AffineIndependent ℝ ![B, C, A] := by
  rw [affineIndependent_iff_not_collinear_set] at hABC ⊢
  rw [Set.pair_comm, Set.insert_comm]
  exact hABC

lemma sum_angle {A B C P : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C}))
    : ∠ P A B + ∠ P B C + ∠ P C A + ∠ A B P + ∠ B C P + ∠ C A P = π := by
  rw [← EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    C (hABC.injective.ne (by decide : (1 : Fin 3) ≠ 0))]
  dsimp
  rw [angle_eq_angle_add_angle_of_mem_interior hABC hP]
  apply affineIndependent_rotate at hABC
  rw [Set.insert_comm, Set.pair_comm] at hP
  rw [angle_eq_angle_add_angle_of_mem_interior hABC hP]
  apply affineIndependent_rotate at hABC
  rw [Set.insert_comm, Set.pair_comm] at hP
  rw [angle_eq_angle_add_angle_of_mem_interior hABC hP]
  ring

snip end

problem imo1991_p5
    (A B C P : EuclideanSpace ℝ (Fin 2))
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C})) :
    ∠ P A B ≤ π / 6 ∨ ∠ P B C ≤ π / 6 ∨ ∠ P C A ≤ π / 6 := by
  have hsum := sum_angle hABC hP
  have hsin := trigonometric_ceva A B C P hABC
  apply analytic_version
    (EuclideanGeometry.angle_nonneg _ _ _)
    (EuclideanGeometry.angle_nonneg _ _ _)
    (EuclideanGeometry.angle_nonneg _ _ _)
    hsum hsin

end Imo1991P5
