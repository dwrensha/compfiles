/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Kimi K3
-/

module

public import Mathlib.Analysis.Normed.Affine.Simplex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Geometry.Euclidean.Circumcenter
public import ProblemExtraction

@[expose] public section

-- This file's proofs are memory-bound: asynchronous elaboration retains per-tactic
-- snapshots whose peak exceeds 4 GiB. Elaborating synchronously lowers peak RSS
-- at the cost of some wall-clock time.
set_option Elab.async false

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

problem_file {
  tags := [.Geometry]
  problemImportedFrom :=
    "https://github.com/jsm28/IMOLean/blob/main/IMO/IMO2023P6.lean"
}

/-!
# International Mathematical Olympiad 2023, Problem 6

Let ABC be an equilateral triangle. Let A₁,B₁,C₁ be interior points of
ABC such that BA₁=A₁C, CB₁ = B₁A, AC₁=C₁B, and

      ∠BA₁C + ∠CB₁A + ∠C₁B = 480°.

Let BC₁ and CB₁ meet at A₂, let CA₁ and AC₁ meet at B₂, and let AB₁ and
BA₁ meet at $C₂.

Prove that if triangle A₁B₁C₁ is scalene, then the three circumcircles
of triangles AA₁A₂, BB₁B₂ and CC₁C₂ all pass through two common points.
-/

open scoped Cardinal EuclideanGeometry Real InnerProductSpace
open Affine Module

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

namespace Imo2023P6

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P] [Fact (finrank ℝ V = 2)]

snip begin

/-- Squared distance between two points given by coordinates in an
orthonormal pair. -/
lemma coord_dist_sq {O : P} {e₁ e₂ : V} (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1)
    (h₁₂ : ⟪e₁, e₂⟫_ℝ = 0) (a b c d : ℝ) :
    dist ((a • e₁ + b • e₂) +ᵥ O) ((c • e₁ + d • e₂) +ᵥ O) ^ 2
      = (a - c) ^ 2 + (b - d) ^ 2 := by
  have hv : ((a • e₁ + b • e₂) +ᵥ O) -ᵥ ((c • e₁ + d • e₂) +ᵥ O)
      = (a - c) • e₁ + (b - d) • e₂ := by
    rw [vadd_vsub_vadd_cancel_right]
    module
  rw [dist_eq_norm_vsub V, hv, norm_add_sq_real, inner_smul_left, inner_smul_right, h₁₂]
  simp only [mul_zero, add_zero]
  rw [norm_smul, norm_smul, h₁, h₂, mul_one, mul_one, Real.norm_eq_abs, Real.norm_eq_abs,
    sq_abs, sq_abs]

/-- The equilateral triangle frame: circumcenter, circumradius, and an adapted
orthonormal pair with explicit coordinates for A, B, C. -/
lemma frame_lemma {A B C : P}
    (hAI : AffineIndependent ℝ ![A, B, C])
    (hEq : (⟨_, hAI⟩ : Triangle ℝ P).Equilateral) :
    ∃ (O : P) (R : ℝ) (e₁ e₂ : V),
      0 < R ∧ ‖e₁‖ = 1 ∧ ‖e₂‖ = 1 ∧ ⟪e₁, e₂⟫_ℝ = 0 ∧
      A = (R • e₁) +ᵥ O ∧
      B = ((-R / 2) • e₁ + (R * Real.sqrt 3 / 2) • e₂) +ᵥ O ∧
      C = ((-R / 2) • e₁ + (-R * Real.sqrt 3 / 2) • e₂) +ᵥ O := by
  have : FiniteDimensional ℝ V := .of_fact_finrank_eq_two
  set T : Triangle ℝ P := ⟨_, hAI⟩
  set O := T.circumcenter
  set R := T.circumradius
  have hR : 0 < R := T.circumradius_pos
  have hdA : dist A O = R := T.dist_circumcenter_eq_circumradius 0
  have hdB : dist B O = R := T.dist_circumcenter_eq_circumradius 1
  have hdC : dist C O = R := T.dist_circumcenter_eq_circumradius 2
  have hAB_AC : dist A B = dist A C :=
    ((Triangle.equilateral_iff_dist_01_eq_02_and_dist_01_eq_12 (t := T)).mp hEq).1
  have hAB_BC : dist A B = dist B C :=
    ((Triangle.equilateral_iff_dist_01_eq_02_and_dist_01_eq_12 (t := T)).mp hEq).2
  have hnba : ‖B -ᵥ A‖ = dist A B := (dist_eq_norm_vsub V B A).symm.trans (dist_comm B A)
  have hnca : ‖C -ᵥ A‖ = dist A C := (dist_eq_norm_vsub V C A).symm.trans (dist_comm C A)
  have hinner_BACA : ⟪B -ᵥ A, C -ᵥ A⟫_ℝ = (dist A B) ^ 2 / 2 := by
    have h1 : dist B C ^ 2 = ‖B -ᵥ A‖ ^ 2 - 2 * ⟪B -ᵥ A, C -ᵥ A⟫_ℝ + ‖C -ᵥ A‖ ^ 2 := by
      rw [dist_eq_norm_vsub V B C, ← vsub_sub_vsub_cancel_right B C A, norm_sub_sq_real]
    rw [← hAB_BC, hnba, hnca, ← hAB_AC] at h1
    linarith
  set G := ((1 / 3 : ℝ) • ((B -ᵥ A) + (C -ᵥ A))) +ᵥ A
  have hGA : G -ᵥ A = (1 / 3 : ℝ) • ((B -ᵥ A) + (C -ᵥ A)) := vadd_vsub _ _
  have hGA_sq : ‖G -ᵥ A‖ ^ 2 = (dist A B) ^ 2 / 3 := by
    rw [hGA, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, norm_add_sq_real, hnba, hnca,
      hinner_BACA, ← hAB_AC]
    ring
  have hinner_GA_BA : ⟪G -ᵥ A, B -ᵥ A⟫_ℝ = (dist A B) ^ 2 / 2 := by
    rw [hGA, real_inner_smul_left, inner_add_left, real_inner_self_eq_norm_sq, hnba,
      real_inner_comm (B -ᵥ A) (C -ᵥ A), hinner_BACA]
    ring
  have hinner_GA_CA : ⟪G -ᵥ A, C -ᵥ A⟫_ℝ = (dist A B) ^ 2 / 2 := by
    rw [hGA, real_inner_smul_left, inner_add_left, hinner_BACA, real_inner_self_eq_norm_sq,
      hnca, ← hAB_AC]
    ring
  have hGB : G -ᵥ B = (G -ᵥ A) - (B -ᵥ A) := (vsub_sub_vsub_cancel_right G B A).symm
  have hGB_sq : ‖G -ᵥ B‖ ^ 2 = (dist A B) ^ 2 / 3 := by
    rw [hGB, norm_sub_sq_real, hGA_sq, hinner_GA_BA, hnba]
    ring
  have hGC : G -ᵥ C = (G -ᵥ A) - (C -ᵥ A) := (vsub_sub_vsub_cancel_right G C A).symm
  have hGC_sq : ‖G -ᵥ C‖ ^ 2 = (dist A B) ^ 2 / 3 := by
    rw [hGC, norm_sub_sq_real, hGA_sq, hinner_GA_CA, hnca, ← hAB_AC]
    ring
  have hr0nonneg : 0 ≤ dist A B * Real.sqrt 3 / 3 :=
    div_nonneg (mul_nonneg dist_nonneg (Real.sqrt_nonneg 3)) (by norm_num)
  have hr0_sq : (dist A B * Real.sqrt 3 / 3) ^ 2 = (dist A B) ^ 2 / 3 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    ring
  have hdGA : dist G A = dist A B * Real.sqrt 3 / 3 := by
    have h1 : dist G A ^ 2 = (dist A B * Real.sqrt 3 / 3) ^ 2 := by
      rw [dist_eq_norm_vsub V G A, hGA_sq, hr0_sq]
    exact (sq_eq_sq₀ dist_nonneg hr0nonneg).mp h1
  have hdGB : dist G B = dist A B * Real.sqrt 3 / 3 := by
    have h1 : dist G B ^ 2 = (dist A B * Real.sqrt 3 / 3) ^ 2 := by
      rw [dist_eq_norm_vsub V G B, hGB_sq, hr0_sq]
    exact (sq_eq_sq₀ dist_nonneg hr0nonneg).mp h1
  have hdGC : dist G C = dist A B * Real.sqrt 3 / 3 := by
    have h1 : dist G C ^ 2 = (dist A B * Real.sqrt 3 / 3) ^ 2 := by
      rw [dist_eq_norm_vsub V G C, hGC_sq, hr0_sq]
    exact (sq_eq_sq₀ dist_nonneg hr0nonneg).mp h1
  have hspan : affineSpan ℝ (Set.range T.points) = ⊤ := by
    rw [show (T.points : Fin 3 → P) = ![A, B, C] from rfl,
      AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one hAI, Fintype.card_fin,
      (Fact.out : finrank ℝ V = 2)]
  have hmem : G ∈ affineSpan ℝ (Set.range T.points) := by
    rw [hspan]
    exact AffineSubspace.mem_top ℝ V G
  have hr : ∀ i, dist (T.points i) G = dist A B * Real.sqrt 3 / 3 := by
    intro i
    fin_cases i
    · rw [dist_comm]
      exact hdGA
    · rw [dist_comm]
      exact hdGB
    · rw [dist_comm]
      exact hdGC
  have hGO : G = O := T.eq_circumcenter_of_dist_eq hmem hr
  have hRR : dist A B * Real.sqrt 3 / 3 = R := T.eq_circumradius_of_dist_eq hmem hr
  have hdistAB2 : dist A B ^ 2 = 3 * R ^ 2 := by
    have h2 : (dist A B * Real.sqrt 3 / 3) ^ 2 = R ^ 2 := by rw [hRR]
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)] at h2
    linarith
  set e₁ : V := R⁻¹ • (A -ᵥ O) with he₁def
  have hAO : ‖A -ᵥ O‖ = R := by rw [← dist_eq_norm_vsub V A O, hdA]
  have hAO_sq : ‖A -ᵥ O‖ ^ 2 = R ^ 2 := by rw [hAO]
  have hBO : ‖B -ᵥ O‖ = R := by rw [← dist_eq_norm_vsub V B O, hdB]
  have hBO_sq : ‖B -ᵥ O‖ ^ 2 = R ^ 2 := by rw [hBO]
  have he₁ : ‖e₁‖ = 1 := by
    rw [he₁def, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR), hAO,
      inv_mul_cancel₀ hR.ne']
  have hinner : ⟪A -ᵥ O, B -ᵥ O⟫_ℝ = -R ^ 2 / 2 := by
    have h1 : dist A B ^ 2 = ‖A -ᵥ O‖ ^ 2 - 2 * ⟪A -ᵥ O, B -ᵥ O⟫_ℝ + ‖B -ᵥ O‖ ^ 2 := by
      rw [dist_eq_norm_vsub V A B, ← vsub_sub_vsub_cancel_right A B O, norm_sub_sq_real]
    rw [hdistAB2, hAO_sq, hBO_sq] at h1
    linarith
  have hBe1 : ⟪B -ᵥ O, e₁⟫_ℝ = -R / 2 := by
    have hR0 : R ≠ 0 := hR.ne'
    rw [he₁def, real_inner_smul_right, real_inner_comm (A -ᵥ O) (B -ᵥ O), hinner]
    field_simp
  set e₂ : V := (R * Real.sqrt 3 / 2)⁻¹ • ((B -ᵥ O) + (R / 2) • e₁) with he₂def
  have hRsqrt : 0 < R * Real.sqrt 3 / 2 :=
    div_pos (mul_pos hR (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 3))) (by norm_num)
  have hnormv2_sq : ‖(B -ᵥ O) + (R / 2) • e₁‖ ^ 2 = 3 * R ^ 2 / 4 := by
    rw [norm_add_sq_real, real_inner_smul_right, hBe1, norm_smul, he₁, mul_one,
      Real.norm_eq_abs, sq_abs, hBO_sq]
    ring
  have hr02 : (R * Real.sqrt 3 / 2) ^ 2 = 3 * R ^ 2 / 4 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    ring
  have hnormv2 : ‖(B -ᵥ O) + (R / 2) • e₁‖ = R * Real.sqrt 3 / 2 :=
    (sq_eq_sq₀ (norm_nonneg _) hRsqrt.le).mp (by rw [hnormv2_sq, hr02])
  have he₂ : ‖e₂‖ = 1 := by
    rw [he₂def, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hRsqrt), hnormv2,
      inv_mul_cancel₀ hRsqrt.ne']
  have he₁₂ : ⟪e₁, e₂⟫_ℝ = 0 := by
    rw [he₂def, real_inner_smul_right, inner_add_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, he₁, real_inner_comm (B -ᵥ O) e₁, hBe1]
    ring
  have hRe1 : R • e₁ = A -ᵥ O := by rw [he₁def, smul_inv_smul₀ hR.ne']
  have hA : A = (R • e₁) +ᵥ O := by rw [hRe1, vsub_vadd]
  have hB2 : (R * Real.sqrt 3 / 2) • e₂ = (B -ᵥ O) + (R / 2) • e₁ := by
    rw [he₂def, smul_inv_smul₀ hRsqrt.ne']
  have hB : B = ((-R / 2) • e₁ + (R * Real.sqrt 3 / 2) • e₂) +ᵥ O := by
    have hstep : (-R / 2) • e₁ + ((B -ᵥ O) + (R / 2) • e₁) = B -ᵥ O := by module
    rw [hB2, hstep, vsub_vadd]
  have hsum : (A -ᵥ O) + (B -ᵥ O) + (C -ᵥ O) = 0 := by
    rw [← hGO, ← neg_vsub_eq_vsub_rev G A, ← neg_vsub_eq_vsub_rev G B,
      ← neg_vsub_eq_vsub_rev G C, hGB, hGC, hGA]
    module
  have hCvec : C -ᵥ O = -(A -ᵥ O) - (B -ᵥ O) := by
    have h : (A -ᵥ O) + (B -ᵥ O) + (C -ᵥ O) + (-(A -ᵥ O) - (B -ᵥ O)) = C -ᵥ O := by module
    rw [hsum, zero_add] at h
    exact h.symm
  have hC : C = ((-R / 2) • e₁ + (-R * Real.sqrt 3 / 2) • e₂) +ᵥ O := by
    have hstep : (-R / 2) • e₁ + (-R * Real.sqrt 3 / 2) • e₂ = C -ᵥ O := by
      have h1 : (-R * Real.sqrt 3 / 2 : ℝ) = -(R * Real.sqrt 3 / 2) := by ring
      rw [h1, neg_smul, hB2, hCvec, ← hRe1]
      module
    rw [hstep, vsub_vadd]
  exact ⟨O, R, e₁, e₂, hR, he₁, he₂, he₁₂, hA, hB, hC⟩

/-- A point of the interior of the equilateral triangle that is equidistant from
B and C lies on the median from A, with coordinate parameter in (0,3). -/
lemma median_coord_A {A B C X : P}
    (hAI : AffineIndependent ℝ ![A, B, C])
    (hX : X ∈ (⟨_, hAI⟩ : Triangle ℝ P).interior)
    (hd : dist B X = dist X C)
    {O : P} {R : ℝ} {e₁ e₂ : V}
    (hR : 0 < R) (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1) (he₁₂ : ⟪e₁, e₂⟫_ℝ = 0)
    (hA : A = (R • e₁) +ᵥ O)
    (hB : B = ((-R / 2) • e₁ + (R * Real.sqrt 3 / 2) • e₂) +ᵥ O)
    (hC : C = ((-R / 2) • e₁ + (-R * Real.sqrt 3 / 2) • e₂) +ᵥ O) :
    ∃ u : ℝ, 0 < u ∧ u < 3 ∧ X = ((R * (u - 1) / 2) • e₁) +ᵥ O := by
  have hs3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  simp only [Affine.Simplex.interior, Affine.Simplex.setInterior, Set.mem_setOf_eq] at hX
  obtain ⟨w, hsum, hwI, hcomb⟩ := hX
  have h2 := Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
    (s := Finset.univ) w ![A, B, C] (by simpa using hsum) O
  rw [h2] at hcomb
  have hXO : X -ᵥ O = w 0 • (A -ᵥ O) + w 1 • (B -ᵥ O) + w 2 • (C -ᵥ O) := by
    rw [← hcomb, vadd_vsub]
    simp [Fin.sum_univ_three]
  have hAv : A -ᵥ O = R • e₁ := by rw [hA, vadd_vsub]
  have hBv : B -ᵥ O = (-R / 2) • e₁ + (R * Real.sqrt 3 / 2) • e₂ := by rw [hB, vadd_vsub]
  have hCv : C -ᵥ O = (-R / 2) • e₁ + (-R * Real.sqrt 3 / 2) • e₂ := by rw [hC, vadd_vsub]
  rw [hAv, hBv, hCv] at hXO
  set X₁ : ℝ := R * (w 0 - (w 1 + w 2) / 2) with hX₁
  set X₂ : ℝ := R * Real.sqrt 3 / 2 * (w 1 - w 2) with hX₂
  have hXv : X -ᵥ O = X₁ • e₁ + X₂ • e₂ := by
    rw [hXO, hX₁, hX₂]
    module
  have hXp : X = (X₁ • e₁ + X₂ • e₂) +ᵥ O := by rw [← hXv, vsub_vadd]
  have hdsq : dist B X ^ 2 = dist X C ^ 2 := congrArg (· ^ 2) hd
  rw [hB, hXp, hC, coord_dist_sq he₁ he₂ he₁₂, coord_dist_sq he₁ he₂ he₁₂] at hdsq
  have hlin : X₂ * (2 * (R * Real.sqrt 3)) = 0 := by linear_combination -hdsq
  have hX2 : X₂ = 0 :=
    (mul_eq_zero.mp hlin).resolve_right
      (mul_ne_zero (by norm_num) (mul_ne_zero hR.ne' hs3.ne'))
  have hsum3 : w 0 + w 1 + w 2 = 1 := by
    rw [Fin.sum_univ_three] at hsum
    exact hsum
  obtain ⟨h0l, h0u⟩ := Set.mem_Ioo.mp (hwI 0)
  refine ⟨3 * w 0, by linarith, by linarith, ?_⟩
  have e1 : X₁ = R * (3 * w 0 - 1) / 2 := by
    rw [hX₁]
    linear_combination (-(R / 2)) * hsum3
  rw [hXp, hX2, zero_smul, add_zero, e1]

/-- Same for the median from B (equidistant from C and A). -/
lemma median_coord_B {A B C X : P}
    (hAI : AffineIndependent ℝ ![A, B, C])
    (hX : X ∈ (⟨_, hAI⟩ : Triangle ℝ P).interior)
    (hd : dist C X = dist X A)
    {O : P} {R : ℝ} {e₁ e₂ : V}
    (hR : 0 < R) (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1) (he₁₂ : ⟪e₁, e₂⟫_ℝ = 0)
    (hA : A = (R • e₁) +ᵥ O)
    (hB : B = ((-R / 2) • e₁ + (R * Real.sqrt 3 / 2) • e₂) +ᵥ O)
    (hC : C = ((-R / 2) • e₁ + (-R * Real.sqrt 3 / 2) • e₂) +ᵥ O) :
    ∃ v : ℝ, 0 < v ∧ v < 3 ∧ X = ((R * (1 - v) / 4) • e₁ +
      (R * Real.sqrt 3 * (v - 1) / 4) • e₂) +ᵥ O := by
  have hs3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsq3 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [Affine.Simplex.interior, Affine.Simplex.setInterior, Set.mem_setOf_eq] at hX
  obtain ⟨w, hsum, hwI, hcomb⟩ := hX
  have h2 := Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
    (s := Finset.univ) w ![A, B, C] (by simpa using hsum) O
  rw [h2] at hcomb
  have hXO : X -ᵥ O = w 0 • (A -ᵥ O) + w 1 • (B -ᵥ O) + w 2 • (C -ᵥ O) := by
    rw [← hcomb, vadd_vsub]
    simp [Fin.sum_univ_three]
  have hAv : A -ᵥ O = R • e₁ := by rw [hA, vadd_vsub]
  have hBv : B -ᵥ O = (-R / 2) • e₁ + (R * Real.sqrt 3 / 2) • e₂ := by rw [hB, vadd_vsub]
  have hCv : C -ᵥ O = (-R / 2) • e₁ + (-R * Real.sqrt 3 / 2) • e₂ := by rw [hC, vadd_vsub]
  rw [hAv, hBv, hCv] at hXO
  set X₁ : ℝ := R * (w 0 - (w 1 + w 2) / 2) with hX₁
  set X₂ : ℝ := R * Real.sqrt 3 / 2 * (w 1 - w 2) with hX₂
  have hXv : X -ᵥ O = X₁ • e₁ + X₂ • e₂ := by
    rw [hXO, hX₁, hX₂]
    module
  have hXp : X = (X₁ • e₁ + X₂ • e₂) +ᵥ O := by rw [← hXv, vsub_vadd]
  have hA' : A = ((R : ℝ) • e₁ + (0 : ℝ) • e₂) +ᵥ O := by rw [hA, zero_smul, add_zero]
  have hdsq : dist C X ^ 2 = dist X A ^ 2 := congrArg (· ^ 2) hd
  rw [hC, hXp, hA', coord_dist_sq he₁ he₂ he₁₂, coord_dist_sq he₁ he₂ he₁₂] at hdsq
  have hlin : 3 * R * X₁ + R * Real.sqrt 3 * X₂ = 0 := by
    linear_combination hdsq - (R ^ 2 / 4) * hsq3
  have hlin2 : 3 * X₁ + Real.sqrt 3 * X₂ = 0 := by
    have h0 : R * (3 * X₁ + Real.sqrt 3 * X₂) = 0 := by linear_combination hlin
    exact (mul_eq_zero.mp h0).resolve_left hR.ne'
  have hww : w 0 = w 2 := by
    rw [hX₁, hX₂] at hlin2
    have h3 : 3 * R * (w 0 - w 2) = 0 := by
      linear_combination hlin2 - (R * (w 1 - w 2) / 2) * hsq3
    have hz := (mul_eq_zero.mp h3).resolve_left (mul_ne_zero (by norm_num) hR.ne')
    linarith
  have hsum3 : w 0 + w 1 + w 2 = 1 := by
    rw [Fin.sum_univ_three] at hsum
    exact hsum
  obtain ⟨h1l, h1u⟩ := Set.mem_Ioo.mp (hwI 1)
  refine ⟨3 * w 1, by linarith, by linarith, ?_⟩
  have e1 : X₁ = R * (1 - 3 * w 1) / 4 := by
    rw [hX₁]
    linear_combination (R / 4) * hsum3 + (3 * R / 4) * hww
  have e2 : X₂ = R * Real.sqrt 3 * (3 * w 1 - 1) / 4 := by
    rw [hX₂]
    linear_combination (-(R * Real.sqrt 3 / 4)) * hsum3 + (R * Real.sqrt 3 / 4) * hww
  rw [hXp, e1, e2]

/-- Same for the median from C (equidistant from A and B). -/
lemma median_coord_C {A B C X : P}
    (hAI : AffineIndependent ℝ ![A, B, C])
    (hX : X ∈ (⟨_, hAI⟩ : Triangle ℝ P).interior)
    (hd : dist A X = dist X B)
    {O : P} {R : ℝ} {e₁ e₂ : V}
    (hR : 0 < R) (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1) (he₁₂ : ⟪e₁, e₂⟫_ℝ = 0)
    (hA : A = (R • e₁) +ᵥ O)
    (hB : B = ((-R / 2) • e₁ + (R * Real.sqrt 3 / 2) • e₂) +ᵥ O)
    (hC : C = ((-R / 2) • e₁ + (-R * Real.sqrt 3 / 2) • e₂) +ᵥ O) :
    ∃ w : ℝ, 0 < w ∧ w < 3 ∧ X = ((R * (1 - w) / 4) • e₁ +
      (R * Real.sqrt 3 * (1 - w) / 4) • e₂) +ᵥ O := by
  have hs3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsq3 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [Affine.Simplex.interior, Affine.Simplex.setInterior, Set.mem_setOf_eq] at hX
  obtain ⟨w, hsum, hwI, hcomb⟩ := hX
  have h2 := Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
    (s := Finset.univ) w ![A, B, C] (by simpa using hsum) O
  rw [h2] at hcomb
  have hXO : X -ᵥ O = w 0 • (A -ᵥ O) + w 1 • (B -ᵥ O) + w 2 • (C -ᵥ O) := by
    rw [← hcomb, vadd_vsub]
    simp [Fin.sum_univ_three]
  have hAv : A -ᵥ O = R • e₁ := by rw [hA, vadd_vsub]
  have hBv : B -ᵥ O = (-R / 2) • e₁ + (R * Real.sqrt 3 / 2) • e₂ := by rw [hB, vadd_vsub]
  have hCv : C -ᵥ O = (-R / 2) • e₁ + (-R * Real.sqrt 3 / 2) • e₂ := by rw [hC, vadd_vsub]
  rw [hAv, hBv, hCv] at hXO
  set X₁ : ℝ := R * (w 0 - (w 1 + w 2) / 2) with hX₁
  set X₂ : ℝ := R * Real.sqrt 3 / 2 * (w 1 - w 2) with hX₂
  have hXv : X -ᵥ O = X₁ • e₁ + X₂ • e₂ := by
    rw [hXO, hX₁, hX₂]
    module
  have hXp : X = (X₁ • e₁ + X₂ • e₂) +ᵥ O := by rw [← hXv, vsub_vadd]
  have hA' : A = ((R : ℝ) • e₁ + (0 : ℝ) • e₂) +ᵥ O := by rw [hA, zero_smul, add_zero]
  have hdsq : dist A X ^ 2 = dist X B ^ 2 := congrArg (· ^ 2) hd
  rw [hA', hXp, hB, coord_dist_sq he₁ he₂ he₁₂, coord_dist_sq he₁ he₂ he₁₂] at hdsq
  have hlin : 3 * R * X₁ - R * Real.sqrt 3 * X₂ = 0 := by
    linear_combination -hdsq - (R ^ 2 / 4) * hsq3
  have hlin2 : 3 * X₁ - Real.sqrt 3 * X₂ = 0 := by
    have h0 : R * (3 * X₁ - Real.sqrt 3 * X₂) = 0 := by linear_combination hlin
    exact (mul_eq_zero.mp h0).resolve_left hR.ne'
  have hww : w 0 = w 1 := by
    rw [hX₁, hX₂] at hlin2
    have h3 : 3 * R * (w 0 - w 1) = 0 := by
      linear_combination hlin2 + (R * (w 1 - w 2) / 2) * hsq3
    have hz := (mul_eq_zero.mp h3).resolve_left (mul_ne_zero (by norm_num) hR.ne')
    linarith
  have hsum3 : w 0 + w 1 + w 2 = 1 := by
    rw [Fin.sum_univ_three] at hsum
    exact hsum
  obtain ⟨h2l, h2u⟩ := Set.mem_Ioo.mp (hwI 2)
  refine ⟨3 * w 2, by linarith, by linarith, ?_⟩
  have e1 : X₁ = R * (1 - 3 * w 2) / 4 := by
    rw [hX₁]
    linear_combination (R / 4) * hsum3 + (3 * R / 4) * hww
  have e2 : X₂ = R * Real.sqrt 3 * (1 - 3 * w 2) / 4 := by
    rw [hX₂]
    linear_combination (R * Real.sqrt 3 / 4) * hsum3 - (R * Real.sqrt 3 / 4) * hww
  rw [hXp, e1, e2]

/-- The angle subtended at a median point of parameter u. -/
lemma angle_at_median_A {A B C X : P} {O : P} {R u : ℝ} {e₁ e₂ : V}
    (hR : 0 < R) (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1) (he₁₂ : ⟪e₁, e₂⟫_ℝ = 0)
    (hu0 : 0 < u) (hu3 : u < 3)
    (hB : B = ((-R / 2) • e₁ + (R * Real.sqrt 3 / 2) • e₂) +ᵥ O)
    (hC : C = ((-R / 2) • e₁ + (-R * Real.sqrt 3 / 2) • e₂) +ᵥ O)
    (hX : X = ((R * (u - 1) / 2) • e₁) +ᵥ O) :
    ∠ B X C = π - 2 * Real.arctan (u / Real.sqrt 3) := by
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hspos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hcoord : ∀ a b c d : ℝ, ⟪a • e₁ + b • e₂, c • e₁ + d • e₂⟫_ℝ = a * c + b * d := by
    intro a b c d
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      he₁₂, real_inner_comm e₁ e₂, real_inner_self_eq_norm_sq, he₁, he₂]
    ring
  have hx : B -ᵥ X = (-R * u / 2) • e₁ + (R * Real.sqrt 3 / 2) • e₂ := by
    rw [hB, hX, vadd_vsub_vadd_cancel_right]
    module
  have hy : C -ᵥ X = (-R * u / 2) • e₁ + (-R * Real.sqrt 3 / 2) • e₂ := by
    rw [hC, hX, vadd_vsub_vadd_cancel_right]
    module
  have hinner : ⟪B -ᵥ X, C -ᵥ X⟫_ℝ = R ^ 2 / 4 * (u ^ 2 - 3) := by
    rw [hx, hy, hcoord]
    linear_combination (-R ^ 2 / 4) * hs3
  have hnx : ‖B -ᵥ X‖ ^ 2 = R ^ 2 / 4 * (u ^ 2 + 3) := by
    rw [← real_inner_self_eq_norm_sq, hx, hcoord]
    linear_combination (R ^ 2 / 4) * hs3
  have hny : ‖C -ᵥ X‖ ^ 2 = R ^ 2 / 4 * (u ^ 2 + 3) := by
    rw [← real_inner_self_eq_norm_sq, hy, hcoord]
    linear_combination (R ^ 2 / 4) * hs3
  have hnx' : ‖B -ᵥ X‖ = Real.sqrt (R ^ 2 / 4 * (u ^ 2 + 3)) := by
    rw [← hnx]
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  have hny' : ‖C -ᵥ X‖ = Real.sqrt (R ^ 2 / 4 * (u ^ 2 + 3)) := by
    rw [← hny]
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  have hprod : ‖B -ᵥ X‖ * ‖C -ᵥ X‖ = R ^ 2 / 4 * (u ^ 2 + 3) := by
    rw [hnx', hny',
      ← Real.sqrt_mul (show (0 : ℝ) ≤ R ^ 2 / 4 * (u ^ 2 + 3) by positivity)
        (R ^ 2 / 4 * (u ^ 2 + 3))]
    exact Real.sqrt_mul_self (show (0 : ℝ) ≤ R ^ 2 / 4 * (u ^ 2 + 3) by positivity)
  have hcos : Real.cos (∠ B X C) = (u ^ 2 - 3) / (u ^ 2 + 3) := by
    unfold EuclideanGeometry.angle
    rw [InnerProductGeometry.cos_angle, hinner, hprod]
    have hne : R ^ 2 / 4 * (u ^ 2 + 3) ≠ 0 := by positivity
    have hne2 : u ^ 2 + 3 ≠ 0 := by positivity
    field_simp
  have hcostr : Real.cos (π - 2 * Real.arctan (u / Real.sqrt 3))
      = (u ^ 2 - 3) / (u ^ 2 + 3) := by
    have hs : (u / Real.sqrt 3) ^ 2 = u ^ 2 / 3 := by
      rw [div_pow, hs3]
    rw [Real.cos_pi_sub, Real.cos_two_mul, Real.cos_arctan, div_pow, one_pow,
      Real.sq_sqrt (show (0 : ℝ) ≤ 1 + (u / Real.sqrt 3) ^ 2 by positivity), hs]
    have hne1 : (1 : ℝ) + u ^ 2 / 3 ≠ 0 := by positivity
    have hne2 : u ^ 2 + 3 ≠ 0 := by positivity
    field_simp
    ring
  have harctan_pos : 0 < Real.arctan (u / Real.sqrt 3) :=
    Real.arctan_pos.2 (div_pos hu0 hspos)
  have harctan_lt : Real.arctan (u / Real.sqrt 3) < π / 3 := by
    have h1 : Real.arctan (Real.sqrt 3) = π / 3 := by
      rw [← Real.tan_pi_div_three]
      exact Real.arctan_tan (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    have h2 : u / Real.sqrt 3 < Real.sqrt 3 := by
      have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
      rw [div_lt_iff₀ hspos]
      linarith
    rw [← h1]
    exact Real.arctan_strictMono h2
  have hθmem : π - 2 * Real.arctan (u / Real.sqrt 3) ∈ Set.Icc 0 π :=
    ⟨by linarith [harctan_lt, Real.pi_pos], by linarith [harctan_pos]⟩
  have hangmem : ∠ B X C ∈ Set.Icc 0 π := by
    unfold EuclideanGeometry.angle
    exact ⟨InnerProductGeometry.angle_nonneg _ _, InnerProductGeometry.angle_le_pi _ _⟩
  exact Real.injOn_cos hangmem hθmem (hcos.trans hcostr.symm)

/-- The angle subtended at the B-median point of parameter v. -/
lemma angle_at_median_B {A B C X : P} {O : P} {R v : ℝ} {e₁ e₂ : V}
    (hR : 0 < R) (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1) (he₁₂ : ⟪e₁, e₂⟫_ℝ = 0)
    (hv0 : 0 < v) (hv3 : v < 3)
    (hA : A = (R • e₁) +ᵥ O)
    (hB : B = ((-R / 2) • e₁ + (R * Real.sqrt 3 / 2) • e₂) +ᵥ O)
    (hC : C = ((-R / 2) • e₁ + (-R * Real.sqrt 3 / 2) • e₂) +ᵥ O)
    (hX : X = ((R * (1 - v) / 4) • e₁ + (R * Real.sqrt 3 * (v - 1) / 4) • e₂) +ᵥ O) :
    ∠ C X A = π - 2 * Real.arctan (v / Real.sqrt 3) := by
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hspos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hcoord : ∀ a b c d : ℝ, ⟪a • e₁ + b • e₂, c • e₁ + d • e₂⟫_ℝ = a * c + b * d := by
    intro a b c d
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      he₁₂, real_inner_comm e₁ e₂, real_inner_self_eq_norm_sq, he₁, he₂]
    ring
  have hx : C -ᵥ X = (R * (v - 3) / 4) • e₁ + (-R * Real.sqrt 3 * (v + 1) / 4) • e₂ := by
    rw [hC, hX, vadd_vsub_vadd_cancel_right]
    module
  have hy : A -ᵥ X = (R * (v + 3) / 4) • e₁ + (R * Real.sqrt 3 * (1 - v) / 4) • e₂ := by
    rw [hA, hX, vadd_vsub_vadd_cancel_right]
    module
  have hinner : ⟪C -ᵥ X, A -ᵥ X⟫_ℝ = R ^ 2 / 4 * (v ^ 2 - 3) := by
    rw [hx, hy, hcoord]
    linear_combination (R ^ 2 * (v ^ 2 - 1) / 16) * hs3
  have hnx : ‖C -ᵥ X‖ ^ 2 = R ^ 2 / 4 * (v ^ 2 + 3) := by
    rw [← real_inner_self_eq_norm_sq, hx, hcoord]
    linear_combination (R ^ 2 * (v + 1) ^ 2 / 16) * hs3
  have hny : ‖A -ᵥ X‖ ^ 2 = R ^ 2 / 4 * (v ^ 2 + 3) := by
    rw [← real_inner_self_eq_norm_sq, hy, hcoord]
    linear_combination (R ^ 2 * (1 - v) ^ 2 / 16) * hs3
  have hnx' : ‖C -ᵥ X‖ = Real.sqrt (R ^ 2 / 4 * (v ^ 2 + 3)) := by
    rw [← hnx]
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  have hny' : ‖A -ᵥ X‖ = Real.sqrt (R ^ 2 / 4 * (v ^ 2 + 3)) := by
    rw [← hny]
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  have hprod : ‖C -ᵥ X‖ * ‖A -ᵥ X‖ = R ^ 2 / 4 * (v ^ 2 + 3) := by
    rw [hnx', hny',
      ← Real.sqrt_mul (show (0 : ℝ) ≤ R ^ 2 / 4 * (v ^ 2 + 3) by positivity)
        (R ^ 2 / 4 * (v ^ 2 + 3))]
    exact Real.sqrt_mul_self (show (0 : ℝ) ≤ R ^ 2 / 4 * (v ^ 2 + 3) by positivity)
  have hcos : Real.cos (∠ C X A) = (v ^ 2 - 3) / (v ^ 2 + 3) := by
    unfold EuclideanGeometry.angle
    rw [InnerProductGeometry.cos_angle, hinner, hprod]
    have hne : R ^ 2 / 4 * (v ^ 2 + 3) ≠ 0 := by positivity
    have hne2 : v ^ 2 + 3 ≠ 0 := by positivity
    field_simp
  have hcostr : Real.cos (π - 2 * Real.arctan (v / Real.sqrt 3))
      = (v ^ 2 - 3) / (v ^ 2 + 3) := by
    have hs : (v / Real.sqrt 3) ^ 2 = v ^ 2 / 3 := by
      rw [div_pow, hs3]
    rw [Real.cos_pi_sub, Real.cos_two_mul, Real.cos_arctan, div_pow, one_pow,
      Real.sq_sqrt (show (0 : ℝ) ≤ 1 + (v / Real.sqrt 3) ^ 2 by positivity), hs]
    have hne1 : (1 : ℝ) + v ^ 2 / 3 ≠ 0 := by positivity
    have hne2 : v ^ 2 + 3 ≠ 0 := by positivity
    field_simp
    ring
  have harctan_pos : 0 < Real.arctan (v / Real.sqrt 3) :=
    Real.arctan_pos.2 (div_pos hv0 hspos)
  have harctan_lt : Real.arctan (v / Real.sqrt 3) < π / 3 := by
    have h1 : Real.arctan (Real.sqrt 3) = π / 3 := by
      rw [← Real.tan_pi_div_three]
      exact Real.arctan_tan (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    have h2 : v / Real.sqrt 3 < Real.sqrt 3 := by
      have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
      rw [div_lt_iff₀ hspos]
      linarith
    rw [← h1]
    exact Real.arctan_strictMono h2
  have hθmem : π - 2 * Real.arctan (v / Real.sqrt 3) ∈ Set.Icc 0 π :=
    ⟨by linarith [harctan_lt, Real.pi_pos], by linarith [harctan_pos]⟩
  have hangmem : ∠ C X A ∈ Set.Icc 0 π := by
    unfold EuclideanGeometry.angle
    exact ⟨InnerProductGeometry.angle_nonneg _ _, InnerProductGeometry.angle_le_pi _ _⟩
  exact Real.injOn_cos hangmem hθmem (hcos.trans hcostr.symm)

/-- The angle subtended at the C-median point of parameter w. -/
lemma angle_at_median_C {A B C X : P} {O : P} {R w : ℝ} {e₁ e₂ : V}
    (hR : 0 < R) (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1) (he₁₂ : ⟪e₁, e₂⟫_ℝ = 0)
    (hw0 : 0 < w) (hw3 : w < 3)
    (hA : A = (R • e₁) +ᵥ O)
    (hB : B = ((-R / 2) • e₁ + (R * Real.sqrt 3 / 2) • e₂) +ᵥ O)
    (hC : C = ((-R / 2) • e₁ + (-R * Real.sqrt 3 / 2) • e₂) +ᵥ O)
    (hX : X = ((R * (1 - w) / 4) • e₁ + (R * Real.sqrt 3 * (1 - w) / 4) • e₂) +ᵥ O) :
    ∠ A X B = π - 2 * Real.arctan (w / Real.sqrt 3) := by
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hspos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hcoord : ∀ a b c d : ℝ, ⟪a • e₁ + b • e₂, c • e₁ + d • e₂⟫_ℝ = a * c + b * d := by
    intro a b c d
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      he₁₂, real_inner_comm e₁ e₂, real_inner_self_eq_norm_sq, he₁, he₂]
    ring
  have hx : A -ᵥ X = (R * (w + 3) / 4) • e₁ + (R * Real.sqrt 3 * (w - 1) / 4) • e₂ := by
    rw [hA, hX, vadd_vsub_vadd_cancel_right]
    module
  have hy : B -ᵥ X = (R * (w - 3) / 4) • e₁ + (R * Real.sqrt 3 * (w + 1) / 4) • e₂ := by
    rw [hB, hX, vadd_vsub_vadd_cancel_right]
    module
  have hinner : ⟪A -ᵥ X, B -ᵥ X⟫_ℝ = R ^ 2 / 4 * (w ^ 2 - 3) := by
    rw [hx, hy, hcoord]
    linear_combination (R ^ 2 * (w ^ 2 - 1) / 16) * hs3
  have hnx : ‖A -ᵥ X‖ ^ 2 = R ^ 2 / 4 * (w ^ 2 + 3) := by
    rw [← real_inner_self_eq_norm_sq, hx, hcoord]
    linear_combination (R ^ 2 * (w - 1) ^ 2 / 16) * hs3
  have hny : ‖B -ᵥ X‖ ^ 2 = R ^ 2 / 4 * (w ^ 2 + 3) := by
    rw [← real_inner_self_eq_norm_sq, hy, hcoord]
    linear_combination (R ^ 2 * (w + 1) ^ 2 / 16) * hs3
  have hnx' : ‖A -ᵥ X‖ = Real.sqrt (R ^ 2 / 4 * (w ^ 2 + 3)) := by
    rw [← hnx]
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  have hny' : ‖B -ᵥ X‖ = Real.sqrt (R ^ 2 / 4 * (w ^ 2 + 3)) := by
    rw [← hny]
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  have hprod : ‖A -ᵥ X‖ * ‖B -ᵥ X‖ = R ^ 2 / 4 * (w ^ 2 + 3) := by
    rw [hnx', hny',
      ← Real.sqrt_mul (show (0 : ℝ) ≤ R ^ 2 / 4 * (w ^ 2 + 3) by positivity)
        (R ^ 2 / 4 * (w ^ 2 + 3))]
    exact Real.sqrt_mul_self (show (0 : ℝ) ≤ R ^ 2 / 4 * (w ^ 2 + 3) by positivity)
  have hcos : Real.cos (∠ A X B) = (w ^ 2 - 3) / (w ^ 2 + 3) := by
    unfold EuclideanGeometry.angle
    rw [InnerProductGeometry.cos_angle, hinner, hprod]
    have hne : R ^ 2 / 4 * (w ^ 2 + 3) ≠ 0 := by positivity
    have hne2 : w ^ 2 + 3 ≠ 0 := by positivity
    field_simp
  have hcostr : Real.cos (π - 2 * Real.arctan (w / Real.sqrt 3))
      = (w ^ 2 - 3) / (w ^ 2 + 3) := by
    have hs : (w / Real.sqrt 3) ^ 2 = w ^ 2 / 3 := by
      rw [div_pow, hs3]
    rw [Real.cos_pi_sub, Real.cos_two_mul, Real.cos_arctan, div_pow, one_pow,
      Real.sq_sqrt (show (0 : ℝ) ≤ 1 + (w / Real.sqrt 3) ^ 2 by positivity), hs]
    have hne1 : (1 : ℝ) + w ^ 2 / 3 ≠ 0 := by positivity
    have hne2 : w ^ 2 + 3 ≠ 0 := by positivity
    field_simp
    ring
  have harctan_pos : 0 < Real.arctan (w / Real.sqrt 3) :=
    Real.arctan_pos.2 (div_pos hw0 hspos)
  have harctan_lt : Real.arctan (w / Real.sqrt 3) < π / 3 := by
    have h1 : Real.arctan (Real.sqrt 3) = π / 3 := by
      rw [← Real.tan_pi_div_three]
      exact Real.arctan_tan (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    have h2 : w / Real.sqrt 3 < Real.sqrt 3 := by
      have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
      rw [div_lt_iff₀ hspos]
      linarith
    rw [← h1]
    exact Real.arctan_strictMono h2
  have hθmem : π - 2 * Real.arctan (w / Real.sqrt 3) ∈ Set.Icc 0 π :=
    ⟨by linarith [harctan_lt, Real.pi_pos], by linarith [harctan_pos]⟩
  have hangmem : ∠ A X B ∈ Set.Icc 0 π := by
    unfold EuclideanGeometry.angle
    exact ⟨InnerProductGeometry.angle_nonneg _ _, InnerProductGeometry.angle_le_pi _ _⟩
  exact Real.injOn_cos hangmem hθmem (hcos.trans hcostr.symm)

/-- The angle-sum condition in tangent parameters gives the polynomial constraint
and the strict upper bounds. -/
lemma hrel_and_bounds {u v w : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hsum : (π - 2 * Real.arctan (u / Real.sqrt 3)) +
            (π - 2 * Real.arctan (v / Real.sqrt 3)) +
            (π - 2 * Real.arctan (w / Real.sqrt 3)) = 8 / 3 * π) :
    u < 1 ∧ v < 1 ∧ w < 1 ∧ w * (3 + u + v - u * v) = 3 - u * v - 3 * u - 3 * v := by
  set s := Real.sqrt 3 with hs_def
  have hs : 0 < s := Real.sqrt_pos.2 (by norm_num)
  have hsq : s ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hss : s * s = 3 := by rw [← pow_two]; exact hsq
  set x := Real.arctan (u / s) with hx_def
  set y := Real.arctan (v / s) with hy_def
  set z := Real.arctan (w / s) with hz_def
  have hx0 : 0 < x := Real.arctan_pos.2 (div_pos hu hs)
  have hy0 : 0 < y := Real.arctan_pos.2 (div_pos hv hs)
  have hz0 : 0 < z := Real.arctan_pos.2 (div_pos hw hs)
  have h1 : x + y + z = π / 6 := by linarith [hsum, Real.pi_pos]
  have hx6 : x < π / 6 := by linarith [h1, hy0, hz0]
  have hy6 : y < π / 6 := by linarith [h1, hx0, hz0]
  have hz6 : z < π / 6 := by linarith [h1, hx0, hy0]
  have hπ26 : π / 6 < π / 2 := by linarith [Real.pi_pos]
  have htan6 : Real.tan (π / 6) = 1 / s := Real.tan_pi_div_six
  -- Strict upper bounds on the parameters, from monotonicity of `tan`.
  have hu1 : u < 1 := by
    have h := Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two hx0.le hπ26 hx6
    rw [hx_def, Real.tan_arctan, htan6] at h
    have h2 := mul_lt_mul_of_pos_right h hs
    rwa [div_mul_cancel₀ u hs.ne', div_mul_cancel₀ (1 : ℝ) hs.ne'] at h2
  have hv1 : v < 1 := by
    have h := Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two hy0.le hπ26 hy6
    rw [hy_def, Real.tan_arctan, htan6] at h
    have h2 := mul_lt_mul_of_pos_right h hs
    rwa [div_mul_cancel₀ v hs.ne', div_mul_cancel₀ (1 : ℝ) hs.ne'] at h2
  have hw1 : w < 1 := by
    have h := Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two hz0.le hπ26 hz6
    rw [hz_def, Real.tan_arctan, htan6] at h
    have h2 := mul_lt_mul_of_pos_right h hs
    rwa [div_mul_cancel₀ w hs.ne', div_mul_cancel₀ (1 : ℝ) hs.ne'] at h2
  -- The polynomial constraint, from the tangent addition formula.
  have hne : ∀ {t : ℝ}, t ∈ Set.Ioo (-(π / 2)) (π / 2) → ∀ k : ℤ,
      t ≠ (2 * k + 1) * π / 2 :=
    fun ht k hk => (Real.cos_pos_of_mem_Ioo ht).ne' (Real.cos_eq_zero_iff.mpr ⟨k, hk⟩)
  have hxmem : x ∈ Set.Ioo (-(π / 2)) (π / 2) :=
    ⟨by linarith [Real.pi_pos, hx0], by linarith [Real.pi_pos, hx6]⟩
  have hymem : y ∈ Set.Ioo (-(π / 2)) (π / 2) :=
    ⟨by linarith [Real.pi_pos, hy0], by linarith [Real.pi_pos, hy6]⟩
  have hzmem : z ∈ Set.Ioo (-(π / 2)) (π / 2) :=
    ⟨by linarith [Real.pi_pos, hz0], by linarith [Real.pi_pos, hz6]⟩
  have hxymem : x + y ∈ Set.Ioo (-(π / 2)) (π / 2) :=
    ⟨by linarith [Real.pi_pos, hx0, hy0], by linarith [Real.pi_pos, h1, hz0]⟩
  set S := (u / s + v / s) / (1 - (u / s) * (v / s)) with hS
  have hSxy : Real.tan (x + y) = S := by
    rw [hS, Real.tan_add' ⟨hne hxmem, hne hymem⟩, hx_def, hy_def, Real.tan_arctan,
      Real.tan_arctan]
  have hTan : (S + w / s) / (1 - S * (w / s)) = 1 / s := by
    have h2 : Real.tan (x + y + z) = 1 / s := by rw [h1, htan6]
    rw [Real.tan_add' ⟨hne hxymem, hne hzmem⟩, hSxy, hz_def, Real.tan_arctan] at h2
    exact h2
  have hD2 : (1 : ℝ) - S * (w / s) ≠ 0 := by
    intro h0
    rw [h0, div_zero] at hTan
    exact (ne_of_gt (one_div_pos.mpr hs)) hTan.symm
  have huv : u * v < 1 := by
    calc u * v < u * 1 := mul_lt_mul_of_pos_left hv1 hu
      _ = u := mul_one u
      _ < 1 := hu1
  have huvs : (u / s) * (v / s) = u * v / 3 := by rw [div_mul_div_comm, hss]
  have hD1 : (0 : ℝ) < 1 - (u / s) * (v / s) := by rw [huvs]; linarith [huv]
  have hS' : S * (1 - (u / s) * (v / s)) = u / s + v / s := by
    rw [hS]
    exact div_mul_cancel₀ _ hD1.ne'
  have key2 : s * S + w = 1 - S * (w / s) := by
    have h := (div_eq_iff hD2).mp hTan
    have h2 := congrArg (s * ·) h
    rw [mul_add, mul_div_cancel₀ w hs.ne', ← mul_assoc, mul_one_div_cancel hs.ne',
      one_mul] at h2
    exact h2
  have key3 : s * S * s + w * s = s - S * w := by
    have h2 := congrArg (· * s) key2
    rw [add_mul, sub_mul, one_mul, mul_assoc S (w / s) s, div_mul_cancel₀ w hs.ne'] at h2
    exact h2
  have eqA : s * S * (1 - (u / s) * (v / s)) = u + v := by
    rw [mul_assoc, hS', mul_add, mul_div_cancel₀ u hs.ne', mul_div_cancel₀ v hs.ne']
  have hA : s * S * (3 - u * v) = 3 * (u + v) := by
    calc s * S * (3 - u * v) = 3 * (s * S * (1 - (u / s) * (v / s))) := by
          rw [huvs]; ring
      _ = 3 * (u + v) := by rw [eqA]
  have hB : S * w * (3 - u * v) * s = 3 * (w * (u + v)) := by
    calc S * w * (3 - u * v) * s = 3 * w * (S * (1 - (u / s) * (v / s)) * s) := by
          rw [huvs]; ring
      _ = 3 * w * ((u / s + v / s) * s) := by rw [hS']
      _ = 3 * (w * (u + v)) := by
          rw [add_mul, div_mul_cancel₀ u hs.ne', div_mul_cancel₀ v hs.ne']; ring
  have h3 : w * (s ^ 2 + u + v - u * v) = s ^ 2 - u * v - s ^ 2 * (u + v) := by
    linear_combination ((3 - u * v) * s / 3) * key3 - (s * s / 3) * hA -
      (1 / 3 : ℝ) * hB + (u * v * (w - 1) / 3) * hsq
  refine ⟨hu1, hv1, hw1, ?_⟩
  linear_combination h3 - (w + u + v - 1) * hsq

/-- The frontend of the proof: coordinates for all six given points,
the parameter constraint from the angle condition, and the parameter
bounds from the interior hypotheses. -/
lemma frontend {A B C A₁ B₁ C₁ : P}
    (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C])
    (equilateral_ABC : (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).Equilateral)
    (A₁_mem_interior_ABC : A₁ ∈ (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).interior)
    (B₁_mem_interior_ABC : B₁ ∈ (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).interior)
    (C₁_mem_interior_ABC : C₁ ∈ (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).interior)
    (BA₁_eq_A₁C : dist B A₁ = dist A₁ C) (CB₁_eq_B₁A : dist C B₁ = dist B₁ A)
    (AC₁_eq_C₁B : dist A C₁ = dist C₁ B)
    (angle_BA₁C_add_angle_CB₁A_add_angle_AC₁B :
      ∠ B A₁ C + ∠ C B₁ A + ∠ A C₁ B = 8 / 3 * π) :
    ∃ (O : P) (R u v u₃ : ℝ) (e₁ e₂ : V),
      0 < R ∧ ‖e₁‖ = 1 ∧ ‖e₂‖ = 1 ∧ ⟪e₁, e₂⟫_ℝ = 0 ∧
      A = (R • e₁) +ᵥ O ∧
      B = ((-R / 2) • e₁ + (R * Real.sqrt 3 / 2) • e₂) +ᵥ O ∧
      C = ((-R / 2) • e₁ + (-R * Real.sqrt 3 / 2) • e₂) +ᵥ O ∧
      A₁ = ((R * (u - 1) / 2) • e₁) +ᵥ O ∧
      B₁ = ((R * (1 - v) / 4) • e₁ + (R * Real.sqrt 3 * (v - 1) / 4) • e₂) +ᵥ O ∧
      C₁ = ((R * (1 - u₃) / 4) • e₁ + (R * Real.sqrt 3 * (1 - u₃) / 4) • e₂) +ᵥ O ∧
      0 < u ∧ u < 1 ∧ 0 < v ∧ v < 1 ∧ 0 < u₃ ∧ u₃ < 1 ∧
      u₃ * (3 + u + v - u * v) = 3 - u * v - 3 * u - 3 * v := by
  obtain ⟨O, R, e₁, e₂, hR, he₁, he₂, he₁₂, hA, hB, hC⟩ :=
    frame_lemma affineIndependent_ABC equilateral_ABC
  obtain ⟨u, hu0, hu3, hA₁⟩ :=
    median_coord_A affineIndependent_ABC A₁_mem_interior_ABC BA₁_eq_A₁C hR he₁ he₂ he₁₂ hA hB hC
  obtain ⟨v, hv0, hv3, hB₁⟩ :=
    median_coord_B affineIndependent_ABC B₁_mem_interior_ABC CB₁_eq_B₁A hR he₁ he₂ he₁₂ hA hB hC
  obtain ⟨u₃, hu₃0, hu₃3, hC₁⟩ :=
    median_coord_C affineIndependent_ABC C₁_mem_interior_ABC AC₁_eq_C₁B hR he₁ he₂ he₁₂ hA hB hC
  have hα := angle_at_median_A (A := A) hR he₁ he₂ he₁₂ hu0 hu3 hB hC hA₁
  have hβ := angle_at_median_B (A := A) (B := B) hR he₁ he₂ he₁₂ hv0 hv3 hA hB hC hB₁
  have hγ := angle_at_median_C (A := A) (B := B) (C := C) hR he₁ he₂ he₁₂ hu₃0 hu₃3 hA hB hC hC₁
  rw [hα, hβ, hγ] at angle_BA₁C_add_angle_CB₁A_add_angle_AC₁B
  obtain ⟨hu1, hv1, hu₃1, hrel⟩ := hrel_and_bounds hu0 hv0 hu₃0
    angle_BA₁C_add_angle_CB₁A_add_angle_AC₁B
  exact ⟨O, R, u, v, u₃, e₁, e₂, hR, he₁, he₂, he₁₂, hA, hB, hC, hA₁, hB₁, hC₁,
    hu0, hu1, hv0, hv1, hu₃0, hu₃1, hrel⟩

/-- Coordinates of `A₂, B₂, C₂`, from the line memberships. -/
lemma a2b2c2_coords {A B C A₁ B₁ C₁ A₂ B₂ C₂ : P}
    (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C])
    (equilateral_ABC : (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).Equilateral)
    (A₂_mem_inf_BC₁_CB₁ : A₂ ∈ line[ℝ, B, C₁] ⊓ line[ℝ, C, B₁])
    (B₂_mem_inf_CA₁_AC₁ : B₂ ∈ line[ℝ, C, A₁] ⊓ line[ℝ, A, C₁])
    (C₂_mem_inf_AB₁_BA₁ : C₂ ∈ line[ℝ, A, B₁] ⊓ line[ℝ, B, A₁])
    {O : P} {R u v u₃ : ℝ} {e₁ e₂ : V}
    (hR : 0 < R) (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1) (he₁₂ : ⟪e₁, e₂⟫_ℝ = 0)
    (hA : A = (R • e₁) +ᵥ O)
    (hB : B = ((-R / 2) • e₁ + (R * Real.sqrt 3 / 2) • e₂) +ᵥ O)
    (hC : C = ((-R / 2) • e₁ + (-R * Real.sqrt 3 / 2) • e₂) +ᵥ O)
    (hA₁ : A₁ = ((R * (u - 1) / 2) • e₁) +ᵥ O)
    (hB₁ : B₁ = ((R * (1 - v) / 4) • e₁ + (R * Real.sqrt 3 * (v - 1) / 4) • e₂) +ᵥ O)
    (hC₁ : C₁ = ((R * (1 - u₃) / 4) • e₁ + (R * Real.sqrt 3 * (1 - u₃) / 4) • e₂) +ᵥ O)
    (hu : 0 < u ∧ u < 1) (hv : 0 < v ∧ v < 1) (hu₃ : 0 < u₃ ∧ u₃ < 1)
    (hrel : u₃ * (3 + u + v - u * v) = 3 - u * v - 3 * u - 3 * v)
    (hscal : u ≠ v ∧ u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3 ≠ 0 ∧
      u ^ 2 * v - u ^ 2 - 2 * u * v - 6 * u - 3 * v + 3 ≠ 0) :
    A₂ = ((-R * (u₃ * v - 2 * u₃ - 2 * v + 3) / (u₃ * v - u₃ - v - 3)) • e₁ +
        (Real.sqrt 3 * R * (u₃ - v) / (u₃ * v - u₃ - v - 3)) • e₂) +ᵥ O ∧
    B₂ = ((R * (u * u₃ - 5 * u + u₃ + 3) / (2 * (u * u₃ - u - u₃ - 3))) • e₁ +
        (-Real.sqrt 3 * R * (u - 3) * (u₃ - 1) / (2 * (u * u₃ - u - u₃ - 3))) • e₂) +ᵥ O ∧
    C₂ = ((R * (u * v - 5 * u + v + 3) / (2 * (u * v - u - v - 3))) • e₁ +
        (Real.sqrt 3 * R * (u - 3) * (v - 1) / (2 * (u * v - u - v - 3))) • e₂) +ᵥ O := by
  -- Coordinates in the orthonormal pair `e₁, e₂` are unique.
  have coord_inj : ∀ {m n m' n' : ℝ}, m • e₁ + n • e₂ = m' • e₁ + n' • e₂ →
      m = m' ∧ n = n' := by
    intro m n m' n' hmn
    have h1 := congrArg (fun z : V => ⟪e₁, z⟫_ℝ) hmn
    have h2 := congrArg (fun z : V => ⟪e₂, z⟫_ℝ) hmn
    simp only [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, he₁, he₂,
      real_inner_comm e₁ e₂, he₁₂, mul_one, mul_zero, add_zero, zero_add, one_pow] at h1 h2
    exact ⟨h1, h2⟩
  have hw : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hR' : R ≠ 0 := ne_of_gt hR
  -- The denominators are nonzero on the parameter domain.
  have hΔAc : u₃ * v - u₃ - v - 3 ≠ 0 := by
    have h1 : u₃ * v < u₃ := by
      have h2 := mul_lt_mul_of_pos_left hv.2 hu₃.1
      rwa [mul_one] at h2
    have h2 : u₃ * v - u₃ - v - 3 < 0 := by linarith [hv.1]
    exact ne_of_lt h2
  have hΔBc : u * u₃ - u - u₃ - 3 ≠ 0 := by
    have h1 : u * u₃ < u := by
      have h2 := mul_lt_mul_of_pos_left hu₃.2 hu.1
      rwa [mul_one] at h2
    have h2 : u * u₃ - u - u₃ - 3 < 0 := by linarith [hu₃.1]
    exact ne_of_lt h2
  have hΔCc : u * v - u - v - 3 ≠ 0 := by
    have h1 : u * v < u := by
      have h2 := mul_lt_mul_of_pos_left hv.2 hu.1
      rwa [mul_one] at h2
    have h2 : u * v - u - v - 3 < 0 := by linarith [hv.1]
    exact ne_of_lt h2
  have hΔB : 2 * (u * u₃ - u - u₃ - 3) ≠ 0 := mul_ne_zero (by norm_num) hΔBc
  have hΔC : 2 * (u * v - u - v - 3) ≠ 0 := mul_ne_zero (by norm_num) hΔCc
  -- The six direction vectors, in coordinates.
  have hC₁B : C₁ -ᵥ B = (R * (3 - u₃) / 4) • e₁ + (-(R * Real.sqrt 3) * (1 + u₃) / 4) • e₂ := by
    rw [← vsub_sub_vsub_cancel_right C₁ B O, hC₁, hB, vadd_vsub, vadd_vsub]
    module
  have hB₁C : B₁ -ᵥ C = (R * (3 - v) / 4) • e₁ + (R * Real.sqrt 3 * (1 + v) / 4) • e₂ := by
    rw [← vsub_sub_vsub_cancel_right B₁ C O, hB₁, hC, vadd_vsub, vadd_vsub]
    module
  have hA₁C : A₁ -ᵥ C = (R * u / 2) • e₁ + (R * Real.sqrt 3 / 2) • e₂ := by
    rw [← vsub_sub_vsub_cancel_right A₁ C O, hA₁, hC, vadd_vsub, vadd_vsub]
    module
  have hC₁A : C₁ -ᵥ A = (-R * (3 + u₃) / 4) • e₁ + (R * Real.sqrt 3 * (1 - u₃) / 4) • e₂ := by
    rw [← vsub_sub_vsub_cancel_right C₁ A O, hC₁, hA, vadd_vsub, vadd_vsub]
    module
  have hB₁A : B₁ -ᵥ A = (-R * (3 + v) / 4) • e₁ + (R * Real.sqrt 3 * (v - 1) / 4) • e₂ := by
    rw [← vsub_sub_vsub_cancel_right B₁ A O, hB₁, hA, vadd_vsub, vadd_vsub]
    module
  have hA₁B : A₁ -ᵥ B = (R * u / 2) • e₁ + (-(R * Real.sqrt 3) / 2) • e₂ := by
    rw [← vsub_sub_vsub_cancel_right A₁ B O, hA₁, hB, vadd_vsub, vadd_vsub]
    module
  -- `A₂`: on the lines through `B, C₁` and through `C, B₁`.
  have hA₂ : A₂ = ((-R * (u₃ * v - 2 * u₃ - 2 * v + 3) / (u₃ * v - u₃ - v - 3)) • e₁ +
      (Real.sqrt 3 * R * (u₃ - v) / (u₃ * v - u₃ - v - 3)) • e₂) +ᵥ O := by
    have hd1 : A₂ -ᵥ B ∈ vectorSpan ℝ ({B, C₁} : Set P) := by
      have h1 := AffineSubspace.vsub_mem_direction
        ((AffineSubspace.mem_inf_iff A₂ _ _).mp A₂_mem_inf_BC₁_CB₁).1
        (left_mem_affineSpan_pair ℝ B C₁)
      rwa [direction_affineSpan] at h1
    have hd2 : A₂ -ᵥ C ∈ vectorSpan ℝ ({C, B₁} : Set P) := by
      have h2 := AffineSubspace.vsub_mem_direction
        ((AffineSubspace.mem_inf_iff A₂ _ _).mp A₂_mem_inf_BC₁_CB₁).2
        (left_mem_affineSpan_pair ℝ C B₁)
      rwa [direction_affineSpan] at h2
    obtain ⟨r, hr⟩ := mem_vectorSpan_pair_rev.mp hd1
    obtain ⟨s, hs⟩ := mem_vectorSpan_pair_rev.mp hd2
    have hO1 : A₂ -ᵥ O = (-R / 2 + r * (R * (3 - u₃) / 4)) • e₁ +
        (R * Real.sqrt 3 / 2 + r * (-(R * Real.sqrt 3) * (1 + u₃) / 4)) • e₂ := by
      rw [← vsub_add_vsub_cancel A₂ B O, ← hr, hC₁B, hB, vadd_vsub]
      module
    have hO2 : A₂ -ᵥ O = (-R / 2 + s * (R * (3 - v) / 4)) • e₁ +
        (-R * Real.sqrt 3 / 2 + s * (R * Real.sqrt 3 * (1 + v) / 4)) • e₂ := by
      rw [← vsub_add_vsub_cancel A₂ C O, ← hs, hB₁C, hC, vadd_vsub]
      module
    obtain ⟨hE1, hE2⟩ := coord_inj (hO1.symm.trans hO2)
    have hdet : (R * (3 - u₃) / 4) * (R * Real.sqrt 3 * (1 + v) / 4) -
        (-(R * Real.sqrt 3) * (1 + u₃) / 4) * (R * (3 - v) / 4) ≠ 0 := by
      have he : (R * (3 - u₃) / 4) * (R * Real.sqrt 3 * (1 + v) / 4) -
          (-(R * Real.sqrt 3) * (1 + u₃) / 4) * (R * (3 - v) / 4) =
          -(R ^ 2 * Real.sqrt 3) / 8 * (u₃ * v - u₃ - v - 3) := by
        ring
      rw [he]
      exact mul_ne_zero (div_ne_zero (neg_ne_zero.mpr
        (mul_ne_zero (pow_ne_zero 2 hR') hw)) (by norm_num)) hΔAc
    have hkx : ((R * (3 - u₃) / 4) * (R * Real.sqrt 3 * (1 + v) / 4) -
        (-(R * Real.sqrt 3) * (1 + u₃) / 4) * (R * (3 - v) / 4)) *
        ((-R / 2 + r * (R * (3 - u₃) / 4)) * (u₃ * v - u₃ - v - 3) +
        R * (u₃ * v - 2 * u₃ - 2 * v + 3)) = 0 := by
      linear_combination
        (R * (3 - u₃) / 4 * (u₃ * v - u₃ - v - 3) * (R * Real.sqrt 3 * (1 + v) / 4)) * hE1 -
        (R * (3 - u₃) / 4 * (u₃ * v - u₃ - v - 3) * (R * (3 - v) / 4)) * hE2
    have hx : (-R / 2 + r * (R * (3 - u₃) / 4)) * (u₃ * v - u₃ - v - 3) =
        -R * (u₃ * v - 2 * u₃ - 2 * v + 3) := by
      rcases mul_eq_zero.mp hkx with h | h
      · exact absurd h hdet
      · linarith
    have hky : ((R * (3 - u₃) / 4) * (R * Real.sqrt 3 * (1 + v) / 4) -
        (-(R * Real.sqrt 3) * (1 + u₃) / 4) * (R * (3 - v) / 4)) *
        ((R * Real.sqrt 3 / 2 + r * (-(R * Real.sqrt 3) * (1 + u₃) / 4)) *
        (u₃ * v - u₃ - v - 3) - Real.sqrt 3 * R * (u₃ - v)) = 0 := by
      linear_combination
        ((-(R * Real.sqrt 3) * (1 + u₃) / 4) * (u₃ * v - u₃ - v - 3) *
          (R * Real.sqrt 3 * (1 + v) / 4)) * hE1 -
        ((-(R * Real.sqrt 3) * (1 + u₃) / 4) * (u₃ * v - u₃ - v - 3) * (R * (3 - v) / 4)) * hE2
    have hy : (R * Real.sqrt 3 / 2 + r * (-(R * Real.sqrt 3) * (1 + u₃) / 4)) *
        (u₃ * v - u₃ - v - 3) = Real.sqrt 3 * R * (u₃ - v) := by
      rcases mul_eq_zero.mp hky with h | h
      · exact absurd h hdet
      · linarith
    rw [eq_vadd_iff_vsub_eq, hO1, (eq_div_iff hΔAc).mpr hx, (eq_div_iff hΔAc).mpr hy]
  -- `B₂`: on the lines through `C, A₁` and through `A, C₁`.
  have hB₂ : B₂ = ((R * (u * u₃ - 5 * u + u₃ + 3) / (2 * (u * u₃ - u - u₃ - 3))) • e₁ +
      (-Real.sqrt 3 * R * (u - 3) * (u₃ - 1) / (2 * (u * u₃ - u - u₃ - 3))) • e₂) +ᵥ O := by
    have hd1 : B₂ -ᵥ C ∈ vectorSpan ℝ ({C, A₁} : Set P) := by
      have h1 := AffineSubspace.vsub_mem_direction
        ((AffineSubspace.mem_inf_iff B₂ _ _).mp B₂_mem_inf_CA₁_AC₁).1
        (left_mem_affineSpan_pair ℝ C A₁)
      rwa [direction_affineSpan] at h1
    have hd2 : B₂ -ᵥ A ∈ vectorSpan ℝ ({A, C₁} : Set P) := by
      have h2 := AffineSubspace.vsub_mem_direction
        ((AffineSubspace.mem_inf_iff B₂ _ _).mp B₂_mem_inf_CA₁_AC₁).2
        (left_mem_affineSpan_pair ℝ A C₁)
      rwa [direction_affineSpan] at h2
    obtain ⟨r, hr⟩ := mem_vectorSpan_pair_rev.mp hd1
    obtain ⟨s, hs⟩ := mem_vectorSpan_pair_rev.mp hd2
    have hO1 : B₂ -ᵥ O = (-R / 2 + r * (R * u / 2)) • e₁ +
        (-R * Real.sqrt 3 / 2 + r * (R * Real.sqrt 3 / 2)) • e₂ := by
      rw [← vsub_add_vsub_cancel B₂ C O, ← hr, hA₁C, hC, vadd_vsub]
      module
    have hO2 : B₂ -ᵥ O = (R + s * (-R * (3 + u₃) / 4)) • e₁ +
        (s * (R * Real.sqrt 3 * (1 - u₃) / 4)) • e₂ := by
      rw [← vsub_add_vsub_cancel B₂ A O, ← hs, hC₁A, hA, vadd_vsub]
      module
    obtain ⟨hE1, hE2⟩ := coord_inj (hO1.symm.trans hO2)
    have hdet : (R * u / 2) * (R * Real.sqrt 3 * (1 - u₃) / 4) -
        (R * Real.sqrt 3 / 2) * (-R * (3 + u₃) / 4) ≠ 0 := by
      have he : (R * u / 2) * (R * Real.sqrt 3 * (1 - u₃) / 4) -
          (R * Real.sqrt 3 / 2) * (-R * (3 + u₃) / 4) =
          -(R ^ 2 * Real.sqrt 3) / 8 * (u * u₃ - u - u₃ - 3) := by
        ring
      rw [he]
      exact mul_ne_zero (div_ne_zero (neg_ne_zero.mpr
        (mul_ne_zero (pow_ne_zero 2 hR') hw)) (by norm_num)) hΔBc
    have hkx : ((R * u / 2) * (R * Real.sqrt 3 * (1 - u₃) / 4) -
        (R * Real.sqrt 3 / 2) * (-R * (3 + u₃) / 4)) *
        ((-R / 2 + r * (R * u / 2)) * (2 * (u * u₃ - u - u₃ - 3)) -
        R * (u * u₃ - 5 * u + u₃ + 3)) = 0 := by
      linear_combination
        (R * u / 2 * (2 * (u * u₃ - u - u₃ - 3)) * (R * Real.sqrt 3 * (1 - u₃) / 4)) * hE1 -
        (R * u / 2 * (2 * (u * u₃ - u - u₃ - 3)) * (-R * (3 + u₃) / 4)) * hE2
    have hx : (-R / 2 + r * (R * u / 2)) * (2 * (u * u₃ - u - u₃ - 3)) =
        R * (u * u₃ - 5 * u + u₃ + 3) := by
      rcases mul_eq_zero.mp hkx with h | h
      · exact absurd h hdet
      · linarith
    have hky : ((R * u / 2) * (R * Real.sqrt 3 * (1 - u₃) / 4) -
        (R * Real.sqrt 3 / 2) * (-R * (3 + u₃) / 4)) *
        ((-R * Real.sqrt 3 / 2 + r * (R * Real.sqrt 3 / 2)) * (2 * (u * u₃ - u - u₃ - 3)) +
        Real.sqrt 3 * R * (u - 3) * (u₃ - 1)) = 0 := by
      linear_combination
        (R * Real.sqrt 3 / 2 * (2 * (u * u₃ - u - u₃ - 3)) *
          (R * Real.sqrt 3 * (1 - u₃) / 4)) * hE1 -
        (R * Real.sqrt 3 / 2 * (2 * (u * u₃ - u - u₃ - 3)) * (-R * (3 + u₃) / 4)) * hE2
    have hy : (-R * Real.sqrt 3 / 2 + r * (R * Real.sqrt 3 / 2)) *
        (2 * (u * u₃ - u - u₃ - 3)) = -Real.sqrt 3 * R * (u - 3) * (u₃ - 1) := by
      rcases mul_eq_zero.mp hky with h | h
      · exact absurd h hdet
      · linarith
    rw [eq_vadd_iff_vsub_eq, hO1, (eq_div_iff hΔB).mpr hx, (eq_div_iff hΔB).mpr hy]
  -- `C₂`: on the lines through `A, B₁` and through `B, A₁`.
  have hC₂ : C₂ = ((R * (u * v - 5 * u + v + 3) / (2 * (u * v - u - v - 3))) • e₁ +
      (Real.sqrt 3 * R * (u - 3) * (v - 1) / (2 * (u * v - u - v - 3))) • e₂) +ᵥ O := by
    have hd1 : C₂ -ᵥ A ∈ vectorSpan ℝ ({A, B₁} : Set P) := by
      have h1 := AffineSubspace.vsub_mem_direction
        ((AffineSubspace.mem_inf_iff C₂ _ _).mp C₂_mem_inf_AB₁_BA₁).1
        (left_mem_affineSpan_pair ℝ A B₁)
      rwa [direction_affineSpan] at h1
    have hd2 : C₂ -ᵥ B ∈ vectorSpan ℝ ({B, A₁} : Set P) := by
      have h2 := AffineSubspace.vsub_mem_direction
        ((AffineSubspace.mem_inf_iff C₂ _ _).mp C₂_mem_inf_AB₁_BA₁).2
        (left_mem_affineSpan_pair ℝ B A₁)
      rwa [direction_affineSpan] at h2
    obtain ⟨r, hr⟩ := mem_vectorSpan_pair_rev.mp hd1
    obtain ⟨s, hs⟩ := mem_vectorSpan_pair_rev.mp hd2
    have hO1 : C₂ -ᵥ O = (R + r * (-R * (3 + v) / 4)) • e₁ +
        (r * (R * Real.sqrt 3 * (v - 1) / 4)) • e₂ := by
      rw [← vsub_add_vsub_cancel C₂ A O, ← hr, hB₁A, hA, vadd_vsub]
      module
    have hO2 : C₂ -ᵥ O = (-R / 2 + s * (R * u / 2)) • e₁ +
        (R * Real.sqrt 3 / 2 + s * (-(R * Real.sqrt 3) / 2)) • e₂ := by
      rw [← vsub_add_vsub_cancel C₂ B O, ← hs, hA₁B, hB, vadd_vsub]
      module
    obtain ⟨hE1, hE2⟩ := coord_inj (hO1.symm.trans hO2)
    have hdet : (-R * (3 + v) / 4) * (-(R * Real.sqrt 3) / 2) -
        (R * Real.sqrt 3 * (v - 1) / 4) * (R * u / 2) ≠ 0 := by
      have he : (-R * (3 + v) / 4) * (-(R * Real.sqrt 3) / 2) -
          (R * Real.sqrt 3 * (v - 1) / 4) * (R * u / 2) =
          -(R ^ 2 * Real.sqrt 3) / 8 * (u * v - u - v - 3) := by
        ring
      rw [he]
      exact mul_ne_zero (div_ne_zero (neg_ne_zero.mpr
        (mul_ne_zero (pow_ne_zero 2 hR') hw)) (by norm_num)) hΔCc
    have hkx : ((-R * (3 + v) / 4) * (-(R * Real.sqrt 3) / 2) -
        (R * Real.sqrt 3 * (v - 1) / 4) * (R * u / 2)) *
        ((R + r * (-R * (3 + v) / 4)) * (2 * (u * v - u - v - 3)) -
        R * (u * v - 5 * u + v + 3)) = 0 := by
      linear_combination
        ((-R * (3 + v) / 4) * (2 * (u * v - u - v - 3)) * (-(R * Real.sqrt 3) / 2)) * hE1 -
        ((-R * (3 + v) / 4) * (2 * (u * v - u - v - 3)) * (R * u / 2)) * hE2
    have hx : (R + r * (-R * (3 + v) / 4)) * (2 * (u * v - u - v - 3)) =
        R * (u * v - 5 * u + v + 3) := by
      rcases mul_eq_zero.mp hkx with h | h
      · exact absurd h hdet
      · linarith
    have hky : ((-R * (3 + v) / 4) * (-(R * Real.sqrt 3) / 2) -
        (R * Real.sqrt 3 * (v - 1) / 4) * (R * u / 2)) *
        ((r * (R * Real.sqrt 3 * (v - 1) / 4)) * (2 * (u * v - u - v - 3)) -
        Real.sqrt 3 * R * (u - 3) * (v - 1)) = 0 := by
      linear_combination
        ((R * Real.sqrt 3 * (v - 1) / 4) * (2 * (u * v - u - v - 3)) *
          (-(R * Real.sqrt 3) / 2)) * hE1 -
        ((R * Real.sqrt 3 * (v - 1) / 4) * (2 * (u * v - u - v - 3)) * (R * u / 2)) * hE2
    have hy : (r * (R * Real.sqrt 3 * (v - 1) / 4)) * (2 * (u * v - u - v - 3)) =
        Real.sqrt 3 * R * (u - 3) * (v - 1) := by
      rcases mul_eq_zero.mp hky with h | h
      · exact absurd h hdet
      · linarith
    rw [eq_vadd_iff_vsub_eq, hO1, (eq_div_iff hΔC).mpr hx, (eq_div_iff hΔC).mpr hy]
  exact ⟨hA₂, hB₂, hC₂⟩

/-- The scalene hypothesis in terms of the parameters. -/
lemma scalene_params {A B C A₁ B₁ C₁ : P}
    (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C])
    (equilateral_ABC : (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).Equilateral)
    (affineIndependent_A₁B₁C₁ : AffineIndependent ℝ ![A₁, B₁, C₁])
    (scalene_A₁B₁C₁ : (⟨_, affineIndependent_A₁B₁C₁⟩ : Triangle ℝ P).Scalene)
    {O : P} {R u v u₃ : ℝ} {e₁ e₂ : V}
    (hR : 0 < R) (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1) (he₁₂ : ⟪e₁, e₂⟫_ℝ = 0)
    (hA : A = (R • e₁) +ᵥ O)
    (hB : B = ((-R / 2) • e₁ + (R * Real.sqrt 3 / 2) • e₂) +ᵥ O)
    (hC : C = ((-R / 2) • e₁ + (-R * Real.sqrt 3 / 2) • e₂) +ᵥ O)
    (hA₁ : A₁ = ((R * (u - 1) / 2) • e₁) +ᵥ O)
    (hB₁ : B₁ = ((R * (1 - v) / 4) • e₁ + (R * Real.sqrt 3 * (v - 1) / 4) • e₂) +ᵥ O)
    (hC₁ : C₁ = ((R * (1 - u₃) / 4) • e₁ + (R * Real.sqrt 3 * (1 - u₃) / 4) • e₂) +ᵥ O)
    (hrel : u₃ * (3 + u + v - u * v) = 3 - u * v - 3 * u - 3 * v) :
    u ≠ v ∧ u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3 ≠ 0 ∧
      u ^ 2 * v - u ^ 2 - 2 * u * v - 6 * u - 3 * v + 3 ≠ 0 := by
  have hsc := Triangle.scalene_iff_dist_ne_and_dist_ne_and_dist_ne.mp scalene_A₁B₁C₁
  have h₁ : dist A₁ B₁ ≠ dist A₁ C₁ := by simpa using hsc.1
  have h₂ : dist A₁ B₁ ≠ dist B₁ C₁ := by simpa using hsc.2.1
  have h₃ : dist A₁ C₁ ≠ dist B₁ C₁ := by simpa using hsc.2.2
  have hA₁' : A₁ = ((R * (u - 1) / 2) • e₁ + (0 : ℝ) • e₂) +ᵥ O := by
    rw [hA₁]
    congr 1
    module
  have hAB2 : dist A₁ B₁ ^ 2 =
      (R * (u - 1) / 2 - R * (1 - v) / 4) ^ 2 + (0 - R * Real.sqrt 3 * (v - 1) / 4) ^ 2 := by
    rw [hA₁', hB₁]
    exact coord_dist_sq he₁ he₂ he₁₂ _ _ _ _
  have hAC2 : dist A₁ C₁ ^ 2 =
      (R * (u - 1) / 2 - R * (1 - u₃) / 4) ^ 2 + (0 - R * Real.sqrt 3 * (1 - u₃) / 4) ^ 2 := by
    rw [hA₁', hC₁]
    exact coord_dist_sq he₁ he₂ he₁₂ _ _ _ _
  have hBC2 : dist B₁ C₁ ^ 2 =
      (R * (1 - v) / 4 - R * (1 - u₃) / 4) ^ 2 +
        (R * Real.sqrt 3 * (v - 1) / 4 - R * Real.sqrt 3 * (1 - u₃) / 4) ^ 2 := by
    rw [hB₁, hC₁]
    exact coord_dist_sq he₁ he₂ he₁₂ _ _ _ _
  have hw : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hden : u * v - u - v - 3 ≠ 0 := by
    intro h0
    have h1 : u * v = u + v + 3 := by linarith
    rw [h1] at hrel
    ring_nf at hrel
    have h2 : u + v = 0 := by linarith
    have h3 : u * v = 3 := by linarith
    have h4 : u ^ 2 + v ^ 2 = -6 := by linear_combination (u + v) * h2 - 2 * h3
    linarith [sq_nonneg u, sq_nonneg v]
  have hI1 : 4 * (u * v - u - v - 3) ^ 2 * (dist A₁ C₁ ^ 2 - dist A₁ B₁ ^ 2) =
      -R ^ 2 * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3) *
        (u ^ 2 * v - u ^ 2 + u * v ^ 2 - 4 * u * v + 3 * u - v ^ 2 + 3 * v + 6) := by
    rw [hAB2, hAC2]
    linear_combination
      (-R ^ 2 * (4 * u ^ 2 * v - 4 * u ^ 2 + u * u₃ * v * Real.sqrt 3 ^ 2 + u * u₃ * v -
        u * u₃ * Real.sqrt 3 ^ 2 - u * u₃ - u * v * Real.sqrt 3 ^ 2 - 9 * u * v +
        5 * u * Real.sqrt 3 ^ 2 - 3 * u - u₃ * v * Real.sqrt 3 ^ 2 - u₃ * v -
        3 * u₃ * Real.sqrt 3 ^ 2 - 3 * u₃ + 5 * v * Real.sqrt 3 ^ 2 + 9 * v +
        3 * Real.sqrt 3 ^ 2 + 15) / 4) * hrel +
      (-R ^ 2 * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3) *
        (u * v ^ 2 - 2 * u * v + 5 * u - v ^ 2 + 2 * v + 3) / 4) * hw
  have hI2 : 4 * (u * v - u - v - 3) ^ 2 * (dist B₁ C₁ ^ 2 - dist A₁ B₁ ^ 2) =
      -R ^ 2 * (u ^ 2 * v - u ^ 2 - 2 * u * v - 6 * u - 3 * v + 3) *
        (u ^ 2 * v - u ^ 2 + u * v ^ 2 - 4 * u * v + 3 * u - v ^ 2 + 3 * v + 6) := by
    rw [hAB2, hBC2]
    linear_combination
      (-R ^ 2 * (u * u₃ * v * Real.sqrt 3 ^ 2 + u * u₃ * v - u * u₃ * Real.sqrt 3 ^ 2 - u * u₃ +
        2 * u * v ^ 2 * Real.sqrt 3 ^ 2 - 2 * u * v ^ 2 - 5 * u * v * Real.sqrt 3 ^ 2 +
        3 * u * v + 7 * u * Real.sqrt 3 ^ 2 + 3 * u - u₃ * v * Real.sqrt 3 ^ 2 - u₃ * v -
        3 * u₃ * Real.sqrt 3 ^ 2 - 3 * u₃ - 2 * v ^ 2 * Real.sqrt 3 ^ 2 + 2 * v ^ 2 +
        v * Real.sqrt 3 ^ 2 + 9 * v + 9 * Real.sqrt 3 ^ 2 - 3) / 4) * hrel +
      (2 * R ^ 2 * (u + v) * (u * v ^ 2 - 2 * u * v + 3 * u - v ^ 2 + 3)) * hw
  have hI3 : 4 * (u * v - u - v - 3) * (dist B₁ C₁ ^ 2 - dist A₁ C₁ ^ 2) =
      -R ^ 2 * (u - v) *
        (u ^ 2 * v - u ^ 2 + u * v ^ 2 - 4 * u * v + 3 * u - v ^ 2 + 3 * v + 6) := by
    rw [hAC2, hBC2]
    linear_combination
      (R ^ 2 * (2 * u - v * Real.sqrt 3 ^ 2 + v + Real.sqrt 3 ^ 2 - 3) / 2) * hrel +
      (R ^ 2 * (v - 1) * (u * v ^ 2 - 2 * u * v + 9 * u - v ^ 2 + 6 * v + 3) / 4) * hw
  have hden4 : (4 : ℝ) * (u * v - u - v - 3) ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 hden)
  have hden4' : (4 : ℝ) * (u * v - u - v - 3) ≠ 0 := mul_ne_zero (by norm_num) hden
  have hsq1 : dist A₁ C₁ ^ 2 - dist A₁ B₁ ^ 2 ≠ 0 := by
    have hs : dist A₁ B₁ ^ 2 ≠ dist A₁ C₁ ^ 2 :=
      fun h => h₁ ((sq_eq_sq₀ dist_nonneg dist_nonneg).mp h)
    exact sub_ne_zero_of_ne hs.symm
  have hsq2 : dist B₁ C₁ ^ 2 - dist A₁ B₁ ^ 2 ≠ 0 := by
    have hs : dist A₁ B₁ ^ 2 ≠ dist B₁ C₁ ^ 2 :=
      fun h => h₂ ((sq_eq_sq₀ dist_nonneg dist_nonneg).mp h)
    exact sub_ne_zero_of_ne hs.symm
  have hsq3 : dist B₁ C₁ ^ 2 - dist A₁ C₁ ^ 2 ≠ 0 := by
    have hs : dist A₁ C₁ ^ 2 ≠ dist B₁ C₁ ^ 2 :=
      fun h => h₃ ((sq_eq_sq₀ dist_nonneg dist_nonneg).mp h)
    exact sub_ne_zero_of_ne hs.symm
  have hE1 : -R ^ 2 * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3) *
      (u ^ 2 * v - u ^ 2 + u * v ^ 2 - 4 * u * v + 3 * u - v ^ 2 + 3 * v + 6) ≠ 0 := by
    rw [← hI1]
    exact mul_ne_zero hden4 hsq1
  have hE2 : -R ^ 2 * (u ^ 2 * v - u ^ 2 - 2 * u * v - 6 * u - 3 * v + 3) *
      (u ^ 2 * v - u ^ 2 + u * v ^ 2 - 4 * u * v + 3 * u - v ^ 2 + 3 * v + 6) ≠ 0 := by
    rw [← hI2]
    exact mul_ne_zero hden4 hsq2
  have hE3 : -R ^ 2 * (u - v) *
      (u ^ 2 * v - u ^ 2 + u * v ^ 2 - 4 * u * v + 3 * u - v ^ 2 + 3 * v + 6) ≠ 0 := by
    rw [← hI3]
    exact mul_ne_zero hden4' hsq3
  have hdA : u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3 ≠ 0 :=
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hE1).1).2
  have hdB : u ^ 2 * v - u ^ 2 - 2 * u * v - 6 * u - 3 * v + 3 ≠ 0 :=
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hE2).1).2
  have huv : u ≠ v := by
    have h1 : u - v ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hE3).1).2
    exact sub_ne_zero.mp h1
  exact ⟨huv, hdA, hdB⟩

/- Self-contained algebraic lemmas for the main proof. -/

noncomputable def sigAd (u v : ℝ) : ℝ := (-24) * (v^2+3) * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3)
noncomputable def delAd (u v R : ℝ) : ℝ := 12 * R * (u+1) * (v^2+3) * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3)
noncomputable def epsAd (u v R : ℝ) : ℝ := (-4) * R * (v^2+3) * (u ^ 2 * v ^ 2 - 6 * u ^ 2 * v + 9 * u ^ 2 + 24 * u * v + 15 * v ^ 2 - 18 * v - 9) * Real.sqrt 3
noncomputable def phiAd (u v R : ℝ) : ℝ := (-12) * R^2 * (u-1) * (v^2+3) * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3)
noncomputable def sigBd (u v : ℝ) : ℝ := 24 * (u^2+3) * (u ^ 2 * v - u ^ 2 - 2 * u * v - 6 * u - 3 * v + 3)
noncomputable def delBd (u v R : ℝ) : ℝ := 12 * R * (u^2+3) * (u ^ 2 * v ^ 2 + 7 * u ^ 2 - 4 * u * v ^ 2 + 8 * u * v - 12 * u + 3 * v ^ 2 - 3)
noncomputable def epsBd (u v R : ℝ) : ℝ := (-4) * R * (u^2+3) * (u*v - 3*u - 3*v - 3) * (u*v + 3*u + 3*v - 3) * Real.sqrt 3
noncomputable def phiBd (u v R : ℝ) : ℝ := 12 * R^2 * (u^2+3) * (v-1) * (u ^ 2 * v - u ^ 2 - 2 * u * v - 6 * u - 3 * v + 3)
noncomputable def sigCd (u v : ℝ) : ℝ := 6 * (u-v) * (u*v - u - v - 3)^3
noncomputable def delCd (u v R : ℝ) : ℝ := 6 * R * (u*v - u - v - 3)^2 * (u ^ 2 * v ^ 2 - u ^ 2 * v + 2 * u ^ 2 - 2 * u * v ^ 2 - 6 * u + v ^ 2 - 3 * v)
noncomputable def epsCd (u v R : ℝ) : ℝ := (-2) * R * v * (u^2+3) * (v-3) * (u*v - u - v - 3)^2 * Real.sqrt 3
noncomputable def phiCd (u v R : ℝ) : ℝ := 12 * R^2 * (u-v) * (u+v) * (u*v - u - v - 3)^2
noncomputable def ald (u v R : ℝ) : ℝ := 288 * R * (u^2+3) * (v^2+3) * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3) * (u ^ 3 * v - u ^ 3 + u ^ 2 * v ^ 2 - u ^ 2 * v - 4 * u * v ^ 2 + 3 * u * v - 15 * u + 3 * v ^ 2 - 3 * v)
noncomputable def bed (u v R : ℝ) : ℝ := (-96) * R * (u^2+3) * (v^2+3) * (u ^ 4 * v ^ 3 - 7 * u ^ 4 * v ^ 2 + 15 * u ^ 4 * v - 9 * u ^ 4 + u ^ 3 * v ^ 4 - 4 * u ^ 3 * v ^ 3 + 18 * u ^ 3 * v ^ 2 + 12 * u ^ 3 * v - 27 * u ^ 3 - u ^ 2 * v ^ 4 - 18 * u ^ 2 * v ^ 3 - 54 * u ^ 2 * v + 9 * u ^ 2 - 9 * u * v ^ 4 + 12 * u * v ^ 3 + 54 * u * v ^ 2 + 108 * u * v + 27 * u + 9 * v ^ 4 + 9 * v ^ 3 + 63 * v ^ 2 - 81 * v) * Real.sqrt 3
noncomputable def gad (u v R : ℝ) : ℝ := (-288) * R^2 * (u-v) * (u^2+3) * (v^2+3) * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3) * (u ^ 2 * v - u ^ 2 - 2 * u * v - 6 * u - 3 * v + 3)
noncomputable def epsA2d (u v R : ℝ) : ℝ := 48 * R^2 * (v^2+3)^2 * (u ^ 2 * v ^ 2 - 6 * u ^ 2 * v + 9 * u ^ 2 + 24 * u * v + 15 * v ^ 2 - 18 * v - 9)^2
noncomputable def be2d (u v R : ℝ) : ℝ := 27648 * R^2 * (u^2+3)^2 * (v^2+3)^2 * (u ^ 4 * v ^ 3 - 7 * u ^ 4 * v ^ 2 + 15 * u ^ 4 * v - 9 * u ^ 4 + u ^ 3 * v ^ 4 - 4 * u ^ 3 * v ^ 3 + 18 * u ^ 3 * v ^ 2 + 12 * u ^ 3 * v - 27 * u ^ 3 - u ^ 2 * v ^ 4 - 18 * u ^ 2 * v ^ 3 - 54 * u ^ 2 * v + 9 * u ^ 2 - 9 * u * v ^ 4 + 12 * u * v ^ 3 + 54 * u * v ^ 2 + 108 * u * v + 27 * u + 9 * v ^ 4 + 9 * v ^ 3 + 63 * v ^ 2 - 81 * v)^2
noncomputable def beepsd (u v R : ℝ) : ℝ := 1152 * R^2 * (u^2+3) * (v^2+3)^2 * (u ^ 4 * v ^ 3 - 7 * u ^ 4 * v ^ 2 + 15 * u ^ 4 * v - 9 * u ^ 4 + u ^ 3 * v ^ 4 - 4 * u ^ 3 * v ^ 3 + 18 * u ^ 3 * v ^ 2 + 12 * u ^ 3 * v - 27 * u ^ 3 - u ^ 2 * v ^ 4 - 18 * u ^ 2 * v ^ 3 - 54 * u ^ 2 * v + 9 * u ^ 2 - 9 * u * v ^ 4 + 12 * u * v ^ 3 + 54 * u * v ^ 2 + 108 * u * v + 27 * u + 9 * v ^ 4 + 9 * v ^ 3 + 63 * v ^ 2 - 81 * v) * (u ^ 2 * v ^ 2 - 6 * u ^ 2 * v + 9 * u ^ 2 + 24 * u * v + 15 * v ^ 2 - 18 * v - 9)
noncomputable def nn0d (u v R : ℝ) : ℝ := 110592 * R^2 * (u^2+3)^3 * (v^2+3)^3 * (u ^ 6 * v ^ 4 - 8 * u ^ 6 * v ^ 3 + 22 * u ^ 6 * v ^ 2 - 24 * u ^ 6 * v + 9 * u ^ 6 + 2 * u ^ 5 * v ^ 5 - 16 * u ^ 5 * v ^ 4 + 32 * u ^ 5 * v ^ 3 + 12 * u ^ 5 * v ^ 2 - 66 * u ^ 5 * v + 36 * u ^ 5 + u ^ 4 * v ^ 6 - 16 * u ^ 4 * v ^ 5 + 36 * u ^ 4 * v ^ 4 + 132 * u ^ 4 * v ^ 3 - 351 * u ^ 4 * v ^ 2 + 108 * u ^ 4 * v + 90 * u ^ 4 - 8 * u ^ 3 * v ^ 6 + 32 * u ^ 3 * v ^ 5 + 132 * u ^ 3 * v ^ 4 - 696 * u ^ 3 * v ^ 3 + 72 * u ^ 3 * v ^ 2 + 792 * u ^ 3 * v - 324 * u ^ 3 + 22 * u ^ 2 * v ^ 6 + 12 * u ^ 2 * v ^ 5 - 351 * u ^ 2 * v ^ 4 + 72 * u ^ 2 * v ^ 3 + 1836 * u ^ 2 * v ^ 2 - 756 * u ^ 2 * v + 189 * u ^ 2 - 24 * u * v ^ 6 - 66 * u * v ^ 5 + 108 * u * v ^ 4 + 792 * u * v ^ 3 - 756 * u * v ^ 2 - 54 * u * v + 9 * v ^ 6 + 36 * v ^ 5 + 90 * v ^ 4 - 324 * v ^ 3 + 189 * v ^ 2)
noncomputable def trhod (u v R : ℝ) : ℝ := (-4608) * R^2 * (u^2+3)^2 * (v^2+3)^3 * (u ^ 4 * v ^ 3 - 7 * u ^ 4 * v ^ 2 + 15 * u ^ 4 * v - 9 * u ^ 4 + u ^ 3 * v ^ 4 - 10 * u ^ 3 * v ^ 3 + 24 * u ^ 3 * v ^ 2 - 6 * u ^ 3 * v - 9 * u ^ 3 - u ^ 2 * v ^ 4 + 6 * u ^ 2 * v ^ 3 + 36 * u ^ 2 * v ^ 2 - 54 * u ^ 2 * v + 45 * u ^ 2 - 9 * u * v ^ 4 + 30 * u * v ^ 3 - 108 * u * v ^ 2 + 18 * u * v - 27 * u + 9 * v ^ 4 - 27 * v ^ 3 - 9 * v ^ 2 + 27 * v)
noncomputable def Rtmp0d (u v R : ℝ) : ℝ := 192 * R^2 * (u^2+3) * (v^2+3)^3 * (u ^ 2 * v ^ 2 - 6 * u ^ 2 * v + 9 * u ^ 2 - 6 * u * v ^ 2 + 24 * u * v - 18 * u + 21 * v ^ 2 - 18 * v + 9)
noncomputable def sqNd (u v R : ℝ) : ℝ := (21233664 * R^4 * (u^2+3)^4 * (v^2+3)^6) * (12 * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3)^2 * (-(u ^ 4 * v ^ 3 - 7 * u ^ 4 * v ^ 2 + 15 * u ^ 4 * v - 9 * u ^ 4 + u ^ 3 * v ^ 4 - 13 * u ^ 3 * v ^ 3 + 45 * u ^ 3 * v ^ 2 - 51 * u ^ 3 * v + 18 * u ^ 3 - 7 * u ^ 2 * v ^ 4 + 45 * u ^ 2 * v ^ 3 - 90 * u ^ 2 * v ^ 2 + 45 * u ^ 2 * v - 9 * u ^ 2 + 15 * u * v ^ 4 - 51 * u * v ^ 3 + 45 * u * v ^ 2 - 9 * u * v - 9 * v ^ 4 + 18 * v ^ 3 - 9 * v ^ 2)))
noncomputable def dA2d (u₃ v : ℝ) : ℝ := u₃ * v - u₃ - v - 3
noncomputable def dB2d (u v u₃ : ℝ) : ℝ := 2 * (u * u₃ - u - u₃ - 3)
noncomputable def dC2d (u v : ℝ) : ℝ := 2 * (u * v - u - v - 3)
noncomputable def al2d (u v R : ℝ) : ℝ := (sigCd u v) * (delAd u v R) - (sigAd u v) * (delCd u v R)
noncomputable def be2pd (u v R : ℝ) : ℝ := (sigCd u v) * (epsAd u v R) - (sigAd u v) * (epsCd u v R)
noncomputable def ga2d (u v R : ℝ) : ℝ := (sigCd u v) * (phiAd u v R) - (sigAd u v) * (phiCd u v R)
noncomputable def Sd (u v R : ℝ) : ℝ := Real.sqrt ((sqNd u v R) * (sigAd u v) ^ 2) / (2 * (sigAd u v) ^ 2 * (nn0d u v R))
noncomputable def caxd (u v R : ℝ) : ℝ := -(delAd u v R) / (2 * (sigAd u v))
noncomputable def cayd (u v R : ℝ) : ℝ := -(epsAd u v R) / (2 * (sigAd u v))
noncomputable def ρ'd (u v R : ℝ) : ℝ := (trhod u v R) / (2 * (sigAd u v) * (nn0d u v R))
noncomputable def Mxd (u v R : ℝ) : ℝ := (caxd u v R) - (ρ'd u v R) * (ald u v R)
noncomputable def Myd (u v R : ℝ) : ℝ := (cayd u v R) - (ρ'd u v R) * (bed u v R)
noncomputable def P1xd (u v R : ℝ) : ℝ := (Mxd u v R) - (Sd u v R) * (bed u v R)
noncomputable def P1yd (u v R : ℝ) : ℝ := (Myd u v R) + (Sd u v R) * (ald u v R)
noncomputable def P2xd (u v R : ℝ) : ℝ := (Mxd u v R) + (Sd u v R) * (bed u v R)
noncomputable def P2yd (u v R : ℝ) : ℝ := (Myd u v R) - (Sd u v R) * (ald u v R)
noncomputable def RA2d (u v R : ℝ) : ℝ := (Rtmp0d u v R) / (4 * (sigAd u v) ^ 2)

lemma incAA (u v R : ℝ) : (sigAd u v) * ((R)^2 + (0)^2) + (delAd u v R) * (R) + (epsAd u v R) * (0) + (phiAd u v R) = 0 := by
  simp only [sigAd, delAd, epsAd, phiAd]
  set dA : ℝ := (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3) with hdA
  ring

lemma incAA1 (u v R : ℝ) : (sigAd u v) * ((R * (u - 1) / 2)^2 + (0)^2) + (delAd u v R) * (R * (u - 1) / 2) + (epsAd u v R) * (0) + (phiAd u v R) = 0 := by
  simp only [sigAd, delAd, epsAd, phiAd]
  set dA : ℝ := (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3) with hdA
  ring

lemma incAA2 (u v u₃ R : ℝ) (hw : (Real.sqrt 3 : ℝ)^2 = 3)
    (hrel : u₃ * (3 + u + v - u * v) = 3 - u * v - 3 * u - 3 * v) (hdenA2C : (u₃ * v - u₃ - v - 3) ≠ 0) :
    (sigAd u v) * (((-R * (u₃ * v - 2 * u₃ - 2 * v + 3)) / (u₃ * v - u₃ - v - 3))^2 + ((Real.sqrt 3 * R * (u₃ - v)) / (u₃ * v - u₃ - v - 3))^2) + (delAd u v R) * ((-R * (u₃ * v - 2 * u₃ - 2 * v + 3)) / (u₃ * v - u₃ - v - 3)) + (epsAd u v R) * ((Real.sqrt 3 * R * (u₃ - v)) / (u₃ * v - u₃ - v - 3)) + (phiAd u v R) = 0 := by
  simp only [sigAd, delAd, epsAd, phiAd]
  set D : ℝ := (u₃ * v - u₃ - v - 3) with hD
  have hdenD : D ≠ 0 := by rw [hD]; exact hdenA2C
  field_simp [hdenD]
  linear_combination (-12 * R^2 * (v^2+3) * (-2) * (v - 3) * (u*u₃*v^2 - 3*u*u₃ - 2*u*v^2 + u₃*v^2 - 6*u₃*v + 3*u₃ + 6*v)) * hrel + ((-4) * (v^2+3) * R^2 * (u₃ - v) * (u^2*u₃*v^3 - 7*u^2*u₃*v^2 + 15*u^2*u₃*v - 9*u^2*u₃ - u^2*v^3 + 3*u^2*v^2 + 9*u^2*v - 27*u^2 + 30*u*u₃*v^2 - 36*u*u₃*v - 18*u*u₃ - 6*u*v^3 - 12*u*v^2 - 54*u*v + 15*u₃*v^3 - 39*u₃*v^2 - 27*u₃*v + 27*u₃ - 9*v^3 + 9*v^2 + 45*v + 27)) * hw

lemma incBB (u v R : ℝ) (hw : (Real.sqrt 3 : ℝ)^2 = 3) : (sigBd u v) * ((-R / 2)^2 + (R * Real.sqrt 3 / 2)^2) + (delBd u v R) * (-R / 2) + (epsBd u v R) * (R * Real.sqrt 3 / 2) + (phiBd u v R) = 0 := by
  have hcore : (2*v+2) * (u ^ 2 * v - u ^ 2 - 2 * u * v - 6 * u - 3 * v + 3)
      = (u^2*v^2 + 7*u^2 - 4*u*v^2 + 8*u*v - 12*u + 3*v^2 - 3) + (u*v - 3*u - 3*v - 3)*(u*v + 3*u + 3*v - 3) := by ring
  simp only [sigBd, delBd, epsBd, phiBd]
  linear_combination (2 * R^2 * (u^2+3) * (3 * (u ^ 2 * v - u ^ 2 - 2 * u * v - 6 * u - 3 * v + 3) - (u*v - 3*u - 3*v - 3)*(u*v + 3*u + 3*v - 3))) * hw + (6 * R^2 * (u^2+3)) * hcore

lemma incBB1aux (u v R : ℝ) (hw : (Real.sqrt 3 : ℝ)^2 = 3) : (2) * ((sigBd u v) * ((R * (1 - v) / 4)^2 + (R * Real.sqrt 3 * (v - 1) / 4)^2) + (delBd u v R) * (R * (1 - v) / 4) + (epsBd u v R) * (R * Real.sqrt 3 * (v - 1) / 4) + (phiBd u v R)) = 0 := by
  simp only [sigBd, delBd, epsBd, phiBd]
  linear_combination (R^2 * (u^2+3) * (v - 1) * (u^2*v^2 - 6*u^2*v + 21*u^2 - 6*u*v^2 + 36*u*v + 18*u + 9*v^2 + 18*v - 27)) * hw

lemma incBB1 (u v R : ℝ) (hw : (Real.sqrt 3 : ℝ)^2 = 3) : (sigBd u v) * ((R * (1 - v) / 4)^2 + (R * Real.sqrt 3 * (v - 1) / 4)^2) + (delBd u v R) * (R * (1 - v) / 4) + (epsBd u v R) * (R * Real.sqrt 3 * (v - 1) / 4) + (phiBd u v R) = 0 := by
  have h := incBB1aux u v R hw
  rcases mul_eq_zero.1 h with h2 | h2
  · norm_num at h2
  · exact h2

lemma incBB2 (u v u₃ R : ℝ) (hw : (Real.sqrt 3 : ℝ)^2 = 3)
    (hrel : u₃ * (3 + u + v - u * v) = 3 - u * v - 3 * u - 3 * v) (hdenB2C : (2 * (u * u₃ - u - u₃ - 3)) ≠ 0) :
    (sigBd u v) * (((R * (u * u₃ - 5 * u + u₃ + 3)) / (2 * (u * u₃ - u - u₃ - 3)))^2 + ((-Real.sqrt 3 * R * (u - 3) * (u₃ - 1)) / (2 * (u * u₃ - u - u₃ - 3)))^2) + (delBd u v R) * ((R * (u * u₃ - 5 * u + u₃ + 3)) / (2 * (u * u₃ - u - u₃ - 3))) + (epsBd u v R) * ((-Real.sqrt 3 * R * (u - 3) * (u₃ - 1)) / (2 * (u * u₃ - u - u₃ - 3))) + (phiBd u v R) = 0 := by
  simp only [sigBd, delBd, epsBd, phiBd]
  set D : ℝ := (2 * (u * u₃ - u - u₃ - 3)) with hD
  have hdenD : D ≠ 0 := by rw [hD]; exact hdenB2C
  field_simp [hdenD]
  linear_combination ((-96) * R^2 * (u - 3) * (u^2+3) * (u^2*u₃*v + u^2*u₃ - 2*u^2*v - 6*u*u₃ + 6*u - 3*u₃*v + 3*u₃)) * hrel + (8 * R^2 * (u - 3) * (u^2+3) * (u₃ - 1) * (u^3*u₃*v^2 + 3*u^3*u₃*v - 12*u^3*u₃ - u^3*v^2 - 3*u^3*v + 12*u^3 - u^2*u₃*v^2 - 39*u^2*u₃*v - 3*u^2*v^2 + 39*u^2*v + 36*u^2 - 9*u*u₃*v^2 + 33*u*u₃*v + 72*u*u₃ + 9*u*v^2 + 63*u*v - 72*u + 9*u₃*v^2 + 27*u₃*v - 36*u₃ + 27*v^2 - 27*v)) * hw

lemma incCCaux (u v R : ℝ) (hw : (Real.sqrt 3 : ℝ)^2 = 3) : (2) * ((sigCd u v) * ((-R / 2)^2 + (-R * Real.sqrt 3 / 2)^2) + (delCd u v R) * (-R / 2) + (epsCd u v R) * (-R * Real.sqrt 3 / 2) + (phiCd u v R)) = 0 := by
  simp only [sigCd, delCd, epsCd, phiCd]
  linear_combination (R^2 * (u*v - u - v - 3)^2 * (2*u^2*v^2 - 3*u^2*v - 3*u^2 - 3*u*v^2 - 9*u + 9*v^2 - 9*v)) * hw

lemma incCC (u v R : ℝ) (hw : (Real.sqrt 3 : ℝ)^2 = 3) : (sigCd u v) * ((-R / 2)^2 + (-R * Real.sqrt 3 / 2)^2) + (delCd u v R) * (-R / 2) + (epsCd u v R) * (-R * Real.sqrt 3 / 2) + (phiCd u v R) = 0 := by
  have h := incCCaux u v R hw
  rcases mul_eq_zero.1 h with h2 | h2
  · norm_num at h2
  · exact h2

lemma incCC1aux (u v u₃ R : ℝ) (hw : (Real.sqrt 3 : ℝ)^2 = 3)
    (hrel : u₃ * (3 + u + v - u * v) = 3 - u * v - 3 * u - 3 * v) : (8) * ((sigCd u v) * ((R * (1 - u₃) / 4)^2 + (R * Real.sqrt 3 * (1 - u₃) / 4)^2) + (delCd u v R) * (R * (1 - u₃) / 4) + (epsCd u v R) * (R * Real.sqrt 3 * (1 - u₃) / 4) + (phiCd u v R)) = 0 := by
  simp only [sigCd, delCd, epsCd, phiCd]
  linear_combination (R^2 * (u₃ - 1) * (u*v - u - v - 3)^2 * (3*u^2*u₃*v - 3*u^2*u₃ + 4*u^2*v^2 - 15*u^2*v + 3*u^2 - 3*u*u₃*v^2 - 9*u*u₃ + 3*u*v^2 + 9*u + 3*u₃*v^2 + 9*u₃*v + 9*v^2 - 45*v)) * hw + ((-12) * R^2 * u^3*u₃*v^2 + 24 * R^2 * u^3*u₃*v - 12 * R^2 * u^3*u₃ + 36 * R^2 * u^3*v^2 - 72 * R^2 * u^3*v + 36 * R^2 * u^3 + 12 * R^2 * u^2*u₃*v^3 + 60 * R^2 * u^2*u₃*v - 72 * R^2 * u^2*u₃ - 36 * R^2 * u^2*v^3 - 180 * R^2 * u^2*v + 216 * R^2 * u^2 - 24 * R^2 * u*u₃*v^3 - 60 * R^2 * u*u₃*v^2 - 108 * R^2 * u*u₃ + 72 * R^2 * u*v^3 + 180 * R^2 * u*v^2 + 324 * R^2 * u + 12 * R^2 * u₃*v^3 + 72 * R^2 * u₃*v^2 + 108 * R^2 * u₃*v - 36 * R^2 * v^3 - 216 * R^2 * v^2 - 324 * R^2 * v) * hrel

lemma incCC1 (u v u₃ R : ℝ) (hw : (Real.sqrt 3 : ℝ)^2 = 3)
    (hrel : u₃ * (3 + u + v - u * v) = 3 - u * v - 3 * u - 3 * v) : (sigCd u v) * ((R * (1 - u₃) / 4)^2 + (R * Real.sqrt 3 * (1 - u₃) / 4)^2) + (delCd u v R) * (R * (1 - u₃) / 4) + (epsCd u v R) * (R * Real.sqrt 3 * (1 - u₃) / 4) + (phiCd u v R) = 0 := by
  have h := incCC1aux u v u₃ R hw hrel
  rcases mul_eq_zero.1 h with h2 | h2
  · norm_num at h2
  · exact h2

lemma incCC2 (u v u₃ R : ℝ) (hw : (Real.sqrt 3 : ℝ)^2 = 3)
    (_hrel : u₃ * (3 + u + v - u * v) = 3 - u * v - 3 * u - 3 * v) (hdenC2C : (2 * (u * v - u - v - 3)) ≠ 0) :
    (sigCd u v) * (((R * (u * v - 5 * u + v + 3)) / (2 * (u * v - u - v - 3)))^2 + ((Real.sqrt 3 * R * (u - 3) * (v - 1)) / (2 * (u * v - u - v - 3)))^2) + (delCd u v R) * ((R * (u * v - 5 * u + v + 3)) / (2 * (u * v - u - v - 3))) + (epsCd u v R) * ((Real.sqrt 3 * R * (u - 3) * (v - 1)) / (2 * (u * v - u - v - 3))) + (phiCd u v R) = 0 := by
  simp only [sigCd, delCd, epsCd, phiCd]
  set D : ℝ := (2 * (u * v - u - v - 3)) with hD
  have hdenD : D ≠ 0 := by rw [hD]; exact hdenC2C
  field_simp [hdenD]
  linear_combination ((-2) * R^2 * (u - 3) * (v - 1) * (u*v - u - v - 3)^3 * (2*u^2*v^2 - 9*u^2*v + 3*u^2 + 3*u*v^2 + 6*u*v - 9*u - 3*v^2 - 9*v)) * hw

lemma hepsA2eqL_aux (v R ep s : ℝ) (hw : s ^ 2 = 3) :
    ((-4) * R * (v^2+3) * ep * s)^2 = (48 * R^2 * (v^2+3)^2 * ep^2) := by
  linear_combination (16 * R^2 * (v^2+3)^2 * ep^2) * hw

lemma hepsA2eqL (u v R : ℝ) (hw : (Real.sqrt 3 : ℝ)^2 = 3) : ((-4) * R * (v^2+3) * (u ^ 2 * v ^ 2 - 6 * u ^ 2 * v + 9 * u ^ 2 + 24 * u * v + 15 * v ^ 2 - 18 * v - 9) * Real.sqrt 3)^2 = (48 * R^2 * (v^2+3)^2 * (u ^ 2 * v ^ 2 - 6 * u ^ 2 * v + 9 * u ^ 2 + 24 * u * v + 15 * v ^ 2 - 18 * v - 9)^2) := hepsA2eqL_aux v R _ _ hw

lemma hbe2eqL_aux (u v R q4 s : ℝ) (hw : s ^ 2 = 3) :
    ((-96) * R * (u^2+3) * (v^2+3) * q4 * s)^2 = (27648 * R^2 * (u^2+3)^2 * (v^2+3)^2 * q4^2) := by
  linear_combination (9216 * R^2 * (u^2+3)^2 * (v^2+3)^2 * q4^2) * hw

lemma hbe2eqL (u v R : ℝ) (hw : (Real.sqrt 3 : ℝ)^2 = 3) : ((-96) * R * (u^2+3) * (v^2+3) * (u ^ 4 * v ^ 3 - 7 * u ^ 4 * v ^ 2 + 15 * u ^ 4 * v - 9 * u ^ 4 + u ^ 3 * v ^ 4 - 4 * u ^ 3 * v ^ 3 + 18 * u ^ 3 * v ^ 2 + 12 * u ^ 3 * v - 27 * u ^ 3 - u ^ 2 * v ^ 4 - 18 * u ^ 2 * v ^ 3 - 54 * u ^ 2 * v + 9 * u ^ 2 - 9 * u * v ^ 4 + 12 * u * v ^ 3 + 54 * u * v ^ 2 + 108 * u * v + 27 * u + 9 * v ^ 4 + 9 * v ^ 3 + 63 * v ^ 2 - 81 * v) * Real.sqrt 3)^2 = (27648 * R^2 * (u^2+3)^2 * (v^2+3)^2 * (u ^ 4 * v ^ 3 - 7 * u ^ 4 * v ^ 2 + 15 * u ^ 4 * v - 9 * u ^ 4 + u ^ 3 * v ^ 4 - 4 * u ^ 3 * v ^ 3 + 18 * u ^ 3 * v ^ 2 + 12 * u ^ 3 * v - 27 * u ^ 3 - u ^ 2 * v ^ 4 - 18 * u ^ 2 * v ^ 3 - 54 * u ^ 2 * v + 9 * u ^ 2 - 9 * u * v ^ 4 + 12 * u * v ^ 3 + 54 * u * v ^ 2 + 108 * u * v + 27 * u + 9 * v ^ 4 + 9 * v ^ 3 + 63 * v ^ 2 - 81 * v)^2) := hbe2eqL_aux u v R _ _ hw

lemma hbeepseqL_aux (u v R q4 ep s : ℝ) (hw : s ^ 2 = 3) :
    ((-96) * R * (u^2+3) * (v^2+3) * q4 * s) * ((-4) * R * (v^2+3) * ep * s)
      = (1152 * R^2 * (u^2+3) * (v^2+3)^2 * q4 * ep) := by
  linear_combination (384 * R^2 * (u^2+3) * (v^2+3)^2 * q4 * ep) * hw

lemma hbeepseqL (u v R : ℝ) (hw : (Real.sqrt 3 : ℝ)^2 = 3) : ((-96) * R * (u^2+3) * (v^2+3) * (u ^ 4 * v ^ 3 - 7 * u ^ 4 * v ^ 2 + 15 * u ^ 4 * v - 9 * u ^ 4 + u ^ 3 * v ^ 4 - 4 * u ^ 3 * v ^ 3 + 18 * u ^ 3 * v ^ 2 + 12 * u ^ 3 * v - 27 * u ^ 3 - u ^ 2 * v ^ 4 - 18 * u ^ 2 * v ^ 3 - 54 * u ^ 2 * v + 9 * u ^ 2 - 9 * u * v ^ 4 + 12 * u * v ^ 3 + 54 * u * v ^ 2 + 108 * u * v + 27 * u + 9 * v ^ 4 + 9 * v ^ 3 + 63 * v ^ 2 - 81 * v) * Real.sqrt 3) * ((-4) * R * (v^2+3) * (u ^ 2 * v ^ 2 - 6 * u ^ 2 * v + 9 * u ^ 2 + 24 * u * v + 15 * v ^ 2 - 18 * v - 9) * Real.sqrt 3) = (1152 * R^2 * (u^2+3) * (v^2+3)^2 * (u ^ 4 * v ^ 3 - 7 * u ^ 4 * v ^ 2 + 15 * u ^ 4 * v - 9 * u ^ 4 + u ^ 3 * v ^ 4 - 4 * u ^ 3 * v ^ 3 + 18 * u ^ 3 * v ^ 2 + 12 * u ^ 3 * v - 27 * u ^ 3 - u ^ 2 * v ^ 4 - 18 * u ^ 2 * v ^ 3 - 54 * u ^ 2 * v + 9 * u ^ 2 - 9 * u * v ^ 4 + 12 * u * v ^ 3 + 54 * u * v ^ 2 + 108 * u * v + 27 * u + 9 * v ^ 4 + 9 * v ^ 3 + 63 * v ^ 2 - 81 * v) * (u ^ 2 * v ^ 2 - 6 * u ^ 2 * v + 9 * u ^ 2 + 24 * u * v + 15 * v ^ 2 - 18 * v - 9)) := hbeepseqL_aux u v R _ _ _ hw


lemma hF4bL (u v R : ℝ) : 3 * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3)^2 * (u ^ 3 * v - u ^ 3 + u ^ 2 * v ^ 2 - u ^ 2 * v - 4 * u * v ^ 2 + 3 * u * v - 15 * u + 3 * v ^ 2 - 3 * v)^2 + (u ^ 4 * v ^ 3 - 7 * u ^ 4 * v ^ 2 + 15 * u ^ 4 * v - 9 * u ^ 4 + u ^ 3 * v ^ 4 - 4 * u ^ 3 * v ^ 3 + 18 * u ^ 3 * v ^ 2 + 12 * u ^ 3 * v - 27 * u ^ 3 - u ^ 2 * v ^ 4 - 18 * u ^ 2 * v ^ 3 - 54 * u ^ 2 * v + 9 * u ^ 2 - 9 * u * v ^ 4 + 12 * u * v ^ 3 + 54 * u * v ^ 2 + 108 * u * v + 27 * u + 9 * v ^ 4 + 9 * v ^ 3 + 63 * v ^ 2 - 81 * v)^2 = 4 * (u^2+3) * (v^2+3) * (u ^ 6 * v ^ 4 - 8 * u ^ 6 * v ^ 3 + 22 * u ^ 6 * v ^ 2 - 24 * u ^ 6 * v + 9 * u ^ 6 + 2 * u ^ 5 * v ^ 5 - 16 * u ^ 5 * v ^ 4 + 32 * u ^ 5 * v ^ 3 + 12 * u ^ 5 * v ^ 2 - 66 * u ^ 5 * v + 36 * u ^ 5 + u ^ 4 * v ^ 6 - 16 * u ^ 4 * v ^ 5 + 36 * u ^ 4 * v ^ 4 + 132 * u ^ 4 * v ^ 3 - 351 * u ^ 4 * v ^ 2 + 108 * u ^ 4 * v + 90 * u ^ 4 - 8 * u ^ 3 * v ^ 6 + 32 * u ^ 3 * v ^ 5 + 132 * u ^ 3 * v ^ 4 - 696 * u ^ 3 * v ^ 3 + 72 * u ^ 3 * v ^ 2 + 792 * u ^ 3 * v - 324 * u ^ 3 + 22 * u ^ 2 * v ^ 6 + 12 * u ^ 2 * v ^ 5 - 351 * u ^ 2 * v ^ 4 + 72 * u ^ 2 * v ^ 3 + 1836 * u ^ 2 * v ^ 2 - 756 * u ^ 2 * v + 189 * u ^ 2 - 24 * u * v ^ 6 - 66 * u * v ^ 5 + 108 * u * v ^ 4 + 792 * u * v ^ 3 - 756 * u * v ^ 2 - 54 * u * v + 9 * v ^ 6 + 36 * v ^ 5 + 90 * v ^ 4 - 324 * v ^ 3 + 189 * v ^ 2) := by ring

lemma hnn0eqL_aux (u v R dA q3 q4 q6 : ℝ)
    (h4b : 3 * dA^2 * q3^2 + q4^2 = 4 * (u^2+3) * (v^2+3) * q6) :
    (288 * R * (u^2+3) * (v^2+3) * dA * q3)^2 + (27648 * R^2 * (u^2+3)^2 * (v^2+3)^2 * q4^2)
      = (110592 * R^2 * (u^2+3)^3 * (v^2+3)^3 * q6) := by
  linear_combination (27648 * R^2 * (u^2+3)^2 * (v^2+3)^2) * h4b

lemma hnn0eqL (u v R : ℝ) (h4b : 3 * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3)^2 * (u ^ 3 * v - u ^ 3 + u ^ 2 * v ^ 2 - u ^ 2 * v - 4 * u * v ^ 2 + 3 * u * v - 15 * u + 3 * v ^ 2 - 3 * v)^2 + (u ^ 4 * v ^ 3 - 7 * u ^ 4 * v ^ 2 + 15 * u ^ 4 * v - 9 * u ^ 4 + u ^ 3 * v ^ 4 - 4 * u ^ 3 * v ^ 3 + 18 * u ^ 3 * v ^ 2 + 12 * u ^ 3 * v - 27 * u ^ 3 - u ^ 2 * v ^ 4 - 18 * u ^ 2 * v ^ 3 - 54 * u ^ 2 * v + 9 * u ^ 2 - 9 * u * v ^ 4 + 12 * u * v ^ 3 + 54 * u * v ^ 2 + 108 * u * v + 27 * u + 9 * v ^ 4 + 9 * v ^ 3 + 63 * v ^ 2 - 81 * v)^2 = 4 * (u^2+3) * (v^2+3) * (u ^ 6 * v ^ 4 - 8 * u ^ 6 * v ^ 3 + 22 * u ^ 6 * v ^ 2 - 24 * u ^ 6 * v + 9 * u ^ 6 + 2 * u ^ 5 * v ^ 5 - 16 * u ^ 5 * v ^ 4 + 32 * u ^ 5 * v ^ 3 + 12 * u ^ 5 * v ^ 2 - 66 * u ^ 5 * v + 36 * u ^ 5 + u ^ 4 * v ^ 6 - 16 * u ^ 4 * v ^ 5 + 36 * u ^ 4 * v ^ 4 + 132 * u ^ 4 * v ^ 3 - 351 * u ^ 4 * v ^ 2 + 108 * u ^ 4 * v + 90 * u ^ 4 - 8 * u ^ 3 * v ^ 6 + 32 * u ^ 3 * v ^ 5 + 132 * u ^ 3 * v ^ 4 - 696 * u ^ 3 * v ^ 3 + 72 * u ^ 3 * v ^ 2 + 792 * u ^ 3 * v - 324 * u ^ 3 + 22 * u ^ 2 * v ^ 6 + 12 * u ^ 2 * v ^ 5 - 351 * u ^ 2 * v ^ 4 + 72 * u ^ 2 * v ^ 3 + 1836 * u ^ 2 * v ^ 2 - 756 * u ^ 2 * v + 189 * u ^ 2 - 24 * u * v ^ 6 - 66 * u * v ^ 5 + 108 * u * v ^ 4 + 792 * u * v ^ 3 - 756 * u * v ^ 2 - 54 * u * v + 9 * v ^ 6 + 36 * v ^ 5 + 90 * v ^ 4 - 324 * v ^ 3 + 189 * v ^ 2)) : (288 * R * (u^2+3) * (v^2+3) * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3) * (u ^ 3 * v - u ^ 3 + u ^ 2 * v ^ 2 - u ^ 2 * v - 4 * u * v ^ 2 + 3 * u * v - 15 * u + 3 * v ^ 2 - 3 * v))^2 + (27648 * R^2 * (u^2+3)^2 * (v^2+3)^2 * (u ^ 4 * v ^ 3 - 7 * u ^ 4 * v ^ 2 + 15 * u ^ 4 * v - 9 * u ^ 4 + u ^ 3 * v ^ 4 - 4 * u ^ 3 * v ^ 3 + 18 * u ^ 3 * v ^ 2 + 12 * u ^ 3 * v - 27 * u ^ 3 - u ^ 2 * v ^ 4 - 18 * u ^ 2 * v ^ 3 - 54 * u ^ 2 * v + 9 * u ^ 2 - 9 * u * v ^ 4 + 12 * u * v ^ 3 + 54 * u * v ^ 2 + 108 * u * v + 27 * u + 9 * v ^ 4 + 9 * v ^ 3 + 63 * v ^ 2 - 81 * v)^2) = (110592 * R^2 * (u^2+3)^3 * (v^2+3)^3 * (u ^ 6 * v ^ 4 - 8 * u ^ 6 * v ^ 3 + 22 * u ^ 6 * v ^ 2 - 24 * u ^ 6 * v + 9 * u ^ 6 + 2 * u ^ 5 * v ^ 5 - 16 * u ^ 5 * v ^ 4 + 32 * u ^ 5 * v ^ 3 + 12 * u ^ 5 * v ^ 2 - 66 * u ^ 5 * v + 36 * u ^ 5 + u ^ 4 * v ^ 6 - 16 * u ^ 4 * v ^ 5 + 36 * u ^ 4 * v ^ 4 + 132 * u ^ 4 * v ^ 3 - 351 * u ^ 4 * v ^ 2 + 108 * u ^ 4 * v + 90 * u ^ 4 - 8 * u ^ 3 * v ^ 6 + 32 * u ^ 3 * v ^ 5 + 132 * u ^ 3 * v ^ 4 - 696 * u ^ 3 * v ^ 3 + 72 * u ^ 3 * v ^ 2 + 792 * u ^ 3 * v - 324 * u ^ 3 + 22 * u ^ 2 * v ^ 6 + 12 * u ^ 2 * v ^ 5 - 351 * u ^ 2 * v ^ 4 + 72 * u ^ 2 * v ^ 3 + 1836 * u ^ 2 * v ^ 2 - 756 * u ^ 2 * v + 189 * u ^ 2 - 24 * u * v ^ 6 - 66 * u * v ^ 5 + 108 * u * v ^ 4 + 792 * u * v ^ 3 - 756 * u * v ^ 2 - 54 * u * v + 9 * v ^ 6 + 36 * v ^ 5 + 90 * v ^ 4 - 324 * v ^ 3 + 189 * v ^ 2)) := hnn0eqL_aux u v R _ _ _ _ h4b

lemma htrhoeqL (u v R : ℝ) : -((288 * R * (u^2+3) * (v^2+3) * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3) * (u ^ 3 * v - u ^ 3 + u ^ 2 * v ^ 2 - u ^ 2 * v - 4 * u * v ^ 2 + 3 * u * v - 15 * u + 3 * v ^ 2 - 3 * v)) * (12 * R * (u+1) * (v^2+3) * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3)) + (1152 * R^2 * (u^2+3) * (v^2+3)^2 * (u ^ 4 * v ^ 3 - 7 * u ^ 4 * v ^ 2 + 15 * u ^ 4 * v - 9 * u ^ 4 + u ^ 3 * v ^ 4 - 4 * u ^ 3 * v ^ 3 + 18 * u ^ 3 * v ^ 2 + 12 * u ^ 3 * v - 27 * u ^ 3 - u ^ 2 * v ^ 4 - 18 * u ^ 2 * v ^ 3 - 54 * u ^ 2 * v + 9 * u ^ 2 - 9 * u * v ^ 4 + 12 * u * v ^ 3 + 54 * u * v ^ 2 + 108 * u * v + 27 * u + 9 * v ^ 4 + 9 * v ^ 3 + 63 * v ^ 2 - 81 * v) * (u ^ 2 * v ^ 2 - 6 * u ^ 2 * v + 9 * u ^ 2 + 24 * u * v + 15 * v ^ 2 - 18 * v - 9))) + 2 * ((-24) * (v^2+3) * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3)) * ((-288) * R^2 * (u-v) * (u^2+3) * (v^2+3) * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3) * (u ^ 2 * v - u ^ 2 - 2 * u * v - 6 * u - 3 * v + 3)) = ((-4608) * R^2 * (u^2+3)^2 * (v^2+3)^3 * (u ^ 4 * v ^ 3 - 7 * u ^ 4 * v ^ 2 + 15 * u ^ 4 * v - 9 * u ^ 4 + u ^ 3 * v ^ 4 - 10 * u ^ 3 * v ^ 3 + 24 * u ^ 3 * v ^ 2 - 6 * u ^ 3 * v - 9 * u ^ 3 - u ^ 2 * v ^ 4 + 6 * u ^ 2 * v ^ 3 + 36 * u ^ 2 * v ^ 2 - 54 * u ^ 2 * v + 45 * u ^ 2 - 9 * u * v ^ 4 + 30 * u * v ^ 3 - 108 * u * v ^ 2 + 18 * u * v - 27 * u + 9 * v ^ 4 - 27 * v ^ 3 - 9 * v ^ 2 + 27 * v)) := by
  have core : (-3) * (u+1) * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3)^2 * (u ^ 3 * v - u ^ 3 + u ^ 2 * v ^ 2 - u ^ 2 * v - 4 * u * v ^ 2 + 3 * u * v - 15 * u + 3 * v ^ 2 - 3 * v)
      - (u ^ 4 * v ^ 3 - 7 * u ^ 4 * v ^ 2 + 15 * u ^ 4 * v - 9 * u ^ 4 + u ^ 3 * v ^ 4 - 4 * u ^ 3 * v ^ 3 + 18 * u ^ 3 * v ^ 2 + 12 * u ^ 3 * v - 27 * u ^ 3 - u ^ 2 * v ^ 4 - 18 * u ^ 2 * v ^ 3 - 54 * u ^ 2 * v + 9 * u ^ 2 - 9 * u * v ^ 4 + 12 * u * v ^ 3 + 54 * u * v ^ 2 + 108 * u * v + 27 * u + 9 * v ^ 4 + 9 * v ^ 3 + 63 * v ^ 2 - 81 * v) * (u ^ 2 * v ^ 2 - 6 * u ^ 2 * v + 9 * u ^ 2 + 24 * u * v + 15 * v ^ 2 - 18 * v - 9)
      + 12 * (u-v) * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3)^2 * (u ^ 2 * v - u ^ 2 - 2 * u * v - 6 * u - 3 * v + 3)
      = (-4) * (u^2+3) * (v^2+3) * (u ^ 4 * v ^ 3 - 7 * u ^ 4 * v ^ 2 + 15 * u ^ 4 * v - 9 * u ^ 4 + u ^ 3 * v ^ 4 - 10 * u ^ 3 * v ^ 3 + 24 * u ^ 3 * v ^ 2 - 6 * u ^ 3 * v - 9 * u ^ 3 - u ^ 2 * v ^ 4 + 6 * u ^ 2 * v ^ 3 + 36 * u ^ 2 * v ^ 2 - 54 * u ^ 2 * v + 45 * u ^ 2 - 9 * u * v ^ 4 + 30 * u * v ^ 3 - 108 * u * v ^ 2 + 18 * u * v - 27 * u + 9 * v ^ 4 - 27 * v ^ 3 - 9 * v ^ 2 + 27 * v) := by ring
  linear_combination (1152 * R^2 * (u^2+3) * (v^2+3)^2) * core

lemma hRtmp0eqL (u v R : ℝ) : (12 * R * (u+1) * (v^2+3) * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3))^2 + (48 * R^2 * (v^2+3)^2 * (u ^ 2 * v ^ 2 - 6 * u ^ 2 * v + 9 * u ^ 2 + 24 * u * v + 15 * v ^ 2 - 18 * v - 9)^2) - 4 * ((-24) * (v^2+3) * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3)) * ((-12) * R^2 * (u-1) * (v^2+3) * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3)) = (192 * R^2 * (u^2+3) * (v^2+3)^3 * (u ^ 2 * v ^ 2 - 6 * u ^ 2 * v + 9 * u ^ 2 - 6 * u * v ^ 2 + 24 * u * v - 18 * u + 21 * v ^ 2 - 18 * v + 9)) := by
  have core : 3 * (u+1)^2 * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3)^2 + (u ^ 2 * v ^ 2 - 6 * u ^ 2 * v + 9 * u ^ 2 + 24 * u * v + 15 * v ^ 2 - 18 * v - 9)^2 - 24 * (u-1) * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3)^2
      = 4 * (u^2+3) * (v^2+3) * (u ^ 2 * v ^ 2 - 6 * u ^ 2 * v + 9 * u ^ 2 - 6 * u * v ^ 2 + 24 * u * v - 18 * u + 21 * v ^ 2 - 18 * v + 9) := by ring
  linear_combination (48 * R^2 * (v^2+3)^2) * core

lemma hF4L (u v R : ℝ) : 12 * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3)^2 * (-(u ^ 4 * v ^ 3 - 7 * u ^ 4 * v ^ 2 + 15 * u ^ 4 * v - 9 * u ^ 4 + u ^ 3 * v ^ 4 - 13 * u ^ 3 * v ^ 3 + 45 * u ^ 3 * v ^ 2 - 51 * u ^ 3 * v + 18 * u ^ 3 - 7 * u ^ 2 * v ^ 4 + 45 * u ^ 2 * v ^ 3 - 90 * u ^ 2 * v ^ 2 + 45 * u ^ 2 * v - 9 * u ^ 2 + 15 * u * v ^ 4 - 51 * u * v ^ 3 + 45 * u * v ^ 2 - 9 * u * v - 9 * v ^ 4 + 18 * v ^ 3 - 9 * v ^ 2)) + (u ^ 4 * v ^ 3 - 7 * u ^ 4 * v ^ 2 + 15 * u ^ 4 * v - 9 * u ^ 4 + u ^ 3 * v ^ 4 - 10 * u ^ 3 * v ^ 3 + 24 * u ^ 3 * v ^ 2 - 6 * u ^ 3 * v - 9 * u ^ 3 - u ^ 2 * v ^ 4 + 6 * u ^ 2 * v ^ 3 + 36 * u ^ 2 * v ^ 2 - 54 * u ^ 2 * v + 45 * u ^ 2 - 9 * u * v ^ 4 + 30 * u * v ^ 3 - 108 * u * v ^ 2 + 18 * u * v - 27 * u + 9 * v ^ 4 - 27 * v ^ 3 - 9 * v ^ 2 + 27 * v)^2 = (u ^ 6 * v ^ 4 - 8 * u ^ 6 * v ^ 3 + 22 * u ^ 6 * v ^ 2 - 24 * u ^ 6 * v + 9 * u ^ 6 + 2 * u ^ 5 * v ^ 5 - 16 * u ^ 5 * v ^ 4 + 32 * u ^ 5 * v ^ 3 + 12 * u ^ 5 * v ^ 2 - 66 * u ^ 5 * v + 36 * u ^ 5 + u ^ 4 * v ^ 6 - 16 * u ^ 4 * v ^ 5 + 36 * u ^ 4 * v ^ 4 + 132 * u ^ 4 * v ^ 3 - 351 * u ^ 4 * v ^ 2 + 108 * u ^ 4 * v + 90 * u ^ 4 - 8 * u ^ 3 * v ^ 6 + 32 * u ^ 3 * v ^ 5 + 132 * u ^ 3 * v ^ 4 - 696 * u ^ 3 * v ^ 3 + 72 * u ^ 3 * v ^ 2 + 792 * u ^ 3 * v - 324 * u ^ 3 + 22 * u ^ 2 * v ^ 6 + 12 * u ^ 2 * v ^ 5 - 351 * u ^ 2 * v ^ 4 + 72 * u ^ 2 * v ^ 3 + 1836 * u ^ 2 * v ^ 2 - 756 * u ^ 2 * v + 189 * u ^ 2 - 24 * u * v ^ 6 - 66 * u * v ^ 5 + 108 * u * v ^ 4 + 792 * u * v ^ 3 - 756 * u * v ^ 2 - 54 * u * v + 9 * v ^ 6 + 36 * v ^ 5 + 90 * v ^ 4 - 324 * v ^ 3 + 189 * v ^ 2) * (u ^ 2 * v ^ 2 - 6 * u ^ 2 * v + 9 * u ^ 2 - 6 * u * v ^ 2 + 24 * u * v - 18 * u + 21 * v ^ 2 - 18 * v + 9) := by ring

lemma bigidL_aux (u v R dA q3b q4 q6 rt0 : ℝ)
    (h4 : 12 * dA^2 * (-q3b) + q4^2 = q6 * rt0) :
    ((21233664 * R^4 * (u^2+3)^4 * (v^2+3)^6) * (12 * dA^2 * (-q3b))) + ((-4608) * R^2 * (u^2+3)^2 * (v^2+3)^3 * q4)^2
      = (110592 * R^2 * (u^2+3)^3 * (v^2+3)^3 * q6) * (192 * R^2 * (u^2+3) * (v^2+3)^3 * rt0) := by
  linear_combination (21233664 * R^4 * (u^2+3)^4 * (v^2+3)^6) * h4

lemma bigidL (u v R : ℝ) (h4 : 12 * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3)^2 * (-(u ^ 4 * v ^ 3 - 7 * u ^ 4 * v ^ 2 + 15 * u ^ 4 * v - 9 * u ^ 4 + u ^ 3 * v ^ 4 - 13 * u ^ 3 * v ^ 3 + 45 * u ^ 3 * v ^ 2 - 51 * u ^ 3 * v + 18 * u ^ 3 - 7 * u ^ 2 * v ^ 4 + 45 * u ^ 2 * v ^ 3 - 90 * u ^ 2 * v ^ 2 + 45 * u ^ 2 * v - 9 * u ^ 2 + 15 * u * v ^ 4 - 51 * u * v ^ 3 + 45 * u * v ^ 2 - 9 * u * v - 9 * v ^ 4 + 18 * v ^ 3 - 9 * v ^ 2)) + (u ^ 4 * v ^ 3 - 7 * u ^ 4 * v ^ 2 + 15 * u ^ 4 * v - 9 * u ^ 4 + u ^ 3 * v ^ 4 - 10 * u ^ 3 * v ^ 3 + 24 * u ^ 3 * v ^ 2 - 6 * u ^ 3 * v - 9 * u ^ 3 - u ^ 2 * v ^ 4 + 6 * u ^ 2 * v ^ 3 + 36 * u ^ 2 * v ^ 2 - 54 * u ^ 2 * v + 45 * u ^ 2 - 9 * u * v ^ 4 + 30 * u * v ^ 3 - 108 * u * v ^ 2 + 18 * u * v - 27 * u + 9 * v ^ 4 - 27 * v ^ 3 - 9 * v ^ 2 + 27 * v)^2 = (u ^ 6 * v ^ 4 - 8 * u ^ 6 * v ^ 3 + 22 * u ^ 6 * v ^ 2 - 24 * u ^ 6 * v + 9 * u ^ 6 + 2 * u ^ 5 * v ^ 5 - 16 * u ^ 5 * v ^ 4 + 32 * u ^ 5 * v ^ 3 + 12 * u ^ 5 * v ^ 2 - 66 * u ^ 5 * v + 36 * u ^ 5 + u ^ 4 * v ^ 6 - 16 * u ^ 4 * v ^ 5 + 36 * u ^ 4 * v ^ 4 + 132 * u ^ 4 * v ^ 3 - 351 * u ^ 4 * v ^ 2 + 108 * u ^ 4 * v + 90 * u ^ 4 - 8 * u ^ 3 * v ^ 6 + 32 * u ^ 3 * v ^ 5 + 132 * u ^ 3 * v ^ 4 - 696 * u ^ 3 * v ^ 3 + 72 * u ^ 3 * v ^ 2 + 792 * u ^ 3 * v - 324 * u ^ 3 + 22 * u ^ 2 * v ^ 6 + 12 * u ^ 2 * v ^ 5 - 351 * u ^ 2 * v ^ 4 + 72 * u ^ 2 * v ^ 3 + 1836 * u ^ 2 * v ^ 2 - 756 * u ^ 2 * v + 189 * u ^ 2 - 24 * u * v ^ 6 - 66 * u * v ^ 5 + 108 * u * v ^ 4 + 792 * u * v ^ 3 - 756 * u * v ^ 2 - 54 * u * v + 9 * v ^ 6 + 36 * v ^ 5 + 90 * v ^ 4 - 324 * v ^ 3 + 189 * v ^ 2) * (u ^ 2 * v ^ 2 - 6 * u ^ 2 * v + 9 * u ^ 2 - 6 * u * v ^ 2 + 24 * u * v - 18 * u + 21 * v ^ 2 - 18 * v + 9)) : ((21233664 * R^4 * (u^2+3)^4 * (v^2+3)^6) * (12 * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3)^2 * (-(u ^ 4 * v ^ 3 - 7 * u ^ 4 * v ^ 2 + 15 * u ^ 4 * v - 9 * u ^ 4 + u ^ 3 * v ^ 4 - 13 * u ^ 3 * v ^ 3 + 45 * u ^ 3 * v ^ 2 - 51 * u ^ 3 * v + 18 * u ^ 3 - 7 * u ^ 2 * v ^ 4 + 45 * u ^ 2 * v ^ 3 - 90 * u ^ 2 * v ^ 2 + 45 * u ^ 2 * v - 9 * u ^ 2 + 15 * u * v ^ 4 - 51 * u * v ^ 3 + 45 * u * v ^ 2 - 9 * u * v - 9 * v ^ 4 + 18 * v ^ 3 - 9 * v ^ 2)))) + ((-4608) * R^2 * (u^2+3)^2 * (v^2+3)^3 * (u ^ 4 * v ^ 3 - 7 * u ^ 4 * v ^ 2 + 15 * u ^ 4 * v - 9 * u ^ 4 + u ^ 3 * v ^ 4 - 10 * u ^ 3 * v ^ 3 + 24 * u ^ 3 * v ^ 2 - 6 * u ^ 3 * v - 9 * u ^ 3 - u ^ 2 * v ^ 4 + 6 * u ^ 2 * v ^ 3 + 36 * u ^ 2 * v ^ 2 - 54 * u ^ 2 * v + 45 * u ^ 2 - 9 * u * v ^ 4 + 30 * u * v ^ 3 - 108 * u * v ^ 2 + 18 * u * v - 27 * u + 9 * v ^ 4 - 27 * v ^ 3 - 9 * v ^ 2 + 27 * v))^2 = (110592 * R^2 * (u^2+3)^3 * (v^2+3)^3 * (u ^ 6 * v ^ 4 - 8 * u ^ 6 * v ^ 3 + 22 * u ^ 6 * v ^ 2 - 24 * u ^ 6 * v + 9 * u ^ 6 + 2 * u ^ 5 * v ^ 5 - 16 * u ^ 5 * v ^ 4 + 32 * u ^ 5 * v ^ 3 + 12 * u ^ 5 * v ^ 2 - 66 * u ^ 5 * v + 36 * u ^ 5 + u ^ 4 * v ^ 6 - 16 * u ^ 4 * v ^ 5 + 36 * u ^ 4 * v ^ 4 + 132 * u ^ 4 * v ^ 3 - 351 * u ^ 4 * v ^ 2 + 108 * u ^ 4 * v + 90 * u ^ 4 - 8 * u ^ 3 * v ^ 6 + 32 * u ^ 3 * v ^ 5 + 132 * u ^ 3 * v ^ 4 - 696 * u ^ 3 * v ^ 3 + 72 * u ^ 3 * v ^ 2 + 792 * u ^ 3 * v - 324 * u ^ 3 + 22 * u ^ 2 * v ^ 6 + 12 * u ^ 2 * v ^ 5 - 351 * u ^ 2 * v ^ 4 + 72 * u ^ 2 * v ^ 3 + 1836 * u ^ 2 * v ^ 2 - 756 * u ^ 2 * v + 189 * u ^ 2 - 24 * u * v ^ 6 - 66 * u * v ^ 5 + 108 * u * v ^ 4 + 792 * u * v ^ 3 - 756 * u * v ^ 2 - 54 * u * v + 9 * v ^ 6 + 36 * v ^ 5 + 90 * v ^ 4 - 324 * v ^ 3 + 189 * v ^ 2)) * (192 * R^2 * (u^2+3) * (v^2+3)^3 * (u ^ 2 * v ^ 2 - 6 * u ^ 2 * v + 9 * u ^ 2 - 6 * u * v ^ 2 + 24 * u * v - 18 * u + 21 * v ^ 2 - 18 * v + 9)) := bigidL_aux u v R _ _ _ _ _ h4

lemma hradBL_corex (u v : ℝ) : (u ^ 2 * v - u ^ 2 - 2 * u * v - 6 * u - 3 * v + 3) * (u + 1) + (u^2*v^2 + 7*u^2 - 4*u*v^2 + 8*u*v - 12*u + 3*v^2 - 3)
    = (u^3*v - u^3 + u^2*v^2 - u^2*v - 4*u*v^2 + 3*u*v - 15*u + 3*v^2 - 3*v) := by ring

lemma hradBL_corey (u v : ℝ) : (u ^ 2 * v - u ^ 2 - 2 * u * v - 6 * u - 3 * v + 3) * (u ^ 2 * v ^ 2 - 6 * u ^ 2 * v + 9 * u ^ 2 + 24 * u * v + 15 * v ^ 2 - 18 * v - 9)
    + (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3) * (u*v - 3*u - 3*v - 3) * (u*v + 3*u + 3*v - 3)
    = (u ^ 4 * v ^ 3 - 7 * u ^ 4 * v ^ 2 + 15 * u ^ 4 * v - 9 * u ^ 4 + u ^ 3 * v ^ 4 - 4 * u ^ 3 * v ^ 3 + 18 * u ^ 3 * v ^ 2 + 12 * u ^ 3 * v - 27 * u ^ 3 - u ^ 2 * v ^ 4 - 18 * u ^ 2 * v ^ 3 - 54 * u ^ 2 * v + 9 * u ^ 2 - 9 * u * v ^ 4 + 12 * u * v ^ 3 + 54 * u * v ^ 2 + 108 * u * v + 27 * u + 9 * v ^ 4 + 9 * v ^ 3 + 63 * v ^ 2 - 81 * v) := by ring

lemma hradBL_aux (u v R dA dB : ℝ)
    (corex : dB * (u + 1) + (u^2*v^2 + 7*u^2 - 4*u*v^2 + 8*u*v - 12*u + 3*v^2 - 3)
      = (u^3*v - u^3 + u^2*v^2 - u^2*v - 4*u*v^2 + 3*u*v - 15*u + 3*v^2 - 3*v))
    (corey : dB * (u ^ 2 * v ^ 2 - 6 * u ^ 2 * v + 9 * u ^ 2 + 24 * u * v + 15 * v ^ 2 - 18 * v - 9)
      + dA * (u*v - 3*u - 3*v - 3) * (u*v + 3*u + 3*v - 3)
      = (u ^ 4 * v ^ 3 - 7 * u ^ 4 * v ^ 2 + 15 * u ^ 4 * v - 9 * u ^ 4 + u ^ 3 * v ^ 4 - 4 * u ^ 3 * v ^ 3 + 18 * u ^ 3 * v ^ 2 + 12 * u ^ 3 * v - 27 * u ^ 3 - u ^ 2 * v ^ 4 - 18 * u ^ 2 * v ^ 3 - 54 * u ^ 2 * v + 9 * u ^ 2 - 9 * u * v ^ 4 + 12 * u * v ^ 3 + 54 * u * v ^ 2 + 108 * u * v + 27 * u + 9 * v ^ 4 + 9 * v ^ 3 + 63 * v ^ 2 - 81 * v)) (x y : ℝ) : (24 * (u^2+3) * dB) * (((-24) * (v^2+3) * dA) * (x^2+y^2) + (12 * R * (u+1) * (v^2+3) * dA) * x + ((-4) * R * (v^2+3) * (u ^ 2 * v ^ 2 - 6 * u ^ 2 * v + 9 * u ^ 2 + 24 * u * v + 15 * v ^ 2 - 18 * v - 9) * Real.sqrt 3) * y + ((-12) * R^2 * (u-1) * (v^2+3) * dA)) - ((-24) * (v^2+3) * dA) * ((24 * (u^2+3) * dB) * (x^2+y^2) + (12 * R * (u^2+3) * (u ^ 2 * v ^ 2 + 7 * u ^ 2 - 4 * u * v ^ 2 + 8 * u * v - 12 * u + 3 * v ^ 2 - 3)) * x + ((-4) * R * (u^2+3) * (u*v - 3*u - 3*v - 3) * (u*v + 3*u + 3*v - 3) * Real.sqrt 3) * y + (12 * R^2 * (u^2+3) * (v-1) * dB)) = (288 * R * (u^2+3) * (v^2+3) * dA * (u ^ 3 * v - u ^ 3 + u ^ 2 * v ^ 2 - u ^ 2 * v - 4 * u * v ^ 2 + 3 * u * v - 15 * u + 3 * v ^ 2 - 3 * v)) * x + ((-96) * R * (u^2+3) * (v^2+3) * (u ^ 4 * v ^ 3 - 7 * u ^ 4 * v ^ 2 + 15 * u ^ 4 * v - 9 * u ^ 4 + u ^ 3 * v ^ 4 - 4 * u ^ 3 * v ^ 3 + 18 * u ^ 3 * v ^ 2 + 12 * u ^ 3 * v - 27 * u ^ 3 - u ^ 2 * v ^ 4 - 18 * u ^ 2 * v ^ 3 - 54 * u ^ 2 * v + 9 * u ^ 2 - 9 * u * v ^ 4 + 12 * u * v ^ 3 + 54 * u * v ^ 2 + 108 * u * v + 27 * u + 9 * v ^ 4 + 9 * v ^ 3 + 63 * v ^ 2 - 81 * v) * Real.sqrt 3) * y + ((-288) * R^2 * (u-v) * (u^2+3) * (v^2+3) * dA * dB) := by
  linear_combination (288 * R * (u^2+3) * (v^2+3) * dA) * corex * x + ((-96) * R * (u^2+3) * (v^2+3) * Real.sqrt 3) * corey * y

lemma hradBL (u v R : ℝ) (x y : ℝ) : (24 * (u^2+3) * (u ^ 2 * v - u ^ 2 - 2 * u * v - 6 * u - 3 * v + 3)) * (((-24) * (v^2+3) * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3)) * (x^2+y^2) + (12 * R * (u+1) * (v^2+3) * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3)) * x + ((-4) * R * (v^2+3) * (u ^ 2 * v ^ 2 - 6 * u ^ 2 * v + 9 * u ^ 2 + 24 * u * v + 15 * v ^ 2 - 18 * v - 9) * Real.sqrt 3) * y + ((-12) * R^2 * (u-1) * (v^2+3) * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3))) - ((-24) * (v^2+3) * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3)) * ((24 * (u^2+3) * (u ^ 2 * v - u ^ 2 - 2 * u * v - 6 * u - 3 * v + 3)) * (x^2+y^2) + (12 * R * (u^2+3) * (u ^ 2 * v ^ 2 + 7 * u ^ 2 - 4 * u * v ^ 2 + 8 * u * v - 12 * u + 3 * v ^ 2 - 3)) * x + ((-4) * R * (u^2+3) * (u*v - 3*u - 3*v - 3) * (u*v + 3*u + 3*v - 3) * Real.sqrt 3) * y + (12 * R^2 * (u^2+3) * (v-1) * (u ^ 2 * v - u ^ 2 - 2 * u * v - 6 * u - 3 * v + 3))) = (288 * R * (u^2+3) * (v^2+3) * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3) * (u ^ 3 * v - u ^ 3 + u ^ 2 * v ^ 2 - u ^ 2 * v - 4 * u * v ^ 2 + 3 * u * v - 15 * u + 3 * v ^ 2 - 3 * v)) * x + ((-96) * R * (u^2+3) * (v^2+3) * (u ^ 4 * v ^ 3 - 7 * u ^ 4 * v ^ 2 + 15 * u ^ 4 * v - 9 * u ^ 4 + u ^ 3 * v ^ 4 - 4 * u ^ 3 * v ^ 3 + 18 * u ^ 3 * v ^ 2 + 12 * u ^ 3 * v - 27 * u ^ 3 - u ^ 2 * v ^ 4 - 18 * u ^ 2 * v ^ 3 - 54 * u ^ 2 * v + 9 * u ^ 2 - 9 * u * v ^ 4 + 12 * u * v ^ 3 + 54 * u * v ^ 2 + 108 * u * v + 27 * u + 9 * v ^ 4 + 9 * v ^ 3 + 63 * v ^ 2 - 81 * v) * Real.sqrt 3) * y + ((-288) * R^2 * (u-v) * (u^2+3) * (v^2+3) * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3) * (u ^ 2 * v - u ^ 2 - 2 * u * v - 6 * u - 3 * v + 3)) := hradBL_aux u v R (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3) (u ^ 2 * v - u ^ 2 - 2 * u * v - 6 * u - 3 * v + 3) (hradBL_corex u v) (hradBL_corey u v) x y

lemma hradCL_aux (u v R dA w : ℝ) (x y : ℝ) : (6 * (u-v) * w^3) * (((-24) * (v^2+3) * dA) * (x^2+y^2) + (12 * R * (u+1) * (v^2+3) * dA) * x + ((-4) * R * (v^2+3) * (u ^ 2 * v ^ 2 - 6 * u ^ 2 * v + 9 * u ^ 2 + 24 * u * v + 15 * v ^ 2 - 18 * v - 9) * Real.sqrt 3) * y + ((-12) * R^2 * (u-1) * (v^2+3) * dA)) - ((-24) * (v^2+3) * dA) * ((6 * (u-v) * w^3) * (x^2+y^2) + (6 * R * w^2 * (u ^ 2 * v ^ 2 - u ^ 2 * v + 2 * u ^ 2 - 2 * u * v ^ 2 - 6 * u + v ^ 2 - 3 * v)) * x + ((-2) * R * v * (u^2+3) * (v-3) * w^2 * Real.sqrt 3) * y + (12 * R^2 * (u-v) * (u+v) * w^2)) = ((6 * (u-v) * w^3) * (12 * R * (u+1) * (v^2+3) * dA) - ((-24) * (v^2+3) * dA) * (6 * R * w^2 * (u ^ 2 * v ^ 2 - u ^ 2 * v + 2 * u ^ 2 - 2 * u * v ^ 2 - 6 * u + v ^ 2 - 3 * v))) * x + ((6 * (u-v) * w^3) * ((-4) * R * (v^2+3) * (u ^ 2 * v ^ 2 - 6 * u ^ 2 * v + 9 * u ^ 2 + 24 * u * v + 15 * v ^ 2 - 18 * v - 9) * Real.sqrt 3) - ((-24) * (v^2+3) * dA) * ((-2) * R * v * (u^2+3) * (v-3) * w^2 * Real.sqrt 3)) * y + ((6 * (u-v) * w^3) * ((-12) * R^2 * (u-1) * (v^2+3) * dA) - ((-24) * (v^2+3) * dA) * (12 * R^2 * (u-v) * (u+v) * w^2)) := by ring

lemma hradCL (u v R : ℝ) (x y : ℝ) : (6 * (u-v) * (u*v - u - v - 3)^3) * (((-24) * (v^2+3) * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3)) * (x^2+y^2) + (12 * R * (u+1) * (v^2+3) * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3)) * x + ((-4) * R * (v^2+3) * (u ^ 2 * v ^ 2 - 6 * u ^ 2 * v + 9 * u ^ 2 + 24 * u * v + 15 * v ^ 2 - 18 * v - 9) * Real.sqrt 3) * y + ((-12) * R^2 * (u-1) * (v^2+3) * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3))) - ((-24) * (v^2+3) * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3)) * ((6 * (u-v) * (u*v - u - v - 3)^3) * (x^2+y^2) + (6 * R * (u*v - u - v - 3)^2 * (u ^ 2 * v ^ 2 - u ^ 2 * v + 2 * u ^ 2 - 2 * u * v ^ 2 - 6 * u + v ^ 2 - 3 * v)) * x + ((-2) * R * v * (u^2+3) * (v-3) * (u*v - u - v - 3)^2 * Real.sqrt 3) * y + (12 * R^2 * (u-v) * (u+v) * (u*v - u - v - 3)^2)) = ((6 * (u-v) * (u*v - u - v - 3)^3) * (12 * R * (u+1) * (v^2+3) * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3)) - ((-24) * (v^2+3) * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3)) * (6 * R * (u*v - u - v - 3)^2 * (u ^ 2 * v ^ 2 - u ^ 2 * v + 2 * u ^ 2 - 2 * u * v ^ 2 - 6 * u + v ^ 2 - 3 * v))) * x + ((6 * (u-v) * (u*v - u - v - 3)^3) * ((-4) * R * (v^2+3) * (u ^ 2 * v ^ 2 - 6 * u ^ 2 * v + 9 * u ^ 2 + 24 * u * v + 15 * v ^ 2 - 18 * v - 9) * Real.sqrt 3) - ((-24) * (v^2+3) * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3)) * ((-2) * R * v * (u^2+3) * (v-3) * (u*v - u - v - 3)^2 * Real.sqrt 3)) * y + ((6 * (u-v) * (u*v - u - v - 3)^3) * ((-12) * R^2 * (u-1) * (v^2+3) * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3)) - ((-24) * (v^2+3) * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3)) * (12 * R^2 * (u-v) * (u+v) * (u*v - u - v - 3)^2)) := hradCL_aux u v R (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3) (u*v - u - v - 3) x y
lemma hcoaxxL_aux (u v R dA : ℝ) : 4 * (u^2+3) * ((6 * (u-v) * (u*v - u - v - 3)^3) * (12 * R * (u+1) * (v^2+3) * dA) - ((-24) * (v^2+3) * dA) * (6 * R * (u*v - u - v - 3)^2 * (u ^ 2 * v ^ 2 - u ^ 2 * v + 2 * u ^ 2 - 2 * u * v ^ 2 - 6 * u + v ^ 2 - 3 * v))) = (u*v - u - v - 3)^2 * ((288 * R * (u^2+3) * (v^2+3) * dA * (u ^ 3 * v - u ^ 3 + u ^ 2 * v ^ 2 - u ^ 2 * v - 4 * u * v ^ 2 + 3 * u * v - 15 * u + 3 * v ^ 2 - 3 * v))) := by
  have h1 : (u - v) * (u*v - u - v - 3) * (u + 1) + 2 * (u^2*v^2 - u^2*v + 2*u^2 - 2*u*v^2 - 6*u + v^2 - 3*v)
      = (u^3*v - u^3 + u^2*v^2 - u^2*v - 4*u*v^2 + 3*u*v - 15*u + 3*v^2 - 3*v) := by ring
  linear_combination (288 * R * (u^2+3) * (v^2+3) * dA * (u*v - u - v - 3)^2) * h1

lemma hcoaxxL (u v R : ℝ) : 4 * (u^2+3) * ((6 * (u-v) * (u*v - u - v - 3)^3) * (12 * R * (u+1) * (v^2+3) * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3)) - ((-24) * (v^2+3) * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3)) * (6 * R * (u*v - u - v - 3)^2 * (u ^ 2 * v ^ 2 - u ^ 2 * v + 2 * u ^ 2 - 2 * u * v ^ 2 - 6 * u + v ^ 2 - 3 * v))) = (u*v - u - v - 3)^2 * ((288 * R * (u^2+3) * (v^2+3) * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3) * (u ^ 3 * v - u ^ 3 + u ^ 2 * v ^ 2 - u ^ 2 * v - 4 * u * v ^ 2 + 3 * u * v - 15 * u + 3 * v ^ 2 - 3 * v))) := hcoaxxL_aux u v R (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3)

lemma hcoaxyL_core (u v : ℝ) : (u - v) * (u*v - u - v - 3) * (u ^ 2 * v ^ 2 - 6 * u ^ 2 * v + 9 * u ^ 2 + 24 * u * v + 15 * v ^ 2 - 18 * v - 9)
    + 2 * v * (u^2+3) * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3) * (v - 3)
    = (u ^ 4 * v ^ 3 - 7 * u ^ 4 * v ^ 2 + 15 * u ^ 4 * v - 9 * u ^ 4 + u ^ 3 * v ^ 4 - 4 * u ^ 3 * v ^ 3 + 18 * u ^ 3 * v ^ 2 + 12 * u ^ 3 * v - 27 * u ^ 3 - u ^ 2 * v ^ 4 - 18 * u ^ 2 * v ^ 3 - 54 * u ^ 2 * v + 9 * u ^ 2 - 9 * u * v ^ 4 + 12 * u * v ^ 3 + 54 * u * v ^ 2 + 108 * u * v + 27 * u + 9 * v ^ 4 + 9 * v ^ 3 + 63 * v ^ 2 - 81 * v) := by ring

lemma hcoaxyL_aux (u v R dA : ℝ)
    (h1 : (u - v) * (u*v - u - v - 3) * (u ^ 2 * v ^ 2 - 6 * u ^ 2 * v + 9 * u ^ 2 + 24 * u * v + 15 * v ^ 2 - 18 * v - 9)
      + 2 * v * (u^2+3) * dA * (v - 3)
      = (u ^ 4 * v ^ 3 - 7 * u ^ 4 * v ^ 2 + 15 * u ^ 4 * v - 9 * u ^ 4 + u ^ 3 * v ^ 4 - 4 * u ^ 3 * v ^ 3 + 18 * u ^ 3 * v ^ 2 + 12 * u ^ 3 * v - 27 * u ^ 3 - u ^ 2 * v ^ 4 - 18 * u ^ 2 * v ^ 3 - 54 * u ^ 2 * v + 9 * u ^ 2 - 9 * u * v ^ 4 + 12 * u * v ^ 3 + 54 * u * v ^ 2 + 108 * u * v + 27 * u + 9 * v ^ 4 + 9 * v ^ 3 + 63 * v ^ 2 - 81 * v)) : 4 * (u^2+3) * ((6 * (u-v) * (u*v - u - v - 3)^3) * ((-4) * R * (v^2+3) * (u ^ 2 * v ^ 2 - 6 * u ^ 2 * v + 9 * u ^ 2 + 24 * u * v + 15 * v ^ 2 - 18 * v - 9) * Real.sqrt 3) - ((-24) * (v^2+3) * dA) * ((-2) * R * v * (u^2+3) * (v-3) * (u*v - u - v - 3)^2 * Real.sqrt 3)) = (u*v - u - v - 3)^2 * (((-96) * R * (u^2+3) * (v^2+3) * (u ^ 4 * v ^ 3 - 7 * u ^ 4 * v ^ 2 + 15 * u ^ 4 * v - 9 * u ^ 4 + u ^ 3 * v ^ 4 - 4 * u ^ 3 * v ^ 3 + 18 * u ^ 3 * v ^ 2 + 12 * u ^ 3 * v - 27 * u ^ 3 - u ^ 2 * v ^ 4 - 18 * u ^ 2 * v ^ 3 - 54 * u ^ 2 * v + 9 * u ^ 2 - 9 * u * v ^ 4 + 12 * u * v ^ 3 + 54 * u * v ^ 2 + 108 * u * v + 27 * u + 9 * v ^ 4 + 9 * v ^ 3 + 63 * v ^ 2 - 81 * v) * Real.sqrt 3)) := by
  linear_combination ((-96) * R * (u^2+3) * (v^2+3) * Real.sqrt 3 * (u*v - u - v - 3)^2) * h1

lemma hcoaxyL (u v R : ℝ) : 4 * (u^2+3) * ((6 * (u-v) * (u*v - u - v - 3)^3) * ((-4) * R * (v^2+3) * (u ^ 2 * v ^ 2 - 6 * u ^ 2 * v + 9 * u ^ 2 + 24 * u * v + 15 * v ^ 2 - 18 * v - 9) * Real.sqrt 3) - ((-24) * (v^2+3) * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3)) * ((-2) * R * v * (u^2+3) * (v-3) * (u*v - u - v - 3)^2 * Real.sqrt 3)) = (u*v - u - v - 3)^2 * (((-96) * R * (u^2+3) * (v^2+3) * (u ^ 4 * v ^ 3 - 7 * u ^ 4 * v ^ 2 + 15 * u ^ 4 * v - 9 * u ^ 4 + u ^ 3 * v ^ 4 - 4 * u ^ 3 * v ^ 3 + 18 * u ^ 3 * v ^ 2 + 12 * u ^ 3 * v - 27 * u ^ 3 - u ^ 2 * v ^ 4 - 18 * u ^ 2 * v ^ 3 - 54 * u ^ 2 * v + 9 * u ^ 2 - 9 * u * v ^ 4 + 12 * u * v ^ 3 + 54 * u * v ^ 2 + 108 * u * v + 27 * u + 9 * v ^ 4 + 9 * v ^ 3 + 63 * v ^ 2 - 81 * v) * Real.sqrt 3)) := hcoaxyL_aux u v R (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3) (hcoaxyL_core u v)

lemma hcoaxcL_core (u v : ℝ) : (u - 1) * (u*v - u - v - 3) - 4 * (u + v) = (u ^ 2 * v - u ^ 2 - 2 * u * v - 6 * u - 3 * v + 3) := by ring

lemma hcoaxcL_aux (u v R dA dB : ℝ)
    (h1 : (u - 1) * (u*v - u - v - 3) - 4 * (u + v) = dB) : 4 * (u^2+3) * ((6 * (u-v) * (u*v - u - v - 3)^3) * ((-12) * R^2 * (u-1) * (v^2+3) * dA) - ((-24) * (v^2+3) * dA) * (12 * R^2 * (u-v) * (u+v) * (u*v - u - v - 3)^2)) = (u*v - u - v - 3)^2 * (((-288) * R^2 * (u-v) * (u^2+3) * (v^2+3) * dA * dB)) := by
  linear_combination ((-288) * R^2 * (u^2+3) * (v^2+3) * dA * (u - v) * (u*v - u - v - 3)^2) * h1

lemma hcoaxcL (u v R : ℝ) : 4 * (u^2+3) * ((6 * (u-v) * (u*v - u - v - 3)^3) * ((-12) * R^2 * (u-1) * (v^2+3) * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3)) - ((-24) * (v^2+3) * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3)) * (12 * R^2 * (u-v) * (u+v) * (u*v - u - v - 3)^2)) = (u*v - u - v - 3)^2 * (((-288) * R^2 * (u-v) * (u^2+3) * (v^2+3) * (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3) * (u ^ 2 * v - u ^ 2 - 2 * u * v - 6 * u - 3 * v + 3))) := hcoaxcL_aux u v R (u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3) (u ^ 2 * v - u ^ 2 - 2 * u * v - 6 * u - 3 * v + 3) (hcoaxcL_core u v)


lemma q3negL {u v u₃ : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1)
    (hu₃0 : 0 < u₃) (hrel : u₃ * (3 + u + v - u * v) = 3 - u * v - 3 * u - 3 * v) :
    (u ^ 4 * v ^ 3 - 7 * u ^ 4 * v ^ 2 + 15 * u ^ 4 * v - 9 * u ^ 4 + u ^ 3 * v ^ 4 - 13 * u ^ 3 * v ^ 3 + 45 * u ^ 3 * v ^ 2 - 51 * u ^ 3 * v + 18 * u ^ 3 - 7 * u ^ 2 * v ^ 4 + 45 * u ^ 2 * v ^ 3 - 90 * u ^ 2 * v ^ 2 + 45 * u ^ 2 * v - 9 * u ^ 2 + 15 * u * v ^ 4 - 51 * u * v ^ 3 + 45 * u * v ^ 2 - 9 * u * v - 9 * v ^ 4 + 18 * v ^ 3 - 9 * v ^ 2) < 0 := by
  set u1 : ℝ := 1 - u with hu1def
  set w0 : ℝ := 3 - 3 * u - 3 * v - u * v with hw0def
  have hu1p : 0 < u1 := sub_pos.2 hu1
  have hw0 : 0 < w0 := by
    have e : 3 - 3 * u - 3 * v - u * v = u₃ * (3 + u + v - u * v) := by linarith [hrel]
    have e2 : 0 < 3 + u + v - u * v := by nlinarith [hu0, hv0]
    rw [hw0def, e]
    exact mul_pos hu₃0 e2
  have hQ3master : (3 * u1)^4 * (3 + u)^7 * (-(u ^ 4 * v ^ 3 - 7 * u ^ 4 * v ^ 2 + 15 * u ^ 4 * v - 9 * u ^ 4 + u ^ 3 * v ^ 4 - 13 * u ^ 3 * v ^ 3 + 45 * u ^ 3 * v ^ 2 - 51 * u ^ 3 * v + 18 * u ^ 3 - 7 * u ^ 2 * v ^ 4 + 45 * u ^ 2 * v ^ 3 - 90 * u ^ 2 * v ^ 2 + 45 * u ^ 2 * v - 9 * u ^ 2 + 15 * u * v ^ 4 - 51 * u * v ^ 3 + 45 * u * v ^ 2 - 9 * u * v - 9 * v ^ 4 + 18 * v ^ 3 - 9 * v ^ 2)) = ((19683) * u^0 * u1^11 * (v*(3+u))^2 * w0^2 + (19683) * u^1 * u1^10 * (v*(3+u))^1 * w0^3 + (170586) * u^1 * u1^10 * (v*(3+u))^2 * w0^2 + (26244) * u^1 * u1^10 * (v*(3+u))^3 * w0^1 + (19683) * u^2 * u1^9 * (v*(3+u))^0 * w0^4 + (196830) * u^2 * u1^9 * (v*(3+u))^1 * w0^3 + (710775) * u^2 * u1^9 * (v*(3+u))^2 * w0^2 + (244944) * u^2 * u1^9 * (v*(3+u))^3 * w0^1 + (34992) * u^2 * u1^9 * (v*(3+u))^4 * w0^0 + (183708) * u^3 * u1^8 * (v*(3+u))^0 * w0^4 + (918540) * u^3 * u1^8 * (v*(3+u))^1 * w0^3) + ((1979964) * u^3 * u1^8 * (v*(3+u))^2 * w0^2 + (1084752) * u^3 * u1^8 * (v*(3+u))^3 * w0^1 + (279936) * u^3 * u1^8 * (v*(3+u))^4 * w0^0 + (734832) * u^4 * u1^7 * (v*(3+u))^0 * w0^4 + (2612736) * u^4 * u1^7 * (v*(3+u))^1 * w0^3 + (4183488) * u^4 * u1^7 * (v*(3+u))^2 * w0^2 + (2954880) * u^4 * u1^7 * (v*(3+u))^3 * w0^1 + (979776) * u^4 * u1^7 * (v*(3+u))^4 * w0^0 + (1632960) * u^5 * u1^6 * (v*(3+u))^0 * w0^4 + (4898880) * u^5 * u1^6 * (v*(3+u))^1 * w0^3 + (6770304) * u^5 * u1^6 * (v*(3+u))^2 * w0^2) + ((5323968) * u^5 * u1^6 * (v*(3+u))^3 * w0^1 + (1949184) * u^5 * u1^6 * (v*(3+u))^4 * w0^0 + (2177280) * u^6 * u1^5 * (v*(3+u))^0 * w0^4 + (6096384) * u^6 * u1^5 * (v*(3+u))^1 * w0^3 + (7941888) * u^6 * u1^5 * (v*(3+u))^2 * w0^2 + (6386688) * u^6 * u1^5 * (v*(3+u))^3 * w0^1 + (2384640) * u^6 * u1^5 * (v*(3+u))^4 * w0^0 + (1741824) * u^7 * u1^4 * (v*(3+u))^0 * w0^4 + (4838400) * u^7 * u1^4 * (v*(3+u))^1 * w0^3 + (6220800) * u^7 * u1^4 * (v*(3+u))^2 * w0^2 + (4921344) * u^7 * u1^4 * (v*(3+u))^3 * w0^1) + ((1797120) * u^7 * u1^4 * (v*(3+u))^4 * w0^0 + (774144) * u^8 * u1^3 * (v*(3+u))^0 * w0^4 + (2211840) * u^8 * u1^3 * (v*(3+u))^1 * w0^3 + (2875392) * u^8 * u1^3 * (v*(3+u))^2 * w0^2 + (2211840) * u^8 * u1^3 * (v*(3+u))^3 * w0^1 + (774144) * u^8 * u1^3 * (v*(3+u))^4 * w0^0 + (147456) * u^9 * u1^2 * (v*(3+u))^0 * w0^4 + (442368) * u^9 * u1^2 * (v*(3+u))^1 * w0^3 + (589824) * u^9 * u1^2 * (v*(3+u))^2 * w0^2 + (442368) * u^9 * u1^2 * (v*(3+u))^3 * w0^1 + (147456) * u^9 * u1^2 * (v*(3+u))^4 * w0^0) := by ring
  have hG1 : 0 < ((19683) * u^0 * u1^11 * (v*(3+u))^2 * w0^2 + (19683) * u^1 * u1^10 * (v*(3+u))^1 * w0^3 + (170586) * u^1 * u1^10 * (v*(3+u))^2 * w0^2 + (26244) * u^1 * u1^10 * (v*(3+u))^3 * w0^1 + (19683) * u^2 * u1^9 * (v*(3+u))^0 * w0^4 + (196830) * u^2 * u1^9 * (v*(3+u))^1 * w0^3 + (710775) * u^2 * u1^9 * (v*(3+u))^2 * w0^2 + (244944) * u^2 * u1^9 * (v*(3+u))^3 * w0^1 + (34992) * u^2 * u1^9 * (v*(3+u))^4 * w0^0 + (183708) * u^3 * u1^8 * (v*(3+u))^0 * w0^4 + (918540) * u^3 * u1^8 * (v*(3+u))^1 * w0^3) := by positivity
  have hG2 : 0 < ((1979964) * u^3 * u1^8 * (v*(3+u))^2 * w0^2 + (1084752) * u^3 * u1^8 * (v*(3+u))^3 * w0^1 + (279936) * u^3 * u1^8 * (v*(3+u))^4 * w0^0 + (734832) * u^4 * u1^7 * (v*(3+u))^0 * w0^4 + (2612736) * u^4 * u1^7 * (v*(3+u))^1 * w0^3 + (4183488) * u^4 * u1^7 * (v*(3+u))^2 * w0^2 + (2954880) * u^4 * u1^7 * (v*(3+u))^3 * w0^1 + (979776) * u^4 * u1^7 * (v*(3+u))^4 * w0^0 + (1632960) * u^5 * u1^6 * (v*(3+u))^0 * w0^4 + (4898880) * u^5 * u1^6 * (v*(3+u))^1 * w0^3 + (6770304) * u^5 * u1^6 * (v*(3+u))^2 * w0^2) := by positivity
  have hG3 : 0 < ((5323968) * u^5 * u1^6 * (v*(3+u))^3 * w0^1 + (1949184) * u^5 * u1^6 * (v*(3+u))^4 * w0^0 + (2177280) * u^6 * u1^5 * (v*(3+u))^0 * w0^4 + (6096384) * u^6 * u1^5 * (v*(3+u))^1 * w0^3 + (7941888) * u^6 * u1^5 * (v*(3+u))^2 * w0^2 + (6386688) * u^6 * u1^5 * (v*(3+u))^3 * w0^1 + (2384640) * u^6 * u1^5 * (v*(3+u))^4 * w0^0 + (1741824) * u^7 * u1^4 * (v*(3+u))^0 * w0^4 + (4838400) * u^7 * u1^4 * (v*(3+u))^1 * w0^3 + (6220800) * u^7 * u1^4 * (v*(3+u))^2 * w0^2 + (4921344) * u^7 * u1^4 * (v*(3+u))^3 * w0^1) := by positivity
  have hG4 : 0 < ((1797120) * u^7 * u1^4 * (v*(3+u))^4 * w0^0 + (774144) * u^8 * u1^3 * (v*(3+u))^0 * w0^4 + (2211840) * u^8 * u1^3 * (v*(3+u))^1 * w0^3 + (2875392) * u^8 * u1^3 * (v*(3+u))^2 * w0^2 + (2211840) * u^8 * u1^3 * (v*(3+u))^3 * w0^1 + (774144) * u^8 * u1^3 * (v*(3+u))^4 * w0^0 + (147456) * u^9 * u1^2 * (v*(3+u))^0 * w0^4 + (442368) * u^9 * u1^2 * (v*(3+u))^1 * w0^3 + (589824) * u^9 * u1^2 * (v*(3+u))^2 * w0^2 + (442368) * u^9 * u1^2 * (v*(3+u))^3 * w0^1 + (147456) * u^9 * u1^2 * (v*(3+u))^4 * w0^0) := by positivity
  have hQ3 : (u ^ 4 * v ^ 3 - 7 * u ^ 4 * v ^ 2 + 15 * u ^ 4 * v - 9 * u ^ 4 + u ^ 3 * v ^ 4 - 13 * u ^ 3 * v ^ 3 + 45 * u ^ 3 * v ^ 2 - 51 * u ^ 3 * v + 18 * u ^ 3 - 7 * u ^ 2 * v ^ 4 + 45 * u ^ 2 * v ^ 3 - 90 * u ^ 2 * v ^ 2 + 45 * u ^ 2 * v - 9 * u ^ 2 + 15 * u * v ^ 4 - 51 * u * v ^ 3 + 45 * u * v ^ 2 - 9 * u * v - 9 * v ^ 4 + 18 * v ^ 3 - 9 * v ^ 2) < 0 := by
    have hpos : 0 < (3 * u1)^4 * (3 + u)^7 * (-(u ^ 4 * v ^ 3 - 7 * u ^ 4 * v ^ 2 + 15 * u ^ 4 * v - 9 * u ^ 4 + u ^ 3 * v ^ 4 - 13 * u ^ 3 * v ^ 3 + 45 * u ^ 3 * v ^ 2 - 51 * u ^ 3 * v + 18 * u ^ 3 - 7 * u ^ 2 * v ^ 4 + 45 * u ^ 2 * v ^ 3 - 90 * u ^ 2 * v ^ 2 + 45 * u ^ 2 * v - 9 * u ^ 2 + 15 * u * v ^ 4 - 51 * u * v ^ 3 + 45 * u * v ^ 2 - 9 * u * v - 9 * v ^ 4 + 18 * v ^ 3 - 9 * v ^ 2)) := by
      rw [hQ3master]
      exact add_pos (add_pos (add_pos hG1 hG2) hG3) hG4
    have hfac : 0 < (3 * u1)^4 * (3 + u)^7 := by positivity
    by_contra hc
    exact absurd hpos (not_lt.2 (mul_nonpos_of_nonneg_of_nonpos hfac.le (neg_nonpos.2 (le_of_not_gt hc))))
  exact hQ3


/-- Completing the square for a circle equation, with atomic coefficients. -/
lemma sqform_aux (sig del eps phi rT x y : ℝ) (hs : sig ≠ 0)
    (hrT : rT = del ^ 2 + eps ^ 2 - 4 * sig * phi) :
    sig * (x ^ 2 + y ^ 2) + del * x + eps * y + phi
      = sig * ((x - (-del / (2 * sig))) ^ 2 + (y - (-eps / (2 * sig))) ^ 2 - rT / (4 * sig ^ 2)) := by
  rw [hrT]; field_simp [hs]; ring

/-- Completing the square for a circle equation, `+`-form with atomic coefficients. -/
lemma sqform_aux2 (sig del eps phi rB x y : ℝ) (hs : sig ≠ 0)
    (hrB : rB = (del ^ 2 + eps ^ 2 - 4 * sig * phi) / (4 * sig ^ 2)) :
    sig * (x ^ 2 + y ^ 2) + del * x + eps * y + phi
      = sig * ((x + del / (2 * sig)) ^ 2 + (y + eps / (2 * sig)) ^ 2 - rB) := by
  rw [hrB]; field_simp [hs]; ring

lemma sqSfactsL (u v u₃ R : ℝ) (hR : 0 < R) (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1)
    (hu₃0 : 0 < u₃) (hu₃1 : u₃ < 1)
    (hrel : u₃ * (3 + u + v - u * v) = 3 - u * v - 3 * u - 3 * v) (huv : u ≠ v)
    (hdA : u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3 ≠ 0)
    (hdB : u ^ 2 * v - u ^ 2 - 2 * u * v - 6 * u - 3 * v + 3 ≠ 0) :
    0 < (sqNd u v R)
      ∧ 0 < (nn0d u v R)
      ∧ 0 < (Sd u v R)
      ∧ (Sd u v R) ^ 2 = (sqNd u v R) / (4 * (sigAd u v) ^ 2 * (nn0d u v R) ^ 2)
      ∧ (ald u v R) ^ 2 + (bed u v R) ^ 2 = (nn0d u v R)
      ∧ (sqNd u v R) + (trhod u v R) ^ 2 = (nn0d u v R) * (Rtmp0d u v R)
      ∧ ∀ x y : ℝ, (sigAd u v) * (x ^ 2 + y ^ 2) + (delAd u v R) * x + (epsAd u v R) * y + (phiAd u v R)
      = (sigAd u v) * ((x - (caxd u v R)) ^ 2 + (y - (cayd u v R)) ^ 2 - (RA2d u v R)) := by
  have hw : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsqrt3ne : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hu3nev : u₃ ≠ v := by
    intro h
    rw [h] at hrel
    have hz : u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3 = 0 := by linear_combination (-1) * hrel
    exact hdA hz
  have hu3neu : u₃ ≠ u := by
    intro h
    rw [h] at hrel
    have hz : u ^ 2 * v - u ^ 2 - 2 * u * v - 6 * u - 3 * v + 3 = 0 := by linear_combination (-1) * hrel
    exact hdB hz
  have hdenA2C : u₃ * v - u₃ - v - 3 ≠ 0 := by
    have h1 : u₃ * v < u₃ := by have h2 := mul_lt_mul_of_pos_left hv1 hu₃0; rwa [mul_one] at h2
    have h2 : u₃ * v - u₃ - v - 3 < 0 := by nlinarith only [h1, hv0]
    exact ne_of_lt h2
  have hdenB2C : u * u₃ - u - u₃ - 3 ≠ 0 := by
    have h1 : u * u₃ < u := by have h2 := mul_lt_mul_of_pos_left hu₃1 hu0; rwa [mul_one] at h2
    have h2 : u * u₃ - u - u₃ - 3 < 0 := by nlinarith only [h1, hu₃0]
    exact ne_of_lt h2
  have hdenC2C : u * v - u - v - 3 ≠ 0 := by
    have h1 : u * v < u := by have h2 := mul_lt_mul_of_pos_left hv1 hu0; rwa [mul_one] at h2
    have h2 : u * v - u - v - 3 < 0 := by nlinarith only [h1, hv0]
    exact ne_of_lt h2
  have hdenA2 : (dA2d u₃ v) ≠ 0 := by simp only [dA2d]; exact hdenA2C
  have hdenB2 : (dB2d u v u₃) ≠ 0 := by simp only [dB2d]; exact mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hdenB2C
  have hdenC2 : (dC2d u v) ≠ 0 := by simp only [dC2d]; exact mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hdenC2C

  have hsigA : (sigAd u v) ≠ 0 := by
    simp only [sigAd]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by positivity : (0:ℝ) < v ^ 2 + 3).ne') hdA
  have hsigB : (sigBd u v) ≠ 0 := by
    simp only [sigBd]
    exact mul_ne_zero (mul_ne_zero (by norm_num : (24:ℝ) ≠ 0)
      (by positivity : (0:ℝ) < u ^ 2 + 3).ne') hdB
  have hsigC : (sigCd u v) ≠ 0 := by
    simp only [sigCd]
    exact mul_ne_zero (mul_ne_zero (by norm_num : (6:ℝ) ≠ 0) (sub_ne_zero.mpr huv))
      (pow_ne_zero 3 hdenC2C)

  have incAA := incAA u v R
  have incAA1 := incAA1 u v R
  have incAA2 := incAA2 u v u₃ R hw hrel hdenA2C
  have incBB := incBB u v R hw
  have incBB1 := incBB1 u v R hw
  have incBB2 := incBB2 u v u₃ R hw hrel (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hdenB2C)
  have incCC := incCC u v R hw
  have incCC1 := incCC1 u v u₃ R hw hrel
  have incCC2 := incCC2 u v u₃ R hw hrel (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hdenC2C)
  have hradB := hradBL u v R
  have hradC := hradCL u v R
  have hcoaxx := hcoaxxL u v R
  have hcoaxy := hcoaxyL u v R
  have hcoaxc := hcoaxcL u v R
  have hepsA2eq := hepsA2eqL u v R hw
  have hbe2eq := hbe2eqL u v R hw
  have hbeepseq := hbeepseqL u v R hw
  have hF4b := hF4bL u v R
  have hnn0eq := hnn0eqL u v R hF4b
  have htrhoeq := htrhoeqL u v R
  have hRtmp0eq := hRtmp0eqL u v R
  have hF4 := hF4L u v R
  have BIGID := bigidL u v R hF4
  have hQ3 := q3negL hu0 hu1 hv0 hv1 hu₃0 hrel
  -- positivity of (sqNd u v R) and (nn0d u v R)
  have hsqNpos : 0 < (sqNd u v R) := by
    simp only [sqNd]
    apply mul_pos (by positivity)
    exact mul_pos (mul_pos (by norm_num) (sq_pos_of_ne_zero hdA)) (neg_pos.2 hQ3)
  have hnn : (ald u v R) ^ 2 + (bed u v R) ^ 2 = (nn0d u v R) := by
    simp only [ald, bed, nn0d]; rw [hbe2eq, hnn0eq]
  have hBIG2 : (sqNd u v R) + (trhod u v R) ^ 2 = (nn0d u v R) * (Rtmp0d u v R) := by
    simp only [sqNd, trhod, nn0d, Rtmp0d]; exact BIGID
  have hnn0pos : 0 < (nn0d u v R) := by
    have hge : 0 ≤ (nn0d u v R) := by rw [← hnn]; positivity
    rcases hge.eq_or_lt with h0 | hpos
    · exfalso
      rw [h0.symm, zero_mul] at hBIG2
      have hz : (sqNd u v R) ≤ 0 := by nlinarith only [sq_nonneg (trhod u v R), hBIG2]
      linarith [hsqNpos, hz]
    · exact hpos
  -- the two common points
  have hSpos : 0 < (Sd u v R) := by
    simp only [Sd]
    exact div_pos (Real.sqrt_pos.2 (mul_pos hsqNpos (sq_pos_of_ne_zero hsigA)))
      (mul_pos (mul_pos (by norm_num) (sq_pos_of_ne_zero hsigA)) hnn0pos)
  have hS2 : (Sd u v R) ^ 2 = (sqNd u v R) / (4 * (sigAd u v) ^ 2 * (nn0d u v R) ^ 2) := by
    simp only [Sd]
    rw [div_pow, Real.sq_sqrt (le_of_lt (mul_pos hsqNpos (sq_pos_of_ne_zero hsigA))),
      div_eq_div_iff (pow_ne_zero 2 (mul_ne_zero (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0)
          (pow_ne_zero 2 hsigA)) hnn0pos.ne'))
        (mul_ne_zero (mul_ne_zero (by norm_num : (4:ℝ) ≠ 0) (pow_ne_zero 2 hsigA))
          (pow_ne_zero 2 hnn0pos.ne'))]
    generalize h1 : (sqNd u v R) = sq0
    generalize h2 : (sigAd u v) = sA
    generalize h3 : (nn0d u v R) = n0
    ring
  -- completed-square form of the circle equation
  have hRA : (Rtmp0d u v R) = (delAd u v R) ^ 2 + (epsAd u v R) ^ 2 - 4 * (sigAd u v) * (phiAd u v R) := by
    simp only [delAd, epsAd, sigAd, phiAd, Rtmp0d]
    rw [hepsA2eq]; exact hRtmp0eq.symm
  have hsqformA : ∀ x y : ℝ, (sigAd u v) * (x ^ 2 + y ^ 2) + (delAd u v R) * x + (epsAd u v R) * y + (phiAd u v R)
      = (sigAd u v) * ((x - (caxd u v R)) ^ 2 + (y - (cayd u v R)) ^ 2 - (RA2d u v R)) := by
    intro x y
    simp only [RA2d, caxd, cayd]
    exact sqform_aux _ _ _ _ _ _ _ hsigA hRA
  have hortho : (ald u v R) * (-(bed u v R)) + (bed u v R) * (ald u v R) = 0 := by ring
  exact ⟨hsqNpos, hnn0pos, hSpos, hS2, hnn, hBIG2, hsqformA⟩

lemma distP12L (u v u₃ R : ℝ) (hR : 0 < R) (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1)
    (hu₃0 : 0 < u₃) (hu₃1 : u₃ < 1)
    (hrel : u₃ * (3 + u + v - u * v) = 3 - u * v - 3 * u - 3 * v) (huv : u ≠ v)
    (hdA : u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3 ≠ 0)
    (hdB : u ^ 2 * v - u ^ 2 - 2 * u * v - 6 * u - 3 * v + 3 ≠ 0)
    (hS2h : (Sd u v R) ^ 2 = (sqNd u v R) / (4 * (sigAd u v) ^ 2 * (nn0d u v R) ^ 2))
    (hnnh : (ald u v R) ^ 2 + (bed u v R) ^ 2 = (nn0d u v R))
    (hBIG2h : (sqNd u v R) + (trhod u v R) ^ 2 = (nn0d u v R) * (Rtmp0d u v R))
    (hnn0posh : 0 < (nn0d u v R)) :
    ((P1xd u v R) - (caxd u v R)) ^ 2 + ((P1yd u v R) - (cayd u v R)) ^ 2 = (RA2d u v R) ∧ ((P2xd u v R) - (caxd u v R)) ^ 2 + ((P2yd u v R) - (cayd u v R)) ^ 2 = (RA2d u v R) := by
  have hw : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsqrt3ne : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hu3nev : u₃ ≠ v := by
    intro h
    rw [h] at hrel
    have hz : u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3 = 0 := by linear_combination (-1) * hrel
    exact hdA hz
  have hu3neu : u₃ ≠ u := by
    intro h
    rw [h] at hrel
    have hz : u ^ 2 * v - u ^ 2 - 2 * u * v - 6 * u - 3 * v + 3 = 0 := by linear_combination (-1) * hrel
    exact hdB hz
  have hdenA2C : u₃ * v - u₃ - v - 3 ≠ 0 := by
    have h1 : u₃ * v < u₃ := by have h2 := mul_lt_mul_of_pos_left hv1 hu₃0; rwa [mul_one] at h2
    have h2 : u₃ * v - u₃ - v - 3 < 0 := by nlinarith only [h1, hv0]
    exact ne_of_lt h2
  have hdenB2C : u * u₃ - u - u₃ - 3 ≠ 0 := by
    have h1 : u * u₃ < u := by have h2 := mul_lt_mul_of_pos_left hu₃1 hu0; rwa [mul_one] at h2
    have h2 : u * u₃ - u - u₃ - 3 < 0 := by nlinarith only [h1, hu₃0]
    exact ne_of_lt h2
  have hdenC2C : u * v - u - v - 3 ≠ 0 := by
    have h1 : u * v < u := by have h2 := mul_lt_mul_of_pos_left hv1 hu0; rwa [mul_one] at h2
    have h2 : u * v - u - v - 3 < 0 := by nlinarith only [h1, hv0]
    exact ne_of_lt h2
  have hdenA2 : (dA2d u₃ v) ≠ 0 := by simp only [dA2d]; exact hdenA2C
  have hdenB2 : (dB2d u v u₃) ≠ 0 := by simp only [dB2d]; exact mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hdenB2C
  have hdenC2 : (dC2d u v) ≠ 0 := by simp only [dC2d]; exact mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hdenC2C

  have hsigA : (sigAd u v) ≠ 0 := by
    simp only [sigAd]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by positivity : (0:ℝ) < v ^ 2 + 3).ne') hdA
  have hsigB : (sigBd u v) ≠ 0 := by
    simp only [sigBd]
    exact mul_ne_zero (mul_ne_zero (by norm_num : (24:ℝ) ≠ 0)
      (by positivity : (0:ℝ) < u ^ 2 + 3).ne') hdB
  have hsigC : (sigCd u v) ≠ 0 := by
    simp only [sigCd]
    exact mul_ne_zero (mul_ne_zero (by norm_num : (6:ℝ) ≠ 0) (sub_ne_zero.mpr huv))
      (pow_ne_zero 3 hdenC2C)

  have hS2 : (Sd u v R) ^ 2 = (sqNd u v R) / (4 * (sigAd u v) ^ 2 * (nn0d u v R) ^ 2) := hS2h
  have hnn : (ald u v R) ^ 2 + (bed u v R) ^ 2 = (nn0d u v R) := hnnh
  have hBIG2 : (sqNd u v R) + (trhod u v R) ^ 2 = (nn0d u v R) * (Rtmp0d u v R) := hBIG2h
  have hnn0pos : 0 < (nn0d u v R) := hnn0posh
  have hortho : (ald u v R) * (-(bed u v R)) + (bed u v R) * (ald u v R) = 0 := by ring
  have hdistP1 : ((P1xd u v R) - (caxd u v R)) ^ 2 + ((P1yd u v R) - (cayd u v R)) ^ 2 = (RA2d u v R) := by
    have e : ((P1xd u v R) - (caxd u v R)) ^ 2 + ((P1yd u v R) - (cayd u v R)) ^ 2
        = (Sd u v R) ^ 2 * ((ald u v R) ^ 2 + (bed u v R) ^ 2) + (ρ'd u v R) ^ 2 * ((ald u v R) ^ 2 + (bed u v R) ^ 2)
          - 2 * (Sd u v R) * (ρ'd u v R) * ((ald u v R) * (-(bed u v R)) + (bed u v R) * (ald u v R)) := by
      simp only [P1xd, P1yd, Mxd, Myd]
      generalize hS' : (Sd u v R) = s0
      generalize hρ'' : (ρ'd u v R) = r0
      generalize ha1 : (ald u v R) = a1
      generalize ha2 : (bed u v R) = a2
      ring
    rw [e, hortho, mul_zero, sub_zero, hnn, hS2]; simp only [ρ'd, RA2d]
    have h1 : (sqNd u v R) / (4 * (sigAd u v) ^ 2 * (nn0d u v R) ^ 2) * (nn0d u v R) = (sqNd u v R) / (4 * (sigAd u v) ^ 2 * (nn0d u v R)) := by
      rw [div_mul_eq_mul_div,
        div_eq_div_iff (mul_ne_zero (mul_ne_zero (by norm_num : (4:ℝ) ≠ 0) (pow_ne_zero 2 hsigA)) (pow_ne_zero 2 hnn0pos.ne'))
          (mul_ne_zero (mul_ne_zero (by norm_num : (4:ℝ) ≠ 0) (pow_ne_zero 2 hsigA)) hnn0pos.ne')]
      generalize h1' : (sqNd u v R) = sq0
      generalize h2' : (sigAd u v) = sA
      generalize h3' : (nn0d u v R) = n0
      ring
    have h2 : ((trhod u v R) / (2 * (sigAd u v) * (nn0d u v R))) ^ 2 * (nn0d u v R) = (trhod u v R) ^ 2 / (4 * (sigAd u v) ^ 2 * (nn0d u v R)) := by
      rw [div_pow, div_mul_eq_mul_div,
        div_eq_div_iff (pow_ne_zero 2 (mul_ne_zero (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hsigA) hnn0pos.ne'))
          (mul_ne_zero (mul_ne_zero (by norm_num : (4:ℝ) ≠ 0) (pow_ne_zero 2 hsigA)) hnn0pos.ne')]
      generalize h4' : (trhod u v R) = t0
      generalize h5' : (sigAd u v) = sA
      generalize h6' : (nn0d u v R) = n0
      ring
    rw [h1, h2, ← add_div, hBIG2,
      div_eq_div_iff (mul_ne_zero (mul_ne_zero (by norm_num : (4:ℝ) ≠ 0) (pow_ne_zero 2 hsigA)) hnn0pos.ne')
        (mul_ne_zero (by norm_num : (4:ℝ) ≠ 0) (pow_ne_zero 2 hsigA))]
    generalize h7' : (nn0d u v R) = n0
    generalize h8' : (Rtmp0d u v R) = rT
    generalize h9' : (sigAd u v) = sA
    ring
  have hdistP2 : ((P2xd u v R) - (caxd u v R)) ^ 2 + ((P2yd u v R) - (cayd u v R)) ^ 2 = (RA2d u v R) := by
    have e : ((P2xd u v R) - (caxd u v R)) ^ 2 + ((P2yd u v R) - (cayd u v R)) ^ 2
        = (Sd u v R) ^ 2 * ((ald u v R) ^ 2 + (bed u v R) ^ 2) + (ρ'd u v R) ^ 2 * ((ald u v R) ^ 2 + (bed u v R) ^ 2)
          + 2 * (Sd u v R) * (ρ'd u v R) * ((ald u v R) * (bed u v R) + (bed u v R) * (-(ald u v R))) := by
      simp only [P2xd, P2yd, Mxd, Myd]
      generalize hS' : (Sd u v R) = s0
      generalize hρ'' : (ρ'd u v R) = r0
      generalize ha1 : (ald u v R) = a1
      generalize ha2 : (bed u v R) = a2
      ring
    have hortho2 : (ald u v R) * (bed u v R) + (bed u v R) * (-(ald u v R)) = 0 := by ring
    rw [e, hortho2, mul_zero, add_zero, hnn, hS2]; simp only [ρ'd, RA2d]
    have h1 : (sqNd u v R) / (4 * (sigAd u v) ^ 2 * (nn0d u v R) ^ 2) * (nn0d u v R) = (sqNd u v R) / (4 * (sigAd u v) ^ 2 * (nn0d u v R)) := by
      rw [div_mul_eq_mul_div,
        div_eq_div_iff (mul_ne_zero (mul_ne_zero (by norm_num : (4:ℝ) ≠ 0) (pow_ne_zero 2 hsigA)) (pow_ne_zero 2 hnn0pos.ne'))
          (mul_ne_zero (mul_ne_zero (by norm_num : (4:ℝ) ≠ 0) (pow_ne_zero 2 hsigA)) hnn0pos.ne')]
      generalize h1' : (sqNd u v R) = sq0
      generalize h2' : (sigAd u v) = sA
      generalize h3' : (nn0d u v R) = n0
      ring
    have h2 : ((trhod u v R) / (2 * (sigAd u v) * (nn0d u v R))) ^ 2 * (nn0d u v R) = (trhod u v R) ^ 2 / (4 * (sigAd u v) ^ 2 * (nn0d u v R)) := by
      rw [div_pow, div_mul_eq_mul_div,
        div_eq_div_iff (pow_ne_zero 2 (mul_ne_zero (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hsigA) hnn0pos.ne'))
          (mul_ne_zero (mul_ne_zero (by norm_num : (4:ℝ) ≠ 0) (pow_ne_zero 2 hsigA)) hnn0pos.ne')]
      generalize h4' : (trhod u v R) = t0
      generalize h5' : (sigAd u v) = sA
      generalize h6' : (nn0d u v R) = n0
      ring
    rw [h1, h2, ← add_div, hBIG2,
      div_eq_div_iff (mul_ne_zero (mul_ne_zero (by norm_num : (4:ℝ) ≠ 0) (pow_ne_zero 2 hsigA)) hnn0pos.ne')
        (mul_ne_zero (by norm_num : (4:ℝ) ≠ 0) (pow_ne_zero 2 hsigA))]
    generalize h7' : (nn0d u v R) = n0
    generalize h8' : (Rtmp0d u v R) = rT
    generalize h9' : (sigAd u v) = sA
    ring
  exact ⟨hdistP1, hdistP2⟩

lemma lineP12L (u v u₃ R : ℝ) (hR : 0 < R) (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1)
    (hu₃0 : 0 < u₃) (hu₃1 : u₃ < 1)
    (hrel : u₃ * (3 + u + v - u * v) = 3 - u * v - 3 * u - 3 * v) (huv : u ≠ v)
    (hdA : u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3 ≠ 0)
    (hdB : u ^ 2 * v - u ^ 2 - 2 * u * v - 6 * u - 3 * v + 3 ≠ 0)
    (hnnh : (ald u v R) ^ 2 + (bed u v R) ^ 2 = (nn0d u v R))
    (hnn0posh : 0 < (nn0d u v R)) :
    (ald u v R) * (P1xd u v R) + (bed u v R) * (P1yd u v R) + (gad u v R) = 0 ∧ (ald u v R) * (P2xd u v R) + (bed u v R) * (P2yd u v R) + (gad u v R) = 0 := by
  have hw : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsqrt3ne : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hu3nev : u₃ ≠ v := by
    intro h
    rw [h] at hrel
    have hz : u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3 = 0 := by linear_combination (-1) * hrel
    exact hdA hz
  have hu3neu : u₃ ≠ u := by
    intro h
    rw [h] at hrel
    have hz : u ^ 2 * v - u ^ 2 - 2 * u * v - 6 * u - 3 * v + 3 = 0 := by linear_combination (-1) * hrel
    exact hdB hz
  have hdenA2C : u₃ * v - u₃ - v - 3 ≠ 0 := by
    have h1 : u₃ * v < u₃ := by have h2 := mul_lt_mul_of_pos_left hv1 hu₃0; rwa [mul_one] at h2
    have h2 : u₃ * v - u₃ - v - 3 < 0 := by nlinarith only [h1, hv0]
    exact ne_of_lt h2
  have hdenB2C : u * u₃ - u - u₃ - 3 ≠ 0 := by
    have h1 : u * u₃ < u := by have h2 := mul_lt_mul_of_pos_left hu₃1 hu0; rwa [mul_one] at h2
    have h2 : u * u₃ - u - u₃ - 3 < 0 := by nlinarith only [h1, hu₃0]
    exact ne_of_lt h2
  have hdenC2C : u * v - u - v - 3 ≠ 0 := by
    have h1 : u * v < u := by have h2 := mul_lt_mul_of_pos_left hv1 hu0; rwa [mul_one] at h2
    have h2 : u * v - u - v - 3 < 0 := by nlinarith only [h1, hv0]
    exact ne_of_lt h2
  have hdenA2 : (dA2d u₃ v) ≠ 0 := by simp only [dA2d]; exact hdenA2C
  have hdenB2 : (dB2d u v u₃) ≠ 0 := by simp only [dB2d]; exact mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hdenB2C
  have hdenC2 : (dC2d u v) ≠ 0 := by simp only [dC2d]; exact mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hdenC2C

  have hsigA : (sigAd u v) ≠ 0 := by
    simp only [sigAd]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by positivity : (0:ℝ) < v ^ 2 + 3).ne') hdA
  have hsigB : (sigBd u v) ≠ 0 := by
    simp only [sigBd]
    exact mul_ne_zero (mul_ne_zero (by norm_num : (24:ℝ) ≠ 0)
      (by positivity : (0:ℝ) < u ^ 2 + 3).ne') hdB
  have hsigC : (sigCd u v) ≠ 0 := by
    simp only [sigCd]
    exact mul_ne_zero (mul_ne_zero (by norm_num : (6:ℝ) ≠ 0) (sub_ne_zero.mpr huv))
      (pow_ne_zero 3 hdenC2C)

  have hbeepseq := hbeepseqL u v R hw
  have htrhoeq := htrhoeqL u v R
  have hnn : (ald u v R) ^ 2 + (bed u v R) ^ 2 = (nn0d u v R) := hnnh
  have hnn0pos : 0 < (nn0d u v R) := hnn0posh
  -- the points lie on the common radical axis
  have hlineM : (ald u v R) * (caxd u v R) + (bed u v R) * (cayd u v R) + (gad u v R) = (trhod u v R) / (2 * (sigAd u v)) := by
    have hbeepseq' : (bed u v R) * (epsAd u v R) = (beepsd u v R) := by
      simp only [bed, epsAd, beepsd]; exact hbeepseq
    have h2 : (ald u v R) * (caxd u v R) + (bed u v R) * (cayd u v R) + (gad u v R)
        = (2 * (sigAd u v) * (gad u v R) - ((ald u v R) * (delAd u v R) + (beepsd u v R))) / (2 * (sigAd u v)) := by
      simp only [caxd, cayd]
      rw [← hbeepseq']
      field_simp [hsigA]
      ring
    rw [h2]
    congr 1
    exact (sub_eq_neg_add _ _).trans htrhoeq
  have hP1line : (ald u v R) * (P1xd u v R) + (bed u v R) * (P1yd u v R) + (gad u v R) = 0 := by
    have e : (ald u v R) * (P1xd u v R) + (bed u v R) * (P1yd u v R) + (gad u v R)
        = ((ald u v R) * (caxd u v R) + (bed u v R) * (cayd u v R) + (gad u v R)) - (ρ'd u v R) * ((ald u v R) ^ 2 + (bed u v R) ^ 2) + (Sd u v R) * ((bed u v R) * (ald u v R) - (ald u v R) * (bed u v R)) := by
      simp only [P1xd, P1yd, Mxd, Myd]; ring
    have hz : (bed u v R) * (ald u v R) - (ald u v R) * (bed u v R) = 0 := by ring
    rw [e, hz, mul_zero, add_zero, hlineM, hnn]; simp only [ρ'd]; rw [div_mul_eq_mul_div, sub_eq_zero,
      div_eq_div_iff (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hsigA)
        (mul_ne_zero (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hsigA) hnn0pos.ne')]
    ring
  have hP2line : (ald u v R) * (P2xd u v R) + (bed u v R) * (P2yd u v R) + (gad u v R) = 0 := by
    have e : (ald u v R) * (P2xd u v R) + (bed u v R) * (P2yd u v R) + (gad u v R)
        = ((ald u v R) * (caxd u v R) + (bed u v R) * (cayd u v R) + (gad u v R)) - (ρ'd u v R) * ((ald u v R) ^ 2 + (bed u v R) ^ 2) + (Sd u v R) * ((ald u v R) * (bed u v R) - (bed u v R) * (ald u v R)) := by
      simp only [P2xd, P2yd, Mxd, Myd]; ring
    have hz : (ald u v R) * (bed u v R) - (bed u v R) * (ald u v R) = 0 := by ring
    rw [e, hz, mul_zero, add_zero, hlineM, hnn]; simp only [ρ'd]; rw [div_mul_eq_mul_div, sub_eq_zero,
      div_eq_div_iff (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hsigA)
        (mul_ne_zero (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hsigA) hnn0pos.ne')]
    ring
  exact ⟨hP1line, hP2line⟩

lemma omegaP12L (u v u₃ R : ℝ) (hR : 0 < R) (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1)
    (hu₃0 : 0 < u₃) (hu₃1 : u₃ < 1)
    (hrel : u₃ * (3 + u + v - u * v) = 3 - u * v - 3 * u - 3 * v) (huv : u ≠ v)
    (hdA : u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3 ≠ 0)
    (hdB : u ^ 2 * v - u ^ 2 - 2 * u * v - 6 * u - 3 * v + 3 ≠ 0)
    (hsqformAh : ∀ x y : ℝ, (sigAd u v) * (x ^ 2 + y ^ 2) + (delAd u v R) * x + (epsAd u v R) * y + (phiAd u v R)
      = (sigAd u v) * ((x - (caxd u v R)) ^ 2 + (y - (cayd u v R)) ^ 2 - (RA2d u v R)))
    (hdistP1h : ((P1xd u v R) - (caxd u v R)) ^ 2 + ((P1yd u v R) - (cayd u v R)) ^ 2 = (RA2d u v R))
    (hdistP2h : ((P2xd u v R) - (caxd u v R)) ^ 2 + ((P2yd u v R) - (cayd u v R)) ^ 2 = (RA2d u v R))
    (hP1lineh : (ald u v R) * (P1xd u v R) + (bed u v R) * (P1yd u v R) + (gad u v R) = 0)
    (hP2lineh : (ald u v R) * (P2xd u v R) + (bed u v R) * (P2yd u v R) + (gad u v R) = 0) :
    (sigAd u v) * ((P1xd u v R) ^ 2 + (P1yd u v R) ^ 2) + (delAd u v R) * (P1xd u v R) + (epsAd u v R) * (P1yd u v R) + (phiAd u v R) = 0
      ∧ (sigAd u v) * ((P2xd u v R) ^ 2 + (P2yd u v R) ^ 2) + (delAd u v R) * (P2xd u v R) + (epsAd u v R) * (P2yd u v R) + (phiAd u v R) = 0
      ∧ (sigBd u v) * ((P1xd u v R) ^ 2 + (P1yd u v R) ^ 2) + (delBd u v R) * (P1xd u v R) + (epsBd u v R) * (P1yd u v R) + (phiBd u v R) = 0
      ∧ (sigBd u v) * ((P2xd u v R) ^ 2 + (P2yd u v R) ^ 2) + (delBd u v R) * (P2xd u v R) + (epsBd u v R) * (P2yd u v R) + (phiBd u v R) = 0
      ∧ (sigCd u v) * ((P1xd u v R) ^ 2 + (P1yd u v R) ^ 2) + (delCd u v R) * (P1xd u v R) + (epsCd u v R) * (P1yd u v R) + (phiCd u v R) = 0
      ∧ (sigCd u v) * ((P2xd u v R) ^ 2 + (P2yd u v R) ^ 2) + (delCd u v R) * (P2xd u v R) + (epsCd u v R) * (P2yd u v R) + (phiCd u v R) = 0 := by
  have hw : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsqrt3ne : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hu3nev : u₃ ≠ v := by
    intro h
    rw [h] at hrel
    have hz : u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3 = 0 := by linear_combination (-1) * hrel
    exact hdA hz
  have hu3neu : u₃ ≠ u := by
    intro h
    rw [h] at hrel
    have hz : u ^ 2 * v - u ^ 2 - 2 * u * v - 6 * u - 3 * v + 3 = 0 := by linear_combination (-1) * hrel
    exact hdB hz
  have hdenA2C : u₃ * v - u₃ - v - 3 ≠ 0 := by
    have h1 : u₃ * v < u₃ := by have h2 := mul_lt_mul_of_pos_left hv1 hu₃0; rwa [mul_one] at h2
    have h2 : u₃ * v - u₃ - v - 3 < 0 := by nlinarith only [h1, hv0]
    exact ne_of_lt h2
  have hdenB2C : u * u₃ - u - u₃ - 3 ≠ 0 := by
    have h1 : u * u₃ < u := by have h2 := mul_lt_mul_of_pos_left hu₃1 hu0; rwa [mul_one] at h2
    have h2 : u * u₃ - u - u₃ - 3 < 0 := by nlinarith only [h1, hu₃0]
    exact ne_of_lt h2
  have hdenC2C : u * v - u - v - 3 ≠ 0 := by
    have h1 : u * v < u := by have h2 := mul_lt_mul_of_pos_left hv1 hu0; rwa [mul_one] at h2
    have h2 : u * v - u - v - 3 < 0 := by nlinarith only [h1, hv0]
    exact ne_of_lt h2
  have hdenA2 : (dA2d u₃ v) ≠ 0 := by simp only [dA2d]; exact hdenA2C
  have hdenB2 : (dB2d u v u₃) ≠ 0 := by simp only [dB2d]; exact mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hdenB2C
  have hdenC2 : (dC2d u v) ≠ 0 := by simp only [dC2d]; exact mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hdenC2C

  have hsigA : (sigAd u v) ≠ 0 := by
    simp only [sigAd]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by positivity : (0:ℝ) < v ^ 2 + 3).ne') hdA
  have hsigB : (sigBd u v) ≠ 0 := by
    simp only [sigBd]
    exact mul_ne_zero (mul_ne_zero (by norm_num : (24:ℝ) ≠ 0)
      (by positivity : (0:ℝ) < u ^ 2 + 3).ne') hdB
  have hsigC : (sigCd u v) ≠ 0 := by
    simp only [sigCd]
    exact mul_ne_zero (mul_ne_zero (by norm_num : (6:ℝ) ≠ 0) (sub_ne_zero.mpr huv))
      (pow_ne_zero 3 hdenC2C)

  have hradB := hradBL u v R
  have hradC := hradCL u v R
  have hcoaxx := hcoaxxL u v R
  have hcoaxy := hcoaxyL u v R
  have hcoaxc := hcoaxcL u v R
  -- def-form versions of the radical-axis and coaxality identities
  have hradB' : ∀ x y : ℝ, (sigBd u v) * ((sigAd u v) * (x ^ 2 + y ^ 2) + (delAd u v R) * x + (epsAd u v R) * y + (phiAd u v R))
      - (sigAd u v) * ((sigBd u v) * (x ^ 2 + y ^ 2) + (delBd u v R) * x + (epsBd u v R) * y + (phiBd u v R))
      = (ald u v R) * x + (bed u v R) * y + (gad u v R) := by
    intro x y
    simp only [sigAd, delAd, epsAd, phiAd, sigBd, delBd, epsBd, phiBd, ald, bed, gad]
    exact hradB x y
  have hradC' : ∀ x y : ℝ, (sigCd u v) * ((sigAd u v) * (x ^ 2 + y ^ 2) + (delAd u v R) * x + (epsAd u v R) * y + (phiAd u v R))
      - (sigAd u v) * ((sigCd u v) * (x ^ 2 + y ^ 2) + (delCd u v R) * x + (epsCd u v R) * y + (phiCd u v R))
      = (al2d u v R) * x + (be2pd u v R) * y + (ga2d u v R) := by
    intro x y
    simp only [sigAd, delAd, epsAd, phiAd, sigCd, delCd, epsCd, phiCd, al2d, be2pd, ga2d]
    exact hradC x y
  have hcoaxx' : 4 * (u ^ 2 + 3) * ((sigCd u v) * (delAd u v R) - (sigAd u v) * (delCd u v R))
      = (u * v - u - v - 3) ^ 2 * (ald u v R) := by
    simp only [sigCd, delAd, sigAd, delCd, ald]; exact hcoaxx
  have hcoaxy' : 4 * (u ^ 2 + 3) * ((sigCd u v) * (epsAd u v R) - (sigAd u v) * (epsCd u v R))
      = (u * v - u - v - 3) ^ 2 * (bed u v R) := by
    simp only [sigCd, epsAd, sigAd, epsCd, bed]; exact hcoaxy
  have hcoaxc' : 4 * (u ^ 2 + 3) * ((sigCd u v) * (phiAd u v R) - (sigAd u v) * (phiCd u v R))
      = (u * v - u - v - 3) ^ 2 * (gad u v R) := by
    simp only [sigCd, phiAd, sigAd, phiCd, gad]; exact hcoaxc
  have hsqformA : ∀ x y : ℝ, (sigAd u v) * (x ^ 2 + y ^ 2) + (delAd u v R) * x + (epsAd u v R) * y + (phiAd u v R)
      = (sigAd u v) * ((x - (caxd u v R)) ^ 2 + (y - (cayd u v R)) ^ 2 - (RA2d u v R)) := hsqformAh
  have hdistP1 : ((P1xd u v R) - (caxd u v R)) ^ 2 + ((P1yd u v R) - (cayd u v R)) ^ 2 = (RA2d u v R) := hdistP1h
  have hdistP2 : ((P2xd u v R) - (caxd u v R)) ^ 2 + ((P2yd u v R) - (cayd u v R)) ^ 2 = (RA2d u v R) := hdistP2h
  have hP1line : (ald u v R) * (P1xd u v R) + (bed u v R) * (P1yd u v R) + (gad u v R) = 0 := hP1lineh
  have hP2line : (ald u v R) * (P2xd u v R) + (bed u v R) * (P2yd u v R) + (gad u v R) = 0 := hP2lineh
  -- both points lie on all three circle equations
  have hP1omegaA : (sigAd u v) * ((P1xd u v R) ^ 2 + (P1yd u v R) ^ 2) + (delAd u v R) * (P1xd u v R) + (epsAd u v R) * (P1yd u v R) + (phiAd u v R) = 0 := by
    rw [hsqformA, hdistP1]
    ring
  have hP2omegaA : (sigAd u v) * ((P2xd u v R) ^ 2 + (P2yd u v R) ^ 2) + (delAd u v R) * (P2xd u v R) + (epsAd u v R) * (P2yd u v R) + (phiAd u v R) = 0 := by
    rw [hsqformA]
    have e2 : ((P2xd u v R) - (caxd u v R)) ^ 2 + ((P2yd u v R) - (cayd u v R)) ^ 2 - (RA2d u v R) = 0 := by rw [hdistP2]; ring
    rw [e2]; ring
  have hP1omegaB : (sigBd u v) * ((P1xd u v R) ^ 2 + (P1yd u v R) ^ 2) + (delBd u v R) * (P1xd u v R) + (epsBd u v R) * (P1yd u v R) + (phiBd u v R) = 0 := by
    have h := hradB' (P1xd u v R) (P1yd u v R)
    rw [hP1omegaA, hP1line] at h
    -- (sigBd u v)*0 - (sigAd u v)*ΩB = 0
    have h' : (sigAd u v) * ((sigBd u v) * ((P1xd u v R) ^ 2 + (P1yd u v R) ^ 2) + (delBd u v R) * (P1xd u v R) + (epsBd u v R) * (P1yd u v R) + (phiBd u v R)) = 0 := by
      linear_combination -h
    rcases mul_eq_zero.1 h' with h1 | h1
    · exact absurd h1 hsigA
    · exact h1
  have hP2omegaB : (sigBd u v) * ((P2xd u v R) ^ 2 + (P2yd u v R) ^ 2) + (delBd u v R) * (P2xd u v R) + (epsBd u v R) * (P2yd u v R) + (phiBd u v R) = 0 := by
    have h := hradB' (P2xd u v R) (P2yd u v R)
    rw [hP2omegaA, hP2line] at h
    have h' : (sigAd u v) * ((sigBd u v) * ((P2xd u v R) ^ 2 + (P2yd u v R) ^ 2) + (delBd u v R) * (P2xd u v R) + (epsBd u v R) * (P2yd u v R) + (phiBd u v R)) = 0 := by
      linear_combination -h
    rcases mul_eq_zero.1 h' with h1 | h1
    · exact absurd h1 hsigA
    · exact h1
  have hcoaxP1 : 4 * (u ^ 2 + 3) * ((al2d u v R) * (P1xd u v R) + (be2pd u v R) * (P1yd u v R) + (ga2d u v R))
      = (u * v - u - v - 3) ^ 2 * ((ald u v R) * (P1xd u v R) + (bed u v R) * (P1yd u v R) + (gad u v R)) := by
    simp only [al2d, be2pd, ga2d]; linear_combination (P1xd u v R) * hcoaxx' + (P1yd u v R) * hcoaxy' + hcoaxc'
  have hP1omegaC : (sigCd u v) * ((P1xd u v R) ^ 2 + (P1yd u v R) ^ 2) + (delCd u v R) * (P1xd u v R) + (epsCd u v R) * (P1yd u v R) + (phiCd u v R) = 0 := by
    have h := hradC' (P1xd u v R) (P1yd u v R)
    rw [hP1omegaA] at h
    have h2 : 4 * (u ^ 2 + 3) * ((sigCd u v) * 0 - (sigAd u v) *
        ((sigCd u v) * ((P1xd u v R) ^ 2 + (P1yd u v R) ^ 2) + (delCd u v R) * (P1xd u v R) + (epsCd u v R) * (P1yd u v R) + (phiCd u v R))) = 0 := by
      linear_combination 4 * (u ^ 2 + 3) * h + hcoaxP1 + (u * v - u - v - 3) ^ 2 * hP1line
    have h3 : 4 * (u ^ 2 + 3) ≠ 0 := by positivity
    have h4 : (sigAd u v) * ((sigCd u v) * ((P1xd u v R) ^ 2 + (P1yd u v R) ^ 2) + (delCd u v R) * (P1xd u v R) + (epsCd u v R) * (P1yd u v R) + (phiCd u v R)) = 0 := by
      rcases mul_eq_zero.1 h2 with h5 | h5
      · exact absurd h5 h3
      · linarith [h5]
    rcases mul_eq_zero.1 h4 with h1 | h1
    · exact absurd h1 hsigA
    · exact h1
  have hcoaxP2 : 4 * (u ^ 2 + 3) * ((al2d u v R) * (P2xd u v R) + (be2pd u v R) * (P2yd u v R) + (ga2d u v R))
      = (u * v - u - v - 3) ^ 2 * ((ald u v R) * (P2xd u v R) + (bed u v R) * (P2yd u v R) + (gad u v R)) := by
    simp only [al2d, be2pd, ga2d]; linear_combination (P2xd u v R) * hcoaxx' + (P2yd u v R) * hcoaxy' + hcoaxc'
  have hP2omegaC : (sigCd u v) * ((P2xd u v R) ^ 2 + (P2yd u v R) ^ 2) + (delCd u v R) * (P2xd u v R) + (epsCd u v R) * (P2yd u v R) + (phiCd u v R) = 0 := by
    have h := hradC' (P2xd u v R) (P2yd u v R)
    rw [hP2omegaA] at h
    have h2 : 4 * (u ^ 2 + 3) * ((sigCd u v) * 0 - (sigAd u v) *
        ((sigCd u v) * ((P2xd u v R) ^ 2 + (P2yd u v R) ^ 2) + (delCd u v R) * (P2xd u v R) + (epsCd u v R) * (P2yd u v R) + (phiCd u v R))) = 0 := by
      linear_combination 4 * (u ^ 2 + 3) * h + hcoaxP2 + (u * v - u - v - 3) ^ 2 * hP2line
    have h3 : 4 * (u ^ 2 + 3) ≠ 0 := by positivity
    have h4 : (sigAd u v) * ((sigCd u v) * ((P2xd u v R) ^ 2 + (P2yd u v R) ^ 2) + (delCd u v R) * (P2xd u v R) + (epsCd u v R) * (P2yd u v R) + (phiCd u v R)) = 0 := by
      rcases mul_eq_zero.1 h2 with h5 | h5
      · exact absurd h5 h3
      · linarith [h5]
    rcases mul_eq_zero.1 h4 with h1 | h1
    · exact absurd h1 hsigA
    · exact h1
  exact ⟨hP1omegaA, hP2omegaA, hP1omegaB, hP2omegaB, hP1omegaC, hP2omegaC⟩

lemma affineAA1A2L {{A B C A₁ B₁ C₁ A₂ B₂ C₂ : P}}
    (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C])
    (equilateral_ABC : (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).Equilateral)
    (A₁_mem_interior_ABC : A₁ ∈ (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).interior)
    (B₁_mem_interior_ABC : B₁ ∈ (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).interior)
    (C₁_mem_interior_ABC : C₁ ∈ (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).interior)
    (BA₁_eq_A₁C : dist B A₁ = dist A₁ C) (CB₁_eq_B₁A : dist C B₁ = dist B₁ A)
    (AC₁_eq_C₁B : dist A C₁ = dist C₁ B)
    (angle_BA₁C_add_angle_CB₁A_add_angle_AC₁B :
      ∠ B A₁ C + ∠ C B₁ A + ∠ A C₁ B = 8 / 3 * π)
    (A₂_mem_inf_BC₁_CB₁ : A₂ ∈ line[ℝ, B, C₁] ⊓ line[ℝ, C, B₁])
    (B₂_mem_inf_CA₁_AC₁ : B₂ ∈ line[ℝ, C, A₁] ⊓ line[ℝ, A, C₁])
    (C₂_mem_inf_AB₁_BA₁ : C₂ ∈ line[ℝ, A, B₁] ⊓ line[ℝ, B, A₁])
    (affineIndependent_A₁B₁C₁ : AffineIndependent ℝ ![A₁, B₁, C₁])
    (scalene_A₁B₁C₁ : (⟨_, affineIndependent_A₁B₁C₁⟩ : Triangle ℝ P).Scalene) :
    AffineIndependent ℝ ![A, A₁, A₂] := by
  obtain ⟨O, R, u, v, u₃, e₁, e₂, hR, he₁, he₂, he₁₂, hA, hB, hC, hA₁, hB₁, hC₁,
    hu0, hu1, hv0, hv1, hu₃0, hu₃1, hrel⟩ :=
    frontend affineIndependent_ABC equilateral_ABC A₁_mem_interior_ABC B₁_mem_interior_ABC
      C₁_mem_interior_ABC BA₁_eq_A₁C CB₁_eq_B₁A AC₁_eq_C₁B
      angle_BA₁C_add_angle_CB₁A_add_angle_AC₁B
  obtain ⟨huv, hdA, hdB⟩ :=
    scalene_params affineIndependent_ABC equilateral_ABC affineIndependent_A₁B₁C₁
      scalene_A₁B₁C₁ hR he₁ he₂ he₁₂ hA hB hC hA₁ hB₁ hC₁ hrel
  obtain ⟨hA₂, hB₂, hC₂⟩ :=
    a2b2c2_coords affineIndependent_ABC equilateral_ABC A₂_mem_inf_BC₁_CB₁
      B₂_mem_inf_CA₁_AC₁ C₂_mem_inf_AB₁_BA₁ hR he₁ he₂ he₁₂ hA hB hC hA₁ hB₁ hC₁
      ⟨hu0, hu1⟩ ⟨hv0, hv1⟩ ⟨hu₃0, hu₃1⟩ hrel ⟨huv, hdA, hdB⟩
  have hw : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsqrt3ne : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hu3nev : u₃ ≠ v := by
    intro h
    rw [h] at hrel
    have hz : u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3 = 0 := by linear_combination (-1) * hrel
    exact hdA hz
  have hu3neu : u₃ ≠ u := by
    intro h
    rw [h] at hrel
    have hz : u ^ 2 * v - u ^ 2 - 2 * u * v - 6 * u - 3 * v + 3 = 0 := by linear_combination (-1) * hrel
    exact hdB hz
  have hdenA2C : u₃ * v - u₃ - v - 3 ≠ 0 := by
    have h1 : u₃ * v < u₃ := by have h2 := mul_lt_mul_of_pos_left hv1 hu₃0; rwa [mul_one] at h2
    have h2 : u₃ * v - u₃ - v - 3 < 0 := by nlinarith only [h1, hv0]
    exact ne_of_lt h2
  have hdenB2C : u * u₃ - u - u₃ - 3 ≠ 0 := by
    have h1 : u * u₃ < u := by have h2 := mul_lt_mul_of_pos_left hu₃1 hu0; rwa [mul_one] at h2
    have h2 : u * u₃ - u - u₃ - 3 < 0 := by nlinarith only [h1, hu₃0]
    exact ne_of_lt h2
  have hdenC2C : u * v - u - v - 3 ≠ 0 := by
    have h1 : u * v < u := by have h2 := mul_lt_mul_of_pos_left hv1 hu0; rwa [mul_one] at h2
    have h2 : u * v - u - v - 3 < 0 := by nlinarith only [h1, hv0]
    exact ne_of_lt h2
  have hdenA2 : (dA2d u₃ v) ≠ 0 := by simp only [dA2d]; exact hdenA2C
  have hA₂' : A₂ = (((-R * (u₃ * v - 2 * u₃ - 2 * v + 3)) / (dA2d u₃ v) : ℝ) • e₁ +
      ((Real.sqrt 3 * R * (u₃ - v)) / (dA2d u₃ v) : ℝ) • e₂) +ᵥ O := by
    rw [hA₂]; simp only [dA2d]
  have inner_e1 : ∀ (px py qx qy : ℝ),
      ⟪((px • e₁ + py • e₂) +ᵥ O) -ᵥ ((qx • e₁ + qy • e₂) +ᵥ O), e₁⟫_ℝ = px - qx := by
    intro px py qx qy
    rw [vadd_vsub_vadd_cancel_right, inner_sub_left, inner_add_left, inner_add_left,
      real_inner_smul_left, real_inner_smul_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, he₁, real_inner_comm e₁ e₂, he₁₂]
    ring
  have inner_e2 : ∀ (px py qx qy : ℝ),
      ⟪((px • e₁ + py • e₂) +ᵥ O) -ᵥ ((qx • e₁ + qy • e₂) +ᵥ O), e₂⟫_ℝ = py - qy := by
    intro px py qx qy
    rw [vadd_vsub_vadd_cancel_right, inner_sub_left, inner_add_left, inner_add_left,
      real_inner_smul_left, real_inner_smul_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, he₂, he₁₂]
    ring
  have hA' : A = ((R : ℝ) • e₁ + (0 : ℝ) • e₂) +ᵥ O := by rw [hA]; simp only [zero_smul, add_zero]
  have hA₁' : A₁ = ((R * (u - 1) / 2 : ℝ) • e₁ + (0 : ℝ) • e₂) +ᵥ O := by rw [hA₁]; simp only [zero_smul, add_zero]
  -- affine independence of (A, A₁, A₂)
  have hcrossA : ⟪A₁ -ᵥ A, e₁⟫_ℝ * ⟪A₂ -ᵥ A, e₂⟫_ℝ - ⟪A₁ -ᵥ A, e₂⟫_ℝ * ⟪A₂ -ᵥ A, e₁⟫_ℝ ≠ 0 := by
    have e1 : ⟪A₁ -ᵥ A, e₁⟫_ℝ = R * (u - 3) / 2 := by
      rw [hA₁', hA', inner_e1]; ring
    have e2 : ⟪A₁ -ᵥ A, e₂⟫_ℝ = 0 := by
      rw [hA₁', hA', inner_e2]; ring
    have e3 : ⟪A₂ -ᵥ A, e₂⟫_ℝ = Real.sqrt 3 * R * (u₃ - v) / (dA2d u₃ v) := by
      rw [hA₂', hA', inner_e2]; ring
    rw [e1, e2, e3]
    simp only [zero_mul, sub_zero]
    exact mul_ne_zero (div_ne_zero (mul_ne_zero hR.ne' (by nlinarith only [hu1])) (by norm_num))
      (div_ne_zero (mul_ne_zero (mul_ne_zero hsqrt3ne hR.ne') (sub_ne_zero.mpr hu3nev)) hdenA2)
  have hAIAA1A2 : AffineIndependent ℝ ![A, A₁, A₂] := by
    rw [affineIndependent_iff_not_collinear]
    intro hcol
    rw [collinear_iff_exists_forall_eq_smul_vadd] at hcol
    obtain ⟨p₀, w, hw⟩ := hcol
    obtain ⟨rA, hrA⟩ := hw A (Set.mem_range_self 0)
    obtain ⟨r1, hr1⟩ := hw A₁ (Set.mem_range_self 1)
    obtain ⟨r2, hr2⟩ := hw A₂ (Set.mem_range_self 2)
    have e1 : A₁ -ᵥ A = (r1 - rA) • w := by
      rw [hr1, hrA, vadd_vsub_vadd_cancel_right]; module
    have e2 : A₂ -ᵥ A = (r2 - rA) • w := by
      rw [hr2, hrA, vadd_vsub_vadd_cancel_right]; module
    rw [e1, e2, real_inner_smul_left, real_inner_smul_left, real_inner_smul_left, real_inner_smul_left] at hcrossA
    have hz : (r1 - rA) * ⟪w, e₁⟫_ℝ * ((r2 - rA) * ⟪w, e₂⟫_ℝ)
        - (r1 - rA) * ⟪w, e₂⟫_ℝ * ((r2 - rA) * ⟪w, e₁⟫_ℝ) = 0 := by ring
    exact hcrossA hz
  exact hAIAA1A2

lemma affineBB1B2L {{A B C A₁ B₁ C₁ A₂ B₂ C₂ : P}}
    (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C])
    (equilateral_ABC : (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).Equilateral)
    (A₁_mem_interior_ABC : A₁ ∈ (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).interior)
    (B₁_mem_interior_ABC : B₁ ∈ (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).interior)
    (C₁_mem_interior_ABC : C₁ ∈ (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).interior)
    (BA₁_eq_A₁C : dist B A₁ = dist A₁ C) (CB₁_eq_B₁A : dist C B₁ = dist B₁ A)
    (AC₁_eq_C₁B : dist A C₁ = dist C₁ B)
    (angle_BA₁C_add_angle_CB₁A_add_angle_AC₁B :
      ∠ B A₁ C + ∠ C B₁ A + ∠ A C₁ B = 8 / 3 * π)
    (A₂_mem_inf_BC₁_CB₁ : A₂ ∈ line[ℝ, B, C₁] ⊓ line[ℝ, C, B₁])
    (B₂_mem_inf_CA₁_AC₁ : B₂ ∈ line[ℝ, C, A₁] ⊓ line[ℝ, A, C₁])
    (C₂_mem_inf_AB₁_BA₁ : C₂ ∈ line[ℝ, A, B₁] ⊓ line[ℝ, B, A₁])
    (affineIndependent_A₁B₁C₁ : AffineIndependent ℝ ![A₁, B₁, C₁])
    (scalene_A₁B₁C₁ : (⟨_, affineIndependent_A₁B₁C₁⟩ : Triangle ℝ P).Scalene) :
    AffineIndependent ℝ ![B, B₁, B₂] := by
  obtain ⟨O, R, u, v, u₃, e₁, e₂, hR, he₁, he₂, he₁₂, hA, hB, hC, hA₁, hB₁, hC₁,
    hu0, hu1, hv0, hv1, hu₃0, hu₃1, hrel⟩ :=
    frontend affineIndependent_ABC equilateral_ABC A₁_mem_interior_ABC B₁_mem_interior_ABC
      C₁_mem_interior_ABC BA₁_eq_A₁C CB₁_eq_B₁A AC₁_eq_C₁B
      angle_BA₁C_add_angle_CB₁A_add_angle_AC₁B
  obtain ⟨huv, hdA, hdB⟩ :=
    scalene_params affineIndependent_ABC equilateral_ABC affineIndependent_A₁B₁C₁
      scalene_A₁B₁C₁ hR he₁ he₂ he₁₂ hA hB hC hA₁ hB₁ hC₁ hrel
  obtain ⟨hA₂, hB₂, hC₂⟩ :=
    a2b2c2_coords affineIndependent_ABC equilateral_ABC A₂_mem_inf_BC₁_CB₁
      B₂_mem_inf_CA₁_AC₁ C₂_mem_inf_AB₁_BA₁ hR he₁ he₂ he₁₂ hA hB hC hA₁ hB₁ hC₁
      ⟨hu0, hu1⟩ ⟨hv0, hv1⟩ ⟨hu₃0, hu₃1⟩ hrel ⟨huv, hdA, hdB⟩
  have hw : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsqrt3ne : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hu3nev : u₃ ≠ v := by
    intro h
    rw [h] at hrel
    have hz : u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3 = 0 := by linear_combination (-1) * hrel
    exact hdA hz
  have hu3neu : u₃ ≠ u := by
    intro h
    rw [h] at hrel
    have hz : u ^ 2 * v - u ^ 2 - 2 * u * v - 6 * u - 3 * v + 3 = 0 := by linear_combination (-1) * hrel
    exact hdB hz
  have hdenA2C : u₃ * v - u₃ - v - 3 ≠ 0 := by
    have h1 : u₃ * v < u₃ := by have h2 := mul_lt_mul_of_pos_left hv1 hu₃0; rwa [mul_one] at h2
    have h2 : u₃ * v - u₃ - v - 3 < 0 := by nlinarith only [h1, hv0]
    exact ne_of_lt h2
  have hdenB2C : u * u₃ - u - u₃ - 3 ≠ 0 := by
    have h1 : u * u₃ < u := by have h2 := mul_lt_mul_of_pos_left hu₃1 hu0; rwa [mul_one] at h2
    have h2 : u * u₃ - u - u₃ - 3 < 0 := by nlinarith only [h1, hu₃0]
    exact ne_of_lt h2
  have hdenC2C : u * v - u - v - 3 ≠ 0 := by
    have h1 : u * v < u := by have h2 := mul_lt_mul_of_pos_left hv1 hu0; rwa [mul_one] at h2
    have h2 : u * v - u - v - 3 < 0 := by nlinarith only [h1, hv0]
    exact ne_of_lt h2
  have hdenB2 : (dB2d u v u₃) ≠ 0 := by simp only [dB2d]; exact mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hdenB2C
  have hB₂' : B₂ = (((R * (u * u₃ - 5 * u + u₃ + 3)) / (dB2d u v u₃) : ℝ) • e₁ +
      ((-Real.sqrt 3 * R * (u - 3) * (u₃ - 1)) / (dB2d u v u₃) : ℝ) • e₂) +ᵥ O := by
    rw [hB₂]; simp only [dB2d]
  have inner_e1 : ∀ (px py qx qy : ℝ),
      ⟪((px • e₁ + py • e₂) +ᵥ O) -ᵥ ((qx • e₁ + qy • e₂) +ᵥ O), e₁⟫_ℝ = px - qx := by
    intro px py qx qy
    rw [vadd_vsub_vadd_cancel_right, inner_sub_left, inner_add_left, inner_add_left,
      real_inner_smul_left, real_inner_smul_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, he₁, real_inner_comm e₁ e₂, he₁₂]
    ring
  have inner_e2 : ∀ (px py qx qy : ℝ),
      ⟪((px • e₁ + py • e₂) +ᵥ O) -ᵥ ((qx • e₁ + qy • e₂) +ᵥ O), e₂⟫_ℝ = py - qy := by
    intro px py qx qy
    rw [vadd_vsub_vadd_cancel_right, inner_sub_left, inner_add_left, inner_add_left,
      real_inner_smul_left, real_inner_smul_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, he₂, he₁₂]
    ring
  -- affine independence of (B, B₁, B₂)
  have hB₁' : B₁ = ((R * (1 - v) / 4 : ℝ) • e₁ + (R * Real.sqrt 3 * (v - 1) / 4 : ℝ) • e₂) +ᵥ O := hB₁
  have hB' : B = ((-R / 2 : ℝ) • e₁ + (R * Real.sqrt 3 / 2 : ℝ) • e₂) +ᵥ O := hB
  have hcrossB : ⟪B₁ -ᵥ B, e₁⟫_ℝ * ⟪B₂ -ᵥ B, e₂⟫_ℝ - ⟪B₁ -ᵥ B, e₂⟫_ℝ * ⟪B₂ -ᵥ B, e₁⟫_ℝ ≠ 0 := by
    have e1 : ⟪B₁ -ᵥ B, e₁⟫_ℝ = R * (3 - v) / 4 := by
      rw [hB₁', hB', inner_e1]; ring
    have e2 : ⟪B₁ -ᵥ B, e₂⟫_ℝ = Real.sqrt 3 * R * (v - 3) / 4 := by
      rw [hB₁', hB', inner_e2]; ring
    have e7 : ⟪B₂ -ᵥ B, e₂⟫_ℝ = (-Real.sqrt 3 * R * (u - 3) * (u₃ - 1) / (dB2d u v u₃)) - Real.sqrt 3 * R / 2 := by
      rw [hB₂', hB', inner_e2]; ring
    have e8 : ⟪B₂ -ᵥ B, e₁⟫_ℝ = (R * (u * u₃ - 5 * u + u₃ + 3)) / (dB2d u v u₃) + R / 2 := by
      rw [hB₂', hB', inner_e1]; ring
    rw [e1, e2, e7, e8]
    have e9 : R * (3 - v) / 4 * ((-Real.sqrt 3 * R * (u - 3) * (u₃ - 1) / (dB2d u v u₃)) - Real.sqrt 3 * R / 2)
        - Real.sqrt 3 * R * (v - 3) / 4 * ((R * (u * u₃ - 5 * u + u₃ + 3)) / (dB2d u v u₃) + R / 2)
        = R ^ 2 * Real.sqrt 3 * (3 - v) * (u₃ - u) / (dB2d u v u₃) := by
      field_simp [hdenB2]
      ring
    rw [e9]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hR.ne') hsqrt3ne)
      (by nlinarith only [hv1])) (sub_ne_zero.mpr hu3neu)) hdenB2
  have hAIBB1B2 : AffineIndependent ℝ ![B, B₁, B₂] := by
    rw [affineIndependent_iff_not_collinear]
    intro hcol
    rw [collinear_iff_exists_forall_eq_smul_vadd] at hcol
    obtain ⟨p₀, w, hw⟩ := hcol
    obtain ⟨rA, hrA⟩ := hw B (Set.mem_range_self 0)
    obtain ⟨r1, hr1⟩ := hw B₁ (Set.mem_range_self 1)
    obtain ⟨r2, hr2⟩ := hw B₂ (Set.mem_range_self 2)
    have e1 : B₁ -ᵥ B = (r1 - rA) • w := by rw [hr1, hrA, vadd_vsub_vadd_cancel_right]; module
    have e2 : B₂ -ᵥ B = (r2 - rA) • w := by rw [hr2, hrA, vadd_vsub_vadd_cancel_right]; module
    rw [e1, e2, real_inner_smul_left, real_inner_smul_left, real_inner_smul_left, real_inner_smul_left] at hcrossB
    have hz : (r1 - rA) * ⟪w, e₁⟫_ℝ * ((r2 - rA) * ⟪w, e₂⟫_ℝ)
        - (r1 - rA) * ⟪w, e₂⟫_ℝ * ((r2 - rA) * ⟪w, e₁⟫_ℝ) = 0 := by ring
    exact hcrossB hz
  exact hAIBB1B2

lemma affineCC1C2L {{A B C A₁ B₁ C₁ A₂ B₂ C₂ : P}}
    (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C])
    (equilateral_ABC : (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).Equilateral)
    (A₁_mem_interior_ABC : A₁ ∈ (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).interior)
    (B₁_mem_interior_ABC : B₁ ∈ (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).interior)
    (C₁_mem_interior_ABC : C₁ ∈ (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).interior)
    (BA₁_eq_A₁C : dist B A₁ = dist A₁ C) (CB₁_eq_B₁A : dist C B₁ = dist B₁ A)
    (AC₁_eq_C₁B : dist A C₁ = dist C₁ B)
    (angle_BA₁C_add_angle_CB₁A_add_angle_AC₁B :
      ∠ B A₁ C + ∠ C B₁ A + ∠ A C₁ B = 8 / 3 * π)
    (A₂_mem_inf_BC₁_CB₁ : A₂ ∈ line[ℝ, B, C₁] ⊓ line[ℝ, C, B₁])
    (B₂_mem_inf_CA₁_AC₁ : B₂ ∈ line[ℝ, C, A₁] ⊓ line[ℝ, A, C₁])
    (C₂_mem_inf_AB₁_BA₁ : C₂ ∈ line[ℝ, A, B₁] ⊓ line[ℝ, B, A₁])
    (affineIndependent_A₁B₁C₁ : AffineIndependent ℝ ![A₁, B₁, C₁])
    (scalene_A₁B₁C₁ : (⟨_, affineIndependent_A₁B₁C₁⟩ : Triangle ℝ P).Scalene) :
    AffineIndependent ℝ ![C, C₁, C₂] := by
  obtain ⟨O, R, u, v, u₃, e₁, e₂, hR, he₁, he₂, he₁₂, hA, hB, hC, hA₁, hB₁, hC₁,
    hu0, hu1, hv0, hv1, hu₃0, hu₃1, hrel⟩ :=
    frontend affineIndependent_ABC equilateral_ABC A₁_mem_interior_ABC B₁_mem_interior_ABC
      C₁_mem_interior_ABC BA₁_eq_A₁C CB₁_eq_B₁A AC₁_eq_C₁B
      angle_BA₁C_add_angle_CB₁A_add_angle_AC₁B
  obtain ⟨huv, hdA, hdB⟩ :=
    scalene_params affineIndependent_ABC equilateral_ABC affineIndependent_A₁B₁C₁
      scalene_A₁B₁C₁ hR he₁ he₂ he₁₂ hA hB hC hA₁ hB₁ hC₁ hrel
  obtain ⟨hA₂, hB₂, hC₂⟩ :=
    a2b2c2_coords affineIndependent_ABC equilateral_ABC A₂_mem_inf_BC₁_CB₁
      B₂_mem_inf_CA₁_AC₁ C₂_mem_inf_AB₁_BA₁ hR he₁ he₂ he₁₂ hA hB hC hA₁ hB₁ hC₁
      ⟨hu0, hu1⟩ ⟨hv0, hv1⟩ ⟨hu₃0, hu₃1⟩ hrel ⟨huv, hdA, hdB⟩
  have hw : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsqrt3ne : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hu3nev : u₃ ≠ v := by
    intro h
    rw [h] at hrel
    have hz : u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3 = 0 := by linear_combination (-1) * hrel
    exact hdA hz
  have hu3neu : u₃ ≠ u := by
    intro h
    rw [h] at hrel
    have hz : u ^ 2 * v - u ^ 2 - 2 * u * v - 6 * u - 3 * v + 3 = 0 := by linear_combination (-1) * hrel
    exact hdB hz
  have hdenA2C : u₃ * v - u₃ - v - 3 ≠ 0 := by
    have h1 : u₃ * v < u₃ := by have h2 := mul_lt_mul_of_pos_left hv1 hu₃0; rwa [mul_one] at h2
    have h2 : u₃ * v - u₃ - v - 3 < 0 := by nlinarith only [h1, hv0]
    exact ne_of_lt h2
  have hdenB2C : u * u₃ - u - u₃ - 3 ≠ 0 := by
    have h1 : u * u₃ < u := by have h2 := mul_lt_mul_of_pos_left hu₃1 hu0; rwa [mul_one] at h2
    have h2 : u * u₃ - u - u₃ - 3 < 0 := by nlinarith only [h1, hu₃0]
    exact ne_of_lt h2
  have hdenC2C : u * v - u - v - 3 ≠ 0 := by
    have h1 : u * v < u := by have h2 := mul_lt_mul_of_pos_left hv1 hu0; rwa [mul_one] at h2
    have h2 : u * v - u - v - 3 < 0 := by nlinarith only [h1, hv0]
    exact ne_of_lt h2
  have hdenC2 : (dC2d u v) ≠ 0 := by simp only [dC2d]; exact mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hdenC2C
  have hC₂' : C₂ = (((R * (u * v - 5 * u + v + 3)) / (dC2d u v) : ℝ) • e₁ +
      ((Real.sqrt 3 * R * (u - 3) * (v - 1)) / (dC2d u v) : ℝ) • e₂) +ᵥ O := by
    rw [hC₂]; simp only [dC2d]
  have inner_e1 : ∀ (px py qx qy : ℝ),
      ⟪((px • e₁ + py • e₂) +ᵥ O) -ᵥ ((qx • e₁ + qy • e₂) +ᵥ O), e₁⟫_ℝ = px - qx := by
    intro px py qx qy
    rw [vadd_vsub_vadd_cancel_right, inner_sub_left, inner_add_left, inner_add_left,
      real_inner_smul_left, real_inner_smul_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, he₁, real_inner_comm e₁ e₂, he₁₂]
    ring
  have inner_e2 : ∀ (px py qx qy : ℝ),
      ⟪((px • e₁ + py • e₂) +ᵥ O) -ᵥ ((qx • e₁ + qy • e₂) +ᵥ O), e₂⟫_ℝ = py - qy := by
    intro px py qx qy
    rw [vadd_vsub_vadd_cancel_right, inner_sub_left, inner_add_left, inner_add_left,
      real_inner_smul_left, real_inner_smul_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, he₂, he₁₂]
    ring
  -- affine independence of (C, C₁, C₂)
  have hC₁' : C₁ = ((R * (1 - u₃) / 4 : ℝ) • e₁ + (R * Real.sqrt 3 * (1 - u₃) / 4 : ℝ) • e₂) +ᵥ O := hC₁
  have hC' : C = ((-R / 2 : ℝ) • e₁ + (-R * Real.sqrt 3 / 2 : ℝ) • e₂) +ᵥ O := hC
  have hcrossC : ⟪C₁ -ᵥ C, e₁⟫_ℝ * ⟪C₂ -ᵥ C, e₂⟫_ℝ - ⟪C₁ -ᵥ C, e₂⟫_ℝ * ⟪C₂ -ᵥ C, e₁⟫_ℝ ≠ 0 := by
    have e1 : ⟪C₁ -ᵥ C, e₁⟫_ℝ = R * (3 - u₃) / 4 := by
      rw [hC₁', hC', inner_e1]; ring
    have e2 : ⟪C₁ -ᵥ C, e₂⟫_ℝ = Real.sqrt 3 * R * (3 - u₃) / 4 := by
      rw [hC₁', hC', inner_e2]; ring
    have e7 : ⟪C₂ -ᵥ C, e₂⟫_ℝ = (Real.sqrt 3 * R * (u - 3) * (v - 1) / (dC2d u v)) + Real.sqrt 3 * R / 2 := by
      rw [hC₂', hC', inner_e2]; ring
    have e8 : ⟪C₂ -ᵥ C, e₁⟫_ℝ = (R * (u * v - 5 * u + v + 3)) / (dC2d u v) + R / 2 := by
      rw [hC₂', hC', inner_e1]; ring
    rw [e1, e2, e7, e8]
    have e9 : R * (3 - u₃) / 4 * ((Real.sqrt 3 * R * (u - 3) * (v - 1) / (dC2d u v)) + Real.sqrt 3 * R / 2)
        - Real.sqrt 3 * R * (3 - u₃) / 4 * ((R * (u * v - 5 * u + v + 3)) / (dC2d u v) + R / 2)
        = R ^ 2 * Real.sqrt 3 * (3 - u₃) * (u - v) / (dC2d u v) := by
      field_simp [hdenC2]
      ring
    rw [e9]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hR.ne') hsqrt3ne)
      (by nlinarith only [hu₃1])) (sub_ne_zero.mpr huv)) hdenC2
  have hAICC1C2 : AffineIndependent ℝ ![C, C₁, C₂] := by
    rw [affineIndependent_iff_not_collinear]
    intro hcol
    rw [collinear_iff_exists_forall_eq_smul_vadd] at hcol
    obtain ⟨p₀, w, hw⟩ := hcol
    obtain ⟨rA, hrA⟩ := hw C (Set.mem_range_self 0)
    obtain ⟨r1, hr1⟩ := hw C₁ (Set.mem_range_self 1)
    obtain ⟨r2, hr2⟩ := hw C₂ (Set.mem_range_self 2)
    have e1 : C₁ -ᵥ C = (r1 - rA) • w := by rw [hr1, hrA, vadd_vsub_vadd_cancel_right]; module
    have e2 : C₂ -ᵥ C = (r2 - rA) • w := by rw [hr2, hrA, vadd_vsub_vadd_cancel_right]; module
    rw [e1, e2, real_inner_smul_left, real_inner_smul_left, real_inner_smul_left, real_inner_smul_left] at hcrossC
    have hz : (r1 - rA) * ⟪w, e₁⟫_ℝ * ((r2 - rA) * ⟪w, e₂⟫_ℝ)
        - (r1 - rA) * ⟪w, e₂⟫_ℝ * ((r2 - rA) * ⟪w, e₁⟫_ℝ) = 0 := by ring
    exact hcrossC hz
  exact hAICC1C2
snip end

problem imo2023_p6 {A B C A₁ B₁ C₁ A₂ B₂ C₂ : P}
    (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C])
    (equilateral_ABC : (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).Equilateral)
    (A₁_mem_interior_ABC : A₁ ∈ (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).interior)
    (B₁_mem_interior_ABC : B₁ ∈ (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).interior)
    (C₁_mem_interior_ABC : C₁ ∈ (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).interior)
    (BA₁_eq_A₁C : dist B A₁ = dist A₁ C) (CB₁_eq_B₁A : dist C B₁ = dist B₁ A)
    (AC₁_eq_C₁B : dist A C₁ = dist C₁ B)
    (angle_BA₁C_add_angle_CB₁A_add_angle_AC₁B :
      ∠ B A₁ C + ∠ C B₁ A + ∠ A C₁ B = 8 / 3 * π)
    (A₂_mem_inf_BC₁_CB₁ : A₂ ∈ line[ℝ, B, C₁] ⊓ line[ℝ, C, B₁])
    (B₂_mem_inf_CA₁_AC₁ : B₂ ∈ line[ℝ, C, A₁] ⊓ line[ℝ, A, C₁])
    (C₂_mem_inf_AB₁_BA₁ : C₂ ∈ line[ℝ, A, B₁] ⊓ line[ℝ, B, A₁])
    (affineIndependent_A₁B₁C₁ : AffineIndependent ℝ ![A₁, B₁, C₁])
    (scalene_A₁B₁C₁ : (⟨_, affineIndependent_A₁B₁C₁⟩ : Triangle ℝ P).Scalene) :
    ∃ affineIndependent_AA₁A₂ : AffineIndependent ℝ ![A, A₁, A₂],
    ∃ affineIndependent_BB₁B₂ : AffineIndependent ℝ ![B, B₁, B₂],
    ∃ affineIndependent_CC₁C₂ : AffineIndependent ℝ ![C, C₁, C₂],
    2 ≤ #((⟨_, affineIndependent_AA₁A₂⟩ : Triangle ℝ P).circumsphere ∩
          (⟨_, affineIndependent_BB₁B₂⟩ : Triangle ℝ P).circumsphere ∩
          (⟨_, affineIndependent_CC₁C₂⟩ : Triangle ℝ P).circumsphere : Set P) := by
  obtain ⟨O, R, u, v, u₃, e₁, e₂, hR, he₁, he₂, he₁₂, hA, hB, hC, hA₁, hB₁, hC₁,
    hu0, hu1, hv0, hv1, hu₃0, hu₃1, hrel⟩ :=
    frontend affineIndependent_ABC equilateral_ABC A₁_mem_interior_ABC B₁_mem_interior_ABC
      C₁_mem_interior_ABC BA₁_eq_A₁C CB₁_eq_B₁A AC₁_eq_C₁B
      angle_BA₁C_add_angle_CB₁A_add_angle_AC₁B
  obtain ⟨huv, hdA, hdB⟩ :=
    scalene_params affineIndependent_ABC equilateral_ABC affineIndependent_A₁B₁C₁
      scalene_A₁B₁C₁ hR he₁ he₂ he₁₂ hA hB hC hA₁ hB₁ hC₁ hrel
  obtain ⟨hA₂, hB₂, hC₂⟩ :=
    a2b2c2_coords affineIndependent_ABC equilateral_ABC A₂_mem_inf_BC₁_CB₁
      B₂_mem_inf_CA₁_AC₁ C₂_mem_inf_AB₁_BA₁ hR he₁ he₂ he₁₂ hA hB hC hA₁ hB₁ hC₁
      ⟨hu0, hu1⟩ ⟨hv0, hv1⟩ ⟨hu₃0, hu₃1⟩ hrel ⟨huv, hdA, hdB⟩
  have hw : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsqrt3ne : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hu3nev : u₃ ≠ v := by
    intro h
    rw [h] at hrel
    have hz : u * v ^ 2 - 2 * u * v - 3 * u - v ^ 2 - 6 * v + 3 = 0 := by linear_combination (-1) * hrel
    exact hdA hz
  have hu3neu : u₃ ≠ u := by
    intro h
    rw [h] at hrel
    have hz : u ^ 2 * v - u ^ 2 - 2 * u * v - 6 * u - 3 * v + 3 = 0 := by linear_combination (-1) * hrel
    exact hdB hz
  have hdenA2C : u₃ * v - u₃ - v - 3 ≠ 0 := by
    have h1 : u₃ * v < u₃ := by have h2 := mul_lt_mul_of_pos_left hv1 hu₃0; rwa [mul_one] at h2
    have h2 : u₃ * v - u₃ - v - 3 < 0 := by nlinarith only [h1, hv0]
    exact ne_of_lt h2
  have hdenB2C : u * u₃ - u - u₃ - 3 ≠ 0 := by
    have h1 : u * u₃ < u := by have h2 := mul_lt_mul_of_pos_left hu₃1 hu0; rwa [mul_one] at h2
    have h2 : u * u₃ - u - u₃ - 3 < 0 := by nlinarith only [h1, hu₃0]
    exact ne_of_lt h2
  have hdenC2C : u * v - u - v - 3 ≠ 0 := by
    have h1 : u * v < u := by have h2 := mul_lt_mul_of_pos_left hv1 hu0; rwa [mul_one] at h2
    have h2 : u * v - u - v - 3 < 0 := by nlinarith only [h1, hv0]
    exact ne_of_lt h2
  have hdenA2 : (dA2d u₃ v) ≠ 0 := by simp only [dA2d]; exact hdenA2C
  have hdenB2 : (dB2d u v u₃) ≠ 0 := by simp only [dB2d]; exact mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hdenB2C
  have hdenC2 : (dC2d u v) ≠ 0 := by simp only [dC2d]; exact mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hdenC2C

  have hsigA : (sigAd u v) ≠ 0 := by
    simp only [sigAd]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by positivity : (0:ℝ) < v ^ 2 + 3).ne') hdA
  have hsigB : (sigBd u v) ≠ 0 := by
    simp only [sigBd]
    exact mul_ne_zero (mul_ne_zero (by norm_num : (24:ℝ) ≠ 0)
      (by positivity : (0:ℝ) < u ^ 2 + 3).ne') hdB
  have hsigC : (sigCd u v) ≠ 0 := by
    simp only [sigCd]
    exact mul_ne_zero (mul_ne_zero (by norm_num : (6:ℝ) ≠ 0) (sub_ne_zero.mpr huv))
      (pow_ne_zero 3 hdenC2C)

  have incAA := incAA u v R
  have incAA1 := incAA1 u v R
  have incAA2 := incAA2 u v u₃ R hw hrel hdenA2C
  have incBB := incBB u v R hw
  have incBB1 := incBB1 u v R hw
  have incBB2 := incBB2 u v u₃ R hw hrel (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hdenB2C)
  have incCC := incCC u v R hw
  have incCC1 := incCC1 u v u₃ R hw hrel
  have incCC2 := incCC2 u v u₃ R hw hrel (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hdenC2C)
  have hradB := hradBL u v R
  have hradC := hradCL u v R
  have hcoaxx := hcoaxxL u v R
  have hcoaxy := hcoaxyL u v R
  have hcoaxc := hcoaxcL u v R
  have hepsA2eq := hepsA2eqL u v R hw
  have hbe2eq := hbe2eqL u v R hw
  have hbeepseq := hbeepseqL u v R hw
  have hF4b := hF4bL u v R
  have hnn0eq := hnn0eqL u v R hF4b
  have htrhoeq := htrhoeqL u v R
  have hRtmp0eq := hRtmp0eqL u v R
  have hF4 := hF4L u v R
  have BIGID := bigidL u v R hF4
  have hQ3 := q3negL hu0 hu1 hv0 hv1 hu₃0 hrel
  obtain ⟨hsqNpos, hnn0pos, hSpos, hS2, hnn, hBIG2, hsqformA⟩ :=
    sqSfactsL u v u₃ R hR hu0 hu1 hv0 hv1 hu₃0 hu₃1 hrel huv hdA hdB
  have hdist12 := distP12L u v u₃ R hR hu0 hu1 hv0 hv1 hu₃0 hu₃1 hrel huv hdA hdB hS2 hnn hBIG2 hnn0pos
  have hline12 := lineP12L u v u₃ R hR hu0 hu1 hv0 hv1 hu₃0 hu₃1 hrel huv hdA hdB hnn hnn0pos
  obtain ⟨hP1omegaA, hP2omegaA, hP1omegaB, hP2omegaB, hP1omegaC, hP2omegaC⟩ :=
    omegaP12L u v u₃ R hR hu0 hu1 hv0 hv1 hu₃0 hu₃1 hrel huv hdA hdB hsqformA hdist12.1 hdist12.2 hline12.1 hline12.2
  have hAIAA1A2 := affineAA1A2L affineIndependent_ABC equilateral_ABC A₁_mem_interior_ABC B₁_mem_interior_ABC
      C₁_mem_interior_ABC BA₁_eq_A₁C CB₁_eq_B₁A AC₁_eq_C₁B
      angle_BA₁C_add_angle_CB₁A_add_angle_AC₁B
      A₂_mem_inf_BC₁_CB₁ B₂_mem_inf_CA₁_AC₁ C₂_mem_inf_AB₁_BA₁
      affineIndependent_A₁B₁C₁ scalene_A₁B₁C₁
  have hAIBB1B2 := affineBB1B2L affineIndependent_ABC equilateral_ABC A₁_mem_interior_ABC B₁_mem_interior_ABC
      C₁_mem_interior_ABC BA₁_eq_A₁C CB₁_eq_B₁A AC₁_eq_C₁B
      angle_BA₁C_add_angle_CB₁A_add_angle_AC₁B
      A₂_mem_inf_BC₁_CB₁ B₂_mem_inf_CA₁_AC₁ C₂_mem_inf_AB₁_BA₁
      affineIndependent_A₁B₁C₁ scalene_A₁B₁C₁
  have hAICC1C2 := affineCC1C2L affineIndependent_ABC equilateral_ABC A₁_mem_interior_ABC B₁_mem_interior_ABC
      C₁_mem_interior_ABC BA₁_eq_A₁C CB₁_eq_B₁A AC₁_eq_C₁B
      angle_BA₁C_add_angle_CB₁A_add_angle_AC₁B
      A₂_mem_inf_BC₁_CB₁ B₂_mem_inf_CA₁_AC₁ C₂_mem_inf_AB₁_BA₁
      affineIndependent_A₁B₁C₁ scalene_A₁B₁C₁
  have hA₂' : A₂ = (((-R * (u₃ * v - 2 * u₃ - 2 * v + 3)) / (dA2d u₃ v) : ℝ) • e₁ +
      ((Real.sqrt 3 * R * (u₃ - v)) / (dA2d u₃ v) : ℝ) • e₂) +ᵥ O := by
    rw [hA₂]; simp only [dA2d]
  have hB₂' : B₂ = (((R * (u * u₃ - 5 * u + u₃ + 3)) / (dB2d u v u₃) : ℝ) • e₁ +
      ((-Real.sqrt 3 * R * (u - 3) * (u₃ - 1)) / (dB2d u v u₃) : ℝ) • e₂) +ᵥ O := by
    rw [hB₂]; simp only [dB2d]
  have hC₂' : C₂ = (((R * (u * v - 5 * u + v + 3)) / (dC2d u v) : ℝ) • e₁ +
      ((Real.sqrt 3 * R * (u - 3) * (v - 1)) / (dC2d u v) : ℝ) • e₂) +ᵥ O := by
    rw [hC₂]; simp only [dC2d]
  -- helpers for inner products of coordinate differences
  have inner_e1 : ∀ (px py qx qy : ℝ),
      ⟪((px • e₁ + py • e₂) +ᵥ O) -ᵥ ((qx • e₁ + qy • e₂) +ᵥ O), e₁⟫_ℝ = px - qx := by
    intro px py qx qy
    rw [vadd_vsub_vadd_cancel_right, inner_sub_left, inner_add_left, inner_add_left,
      real_inner_smul_left, real_inner_smul_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, he₁, real_inner_comm e₁ e₂, he₁₂]
    ring
  have inner_e2 : ∀ (px py qx qy : ℝ),
      ⟪((px • e₁ + py • e₂) +ᵥ O) -ᵥ ((qx • e₁ + qy • e₂) +ᵥ O), e₂⟫_ℝ = py - qy := by
    intro px py qx qy
    rw [vadd_vsub_vadd_cancel_right, inner_sub_left, inner_add_left, inner_add_left,
      real_inner_smul_left, real_inner_smul_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, he₂, he₁₂]
    ring
  have hA' : A = ((R : ℝ) • e₁ + (0 : ℝ) • e₂) +ᵥ O := by rw [hA]; simp only [zero_smul, add_zero]
  have hA₁' : A₁ = ((R * (u - 1) / 2 : ℝ) • e₁ + (0 : ℝ) • e₂) +ᵥ O := by rw [hA₁]; simp only [zero_smul, add_zero]
  -- affine independence of (B, B₁, B₂)
  have hB₁' : B₁ = ((R * (1 - v) / 4 : ℝ) • e₁ + (R * Real.sqrt 3 * (v - 1) / 4 : ℝ) • e₂) +ᵥ O := hB₁
  have hB' : B = ((-R / 2 : ℝ) • e₁ + (R * Real.sqrt 3 / 2 : ℝ) • e₂) +ᵥ O := hB
  -- affine independence of (C, C₁, C₂)
  have hC₁' : C₁ = ((R * (1 - u₃) / 4 : ℝ) • e₁ + (R * Real.sqrt 3 * (1 - u₃) / 4 : ℝ) • e₂) +ᵥ O := hC₁
  have hC' : C = ((-R / 2 : ℝ) • e₁ + (-R * Real.sqrt 3 / 2 : ℝ) • e₂) +ᵥ O := hC
  -- the two points as elements of P
  set P1pt : P := (((P1xd u v R) • e₁ + (P1yd u v R) • e₂) +ᵥ O) with hP1pt
  set P2pt : P := (((P2xd u v R) • e₁ + (P2yd u v R) • e₂) +ᵥ O) with hP2pt
  have hP1neP2 : P1pt ≠ P2pt := by
    have hdist : dist P1pt P2pt ^ 2 = 4 * (Sd u v R) ^ 2 * (nn0d u v R) := by
      rw [hP1pt, hP2pt, coord_dist_sq he₁ he₂ he₁₂]; simp only [P1xd, P1yd, P2xd, P2yd]
      linear_combination 4 * (Sd u v R) ^ 2 * hnn
    intro h
    rw [h, dist_self] at hdist
    have hz : 0 < 4 * (Sd u v R) ^ 2 * (nn0d u v R) := by positivity
    linarith [hz, hdist]
  -- generic membership transport for each circle
  have hmemA : ∀ (x y : ℝ), (sigAd u v) * (x ^ 2 + y ^ 2) + (delAd u v R) * x + (epsAd u v R) * y + (phiAd u v R) = 0 →
      dist ((x • e₁ + y • e₂) +ᵥ O)
        (((-(delAd u v R) / (2 * (sigAd u v))) • e₁ + (-(epsAd u v R) / (2 * (sigAd u v))) • e₂) +ᵥ O) = dist A
        (((-(delAd u v R) / (2 * (sigAd u v))) • e₁ + (-(epsAd u v R) / (2 * (sigAd u v))) • e₂) +ᵥ O) := by
    intro x y hO
    have h1 : dist ((x • e₁ + y • e₂) +ᵥ O)
        (((-(delAd u v R) / (2 * (sigAd u v))) • e₁ + (-(epsAd u v R) / (2 * (sigAd u v))) • e₂) +ᵥ O) ^ 2 = (RA2d u v R) := by
      rw [coord_dist_sq he₁ he₂ he₁₂]
      have h2 := hsqformA x y
      rw [hO] at h2
      rcases mul_eq_zero.1 h2.symm with h3 | h3
      · exact absurd h3 hsigA
      · simp only [caxd, cayd] at h3; linear_combination h3
    have h2 : dist A (((-(delAd u v R) / (2 * (sigAd u v))) • e₁ + (-(epsAd u v R) / (2 * (sigAd u v))) • e₂) +ᵥ O) ^ 2 = (RA2d u v R) := by
      rw [hA', coord_dist_sq he₁ he₂ he₁₂]
      have incAAf : (sigAd u v) * (R ^ 2 + 0 ^ 2) + (delAd u v R) * R + (epsAd u v R) * 0 + (phiAd u v R) = 0 := incAA
      have h4 := hsqformA R 0
      rw [incAAf] at h4
      rcases mul_eq_zero.1 h4.symm with h3 | h3
      · exact absurd h3 hsigA
      · simp only [caxd, cayd] at h3; linear_combination h3
    have h3 : dist ((x • e₁ + y • e₂) +ᵥ O)
        (((-(delAd u v R) / (2 * (sigAd u v))) • e₁ + (-(epsAd u v R) / (2 * (sigAd u v))) • e₂) +ᵥ O) ^ 2
        = dist A (((-(delAd u v R) / (2 * (sigAd u v))) • e₁ + (-(epsAd u v R) / (2 * (sigAd u v))) • e₂) +ᵥ O) ^ 2 := by
      rw [h1, h2]
    exact (sq_eq_sq₀ dist_nonneg dist_nonneg).mp h3
  have hmemB : ∀ (x y : ℝ), (sigBd u v) * (x ^ 2 + y ^ 2) + (delBd u v R) * x + (epsBd u v R) * y + (phiBd u v R) = 0 →
      dist ((x • e₁ + y • e₂) +ᵥ O)
        (((-(delBd u v R) / (2 * (sigBd u v))) • e₁ + (-(epsBd u v R) / (2 * (sigBd u v))) • e₂) +ᵥ O) = dist B
        (((-(delBd u v R) / (2 * (sigBd u v))) • e₁ + (-(epsBd u v R) / (2 * (sigBd u v))) • e₂) +ᵥ O) := by
    intro x y hO
    set RB2 : ℝ := ((delBd u v R) ^ 2 + (epsBd u v R) ^ 2 - 4 * (sigBd u v) * (phiBd u v R)) / (4 * (sigBd u v) ^ 2) with hRB2
    have hsqformB : ∀ x y : ℝ, (sigBd u v) * (x ^ 2 + y ^ 2) + (delBd u v R) * x + (epsBd u v R) * y + (phiBd u v R)
        = (sigBd u v) * ((x + (delBd u v R) / (2 * (sigBd u v))) ^ 2 + (y + (epsBd u v R) / (2 * (sigBd u v))) ^ 2 - RB2) := by
      intro x' y'
      exact sqform_aux2 _ _ _ _ _ _ _ hsigB hRB2
    have h1 : dist ((x • e₁ + y • e₂) +ᵥ O)
        (((-(delBd u v R) / (2 * (sigBd u v))) • e₁ + (-(epsBd u v R) / (2 * (sigBd u v))) • e₂) +ᵥ O) ^ 2 = RB2 := by
      rw [coord_dist_sq he₁ he₂ he₁₂]
      have h2 := hsqformB x y
      rw [hO] at h2
      rcases mul_eq_zero.1 h2.symm with h3 | h3
      · exact absurd h3 hsigB
      · linear_combination h3
    have h2 : dist B (((-(delBd u v R) / (2 * (sigBd u v))) • e₁ + (-(epsBd u v R) / (2 * (sigBd u v))) • e₂) +ᵥ O) ^ 2 = RB2 := by
      rw [hB', coord_dist_sq he₁ he₂ he₁₂]
      have incBBf : (sigBd u v) * ((-R / 2) ^ 2 + (R * Real.sqrt 3 / 2) ^ 2) + (delBd u v R) * (-R / 2) + (epsBd u v R) * (R * Real.sqrt 3 / 2) + (phiBd u v R) = 0 := by
        exact incBB
      have h4 := hsqformB (-R / 2) (R * Real.sqrt 3 / 2)
      rw [incBBf] at h4
      rcases mul_eq_zero.1 h4.symm with h3 | h3
      · exact absurd h3 hsigB
      · linear_combination h3
    have h3 : dist ((x • e₁ + y • e₂) +ᵥ O)
        (((-(delBd u v R) / (2 * (sigBd u v))) • e₁ + (-(epsBd u v R) / (2 * (sigBd u v))) • e₂) +ᵥ O) ^ 2
        = dist B (((-(delBd u v R) / (2 * (sigBd u v))) • e₁ + (-(epsBd u v R) / (2 * (sigBd u v))) • e₂) +ᵥ O) ^ 2 := by
      rw [h1, h2]
    exact (sq_eq_sq₀ dist_nonneg dist_nonneg).mp h3
  have hmemC : ∀ (x y : ℝ), (sigCd u v) * (x ^ 2 + y ^ 2) + (delCd u v R) * x + (epsCd u v R) * y + (phiCd u v R) = 0 →
      dist ((x • e₁ + y • e₂) +ᵥ O)
        (((-(delCd u v R) / (2 * (sigCd u v))) • e₁ + (-(epsCd u v R) / (2 * (sigCd u v))) • e₂) +ᵥ O) = dist C
        (((-(delCd u v R) / (2 * (sigCd u v))) • e₁ + (-(epsCd u v R) / (2 * (sigCd u v))) • e₂) +ᵥ O) := by
    intro x y hO
    set RC2 : ℝ := ((delCd u v R) ^ 2 + (epsCd u v R) ^ 2 - 4 * (sigCd u v) * (phiCd u v R)) / (4 * (sigCd u v) ^ 2) with hRC2
    have hsqformC : ∀ x y : ℝ, (sigCd u v) * (x ^ 2 + y ^ 2) + (delCd u v R) * x + (epsCd u v R) * y + (phiCd u v R)
        = (sigCd u v) * ((x + (delCd u v R) / (2 * (sigCd u v))) ^ 2 + (y + (epsCd u v R) / (2 * (sigCd u v))) ^ 2 - RC2) := by
      intro x' y'
      exact sqform_aux2 _ _ _ _ _ _ _ hsigC hRC2
    have h1 : dist ((x • e₁ + y • e₂) +ᵥ O)
        (((-(delCd u v R) / (2 * (sigCd u v))) • e₁ + (-(epsCd u v R) / (2 * (sigCd u v))) • e₂) +ᵥ O) ^ 2 = RC2 := by
      rw [coord_dist_sq he₁ he₂ he₁₂]
      have h2 := hsqformC x y
      rw [hO] at h2
      rcases mul_eq_zero.1 h2.symm with h3 | h3
      · exact absurd h3 hsigC
      · linear_combination h3
    have h2 : dist C (((-(delCd u v R) / (2 * (sigCd u v))) • e₁ + (-(epsCd u v R) / (2 * (sigCd u v))) • e₂) +ᵥ O) ^ 2 = RC2 := by
      rw [hC', coord_dist_sq he₁ he₂ he₁₂]
      have incCCf : (sigCd u v) * ((-R / 2) ^ 2 + (-R * Real.sqrt 3 / 2) ^ 2) + (delCd u v R) * (-R / 2) + (epsCd u v R) * (-R * Real.sqrt 3 / 2) + (phiCd u v R) = 0 := by
        exact incCC
      have h4 := hsqformC (-R / 2) (-R * Real.sqrt 3 / 2)
      rw [incCCf] at h4
      rcases mul_eq_zero.1 h4.symm with h3 | h3
      · exact absurd h3 hsigC
      · linear_combination h3
    have h3 : dist ((x • e₁ + y • e₂) +ᵥ O)
        (((-(delCd u v R) / (2 * (sigCd u v))) • e₁ + (-(epsCd u v R) / (2 * (sigCd u v))) • e₂) +ᵥ O) ^ 2
        = dist C (((-(delCd u v R) / (2 * (sigCd u v))) • e₁ + (-(epsCd u v R) / (2 * (sigCd u v))) • e₂) +ᵥ O) ^ 2 := by
      rw [h1, h2]
    exact (sq_eq_sq₀ dist_nonneg dist_nonneg).mp h3
  have incAA1f : (sigAd u v) * ((R * (u - 1) / 2) ^ 2 + (0) ^ 2) + (delAd u v R) * (R * (u - 1) / 2) + (epsAd u v R) * 0 + (phiAd u v R) = 0 := by
    exact incAA1
  have incAA2f : (sigAd u v) * (((-R * (u₃ * v - 2 * u₃ - 2 * v + 3)) / (u₃ * v - u₃ - v - 3)) ^ 2 + ((Real.sqrt 3 * R * (u₃ - v)) / (u₃ * v - u₃ - v - 3)) ^ 2) + (delAd u v R) * ((-R * (u₃ * v - 2 * u₃ - 2 * v + 3)) / (u₃ * v - u₃ - v - 3)) + (epsAd u v R) * ((Real.sqrt 3 * R * (u₃ - v)) / (u₃ * v - u₃ - v - 3)) + (phiAd u v R) = 0 := by
    exact incAA2
  have incBB1f : (sigBd u v) * ((R * (1 - v) / 4) ^ 2 + (R * Real.sqrt 3 * (v - 1) / 4) ^ 2) + (delBd u v R) * (R * (1 - v) / 4) + (epsBd u v R) * (R * Real.sqrt 3 * (v - 1) / 4) + (phiBd u v R) = 0 := by
    exact incBB1
  have incBB2f : (sigBd u v) * (((R * (u * u₃ - 5 * u + u₃ + 3)) / (2 * (u * u₃ - u - u₃ - 3))) ^ 2 + ((-Real.sqrt 3 * R * (u - 3) * (u₃ - 1)) / (2 * (u * u₃ - u - u₃ - 3))) ^ 2) + (delBd u v R) * ((R * (u * u₃ - 5 * u + u₃ + 3)) / (2 * (u * u₃ - u - u₃ - 3))) + (epsBd u v R) * ((-Real.sqrt 3 * R * (u - 3) * (u₃ - 1)) / (2 * (u * u₃ - u - u₃ - 3))) + (phiBd u v R) = 0 := by
    exact incBB2
  have incCC1f : (sigCd u v) * ((R * (1 - u₃) / 4) ^ 2 + (R * Real.sqrt 3 * (1 - u₃) / 4) ^ 2) + (delCd u v R) * (R * (1 - u₃) / 4) + (epsCd u v R) * (R * Real.sqrt 3 * (1 - u₃) / 4) + (phiCd u v R) = 0 := by
    exact incCC1
  have incCC2f : (sigCd u v) * (((R * (u * v - 5 * u + v + 3)) / (2 * (u * v - u - v - 3))) ^ 2 + ((Real.sqrt 3 * R * (u - 3) * (v - 1)) / (2 * (u * v - u - v - 3))) ^ 2) + (delCd u v R) * ((R * (u * v - 5 * u + v + 3)) / (2 * (u * v - u - v - 3))) + (epsCd u v R) * ((Real.sqrt 3 * R * (u - 3) * (v - 1)) / (2 * (u * v - u - v - 3))) + (phiCd u v R) = 0 := by
    exact incCC2
  -- circumcenters and circumradii via uniqueness
  have : FiniteDimensional ℝ V := .of_fact_finrank_eq_two
  have hspanA : affineSpan ℝ (Set.range (⟨_, hAIAA1A2⟩ : Triangle ℝ P).points) = ⊤ := by
    rw [AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one hAIAA1A2,
      Fintype.card_fin, (Fact.out : finrank ℝ V = 2)]
  have : FiniteDimensional ℝ V := .of_fact_finrank_eq_two
  have hspanB : affineSpan ℝ (Set.range (⟨_, hAIBB1B2⟩ : Triangle ℝ P).points) = ⊤ := by
    rw [AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one hAIBB1B2,
      Fintype.card_fin, (Fact.out : finrank ℝ V = 2)]
  have : FiniteDimensional ℝ V := .of_fact_finrank_eq_two
  have hspanC : affineSpan ℝ (Set.range (⟨_, hAICC1C2⟩ : Triangle ℝ P).points) = ⊤ := by
    rw [AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one hAICC1C2,
      Fintype.card_fin, (Fact.out : finrank ℝ V = 2)]
  have hcenA : (((-(delAd u v R) / (2 * (sigAd u v))) • e₁ + (-(epsAd u v R) / (2 * (sigAd u v))) • e₂) +ᵥ O)
      = (⟨_, hAIAA1A2⟩ : Triangle ℝ P).circumcenter := by
    apply Affine.Simplex.eq_circumcenter_of_dist_eq _ (by rw [hspanA]; exact AffineSubspace.mem_top ℝ V _) (r := dist A (((-(delAd u v R) / (2 * (sigAd u v))) • e₁ + (-(epsAd u v R) / (2 * (sigAd u v))) • e₂) +ᵥ O))
    intro i
    fin_cases i
    ·       rfl
    · show dist A₁ (((-(delAd u v R) / (2 * (sigAd u v))) • e₁ + (-(epsAd u v R) / (2 * (sigAd u v))) • e₂) +ᵥ O) = dist A (((-(delAd u v R) / (2 * (sigAd u v))) • e₁ + (-(epsAd u v R) / (2 * (sigAd u v))) • e₂) +ᵥ O)
      rw [hA₁']
      exact hmemA _ _ incAA1f
    · show dist A₂ (((-(delAd u v R) / (2 * (sigAd u v))) • e₁ + (-(epsAd u v R) / (2 * (sigAd u v))) • e₂) +ᵥ O) = dist A (((-(delAd u v R) / (2 * (sigAd u v))) • e₁ + (-(epsAd u v R) / (2 * (sigAd u v))) • e₂) +ᵥ O)
      rw [hA₂']
      exact hmemA _ _ incAA2f
  have hcenB : (((-(delBd u v R) / (2 * (sigBd u v))) • e₁ + (-(epsBd u v R) / (2 * (sigBd u v))) • e₂) +ᵥ O)
      = (⟨_, hAIBB1B2⟩ : Triangle ℝ P).circumcenter := by
    apply Affine.Simplex.eq_circumcenter_of_dist_eq _ (by rw [hspanB]; exact AffineSubspace.mem_top ℝ V _) (r := dist B (((-(delBd u v R) / (2 * (sigBd u v))) • e₁ + (-(epsBd u v R) / (2 * (sigBd u v))) • e₂) +ᵥ O))
    intro i
    fin_cases i
    ·       rfl
    · show dist B₁ (((-(delBd u v R) / (2 * (sigBd u v))) • e₁ + (-(epsBd u v R) / (2 * (sigBd u v))) • e₂) +ᵥ O) = dist B (((-(delBd u v R) / (2 * (sigBd u v))) • e₁ + (-(epsBd u v R) / (2 * (sigBd u v))) • e₂) +ᵥ O)
      rw [hB₁']
      exact hmemB _ _ incBB1f
    · show dist B₂ (((-(delBd u v R) / (2 * (sigBd u v))) • e₁ + (-(epsBd u v R) / (2 * (sigBd u v))) • e₂) +ᵥ O) = dist B (((-(delBd u v R) / (2 * (sigBd u v))) • e₁ + (-(epsBd u v R) / (2 * (sigBd u v))) • e₂) +ᵥ O)
      rw [hB₂']
      exact hmemB _ _ incBB2f
  have hcenC : (((-(delCd u v R) / (2 * (sigCd u v))) • e₁ + (-(epsCd u v R) / (2 * (sigCd u v))) • e₂) +ᵥ O)
      = (⟨_, hAICC1C2⟩ : Triangle ℝ P).circumcenter := by
    apply Affine.Simplex.eq_circumcenter_of_dist_eq _ (by rw [hspanC]; exact AffineSubspace.mem_top ℝ V _) (r := dist C (((-(delCd u v R) / (2 * (sigCd u v))) • e₁ + (-(epsCd u v R) / (2 * (sigCd u v))) • e₂) +ᵥ O))
    intro i
    fin_cases i
    ·       rfl
    · show dist C₁ (((-(delCd u v R) / (2 * (sigCd u v))) • e₁ + (-(epsCd u v R) / (2 * (sigCd u v))) • e₂) +ᵥ O) = dist C (((-(delCd u v R) / (2 * (sigCd u v))) • e₁ + (-(epsCd u v R) / (2 * (sigCd u v))) • e₂) +ᵥ O)
      rw [hC₁']
      exact hmemC _ _ incCC1f
    · show dist C₂ (((-(delCd u v R) / (2 * (sigCd u v))) • e₁ + (-(epsCd u v R) / (2 * (sigCd u v))) • e₂) +ᵥ O) = dist C (((-(delCd u v R) / (2 * (sigCd u v))) • e₁ + (-(epsCd u v R) / (2 * (sigCd u v))) • e₂) +ᵥ O)
      rw [hC₂']
      exact hmemC _ _ incCC2f
  have hradA : dist A (((-(delAd u v R) / (2 * (sigAd u v))) • e₁ + (-(epsAd u v R) / (2 * (sigAd u v))) • e₂) +ᵥ O)
      = (⟨_, hAIAA1A2⟩ : Triangle ℝ P).circumradius := by
    apply Affine.Simplex.eq_circumradius_of_dist_eq (p := (((-(delAd u v R) / (2 * (sigAd u v))) • e₁ + (-(epsAd u v R) / (2 * (sigAd u v))) • e₂) +ᵥ O)) _ (by rw [hspanA]; exact AffineSubspace.mem_top ℝ V _) (r := dist A (((-(delAd u v R) / (2 * (sigAd u v))) • e₁ + (-(epsAd u v R) / (2 * (sigAd u v))) • e₂) +ᵥ O))
    intro i
    fin_cases i
    ·       rfl
    · show dist A₁ (((-(delAd u v R) / (2 * (sigAd u v))) • e₁ + (-(epsAd u v R) / (2 * (sigAd u v))) • e₂) +ᵥ O) = dist A (((-(delAd u v R) / (2 * (sigAd u v))) • e₁ + (-(epsAd u v R) / (2 * (sigAd u v))) • e₂) +ᵥ O)
      rw [hA₁']
      exact hmemA _ _ incAA1f
    · show dist A₂ (((-(delAd u v R) / (2 * (sigAd u v))) • e₁ + (-(epsAd u v R) / (2 * (sigAd u v))) • e₂) +ᵥ O) = dist A (((-(delAd u v R) / (2 * (sigAd u v))) • e₁ + (-(epsAd u v R) / (2 * (sigAd u v))) • e₂) +ᵥ O)
      rw [hA₂']
      exact hmemA _ _ incAA2f
  have hradB : dist B (((-(delBd u v R) / (2 * (sigBd u v))) • e₁ + (-(epsBd u v R) / (2 * (sigBd u v))) • e₂) +ᵥ O)
      = (⟨_, hAIBB1B2⟩ : Triangle ℝ P).circumradius := by
    apply Affine.Simplex.eq_circumradius_of_dist_eq (p := (((-(delBd u v R) / (2 * (sigBd u v))) • e₁ + (-(epsBd u v R) / (2 * (sigBd u v))) • e₂) +ᵥ O)) _ (by rw [hspanB]; exact AffineSubspace.mem_top ℝ V _) (r := dist B (((-(delBd u v R) / (2 * (sigBd u v))) • e₁ + (-(epsBd u v R) / (2 * (sigBd u v))) • e₂) +ᵥ O))
    intro i
    fin_cases i
    ·       rfl
    · show dist B₁ (((-(delBd u v R) / (2 * (sigBd u v))) • e₁ + (-(epsBd u v R) / (2 * (sigBd u v))) • e₂) +ᵥ O) = dist B (((-(delBd u v R) / (2 * (sigBd u v))) • e₁ + (-(epsBd u v R) / (2 * (sigBd u v))) • e₂) +ᵥ O)
      rw [hB₁']
      exact hmemB _ _ incBB1f
    · show dist B₂ (((-(delBd u v R) / (2 * (sigBd u v))) • e₁ + (-(epsBd u v R) / (2 * (sigBd u v))) • e₂) +ᵥ O) = dist B (((-(delBd u v R) / (2 * (sigBd u v))) • e₁ + (-(epsBd u v R) / (2 * (sigBd u v))) • e₂) +ᵥ O)
      rw [hB₂']
      exact hmemB _ _ incBB2f
  have hradC : dist C (((-(delCd u v R) / (2 * (sigCd u v))) • e₁ + (-(epsCd u v R) / (2 * (sigCd u v))) • e₂) +ᵥ O)
      = (⟨_, hAICC1C2⟩ : Triangle ℝ P).circumradius := by
    apply Affine.Simplex.eq_circumradius_of_dist_eq (p := (((-(delCd u v R) / (2 * (sigCd u v))) • e₁ + (-(epsCd u v R) / (2 * (sigCd u v))) • e₂) +ᵥ O)) _ (by rw [hspanC]; exact AffineSubspace.mem_top ℝ V _) (r := dist C (((-(delCd u v R) / (2 * (sigCd u v))) • e₁ + (-(epsCd u v R) / (2 * (sigCd u v))) • e₂) +ᵥ O))
    intro i
    fin_cases i
    ·       rfl
    · show dist C₁ (((-(delCd u v R) / (2 * (sigCd u v))) • e₁ + (-(epsCd u v R) / (2 * (sigCd u v))) • e₂) +ᵥ O) = dist C (((-(delCd u v R) / (2 * (sigCd u v))) • e₁ + (-(epsCd u v R) / (2 * (sigCd u v))) • e₂) +ᵥ O)
      rw [hC₁']
      exact hmemC _ _ incCC1f
    · show dist C₂ (((-(delCd u v R) / (2 * (sigCd u v))) • e₁ + (-(epsCd u v R) / (2 * (sigCd u v))) • e₂) +ᵥ O) = dist C (((-(delCd u v R) / (2 * (sigCd u v))) • e₁ + (-(epsCd u v R) / (2 * (sigCd u v))) • e₂) +ᵥ O)
      rw [hC₂']
      exact hmemC _ _ incCC2f
  -- the two points lie in all three circumspheres
  have hP1_memA : P1pt ∈ (⟨_, hAIAA1A2⟩ : Triangle ℝ P).circumsphere := by
    rw [EuclideanGeometry.mem_sphere, Affine.Simplex.circumsphere_center, ← hcenA,
      Affine.Simplex.circumsphere_radius, ← hradA]
    exact hmemA _ _ hP1omegaA
  have hP1_memB : P1pt ∈ (⟨_, hAIBB1B2⟩ : Triangle ℝ P).circumsphere := by
    rw [EuclideanGeometry.mem_sphere, Affine.Simplex.circumsphere_center, ← hcenB,
      Affine.Simplex.circumsphere_radius, ← hradB]
    exact hmemB _ _ hP1omegaB
  have hP1_memC : P1pt ∈ (⟨_, hAICC1C2⟩ : Triangle ℝ P).circumsphere := by
    rw [EuclideanGeometry.mem_sphere, Affine.Simplex.circumsphere_center, ← hcenC,
      Affine.Simplex.circumsphere_radius, ← hradC]
    exact hmemC _ _ hP1omegaC
  have hP2_memA : P2pt ∈ (⟨_, hAIAA1A2⟩ : Triangle ℝ P).circumsphere := by
    rw [EuclideanGeometry.mem_sphere, Affine.Simplex.circumsphere_center, ← hcenA,
      Affine.Simplex.circumsphere_radius, ← hradA]
    exact hmemA _ _ hP2omegaA
  have hP2_memB : P2pt ∈ (⟨_, hAIBB1B2⟩ : Triangle ℝ P).circumsphere := by
    rw [EuclideanGeometry.mem_sphere, Affine.Simplex.circumsphere_center, ← hcenB,
      Affine.Simplex.circumsphere_radius, ← hradB]
    exact hmemB _ _ hP2omegaB
  have hP2_memC : P2pt ∈ (⟨_, hAICC1C2⟩ : Triangle ℝ P).circumsphere := by
    rw [EuclideanGeometry.mem_sphere, Affine.Simplex.circumsphere_center, ← hcenC,
      Affine.Simplex.circumsphere_radius, ← hradC]
    exact hmemC _ _ hP2omegaC
  -- final cardinality argument
  refine ⟨hAIAA1A2, hAIBB1B2, hAICC1C2, ?_⟩
  have hP1mem : P1pt ∈ ((⟨_, hAIAA1A2⟩ : Triangle ℝ P).circumsphere ∩
      (⟨_, hAIBB1B2⟩ : Triangle ℝ P).circumsphere ∩
      (⟨_, hAICC1C2⟩ : Triangle ℝ P).circumsphere : Set P) :=
    ⟨⟨hP1_memA, hP1_memB⟩, hP1_memC⟩
  have hP2mem : P2pt ∈ ((⟨_, hAIAA1A2⟩ : Triangle ℝ P).circumsphere ∩
      (⟨_, hAIBB1B2⟩ : Triangle ℝ P).circumsphere ∩
      (⟨_, hAICC1C2⟩ : Triangle ℝ P).circumsphere : Set P) :=
    ⟨⟨hP2_memA, hP2_memB⟩, hP2_memC⟩
  rw [Cardinal.two_le_iff]
  exact ⟨⟨P1pt, hP1mem⟩, ⟨P2pt, hP2mem⟩, by
    intro h
    rw [Subtype.mk.injEq] at h
    exact hP1neP2 h⟩
end Imo2023P6
