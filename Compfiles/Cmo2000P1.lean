/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: sjfhsjfh
-/
import Mathlib.Geometry.Euclidean.Angle.Sphere
import Mathlib.Geometry.Euclidean.Sphere.SecondInter

import ProblemExtraction
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Geometry.Euclidean.Sphere.Power

problem_file { tags := [.Geometry] }

/-!
# China Mathematical Olympiad 2000, Problem 1

In acute-angled triangle `ABC`, `E`, `F` are on the side `BC`, such that
`∠BAE = ∠CAF`, and let `M`, `N` be the projections of `F` onto
`AB`, `AC`, respectively. The line `AE` intersects `⊙(ABC)` at `D`
(different from point `A`).
Prove that `S_{AMDN} = S_{△ABC}`.
-/

open Affine Affine.Simplex EuclideanGeometry FiniteDimensional Module Mathlib.Meta.Positivity

open scoped Affine EuclideanGeometry Real

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable {V : Type*} {Pt : Type*}

variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]

variable [NormedAddTorsor V Pt]

namespace Cmo2000P1

/-- Area of triangle `XYZ` via the formula `½·|v||w|·sin θ`,
where `v = Y-X`, `w = Z-X`. -/
noncomputable def area3 (X Y Z : Pt) : ℝ :=
  1 / 2 * Real.sqrt (‖Y -ᵥ X‖^2 * ‖Z -ᵥ X‖^2 - (@Inner.inner ℝ V _ (Y -ᵥ X) (Z -ᵥ X)) ^ 2)

/-- Area of quadrilateral with vertices `A`, `M`, `D`, `N` (with diagonal `AD`). -/
noncomputable def area4 (A M D N : Pt) : ℝ :=
  area3 A M D + area3 A D N

snip begin

lemma three_set_inv_eq {α : Type*}
  (A B C : α)
  : ({A, B, C} : Set α) = {C, B, A} := by
  ext; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

lemma affine_indep₃_inv {A B C : Pt}
  (h : AffineIndependent ℝ ![A, B, C])
  : AffineIndependent ℝ ![C, B, A] := by
  refine affineIndependent_iff_not_collinear.mpr ?_
  rewrite [← show Set.range ![A, B, C] = Set.range ![C, B, A] by
  ext x; simp; tauto]
  exact affineIndependent_iff_not_collinear.mp h

lemma affine_indep₃_rot {A B C : Pt}
  (h : AffineIndependent ℝ ![A, B, C])
  : AffineIndependent ℝ ![B, C, A] := by
  refine affineIndependent_iff_not_collinear.mpr ?_
  rewrite [← show Set.range ![A, B, C] = Set.range ![B, C, A] by
  ext x; simp; tauto]
  exact affineIndependent_iff_not_collinear.mp h

lemma collinear_iff_on_line (A B C : Pt) (h_ne : A ≠ B)
  : Collinear ℝ ({A, B, C} : Set Pt) ↔ C ∈ line[ℝ, A ,B] := by
  refine ⟨?line, ?coll⟩
  case line =>
    intro h; exact Collinear.mem_affineSpan_of_mem_of_ne h (Set.mem_insert A {B, C})
      (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true])
      (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true]) h_ne
  case coll =>
    intro h; refine collinear_iff_of_mem (Set.mem_insert A {B, C}) |>.mpr ?_
    obtain ⟨P, ⟨hPAB, ⟨v, ⟨hv, hvC⟩⟩⟩⟩ := mem_affineSpan_iff_exists ℝ |>.mp h
    subst hvC
    rcases hPAB with (rfl | rfl)
    · obtain ⟨r, hr⟩ := vadd_left_mem_affineSpan_pair.mp h
      by_cases! h_rne₀ : r = 0
      · have : v = 0 := by rewrite [← hr, h_rne₀, zero_smul]; rfl
        subst this; use B -ᵥ P; simp
        refine ⟨?_, ?_⟩
        · use 1; rewrite [one_smul, vsub_vadd]; rfl
        · use 0; rewrite [zero_smul, zero_vadd]; rfl
      use v; intro p hp;
      rcases hp with (rfl | rfl | rfl)
      · use 0; rewrite [zero_smul, zero_vadd]; rfl
      · use 1 / r; rw [← hr, smul_smul, one_div_mul_cancel h_rne₀, one_smul, vsub_vadd]
      · use 1; rewrite [one_smul]; rfl
    · obtain ⟨r, hr⟩ := vadd_right_mem_affineSpan_pair.mp h
      by_cases! h_rne₀ : r = 0
      · have : v = 0 := by rewrite [← hr, h_rne₀, zero_smul]; rfl
        subst this; use P -ᵥ A; simp
        refine ⟨?_, ?_⟩
        · use 0; rewrite [zero_smul, zero_vadd]; rfl
        · use 1; rewrite [one_smul, vsub_vadd]; rfl
      use v; intro p hp
      rcases hp with (rfl | rfl | rfl)
      · use 0; rewrite [zero_smul, zero_vadd]; rfl
      · use -1 / r; rewrite [← hr, smul_smul, div_mul_cancel₀ _ h_rne₀, neg_one_smul,
          neg_vsub_eq_vsub_rev, vsub_vadd]; rfl
      · use (1 - 1 / r); rewrite [← hr, smul_smul, sub_mul, one_div_mul_cancel h_rne₀,
          one_mul, sub_smul, vadd_eq_vadd_iff_sub_eq_vsub, one_smul, sub_sub, add_comm,
          ← sub_sub, sub_self, zero_sub, neg_vsub_eq_vsub_rev]; rfl

lemma line_comm (A B : Pt)
  : line[ℝ, A, B] = line[ℝ, B, A] := by
  congr 1; ext; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

lemma line_swap_iff (A B C : Pt) (h_neAC : A ≠ C) (h_neBC : B ≠ C)
  : A ∈ line[ℝ, B, C] ↔ B ∈ line[ℝ, A, C] := by
  suffices helper : ∀ (A B C : Pt), ∀ (h_neAC : A ≠ C), ∀ (h_neBC : B ≠ C),
    ∀ (h : A ∈ line[ℝ, B, C]), B ∈ line[ℝ, A, C] by
    refine ⟨helper A B C h_neAC h_neBC, helper B A C h_neBC h_neAC⟩
  intro A B C h_neAC h_neBC h
  refine collinear_iff_on_line A C B h_neAC |>.mp ?_
  rewrite [three_set_inv_eq]
  exact collinear_iff_on_line B C A h_neBC |>.mpr h

lemma on_line_swap_left (A B C : Pt) (h_ne : A ≠ C)
  (h : A ∈ line[ℝ, B, C]) : B ∈ line[ℝ, A, C] := by
  by_cases! h_ne' : B = C
  · subst h_ne'; simp only [Set.mem_singleton_iff, Set.insert_eq_of_mem,
      AffineSubspace.mem_affineSpan_singleton] at h
    absurd h_ne; exact h
  exact line_swap_iff A B C h_ne h_ne'|>.mp h

lemma on_line_swap_right (A B C : Pt) (h_ne : A ≠ B)
  (h : A ∈ line[ℝ, B, C]) : C ∈ line[ℝ, B, A] := by
  rewrite [line_comm] at ⊢ h; exact on_line_swap_left A C B h_ne h

lemma on_both_sides {A B C D : Pt}
  (h_tri : AffineIndependent ℝ ![A, B, C])
  (h_BC : Wbtw ℝ B D C) (h_AC : Wbtw ℝ A D C)
  : C = D := by
  by_contra! h_CeqD
  obtain ⟨rB, ⟨_, hB⟩⟩ := Set.mem_image _ _ _ |>.mp <|
    Wbtw.right_mem_image_Ici_of_left_ne (wbtw_comm.mp h_BC) h_CeqD
  obtain ⟨rA, ⟨_, hA⟩⟩ := Set.mem_image _ _ _ |>.mp <|
    Wbtw.right_mem_image_Ici_of_left_ne (wbtw_comm.mp h_AC) h_CeqD
  absurd h_tri; refine collinear_iff_not_affineIndependent_set.mp <|
    collinear_iff_of_mem (p₀ := C) (by simp) |>.mpr ?_
  use D -ᵥ C; simp [← hA, ← hB, AffineMap.lineMap]
  refine ⟨?caseA, ?caseB, ?caseC⟩
  case caseA => use rA
  case caseB => use rB
  case caseC => use 0; rewrite [zero_smul, zero_vadd]; rfl

lemma on_both_sides' {A B C D : Pt}
  (h_tri : AffineIndependent ℝ ![A, B, C])
  (h_BC : Wbtw ℝ B D C) (h_AC : Wbtw ℝ A C D)
  : C = D := by
  by_contra! h_CeqD
  obtain ⟨rB, ⟨_, hB⟩⟩ := Set.mem_image _ _ _ |>.mp <|
    Wbtw.right_mem_image_Ici_of_left_ne (wbtw_comm.mp h_BC) h_CeqD
  obtain ⟨rA, ⟨_, hA⟩⟩ := Set.mem_image _ _ _ |>.mp <|
    Wbtw.right_mem_image_Ici_of_left_ne (wbtw_comm.mp h_AC) h_CeqD.symm
  absurd h_tri; refine collinear_iff_not_affineIndependent_set.mp <|
    collinear_iff_of_mem (p₀ := C) (by simp) |>.mpr ?_
  use D -ᵥ C; simp [← hA, ← hB, AffineMap.lineMap]
  refine ⟨?caseA, ?caseB, ?caseC⟩
  case caseA => use 1 - rA; calc rA • (C -ᵥ D) +ᵥ D
    _ = ((D -ᵥ C) + rA • (C -ᵥ D)) +ᵥ C := by rw [add_comm, add_vadd, vsub_vadd]
    _ = (1 - rA) • (D -ᵥ C) +ᵥ C := by
      rw [sub_smul, one_smul, sub_eq_add_neg, ← smul_neg, neg_vsub_eq_vsub_rev]
  case caseB => use rB
  case caseC => use 0; rewrite [zero_smul, zero_vadd]; rfl

lemma angle_sin_nonneg {V : Type*} {Pt : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace Pt] [NormedAddTorsor V Pt]
  (A B C : Pt) : (∠ A B C).sin ≥ 0 :=
  Real.sin_nonneg_of_nonneg_of_le_pi (angle_nonneg A B C) (angle_le_pi A B C)

lemma angle_cos_nonneg_of_le_pi_div_two {V : Type*} {Pt : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace Pt] [NormedAddTorsor V Pt]
  (A B C : Pt) (h : ∠ A B C ≤ π / 2) : (∠ A B C).cos ≥ 0 :=
  (Real.cos_nonneg_of_neg_pi_div_two_le_of_le (le_trans (neg_nonpos.mpr
    Real.pi_div_two_pos.le) (angle_nonneg A B C)) h)

lemma area_sin (A B C : Pt)
  : area3 A B C = 1 / 2 * dist A B * dist A C * (∠ B A C).sin := by
  suffices h : Real.sqrt (‖B -ᵥ A‖ ^ 2 * ‖C -ᵥ A‖ ^ 2
    - (@Inner.inner ℝ V _ (B -ᵥ A) (C -ᵥ A)) ^ 2)
    = ‖A -ᵥ B‖ * ‖A -ᵥ C‖ * (∠ B A C).sin by
    unfold area3; rewrite [h, ← mul_assoc, ← mul_assoc,
      dist_eq_norm_vsub, dist_eq_norm_vsub]; rfl
  have h_cos_sq : ∀ θ : ℝ, 1 - θ.cos ^ 2 = θ.sin ^ 2 := fun θ => by
    rewrite [← Real.cos_sq_add_sin_sq θ, add_sub_cancel_left]; rfl
  rewrite [
    ← InnerProductGeometry.cos_angle_mul_norm_mul_norm _ _, mul_pow, mul_pow,
    ← one_sub_mul, h_cos_sq,
  ]
  refine Real.sqrt_eq_iff_eq_sq ?nonneg1 ?nonneg2 |>.mpr ?sq_eq
  case nonneg1 => exact mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  case nonneg2 =>
    refine mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ?sin_nonneg
    exact angle_sin_nonneg B A C
  rewrite [mul_comm, mul_pow, mul_pow, ← norm_neg (B -ᵥ A), neg_vsub_eq_vsub_rev,
    ← norm_neg (C -ᵥ A), neg_vsub_eq_vsub_rev]; rfl

lemma dist_chord_sq {A B : Pt} {S : Sphere Pt}
  (h_A : A ∈ S) (h_B : B ∈ S)
  : 2 * (S.radius ^ 2 - inner ℝ (A -ᵥ S.center) (B -ᵥ S.center)) = dist A B ^ 2 := by
  rewrite [
    mul_sub 2 _ _, dist_eq_norm_vsub V A B, ← real_inner_self_eq_norm_sq,
    ← vsub_sub_vsub_cancel_right A B S.center,
    inner_sub_left, inner_sub_right, inner_sub_right,
    real_inner_self_eq_norm_sq (A -ᵥ S.center),
    ← dist_eq_norm_vsub V A S.center, mem_sphere.mp h_A,
    real_inner_self_eq_norm_sq (B -ᵥ S.center),
    ← dist_eq_norm_vsub V B S.center, mem_sphere.mp h_B,
    sub_sub_eq_add_sub, add_sub_assoc, sub_add_sub_comm, ← two_mul (S.radius ^ 2),
    sub_right_inj.eq, two_mul, add_right_inj
  ]; exact real_inner_comm _ _

lemma power_nonpos_iff_wbtw {A B C : Pt} (S : Sphere Pt)
  (h_A : A ∈ S) (h_B : B ∈ S) (h_AB : A ≠ B)
  (h_C : C ∈ line[ℝ, A ,B])
  : S.power C ≤ 0 ↔ Wbtw ℝ A C B := by
  have h_r_nonneg : S.radius ≥ 0 := S.radius_nonneg_of_mem h_A
  have hdA : dist A S.center = S.radius := mem_sphere.mp h_A
  have hdB : dist B S.center = S.radius := mem_sphere.mp h_B
  have h_dist_AB :
    2 * (S.radius ^ 2 - inner ℝ (A -ᵥ S.center) (B -ᵥ S.center)) = dist A B ^ 2
    := dist_chord_sq h_A h_B
  refine ⟨?wbtw, ?power_nonpos⟩
  case wbtw =>
    intro h; conv at h => rewrite [Sphere.power_nonpos_iff_dist_center_le_radius
      h_r_nonneg, ← sq_le_sq₀ (dist_nonneg (x := C) (y := S.center)) h_r_nonneg]
    obtain ⟨v, h_coll⟩ := collinear_iff_of_mem
      (Set.mem_insert A ({B, C} : Set Pt)) |>.mp <|
      collinear_iff_on_line A B C h_AB |>.mpr h_C
    obtain ⟨r_C, h_C_eq⟩ := h_coll C (by tauto)
    obtain ⟨r_B, h_B_eq⟩ := h_coll B (by tauto)
    by_cases! h_r_B : r_B = 0
    · rewrite [h_r_B, zero_smul, zero_vadd] at h_B_eq
      absurd h_AB.symm; exact h_B_eq
    use r_C / r_B
    have h_eq : (r_C / r_B) • (B -ᵥ A) +ᵥ A = C := by
      simp [h_B_eq, h_C_eq, smul_smul]; congr 1
      exact div_mul_cancel₀ r_C h_r_B
    rewrite [← h_eq, dist_eq_norm_vsub, ← vsub_sub_vsub_cancel_right B A S.center,
        smul_sub, vadd_vsub_assoc, sub_add_comm] at h
    nth_rewrite 1 [show A -ᵥ S.center = (1 : ℝ) • (A -ᵥ S.center) by
      exact Eq.symm (MulAction.one_smul (A -ᵥ S.center))] at h
    conv at h =>
      rewrite [← sub_smul, ← real_inner_self_eq_norm_sq, real_inner_add_add_self]
      simp only [inner_smul_right, inner_smul_left, conj_trivial,
        real_inner_self_eq_norm_sq, ← sq, ← mul_assoc]
      rewrite [← dist_eq_norm_vsub, hdA, ← dist_eq_norm_vsub, hdB, add_comm,
        ← add_assoc, ← add_mul, show (r_C / r_B) ^ 2 + (1 - r_C / r_B) ^ 2
          = 1 - 2 * (r_C / r_B) * (1 - r_C / r_B) by ring,
        sub_mul, one_mul, sub_add, ← mul_sub, mul_comm 2, mul_assoc,
        mul_mul_mul_comm, h_dist_AB, sub_le_self_iff, mul_nonneg_iff_of_pos_right
        <| pow_two_pos_of_ne_zero <| dist_ne_zero.mpr h_AB]
    by_cases! h_zero : r_C / r_B = 0
    · rewrite [h_zero]; field_simp at h_zero; rewrite [mul_zero] at h_zero
      rewrite [h_zero, zero_smul, zero_vadd] at h_C_eq
      exact ⟨unitInterval.zero_mem, by simp [AffineMap.lineMap, h_C_eq]⟩
    suffices h_ratio_pos : r_C / r_B > 0 by
      refine ⟨⟨h_ratio_pos.le, ?one⟩, ?eq⟩
      case eq => simpa [AffineMap.lineMap] using h_eq
      case one => exact sub_nonneg.mp <| mul_nonneg_iff_of_pos_left h_ratio_pos |>.mp h
    by_contra! h_nonpos
    absurd le_trans (tsub_nonpos.mp <| nonpos_of_mul_nonneg_right h <|
      lt_of_le_of_ne h_nonpos h_zero) h_nonpos; norm_num
  case power_nonpos =>
    intro ⟨r, ⟨⟨hr_0, hr_1⟩, heq⟩⟩
    refine Sphere.power_nonpos_iff_dist_center_le_radius h_r_nonneg |>.mpr
      <| sq_le_sq₀ (dist_nonneg (x := C) (y := S.center)) h_r_nonneg |>.mp ?_
    simp [AffineMap.lineMap] at heq; rewrite [← heq, dist_eq_norm_vsub]
    calc ‖(r • (B -ᵥ A) +ᵥ A) -ᵥ S.center‖ ^ 2
      _ = (inner ℝ ((1 - r) • (A -ᵥ S.center) + r • (B -ᵥ S.center))
          ((1 - r) • (A -ᵥ S.center) + r • (B -ᵥ S.center))) := by
        rewrite [real_inner_self_eq_norm_sq]; congr 2; rewrite [
          sub_smul, one_smul, add_comm, add_sub_left_comm, ← smul_sub,
          vsub_sub_vsub_cancel_right, add_comm, vadd_vsub_assoc,
        ]; rfl
      _ = S.radius ^ 2 - 2 * r * (1 - r) *
        (S.radius ^ 2 - inner ℝ (A -ᵥ S.center) (B -ᵥ S.center)) := by
        rewrite [real_inner_add_add_self]; simp only [real_inner_self_eq_norm_sq,
          inner_smul_right, inner_smul_left, conj_trivial, ← dist_eq_norm_vsub,
          hdA, hdB]; ring
      _ = S.radius ^ 2 - r * (1 - r) * dist A B ^ 2 := by
        congr 1; rewrite [mul_comm 2, mul_assoc, mul_mul_mul_comm, h_dist_AB]; rfl
      _ ≤ S.radius ^ 2 := sub_le_self (S.radius ^ 2) <| mul_nonneg (mul_nonneg hr_0
        (sub_nonneg_of_le hr_1)) (sq_nonneg (dist A B))

lemma wbtw_on_sphere_eq {A B C : Pt} {S : Sphere Pt}
  (h_wbtw : Wbtw ℝ A B C)
  (hA : A ∈ S) (hB : B ∈ S) (hC : C ∈ S)
  : B = A ∨ B = C := by
  obtain ⟨r, ⟨⟨hr₀, hr₁⟩, heq⟩⟩ := h_wbtw
  simp [AffineMap.lineMap] at heq
  have h_lmap : (r • (C -ᵥ A) +ᵥ A) -ᵥ S.center
    = r • (C -ᵥ S.center) + (1 - r) • (A -ᵥ S.center) := by
    rw [sub_smul, add_sub, add_sub_right_comm, ← smul_sub, vsub_sub_vsub_cancel_right,
      one_smul, vadd_vsub_eq_sub_vsub, sub_eq_add_neg, neg_vsub_eq_vsub_rev]
  have h_r_simp : 1 - (r ^ 2 + (1 - r) ^ 2) = 2 * r * (1 - r) := by ring
  have : dist B S.center ^ 2 = S.radius ^ 2 := by rw [mem_sphere.mp hB]
  conv at this =>
    rewrite [← heq, dist_eq_norm_vsub, h_lmap, ← real_inner_self_eq_norm_sq,
      real_inner_add_add_self, real_inner_self_eq_norm_sq]
    simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, ← dist_eq_norm_vsub,
      norm_smul, mul_pow, sq_abs]
    rewrite [mem_sphere.mp hA, mem_sphere.mp hC, add_comm (r ^ 2 * _), add_assoc,
      ← add_mul, inner_smul_left, inner_smul_right]
    simp only [conj_trivial, ← mul_assoc]
  have := sub_eq_zero_of_eq this
  conv at this =>
    rewrite [add_sub_right_comm, sub_add, ← one_sub_mul, h_r_simp, ← mul_sub,
      ← neg_sub (_ ^ 2), mul_neg, mul_comm 2 _, mul_mul_mul_comm', mul_assoc _ 2,
      dist_chord_sq hC hA, neg_eq_zero, mul_eq_zero, mul_eq_zero, sq_eq_zero_iff,
      dist_eq_zero, or_assoc]
  rcases this with (h | h | h)
  · simp [h] at heq
    exact Or.inl heq.symm
  · simp [eq_of_sub_eq_zero h |>.symm] at heq
    exact Or.inr heq.symm
  · simp [vsub_eq_zero_iff_eq.mpr h] at heq
    exact Or.inl heq.symm

lemma wbtw_tri_ne (A B C D : Pt)
  (h_tri : AffineIndependent ℝ ![A, B, C]) (hD : Wbtw ℝ B D C)
  : A ≠ D := by
  by_contra! heq
  rewrite [← heq] at hD; obtain ⟨r, ⟨_, h⟩⟩ := hD
  conv at h => simp [AffineMap.lineMap]; rewrite [← vsub_eq_zero_iff_eq]
  have h_absurd := h_tri {0, 1, 2} ![-1, 1 - r, r]
    (by simp) (by
    simp [Finset.weightedVSub]
    calc _ -ᵥ A + ((1 - r) • (B -ᵥ _) + r • (C -ᵥ _))
      _ = (B -ᵥ A) - r • (B -ᵥ C) := by
        rewrite [
          sub_smul, sub_add, ← smul_sub, vsub_sub_vsub_cancel_right, one_smul,
          add_sub, add_comm (_ -ᵥ A), vsub_add_vsub_cancel,
        ]; rfl
      _ = (r • (C -ᵥ B) +ᵥ B) -ᵥ A := by
        rewrite [
          vadd_vsub_assoc, add_comm, sub_eq_add_neg, add_right_inj,
          ← smul_neg, neg_vsub_eq_vsub_rev,
        ]; rfl
      _ = 0 := h)
    0 (Finset.mem_insert_self 0 {1, 2})
  simp at h_absurd

lemma angle_split {A B C D : Pt}
  (h_tri : AffineIndependent ℝ ![A, B, C]) (hD : Wbtw ℝ B D C)
  : ∠ B A D + ∠ D A C = ∠ B A C := by
  refine InnerProductGeometry.angle_eq_angle_add_angle_iff
    (vsub_eq_zero_iff_eq.not.mpr <| wbtw_tri_ne A B C D h_tri hD |>.symm)
    |>.mpr (Or.inr ?_) |>.symm
  obtain ⟨r, ⟨⟨h_r_nonneg, h_r_1⟩, h⟩⟩ := hD
  simp [AffineMap.lineMap] at h
  refine Submodule.mem_span_pair.mpr ?_
  let a : NNReal := ⟨1 - r, sub_nonneg_of_le h_r_1⟩
  let b : NNReal := ⟨r, h_r_nonneg⟩
  use a, b
  change (1 - r) • (B -ᵥ A) + r • (C -ᵥ A) = D -ᵥ A
  rewrite [
    ← h, vadd_vsub_assoc, ← vsub_sub_vsub_cancel_right C B A, smul_sub, sub_add_comm,
    add_left_inj (r • (C -ᵥ A)), sub_smul, one_smul,
  ]; rfl

lemma orthogonalProj_angle_pi_div_two (A B C D : Pt)
  (h_proj : B = orthogonalProjection (line[ℝ, C, D]) A)
  : ∠ A B C = π / 2 ∧ ∠ A B D = π / 2 := by
  have hB_mem_CD : B ∈ line[ℝ, C, D] := by rw [h_proj]; exact orthogonalProjection_mem A
  have hC_mem : C ∈ line[ℝ, C, D] := left_mem_affineSpan_pair ℝ C D
  have hD_mem : D ∈ line[ℝ, C, D] := right_mem_affineSpan_pair ℝ C D
  refine ⟨?_, ?_⟩
  <;> refine InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two _ _ |>.mp ?_
  <;> rewrite [real_inner_comm, ← neg_eq_zero, ← inner_neg_right, neg_vsub_eq_vsub_rev]
  · have := orthogonalProjection_vsub_mem_direction_orthogonal (affineSpan ℝ {C, D}) A
      _ (AffineSubspace.vsub_mem_direction hC_mem hB_mem_CD)
    rewrite [← h_proj] at this; exact this
  · have := orthogonalProjection_vsub_mem_direction_orthogonal (affineSpan ℝ {C, D}) A
      _ (AffineSubspace.vsub_mem_direction hD_mem hB_mem_CD)
    rewrite [← h_proj] at this; exact this

lemma triagle_no_rep {A B C : Pt}
  (h_tri : AffineIndependent ℝ ![A, B, C])
  : A ≠ B ∧ B ≠ C ∧ A ≠ C := by
  refine ⟨?_, ?_, ?_⟩
  <;> by_contra! h
  · have := h_tri {0, 1, 2} ![1, -1, 0] (by simp)
      (by simp [Finset.weightedVSub, h]) 0 (Finset.insert_eq_self.mp rfl)
    simp only [Fin.isValue, Matrix.cons_val, one_ne_zero] at this
  · have := h_tri {0, 1, 2} ![0, 1, -1] (by simp)
      (by simp [Finset.weightedVSub, h]) 1 (Finset.insert_eq_self.mp rfl)
    simp only [Fin.isValue, Matrix.cons_val, one_ne_zero] at this
  · have := h_tri {0, 1, 2} ![-1, 0, 1] (by simp)
      (by simp [Finset.weightedVSub, h]) 2 (Finset.insert_eq_self.mp rfl)
    simp only [Fin.isValue, Matrix.cons_val, one_ne_zero] at this

lemma orthogonalProj_wbtw_acute (A B C : Pt)
  (h_tri : AffineIndependent ℝ ![A, B, C])
  (h_acuteB : ∠ A B C < π / 2) (h_acuteC : ∠ A C B < π / 2)
  : let (eq := _) H : Pt := orthogonalProjection (line[ℝ, B, C]) A
    Wbtw ℝ B H C := by
  intro H hH; use (∠ A C B).sin * (∠ A B C).cos / (∠ B A C).sin
  have h_BAC_sin_ne₀ : (∠ B A C).sin ≠ 0 := by
    by_contra! h
    absurd collinear_iff_eq_or_eq_or_sin_eq_zero.mpr (Or.inr (Or.inr h))
    simpa using affineIndependent_iff_not_collinear.mp <| affine_indep₃_rot <|
      affine_indep₃_rot h_tri
  have h_BAC_sin_pos : (∠ B A C).sin > 0 :=
    lt_of_le_of_ne (angle_sin_nonneg B A C) h_BAC_sin_ne₀.symm
  refine ⟨⟨?ge0, ?le1⟩, ?_⟩
  case ge0 =>
    exact div_nonneg (mul_nonneg (angle_sin_nonneg A C B) <|
      angle_cos_nonneg_of_le_pi_div_two A B C h_acuteB.le) <| angle_sin_nonneg B A C
  case le1 =>
    refine (div_le_one₀ h_BAC_sin_pos).mpr ?_
    have h_BAC_sin_add : (∠ B A C).sin = (∠ A C B + ∠ A B C).sin := by
      rewrite [← Real.sin_pi_sub (∠ B A C)]; congr 1;
      refine sub_eq_of_eq_add (Eq.symm ?_)
      rewrite [angle_comm A C B, angle_comm B A C, add_comm (∠ B C A)]
      exact angle_add_angle_add_angle_eq_pi C (triagle_no_rep h_tri |>.left.symm)
    rewrite [h_BAC_sin_add, Real.sin_add, le_add_iff_nonneg_right]
    exact mul_nonneg (angle_cos_nonneg_of_le_pi_div_two A C B h_acuteC.le) <|
      angle_sin_nonneg A B C
  simp [AffineMap.lineMap]; rewrite [hH, orthogonalProjection_apply_mem _
    (left_mem_affineSpan_pair ℝ B C), vadd_right_cancel_iff B]
  set s := line[ℝ, B, C] with hs
  set w := (s.direction.orthogonalProjection (A -ᵥ B) : V) with hw
  have h_BneC : B ≠ C := (triagle_no_rep h_tri).right.left
  have h_dir_span : s.direction = Submodule.span ℝ {C -ᵥ B} := by
    rw [hs, line_comm B C, direction_affineSpan (k := ℝ), vectorSpan_pair (k := ℝ) C B]
  have h_mem_span : w ∈ Submodule.span ℝ {C -ᵥ B} := by
    rw [← h_dir_span]; exact Submodule.coe_mem _
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp h_mem_span
  rewrite [← hr]; congr 1
  have h_inner_w : inner ℝ w (C -ᵥ B) = inner ℝ (A -ᵥ B) (C -ᵥ B) := by
    refine eq_of_sub_eq_zero ?_
    have h_H_expand : H -ᵥ A = w - (A -ᵥ B) := by
      rw [hH, orthogonalProjection_apply_mem _ (left_mem_affineSpan_pair ℝ B C),
        vadd_vsub_eq_sub_vsub, ← hw]
    rewrite [← inner_sub_left, ← h_H_expand, real_inner_comm]
    have h_CB_dir : C -ᵥ B ∈ s.direction := by
      rw [h_dir_span]; exact Submodule.mem_span_singleton.mpr ⟨1, by simp⟩
    have h_HA_ortho : (H -ᵥ A) ∈ s.directionᗮ := by
      rw [hH]; exact orthogonalProjection_vsub_mem_direction_orthogonal s A
    exact h_HA_ortho (C -ᵥ B) h_CB_dir
  rw [← hr, inner_smul_left] at h_inner_w
  have h_norm_ne₀ : ‖C -ᵥ B‖ ≠ 0 := norm_ne_zero_iff.mpr (vsub_ne_zero.mpr h_BneC.symm)
  have h_inner_self_ne : inner ℝ (C -ᵥ B) (C -ᵥ B) ≠ 0 := by
    rw [real_inner_self_eq_norm_sq]; exact pow_ne_zero 2 h_norm_ne₀
  have hr_eq : r = inner ℝ (A -ᵥ B) (C -ᵥ B) / inner ℝ (C -ᵥ B) (C -ᵥ B) := by
    field_simp [h_inner_self_ne]; rw [← h_inner_w]; congr
  have h_ratio : ‖A -ᵥ B‖ / ‖C -ᵥ B‖ = (∠ A C B).sin / (∠ B A C).sin := by
    field_simp [h_BAC_sin_pos.ne, h_norm_ne₀]
    simp [← dist_eq_norm_vsub, mul_comm (dist _ _) _]
    rw [sin_angle_mul_dist_eq_sin_angle_mul_dist A C B, dist_comm B A]
  have hr_t : r = ((∠ A C B).sin * (∠ A B C).cos / (∠ B A C).sin) := by
    rewrite [
      mul_div_right_comm, ← h_ratio, hr_eq, real_inner_self_eq_norm_sq,
      ← InnerProductGeometry.cos_angle_mul_norm_mul_norm, ← EuclideanGeometry.angle,
      mul_comm (Real.cos _) _, mul_div_right_comm, sq, mul_div_mul_comm,
      div_self h_norm_ne₀, mul_one,
    ]; rfl
  exact hr_t.symm

lemma wbtw_orthogonalProj_wbtw_acute (A B C P F : Pt)
  (h_tri : AffineIndependent ℝ ![A, B, C])
  (h_acuteB : ∠ A B C < π / 2) (h_acuteC : ∠ A C B < π / 2)
  (hP : Wbtw ℝ A P B) (hF : F = orthogonalProjection (line[ℝ, B, C]) P)
  : Wbtw ℝ B F C := by
  unfold Wbtw affineSegment at ⊢ hP; rewrite [Set.mem_image] at ⊢ hP
  let (eq := hH) H : Pt := orthogonalProjection (line[ℝ, B, C]) A
  have hH : Wbtw ℝ B H C := orthogonalProj_wbtw_acute A B C h_tri h_acuteB h_acuteC
  obtain ⟨r, ⟨hr_0, hr_1⟩, h_eq⟩ := hP
  obtain ⟨r', ⟨hr'_0, hr'_1⟩, h_eq'⟩ := hH
  let (eq := hr'') r'' := 1 - r
  have hF' : F = (AffineMap.lineMap H B) r := by
    set s := affineSpan ℝ {B, C} with hs
    have hB : B ∈ s := left_mem_affineSpan_pair ℝ B C
    have h_proj_lineMap (a b : Pt) (r : ℝ) :
      (orthogonalProjection s (AffineMap.lineMap a b r) : Pt)
      = AffineMap.lineMap (orthogonalProjection s a : Pt)
        (orthogonalProjection s b : Pt) r := by
      simp [orthogonalProjection_apply_mem s hB,
        AffineMap.lineMap_apply, vsub_vadd_eq_vsub_sub]
      congr 1; rewrite [← show (b -ᵥ B) - (a -ᵥ B) = b -ᵥ a by
        exact vsub_sub_vsub_cancel_right b a B]
      rewrite [map_sub]; rfl
    have h_projB : (orthogonalProjection s B : Pt) = B := by
      exact congrArg Subtype.val (orthogonalProjection_mem_subspace_eq_self ⟨B, hB⟩)
    calc
      F = (orthogonalProjection s P : Pt) := hF
      _ = (orthogonalProjection s (AffineMap.lineMap A B r) : Pt) := by rw [← h_eq]
      _ = AffineMap.lineMap ((orthogonalProjection s A : Pt))
        ((orthogonalProjection s B : Pt)) r := h_proj_lineMap A B r
      _ = AffineMap.lineMap H B r := by rw [hH, h_projB]
  conv at hF' =>
    simp [AffineMap.lineMap, ← h_eq', vsub_vadd_eq_vsub_sub, smul_smul, vadd_vadd]
    rewrite [← neg_smul, ← add_smul, neg_add_eq_sub, ← one_sub_mul, mul_comm, ← hr'']
  have hr''_0 : r'' ≥ 0 := by rewrite [hr'', ge_iff_le, sub_nonneg]; exact hr_1
  have hr''_1 : r'' ≤ 1 := by rewrite [hr'', sub_le_comm, sub_self]; exact hr_0
  have h_mul'_1 : r' * r'' ≤ 1 := mul_le_one₀ hr'_1 hr''_0 hr''_1
  use r' * r''
  exact ⟨Set.mem_Icc.mpr ⟨(mul_nonneg hr'_0 hr''_0), h_mul'_1⟩, hF'.symm⟩

lemma helper_EwbtwAD {A B C E D : Pt}
  (h_tri : AffineIndependent ℝ ![A, B, C]) (hE : Wbtw ℝ B E C)
  (hD_mem : D ∈ ((⟨_, h_tri⟩ : Triangle ℝ Pt).circumsphere : Sphere Pt))
  (hD_ne_A : D ≠ A) (hD_AE : D ∈ line[ℝ, A, E])
  : Wbtw ℝ A E D := by
  set ABC : Triangle ℝ Pt := ⟨_, h_tri⟩
  set O_ABC := ABC.circumsphere
  obtain ⟨h_AneB, h_BneC, h_AneC⟩ := triagle_no_rep h_tri
  exact power_nonpos_iff_wbtw O_ABC (ABC.mem_circumsphere 0) hD_mem
    hD_ne_A.symm (on_line_swap_right D A E hD_ne_A hD_AE) |>.mp <|
    power_nonpos_iff_wbtw O_ABC (ABC.mem_circumsphere 1) (ABC.mem_circumsphere 2)
    h_BneC (Wbtw.mem_affineSpan hE) |>.mpr hE

lemma helper_AneE {A B C E : Pt}
  (h_tri : AffineIndependent ℝ ![A, B, C]) (hE : Wbtw ℝ B E C)
  : A ≠ E := by
  by_contra! h_AeqE; subst h_AeqE; absurd h_tri
  refine collinear_iff_not_affineIndependent.mp ?_
  simp; refine collinear_iff_of_mem (p₀ := B) (by simp) |>.mpr ?_
  obtain ⟨r, ⟨⟨hr0, hr1⟩, heq⟩⟩ := hE; simp [AffineMap.lineMap] at heq
  use C -ᵥ B; simp; refine ⟨?_, ?_, ?_⟩
  · use 1; rewrite [one_smul, vsub_vadd]; rfl
  · use 0; rewrite [zero_smul, zero_vadd]; rfl
  · use r; exact heq.symm

lemma helper_AneM {A B C F M : Pt}
  (h_tri : AffineIndependent ℝ ![A, B, C]) (hF : Wbtw ℝ B F C)
  (hM : M = orthogonalProjection (line[ℝ, A, B]) F) (h_acuteA : ∠ B A C < π / 2)
  : A ≠ M := by
  by_contra! h; subst h
  have hBAC := angle_split h_tri hF |>.symm
  rewrite [angle_comm B A F, orthogonalProj_angle_pi_div_two F A A B hM |>.right] at hBAC
  rewrite [hBAC] at h_acuteA
  absurd neg_of_add_lt_right h_acuteA; push Not; exact angle_nonneg F A C

lemma helper_AneN {A B C F N : Pt}
  (h_tri : AffineIndependent ℝ ![A, B, C]) (hF : Wbtw ℝ B F C)
  (hN : N = orthogonalProjection (line[ℝ, A, C]) F) (h_acuteA : ∠ B A C < π / 2)
  : A ≠ N := by
  by_contra! h; subst h
  have hBAC := angle_split h_tri hF |>.symm
  rewrite [angle_comm B A F, orthogonalProj_angle_pi_div_two F A A C hN |>.right] at hBAC
  rewrite [hBAC] at h_acuteA
  absurd neg_of_add_lt_left h_acuteA; push Not; exact angle_nonneg F A B

lemma helper_not_coll_FAB {A B C F : Pt}
  (h_tri : AffineIndependent ℝ ![A, B, C])
  (hF : Wbtw ℝ B F C) (h_BneF : B ≠ F)
  : ¬ Collinear ℝ ({F, A, B} : Set Pt) := by
  obtain ⟨r, ⟨hr, heq⟩⟩ := hF; simp [AffineMap.lineMap] at heq
  have h_rne₀ : r ≠ 0 := by
    by_contra! h; subst h; absurd h_BneF
    simpa only [zero_smul, zero_vadd] using heq
  conv at heq => rewrite [Eq.comm, eq_vadd_iff_vsub_eq]
  have hC : C = r⁻¹ • (F -ᵥ B) +ᵥ B := by
    rewrite [heq, smul_smul, inv_mul_cancel₀ h_rne₀, one_smul, vsub_vadd]; rfl
  by_contra! h
  absurd h_tri; refine collinear_iff_not_affineIndependent.mp <| ?_; simp
  refine collinear_iff_of_mem (p₀ := B) (by simp) |>.mpr ?_
  obtain ⟨v, hp⟩ := collinear_iff_of_mem (p₀ := B) (by simp) |>.mp h
  obtain ⟨rA, hrA⟩ := hp A (by simp)
  obtain ⟨rF, hrF⟩ := hp F (by simp); subst hrF;
  use v; simp; refine ⟨?_, ?_, ?_⟩
  · use r⁻¹ * rF; rewrite [hC, vadd_vsub, smul_smul]; rfl
  · use 0; rewrite [zero_smul, zero_vadd]; rfl
  · use rA

lemma helper_BeqF_iff_CeqE {A B C E F : Pt}
  (h_tri : AffineIndependent ℝ ![A, B, C])
  (hE : Wbtw ℝ B E C)
  (hF : Wbtw ℝ B F C)
  (h_BAE_CAF : ∠ B A E = ∠ C A F)
  : B = F ↔ C = E := by
  obtain ⟨h_AneB, h_BneC, h_AneC⟩ := triagle_no_rep h_tri
  have h_splitE := angle_split h_tri hE
  have h_splitF := angle_split h_tri hF
  refine ⟨?_, ?_⟩
  <;> intro h <;> subst h
  <;> simp only [wbtw_self_left, wbtw_self_right, add_eq_right, add_eq_left,
        angle_self_of_ne h_AneB.symm, angle_self_of_ne h_AneC.symm]
        at hE hF h_splitE h_splitF
  <;> simp_all only
  · have h : ∠ C A E = 0 := by
      rw [angle_comm, eq_sub_of_add_eq' h_splitE, angle_comm C A B, sub_self]
    rcases angle_eq_zero_iff_eq_and_ne_or_sbtw.mp h with (h | h)
    · exact h.left
    by_contra! hCE; absurd h_tri; refine collinear_iff_not_affineIndependent_set.mp <|
      collinear_iff_of_mem (p₀ := C) (by simp) |>.mpr ?_
    obtain ⟨rB, ⟨hrB, hrBeq⟩⟩ := Set.mem_image _ _ _ |>.mp <|
      Wbtw.right_mem_image_Ici_of_left_ne (wbtw_comm.mp hE) hCE
    simp [AffineMap.lineMap] at hrBeq
    use E -ᵥ C; simp; refine ⟨?_, by use rB; exact hrBeq.symm, by use 0; simp⟩
    rcases h with (h | h)
    <;> obtain ⟨r, ⟨_, hreq⟩⟩ := Set.mem_image _ _ _ |>.mp <|
          Sbtw.right_mem_image_Ioi (sbtw_comm.mp h)
    <;> simp [← hreq, AffineMap.lineMap]
    · use 1 - r; rw [sub_smul, one_smul, sub_eq_add_neg, ← smul_neg,
        neg_vsub_eq_vsub_rev, add_comm, add_vadd, vsub_vadd]
    · use r
  · have h_BAF₀ : ∠ B A F = 0 := by
      rw [eq_sub_of_add_eq h_splitF, angle_comm F A C, sub_self]
    rcases angle_eq_zero_iff_eq_and_ne_or_sbtw.mp h_BAF₀ with (h | h)
    · exact h.left
    by_contra! hBF; absurd h_tri; refine collinear_iff_not_affineIndependent_set.mp <|
      collinear_iff_of_mem (p₀ := B) (by simp) |>.mpr ?_
    obtain ⟨rC, ⟨hrC, hrCeq⟩⟩ := Set.mem_image _ _ _ |>.mp <|
      Wbtw.right_mem_image_Ici_of_left_ne hF hBF; simp [AffineMap.lineMap] at hrCeq
    use F -ᵥ B; simp; refine ⟨?_, by use 0; simp, by use rC; exact hrCeq.symm⟩
    rcases h with (h | h)
    <;> obtain ⟨r, ⟨_, hreq⟩⟩ := Set.mem_image _ _ _ |>.mp <|
          Sbtw.right_mem_image_Ioi (sbtw_comm.mp h)
    <;> simp [← hreq, AffineMap.lineMap]
    · use 1 - r; rw [sub_smul, one_smul, sub_eq_add_neg, ← smul_neg,
        neg_vsub_eq_vsub_rev, add_comm, add_vadd, vsub_vadd]
    · use r

lemma helper_CeqD_iff_CeqE {A B C D E F : Pt}
  (h_tri : AffineIndependent ℝ ![A, B, C])
  (hE : Wbtw ℝ B E C)
  (h_BAE_CAF : ∠ B A E = ∠ C A F)
  (hD_mem : D ∈ ((⟨_, h_tri⟩ : Triangle ℝ Pt).circumsphere : Sphere Pt))
  (hD_ne_A : D ≠ A) (h_EwbtwAD : Wbtw ℝ A E D)
  : C = D ↔ C = E := by
  obtain ⟨h_AneB, h_BneC, h_AneC⟩ := triagle_no_rep h_tri
  refine ⟨?_, ?_⟩
  · intro h_CeqD; subst h_CeqD
    exact on_both_sides h_tri hE h_EwbtwAD
  · intro h_CeqE; subst h_CeqE
    set ABC : Triangle ℝ Pt := ⟨_, h_tri⟩
    exact wbtw_on_sphere_eq h_EwbtwAD (ABC.mem_circumsphere 0) (ABC.mem_circumsphere 2)
      hD_mem |>.resolve_left h_AneC.symm

lemma helper_BeqF_iff_CeqD {A B C D E F : Pt}
  (h_tri : AffineIndependent ℝ ![A, B, C])
  (hE : Wbtw ℝ B E C)
  (hF : Wbtw ℝ B F C)
  (h_BAE_CAF : ∠ B A E = ∠ C A F)
  (hD_mem : D ∈ ((⟨_, h_tri⟩ : Triangle ℝ Pt).circumsphere : Sphere Pt))
  (hD_ne_A : D ≠ A) (h_EwbtwAD : Wbtw ℝ A E D)
  : B = F ↔ C = D :=
  helper_BeqF_iff_CeqE h_tri hE hF h_BAE_CAF |>.trans <| Iff.symm <|
  helper_CeqD_iff_CeqE h_tri hE h_BAE_CAF hD_mem hD_ne_A h_EwbtwAD

lemma helper_ABACeqADAF {A B C D E F : Pt}
  [Fact (finrank ℝ V = 2)] [Oriented ℝ V (Fin 2)]
  (h_tri : AffineIndependent ℝ ![A, B, C])
  (h_acuteB : ∠ C B A < π / 2)
  (hE : Wbtw ℝ B E C)
  (hF : Wbtw ℝ B F C)
  (h_BAE_CAF : ∠ B A E = ∠ C A F)
  (hD_mem : D ∈ ((⟨_, h_tri⟩ : Triangle ℝ Pt).circumsphere : Sphere Pt))
  (h_DneA : D ≠ A) (h_AneE : A ≠ E) (h_EwbtwAD : Wbtw ℝ A E D)
  : dist A B * dist A C = dist A D * dist A F := by
  let ABC : Triangle ℝ Pt := ⟨_, h_tri⟩
  obtain ⟨h_AneB, h_BneC, h_AneC⟩ := triagle_no_rep h_tri
  suffices h_sim : Similar ![C, A, D] ![F, A, B] by
    obtain ⟨r, ⟨hr, h⟩⟩ := similar_iff_exists_pos_pairwise_dist_eq.mp h_sim
    have h_AD_rAB : dist A D = r * dist A B := by
      rewrite [dist_comm A D, dist_comm A B]
      have : (2 : Fin 3) ≠ 1 := by
        simp only [Fin.isValue, ne_eq, Fin.reduceEq, not_false_eq_true]
      simpa using h this
    have h_AC_rAF : dist A C = r * dist A F := by
      rewrite [dist_comm A C, dist_comm A F]
      have : (0 : Fin 3) ≠ 1 := by norm_num
      simpa using h this
    rewrite [h_AD_rAB, h_AC_rAF, ← mul_assoc]; congr 1; exact mul_comm _ r
  refine similar_comm.mp ?_
  by_cases! h_BE : B = E
  · subst h_BE
    have h_BeqD : B = D := wbtw_on_sphere_eq h_EwbtwAD
      (ABC.mem_circumsphere 0) (ABC.mem_circumsphere 1) hD_mem
      |>.resolve_left h_AneB.symm
    have h_CeqF : C = F := by
      rewrite [angle_self_of_ne h_AneB.symm] at h_BAE_CAF
      rcases angle_eq_zero_iff_ne_and_wbtw.mp h_BAE_CAF.symm with (⟨_, h⟩ | ⟨h_FneA, h⟩)
      · exact on_both_sides' h_tri hF h
      · exact on_both_sides h_tri hF h
    rewrite [h_BeqD, h_CeqF]; exact Similar.refl _
  by_cases! h_BF : B = F
  · have h_DeqC : D = C := helper_BeqF_iff_CeqD h_tri
      hE hF h_BAE_CAF hD_mem h_DneA h_EwbtwAD |>.mp h_BF |>.symm
    subst h_BF h_DeqC
    have hBA : dist B A ≠ 0 := dist_eq_zero.not.mpr h_AneB.symm
    have hDA : dist D A ≠ 0 := dist_eq_zero.not.mpr h_DneA
    refine similar_of_side_side hBA hDA ?_ ?_
    · rw [dist_comm B A, dist_comm D A]
    simp only [dist_self, mul_zero, zero_mul]
  have h_CneD : C ≠ D := helper_BeqF_iff_CeqD h_tri
    hE hF h_BAE_CAF hD_mem h_DneA h_EwbtwAD |>.not.mp h_BF
  have h_CneE : C ≠ E := helper_CeqD_iff_CeqE h_tri
    hE h_BAE_CAF hD_mem h_DneA h_EwbtwAD |>.not.mp h_CneD
  have h_not_coll_FAB : ¬ Collinear ℝ ({F, A, B} : Set Pt) :=
    helper_not_coll_FAB h_tri hF h_BF
  refine similar_of_angle_angle h_not_coll_FAB ?_ ?_
  · rewrite [← add_left_inj (∠ C A F), angle_comm F A B, angle_comm C A F,
      angle_split h_tri hF, ← angle_split h_tri hE, angle_comm F A C, h_BAE_CAF,
      add_comm, add_left_inj, angle_comm E A C]
    exact Wbtw.angle_eq_right C h_EwbtwAD h_AneE.symm
  have h_ABF_ABC : ∠ A B F = ∠ A B C := Wbtw.angle_eq_right A hF h_BF.symm
  rewrite [h_ABF_ABC]
  suffices h : ∡ A B C = ∡ A D C by
    refine angle_eq_iff_oangle_eq_of_sign_eq
      h_AneB h_BneC.symm h_DneA.symm h_CneD ?_ |>.mpr h
    congr 1
  have h_ABC_sign_ne₀ : (∡ A B C).sign ≠ 0 := oangle_sign_eq_zero_iff_collinear.not.mpr
    <| affineIndependent_iff_not_collinear_set.mp h_tri
  have h_two_zsmul_eq : (2 : ℤ) • ∡ A B C = (2 : ℤ) • ∡ A D C :=
    Sphere.two_zsmul_oangle_eq (mem_circumsphere ABC 0) (mem_circumsphere ABC 1)
    hD_mem (mem_circumsphere ABC 2) h_AneB.symm h_BneC h_DneA h_CneD.symm
  have h_EsbtwBC : Sbtw ℝ B E C := ⟨hE, h_BE.symm, h_CneE.symm⟩
  by_cases! h_DE : D = E
  · subst h_DE; absurd h_CneD
    exact wbtw_on_sphere_eq hE (ABC.mem_circumsphere 1) hD_mem (ABC.mem_circumsphere 2)
      |>.resolve_left h_BE.symm |>.symm
  have h_EsbtwAD : Sbtw ℝ A E D := ⟨h_EwbtwAD, h_AneE.symm, h_DE.symm⟩
  exact Real.Angle.two_zsmul_eq_iff_eq h_ABC_sign_ne₀
    (Sbtw.oangle_sign_eq_of_sbtw h_EsbtwAD (sbtw_comm.mp h_EsbtwBC))
    |>.mp h_two_zsmul_eq

snip end

problem cmo2000_p1
  [Fact (finrank ℝ V = 2)] [Oriented ℝ V (Fin 2)]
  (A B C E F M N D : Pt)
  (h_tri : AffineIndependent ℝ ![A, B, C])
  (h_acuteA : ∠ B A C < π / 2)
  (h_acuteB : ∠ C B A < π / 2)
  (h_acuteC : ∠ A C B < π / 2)
  (hE : Wbtw ℝ B E C)
  (hF : Wbtw ℝ B F C)
  (h_BAE_CAF : ∠ B A E = ∠ C A F)
  (hM : M = orthogonalProjection (line[ℝ, A, B]) F)
  (hN : N = orthogonalProjection (line[ℝ, A, C]) F)
  (hD_mem : D ∈ ((⟨_, h_tri⟩ : Triangle ℝ Pt).circumsphere : Sphere Pt))
  (hD_ne_A : D ≠ A) (hD_AE : D ∈ line[ℝ, A, E]) :
  area4 A M D N = area3 A B C := by
  unfold area4; rewrite [area_sin, area_sin, area_sin]
  simp only [mul_assoc]; rewrite [← mul_add, ← mul_assoc (dist A B)]; congr 1
  have h_BAC_E : ∠ B A E + ∠ E A C = ∠ B A C := angle_split h_tri hE
  have h_BAC_F : ∠ B A F + ∠ F A C = ∠ B A C := angle_split h_tri hF
  have h_MwbtwAB : Wbtw ℝ A M B := wbtw_comm.mp <| wbtw_orthogonalProj_wbtw_acute C B A
    F M (affine_indep₃_inv h_tri) h_acuteB (by rewrite [angle_comm]; exact h_acuteA)
    (wbtw_comm.mp hF) (by simp only [line_comm B A]; exact hM)
  have h_NwbtwAC : Wbtw ℝ A N C := wbtw_comm.mp <| wbtw_orthogonalProj_wbtw_acute B C A
    F N (affine_indep₃_rot h_tri) (by rewrite [angle_comm]; exact h_acuteC) h_acuteA
    hF (by simp only [line_comm C A]; exact hN)
  have h_EwbtwAD : Wbtw ℝ A E D := helper_EwbtwAD h_tri hE hD_mem hD_ne_A hD_AE
  have h_AneM : A ≠ M := helper_AneM h_tri hF hM h_acuteA
  have h_AneN : A ≠ N := helper_AneN h_tri hF hN h_acuteA
  have h_AneE : A ≠ E := helper_AneE h_tri hE
  have h_NAF_CAF : ∠ N A F = ∠ C A F :=
    Wbtw.angle_eq_left F h_NwbtwAC h_AneN.symm
  have h_MAD_BAE : ∠ M A D = ∠ B A E :=
    Eq.trans (Wbtw.angle_eq_left D h_MwbtwAB h_AneM.symm)
    (Wbtw.angle_eq_right B h_EwbtwAD h_AneE.symm |>.symm)
  have h_DAN_DAC : ∠ D A N = ∠ D A C :=
    Wbtw.angle_eq_right D h_NwbtwAC h_AneN.symm
  have h_DAN_EAC : ∠ D A N = ∠ E A C := Eq.trans h_DAN_DAC
    (Wbtw.angle_eq_left C h_EwbtwAD h_AneE.symm |>.symm)
  have h_BAF_EAC : ∠ B A F = ∠ E A C := Eq.trans (eq_sub_of_add_eq h_BAC_F)
    (sub_eq_of_eq_add <| Eq.trans
    h_BAC_E.symm (by rw [h_BAE_CAF, angle_comm F A C, add_comm]))
  have h_MAF_EAC : ∠ M A F = ∠ E A C := Eq.trans
    (Wbtw.angle_eq_left F h_MwbtwAB h_AneM.symm) <| h_BAF_EAC
  have h_AM : dist A M = dist A F * (∠ M A F).cos :=
    Eq.trans (cos_angle_mul_dist_of_angle_eq_pi_div_two
      (orthogonalProj_angle_pi_div_two F M A B hM |>.left) |>.symm)
      (by rewrite [mul_comm]; congr 1; exact dist_comm F A)
  have h_AN : dist A N = dist A F * (∠ N A F).cos :=
    Eq.trans (cos_angle_mul_dist_of_angle_eq_pi_div_two
      (orthogonalProj_angle_pi_div_two F N A C hN |>.left) |>.symm)
      (by rewrite [mul_comm]; congr 1; exact dist_comm F A)
  have h_ABACeqADAF : dist A B * dist A C = dist A D * dist A F :=
    helper_ABACeqADAF h_tri h_acuteB hE hF h_BAE_CAF hD_mem hD_ne_A h_AneE h_EwbtwAD
  rewrite [
    h_ABACeqADAF, h_AM, h_AN, ← h_BAC_E, Real.sin_add,
    h_MAD_BAE, h_BAE_CAF, h_NAF_CAF, h_DAN_EAC, h_MAF_EAC
  ]; ring

end Cmo2000P1
