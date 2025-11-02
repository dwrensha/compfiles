/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Benpigchu
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 2014, Problem 4

Let P and Q be on segment BC of an acute triangle ABC such that
∠PAB = ∠BCA and ∠CAQ = ∠ABC. Let M and N be points on lines AB
and AQ, respectively, such that P is the midpoint of AM and Q
is the midpoint of AN. Prove that BM and CN meet on the
circumcircle of triangle ABC.
-/

namespace Imo2014P4

open scoped EuclideanGeometry

snip begin

open EuclideanGeometry Affine

local instance planeFiniteDim :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
  ⟨finrank_euclideanSpace_fin⟩

noncomputable local instance someOrientation :
    Module.Oriented ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2) :=
  ⟨Module.Basis.orientation (Module.finBasisOfFinrankEq _ _ planeFiniteDim.out)⟩

lemma angle_eq_of_oangle_eq {A₁ A₂ A₃ B₁ B₂ B₃ : EuclideanSpace ℝ (Fin 2)}
  (h: ∡ A₁ A₂ A₃ = ∡ B₁ B₂ B₃)
  (hA₁: A₁ ≠ A₂) (hA₂: A₃ ≠ A₂) (hB₁: B₁ ≠ B₂) (hB₂: B₃ ≠ B₂)
  : ∠ A₁ A₂ A₃ = ∠ B₁ B₂ B₃ := by
  rw [angle_eq_abs_oangle_toReal hA₁ hA₂, angle_eq_abs_oangle_toReal hB₁ hB₂, h]

lemma angle_eq_of_cos_angle_eq {A₁ A₂ A₃ B₁ B₂ B₃ : EuclideanSpace ℝ (Fin 2)}
  (h : Real.cos (∠ A₁ A₂ A₃) = Real.cos (∠ B₁ B₂ B₃)) : ∠ A₁ A₂ A₃ = ∠ B₁ B₂ B₃ := by
  unfold EuclideanGeometry.angle at *
  rw [InnerProductGeometry.cos_angle, InnerProductGeometry.cos_angle] at h
  unfold InnerProductGeometry.angle at *
  rw [h]

lemma eq_max_of_max_ne_top
  {A B : Submodule ℝ (EuclideanSpace ℝ (Fin 2))}
  (hA : Module.finrank ℝ A = 1)
  (h : A ⊔ B ≠ ⊤) : A = A ⊔ B := by
  apply Submodule.eq_of_le_of_finrank_eq le_sup_left
  rw [hA]
  have hAB := Submodule.finrank_le (A ⊔ B)
  rw [planeFiniteDim.out] at hAB
  have hAB' : 1 ≤ Module.finrank ℝ ↥(A ⊔ B) := by
    rw [← hA]
    exact Submodule.finrank_mono le_sup_left
  have hAB'' : Module.finrank ℝ ↥(A ⊔ B) ≠ 2 := by
    contrapose! h
    apply Submodule.eq_top_of_finrank_eq
    rw [planeFiniteDim.out, h]
  cutsat

lemma affineSpan_pair_finrank {A B : EuclideanSpace ℝ (Fin 2)}
  (hAB : A ≠ B): Module.finrank ℝ (affineSpan ℝ {A, B}).direction = 1 := by
  rw [direction_affineSpan]
  have h := affineIndependent_of_ne ℝ hAB
  have h' : Set.range ![A, B] = {A, B} := by
    simp
    rw [Set.pair_comm]
  rw [← h']
  apply AffineIndependent.finrank_vectorSpan h
  simp

lemma inter_nonempty_of_not_parallel
  {A₁ A₂ B₁ B₂ : EuclideanSpace ℝ (Fin 2)}
  (hA : A₁ ≠ A₂) (hB : B₁ ≠ B₂)
  (h : ¬line[ℝ, A₁, A₂] ∥ line[ℝ, B₁, B₂]) :
  Set.Nonempty ((line[ℝ, A₁, A₂] : Set _) ∩ (line[ℝ, B₁, B₂] : Set (EuclideanSpace ℝ (Fin 2)))) := by
  have hA' : (line[ℝ, A₁, A₂] : Set (EuclideanSpace ℝ (Fin 2))).Nonempty := by
    use A₁
    apply mem_affineSpan
    simp
  have hB' : (line[ℝ, B₁, B₂] : Set (EuclideanSpace ℝ (Fin 2))).Nonempty := by
    use B₁
    apply mem_affineSpan
    simp
  apply AffineSubspace.inter_nonempty_of_nonempty_of_sup_direction_eq_top hA' hB'
  contrapose! h
  rw [AffineSubspace.parallel_iff_direction_eq_and_eq_bot_iff_eq_bot]
  constructor
  · set A := (affineSpan ℝ {A₁, A₂}).direction
    set B := (affineSpan ℝ {B₁, B₂}).direction
    trans A ⊔ B
    · exact eq_max_of_max_ne_top (affineSpan_pair_finrank hA) h
    · symm
      rw [sup_comm] at *
      exact eq_max_of_max_ne_top (affineSpan_pair_finrank hB) h
  · rw [affineSpan_eq_bot, affineSpan_eq_bot]
    constructor <;> intro h' <;> contrapose! h' <;> simp

lemma mem_affineSpan_pair_of_collinear {A B C : EuclideanSpace ℝ (Fin 2)}
  (hBC : B ≠ C) (h : Collinear ℝ {A, B, C}) :
  A ∈ affineSpan ℝ {B, C} := by
  apply Collinear.mem_affineSpan_of_mem_of_ne h (by simp) (by simp) (by simp) hBC

lemma mem_circumsphere_of_concyclic
  (ABC : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (D : EuclideanSpace ℝ (Fin 2))
  (hABCD : Concyclic {D, ABC.points 0, ABC.points 1, ABC.points 2}) :
  D ∈ Affine.Simplex.circumsphere ABC := by
  have hABCD' := EuclideanGeometry.Concyclic.Cospherical hABCD
  rw [EuclideanGeometry.cospherical_iff_exists_sphere] at hABCD'
  rcases hABCD' with ⟨S, hS⟩
  have hABC := (Affine.Simplex.circumsphere_unique_dist_eq ABC).right
  have h : S = Affine.Simplex.circumsphere ABC := by
    apply hABC
    constructor
    · rw [Affine.Simplex.span_eq_top ABC planeFiniteDim.out]
      apply AffineSubspace.mem_top
    · intro x hx
      simp at hx
      rcases hx with ⟨i, hi⟩
      rw [← hi]
      fin_cases i <;> simp [-mem_sphere_iff_norm, -Metric.mem_sphere] at hi ⊢ <;> apply hS <;> simp
  rw [← h]
  apply hS
  simp

structure Imo2014q4Cfg where
  (A B C P Q M N : EuclideanSpace ℝ (Fin 2))
  (hABC : AffineIndependent ℝ ![A, B, C])
  (acuteA : ∠ C A B < Real.pi / 2)
  (acuteB : ∠ A B C < Real.pi / 2)
  (acuteC : ∠ B C A < Real.pi / 2)
  (hP : Wbtw ℝ B P C)
  (hQ : Wbtw ℝ B Q C)
  (hPAB : ∠ P A B = ∠ B C A)
  (hCAQ : ∠ C A Q = ∠ A B C)
  (hPAM : P = midpoint ℝ A M)
  (hQAN : Q = midpoint ℝ A N)

namespace Imo2014q4Cfg

variable (cfg : Imo2014q4Cfg)

def symm : Imo2014q4Cfg where
  A := cfg.A
  B := cfg.C
  C := cfg.B
  P := cfg.Q
  Q := cfg.P
  M := cfg.N
  N := cfg.M
  hABC := by
    rw [← affineIndependent_equiv (Equiv.swap (1 : Fin 3) 2)]
    convert cfg.hABC using 1
    ext x
    fin_cases x <;> rfl
  acuteA := by
    rw [angle_comm]
    exact cfg.acuteA
  acuteB := by
    rw [angle_comm]
    exact cfg.acuteC
  acuteC := by
    rw [angle_comm]
    exact cfg.acuteB
  hP := Wbtw.symm cfg.hQ
  hQ := Wbtw.symm cfg.hP
  hPAB := by
    rw [angle_comm cfg.Q cfg.A cfg.C]
    rw [angle_comm cfg.C cfg.B cfg.A]
    exact cfg.hCAQ
  hCAQ := by
    rw [angle_comm cfg.B cfg.A cfg.P]
    rw [angle_comm cfg.A cfg.C cfg.B]
    exact cfg.hPAB
  hPAM := cfg.hQAN
  hQAN := cfg.hPAM

noncomputable def L := midpoint ℝ cfg.B cfg.C

def ABC : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)) :=
  ⟨![cfg.A, cfg.B, cfg.C], cfg.hABC⟩

def D_set := ((line[ℝ, cfg.B, cfg.M] : Set _) ∩ (line[ℝ, cfg.C, cfg.N] : Set (EuclideanSpace ℝ (Fin 2))))

lemma L_symm : cfg.L = cfg.symm.L := by
  simp [L, symm]
  exact midpoint_comm cfg.B cfg.C

lemma D_symm : cfg.D_set = cfg.symm.D_set := by
  simp [D_set, symm]
  rw [Set.inter_comm]

lemma B_ne_A : cfg.B ≠ cfg.A := by
    exact cfg.hABC.injective.ne (by decide : (1 : Fin 3) ≠ 0)

lemma C_ne_A : cfg.C ≠ cfg.A := by
    exact cfg.hABC.injective.ne (by decide : (2 : Fin 3) ≠ 0)

lemma C_ne_B : cfg.C ≠ cfg.B := by
    exact cfg.hABC.injective.ne (by decide : (2 : Fin 3) ≠ 1)

lemma sin_angle_in_ABC_pos (i j k : Fin 3) (h : Function.Injective ![i, j, k])
  : Real.sin (∠ (cfg.ABC.points i) (cfg.ABC.points j) (cfg.ABC.points k)) ≠ 0 := by
  apply EuclideanGeometry.sin_ne_zero_of_not_collinear
  rw [← affineIndependent_iff_not_collinear_set]
  have h' : ![cfg.ABC.points i, cfg.ABC.points j, cfg.ABC.points k] = Function.comp cfg.ABC.points ![i, j, k]:= by
    ext x
    fin_cases x <;> simp
  rw [h']
  apply AffineIndependent.comp_embedding ⟨_, h⟩
  exact cfg.ABC.independent

lemma angle_in_ABC_pos (i j k : Fin 3) (h : Function.Injective ![i, j, k])
  : ∠ (cfg.ABC.points i) (cfg.ABC.points j) (cfg.ABC.points k) ≠ 0 := by
  have h':= sin_angle_in_ABC_pos cfg i j k h
  contrapose! h'
  rw [h']
  exact Real.sin_zero

lemma P_ne_B : cfg.P ≠ cfg.B := by
  have h' := angle_self_of_ne cfg.B_ne_A
  contrapose! h'
  nth_rw 1 [← h']
  rw [cfg.hPAB]
  exact angle_in_ABC_pos cfg (1 : Fin 3) 2 0 (by decide)

lemma oangle_PBA_eq_CBA : ∡ cfg.P cfg.B cfg.A = ∡ cfg.C cfg.B cfg.A := by
  apply Wbtw.oangle_eq_left cfg.hP
  exact cfg.P_ne_B

lemma PBA_eq_CBA : ∠ cfg.P cfg.B cfg.A = ∠ cfg.C cfg.B cfg.A := by
  exact angle_eq_of_oangle_eq cfg.oangle_PBA_eq_CBA cfg.P_ne_B cfg.B_ne_A.symm cfg.C_ne_B cfg.B_ne_A.symm

lemma P_ne_A : cfg.P ≠ cfg.A := by
  have h' := angle_self_of_ne cfg.B_ne_A.symm
  contrapose! h'
  nth_rw 1 [← h']
  rw [PBA_eq_CBA]
  exact angle_in_ABC_pos cfg (2 : Fin 3) 1 0 (by decide)

lemma oangle_PAB_eq_BCA : ∡ cfg.P cfg.A cfg.B = ∡ cfg.B cfg.C cfg.A := by
  apply oangle_eq_of_angle_eq_of_sign_eq (cfg.hPAB)
  rw [← oangle_swap₂₃_sign cfg.P cfg.B cfg.A]
  rw [← oangle_swap₁₂_sign cfg.C cfg.B cfg.A]
  rw [cfg.oangle_PBA_eq_CBA]

lemma APB_eq_CBA : ∠ cfg.B cfg.P cfg.A = ∠ cfg.B cfg.A cfg.C := by
  have h₁ := angle_add_angle_add_angle_eq_pi cfg.P cfg.B_ne_A
  have h₂ := angle_add_angle_add_angle_eq_pi cfg.C cfg.B_ne_A
  rw [← h₂, angle_comm cfg.A cfg.B cfg.P, cfg.hPAB] at h₁
  rw [PBA_eq_CBA] at h₁
  rw [angle_comm cfg.C cfg.B cfg.A, add_right_comm, add_left_cancel_iff] at h₁
  rw [h₁, angle_comm]

lemma AB_to_AP_eq_CB_to_CA : dist cfg.A cfg.B / dist cfg.A cfg.P = dist cfg.C cfg.B / dist cfg.C cfg.A := by
  have h₁ := law_sin cfg.B cfg.P cfg.A
  have h₂ := law_sin cfg.A cfg.B cfg.C
  rw [div_eq_div_iff (dist_ne_zero.mpr cfg.P_ne_A.symm) (dist_ne_zero.mpr cfg.C_ne_A)]
  rw [cfg.APB_eq_CBA, angle_comm cfg.A cfg.B cfg.P, cfg.PBA_eq_CBA] at h₁
  rw [angle_comm cfg.A cfg.B cfg.C, angle_comm cfg.C cfg.A cfg.B] at h₂
  have hBAC : Real.sin (∠ cfg.B cfg.A cfg.C) ≠ 0 := by
    exact sin_angle_in_ABC_pos cfg (1: Fin 3) 0 2 (by decide)
  have hCBA : Real.sin (∠ cfg.C cfg.B cfg.A) ≠ 0 := by
    exact sin_angle_in_ABC_pos cfg (2: Fin 3) 1 0 (by decide)
  apply mul_right_cancel₀ hBAC
  apply mul_left_cancel₀ hCBA
  rw [mul_assoc, ← mul_assoc, ← h₁]
  nth_rw 3 [mul_comm]
  rw [← h₂, dist_comm cfg.A cfg.P, dist_comm cfg.B cfg.C]
  ring

lemma AB_to_AM_eq_CL_to_CA : dist cfg.A cfg.B / dist cfg.A cfg.M = dist cfg.C cfg.L / dist cfg.C cfg.A := by
  rw [L, dist_right_midpoint, dist_comm cfg.B cfg.C, mul_div_assoc]
  rw [← AB_to_AP_eq_CB_to_CA, cfg.hPAM, dist_left_midpoint, Real.norm_ofNat]
  ring

lemma wbtw_APM : Wbtw ℝ cfg.A cfg.P cfg.M := by
  rw [cfg.hPAM]
  exact wbtw_midpoint _ _ _

lemma wbtw_CLB : Wbtw ℝ cfg.C cfg.L cfg.B := by
  rw [L, wbtw_comm]
  exact wbtw_midpoint _ _ _

lemma C_ne_L : cfg.C ≠ cfg.L := by
  rw [← dist_pos, L, dist_right_midpoint, Real.norm_ofNat]
  apply mul_pos (by norm_num)
  rw [dist_pos]
  exact cfg.C_ne_B.symm

lemma oangle_BAM_eq_LCA : ∡ cfg.M cfg.A cfg.B = ∡ cfg.L cfg.C cfg.A := by
  rw [← Wbtw.oangle_eq_left cfg.wbtw_APM cfg.P_ne_A]
  rw [Wbtw.oangle_eq_left cfg.wbtw_CLB cfg.C_ne_L.symm]
  exact cfg.oangle_PAB_eq_BCA

lemma M_ne_A : cfg.M ≠ cfg.A := by
  have h' := cfg.P_ne_A
  contrapose! h'
  rw [← dist_eq_zero, cfg.hPAM, dist_comm, dist_left_midpoint]
  apply mul_eq_zero_of_right
  rw [dist_eq_zero]
  exact h'.symm

lemma BAM_eq_LCA : ∠ cfg.M cfg.A cfg.B = ∠ cfg.L cfg.C cfg.A := by
  exact angle_eq_of_oangle_eq cfg.oangle_BAM_eq_LCA cfg.M_ne_A cfg.B_ne_A cfg.C_ne_L.symm cfg.C_ne_A.symm

lemma BM_to_AM_eq_LA_to_CA: dist cfg.B cfg.M / dist cfg.A cfg.M = dist cfg.L cfg.A / dist cfg.C cfg.A := by
  rw [← mul_self_inj (by positivity) (by positivity)]
  rw [← pow_two, ← pow_two, div_pow, div_pow]
  rw [pow_two, pow_two, pow_two, pow_two]
  rw [law_cos cfg.B cfg.A cfg.M, law_cos cfg.L cfg.C cfg.A]
  rw [sub_div, sub_div, add_div, add_div, angle_comm, cfg.BAM_eq_LCA]
  rw [← pow_two, ← pow_two, ← pow_two, ← div_pow, ← div_pow]
  rw [← pow_two, ← pow_two, ← pow_two, ← div_pow, ← div_pow]
  rw [dist_comm cfg.M cfg.A, dist_comm cfg.A cfg.C]
  nth_rw 1 [mul_div_right_comm]
  nth_rw 2 [mul_div_right_comm]
  nth_rw 3 [pow_two]
  nth_rw 5 [pow_two]
  rw [← div_div, ← div_div]
  nth_rw 1 [← mul_div]
  nth_rw 2 [← mul_div]
  rw [div_self (dist_ne_zero.mpr cfg.M_ne_A.symm), div_self (dist_ne_zero.mpr cfg.C_ne_A)]
  rw [mul_one, mul_one, mul_div_assoc, mul_div_assoc]
  rw [dist_comm cfg.B cfg.A, dist_comm cfg.L cfg.C]
  rw [AB_to_AM_eq_CL_to_CA]

lemma L_ne_A : cfg.L ≠ cfg.A := by
  have h' := wbtw_midpoint ℝ cfg.B cfg.C
  rw [← L] at h'
  contrapose! h'
  rw [h']
  have h := AffineIndependent.not_wbtw_of_injective (1 : Fin 3) 0 2 (by decide) cfg.ABC.independent
  exact h

lemma B_ne_M : cfg.B ≠ cfg.M := by
  intro h'
  rw [← dist_eq_zero] at *
  have h'' := cfg.BM_to_AM_eq_LA_to_CA
  rw [h', zero_div] at h''
  symm at h''
  rw [div_eq_zero_iff] at h''
  contrapose! h''
  rw [dist_ne_zero, dist_ne_zero]
  exact ⟨cfg.L_ne_A, cfg.C_ne_A⟩

lemma MBA_eq_CLA : ∠ cfg.M cfg.B cfg.A = ∠ cfg.C cfg.L cfg.A := by
  apply angle_eq_of_cos_angle_eq
  have h₁ := (law_cos cfg.M cfg.B cfg.A).symm
  have h₂ := (law_cos cfg.A cfg.L cfg.C).symm
  rw [← div_eq_one_iff_eq (mul_self_ne_zero.mpr (dist_ne_zero.mpr cfg.M_ne_A))] at h₁
  rw [← div_eq_one_iff_eq (mul_self_ne_zero.mpr (dist_ne_zero.mpr cfg.C_ne_A.symm))] at h₂
  rw [← h₂] at h₁
  rw [sub_div, sub_div, add_div, add_div] at h₁
  rw [← pow_two, ← pow_two, ← pow_two, ← div_pow, ← div_pow] at h₁
  rw [← pow_two, ← pow_two, ← pow_two, ← div_pow, ← div_pow] at h₁
  nth_rw 3 [pow_two] at h₁
  nth_rw 5 [pow_two] at h₁
  nth_rw 1 [mul_div_right_comm] at h₁
  nth_rw 2 [mul_div_right_comm] at h₁
  rw [← div_div, ← div_div] at h₁
  nth_rw 1 [← mul_div] at h₁
  nth_rw 2 [← mul_div] at h₁
  nth_rw 1 [← div_mul_eq_mul_div,] at h₁
  nth_rw 2 [← div_mul_eq_mul_div,] at h₁
  rw [← mul_div, ← mul_div] at h₁
  rw [dist_comm cfg.M cfg.A, dist_comm cfg.A cfg.C] at h₁
  rw [dist_comm cfg.M cfg.B, dist_comm cfg.A cfg.L] at h₁
  rw [cfg.BM_to_AM_eq_LA_to_CA, cfg.AB_to_AM_eq_CL_to_CA] at h₁
  rw [sub_right_inj] at h₁
  rw [angle_comm cfg.C cfg.L cfg.A]
  apply mul_left_cancel₀ _ h₁
  rw [mul_assoc]
  apply mul_ne_zero (by norm_num)
  apply mul_ne_zero
  · apply div_ne_zero
    · exact dist_ne_zero.mpr cfg.L_ne_A
    · exact dist_ne_zero.mpr cfg.C_ne_A
  · apply div_ne_zero
    · exact dist_ne_zero.mpr cfg.C_ne_L
    · exact dist_ne_zero.mpr cfg.C_ne_A

lemma oangle_MBA_eq_CLA : ∡ cfg.M cfg.B cfg.A = ∡ cfg.C cfg.L cfg.A := by
  apply oangle_eq_of_angle_eq_of_sign_eq (cfg.MBA_eq_CLA)
  rw [← oangle_swap₂₃_sign cfg.M cfg.A cfg.B]
  rw [← oangle_swap₁₂_sign cfg.L cfg.C cfg.A]
  rw [cfg.oangle_BAM_eq_LCA]

lemma oangle_NCA_eq_BLA: ∡ cfg.N cfg.C cfg.A = ∡ cfg.B cfg.L cfg.A := by
  have h := cfg.symm.oangle_MBA_eq_CLA
  rw [← L_symm] at h
  simp [symm] at h
  exact h

lemma oangle_NCA_MBA: (2 : ℤ) • ∡ cfg.N cfg.C cfg.A = (2 : ℤ) • ∡ cfg.M cfg.B cfg.A := by
  rw [oangle_MBA_eq_CLA, oangle_NCA_eq_BLA]
  have hL := sbtw_midpoint_of_ne ℝ cfg.C_ne_B.symm
  rw [← L] at hL
  rw [Sbtw.oangle_eq_add_pi_left hL cfg.L_ne_A.symm]
  rw [smul_add, two_zsmul (Real.pi : Real.Angle), Real.Angle.coe_pi_add_coe_pi, add_zero]

lemma N_ne_Q : cfg.M ≠ cfg.P := by
  rw [cfg.hPAM, ← dist_ne_zero, dist_right_midpoint]
  apply mul_ne_zero (by norm_num)
  rw [dist_ne_zero]
  exact cfg.M_ne_A.symm

lemma D_ne_C {D : EuclideanSpace ℝ (Fin 2)} (hD : D ∈ cfg.D_set) : D ≠ cfg.C := by
  rw [D_set, Set.mem_inter_iff] at hD
  intro h'
  rw [h'] at hD
  have hBCM := collinear_insert_of_mem_affineSpan_pair hD.left
  rw [Set.pair_comm, Set.insert_comm] at hBCM
  apply mem_affineSpan_pair_of_collinear cfg.C_ne_B at hBCM
  have hBPC := Wbtw.collinear cfg.hP
  rw [Set.insert_comm, Set.pair_comm] at hBPC
  apply mem_affineSpan_pair_of_collinear cfg.C_ne_B at hBPC
  have hPMBC := collinear_insert_insert_of_mem_affineSpan_pair hBCM hBPC
  nth_rw 2 [Set.insert_comm] at hPMBC
  rw [Set.pair_comm] at hPMBC
  nth_rw 1 [Set.insert_comm] at hPMBC
  nth_rw 2 [Set.insert_comm] at hPMBC
  have hBMP := Collinear.subset (Set.subset_insert _ _) hPMBC
  nth_rw 1 [Set.insert_comm] at hPMBC
  have hCMP := Collinear.subset (Set.subset_insert _ _) hPMBC
  apply mem_affineSpan_pair_of_collinear cfg.N_ne_Q at hBMP
  apply mem_affineSpan_pair_of_collinear cfg.N_ne_Q at hCMP
  have hAMP := Wbtw.collinear (wbtw_midpoint ℝ cfg.A cfg.M)
  rw [← cfg.hPAM, Set.pair_comm] at hAMP
  apply mem_affineSpan_pair_of_collinear cfg.N_ne_Q at hAMP
  have hABC := collinear_triple_of_mem_affineSpan_pair hAMP hBMP hCMP
  contrapose! hABC
  rw [← affineIndependent_iff_not_collinear_set]
  exact cfg.hABC

lemma D_ne_B {D : EuclideanSpace ℝ (Fin 2)} (hD : D ∈ cfg.D_set) : D ≠ cfg.B := by
  rw [cfg.D_symm] at hD
  have h := cfg.symm.D_ne_C hD
  simp [symm] at h
  exact h

lemma oangle_DBA_MBA {D : EuclideanSpace ℝ (Fin 2)} (hD : D ∈ cfg.D_set) :
  (2 : ℤ) • ∡ D cfg.B cfg.A = (2 : ℤ) • ∡ cfg.M cfg.B cfg.A := by
  rw [D_set, Set.mem_inter_iff] at hD
  have hDBM := collinear_insert_of_mem_affineSpan_pair hD.left
  exact Collinear.two_zsmul_oangle_eq_left hDBM (cfg.D_ne_B hD) cfg.B_ne_M.symm

lemma oangle_DCA_NCA {D : EuclideanSpace ℝ (Fin 2)} (hD : D ∈ cfg.D_set) :
  (2 : ℤ) • ∡ D cfg.C cfg.A = (2 : ℤ) • ∡ cfg.N cfg.C cfg.A := by
  rw [cfg.D_symm] at hD
  have h := cfg.symm.oangle_DBA_MBA hD
  simp [symm] at h
  exact h

theorem result₁ : Set.Nonempty cfg.D_set := by
  apply inter_nonempty_of_not_parallel cfg.B_ne_M cfg.symm.B_ne_M
  simp [symm]
  intro h'
  have h'' := AffineSubspace.Parallel.refl (affineSpan ℝ {cfg.B, cfg.C})
  nth_rw 1 [Set.pair_comm] at h''
  nth_rw 1 [Set.pair_comm] at h'
  nth_rw 2 [Set.pair_comm] at h'
  have h_CBM_BCM := EuclideanGeometry.two_zsmul_oangle_of_parallel h'' h'
  have h_CBM := EuclideanGeometry.oangle_sub_right cfg.C_ne_B cfg.B_ne_M.symm cfg.B_ne_A.symm
  have h_BCM := EuclideanGeometry.oangle_sub_right cfg.C_ne_B.symm cfg.symm.B_ne_M.symm cfg.C_ne_A.symm
  simp [symm] at h_BCM
  rw [← h_CBM, ← h_BCM, zsmul_sub, zsmul_sub] at h_CBM_BCM
  rw [cfg.oangle_NCA_MBA, sub_left_inj, ← sub_eq_zero, ← zsmul_sub] at h_CBM_BCM
  rw [oangle_rev cfg.A cfg.C cfg.B, sub_neg_eq_add] at h_CBM_BCM
  rw [← add_right_inj ((2 : ℤ) • ∡ cfg.B cfg.A cfg.C), add_zero, ← zsmul_add, ← add_assoc, add_right_comm] at h_CBM_BCM
  rw [EuclideanGeometry.oangle_add_oangle_add_oangle_eq_pi cfg.B_ne_A.symm cfg.C_ne_A  cfg.C_ne_B.symm] at h_CBM_BCM
  symm at h_CBM_BCM
  rw [two_zsmul (Real.pi : Real.Angle), Real.Angle.coe_pi_add_coe_pi] at h_CBM_BCM
  rw [Real.Angle.two_zsmul_eq_zero_iff, oangle_eq_zero_or_eq_pi_iff_collinear] at h_CBM_BCM
  rw [Set.insert_comm, collinear_iff_not_affineIndependent_set] at h_CBM_BCM
  contrapose! h_CBM_BCM
  exact cfg.hABC

theorem result₂ : cfg.D_set ⊆ Affine.Simplex.circumsphere cfg.ABC := by
  rintro D hD
  have h : (2 : ℤ) • ∡ D cfg.C cfg.A = (2 : ℤ) • ∡ D cfg.B cfg.A := by
    rw [cfg.oangle_DBA_MBA hD]
    rw [cfg.oangle_DCA_NCA hD]
    exact cfg.oangle_NCA_MBA
  rcases EuclideanGeometry.concyclic_or_collinear_of_two_zsmul_oangle_eq h with hh|hh
  · apply mem_circumsphere_of_concyclic cfg.ABC D
    simp [ABC]
    nth_rw 2 [Set.insert_comm]
    rw [Set.pair_comm]
    nth_rw 2 [Set.insert_comm]
    exact hh
  · have h' : {cfg.A, cfg.B, cfg.C} ⊆ ({D, cfg.C, cfg.B, cfg.A} : Set _) := by
      trans {cfg.C, cfg.B, cfg.A}
      · rw [Set.insert_comm, Set.pair_comm, Set.insert_comm]
      · exact Set.subset_insert D {cfg.C, cfg.B, cfg.A}
    apply Collinear.subset h' at hh
    rw [collinear_iff_not_affineIndependent_set] at hh
    contrapose! hh
    exact cfg.hABC

end Imo2014q4Cfg

snip end

problem imo2014_p4
    (A B C P Q M N : EuclideanSpace ℝ (Fin 2))
    (hABC : AffineIndependent ℝ ![A, B, C])
    (acuteA : ∠ C A B < Real.pi / 2)
    (acuteB : ∠ A B C < Real.pi / 2)
    (acuteC : ∠ B C A < Real.pi / 2)
    (hP : Wbtw ℝ B P C)
    (hQ : Wbtw ℝ B Q C)
    (hPAB : ∠ P A B = ∠ B C A)
    (hCAQ : ∠ C A Q = ∠ A B C)
    (hPAM : P = midpoint ℝ A M)
    (hQAN : Q = midpoint ℝ A N)
    : let ABC : Affine.Triangle _ _ := ⟨![A, B, C], hABC⟩
      let D := (line[ℝ, B, M] : Set _) ∩ (line[ℝ, C, N] : Set (EuclideanSpace ℝ (Fin 2)))
      Set.Nonempty D ∧ D ⊆ Affine.Simplex.circumsphere ABC := by
  set cfg : Imo2014q4Cfg := ⟨A, B, C, P, Q, M, N, hABC, acuteA, acuteB, acuteC, hP, hQ, hPAB, hCAQ, hPAM, hQAN⟩
  exact ⟨cfg.result₁, cfg.result₂⟩


end Imo2014P4
