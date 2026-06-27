/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Liao
-/

import Mathlib.Tactic
import Mathlib

import ProblemExtraction

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 2025, Problem 4

Let `H` be the orthocenter of an acute triangle `ABC`, let `F` be the foot of the altitude
from `C` to `AB`, and let `P` be the reflection of `H` across `BC`. Suppose that the
circumcircle of triangle `AFP` intersects line `BC` at two distinct points `X` and `Y`.
Prove that `CX = CY`.


-/

namespace Usamo2025P4

open EuclideanGeometry RealInnerProductSpace

snip begin

noncomputable def Mc (A H C : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  (2⁻¹ : ℝ) • (A - H + (2 : ℝ) • C)

lemma p4_reduction (B C O X Y : EuclideanSpace ℝ (Fin 2))
    (hperp : ⟪O -ᵥ C, B -ᵥ C⟫ = 0)
    (hX : X ∈ affineSpan ℝ ({B, C} : Set (EuclideanSpace ℝ (Fin 2))))
    (hY : Y ∈ affineSpan ℝ ({B, C} : Set (EuclideanSpace ℝ (Fin 2))))
    (hd : dist O X = dist O Y) :
    dist C X = dist C Y := by
  obtain ⟨s, hs⟩ : ∃ s : ℝ, X = (1 - s) • B + s • C := by
    rcases hX with ⟨ s, hs ⟩;
    rcases hs with ⟨ rfl | rfl, v, hv, rfl ⟩;
    · rw [ mem_vectorSpan_pair ] at hv;
      rcases hv with ⟨ r, rfl ⟩ ; exact ⟨ -r, by ext ; simpa using by ring ⟩ ;
    · rw [ mem_vectorSpan_pair ] at hv;
      rcases hv with ⟨ r, rfl ⟩ ; exact ⟨ 1 - r, by ext ; simpa using by ring ⟩ ;
  obtain ⟨u, hu⟩ : ∃ u : ℝ, Y = (1 - u) • B + u • C := by
    rcases hY with ⟨ u, hu ⟩;
    rcases hu with ⟨ rfl | rfl, v, hv, rfl ⟩ <;> simp_all +decide [ vectorSpan_pair ];
    · rcases Submodule.mem_span_singleton.mp hv with ⟨ t, rfl ⟩ ; exact ⟨ -t, by ext ; simpa using by ring ⟩ ;
    · obtain ⟨ t, rfl ⟩ := Submodule.mem_span_singleton.mp hv; exact ⟨ 1 - t, by ext ; simpa using by ring ⟩ ;
  simp_all +decide [ dist_eq_norm, EuclideanSpace.norm_eq ];
  rw [ Real.sqrt_inj ( by positivity ) ( by positivity ) ] at *;
  simp_all +decide [ Fin.sum_univ_two, inner ];
  grind

lemma p4_circumcenter (A B C H F P : EuclideanSpace ℝ (Fin 2))
    (hH1 : ⟪H -ᵥ A, C -ᵥ B⟫ = 0)
    (hH2 : ⟪H -ᵥ B, C -ᵥ A⟫ = 0)
    (hFline : F ∈ affineSpan ℝ ({A, B} : Set (EuclideanSpace ℝ (Fin 2))))
    (hFperp : ⟪C -ᵥ F, B -ᵥ A⟫ = 0)
    (hPperp : ⟪P -ᵥ H, C -ᵥ B⟫ = 0)
    (hPmid : midpoint ℝ H P ∈ affineSpan ℝ ({B, C} : Set (EuclideanSpace ℝ (Fin 2)))) :
    dist (Mc A H C) A = dist (Mc A H C) F ∧ dist (Mc A H C) A = dist (Mc A H C) P := by
  obtain ⟨v, hv⟩ : ∃ v : ℝ, midpoint ℝ H P = B + v • (C -ᵥ B) := by
    rcases hPmid with ⟨ v, hv ⟩;
    rcases hv with ⟨ rfl | rfl, w, hw, hw' ⟩ <;> simp_all +decide [ vectorSpan_pair ];
    · rw [ Submodule.mem_span_singleton ] at hw ; obtain ⟨ k, rfl ⟩ := hw ; exact ⟨ -k, by ext ; simpa using by ring ⟩;
    · obtain ⟨ k, hk ⟩ := Submodule.mem_span_singleton.mp hw; use 1 - k; simp_all +decide [ sub_smul, smul_sub ] ; abel_nf;
      exact hk ▸ by abel1;
  have hP : P = 2 • (B + v • (C -ᵥ B)) - H := by
    rw [ ← hv ] ; ext ; norm_num [ midpoint_eq_smul_add ] ; ring;
  obtain ⟨t, ht⟩ : ∃ t : ℝ, F = A + t • (B -ᵥ A) := by
    rcases hFline with ⟨ t, ht ⟩;
    rcases ht with ⟨ rfl | rfl, v, hv, rfl ⟩ <;> norm_num [ vectorSpan_pair ] at *;
    · rw [ Submodule.mem_span_singleton ] at hv ; obtain ⟨ k, rfl ⟩ := hv ; exact ⟨ -k, by ext ; norm_num ; ring ⟩;
    · rw [ Submodule.mem_span_singleton ] at hv;
      obtain ⟨ a, rfl ⟩ := hv; exact ⟨ 1 - a, by ext ; simpa using by ring ⟩ ;
  have hF : F = A + t • (B -ᵥ A) := by
    exact ht;

  unfold Mc
  constructor
  · simp_all +decide [dist_eq_norm, EuclideanSpace.norm_eq]
    rw [Real.sqrt_inj (by positivity) (by positivity)]
    simp_all +decide [Fin.sum_univ_two, inner]
    ring_nf at *
    grind
  · simp_all +decide [dist_eq_norm, EuclideanSpace.norm_eq]
    rw [Real.sqrt_inj (by positivity) (by positivity)]
    simp_all +decide [Fin.sum_univ_two, inner]
    ring_nf at *
    grind

lemma p4_perp (A B C H : EuclideanSpace ℝ (Fin 2))
    (hH1 : ⟪H -ᵥ A, C -ᵥ B⟫ = 0) :
    ⟪Mc A H C -ᵥ C, B -ᵥ C⟫ = 0 := by
  unfold Mc;
  norm_num [ Fin.sum_univ_two, inner ] at * ; linarith

lemma angle_lt_pi_div_two_inner_pos (p q r : EuclideanSpace ℝ (Fin 2))
    (hq1 : p ≠ q) (hq2 : r ≠ q) (h : ∠ p q r < Real.pi / 2) :
    0 < ⟪p -ᵥ q, r -ᵥ q⟫ := by
  have hcos : Real.cos (∠ p q r) = ⟪p -ᵥ q, r -ᵥ q⟫ / (‖p -ᵥ q‖ * ‖r -ᵥ q‖) := by
    rw [EuclideanGeometry.angle]; exact InnerProductGeometry.cos_angle _ _
  have hpos : 0 < Real.cos (∠ p q r) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, EuclideanGeometry.angle_nonneg p q r], h⟩
  rw [hcos] at hpos
  have hden : 0 < ‖p -ᵥ q‖ * ‖r -ᵥ q‖ := by
    apply mul_pos <;> rw [norm_pos_iff] <;> [exact sub_ne_zero.mpr hq1; exact sub_ne_zero.mpr hq2]
  nlinarith [mul_pos hpos hden, div_mul_cancel₀ (⟪p -ᵥ q, r -ᵥ q⟫) (ne_of_gt hden)]

lemma p4_not_collinear (A B C H F P O : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    (htri : AffineIndependent ℝ ![A, B, C])
    (hacuteA : ∠ B A C < Real.pi / 2)
    (hacuteB : ∠ A B C < Real.pi / 2)
    (hacuteC : ∠ B C A < Real.pi / 2)
    (hH1 : ⟪H -ᵥ A, C -ᵥ B⟫ = 0)
    (hH2 : ⟪H -ᵥ B, C -ᵥ A⟫ = 0)
    (hFline : F ∈ affineSpan ℝ ({A, B} : Set (EuclideanSpace ℝ (Fin 2))))
    (hFperp : ⟪C -ᵥ F, B -ᵥ A⟫ = 0)
    (hPperp : ⟪P -ᵥ H, C -ᵥ B⟫ = 0)
    (hPmid : midpoint ℝ H P ∈ affineSpan ℝ ({B, C} : Set (EuclideanSpace ℝ (Fin 2))))
    (hOA : dist O A = r) (hOF : dist O F = r) (hOP : dist O P = r) :
    ¬ Collinear ℝ ({A, F, P} : Set (EuclideanSpace ℝ (Fin 2))) := by
  have hAB : A ≠ B := by simpa using htri.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hAC : A ≠ C := by simpa using htri.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hBC : B ≠ C := by simpa using htri.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  have posA : 0 < ⟪B -ᵥ A, C -ᵥ A⟫ :=
    angle_lt_pi_div_two_inner_pos B A C hAB.symm hAC.symm hacuteA
  have posB : 0 < ⟪A -ᵥ B, C -ᵥ B⟫ :=
    angle_lt_pi_div_two_inner_pos A B C hAB hBC.symm hacuteB
  have posC : 0 < ⟪A -ᵥ C, B -ᵥ C⟫ := by
    have := angle_lt_pi_div_two_inner_pos B C A hBC hAC hacuteC
    rwa [real_inner_comm] at this
  have hAF : A ≠ F := by
    intro h; rw [← h] at hFperp; rw [real_inner_comm] at hFperp; linarith [posA]
  have hFP : F ≠ P := by
    intro hFP
    have hPA : ⟪P -ᵥ A, C -ᵥ B⟫ = 0 := by
      rw [← vsub_add_vsub_cancel P H A, inner_add_left, hPperp, hH1, add_zero]
    obtain ⟨s, hs⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hFline
    rw [AffineMap.lineMap_apply] at hs
    have hFmA : F -ᵥ A = s • (B -ᵥ A) := by rw [← hs]; simp
    have hBApos : 0 < ⟪B -ᵥ A, B -ᵥ A⟫ :=
      real_inner_self_pos.mpr (sub_ne_zero.mpr (Ne.symm hAB))
    have key : s * ⟪B -ᵥ A, C -ᵥ B⟫ = 0 := by
      have h2 : ⟪F -ᵥ A, C -ᵥ B⟫ = s * ⟪B -ᵥ A, C -ᵥ B⟫ := by
        rw [hFmA, inner_smul_left]; simp
      rw [hFP, hPA] at h2; linarith
    have hsval : ⟪C -ᵥ A, B -ᵥ A⟫ = s * ⟪B -ᵥ A, B -ᵥ A⟫ := by
      have h3 : ⟪C -ᵥ F, B -ᵥ A⟫ = ⟪C -ᵥ A, B -ᵥ A⟫ - s * ⟪B -ᵥ A, B -ᵥ A⟫ := by
        rw [← vsub_sub_vsub_cancel_right C F A, hFmA, inner_sub_left, inner_smul_left]; simp
      rw [hFperp] at h3; linarith
    have hsg : 0 < s := by
      rw [real_inner_comm] at posA
      nlinarith [hsval, posA, hBApos]
    have hzero : ⟪B -ᵥ A, C -ᵥ B⟫ = 0 := by
      rcases mul_eq_zero.mp key with h | h
      · linarith
      · exact h
    have hneg : ⟪A -ᵥ B, C -ᵥ B⟫ = - ⟪B -ᵥ A, C -ᵥ B⟫ := by
      rw [← inner_neg_left]; congr 1; rw [neg_vsub_eq_vsub_rev]
    rw [hzero, neg_zero] at hneg
    linarith [posB]
  have hAP : A ≠ P := by
    intro hAP
    rw [← hAP] at hPmid
    obtain ⟨u, hu⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hPmid
    rw [AffineMap.lineMap_apply] at hu
    have hmidA : midpoint ℝ H A -ᵥ A = (2 : ℝ)⁻¹ • (H -ᵥ A) := by
      rw [midpoint_comm]; exact midpoint_vsub_left A H
    have hHA : H -ᵥ A = (2 * u) • (C -ᵥ B) + (2 : ℝ) • (B -ᵥ A) := by
      have e : (u • (C -ᵥ B) +ᵥ B) -ᵥ A = (2 : ℝ)⁻¹ • (H -ᵥ A) := by rw [hu]; exact hmidA
      rw [vadd_vsub_assoc] at e
      have e2 : (2 : ℝ) • (u • (C -ᵥ B) + (B -ᵥ A)) = H -ᵥ A := by
        rw [e, smul_smul]; norm_num
      rw [smul_add, smul_smul] at e2
      linear_combination (norm := module) -e2
    have hHB : H -ᵥ B = (2 * u) • (C -ᵥ B) + (B -ᵥ A) := by
      have h : H -ᵥ B = (H -ᵥ A) - (B -ᵥ A) := by rw [vsub_sub_vsub_cancel_right]
      rw [h, hHA]; module
    have hm : ⟪C -ᵥ B, C -ᵥ A⟫ = ⟪A -ᵥ C, B -ᵥ C⟫ := by
      rw [show A -ᵥ C = -(C -ᵥ A) by rw [neg_vsub_eq_vsub_rev],
          show B -ᵥ C = -(C -ᵥ B) by rw [neg_vsub_eq_vsub_rev],
          inner_neg_neg, real_inner_comm]
    have hD : ⟪C -ᵥ B, C -ᵥ B⟫ = ⟪A -ᵥ B, C -ᵥ B⟫ + ⟪A -ᵥ C, B -ᵥ C⟫ := by
      have hmc : ⟪A -ᵥ C, B -ᵥ C⟫ = ⟪C -ᵥ A, C -ᵥ B⟫ := by rw [← hm, real_inner_comm]
      rw [hmc, ← inner_add_left]
      congr 1
      rw [add_comm, vsub_add_vsub_cancel]
    have hpBneg : ⟪B -ᵥ A, C -ᵥ B⟫ = - ⟪A -ᵥ B, C -ᵥ B⟫ := by
      rw [← inner_neg_left]; congr 1; rw [neg_vsub_eq_vsub_rev]
    have hE1 : u * (⟪A -ᵥ B, C -ᵥ B⟫ + ⟪A -ᵥ C, B -ᵥ C⟫) = ⟪A -ᵥ B, C -ᵥ B⟫ := by
      have h := hH1
      rw [hHA, inner_add_left, real_inner_smul_left, real_inner_smul_left, hD, hpBneg] at h
      linear_combination h / 2
    have hE2 : 2 * u * ⟪A -ᵥ C, B -ᵥ C⟫ = - ⟪B -ᵥ A, C -ᵥ A⟫ := by
      have h := hH2
      rw [hHB, inner_add_left, real_inner_smul_left, hm] at h
      linear_combination h
    nlinarith [hE1, hE2, posA, posB, posC, mul_pos posB posC]
  have hcosph : Cospherical ({A, F, P} : Set (EuclideanSpace ℝ (Fin 2))) := by
    refine ⟨O, r, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl <;> rw [dist_comm] <;> assumption
  have hai := hcosph.affineIndependent_of_mem_of_ne
    (Set.mem_insert _ _)
    (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    hAF hAP hFP
  rwa [affineIndependent_iff_not_collinear_set] at hai

lemma p4_lin_indep (A F P : EuclideanSpace ℝ (Fin 2))
    (h : ¬ Collinear ℝ ({A, F, P} : Set (EuclideanSpace ℝ (Fin 2)))) :
    LinearIndependent ℝ ![A -ᵥ F, A -ᵥ P] := by
  have hAmem : A ∈ ({A, F, P} : Set (EuclideanSpace ℝ (Fin 2))) := by simp
  rw [linearIndependent_fin2]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
  refine ⟨?_, ?_⟩
  · intro hP
    rw [vsub_eq_zero_iff_eq] at hP
    refine h ((collinear_iff_of_mem hAmem).2 ⟨F -ᵥ A, ?_⟩)
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp [← hP]⟩
  · intro a ha
    refine h ((collinear_iff_of_mem hAmem).2 ⟨P -ᵥ A, ?_⟩)
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | hpF | rfl
    · exact ⟨0, by simp⟩
    · subst p
      refine ⟨a, ?_⟩
      rw [eq_vadd_iff_vsub_eq, ← neg_vsub_eq_vsub_rev A F, ← ha, ← smul_neg,
        neg_vsub_eq_vsub_rev]
    · exact ⟨1, by simp⟩

snip end

problem usamo2025_p4
    (A B C H F P X Y : EuclideanSpace ℝ (Fin 2))
    (htri : AffineIndependent ℝ ![A, B, C])
    (hacuteA : ∠ B A C < Real.pi / 2)
    (hacuteB : ∠ A B C < Real.pi / 2)
    (hacuteC : ∠ B C A < Real.pi / 2)
    (hH1 : ⟪H -ᵥ A, C -ᵥ B⟫ = 0)
    (hH2 : ⟪H -ᵥ B, C -ᵥ A⟫ = 0)
    (hFline : F ∈ affineSpan ℝ ({A, B} : Set (EuclideanSpace ℝ (Fin 2))))
    (hFperp : ⟪C -ᵥ F, B -ᵥ A⟫ = 0)
    (hPperp : ⟪P -ᵥ H, C -ᵥ B⟫ = 0)
    (hPmid : midpoint ℝ H P ∈ affineSpan ℝ ({B, C} : Set (EuclideanSpace ℝ (Fin 2))))
    (hXline : X ∈ affineSpan ℝ ({B, C} : Set (EuclideanSpace ℝ (Fin 2))))
    (hYline : Y ∈ affineSpan ℝ ({B, C} : Set (EuclideanSpace ℝ (Fin 2))))
    (hXY : X ≠ Y)
    (hcirc : ∃ O : EuclideanSpace ℝ (Fin 2), ∃ r : ℝ,
        dist O A = r ∧ dist O F = r ∧ dist O P = r ∧ dist O X = r ∧ dist O Y = r) :
    dist C X = dist C Y := by
  obtain ⟨O, r, hOA, hOF, hOP, hOX, hOY⟩ := hcirc
  have hr_pos : 0 < r := by
    by_contra hr_nonpos
    refine hXY ?_
    rw [← dist_le_zero ] at *
    aesop
  have hOM : O = Mc A H C := by
    have h_eq_dist := Usamo2025P4.p4_circumcenter A B C H F P hH1 hH2 hFline hFperp hPperp hPmid
    have hd1 : ⟪O -ᵥ Mc A H C, A -ᵥ F⟫ = 0 :=
      inner_vsub_vsub_of_dist_eq_of_dist_eq
        (by rw [dist_comm F, dist_comm A]; exact h_eq_dist.1.symm)
        (by rw [dist_comm F, dist_comm A, hOF, hOA])
    have hd2 : ⟪O -ᵥ Mc A H C, A -ᵥ P⟫ = 0 :=
      inner_vsub_vsub_of_dist_eq_of_dist_eq
        (by rw [dist_comm P, dist_comm A]; exact h_eq_dist.2.symm)
        (by rw [dist_comm P, dist_comm A, hOP, hOA])
    have h_not_collinear : ¬ Collinear ℝ ({A, F, P} : Set (EuclideanSpace ℝ (Fin 2))) :=
      p4_not_collinear A B C H F P O r htri hacuteA hacuteB hacuteC hH1 hH2
        hFline hFperp hPperp hPmid hOA hOF hOP
    have h_lin_ind : LinearIndependent ℝ ![A -ᵥ F, A -ᵥ P] :=
      p4_lin_indep A F P h_not_collinear
    have h_span : Submodule.span ℝ (Set.range ![A -ᵥ F, A -ᵥ P]) = ⊤ :=
      h_lin_ind.span_eq_top_of_card_eq_finrank (by simp)
    have h_orthogonal : ∀ v ∈ Submodule.span ℝ (Set.range ![A -ᵥ F, A -ᵥ P]),
        ⟪O -ᵥ Mc A H C, v⟫ = 0 := by
      intro v hv
      rw [Submodule.mem_span_range_iff_exists_fun] at hv
      obtain ⟨f, rfl⟩ := hv
      rw [inner_sum]
      simp only [Fin.sum_univ_two, inner_smul_right, Matrix.cons_val_zero, Matrix.cons_val_one,
        hd1, hd2, mul_zero, add_zero]
    have hself : ⟪O -ᵥ Mc A H C, O -ᵥ Mc A H C⟫ = 0 :=
      h_orthogonal _ (h_span ▸ Submodule.mem_top)
    rw [inner_self_eq_zero] at hself
    exact vsub_eq_zero_iff_eq.mp hself
  apply p4_reduction B C O X Y (by
  exact hOM.symm ▸ p4_perp A B C H hH1) hXline hYline (by
  linarith)

end Usamo2025P4
