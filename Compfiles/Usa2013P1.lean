/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 2013, Problem 1

In triangle ABC, points P, Q, R lie on sides BC, CA, AB, respectively.
Let ω_A, ω_B, ω_C denote the circumcircles of triangles AQR, BRP, CPQ,
respectively. Given the fact that segment AP intersects ω_A, ω_B, ω_C
again at X, Y, Z respectively, prove that YX/XZ = BP/PC.
-/

namespace Usa2013P1

open scoped RealInnerProductSpace

snip begin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A Stewart-type identity: the squared norm of an affine combination
`(1 - t) • u + t • v` is a quadratic polynomial in `t`. -/
lemma norm_sq_affine_comb (t : ℝ) (u v : E) :
    ‖(1 - t) • u + t • v‖ ^ 2
      = (1 - t) * ‖u‖ ^ 2 + t * ‖v‖ ^ 2 - t * (1 - t) * ‖u - v‖ ^ 2 := by
  rw [norm_add_sq_real, norm_sub_sq_real, norm_smul, norm_smul,
    real_inner_smul_left, real_inner_smul_right]
  simp only [Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- The squared distance from a point `A + c • e` on a line to a fixed point `O`,
as a quadratic polynomial in the parameter `c`. -/
lemma norm_sq_add_smul_sub (A O e : E) (c : ℝ) :
    ‖A + c • e - O‖ ^ 2
      = ‖A - O‖ ^ 2 + c * (2 * ⟪A - O, e⟫) + c ^ 2 * ‖e‖ ^ 2 := by
  have h : A + c • e - O = (A - O) + c • e := by abel
  rw [h, norm_add_sq_real, real_inner_smul_right, norm_smul]
  simp only [Real.norm_eq_abs, mul_pow, sq_abs]
  ring

snip end

problem usa2013_p1
    {A B C P Q R X Y Z OA OB OC : EuclideanSpace ℝ (Fin 2)}
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))))
    -- P, Q, R lie on the sides BC, CA, AB (strictly between the vertices).
    (hP : ∃ t : ℝ, 0 < t ∧ t < 1 ∧ P = B + t • (C - B))
    (hQ : ∃ w : ℝ, 0 < w ∧ w < 1 ∧ Q = A + w • (C - A))
    (hR : ∃ v : ℝ, 0 < v ∧ v < 1 ∧ R = A + v • (B - A))
    -- OA, OB, OC are the circumcenters of AQR, BRP, CPQ.
    (hOA : dist OA A = dist OA Q ∧ dist OA Q = dist OA R)
    (hOB : dist OB B = dist OB R ∧ dist OB R = dist OB P)
    (hOC : dist OC C = dist OC P ∧ dist OC P = dist OC Q)
    -- X, Y, Z are the second intersections of segment AP with ω_A, ω_B, ω_C.
    (hX : (∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ X = A + s • (P - A)) ∧ X ≠ A ∧
      dist X OA = dist A OA)
    (hY : (∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ Y = A + s • (P - A)) ∧ Y ≠ P ∧
      dist Y OB = dist P OB)
    (hZ : (∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ Z = A + s • (P - A)) ∧ Z ≠ P ∧
      dist Z OC = dist P OC)
    -- Nondegeneracy of the configuration.
    (hYZ : Y ≠ Z) :
    dist Y X / dist X Z = dist B P / dist P C := by
  -- Unpack the parametrizations.
  obtain ⟨t, ht0, ht1, hPt⟩ := hP
  obtain ⟨w, hw0, hw1, hQw⟩ := hQ
  obtain ⟨v, hv0, hv1, hRv⟩ := hR
  obtain ⟨⟨sx, -, -, hXs⟩, hXA, hXc⟩ := hX
  obtain ⟨⟨sy, -, -, hYs⟩, hYP, hYc⟩ := hY
  obtain ⟨⟨sz, -, -, hZs⟩, hZP, hZc⟩ := hZ
  obtain ⟨hOA1, hOA2⟩ := hOA
  obtain ⟨hOB1, hOB2⟩ := hOB
  obtain ⟨hOC1, hOC2⟩ := hOC
  -- Nondegeneracy: B ≠ C and A ≠ P follow from non-collinearity of A, B, C.
  have hBC : B ≠ C := by
    intro h
    apply hABC
    rw [h]
    simpa using collinear_pair ℝ A C
  have hAP : A ≠ P := by
    intro h
    apply hABC
    rw [collinear_iff_exists_forall_eq_smul_vadd]
    refine ⟨B, C - B, fun p hp => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨t, by rw [h, hPt, vadd_eq_add, add_comm B]⟩
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp [vadd_eq_add]⟩
  -- Incidence conditions as equalities of squared distances.
  have cX : ‖X - OA‖ ^ 2 = ‖A - OA‖ ^ 2 := by
    rw [← dist_eq_norm, ← dist_eq_norm, hXc]
  have cQ_A : ‖Q - OA‖ ^ 2 = ‖A - OA‖ ^ 2 := by
    rw [← dist_eq_norm, ← dist_eq_norm, dist_comm Q OA, dist_comm A OA, hOA1]
  have cR_A : ‖R - OA‖ ^ 2 = ‖A - OA‖ ^ 2 := by
    rw [← dist_eq_norm, ← dist_eq_norm, dist_comm R OA, dist_comm A OA, ← hOA2, hOA1]
  have cR_B : ‖R - OB‖ ^ 2 = ‖B - OB‖ ^ 2 := by
    rw [← dist_eq_norm, ← dist_eq_norm, dist_comm R OB, dist_comm B OB, ← hOB1]
  have cP_B : ‖P - OB‖ ^ 2 = ‖B - OB‖ ^ 2 := by
    rw [← dist_eq_norm, ← dist_eq_norm, dist_comm P OB, dist_comm B OB, ← hOB2, hOB1]
  have cY_B : ‖Y - OB‖ ^ 2 = ‖B - OB‖ ^ 2 := by
    rw [← dist_eq_norm, ← dist_eq_norm, hYc, dist_comm P OB, dist_comm B OB,
      ← hOB2, hOB1]
  have cQ_C : ‖Q - OC‖ ^ 2 = ‖C - OC‖ ^ 2 := by
    rw [← dist_eq_norm, ← dist_eq_norm, dist_comm Q OC, dist_comm C OC, ← hOC2, hOC1]
  have cP_C : ‖P - OC‖ ^ 2 = ‖C - OC‖ ^ 2 := by
    rw [← dist_eq_norm, ← dist_eq_norm, dist_comm P OC, dist_comm C OC, ← hOC1]
  have cZ_C : ‖Z - OC‖ ^ 2 = ‖C - OC‖ ^ 2 := by
    rw [← dist_eq_norm, ← dist_eq_norm, hZc, dist_comm P OC, dist_comm C OC, ← hOC1]
  -- The parameters are nonzero / not one.
  have hsx0 : sx ≠ 0 := fun h => hXA (by rw [hXs, h, zero_smul, add_zero])
  have hsy1 : sy ≠ 1 := fun h => hYP (by simp [hYs, h])
  have hsz1 : sz ≠ 1 := fun h => hZP (by simp [hZs, h])
  have hsysz : sy ≠ sz := fun h => hYZ (by rw [hYs, hZs, h])
  have hv0n : v ≠ 0 := ne_of_gt hv0
  have hv1n : v ≠ 1 := ne_of_lt hv1
  have hw0n : w ≠ 0 := ne_of_gt hw0
  have hw1n : w ≠ 1 := ne_of_lt hw1
  -- ω_A: quadratic equations for the intersections of lines AP, AB, AC with the circle.
  have hsx : 2 * ⟪A - OA, P - A⟫ + sx * ‖P - A‖ ^ 2 = 0 := by
    have h := cX
    rw [hXs, norm_sq_add_smul_sub] at h
    have h2 : sx * (2 * ⟪A - OA, P - A⟫ + sx * ‖P - A‖ ^ 2) = 0 := by
      linear_combination h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 hsx0
    · exact h3
  have hvr : 2 * ⟪A - OA, B - A⟫ + v * ‖B - A‖ ^ 2 = 0 := by
    have h := cR_A
    rw [hRv, norm_sq_add_smul_sub] at h
    have h2 : v * (2 * ⟪A - OA, B - A⟫ + v * ‖B - A‖ ^ 2) = 0 := by
      linear_combination h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 hv0n
    · exact h3
  have hwq : 2 * ⟪A - OA, C - A⟫ + w * ‖C - A‖ ^ 2 = 0 := by
    have h := cQ_A
    rw [hQw, norm_sq_add_smul_sub] at h
    have h2 : w * (2 * ⟪A - OA, C - A⟫ + w * ‖C - A‖ ^ 2) = 0 := by
      linear_combination h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 hw0n
    · exact h3
  -- Powers of B, C, P with respect to ω_A.
  have hpowB : ‖B - OA‖ ^ 2 - ‖A - OA‖ ^ 2 = (1 - v) * ‖B - A‖ ^ 2 := by
    have h1 : B = A + (1 : ℝ) • (B - A) := by simp
    have h2 := norm_sq_add_smul_sub A OA (B - A) 1
    rw [← h1] at h2
    linear_combination h2 + hvr
  have hpowC : ‖C - OA‖ ^ 2 - ‖A - OA‖ ^ 2 = (1 - w) * ‖C - A‖ ^ 2 := by
    have h1 : C = A + (1 : ℝ) • (C - A) := by simp
    have h2 := norm_sq_add_smul_sub A OA (C - A) 1
    rw [← h1] at h2
    linear_combination h2 + hwq
  have hpowP1 : ‖P - OA‖ ^ 2 - ‖A - OA‖ ^ 2 = (1 - sx) * ‖P - A‖ ^ 2 := by
    have h1 : P = A + (1 : ℝ) • (P - A) := by simp
    have h2 := norm_sq_add_smul_sub A OA (P - A) 1
    rw [← h1] at h2
    linear_combination h2 + hsx
  have hPOA : P - OA = (1 - t) • (B - OA) + t • (C - OA) := by
    rw [hPt]; module
  have hpowP2 : ‖P - OA‖ ^ 2
      = (1 - t) * ‖B - OA‖ ^ 2 + t * ‖C - OA‖ ^ 2 - t * (1 - t) * ‖B - C‖ ^ 2 := by
    rw [hPOA, norm_sq_affine_comb, show (B - OA) - (C - OA) = B - C by abel]
  -- The power of P with respect to ω_A, computed two ways.
  have hkeyX : (1 - sx) * ‖P - A‖ ^ 2
      = (1 - t) * ((1 - v) * ‖B - A‖ ^ 2) + t * ((1 - w) * ‖C - A‖ ^ 2)
        - t * (1 - t) * ‖B - C‖ ^ 2 := by
    linear_combination hpowP2 - hpowP1 + (1 - t) * hpowB + t * hpowC
  -- Stewart's identity for the cevian AP of triangle ABC.
  have hd : P - A = (1 - t) • (B - A) + t • (C - A) := by
    rw [hPt]; module
  have hD : ‖P - A‖ ^ 2
      = (1 - t) * ‖B - A‖ ^ 2 + t * ‖C - A‖ ^ 2 - t * (1 - t) * ‖B - C‖ ^ 2 := by
    rw [hd, norm_sq_affine_comb, show (B - A) - (C - A) = B - C by abel]
  -- ω_B: the power of A, and the parameter of Y.
  have hr1 : ‖A - OB‖ ^ 2 + v * (2 * ⟪A - OB, B - A⟫) + v ^ 2 * ‖B - A‖ ^ 2
      = ‖B - OB‖ ^ 2 := by
    have h := cR_B
    rw [hRv, norm_sq_add_smul_sub] at h
    exact h
  have hb1 : ‖B - OB‖ ^ 2
      = ‖A - OB‖ ^ 2 + (2 * ⟪A - OB, B - A⟫) + ‖B - A‖ ^ 2 := by
    have h1 : B = A + (1 : ℝ) • (B - A) := by simp
    have h2 := norm_sq_add_smul_sub A OB (B - A) 1
    rw [← h1] at h2
    linear_combination h2
  have hpowBA : ‖A - OB‖ ^ 2 - ‖B - OB‖ ^ 2 = v * ‖B - A‖ ^ 2 := by
    have h3 : (1 - v) * ((‖A - OB‖ ^ 2 - ‖B - OB‖ ^ 2) - v * ‖B - A‖ ^ 2) = 0 := by
      linear_combination hr1 + v * hb1
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd (eq_of_sub_eq_zero h4).symm hv1n
    · exact eq_of_sub_eq_zero h4
  have hp1 : ‖A - OB‖ ^ 2 + (2 * ⟪A - OB, P - A⟫) + ‖P - A‖ ^ 2
      = ‖B - OB‖ ^ 2 := by
    have h1 : P = A + (1 : ℝ) • (P - A) := by simp
    have h := cP_B
    rw [h1, norm_sq_add_smul_sub] at h
    linear_combination h
  have hy1 : ‖A - OB‖ ^ 2 + sy * (2 * ⟪A - OB, P - A⟫) + sy ^ 2 * ‖P - A‖ ^ 2
      = ‖B - OB‖ ^ 2 := by
    have h := cY_B
    rw [hYs, norm_sq_add_smul_sub] at h
    exact h
  have hsy : sy * ‖P - A‖ ^ 2 = v * ‖B - A‖ ^ 2 := by
    have h3 : (1 - sy) * (sy * ‖P - A‖ ^ 2 - (‖A - OB‖ ^ 2 - ‖B - OB‖ ^ 2)) = 0 := by
      linear_combination sy * hp1 - hy1
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd (sub_eq_zero.mp h4).symm hsy1
    · exact (sub_eq_zero.mp h4).trans hpowBA
  -- ω_C: the power of A, and the parameter of Z.
  have hq1 : ‖A - OC‖ ^ 2 + w * (2 * ⟪A - OC, C - A⟫) + w ^ 2 * ‖C - A‖ ^ 2
      = ‖C - OC‖ ^ 2 := by
    have h := cQ_C
    rw [hQw, norm_sq_add_smul_sub] at h
    exact h
  have hc1 : ‖C - OC‖ ^ 2
      = ‖A - OC‖ ^ 2 + (2 * ⟪A - OC, C - A⟫) + ‖C - A‖ ^ 2 := by
    have h1 : C = A + (1 : ℝ) • (C - A) := by simp
    have h2 := norm_sq_add_smul_sub A OC (C - A) 1
    rw [← h1] at h2
    linear_combination h2
  have hpowCA : ‖A - OC‖ ^ 2 - ‖C - OC‖ ^ 2 = w * ‖C - A‖ ^ 2 := by
    have h3 : (1 - w) * ((‖A - OC‖ ^ 2 - ‖C - OC‖ ^ 2) - w * ‖C - A‖ ^ 2) = 0 := by
      linear_combination hq1 + w * hc1
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd (eq_of_sub_eq_zero h4).symm hw1n
    · exact eq_of_sub_eq_zero h4
  have hp2 : ‖A - OC‖ ^ 2 + (2 * ⟪A - OC, P - A⟫) + ‖P - A‖ ^ 2
      = ‖C - OC‖ ^ 2 := by
    have h1 : P = A + (1 : ℝ) • (P - A) := by simp
    have h := cP_C
    rw [h1, norm_sq_add_smul_sub] at h
    linear_combination h
  have hz1 : ‖A - OC‖ ^ 2 + sz * (2 * ⟪A - OC, P - A⟫) + sz ^ 2 * ‖P - A‖ ^ 2
      = ‖C - OC‖ ^ 2 := by
    have h := cZ_C
    rw [hZs, norm_sq_add_smul_sub] at h
    exact h
  have hsz : sz * ‖P - A‖ ^ 2 = w * ‖C - A‖ ^ 2 := by
    have h3 : (1 - sz) * (sz * ‖P - A‖ ^ 2 - (‖A - OC‖ ^ 2 - ‖C - OC‖ ^ 2)) = 0 := by
      linear_combination sz * hp2 - hz1
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd (sub_eq_zero.mp h4).symm hsz1
    · exact (sub_eq_zero.mp h4).trans hpowCA
  -- The key identity: X divides YZ in the ratio BP : PC.
  have hTD : sx * ‖P - A‖ ^ 2
      = (1 - t) * sy * ‖P - A‖ ^ 2 + t * sz * ‖P - A‖ ^ 2 := by
    linear_combination hD - hkeyX - (1 - t) * hsy - t * hsz
  have hDne : ‖P - A‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm hAP)))
  have hmain : sx = (1 - t) * sy + t * sz :=
    mul_right_cancel₀ hDne (by linear_combination hTD)
  -- Distances along the line AP.
  have hYXv : Y - X = (sy - sx) • (P - A) := by rw [hYs, hXs]; module
  have hXZv : X - Z = (sx - sz) • (P - A) := by rw [hXs, hZs]; module
  have hsyx : sy - sx = t * (sy - sz) := by linear_combination -hmain
  have hsxz : sx - sz = (1 - t) * (sy - sz) := by linear_combination hmain
  have hYX : dist Y X = t * |sy - sz| * ‖P - A‖ := by
    rw [dist_eq_norm, hYXv, norm_smul, Real.norm_eq_abs, hsyx, abs_mul,
      abs_of_pos ht0]
  have hXZ : dist X Z = (1 - t) * |sy - sz| * ‖P - A‖ := by
    rw [dist_eq_norm, hXZv, norm_smul, Real.norm_eq_abs, hsxz, abs_mul,
      abs_of_pos (sub_pos.mpr ht1)]
  -- Distances along the side BC.
  have hBPv : B - P = (-t) • (C - B) := by rw [hPt]; module
  have hPCv : P - C = (1 - t) • (B - C) := by rw [hPt]; module
  have hBP : dist B P = t * ‖C - B‖ := by
    rw [dist_eq_norm, hBPv, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos ht0]
  have hPC : dist P C = (1 - t) * ‖C - B‖ := by
    rw [dist_eq_norm, hPCv, norm_smul, Real.norm_eq_abs,
      abs_of_pos (sub_pos.mpr ht1), norm_sub_rev]
  -- Conclude.
  have hΔ : |sy - sz| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hsysz)
  have hPA : ‖P - A‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm hAP))
  have hCB : ‖C - B‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm hBC))
  have h1t : 1 - t ≠ 0 := ne_of_gt (sub_pos.mpr ht1)
  rw [hYX, hXZ, hBP, hPC, div_eq_div_iff (mul_ne_zero (mul_ne_zero h1t hΔ) hPA)
    (mul_ne_zero h1t hCB)]
  ring

end Usa2013P1
