/-
Copyright (c) 2023 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongyu Ouyang
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 1996, Problem 1

Prove that the average of the numbers n⬝sin(n π / 180)
for n ∈ {2,4,6,…,180} is 1/tan(π/180).
-/

namespace Usa1996P1
open BigOperators

problem usa1996_p1 :
    (1 / (90:ℝ)) * ∑ n in Finset.range 90, (2 * (n+1)) * Real.sin ((2 * (n+1)) * Real.pi / 180)
    = 1 / Real.tan (Real.pi / 180) := by
  have sin1 : Real.sin (Real.pi / 180) ≠ 0 := by
    have h1 : -Real.pi < Real.pi / 180 := by linarith [Real.pi_pos]
    apply (Real.sin_eq_zero_iff_of_lt_of_lt h1 (by linarith)).not.mpr
    positivity
  have cos_add : ∀ (x y : ℝ), x + y = Real.pi → Real.cos x + Real.cos y = 0 := by
    intro x y h; rw [(by linarith only [h] : y = Real.pi - x)]; rw [Real.cos_pi_sub, add_right_neg]
  apply mul_left_cancel₀ sin1
  rw [mul_comm, mul_assoc, Finset.sum_mul]
  rw [Real.tan_eq_sin_div_cos]
  convert_to 1 / (90:ℝ) * ∑ n in Finset.range 90, (↑n + 1) *
      (Real.cos ((2 * (↑n + 1) - 1) * Real.pi / 180) -
       Real.cos ((2 * (↑n + 1) + 1) * Real.pi / 180)) = Real.cos (Real.pi / 180)
  · congr! 2 with n _
    rw [Real.cos_sub_cos]
    rw [show (((2 * (↑n + 1) - 1) * Real.pi / 180 + (2 * (↑n + 1) + 1) * Real.pi / 180) / 2) =
             (2 * (n + 1) * Real.pi / 180) by ring]
    rw [show (((2 * (↑n + 1) - 1) * Real.pi / 180 - (2 * (↑n + 1) + 1) * Real.pi / 180) / 2) =
             (-(Real.pi / 180)) by ring]
    rw [Real.sin_neg]
    linarith only
  · field_simp [mul_comm]
  · field_simp
    convert_to (∑ n in Finset.range 45, (Real.cos (((89 - n) * 2 + 1) * Real.pi / 180) +
                                         Real.cos ((n * 2 + 1) * Real.pi / 180)))
        - 90 * Real.cos (181 * Real.pi / 180) = _
    · have h1 : ∀ n ∈ Finset.range 90,
        (↑n + 1) * (Real.cos ((2 * (↑n + 1) - 1) * Real.pi / 180)
             - Real.cos ((2 * (↑n + 1) + 1) * Real.pi / 180)) =
        ((↑n + 1) * (Real.cos ((2 * (↑n + 1) - 1) * Real.pi / 180))
                      - (↑n + 1) * Real.cos ((2 * (↑n + 1) + 1) * Real.pi / 180)) := by
        intro n _
        ring_nf
      rw [Finset.sum_congr rfl h1]; clear h1
      rw [Finset.sum_sub_distrib]
      nth_rewrite 2 [Finset.sum_range_succ]
      have h1 : ∑ x in Finset.range 89, (↑x + 1) * Real.cos ((2 * (↑x + 1) + 1) * Real.pi / 180) =
             ∑ x in Finset.range 90, (↑x) * Real.cos ((2 * (↑x + 1) - 1) * Real.pi / 180) := by
        nth_rewrite 2 [Finset.sum_range_succ']
        simp only [Nat.cast_add, Nat.cast_one, CharP.cast_eq_zero,
                   zero_add, mul_one, zero_mul, add_zero]
        apply Finset.sum_congr rfl
        intro x _
        have h3 : 2 * ((x:ℝ) + 1) + 1 = 2 * (↑x + 1 + 1) - 1 := by ring
        rw [h3]
      rw [h1]; clear h1
      rw [sub_add_eq_sub_sub, ←Finset.sum_sub_distrib]
      have h4 : ∀ x ∈ Finset.range 90,
         ((↑x + 1) * Real.cos ((2 * (↑x + 1) - 1) * Real.pi / 180) -
           ↑x * Real.cos ((2 * (↑x + 1) - 1) * Real.pi / 180)) =
          Real.cos ((2 * (↑x + 1) - 1) * Real.pi / 180) := by
        intro x _; ring
      rw [Finset.sum_congr rfl h4]; clear h4
      have h5 : ∑ x in Finset.range 90, Real.cos ((2 * (↑x + 1) - 1) * Real.pi / 180)
          = ∑ n in Finset.range 45, (Real.cos (((89 - ↑n) * 2 + 1) * Real.pi / 180) +
                                     Real.cos ((↑n * 2 + 1) * Real.pi / 180)) := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.range_eq_Ico]
        have h6 : 0 ≤ 45 := by norm_num
        have h7 : 45 ≤ 90 := by norm_num
        rw [←Finset.sum_Ico_consecutive
             (f := (fun x ↦ Real.cos ((2 * (↑x + 1) - 1) * Real.pi / 180))) h6 h7]
        have h8 : ∀ i ∈ Finset.Ico (0:ℕ) 45,
             Real.cos ((2 * (↑i + 1) - 1) * Real.pi / 180) =
                        Real.cos ((↑i * 2 + 1) * Real.pi / 180) := by
          intro i _
          have h10 : 2 * ((i:ℝ) + 1) - 1 = ↑i * 2 + 1 := by ring
          rw [h10]
        rw [Finset.sum_congr rfl h8]; clear h8
        have h9 :
            ∑ i in Finset.Ico (45:ℕ) 90, Real.cos ((2 * (↑i + 1) - 1) * Real.pi / 180) =
            ∑ x in Finset.Ico (0:ℕ) 45, Real.cos (((89 - ↑x) * 2 + 1) * Real.pi / 180) := by
          have h15 : 45 = 89 + 1 - 45 := by norm_num
          have h16 : 90 = 89 + 1 - 0 := by norm_num
          nth_rewrite 1 [h15, h16]
          rw [←Finset.sum_Ico_reflect _ 0 h7]
          apply Finset.sum_congr rfl
          intro x hx
          apply congrArg
          have h18 : (((89 - x) : ℕ) : ℝ) = 89 - x := by
            apply Nat.cast_sub
            rw [Finset.mem_Ico] at hx
            omega
          rw [h18]
          ring
        rw [h9]; clear h9
        exact add_comm _ _
      rw [←h5]
      norm_num1
      ring
    · rw [mul_comm]
      rw [Finset.sum_eq_zero]
      simp only [zero_sub]
      rw [←neg_mul, ←Real.cos_sub_pi]
      congr; ring
      intro n _
      rw [cos_add]
      ring
