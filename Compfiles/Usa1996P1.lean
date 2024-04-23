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

set_option maxHeartbeats 800000
problem usa1996_p1 :
    (1 / (90:ℝ)) * ∑ n in Finset.range 90, (2 * (n+1)) * Real.sin ((2 * (n+1)) * Real.pi / 180)
    = 1 / Real.tan (Real.pi / 180) := by
  have sin1 : Real.sin (Real.pi / 180) ≠ 0 := by
    apply ne_of_gt; apply Real.sin_pos_of_pos_of_lt_pi; positivity; trans 3
    trans 3.15 / 180
    apply div_lt_div_of_pos_right Real.pi_lt_315
    norm_num
    norm_num
    exact Real.pi_gt_three
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
             (2 * (n + 1) * Real.pi / 180) from by ring]
    rw [show (((2 * (↑n + 1) - 1) * Real.pi / 180 - (2 * (↑n + 1) + 1) * Real.pi / 180) / 2) =
             (-(Real.pi / 180)) from by ring]
    rw [Real.sin_neg]
    linarith only
  · field_simp [mul_comm]
  · field_simp
    convert_to (∑ n in Finset.range 45, (Real.cos (((89 - n) * 2 + 1) * Real.pi / 180) +
                                         Real.cos ((n * 2 + 1) * Real.pi / 180)))
        - 90 * Real.cos (181 * Real.pi / 180) = _
    · unfold Finset.range Multiset.range List.range
      dsimp [List.range.loop]
      dsimp [List.range.loop, Multiset.sum]
      simp only [one_div, Finset.sum_mk, Multiset.map_coe, Multiset.sum_coe]
      norm_num
      ring_nf
    · rw [mul_comm]
      rw [Finset.sum_eq_zero]
      simp only [zero_sub]
      rw [←neg_mul, ←Real.cos_sub_pi]
      congr; ring
      intro n _
      rw [cos_add]
      ring
