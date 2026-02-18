/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongyu Ouyang
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

import ProblemExtraction

set_option backward.isDefEq.respectTransparency false

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 1992, Problem 2

Prove that

1 / cos 0° / cos 1° + 1 / cos 1° / cos 2° + ... + 1 / cos 88° / cos 99° = cos 1° / sin² 1°
-/

namespace Usa1992P2

open Real

problem usa1992_p2 :
  ∑ i ∈ Finset.range 89, 1 / cos (i * π / 180) / cos ((i + 1) * π / 180) =
  cos (π / 180) / sin (π / 180) ^ 2 := by

  have cosi : ∀ {i : ℕ}, i < 90 → (↑i * π / 180).cos ≠ 0 := by
    intro i hi
    rw [Real.cos_ne_zero_iff]
    intro k
    cancel_denoms
    norm_cast
    lia

  have ha : sin (π / 180) ≠ 0 := by
    rw [← Real.cos_pi_div_two_sub]
    rw [show (π / 2 - π / 180) = (89 * π / 180) by ring]
    exact cosi (show 89 < 90 by norm_num)

  norm_cast
  rw [sq, div_mul_eq_div_div, ← (mul_right_inj' ha), mul_div_assoc',
      mul_div_right_comm, div_self ha, one_mul, Finset.mul_sum]
  conv => lhs; arg 2; intro i; rw [div_div, mul_div_assoc', mul_one]
  suffices new_goal :
    ∑ i ∈ Finset.range 89, (π / 180).sin / ((↑i * π / 180).cos * (↑(i + 1) * π / 180).cos) =
    ∑ i ∈ Finset.range 89, (((↑(i + 1)) * π / 180).sin / ((↑(i + 1)) * π / 180).cos -
                             (↑i * π / 180).sin / (↑i * π / 180).cos)
  · rw [new_goal]
    rw [Finset.sum_range_sub (fun i ↦ (↑i * π / 180).sin / (↑i * π / 180).cos) 89]
    simp only [Nat.cast_ofNat, CharP.cast_eq_zero, zero_mul, zero_div,
               sin_zero, cos_zero, div_one, sub_zero]
    rw [← Real.cos_pi_div_two_sub, ← Real.cos_pi_div_two_sub]
    rw [show (π / 2 - 89 * π / 180) = π / 180 by ring]
    rw [show (π / 2 - π / 180) = 89 * π / 180 by ring]

  apply Finset.sum_congr rfl
  simp only [Finset.mem_range]
  intro i hi
  rw [show (π / 180) = ((i + 1) : ℝ) * π / 180 - (i : ℝ) * π / 180 by ring]
  rw [Real.sin_sub, sub_div]
  norm_cast
  rw [div_mul_eq_div_div]
  rw [mul_div_cancel_right₀ _ (cosi (show i < 90 by lia))]
  rw [mul_comm (cos (↑(i + 1) * π / 180)) (sin (↑i * π / 180))]
  rw [mul_comm (cos (↑i * π / 180)) (cos (↑(i + 1) * π / 180))]
  rw [div_mul_eq_div_div]
  rw [mul_div_cancel_right₀ _ (cosi (show (i+1) < 90 by lia))]

end Usa1992P2
