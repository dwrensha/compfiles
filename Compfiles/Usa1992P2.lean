/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongyu Ouyang
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Digits
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 1992, Problem 2

Prove that 

1 / cos 0° cos 1° + 1 / cos 1° cos 2° + ... + 1 / cos 88° cos 99° = cos 1° / sin² 1°
-/

namespace Usa1992P2

open Real

problem usa1992_p1 :
  (∑ i ∈ Finset.range 89, 1 / cos (i * π / 180) / cos ((i + 1) * π / 180)) = cos (π / 180) / sin (π / 180) / sin (π / 180) := by

  have π_ne_zero : π ≠ 0 := ne_of_gt Real.pi_pos
  have cosi : ∀ {i : ℕ}, i < 90 → (↑i * π / 180).cos ≠ 0 := by 
    intro i hi
    rw [Real.cos_ne_zero_iff]
    intros k con
    have con2 : π * (↑i / 180) = π * ((2 * ↑k + 1) / 2) := by linear_combination con
    clear con
    rw [mul_eq_mul_left_iff] at con2
    revert con2
    simp only [imp_false, not_or]
    constructor
    · intro con
      have con2 : 180 * (i : ℝ) / 180 = (2 * (k : ℝ) + 1) * (180 / 2) := by rw [mul_div_assoc', (mul_comm _ 180), ← mul_div, ← mul_div, con]
      clear con
      norm_num at con2
      revert con2
      by_cases hk : 0 ≤ k
      apply ne_of_lt; norm_cast; linarith
      apply ne_of_gt; norm_cast; linarith
    · exact π_ne_zero

  have ha : sin (π / 180) ≠ 0 := by 
    rw [← Real.cos_pi_div_two_sub]
    rw [show (π / 2 - π / 180) = (89 * π / 180) by linarith]
    exact cosi (show 89 < 90 by linarith)

  field_simp
  rw [←mul_assoc, Finset.sum_mul]
  conv => {
    lhs
    arg 1
    arg 2
    intro i
    rw [show 1 / ((↑i * π / 180).cos * ((↑i + 1) * π / 180).cos) * (π / 180).sin = ((i + 1) * π / 180 - i * π / 180).sin / ((↑i * π / 180).cos * ((↑i + 1) * π / 180).cos) by ring_nf]
    rw [Real.sin_sub, sub_div]
    rw [show  ((↑i + 1) * π / 180).sin * (↑i * π / 180).cos / ((↑i * π / 180).cos * ((↑i + 1) * π / 180).cos) -
    ((↑i + 1) * π / 180).cos * (↑i * π / 180).sin / ((↑i * π / 180).cos * ((↑i + 1) * π / 180).cos) =
          (↑i * π / 180).cos / (↑i * π / 180).cos * ((↑i + 1) * π / 180).sin / ((↑i + 1) * π / 180).cos - ((↑i + 1) * π / 180).cos / ((↑i + 1) * π / 180).cos * (↑i * π / 180).sin / (↑i * π / 180).cos by linear_combination]
  }
  suffices new_goal : (∑ i ∈ Finset.range 89,
        ((↑i * π / 180).cos / (↑i * π / 180).cos * ((↑i + 1) * π / 180).sin / ((↑i + 1) * π / 180).cos -
          ((↑i + 1) * π / 180).cos / ((↑i + 1) * π / 180).cos * (↑i * π / 180).sin / (↑i * π / 180).cos)) = (∑ i ∈ Finset.range 89,
        (((↑(i + 1)) * π / 180).sin / ((↑(i + 1)) * π / 180).cos -
          (↑i * π / 180).sin / (↑i * π / 180).cos))
  rw [new_goal]
  rw [Finset.sum_range_sub (fun i ↦ (↑i * π / 180).sin / (↑i * π / 180).cos) 89]
  simp
  rw [← Real.cos_pi_div_two_sub, ← Real.cos_pi_div_two_sub]
  rw [show (π / 2 - 89 * π / 180).cos / (89 * π / 180).cos * (π / 2 - π / 180).cos =
           (π / 180).cos / (89 * π / 180).cos * (89 * π / 180).cos by congr; linarith; linarith]
  have ha : (89 * π / 180).cos ≠ 0 := cosi (show 89 < 90 by linarith)
  field_simp

  apply Finset.sum_congr rfl
  simp only [Finset.mem_range]
  intro i hi
  have cosi1 := cosi (show i < 90 by linarith)
  have cosi2 := cosi (show (i+1) < 90 by linarith)
  norm_cast
  rw [(div_self cosi1)]
  rw [(div_self cosi2)]
  simp only [Nat.cast_add, Nat.cast_one, one_mul]
 
