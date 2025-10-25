/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongyu Ouyang
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Bounds

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1963, Problem 5

Prove that cos(π/7) - cos(2π/7) + cos(3π/7) = 1/2.
-/

namespace Imo1963P5

open scoped Real

problem imo1963_p5 :
    Real.cos (π/7) - Real.cos (2*π/7) + Real.cos (3*π/7) = 1/2 := by
  rw [show (2*π/7) = π - (5*π/7) by linarith]
  rw [Real.cos_pi_sub]
  simp only [sub_neg_eq_add]
  have h : 2 * Real.sin (π / 7) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
    apply ne_of_gt
    apply Real.sin_pos_of_pos_of_lt_pi
    · simp only [Nat.ofNat_pos, div_pos_iff_of_pos_right, Real.pi_pos]
    trans 1
    · rw [div_lt_one (by linarith only)]
      linarith only [Real.pi_le_four]
    · linarith only [Real.pi_gt_three]
  apply (mul_right_inj' h).mp
  rw [left_distrib, left_distrib]
  have prod_sum : ∀ (x y : ℝ),
      2 * Real.sin x * Real.cos y = Real.sin (x + y) - Real.sin (y - x) := by
    intro x y
    rw [Real.sin_add, Real.sin_sub]
    linarith only
  rw [prod_sum, prod_sum, prod_sum]
  rw [show (π / 7 + π / 7)     = 2 * π / 7 by linarith only]
  rw [show (π / 7 - π / 7)     = 0         by linarith only]
  rw [show (π / 7 + 5 * π / 7) = 6 * π / 7 by linarith only]
  rw [show (5 * π / 7 - π / 7) = 4 * π / 7 by linarith only]
  rw [show (π / 7 + 3 * π / 7) = 4 * π / 7 by linarith only]
  rw [show (3 * π / 7 - π / 7) = 2 * π / 7 by linarith only]
  rw [Real.sin_zero]
  ring_nf
  rw [← Real.sin_pi_sub]
  rw [show (π - π * (6 / 7)) = π / 7 by linarith]
  congr
  linarith
end Imo1963P5
