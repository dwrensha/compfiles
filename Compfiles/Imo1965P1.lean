/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1965, Problem 1

Determine all values x in the interval 0 ≤ x ≤ 2π which
satisfy the inequality

   2 cos x ≤ |√(1 + sin 2x) − √(1 − sin 2x)| ≤ √2.
-/

namespace Imo1965P1

open Real Set

determine the_answer : Set ℝ := Icc (π/4) (7*π/4)

problem imo1965_p1 :
    {x ∈ Icc 0 (2*π) |
       |√(1 + sin (2*x)) - √(1 - sin (2*x))| ∈ Icc (2 * cos x) (√2)}
     = the_answer := by
  -- We follow https://artofproblemsolving.com/wiki/index.php/1965_IMO_Problems/Problem_1.
  have h0 : ∀ x, (√(1 + sin (2*x)) - √(1 - sin (2*x)))^2 = 2 - 2*|cos (2*x)| := by
    intro x
    rw [←sqrt_sq_eq_abs (cos (2 * x)), cos_sq', sub_sq, sq_sqrt, sq_sqrt, mul_assoc,
      ←sqrt_mul]; ring_nf
    repeat { linarith [sin_le_one (2 * x), neg_one_le_sin (2 * x)] }
  have : ∀ x, |√(1 + sin (2*x)) - √(1 - sin (2*x))| ≤ √2 := by
    intro x
    apply nonneg_le_nonneg_of_sq_le_sq (by norm_num)
    simp [←pow_two, h0]
  simp only [Set.mem_Icc]
  simp_rw [this, and_true]
  symm; ext x; constructor; dsimp
  . rw [the_answer]; rintro ⟨h1, h2⟩
    constructor
    . constructor <;> linarith
    have : x ∈ Ico (π/4) (π / 2) ∪ Icc (π/2) (3*π/2) ∪ Ioc (3*π/2) (7*π/4) := by
      simp only [the_answer, mem_Icc, mem_union, mem_Ico, mem_Ioc]
      rcases lt_or_ge x (π/2) with h3 | h3 <;>
        rcases le_or_gt x (3*π/2) with h4 | h4 <;> simp [*]
    rcases this with (⟨_, h4⟩ | ⟨h3, h4⟩) | ⟨h3, _⟩
    . have cos2x_nonpos : cos (2*x) ≤ 0 := by
        apply cos_nonpos_of_pi_div_two_le_of_le <;> linarith
      have cosx_nonneg : 0 ≤ cos x := by
        apply cos_nonneg_of_neg_pi_div_two_le_of_le <;> linarith
      have cosx2_nonneg : 0 ≤ 2 * cos x := by linarith
      rw [←abs_of_nonneg cosx2_nonneg, ←sq_le_sq, h0, abs_of_nonpos cos2x_nonpos, cos_two_mul]
      linarith
    . trans 0; swap; simp
      suffices cos x ≤ 0 by linarith
      apply cos_nonpos_of_pi_div_two_le_of_le h3
      linarith
    . have cos2x_nonpos : cos (2*x) ≤ 0 := by
        rw [←cos_neg, ←cos_add_two_pi, ←cos_add_two_pi]
        apply cos_nonpos_of_pi_div_two_le_of_le <;> linarith
      have cosx_nonneg : 0 ≤ cos x := by
        rw [←cos_neg, ←cos_add_two_pi]
        apply cos_nonneg_of_neg_pi_div_two_le_of_le <;> linarith
      have cosx2_nonneg : 0 ≤ 2 * cos x := by linarith
      rw [←abs_of_nonneg cosx2_nonneg, ←sq_le_sq, h0, abs_of_nonpos cos2x_nonpos, cos_two_mul]
      linarith
  rintro ⟨⟨h1, h2⟩, h3⟩
  by_contra h4
  rw [the_answer, mem_Icc, not_and_or] at h4; push_neg at h4
  have cos2x_nonneg : 0 ≤ cos (2*x) := by
    rcases h4 with h4 | h4
    . apply cos_nonneg_of_neg_pi_div_two_le_of_le <;> linarith
    . rw [←cos_sub_two_pi, ←cos_sub_two_pi]
      apply cos_nonneg_of_neg_pi_div_two_le_of_le <;> linarith
  have cosx_nonneg : 0 ≤ cos x := by
    rcases h4 with h4 | h4
    . apply cos_nonneg_of_neg_pi_div_two_le_of_le <;> linarith
    . rw [←cos_neg, ←cos_add_two_pi]
      apply cos_nonneg_of_neg_pi_div_two_le_of_le <;> linarith
  have cosx2_nonneg : 0 ≤ 2 * cos x := by linarith
  rw [←abs_of_nonneg cosx2_nonneg, ←sq_le_sq, h0, abs_of_nonneg cos2x_nonneg, cos_two_mul] at h3
  ring_nf at h3
  suffices (cos (π/4))^2 < (cos x)^2 by
    rw [cos_pi_div_four, div_pow] at this; norm_num at this
    linarith
  rw [sq_lt_sq, abs_of_nonneg cosx_nonneg, abs_of_nonneg]
  swap; simp [cos_pi_div_four]; positivity
  rcases h4 with h5 | h5
  . apply cos_lt_cos_of_nonneg_of_le_pi_div_two h1 (by linarith) h5
  rw [←cos_neg x, ←cos_add_two_pi (-x)]
  apply cos_lt_cos_of_nonneg_of_le_pi_div_two <;> linarith
