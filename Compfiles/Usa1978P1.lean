/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongyu Ouyang
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra, .Inequality] }

/-!
# USA Mathematical Olympiad 1978, Problem 1

Given that a,b,c,d,e are real numbers such that

  a  + b  + c  + d  + e  = 8
  a² + b² + c² + d² + e² = 16,

determine the maximum value of e.
-/

namespace Usa1978P1

noncomputable determine max_e : ℝ := (16 : ℝ) / 5

abbrev IsGood (a b c d e : ℝ) : Prop :=
  a + b + c + d + e = 8 ∧ a^2 + b^2 + c^2 + d^2 + e^2 = 16

problem usa1978_p1 :
    IsGreatest { e : ℝ | ∃ a b c d : ℝ, IsGood a b c d e } max_e := by
  -- solution 3 from
  -- https://artofproblemsolving.com/wiki/index.php/1978_USAMO_Problems/Problem_1
  unfold IsGreatest IsGood max_e upperBounds
  constructor
  · simp only [Set.mem_setOf_eq]
    use (6 / 5)
    use (6 / 5)
    use (6 / 5)
    use (6 / 5)
    constructor <;> norm_num
  · simp only [Set.mem_setOf_eq]
    intro e
    contrapose!
    intro he a b c d
    intro h1 h2
    apply (not_le_of_gt he)
    have h11 : (a + b + c + d) ^ 2 = (8 - e) ^ 2 := by
      rw [(by rw [←h1]; simp only [add_sub_cancel_right] : a + b + c + d = 8 - e)]
    have h12 :  a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 16 - e ^ 2 := by
      rw [←h2]; simp only [add_sub_cancel_right]
    have h3 : (a - b)^2 + (a - c)^2 + (a - d)^2 + (b - c)^2 + (b - d)^2 + (c - d)^2 = 4 * (16 - e^2) - (8 - e)^2 := by
      linear_combination 4 * h12 - h11
    have h4 : 4 * (16 - e ^ 2) - (8 - e) ^ 2 ≥ 0 := by rw [←h3]; positivity
    revert h4
    rw [(by ring_nf : 4 * (16 - e ^ 2) - (8 - e) ^ 2 = e * (16 - 5 * e))]
    contrapose!
    intro _
    rw [mul_comm]
    apply mul_neg_of_neg_of_pos
    linarith
    positivity
