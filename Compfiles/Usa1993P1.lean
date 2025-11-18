/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 1993, Problem 1

For each integer n ≥ 2, determine whether a or b is larger,
where a and b are positive real numbers satisfying

            aⁿ = a + 1,     b²ⁿ = b + 3a.
-/

namespace Usa1993P1

determine a_is_larger : ℕ → Bool := fun _ ↦ true

problem usa1993_p1 (n : ℕ) (hn : 2 ≤ n) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (han : a^n = a + 1) (hbn : b^(2 * n) = b + 3 * a) :
    if a_is_larger n then b < a else a < b := by
  -- informal proof outline taken from
  -- https://artofproblemsolving.com/wiki/index.php/1993_USAMO_Problems/Problem_1
  simp only [a_is_larger, ite_true]
  have h1 : a^(2 * n) - a = a^2 + a + 1 := by
    have h2 : a^n * a^n = (a + 1) * (a + 1) :=
      abs_eq_iff_mul_self_eq.mp (congrArg abs han)
    linear_combination h2
  have h3 : b ^ (2 * n) - b = 3 * a := sub_eq_of_eq_add' hbn
  have h4 : a - 1 ≠ 0 := by
    intro H
    obtain rfl : a = 1 := by linarith only [H]
    norm_num at han
  have h5 : 0 < (a - 1)^2 := by positivity
  have h6 : 3 * a < a^2 + a + 1 := by linarith only [h5]
  have h7 : b ^ (2 * n) - b < a^(2 * n) - a := by linarith only [h1, h3, h6]
  cases n with | zero => norm_num at hn | succ n =>
  have h11 : 0 ≤ a := LT.lt.le ha
  have h20 : 0 ≤ b := LT.lt.le hb

  have h8 : 1 < a := by
    rw[pow_succ] at han
    have h9 : a < a * a^n := by linarith only [han, ha]
    have h10 : 1 < a^n := (lt_mul_iff_one_lt_right ha).mp h9
    rw [←one_pow n] at h10
    exact lt_of_pow_lt_pow_left₀ n h11 h10
  obtain h12 | rfl | h14 := lt_trichotomy a b
  · exfalso
    have h15 : a^(2*n + 1) - 1 < b^(2* n + 1) - 1 := by
      have h15' : a^(2*n + 1) < b^(2* n + 1) :=
        pow_lt_pow_left₀ h12 h11 (Nat.succ_ne_zero (2 * n))
      exact sub_lt_sub_right h15' 1
    have h16 : 0 < a ^(2 * n + 1) - 1 := by
      suffices H : 1 < a ^ (2 * n + 1) from sub_pos.mpr H
      exact one_lt_pow₀ h8 (Nat.succ_ne_zero (2 * n))
    have h17 : a * (a^(2*n + 1) - 1) < b * (b^(2* n + 1) - 1) :=
      mul_lt_mul_of_pos' h12 h15 h16 hb
    have h18 : a * (a ^ (2 * n + 1) - 1) = a^(2*(n + 1)) - a := by ring
    have h19 : b * (b ^ (2 * n + 1) - 1) = b^(2*(n + 1)) - b := by ring
    order
  · linarith only [h7]
  · exact h14


end Usa1993P1
