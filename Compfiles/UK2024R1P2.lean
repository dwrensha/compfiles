/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: short_c1rcuit
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-
# British Mathematical Olympiad 2024, Round 1, Problem 1

The sequence of integers a₀, a₁, ⋯ has the property that for each
i ≥ 2, aᵢ is either 2 * aᵢ₋₁ - aᵢ₋₂, or 2 * aᵢ₋₂ - aᵢ₋₁.

Given that a₂₀₂₃ and a₂₀₂₄ are consecutive integers, prove that a₀
and a₁ are consecutive.
-/

namespace UK2024R1P2

problem uk2024_r1_p2 (a : ℕ → ℤ)
    (ha : ∀ i ≥ 2, a i = 2 * a (i - 1) - a (i - 2) ∨ a i = 2 * a (i - 2) - a (i - 1))
    (ha' : |a 2023 - a 2024| = 1) :
    |a 0 - a 1| = 1 :=  by
  suffices H : ∀ k ≤ 2023, |a k - a (k + 1)| = 1 from H 0 (Nat.zero_le _)
  intro k hk
  induction hk using Nat.decreasingInduction with
  | self => exact ha'
  | of_succ i _ hP =>
    specialize ha (i + 1 + 1) (by norm_num)
    simp at *
    obtain ha | ha := ha <;> rw [ha] at hP
    · rwa [two_mul, ←sub_add, sub_add_cancel_right, neg_add_eq_sub] at hP
    -- This branch is invalid because the difference between the terms we know are consecutive is both 1 and a multiple of 2, which is a contradiction
    · rw [←sub_add, sub_add_eq_add_sub, ←two_mul, ←mul_sub_left_distrib, abs_mul, Int.mul_eq_one_iff_eq_one_or_neg_one] at hP
      obtain hP | hP := hP <;> replace hP := hP.1 <;> norm_num at hP

end UK2024R1P2
