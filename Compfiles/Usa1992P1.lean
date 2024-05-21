/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Data.Nat.Digits
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 1992, Problem 1

Find, as a function of n, the sum of the digits of

     9 × 99 × 9999 × ... × (10^2ⁿ - 1),

where each factor has twice as many digits as the last one.
-/

namespace Usa1992P1
open BigOperators

determine solution : ℕ → ℕ := fun n ↦ 9 * 2 ^ n

problem usa1992_p1 (n : ℕ) :
    (Nat.digits 10
     (∏ i ∈ Finset.range (n + 1), (10^(2^i) - 1))).sum = solution n := by
    -- we follow the informal proof from
    -- https://prase.cz/kalva/usa/usoln/usol921.html

    -- Induction on n.
    induction' n with n ih
    · simp; done

    -- Assume it is true for n-1.
    -- Obviously a_n < 10 to the power of 2^n
    let a i := 10^(2^i) - 1
    have h1 : ∀ i, a i < 10 ^ (2 ^ i) := fun i ↦ by
      dsimp [a]
      have h2 : 0 < 10 ^ 2 ^ i := by positivity
      omega

    let b : ℕ → ℕ := fun m ↦ ∏ i ∈ Finset.range (m + 1), a i
    -- So b_{n-1} < 10 to the power of (1 + 2 + 2^2 + ... + 2^{n-1}).
    have h2 : ∀ m, b m < 10^(∑ i ∈ Finset.range (m + 1), 2^i) := fun m ↦ by
      dsimp [b]
      rw [←Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_lt_prod_of_nonempty ?_ ?_ Finset.nonempty_range_succ
      · intro i hi
        dsimp [a]
        have h3 : 1 ≤ 2 ^ i := Nat.one_le_two_pow
        have h4 : 10 ^ 1 ≤ 10 ^ (2 ^ i) :=
          Nat.pow_le_pow_of_le_right (by norm_num) h3
        dsimp at h4
        calc
          _ < 10 - 1 := by norm_num
          _ = 10^1 - 1 := by omega
          _ ≤ 10^(2^i) - 1 := Nat.sub_le_sub_right h4 _
      · intro i hi
        exact h1 i

    /- ... < 10 to the power of 2n. Now bn = bn-110N - bn-1, where N = 2n. But bn-1 < 10N, so bn = (bn-1 - 1)10N + (10N - bn-1) and the digit sum of bn is just the digit sum of (bn-1 - 1)10N plus the digit sum of (10N - bn-1).

    Now bn-1 is odd and so its last digit is non-zero, so the digit sum of bn-1 - 1 is one less than the digit sum of bn-1, and hence is 9·2n-1 - 1. Multiplying by 10N does not change the digit sum. (10N - 1) - bn-1 has 2n digits, each 9 minus the corresponding digit of bn-1, so its digit sum is 9·2n - 9·2n-1. bn-1 is odd, so its last digit is not 0 and hence the last digit of (10N - 1) - bn-1 is not 9. So the digit sum of 10N - bn-1 is 9·2n - 9·2n-1 + 1. Hence bn has digit sum (9·2n-1 - 1) + (9·2n - 9·2n-1 + 1) = 9·2n.
    -/

    sorry
