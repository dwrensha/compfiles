/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import Compfiles.Meta.ProblemExtraction

problem_file

/-!
# International Mathematical Olympiad 1982, Problem 1

Let f be a function from positive integers to nonnegative integers such that
 1) f(2) = 0
 2) f(3) > 0
 3) f(9999) = 3333
 4) for all m,n > 0, f (m + n) - f (m) - f(n) = 1 or 0

Determine the value of f(1982).
-/

namespace Imo1982P1

determine solution_value : ℕ := 660

problem imo1982_p1 (f : ℕ → ℕ)
    (h2 : f 2 = 0)
    (h3 : 0 < f 3)
    (h9999 : f 9999 = 3333)
    (hf : ∀ m n, 0 < m → 0 < n → f (m + n) = f m + f n ∨ f (m + n) = f m + f n + 1) :
    f 1982 = solution_value := by
  -- Follow Solution 1 by sayantanchakraborty at
  -- https://artofproblemsolving.com/wiki/index.php/1982_IMO_Problems/Problem_1
  have h4 : f 1 = 0 := by
    have h5 := hf 1 1 Nat.one_pos Nat.one_pos
    rw [h2] at h5
    cases' h5 with h6 h6
    · exact Nat.bit0_eq_zero.mp h6.symm
    · rw [add_assoc] at h6
      exact Nat.eq_zero_of_add_eq_zero_right h6.symm
  have h5 : f 3 = 1 := by
    have := hf 1 2 Nat.one_pos two_pos
    aesop
  have h7 : ∀ m n, 0 < m → 0 < n → f m + f n ≤ f (m + n) := by
    intro m n hm hn
    cases' hf m n hm hn with h8 h8
    · exact Nat.le_of_eq h8.symm
    · exact Nat.le.intro h8.symm
  have h6 : ∀ k, 0 < k → f (3 * k) < f (3 * k + 3) := fun k hk ↦ by
    calc _ < f (3 * k) + f 3 := Nat.lt_add_of_pos_right h3
         _ ≤ _ := h7 _ _ (Nat.succ_mul_pos 2 hk) three_pos
  have h8 : ∀ k, 0 < k → k ≤ 3333 → f (3 * k) = k := by
     intro k hk0 hk1
     sorry
  sorry
