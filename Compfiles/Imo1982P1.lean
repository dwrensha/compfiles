/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

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
  -- Follows Solution 1 by sayantanchakraborty at
  -- https://artofproblemsolving.com/wiki/index.php/1982_IMO_Problems/Problem_1
  have h4 : f 1 = 0 := by
    have h5 := hf 1 1 Nat.one_pos Nat.one_pos
    rw [h2] at h5
    omega
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
  have h9 : ∀ k l, 0 < k → f (3 * k) + l ≤ f (3 * (k + l)) := by
    intro k l hk
    induction' l with l ih
    · simp
    · have h10 := h6 (k + l) (Nat.add_pos_left hk l)
      have h11 : 3 * (k + l) + 3 = 3 * (k + Nat.succ l) := by omega
      have h12 : f (3 * k) + Nat.succ l = f (3 * k) + l + 1 := by omega
      rw [←h11, h12]
      omega
  have h8 : ∀ k, 0 < k → k ≤ 3333 → f (3 * k) = k := by
     intro k hk0 hk1
     by_contra! H
     have h11 := h9 1 (k - 1) zero_lt_one
     have h12 : 1 + (k - 1) = k := Nat.add_sub_of_le hk0
     rw [mul_one, h5, h12] at h11
     have h13 : k < f (3 * k) := Nat.lt_of_le_of_ne h11 H.symm
     have h14 := h9 k (3333 - k) hk0
     have h15 : k + (3333 - k) = 3333 := Nat.add_sub_of_le hk1
     rw [h15, h9999] at h14
     omega
  have h20 : ∀ k, 0 < k → f k ≤ f (k + 1) := by
    intro k hk
    cases' hf k 1 hk one_pos with h21 h21 <;> omega
  have h30 : ∀ k l, 0 < k → l ≤ f k → l + l ≤ f (k + k) := by
    intro k l hk hl
    cases' hf k k hk hk with h21 h21 <;> omega
  have h10 : ∀ k, 0 < k → 12 * k + 9 ≤ 9999 → f (3 * k + 2) = k := by
    intro k hk hk1
    cases' hf (3*k) 2 (Nat.succ_mul_pos 2 hk) two_pos with h11 h11
    · rw [h11, h2, add_zero]
      exact h8 k hk (by omega)
    · rw [h2, add_zero, h8 k hk (by omega)] at h11
      exfalso
      have h12 : 2 * k + 2 ≤ f (6 * k + 4) := by
        have h14 : 3 * k + 2 + (3 * k + 2) = 6 * k + 4 := by ring
        have h15 : k + 1 + (k + 1) = 2 * k + 2 := by ring
        rw [←h14, ←h15]
        exact h30 _ _ (Nat.succ_pos _) (Nat.le_of_eq h11.symm)
      have h13 : 4 * k + 4 ≤ f (12 * k + 8) := by
        have h14 : 6 * k + 4 + (6 * k + 4) = 12 * k + 8 := by ring
        have h15 : 2 * k + 2 + (2 * k + 2) = 4 * k + 4 := by ring
        rw [←h14, ←h15]
        exact h30 _ _ (Nat.succ_pos _) h12
      have h14 : f (12 * k + 8) ≤ f (12 * k + 9) := by
        have h15 : 12 * k + 8 + 1 = 12 * k + 9 := by ring
        rw [←h15]
        exact h20 _ (Nat.succ_pos _)
      have h15 : f (12 * k + 9) = 4 * k + 3 := by
         have h16 : 3 * (4 * k + 3) = 12 * k + 9 := by ring
         have h17 := h8 (4 * k + 3) (Nat.succ_pos _) (by omega)
         rw [h16] at h17
         exact h17
      rw [h15] at h14
      exact Nat.lt_le_asymm h13 h14
  exact h10 660 (Nat.succ_pos _) (by norm_num)


end Imo1982P1
