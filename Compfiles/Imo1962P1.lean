/-
Copyright (c) 2020 Kevin Lacker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker
-/
import Mathlib.Data.Nat.Digits.Lemmas

import ProblemExtraction

problem_file {
  tags := [.NumberTheory]
  importedFrom :=
    "https://github.com/leanprover-community/mathlib4/blob/master/Archive/Imo/Imo1962Q1.lean"
}

/-!
# International Mathematical Olympiad 1962, Problem 1

Find the smallest natural number $n$ which has the following properties:

(a) Its decimal representation has 6 as the last digit.

(b) If the last digit 6 is erased and placed in front of the remaining digits,
the resulting number is four times as large as the original number $n$.
-/


namespace Imo1962P1

open Nat

def ProblemPredicate (n : ℕ) : Prop :=
  (digits 10 n).headI = 6 ∧ ofDigits 10 ((digits 10 n).tail.concat 6) = 4 * n

snip begin
/-!
First, it's inconvenient to work with digits, so let's simplify them out of the problem.
-/

abbrev ProblemPredicate' (c n : ℕ) : Prop :=
  n = 10 * c + 6 ∧ 6 * 10 ^ (digits 10 c).length + c = 4 * n

theorem without_digits {n : ℕ} (h1 : ProblemPredicate n) : ∃ c : ℕ, ProblemPredicate' c n := by
  use n / 10
  cases' n with n
  · have h2 : ¬ProblemPredicate 0 := by norm_num [ProblemPredicate]
    contradiction
  · rw [ProblemPredicate, digits_def' (by decide : 2 ≤ 10) n.succ_pos, List.headI, List.tail_cons,
      List.concat_eq_append] at h1
    constructor
    · rw [← h1.left, div_add_mod (n + 1) 10]
    · rw [← h1.right, ofDigits_append, ofDigits_digits, ofDigits_singleton, add_comm, mul_comm]

/-!
Now we can eliminate possibilities for `(digits 10 c).length` until we get to the one that works.
-/


theorem case_0_digit {c n : ℕ} (h1 : (digits 10 c).length = 0) : ¬ProblemPredicate' c n := by
  intro h2
  have h3 : 6 * 10 ^ 0 + c = 6 * 10 ^ (digits 10 c).length + c := by rw [h1]
  omega

theorem case_1_digit {c n : ℕ} (h1 : (digits 10 c).length = 1) : ¬ProblemPredicate' c n := by
  intro h2
  have h3 : 6 * 10 ^ 1 + c = 6 * 10 ^ (digits 10 c).length + c := by rw [h1]
  omega

theorem case_2_digit {c n : ℕ} (h1 : (digits 10 c).length = 2) : ¬ProblemPredicate' c n := by
  intro h2
  have h3 : 6 * 10 ^ 2 + c = 6 * 10 ^ (digits 10 c).length + c := by rw [h1]
  omega

theorem case_3_digit {c n : ℕ} (h1 : (digits 10 c).length = 3) : ¬ProblemPredicate' c n := by
  intro h2
  have h3 : 6 * 10 ^ 3 + c = 6 * 10 ^ (digits 10 c).length + c := by rw [h1]
  omega

theorem case_4_digit {c n : ℕ} (h1 : (digits 10 c).length = 4) : ¬ProblemPredicate' c n := by
  intro h2
  have h3 : 6 * 10 ^ 4 + c = 6 * 10 ^ (digits 10 c).length + c := by rw [h1]
  omega

/-- Putting this inline causes a deep recursion error, so we separate it out. -/
theorem helper_5_digit {c : ℤ} (h : 6 * 10 ^ 5 + c = 4 * (10 * c + 6)) : c = 15384 := by linarith

theorem case_5_digit {c n : ℕ} (h1 : (digits 10 c).length = 5) (h2 : ProblemPredicate' c n) :
    c = 15384 := by
  have h3 : 6 * 10 ^ 5 + c = 6 * 10 ^ (digits 10 c).length + c := by rw [h1]
  omega

/-- `linarith` fails on numbers this large, so this lemma spells out some of the arithmetic
that normally would be automated.
-/
theorem case_more_digits {c n : ℕ} (h1 : (digits 10 c).length ≥ 6) (h2 : ProblemPredicate' c n) :
    n ≥ 153846 := by
  have h3 : c ≠ 0 := by
    intro h4
    have h5 : (digits 10 c).length = 0 := by simp [h4]
    exact case_0_digit h5 h2
  calc
    n ≥ 10 * c := le.intro h2.left.symm
    _ ≥ 10 ^ (digits 10 c).length := (base_pow_length_digits_le 10 c (by decide) h3)
    _ ≥ 10 ^ 6 := pow_le_pow_right₀ (by decide) h1
    _ ≥ 153846 := by norm_num

/-!
Now we combine these cases to show that 153846 is the smallest solution.
-/

theorem satisfied_by_153846 : ProblemPredicate 153846 := by
  norm_num [ProblemPredicate]
  decide

theorem no_smaller_solutions (n : ℕ) (h1 : ProblemPredicate n) : n ≥ 153846 := by
  have ⟨c, h2⟩ := without_digits h1
  have h3 : (digits 10 c).length < 6 ∨ (digits 10 c).length ≥ 6 := by apply lt_or_ge
  cases h3 with
  | inr h3 => exact case_more_digits h3 h2
  | inl h3 =>
    interval_cases h : (digits 10 c).length
    · exfalso; exact case_0_digit h h2
    · exfalso; exact case_1_digit h h2
    · exfalso; exact case_2_digit h h2
    · exfalso; exact case_3_digit h h2
    · exfalso; exact case_4_digit h h2
    · have h4 : c = 15384 := case_5_digit h h2
      have h5 : n = 10 * 15384 + 6 := h4 ▸ h2.left
      exact Nat.le_of_eq h5.symm

snip end

determine solution : ℕ := 153846

problem imo1962_p1 : IsLeast {n | ProblemPredicate n} solution :=
  ⟨satisfied_by_153846, no_smaller_solutions⟩



end Imo1962P1
