/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file

/-!
# USA Mathematical Olympiad 2011, Problem 4

For any integer n ≥ 2, define P(n) to be the proposition:

  P(n) ≡  2^(2^n) % (2^n - 1) is a power of 4

Either prove that P(n) is always true, or find a counterexample.
-/

namespace Usa2011P4

abbrev P (n : ℕ) : Prop := ∃ k, 4^k = 2^(2^n) % (2^n - 1)

inductive SolutionData where
| AlwaysTrue : SolutionData
| CounterExample : ℕ → SolutionData

determine solution_data : SolutionData := SolutionData.CounterExample 25

problem usa2011_p4 :
    match solution_data with
    | .AlwaysTrue => ∀ n, 2 ≤ n → P n
    | .CounterExample m => 2 ≤ m ∧ ¬ P m := by
  -- See https://web.evanchen.cc/exams/USAMO-2011-notes.pdf for an informal proof.
  dsimp
  refine' ⟨by norm_num, _⟩
  rw [not_exists]
  intro x hx
  rw [show 4 = 2^2 by rfl, ←Nat.pow_mul] at hx

  -- 2^(2^25) is small enough that we can just normalize it.
  rw [show 2 ^ 2 ^ 25 % (2 ^ 25 - 1) = 2 ^ 7 by rfl] at hx

  have h2 : 2 ≤ 2 := by norm_num
  have h3 := Nat.pow_right_injective h2 hx
  apply_fun (· % 2) at h3
  norm_num at h3
