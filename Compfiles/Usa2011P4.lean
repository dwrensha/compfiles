/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import Compfiles.Meta.ProblemExtraction

problem_file

/-!
# USA Mathematical Olympiad 2011, Problem 4

For any integer n > 1, let P(n) be the proposition:

  "2^(2^n) % (2^n - 1) is a power of 4"

Either prove that P(n) is always true, or find a counterexample.
-/

namespace Usa2011P4

abbrev P (n : ℕ) : Prop := ∃ k, 4^k = 2^(2^n) % (2^n - 1)

inductive SolutionData where
| AlwaysTrue : SolutionData
| CounterExample : ℕ → SolutionData

determine solution_data : SolutionData := sorry

problem usa2011_p4 :
    match solution_data with
    | .AlwaysTrue => ∀ n, 2 ≤ n → P n
    | .CounterExample m => 2 ≤ m ∧ ¬ P m := by
  sorry
