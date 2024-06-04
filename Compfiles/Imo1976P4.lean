/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 1976, Problem 4

Determine, with proof, the largest number which is the product
of positive integers whose sum is 1976.
-/

namespace Imo1976P4

determine solution : ℕ := sorry

problem imo1976_p4 :
    IsGreatest
      { n | ∃ s : Finset ℕ, ∑ i ∈ s, i = 1976 ∧ ∏ i ∈ s, i = n }
      solution := by
  sorry
