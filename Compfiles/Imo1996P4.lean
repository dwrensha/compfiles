/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 1996, Problem 4

The positive integers a and b are such that the numbers 15a + 16b
and 16a − 15b are both squares of positive integers. What is the least
possible value that can be taken on by the smaller of these two squares?

-/

namespace Imo1996P4

determine solution : ℤ := sorry

def S := { l | ∃ a b m n : ℤ,
    0 < a ∧ 0 < b ∧ 0 < m ∧ 0 < n ∧
    15*a + 16*b = m^2 ∧
    16*a - 15*b = n^2 ∧
    l = min (m^2) (n^2) }

problem imo1996P4 : solution ∈ S ∧ ∀ x ∈ S, solution ≤ x := by
  sorry

end Imo1996P4
