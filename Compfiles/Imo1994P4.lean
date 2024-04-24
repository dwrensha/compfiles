/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 1994, Problem 4

Determine all ordered pairs of positive integers (m, n) such that

            (n³ + 1) / (mn - 1)

is an integer.
-/

namespace Imo1994P4

determine SolutionSet : Set (ℤ × ℤ) := sorry

problem imo1994_p4 (m n : ℤ) :
    (m, n) ∈ SolutionSet ↔
    0 < m ∧ 0 < n ∧ (m * n - 1) ∣ (n^3 + 1) := by
  sorry
