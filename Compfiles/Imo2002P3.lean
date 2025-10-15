/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 2002, Problem 3

Find all pairs of positive integers m,n ≥ 3 for which
there exist infinitely many positive integers a such that

   (aᵐ + a - 1) / (aⁿ + a² - 1)

is itself an integer.

-/

namespace Imo2002P3

determine solution : Set (ℕ × ℕ) := sorry

problem imo2002P3 (m n : ℕ) :
    ⟨m, n⟩ ∈ solution ↔
      Set.Infinite { a : ℤ | 0 < a ∧ a ^ n + a ^ 2 - 1 ∣ a ^ m + a - 1 } := by
  sorry

end Imo2002P3
