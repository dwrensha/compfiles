/-
Copyright (c) 2025 The Compfiles Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra, .NumberTheory] }

/-!
# International Mathematical Olympiad 2000, Problem 5

Does there exist a positive integer n such that n has exactly
2000 distinct prime divisors and n divides 2ⁿ + 1?

-/

namespace Imo2000P5

determine solution : Bool := sorry

problem imo2000P5 :
    ∃ n, 0 < n ∧ n.primeFactors.card = 2000 ∧ n ∣ 2 ^ n + 1
    ↔ solution := by
  sorry

end Imo2000P5
