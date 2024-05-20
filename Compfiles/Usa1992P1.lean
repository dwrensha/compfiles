/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Data.Nat.Digits
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 1992, Problem 1

Find, as a function of n, the sum of the digits of

     9 × 99 × 9999 × ... × (10^2ⁿ - 1),

where each factor has twice as many digits as the last one.
-/

namespace Usa1992P1
open BigOperators

determine solution : ℕ → ℕ := sorry

problem usa1992_p1 (n : ℕ) :
    (Nat.digits 10
     (∏ i ∈ Finset.range n, (10^(2^(i + 1)) - 1))).sum = solution n := by
  sorry
