/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InternLM-MATH LEAN Formalizer v0.1
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 1978, Problem 1

m and n are positive integers with m < n.
The last three decimal digits of 1978ᵐ are the same as the
last three decimal digits of 1978ⁿ.
Find m and n such that m + n has the least possible value.
-/

namespace Imo1978P1

determine solution : ℕ × ℕ := (3, 103)

abbrev ValidPair : ℕ × ℕ → Prop
| (m, n) => 1 ≤ m ∧ m < n ∧ (1978^m) % 1000 = (1978^n) % 1000

problem imo1978_p1 (m n : ℕ)
    (hmn : (m, n) = solution) :
    ValidPair (m, n) ∧
    (∀ m' n' : ℕ, ValidPair (m', n') → m + n ≤ m' + n') := by
  sorry

end Imo1978P1
