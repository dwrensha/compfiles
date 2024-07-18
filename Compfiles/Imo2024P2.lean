/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 2024, Problem 2

For which pairs of positive integers (a,b) is the sequence

   gcd(aⁿ + b, bⁿ + a),   n = 1, 2, ...

eventually constant?
-/

namespace Imo2024P2

determine SolutionSet : Set (ℕ+ × ℕ+) := sorry

problem imo2024_p2 (a b : ℕ+) :
    (a, b) ∈ SolutionSet ↔
    ∃ m C : ℕ,
      ∀ n, m ≤ n → Nat.gcd (a^n + b) (b^n + a) = C := by
  sorry

end Imo2024P2
