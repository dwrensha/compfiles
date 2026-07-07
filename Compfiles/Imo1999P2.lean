/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra, .Inequality] }

/-!
# International Mathematical Olympiad 1999, Problem 2

Let n ≥ 2 be a fixed integer. Find the least constant C such that

  ∑_{i < j} xᵢxⱼ(xᵢ² + xⱼ²) ≤ C (∑ i, xᵢ)⁴

for all non-negative real numbers x₁, ..., xₙ.
-/

namespace Imo1999P2

determine C : ℝ := sorry

problem imo1999_p2 (n : ℕ) (hn : 2 ≤ n) :
    IsLeast
      {c : ℝ | ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) →
        ∑ i, ∑ j ∈ Finset.Ioi i, x i * x j * ((x i) ^ 2 + (x j) ^ 2) ≤
          c * (∑ i, x i) ^ 4}
      C := by
  sorry

end Imo1999P2
