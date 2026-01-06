/-
Copyright (c) 2025 The Compfiles Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib

import ProblemExtraction


problem_file {
  tags := [.NumberTheory]
}

/-!
# International Mathematical Olympiad 1996, Problem 6

Let p, q, n be three positive integers with p + q < n. Let (x₀, x₁, . . . , xₙ)
be an (n + 1)-tuple of integers satisfying the following conditions:
(a) x₀ = xₙ = 0.
(b) For each i with 1 ≤ i ≤ n, either xᵢ − xᵢ₋₁ = p or xᵢ − xᵢ₋₁ = −q.
Show that there exist indices i < j with (i, j) ≠ (0, n), such that xᵢ = xⱼ.

-/

namespace Imo1996P6

problem imo1996_p6 {p q n : ℕ} (x : ℕ → ℤ)
    (h₁ : 0 < p) (h₂ : 0 < q) (h₃ : 0 < n) (h₄ : p + q < n)
    (h₅ : x 0 = 0) (h₆ : x n = 0)
    (h₇ : ∀ i < n, x (i + 1) - x i = p ∨ x (i + 1) - x i = -q) :
    ∃ i j : ℕ, 0 ≤ i ∧ i < j ∧ j ≤ n ∧ (i, j) ≠ (0, n) ∧ x i = x j := by
  sorry

end Imo1996P6
