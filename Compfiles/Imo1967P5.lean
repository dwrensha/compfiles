/-
Copyright (c) 2025 The Compfiles Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib

import ProblemExtraction


problem_file {
  tags := [.Combinatorics]
}

/-!
# International Mathematical Olympiad 1967, Problem 5

Consider the sequence {cₙ}, where

   c₁ = a₁  + a₂  + ... + a₈
   c₂ = a₁² + a₂² + ... + a₈²
   ...
   cₙ = a₁ⁿ + a₂ⁿ + ... + a₈ⁿ

in which a₁, a₂, ..., a₈ are real numbers not all
equal to zero. Suppose that an infinite number of terms
of the sequence {cₙ} are equal to zero. Find all natural
numbers n such that cₙ = 0.
-/

namespace Imo1967P5

determine solution : (Fin 8 → ℝ) → Set ℕ := sorry

problem imo1967_p5 (a : Fin 8 → ℝ)
    (h : Set.Infinite {n | ∑ i, a i ^ n = 0}) :
    solution a = {n | ∑ i, a i ^ n = 0} := by
  sorry

end Imo1967P5
