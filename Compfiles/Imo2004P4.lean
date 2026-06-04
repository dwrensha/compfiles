/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra, .Inequality] }

/-!
# International Mathematical Olympiad 2004, Problem 4

Let n ≥ 3 be an integer. Let t₁, t₂, ..., tₙ be positive real numbers
such that

  n² + 1 > (t₁ + t₂ + ⋯ + tₙ) (1/t₁ + 1/t₂ + ⋯ + 1/tₙ).

Show that tᵢ, tⱼ, tₖ are the side lengths of a triangle for all i, j, k
with 1 ≤ i < j < k ≤ n.
-/

namespace Imo2004P4

problem imo2004_p4 (n : ℕ) (hn : 3 ≤ n) (t : Fin n → ℝ)
    (ht : ∀ i, 0 < t i)
    (hsum : (∑ i, t i) * (∑ i, 1 / t i) < n ^ 2 + 1)
    (i j k : Fin n) (hij : i < j) (hjk : j < k) :
    ∃ T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)),
      dist (T.points 0) (T.points 1) = t i ∧
      dist (T.points 1) (T.points 2) = t j ∧
      dist (T.points 2) (T.points 0) = t k := by
  sorry


end Imo2004P4
