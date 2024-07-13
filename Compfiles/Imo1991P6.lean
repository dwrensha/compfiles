/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1991, Problem 6

An infinite sequence x₀,x₁,x₂,... of real numbers is said to be *bounded*
if there is a constant C such that |xᵢ| ≤ C for every i ≥ 0.

Given any real number a > 1, construct a bounded infinite sequence
x₀,x₁,x₂,... such that

                  |xᵢ - xⱼ|⬝|i - j| ≥ 1

for every pair of distinct nonnegative integers i, j.
-/

namespace Imo1991P6

abbrev Bounded (x : ℕ → ℝ) : Prop := ∃ C, ∀ i, |x i| ≤ C

determine solution (a : ℝ) (ha : 1 < a) : ℕ → ℝ := sorry

problem imo1991_p6 (a : ℝ) (ha : 1 < a) :
    Bounded (solution a ha) ∧
    ∀ i j, i ≠ j →
      1 ≤ |solution a ha i - solution a ha j| * |(i:ℝ) - j| := by
  sorry


end Imo1991P6
