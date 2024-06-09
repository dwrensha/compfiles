/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1963, Problem 4

Find all solutions x₁,x₂,x₃,x₄,x₅ of the system

  x₅ + x₂ = yx₁
  x₁ + x₃ = yx₂
  x₂ + x₄ = yx₃
  x₃ + x₅ = yx₄
  x₄ + x₁ = yx₅

where y is a parameter.
-/

namespace Imo1963P4

determine SolutionSet (y : ℝ) : Set (ℝ × ℝ × ℝ × ℝ × ℝ) := sorry

problem imo1963_p4 (x₁ x₂ x₃ x₄ x₅ y : ℝ) :
    (x₁, x₂, x₃, x₄, x₅) ∈ SolutionSet y ↔
    (x₅ + x₂ = y * x₁ ∧
     x₁ + x₃ = y * x₂ ∧
     x₂ + x₄ = y * x₃ ∧
     x₃ + x₅ = y * x₄ ∧
     x₄ + x₁ = y * x₅) := by
  sorry
