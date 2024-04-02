/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 2015, Problem 1

Solve in integers the equation x² + xy + y² = ((x + y) / 3 + 1)³.
-/

namespace Usa2015P1

determine SolutionSet : Set (ℤ × ℤ) := sorry

problem usa2015_p1 (x y : ℤ) :
    ⟨x, y⟩ ∈ SolutionSet ↔
    x^2 + x * y + y^2 = ((x + y) / 3 + 1)^3 := by
  sorry
