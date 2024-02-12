/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1999, Problem 6

Determine all functions f : ℝ → ℝ such that

  f(x - f(y)) = f(f(y)) + xf(y) + f(x) - 1

for all x,y ∈ ℝ.
-/

namespace Imo1999P6

determine solution_set : Set (ℝ → ℝ) := sorry

problem imo1999_p6 (f : ℝ → ℝ) :
    f ∈ solution_set ↔
    ∀ x y, f (x - f y) = f (f y) + x * f y + f x - 1 := by
  sorry
