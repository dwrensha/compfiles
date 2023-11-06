/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file

/-!
# International Mathematical Olympiad 1992, Problem 2

Determine all functions f : ℝ → ℝ such that
for all x,y ∈ ℝ, f(x² + f(y)) = y + (f(x))².
-/

namespace Imo1992P2

determine solution_set : Set (ℝ → ℝ) := sorry

problem imo1992_p2 (f : ℝ → ℝ) :
    f ∈ solution_set ↔
    ∀ x y, f (x^2 + f y) = y + (f x)^2 := by
  sorry
