/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file

/-!
# International Mathematical Olympiad 2015, Problem 5

Determine all functions f : ℝ → ℝ that satisfy

  f(x + f(x + y)) + f(xy) = x + f(x + y) + yf(x)

for all x,y.
-/

namespace Imo2012P5

determine solution_set : Set (ℝ → ℝ) := sorry

problem imo2015_p5 (f : ℝ → ℝ) :
    f ∈ solution_set ↔
    ∀ x y, f (x + f (x + y)) + f (x * y) = x + f (x + y) + y * f x := by
  sorry
