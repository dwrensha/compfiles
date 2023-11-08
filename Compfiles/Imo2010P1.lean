/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file

/-!
# International Mathematical Olympiad 2010, Problem 1

Determine all functions f : ℝ → ℝ such that for all x,y ∈ ℝ,

               f(⌊x⌋y) = f(x)⌊f(y)⌋.
-/

namespace Imo2010P1

determine solution_set : Set (ℝ → ℝ) := sorry

problem imo2010_p1 (f : ℝ → ℝ) :
    f ∈ solution_set ↔ ∀ x y, f (⌊x⌋ * y) = f x * ⌊f y⌋ := by
  sorry
