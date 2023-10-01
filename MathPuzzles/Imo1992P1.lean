/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import MathPuzzles.Meta.ProblemExtraction

#[problem_setup]/-!
# International Mathematical Olympiad 1992, Problem 1

Find all integers 1 < a < b < c such that
(a - 1)(b - 1)(c - 1) divides abc - 1.
-/

#[problem_setup] namespace Imo1992P1

fill_in_the_blank solution_set : Set (ℤ × ℤ × ℤ) := sorry

problem imo1992_p1 (a b c : ℤ) (ha : 1 < a) (hb : a < b) (hc : b < c) :
    ⟨a, b, c⟩ ∈ solution_set ↔
    (a - 1) * (b - 1) * (c - 1) ∣ a * b * c - 1 := by
  sorry
