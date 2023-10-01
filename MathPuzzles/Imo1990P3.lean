/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import MathPuzzles.Meta.ProblemExtraction

#[problem_setup]/-!
# International Mathematical Olympiad 1990, Problem 3

Find all integers n > 1 such that n² divides 2ⁿ + 1.
-/

#[problem_setup] namespace Imo1990P3

fill_in_the_blank solution_set : Set ℕ := sorry

problem imo1990_p3 (n : ℕ) (hn : 1 < n) : n ∈ solution_set ↔ n^2 ∣ 2^n + 1 := by
  sorry
