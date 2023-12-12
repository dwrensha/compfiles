/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file

/-!
# USA Mathematical Olympiad 1990, Problem 2

A sequence of functions {fₙ(x)} is defined recursively as follows:

                  f₀(x) = 8
                fₙ₊₁(x) = √(x² + 6fₙ(x)).

For each nonnegative integer n, find all real solutions of the equation

                  fₙ(x) = 2x.
-/

namespace Usa1990P2

noncomputable def f : ℕ → ℝ → ℝ
|     0, _ => 8
| n + 1, x => Real.sqrt (x^2 + 6 * f n x)

determine solution_set (n : ℕ) : Set ℝ := sorry

problem usa1990_p2 (n : ℕ) (x : ℝ) : x ∈ solution_set n ↔ f n x = 2 * x := by
  sorry
