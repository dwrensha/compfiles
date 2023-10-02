/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import MathPuzzles.Meta.ProblemExtraction

#[problem_setup]/-!
# International Mathematical Olympiad 2017, Problem 2

Find all functions `f : ℝ → ℝ` that satisfy

  ∀ x,y ∈ ℝ, f(f(x)f(y)) + f(x + y) = f(xy).

-/

#[problem_setup] namespace Imo2017P2

fill_in_the_blank solution_set : Set (ℝ → ℝ) :=
  { fun _ ↦ 0, fun x ↦ x - 1, fun x ↦ 1 - x }

problem imo2017_p2 (f : ℝ → ℝ) :
    f ∈ solution_set ↔ ∀ x y, f (f x * f y) + f (x + y) = f (x * y) := by
  constructor
  · intro hf x y
    simp only [Set.mem_singleton_iff, Set.mem_insert_iff] at hf
    obtain rfl | rfl | rfl := hf <;> ring
  · intro hf
    sorry
