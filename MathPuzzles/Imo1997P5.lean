/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import MathPuzzles.Meta.ProblemExtraction

#[problem_setup]/-!
# International Mathematical Olympiad 1997, Problem 5

Determine all pairs of integers 1 ≤ a,b that satisfy a ^ (b ^ 2) = b ^ a.
-/

#[problem_setup] namespace Imo1997P5

determine solution_set : Set (ℕ × ℕ) := sorry

problem imo1997_p5 (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ⟨a,b⟩ ∈ solution_set ↔ a ^ (b ^ 2) = b ^ a := by
  sorry
