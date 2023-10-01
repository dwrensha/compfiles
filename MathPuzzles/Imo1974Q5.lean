/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import MathPuzzles.Meta.ProblemExtraction

#[problem_setup]/-!
# International Mathematical Olympiad 1974, Problem 5

What are the possible values of

 a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d)

as a,b,c,d range over the positive real numbers?
-/

#[problem_setup] namespace Imo1974Q5

fill_in_the_blank solution_set : Set ℝ := Set.Ioo 1 2

problem imo1974_q5 (x : ℝ) :
    x ∈ solution_set ↔
    ∃ a b c d : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
     x = a / (a + b + d) + b / (a + b + c) +
         c / (b + c + d) + d / (a + c + d) := by
  constructor
  · intro hx
    sorry
  · rintro ⟨a, b, c, d, ha, hb, hc, hd, hs⟩
    sorry
