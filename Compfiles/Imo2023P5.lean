/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

import Compfiles.Meta.ProblemExtraction

problem_file

/-!
# International Mathematical Olympiad 2023, Problem 5

Let n be a positive integer. A _Japanese triangle_ is defined as
a set of 1 + 2 + ... + n dots arranged as an equilateral
triangle. Each dot is colored white or red, such that each row
has exactly one red dot.

A _ninja path_ is a sequence of n dots obtained by starting in the
top row (which has length 1), and then at each step going to one of
the dot immediately below the current dot, until the bottom
row is reached.

In terms of n, determine the greatest k such that in each Japanese triangle
there is a ninja path containing at least k red dots.
-/

namespace Imo2023P5

structure JapaneseTriangle (n : ℕ) where
  red : (i : Fin n) → Fin i.val

structure NinjaPath (n : ℕ) where
  steps : (i : Fin n) → Fin i.val
  steps_valid : ∀ i : Fin n, (h : i.val + 1 < n) →
     ((steps i).val = steps ⟨i.val+1, h⟩ ∨
      (steps i).val + 1 = steps ⟨i.val+1, h⟩)

determine solution_value (n : ℕ) : ℕ := sorry

problem imo2023_p5 (n : ℕ) :
    IsGreatest {k | ∀ j : JapaneseTriangle n,
                    ∃ p : NinjaPath n,
                      k ≤ Fintype.card {i : Fin n // j.red i = p.steps i}}
               (solution_value n) := by
  sorry
