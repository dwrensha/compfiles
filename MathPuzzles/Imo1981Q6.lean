/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

import MathPuzzles.Meta.ProblemExtraction

#[problem_setup]/-!
# International Mathematical Olympiad 1981, Problem 6

Suppose that f : ℕ × ℕ → ℕ satisfies

 1) f (0, y) = y + 1
 2) f (x + 1, 0) = f (x, 1),
 3) f (x + 1, y + 1) = f (x, f (x + 1, y))

for all x y ∈ ℕ.

Determine f (4, 1981).

-/

#[problem_setup] namespace Imo1981Q6

fill_in_the_blank solution_value : ℕ := (2^·)^[1984] 1 - 3

problem Imo1981Q6 (f : ℕ → ℕ → ℕ)
    (h1 : ∀ y, f 0 y = y + 1)
    (h2 : ∀ x, f (x + 1) 0 = f x 1)
    (h3 : ∀ x y, f (x + 1) (y + 1) = f x (f (x + 1) y)) :
    f 4 1981 = solution_value := by
  have h4 : ∀ y, f 1 y = y + 2 := by sorry
  have h5 : ∀ y, f 1 (y + 1) = f 1 y + 1 := by sorry
  have h6 : ∀ y, f 4 (y + 1) + 3 = 2^(f 4 y + 3) := by sorry
  sorry
