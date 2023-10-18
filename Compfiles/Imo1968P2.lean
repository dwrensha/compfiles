/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Nat.Digits
import Mathlib.Tactic

import Compfiles.Meta.ProblemExtraction

problem_file

/-!
# International Mathematical Olympiad 1968, Problem 2

Determine the set of natural numbers x such that
the sum of the decimal digits of x is equal to x² - 10x - 22.
-/

namespace Imo1968P2

determine solution_set : Set ℕ := { 12 }

problem imo1968_p2 (x : ℕ) :
    x ∈ solution_set ↔
    x^2 = 10 * x + 22 + (Nat.digits 10 x).prod := by
  constructor
  · rintro rfl; norm_num
  · intro hs
    sorry
