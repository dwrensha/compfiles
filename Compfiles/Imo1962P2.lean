/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1962, Problem 2

Determine all real numbers x which satisfy

  √(3 - x) - √(x + 1) > 1/2.
-/

namespace Imo1962P2

determine solution_set : Set ℝ := sorry

problem imo1962_p2 (x : ℝ) :
    x ∈ solution_set ↔
    x ≤ 3 ∧ -1 ≤ x ∧ 1/2 < Real.sqrt (3 - x) - Real.sqrt (x + 1) := by
  sorry
