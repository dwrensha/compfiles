/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file

/-!
# USA Mathematical Olympiad 1987, Problem 1

Determine all solutions to

     (m² + n)(m + n²) = (m - n)³

where m and n are non-zero integers.
-/

namespace Usa1987P1

determine solution_set : Set (ℤ × ℤ) := sorry

problem usa2001_p1 (m n : ℤ) :
    (m, n) ∈ solution_set ↔
    m ≠ 0 ∧ n ≠ 0 ∧ (m^2 + n) * (m + n^2) = (m - n)^3 := by
  sorry
