/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file

/-!
# USA Mathematical Olympiad 1993, Problem 1

For each integer n ≥ 2, determine whether a or b is larger,
where a and b are positive real numbers satisfying

            aⁿ = a + 1,     b²ⁿ = b + 3a.
-/

namespace Usa1993P1

determine a_is_larger : ℕ → Bool := sorry

problem usa1993_p5 (n : ℕ) (hn : 2 ≤ n) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (han : a^n = a + 1) (hbn : b^(2 * n) = b + 3 * a) :
    if a_is_larger n then b < a else a < b := by
  sorry
