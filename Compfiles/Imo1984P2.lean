/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 1984, Problem 2

Find a pair of positive integers a and b such that

 (i) ab(a + b) is not divisible by 7.
 (ii) (a + b)⁷ - a⁷ - b⁷ is divisible by 7⁷.
-/

namespace Imo1984P2

determine a : ℤ := 18
determine b : ℤ := 1

problem imo1984_p2 :
    (0 < a) ∧ (0 < b) ∧
    (¬ 7 ∣ a * b * (a + b)) ∧
    7^7 ∣ (a + b)^7 - a^7 - b^7 := by
  decide
