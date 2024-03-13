/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra, .Inequality] }

/-!
# International Mathematical Olympiad 1995, Problem 2

Let a, b, c be positive real numbers such that abc = 1. Show that

    1 / (a³(b + c)) + 1 / (b³(c + a)) + 1 / (c³(a + b)) ≥ 3/2.
-/

namespace Imo1995P2

problem imo1995_p2 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    3 / 2 ≤ 1 / (a^3 * (b + c)) + 1 / (b^3 * (c + a)) + 1 / (c^3 * (a + b)) := by
  sorry
