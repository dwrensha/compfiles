/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra, .Inequality] }

/-!
# International Mathematical Olympiad 2000, Problem 2

Let a, b, c be real numbers such that abc = 1. Show that

    (a - 1 + 1/b)(b - 1 + 1/c)(c - 1 + 1/a) ≤ 1.
-/

namespace Imo2000P2

problem imo2000_p2 (a b c : ℝ) (habc : a * b * c = 1) :
    (a - 1 + 1 / b) * ( b - 1 + 1 / c) * (c - 1 + 1 / a) ≤ 1 := by
  sorry
