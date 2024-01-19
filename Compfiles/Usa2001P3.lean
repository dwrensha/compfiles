/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 2001, Problem 3

Let a,b,c ≥ 0 be real numbers satsifying

        a² + b² + c² + abc = 4.

Show that

        0 ≤ ab + bc + ca - abc ≤ 2.
-/

namespace Usa2001P3

problem usa2001_p3 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a^2 + b^2 + c^2 + a * b * c = 4) :
    0 ≤ a * b + b * c + c * a - a * b * c ∧
    a * b + b * c + c * a - a * b * c ≤ 2 := by
  sorry
