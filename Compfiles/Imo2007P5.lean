/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file

/-!
# International Mathematical Olympiad 2007, Problem 5

Let a and b be positive integers. Show that if 4ab - 1 divides (4a² - 1)²
then a = b.
-/

namespace Imo2007P5

problem imo2007_p5 (a b : ℤ) (ha : 0 < a) (hb : 0 < b)
    (hab : 4 * a * b - 1 ∣ (4 * a^2 - 1)^2) : a = b := by
  sorry
