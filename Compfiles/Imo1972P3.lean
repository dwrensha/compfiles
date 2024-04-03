/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 1972, Problem 3

Let m and n be non-negative integers. Prove that

     (2m)!(2n)! / (m!n!(m + n)!)

is an integer.
-/

namespace Imo1972P3

open scoped Nat

problem imo1972_p3 (m n : ℕ) :
    m ! * n ! * (m + n)! ∣ (2 * m)! * (2 * n)! := by
  sorry
