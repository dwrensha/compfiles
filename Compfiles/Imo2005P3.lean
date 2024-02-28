/-
Copyright (c) 2021 Manuel Candales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Candales
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

import ProblemExtraction

problem_file {
  tags := [.Algebra],
  importedFrom :=
    "https://github.com/leanprover-community/mathlib4/blob/master/Archive/Imo/Imo2005P3.lean",
}

/-!
# International Mathematical Olympiad 2005, Problem 3
Let `x`, `y` and `z` be positive real numbers such that `xyz ≥ 1`. Prove that:
`(x^5 - x^2)/(x^5 + y^2 + z^2) + (y^5 - y^2)/(y^5 + z^2 + x^2) + (z^5 - z^2)/(z^5 + x^2 + y^2) ≥ 0`
-/

namespace Imo2005P3

snip begin

/-
# Solution
The solution by Iurie Boreico from Moldova is presented, which won a special prize during the exam.
The key insight is that `(x^5-x^2)/(x^5+y^2+z^2) ≥ (x^2-y*z)/(x^2+y^2+z^2)`, which is proven by
factoring `(x^5-x^2)/(x^5+y^2+z^2) - (x^5-x^2)/(x^3*(x^2+y^2+z^2))` into a non-negative expression
and then making use of `xyz ≥ 1` to show `(x^5-x^2)/(x^3*(x^2+y^2+z^2)) ≥ (x^2-y*z)/(x^2+y^2+z^2)`.
-/

theorem key_insight (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (h : x * y * z ≥ 1) :
    (x ^ 5 - x ^ 2) / (x ^ 5 + y ^ 2 + z ^ 2) ≥ (x ^ 2 - y * z) / (x ^ 2 + y ^ 2 + z ^ 2) := by
  have key :
    (x ^ 5 - x ^ 2) / (x ^ 5 + y ^ 2 + z ^ 2) -
        (x ^ 5 - x ^ 2 * 1) / (x ^ 3 * (x ^ 2 + y ^ 2 + z ^ 2)) =
      (x ^ 3 - 1) ^ 2 * x ^ 2 * (y ^ 2 + z ^ 2) /
        ((x ^ 5 + y ^ 2 + z ^ 2) * (x ^ 3 * (x ^ 2 + y ^ 2 + z ^ 2))) := by
    field_simp
    ring
  have h₅ :
    (x ^ 3 - 1) ^ 2 * x ^ 2 * (y ^ 2 + z ^ 2) /
        ((x ^ 5 + y ^ 2 + z ^ 2) * (x ^ 3 * (x ^ 2 + y ^ 2 + z ^ 2))) ≥ 0 := by positivity
  calc
    (x ^ 5 - x ^ 2) / (x ^ 5 + y ^ 2 + z ^ 2)
      ≥ (x ^ 5 - x ^ 2 * 1) / (x ^ 3 * (x ^ 2 + y ^ 2 + z ^ 2)) := by linarith only [key, h₅]
    _ ≥ (x ^ 5 - x ^ 2 * (x * y * z)) / (x ^ 3 * (x ^ 2 + y ^ 2 + z ^ 2)) := by gcongr
    _ = (x ^ 2 - y * z) / (x ^ 2 + y ^ 2 + z ^ 2) := by field_simp; ring

snip end

problem imo2005_p3 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (h : x * y * z ≥ 1) :
    (x ^ 5 - x ^ 2) / (x ^ 5 + y ^ 2 + z ^ 2) + (y ^ 5 - y ^ 2) / (y ^ 5 + z ^ 2 + x ^ 2) +
        (z ^ 5 - z ^ 2) / (z ^ 5 + x ^ 2 + y ^ 2) ≥
      0 := by
  calc
    (x ^ 5 - x ^ 2) / (x ^ 5 + y ^ 2 + z ^ 2) + (y ^ 5 - y ^ 2) / (y ^ 5 + z ^ 2 + x ^ 2) +
          (z ^ 5 - z ^ 2) / (z ^ 5 + x ^ 2 + y ^ 2) ≥
        (x ^ 2 - y * z) / (x ^ 2 + y ^ 2 + z ^ 2) + (y ^ 2 - z * x) / (y ^ 2 + z ^ 2 + x ^ 2) +
          (z ^ 2 - x * y) / (z ^ 2 + x ^ 2 + y ^ 2) := by
      gcongr ?_ + ?_ + ?_ <;> apply key_insight <;> linarith
    _ = 1 / 2 * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) / (x ^ 2 + y ^ 2 + z ^ 2) := by ring
    _ ≥ 0 := by positivity
