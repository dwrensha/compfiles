/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InternLM-MATH LEAN Formalizer v0.1
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1963, Problem 4

Find all solutions $x_1,x_2,x_3,x_4,x_5$ of the system

x_5+x_2&=&yx_1
x_1+x_3&=&yx_2
x_2+x_4&=&yx_3
x_3+x_5&=&yx_4
x_4+x_1&=&yx_5

where $y$ is a parameter.
-/

namespace Imo1963P4

determine solution_set : Set (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ) := sorry

problem imo1963_p4 (x : Fin 6 → ℝ) (y : ℝ)
  (hx0 : x 2 + x 5 = x 1 * y)
  (hx1 : x 1 + x 3 = x 2 * y)
  (hx2 : x 2 + x 4 = x 3 * y)
  (hx3 : x 3 + x 5 = x 4 * y)
  (hx4 : x 4 + x 1 = x 5 * y) :
    (y, x 1, x 2, x 3, x 4, x 5) ∈ solution_set := by sorry
