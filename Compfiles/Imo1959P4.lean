/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InternLM-MATH LEAN Formalizer v0.1. This is auto-formalized by InternLM-MATH LEAN Formalizer v0.1, modified and verified by InternLM-MATH team members.
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1959, Problem 4

Construct a right triangle with a given hypotenuse $c$ such that the median drawn to the hypotenuse is the geometric mean of the two legs of the triangle.
-/

namespace Imo1959P4

problem imo1959_p4 (c : ℝ) (hc : 0 < c) : ∃ a b : ℝ, a^2 + b^2 = c^2 ∧ a*b = c ^ 2 / 4 := by sorry