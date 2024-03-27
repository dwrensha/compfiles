/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra, .Inequality] }

/-!
# USA Mathematical Olympiad 1980, Problem 5

Let x,y,z be real numbers in the closed interval [0,1]. Show that

 x/(y + z + 1) + y/(z + x + 1) + z/(x + y + 1) ≤ 1 + (1 - x)(1 - y)(1 - z).
-/

namespace Usa1980P5

problem usa1980_p5 (x y z : ℝ)
    (hx : x ∈ Set.Icc 0 1)
    (hy : y ∈ Set.Icc 0 1)
    (hz : z ∈ Set.Icc 0 1) :
    x / (y + z + 1) + y / (z + x + 1) + z / (x + y + 1) ≤
    1 + (1 - x) * (1 - y) * (1 - z) := by
  sorry
