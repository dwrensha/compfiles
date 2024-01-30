/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 2002, Problem 5

Determine all functions f : ℝ → ℝ such that

  (f(x) + f(z))(f(y) + f(t)) = f(xy - zt) + f(xt + yz)

for all real numbers x,y,z,t.
-/

namespace Imo2002P5

determine solution_set : Set (ℝ → ℝ) := sorry

problem imo2002_p5 (f : ℝ → ℝ) :
    f ∈ solution_set ↔
    ∀ x y z t, (f x + f z) * (f y + f t) =
               f (x * y - z * t) + f (x * t + y * z) := by
  sorry
