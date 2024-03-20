/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra, .Inequality] }

/-!
# International Mathematical Olympiad 1964, Problem 2

Suppose that a,b,c are the side lengths of a triangle. Prove that

   a²(b + c - a) + b²(c + a - b) + c²(a + b - c) ≤ 3abc.
-/

namespace Imo1964P2

abbrev Pt := EuclideanSpace ℝ (Fin 2)

problem imo1964_p2
    (T : Affine.Triangle ℝ Pt)
    (a b c : ℝ)
    (ha : a = dist (T.points 1) (T.points 2))
    (hb : b = dist (T.points 2) (T.points 0))
    (hb : c = dist (T.points 0) (T.points 1)) :
    a^2 * (b + c - a) + b^2 * (c + a - b) + c^2 * (a + b - c) ≤
    3 * a * b * c := by
  sorry
