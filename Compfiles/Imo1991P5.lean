/-
Copyright (c) 2025 The Compfiles Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib

import ProblemExtraction

problem_file {
  tags := [.Geometry]
}

/-!
# International Mathematical Olympiad 1991, Problem 5

Let ABC be a triangle and P be an interior point of ABC.
Show that at least one of the angles ∠PAB, ∠PBC, ∠PCA is
less than or equal to 30°.

-/

namespace Imo1991P5

open scoped Affine EuclideanGeometry Real

problem imo1991_p5
    (A B C P : EuclideanSpace ℝ (Fin 2))
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C})) :
    ∠ P A B ≤ π / 6 ∨ ∠ P B C ≤ π / 6 ∨ ∠ P C A ≤ π / 6 := by
  sorry

end Imo1991P5
