/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdelmouksit SAGUENI
-/
module

public import Mathlib
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Geometry, .Inequality]
  problemImportedFrom :=
    "https://artofproblemsolving.com/wiki/index.php/1982_USAMO_Problems/Problem_3"
}

open Affine
open scoped Affine Real

namespace Usa1982P3

abbrev Point := EuclideanSpace ℝ (Fin 2)

/-!
# USA Mathematical Olympiad 1982, Problem 3

Let `ABC` be an equilateral triangle, and let `A₁` be an interior point of
`ABC`. If `A₂` is an interior point of triangle `A₁BC`, then the
isoperimetric quotient of `A₁BC` is greater than that of `A₂BC`.

The isoperimetric quotient is area divided by the square of perimeter.
-/

/-- The perimeter of the triangle with vertices `A`, `B`, and `C`. -/
def trianglePerimeter (A B C : Point) : ℝ :=
  dist A B + dist B C + dist C A

/-- The area of a triangle, expressed by Heron's formula. -/
noncomputable def triangleArea (A B C : Point) : ℝ :=
  let s := trianglePerimeter A B C / 2
  Real.sqrt (s * (s - dist A B) * (s - dist B C) * (s - dist C A))

/-- The area-to-squared-perimeter ratio of a triangle. -/
noncomputable def isoperimetricQuotient (A B C : Point) : ℝ :=
  triangleArea A B C / (trianglePerimeter A B C) ^ 2

problem usa1982_p3
    (A B C A₁ A₂ : Point)
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hEquilateral : dist A B = dist B C ∧ dist B C = dist C A)
    (hA₁ : A₁ ∈ interior (convexHull ℝ ({A, B, C} : Set Point)))
    (hA₂ : A₂ ∈ interior (convexHull ℝ ({A₁, B, C} : Set Point))) :
    isoperimetricQuotient A₁ B C >
      isoperimetricQuotient A₂ B C := by
  sorry

end Usa1982P3
