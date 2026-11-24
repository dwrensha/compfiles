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

open Affine FiniteDimensional Module
open scoped Affine Real

namespace Usa1982P3

variable {V P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [MetricSpace P] [NormedAddTorsor V P]
variable [Fact (finrank ℝ V = 2)]

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

/-!
# USA Mathematical Olympiad 1982, Problem 3

Let `ABC` be an equilateral triangle, and let `A₁` be an interior point
of `ABC`. If `A₂` is an interior point of triangle `A₁BC`, then the
isoperimetric quotient of `A₁BC` is greater than that of `A₂BC`.
-/

/-- The perimeter of the triangle with vertices `A`, `B`, and `C`. -/
def trianglePerimeter (A B C : P) : ℝ :=
  dist A B + dist B C + dist C A

/-- Triangle area, expressed using Heron's formula. -/
noncomputable def triangleArea (A B C : P) : ℝ :=
  let s := trianglePerimeter A B C / 2
  Real.sqrt (s * (s - dist A B) * (s - dist B C) * (s - dist C A))

/-- Area divided by the square of the perimeter. -/
noncomputable def isoperimetricQuotient (A B C : P) : ℝ :=
  triangleArea A B C / (trianglePerimeter A B C) ^ 2

problem usa1982_p3
    (A B C A₁ A₂ : P)
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hEquilateral : dist A B = dist B C ∧ dist B C = dist C A)
    (hA₁ : A₁ ∈ interior (convexHull ℝ ({A, B, C} : Set P)))
    (hA₂ : A₂ ∈ interior (convexHull ℝ ({A₁, B, C} : Set P))) :
    isoperimetricQuotient A₁ B C >
      isoperimetricQuotient A₂ B C := by
  sorry

end Usa1982P3
