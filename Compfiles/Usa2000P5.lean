/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.Geometry.Euclidean.Triangle

import ProblemExtraction

problem_file { tags := [.Geometry] }

/-!
# Usa Mathematical Olympiad 2000, Problem 5

Let A₁A₂A₃ be a triangle, and let ω₁ be a circle in its plane
passing through A₁ and A₂. Suppose there exist circles ω₂,ω₃,⋯,ω₇
such that for k=2,3,⋯,7, circle ωₖ is externally tangent to ωₖ₋₁
and passes through Aₖ and Aₖ₊₁ (indices mod 3).

Prove that ω₇ = ω₁.
-/

namespace Imo2000P5

open scoped EuclideanGeometry

abbrev Circle := EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2))

def ExternallyTangent (c1 c2 : Circle) : Prop :=
  dist c1.center c2.center = c1.radius + c2.radius

problem imo2000_p5
    (A : ZMod 3 → EuclideanSpace ℝ (Fin 2))
    (hABC : AffineIndependent ℝ ![A 0, A 1, A 2])
    (ω : Fin 7 → Circle)
    (hTangent : ∀ i, i < 6 → ExternallyTangent (ω i) (ω (i + 1)))
    (hA : ∀ i : ℕ, i < 7 → (A i ∈ ω i ∧ A (i + 1) ∈ ω i))
    : ω 0 = ω 6 := by
  sorry


end Imo2000P5
