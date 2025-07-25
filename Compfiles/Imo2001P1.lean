/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Geometry.Euclidean.Circumcenter
import Mathlib.Geometry.Euclidean.Triangle

import ProblemExtraction

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 2001, Problem 1

Let ABC be an acute-angled triangle with O as its circumcenter. Let P
on line BC be the foot of the altitude from A. Assume that
∠BCA ≥ ∠ABC + 30°. Prove that ∠CAB + ∠COP < 90°.
-/

namespace Imo2001P1

open scoped EuclideanGeometry

snip begin

-- We need some instances in order to talk about oriented angles.

local instance planeFiniteDim :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
  ⟨finrank_euclideanSpace_fin⟩

noncomputable local instance someOrientation :
    Module.Oriented ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2) :=
  ⟨Module.Basis.orientation (Module.finBasisOfFinrankEq _ _ planeFiniteDim.out)⟩

lemma lemma1
    (t : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)))
    : ∡ t.circumcenter (t.points 2) (t.points 1) =
      Real.pi - ∡ (t.points 1) (t.points 0) (t.points 2) := by
  sorry

snip end

problem imo2001_p1
    (A B C : EuclideanSpace ℝ (Fin 2))
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hAcuteA : ∠ C A B < Real.pi / 2)
    (hAcuteB : ∠ A B C < Real.pi / 2)
    (hAcuteC : ∠ B C A < Real.pi / 2)
    (hAB : ∠ A B C + Real.pi / 6 ≤ ∠ B C A)
    : let ABC : Affine.Triangle _ _ := ⟨![A, B, C], hABC⟩
      let P := EuclideanGeometry.orthogonalProjection line[ℝ, B, C] A
      ∠ C A B + ∠ C ABC.circumcenter P < Real.pi / 2 := by
  intro ABC P
  sorry


end Imo2001P1
