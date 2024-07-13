/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Sphere
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.Geometry.Euclidean.Triangle

import ProblemExtraction

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 2014, Problem 4

Let P and Q be on segment BC of an acute triangle ABC such that
∠PAB = ∠BCA and ∠CAQ = ∠ABC. Let M and N be points on lines AB
and AQ, respectively, such that P is the midpoint of AM and Q
is the midpoint of AN. Prove that BM and CN meet on the
circumcircle of triangle ABC.
-/

namespace Imo2014P4

open scoped EuclideanGeometry

problem imo2014_p4
    (A B C P Q M N : EuclideanSpace ℝ (Fin 2))
    (hABC : AffineIndependent ℝ ![A, B, C])
    (acuteA : ∠ C A B < Real.pi / 2)
    (acuteB : ∠ A B C < Real.pi / 2)
    (acuteC : ∠ B C A < Real.pi / 2)
    (hP : Sbtw ℝ P B C)
    (hQ : Sbtw ℝ Q B C)
    (hPAB : ∠ P A B = ∠ B C A)
    (hCAQ : ∠ C A Q = ∠ A B C)
    (hM : M ∈ line[ℝ, A, M])
    (hN : Q ∈ line[ℝ, A, N])
    (hPAM : P = midpoint ℝ A M)
    (hQAN : Q = midpoint ℝ A N)
    : let ABC : Affine.Triangle _ _ := ⟨![A, B, C], hABC⟩
      let D := (line[ℝ, B, M] : Set _) ∩ (line[ℝ, C, N] : Set (EuclideanSpace ℝ (Fin 2)))
      Set.Nonempty D ∧ D ⊆ Affine.Simplex.circumsphere ABC := by
  sorry


end Imo2014P4
