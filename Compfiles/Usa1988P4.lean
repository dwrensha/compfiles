/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karl Mehltretter
-/

import Mathlib.Geometry.Euclidean.Incenter
import Mathlib.Geometry.Euclidean.Circumcenter
import Mathlib.Geometry.Euclidean.Triangle

import ProblemExtraction

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 1988, Problem 4

ABC is a triangle with incenter I. Show that the circumcenters
of triangles IAB, IBC, and ICA lie on a circle whose center is
the circumcenter of triangle ABC.
-/

open scoped EuclideanGeometry
open Affine Module

namespace Usa1988P4

variable {V P : Type*} [NormedAddCommGroup V]
variable [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P] [Fact (finrank ℝ V = 2)]

noncomputable abbrev I (A B C : P)
    (hABC : AffineIndependent ℝ ![A, B, C]) : P :=
  (⟨![A, B, C], hABC⟩ : Triangle ℝ P).incenter

noncomputable abbrev O (A B C : P)
    (hABC : AffineIndependent ℝ ![A, B, C]) : P :=
  (⟨![A, B, C], hABC⟩ : Triangle ℝ P).circumcenter

problem usa1988_p4 (A B C : P)
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hIAB : AffineIndependent ℝ ![I A B C hABC, A, B])
    (hIBC : AffineIndependent ℝ ![I A B C hABC, B, C])
    (hICA : AffineIndependent ℝ ![I A B C hABC, C, A]) :
    ∃ ω : EuclideanGeometry.Sphere P,
      0 < ω.radius ∧
        ω.center = O A B C hABC ∧
        O (I A B C hABC) A B hIAB ∈ ω ∧
        O (I A B C hABC) B C hIBC ∈ ω ∧
        O (I A B C hABC) C A hICA ∈ ω := by
  sorry

end Usa1988P4
