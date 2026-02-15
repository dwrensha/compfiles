/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib

import ProblemExtraction

problem_file {
  tags := [.Geometry]
  problemImportedFrom :=
    "https://github.com/jsm28/IMOLean/blob/main/IMO/IMO2025P2.lean"
}

/-!
# International Mathematical Olympiad 2025, Problem 2

Let Ω and Γ be circles with centres M and N, respectively, such that
the radius of Ω is less than the radius of Γ. Suppose Ω and Γ intersect
at two distinct points A and B. Line MN intersects Ω at C and Γ at D,
so that C, M, N, D lie on MN in that order. Let P be the circumcentre
of triangle ACD. Line AP meets Ω again at E ≠ A and meets Γ again at
F ≠ A. Let H be the orthocentre of triangle PMN.

Prove that the line through H parallel to AP is tangent to the circumcircle
of triangle BEF.
-/

open scoped Real
open Affine EuclideanGeometry Module

namespace Imo2025P2

variable {V Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt] [Fact (finrank ℝ V = 2)]

problem imo2025_p2 {M N A B C D P E F H : Pt} {Ω Γ : Sphere Pt}
    (Ω_center_eq_M : Ω.center = M) (Γ_center_eq_N : Γ.center = N)
    (Ω_radius_lt_Γ_radius : Ω.radius < Γ.radius)
    (A_mem_inter : A ∈ (Ω ∩ Γ : Set Pt)) (B_mem_inter : B ∈ (Ω ∩ Γ : Set Pt))
    (A_ne_B : A ≠ B) (M_ne_N : M ≠ N)
    (C_mem_inter : C ∈ (line[ℝ, M, N] ∩ Ω : Set Pt))
    (D_mem_inter : D ∈ (line[ℝ, M, N] ∩ Γ : Set Pt))
    (sbtw_C_M_N_D : [C, M, N, D].Sbtw ℝ)
    (affineIndependent_ACD : AffineIndependent ℝ ![A, C, D])
    (P_eq_circumcenter :
      P = (⟨_, affineIndependent_ACD⟩ : Triangle ℝ Pt).circumcenter)
    (E_mem_inter : E ∈ (line[ℝ, A, P] ∩ Ω : Set Pt)) (E_ne_A : E ≠ A)
    (F_mem_inter : F ∈ (line[ℝ, A, P] ∩ Γ : Set Pt)) (F_ne_A : F ≠ A)
    (affineIndependent_PMN : AffineIndependent ℝ ![P, M, N])
    (H_eq_orthocenter :
      H = Triangle.orthocenter (⟨_, affineIndependent_PMN⟩ : Triangle ℝ Pt)) :
    ∃ affineIndependent_BEF : AffineIndependent ℝ ![B, E, F],
      (⟨_, affineIndependent_BEF⟩ : Triangle ℝ Pt).circumsphere.IsTangent
        (AffineSubspace.mk' H line[ℝ, A, P].direction) := by
  sorry

end Imo2025P2
