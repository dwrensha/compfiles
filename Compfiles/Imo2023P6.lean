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
    "https://github.com/jsm28/IMOLean/blob/main/IMO/IMO2023P6.lean"
}

/-!
# International Mathematical Olympiad 2023, Problem 6

Let ABC be an equilateral triangle. Let A₁,B₁,C₁ be interior points of
ABC such that BA₁=A₁C, CB₁ = B₁A, AC₁=C₁B, and

      ∠BA₁C + ∠CB₁A + ∠C₁B = 480°.

Let BC₁ and CB₁ meet at A₂, let CA₁ and AC₁ meet at B₂, and let AB₁ and
BA₁ meet at $C₂.

Prove that if triangle A₁B₁C₁ is scalene, then the three circumcircles
of triangles AA₁A₂, BB₁B₂ and CC₁C₂ all pass through two common points.
-/

open scoped Cardinal EuclideanGeometry Real
open Affine Module

namespace Imo2023P6

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P] [Fact (finrank ℝ V = 2)]

problem imo2023_p6 {A B C A₁ B₁ C₁ A₂ B₂ C₂ : P}
    (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C])
    (equilateral_ABC : (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).Equilateral)
    (A₁_mem_interior_ABC : A₁ ∈ (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).interior)
    (B₁_mem_interior_ABC : B₁ ∈ (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).interior)
    (C₁_mem_interior_ABC : C₁ ∈ (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).interior)
    (BA₁_eq_A₁C : dist B A₁ = dist A₁ C) (CB₁_eq_B₁A : dist C B₁ = dist B₁ A)
    (AC₁_eq_C₁B : dist A C₁ = dist C₁ B)
    (angle_BA₁C_add_angle_CB₁A_add_angle_AC₁B :
      ∠ B A₁ C + ∠ C B₁ A + ∠ A C₁ B = 8 / 3 * π)
    (A₂_mem_inf_BC₁_CB₁ : A₂ ∈ line[ℝ, B, C₁] ⊓ line[ℝ, C, B₁])
    (B₂_mem_inf_CA₁_AC₁ : B₂ ∈ line[ℝ, C, A₁] ⊓ line[ℝ, A, C₁])
    (C₂_mem_inf_AB₁_BA₁ : C₂ ∈ line[ℝ, A, B₁] ⊓ line[ℝ, B, A₁])
    (affineIndependent_A₁B₁C₁ : AffineIndependent ℝ ![A₁, B₁, C₁])
    (scalene_A₁B₁C₁ : (⟨_, affineIndependent_A₁B₁C₁⟩ : Triangle ℝ P).Scalene) :
    ∃ affineIndependent_AA₁A₂ : AffineIndependent ℝ ![A, A₁, A₂],
    ∃ affineIndependent_BB₁B₂ : AffineIndependent ℝ ![B, B₁, B₂],
    ∃ affineIndependent_CC₁C₂ : AffineIndependent ℝ ![C, C₁, C₂],
    2 ≤ #((⟨_, affineIndependent_AA₁A₂⟩ : Triangle ℝ P).circumsphere ∩
          (⟨_, affineIndependent_BB₁B₂⟩ : Triangle ℝ P).circumsphere ∩
          (⟨_, affineIndependent_CC₁C₂⟩ : Triangle ℝ P).circumsphere : Set P) := by
  sorry

end Imo2023P6
