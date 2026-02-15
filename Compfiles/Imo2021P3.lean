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
    "https://github.com/jsm28/IMOLean/blob/main/IMO/IMO2021P3.lean"
}

/-!
# International Mathematical Olympiad 2021, Problem 3

Let D be an interior point of the acute triangle $ABC$ with
AB > AC so that ∠DAB = ∠CAD. The point E on the
segment AC satisfies ∠ADE = ∠BCD, the point F on
the segment AB satisfies ∠FDA = ∠DBC, and the point
X on the line AC satisfies CX = BX. Let O₁ and O₂ be
the circumcenters of the triangles ADC and EXD, respectively.
Prove that the lines BC, EF, and O₁O₂ are concurrent.
-/

open scoped EuclideanGeometry
open Affine Module

namespace Imo2021P3

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P] [Fact (finrank ℝ V = 2)]

problem imo2021_p3 {A B C D E F X O₁ O₂ : P}
    (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C])
    (acuteAngled_ABC : (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).AcuteAngled)
    (AC_lt_AB : dist A C < dist A B)
    (D_mem_interior_ABC : D ∈ (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).interior)
    (angle_DAB_eq_angle_CAD : ∠ D A B = ∠ C A D) (wbtw_A_E_C : Wbtw ℝ A E C)
    (angle_ADE_eq_angle_BCD : ∠ A D E = ∠ B C D) (wbtw_A_F_B : Wbtw ℝ A F B)
    (angle_FDA_eq_angle_DBC : ∠ F D A = ∠ D B C) (X_mem_AC : X ∈ line[ℝ, A, C])
    (CX_eq_BX : dist C X = dist B X)
    (affineIndependent_ADC : AffineIndependent ℝ ![A, D, C])
    (O₁_eq_circumcenter_ADC :
      O₁ = (⟨_, affineIndependent_ADC⟩ : Triangle ℝ P).circumcenter)
    (affineIndependent_EXD : AffineIndependent ℝ ![E, X, D])
    (O₂_eq_circumcenter_EXD :
      O₂ = (⟨_, affineIndependent_EXD⟩ : Triangle ℝ P).circumcenter) :
    E ≠ F ∧ O₁ ≠ O₂ ∧
    (line[ℝ, B, C] ∩ line[ℝ, E, F] ∩ line[ℝ, O₁, O₂] : Set P).Nonempty := by
  sorry

end Imo2021P3
