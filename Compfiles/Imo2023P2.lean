/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
import Mathlib.Geometry.Euclidean.Angle.Sphere
import Mathlib.Geometry.Euclidean.Sphere.SecondInter

import ProblemExtraction

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 2023, Problem 2

Let ABC be an acute-angled triangle with AB < AC.
Let Ω be the circumcircle of ABC.
Let S be the midpoint of the arc CB of Ω containing A.
The perpendicular from A to BC meets BS at D and meets Ω again at E ≠ A.
The line through D parallel to BC meets line BE at L.
Denote the circumcircle of triangle BDL by ω.
Let ω meet Ω again at P ≠ B.
Prove that the line tangent to ω at P meets line BS on the internal angle bisector of ∠BAC.
-/

open Affine Affine.Simplex EuclideanGeometry FiniteDimensional

open scoped Affine EuclideanGeometry Real InnerProductSpace

set_option linter.uppercaseLean3 false

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable (V : Type*) (Pt : Type*)

variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]

variable [NormedAddTorsor V Pt] [hd2 : Fact (finrank ℝ V = 2)]

variable [Module.Oriented ℝ V (Fin 2)]

def acute (A B C : Pt) : Prop :=
  ∠ A B C < π / 2 ∧ ∠ B C A < π / 2 ∧ ∠ C A B < π / 2

def perp_to (l : AffineSubspace ℝ Pt) (m : AffineSubspace ℝ Pt) : Prop :=
  ∀ x ∈ l.direction, ∀ y ∈ m.direction, ⟪x, y⟫_ℝ = 0

/-- A space is tangent to a sphere if it intersects it at exactly one point -/
def is_tangent (L : AffineSubspace ℝ Pt) (ω : Sphere Pt) : Prop :=
  ∃! P : Pt, P ∈ (ω : Set Pt) ∧ P ∈ L

namespace Imo2023P2

problem imo2023_p1
  -- Points
  ( A B C D E L S P : Pt )
  -- Circles
  ( Ω ω : Sphere Pt )
  -- Lines
  ( perp_A_BC prll_D_BC tang_P_ω : AffineSubspace ℝ Pt )
  -- Let ABC be an acute-angled triangle
  ( h_acute_ABC : acute V Pt A B C )
  -- with AB < AC.
  ( h_AB_lt_BC : dist A B < dist A C )
  -- Let Ω be the circumcircle of ABC.
  ( h_Ω : {A, B, C} ⊆ (Ω : Set Pt) )
  -- Let S be the midpoint of the arc CB of Ω
  ( h_S_Ω : dist S C = dist S B ∧ S ∈ (Ω : Set Pt))
  -- ... containing A.
  (h_S_A : (∡ C B S).sign = (∡ C B A).sign)
  -- The perpendicular from A to BC ...
  (h_perp_A_BC : perp_to V Pt perp_A_BC (affineSpan ℝ {B, C}) ∧ A ∈ perp_A_BC)
  -- ... meets BS at D
  ( h_D : D ∈ (perp_A_BC : Set Pt) ∩ (affineSpan ℝ {B, S}) )
  -- ... and meets Ω again at E ...
  ( h_E : E ∈ (perp_A_BC : Set Pt) ∩ Ω )
  -- ... E ≠ A.
  ( h_E_ne_A : E ≠ A )
  -- The line through D parallel to BC ...
  ( h_prll_D_BC : D ∈ prll_D_BC ∧ AffineSubspace.Parallel prll_D_BC (affineSpan ℝ {B, C}))
  --- ... meets line BE at L.
  ( h_L : L ∈ (prll_D_BC : Set Pt) ∩ affineSpan ℝ {B, E} )
  -- Denote the circumcircle of triangle BDL by ω.
  ( h_ω : {B, D, L} ⊆ (ω : Set Pt) )
  -- Let ω meet Ω again at P ...
  ( h_P : P ∈ (ω : Set Pt) ∩ Ω )
  -- P ≠ B.
  ( h_P_ne_B : P ≠ B )
  -- Prove that the line tangent to ω at P ...
  ( h_tang_P_ω : is_tangent V Pt tang_P_ω ω ∧ P ∈ tang_P_ω) :
  -- meets line BS on the internal angle bisector of ∠BAC.
  ∃ X : Pt,
    X ∈ (tang_P_ω : Set Pt) ∩ affineSpan ℝ {B, S}
    ∧ ∠ B A X = ∠ X A C
    ∧ ∠ B A X < π / 2 := by sorry
