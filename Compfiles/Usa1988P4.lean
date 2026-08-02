/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karl Mehltretter, Kimi K3
-/

module

public import Mathlib.Geometry.Euclidean.Incenter
public import Mathlib.Geometry.Euclidean.Circumcenter
public import Mathlib.Geometry.Euclidean.Triangle
public import Mathlib.Geometry.Euclidean.Angle.Incenter
public import Mathlib.Geometry.Euclidean.Angle.Sphere
public import Mathlib.Tactic.Module
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 1988, Problem 4

ABC is a triangle with incenter I. Show that the circumcenters
of triangles IAB, IBC, and ICA lie on a circle whose center is
the circumcenter of triangle ABC.
-/

open scoped EuclideanGeometry Real
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

/-- The circumcenter of the triangle formed by the incenter of a triangle and two of its
vertices lies on the circumsphere of the triangle. This is the key step: by the central
angle theorem, twice the oriented angle at that circumcenter equals twice the oriented
angle at the third vertex, so the inscribed angle theorem converse applies. -/
theorem circumcenter_incenter_pair_mem_circumsphere {X Y Z : P}
    (hXYZ : AffineIndependent ℝ ![X, Y, Z]) (J : P)
    (hJ : J = (⟨![X, Y, Z], hXYZ⟩ : Triangle ℝ P).incenter)
    (hJXY : AffineIndependent ℝ ![J, X, Y]) :
    (⟨![J, X, Y], hJXY⟩ : Triangle ℝ P).circumcenter ∈
      (⟨![X, Y, Z], hXYZ⟩ : Triangle ℝ P).circumsphere := by
  subst hJ
  letI : FiniteDimensional ℝ V := FiniteDimensional.of_fact_finrank_eq_two
  letI : Module.Oriented ℝ V (Fin 2) :=
    ⟨Basis.orientation (finBasisOfFinrankEq ℝ V (Fact.out : finrank ℝ V = 2))⟩
  set T : Triangle ℝ P := ⟨![X, Y, Z], hXYZ⟩
  set S : Triangle ℝ P := ⟨![T.incenter, X, Y], hJXY⟩
  -- distinctness of the relevant points
  have hXY : X ≠ Y := hXYZ.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hXZ : X ≠ Z := hXYZ.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hZY : Z ≠ Y := (hXYZ.injective.ne (show (1 : Fin 3) ≠ 2 by decide)).symm
  have hJX : T.incenter ≠ X := hJXY.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hJY : T.incenter ≠ Y := hJXY.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  -- the central angle at the circumcenter of `(J, X, Y)` is twice the angle at `J`
  have hCA : ∡ X S.circumcenter Y = (2 : ℤ) • ∡ X T.incenter Y := by
    rw [← Affine.Simplex.circumsphere_center S]
    exact EuclideanGeometry.Sphere.oangle_center_eq_two_zsmul_oangle
      (S.mem_circumsphere 1) (S.mem_circumsphere 0) (S.mem_circumsphere 2) hJX hJY
  -- the incenter bisects the angles of `T` at `X` and at `Y`
  have bX : ∡ Z X T.incenter = ∡ T.incenter X Y :=
    Affine.Triangle.oangle_incenter_eq (t := T) (i₁ := 0) (i₂ := 2) (i₃ := 1)
      (by decide) (by decide) (by decide)
  have bY : ∡ X Y T.incenter = ∡ T.incenter Y Z :=
    Affine.Triangle.oangle_incenter_eq (t := T) (i₁ := 1) (i₂ := 0) (i₃ := 2)
      (by decide) (by decide) (by decide)
  -- angle sums in the triangles `(X, J, Y)` and `(Z, X, Y)`
  have e1 : ∡ X T.incenter Y + ∡ T.incenter Y X + ∡ Y X T.incenter = π :=
    EuclideanGeometry.oangle_add_oangle_add_oangle_eq_pi hJX hJY.symm hXY
  have e2 : ∡ Z X Y + ∡ X Y Z + ∡ Y Z X = π :=
    EuclideanGeometry.oangle_add_oangle_add_oangle_eq_pi hXZ hXY.symm hZY
  -- splitting the angles of `T` at `X` and `Y` along the bisector
  have sX : ∡ Z X T.incenter + ∡ T.incenter X Y = ∡ Z X Y :=
    EuclideanGeometry.oangle_add hXZ.symm hJX hXY.symm
  have sY : ∡ X Y T.incenter + ∡ T.incenter Y Z = ∡ X Y Z :=
    EuclideanGeometry.oangle_add hXY hJY hZY
  -- the oriented-angle chase, carried out in the `ℤ`-module `Real.Angle`
  have hpi : (2 : ℤ) • (π : Real.Angle) = 0 := Real.Angle.two_zsmul_coe_pi
  have r1 : ∡ Y X T.incenter = -∡ T.incenter X Y := EuclideanGeometry.oangle_rev _ _ _
  have r2 : ∡ T.incenter Y X = -∡ X Y T.incenter := EuclideanGeometry.oangle_rev _ _ _
  have r3 : ∡ X Z Y = -∡ Y Z X := EuclideanGeometry.oangle_rev _ _ _
  have e1d : (2 : ℤ) • ∡ X T.incenter Y =
      (2 : ℤ) • ∡ T.incenter X Y + (2 : ℤ) • ∡ X Y T.incenter := by
    have h := congrArg ((2 : ℤ) • ·) e1
    rw [hpi, r1, r2] at h
    have h' : (2 : ℤ) • (∡ X T.incenter Y + -∡ X Y T.incenter + -∡ T.incenter X Y) =
        (2 : ℤ) • ∡ X T.incenter Y +
          -((2 : ℤ) • ∡ T.incenter X Y + (2 : ℤ) • ∡ X Y T.incenter) := by
      module
    rw [h'] at h
    exact eq_of_sub_eq_zero (by rw [sub_eq_add_neg]; exact h)
  have hf : (2 : ℤ) • ∡ Z X Y = (2 : ℤ) • ((2 : ℤ) • ∡ T.incenter X Y) := by
    have h := congrArg ((2 : ℤ) • ·) sX
    rw [bX] at h
    rw [← h]
    module
  have hg : (2 : ℤ) • ∡ X Y Z = (2 : ℤ) • ((2 : ℤ) • ∡ X Y T.incenter) := by
    have h := congrArg ((2 : ℤ) • ·) sY
    rw [← bY] at h
    rw [← h]
    module
  have e2d : (2 : ℤ) • ∡ Y Z X =
      -((2 : ℤ) • ((2 : ℤ) • ∡ T.incenter X Y) +
        (2 : ℤ) • ((2 : ℤ) • ∡ X Y T.incenter)) := by
    have h := congrArg ((2 : ℤ) • ·) e2
    have h' : (2 : ℤ) • (∡ Z X Y + ∡ X Y Z + ∡ Y Z X) =
        (2 : ℤ) • ∡ Z X Y + (2 : ℤ) • ∡ X Y Z + (2 : ℤ) • ∡ Y Z X := by
      module
    rw [hpi, h', hf, hg] at h
    exact eq_neg_of_add_eq_zero_right h
  have key : (2 : ℤ) • ∡ X S.circumcenter Y = (2 : ℤ) • ∡ X Z Y := by
    rw [hCA, e1d, r3, zsmul_neg, e2d]
    module
  exact Affine.Triangle.mem_circumsphere_of_two_zsmul_oangle_eq
    (t := T) (p := S.circumcenter) (i₁ := 0) (i₂ := 2) (i₃ := 1)
    (by decide) (by decide) (by decide) key

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
  -- cyclic rotations of the index set
  let e₁ : Fin 3 ≃ Fin 3 := ⟨![2, 0, 1], ![1, 2, 0], by decide, by decide⟩
  let e₂ : Fin 3 ≃ Fin 3 := ⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩
  have hBCA : AffineIndependent ℝ ![B, C, A] := by
    have h := (affineIndependent_equiv e₁.symm).2 hABC
    rwa [show (![A, B, C] ∘ ⇑e₁.symm) = ![B, C, A] from by
      funext i; fin_cases i <;> rfl] at h
  have hCAB : AffineIndependent ℝ ![C, A, B] := by
    have h := (affineIndependent_equiv e₂.symm).2 hABC
    rwa [show (![A, B, C] ∘ ⇑e₂.symm) = ![C, A, B] from by
      funext i; fin_cases i <;> rfl] at h
  -- the rotated triangles are reindexings of the original triangle
  have hT2 : (⟨![B, C, A], hBCA⟩ : Triangle ℝ P)
      = (⟨![A, B, C], hABC⟩ : Triangle ℝ P).reindex e₁ :=
    (Affine.Simplex.ext fun i => by fin_cases i <;> rfl).symm
  have hT3 : (⟨![C, A, B], hCAB⟩ : Triangle ℝ P)
      = (⟨![A, B, C], hABC⟩ : Triangle ℝ P).reindex e₂ :=
    (Affine.Simplex.ext fun i => by fin_cases i <;> rfl).symm
  -- hence their incenters and circumspheres agree with those of `ABC`
  have hI2 : (⟨![B, C, A], hBCA⟩ : Triangle ℝ P).incenter
      = (⟨![A, B, C], hABC⟩ : Triangle ℝ P).incenter := by
    rw [hT2, Affine.Simplex.incenter_reindex]
  have hI3 : (⟨![C, A, B], hCAB⟩ : Triangle ℝ P).incenter
      = (⟨![A, B, C], hABC⟩ : Triangle ℝ P).incenter := by
    rw [hT3, Affine.Simplex.incenter_reindex]
  have hS2 : (⟨![B, C, A], hBCA⟩ : Triangle ℝ P).circumsphere
      = (⟨![A, B, C], hABC⟩ : Triangle ℝ P).circumsphere := by
    rw [hT2, Affine.Simplex.circumsphere_reindex]
  have hS3 : (⟨![C, A, B], hCAB⟩ : Triangle ℝ P).circumsphere
      = (⟨![A, B, C], hABC⟩ : Triangle ℝ P).circumsphere := by
    rw [hT3, Affine.Simplex.circumsphere_reindex]
  -- apply the key lemma to the three rotations
  have k1 : O (I A B C hABC) A B hIAB ∈
      (⟨![A, B, C], hABC⟩ : Triangle ℝ P).circumsphere :=
    circumcenter_incenter_pair_mem_circumsphere hABC (I A B C hABC) rfl hIAB
  have k2 : O (I A B C hABC) B C hIBC ∈
      (⟨![A, B, C], hABC⟩ : Triangle ℝ P).circumsphere := by
    have h := circumcenter_incenter_pair_mem_circumsphere hBCA (I A B C hABC)
      (by rw [hI2]) hIBC
    rwa [hS2] at h
  have k3 : O (I A B C hABC) C A hICA ∈
      (⟨![A, B, C], hABC⟩ : Triangle ℝ P).circumsphere := by
    have h := circumcenter_incenter_pair_mem_circumsphere hCAB (I A B C hABC)
      (by rw [hI3]) hICA
    rwa [hS3] at h
  -- the circle is the circumsphere of `ABC` itself
  exact ⟨(⟨![A, B, C], hABC⟩ : Triangle ℝ P).circumsphere,
    Affine.Simplex.circumradius_pos _, rfl, k1, k2, k3⟩

end Usa1988P4
