/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Geometry.Euclidean.Angle.Sphere
public import Mathlib.Geometry.Euclidean.Sphere.Ptolemy
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 1994, Problem 3

The hexagon ABCDEF has the following properties: (1) its vertices lie on a
circle; (2) AB = CD = EF; and (3) the diagonals AD, BE, CF meet at a point.
Let X be the intersection of AD and CE. Show that CX/XE = (AC/CE)².
-/

namespace Usa1994P3

open EuclideanGeometry Real
open scoped EuclideanGeometry

snip begin

local instance planeFiniteDim :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
  ⟨finrank_euclideanSpace_fin⟩

noncomputable local instance someOrientation :
    Module.Oriented ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2) :=
  ⟨Module.Basis.orientation (Module.finBasisOfFinrankEq _ _ planeFiniteDim.out)⟩

/-- Three distinct points on a sphere in a Euclidean affine space are never
collinear: a line meets a sphere in at most two points. -/
lemma not_collinear_of_cospherical {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {P : Type*} [MetricSpace P] [NormedAddTorsor V P]
    {S : Set P} (hS : Cospherical S)
    {U V W : P} (hU : U ∈ S) (hV : V ∈ S) (hW : W ∈ S)
    (hUV : U ≠ V) (hVW : V ≠ W) (hUW : U ≠ W) :
    ¬ Collinear ℝ ({U, V, W} : Set P) := by
  obtain ⟨O, R, hR⟩ := (cospherical_def S).mp hS
  have dU : dist U O = R := hR U hU
  have dV : dist V O = R := hR V hV
  have dW : dist W O = R := hR W hW
  intro hcol
  have mU : U ∈ (⟨O, R⟩ : Sphere P) := mem_sphere.mpr dU
  have mV : V ∈ (⟨O, R⟩ : Sphere P) := mem_sphere.mpr dV
  have mW : W ∈ (⟨O, R⟩ : Sphere P) := mem_sphere.mpr dW
  have key : ∀ p₁ p₂ p : P, p₁ ∈ (⟨O, R⟩ : Sphere P) → p₂ ∈ (⟨O, R⟩ : Sphere P) →
      dist p O = R → Sbtw ℝ p₁ p p₂ → False := by
    intro p₁ p₂ p h₁ h₂ hp hsb
    have hlt := Sphere.dist_center_lt_radius_of_sbtw h₁ h₂ hsb
    change dist O p < R at hlt
    have hp' : dist O p = R := by rw [dist_comm]; exact hp
    rw [hp'] at hlt
    exact absurd hlt (lt_irrefl R)
  rcases hcol.wbtw_or_wbtw_or_wbtw with hw | hw | hw
  · exact key U W V mU mW dV ⟨hw, hUV.symm, hVW⟩
  · exact key V U W mV mU dW ⟨hw, hVW.symm, hUW.symm⟩
  · exact key W V U mW mV dU ⟨hw, hUW, hUV⟩

/-- Extended law of sines on a given sphere in the plane: for three distinct
points on the sphere, a side over the sine of the opposite angle equals the
diameter. -/
lemma dist_div_sin_angle_eq_two_mul_radius {s : Sphere (EuclideanSpace ℝ (Fin 2))}
    {U V W : EuclideanSpace ℝ (Fin 2)} (hU : U ∈ s) (hV : V ∈ s) (hW : W ∈ s)
    (hUV : U ≠ V) (hUW : U ≠ W) (hVW : V ≠ W) :
    dist U W / Real.sin (∠ U V W) = 2 * s.radius := by
  have e1 : Real.sin (∠ U V W) = |(∡ U V W).sin| := by
    rw [angle_eq_abs_oangle_toReal hUV hVW.symm,
      ← Real.abs_sin_eq_sin_abs_of_abs_le_pi (Real.Angle.abs_toReal_le_pi _),
      Real.Angle.sin_toReal]
  rw [e1]
  exact Sphere.dist_div_sin_oangle_eq_two_mul_radius hU hV hW hUV hUW hVW

/-- The sine of an angle of a non-collinear triple is positive. -/
lemma sin_angle_pos_of_not_collinear {U V W : EuclideanSpace ℝ (Fin 2)}
    (h : ¬ Collinear ℝ ({U, V, W} : Set (EuclideanSpace ℝ (Fin 2)))) :
    0 < Real.sin (∠ U V W) :=
  EuclideanGeometry.sin_pos_of_not_collinear h

/-- If `a, b, c` are strictly between and `a, c, e` are not collinear, then
`a, b, e` are not collinear either. -/
lemma not_collinear_of_sbtw_of_not_collinear {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {P : Type*} [MetricSpace P] [NormedAddTorsor V P]
    {a b c e : P} (hs : Sbtw ℝ a b c) (hnc : ¬ Collinear ℝ ({a, c, e} : Set P)) :
    ¬ Collinear ℝ ({a, b, e} : Set P) := by
  intro h
  apply hnc
  have hcol : Collinear ℝ ({a, b, c} : Set P) := hs.wbtw.collinear
  have hc : c ∈ line[ℝ, a, b] :=
    hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hs.left_ne
  have he : e ∈ line[ℝ, a, b] :=
    h.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hs.left_ne
  have ha : a ∈ line[ℝ, a, b] := left_mem_affineSpan_pair ℝ a b
  exact collinear_triple_of_mem_affineSpan_pair ha hc he

/-- The cosine of an angle via the law of cosines. -/
lemma cos_angle_eq_of_ne {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {P : Type*} [MetricSpace P] [NormedAddTorsor V P]
    {p₁ p₂ p₃ : P} (h₁₂ : p₁ ≠ p₂) (h₃₂ : p₃ ≠ p₂) :
    Real.cos (∠ p₁ p₂ p₃) =
      (dist p₁ p₂ ^ 2 + dist p₂ p₃ ^ 2 - dist p₁ p₃ ^ 2) / (2 * dist p₁ p₂ * dist p₂ p₃) := by
  have lc := law_cos p₁ p₂ p₃
  rw [dist_comm p₃ p₂] at lc
  have h : 2 * dist p₁ p₂ * dist p₂ p₃ * Real.cos (∠ p₁ p₂ p₃) =
      dist p₁ p₂ ^ 2 + dist p₂ p₃ ^ 2 - dist p₁ p₃ ^ 2 := by
    linear_combination lc
  have hz : 2 * dist p₁ p₂ * dist p₂ p₃ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (two_ne_zero' ℝ) (dist_ne_zero.mpr h₁₂)) (dist_ne_zero.mpr h₃₂.symm)
  rw [eq_div_iff hz]
  linear_combination h

snip end

problem usa1994_p3
    (A B C D E F X Y Z W : EuclideanSpace ℝ (Fin 2))
    (hcyc : Cospherical ({A, B, C, D, E, F} : Set _))
    (nAB : A ≠ B) (nAC : A ≠ C) (nAD : A ≠ D) (nAE : A ≠ E) (nAF : A ≠ F)
    (nBC : B ≠ C) (nBD : B ≠ D) (nBE : B ≠ E) (nBF : B ≠ F)
    (nCD : C ≠ D) (nCE : C ≠ E) (nCF : C ≠ F)
    (nDE : D ≠ E) (nDF : D ≠ F) (nEF : E ≠ F)
    (hAB : dist A B = dist C D) (hEF : dist C D = dist E F)
    (hYAD : ∠ A Y D = π) (hYBE : ∠ B Y E = π) (hYCF : ∠ C Y F = π)
    (hXAD : ∠ A X D = π) (hXCE : ∠ C X E = π)
    (hZCE : ∠ C Z E = π) (hZDF : ∠ D Z F = π)
    (hWAC : ∠ A W C = π) (hWBD : ∠ B W D = π)
    (hOrdA1 : ∠ B A C + ∠ C A D = ∠ B A D)
    (hOrdA2 : ∠ C A D + ∠ D A E = ∠ C A E)
    (hOrdE1 : ∠ A E B + ∠ B E C = ∠ A E C)
    (hOrdE2 : ∠ B E C + ∠ C E D = ∠ B E D)
    (hOrdC : ∠ D C E + ∠ E C F = ∠ D C F)
    (hOrdD : ∠ C D A + ∠ A D E = ∠ C D E) :
    dist C X / dist X E = (dist A C / dist C E) ^ 2 := by
  -- ## Setup: center, radius, and basic non-degeneracy facts
  obtain ⟨O, R, hR⟩ := (cospherical_def _).mp hcyc
  have mA : A ∈ (⟨O, R⟩ : Sphere (EuclideanSpace ℝ (Fin 2))) := mem_sphere.mpr (hR A (by simp))
  have mB : B ∈ (⟨O, R⟩ : Sphere (EuclideanSpace ℝ (Fin 2))) := mem_sphere.mpr (hR B (by simp))
  have mC : C ∈ (⟨O, R⟩ : Sphere (EuclideanSpace ℝ (Fin 2))) := mem_sphere.mpr (hR C (by simp))
  have mD : D ∈ (⟨O, R⟩ : Sphere (EuclideanSpace ℝ (Fin 2))) := mem_sphere.mpr (hR D (by simp))
  have mE : E ∈ (⟨O, R⟩ : Sphere (EuclideanSpace ℝ (Fin 2))) := mem_sphere.mpr (hR E (by simp))
  have mF : F ∈ (⟨O, R⟩ : Sphere (EuclideanSpace ℝ (Fin 2))) := mem_sphere.mpr (hR F (by simp))
  have sA : A ∈ ({A, B, C, D, E, F} : Set _) := by simp
  have sB : B ∈ ({A, B, C, D, E, F} : Set _) := by simp
  have sC : C ∈ ({A, B, C, D, E, F} : Set _) := by simp
  have sD : D ∈ ({A, B, C, D, E, F} : Set _) := by simp
  have sE : E ∈ ({A, B, C, D, E, F} : Set _) := by simp
  have sF : F ∈ ({A, B, C, D, E, F} : Set _) := by simp
  -- non-collinearity of triples of circle points
  have ncl : ∀ {U V W : EuclideanSpace ℝ (Fin 2)},
      U ∈ ({A, B, C, D, E, F} : Set _) → V ∈ ({A, B, C, D, E, F} : Set _) →
      W ∈ ({A, B, C, D, E, F} : Set _) → U ≠ V → V ≠ W → U ≠ W →
      ¬ Collinear ℝ ({U, V, W} : Set _) :=
    fun hU hV hW hUV hVW hUW => not_collinear_of_cospherical hcyc hU hV hW hUV hVW hUW
  have hRpos : 0 < R := by
    have dA : dist A O = R := hR A (by simp)
    have dB : dist B O = R := hR B (by simp)
    rcases eq_or_ne R 0 with hR0 | hR0
    · have hA0 : A = O := by rwa [← dist_eq_zero, dA]
      have hB0 : B = O := by rwa [← dist_eq_zero, dB]
      exact absurd (hA0.trans hB0.symm) nAB
    · exact lt_of_le_of_ne (dist_nonneg.trans_eq dA) hR0.symm
  -- extended law of sines on the circle: sin of an inscribed angle = chord / diameter
  have hsin : ∀ {U V W : EuclideanSpace ℝ (Fin 2)},
      U ∈ (⟨O, R⟩ : Sphere (EuclideanSpace ℝ (Fin 2))) →
      V ∈ (⟨O, R⟩ : Sphere (EuclideanSpace ℝ (Fin 2))) →
      W ∈ (⟨O, R⟩ : Sphere (EuclideanSpace ℝ (Fin 2))) → U ≠ V → U ≠ W → V ≠ W →
      Real.sin (∠ U V W) = dist U W / (2 * R) := by
    intro U V W hU hV hW hUV hUW hVW
    have h2 := dist_div_sin_angle_eq_two_mul_radius hU hV hW hUV hUW hVW
    have hsinpos : Real.sin (∠ U V W) ≠ 0 := by
      have hnc := not_collinear_of_cospherical
        (Sphere.cospherical (⟨O, R⟩ : Sphere (EuclideanSpace ℝ (Fin 2)))) hU hV hW hUV hVW hUW
      exact (sin_angle_pos_of_not_collinear hnc).ne'
    have h2' : dist U W / Real.sin (∠ U V W) = 2 * R := h2
    field_simp [hsinpos, hRpos.ne'] at h2' ⊢
    exact h2'.symm
  -- ## Sbtw facts from the angle-π hypotheses
  have sYAD : Sbtw ℝ A Y D := angle_eq_pi_iff_sbtw.mp hYAD
  have sYBE : Sbtw ℝ B Y E := angle_eq_pi_iff_sbtw.mp hYBE
  have sYCF : Sbtw ℝ C Y F := angle_eq_pi_iff_sbtw.mp hYCF
  have sXAD : Sbtw ℝ A X D := angle_eq_pi_iff_sbtw.mp hXAD
  have sXCE : Sbtw ℝ C X E := angle_eq_pi_iff_sbtw.mp hXCE
  have cYAD : Collinear ℝ ({A, Y, D} : Set _) := sYAD.wbtw.collinear
  have cYBE : Collinear ℝ ({B, Y, E} : Set _) := sYBE.wbtw.collinear
  have cYCF : Collinear ℝ ({C, Y, F} : Set _) := sYCF.wbtw.collinear
  have cXAD : Collinear ℝ ({A, X, D} : Set _) := sXAD.wbtw.collinear
  have cXCE : Collinear ℝ ({C, X, E} : Set _) := sXCE.wbtw.collinear
  -- ## M1': dist Y A * dist D E = dist Y E * dist A B
  have hM1 : dist Y A * dist D E = dist Y E * dist A B := by
    have e1 : Real.sin (∠ E A Y) = dist D E / (2 * R) := by
      rw [angle_comm E A Y, sYAD.angle_eq_left E]
      exact hsin mD mA mE nAD.symm nDE nAE
    have e2 : Real.sin (∠ A E Y) = dist A B / (2 * R) := by
      rw [angle_comm A E Y, (sYBE.symm).angle_eq_left A, angle_comm B E A]
      exact hsin mA mE mB nAE nAB nBE.symm
    have e3 := law_sin E Y A
    have e4 := law_sin A Y E
    rw [angle_comm E Y A] at e3
    rw [e1] at e4; rw [e2] at e3
    rw [dist_comm E A] at e4
    field_simp [hRpos.ne'] at e3 e4
    have hs : Real.sin (∠ A Y E) ≠ 0 := by
      have hnc : ¬ Collinear ℝ ({A, Y, E} : Set _) :=
        not_collinear_of_sbtw_of_not_collinear sYAD (ncl sA sD sE nAD nDE nAE)
      exact (sin_angle_pos_of_not_collinear hnc).ne'
    have key : dist Y A * dist D E * (Real.sin (∠ A Y E) * (2 * R)) =
        dist Y E * dist A B * (Real.sin (∠ A Y E) * (2 * R)) := by
      linear_combination (dist D E) * e3 - (dist A B) * e4
    exact mul_right_cancel₀ (mul_ne_zero hs (mul_ne_zero (two_ne_zero' ℝ) hRpos.ne')) key
  -- ## M2b: dist Y C * dist A B = dist Y E * dist B C
  have hM2 : dist Y C * dist A B = dist Y E * dist B C := by
    have hABEF : dist A B = dist E F := hAB.trans hEF
    have e1 : Real.sin (∠ E C Y) = dist E F / (2 * R) := by
      rw [angle_comm E C Y, sYCF.angle_eq_left E, ← dist_comm F E]
      exact hsin mF mC mE nCF.symm nEF.symm nCE
    have e2 : Real.sin (∠ C E Y) = dist B C / (2 * R) := by
      rw [angle_comm C E Y, (sYBE.symm).angle_eq_left C]
      exact hsin mB mE mC nBE nBC nCE.symm
    have e3 := law_sin E Y C
    have e4 := law_sin C Y E
    rw [angle_comm E Y C] at e3
    rw [e1] at e4; rw [e2] at e3
    rw [dist_comm C E] at e3
    field_simp [hRpos.ne'] at e3 e4
    have hs : Real.sin (∠ C Y E) ≠ 0 := by
      have hnc : ¬ Collinear ℝ ({C, Y, E} : Set _) :=
        not_collinear_of_sbtw_of_not_collinear sYCF (ncl sC sF sE nCF nEF.symm nCE)
      exact (sin_angle_pos_of_not_collinear hnc).ne'
    have key : dist Y C * dist E F * (Real.sin (∠ C Y E) * (2 * R)) =
        dist Y E * dist B C * (Real.sin (∠ C Y E) * (2 * R)) := by
      linear_combination (dist E F) * e3 - (dist B C) * e4
    have key' := mul_right_cancel₀ (mul_ne_zero hs (mul_ne_zero (two_ne_zero' ℝ) hRpos.ne')) key
    rwa [hABEF]
  -- ## J4: dist Y D * dist A E = dist Y E * dist B D
  have hJ4 : dist Y D * dist A E = dist Y E * dist B D := by
    have e1 : Real.sin (∠ E D Y) = dist A E / (2 * R) := by
      rw [angle_comm E D Y, (sYAD.symm).angle_eq_left E]
      exact hsin mA mD mE nAD nAE nDE
    have e2 : Real.sin (∠ D E Y) = dist B D / (2 * R) := by
      rw [angle_comm D E Y, (sYBE.symm).angle_eq_left D]
      exact hsin mB mE mD nBE nBD nDE.symm
    have e3 := law_sin E Y D
    have e4 := law_sin D Y E
    rw [angle_comm E Y D] at e3
    rw [e1] at e4; rw [e2] at e3
    rw [dist_comm D E] at e3
    field_simp [hRpos.ne'] at e3 e4
    have hs : Real.sin (∠ D Y E) ≠ 0 := by
      have hnc : ¬ Collinear ℝ ({D, Y, E} : Set _) :=
        not_collinear_of_sbtw_of_not_collinear sYAD.symm (ncl sD sA sE nAD.symm nAE nDE)
      exact (sin_angle_pos_of_not_collinear hnc).ne'
    have key : dist Y D * dist A E * (Real.sin (∠ D Y E) * (2 * R)) =
        dist Y E * dist B D * (Real.sin (∠ D Y E) * (2 * R)) := by
      linear_combination (dist A E) * e3 - (dist B D) * e4
    exact mul_right_cancel₀ (mul_ne_zero hs (mul_ne_zero (two_ne_zero' ℝ) hRpos.ne')) key
  -- ## X-i: dist X A * dist C D = dist X C * dist A E
  have hXi : dist X A * dist C D = dist X C * dist A E := by
    have e1 : Real.sin (∠ A E X) = dist A C / (2 * R) := by
      rw [angle_comm A E X, (sXCE.symm).angle_eq_left A, angle_comm C E A]
      exact hsin mA mE mC nAE nAC nCE.symm
    have e2 : Real.sin (∠ C D X) = dist A C / (2 * R) := by
      rw [angle_comm C D X, (sXAD.symm).angle_eq_left C]
      exact hsin mA mD mC nAD nAC nCD.symm
    have e3 := law_sin E X A
    have e4 := law_sin D X C
    rw [angle_comm E X A] at e3
    rw [e1] at e3; rw [e2] at e4
    have hvert : Real.sin (∠ D X C) = Real.sin (∠ A X E) :=
      congrArg Real.sin (angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi hXAD
        (by rw [angle_comm E X C]; exact hXCE)).symm
    rw [hvert] at e4
    field_simp [hRpos.ne'] at e3 e4
    have hs : Real.sin (∠ A X E) ≠ 0 := by
      have hnc : ¬ Collinear ℝ ({A, X, E} : Set _) :=
        not_collinear_of_sbtw_of_not_collinear sXAD (ncl sA sD sE nAD nDE nAE)
      exact (sin_angle_pos_of_not_collinear hnc).ne'
    have key : dist X A * dist C D * (Real.sin (∠ A X E) * (2 * R)) =
        dist X C * dist A E * (Real.sin (∠ A X E) * (2 * R)) := by
      linear_combination (dist C D) * e3 - (dist A E) * e4
    exact mul_right_cancel₀ (mul_ne_zero hs (mul_ne_zero (two_ne_zero' ℝ) hRpos.ne')) key
  -- ## X-i': dist X A * dist D E = dist X E * dist A C
  have hXi' : dist X A * dist D E = dist X E * dist A C := by
    have e1 : Real.sin (∠ A C X) = dist A E / (2 * R) := by
      rw [angle_comm A C X, sXCE.angle_eq_left A, dist_comm A E]
      exact hsin mE mC mA nCE.symm nAE.symm nAC.symm
    have e2 : Real.sin (∠ E A X) = dist D E / (2 * R) := by
      rw [angle_comm E A X, sXAD.angle_eq_left E]
      exact hsin mD mA mE nAD.symm nDE nAE
    have e3 := law_sin C X A
    have e4 := law_sin A X E
    rw [angle_comm C X A] at e3
    rw [e1] at e3; rw [e2] at e4
    have hsupp : ∠ A X C + ∠ A X E = π := angle_add_angle_eq_pi_of_angle_eq_pi A hXCE
    have hsinAXC : Real.sin (∠ A X C) = Real.sin (∠ A X E) := by
      rw [← Real.sin_pi_sub (∠ A X C), ← hsupp, add_sub_cancel_left]
    rw [hsinAXC] at e3
    rw [dist_comm E A] at e4
    field_simp [hRpos.ne'] at e3 e4
    have hs : Real.sin (∠ A X E) ≠ 0 := by
      have hnc : ¬ Collinear ℝ ({A, X, E} : Set _) :=
        not_collinear_of_sbtw_of_not_collinear sXAD (ncl sA sD sE nAD nDE nAE)
      exact (sin_angle_pos_of_not_collinear hnc).ne'
    have key : dist X A * dist D E * (Real.sin (∠ A X E) * (2 * R)) =
        dist X E * dist A C * (Real.sin (∠ A X E) * (2 * R)) := by
      linear_combination (dist D E) * e3 - (dist A C) * e4
    exact mul_right_cancel₀ (mul_ne_zero hs (mul_ne_zero (two_ne_zero' ℝ) hRpos.ne')) key
  -- ## E1: Ptolemy on ACDE: dist A C * dist D E + dist C D * dist E A = dist A D * dist C E
  have hE1 : dist A C * dist D E + dist C D * dist E A = dist A D * dist C E := by
    have hsub : Cospherical ({A, C, D, E} : Set _) := by
      apply hcyc.subset
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> simp
    exact mul_dist_add_mul_dist_eq_mul_dist_of_cospherical hsub hXAD hXCE
  -- ## E2: Ptolemy on ABDE: dist A B * dist D E + dist B D * dist E A = dist A D * dist B E
  have hE2 : dist A B * dist D E + dist B D * dist E A = dist A D * dist B E := by
    have hsub : Cospherical ({A, B, D, E} : Set _) := by
      apply hcyc.subset
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> simp
    exact mul_dist_add_mul_dist_eq_mul_dist_of_cospherical hsub hYAD hYBE
  -- ## E3: Ptolemy on ACDF: dist A C * dist D F + dist C D * dist F A = dist A D * dist C F
  have hE3 : dist A C * dist D F + dist C D * dist F A = dist A D * dist C F := by
    have hsub : Cospherical ({A, C, D, F} : Set _) := by
      apply hcyc.subset
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> simp
    exact mul_dist_add_mul_dist_eq_mul_dist_of_cospherical hsub hYAD hYCF
  -- ## E4: Ptolemy on BCEF: dist B C * dist E F + dist C E * dist F B = dist B E * dist C F
  have hE4 : dist B C * dist E F + dist C E * dist F B = dist B E * dist C F := by
    have hsub : Cospherical ({B, C, E, F} : Set _) := by
      apply hcyc.subset
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> simp
    exact mul_dist_add_mul_dist_eq_mul_dist_of_cospherical hsub hYBE hYCF
  -- ## E5/E6: power of point Y (intersecting chords)
  have hE5 : dist A Y * dist D Y = dist B Y * dist E Y := by
    have hsub : Cospherical ({A, D, B, E} : Set _) := by
      apply hcyc.subset
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> simp
    exact mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi (a := A) (b := D) (c := B) (d := E) hsub hYAD hYBE
  have hE6 : dist B Y * dist E Y = dist C Y * dist F Y := by
    have hsub : Cospherical ({B, E, C, F} : Set _) := by
      apply hcyc.subset
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> simp
    exact mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi (a := B) (b := E) (c := C) (d := F) hsub hYBE hYCF
  -- ## J1: dist Y A * dist B D = dist Y B * dist A E
  have hJ1 : dist Y A * dist B D = dist Y B * dist A E := by
    have e1 : Real.sin (∠ B A Y) = dist B D / (2 * R) := by
      rw [angle_comm B A Y, sYAD.angle_eq_left B, ← dist_comm D B]
      exact hsin mD mA mB nAD.symm nBD.symm nAB
    have e2 : Real.sin (∠ A B Y) = dist A E / (2 * R) := by
      rw [angle_comm A B Y, sYBE.angle_eq_left A, dist_comm A E]
      exact hsin mE mB mA nBE.symm nAE.symm nAB.symm
    have e3 := law_sin B Y A
    have e4 := law_sin A Y B
    rw [angle_comm B Y A] at e3
    rw [e1] at e4; rw [e2] at e3
    rw [dist_comm B A] at e4
    field_simp [hRpos.ne'] at e3 e4
    have hs : Real.sin (∠ A Y B) ≠ 0 := by
      have hnc : ¬ Collinear ℝ ({A, Y, B} : Set _) :=
        not_collinear_of_sbtw_of_not_collinear sYAD (ncl sA sD sB nAD nBD.symm nAB)
      exact (sin_angle_pos_of_not_collinear hnc).ne'
    have key : dist Y A * dist B D * (Real.sin (∠ A Y B) * (2 * R)) =
        dist Y B * dist A E * (Real.sin (∠ A Y B) * (2 * R)) := by
      linear_combination (dist B D) * e3 - (dist A E) * e4
    exact mul_right_cancel₀ (mul_ne_zero hs (mul_ne_zero (two_ne_zero' ℝ) hRpos.ne')) key
  -- ## J2: dist Y B * dist C E = dist Y C * dist B F
  have hJ2 : dist Y B * dist C E = dist Y C * dist B F := by
    have e1 : Real.sin (∠ B C Y) = dist B F / (2 * R) := by
      rw [angle_comm B C Y, sYCF.angle_eq_left B, dist_comm B F]
      exact hsin mF mC mB nCF.symm nBF.symm nBC.symm
    have e2 : Real.sin (∠ C B Y) = dist C E / (2 * R) := by
      rw [angle_comm C B Y, sYBE.angle_eq_left C, dist_comm C E]
      exact hsin mE mB mC nBE.symm nCE.symm nBC
    have e3 := law_sin C Y B
    have e4 := law_sin B Y C
    rw [angle_comm C Y B] at e3
    rw [e1] at e3; rw [e2] at e4
    rw [dist_comm C B] at e4
    field_simp [hRpos.ne'] at e3 e4
    have hs : Real.sin (∠ B Y C) ≠ 0 := by
      have hnc : ¬ Collinear ℝ ({B, Y, C} : Set _) :=
        not_collinear_of_sbtw_of_not_collinear sYBE (ncl sB sE sC nBE nCE.symm nBC)
      exact (sin_angle_pos_of_not_collinear hnc).ne'
    have key : dist Y B * dist C E * (Real.sin (∠ B Y C) * (2 * R)) =
        dist Y C * dist B F * (Real.sin (∠ B Y C) * (2 * R)) := by
      linear_combination (dist C E) * e3 - (dist B F) * e4
    exact mul_right_cancel₀ (mul_ne_zero hs (mul_ne_zero (two_ne_zero' ℝ) hRpos.ne')) key
  -- ## J3: dist Y C * dist D F = dist Y D * dist A C
  have hJ3 : dist Y C * dist D F = dist Y D * dist A C := by
    have e1 : Real.sin (∠ C D Y) = dist A C / (2 * R) := by
      rw [angle_comm C D Y, (sYAD.symm).angle_eq_left C]
      exact hsin mA mD mC nAD nAC nCD.symm
    have e2 : Real.sin (∠ D C Y) = dist D F / (2 * R) := by
      rw [angle_comm D C Y, sYCF.angle_eq_left D, dist_comm D F]
      exact hsin mF mC mD nCF.symm nDF.symm nCD
    have e3 := law_sin D Y C
    have e4 := law_sin C Y D
    rw [angle_comm D Y C] at e3
    rw [e1] at e3; rw [e2] at e4
    rw [dist_comm D C] at e4
    field_simp [hRpos.ne'] at e3 e4
    have hs : Real.sin (∠ C Y D) ≠ 0 := by
      have hnc : ¬ Collinear ℝ ({C, Y, D} : Set _) :=
        not_collinear_of_sbtw_of_not_collinear sYCF (ncl sC sF sD nCF nDF.symm nCD)
      exact (sin_angle_pos_of_not_collinear hnc).ne'
    have key : dist Y C * dist D F * (Real.sin (∠ C Y D) * (2 * R)) =
        dist Y D * dist A C * (Real.sin (∠ C Y D) * (2 * R)) := by
      linear_combination (dist D F) * e3 - (dist A C) * e4
    exact mul_right_cancel₀ (mul_ne_zero hs (mul_ne_zero (two_ne_zero' ℝ) hRpos.ne')) key
  -- ## J5: dist Y E * dist B F = dist Y F * dist C E
  have hJ5 : dist Y E * dist B F = dist Y F * dist C E := by
    have e1 : Real.sin (∠ E F Y) = dist C E / (2 * R) := by
      rw [angle_comm E F Y, (sYCF.symm).angle_eq_left E]
      exact hsin mC mF mE nCF nCE nEF.symm
    have e2 : Real.sin (∠ F E Y) = dist B F / (2 * R) := by
      rw [angle_comm F E Y, (sYBE.symm).angle_eq_left F]
      exact hsin mB mE mF nBE nBF nEF
    have e3 := law_sin F Y E
    have e4 := law_sin E Y F
    rw [angle_comm F Y E] at e3
    rw [e1] at e3; rw [e2] at e4
    rw [dist_comm F E] at e4
    field_simp [hRpos.ne'] at e3 e4
    have hs : Real.sin (∠ E Y F) ≠ 0 := by
      have hnc : ¬ Collinear ℝ ({E, Y, F} : Set _) :=
        not_collinear_of_sbtw_of_not_collinear sYBE.symm (ncl sE sB sF nBE.symm nBF nEF)
      exact (sin_angle_pos_of_not_collinear hnc).ne'
    have key : dist Y E * dist B F * (Real.sin (∠ E Y F) * (2 * R)) =
        dist Y F * dist C E * (Real.sin (∠ E Y F) * (2 * R)) := by
      linear_combination (dist B F) * e3 - (dist C E) * e4
    exact mul_right_cancel₀ (mul_ne_zero hs (mul_ne_zero (two_ne_zero' ℝ) hRpos.ne')) key
  -- ## J6: dist Y F * dist A C = dist Y A * dist D F
  have hJ6 : dist Y F * dist A C = dist Y A * dist D F := by
    have e1 : Real.sin (∠ F A Y) = dist D F / (2 * R) := by
      rw [angle_comm F A Y, sYAD.angle_eq_left F]
      exact hsin mD mA mF nAD.symm nDF nAF
    have e2 : Real.sin (∠ A F Y) = dist A C / (2 * R) := by
      rw [angle_comm A F Y, (sYCF.symm).angle_eq_left A, angle_comm C F A]
      exact hsin mA mF mC nAF nAC nCF.symm
    have e3 := law_sin F Y A
    have e4 := law_sin A Y F
    rw [angle_comm F Y A] at e3
    rw [e2] at e3; rw [e1] at e4
    rw [dist_comm F A] at e4
    field_simp [hRpos.ne'] at e3 e4
    have hs : Real.sin (∠ A Y F) ≠ 0 := by
      have hnc : ¬ Collinear ℝ ({A, Y, F} : Set _) :=
        not_collinear_of_sbtw_of_not_collinear sYAD (ncl sA sD sF nAD nDF nAF)
      exact (sin_angle_pos_of_not_collinear hnc).ne'
    have key : dist Y F * dist A C * (Real.sin (∠ A Y F) * (2 * R)) =
        dist Y A * dist D F * (Real.sin (∠ A Y F) * (2 * R)) := by
      linear_combination (dist A C) * e4 - (dist D F) * e3
    exact mul_right_cancel₀ (mul_ne_zero hs (mul_ne_zero (two_ne_zero' ℝ) hRpos.ne')) key
  -- ## M3a: dist Y A * dist A B = dist Y C * dist F A
  have hM3 : dist Y A * dist A B = dist Y C * dist F A := by
    have e1 : Real.sin (∠ A C Y) = dist F A / (2 * R) := by
      rw [angle_comm A C Y, sYCF.angle_eq_left A]
      exact hsin mF mC mA nCF.symm nAF.symm nAC.symm
    have e2 : Real.sin (∠ C A Y) = dist C D / (2 * R) := by
      rw [angle_comm C A Y, sYAD.angle_eq_left C, angle_comm D A C]
      exact hsin mC mA mD nAC.symm nCD nAD
    have e3 := law_sin C Y A
    have e4 := law_sin A Y C
    rw [angle_comm C Y A] at e3
    rw [e1] at e3; rw [e2] at e4
    rw [dist_comm C A] at e4
    field_simp [hRpos.ne'] at e3 e4
    have hs : Real.sin (∠ A Y C) ≠ 0 := by
      have hnc : ¬ Collinear ℝ ({A, Y, C} : Set _) :=
        not_collinear_of_sbtw_of_not_collinear sYAD (ncl sA sD sC nAD nCD.symm nAC)
      exact (sin_angle_pos_of_not_collinear hnc).ne'
    have key : dist Y A * dist C D * (Real.sin (∠ A Y C) * (2 * R)) =
        dist Y C * dist F A * (Real.sin (∠ A Y C) * (2 * R)) := by
      linear_combination (dist C D) * e3 - (dist F A) * e4
    have key' := mul_right_cancel₀ (mul_ne_zero hs (mul_ne_zero (two_ne_zero' ℝ) hRpos.ne')) key
    rwa [hAB]
  -- ## projection: dist C E = dist Y C * cos(∠ F C E) + dist Y E * cos(∠ B E C)
  have hproj : dist C E = dist Y C * Real.cos (∠ F C E) + dist Y E * Real.cos (∠ B E C) := by
    have lc1 := law_cos Y C E
    have lc2 := law_cos Y E C
    rw [dist_comm C E] at lc2
    have hz : 2 * dist E C * (dist Y C * Real.cos (∠ Y C E) +
        dist Y E * Real.cos (∠ Y E C) - dist E C) = 0 := by
      linear_combination lc1 + lc2
    have hCE : dist E C ≠ 0 := dist_ne_zero.mpr nCE.symm
    have key : dist Y C * Real.cos (∠ Y C E) + dist Y E * Real.cos (∠ Y E C) - dist E C = 0 := by
      rcases mul_eq_zero.mp hz with h | h
      · exfalso; exact mul_ne_zero (two_ne_zero' ℝ) hCE h
      · exact h
    have e1 : Real.cos (∠ Y C E) = Real.cos (∠ F C E) := congrArg Real.cos (sYCF.angle_eq_left E)
    have e2 : Real.cos (∠ Y E C) = Real.cos (∠ B E C) := congrArg Real.cos ((sYBE.symm).angle_eq_left C)
    rw [e1, e2] at key
    have key2 : dist E C = dist Y C * Real.cos (∠ F C E) + dist Y E * Real.cos (∠ B E C) := by
      linarith [key]
    rw [dist_comm E C] at key2
    exact key2
  -- ## REL1 (from hOrdE2): dist B D = dist B C * cos(∠ C E D) + dist C D * cos(∠ B E C)
  have hREL1 : dist B D = dist B C * Real.cos (∠ C E D) + dist C D * Real.cos (∠ B E C) := by
    have h1 : Real.sin (∠ B E D) = dist B D / (2 * R) := hsin mB mE mD nBE nBD nDE.symm
    have h2 : Real.sin (∠ B E C) = dist B C / (2 * R) := hsin mB mE mC nBE nBC nCE.symm
    have h3 : Real.sin (∠ C E D) = dist C D / (2 * R) := hsin mC mE mD nCE nCD nDE.symm
    have h4 : Real.sin (∠ B E D) = Real.sin (∠ B E C + ∠ C E D) := by rw [hOrdE2]
    rw [Real.sin_add] at h4
    rw [h1, h2, h3] at h4
    field_simp [hRpos.ne'] at h4
    linear_combination h4
  have hREL1' : dist B D = dist B C * Real.cos (∠ C E D) + dist A B * Real.cos (∠ B E C) := by
    rw [hAB]
    exact hREL1
  -- ## REL-A2 (from hOrdA2): dist C E = dist C D * cos(∠ D A E) + dist D E * cos(∠ C A D)
  have hRELA2 : dist C E = dist C D * Real.cos (∠ D A E) + dist D E * Real.cos (∠ C A D) := by
    have h1 : Real.sin (∠ C A E) = dist C E / (2 * R) := hsin mC mA mE nAC.symm nCE nAE
    have h2 : Real.sin (∠ C A D) = dist C D / (2 * R) := hsin mC mA mD nAC.symm nCD nAD
    have h3 : Real.sin (∠ D A E) = dist D E / (2 * R) := hsin mD mA mE nAD.symm nDE nAE
    have h4 : Real.sin (∠ C A E) = Real.sin (∠ C A D + ∠ D A E) := by rw [hOrdA2]
    rw [Real.sin_add] at h4
    rw [h1, h2, h3] at h4
    field_simp [hRpos.ne'] at h4
    linear_combination h4
  -- ## E-K1 (exterior angle): dist A E * dist D E =
  --    dist Y E * (dist B D * cos(∠ E B A) + dist A E * cos(∠ D A B))
  have hEK1 : dist A E * dist D E =
      dist Y E * (dist B D * Real.cos (∠ E B A) + dist A E * Real.cos (∠ D A B)) := by
    -- ∠ A Y E = ∠ Y A B + ∠ Y B A (exterior angle of △YAB along line BE)
    have hsupp : ∠ A Y B + ∠ A Y E = π := angle_add_angle_eq_pi_of_angle_eq_pi A hYBE
    have hsum : ∠ Y A B + ∠ Y B A + ∠ A Y B = π := by
      have h := angle_add_angle_add_angle_eq_pi B sYAD.left_ne
      rw [angle_comm A B Y, angle_comm B Y A] at h
      exact h
    have hext : ∠ A Y E = ∠ Y A B + ∠ Y B A := by linarith [hsum, hsupp]
    -- law of sines in △YAE: sin∠AYE = AE·sin∠YAE / YE
    have ls := law_sin A Y E
    have e1 : Real.sin (∠ E A Y) = dist D E / (2 * R) := by
      rw [angle_comm E A Y, sYAD.angle_eq_left E]
      exact hsin mD mA mE nAD.symm nDE nAE
    rw [e1] at ls
    have e2 : Real.sin (∠ Y A B) = dist B D / (2 * R) := by
      rw [sYAD.angle_eq_left B, ← dist_comm D B]
      exact hsin mD mA mB nAD.symm nBD.symm nAB
    have e3 : Real.sin (∠ Y B A) = dist A E / (2 * R) := by
      rw [sYBE.angle_eq_left A, angle_comm E B A]
      exact hsin mA mB mE nAB nAE nBE
    have hsin' : Real.sin (∠ A Y E) = Real.sin (∠ Y A B + ∠ Y B A) := by rw [hext]
    rw [Real.sin_add] at hsin'
    rw [e2, e3] at hsin'
    rw [hsin'] at ls
    rw [dist_comm E A] at ls
    have key : dist Y E * (dist B D * Real.cos (∠ Y B A) + dist A E * Real.cos (∠ Y A B)) =
        dist A E * dist D E := by
      field_simp [hRpos.ne'] at ls
      linear_combination ls
    rw [sYBE.angle_eq_left A, sYAD.angle_eq_left B] at key
    exact key.symm
  -- ## projection in △YAE: dist A E = dist Y A * cos(∠ D A E) + dist Y E * cos(∠ B E A)
  have hprojAE : dist A E = dist Y A * Real.cos (∠ D A E) + dist Y E * Real.cos (∠ B E A) := by
    have lc1 := law_cos Y A E
    have lc2 := law_cos Y E A
    rw [dist_comm A E] at lc2
    have hz : 2 * dist E A * (dist Y A * Real.cos (∠ Y A E) +
        dist Y E * Real.cos (∠ Y E A) - dist E A) = 0 := by
      linear_combination lc1 + lc2
    have hAE : dist E A ≠ 0 := dist_ne_zero.mpr nAE.symm
    have key : dist Y A * Real.cos (∠ Y A E) + dist Y E * Real.cos (∠ Y E A) - dist E A = 0 := by
      rcases mul_eq_zero.mp hz with h | h
      · exfalso; exact mul_ne_zero (two_ne_zero' ℝ) hAE h
      · exact h
    have e1 : Real.cos (∠ Y A E) = Real.cos (∠ D A E) := congrArg Real.cos (sYAD.angle_eq_left E)
    have e2 : Real.cos (∠ Y E A) = Real.cos (∠ B E A) := congrArg Real.cos ((sYBE.symm).angle_eq_left A)
    rw [e1, e2] at key
    have key2 : dist E A = dist Y A * Real.cos (∠ D A E) + dist Y E * Real.cos (∠ B E A) := by
      linarith [key]
    rw [dist_comm E A] at key2
    exact key2
  -- ## goalA: dist X C * dist A E * dist D E = dist X E * dist A C * dist C D
  have hgoalAcd : dist X C * dist A E * dist D E = dist X E * dist A C * dist C D := by
    calc dist X C * dist A E * dist D E = (dist X C * dist A E) * dist D E := by ring
      _ = (dist X A * dist C D) * dist D E := by rw [← hXi]
      _ = (dist X A * dist D E) * dist C D := by ring
      _ = (dist X E * dist A C) * dist C D := by rw [hXi']
      _ = dist X E * dist A C * dist C D := by ring
  have hgoalA : dist X C * dist A E * dist D E = dist X E * dist A C * dist A B := by
    rwa [← hAB] at hgoalAcd
  -- ## COSREL-Q2: cos(∠ C A D) = cos(∠ B E A)   [algebraic, proof below]
  have hCQ2 : Real.cos (∠ C A D) = Real.cos (∠ B E A) := by
    have hA : Real.cos (∠ C A D) = Real.cos (∠ C E D) := by
      -- A and E lie on the same side of line CD, since X is strictly inside
      -- both segments AD and CE.
      have hXE : X ∈ line[ℝ, C, E] :=
        cXCE.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) nCE
      have hXnot : X ∉ line[ℝ, C, D] := by
        intro hX
        have hCDX : Collinear ℝ ({X, C, D} : Set _) :=
          collinear_insert_of_mem_affineSpan_pair hX
        have hD' : D ∈ line[ℝ, C, X] :=
          hCDX.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) sXCE.left_ne
        have hC' : C ∈ line[ℝ, C, X] := left_mem_affineSpan_pair ℝ C X
        have hE' : E ∈ line[ℝ, C, X] := by
          have hCEX : Collinear ℝ ({X, C, E} : Set _) :=
            collinear_insert_of_mem_affineSpan_pair hXE
          exact hCEX.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) sXCE.left_ne
        have hCDE : Collinear ℝ ({C, D, E} : Set _) :=
          collinear_triple_of_mem_affineSpan_pair hC' hD' hE'
        exact ncl sC sD sE nCD nDE nCE hCDE
      obtain ⟨⟨t₂, ⟨ht₂0, ht₂1⟩, hXt₂⟩, hne₁₂, hne₂₂⟩ := sXCE
      obtain ⟨⟨t₁, ⟨ht₁0, ht₁1⟩, hXt₁⟩, hne₁₁, hne₂₁⟩ := sXAD.symm
      have ht₂ : 0 < t₂ := by
        rcases eq_or_ne t₂ 0 with h | h
        · subst h; simp [AffineMap.lineMap_apply_zero] at hXt₂
          exact absurd hXt₂ hne₁₂.symm
        · exact lt_of_le_of_ne ht₂0 h.symm
      have ht₁ : 0 < t₁ := by
        rcases eq_or_ne t₁ 0 with h | h
        · subst h; simp [AffineMap.lineMap_apply_zero] at hXt₁
          exact absurd hXt₁ hne₁₁.symm
        · exact lt_of_le_of_ne ht₁0 h.symm
      have hE'not : E ∉ line[ℝ, C, D] := by
        intro hE''
        have hCDE : Collinear ℝ ({E, C, D} : Set _) :=
          collinear_insert_of_mem_affineSpan_pair hE''
        exact ncl sE sC sD nCE.symm nCD nDE.symm hCDE
      have hsideXE : (line[ℝ, C, D]).SSameSide X E := by
        have h := AffineSubspace.sSameSide_lineMap_left (left_mem_affineSpan_pair ℝ C D) hE'not ht₂
        exact hXt₂.symm ▸ h
      have hsideXA : (line[ℝ, C, D]).SSameSide X A := by
        have hA' : A ∉ line[ℝ, C, D] := by
          intro hA''
          have hACD : Collinear ℝ ({A, C, D} : Set _) :=
            collinear_insert_of_mem_affineSpan_pair hA''
          exact ncl sA sC sD nAC nCD nAD hACD
        have h := AffineSubspace.sSameSide_lineMap_left (right_mem_affineSpan_pair ℝ C D) hA' ht₁
        exact hXt₁.symm ▸ h
      have hside : (line[ℝ, C, D]).SSameSide A E :=
        (AffineSubspace.sSameSide_comm.mp hsideXA).trans hsideXE
      -- same side gives equal signs of the oriented angles
      have hsgn : (∡ C A D).sign = (∡ C E D).sign :=
        AffineSubspace.SSameSide.oangle_sign_eq (left_mem_affineSpan_pair ℝ C D)
          (right_mem_affineSpan_pair ℝ C D) (AffineSubspace.sSameSide_comm.mp hside)
      -- inscribed angle theorem, oriented form
      have hsub : Cospherical ({C, A, E, D} : Set _) := by
        apply hcyc.subset
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> simp
      have h2 : (2 : ℤ) • ∡ C A D = (2 : ℤ) • ∡ C E D :=
        Cospherical.two_zsmul_oangle_eq hsub nAC nAD nCE.symm nDE.symm
      -- the two alternatives of the 2-torsion; the equal signs rule out `+π`
      have hcases : ∡ C A D = ∡ C E D ∨ ∡ C A D = π + ∡ C E D := by
        have h2' : (2 : ℤ) • (∡ C A D - ∡ C E D) = 0 := by
          rw [zsmul_sub, h2, sub_self]
        rcases Real.Angle.two_zsmul_eq_zero_iff.mp h2' with h | h
        · left; exact sub_eq_zero.mp h
        · right; exact sub_eq_iff_eq_add.mp h
      have hang : ∡ C A D = ∡ C E D := by
        rcases hcases with h | h
        · exact h
        · exfalso
          have hsgn0 : (∡ C E D).sign = 0 := by
            have h1 := hsgn
            rw [h, Real.Angle.sign_pi_add] at h1
            rcases SignType.trichotomy (∡ C E D).sign with h0 | h0 | h0
            · rw [h0] at h1
              exact absurd h1 (by decide)
            · exact h0
            · rw [h0] at h1
              exact absurd h1 (by decide)
          have h0 : (∡ C A D).sign = 0 := by
            rw [hsgn]
            exact hsgn0
          rw [Real.Angle.sign_eq_zero_iff] at h0
          have hne : ∡ C A D ≠ 0 ∧ ∡ C A D ≠ π := by
            rw [oangle_ne_zero_and_ne_pi_iff_not_collinear]
            exact ncl sC sA sD nAC.symm nAD nCD
          rcases h0 with h0 | h0
          · exact hne.1 h0
          · exact hne.2 h0
      have e1 : ∠ C A D = |(∡ C A D).toReal| := angle_eq_abs_oangle_toReal nAC.symm nAD.symm
      have e2 : ∠ C E D = |(∡ C E D).toReal| := angle_eq_abs_oangle_toReal nCE nDE
      rw [e1, e2, hang]
    have hB : Real.cos (∠ C E D) = Real.cos (∠ B E A) := by
      have sWAC : Sbtw ℝ A W C := angle_eq_pi_iff_sbtw.mp hWAC
      have sWBD : Sbtw ℝ B W D := angle_eq_pi_iff_sbtw.mp hWBD
      -- ## AC = BD: diagonals of the isoceles trapezoid ABCD are equal
      -- WA = WD (law of sines in △WAB, △WDC)
      have w1 : Real.sin (∠ W B A) = dist D A / (2 * R) := by
        rw [sWBD.angle_eq_left A]
        exact hsin mD mB mA nBD.symm nAD.symm nAB.symm
      have w2 : Real.sin (∠ D C W) = dist A D / (2 * R) := by
        rw [angle_comm D C W, (sWAC.symm).angle_eq_left D]
        exact hsin mA mC mD nAC nAD nCD
      have l1 := law_sin B W A
      have l2 := law_sin C W D
      rw [angle_comm A B W] at l1
      rw [w1] at l1
      rw [w2] at l2
      have hvert : ∠ A W B = ∠ C W D :=
        angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi hWAC hWBD
      rw [angle_comm B W A] at l1
      rw [dist_comm D A] at l1
      rw [← hvert] at l2
      rw [dist_comm D C, ← hAB] at l2
      have hs1 : Real.sin (∠ A W B) ≠ 0 := by
        have hnc : ¬ Collinear ℝ ({A, W, B} : Set _) :=
          not_collinear_of_sbtw_of_not_collinear sWAC (ncl sA sC sB nAC nBC.symm nAB)
        exact (sin_angle_pos_of_not_collinear hnc).ne'
      have hWA : dist W A = dist W D := by
        have key : Real.sin (∠ A W B) * dist W A = Real.sin (∠ A W B) * dist W D := by
          linear_combination l1 - l2
        exact mul_left_cancel₀ hs1 key
      -- WB = WC (law of sines in △WAB, △WDC)
      have w3 : Real.sin (∠ B A W) = dist C B / (2 * R) := by
        rw [angle_comm B A W, sWAC.angle_eq_left B]
        exact hsin mC mA mB nAC.symm nBC.symm nAB
      have w4 : Real.sin (∠ C D W) = dist B C / (2 * R) := by
        rw [angle_comm C D W, (sWBD.symm).angle_eq_left C]
        exact hsin mB mD mC nBD nBC nCD.symm
      have l3 := law_sin A W B
      have l4 := law_sin D W C
      rw [w3] at l3
      rw [dist_comm C B, dist_comm B A] at l3
      rw [w4] at l4
      rw [angle_comm D W C] at l4
      rw [← hvert] at l4
      rw [← hAB] at l4
      have hWB : dist W B = dist W C := by
        have key : Real.sin (∠ A W B) * dist W B = Real.sin (∠ A W B) * dist W C := by
          linear_combination l3 - l4
        exact mul_left_cancel₀ hs1 key
      -- diagonal equality AC = BD
      have hAC : dist A C = dist A W + dist W C := by
        have h := dist_eq_add_dist_of_angle_eq_pi hWAC
        rw [dist_comm C W] at h
        exact h
      have hBD : dist B D = dist B W + dist W D := by
        have h := dist_eq_add_dist_of_angle_eq_pi hWBD
        rw [dist_comm D W] at h
        exact h
      have hWA' : dist A W = dist W D := by
        rw [dist_comm A W]
        exact hWA
      have hWB' : dist B W = dist W C := by
        rw [dist_comm B W]
        exact hWB
      have hACBD : dist A C = dist B D := by
        linarith [hAC, hBD, hWA', hWB']
      -- ## subtraction via the two hOrd angle additions
      have e1 : Real.sin (∠ A E C) = dist A C / (2 * R) := hsin mA mE mC nAE nAC nCE.symm
      have e2 : Real.sin (∠ B E D) = dist B D / (2 * R) := hsin mB mE mD nBE nBD nDE.symm
      have hsAE : Real.sin (∠ A E C) = Real.sin (∠ B E D) := by
        rw [e1, e2, hACBD]
      rw [← hOrdE1, ← hOrdE2, Real.sin_add, Real.sin_add] at hsAE
      have e3 : Real.sin (∠ A E B) = dist A B / (2 * R) := hsin mA mE mB nAE nAB nBE.symm
      have e4 : Real.sin (∠ C E D) = dist C D / (2 * R) := hsin mC mE mD nCE nCD nDE.symm
      have e5 : Real.sin (∠ B E C) = dist B C / (2 * R) := hsin mB mE mC nBE nBC nCE.symm
      rw [e3, e4, e5, hAB] at hsAE
      have key : Real.cos (∠ C E D) * dist B C + Real.cos (∠ B E C) * dist C D =
          Real.cos (∠ A E B) * dist B C + Real.cos (∠ B E C) * dist C D := by
        field_simp [hRpos.ne'] at hsAE
        linear_combination -hsAE
      have hBCne : dist B C ≠ 0 := dist_ne_zero.mpr nBC
      have key2 : Real.cos (∠ A E B) * dist B C = Real.cos (∠ C E D) * dist B C := by
        linear_combination -key
      have key3 : Real.cos (∠ A E B) = Real.cos (∠ C E D) := mul_right_cancel₀ hBCne key2
      rw [angle_comm B E A]
      exact key3.symm
    rw [hA, hB]
  -- ## K4': dist Y E * dist C E = dist A E * dist D E
  have hK4' : dist Y E * dist C E = dist A E * dist D E := by
    have h1 : dist A E = dist Y A * Real.cos (∠ D A E) + dist Y E * Real.cos (∠ C A D) := by
      rw [hprojAE, ← hCQ2]
    have h2 : dist A E * dist D E = dist Y E * (dist A B * Real.cos (∠ D A E) + dist D E * Real.cos (∠ C A D)) := by
      have h1d := congrArg (· * dist D E) h1
      linear_combination h1d + Real.cos (∠ D A E) * hM1
    rw [hAB, ← hRELA2] at h2
    exact h2.symm
  -- ## COSREL2: cos(∠ F C E) = cos(∠ C E D)   [geometric: the isoceles trapezoid]
  have hC2 : Real.cos (∠ F C E) = Real.cos (∠ C E D) := by
    have sZCE : Sbtw ℝ C Z E := angle_eq_pi_iff_sbtw.mp hZCE
    have sZDF : Sbtw ℝ D Z F := angle_eq_pi_iff_sbtw.mp hZDF
    -- ZD = ZE via the law of sines in △ZDE
    have e1 : Real.sin (∠ Z D E) = dist F E / (2 * R) := by
      rw [sZDF.angle_eq_left E]
      exact hsin mF mD mE nDF.symm nEF.symm nDE
    have e2 : Real.sin (∠ D E Z) = dist C D / (2 * R) := by
      rw [angle_comm D E Z, (sZCE.symm).angle_eq_left D]
      exact hsin mC mE mD nCE nCD nDE.symm
    have l1 := law_sin D Z E
    have l2 := law_sin E Z D
    rw [angle_comm E D Z] at l1
    rw [e1] at l1; rw [e2] at l2
    rw [hEF] at l2
    rw [angle_comm E Z D] at l2
    rw [dist_comm E F, dist_comm D E] at l2
    have hs1 : Real.sin (∠ D Z E) ≠ 0 := by
      have hnc : ¬ Collinear ℝ ({D, Z, E} : Set _) :=
        not_collinear_of_sbtw_of_not_collinear sZDF (ncl sD sF sE nDF nEF.symm nDE)
      exact (sin_angle_pos_of_not_collinear hnc).ne'
    have hZD : dist Z D = dist Z E := by
      have key : Real.sin (∠ D Z E) * dist Z E = Real.sin (∠ D Z E) * dist Z D := by
        linear_combination l1 - l2
      exact (mul_left_cancel₀ hs1 key).symm
    -- ZC = ZF via the law of sines in △ZCF
    have e3 : Real.sin (∠ Z C F) = dist E F / (2 * R) := by
      rw [sZCE.angle_eq_left F]
      exact hsin mE mC mF nCE.symm nEF nCF
    have e4 : Real.sin (∠ C F Z) = dist D C / (2 * R) := by
      rw [angle_comm C F Z, (sZDF.symm).angle_eq_left C]
      exact hsin mD mF mC nDF nCD.symm nCF.symm
    have l3 := law_sin C Z F
    have l4 := law_sin F Z C
    rw [angle_comm F C Z] at l3
    rw [e3] at l3; rw [e4] at l4
    have hEF' : dist D C = dist E F := (dist_comm D C).trans hEF
    rw [hEF'] at l4
    rw [angle_comm F Z C] at l4
    rw [dist_comm C F] at l4
    have hs2 : Real.sin (∠ C Z F) ≠ 0 := by
      have hnc : ¬ Collinear ℝ ({C, Z, F} : Set _) :=
        not_collinear_of_sbtw_of_not_collinear sZCE (ncl sC sE sF nCE nEF nCF)
      exact (sin_angle_pos_of_not_collinear hnc).ne'
    have hZF : dist Z C = dist Z F := by
      have key : Real.sin (∠ C Z F) * dist Z F = Real.sin (∠ C Z F) * dist Z C := by
        linear_combination l3 - l4
      exact (mul_left_cancel₀ hs2 key).symm
    -- isoceles base angles
    have hbase1 : ∠ Z D E = ∠ Z E D := angle_eq_angle_of_dist_eq hZD
    have hbase2 : ∠ Z C F = ∠ Z F C := angle_eq_angle_of_dist_eq hZF
    have hvert : ∠ D Z E = ∠ F Z C :=
      angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi hZDF (by rw [angle_comm E Z C]; exact hZCE)
    have hsum1 : ∠ Z D E + ∠ Z E D + ∠ D Z E = π := by
      have h := angle_add_angle_add_angle_eq_pi E sZDF.left_ne
      rw [angle_comm D E Z, angle_comm E Z D] at h
      linarith [h]
    have hsum2 : ∠ Z C F + ∠ Z F C + ∠ C Z F = π := by
      have h := angle_add_angle_add_angle_eq_pi F sZCE.left_ne
      rw [angle_comm C F Z, angle_comm F Z C] at h
      linarith [h]
    have hang : ∠ Z E D = ∠ Z C F := by
      linarith [hbase1, hbase2, hvert, hsum1, hsum2, angle_comm F Z C]
    -- translate back to the required angles
    have e5 : ∠ Z E D = ∠ C E D := (sZCE.symm).angle_eq_left D
    have e6 : ∠ Z C F = ∠ E C F := sZCE.angle_eq_left F
    rw [e5, e6] at hang
    rw [angle_comm F C E]
    exact congrArg Real.cos hang.symm
  -- ## K4'': dist A B * dist C E = dist Y D * dist A E
  have hK4'' : dist A B * dist C E = dist Y D * dist A E := by
    have step1 : dist A B * dist C E = dist Y C * dist A B * Real.cos (∠ C E D) +
        dist Y E * dist A B * Real.cos (∠ B E C) := by
      linear_combination (dist A B) * hproj + (dist Y C * dist A B) * hC2
    have step2 : dist Y C * dist A B * Real.cos (∠ C E D) = dist Y E * dist B C * Real.cos (∠ C E D) := by
      rw [hM2]
    have step3 : dist Y E * dist B D = dist Y E * dist B C * Real.cos (∠ C E D) +
        dist Y E * dist A B * Real.cos (∠ B E C) := by
      linear_combination (dist Y E) * hREL1'
    have step4 : dist Y E * dist B D = dist Y D * dist A E := hJ4.symm
    linarith [step1, step2, step3, step4]
  -- ## K1a: dist Y A * dist C E = dist A E * dist A B
  have hK1a : dist Y A * dist C E = dist A E * dist A B := by
    have h1 : dist Y A * dist C E * dist D E = dist A E * dist A B * dist D E := by
      linear_combination (dist C E) * hM1 + (dist A B) * hK4'
    exact mul_right_cancel₀ (dist_ne_zero.mpr nDE) h1
  -- ## K1: dist Y D * dist C E = dist A C * dist D E
  have hK1 : dist Y D * dist C E = dist A C * dist D E := by
    have had : dist A D = dist Y A + dist Y D := by
      have h := dist_eq_add_dist_of_angle_eq_pi hYAD
      rw [dist_comm A Y, dist_comm D Y] at h
      exact h
    rw [had, ← hAB, dist_comm E A] at hE1
    linear_combination -hE1 - hK1a
  -- ## goalB: dist A B * dist C E ^ 2 = dist A C * dist A E * dist D E
  have hgoalB : dist A B * dist C E ^ 2 = dist A C * dist A E * dist D E := by
    calc dist A B * dist C E ^ 2 = (dist A B * dist C E) * dist C E := by ring
      _ = (dist Y D * dist A E) * dist C E := by rw [hK4'']
      _ = dist Y D * dist C E * dist A E := by ring
      _ = dist A C * dist D E * dist A E := by rw [hK1]
      _ = dist A C * dist A E * dist D E := by ring
  -- ## final assembly
  have hXE : dist X E ≠ 0 := dist_ne_zero.mpr sXCE.right_ne.symm
  have hCE' : dist C E ≠ 0 := dist_ne_zero.mpr nCE
  have hfin : dist X C * dist C E ^ 2 = dist X E * dist A C ^ 2 := by
    have hrd : dist A E * dist D E ≠ 0 := mul_ne_zero (dist_ne_zero.mpr nAE) (dist_ne_zero.mpr nDE)
    have key : (dist A E * dist D E) * (dist X C * dist C E ^ 2) =
        (dist A E * dist D E) * (dist X E * dist A C ^ 2) := by
      linear_combination (dist C E ^ 2) * hgoalA + (dist X E * dist A C) * hgoalB
    exact mul_left_cancel₀ hrd key
  rw [dist_comm C X, div_pow]
  rw [div_eq_div_iff hXE (pow_ne_zero 2 hCE')]
  linear_combination hfin

end Usa1994P3
