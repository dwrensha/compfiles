/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Geometry.Euclidean.Angle.Sphere
public import Mathlib.Geometry.Euclidean.Triangle
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 2020, Problem 1

Consider the convex quadrilateral ABCD. The point P is in the interior of ABCD.
The following ratio equalities hold:

  ∠PAD : ∠PBA : ∠DPA = 1 : 2 : 3 = ∠CBP : ∠BAP : ∠BPC.

Prove that the following three lines meet in a point: the internal bisectors
of angles ∠ADP and ∠PCB and the perpendicular bisector of segment AB.
-/

namespace Imo2020P1

open scoped EuclideanGeometry

snip begin

open EuclideanGeometry

-- We need some instances in order to talk about oriented angles.

local instance planeFiniteDim :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
  ⟨finrank_euclideanSpace_fin⟩

noncomputable local instance someOrientation :
    Module.Oriented ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2) :=
  ⟨Module.Basis.orientation (Module.finBasisOfFinrankEq _ _ planeFiniteDim.out)⟩

/-- The circumcenter `O` of `△PAB` lies on the internal bisector of `∠PCB`,
following the angle chase of the official solution: `BOPC` is concyclic and
`OP = OB`, so the chords `OP` and `OB` subtend equal angles at `C`. -/
lemma bisector_at_C
    {A B C P O : EuclideanSpace ℝ (Fin 2)}
    (hOA : dist O A = dist O P) (hOB : dist O B = dist O P)
    (hABP : ¬Collinear ℝ ({A, B, P} : Set (EuclideanSpace ℝ (Fin 2))))
    (hBCP : ¬Collinear ℝ ({B, C, P} : Set (EuclideanSpace ℝ (Fin 2))))
    (hsCBP : (∡ C B P).sign = 1) (hsBPC : (∡ B P C).sign = 1) (hsBAP : (∡ B A P).sign = 1)
    (hS1 : line[ℝ, P, C].SSameSide O B) (hS2 : line[ℝ, C, B].SSameSide O P)
    (hratio : ∃ y : ℝ, 0 < y ∧ ∠ C B P = y ∧ ∠ B A P = 2 * y ∧ ∠ B P C = 3 * y) :
    ∠ P C O = ∠ P C B / 2 := by
  obtain ⟨y, hy0, hyCBP, hyBAP, hyBPC⟩ := hratio
  -- distinctness of points
  obtain ⟨hBCP0, -⟩ := oangle_ne_zero_and_ne_pi_iff_not_collinear.2 hBCP
  have hBC : B ≠ C := left_ne_of_oangle_ne_zero hBCP0
  have hCP : C ≠ P := (right_ne_of_oangle_ne_zero hBCP0).symm
  have hBP : B ≠ P := left_ne_right_of_oangle_ne_zero hBCP0
  obtain ⟨hABP0, -⟩ := oangle_ne_zero_and_ne_pi_iff_not_collinear.2 hABP
  have hAB : A ≠ B := left_ne_of_oangle_ne_zero hABP0
  have hAP : A ≠ P := left_ne_right_of_oangle_ne_zero hABP0
  have hCO : C ≠ O := by
    intro h
    have hd : dist C P = dist C B := by rw [h]; exact hOB.symm
    have hang := angle_eq_angle_of_dist_eq hd
    rw [angle_comm C P B, hyBPC, hyCBP] at hang
    linarith
  have hBO : B ≠ O := by
    intro h
    have h1 : dist O B = 0 := by rw [h]; exact dist_self O
    have h2 : dist O P = 0 := hOB ▸ h1
    have h3 : O = P := dist_eq_zero.1 h2
    exact hBP (h.trans h3)
  have hPO : P ≠ O := by
    intro h
    have h1 : dist O P = 0 := by rw [h]; exact dist_self O
    have h2 : dist O A = 0 := hOA ▸ h1
    have h3 : O = A := dist_eq_zero.1 h2
    exact hAP (h.trans h3).symm
  -- the angle at the center of the circle through `A`, `B`, `P` is twice the
  -- angle at the circumference
  have hinsc : ∡ B O P = (2 : ℤ) • ∡ B A P :=
    Sphere.oangle_center_eq_two_zsmul_oangle
      (s := (⟨O, dist P O⟩ : Sphere (EuclideanSpace ℝ (Fin 2))))
      (p₁ := B) (p₂ := A) (p₃ := P)
      (mem_sphere.2 (show dist B O = dist P O by rw [dist_comm B O, hOB, dist_comm P O]))
      (mem_sphere.2 (show dist A O = dist P O by rw [dist_comm A O, hOA, dist_comm P O]))
      (mem_sphere.2 rfl) hAB hAP
  -- oriented values of the given angles, from their signs
  have hvCBP : ∡ C B P = ((y : ℝ) : Real.Angle) := by
    rw [oangle_eq_angle_of_sign_eq_one hsCBP, hyCBP]
  have hvBPC : ∡ B P C = ((3 * y : ℝ) : Real.Angle) := by
    rw [oangle_eq_angle_of_sign_eq_one hsBPC, hyBPC]
  have hvBAP : ∡ B A P = ((2 * y : ℝ) : Real.Angle) := by
    rw [oangle_eq_angle_of_sign_eq_one hsBAP, hyBAP]
  -- oriented angle sum of the triangle `BCP`
  have htri : ∡ B C P + ∡ C P B + ∡ P B C = (Real.pi : Real.Angle) :=
    oangle_add_oangle_add_oangle_eq_pi hBC.symm hCP.symm hBP
  have hvBCP : ∡ B C P = ((Real.pi + 4 * y : ℝ) : Real.Angle) := by
    calc ∡ B C P = ∡ B C P + ∡ C P B + ∡ P B C - ∡ C P B - ∡ P B C := by abel
      _ = (Real.pi : Real.Angle) + ∡ B P C + ∡ C B P := by
        rw [htri, oangle_rev B P C, oangle_rev C B P]; abel
      _ = ((Real.pi + 4 * y : ℝ) : Real.Angle) := by
        rw [hvBPC, hvCBP]; simp only [← Real.Angle.coe_add]; congr 1; ring
  -- `2 • ∡BCP = 2 • ∡BOP`, so `BOPC` is concyclic
  have h2eq : (2 : ℤ) • ∡ B C P = (2 : ℤ) • ∡ B O P := by
    rw [hvBCP, hinsc, hvBAP, smul_smul, ← Real.Angle.coe_zsmul, ← Real.Angle.coe_zsmul,
      Real.Angle.angle_eq_iff_two_pi_dvd_sub]
    exact ⟨1, by simp only [zsmul_eq_mul]; ring⟩
  have hcyc : Cospherical ({B, C, O, P} : Set (EuclideanSpace ℝ (Fin 2))) :=
    cospherical_of_two_zsmul_oangle_eq_of_not_collinear h2eq hBCP
  have hcyc' : Cospherical ({P, C, B, O} : Set (EuclideanSpace ℝ (Fin 2))) :=
    hcyc.subset (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)
  have hcyc'' : Cospherical ({B, C, P, O} : Set (EuclideanSpace ℝ (Fin 2))) :=
    hcyc.subset (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)
  -- angles subtending the chords `PO` and `BO`
  have hchord1 : (2 : ℤ) • ∡ P C O = (2 : ℤ) • ∡ P B O :=
    hcyc'.two_zsmul_oangle_eq hCP hCO hBP hBO
  have hchord2 : (2 : ℤ) • ∡ B C O = (2 : ℤ) • ∡ B P O :=
    hcyc''.two_zsmul_oangle_eq hBC.symm hCO hBP.symm hPO
  -- the triangle `OPB` is isosceles
  have hiso : ∡ O P B = ∡ P B O := oangle_eq_oangle_of_dist_eq hOB.symm
  have h2final : (2 : ℤ) • ∡ P C O = (2 : ℤ) • ∡ O C B := by
    have hr3 : ∡ B P O = -∡ O P B := oangle_rev O P B
    have hr4 : ∡ O C B = -∡ B C O := oangle_rev B C O
    rw [hchord1, ← hiso, hr4, smul_neg, hchord2, hr3, smul_neg, neg_neg]
  -- the two oriented angles have the same sign
  have hsgn1 : (∡ P C O).sign = 1 := by
    have h := hS1.oangle_sign_eq (left_mem_affineSpan_pair ℝ P C)
      (right_mem_affineSpan_pair ℝ P C)
    have e1 : (∡ P B C).sign = -1 := by rw [← oangle_swap₁₃_sign C B P, hsCBP]
    have e2 : (∡ P O C).sign = -1 := h ▸ e1
    rw [← oangle_swap₂₃_sign P O C, e2, neg_neg]
  have hsgn2 : (∡ O C B).sign = 1 := by
    have h := hS2.oangle_sign_eq (left_mem_affineSpan_pair ℝ C B)
      (right_mem_affineSpan_pair ℝ C B)
    have e1 : (∡ C P B).sign = -1 := by rw [← oangle_swap₁₃_sign B P C, hsBPC]
    have e2 : (∡ C O B).sign = -1 := h ▸ e1
    rw [← oangle_rotate_sign O C B, ← oangle_swap₂₃_sign C O B, e2, neg_neg]
  have hOeq : ∡ P C O = ∡ O C B :=
    (Real.Angle.two_zsmul_eq_iff_eq (by rw [hsgn1]; exact one_ne_zero)
      (hsgn1.trans hsgn2.symm)).1 h2final
  exact angle_eq_angle_div_two_of_oangle_eq_of_sSameSide hCP.symm hOeq hS1

/-- The circumcenter `O` of `△PAB` lies on the internal bisector of `∠ADP`;
the mirror image of `bisector_at_C`. -/
lemma bisector_at_D
    {A B D P O : EuclideanSpace ℝ (Fin 2)}
    (hOA : dist O A = dist O P) (hOB : dist O B = dist O P)
    (hABP : ¬Collinear ℝ ({A, B, P} : Set (EuclideanSpace ℝ (Fin 2))))
    (hADP : ¬Collinear ℝ ({A, D, P} : Set (EuclideanSpace ℝ (Fin 2))))
    (hsPAD : (∡ P A D).sign = 1) (hsPBA : (∡ P B A).sign = 1) (hsDPA : (∡ D P A).sign = 1)
    (hS3 : line[ℝ, A, D].SSameSide O P) (hS4 : line[ℝ, D, P].SSameSide O A)
    (hratio : ∃ x : ℝ, 0 < x ∧ ∠ P A D = x ∧ ∠ P B A = 2 * x ∧ ∠ D P A = 3 * x) :
    ∠ A D O = ∠ A D P / 2 := by
  obtain ⟨x, hx0, hxPAD, hxPBA, hxDPA⟩ := hratio
  -- distinctness of points
  obtain ⟨hADP0, -⟩ := oangle_ne_zero_and_ne_pi_iff_not_collinear.2 hADP
  have hAD : A ≠ D := left_ne_of_oangle_ne_zero hADP0
  have hDP : D ≠ P := (right_ne_of_oangle_ne_zero hADP0).symm
  have hAP : A ≠ P := left_ne_right_of_oangle_ne_zero hADP0
  obtain ⟨hABP0, -⟩ := oangle_ne_zero_and_ne_pi_iff_not_collinear.2 hABP
  have hAB : A ≠ B := left_ne_of_oangle_ne_zero hABP0
  have hBP : B ≠ P := (right_ne_of_oangle_ne_zero hABP0).symm
  have hDO : D ≠ O := by
    intro h
    have hd : dist D P = dist D A := by rw [h]; exact hOA.symm
    have hang := angle_eq_angle_of_dist_eq hd
    rw [angle_comm D A P, hxDPA, hxPAD] at hang
    linarith
  have hAO : A ≠ O := by
    intro h
    have h1 : dist O A = 0 := by rw [h]; exact dist_self O
    have h2 : dist O P = 0 := hOA ▸ h1
    have h3 : O = P := dist_eq_zero.1 h2
    exact hAP (h.trans h3)
  have hPO : P ≠ O := by
    intro h
    have h1 : dist O P = 0 := by rw [h]; exact dist_self O
    have h2 : dist O A = 0 := hOA ▸ h1
    have h3 : O = A := dist_eq_zero.1 h2
    exact hAP (h.trans h3).symm
  -- the angle at the center of the circle through `A`, `B`, `P` is twice the
  -- angle at the circumference
  have hinsc : ∡ A O P = (2 : ℤ) • ∡ A B P :=
    Sphere.oangle_center_eq_two_zsmul_oangle
      (s := (⟨O, dist P O⟩ : Sphere (EuclideanSpace ℝ (Fin 2))))
      (p₁ := A) (p₂ := B) (p₃ := P)
      (mem_sphere.2 (show dist A O = dist P O by rw [dist_comm A O, hOA, dist_comm P O]))
      (mem_sphere.2 (show dist B O = dist P O by rw [dist_comm B O, hOB, dist_comm P O]))
      (mem_sphere.2 rfl) hAB.symm hBP
  -- oriented values of the given angles, from their signs
  have hvPAD : ∡ P A D = ((x : ℝ) : Real.Angle) := by
    rw [oangle_eq_angle_of_sign_eq_one hsPAD, hxPAD]
  have hvPBA : ∡ P B A = ((2 * x : ℝ) : Real.Angle) := by
    rw [oangle_eq_angle_of_sign_eq_one hsPBA, hxPBA]
  have hvDPA : ∡ D P A = ((3 * x : ℝ) : Real.Angle) := by
    rw [oangle_eq_angle_of_sign_eq_one hsDPA, hxDPA]
  have hvABP : ∡ A B P = ((-2 * x : ℝ) : Real.Angle) := by
    rw [oangle_rev P B A, hvPBA, ← Real.Angle.coe_neg]; congr 1; ring
  -- oriented angle sum of the triangle `ADP`
  have htri : ∡ A D P + ∡ D P A + ∡ P A D = (Real.pi : Real.Angle) :=
    oangle_add_oangle_add_oangle_eq_pi hAD.symm hDP.symm hAP
  have hvADP : ∡ A D P = ((Real.pi - 4 * x : ℝ) : Real.Angle) := by
    calc ∡ A D P = ∡ A D P + ∡ D P A + ∡ P A D - ∡ D P A - ∡ P A D := by abel
      _ = (Real.pi : Real.Angle) + -(∡ D P A) + -(∡ P A D) := by rw [htri]; abel
      _ = ((Real.pi - 4 * x : ℝ) : Real.Angle) := by
        rw [hvDPA, hvPAD]; simp only [← Real.Angle.coe_add, ← Real.Angle.coe_neg]; congr 1; ring
  -- `2 • ∡ADP = 2 • ∡AOP`, so `AOPD` is concyclic
  have h2eq : (2 : ℤ) • ∡ A D P = (2 : ℤ) • ∡ A O P := by
    rw [hvADP, hinsc, hvABP, smul_smul, ← Real.Angle.coe_zsmul, ← Real.Angle.coe_zsmul,
      Real.Angle.angle_eq_iff_two_pi_dvd_sub]
    exact ⟨1, by simp only [zsmul_eq_mul]; ring⟩
  have hcyc : Cospherical ({A, D, O, P} : Set (EuclideanSpace ℝ (Fin 2))) :=
    cospherical_of_two_zsmul_oangle_eq_of_not_collinear h2eq hADP
  have hcyc' : Cospherical ({A, D, P, O} : Set (EuclideanSpace ℝ (Fin 2))) :=
    hcyc.subset (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)
  have hcyc'' : Cospherical ({O, D, A, P} : Set (EuclideanSpace ℝ (Fin 2))) :=
    hcyc.subset (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)
  -- angles subtending the chords `AO` and `PO`
  have hchord1 : (2 : ℤ) • ∡ A D O = (2 : ℤ) • ∡ A P O :=
    hcyc'.two_zsmul_oangle_eq hAD.symm hDO hAP.symm hPO
  have hchord2 : (2 : ℤ) • ∡ O D P = (2 : ℤ) • ∡ O A P :=
    hcyc''.two_zsmul_oangle_eq hDO hDP hAO hAP
  -- the triangle `OAP` is isosceles
  have hiso : ∡ O A P = ∡ A P O := oangle_eq_oangle_of_dist_eq hOA
  have h2final : (2 : ℤ) • ∡ A D O = (2 : ℤ) • ∡ O D P := by
    rw [hchord1, ← hiso, ← hchord2]
  -- the two oriented angles have the same sign
  have hsgn1 : (∡ A D O).sign = 1 := by
    have h := hS3.oangle_sign_eq (left_mem_affineSpan_pair ℝ A D)
      (right_mem_affineSpan_pair ℝ A D)
    have e1 : (∡ A P D).sign = -1 := by rw [← oangle_swap₁₃_sign D P A, hsDPA]
    have e2 : (∡ A O D).sign = -1 := h ▸ e1
    rw [← oangle_swap₂₃_sign A O D, e2, neg_neg]
  have hsgn2 : (∡ O D P).sign = 1 := by
    have h := hS4.oangle_sign_eq (left_mem_affineSpan_pair ℝ D P)
      (right_mem_affineSpan_pair ℝ D P)
    have e1 : (∡ D A P).sign = -1 := by rw [← oangle_swap₁₃_sign P A D, hsPAD]
    have e2 : (∡ D O P).sign = -1 := h ▸ e1
    rw [← oangle_rotate_sign O D P, ← oangle_swap₂₃_sign D O P, e2, neg_neg]
  have hOeq : ∡ A D O = ∡ O D P :=
    (Real.Angle.two_zsmul_eq_iff_eq (by rw [hsgn1]; exact one_ne_zero)
      (hsgn1.trans hsgn2.symm)).1 h2final
  exact angle_eq_angle_div_two_of_oangle_eq_of_sSameSide hAD hOeq hS3

snip end

problem imo2020_p1
    (A B C D P O : EuclideanSpace ℝ (Fin 2))
    -- `O` is equidistant from `A`, `B` and `P`: it is the circumcenter of `△PAB`.
    (hOA : dist O A = dist O P) (hOB : dist O B = dist O P)
    -- the triangles `PAB`, `BCP` and `ADP` are nondegenerate
    (hABP : ¬Collinear ℝ ({A, B, P} : Set (EuclideanSpace ℝ (Fin 2))))
    (hBCP : ¬Collinear ℝ ({B, C, P} : Set (EuclideanSpace ℝ (Fin 2))))
    (hADP : ¬Collinear ℝ ({A, D, P} : Set (EuclideanSpace ℝ (Fin 2))))
    -- the configuration is positively oriented (`P` inside the convex
    -- quadrilateral `ABCD`)
    (hsCBP : (∡ C B P).sign = 1) (hsBPC : (∡ B P C).sign = 1) (hsBAP : (∡ B A P).sign = 1)
    (hsPAD : (∡ P A D).sign = 1) (hsPBA : (∡ P B A).sign = 1) (hsDPA : (∡ D P A).sign = 1)
    -- `O` and the relevant vertices lie on the same side of the sides
    (hS1 : line[ℝ, P, C].SSameSide O B) (hS2 : line[ℝ, C, B].SSameSide O P)
    (hS3 : line[ℝ, A, D].SSameSide O P) (hS4 : line[ℝ, D, P].SSameSide O A)
    -- the angle ratio conditions
    (hratioD : ∃ x : ℝ, 0 < x ∧ ∠ P A D = x ∧ ∠ P B A = 2 * x ∧ ∠ D P A = 3 * x)
    (hratioC : ∃ y : ℝ, 0 < y ∧ ∠ C B P = y ∧ ∠ B A P = 2 * y ∧ ∠ B P C = 3 * y) :
    O ∈ AffineSubspace.perpBisector A B ∧ ∠ P C O = ∠ P C B / 2 ∧ ∠ A D O = ∠ A D P / 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [AffineSubspace.mem_perpBisector_iff_dist_eq]
    exact hOA.trans hOB.symm
  · exact bisector_at_C hOA hOB hABP hBCP hsCBP hsBPC hsBAP hS1 hS2 hratioC
  · exact bisector_at_D hOA hOB hABP hADP hsPAD hsPBA hsDPA hS3 hS4 hratioD

end Imo2020P1
