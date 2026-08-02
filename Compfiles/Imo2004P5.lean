/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
public import Mathlib.Geometry.Euclidean.Sphere.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 2004, Problem 5

In a convex quadrilateral `ABCD`, the diagonal `BD` bisects neither the angle
`ABC` nor the angle `CDA`. The point `P` lies inside `ABCD` and satisfies
`∠PBC = ∠DBA` and `∠PDC = ∠BDA`. Prove that `ABCD` is a cyclic quadrilateral
if and only if `AP = CP`.
-/

namespace Imo2004P5

open scoped EuclideanGeometry RealInnerProductSpace

open EuclideanGeometry

local instance planeFiniteDim :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
  ⟨finrank_euclideanSpace_fin⟩

noncomputable local instance someOrientation :
    Module.Oriented ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2) :=
  ⟨Module.Basis.orientation (Module.finBasisOfFinrankEq _ _ planeFiniteDim.out)⟩

/-- The Euclidean plane. -/
abbrev E2 := EuclideanSpace ℝ (Fin 2)

snip begin

/-- The 2D determinant `u₀v₁ - u₁v₀` (signed area form) on the plane. -/
def cr (u v : E2) : ℝ := u 0 * v 1 - u 1 * v 0

@[simp] lemma cr_self (u : E2) : cr u u = 0 := by simp [cr]; ring

lemma cr_anti (u v : E2) : cr u v = -cr v u := by simp [cr]; ring

lemma cr_add_left (u v w : E2) : cr (u + v) w = cr u w + cr v w := by
  simp [cr]; ring

lemma cr_add_right (u v w : E2) : cr u (v + w) = cr u v + cr u w := by
  simp [cr]; ring

lemma cr_sub_left (u v w : E2) : cr (u - v) w = cr u w - cr v w := by
  simp [cr]; ring

lemma cr_sub_right (u v w : E2) : cr u (v - w) = cr u v - cr u w := by
  simp [cr]; ring

lemma cr_smul_left (c : ℝ) (u v : E2) : cr (c • u) v = c * cr u v := by
  simp [cr, smul_eq_mul]; ring

lemma cr_smul_right (c : ℝ) (u v : E2) : cr u (c • v) = c * cr u v := by
  simp [cr, smul_eq_mul]; ring

@[simp] lemma cr_zero_left (v : E2) : cr 0 v = 0 := by simp [cr]
@[simp] lemma cr_zero_right (u : E2) : cr u 0 = 0 := by simp [cr]

lemma cr_neg_left (u v : E2) : cr (-u) v = -cr u v := by
  rw [← neg_one_smul ℝ u, cr_smul_left]; simp

lemma cr_neg_right (u v : E2) : cr u (-v) = -cr u v := by
  rw [← neg_one_smul ℝ v, cr_smul_right]; simp

/-- If two independent linear equations `cr w v = 0`, `cr u w = 0` hold with
`cr u v ≠ 0`, then `w = 0`. -/
lemma eq_zero_of_cr_eq_zero_of_cr_eq_zero {u v w : E2}
    (hΩ : cr u v ≠ 0) (h1 : cr w v = 0) (h2 : cr u w = 0) : w = 0 := by
  have hw0 : w 0 = 0 := by
    have h : w 0 * cr u v = 0 := by
      simp only [cr] at h1 h2 ⊢
      linear_combination u 0 * h1 + v 0 * h2
    exact mul_eq_zero.mp h |>.resolve_right hΩ
  have hw1 : w 1 = 0 := by
    have h : w 1 * cr u v = 0 := by
      simp only [cr] at h1 h2 ⊢
      linear_combination u 1 * h1 + v 1 * h2
    exact mul_eq_zero.mp h |>.resolve_right hΩ
  ext i
  fin_cases i <;> simp [hw0, hw1]

/-- Lagrange's identity: `cr u v` squared plus `⟪u,v⟫` squared is `‖u‖²‖v‖²`. -/
lemma cr_sq_eq (u v : E2) :
    cr u v ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2 := by
  have hnu : ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 := by
    rw [EuclideanSpace.norm_eq]
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
    simp [Fin.sum_univ_two]
  have hnv : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
    rw [EuclideanSpace.norm_eq]
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
    simp [Fin.sum_univ_two]
  have hin : ⟪u, v⟫ = u 0 * v 0 + u 1 * v 1 := by
    rw [PiLp.inner_apply, Fin.sum_univ_two]
    simp [RCLike.inner_apply, mul_comm]
  rw [hnu, hnv, hin]
  simp [cr]
  ring

/-- `ConvexQuadrilateral A B C D` says the four points are the vertices of a
convex quadrilateral listed in cyclic order, expressed by saying that the
diagonals strictly separate opposite vertices: `A` and `C` lie on opposite
sides of the line `BD`, and `B` and `D` lie on opposite sides of the line `AC`
(equivalently, the segments `AC` and `BD` cross). -/
structure ConvexQuadrilateral (A B C D : E2) : Prop where
  diag_BD : cr (D - B) (A - B) * cr (D - B) (C - B) < 0
  diag_AC : cr (C - A) (B - A) * cr (C - A) (D - A) < 0

namespace ConvexQuadrilateral

/-- Component-level `cr` identities used to move between reference points. -/
lemma cr_DBAC_eq (A B D : E2) :
    cr (D - B) (A - B) = cr (B - A) (D - A) := by simp [cr]; ring

lemma edge_AB {A B C D : E2} (h : ConvexQuadrilateral A B C D) :
    0 < cr (C - B) (A - B) * cr (D - B) (A - B) := by
  obtain ⟨h1, h2⟩ := h
  have e1 : cr (C - A) (B - A) = -cr (C - B) (A - B) := by simp [cr]; ring
  have e2 : cr (C - A) (D - A) = cr (D - C) (A - C) := by simp [cr]; ring
  have e3 : cr (D - B) (C - B)
      = cr (D - B) (A - B) - cr (C - B) (A - B) - cr (D - C) (A - C) := by
    simp [cr]; ring
  rw [e3] at h1
  rw [e1, e2] at h2
  have hu : cr (C - B) (A - B) ≠ 0 := by
    rintro hz
    rw [hz] at h2
    simp at h2
  rcases lt_or_gt_of_ne hu with hun | hup
  · have hwn : cr (D - C) (A - C) < 0 := by nlinarith [h2, hun]
    have hvn : cr (D - B) (A - B) < 0 := by nlinarith [h1, hun, hwn]
    nlinarith [hun, hvn]
  · have hwp : 0 < cr (D - C) (A - C) := by nlinarith [h2, hup]
    have hvp : 0 < cr (D - B) (A - B) := by nlinarith [h1, hup, hwp]
    nlinarith [hup, hvp]

lemma edge_BC {A B C D : E2} (h : ConvexQuadrilateral A B C D) :
    0 < cr (C - B) (A - B) * cr (C - B) (D - B) := by
  obtain ⟨h1, h2⟩ := h
  have e1 : cr (C - A) (B - A) = -cr (C - B) (A - B) := by simp [cr]; ring
  have e2 : cr (C - A) (D - A) = cr (D - C) (A - C) := by simp [cr]; ring
  have e3 : cr (D - B) (C - B)
      = cr (D - B) (A - B) - cr (C - B) (A - B) - cr (D - C) (A - C) := by
    simp [cr]; ring
  have e4 : cr (C - B) (D - B)
      = cr (C - B) (A - B) + cr (D - C) (A - C) - cr (D - B) (A - B) := by
    simp [cr]; ring
  rw [e3] at h1
  rw [e1, e2] at h2
  rw [e4]
  have hu : cr (C - B) (A - B) ≠ 0 := by
    rintro hz
    rw [hz] at h2
    simp at h2
  rcases lt_or_gt_of_ne hu with hun | hup
  · have hwn : cr (D - C) (A - C) < 0 := by nlinarith [h2, hun]
    have hvn : cr (D - B) (A - B) < 0 := by nlinarith [h1, hun, hwn]
    have hvw : cr (C - B) (A - B) + cr (D - C) (A - C) < cr (D - B) (A - B) := by
      nlinarith [h1, hun, hwn, hvn]
    nlinarith [hun, hvw]
  · have hwp : 0 < cr (D - C) (A - C) := by nlinarith [h2, hup]
    have hvp : 0 < cr (D - B) (A - B) := by nlinarith [h1, hup, hwp]
    have hvw : cr (D - B) (A - B) < cr (C - B) (A - B) + cr (D - C) (A - C) := by
      nlinarith [h1, hup, hwp, hvp]
    nlinarith [hup, hvw]

lemma edge_CD {A B C D : E2} (h : ConvexQuadrilateral A B C D) :
    0 < cr (D - C) (A - C) * cr (D - C) (B - C) := by
  obtain ⟨h1, h2⟩ := h
  have e1 : cr (C - A) (B - A) = -cr (C - B) (A - B) := by simp [cr]; ring
  have e2 : cr (C - A) (D - A) = cr (D - C) (A - C) := by simp [cr]; ring
  have e3 : cr (D - B) (C - B)
      = cr (D - B) (A - B) - cr (C - B) (A - B) - cr (D - C) (A - C) := by
    simp [cr]; ring
  have e5 : cr (D - C) (B - C)
      = cr (C - B) (A - B) - cr (D - B) (A - B) + cr (D - C) (A - C) := by
    simp [cr]; ring
  rw [e3] at h1
  rw [e1, e2] at h2
  rw [e5]
  have hu : cr (C - B) (A - B) ≠ 0 := by
    rintro hz
    rw [hz] at h2
    simp at h2
  rcases lt_or_gt_of_ne hu with hun | hup
  · have hwn : cr (D - C) (A - C) < 0 := by nlinarith [h2, hun]
    have hvn : cr (D - B) (A - B) < 0 := by nlinarith [h1, hun, hwn]
    have hvw : cr (C - B) (A - B) + cr (D - C) (A - C) < cr (D - B) (A - B) := by
      nlinarith [h1, hun, hwn, hvn]
    nlinarith [hun, hvw]
  · have hwp : 0 < cr (D - C) (A - C) := by nlinarith [h2, hup]
    have hvp : 0 < cr (D - B) (A - B) := by nlinarith [h1, hup, hwp]
    have hvw : cr (D - B) (A - B) < cr (C - B) (A - B) + cr (D - C) (A - C) := by
      nlinarith [h1, hup, hwp, hvp]
    nlinarith [hup, hvw]

lemma edge_DA {A B C D : E2} (h : ConvexQuadrilateral A B C D) :
    0 < cr (D - C) (A - C) * cr (D - B) (A - B) := by
  obtain ⟨h1, h2⟩ := h
  have e1 : cr (C - A) (B - A) = -cr (C - B) (A - B) := by simp [cr]; ring
  have e2 : cr (C - A) (D - A) = cr (D - C) (A - C) := by simp [cr]; ring
  have e3 : cr (D - B) (C - B)
      = cr (D - B) (A - B) - cr (C - B) (A - B) - cr (D - C) (A - C) := by
    simp [cr]; ring
  rw [e3] at h1
  rw [e1, e2] at h2
  have hu : cr (C - B) (A - B) ≠ 0 := by
    rintro hz
    rw [hz] at h2
    simp at h2
  rcases lt_or_gt_of_ne hu with hun | hup
  · have hwn : cr (D - C) (A - C) < 0 := by nlinarith [h2, hun]
    have hvn : cr (D - B) (A - B) < 0 := by nlinarith [h1, hun, hwn]
    nlinarith [hwn, hvn]
  · have hwp : 0 < cr (D - C) (A - C) := by nlinarith [h2, hup]
    have hvp : 0 < cr (D - B) (A - B) := by nlinarith [h1, hup, hwp]
    nlinarith [hwp, hvp]

lemma ne_BD {A B C D : E2} (h : ConvexQuadrilateral A B C D) : B ≠ D := by
  rintro rfl
  obtain ⟨h1, _⟩ := h
  simp at h1

lemma ne_AB {A B C D : E2} (h : ConvexQuadrilateral A B C D) : A ≠ B := by
  rintro rfl
  obtain ⟨h1, _⟩ := h
  simp at h1

lemma ne_AD {A B C D : E2} (h : ConvexQuadrilateral A B C D) : A ≠ D := by
  rintro rfl
  obtain ⟨_, h2⟩ := h
  simp at h2

lemma ne_CB {A B C D : E2} (h : ConvexQuadrilateral A B C D) : C ≠ B := by
  rintro rfl
  obtain ⟨h1, _⟩ := h
  simp at h1

lemma ne_CD {A B C D : E2} (h : ConvexQuadrilateral A B C D) : C ≠ D := by
  rintro rfl
  obtain ⟨_, h2⟩ := h
  simp at h2

/-- `cr u` as a real-linear map (side-of-line functional). -/
noncomputable def crLin (u : E2) : E2 →ₗ[ℝ] ℝ where
  toFun X := cr u X
  map_add' X Y := by rw [cr_add_right]
  map_smul' c X := by simp [cr_smul_right]

/-- An interior point of the quadrilateral lies strictly on the same side of
the edge line `BC` as `A`. -/
lemma side_BC {A B C D P : E2} (h : ConvexQuadrilateral A B C D)
    (hP : P ∈ interior (convexHull ℝ ({A, B, C, D} : Set E2))) :
    0 < cr (C - B) (P - B) * cr (C - B) (A - B) := by
  have hBC := h.edge_BC
  have hσ : cr (C - B) (A - B) ≠ 0 := by
    rintro hz
    rw [hz, zero_mul] at hBC
    exact lt_irrefl 0 hBC
  set f : E2 →ₗ[ℝ] ℝ := cr (C - B) (A - B) • crLin (C - B) with hf
  have hfX : ∀ X : E2, f X = cr (C - B) (A - B) * cr (C - B) X := by
    intro X
    simp [hf, crLin, smul_eq_mul]
  have hside : ∀ X : E2, f X - f B = cr (C - B) (A - B) * cr (C - B) (X - B) := by
    intro X
    rw [hfX X, hfX B, cr_sub_right (C - B) X B]
    ring
  have hA : f B ≤ f A := by
    have h1 := hside A
    have h2 : 0 < cr (C - B) (A - B) * cr (C - B) (A - B) := mul_self_pos.mpr hσ
    linarith
  have hC : f B ≤ f C := by
    have h1 := hside C
    rw [cr_self, mul_zero] at h1
    linarith
  have hD : f B ≤ f D := by
    have h1 := hside D
    linarith
  have hsub : convexHull ℝ ({A, B, C, D} : Set E2) ⊆ ⇑f ⁻¹' Set.Ici (f B) := by
    refine convexHull_min ?_ ((convex_Ici (f B)).linear_preimage f)
    intro X hX
    have hXle : f B ≤ f X := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
      rcases hX with rfl | rfl | rfl | rfl
      · exact hA
      · exact le_rfl
      · exact hC
      · exact hD
    exact hXle
  have hPH : f B ≤ f P := hsub (interior_subset hP)
  have hne : f P ≠ f B := by
    intro hEq
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hP)
    have hδpos : 0 < ε / 2 / (‖A - B‖ + 1) := by positivity
    set δ := ε / 2 / (‖A - B‖ + 1) with hδdef
    set X := P - δ • (A - B) with hXdef
    have hdist : dist X P < ε := by
      have hnorm : (0 : ℝ) ≤ ‖A - B‖ := norm_nonneg _
      have e : X - P = -(δ • (A - B)) := by rw [hXdef]; abel
      rw [dist_eq_norm, e, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hδpos]
      have h1 : ‖A - B‖ / (‖A - B‖ + 1) < 1 := by
        rw [div_lt_one (by linarith : (0 : ℝ) < ‖A - B‖ + 1)]
        linarith
      rw [hδdef]
      have h2 : ε / 2 / (‖A - B‖ + 1) * ‖A - B‖ = ε / 2 * (‖A - B‖ / (‖A - B‖ + 1)) := by
        rw [div_mul_eq_mul_div, mul_div_assoc]
      rw [h2]
      nlinarith [h1, hε]
    have hXH : f B ≤ f X := hsub (hεsub (Metric.mem_ball.mpr hdist))
    have h1 : cr (C - B) (A - B) * cr (C - B) (P - B) = 0 := by
      have h2 := hside P
      rw [hEq, sub_self] at h2
      exact h2.symm
    have hcrX : cr (C - B) (X - B) = cr (C - B) (P - B) - δ * cr (C - B) (A - B) := by
      have e : X - B = (P - B) - δ • (A - B) := by rw [hXdef]; abel
      rw [e, cr_sub_right, cr_smul_right]
    have h2 := hside X
    rw [hcrX] at h2
    have hσ2 : 0 < cr (C - B) (A - B) * cr (C - B) (A - B) := mul_self_pos.mpr hσ
    have hδσ : 0 < δ * (cr (C - B) (A - B) * cr (C - B) (A - B)) := mul_pos hδpos hσ2
    nlinarith [hXH, h1, h2, hδσ]
  have hlt : f B < f P := lt_of_le_of_ne hPH hne.symm
  have hfin := hside P
  rw [mul_comm]
  linarith

/-- An interior point of the quadrilateral lies strictly on the same side of
the edge line `CD` as `A`. -/
lemma side_CD {A B C D P : E2} (h : ConvexQuadrilateral A B C D)
    (hP : P ∈ interior (convexHull ℝ ({A, B, C, D} : Set E2))) :
    0 < cr (D - C) (P - C) * cr (D - C) (A - C) := by
  have hCD := h.edge_CD
  have hσ : cr (D - C) (A - C) ≠ 0 := by
    rintro hz
    rw [hz, zero_mul] at hCD
    exact lt_irrefl 0 hCD
  set f : E2 →ₗ[ℝ] ℝ := cr (D - C) (A - C) • crLin (D - C) with hf
  have hfX : ∀ X : E2, f X = cr (D - C) (A - C) * cr (D - C) X := by
    intro X
    simp [hf, crLin, smul_eq_mul]
  have hside : ∀ X : E2, f X - f C = cr (D - C) (A - C) * cr (D - C) (X - C) := by
    intro X
    rw [hfX X, hfX C, cr_sub_right (D - C) X C]
    ring
  have hA : f C ≤ f A := by
    have h1 := hside A
    have h2 : 0 < cr (D - C) (A - C) * cr (D - C) (A - C) := mul_self_pos.mpr hσ
    linarith
  have hB : f C ≤ f B := by
    have h1 := hside B
    linarith
  have hD : f C ≤ f D := by
    have h1 := hside D
    rw [cr_self, mul_zero] at h1
    linarith
  have hsub : convexHull ℝ ({A, B, C, D} : Set E2) ⊆ ⇑f ⁻¹' Set.Ici (f C) := by
    refine convexHull_min ?_ ((convex_Ici (f C)).linear_preimage f)
    intro X hX
    have hXle : f C ≤ f X := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
      rcases hX with rfl | rfl | rfl | rfl
      · exact hA
      · exact hB
      · exact le_rfl
      · exact hD
    exact hXle
  have hPH : f C ≤ f P := hsub (interior_subset hP)
  have hne : f P ≠ f C := by
    intro hEq
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hP)
    have hδpos : 0 < ε / 2 / (‖A - C‖ + 1) := by positivity
    set δ := ε / 2 / (‖A - C‖ + 1) with hδdef
    set X := P - δ • (A - C) with hXdef
    have hdist : dist X P < ε := by
      have hnorm : (0 : ℝ) ≤ ‖A - C‖ := norm_nonneg _
      have e : X - P = -(δ • (A - C)) := by rw [hXdef]; abel
      rw [dist_eq_norm, e, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hδpos]
      have h1 : ‖A - C‖ / (‖A - C‖ + 1) < 1 := by
        rw [div_lt_one (by linarith : (0 : ℝ) < ‖A - C‖ + 1)]
        linarith
      rw [hδdef]
      have h2 : ε / 2 / (‖A - C‖ + 1) * ‖A - C‖ = ε / 2 * (‖A - C‖ / (‖A - C‖ + 1)) := by
        rw [div_mul_eq_mul_div, mul_div_assoc]
      rw [h2]
      nlinarith [h1, hε]
    have hXH : f C ≤ f X := hsub (hεsub (Metric.mem_ball.mpr hdist))
    have h1 : cr (D - C) (A - C) * cr (D - C) (P - C) = 0 := by
      have h2 := hside P
      rw [hEq, sub_self] at h2
      exact h2.symm
    have hcrX : cr (D - C) (X - C) = cr (D - C) (P - C) - δ * cr (D - C) (A - C) := by
      have e : X - C = (P - C) - δ • (A - C) := by rw [hXdef]; abel
      rw [e, cr_sub_right, cr_smul_right]
    have h2 := hside X
    rw [hcrX] at h2
    have hσ2 : 0 < cr (D - C) (A - C) * cr (D - C) (A - C) := mul_self_pos.mpr hσ
    have hδσ : 0 < δ * (cr (D - C) (A - C) * cr (D - C) (A - C)) := mul_pos hδpos hσ2
    nlinarith [hXH, h1, h2, hδσ]
  have hlt : f C < f P := lt_of_le_of_ne hPH hne.symm
  have hfin := hside P
  rw [mul_comm]
  linarith

lemma ne_PB {A B C D P : E2} (h : ConvexQuadrilateral A B C D)
    (hP : P ∈ interior (convexHull ℝ ({A, B, C, D} : Set E2))) : P ≠ B := by
  rintro rfl
  have h1 := h.side_BC hP
  simp at h1

lemma ne_PD {A B C D P : E2} (h : ConvexQuadrilateral A B C D)
    (hP : P ∈ interior (convexHull ℝ ({A, B, C, D} : Set E2))) : P ≠ D := by
  rintro rfl
  have h1 := h.side_CD hP
  simp at h1

end ConvexQuadrilateral

/-! ### Barycentric coordinates with respect to `P, B, D`

Any point `X` of the plane has a unique representation
`X = P + sc P B D X • (B - P) + tc P B D X • (D - P)` when `P, B, D` are not
collinear; we also set `xc P B D X = 1 - sc - tc`, the coefficient of `P`. -/

/-- The `B`-coordinate of `X` in the affine basis `P, B, D`. -/
noncomputable def sc (P B D X : E2) : ℝ := cr (X - P) (D - P) / cr (B - P) (D - P)

/-- The `D`-coordinate of `X` in the affine basis `P, B, D`. -/
noncomputable def tc (P B D X : E2) : ℝ := cr (B - P) (X - P) / cr (B - P) (D - P)

/-- The `P`-coordinate of `X` in the affine basis `P, B, D`. -/
noncomputable def xc (P B D X : E2) : ℝ := 1 - sc P B D X - tc P B D X

section Coords

variable {P B D : E2}

lemma coord_eq (hΩ : cr (B - P) (D - P) ≠ 0) (X : E2) :
    X - P = sc P B D X • (B - P) + tc P B D X • (D - P) := by
  have key : X - P - (sc P B D X • (B - P) + tc P B D X • (D - P)) = 0 := by
    refine eq_zero_of_cr_eq_zero_of_cr_eq_zero hΩ ?_ ?_
    · rw [cr_sub_left, cr_add_left, cr_smul_left, cr_smul_left, cr_self, mul_zero,
        add_zero, sc, div_mul_cancel₀ _ hΩ, sub_self]
    · rw [cr_sub_right, cr_add_right, cr_smul_right, cr_smul_right, cr_self, mul_zero,
        zero_add, tc, div_mul_cancel₀ _ hΩ, sub_self]
  rw [sub_eq_zero] at key
  exact key

@[simp] lemma sc_B (hΩ : cr (B - P) (D - P) ≠ 0) : sc P B D B = 1 := div_self hΩ

@[simp] lemma tc_B : tc P B D B = 0 := by simp [tc]

@[simp] lemma sc_D : sc P B D D = 0 := by simp [sc]

@[simp] lemma tc_D (hΩ : cr (B - P) (D - P) ≠ 0) : tc P B D D = 1 := div_self hΩ

@[simp] lemma sc_P : sc P B D P = 0 := by simp [sc]

@[simp] lemma tc_P : tc P B D P = 0 := by simp [tc]

lemma xc_sum (X : E2) : xc P B D X + sc P B D X + tc P B D X = 1 := by
  simp [xc]
  ring

/-- Expand `cr` of two vectors written in the basis `B - P, D - P`. -/
lemma cr_expand {a b c d : ℝ} :
    cr (a • (B - P) + b • (D - P)) (c • (B - P) + d • (D - P))
      = (a * d - b * c) * cr (B - P) (D - P) := by
  have hanti : cr (D - P) (B - P) = -cr (B - P) (D - P) := cr_anti _ _
  simp only [cr_add_left, cr_add_right, cr_smul_left, cr_smul_right, cr_self,
    mul_zero, add_zero, hanti]
  ring

/-- The `P`-coordinate of `X` measures the (signed) side of line `BD`. -/
lemma xc_cr (hΩ : cr (B - P) (D - P) ≠ 0) (X : E2) :
    cr (D - B) (X - B) = xc P B D X * cr (B - P) (D - P) := by
  have e1 : D - B = (D - P) - (B - P) := by abel
  have e2 : X - B = (sc P B D X - 1) • (B - P) + tc P B D X • (D - P) := by
    rw [show X - B = X - P - (B - P) by abel, coord_eq hΩ X, sub_smul, one_smul]
    abel
  have hanti : cr (D - P) (B - P) = -cr (B - P) (D - P) := cr_anti _ _
  rw [e1, e2]
  simp only [cr_sub_left, cr_add_right, cr_smul_right, cr_self, hanti, xc]
  ring

end Coords

/-! ### The configuration package

Side facts and nondegeneracies following from convexity, interiority of `P`
and the non-bisecting hypothesis. -/

section Config

variable {A B C D P : E2}
  (hconv : ConvexQuadrilateral A B C D)
  (hP : P ∈ interior (convexHull ℝ ({A, B, C, D} : Set E2)))
  (hbisB : ∠ A B D ≠ ∠ D B C) (hB : ∠ P B C = ∠ D B A)

include hconv hP hbisB hB

/-- `P` does not lie on the line `BD`: this is the content of the hypothesis
that `BD` does not bisect `∠ABC`. -/
lemma omega_ne_zero : cr (B - P) (D - P) ≠ 0 := by
  intro hΩ
  have hcr : cr (D - B) (P - B) = 0 := by
    have h1 : cr (D - B) (P - B) = cr (B - P) (D - P) := by simp [cr]; ring
    rw [h1, hΩ]
  have hBD : D - B ≠ 0 := sub_ne_zero.mpr (Ne.symm (ConvexQuadrilateral.ne_BD hconv))
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, P - B = μ • (D - B) := by
    have hc : (D - B) 0 * (P - B) 1 = (D - B) 1 * (P - B) 0 := by
      have hc0 := hcr
      simp only [cr] at hc0
      linear_combination hc0
    by_cases h0 : (D - B) 0 = 0
    · have h1 : (D - B) 1 ≠ 0 := by
        intro hz
        apply hBD
        ext i
        fin_cases i <;> simp [h0, hz]
      have hb0 : (P - B) 0 = 0 := by
        rw [h0, zero_mul] at hc
        exact (mul_eq_zero.mp hc.symm).resolve_left h1
      exact ⟨(P - B) 1 / (D - B) 1, by
        ext i
        fin_cases i
        · simp [smul_eq_mul, hb0, h0]
        · have h1' : (D 1 - B 1 : ℝ) ≠ 0 := by simpa using h1
          simp [smul_eq_mul, div_mul_cancel₀ _ h1']⟩
    · exact ⟨(P - B) 0 / (D - B) 0, by
        ext i
        fin_cases i
        · have h0' : (D 0 - B 0 : ℝ) ≠ 0 := by simpa using h0
          simp [smul_eq_mul, div_mul_cancel₀ _ h0']
        · have hb1 : (P - B) 1 = (P - B) 0 / (D - B) 0 * (D - B) 1 := by
            rw [div_mul_eq_mul_div, eq_div_iff h0]
            linear_combination hc
          simp [smul_eq_mul, hb1]⟩
  have hsBC := ConvexQuadrilateral.side_BC hconv hP
  have heBC := ConvexQuadrilateral.edge_BC hconv
  have hμcr : cr (C - B) (P - B) = μ * cr (C - B) (D - B) := by
    rw [hμ, cr_smul_right]
  have hμpos : 0 < μ := by
    rcases lt_or_ge 0 μ with hpos | hcon
    · exact hpos
    · rw [hμcr] at hsBC
      nlinarith [hsBC, heBC, hcon]
  have hang : ∠ P B C = ∠ D B C := by
    show InnerProductGeometry.angle (P -ᵥ B) (C -ᵥ B)
      = InnerProductGeometry.angle (D -ᵥ B) (C -ᵥ B)
    simp only [vsub_eq_sub]
    rw [hμ]
    exact InnerProductGeometry.angle_smul_left_of_pos _ _ hμpos
  apply hbisB
  rw [EuclideanGeometry.angle_comm A B D, ← hB]
  exact hang

end Config

/-! ### Metric data and the distance master identity -/

section Metric

variable {P B D : E2}

/-- The quadratic form `Q(q, r) = ‖q • (B - P) + r • (D - P)‖²`. -/
noncomputable def Qform (P B D : E2) (q r : ℝ) : ℝ :=
  dist P B ^ 2 * q ^ 2 + 2 * ⟪B - P, D - P⟫ * q * r + dist P D ^ 2 * r ^ 2

lemma inner_expand {a b c d : ℝ} :
    ⟪a • (B - P) + b • (D - P), c • (B - P) + d • (D - P)⟫
      = a * c * ⟪B - P, B - P⟫ + (a * d + b * c) * ⟪B - P, D - P⟫
        + b * d * ⟪D - P, D - P⟫ := by
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right]
  rw [real_inner_comm (D - P) (B - P)]
  ring

lemma norm_expand_sq {a b : ℝ} :
    ‖a • (B - P) + b • (D - P)‖ ^ 2 = Qform P B D a b := by
  rw [Qform, ← real_inner_self_eq_norm_sq, inner_expand,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  have h1 : ‖B - P‖ = dist P B := by rw [dist_eq_norm, norm_sub_rev]
  have h2 : ‖D - P‖ = dist P D := by rw [dist_eq_norm, norm_sub_rev]
  rw [h1, h2]
  ring

/-- `PA²` in coordinates. -/
lemma dist_sq_eq_Qform (hΩ : cr (B - P) (D - P) ≠ 0) (X : E2) :
    dist P X ^ 2 = Qform P B D (sc P B D X) (tc P B D X) := by
  rw [dist_eq_norm, norm_sub_rev, coord_eq hΩ X, norm_expand_sq]

/-- Law of cosines: `BD² = PB² + PD² - 2⟪B - P, D - P⟫`. -/
lemma dist_BD_sq : dist B D ^ 2
    = dist P B ^ 2 + dist P D ^ 2 - 2 * ⟪B - P, D - P⟫ := by
  have e : B - D = (B - P) - (D - P) := by abel
  rw [dist_eq_norm, e, norm_sub_sq_real]
  have h1 : ‖B - P‖ = dist P B := by rw [dist_eq_norm, norm_sub_rev]
  have h2 : ‖D - P‖ = dist P D := by rw [dist_eq_norm, norm_sub_rev]
  rw [h1, h2]
  ring

/-- The barycentric distance identity: for normalized coordinates
(`xc + sc + tc = 1`), the squared distance to any point `Q` is the weighted
sum of squared distances minus the weighted sum of squared side lengths. -/
lemma dist_sq_bary (hΩ : cr (B - P) (D - P) ≠ 0) (Q X : E2) :
    dist Q X ^ 2
      = xc P B D X * dist Q P ^ 2 + sc P B D X * dist Q B ^ 2
        + tc P B D X * dist Q D ^ 2
        - (dist B D ^ 2 * sc P B D X * tc P B D X
          + dist P D ^ 2 * tc P B D X * xc P B D X
          + dist P B ^ 2 * xc P B D X * sc P B D X) := by
  have hsum : xc P B D X + sc P B D X + tc P B D X = 1 := xc_sum X
  have hX : X - Q
      = xc P B D X • (P - Q) + sc P B D X • (B - Q) + tc P B D X • (D - Q) := by
    rw [show X - Q = (X - P) + (P - Q) by abel, coord_eq hΩ X, xc]
    module
  have hexp : ⟪xc P B D X • (P - Q) + sc P B D X • (B - Q) + tc P B D X • (D - Q),
        xc P B D X • (P - Q) + sc P B D X • (B - Q) + tc P B D X • (D - Q)⟫
      = xc P B D X ^ 2 * ⟪P - Q, P - Q⟫ + sc P B D X ^ 2 * ⟪B - Q, B - Q⟫
        + tc P B D X ^ 2 * ⟪D - Q, D - Q⟫
        + xc P B D X * sc P B D X * (2 * ⟪P - Q, B - Q⟫)
        + xc P B D X * tc P B D X * (2 * ⟪P - Q, D - Q⟫)
        + sc P B D X * tc P B D X * (2 * ⟪B - Q, D - Q⟫) := by
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right]
    rw [real_inner_comm (B - Q) (P - Q), real_inner_comm (D - Q) (P - Q),
      real_inner_comm (D - Q) (B - Q)]
    ring
  have huv : 2 * ⟪P - Q, B - Q⟫
      = ⟪P - Q, P - Q⟫ + ⟪B - Q, B - Q⟫ - dist P B ^ 2 := by
    have e : ‖(P - Q) - (B - Q)‖ ^ 2
        = ⟪P - Q, P - Q⟫ + ⟪B - Q, B - Q⟫ - 2 * ⟪P - Q, B - Q⟫ := by
      rw [norm_sub_sq_real, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
      ring
    have e2 : (P - Q) - (B - Q) = P - B := by abel
    have e3 : ‖P - B‖ = dist P B := by rw [dist_eq_norm, norm_sub_rev]
    rw [e2, e3] at e
    linarith
  have huw : 2 * ⟪P - Q, D - Q⟫
      = ⟪P - Q, P - Q⟫ + ⟪D - Q, D - Q⟫ - dist P D ^ 2 := by
    have e : ‖(P - Q) - (D - Q)‖ ^ 2
        = ⟪P - Q, P - Q⟫ + ⟪D - Q, D - Q⟫ - 2 * ⟪P - Q, D - Q⟫ := by
      rw [norm_sub_sq_real, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
      ring
    have e2 : (P - Q) - (D - Q) = P - D := by abel
    have e3 : ‖P - D‖ = dist P D := by rw [dist_eq_norm, norm_sub_rev]
    rw [e2, e3] at e
    linarith
  have hvw : 2 * ⟪B - Q, D - Q⟫
      = ⟪B - Q, B - Q⟫ + ⟪D - Q, D - Q⟫ - dist B D ^ 2 := by
    have e : ‖(B - Q) - (D - Q)‖ ^ 2
        = ⟪B - Q, B - Q⟫ + ⟪D - Q, D - Q⟫ - 2 * ⟪B - Q, D - Q⟫ := by
      rw [norm_sub_sq_real, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
      ring
    have e2 : (B - Q) - (D - Q) = B - D := by abel
    have e3 : ‖B - D‖ = dist B D := by rw [dist_eq_norm]
    rw [e2, e3] at e
    linarith
  have hu : ⟪P - Q, P - Q⟫ = dist Q P ^ 2 := by
    rw [real_inner_self_eq_norm_sq, dist_eq_norm, norm_sub_rev]
  have hv : ⟪B - Q, B - Q⟫ = dist Q B ^ 2 := by
    rw [real_inner_self_eq_norm_sq, dist_eq_norm, norm_sub_rev]
  have hw : ⟪D - Q, D - Q⟫ = dist Q D ^ 2 := by
    rw [real_inner_self_eq_norm_sq, dist_eq_norm, norm_sub_rev]
  rw [dist_eq_norm, norm_sub_rev, ← real_inner_self_eq_norm_sq, hX, hexp, huv, huw, hvw,
    hu, hv, hw]
  linear_combination
    (xc P B D X * dist Q P ^ 2 + sc P B D X * dist Q B ^ 2
      + tc P B D X * dist Q D ^ 2) * hsum

end Metric

/-! ### The circle criterion -/

section Circle

variable {P B D : E2}

/-- The circle potential: `X` lies on the circle through `B, D` whose power at
`P` equals `Vval P B D X`. -/
noncomputable def Vval (P B D X : E2) : ℝ :=
  (dist B D ^ 2 * sc P B D X * tc P B D X
    + dist P D ^ 2 * tc P B D X * xc P B D X
    + dist P B ^ 2 * xc P B D X * sc P B D X) / xc P B D X

/-- A point `X` with `xc X ≠ 0` lies on a circle through `B` and `D` iff its
circle potential equals the power of `P` for that circle. -/
lemma on_circle_iff (hΩ : cr (B - P) (D - P) ≠ 0) {O : E2} {r : ℝ} {X : E2}
    (hOB : dist O B = r) (hOD : dist O D = r) (hx : xc P B D X ≠ 0) :
    dist O X = r ↔ Vval P B D X = dist O P ^ 2 - r ^ 2 := by
  have hr : 0 ≤ r := by rw [← hOB]; exact dist_nonneg
  have hsum : xc P B D X + sc P B D X + tc P B D X = 1 := xc_sum X
  have key := dist_sq_bary hΩ O X
  rw [hOB, hOD] at key
  constructor
  · intro h
    rw [h] at key
    have e : dist B D ^ 2 * sc P B D X * tc P B D X
        + dist P D ^ 2 * tc P B D X * xc P B D X
        + dist P B ^ 2 * xc P B D X * sc P B D X
        = xc P B D X * (dist O P ^ 2 - r ^ 2) := by
      linear_combination key + r ^ 2 * hsum
    rw [Vval, e, mul_div_cancel_left₀ _ hx]
  · intro h
    rw [Vval, div_eq_iff hx] at h
    have e2 : dist O X ^ 2 = r ^ 2 := by
      linear_combination key - h + r ^ 2 * hsum
    exact (mul_self_inj_of_nonneg dist_nonneg hr).mp (by linear_combination e2)

/-- Four points are concyclic iff the circle potentials of `A` and `C` agree
(given `A, C` off the line `BD`). -/
lemma cospherical_iff_Vval (hΩ : cr (B - P) (D - P) ≠ 0) {A C : E2}
    (hxA : xc P B D A ≠ 0) (hxC : xc P B D C ≠ 0) :
    Cospherical ({A, B, C, D} : Set E2) ↔ Vval P B D A = Vval P B D C := by
  constructor
  · intro hc
    rw [cospherical_def] at hc
    obtain ⟨O, r, hr⟩ := hc
    have hB : dist B O = r := hr B (by simp)
    have hD : dist D O = r := hr D (by simp)
    have hA : dist A O = r := hr A (by simp)
    have hC : dist C O = r := hr C (by simp)
    rw [dist_comm B O] at hB
    rw [dist_comm D O] at hD
    rw [dist_comm A O] at hA
    rw [dist_comm C O] at hC
    have e1 := (on_circle_iff hΩ hB hD hxA).mp hA
    have e2 := (on_circle_iff hΩ hB hD hxC).mp hC
    rw [e1, e2]
  · intro h
    set M : E2 := (2⁻¹ : ℝ) • (B + D) with hM
    set n : E2 := !₂[-(D - B) 1, (D - B) 0] with hn
    set k := Vval P B D A with hk
    have hn_inner : ⟪D - B, n⟫ = 0 := by
      rw [hn, PiLp.inner_apply, Fin.sum_univ_two]
      simp [RCLike.inner_apply, mul_comm]
      ring
    have hMB : M - B = (2⁻¹ : ℝ) • (D - B) := by rw [hM]; module
    have hMD : M - D = (2⁻¹ : ℝ) • (B - D) := by rw [hM]; module
    have hn_BP : ⟪B - P, n⟫ = -cr (B - P) (D - P) := by
      have e : ⟪B - P, n⟫ = -cr (B - P) (D - B) := by
        rw [hn, PiLp.inner_apply, Fin.sum_univ_two]
        simp [cr, RCLike.inner_apply, mul_comm]
        ring
      rw [e, show D - B = (D - P) - (B - P) by abel, cr_sub_right, cr_self, sub_zero]
    have hn_BP_ne : ⟪B - P, n⟫ ≠ 0 := by
      rw [hn_BP]
      exact neg_ne_zero.mpr hΩ
    set t := (k - (‖M - P‖ ^ 2 - ‖M - B‖ ^ 2)) / (2 * ⟪B - P, n⟫) with ht
    have hMPB : ⟪M - P, t • n⟫ - ⟪M - B, t • n⟫ = t * ⟪B - P, n⟫ := by
      rw [← inner_sub_left, show M - P - (M - B) = B - P by abel, real_inner_smul_right]
    have hpow : dist (M + t • n) P ^ 2 - dist (M + t • n) B ^ 2 = k := by
      have d1 : dist (M + t • n) P ^ 2
          = ‖M - P‖ ^ 2 + ‖t • n‖ ^ 2 + 2 * ⟪M - P, t • n⟫ := by
        rw [dist_eq_norm, show M + t • n - P = (M - P) + t • n by abel, norm_add_sq_real]
        ring
      have d2 : dist (M + t • n) B ^ 2
          = ‖M - B‖ ^ 2 + ‖t • n‖ ^ 2 + 2 * ⟪M - B, t • n⟫ := by
        rw [dist_eq_norm, show M + t • n - B = (M - B) + t • n by abel, norm_add_sq_real]
        ring
      have e2 : (‖M - P‖ ^ 2 - ‖M - B‖ ^ 2) + 2 * t * ⟪B - P, n⟫ = k := by
        rw [ht]
        field_simp
        ring
      rw [d1, d2]
      linear_combination e2 + 2 * hMPB
    have hBD_eq : dist (M + t • n) B = dist (M + t • n) D := by
      have d1 : dist (M + t • n) B ^ 2
          = ‖M - B‖ ^ 2 + ‖t • n‖ ^ 2 + 2 * ⟪M - B, t • n⟫ := by
        rw [dist_eq_norm, show M + t • n - B = (M - B) + t • n by abel, norm_add_sq_real]
        ring
      have d2 : dist (M + t • n) D ^ 2
          = ‖M - D‖ ^ 2 + ‖t • n‖ ^ 2 + 2 * ⟪M - D, t • n⟫ := by
        rw [dist_eq_norm, show M + t • n - D = (M - D) + t • n by abel, norm_add_sq_real]
        ring
      have e1 : ‖M - B‖ = ‖M - D‖ := by
        have e2 : ‖(2⁻¹ : ℝ)‖ = 2⁻¹ := by
          rw [Real.norm_eq_abs, abs_of_nonneg (by norm_num)]
        rw [hMB, hMD, norm_smul, norm_smul, e2, norm_sub_rev]
      have e3 : ⟪M - B, t • n⟫ = 0 := by
        rw [hMB, real_inner_smul_left, real_inner_smul_right, hn_inner]
        simp
      have e4 : ⟪M - D, t • n⟫ = 0 := by
        rw [hMD, show B - D = -(D - B) by abel, real_inner_smul_left, inner_neg_left,
          real_inner_smul_right, hn_inner]
        simp
      have e5 : dist (M + t • n) B ^ 2 = dist (M + t • n) D ^ 2 := by
        rw [d1, d2, e1, e3, e4]
      exact (mul_self_inj_of_nonneg dist_nonneg dist_nonneg).mp (by linear_combination e5)
    refine (cospherical_def _).mpr ⟨M + t • n, dist (M + t • n) B, fun p hp => ?_⟩
    have hVC : Vval P B D C = k := h.symm
    have hOA : dist (M + t • n) A = dist (M + t • n) B :=
      (on_circle_iff hΩ rfl hBD_eq.symm hxA).mpr (by rw [← hk, hpow])
    have hOC : dist (M + t • n) C = dist (M + t • n) B :=
      (on_circle_iff hΩ rfl hBD_eq.symm hxC).mpr (by rw [hVC, hpow])
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with h | h | h | h
    · rw [h, dist_comm]; exact hOA
    · rw [h]; exact dist_comm _ _
    · rw [h, dist_comm]; exact hOC
    · rw [h, dist_comm]; exact hBD_eq.symm

end Circle

/-! ### Oriented angle bridges -/

section Oangle

open EuclideanGeometry

variable {P B D : E2}

/-- The sine of an oriented angle is the area form divided by the norms. -/
lemma sin_oangle (u v : E2) :
    Real.Angle.sin (o.oangle u v) = o.areaForm u v / (‖u‖ * ‖v‖) := by
  rw [Orientation.oangle, Real.Angle.sin_coe, Complex.sin_arg,
    o.norm_kahler, o.kahler_apply_apply]
  simp

/-- The sign of an oriented angle is the sign of the area form. -/
lemma sign_oangle (u v : E2) (hu : u ≠ 0) (hv : v ≠ 0) :
    (o.oangle u v).sign = SignType.sign (o.areaForm u v) := by
  rw [Real.Angle.sign, sin_oangle u v]
  have hpos : 0 < ‖u‖ * ‖v‖ := mul_pos (norm_pos_iff.mpr hu) (norm_pos_iff.mpr hv)
  rw [div_eq_mul_inv, sign_mul, sign_pos (inv_pos.mpr hpos), mul_one]

/-- Expand the area form of two vectors written in the basis `B - P, D - P`. -/
lemma areaForm_expand {a b c d : ℝ} :
    o.areaForm (a • (B - P) + b • (D - P)) (c • (B - P) + d • (D - P))
      = (a * d - b * c) * o.areaForm (B - P) (D - P) := by
  have hswap : o.areaForm (D - P) (B - P) = -o.areaForm (B - P) (D - P) :=
    o.areaForm_swap _ _
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, o.areaForm_apply_self, hswap]
  ring

/-- The area form of the basis is nonzero. -/
lemma areaForm_ne_zero (hΩ : cr (B - P) (D - P) ≠ 0) :
    o.areaForm (B - P) (D - P) ≠ 0 := by
  have h := o.inner_sq_add_areaForm_sq (B - P) (D - P)
  have hcr := cr_sq_eq (B - P) (D - P)
  have hsq : o.areaForm (B - P) (D - P) ^ 2 = cr (B - P) (D - P) ^ 2 := by
    linear_combination h - hcr
  intro hz
  rw [hz] at hsq
  simp at hsq
  exact (pow_ne_zero 2 hΩ) hsq.symm

/-- The vectors `P - B, C - B, A - B, D - B` in basis coordinates. -/
lemma sub_B_eq (hΩ : cr (B - P) (D - P) ≠ 0) (X : E2) :
    X - B = (sc P B D X - 1) • (B - P) + tc P B D X • (D - P) := by
  rw [show X - B = X - P - (B - P) by abel, coord_eq hΩ X, sub_smul, one_smul]
  abel

lemma sub_D_eq (hΩ : cr (B - P) (D - P) ≠ 0) (X : E2) :
    X - D = sc P B D X • (B - P) + (tc P B D X - 1) • (D - P) := by
  rw [show X - D = X - P - (D - P) by abel, coord_eq hΩ X, sub_smul, one_smul]
  abel

/-- `areaForm (P - B) (X - B)` in coordinates. -/
lemma areaForm_PB_of (hΩ : cr (B - P) (D - P) ≠ 0) (X : E2) :
    o.areaForm (P - B) (X - B) = -tc P B D X * o.areaForm (B - P) (D - P) := by
  have e1 : P - B = (-1 : ℝ) • (B - P) + (0 : ℝ) • (D - P) := by module
  have h := areaForm_expand (P := P) (B := B) (D := D) (a := -1) (b := 0)
    (c := sc P B D X - 1) (d := tc P B D X)
  have h' : (-1 * tc P B D X - 0 * (sc P B D X - 1)) * (o.areaForm (B - P)) (D - P)
      = -tc P B D X * (o.areaForm (B - P)) (D - P) := by ring
  rw [e1, sub_B_eq hΩ X]
  exact h.trans h'

/-- `areaForm (X - B) (D - B)` in coordinates. -/
lemma areaForm_XB_DB (hΩ : cr (B - P) (D - P) ≠ 0) (X : E2) :
    o.areaForm (X - B) (D - B) = -xc P B D X * o.areaForm (B - P) (D - P) := by
  have e1 : D - B = (-1 : ℝ) • (B - P) + (1 : ℝ) • (D - P) := by module
  have h := areaForm_expand (P := P) (B := B) (D := D) (a := sc P B D X - 1)
    (b := tc P B D X) (c := -1) (d := 1)
  have h' : ((sc P B D X - 1) * 1 - tc P B D X * -1) * (o.areaForm (B - P)) (D - P)
      = -(1 - sc P B D X - tc P B D X) * (o.areaForm (B - P)) (D - P) := by ring
  rw [sub_B_eq hΩ X, e1, xc]
  exact h.trans h'

/-- `areaForm (P - D) (X - D)` in coordinates. -/
lemma areaForm_PD_of (hΩ : cr (B - P) (D - P) ≠ 0) (X : E2) :
    o.areaForm (P - D) (X - D) = sc P B D X * o.areaForm (B - P) (D - P) := by
  have e1 : P - D = (0 : ℝ) • (B - P) + (-1 : ℝ) • (D - P) := by module
  have h := areaForm_expand (P := P) (B := B) (D := D) (a := 0) (b := -1)
    (c := sc P B D X) (d := tc P B D X - 1)
  have h' : (0 * (tc P B D X - 1) - -1 * sc P B D X) * (o.areaForm (B - P)) (D - P)
      = sc P B D X * (o.areaForm (B - P)) (D - P) := by ring
  rw [e1, sub_D_eq hΩ X]
  exact h.trans h'

/-- `areaForm (X - D) (B - D)` in coordinates. -/
lemma areaForm_XD_BD (hΩ : cr (B - P) (D - P) ≠ 0) (X : E2) :
    o.areaForm (X - D) (B - D) = xc P B D X * o.areaForm (B - P) (D - P) := by
  have e1 : B - D = (1 : ℝ) • (B - P) + (-1 : ℝ) • (D - P) := by module
  have h := areaForm_expand (P := P) (B := B) (D := D) (a := sc P B D X)
    (b := tc P B D X - 1) (c := 1) (d := -1)
  have h' : (sc P B D X * -1 - (tc P B D X - 1) * 1) * (o.areaForm (B - P)) (D - P)
      = (1 - sc P B D X - tc P B D X) * (o.areaForm (B - P)) (D - P) := by ring
  rw [sub_D_eq hΩ X, e1, xc]
  exact h.trans h'

lemma signType_neg_one_mul (s : SignType) : (-1 : SignType) * s = -s := by
  cases s <;> rfl

lemma sign_neg_mul_of_pos {x y : ℝ} (hx : 0 < x) :
    SignType.sign (-x * y) = -SignType.sign y := by
  rw [sign_mul, Left.sign_neg, sign_pos hx, signType_neg_one_mul]

lemma sign_neg_mul_of_neg {x y : ℝ} (hx : x < 0) :
    SignType.sign (-x * y) = SignType.sign y := by
  rw [sign_mul, Left.sign_neg, sign_neg hx, neg_neg, one_mul]

lemma sign_pos_mul_of_pos {x y : ℝ} (hx : 0 < x) :
    SignType.sign (x * y) = SignType.sign y := by
  rw [sign_mul, sign_pos hx, one_mul]

lemma sign_pos_mul_of_neg {x y : ℝ} (hx : x < 0) :
    SignType.sign (x * y) = -SignType.sign y := by
  rw [sign_mul, sign_neg hx, signType_neg_one_mul]

/-- Isogonality at `B`: from `∠PBC = ∠DBA` and the configuration, the rays
`BA, BC` are isogonal in `∠PBD`, as oriented angles. -/
lemma oangle_isogonal_B (hΩ : cr (B - P) (D - P) ≠ 0) {A C : E2}
    (hPB : P ≠ B) (hCB : C ≠ B) (hAB : A ≠ B) (hDB : D ≠ B)
    (hB : ∠ P B C = ∠ D B A)
    (hs : 0 < tc P B D C * xc P B D A) :
    o.oangle (P - B) (C - B) = o.oangle (A - B) (D - B) := by
  have hB' : InnerProductGeometry.angle (P - B) (C - B)
      = InnerProductGeometry.angle (A - B) (D - B) := by
    simp only [EuclideanGeometry.angle, vsub_eq_sub] at hB
    rw [InnerProductGeometry.angle_comm (A - B) (D - B)]
    exact hB
  have hsign : (o.oangle (P - B) (C - B)).sign = (o.oangle (A - B) (D - B)).sign := by
    rw [sign_oangle _ _ (sub_ne_zero.mpr hPB) (sub_ne_zero.mpr hCB),
      sign_oangle _ _ (sub_ne_zero.mpr hAB) (sub_ne_zero.mpr hDB),
      areaForm_PB_of hΩ C, areaForm_XB_DB hΩ A]
    rcases mul_pos_iff.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [sign_neg_mul_of_pos h1, sign_neg_mul_of_pos h2]
    · rw [sign_neg_mul_of_neg h1, sign_neg_mul_of_neg h2]
  exact o.oangle_eq_of_angle_eq_of_sign_eq hB' hsign

/-- Isogonality at `D`, similarly. -/
lemma oangle_isogonal_D (hΩ : cr (B - P) (D - P) ≠ 0) {A C : E2}
    (hPD : P ≠ D) (hCD : C ≠ D) (hAD : A ≠ D) (hBD : B ≠ D)
    (hD : ∠ P D C = ∠ B D A)
    (hs : 0 < sc P B D C * xc P B D A) :
    o.oangle (P - D) (C - D) = o.oangle (A - D) (B - D) := by
  have hD' : InnerProductGeometry.angle (P - D) (C - D)
      = InnerProductGeometry.angle (A - D) (B - D) := by
    simp only [EuclideanGeometry.angle, vsub_eq_sub] at hD
    rw [InnerProductGeometry.angle_comm (A - D) (B - D)]
    exact hD
  have hsign : (o.oangle (P - D) (C - D)).sign = (o.oangle (A - D) (B - D)).sign := by
    rw [sign_oangle _ _ (sub_ne_zero.mpr hPD) (sub_ne_zero.mpr hCD),
      sign_oangle _ _ (sub_ne_zero.mpr hAD) (sub_ne_zero.mpr hBD),
      areaForm_PD_of hΩ C, areaForm_XD_BD hΩ A]
    rcases mul_pos_iff.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [sign_pos_mul_of_pos h1, sign_pos_mul_of_pos h2]
    · rw [sign_pos_mul_of_neg h1, sign_pos_mul_of_neg h2]
  exact o.oangle_eq_of_angle_eq_of_sign_eq hD' hsign

/-- The first isogonal relation: `BD²·tcA·tcC = PB²·xcA·xcC`. -/
lemma REL_B (hΩ : cr (B - P) (D - P) ≠ 0) {A C : E2}
    (hPB : P ≠ B) (hCB : C ≠ B) (hAB : A ≠ B) (hDB : D ≠ B)
    (hB : ∠ P B C = ∠ D B A)
    (hs : 0 < tc P B D C * xc P B D A) :
    dist B D ^ 2 * tc P B D A * tc P B D C
      = dist P B ^ 2 * xc P B D A * xc P B D C := by
  have h1 := oangle_isogonal_B hΩ hPB hCB hAB hDB hB hs
  have h2 : o.oangle (P - B) (A - B) = o.oangle (C - B) (D - B) := by
    have h2a : o.oangle (P - B) (A - B) + o.oangle (A - B) (D - B)
        = o.oangle (P - B) (D - B) :=
      o.oangle_add (sub_ne_zero.mpr hPB) (sub_ne_zero.mpr hAB) (sub_ne_zero.mpr hDB)
    have h2b : o.oangle (C - B) (P - B) + o.oangle (P - B) (D - B)
        = o.oangle (C - B) (D - B) :=
      o.oangle_add (sub_ne_zero.mpr hCB) (sub_ne_zero.mpr hPB) (sub_ne_zero.mpr hDB)
    have hrev : o.oangle (C - B) (P - B) = -o.oangle (P - B) (C - B) := o.oangle_rev _ _
    have e1 : o.oangle (P - B) (A - B)
        = o.oangle (P - B) (D - B) - o.oangle (A - B) (D - B) := by
      rw [← h2a]; abel
    have e2 : o.oangle (C - B) (D - B)
        = o.oangle (P - B) (D - B) - o.oangle (P - B) (C - B) := by
      rw [← h2b, hrev]; abel
    rw [e1, e2, h1]
  have hΩ' : o.areaForm (B - P) (D - P) ≠ 0 := areaForm_ne_zero hΩ
  have d1 : ‖P - B‖ * ‖C - B‖ ≠ 0 :=
    mul_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hPB))
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hCB))
  have d2 : ‖A - B‖ * ‖D - B‖ ≠ 0 :=
    mul_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hAB))
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hDB))
  have s1 := congrArg Real.Angle.sin h1
  rw [sin_oangle, sin_oangle, areaForm_PB_of hΩ C, areaForm_XB_DB hΩ A,
    div_eq_div_iff d1 d2] at s1
  have R1 : tc P B D C * (‖A - B‖ * ‖D - B‖) = xc P B D A * (‖P - B‖ * ‖C - B‖) := by
    have s1' : (-o.areaForm (B - P) (D - P)) * (tc P B D C * (‖A - B‖ * ‖D - B‖))
        = (-o.areaForm (B - P) (D - P)) * (xc P B D A * (‖P - B‖ * ‖C - B‖)) := by
      linear_combination s1
    exact mul_left_cancel₀ (neg_ne_zero.mpr hΩ') s1'
  have s2 := congrArg Real.Angle.sin h2
  have d3 : ‖P - B‖ * ‖A - B‖ ≠ 0 :=
    mul_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hPB))
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hAB))
  have d4 : ‖C - B‖ * ‖D - B‖ ≠ 0 :=
    mul_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hCB))
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hDB))
  rw [sin_oangle, sin_oangle, areaForm_PB_of hΩ A, areaForm_XB_DB hΩ C,
    div_eq_div_iff d3 d4] at s2
  have R2 : tc P B D A * (‖C - B‖ * ‖D - B‖) = xc P B D C * (‖P - B‖ * ‖A - B‖) := by
    have s2' : (-o.areaForm (B - P) (D - P)) * (tc P B D A * (‖C - B‖ * ‖D - B‖))
        = (-o.areaForm (B - P) (D - P)) * (xc P B D C * (‖P - B‖ * ‖A - B‖)) := by
      linear_combination s2
    exact mul_left_cancel₀ (neg_ne_zero.mpr hΩ') s2'
  have hne : ‖A - B‖ * ‖C - B‖ ≠ 0 :=
    mul_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hAB))
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hCB))
  have e1 : tc P B D A * tc P B D C * ‖D - B‖ ^ 2 * (‖A - B‖ * ‖C - B‖)
      = xc P B D A * xc P B D C * ‖P - B‖ ^ 2 * (‖A - B‖ * ‖C - B‖) := by
    linear_combination (tc P B D A * (‖C - B‖ * ‖D - B‖)) * R1 +
      (xc P B D A * (‖P - B‖ * ‖C - B‖)) * R2
  have hfin : tc P B D A * tc P B D C * ‖D - B‖ ^ 2
      = xc P B D A * xc P B D C * ‖P - B‖ ^ 2 := mul_right_cancel₀ hne e1
  have hDB' : ‖D - B‖ = dist B D := by rw [dist_eq_norm, norm_sub_rev]
  have hPB' : ‖P - B‖ = dist P B := by rw [dist_eq_norm, norm_sub_rev]
  rw [hDB', hPB'] at hfin
  linear_combination hfin

/-- The second isogonal relation: `BD²·scA·scC = PD²·xcA·xcC`. -/
lemma REL_D (hΩ : cr (B - P) (D - P) ≠ 0) {A C : E2}
    (hPD : P ≠ D) (hCD : C ≠ D) (hAD : A ≠ D) (hBD : B ≠ D)
    (hD : ∠ P D C = ∠ B D A)
    (hs : 0 < sc P B D C * xc P B D A) :
    dist B D ^ 2 * sc P B D A * sc P B D C
      = dist P D ^ 2 * xc P B D A * xc P B D C := by
  have h1 := oangle_isogonal_D hΩ hPD hCD hAD hBD hD hs
  have h2 : o.oangle (P - D) (A - D) = o.oangle (C - D) (B - D) := by
    have h2a : o.oangle (P - D) (A - D) + o.oangle (A - D) (B - D)
        = o.oangle (P - D) (B - D) :=
      o.oangle_add (sub_ne_zero.mpr hPD) (sub_ne_zero.mpr hAD) (sub_ne_zero.mpr hBD)
    have h2b : o.oangle (C - D) (P - D) + o.oangle (P - D) (B - D)
        = o.oangle (C - D) (B - D) :=
      o.oangle_add (sub_ne_zero.mpr hCD) (sub_ne_zero.mpr hPD) (sub_ne_zero.mpr hBD)
    have hrev : o.oangle (C - D) (P - D) = -o.oangle (P - D) (C - D) := o.oangle_rev _ _
    have e1 : o.oangle (P - D) (A - D)
        = o.oangle (P - D) (B - D) - o.oangle (A - D) (B - D) := by
      rw [← h2a]; abel
    have e2 : o.oangle (C - D) (B - D)
        = o.oangle (P - D) (B - D) - o.oangle (P - D) (C - D) := by
      rw [← h2b, hrev]; abel
    rw [e1, e2, h1]
  have hΩ' : o.areaForm (B - P) (D - P) ≠ 0 := areaForm_ne_zero hΩ
  have d1 : ‖P - D‖ * ‖C - D‖ ≠ 0 :=
    mul_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hPD))
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hCD))
  have d2 : ‖A - D‖ * ‖B - D‖ ≠ 0 :=
    mul_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hAD))
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hBD))
  have s3 := congrArg Real.Angle.sin h1
  rw [sin_oangle, sin_oangle, areaForm_PD_of hΩ C, areaForm_XD_BD hΩ A,
    div_eq_div_iff d1 d2] at s3
  have R3 : sc P B D C * (‖A - D‖ * ‖B - D‖) = xc P B D A * (‖P - D‖ * ‖C - D‖) := by
    have s3' : (o.areaForm (B - P) (D - P)) * (sc P B D C * (‖A - D‖ * ‖B - D‖))
        = (o.areaForm (B - P) (D - P)) * (xc P B D A * (‖P - D‖ * ‖C - D‖)) := by
      linear_combination s3
    exact mul_left_cancel₀ hΩ' s3'
  have s4 := congrArg Real.Angle.sin h2
  have d3 : ‖P - D‖ * ‖A - D‖ ≠ 0 :=
    mul_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hPD))
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hAD))
  have d4 : ‖C - D‖ * ‖B - D‖ ≠ 0 :=
    mul_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hCD))
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hBD))
  rw [sin_oangle, sin_oangle, areaForm_PD_of hΩ A, areaForm_XD_BD hΩ C,
    div_eq_div_iff d3 d4] at s4
  have R4 : sc P B D A * (‖C - D‖ * ‖B - D‖) = xc P B D C * (‖P - D‖ * ‖A - D‖) := by
    have s4' : (o.areaForm (B - P) (D - P)) * (sc P B D A * (‖C - D‖ * ‖B - D‖))
        = (o.areaForm (B - P) (D - P)) * (xc P B D C * (‖P - D‖ * ‖A - D‖)) := by
      linear_combination s4
    exact mul_left_cancel₀ hΩ' s4'
  have hne : ‖A - D‖ * ‖C - D‖ ≠ 0 :=
    mul_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hAD))
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hCD))
  have e1 : sc P B D A * sc P B D C * ‖B - D‖ ^ 2 * (‖A - D‖ * ‖C - D‖)
      = xc P B D A * xc P B D C * ‖P - D‖ ^ 2 * (‖A - D‖ * ‖C - D‖) := by
    linear_combination (sc P B D A * (‖C - D‖ * ‖B - D‖)) * R3 +
      (xc P B D A * (‖P - D‖ * ‖C - D‖)) * R4
  have hfin : sc P B D A * sc P B D C * ‖B - D‖ ^ 2
      = xc P B D A * xc P B D C * ‖P - D‖ ^ 2 := mul_right_cancel₀ hne e1
  have hBD' : ‖B - D‖ = dist B D := by rw [dist_eq_norm]
  have hPD' : ‖P - D‖ = dist P D := by rw [dist_eq_norm, norm_sub_rev]
  rw [hBD', hPD'] at hfin
  linear_combination hfin

end Oangle

/-! ### Final algebra -/

section Final

variable {P B D A C : E2}

/-- With the two isogonal relations in place, concyclicity and `PA = PC` are
equivalent. -/
lemma final (hΩ : cr (B - P) (D - P) ≠ 0)
    (hPB : P ≠ B) (hPD : P ≠ D) (hBD : B ≠ D)
    (hxA : xc P B D A ≠ 0) (hxC : xc P B D C ≠ 0)
    (hxAxC : xc P B D A * xc P B D C < 0)
    (hREL_B : dist B D ^ 2 * tc P B D A * tc P B D C
      = dist P B ^ 2 * xc P B D A * xc P B D C)
    (hREL_D : dist B D ^ 2 * sc P B D A * sc P B D C
      = dist P D ^ 2 * xc P B D A * xc P B D C) :
    (Vval P B D A = Vval P B D C) ↔ dist P A = dist P C := by
  have ha : 0 < dist B D := dist_pos.mpr hBD
  have hb : 0 < dist P D := dist_pos.mpr hPD
  have hc : 0 < dist P B := dist_pos.mpr hPB
  -- Coordinates are nonzero.
  have hxcAxC : xc P B D A * xc P B D C ≠ 0 := ne_of_lt hxAxC
  have hscA : sc P B D A ≠ 0 := by
    intro hz
    rw [hz] at hREL_D
    have h0 : (0:ℝ) = dist P D ^ 2 * (xc P B D A * xc P B D C) := by
      linear_combination hREL_D
    rcases mul_eq_zero.mp h0.symm with h1 | h1
    · exact hPD (dist_eq_zero.mp (sq_eq_zero_iff.mp h1))
    · exact hxcAxC h1
  have hscC : sc P B D C ≠ 0 := by
    intro hz
    rw [hz] at hREL_D
    have h0 : (0:ℝ) = dist P D ^ 2 * (xc P B D A * xc P B D C) := by
      linear_combination hREL_D
    rcases mul_eq_zero.mp h0.symm with h1 | h1
    · exact hPD (dist_eq_zero.mp (sq_eq_zero_iff.mp h1))
    · exact hxcAxC h1
  have htcA : tc P B D A ≠ 0 := by
    intro hz
    rw [hz] at hREL_B
    have h0 : (0:ℝ) = dist P B ^ 2 * (xc P B D A * xc P B D C) := by
      linear_combination hREL_B
    rcases mul_eq_zero.mp h0.symm with h1 | h1
    · exact hPB (dist_eq_zero.mp (sq_eq_zero_iff.mp h1))
    · exact hxcAxC h1
  have htcC : tc P B D C ≠ 0 := by
    intro hz
    rw [hz] at hREL_B
    have h0 : (0:ℝ) = dist P B ^ 2 * (xc P B D A * xc P B D C) := by
      linear_combination hREL_B
    rcases mul_eq_zero.mp h0.symm with h1 | h1
    · exact hPB (dist_eq_zero.mp (sq_eq_zero_iff.mp h1))
    · exact hxcAxC h1
  -- The parameters `u, v, w` of the barycentric solution.
  set u := xc P B D A / dist B D with hu
  set v := sc P B D A / dist P D with hv
  set w := tc P B D A / dist P B with hw
  clear_value u v w
  have hu0 : u ≠ 0 := by
    rw [hu]; exact div_ne_zero hxA (ne_of_gt ha)
  have hv0 : v ≠ 0 := by
    rw [hv]; exact div_ne_zero hscA (ne_of_gt hb)
  have hw0 : w ≠ 0 := by
    rw [hw]; exact div_ne_zero htcA (ne_of_gt hc)
  have hxcA : xc P B D A = dist B D * u := by
    rw [hu]; field_simp [ne_of_gt ha]
  have hscA2 : sc P B D A = dist P D * v := by
    rw [hv]; field_simp [ne_of_gt hb]
  have htcA2 : tc P B D A = dist P B * w := by
    rw [hw]; field_simp [ne_of_gt hc]
  have hM : dist B D * u + dist P D * v + dist P B * w = 1 := by
    rw [← hxcA, ← hscA2, ← htcA2]
    exact xc_sum A
  -- The scale factor `lam` relating the coordinates of `A` and `C`.
  set lam := xc P B D A * xc P B D C / dist B D ^ 2 with hlam
  clear_value lam
  have hlam0 : lam ≠ 0 := by
    rw [hlam]
    exact div_ne_zero (mul_ne_zero hxA hxC) (pow_ne_zero 2 (ne_of_gt ha))
  have hlamspec : xc P B D A * xc P B D C = lam * dist B D ^ 2 := by
    rw [hlam]; field_simp [pow_ne_zero 2 (ne_of_gt ha)]
  have hxcC2 : xc P B D C = lam * dist B D / u := by
    have h1 : xc P B D A * xc P B D C = dist B D * (lam * dist B D) := by
      linear_combination hlamspec
    rw [hxcA] at h1
    have h2 : dist B D * (u * xc P B D C) = dist B D * (lam * dist B D) := by
      linear_combination h1
    have e : u * xc P B D C = lam * dist B D := mul_left_cancel₀ (ne_of_gt ha) h2
    rw [← e]; field_simp [hu0]
  have hscC2 : sc P B D C = lam * dist P D / v := by
    have h1 : dist B D ^ 2 * (dist P D * v) * sc P B D C
        = dist P D ^ 2 * (lam * dist B D ^ 2) := by
      linear_combination hREL_D + dist P D ^ 2 * hlamspec
        - (dist B D ^ 2 * sc P B D C) * hscA2
    have h2 : (dist B D ^ 2 * dist P D) * (v * sc P B D C)
        = (dist B D ^ 2 * dist P D) * (lam * dist P D) := by
      linear_combination h1
    have e : v * sc P B D C = lam * dist P D :=
      mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 2 (ne_of_gt ha)) (ne_of_gt hb)) h2
    rw [← e]; field_simp [hv0]
  have htcC2 : tc P B D C = lam * dist P B / w := by
    have h1 : dist B D ^ 2 * (dist P B * w) * tc P B D C
        = dist P B ^ 2 * (lam * dist B D ^ 2) := by
      linear_combination hREL_B + dist P B ^ 2 * hlamspec
        - (dist B D ^ 2 * tc P B D C) * htcA2
    have h2 : (dist B D ^ 2 * dist P B) * (w * tc P B D C)
        = (dist B D ^ 2 * dist P B) * (lam * dist P B) := by
      linear_combination h1
    have e : w * tc P B D C = lam * dist P B :=
      mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 2 (ne_of_gt ha)) (ne_of_gt hc)) h2
    rw [← e]; field_simp [hw0]
  -- The key quantity `N` and the normalization `lam * N = u * v * w`.
  set N := dist B D * v * w + dist P D * w * u + dist P B * u * v with hN
  clear_value N
  have hlamN : lam * N = u * v * w := by
    have hsum : xc P B D C + sc P B D C + tc P B D C = 1 := xc_sum C
    rw [hxcC2, hscC2, htcC2] at hsum
    have e : lam * (dist B D / u + dist P D / v + dist P B / w) = 1 := by
      linear_combination hsum
    rw [hN]
    field_simp [hu0, hv0, hw0] at e ⊢
    linear_combination e
  have huvw : u * v * w ≠ 0 := mul_ne_zero (mul_ne_zero hu0 hv0) hw0
  have hN0 : N ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hlamN
    exact huvw hlamN.symm
  have hlam_eq : lam = u * v * w / N := by
    rw [← hlamN]; field_simp [hN0]
  -- Circle potential of `A`.
  have hVA : Vval P B D A = dist P D * dist P B * N / u := by
    rw [Vval, hxcA, hscA2, htcA2, hN]
    field_simp [hu0]
  -- Circle potential of `C`.
  have hnumC : (dist B D ^ 2 * sc P B D C * tc P B D C
      + dist P D ^ 2 * tc P B D C * xc P B D C
      + dist P B ^ 2 * xc P B D C * sc P B D C) * (u * v * w)
      = lam ^ 2 * (dist B D * dist P D * dist P B)
        * (dist B D * u + dist P D * v + dist P B * w) := by
    rw [hxcC2, hscC2, htcC2]
    field_simp [hu0, hv0, hw0]
  rw [hM, mul_one] at hnumC
  have hnumC2 : dist B D ^ 2 * sc P B D C * tc P B D C
      + dist P D ^ 2 * tc P B D C * xc P B D C
      + dist P B ^ 2 * xc P B D C * sc P B D C
      = lam ^ 2 * (dist B D * dist P D * dist P B) / (u * v * w) :=
    (eq_div_iff huvw).mpr hnumC
  have hVC : Vval P B D C = dist P D * dist P B * u / N := by
    rw [Vval, hnumC2, hxcC2, hlam_eq]
    field_simp [hu0, hv0, hw0, hN0, ne_of_gt ha]
  -- Concyclicity ⟺ `N² = u²`.
  have hbc : (0:ℝ) < dist P D * dist P B := mul_pos hb hc
  have hCyc : (Vval P B D A = Vval P B D C) ↔ N ^ 2 = u ^ 2 := by
    rw [hVA, hVC]
    constructor
    · intro h
      rw [div_eq_div_iff hu0 hN0] at h
      have h2 : N * N = u * u :=
        mul_left_cancel₀ (ne_of_gt hbc) (by linear_combination h)
      rw [pow_two, pow_two]
      exact h2
    · intro h
      rw [div_eq_div_iff hu0 hN0]
      have h2 : N * N = u * u := by
        rw [← pow_two, ← pow_two]
        exact h
      linear_combination (dist P D * dist P B) * h2
  -- `PA = PC` ⟺ `N² = u²`.
  have hAP : A ≠ P := by
    rintro rfl
    exact hscA sc_P
  have hE0 : 0 < Qform P B D (sc P B D A) (tc P B D A) := by
    rw [← dist_sq_eq_Qform hΩ A]
    exact pow_pos (dist_pos.mpr hAP.symm) 2
  have hPA : dist P A * dist P A = Qform P B D (sc P B D A) (tc P B D A) := by
    linear_combination dist_sq_eq_Qform hΩ A
  have hPC : dist P C * dist P C * N ^ 2
      = u ^ 2 * Qform P B D (sc P B D A) (tc P B D A) := by
    have h1 : dist P C ^ 2 = Qform P B D (sc P B D C) (tc P B D C) :=
      dist_sq_eq_Qform hΩ C
    rw [Qform, hscC2, htcC2, hlam_eq] at h1
    rw [Qform, hscA2, htcA2]
    field_simp [hv0, hw0, hN0] at h1
    linear_combination h1
  have e : dist P A * dist P A = dist P C * dist P C ↔ dist P A = dist P C :=
    mul_self_inj_of_nonneg dist_nonneg dist_nonneg
  have hdist : (dist P A = dist P C) ↔ N ^ 2 = u ^ 2 := by
    constructor
    · intro h
      have h2 := e.mpr h
      have h3 : Qform P B D (sc P B D A) (tc P B D A) * N ^ 2
          = Qform P B D (sc P B D A) (tc P B D A) * u ^ 2 := by
        linear_combination hPC - N ^ 2 * hPA + N ^ 2 * h2
      exact mul_left_cancel₀ (ne_of_gt hE0) h3
    · intro h
      apply e.mp
      rw [h] at hPC
      have h3 : u ^ 2 * (dist P C * dist P C)
          = u ^ 2 * Qform P B D (sc P B D A) (tc P B D A) := by
        linear_combination hPC
      have h4 : dist P C * dist P C = Qform P B D (sc P B D A) (tc P B D A) :=
        mul_left_cancel₀ (pow_ne_zero 2 hu0) h3
      linear_combination hPA - h4
  exact hCyc.trans hdist.symm

end Final

/-! ### Main theorem -/

lemma cr_BP_CP (B C P : E2) : cr (B - P) (C - P) = cr (C - B) (P - B) := by
  simp [cr]; ring

lemma cr_CP_DP (C D P : E2) : cr (C - P) (D - P) = cr (D - C) (P - C) := by
  simp [cr]; ring

lemma mul_pos_of_mul_pos_of_mul_pos {p q r : ℝ} (h1 : 0 < p * q) (h2 : 0 < q * r) :
    0 < p * r := by
  have hq : q ≠ 0 := by
    rintro rfl
    simp at h1
  have h3 : 0 < (p * q) * (q * r) := mul_pos h1 h2
  have h4 : (p * q) * (q * r) = (p * r) * (q * q) := by ring
  rw [h4] at h3
  exact pos_of_mul_pos_left h3 (mul_self_nonneg q)

theorem main {A B C D P : E2}
    (hconv : ConvexQuadrilateral A B C D)
    (hP : P ∈ interior (convexHull ℝ ({A, B, C, D} : Set E2)))
    (hbisB : ∠ A B D ≠ ∠ D B C) (_hbisD : ∠ A D B ≠ ∠ B D C)
    (hB : ∠ P B C = ∠ D B A) (hD : ∠ P D C = ∠ B D A) :
    Cospherical ({A, B, C, D} : Set E2) ↔ dist A P = dist C P := by
  have hΩ : cr (B - P) (D - P) ≠ 0 := omega_ne_zero hconv hP hbisB hB
  have hΩ2 : 0 < cr (B - P) (D - P) * cr (B - P) (D - P) := mul_self_pos.mpr hΩ
  -- Nondegeneracies.
  have hPB : P ≠ B := hconv.ne_PB hP
  have hPD : P ≠ D := hconv.ne_PD hP
  have hBD : B ≠ D := hconv.ne_BD
  have hAB : A ≠ B := hconv.ne_AB
  have hAD : A ≠ D := hconv.ne_AD
  have hCB : C ≠ B := hconv.ne_CB
  have hCD : C ≠ D := hconv.ne_CD
  have hDB : D ≠ B := hBD.symm
  -- `A` and `C` lie on opposite sides of the diagonal `BD`.
  have hxcr : (xc P B D A * cr (B - P) (D - P)) * (xc P B D C * cr (B - P) (D - P)) < 0 := by
    rw [← xc_cr hΩ A, ← xc_cr hΩ C]
    exact hconv.diag_BD
  have hxAxC : xc P B D A * xc P B D C < 0 := by
    have e : xc P B D A * xc P B D C * (cr (B - P) (D - P) * cr (B - P) (D - P)) < 0 := by
      linarith [hxcr]
    by_contra hge
    push Not at hge
    exact absurd e (not_lt.mpr (mul_nonneg hge (mul_self_nonneg _)))
  have hxA : xc P B D A ≠ 0 := left_ne_zero_of_mul (ne_of_lt hxAxC)
  have hxC : xc P B D C ≠ 0 := right_ne_zero_of_mul (ne_of_lt hxAxC)
  -- The sign facts.
  have hs1 : 0 < tc P B D C * xc P B D A := by
    have h1 : 0 < cr (C - B) (P - B) * cr (C - B) (A - B) := hconv.side_BC hP
    have h2 : 0 < cr (C - B) (A - B) * cr (D - B) (A - B) := hconv.edge_AB
    have h3 : 0 < cr (C - B) (P - B) * cr (D - B) (A - B) :=
      mul_pos_of_mul_pos_of_mul_pos h1 h2
    have e : 0 < (tc P B D C * cr (B - P) (D - P)) * (xc P B D A * cr (B - P) (D - P)) := by
      rw [tc, div_mul_cancel₀ _ hΩ, ← xc_cr hΩ A, cr_BP_CP]
      exact h3
    have e2 : 0 < tc P B D C * xc P B D A * (cr (B - P) (D - P) * cr (B - P) (D - P)) := by
      linarith [e]
    exact pos_of_mul_pos_left e2 (mul_self_nonneg _)
  have hs2 : 0 < sc P B D C * xc P B D A := by
    have h1 : 0 < cr (D - C) (P - C) * cr (D - C) (A - C) := hconv.side_CD hP
    have h2 : 0 < cr (D - C) (A - C) * cr (D - B) (A - B) := hconv.edge_DA
    have h3 : 0 < cr (D - C) (P - C) * cr (D - B) (A - B) :=
      mul_pos_of_mul_pos_of_mul_pos h1 h2
    have e : 0 < (sc P B D C * cr (B - P) (D - P)) * (xc P B D A * cr (B - P) (D - P)) := by
      rw [sc, div_mul_cancel₀ _ hΩ, ← xc_cr hΩ A, cr_CP_DP]
      exact h3
    have e2 : 0 < sc P B D C * xc P B D A * (cr (B - P) (D - P) * cr (B - P) (D - P)) := by
      linarith [e]
    exact pos_of_mul_pos_left e2 (mul_self_nonneg _)
  -- The isogonal relations.
  have hREL_B := REL_B hΩ hPB hCB hAB hDB hB hs1
  have hREL_D := REL_D hΩ hPD hCD hAD hBD hD hs2
  -- Conclusion.
  have hfin := final hΩ hPB hPD hBD hxA hxC hxAxC hREL_B hREL_D
  have hcy := cospherical_iff_Vval hΩ hxA hxC
  exact hcy.trans (hfin.trans (by rw [dist_comm P A, dist_comm P C]))

snip end

problem imo2004_p5
    (A B C D P : EuclideanSpace ℝ (Fin 2))
    (hconv : ConvexQuadrilateral A B C D)
    (hP : P ∈ interior (convexHull ℝ ({A, B, C, D} : Set (EuclideanSpace ℝ (Fin 2)))))
    (hbisB : ∠ A B D ≠ ∠ D B C) (hbisD : ∠ A D B ≠ ∠ B D C)
    (hB : ∠ P B C = ∠ D B A) (hD : ∠ P D C = ∠ B D A) :
    Cospherical ({A, B, C, D} : Set (EuclideanSpace ℝ (Fin 2))) ↔ dist A P = dist C P := by
  exact main hconv hP hbisB hbisD hB hD

end Imo2004P5
