/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Data.Int.Star
public import Mathlib.Geometry.Euclidean.Angle.Sphere
public import Mathlib.Geometry.Euclidean.Circumcenter
public import Mathlib.Geometry.Euclidean.Inversion.Basic
public import Mathlib.Geometry.Euclidean.Simplex
public import Mathlib.Geometry.Euclidean.Sphere.Power
public import Mathlib.Geometry.Euclidean.Sphere.SecondInter
public import Mathlib.Geometry.Euclidean.Similarity
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Geometry.Euclidean.Triangle
public import Mathlib.Topology.MetricSpace.Similarity
public import ProblemExtraction

@[expose] public section

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

open scoped EuclideanGeometry RealInnerProductSpace
open Affine Module Real

namespace Imo2021P3

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P] [Fact (finrank ℝ V = 2)]

snip begin

/-- Interior membership is invariant under cycling the vertices of the triangle. -/
theorem mem_interior_cycle {A B C D : P} (hai : AffineIndependent ℝ ![A, B, C])
    (hai' : AffineIndependent ℝ ![B, C, A])
    (hD : D ∈ (⟨_, hai⟩ : Triangle ℝ P).interior) :
    D ∈ (⟨_, hai'⟩ : Triangle ℝ P).interior := by
  obtain ⟨w, hsum, hw, hcomb⟩ := hD
  have hcomb' : Finset.univ.affineCombination ℝ ![A, B, C] w = D := hcomb
  have hsum3 : w 0 + w 1 + w 2 = 1 := by
    have := hsum
    rw [Fin.sum_univ_three] at this
    exact this
  have hs : ∑ i, ![w 1, w 2, w 0] i = 1 := by
    rw [Fin.sum_univ_three]
    show w 1 + w 2 + w 0 = 1
    linarith
  refine ⟨![w 1, w 2, w 0], hs, fun i => by fin_cases i <;> simp [hw], ?_⟩
  have e1 := Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
    Finset.univ ![w 1, w 2, w 0] ![B, C, A] hs A
  have e2 := Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
    Finset.univ w ![A, B, C] hsum A
  rw [← hcomb', e1, e2]
  congr 1
  rw [Finset.weightedVSubOfPoint_apply, Finset.weightedVSubOfPoint_apply,
    Fin.sum_univ_three, Fin.sum_univ_three]
  show w 1 • (B -ᵥ A) + w 2 • (C -ᵥ A) + w 0 • (A -ᵥ A) =
    w 0 • (A -ᵥ A) + w 1 • (B -ᵥ A) + w 2 • (C -ᵥ A)
  rw [vsub_self, smul_zero, add_zero, zero_add]

/-- From an interior point of a triangle, the cevian through a vertex meets the opposite
side in a point strictly between the side's endpoints, and the interior point lies strictly
between the vertex and that meeting point. -/
theorem exists_sbtw_cevian_of_mem_interior {A B C D : P}
    (hai : AffineIndependent ℝ ![A, B, C])
    (hD : D ∈ (⟨_, hai⟩ : Triangle ℝ P).interior) :
    ∃ L : P, Sbtw ℝ B L C ∧ Sbtw ℝ A D L := by
  obtain ⟨w, hsum, hw, hcomb⟩ := hD
  have hcomb' : Finset.univ.affineCombination ℝ ![A, B, C] w = D := hcomb
  have hw0 := hw 0
  have hw1 := hw 1
  have hw2 := hw 2
  have hw12 : 0 < w 1 + w 2 := by linarith [hw1.1, hw2.1]
  have hsum3 : w 0 + w 1 + w 2 = 1 := by
    have := hsum
    rw [Fin.sum_univ_three] at this
    linarith
  have hBC : B ≠ C := hai.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  have hABC : ¬Collinear ℝ ({A, B, C} : Set P) := affineIndependent_iff_not_collinear_set.mp hai
  have hAnBC : A ∉ line[ℝ, B, C] := fun hmem => hABC (collinear_insert_of_mem_affineSpan_pair hmem)
  -- The cevian point, as an explicit affine combination.
  set L : P := AffineMap.lineMap B C (w 2 / (w 1 + w 2)) with hLdef
  have hsbtw_BLC : Sbtw ℝ B L C := by
    rw [hLdef, sbtw_lineMap_iff]
    refine ⟨hBC, div_pos hw2.1 hw12, ?_⟩
    rw [div_lt_one hw12]
    linarith [hw1.1]
  refine ⟨L, hsbtw_BLC, ?_⟩
  -- `D` is the line map from `A` to `L` with coefficient `w 1 + w 2`.
  have key : D -ᵥ A =
      (w 1 + w 2) • (AffineMap.lineMap B C (w 2 / (w 1 + w 2)) -ᵥ A) := by
    have hD' : D -ᵥ A = w 1 • (B -ᵥ A) + w 2 • (C -ᵥ A) := by
      have e2 := Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
        Finset.univ w ![A, B, C] hsum A
      rw [hcomb'] at e2
      have h := congr_arg (· -ᵥ A) e2
      rw [vadd_vsub] at h
      rw [h, Finset.weightedVSubOfPoint_apply, Fin.sum_univ_three]
      simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    rw [AffineMap.lineMap_apply, vadd_vsub_assoc, hD',
      show C -ᵥ B = (C -ᵥ A) - (B -ᵥ A) by rw [vsub_sub_vsub_cancel_right]]
    have e3 : (w 1 + w 2) • ((w 2 / (w 1 + w 2)) • ((C -ᵥ A) - (B -ᵥ A))) =
        w 2 • ((C -ᵥ A) - (B -ᵥ A)) := by
      rw [smul_smul, mul_div_cancel₀ _ (ne_of_gt hw12)]
    rw [smul_add, e3]
    module
  have hDline : D = AffineMap.lineMap A L (w 1 + w 2) := by
    rw [hLdef, AffineMap.lineMap_apply, ← key]
    exact (vsub_vadd D A).symm
  rw [hDline, sbtw_lineMap_iff]
  refine ⟨fun hAL => hAnBC (hAL ▸ hsbtw_BLC.wbtw.mem_affineSpan), hw12, ?_⟩
  linarith [hw0.1]

/-- The cevian angle split at a vertex: for an interior point `D`, the ray `AD` lies inside
the angle `∠BAC`, so the angle at `A` splits. -/
theorem angle_add_of_mem_interior {A B C D : P}
    (hai : AffineIndependent ℝ ![A, B, C])
    (hD : D ∈ (⟨_, hai⟩ : Triangle ℝ P).interior) (hAB : A ≠ B) (hAC : A ≠ C) (hAD : A ≠ D) :
    ∠ B A D + ∠ D A C = ∠ B A C := by
  obtain ⟨L, hBLC, hADL⟩ := exists_sbtw_cevian_of_mem_interior hai hD
  have h1 := EuclideanGeometry.angle_add_of_ne_of_ne hAB hAC hBLC.wbtw
  have h2 := hADL.wbtw.angle_eq_right B hAD.symm
  have h3 := hADL.wbtw.angle_eq_left C hAD.symm
  rw [h2, h3]
  exact h1

/-- An interior point of a triangle does not lie on the line through any side. -/
theorem not_mem_line_of_mem_interior {A B C D : P}
    (hai : AffineIndependent ℝ ![A, B, C])
    (hD : D ∈ (⟨_, hai⟩ : Triangle ℝ P).interior) : D ∉ line[ℝ, B, C] := by
  intro hDline
  have hBC : B ≠ C := hai.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hDline
  obtain ⟨c, hc⟩ := hDline
  obtain ⟨w, hsum, hw, hcomb⟩ := hD
  have hcomb' : Finset.univ.affineCombination ℝ ![A, B, C] w = D := hcomb
  have hB : Finset.univ.affineCombination ℝ ![A, B, C] (Pi.single 1 1) = B :=
    Finset.affineCombination_piSingle ℝ Finset.univ ![A, B, C] (Finset.mem_univ 1)
  have hC : Finset.univ.affineCombination ℝ ![A, B, C] (Pi.single 2 1) = C :=
    Finset.affineCombination_piSingle ℝ Finset.univ ![A, B, C] (Finset.mem_univ 2)
  have hc' : Finset.univ.affineCombination ℝ ![A, B, C] w =
      AffineMap.lineMap (Finset.univ.affineCombination ℝ ![A, B, C] (Pi.single 1 1))
        (Finset.univ.affineCombination ℝ ![A, B, C] (Pi.single 2 1)) c := by
    rw [hB, hC, hcomb']
    exact hc.symm
  have key := (hai.affineCombination_eq_lineMap_iff_weight_lineMap
    (w₁ := Pi.single 1 1) (w₂ := Pi.single 2 1) hsum
    (Fintype.sum_pi_single' 1 _) (Fintype.sum_pi_single' 2 _) c).mp hc'
  have h0 : w 0 = 0 := by
    have h0' := key 0 (Finset.mem_univ 0)
    simp only [Pi.single_eq_of_ne (show (0 : Fin 3) ≠ 1 by decide),
      Pi.single_eq_of_ne (show (0 : Fin 3) ≠ 2 by decide), AffineMap.lineMap_apply_module,
      smul_zero, add_zero] at h0'
    exact h0'
  have hpos := (hw 0).1
  rw [h0] at hpos
  exact lt_irrefl (0 : ℝ) hpos

/-- Affine independence is invariant under cycling the vertices. -/
theorem affineIndependent_cycle {A B C : P} (hai : AffineIndependent ℝ ![A, B, C]) :
    AffineIndependent ℝ ![B, C, A] := by
  rw [affineIndependent_iff_not_collinear_set] at hai ⊢
  rwa [show ({B, C, A} : Set P) = {A, B, C} by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto]

/-- If `E` lies on line `AC` but `D` does not, then `A, D, E` are not collinear. -/
theorem not_collinear_of_not_mem_line {A C D E : P} (hE : E ∈ line[ℝ, A, C]) (hAE : A ≠ E)
    (hD : D ∉ line[ℝ, A, C]) : ¬Collinear ℝ ({A, D, E} : Set P) := by
  intro hcol
  have hsub : line[ℝ, A, E] ≤ line[ℝ, A, C] := by
    rw [affineSpan_le, Set.insert_subset_iff]
    exact ⟨left_mem_affineSpan_pair ℝ A C, Set.singleton_subset_iff.2 hE⟩
  exact hD (hsub (hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hAE))

/-- The law of sines, in ratio form: in a non-degenerate triangle `p₁ p₂ p₃`,
`p₁p₃ · sin(angle at p₁) = p₂p₃ · sin(angle at p₂)`. -/
theorem dist_mul_sin_eq_dist_mul_sin {p₁ p₂ p₃ : P} (h : ¬Collinear ℝ ({p₁, p₂, p₃} : Set P)) :
    dist p₁ p₃ * Real.sin (∠ p₂ p₁ p₃) = dist p₂ p₃ * Real.sin (∠ p₁ p₂ p₃) := by
  have hai : AffineIndependent ℝ ![p₁, p₂, p₃] := affineIndependent_iff_not_collinear_set.mpr h
  have e1 : dist p₁ p₃ / Real.sin (∠ p₁ p₂ p₃) =
      2 * (⟨_, hai⟩ : Triangle ℝ P).circumradius :=
    Affine.Triangle.dist_div_sin_angle_eq_two_mul_circumradius (⟨_, hai⟩ : Triangle ℝ P)
      (show (0 : Fin 3) ≠ 1 by decide) (show (0 : Fin 3) ≠ 2 by decide)
      (show (1 : Fin 3) ≠ 2 by decide)
  have e2 : dist p₂ p₃ / Real.sin (∠ p₂ p₁ p₃) =
      2 * (⟨_, hai⟩ : Triangle ℝ P).circumradius :=
    Affine.Triangle.dist_div_sin_angle_eq_two_mul_circumradius (⟨_, hai⟩ : Triangle ℝ P)
      (show (1 : Fin 3) ≠ 0 by decide) (show (1 : Fin 3) ≠ 2 by decide)
      (show (0 : Fin 3) ≠ 2 by decide)
  have hs1 : Real.sin (∠ p₁ p₂ p₃) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (EuclideanGeometry.angle_pos_of_not_collinear h)
      (EuclideanGeometry.angle_lt_pi_of_not_collinear h))
  have hs2 : Real.sin (∠ p₂ p₁ p₃) ≠ 0 := by
    have h' : ¬Collinear ℝ ({p₂, p₁, p₃} : Set P) := by
      rwa [show ({p₂, p₁, p₃} : Set P) = {p₁, p₂, p₃} by
        ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (EuclideanGeometry.angle_pos_of_not_collinear h')
      (EuclideanGeometry.angle_lt_pi_of_not_collinear h'))
  have heq : dist p₁ p₃ / Real.sin (∠ p₁ p₂ p₃) = dist p₂ p₃ / Real.sin (∠ p₂ p₁ p₃) := by
    rw [e1, e2]
  rw [div_eq_div_iff hs1 hs2] at heq
  exact heq

/-- The trigonometric identity behind `AE · AC = AF · AB`: given the angle sum and the
trigonometric Ceva relation, the two products of shifted sines agree. -/
theorem sin_mul_sin_eq_sin_mul_sin {a b g p e : ℝ}
    (hsum : 2 * a + b + g + p + e = π)
    (hcev : Real.sin b * Real.sin e = Real.sin g * Real.sin p) :
    Real.sin (a + p) * Real.sin (a + g) = Real.sin (a + e) * Real.sin (a + b) := by
  have h1 : Real.cos (2 * a + p + g) = -Real.cos (b + e) := by
    have h : 2 * a + p + g = π - (b + e) := by linarith
    rw [h, Real.cos_pi_sub]
  have h2 : Real.cos (2 * a + e + b) = -Real.cos (p + g) := by
    have h : 2 * a + e + b = π - (p + g) := by linarith
    rw [h, Real.cos_pi_sub]
  have e1 : 2 * Real.sin (a + p) * Real.sin (a + g) = Real.cos (p - g) + Real.cos (b + e) := by
    have h : 2 * Real.sin (a + p) * Real.sin (a + g) =
        Real.cos ((a + p) - (a + g)) - Real.cos ((a + p) + (a + g)) := by
      simp only [Real.cos_sub, Real.cos_add, Real.sin_sub, Real.sin_add]
      ring
    rw [show (a + p) - (a + g) = p - g by ring, show (a + p) + (a + g) = 2 * a + p + g by ring,
      h1] at h
    linarith [h]
  have e2 : 2 * Real.sin (a + e) * Real.sin (a + b) = Real.cos (e - b) + Real.cos (p + g) := by
    have h : 2 * Real.sin (a + e) * Real.sin (a + b) =
        Real.cos ((a + e) - (a + b)) - Real.cos ((a + e) + (a + b)) := by
      simp only [Real.cos_sub, Real.cos_add, Real.sin_sub, Real.sin_add]
      ring
    rw [show (a + e) - (a + b) = e - b by ring, show (a + e) + (a + b) = 2 * a + e + b by ring,
      h2] at h
    linarith [h]
  have hpg : Real.cos (p - g) - Real.cos (p + g) = 2 * Real.sin p * Real.sin g := by
    simp only [Real.cos_sub, Real.cos_add]
    ring
  have heb : Real.cos (e - b) - Real.cos (e + b) = 2 * Real.sin e * Real.sin b := by
    simp only [Real.cos_sub, Real.cos_add]
    ring
  have hbe : Real.cos (b + e) = Real.cos (e + b) := by rw [add_comm]
  rw [hbe] at e1
  have h3 : 2 * Real.sin (a + p) * Real.sin (a + g) =
      2 * Real.sin (a + e) * Real.sin (a + b) := by
    rw [e1, e2]
    linear_combination hpg - heb - 2 * hcev
  linarith [h3]

/-- Non-collinearity of a triple is invariant under cycling. -/
theorem not_collinear_cycle {p₁ p₂ p₃ : P} (h : ¬Collinear ℝ ({p₁, p₂, p₃} : Set P)) :
    ¬Collinear ℝ ({p₂, p₃, p₁} : Set P) := by
  rwa [show ({p₂, p₃, p₁} : Set P) = {p₁, p₂, p₃} by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]

/-- Non-collinearity of a triple is invariant under swapping the first two points. -/
theorem not_collinear_swap {p₁ p₂ p₃ : P} (h : ¬Collinear ℝ ({p₁, p₂, p₃} : Set P)) :
    ¬Collinear ℝ ({p₂, p₁, p₃} : Set P) := by
  rwa [show ({p₂, p₁, p₃} : Set P) = {p₁, p₂, p₃} by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]

/-- Non-collinearity of a triple is invariant under swapping the last two points. -/
theorem not_collinear_swap23 {p₁ p₂ p₃ : P} (h : ¬Collinear ℝ ({p₁, p₂, p₃} : Set P)) :
    ¬Collinear ℝ ({p₁, p₃, p₂} : Set P) := by
  rwa [show ({p₁, p₃, p₂} : Set P) = {p₁, p₂, p₃} by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]

/-- The key metric relation of the configuration: `AE · AC = AF · AB`
(equivalently, `BCEF` is cyclic). This is proved by trigonometric computation:
the law of sines in triangles `ADE`, `ADF`, `ACD`, `ABD`, `BCD`, the trigonometric
form of Ceva's theorem for the concurrent cevians at `D`, and a product-to-sum
identity using the angle sum of the triangle. -/
theorem dist_AE_mul_AC_eq_dist_AF_mul_AB {A B C D E F : P}
    (hai : AffineIndependent ℝ ![A, B, C])
    (hDint : D ∈ (⟨_, hai⟩ : Triangle ℝ P).interior)
    (hbis : ∠ D A B = ∠ C A D)
    (hEw : Wbtw ℝ A E C) (hDE : ∠ A D E = ∠ B C D)
    (hFw : Wbtw ℝ A F B) (hDF : ∠ F D A = ∠ D B C) :
    dist A E * dist A C = dist A F * dist A B := by
  -- Basic distinctness and non-collinearity facts.
  have hAB : A ≠ B := hai.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hAC : A ≠ C := hai.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hBC : B ≠ C := hai.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  have hBA : B ≠ A := hAB.symm
  have hCA : C ≠ A := hAC.symm
  have hCB : C ≠ B := hBC.symm
  have hDA : D ≠ A := by
    rintro rfl
    exact Simplex.point_notMem_interior _ 0 hDint
  have hDB : D ≠ B := by
    rintro rfl
    exact Simplex.point_notMem_interior _ 1 hDint
  have hDC : D ≠ C := by
    rintro rfl
    exact Simplex.point_notMem_interior _ 2 hDint
  have hAD : A ≠ D := hDA.symm
  have hBD : B ≠ D := hDB.symm
  have hCD : C ≠ D := hDC.symm
  have hai_BCA : AffineIndependent ℝ ![B, C, A] := affineIndependent_cycle hai
  have hai_CAB : AffineIndependent ℝ ![C, A, B] := affineIndependent_cycle hai_BCA
  have hDint_BCA := mem_interior_cycle hai hai_BCA hDint
  have hDint_CAB := mem_interior_cycle hai_BCA hai_CAB hDint_BCA
  have hDnBC : D ∉ line[ℝ, B, C] := not_mem_line_of_mem_interior hai hDint
  have hDnCA : D ∉ line[ℝ, C, A] := not_mem_line_of_mem_interior hai_BCA hDint_BCA
  have hDnAB : D ∉ line[ℝ, A, B] := not_mem_line_of_mem_interior hai_CAB hDint_CAB
  have hDnAC : D ∉ line[ℝ, A, C] := by
    have e : line[ℝ, C, A] = line[ℝ, A, C] := by rw [Set.pair_comm]
    rwa [e] at hDnCA
  have hDnBA : D ∉ line[ℝ, B, A] := by
    have e : line[ℝ, A, B] = line[ℝ, B, A] := by rw [Set.pair_comm]
    rwa [e] at hDnAB
  have hncABC : ¬Collinear ℝ ({A, B, C} : Set P) := affineIndependent_iff_not_collinear_set.mp hai
  have hncACB : ¬Collinear ℝ ({A, C, B} : Set P) := not_collinear_swap23 hncABC
  have hncBCD : ¬Collinear ℝ ({B, C, D} : Set P) :=
    fun h => hDnBC (h.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hBC)
  have hncDBC : ¬Collinear ℝ ({D, B, C} : Set P) := not_collinear_swap (not_collinear_swap23 hncBCD)
  have hncCDA : ¬Collinear ℝ ({C, D, A} : Set P) :=
    not_collinear_of_not_mem_line (right_mem_affineSpan_pair ℝ C A) hCA hDnCA
  have hncCAD : ¬Collinear ℝ ({C, A, D} : Set P) := not_collinear_swap23 hncCDA
  have hncDCA : ¬Collinear ℝ ({D, C, A} : Set P) := not_collinear_swap hncCDA
  have hncBDA : ¬Collinear ℝ ({B, D, A} : Set P) :=
    not_collinear_of_not_mem_line (right_mem_affineSpan_pair ℝ B A) hBA hDnBA
  have hncDBA : ¬Collinear ℝ ({D, B, A} : Set P) := not_collinear_swap hncBDA
  have hncBAD : ¬Collinear ℝ ({B, A, D} : Set P) := not_collinear_swap23 hncBDA
  -- `E ≠ A` and `F ≠ A`, since the relevant angles are nonzero.
  have hBCDne : ∠ B C D ≠ 0 := EuclideanGeometry.angle_ne_zero_of_not_collinear hncBCD
  have hDBCne : ∠ D B C ≠ 0 := EuclideanGeometry.angle_ne_zero_of_not_collinear hncDBC
  have hEneA : E ≠ A := by
    intro hEA
    rw [hEA, EuclideanGeometry.angle_self_of_ne hAD] at hDE
    exact hBCDne hDE.symm
  have hFneA : F ≠ A := by
    intro hFA
    rw [hFA, EuclideanGeometry.angle_self_of_ne hAD] at hDF
    exact hDBCne hDF.symm
  have hncDEA : ¬Collinear ℝ ({D, E, A} : Set P) :=
    not_collinear_cycle (not_collinear_of_not_mem_line hEw.mem_affineSpan hEneA.symm hDnAC)
  have hncDFA : ¬Collinear ℝ ({D, F, A} : Set P) :=
    not_collinear_cycle (not_collinear_of_not_mem_line hFw.mem_affineSpan hFneA.symm hDnAB)
  -- The cevian angle splits.
  have hcevA : ∠ B A D + ∠ D A C = ∠ B A C := angle_add_of_mem_interior hai hDint hAB hAC hAD
  have hcevB : ∠ C B D + ∠ D B A = ∠ C B A := angle_add_of_mem_interior hai_BCA hDint_BCA hBC hBA hBD
  have hcevC : ∠ A C D + ∠ D C B = ∠ A C B := angle_add_of_mem_interior hai_CAB hDint_CAB hCA hCB hCD
  -- Triangle angle sums.
  have hsumACD : ∠ A C D + ∠ C D A + ∠ D A C = π :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi D hCA
  have hsumDCE : ∠ D C E + ∠ C E D + ∠ E D C = π :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi E hCD
  have hsumDAF : ∠ D A F + ∠ A F D + ∠ F D A = π :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi F hAD
  have hsumABD : ∠ A B D + ∠ B D A + ∠ D A B = π :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi D hBA
  have hsumABC : ∠ B C A + ∠ C A B + ∠ A B C = π :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi A hCB
  have hADEsum : ∠ A D E + ∠ E D C = ∠ A D C :=
    EuclideanGeometry.angle_add_of_ne_of_ne hDA hDC hEw
  -- The total angle sum in terms of the five base angles.
  have hsum : 2 * ∠ C A D + ∠ B C D + ∠ D B C + ∠ D C A + ∠ D B A = π := by
    have c1 : ∠ B C A = ∠ A C B := EuclideanGeometry.angle_comm B C A
    have c2 : ∠ C A B = ∠ B A C := EuclideanGeometry.angle_comm C A B
    have c3 : ∠ C B D = ∠ D B C := EuclideanGeometry.angle_comm C B D
    have c4 : ∠ D C B = ∠ B C D := EuclideanGeometry.angle_comm D C B
    have c5 : ∠ A C D = ∠ D C A := EuclideanGeometry.angle_comm A C D
    have c6 : ∠ B A D = ∠ D A B := EuclideanGeometry.angle_comm B A D
    have c7 : ∠ D A C = ∠ C A D := EuclideanGeometry.angle_comm D A C
    have c8 : ∠ C B A = ∠ A B C := EuclideanGeometry.angle_comm C B A
    linarith [hsumABC, hcevA, hcevB, hcevC, c1, c2, c3, c4, c5, c6, c7, c8, hbis]
  -- Angle values.
  have hvADC : ∠ C D A = π - (∠ C A D + ∠ D C A) := by
    have c1 : ∠ A C D = ∠ D C A := EuclideanGeometry.angle_comm A C D
    have c2 : ∠ D A C = ∠ C A D := EuclideanGeometry.angle_comm D A C
    linarith [hsumACD, c1, c2]
  have hvEDC : ∠ E D C = ∠ C D A - ∠ B C D := by
    have c1 : ∠ A D C = ∠ C D A := EuclideanGeometry.angle_comm A D C
    linarith [hADEsum, c1, hDE]
  -- `E ≠ C`: otherwise `∠ADC = ∠BCD`, contradicting the angle sum.
  have hEneC : E ≠ C := by
    intro hEC
    rw [hEC] at hDE
    have c1 : ∠ A D C = ∠ C D A := EuclideanGeometry.angle_comm A D C
    rw [c1, hvADC] at hDE
    have c2 : ∠ D C B = ∠ B C D := EuclideanGeometry.angle_comm D C B
    have c3 : ∠ B C A = ∠ A C B := EuclideanGeometry.angle_comm B C A
    have c4 : ∠ C A B = ∠ B A C := EuclideanGeometry.angle_comm C A B
    have c5 : ∠ D A C = ∠ C A D := EuclideanGeometry.angle_comm D A C
    have c6 : ∠ A C D = ∠ D C A := EuclideanGeometry.angle_comm A C D
    have hp1 : 0 < ∠ B A D := EuclideanGeometry.angle_pos_of_not_collinear hncBAD
    have hp2 : 0 < ∠ A B C := EuclideanGeometry.angle_pos_of_not_collinear hncABC
    linarith [hDE, hcevA, hcevC, c2, c3, c4, c5, c6, hsumABC, hp1, hp2]
  -- `F ≠ B`: otherwise `∠BDA = ∠DBC`, contradicting the angle sum.
  have hFneB : F ≠ B := by
    intro hFB
    rw [hFB] at hDF
    have hvBDA0 : ∠ B D A = π - (∠ D A B + ∠ D B A) := by
      have c1 : ∠ A B D = ∠ D B A := EuclideanGeometry.angle_comm A B D
      linarith [hsumABD, c1]
    rw [hvBDA0] at hDF
    have c1 : ∠ C B D = ∠ D B C := EuclideanGeometry.angle_comm C B D
    have c2 : ∠ C B A = ∠ A B C := EuclideanGeometry.angle_comm C B A
    have c3 : ∠ B C A = ∠ A C B := EuclideanGeometry.angle_comm B C A
    have c4 : ∠ C A B = ∠ B A C := EuclideanGeometry.angle_comm C A B
    have c5 : ∠ B A D = ∠ D A B := EuclideanGeometry.angle_comm B A D
    have c6 : ∠ D A C = ∠ C A D := EuclideanGeometry.angle_comm D A C
    have hp1 : 0 < ∠ C A D := EuclideanGeometry.angle_pos_of_not_collinear hncCAD
    have hp2 : 0 < ∠ A C B := EuclideanGeometry.angle_pos_of_not_collinear hncACB
    linarith [hDF, hcevB, hcevA, hsumABC, c1, c2, c3, c4, c5, c6, hp1, hp2, hbis]
  -- Ray equalities and the remaining angle values.
  have hDCE : ∠ D C E = ∠ D C A := hEw.symm.angle_eq_right D hEneC
  have hFAD : ∠ F A D = ∠ B A D := hFw.angle_eq_left D hFneA
  have hAEC : ∠ A E C = π := EuclideanGeometry.angle_eq_pi_iff_sbtw.mpr ⟨hEw, hEneA, hEneC⟩
  have hDEADEC : ∠ D E A + ∠ D E C = π := EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi D hAEC
  have hvDEC : ∠ D E C = ∠ C A D + ∠ B C D := by
    have c1 : ∠ C E D = ∠ D E C := EuclideanGeometry.angle_comm C E D
    linarith [hsumDCE, c1, hDCE, hvEDC, hvADC]
  have hvDEA : ∠ D E A = π - (∠ C A D + ∠ B C D) := by
    linarith [hDEADEC, hvDEC]
  have hvAFD : ∠ A F D = π - (∠ D A B + ∠ D B C) := by
    have c1 : ∠ D A F = ∠ F A D := EuclideanGeometry.angle_comm D A F
    have c2 : ∠ B A D = ∠ D A B := EuclideanGeometry.angle_comm B A D
    linarith [hsumDAF, c1, c2, hFAD, hDF]
  have hvBDA : ∠ B D A = π - (∠ D A B + ∠ D B A) := by
    have c1 : ∠ A B D = ∠ D B A := EuclideanGeometry.angle_comm A B D
    linarith [hsumABD, c1]
  -- Positivity of sines.
  have hpα : 0 < ∠ C A D := EuclideanGeometry.angle_pos_of_not_collinear hncCAD
  have hpβ : 0 < ∠ B C D := EuclideanGeometry.angle_pos_of_not_collinear hncBCD
  have hpγ : 0 < ∠ D B C := EuclideanGeometry.angle_pos_of_not_collinear hncDBC
  have hpφ : 0 < ∠ D C A := EuclideanGeometry.angle_pos_of_not_collinear hncDCA
  have hpε : 0 < ∠ D B A := EuclideanGeometry.angle_pos_of_not_collinear hncDBA
  have hsinαβ : 0 < Real.sin (∠ C A D + ∠ B C D) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hsum, hpα, hpγ, hpφ, hpε])
  have hsinαγ : 0 < Real.sin (∠ C A D + ∠ D B C) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hsum, hpα, hpβ, hpφ, hpε])
  have hsinφ : 0 < Real.sin (∠ D C A) :=
    Real.sin_pos_of_pos_of_lt_pi hpφ (EuclideanGeometry.angle_lt_pi_of_not_collinear hncDCA)
  have hsinε : 0 < Real.sin (∠ D B A) :=
    Real.sin_pos_of_pos_of_lt_pi hpε (EuclideanGeometry.angle_lt_pi_of_not_collinear hncDBA)
  -- The law of sines, applied in the five triangles.
  have sinDEA : Real.sin (∠ D E A) = Real.sin (∠ C A D + ∠ B C D) := by
    rw [hvDEA, Real.sin_pi_sub]
  have sinAFD : Real.sin (∠ D F A) = Real.sin (∠ D A B + ∠ D B C) := by
    have c4 : ∠ D F A = ∠ A F D := EuclideanGeometry.angle_comm D F A
    rw [c4, hvAFD, Real.sin_pi_sub]
  have sinCDA : Real.sin (∠ C D A) = Real.sin (∠ C A D + ∠ D C A) := by
    rw [hvADC, Real.sin_pi_sub]
  have sinBDA : Real.sin (∠ B D A) = Real.sin (∠ D A B + ∠ D B A) := by
    rw [hvBDA, Real.sin_pi_sub]
  have e1 : dist A E * Real.sin (∠ C A D + ∠ B C D) = dist A D * Real.sin (∠ B C D) := by
    have h := dist_mul_sin_eq_dist_mul_sin hncDEA
    have c1 : ∠ E D A = ∠ A D E := EuclideanGeometry.angle_comm E D A
    have c2 : dist D A = dist A D := dist_comm D A
    have c3 : dist E A = dist A E := dist_comm E A
    rw [c1, hDE, c2, c3, sinDEA] at h
    exact h.symm
  have e2 : dist A F * Real.sin (∠ C A D + ∠ D B C) = dist A D * Real.sin (∠ D B C) := by
    have h := dist_mul_sin_eq_dist_mul_sin hncDFA
    have c2 : dist D A = dist A D := dist_comm D A
    have c3 : dist F A = dist A F := dist_comm F A
    rw [hDF, c2, c3, sinAFD, hbis] at h
    exact h.symm
  have e3 : dist A C * Real.sin (∠ D C A) = dist A D * Real.sin (∠ C A D + ∠ D C A) := by
    have h := dist_mul_sin_eq_dist_mul_sin hncCDA
    have c2 : dist C A = dist A C := dist_comm C A
    have c3 : dist D A = dist A D := dist_comm D A
    rw [c2, c3, sinCDA] at h
    exact h
  have e4 : dist A B * Real.sin (∠ D B A) = dist A D * Real.sin (∠ C A D + ∠ D B A) := by
    have h := dist_mul_sin_eq_dist_mul_sin hncBDA
    have c2 : dist B A = dist A B := dist_comm B A
    have c3 : dist D A = dist A D := dist_comm D A
    rw [c2, c3, sinBDA, hbis] at h
    exact h
  have e5 : dist B D * Real.sin (∠ D B A) = dist A D * Real.sin (∠ D A B) := by
    have h := dist_mul_sin_eq_dist_mul_sin hncBAD
    have c1 : ∠ A B D = ∠ D B A := EuclideanGeometry.angle_comm A B D
    have c2 : ∠ B A D = ∠ D A B := EuclideanGeometry.angle_comm B A D
    rw [c1, c2] at h
    exact h
  have e6 : dist C D * Real.sin (∠ D C A) = dist A D * Real.sin (∠ C A D) := by
    have h := dist_mul_sin_eq_dist_mul_sin hncCAD
    have c1 : ∠ A C D = ∠ D C A := EuclideanGeometry.angle_comm A C D
    rw [c1] at h
    exact h
  have e7 : dist B D * Real.sin (∠ D B C) = dist C D * Real.sin (∠ B C D) := by
    have h := dist_mul_sin_eq_dist_mul_sin hncBCD
    have c1 : ∠ C B D = ∠ D B C := EuclideanGeometry.angle_comm C B D
    rw [c1] at h
    exact h
  -- Trigonometric Ceva.
  have hcev : Real.sin (∠ B C D) * Real.sin (∠ D B A) =
      Real.sin (∠ D B C) * Real.sin (∠ D C A) := by
    have hCD0 : dist C D ≠ 0 := (dist_pos.mpr hCD).ne'
    have hi : dist B D * Real.sin (∠ D B A) = dist C D * Real.sin (∠ D C A) := by
      rw [e5, e6, hbis]
    have hii : dist B D * Real.sin (∠ D B C) = dist C D * Real.sin (∠ B C D) := e7
    apply mul_left_cancel₀ hCD0
    calc dist C D * (Real.sin (∠ B C D) * Real.sin (∠ D B A))
        = dist C D * Real.sin (∠ B C D) * Real.sin (∠ D B A) := by ring
      _ = dist B D * Real.sin (∠ D B C) * Real.sin (∠ D B A) := by rw [hii]
      _ = dist B D * Real.sin (∠ D B A) * Real.sin (∠ D B C) := by ring
      _ = dist C D * Real.sin (∠ D C A) * Real.sin (∠ D B C) := by rw [hi]
      _ = dist C D * (Real.sin (∠ D B C) * Real.sin (∠ D C A)) := by ring
  -- The product identity.
  have hid : Real.sin (∠ C A D + ∠ D C A) * Real.sin (∠ C A D + ∠ D B C) =
      Real.sin (∠ C A D + ∠ D B A) * Real.sin (∠ C A D + ∠ B C D) :=
    sin_mul_sin_eq_sin_mul_sin hsum hcev
  have hprod : Real.sin (∠ B C D) * Real.sin (∠ C A D + ∠ D C A) *
        (Real.sin (∠ C A D + ∠ D B C) * Real.sin (∠ D B A)) =
      Real.sin (∠ D B C) * Real.sin (∠ C A D + ∠ D B A) *
        (Real.sin (∠ C A D + ∠ B C D) * Real.sin (∠ D C A)) := by
    rw [show Real.sin (∠ B C D) * Real.sin (∠ C A D + ∠ D C A) *
          (Real.sin (∠ C A D + ∠ D B C) * Real.sin (∠ D B A)) =
        (Real.sin (∠ B C D) * Real.sin (∠ D B A)) *
          (Real.sin (∠ C A D + ∠ D C A) * Real.sin (∠ C A D + ∠ D B C)) by ring]
    rw [show Real.sin (∠ D B C) * Real.sin (∠ C A D + ∠ D B A) *
          (Real.sin (∠ C A D + ∠ B C D) * Real.sin (∠ D C A)) =
        (Real.sin (∠ D B C) * Real.sin (∠ D C A)) *
          (Real.sin (∠ C A D + ∠ D B A) * Real.sin (∠ C A D + ∠ B C D)) by ring]
    rw [hcev, hid]
  -- Final assembly: multiply out and cancel the positive sine factor.
  have k1 : dist A E * dist A C * (Real.sin (∠ C A D + ∠ B C D) * Real.sin (∠ D C A) *
        (Real.sin (∠ C A D + ∠ D B C) * Real.sin (∠ D B A))) =
      dist A F * dist A B * (Real.sin (∠ C A D + ∠ B C D) * Real.sin (∠ D C A) *
        (Real.sin (∠ C A D + ∠ D B C) * Real.sin (∠ D B A))) := by
    have m1 : (dist A E * Real.sin (∠ C A D + ∠ B C D)) * (dist A C * Real.sin (∠ D C A)) *
        (Real.sin (∠ C A D + ∠ D B C) * Real.sin (∠ D B A)) =
        (dist A F * Real.sin (∠ C A D + ∠ D B C)) * (dist A B * Real.sin (∠ D B A)) *
        (Real.sin (∠ C A D + ∠ B C D) * Real.sin (∠ D C A)) := by
      rw [e1, e3, e2, e4]
      rw [show dist A D * Real.sin (∠ B C D) * (dist A D * Real.sin (∠ C A D + ∠ D C A)) *
            (Real.sin (∠ C A D + ∠ D B C) * Real.sin (∠ D B A)) =
          (dist A D * dist A D) * (Real.sin (∠ B C D) * Real.sin (∠ C A D + ∠ D C A) *
            (Real.sin (∠ C A D + ∠ D B C) * Real.sin (∠ D B A))) by ring]
      rw [show dist A D * Real.sin (∠ D B C) * (dist A D * Real.sin (∠ C A D + ∠ D B A)) *
            (Real.sin (∠ C A D + ∠ B C D) * Real.sin (∠ D C A)) =
          (dist A D * dist A D) * (Real.sin (∠ D B C) * Real.sin (∠ C A D + ∠ D B A) *
            (Real.sin (∠ C A D + ∠ B C D) * Real.sin (∠ D C A))) by ring]
      rw [hprod]
    have n1 : dist A E * dist A C * (Real.sin (∠ C A D + ∠ B C D) * Real.sin (∠ D C A) *
        (Real.sin (∠ C A D + ∠ D B C) * Real.sin (∠ D B A))) =
        (dist A E * Real.sin (∠ C A D + ∠ B C D)) * (dist A C * Real.sin (∠ D C A)) *
        (Real.sin (∠ C A D + ∠ D B C) * Real.sin (∠ D B A)) := by ring
    have n2 : dist A F * dist A B * (Real.sin (∠ C A D + ∠ B C D) * Real.sin (∠ D C A) *
        (Real.sin (∠ C A D + ∠ D B C) * Real.sin (∠ D B A))) =
        (dist A F * Real.sin (∠ C A D + ∠ D B C)) * (dist A B * Real.sin (∠ D B A)) *
        (Real.sin (∠ C A D + ∠ B C D) * Real.sin (∠ D C A)) := by ring
    rw [n1, n2]
    exact m1
  have hpos : 0 < Real.sin (∠ C A D + ∠ B C D) * Real.sin (∠ D C A) *
      (Real.sin (∠ C A D + ∠ D B C) * Real.sin (∠ D B A)) :=
    mul_pos (mul_pos hsinαβ hsinφ) (mul_pos hsinαγ hsinε)
  exact mul_right_cancel₀ (ne_of_gt hpos) k1

/-- `E ≠ A`: the angle `∠BCD` is nonzero, but `∠ADA = 0`. -/
theorem E_ne_A {A B C D E : P} (hai : AffineIndependent ℝ ![A, B, C])
    (hDint : D ∈ (⟨_, hai⟩ : Triangle ℝ P).interior) (hDE : ∠ A D E = ∠ B C D) : E ≠ A := by
  intro hEA
  have hAD : A ≠ D := by
    rintro rfl
    exact Simplex.point_notMem_interior _ 0 hDint
  have hBC : B ≠ C := hai.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  have hDnBC : D ∉ line[ℝ, B, C] := not_mem_line_of_mem_interior hai hDint
  have hnc : ¬Collinear ℝ ({B, C, D} : Set P) :=
    fun h => hDnBC (h.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hBC)
  have hBCDne : ∠ B C D ≠ 0 := EuclideanGeometry.angle_ne_zero_of_not_collinear hnc
  rw [hEA, EuclideanGeometry.angle_self_of_ne hAD] at hDE
  exact hBCDne hDE.symm

/-- `E ≠ C`: otherwise `∠ADC = ∠BCD`, contradicting the angle sum of `ABC`. -/
theorem E_ne_C {A B C D E : P} (hai : AffineIndependent ℝ ![A, B, C])
    (hDint : D ∈ (⟨_, hai⟩ : Triangle ℝ P).interior)
    (hbis : ∠ D A B = ∠ C A D) (hEw : Wbtw ℝ A E C) (hDE : ∠ A D E = ∠ B C D) : E ≠ C := by
  intro hEC
  rw [hEC] at hDE
  have hAB : A ≠ B := hai.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hAC : A ≠ C := hai.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hBC : B ≠ C := hai.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  have hAD : A ≠ D := by
    rintro rfl
    exact Simplex.point_notMem_interior _ 0 hDint
  have hCD : C ≠ D := by
    rintro rfl
    exact Simplex.point_notMem_interior _ 2 hDint
  have hCA : C ≠ A := hAC.symm
  have hCB : C ≠ B := hBC.symm
  have hai_BCA : AffineIndependent ℝ ![B, C, A] := affineIndependent_cycle hai
  have hai_CAB : AffineIndependent ℝ ![C, A, B] := affineIndependent_cycle hai_BCA
  have hDint_BCA := mem_interior_cycle hai hai_BCA hDint
  have hDint_CAB := mem_interior_cycle hai_BCA hai_CAB hDint_BCA
  have hcevA : ∠ B A D + ∠ D A C = ∠ B A C := angle_add_of_mem_interior hai hDint hAB hAC hAD
  have hcevC : ∠ A C D + ∠ D C B = ∠ A C B :=
    angle_add_of_mem_interior hai_CAB hDint_CAB hCA hCB hCD
  have hsumACD : ∠ A C D + ∠ C D A + ∠ D A C = π :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi D hCA
  have hsumABC : ∠ B C A + ∠ C A B + ∠ A B C = π :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi A hCB
  have hvADC : ∠ C D A = π - (∠ C A D + ∠ D C A) := by
    have c1 : ∠ A C D = ∠ D C A := EuclideanGeometry.angle_comm A C D
    have c2 : ∠ D A C = ∠ C A D := EuclideanGeometry.angle_comm D A C
    linarith [hsumACD, c1, c2]
  rw [EuclideanGeometry.angle_comm A D C, hvADC] at hDE
  have hDnAB : D ∉ line[ℝ, A, B] := not_mem_line_of_mem_interior hai_CAB hDint_CAB
  have hDnBA : D ∉ line[ℝ, B, A] := by
    have e : line[ℝ, A, B] = line[ℝ, B, A] := by rw [Set.pair_comm]
    rwa [e] at hDnAB
  have hncBDA : ¬Collinear ℝ ({B, D, A} : Set P) :=
    not_collinear_of_not_mem_line (right_mem_affineSpan_pair ℝ B A) hAB.symm hDnBA
  have hncBAD : ¬Collinear ℝ ({B, A, D} : Set P) := not_collinear_swap23 hncBDA
  have hncABC : ¬Collinear ℝ ({A, B, C} : Set P) := affineIndependent_iff_not_collinear_set.mp hai
  have c2 : ∠ D C B = ∠ B C D := EuclideanGeometry.angle_comm D C B
  have c3 : ∠ B C A = ∠ A C B := EuclideanGeometry.angle_comm B C A
  have c4 : ∠ C A B = ∠ B A C := EuclideanGeometry.angle_comm C A B
  have c5 : ∠ D A C = ∠ C A D := EuclideanGeometry.angle_comm D A C
  have c6 : ∠ A C D = ∠ D C A := EuclideanGeometry.angle_comm A C D
  have hp1 : 0 < ∠ B A D := EuclideanGeometry.angle_pos_of_not_collinear hncBAD
  have hp2 : 0 < ∠ A B C := EuclideanGeometry.angle_pos_of_not_collinear hncABC
  linarith [hDE, hcevA, hcevC, c2, c3, c4, c5, c6, hsumABC, hp1, hp2]

/-- `F ≠ A`: the angle `∠DBC` is nonzero, but `∠ADA = 0`. -/
theorem F_ne_A {A B C D F : P} (hai : AffineIndependent ℝ ![A, B, C])
    (hDint : D ∈ (⟨_, hai⟩ : Triangle ℝ P).interior) (hDF : ∠ F D A = ∠ D B C) : F ≠ A := by
  intro hFA
  have hAD : A ≠ D := by
    rintro rfl
    exact Simplex.point_notMem_interior _ 0 hDint
  have hBC : B ≠ C := hai.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  have hDnBC : D ∉ line[ℝ, B, C] := not_mem_line_of_mem_interior hai hDint
  have hncBCD : ¬Collinear ℝ ({B, C, D} : Set P) :=
    fun h => hDnBC (h.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hBC)
  have hncDBC : ¬Collinear ℝ ({D, B, C} : Set P) := not_collinear_swap (not_collinear_swap23 hncBCD)
  have hne : ∠ D B C ≠ 0 := EuclideanGeometry.angle_ne_zero_of_not_collinear hncDBC
  rw [hFA, EuclideanGeometry.angle_self_of_ne hAD] at hDF
  exact hne hDF.symm

/-- `F ≠ B`: otherwise `∠BDA = ∠DBC`, contradicting the angle sum of `ABC`. -/
theorem F_ne_B {A B C D F : P} (hai : AffineIndependent ℝ ![A, B, C])
    (hDint : D ∈ (⟨_, hai⟩ : Triangle ℝ P).interior)
    (hbis : ∠ D A B = ∠ C A D) (hFw : Wbtw ℝ A F B) (hDF : ∠ F D A = ∠ D B C) : F ≠ B := by
  intro hFB
  rw [hFB] at hDF
  have hAB : A ≠ B := hai.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hAC : A ≠ C := hai.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hBC : B ≠ C := hai.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  have hAD : A ≠ D := by
    rintro rfl
    exact Simplex.point_notMem_interior _ 0 hDint
  have hBD : B ≠ D := by
    rintro rfl
    exact Simplex.point_notMem_interior _ 1 hDint
  have hBA : B ≠ A := hAB.symm
  have hCA : C ≠ A := hAC.symm
  have hCB : C ≠ B := hBC.symm
  have hai_BCA : AffineIndependent ℝ ![B, C, A] := affineIndependent_cycle hai
  have hDint_BCA := mem_interior_cycle hai hai_BCA hDint
  have hcevA : ∠ B A D + ∠ D A C = ∠ B A C := angle_add_of_mem_interior hai hDint hAB hAC hAD
  have hcevB : ∠ C B D + ∠ D B A = ∠ C B A :=
    angle_add_of_mem_interior hai_BCA hDint_BCA hBC hBA hBD
  have hsumABD : ∠ A B D + ∠ B D A + ∠ D A B = π :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi D hBA
  have hsumABC : ∠ B C A + ∠ C A B + ∠ A B C = π :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi A hCB
  have hvBDA : ∠ B D A = π - (∠ D A B + ∠ D B A) := by
    have c1 : ∠ A B D = ∠ D B A := EuclideanGeometry.angle_comm A B D
    linarith [hsumABD, c1]
  rw [hvBDA] at hDF
  have hDnCA : D ∉ line[ℝ, C, A] := not_mem_line_of_mem_interior hai_BCA hDint_BCA
  have hncCDA : ¬Collinear ℝ ({C, D, A} : Set P) :=
    not_collinear_of_not_mem_line (right_mem_affineSpan_pair ℝ C A) hCA hDnCA
  have hncCAD : ¬Collinear ℝ ({C, A, D} : Set P) := not_collinear_swap23 hncCDA
  have hncACB : ¬Collinear ℝ ({A, C, B} : Set P) :=
    not_collinear_swap23 (affineIndependent_iff_not_collinear_set.mp hai)
  have c1 : ∠ C B D = ∠ D B C := EuclideanGeometry.angle_comm C B D
  have c2 : ∠ C B A = ∠ A B C := EuclideanGeometry.angle_comm C B A
  have c3 : ∠ B C A = ∠ A C B := EuclideanGeometry.angle_comm B C A
  have c4 : ∠ C A B = ∠ B A C := EuclideanGeometry.angle_comm C A B
  have c5 : ∠ B A D = ∠ D A B := EuclideanGeometry.angle_comm B A D
  have c6 : ∠ D A C = ∠ C A D := EuclideanGeometry.angle_comm D A C
  have hp1 : 0 < ∠ C A D := EuclideanGeometry.angle_pos_of_not_collinear hncCAD
  have hp2 : 0 < ∠ A C B := EuclideanGeometry.angle_pos_of_not_collinear hncACB
  linarith [hDF, hcevB, hcevA, hsumABC, c1, c2, c3, c4, c5, c6, hp1, hp2, hbis]

/-- If `E` lies on `AC`, `F` on `AB` (both different from `A`), then `E, A, F` are not
collinear (since `A, B, C` are not). -/
theorem not_collinear_EAF {A B C E F : P} (hai : AffineIndependent ℝ ![A, B, C])
    (hE : E ∈ line[ℝ, A, C]) (hF : F ∈ line[ℝ, A, B]) (hEA : E ≠ A) (hFA : F ≠ A) :
    ¬Collinear ℝ ({E, A, F} : Set P) := by
  intro hcol
  have hncABC : ¬Collinear ℝ ({A, B, C} : Set P) := affineIndependent_iff_not_collinear_set.mp hai
  have hF_line : F ∈ line[ℝ, E, A] :=
    hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hEA
  have hEq : line[ℝ, E, A] = line[ℝ, A, C] := by
    have hcoll : Collinear ℝ ({E, A, C} : Set P) := collinear_insert_of_mem_affineSpan_pair hE
    have h1 := hcoll.affineSpan_eq_of_ne (show E ∈ ({E, A, C} : Set P) by simp)
      (show A ∈ ({E, A, C} : Set P) by simp) hEA
    rw [h1]
    apply le_antisymm
    · rw [affineSpan_le, Set.insert_subset_iff, Set.insert_subset_iff]
      refine ⟨hE, left_mem_affineSpan_pair ℝ A C, ?_⟩
      simp [right_mem_affineSpan_pair ℝ A C]
    · apply affineSpan_mono ℝ
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      tauto
  rw [hEq] at hF_line
  have hB_line : B ∈ line[ℝ, A, F] :=
    (collinear_insert_of_mem_affineSpan_pair hF).mem_affineSpan_of_mem_of_ne
      (by simp) (by simp) (by simp) hFA.symm
  have hC_line : C ∈ line[ℝ, A, F] :=
    (collinear_insert_of_mem_affineSpan_pair hF_line).mem_affineSpan_of_mem_of_ne
      (by simp) (by simp) (by simp) hFA.symm
  have hcol4 : Collinear ℝ ({B, C, A, F} : Set P) :=
    collinear_insert_insert_of_mem_affineSpan_pair hB_line hC_line
  have hcol3 : Collinear ℝ ({A, B, C} : Set P) := hcol4.subset (by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto)
  exact hncABC hcol3


/-- The "two secants" converse of the power-of-a-point theorem: if `p` lies strictly
outside the segments `p₁p₂` and `p₃p₄`, and `dist p₁ p * dist p₂ p = dist p₃ p * dist p₄ p`,
then the four points are cospherical. Auxiliary version, in an oriented 2-dimensional
space. -/
private theorem cospherical_of_mul_dist_eq_mul_dist_of_sbtw_aux
    [Module.Oriented ℝ V (Fin 2)] {p₁ p₂ p₃ p₄ p : P}
    (h : dist p₁ p * dist p₂ p = dist p₃ p * dist p₄ p)
    (hp₁₂ : Sbtw ℝ p p₁ p₂) (hp₃₄ : Sbtw ℝ p p₃ p₄) (hn : ¬ Collinear ℝ ({p₁, p, p₃} : Set P)) :
    EuclideanGeometry.Cospherical ({p₁, p₂, p₃, p₄} : Set P) := by
  have h_angle_eq : ∠ p₁ p p₄ = ∠ p₃ p p₂ := by
    have e1 : ∠ p₁ p p₄ = ∠ p₂ p p₄ := hp₁₂.wbtw.angle_eq_left p₄ hp₁₂.ne_left
    have e2 : ∠ p₂ p p₃ = ∠ p₂ p p₄ := hp₃₄.wbtw.angle_eq_right p₂ hp₃₄.ne_left
    rw [e1, e2.symm, EuclideanGeometry.angle_comm p₂ p p₃]
  have h_notcol_p₁p₂p₃ : ¬ Collinear ℝ ({p₁, p₂, p₃} : Set P) := by
    have hai : AffineIndependent ℝ ![p₁, p, p₃] := affineIndependent_iff_not_collinear_set.mpr hn
    rw [← affineIndependent_iff_not_collinear_set]
    have hcol : Collinear ℝ ({p₁, p, p₂} : Set P) := by
      have h' := hp₁₂.wbtw.collinear
      rwa [show ({p, p₁, p₂} : Set P) = {p₁, p, p₂} by
        ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at h'
    have h1 := affineIndependent_of_affineIndependent_collinear_ne
      (AffineIndependent.comm_left (AffineIndependent.comm_right hai)) hcol hp₁₂.ne_right
    exact AffineIndependent.comm_right (AffineIndependent.comm_left h1)
  have h_notcol_p₁pp₄ : ¬ Collinear ℝ ({p₁, p, p₄} : Set P) := by
    intro hcol
    apply hn
    have hp₃mem : p₃ ∈ line[ℝ, p, p₄] := hp₃₄.wbtw.mem_affineSpan
    have hp₁mem : p₁ ∈ line[ℝ, p, p₄] :=
      hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hp₃₄.left_ne_right
    have hcol4 : Collinear ℝ ({p₁, p₃, p, p₄} : Set P) :=
      collinear_insert_insert_of_mem_affineSpan_pair hp₁mem hp₃mem
    exact hcol4.subset (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      tauto)
  have h_notcol_p₃pp₂ : ¬ Collinear ℝ ({p₃, p, p₂} : Set P) := by
    intro hcol
    apply hn
    have hp₁mem : p₁ ∈ line[ℝ, p, p₂] := hp₁₂.wbtw.mem_affineSpan
    have hp₃mem : p₃ ∈ line[ℝ, p, p₂] :=
      hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hp₁₂.left_ne_right
    have hcol4 : Collinear ℝ ({p₃, p₁, p, p₂} : Set P) :=
      collinear_insert_insert_of_mem_affineSpan_pair hp₃mem hp₁mem
    exact hcol4.subset (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      tauto)
  suffices h' : EuclideanGeometry.Cospherical ({p₁, p₂, p₄, p₃} : Set P) by
    rwa [show ({p₁, p₂, p₄, p₃} : Set P) = {p₁, p₂, p₃, p₄} by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at h'
  apply EuclideanGeometry.cospherical_of_two_zsmul_oangle_eq_of_not_collinear ?_ h_notcol_p₁p₂p₃
  have h_unor : ∠ p₁ p₂ p₃ = ∠ p₁ p₄ p₃ := by
    have e1 : ∠ p₁ p₂ p₃ = ∠ p p₂ p₃ := hp₁₂.symm.wbtw.angle_eq_left p₃ hp₁₂.ne_right
    have e2 : ∠ p₁ p₄ p₃ = ∠ p₁ p₄ p := hp₃₄.symm.wbtw.angle_eq_right p₁ hp₃₄.ne_right
    have h_sim : Similar ![p₁, p, p₄] ![p₃, p, p₂] := by
      apply EuclideanGeometry.similar_of_side_angle_side h_notcol_p₁pp₄ h_notcol_p₃pp₂
        h_angle_eq ?_
      grind [dist_comm]
    have e3 : ∠ p p₂ p₃ = ∠ p p₄ p₁ := h_sim.angle_eq_all.2.1.symm
    rw [e1, e2, e3, EuclideanGeometry.angle_comm p p₄ p₁]
  have h_sign : (∡ p₁ p₂ p₃).sign = (∡ p₁ p₄ p₃).sign :=
    (Sbtw.oangle_sign_eq_of_sbtw_left hp₁₂ hp₃₄).symm
  have h_o : ∡ p₁ p₂ p₃ = ∡ p₁ p₄ p₃ :=
    EuclideanGeometry.oangle_eq_of_angle_eq_of_sign_eq h_unor h_sign
  rw [h_o]

/-- The "two secants" converse of the power-of-a-point theorem: if `p` lies strictly
outside the segments `p₁p₂` and `p₃p₄`, and `dist p₁ p * dist p₂ p = dist p₃ p * dist p₄ p`,
then the four points are cospherical. -/
theorem cospherical_of_mul_dist_eq_mul_dist_of_sbtw {p₁ p₂ p₃ p₄ p : P}
    (h : dist p₁ p * dist p₂ p = dist p₃ p * dist p₄ p)
    (hp₁₂ : Sbtw ℝ p p₁ p₂) (hp₃₄ : Sbtw ℝ p p₃ p₄) (hn : ¬ Collinear ℝ ({p₁, p, p₃} : Set P)) :
    EuclideanGeometry.Cospherical ({p₁, p₂, p₃, p₄} : Set P) := by
  have hindep : AffineIndependent ℝ ![p₁, p, p₃] := affineIndependent_iff_not_collinear_set.mpr hn
  set t : Affine.Triangle ℝ P := ⟨_, hindep⟩ with ht
  set S : AffineSubspace ℝ P := affineSpan ℝ (Set.range t.points) with hS
  have hp₂ : p₂ ∈ S := by
    suffices hmem : p₂ ∈ affineSpan ℝ {p₁, p} by exact affineSpan_mono ℝ (by simp [ht]; grind) hmem
    exact hp₁₂.wbtw.collinear.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hp₁₂.ne_left
  have hp₄ : p₄ ∈ S := by
    suffices hmem : p₄ ∈ affineSpan ℝ {p₃, p} by exact affineSpan_mono ℝ (by simp [ht]; grind) hmem
    exact hp₃₄.wbtw.collinear.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hp₃₄.ne_left
  let s_isom : AffineIsometry ℝ S P := S.subtypeₐᵢ
  let p₁' : S := ⟨p₁, mem_affineSpan ℝ (s := Set.range t.points) (by aesop)⟩
  let p' : S := ⟨p, mem_affineSpan ℝ (s := Set.range t.points) (by aesop)⟩
  let p₃' : S := ⟨p₃, mem_affineSpan ℝ (s := Set.range t.points) (by aesop)⟩
  let p₂' : S := ⟨p₂, hp₂⟩
  let p₄' : S := ⟨p₄, hp₄⟩
  have h_dist' : dist p₁' p' * dist p₂' p' = dist p₃' p' * dist p₄' p' := by
    simpa [dist_eq_norm_vsub, ← s_isom.dist_map] using h
  have hp₁₂' : Sbtw ℝ p' p₁' p₂' := by
    rw [sbtw_iff_mem_image_Ioo_and_ne] at hp₁₂
    obtain ⟨hs, hne⟩ := hp₁₂
    rw [sbtw_iff_mem_image_Ioo_and_ne]
    obtain ⟨r, hr, hreq⟩ := hs
    refine ⟨⟨r, hr, Subtype.ext ?_⟩, fun hcontra => hne (Subtype.ext_iff.mp hcontra)⟩
    show AffineSubspace.subtype S (AffineMap.lineMap p' p₂' r) = p₁
    rw [AffineMap.apply_lineMap]
    exact hreq
  have hp₃₄' : Sbtw ℝ p' p₃' p₄' := by
    rw [sbtw_iff_mem_image_Ioo_and_ne] at hp₃₄
    obtain ⟨hs, hne⟩ := hp₃₄
    rw [sbtw_iff_mem_image_Ioo_and_ne]
    obtain ⟨r, hr, hreq⟩ := hs
    refine ⟨⟨r, hr, Subtype.ext ?_⟩, fun hcontra => hne (Subtype.ext_iff.mp hcontra)⟩
    show AffineSubspace.subtype S (AffineMap.lineMap p' p₄' r) = p₃
    rw [AffineMap.apply_lineMap]
    exact hreq
  have hncol : ¬ Collinear ℝ {p₁', p', p₃'} := by
    rw [← affineIndependent_iff_not_collinear_set,
      ← s_isom.toAffineMap.affineIndependent_iff s_isom.injective]
    convert! hindep
    ext i; fin_cases i <;> rfl
  have hf2 : Fact (finrank ℝ S.direction = 2) := ⟨by
    rw [hS, direction_affineSpan, t.independent.finrank_vectorSpan]
    simp⟩
  letI : Module.Oriented ℝ S.direction (Fin 2) :=
    ⟨Basis.orientation (finBasisOfFinrankEq _ _ hf2.out)⟩
  have h_cospherical' : EuclideanGeometry.Cospherical ({p₁', p₂', p₃', p₄'} : Set S) :=
    cospherical_of_mul_dist_eq_mul_dist_of_sbtw_aux h_dist' hp₁₂' hp₃₄' hncol
  simpa [Set.image_insert_eq, Set.image_singleton] using
    EuclideanGeometry.Cospherical.subtype_val h_cospherical'

/-- The points `B, C, E, F` are concyclic: from `AE · AC = AF · AB` by the converse of
the power-of-a-point theorem. -/
theorem concyclic_BCEF {A B C D E F : P}
    (hai : AffineIndependent ℝ ![A, B, C])
    (hDint : D ∈ (⟨_, hai⟩ : Triangle ℝ P).interior)
    (hbis : ∠ D A B = ∠ C A D)
    (hEw : Wbtw ℝ A E C) (hDE : ∠ A D E = ∠ B C D)
    (hFw : Wbtw ℝ A F B) (hDF : ∠ F D A = ∠ D B C) :
    EuclideanGeometry.Concyclic ({B, C, E, F} : Set P) := by
  have hEneA := E_ne_A hai hDint hDE
  have hEneC := E_ne_C hai hDint hbis hEw hDE
  have hFneA := F_ne_A hai hDint hDF
  have hFneB := F_ne_B hai hDint hbis hFw hDF
  have hmul := dist_AE_mul_AC_eq_dist_AF_mul_AB hai hDint hbis hEw hDE hFw hDF
  have hmul' : dist E A * dist C A = dist F A * dist B A := by
    rw [dist_comm E A, dist_comm C A, dist_comm F A, dist_comm B A]
    exact hmul
  have hEAC : Sbtw ℝ A E C := ⟨hEw, hEneA, hEneC⟩
  have hFAB : Sbtw ℝ A F B := ⟨hFw, hFneA, hFneB⟩
  have hnEAF : ¬Collinear ℝ ({E, A, F} : Set P) :=
    not_collinear_EAF hai hEw.mem_affineSpan hFw.mem_affineSpan hEneA hFneA
  have hcosp : EuclideanGeometry.Cospherical ({E, C, F, B} : Set P) :=
    cospherical_of_mul_dist_eq_mul_dist_of_sbtw hmul' hEAC hFAB hnEAF
  have hcosp' : EuclideanGeometry.Cospherical ({B, C, E, F} : Set P) := by
    rwa [show ({E, C, F, B} : Set P) = {B, C, E, F} by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at hcosp
  exact ⟨hcosp', coplanar_of_fact_finrank_eq_two _⟩

/-- `E ≠ F`: a common point of lines `AC` and `AB` different from `A` would force
`A, B, C` to be collinear. -/
theorem E_ne_F {A B C E F : P} (hai : AffineIndependent ℝ ![A, B, C])
    (hEw : Wbtw ℝ A E C) (hFw : Wbtw ℝ A F B) (hEA : E ≠ A) (hFA : F ≠ A) : E ≠ F := by
  intro hEF'
  have hEAC : E ∈ line[ℝ, A, C] := hEw.mem_affineSpan
  have hFAB : F ∈ line[ℝ, A, B] := hFw.mem_affineSpan
  subst hEF'
  have hncABC : ¬Collinear ℝ ({A, B, C} : Set P) := affineIndependent_iff_not_collinear_set.mp hai
  have hB_line : B ∈ line[ℝ, E, A] :=
    (collinear_insert_of_mem_affineSpan_pair hFAB).mem_affineSpan_of_mem_of_ne
      (by simp) (by simp) (by simp) hEA
  have hC_line : C ∈ line[ℝ, E, A] :=
    (collinear_insert_of_mem_affineSpan_pair hEAC).mem_affineSpan_of_mem_of_ne
      (by simp) (by simp) (by simp) hEA
  have hcol4 : Collinear ℝ ({B, C, E, A} : Set P) :=
    collinear_insert_insert_of_mem_affineSpan_pair hB_line hC_line
  have hcol3 : Collinear ℝ ({A, B, C} : Set P) := hcol4.subset (by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto)
  exact hncABC hcol3

/-- The intersection point `Z` of lines `BC` and `EF`, constructed explicitly together with
its ordering properties: `Z` lies beyond `C` on line `BC` and beyond `E` on line `EF`.
The construction uses `AE · AC = AF · AB` and `AB > AC`. -/
theorem exists_Z {A B C D E F : P}
    (hai : AffineIndependent ℝ ![A, B, C])
    (hDint : D ∈ (⟨_, hai⟩ : Triangle ℝ P).interior)
    (hbis : ∠ D A B = ∠ C A D) (hlt : dist A C < dist A B)
    (hEw : Wbtw ℝ A E C) (hDE : ∠ A D E = ∠ B C D)
    (hFw : Wbtw ℝ A F B) (hDF : ∠ F D A = ∠ D B C) :
    ∃ Z : P, Z ∈ line[ℝ, B, C] ∧ Sbtw ℝ B C Z ∧ Z ∈ line[ℝ, E, F] ∧ Sbtw ℝ Z E F := by
  -- Parameters of `E` and `F` on their respective segments.
  have hEneA := E_ne_A hai hDint hDE
  have hEneC := E_ne_C hai hDint hbis hEw hDE
  have hFneA := F_ne_A hai hDint hDF
  have hFneB := F_ne_B hai hDint hbis hFw hDF
  have hsE : Sbtw ℝ A E C := ⟨hEw, hEneA, hEneC⟩
  have hsF : Sbtw ℝ A F B := ⟨hFw, hFneA, hFneB⟩
  rw [sbtw_iff_mem_image_Ioo_and_ne] at hsE hsF
  obtain ⟨hsE', hAneC⟩ := hsE
  obtain ⟨hsF', hAneB⟩ := hsF
  obtain ⟨eC, heCIoo, hEeq⟩ := hsE'
  obtain ⟨fB, hfBIoo, hFeq⟩ := hsF'
  have hAB : A ≠ B := hai.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hAC : A ≠ C := hai.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hBC : B ≠ C := hai.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  -- Distance relations.
  have hdE : dist A E = eC * dist A C := by
    rw [← hEeq, dist_comm A (AffineMap.lineMap A C eC), dist_lineMap_left, Real.norm_eq_abs,
      abs_of_pos heCIoo.1]
  have hdF : dist A F = fB * dist A B := by
    rw [← hFeq, dist_comm A (AffineMap.lineMap A B fB), dist_lineMap_left, Real.norm_eq_abs,
      abs_of_pos hfBIoo.1]
  -- `eC > fB` from `AE·AC = AF·AB` and `AB > AC`.
  have hmul := dist_AE_mul_AC_eq_dist_AF_mul_AB hai hDint hbis hEw hDE hFw hDF
  rw [hdE, hdF] at hmul
  have heCfB : fB < eC := by
    have hAC0 : 0 < dist A C := dist_pos.mpr hAC
    have hAB0 : 0 < dist A B := dist_pos.mpr hAB
    by_contra hge
    push_neg at hge
    have h6 : eC * dist A C * dist A C = eC * (dist A C * dist A C) := by ring
    have h7 : fB * dist A B * dist A B = fB * (dist A B * dist A B) := by ring
    rw [h6, h7] at hmul
    have h3 : eC * (dist A B * dist A B) ≤ eC * (dist A C * dist A C) := by
      have h5 : eC * (dist A B * dist A B) ≤ fB * (dist A B * dist A B) :=
        mul_le_mul_of_nonneg_right hge (mul_pos hAB0 hAB0).le
      rwa [← hmul] at h5
    have h8 : dist A C * dist A C < dist A B * dist A B :=
      mul_lt_mul hlt hlt.le hAC0 dist_nonneg
    have h9 : dist A B * dist A B ≤ dist A C * dist A C := by
      nlinarith [h3, heCIoo.1]
    linarith [h8, h9]
  -- The explicit parameters of `Z`.
  set u := (1 - fB) * eC / (eC - fB) with hudef
  set v := (eC - 1) / (eC - fB) with hvdef
  have hd0 : eC - fB ≠ 0 := ne_of_gt (sub_pos.mpr heCfB)
  have hu0 : 0 < u := div_pos (mul_pos (sub_pos.mpr hfBIoo.2) heCIoo.1) (sub_pos.mpr heCfB)
  have hu1 : 1 < u := by
    rw [hudef, one_lt_div (sub_pos.mpr heCfB)]
    nlinarith [heCIoo.2, hfBIoo.1]
  have hv0 : v < 0 := div_neg_of_neg_of_pos (sub_neg.mpr heCIoo.2) (sub_pos.mpr heCfB)
  have hscalar1 : v * fB = 1 - u := by
    rw [hvdef, hudef]
    field_simp
    ring
  have hscalar2 : (1 - v) * eC = u := by
    rw [hvdef, hudef]
    field_simp
    ring
  -- The vector identity for `Z` on line `EF` (used twice below).
  have hEv : E -ᵥ A = eC • (C -ᵥ A) := by
    rw [← hEeq, AffineMap.lineMap_apply, vadd_vsub]
  have hFv : F -ᵥ A = fB • (B -ᵥ A) := by
    rw [← hFeq, AffineMap.lineMap_apply, vadd_vsub]
  have hZEF : u • (C -ᵥ B) +ᵥ B = AffineMap.lineMap E F v := by
    apply vsub_left_cancel (p := A)
    rw [AffineMap.lineMap_apply, vadd_vsub_assoc, vadd_vsub_assoc,
      show C -ᵥ B = (C -ᵥ A) - (B -ᵥ A) by rw [vsub_sub_vsub_cancel_right],
      show F -ᵥ E = (F -ᵥ A) - (E -ᵥ A) by rw [vsub_sub_vsub_cancel_right], hEv, hFv]
    rw [show u • ((C -ᵥ A) - (B -ᵥ A)) + (B -ᵥ A) = (1 - u) • (B -ᵥ A) + u • (C -ᵥ A) by
        module,
      show v • (fB • (B -ᵥ A) - eC • (C -ᵥ A)) + eC • (C -ᵥ A) =
        (v * fB) • (B -ᵥ A) + ((1 - v) * eC) • (C -ᵥ A) by module, hscalar1, hscalar2]
  -- The point `Z`.
  refine ⟨u • (C -ᵥ B) +ᵥ B, ?_, ?_, ?_, ?_⟩
  · -- `Z ∈ line[ℝ, B, C]`.
    have hZeq : u • (C -ᵥ B) +ᵥ B = AffineMap.lineMap B C u := by
      rw [AffineMap.lineMap_apply]
    rw [hZeq]
    exact (mem_affineSpan_pair_iff_exists_lineMap_eq).mpr ⟨u, rfl⟩
  · -- `Sbtw ℝ B C Z`: since `C = lineMap B Z (1/u)` with `1/u ∈ (0,1)`.
    have hCeq : C = AffineMap.lineMap B (u • (C -ᵥ B) +ᵥ B) (1 / u) := by
      rw [AffineMap.lineMap_apply, vadd_vsub, smul_smul,
        one_div_mul_cancel (ne_of_gt hu0), one_smul, vsub_vadd C B]
    have hS : Sbtw ℝ B (AffineMap.lineMap B (u • (C -ᵥ B) +ᵥ B) (1 / u))
        (u • (C -ᵥ B) +ᵥ B) := by
      rw [sbtw_lineMap_iff]
      refine ⟨fun hBZ => ?_, one_div_pos.mpr hu0, (div_lt_one hu0).mpr hu1⟩
      · rw [← hBZ] at hCeq
        rw [AffineMap.lineMap_same_apply] at hCeq
        exact hBC hCeq.symm
    rw [← hCeq] at hS
    exact hS
  · -- `Z ∈ line[ℝ, E, F]`.
    rw [hZEF]
    exact (mem_affineSpan_pair_iff_exists_lineMap_eq).mpr ⟨v, rfl⟩
  · -- `Sbtw ℝ Z E F`: since `E = lineMap Z F w` with `w = -v/(1-v) ∈ (0,1)`.
    have hZE : (u • (C -ᵥ B) +ᵥ B) -ᵥ E = v • (F -ᵥ E) := by
      rw [hZEF, AffineMap.lineMap_apply, vadd_vsub]
    have hEeq2 : E = AffineMap.lineMap (u • (C -ᵥ B) +ᵥ B) F (-v / (1 - v)) := by
      have h1v' : (0 : ℝ) < 1 - v := by linarith [hv0]
      apply vsub_left_cancel (p := (u • (C -ᵥ B) +ᵥ B))
      rw [AffineMap.lineMap_apply, vadd_vsub,
        show F -ᵥ (u • (C -ᵥ B) +ᵥ B) = (F -ᵥ E) - ((u • (C -ᵥ B) +ᵥ B) -ᵥ E) by
          rw [vsub_sub_vsub_cancel_right],
        hZE, show E -ᵥ (u • (C -ᵥ B) +ᵥ B) = -(v • (F -ᵥ E)) by
          rw [← hZE, neg_vsub_eq_vsub_rev],
        show (F -ᵥ E) - v • (F -ᵥ E) = (1 - v) • (F -ᵥ E) by module,
        show -(v • (F -ᵥ E)) = -v • (F -ᵥ E) by module, smul_smul,
        show -v / (1 - v) * (1 - v) = -v by rw [div_mul_cancel₀ _ (ne_of_gt h1v')]]
    rw [hEeq2, sbtw_lineMap_iff]
    have h1v : (0 : ℝ) < 1 - v := by linarith [hv0]
    refine ⟨?_, div_pos (neg_pos.mpr hv0) h1v, by rw [div_lt_one h1v]; linarith [hv0]⟩
    · -- `Z ≠ F`: `Z` is on line `BC` beyond `C`, `F` is on line `AB`, `F ≠ B`.
      intro hZF
      rw [hZF] at hZEF
      -- then `lineMap E F v = F`, so `E, F` on line `BC`.
      have hFBC : F ∈ line[ℝ, B, C] := by
        have h1 : (u • (C -ᵥ B) +ᵥ B) ∈ line[ℝ, B, C] := by
          have hZeq : u • (C -ᵥ B) +ᵥ B = AffineMap.lineMap B C u := by
            rw [AffineMap.lineMap_apply]
          rw [hZeq]
          exact (mem_affineSpan_pair_iff_exists_lineMap_eq).mpr ⟨u, rfl⟩
        rwa [hZF] at h1
      have hFAB : F ∈ line[ℝ, A, B] := hFw.mem_affineSpan
      have hncABC : ¬Collinear ℝ ({A, B, C} : Set P) :=
        affineIndependent_iff_not_collinear_set.mp hai
      have hA_line : A ∈ line[ℝ, B, F] :=
        (collinear_insert_of_mem_affineSpan_pair hFAB).mem_affineSpan_of_mem_of_ne
          (by simp) (by simp) (by simp) hFneB.symm
      have hC_line : C ∈ line[ℝ, B, F] :=
        (collinear_insert_of_mem_affineSpan_pair hFBC).mem_affineSpan_of_mem_of_ne
          (by simp) (by simp) (by simp) hFneB.symm
      have hcol4 : Collinear ℝ ({A, C, B, F} : Set P) :=
        collinear_insert_insert_of_mem_affineSpan_pair hA_line hC_line
      have hcol3 : Collinear ℝ ({A, B, C} : Set P) := hcol4.subset (by
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
        tauto)
      exact hncABC hcol3

/-- An interior point of a triangle is strictly on the same side of any side line as the
opposite vertex. -/
theorem sSameSide_of_mem_interior {A B C D : P} (hai : AffineIndependent ℝ ![A, B, C])
    (hD : D ∈ (⟨_, hai⟩ : Triangle ℝ P).interior) :
    (line[ℝ, B, C]).SSameSide A D := by
  obtain ⟨L, hBLC, hADL⟩ := exists_sbtw_cevian_of_mem_interior hai hD
  have hAnBC : A ∉ line[ℝ, B, C] := by
    have hnc : ¬Collinear ℝ ({A, B, C} : Set P) := affineIndependent_iff_not_collinear_set.mp hai
    exact fun h => hnc (collinear_insert_of_mem_affineSpan_pair h)
  have hDnBC : D ∉ line[ℝ, B, C] := not_mem_line_of_mem_interior hai hD
  refine ⟨⟨L, hBLC.wbtw.mem_affineSpan, L, hBLC.wbtw.mem_affineSpan, ?_⟩, hAnBC, hDnBC⟩
  rw [sbtw_iff_mem_image_Ioo_and_ne] at hADL
  obtain ⟨hs, hne⟩ := hADL
  obtain ⟨t, htIoo, hteq⟩ := hs
  -- `D -ᵥ L = (1 - t) • (A -ᵥ L)` with `1 - t > 0`, so `A` and `D` are on the same ray from `L`.
  have hDL : D -ᵥ L = (1 - t) • (A -ᵥ L) := by
    rw [← hteq, AffineMap.lineMap_apply, vadd_vsub_assoc,
      show A -ᵥ L = -(L -ᵥ A) by rw [neg_vsub_eq_vsub_rev]]
    module
  rw [hDL]
  exact SameRay.sameRay_pos_smul_right _ (sub_pos.mpr htIoo.2)

/-- The bisector condition lifts to oriented angles with the same sign (the alternative
sign choice would force `A, B, C` collinear). -/
theorem oangle_DAB_eq_oangle_CAD [Module.Oriented ℝ V (Fin 2)] {A B C D : P}
    (hai : AffineIndependent ℝ ![A, B, C])
    (hDint : D ∈ (⟨_, hai⟩ : Triangle ℝ P).interior)
    (hbis : ∠ D A B = ∠ C A D) : ∡ D A B = ∡ C A D := by
  have hAB : A ≠ B := hai.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hAC : A ≠ C := hai.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hAD : A ≠ D := by
    rintro rfl
    exact Simplex.point_notMem_interior _ 0 hDint
  have hcase := EuclideanGeometry.oangle_eq_or_eq_neg_of_angle_eq hbis hAD hAB hAC hAD
  rcases hcase with h | h
  · exact h
  · exfalso
    have hadd : ∡ C A B = ∡ C A D + ∡ D A B := (EuclideanGeometry.oangle_add hAC.symm hAD.symm hAB.symm).symm
    rw [h, add_neg_cancel] at hadd
    have hcoll : Collinear ℝ ({C, A, B} : Set P) :=
      (EuclideanGeometry.oangle_eq_zero_or_eq_pi_iff_collinear).mp (Or.inl hadd)
    have hcoll' : Collinear ℝ ({A, B, C} : Set P) := by
      rwa [show ({C, A, B} : Set P) = {A, B, C} by
        ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at hcoll
    exact (affineIndependent_iff_not_collinear_set.mp hai) hcoll'

/-- The condition `∠ADE = ∠BCD` lifts to oriented angles with matching signs, using that
`E` is on the same side of `AD` as `C` and `D` is on the same side of `BC` as `A`. -/
theorem oangle_ADE_eq_oangle_BCD [Module.Oriented ℝ V (Fin 2)] {A B C D E : P}
    (hai : AffineIndependent ℝ ![A, B, C])
    (hDint : D ∈ (⟨_, hai⟩ : Triangle ℝ P).interior)
    (hbis : ∠ D A B = ∠ C A D)
    (hEw : Wbtw ℝ A E C) (hDE : ∠ A D E = ∠ B C D) : ∡ A D E = ∡ B C D := by
  have hEneA := E_ne_A hai hDint hDE
  have hEneC := E_ne_C hai hDint hbis hEw hDE
  have hse : Sbtw ℝ A E C := ⟨hEw, hEneA, hEneC⟩
  have hai_BCA : AffineIndependent ℝ ![B, C, A] := affineIndependent_cycle hai
  have hDint_BCA := mem_interior_cycle hai hai_BCA hDint
  have hsBD : (line[ℝ, C, A]).SSameSide B D := sSameSide_of_mem_interior hai_BCA hDint_BCA
  have hsAD : (line[ℝ, B, C]).SSameSide A D := sSameSide_of_mem_interior hai hDint
  have hsCA : line[ℝ, C, A] = line[ℝ, A, C] := by rw [Set.pair_comm]
  -- sign chain for `∡ADE`.
  have hs1 : (∡ A D E).sign = (∡ A D C).sign := Sbtw.oangle_sign_eq_left D hse
  have hs2 : (∡ A D C).sign = (∡ A B C).sign := by
    rw [hsCA] at hsBD
    exact AffineSubspace.SSameSide.oangle_sign_eq (left_mem_affineSpan_pair ℝ A C)
      (right_mem_affineSpan_pair ℝ A C) hsBD
  have hs3 : (∡ A B C).sign = (∡ B C A).sign := (EuclideanGeometry.oangle_rotate_sign A B C).symm
  -- sign chain for `∡BCD`.
  have ht1 : (∡ B C D).sign = (∡ C D B).sign := (EuclideanGeometry.oangle_rotate_sign B C D).symm
  have ht2 : (∡ C D B).sign = -(∡ B D C).sign := by
    rw [EuclideanGeometry.oangle_rev B D C, Real.Angle.sign_neg]
  have ht3 : (∡ B D C).sign = (∡ B A C).sign :=
    AffineSubspace.SSameSide.oangle_sign_eq (left_mem_affineSpan_pair ℝ B C)
      (right_mem_affineSpan_pair ℝ B C) hsAD
  have ht4 : (∡ B A C).sign = (∡ A C B).sign := (EuclideanGeometry.oangle_rotate_sign B A C).symm
  have ht5 : (∡ A C B).sign = -(∡ B C A).sign := by
    rw [EuclideanGeometry.oangle_rev B C A, Real.Angle.sign_neg]
  have hsign : (∡ A D E).sign = (∡ B C D).sign := by
    rw [hs1, hs2, hs3, ht1, ht2, ht3, ht4, ht5, neg_neg]
  exact EuclideanGeometry.oangle_eq_of_angle_eq_of_sign_eq hDE hsign

/-- The condition `∠FDA = ∠DBC` lifts to oriented angles with matching signs. -/
theorem oangle_FDA_eq_oangle_DBC [Module.Oriented ℝ V (Fin 2)] {A B C D F : P}
    (hai : AffineIndependent ℝ ![A, B, C])
    (hDint : D ∈ (⟨_, hai⟩ : Triangle ℝ P).interior)
    (hbis : ∠ D A B = ∠ C A D)
    (hFw : Wbtw ℝ A F B) (hDF : ∠ F D A = ∠ D B C) : ∡ F D A = ∡ D B C := by
  have hFneA := F_ne_A hai hDint hDF
  have hFneB := F_ne_B hai hDint hbis hFw hDF
  have hsf : Sbtw ℝ A F B := ⟨hFw, hFneA, hFneB⟩
  have hai_BCA : AffineIndependent ℝ ![B, C, A] := affineIndependent_cycle hai
  have hai_CAB : AffineIndependent ℝ ![C, A, B] := affineIndependent_cycle hai_BCA
  have hDint_BCA := mem_interior_cycle hai hai_BCA hDint
  have hDint_CAB := mem_interior_cycle hai_BCA hai_CAB hDint_BCA
  have hsCD : (line[ℝ, A, B]).SSameSide C D := sSameSide_of_mem_interior hai_CAB hDint_CAB
  have hsAD : (line[ℝ, B, C]).SSameSide A D := sSameSide_of_mem_interior hai hDint
  -- sign chain for `∡FDA`.
  have hs1 : (∡ F D A).sign = -(∡ A D F).sign := by
    rw [EuclideanGeometry.oangle_rev A D F, Real.Angle.sign_neg]
  have hs2 : (∡ A D F).sign = (∡ A D B).sign := Sbtw.oangle_sign_eq_left D hsf
  have hs3 : (∡ A D B).sign = (∡ A C B).sign :=
    AffineSubspace.SSameSide.oangle_sign_eq (left_mem_affineSpan_pair ℝ A B)
      (right_mem_affineSpan_pair ℝ A B) hsCD
  have hs4 : (∡ A C B).sign = -(∡ B C A).sign := by
    rw [EuclideanGeometry.oangle_rev B C A, Real.Angle.sign_neg]
  -- sign chain for `∡DBC` (reusing the one from `oangle_ADE_eq_oangle_BCD`).
  have ht1 : (∡ D B C).sign = (∡ B C D).sign := (EuclideanGeometry.oangle_rotate_sign D B C).symm
  have ht2 : (∡ B C D).sign = (∡ C D B).sign := (EuclideanGeometry.oangle_rotate_sign B C D).symm
  have ht3 : (∡ C D B).sign = -(∡ B D C).sign := by
    rw [EuclideanGeometry.oangle_rev B D C, Real.Angle.sign_neg]
  have ht4 : (∡ B D C).sign = (∡ B A C).sign :=
    AffineSubspace.SSameSide.oangle_sign_eq (left_mem_affineSpan_pair ℝ B C)
      (right_mem_affineSpan_pair ℝ B C) hsAD
  have ht5 : (∡ B A C).sign = (∡ A C B).sign := (EuclideanGeometry.oangle_rotate_sign B A C).symm
  have ht6 : (∡ A C B).sign = -(∡ B C A).sign := by
    rw [EuclideanGeometry.oangle_rev B C A, Real.Angle.sign_neg]
  have hsign : (∡ F D A).sign = (∡ D B C).sign := by
    rw [hs1, hs2, hs3, hs4, ht1, ht2, ht3, ht4, ht5, ht6, neg_neg]
  exact EuclideanGeometry.oangle_eq_of_angle_eq_of_sign_eq hDF hsign

/-- The tangent-chord angle theorem in oriented form: twice the oriented angle between the
tangent line at `D` and the chord `DC` equals twice the oriented inscribed angle over that
chord from any other point `B` of the circle. -/
theorem two_zsmul_oangle_tangent_chord [Module.Oriented ℝ V (Fin 2)]
    {s : EuclideanGeometry.Sphere P} {T D B C : P} {as : AffineSubspace ℝ P}
    (hD : D ∈ s) (hB : B ∈ s) (hC : C ∈ s) (hT : s.IsTangentAt D as) (hTas : T ∈ as)
    (hTD : T ≠ D) (hCD : C ≠ D) (hBD : B ≠ D) (hBC : B ≠ C) :
    (2 : ℤ) • ∡ T D C = (2 : ℤ) • ∡ D B C := by
  have hDO : D ≠ s.center := by
    intro hDc
    have h1 : s.radius = 0 := by rw [← EuclideanGeometry.mem_sphere.mp hD, hDc, dist_self]
    have h2 : dist C s.center = s.radius := EuclideanGeometry.mem_sphere.mp hC
    rw [h1, dist_eq_zero] at h2
    exact hCD (h2.trans hDc.symm)
  have horth : Module.Oriented.positiveOrientation.oangle (T -ᵥ D) (D -ᵥ s.center) = (π / 2 : ℝ) ∨
      Module.Oriented.positiveOrientation.oangle (T -ᵥ D) (D -ᵥ s.center) = (-π / 2 : ℝ) := by
    have h := (Module.Oriented.positiveOrientation.eq_zero_or_oangle_eq_iff_inner_eq_zero).mpr
      (hT.inner_left_eq_zero_of_mem hTas)
    rcases h with h0 | h0 | h90 | h90
    · exact absurd (vsub_eq_zero_iff_eq.mp h0) hTD
    · exact absurd (vsub_eq_zero_iff_eq.mp h0) hDO
    · exact Or.inl h90
    · exact Or.inr h90
  have ho1 : (2 : ℤ) • ∡ T D s.center = π := by
    have h1 : ∡ T D s.center =
        Module.Oriented.positiveOrientation.oangle (T -ᵥ D) (D -ᵥ s.center) + π := by
      rw [show ∡ T D s.center =
          Module.Oriented.positiveOrientation.oangle (T -ᵥ D) (s.center -ᵥ D) from rfl,
        show (s.center -ᵥ D) = -(D -ᵥ s.center) by rw [neg_vsub_eq_vsub_rev],
        (Module.Oriented.positiveOrientation).oangle_neg_right (vsub_ne_zero.mpr hTD) (vsub_ne_zero.mpr hDO)]
    rw [h1, smul_add]
    rcases horth with h90 | h90
    · rw [h90, Real.Angle.two_zsmul_coe_div_two π, Real.Angle.two_zsmul_coe_pi, add_zero]
    · rw [h90, Real.Angle.two_zsmul_neg_pi_div_two, Real.Angle.two_zsmul_coe_pi, add_zero]
  have hsplit : ∡ T D C = ∡ T D s.center + ∡ s.center D C :=
    (EuclideanGeometry.oangle_add hTD hDO.symm hCD).symm
  have hcentral : ∡ D s.center C = (2 : ℤ) • ∡ D B C :=
    EuclideanGeometry.Sphere.oangle_center_eq_two_zsmul_oangle hD hB hC hBD hBC
  have hiso : ∡ D s.center C = π - (2 : ℤ) • ∡ s.center C D :=
    EuclideanGeometry.Sphere.oangle_eq_pi_sub_two_zsmul_oangle_center_left hD hC hCD.symm
  have hbase : ∡ s.center C D = ∡ C D s.center :=
    EuclideanGeometry.oangle_eq_oangle_of_dist_eq
      (EuclideanGeometry.dist_center_eq_dist_center_of_mem_sphere' hC hD)
  rw [hsplit, smul_add, ho1, ← hcentral, hiso, hbase,
    show ∡ C D s.center = -∡ s.center D C from EuclideanGeometry.oangle_rev s.center D C,
    smul_neg, sub_neg_eq_add]

/-- The anti-parallel relation: from the cyclicity of `BCEF`, twice the oriented angle
`∡AFE` equals twice `∡BCA` (i.e., `EF` is anti-parallel to `BC` in angle `A`). -/
theorem two_zsmul_oangle_AFE_eq_two_zsmul_oangle_BCA [Module.Oriented ℝ V (Fin 2)]
    {A B C D E F : P}
    (hai : AffineIndependent ℝ ![A, B, C])
    (hDint : D ∈ (⟨_, hai⟩ : Triangle ℝ P).interior)
    (hbis : ∠ D A B = ∠ C A D)
    (hEw : Wbtw ℝ A E C) (hDE : ∠ A D E = ∠ B C D)
    (hFw : Wbtw ℝ A F B) (hDF : ∠ F D A = ∠ D B C) :
    (2 : ℤ) • ∡ A F E = (2 : ℤ) • ∡ B C A := by
  have hEneA := E_ne_A hai hDint hDE
  have hEneC := E_ne_C hai hDint hbis hEw hDE
  have hFneA := F_ne_A hai hDint hDF
  have hFneB := F_ne_B hai hDint hbis hFw hDF
  have hEF : E ≠ F := E_ne_F hai hEw hFw hEneA hFneA
  have hAB : A ≠ B := hai.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hAC : A ≠ C := hai.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hBC : B ≠ C := hai.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  -- `E ≠ B` and `F ≠ C`, since those points lie on different side lines of the triangle.
  have hEB : E ≠ B := by
    intro hEB
    rw [hEB] at hEw
    exact (affineIndependent_iff_not_collinear_set.mp hai) hEw.collinear
  have hFC : F ≠ C := by
    intro hFC
    rw [hFC] at hFw
    have h := hFw.collinear
    rw [show ({A, C, B} : Set P) = {A, B, C} by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at h
    exact (affineIndependent_iff_not_collinear_set.mp hai) h
  -- The circle through `B, C, E, F`.
  have hcyc := concyclic_BCEF hai hDint hbis hEw hDE hFw hDF
  obtain ⟨s, hs⟩ := EuclideanGeometry.cospherical_iff_exists_sphere.mp hcyc.Cospherical
  have hmems : B ∈ s ∧ C ∈ s ∧ E ∈ s ∧ F ∈ s := by
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff] at hs
    exact hs
  obtain ⟨hBs, hCs, hEs, hFs⟩ := hmems
  -- `2•∡AFE = 2•∡BFE` (line replacement on `AB`).
  have r1 : (2 : ℤ) • ∡ A F E = (2 : ℤ) • ∡ B F E := by
    have hc : Collinear ℝ ({A, F, B} : Set P) := by
      have h := collinear_insert_of_mem_affineSpan_pair hFw.mem_affineSpan
      rwa [show ({F, A, B} : Set P) = {A, F, B} by
        ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at h
    exact Collinear.two_zsmul_oangle_eq_left hc hFneA.symm hFneB.symm
  -- `2•∡BFE = 2•∡BCE` (inscribed angle over chord `BE`).
  have r2 : (2 : ℤ) • ∡ B F E = (2 : ℤ) • ∡ B C E :=
    EuclideanGeometry.Sphere.two_zsmul_oangle_eq hBs hFs hCs hEs hFneB hEF.symm hBC.symm hEneC.symm
  -- `2•∡BCE = 2•∡BCA` (line replacement on `CA`).
  have r3 : (2 : ℤ) • ∡ B C E = (2 : ℤ) • ∡ B C A := by
    have hc : Collinear ℝ ({E, C, A} : Set P) := by
      have h := collinear_insert_of_mem_affineSpan_pair hEw.mem_affineSpan
      rwa [show ({E, A, C} : Set P) = {E, C, A} by
        ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at h
    exact Collinear.two_zsmul_oangle_eq_right hc hEneC hAC
  rw [r1, r2, r3]

/-- If `Z` lies on line `BC` strictly beyond `C`, then `Z` is strictly outside any sphere
through `B` and `C`. -/
theorem radius_lt_dist_center_of_sbtw_of_mem_sphere {s : EuclideanGeometry.Sphere P} {Z B C : P}
    (hB : B ∈ s) (hC : C ∈ s) (hBC : B ≠ C) (hZ : Z ∈ line[ℝ, B, C]) (hsbtw : Sbtw ℝ B C Z) :
    s.radius < dist Z s.center := by
  by_contra hle
  push_neg at hle
  have hZC : Z ≠ B := hsbtw.left_ne_right.symm
  have hZBv : Z -ᵥ B ∈ (line[ℝ, B, C]).direction :=
    AffineSubspace.vsub_mem_direction hZ (left_mem_affineSpan_pair ℝ B C)
  rw [direction_affineSpan, vectorSpan_pair] at hZBv
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hZBv
  have ht0 : t ≠ 0 := by
    intro ht0
    rw [ht0, zero_smul] at ht
    exact hZC (vsub_eq_zero_iff_eq.mp ht.symm)
  have hsC : s.secondInter B (C -ᵥ B) = C := by
    have h := (EuclideanGeometry.Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair hB
      (right_mem_affineSpan_pair ℝ B C)).mpr hC
    rcases h with h | h
    · exact absurd h hBC.symm
    · exact h.symm
  have hsi : s.secondInter B (Z -ᵥ B) = C := by
    rw [← ht, EuclideanGeometry.Sphere.secondInter_smul s B (B -ᵥ C) ht0,
      show (B -ᵥ C) = -(C -ᵥ B) by rw [neg_vsub_eq_vsub_rev],
      EuclideanGeometry.Sphere.secondInter_neg s B (C -ᵥ B), hsC]
  have hw := EuclideanGeometry.Sphere.wbtw_secondInter hB hle
  rw [hsi] at hw
  have hCZ : C = Z := (Wbtw.swap_left_iff hw.symm).mp hsbtw.wbtw.symm
  exact hsbtw.ne_right hCZ

/-- The points `D, E, F` are not collinear: `∡EDF = −(∡BCD + ∡DBC)`, which is nonzero
(and not `π`) since `B, D, C` are not collinear. -/
theorem not_collinear_DEF [Module.Oriented ℝ V (Fin 2)] {A B C D E F : P}
    (hai : AffineIndependent ℝ ![A, B, C])
    (hDint : D ∈ (⟨_, hai⟩ : Triangle ℝ P).interior)
    (hbis : ∠ D A B = ∠ C A D)
    (hEw : Wbtw ℝ A E C) (hDE : ∠ A D E = ∠ B C D)
    (hFw : Wbtw ℝ A F B) (hDF : ∠ F D A = ∠ D B C) :
    ¬Collinear ℝ ({D, E, F} : Set P) := by
  have hDA : D ≠ A := by
    rintro rfl
    exact Simplex.point_notMem_interior _ 0 hDint
  have hDB : D ≠ B := by
    rintro rfl
    exact Simplex.point_notMem_interior _ 1 hDint
  have hDC : D ≠ C := by
    rintro rfl
    exact Simplex.point_notMem_interior _ 2 hDint
  have hBC : B ≠ C := hai.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  have hDnBC : D ∉ line[ℝ, B, C] := not_mem_line_of_mem_interior hai hDint
  have hDnAC : D ∉ line[ℝ, A, C] := by
    have hai_BCA : AffineIndependent ℝ ![B, C, A] := affineIndependent_cycle hai
    have h := not_mem_line_of_mem_interior hai_BCA (mem_interior_cycle hai hai_BCA hDint)
    have e : line[ℝ, C, A] = line[ℝ, A, C] := by rw [Set.pair_comm]
    rwa [e] at h
  have hDnAB : D ∉ line[ℝ, A, B] := by
    have hai_BCA : AffineIndependent ℝ ![B, C, A] := affineIndependent_cycle hai
    have hai_CAB : AffineIndependent ℝ ![C, A, B] := affineIndependent_cycle hai_BCA
    exact not_mem_line_of_mem_interior hai_CAB
      (mem_interior_cycle hai_BCA hai_CAB (mem_interior_cycle hai hai_BCA hDint))
  have hED : E ≠ D := by
    intro hED
    subst hED
    exact hDnAC hEw.mem_affineSpan
  have hFD : F ≠ D := by
    intro hFD
    subst hFD
    exact hDnAB hFw.mem_affineSpan
  have hncBCD : ¬Collinear ℝ ({B, C, D} : Set P) :=
    fun h => hDnBC (h.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hBC)
  have hncBDC : ¬Collinear ℝ ({B, D, C} : Set P) := not_collinear_swap23 hncBCD
  -- The oriented angle computation.
  have hbis_o := oangle_DAB_eq_oangle_CAD hai hDint hbis
  have hDE_o := oangle_ADE_eq_oangle_BCD hai hDint hbis hEw hDE
  have hDF_o := oangle_FDA_eq_oangle_DBC hai hDint hbis hFw hDF
  have h1 : ∡ E D F = ∡ E D A + ∡ A D F := (EuclideanGeometry.oangle_add hED hDA.symm hFD).symm
  have h2 : ∡ E D A = -∡ B C D := by
    rw [EuclideanGeometry.oangle_rev A D E, hDE_o]
  have h3 : ∡ A D F = -∡ D B C := by
    rw [EuclideanGeometry.oangle_rev F D A, hDF_o]
  -- `2•(∡BCD + ∡DBC) = 2•∡BDC` from the triangle angle sum.
  have h4 : (2 : ℤ) • (∡ B C D + ∡ D B C) = (2 : ℤ) • ∡ B D C := by
    have hsum : ∡ B D C + ∡ D C B + ∡ C B D = π :=
      EuclideanGeometry.oangle_add_oangle_add_oangle_eq_pi hDB hDC.symm hBC
    have c1 : ∡ B C D = -∡ D C B := EuclideanGeometry.oangle_rev D C B
    have c2 : ∡ D B C = -∡ C B D := EuclideanGeometry.oangle_rev C B D
    rw [c1, c2]
    have h5 : -∡ D C B + -∡ C B D = ∡ B D C - π := by
      have h6 : ∡ D C B + ∡ C B D = π - ∡ B D C := by
        rw [← hsum]
        abel
      rw [show -∡ D C B + -∡ C B D = -(∡ D C B + ∡ C B D) by abel, h6, neg_sub]
    rw [h5, smul_sub, Real.Angle.two_zsmul_coe_pi, sub_zero]
  have h6 : (2 : ℤ) • ∡ E D F = (2 : ℤ) • (-∡ B D C) := by
    have e1 : (2 : ℤ) • ∡ E D F = (2 : ℤ) • (-∡ B C D) + (2 : ℤ) • (-∡ D B C) := by
      rw [h1, h2, h3, smul_add]
    have e2 : (2 : ℤ) • (-∡ B C D) + (2 : ℤ) • (-∡ D B C) =
        -((2 : ℤ) • (∡ B C D + ∡ D B C)) := by
      rw [← smul_add, ← smul_neg, neg_add]
    rw [e1, e2, h4, smul_neg]
  intro hcol
  have hcol' : Collinear ℝ ({E, D, F} : Set P) := by
    rwa [show ({D, E, F} : Set P) = {E, D, F} by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at hcol
  have h0 : ∡ E D F = 0 ∨ ∡ E D F = π :=
    (EuclideanGeometry.oangle_eq_zero_or_eq_pi_iff_collinear).mpr hcol'
  have h0' : (2 : ℤ) • ∡ E D F = 0 := by
    rcases h0 with h0 | h0
    · rw [h0, smul_zero]
    · rw [h0, Real.Angle.two_zsmul_coe_pi]
  rw [h6, smul_neg, neg_eq_zero] at h0'
  have h0'' : ∡ B D C = 0 ∨ ∡ B D C = π := (Real.Angle.two_zsmul_eq_zero_iff).mp h0'
  exact hncBDC ((EuclideanGeometry.oangle_eq_zero_or_eq_pi_iff_collinear).mp h0'')

set_option maxHeartbeats 800000

/-- The tangent chase: any point `T` (different from `D`) of the tangent line of the
circumcircle of `BCD` at `D` satisfies `2 • ∡ T D E = 2 • ∡ D F E`. This is the heart of
the proof that the tangent lines of `(BCD)` and `(DEF)` at `D` coincide. -/
theorem two_zsmul_oangle_tangent_chase [Module.Oriented ℝ V (Fin 2)] {A B C D E F T : P}
    (hai : AffineIndependent ℝ ![A, B, C])
    (hDint : D ∈ (⟨_, hai⟩ : Triangle ℝ P).interior)
    (hbis : ∠ D A B = ∠ C A D)
    (hEw : Wbtw ℝ A E C) (hDE : ∠ A D E = ∠ B C D)
    (hFw : Wbtw ℝ A F B) (hDF : ∠ F D A = ∠ D B C)
    (htBCD : AffineIndependent ℝ ![B, C, D])
    (hT : T ∈ (⟨_, htBCD⟩ : Triangle ℝ P).circumsphere.orthRadius D)
    (hTD : T ≠ D) :
    (2 : ℤ) • ∡ T D E = (2 : ℤ) • ∡ D F E := by
  have hncBCD : ¬Collinear ℝ ({B, C, D} : Set P) := affineIndependent_iff_not_collinear_set.mp htBCD
  -- Basic facts.
  have hAB : A ≠ B := hai.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hAC : A ≠ C := hai.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hBC : B ≠ C := hai.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  have hDA : D ≠ A := by
    rintro rfl
    exact Simplex.point_notMem_interior _ 0 hDint
  have hDB : D ≠ B := by
    rintro rfl
    exact Simplex.point_notMem_interior _ 1 hDint
  have hDC : D ≠ C := by
    rintro rfl
    exact Simplex.point_notMem_interior _ 2 hDint
  have hBD : B ≠ D := hDB.symm
  have hCD : C ≠ D := hDC.symm
  have hEneA := E_ne_A hai hDint hDE
  have hEneC := E_ne_C hai hDint hbis hEw hDE
  have hFneA := F_ne_A hai hDint hDF
  have hFneB := F_ne_B hai hDint hbis hFw hDF
  have hEF : E ≠ F := E_ne_F hai hEw hFw hEneA hFneA
  have hsf : Sbtw ℝ A F B := ⟨hFw, hFneA, hFneB⟩
  have hDnAC : D ∉ line[ℝ, A, C] := by
    have hai_BCA : AffineIndependent ℝ ![B, C, A] := affineIndependent_cycle hai
    have h := not_mem_line_of_mem_interior hai_BCA (mem_interior_cycle hai hai_BCA hDint)
    have e : line[ℝ, C, A] = line[ℝ, A, C] := by rw [Set.pair_comm]
    rwa [e] at h
  have hDnAB : D ∉ line[ℝ, A, B] := by
    have hai_BCA : AffineIndependent ℝ ![B, C, A] := affineIndependent_cycle hai
    have hai_CAB : AffineIndependent ℝ ![C, A, B] := affineIndependent_cycle hai_BCA
    exact not_mem_line_of_mem_interior hai_CAB
      (mem_interior_cycle hai_BCA hai_CAB (mem_interior_cycle hai hai_BCA hDint))
  have hED : E ≠ D := by
    intro hED
    rw [hED] at hEw
    exact hDnAC hEw.mem_affineSpan
  have hFD : F ≠ D := by
    intro hFD
    rw [hFD] at hFw
    exact hDnAB hFw.mem_affineSpan
  -- The circle through `B, C, D` and its tangent line at `D`.
  set tBCD : Triangle ℝ P := ⟨_, affineIndependent_iff_not_collinear_set.mpr hncBCD⟩ with htBCD
  set sBCD : EuclideanGeometry.Sphere P := tBCD.circumsphere with hsBCD
  have hDs : D ∈ sBCD := Simplex.mem_circumsphere tBCD 2
  have hBs : B ∈ sBCD := Simplex.mem_circumsphere tBCD 0
  have hCs : C ∈ sBCD := Simplex.mem_circumsphere tBCD 1
  have hTan : sBCD.IsTangentAt D (sBCD.orthRadius D) :=
    (EuclideanGeometry.Sphere.isTangentAt_orthRadius_iff_mem).mpr hDs
  -- The oriented-angle inputs.
  have hbis_o : ∡ D A B = ∡ C A D := oangle_DAB_eq_oangle_CAD hai hDint hbis
  have hDE_o : ∡ A D E = ∡ B C D := oangle_ADE_eq_oangle_BCD hai hDint hbis hEw hDE
  have hDF_o : ∡ F D A = ∡ D B C := oangle_FDA_eq_oangle_DBC hai hDint hbis hFw hDF
  -- Tangent-chord on `(BCD)`.
  have htc : (2 : ℤ) • ∡ T D C = (2 : ℤ) • ∡ D B C :=
    two_zsmul_oangle_tangent_chord hDs hBs hCs hTan hT hTD hCD hBD hBC
  -- Left-hand side expansion.
  have k1 : (2 : ℤ) • ∡ T D E =
      (2 : ℤ) • ∡ D B C + (2 : ℤ) • (-∡ A D C) + (2 : ℤ) • ∡ B C D := by
    have hsplit : ∡ T D E = ∡ T D C + ∡ C D E := (EuclideanGeometry.oangle_add hTD hCD hED).symm
    have hCDE : ∡ C D E = ∡ C D A + ∡ A D E := (EuclideanGeometry.oangle_add hCD hDA.symm hED).symm
    have hCDA : ∡ C D A = -∡ A D C := EuclideanGeometry.oangle_rev A D C
    rw [hsplit, hCDE, hCDA, hDE_o, smul_add, smul_add, htc, add_assoc]
  -- Right-hand side expansion.
  have k2 : (2 : ℤ) • ∡ D F E =
      (2 : ℤ) • ∡ D A B + (2 : ℤ) • ∡ D B C + (2 : ℤ) • ∡ B C A := by
    have hsplit : ∡ D F E = ∡ D F A + ∡ A F E := (EuclideanGeometry.oangle_add hFD.symm hFneA.symm hEF).symm
    have hsumADF : ∡ A D F + ∡ D F A + ∡ F A D = π :=
      EuclideanGeometry.oangle_add_oangle_add_oangle_eq_pi hDA hFD hFneA.symm
    have hDFA : ∡ D F A = π + ∡ D A B + ∡ D B C := by
      have c1 : ∡ F A D = ∡ B A D := Sbtw.oangle_eq_left hsf
      have c2 : ∡ A D F = -∡ D B C := by
        rw [EuclideanGeometry.oangle_rev F D A, hDF_o]
      have c3 : ∡ B A D = -∡ D A B := EuclideanGeometry.oangle_rev D A B
      rw [c1] at hsumADF
      rw [c2] at hsumADF
      rw [c3] at hsumADF
      rw [← hsumADF]
      abel
    have hAFE : (2 : ℤ) • ∡ A F E = (2 : ℤ) • ∡ B C A :=
      two_zsmul_oangle_AFE_eq_two_zsmul_oangle_BCA hai hDint hbis hEw hDE hFw hDF
    rw [hsplit, smul_add, hDFA, smul_add, smul_add, Real.Angle.two_zsmul_coe_pi, zero_add, hAFE]
  -- The angle-sum relation for `−∡ADC`.
  have hneg : (2 : ℤ) • (-∡ A D C) = (2 : ℤ) • ∡ D C A + (2 : ℤ) • ∡ C A D := by
    have hsumADC : ∡ A D C + ∡ D C A + ∡ C A D = π :=
      EuclideanGeometry.oangle_add_oangle_add_oangle_eq_pi hDA hCD hAC
    have h7 : -∡ A D C = ∡ D C A + ∡ C A D - π := by
      rw [← hsumADC]
      abel
    rw [h7, smul_sub, smul_add, Real.Angle.two_zsmul_coe_pi, sub_zero]
  -- The `∡BCD + ∡DCA = ∡BCA` relation.
  have hBCA : (2 : ℤ) • ∡ B C D + (2 : ℤ) • ∡ D C A = (2 : ℤ) • ∡ B C A := by
    rw [← smul_add, EuclideanGeometry.oangle_add hBC hDC hAC]
  -- Final assembly.
  rw [k1, k2, hneg, hbis_o]
  rw [show (2 : ℤ) • ∡ D B C + ((2 : ℤ) • ∡ D C A + (2 : ℤ) • ∡ C A D) + (2 : ℤ) • ∡ B C D =
      (2 : ℤ) • ∡ D B C + ((2 : ℤ) • ∡ B C D + (2 : ℤ) • ∡ D C A) + (2 : ℤ) • ∡ C A D by abel]
  rw [hBCA]
  abel

/-- Converse of the tangent-chord relation: if `2 • ∡ X D E = 2 • ∡ D F E`, then `X` lies on
the tangent line of the circle `(DEF)` at `D`. -/
theorem mem_orthRadius_of_two_zsmul_oangle_eq [Module.Oriented ℝ V (Fin 2)]
    {s : EuclideanGeometry.Sphere P} {X D E F : P}
    (hD : D ∈ s) (hE : E ∈ s) (hF : F ∈ s)
    (hED : E ≠ D) (hFD : F ≠ D) (hXD : X ≠ D) (hEF : E ≠ F)
    (h : (2 : ℤ) • ∡ X D E = (2 : ℤ) • ∡ D F E) :
    X ∈ s.orthRadius D := by
  letI : FiniteDimensional ℝ V :=
    FiniteDimensional.of_finrank_eq_succ (n := 1) (Fact.out : finrank ℝ V = 2)
  have hTan : s.IsTangentAt D (s.orthRadius D) :=
    (EuclideanGeometry.Sphere.isTangentAt_orthRadius_iff_mem).mpr hD
  -- A point of the tangent line different from `D`.
  have hDO : D ≠ s.center := by
    intro hDc
    have h1 : s.radius = 0 := by rw [← EuclideanGeometry.mem_sphere.mp hD, hDc, dist_self]
    have h2 : dist E s.center = s.radius := EuclideanGeometry.mem_sphere.mp hE
    rw [h1, dist_eq_zero] at h2
    exact hED (h2.trans hDc.symm)
  have hdir_ne : (s.orthRadius D).direction ≠ ⊥ := by
    have hfin := EuclideanGeometry.Sphere.finrank_orthRadius hDO
    have h2 : finrank ℝ V = 2 := Fact.out
    rw [h2] at hfin
    intro hbot
    rw [hbot] at hfin
    simp at hfin
  obtain ⟨w, hw_mem, hw_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hdir_ne
  set T₀ : P := w +ᵥ D with hT₀def
  have hT₀ne : T₀ ≠ D := by
    intro h
    rw [hT₀def] at h
    have h3 : (w +ᵥ D) -ᵥ D = w := vadd_vsub w D
    rw [h, vsub_self] at h3
    exact hw_ne h3.symm
  have hT₀mem : T₀ ∈ s.orthRadius D :=
    AffineSubspace.vadd_mem_of_mem_direction hw_mem (EuclideanGeometry.Sphere.self_mem_orthRadius s D)
  have htc : (2 : ℤ) • ∡ T₀ D E = (2 : ℤ) • ∡ D F E :=
    two_zsmul_oangle_tangent_chord hD hF hE hTan hT₀mem hT₀ne hED hFD hEF.symm
  -- The angles `∡XDE` and `∡T₀DE` are equal mod `π`, so `X, D, T₀` are collinear.
  have hT0 : (2 : ℤ) • ∡ T₀ D E = (2 : ℤ) • ∡ X D E := htc.trans h.symm
  have hcase : ∡ T₀ D E = ∡ X D E ∨ ∡ T₀ D E = ∡ X D E + π := Real.Angle.two_zsmul_eq_iff.mp hT0
  have hcoll : Collinear ℝ ({X, D, T₀} : Set P) := by
    have hsub : ∡ X D T₀ = 0 ∨ ∡ X D T₀ = π := by
      rcases hcase with hc | hc
      · have h1 : ∡ X D E - ∡ T₀ D E = 0 := by rw [hc, sub_self]
        rw [EuclideanGeometry.oangle_sub_right hXD hT₀ne hED] at h1
        exact Or.inl h1
      · have h1 : ∡ X D E - ∡ T₀ D E = π := by
          rw [hc, sub_add_eq_sub_sub, sub_self, zero_sub, Real.Angle.neg_coe_pi]
        rw [EuclideanGeometry.oangle_sub_right hXD hT₀ne hED] at h1
        exact Or.inr h1
    exact (EuclideanGeometry.oangle_eq_zero_or_eq_pi_iff_collinear).mp hsub
  have hXline : X ∈ line[ℝ, D, T₀] :=
    hcoll.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hT₀ne.symm
  -- `line[D, T₀] = s.orthRadius D` since both are 1-dimensional and share two points.
  have hle : line[ℝ, D, T₀] ≤ s.orthRadius D := by
    rw [affineSpan_le, Set.insert_subset_iff]
    exact ⟨EuclideanGeometry.Sphere.self_mem_orthRadius s D, Set.singleton_subset_iff.mpr hT₀mem⟩
  have hdir_eq : (line[ℝ, D, T₀]).direction = (s.orthRadius D).direction := by
    have hfin1 : finrank ℝ (s.orthRadius D).direction = 1 := by
      have h := EuclideanGeometry.Sphere.finrank_orthRadius hDO
      have h2 : finrank ℝ V = 2 := Fact.out
      rw [h2] at h
      linarith [h]
    have hfin2 : finrank ℝ (line[ℝ, D, T₀]).direction = 1 := by
      rw [direction_affineSpan, vectorSpan_pair, finrank_span_singleton
        (vsub_ne_zero.mpr hT₀ne.symm)]
    have hle_dir : (line[ℝ, D, T₀]).direction ≤ (s.orthRadius D).direction :=
      AffineSubspace.direction_le hle
    exact Submodule.eq_of_le_of_finrank_eq hle_dir (by rw [hfin2, hfin1])
  have hEq : line[ℝ, D, T₀] = s.orthRadius D :=
    (AffineSubspace.eq_iff_direction_eq_of_mem (left_mem_affineSpan_pair ℝ D T₀)
      (EuclideanGeometry.Sphere.self_mem_orthRadius s D)).mpr hdir_eq
  rwa [hEq] at hXline

/-- The power-difference of two spheres through a common point `D` is an affine-linear
function of the point; in particular, equal powers at `Z` force `Z` onto the radical
hyperplane through `D` perpendicular to the line of centers. -/
theorem inner_eq_zero_of_power_eq_power {s₁ s₂ : EuclideanGeometry.Sphere P} {Z D : P}
    (hD1 : D ∈ s₁) (hD2 : D ∈ s₂) (h : s₁.power Z = s₂.power Z) :
    ⟪Z -ᵥ D, s₂.center -ᵥ s₁.center⟫ = 0 := by
  have hr1 : s₁.radius = dist D s₁.center := (EuclideanGeometry.mem_sphere.mp hD1).symm
  have hr2 : s₂.radius = dist D s₂.center := (EuclideanGeometry.mem_sphere.mp hD2).symm
  rw [EuclideanGeometry.Sphere.power, EuclideanGeometry.Sphere.power, hr1, hr2] at h
  have e : ∀ O : P, dist Z O ^ 2 - dist D O ^ 2 = dist Z D ^ 2 + 2 * ⟪Z -ᵥ D, D -ᵥ O⟫ := by
    intro O
    rw [dist_eq_norm_vsub, dist_eq_norm_vsub, dist_eq_norm_vsub,
      show Z -ᵥ O = (Z -ᵥ D) + (D -ᵥ O) by rw [vsub_add_vsub_cancel], norm_add_sq_real]
    ring
  have h2 : dist Z s₁.center ^ 2 - dist D s₁.center ^ 2 =
      dist Z s₂.center ^ 2 - dist D s₂.center ^ 2 := by linarith [h]
  rw [e, e] at h2
  have hinner : ⟪Z -ᵥ D, D -ᵥ s₁.center⟫ = ⟪Z -ᵥ D, D -ᵥ s₂.center⟫ := by linarith [h2]
  have h3 : s₂.center -ᵥ s₁.center = (D -ᵥ s₁.center) - (D -ᵥ s₂.center) :=
    (vsub_sub_vsub_cancel_left s₂.center s₁.center D).symm
  rw [h3, inner_sub_right, hinner, sub_self]

/-- The five base angles of the configuration: their sum and their values. This packages
`2α + β + γ + φ + ε = π` (with `α = ∠CAD`, `β = ∠BCD`, `γ = ∠DBC`, `φ = ∠DCA`, `ε = ∠DBA`)
together with positivity and the derived values `∠DEC = α + β` and `∠AFD = π − ∠DAB − γ`. -/
theorem config_angles {A B C D E F : P}
    (hai : AffineIndependent ℝ ![A, B, C])
    (hDint : D ∈ (⟨_, hai⟩ : Triangle ℝ P).interior)
    (hbis : ∠ D A B = ∠ C A D)
    (hEw : Wbtw ℝ A E C) (hDE : ∠ A D E = ∠ B C D)
    (hFw : Wbtw ℝ A F B) (hDF : ∠ F D A = ∠ D B C) :
    2 * ∠ C A D + ∠ B C D + ∠ D B C + ∠ D C A + ∠ D B A = π ∧
    0 < ∠ C A D ∧ 0 < ∠ B C D ∧ 0 < ∠ D B C ∧ 0 < ∠ D C A ∧ 0 < ∠ D B A ∧
    ∠ D E C = ∠ C A D + ∠ B C D ∧ ∠ A F D = π - (∠ D A B + ∠ D B C) := by
  have hAB : A ≠ B := hai.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hAC : A ≠ C := hai.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hBC : B ≠ C := hai.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  have hBA : B ≠ A := hAB.symm
  have hCA : C ≠ A := hAC.symm
  have hCB : C ≠ B := hBC.symm
  have hDA : D ≠ A := by
    rintro rfl
    exact Simplex.point_notMem_interior _ 0 hDint
  have hDB : D ≠ B := by
    rintro rfl
    exact Simplex.point_notMem_interior _ 1 hDint
  have hDC : D ≠ C := by
    rintro rfl
    exact Simplex.point_notMem_interior _ 2 hDint
  have hAD : A ≠ D := hDA.symm
  have hBD : B ≠ D := hDB.symm
  have hCD : C ≠ D := hDC.symm
  have hai_BCA : AffineIndependent ℝ ![B, C, A] := affineIndependent_cycle hai
  have hai_CAB : AffineIndependent ℝ ![C, A, B] := affineIndependent_cycle hai_BCA
  have hDint_BCA := mem_interior_cycle hai hai_BCA hDint
  have hDint_CAB := mem_interior_cycle hai_BCA hai_CAB hDint_BCA
  have hDnBC : D ∉ line[ℝ, B, C] := not_mem_line_of_mem_interior hai hDint
  have hDnCA : D ∉ line[ℝ, C, A] := not_mem_line_of_mem_interior hai_BCA hDint_BCA
  have hDnAB : D ∉ line[ℝ, A, B] := not_mem_line_of_mem_interior hai_CAB hDint_CAB
  have hDnAC : D ∉ line[ℝ, A, C] := by
    have e : line[ℝ, C, A] = line[ℝ, A, C] := by rw [Set.pair_comm]
    rwa [e] at hDnCA
  have hncABC : ¬Collinear ℝ ({A, B, C} : Set P) := affineIndependent_iff_not_collinear_set.mp hai
  have hncBCD : ¬Collinear ℝ ({B, C, D} : Set P) :=
    fun h => hDnBC (h.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hBC)
  have hncDBC : ¬Collinear ℝ ({D, B, C} : Set P) := not_collinear_swap (not_collinear_swap23 hncBCD)
  have hncCDA : ¬Collinear ℝ ({C, D, A} : Set P) :=
    not_collinear_of_not_mem_line (right_mem_affineSpan_pair ℝ C A) hCA hDnCA
  have hncCAD : ¬Collinear ℝ ({C, A, D} : Set P) := not_collinear_swap23 hncCDA
  have hncDCA : ¬Collinear ℝ ({D, C, A} : Set P) := not_collinear_swap hncCDA
  have hDnBA : D ∉ line[ℝ, B, A] := by
    have e : line[ℝ, A, B] = line[ℝ, B, A] := by rw [Set.pair_comm]
    rwa [e] at hDnAB
  have hncBDA : ¬Collinear ℝ ({B, D, A} : Set P) :=
    not_collinear_of_not_mem_line (right_mem_affineSpan_pair ℝ B A) hBA hDnBA
  have hncDBA : ¬Collinear ℝ ({D, B, A} : Set P) := not_collinear_swap hncBDA
  have hBCDne : ∠ B C D ≠ 0 := EuclideanGeometry.angle_ne_zero_of_not_collinear hncBCD
  have hDBCne : ∠ D B C ≠ 0 := EuclideanGeometry.angle_ne_zero_of_not_collinear hncDBC
  have hEneA : E ≠ A := by
    intro hEA
    rw [hEA, EuclideanGeometry.angle_self_of_ne hAD] at hDE
    exact hBCDne hDE.symm
  have hFneA : F ≠ A := by
    intro hFA
    rw [hFA, EuclideanGeometry.angle_self_of_ne hAD] at hDF
    exact hDBCne hDF.symm
  have hED : E ≠ D := by
    intro hED
    rw [hED] at hEw
    exact hDnAC hEw.mem_affineSpan
  have hFD : F ≠ D := by
    intro hFD
    rw [hFD] at hFw
    exact hDnAB hFw.mem_affineSpan
  -- The cevian angle splits.
  have hcevA : ∠ B A D + ∠ D A C = ∠ B A C := angle_add_of_mem_interior hai hDint hAB hAC hAD
  have hcevB : ∠ C B D + ∠ D B A = ∠ C B A := angle_add_of_mem_interior hai_BCA hDint_BCA hBC hBA hBD
  have hcevC : ∠ A C D + ∠ D C B = ∠ A C B := angle_add_of_mem_interior hai_CAB hDint_CAB hCA hCB hCD
  -- Triangle angle sums.
  have hsumACD : ∠ A C D + ∠ C D A + ∠ D A C = π :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi D hCA
  have hsumDCE : ∠ D C E + ∠ C E D + ∠ E D C = π :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi E hCD
  have hsumDAF : ∠ D A F + ∠ A F D + ∠ F D A = π :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi F hAD
  have hsumABC : ∠ B C A + ∠ C A B + ∠ A B C = π :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi A hCB
  have hADEsum : ∠ A D E + ∠ E D C = ∠ A D C :=
    EuclideanGeometry.angle_add_of_ne_of_ne hDA hDC hEw
  -- The total angle sum in terms of the five base angles.
  have hsum : 2 * ∠ C A D + ∠ B C D + ∠ D B C + ∠ D C A + ∠ D B A = π := by
    have c1 : ∠ B C A = ∠ A C B := EuclideanGeometry.angle_comm B C A
    have c2 : ∠ C A B = ∠ B A C := EuclideanGeometry.angle_comm C A B
    have c3 : ∠ C B D = ∠ D B C := EuclideanGeometry.angle_comm C B D
    have c4 : ∠ D C B = ∠ B C D := EuclideanGeometry.angle_comm D C B
    have c5 : ∠ A C D = ∠ D C A := EuclideanGeometry.angle_comm A C D
    have c6 : ∠ B A D = ∠ D A B := EuclideanGeometry.angle_comm B A D
    have c7 : ∠ D A C = ∠ C A D := EuclideanGeometry.angle_comm D A C
    have c8 : ∠ C B A = ∠ A B C := EuclideanGeometry.angle_comm C B A
    linarith [hsumABC, hcevA, hcevB, hcevC, c1, c2, c3, c4, c5, c6, c7, c8, hbis]
  -- Angle values.
  have hvADC : ∠ C D A = π - (∠ C A D + ∠ D C A) := by
    have c1 : ∠ A C D = ∠ D C A := EuclideanGeometry.angle_comm A C D
    have c2 : ∠ D A C = ∠ C A D := EuclideanGeometry.angle_comm D A C
    linarith [hsumACD, c1, c2]
  have hvEDC : ∠ E D C = ∠ C D A - ∠ B C D := by
    have c1 : ∠ A D C = ∠ C D A := EuclideanGeometry.angle_comm A D C
    linarith [hADEsum, c1, hDE]
  -- `E ≠ C`: otherwise `∠ADC = ∠BCD`, contradicting the angle sum.
  have hEneC : E ≠ C := by
    intro hEC
    rw [hEC] at hDE
    have c1 : ∠ A D C = ∠ C D A := EuclideanGeometry.angle_comm A D C
    rw [c1, hvADC] at hDE
    have hncBAD : ¬Collinear ℝ ({B, A, D} : Set P) := not_collinear_swap23 hncBDA
    have c2 : ∠ D C B = ∠ B C D := EuclideanGeometry.angle_comm D C B
    have c3 : ∠ B C A = ∠ A C B := EuclideanGeometry.angle_comm B C A
    have c4 : ∠ C A B = ∠ B A C := EuclideanGeometry.angle_comm C A B
    have c5 : ∠ D A C = ∠ C A D := EuclideanGeometry.angle_comm D A C
    have c6 : ∠ A C D = ∠ D C A := EuclideanGeometry.angle_comm A C D
    have hp1 : 0 < ∠ B A D := EuclideanGeometry.angle_pos_of_not_collinear hncBAD
    have hp2 : 0 < ∠ A B C := EuclideanGeometry.angle_pos_of_not_collinear hncABC
    linarith [hDE, hcevA, hcevC, c2, c3, c4, c5, c6, hsumABC, hp1, hp2]
  -- Ray equalities and the remaining angle values.
  have hDCE : ∠ D C E = ∠ D C A := hEw.symm.angle_eq_right D hEneC
  have hFAD : ∠ F A D = ∠ B A D := hFw.angle_eq_left D hFneA
  have hAEC : ∠ A E C = π := EuclideanGeometry.angle_eq_pi_iff_sbtw.mpr ⟨hEw, hEneA, hEneC⟩
  have hDEADEC : ∠ D E A + ∠ D E C = π :=
    EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi D hAEC
  have hvDEC : ∠ D E C = ∠ C A D + ∠ B C D := by
    have c1 : ∠ C E D = ∠ D E C := EuclideanGeometry.angle_comm C E D
    linarith [hsumDCE, c1, hDCE, hvEDC, hvADC]
  have hvAFD : ∠ A F D = π - (∠ D A B + ∠ D B C) := by
    have c1 : ∠ D A F = ∠ F A D := EuclideanGeometry.angle_comm D A F
    have c2 : ∠ B A D = ∠ D A B := EuclideanGeometry.angle_comm B A D
    linarith [hsumDAF, c1, c2, hFAD, hDF]
  -- Positivity of the five base angles.
  have hpα : 0 < ∠ C A D := EuclideanGeometry.angle_pos_of_not_collinear hncCAD
  have hpβ : 0 < ∠ B C D := EuclideanGeometry.angle_pos_of_not_collinear hncBCD
  have hpγ : 0 < ∠ D B C := EuclideanGeometry.angle_pos_of_not_collinear hncDBC
  have hpφ : 0 < ∠ D C A := EuclideanGeometry.angle_pos_of_not_collinear hncDCA
  have hpε : 0 < ∠ D B A := EuclideanGeometry.angle_pos_of_not_collinear hncDBA
  exact ⟨hsum, hpα, hpβ, hpγ, hpφ, hpε, hvDEC, hvAFD⟩

/-- The circumcircles of `BCD` and `DEF` are distinct: otherwise `E` and `F` would both lie
on the circle through `B, C, D`, and the inscribed-angle conditions would force
`∠CAD = 0`, contradicting the interiority of `D`. -/
theorem sphere_BCD_ne_sphere_DEF [Module.Oriented ℝ V (Fin 2)] {A B C D E F : P}
    (hai : AffineIndependent ℝ ![A, B, C])
    (hDint : D ∈ (⟨_, hai⟩ : Triangle ℝ P).interior)
    (hbis : ∠ D A B = ∠ C A D)
    (hEw : Wbtw ℝ A E C) (hDE : ∠ A D E = ∠ B C D)
    (hFw : Wbtw ℝ A F B) (hDF : ∠ F D A = ∠ D B C)
    (htBCD : AffineIndependent ℝ ![B, C, D]) (htDEF : AffineIndependent ℝ ![D, E, F]) :
    (⟨_, htBCD⟩ : Triangle ℝ P).circumsphere ≠ (⟨_, htDEF⟩ : Triangle ℝ P).circumsphere := by
  intro hseq
  obtain ⟨hsum, hpα, hpβ, hpγ, hpφ, hpε, hvDEC, hvAFD⟩ :=
    config_angles hai hDint hbis hEw hDE hFw hDF
  have hEneA := E_ne_A hai hDint hDE
  have hEneC := E_ne_C hai hDint hbis hEw hDE
  have hFneA := F_ne_A hai hDint hDF
  have hFneB := F_ne_B hai hDint hbis hFw hDF
  have hEF : E ≠ F := E_ne_F hai hEw hFw hEneA hFneA
  have hFC : F ≠ C := by
    intro hFC
    rw [hFC] at hFw
    have h := hFw.collinear
    rw [show ({A, C, B} : Set P) = {A, B, C} by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at h
    exact (affineIndependent_iff_not_collinear_set.mp hai) h
  have hBC : B ≠ C := hai.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  have hBD : B ≠ D := by
    rintro rfl
    exact Simplex.point_notMem_interior _ 1 hDint
  have hCD : C ≠ D := by
    rintro rfl
    exact Simplex.point_notMem_interior _ 2 hDint
  have hED : E ≠ D := by
    have hDnAC : D ∉ line[ℝ, A, C] := by
      have hai_BCA : AffineIndependent ℝ ![B, C, A] := affineIndependent_cycle hai
      have h := not_mem_line_of_mem_interior hai_BCA (mem_interior_cycle hai hai_BCA hDint)
      have e : line[ℝ, C, A] = line[ℝ, A, C] := by rw [Set.pair_comm]
      rwa [e] at h
    intro hED
    rw [hED] at hEw
    exact hDnAC hEw.mem_affineSpan
  have hFD : F ≠ D := by
    have hai_BCA : AffineIndependent ℝ ![B, C, A] := affineIndependent_cycle hai
    have hai_CAB : AffineIndependent ℝ ![C, A, B] := affineIndependent_cycle hai_BCA
    have hDnAB := not_mem_line_of_mem_interior hai_CAB
      (mem_interior_cycle hai_BCA hai_CAB (mem_interior_cycle hai hai_BCA hDint))
    intro hFD
    rw [hFD] at hFw
    exact hDnAB hFw.mem_affineSpan
  set sBCD : EuclideanGeometry.Sphere P := (⟨_, htBCD⟩ : Triangle ℝ P).circumsphere with hsBCD
  set sDEF : EuclideanGeometry.Sphere P := (⟨_, htDEF⟩ : Triangle ℝ P).circumsphere with hsDEF
  have hCs : C ∈ sBCD := Simplex.mem_circumsphere _ 1
  have hBs : B ∈ sBCD := Simplex.mem_circumsphere _ 0
  have hDs : D ∈ sBCD := Simplex.mem_circumsphere _ 2
  have hDs2 : D ∈ sDEF := Simplex.mem_circumsphere _ 0
  have hEs2 : E ∈ sDEF := Simplex.mem_circumsphere _ 1
  have hFs2 : F ∈ sDEF := Simplex.mem_circumsphere _ 2
  have hEs : E ∈ sBCD := hseq ▸ hEs2
  have hFs : F ∈ sBCD := hseq ▸ hFs2
  -- Inscribed-angle conditions for `E` and `F` on the circle `(BCD)`.
  have hinE : (2 : ℤ) • ∡ C B D = (2 : ℤ) • ∡ C E D :=
    EuclideanGeometry.Sphere.two_zsmul_oangle_eq hCs hBs hEs hDs hBC hBD hEneC hED
  have hinF : (2 : ℤ) • ∡ B C D = (2 : ℤ) • ∡ B F D :=
    EuclideanGeometry.Sphere.two_zsmul_oangle_eq hBs hCs hFs hDs hBC.symm hCD hFneB hFD
  -- Convert to unoriented relations via the cosine.
  have hcosE : Real.cos (∠ C B D) = Real.cos (∠ C E D) ∨ Real.cos (∠ C B D) = -Real.cos (∠ C E D) := by
    have h1 := EuclideanGeometry.cos_oangle_eq_cos_angle hBC.symm hBD.symm
    have h2 := EuclideanGeometry.cos_oangle_eq_cos_angle hEneC.symm hED.symm
    rcases Real.Angle.two_zsmul_eq_iff.mp hinE with hcase | hcase
    · exact Or.inl (by rw [← h1, ← h2, hcase])
    · exact Or.inr (by rw [← h1, ← h2, hcase, Real.Angle.cos_add_pi])
  have hcosF : Real.cos (∠ B C D) = Real.cos (∠ B F D) ∨ Real.cos (∠ B C D) = -Real.cos (∠ B F D) := by
    have h1 := EuclideanGeometry.cos_oangle_eq_cos_angle hBC hCD.symm
    have h2 := EuclideanGeometry.cos_oangle_eq_cos_angle hFneB.symm hFD.symm
    rcases Real.Angle.two_zsmul_eq_iff.mp hinF with hcase | hcase
    · exact Or.inl (by rw [← h1, ← h2, hcase])
    · exact Or.inr (by rw [← h1, ← h2, hcase, Real.Angle.cos_add_pi])
  -- The angle relations in unoriented form.
  have hE1_or : ∠ C B D = ∠ C E D ∨ ∠ C B D = π - ∠ C E D := by
    have hnonneg1 : 0 ≤ ∠ C B D := EuclideanGeometry.angle_nonneg C B D
    have hnonneg2 : 0 ≤ ∠ C E D := EuclideanGeometry.angle_nonneg C E D
    have hle1 : ∠ C B D ≤ π := EuclideanGeometry.angle_le_pi C B D
    have hle2 : ∠ C E D ≤ π := EuclideanGeometry.angle_le_pi C E D
    rcases hcosE with hcos | hcos
    · exact Or.inl ((Real.injOn_cos.eq_iff ⟨hnonneg1, hle1⟩ ⟨hnonneg2, hle2⟩).mp hcos)
    · refine Or.inr ((Real.injOn_cos.eq_iff ⟨hnonneg1, hle1⟩
        ⟨by linarith [hnonneg2, hle2], by linarith [hnonneg2, hle2]⟩).mp ?_)
      rw [Real.cos_pi_sub]
      exact hcos
  have hF1_or : ∠ B C D = ∠ B F D ∨ ∠ B C D = π - ∠ B F D := by
    have hnonneg1 : 0 ≤ ∠ B C D := EuclideanGeometry.angle_nonneg B C D
    have hnonneg2 : 0 ≤ ∠ B F D := EuclideanGeometry.angle_nonneg B F D
    have hle1 : ∠ B C D ≤ π := EuclideanGeometry.angle_le_pi B C D
    have hle2 : ∠ B F D ≤ π := EuclideanGeometry.angle_le_pi B F D
    rcases hcosF with hcos | hcos
    · exact Or.inl ((Real.injOn_cos.eq_iff ⟨hnonneg1, hle1⟩ ⟨hnonneg2, hle2⟩).mp hcos)
    · refine Or.inr ((Real.injOn_cos.eq_iff ⟨hnonneg1, hle1⟩
        ⟨by linarith [hnonneg2, hle2], by linarith [hnonneg2, hle2]⟩).mp ?_)
      rw [Real.cos_pi_sub]
      exact hcos
  -- The angle values.
  have hCED : ∠ C E D = ∠ C A D + ∠ B C D := by
    have c1 : ∠ C E D = ∠ D E C := EuclideanGeometry.angle_comm C E D
    rw [c1, hvDEC]
  have hBFD : ∠ B F D = ∠ D A B + ∠ D B C := by
    have hAFB : ∠ A F B = π := EuclideanGeometry.angle_eq_pi_iff_sbtw.mpr ⟨hFw, hFneA, hFneB⟩
    have h1 : ∠ D F A + ∠ D F B = π := EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi D hAFB
    have c1 : ∠ D F B = ∠ B F D := EuclideanGeometry.angle_comm D F B
    have c2 : ∠ D F A = ∠ A F D := EuclideanGeometry.angle_comm D F A
    linarith [h1, c1, c2, hvAFD]
  have hbis' : ∠ D A B = ∠ C A D := hbis
  have hCBD : ∠ C B D = ∠ D B C := EuclideanGeometry.angle_comm C B D
  have hBCD : ∠ B C D = ∠ B C D := rfl
  -- Case analysis: the alternative branches contradict the angle sum; the main branches
  -- force `∠CAD = 0`.
  rcases hE1_or with hE1 | hE2
  · rcases hF1_or with hF1 | hF2
    · -- `γ = α + β` and `β = α + γ`: forces `α = 0`.
      rw [hCED, hCBD] at hE1
      rw [hBFD, hbis'] at hF1
      linarith [hE1, hF1, hpα]
    · -- `β = π − α − γ`: contradicts the angle sum.
      rw [hBFD, hbis'] at hF2
      linarith [hF2, hsum, hpα, hpφ, hpε]
  · rcases hF1_or with hF1 | hF2
    · rw [hCED, hCBD] at hE2
      rw [hBFD, hbis'] at hF1
      linarith [hE2, hF1, hsum, hpα, hpφ, hpε]
    · rw [hCED, hCBD] at hE2
      rw [hBFD, hbis'] at hF2
      linarith [hE2, hF2, hsum, hpα, hpφ, hpε]


/-- The tangent lines of the circumcircles of `BCD` and `DEF` at `D` coincide, and both
pass through `Z = BC ∩ EF`. As a consequence `ZD² = ZB·ZC = ZE·ZF`. -/
theorem tangent_power_at_Z [Module.Oriented ℝ V (Fin 2)] {A B C D E F X Z : P}
    (hai : AffineIndependent ℝ ![A, B, C])
    (hDint : D ∈ (⟨_, hai⟩ : Triangle ℝ P).interior)
    (hbis : ∠ D A B = ∠ C A D) (hlt : dist A C < dist A B)
    (hEw : Wbtw ℝ A E C) (hDE : ∠ A D E = ∠ B C D)
    (hFw : Wbtw ℝ A F B) (hDF : ∠ F D A = ∠ D B C)
    (hX : X ∈ line[ℝ, A, C]) (hXCB : dist C X = dist B X)
    (hEXD : AffineIndependent ℝ ![E, X, D])
    (hZBC : Z ∈ line[ℝ, B, C]) (hZsbtw : Sbtw ℝ B C Z)
    (hZEF : Z ∈ line[ℝ, E, F]) (hZsbtwEF : Sbtw ℝ Z E F) :
    ∃ sBCD sDEF : EuclideanGeometry.Sphere P,
      sBCD.IsTangentAt D (line[ℝ, D, Z]) ∧ sDEF.IsTangentAt D (line[ℝ, D, Z]) ∧
      dist Z D ^ 2 = dist Z B * dist Z C ∧ dist Z D ^ 2 = dist Z E * dist Z F ∧
      B ∈ sBCD ∧ C ∈ sBCD ∧ D ∈ sBCD ∧ D ∈ sDEF ∧ E ∈ sDEF ∧ F ∈ sDEF := by
  letI : FiniteDimensional ℝ V :=
    FiniteDimensional.of_finrank_eq_succ (n := 1) (Fact.out : finrank ℝ V = 2)
  -- Basic facts.
  have hAB : A ≠ B := hai.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hAC : A ≠ C := hai.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hBC : B ≠ C := hai.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  have hDA : D ≠ A := by
    rintro rfl
    exact Simplex.point_notMem_interior _ 0 hDint
  have hDB : D ≠ B := by
    rintro rfl
    exact Simplex.point_notMem_interior _ 1 hDint
  have hDC : D ≠ C := by
    rintro rfl
    exact Simplex.point_notMem_interior _ 2 hDint
  have hEneA := E_ne_A hai hDint hDE
  have hEneC := E_ne_C hai hDint hbis hEw hDE
  have hFneA := F_ne_A hai hDint hDF
  have hFneB := F_ne_B hai hDint hbis hFw hDF
  have hEF : E ≠ F := E_ne_F hai hEw hFw hEneA hFneA
  have hED : E ≠ D := by
    have hDnAC : D ∉ line[ℝ, A, C] := by
      have hai_BCA : AffineIndependent ℝ ![B, C, A] := affineIndependent_cycle hai
      have h := not_mem_line_of_mem_interior hai_BCA (mem_interior_cycle hai hai_BCA hDint)
      have e : line[ℝ, C, A] = line[ℝ, A, C] := by rw [Set.pair_comm]
      rwa [e] at h
    intro hED
    rw [hED] at hEw
    exact hDnAC hEw.mem_affineSpan
  have hFD : F ≠ D := by
    have hai_BCA : AffineIndependent ℝ ![B, C, A] := affineIndependent_cycle hai
    have hai_CAB : AffineIndependent ℝ ![C, A, B] := affineIndependent_cycle hai_BCA
    have hDnAB := not_mem_line_of_mem_interior hai_CAB
      (mem_interior_cycle hai_BCA hai_CAB (mem_interior_cycle hai hai_BCA hDint))
    intro hFD
    rw [hFD] at hFw
    exact hDnAB hFw.mem_affineSpan
  have hZD : Z ≠ D := by
    have hDnBC : D ∉ line[ℝ, B, C] := not_mem_line_of_mem_interior hai hDint
    intro hZD
    rw [hZD] at hZBC
    exact hDnBC hZBC
  have hZB : Z ≠ B := hZsbtw.left_ne_right.symm
  have hZC : Z ≠ C := hZsbtw.ne_right.symm
  have hZE : Z ≠ E := hZsbtwEF.ne_left.symm
  have hZF : Z ≠ F := hZsbtwEF.left_ne_right
  -- The circles.
  have htBCD : AffineIndependent ℝ ![B, C, D] := by
    have hDnBC : D ∉ line[ℝ, B, C] := not_mem_line_of_mem_interior hai hDint
    have hnc : ¬Collinear ℝ ({B, C, D} : Set P) :=
      fun h => hDnBC (h.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hBC)
    exact affineIndependent_iff_not_collinear_set.mpr hnc
  have htDEF : AffineIndependent ℝ ![D, E, F] :=
    affineIndependent_iff_not_collinear_set.mpr
      (not_collinear_DEF hai hDint hbis hEw hDE hFw hDF)
  set sBCD : EuclideanGeometry.Sphere P := (⟨_, htBCD⟩ : Triangle ℝ P).circumsphere with hsBCD
  set sDEF : EuclideanGeometry.Sphere P := (⟨_, htDEF⟩ : Triangle ℝ P).circumsphere with hsDEF
  have hDs : D ∈ sBCD := Simplex.mem_circumsphere _ 2
  have hBs : B ∈ sBCD := Simplex.mem_circumsphere _ 0
  have hCs : C ∈ sBCD := Simplex.mem_circumsphere _ 1
  have hDs2 : D ∈ sDEF := Simplex.mem_circumsphere _ 0
  have hEs2 : E ∈ sDEF := Simplex.mem_circumsphere _ 1
  have hFs2 : F ∈ sDEF := Simplex.mem_circumsphere _ 2
  have hXs2 : X ∈ (⟨_, hEXD⟩ : Triangle ℝ P).circumsphere := Simplex.mem_circumsphere _ 1
  -- `Z` is outside both circles.
  have hOut1 : sBCD.radius < dist Z sBCD.center :=
    radius_lt_dist_center_of_sbtw_of_mem_sphere hBs hCs hBC hZBC hZsbtw
  have hOut2 : sDEF.radius < dist Z sDEF.center :=
    radius_lt_dist_center_of_sbtw_of_mem_sphere hFs2 hEs2 hEF.symm
      (by rwa [Set.pair_comm] at hZEF) hZsbtwEF.symm
  -- The power equalities.
  have hpowBCEF : dist Z B * dist Z C = dist Z E * dist Z F := by
    obtain ⟨s0, hs0⟩ := EuclideanGeometry.cospherical_iff_exists_sphere.mp
      (concyclic_BCEF hai hDint hbis hEw hDE hFw hDF).Cospherical
    have hmems : B ∈ s0 ∧ C ∈ s0 ∧ E ∈ s0 ∧ F ∈ s0 := by
      simp only [Set.insert_subset_iff, Set.singleton_subset_iff] at hs0
      exact hs0
    obtain ⟨hBs0, hCs0, hEs0, hFs0⟩ := hmems
    have h1 : dist Z B * dist Z C = |s0.power Z| :=
      EuclideanGeometry.Sphere.mul_dist_eq_abs_power hZBC hBs0 hCs0
    have h2 : dist Z E * dist Z F = |s0.power Z| :=
      EuclideanGeometry.Sphere.mul_dist_eq_abs_power hZEF hEs0 hFs0
    rw [h1, h2]
  have hZBZC : dist Z B * dist Z C = sBCD.power Z :=
    EuclideanGeometry.Sphere.mul_dist_eq_power_of_radius_le_dist_center
      (EuclideanGeometry.Sphere.radius_nonneg_of_mem hBs) hZBC hBs hCs hOut1.le
  have hZEZF : dist Z E * dist Z F = sDEF.power Z :=
    EuclideanGeometry.Sphere.mul_dist_eq_power_of_radius_le_dist_center
      (EuclideanGeometry.Sphere.radius_nonneg_of_mem hEs2) hZEF hEs2 hFs2 hOut2.le
  have hpow_eq : sBCD.power Z = sDEF.power Z := by
    rw [← hZBZC, ← hZEZF]
    exact hpowBCEF
  -- The two tangent lines at `D` coincide.
  have hTanBCD : sBCD.IsTangentAt D (sBCD.orthRadius D) :=
    (EuclideanGeometry.Sphere.isTangentAt_orthRadius_iff_mem).mpr hDs
  have hTanDEF : sDEF.IsTangentAt D (sDEF.orthRadius D) :=
    (EuclideanGeometry.Sphere.isTangentAt_orthRadius_iff_mem).mpr hDs2
  have hsub : sBCD.orthRadius D ≤ sDEF.orthRadius D := by
    intro T hTm
    by_cases hTD : T = D
    · rw [hTD]
      exact EuclideanGeometry.Sphere.self_mem_orthRadius sDEF D
    · exact mem_orthRadius_of_two_zsmul_oangle_eq hDs2 hEs2 hFs2 hED hFD hTD hEF
        (two_zsmul_oangle_tangent_chase hai hDint hbis hEw hDE hFw hDF htBCD hTm hTD)
  have hDnBCD : D ≠ sBCD.center := by
    intro hDc
    have h0 : sBCD.radius = 0 := by
      have h := hDs
      rw [hDc, EuclideanGeometry.Sphere.center_mem_iff] at h
      exact h
    have h1 : dist B sBCD.center = 0 := by
      have h2 := EuclideanGeometry.mem_sphere.mp hBs
      rw [h0] at h2
      exact h2
    exact hDB (((dist_eq_zero.mp h1).trans hDc.symm).symm)
  have hDnDEF : D ≠ sDEF.center := by
    intro hDc
    have h0 : sDEF.radius = 0 := by
      have h := hDs2
      rw [hDc, EuclideanGeometry.Sphere.center_mem_iff] at h
      exact h
    have h1 : dist E sDEF.center = 0 := by
      have h2 := EuclideanGeometry.mem_sphere.mp hEs2
      rw [h0] at h2
      exact h2
    exact hED ((dist_eq_zero.mp h1).trans hDc.symm)
  have hfin1 : finrank ℝ (sBCD.orthRadius D).direction = 1 := by
    have h := EuclideanGeometry.Sphere.finrank_orthRadius hDnBCD
    have h2 : finrank ℝ V = 2 := Fact.out
    rw [h2] at h
    linarith [h]
  have hfin2 : finrank ℝ (sDEF.orthRadius D).direction = 1 := by
    have h := EuclideanGeometry.Sphere.finrank_orthRadius hDnDEF
    have h2 : finrank ℝ V = 2 := Fact.out
    rw [h2] at h
    linarith [h]
  have hEq : sBCD.orthRadius D = sDEF.orthRadius D :=
    (AffineSubspace.eq_iff_direction_eq_of_mem (EuclideanGeometry.Sphere.self_mem_orthRadius sBCD D)
      (EuclideanGeometry.Sphere.self_mem_orthRadius sDEF D)).mpr
      (Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hsub) (by rw [hfin1, hfin2]))
  -- The two circles are distinct (the inscribed-angle conditions would force `∠CAD = 0`).
  have hsne : sBCD ≠ sDEF :=
    sphere_BCD_ne_sphere_DEF hai hDint hbis hEw hDE hFw hDF htBCD htDEF
  -- The centers are collinear with `D` on the common normal.
  have hspan : (ℝ ∙ (D -ᵥ sBCD.center)) = (ℝ ∙ (D -ᵥ sDEF.center)) := by
    have h1 := congr_arg Submodule.orthogonal (congr_arg AffineSubspace.direction hEq)
    rw [EuclideanGeometry.Sphere.direction_orthRadius,
      EuclideanGeometry.Sphere.direction_orthRadius, Submodule.orthogonal_orthogonal,
      Submodule.orthogonal_orthogonal] at h1
    exact h1
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp
    (hspan ▸ Submodule.mem_span_singleton_self (D -ᵥ sBCD.center))
  have ht1 : t ≠ 1 := by
    intro ht1
    rw [ht1, one_smul] at ht
    have hc : sBCD.center = sDEF.center := by
      have hneg := congrArg Neg.neg ht
      simp only [neg_vsub_eq_vsub_rev] at hneg
      exact (vsub_left_cancel_iff.mp hneg).symm
    have hr : sBCD.radius = sDEF.radius := by
      have h1 := EuclideanGeometry.mem_sphere.mp hDs
      have h2 := EuclideanGeometry.mem_sphere.mp hDs2
      rw [hc] at h1
      exact h1.symm.trans h2
    exact hsne (by
      rw [← EuclideanGeometry.Sphere.mk_center_radius sBCD,
        ← EuclideanGeometry.Sphere.mk_center_radius sDEF, hc, hr])
  -- `Z` is on the common tangent line.
  have hZtan : Z ∈ sDEF.orthRadius D := by
    rw [← hEq]
    have hinner : ⟪Z -ᵥ D, D -ᵥ sBCD.center⟫ = 0 := by
      have hexp := inner_eq_zero_of_power_eq_power hDs hDs2 hpow_eq
      have hsub2 : sDEF.center -ᵥ sBCD.center = (t - 1) • (D -ᵥ sDEF.center) := by
        have h5 : sDEF.center -ᵥ sBCD.center = (D -ᵥ sBCD.center) - (D -ᵥ sDEF.center) :=
          (vsub_sub_vsub_cancel_left sDEF.center sBCD.center D).symm
        rw [h5, ← ht]
        module
      rw [hsub2, inner_smul_right] at hexp
      have h4 : ⟪Z -ᵥ D, D -ᵥ sDEF.center⟫ = 0 := by
        rcases mul_eq_zero.mp hexp with h5 | h5
        · exact absurd (sub_eq_zero.mp h5) ht1
        · exact h5
      rw [← ht, inner_smul_right, h4, mul_zero]
    have hinner' : ⟪Z -ᵥ D, D -ᵥ sBCD.center⟫ = 0 := hinner
    have := (EuclideanGeometry.Sphere.mem_orthRadius_iff_inner_left).mpr hinner'
    exact this
  have hEqLine : line[ℝ, D, Z] = sDEF.orthRadius D := by
    have hle : line[ℝ, D, Z] ≤ sDEF.orthRadius D := by
      rw [affineSpan_le, Set.insert_subset_iff]
      exact ⟨EuclideanGeometry.Sphere.self_mem_orthRadius sDEF D,
        Set.singleton_subset_iff.mpr hZtan⟩
    have hfin3 : finrank ℝ (line[ℝ, D, Z]).direction = 1 := by
      rw [direction_affineSpan, vectorSpan_pair,
        finrank_span_singleton (vsub_ne_zero.mpr hZD.symm)]
    exact (AffineSubspace.eq_iff_direction_eq_of_mem (left_mem_affineSpan_pair ℝ D Z)
      (EuclideanGeometry.Sphere.self_mem_orthRadius sDEF D)).mpr
      (Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hle) (by rw [hfin3, hfin2]))
  have hTanZ : sDEF.IsTangentAt D (line[ℝ, D, Z]) := hEqLine ▸ hTanDEF
  have hTanZ2 : sBCD.IsTangentAt D (line[ℝ, D, Z]) := hEqLine ▸ (hEq ▸ hTanBCD)
  -- The products.
  refine ⟨sBCD, sDEF, hTanZ2, hTanZ, ?_, ?_, hBs, hCs, hDs, hDs2, hEs2, hFs2⟩
  · have hTanZ2' : sBCD.IsTangentAt D (line[ℝ, Z, D]) := by
      rw [Set.pair_comm] at hTanZ2
      exact hTanZ2
    have hpow2 : dist Z D ^ 2 = sBCD.power Z := (hTanZ2'.power_eq_dist_sq).symm
    rw [hpow2, hZBZC]
  · have hTanZ' : sDEF.IsTangentAt D (line[ℝ, Z, D]) := by
      rw [Set.pair_comm] at hTanZ
      exact hTanZ
    have hpow1 : dist Z D ^ 2 = sDEF.power Z := (hTanZ'.power_eq_dist_sq).symm
    rw [hpow1, hZEZF]

theorem sphere_eq_of_mem_of_mem_of_mem_of_not_collinear {s₁ s₂ : EuclideanGeometry.Sphere P}
    {p₁ p₂ p₃ : P}
    (h₁₁ : p₁ ∈ s₁) (h₁₂ : p₂ ∈ s₁) (h₁₃ : p₃ ∈ s₁)
    (h₂₁ : p₁ ∈ s₂) (h₂₂ : p₂ ∈ s₂) (h₂₃ : p₃ ∈ s₂)
    (hnc : ¬Collinear ℝ ({p₁, p₂, p₃} : Set P)) : s₁ = s₂ := by
  haveI : FiniteDimensional ℝ V := .of_fact_finrank_eq_two
  by_contra hne
  have h12 : p₁ ≠ p₂ := by
    intro h
    apply hnc
    have hset : ({p₁, p₂, p₃} : Set P) = {p₂, p₃} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro (rfl | rfl | rfl)
        · exact Or.inl h
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
    rw [hset]
    exact collinear_pair ℝ _ _
  have h31 : p₃ ≠ p₁ := by
    intro h
    apply hnc
    have hset : ({p₁, p₂, p₃} : Set P) = {p₂, p₁} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro (rfl | rfl | rfl)
        · exact Or.inr rfl
        · exact Or.inl rfl
        · exact Or.inr h
      · rintro (rfl | rfl)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl rfl
    rw [hset]
    exact collinear_pair ℝ _ _
  have h32 : p₃ ≠ p₂ := by
    intro h
    apply hnc
    have hset : ({p₁, p₂, p₃} : Set P) = {p₁, p₂} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro (rfl | rfl | rfl)
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact Or.inr h
      · rintro (rfl | rfl)
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
    rw [hset]
    exact collinear_pair ℝ _ _
  rcases EuclideanGeometry.eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two Fact.out hne h12
    h₁₁ h₁₂ h₁₃ h₂₁ h₂₂ h₂₃ with h | h
  · exact h31 h
  · exact h32 h

/-- LEMMA 4: image of a point on a sphere through the inversion center has fixed
inner product with the radius vector. -/
theorem inner_inversion_vsub_center_eq_half_sq {s : EuclideanGeometry.Sphere P} {c x : P} {R : ℝ}
    (hc : c ∈ s) (hx : x ∈ s) (hxne : x ≠ c) :
    ⟪EuclideanGeometry.inversion c R x -ᵥ c, s.center -ᵥ c⟫ = R ^ 2 / 2 := by
  rw [EuclideanGeometry.mem_sphere] at hc hx
  have hu : x -ᵥ c ≠ 0 := by rwa [vsub_ne_zero]
  have hnorm_w : ‖s.center -ᵥ c‖ = s.radius := by
    rw [← neg_vsub_eq_vsub_rev c s.center, norm_neg, ← dist_eq_norm_vsub V c s.center, hc]
  have hnorm_uw : ‖(x -ᵥ c) - (s.center -ᵥ c)‖ = s.radius := by
    rw [vsub_sub_vsub_cancel_right, ← dist_eq_norm_vsub V x s.center, hx]
  have key : ‖x -ᵥ c‖ ^ 2 = 2 * ⟪x -ᵥ c, s.center -ᵥ c⟫ := by
    have h := norm_sub_sq_real (x -ᵥ c) (s.center -ᵥ c)
    rw [hnorm_uw, hnorm_w] at h
    linarith
  have hune : ‖x -ᵥ c‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hu)
  have hin : ⟪x -ᵥ c, s.center -ᵥ c⟫ ≠ 0 := by
    intro hz
    apply hune
    rw [key, hz]
    ring
  rw [EuclideanGeometry.inversion_vsub_center, dist_eq_norm_vsub V x c, div_pow,
    real_inner_smul_left, key]
  field_simp [hin]

/-- LEMMA 3: image of a sphere under inversion is a sphere. -/
theorem inversion_sphere_image {s : EuclideanGeometry.Sphere P} {c : P} {R : ℝ}
    (hR : R ≠ 0) (hs : (s : Set P).Nonempty) (hc : c ∉ s) :
    ∃ s' : EuclideanGeometry.Sphere P,
      Set.image (EuclideanGeometry.inversion c R) s = s' ∧
      s'.center = (R ^ 2 / s.power c) • (s.center -ᵥ c) +ᵥ c ∧
      s'.radius = R ^ 2 * s.radius / |s.power c| := by
  obtain ⟨p₀, hp₀⟩ := hs
  have hr0 : 0 ≤ s.radius := EuclideanGeometry.Sphere.radius_nonneg_of_mem hp₀
  have hP : s.power c ≠ 0 := by
    intro hP0
    exact hc ((EuclideanGeometry.Sphere.power_eq_zero_iff_mem_sphere hr0).mp hP0)
  set Pp := s.power c with hPdef
  set w : V := s.center -ᵥ c with hwdef
  have hPw : Pp = ‖w‖ ^ 2 - s.radius ^ 2 := by
    rw [hPdef]
    unfold EuclideanGeometry.Sphere.power
    rw [dist_eq_norm_vsub V c s.center, ← norm_neg (c -ᵥ s.center), neg_vsub_eq_vsub_rev c s.center,
      ← hwdef]
  set r' := R ^ 2 * s.radius / |Pp| with hr'def
  have hr'0 : 0 ≤ r' := div_nonneg (mul_nonneg (sq_nonneg _) hr0) (abs_nonneg _)
  have key : ∀ y : P, (EuclideanGeometry.inversion c R y ∈ s) ↔
      dist y ((R ^ 2 / Pp) • w +ᵥ c) = r' := by
    intro y
    by_cases hyc : y = c
    · rw [hyc]
      rw [EuclideanGeometry.inversion_self]
      constructor
      · intro h'
        exact absurd h' hc
      · intro h
        exfalso
        have hd : dist c ((R ^ 2 / Pp) • w +ᵥ c) = R ^ 2 * ‖w‖ / |Pp| := by
          rw [dist_eq_norm_vsub' V c _, vadd_vsub, norm_smul, Real.norm_eq_abs, abs_div,
            abs_of_nonneg (sq_nonneg R), div_mul_eq_mul_div]
        rw [hd, hr'def] at h
        have hPabs : |Pp| ≠ 0 := abs_ne_zero.mpr hP
        have e1 : R ^ 2 * ‖w‖ = R ^ 2 * s.radius := by
          have h2 := congrArg (· * |Pp|) h
          rwa [div_mul_cancel₀ _ hPabs, div_mul_cancel₀ _ hPabs] at h2
        have e2 : ‖w‖ = s.radius := mul_left_cancel₀ (pow_ne_zero 2 hR) e1
        exact hc (by
          rw [EuclideanGeometry.mem_sphere, dist_eq_norm_vsub V c s.center,
            ← norm_neg (c -ᵥ s.center), neg_vsub_eq_vsub_rev c s.center, ← hwdef, e2])
    · have hz : y -ᵥ c ≠ 0 := by rwa [vsub_ne_zero]
      set z := y -ᵥ c with hzdef
      have hzn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
      have h1 : EuclideanGeometry.inversion c R y -ᵥ s.center = (R ^ 2 / ‖z‖ ^ 2) • z - w := by
        rw [← vsub_sub_vsub_cancel_right (EuclideanGeometry.inversion c R y) s.center c,
          EuclideanGeometry.inversion_vsub_center, ← hwdef, ← hzdef, dist_eq_norm_vsub V y c,
          ← hzdef, div_pow]
      have hd1 : dist (EuclideanGeometry.inversion c R y) s.center ^ 2 =
          (R ^ 2 / ‖z‖ ^ 2) ^ 2 * ‖z‖ ^ 2 - 2 * (R ^ 2 / ‖z‖ ^ 2) * ⟪z, w⟫ + ‖w‖ ^ 2 := by
        rw [dist_eq_norm_vsub V _ s.center, h1, norm_sub_sq_real, real_inner_smul_left, norm_smul,
          Real.norm_eq_abs, mul_pow, sq_abs]
        ring
      have eqA : ‖z‖ ^ 2 * (dist (EuclideanGeometry.inversion c R y) s.center ^ 2 - s.radius ^ 2) =
          R ^ 4 - 2 * R ^ 2 * ⟪z, w⟫ + ‖z‖ ^ 2 * Pp := by
        rw [hd1, hPw]
        field_simp [pow_ne_zero 2 hzn]
        ring
      have h2 : y -ᵥ ((R ^ 2 / Pp) • w +ᵥ c) = z - (R ^ 2 / Pp) • w := by
        rw [vsub_vadd_eq_vsub_sub, ← hzdef]
      have hd2 : dist y ((R ^ 2 / Pp) • w +ᵥ c) ^ 2 =
          ‖z‖ ^ 2 - 2 * (R ^ 2 / Pp) * ⟪z, w⟫ + (R ^ 2 / Pp) ^ 2 * ‖w‖ ^ 2 := by
        rw [dist_eq_norm_vsub V y _, h2, norm_sub_sq_real, real_inner_smul_right, norm_smul,
          Real.norm_eq_abs, mul_pow, sq_abs]
        ring
      have hr'sq : r' ^ 2 = R ^ 4 * s.radius ^ 2 / Pp ^ 2 := by
        rw [hr'def, div_pow, mul_pow, sq_abs]
        ring
      have hX : ‖w‖ ^ 2 - s.radius ^ 2 ≠ 0 := by rw [← hPw]; exact hP
      have eqB : Pp ^ 2 * (dist y ((R ^ 2 / Pp) • w +ᵥ c) ^ 2 - r' ^ 2) =
          Pp * (R ^ 4 - 2 * R ^ 2 * ⟪z, w⟫ + ‖z‖ ^ 2 * Pp) := by
        rw [hd2, hr'sq, hPw]
        field_simp [hX, pow_ne_zero 2 hX]
        ring
      rw [EuclideanGeometry.mem_sphere]
      constructor
      · intro h
        have hA : R ^ 4 - 2 * R ^ 2 * ⟪z, w⟫ + ‖z‖ ^ 2 * Pp = 0 := by
          have h1' : dist (EuclideanGeometry.inversion c R y) s.center ^ 2 - s.radius ^ 2 = 0 := by
            rw [h]; ring
          have h2' := eqA
          rw [h1', mul_zero] at h2'
          exact h2'.symm
        have hB : dist y ((R ^ 2 / Pp) • w +ᵥ c) ^ 2 = r' ^ 2 := by
          have h2' : Pp ^ 2 * (dist y ((R ^ 2 / Pp) • w +ᵥ c) ^ 2 - r' ^ 2) = 0 := by
            rw [eqB, hA, mul_zero]
          rcases mul_eq_zero.mp h2' with h3 | h3
          · exact absurd h3 (pow_ne_zero 2 hP)
          · exact eq_of_sub_eq_zero h3
        exact (pow_left_inj₀ dist_nonneg hr'0 two_ne_zero).mp hB
      · intro h
        have hB : R ^ 4 - 2 * R ^ 2 * ⟪z, w⟫ + ‖z‖ ^ 2 * Pp = 0 := by
          have h1' : dist y ((R ^ 2 / Pp) • w +ᵥ c) ^ 2 - r' ^ 2 = 0 := by
            rw [h]; ring
          have h2' := eqB
          rw [h1', mul_zero] at h2'
          exact (mul_eq_zero.mp h2'.symm).resolve_left hP
        have hA : dist (EuclideanGeometry.inversion c R y) s.center ^ 2 = s.radius ^ 2 := by
          have h2' : ‖z‖ ^ 2 *
              (dist (EuclideanGeometry.inversion c R y) s.center ^ 2 - s.radius ^ 2) = 0 := by
            rw [eqA, hB]
          rcases mul_eq_zero.mp h2' with h3 | h3
          · exact absurd h3 (pow_ne_zero 2 hzn)
          · exact eq_of_sub_eq_zero h3
        exact (pow_left_inj₀ dist_nonneg hr0 two_ne_zero).mp hA
  refine ⟨⟨(R ^ 2 / Pp) • w +ᵥ c, r'⟩, ?_, rfl, rfl⟩
  rw [EuclideanGeometry.Sphere.coe_mk]
  ext y
  simp only [Set.mem_image, Metric.mem_sphere]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (key (EuclideanGeometry.inversion c R x)).mp
      (by rwa [EuclideanGeometry.inversion_inversion c hR])
  · intro h
    exact ⟨EuclideanGeometry.inversion c R y, (key y).mpr h,
      EuclideanGeometry.inversion_inversion c hR y⟩

/-- LEMMA 5: triangle interior lies strictly inside the circumcircle. -/
theorem dist_lt_circumradius_of_mem_interior {t : Affine.Triangle ℝ P} {D : P}
    (hD : D ∈ t.interior) : dist D t.circumcenter < t.circumradius := by
  obtain ⟨w, hw1, hwI, hDw⟩ := hD
  have hr : 0 < t.circumradius := t.circumradius_pos
  set O := t.circumcenter with hO
  have hw1' : w 0 + w 1 + w 2 = 1 := by
    rw [← Fin.sum_univ_three]
    exact hw1
  have hDv : D -ᵥ O = w 0 • (t.points 0 -ᵥ O) + w 1 • (t.points 1 -ᵥ O) +
      w 2 • (t.points 2 -ᵥ O) := by
    rw [← hDw,
      Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one Finset.univ w t.points hw1 O,
      vadd_vsub, Finset.weightedVSubOfPoint_apply, Fin.sum_univ_three]
  have hv : ∀ i : Fin 3, ‖t.points i -ᵥ O‖ = t.circumradius := fun i => by
    rw [← dist_eq_norm_vsub V _ O]
    exact t.dist_circumcenter_eq_circumradius i
  have hvsq : ∀ i : Fin 3, ‖t.points i -ᵥ O‖ ^ 2 = t.circumradius ^ 2 := fun i => by rw [hv i]
  have hne : ∀ {i j : Fin 3}, i ≠ j → t.points i -ᵥ O ≠ t.points j -ᵥ O := fun hij h =>
    (t.independent.injective.ne hij) (vsub_left_injective O h)
  have hinner : ∀ {i j : Fin 3}, i ≠ j →
      ⟪t.points i -ᵥ O, t.points j -ᵥ O⟫ < t.circumradius ^ 2 := by
    intro i j hij
    have h := norm_sub_sq_real (t.points i -ᵥ O) (t.points j -ᵥ O)
    have hpos : (0 : ℝ) < ‖(t.points i -ᵥ O) - (t.points j -ᵥ O)‖ ^ 2 :=
      sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hne hij)))
    have h0 := hvsq i
    have h1 := hvsq j
    linarith
  have hexp : ‖D -ᵥ O‖ ^ 2 =
      w 0 ^ 2 * ‖t.points 0 -ᵥ O‖ ^ 2 + w 1 ^ 2 * ‖t.points 1 -ᵥ O‖ ^ 2 +
      w 2 ^ 2 * ‖t.points 2 -ᵥ O‖ ^ 2 +
      2 * (w 0 * w 1) * ⟪t.points 0 -ᵥ O, t.points 1 -ᵥ O⟫ +
      2 * (w 0 * w 2) * ⟪t.points 0 -ᵥ O, t.points 2 -ᵥ O⟫ +
      2 * (w 1 * w 2) * ⟪t.points 1 -ᵥ O, t.points 2 -ᵥ O⟫ := by
    rw [hDv]
    simp only [norm_add_sq_real, inner_add_left, real_inner_smul_left, real_inner_smul_right,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg (hwI 0).1.le, abs_of_nonneg (hwI 1).1.le,
      abs_of_nonneg (hwI 2).1.le]
    ring
  rw [hvsq 0, hvsq 1, hvsq 2] at hexp
  have e01 : 2 * (w 0 * w 1) * ⟪t.points 0 -ᵥ O, t.points 1 -ᵥ O⟫ <
      2 * (w 0 * w 1) * t.circumradius ^ 2 :=
    mul_lt_mul_of_pos_left (hinner (by decide : (0 : Fin 3) ≠ 1))
      (mul_pos two_pos (mul_pos (hwI 0).1 (hwI 1).1))
  have e02 : 2 * (w 0 * w 2) * ⟪t.points 0 -ᵥ O, t.points 2 -ᵥ O⟫ <
      2 * (w 0 * w 2) * t.circumradius ^ 2 :=
    mul_lt_mul_of_pos_left (hinner (by decide : (0 : Fin 3) ≠ 2))
      (mul_pos two_pos (mul_pos (hwI 0).1 (hwI 2).1))
  have e12 : 2 * (w 1 * w 2) * ⟪t.points 1 -ᵥ O, t.points 2 -ᵥ O⟫ <
      2 * (w 1 * w 2) * t.circumradius ^ 2 :=
    mul_lt_mul_of_pos_left (hinner (by decide : (1 : Fin 3) ≠ 2))
      (mul_pos two_pos (mul_pos (hwI 1).1 (hwI 2).1))
  have hwsq : (w 0 + w 1 + w 2) ^ 2 = 1 := by
    rw [hw1']
    norm_num
  have hsum : w 0 ^ 2 * t.circumradius ^ 2 + w 1 ^ 2 * t.circumradius ^ 2 +
      w 2 ^ 2 * t.circumradius ^ 2 + 2 * (w 0 * w 1) * t.circumradius ^ 2 +
      2 * (w 0 * w 2) * t.circumradius ^ 2 + 2 * (w 1 * w 2) * t.circumradius ^ 2 =
      t.circumradius ^ 2 := by
    calc w 0 ^ 2 * t.circumradius ^ 2 + w 1 ^ 2 * t.circumradius ^ 2 +
          w 2 ^ 2 * t.circumradius ^ 2 + 2 * (w 0 * w 1) * t.circumradius ^ 2 +
          2 * (w 0 * w 2) * t.circumradius ^ 2 + 2 * (w 1 * w 2) * t.circumradius ^ 2
        = (w 0 + w 1 + w 2) ^ 2 * t.circumradius ^ 2 := by ring
      _ = t.circumradius ^ 2 := by rw [hwsq]; ring
  have hlt : ‖D -ᵥ O‖ ^ 2 < t.circumradius ^ 2 := by linarith [hexp, e01, e02, e12, hsum]
  rw [dist_eq_norm_vsub V D O]
  exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hr.le two_ne_zero).mp hlt

/-- `Z, C, E` are not collinear, so they form a triangle: `E` lies on line `AC`, and
line `AC` meets line `BC` (which contains `Z ≠ C`) only at `C`. -/
theorem affineIndependent_ZCE {A B C E Z : P} (hai : AffineIndependent ℝ ![A, B, C])
    (hEAC : E ∈ line[ℝ, A, C]) (hEC : E ≠ C) (hZBC : Z ∈ line[ℝ, B, C]) (hZC : Z ≠ C) :
    AffineIndependent ℝ ![Z, C, E] := by
  refine affineIndependent_iff_not_collinear_set.mpr fun hcol => ?_
  have hEline : E ∈ line[ℝ, Z, C] :=
    hcol.mem_affineSpan_of_mem_of_ne (Set.mem_insert _ _)
      (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))) hZC
  have hsub : ({E, C, Z} : Set P) ⊆ {Z, C, E} := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  have hZline : Z ∈ line[ℝ, E, C] :=
    (hcol.subset hsub).mem_affineSpan_of_mem_of_ne (Set.mem_insert _ _)
      (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))) hEC
  -- `Z` is on both line `BC` and line `EC = line AC`; hence lines coincide or `Z = C`.
  have hA : A ∈ line[ℝ, E, C] := by
    have hEAC' : E ∈ line[ℝ, C, A] := Set.pair_comm A C ▸ hEAC
    exact (collinear_insert_of_mem_affineSpan_pair hEAC').mem_affineSpan_of_mem_of_ne
      (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))) hEC
  have hB : B ∈ line[ℝ, Z, C] :=
    (collinear_insert_of_mem_affineSpan_pair hZBC).mem_affineSpan_of_mem_of_ne
      (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) hZC
  have hB' : B ∈ line[ℝ, E, C] := by
    have h1 : line[ℝ, Z, C] = line[ℝ, E, C] :=
      (AffineSubspace.eq_iff_direction_eq_of_mem (right_mem_affineSpan_pair ℝ Z C)
        (right_mem_affineSpan_pair ℝ E C)).mpr
        (Submodule.eq_of_le_of_finrank_eq
          (AffineSubspace.direction_le (by
            rw [affineSpan_le, Set.insert_subset_iff]
            exact ⟨hZline, Set.singleton_subset_iff.mpr (right_mem_affineSpan_pair ℝ E C)⟩))
          (by rw [direction_affineSpan, vectorSpan_pair, direction_affineSpan, vectorSpan_pair,
              finrank_span_singleton (vsub_ne_zero.mpr hZC),
              finrank_span_singleton (vsub_ne_zero.mpr hEC)]))
    rwa [h1] at hB
  have hcol3 : Collinear ℝ ({A, B, C} : Set P) :=
    (collinear_insert_insert_of_mem_affineSpan_pair hA hB').subset
      (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)
  exact (affineIndependent_iff_not_collinear_set.mp hai) hcol3

/-- A point of line `BC` different from `C` does not lie on line `AC`. -/
theorem not_mem_line_AC_of_mem_line_BC {A B C Z : P} (hai : AffineIndependent ℝ ![A, B, C])
    (hZBC : Z ∈ line[ℝ, B, C]) (hZC : Z ≠ C) : Z ∉ line[ℝ, A, C] := by
  intro hZAC
  have hA : A ∈ line[ℝ, Z, C] :=
    (collinear_insert_of_mem_affineSpan_pair hZAC).mem_affineSpan_of_mem_of_ne
      (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) hZC
  have hB : B ∈ line[ℝ, Z, C] :=
    (collinear_insert_of_mem_affineSpan_pair hZBC).mem_affineSpan_of_mem_of_ne
      (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) hZC
  have hcol3 : Collinear ℝ ({A, B, C} : Set P) :=
    (collinear_insert_insert_of_mem_affineSpan_pair hA hB).subset
      (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)
  exact (affineIndependent_iff_not_collinear_set.mp hai) hcol3

/-- A point of line `BC` different from `B` does not lie on line `AB`. -/
theorem not_mem_line_AB_of_mem_line_BC {A B C Z : P} (hai : AffineIndependent ℝ ![A, B, C])
    (hZBC : Z ∈ line[ℝ, B, C]) (hZB : Z ≠ B) : Z ∉ line[ℝ, A, B] := by
  intro hZAB
  have hA : A ∈ line[ℝ, Z, B] :=
    (collinear_insert_of_mem_affineSpan_pair hZAB).mem_affineSpan_of_mem_of_ne
      (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) hZB
  have hC : C ∈ line[ℝ, Z, B] :=
    (collinear_insert_of_mem_affineSpan_pair hZBC).mem_affineSpan_of_mem_of_ne
      (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))) hZB
  have hcol3 : Collinear ℝ ({A, B, C} : Set P) :=
    (collinear_insert_insert_of_mem_affineSpan_pair hA hC).subset
      (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)
  exact (affineIndependent_iff_not_collinear_set.mp hai) hcol3

/-- If `E` lies on line `AC` with `E ≠ C`, then `A` lies on line `CE`. -/
theorem mem_line_CE_of_mem_line_AC {A C E : P} (hEAC : E ∈ line[ℝ, A, C]) (hEC : E ≠ C) :
    A ∈ line[ℝ, C, E] := by
  have h1 : E ∈ line[ℝ, C, A] := Set.pair_comm A C ▸ hEAC
  have h2 := (collinear_insert_of_mem_affineSpan_pair h1).mem_affineSpan_of_mem_of_ne
    (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))) hEC
  rwa [Set.pair_comm E C] at h2

/-- If `E` lies on line `AC` with `E ≠ C` and `A ≠ C`, then lines `CA` and `CE` agree. -/
theorem line_CA_eq_line_CE_of_mem {A C E : P} (hEAC : E ∈ line[ℝ, A, C]) (hAC : A ≠ C)
    (hEC : E ≠ C) : line[ℝ, C, A] = line[ℝ, C, E] :=
  (AffineSubspace.eq_iff_direction_eq_of_mem (left_mem_affineSpan_pair ℝ C A)
    (left_mem_affineSpan_pair ℝ C E)).mpr
    (Submodule.eq_of_le_of_finrank_eq
      (AffineSubspace.direction_le (by
        rw [affineSpan_le, Set.insert_subset_iff]
        exact ⟨left_mem_affineSpan_pair ℝ C E,
          Set.singleton_subset_iff.mpr (mem_line_CE_of_mem_line_AC hEAC hEC)⟩))
      (by rw [direction_affineSpan, vectorSpan_pair, direction_affineSpan, vectorSpan_pair,
          finrank_span_singleton (vsub_ne_zero.mpr hAC.symm),
          finrank_span_singleton (vsub_ne_zero.mpr hEC.symm)]))

/-- If `E` lies on line `AC` with `E ≠ A` and `A ≠ C`, then lines `EA` and `CA` agree. -/
theorem line_EA_eq_line_CA_of_mem {A C E : P} (hEAC : E ∈ line[ℝ, A, C]) (hEneA : E ≠ A)
    (hAC : A ≠ C) : line[ℝ, E, A] = line[ℝ, C, A] := by
  rw [Set.pair_comm E A, Set.pair_comm C A]
  exact (AffineSubspace.eq_iff_direction_eq_of_mem (left_mem_affineSpan_pair ℝ A E)
    (left_mem_affineSpan_pair ℝ A C)).mpr
    (Submodule.eq_of_le_of_finrank_eq
      (AffineSubspace.direction_le (by
        rw [affineSpan_le, Set.insert_subset_iff]
        exact ⟨left_mem_affineSpan_pair ℝ A C, Set.singleton_subset_iff.mpr hEAC⟩))
      (by rw [direction_affineSpan, vectorSpan_pair, direction_affineSpan, vectorSpan_pair,
          finrank_span_singleton (vsub_ne_zero.mpr hEneA.symm),
          finrank_span_singleton (vsub_ne_zero.mpr hAC)]))

/-- The Miquel point of the cyclic quadrilateral `BCEF`: the second intersection of line `AZ`
with the circumcircle of `ABC`. It lies on line `AZ` and differs from all of
`A, Z, C, B, E`. -/
theorem miquel_M_exists [Module.Oriented ℝ V (Fin 2)] {A B C D E F Z : P}
    (hai : AffineIndependent ℝ ![A, B, C])
    (hDint : D ∈ (⟨_, hai⟩ : Triangle ℝ P).interior)
    (hbis : ∠ D A B = ∠ C A D)
    (hEw : Wbtw ℝ A E C) (hDE : ∠ A D E = ∠ B C D)
    (hFw : Wbtw ℝ A F B) (hDF : ∠ F D A = ∠ D B C)
    (hZBC : Z ∈ line[ℝ, B, C]) (hZsbtw : Sbtw ℝ B C Z)
    (hZEF : Z ∈ line[ℝ, E, F]) (hZsbtwEF : Sbtw ℝ Z E F) :
    ∃ M : P, M ∈ (⟨_, hai⟩ : Triangle ℝ P).circumsphere ∧ M ∈ line[ℝ, A, Z] ∧
      M ≠ A ∧ M ≠ Z ∧ M ≠ C ∧ M ≠ B ∧ M ≠ E := by
  letI : FiniteDimensional ℝ V :=
    FiniteDimensional.of_finrank_eq_succ (n := 1) (Fact.out : finrank ℝ V = 2)
  have hAB : A ≠ B := hai.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hAC : A ≠ C := hai.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hBC : B ≠ C := hai.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  have hEneA := E_ne_A hai hDint hDE
  have hEneC := E_ne_C hai hDint hbis hEw hDE
  have hFneA := F_ne_A hai hDint hDF
  have hFneB := F_ne_B hai hDint hbis hFw hDF
  have hEF : E ≠ F := E_ne_F hai hEw hFw hEneA hFneA
  have hZB : Z ≠ B := hZsbtw.left_ne_right.symm
  have hZC : Z ≠ C := hZsbtw.ne_right.symm
  have hZE : Z ≠ E := hZsbtwEF.ne_left.symm
  have hZF : Z ≠ F := hZsbtwEF.left_ne_right
  have hZA : Z ∉ line[ℝ, A, C] := not_mem_line_AC_of_mem_line_BC hai hZBC hZC
  have hZnA : Z ∉ line[ℝ, A, B] := not_mem_line_AB_of_mem_line_BC hai hZBC hZB
  have hZneA : Z ≠ A := fun h => hZA (by rw [h]; exact left_mem_affineSpan_pair ℝ A C)
  have hEAC : E ∈ line[ℝ, A, C] := hEw.mem_affineSpan
  have hFAB : F ∈ line[ℝ, A, B] := hFw.mem_affineSpan
  have hcycBCEF : EuclideanGeometry.Cospherical ({B, C, E, F} : Set P) :=
    (concyclic_BCEF hai hDint hbis hEw hDE hFw hDF).Cospherical
  -- The triangle and its circumsphere.
  have haiCBA : AffineIndependent ℝ ![C, B, A] := by
    refine affineIndependent_iff_not_collinear_set.mpr fun hcol => ?_
    exact (affineIndependent_iff_not_collinear_set.mp hai)
      (hcol.subset (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto))
  set sABC : EuclideanGeometry.Sphere P := (⟨_, hai⟩ : Triangle ℝ P).circumsphere with hsABC
  have hAs : A ∈ sABC := Simplex.mem_circumsphere _ 0
  have hBs : B ∈ sABC := Simplex.mem_circumsphere _ 1
  have hCs : C ∈ sABC := Simplex.mem_circumsphere _ 2
  have hsABC_eq : (⟨_, haiCBA⟩ : Triangle ℝ P).circumsphere = sABC := by
    have hnc : ¬Collinear ℝ ({C, B, A} : Set P) := affineIndependent_iff_not_collinear_set.mp haiCBA
    exact sphere_eq_of_mem_of_mem_of_mem_of_not_collinear
      (Simplex.mem_circumsphere _ 0) (Simplex.mem_circumsphere _ 1) (Simplex.mem_circumsphere _ 2)
      hCs hBs hAs hnc
  set M : P := sABC.secondInter A (Z -ᵥ A) with hMdef
  have hMmem : M ∈ sABC := (EuclideanGeometry.Sphere.secondInter_mem _).mpr hAs
  have hMline : M ∈ line[ℝ, A, Z] := EuclideanGeometry.Sphere.secondInter_vsub_mem_affineSpan _ _ _
  -- The non-degenerate triangle `ZCE`.
  have htZCE : AffineIndependent ℝ ![Z, C, E] := affineIndependent_ZCE hai hEAC hEneC hZBC hZC
  set sZCE : EuclideanGeometry.Sphere P := (⟨_, htZCE⟩ : Triangle ℝ P).circumsphere with hsZCE
  have hZs : Z ∈ sZCE := Simplex.mem_circumsphere _ 0
  have hCs2 : C ∈ sZCE := Simplex.mem_circumsphere _ 1
  have hEs2 : E ∈ sZCE := Simplex.mem_circumsphere _ 2
  refine ⟨M, hMmem, hMline, ?_, ?_, ?_, ?_, ?_⟩
  · -- `M ≠ A`: otherwise line `AZ` is tangent to `(ABC)` at `A`; a second degeneracy
    -- (line `AZ` tangent to `(ZCE)` at `Z`) then forces `A, B, C` collinear.
    intro hMA
    have htan1 : ⟪Z -ᵥ A, A -ᵥ sABC.center⟫ = 0 := by
      have h : sABC.secondInter A (Z -ᵥ A) = A := hMA
      rwa [EuclideanGeometry.Sphere.secondInter_eq_self_iff] at h
    have hZorth : Z ∈ sABC.orthRadius A :=
      EuclideanGeometry.Sphere.mem_orthRadius_iff_inner_left.mpr htan1
    have hOnA : A ≠ sABC.center := by
      intro hDc
      have h1 : sABC.radius = 0 := by
        have h := hAs
        rw [hDc, EuclideanGeometry.Sphere.center_mem_iff] at h
        exact h
      have h2 : dist B sABC.center = 0 := by
        have h3 := EuclideanGeometry.mem_sphere.mp hBs
        rw [h1] at h3
        exact h3
      exact hAB (((dist_eq_zero.mp h2).trans hDc.symm).symm)
    have hline1 : line[ℝ, A, Z] = sABC.orthRadius A := by
      apply (AffineSubspace.eq_iff_direction_eq_of_mem (left_mem_affineSpan_pair ℝ A Z)
        (EuclideanGeometry.Sphere.self_mem_orthRadius sABC A)).mpr
      apply Submodule.eq_of_le_of_finrank_eq
      · exact AffineSubspace.direction_le (by
          rw [affineSpan_le, Set.insert_subset_iff]
          exact ⟨EuclideanGeometry.Sphere.self_mem_orthRadius sABC A,
            Set.singleton_subset_iff.mpr hZorth⟩)
      · have hfin1 : finrank ℝ (sABC.orthRadius A).direction = 1 := by
          have h := EuclideanGeometry.Sphere.finrank_orthRadius hOnA
          have h2 : finrank ℝ V = 2 := Fact.out
          rw [h2] at h
          linarith [h]
        have hfin2 : finrank ℝ (line[ℝ, A, Z]).direction = 1 := by
          rw [direction_affineSpan, vectorSpan_pair,
            finrank_span_singleton (vsub_ne_zero.mpr hZneA.symm)]
        rw [hfin1, hfin2]
    have hTanA : sABC.IsTangentAt A (line[ℝ, A, Z]) :=
      hline1 ▸ (EuclideanGeometry.Sphere.isTangentAt_orthRadius_iff_mem).mpr hAs
    -- Tangent-chord: `2•∡ZAB = 2•∡ACB`; triangle `ABZ` then gives `2•∡BZA = 2•∡BAC`.
    have htc1 : (2 : ℤ) • ∡ Z A B = (2 : ℤ) • ∡ A C B :=
      two_zsmul_oangle_tangent_chord hAs hCs hBs hTanA (right_mem_affineSpan_pair ℝ A Z)
        hZneA hAB.symm hAC.symm hBC.symm
    have hsum1 : (2 : ℤ) • ∡ B Z A = -((2 : ℤ) • ∡ A C B + (2 : ℤ) • ∡ A B C) := by
      have hs := EuclideanGeometry.oangle_add_oangle_add_oangle_eq_pi hZneA.symm hAB.symm hZB
      have hs' := congrArg ((2 : ℤ) • ·) hs
      simp only [smul_add, Real.Angle.two_zsmul_coe_pi] at hs'
      have hABZ : (2 : ℤ) • ∡ A B Z = (2 : ℤ) • ∡ A B C :=
        Collinear.two_zsmul_oangle_eq_right (collinear_insert_of_mem_affineSpan_pair hZBC)
          hZB hBC.symm
      rw [htc1, hABZ] at hs'
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact hs'
    -- The second intersection of line `ZA` with `(ZCE)`.
    set M₁ : P := sZCE.secondInter Z (A -ᵥ Z) with hM₁def
    have hM₁mem : M₁ ∈ sZCE := (EuclideanGeometry.Sphere.secondInter_mem _).mpr hZs
    have hM₁line : M₁ ∈ line[ℝ, Z, A] := EuclideanGeometry.Sphere.secondInter_vsub_mem_affineSpan _ _ _
    have hM₁neC : M₁ ≠ C := by
      intro h
      have hCline : C ∈ line[ℝ, Z, A] := h ▸ hM₁line
      have hZAC' : Z ∈ line[ℝ, C, A] :=
        (collinear_insert_of_mem_affineSpan_pair hCline).mem_affineSpan_of_mem_of_ne
          (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
          (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) hAC.symm
      rw [Set.pair_comm C A] at hZAC'
      exact hZA hZAC'
    by_cases hM₁Z : M₁ = Z
    · -- Line `ZA` tangent to `(ZCE)` at `Z`: forces `2•∡ACB = 0`.
      have htan2 : ⟪A -ᵥ Z, Z -ᵥ sZCE.center⟫ = 0 := by
        have h : sZCE.secondInter Z (A -ᵥ Z) = Z := hM₁Z
        rwa [EuclideanGeometry.Sphere.secondInter_eq_self_iff] at h
      have hAorth : A ∈ sZCE.orthRadius Z :=
        EuclideanGeometry.Sphere.mem_orthRadius_iff_inner_left.mpr htan2
      have hOnZ : Z ≠ sZCE.center := by
        intro hDc
        have h1 : sZCE.radius = 0 := by
          have h := hZs
          rw [hDc, EuclideanGeometry.Sphere.center_mem_iff] at h
          exact h
        have h2 : dist E sZCE.center = 0 := by
          have h3 := EuclideanGeometry.mem_sphere.mp hEs2
          rw [h1] at h3
          exact h3
        exact hZE.symm ((dist_eq_zero.mp h2).trans hDc.symm)
      have hline2 : line[ℝ, Z, A] = sZCE.orthRadius Z := by
        apply (AffineSubspace.eq_iff_direction_eq_of_mem (left_mem_affineSpan_pair ℝ Z A)
          (EuclideanGeometry.Sphere.self_mem_orthRadius sZCE Z)).mpr
        apply Submodule.eq_of_le_of_finrank_eq
        · exact AffineSubspace.direction_le (by
            rw [affineSpan_le, Set.insert_subset_iff]
            exact ⟨EuclideanGeometry.Sphere.self_mem_orthRadius sZCE Z,
              Set.singleton_subset_iff.mpr hAorth⟩)
        · have hfin1 : finrank ℝ (sZCE.orthRadius Z).direction = 1 := by
            have h := EuclideanGeometry.Sphere.finrank_orthRadius hOnZ
            have h2 : finrank ℝ V = 2 := Fact.out
            rw [h2] at h
            linarith [h]
          have hfin2 : finrank ℝ (line[ℝ, Z, A]).direction = 1 := by
            rw [direction_affineSpan, vectorSpan_pair,
              finrank_span_singleton (vsub_ne_zero.mpr hZneA)]
          rw [hfin1, hfin2]
      have hTanZ : sZCE.IsTangentAt Z (line[ℝ, Z, A]) :=
        hline2 ▸ (EuclideanGeometry.Sphere.isTangentAt_orthRadius_iff_mem).mpr hZs
      have htc2 : (2 : ℤ) • ∡ A Z C = (2 : ℤ) • ∡ Z E C :=
        two_zsmul_oangle_tangent_chord hZs hEs2 hCs2 hTanZ (right_mem_affineSpan_pair ℝ Z A)
          hZneA.symm hZC.symm hZE.symm hEneC
      -- Compute both sides: `2•∡AZC = 2•∡ACB + 2•∡ABC` and `2•∡ZEC = 2•∡ABC`.
      have e1 : (2 : ℤ) • ∡ A Z C = (2 : ℤ) • ∡ A C B + (2 : ℤ) • ∡ A B C := by
        have h1 : (2 : ℤ) • ∡ A Z C = (2 : ℤ) • ∡ A Z B :=
          Collinear.two_zsmul_oangle_eq_right
            ((collinear_insert_of_mem_affineSpan_pair hZBC).subset
              (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto))
            hZC.symm hZB.symm
        have h2 : (2 : ℤ) • ∡ A Z B = -((2 : ℤ) • ∡ B Z A) := by
          rw [EuclideanGeometry.oangle_rev, smul_neg]
        rw [h1, h2, hsum1, neg_neg]
      have e2 : (2 : ℤ) • ∡ Z E C = (2 : ℤ) • ∡ A B C := by
        have h1 : (2 : ℤ) • ∡ Z E C = (2 : ℤ) • ∡ F E C :=
          Collinear.two_zsmul_oangle_eq_left (collinear_insert_of_mem_affineSpan_pair hZEF)
            hZE hEF.symm
        have h2 : (2 : ℤ) • ∡ F E C = (2 : ℤ) • ∡ F B C :=
          (hcycBCEF.subset (by intro x hx; simp only [Set.mem_insert_iff,
            Set.mem_singleton_iff] at hx ⊢; tauto)).two_zsmul_oangle_eq
            hEF hEneC hFneB.symm hBC
        have h3 : (2 : ℤ) • ∡ F B C = (2 : ℤ) • ∡ A B C :=
          Collinear.two_zsmul_oangle_eq_left
            ((collinear_insert_of_mem_affineSpan_pair hFAB).subset
              (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto))
            hFneB hAB
        rw [h1, h2, h3]
      -- Conclusion: `2•∡ACB = 0`, so `A, B, C` are collinear.
      rw [e1, e2] at htc2
      have key : (2 : ℤ) • ∡ A C B = 0 := by
        rw [show (2 : ℤ) • ∡ A C B = (2 : ℤ) • ∡ A C B + (2 : ℤ) • ∡ A B C - (2 : ℤ) • ∡ A B C
          from by abel, htc2, sub_self]
      have h0 : ∡ A C B = 0 ∨ ∡ A C B = π := Real.Angle.two_zsmul_eq_zero_iff.mp key
      have hcol : Collinear ℝ ({A, C, B} : Set P) :=
        EuclideanGeometry.oangle_eq_zero_or_eq_pi_iff_collinear.mp h0
      exact (affineIndependent_iff_not_collinear_set.mp hai)
        (hcol.subset (by intro x hx; simp only [Set.mem_insert_iff,
          Set.mem_singleton_iff] at hx ⊢; tauto))
    · -- The Miquel chase: `M₁` lies on `(ABC)`, hence equals `A`, forcing `A ∈ (ZCE)`.
      -- First: `A ∉ (ZCE)`, since `(ZCE) ∩ line CE = {C, E}`.
      have hAnot : A ∉ sZCE := by
        intro hAsZCE
        have hAline : A ∈ line[ℝ, C, E] := by
          have h1 : A ∈ line[ℝ, C, A] := right_mem_affineSpan_pair ℝ C A
          rwa [line_CA_eq_line_CE_of_mem hEAC hAC hEneC] at h1
        rcases (EuclideanGeometry.Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
          hCs2 hAline).mpr hAsZCE with h2 | h2
        · exact hAC h2
        · have hE : E = sZCE.secondInter C (E -ᵥ C) := by
            rcases (EuclideanGeometry.Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
              hCs2 (right_mem_affineSpan_pair ℝ C E)).mpr hEs2 with h3 | h3
            · exact absurd h3 hEneC
            · exact h3
          exact hEneA (h2.trans hE.symm).symm
      by_cases hM₁A' : M₁ = A
      · exact hAnot (hM₁A' ▸ hM₁mem)
      · have hchase : (2 : ℤ) • ∡ C M₁ A = (2 : ℤ) • ∡ C B A := by
          have h1 : (2 : ℤ) • ∡ C M₁ A = (2 : ℤ) • ∡ C M₁ Z :=
            Collinear.two_zsmul_oangle_eq_right
              ((collinear_insert_of_mem_affineSpan_pair hM₁line).subset
                (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto))
              (Ne.symm hM₁A') (Ne.symm hM₁Z)
          have h2 : (2 : ℤ) • ∡ C M₁ Z = (2 : ℤ) • ∡ C E Z :=
            EuclideanGeometry.Sphere.two_zsmul_oangle_eq hCs2 hM₁mem hEs2 hZs hM₁neC hM₁Z hEneC hZE.symm
          have h3 : (2 : ℤ) • ∡ C E Z = (2 : ℤ) • ∡ C E F :=
            Collinear.two_zsmul_oangle_eq_right (collinear_insert_of_mem_affineSpan_pair hZEF)
              hZE hEF.symm
          have h4 : (2 : ℤ) • ∡ C E F = (2 : ℤ) • ∡ C B F :=
            (hcycBCEF.subset (by intro x hx; simp only [Set.mem_insert_iff,
              Set.mem_singleton_iff] at hx ⊢; tauto)).two_zsmul_oangle_eq
              hEneC hEF hBC hFneB.symm
          have h5 : (2 : ℤ) • ∡ C B F = (2 : ℤ) • ∡ C B A :=
            Collinear.two_zsmul_oangle_eq_right
              ((collinear_insert_of_mem_affineSpan_pair hFAB).subset
                (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto))
              hFneB hAB
          rw [h1, h2, h3, h4, h5]
        -- `M₁ ∈ (CBA) = sABC`.
        have htCM₁A : AffineIndependent ℝ ![C, M₁, A] := by
          refine affineIndependent_iff_not_collinear_set.mpr fun hcol => ?_
          have hM₁CA : M₁ ∈ line[ℝ, C, A] :=
            hcol.mem_affineSpan_of_mem_of_ne (Set.mem_insert _ _)
              (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
              (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) hAC.symm
          have hM₁CA' : M₁ ∈ line[ℝ, C, E] := by
            rwa [line_CA_eq_line_CE_of_mem hEAC hAC hEneC] at hM₁CA
          -- `M₁ ∈ (ZCE) ∩ line CE = {C, E}`.
          rcases (EuclideanGeometry.Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
            hCs2 hM₁CA').mpr hM₁mem with h | h
          · exact hM₁neC h
          · have hE : E = sZCE.secondInter C (E -ᵥ C) := by
              rcases (EuclideanGeometry.Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
                hCs2 (right_mem_affineSpan_pair ℝ C E)).mpr hEs2 with h2 | h2
              · exact absurd h2 hEneC
              · exact h2
            have hM₁E : M₁ = E := h.trans hE.symm
            have hEline : E ∈ line[ℝ, Z, A] := hM₁E ▸ hM₁line
            have hZAC' : Z ∈ line[ℝ, E, A] :=
              (collinear_insert_of_mem_affineSpan_pair hEline).mem_affineSpan_of_mem_of_ne
                (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
                (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) hEneA
            rw [line_EA_eq_line_CA_of_mem hEAC hEneA hAC, Set.pair_comm C A] at hZAC'
            exact hZA hZAC'
        have hsph : (⟨![C, M₁, A], htCM₁A⟩ : Triangle ℝ P).circumsphere = sABC :=
          (Affine.Triangle.circumsphere_eq_circumsphere_of_eq_of_eq_of_two_zsmul_oangle_eq
            (t₁ := ⟨![C, M₁, A], htCM₁A⟩) (t₂ := ⟨![C, B, A], haiCBA⟩)
            (show (0 : Fin 3) ≠ 1 by decide) (show (0 : Fin 3) ≠ 2 by decide)
            (show (1 : Fin 3) ≠ 2 by decide) rfl rfl hchase).trans hsABC_eq
        have hM₁sABC : M₁ ∈ sABC := hsph ▸ Simplex.mem_circumsphere _ 1
        -- `M₁ ∈ line AZ ∩ (ABC) = {A, M}`, so `M₁ = A`; contradiction with `A ∉ (ZCE)`.
        have hM₁line' : M₁ ∈ line[ℝ, A, Z] := by rwa [Set.pair_comm Z A] at hM₁line
        have hM₁A : M₁ = A := by
          rcases (EuclideanGeometry.Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
            hAs hM₁line').mpr hM₁sABC with h | h
          · exact h
          · exact h.trans hMA
        exact hAnot (hM₁A ▸ hM₁mem)
  · -- `M ≠ Z`: otherwise `Z ∈ (ABC) ∩ line BC = {B, C}`.
    intro hMZ
    have hZsABC : Z ∈ sABC := hMZ ▸ hMmem
    rcases (EuclideanGeometry.Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
      hBs hZBC).mpr hZsABC with h | h
    · exact hZB h
    · have hC : C = sABC.secondInter B (C -ᵥ B) := by
        rcases (EuclideanGeometry.Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
          hBs (right_mem_affineSpan_pair ℝ B C)).mpr hCs with h2 | h2
        · exact absurd h2 hBC.symm
        · exact h2
      exact hZC (h.trans hC.symm)
  · -- `M ≠ C`
    intro hMC
    have hCline : C ∈ line[ℝ, A, Z] := hMC ▸ hMline
    have hZAC' : Z ∈ line[ℝ, C, A] :=
      (collinear_insert_of_mem_affineSpan_pair hCline).mem_affineSpan_of_mem_of_ne
        (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))) hAC.symm
    rw [Set.pair_comm C A] at hZAC'
    exact hZA hZAC'
  · -- `M ≠ B`
    intro hMB
    have hBline : B ∈ line[ℝ, A, Z] := hMB ▸ hMline
    have hZAB' : Z ∈ line[ℝ, B, A] :=
      (collinear_insert_of_mem_affineSpan_pair hBline).mem_affineSpan_of_mem_of_ne
        (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))) hAB.symm
    rw [Set.pair_comm B A] at hZAB'
    exact hZnA hZAB'
  · -- `M ≠ E`
    intro hME
    have hEline : E ∈ line[ℝ, A, Z] := hME ▸ hMline
    have hZAE' : Z ∈ line[ℝ, E, A] :=
      (collinear_insert_of_mem_affineSpan_pair hEline).mem_affineSpan_of_mem_of_ne
        (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))) hEneA
    rw [line_EA_eq_line_CA_of_mem hEAC hEneA hAC, Set.pair_comm C A] at hZAE'
    exact hZA hZAE'

/-- The Miquel point lies on the circumcircle of `ZCE` (the Miquel chase). -/
theorem miquel_M_on_ZCE [Module.Oriented ℝ V (Fin 2)] {A B C D E F Z M : P}
    (hai : AffineIndependent ℝ ![A, B, C])
    (hDint : D ∈ (⟨_, hai⟩ : Triangle ℝ P).interior)
    (hbis : ∠ D A B = ∠ C A D)
    (hEw : Wbtw ℝ A E C) (hDE : ∠ A D E = ∠ B C D)
    (hFw : Wbtw ℝ A F B) (hDF : ∠ F D A = ∠ D B C)
    (hZBC : Z ∈ line[ℝ, B, C]) (hZsbtw : Sbtw ℝ B C Z)
    (hZEF : Z ∈ line[ℝ, E, F]) (hZsbtwEF : Sbtw ℝ Z E F)
    (hMmem : M ∈ (⟨_, hai⟩ : Triangle ℝ P).circumsphere) (hMline : M ∈ line[ℝ, A, Z])
    (hMA : M ≠ A) (hMZ : M ≠ Z) (hMC : M ≠ C) (hMB : M ≠ B) (hME : M ≠ E) :
    M ∈ (⟨_, affineIndependent_ZCE hai hEw.mem_affineSpan (E_ne_C hai hDint hbis hEw hDE)
      hZBC hZsbtw.ne_right.symm⟩ : Triangle ℝ P).circumsphere := by
  have hAB : A ≠ B := hai.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hAC : A ≠ C := hai.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hBC : B ≠ C := hai.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  have hEneA := E_ne_A hai hDint hDE
  have hEneC := E_ne_C hai hDint hbis hEw hDE
  have hFneB := F_ne_B hai hDint hbis hFw hDF
  have hFneA := F_ne_A hai hDint hDF
  have hEF : E ≠ F := E_ne_F hai hEw hFw hEneA hFneA
  have hZC : Z ≠ C := hZsbtw.ne_right.symm
  have hZE : Z ≠ E := hZsbtwEF.ne_left.symm
  have hFAB : F ∈ line[ℝ, A, B] := hFw.mem_affineSpan
  have hcycBCEF : EuclideanGeometry.Cospherical ({B, C, E, F} : Set P) :=
    (concyclic_BCEF hai hDint hbis hEw hDE hFw hDF).Cospherical
  set sABC : EuclideanGeometry.Sphere P := (⟨_, hai⟩ : Triangle ℝ P).circumsphere with hsABC
  have hAs : A ∈ sABC := Simplex.mem_circumsphere _ 0
  have hBs : B ∈ sABC := Simplex.mem_circumsphere _ 1
  have hCs : C ∈ sABC := Simplex.mem_circumsphere _ 2
  have htZCE : AffineIndependent ℝ ![Z, C, E] :=
    affineIndependent_ZCE hai hEw.mem_affineSpan hEneC hZBC hZC
  set sZCE : EuclideanGeometry.Sphere P := (⟨_, htZCE⟩ : Triangle ℝ P).circumsphere with hsZCE
  have hchase : (2 : ℤ) • ∡ C M Z = (2 : ℤ) • ∡ C E Z := by
    have h1 : (2 : ℤ) • ∡ C M Z = (2 : ℤ) • ∡ C M A :=
      Collinear.two_zsmul_oangle_eq_right
        ((collinear_insert_of_mem_affineSpan_pair hMline).subset
          (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto))
        hMZ.symm hMA.symm
    have h2 : (2 : ℤ) • ∡ C M A = (2 : ℤ) • ∡ C B A :=
      EuclideanGeometry.Sphere.two_zsmul_oangle_eq hCs hMmem hBs hAs hMC hMA hBC hAB.symm
    have h3 : (2 : ℤ) • ∡ C B A = (2 : ℤ) • ∡ C B F :=
      Collinear.two_zsmul_oangle_eq_right
        ((collinear_insert_of_mem_affineSpan_pair hFAB).subset
          (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto))
        hAB hFneB
    have h4 : (2 : ℤ) • ∡ C B F = (2 : ℤ) • ∡ C E F :=
      (hcycBCEF.subset (by intro x hx; simp only [Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx ⊢; tauto)).two_zsmul_oangle_eq
        hBC hFneB.symm hEneC hEF
    have h5 : (2 : ℤ) • ∡ C E F = (2 : ℤ) • ∡ C E Z :=
      Collinear.two_zsmul_oangle_eq_right
        ((collinear_insert_of_mem_affineSpan_pair hZEF).subset
          (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto))
        hEF.symm hZE
    rw [h1, h2, h3, h4, h5]
  -- The two triangles `CMZ` and `CEZ` have the same circumsphere.
  have htCMZ : AffineIndependent ℝ ![C, M, Z] := by
    refine affineIndependent_iff_not_collinear_set.mpr fun hcol => ?_
    have hMlineCZ : M ∈ line[ℝ, C, Z] :=
      hcol.mem_affineSpan_of_mem_of_ne (Set.mem_insert _ _)
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
        (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) hZC.symm
    have hMBC : M ∈ line[ℝ, B, C] := by
      have h1 : line[ℝ, C, Z] = line[ℝ, B, C] :=
        (AffineSubspace.eq_iff_direction_eq_of_mem (left_mem_affineSpan_pair ℝ C Z)
          (right_mem_affineSpan_pair ℝ B C)).mpr
          (Submodule.eq_of_le_of_finrank_eq
            (AffineSubspace.direction_le (by
              rw [affineSpan_le, Set.insert_subset_iff]
              exact ⟨right_mem_affineSpan_pair ℝ B C,
                Set.singleton_subset_iff.mpr hZBC⟩))
            (by rw [direction_affineSpan, vectorSpan_pair, direction_affineSpan, vectorSpan_pair,
                finrank_span_singleton (vsub_ne_zero.mpr hZC.symm),
                finrank_span_singleton (vsub_ne_zero.mpr hBC)]))
      rwa [h1] at hMlineCZ
    rcases (EuclideanGeometry.Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
      hBs hMBC).mpr hMmem with h | h
    · exact hMB h
    · have hC2 : C = sABC.secondInter B (C -ᵥ B) := by
        rcases (EuclideanGeometry.Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
          hBs (right_mem_affineSpan_pair ℝ B C)).mpr hCs with h2 | h2
        · exact absurd h2 hBC.symm
        · exact h2
      exact hMC (h.trans hC2.symm)
  have htCEZ : AffineIndependent ℝ ![C, E, Z] := affineIndependent_cycle htZCE
  have hsph : (⟨![C, M, Z], htCMZ⟩ : Triangle ℝ P).circumsphere =
      (⟨![C, E, Z], htCEZ⟩ : Triangle ℝ P).circumsphere :=
    Affine.Triangle.circumsphere_eq_circumsphere_of_eq_of_eq_of_two_zsmul_oangle_eq
      (show (0 : Fin 3) ≠ 1 by decide) (show (0 : Fin 3) ≠ 2 by decide)
      (show (1 : Fin 3) ≠ 2 by decide) rfl rfl hchase
  have hsZCE_eq : (⟨![C, E, Z], htCEZ⟩ : Triangle ℝ P).circumsphere = sZCE := by
    have hnc : ¬Collinear ℝ ({C, E, Z} : Set P) := affineIndependent_iff_not_collinear_set.mp htCEZ
    exact sphere_eq_of_mem_of_mem_of_mem_of_not_collinear
      (Simplex.mem_circumsphere _ 0) (Simplex.mem_circumsphere _ 1) (Simplex.mem_circumsphere _ 2)
      (Simplex.mem_circumsphere _ 1) (Simplex.mem_circumsphere _ 2) (Simplex.mem_circumsphere _ 0) hnc
  exact (hsph.trans hsZCE_eq) ▸ Simplex.mem_circumsphere _ 1

/-- The power of `Z` with respect to the circumcircle of `ABC`: `ZM · ZA = ZB · ZC`. -/
theorem miquel_M_power {A B C Z M : P}
    (hai : AffineIndependent ℝ ![A, B, C])
    (hZBC : Z ∈ line[ℝ, B, C]) (hZsbtw : Sbtw ℝ B C Z)
    (hMmem : M ∈ (⟨_, hai⟩ : Triangle ℝ P).circumsphere) (hMline : M ∈ line[ℝ, A, Z])
    (hMA : M ≠ A) :
    dist Z M * dist Z A = dist Z B * dist Z C := by
  have hBC : B ≠ C := hai.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  set sABC : EuclideanGeometry.Sphere P := (⟨_, hai⟩ : Triangle ℝ P).circumsphere with hsABC
  have hAs : A ∈ sABC := Simplex.mem_circumsphere _ 0
  have hBs : B ∈ sABC := Simplex.mem_circumsphere _ 1
  have hCs : C ∈ sABC := Simplex.mem_circumsphere _ 2
  have hOut : sABC.radius < dist Z sABC.center :=
    radius_lt_dist_center_of_sbtw_of_mem_sphere hBs hCs hBC hZBC hZsbtw
  have h1 : dist Z B * dist Z C = sABC.power Z :=
    EuclideanGeometry.Sphere.mul_dist_eq_power_of_radius_le_dist_center
      (EuclideanGeometry.Sphere.radius_nonneg_of_mem hBs) hZBC hBs hCs hOut.le
  have hMline' : Z ∈ line[ℝ, M, A] :=
    (collinear_insert_of_mem_affineSpan_pair hMline).mem_affineSpan_of_mem_of_ne
      (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))) hMA
  have h2 : dist Z M * dist Z A = sABC.power Z :=
    EuclideanGeometry.Sphere.mul_dist_eq_power_of_radius_le_dist_center
      (EuclideanGeometry.Sphere.radius_nonneg_of_mem hBs) hMline' hMmem hAs hOut.le
  rw [h2, h1]

/-- A point strictly between two points of a sphere lies strictly inside it. -/
theorem dist_center_lt_radius_of_sbtw_of_mem_sphere {s : EuclideanGeometry.Sphere P} {M Z A : P}
    (hM : M ∈ s) (hZ : Z ∈ s) (hMZ : M ≠ Z) (h : Sbtw ℝ M A Z) :
    dist A s.center < s.radius := by
  obtain ⟨t, ht, rfl⟩ := (sbtw_iff_mem_image_Ioo_and_ne.mp h).1
  have hrM : dist M s.center = s.radius := EuclideanGeometry.mem_sphere.mp hM
  have hrZ : dist Z s.center = s.radius := EuclideanGeometry.mem_sphere.mp hZ
  have hnM : ‖M -ᵥ s.center‖ = s.radius := by rw [← hrM, dist_eq_norm_vsub]
  have hnZ : ‖Z -ᵥ s.center‖ = s.radius := by rw [← hrZ, dist_eq_norm_vsub]
  have e1 : (AffineMap.lineMap M Z t) -ᵥ s.center =
      (1 - t) • (M -ᵥ s.center) + t • (Z -ᵥ s.center) := by
    rw [AffineMap.lineMap_apply, vadd_vsub_assoc, ← vsub_sub_vsub_cancel_left Z M s.center,
      ← neg_vsub_eq_vsub_rev M s.center, ← neg_vsub_eq_vsub_rev Z s.center]
    module
  have hinner : ⟪M -ᵥ s.center, Z -ᵥ s.center⟫ < s.radius ^ 2 := by
    have h1 : ‖(M -ᵥ s.center) - (Z -ᵥ s.center)‖ ^ 2 =
        2 * s.radius ^ 2 - 2 * ⟪M -ᵥ s.center, Z -ᵥ s.center⟫ := by
      rw [norm_sub_sq_real, hnM, hnZ]
      ring
    have h2 : (M -ᵥ s.center) - (Z -ᵥ s.center) = M -ᵥ Z :=
      vsub_sub_vsub_cancel_right M Z s.center
    have h3 : 0 < ‖M -ᵥ Z‖ ^ 2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (vsub_ne_zero.mpr hMZ))
    rw [h2] at h1
    nlinarith [h1, h3]
  have heq : dist (AffineMap.lineMap M Z t) s.center ^ 2 =
      (1 - t) ^ 2 * s.radius ^ 2 + t ^ 2 * s.radius ^ 2 +
        2 * (1 - t) * t * ⟪M -ᵥ s.center, Z -ᵥ s.center⟫ := by
    rw [dist_eq_norm_vsub, e1, norm_add_sq_real, norm_smul, norm_smul,
      real_inner_smul_left, inner_smul_right, hnM, hnZ,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ht.1, abs_of_pos (sub_pos.mpr ht.2)]
    ring
  have h5 : 2 * (1 - t) * t * ⟪M -ᵥ s.center, Z -ᵥ s.center⟫ <
      2 * (1 - t) * t * s.radius ^ 2 :=
    mul_lt_mul_of_pos_left hinner (mul_pos (mul_pos two_pos (sub_pos.mpr ht.2)) ht.1)
  have h7 : (1 - t) ^ 2 * s.radius ^ 2 + t ^ 2 * s.radius ^ 2 +
      2 * (1 - t) * t * s.radius ^ 2 = s.radius ^ 2 := by ring
  have h6 : dist (AffineMap.lineMap M Z t) s.center ^ 2 < s.radius ^ 2 := by
    nlinarith [heq, h5, h7]
  exact (pow_lt_pow_iff_left₀ dist_nonneg (EuclideanGeometry.Sphere.radius_nonneg_of_mem hM)
    two_ne_zero).mp h6

/-- The Miquel point lies strictly between `A` and `Z`. -/
theorem miquel_M_sbtw [Module.Oriented ℝ V (Fin 2)] {A B C E Z M : P}
    (hai : AffineIndependent ℝ ![A, B, C])
    (hacute : (⟨_, hai⟩ : Triangle ℝ P).AcuteAngled)
    (htZCE : AffineIndependent ℝ ![Z, C, E])
    (hEw : Wbtw ℝ A E C) (hEneA : E ≠ A) (hEneC : E ≠ C)
    (hZsbtw : Sbtw ℝ B C Z)
    (hMmem : M ∈ (⟨_, htZCE⟩ : Triangle ℝ P).circumsphere) (hMline : M ∈ line[ℝ, A, Z])
    (hMA : M ≠ A) (hMZ : M ≠ Z) :
    Sbtw ℝ A M Z := by
  have hAB : A ≠ B := hai.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hAC : A ≠ C := hai.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hBC : B ≠ C := hai.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  have hZC : Z ≠ C := hZsbtw.ne_right.symm
  have hZneA : Z ≠ A := by
    intro h
    apply affineIndependent_iff_not_collinear_set.mp htZCE
    rw [h]
    exact (collinear_insert_of_mem_affineSpan_pair hEw.mem_affineSpan).subset
      (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)
  set sZCE : EuclideanGeometry.Sphere P := (⟨_, htZCE⟩ : Triangle ℝ P).circumsphere with hsZCE
  have hZs : Z ∈ sZCE := Simplex.mem_circumsphere _ 0
  have hCs : C ∈ sZCE := Simplex.mem_circumsphere _ 1
  have hEs : E ∈ sZCE := Simplex.mem_circumsphere _ 2
  -- `A` lies outside `(ZCE)`.
  have hOut : sZCE.radius < dist A sZCE.center := by
    have hAEC : Sbtw ℝ A E C := ⟨hEw, hEneA, hEneC⟩
    have hAline : A ∈ line[ℝ, C, E] := mem_line_CE_of_mem_line_AC hEw.mem_affineSpan hEneC
    exact radius_lt_dist_center_of_sbtw_of_mem_sphere hCs hEs hEneC.symm hAline hAEC.symm
  -- The two secant products from `A`: `AM · AZ = AE · AC`.
  have hMline' : A ∈ line[ℝ, M, Z] :=
    (collinear_insert_of_mem_affineSpan_pair hMline).mem_affineSpan_of_mem_of_ne
      (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) hMZ
  have hprod1 : dist A M * dist A Z = sZCE.power A :=
    EuclideanGeometry.Sphere.mul_dist_eq_power_of_radius_le_dist_center
      (EuclideanGeometry.Sphere.radius_nonneg_of_mem hCs) hMline' hMmem hZs hOut.le
  have hAEC' : A ∈ line[ℝ, E, C] := by
    have h1 : A ∈ line[ℝ, C, E] := mem_line_CE_of_mem_line_AC hEw.mem_affineSpan hEneC
    rwa [Set.pair_comm C E] at h1
  have hprod2 : dist A E * dist A C = sZCE.power A :=
    EuclideanGeometry.Sphere.mul_dist_eq_power_of_radius_le_dist_center
      (EuclideanGeometry.Sphere.radius_nonneg_of_mem hCs) hAEC' hEs hCs hOut.le
  have hAM : dist A M * dist A Z = dist A E * dist A C := by rw [hprod1, hprod2]
  -- `AZ > AC` because the angle `∠ACZ` is obtuse (it is `π − ∠ACB` and the triangle is acute).
  have hAZ : dist A C < dist A Z := by
    have hacuteC : ∠ A C B < π / 2 := by
      have h3 := (Affine.Triangle.acuteAngled_iff_angle_lt.mp hacute).2.1
      rw [EuclideanGeometry.angle_comm] at h3
      exact h3
    have hCpos : 0 < Real.cos (∠ A C B) :=
      Real.cos_pos_of_mem_Ioo ⟨by
        have h1 : 0 < ∠ A C B := (EuclideanGeometry.angle_nonneg A C B).lt_of_ne'
          (EuclideanGeometry.angle_ne_zero_of_not_collinear
            (not_collinear_swap23 (affineIndependent_iff_not_collinear_set.mp hai)))
        linarith [Real.pi_pos], hacuteC⟩
    have hACZ : ∡ A C Z = ∡ A C B + π := by
      have h1 : ∡ B C Z = π := Sbtw.oangle₁₂₃_eq_pi hZsbtw
      have h2 : ∡ A C B + ∡ B C Z = ∡ A C Z :=
        EuclideanGeometry.oangle_add hAC hBC hZC
      rw [h1] at h2
      exact h2.symm
    have hcos : Real.cos (∠ A C Z) = -Real.cos (∠ A C B) := by
      have h1 : Real.Angle.cos (∡ A C Z) = Real.cos (∠ A C Z) :=
        EuclideanGeometry.cos_oangle_eq_cos_angle hAC hZC
      have h4 : Real.Angle.cos (∡ A C B) = Real.cos (∠ A C B) :=
        EuclideanGeometry.cos_oangle_eq_cos_angle hAC hBC
      rw [← h1, hACZ, Real.Angle.cos_add_pi, h4]
    have hloc := EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle
      A C Z
    rw [hcos] at hloc
    have hCZ : 0 < dist Z C := dist_pos.mpr hZC
    have hACpos : 0 < dist A C := dist_pos.mpr hAC
    have hsq : dist A C ^ 2 < dist A Z ^ 2 := by
      nlinarith [hloc, hCpos, hCZ, hACpos, mul_pos hCZ hCpos, mul_pos hACpos (mul_pos hCZ hCpos)]
    exact (pow_lt_pow_iff_left₀ dist_nonneg dist_nonneg two_ne_zero).mp hsq
  -- Trichotomy on the line `AZ`.
  have hcol : Collinear ℝ ({A, M, Z} : Set P) :=
    (collinear_insert_of_mem_affineSpan_pair hMline).subset
      (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)
  rcases hcol.wbtw_or_wbtw_or_wbtw with hw | hw | hw
  · exact ⟨hw, hMA, hMZ⟩
  · -- `Z` between `M` and `A`: then `AM > AZ`, contradicting `AM · AZ = AE · AC < AZ²`.
    exfalso
    have hgt : dist A Z < dist A M := by
      have h1 : dist M Z + dist Z A = dist M A := hw.dist_add_dist
      have h2 : 0 < dist Z M := dist_pos.mpr hMZ.symm
      have h3 : dist A M = dist A Z + dist Z M := by
        have e1 : dist M A = dist A M := dist_comm M A
        have e2 : dist M Z = dist Z M := dist_comm M Z
        have e3 : dist Z A = dist A Z := dist_comm Z A
        linarith [h1]
      linarith [h3, h2]
    have hAZpos : 0 < dist A Z := dist_pos.mpr hZneA.symm
    have hAEle : dist A E ≤ dist A C := by
      have h1 : dist A E + dist E C = dist A C := hEw.dist_add_dist
      have h2 : 0 ≤ dist E C := dist_nonneg
      linarith [h1]
    have h1 : dist A Z * dist A Z < dist A M * dist A Z :=
      mul_lt_mul_of_pos_right hgt hAZpos
    have h2 : dist A C * dist A C < dist A Z * dist A Z :=
      mul_lt_mul hAZ hAZ.le (dist_pos.mpr hAC) dist_nonneg
    have h3 : dist A E * dist A C ≤ dist A C * dist A C :=
      mul_le_mul_of_nonneg_right hAEle dist_nonneg
    nlinarith [hAM, h1, h2, h3]
  · -- `A` between `M` and `Z`: then `A` lies strictly inside `(ZCE)`, contradicting `hOut`.
    exfalso
    have hin : dist A sZCE.center < sZCE.radius :=
      dist_center_lt_radius_of_sbtw_of_mem_sphere hMmem hZs hMZ
        (Sbtw.symm ⟨hw, hZneA.symm, hMA.symm⟩)
    linarith [hOut, hin]

/-- The points `B, X, M, E` are concyclic (Kafi's claim): the chase gives
`2•∡EMB = 2•∡EXB`, using that `M ∈ (ABC) ∩ (ZCE)` and that `BXC` is isosceles. -/
theorem concyclic_BXME [Module.Oriented ℝ V (Fin 2)] {A B C D E F X Z M : P}
    (hai : AffineIndependent ℝ ![A, B, C])
    (hDint : D ∈ (⟨_, hai⟩ : Triangle ℝ P).interior)
    (hbis : ∠ D A B = ∠ C A D)
    (hEw : Wbtw ℝ A E C) (hDE : ∠ A D E = ∠ B C D)
    (hFw : Wbtw ℝ A F B) (hDF : ∠ F D A = ∠ D B C)
    (hX : X ∈ line[ℝ, A, C]) (hXCB : dist C X = dist B X)
    (hEXD : AffineIndependent ℝ ![E, X, D])
    (hZBC : Z ∈ line[ℝ, B, C]) (hZsbtw : Sbtw ℝ B C Z)
    (hZEF : Z ∈ line[ℝ, E, F]) (hZsbtwEF : Sbtw ℝ Z E F)
    (hMmem : M ∈ (⟨_, hai⟩ : Triangle ℝ P).circumsphere)
    (hMmemZCE : M ∈ (⟨_, affineIndependent_ZCE hai hEw.mem_affineSpan
      (E_ne_C hai hDint hbis hEw hDE) hZBC hZsbtw.ne_right.symm⟩ : Triangle ℝ P).circumsphere)
    (hMline : M ∈ line[ℝ, A, Z])
    (hMA : M ≠ A) (hMZ : M ≠ Z) (hMC : M ≠ C) (hMB : M ≠ B) (hME : M ≠ E) :
    EuclideanGeometry.Cospherical ({E, M, X, B} : Set P) := by
  have hAB : A ≠ B := hai.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hAC : A ≠ C := hai.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hBC : B ≠ C := hai.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  have hEneC := E_ne_C hai hDint hbis hEw hDE
  have hZC : Z ≠ C := hZsbtw.ne_right.symm
  have hEX : E ≠ X := hEXD.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hCX : C ≠ X := by
    intro h
    rw [← h, dist_self] at hXCB
    exact hBC (dist_eq_zero.mp hXCB.symm)
  have hBX : B ≠ X := by
    intro h
    rw [← h, dist_self] at hXCB
    exact hBC.symm (dist_eq_zero.mp hXCB)
  have hXBC : dist X B = dist X C := by
    rw [dist_comm X B, hXCB.symm, dist_comm X C]
  set sABC : EuclideanGeometry.Sphere P := (⟨_, hai⟩ : Triangle ℝ P).circumsphere with hsABC
  have hAs : A ∈ sABC := Simplex.mem_circumsphere _ 0
  have hBs : B ∈ sABC := Simplex.mem_circumsphere _ 1
  have hCs : C ∈ sABC := Simplex.mem_circumsphere _ 2
  have htZCE : AffineIndependent ℝ ![Z, C, E] :=
    affineIndependent_ZCE hai hEw.mem_affineSpan hEneC hZBC hZC
  set sZCE : EuclideanGeometry.Sphere P := (⟨_, htZCE⟩ : Triangle ℝ P).circumsphere with hsZCE
  have hZs2 : Z ∈ sZCE := Simplex.mem_circumsphere _ 0
  have hCs2 : C ∈ sZCE := Simplex.mem_circumsphere _ 1
  have hEs2 : E ∈ sZCE := Simplex.mem_circumsphere _ 2
  -- The two sides of the angle equality.
  have e1 : (2 : ℤ) • ∡ E M B = (2 : ℤ) • ∡ A C B + (2 : ℤ) • ∡ A C B := by
    have h6 : (2 : ℤ) • ∡ E M B = (2 : ℤ) • ∡ E M A + (2 : ℤ) • ∡ A M B := by
      rw [← EuclideanGeometry.oangle_add hME.symm hMA.symm hMB.symm, smul_add]
    have h1 : (2 : ℤ) • ∡ E M A = (2 : ℤ) • ∡ E M Z :=
      Collinear.two_zsmul_oangle_eq_right
        ((collinear_insert_of_mem_affineSpan_pair hMline).subset
          (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto))
        hMA.symm hMZ.symm
    have h2 : (2 : ℤ) • ∡ E M Z = (2 : ℤ) • ∡ E C Z :=
      EuclideanGeometry.Sphere.two_zsmul_oangle_eq hEs2 hMmemZCE hCs2 hZs2 hME hMZ hEneC.symm hZC.symm
    have h3 : (2 : ℤ) • ∡ E C Z = (2 : ℤ) • ∡ A C Z :=
      Collinear.two_zsmul_oangle_eq_left
        (collinear_insert_of_mem_affineSpan_pair (Set.pair_comm A C ▸ hEw.mem_affineSpan))
        hEneC hAC
    have h4 : (2 : ℤ) • ∡ A C Z = (2 : ℤ) • ∡ A C B :=
      Collinear.two_zsmul_oangle_eq_right
        ((collinear_insert_of_mem_affineSpan_pair hZBC).subset
          (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto))
        hZC hBC
    have h5 : (2 : ℤ) • ∡ A M B = (2 : ℤ) • ∡ A C B :=
      EuclideanGeometry.Sphere.two_zsmul_oangle_eq hAs hMmem hCs hBs hMA hMB hAC.symm hBC.symm
    rw [h6, h1, h2, h3, h4, h5]
  have e2 : (2 : ℤ) • ∡ E X B = (2 : ℤ) • ∡ A C B + (2 : ℤ) • ∡ A C B := by
    have hcolEXC : Collinear ℝ ({E, X, C} : Set P) :=
      (collinear_insert_insert_of_mem_affineSpan_pair hEw.mem_affineSpan hX).subset
        (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)
    have h1 : (2 : ℤ) • ∡ E X B = (2 : ℤ) • ∡ C X B :=
      Collinear.two_zsmul_oangle_eq_left hcolEXC hEX hCX
    have h2 : (2 : ℤ) • ∡ X B C = (2 : ℤ) • ∡ B C X :=
      congrArg ((2 : ℤ) • ·) (EuclideanGeometry.oangle_eq_oangle_of_dist_eq hXBC)
    have hcolXCA : Collinear ℝ ({X, C, A} : Set P) :=
      (collinear_insert_of_mem_affineSpan_pair hX).subset
        (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)
    have h4 : (2 : ℤ) • ∡ B C X = (2 : ℤ) • ∡ B C A :=
      Collinear.two_zsmul_oangle_eq_right hcolXCA hCX.symm hAC
    have h5 : (2 : ℤ) • ∡ B C A = -((2 : ℤ) • ∡ A C B) := by
      rw [EuclideanGeometry.oangle_rev, smul_neg]
    have h3 : (2 : ℤ) • ∡ C X B + ((2 : ℤ) • ∡ X B C + (2 : ℤ) • ∡ B C X) = 0 := by
      have hs := EuclideanGeometry.oangle_add_oangle_add_oangle_eq_pi hCX.symm hBX hBC.symm
      have h := congrArg ((2 : ℤ) • ·) hs
      simp only [smul_add, Real.Angle.two_zsmul_coe_pi] at h
      rw [add_assoc] at h
      exact h
    rw [h2, h4, h5] at h3
    have h3fin : (2 : ℤ) • ∡ C X B = -(-((2 : ℤ) • ∡ A C B) + -((2 : ℤ) • ∡ A C B)) := by
      rw [eq_neg_iff_add_eq_zero]
      exact h3
    rw [h1, h3fin, neg_add, neg_neg]
  have hchase : (2 : ℤ) • ∡ E M B = (2 : ℤ) • ∡ E X B := e1.trans e2.symm
  rcases EuclideanGeometry.cospherical_or_collinear_of_two_zsmul_oangle_eq hchase with h | h
  · exact h
  · -- The four points are not collinear: `X` would lie on line `EB ∩ line AC = {E}`.
    exfalso
    have hEB : E ≠ B := by
      intro hEB'
      exact (not_mem_line_AC_of_mem_line_BC hai (left_mem_affineSpan_pair ℝ B C) hBC)
        (hEB' ▸ hEw.mem_affineSpan)
    have hXline : X ∈ line[ℝ, E, B] :=
      h.mem_affineSpan_of_mem_of_ne (Set.mem_insert _ _)
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
          (Set.mem_singleton _))))
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))) hEB
    have hBline : B ∈ line[ℝ, X, E] :=
      (collinear_insert_of_mem_affineSpan_pair hXline).mem_affineSpan_of_mem_of_ne
        (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))) hEX.symm
    have hle : line[ℝ, X, E] ≤ line[ℝ, A, C] := by
      rw [affineSpan_le, Set.insert_subset_iff]
      exact ⟨hX, Set.singleton_subset_iff.mpr hEw.mem_affineSpan⟩
    exact (not_mem_line_AC_of_mem_line_BC hai (left_mem_affineSpan_pair ℝ B C) hBC) (hle hBline)

/-- The intersection `R` of lines `AC` and `BM` lies strictly between `A` and `C` and
strictly between `M` and `B`. -/
theorem R_exists [Module.Oriented ℝ V (Fin 2)] {A B C Z M : P}
    (hai : AffineIndependent ℝ ![A, B, C])
    (hZBC : Z ∈ line[ℝ, B, C]) (hZsbtw : Sbtw ℝ B C Z)
    (hMsbtw : Sbtw ℝ A M Z)
    (hMmem : M ∈ (⟨_, hai⟩ : Triangle ℝ P).circumsphere)
    (hMA : M ≠ A) (hMC : M ≠ C) (hMB : M ≠ B) :
    ∃ R : P, R ∈ line[ℝ, A, C] ∧ Sbtw ℝ A R C ∧ Sbtw ℝ M R B := by
  have hAB : A ≠ B := hai.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hAC : A ≠ C := hai.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hBC : B ≠ C := hai.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  have hZC : Z ≠ C := hZsbtw.ne_right.symm
  have hZB : Z ≠ B := hZsbtw.left_ne_right.symm
  have hZA : Z ∉ line[ℝ, A, C] := not_mem_line_AC_of_mem_line_BC hai hZBC hZC
  have hBnAC : B ∉ line[ℝ, A, C] :=
    not_mem_line_AC_of_mem_line_BC hai (left_mem_affineSpan_pair ℝ B C) hBC
  set sABC : EuclideanGeometry.Sphere P := (⟨_, hai⟩ : Triangle ℝ P).circumsphere with hsABC
  have hAs : A ∈ sABC := Simplex.mem_circumsphere _ 0
  have hBs : B ∈ sABC := Simplex.mem_circumsphere _ 1
  have hCs : C ∈ sABC := Simplex.mem_circumsphere _ 2
  -- `M` and `B` are on opposite sides of line `AC` (via `Z`).
  have hMZside : (line[ℝ, A, C]).SSameSide M Z := by
    obtain ⟨t, ht, rfl⟩ := (sbtw_iff_mem_image_Ioo_and_ne.mp hMsbtw).1
    exact AffineSubspace.sSameSide_lineMap_left (left_mem_affineSpan_pair ℝ A C) hZA ht.1
  have hBZopp : (line[ℝ, A, C]).SOppSide B Z :=
    ⟨AffineSubspace.wOppSide_iff_exists_wbtw.2 ⟨C, right_mem_affineSpan_pair ℝ A C, hZsbtw.wbtw⟩,
      hBnAC, hZA⟩
  have hMBopp : (line[ℝ, A, C]).SOppSide M B :=
    (hBZopp.trans_sSameSide hMZside.symm).symm
  obtain ⟨R, hRline, hRMB⟩ := hMBopp.exists_sbtw
  refine ⟨R, hRline, ?_, hRMB⟩
  -- For `Sbtw A R C`, work on line `BM`: `A` and `C` are on opposite sides of it.
  have hAnBM : A ∉ line[ℝ, B, M] := by
    intro h
    have hMline2 : M ∈ line[ℝ, A, B] :=
      (collinear_insert_of_mem_affineSpan_pair h).mem_affineSpan_of_mem_of_ne
        (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))) hAB
    rcases (EuclideanGeometry.Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
      hAs hMline2).mpr hMmem with h2 | h2
    · exact hMA h2
    · have hB2 : B = sABC.secondInter A (B -ᵥ A) := by
        rcases (EuclideanGeometry.Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
          hAs (right_mem_affineSpan_pair ℝ A B)).mpr hBs with h3 | h3
        · exact absurd h3 hAB.symm
        · exact h3
      exact hMB (h2.trans hB2.symm)
  have hZnBM : Z ∉ line[ℝ, B, M] := by
    intro h
    have hMline2 : M ∈ line[ℝ, Z, B] :=
      (collinear_insert_of_mem_affineSpan_pair h).mem_affineSpan_of_mem_of_ne
        (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))) hZB
    have hle : line[ℝ, Z, B] ≤ line[ℝ, B, C] := by
      rw [affineSpan_le, Set.insert_subset_iff]
      exact ⟨hZBC, Set.singleton_subset_iff.mpr (left_mem_affineSpan_pair ℝ B C)⟩
    have hMBC : M ∈ line[ℝ, B, C] := hle hMline2
    rcases (EuclideanGeometry.Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
      hBs hMBC).mpr hMmem with h2 | h2
    · exact hMB h2
    · have hC2 : C = sABC.secondInter B (C -ᵥ B) := by
        rcases (EuclideanGeometry.Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
          hBs (right_mem_affineSpan_pair ℝ B C)).mpr hCs with h3 | h3
        · exact absurd h3 hBC.symm
        · exact h3
      exact hMC (h2.trans hC2.symm)
  have hAZopp : (line[ℝ, B, M]).SOppSide A Z :=
    ⟨AffineSubspace.wOppSide_iff_exists_wbtw.2 ⟨M, right_mem_affineSpan_pair ℝ B M, hMsbtw.wbtw⟩,
      hAnBM, hZnBM⟩
  have hZCside : (line[ℝ, B, M]).SSameSide Z C := by
    obtain ⟨t, ht, rfl⟩ := (sbtw_iff_mem_image_Ioo_and_ne.mp hZsbtw).1
    exact (AffineSubspace.sSameSide_lineMap_left (left_mem_affineSpan_pair ℝ B M) hZnBM ht.1).symm
  have hACopp : (line[ℝ, B, M]).SOppSide A C := hAZopp.trans_sSameSide hZCside
  obtain ⟨R', hR'line, hR'AC⟩ := hACopp.exists_sbtw
  -- The two intersection points coincide.
  have hR'eq : R' = R := by
    by_contra hne
    have hR'ACline : R' ∈ line[ℝ, A, C] := hR'AC.wbtw.mem_affineSpan
    have hRBM : R ∈ line[ℝ, B, M] := by
      have h1 : R ∈ line[ℝ, M, B] := hRMB.wbtw.mem_affineSpan
      rwa [Set.pair_comm M B] at h1
    have hRR' : finrank ℝ (line[ℝ, R', R]).direction = 1 := by
      rw [direction_affineSpan, vectorSpan_pair, finrank_span_singleton (vsub_ne_zero.mpr hne)]
    have e1 : line[ℝ, R', R] = line[ℝ, A, C] :=
      (AffineSubspace.eq_iff_direction_eq_of_mem (left_mem_affineSpan_pair ℝ R' R)
        hR'ACline).mpr
        (Submodule.eq_of_le_of_finrank_eq
          (AffineSubspace.direction_le (by
            rw [affineSpan_le, Set.insert_subset_iff]
            exact ⟨hR'ACline, Set.singleton_subset_iff.mpr hRline⟩))
          (by rw [hRR', direction_affineSpan, vectorSpan_pair,
            finrank_span_singleton (vsub_ne_zero.mpr hAC)]))
    have e2 : line[ℝ, R', R] = line[ℝ, B, M] :=
      (AffineSubspace.eq_iff_direction_eq_of_mem (left_mem_affineSpan_pair ℝ R' R)
        hR'line).mpr
        (Submodule.eq_of_le_of_finrank_eq
          (AffineSubspace.direction_le (by
            rw [affineSpan_le, Set.insert_subset_iff]
            exact ⟨hR'line, Set.singleton_subset_iff.mpr hRBM⟩))
          (by rw [hRR', direction_affineSpan, vectorSpan_pair,
            finrank_span_singleton (vsub_ne_zero.mpr hMB.symm)]))
    have hBmem : B ∈ line[ℝ, A, C] := by
      have h1 : B ∈ line[ℝ, B, M] := left_mem_affineSpan_pair ℝ B M
      rw [← e2, e1] at h1
      exact h1
    exact hBnAC hBmem
  exact hR'eq ▸ hR'AC

/-- The second intersection `N` of line `DR` with the circle `(ACD)`: it lies on `(DEX)`
(Kafi's radical-axis claim, via the product chain through the circles `(ACD)`, `(ABC)`,
`(BXME)`, `(DEX)`), and on `(BDM)` when `B, D, M` are not collinear. -/
theorem N_facts [Module.Oriented ℝ V (Fin 2)] {A B C D E F X Z M R : P}
    (hai : AffineIndependent ℝ ![A, B, C])
    (hDint : D ∈ (⟨_, hai⟩ : Triangle ℝ P).interior)
    (hbis : ∠ D A B = ∠ C A D)
    (hEw : Wbtw ℝ A E C) (hDE : ∠ A D E = ∠ B C D)
    (hFw : Wbtw ℝ A F B) (hDF : ∠ F D A = ∠ D B C)
    (hX : X ∈ line[ℝ, A, C]) (hXCB : dist C X = dist B X)
    (hEXD : AffineIndependent ℝ ![E, X, D])
    (haiADC : AffineIndependent ℝ ![A, D, C])
    (hZBC : Z ∈ line[ℝ, B, C]) (hZsbtw : Sbtw ℝ B C Z)
    (hZEF : Z ∈ line[ℝ, E, F]) (hZsbtwEF : Sbtw ℝ Z E F)
    (hMmem : M ∈ (⟨_, hai⟩ : Triangle ℝ P).circumsphere)
    (hMline : M ∈ line[ℝ, A, Z])
    (hMA : M ≠ A) (hMZ : M ≠ Z) (hMC : M ≠ C) (hMB : M ≠ B) (hME : M ≠ E)
    (hcycBXME : EuclideanGeometry.Cospherical ({E, M, X, B} : Set P))
    (hRline : R ∈ line[ℝ, A, C]) (hRAC : Sbtw ℝ A R C) (hRMB : Sbtw ℝ M R B) :
    ∃ N : P, N ∈ (⟨_, haiADC⟩ : Triangle ℝ P).circumsphere ∧
      N ∈ (⟨_, hEXD⟩ : Triangle ℝ P).circumsphere ∧
      N ∈ line[ℝ, D, R] ∧ Sbtw ℝ D R N ∧ N ≠ D ∧ N ≠ R ∧
      dist R N * dist R D = dist R A * dist R C ∧
      dist R A * dist R C = dist R M * dist R B ∧
      dist R M * dist R B = dist R E * dist R X ∧
      (∀ hnc : ¬Collinear ℝ ({B, D, M} : Set P),
        N ∈ (⟨_, affineIndependent_iff_not_collinear_set.mpr hnc⟩ : Triangle ℝ P).circumsphere) := by
  have hAB : A ≠ B := hai.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hAC : A ≠ C := hai.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hBC : B ≠ C := hai.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  have hEX : E ≠ X := hEXD.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hCX : C ≠ X := by
    intro h
    rw [← h, dist_self] at hXCB
    exact hBC (dist_eq_zero.mp hXCB.symm)
  have hBX : B ≠ X := by
    intro h
    rw [← h, dist_self] at hXCB
    exact hBC.symm (dist_eq_zero.mp hXCB)
  have hEB : E ≠ B := by
    intro hEB'
    exact (not_mem_line_AC_of_mem_line_BC hai (left_mem_affineSpan_pair ℝ B C) hBC)
      (hEB' ▸ hEw.mem_affineSpan)
  have hEAC : E ∈ line[ℝ, A, C] := hEw.mem_affineSpan
  have hBnAC : B ∉ line[ℝ, A, C] :=
    not_mem_line_AC_of_mem_line_BC hai (left_mem_affineSpan_pair ℝ B C) hBC
  have hDnAC : D ∉ line[ℝ, A, C] := by
    have hai_BCA : AffineIndependent ℝ ![B, C, A] := affineIndependent_cycle hai
    have h := not_mem_line_of_mem_interior hai_BCA (mem_interior_cycle hai hai_BCA hDint)
    rwa [Set.pair_comm C A] at h
  -- The five circles and their membership facts.
  set sABC : EuclideanGeometry.Sphere P := (⟨_, hai⟩ : Triangle ℝ P).circumsphere with hsABC
  have hAs : A ∈ sABC := Simplex.mem_circumsphere _ 0
  have hBs : B ∈ sABC := Simplex.mem_circumsphere _ 1
  have hCs : C ∈ sABC := Simplex.mem_circumsphere _ 2
  set sACD : EuclideanGeometry.Sphere P := (⟨_, haiADC⟩ : Triangle ℝ P).circumsphere with hsACD
  have hAs2 : A ∈ sACD := Simplex.mem_circumsphere _ 0
  have hDs : D ∈ sACD := Simplex.mem_circumsphere _ 1
  have hCs2 : C ∈ sACD := Simplex.mem_circumsphere _ 2
  set sDEX : EuclideanGeometry.Sphere P := (⟨_, hEXD⟩ : Triangle ℝ P).circumsphere with hsDEX
  have hEs3 : E ∈ sDEX := Simplex.mem_circumsphere _ 0
  have hXs3 : X ∈ sDEX := Simplex.mem_circumsphere _ 1
  have hDs3 : D ∈ sDEX := Simplex.mem_circumsphere _ 2
  -- The circle `(BXE)` contains `M`.
  have htEXB : AffineIndependent ℝ ![E, X, B] := by
    refine affineIndependent_iff_not_collinear_set.mpr fun hcol => ?_
    have hBline : B ∈ line[ℝ, E, X] :=
      hcol.mem_affineSpan_of_mem_of_ne (Set.mem_insert _ _)
        (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))) hEX
    have hle : line[ℝ, E, X] ≤ line[ℝ, A, C] := by
      rw [affineSpan_le, Set.insert_subset_iff]
      exact ⟨hEAC, Set.singleton_subset_iff.mpr hX⟩
    exact hBnAC (hle hBline)
  set sBXE : EuclideanGeometry.Sphere P := (⟨_, htEXB⟩ : Triangle ℝ P).circumsphere with hsBXE
  have hEs4 : E ∈ sBXE := Simplex.mem_circumsphere _ 0
  have hXs4 : X ∈ sBXE := Simplex.mem_circumsphere _ 1
  have hBs4 : B ∈ sBXE := Simplex.mem_circumsphere _ 2
  have hMs4 : M ∈ sBXE := by
    obtain ⟨s₀, hs₀⟩ := EuclideanGeometry.cospherical_iff_exists_sphere.mp hcycBXME
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff] at hs₀
    obtain ⟨hEs₀, hMs₀, hXs₀, hBs₀⟩ := hs₀
    have h := sphere_eq_of_mem_of_mem_of_mem_of_not_collinear hEs₀ hXs₀ hBs₀ hEs4 hXs4 hBs4
      (affineIndependent_iff_not_collinear_set.mp htEXB)
    exact h ▸ hMs₀
  -- `R` strictly inside the circles `(ACD)` and `(BXE)`.
  have hRin1 : dist R sACD.center < sACD.radius :=
    dist_center_lt_radius_of_sbtw_of_mem_sphere hAs2 hCs2 hAC hRAC
  have hRin2 : dist R sBXE.center < sBXE.radius :=
    dist_center_lt_radius_of_sbtw_of_mem_sphere hMs4 hBs4 hMB hRMB
  -- Line memberships of `R`.
  have hRMB' : R ∈ line[ℝ, M, B] := hRMB.wbtw.mem_affineSpan
  have hREX : R ∈ line[ℝ, E, X] := by
    have h1 : line[ℝ, E, X] = line[ℝ, A, C] :=
      (AffineSubspace.eq_iff_direction_eq_of_mem (left_mem_affineSpan_pair ℝ E X) hEAC).mpr
        (Submodule.eq_of_le_of_finrank_eq
          (AffineSubspace.direction_le (by
            rw [affineSpan_le, Set.insert_subset_iff]
            exact ⟨hEAC, Set.singleton_subset_iff.mpr hX⟩))
          (by rw [direction_affineSpan, vectorSpan_pair, direction_affineSpan, vectorSpan_pair,
              finrank_span_singleton (vsub_ne_zero.mpr hEX),
              finrank_span_singleton (vsub_ne_zero.mpr hAC)]))
    rwa [← h1] at hRline
  -- `N`, the second intersection of line `DR` with `(ACD)`.
  set N : P := sACD.secondInter D (R -ᵥ D) with hNdef
  have hNmem : N ∈ sACD := (EuclideanGeometry.Sphere.secondInter_mem _).mpr hDs
  have hNline : N ∈ line[ℝ, D, R] := EuclideanGeometry.Sphere.secondInter_vsub_mem_affineSpan _ _ _
  have hDRN : Sbtw ℝ D R N := EuclideanGeometry.Sphere.sbtw_secondInter hDs hRin1
  have hRDN : R ∈ line[ℝ, D, N] := hDRN.wbtw.mem_affineSpan
  -- The product chain (all as absolute powers).
  have hp1 : dist R N * dist R D = |sACD.power R| :=
    EuclideanGeometry.Sphere.mul_dist_eq_abs_power (Set.pair_comm D N ▸ hRDN) hNmem hDs
  have hp2 : dist R A * dist R C = |sACD.power R| :=
    EuclideanGeometry.Sphere.mul_dist_eq_abs_power hRline hAs2 hCs2
  have hp3 : dist R A * dist R C = |sABC.power R| :=
    EuclideanGeometry.Sphere.mul_dist_eq_abs_power hRline hAs hCs
  have hp4 : dist R M * dist R B = |sABC.power R| :=
    EuclideanGeometry.Sphere.mul_dist_eq_abs_power hRMB' hMmem hBs
  have hp5 : dist R M * dist R B = |sBXE.power R| :=
    EuclideanGeometry.Sphere.mul_dist_eq_abs_power hRMB' hMs4 hBs4
  have hp6 : dist R E * dist R X = |sBXE.power R| :=
    EuclideanGeometry.Sphere.mul_dist_eq_abs_power hREX hEs4 hXs4
  have hp7 : dist R E * dist R X = |sDEX.power R| :=
    EuclideanGeometry.Sphere.mul_dist_eq_abs_power hREX hEs3 hXs3
  have hc1 : dist R N * dist R D = dist R A * dist R C := by rw [hp1, hp2]
  have hc2 : dist R A * dist R C = dist R M * dist R B := by rw [hp3, hp4]
  have hc3 : dist R M * dist R B = dist R E * dist R X := by rw [hp5, hp6]
  have hc4 : dist R N * dist R D = dist R E * dist R X := hc1.trans (hc2.trans hc3)
  -- `R ≠ E` and `R ≠ X` (both via the circle count on `(BXE)`).
  have hRE : R ≠ E := by
    intro h
    have hEline : E ∈ line[ℝ, M, B] := h ▸ hRMB'
    rcases (EuclideanGeometry.Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
      hMs4 hEline).mpr hEs4 with h3 | h3
    · exact hME h3.symm
    · have hB3 : B = sBXE.secondInter M (B -ᵥ M) := by
        rcases (EuclideanGeometry.Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
          hMs4 (right_mem_affineSpan_pair ℝ M B)).mpr hBs4 with h4 | h4
        · exact absurd h4 hMB.symm
        · exact h4
      exact hEB (h3.trans hB3.symm)
  have hRX : R ≠ X := by
    intro h
    have hXline : X ∈ line[ℝ, M, B] := h ▸ hRMB'
    rcases (EuclideanGeometry.Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
      hMs4 hXline).mpr hXs4 with h3 | h3
    · have hMline2 : M ∈ line[ℝ, A, C] := h3 ▸ hX
      rcases (EuclideanGeometry.Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
        hAs hMline2).mpr hMmem with h4 | h4
      · exact hMA h4
      · have hC4 : C = sABC.secondInter A (C -ᵥ A) := by
          rcases (EuclideanGeometry.Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
            hAs (right_mem_affineSpan_pair ℝ A C)).mpr hCs with h5 | h5
          · exact absurd h5 hAC.symm
          · exact h5
        exact hMC (h4.trans hC4.symm)
    · have hB3 : B = sBXE.secondInter M (B -ᵥ M) := by
        rcases (EuclideanGeometry.Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
          hMs4 (right_mem_affineSpan_pair ℝ M B)).mpr hBs4 with h4 | h4
        · exact absurd h4 hMB.symm
        · exact h4
      exact hBX (h3.trans hB3.symm).symm
  -- The two `π`-angle facts at `R`.
  have hangNRD : ∠ N R D = π := by
    rw [EuclideanGeometry.angle_comm]
    exact EuclideanGeometry.angle_eq_pi_iff_sbtw.mpr hDRN
  have hangERX : ∠ E R X = π := by
    have hW : Wbtw ℝ E R X := by
      have hXER : X ∈ line[ℝ, E, R] :=
        (collinear_insert_of_mem_affineSpan_pair hREX).mem_affineSpan_of_mem_of_ne
          (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) (Set.mem_insert _ _)
          (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))) hRE.symm
      have h2 : X = sBXE.secondInter E (R -ᵥ E) := by
        rcases (EuclideanGeometry.Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
          hEs4 hXER).mpr hXs4 with h3 | h3
        · exact absurd h3 hEX.symm
        · exact h3
      rw [h2]
      exact EuclideanGeometry.Sphere.wbtw_secondInter hEs4 hRin2.le
    exact EuclideanGeometry.angle_eq_pi_iff_sbtw.mpr ⟨hW, hRE, hRX⟩
  have hangMRB : ∠ M R B = π := EuclideanGeometry.angle_eq_pi_iff_sbtw.mpr hRMB
  -- `N, R, E` are not collinear (else `D` would lie on line `AC`).
  have hncNRE : ¬Collinear ℝ ({N, R, E} : Set P) := by
    intro hcol
    have hEline : E ∈ line[ℝ, N, R] :=
      hcol.mem_affineSpan_of_mem_of_ne (Set.mem_insert _ _)
        (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))) hDRN.ne_right.symm
    have hEDR : E ∈ line[ℝ, D, R] := by
      have h2 : line[ℝ, N, R] = line[ℝ, D, R] :=
        (AffineSubspace.eq_iff_direction_eq_of_mem (right_mem_affineSpan_pair ℝ N R)
          (right_mem_affineSpan_pair ℝ D R)).mpr
          (Submodule.eq_of_le_of_finrank_eq
            (AffineSubspace.direction_le (by
              rw [affineSpan_le, Set.insert_subset_iff]
              exact ⟨hNline,
                Set.singleton_subset_iff.mpr (right_mem_affineSpan_pair ℝ D R)⟩))
            (by rw [direction_affineSpan, vectorSpan_pair, direction_affineSpan, vectorSpan_pair,
                finrank_span_singleton (vsub_ne_zero.mpr hDRN.ne_right.symm),
                finrank_span_singleton (vsub_ne_zero.mpr hDRN.ne_left.symm)]))
      rwa [h2] at hEline
    have hDline : D ∈ line[ℝ, E, R] :=
      (collinear_insert_of_mem_affineSpan_pair hEDR).mem_affineSpan_of_mem_of_ne
        (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
        (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) hRE.symm
    have hle2 : line[ℝ, E, R] ≤ line[ℝ, A, C] := by
      rw [affineSpan_le, Set.insert_subset_iff]
      exact ⟨hEAC, Set.singleton_subset_iff.mpr hRline⟩
    exact hDnAC (hle2 hDline)
  -- `N ∈ (DEX)` via the intersecting-secants converse.
  have hNinDEX : N ∈ sDEX := by
    have hc4' : dist N R * dist D R = dist E R * dist X R := by
      rw [dist_comm N R, dist_comm D R, dist_comm E R, dist_comm X R]
      exact hc4
    have hcy : EuclideanGeometry.Cospherical ({N, D, E, X} : Set P) :=
      EuclideanGeometry.cospherical_of_mul_dist_eq_mul_dist_of_angle_eq_pi hc4' hangNRD hangERX hncNRE
    obtain ⟨s₀, hs₀⟩ := EuclideanGeometry.cospherical_iff_exists_sphere.mp hcy
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff] at hs₀
    obtain ⟨hNs₀, hDs₀, hEs₀, hXs₀⟩ := hs₀
    have h := sphere_eq_of_mem_of_mem_of_mem_of_not_collinear hDs₀ hEs₀ hXs₀ hDs3 hEs3 hXs3
      (not_collinear_cycle (not_collinear_cycle (affineIndependent_iff_not_collinear_set.mp hEXD)))
    exact h ▸ hNs₀
  -- `N ∈ (BDM)` when `B, D, M` are not collinear.
  have hNinBDM : ∀ hnc : ¬Collinear ℝ ({B, D, M} : Set P),
      N ∈ (⟨_, affineIndependent_iff_not_collinear_set.mpr hnc⟩ : Triangle ℝ P).circumsphere := by
    intro hnc
    have hncNRM : ¬Collinear ℝ ({N, R, M} : Set P) := by
      intro hcol
      have hMline2 : M ∈ line[ℝ, N, R] :=
        hcol.mem_affineSpan_of_mem_of_ne (Set.mem_insert _ _)
          (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
          (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))) hDRN.ne_right.symm
      have hMDR : M ∈ line[ℝ, D, R] := by
        have h2 : line[ℝ, N, R] = line[ℝ, D, R] :=
          (AffineSubspace.eq_iff_direction_eq_of_mem (right_mem_affineSpan_pair ℝ N R)
            (right_mem_affineSpan_pair ℝ D R)).mpr
            (Submodule.eq_of_le_of_finrank_eq
              (AffineSubspace.direction_le (by
                rw [affineSpan_le, Set.insert_subset_iff]
                exact ⟨hNline,
                  Set.singleton_subset_iff.mpr (right_mem_affineSpan_pair ℝ D R)⟩))
              (by rw [direction_affineSpan, vectorSpan_pair, direction_affineSpan, vectorSpan_pair,
                  finrank_span_singleton (vsub_ne_zero.mpr hDRN.ne_right.symm),
                  finrank_span_singleton (vsub_ne_zero.mpr hDRN.ne_left.symm)]))
        rwa [h2] at hMline2
      have hDline : D ∈ line[ℝ, M, R] :=
        (collinear_insert_of_mem_affineSpan_pair hMDR).mem_affineSpan_of_mem_of_ne
          (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
          (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) hRMB.ne_left.symm
      have hle3 : line[ℝ, M, R] ≤ line[ℝ, M, B] := by
        rw [affineSpan_le, Set.insert_subset_iff]
        exact ⟨left_mem_affineSpan_pair ℝ M B, Set.singleton_subset_iff.mpr hRMB'⟩
      have hDMB : D ∈ line[ℝ, M, B] := hle3 hDline
      exact hnc ((collinear_insert_of_mem_affineSpan_pair hDMB).subset
        (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto))
    have hc4'' : dist N R * dist D R = dist M R * dist B R := by
      rw [dist_comm N R, dist_comm D R, dist_comm M R, dist_comm B R]
      exact hc1.trans hc2
    have hcy : EuclideanGeometry.Cospherical ({N, D, M, B} : Set P) :=
      EuclideanGeometry.cospherical_of_mul_dist_eq_mul_dist_of_angle_eq_pi
        hc4'' hangNRD hangMRB hncNRM
    obtain ⟨s₀, hs₀⟩ := EuclideanGeometry.cospherical_iff_exists_sphere.mp hcy
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff] at hs₀
    obtain ⟨hNs₀, hDs₀, hMs₀, hBs₀⟩ := hs₀
    set sBDM : EuclideanGeometry.Sphere P :=
      (⟨_, affineIndependent_iff_not_collinear_set.mpr hnc⟩ : Triangle ℝ P).circumsphere with hsBDM
    have hBs5 : B ∈ sBDM := Simplex.mem_circumsphere _ 0
    have hDs5 : D ∈ sBDM := Simplex.mem_circumsphere _ 1
    have hMs5 : M ∈ sBDM := Simplex.mem_circumsphere _ 2
    have h := sphere_eq_of_mem_of_mem_of_mem_of_not_collinear hDs₀ hMs₀ hBs₀ hDs5 hMs5 hBs5
      (not_collinear_cycle hnc)
    exact h ▸ hNs₀
  exact ⟨N, hNmem, hNinDEX, hNline, hDRN, hDRN.left_ne_right.symm, hDRN.ne_right.symm,
    hc1, hc2, hc3, hNinBDM⟩

/-- If `x` lies on the ray from `Z` through `c` (as a positive `lineMap` multiple) and
`Zx · Zc = Zq²`, then `x` is the inversion of `c` in the circle with center `Z` and
radius `Zq`. -/
theorem eq_inversion_of_ray_of_mul_dist_eq {Z c x q : P} {r : ℝ}
    (hr : 0 < r) (hx : x = AffineMap.lineMap Z c r)
    (hd : dist Z x * dist Z c = dist Z q ^ 2) (hc : Z ≠ c) :
    x = EuclideanGeometry.inversion Z (dist Z q) c := by
  have hZP : 0 < dist Z c := dist_pos.mpr hc
  have h2 : dist Z x = r * dist Z c := by
    rw [hx, ← dist_comm (AffineMap.lineMap Z c r) Z, dist_lineMap_left Z c r, Real.norm_eq_abs,
      abs_of_pos hr]
  rw [h2] at hd
  have h5 : r * (dist Z c) ^ 2 = (dist Z q) ^ 2 := by nlinarith [hd]
  have h6 : r = (dist Z q / dist Z c) ^ 2 := by
    rw [div_pow, eq_div_iff (pow_ne_zero 2 hZP.ne')]
    exact h5
  rw [hx, EuclideanGeometry.inversion_eq_lineMap, h6, dist_comm Z c]

/-- `M`, `B`, `D` are the images of `A`, `C`, `D` under the inversion at `(Z, ZD)`. -/
theorem inversion_facts {A B C D Z M : P}
    (hZneA : Z ≠ A) (hZC : Z ≠ C)
    (hZsbtw : Sbtw ℝ B C Z) (hZMA : Sbtw ℝ Z M A)
    (hZMZA : dist Z M * dist Z A = dist Z D ^ 2)
    (hZBZC : dist Z B * dist Z C = dist Z D ^ 2) :
    M = EuclideanGeometry.inversion Z (dist Z D) A ∧
    B = EuclideanGeometry.inversion Z (dist Z D) C ∧
    D = EuclideanGeometry.inversion Z (dist Z D) D := by
  refine ⟨?_, ?_, (EuclideanGeometry.inversion_dist_center' Z D).symm⟩
  · obtain ⟨t, ht, rfl⟩ := (sbtw_iff_mem_image_Ioo_and_ne.mp hZMA).1
    exact eq_inversion_of_ray_of_mul_dist_eq ht.1 rfl hZMZA hZneA
  · -- `B` is on the ray from `Z` through `C` (beyond `C`).
    have hBline : B ∈ line[ℝ, Z, C] :=
      hZsbtw.symm.wbtw.collinear.mem_affineSpan_of_mem_of_ne (Set.mem_insert _ _)
        (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))) hZC
    rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hBline
    obtain ⟨t, ht⟩ := hBline
    obtain ⟨u, hu, hCu⟩ := (sbtw_iff_mem_image_Ioo_and_ne.mp hZsbtw.symm).1
    have hv1 : B -ᵥ Z = t • (C -ᵥ Z) := by rw [← ht, AffineMap.lineMap_apply, vadd_vsub]
    have hv2 : C -ᵥ Z = u • (B -ᵥ Z) := by rw [← hCu, AffineMap.lineMap_apply, vadd_vsub]
    rw [hv1, smul_smul] at hv2
    have hCnZ : C -ᵥ Z ≠ 0 := vsub_ne_zero.mpr hZC.symm
    have h7 : (u * t) • (C -ᵥ Z) = 1 • (C -ᵥ Z) := by rw [← hv2, one_smul]
    have hut : u * t = 1 := by
      have h8 : (1 - u * t) • (C -ᵥ Z) = 0 := by
        rw [sub_smul, one_smul, sub_eq_zero]
        exact hv2
      have h9 := (smul_eq_zero_iff_left hCnZ).mp h8
      linarith [h9]
    have htpos : 0 < t := by
      have h8 : 0 < u := hu.1
      have h9 : u ≠ 0 := ne_of_gt h8
      have h10 : t = u⁻¹ := by
        field_simp [h9]
        linarith [hut]
      rw [h10]
      positivity
    exact eq_inversion_of_ray_of_mul_dist_eq htpos ht.symm hZBZC hZC

/-- If `Z` lies on the circle `(ACD)`, then `B, D, M` are collinear: all three are images
under the inversion at `(Z, ZD)` of points of `(ACD)`, hence lie on the line of points `y`
with `⟪y −ᵥ Z, O₁ −ᵥ Z⟫ = ZD²/2`. -/
theorem collinear_BDM_of_mem_sACD {sACD : EuclideanGeometry.Sphere P} {A B C D M Z : P}
    (hZmem : Z ∈ sACD) (hAmem : A ∈ sACD) (hCmem : C ∈ sACD) (hDmem : D ∈ sACD)
    (hZA : Z ≠ A) (hZC : Z ≠ C) (hZD : Z ≠ D) (hMB : M ≠ B)
    (hMinv : M = EuclideanGeometry.inversion Z (dist Z D) A)
    (hBinv : B = EuclideanGeometry.inversion Z (dist Z D) C)
    (hDinv : D = EuclideanGeometry.inversion Z (dist Z D) D) :
    Collinear ℝ ({B, D, M} : Set P) := by
  letI : FiniteDimensional ℝ V :=
    FiniteDimensional.of_finrank_eq_succ (n := 1) (Fact.out : finrank ℝ V = 2)
  have eM : ⟪M -ᵥ Z, sACD.center -ᵥ Z⟫ = dist Z D ^ 2 / 2 := by
    have e := inner_inversion_vsub_center_eq_half_sq (R := dist Z D) hZmem hAmem hZA.symm
    rwa [← hMinv] at e
  have eB : ⟪B -ᵥ Z, sACD.center -ᵥ Z⟫ = dist Z D ^ 2 / 2 := by
    have e := inner_inversion_vsub_center_eq_half_sq (R := dist Z D) hZmem hCmem hZC.symm
    rwa [← hBinv] at e
  have eD : ⟪D -ᵥ Z, sACD.center -ᵥ Z⟫ = dist Z D ^ 2 / 2 := by
    have e := inner_inversion_vsub_center_eq_half_sq (R := dist Z D) hZmem hDmem hZD.symm
    rwa [← hDinv] at e
  have hOnZ : sACD.center -ᵥ Z ≠ 0 := by
    rw [vsub_ne_zero]
    intro h
    have h1 : dist Z sACD.center = sACD.radius := EuclideanGeometry.mem_sphere.mp hZmem
    rw [← h, dist_self] at h1
    have h2 : dist A sACD.center = sACD.radius := EuclideanGeometry.mem_sphere.mp hAmem
    rw [← h1, dist_eq_zero] at h2
    exact hZA.symm (h2.trans h)
  have hMB2 : ⟪M -ᵥ B, sACD.center -ᵥ Z⟫ = 0 := by
    rw [← vsub_sub_vsub_cancel_right M B Z, inner_sub_left, eM, eB, sub_self]
  have hDM : ⟪D -ᵥ M, sACD.center -ᵥ Z⟫ = 0 := by
    rw [← vsub_sub_vsub_cancel_right D M Z, inner_sub_left, eD, eM, sub_self]
  have hfin : finrank ℝ (ℝ ∙ (sACD.center -ᵥ Z))ᗮ = 1 :=
    Submodule.finrank_orthogonal_span_singleton hOnZ
  have hBMmem : M -ᵥ B ∈ (ℝ ∙ (sACD.center -ᵥ Z))ᗮ :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.mpr hMB2
  have hDMmem : D -ᵥ M ∈ (ℝ ∙ (sACD.center -ᵥ Z))ᗮ :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.mpr hDM
  have hspan : (ℝ ∙ (M -ᵥ B)) = (ℝ ∙ (sACD.center -ᵥ Z))ᗮ :=
    Submodule.eq_of_le_of_finrank_eq
      (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hBMmem))
      (by rw [hfin, finrank_span_singleton (vsub_ne_zero.mpr hMB)])
  have hDspan : D -ᵥ M ∈ ℝ ∙ (M -ᵥ B) := hspan.symm ▸ hDMmem
  have hDline : D ∈ line[ℝ, M, B] := by
    have h1 := AffineSubspace.vadd_mem_of_mem_direction
      (by rw [direction_affineSpan, vectorSpan_pair]; exact hDspan)
      (left_mem_affineSpan_pair ℝ M B)
    rwa [vsub_vadd D M] at h1
  exact (collinear_insert_of_mem_affineSpan_pair hDline).subset
    (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)

/-- The circumcenters of `ADC` and `EXD` differ: equality would put both `E` and `X` on the
circle `(ACD)`, and line `AC` meets that circle only in `A` and `C`. -/
theorem O1_ne_O2 {A B C D E X : P}
    (hai : AffineIndependent ℝ ![A, B, C])
    (hlt : dist A C < dist A B)
    (hEAC : E ∈ line[ℝ, A, C]) (hEneA : E ≠ A) (hEneC : E ≠ C)
    (hX : X ∈ line[ℝ, A, C]) (hXCB : dist C X = dist B X)
    (hEXD : AffineIndependent ℝ ![E, X, D])
    (haiADC : AffineIndependent ℝ ![A, D, C]) :
    (⟨_, haiADC⟩ : Triangle ℝ P).circumcenter ≠ (⟨_, hEXD⟩ : Triangle ℝ P).circumcenter := by
  intro h
  have hAC : A ≠ C := hai.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hBC : B ≠ C := hai.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  have hEX : E ≠ X := hEXD.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  set sACD : EuclideanGeometry.Sphere P := (⟨_, haiADC⟩ : Triangle ℝ P).circumsphere with hsACD
  set sDEX : EuclideanGeometry.Sphere P := (⟨_, hEXD⟩ : Triangle ℝ P).circumsphere with hsDEX
  have hDs : D ∈ sACD := Simplex.mem_circumsphere _ 1
  have hDs2 : D ∈ sDEX := Simplex.mem_circumsphere _ 2
  have hEs2 : E ∈ sDEX := Simplex.mem_circumsphere _ 0
  have hXs2 : X ∈ sDEX := Simplex.mem_circumsphere _ 1
  have hAs : A ∈ sACD := Simplex.mem_circumsphere _ 0
  have hCs : C ∈ sACD := Simplex.mem_circumsphere _ 2
  have hspeq : sACD = sDEX := by
    have hc : sACD.center = sDEX.center := h
    have hr : sACD.radius = sDEX.radius := by
      have h1 := EuclideanGeometry.mem_sphere.mp hDs
      have h2 := EuclideanGeometry.mem_sphere.mp hDs2
      rw [hc] at h1
      exact h1.symm.trans h2
    rw [← EuclideanGeometry.Sphere.mk_center_radius sACD,
      ← EuclideanGeometry.Sphere.mk_center_radius sDEX, hc, hr]
  -- `E ∈ sACD`: count on line `AC`.
  rcases (EuclideanGeometry.Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
    hAs hEAC).mpr (hspeq.symm ▸ hEs2) with h1 | h1
  · exact hEneA h1
  · have hC2 : C = sACD.secondInter A (C -ᵥ A) := by
      rcases (EuclideanGeometry.Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
        hAs (right_mem_affineSpan_pair ℝ A C)).mpr hCs with h2 | h2
      · exact absurd h2 hAC.symm
      · exact h2
    exact hEneC (h1.trans hC2.symm)

snip end

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
  -- Choose an orientation of the plane for the oriented-angle arguments.
  letI : FiniteDimensional ℝ V := FiniteDimensional.of_fact_finrank_eq_two
  letI : Module.Oriented ℝ V (Fin 2) :=
    ⟨(finBasisOfFinrankEq ℝ V (Fact.out : finrank ℝ V = 2)).orientation⟩
  -- A vertex of the triangle is not an interior point, so `A ≠ D`.
  have hA_ne_D : A ≠ D := by
    rintro rfl
    exact Simplex.point_notMem_interior _ 0 D_mem_interior_ABC
  -- Distinct vertices of the triangle.
  have hBC : B ≠ C :=
    affineIndependent_ABC.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  -- An interior point `D` does not lie on the line `BC`; hence `B, C, D` are not collinear.
  have hBCD : ¬Collinear ℝ ({B, C, D} : Set P) := by
    intro hcol
    have hDline : D ∈ line[ℝ, B, C] :=
      hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hBC
    rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hDline
    obtain ⟨c, hc⟩ := hDline
    obtain ⟨w, hsum, hwI, hcomb⟩ := D_mem_interior_ABC
    have hcomb' : Finset.univ.affineCombination ℝ ![A, B, C] w = D := hcomb
    have hB : Finset.univ.affineCombination ℝ ![A, B, C] (Pi.single 1 1) = B :=
      Finset.affineCombination_piSingle ℝ Finset.univ ![A, B, C] (Finset.mem_univ 1)
    have hC : Finset.univ.affineCombination ℝ ![A, B, C] (Pi.single 2 1) = C :=
      Finset.affineCombination_piSingle ℝ Finset.univ ![A, B, C] (Finset.mem_univ 2)
    have hc' : Finset.univ.affineCombination ℝ ![A, B, C] w =
        AffineMap.lineMap (Finset.univ.affineCombination ℝ ![A, B, C] (Pi.single 1 1))
          (Finset.univ.affineCombination ℝ ![A, B, C] (Pi.single 2 1)) c := by
      rw [hB, hC, hcomb']
      exact hc.symm
    have key := (affineIndependent_ABC.affineCombination_eq_lineMap_iff_weight_lineMap
      (w₁ := Pi.single 1 1) (w₂ := Pi.single 2 1) hsum
      (Fintype.sum_pi_single' 1 _) (Fintype.sum_pi_single' 2 _) c).mp hc'
    have h0 : w 0 = 0 := by
      have h0' := key 0 (Finset.mem_univ 0)
      simp only [Pi.single_eq_of_ne (show (0 : Fin 3) ≠ 1 by decide),
        Pi.single_eq_of_ne (show (0 : Fin 3) ≠ 2 by decide), AffineMap.lineMap_apply_module,
        smul_zero, add_zero] at h0'
      exact h0'
    have hpos := (hwI 0).1
    rw [h0] at hpos
    exact lt_irrefl (0 : ℝ) hpos
  have hDBC : ¬Collinear ℝ ({D, B, C} : Set P) := by
    have hset : ({D, B, C} : Set P) = {B, C, D} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rwa [hset]
  -- Non-collinear triples determine nonzero angles.
  have hBCD_angle : ∠ B C D ≠ 0 :=
    EuclideanGeometry.angle_ne_zero_of_not_collinear hBCD
  have hDBC_angle : ∠ D B C ≠ 0 :=
    EuclideanGeometry.angle_ne_zero_of_not_collinear hDBC
  -- `E ≠ A`: otherwise `∠ A D E = ∠ A D A = 0`, but it equals `∠ B C D ≠ 0`.
  have hE_ne_A : E ≠ A := by
    intro hEA
    rw [hEA, EuclideanGeometry.angle_self_of_ne hA_ne_D] at angle_ADE_eq_angle_BCD
    exact hBCD_angle angle_ADE_eq_angle_BCD.symm
  -- `F ≠ A`: otherwise `∠ F D A = ∠ A D A = 0`, but it equals `∠ D B C ≠ 0`.
  have hF_ne_A : F ≠ A := by
    intro hFA
    rw [hFA, EuclideanGeometry.angle_self_of_ne hA_ne_D] at angle_FDA_eq_angle_DBC
    exact hDBC_angle angle_FDA_eq_angle_DBC.symm
  -- `E ≠ F`: a common point of the lines `AC` and `AB` different from `A` would force
  -- `A, B, C` to be collinear.
  have hEF : E ≠ F := by
    intro hEF'
    have hEAC : E ∈ line[ℝ, A, C] := wbtw_A_E_C.mem_affineSpan
    have hFAB : F ∈ line[ℝ, A, B] := wbtw_A_F_B.mem_affineSpan
    subst hEF'
    have hB_line : B ∈ line[ℝ, E, A] :=
      (collinear_insert_of_mem_affineSpan_pair hFAB).mem_affineSpan_of_mem_of_ne
        (by simp) (by simp) (by simp) hE_ne_A
    have hC_line : C ∈ line[ℝ, E, A] :=
      (collinear_insert_of_mem_affineSpan_pair hEAC).mem_affineSpan_of_mem_of_ne
        (by simp) (by simp) (by simp) hE_ne_A
    have hcol4 : Collinear ℝ ({B, C, E, A} : Set P) :=
      collinear_insert_insert_of_mem_affineSpan_pair hB_line hC_line
    have hcol3 : Collinear ℝ ({A, B, C} : Set P) :=
      hcol4.subset (by
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
        tauto)
    exact (affineIndependent_iff_not_collinear_set.mp affineIndependent_ABC) hcol3
  -- Obtain `Z = BC ∩ EF` and its tangent-power property.
  obtain ⟨Z, hZBC, hZsbtw, hZEF, hZsbtwEF⟩ := exists_Z affineIndependent_ABC D_mem_interior_ABC
    angle_DAB_eq_angle_CAD AC_lt_AB wbtw_A_E_C angle_ADE_eq_angle_BCD wbtw_A_F_B angle_FDA_eq_angle_DBC
  obtain ⟨sBCD, sDEF, hTanZ2, hTanZ, hZD2BC, hZD2EF, hBsBCD, hCsBCD, hDsBCD, hDsDEF, hEsDEF,
    hFsDEF⟩ := tangent_power_at_Z affineIndependent_ABC D_mem_interior_ABC angle_DAB_eq_angle_CAD
    AC_lt_AB wbtw_A_E_C angle_ADE_eq_angle_BCD wbtw_A_F_B angle_FDA_eq_angle_DBC X_mem_AC CX_eq_BX
    affineIndependent_EXD hZBC hZsbtw hZEF hZsbtwEF
  -- The Miquel point `M` and its properties.
  obtain ⟨M, hMmem, hMline, hMA, hMZ, hMC, hMB, hME⟩ := miquel_M_exists affineIndependent_ABC
    D_mem_interior_ABC angle_DAB_eq_angle_CAD wbtw_A_E_C angle_ADE_eq_angle_BCD
    wbtw_A_F_B angle_FDA_eq_angle_DBC hZBC hZsbtw hZEF hZsbtwEF
  have hMZCE := miquel_M_on_ZCE affineIndependent_ABC D_mem_interior_ABC angle_DAB_eq_angle_CAD
    wbtw_A_E_C angle_ADE_eq_angle_BCD wbtw_A_F_B angle_FDA_eq_angle_DBC hZBC hZsbtw hZEF hZsbtwEF
    hMmem hMline hMA hMZ hMC hMB hME
  have hEneA : E ≠ A := hE_ne_A
  have hEneC : E ≠ C := E_ne_C affineIndependent_ABC D_mem_interior_ABC angle_DAB_eq_angle_CAD
    wbtw_A_E_C angle_ADE_eq_angle_BCD
  have hMsbtw : Sbtw ℝ A M Z := miquel_M_sbtw affineIndependent_ABC acuteAngled_ABC
    (affineIndependent_ZCE affineIndependent_ABC wbtw_A_E_C.mem_affineSpan hEneC hZBC
      hZsbtw.ne_right.symm)
    wbtw_A_E_C hEneA hEneC hZsbtw hMZCE hMline hMA hMZ
  have hZMA : Sbtw ℝ Z M A := hMsbtw.symm
  have hMpow := miquel_M_power affineIndependent_ABC hZBC hZsbtw hMmem hMline hMA
  have hZMZA : dist Z M * dist Z A = dist Z D ^ 2 := by rw [hMpow, hZD2BC]
  have hZBZC : dist Z B * dist Z C = dist Z D ^ 2 := hZD2BC.symm
  have hcyc := concyclic_BXME affineIndependent_ABC D_mem_interior_ABC angle_DAB_eq_angle_CAD
    wbtw_A_E_C angle_ADE_eq_angle_BCD wbtw_A_F_B angle_FDA_eq_angle_DBC X_mem_AC CX_eq_BX
    affineIndependent_EXD hZBC hZsbtw hZEF hZsbtwEF hMmem hMZCE hMline hMA hMZ hMC hMB hME
  -- The point `R = AC ∩ BM` and `N`, with `N ∈ (DEX)`.
  obtain ⟨R, hRline, hRAC, hRMB⟩ := R_exists affineIndependent_ABC hZBC hZsbtw hMsbtw hMmem hMA hMC hMB
  obtain ⟨N, hNmem, hNinDEX, hNline, hDRN, hND, hNR, hc1, hc2, hc3, hNinBDM⟩ :=
    N_facts affineIndependent_ABC D_mem_interior_ABC angle_DAB_eq_angle_CAD wbtw_A_E_C
      angle_ADE_eq_angle_BCD wbtw_A_F_B angle_FDA_eq_angle_DBC X_mem_AC CX_eq_BX
      affineIndependent_EXD affineIndependent_ADC hZBC hZsbtw hZEF hZsbtwEF hMmem hMline
      hMA hMZ hMC hMB hME hcyc hRline hRAC hRMB
  -- Basic distinctness facts.
  have hAB : A ≠ B :=
    affineIndependent_ABC.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hDB : D ≠ B := by
    rintro rfl
    exact Simplex.point_notMem_interior _ 1 D_mem_interior_ABC
  have hDC : D ≠ C := by
    rintro rfl
    exact Simplex.point_notMem_interior _ 2 D_mem_interior_ABC
  have hZD : Z ≠ D := by
    intro h
    rw [h] at hZBC
    exact (not_mem_line_of_mem_interior affineIndependent_ABC D_mem_interior_ABC) hZBC
  have hZA : Z ≠ A := by
    intro h
    rw [h] at hZBC
    exact (affineIndependent_iff_not_collinear_set.mp affineIndependent_ABC)
      (collinear_insert_of_mem_affineSpan_pair hZBC)
  have hZC : Z ≠ C := hZsbtw.ne_right.symm
  have hZB : Z ≠ B := hZsbtw.left_ne_right.symm
  -- The inversion at `(Z, ZD)` and the two circles.
  obtain ⟨hMinv, hBinv, hDinv⟩ := inversion_facts hZA hZC hZsbtw hZMA hZMZA hZBZC
  set sACD : EuclideanGeometry.Sphere P := (⟨_, affineIndependent_ADC⟩ : Triangle ℝ P).circumsphere
  set sDEX : EuclideanGeometry.Sphere P := (⟨_, affineIndependent_EXD⟩ : Triangle ℝ P).circumsphere
  have hDs : D ∈ sACD := Simplex.mem_circumsphere _ 1
  have hAs : A ∈ sACD := Simplex.mem_circumsphere _ 0
  have hCs : C ∈ sACD := Simplex.mem_circumsphere _ 2
  have hDs2 : D ∈ sDEX := Simplex.mem_circumsphere _ 2
  have hO1O2 : sACD.center ≠ sDEX.center :=
    O1_ne_O2 affineIndependent_ABC AC_lt_AB wbtw_A_E_C.mem_affineSpan hEneA hEneC X_mem_AC CX_eq_BX
      affineIndependent_EXD affineIndependent_ADC
  letI : FiniteDimensional ℝ V :=
    FiniteDimensional.of_finrank_eq_succ (n := 1) (Fact.out : finrank ℝ V = 2)
  -- `Z` lies on the perpendicular bisector of `DN` (two cases).
  have hfin : ∀ {c : EuclideanGeometry.Sphere P}, D ∈ c → N ∈ c →
      c.center ∈ AffineSubspace.perpBisector D N :=
    fun {c} hD' hN' => AffineSubspace.mem_perpBisector_iff_dist_eq.mpr (by
      rw [dist_comm (EuclideanGeometry.Sphere.center c) D,
        dist_comm (EuclideanGeometry.Sphere.center c) N]
      exact (EuclideanGeometry.mem_sphere.mp hD').trans (EuclideanGeometry.mem_sphere.mp hN').symm)
  have hZperp : Z ∈ AffineSubspace.perpBisector D N := by
    by_cases hZmem : Z ∈ sACD
    · -- Case 1: `Z ∈ (ACD)`. Then `B, D, M` are collinear, so `N` lies on line `DB`,
      -- and `ZDN` is isosceles by an oriented-angle chase.
      have hcolBDM := collinear_BDM_of_mem_sACD hZmem hAs hCs hDs hZA hZC hZD hMB hMinv hBinv hDinv
      have hDnBM : D ∈ line[ℝ, B, M] :=
        hcolBDM.mem_affineSpan_of_mem_of_ne (Set.mem_insert _ _)
          (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
          (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) hMB.symm
      have hRMB' : R ∈ line[ℝ, M, B] := hRMB.wbtw.mem_affineSpan
      have hDMB' : D ∈ line[ℝ, M, B] := by
        have h1 : line[ℝ, B, M] = line[ℝ, M, B] := by rw [Set.pair_comm B M]
        rwa [h1] at hDnBM
      have hRDB : R ∈ line[ℝ, D, B] :=
        (collinear_insert_insert_of_mem_affineSpan_pair hDMB' hRMB').mem_affineSpan_of_mem_of_ne
          (Set.mem_insert _ _)
          (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
            (Set.mem_singleton _))))
          (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) hDB
      have hlineDRB : line[ℝ, D, R] = line[ℝ, D, B] :=
        (AffineSubspace.eq_iff_direction_eq_of_mem (left_mem_affineSpan_pair ℝ D R)
          (left_mem_affineSpan_pair ℝ D B)).mpr
          (Submodule.eq_of_le_of_finrank_eq
            (AffineSubspace.direction_le (by
              rw [affineSpan_le, Set.insert_subset_iff]
              exact ⟨left_mem_affineSpan_pair ℝ D B, Set.singleton_subset_iff.mpr hRDB⟩))
            (by rw [direction_affineSpan, vectorSpan_pair, direction_affineSpan, vectorSpan_pair,
                finrank_span_singleton (vsub_ne_zero.mpr hDRN.ne_left.symm),
                finrank_span_singleton (vsub_ne_zero.mpr hDB)]))
      have hNDB : N ∈ line[ℝ, D, B] := by rwa [hlineDRB] at hNline
      have hZnotDB : Z ∉ line[ℝ, D, B] := by
        intro hZline
        have hDZ : D ∈ line[ℝ, Z, B] :=
          (collinear_insert_of_mem_affineSpan_pair hZline).mem_affineSpan_of_mem_of_ne
            (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
            (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) hZB
        have hle6 : line[ℝ, Z, B] ≤ line[ℝ, B, C] := by
          rw [affineSpan_le, Set.insert_subset_iff]
          exact ⟨hZBC, Set.singleton_subset_iff.mpr (left_mem_affineSpan_pair ℝ B C)⟩
        exact (not_mem_line_of_mem_interior affineIndependent_ABC D_mem_interior_ABC) (hle6 hDZ)
      have hNZ : N ≠ Z := fun h => hZnotDB (h ▸ hNDB)
      have hncZDN : ¬Collinear ℝ ({Z, D, N} : Set P) := by
        intro hcol
        have hZline : Z ∈ line[ℝ, D, N] :=
          hcol.mem_affineSpan_of_mem_of_ne (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
            (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
            (Set.mem_insert _ _) hND.symm
        have hZDR : Z ∈ line[ℝ, D, R] := by
          have h5 : line[ℝ, D, N] = line[ℝ, D, R] :=
            (AffineSubspace.eq_iff_direction_eq_of_mem (left_mem_affineSpan_pair ℝ D N)
              (left_mem_affineSpan_pair ℝ D R)).mpr
              (Submodule.eq_of_le_of_finrank_eq
                (AffineSubspace.direction_le (by
                  rw [affineSpan_le, Set.insert_subset_iff]
                  exact ⟨left_mem_affineSpan_pair ℝ D R, Set.singleton_subset_iff.mpr hNline⟩))
                (by rw [direction_affineSpan, vectorSpan_pair, direction_affineSpan, vectorSpan_pair,
                    finrank_span_singleton (vsub_ne_zero.mpr hND.symm),
                    finrank_span_singleton (vsub_ne_zero.mpr hDRN.ne_left.symm)]))
          rwa [h5] at hZline
        exact hZnotDB (by rwa [hlineDRB] at hZDR)
      have key : (2 : ℤ) • ∡ D N Z = (2 : ℤ) • ∡ Z D N := by
        have h1 : (2 : ℤ) • ∡ D N Z = (2 : ℤ) • ∡ D C Z :=
          EuclideanGeometry.Sphere.two_zsmul_oangle_eq hDs hNmem hCs hZmem hND hNZ hDC.symm hZC.symm
        have h2 : (2 : ℤ) • ∡ D C Z = (2 : ℤ) • ∡ D C B :=
          Collinear.two_zsmul_oangle_eq_right
            (collinear_insert_of_mem_affineSpan_pair (Set.pair_comm B C ▸ hZBC))
            hZC hBC
        have h3 : (2 : ℤ) • ∡ D C B = (2 : ℤ) • ∡ Z D B :=
          (two_zsmul_oangle_tangent_chord hDsBCD hCsBCD hBsBCD hTanZ2
            (right_mem_affineSpan_pair ℝ D Z) hZD hDB.symm hDC.symm hBC.symm).symm
        have h4 : (2 : ℤ) • ∡ Z D B = (2 : ℤ) • ∡ Z D N :=
          Collinear.two_zsmul_oangle_eq_right
            ((collinear_insert_of_mem_affineSpan_pair hNDB).subset
              (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto))
            hDB.symm hND
        rw [h1, h2, h3, h4]
      have hsin : Real.sin (∠ D N Z) = Real.sin (∠ Z D N) := by
        rcases Real.Angle.two_zsmul_eq_iff.mp key with h | h
        · have h1 : Real.cos (∠ D N Z) = Real.cos (∠ Z D N) := by
            rw [← EuclideanGeometry.cos_oangle_eq_cos_angle hND.symm hNZ.symm,
              ← EuclideanGeometry.cos_oangle_eq_cos_angle hZD hND, h]
          have h2 : ∠ D N Z = ∠ Z D N :=
            (Real.injOn_cos.eq_iff
              ⟨EuclideanGeometry.angle_nonneg D N Z, EuclideanGeometry.angle_le_pi D N Z⟩
              ⟨EuclideanGeometry.angle_nonneg Z D N, EuclideanGeometry.angle_le_pi Z D N⟩).mp h1
          rw [h2]
        · have h1 : Real.cos (∠ D N Z) = -Real.cos (∠ Z D N) := by
            rw [← EuclideanGeometry.cos_oangle_eq_cos_angle hND.symm hNZ.symm,
              ← EuclideanGeometry.cos_oangle_eq_cos_angle hZD hND, h, Real.Angle.cos_add_pi]
          have h2 : Real.cos (∠ D N Z) = Real.cos (π - ∠ Z D N) := by
            rw [Real.cos_pi_sub, h1]
          have h3 : ∠ D N Z = π - ∠ Z D N :=
            (Real.injOn_cos.eq_iff
              ⟨EuclideanGeometry.angle_nonneg D N Z, EuclideanGeometry.angle_le_pi D N Z⟩
              ⟨by linarith [EuclideanGeometry.angle_le_pi Z D N],
                by linarith [EuclideanGeometry.angle_nonneg Z D N]⟩).mp h2
          rw [h3, Real.sin_pi_sub]
      have hnc2 : ¬Collinear ℝ ({D, N, Z} : Set P) := by
        intro hcol
        exact hncZDN (hcol.subset (by intro x hx; simp only [Set.mem_insert_iff,
          Set.mem_singleton_iff] at hx ⊢; tauto))
      have hls : dist D Z * Real.sin (∠ N D Z) = dist N Z * Real.sin (∠ D N Z) :=
        dist_mul_sin_eq_dist_mul_sin hnc2
      have hsin2 : 0 < Real.sin (∠ Z D N) := by
        have h1 : ∠ Z D N ≠ 0 := EuclideanGeometry.angle_ne_zero_of_not_collinear hncZDN
        have h2 : ∠ Z D N ≠ π := by
          intro h3
          exact hncZDN (EuclideanGeometry.angle_eq_pi_iff_sbtw.mp h3).wbtw.collinear
        have h3 : 0 < ∠ Z D N := (EuclideanGeometry.angle_nonneg Z D N).lt_of_ne' h1
        have h4 : ∠ Z D N < π := (EuclideanGeometry.angle_le_pi Z D N).lt_of_ne h2
        exact Real.sin_pos_of_mem_Ioo ⟨h3, h4⟩
      have hcancel : dist D Z = dist N Z := by
        have h5 : dist D Z * Real.sin (∠ Z D N) = dist N Z * Real.sin (∠ Z D N) := by
          rw [EuclideanGeometry.angle_comm N D Z, hsin] at hls
          exact hls
        exact mul_right_cancel₀ hsin2.ne' h5
      exact AffineSubspace.mem_perpBisector_iff_dist_eq.mpr (by
        rw [dist_comm Z D, dist_comm Z N]
        exact hcancel)
    · -- Case 2: `Z ∉ (ACD)`. The inversion at `(Z, ZD)` swaps `(ACD)` and `(BDM)`,
      -- so `Z` is on the line of centers.
      have hnc : ¬Collinear ℝ ({B, D, M} : Set P) := by
        intro hcol
        obtain ⟨s', himage, hcenter, hradius⟩ := inversion_sphere_image (dist_pos.mpr hZD).ne'
          ⟨D, hDs⟩ hZmem
        have hM' : M ∈ s' := by
          have h1 : M ∈ EuclideanGeometry.inversion Z (dist Z D) '' Metric.sphere sACD.center sACD.radius :=
            by exact ⟨A, hAs, hMinv.symm⟩
          rwa [himage] at h1
        have hB' : B ∈ s' := by
          have h1 : B ∈ EuclideanGeometry.inversion Z (dist Z D) '' Metric.sphere sACD.center sACD.radius :=
            by exact ⟨C, hCs, hBinv.symm⟩
          rwa [himage] at h1
        have hD' : D ∈ s' := by
          have h1 : D ∈ EuclideanGeometry.inversion Z (dist Z D) '' Metric.sphere sACD.center sACD.radius :=
            by exact ⟨D, hDs, hDinv.symm⟩
          rwa [himage] at h1
        have hDline : D ∈ line[ℝ, M, B] :=
          hcol.mem_affineSpan_of_mem_of_ne (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
            (Set.mem_singleton _))) (Set.mem_insert _ _)
            (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) hMB
        have hBline2 : B ∈ line[ℝ, M, B] := right_mem_affineSpan_pair ℝ M B
        have hMD : M ≠ D := by
          intro hMD2
          rw [hMD2] at hMmem
          have hlt2 := dist_lt_circumradius_of_mem_interior (t := ⟨_, affineIndependent_ABC⟩)
            D_mem_interior_ABC
          have hlt2' : dist D (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).circumsphere.center <
              (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).circumsphere.radius := hlt2
          have h3 := EuclideanGeometry.mem_sphere.mp hMmem
          rw [h3] at hlt2'
          exact lt_irrefl _ hlt2'
        rcases (EuclideanGeometry.Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
          hM' hDline).mpr hD' with h1 | h1
        · exact hMD h1.symm
        · rcases (EuclideanGeometry.Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
            hM' hBline2).mpr hB' with h2 | h2
          · exact hMB h2.symm
          · exact hDB (h1.trans h2.symm)
      obtain ⟨s', himage, hcenter, hradius⟩ := inversion_sphere_image (dist_pos.mpr hZD).ne'
        ⟨D, hDs⟩ hZmem
      have hM' : M ∈ s' := by
        have h1 : M ∈ EuclideanGeometry.inversion Z (dist Z D) '' Metric.sphere sACD.center sACD.radius :=
          by exact ⟨A, hAs, hMinv.symm⟩
        rwa [himage] at h1
      have hB' : B ∈ s' := by
        have h1 : B ∈ EuclideanGeometry.inversion Z (dist Z D) '' Metric.sphere sACD.center sACD.radius :=
          by exact ⟨C, hCs, hBinv.symm⟩
        rwa [himage] at h1
      have hD' : D ∈ s' := by
        have h1 : D ∈ EuclideanGeometry.inversion Z (dist Z D) '' Metric.sphere sACD.center sACD.radius :=
          by exact ⟨D, hDs, hDinv.symm⟩
        rwa [himage] at h1
      set sBDM : EuclideanGeometry.Sphere P :=
        (⟨_, affineIndependent_iff_not_collinear_set.mpr hnc⟩ : Triangle ℝ P).circumsphere
      have hMs5 : M ∈ sBDM := Simplex.mem_circumsphere _ 2
      have hBs5 : B ∈ sBDM := Simplex.mem_circumsphere _ 0
      have hDs5 : D ∈ sBDM := Simplex.mem_circumsphere _ 1
      have hs'sBDM : s' = sBDM :=
        sphere_eq_of_mem_of_mem_of_mem_of_not_collinear hM' hB' hD' hMs5 hBs5 hDs5
          (not_collinear_cycle (not_collinear_cycle hnc))
      -- `Z` on the line of centers of `(ACD)` and `(BDM)`.
      have hZcol : Collinear ℝ ({Z, sACD.center, sBDM.center} : Set P) := by
        have h1 : s'.center -ᵥ Z = (dist Z D ^ 2 / sACD.power Z) • (sACD.center -ᵥ Z) := by
          rw [hcenter, vadd_vsub]
        have h2 : sBDM.center -ᵥ Z = (dist Z D ^ 2 / sACD.power Z) • (sACD.center -ᵥ Z) := by
          rw [← hs'sBDM]
          exact h1
        have h3 : sBDM.center -ᵥ Z ∈ ℝ ∙ (sACD.center -ᵥ Z) :=
          Submodule.mem_span_singleton.mpr ⟨_, h2.symm⟩
        have h4 : sBDM.center ∈ line[ℝ, Z, sACD.center] := by
          have h5 := AffineSubspace.vadd_mem_of_mem_direction
            (by rw [direction_affineSpan, vectorSpan_pair_rev]; exact h3)
            (left_mem_affineSpan_pair ℝ Z sACD.center)
          rwa [vsub_vadd sBDM.center Z] at h5
        exact (collinear_insert_of_mem_affineSpan_pair h4).subset
          (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)
      -- The centers of `(ACD)` and `(BDM)` differ (else `D` would lie on `(ABC)`).
      have hO1O3 : sACD.center ≠ sBDM.center := by
        intro h
        have hsp : sACD = sBDM := by
          have hr : sACD.radius = sBDM.radius := by
            have h1 := EuclideanGeometry.mem_sphere.mp hDs
            have h2 := EuclideanGeometry.mem_sphere.mp hDs5
            rw [h] at h1
            exact h1.symm.trans h2
          rw [← EuclideanGeometry.Sphere.mk_center_radius sACD,
            ← EuclideanGeometry.Sphere.mk_center_radius sBDM, h, hr]
        have hAs5 : A ∈ sBDM := hsp ▸ hAs
        have hCs5 : C ∈ sBDM := hsp ▸ hCs
        set sABC : EuclideanGeometry.Sphere P :=
          (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).circumsphere
        have hAsABC : A ∈ sABC := Simplex.mem_circumsphere _ 0
        have hBsABC : B ∈ sABC := Simplex.mem_circumsphere _ 1
        have hncABM : ¬Collinear ℝ ({A, B, M} : Set P) := by
          intro hcol
          have hMline2 : M ∈ line[ℝ, A, B] :=
            hcol.mem_affineSpan_of_mem_of_ne (Set.mem_insert _ _)
              (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
              (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))) hAB
          rcases (EuclideanGeometry.Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
            hAsABC hMline2).mpr hMmem with h2 | h2
          · exact hMA h2
          · have hB2 : B = sABC.secondInter A (B -ᵥ A) := by
              rcases (EuclideanGeometry.Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
                hAsABC (right_mem_affineSpan_pair ℝ A B)).mpr hBsABC with h3 | h3
              · exact absurd h3 hAB.symm
              · exact h3
            exact hMB (h2.trans hB2.symm)
        have hsp2 : sBDM = sABC :=
          sphere_eq_of_mem_of_mem_of_mem_of_not_collinear hAs5 hBs5 hMs5 hAsABC hBsABC hMmem hncABM
        have hDsABC : D ∈ sABC := hsp2 ▸ hDs5
        have hlt2 := dist_lt_circumradius_of_mem_interior (t := ⟨_, affineIndependent_ABC⟩)
          D_mem_interior_ABC
        have hlt2' : dist D (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).circumsphere.center <
            (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).circumsphere.radius := hlt2
        have h3 := EuclideanGeometry.mem_sphere.mp hDsABC
        rw [h3] at hlt2'
        exact lt_irrefl _ hlt2'
      have hle : line[ℝ, sACD.center, sBDM.center] ≤ AffineSubspace.perpBisector D N := by
        rw [affineSpan_le, Set.insert_subset_iff]
        exact ⟨hfin hDs hNmem, Set.singleton_subset_iff.mpr (hfin hDs5 (hNinBDM hnc))⟩
      have hZline : Z ∈ line[ℝ, sACD.center, sBDM.center] :=
        hZcol.mem_affineSpan_of_mem_of_ne (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
          (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
          (Set.mem_insert _ _) hO1O3
      exact hle hZline
  -- The line of centers is the perpendicular bisector of `DN`.
  have hperpline : line[ℝ, sACD.center, sDEX.center] = AffineSubspace.perpBisector D N := by
    apply (AffineSubspace.eq_iff_direction_eq_of_mem
      (left_mem_affineSpan_pair ℝ sACD.center sDEX.center) (hfin hDs hNmem)).mpr
    apply Submodule.eq_of_le_of_finrank_eq
    · exact AffineSubspace.direction_le (by
        rw [affineSpan_le, Set.insert_subset_iff]
        exact ⟨hfin hDs hNmem, Set.singleton_subset_iff.mpr (hfin hDs2 hNinDEX)⟩)
    · have hfr : finrank ℝ (AffineSubspace.perpBisector D N).direction = 1 := by
        rw [AffineSubspace.direction_perpBisector]
        exact Submodule.finrank_orthogonal_span_singleton (vsub_ne_zero.mpr hND)
      rw [hfr, direction_affineSpan, vectorSpan_pair,
        finrank_span_singleton (vsub_ne_zero.mpr hO1O2)]
  -- Assemble the conclusion.
  have hZin : Z ∈ line[ℝ, sACD.center, sDEX.center] := hperpline ▸ hZperp
  refine ⟨hEF, ?_, ⟨Z, Set.mem_inter (Set.mem_inter hZBC hZEF) ?_⟩⟩
  · rw [O₁_eq_circumcenter_ADC, O₂_eq_circumcenter_EXD]
    exact hO1O2
  · rw [O₁_eq_circumcenter_ADC, O₂_eq_circumcenter_EXD]
    exact hZin

end Imo2021P3
