/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.TwoDim
public import Mathlib.Geometry.Euclidean.MongePoint
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 2014, Problem 5

Let ABC be a triangle with orthocenter H and let P be the second intersection
of the circumcircle of triangle AHC with the internal bisector of ∠BAC.
Let X be the circumcenter of triangle APB and let Y be the orthocenter of
triangle APC. Prove that the length of segment XY is equal to the circumradius
of triangle ABC.
-/

namespace Usa2014P5

open Affine EuclideanGeometry Module

open scoped RealInnerProductSpace

/-- The Euclidean plane, coordinatized. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

variable {V Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
  [NormedAddTorsor V Pt] [Fact (finrank ℝ V = 2)]

snip begin

/-- Distance in the coordinatized plane, as a square root of a sum of squares. -/
lemma dist_eq_sqrt (x y : Plane) :
    dist x y = Real.sqrt ((x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]

/-- Extensionality for the coordinatized plane. -/
lemma plane_ext {x y : Plane} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  ext i
  fin_cases i
  · exact h0
  · exact h1

/-- If two sides of a "triangle" are parallel, it is not a genuine triangle. -/
lemma not_affineIndependent_of_vsub_smul {A B C : Pt} {r : ℝ} (h : B -ᵥ A = r • (C -ᵥ A)) :
    ¬ AffineIndependent ℝ ![A, B, C] := by
  rw [affineIndependent_iff_not_collinear_set]
  intro hnc
  apply hnc
  rw [collinear_iff_of_mem (Set.mem_insert A _)]
  refine ⟨C -ᵥ A, fun p hp => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨r, by rwa [eq_vadd_iff_vsub_eq]⟩
  · exact ⟨1, by simp⟩

/-- In the plane, a point equidistant from the three vertices of a triangle is its
circumcenter, and the common distance is its circumradius. -/
lemma circum_eq {A B C O : Plane} (h : AffineIndependent ℝ ![A, B, C])
    (hAB : dist A O = dist B O) (hAC : dist A O = dist C O) :
    O = (⟨![A, B, C], h⟩ : Triangle ℝ Plane).circumcenter ∧
      dist A O = (⟨![A, B, C], h⟩ : Triangle ℝ Plane).circumradius := by
  have htop : affineSpan ℝ (Set.range ![A, B, C]) = ⊤ :=
    h.affineSpan_eq_top_iff_card_eq_finrank_add_one.2 (by simp)
  have hO : O ∈ affineSpan ℝ (Set.range ![A, B, C]) := by
    rw [htop]
    exact AffineSubspace.mem_top ℝ (EuclideanSpace ℝ (Fin 2)) O
  have hr : ∀ i, dist (![A, B, C] i) O = dist A O := by
    intro i
    fin_cases i
    · simp
    · simpa using hAB.symm
    · simpa using hAC.symm
  exact ⟨Affine.Simplex.eq_circumcenter_of_dist_eq _ hO hr,
    Affine.Simplex.eq_circumradius_of_dist_eq _ hO hr⟩

/-- Sylvester's theorem: the orthocenter in terms of the circumcenter. -/
lemma orthocenter_eq_add_sub {A B C H O : Plane} (h : AffineIndependent ℝ ![A, B, C])
    (hH : H = Triangle.orthocenter ⟨![A, B, C], h⟩)
    (hO : O = (⟨![A, B, C], h⟩ : Triangle ℝ Plane).circumcenter) :
    H = A + B + C - 2 • O := by
  have hs := Triangle.orthocenter_vsub_circumcenter_eq_sum_vsub
    (⟨![A, B, C], h⟩ : Triangle ℝ Plane)
  rw [← hH, ← hO] at hs
  have hpts : (⟨![A, B, C], h⟩ : Triangle ℝ Plane).points = ![A, B, C] := rfl
  rw [hpts, Fin.sum_univ_three] at hs
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val_two] at hs
  simp only [vsub_eq_sub] at hs
  have : H = ((A - O) + (B - O) + (C - O)) + O := by
    rw [← hs]
    abel
  rw [this]
  module

/-- The coordinate form of the problem: the triangle is placed with A at the origin
and the internal bisector of ∠BAC as the positive x-axis, so that
B = c • (u, v), C = b • (u, -v) and P = (p, 0). -/
lemma coord_main {u v b c p : ℝ} (hu : u ≠ 0) (hv : v ≠ 0)
    {A B C P H X Y : Plane}
    (hA : A = 0) (hB : B = !₂[c * u, c * v]) (hC : C = !₂[b * u, -(b * v)])
    (hP : P = !₂[p, 0])
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hH : H = Triangle.orthocenter ⟨![A, B, C], hABC⟩)
    (hAHC : AffineIndependent ℝ ![A, H, C])
    (hPs : P ∈ (⟨![A, H, C], hAHC⟩ : Triangle ℝ Plane).circumsphere)
    (hPA : P ≠ A)
    (hAPB : AffineIndependent ℝ ![A, P, B])
    (hX : X = (⟨![A, P, B], hAPB⟩ : Triangle ℝ Plane).circumcenter)
    (hAPC : AffineIndependent ℝ ![A, P, C])
    (hY : Y = Triangle.orthocenter ⟨![A, P, C], hAPC⟩) :
    dist X Y = (⟨![A, B, C], hABC⟩ : Triangle ℝ Plane).circumradius := by
  subst hA hB hC hP
  have hp : p ≠ 0 := by
    intro hp0
    apply hPA
    rw [hp0]
    ext i
    fin_cases i <;> simp
  -- the circumcenter O₁ of ABC and the circumradius
  have d11 : dist (0 : Plane) !₂[(b + c) * (u ^ 2 + v ^ 2) / (4 * u), (c - b) * (u ^ 2 + v ^ 2) / (4 * v)]
      = dist !₂[c * u, c * v]
        !₂[(b + c) * (u ^ 2 + v ^ 2) / (4 * u), (c - b) * (u ^ 2 + v ^ 2) / (4 * v)] := by
    rw [dist_eq_sqrt, dist_eq_sqrt]
    congr 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, PiLp.zero_apply]
    field_simp
    ring
  have d12 : dist (0 : Plane) !₂[(b + c) * (u ^ 2 + v ^ 2) / (4 * u), (c - b) * (u ^ 2 + v ^ 2) / (4 * v)]
      = dist !₂[b * u, -(b * v)]
        !₂[(b + c) * (u ^ 2 + v ^ 2) / (4 * u), (c - b) * (u ^ 2 + v ^ 2) / (4 * v)] := by
    rw [dist_eq_sqrt, dist_eq_sqrt]
    congr 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, PiLp.zero_apply]
    field_simp
    ring
  obtain ⟨hO1, hR⟩ := circum_eq hABC d11 d12
  -- the orthocenter H of ABC, in coordinates
  have hHv : H = 0 + !₂[c * u, c * v] + !₂[b * u, -(b * v)] -
      2 • !₂[(b + c) * (u ^ 2 + v ^ 2) / (4 * u), (c - b) * (u ^ 2 + v ^ 2) / (4 * v)] :=
    orthocenter_eq_add_sub hABC hH hO1
  have hHc : H = !₂[(b + c) * (u ^ 2 - v ^ 2) / (2 * u), (b - c) * (u ^ 2 - v ^ 2) / (2 * v)] := by
    rw [hHv]
    refine plane_ext ?_ ?_
    · simp [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, Matrix.cons_val_zero]
      rw [eq_div_iff (mul_ne_zero (by norm_num) hu)]
      field_simp [hu]
      ring
    · simp [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, Matrix.cons_val_one]
      rw [eq_div_iff (mul_ne_zero (by norm_num) hv)]
      field_simp [hv]
      ring
  -- the circumcenter O₂ of AHC
  have d21 : dist (0 : Plane)
      !₂[(3 * b * u ^ 2 - b * v ^ 2 - c * (u ^ 2 + v ^ 2)) / (4 * u),
        (b * u ^ 2 - 3 * b * v ^ 2 - c * (u ^ 2 + v ^ 2)) / (4 * v)]
      = dist H
        !₂[(3 * b * u ^ 2 - b * v ^ 2 - c * (u ^ 2 + v ^ 2)) / (4 * u),
          (b * u ^ 2 - 3 * b * v ^ 2 - c * (u ^ 2 + v ^ 2)) / (4 * v)] := by
    rw [hHc, dist_eq_sqrt, dist_eq_sqrt]
    congr 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, PiLp.zero_apply]
    field_simp
    ring
  have d22 : dist (0 : Plane)
      !₂[(3 * b * u ^ 2 - b * v ^ 2 - c * (u ^ 2 + v ^ 2)) / (4 * u),
        (b * u ^ 2 - 3 * b * v ^ 2 - c * (u ^ 2 + v ^ 2)) / (4 * v)]
      = dist !₂[b * u, -(b * v)]
        !₂[(3 * b * u ^ 2 - b * v ^ 2 - c * (u ^ 2 + v ^ 2)) / (4 * u),
          (b * u ^ 2 - 3 * b * v ^ 2 - c * (u ^ 2 + v ^ 2)) / (4 * v)] := by
    rw [dist_eq_sqrt, dist_eq_sqrt]
    congr 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, PiLp.zero_apply]
    field_simp
    ring
  obtain ⟨hO2, -⟩ := circum_eq hAHC d21 d22
  -- the condition that P lies on the circumcircle of AHC, as an equation
  have hPs2 : dist !₂[p, 0]
      !₂[(3 * b * u ^ 2 - b * v ^ 2 - c * (u ^ 2 + v ^ 2)) / (4 * u),
        (b * u ^ 2 - 3 * b * v ^ 2 - c * (u ^ 2 + v ^ 2)) / (4 * v)]
      = dist (0 : Plane)
        !₂[(3 * b * u ^ 2 - b * v ^ 2 - c * (u ^ 2 + v ^ 2)) / (4 * u),
          (b * u ^ 2 - 3 * b * v ^ 2 - c * (u ^ 2 + v ^ 2)) / (4 * v)] := by
    have h1 : dist !₂[p, 0] (⟨![0, H, !₂[b * u, -(b * v)]], hAHC⟩ : Triangle ℝ Plane).circumcenter
        = (⟨![0, H, !₂[b * u, -(b * v)]], hAHC⟩ : Triangle ℝ Plane).circumradius := by
      have hm := mem_sphere.1 hPs
      rwa [Affine.Simplex.circumsphere_center, Affine.Simplex.circumsphere_radius] at hm
    have h2 : dist (0 : Plane)
        (⟨![0, H, !₂[b * u, -(b * v)]], hAHC⟩ : Triangle ℝ Plane).circumcenter
        = (⟨![0, H, !₂[b * u, -(b * v)]], hAHC⟩ : Triangle ℝ Plane).circumradius := by
      simpa using Affine.Simplex.dist_circumcenter_eq_circumradius
        (⟨![0, H, !₂[b * u, -(b * v)]], hAHC⟩ : Triangle ℝ Plane) (0 : Fin 3)
    rw [← hO2] at h1 h2
    rw [← h1] at h2
    exact h2.symm
  have hcon : 2 * u * p = 3 * b * u ^ 2 - b * v ^ 2 - c * (u ^ 2 + v ^ 2) := by
    rw [dist_eq_sqrt, dist_eq_sqrt] at hPs2
    have h0 := congrArg (· ^ 2) hPs2
    rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)] at h0
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, PiLp.zero_apply, zero_sub,
      neg_sq] at h0
    have hring : p * (p - 2 *
        ((3 * b * u ^ 2 - b * v ^ 2 - c * (u ^ 2 + v ^ 2)) / (4 * u)))
        = ((p - (3 * b * u ^ 2 - b * v ^ 2 - c * (u ^ 2 + v ^ 2)) / (4 * u)) ^ 2 +
            ((b * u ^ 2 - 3 * b * v ^ 2 - c * (u ^ 2 + v ^ 2)) / (4 * v)) ^ 2) -
          (((3 * b * u ^ 2 - b * v ^ 2 - c * (u ^ 2 + v ^ 2)) / (4 * u)) ^ 2 +
            ((b * u ^ 2 - 3 * b * v ^ 2 - c * (u ^ 2 + v ^ 2)) / (4 * v)) ^ 2) := by
      ring
    rw [h0] at hring
    rw [sub_self] at hring
    rcases mul_eq_zero.1 hring with hp0 | h2
    · exact absurd hp0 hp
    · have hp2 : p = 2 * ((3 * b * u ^ 2 - b * v ^ 2 - c * (u ^ 2 + v ^ 2)) / (4 * u)) := by
        linarith [h2]
      rw [hp2]
      field_simp
      ring
  -- the circumcenter O₃ of APC and the orthocenter Y of APC
  have d31 : dist (0 : Plane) !₂[p / 2, (p * u - b * (u ^ 2 + v ^ 2)) / (2 * v)]
      = dist !₂[p, 0] !₂[p / 2, (p * u - b * (u ^ 2 + v ^ 2)) / (2 * v)] := by
    rw [dist_eq_sqrt, dist_eq_sqrt]
    congr 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, PiLp.zero_apply]
    field_simp
    ring
  have d32 : dist (0 : Plane) !₂[p / 2, (p * u - b * (u ^ 2 + v ^ 2)) / (2 * v)]
      = dist !₂[b * u, -(b * v)] !₂[p / 2, (p * u - b * (u ^ 2 + v ^ 2)) / (2 * v)] := by
    rw [dist_eq_sqrt, dist_eq_sqrt]
    congr 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, PiLp.zero_apply]
    field_simp
    ring
  obtain ⟨hO3, -⟩ := circum_eq hAPC d31 d32
  have hYv : Y = 0 + !₂[p, 0] + !₂[b * u, -(b * v)] -
      2 • !₂[p / 2, (p * u - b * (u ^ 2 + v ^ 2)) / (2 * v)] :=
    orthocenter_eq_add_sub hAPC hY hO3
  have hYc : Y = !₂[b * u, u * (b * u - p) / v] := by
    rw [hYv]
    refine plane_ext ?_ ?_
    · simp [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, Matrix.cons_val_zero]
      ring
    · simp [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, Matrix.cons_val_one]
      rw [eq_div_iff hv]
      field_simp [hv]
      ring
  -- the circumcenter X of APB
  have d41 : dist (0 : Plane) !₂[p / 2, (c * (u ^ 2 + v ^ 2) - p * u) / (2 * v)]
      = dist !₂[p, 0] !₂[p / 2, (c * (u ^ 2 + v ^ 2) - p * u) / (2 * v)] := by
    rw [dist_eq_sqrt, dist_eq_sqrt]
    congr 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, PiLp.zero_apply]
    field_simp
    ring
  have d42 : dist (0 : Plane) !₂[p / 2, (c * (u ^ 2 + v ^ 2) - p * u) / (2 * v)]
      = dist !₂[c * u, c * v] !₂[p / 2, (c * (u ^ 2 + v ^ 2) - p * u) / (2 * v)] := by
    rw [dist_eq_sqrt, dist_eq_sqrt]
    congr 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, PiLp.zero_apply]
    field_simp
    ring
  obtain ⟨hO4, -⟩ := circum_eq hAPB d41 d42
  have hXe : X = !₂[p / 2, (c * (u ^ 2 + v ^ 2) - p * u) / (2 * v)] := hX.trans hO4.symm
  -- the final computation
  have hcert : 16 * u ^ 2 * v ^ 2 *
        ((p / 2 - b * u) ^ 2 +
          ((c * (u ^ 2 + v ^ 2) - p * u) / (2 * v) - u * (b * u - p) / v) ^ 2) -
      16 * u ^ 2 * v ^ 2 *
        (((b + c) * (u ^ 2 + v ^ 2) / (4 * u)) ^ 2 + ((c - b) * (u ^ 2 + v ^ 2) / (4 * v)) ^ 2)
      = (2 * u * p - (3 * b * u ^ 2 - b * v ^ 2 - c * (u ^ 2 + v ^ 2))) * (u ^ 2 + v ^ 2) *
        (2 * u * p + (3 * b * u ^ 2 - b * v ^ 2 - c * (u ^ 2 + v ^ 2)) - 8 * b * u ^ 2 +
          4 * c * u ^ 2) := by
    field_simp
    ring
  rw [hcon] at hcert
  have hE2 : 16 * u ^ 2 * v ^ 2 *
      ((p / 2 - b * u) ^ 2 + ((c * (u ^ 2 + v ^ 2) - p * u) / (2 * v) - u * (b * u - p) / v) ^ 2)
      = 16 * u ^ 2 * v ^ 2 *
        (((b + c) * (u ^ 2 + v ^ 2) / (4 * u)) ^ 2 + ((c - b) * (u ^ 2 + v ^ 2) / (4 * v)) ^ 2) := by
    linarith [hcert]
  have h16 : (16 : ℝ) * u ^ 2 * v ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hu)) (pow_ne_zero 2 hv)
  have hE : (p / 2 - b * u) ^ 2 +
        ((c * (u ^ 2 + v ^ 2) - p * u) / (2 * v) - u * (b * u - p) / v) ^ 2
      = ((b + c) * (u ^ 2 + v ^ 2) / (4 * u)) ^ 2 + ((c - b) * (u ^ 2 + v ^ 2) / (4 * v)) ^ 2 :=
    (mul_eq_mul_left_iff.1 hE2).resolve_right h16
  rw [← hR, hXe, hYc, dist_eq_sqrt, dist_eq_sqrt]
  congr 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, PiLp.zero_apply, zero_sub, neg_sq]
  exact hE

/-- Transporting an orthocenter along an affine isometry. -/
lemma orthocenter_map {V₂ P₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂]
    [MetricSpace P₂] [NormedAddTorsor V₂ P₂] (t : Triangle ℝ Pt) (f : Pt →ᵃⁱ[ℝ] P₂) :
    Triangle.orthocenter (t.map f.toAffineMap f.injective) = f (Triangle.orthocenter t) :=
  Affine.Simplex.mongePoint_map t f

snip end

problem usa2014_p5 {A B C H P X Y : Pt}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hH : H = Triangle.orthocenter (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt))
    (hAHC : AffineIndependent ℝ ![A, H, C])
    (hPs : P ∈ (⟨![A, H, C], hAHC⟩ : Triangle ℝ Pt).circumsphere)
    (hPbis : ∃ t : ℝ, 0 < t ∧ P -ᵥ A =
      t • ((dist A B)⁻¹ • (B -ᵥ A) + (dist A C)⁻¹ • (C -ᵥ A)))
    (hPA : P ≠ A)
    (hAPB : AffineIndependent ℝ ![A, P, B])
    (hX : X = (⟨![A, P, B], hAPB⟩ : Triangle ℝ Pt).circumcenter)
    (hAPC : AffineIndependent ℝ ![A, P, C])
    (hY : Y = Triangle.orthocenter (⟨![A, P, C], hAPC⟩ : Triangle ℝ Pt)) :
    dist X Y = (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).circumradius := by
  obtain ⟨t, ht, htv⟩ := hPbis
  have hfin : finrank ℝ V = 2 := Fact.out
  haveI : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ 1
  -- the vertices are distinct
  have hinj := hABC.injective
  have hABne : A ≠ B := fun hAB =>
    (by decide : (0 : Fin 3) ≠ 1) (hinj (by simpa using hAB))
  have hACne : A ≠ C := fun hAC =>
    (by decide : (0 : Fin 3) ≠ 2) (hinj (by simpa using hAC))
  have hc₀pos : 0 < dist A B := dist_pos.2 hABne
  have hb₀pos : 0 < dist A C := dist_pos.2 hACne
  have hc₀ne : dist A B ≠ 0 := hc₀pos.ne'
  have hb₀ne : dist A C ≠ 0 := hb₀pos.ne'
  -- unit vectors along AB and AC
  set uB : V := (dist A B)⁻¹ • (B -ᵥ A) with huB
  set uC : V := (dist A C)⁻¹ • (C -ᵥ A) with huC
  have huBnorm : ‖uB‖ = 1 := by
    rw [huB, norm_smul, norm_inv, Real.norm_of_nonneg hc₀pos.le, ← dist_eq_norm_vsub',
      inv_mul_cancel₀ hc₀ne]
  have huCnorm : ‖uC‖ = 1 := by
    rw [huC, norm_smul, norm_inv, Real.norm_of_nonneg hb₀pos.le, ← dist_eq_norm_vsub',
      inv_mul_cancel₀ hb₀ne]
  -- the bisector direction
  set s : V := uB + uC with hs
  have hsne : s ≠ 0 := by
    intro hs0
    have h1 : uB = -uC := by
      rw [hs] at hs0
      exact eq_neg_of_add_eq_zero_left hs0
    have h1' := congrArg ((dist A B) • ·) h1
    rw [huB, huC, smul_inv_smul₀ hc₀ne, smul_neg, smul_smul, ← neg_smul] at h1'
    exact not_affineIndependent_of_vsub_smul h1' hABC
  -- an orthonormal basis adapted to the bisector
  set e₁ : V := ‖s‖⁻¹ • s with he₁
  have hsnorm : ‖s‖ ≠ 0 := norm_ne_zero_iff.2 hsne
  have he₁norm : ‖e₁‖ = 1 := by
    rw [he₁, norm_smul, norm_inv, Real.norm_of_nonneg (norm_nonneg s), inv_mul_cancel₀ hsnorm]
  set o : Orientation ℝ V (Fin 2) := (Module.finBasisOfFinrankEq ℝ V hfin).orientation
  set J := o.rightAngleRotation with hJ
  set e₂ : V := J e₁ with he₂
  have he₂norm : ‖e₂‖ = 1 := by
    rw [he₂, hJ, LinearIsometryEquiv.norm_map, he₁norm]
  have he₁e₂ : ⟪e₁, e₂⟫ = 0 := by
    simp [he₂, hJ]
  have he₂e₁ : ⟪e₂, e₁⟫ = 0 := by
    rw [real_inner_comm]
    exact he₁e₂
  have horth : Orthonormal ℝ ![e₁, e₂] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [he₁norm, he₂norm, he₁e₂, he₂e₁]
  set BB : Basis (Fin 2) ℝ V := basisOfLinearIndependentOfCardEqFinrank horth.linearIndependent
    (by rw [Fintype.card_fin, hfin])
  have hBcoe : ⇑BB = ![e₁, e₂] := Basis.coe_mk ..
  set oB : OrthonormalBasis (Fin 2) ℝ V := BB.toOrthonormalBasis (hBcoe.symm ▸ horth)
  have hoBi : ∀ i, oB i = ![e₁, e₂] i := fun i =>
    (congrFun (Module.Basis.coe_toOrthonormalBasis BB _) i).trans (congrFun hBcoe i)
  set φ : V ≃ₗᵢ[ℝ] Plane := oB.repr with hφ
  have hφi : ∀ x i, φ x i = ⟪![e₁, e₂] i, x⟫ := fun x i => by
    rw [hφ, OrthonormalBasis.repr_apply_apply, hoBi i]
  -- the affine isometry sending A to 0 and the bisector to the x-axis
  set Ψ : Pt ≃ᵃⁱ[ℝ] Plane := AffineIsometryEquiv.mk' (fun q => φ (q -ᵥ A)) φ A
    (fun q => by simp)
  have hΨq : ∀ q, Ψ q = φ (q -ᵥ A) := fun q => rfl
  have hΨA : Ψ A = 0 := by
    rw [hΨq, vsub_self, map_zero]
  -- images of B, C, P
  have hBA : B -ᵥ A = (dist A B) • uB := by
    rw [huB]
    exact (smul_inv_smul₀ hc₀ne _).symm
  have hCA : C -ᵥ A = (dist A C) • uC := by
    rw [huC]
    exact (smul_inv_smul₀ hb₀ne _).symm
  set u := (φ uB) 0 with hu
  set v := (φ uB) 1 with hv
  have hφB : φ uB = !₂[u, v] := by
    refine plane_ext ?_ ?_
    · simp only [Matrix.cons_val_zero]
      exact hu.symm
    · simp only [Matrix.cons_val_one]
      exact hv.symm
  have hΨB : Ψ B = !₂[(dist A B) * u, (dist A B) * v] := by
    rw [hΨq, hBA, map_smul, hφB]
    refine plane_ext ?_ ?_ <;>
      simp [PiLp.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  -- key inner product computations
  have hφB0 : (φ uB) 0 = ⟪e₁, uB⟫ := by
    rw [hφi, Matrix.cons_val_zero]
  have hφB1 : (φ uB) 1 = ⟪e₂, uB⟫ := by
    rw [hφi, Matrix.cons_val_one, Matrix.cons_val_zero]
  have hφC0 : (φ uC) 0 = ⟪e₁, uC⟫ := by
    rw [hφi, Matrix.cons_val_zero]
  have hφC1 : (φ uC) 1 = ⟪e₂, uC⟫ := by
    rw [hφi, Matrix.cons_val_one, Matrix.cons_val_zero]
  have hφs0 : (φ s) 0 = ‖s‖ := by
    rw [hφi, Matrix.cons_val_zero, he₁, real_inner_smul_left, real_inner_self_eq_norm_sq,
      inv_mul_eq_div, pow_two, div_eq_iff hsnorm]
  have hφs1 : (φ s) 1 = 0 := by
    rw [hφi, Matrix.cons_val_one, Matrix.cons_val_zero, he₂, hJ, he₁, map_smul,
      real_inner_smul_left, o.inner_rightAngleRotation_self, mul_zero]
  have kB' : ⟪s, uB⟫ = 1 + ⟪uB, uC⟫ := by
    rw [hs, inner_add_left, real_inner_self_eq_norm_sq, huBnorm, one_pow, real_inner_comm uB uC]
  have kB : ⟪e₁, uB⟫ = ‖s‖⁻¹ * (1 + ⟪uB, uC⟫) := by
    rw [he₁, real_inner_smul_left, kB']
  have kC' : ⟪s, uC⟫ = 1 + ⟪uB, uC⟫ := by
    rw [hs, inner_add_left, real_inner_self_eq_norm_sq, huCnorm, one_pow, add_comm]
  have kC : ⟪e₁, uC⟫ = ‖s‖⁻¹ * (1 + ⟪uB, uC⟫) := by
    rw [he₁, real_inner_smul_left, kC']
  have hC0 : (φ uC) 0 = u := by
    rw [hφC0, kC, ← kB, ← hφB0]
  have hC1 : (φ uC) 1 = -v := by
    have h1 : ⟪e₂, uB⟫ + ⟪e₂, uC⟫ = 0 := by
      rw [← inner_add_right, ← hs, he₂, hJ, he₁, map_smul, real_inner_smul_left,
        o.inner_rightAngleRotation_self, mul_zero]
    have h2 : ⟪e₂, uC⟫ = -⟪e₂, uB⟫ := by linarith [h1]
    rw [hφC1, h2, ← hφB1, hv]
  have hφC : φ uC = !₂[u, -v] := by
    refine plane_ext ?_ ?_
    · rw [hC0]
      simp only [Matrix.cons_val_zero]
    · rw [hC1]
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  have hΨC : Ψ C = !₂[(dist A C) * u, -((dist A C) * v)] := by
    rw [hΨq, hCA, map_smul, hφC]
    refine plane_ext ?_ ?_ <;>
      simp [PiLp.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, mul_neg]
  -- the image of P
  have hφs : φ s = !₂[‖s‖, 0] := by
    refine plane_ext ?_ ?_
    · rw [hφs0]
      simp only [Matrix.cons_val_zero]
    · rw [hφs1]
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  have hΨP : Ψ P = !₂[t * ‖s‖, 0] := by
    rw [hΨq, htv, map_smul, hφs]
    refine plane_ext ?_ ?_ <;>
      simp [PiLp.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero]
  -- u ≠ 0 since s ≠ 0
  have hu2 : u ≠ 0 := by
    have hsnorm2 : ‖s‖ ^ 2 = 2 + 2 * ⟪uB, uC⟫ := by
      rw [← real_inner_self_eq_norm_sq, hs, inner_add_left, inner_add_right, inner_add_right,
        real_inner_self_eq_norm_sq, huBnorm, one_pow, real_inner_self_eq_norm_sq, huCnorm,
        one_pow, real_inner_comm uB uC]
      ring
    have h1m : 1 + ⟪uB, uC⟫ = ‖s‖ ^ 2 / 2 := by linarith [hsnorm2]
    have hue : u = ‖s‖ / 2 := by
      rw [hu, hφB0, kB, h1m, inv_mul_eq_div, pow_two, div_eq_iff hsnorm]
      ring
    rw [hue]
    have hsp : 0 < ‖s‖ := norm_pos_iff.2 hsne
    linarith
  -- v ≠ 0 since the triangle is genuine
  have hv2 : v ≠ 0 := by
    intro hv0
    have h1 : φ uB = φ uC := by
      rw [hφB, hφC, hv0, neg_zero]
    have h2 : uB = uC := φ.injective h1
    have h3 : B -ᵥ A = (dist A B * (dist A C)⁻¹) • (C -ᵥ A) := by
      have h2' := congrArg ((dist A B) • ·) h2
      rw [huB, huC, smul_inv_smul₀ hc₀ne, smul_smul] at h2'
      exact h2'
    exact not_affineIndependent_of_vsub_smul h3 hABC
  -- mapped hypotheses
  have hmap : ∀ (p : Fin 3 → Pt),
      (Ψ.toAffineIsometry.toAffineMap ∘ p) = ![Ψ (p 0), Ψ (p 1), Ψ (p 2)] := by
    intro p
    ext i
    fin_cases i <;> rfl
  have hABC' : AffineIndependent ℝ ![Ψ A, Ψ B, Ψ C] := by
    have h := hABC.map' Ψ.toAffineIsometry.toAffineMap Ψ.toAffineIsometry.injective
    rw [hmap] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at h
    exact h
  have hAHC' : AffineIndependent ℝ ![Ψ A, Ψ H, Ψ C] := by
    have h := hAHC.map' Ψ.toAffineIsometry.toAffineMap Ψ.toAffineIsometry.injective
    rw [hmap] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at h
    exact h
  have hAPB' : AffineIndependent ℝ ![Ψ A, Ψ P, Ψ B] := by
    have h := hAPB.map' Ψ.toAffineIsometry.toAffineMap Ψ.toAffineIsometry.injective
    rw [hmap] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at h
    exact h
  have hAPC' : AffineIndependent ℝ ![Ψ A, Ψ P, Ψ C] := by
    have h := hAPC.map' Ψ.toAffineIsometry.toAffineMap Ψ.toAffineIsometry.injective
    rw [hmap] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at h
    exact h
  have hTABC : (⟨![Ψ A, Ψ B, Ψ C], hABC'⟩ : Triangle ℝ Plane) =
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).map Ψ.toAffineIsometry.toAffineMap Ψ.toAffineIsometry.injective := by
    ext i <;> fin_cases i <;> rfl
  have hTAHC : (⟨![Ψ A, Ψ H, Ψ C], hAHC'⟩ : Triangle ℝ Plane) =
      (⟨![A, H, C], hAHC⟩ : Triangle ℝ Pt).map Ψ.toAffineIsometry.toAffineMap Ψ.toAffineIsometry.injective := by
    ext i <;> fin_cases i <;> rfl
  have hTAPB : (⟨![Ψ A, Ψ P, Ψ B], hAPB'⟩ : Triangle ℝ Plane) =
      (⟨![A, P, B], hAPB⟩ : Triangle ℝ Pt).map Ψ.toAffineIsometry.toAffineMap Ψ.toAffineIsometry.injective := by
    ext i <;> fin_cases i <;> rfl
  have hTAPC : (⟨![Ψ A, Ψ P, Ψ C], hAPC'⟩ : Triangle ℝ Plane) =
      (⟨![A, P, C], hAPC⟩ : Triangle ℝ Pt).map Ψ.toAffineIsometry.toAffineMap Ψ.toAffineIsometry.injective := by
    ext i <;> fin_cases i <;> rfl
  have hH' : Ψ H = Triangle.orthocenter (⟨![Ψ A, Ψ B, Ψ C], hABC'⟩ : Triangle ℝ Plane) := by
    rw [hH, hTABC]
    exact (orthocenter_map (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt) Ψ.toAffineIsometry).symm
  have hX' : Ψ X = (⟨![Ψ A, Ψ P, Ψ B], hAPB'⟩ : Triangle ℝ Plane).circumcenter := by
    rw [hX, hTAPB]
    exact (Affine.Simplex.circumcenter_map (⟨![A, P, B], hAPB⟩ : Triangle ℝ Pt) Ψ.toAffineIsometry).symm
  have hY' : Ψ Y = Triangle.orthocenter (⟨![Ψ A, Ψ P, Ψ C], hAPC'⟩ : Triangle ℝ Plane) := by
    rw [hY, hTAPC]
    exact (orthocenter_map (⟨![A, P, C], hAPC⟩ : Triangle ℝ Pt) Ψ.toAffineIsometry).symm
  have hPs' : Ψ P ∈ (⟨![Ψ A, Ψ H, Ψ C], hAHC'⟩ : Triangle ℝ Plane).circumsphere := by
    have h1 : dist P (⟨![A, H, C], hAHC⟩ : Triangle ℝ Pt).circumcenter =
        (⟨![A, H, C], hAHC⟩ : Triangle ℝ Pt).circumradius := by
      have hm := mem_sphere.1 hPs
      rwa [Affine.Simplex.circumsphere_center, Affine.Simplex.circumsphere_radius] at hm
    rw [mem_sphere, hTAHC, Affine.Simplex.circumsphere_center,
      Affine.Simplex.circumsphere_radius, Affine.Simplex.circumcenter_map,
      Affine.Simplex.circumradius_map, AffineIsometryEquiv.coe_toAffineIsometry, Ψ.dist_map]
    exact h1
  have hPA' : Ψ P ≠ Ψ A := Ψ.injective.ne hPA
  -- apply the coordinate lemma
  have hresult := coord_main hu2 hv2 hΨA hΨB hΨC hΨP hABC' hH' hAHC' hPs' hPA' hAPB' hX' hAPC'
    hY'
  rw [hTABC, Affine.Simplex.circumradius_map] at hresult
  rw [← hresult, Ψ.dist_map]

end Usa2014P5
