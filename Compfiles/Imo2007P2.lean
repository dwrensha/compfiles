/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Geometry.Euclidean.Sphere.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 2007, Problem 2

Consider five points A, B, C, D and E such that ABCD is a parallelogram and
BCED is a cyclic quadrilateral. Let ℓ be a line passing through A. Suppose
that ℓ intersects the interior of the segment DC at F and intersects line
BC at G. Suppose also that EF = EG = EC. Prove that ℓ is the bisector of
angle DAB.
-/

open Affine AffineMap EuclideanGeometry Module

open scoped RealInnerProductSpace InnerProductSpace EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

namespace Imo2007P2

snip begin

/-- A point on the line through `x` and `y` can be written in parametric form. -/
theorem mem_line {x y G : P} (h : G ∈ line[ℝ, x, y]) :
    ∃ r : ℝ, r • (y -ᵥ x) = G -ᵥ x := by
  have hx : x ∈ line[ℝ, x, y] := left_mem_affineSpan_pair ℝ x y
  rw [← AffineSubspace.vsub_right_mem_direction_iff_mem hx G,
    direction_affineSpan] at h
  rw [vectorSpan_eq_span_vsub_set_right ℝ (Set.mem_insert x {y})] at h
  simp only [Set.image_pair, vsub_self, Submodule.span_insert_zero] at h
  exact Submodule.mem_span_singleton.mp h

/-- If `u, v` are linearly independent, a linear combination of them that
vanishes has zero coefficients. -/
theorem eq_zero_of_pair {u v : V} (hli : LinearIndependent ℝ ![u, v]) {c d : ℝ}
    (h : c • u + d • v = 0) : c = 0 ∧ d = 0 := by
  have h2 : ∀ i : Fin 2, ![c, d] i = 0 := by
    refine Fintype.linearIndependent_iff.mp hli ![c, d] ?_
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact h
  exact ⟨h2 0, h2 1⟩

/-- The range of a two-element family `![u, v]`. -/
theorem range_pair {α : Type*} (u v : α) : Set.range ![u, v] = {u, v} := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

snip end

problem imo2007_p2 [Fact (finrank ℝ V = 2)] {A B C D E F G : P}
    (hABCD : C -ᵥ B = D -ᵥ A)
    (hli : LinearIndependent ℝ ![B -ᵥ A, D -ᵥ A])
    (hcyc : Cospherical ({B, C, D, E} : Set P))
    (hF : Sbtw ℝ D F C)
    (hG : G ∈ line[ℝ, B, C])
    (hℓ : G ∈ line[ℝ, A, F])
    (hEF : dist E F = dist E C)
    (hEG : dist E G = dist E C) :
    ∠ D A F = ∠ F A B := by
  -- side vectors of the parallelogram, with `A` as base point
  set u := B -ᵥ A with hu
  set v := D -ᵥ A with hv
  have hCv : C -ᵥ A = u + v := by
    have h1 : C -ᵥ A = (C -ᵥ B) + u := (vsub_add_vsub_cancel C B A).symm
    rw [h1, hABCD, add_comm]
  have hu0 : u ≠ 0 := by
    have h := hli.ne_zero (0 : Fin 2)
    simpa using h
  have hv0 : v ≠ 0 := by
    have h := hli.ne_zero (1 : Fin 2)
    simpa using h
  -- parametrization of `F` on the open segment `DC`
  obtain ⟨hW, hFD, hFC⟩ := hF
  rw [Wbtw, affineSegment, Set.mem_image] at hW
  obtain ⟨b, hbI, hbl⟩ := hW
  rw [Set.mem_Icc] at hbI
  have hb0 : 0 < b := by
    rcases eq_or_lt_of_le hbI.1 with h | h
    · exfalso
      apply hFD
      rw [← hbl, ← h, lineMap_apply_zero]
    · exact h
  have hb1 : b < 1 := by
    rcases eq_or_lt_of_le hbI.2 with h | h
    · exfalso
      apply hFC
      rw [← hbl, h, lineMap_apply_one]
    · exact h
  have hFv : F -ᵥ A = v + b • u := by
    have h1 : F -ᵥ D = b • (C -ᵥ D) := by
      rw [← hbl]
      exact lineMap_vsub_left D C b
    have h2 : C -ᵥ D = u := by
      have h3 : C -ᵥ D = (C -ᵥ A) - (D -ᵥ A) := (vsub_sub_vsub_cancel_right C D A).symm
      rw [h3, hCv, hv, add_sub_cancel_right]
    have h4 : F -ᵥ A = (F -ᵥ D) + v := (vsub_add_vsub_cancel F D A).symm
    rw [h4, h1, h2, add_comm]
  -- parametrization of `G` on the line `BC`
  obtain ⟨t, ht⟩ := mem_line hG
  have hGv : G -ᵥ A = u + t • v := by
    have h1 : G -ᵥ A = (G -ᵥ B) + u := (vsub_add_vsub_cancel G B A).symm
    rw [h1, ← ht, hABCD, add_comm]
  -- collinearity of `A, F, G` gives `b * t = 1`
  obtain ⟨rr, hrr⟩ := mem_line hℓ
  have hvec : (1 - rr * b) • u + (t - rr) • v = 0 := by
    have h1 : u + t • v = rr • (v + b • u) := by
      rw [← hGv, ← hFv]
      exact hrr.symm
    have h2 : u + t • v - rr • (v + b • u) = (1 - rr * b) • u + (t - rr) • v := by
      module
    rw [h1, sub_self] at h2
    exact h2.symm
  obtain ⟨hc1, hc2⟩ := eq_zero_of_pair hli hvec
  have hbt : b * t = 1 := by
    have h1 : rr * b = 1 := by linarith [hc1]
    have h2 : t = rr := sub_eq_zero.mp hc2
    rw [h2, mul_comm]
    exact h1
  -- `E -ᵥ A` lies in the span of `u, v`, which is the whole plane
  have htop : Submodule.span ℝ (Set.range ![u, v]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simpa using (Fact.out : finrank ℝ V = 2).symm)
  obtain ⟨α, β, hE⟩ : ∃ α β : ℝ, α • u + β • v = E -ᵥ A := by
    have hmem : E -ᵥ A ∈ Submodule.span ℝ (Set.range ![u, v]) := by
      rw [htop]
      exact Submodule.mem_top
    rw [range_pair, Submodule.mem_span_pair] at hmem
    exact hmem
  -- the equation `EF = EC`, squared and expanded
  have hECe : E -ᵥ C = (E -ᵥ A) - (C -ᵥ A) := (vsub_sub_vsub_cancel_right E C A).symm
  have hEFn : ‖E -ᵥ F‖ ^ 2 = ‖E -ᵥ C‖ ^ 2 := by
    rw [← dist_eq_norm_vsub, ← dist_eq_norm_vsub, hEF]
  have hEFe : E -ᵥ F = (E -ᵥ A) - (F -ᵥ A) := (vsub_sub_vsub_cancel_right E F A).symm
  rw [hEFe, hECe, ← hE, hFv, hCv] at hEFn
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_add_left,
    inner_add_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm u v] at hEFn
  ring_nf at hEFn
  have hbne : (1 : ℝ) - b ≠ 0 := by
    have h : b ≠ 1 := ne_of_lt hb1
    intro h1
    apply h
    linarith
  have hI1 : 2 * (α * ⟪u, u⟫_ℝ + β * ⟪u, v⟫_ℝ) = (1 + b) * ⟪u, u⟫_ℝ + 2 * ⟪u, v⟫_ℝ :=
    mul_left_cancel₀ hbne (by linear_combination hEFn)
  -- the equation `EG = EC`, squared and expanded
  have hEGn : ‖E -ᵥ G‖ ^ 2 = ‖E -ᵥ C‖ ^ 2 := by
    rw [← dist_eq_norm_vsub, ← dist_eq_norm_vsub, hEG]
  have hEGe : E -ᵥ G = (E -ᵥ A) - (G -ᵥ A) := (vsub_sub_vsub_cancel_right E G A).symm
  rw [hEGe, hECe, ← hE, hGv, hCv] at hEGn
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_add_left,
    inner_add_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm u v] at hEGn
  ring_nf at hEGn
  have htne : (1 : ℝ) - t ≠ 0 := by
    intro h1
    have h2 : t = 1 := by linarith
    rw [h2, mul_one] at hbt
    exact (ne_of_lt hb1) hbt
  have hI2 : 2 * (α * ⟪u, v⟫_ℝ + β * ⟪v, v⟫_ℝ) = (1 + t) * ⟪v, v⟫_ℝ + 2 * ⟪u, v⟫_ℝ :=
    mul_left_cancel₀ htne (by linear_combination hEGn)
  -- the cosphericality condition: let `O` be the common center
  obtain ⟨O, R, hR⟩ := hcyc
  have hOB : ‖B -ᵥ O‖ = R := by
    rw [← dist_eq_norm_vsub]
    exact hR B (by simp)
  have hOC : ‖C -ᵥ O‖ = R := by
    rw [← dist_eq_norm_vsub]
    exact hR C (by simp)
  have hOD : ‖D -ᵥ O‖ = R := by
    rw [← dist_eq_norm_vsub]
    exact hR D (by simp)
  have hOE : ‖E -ᵥ O‖ = R := by
    rw [← dist_eq_norm_vsub]
    exact hR E (by simp)
  have hCOe : C -ᵥ O = (C -ᵥ A) - (O -ᵥ A) := (vsub_sub_vsub_cancel_right C O A).symm
  have hDOe : D -ᵥ O = (D -ᵥ A) - (O -ᵥ A) := (vsub_sub_vsub_cancel_right D O A).symm
  have hBOe : B -ᵥ O = (B -ᵥ A) - (O -ᵥ A) := (vsub_sub_vsub_cancel_right B O A).symm
  have hEOe : E -ᵥ O = (E -ᵥ A) - (O -ᵥ A) := (vsub_sub_vsub_cancel_right E O A).symm
  -- from `OC = OD`: the inner product of `O -ᵥ A` with `u`
  have hs1 : ‖C -ᵥ O‖ ^ 2 = ‖D -ᵥ O‖ ^ 2 := by rw [hOC, hOD]
  rw [hCOe, hDOe, hCv, ← hv] at hs1
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_add_left,
    inner_add_right, real_inner_comm u v,
    real_inner_comm u (O -ᵥ A), real_inner_comm v (O -ᵥ A)] at hs1
  ring_nf at hs1
  have hoU : ⟪u, u⟫_ℝ + 2 * ⟪u, v⟫_ℝ = 2 * ⟪u, O -ᵥ A⟫_ℝ := by
    linear_combination hs1
  -- from `OB = OD`: the inner product of `O -ᵥ A` with `v`
  have hs2 : ‖B -ᵥ O‖ ^ 2 = ‖D -ᵥ O‖ ^ 2 := by rw [hOB, hOD]
  rw [hBOe, hDOe, ← hu, ← hv] at hs2
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    real_inner_comm u (O -ᵥ A), real_inner_comm v (O -ᵥ A)] at hs2
  ring_nf at hs2
  have hoV : ⟪v, v⟫_ℝ + 2 * ⟪u, v⟫_ℝ = 2 * ⟪v, O -ᵥ A⟫_ℝ := by
    linear_combination -hs2 + hoU
  -- from `OE = OB`: a third equation on `α, β`
  have hs3 : ‖E -ᵥ O‖ ^ 2 = ‖B -ᵥ O‖ ^ 2 := by rw [hOE, hOB]
  rw [hEOe, hBOe, ← hE, ← hu] at hs3
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_add_left,
    inner_add_right, real_inner_smul_left, real_inner_smul_right, real_inner_comm u v,
    real_inner_comm u (O -ᵥ A), real_inner_comm v (O -ᵥ A)] at hs3
  ring_nf at hs3
  have hI3 : α * ((b - 1) * ⟪u, u⟫_ℝ - 2 * ⟪u, v⟫_ℝ)
      + β * ((t - 1) * ⟪v, v⟫_ℝ - 2 * ⟪u, v⟫_ℝ) + 4 * ⟪u, v⟫_ℝ = 0 := by
    linear_combination 2 * hs3 - α * hI1 - β * hI2 + (2 - 2 * α) * hoU - 2 * β * hoV
  -- eliminating `α, β` from the three equations
  have hp : (0 : ℝ) < ⟪u, u⟫_ℝ := by
    rw [real_inner_self_eq_norm_sq]
    exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hu0)
  have hq : (0 : ℝ) < ⟪v, v⟫_ℝ := by
    rw [real_inner_self_eq_norm_sq]
    exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv0)
  have hmain4 : (⟪u, u⟫_ℝ * ⟪v, v⟫_ℝ) * (b ^ 2 * ⟪u, u⟫_ℝ + ⟪v, v⟫_ℝ * t ^ 2)
      = (⟪u, u⟫_ℝ * ⟪v, v⟫_ℝ)
        * (⟪u, u⟫_ℝ + ⟪v, v⟫_ℝ + 2 * ⟪u, v⟫_ℝ * b * t - 2 * ⟪u, v⟫_ℝ) := by
    linear_combination
      2 * (⟪u, u⟫_ℝ * ⟪v, v⟫_ℝ - ⟪u, v⟫_ℝ ^ 2) * hI3 -
      (⟪v, v⟫_ℝ * ((b - 1) * ⟪u, u⟫_ℝ - 2 * ⟪u, v⟫_ℝ)
        - ⟪u, v⟫_ℝ * ((t - 1) * ⟪v, v⟫_ℝ - 2 * ⟪u, v⟫_ℝ)) * hI1 -
      (⟪u, u⟫_ℝ * ((t - 1) * ⟪v, v⟫_ℝ - 2 * ⟪u, v⟫_ℝ)
        - ⟪u, v⟫_ℝ * ((b - 1) * ⟪u, u⟫_ℝ - 2 * ⟪u, v⟫_ℝ)) * hI2
  have hmain : b ^ 2 * ⟪u, u⟫_ℝ + ⟪v, v⟫_ℝ * t ^ 2
      = ⟪u, u⟫_ℝ + ⟪v, v⟫_ℝ + 2 * ⟪u, v⟫_ℝ * b * t - 2 * ⟪u, v⟫_ℝ :=
    mul_left_cancel₀ (ne_of_gt (mul_pos hp hq)) hmain4
  -- using `b * t = 1`, this factors as `(b² - 1) * (b² * |u|² - |v|²) = 0`
  have h2 : b ^ 2 * ⟪u, u⟫_ℝ + ⟪v, v⟫_ℝ * t ^ 2 = ⟪u, u⟫_ℝ + ⟪v, v⟫_ℝ := by
    linear_combination hmain + 2 * ⟪u, v⟫_ℝ * hbt
  have hbt2 : b ^ 2 * t ^ 2 = 1 := by rw [← mul_pow, hbt, one_pow]
  have hfinal : (b ^ 2 - 1) * (b ^ 2 * ⟪u, u⟫_ℝ - ⟪v, v⟫_ℝ) = 0 := by
    linear_combination b ^ 2 * h2 - ⟪v, v⟫_ℝ * hbt2
  have hb2ne : b ^ 2 - 1 ≠ 0 := by
    have h : b ^ 2 < 1 := pow_lt_one₀ hb0.le hb1 (by norm_num : (2 : ℕ) ≠ 0)
    intro h1
    rw [sub_eq_zero] at h1
    linarith
  have hbq : b ^ 2 * ⟪u, u⟫_ℝ = ⟪v, v⟫_ℝ := by
    rcases mul_eq_zero.mp hfinal with h | h
    · exact absurd h hb2ne
    · rw [sub_eq_zero] at h
      exact h
  -- the equality of cosines gives the equality of angles
  have heF0 : v + b • u ≠ 0 := by
    intro h
    have h1 : b • u + (1 : ℝ) • v = 0 := by rwa [one_smul, add_comm]
    obtain ⟨-, h2⟩ := eq_zero_of_pair hli h1
    exact one_ne_zero h2
  have hNu : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu0
  have hNeF : ‖v + b • u‖ ≠ 0 := norm_ne_zero_iff.mpr heF0
  have hNv : ‖v‖ = b * ‖u‖ := by
    rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, ← hbq,
      Real.sqrt_mul (sq_nonneg b), Real.sqrt_sq hb0.le]
  have hinner1 : ⟪v, v + b • u⟫_ℝ = b * (⟪u, v⟫_ℝ + b * ⟪u, u⟫_ℝ) := by
    simp only [inner_add_right, real_inner_smul_right, real_inner_comm u v]
    linear_combination -hbq
  have hinner2 : ⟪v + b • u, u⟫_ℝ = ⟪u, v⟫_ℝ + b * ⟪u, u⟫_ℝ := by
    simp only [inner_add_left, real_inner_smul_left, real_inner_comm u v]
  show InnerProductGeometry.angle (D -ᵥ A) (F -ᵥ A) = InnerProductGeometry.angle (F -ᵥ A) (B -ᵥ A)
  rw [InnerProductGeometry.angle, InnerProductGeometry.angle, ← hv, hFv, ← hu,
    hNv, hinner1, hinner2]
  field_simp

end Imo2007P2
