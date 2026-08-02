/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Projection
public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1984, Problem 4

Let ABCD be a convex quadrilateral such that the line CD is a tangent
to the circle on AB as diameter. Prove that the line AB is a tangent to
the circle on CD as diameter if and only if the lines BC and AD are parallel.

# Formalization note

We work in the Euclidean plane `EuclideanSpace ℝ (Fin 2)`.

* The circle on a segment `XY` as diameter is the circle with center
  `midpoint ℝ X Y` and radius `dist X Y / 2`. A line `ℓ` is tangent to a
  circle with center `O` and radius `r` iff the distance from `O` to `ℓ`
  equals `r`, i.e. `dist O (orthogonalProjection ℓ O) = r`.
* `ConvexQuad A B C D` encodes "`ABCD` is a strictly convex quadrilateral
  with vertices in this order": the four cross products of consecutive edge
  vectors are all positive or all negative.
-/

namespace Imo1984P4

open Affine EuclideanGeometry

open scoped RealInnerProductSpace

/-- Points of the Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- The 2-dimensional cross product (a scalar) of two vectors of the plane. -/
def cross (u v : Pt) : ℝ := u 0 * v 1 - u 1 * v 0

/-- `ConvexQuad A B C D` says that `ABCD` is a strictly convex quadrilateral
with vertices in this order. -/
def ConvexQuad (A B C D : Pt) : Prop :=
  (0 < cross (B - A) (C - B) ∧ 0 < cross (C - B) (D - C) ∧
      0 < cross (D - C) (A - D) ∧ 0 < cross (A - D) (B - A)) ∨
    (cross (B - A) (C - B) < 0 ∧ cross (C - B) (D - C) < 0 ∧
      cross (D - C) (A - D) < 0 ∧ cross (A - D) (B - A) < 0)

snip begin

/-- Extensionality for points of the plane. -/
theorem Pt.ext {x y : Pt} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  apply WithLp.ofLp_injective (p := 2)
  funext i
  fin_cases i <;> assumption

/-- The inner product in coordinates. -/
theorem inner_pt (u v : Pt) : ⟪u, v⟫ = u 0 * v 0 + u 1 * v 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, RCLike.inner_apply]
  simp only [conj_trivial]
  ring

/-- The squared norm in coordinates. -/
theorem norm_sq_pt (u : Pt) : ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
  congr 1 <;> simp [sq_abs]

/-- The Lagrange identity relating cross product, norm and inner product. -/
theorem cross_sq (u v : Pt) : cross u v ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2 := by
  rw [cross, inner_pt, norm_sq_pt, norm_sq_pt]
  ring

/-- In the plane, a vector with vanishing cross product with a nonzero vector
is a scalar multiple of it. -/
theorem exists_smul_of_cross_eq_zero {u v : Pt} (h : cross u v = 0) (hu : u ≠ 0) :
    ∃ t : ℝ, v = t • u := by
  have hu' : u 0 ≠ 0 ∨ u 1 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hu (Pt.ext (by simpa using hcon.1) (by simpa using hcon.2))
  simp only [cross, sub_eq_zero] at h
  rcases hu' with h0 | h1
  · refine ⟨v 0 / u 0, Pt.ext ?_ ?_⟩
    · rw [PiLp.smul_apply, smul_eq_mul, div_mul_cancel₀ _ h0]
    · rw [PiLp.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff h0]
      linear_combination h
  · refine ⟨v 1 / u 1, Pt.ext ?_ ?_⟩
    · rw [PiLp.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff h1]
      linear_combination h.symm
    · rw [PiLp.smul_apply, smul_eq_mul, div_mul_cancel₀ _ h1]

/-- The distance from a point to the line through two distinct points,
expressed with the cross product. -/
theorem dist_orthogonalProjection_sq {C D M : Pt} (hCD : C ≠ D) :
    dist M (orthogonalProjection line[ℝ, C, D] M : Pt) ^ 2 =
      cross (D - C) (M - C) ^ 2 / dist C D ^ 2 := by
  set P := (orthogonalProjection line[ℝ, C, D] M : Pt) with hP
  have hPmem : P ∈ line[ℝ, C, D] := orthogonalProjection_mem _
  have horth : M -ᵥ P ∈ (line[ℝ, C, D]).directionᗮ :=
    vsub_orthogonalProjection_mem_direction_orthogonal _ _
  have hDCmem : D -ᵥ C ∈ (line[ℝ, C, D]).direction :=
    AffineSubspace.vsub_mem_direction (right_mem_affineSpan_pair ℝ C D)
      (left_mem_affineSpan_pair ℝ C D)
  have hPCmem : P -ᵥ C ∈ (line[ℝ, C, D]).direction :=
    AffineSubspace.vsub_mem_direction hPmem (left_mem_affineSpan_pair ℝ C D)
  rw [direction_affineSpan, vectorSpan_pair] at hPCmem
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hPCmem
  have hinner : ⟪(D : Pt) - C, M - P⟫ = 0 := by
    rw [← vsub_eq_sub, ← vsub_eq_sub]
    exact Submodule.inner_right_of_mem_orthogonal hDCmem horth
  have e1 : cross (D - C) (M - C) = cross (D - C) (M - P) := by
    have hMC : M - C = (M - P) + (P - C) := by abel
    have hPC : P - C = t • (C - D) := by
      rw [← vsub_eq_sub P C, ← vsub_eq_sub C D, ← ht]
    rw [hMC, hPC]
    simp only [cross, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have e2 : cross (D - C) (M - P) ^ 2 = ‖D - C‖ ^ 2 * ‖M - P‖ ^ 2 := by
    rw [cross_sq, hinner]
    simp
  rw [e1, e2, dist_eq_norm M P, dist_eq_norm C D, norm_sub_rev C D,
    eq_div_iff (pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr
      (fun e => hCD e.symm))))]
  ring

/-- Two lines of the plane are parallel iff the cross product of their
direction vectors vanishes. -/
theorem parallel_iff_cross {A B C D : Pt} (hCB : C ≠ B) (hDA : D ≠ A) :
    line[ℝ, B, C] ∥ line[ℝ, A, D] ↔ cross (C - B) (D - A) = 0 := by
  constructor
  · rintro ⟨v, hv⟩
    have hD : D ∈ line[ℝ, A, D] := right_mem_affineSpan_pair ℝ A D
    have hA : A ∈ line[ℝ, A, D] := left_mem_affineSpan_pair ℝ A D
    rw [hv] at hD hA
    obtain ⟨y, hy, rfl⟩ := AffineSubspace.mem_map.mp hD
    obtain ⟨z, hz, hz'⟩ := AffineSubspace.mem_map.mp hA
    simp only [AffineEquiv.coe_toAffineMap, AffineEquiv.constVAdd_apply] at hz' ⊢
    have hsub : (v +ᵥ y) -ᵥ A ∈ (line[ℝ, B, C]).direction := by
      have e : (v +ᵥ y) -ᵥ A = y -ᵥ z := by
        rw [← hz']
        simp only [vsub_eq_sub, vadd_eq_add]
        abel
      rw [e]
      exact AffineSubspace.vsub_mem_direction hy hz
    rw [direction_affineSpan, vectorSpan_pair] at hsub
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hsub
    have e : (v +ᵥ y) - A = t • (B - C) := by
      rw [← vsub_eq_sub, ← ht, ← vsub_eq_sub]
    rw [e]
    simp only [cross, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  · intro h
    obtain ⟨t, ht⟩ := exists_smul_of_cross_eq_zero h (sub_ne_zero.mpr hCB)
    have ht0 : t ≠ 0 := by
      intro e
      rw [e, zero_smul, sub_eq_zero] at ht
      exact hDA ht
    refine ⟨A -ᵥ B, ?_⟩
    rw [AffineSubspace.map_span]
    have h1 : (↑(AffineEquiv.constVAdd ℝ Pt (A -ᵥ B)) : Pt →ᵃ[ℝ] Pt) B = A := by
      simp [AffineEquiv.constVAdd_apply]
    have h2 : (↑(AffineEquiv.constVAdd ℝ Pt (A -ᵥ B)) : Pt →ᵃ[ℝ] Pt) C = A + (C - B) := by
      simp only [AffineEquiv.coe_toAffineMap, AffineEquiv.constVAdd_apply]
      rw [vsub_eq_sub, vadd_eq_add]
      abel
    rw [Set.image_insert_eq, Set.image_singleton, h1, h2]
    apply AffineSubspace.ext_of_direction_eq
    · rw [direction_affineSpan, direction_affineSpan, vectorSpan_pair, vectorSpan_pair]
      have e1 : A -ᵥ D = (-t) • (C - B) := by
        rw [vsub_eq_sub, neg_smul, ← ht]
        abel
      have e2 : A -ᵥ (A + (C - B)) = (-1) • (C - B) := by
        rw [vsub_eq_sub, neg_one_smul]
        abel
      rw [e1, e2]
      apply le_antisymm <;>
        rw [Submodule.span_le, Set.singleton_subset_iff] <;>
        apply Submodule.mem_span_singleton.mpr
      · exact ⟨t, by rw [neg_one_smul, smul_neg, neg_smul]⟩
      · exact ⟨t⁻¹, by rw [neg_smul, smul_neg, ← mul_smul, inv_mul_cancel₀ ht0, one_smul,
          neg_one_smul]⟩
    · exact ⟨A, left_mem_affineSpan_pair ℝ A D, left_mem_affineSpan_pair ℝ _ _⟩

/-! ### Algebraic identities

The five elementary identities behind the problem: everything is expanded
in coordinates and closed by `ring`. -/

theorem cross_tangent_left (A B C D : Pt) :
    cross (D - C) (midpoint ℝ A B - C) =
      cross (D - C) (midpoint ℝ A B - midpoint ℝ C D) := by
  simp only [cross, midpoint_eq_smul_add, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul, invOf_eq_inv]
  ring

theorem cross_tangent_right (A B C D : Pt) :
    cross (B - A) (midpoint ℝ C D - A) =
      cross (midpoint ℝ A B - midpoint ℝ C D) (B - A) := by
  simp only [cross, midpoint_eq_smul_add, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul, invOf_eq_inv]
  ring

theorem cross_parallel (A B C D : Pt) :
    cross (C - B) (D - A) =
      cross (D - C) (midpoint ℝ A B - midpoint ℝ C D) -
        cross (midpoint ℝ A B - midpoint ℝ C D) (B - A) := by
  simp only [cross, midpoint_eq_smul_add, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul, invOf_eq_inv]
  ring

theorem cross_convex_left (A B C D : Pt) :
    cross (B - A) (C - B) + cross (A - D) (B - A) =
      2 * cross (midpoint ℝ A B - midpoint ℝ C D) (B - A) := by
  simp only [cross, midpoint_eq_smul_add, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul, invOf_eq_inv]
  ring

theorem cross_convex_right (A B C D : Pt) :
    cross (C - B) (D - C) + cross (D - C) (A - D) =
      2 * cross (D - C) (midpoint ℝ A B - midpoint ℝ C D) := by
  simp only [cross, midpoint_eq_smul_add, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul, invOf_eq_inv]
  ring

snip end

problem imo1984_p4 {A B C D : Pt} (hAB : A ≠ B) (hCD : C ≠ D) (hconv : ConvexQuad A B C D)
    (htan : dist (midpoint ℝ A B)
        (orthogonalProjection line[ℝ, C, D] (midpoint ℝ A B) : Pt) = dist A B / 2) :
    dist (midpoint ℝ C D)
        (orthogonalProjection line[ℝ, A, B] (midpoint ℝ C D) : Pt) = dist C D / 2 ↔
      line[ℝ, B, C] ∥ line[ℝ, A, D] := by
  have h0 : cross (B - A) (B - B) = 0 := by
    simp only [cross, PiLp.sub_apply]
    ring
  have h0' : cross (A - C) (A - A) = 0 := by
    simp only [cross, PiLp.sub_apply]
    ring
  have hCB : C ≠ B := by
    intro e
    rcases hconv with ⟨h1, -, -, -⟩ | ⟨h1, -, -, -⟩ <;>
      rw [e, h0] at h1 <;> simp at h1
  have hDA : D ≠ A := by
    intro e
    rcases hconv with ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ <;>
      rw [e, h0'] at h3 <;> simp at h3
  have hAB' : dist A B ≠ 0 := dist_ne_zero.mpr hAB
  have hCD' : dist C D ≠ 0 := dist_ne_zero.mpr hCD
  -- Square the tangency hypothesis.
  have hsq : 4 * cross (D - C) (midpoint ℝ A B - midpoint ℝ C D) ^ 2 =
      dist A B ^ 2 * dist C D ^ 2 := by
    have hb := dist_orthogonalProjection_sq hCD (M := midpoint ℝ A B)
    rw [cross_tangent_left A B C D] at hb
    have e : dist (midpoint ℝ A B)
          (orthogonalProjection line[ℝ, C, D] (midpoint ℝ A B) : Pt) ^ 2 = dist A B ^ 2 / 4 := by
      rw [htan]
      ring
    rw [e, eq_div_iff (pow_ne_zero 2 hCD')] at hb
    linarith [hb]
  -- Reformulate the left-hand side of the goal.
  have e0 : dist (midpoint ℝ C D)
        (orthogonalProjection line[ℝ, A, B] (midpoint ℝ C D) : Pt) = dist C D / 2 ↔
      4 * cross (midpoint ℝ A B - midpoint ℝ C D) (B - A) ^ 2 = dist A B ^ 2 * dist C D ^ 2 := by
    have hb := dist_orthogonalProjection_sq hAB (M := midpoint ℝ C D)
    rw [cross_tangent_right A B C D] at hb
    constructor
    · intro e
      have e2 : dist (midpoint ℝ C D)
            (orthogonalProjection line[ℝ, A, B] (midpoint ℝ C D) : Pt) ^ 2 = dist C D ^ 2 / 4 := by
        rw [e]
        ring
      rw [e2, eq_div_iff (pow_ne_zero 2 hAB')] at hb
      linarith [hb]
    · intro e
      have e2 : dist (midpoint ℝ C D)
            (orthogonalProjection line[ℝ, A, B] (midpoint ℝ C D) : Pt) ^ 2 = (dist C D / 2) ^ 2 := by
        rw [hb, div_eq_iff (pow_ne_zero 2 hAB')]
        linarith [e]
      have hnonneg : 0 ≤ dist C D / 2 := by positivity
      exact (sq_eq_sq₀ dist_nonneg hnonneg).mp e2
  rw [e0]
  -- The two squared quantities agree; convexity rules out the opposite-sign case.
  have hsame : cross (midpoint ℝ A B - midpoint ℝ C D) (B - A) +
        cross (D - C) (midpoint ℝ A B - midpoint ℝ C D) ≠ 0 := by
    have e4 := cross_convex_left A B C D
    have e5 := cross_convex_right A B C D
    rcases hconv with ⟨s1, s2, s3, s4⟩ | ⟨s1, s2, s3, s4⟩
    · have : 0 < cross (midpoint ℝ A B - midpoint ℝ C D) (B - A) +
          cross (D - C) (midpoint ℝ A B - midpoint ℝ C D) := by linarith
      exact ne_of_gt this
    · have : cross (midpoint ℝ A B - midpoint ℝ C D) (B - A) +
          cross (D - C) (midpoint ℝ A B - midpoint ℝ C D) < 0 := by linarith
      exact ne_of_lt this
  constructor
  · intro e
    have e'' : cross (midpoint ℝ A B - midpoint ℝ C D) (B - A) ^ 2 =
        cross (D - C) (midpoint ℝ A B - midpoint ℝ C D) ^ 2 := by linarith [e, hsq]
    have e' : (cross (midpoint ℝ A B - midpoint ℝ C D) (B - A) -
          cross (D - C) (midpoint ℝ A B - midpoint ℝ C D)) *
        (cross (midpoint ℝ A B - midpoint ℝ C D) (B - A) +
          cross (D - C) (midpoint ℝ A B - midpoint ℝ C D)) = 0 := by
      rw [show (cross (midpoint ℝ A B - midpoint ℝ C D) (B - A) -
            cross (D - C) (midpoint ℝ A B - midpoint ℝ C D)) *
          (cross (midpoint ℝ A B - midpoint ℝ C D) (B - A) +
            cross (D - C) (midpoint ℝ A B - midpoint ℝ C D)) =
          cross (midpoint ℝ A B - midpoint ℝ C D) (B - A) ^ 2 -
            cross (D - C) (midpoint ℝ A B - midpoint ℝ C D) ^ 2 from by ring,
        sub_eq_zero]
      exact e''
    rcases mul_eq_zero.mp e' with e1 | e2
    · apply (parallel_iff_cross hCB hDA).mpr
      rw [cross_parallel A B C D]
      linarith [e1]
    · exact absurd e2 hsame
  · intro hp
    have hc := (parallel_iff_cross hCB hDA).mp hp
    rw [cross_parallel A B C D] at hc
    have e : cross (midpoint ℝ A B - midpoint ℝ C D) (B - A) =
        cross (D - C) (midpoint ℝ A B - midpoint ℝ C D) := by linarith [hc]
    rw [e]
    linarith [hsq]

end Imo1984P4
