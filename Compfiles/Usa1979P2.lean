/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 1979, Problem 2

N is the north pole. A and B are points on a great circle through N
equidistant from N. C is a point on the equator. Show that the great circle
through C and N bisects the angle ACB in the spherical triangle ABC
(a spherical triangle has great circle arcs as sides).
-/

namespace Usa1979P2

open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

snip begin

/-- Reflection across the line spanned by a unit vector `N` preserves the
inner product with `N`. Algebraically this is the fact that rotating the
sphere by 180° about the diameter through `N` fixes angles at `N`. -/
lemma inner_reflect (x N : V) (hN : ‖N‖ = 1) :
    ⟪N, -x + (2 * ⟪x, N⟫) • N⟫ = ⟪x, N⟫ := by
  have hNN : ⟪N, N⟫ = 1 := by rw [real_inner_self_eq_norm_mul_norm, hN, mul_one]
  simp only [inner_add_right, inner_neg_right, real_inner_smul_right, hNN, mul_one,
    real_inner_comm x N]
  ring

/-- Reflection across the line spanned by a unit vector `N` preserves norms. -/
lemma norm_reflect (x N : V) (hN : ‖N‖ = 1) :
    ‖-x + (2 * ⟪x, N⟫) • N‖ = ‖x‖ := by
  have hNN : ⟪N, N⟫ = 1 := by rw [real_inner_self_eq_norm_mul_norm, hN, mul_one]
  have hsq : ‖-x + (2 * ⟪x, N⟫) • N‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq (-x + (2 * ⟪x, N⟫) • N),
      ← real_inner_self_eq_norm_sq x]
    simp only [inner_add_left, inner_add_right, inner_neg_left, inner_neg_right,
      real_inner_smul_left, real_inner_smul_right, hNN, real_inner_comm x N]
    ring
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

snip end

problem usa1979_p2
    (N A B C : V)
    -- The four points lie on the unit sphere centered at the origin.
    (hN : ‖N‖ = 1) (hA : ‖A‖ = 1) (hB : ‖B‖ = 1) (_hC : ‖C‖ = 1)
    -- `A` and `B` are equidistant from `N`: for unit vectors the spherical
    -- distance `Real.arccos ⟪X, N⟫` from `N` is equal iff the inner products
    -- with `N` are equal.
    (hdist : ⟪A, N⟫ = ⟪B, N⟫)
    -- `A` and `B` lie on a great circle through `N`, i.e. on the intersection
    -- of the sphere with a 2-dimensional subspace containing `N` and `A`.
    (hcircle : B ∈ Submodule.span ℝ {A, N})
    -- `C` lies on the equator, the great circle orthogonal to the pole `N`.
    (hequator : ⟪C, N⟫ = 0) :
    -- The angle at `C` between two great-circle arcs `CX` and `CY` is the
    -- angle between the tangent vectors `X - ⟪X, C⟫ • C` and `Y - ⟪Y, C⟫ • C`
    -- of the arcs at `C`; the equation says that the great circle through
    -- `C` and `N` bisects the angle `ACB`.
    InnerProductGeometry.angle (A - ⟪A, C⟫ • C) (N - ⟪N, C⟫ • C) =
      InnerProductGeometry.angle (N - ⟪N, C⟫ • C) (B - ⟪B, C⟫ • C) := by
  -- Basic inner-product consequences of the unit hypotheses.
  have hNN : ⟪N, N⟫ = 1 := by rw [real_inner_self_eq_norm_mul_norm, hN, mul_one]
  have hAA : ⟪A, A⟫ = 1 := by rw [real_inner_self_eq_norm_mul_norm, hA, mul_one]
  have hBB : ⟪B, B⟫ = 1 := by rw [real_inner_self_eq_norm_mul_norm, hB, mul_one]
  have hNC : ⟪N, C⟫ = 0 := by rw [real_inner_comm]; exact hequator
  -- Since `⟪N, C⟫ = 0`, the tangent vector at `C` of the arc `CN` is `N` itself.
  simp only [hNC, zero_smul, sub_zero]
  -- Unpack the great-circle hypothesis.
  rw [Submodule.mem_span_pair] at hcircle
  obtain ⟨α, β, hαβ⟩ := hcircle
  -- The scalar constraint coming from `‖B‖ = 1`.
  have e1 : α ^ 2 + β ^ 2 + 2 * α * β * ⟪A, N⟫ = 1 := by
    have h := hBB
    rw [← hαβ] at h
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      hAA, hNN, real_inner_comm A N] at h
    linear_combination h
  -- The scalar constraint coming from `⟪B, N⟫ = ⟪A, N⟫`.
  have e2 : α * ⟪A, N⟫ + β = ⟪A, N⟫ := by
    have h := hdist
    rw [← hαβ] at h
    simp only [inner_add_left, real_inner_smul_left, hNN] at h
    linear_combination -h
  -- Combining both constraints gives `(1 - ⟪A, N⟫ ^ 2) * (α ^ 2 - 1) = 0`.
  have hd2 : (α * ⟪A, N⟫ + β - ⟪A, N⟫) ^ 2 = 0 := by
    rw [sq_eq_zero_iff, sub_eq_zero]; exact e2
  have hfactor : (1 - ⟪A, N⟫ ^ 2) * (α ^ 2 - 1) = 0 := by
    linear_combination e1 - 2 * ⟪A, N⟫ * e2 - hd2
  rcases mul_eq_zero.mp hfactor with hk1 | hα1
  · -- Case `⟪A, N⟫ ^ 2 = 1`: then `A = ±N`, and equidistance forces `B = A`.
    have hAk : A = ⟪A, N⟫ • N := by
      have h1 : ⟪A - ⟪A, N⟫ • N, A - ⟪A, N⟫ • N⟫ = 1 - ⟪A, N⟫ ^ 2 := by
        simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
          real_inner_smul_right, hAA, hNN, real_inner_comm A N]
        ring
      have h0 : ⟪A - ⟪A, N⟫ • N, A - ⟪A, N⟫ • N⟫ = 0 := by rw [h1]; exact hk1
      rw [real_inner_self_eq_norm_sq, sq_eq_zero_iff, norm_eq_zero, sub_eq_zero] at h0
      exact h0
    have hB' : B = A := by
      rw [← hαβ, hAk, smul_smul, ← add_smul, e2]
    rw [hB']
    exact InnerProductGeometry.angle_comm _ _
  · have hα2 : α ^ 2 = 1 := sub_eq_zero.mp hα1
    rw [sq_eq_one_iff] at hα2
    rcases hα2 with rfl | hαneg
    · -- Case `α = 1`: then `β = 0` and `B = A`.
      have hβ0 : β = 0 := by linarith [e2]
      have hB' : B = A := by rw [← hαβ, hβ0, zero_smul, add_zero, one_smul]
      rw [hB']
      exact InnerProductGeometry.angle_comm _ _
    · -- Case `α = -1`: then `β = 2 * ⟪A, N⟫`, so `B` is the reflection of `A`
      -- across the line through `N`, and the claim follows from that
      -- reflection being an isometry fixing `N`.
      have hβ : β = 2 * ⟪A, N⟫ := by rw [hαneg] at e2; linarith [e2]
      have hB' : B = -A + (2 * ⟪A, N⟫) • N := by
        rw [← hαβ, hαneg, hβ, neg_smul, one_smul]
      have hbC : ⟪B, C⟫ = -⟪A, C⟫ := by
        rw [hB', inner_add_left, inner_neg_left, real_inner_smul_left, hNC, mul_zero, add_zero]
      have hi1 : ⟪A - ⟪A, C⟫ • C, N⟫ = ⟪A, N⟫ := by
        rw [inner_sub_left, real_inner_smul_left, hequator, mul_zero, sub_zero]
      have hvec : B - ⟪B, C⟫ • C = -(A - ⟪A, C⟫ • C) + (2 * ⟪A, N⟫) • N := by
        rw [hbC, hB']
        module
      have hnorm : ‖B - ⟪B, C⟫ • C‖ = ‖A - ⟪A, C⟫ • C‖ := by
        rw [hvec, ← hi1]
        exact norm_reflect _ _ hN
      have hin2 : ⟪N, B - ⟪B, C⟫ • C⟫ = ⟪A - ⟪A, C⟫ • C, N⟫ := by
        rw [hvec, ← hi1]
        exact inner_reflect _ _ hN
      rw [InnerProductGeometry.angle, InnerProductGeometry.angle, hin2, hnorm, hN, mul_one,
        one_mul]

end Usa1979P2
