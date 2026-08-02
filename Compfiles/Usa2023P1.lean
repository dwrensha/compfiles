/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 2023, Problem 1

In an acute triangle ABC, let M be the midpoint of BC. Let P be the foot of
the perpendicular from C to AM. Suppose that the circumcircle of triangle ABP
intersects line BC at two distinct points B and Q. Let N be the midpoint of AQ.
Prove that NB = NC.
-/

namespace Usa2023P1

open RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

snip begin

/--
Power of a point, in inner-product form. Suppose that `X` and `Y` are two
points of a circle with center `O` and radius `r`, and suppose that `M`, `X`,
`Y` are collinear with `Y - M = u • (X - M)` and `u ≠ 1` (so `X ≠ Y`). Then
`⟪X - M, Y - M⟫` equals the power `‖O - M‖ ^ 2 - r ^ 2` of the point `M`
with respect to the circle.
-/
lemma power_of_point {X Y M O : V} {r u : ℝ}
    (hX : dist X O = r) (hY : dist Y O = r)
    (h : Y - M = u • (X - M)) (hu : u ≠ 1) :
    ⟪X - M, Y - M⟫ = ‖O - M‖ ^ 2 - r ^ 2 := by
  have hX' : ‖X - M - (O - M)‖ ^ 2 = r ^ 2 := by
    rw [sub_sub_sub_cancel_right, ← dist_eq_norm, hX]
  have hY' : ‖Y - M - (O - M)‖ ^ 2 = r ^ 2 := by
    rw [sub_sub_sub_cancel_right, ← dist_eq_norm, hY]
  rw [h, norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    real_inner_smul_left] at hY'
  rw [norm_sub_sq_real] at hX'
  rw [h, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have key : 2 * ⟪X - M, O - M⟫ = (u + 1) * ‖X - M‖ ^ 2 := by
    have h2 : (u - 1) * ((u + 1) * ‖X - M‖ ^ 2 - 2 * ⟪X - M, O - M⟫) = 0 := by
      linear_combination hY' - hX'
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 (sub_ne_zero.mpr hu)
    · linarith
  linear_combination -key - hX'

snip end

problem usa2023_p1
    (A B C : V)
    (hacute : 0 < ⟪B - A, C - A⟫ ∧ 0 < ⟪A - B, C - B⟫ ∧ 0 < ⟪A - C, B - C⟫)
    (M P Q N : V)
    (hM : M = midpoint ℝ B C)
    (hPline : ∃ t : ℝ, P = A + t • (M - A))
    (hPperp : ⟪C - P, M - A⟫ = 0)
    (hQline : ∃ s : ℝ, Q = B + s • (C - B))
    (hQB : Q ≠ B)
    (hcirc : ∃ O : V, ∃ r : ℝ,
      dist A O = r ∧ dist B O = r ∧ dist P O = r ∧ dist Q O = r)
    (hN : N = midpoint ℝ A Q) :
    dist N B = dist N C := by
  obtain ⟨hacuteA, -, hacuteC⟩ := hacute
  obtain ⟨t, ht⟩ := hPline
  obtain ⟨s, hs⟩ := hQline
  obtain ⟨O, r, hA, hB, hP, hQ⟩ := hcirc
  -- Vector form of the midpoint relations.
  have hBC : C - M = -(B - M) := by
    rw [hM, midpoint_eq_smul_add]
    simp only [invOf_eq_inv]
    module
  have hPA : P - M = (1 - t) • (A - M) := by
    rw [ht, hM, midpoint_eq_smul_add]
    simp only [invOf_eq_inv]
    module
  have hQB' : Q - M = (1 - 2 * s) • (B - M) := by
    rw [hs, hM, midpoint_eq_smul_add]
    simp only [invOf_eq_inv]
    module
  -- The foot `P` differs from `A`: otherwise `CP ⊥ AM` would force the angle
  -- at `A` to be a right angle, contradicting acuteness.
  have hCA : C - A ≠ 0 := by
    intro h
    have h2 : A - C = 0 := by rw [← neg_eq_zero, neg_sub]; exact h
    rw [h2, inner_zero_left] at hacuteC
    exact (lt_irrefl 0 hacuteC).elim
  have hpos : 0 < ⟪C - A, M - A⟫ := by
    have hMA : M - A = (2 : ℝ)⁻¹ • ((B - A) + (C - A)) := by
      rw [hM, midpoint_eq_smul_add]
      simp only [invOf_eq_inv]
      module
    rw [hMA, real_inner_smul_right, inner_add_right, real_inner_self_eq_norm_sq,
      real_inner_comm (B - A) (C - A)]
    have hnorm : 0 < ‖C - A‖ ^ 2 := by
      have h1 : 0 < ‖C - A‖ := norm_pos_iff.mpr hCA
      nlinarith [sq_nonneg ‖C - A‖]
    positivity
  have ht0 : t ≠ 0 := by
    intro ht0
    rw [ht0, zero_smul, add_zero] at ht
    rw [ht] at hPperp
    exact (ne_of_gt hpos) hPperp
  have hu1 : (1 : ℝ) - t ≠ 1 := by
    intro h
    apply ht0
    linarith
  -- Power of `M` with respect to the circumcircle, computed along each chord.
  have hpow1 : ⟪A - M, P - M⟫ = ‖O - M‖ ^ 2 - r ^ 2 :=
    power_of_point hA hP hPA hu1
  have hs0 : s ≠ 0 := by
    intro hs0
    rw [hs0, zero_smul, add_zero] at hs
    exact hQB hs
  have hu2 : (1 : ℝ) - 2 * s ≠ 1 := by
    intro h
    apply hs0
    linarith
  have hpow2 : ⟪B - M, Q - M⟫ = ‖O - M‖ ^ 2 - r ^ 2 :=
    power_of_point hB hQ hQB' hu2
  have hpow : ⟪A - M, P - M⟫ = ⟪B - M, Q - M⟫ := by rw [hpow1, hpow2]
  -- The key computation: `N - M` is orthogonal to `B - M`, so `N` lies on the
  -- perpendicular bisector of `BC`.
  have hkey : ⟪N - M, B - M⟫ = 0 := by
    have hNM : N - M = (2 : ℝ)⁻¹ • ((A - M) + (Q - M)) := by
      rw [hN, hM, midpoint_eq_smul_add, midpoint_eq_smul_add]
      simp only [invOf_eq_inv]
      module
    rw [hNM, real_inner_smul_left, inner_add_left, hQB', real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    rw [hPA, real_inner_smul_right, real_inner_self_eq_norm_sq,
      hQB', real_inner_smul_right, real_inner_self_eq_norm_sq] at hpow
    have h1 : C - P = -(B - M) - (1 - t) • (A - M) := by
      rw [show C - P = (C - M) - (P - M) by abel, hBC, hPA]
    rw [h1, show M - A = -(A - M) by abel] at hPperp
    rw [inner_sub_left (-(B - M)) ((1 - t) • (A - M)) (-(A - M)),
      inner_neg_left (B - M) (-(A - M)), inner_neg_right (B - M) (A - M),
      real_inner_smul_left (A - M) (-(A - M)) (1 - t),
      inner_neg_right (A - M) (A - M), real_inner_self_eq_norm_sq (A - M),
      real_inner_comm (A - M) (B - M)] at hPperp
    linarith [hpow, hPperp]
  -- Conclude `dist N B = dist N C`.
  have hNB : dist N B ^ 2 = ‖N - M‖ ^ 2 - 2 * ⟪N - M, B - M⟫ + ‖B - M‖ ^ 2 := by
    rw [dist_eq_norm, show N - B = (N - M) - (B - M) by abel, norm_sub_sq_real]
  have hNC : dist N C ^ 2 = ‖N - M‖ ^ 2 + 2 * ⟪N - M, B - M⟫ + ‖B - M‖ ^ 2 := by
    rw [dist_eq_norm, show N - C = (N - M) + (B - M) by
      rw [show N - C = (N - M) - (C - M) by abel, hBC, sub_neg_eq_add], norm_add_sq_real]
  have hsq : dist N B ^ 2 = dist N C ^ 2 := by
    rw [hkey] at hNB hNC
    linear_combination hNB - hNC
  rw [sq_eq_sq_iff_abs_eq_abs, abs_of_nonneg dist_nonneg, abs_of_nonneg dist_nonneg] at hsq
  exact hsq

end Usa2023P1
