/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 1977, Problem 4

ABCD is a tetrahedron. The midpoint of AB is M and the midpoint of CD is N.
Show that MN is perpendicular to AB and CD iff AC = BD and AD = BC.
-/

namespace Usa1977P4

open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

snip begin

/-- Polarization identity: the inner product of a sum with a difference
is the difference of the squared norms. -/
lemma inner_add_sub_self (u w : V) : ⟪u + w, u - w⟫ = ‖u‖ ^ 2 - ‖w‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq u, ← real_inner_self_eq_norm_sq w,
    inner_sub_right, inner_add_left, inner_add_left, real_inner_comm w u]
  ring

/-- The vector from the midpoint of `AB` to the midpoint of `CD` is
one half of `(C + D) - (A + B)`. -/
lemma midpoint_sub_midpoint (A B C D : V) :
    midpoint ℝ C D - midpoint ℝ A B = (⅟2 : ℝ) • ((C + D) - (A + B)) := by
  rw [midpoint_eq_smul_add, midpoint_eq_smul_add, ← smul_sub]

/-- With `v = (A + B) - (C + D)` (twice the vector `NM`), the sum of
`⟪v, A - B⟫` and `⟪v, C - D⟫` equals `‖A - D‖² - ‖B - C‖²`. -/
lemma inner_sum_eq_norm_sq_sub (A B C D : V) :
    ⟪(A + B) - (C + D), A - B⟫ + ⟪(A + B) - (C + D), C - D⟫ =
      ‖A - D‖ ^ 2 - ‖B - C‖ ^ 2 := by
  rw [← inner_add_right,
    show (A - B) + (C - D) = (A - D) - (B - C) from by abel,
    show (A + B) - (C + D) = (A - D) + (B - C) from by abel,
    inner_add_sub_self]

/-- With `v = (A + B) - (C + D)` (twice the vector `NM`), the difference of
`⟪v, A - B⟫` and `⟪v, C - D⟫` equals `‖A - C‖² - ‖B - D‖²`. -/
lemma inner_sub_eq_norm_sq_sub (A B C D : V) :
    ⟪(A + B) - (C + D), A - B⟫ - ⟪(A + B) - (C + D), C - D⟫ =
      ‖A - C‖ ^ 2 - ‖B - D‖ ^ 2 := by
  rw [← inner_sub_right,
    show (A - B) - (C - D) = (A - C) - (B - D) from by abel,
    show (A + B) - (C + D) = (A - C) + (B - D) from by abel,
    inner_add_sub_self]

/-- `MN` is perpendicular to `AB` iff the doubled midpoint vector
`(A + B) - (C + D)` is perpendicular to `A - B`. -/
lemma inner_midpoint_ab_iff (A B C D : V) :
    ⟪midpoint ℝ C D - midpoint ℝ A B, B - A⟫ = 0 ↔
      ⟪(A + B) - (C + D), A - B⟫ = 0 := by
  rw [midpoint_sub_midpoint, real_inner_smul_left,
    show (C + D) - (A + B) = -((A + B) - (C + D)) from (neg_sub _ _).symm,
    show B - A = -(A - B) from (neg_sub _ _).symm,
    inner_neg_left, inner_neg_right, neg_neg,
    mul_eq_zero_iff_left (by norm_num [invOf_eq_inv] : (⅟2 : ℝ) ≠ 0)]

/-- `MN` is perpendicular to `CD` iff the doubled midpoint vector
`(A + B) - (C + D)` is perpendicular to `C - D`. -/
lemma inner_midpoint_cd_iff (A B C D : V) :
    ⟪midpoint ℝ C D - midpoint ℝ A B, D - C⟫ = 0 ↔
      ⟪(A + B) - (C + D), C - D⟫ = 0 := by
  rw [midpoint_sub_midpoint, real_inner_smul_left,
    show (C + D) - (A + B) = -((A + B) - (C + D)) from (neg_sub _ _).symm,
    show D - C = -(C - D) from (neg_sub _ _).symm,
    inner_neg_left, inner_neg_right, neg_neg,
    mul_eq_zero_iff_left (by norm_num [invOf_eq_inv] : (⅟2 : ℝ) ≠ 0)]

/-- Equality of distances, stated with squared norms of the difference
vectors. -/
lemma dist_eq_iff_norm_sq_eq {V' : Type*} [NormedAddCommGroup V'] (X Y Z W : V') :
    dist X Y = dist Z W ↔ ‖X - Y‖ ^ 2 = ‖Z - W‖ ^ 2 := by
  rw [dist_eq_norm, dist_eq_norm, sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]

snip end

problem usa1977_p4 (A B C D : V) :
    (⟪midpoint ℝ C D - midpoint ℝ A B, B - A⟫ = 0 ∧
      ⟪midpoint ℝ C D - midpoint ℝ A B, D - C⟫ = 0) ↔
    dist A C = dist B D ∧ dist A D = dist B C := by
  rw [inner_midpoint_ab_iff, inner_midpoint_cd_iff,
    dist_eq_iff_norm_sq_eq, dist_eq_iff_norm_sq_eq]
  constructor
  · rintro ⟨h1, h2⟩
    have e1 := inner_sum_eq_norm_sq_sub A B C D
    have e2 := inner_sub_eq_norm_sq_sub A B C D
    rw [h1, h2, add_zero] at e1
    rw [h1, h2, sub_zero] at e2
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    have e1 := inner_sum_eq_norm_sq_sub A B C D
    have e2 := inner_sub_eq_norm_sq_sub A B C D
    rw [h2, sub_self] at e1
    rw [h1, sub_self] at e2
    constructor <;> linarith

end Usa1977P4
