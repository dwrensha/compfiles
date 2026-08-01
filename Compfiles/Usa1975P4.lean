/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 1975, Problem 4

Two circles intersect at two points, one of them X. Find Y on one circle and
Z on the other, so that X, Y and Z are collinear and XY · XZ is as large as
possible.
-/

namespace Usa1975P4

open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {P : Type*} [MetricSpace P] [NormedAddTorsor V P]

/-- The second intersection of the line through `X` with unit direction `u`
and the circle with center `c` passing through `X`. -/
noncomputable def secondIntersection (c X : P) (u : V) : P :=
  (2 * ⟪c -ᵥ X, u⟫) • u +ᵥ X

/-- The set of all products `XY * XZ`, where `Y` (resp. `Z`) ranges over the
second intersection of a line through `X` with the first (resp. second)
circle. -/
def products (c₁ c₂ X : P) : Set ℝ :=
  {p | ∃ u : V, ‖u‖ = 1 ∧
    p = dist X (secondIntersection c₁ X u) * dist X (secondIntersection c₂ X u)}

snip begin

/-- Reflection across the line spanned by a unit vector preserves the norm. -/
lemma norm_two_mul_inner_smul_sub (a u : V) (hu : ‖u‖ = 1) :
    ‖(2 * ⟪a, u⟫) • u - a‖ = ‖a‖ := by
  have h : ‖(2 * ⟪a, u⟫) • u - a‖ ^ 2 = ‖a‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, hu, mul_one, Real.norm_eq_abs, sq_abs,
      real_inner_smul_left, real_inner_comm a u]
    ring
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- **Key estimate**: for a unit vector `u`,
`|⟪a, u⟫ * ⟪b, u⟫| ≤ (|⟪a, b⟫| + ‖a‖ * ‖b‖) / 2`. -/
lemma abs_inner_mul_inner_le (a b u : V) (hu : ‖u‖ = 1) :
    |⟪a, u⟫ * ⟪b, u⟫| ≤ (|⟪a, b⟫| + ‖a‖ * ‖b‖) / 2 := by
  have h1 : |⟪(2 * ⟪a, u⟫) • u - a, b⟫| ≤ ‖(2 * ⟪a, u⟫) • u - a‖ * ‖b‖ :=
    abs_real_inner_le_norm _ _
  rw [norm_two_mul_inner_smul_sub a u hu] at h1
  have h2 : ⟪(2 * ⟪a, u⟫) • u - a, b⟫ = 2 * (⟪a, u⟫ * ⟪b, u⟫) - ⟪a, b⟫ := by
    rw [inner_sub_left, real_inner_smul_left, real_inner_comm b u]
    ring
  rw [h2] at h1
  have h3 : |2 * (⟪a, u⟫ * ⟪b, u⟫)| - |⟪a, b⟫| ≤ ‖a‖ * ‖b‖ :=
    le_trans (abs_sub_abs_le_abs_sub _ _) h1
  rw [abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)] at h3
  linarith

/-- When `0 ≤ ⟪a, b⟫`, the key estimate is sharp: the bisector of the
directions of `a` and `b` attains equality. -/
lemma attain_of_inner_nonneg (a b : V) (ha : a ≠ 0) (hb : b ≠ 0) (hq : 0 ≤ ⟪a, b⟫) :
    ∃ u : V, ‖u‖ = 1 ∧ |⟪a, u⟫ * ⟪b, u⟫| = (|⟪a, b⟫| + ‖a‖ * ‖b‖) / 2 := by
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hnb : 0 < ‖b‖ := norm_pos_iff.mpr hb
  set K : ℝ := ⟪a, b⟫ + ‖a‖ * ‖b‖ with hK_def
  have hK : 0 < K := by
    have h := mul_pos hna hnb
    linarith
  have h2K : 0 < 2 * (‖a‖ * ‖b‖) * K := mul_pos (mul_pos two_pos (mul_pos hna hnb)) hK
  set w : V := ‖b‖ • a + ‖a‖ • b with hw_def
  have haw : ⟪a, w⟫ = ‖a‖ * K := by
    simp only [hw_def, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    rw [hK_def]
    ring
  have hbw : ⟪b, w⟫ = ‖b‖ * K := by
    simp only [hw_def, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
      real_inner_comm a b]
    rw [hK_def]
    ring
  have hw_sq : ‖w‖ ^ 2 = 2 * (‖a‖ * ‖b‖) * K := by
    have h : ⟪w, w⟫ = 2 * (‖a‖ * ‖b‖) * K := by
      simp only [hw_def, inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right, real_inner_self_eq_norm_sq, real_inner_comm a b, norm_smul,
        Real.norm_eq_abs]
      rw [abs_of_nonneg (norm_nonneg b), abs_of_nonneg (norm_nonneg a), hK_def]
      ring
    rwa [← real_inner_self_eq_norm_sq]
  have hw_ne : w ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hw_sq
    simp at hw_sq
    rcases hw_sq with (h | h) | h
    · exact ha h
    · exact hb h
    · exact hK.ne' h
  have hNw : ‖w‖ ≠ 0 := (norm_pos_iff.mpr hw_ne).ne'
  refine ⟨‖w‖⁻¹ • w, ?_, ?_⟩
  · rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ hNw]
  · have hnn : (0 : ℝ) ≤ ‖w‖⁻¹ * (‖a‖ * K) * (‖w‖⁻¹ * (‖b‖ * K)) :=
      mul_nonneg
        (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (mul_nonneg (norm_nonneg _) hK.le))
        (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (mul_nonneg (norm_nonneg _) hK.le))
    rw [real_inner_smul_right, real_inner_smul_right, haw, hbw, abs_of_nonneg hnn,
      abs_of_nonneg hq]
    have e1 : ‖w‖⁻¹ * (‖a‖ * K) * (‖w‖⁻¹ * (‖b‖ * K)) =
        (‖w‖ ^ 2)⁻¹ * ((‖a‖ * ‖b‖ * K) * K) := by
      rw [← inv_pow]
      ring
    rw [e1, hw_sq, ← hK_def]
    have hM : 2 * (‖a‖ * ‖b‖) * K ≠ 0 := h2K.ne'
    field_simp

/-- The key estimate is attained by some unit vector. -/
lemma exists_unit_abs_inner_mul_inner (a b : V) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ u : V, ‖u‖ = 1 ∧ |⟪a, u⟫ * ⟪b, u⟫| = (|⟪a, b⟫| + ‖a‖ * ‖b‖) / 2 := by
  rcases le_or_gt 0 ⟪a, b⟫ with hq | hq
  · exact attain_of_inner_nonneg a b ha hb hq
  · obtain ⟨u, hu, h⟩ := attain_of_inner_nonneg a (-b) ha (neg_ne_zero.mpr hb) (by
      rw [inner_neg_right]
      linarith)
    refine ⟨u, hu, ?_⟩
    rw [inner_neg_right, inner_neg_left, norm_neg, abs_neg, mul_neg, abs_neg] at h
    exact h

/-- The second intersection indeed lies on the circle centered at `c`
passing through `X`. -/
lemma dist_secondIntersection (c X : P) (u : V) (hu : ‖u‖ = 1) :
    dist (secondIntersection c X u) c = dist X c := by
  have h : ‖(2 * ⟪c -ᵥ X, u⟫) • u + (X -ᵥ c)‖ = ‖X -ᵥ c‖ := by
    have h2 : ‖(2 * ⟪c -ᵥ X, u⟫) • u + (X -ᵥ c)‖ ^ 2 = ‖X -ᵥ c‖ ^ 2 := by
      rw [norm_add_sq_real, norm_smul, hu, mul_one, Real.norm_eq_abs, sq_abs,
        real_inner_smul_left]
      have e1 : ⟪c -ᵥ X, u⟫ = -⟪u, X -ᵥ c⟫ := by
        rw [← neg_vsub_eq_vsub_rev, inner_neg_left, real_inner_comm u (X -ᵥ c)]
      rw [e1]
      ring
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2
  rw [secondIntersection, dist_eq_norm_vsub, vadd_vsub_assoc, h, ← dist_eq_norm_vsub]

/-- For a unit direction `u`, the product `XY * XZ` equals
`4 * |⟪c₁ -ᵥ X, u⟫ * ⟪c₂ -ᵥ X, u⟫|`. -/
lemma product_eq_four_mul_abs (c₁ c₂ X : P) (u : V) (hu : ‖u‖ = 1) :
    dist X (secondIntersection c₁ X u) * dist X (secondIntersection c₂ X u) =
      4 * |⟪c₁ -ᵥ X, u⟫ * ⟪c₂ -ᵥ X, u⟫| := by
  have e : ∀ c : P, dist X (secondIntersection c X u) = 2 * |⟪c -ᵥ X, u⟫| := by
    intro c
    rw [secondIntersection, dist_comm X _, dist_eq_norm_vsub, vadd_vsub, norm_smul, hu,
      mul_one, Real.norm_eq_abs, abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
  rw [e c₁, e c₂, abs_mul]
  ring

/-- Algebraic core of the problem: the greatest value of
`4 * |⟪a, u⟫ * ⟪b, u⟫|` over unit vectors `u`. -/
theorem isGreatest_four_mul_abs_inner (a b : V) (ha : a ≠ 0) (hb : b ≠ 0) :
    IsGreatest {p : ℝ | ∃ u : V, ‖u‖ = 1 ∧ p = 4 * |⟪a, u⟫ * ⟪b, u⟫|}
      (2 * (|⟪a, b⟫| + ‖a‖ * ‖b‖)) := by
  constructor
  · obtain ⟨u, hu, h⟩ := exists_unit_abs_inner_mul_inner a b ha hb
    exact ⟨u, hu, by rw [h]; ring⟩
  · rintro p ⟨u, hu, rfl⟩
    have h := abs_inner_mul_inner_le a b u hu
    linarith [abs_nonneg (⟪a, u⟫ * ⟪b, u⟫)]

snip end

determine maxProduct (r₁ r₂ d : ℝ) : ℝ := 2 * r₁ * r₂ + |r₁ ^ 2 + r₂ ^ 2 - d ^ 2|

problem usa1975_p4 (c₁ c₂ X : P) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hX₁ : dist X c₁ = r₁) (hX₂ : dist X c₂ = r₂) :
    IsGreatest (products c₁ c₂ X) (maxProduct r₁ r₂ (dist c₁ c₂)) := by
  have ha : ‖c₁ -ᵥ X‖ = r₁ := by
    rw [← dist_eq_norm_vsub, dist_comm]
    exact hX₁
  have hb : ‖c₂ -ᵥ X‖ = r₂ := by
    rw [← dist_eq_norm_vsub, dist_comm]
    exact hX₂
  have hab : 2 * ⟪c₁ -ᵥ X, c₂ -ᵥ X⟫ = r₁ ^ 2 + r₂ ^ 2 - dist c₁ c₂ ^ 2 := by
    have h := norm_sub_sq_real (c₁ -ᵥ X) (c₂ -ᵥ X)
    rw [vsub_sub_vsub_cancel_right, ← dist_eq_norm_vsub, ha, hb] at h
    linarith
  have hset : products c₁ c₂ X =
      {p : ℝ | ∃ u : V, ‖u‖ = 1 ∧ p = 4 * |⟪c₁ -ᵥ X, u⟫ * ⟪c₂ -ᵥ X, u⟫|} := by
    ext p
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, product_eq_four_mul_abs c₁ c₂ X u hu⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, (product_eq_four_mul_abs c₁ c₂ X u hu).symm⟩
  have hval : maxProduct r₁ r₂ (dist c₁ c₂) =
      2 * (|⟪c₁ -ᵥ X, c₂ -ᵥ X⟫| + ‖c₁ -ᵥ X‖ * ‖c₂ -ᵥ X‖) := by
    have h2 : |r₁ ^ 2 + r₂ ^ 2 - dist c₁ c₂ ^ 2| = 2 * |⟪c₁ -ᵥ X, c₂ -ᵥ X⟫| := by
      rw [← hab, abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    rw [maxProduct, ha, hb, h2]
    ring
  rw [hset, hval]
  exact isGreatest_four_mul_abs_inner _ _
    (norm_pos_iff.mp (by rw [ha]; exact hr₁)) (norm_pos_iff.mp (by rw [hb]; exact hr₂))

end Usa1975P4
