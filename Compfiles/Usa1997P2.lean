/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 1997, Problem 2

ABC is a triangle. Take points D, E, F on the perpendicular bisectors of
BC, CA, AB respectively. Show that the lines through A, B, C perpendicular
to EF, FD, DE respectively are concurrent.

## Note on the formal statement

As literally stated, the problem needs a non-degeneracy assumption: if
D, E, F are collinear the three lines can be parallel and distinct, and
then they are not concurrent. A concrete counterexample is
A = D = (0, 0), B = (1, 0), C = (0, 1), E = (1, 1/2), F = (1/2, 1/4):
all three bisector conditions hold, but the three lines are the parallel
lines `2x + y = 0`, `2x + y = 2` and `2x + y = 1`. We therefore add the
hypothesis that D, E, F are not collinear (which also guarantees that
EF, FD and DE are genuine lines and that the first two perpendiculars
actually meet).

The formalization follows J. Scholes' kalva solution.
-/

namespace Usa1997P2

open scoped InnerProductSpace

snip begin

/-- If `X` is equidistant from `P` and from `Q`, then the difference of the
squared norms of `Q` and `P` equals `2 * (⟪X, Q⟫ - ⟪X, P⟫)`. -/
lemma two_mul_inner_sub_of_dist_eq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {X P Q : V} (h : dist X P = dist X Q) :
    2 * (⟪X, Q⟫_ℝ - ⟪X, P⟫_ℝ) = ⟪Q, Q⟫_ℝ - ⟪P, P⟫_ℝ := by
  have h2 : ⟪X - P, X - P⟫_ℝ = ⟪X - Q, X - Q⟫_ℝ := by
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, ← dist_eq_norm, ← dist_eq_norm, h]
  simp only [inner_sub_left, inner_sub_right] at h2
  rw [real_inner_comm X P, real_inner_comm X Q] at h2
  linear_combination h2

/-- If three points are not collinear, then the two difference vectors
`E - F` and `F - D` are linearly independent. -/
lemma not_collinear_indep {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {D E F : V} (h : ¬ Collinear ℝ ({D, E, F} : Set V)) :
    LinearIndependent ℝ ![E - F, F - D] := by
  rw [linearIndependent_fin2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · intro hFD
    apply h
    rw [sub_eq_zero] at hFD
    rw [hFD]
    rw [Set.insert_eq_of_mem (Set.mem_insert_of_mem E (Set.mem_singleton D))]
    exact collinear_pair ℝ E D
  · intro a ha
    apply h
    rw [collinear_iff_exists_forall_eq_smul_vadd]
    refine ⟨F, F - D, fun p hp ↦ ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨-1, by rw [vadd_eq_add]; module⟩
    · exact ⟨a, by rw [eq_vadd_iff_vsub_eq, vsub_eq_sub]; exact ha.symm⟩
    · exact ⟨0, by simp⟩

/-- The Gram determinant of two linearly independent vectors is strictly
positive (the strict Cauchy–Schwarz inequality). -/
lemma gram_det_pos {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {v₁ v₂ : V} (h : LinearIndependent ℝ ![v₁, v₂]) :
    0 < ⟪v₁, v₁⟫_ℝ * ⟪v₂, v₂⟫_ℝ - ⟪v₁, v₂⟫_ℝ * ⟪v₁, v₂⟫_ℝ := by
  rw [linearIndependent_fin2] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
  obtain ⟨hv2, hv1⟩ := h
  have h1 : v₁ ≠ 0 := by
    intro hz
    exact hv1 0 (by rw [zero_smul]; exact hz.symm)
  have ha1 : 0 < ⟪v₁, v₁⟫_ℝ := by
    rw [real_inner_self_eq_norm_sq]
    exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr h1)
  set c := ⟪v₂, v₁⟫_ℝ / ⟪v₁, v₁⟫_ℝ with hc
  have hw : v₂ - c • v₁ ≠ 0 := by
    intro hw0
    have hc0 : c ≠ 0 := by
      intro hcc
      rw [hcc, zero_smul, sub_zero] at hw0
      exact hv2 hw0
    have e1 : v₂ = c • v₁ := by
      rw [← sub_eq_zero]
      exact hw0
    have e2 : v₁ = c⁻¹ • v₂ := by
      rw [e1, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    exact hv1 c⁻¹ e2.symm
  have hww : 0 < ⟪v₂ - c • v₁, v₂ - c • v₁⟫_ℝ := by
    rw [real_inner_self_eq_norm_sq]
    exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hw)
  have key : ⟪v₁, v₁⟫_ℝ * ⟪v₂ - c • v₁, v₂ - c • v₁⟫_ℝ
      = ⟪v₁, v₁⟫_ℝ * ⟪v₂, v₂⟫_ℝ - ⟪v₁, v₂⟫_ℝ * ⟪v₁, v₂⟫_ℝ := by
    rw [hc]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_comm v₁ v₂]
    field_simp [ne_of_gt ha1]
    ring
  have hpos := mul_pos ha1 hww
  rw [key] at hpos
  exact hpos

snip end

problem usa1997_p2
    (A B C D E F : EuclideanSpace ℝ (Fin 2))
    (_hABC : ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))))
    (hD : dist D B = dist D C) (hE : dist E C = dist E A) (hF : dist F A = dist F B)
    (hDEF : ¬ Collinear ℝ ({D, E, F} : Set (EuclideanSpace ℝ (Fin 2)))) :
    ∃ P : EuclideanSpace ℝ (Fin 2),
      ⟪P - A, E - F⟫_ℝ = 0 ∧ ⟪P - B, F - D⟫_ℝ = 0 ∧ ⟪P - C, D - E⟫_ℝ = 0 := by
  -- The scalar identity behind the "equal differences of squares" argument.
  have hsum : ⟪A, E - F⟫_ℝ + ⟪B, F - D⟫_ℝ + ⟪C, D - E⟫_ℝ = 0 := by
    have h1 := two_mul_inner_sub_of_dist_eq hD
    have h2 := two_mul_inner_sub_of_dist_eq hE
    have h3 := two_mul_inner_sub_of_dist_eq hF
    simp only [inner_sub_right]
    rw [← real_inner_comm D C, ← real_inner_comm D B] at h1
    rw [← real_inner_comm E A, ← real_inner_comm E C] at h2
    rw [← real_inner_comm F B, ← real_inner_comm F A] at h3
    linear_combination (h1 + h2 + h3) / 2
  -- The two direction vectors are independent, so their Gram determinant is nonzero.
  have hgram := gram_det_pos (not_collinear_indep hDEF)
  set v₁ := E - F with hv₁
  set v₂ := F - D with hv₂
  set a₁ := ⟪v₁, v₁⟫_ℝ with ha₁
  set a₂ := ⟪v₂, v₂⟫_ℝ with ha₂
  set b := ⟪v₁, v₂⟫_ℝ with hb
  set c₁ := ⟪A, v₁⟫_ℝ with hc₁
  set c₂ := ⟪B, v₂⟫_ℝ with hc₂
  have hΔ : a₁ * a₂ - b * b ≠ 0 := ne_of_gt hgram
  -- The explicit Cramer-rule intersection point of the first two lines.
  set P := ((c₁ * a₂ - c₂ * b) / (a₁ * a₂ - b * b)) • v₁
      + ((c₂ * a₁ - c₁ * b) / (a₁ * a₂ - b * b)) • v₂ with hP
  have key1 : ⟪P, v₁⟫_ℝ = c₁ := by
    rw [hP]
    simp only [inner_add_left, real_inner_smul_left]
    rw [← ha₁, real_inner_comm v₁ v₂, ← hb]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
    rw [show (c₁ * a₂ - c₂ * b) * a₁ + (c₂ * a₁ - c₁ * b) * b
          = c₁ * (a₁ * a₂ - b * b) by ring]
    exact mul_div_cancel_right₀ _ hΔ
  have key2 : ⟪P, v₂⟫_ℝ = c₂ := by
    rw [hP]
    simp only [inner_add_left, real_inner_smul_left]
    rw [← hb, ← ha₂]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
    rw [show (c₁ * a₂ - c₂ * b) * b + (c₂ * a₁ - c₁ * b) * a₂
          = c₂ * (a₁ * a₂ - b * b) by ring]
    exact mul_div_cancel_right₀ _ hΔ
  refine ⟨P, ?_, ?_, ?_⟩
  · rw [inner_sub_left, key1, ← hc₁, sub_self]
  · rw [inner_sub_left, key2, ← hc₂, sub_self]
  · have hv₃ : D - E = -(v₁ + v₂) := by
      rw [hv₁, hv₂]
      abel
    rw [hv₃] at hsum
    simp only [inner_neg_right, inner_add_right] at hsum
    rw [hv₃]
    simp only [inner_sub_left, inner_neg_right, inner_add_right]
    rw [key1, key2]
    linear_combination -hsum

end Usa1997P2
