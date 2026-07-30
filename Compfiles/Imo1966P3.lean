/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry, .Inequality] }

/-!
# International Mathematical Olympiad 1966, Problem 3

Prove that the sum of the distances of the vertices of a regular
tetrahedron from the center of its circumscribed sphere is less than
the sum of the distances of these vertices from any other point in space.
-/

namespace Imo1966P3

open scoped RealInnerProductSpace

abbrev Pt := EuclideanSpace ℝ (Fin 3)

/-- The center of a tetrahedron with vertices `v`: its centroid.
For a *regular* tetrahedron the centroid coincides with the center of the
circumscribed sphere; indeed, `norm_sub_center_sq` below shows that the
centroid is equidistant from all four vertices. -/
noncomputable def center (v : Fin 4 → Pt) : Pt := (4 : ℝ)⁻¹ • ∑ i, v i

snip begin

/-- The unit vector pointing from the center of the tetrahedron towards
its `i`-th vertex. -/
noncomputable def unitVec (v : Fin 4 → Pt) (i : Fin 4) : Pt :=
  (‖v i - center v‖)⁻¹ • (v i - center v)

/-- The vertices, viewed from the centroid, sum to zero. -/
lemma sum_sub_center (v : Fin 4 → Pt) : ∑ i, (v i - center v) = 0 := by
  have h4 : (4 : ℝ) ≠ 0 := by norm_num
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  unfold center
  rw [← Nat.cast_smul_eq_nsmul ℝ, Nat.cast_ofNat, smul_smul, mul_inv_cancel₀ h4,
    one_smul, sub_self]

/-- Polarization: the inner product of two vertices viewed from the center,
expressed through the side length `s`. -/
lemma inner_sub_center_sub_center {v : Fin 4 → Pt} {s : ℝ}
    (hv : ∀ i j : Fin 4, i ≠ j → dist (v i) (v j) = s) {i j : Fin 4} (hij : i ≠ j) :
    ⟪v i - center v, v j - center v⟫ =
      (‖v i - center v‖ ^ 2 + ‖v j - center v‖ ^ 2 - s ^ 2) / 2 := by
  have h1 : ‖v i - v j‖ = s := by rw [← dist_eq_norm]; exact hv i j hij
  have h2 : v i - v j = (v i - center v) - (v j - center v) := by abel
  have h3 : ‖(v i - center v) - (v j - center v)‖ ^ 2 = s ^ 2 := by rw [← h2, h1]
  have h4 := norm_sub_sq_real (v i - center v) (v j - center v)
  linarith [h3, h4]

/-- The squared distance from a vertex to the center: `3s²/8`.
In particular the center is equidistant from all vertices, so it is indeed
the center of the circumscribed sphere. -/
lemma norm_sub_center_sq {v : Fin 4 → Pt} {s : ℝ}
    (hv : ∀ i j : Fin 4, i ≠ j → dist (v i) (v j) = s) (i : Fin 4) :
    ‖v i - center v‖ ^ 2 = 3 * s ^ 2 / 8 := by
  -- Taking the inner product of `v k - center v` with `∑ j, (v j - center v) = 0`
  -- yields `4‖u k‖² = 3s² - S`, where `S = ∑ j, ‖u j‖²`.
  have hE : ∀ k : Fin 4,
      4 * ‖v k - center v‖ ^ 2 = 3 * s ^ 2 - ∑ j, ‖v j - center v‖ ^ 2 := by
    intro k
    have h0 : ⟪v k - center v, ∑ j, (v j - center v)⟫ = 0 := by
      rw [sum_sub_center v, inner_zero_right]
    rw [inner_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ k),
      real_inner_self_eq_norm_sq] at h0
    have hrw : ∑ j ∈ Finset.univ.erase k, ⟪v k - center v, v j - center v⟫
        = ∑ j ∈ Finset.univ.erase k,
          (‖v k - center v‖ ^ 2 + ‖v j - center v‖ ^ 2 - s ^ 2) / 2 := by
      apply Finset.sum_congr rfl
      intro j hj
      exact inner_sub_center_sub_center hv ((Finset.mem_erase.mp hj).1.symm)
    rw [hrw] at h0
    have hcard : (Finset.univ.erase k).card = 3 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
    simp only [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_const, hcard, nsmul_eq_mul, Nat.cast_ofNat] at h0
    have hserase : ∑ j ∈ Finset.univ.erase k, ‖v j - center v‖ ^ 2
        = (∑ j, ‖v j - center v‖ ^ 2) - ‖v k - center v‖ ^ 2 := by
      have h := Finset.sum_erase_add _ (fun j => ‖v j - center v‖ ^ 2) (Finset.mem_univ k)
      linarith [h]
    rw [hserase] at h0
    linarith [h0]
  -- Summing the four equations gives `S = 3s²/2`.
  have hS : ∑ j, ‖v j - center v‖ ^ 2 = 3 * s ^ 2 / 2 := by
    have hsum : (∑ k, 4 * ‖v k - center v‖ ^ 2)
        = ∑ k, (3 * s ^ 2 - ∑ j, ‖v j - center v‖ ^ 2) :=
      Finset.sum_congr rfl fun k _ => hE k
    simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at hsum
    linarith [hsum]
  have hk := hE i
  linarith [hS, hk]

lemma norm_sub_center_pos {v : Fin 4 → Pt} {s : ℝ} (hs : 0 < s)
    (hv : ∀ i j : Fin 4, i ≠ j → dist (v i) (v j) = s) (i : Fin 4) :
    0 < ‖v i - center v‖ := by
  have h3 : 0 < 3 * s ^ 2 / 8 := by have h2 := pow_pos hs 2; linarith
  rw [← norm_sub_center_sq hv i] at h3
  by_contra h
  push Not at h
  have h0 : ‖v i - center v‖ = 0 := le_antisymm h (norm_nonneg _)
  rw [h0] at h3
  simp at h3

lemma norm_sub_center_eq {v : Fin 4 → Pt} {s : ℝ}
    (hv : ∀ i j : Fin 4, i ≠ j → dist (v i) (v j) = s) (i j : Fin 4) :
    ‖v i - center v‖ = ‖v j - center v‖ := by
  have h1 := norm_sub_center_sq hv i
  have h2 := norm_sub_center_sq hv j
  have h3 : ‖v i - center v‖ ^ 2 = ‖v j - center v‖ ^ 2 := by linarith [h1, h2]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h3

lemma unitVec_norm {v : Fin 4 → Pt} {s : ℝ} (hs : 0 < s)
    (hv : ∀ i j : Fin 4, i ≠ j → dist (v i) (v j) = s) (i : Fin 4) :
    ‖unitVec v i‖ = 1 := by
  have hpos := norm_sub_center_pos hs hv i
  unfold unitVec
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (ne_of_gt hpos)]

/-- The unit vectors towards the vertices sum to zero
(since all vertices are at the same distance from the center). -/
lemma sum_unitVec {v : Fin 4 → Pt} {s : ℝ}
    (hv : ∀ i j : Fin 4, i ≠ j → dist (v i) (v j) = s) :
    ∑ i, unitVec v i = 0 := by
  have h1 : ∀ i : Fin 4, unitVec v i = (‖v 0 - center v‖)⁻¹ • (v i - center v) := by
    intro i
    unfold unitVec
    rw [norm_sub_center_eq hv i 0]
  have h2 : ∑ i, unitVec v i = ∑ i, (‖v 0 - center v‖)⁻¹ • (v i - center v) :=
    Finset.sum_congr rfl fun i _ => h1 i
  rw [h2, ← Finset.smul_sum, sum_sub_center, smul_zero]

lemma unitVec_inner {v : Fin 4 → Pt} {s : ℝ} (hs : 0 < s)
    (hv : ∀ i j : Fin 4, i ≠ j → dist (v i) (v j) = s) (i : Fin 4) :
    ⟪unitVec v i, v i - center v⟫ = ‖v i - center v‖ := by
  have hpos := norm_sub_center_pos hs hv i
  unfold unitVec
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq, inv_mul_eq_div,
    div_eq_iff (ne_of_gt hpos), pow_two]

/-- Cauchy–Schwarz applied to each term. -/
lemma unitVec_inner_le {v : Fin 4 → Pt} {s : ℝ} (hs : 0 < s)
    (hv : ∀ i j : Fin 4, i ≠ j → dist (v i) (v j) = s) (i : Fin 4) (p : Pt) :
    ⟪unitVec v i, v i - p⟫ ≤ dist p (v i) := by
  have h := real_inner_le_norm (unitVec v i) (v i - p)
  rw [unitVec_norm hs hv i, one_mul] at h
  rw [dist_eq_norm, norm_sub_rev]
  exact h

/-- Summing the unit-vector inner products gives the sum of the
distances from the center. -/
lemma sum_unitVec_inner {v : Fin 4 → Pt} {s : ℝ} (hs : 0 < s)
    (hv : ∀ i j : Fin 4, i ≠ j → dist (v i) (v j) = s) (p : Pt) :
    ∑ i, ⟪unitVec v i, v i - p⟫ = ∑ i, dist (center v) (v i) := by
  have hdecomp : ∀ i : Fin 4, v i - p = (v i - center v) - (p - center v) :=
    fun i => by abel
  calc ∑ i, ⟪unitVec v i, v i - p⟫
      = ∑ i, ⟪unitVec v i, (v i - center v) - (p - center v)⟫ :=
        Finset.sum_congr rfl fun i _ => by rw [hdecomp i]
    _ = ∑ i, (⟪unitVec v i, v i - center v⟫ - ⟪unitVec v i, p - center v⟫) :=
        Finset.sum_congr rfl fun i _ => inner_sub_right _ _ _
    _ = ∑ i, ⟪unitVec v i, v i - center v⟫ - ∑ i, ⟪unitVec v i, p - center v⟫ :=
        Finset.sum_sub_distrib _ _
    _ = ∑ i, ‖v i - center v‖ - ⟪∑ i, unitVec v i, p - center v⟫ := by
        rw [Finset.sum_congr rfl (fun i _ => unitVec_inner hs hv i), ← sum_inner]
    _ = ∑ i, ‖v i - center v‖ := by
        rw [sum_unitVec hv, inner_zero_left, sub_zero]
    _ = ∑ i, dist (center v) (v i) :=
        Finset.sum_congr rfl fun i _ => ((dist_eq_norm _ _).trans (norm_sub_rev _ _)).symm

/-- The non-strict inequality: the center minimizes the sum of distances. -/
lemma sum_dist_center_le {v : Fin 4 → Pt} {s : ℝ} (hs : 0 < s)
    (hv : ∀ i j : Fin 4, i ≠ j → dist (v i) (v j) = s) (p : Pt) :
    ∑ i, dist (center v) (v i) ≤ ∑ i, dist p (v i) := by
  rw [← sum_unitVec_inner hs hv p]
  exact Finset.sum_le_sum fun i _ => unitVec_inner_le hs hv i p

snip end

problem imo1966_p3 (v : Fin 4 → Pt) (s : ℝ) (hs : 0 < s)
    (hv : ∀ i j : Fin 4, i ≠ j → dist (v i) (v j) = s)
    (p : Pt) (hp : p ≠ center v) :
    ∑ i, dist (center v) (v i) < ∑ i, dist p (v i) := by
  refine lt_of_le_of_ne (sum_dist_center_le hs hv p) ?_
  intro heq
  apply hp
  -- Equality forces equality in every Cauchy–Schwarz term.
  have hterm : ∀ i, ⟪unitVec v i, v i - p⟫ = dist p (v i) := by
    have h2 : ∑ i, ⟪unitVec v i, v i - p⟫ = ∑ i, dist p (v i) := by
      rw [sum_unitVec_inner hs hv p]; exact heq
    exact fun i =>
      (Finset.sum_eq_sum_iff_of_le fun i _ => unitVec_inner_le hs hv i p).mp h2 i
        (Finset.mem_univ i)
  -- Hence `v i - p` is a nonnegative multiple of the unit vector `unitVec v i`.
  have hvec : ∀ i, v i - p = ⟪unitVec v i, v i - p⟫ • unitVec v i := by
    intro i
    have ha : 0 ≤ ⟪unitVec v i, v i - p⟫ := by
      rw [hterm i]; exact dist_nonneg
    have hz : ‖v i - p‖ = ⟪unitVec v i, v i - p⟫ := by
      rw [hterm i, dist_eq_norm, norm_sub_rev]
    have hsq : ‖(v i - p) - ⟪unitVec v i, v i - p⟫ • unitVec v i‖ ^ 2 = 0 := by
      have e1 := norm_sub_sq_real (v i - p) (⟪unitVec v i, v i - p⟫ • unitVec v i)
      have e2 : ⟪v i - p, ⟪unitVec v i, v i - p⟫ • unitVec v i⟫
          = ⟪unitVec v i, v i - p⟫ * ⟪unitVec v i, v i - p⟫ := by
        rw [real_inner_smul_right, real_inner_comm]
      have e3 : ‖⟪unitVec v i, v i - p⟫ • unitVec v i‖ = ⟪unitVec v i, v i - p⟫ := by
        rw [norm_smul, unitVec_norm hs hv i, mul_one, Real.norm_eq_abs, abs_of_nonneg ha]
      rw [e2, e3, hz] at e1
      linarith [e1]
    have h0 : (v i - p) - ⟪unitVec v i, v i - p⟫ • unitVec v i = 0 := by
      have h' := (pow_eq_zero_iff (show (2 : ℕ) ≠ 0 by norm_num)).mp hsq
      exact norm_eq_zero.mp h'
    exact sub_eq_zero.mp h0
  -- Therefore `p - center v` is a scalar multiple of every `v i - center v`.
  have h4 : ∀ i, v i - p = (‖v i - p‖ * ‖v 0 - center v‖⁻¹) • (v i - center v) := by
    intro i
    have hz : ⟪unitVec v i, v i - p⟫ = ‖v i - p‖ := by
      rw [hterm i, dist_eq_norm, norm_sub_rev]
    have h3 : unitVec v i = ‖v 0 - center v‖⁻¹ • (v i - center v) := by
      unfold unitVec
      rw [norm_sub_center_eq hv i 0]
    have h5 := hvec i
    rw [hz, h3, smul_smul] at h5
    exact h5
  have hscal : ∀ i, p - center v
      = (1 - ‖v i - p‖ * ‖v 0 - center v‖⁻¹) • (v i - center v) := by
    intro i
    have h2 : p - center v = (v i - center v) - (v i - p) := by abel
    rw [h2]
    conv_lhs => rw [h4 i]
    rw [sub_smul, one_smul]
  -- Comparing the scalars for the vertices `0` and `1` (which are not
  -- collinear with the center) forces the scalar to be zero.
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have hqq : (1 - ‖v 0 - p‖ * ‖v 0 - center v‖⁻¹) • (v 0 - center v)
      = (1 - ‖v 1 - p‖ * ‖v 0 - center v‖⁻¹) • (v 1 - center v) := by
    rw [← hscal 0, ← hscal 1]
  have e1 : (1 - ‖v 0 - p‖ * ‖v 0 - center v‖⁻¹) *
        ⟪v 0 - center v, v 0 - center v⟫
      = (1 - ‖v 1 - p‖ * ‖v 0 - center v‖⁻¹) *
        ⟪v 1 - center v, v 0 - center v⟫ := by
    have h := congr_arg (fun x => ⟪x, v 0 - center v⟫) hqq
    simpa only [real_inner_smul_left] using h
  have e2 : (1 - ‖v 0 - p‖ * ‖v 0 - center v‖⁻¹) *
        ⟪v 0 - center v, v 1 - center v⟫
      = (1 - ‖v 1 - p‖ * ‖v 0 - center v‖⁻¹) *
        ⟪v 1 - center v, v 1 - center v⟫ := by
    have h := congr_arg (fun x => ⟪x, v 1 - center v⟫) hqq
    simpa only [real_inner_smul_left] using h
  have hu00 : ⟪v 0 - center v, v 0 - center v⟫ = 3 * s ^ 2 / 8 := by
    rw [real_inner_self_eq_norm_sq, norm_sub_center_sq hv 0]
  have hu11 : ⟪v 1 - center v, v 1 - center v⟫ = 3 * s ^ 2 / 8 := by
    rw [real_inner_self_eq_norm_sq, norm_sub_center_sq hv 1]
  have hu01 : ⟪v 0 - center v, v 1 - center v⟫ = -s ^ 2 / 8 := by
    have h := inner_sub_center_sub_center hv h01
    rw [norm_sub_center_sq hv 0, norm_sub_center_sq hv 1] at h
    linarith [h]
  have hu10 : ⟪v 1 - center v, v 0 - center v⟫ = -s ^ 2 / 8 := by
    rw [real_inner_comm]; exact hu01
  rw [hu00, hu10] at e1
  rw [hu01, hu11] at e2
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hs)
  have g1 : 3 * (1 - ‖v 0 - p‖ * ‖v 0 - center v‖⁻¹)
      + (1 - ‖v 1 - p‖ * ‖v 0 - center v‖⁻¹) = 0 := by
    have e1' : s ^ 2 * (3 * (1 - ‖v 0 - p‖ * ‖v 0 - center v‖⁻¹)
        + (1 - ‖v 1 - p‖ * ‖v 0 - center v‖⁻¹)) = 0 := by
      linarith [e1]
    rcases mul_eq_zero.mp e1' with h | h
    · exact absurd h hs2
    · exact h
  have g2 : (1 - ‖v 0 - p‖ * ‖v 0 - center v‖⁻¹)
      + 3 * (1 - ‖v 1 - p‖ * ‖v 0 - center v‖⁻¹) = 0 := by
    have e2' : s ^ 2 * ((1 - ‖v 0 - p‖ * ‖v 0 - center v‖⁻¹)
        + 3 * (1 - ‖v 1 - p‖ * ‖v 0 - center v‖⁻¹)) = 0 := by
      linarith [e2]
    rcases mul_eq_zero.mp e2' with h | h
    · exact absurd h hs2
    · exact h
  have ht0 : (1 - ‖v 0 - p‖ * ‖v 0 - center v‖⁻¹) = 0 := by linarith [g1, g2]
  have hfin : p - center v = 0 := by rw [hscal 0, ht0, zero_smul]
  exact sub_eq_zero.mp hfin

end Imo1966P3
