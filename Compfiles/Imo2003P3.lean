/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.OfNorm
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 2003, Problem 3

A convex hexagon has the property that for any pair of opposite sides
the distance between their midpoints is ½√3 times the sum of their
lengths. Show that all the hexagon's angles are equal.

# Formalization note

Of the convexity hypothesis we only use that the vertices of the
hexagon are distinct, so we assume directly that consecutive vertices
are distinct and that the pairs of opposite vertices (A,D), (B,E) and
(C,F) are distinct.  The proof below is in fact purely algebraic and
is carried out in an arbitrary real inner product space; the key lemma
`hex_key` shows that the two angles at two consecutive vertices `B`
and `C` are both `2π/3`, and the full result follows by cyclically
relabeling the vertices.
-/

namespace Imo2003P3

open scoped EuclideanGeometry RealInnerProductSpace

/-- The Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

snip begin

/-- The distance between two midpoints, in vector form. -/
theorem dist_midpoint_midpoint_eq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (p₁ p₂ p₃ p₄ : V) :
    dist (midpoint ℝ p₁ p₂) (midpoint ℝ p₃ p₄) = ‖(p₁ - p₃) + (p₂ - p₄)‖ / 2 := by
  rw [dist_eq_norm, midpoint_eq_smul_add, midpoint_eq_smul_add, ← smul_sub, norm_smul]
  have hnorm2 : ‖(⅟2 : ℝ)‖ = 1 / 2 := by
    rw [invOf_eq_inv, Real.norm_eq_abs]
    norm_num
  rw [hnorm2, show (p₁ + p₂ - (p₃ + p₄)) = (p₁ - p₃) + (p₂ - p₄) by abel]
  ring

/-- The key lemma.  If six points of a real inner product space satisfy the
three midpoint conditions of the problem (with the indicated nondegeneracy),
then the interior angles of the hexagon `ABCDEF` at `B` and at `C` both
equal `2π/3`.

Write `X = A - D`, `Y = B - E`, `Z = C - F` for the three "long diagonal"
vectors.  The midpoint condition for the pair of opposite sides `(AB, DE)`
says `‖X + Y‖ = √3 (‖A - B‖ + ‖D - E‖) ≥ √3 ‖X - Y‖`, which squared gives
`‖X‖² + ‖Y‖² ≤ 4 ⟪X, Y⟫`; similarly for the other two pairs.  Adding the
three inequalities yields `‖X - Y + Z‖² ≤ 0`, hence `Y = X + Z` and equality
holds everywhere.  From the equalities one gets `‖X‖ = ‖Y‖ = ‖Z‖`,
`⟪X, Z⟫ = -‖X‖²/2`, and the triangle-inequality equalities show that each
side is parallel to a long diagonal, which gives the angles. -/
theorem hex_key {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (A B C D E F : V)
    (hAB : A ≠ B) (hBC : B ≠ C) (hCD : C ≠ D) (hAD : A ≠ D)
    (h1 : ‖(A - D) + (B - E)‖ = Real.sqrt 3 * (dist A B + dist D E))
    (h2 : ‖(B - E) + (C - F)‖ = Real.sqrt 3 * (dist B C + dist E F))
    (h3 : ‖(C - F) - (A - D)‖ = Real.sqrt 3 * (dist C D + dist F A)) :
    InnerProductGeometry.angle (A - B) (C - B) = 2 * Real.pi / 3 ∧
    InnerProductGeometry.angle (B - C) (D - C) = 2 * Real.pi / 3 := by
  -- Step 1: the three master inequalities.
  have hsq1 : 3 * ‖(A - D) - (B - E)‖ ^ 2 ≤ ‖(A - D) + (B - E)‖ ^ 2 := by
    rw [h1, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    have htri : ‖(A - D) - (B - E)‖ ≤ dist A B + dist D E := by
      rw [show (A - D) - (B - E) = (A - B) - (D - E) by abel, dist_eq_norm, dist_eq_norm]
      exact norm_sub_le _ _
    have hsq : ‖(A - D) - (B - E)‖ ^ 2 ≤ (dist A B + dist D E) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (add_nonneg dist_nonneg dist_nonneg)).mpr htri
    linarith [hsq]
  have I1 : ‖A - D‖ ^ 2 + ‖B - E‖ ^ 2 ≤ 4 * ⟪A - D, B - E⟫ := by
    have h1sq := norm_add_sq_real (A - D) (B - E)
    have h2sq := norm_sub_sq_real (A - D) (B - E)
    linarith [hsq1, h1sq, h2sq]
  have hsq2 : 3 * ‖(B - E) - (C - F)‖ ^ 2 ≤ ‖(B - E) + (C - F)‖ ^ 2 := by
    rw [h2, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    have htri : ‖(B - E) - (C - F)‖ ≤ dist B C + dist E F := by
      rw [show (B - E) - (C - F) = (B - C) - (E - F) by abel, dist_eq_norm, dist_eq_norm]
      exact norm_sub_le _ _
    have hsq : ‖(B - E) - (C - F)‖ ^ 2 ≤ (dist B C + dist E F) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (add_nonneg dist_nonneg dist_nonneg)).mpr htri
    linarith [hsq]
  have I2 : ‖B - E‖ ^ 2 + ‖C - F‖ ^ 2 ≤ 4 * ⟪B - E, C - F⟫ := by
    have h1sq := norm_add_sq_real (B - E) (C - F)
    have h2sq := norm_sub_sq_real (B - E) (C - F)
    linarith [hsq2, h1sq, h2sq]
  have hsq3 : 3 * ‖(C - F) + (A - D)‖ ^ 2 ≤ ‖(C - F) - (A - D)‖ ^ 2 := by
    rw [h3, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    have htri : ‖(C - F) + (A - D)‖ ≤ dist C D + dist F A := by
      rw [show (C - F) + (A - D) = (C - D) - (F - A) by abel, dist_eq_norm, dist_eq_norm]
      exact norm_sub_le _ _
    have hsq : ‖(C - F) + (A - D)‖ ^ 2 ≤ (dist C D + dist F A) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (add_nonneg dist_nonneg dist_nonneg)).mpr htri
    linarith [hsq]
  have I3 : ‖C - F‖ ^ 2 + ‖A - D‖ ^ 2 ≤ -4 * ⟪C - F, A - D⟫ := by
    have h1sq := norm_sub_sq_real (C - F) (A - D)
    have h2sq := norm_add_sq_real (C - F) (A - D)
    linarith [hsq3, h1sq, h2sq]
  -- Step 2: the three inequalities sum to `-‖X - Y + Z‖² ≥ 0`.
  have hexp : ‖(A - D) - (B - E) + (C - F)‖ ^ 2 =
      (‖A - D‖ ^ 2 - 2 * ⟪A - D, B - E⟫ + ‖B - E‖ ^ 2) +
        2 * (⟪A - D, C - F⟫ - ⟪B - E, C - F⟫) + ‖C - F‖ ^ 2 := by
    rw [norm_add_sq_real, norm_sub_sq_real, inner_sub_left (A - D) (B - E) (C - F)]
  have hs0 : ‖(A - D) - (B - E) + (C - F)‖ ^ 2 = 0 := by
    have hnn : 0 ≤ ‖(A - D) - (B - E) + (C - F)‖ ^ 2 := sq_nonneg _
    rw [hexp] at hnn ⊢
    linarith [I1, I2, I3, hnn, real_inner_comm (C - F) (A - D)]
  have hs0' := hs0
  rw [hexp] at hs0'
  have hXYZ : (A - D) - (B - E) + (C - F) = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hs0)
  have hcomm : ⟪C - F, A - D⟫ = ⟪A - D, C - F⟫ := real_inner_comm _ _
  -- Hence equality holds in each of the three inequalities.
  have eI1 : 4 * ⟪A - D, B - E⟫ = ‖A - D‖ ^ 2 + ‖B - E‖ ^ 2 := by
    linarith [I1, I2, I3, hs0', hcomm]
  have eI2 : 4 * ⟪B - E, C - F⟫ = ‖B - E‖ ^ 2 + ‖C - F‖ ^ 2 := by
    linarith [I1, I2, I3, hs0', hcomm]
  have eI3 : -4 * ⟪C - F, A - D⟫ = ‖C - F‖ ^ 2 + ‖A - D‖ ^ 2 := by
    linarith [I1, I2, I3, hs0', hcomm]
  -- `Y = X + Z`.
  have hY : B - E = (A - D) + (C - F) := by
    have h' : (A - D) + (C - F) - (B - E) = 0 := by
      rw [← hXYZ]; abel
    rw [sub_eq_zero] at h'
    exact h'.symm
  -- Consequences: the three diagonal vectors have equal lengths and known
  -- mutual inner products.
  have k1 : ⟪A - D, B - E⟫ = ‖A - D‖ ^ 2 + ⟪A - D, C - F⟫ := by
    rw [hY, inner_add_right, real_inner_self_eq_norm_sq]
  have k2 : ‖B - E‖ ^ 2 = ‖A - D‖ ^ 2 + 2 * ⟪A - D, C - F⟫ + ‖C - F‖ ^ 2 := by
    rw [hY]; exact norm_add_sq_real _ _
  have hnormXZ2 : ‖A - D‖ ^ 2 = ‖C - F‖ ^ 2 := by
    linarith [eI1, eI3, k1, k2, hcomm]
  have hinnerXZ : ⟪A - D, C - F⟫ = -‖A - D‖ ^ 2 / 2 := by
    linarith [eI3, hnormXZ2, hcomm]
  have hnormY2 : ‖B - E‖ ^ 2 = ‖A - D‖ ^ 2 := by
    linarith [k2, hinnerXZ, hnormXZ2]
  have hinnerXY : ⟪A - D, B - E⟫ = ‖A - D‖ ^ 2 / 2 := by
    linarith [k1, hinnerXZ]
  have hnormXZ : ‖A - D‖ = ‖C - F‖ :=
    (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hnormXZ2
  have hnormXY : ‖A - D‖ = ‖B - E‖ :=
    ((sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hnormY2).symm
  have hXne : A - D ≠ 0 := sub_ne_zero.mpr hAD
  have hXn : ‖A - D‖ ≠ 0 := norm_ne_zero_iff.mpr hXne
  have hZne : C - F ≠ 0 := by
    intro h
    exact hXn (by rw [hnormXZ, h, norm_zero])
  have hYne : B - E ≠ 0 := by
    intro h
    exact hXn (by rw [hnormXY, h, norm_zero])
  -- Step 3: equality in the triangle inequalities, giving `SameRay` relations.
  have hs1 : ‖A - B‖ + ‖D - E‖ = ‖(A - B) + (E - D)‖ := by
    have hsq : ‖(A - D) + (B - E)‖ ^ 2 = 3 * ‖(A - D) - (B - E)‖ ^ 2 := by
      have h1sq := norm_add_sq_real (A - D) (B - E)
      have h2sq := norm_sub_sq_real (A - D) (B - E)
      linarith [eI1, h1sq, h2sq]
    rw [h1, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), dist_eq_norm, dist_eq_norm] at hsq
    have h3' : (‖A - B‖ + ‖D - E‖) ^ 2 = ‖(A - D) - (B - E)‖ ^ 2 := by linarith [hsq]
    have h' := (sq_eq_sq₀ (add_nonneg (norm_nonneg _) (norm_nonneg _))
      (norm_nonneg _)).mp h3'
    rw [h']; congr 1; abel
  have hSR1 : SameRay ℝ (A - B) (E - D) := by
    rw [sameRay_iff_norm_add]
    have hne : ‖D - E‖ = ‖E - D‖ := by rw [← norm_neg (D - E), neg_sub]
    rw [hne] at hs1
    exact hs1.symm
  obtain ⟨t₁, ht₁0, ht₁⟩ := SameRay.exists_nonneg_left hSR1 (sub_ne_zero.mpr hAB)
  have hs2 : ‖B - C‖ + ‖E - F‖ = ‖(B - C) + (F - E)‖ := by
    have hsq : ‖(B - E) + (C - F)‖ ^ 2 = 3 * ‖(B - E) - (C - F)‖ ^ 2 := by
      have h1sq := norm_add_sq_real (B - E) (C - F)
      have h2sq := norm_sub_sq_real (B - E) (C - F)
      linarith [eI2, h1sq, h2sq]
    rw [h2, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), dist_eq_norm, dist_eq_norm] at hsq
    have h3' : (‖B - C‖ + ‖E - F‖) ^ 2 = ‖(B - E) - (C - F)‖ ^ 2 := by linarith [hsq]
    have h' := (sq_eq_sq₀ (add_nonneg (norm_nonneg _) (norm_nonneg _))
      (norm_nonneg _)).mp h3'
    rw [h']; congr 1; abel
  have hSR2 : SameRay ℝ (B - C) (F - E) := by
    rw [sameRay_iff_norm_add]
    have hne : ‖E - F‖ = ‖F - E‖ := by rw [← norm_neg (E - F), neg_sub]
    rw [hne] at hs2
    exact hs2.symm
  obtain ⟨t₂, ht₂0, ht₂⟩ := SameRay.exists_nonneg_left hSR2 (sub_ne_zero.mpr hBC)
  have hs3 : ‖C - D‖ + ‖F - A‖ = ‖(C - D) + (A - F)‖ := by
    have hsq : ‖(C - F) - (A - D)‖ ^ 2 = 3 * ‖(C - F) + (A - D)‖ ^ 2 := by
      have h1sq := norm_sub_sq_real (C - F) (A - D)
      have h2sq := norm_add_sq_real (C - F) (A - D)
      linarith [eI3, h1sq, h2sq]
    rw [h3, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), dist_eq_norm, dist_eq_norm] at hsq
    have h3' : (‖C - D‖ + ‖F - A‖) ^ 2 = ‖(C - F) + (A - D)‖ ^ 2 := by linarith [hsq]
    have h' := (sq_eq_sq₀ (add_nonneg (norm_nonneg _) (norm_nonneg _))
      (norm_nonneg _)).mp h3'
    rw [h']; congr 1; abel
  have hSR3 : SameRay ℝ (C - D) (A - F) := by
    rw [sameRay_iff_norm_add]
    have hne : ‖F - A‖ = ‖A - F‖ := by rw [← norm_neg (F - A), neg_sub]
    rw [hne] at hs3
    exact hs3.symm
  obtain ⟨t₃, ht₃0, ht₃⟩ := SameRay.exists_nonneg_left hSR3 (sub_ne_zero.mpr hCD)
  -- Step 4: each side of the hexagon is parallel to a long diagonal.
  have hp1 : A - B = (1 / (1 + t₁)) • (F - C) := by
    have hde : (A - D) - (B - E) = (1 + t₁) • (A - B) := by
      rw [show (A - D) - (B - E) = (A - B) + (E - D) by abel, ← ht₁, add_smul, one_smul]
    have hfc : F - C = (1 + t₁) • (A - B) := by
      have hh : F - C = (A - D) - (B - E) := by rw [hY]; abel
      rw [hh, hde]
    rw [hfc, smul_smul, one_div,
      inv_mul_cancel₀ (ne_of_gt (by linarith : (0:ℝ) < 1 + t₁)), one_smul]
  have hp2 : B - C = (1 / (1 + t₂)) • (A - D) := by
    have hde : (B - E) - (C - F) = (1 + t₂) • (B - C) := by
      rw [show (B - E) - (C - F) = (B - C) + (F - E) by abel, ← ht₂, add_smul, one_smul]
    have had : A - D = (1 + t₂) • (B - C) := by
      have hh : A - D = (B - E) - (C - F) := by rw [hY]; abel
      rw [hh, hde]
    rw [had, smul_smul, one_div,
      inv_mul_cancel₀ (ne_of_gt (by linarith : (0:ℝ) < 1 + t₂)), one_smul]
  have hp3 : C - D = (1 / (1 + t₃)) • (B - E) := by
    have hbe : B - E = (1 + t₃) • (C - D) := by
      rw [hY, show (A - D) + (C - F) = (C - D) + (A - F) by abel, ← ht₃, add_smul, one_smul]
    rw [hbe, smul_smul, one_div,
      inv_mul_cancel₀ (ne_of_gt (by linarith : (0:ℝ) < 1 + t₃)), one_smul]
  -- Step 5: angle computations.
  have h2pi3 : Real.arccos (-1/2) = 2 * Real.pi / 3 := by
    have hcos : Real.cos (2 * Real.pi / 3) = -1/2 := by
      have hh : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
      rw [hh, Real.cos_pi_sub, Real.cos_pi_div_three]
      norm_num
    rw [← hcos]
    exact Real.arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hpi3 : Real.arccos (1/2) = Real.pi / 3 := by
    rw [← Real.cos_pi_div_three]
    exact Real.arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hangle : ∀ x y : V, InnerProductGeometry.angle x y =
      Real.arccos (⟪x, y⟫ / (‖x‖ * ‖y‖)) := fun x y => rfl
  have angle_eq_2pi3 : ∀ u v : V, u ≠ 0 → v ≠ 0 → ‖u‖ = ‖v‖ →
      ⟪u, v⟫ = -‖u‖ ^ 2 / 2 → InnerProductGeometry.angle u v = 2 * Real.pi / 3 := by
    intro u v hu hv huv hi
    have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hvn : ‖v‖ ≠ 0 := ne_of_gt hvpos
    rw [hangle, hi, huv]
    have e : -‖v‖ ^ 2 / 2 / (‖v‖ * ‖v‖) = -1/2 := by
      field_simp
    rw [e, h2pi3]
  have angle_eq_pi3 : ∀ u v : V, u ≠ 0 → v ≠ 0 → ‖u‖ = ‖v‖ →
      ⟪u, v⟫ = ‖u‖ ^ 2 / 2 → InnerProductGeometry.angle u v = Real.pi / 3 := by
    intro u v hu hv huv hi
    have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hvn : ‖v‖ ≠ 0 := ne_of_gt hvpos
    rw [hangle, hi, huv]
    have e : ‖v‖ ^ 2 / 2 / (‖v‖ * ‖v‖) = 1/2 := by
      field_simp
    rw [e, hpi3]
  have h1t1 : (0:ℝ) < 1 / (1 + t₁) := by
    have h : (0:ℝ) < 1 + t₁ := by linarith
    positivity
  have h1t2 : (0:ℝ) < 1 / (1 + t₂) := by
    have h : (0:ℝ) < 1 + t₂ := by linarith
    positivity
  have h1t3 : (0:ℝ) < 1 / (1 + t₃) := by
    have h : (0:ℝ) < 1 + t₃ := by linarith
    positivity
  have hangle1 : InnerProductGeometry.angle (A - B) (C - B) = 2 * Real.pi / 3 := by
    have hCB : C - B = (1 / (1 + t₂)) • (D - A) := by
      rw [show C - B = -(B - C) by abel, hp2, ← smul_neg, neg_sub]
    rw [hp1, hCB, InnerProductGeometry.angle_smul_left_of_pos _ _ h1t1,
      InnerProductGeometry.angle_smul_right_of_pos _ _ h1t2,
      show F - C = -(C - F) by abel, show D - A = -(A - D) by abel,
      InnerProductGeometry.angle_neg_neg, InnerProductGeometry.angle_comm]
    exact angle_eq_2pi3 (A - D) (C - F) hXne hZne hnormXZ hinnerXZ
  have hangle2 : InnerProductGeometry.angle (B - C) (D - C) = 2 * Real.pi / 3 := by
    have hDC : D - C = (1 / (1 + t₃)) • (E - B) := by
      rw [show D - C = -(C - D) by abel, hp3, ← smul_neg, neg_sub]
    rw [hp2, hDC, InnerProductGeometry.angle_smul_left_of_pos _ _ h1t2,
      InnerProductGeometry.angle_smul_right_of_pos _ _ h1t3,
      show E - B = -(B - E) by abel, InnerProductGeometry.angle_neg_right,
      angle_eq_pi3 (A - D) (B - E) hXne hYne hnormXY hinnerXY]
    ring
  exact ⟨hangle1, hangle2⟩

snip end

problem imo2003_p3 (A B C D E F : Pt)
    (hAB : A ≠ B) (hBC : B ≠ C) (hCD : C ≠ D)
    (hDE : D ≠ E) (hEF : E ≠ F) (hFA : F ≠ A)
    (hAD : A ≠ D) (hBE : B ≠ E) (hCF : C ≠ F)
    (h1 : dist (midpoint ℝ A B) (midpoint ℝ D E) =
      Real.sqrt 3 / 2 * (dist A B + dist D E))
    (h2 : dist (midpoint ℝ B C) (midpoint ℝ E F) =
      Real.sqrt 3 / 2 * (dist B C + dist E F))
    (h3 : dist (midpoint ℝ C D) (midpoint ℝ F A) =
      Real.sqrt 3 / 2 * (dist C D + dist F A)) :
    ∠ A B C = ∠ B C D ∧ ∠ B C D = ∠ C D E ∧ ∠ C D E = ∠ D E F ∧
      ∠ D E F = ∠ E F A ∧ ∠ E F A = ∠ F A B := by
  -- Rewrite the midpoint conditions in vector form.
  have g1 : ‖(A - D) + (B - E)‖ = Real.sqrt 3 * (dist A B + dist D E) := by
    have hm := dist_midpoint_midpoint_eq A B D E
    rw [hm] at h1
    calc ‖(A - D) + (B - E)‖
        = 2 * (‖(A - D) + (B - E)‖ / 2) := by ring
      _ = 2 * (Real.sqrt 3 / 2 * (dist A B + dist D E)) := by rw [h1]
      _ = Real.sqrt 3 * (dist A B + dist D E) := by ring
  have g2 : ‖(B - E) + (C - F)‖ = Real.sqrt 3 * (dist B C + dist E F) := by
    have hm := dist_midpoint_midpoint_eq B C E F
    rw [hm] at h2
    calc ‖(B - E) + (C - F)‖
        = 2 * (‖(B - E) + (C - F)‖ / 2) := by ring
      _ = 2 * (Real.sqrt 3 / 2 * (dist B C + dist E F)) := by rw [h2]
      _ = Real.sqrt 3 * (dist B C + dist E F) := by ring
  have g3 : ‖(C - F) - (A - D)‖ = Real.sqrt 3 * (dist C D + dist F A) := by
    have hm := dist_midpoint_midpoint_eq C D F A
    rw [show (C - F) + (D - A) = (C - F) - (A - D) by abel] at hm
    rw [hm] at h3
    calc ‖(C - F) - (A - D)‖
        = 2 * (‖(C - F) - (A - D)‖ / 2) := by ring
      _ = 2 * (Real.sqrt 3 / 2 * (dist C D + dist F A)) := by rw [h3]
      _ = Real.sqrt 3 * (dist C D + dist F A) := by ring
  -- The angles at `B` and `C`.
  obtain ⟨hA1, hA2⟩ := hex_key A B C D E F hAB hBC hCD hAD g1 g2 g3
  -- Cyclically relabel: the hexagon `(C, D, E, F, A, B)` also satisfies the
  -- conditions, which gives the angles at `D` and `E`.
  have g1' : ‖(C - F) + (D - A)‖ = Real.sqrt 3 * (dist C D + dist F A) := by
    rw [show (C - F) + (D - A) = (C - F) - (A - D) by abel]; exact g3
  have g2' : ‖(D - A) + (E - B)‖ = Real.sqrt 3 * (dist D E + dist A B) := by
    rw [show (D - A) + (E - B) = -((A - D) + (B - E)) by abel, norm_neg,
      show dist D E + dist A B = dist A B + dist D E by rw [add_comm]]
    exact g1
  have g3' : ‖(E - B) - (C - F)‖ = Real.sqrt 3 * (dist E F + dist B C) := by
    rw [show (E - B) - (C - F) = -((B - E) + (C - F)) by abel, norm_neg,
      show dist E F + dist B C = dist B C + dist E F by rw [add_comm]]
    exact g2
  obtain ⟨hC1, hC2⟩ := hex_key C D E F A B hCD hDE hEF hCF g1' g2' g3'
  -- And once more with `(E, F, A, B, C, D)`, giving the angles at `F` and `A`.
  have g1'' : ‖(E - B) + (F - C)‖ = Real.sqrt 3 * (dist E F + dist B C) := by
    rw [show (E - B) + (F - C) = -((B - E) + (C - F)) by abel, norm_neg,
      show dist E F + dist B C = dist B C + dist E F by rw [add_comm]]
    exact g2
  have g2'' : ‖(F - C) + (A - D)‖ = Real.sqrt 3 * (dist F A + dist C D) := by
    rw [show (F - C) + (A - D) = -((C - F) - (A - D)) by abel, norm_neg,
      show dist F A + dist C D = dist C D + dist F A by rw [add_comm]]
    exact g3
  have g3'' : ‖(A - D) - (E - B)‖ = Real.sqrt 3 * (dist A B + dist D E) := by
    rw [show (A - D) - (E - B) = (A - D) + (B - E) by abel]; exact g1
  obtain ⟨hE1, hE2⟩ := hex_key E F A B C D hEF hFA hAB hBE.symm g1'' g2'' g3''
  -- Convert to Euclidean angles and conclude.
  have eABC : ∠ A B C = 2 * Real.pi / 3 := by
    show InnerProductGeometry.angle (A -ᵥ B) (C -ᵥ B) = _
    rw [vsub_eq_sub, vsub_eq_sub]; exact hA1
  have eBCD : ∠ B C D = 2 * Real.pi / 3 := by
    show InnerProductGeometry.angle (B -ᵥ C) (D -ᵥ C) = _
    rw [vsub_eq_sub, vsub_eq_sub]; exact hA2
  have eCDE : ∠ C D E = 2 * Real.pi / 3 := by
    show InnerProductGeometry.angle (C -ᵥ D) (E -ᵥ D) = _
    rw [vsub_eq_sub, vsub_eq_sub]; exact hC1
  have eDEF : ∠ D E F = 2 * Real.pi / 3 := by
    show InnerProductGeometry.angle (D -ᵥ E) (F -ᵥ E) = _
    rw [vsub_eq_sub, vsub_eq_sub]; exact hC2
  have eEFA : ∠ E F A = 2 * Real.pi / 3 := by
    show InnerProductGeometry.angle (E -ᵥ F) (A -ᵥ F) = _
    rw [vsub_eq_sub, vsub_eq_sub]; exact hE1
  have eFAB : ∠ F A B = 2 * Real.pi / 3 := by
    show InnerProductGeometry.angle (F -ᵥ A) (B -ᵥ A) = _
    rw [vsub_eq_sub, vsub_eq_sub]; exact hE2
  exact ⟨eABC.trans eBCD.symm, eBCD.trans eCDE.symm, eCDE.trans eDEF.symm,
    eDEF.trans eEFA.symm, eEFA.trans eFAB.symm⟩

end Imo2003P3
