/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 1970, Problem 6

In a plane there are 100 points, no three of which are collinear.
Consider all possible triangles having these points as vertices.
Prove that no more that 70% of these triangles are acute.
-/

namespace Imo1970P6

open scoped EuclideanGeometry Real RealInnerProductSpace
open EuclideanGeometry Finset

abbrev Pt := EuclideanSpace ℝ (Fin 2)

snip begin

/-
The solution follows the classical argument: among any four of the points, at
least one of the four triangles they determine is non-acute.  Hence among any
five points at least three of the ten triangles are non-acute, and a double
count over all 5-element subsets shows that at least 3/10 of all triangles are
non-acute.

For the four-point lemma, an affine dependence between the four points either
exhibits one point as a positive convex combination of the other three (and
then the three angles at that point cannot all be acute, by taking inner
products with the dependence), or splits the points into two pairs whose
connecting segments cross (and then the four angles of the convex
quadrilateral sum to `2 * π`, so one of them is at least `π / 2`).
-/

/-! ### Noncollinearity helpers -/

/-- Abbreviation for the noncollinearity hypothesis on a triple of points. -/
def NC (x y z : Pt) : Prop := ¬ Collinear ℝ ({x, y, z} : Set Pt)

lemma NC.swap₁₂ {x y z : Pt} (h : NC x y z) : NC y x z := by
  unfold NC at h ⊢; rwa [Set.insert_comm]

lemma NC.swap₂₃ {x y z : Pt} (h : NC x y z) : NC x z y := by
  unfold NC at h ⊢; rwa [Set.pair_comm z y]

lemma NC.ne₁₂ {x y z : Pt} (h : NC x y z) : x ≠ y := by
  rintro rfl
  rw [NC, Set.insert_idem] at h
  exact h (collinear_pair ℝ x z)

lemma NC.ne₂₃ {x y z : Pt} (h : NC x y z) : y ≠ z := (h.swap₁₂.swap₂₃).ne₁₂

lemma NC.ne₁₃ {x y z : Pt} (h : NC x y z) : x ≠ z := h.swap₂₃.ne₁₂

/-! ### Non-acute triangles -/

/-- The triple of points `X`, `Y`, `Z` has an angle of at least `π / 2`
(at `X`, at `Y`, or at `Z` respectively). -/
def Bad (X Y Z : Pt) : Prop :=
  π / 2 ≤ ∠ Y X Z ∨ π / 2 ≤ ∠ X Y Z ∨ π / 2 ≤ ∠ X Z Y

lemma Bad.swap₁₂ {X Y Z : Pt} (h : Bad X Y Z) : Bad Y X Z := by
  unfold Bad at h ⊢; rw [angle_comm X Z Y] at h; tauto

lemma Bad.swap₂₃ {X Y Z : Pt} (h : Bad X Y Z) : Bad X Z Y := by
  unfold Bad at h ⊢; rw [angle_comm Y X Z] at h; tauto

/-! ### The case of a point inside the triangle formed by three others -/

lemma inner_pos_of_angle_lt {u v : Pt} (hu : u ≠ 0) (hv : v ≠ 0)
    (h : InnerProductGeometry.angle u v < π / 2) : 0 < ⟪u, v⟫ := by
  have h0 : 0 < Real.cos (InnerProductGeometry.angle u v) :=
    Real.cos_pos_of_mem_Ioo
      ⟨by linarith [InnerProductGeometry.angle_nonneg u v, Real.pi_pos], h⟩
  rw [InnerProductGeometry.cos_angle] at h0
  have hn : 0 < ‖u‖ * ‖v‖ := mul_pos (norm_pos_iff.mpr hu) (norm_pos_iff.mpr hv)
  have h1 := mul_pos h0 hn
  rwa [div_mul_cancel₀ _ hn.ne'] at h1

/-- If `A` is a combination of `B`, `C`, `D` with positive weights (an interior point
of the triangle `B C D`), then the angles `∠ B A C` and `∠ B A D` cannot both be
acute. -/
lemma hull_case {A B C D : Pt} (hAB : A ≠ B) (hAC : A ≠ C) (hAD : A ≠ D)
    {wb wc wd : ℝ} (hwb : 0 < wb) (hwc : 0 < wc) (hwd : 0 < wd)
    (hvec : wb • (B - A) + wc • (C - A) + wd • (D - A) = 0) :
    π / 2 ≤ ∠ B A C ∨ π / 2 ≤ ∠ B A D := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hub : (B - A) ≠ 0 := sub_ne_zero.mpr (Ne.symm hAB)
  have huc : (C - A) ≠ 0 := sub_ne_zero.mpr (Ne.symm hAC)
  have hud : (D - A) ≠ 0 := sub_ne_zero.mpr (Ne.symm hAD)
  have p1 : 0 < ⟪B - A, C - A⟫ := inner_pos_of_angle_lt hub huc h1
  have p2 : 0 < ⟪B - A, D - A⟫ := inner_pos_of_angle_lt hub hud h2
  have h0 : ⟪B - A, wb • (B - A) + wc • (C - A) + wd • (D - A)⟫ = 0 := by
    rw [hvec, inner_zero_right]
  rw [inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right] at h0
  have hbb : 0 < ⟪B - A, B - A⟫ := real_inner_self_pos.mpr hub
  linarith [mul_pos hwb hbb, mul_pos hwc p1, mul_pos hwd p2]

/-! ### The case of two crossing segments -/

/-- If `w` lies strictly between `x` and `y`, then the angle subtended by `x` and `y`
at any point `z` splits as the sum of the angles subtended by `x, w` and by `w, y`. -/
lemma angle_split {x w y : Pt} (z : Pt) (h : Sbtw ℝ x w y) :
    ∠ x z y = ∠ x z w + ∠ w z y := by
  have t1 := angle_add_angle_add_angle_eq_pi z h.ne_left
  have t2 := angle_add_angle_add_angle_eq_pi z h.ne_right
  have t3 := angle_add_angle_add_angle_eq_pi z h.left_ne_right.symm
  have hline := angle_add_angle_eq_pi_of_angle_eq_pi z h.angle₁₂₃_eq_pi
  have r1 : ∠ z x w = ∠ z x y := h.angle_eq_right z
  have r2 : ∠ z y w = ∠ z y x := h.symm.angle_eq_right z
  have c1 : ∠ x w z = ∠ z w x := angle_comm _ _ _
  have c2 : ∠ y w z = ∠ z w y := angle_comm _ _ _
  have c3 : ∠ w z x = ∠ x z w := angle_comm _ _ _
  have c4 : ∠ x y z = ∠ z y x := angle_comm _ _ _
  have c5 : ∠ y z x = ∠ x z y := angle_comm _ _ _
  linarith

/-- If the segments `A C` and `B D` cross, then one of the angles of the
quadrilateral `A B C D` is at least `π / 2`; each of those four angles is an
angle of one of the four triangles on the points `A`, `B`, `C`, `D`. -/
lemma quad_case {A B C D Q : Pt} (hAC : Sbtw ℝ A Q C) (hBD : Sbtw ℝ B Q D)
    (hBA : B ≠ A) (hDC : D ≠ C) :
    π / 2 ≤ ∠ B A D ∨ π / 2 ≤ ∠ A B C ∨ π / 2 ≤ ∠ B C D ∨ π / 2 ≤ ∠ C D A := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3, h4⟩ := hcon
  have sA : ∠ B A D = ∠ B A Q + ∠ Q A D := angle_split A hBD
  have sC : ∠ B C D = ∠ B C Q + ∠ Q C D := angle_split C hBD
  have rA1 : ∠ B A Q = ∠ B A C := hAC.angle_eq_right B
  have rA2 : ∠ Q A D = ∠ C A D := by
    rw [angle_comm Q A D, angle_comm C A D]
    exact hAC.angle_eq_right D
  have rC1 : ∠ B C Q = ∠ B C A := hAC.symm.angle_eq_right B
  have rC2 : ∠ Q C D = ∠ A C D := by
    rw [angle_comm Q C D, angle_comm A C D]
    exact hAC.symm.angle_eq_right D
  have t1 : ∠ A B C + ∠ B C A + ∠ C A B = π := angle_add_angle_add_angle_eq_pi C hBA
  have t2 : ∠ C D A + ∠ D A C + ∠ A C D = π := angle_add_angle_add_angle_eq_pi A hDC
  have c1 : ∠ C A B = ∠ B A C := angle_comm _ _ _
  have c2 : ∠ D A C = ∠ C A D := angle_comm _ _ _
  linarith

/-- From an affine dependence with two positive and two negative weights, produce
the crossing point of the two segments. -/
lemma crossing_lemma {X Y Z W : Pt} {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : c < 0) (hd : d < 0) (hsum : a + b + c + d = 0)
    (hvec : a • X + b • Y + c • Z + d • W = 0) (hXY : X ≠ Y) (hZW : Z ≠ W) :
    ∃ Q, Sbtw ℝ X Q Y ∧ Sbtw ℝ Z Q W := by
  set S := a + b with hS
  have hS0 : 0 < S := by positivity
  refine ⟨AffineMap.lineMap X Y (b / S), ?_, ?_⟩
  · rw [sbtw_lineMap_iff]
    refine ⟨hXY, div_pos hb hS0, (div_lt_one hS0).mpr ?_⟩
    rw [hS]
    linarith
  · have hQ : (AffineMap.lineMap X Y (b / S) : Pt) = AffineMap.lineMap Z W (-d / S) := by
      rw [AffineMap.lineMap_apply_module', AffineMap.lineMap_apply_module']
      apply smul_right_injective Pt hS0.ne'
      show S • ((b / S) • (Y - X) + X) = S • ((-d / S) • (W - Z) + Z)
      rw [smul_add, smul_add, smul_smul, smul_smul,
          show S * (b / S) = b by rw [mul_comm, div_mul_cancel₀ _ hS0.ne'],
          show S * (-d / S) = -d by rw [mul_comm, div_mul_cancel₀ _ hS0.ne']]
      have hz : (a + b + c + d) • (Z : Pt) = (0 : ℝ) • (Z : Pt) := by
        rw [show a + b + c + d = 0 from hsum]
      linear_combination (norm := module) hvec - hz
    rw [hQ, sbtw_lineMap_iff]
    refine ⟨hZW, ?_, ?_⟩
    · exact div_pos (by linarith) hS0
    · rw [div_lt_one hS0, hS]
      linarith

/-! ### The four-point lemma -/

/-- An affine dependence between three points means they are collinear. -/
lemma collinear_of_dependent {X Y Z : Pt} {a b c : ℝ}
    (hvec : a • X + b • Y + c • Z = 0) (hsum : a + b + c = 0)
    (hne : ¬ (a = 0 ∧ b = 0 ∧ c = 0)) : Collinear ℝ ({X, Y, Z} : Set Pt) := by
  by_contra hcol
  have hind := affineIndependent_iff_not_collinear_set.mpr hcol
  rw [affineIndependent_iff_of_fintype] at hind
  have hs : ∑ i, ![a, b, c] i = 0 := by
    rw [Fin.sum_univ_three]
    simpa using hsum
  have h := hind ![a, b, c] hs (by
    rw [Finset.weightedVSub_eq_linear_combination _ hs, Fin.sum_univ_three]
    simpa using hvec)
  exact hne ⟨h 0, h 1, h 2⟩

/-- The core sign-analysis: given an affine dependence with all weights nonzero
and the first one positive, some triple of the four points is `Bad`. -/
lemma four_point_aux {A B C D : Pt} (h₁ : NC A B C) (h₂ : NC A B D)
    (h₃ : NC A C D) (w : Fin 4 → ℝ)
    (hw0 : w 0 + w 1 + w 2 + w 3 = 0)
    (hvec : w 0 • A + w 1 • B + w 2 • C + w 3 • D = 0)
    (hall : ∀ j, w j ≠ 0) (hpos : 0 < w 0) :
    Bad A B C ∨ Bad A B D ∨ Bad A C D ∨ Bad B C D := by
  have hzA : (w 0 + w 1 + w 2 + w 3) • (A : Pt) = (0 : ℝ) • (A : Pt) := by rw [hw0]
  have hzB : (w 0 + w 1 + w 2 + w 3) • (B : Pt) = (0 : ℝ) • (B : Pt) := by rw [hw0]
  have hzC : (w 0 + w 1 + w 2 + w 3) • (C : Pt) = (0 : ℝ) • (C : Pt) := by rw [hw0]
  have hzD : (w 0 + w 1 + w 2 + w 3) • (D : Pt) = (0 : ℝ) • (D : Pt) := by rw [hw0]
  rcases lt_or_gt_of_ne (hall 1) with s1 | s1 <;> rcases lt_or_gt_of_ne (hall 2) with s2 | s2 <;>
    rcases lt_or_gt_of_ne (hall 3) with s3 | s3
  · -- w1, w2, w3 < 0 : A is inside triangle B C D
    have hvec' : (-w 1) • (B - A) + (-w 2) • (C - A) + (-w 3) • (D - A) = 0 := by
      linear_combination (norm := module) -hvec + hzA
    have hbad := hull_case h₁.ne₁₂ h₁.ne₁₃ h₂.ne₁₃
      (neg_pos.mpr s1) (neg_pos.mpr s2) (neg_pos.mpr s3) hvec'
    rcases hbad with hb | hb
    · exact Or.inl (Or.inl hb)
    · exact Or.inr (Or.inl (Or.inl hb))
  · -- w1, w2 < 0 < w3 : segments A D and B C cross
    obtain ⟨Q, hQ1, hQ2⟩ := crossing_lemma hpos s3 s1 s2 (by linarith)
      (by linear_combination (norm := module) hvec) h₂.ne₁₃ h₁.ne₂₃
    have hbad := quad_case hQ1 hQ2 h₁.ne₁₂.symm h₃.ne₂₃
    rcases hbad with hb | hb | hb | hb
    · exact Or.inl (Or.inl hb)
    · exact Or.inr (Or.inl (Or.inr (Or.inl hb)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hb))))
    · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (angle_comm D C A ▸ hb)))))
  · -- w1, w3 < 0 < w2 : segments A C and B D cross
    obtain ⟨Q, hQ1, hQ2⟩ := crossing_lemma hpos s2 s1 s3 (by linarith)
      (by linear_combination (norm := module) hvec) h₁.ne₁₃ h₂.ne₂₃
    have hbad := quad_case hQ1 hQ2 h₁.ne₁₂.symm h₃.ne₂₃.symm
    rcases hbad with hb | hb | hb | hb
    · exact Or.inr (Or.inl (Or.inl hb))
    · exact Or.inl (Or.inr (Or.inl hb))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb))))
    · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (angle_comm C D A ▸ hb)))))
  · -- w1 < 0 < w2, w3 : B is inside triangle A C D
    have hvec' : (w 0) • (A - B) + (w 2) • (C - B) + (w 3) • (D - B) = 0 := by
      linear_combination (norm := module) hvec - hzB
    have hbad := hull_case h₁.ne₁₂.symm h₁.ne₂₃ h₂.ne₂₃ hpos s2 s3 hvec'
    rcases hbad with hb | hb
    · exact Or.inl (Or.inr (Or.inl hb))
    · exact Or.inr (Or.inl (Or.inr (Or.inl hb)))
  · -- w2, w3 < 0 < w1 : segments A B and C D cross
    obtain ⟨Q, hQ1, hQ2⟩ := crossing_lemma hpos s1 s2 s3 (by linarith)
      (by linear_combination (norm := module) hvec) h₁.ne₁₂ h₃.ne₂₃
    have hbad := quad_case hQ1 hQ2 h₁.ne₁₃.symm h₂.ne₂₃.symm
    rcases hbad with hb | hb | hb | hb
    · exact Or.inr (Or.inr (Or.inl (Or.inl hb)))
    · exact Or.inl (Or.inr (Or.inr hb))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hb)))
    · exact Or.inr (Or.inl (Or.inr (Or.inr (angle_comm B D A ▸ hb))))
  · -- w2 < 0 < w1, w3 : C is inside triangle A B D
    have hvec' : (w 0) • (A - C) + (w 1) • (B - C) + (w 3) • (D - C) = 0 := by
      linear_combination (norm := module) hvec - hzC
    have hbad := hull_case h₁.ne₁₃.symm h₁.ne₂₃.symm h₃.ne₂₃ hpos s1 s3 hvec'
    rcases hbad with hb | hb
    · exact Or.inl (Or.inr (Or.inr hb))
    · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl hb))))
  · -- w3 < 0 < w1, w2 : D is inside triangle A B C
    have hvec' : (w 0) • (A - D) + (w 1) • (B - D) + (w 2) • (C - D) = 0 := by
      linear_combination (norm := module) hvec - hzD
    have hbad := hull_case h₂.ne₁₃.symm h₂.ne₂₃.symm h₃.ne₂₃.symm hpos s1 s2 hvec'
    rcases hbad with hb | hb
    · exact Or.inr (Or.inl (Or.inr (Or.inr hb)))
    · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr hb))))
  · -- all weights positive: contradicts the sum being zero
    exact absurd hw0 (by linarith : (0:ℝ) < w 0 + w 1 + w 2 + w 3).ne'

/-- Among four points in the plane, no three of which are collinear, some triple
forms a triangle with an angle of at least `π / 2`. -/
lemma four_point {A B C D : Pt} (h₁ : NC A B C) (h₂ : NC A B D)
    (h₃ : NC A C D) (h₄ : NC B C D) :
    Bad A B C ∨ Bad A B D ∨ Bad A C D ∨ Bad B C D := by
  -- four points in the plane are affinely dependent
  have hdep : ¬ AffineIndependent ℝ ![A, B, C, D] := by
    intro hind
    have hcard := hind.card_le_finrank_succ
    have hfr : Module.finrank ℝ ↥(vectorSpan ℝ (Set.range ![A, B, C, D])) ≤ 2 :=
      le_trans (Submodule.finrank_le _) finrank_euclideanSpace_fin.le
    rw [Fintype.card_fin] at hcard
    lia
  rw [affineIndependent_iff_of_fintype] at hdep
  push Not at hdep
  obtain ⟨w, hw0, hwv, hwne⟩ := hdep
  rw [Finset.weightedVSub_eq_linear_combination _ hw0] at hwv
  rw [Fin.sum_univ_four] at hwv hw0
  have hvec : w 0 • A + w 1 • B + w 2 • C + w 3 • D = 0 := by simpa using hwv
  -- all weights are nonzero, since no three of the points are collinear
  have hor : w 0 = 0 ∨ w 1 = 0 ∨ w 2 = 0 ∨ w 3 = 0 →
      (w 0 = 0 ∧ w 1 = 0 ∧ w 2 = 0 ∧ w 3 = 0) := by
    rintro (hj | hj | hj | hj)
    · have h3 : w 1 = 0 ∧ w 2 = 0 ∧ w 3 = 0 := by
        by_contra hne
        exact h₄ (collinear_of_dependent
          (by rw [hj] at hvec; simpa using hvec) (by linarith) hne)
      exact ⟨hj, h3.1, h3.2.1, h3.2.2⟩
    · have h3 : w 0 = 0 ∧ w 2 = 0 ∧ w 3 = 0 := by
        by_contra hne
        exact h₃ (collinear_of_dependent
          (by rw [hj] at hvec; simpa using hvec) (by linarith) hne)
      exact ⟨h3.1, hj, h3.2.1, h3.2.2⟩
    · have h3 : w 0 = 0 ∧ w 1 = 0 ∧ w 3 = 0 := by
        by_contra hne
        exact h₂ (collinear_of_dependent
          (by rw [hj] at hvec; simpa using hvec) (by linarith) hne)
      exact ⟨h3.1, h3.2.1, hj, h3.2.2⟩
    · have h3 : w 0 = 0 ∧ w 1 = 0 ∧ w 2 = 0 := by
        by_contra hne
        exact h₁ (collinear_of_dependent
          (by rw [hj] at hvec; simpa using hvec) (by linarith) hne)
      exact ⟨h3.1, h3.2.1, h3.2.2, hj⟩
  have hall : ∀ j, w j ≠ 0 := by
    have hnot : ¬ (w 0 = 0 ∧ w 1 = 0 ∧ w 2 = 0 ∧ w 3 = 0) := by
      rintro ⟨e0, e1, e2, e3⟩
      obtain ⟨i, hi⟩ := hwne
      fin_cases i <;> first | exact hi e0 | exact hi e1 | exact hi e2 | exact hi e3
    intro j hj
    apply hnot
    apply hor
    fin_cases j <;> tauto
  rcases lt_or_gt_of_ne (hall 0) with h0 | h0
  · refine four_point_aux h₁ h₂ h₃ (fun i => -(w i)) ?_ ?_ ?_ ?_
    · show -(w 0) + -(w 1) + -(w 2) + -(w 3) = 0
      linarith
    · show -(w 0) • A + -(w 1) • B + -(w 2) • C + -(w 3) • D = 0
      linear_combination (norm := module) -hvec
    · intro j
      show -(w j) ≠ 0
      simpa using hall j
    · show 0 < -(w 0)
      linarith
  · exact four_point_aux h₁ h₂ h₃ w hw0 hvec hall h0

/-! ### Counting -/

section Counting

open scoped Classical

/-- The predicate from the problem statement: the 3-element subset `w` of indices
spans an acute-angled triangle. -/
def AcuteSet (P : Fin 100 → Pt) (w : Finset (Fin 100)) : Prop :=
  ∃ a b c : Fin 100, w = {a, b, c} ∧
    ∃ t : Affine.Triangle ℝ Pt, ![P a, P b, P c] = t.points ∧ t.AcuteAngled

lemma triple_perm {x y z a b c : Fin 100} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h : ({x, y, z} : Finset (Fin 100)) = {a, b, c}) :
    (a = x ∧ b = y ∧ c = z) ∨ (a = x ∧ b = z ∧ c = y) ∨
    (a = y ∧ b = x ∧ c = z) ∨ (a = y ∧ b = z ∧ c = x) ∨
    (a = z ∧ b = x ∧ c = y) ∨ (a = z ∧ b = y ∧ c = x) := by
  simp only [Finset.ext_iff, Finset.mem_insert, Finset.mem_singleton] at h
  have h1 := h x; have h2 := h y; have h3 := h z
  have h4 := h a; have h5 := h b; have h6 := h c
  grind

lemma not_acuteSet_of_bad {P : Fin 100 → Pt} {x y z : Fin 100}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hbad : Bad (P x) (P y) (P z)) : ¬ AcuteSet P {x, y, z} := by
  rintro ⟨a, b, c, habc, t, ht, hacute⟩
  have hbad' : Bad (P a) (P b) (P c) := by
    rcases triple_perm hxy hxz hyz habc with
      ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
      subst h1 <;> subst h2 <;> subst h3
    · exact hbad
    · exact hbad.swap₂₃
    · exact hbad.swap₁₂
    · exact hbad.swap₁₂.swap₂₃
    · exact hbad.swap₂₃.swap₁₂
    · exact hbad.swap₁₂.swap₂₃.swap₁₂
  obtain hB | hB | hB := hbad' <;>
    [have h2 := hacute 1 0 2 (by decide) (by decide) (by decide);
     have h2 := hacute 0 1 2 (by decide) (by decide) (by decide);
     have h2 := hacute 0 2 1 (by decide) (by decide) (by decide)] <;>
  · rw [← ht] at h2
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at h2
    linarith

/-- Among any four of the points, some three of them form a non-acute triangle. -/
lemma exists_nonacute_triple {P : Fin 100 → Pt}
    (hP : ∀ a b c : Fin 100, List.Nodup [a, b, c] → ¬ Collinear ℝ {P a, P b, P c})
    {s : Finset (Fin 100)} (hs : s.card = 4) :
    ∃ w : Finset (Fin 100), w ⊆ s ∧ w.card = 3 ∧ ¬ AcuteSet P w := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ := Finset.card_eq_four.mp hs
  have nc : ∀ x y z : Fin 100, x ≠ y → x ≠ z → y ≠ z → NC (P x) (P y) (P z) := by
    intro x y z h1 h2 h3
    exact hP x y z (by simp [h1, h2, h3])
  rcases four_point (nc a b c hab hac hbc) (nc a b d hab had hbd)
      (nc a c d hac had hcd) (nc b c d hbc hbd hcd) with hb | hb | hb | hb
  · exact ⟨{a, b, c}, by simp,
      Finset.card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩,
      not_acuteSet_of_bad hab hac hbc hb⟩
  · exact ⟨{a, b, d}, by simp [Finset.insert_subset_iff],
      Finset.card_eq_three.mpr ⟨a, b, d, hab, had, hbd, rfl⟩,
      not_acuteSet_of_bad hab had hbd hb⟩
  · exact ⟨{a, c, d}, by simp [Finset.insert_subset_iff],
      Finset.card_eq_three.mpr ⟨a, c, d, hac, had, hcd, rfl⟩,
      not_acuteSet_of_bad hac had hcd hb⟩
  · exact ⟨{b, c, d}, by simp,
      Finset.card_eq_three.mpr ⟨b, c, d, hbc, hbd, hcd, rfl⟩,
      not_acuteSet_of_bad hbc hbd hcd hb⟩

/-- The number of `(w.card + k)`-element subsets of `s` containing a fixed
`w ⊆ s` is `(s.card - w.card).choose k`. -/
lemma card_supersets {w s : Finset (Fin 100)} (hws : w ⊆ s) (k : ℕ) :
    ((s.powersetCard (w.card + k)).filter (fun u => w ⊆ u)).card =
      (s.card - w.card).choose k := by
  rw [← Finset.card_sdiff_of_subset hws, ← Finset.card_powersetCard k (s \ w)]
  apply Finset.card_bij' (fun u _ => u \ w) (fun v _ => v ∪ w)
  · intro u hu
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hu
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.sdiff_subset_sdiff hu.1.1 (Finset.Subset.refl w), ?_⟩
    rw [Finset.card_sdiff_of_subset hu.2, hu.1.2]
    lia
  · intro v hv
    rw [Finset.mem_powersetCard] at hv
    have hdisj : Disjoint v w := Finset.disjoint_of_subset_left hv.1 Finset.sdiff_disjoint
    rw [Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨Finset.union_subset (hv.1.trans (Finset.sdiff_subset)) hws, ?_⟩,
      Finset.subset_union_right⟩
    rw [Finset.card_union_of_disjoint hdisj, hv.2]
    lia
  · intro u hu
    rw [Finset.mem_filter] at hu
    exact Finset.sdiff_union_of_subset hu.2
  · intro v hv
    rw [Finset.mem_powersetCard] at hv
    have hdisj : Disjoint v w := Finset.disjoint_of_subset_left hv.1 Finset.sdiff_disjoint
    rw [Finset.union_sdiff_right, hdisj.sdiff_eq_left]

/-- Among any five of the points, at least three of the ten 3-element subsets
form a non-acute triangle. -/
lemma five_point_bound {P : Fin 100 → Pt}
    (hP : ∀ a b c : Fin 100, List.Nodup [a, b, c] → ¬ Collinear ℝ {P a, P b, P c})
    {s : Finset (Fin 100)} (hs : s.card = 5) :
    3 ≤ ((s.powersetCard 3).filter (fun w => ¬ AcuteSet P w)).card := by
  have choice : ∀ u : Finset (Fin 100), ∃ v : Finset (Fin 100),
      u.card = 4 → (v ⊆ u ∧ v.card = 3 ∧ ¬ AcuteSet P v) := by
    intro u
    by_cases hu : u.card = 4
    · obtain ⟨v, h1, h2, h3⟩ := exists_nonacute_triple hP hu
      exact ⟨v, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨∅, fun h => absurd h hu⟩
  choose f hf using choice
  have himg : ((s.powersetCard 4).image f) ⊆
      (s.powersetCard 3).filter (fun w => ¬ AcuteSet P w) := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    rw [Finset.mem_powersetCard] at hu
    obtain ⟨h1, h2, h3⟩ := hf u hu.2
    rw [Finset.mem_filter, Finset.mem_powersetCard]
    exact ⟨⟨h1.trans hu.1, h2⟩, h3⟩
  have hfib : ∀ v ∈ (s.powersetCard 4).image f,
      ((s.powersetCard 4).filter (fun u => f u = v)).card ≤ 2 := by
    intro v hv
    obtain ⟨u₀, hu₀, rfl⟩ := Finset.mem_image.mp hv
    rw [Finset.mem_powersetCard] at hu₀
    obtain ⟨hv1, hv2, -⟩ := hf u₀ hu₀.2
    calc ((s.powersetCard 4).filter (fun u => f u = f u₀)).card
        ≤ ((s.powersetCard 4).filter (fun u => f u₀ ⊆ u)).card := by
          apply Finset.card_le_card
          intro u hu
          rw [Finset.mem_filter] at hu ⊢
          obtain ⟨hu1, hu2⟩ := hu
          rw [Finset.mem_powersetCard] at hu1
          obtain ⟨hsub, -, -⟩ := hf u hu1.2
          exact ⟨by rwa [Finset.mem_powersetCard], by rw [← hu2]; exact hsub⟩
      _ = 2 := by
          rw [show (4:ℕ) = (f u₀).card + 1 by rw [hv2],
              card_supersets (hv1.trans hu₀.1), hs, hv2]
          decide
  have hcard5 : (s.powersetCard 4).card = 5 := by
    rw [Finset.card_powersetCard, hs]
    decide
  have hle := Finset.card_le_mul_card_image (s.powersetCard 4) 2 hfib
  rw [hcard5] at hle
  calc 3 ≤ ((s.powersetCard 4).image f).card := by lia
    _ ≤ _ := Finset.card_le_card himg

/-- Globally, at least `3 * (100.choose 5) / (97.choose 2) = 48510` of the
3-element subsets form a non-acute triangle. -/
lemma global_bound {P : Fin 100 → Pt}
    (hP : ∀ a b c : Fin 100, List.Nodup [a, b, c] → ¬ Collinear ℝ {P a, P b, P c}) :
    48510 ≤ (((univ : Finset (Fin 100)).powersetCard 3).filter
      (fun w => ¬ AcuteSet P w)).card := by
  set N := ((univ : Finset (Fin 100)).powersetCard 3).filter (fun w => ¬ AcuteSet P w)
    with hN
  have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := N) (t := (univ : Finset (Fin 100)).powersetCard 5)
    (r := fun (w u : Finset (Fin 100)) => w ⊆ u)
  have hsum1 : ∀ w ∈ N,
      ((((univ : Finset (Fin 100)).powersetCard 5)).bipartiteAbove
        (fun (w u : Finset (Fin 100)) => w ⊆ u) w).card = 4656 := by
    intro w hw
    rw [hN, Finset.mem_filter, Finset.mem_powersetCard] at hw
    obtain ⟨⟨-, hw3⟩, -⟩ := hw
    show ((((univ : Finset (Fin 100)).powersetCard 5)).filter (fun u => w ⊆ u)).card = 4656
    rw [show (5:ℕ) = w.card + 2 by rw [hw3], card_supersets (Finset.subset_univ w) 2,
        Finset.card_fin, hw3]
    decide
  have hsum2 : ∀ u ∈ (univ : Finset (Fin 100)).powersetCard 5,
      3 ≤ (N.bipartiteBelow (fun (w u : Finset (Fin 100)) => w ⊆ u) u).card := by
    intro u hu
    rw [Finset.mem_powersetCard] at hu
    have heq : N.bipartiteBelow (fun (w u : Finset (Fin 100)) => w ⊆ u) u =
        (u.powersetCard 3).filter (fun w => ¬ AcuteSet P w) := by
      ext w
      rw [Finset.bipartiteBelow, hN]
      simp only [Finset.mem_filter, Finset.mem_powersetCard]
      constructor
      · rintro ⟨⟨⟨-, hw3⟩, hwa⟩, hwu⟩
        exact ⟨⟨hwu, hw3⟩, hwa⟩
      · rintro ⟨⟨hwu, hw3⟩, hwa⟩
        exact ⟨⟨⟨Finset.subset_univ w, hw3⟩, hwa⟩, hwu⟩
    rw [heq]
    exact five_point_bound hP hu.2
  have e1 : ∑ w ∈ N, ((((univ : Finset (Fin 100)).powersetCard 5)).bipartiteAbove
      (fun (w u : Finset (Fin 100)) => w ⊆ u) w).card = N.card * 4656 :=
    Finset.sum_const_nat hsum1
  have e2 : ∑ u ∈ (univ : Finset (Fin 100)).powersetCard 5, 3 ≤
      ∑ u ∈ (univ : Finset (Fin 100)).powersetCard 5,
        (N.bipartiteBelow (fun (w u : Finset (Fin 100)) => w ⊆ u) u).card :=
    Finset.sum_le_sum hsum2
  have e4 : ((univ : Finset (Fin 100)).powersetCard 5).card = 75287520 := by
    rw [Finset.card_powersetCard, Finset.card_fin,
        Nat.choose_eq_descFactorial_div_factorial]
    rfl
  have key : 48510 * 4656 ≤ N.card * 4656 := by
    rw [← e1, hdc]
    calc 48510 * 4656 = 75287520 * 3 := by norm_num
      _ = ((univ : Finset (Fin 100)).powersetCard 5).card * 3 := by rw [e4]
      _ = ∑ u ∈ (univ : Finset (Fin 100)).powersetCard 5, 3 :=
        (Finset.sum_const_nat fun _ _ => rfl).symm
      _ ≤ _ := e2
  exact Nat.le_of_mul_le_mul_right key (by norm_num)

end Counting

snip end

problem imo1970_p6
    (P : Fin 100 → Pt)
    (hP : ∀ a b c : Fin 100,
             List.Nodup [a, b, c] → ¬ Collinear ℝ {P a, P b, P c}) :
    let cardAll := Nat.card { s : Finset (Fin 100) | s.card = 3 }
    let cardAcute := Nat.card { s : Finset (Fin 100) | s.card = 3 ∧
      ∃ a b c : Fin 100, s = {a, b, c} ∧
      ∃ t : Affine.Triangle ℝ Pt, ![P a, P b, P c] = t.points ∧ t.AcuteAngled }
    (cardAcute : ℚ) / cardAll ≤ 7 / 10 := by
  intro cardAll cardAcute
  classical
  have hPC : ((univ : Finset (Fin 100)).powersetCard 3).card = 161700 := by
    rw [Finset.card_powersetCard, Finset.card_fin,
        Nat.choose_eq_descFactorial_div_factorial]
    rfl
  have hAll : cardAll = 161700 := by
    have h1 : cardAll = ((univ : Finset (Fin 100)).powersetCard 3).card := by
      show Nat.card {s : Finset (Fin 100) | s.card = 3} = _
      exact Nat.subtype_card _ (fun u => by simp [Finset.mem_powersetCard])
    rw [h1, hPC]
  have hAcute : cardAcute = (((univ : Finset (Fin 100)).powersetCard 3).filter
      (fun w => AcuteSet P w)).card := by
    show Nat.card {s : Finset (Fin 100) | s.card = 3 ∧ AcuteSet P s} = _
    refine Nat.subtype_card _ (fun u => ?_)
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and,
      Set.mem_setOf_eq]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (Fin 100)).powersetCard 3) (p := fun w => AcuteSet P w)
  rw [hPC] at hsplit
  have hbound := global_bound hP
  have hac : (((univ : Finset (Fin 100)).powersetCard 3).filter
      (fun w => AcuteSet P w)).card ≤ 113190 := by
    lia
  rw [hAll, hAcute, div_le_iff₀ (by norm_num : (0:ℚ) < ((161700:ℕ):ℚ))]
  exact le_trans (b := (113190 : ℚ)) (mod_cast hac) (by norm_num)

end Imo1970P6
