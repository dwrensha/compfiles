/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Geometry.Euclidean.Angle.Sphere
public import Mathlib.Geometry.Euclidean.Triangle
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 2022, Problem 4

Let `ABCDE` be a convex pentagon such that `BC = DE`. Assume that there is a point `T`
inside `ABCDE` with `TB = TD`, `TC = TE` and `∠ABT = ∠TEA`. Let line `AB` intersect lines
`CD` and `CT` at points `P` and `Q`, respectively. Assume that the points `P`, `B`, `A`, `Q`
occur on their line in that order. Let line `AE` intersect `CD` and `DT` at points `R` and
`S`, respectively. Assume that the points `R`, `E`, `A`, `S` occur on their line in that
order. Prove that the points `P`, `S`, `Q`, `R` lie on a circle.
-/

namespace Imo2022P4

open scoped EuclideanGeometry

open EuclideanGeometry Affine

snip begin

/-- The plane in which the problem takes place. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

local instance planeFiniteDim :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
  ⟨finrank_euclideanSpace_fin⟩

noncomputable local instance someOrientation :
    Module.Oriented ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2) :=
  ⟨Module.Basis.orientation (Module.finBasisOfFinrankEq _ _ planeFiniteDim.out)⟩

/-- The sign of an oriented angle equals the sign of the area form. -/
theorem sign_oangle_eq_sign_areaForm (U V X : Pt) :
    (∡ U V X).sign = SignType.sign (positiveOrientation.areaForm (U -ᵥ V) (X -ᵥ V)) := by
  have him : (positiveOrientation.kahler (U -ᵥ V) (X -ᵥ V)).im =
      positiveOrientation.areaForm (U -ᵥ V) (X -ᵥ V) := by
    simp [Orientation.kahler_apply_apply]
  have e : ∡ U V X =
      ((Complex.arg (positiveOrientation.kahler (U -ᵥ V) (X -ᵥ V)) : ℝ) : Real.Angle) := rfl
  rw [e, Real.Angle.sign, Real.Angle.sin_coe, Complex.sin_arg, him]
  by_cases ha : positiveOrientation.areaForm (U -ᵥ V) (X -ᵥ V) = 0
  · rw [ha, zero_div]
  · have hz : positiveOrientation.kahler (U -ᵥ V) (X -ᵥ V) ≠ 0 := by
      intro hzc
      rw [hzc, Complex.zero_im] at him
      exact ha him.symm
    have hn : 0 < ‖positiveOrientation.kahler (U -ᵥ V) (X -ᵥ V)‖ := norm_pos_iff.mpr hz
    rcases lt_or_gt_of_ne ha with hlt | hgt
    · rw [sign_eq_neg_one_iff.mpr hlt,
        sign_eq_neg_one_iff.mpr (div_neg_of_neg_of_pos hlt hn)]
    · rw [sign_eq_one_iff.mpr hgt, sign_eq_one_iff.mpr (div_pos hgt hn)]

/-- Evaluating `Z ↦ areaForm a (Z -ᵥ V)` on a point of the segment `XY` gives the
corresponding affine combination of the values at `X` and `Y`. -/
private theorem areaForm_vsub_lineMap (a V X Y : Pt) (t : ℝ) :
    positiveOrientation.areaForm a (AffineMap.lineMap X Y t -ᵥ V) =
      (1 - t) * positiveOrientation.areaForm a (X -ᵥ V) +
        t * positiveOrientation.areaForm a (Y -ᵥ V) := by
  have hZ : AffineMap.lineMap X Y t -ᵥ V = (1 - t) • (X -ᵥ V) + t • (Y -ᵥ V) := by
    rw [AffineMap.lineMap_apply, vadd_vsub_assoc, ← vsub_sub_vsub_cancel_right Y X V,
      smul_sub, sub_smul, one_smul]
    abel
  rw [hZ, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- Strictly-between points inherit the side of a line: if `X` and `Y` are strictly on
the positive-sign side of line `UV`, so is any point strictly between them. -/
theorem sign_oangle_eq_one_of_sbtw {U V X Y Z : Pt}
    (hX : (∡ U V X).sign = 1) (hY : (∡ U V Y).sign = 1) (h : Sbtw ℝ X Z Y) :
    (∡ U V Z).sign = 1 := by
  rw [sign_oangle_eq_sign_areaForm] at hX hY ⊢
  rw [sign_eq_one_iff] at hX hY ⊢
  obtain ⟨hw, hZX, hZY⟩ := h
  obtain ⟨t, ht, rfl⟩ := hw
  rw [Set.mem_Icc] at ht
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hZX (AffineMap.lineMap_apply_zero X Y)
  have ht1 : t ≠ 1 := by
    rintro rfl
    exact hZY (AffineMap.lineMap_apply_one X Y)
  rw [areaForm_vsub_lineMap]
  have ht0' : 0 < t := lt_of_le_of_ne ht.1 ht0.symm
  have h1t : 0 < 1 - t := sub_pos.mpr (lt_of_le_of_ne ht.2 ht1)
  exact add_pos (mul_pos h1t hX) (mul_pos ht0' hY)

/-- Crossing lemma: if `X` and `Y` are strictly on opposite sides of line `UV`, and `Q`
lies on both line `UV` and line `XY`, then `Q` is strictly between `X` and `Y`. -/
theorem sbtw_of_sides_opposite {U V X Y Q : Pt}
    (hX : (∡ U V X).sign = -1) (hY : (∡ U V Y).sign = 1)
    (hUV : Collinear ℝ ({U, V, Q} : Set Pt))
    (hXY : Collinear ℝ ({X, Y, Q} : Set Pt)) :
    Sbtw ℝ X Q Y := by
  rw [sign_oangle_eq_sign_areaForm] at hX hY
  have hfX : positiveOrientation.areaForm (U -ᵥ V) (X -ᵥ V) < 0 := sign_eq_neg_one_iff.mp hX
  have hfY : 0 < positiveOrientation.areaForm (U -ᵥ V) (Y -ᵥ V) := sign_eq_one_iff.mp hY
  have hfQ : positiveOrientation.areaForm (U -ᵥ V) (Q -ᵥ V) = 0 := by
    rw [← oangle_sign_eq_zero_iff_collinear] at hUV
    rw [sign_oangle_eq_sign_areaForm] at hUV
    exact sign_eq_zero_iff.mp hUV
  rcases hXY.wbtw_or_wbtw_or_wbtw with h | h | h
  · exfalso
    obtain ⟨t, ht, rfl⟩ := h
    rw [Set.mem_Icc] at ht
    rw [areaForm_vsub_lineMap, hfQ, mul_zero, add_zero] at hfY
    have : (1 - t) * positiveOrientation.areaForm (U -ᵥ V) (X -ᵥ V) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht.2) hfX.le
    linarith
  · rw [wbtw_comm] at h
    refine ⟨h, fun hne => ?_, fun hne => ?_⟩
    · rw [hne] at hfQ; linarith
    · rw [hne] at hfQ; linarith
  · exfalso
    obtain ⟨t, ht, rfl⟩ := h
    rw [Set.mem_Icc] at ht
    rw [areaForm_vsub_lineMap, hfQ, mul_zero, zero_add] at hfX
    have : 0 ≤ t * positiveOrientation.areaForm (U -ᵥ V) (Y -ᵥ V) := mul_nonneg ht.1 hfY.le
    linarith

/-- Betweenness exclusivity. -/
theorem false_of_wbtw_wbtw {B Q A : Pt} (h₁ : Wbtw ℝ B Q A) (h₂ : Wbtw ℝ B A Q)
    (h : A ≠ Q) : False := by
  obtain ⟨s, hs, hQs⟩ := h₁
  obtain ⟨t, ht, hAt⟩ := h₂
  rw [Set.mem_Icc] at hs ht
  have e1 : Q -ᵥ B = s • (A -ᵥ B) := by
    rw [← hQs, AffineMap.lineMap_apply, vadd_vsub_assoc, vsub_self, add_zero]
  have e2 : A -ᵥ B = t • (Q -ᵥ B) := by
    rw [← hAt, AffineMap.lineMap_apply, vadd_vsub_assoc, vsub_self, add_zero]
  by_cases hQB : Q = B
  · subst hQB
    rw [AffineMap.lineMap_same] at hAt
    exact h hAt.symm
  · have hv : Q -ᵥ B ≠ 0 := vsub_ne_zero.mpr hQB
    have e3 : s • (A -ᵥ B) = (s * t) • (Q -ᵥ B) := by rw [e2, smul_smul]
    have e4 : Q -ᵥ B = (s * t) • (Q -ᵥ B) := e1.trans e3
    have e5 : (s * t - 1) • (Q -ᵥ B) = 0 := by
      rw [sub_smul, one_smul, ← e4, sub_self]
    rcases smul_eq_zero.mp e5 with hst | hst
    · have hst1 : s * t = 1 := by linarith
      have hle := mul_le_mul_of_nonneg_left ht.2 hs.1
      rw [hst1, mul_one] at hle
      have hs1 : s = 1 := le_antisymm hs.2 hle
      rw [hs1, AffineMap.lineMap_apply_one] at hQs
      exact h hQs
    · exact hv hst

/-- Two points on a line through `V` are on the same ray from `V` or on opposite rays. -/
theorem sameRay_or_sameRay_neg_vsub_of_collinear {U V Q : Pt} (hU : U ≠ V) (hQ : Q ≠ V)
    (h : Collinear ℝ ({U, V, Q} : Set Pt)) :
    SameRay ℝ (U -ᵥ V) (Q -ᵥ V) ∨ SameRay ℝ (U -ᵥ V) (V -ᵥ Q) := by
  rw [← oangle_eq_zero_or_eq_pi_iff_collinear] at h
  rcases h with h | h
  · exact Or.inl (positiveOrientation.oangle_eq_zero_iff_sameRay.mp h)
  · refine Or.inr ?_
    rw [← neg_vsub_eq_vsub_rev Q V]
    exact (positiveOrientation.oangle_eq_pi_iff_sameRay_neg.mp h).2.2

/-- If a 1-dimensional submodule is contained in a non-top supermodule, the supermodule
is forced to be equal (there is no room for intermediate dimensions in the plane). -/
private lemma eq_max_of_max_ne_top {A B : Submodule ℝ Pt}
    (hA : Module.finrank ℝ A = 1) (h : A ⊔ B ≠ ⊤) : A = A ⊔ B := by
  apply Submodule.eq_of_le_of_finrank_eq le_sup_left
  rw [hA]
  have hAB := Submodule.finrank_le (A ⊔ B)
  rw [planeFiniteDim.out] at hAB
  have hAB' : 1 ≤ Module.finrank ℝ ↥(A ⊔ B) := by
    simp_rw [← hA]
    exact Submodule.finrank_mono le_sup_left
  have hAB'' : Module.finrank ℝ ↥(A ⊔ B) ≠ 2 := by
    contrapose! h
    apply Submodule.eq_top_of_finrank_eq
    rw [planeFiniteDim.out, h]
  interval_cases Module.finrank ℝ ↥(A ⊔ B) <;> lia

/-- The direction of the affine span of two distinct points of the plane is
1-dimensional. -/
private lemma affineSpan_pair_finrank {A B : Pt} (hAB : A ≠ B) :
    Module.finrank ℝ (affineSpan ℝ {A, B}).direction = 1 := by
  rw [direction_affineSpan]
  have h := affineIndependent_of_ne ℝ hAB
  have h' : Set.range ![A, B] = {A, B} := by
    simp
    rw [Set.pair_comm]
  rw [← h']
  apply AffineIndependent.finrank_vectorSpan h
  simp

/-- Two non-parallel lines in the plane meet, and the intersection is collinear with
both pairs. -/
theorem exists_collinear_inter_of_not_parallel {U V X Y : Pt}
    (hU : U ≠ V) (hX : X ≠ Y) (h : ¬ line[ℝ, U, V] ∥ line[ℝ, X, Y]) :
    ∃ Q : Pt, Collinear ℝ ({U, V, Q} : Set Pt) ∧ Collinear ℝ ({X, Y, Q} : Set Pt) := by
  have hU' : (line[ℝ, U, V] : Set Pt).Nonempty := by
    use U
    apply mem_affineSpan
    simp
  have hX' : (line[ℝ, X, Y] : Set Pt).Nonempty := by
    use X
    apply mem_affineSpan
    simp
  have key : (line[ℝ, U, V] : AffineSubspace ℝ Pt).direction ⊔
      (line[ℝ, X, Y] : AffineSubspace ℝ Pt).direction = ⊤ := by
    contrapose! h
    rw [AffineSubspace.parallel_iff_direction_eq_and_eq_bot_iff_eq_bot]
    constructor
    · set A := (affineSpan ℝ {U, V}).direction
      set B := (affineSpan ℝ {X, Y}).direction
      trans A ⊔ B
      · exact eq_max_of_max_ne_top (affineSpan_pair_finrank hU) h
      · symm
        rw [sup_comm] at *
        exact eq_max_of_max_ne_top (affineSpan_pair_finrank hX) h
    · rw [affineSpan_eq_bot, affineSpan_eq_bot]
      constructor <;> intro h' <;> contrapose! h' <;> simp
  obtain ⟨Q, hQUV, hQXY⟩ :=
    AffineSubspace.inter_nonempty_of_nonempty_of_sup_direction_eq_top hU' hX' key
  refine ⟨Q, ?_, ?_⟩
  · have hc := collinear_insert_of_mem_affineSpan_pair hQUV
    rwa [show ({Q, U, V} : Set Pt) = {U, V, Q} by
      ext w; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at hc
  · have hc := collinear_insert_of_mem_affineSpan_pair hQXY
    rwa [show ({Q, X, Y} : Set Pt) = {X, Y, Q} by
      ext w; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at hc

/-- A configuration satisfying the conditions of the problem. We define this structure to
avoid passing many hypotheses around as we build up information about the configuration; the
final result for a statement of the problem not using this structure is then deduced from one
in terms of this structure.

The convexity of the pentagon is expressed by saying that walking around the vertices
`A → B → C → D → E → A` always makes a strict left turn (positive `sign` of the oriented
angle), so the pentagon is strictly convex with the vertices in counterclockwise order.
That `T` lies inside the pentagon is expressed both literally (membership in the interior
of the convex hull) and through the implied facts (included as hypotheses, following the
usual conventions for formalizing olympiad geometry problems) that `T` lies strictly to
the left of every directed edge of the pentagon. -/
structure Imo2022q4Cfg where
  (A B C D E T P Q R S : Pt)
  -- The pentagon is strictly convex, with the vertices in clockwise order; this is
  -- expressed by saying that the three vertices not on an edge all lie strictly on the
  -- same (interior) side of every edge.
  hconv_AB : ∀ X ∈ ({C, D, E} : Set Pt), 0 < (∡ A B X).sign
  hconv_BC : ∀ X ∈ ({D, E, A} : Set Pt), 0 < (∡ B C X).sign
  hconv_CD : ∀ X ∈ ({E, A, B} : Set Pt), 0 < (∡ C D X).sign
  hconv_DE : ∀ X ∈ ({A, B, C} : Set Pt), 0 < (∡ D E X).sign
  hconv_EA : ∀ X ∈ ({B, C, D} : Set Pt), 0 < (∡ E A X).sign
  -- `T` lies inside the pentagon.
  T_mem_interior : T ∈ interior (convexHull ℝ {A, B, C, D, E})
  oangle_ABT_pos : 0 < (∡ A B T).sign
  oangle_BCT_pos : 0 < (∡ B C T).sign
  oangle_CDT_pos : 0 < (∡ C D T).sign
  oangle_DET_pos : 0 < (∡ D E T).sign
  oangle_EAT_pos : 0 < (∡ E A T).sign
  dist_TB_eq_TD : dist T B = dist T D
  dist_TC_eq_TE : dist T C = dist T E
  dist_BC_eq_DE : dist B C = dist D E
  angle_ABT_eq_TEA : ∠ A B T = ∠ T E A
  -- Hypotheses implicit in the named angles and lines.
  A_ne_B : A ≠ B
  T_ne_B : T ≠ B
  T_ne_E : T ≠ E
  A_ne_E : A ≠ E
  C_ne_D : C ≠ D
  C_ne_T : C ≠ T
  D_ne_T : D ≠ T
  -- `P` is the intersection of line `AB` with line `CD`.
  collinear_ABP : Collinear ℝ ({A, B, P} : Set Pt)
  collinear_CDP : Collinear ℝ ({C, D, P} : Set Pt)
  -- `Q` is the intersection of line `AB` with line `CT`.
  collinear_ABQ : Collinear ℝ ({A, B, Q} : Set Pt)
  collinear_CTQ : Collinear ℝ ({C, T, Q} : Set Pt)
  -- `R` is the intersection of line `AE` with line `CD`.
  collinear_AER : Collinear ℝ ({A, E, R} : Set Pt)
  collinear_CDR : Collinear ℝ ({C, D, R} : Set Pt)
  -- `S` is the intersection of line `AE` with line `DT`.
  collinear_AES : Collinear ℝ ({A, E, S} : Set Pt)
  collinear_DTS : Collinear ℝ ({D, T, S} : Set Pt)
  -- The points `P, B, A, Q` occur on their line in that order.
  sbtw_PBA : Sbtw ℝ P B A
  sbtw_BAQ : Sbtw ℝ B A Q
  -- The points `R, E, A, S` occur on their line in that order.
  sbtw_REA : Sbtw ℝ R E A
  sbtw_EAS : Sbtw ℝ E A S

/-- If `0 < (∡ x y z).sign`, then `z ≠ y`. -/
theorem right_ne_left_of_oangle_sign_pos {x y z : Pt} (h : 0 < (∡ x y z).sign) :
    z ≠ y := by
  rintro rfl
  rw [oangle_self_right, Real.Angle.sign_zero] at h
  exact lt_irrefl _ h

/-- If `0 < (∡ x y z).sign`, then `x ≠ y`. -/
theorem left_ne_right_of_oangle_sign_pos {x y z : Pt} (h : 0 < (∡ x y z).sign) :
    x ≠ y := by
  rintro rfl
  rw [oangle_self_left, Real.Angle.sign_zero] at h
  exact lt_irrefl _ h

/-- If `0 < (∡ x y z).sign`, then `x ≠ z`. -/
theorem first_ne_third_of_oangle_sign_pos {x y z : Pt} (h : 0 < (∡ x y z).sign) :
    x ≠ z := by
  rintro rfl
  rw [oangle_self_left_right, Real.Angle.sign_zero] at h
  exact lt_irrefl _ h

/-- If `0 < (∡ x y z).sign`, then the three points are not collinear. -/
theorem not_collinear_of_oangle_sign_pos {x y z : Pt} (h : 0 < (∡ x y z).sign) :
    ¬Collinear ℝ ({x, y, z} : Set Pt) := by
  rw [← oangle_sign_eq_zero_iff_collinear]
  exact ne_of_gt h

/-- SSS congruence, unoriented-angle form: if two triangles have pairwise equal side
lengths, then corresponding angles are equal. -/
theorem angle_eq_angle_of_sss {p₁ p₂ p₃ q₁ q₂ q₃ : Pt}
    (h₁ : dist p₁ p₂ = dist q₁ q₂) (h₂ : dist p₂ p₃ = dist q₂ q₃)
    (h₃ : dist p₃ p₁ = dist q₃ q₁) (hp₁ : p₁ ≠ p₂) (hp₃ : p₃ ≠ p₂) :
    ∠ p₁ p₂ p₃ = ∠ q₁ q₂ q₃ := by
  have hd1 : dist p₁ p₂ ≠ 0 := dist_ne_zero.mpr hp₁
  have hd3 : dist p₃ p₂ ≠ 0 := dist_ne_zero.mpr hp₃
  apply Real.injOn_cos (Set.mem_Icc.mpr ⟨angle_nonneg _ _ _, angle_le_pi _ _ _⟩)
    (Set.mem_Icc.mpr ⟨angle_nonneg _ _ _, angle_le_pi _ _ _⟩)
  have lc₁ := dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle p₁ p₂ p₃
  have lc₂ := dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle q₁ q₂ q₃
  have e₁ : dist q₁ q₂ = dist p₁ p₂ := h₁.symm
  have e₂ : dist q₃ q₂ = dist p₃ p₂ := by rw [dist_comm q₃ q₂, dist_comm p₃ p₂]; exact h₂.symm
  have e₃ : dist q₁ q₃ = dist p₁ p₃ := by rw [dist_comm q₁ q₃, dist_comm p₁ p₃]; exact h₃.symm
  rw [e₁, e₂, e₃] at lc₂
  have key : 2 * dist p₁ p₂ * dist p₃ p₂ * Real.cos (∠ p₁ p₂ p₃) =
      2 * dist p₁ p₂ * dist p₃ p₂ * Real.cos (∠ q₁ q₂ q₃) := by linarith [lc₁, lc₂]
  have hne : (2 : ℝ) * dist p₁ p₂ * dist p₃ p₂ ≠ 0 := by positivity
  exact mul_left_cancel₀ hne key

/-- SSS similarity with a ratio: if the sides of one triangle are a fixed multiple of the
sides of another, corresponding angles are equal. -/
theorem angle_eq_angle_of_sss_smul {p₁ p₂ p₃ q₁ q₂ q₃ : Pt} {lam : ℝ}
    (h₁ : dist p₁ p₂ = lam * dist q₁ q₂) (h₂ : dist p₂ p₃ = lam * dist q₂ q₃)
    (h₃ : dist p₃ p₁ = lam * dist q₃ q₁) (hp₁ : p₁ ≠ p₂) (hp₃ : p₃ ≠ p₂) :
    ∠ p₁ p₂ p₃ = ∠ q₁ q₂ q₃ := by
  have hd1 : dist p₁ p₂ ≠ 0 := dist_ne_zero.mpr hp₁
  have hd3 : dist p₃ p₂ ≠ 0 := dist_ne_zero.mpr hp₃
  have hlam : lam ≠ 0 := by
    intro h
    rw [h, zero_mul] at h₁
    exact hd1 h₁
  have hq1 : dist q₁ q₂ ≠ 0 := by
    intro h
    apply hd1
    rw [h₁, h, mul_zero]
  have hq3 : dist q₂ q₃ ≠ 0 := by
    intro h
    apply hd3
    rw [dist_comm p₃ p₂, h₂, h, mul_zero]
  apply Real.injOn_cos (Set.mem_Icc.mpr ⟨angle_nonneg _ _ _, angle_le_pi _ _ _⟩)
    (Set.mem_Icc.mpr ⟨angle_nonneg _ _ _, angle_le_pi _ _ _⟩)
  have lc₁ := dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle p₁ p₂ p₃
  have lc₂ := dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle q₁ q₂ q₃
  rw [dist_comm q₃ q₂, dist_comm q₁ q₃] at lc₂
  rw [h₁, dist_comm p₃ p₂, h₂, dist_comm p₁ p₃, h₃] at lc₁
  have key : 2 * lam ^ 2 * dist q₁ q₂ * dist q₂ q₃ * Real.cos (∠ p₁ p₂ p₃) =
      2 * lam ^ 2 * dist q₁ q₂ * dist q₂ q₃ * Real.cos (∠ q₁ q₂ q₃) := by
    linear_combination lc₁ - lam ^ 2 * lc₂
  have hne : (2 : ℝ) * lam ^ 2 * dist q₁ q₂ * dist q₂ q₃ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero 2 hlam)) hq1) hq3
  exact mul_left_cancel₀ hne key

/-- Twice an oriented angle is unchanged when both legs are rescaled by nonzero scalars. -/
theorem two_zsmul_oangle_smul {x y : Pt} {a b : ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    (2 : ℤ) • positiveOrientation.oangle (a • x) (b • y) =
      (2 : ℤ) • positiveOrientation.oangle x y := by
  have hnl : ∀ u v : Pt, u ≠ 0 → v ≠ 0 →
      (2 : ℤ) • positiveOrientation.oangle (-u) v =
        (2 : ℤ) • positiveOrientation.oangle u v := by
    intro u v hu hv
    rw [positiveOrientation.oangle_neg_left hu hv, smul_add, Real.Angle.two_zsmul_coe_pi,
      add_zero]
  have hnr : ∀ u v : Pt, u ≠ 0 → v ≠ 0 →
      (2 : ℤ) • positiveOrientation.oangle u (-v) =
        (2 : ℤ) • positiveOrientation.oangle u v := by
    intro u v hu hv
    rw [positiveOrientation.oangle_neg_right hu hv, smul_add, Real.Angle.two_zsmul_coe_pi,
      add_zero]
  rcases lt_or_gt_of_ne ha with ha | ha
  · rw [positiveOrientation.oangle_smul_left_of_neg _ _ ha,
      hnl _ _ hx (smul_ne_zero hb hy)]
    rcases lt_or_gt_of_ne hb with hb | hb
    · rw [positiveOrientation.oangle_smul_right_of_neg _ _ hb, hnr _ _ hx hy]
    · rw [positiveOrientation.oangle_smul_right_of_pos _ _ hb]
  · rw [positiveOrientation.oangle_smul_left_of_pos _ _ ha]
    rcases lt_or_gt_of_ne hb with hb | hb
    · rw [positiveOrientation.oangle_smul_right_of_neg _ _ hb, hnr _ _ hx hy]
    · rw [positiveOrientation.oangle_smul_right_of_pos _ _ hb]

/-- `SignType`: strictly positive implies equal to one. -/
theorem SignType.eq_one_of_zero_lt {s : SignType} (h : 0 < s) : s = 1 := by
  fin_cases s <;> simp at h ⊢

/-- `SignType`: strictly negative implies equal to minus one. -/
theorem SignType.eq_neg_one_of_lt_zero {s : SignType} (h : s < 0) : s = -1 := by
  fin_cases s <;> simp at h ⊢

theorem sign_eq_one_of_oangle_pos {x y z : Pt} (h : 0 < (∡ x y z).sign) :
    (∡ x y z).sign = 1 :=
  SignType.eq_one_of_zero_lt h

/-- Permutation of a collinear triple. -/
theorem collinear_swap {a b c : Pt} (h : Collinear ℝ ({a, b, c} : Set Pt)) :
    Collinear ℝ ({a, c, b} : Set Pt) := by
  rwa [Set.pair_comm b c] at h

/-- Permutation of a collinear triple. -/
theorem collinear_rotate {a b c : Pt} (h : Collinear ℝ ({a, b, c} : Set Pt)) :
    Collinear ℝ ({b, c, a} : Set Pt) := by
  rwa [Set.insert_comm a b, Set.pair_comm a c] at h

/-- Permutation of a collinear triple. -/
theorem collinear_rev {a b c : Pt} (h : Collinear ℝ ({a, b, c} : Set Pt)) :
    Collinear ℝ ({c, b, a} : Set Pt) := by
  rwa [Set.insert_comm a b, Set.pair_comm a c, Set.insert_comm b c] at h

/-- Sines of unoriented angles are equal when twice the oriented angles are equal. -/
theorem sin_angle_eq_sin_angle_of_two_zsmul_oangle_eq {p₁ p₂ p₃ q₁ q₂ q₃ : Pt}
    (hp₁ : p₁ ≠ p₂) (hp₃ : p₃ ≠ p₂) (hq₁ : q₁ ≠ q₂) (hq₃ : q₃ ≠ q₂)
    (h : (2 : ℤ) • ∡ p₁ p₂ p₃ = (2 : ℤ) • ∡ q₁ q₂ q₃) :
    Real.sin (∠ p₁ p₂ p₃) = Real.sin (∠ q₁ q₂ q₃) := by
  rw [angle_eq_abs_oangle_toReal hp₁ hp₃, angle_eq_abs_oangle_toReal hq₁ hq₃,
    ← Real.abs_sin_eq_sin_abs_of_abs_le_pi (Real.Angle.abs_toReal_le_pi _),
    ← Real.abs_sin_eq_sin_abs_of_abs_le_pi (Real.Angle.abs_toReal_le_pi _),
    Real.Angle.sin_toReal, Real.Angle.sin_toReal]
  have h' : (2 : ℤ) • (∡ p₁ p₂ p₃ - ∡ q₁ q₂ q₃) = 0 := by rw [smul_sub, h, sub_self]
  rw [Real.Angle.two_zsmul_eq_zero_iff] at h'
  rcases h' with h' | h'
  · rw [sub_eq_zero] at h'
    rw [h']
  · rw [sub_eq_iff_eq_add] at h'
    rw [h', add_comm, Real.Angle.sin_add_pi, abs_neg]

/-- Sines of unoriented angles are equal when twice the oriented angles are anti-equal. -/
theorem sin_angle_eq_sin_angle_of_two_zsmul_oangle_eq_neg {p₁ p₂ p₃ q₁ q₂ q₃ : Pt}
    (hp₁ : p₁ ≠ p₂) (hp₃ : p₃ ≠ p₂) (hq₁ : q₁ ≠ q₂) (hq₃ : q₃ ≠ q₂)
    (h : (2 : ℤ) • ∡ p₁ p₂ p₃ = -((2 : ℤ) • ∡ q₁ q₂ q₃)) :
    Real.sin (∠ p₁ p₂ p₃) = Real.sin (∠ q₁ q₂ q₃) := by
  rw [angle_eq_abs_oangle_toReal hp₁ hp₃, angle_eq_abs_oangle_toReal hq₁ hq₃,
    ← Real.abs_sin_eq_sin_abs_of_abs_le_pi (Real.Angle.abs_toReal_le_pi _),
    ← Real.abs_sin_eq_sin_abs_of_abs_le_pi (Real.Angle.abs_toReal_le_pi _),
    Real.Angle.sin_toReal, Real.Angle.sin_toReal]
  have h' : (2 : ℤ) • (∡ p₁ p₂ p₃ + ∡ q₁ q₂ q₃) = 0 := by rw [smul_add, h, neg_add_cancel]
  rw [Real.Angle.two_zsmul_eq_zero_iff] at h'
  rcases h' with h' | h'
  · rw [add_eq_zero_iff_eq_neg] at h'
    rw [h', Real.Angle.sin_neg, abs_neg]
  · have h'' : Real.Angle.sin (↑Real.pi - ∡ q₁ q₂ q₃) = Real.Angle.sin (∡ q₁ q₂ q₃) := by
      rw [sub_eq_add_neg, add_comm, Real.Angle.sin_add_pi, Real.Angle.sin_neg, neg_neg]
    rw [eq_sub_iff_add_eq.mpr h', h'']

namespace Imo2022q4Cfg

variable (cfg : Imo2022q4Cfg)

/-! ### Nondegeneracy facts extracted from the convexity and interior hypotheses -/

/-- The turn-angle signs, as special cases of the half-plane hypotheses. -/
theorem oangle_ABC_pos : 0 < (∡ cfg.A cfg.B cfg.C).sign := cfg.hconv_AB _ (by simp)

theorem oangle_BCD_pos : 0 < (∡ cfg.B cfg.C cfg.D).sign := cfg.hconv_BC _ (by simp)

theorem oangle_CDE_pos : 0 < (∡ cfg.C cfg.D cfg.E).sign := cfg.hconv_CD _ (by simp)

theorem oangle_DEA_pos : 0 < (∡ cfg.D cfg.E cfg.A).sign := cfg.hconv_DE _ (by simp)

theorem oangle_EAB_pos : 0 < (∡ cfg.E cfg.A cfg.B).sign := cfg.hconv_EA _ (by simp)

/-- `B ≠ C` (from strict convexity at `B`). -/
theorem B_ne_C : cfg.B ≠ cfg.C :=
  (right_ne_left_of_oangle_sign_pos cfg.oangle_ABC_pos).symm

/-- `D ≠ E` (from strict convexity at `D`). -/
theorem D_ne_E : cfg.D ≠ cfg.E :=
  (right_ne_left_of_oangle_sign_pos cfg.oangle_CDE_pos).symm

/-- `A ≠ C` (from strict convexity at `B`). -/
theorem A_ne_C : cfg.A ≠ cfg.C := first_ne_third_of_oangle_sign_pos cfg.oangle_ABC_pos

/-- `B ≠ D` (from strict convexity at `C`). -/
theorem B_ne_D : cfg.B ≠ cfg.D := first_ne_third_of_oangle_sign_pos cfg.oangle_BCD_pos

/-- `C ≠ E` (from strict convexity at `D`). -/
theorem C_ne_E : cfg.C ≠ cfg.E := first_ne_third_of_oangle_sign_pos cfg.oangle_CDE_pos

/-- `D ≠ A` (from strict convexity at `E`). -/
theorem D_ne_A : cfg.D ≠ cfg.A := first_ne_third_of_oangle_sign_pos cfg.oangle_DEA_pos

/-- `E ≠ B` (from strict convexity at `A`). -/
theorem E_ne_B : cfg.E ≠ cfg.B := first_ne_third_of_oangle_sign_pos cfg.oangle_EAB_pos

/-- `T ≠ A` (since `T` is strictly to the left of edge `EA`). -/
theorem T_ne_A : cfg.T ≠ cfg.A :=
  right_ne_left_of_oangle_sign_pos cfg.oangle_EAT_pos

/-- Consecutive vertices of the pentagon are not collinear. -/
theorem not_collinear_ABC : ¬Collinear ℝ ({cfg.A, cfg.B, cfg.C} : Set Pt) :=
  not_collinear_of_oangle_sign_pos cfg.oangle_ABC_pos

theorem not_collinear_BCD : ¬Collinear ℝ ({cfg.B, cfg.C, cfg.D} : Set Pt) :=
  not_collinear_of_oangle_sign_pos cfg.oangle_BCD_pos

theorem not_collinear_CDE : ¬Collinear ℝ ({cfg.C, cfg.D, cfg.E} : Set Pt) :=
  not_collinear_of_oangle_sign_pos cfg.oangle_CDE_pos

theorem not_collinear_DEA : ¬Collinear ℝ ({cfg.D, cfg.E, cfg.A} : Set Pt) :=
  not_collinear_of_oangle_sign_pos cfg.oangle_DEA_pos

theorem not_collinear_EAB : ¬Collinear ℝ ({cfg.E, cfg.A, cfg.B} : Set Pt) :=
  not_collinear_of_oangle_sign_pos cfg.oangle_EAB_pos

/-- `T` is not collinear with any edge of the pentagon. -/
theorem not_collinear_ABT : ¬Collinear ℝ ({cfg.A, cfg.B, cfg.T} : Set Pt) :=
  not_collinear_of_oangle_sign_pos cfg.oangle_ABT_pos

theorem not_collinear_BCT : ¬Collinear ℝ ({cfg.B, cfg.C, cfg.T} : Set Pt) :=
  not_collinear_of_oangle_sign_pos cfg.oangle_BCT_pos

theorem not_collinear_CDT : ¬Collinear ℝ ({cfg.C, cfg.D, cfg.T} : Set Pt) :=
  not_collinear_of_oangle_sign_pos cfg.oangle_CDT_pos

theorem not_collinear_DET : ¬Collinear ℝ ({cfg.D, cfg.E, cfg.T} : Set Pt) :=
  not_collinear_of_oangle_sign_pos cfg.oangle_DET_pos

theorem not_collinear_EAT : ¬Collinear ℝ ({cfg.E, cfg.A, cfg.T} : Set Pt) :=
  not_collinear_of_oangle_sign_pos cfg.oangle_EAT_pos

/-! ### SSS congruence of `△BTC` and `△DTE` -/

/-- The triangles `BTC` and `DTE` are congruent (SSS); angle at `T`. -/
theorem angle_BTC_eq_DTE : ∠ cfg.B cfg.T cfg.C = ∠ cfg.D cfg.T cfg.E := by
  apply angle_eq_angle_of_sss _ _ _ cfg.T_ne_B.symm cfg.C_ne_T
  · rw [dist_comm cfg.B cfg.T, dist_comm cfg.D cfg.T]; exact cfg.dist_TB_eq_TD
  · exact cfg.dist_TC_eq_TE
  · rw [dist_comm cfg.C cfg.B, dist_comm cfg.E cfg.D]; exact cfg.dist_BC_eq_DE

/-- The triangles `BTC` and `DTE` are congruent (SSS); angle at `B` and `D`. -/
theorem angle_TBC_eq_TDE : ∠ cfg.T cfg.B cfg.C = ∠ cfg.T cfg.D cfg.E := by
  apply angle_eq_angle_of_sss _ _ _ cfg.T_ne_B cfg.B_ne_C.symm
  · exact cfg.dist_TB_eq_TD
  · exact cfg.dist_BC_eq_DE
  · rw [dist_comm cfg.C cfg.T, dist_comm cfg.E cfg.T]; exact cfg.dist_TC_eq_TE

/-- The triangles `BTC` and `DTE` are congruent (SSS); angle at `C` and `E`. -/
theorem angle_BCT_eq_DET : ∠ cfg.B cfg.C cfg.T = ∠ cfg.D cfg.E cfg.T := by
  apply angle_eq_angle_of_sss _ _ _ cfg.B_ne_C cfg.C_ne_T.symm
  · exact cfg.dist_BC_eq_DE
  · rw [dist_comm cfg.C cfg.T, dist_comm cfg.E cfg.T]; exact cfg.dist_TC_eq_TE
  · exact cfg.dist_TB_eq_TD

/-! ### Signs of key oriented angles, and oriented versions of the congruences -/

theorem sign_BTC : (∡ cfg.B cfg.T cfg.C).sign = -1 := by
  have h : (∡ cfg.B cfg.C cfg.T).sign = 1 := sign_eq_one_of_oangle_pos cfg.oangle_BCT_pos
  have hr : (∡ cfg.C cfg.T cfg.B).sign = (∡ cfg.B cfg.C cfg.T).sign := oangle_rotate_sign _ _ _
  have hs : (∡ cfg.B cfg.T cfg.C).sign = -(∡ cfg.C cfg.T cfg.B).sign :=
    (oangle_swap₁₃_sign _ _ _).symm
  rw [hs, hr, h]

theorem sign_DTE : (∡ cfg.D cfg.T cfg.E).sign = -1 := by
  have h : (∡ cfg.D cfg.E cfg.T).sign = 1 := sign_eq_one_of_oangle_pos cfg.oangle_DET_pos
  have hr : (∡ cfg.E cfg.T cfg.D).sign = (∡ cfg.D cfg.E cfg.T).sign := oangle_rotate_sign _ _ _
  have hs : (∡ cfg.D cfg.T cfg.E).sign = -(∡ cfg.E cfg.T cfg.D).sign :=
    (oangle_swap₁₃_sign _ _ _).symm
  rw [hs, hr, h]

theorem sign_ABT : (∡ cfg.A cfg.B cfg.T).sign = 1 :=
  sign_eq_one_of_oangle_pos cfg.oangle_ABT_pos

theorem sign_TEA : (∡ cfg.T cfg.E cfg.A).sign = 1 := by
  have h : (∡ cfg.E cfg.A cfg.T).sign = 1 := sign_eq_one_of_oangle_pos cfg.oangle_EAT_pos
  have hr : (∡ cfg.E cfg.A cfg.T).sign = (∡ cfg.T cfg.E cfg.A).sign := oangle_rotate_sign _ _ _
  rw [← hr, h]

/-- The SSS congruence, oriented form. -/
theorem oangle_BTC_eq_DTE : ∡ cfg.B cfg.T cfg.C = ∡ cfg.D cfg.T cfg.E :=
  oangle_eq_of_angle_eq_of_sign_eq cfg.angle_BTC_eq_DTE (by rw [cfg.sign_BTC, cfg.sign_DTE])

/-- The given angle condition, oriented form. -/
theorem oangle_ABT_eq_TEA : ∡ cfg.A cfg.B cfg.T = ∡ cfg.T cfg.E cfg.A :=
  oangle_eq_of_angle_eq_of_sign_eq cfg.angle_ABT_eq_TEA (by rw [cfg.sign_ABT, cfg.sign_TEA])

/-- `∡ B T D = ∡ C T E` (the two rotation angles at `T` coincide). -/
theorem oangle_BTD_eq_CTE : ∡ cfg.B cfg.T cfg.D = ∡ cfg.C cfg.T cfg.E := by
  have hB : cfg.B ≠ cfg.T := cfg.T_ne_B.symm
  have hC : cfg.C ≠ cfg.T := cfg.C_ne_T
  have hD : cfg.D ≠ cfg.T := cfg.D_ne_T
  have hE : cfg.E ≠ cfg.T := cfg.T_ne_E.symm
  rw [← oangle_add hB hC hD, ← oangle_add hC hD hE, cfg.oangle_BTC_eq_DTE, add_comm]

/-! ### Distinctness from the order hypotheses -/

theorem B_ne_Q : cfg.B ≠ cfg.Q := cfg.sbtw_BAQ.left_ne_right
theorem A_ne_Q : cfg.A ≠ cfg.Q := cfg.sbtw_BAQ.ne_right
theorem A_ne_S : cfg.A ≠ cfg.S := cfg.sbtw_EAS.ne_right
theorem E_ne_S : cfg.E ≠ cfg.S := cfg.sbtw_EAS.left_ne_right
theorem P_ne_B : cfg.P ≠ cfg.B := cfg.sbtw_PBA.left_ne
theorem P_ne_A : cfg.P ≠ cfg.A := cfg.sbtw_PBA.left_ne_right
theorem R_ne_E : cfg.R ≠ cfg.E := cfg.sbtw_REA.left_ne
theorem R_ne_A : cfg.R ≠ cfg.A := cfg.sbtw_REA.left_ne_right

theorem Q_ne_T : cfg.Q ≠ cfg.T := by
  intro h
  apply cfg.not_collinear_ABT
  rw [← h]
  exact cfg.collinear_ABQ

theorem Q_ne_C : cfg.Q ≠ cfg.C := by
  intro h
  apply cfg.not_collinear_ABC
  rw [← h]
  exact cfg.collinear_ABQ

theorem S_ne_T : cfg.S ≠ cfg.T := by
  intro h
  apply cfg.not_collinear_EAT
  rw [← h]
  exact collinear_swap (collinear_rotate cfg.collinear_AES)

theorem P_ne_C : cfg.P ≠ cfg.C := by
  intro h
  apply cfg.not_collinear_ABC
  rw [← h]
  exact cfg.collinear_ABP

theorem not_collinear_ABD : ¬Collinear ℝ ({cfg.A, cfg.B, cfg.D} : Set Pt) :=
  not_collinear_of_oangle_sign_pos (cfg.hconv_AB _ (by simp))

theorem P_ne_D : cfg.P ≠ cfg.D := by
  intro h
  apply cfg.not_collinear_ABD
  rw [← h]
  exact cfg.collinear_ABP

theorem not_collinear_AED : ¬Collinear ℝ ({cfg.A, cfg.E, cfg.D} : Set Pt) :=
  fun h => cfg.not_collinear_DEA (collinear_rotate (collinear_swap h))

theorem R_ne_C : cfg.R ≠ cfg.C := by
  intro h
  apply not_collinear_of_oangle_sign_pos (cfg.hconv_EA _ (by simp) :
    0 < (∡ cfg.E cfg.A cfg.C).sign)
  rw [← h]
  exact collinear_swap (collinear_rotate cfg.collinear_AER)

theorem R_ne_D : cfg.R ≠ cfg.D := by
  intro h
  apply cfg.not_collinear_AED
  rw [← h]
  exact cfg.collinear_AER

/-! ### Non-collinearity of the similarity triangles -/

theorem not_collinear_BQT : ¬Collinear ℝ ({cfg.B, cfg.Q, cfg.T} : Set Pt) := by
  intro h
  apply cfg.not_collinear_ABT
  have hiff : Collinear ℝ (insert cfg.A {cfg.B, cfg.Q, cfg.T}) ↔
      Collinear ℝ ({cfg.A, cfg.B, cfg.Q} : Set Pt) :=
    h.collinear_insert_iff_of_ne (by simp : cfg.B ∈ ({cfg.B, cfg.Q, cfg.T} : Set Pt))
      (by simp : cfg.Q ∈ ({cfg.B, cfg.Q, cfg.T} : Set Pt)) cfg.B_ne_Q
  have h4 : Collinear ℝ (insert cfg.A {cfg.B, cfg.Q, cfg.T}) := hiff.2 cfg.collinear_ABQ
  apply h4.subset
  intro x hx
  simp at hx
  rcases hx with rfl | rfl | rfl
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
      (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

theorem not_collinear_EST : ¬Collinear ℝ ({cfg.E, cfg.S, cfg.T} : Set Pt) := by
  intro h
  apply cfg.not_collinear_EAT
  have hiff : Collinear ℝ (insert cfg.A {cfg.E, cfg.S, cfg.T}) ↔
      Collinear ℝ ({cfg.A, cfg.E, cfg.S} : Set Pt) :=
    h.collinear_insert_iff_of_ne (by simp : cfg.E ∈ ({cfg.E, cfg.S, cfg.T} : Set Pt))
      (by simp : cfg.S ∈ ({cfg.E, cfg.S, cfg.T} : Set Pt)) cfg.E_ne_S
  have h4 : Collinear ℝ (insert cfg.A {cfg.E, cfg.S, cfg.T}) := hiff.2 cfg.collinear_AES
  apply h4.subset
  intro x hx
  simp at hx
  rcases hx with rfl | rfl | rfl <;> simp

/-! ### Sign anchors at the intersection points -/

theorem sign_BCQ : (∡ cfg.B cfg.C cfg.Q).sign = 1 := by
  have h₁ : SameRay ℝ (cfg.A -ᵥ cfg.B) (cfg.Q -ᵥ cfg.B) := cfg.sbtw_BAQ.wbtw.sameRay_vsub_left
  have hcol : Collinear ℝ ({cfg.B, cfg.A, cfg.B, cfg.Q} : Set Pt) := by
    rw [Set.insert_eq_of_mem (by simp : cfg.B ∈ insert cfg.A (insert cfg.B {cfg.Q}))]
    exact cfg.collinear_ABQ
  have h := Collinear.oangle_sign_of_sameRay_vsub cfg.C cfg.A_ne_B.symm cfg.B_ne_Q hcol h₁
  rw [← h]
  exact sign_eq_one_of_oangle_pos (cfg.hconv_BC cfg.A (by simp : cfg.A ∈ ({cfg.D, cfg.E, cfg.A} : Set Pt)))

theorem sign_DES : (∡ cfg.D cfg.E cfg.S).sign = 1 := by
  have h₂ : SameRay ℝ (cfg.A -ᵥ cfg.E) (cfg.S -ᵥ cfg.E) := cfg.sbtw_EAS.wbtw.sameRay_vsub_left
  obtain ⟨r₂, hr₂, hvr₂⟩ := h₂.exists_pos_left (vsub_ne_zero.mpr cfg.A_ne_E)
    (vsub_ne_zero.mpr cfg.E_ne_S.symm)
  have h : ∡ cfg.D cfg.E cfg.S = ∡ cfg.D cfg.E cfg.A := by
    show positiveOrientation.oangle (cfg.D -ᵥ cfg.E) (cfg.S -ᵥ cfg.E) =
      positiveOrientation.oangle (cfg.D -ᵥ cfg.E) (cfg.A -ᵥ cfg.E)
    rw [← hvr₂, positiveOrientation.oangle_smul_right_of_pos _ _ hr₂]
  rw [h]
  exact sign_eq_one_of_oangle_pos cfg.oangle_DEA_pos

theorem sign_CTB : (∡ cfg.C cfg.T cfg.B).sign = 1 := by
  have h : (∡ cfg.B cfg.C cfg.T).sign = 1 := sign_eq_one_of_oangle_pos cfg.oangle_BCT_pos
  have hr : (∡ cfg.C cfg.T cfg.B).sign = (∡ cfg.B cfg.C cfg.T).sign := oangle_rotate_sign _ _ _
  rw [hr, h]

theorem sign_CDT : (∡ cfg.C cfg.D cfg.T).sign = 1 :=
  sign_eq_one_of_oangle_pos cfg.oangle_CDT_pos

/-- `A` does not lie on line `CT`. -/
theorem sign_CTA_ne_zero : (∡ cfg.C cfg.T cfg.A).sign ≠ 0 := by
  intro h0
  have hcol : Collinear ℝ ({cfg.C, cfg.T, cfg.A} : Set Pt) :=
    oangle_sign_eq_zero_iff_collinear.mp h0
  by_cases hQA : cfg.Q = cfg.A
  · exact cfg.A_ne_Q hQA.symm
  · apply cfg.not_collinear_ABT
    have hiff1 : Collinear ℝ (insert cfg.Q {cfg.C, cfg.T, cfg.A}) ↔
        Collinear ℝ ({cfg.Q, cfg.C, cfg.T} : Set Pt) :=
      hcol.collinear_insert_iff_of_ne (by simp : cfg.C ∈ ({cfg.C, cfg.T, cfg.A} : Set Pt))
        (by simp : cfg.T ∈ ({cfg.C, cfg.T, cfg.A} : Set Pt)) cfg.C_ne_T
    have h4 : Collinear ℝ (insert cfg.Q {cfg.C, cfg.T, cfg.A}) :=
      hiff1.2 (collinear_rotate (collinear_rotate cfg.collinear_CTQ))
    have hiff2 : Collinear ℝ (insert cfg.B (insert cfg.Q {cfg.C, cfg.T, cfg.A})) ↔
        Collinear ℝ ({cfg.B, cfg.A, cfg.Q} : Set Pt) :=
      h4.collinear_insert_iff_of_ne
        (by simp : cfg.A ∈ insert cfg.Q {cfg.C, cfg.T, cfg.A})
        (by simp : cfg.Q ∈ insert cfg.Q {cfg.C, cfg.T, cfg.A}) cfg.A_ne_Q
    have h5 : Collinear ℝ (insert cfg.B (insert cfg.Q {cfg.C, cfg.T, cfg.A})) :=
      hiff2.2 (collinear_swap (collinear_rotate cfg.collinear_ABQ))
    apply h5.subset
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
        (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
        (Set.mem_insert _ _)))

/-- `A` does not lie on line `DT`. -/
theorem sign_DTA_ne_zero : (∡ cfg.D cfg.T cfg.A).sign ≠ 0 := by
  intro h0
  have hcol : Collinear ℝ ({cfg.D, cfg.T, cfg.A} : Set Pt) :=
    oangle_sign_eq_zero_iff_collinear.mp h0
  by_cases hSA : cfg.S = cfg.A
  · exact cfg.A_ne_S hSA.symm
  · apply cfg.not_collinear_EAT
    have hiff1 : Collinear ℝ (insert cfg.S {cfg.D, cfg.T, cfg.A}) ↔
        Collinear ℝ ({cfg.S, cfg.D, cfg.T} : Set Pt) :=
      hcol.collinear_insert_iff_of_ne (by simp : cfg.D ∈ ({cfg.D, cfg.T, cfg.A} : Set Pt))
        (by simp : cfg.T ∈ ({cfg.D, cfg.T, cfg.A} : Set Pt)) cfg.D_ne_T
    have h4 : Collinear ℝ (insert cfg.S {cfg.D, cfg.T, cfg.A}) :=
      hiff1.2 (collinear_rotate (collinear_rotate cfg.collinear_DTS))
    have hiff2 : Collinear ℝ (insert cfg.E (insert cfg.S {cfg.D, cfg.T, cfg.A})) ↔
        Collinear ℝ ({cfg.E, cfg.A, cfg.S} : Set Pt) :=
      h4.collinear_insert_iff_of_ne
        (by simp : cfg.A ∈ insert cfg.S {cfg.D, cfg.T, cfg.A})
        (by simp : cfg.S ∈ insert cfg.S {cfg.D, cfg.T, cfg.A}) cfg.A_ne_S
    have h5 : Collinear ℝ (insert cfg.E (insert cfg.S {cfg.D, cfg.T, cfg.A})) :=
      hiff2.2 (collinear_swap (collinear_rotate cfg.collinear_AES))
    apply h5.subset
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
        (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
    · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
        (Set.mem_insert _ _)))

/-- The side of line `CT` containing `B` also contains `A`. -/
theorem sign_CTA : (∡ cfg.C cfg.T cfg.A).sign = 1 := by
  have h0 := cfg.sign_CTA_ne_zero
  rcases lt_trichotomy (∡ cfg.C cfg.T cfg.A).sign 0 with hlt | heq | hgt
  · have hlt' := SignType.eq_neg_one_of_lt_zero hlt
    exact False.elim (by
      have hs := sbtw_of_sides_opposite (U := cfg.C) (V := cfg.T) (X := cfg.A) (Y := cfg.B)
        (Q := cfg.Q) hlt' cfg.sign_CTB cfg.collinear_CTQ cfg.collinear_ABQ
      exact false_of_wbtw_wbtw (wbtw_comm.mp hs.wbtw) cfg.sbtw_BAQ.wbtw cfg.A_ne_Q)
  · exact absurd heq h0
  · exact SignType.eq_one_of_zero_lt hgt

/-- The side of line `DT` containing `E` also contains `A`. -/
theorem sign_DTA : (∡ cfg.D cfg.T cfg.A).sign = -1 := by
  have h0 := cfg.sign_DTA_ne_zero
  rcases lt_trichotomy (∡ cfg.D cfg.T cfg.A).sign 0 with hlt | heq | hgt
  · exact SignType.eq_neg_one_of_lt_zero hlt
  · exact absurd heq h0
  · have hgt' := SignType.eq_one_of_zero_lt hgt
    exact False.elim (by
      have hs := sbtw_of_sides_opposite (U := cfg.D) (V := cfg.T) (X := cfg.E) (Y := cfg.A)
        (Q := cfg.S) cfg.sign_DTE hgt' cfg.collinear_DTS
        (collinear_swap (collinear_rotate cfg.collinear_AES))
      exact false_of_wbtw_wbtw hs.wbtw cfg.sbtw_EAS.wbtw cfg.A_ne_S)

/-- `Q` is on the ray from `T` opposite to `C` (POS1). -/
theorem sameRay_QT : SameRay ℝ (cfg.Q -ᵥ cfg.T) (cfg.T -ᵥ cfg.C) := by
  have hd := sameRay_or_sameRay_neg_vsub_of_collinear cfg.C_ne_T cfg.Q_ne_T cfg.collinear_CTQ
  rcases hd with h | h
  · -- `Q` on ray `TC`: exclude.
    exfalso
    obtain ⟨μ, hμ, hμv⟩ := h.exists_pos_left (vsub_ne_zero.mpr cfg.C_ne_T)
      (vsub_ne_zero.mpr cfg.Q_ne_T)
    -- `Q = lineMap T C μ` with `μ > 0`.
    have hQ : cfg.Q = AffineMap.lineMap cfg.T cfg.C μ := by
      rw [AffineMap.lineMap_apply, hμv]; exact (vsub_vadd cfg.Q cfg.T).symm
    by_cases hμ1 : μ < 1
    · -- `0 < μ < 1`: `Q` strictly between `T` and `C`, so on the interior side of `AB`.
      have hfT : 0 < positiveOrientation.areaForm (cfg.A -ᵥ cfg.B) (cfg.T -ᵥ cfg.B) :=
        sign_eq_one_iff.mp (by
          rw [← sign_oangle_eq_sign_areaForm]; exact cfg.sign_ABT)
      have hfC : 0 < positiveOrientation.areaForm (cfg.A -ᵥ cfg.B) (cfg.C -ᵥ cfg.B) :=
        sign_eq_one_iff.mp (by
          rw [← sign_oangle_eq_sign_areaForm]
          exact sign_eq_one_of_oangle_pos cfg.oangle_ABC_pos)
      have hfQ : positiveOrientation.areaForm (cfg.A -ᵥ cfg.B) (cfg.Q -ᵥ cfg.B) = 0 := by
        have h0 : (∡ cfg.A cfg.B cfg.Q).sign = 0 :=
          oangle_sign_eq_zero_iff_collinear.mpr cfg.collinear_ABQ
        rw [sign_oangle_eq_sign_areaForm] at h0
        exact sign_eq_zero_iff.mp h0
      rw [hQ, areaForm_vsub_lineMap] at hfQ
      have : 0 < (1 - μ) * positiveOrientation.areaForm (cfg.A -ᵥ cfg.B) (cfg.T -ᵥ cfg.B) +
          μ * positiveOrientation.areaForm (cfg.A -ᵥ cfg.B) (cfg.C -ᵥ cfg.B) :=
        add_pos (mul_pos (sub_pos.mpr hμ1) hfT) (mul_pos hμ hfC)
      linarith
    · -- `μ ≥ 1`: `Q` beyond `C` (or equal), so `σ(∡ B C Q) = -1`, against the anchor.
      push_neg at hμ1
      have hμ' : 1 < μ := by
        rcases eq_or_lt_of_le hμ1 with heq | hlt'
        · exfalso
          apply cfg.Q_ne_C
          have hv : cfg.Q -ᵥ cfg.T = cfg.C -ᵥ cfg.T := by rw [← hμv, ← heq, one_smul]
          exact vsub_left_cancel hv
        · exact hlt'
      have hs : (∡ cfg.B cfg.C cfg.Q).sign = -1 := by
        have hv : cfg.Q -ᵥ cfg.C = (μ - 1) • (cfg.C -ᵥ cfg.T) := by
          rw [← vsub_sub_vsub_cancel_right cfg.Q cfg.C cfg.T, ← hμv, sub_smul, one_smul]
        have hπ : ∡ cfg.B cfg.C cfg.Q = ∡ cfg.B cfg.C cfg.T + ↑Real.pi := by
          show positiveOrientation.oangle (cfg.B -ᵥ cfg.C) (cfg.Q -ᵥ cfg.C) =
            positiveOrientation.oangle (cfg.B -ᵥ cfg.C) (cfg.T -ᵥ cfg.C) + ↑Real.pi
          rw [hv, positiveOrientation.oangle_smul_right_of_pos _ _ (sub_pos.mpr hμ'),
            ← neg_vsub_eq_vsub_rev cfg.T cfg.C,
            positiveOrientation.oangle_neg_right (vsub_ne_zero.mpr cfg.B_ne_C)
              (vsub_ne_zero.mpr cfg.C_ne_T.symm)]
        rw [hπ, Real.Angle.sign_add_pi, sign_eq_one_of_oangle_pos cfg.oangle_BCT_pos]
      have h1 := cfg.sign_BCQ
      rw [hs] at h1
      simp at h1
  · rw [← neg_vsub_eq_vsub_rev cfg.T cfg.C, ← neg_vsub_eq_vsub_rev cfg.Q cfg.T] at h
    exact (sameRay_neg_iff.mp h).symm

/-- `S` is on the ray from `T` opposite to `D` (POS2). -/
theorem sameRay_ST : SameRay ℝ (cfg.S -ᵥ cfg.T) (cfg.T -ᵥ cfg.D) := by
  have hd := sameRay_or_sameRay_neg_vsub_of_collinear cfg.D_ne_T cfg.S_ne_T cfg.collinear_DTS
  rcases hd with h | h
  · -- `S` on ray `TD`: exclude.
    exfalso
    obtain ⟨ν, hν, hνv⟩ := h.exists_pos_left (vsub_ne_zero.mpr cfg.D_ne_T)
      (vsub_ne_zero.mpr cfg.S_ne_T)
    have hS : cfg.S = AffineMap.lineMap cfg.T cfg.D ν := by
      rw [AffineMap.lineMap_apply, hνv]; exact (vsub_vadd cfg.S cfg.T).symm
    by_cases hν1 : ν < 1
    · -- `0 < ν < 1`: `S` strictly between `T` and `D`, so on the interior side of `AE`.
      have hfT : 0 < positiveOrientation.areaForm (cfg.E -ᵥ cfg.A) (cfg.T -ᵥ cfg.A) :=
        sign_eq_one_iff.mp (by
          rw [← sign_oangle_eq_sign_areaForm]
          exact sign_eq_one_of_oangle_pos cfg.oangle_EAT_pos)
      have hfD : 0 < positiveOrientation.areaForm (cfg.E -ᵥ cfg.A) (cfg.D -ᵥ cfg.A) :=
        sign_eq_one_iff.mp (by
          rw [← sign_oangle_eq_sign_areaForm]
          exact sign_eq_one_of_oangle_pos (cfg.hconv_EA cfg.D (by simp : cfg.D ∈ ({cfg.B, cfg.C, cfg.D} : Set Pt))))
      have hfS : positiveOrientation.areaForm (cfg.E -ᵥ cfg.A) (cfg.S -ᵥ cfg.A) = 0 := by
        have h0 : (∡ cfg.E cfg.A cfg.S).sign = 0 :=
          oangle_sign_eq_zero_iff_collinear.mpr (collinear_swap (collinear_rotate cfg.collinear_AES))
        rw [sign_oangle_eq_sign_areaForm] at h0
        exact sign_eq_zero_iff.mp h0
      rw [hS, areaForm_vsub_lineMap] at hfS
      have : 0 < (1 - ν) * positiveOrientation.areaForm (cfg.E -ᵥ cfg.A) (cfg.T -ᵥ cfg.A) +
          ν * positiveOrientation.areaForm (cfg.E -ᵥ cfg.A) (cfg.D -ᵥ cfg.A) :=
        add_pos (mul_pos (sub_pos.mpr hν1) hfT) (mul_pos hν hfD)
      linarith
    · -- `ν ≥ 1`: `S` beyond `D` (or equal), so `σ(∡ A D S) = 1`, against the anchor `-1`.
      push_neg at hν1
      have hν' : 1 < ν := by
        rcases eq_or_lt_of_le hν1 with heq | hlt'
        · exfalso
          apply cfg.not_collinear_AED
          have hv : cfg.S -ᵥ cfg.T = cfg.D -ᵥ cfg.T := by rw [← hνv, ← heq, one_smul]
          have hSD : cfg.S = cfg.D := vsub_left_cancel hv
          rw [← hSD]
          exact cfg.collinear_AES
        · exact hlt'
      -- anchor: `σ(∡ A D S) = -1` from the given order via the segment-sign lemma.
      have hanchor : (∡ cfg.A cfg.D cfg.S).sign = -1 := by
        have h₂ : SameRay ℝ (cfg.S -ᵥ cfg.A) (cfg.A -ᵥ cfg.E) :=
          (cfg.sbtw_EAS.wbtw.sameRay_vsub).symm
        have hcol : Collinear ℝ ({cfg.A, cfg.S, cfg.E, cfg.A} : Set Pt) := by
          rw [Set.insert_eq_of_mem (by simp : cfg.A ∈ insert cfg.S (insert cfg.E {cfg.A}))]
          exact collinear_rev cfg.collinear_AES
        have h := Collinear.oangle_sign_of_sameRay_vsub cfg.D cfg.A_ne_S cfg.A_ne_E.symm hcol h₂
        -- h : (∡ A D S).sign = (∡ E D A).sign
        rw [h]
        have h'' : (∡ cfg.E cfg.D cfg.A).sign = -(∡ cfg.A cfg.D cfg.E).sign :=
          (oangle_swap₁₃_sign _ _ _).symm
        rw [h'', ← oangle_rotate_sign cfg.A cfg.D cfg.E, sign_eq_one_of_oangle_pos cfg.oangle_DEA_pos]
      have hs : (∡ cfg.A cfg.D cfg.S).sign = 1 := by
        have hv : cfg.S -ᵥ cfg.D = (ν - 1) • (cfg.D -ᵥ cfg.T) := by
          rw [← vsub_sub_vsub_cancel_right cfg.S cfg.D cfg.T, ← hνv, sub_smul, one_smul]
        have hπ : ∡ cfg.A cfg.D cfg.S = ∡ cfg.A cfg.D cfg.T + ↑Real.pi := by
          show positiveOrientation.oangle (cfg.A -ᵥ cfg.D) (cfg.S -ᵥ cfg.D) =
            positiveOrientation.oangle (cfg.A -ᵥ cfg.D) (cfg.T -ᵥ cfg.D) + ↑Real.pi
          rw [hv, positiveOrientation.oangle_smul_right_of_pos _ _ (sub_pos.mpr hν'),
            ← neg_vsub_eq_vsub_rev cfg.T cfg.D,
            positiveOrientation.oangle_neg_right (vsub_ne_zero.mpr cfg.D_ne_A.symm)
              (vsub_ne_zero.mpr cfg.D_ne_T.symm)]
        rw [hπ, Real.Angle.sign_add_pi]
        have hsgn : (∡ cfg.A cfg.D cfg.T).sign = -1 := by
          rw [← oangle_rotate_sign cfg.A cfg.D cfg.T]
          exact cfg.sign_DTA
        rw [hsgn, neg_neg]
      rw [hs] at hanchor
      simp at hanchor
  · rw [← neg_vsub_eq_vsub_rev cfg.T cfg.D, ← neg_vsub_eq_vsub_rev cfg.S cfg.T] at h
    exact (sameRay_neg_iff.mp h).symm

/-! ### Fan angle addition (both sign versions) -/

/-- If `A + B = C` holds for oriented angles and all three have sign `1`, the unoriented
angles also add. -/
theorem angle_add_angle_eq_angle_of_sign_eq_one {p p₁ p₂ p₃ : Pt}
    (hp₁ : p₁ ≠ p) (hp₂ : p₂ ≠ p) (hp₃ : p₃ ≠ p)
    (h₁ : (∡ p₁ p p₂).sign = 1) (h₂ : (∡ p₂ p p₃).sign = 1) (h₃ : (∡ p₁ p p₃).sign = 1) :
    ∠ p₁ p p₂ + ∠ p₂ p p₃ = ∠ p₁ p p₃ := by
  have h := oangle_add hp₁ hp₂ hp₃
  rw [oangle_eq_angle_of_sign_eq_one h₁, oangle_eq_angle_of_sign_eq_one h₂,
    oangle_eq_angle_of_sign_eq_one h₃, ← Real.Angle.coe_add] at h
  have ha : 0 < ∠ p₁ p p₂ := angle_pos_of_not_collinear (by
    rw [← oangle_sign_eq_zero_iff_collinear, h₁]
    simp)
  have hb : 0 < ∠ p₂ p p₃ := angle_pos_of_not_collinear (by
    rw [← oangle_sign_eq_zero_iff_collinear, h₂]
    simp)
  have hc : 0 < ∠ p₁ p p₃ := angle_pos_of_not_collinear (by
    rw [← oangle_sign_eq_zero_iff_collinear, h₃]
    simp)
  have htr := congrArg Real.Angle.toReal h
  rw [Real.Angle.toReal_coe_eq_self_iff.mpr
    ⟨lt_of_lt_of_le (by linarith [Real.pi_pos] : (-Real.pi : ℝ) < 0) (angle_nonneg _ _ _),
     angle_le_pi _ _ _⟩] at htr
  by_cases hab : ∠ p₁ p p₂ + ∠ p₂ p p₃ ≤ Real.pi
  · rw [Real.Angle.toReal_coe_eq_self_iff.mpr ⟨by linarith [ha, hb], hab⟩] at htr
    linarith [htr]
  · push Not at hab
    have hper : ((∠ p₁ p p₂ + ∠ p₂ p p₃ - 2 * Real.pi : ℝ) : Real.Angle) =
        ((∠ p₁ p p₂ + ∠ p₂ p p₃ : ℝ) : Real.Angle) := by
      have h0 : ((2 * Real.pi : ℝ) : Real.Angle) = 0 := Real.Angle.coe_two_pi
      have h1 := Real.Angle.coe_add (∠ p₁ p p₂ + ∠ p₂ p p₃ - 2 * Real.pi) (2 * Real.pi)
      rw [sub_add_cancel, h0, add_zero] at h1
      exact h1.symm
    rw [← hper, Real.Angle.toReal_coe_eq_self_iff.mpr ⟨by linarith [hab],
      by linarith [hab, angle_le_pi p₁ p p₂, angle_le_pi p₂ p p₃]⟩] at htr
    linarith [htr, hab, hc, angle_le_pi p₁ p p₂, angle_le_pi p₂ p p₃, angle_le_pi p₁ p p₃]

/-- If `A + B = C` holds for oriented angles and all three have sign `-1`, the unoriented
angles also add. -/
theorem angle_add_angle_eq_angle_of_sign_eq_neg_one {p p₁ p₂ p₃ : Pt}
    (hp₁ : p₁ ≠ p) (hp₂ : p₂ ≠ p) (hp₃ : p₃ ≠ p)
    (h₁ : (∡ p₁ p p₂).sign = -1) (h₂ : (∡ p₂ p p₃).sign = -1) (h₃ : (∡ p₁ p p₃).sign = -1) :
    ∠ p₁ p p₂ + ∠ p₂ p p₃ = ∠ p₁ p p₃ := by
  have s₁ : (∡ p₃ p p₂).sign = 1 := by rw [← oangle_swap₁₃_sign, h₂, neg_neg]
  have s₂ : (∡ p₂ p p₁).sign = 1 := by rw [← oangle_swap₁₃_sign, h₁, neg_neg]
  have s₃ : (∡ p₃ p p₁).sign = 1 := by rw [← oangle_swap₁₃_sign, h₃, neg_neg]
  have h := angle_add_angle_eq_angle_of_sign_eq_one hp₃ hp₂ hp₁ s₁ s₂ s₃
  rw [angle_comm p₃ p p₂, angle_comm p₂ p p₁, angle_comm p₃ p p₁] at h
  linarith

/-! ### Positions of `P` and `R` on line `CD` -/

theorem sign_CTD : (∡ cfg.C cfg.T cfg.D).sign = -1 := by
  have hr : (∡ cfg.D cfg.T cfg.C).sign = (∡ cfg.C cfg.D cfg.T).sign := oangle_rotate_sign _ _ _
  have hs : (∡ cfg.C cfg.T cfg.D).sign = -(∡ cfg.D cfg.T cfg.C).sign :=
    (oangle_swap₁₃_sign _ _ _).symm
  rw [hs, hr, sign_eq_one_of_oangle_pos cfg.oangle_CDT_pos]

theorem sign_DTC : (∡ cfg.D cfg.T cfg.C).sign = 1 := by
  have hr : (∡ cfg.D cfg.T cfg.C).sign = (∡ cfg.C cfg.D cfg.T).sign := oangle_rotate_sign _ _ _
  rw [hr, sign_eq_one_of_oangle_pos cfg.oangle_CDT_pos]

/-- `R` is beyond `E` from `A`, so `∡ D E R = ∡ D E A + π`. -/
theorem sign_DER : (∡ cfg.D cfg.E cfg.R).sign = -1 := by
  have h₂ : SameRay ℝ (cfg.E -ᵥ cfg.R) (cfg.A -ᵥ cfg.E) := cfg.sbtw_REA.wbtw.sameRay_vsub
  obtain ⟨r, hr, hvr⟩ := h₂.exists_pos_left (vsub_ne_zero.mpr cfg.R_ne_E.symm)
    (vsub_ne_zero.mpr cfg.A_ne_E)
  have hπ : ∡ cfg.D cfg.E cfg.R = ∡ cfg.D cfg.E cfg.A + ↑Real.pi := by
    show positiveOrientation.oangle (cfg.D -ᵥ cfg.E) (cfg.R -ᵥ cfg.E) =
      positiveOrientation.oangle (cfg.D -ᵥ cfg.E) (cfg.A -ᵥ cfg.E) + ↑Real.pi
    rw [← neg_vsub_eq_vsub_rev cfg.E cfg.R, ← hvr,
      positiveOrientation.oangle_smul_right_of_pos _ _ hr,
      positiveOrientation.oangle_neg_right (vsub_ne_zero.mpr cfg.D_ne_E)
        (vsub_ne_zero.mpr cfg.R_ne_E.symm)]
  rw [hπ, Real.Angle.sign_add_pi, sign_eq_one_of_oangle_pos cfg.oangle_DEA_pos]

theorem sign_EDR : (∡ cfg.E cfg.D cfg.R).sign = 1 := by
  have h : (∡ cfg.E cfg.D cfg.R).sign = -(∡ cfg.D cfg.E cfg.R).sign :=
    (oangle_swap₁₂_sign _ _ _).symm
  rw [h, cfg.sign_DER, neg_neg]

/-- `P` is beyond `B` from `A`, so `∡ C B P = ∡ C B A + π`. -/
theorem sign_CBP : (∡ cfg.C cfg.B cfg.P).sign = 1 := by
  have h₁ : SameRay ℝ (cfg.B -ᵥ cfg.P) (cfg.A -ᵥ cfg.B) := cfg.sbtw_PBA.wbtw.sameRay_vsub
  obtain ⟨r, hr, hvr⟩ := h₁.exists_pos_left (vsub_ne_zero.mpr cfg.P_ne_B.symm)
    (vsub_ne_zero.mpr cfg.A_ne_B)
  have hπ : ∡ cfg.C cfg.B cfg.P = ∡ cfg.C cfg.B cfg.A + ↑Real.pi := by
    show positiveOrientation.oangle (cfg.C -ᵥ cfg.B) (cfg.P -ᵥ cfg.B) =
      positiveOrientation.oangle (cfg.C -ᵥ cfg.B) (cfg.A -ᵥ cfg.B) + ↑Real.pi
    rw [← neg_vsub_eq_vsub_rev cfg.B cfg.P, ← hvr,
      positiveOrientation.oangle_smul_right_of_pos _ _ hr,
      positiveOrientation.oangle_neg_right (vsub_ne_zero.mpr cfg.B_ne_C.symm)
        (vsub_ne_zero.mpr cfg.P_ne_B.symm)]
  have hs : (∡ cfg.C cfg.B cfg.A).sign = -(∡ cfg.A cfg.B cfg.C).sign :=
    (oangle_swap₁₃_sign _ _ _).symm
  rw [hπ, Real.Angle.sign_add_pi, hs, sign_eq_one_of_oangle_pos cfg.oangle_ABC_pos, neg_neg]

theorem sign_BCP : (∡ cfg.B cfg.C cfg.P).sign = -1 := by
  have h : (∡ cfg.B cfg.C cfg.P).sign = -(∡ cfg.P cfg.C cfg.B).sign :=
    (oangle_swap₁₃_sign _ _ _).symm
  have hr : (∡ cfg.P cfg.C cfg.B).sign = (∡ cfg.C cfg.B cfg.P).sign :=
    (oangle_rotate_sign cfg.B cfg.P cfg.C).trans (oangle_rotate_sign cfg.C cfg.B cfg.P)
  rw [h, hr, cfg.sign_CBP]

/-- `R` lies beyond `D` on line `CD`: `R −ᵥ D = t • (D −ᵥ C)` with `t > 0`. -/
theorem R_pos : ∃ t : ℝ, 0 < t ∧ cfg.R -ᵥ cfg.D = t • (cfg.D -ᵥ cfg.C) := by
  have hR : cfg.R ∈ affineSpan ℝ ({cfg.C, cfg.D} : Set Pt) := by
    have h := cfg.collinear_CDR.affineSpan_eq_of_ne (Set.mem_insert _ _)
      (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) cfg.C_ne_D
    rw [h]
    apply mem_affineSpan
    simp
  have hD : cfg.D ∈ affineSpan ℝ ({cfg.C, cfg.D} : Set Pt) := by
    apply mem_affineSpan
    simp
  have hv : cfg.R -ᵥ cfg.D ∈ Submodule.span ℝ {cfg.C -ᵥ cfg.D} := by
    have h2 := AffineSubspace.vsub_mem_direction hR hD
    rw [direction_affineSpan, vectorSpan_pair] at h2
    exact h2
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hv
  refine ⟨-s, ?_, ?_⟩
  · by_cases hs0 : s = 0
    · exfalso
      rw [hs0, zero_smul] at hs
      exact cfg.R_ne_D (vsub_eq_zero_iff_eq.mp hs.symm)
    rcases lt_or_gt_of_ne hs0 with hlt | hgt
    · exact neg_pos.mpr hlt
    · exfalso
      have h1 : ∡ cfg.E cfg.D cfg.R = ∡ cfg.E cfg.D cfg.C := by
        show positiveOrientation.oangle (cfg.E -ᵥ cfg.D) (cfg.R -ᵥ cfg.D) =
          positiveOrientation.oangle (cfg.E -ᵥ cfg.D) (cfg.C -ᵥ cfg.D)
        rw [← hs, positiveOrientation.oangle_smul_right_of_pos _ _ hgt]
      have h2 : (∡ cfg.E cfg.D cfg.R).sign = -1 := by
        rw [h1]
        have h3 : (∡ cfg.E cfg.D cfg.C).sign = -(∡ cfg.C cfg.D cfg.E).sign :=
          (oangle_swap₁₃_sign _ _ _).symm
        rw [h3, sign_eq_one_of_oangle_pos cfg.oangle_CDE_pos]
      have h4 := cfg.sign_EDR
      rw [h2] at h4
      simp at h4
  · rw [neg_smul, ← neg_vsub_eq_vsub_rev cfg.C cfg.D, smul_neg, neg_neg, ← hs]

/-- `P` lies beyond `C` on line `CD`: `P −ᵥ C = u • (C −ᵥ D)` with `u > 0`. -/
theorem P_pos : ∃ u : ℝ, 0 < u ∧ cfg.P -ᵥ cfg.C = u • (cfg.C -ᵥ cfg.D) := by
  have hP : cfg.P ∈ affineSpan ℝ ({cfg.C, cfg.D} : Set Pt) := by
    have h := cfg.collinear_CDP.affineSpan_eq_of_ne (Set.mem_insert _ _)
      (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) cfg.C_ne_D
    rw [h]
    apply mem_affineSpan
    simp
  have hC : cfg.C ∈ affineSpan ℝ ({cfg.C, cfg.D} : Set Pt) := by
    apply mem_affineSpan
    simp
  have hv : cfg.P -ᵥ cfg.C ∈ Submodule.span ℝ {cfg.C -ᵥ cfg.D} := by
    have h2 := AffineSubspace.vsub_mem_direction hP hC
    rw [direction_affineSpan, vectorSpan_pair] at h2
    exact h2
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.mp hv
  refine ⟨u, ?_, hu.symm⟩
  by_cases hu0 : u = 0
  · exfalso
    rw [hu0, zero_smul] at hu
    exact cfg.P_ne_C (vsub_eq_zero_iff_eq.mp hu.symm)
  rcases lt_or_gt_of_ne hu0 with hlt | hgt
  · exfalso
    have h1 : ∡ cfg.B cfg.C cfg.P = ∡ cfg.B cfg.C cfg.D := by
      show positiveOrientation.oangle (cfg.B -ᵥ cfg.C) (cfg.P -ᵥ cfg.C) =
        positiveOrientation.oangle (cfg.B -ᵥ cfg.C) (cfg.D -ᵥ cfg.C)
      rw [← hu, positiveOrientation.oangle_smul_right_of_neg _ _ hlt,
        ← neg_vsub_eq_vsub_rev cfg.C cfg.D]
    have h2 : (∡ cfg.B cfg.C cfg.P).sign = 1 := by
      rw [h1, sign_eq_one_of_oangle_pos cfg.oangle_BCD_pos]
    have h4 := cfg.sign_BCP
    rw [h2] at h4
    simp at h4
  · exact hgt

/-! ### Non-parallelism -/

/-- Line `CT` is not parallel to line `AE`. -/
theorem not_parallel_CT_AE : ¬ line[ℝ, cfg.C, cfg.T] ∥ line[ℝ, cfg.A, cfg.E] := by
  intro hpar
  obtain ⟨t, ht, htv⟩ := cfg.R_pos
  have hfD : positiveOrientation.areaForm (cfg.C -ᵥ cfg.T) (cfg.D -ᵥ cfg.T) < 0 :=
    sign_eq_neg_one_iff.mp (by rw [← sign_oangle_eq_sign_areaForm]; exact cfg.sign_CTD)
  have hself : positiveOrientation.areaForm (cfg.C -ᵥ cfg.T) (cfg.D -ᵥ cfg.C) =
      positiveOrientation.areaForm (cfg.C -ᵥ cfg.T) (cfg.D -ᵥ cfg.T) := by
    rw [← vsub_sub_vsub_cancel_right cfg.D cfg.C cfg.T, map_sub,
      positiveOrientation.areaForm_apply_self, sub_zero]
  have hfR : positiveOrientation.areaForm (cfg.C -ᵥ cfg.T) (cfg.R -ᵥ cfg.T) < 0 := by
    have hv : cfg.R -ᵥ cfg.T = (cfg.D -ᵥ cfg.T) + t • (cfg.D -ᵥ cfg.C) := by
      rw [← htv, add_comm, vsub_add_vsub_cancel]
    rw [hv, map_add, map_smul, smul_eq_mul, hself]
    have hle : (1 + t) * positiveOrientation.areaForm (cfg.C -ᵥ cfg.T) (cfg.D -ᵥ cfg.T) < 0 :=
      mul_neg_of_pos_of_neg (by linarith) hfD
    linarith
  have hfA : 0 < positiveOrientation.areaForm (cfg.C -ᵥ cfg.T) (cfg.A -ᵥ cfg.T) :=
    sign_eq_one_iff.mp (by rw [← sign_oangle_eq_sign_areaForm]; exact cfg.sign_CTA)
  have hdir0 : positiveOrientation.areaForm (cfg.C -ᵥ cfg.T) (cfg.E -ᵥ cfg.A) = 0 := by
    have hdir : (affineSpan ℝ ({cfg.C, cfg.T} : Set Pt)).direction =
        (affineSpan ℝ ({cfg.A, cfg.E} : Set Pt)).direction :=
      (AffineSubspace.parallel_iff_direction_eq_and_eq_bot_iff_eq_bot.mp hpar).1
    rw [direction_affineSpan, direction_affineSpan, vectorSpan_pair, vectorSpan_pair] at hdir
    have hEA : cfg.E -ᵥ cfg.A ∈ Submodule.span ℝ {cfg.A -ᵥ cfg.E} := by
      have h1 : (-1 : ℝ) • (cfg.A -ᵥ cfg.E) ∈ Submodule.span ℝ {cfg.A -ᵥ cfg.E} :=
        Submodule.smul_mem _ (-1 : ℝ) (Submodule.mem_span_singleton_self _)
      rw [neg_one_smul, neg_vsub_eq_vsub_rev cfg.A cfg.E] at h1
      exact h1
    rw [← hdir] at hEA
    obtain ⟨q, hq⟩ := Submodule.mem_span_singleton.mp hEA
    rw [← hq, map_smul, smul_eq_mul, positiveOrientation.areaForm_apply_self, mul_zero]
  have hfRA : positiveOrientation.areaForm (cfg.C -ᵥ cfg.T) (cfg.R -ᵥ cfg.T) =
      positiveOrientation.areaForm (cfg.C -ᵥ cfg.T) (cfg.A -ᵥ cfg.T) := by
    have hR : cfg.R ∈ affineSpan ℝ ({cfg.A, cfg.E} : Set Pt) := by
      have h := cfg.collinear_AER.affineSpan_eq_of_ne (Set.mem_insert _ _)
        (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) cfg.A_ne_E
      rw [h]
      apply mem_affineSpan
      simp
    have hA : cfg.A ∈ affineSpan ℝ ({cfg.A, cfg.E} : Set Pt) := by
      apply mem_affineSpan
      simp
    have hv2 : cfg.R -ᵥ cfg.A ∈ Submodule.span ℝ {cfg.A -ᵥ cfg.E} := by
      have h2 := AffineSubspace.vsub_mem_direction hR hA
      rw [direction_affineSpan, vectorSpan_pair] at h2
      exact h2
    obtain ⟨q, hq⟩ := Submodule.mem_span_singleton.mp hv2
    have hv : cfg.R -ᵥ cfg.T = (cfg.A -ᵥ cfg.T) + (-q) • (cfg.E -ᵥ cfg.A) := by
      have hqe : cfg.R -ᵥ cfg.A = (-q) • (cfg.E -ᵥ cfg.A) := by
        rw [neg_smul, ← neg_vsub_eq_vsub_rev cfg.A cfg.E, smul_neg, neg_neg, ← hq]
      rw [← hqe, add_comm, vsub_add_vsub_cancel]
    rw [hv, map_add, map_smul, smul_eq_mul, hdir0, mul_zero, add_zero]
  rw [hfRA] at hfR
  linarith

/-- Line `DT` is not parallel to line `AB`. -/
theorem not_parallel_DT_AB : ¬ line[ℝ, cfg.D, cfg.T] ∥ line[ℝ, cfg.A, cfg.B] := by
  intro hpar
  obtain ⟨u, hu, huv⟩ := cfg.P_pos
  have hfC : 0 < positiveOrientation.areaForm (cfg.D -ᵥ cfg.T) (cfg.C -ᵥ cfg.T) :=
    sign_eq_one_iff.mp (by rw [← sign_oangle_eq_sign_areaForm]; exact cfg.sign_DTC)
  have hself : positiveOrientation.areaForm (cfg.D -ᵥ cfg.T) (cfg.C -ᵥ cfg.D) =
      positiveOrientation.areaForm (cfg.D -ᵥ cfg.T) (cfg.C -ᵥ cfg.T) := by
    rw [← vsub_sub_vsub_cancel_right cfg.C cfg.D cfg.T, map_sub,
      positiveOrientation.areaForm_apply_self, sub_zero]
  have hfP : 0 < positiveOrientation.areaForm (cfg.D -ᵥ cfg.T) (cfg.P -ᵥ cfg.T) := by
    have hv : cfg.P -ᵥ cfg.T = (cfg.C -ᵥ cfg.T) + u • (cfg.C -ᵥ cfg.D) := by
      rw [← huv, add_comm, vsub_add_vsub_cancel]
    rw [hv, map_add, map_smul, smul_eq_mul, hself]
    have hle : 0 < (1 + u) * positiveOrientation.areaForm (cfg.D -ᵥ cfg.T) (cfg.C -ᵥ cfg.T) :=
      mul_pos (by linarith) hfC
    linarith
  have hfA : positiveOrientation.areaForm (cfg.D -ᵥ cfg.T) (cfg.A -ᵥ cfg.T) < 0 :=
    sign_eq_neg_one_iff.mp (by rw [← sign_oangle_eq_sign_areaForm]; exact cfg.sign_DTA)
  have hdir0 : positiveOrientation.areaForm (cfg.D -ᵥ cfg.T) (cfg.B -ᵥ cfg.A) = 0 := by
    have hdir : (affineSpan ℝ ({cfg.D, cfg.T} : Set Pt)).direction =
        (affineSpan ℝ ({cfg.A, cfg.B} : Set Pt)).direction :=
      (AffineSubspace.parallel_iff_direction_eq_and_eq_bot_iff_eq_bot.mp hpar).1
    rw [direction_affineSpan, direction_affineSpan, vectorSpan_pair, vectorSpan_pair] at hdir
    have hBA : cfg.B -ᵥ cfg.A ∈ Submodule.span ℝ {cfg.A -ᵥ cfg.B} := by
      have h1 : (-1 : ℝ) • (cfg.A -ᵥ cfg.B) ∈ Submodule.span ℝ {cfg.A -ᵥ cfg.B} :=
        Submodule.smul_mem _ (-1 : ℝ) (Submodule.mem_span_singleton_self _)
      rw [neg_one_smul, neg_vsub_eq_vsub_rev cfg.A cfg.B] at h1
      exact h1
    rw [← hdir] at hBA
    obtain ⟨q, hq⟩ := Submodule.mem_span_singleton.mp hBA
    rw [← hq, map_smul, smul_eq_mul, positiveOrientation.areaForm_apply_self, mul_zero]
  have hfPA : positiveOrientation.areaForm (cfg.D -ᵥ cfg.T) (cfg.P -ᵥ cfg.T) =
      positiveOrientation.areaForm (cfg.D -ᵥ cfg.T) (cfg.A -ᵥ cfg.T) := by
    have hP : cfg.P ∈ affineSpan ℝ ({cfg.A, cfg.B} : Set Pt) := by
      have h := cfg.collinear_ABP.affineSpan_eq_of_ne (Set.mem_insert _ _)
        (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) cfg.A_ne_B
      rw [h]
      apply mem_affineSpan
      simp
    have hA : cfg.A ∈ affineSpan ℝ ({cfg.A, cfg.B} : Set Pt) := by
      apply mem_affineSpan
      simp
    have hv2 : cfg.P -ᵥ cfg.A ∈ Submodule.span ℝ {cfg.A -ᵥ cfg.B} := by
      have h2 := AffineSubspace.vsub_mem_direction hP hA
      rw [direction_affineSpan, vectorSpan_pair] at h2
      exact h2
    obtain ⟨q, hq⟩ := Submodule.mem_span_singleton.mp hv2
    have hv : cfg.P -ᵥ cfg.T = (cfg.A -ᵥ cfg.T) + (-q) • (cfg.B -ᵥ cfg.A) := by
      have hqe : cfg.P -ᵥ cfg.A = (-q) • (cfg.B -ᵥ cfg.A) := by
        rw [neg_smul, ← neg_vsub_eq_vsub_rev cfg.A cfg.B, smul_neg, neg_neg, ← hq]
      rw [← hqe, add_comm, vsub_add_vsub_cancel]
    rw [hv, map_add, map_smul, smul_eq_mul, hdir0, mul_zero, add_zero]
  rw [hfPA] at hfP
  linarith

/-! ### The auxiliary points `K = CT ∩ AE` and `L = DT ∩ AB` -/

theorem K_exists : ∃ K : Pt, Collinear ℝ ({cfg.C, cfg.T, K} : Set Pt) ∧
    Collinear ℝ ({cfg.A, cfg.E, K} : Set Pt) :=
  exists_collinear_inter_of_not_parallel cfg.C_ne_T cfg.A_ne_E cfg.not_parallel_CT_AE

/-- The intersection `K` of lines `CT` and `AE`. -/
noncomputable def K : Pt := Classical.choose cfg.K_exists

theorem K_on_CT : Collinear ℝ ({cfg.C, cfg.T, cfg.K} : Set Pt) :=
  (Classical.choose_spec cfg.K_exists).1

theorem K_on_AE : Collinear ℝ ({cfg.A, cfg.E, cfg.K} : Set Pt) :=
  (Classical.choose_spec cfg.K_exists).2

theorem L_exists : ∃ L : Pt, Collinear ℝ ({cfg.D, cfg.T, L} : Set Pt) ∧
    Collinear ℝ ({cfg.A, cfg.B, L} : Set Pt) :=
  exists_collinear_inter_of_not_parallel cfg.D_ne_T cfg.A_ne_B cfg.not_parallel_DT_AB

/-- The intersection `L` of lines `DT` and `AB`. -/
noncomputable def L : Pt := Classical.choose cfg.L_exists

theorem L_on_DT : Collinear ℝ ({cfg.D, cfg.T, cfg.L} : Set Pt) :=
  (Classical.choose_spec cfg.L_exists).1

theorem L_on_AB : Collinear ℝ ({cfg.A, cfg.B, cfg.L} : Set Pt) :=
  (Classical.choose_spec cfg.L_exists).2

/-- `∠TBQ = ∠TBA` since `Q` is on ray `BA` from `B`; similarly `∠TES = ∠TEA`. -/
theorem angle_TBQ_eq_TES : ∠ cfg.T cfg.B cfg.Q = ∠ cfg.T cfg.E cfg.S := by
  have h₁ : SameRay ℝ (cfg.A -ᵥ cfg.B) (cfg.Q -ᵥ cfg.B) := cfg.sbtw_BAQ.wbtw.sameRay_vsub_left
  have h₂ : SameRay ℝ (cfg.A -ᵥ cfg.E) (cfg.S -ᵥ cfg.E) := cfg.sbtw_EAS.wbtw.sameRay_vsub_left
  obtain ⟨r₁, hr₁, hvr₁⟩ := h₁.exists_pos_left (vsub_ne_zero.mpr cfg.A_ne_B)
    (vsub_ne_zero.mpr cfg.B_ne_Q.symm)
  obtain ⟨r₂, hr₂, hvr₂⟩ := h₂.exists_pos_left (vsub_ne_zero.mpr cfg.A_ne_E)
    (vsub_ne_zero.mpr cfg.E_ne_S.symm)
  show InnerProductGeometry.angle _ _ = InnerProductGeometry.angle _ _
  rw [← hvr₁, ← hvr₂, InnerProductGeometry.angle_smul_right_of_pos _ _ hr₁,
    InnerProductGeometry.angle_smul_right_of_pos _ _ hr₂]
  show ∠ cfg.T cfg.B cfg.A = ∠ cfg.T cfg.E cfg.A
  rw [angle_comm cfg.T cfg.B cfg.A, cfg.angle_ABT_eq_TEA]

/-- Twice the oriented angle relation at `Q` and `S` (indirect similarity). -/
theorem two_zsmul_oangle_BQT : (2 : ℤ) • ∡ cfg.B cfg.Q cfg.T = -((2 : ℤ) • ∡ cfg.E cfg.S cfg.T) := by
  have hsum₁ := oangle_add_oangle_add_oangle_eq_pi cfg.B_ne_Q cfg.T_ne_B cfg.Q_ne_T
  have hsum₂ := oangle_add_oangle_add_oangle_eq_pi cfg.E_ne_S cfg.T_ne_E cfg.S_ne_T
  have hm1 : (2 : ℤ) • ∡ cfg.Q cfg.B cfg.T = (2 : ℤ) • ∡ cfg.A cfg.B cfg.T :=
    Collinear.two_zsmul_oangle_eq_left (collinear_rotate (collinear_swap cfg.collinear_ABQ))
      cfg.B_ne_Q.symm cfg.A_ne_B
  have hm2 : (2 : ℤ) • ∡ cfg.B cfg.T cfg.Q = (2 : ℤ) • ∡ cfg.B cfg.T cfg.C :=
    Collinear.two_zsmul_oangle_eq_right (collinear_rev cfg.collinear_CTQ) cfg.Q_ne_T cfg.C_ne_T
  have hm3 : (2 : ℤ) • ∡ cfg.S cfg.E cfg.T = (2 : ℤ) • ∡ cfg.A cfg.E cfg.T :=
    Collinear.two_zsmul_oangle_eq_left (collinear_rev cfg.collinear_AES)
      cfg.E_ne_S.symm cfg.A_ne_E
  have hm4 : (2 : ℤ) • ∡ cfg.E cfg.T cfg.S = (2 : ℤ) • ∡ cfg.E cfg.T cfg.D :=
    Collinear.two_zsmul_oangle_eq_right (collinear_rev cfg.collinear_DTS) cfg.S_ne_T cfg.D_ne_T
  have h2 : (2 : ℤ) • ∡ cfg.Q cfg.B cfg.T + (2 : ℤ) • ∡ cfg.B cfg.T cfg.Q +
      (2 : ℤ) • ∡ cfg.T cfg.Q cfg.B = 0 := by
    have h := hsum₁
    apply_fun ((2 : ℤ) • ·) at h
    rwa [smul_add, smul_add, Real.Angle.two_zsmul_coe_pi] at h
  have h3 : (2 : ℤ) • ∡ cfg.S cfg.E cfg.T + (2 : ℤ) • ∡ cfg.E cfg.T cfg.S +
      (2 : ℤ) • ∡ cfg.T cfg.S cfg.E = 0 := by
    have h := hsum₂
    apply_fun ((2 : ℤ) • ·) at h
    rwa [smul_add, smul_add, Real.Angle.two_zsmul_coe_pi] at h
  rw [hm1, hm2] at h2
  rw [hm3, hm4] at h3
  have hrev1 : ∡ cfg.T cfg.E cfg.A = -∡ cfg.A cfg.E cfg.T :=
    add_eq_zero_iff_eq_neg.mp (oangle_add_oangle_rev _ _ _)
  have hrev2 : ∡ cfg.D cfg.T cfg.E = -∡ cfg.E cfg.T cfg.D :=
    add_eq_zero_iff_eq_neg.mp (oangle_add_oangle_rev _ _ _)
  have hrev3 : ∡ cfg.B cfg.Q cfg.T = -∡ cfg.T cfg.Q cfg.B :=
    add_eq_zero_iff_eq_neg.mp (oangle_add_oangle_rev _ _ _)
  have hrev4 : ∡ cfg.E cfg.S cfg.T = -∡ cfg.T cfg.S cfg.E :=
    add_eq_zero_iff_eq_neg.mp (oangle_add_oangle_rev _ _ _)
  rw [cfg.oangle_ABT_eq_TEA, cfg.oangle_BTC_eq_DTE, hrev1, hrev2, smul_neg, smul_neg] at h2
  -- h2 : -(2)•∡AET + -(2)•∡ETD + (2)•∡TQB = 0
  have h6 : -((2 : ℤ) • ∡ cfg.A cfg.E cfg.T) + -((2 : ℤ) • ∡ cfg.E cfg.T cfg.D) =
      -((2 : ℤ) • ∡ cfg.T cfg.Q cfg.B) := add_eq_zero_iff_eq_neg.mp h2
  have e1 : (2 : ℤ) • ∡ cfg.T cfg.Q cfg.B =
      (2 : ℤ) • ∡ cfg.A cfg.E cfg.T + (2 : ℤ) • ∡ cfg.E cfg.T cfg.D := by
    rw [← neg_add] at h6
    exact (neg_inj.mp h6).symm
  -- h3 : (2)•∡AET + (2)•∡ETD + (2)•∡TSE = 0
  have e2 : (2 : ℤ) • ∡ cfg.T cfg.S cfg.E =
      -((2 : ℤ) • ∡ cfg.A cfg.E cfg.T + (2 : ℤ) • ∡ cfg.E cfg.T cfg.D) := by
    have h7 := add_eq_zero_iff_eq_neg.mp h3
    rw [h7, neg_neg]
  rw [hrev3, hrev4, smul_neg, smul_neg, neg_neg, e1, e2]

/-- The first similarity ratio: `TQ · TE = TS · TB`. -/
theorem dist_TQ_mul_TE : dist cfg.T cfg.Q * dist cfg.T cfg.E =
    dist cfg.T cfg.S * dist cfg.T cfg.B := by
  have h1 := sin_angle_mul_dist_eq_sin_angle_mul_dist cfg.B cfg.Q cfg.T
  have h2 := sin_angle_mul_dist_eq_sin_angle_mul_dist cfg.E cfg.S cfg.T
  have h3 : Real.sin (∠ cfg.B cfg.Q cfg.T) = Real.sin (∠ cfg.E cfg.S cfg.T) :=
    sin_angle_eq_sin_angle_of_two_zsmul_oangle_eq_neg cfg.B_ne_Q cfg.Q_ne_T.symm
      cfg.E_ne_S cfg.S_ne_T.symm cfg.two_zsmul_oangle_BQT
  have h4 : Real.sin (∠ cfg.T cfg.B cfg.Q) = Real.sin (∠ cfg.T cfg.E cfg.S) := by
    rw [cfg.angle_TBQ_eq_TES]
  have h5 : 0 < Real.sin (∠ cfg.B cfg.Q cfg.T) := sin_pos_of_not_collinear cfg.not_collinear_BQT
  have h6 : 0 < Real.sin (∠ cfg.E cfg.S cfg.T) := sin_pos_of_not_collinear cfg.not_collinear_EST
  rw [dist_comm cfg.Q cfg.T] at h1
  rw [dist_comm cfg.S cfg.T] at h2
  have e1 : dist cfg.T cfg.Q =
      Real.sin (∠ cfg.T cfg.B cfg.Q) * dist cfg.T cfg.B / Real.sin (∠ cfg.B cfg.Q cfg.T) := by
    rw [eq_div_iff h5.ne', mul_comm, h1]
  have e2 : dist cfg.T cfg.S =
      Real.sin (∠ cfg.T cfg.E cfg.S) * dist cfg.T cfg.E / Real.sin (∠ cfg.E cfg.S cfg.T) := by
    rw [eq_div_iff h6.ne', mul_comm, h2]
  rw [e1, e2, h3, h4]
  field_simp

/-! ### The second similarity: `△BTL ∼ −△ETK`, and its ratio -/

/-- If `B, T, D` are collinear, so are `C, T, E` (the rotation collapses). -/
theorem collinear_CTE_of_collinear_BTD (hBTD : Collinear ℝ ({cfg.B, cfg.T, cfg.D} : Set Pt)) :
    Collinear ℝ ({cfg.C, cfg.T, cfg.E} : Set Pt) := by
  have h := oangle_eq_zero_or_eq_pi_iff_collinear.mpr hBTD
  rw [cfg.oangle_BTD_eq_CTE] at h
  exact oangle_eq_zero_or_eq_pi_iff_collinear.mp h

/-- In the antipodal case, `L = B`. -/
theorem L_eq_B_of_collinear_BTD (hBTD : Collinear ℝ ({cfg.B, cfg.T, cfg.D} : Set Pt))
    (hne : cfg.L ≠ cfg.B) : False := by
  apply cfg.not_collinear_ABT
  have hiff4 : Collinear ℝ (insert cfg.B {cfg.D, cfg.T, cfg.L}) ↔
      Collinear ℝ ({cfg.B, cfg.D, cfg.T} : Set Pt) :=
    cfg.L_on_DT.collinear_insert_iff_of_ne (by simp : cfg.D ∈ ({cfg.D, cfg.T, cfg.L} : Set Pt))
      (by simp : cfg.T ∈ ({cfg.D, cfg.T, cfg.L} : Set Pt)) cfg.D_ne_T
  have h4 : Collinear ℝ (insert cfg.B {cfg.D, cfg.T, cfg.L}) := hiff4.2 (collinear_swap hBTD)
  have hiff5 : Collinear ℝ (insert cfg.A (insert cfg.B {cfg.D, cfg.T, cfg.L})) ↔
      Collinear ℝ ({cfg.A, cfg.L, cfg.B} : Set Pt) :=
    h4.collinear_insert_iff_of_ne (by simp : cfg.L ∈ _)
      (by simp : cfg.B ∈ _) hne
  have h5 : Collinear ℝ (insert cfg.A (insert cfg.B {cfg.D, cfg.T, cfg.L})) :=
    hiff5.2 (collinear_swap cfg.L_on_AB)
  apply h5.subset
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
      (Set.mem_insert _ _)))

/-- In the antipodal case, `K = E`. -/
theorem K_eq_E_of_collinear_CTE (hCTE : Collinear ℝ ({cfg.C, cfg.T, cfg.E} : Set Pt))
    (hne : cfg.K ≠ cfg.E) : False := by
  apply cfg.not_collinear_EAT
  have hiff4 : Collinear ℝ (insert cfg.E {cfg.C, cfg.T, cfg.K}) ↔
      Collinear ℝ ({cfg.E, cfg.C, cfg.T} : Set Pt) :=
    cfg.K_on_CT.collinear_insert_iff_of_ne (by simp : cfg.C ∈ ({cfg.C, cfg.T, cfg.K} : Set Pt))
      (by simp : cfg.T ∈ ({cfg.C, cfg.T, cfg.K} : Set Pt)) cfg.C_ne_T
  have h4 : Collinear ℝ (insert cfg.E {cfg.C, cfg.T, cfg.K}) :=
      hiff4.2 (collinear_rotate (collinear_rotate hCTE))
  have hiff5 : Collinear ℝ (insert cfg.A (insert cfg.E {cfg.C, cfg.T, cfg.K})) ↔
      Collinear ℝ ({cfg.A, cfg.K, cfg.E} : Set Pt) :=
    h4.collinear_insert_iff_of_ne (by simp : cfg.K ∈ _)
      (by simp : cfg.E ∈ _) hne
  have h5 : Collinear ℝ (insert cfg.A (insert cfg.E {cfg.C, cfg.T, cfg.K})) :=
    hiff5.2 (collinear_swap cfg.K_on_AE)
  apply h5.subset
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
      (Set.mem_insert _ _)))

/-- The second similarity ratio: `TL · TE = TK · TB`. -/
theorem dist_TL_mul_TE : dist cfg.T cfg.L * dist cfg.T cfg.E =
    dist cfg.T cfg.K * dist cfg.T cfg.B := by
  by_cases hBTD : Collinear ℝ ({cfg.B, cfg.T, cfg.D} : Set Pt)
  · -- antipodal case: `L = B` and `K = E`.
    by_cases hLB : cfg.L = cfg.B
    · rw [hLB]
      by_cases hKE : cfg.K = cfg.E
      · rw [hKE, mul_comm]
      · exact (cfg.K_eq_E_of_collinear_CTE (cfg.collinear_CTE_of_collinear_BTD hBTD) hKE).elim
    · exact (cfg.L_eq_B_of_collinear_BTD hBTD hLB).elim
  · -- generic case: law of sines on `△BTL` and `△ETK`.
    have hLB : cfg.L ≠ cfg.B := by
      intro h
      apply hBTD
      rw [← h]
      exact collinear_rev cfg.L_on_DT
    have hKE : cfg.K ≠ cfg.E := by
      intro h
      apply hBTD
      have hCTE : Collinear ℝ ({cfg.C, cfg.T, cfg.E} : Set Pt) := by
        rw [← h]
        exact cfg.K_on_CT
      have h2 := oangle_eq_zero_or_eq_pi_iff_collinear.mpr hCTE
      rw [← cfg.oangle_BTD_eq_CTE] at h2
      exact oangle_eq_zero_or_eq_pi_iff_collinear.mp h2
    have hLT : cfg.L ≠ cfg.T := by
      intro h
      apply cfg.not_collinear_ABT
      rw [← h]
      exact cfg.L_on_AB
    have hKT : cfg.K ≠ cfg.T := by
      intro h
      apply cfg.not_collinear_EAT
      rw [← h]
      exact collinear_swap (collinear_rotate cfg.K_on_AE)
    have hnc1 : ¬Collinear ℝ ({cfg.B, cfg.L, cfg.T} : Set Pt) := by
      intro hcol
      apply cfg.not_collinear_ABT
      have hiff : Collinear ℝ (insert cfg.A {cfg.B, cfg.L, cfg.T}) ↔
          Collinear ℝ ({cfg.A, cfg.B, cfg.L} : Set Pt) :=
        hcol.collinear_insert_iff_of_ne (by simp : cfg.B ∈ ({cfg.B, cfg.L, cfg.T} : Set Pt))
          (by simp : cfg.L ∈ ({cfg.B, cfg.L, cfg.T} : Set Pt)) hLB.symm
      have h4 : Collinear ℝ (insert cfg.A {cfg.B, cfg.L, cfg.T}) := hiff.2 cfg.L_on_AB
      apply h4.subset
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | rfl <;> simp
    have hnc2 : ¬Collinear ℝ ({cfg.E, cfg.K, cfg.T} : Set Pt) := by
      intro hcol
      apply cfg.not_collinear_EAT
      have hiff : Collinear ℝ (insert cfg.A {cfg.E, cfg.K, cfg.T}) ↔
          Collinear ℝ ({cfg.A, cfg.E, cfg.K} : Set Pt) :=
        hcol.collinear_insert_iff_of_ne (by simp : cfg.E ∈ ({cfg.E, cfg.K, cfg.T} : Set Pt))
          (by simp : cfg.K ∈ ({cfg.E, cfg.K, cfg.T} : Set Pt)) hKE.symm
      have h4 : Collinear ℝ (insert cfg.A {cfg.E, cfg.K, cfg.T}) := hiff.2 cfg.K_on_AE
      apply h4.subset
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | rfl <;> simp
    -- sin(∠TBL) = sin(∠TEK)
    have hmL : (2 : ℤ) • ∡ cfg.T cfg.B cfg.L = (2 : ℤ) • ∡ cfg.T cfg.B cfg.A :=
      Collinear.two_zsmul_oangle_eq_right (collinear_rev cfg.L_on_AB) hLB cfg.A_ne_B
    have hmK : (2 : ℤ) • ∡ cfg.T cfg.E cfg.K = (2 : ℤ) • ∡ cfg.T cfg.E cfg.A :=
      Collinear.two_zsmul_oangle_eq_right (collinear_rev cfg.K_on_AE) hKE cfg.A_ne_E
    have hsin1 : Real.sin (∠ cfg.T cfg.B cfg.L) = Real.sin (∠ cfg.T cfg.B cfg.A) :=
      sin_angle_eq_sin_angle_of_two_zsmul_oangle_eq cfg.T_ne_B hLB cfg.T_ne_B
        cfg.A_ne_B hmL
    have hsin2 : Real.sin (∠ cfg.T cfg.E cfg.K) = Real.sin (∠ cfg.T cfg.E cfg.A) :=
      sin_angle_eq_sin_angle_of_two_zsmul_oangle_eq cfg.T_ne_E hKE cfg.T_ne_E
        cfg.A_ne_E hmK
    have hsin_TBL_TES : Real.sin (∠ cfg.T cfg.B cfg.L) = Real.sin (∠ cfg.T cfg.E cfg.K) := by
      rw [hsin1, hsin2, angle_comm cfg.T cfg.B cfg.A, cfg.angle_ABT_eq_TEA]
    -- sin(∠BLT) = sin(∠EKT) via the oriented triangle sums
    have hsum₁ := oangle_add_oangle_add_oangle_eq_pi hLB.symm cfg.T_ne_B hLT
    have hsum₂ := oangle_add_oangle_add_oangle_eq_pi hKE.symm cfg.T_ne_E hKT
    have hm1 : (2 : ℤ) • ∡ cfg.L cfg.B cfg.T = (2 : ℤ) • ∡ cfg.A cfg.B cfg.T :=
      Collinear.two_zsmul_oangle_eq_left (collinear_rev cfg.L_on_AB) hLB cfg.A_ne_B
    have hm2 : (2 : ℤ) • ∡ cfg.B cfg.T cfg.L = (2 : ℤ) • ∡ cfg.B cfg.T cfg.D :=
      Collinear.two_zsmul_oangle_eq_right (collinear_rev cfg.L_on_DT) hLT cfg.D_ne_T
    have hm3 : (2 : ℤ) • ∡ cfg.K cfg.E cfg.T = (2 : ℤ) • ∡ cfg.A cfg.E cfg.T :=
      Collinear.two_zsmul_oangle_eq_left (collinear_rev cfg.K_on_AE) hKE cfg.A_ne_E
    have hm4 : (2 : ℤ) • ∡ cfg.E cfg.T cfg.K = (2 : ℤ) • ∡ cfg.E cfg.T cfg.C :=
      Collinear.two_zsmul_oangle_eq_right (collinear_rev cfg.K_on_CT) hKT cfg.C_ne_T
    have h2 : (2 : ℤ) • ∡ cfg.L cfg.B cfg.T + (2 : ℤ) • ∡ cfg.B cfg.T cfg.L +
        (2 : ℤ) • ∡ cfg.T cfg.L cfg.B = 0 := by
      have h := hsum₁
      apply_fun ((2 : ℤ) • ·) at h
      rwa [smul_add, smul_add, Real.Angle.two_zsmul_coe_pi] at h
    have h3 : (2 : ℤ) • ∡ cfg.K cfg.E cfg.T + (2 : ℤ) • ∡ cfg.E cfg.T cfg.K +
        (2 : ℤ) • ∡ cfg.T cfg.K cfg.E = 0 := by
      have h := hsum₂
      apply_fun ((2 : ℤ) • ·) at h
      rwa [smul_add, smul_add, Real.Angle.two_zsmul_coe_pi] at h
    rw [hm1, hm2] at h2
    rw [hm3, hm4] at h3
    have hrev1 : ∡ cfg.B cfg.L cfg.T = -∡ cfg.T cfg.L cfg.B :=
      add_eq_zero_iff_eq_neg.mp (oangle_add_oangle_rev _ _ _)
    have hrev2 : ∡ cfg.E cfg.K cfg.T = -∡ cfg.T cfg.K cfg.E :=
      add_eq_zero_iff_eq_neg.mp (oangle_add_oangle_rev _ _ _)
    have hrev3 : ∡ cfg.A cfg.E cfg.T = -∡ cfg.T cfg.E cfg.A :=
      add_eq_zero_iff_eq_neg.mp (oangle_add_oangle_rev _ _ _)
    have hrev4 : ∡ cfg.E cfg.T cfg.C = -∡ cfg.C cfg.T cfg.E :=
      add_eq_zero_iff_eq_neg.mp (oangle_add_oangle_rev _ _ _)
    have e1 : (2 : ℤ) • ∡ cfg.T cfg.L cfg.B =
        -((2 : ℤ) • ∡ cfg.A cfg.B cfg.T + (2 : ℤ) • ∡ cfg.B cfg.T cfg.D) := by
      have h6 := add_eq_zero_iff_eq_neg.mp h2
      rw [h6, neg_neg]
    have e2 : (2 : ℤ) • ∡ cfg.T cfg.K cfg.E =
        -((2 : ℤ) • ∡ cfg.A cfg.E cfg.T + (2 : ℤ) • ∡ cfg.E cfg.T cfg.C) := by
      have h7 := add_eq_zero_iff_eq_neg.mp h3
      rw [h7, neg_neg]
    have key : (2 : ℤ) • ∡ cfg.B cfg.L cfg.T = -((2 : ℤ) • ∡ cfg.E cfg.K cfg.T) := by
      rw [hrev1, hrev2, smul_neg, smul_neg, e1, e2, neg_neg, neg_neg,
        cfg.oangle_ABT_eq_TEA, cfg.oangle_BTD_eq_CTE, hrev3, hrev4, smul_neg, smul_neg,
        ← neg_add, neg_neg]
    have hsin3 : Real.sin (∠ cfg.B cfg.L cfg.T) = Real.sin (∠ cfg.E cfg.K cfg.T) :=
      sin_angle_eq_sin_angle_of_two_zsmul_oangle_eq_neg hLB.symm hLT.symm hKE.symm hKT.symm key
    -- law of sines assembly
    have h1 := sin_angle_mul_dist_eq_sin_angle_mul_dist cfg.B cfg.L cfg.T
    have h2 := sin_angle_mul_dist_eq_sin_angle_mul_dist cfg.E cfg.K cfg.T
    have h5 : 0 < Real.sin (∠ cfg.B cfg.L cfg.T) := sin_pos_of_not_collinear hnc1
    have h6 : 0 < Real.sin (∠ cfg.E cfg.K cfg.T) := sin_pos_of_not_collinear hnc2
    rw [dist_comm cfg.L cfg.T] at h1
    rw [dist_comm cfg.K cfg.T] at h2
    have e1 : dist cfg.T cfg.L =
        Real.sin (∠ cfg.T cfg.B cfg.L) * dist cfg.T cfg.B / Real.sin (∠ cfg.B cfg.L cfg.T) := by
      rw [eq_div_iff h5.ne', mul_comm, h1]
    have e2 : dist cfg.T cfg.K =
        Real.sin (∠ cfg.T cfg.E cfg.K) * dist cfg.T cfg.E / Real.sin (∠ cfg.E cfg.K cfg.T) := by
      rw [eq_div_iff h6.ne', mul_comm, h2]
    rw [e1, e2, hsin3, hsin_TBL_TES]
    field_simp

/-- `TK · TQ = TL · TS` (power of `T` with respect to the circle `KLSQ`). -/
theorem dist_TK_mul_TQ : dist cfg.T cfg.K * dist cfg.T cfg.Q =
    dist cfg.T cfg.L * dist cfg.T cfg.S := by
  have hTE : dist cfg.T cfg.E ≠ 0 := dist_ne_zero.mpr cfg.T_ne_E
  have hr1 := cfg.dist_TQ_mul_TE
  have hr2 := cfg.dist_TL_mul_TE
  have h1 : dist cfg.T cfg.K * dist cfg.T cfg.Q * dist cfg.T cfg.E =
      dist cfg.T cfg.L * dist cfg.T cfg.S * dist cfg.T cfg.E := by
    linear_combination (dist cfg.T cfg.K) * hr1 - (dist cfg.T cfg.S) * hr2
  exact mul_right_cancel₀ hTE h1

/-- `TK · TD = TL · TC`. -/
theorem dist_TK_mul_TD : dist cfg.T cfg.K * dist cfg.T cfg.D =
    dist cfg.T cfg.L * dist cfg.T cfg.C := by
  have hr2 := cfg.dist_TL_mul_TE
  rw [cfg.dist_TB_eq_TD, ← cfg.dist_TC_eq_TE] at hr2
  exact hr2.symm

/-! ### A vector version of the area-form sign lemma -/

theorem sign_oangle_eq_sign_areaForm_vec (x y : EuclideanSpace ℝ (Fin 2)) :
    (positiveOrientation.oangle x y).sign = SignType.sign (positiveOrientation.areaForm x y) := by
  have him : (positiveOrientation.kahler x y).im = positiveOrientation.areaForm x y := by
    simp [Orientation.kahler_apply_apply]
  have e : positiveOrientation.oangle x y =
      ((Complex.arg (positiveOrientation.kahler x y) : ℝ) : Real.Angle) := rfl
  rw [e, Real.Angle.sign, Real.Angle.sin_coe, Complex.sin_arg, him]
  by_cases ha : positiveOrientation.areaForm x y = 0
  · rw [ha, zero_div]
  · have hz : positiveOrientation.kahler x y ≠ 0 := by
      intro hzc
      rw [hzc, Complex.zero_im] at him
      exact ha him.symm
    have hn : 0 < ‖positiveOrientation.kahler x y‖ := norm_pos_iff.mpr hz
    rcases lt_or_gt_of_ne ha with hlt | hgt
    · rw [sign_eq_neg_one_iff.mpr hlt,
        sign_eq_neg_one_iff.mpr (div_neg_of_neg_of_pos hlt hn)]
    · rw [sign_eq_one_iff.mpr hgt, sign_eq_one_iff.mpr (div_pos hgt hn)]

/-- Dropping a component parallel to the first leg does not change the sign of an
oriented angle. -/
theorem oangle_sign_eq_of_vadd_right {x y : EuclideanSpace ℝ (Fin 2)} (c : ℝ) :
    (positiveOrientation.oangle x (y + c • x)).sign = (positiveOrientation.oangle x y).sign := by
  rw [sign_oangle_eq_sign_areaForm_vec, sign_oangle_eq_sign_areaForm_vec, map_add, map_smul,
    smul_eq_mul, positiveOrientation.areaForm_apply_self, mul_zero, add_zero]

/-! ### A batch of sign lemmas -/

theorem sign_ACT : (∡ cfg.A cfg.C cfg.T).sign = 1 := by
  have hr : (∡ cfg.A cfg.C cfg.T).sign = (∡ cfg.C cfg.T cfg.A).sign :=
    (oangle_rotate_sign cfg.A cfg.C cfg.T).symm
  rw [hr, cfg.sign_CTA]

theorem sign_CAE : (∡ cfg.C cfg.A cfg.E).sign = -1 := by
  rw [(oangle_swap₁₃_sign cfg.E cfg.A cfg.C).symm,
    sign_eq_one_of_oangle_pos (cfg.hconv_EA cfg.C (by simp : cfg.C ∈ ({cfg.B, cfg.C, cfg.D} : Set Pt)))]

theorem sign_BAC : (∡ cfg.B cfg.A cfg.C).sign = -1 := by
  rw [(oangle_swap₁₃_sign cfg.C cfg.A cfg.B).symm, oangle_rotate_sign cfg.B cfg.C cfg.A,
    sign_eq_one_of_oangle_pos (cfg.hconv_BC cfg.A (by simp : cfg.A ∈ ({cfg.D, cfg.E, cfg.A} : Set Pt)))]

theorem sign_BAE : (∡ cfg.B cfg.A cfg.E).sign = -1 := by
  rw [(oangle_swap₁₃_sign cfg.E cfg.A cfg.B).symm, sign_eq_one_of_oangle_pos cfg.oangle_EAB_pos]

theorem sign_CAD : (∡ cfg.C cfg.A cfg.D).sign = -1 := by
  rw [(oangle_swap₁₃_sign cfg.D cfg.A cfg.C).symm, ← oangle_rotate_sign cfg.D cfg.A cfg.C,
    ← oangle_rotate_sign cfg.A cfg.C cfg.D,
    sign_eq_one_of_oangle_pos (cfg.hconv_CD cfg.A (by simp : cfg.A ∈ ({cfg.E, cfg.A, cfg.B} : Set Pt)))]

theorem sign_DAE : (∡ cfg.D cfg.A cfg.E).sign = -1 := by
  rw [(oangle_swap₁₃_sign cfg.E cfg.A cfg.D).symm,
    sign_eq_one_of_oangle_pos (cfg.hconv_EA cfg.D (by simp : cfg.D ∈ ({cfg.B, cfg.C, cfg.D} : Set Pt)))]

theorem sign_CAT : (∡ cfg.C cfg.A cfg.T).sign = -1 := by
  rw [(oangle_swap₁₃_sign cfg.T cfg.A cfg.C).symm, ← oangle_rotate_sign cfg.T cfg.A cfg.C, cfg.sign_ACT]

theorem sign_TAE : (∡ cfg.T cfg.A cfg.E).sign = -1 := by
  rw [(oangle_swap₁₃_sign cfg.E cfg.A cfg.T).symm, sign_eq_one_of_oangle_pos cfg.oangle_EAT_pos]

theorem sign_ATB : (∡ cfg.A cfg.T cfg.B).sign = -1 := by
  rw [← oangle_rotate_sign cfg.A cfg.T cfg.B, (oangle_swap₁₃_sign cfg.A cfg.B cfg.T).symm, cfg.sign_ABT]

theorem sign_ATE : (∡ cfg.A cfg.T cfg.E).sign = 1 := by
  have h : (∡ cfg.A cfg.T cfg.E).sign = -(∡ cfg.E cfg.T cfg.A).sign :=
    (oangle_swap₁₃_sign _ _ _).symm
  rw [h, ← oangle_rotate_sign cfg.E cfg.T cfg.A, cfg.sign_TAE, neg_neg]

theorem sign_ACD : (∡ cfg.A cfg.C cfg.D).sign = 1 := by
  rw [← oangle_rotate_sign cfg.A cfg.C cfg.D,
    sign_eq_one_of_oangle_pos (cfg.hconv_CD cfg.A (by simp : cfg.A ∈ ({cfg.E, cfg.A, cfg.B} : Set Pt)))]

theorem sign_ADE : (∡ cfg.A cfg.D cfg.E).sign = 1 := by
  rw [← oangle_rotate_sign cfg.A cfg.D cfg.E,
    sign_eq_one_of_oangle_pos (cfg.hconv_DE cfg.A (by simp : cfg.A ∈ ({cfg.A, cfg.B, cfg.C} : Set Pt)))]

theorem sign_DAT : (∡ cfg.D cfg.A cfg.T).sign = 1 := by
  have h : (∡ cfg.A cfg.T cfg.D).sign = -(∡ cfg.D cfg.T cfg.A).sign :=
    (oangle_swap₁₃_sign _ _ _).symm
  rw [← oangle_rotate_sign cfg.D cfg.A cfg.T, h, cfg.sign_DTA, neg_neg]

theorem sign_TAB : (∡ cfg.T cfg.A cfg.B).sign = 1 := by
  rw [← oangle_rotate_sign cfg.T cfg.A cfg.B, cfg.sign_ABT]

theorem sign_DAB : (∡ cfg.D cfg.A cfg.B).sign = 1 := by
  rw [← oangle_rotate_sign cfg.D cfg.A cfg.B,
    sign_eq_one_of_oangle_pos (cfg.hconv_AB cfg.D (by simp : cfg.D ∈ ({cfg.C, cfg.D, cfg.E} : Set Pt)))]

theorem sign_CBT : (∡ cfg.C cfg.B cfg.T).sign = -1 := by
  rw [(oangle_swap₁₃_sign cfg.T cfg.B cfg.C).symm, ← oangle_rotate_sign cfg.T cfg.B cfg.C,
    sign_eq_one_of_oangle_pos cfg.oangle_BCT_pos]

theorem sign_TBA : (∡ cfg.T cfg.B cfg.A).sign = -1 := by
  rw [(oangle_swap₁₃_sign cfg.A cfg.B cfg.T).symm, cfg.sign_ABT]

theorem sign_CBA : (∡ cfg.C cfg.B cfg.A).sign = -1 := by
  rw [(oangle_swap₁₃_sign cfg.A cfg.B cfg.C).symm, sign_eq_one_of_oangle_pos cfg.oangle_ABC_pos]

theorem sign_TDE : (∡ cfg.T cfg.D cfg.E).sign = 1 := by
  rw [← oangle_rotate_sign cfg.T cfg.D cfg.E, sign_eq_one_of_oangle_pos cfg.oangle_DET_pos]

/-! ### Fan relations at the pentagon's vertices -/

theorem fan_BCT : ∠ cfg.B cfg.C cfg.A + ∠ cfg.A cfg.C cfg.T = ∠ cfg.B cfg.C cfg.T :=
  angle_add_angle_eq_angle_of_sign_eq_one cfg.B_ne_C cfg.A_ne_C cfg.C_ne_T.symm
    (sign_eq_one_of_oangle_pos (cfg.hconv_BC cfg.A (by simp : cfg.A ∈ ({cfg.D, cfg.E, cfg.A} : Set Pt))))
    cfg.sign_ACT (sign_eq_one_of_oangle_pos cfg.oangle_BCT_pos)

theorem fan_BCD : ∠ cfg.B cfg.C cfg.T + ∠ cfg.T cfg.C cfg.D = ∠ cfg.B cfg.C cfg.D :=
  angle_add_angle_eq_angle_of_sign_eq_one cfg.B_ne_C cfg.C_ne_T.symm cfg.C_ne_D.symm
    (sign_eq_one_of_oangle_pos cfg.oangle_BCT_pos)
    (by rw [← oangle_rotate_sign cfg.T cfg.C cfg.D, sign_eq_one_of_oangle_pos cfg.oangle_CDT_pos])
    (sign_eq_one_of_oangle_pos cfg.oangle_BCD_pos)

theorem fan_ACD : ∠ cfg.B cfg.C cfg.A + ∠ cfg.A cfg.C cfg.D = ∠ cfg.B cfg.C cfg.D :=
  angle_add_angle_eq_angle_of_sign_eq_one cfg.B_ne_C cfg.A_ne_C cfg.C_ne_D.symm
    (sign_eq_one_of_oangle_pos (cfg.hconv_BC cfg.A (by simp : cfg.A ∈ ({cfg.D, cfg.E, cfg.A} : Set Pt))))
    cfg.sign_ACD (sign_eq_one_of_oangle_pos cfg.oangle_BCD_pos)

theorem fan_BAE : ∠ cfg.B cfg.A cfg.C + ∠ cfg.C cfg.A cfg.E = ∠ cfg.B cfg.A cfg.E :=
  angle_add_angle_eq_angle_of_sign_eq_neg_one cfg.A_ne_B.symm cfg.A_ne_C.symm cfg.A_ne_E.symm
    cfg.sign_BAC cfg.sign_CAE cfg.sign_BAE

theorem fan_CAE_split : ∠ cfg.C cfg.A cfg.D + ∠ cfg.D cfg.A cfg.E = ∠ cfg.C cfg.A cfg.E :=
  angle_add_angle_eq_angle_of_sign_eq_neg_one cfg.A_ne_C.symm cfg.D_ne_A cfg.A_ne_E.symm
    cfg.sign_CAD cfg.sign_DAE cfg.sign_CAE

theorem fan_TAE : ∠ cfg.T cfg.A cfg.C + ∠ cfg.T cfg.A cfg.E = ∠ cfg.C cfg.A cfg.E := by
  have s₁ : (∡ cfg.E cfg.A cfg.T).sign = 1 := by
    rw [← oangle_swap₁₃_sign cfg.T cfg.A cfg.E, cfg.sign_TAE, neg_neg]
  have s₂ : (∡ cfg.T cfg.A cfg.C).sign = 1 := by
    rw [← oangle_swap₁₃_sign cfg.C cfg.A cfg.T, cfg.sign_CAT, neg_neg]
  have s₃ : (∡ cfg.E cfg.A cfg.C).sign = 1 := by
    rw [← oangle_swap₁₃_sign cfg.C cfg.A cfg.E, cfg.sign_CAE, neg_neg]
  have h : ∠ cfg.E cfg.A cfg.T + ∠ cfg.T cfg.A cfg.C = ∠ cfg.E cfg.A cfg.C :=
    angle_add_angle_eq_angle_of_sign_eq_one cfg.A_ne_E.symm cfg.T_ne_A cfg.A_ne_C.symm s₁ s₂ s₃
  rw [angle_comm cfg.E cfg.A cfg.T, angle_comm cfg.T cfg.A cfg.C, angle_comm cfg.E cfg.A cfg.C] at h
  have hc : ∠ cfg.T cfg.A cfg.C = ∠ cfg.C cfg.A cfg.T := angle_comm _ _ _
  linarith [h, hc]

theorem fan_BAD : ∠ cfg.B cfg.A cfg.D + ∠ cfg.D cfg.A cfg.E = ∠ cfg.B cfg.A cfg.E :=
  angle_add_angle_eq_angle_of_sign_eq_neg_one cfg.A_ne_B.symm cfg.D_ne_A cfg.A_ne_E.symm
    (by rw [(oangle_swap₁₃_sign cfg.D cfg.A cfg.B).symm, cfg.sign_DAB])
    cfg.sign_DAE cfg.sign_BAE

theorem fan_CDE : ∠ cfg.C cfg.D cfg.A + ∠ cfg.A cfg.D cfg.E = ∠ cfg.C cfg.D cfg.E :=
  angle_add_angle_eq_angle_of_sign_eq_one cfg.C_ne_D cfg.D_ne_A.symm cfg.D_ne_E.symm
    (sign_eq_one_of_oangle_pos (cfg.hconv_CD cfg.A (by simp : cfg.A ∈ ({cfg.E, cfg.A, cfg.B} : Set Pt))))
    cfg.sign_ADE (sign_eq_one_of_oangle_pos cfg.oangle_CDE_pos)

theorem fan_CDT : ∠ cfg.C cfg.D cfg.T + ∠ cfg.T cfg.D cfg.E = ∠ cfg.C cfg.D cfg.E :=
  angle_add_angle_eq_angle_of_sign_eq_one cfg.C_ne_D cfg.D_ne_T.symm cfg.D_ne_E.symm
    (sign_eq_one_of_oangle_pos cfg.oangle_CDT_pos) cfg.sign_TDE
    (sign_eq_one_of_oangle_pos cfg.oangle_CDE_pos)

theorem fan_ADE_T : ∠ cfg.T cfg.D cfg.A + ∠ cfg.A cfg.D cfg.E = ∠ cfg.T cfg.D cfg.E :=
  angle_add_angle_eq_angle_of_sign_eq_one cfg.D_ne_T.symm cfg.D_ne_A.symm cfg.D_ne_E.symm
    (by rw [← oangle_rotate_sign cfg.T cfg.D cfg.A, cfg.sign_DAT])
    cfg.sign_ADE cfg.sign_TDE

theorem fan_DET : ∠ cfg.D cfg.E cfg.T + ∠ cfg.T cfg.E cfg.A = ∠ cfg.D cfg.E cfg.A :=
  angle_add_angle_eq_angle_of_sign_eq_one cfg.D_ne_E cfg.T_ne_E cfg.A_ne_E
    (sign_eq_one_of_oangle_pos cfg.oangle_DET_pos) cfg.sign_TEA
    (sign_eq_one_of_oangle_pos cfg.oangle_DEA_pos)

theorem fan_CBA : ∠ cfg.C cfg.B cfg.T + ∠ cfg.T cfg.B cfg.A = ∠ cfg.C cfg.B cfg.A :=
  angle_add_angle_eq_angle_of_sign_eq_neg_one cfg.B_ne_C.symm cfg.T_ne_B cfg.A_ne_B
    cfg.sign_CBT cfg.sign_TBA cfg.sign_CBA

/-! ### Triangle angle sums -/

theorem tri_ABC : ∠ cfg.A cfg.B cfg.C + ∠ cfg.B cfg.C cfg.A + ∠ cfg.C cfg.A cfg.B = Real.pi :=
  angle_add_angle_add_angle_eq_pi cfg.C cfg.A_ne_B.symm

theorem tri_ACD : ∠ cfg.A cfg.C cfg.D + ∠ cfg.C cfg.D cfg.A + ∠ cfg.D cfg.A cfg.C = Real.pi :=
  angle_add_angle_add_angle_eq_pi cfg.D cfg.A_ne_C.symm

theorem tri_ADE : ∠ cfg.A cfg.D cfg.E + ∠ cfg.D cfg.E cfg.A + ∠ cfg.E cfg.A cfg.D = Real.pi :=
  angle_add_angle_add_angle_eq_pi cfg.E cfg.D_ne_A

theorem tri_ACT : ∠ cfg.C cfg.A cfg.T + ∠ cfg.A cfg.T cfg.C + ∠ cfg.T cfg.C cfg.A = Real.pi :=
  angle_add_angle_add_angle_eq_pi cfg.T cfg.A_ne_C

theorem tri_BCP : ∠ cfg.B cfg.C cfg.P + ∠ cfg.C cfg.P cfg.B + ∠ cfg.P cfg.B cfg.C = Real.pi :=
  angle_add_angle_add_angle_eq_pi cfg.P cfg.B_ne_C.symm

theorem tri_DRE : ∠ cfg.D cfg.R cfg.E + ∠ cfg.R cfg.E cfg.D + ∠ cfg.E cfg.D cfg.R = Real.pi :=
  angle_add_angle_add_angle_eq_pi cfg.E cfg.R_ne_D

/-- The sum of the interior angles of the pentagon is `3π`. -/
theorem pentagon_sum : ∠ cfg.A cfg.B cfg.C + ∠ cfg.B cfg.C cfg.D + ∠ cfg.C cfg.D cfg.E +
    ∠ cfg.D cfg.E cfg.A + ∠ cfg.B cfg.A cfg.E = 3 * Real.pi := by
  have h1 := cfg.tri_ABC
  have h2 := cfg.tri_ACD
  have h3 := cfg.tri_ADE
  have h4 := cfg.fan_ACD
  have h5 := cfg.fan_BAE
  have h6 := cfg.fan_CAE_split
  have h7 := cfg.fan_CDE
  have hc1 : ∠ cfg.C cfg.A cfg.B = ∠ cfg.B cfg.A cfg.C := angle_comm _ _ _
  have hc2 : ∠ cfg.E cfg.A cfg.D = ∠ cfg.D cfg.A cfg.E := angle_comm _ _ _
  have hc3 : ∠ cfg.D cfg.A cfg.C = ∠ cfg.C cfg.A cfg.D := angle_comm _ _ _
  linarith [h1, h2, h3, h4, h5, h6, h7, hc1, hc2, hc3]

/-- `∠RDE = π − ∠CDE` (since `R` is beyond `D` from `C`). -/
theorem angle_RDE : ∠ cfg.R cfg.D cfg.E = Real.pi - ∠ cfg.C cfg.D cfg.E := by
  obtain ⟨t, ht, htv⟩ := cfg.R_pos
  show InnerProductGeometry.angle _ _ = Real.pi - InnerProductGeometry.angle _ _
  rw [htv, InnerProductGeometry.angle_smul_left_of_pos _ _ ht,
    ← neg_vsub_eq_vsub_rev cfg.C cfg.D, InnerProductGeometry.angle_neg_left]

/-- `∠DER = π − ∠DEA` (since `R` is beyond `E` from `A`). -/
theorem angle_DER : ∠ cfg.D cfg.E cfg.R = Real.pi - ∠ cfg.D cfg.E cfg.A := by
  have h₂ : SameRay ℝ (cfg.E -ᵥ cfg.R) (cfg.A -ᵥ cfg.E) := cfg.sbtw_REA.wbtw.sameRay_vsub
  obtain ⟨r, hr, hvr⟩ := h₂.exists_pos_left (vsub_ne_zero.mpr cfg.R_ne_E.symm)
    (vsub_ne_zero.mpr cfg.A_ne_E)
  show InnerProductGeometry.angle _ _ = Real.pi - InnerProductGeometry.angle _ _
  rw [← neg_vsub_eq_vsub_rev cfg.E cfg.R, InnerProductGeometry.angle_neg_right, ← hvr,
    InnerProductGeometry.angle_smul_right_of_pos _ _ hr]

/-- The lines `DC` and `EA` meet on the far side, forcing `∠CDE + ∠DEA > π`. -/
theorem angle_CDE_add_DEA_gt : Real.pi < ∠ cfg.C cfg.D cfg.E + ∠ cfg.D cfg.E cfg.A := by
  have hnc : ¬Collinear ℝ ({cfg.D, cfg.R, cfg.E} : Set Pt) := by
    intro hcol
    apply cfg.not_collinear_AED
    have hiff : Collinear ℝ (insert cfg.A {cfg.D, cfg.R, cfg.E}) ↔
        Collinear ℝ ({cfg.A, cfg.R, cfg.E} : Set Pt) :=
      hcol.collinear_insert_iff_of_ne (by simp : cfg.R ∈ ({cfg.D, cfg.R, cfg.E} : Set Pt))
        (by simp : cfg.E ∈ ({cfg.D, cfg.R, cfg.E} : Set Pt)) cfg.R_ne_E
    have h4 : Collinear ℝ (insert cfg.A {cfg.D, cfg.R, cfg.E}) :=
      hiff.2 (collinear_swap cfg.collinear_AER)
    apply h4.subset
    intro x hx
    simp at hx
    rcases hx with rfl | rfl | rfl <;> simp
  have hpos : 0 < ∠ cfg.D cfg.R cfg.E := angle_pos_of_not_collinear hnc
  have hsum := cfg.tri_DRE
  have hRDE := cfg.angle_RDE
  have hDER := cfg.angle_DER
  have hc1 : ∠ cfg.E cfg.D cfg.R = ∠ cfg.R cfg.D cfg.E := angle_comm _ _ _
  have hc2 : ∠ cfg.R cfg.E cfg.D = ∠ cfg.D cfg.E cfg.R := angle_comm _ _ _
  linarith [hpos, hsum, hRDE, hDER, hc1, hc2]

/-- The key Euclid inequality for `K`'s position: `∠TCA + ∠CAE < π`. -/
theorem ineq_TCA_CAE : ∠ cfg.T cfg.C cfg.A + ∠ cfg.C cfg.A cfg.E < Real.pi := by
  have h1 := cfg.fan_BCT
  have h2 := cfg.fan_BAE
  have h3 := cfg.tri_ABC
  have h4 := cfg.fan_BCD
  have h5 := cfg.pentagon_sum
  have h6 := cfg.angle_CDE_add_DEA_gt
  have hpos : 0 < ∠ cfg.T cfg.C cfg.D := angle_pos_of_not_collinear (by
    intro hcol
    apply cfg.not_collinear_CDT
    exact collinear_rotate hcol)
  have hcomm1 : ∠ cfg.T cfg.C cfg.A = ∠ cfg.A cfg.C cfg.T := angle_comm _ _ _
  have hcomm2 : ∠ cfg.C cfg.A cfg.B = ∠ cfg.B cfg.A cfg.C := angle_comm _ _ _
  linarith [h1, h2, h3, h4, h5, h6, hpos, hcomm1, hcomm2]

/-- The sign of `∡ C T U` where `U` is `T` shifted by the vector `E −ᵥ A`; it records
that lines `CT` and `AE` meet on the `E`-side of `A`. -/
theorem sign_CTU : (∡ cfg.C cfg.T ((cfg.E -ᵥ cfg.A) +ᵥ cfg.T)).sign = -1 := by
  set U := (cfg.E -ᵥ cfg.A) +ᵥ cfg.T with hU
  have hUT : U -ᵥ cfg.T = cfg.E -ᵥ cfg.A := by rw [hU, vadd_vsub]
  have hU' : U ≠ cfg.T := by
    intro h
    apply cfg.A_ne_E
    have h1 : cfg.E -ᵥ cfg.A = 0 := by rw [← hUT, h, vsub_self]
    exact (vsub_eq_zero_iff_eq.mp h1).symm
  have hsATU : (∡ cfg.A cfg.T U).sign = 1 := by
    have hsub : cfg.E -ᵥ cfg.A = (cfg.E -ᵥ cfg.T) + (-1 : ℝ) • (cfg.A -ᵥ cfg.T) := by
      rw [neg_one_smul, ← vsub_sub_vsub_cancel_right cfg.E cfg.A cfg.T, sub_eq_add_neg]
    show (positiveOrientation.oangle (cfg.A -ᵥ cfg.T) (U -ᵥ cfg.T)).sign = 1
    rw [hUT, hsub, oangle_sign_eq_of_vadd_right]
    exact cfg.sign_ATE
  have hadd : ∡ cfg.C cfg.T cfg.A + ∡ cfg.A cfg.T U = ∡ cfg.C cfg.T U :=
    oangle_add cfg.C_ne_T cfg.T_ne_A.symm hU'
  have hATU : ∠ cfg.A cfg.T U = Real.pi - ∠ cfg.T cfg.A cfg.E := by
    show InnerProductGeometry.angle _ _ = Real.pi - InnerProductGeometry.angle _ _
    rw [hUT, ← neg_vsub_eq_vsub_rev cfg.T cfg.A, InnerProductGeometry.angle_neg_left]
  have hgt : Real.pi < ∠ cfg.C cfg.T cfg.A + ∠ cfg.A cfg.T U := by
    have hsum := cfg.tri_ACT
    have hfan := cfg.fan_TAE
    have hineq := cfg.ineq_TCA_CAE
    have hcomm1 : ∠ cfg.A cfg.T cfg.C = ∠ cfg.C cfg.T cfg.A := angle_comm _ _ _
    have hcomm2 : ∠ cfg.C cfg.A cfg.T = ∠ cfg.T cfg.A cfg.C := angle_comm _ _ _
    have hcomm3 : ∠ cfg.T cfg.C cfg.A = ∠ cfg.A cfg.C cfg.T := angle_comm _ _ _
    linarith [hATU, hsum, hfan, hineq, hcomm1, hcomm2, hcomm3]
  have ht : (∡ cfg.C cfg.T U).toReal = ∠ cfg.C cfg.T cfg.A + ∠ cfg.A cfg.T U - 2 * Real.pi := by
    have h2 : ∡ cfg.C cfg.T U = ((∠ cfg.C cfg.T cfg.A + ∠ cfg.A cfg.T U : ℝ) : Real.Angle) := by
      rw [← hadd, oangle_eq_angle_of_sign_eq_one cfg.sign_CTA,
        oangle_eq_angle_of_sign_eq_one hsATU, ← Real.Angle.coe_add]
    rw [h2]
    have hper : ((∠ cfg.C cfg.T cfg.A + ∠ cfg.A cfg.T U - 2 * Real.pi : ℝ) : Real.Angle) =
        ((∠ cfg.C cfg.T cfg.A + ∠ cfg.A cfg.T U : ℝ) : Real.Angle) := by
      have h0 : ((2 * Real.pi : ℝ) : Real.Angle) = 0 := Real.Angle.coe_two_pi
      have h1 := Real.Angle.coe_add (∠ cfg.C cfg.T cfg.A + ∠ cfg.A cfg.T U - 2 * Real.pi)
        (2 * Real.pi)
      rw [sub_add_cancel, h0, add_zero] at h1
      exact h1.symm
    have hb1 : -Real.pi < ∠ cfg.C cfg.T cfg.A + ∠ cfg.A cfg.T U - 2 * Real.pi := by
      linarith [hgt]
    have hb2 : ∠ cfg.C cfg.T cfg.A + ∠ cfg.A cfg.T U - 2 * Real.pi ≤ Real.pi := by
      linarith [hgt, angle_le_pi (cfg.C) (cfg.T) (cfg.A), angle_le_pi (cfg.A) (cfg.T) U]
    rw [← hper, Real.Angle.toReal_coe_eq_self_iff.mpr ⟨hb1, hb2⟩]
  have hI1 : (∡ cfg.C cfg.T cfg.A).toReal ∈ Set.Ioo 0 Real.pi := by
    rw [Real.Angle.toReal_mem_Ioo_iff_sign_pos, cfg.sign_CTA]
  have hI1' : (∡ cfg.C cfg.T cfg.A).toReal = ∠ cfg.C cfg.T cfg.A := by
    rw [oangle_eq_angle_of_sign_eq_one cfg.sign_CTA, Real.Angle.toReal_coe_eq_self_iff]
    exact ⟨by linarith [Real.pi_pos, angle_nonneg cfg.C cfg.T cfg.A], angle_le_pi _ _ _⟩
  rw [hI1'] at hI1
  have hI2 : (∡ cfg.A cfg.T U).toReal ∈ Set.Ioo 0 Real.pi := by
    rw [Real.Angle.toReal_mem_Ioo_iff_sign_pos, hsATU]
  have hI2' : (∡ cfg.A cfg.T U).toReal = ∠ cfg.A cfg.T U := by
    rw [oangle_eq_angle_of_sign_eq_one hsATU, Real.Angle.toReal_coe_eq_self_iff]
    exact ⟨by linarith [Real.pi_pos, angle_nonneg cfg.A cfg.T U], angle_le_pi _ _ _⟩
  rw [hI2'] at hI2
  have hneg : (∡ cfg.C cfg.T U).toReal < 0 := by rw [ht]; linarith [hI1.2, hI2.2]
  exact Real.Angle.toReal_neg_iff_sign_neg.mp hneg

/-- Decomposition of `T −ᵥ A` in the basis `(C −ᵥ A, E −ᵥ A)`, with positive coefficients
and `α < 1` (this is what places `K` beyond `T` from `C`). -/
theorem T_decomp : ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ α < 1 ∧
    cfg.T -ᵥ cfg.A = α • (cfg.C -ᵥ cfg.A) + β • (cfg.E -ᵥ cfg.A) := by
  set c := cfg.C -ᵥ cfg.A
  set e := cfg.E -ᵥ cfg.A
  have hce : positiveOrientation.areaForm c e ≠ 0 := by
    have h : (∡ cfg.C cfg.A cfg.E).sign = -1 := cfg.sign_CAE
    rw [sign_oangle_eq_sign_areaForm, sign_eq_neg_one_iff] at h
    exact h.ne
  set α := positiveOrientation.areaForm (cfg.T -ᵥ cfg.A) e / positiveOrientation.areaForm c e
    with hα_def
  set β := positiveOrientation.areaForm c (cfg.T -ᵥ cfg.A) / positiveOrientation.areaForm c e
    with hβ_def
  have hvec : cfg.T -ᵥ cfg.A = α • c + β • e := by
    have hinj : ∀ w : EuclideanSpace ℝ (Fin 2),
        positiveOrientation.areaForm w e = 0 → positiveOrientation.areaForm w c = 0 → w = 0 := by
      intro w hwe hwc
      by_contra hw
      have hse : (positiveOrientation.oangle w e).sign = 0 := by
        rw [sign_oangle_eq_sign_areaForm_vec, hwe]
        simp
      have hsc : (positiveOrientation.oangle w c).sign = 0 := by
        rw [sign_oangle_eq_sign_areaForm_vec, hwc]
        simp
      have he0 : e ≠ 0 := by
        intro he
        apply hce
        rw [he]
        simp
      have hc0 : c ≠ 0 := by
        intro hc
        apply hce
        rw [hc]
        simp
      rw [Real.Angle.sign_eq_zero_iff] at hse hsc
      have hq : ∃ q : ℝ, e = q • w := by
        rcases hse with hse | hse
        · obtain ⟨r, hr, hvr⟩ :=
            (positiveOrientation.oangle_eq_zero_iff_sameRay.mp hse).exists_pos_left hw he0
          exact ⟨r, hvr.symm⟩
        · obtain ⟨r, hr, hvr⟩ :=
            (positiveOrientation.oangle_eq_pi_iff_sameRay_neg.mp hse).2.2.exists_pos_left hw
              (neg_ne_zero.mpr he0)
          exact ⟨-r, by rw [neg_smul, hvr, neg_neg]⟩
      have hq' : ∃ q' : ℝ, c = q' • w := by
        rcases hsc with hsc | hsc
        · obtain ⟨r, hr, hvr⟩ :=
            (positiveOrientation.oangle_eq_zero_iff_sameRay.mp hsc).exists_pos_left hw hc0
          exact ⟨r, hvr.symm⟩
        · obtain ⟨r, hr, hvr⟩ :=
            (positiveOrientation.oangle_eq_pi_iff_sameRay_neg.mp hsc).2.2.exists_pos_left hw
              (neg_ne_zero.mpr hc0)
          exact ⟨-r, by rw [neg_smul, hvr, neg_neg]⟩
      obtain ⟨q, hq⟩ := hq
      obtain ⟨q', hq'⟩ := hq'
      apply hce
      simp only [hq, hq', map_smul, LinearMap.smul_apply,
        positiveOrientation.areaForm_apply_self, smul_zero]
    have h1 : positiveOrientation.areaForm (cfg.T -ᵥ cfg.A - (α • c + β • e)) e = 0 := by
      simp only [map_sub, map_add, map_smul, LinearMap.sub_apply, LinearMap.add_apply,
        LinearMap.smul_apply, positiveOrientation.areaForm_apply_self, smul_zero, add_zero,
        smul_eq_mul, mul_zero]
      have hα : positiveOrientation.areaForm (α • c) e =
          positiveOrientation.areaForm (cfg.T -ᵥ cfg.A) e := by
        rw [map_smul, LinearMap.smul_apply, smul_eq_mul, hα_def, div_mul_cancel₀ _ hce]
      rw [← hα, map_smul, LinearMap.smul_apply, smul_eq_mul, sub_self]
    have h2 : positiveOrientation.areaForm (cfg.T -ᵥ cfg.A - (α • c + β • e)) c = 0 := by
      simp only [map_sub, map_add, map_smul, LinearMap.sub_apply, LinearMap.add_apply,
        LinearMap.smul_apply, positiveOrientation.areaForm_apply_self, smul_zero, add_zero,
        zero_add, smul_eq_mul, mul_zero]
      have hβ : positiveOrientation.areaForm (β • e) c =
          positiveOrientation.areaForm (cfg.T -ᵥ cfg.A) c := by
        rw [map_smul, LinearMap.smul_apply, smul_eq_mul, hβ_def,
          positiveOrientation.areaForm_swap e c, mul_neg, div_mul_cancel₀ _ hce,
          positiveOrientation.areaForm_swap, neg_neg]
      rw [← hβ, map_smul, LinearMap.smul_apply, smul_eq_mul, sub_self]
    have h3 := hinj _ h1 h2
    exact sub_eq_zero.mp h3
  have hα_pos : 0 < α := by
    rw [hα_def]
    apply div_pos_of_neg_of_neg
    · have h : (∡ cfg.T cfg.A cfg.E).sign = -1 := cfg.sign_TAE
      rw [sign_oangle_eq_sign_areaForm, sign_eq_neg_one_iff] at h
      exact h
    · have h : (∡ cfg.C cfg.A cfg.E).sign = -1 := cfg.sign_CAE
      rw [sign_oangle_eq_sign_areaForm, sign_eq_neg_one_iff] at h
      exact h
  have hβ_pos : 0 < β := by
    rw [hβ_def]
    apply div_pos_of_neg_of_neg
    · have h : (∡ cfg.C cfg.A cfg.T).sign = -1 := cfg.sign_CAT
      rw [sign_oangle_eq_sign_areaForm, sign_eq_neg_one_iff] at h
      exact h
    · have h : (∡ cfg.C cfg.A cfg.E).sign = -1 := cfg.sign_CAE
      rw [sign_oangle_eq_sign_areaForm, sign_eq_neg_one_iff] at h
      exact h
  refine ⟨α, β, hα_pos, hβ_pos, ?_, hvec⟩
  -- `α < 1` from `σ(oangle(e, T−C)) = −1` (i.e. `sign_CTU`).
  have hEc : (positiveOrientation.oangle e c).sign = 1 := by
    show (∡ cfg.E cfg.A cfg.C).sign = 1
    exact sign_eq_one_of_oangle_pos (cfg.hconv_EA cfg.C (by simp : cfg.C ∈ ({cfg.B, cfg.C, cfg.D} : Set Pt)))
  have hs : (positiveOrientation.oangle e (cfg.T -ᵥ cfg.C)).sign = -1 := by
    have hrev : positiveOrientation.oangle e (cfg.T -ᵥ cfg.C) =
        -positiveOrientation.oangle (cfg.T -ᵥ cfg.C) e := positiveOrientation.oangle_rev _ _
    have hneg : positiveOrientation.oangle (cfg.T -ᵥ cfg.C) e =
        positiveOrientation.oangle (cfg.C -ᵥ cfg.T) e + ↑Real.pi := by
      rw [← neg_vsub_eq_vsub_rev cfg.C cfg.T, positiveOrientation.oangle_neg_left
        (vsub_ne_zero.mpr cfg.C_ne_T) (vsub_ne_zero.mpr cfg.A_ne_E.symm)]
    have h4 : (∡ cfg.C cfg.T ((cfg.E -ᵥ cfg.A) +ᵥ cfg.T)).sign = -1 := cfg.sign_CTU
    have h5 : positiveOrientation.oangle (cfg.C -ᵥ cfg.T) e =
        ∡ cfg.C cfg.T ((cfg.E -ᵥ cfg.A) +ᵥ cfg.T) := by
      show positiveOrientation.oangle (cfg.C -ᵥ cfg.T) e =
        positiveOrientation.oangle (cfg.C -ᵥ cfg.T) (((cfg.E -ᵥ cfg.A) +ᵥ cfg.T) -ᵥ cfg.T)
      rw [vadd_vsub]
    rw [hrev, hneg, h5, Real.Angle.sign_neg, Real.Angle.sign_add_pi, h4, neg_neg]
  have hvec2 : cfg.T -ᵥ cfg.C = (α - 1) • c + β • e := by
    have h : cfg.T -ᵥ cfg.C = (cfg.T -ᵥ cfg.A) - (cfg.C -ᵥ cfg.A) :=
      vsub_sub_vsub_cancel_right cfg.T cfg.C cfg.A |>.symm
    rw [h, hvec]
    module
  have hdrop : (positiveOrientation.oangle e ((α - 1) • c + β • e)).sign =
      (positiveOrientation.oangle e ((α - 1) • c)).sign :=
    oangle_sign_eq_of_vadd_right β
  rw [hvec2, hdrop] at hs
  by_contra hα_ge
  push Not at hα_ge
  rcases eq_or_lt_of_le hα_ge with heq1 | hgt1
  · rw [heq1, sub_self, zero_smul] at hs
    have h7 : (positiveOrientation.oangle e 0).sign = 0 := by
      rw [sign_oangle_eq_sign_areaForm_vec, map_zero]
      simp
    rw [h7] at hs
    simp at hs
  · have hgt : (positiveOrientation.oangle e ((α - 1) • c)).sign = 1 := by
      rw [positiveOrientation.oangle_smul_right_of_pos _ _ (sub_pos.mpr hgt1)]
      exact hEc
    rw [hgt] at hs
    simp at hs

/-- `K` is on the ray from `T` opposite to `C` (POS3). -/
theorem sameRay_KT : SameRay ℝ (cfg.K -ᵥ cfg.T) (cfg.T -ᵥ cfg.C) := by
  have hKT : cfg.K ≠ cfg.T := by
    intro h
    apply cfg.not_collinear_EAT
    rw [← h]
    exact collinear_swap (collinear_rotate cfg.K_on_AE)
  obtain ⟨α, β, hα, hβ, hα1, hvec⟩ := cfg.T_decomp
  -- `K −ᵥ A = s • (E −ᵥ A)` for some `s`.
  have hK1 : cfg.K ∈ affineSpan ℝ ({cfg.A, cfg.E} : Set Pt) := by
    have h := cfg.K_on_AE.affineSpan_eq_of_ne (Set.mem_insert _ _)
      (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) cfg.A_ne_E
    rw [h]
    apply mem_affineSpan
    simp
  have hA : cfg.A ∈ affineSpan ℝ ({cfg.A, cfg.E} : Set Pt) := by
    apply mem_affineSpan
    simp
  have hv : cfg.K -ᵥ cfg.A ∈ Submodule.span ℝ {cfg.E -ᵥ cfg.A} := by
    have h2 := AffineSubspace.vsub_mem_direction hK1 hA
    rw [direction_affineSpan, vectorSpan_pair_rev] at h2
    exact h2
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hv
  -- `K −ᵥ C = λ • (T −ᵥ C)` for some `λ`.
  have hK2 : cfg.K ∈ affineSpan ℝ ({cfg.C, cfg.T} : Set Pt) := by
    have h := cfg.K_on_CT.affineSpan_eq_of_ne (Set.mem_insert _ _)
      (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) cfg.C_ne_T
    rw [h]
    apply mem_affineSpan
    simp
  have hC : cfg.C ∈ affineSpan ℝ ({cfg.C, cfg.T} : Set Pt) := by
    apply mem_affineSpan
    simp
  have hv2 : cfg.K -ᵥ cfg.C ∈ Submodule.span ℝ {cfg.T -ᵥ cfg.C} := by
    have h2 := AffineSubspace.vsub_mem_direction hK2 hC
    rw [direction_affineSpan, vectorSpan_pair_rev] at h2
    exact h2
  obtain ⟨l, hl⟩ := Submodule.mem_span_singleton.mp hv2
  -- the two vector expressions for `K −ᵥ T`.
  have hXY : (cfg.A -ᵥ cfg.T) + s • (cfg.E -ᵥ cfg.A) = (cfg.C -ᵥ cfg.T) + l • (cfg.T -ᵥ cfg.C) := by
    have h2 : cfg.K -ᵥ cfg.T = (cfg.A -ᵥ cfg.T) + s • (cfg.E -ᵥ cfg.A) := by
      have h4 : cfg.K -ᵥ cfg.T = (cfg.A -ᵥ cfg.T) + (cfg.K -ᵥ cfg.A) := by
        rw [add_comm, vsub_add_vsub_cancel]
      rw [h4, hs]
    have h3 : cfg.K -ᵥ cfg.T = (cfg.C -ᵥ cfg.T) + l • (cfg.T -ᵥ cfg.C) := by
      have h4 : cfg.K -ᵥ cfg.T = (cfg.C -ᵥ cfg.T) + (cfg.K -ᵥ cfg.C) := by
        rw [add_comm, vsub_add_vsub_cancel]
      rw [h4, hl]
    rw [← h2, ← h3]
  -- expand in the basis.
  set c := cfg.C -ᵥ cfg.A
  set e := cfg.E -ᵥ cfg.A
  have hce : positiveOrientation.areaForm c e ≠ 0 := by
    have h : (∡ cfg.C cfg.A cfg.E).sign = -1 := cfg.sign_CAE
    rw [sign_oangle_eq_sign_areaForm, sign_eq_neg_one_iff] at h
    exact h.ne
  have hAT : cfg.A -ᵥ cfg.T = (-α) • c + (-β) • e := by
    rw [← neg_vsub_eq_vsub_rev cfg.T cfg.A, hvec]
    module
  have hCT : cfg.C -ᵥ cfg.T = (1 - α) • c + (-β) • e := by
    have h : cfg.C -ᵥ cfg.T = (cfg.C -ᵥ cfg.A) - (cfg.T -ᵥ cfg.A) :=
      vsub_sub_vsub_cancel_right cfg.C cfg.T cfg.A |>.symm
    rw [h, hvec]
    module
  have hTC : cfg.T -ᵥ cfg.C = (α - 1) • c + β • e := by
    have h : cfg.T -ᵥ cfg.C = (cfg.T -ᵥ cfg.A) - (cfg.C -ᵥ cfg.A) :=
      vsub_sub_vsub_cancel_right cfg.T cfg.C cfg.A |>.symm
    rw [h, hvec]
    module
  -- apply the area form with `e` and with `c`.
  have he1 := congrArg (fun v => positiveOrientation.areaForm v e) hXY
  rw [hAT, hCT, hTC] at he1
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    positiveOrientation.areaForm_apply_self, mul_zero, add_zero] at he1
  have hce2 : positiveOrientation.areaForm e c ≠ 0 := by
    rw [positiveOrientation.areaForm_swap]
    exact neg_ne_zero.mpr hce
  have hc1 := congrArg (fun v => positiveOrientation.areaForm v c) hXY
  rw [hAT, hCT, hTC] at hc1
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    positiveOrientation.areaForm_apply_self, mul_zero, add_zero] at hc1
  have hce2 : positiveOrientation.areaForm e c ≠ 0 := by
    rw [positiveOrientation.areaForm_swap]
    exact neg_ne_zero.mpr hce
  -- solve the system: `l * (α - 1) = -1`, `s = β * l > 0`.
  have hl1 : l * (α - 1) = -1 := by
    have h1 : -α = (1 - α) + l * (α - 1) :=
      mul_right_cancel₀ hce (by linear_combination he1)
    linarith [h1]
  have hs_eq : s = β * l := by
    have h1 : s = l * β := mul_right_cancel₀ hce2 (by linear_combination hc1)
    rw [h1, mul_comm]
  have hs_pos : 0 < s := by
    have hl_pos : 0 < l := by
      have h1 : 0 < 1 - α := sub_pos.mpr hα1
      have h2 : l * (1 - α) = 1 := by linarith [hl1]
      nlinarith [h1, h2]
    rw [hs_eq]
    exact mul_pos hβ hl_pos
  -- hence `σ(∡ A T K) = 1`.
  have hg : 0 < positiveOrientation.areaForm (cfg.A -ᵥ cfg.T) (cfg.E -ᵥ cfg.A) := by
    have hsub : cfg.E -ᵥ cfg.A = (cfg.E -ᵥ cfg.T) + (-1 : ℝ) • (cfg.A -ᵥ cfg.T) := by
      rw [neg_one_smul, ← vsub_sub_vsub_cancel_right cfg.E cfg.A cfg.T, sub_eq_add_neg]
    have h : SignType.sign (positiveOrientation.areaForm (cfg.A -ᵥ cfg.T) (cfg.E -ᵥ cfg.T)) = 1 := by
      rw [← sign_oangle_eq_sign_areaForm_vec]
      exact cfg.sign_ATE
    rw [sign_eq_one_iff] at h
    rw [hsub, map_add, map_smul, smul_eq_mul, positiveOrientation.areaForm_apply_self,
      mul_zero, add_zero]
    exact h
  have hsign_ATK : (∡ cfg.A cfg.T cfg.K).sign = 1 := by
    have hkv : cfg.K -ᵥ cfg.T = (cfg.A -ᵥ cfg.T) + s • (cfg.E -ᵥ cfg.A) := by
      have h4 : cfg.K -ᵥ cfg.T = (cfg.A -ᵥ cfg.T) + (cfg.K -ᵥ cfg.A) := by
        rw [add_comm, vsub_add_vsub_cancel]
      rw [h4, hs]
    have h1 : (∡ cfg.A cfg.T cfg.K).sign =
        SignType.sign (positiveOrientation.areaForm (cfg.A -ᵥ cfg.T) (cfg.K -ᵥ cfg.T)) :=
      sign_oangle_eq_sign_areaForm _ _ _
    rw [h1, hkv, map_add, positiveOrientation.areaForm_apply_self, zero_add, map_smul,
      smul_eq_mul, sign_eq_one_iff.mpr (mul_pos hs_pos hg)]
  -- conclude via the ray dichotomy on line `CT`.
  have hd := sameRay_or_sameRay_neg_vsub_of_collinear cfg.C_ne_T hKT cfg.K_on_CT
  rcases hd with h | h
  · exfalso
    obtain ⟨r, hr, hvr⟩ := h.exists_pos_left (vsub_ne_zero.mpr cfg.C_ne_T)
      (vsub_ne_zero.mpr hKT)
    have h1 : (∡ cfg.A cfg.T cfg.K).sign = -1 := by
      have h2 : ∡ cfg.A cfg.T cfg.K = ∡ cfg.A cfg.T cfg.C := by
        show positiveOrientation.oangle (cfg.A -ᵥ cfg.T) (cfg.K -ᵥ cfg.T) =
          positiveOrientation.oangle (cfg.A -ᵥ cfg.T) (cfg.C -ᵥ cfg.T)
        rw [← hvr, positiveOrientation.oangle_smul_right_of_pos _ _ hr]
      have h3 : (∡ cfg.A cfg.T cfg.C).sign = -(∡ cfg.C cfg.T cfg.A).sign :=
        (oangle_swap₁₃_sign _ _ _).symm
      rw [h2, h3, cfg.sign_CTA]
    rw [h1] at hsign_ATK
    simp at hsign_ATK
  · rw [← neg_vsub_eq_vsub_rev cfg.T cfg.C, ← neg_vsub_eq_vsub_rev cfg.K cfg.T] at h
    exact (sameRay_neg_iff.mp h).symm

/-! ### POS4: `L` is on the ray from `T` opposite to `D`

This mirrors the `K`/`C` analysis (`sign_CTU`, `T_decomp`, `sameRay_KT`) on the other
side of the figure.  The key Euclid inequality is `∠ADT + ∠DAB < π`. -/

theorem tri_ADT : ∠ cfg.A cfg.D cfg.T + ∠ cfg.D cfg.T cfg.A + ∠ cfg.T cfg.A cfg.D =
    Real.pi :=
  angle_add_angle_add_angle_eq_pi cfg.T cfg.D_ne_A

theorem fan_DAT : ∠ cfg.D cfg.A cfg.T + ∠ cfg.T cfg.A cfg.B = ∠ cfg.D cfg.A cfg.B :=
  angle_add_angle_eq_angle_of_sign_eq_one cfg.D_ne_A cfg.T_ne_A cfg.A_ne_B.symm
    cfg.sign_DAT cfg.sign_TAB cfg.sign_DAB

/-- The key Euclid inequality for `L`'s position: `∠ADT + ∠DAB < π`. -/
theorem ineq_ADT_DAB : ∠ cfg.A cfg.D cfg.T + ∠ cfg.D cfg.A cfg.B < Real.pi := by
  have h1 := cfg.fan_ADE_T
  have h2 := cfg.fan_BAD
  have h3 := cfg.angle_TBC_eq_TDE
  have h4 := cfg.fan_CBA
  have h5 := cfg.angle_ABT_eq_TEA
  have h6 := cfg.pentagon_sum
  have h7 := cfg.tri_ADE
  have h8 := cfg.fan_BCD
  have h9 := cfg.fan_DET
  have h10 := cfg.angle_BCT_eq_DET
  have h11 := cfg.angle_CDE_add_DEA_gt
  have hpos : 0 < ∠ cfg.T cfg.C cfg.D := angle_pos_of_not_collinear (by
    intro hcol
    apply cfg.not_collinear_CDT
    exact collinear_rotate hcol)
  have hc1 : ∠ cfg.A cfg.D cfg.T = ∠ cfg.T cfg.D cfg.A := angle_comm _ _ _
  have hc2 : ∠ cfg.D cfg.A cfg.B = ∠ cfg.B cfg.A cfg.D := angle_comm _ _ _
  have hc3 : ∠ cfg.C cfg.B cfg.A = ∠ cfg.A cfg.B cfg.C := angle_comm _ _ _
  have hc4 : ∠ cfg.T cfg.B cfg.C = ∠ cfg.C cfg.B cfg.T := angle_comm _ _ _
  have hc5 : ∠ cfg.T cfg.B cfg.A = ∠ cfg.A cfg.B cfg.T := angle_comm _ _ _
  have hc7 : ∠ cfg.E cfg.A cfg.D = ∠ cfg.D cfg.A cfg.E := angle_comm _ _ _
  linarith [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hpos, hc1, hc2, hc3, hc4, hc5,
    hc7]

/-- The sign of `∡ U T D` where `U` is `T` shifted by the vector `B −ᵥ A`; it records
that lines `DT` and `AB` meet on the `B`-side of `A`. -/
theorem sign_UTD : (∡ ((cfg.B -ᵥ cfg.A) +ᵥ cfg.T) cfg.T cfg.D).sign = -1 := by
  set U := (cfg.B -ᵥ cfg.A) +ᵥ cfg.T with hU
  have hUT : U -ᵥ cfg.T = cfg.B -ᵥ cfg.A := by rw [hU, vadd_vsub]
  have hU' : U ≠ cfg.T := by
    intro h
    apply cfg.A_ne_B
    have h1 : cfg.B -ᵥ cfg.A = 0 := by rw [← hUT, h, vsub_self]
    exact (vsub_eq_zero_iff_eq.mp h1).symm
  have hsATU : (∡ cfg.A cfg.T U).sign = -1 := by
    have hsub : cfg.B -ᵥ cfg.A = (cfg.B -ᵥ cfg.T) + (-1 : ℝ) • (cfg.A -ᵥ cfg.T) := by
      rw [neg_one_smul, ← vsub_sub_vsub_cancel_right cfg.B cfg.A cfg.T, sub_eq_add_neg]
    show (positiveOrientation.oangle (cfg.A -ᵥ cfg.T) (U -ᵥ cfg.T)).sign = -1
    rw [hUT, hsub, oangle_sign_eq_of_vadd_right]
    exact cfg.sign_ATB
  have hsUTA : (∡ U cfg.T cfg.A).sign = 1 := by
    rw [(oangle_swap₁₃_sign cfg.A cfg.T U).symm, hsATU, neg_neg]
  have hsATD : (∡ cfg.A cfg.T cfg.D).sign = 1 := by
    rw [(oangle_swap₁₃_sign cfg.D cfg.T cfg.A).symm, cfg.sign_DTA, neg_neg]
  have hadd : ∡ U cfg.T cfg.A + ∡ cfg.A cfg.T cfg.D = ∡ U cfg.T cfg.D :=
    oangle_add hU' cfg.T_ne_A.symm cfg.D_ne_T
  have hATU : ∠ cfg.A cfg.T U = Real.pi - ∠ cfg.T cfg.A cfg.B := by
    show InnerProductGeometry.angle _ _ = Real.pi - InnerProductGeometry.angle _ _
    rw [hUT, ← neg_vsub_eq_vsub_rev cfg.T cfg.A, InnerProductGeometry.angle_neg_left]
  have hgt : Real.pi < ∠ U cfg.T cfg.A + ∠ cfg.A cfg.T cfg.D := by
    have hsum := cfg.tri_ADT
    have hfan := cfg.fan_DAT
    have hineq := cfg.ineq_ADT_DAB
    have hcomm1 : ∠ cfg.D cfg.T cfg.A = ∠ cfg.A cfg.T cfg.D := angle_comm _ _ _
    have hcomm2 : ∠ cfg.T cfg.A cfg.D = ∠ cfg.D cfg.A cfg.T := angle_comm _ _ _
    have hcomm3 : ∠ U cfg.T cfg.A = ∠ cfg.A cfg.T U := angle_comm _ _ _
    linarith [hATU, hsum, hfan, hineq, hcomm1, hcomm2, hcomm3]
  have ht : (∡ U cfg.T cfg.D).toReal = ∠ U cfg.T cfg.A + ∠ cfg.A cfg.T cfg.D -
      2 * Real.pi := by
    have h2 : ∡ U cfg.T cfg.D = ((∠ U cfg.T cfg.A + ∠ cfg.A cfg.T cfg.D : ℝ) : Real.Angle) := by
      rw [← hadd, oangle_eq_angle_of_sign_eq_one hsUTA,
        oangle_eq_angle_of_sign_eq_one hsATD, ← Real.Angle.coe_add]
    rw [h2]
    have hper : ((∠ U cfg.T cfg.A + ∠ cfg.A cfg.T cfg.D - 2 * Real.pi : ℝ) : Real.Angle) =
        ((∠ U cfg.T cfg.A + ∠ cfg.A cfg.T cfg.D : ℝ) : Real.Angle) := by
      have h0 : ((2 * Real.pi : ℝ) : Real.Angle) = 0 := Real.Angle.coe_two_pi
      have h1 := Real.Angle.coe_add (∠ U cfg.T cfg.A + ∠ cfg.A cfg.T cfg.D - 2 * Real.pi)
        (2 * Real.pi)
      rw [sub_add_cancel, h0, add_zero] at h1
      exact h1.symm
    have hb1 : -Real.pi < ∠ U cfg.T cfg.A + ∠ cfg.A cfg.T cfg.D - 2 * Real.pi := by
      linarith [hgt]
    have hb2 : ∠ U cfg.T cfg.A + ∠ cfg.A cfg.T cfg.D - 2 * Real.pi ≤ Real.pi := by
      linarith [hgt, angle_le_pi U (cfg.T) (cfg.A), angle_le_pi (cfg.A) (cfg.T) (cfg.D)]
    rw [← hper, Real.Angle.toReal_coe_eq_self_iff.mpr ⟨hb1, hb2⟩]
  have hI1 : (∡ U cfg.T cfg.A).toReal ∈ Set.Ioo 0 Real.pi := by
    rw [Real.Angle.toReal_mem_Ioo_iff_sign_pos, hsUTA]
  have hI1' : (∡ U cfg.T cfg.A).toReal = ∠ U cfg.T cfg.A := by
    rw [oangle_eq_angle_of_sign_eq_one hsUTA, Real.Angle.toReal_coe_eq_self_iff]
    exact ⟨by linarith [Real.pi_pos, angle_nonneg U cfg.T cfg.A], angle_le_pi _ _ _⟩
  rw [hI1'] at hI1
  have hI2 : (∡ cfg.A cfg.T cfg.D).toReal ∈ Set.Ioo 0 Real.pi := by
    rw [Real.Angle.toReal_mem_Ioo_iff_sign_pos, hsATD]
  have hI2' : (∡ cfg.A cfg.T cfg.D).toReal = ∠ cfg.A cfg.T cfg.D := by
    rw [oangle_eq_angle_of_sign_eq_one hsATD, Real.Angle.toReal_coe_eq_self_iff]
    exact ⟨by linarith [Real.pi_pos, angle_nonneg cfg.A cfg.T cfg.D], angle_le_pi _ _ _⟩
  rw [hI2'] at hI2
  have hneg : (∡ U cfg.T cfg.D).toReal < 0 := by rw [ht]; linarith [hI1.2, hI2.2]
  exact Real.Angle.toReal_neg_iff_sign_neg.mp hneg

/-- Decomposition of `T −ᵥ A` in the basis `(D −ᵥ A, B −ᵥ A)`, with positive coefficients
and `α < 1` (this is what places `L` beyond `T` from `D`). -/
theorem T_decomp_DT : ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ α < 1 ∧
    cfg.T -ᵥ cfg.A = α • (cfg.D -ᵥ cfg.A) + β • (cfg.B -ᵥ cfg.A) := by
  set d := cfg.D -ᵥ cfg.A
  set b := cfg.B -ᵥ cfg.A
  have hdb : positiveOrientation.areaForm d b ≠ 0 := by
    have h : (∡ cfg.D cfg.A cfg.B).sign = 1 := cfg.sign_DAB
    rw [sign_oangle_eq_sign_areaForm, sign_eq_one_iff] at h
    exact h.ne'
  set α := positiveOrientation.areaForm (cfg.T -ᵥ cfg.A) b / positiveOrientation.areaForm d b
    with hα_def
  set β := positiveOrientation.areaForm d (cfg.T -ᵥ cfg.A) / positiveOrientation.areaForm d b
    with hβ_def
  have hvec : cfg.T -ᵥ cfg.A = α • d + β • b := by
    have hinj : ∀ w : EuclideanSpace ℝ (Fin 2),
        positiveOrientation.areaForm w b = 0 → positiveOrientation.areaForm w d = 0 →
          w = 0 := by
      intro w hwb hwd
      by_contra hw
      have hsb : (positiveOrientation.oangle w b).sign = 0 := by
        rw [sign_oangle_eq_sign_areaForm_vec, hwb]
        simp
      have hsd : (positiveOrientation.oangle w d).sign = 0 := by
        rw [sign_oangle_eq_sign_areaForm_vec, hwd]
        simp
      have hb0 : b ≠ 0 := by
        intro hb
        apply hdb
        rw [hb]
        simp
      have hd0 : d ≠ 0 := by
        intro hd
        apply hdb
        rw [hd]
        simp
      rw [Real.Angle.sign_eq_zero_iff] at hsb hsd
      have hq : ∃ q : ℝ, b = q • w := by
        rcases hsb with hsb | hsb
        · obtain ⟨r, hr, hvr⟩ :=
            (positiveOrientation.oangle_eq_zero_iff_sameRay.mp hsb).exists_pos_left hw hb0
          exact ⟨r, hvr.symm⟩
        · obtain ⟨r, hr, hvr⟩ :=
            (positiveOrientation.oangle_eq_pi_iff_sameRay_neg.mp hsb).2.2.exists_pos_left hw
              (neg_ne_zero.mpr hb0)
          exact ⟨-r, by rw [neg_smul, hvr, neg_neg]⟩
      have hq' : ∃ q' : ℝ, d = q' • w := by
        rcases hsd with hsd | hsd
        · obtain ⟨r, hr, hvr⟩ :=
            (positiveOrientation.oangle_eq_zero_iff_sameRay.mp hsd).exists_pos_left hw hd0
          exact ⟨r, hvr.symm⟩
        · obtain ⟨r, hr, hvr⟩ :=
            (positiveOrientation.oangle_eq_pi_iff_sameRay_neg.mp hsd).2.2.exists_pos_left hw
              (neg_ne_zero.mpr hd0)
          exact ⟨-r, by rw [neg_smul, hvr, neg_neg]⟩
      obtain ⟨q, hq⟩ := hq
      obtain ⟨q', hq'⟩ := hq'
      apply hdb
      simp only [hq, hq', map_smul, LinearMap.smul_apply,
        positiveOrientation.areaForm_apply_self, smul_zero]
    have h1 : positiveOrientation.areaForm (cfg.T -ᵥ cfg.A - (α • d + β • b)) b = 0 := by
      simp only [map_sub, map_add, map_smul, LinearMap.sub_apply, LinearMap.add_apply,
        LinearMap.smul_apply, positiveOrientation.areaForm_apply_self, smul_zero, add_zero,
        smul_eq_mul, mul_zero]
      have hα : positiveOrientation.areaForm (α • d) b =
          positiveOrientation.areaForm (cfg.T -ᵥ cfg.A) b := by
        rw [map_smul, LinearMap.smul_apply, smul_eq_mul, hα_def, div_mul_cancel₀ _ hdb]
      rw [← hα, map_smul, LinearMap.smul_apply, smul_eq_mul, sub_self]
    have h2 : positiveOrientation.areaForm (cfg.T -ᵥ cfg.A - (α • d + β • b)) d = 0 := by
      simp only [map_sub, map_add, map_smul, LinearMap.sub_apply, LinearMap.add_apply,
        LinearMap.smul_apply, positiveOrientation.areaForm_apply_self, smul_zero, add_zero,
        zero_add, smul_eq_mul, mul_zero]
      have hβ : positiveOrientation.areaForm (β • b) d =
          positiveOrientation.areaForm (cfg.T -ᵥ cfg.A) d := by
        rw [map_smul, LinearMap.smul_apply, smul_eq_mul, hβ_def,
          positiveOrientation.areaForm_swap b d, mul_neg, div_mul_cancel₀ _ hdb,
          positiveOrientation.areaForm_swap, neg_neg]
      rw [← hβ, map_smul, LinearMap.smul_apply, smul_eq_mul, sub_self]
    have h3 := hinj _ h1 h2
    exact sub_eq_zero.mp h3
  have hα_pos : 0 < α := by
    rw [hα_def]
    apply div_pos
    · have h : (∡ cfg.T cfg.A cfg.B).sign = 1 := cfg.sign_TAB
      rw [sign_oangle_eq_sign_areaForm, sign_eq_one_iff] at h
      exact h
    · have h : (∡ cfg.D cfg.A cfg.B).sign = 1 := cfg.sign_DAB
      rw [sign_oangle_eq_sign_areaForm, sign_eq_one_iff] at h
      exact h
  have hβ_pos : 0 < β := by
    rw [hβ_def]
    apply div_pos
    · have h : (∡ cfg.D cfg.A cfg.T).sign = 1 := cfg.sign_DAT
      rw [sign_oangle_eq_sign_areaForm, sign_eq_one_iff] at h
      exact h
    · have h : (∡ cfg.D cfg.A cfg.B).sign = 1 := cfg.sign_DAB
      rw [sign_oangle_eq_sign_areaForm, sign_eq_one_iff] at h
      exact h
  refine ⟨α, β, hα_pos, hβ_pos, ?_, hvec⟩
  -- `α < 1` from `σ(oangle(b, T−D)) = +1` (i.e. `sign_UTD`).
  have hDb : (positiveOrientation.oangle b d).sign = -1 := by
    show (∡ cfg.B cfg.A cfg.D).sign = -1
    rw [(oangle_swap₁₃_sign cfg.D cfg.A cfg.B).symm, cfg.sign_DAB]
  have hs : (positiveOrientation.oangle b (cfg.T -ᵥ cfg.D)).sign = 1 := by
    have hrev : positiveOrientation.oangle b (cfg.T -ᵥ cfg.D) =
        -positiveOrientation.oangle (cfg.T -ᵥ cfg.D) b := positiveOrientation.oangle_rev _ _
    have hneg : positiveOrientation.oangle (cfg.T -ᵥ cfg.D) b =
        positiveOrientation.oangle (cfg.D -ᵥ cfg.T) b + ↑Real.pi := by
      rw [← neg_vsub_eq_vsub_rev cfg.D cfg.T, positiveOrientation.oangle_neg_left
        (vsub_ne_zero.mpr cfg.D_ne_T) (vsub_ne_zero.mpr cfg.A_ne_B.symm)]
    have h4 : (∡ ((cfg.B -ᵥ cfg.A) +ᵥ cfg.T) cfg.T cfg.D).sign = -1 := cfg.sign_UTD
    have h6 : (∡ cfg.D cfg.T ((cfg.B -ᵥ cfg.A) +ᵥ cfg.T)).sign = 1 := by
      rw [(oangle_swap₁₃_sign ((cfg.B -ᵥ cfg.A) +ᵥ cfg.T) cfg.T cfg.D).symm, h4, neg_neg]
    have h5 : positiveOrientation.oangle (cfg.D -ᵥ cfg.T) b =
        ∡ cfg.D cfg.T ((cfg.B -ᵥ cfg.A) +ᵥ cfg.T) := by
      show positiveOrientation.oangle (cfg.D -ᵥ cfg.T) b =
        positiveOrientation.oangle (cfg.D -ᵥ cfg.T) (((cfg.B -ᵥ cfg.A) +ᵥ cfg.T) -ᵥ cfg.T)
      rw [vadd_vsub]
    rw [hrev, hneg, h5, Real.Angle.sign_neg, Real.Angle.sign_add_pi, h6, neg_neg]
  have hvec2 : cfg.T -ᵥ cfg.D = (α - 1) • d + β • b := by
    have h : cfg.T -ᵥ cfg.D = (cfg.T -ᵥ cfg.A) - (cfg.D -ᵥ cfg.A) :=
      vsub_sub_vsub_cancel_right cfg.T cfg.D cfg.A |>.symm
    rw [h, hvec]
    module
  have hdrop : (positiveOrientation.oangle b ((α - 1) • d + β • b)).sign =
      (positiveOrientation.oangle b ((α - 1) • d)).sign :=
    oangle_sign_eq_of_vadd_right β
  rw [hvec2, hdrop] at hs
  by_contra hα_ge
  push_neg at hα_ge
  rcases eq_or_lt_of_le hα_ge with heq1 | hgt1
  · rw [heq1, sub_self, zero_smul] at hs
    have h7 : (positiveOrientation.oangle b 0).sign = 0 := by
      rw [sign_oangle_eq_sign_areaForm_vec, map_zero]
      simp
    rw [h7] at hs
    simp at hs
  · have hgt : (positiveOrientation.oangle b ((α - 1) • d)).sign = -1 := by
      rw [positiveOrientation.oangle_smul_right_of_pos _ _ (sub_pos.mpr hgt1)]
      exact hDb
    rw [hgt] at hs
    simp at hs

/-- `L` is on the ray from `T` opposite to `D` (POS4). -/
theorem sameRay_LT : SameRay ℝ (cfg.L -ᵥ cfg.T) (cfg.T -ᵥ cfg.D) := by
  have hLT : cfg.L ≠ cfg.T := by
    intro h
    apply cfg.not_collinear_ABT
    rw [← h]
    exact cfg.L_on_AB
  obtain ⟨α, β, hα, hβ, hα1, hvec⟩ := cfg.T_decomp_DT
  -- `L −ᵥ A = s • (B −ᵥ A)` for some `s`.
  have hL1 : cfg.L ∈ affineSpan ℝ ({cfg.A, cfg.B} : Set Pt) := by
    have h := cfg.L_on_AB.affineSpan_eq_of_ne (Set.mem_insert _ _)
      (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) cfg.A_ne_B
    rw [h]
    apply mem_affineSpan
    simp
  have hA : cfg.A ∈ affineSpan ℝ ({cfg.A, cfg.B} : Set Pt) := by
    apply mem_affineSpan
    simp
  have hv : cfg.L -ᵥ cfg.A ∈ Submodule.span ℝ {cfg.B -ᵥ cfg.A} := by
    have h2 := AffineSubspace.vsub_mem_direction hL1 hA
    rw [direction_affineSpan, vectorSpan_pair_rev] at h2
    exact h2
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hv
  -- `L −ᵥ D = l • (T −ᵥ D)` for some `l`.
  have hL2 : cfg.L ∈ affineSpan ℝ ({cfg.D, cfg.T} : Set Pt) := by
    have h := cfg.L_on_DT.affineSpan_eq_of_ne (Set.mem_insert _ _)
      (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) cfg.D_ne_T
    rw [h]
    apply mem_affineSpan
    simp
  have hD : cfg.D ∈ affineSpan ℝ ({cfg.D, cfg.T} : Set Pt) := by
    apply mem_affineSpan
    simp
  have hv2 : cfg.L -ᵥ cfg.D ∈ Submodule.span ℝ {cfg.T -ᵥ cfg.D} := by
    have h2 := AffineSubspace.vsub_mem_direction hL2 hD
    rw [direction_affineSpan, vectorSpan_pair_rev] at h2
    exact h2
  obtain ⟨l, hl⟩ := Submodule.mem_span_singleton.mp hv2
  -- the two vector expressions for `L −ᵥ T`.
  have hXY : (cfg.A -ᵥ cfg.T) + s • (cfg.B -ᵥ cfg.A) = (cfg.D -ᵥ cfg.T) + l • (cfg.T -ᵥ cfg.D) := by
    have h2 : cfg.L -ᵥ cfg.T = (cfg.A -ᵥ cfg.T) + s • (cfg.B -ᵥ cfg.A) := by
      have h4 : cfg.L -ᵥ cfg.T = (cfg.A -ᵥ cfg.T) + (cfg.L -ᵥ cfg.A) := by
        rw [add_comm, vsub_add_vsub_cancel]
      rw [h4, hs]
    have h3 : cfg.L -ᵥ cfg.T = (cfg.D -ᵥ cfg.T) + l • (cfg.T -ᵥ cfg.D) := by
      have h4 : cfg.L -ᵥ cfg.T = (cfg.D -ᵥ cfg.T) + (cfg.L -ᵥ cfg.D) := by
        rw [add_comm, vsub_add_vsub_cancel]
      rw [h4, hl]
    rw [← h2, ← h3]
  -- expand in the basis.
  set d := cfg.D -ᵥ cfg.A
  set b := cfg.B -ᵥ cfg.A
  have hdb : positiveOrientation.areaForm d b ≠ 0 := by
    have h : (∡ cfg.D cfg.A cfg.B).sign = 1 := cfg.sign_DAB
    rw [sign_oangle_eq_sign_areaForm, sign_eq_one_iff] at h
    exact h.ne'
  have hAT : cfg.A -ᵥ cfg.T = (-α) • d + (-β) • b := by
    rw [← neg_vsub_eq_vsub_rev cfg.T cfg.A, hvec]
    module
  have hDT : cfg.D -ᵥ cfg.T = (1 - α) • d + (-β) • b := by
    have h : cfg.D -ᵥ cfg.T = (cfg.D -ᵥ cfg.A) - (cfg.T -ᵥ cfg.A) :=
      vsub_sub_vsub_cancel_right cfg.D cfg.T cfg.A |>.symm
    rw [h, hvec]
    module
  have hTD : cfg.T -ᵥ cfg.D = (α - 1) • d + β • b := by
    have h : cfg.T -ᵥ cfg.D = (cfg.T -ᵥ cfg.A) - (cfg.D -ᵥ cfg.A) :=
      vsub_sub_vsub_cancel_right cfg.T cfg.D cfg.A |>.symm
    rw [h, hvec]
    module
  -- apply the area form with `b` and with `d`.
  have he1 := congrArg (fun v => positiveOrientation.areaForm v b) hXY
  rw [hAT, hDT, hTD] at he1
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    positiveOrientation.areaForm_apply_self, mul_zero, add_zero] at he1
  have hdb2 : positiveOrientation.areaForm b d ≠ 0 := by
    rw [positiveOrientation.areaForm_swap]
    exact neg_ne_zero.mpr hdb
  have hc1 := congrArg (fun v => positiveOrientation.areaForm v d) hXY
  rw [hAT, hDT, hTD] at hc1
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    positiveOrientation.areaForm_apply_self, mul_zero, add_zero] at hc1
  -- solve the system: `l * (α - 1) = -1`, `s = β * l > 0`.
  have hl1 : l * (α - 1) = -1 := by
    have h1 : -α = (1 - α) + l * (α - 1) :=
      mul_right_cancel₀ hdb (by linear_combination he1)
    linarith [h1]
  have hs_eq : s = β * l := by
    have h1 : s = l * β := mul_right_cancel₀ hdb2 (by linear_combination hc1)
    rw [h1, mul_comm]
  have hs_pos : 0 < s := by
    have hl_pos : 0 < l := by
      have h1 : 0 < 1 - α := sub_pos.mpr hα1
      have h2 : l * (1 - α) = 1 := by linarith [hl1]
      nlinarith [h1, h2]
    rw [hs_eq]
    exact mul_pos hβ hl_pos
  -- hence `σ(∡ A T L) = -1`.
  have hg : positiveOrientation.areaForm (cfg.A -ᵥ cfg.T) (cfg.B -ᵥ cfg.A) < 0 := by
    have hsub : cfg.B -ᵥ cfg.A = (cfg.B -ᵥ cfg.T) + (-1 : ℝ) • (cfg.A -ᵥ cfg.T) := by
      rw [neg_one_smul, ← vsub_sub_vsub_cancel_right cfg.B cfg.A cfg.T, sub_eq_add_neg]
    have h : SignType.sign (positiveOrientation.areaForm (cfg.A -ᵥ cfg.T) (cfg.B -ᵥ cfg.T)) =
        -1 := by
      rw [← sign_oangle_eq_sign_areaForm_vec]
      exact cfg.sign_ATB
    rw [sign_eq_neg_one_iff] at h
    rw [hsub, map_add, map_smul, smul_eq_mul, positiveOrientation.areaForm_apply_self,
      mul_zero, add_zero]
    exact h
  have hsign_ATL : (∡ cfg.A cfg.T cfg.L).sign = -1 := by
    have hkv : cfg.L -ᵥ cfg.T = (cfg.A -ᵥ cfg.T) + s • (cfg.B -ᵥ cfg.A) := by
      have h4 : cfg.L -ᵥ cfg.T = (cfg.A -ᵥ cfg.T) + (cfg.L -ᵥ cfg.A) := by
        rw [add_comm, vsub_add_vsub_cancel]
      rw [h4, hs]
    have h1 : (∡ cfg.A cfg.T cfg.L).sign =
        SignType.sign (positiveOrientation.areaForm (cfg.A -ᵥ cfg.T) (cfg.L -ᵥ cfg.T)) :=
      sign_oangle_eq_sign_areaForm _ _ _
    rw [h1, hkv, map_add, positiveOrientation.areaForm_apply_self, zero_add, map_smul,
      smul_eq_mul, sign_eq_neg_one_iff.mpr (mul_neg_of_pos_of_neg hs_pos hg)]
  -- conclude via the ray dichotomy on line `DT`.
  have hd := sameRay_or_sameRay_neg_vsub_of_collinear cfg.D_ne_T hLT cfg.L_on_DT
  rcases hd with h | h
  · exfalso
    obtain ⟨r, hr, hvr⟩ := h.exists_pos_left (vsub_ne_zero.mpr cfg.D_ne_T)
      (vsub_ne_zero.mpr hLT)
    have h1 : (∡ cfg.A cfg.T cfg.L).sign = 1 := by
      have h2 : ∡ cfg.A cfg.T cfg.L = ∡ cfg.A cfg.T cfg.D := by
        show positiveOrientation.oangle (cfg.A -ᵥ cfg.T) (cfg.L -ᵥ cfg.T) =
          positiveOrientation.oangle (cfg.A -ᵥ cfg.T) (cfg.D -ᵥ cfg.T)
        rw [← hvr, positiveOrientation.oangle_smul_right_of_pos _ _ hr]
      have h3 : (∡ cfg.A cfg.T cfg.D).sign = -(∡ cfg.D cfg.T cfg.A).sign :=
        (oangle_swap₁₃_sign _ _ _).symm
      rw [h2, h3, cfg.sign_DTA, neg_neg]
    rw [h1] at hsign_ATL
    simp at hsign_ATL
  · rw [← neg_vsub_eq_vsub_rev cfg.T cfg.D, ← neg_vsub_eq_vsub_rev cfg.L cfg.T] at h
    exact (sameRay_neg_iff.mp h).symm

/-! ### The finish: `KLSQ` concyclic, `KL ∥ CD`, and Reim's theorem -/

theorem K_ne_T : cfg.K ≠ cfg.T := by
  intro h
  apply cfg.not_collinear_EAT
  rw [← h]
  exact collinear_swap (collinear_rotate cfg.K_on_AE)

theorem L_ne_T : cfg.L ≠ cfg.T := by
  intro h
  apply cfg.not_collinear_ABT
  rw [← h]
  exact cfg.L_on_AB

/-- Lines `AB` and `AE` meet only at `A`. -/
theorem false_of_collinear_AB_AE {X : Pt} (hX : X ≠ cfg.A)
    (h1 : Collinear ℝ ({cfg.A, cfg.B, X} : Set Pt))
    (h2 : Collinear ℝ ({cfg.A, cfg.E, X} : Set Pt)) : False := by
  apply cfg.not_collinear_EAB
  have hiff : Collinear ℝ (insert cfg.B ({cfg.A, cfg.E, X} : Set Pt)) ↔
      Collinear ℝ ({cfg.B, cfg.A, X} : Set Pt) :=
    h2.collinear_insert_iff_of_ne (by simp : cfg.A ∈ ({cfg.A, cfg.E, X} : Set Pt))
      (by simp : X ∈ ({cfg.A, cfg.E, X} : Set Pt)) hX.symm
  have h4 : Collinear ℝ (insert cfg.B ({cfg.A, cfg.E, X} : Set Pt)) :=
    hiff.2 (collinear_swap (collinear_rotate h1))
  apply h4.subset
  intro x hx
  simp at hx
  rcases hx with rfl | rfl | rfl <;> simp

/-- Lines `CT` and `DT` meet only at `T`. -/
theorem false_of_collinear_CT_DT {X : Pt} (hX : X ≠ cfg.T)
    (h1 : Collinear ℝ ({cfg.C, cfg.T, X} : Set Pt))
    (h2 : Collinear ℝ ({cfg.D, cfg.T, X} : Set Pt)) : False := by
  apply cfg.not_collinear_CDT
  have hiff : Collinear ℝ (insert cfg.D ({cfg.C, cfg.T, X} : Set Pt)) ↔
      Collinear ℝ ({cfg.D, cfg.T, X} : Set Pt) :=
    h1.collinear_insert_iff_of_ne (by simp : cfg.T ∈ ({cfg.C, cfg.T, X} : Set Pt))
      (by simp : X ∈ ({cfg.C, cfg.T, X} : Set Pt)) (Ne.symm hX)
  have h4 : Collinear ℝ (insert cfg.D ({cfg.C, cfg.T, X} : Set Pt)) := hiff.2 h2
  apply h4.subset
  intro x hx
  simp at hx
  rcases hx with rfl | rfl | rfl <;> simp

/-- Lines `CD` and `CT` meet only at `C`. -/
theorem false_of_collinear_CD_CT {X : Pt} (hX : X ≠ cfg.C)
    (h1 : Collinear ℝ ({cfg.C, cfg.D, X} : Set Pt))
    (h2 : Collinear ℝ ({cfg.C, cfg.T, X} : Set Pt)) : False := by
  apply cfg.not_collinear_CDT
  have hiff : Collinear ℝ (insert cfg.T ({cfg.C, cfg.D, X} : Set Pt)) ↔
      Collinear ℝ ({cfg.T, cfg.C, X} : Set Pt) :=
    h1.collinear_insert_iff_of_ne (by simp : cfg.C ∈ ({cfg.C, cfg.D, X} : Set Pt))
      (by simp : X ∈ ({cfg.C, cfg.D, X} : Set Pt)) (Ne.symm hX)
  have h4 : Collinear ℝ (insert cfg.T ({cfg.C, cfg.D, X} : Set Pt)) :=
    hiff.2 (collinear_swap (collinear_rotate h2))
  apply h4.subset
  intro x hx
  simp at hx
  rcases hx with rfl | rfl | rfl <;> simp

theorem K_ne_L : cfg.K ≠ cfg.L := by
  intro h
  exact cfg.false_of_collinear_CT_DT cfg.K_ne_T cfg.K_on_CT
    (by rw [h]; exact cfg.L_on_DT)

theorem K_ne_S : cfg.K ≠ cfg.S := by
  intro h
  exact cfg.false_of_collinear_CT_DT cfg.K_ne_T cfg.K_on_CT
    (by rw [h]; exact cfg.collinear_DTS)

theorem L_ne_Q : cfg.L ≠ cfg.Q := by
  intro h
  exact cfg.false_of_collinear_CT_DT cfg.L_ne_T
    (by rw [h]; exact cfg.collinear_CTQ) cfg.L_on_DT

theorem L_ne_S : cfg.L ≠ cfg.S := by
  intro h
  exact cfg.false_of_collinear_AB_AE cfg.A_ne_S.symm
    (by rw [← h]; exact cfg.L_on_AB) cfg.collinear_AES

theorem Q_ne_K : cfg.Q ≠ cfg.K := by
  intro h
  exact cfg.false_of_collinear_AB_AE cfg.A_ne_Q.symm cfg.collinear_ABQ
    (by rw [h]; exact cfg.K_on_AE)

theorem S_ne_Q : cfg.S ≠ cfg.Q := by
  intro h
  exact cfg.false_of_collinear_AB_AE cfg.A_ne_S.symm
    (by rw [h]; exact cfg.collinear_ABQ) cfg.collinear_AES

theorem R_ne_P : cfg.R ≠ cfg.P := by
  intro h
  exact cfg.false_of_collinear_AB_AE cfg.R_ne_A
    (by rw [h]; exact cfg.collinear_ABP) cfg.collinear_AER

theorem Q_ne_P : cfg.Q ≠ cfg.P := by
  intro h
  exact cfg.false_of_collinear_CD_CT cfg.Q_ne_C
    (by rw [h]; exact cfg.collinear_CDP) cfg.collinear_CTQ

/-- `R ≠ S` (they are separated by `E, A` on line `AE`). -/
theorem R_ne_S : cfg.R ≠ cfg.S := by
  intro h
  apply false_of_wbtw_wbtw cfg.sbtw_REA.wbtw
  · rw [h]
    exact cfg.sbtw_EAS.wbtw.symm
  · exact cfg.A_ne_E

/-- A point of a collinear triple lies in the affine span of the other two. -/
theorem mem_affineSpan_pair_of_collinear {U V X : Pt} (hUV : U ≠ V)
    (h : Collinear ℝ ({U, V, X} : Set Pt)) : X ∈ affineSpan ℝ ({U, V} : Set Pt) := by
  have he := h.affineSpan_eq_of_ne (Set.mem_insert _ _)
    (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) hUV
  rw [he]
  apply mem_affineSpan
  simp

/-- `K, L, S, Q` are concyclic: the SAS similarity `△TKL ~ △TSQ` (ratio `TK/TS = TL/TQ`
from `TK·TQ = TL·TS`, included angle `∠KTL = ∠STQ = ∠CTD`) gives `∠TKL = ∠TSQ`, which
with sign analysis yields `(2 : ℤ) • ∡ Q K L = (2 : ℤ) • ∡ Q S L`. -/
theorem concyclic_KLSQ : Concyclic ({cfg.K, cfg.L, cfg.S, cfg.Q} : Set Pt) := by
  obtain ⟨κK, hκK, hKv⟩ := cfg.sameRay_KT.exists_pos_right
    (vsub_ne_zero.mpr cfg.K_ne_T) (vsub_ne_zero.mpr cfg.C_ne_T.symm)
  obtain ⟨κQ, hκQ, hQv⟩ := cfg.sameRay_QT.exists_pos_right
    (vsub_ne_zero.mpr cfg.Q_ne_T) (vsub_ne_zero.mpr cfg.C_ne_T.symm)
  obtain ⟨μL, hμL, hLv⟩ := cfg.sameRay_LT.exists_pos_right
    (vsub_ne_zero.mpr cfg.L_ne_T) (vsub_ne_zero.mpr cfg.D_ne_T.symm)
  obtain ⟨μS, hμS, hSv⟩ := cfg.sameRay_ST.exists_pos_right
    (vsub_ne_zero.mpr cfg.S_ne_T) (vsub_ne_zero.mpr cfg.D_ne_T.symm)
  -- included angles at `T`
  have hKTL : ∠ cfg.K cfg.T cfg.L = ∠ cfg.C cfg.T cfg.D := by
    show InnerProductGeometry.angle (cfg.K -ᵥ cfg.T) (cfg.L -ᵥ cfg.T) =
      InnerProductGeometry.angle (cfg.C -ᵥ cfg.T) (cfg.D -ᵥ cfg.T)
    rw [hKv, hLv, InnerProductGeometry.angle_smul_left_of_pos _ _ hκK,
      InnerProductGeometry.angle_smul_right_of_pos _ _ hμL,
      ← neg_vsub_eq_vsub_rev cfg.C cfg.T, ← neg_vsub_eq_vsub_rev cfg.D cfg.T,
      InnerProductGeometry.angle_neg_left, InnerProductGeometry.angle_neg_right,
      sub_sub_cancel]
  have hSTQ : ∠ cfg.S cfg.T cfg.Q = ∠ cfg.D cfg.T cfg.C := by
    show InnerProductGeometry.angle (cfg.S -ᵥ cfg.T) (cfg.Q -ᵥ cfg.T) =
      InnerProductGeometry.angle (cfg.D -ᵥ cfg.T) (cfg.C -ᵥ cfg.T)
    rw [hSv, hQv, InnerProductGeometry.angle_smul_left_of_pos _ _ hμS,
      InnerProductGeometry.angle_smul_right_of_pos _ _ hκQ,
      ← neg_vsub_eq_vsub_rev cfg.D cfg.T, ← neg_vsub_eq_vsub_rev cfg.C cfg.T,
      InnerProductGeometry.angle_neg_left, InnerProductGeometry.angle_neg_right,
      sub_sub_cancel]
  have hSTQ' : ∠ cfg.S cfg.T cfg.Q = ∠ cfg.C cfg.T cfg.D := hSTQ.trans (angle_comm _ _ _)
  -- the common ratio `lam = TK / TS = TL / TQ`
  have hTS : dist cfg.T cfg.S ≠ 0 := dist_ne_zero.mpr cfg.S_ne_T.symm
  set lam := dist cfg.T cfg.K / dist cfg.T cfg.S with hlam
  have hlam_pos : 0 < lam :=
    div_pos (dist_pos.mpr cfg.K_ne_T.symm) (dist_pos.mpr cfg.S_ne_T.symm)
  have hK_lam : dist cfg.T cfg.K = lam * dist cfg.T cfg.S := (div_mul_cancel₀ _ hTS).symm
  have hL_lam : dist cfg.T cfg.L = lam * dist cfg.T cfg.Q := by
    have h2 := cfg.dist_TK_mul_TQ
    have h3 : lam * dist cfg.T cfg.S = dist cfg.T cfg.K := div_mul_cancel₀ _ hTS
    have h4 : dist cfg.T cfg.L * dist cfg.T cfg.S =
        (lam * dist cfg.T cfg.Q) * dist cfg.T cfg.S := by
      linear_combination -h2 - dist cfg.T cfg.Q * h3
    exact mul_right_cancel₀ hTS h4
  -- the third side `KL = lam · SQ` from the law of cosines
  have hKL_lam : dist cfg.K cfg.L = lam * dist cfg.S cfg.Q := by
    have lc₁ := dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle
      cfg.K cfg.T cfg.L
    have lc₂ := dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle
      cfg.S cfg.T cfg.Q
    rw [dist_comm cfg.K cfg.T, dist_comm cfg.L cfg.T, hKTL] at lc₁
    rw [dist_comm cfg.S cfg.T, dist_comm cfg.Q cfg.T, hSTQ'] at lc₂
    rw [hK_lam, hL_lam] at lc₁
    have hSQ2 : dist cfg.K cfg.L ^ 2 = lam ^ 2 * dist cfg.S cfg.Q ^ 2 := by
      linear_combination lc₁ - lam ^ 2 * lc₂
    have hSQ_pos : 0 < dist cfg.S cfg.Q := dist_pos.mpr cfg.S_ne_Q
    have hfact : (dist cfg.K cfg.L - lam * dist cfg.S cfg.Q) *
        (dist cfg.K cfg.L + lam * dist cfg.S cfg.Q) = 0 := by
      nlinarith [hSQ2]
    have hsum : 0 < dist cfg.K cfg.L + lam * dist cfg.S cfg.Q := by
      have h1 : 0 < lam * dist cfg.S cfg.Q := mul_pos hlam_pos hSQ_pos
      linarith [h1, dist_nonneg (x := cfg.K) (y := cfg.L)]
    rcases mul_eq_zero.mp hfact with h | h
    · linarith [h]
    · linarith [h, hsum]
  -- SSS similarity: `∠TKL = ∠TSQ`
  have hTKL2 : ∠ cfg.T cfg.K cfg.L = ∠ cfg.T cfg.S cfg.Q :=
    angle_eq_angle_of_sss_smul hK_lam hKL_lam (by
      rw [dist_comm cfg.L cfg.T, hL_lam, dist_comm cfg.Q cfg.T])
      cfg.K_ne_T.symm cfg.K_ne_L.symm
  -- signs of the two oriented angles
  have h4 : positiveOrientation.areaForm (cfg.T -ᵥ cfg.C) (cfg.T -ᵥ cfg.D) < 0 := by
    have h : (∡ cfg.C cfg.T cfg.D).sign = -1 := cfg.sign_CTD
    rw [sign_oangle_eq_sign_areaForm, sign_eq_neg_one_iff] at h
    have h5 : positiveOrientation.areaForm (cfg.T -ᵥ cfg.C) (cfg.T -ᵥ cfg.D) =
        positiveOrientation.areaForm (cfg.C -ᵥ cfg.T) (cfg.D -ᵥ cfg.T) := by
      rw [← neg_vsub_eq_vsub_rev cfg.C cfg.T, ← neg_vsub_eq_vsub_rev cfg.D cfg.T]
      simp only [map_neg, LinearMap.neg_apply, neg_neg]
    rwa [h5]
  have hsign_TKL : (∡ cfg.T cfg.K cfg.L).sign = 1 := by
    have h1 : (∡ cfg.T cfg.K cfg.L).sign =
        SignType.sign (positiveOrientation.areaForm (cfg.T -ᵥ cfg.K) (cfg.L -ᵥ cfg.K)) :=
      sign_oangle_eq_sign_areaForm _ _ _
    have h2 : cfg.T -ᵥ cfg.K = (-κK) • (cfg.T -ᵥ cfg.C) := by
      rw [← neg_vsub_eq_vsub_rev cfg.K cfg.T, hKv, neg_smul]
    have h3 : cfg.L -ᵥ cfg.K = (cfg.L -ᵥ cfg.T) - (cfg.K -ᵥ cfg.T) :=
      (vsub_sub_vsub_cancel_right cfg.L cfg.K cfg.T).symm
    rw [h1, h2, h3, hLv, hKv]
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      positiveOrientation.areaForm_apply_self, smul_zero, sub_zero, smul_eq_mul,
      sign_eq_one_iff]
    nlinarith [hκK, hμL, h4, mul_pos hκK hμL]
  have hsign_TSQ : (∡ cfg.T cfg.S cfg.Q).sign = -1 := by
    have h1 : (∡ cfg.T cfg.S cfg.Q).sign =
        SignType.sign (positiveOrientation.areaForm (cfg.T -ᵥ cfg.S) (cfg.Q -ᵥ cfg.S)) :=
      sign_oangle_eq_sign_areaForm _ _ _
    have h2 : cfg.T -ᵥ cfg.S = (-μS) • (cfg.T -ᵥ cfg.D) := by
      rw [← neg_vsub_eq_vsub_rev cfg.S cfg.T, hSv, neg_smul]
    have h3 : cfg.Q -ᵥ cfg.S = (cfg.Q -ᵥ cfg.T) - (cfg.S -ᵥ cfg.T) :=
      (vsub_sub_vsub_cancel_right cfg.Q cfg.S cfg.T).symm
    have h4' : 0 < positiveOrientation.areaForm (cfg.T -ᵥ cfg.D) (cfg.T -ᵥ cfg.C) := by
      rw [positiveOrientation.areaForm_swap]
      exact neg_pos.mpr h4
    rw [h1, h2, h3, hQv, hSv]
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      positiveOrientation.areaForm_apply_self, smul_zero, sub_zero, smul_eq_mul,
      sign_eq_neg_one_iff]
    nlinarith [hκQ, hμS, h4', mul_pos hκQ h4']
  have hsign_QST : (∡ cfg.Q cfg.S cfg.T).sign = 1 := by
    rw [(oangle_swap₁₃_sign cfg.T cfg.S cfg.Q).symm, hsign_TSQ, neg_neg]
  have horient : ∡ cfg.T cfg.K cfg.L = ∡ cfg.Q cfg.S cfg.T :=
    oangle_eq_of_angle_eq_of_sign_eq (hTKL2.trans (angle_comm _ _ _))
      (by rw [hsign_TKL, hsign_QST])
  -- collinearity witnesses for the mod-π moves
  have hT_mem : cfg.T ∈ affineSpan ℝ ({cfg.C, cfg.T} : Set Pt) := by
    apply mem_affineSpan
    simp
  have hQ_mem : cfg.Q ∈ affineSpan ℝ ({cfg.C, cfg.T} : Set Pt) :=
    mem_affineSpan_pair_of_collinear cfg.C_ne_T cfg.collinear_CTQ
  have hK_mem : cfg.K ∈ affineSpan ℝ ({cfg.C, cfg.T} : Set Pt) :=
    mem_affineSpan_pair_of_collinear cfg.C_ne_T cfg.K_on_CT
  have hcol_TKQ : Collinear ℝ ({cfg.T, cfg.K, cfg.Q} : Set Pt) :=
    collinear_triple_of_mem_affineSpan_pair hT_mem hK_mem hQ_mem
  have hT_mem2 : cfg.T ∈ affineSpan ℝ ({cfg.D, cfg.T} : Set Pt) := by
    apply mem_affineSpan
    simp
  have hL_mem2 : cfg.L ∈ affineSpan ℝ ({cfg.D, cfg.T} : Set Pt) :=
    mem_affineSpan_pair_of_collinear cfg.D_ne_T cfg.L_on_DT
  have hS_mem2 : cfg.S ∈ affineSpan ℝ ({cfg.D, cfg.T} : Set Pt) :=
    mem_affineSpan_pair_of_collinear cfg.D_ne_T cfg.collinear_DTS
  have hcol_LST : Collinear ℝ ({cfg.L, cfg.S, cfg.T} : Set Pt) :=
    collinear_triple_of_mem_affineSpan_pair hL_mem2 hS_mem2 hT_mem2
  have hQKL : ¬Collinear ℝ ({cfg.Q, cfg.K, cfg.L} : Set Pt) := by
    intro hcol
    have hL_mem : cfg.L ∈ affineSpan ℝ ({cfg.C, cfg.T} : Set Pt) := by
      have hle : affineSpan ℝ ({cfg.Q, cfg.K} : Set Pt) ≤
          affineSpan ℝ ({cfg.C, cfg.T} : Set Pt) := by
        rw [affineSpan_le]
        intro x hx
        simp at hx
        rcases hx with rfl | rfl
        · exact hQ_mem
        · exact hK_mem
      exact hle (mem_affineSpan_pair_of_collinear cfg.Q_ne_K hcol)
    have hLT_col : Collinear ℝ ({cfg.L, cfg.C, cfg.T} : Set Pt) :=
      collinear_insert_of_mem_affineSpan_pair hL_mem
    exact cfg.false_of_collinear_CT_DT cfg.L_ne_T (collinear_rotate hLT_col) cfg.L_on_DT
  have hmove1 : (2 : ℤ) • ∡ cfg.T cfg.K cfg.L = (2 : ℤ) • ∡ cfg.Q cfg.K cfg.L :=
    hcol_TKQ.two_zsmul_oangle_eq_left cfg.K_ne_T.symm cfg.Q_ne_K
  have hmove2 : (2 : ℤ) • ∡ cfg.Q cfg.S cfg.T = (2 : ℤ) • ∡ cfg.Q cfg.S cfg.L :=
    (collinear_rev hcol_LST).two_zsmul_oangle_eq_right cfg.S_ne_T.symm cfg.L_ne_S
  have h2z : (2 : ℤ) • ∡ cfg.T cfg.K cfg.L = (2 : ℤ) • ∡ cfg.Q cfg.S cfg.T := by
    rw [horient]
  have hcrit : (2 : ℤ) • ∡ cfg.Q cfg.K cfg.L = (2 : ℤ) • ∡ cfg.Q cfg.S cfg.L :=
    hmove1.symm.trans (h2z.trans hmove2)
  have hset : ({cfg.Q, cfg.K, cfg.S, cfg.L} : Set Pt) = {cfg.K, cfg.L, cfg.S, cfg.Q} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [← hset]
  exact concyclic_of_two_zsmul_oangle_eq_of_not_collinear hcrit hQKL

/-- `KL` is parallel to `CD`: the vector form `K −ᵥ L = κ • (D −ᵥ C)` with `κ > 0`,
from `TK/TC = TL/TD` (i.e. `TK·TD = TL·TC`) and the ray positions of `K` and `L`. -/
theorem KL_eq_smul_CD : ∃ κ : ℝ, 0 < κ ∧ cfg.K -ᵥ cfg.L = κ • (cfg.D -ᵥ cfg.C) := by
  obtain ⟨κK, hκK, hKv⟩ := cfg.sameRay_KT.exists_pos_right
    (vsub_ne_zero.mpr cfg.K_ne_T) (vsub_ne_zero.mpr cfg.C_ne_T.symm)
  obtain ⟨μL, hμL, hLv⟩ := cfg.sameRay_LT.exists_pos_right
    (vsub_ne_zero.mpr cfg.L_ne_T) (vsub_ne_zero.mpr cfg.D_ne_T.symm)
  have hTKκ : dist cfg.T cfg.K = κK * dist cfg.T cfg.C := by
    rw [dist_eq_norm_vsub, ← neg_vsub_eq_vsub_rev cfg.K cfg.T, norm_neg, hKv, norm_smul,
      Real.norm_eq_abs, abs_of_pos hκK, ← dist_eq_norm_vsub]
  have hTLμ : dist cfg.T cfg.L = μL * dist cfg.T cfg.D := by
    rw [dist_eq_norm_vsub, ← neg_vsub_eq_vsub_rev cfg.L cfg.T, norm_neg, hLv, norm_smul,
      Real.norm_eq_abs, abs_of_pos hμL, ← dist_eq_norm_vsub]
  have hκ : κK = μL := by
    have h1 := cfg.dist_TK_mul_TD
    rw [hTKκ, hTLμ] at h1
    have h2 : κK * (dist cfg.T cfg.C * dist cfg.T cfg.D) =
        μL * (dist cfg.T cfg.C * dist cfg.T cfg.D) := by
      linear_combination h1
    exact mul_right_cancel₀
      (mul_ne_zero (dist_ne_zero.mpr cfg.C_ne_T.symm) (dist_ne_zero.mpr cfg.D_ne_T.symm)) h2
  refine ⟨κK, hκK, ?_⟩
  have h3 : cfg.L -ᵥ cfg.K = (cfg.L -ᵥ cfg.T) - (cfg.K -ᵥ cfg.T) :=
    (vsub_sub_vsub_cancel_right cfg.L cfg.K cfg.T).symm
  have h4 : cfg.L -ᵥ cfg.K = κK • (cfg.C -ᵥ cfg.D) := by
    rw [h3, hLv, hKv, ← hκ, ← smul_sub]
    congr 1
    exact vsub_sub_vsub_cancel_left _ _ _
  rw [← neg_vsub_eq_vsub_rev cfg.L cfg.K, h4, ← neg_vsub_eq_vsub_rev cfg.C cfg.D, smul_neg]

theorem result : Concyclic ({cfg.P, cfg.S, cfg.Q, cfg.R} : Set Pt) := by
  -- scalar forms on lines `CD` and `AB`
  have hR_mem : cfg.R ∈ affineSpan ℝ ({cfg.C, cfg.D} : Set Pt) :=
    mem_affineSpan_pair_of_collinear cfg.C_ne_D cfg.collinear_CDR
  have hP_mem : cfg.P ∈ affineSpan ℝ ({cfg.C, cfg.D} : Set Pt) :=
    mem_affineSpan_pair_of_collinear cfg.C_ne_D cfg.collinear_CDP
  have hvRP : cfg.R -ᵥ cfg.P ∈ Submodule.span ℝ {cfg.D -ᵥ cfg.C} := by
    have h2 := AffineSubspace.vsub_mem_direction hR_mem hP_mem
    rw [direction_affineSpan, vectorSpan_pair_rev] at h2
    exact h2
  obtain ⟨t₁, ht₁⟩ := Submodule.mem_span_singleton.mp hvRP
  have ht1 : t₁ ≠ 0 := by
    intro h
    apply cfg.R_ne_P
    rw [← vsub_eq_zero_iff_eq, ← ht₁, h, zero_smul]
  have hQ_mem : cfg.Q ∈ affineSpan ℝ ({cfg.A, cfg.B} : Set Pt) :=
    mem_affineSpan_pair_of_collinear cfg.A_ne_B cfg.collinear_ABQ
  have hP_mem2 : cfg.P ∈ affineSpan ℝ ({cfg.A, cfg.B} : Set Pt) :=
    mem_affineSpan_pair_of_collinear cfg.A_ne_B cfg.collinear_ABP
  have hvQP : cfg.Q -ᵥ cfg.P ∈ Submodule.span ℝ {cfg.B -ᵥ cfg.A} := by
    have h2 := AffineSubspace.vsub_mem_direction hQ_mem hP_mem2
    rw [direction_affineSpan, vectorSpan_pair_rev] at h2
    exact h2
  obtain ⟨t₂, ht₂⟩ := Submodule.mem_span_singleton.mp hvQP
  have ht2 : t₂ ≠ 0 := by
    intro h
    apply cfg.Q_ne_P
    rw [← vsub_eq_zero_iff_eq, ← ht₂, h, zero_smul]
  have hL_mem3 : cfg.L ∈ affineSpan ℝ ({cfg.A, cfg.B} : Set Pt) :=
    mem_affineSpan_pair_of_collinear cfg.A_ne_B cfg.L_on_AB
  have hvQL : cfg.Q -ᵥ cfg.L ∈ Submodule.span ℝ {cfg.B -ᵥ cfg.A} := by
    have h2 := AffineSubspace.vsub_mem_direction hQ_mem hL_mem3
    rw [direction_affineSpan, vectorSpan_pair_rev] at h2
    exact h2
  obtain ⟨t₃, ht₃⟩ := Submodule.mem_span_singleton.mp hvQL
  have ht3 : t₃ ≠ 0 := by
    intro h
    apply cfg.L_ne_Q.symm
    rw [← vsub_eq_zero_iff_eq, ← ht₃, h, zero_smul]
  obtain ⟨κ, hκ, hκv⟩ := cfg.KL_eq_smul_CD
  -- Reim's theorem: the fourfold oriented-angle chain mod `π`
  have e1 : (2 : ℤ) • ∡ cfg.R cfg.P cfg.Q =
      (2 : ℤ) • positiveOrientation.oangle (cfg.D -ᵥ cfg.C) (cfg.B -ᵥ cfg.A) := by
    show (2 : ℤ) • positiveOrientation.oangle (cfg.R -ᵥ cfg.P) (cfg.Q -ᵥ cfg.P) = _
    rw [← ht₁, ← ht₂]
    exact two_zsmul_oangle_smul (vsub_ne_zero.mpr cfg.C_ne_D.symm)
      (vsub_ne_zero.mpr cfg.A_ne_B.symm) ht1 ht2
  have e2 : (2 : ℤ) • ∡ cfg.K cfg.L cfg.Q =
      (2 : ℤ) • positiveOrientation.oangle (cfg.D -ᵥ cfg.C) (cfg.B -ᵥ cfg.A) := by
    show (2 : ℤ) • positiveOrientation.oangle (cfg.K -ᵥ cfg.L) (cfg.Q -ᵥ cfg.L) = _
    rw [hκv, ← ht₃]
    exact two_zsmul_oangle_smul (vsub_ne_zero.mpr cfg.C_ne_D.symm)
      (vsub_ne_zero.mpr cfg.A_ne_B.symm) hκ.ne' ht3
  have e3 : (2 : ℤ) • ∡ cfg.K cfg.L cfg.Q = (2 : ℤ) • ∡ cfg.K cfg.S cfg.Q :=
    cfg.concyclic_KLSQ.1.two_zsmul_oangle_eq cfg.K_ne_L.symm cfg.L_ne_Q cfg.K_ne_S.symm
      cfg.S_ne_Q
  have hK_mem2 : cfg.K ∈ affineSpan ℝ ({cfg.A, cfg.E} : Set Pt) :=
    mem_affineSpan_pair_of_collinear cfg.A_ne_E cfg.K_on_AE
  have hS_mem4 : cfg.S ∈ affineSpan ℝ ({cfg.A, cfg.E} : Set Pt) :=
    mem_affineSpan_pair_of_collinear cfg.A_ne_E cfg.collinear_AES
  have hR_mem2 : cfg.R ∈ affineSpan ℝ ({cfg.A, cfg.E} : Set Pt) :=
    mem_affineSpan_pair_of_collinear cfg.A_ne_E cfg.collinear_AER
  have hcol_KSR : Collinear ℝ ({cfg.K, cfg.S, cfg.R} : Set Pt) :=
    collinear_triple_of_mem_affineSpan_pair hK_mem2 hS_mem4 hR_mem2
  have e4 : (2 : ℤ) • ∡ cfg.K cfg.S cfg.Q = (2 : ℤ) • ∡ cfg.R cfg.S cfg.Q :=
    hcol_KSR.two_zsmul_oangle_eq_left cfg.K_ne_S cfg.R_ne_S
  have hRPQ : ¬Collinear ℝ ({cfg.R, cfg.P, cfg.Q} : Set Pt) := by
    intro hcol
    have hR_mem3 : cfg.R ∈ affineSpan ℝ ({cfg.A, cfg.B} : Set Pt) := by
      have hle : affineSpan ℝ ({cfg.P, cfg.Q} : Set Pt) ≤
          affineSpan ℝ ({cfg.A, cfg.B} : Set Pt) := by
        rw [affineSpan_le]
        intro x hx
        simp at hx
        rcases hx with rfl | rfl
        · exact hP_mem2
        · exact hQ_mem
      exact hle (mem_affineSpan_pair_of_collinear cfg.Q_ne_P.symm (collinear_rotate hcol))
    have hRAB : Collinear ℝ ({cfg.R, cfg.A, cfg.B} : Set Pt) :=
      collinear_insert_of_mem_affineSpan_pair hR_mem3
    exact cfg.false_of_collinear_AB_AE cfg.R_ne_A (collinear_rotate hRAB) cfg.collinear_AER
  have key : (2 : ℤ) • ∡ cfg.R cfg.P cfg.Q = (2 : ℤ) • ∡ cfg.R cfg.S cfg.Q :=
    e1.trans (e2.symm.trans (e3.trans e4))
  have hset : ({cfg.R, cfg.P, cfg.S, cfg.Q} : Set Pt) = {cfg.P, cfg.S, cfg.Q, cfg.R} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [← hset]
  exact concyclic_of_two_zsmul_oangle_eq_of_not_collinear key hRPQ

/- ## Proof summary (following Evan Chen's IMO 2022 notes, §2.1, and the official solution)

The proof is complete; its structure:

- **Statement**: config structure `Imo2022q4Cfg` + `problem`.  Convexity is stated as
  strict left turns (`0 < (∡ A B C).sign` etc.); `T` inside is stated both as
  `interior (convexHull ...)` membership and as the implied strict left-of-edge
  conditions `0 < (∡ A B T).sign` etc. (which make all nondegeneracy derivations
  mechanical, avoiding a `convexHull`/`interior` ↔ `oangle` bridge).
- **Nondegeneracy layer**: vertex distinctness, non-collinearity of consecutive vertices
  and of `T` with every edge, all from the sign hypotheses.
- **SSS congruence** of `△BTC` and `△DTE`: `angle_BTC_eq_DTE`, `angle_TBC_eq_TDE`,
  `angle_BCT_eq_DET` (law of cosines + `Real.injOn_cos`), with oriented upgrades
  (`oangle_BTC_eq_DTE`, etc.) via sign computations.
- **Ratio chain** (law of sines through the indirect similarities `△BTQ ~ △ETS`,
  `△BTL ~ △ETK`): `dist_TQ_mul_TE` (`TQ·TE = TS·TB`), `dist_TL_mul_TE`
  (`TL·TE = TK·TB`), and the cross-multiplied forms `dist_TK_mul_TQ` (`TK·TQ = TL·TS`)
  and `dist_TK_mul_TD` (`TK·TD = TL·TC`).
- **Ray positions** (the heart of the matter, replacing the classical ratio chain
  through `X = BT ∩ AE`, `Y = ET ∩ AB`, which is not needed):
  - `sameRay_QT`, `sameRay_ST`: `Q` (resp. `S`) is on the ray from `T` opposite to `C`
    (resp. `D`), from the given `Sbtw` orders via sign arguments.
  - `sameRay_KT` (POS3): `K = CT ∩ AE` is on the ray from `T` opposite to `C`.  The
    proof decomposes `T −ᵥ A` in the basis `(C −ᵥ A, E −ᵥ A)` (`T_decomp`); the key
    coefficient bound `α < 1` is the Euclid inequality `∠CTA + ∠ATU > π` (`sign_CTU`),
    which follows from `∠TCA + ∠CAE < π` (`ineq_TCA_CAE`, proved from the pentagon
    angle sum and `∠CDE + ∠DEA > π`).
  - `sameRay_LT` (POS4): `L = DT ∩ AB` is on the ray from `T` opposite to `D`,
    mirroring POS3 with basis `(D −ᵥ A, B −ᵥ A)`; the Euclid inequality is
    `∠ADT + ∠DAB < π` (`ineq_ADT_DAB`), proved from the pentagon angle sum, the SSS
    congruences, and `∠CDE + ∠DEA > π`.
- **`KLSQ` concyclic** (`concyclic_KLSQ`): SAS similarity of `△TKL` and `△TSQ`
  (`TK/TS = TL/TQ` from `TK·TQ = TL·TS`, included angle `∠KTL = ∠STQ = ∠CTD`, third
  side from the law of cosines) gives `∠TKL = ∠TSQ`; sign analysis of the two oriented
  angles turns this into `(2 : ℤ) • ∡ Q K L = (2 : ℤ) • ∡ Q S L`, and
  `concyclic_of_two_zsmul_oangle_eq_of_not_collinear` concludes.
- **`KL ∥ CD`** (`KL_eq_smul_CD`): `K −ᵥ L = κ • (D −ᵥ C)` with `κ > 0`, from
  `TK·TD = TL·TC` and the ray positions of `K` and `L`.
- **Reim's theorem finish** (`result`): the oriented angle chain mod `π`
  `(2 : ℤ) • ∡ R P Q = (2 : ℤ) • ∡ (D −ᵥ C, B −ᵥ A) = (2 : ℤ) • ∡ K L Q`
  `= (2 : ℤ) • ∡ K S Q` (circle `KLSQ`) `= (2 : ℤ) • ∡ R S Q`, plus
  `¬Collinear {R, P, Q}`, gives `Concyclic {P, S, Q, R}`.

PITFALLS discovered:
- The similarities are INDIRECT (Evan Chen's `−∼`).  `Q` lies on line `CT` but on the
  ray from `T` OPPOSITE to `C` (and similarly `S` opposite to `D`, `K` opposite to `C`,
  `L` opposite to `D`); these ray facts must be DERIVED from the configuration via the
  Euclid inequalities above.  The robust route is oriented-angle chasing mod `π`
  (i.e. `(2 : ℤ) • ∡` equalities) plus sign computations via the area form
  (`sign_oangle_eq_sign_areaForm`) to resolve signs when ratios of unsigned lengths are
  needed.
- `angle_eq_angle_of_sss` needs the two side-adjacent `≠` facts at the vertex
  (`p₁ ≠ p₂`, `p₃ ≠ p₂`); for obtuse configurations get them from the convexity
  sign hypotheses as done in `B_ne_C` etc.
-/

end Imo2022q4Cfg

snip end

problem imo2022_p4
    (A B C D E T P Q R S : EuclideanSpace ℝ (Fin 2))
    (hconv_AB : ∀ X ∈ ({C, D, E} : Set (EuclideanSpace ℝ (Fin 2))), 0 < (∡ A B X).sign)
    (hconv_BC : ∀ X ∈ ({D, E, A} : Set (EuclideanSpace ℝ (Fin 2))), 0 < (∡ B C X).sign)
    (hconv_CD : ∀ X ∈ ({E, A, B} : Set (EuclideanSpace ℝ (Fin 2))), 0 < (∡ C D X).sign)
    (hconv_DE : ∀ X ∈ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))), 0 < (∡ D E X).sign)
    (hconv_EA : ∀ X ∈ ({B, C, D} : Set (EuclideanSpace ℝ (Fin 2))), 0 < (∡ E A X).sign)
    (T_mem_interior : T ∈ interior (convexHull ℝ {A, B, C, D, E}))
    (oangle_ABT_pos : 0 < (∡ A B T).sign)
    (oangle_BCT_pos : 0 < (∡ B C T).sign)
    (oangle_CDT_pos : 0 < (∡ C D T).sign)
    (oangle_DET_pos : 0 < (∡ D E T).sign)
    (oangle_EAT_pos : 0 < (∡ E A T).sign)
    (dist_TB_eq_TD : dist T B = dist T D)
    (dist_TC_eq_TE : dist T C = dist T E)
    (dist_BC_eq_DE : dist B C = dist D E)
    (angle_ABT_eq_TEA : ∠ A B T = ∠ T E A)
    (A_ne_B : A ≠ B) (T_ne_B : T ≠ B) (T_ne_E : T ≠ E) (A_ne_E : A ≠ E)
    (C_ne_D : C ≠ D) (C_ne_T : C ≠ T) (D_ne_T : D ≠ T)
    (collinear_ABP : Collinear ℝ ({A, B, P} : Set (EuclideanSpace ℝ (Fin 2))))
    (collinear_CDP : Collinear ℝ ({C, D, P} : Set (EuclideanSpace ℝ (Fin 2))))
    (collinear_ABQ : Collinear ℝ ({A, B, Q} : Set (EuclideanSpace ℝ (Fin 2))))
    (collinear_CTQ : Collinear ℝ ({C, T, Q} : Set (EuclideanSpace ℝ (Fin 2))))
    (collinear_AER : Collinear ℝ ({A, E, R} : Set (EuclideanSpace ℝ (Fin 2))))
    (collinear_CDR : Collinear ℝ ({C, D, R} : Set (EuclideanSpace ℝ (Fin 2))))
    (collinear_AES : Collinear ℝ ({A, E, S} : Set (EuclideanSpace ℝ (Fin 2))))
    (collinear_DTS : Collinear ℝ ({D, T, S} : Set (EuclideanSpace ℝ (Fin 2))))
    (sbtw_PBA : Sbtw ℝ P B A) (sbtw_BAQ : Sbtw ℝ B A Q)
    (sbtw_REA : Sbtw ℝ R E A) (sbtw_EAS : Sbtw ℝ E A S) :
    Concyclic ({P, S, Q, R} : Set (EuclideanSpace ℝ (Fin 2))) :=
  (⟨A, B, C, D, E, T, P, Q, R, S, hconv_AB, hconv_BC, hconv_CD, hconv_DE, hconv_EA,
    T_mem_interior, oangle_ABT_pos, oangle_BCT_pos, oangle_CDT_pos, oangle_DET_pos,
    oangle_EAT_pos, dist_TB_eq_TD, dist_TC_eq_TE, dist_BC_eq_DE, angle_ABT_eq_TEA,
    A_ne_B, T_ne_B, T_ne_E, A_ne_E, C_ne_D, C_ne_T, D_ne_T, collinear_ABP, collinear_CDP,
    collinear_ABQ, collinear_CTQ, collinear_AER, collinear_CDR, collinear_AES,
    collinear_DTS, sbtw_PBA, sbtw_BAQ, sbtw_REA, sbtw_EAS⟩ : Imo2022q4Cfg).result

end Imo2022P4
