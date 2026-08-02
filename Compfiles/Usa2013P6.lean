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
public import Mathlib.Analysis.InnerProductSpace.TwoDim
public import Mathlib.Geometry.Euclidean.Circumcenter
public import Mathlib.Geometry.Euclidean.Sphere.Tangent
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 2013, Problem 6

Let `ABC` be a triangle. Find all points `P` on segment `BC` satisfying the following
property: If `X` and `Y` are the intersections of line `PA` with the common external
tangent lines of the circumcircles of triangles `PAB` and `PAC`, then

  `(PA/XY)² + PB·PC/(AB·AC) = 1`.
-/

open Affine EuclideanGeometry FiniteDimensional Module

open scoped Affine RealInnerProductSpace

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable {V : Type*} {Pt : Type*}

variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]

variable [NormedAddTorsor V Pt] [hd2 : Fact (finrank ℝ V = 2)] {o : Orientation ℝ V (Fin 2)}

local notation "ω" => o.areaForm
local notation "J" => o.rightAngleRotation

namespace Usa2013P6

snip begin

/-!
### Basic toolbox lemmas
-/

omit hd2 in
/-- If `O` is equidistant from `U` and `W`, then `⟪O -ᵥ W, U -ᵥ W⟫ = ‖U -ᵥ W‖^2 / 2`. -/
lemma inner_vsub_eq_half_of_dist_eq {O U W : Pt} (h : dist O U = dist O W) :
    ⟪O -ᵥ W, U -ᵥ W⟫ = ‖U -ᵥ W‖ ^ 2 / 2 := by
  have h1 : ‖O -ᵥ W - (U -ᵥ W)‖ = ‖O -ᵥ W‖ := by
    rw [vsub_sub_vsub_cancel_right]
    rwa [dist_eq_norm_vsub, dist_eq_norm_vsub] at h
  have h2 := congrArg (· ^ 2) h1
  rw [norm_sub_sq_real] at h2
  linarith

omit hd2 in
/-- Pythagoras: if `X -ᵥ Y` and `Z -ᵥ Y` are orthogonal,
then `dist X Z ^ 2 = dist X Y ^ 2 + dist Y Z ^ 2`. -/
lemma dist_sq_eq_add_of_inner_eq_zero {X Y Z : Pt} (h : ⟪X -ᵥ Y, Z -ᵥ Y⟫ = 0) :
    dist X Z ^ 2 = dist X Y ^ 2 + dist Y Z ^ 2 := by
  have h1 : X -ᵥ Z = (X -ᵥ Y) + (Y -ᵥ Z) := by rw [vsub_add_vsub_cancel]
  have h2 : ⟪X -ᵥ Y, Y -ᵥ Z⟫ = 0 := by
    rw [← neg_vsub_eq_vsub_rev Z Y, inner_neg_right, h, neg_zero]
  rw [dist_eq_norm_vsub, h1, norm_add_sq_real, h2, dist_eq_norm_vsub, dist_eq_norm_vsub]
  linarith

/-- The rotation by 90 degrees preserves the norm. -/
lemma norm_rightAngleRotation (x : V) : ‖J x‖ = ‖x‖ :=
  LinearIsometryEquiv.norm_map _ x

/-- The rotation by 90 degrees of a nonzero vector is nonzero. -/
lemma rightAngleRotation_ne_zero {x : V} (hx : x ≠ 0) : J x ≠ 0 := by
  intro hJx
  have h1 : ‖J x‖ = ‖x‖ := norm_rightAngleRotation x
  rw [hJx, norm_zero] at h1
  exact hx (norm_eq_zero.mp h1.symm)

/-- In dimension 2, the orthogonal complement of the span of `n` is the span of `J n`. -/
lemma orthogonal_span_singleton_eq_span_rightAngleRotation {n : V} (hn : n ≠ 0) :
    (ℝ ∙ n : Submodule ℝ V)ᗮ = ℝ ∙ J n := by
  have hJn : J n ≠ 0 := rightAngleRotation_ne_zero hn
  have hle : ℝ ∙ J n ≤ (ℝ ∙ n : Submodule ℝ V)ᗮ := by
    rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_orthogonal]
    intro u hu
    rw [Submodule.mem_span_singleton] at hu
    obtain ⟨r, rfl⟩ := hu
    rw [inner_smul_left, o.inner_rightAngleRotation_right, o.areaForm_apply_self, neg_zero,
      mul_zero]
  have hfin : Module.finrank ℝ (ℝ ∙ n : Submodule ℝ V)ᗮ = 1 := by
    have h1 := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ n : Submodule ℝ V)
    rw [finrank_span_singleton hn, hd2.out] at h1
    omega
  have hfin2 : Module.finrank ℝ (ℝ ∙ J n : Submodule ℝ V) = 1 :=
    finrank_span_singleton hJn
  exact (Submodule.eq_of_le_of_finrank_eq hle (hfin2.trans hfin.symm)).symm

/-- In dimension 2, a vector orthogonal to a nonzero vector `n` is a multiple of `J n`. -/
lemma exists_smul_rightAngleRotation_of_inner_eq_zero {v n : V} (hn : n ≠ 0)
    (h : ⟪v, n⟫ = 0) :
    ∃ μ : ℝ, v = μ • J n := by
  have hv : v ∈ (ℝ ∙ n : Submodule ℝ V)ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro u hu
    rw [Submodule.mem_span_singleton] at hu
    obtain ⟨r, rfl⟩ := hu
    rw [inner_smul_right, h, mul_zero]
  rw [orthogonal_span_singleton_eq_span_rightAngleRotation (o := o) hn,
    Submodule.mem_span_singleton] at hv
  obtain ⟨μ, hμ⟩ := hv
  exact ⟨μ, hμ.symm⟩

/-- The key two-dimensional identity: for `v` orthogonal to `n`,
`⟪v, w⟫ ^ 2 * ‖n‖ ^ 2 = ‖v‖ ^ 2 * ω n w ^ 2`. -/
lemma inner_sq_mul_norm_sq_of_orthogonal {v n w : V} (h : ⟪v, n⟫ = 0) :
    ⟪v, w⟫ ^ 2 * ‖n‖ ^ 2 = ‖v‖ ^ 2 * ω n w ^ 2 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · obtain ⟨μ, rfl⟩ := exists_smul_rightAngleRotation_of_inner_eq_zero (o := o) hn h
    have hsq : (|μ| * ‖n‖) ^ 2 = μ ^ 2 * ‖n‖ ^ 2 := by rw [mul_pow, sq_abs]
    rw [real_inner_smul_left, o.inner_rightAngleRotation_left, norm_smul, Real.norm_eq_abs,
      norm_rightAngleRotation, hsq]
    ring

/-- The squared area form in terms of norms and the inner product. -/
lemma areaForm_sq_eq (x y : V) : ω x y ^ 2 = ‖x‖ ^ 2 * ‖y‖ ^ 2 - ⟪x, y⟫ ^ 2 := by
  have h := o.inner_sq_add_areaForm_sq x y
  linarith

/-!
### Betweenness and collinearity helpers
-/

omit hd2 in
/-- A point weakly between two points and different from the endpoints lies strictly
between. -/
lemma sbtw_of_wbtw {B C P : Pt} (hP : Wbtw ℝ B P C) (hPB : P ≠ B) (hPC : P ≠ C) :
    Sbtw ℝ B P C :=
  ⟨hP, hPB, hPC⟩

omit hd2 in
/-- Strict betweenness in terms of the line map parametrization. -/
lemma exists_lineMap_of_sbtw {B C P : Pt} (h : Sbtw ℝ B P C) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ AffineMap.lineMap B C s = P := by
  rw [sbtw_iff_mem_image_Ioo_and_ne] at h
  obtain ⟨⟨s, hs, rfl⟩, -⟩ := h
  exact ⟨s, hs.1, hs.2, rfl⟩

omit hd2 in
/-- If `P` lies on line `BC` and is different from `B`, then non-collinearity of `A`, `B`,
`C` implies non-collinearity of `P`, `A`, `B`. -/
lemma not_collinear_of_mem_line {A B C P : Pt} (hABC : ¬ Collinear ℝ ({A, B, C} : Set Pt))
    (hP : P ∈ line[ℝ, B, C]) (hPB : P ≠ B) :
    ¬ Collinear ℝ ({P, A, B} : Set Pt) := by
  intro hPAB
  apply hABC
  have hA : A ∈ line[ℝ, P, B] :=
    hPAB.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hPB
  have hsub : line[ℝ, P, B] ≤ line[ℝ, B, C] := by
    rw [affineSpan_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hP, left_mem_affineSpan_pair ℝ B C⟩
  exact collinear_insert_of_mem_affineSpan_pair (hsub hA)

omit hd2 in
/-- Non-collinear points are pairwise distinct (first and second). -/
lemma ne_of_not_collinear₁₂ {A B C : Pt} (h : ¬ Collinear ℝ ({A, B, C} : Set Pt)) :
    A ≠ B := by
  rintro rfl
  simp [collinear_pair] at h

omit hd2 in
/-- Non-collinear points are pairwise distinct (first and third). -/
lemma ne_of_not_collinear₁₃ {A B C : Pt} (h : ¬ Collinear ℝ ({A, B, C} : Set Pt)) :
    A ≠ C := by
  rintro rfl
  simp [collinear_pair] at h

omit hd2 in
/-- Non-collinear points are pairwise distinct (second and third). -/
lemma ne_of_not_collinear₂₃ {A B C : Pt} (h : ¬ Collinear ℝ ({A, B, C} : Set Pt)) :
    B ≠ C := by
  rintro rfl
  simp [collinear_pair] at h

omit hd2 in
/-- Permutation of a non-collinearity hypothesis. -/
lemma not_collinear_perm {A B C : Pt} (h : ¬ Collinear ℝ ({A, B, C} : Set Pt)) :
    ¬ Collinear ℝ ({B, A, C} : Set Pt) := by
  have : ({B, A, C} : Set Pt) = {A, B, C} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [this]
  exact h

omit hd2 in
/-- In a non-degenerate triangle, the strict triangle inequality holds. -/
lemma dist_lt_add_of_not_collinear {A B C : Pt} (h : ¬ Collinear ℝ ({A, B, C} : Set Pt)) :
    dist B C < dist A B + dist A C := by
  have hle : dist B C ≤ dist B A + dist A C := dist_triangle B A C
  rw [dist_comm B A] at hle
  refine lt_of_le_of_ne hle ?_
  intro heq
  rw [dist_comm A B, eq_comm, dist_add_dist_eq_iff] at heq
  exact h (collinear_insert_of_mem_affineSpan_pair (affineSegment_subset_affineSpan ℝ B C heq))

/-- The squared area form is positive for non-collinear points. -/
lemma areaForm_sq_pos_of_not_collinear {A B P : Pt}
    (h : ¬ Collinear ℝ ({P, A, B} : Set Pt)) :
    0 < ω (A -ᵥ P) (B -ᵥ P) ^ 2 := by
  have hAP : A ≠ P := (ne_of_not_collinear₁₂ h).symm
  have hBP : B ≠ P := (ne_of_not_collinear₁₃ h).symm
  have ha' : A -ᵥ P ≠ 0 := vsub_ne_zero.mpr hAP
  have hb' : B -ᵥ P ≠ 0 := vsub_ne_zero.mpr hBP
  have hna : ‖A -ᵥ P‖ ≠ 0 := norm_ne_zero_iff.mpr ha'
  have hnb : ‖B -ᵥ P‖ ≠ 0 := norm_ne_zero_iff.mpr hb'
  have hdep : ∀ t : ℝ, B -ᵥ P ≠ t • (A -ᵥ P) := by
    intro t ht
    apply h
    have hB : B ∈ line[ℝ, P, A] := by
      rw [← vsub_vadd B P, vadd_left_mem_affineSpan_pair]
      exact ⟨t, ht.symm⟩
    have hset : ({B, P, A} : Set Pt) = {P, A, B} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [← hset]
    exact collinear_insert_of_mem_affineSpan_pair hB
  -- strict Cauchy–Schwarz, since the vectors are linearly independent
  have habs : |⟪A -ᵥ P, B -ᵥ P⟫| < ‖A -ᵥ P‖ * ‖B -ᵥ P‖ := by
    rw [abs_lt]
    refine ⟨?_, ?_⟩
    · have h1 : ⟪P -ᵥ A, B -ᵥ P⟫ < ‖P -ᵥ A‖ * ‖B -ᵥ P‖ := by
        rw [inner_lt_norm_mul_iff_real]
        intro hbad
        have hna' : ‖P -ᵥ A‖ ≠ 0 := by
          rw [← neg_vsub_eq_vsub_rev, norm_neg]
          exact hna
        have e := congrArg ((‖P -ᵥ A‖)⁻¹ • ·) hbad
        rw [smul_smul, smul_smul, inv_mul_cancel₀ hna', one_smul] at e
        have h2 : B -ᵥ P = (‖B -ᵥ P‖ / ‖P -ᵥ A‖) • (P -ᵥ A) := by
          rw [div_eq_mul_inv, mul_comm]
          exact e.symm
        exact hdep (-(‖B -ᵥ P‖ / ‖P -ᵥ A‖)) (by
          conv_lhs => rw [h2]
          rw [neg_smul, ← smul_neg, neg_vsub_eq_vsub_rev])
      rwa [← neg_vsub_eq_vsub_rev, inner_neg_left, norm_neg, neg_lt] at h1
    · rw [inner_lt_norm_mul_iff_real]
      intro hbad
      have e := congrArg ((‖A -ᵥ P‖)⁻¹ • ·) hbad
      rw [smul_smul, smul_smul, inv_mul_cancel₀ hna, one_smul] at e
      have h2 : B -ᵥ P = (‖B -ᵥ P‖ / ‖A -ᵥ P‖) • (A -ᵥ P) := by
        rw [div_eq_mul_inv, mul_comm]
        exact e.symm
      exact hdep _ h2
  rw [areaForm_sq_eq]
  have hnn : |‖A -ᵥ P‖ * ‖B -ᵥ P‖| = ‖A -ᵥ P‖ * ‖B -ᵥ P‖ :=
    abs_of_nonneg (by positivity)
  have hsq : ⟪A -ᵥ P, B -ᵥ P⟫ ^ 2 < (‖A -ᵥ P‖ * ‖B -ᵥ P‖) ^ 2 :=
    sq_lt_sq.2 (by rwa [hnn])
  rw [mul_pow] at hsq
  linarith

omit hd2 in
/-- Circumspheres through three non-collinear points exist (from the simplex
circumsphere). -/
lemma exists_sphere_through {U W Z : Pt} (h : ¬ Collinear ℝ ({U, W, Z} : Set Pt)) :
    ∃ s : Sphere Pt, U ∈ s ∧ W ∈ s ∧ Z ∈ s := by
  let T : Affine.Triangle ℝ Pt := ⟨![U, W, Z], affineIndependent_iff_not_collinear_set.2 h⟩
  exact ⟨T.circumsphere,
    T.mem_circumsphere 0, T.mem_circumsphere 1, T.mem_circumsphere 2⟩

/-!
### The relations between the two circumcircles
-/

/-- One-circle computation: if `o₁` has the inner products of a circumcenter of a triangle
with side vectors `x` and `y` emanating from one vertex, then
`‖o₁‖ ^ 2 * (4 * ω x y ^ 2) = ‖x‖ ^ 2 * ‖y‖ ^ 2 * ‖x - y‖ ^ 2`. -/
lemma norm_sq_mul_four_areaForm_sq {x y o₁ : V} (h₁ : ⟪o₁, x⟫ = ‖x‖ ^ 2 / 2)
    (h₂ : ⟪o₁, y⟫ = ‖y‖ ^ 2 / 2) :
    ‖o₁‖ ^ 2 * (4 * ω x y ^ 2) = ‖x‖ ^ 2 * ‖y‖ ^ 2 * ‖x - y‖ ^ 2 := by
  set w := o₁ - (1 / 2 : ℝ) • x with hw
  have hwx : ⟪w, x⟫ = 0 := by
    rw [hw, inner_sub_left, real_inner_smul_left, h₁, real_inner_self_eq_norm_sq]
    ring
  have hwy : ⟪w, y⟫ = (‖y‖ ^ 2 - ⟪x, y⟫) / 2 := by
    rw [hw, inner_sub_left, real_inner_smul_left, h₂]
    ring
  have hnormx : ‖(1 / 2 : ℝ) • x‖ = ‖x‖ / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num)]
    ring
  have hnorm : ‖o₁‖ ^ 2 = ‖w‖ ^ 2 + ‖x‖ ^ 2 / 4 := by
    have ho : o₁ = w + (1 / 2 : ℝ) • x := by rw [hw]; abel
    rw [ho, norm_add_sq_real, real_inner_smul_right, hwx, hnormx]
    ring
  have hid := inner_sq_mul_norm_sq_of_orthogonal (o := o) hwx (w := y)
  have step1 : ‖w‖ ^ 2 * ω x y ^ 2 = ((‖y‖ ^ 2 - ⟪x, y⟫) / 2) ^ 2 * ‖x‖ ^ 2 := by
    rw [← hwy, hid]
  have hω := areaForm_sq_eq (o := o) x y
  have hsub : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * ⟪x, y⟫ + ‖y‖ ^ 2 := norm_sub_sq_real x y
  nlinarith [step1, hnorm, hω, hsub]

/-- The relations between the circumcircles of `PAB` and `PAC`: there is a positive
constant `K` (the squared ratio of the spiral similarity taking `ABC` to `AO₁O₂`) such
that `R₁² = K·c²`, `R₂² = K·b²`, `O₁O₂² = K·a²`, `R₁R₂ = K·b·c` and
`AP²·a² = K·((b+c)²-a²)(a²-(b-c)²)`. -/
lemma center_relations {A B C P : Pt} (hABC : ¬ Collinear ℝ ({A, B, C} : Set Pt))
    (hsbtw : Sbtw ℝ B P C) {s₁ s₂ : Sphere Pt}
    (hA₁ : A ∈ s₁) (hB₁ : B ∈ s₁) (hP₁ : P ∈ s₁)
    (hA₂ : A ∈ s₂) (hC₂ : C ∈ s₂) (hP₂ : P ∈ s₂) :
    ∃ K : ℝ, 0 < K ∧
      s₁.radius ^ 2 = K * dist A B ^ 2 ∧
      s₂.radius ^ 2 = K * dist A C ^ 2 ∧
      dist s₁.center s₂.center ^ 2 = K * dist B C ^ 2 ∧
      s₁.radius * s₂.radius = K * dist A B * dist A C ∧
      dist A P ^ 2 * dist B C ^ 2 =
        K * (((dist A B + dist A C) ^ 2 - dist B C ^ 2) *
          (dist B C ^ 2 - (dist A B - dist A C) ^ 2)) ∧
      s₁.center ≠ s₂.center := by
  -- The statement does not mention `o`, so the section variable is not auto-bound;
  -- introduce an orientation locally (any orientation works, the statement is independent
  -- of the choice) so that `ω` and the two-dimensional lemmas can be applied.
  have o : Orientation ℝ V (Fin 2) := (Module.finBasisOfFinrankEq ℝ V hd2.out).orientation
  obtain ⟨s, hs0, hs1, rfl⟩ := exists_lineMap_of_sbtw hsbtw
  set Ps := AffineMap.lineMap B C s with hPs
  have hPB : Ps ≠ B := hsbtw.2.1
  have hBC : B ≠ C := ne_of_not_collinear₂₃ hABC
  have hPline : Ps ∈ line[ℝ, B, C] := by
    rw [hPs]
    exact AffineMap.lineMap_mem_affineSpan_pair s B C
  have hAP : A ≠ Ps := by
    intro h
    apply hABC
    rw [← h] at hPline
    exact collinear_insert_of_mem_affineSpan_pair hPline
  have hPAB : ¬ Collinear ℝ ({Ps, A, B} : Set Pt) :=
    not_collinear_of_mem_line hABC hPline hPB
  set a' := A -ᵥ Ps with ha'
  set b' := B -ᵥ Ps with hb'
  set c' := C -ᵥ Ps with hc'
  set v' := C -ᵥ B with hv'
  set u := B -ᵥ A with hu
  set w := C -ᵥ A with hw
  have hωpos : 0 < o.areaForm a' b' ^ 2 := areaForm_sq_pos_of_not_collinear (o := o) hPAB
  have h4W : (4 : ℝ) * o.areaForm a' b' ^ 2 ≠ 0 := ne_of_gt (mul_pos (by norm_num) hωpos)
  -- Parametrize the points on line `BC`.
  have hb'v : b' = (-s) • v' := by
    have h1 : Ps -ᵥ B = s • v' := by rw [hPs, AffineMap.lineMap_vsub_left, ← hv']
    rw [hb', ← neg_vsub_eq_vsub_rev, h1, neg_smul]
  have hc'v : c' = (1 - s) • v' := by
    have h1 : Ps -ᵥ C = (1 - s) • (B -ᵥ C) := by rw [hPs, AffineMap.lineMap_vsub_right]
    rw [hc', ← neg_vsub_eq_vsub_rev, h1, hv', ← smul_neg, neg_vsub_eq_vsub_rev]
  set lam := (1 - s) / s with hlamdef
  have hlam : 0 < lam := by rw [hlamdef]; exact div_pos (by linarith) hs0
  have hlam2ne : lam ^ 2 ≠ 0 := pow_ne_zero 2 hlam.ne'
  have hc'b : c' = (-lam) • b' := by
    rw [hc'v, hb'v, smul_smul, hlamdef]
    congr 1
    rw [neg_mul, mul_neg, neg_neg, div_mul_cancel₀ _ hs0.ne']
  have hωac : o.areaForm a' c' = -lam * o.areaForm a' b' := by
    rw [hc'b, map_smul, smul_eq_mul]
  have hnormc : ‖c'‖ = lam * ‖b'‖ := by
    rw [hc'b, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hlam]
  have hnormb : ‖b'‖ = s * ‖v'‖ := by
    rw [hb'v, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hs0]
  -- Distances to the centers.
  have hdA1 : dist A s₁.center = s₁.radius := mem_sphere.mp hA₁
  have hdB1 : dist B s₁.center = s₁.radius := mem_sphere.mp hB₁
  have hdP1 : dist Ps s₁.center = s₁.radius := mem_sphere.mp hP₁
  have hdA2 : dist A s₂.center = s₂.radius := mem_sphere.mp hA₂
  have hdC2 : dist C s₂.center = s₂.radius := mem_sphere.mp hC₂
  have hdP2 : dist Ps s₂.center = s₂.radius := mem_sphere.mp hP₂
  -- The inner products characterizing the two circumcenters.
  have hinner1A : ⟪s₁.center -ᵥ Ps, a'⟫ = ‖a'‖ ^ 2 / 2 := by
    rw [ha']
    exact inner_vsub_eq_half_of_dist_eq (by
      rw [dist_comm s₁.center A, dist_comm s₁.center Ps, hdA1, hdP1])
  have hinner1B : ⟪s₁.center -ᵥ Ps, b'⟫ = ‖b'‖ ^ 2 / 2 := by
    rw [hb']
    exact inner_vsub_eq_half_of_dist_eq (by
      rw [dist_comm s₁.center B, dist_comm s₁.center Ps, hdB1, hdP1])
  have hinner2A : ⟪s₂.center -ᵥ Ps, a'⟫ = ‖a'‖ ^ 2 / 2 := by
    rw [ha']
    exact inner_vsub_eq_half_of_dist_eq (by
      rw [dist_comm s₂.center A, dist_comm s₂.center Ps, hdA2, hdP2])
  have hinner2C : ⟪s₂.center -ᵥ Ps, c'⟫ = ‖c'‖ ^ 2 / 2 := by
    rw [hc']
    exact inner_vsub_eq_half_of_dist_eq (by
      rw [dist_comm s₂.center C, dist_comm s₂.center Ps, hdC2, hdP2])
  have hinner2B : ⟪s₂.center -ᵥ Ps, b'⟫ = -lam * ‖b'‖ ^ 2 / 2 := by
    have h1 := hinner2C
    rw [hnormc, hc'b, real_inner_smul_right] at h1
    have h2 : lam * ⟪s₂.center -ᵥ Ps, b'⟫ = lam * (-lam * ‖b'‖ ^ 2 / 2) := by
      linarith [h1]
    exact mul_left_cancel₀ hlam.ne' h2
  -- Norms of the relevant vectors.
  have hnormO1 : ‖s₁.center -ᵥ Ps‖ = s₁.radius := by
    rw [← dist_eq_norm_vsub, dist_comm s₁.center Ps, hdP1]
  have hnormO2 : ‖s₂.center -ᵥ Ps‖ = s₂.radius := by
    rw [← dist_eq_norm_vsub, dist_comm s₂.center Ps, hdP2]
  have hnormAB : ‖a' - b'‖ = dist A B := by
    rw [ha', hb', vsub_sub_vsub_cancel_right, ← dist_eq_norm_vsub]
  have hnormAC : ‖a' - c'‖ = dist A C := by
    rw [ha', hc', vsub_sub_vsub_cancel_right, ← dist_eq_norm_vsub]
  have hnormv' : ‖v'‖ = dist B C := by
    rw [hv', ← dist_eq_norm_vsub, dist_comm C B]
  -- The three squared-length relations, each scaled by `4 * o.areaForm a' b' ^ 2`.
  have E1 := norm_sq_mul_four_areaForm_sq (o := o) (x := a') (y := b')
    (o₁ := s₁.center -ᵥ Ps) hinner1A hinner1B
  rw [hnormO1, hnormAB] at E1
  have E2 := norm_sq_mul_four_areaForm_sq (o := o) (x := a') (y := c')
    (o₁ := s₂.center -ᵥ Ps) hinner2A hinner2C
  rw [hnormO2, hnormAC, hωac, hnormc] at E2
  have E2' : s₂.radius ^ 2 * (4 * o.areaForm a' b' ^ 2) = ‖a'‖ ^ 2 * ‖b'‖ ^ 2 * dist A C ^ 2 := by
    refine mul_right_cancel₀ hlam2ne ?_
    linear_combination E2
  have hinnerv_a : ⟪s₂.center -ᵥ Ps - (s₁.center -ᵥ Ps), a'⟫ = 0 := by
    rw [inner_sub_left, hinner2A, hinner1A, sub_self]
  have hinnerv_b : ⟪s₂.center -ᵥ Ps - (s₁.center -ᵥ Ps), b'⟫ =
      -(1 + lam) * ‖b'‖ ^ 2 / 2 := by
    rw [inner_sub_left, hinner2B, hinner1B]
    ring
  have hav : c' - b' = v' := by rw [hc', hb', vsub_sub_vsub_cancel_right, ← hv']
  have hv'b : v' = (-(1 + lam)) • b' := by
    rw [← hav, hc'b]
    rw [show (-(1 + lam) : ℝ) = -lam - 1 by ring, sub_smul, one_smul]
  have hnormv'b : ‖v'‖ = (1 + lam) * ‖b'‖ := by
    rw [hv'b, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (by linarith [hlam])]
  have hnormv : ‖s₂.center -ᵥ Ps - (s₁.center -ᵥ Ps)‖ = dist s₁.center s₂.center := by
    rw [vsub_sub_vsub_cancel_right, ← dist_eq_norm_vsub, dist_comm s₂.center s₁.center]
  have E3raw := inner_sq_mul_norm_sq_of_orthogonal (o := o)
    (v := s₂.center -ᵥ Ps - (s₁.center -ᵥ Ps)) (n := a') (w := b') hinnerv_a
  rw [hinnerv_b, hnormv] at E3raw
  have E3' : dist s₁.center s₂.center ^ 2 * (4 * o.areaForm a' b' ^ 2) =
      ‖a'‖ ^ 2 * ‖b'‖ ^ 2 * dist B C ^ 2 := by
    rw [← hnormv', hnormv'b]
    linarith [E3raw]
  -- The proportionality constant `K`.
  set K := ‖a'‖ ^ 2 * ‖b'‖ ^ 2 / (4 * o.areaForm a' b' ^ 2) with hKdef
  have hKpos : 0 < K := by
    rw [hKdef]
    have hna : 0 < ‖a'‖ := norm_pos_iff.mpr (vsub_ne_zero.mpr hAP)
    have hnb : 0 < ‖b'‖ := norm_pos_iff.mpr (vsub_ne_zero.mpr hPB.symm)
    exact div_pos (mul_pos (pow_pos hna _) (pow_pos hnb _)) (mul_pos (by norm_num) hωpos)
  have hK : K * (4 * o.areaForm a' b' ^ 2) = ‖a'‖ ^ 2 * ‖b'‖ ^ 2 := by
    rw [hKdef]
    exact div_mul_cancel₀ _ h4W
  have hR1 : s₁.radius ^ 2 = K * dist A B ^ 2 := by
    refine mul_right_cancel₀ h4W ?_
    linear_combination E1 - dist A B ^ 2 * hK
  have hR2 : s₂.radius ^ 2 = K * dist A C ^ 2 := by
    refine mul_right_cancel₀ h4W ?_
    linear_combination E2' - dist A C ^ 2 * hK
  have hd : dist s₁.center s₂.center ^ 2 = K * dist B C ^ 2 := by
    refine mul_right_cancel₀ h4W ?_
    linear_combination E3' - dist B C ^ 2 * hK
  -- The product of the two radii, from the squared relations.
  have hsq12 : (s₁.radius * s₂.radius) ^ 2 = (K * dist A B * dist A C) ^ 2 := by
    rw [mul_pow, hR1, hR2]
    ring
  have hR1R2 : s₁.radius * s₂.radius = K * dist A B * dist A C := by
    have h1 : 0 ≤ s₁.radius := Sphere.radius_nonneg_of_mem hA₁
    have h2 : 0 ≤ s₂.radius := Sphere.radius_nonneg_of_mem hA₂
    exact (sq_eq_sq₀ (mul_nonneg h1 h2)
      (mul_nonneg (mul_nonneg hKpos.le dist_nonneg) dist_nonneg)).mp hsq12
  -- The Heron-type identity for `AP² · BC²`.
  have huv : v' = w - u := by rw [hw, hu, vsub_sub_vsub_cancel_right, ← hv']
  have hab : a' = -u + b' := by
    rw [ha', hu, neg_vsub_eq_vsub_rev, hb', vsub_add_vsub_cancel]
  have hωab_s : o.areaForm a' b' = s * o.areaForm u w := by
    have h1 : o.areaForm a' b' = -o.areaForm u b' := by
      rw [hab, map_add, LinearMap.add_apply, map_neg, LinearMap.neg_apply,
        o.areaForm_apply_self, add_zero]
    rw [h1, hb'v, huv, map_smul, smul_eq_mul, map_sub, o.areaForm_apply_self, sub_zero]
    ring
  have hnormu : ‖u‖ = dist A B := by rw [hu, ← dist_eq_norm_vsub, dist_comm B A]
  have hnormw : ‖w‖ = dist A C := by rw [hw, ← dist_eq_norm_vsub, dist_comm C A]
  have hnormuw : ‖u - w‖ = dist B C := by
    rw [hu, hw, vsub_sub_vsub_cancel_right, ← dist_eq_norm_vsub]
  have hinner_uw : ⟪u, w⟫ = (dist A B ^ 2 + dist A C ^ 2 - dist B C ^ 2) / 2 := by
    have h := norm_sub_sq_real u w
    rw [hnormuw, hnormu, hnormw] at h
    linarith
  have hHeron : 4 * o.areaForm u w ^ 2 =
      ((dist A B + dist A C) ^ 2 - dist B C ^ 2) *
        (dist B C ^ 2 - (dist A B - dist A C) ^ 2) := by
    rw [areaForm_sq_eq (o := o), hnormu, hnormw, hinner_uw]
    ring
  have hnorma : ‖a'‖ = dist A Ps := by rw [ha', ← dist_eq_norm_vsub]
  have hKω : K * (4 * o.areaForm u w ^ 2) = ‖a'‖ ^ 2 * ‖v'‖ ^ 2 := by
    refine mul_right_cancel₀ (pow_ne_zero 2 hs0.ne') ?_
    have hK2 := hK
    rw [hωab_s, hnormb] at hK2
    linear_combination hK2
  have hAPsq : dist A Ps ^ 2 * dist B C ^ 2 =
      K * (((dist A B + dist A C) ^ 2 - dist B C ^ 2) *
        (dist B C ^ 2 - (dist A B - dist A C) ^ 2)) := by
    rw [← hHeron, ← hnorma, ← hnormv']
    exact hKω.symm
  -- The two centers are distinct.
  have hcenters : s₁.center ≠ s₂.center := by
    intro hO
    have hdOB : dist s₁.center B = dist s₁.center Ps := by
      rw [dist_comm s₁.center B, dist_comm s₁.center Ps, hdB1, hdP1]
    have hdOC : dist s₁.center C = dist s₁.center Ps := by
      rw [hO, dist_comm s₂.center C, dist_comm s₂.center Ps, hdC2, hdP2]
    have hCBv : C -ᵥ s₁.center = v' + (B -ᵥ s₁.center) := by
      rw [← vsub_add_vsub_cancel C B s₁.center, hv']
    have hPBv : Ps -ᵥ s₁.center = s • v' + (B -ᵥ s₁.center) := by
      have h1 : Ps -ᵥ B = s • v' := by rw [hPs, AffineMap.lineMap_vsub_left, ← hv']
      rw [← vsub_add_vsub_cancel Ps B s₁.center, h1]
    have e0 : dist s₁.center Ps ^ 2 = ‖B -ᵥ s₁.center‖ ^ 2 := by
      rw [← hdOB, dist_comm s₁.center B, dist_eq_norm_vsub]
    have e1 : dist s₁.center Ps ^ 2 =
        ‖v'‖ ^ 2 + 2 * ⟪v', B -ᵥ s₁.center⟫ + ‖B -ᵥ s₁.center‖ ^ 2 := by
      rw [← hdOC, dist_comm s₁.center C, dist_eq_norm_vsub, hCBv, norm_add_sq_real]
    have es : dist s₁.center Ps ^ 2 =
        s ^ 2 * ‖v'‖ ^ 2 + 2 * s * ⟪v', B -ᵥ s₁.center⟫ + ‖B -ᵥ s₁.center‖ ^ 2 := by
      rw [dist_comm s₁.center Ps, dist_eq_norm_vsub, hPBv, norm_add_sq_real, norm_smul,
        real_inner_smul_left, Real.norm_eq_abs, abs_of_pos hs0]
      ring
    have hv'ne : v' ≠ 0 := by
      rw [hv']
      exact vsub_ne_zero.mpr hBC.symm
    have hE1 : ‖v'‖ ^ 2 + 2 * ⟪v', B -ᵥ s₁.center⟫ = 0 := by linarith [e0, e1]
    have hE2 : s * (s * ‖v'‖ ^ 2 + 2 * ⟪v', B -ᵥ s₁.center⟫) = 0 := by linarith [e0, es]
    have hE3 : s * ‖v'‖ ^ 2 + 2 * ⟪v', B -ᵥ s₁.center⟫ = 0 := by
      rcases mul_eq_zero.mp hE2 with h | h
      · exact absurd h hs0.ne'
      · exact h
    have hE4 : (1 - s) * ‖v'‖ ^ 2 = 0 := by linarith [hE1, hE3]
    rcases mul_eq_zero.mp hE4 with h | h
    · have hs1' : s = 1 := by linarith
      linarith
    · exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hv'ne) h
  exact ⟨K, hKpos, hR1, hR2, hd, hR1R2, hAPsq, hcenters⟩

/-!
### Tangent line geometry
-/

/-- Two spheres through two distinct points `A` and `P` with distinct centers satisfy the
strict inequality `(R₁ - R₂)² < d²` (they are "properly intersecting"). -/
lemma dist_sq_sub_sq_pos (V : Type*) {Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace Pt] [NormedAddTorsor V Pt] [Fact (finrank ℝ V = 2)] {s₁ s₂ : Sphere Pt} {A P : Pt}
    (hA₁ : A ∈ s₁) (hP₁ : P ∈ s₁)
    (hA₂ : A ∈ s₂) (hP₂ : P ∈ s₂) (hAP : A ≠ P) (hcenters : s₁.center ≠ s₂.center) :
    (s₁.radius - s₂.radius) ^ 2 < dist s₁.center s₂.center ^ 2 := by
  set a' := A -ᵥ P with ha'
  have hR₁ : 0 < s₁.radius := by
    have h1 := s₁.radius_nonneg_of_mem hA₁
    have h2 : s₁.radius ≠ 0 := by
      intro hr
      rw [mem_sphere, hr, dist_eq_zero] at hA₁ hP₁
      exact hAP (hA₁.trans hP₁.symm)
    exact lt_of_le_of_ne h1 h2.symm
  have hR₂ : 0 < s₂.radius := by
    have h1 := s₂.radius_nonneg_of_mem hA₂
    have h2 : s₂.radius ≠ 0 := by
      intro hr
      rw [mem_sphere, hr, dist_eq_zero] at hA₂ hP₂
      exact hAP (hA₂.trans hP₂.symm)
    exact lt_of_le_of_ne h1 h2.symm
  have hdA₁ : dist s₁.center A = s₁.radius := by rw [dist_comm]; exact mem_sphere.1 hA₁
  have hdP₁ : dist s₁.center P = s₁.radius := by rw [dist_comm]; exact mem_sphere.1 hP₁
  have hdA₂ : dist s₂.center A = s₂.radius := by rw [dist_comm]; exact mem_sphere.1 hA₂
  have hdP₂ : dist s₂.center P = s₂.radius := by rw [dist_comm]; exact mem_sphere.1 hP₂
  have h1 : ⟪s₁.center -ᵥ P, a'⟫ = ‖a'‖ ^ 2 / 2 :=
    inner_vsub_eq_half_of_dist_eq (hdA₁.trans hdP₁.symm)
  have h3 : ⟪s₂.center -ᵥ P, a'⟫ = ‖a'‖ ^ 2 / 2 :=
    inner_vsub_eq_half_of_dist_eq (hdA₂.trans hdP₂.symm)
  have hperp1 : ⟪A -ᵥ s₁.center, a'⟫ = ‖a'‖ ^ 2 / 2 := by
    have e : A -ᵥ s₁.center = a' - (s₁.center -ᵥ P) := by
      rw [ha', vsub_sub_vsub_cancel_right]
    rw [e, inner_sub_left, h1, real_inner_self_eq_norm_sq]
    ring
  have hperp2 : ⟪A -ᵥ s₂.center, a'⟫ = ‖a'‖ ^ 2 / 2 := by
    have e : A -ᵥ s₂.center = a' - (s₂.center -ᵥ P) := by
      rw [ha', vsub_sub_vsub_cancel_right]
    rw [e, inner_sub_left, h3, real_inner_self_eq_norm_sq]
    ring
  have ha'0 : a' ≠ 0 := vsub_ne_zero.mpr hAP
  -- the key non-vanishing vector
  have hz : s₂.radius • (A -ᵥ s₁.center) - s₁.radius • (A -ᵥ s₂.center) ≠ 0 := by
    intro hz0
    have heq : s₂.radius • (A -ᵥ s₁.center) = s₁.radius • (A -ᵥ s₂.center) :=
      sub_eq_zero.mp hz0
    have hinner := congrArg (fun w => ⟪w, a'⟫) heq
    rw [real_inner_smul_left, real_inner_smul_left, hperp1, hperp2] at hinner
    have hn : (0:ℝ) < ‖a'‖ ^ 2 / 2 := by positivity [norm_pos_iff.mpr ha'0]
    have hRR : s₂.radius = s₁.radius := mul_right_cancel₀ hn.ne' hinner
    rw [hRR] at heq
    have hAeq : A -ᵥ s₁.center = A -ᵥ s₂.center := by
      have h := congrArg ((s₁.radius)⁻¹ • ·) heq
      rw [smul_smul, smul_smul, inv_mul_cancel₀ hR₁.ne', one_smul, one_smul] at h
      exact h
    have hz0 : s₂.center -ᵥ s₁.center = 0 := by
      have e : (A -ᵥ s₁.center) - (A -ᵥ s₂.center) = 0 := sub_eq_zero.mpr hAeq
      rw [vsub_sub_vsub_cancel_left] at e
      exact e
    exact hcenters (vsub_eq_zero_iff_eq.mp hz0).symm
  -- expand ‖z‖² > 0
  have hz2 : 0 < ‖s₂.radius • (A -ᵥ s₁.center) - s₁.radius • (A -ᵥ s₂.center)‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr hz) 2
  have hdX₁ : ‖A -ᵥ s₁.center‖ = s₁.radius := by
    rw [← dist_eq_norm_vsub]; exact mem_sphere.1 hA₁
  have hdX₂ : ‖A -ᵥ s₂.center‖ = s₂.radius := by
    rw [← dist_eq_norm_vsub]; exact mem_sphere.1 hA₂
  rw [norm_sub_sq_real, norm_smul, norm_smul, hdX₁, hdX₂, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hR₁, abs_of_pos hR₂, real_inner_smul_left, real_inner_smul_right] at hz2
  have hd : dist s₁.center s₂.center ^ 2 =
      s₁.radius ^ 2 + s₂.radius ^ 2 - 2 * ⟪A -ᵥ s₁.center, A -ᵥ s₂.center⟫ := by
    rw [dist_eq_norm_vsub]
    have e : s₁.center -ᵥ s₂.center = (A -ᵥ s₂.center) - (A -ᵥ s₁.center) := by
      rw [vsub_sub_vsub_cancel_left]
    rw [e, norm_sub_sq_real, hdX₁, hdX₂, real_inner_comm (A -ᵥ s₂.center)]
    ring
  have hI : ⟪A -ᵥ s₁.center, A -ᵥ s₂.center⟫ < s₁.radius * s₂.radius := by
    have h2 : (s₁.radius * s₂.radius) * ⟪A -ᵥ s₁.center, A -ᵥ s₂.center⟫ <
        (s₁.radius * s₂.radius) * (s₁.radius * s₂.radius) := by
      nlinarith [hz2]
    exact lt_of_mul_lt_mul_left h2 (mul_nonneg hR₁.le hR₂.le)
  rw [hd]
  nlinarith [hI]

/-- For a common external tangent line `ℓ` of two spheres `s₁`, `s₂` which both pass
through two distinct points `A` and `P`, with `X` the intersection of `ℓ` with line `PA`:
there are tangency points `X₁`, `X₂` on the two spheres such that `ℓ` is the tangent
space at those points, the radii to the tangency points are parallel and point to the
same side, and `X` is the midpoint of `X₁X₂`. -/
lemma exists_tangentPoints_of_mem_commonExtTangents {s₁ s₂ : Sphere Pt} {A P X : Pt}
    {ℓ : AffineSubspace ℝ Pt}
    (hA₁ : A ∈ s₁) (hP₁ : P ∈ s₁) (hA₂ : A ∈ s₂) (hP₂ : P ∈ s₂) (hAP : A ≠ P)
    (hcenters : s₁.center ≠ s₂.center)
    (hℓ : ℓ ∈ s₁.commonExtTangents s₂) (hXℓ : X ∈ ℓ) (hXline : X ∈ line[ℝ, P, A]) :
    ∃ X₁ X₂ : Pt, X₁ ∈ s₁ ∧ X₂ ∈ s₂ ∧ ℓ = s₁.orthRadius X₁ ∧ ℓ = s₂.orthRadius X₂ ∧
      X₂ -ᵥ s₂.center = (s₂.radius / s₁.radius) • (X₁ -ᵥ s₁.center) ∧
      X = midpoint ℝ X₁ X₂ := by
  -- unpack the common external tangent
  rw [Sphere.mem_commonExtTangents_iff, Sphere.mem_commonTangents_iff] at hℓ
  obtain ⟨⟨⟨X₁, hX₁, hℓ₁⟩, ⟨X₂, hX₂, hℓ₂⟩⟩, hext⟩ := hℓ
  -- radii are positive
  have hR₁ : 0 < s₁.radius := by
    have h1 := s₁.radius_nonneg_of_mem hA₁
    have h2 : s₁.radius ≠ 0 := by
      intro hr
      rw [mem_sphere, hr, dist_eq_zero] at hA₁ hP₁
      exact hAP (hA₁.trans hP₁.symm)
    exact lt_of_le_of_ne h1 h2.symm
  have hR₂ : 0 < s₂.radius := by
    have h1 := s₂.radius_nonneg_of_mem hA₂
    have h2 : s₂.radius ≠ 0 := by
      intro hr
      rw [mem_sphere, hr, dist_eq_zero] at hA₂ hP₂
      exact hAP (hA₂.trans hP₂.symm)
    exact lt_of_le_of_ne h1 h2.symm
  -- the tangency points lie on ℓ
  have hX₁ℓ : X₁ ∈ ℓ := hℓ₁ ▸ s₁.self_mem_orthRadius X₁
  have hX₂ℓ : X₂ ∈ ℓ := hℓ₂ ▸ s₂.self_mem_orthRadius X₂
  set u := X₁ -ᵥ s₁.center with hu
  set v := X₂ -ᵥ s₂.center with hv
  have hu0 : u ≠ 0 := by
    have hd : dist X₁ s₁.center = s₁.radius := mem_sphere.1 hX₁
    have hne : X₁ ≠ s₁.center := by
      intro hc
      rw [hc, dist_self] at hd
      exact hR₁.ne' hd.symm
    exact vsub_ne_zero.mpr hne
  have hnu : ‖u‖ = s₁.radius := by rw [hu, ← dist_eq_norm_vsub]; exact mem_sphere.1 hX₁
  have hnv : ‖v‖ = s₂.radius := by rw [hv, ← dist_eq_norm_vsub]; exact mem_sphere.1 hX₂
  -- the two radius vectors are parallel: v = ρ • u
  have hdir : ℓ.direction = (ℝ ∙ u : Submodule ℝ V)ᗮ := by
    rw [← hℓ₁, Sphere.direction_orthRadius]
  have hvorth : v ∈ (ℓ.direction)ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro w hw
    have hwd : w ∈ (ℝ ∙ v : Submodule ℝ V)ᗮ := by
      have hw2 : ℓ.direction = (ℝ ∙ v : Submodule ℝ V)ᗮ := by
        rw [← hℓ₂, Sphere.direction_orthRadius, hv]
      rw [hw2] at hw
      exact hw
    exact Submodule.inner_right_of_mem_orthogonal (Submodule.mem_span_singleton_self v) hwd
  have horth : (ℓ.direction)ᗮ = ℝ ∙ u := by
    rw [hdir, Submodule.orthogonal_orthogonal]
  rw [horth, Submodule.mem_span_singleton] at hvorth
  obtain ⟨ρ, hρ⟩ := hvorth
  -- the chain identity
  have hchain : s₂.center -ᵥ s₁.center = (X₂ -ᵥ X₁) + (1 - ρ) • u := by
    have e : s₂.center -ᵥ s₁.center = (X₂ -ᵥ X₁) + u - v := by
      rw [hu, hv, vsub_add_vsub_cancel X₂ X₁ s₁.center, vsub_sub_vsub_cancel_left]
    rw [e, ← hρ, sub_smul, one_smul]
    module
  -- ρ ≥ 0, using the external condition
  have hρnonneg : 0 ≤ ρ := by
    by_contra hneg
    have hρlt : ρ < 0 := not_le.mp hneg
    have hs0pos : (0:ℝ) < 1 / (1 - ρ) := one_div_pos.mpr (by linarith)
    have hs0lt : (1:ℝ) / (1 - ρ) < 1 := by
      rw [div_lt_one (by linarith : (0:ℝ) < 1 - ρ)]
      linarith
    have hs0mul : (1 / (1 - ρ)) * (1 - ρ) = 1 :=
      div_mul_cancel₀ 1 (by linarith : (1:ℝ) - ρ ≠ 0)
    have hQmem : ((1 / (1 - ρ)) • (X₂ -ᵥ X₁) +ᵥ X₁) ∈ ℓ :=
      AffineSubspace.vadd_mem_of_mem_direction
        (Submodule.smul_mem _ _ (AffineSubspace.vsub_mem_direction hX₂ℓ hX₁ℓ)) hX₁ℓ
    have hQeq : (1 / (1 - ρ)) • (X₂ -ᵥ X₁) +ᵥ X₁ =
        AffineMap.lineMap s₁.center s₂.center (1 / (1 - ρ)) := by
      apply vsub_left_injective s₁.center
      dsimp only
      rw [vadd_vsub_assoc, AffineMap.lineMap_vsub_left, hchain, smul_add, smul_smul, hs0mul,
        one_smul, ← hu]
    have hSbtw : Sbtw ℝ s₁.center
        (AffineMap.lineMap s₁.center s₂.center (1 / (1 - ρ))) s₂.center := by
      rw [sbtw_lineMap_iff]
      exact ⟨hcenters, hs0pos, hs0lt⟩
    rw [← hQeq] at hSbtw
    exact hext _ hQmem hSbtw
  -- ρ = R₂ / R₁
  have hρval : ρ = s₂.radius / s₁.radius := by
    have h1 : ‖ρ • u‖ = ‖v‖ := by rw [hρ]
    rw [norm_smul, Real.norm_eq_abs, hnu, hnv] at h1
    have h2 : |ρ| = s₂.radius / s₁.radius := by
      rw [eq_div_iff hR₁.ne']
      exact h1
    rw [abs_of_nonneg hρnonneg] at h2
    exact h2
  have hρR : ρ * s₁.radius = s₂.radius := by rw [hρval, div_mul_cancel₀ _ hR₁.ne']
  -- the tangency points are distinct
  have hX1neX2 : X₁ ≠ X₂ := by
    intro he
    have hchain0 : s₂.center -ᵥ s₁.center = (1 - ρ) • u := by
      rw [hchain, he, vsub_self, zero_add]
    have hdsq : dist s₁.center s₂.center ^ 2 = (s₁.radius - s₂.radius) ^ 2 := by
      have h1 : ‖(1 - ρ) • u‖ ^ 2 = (1 - ρ) ^ 2 * s₁.radius ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hnu]
      rw [dist_eq_norm_vsub, ← neg_vsub_eq_vsub_rev, norm_neg, hchain0, h1]
      nlinarith [hρR]
    have hpos := dist_sq_sub_sq_pos V hA₁ hP₁ hA₂ hP₂ hAP hcenters
    rw [hdsq] at hpos
    exact lt_irrefl _ hpos
  -- the tangency points as tangent spaces
  have htan1 : s₁.IsTangentAt X₁ ℓ := hℓ₁ ▸ (Sphere.isTangentAt_orthRadius_iff_mem.2 hX₁)
  have htan2 : s₂.IsTangentAt X₂ ℓ := hℓ₂ ▸ (Sphere.isTangentAt_orthRadius_iff_mem.2 hX₂)
  have hd1 : dist X s₁.center ^ 2 = s₁.radius ^ 2 + dist X X₁ ^ 2 :=
    htan1.dist_sq_eq_of_mem hXℓ
  have hd2' : dist X s₂.center ^ 2 = s₂.radius ^ 2 + dist X X₂ ^ 2 :=
    htan2.dist_sq_eq_of_mem hXℓ
  -- the midpoint M of AP and perpendicularity facts
  have hdA₁ : dist s₁.center A = s₁.radius := by rw [dist_comm]; exact mem_sphere.1 hA₁
  have hdP₁ : dist s₁.center P = s₁.radius := by rw [dist_comm]; exact mem_sphere.1 hP₁
  have hdA₂ : dist s₂.center A = s₂.radius := by rw [dist_comm]; exact mem_sphere.1 hA₂
  have hdP₂ : dist s₂.center P = s₂.radius := by rw [dist_comm]; exact mem_sphere.1 hP₂
  have h1 : ⟪s₁.center -ᵥ P, A -ᵥ P⟫ = ‖A -ᵥ P‖ ^ 2 / 2 :=
    inner_vsub_eq_half_of_dist_eq (hdA₁.trans hdP₁.symm)
  have h3 : ⟪s₂.center -ᵥ P, A -ᵥ P⟫ = ‖A -ᵥ P‖ ^ 2 / 2 :=
    inner_vsub_eq_half_of_dist_eq (hdA₂.trans hdP₂.symm)
  have h2eq : (⅟2 : ℝ) = 1 / 2 := by rw [invOf_eq_inv, one_div]
  set M := midpoint ℝ A P with hM
  have hMP : M -ᵥ P = (1 / 2 : ℝ) • (A -ᵥ P) := by
    rw [hM, ← h2eq]
    exact midpoint_vsub_right A P
  have hO₁M : s₁.center -ᵥ M = (s₁.center -ᵥ P) - (1 / 2 : ℝ) • (A -ᵥ P) := by
    rw [← hMP, vsub_sub_vsub_cancel_right]
  have hO₂M : s₂.center -ᵥ M = (s₂.center -ᵥ P) - (1 / 2 : ℝ) • (A -ᵥ P) := by
    rw [← hMP, vsub_sub_vsub_cancel_right]
  have hperp1 : ⟪s₁.center -ᵥ M, A -ᵥ P⟫ = 0 := by
    rw [hO₁M, inner_sub_left, real_inner_smul_left, h1, real_inner_self_eq_norm_sq]
    ring
  have hperp2 : ⟪s₂.center -ᵥ M, A -ᵥ P⟫ = 0 := by
    rw [hO₂M, inner_sub_left, real_inner_smul_left, h3, real_inner_self_eq_norm_sq]
    ring
  have hperp1' : ⟪A -ᵥ P, s₁.center -ᵥ M⟫ = 0 := inner_eq_zero_symm.mp hperp1
  have hperp2' : ⟪A -ᵥ P, s₂.center -ᵥ M⟫ = 0 := inner_eq_zero_symm.mp hperp2
  -- M lies on line PA
  have hMline : M ∈ line[ℝ, P, A] := by
    have h1 : M ∈ line[ℝ, A, P] := by
      have h2 : M = (1 / 2 : ℝ) • (P -ᵥ A) +ᵥ A := by
        have h3 : M -ᵥ A = (1 / 2 : ℝ) • (P -ᵥ A) := by
          rw [hM, ← h2eq]
          exact midpoint_vsub_left A P
        rw [← h3, vsub_vadd]
      rw [h2, vadd_left_mem_affineSpan_pair]
      exact ⟨1 / 2, rfl⟩
    rw [Set.pair_comm A P] at h1
    exact h1
  -- X -ᵥ M is a multiple of P -ᵥ A
  have hXMd : X -ᵥ M ∈ (line[ℝ, P, A]).direction :=
    AffineSubspace.vsub_mem_direction hXline hMline
  rw [direction_affineSpan, vectorSpan_pair] at hXMd
  rw [Submodule.mem_span_singleton] at hXMd
  obtain ⟨τ, hτ⟩ := hXMd
  have hPA : P -ᵥ A = -(A -ᵥ P) := (neg_vsub_eq_vsub_rev _ _).symm
  have hperpX1 : ⟪X -ᵥ M, s₁.center -ᵥ M⟫ = 0 := by
    rw [← hτ, real_inner_smul_left, hPA, inner_neg_left, hperp1', neg_zero, mul_zero]
  have hperpX2 : ⟪X -ᵥ M, s₂.center -ᵥ M⟫ = 0 := by
    rw [← hτ, real_inner_smul_left, hPA, inner_neg_left, hperp2', neg_zero, mul_zero]
  have hpy1 : dist X s₁.center ^ 2 = dist X M ^ 2 + dist M s₁.center ^ 2 :=
    dist_sq_eq_add_of_inner_eq_zero hperpX1
  have hpy2 : dist X s₂.center ^ 2 = dist X M ^ 2 + dist M s₂.center ^ 2 :=
    dist_sq_eq_add_of_inner_eq_zero hperpX2
  have hAvM : A -ᵥ M = (1 / 2 : ℝ) • (A -ᵥ P) := by
    rw [hM, ← h2eq]
    exact left_vsub_midpoint A P
  have hperpA1 : ⟪A -ᵥ M, s₁.center -ᵥ M⟫ = 0 := by
    rw [hAvM, real_inner_smul_left, hperp1', mul_zero]
  have hperpA2 : ⟪A -ᵥ M, s₂.center -ᵥ M⟫ = 0 := by
    rw [hAvM, real_inner_smul_left, hperp2', mul_zero]
  have hpyA1 : dist A s₁.center ^ 2 = dist A M ^ 2 + dist M s₁.center ^ 2 :=
    dist_sq_eq_add_of_inner_eq_zero hperpA1
  have hpyA2 : dist A s₂.center ^ 2 = dist A M ^ 2 + dist M s₂.center ^ 2 :=
    dist_sq_eq_add_of_inner_eq_zero hperpA2
  have hAM : dist A M = dist A P / 2 := by
    rw [dist_eq_norm_vsub, hAvM, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2), ← dist_eq_norm_vsub]
    ring
  -- equal tangent lengths from X
  have hdA₁' : dist A s₁.center = s₁.radius := mem_sphere.1 hA₁
  have hdA₂' : dist A s₂.center = s₂.radius := mem_sphere.1 hA₂
  have hdA₁'sq : dist A s₁.center ^ 2 = s₁.radius ^ 2 := by rw [hdA₁']
  have hdA₂'sq : dist A s₂.center ^ 2 = s₂.radius ^ 2 := by rw [hdA₂']
  have hXX1 : dist X X₁ ^ 2 = dist X M ^ 2 - dist A M ^ 2 := by
    linear_combination -hd1 + hpy1 - hpyA1 + hdA₁'sq
  have hXX2 : dist X X₂ ^ 2 = dist X M ^ 2 - dist A M ^ 2 := by
    linear_combination -hd2' + hpy2 - hpyA2 + hdA₂'sq
  have hXX : dist X X₁ = dist X X₂ := by
    have h := hXX1.trans hXX2.symm
    exact (sq_eq_sq₀ dist_nonneg dist_nonneg).mp h
  -- X is a scalar multiple along the tangent line
  have hX1X2d : X₂ -ᵥ X₁ ∈ ℓ.direction := AffineSubspace.vsub_mem_direction hX₂ℓ hX₁ℓ
  have hXX1d : X -ᵥ X₁ ∈ ℓ.direction := AffineSubspace.vsub_mem_direction hXℓ hX₁ℓ
  have hdirfin : Module.finrank ℝ ℓ.direction = 1 := by
    rw [hdir]
    have h1 := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ u : Submodule ℝ V)
    rw [finrank_span_singleton hu0, hd2.out] at h1
    omega
  have hspan : (ℝ ∙ (X₂ -ᵥ X₁) : Submodule ℝ V) = ℓ.direction := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_singleton_le_iff_mem]
      exact hX1X2d
    · rw [finrank_span_singleton (vsub_ne_zero.mpr (Ne.symm hX1neX2)), hdirfin]
  rw [← hspan, Submodule.mem_span_singleton] at hXX1d
  obtain ⟨σ, hσ⟩ := hXX1d
  have hD0 : ‖X₂ -ᵥ X₁‖ ≠ 0 := norm_ne_zero_iff.mpr (vsub_ne_zero.mpr (Ne.symm hX1neX2))
  have hσ1 : dist X X₁ = |σ| * ‖X₂ -ᵥ X₁‖ := by
    rw [dist_eq_norm_vsub, ← hσ, norm_smul, Real.norm_eq_abs]
  have hσ2 : dist X X₂ = |1 - σ| * ‖X₂ -ᵥ X₁‖ := by
    have e : X -ᵥ X₂ = (σ - 1) • (X₂ -ᵥ X₁) := by
      have e1 : X -ᵥ X₂ = (X -ᵥ X₁) - (X₂ -ᵥ X₁) := by rw [vsub_sub_vsub_cancel_right]
      rw [e1, ← hσ]
      module
    rw [dist_eq_norm_vsub, e, norm_smul, Real.norm_eq_abs, abs_sub_comm σ 1]
  have hσabs : |σ| = |1 - σ| := by
    have h := hXX
    rw [hσ1, hσ2] at h
    exact mul_right_cancel₀ hD0 h
  have hσval : σ = 1 / 2 := by
    rw [abs_eq_abs] at hσabs
    rcases hσabs with h | h
    · linarith
    · linarith
  have hfinal : X = midpoint ℝ X₁ X₂ := by
    have h1 : X -ᵥ X₁ = (1 / 2 : ℝ) • (X₂ -ᵥ X₁) := by rw [← hσ, hσval]
    have h2 : midpoint ℝ X₁ X₂ -ᵥ X₁ = (1 / 2 : ℝ) • (X₂ -ᵥ X₁) := by
      rw [← h2eq]
      exact midpoint_vsub_left X₁ X₂
    exact (vsub_left_injective X₁).eq_iff.mp (h1.trans h2.symm)
  exact ⟨X₁, X₂, hX₁, hX₂, hℓ₁.symm, hℓ₂.symm, by rw [← hv, ← hρ, hρval, ← hu], hfinal⟩

omit hd2 in
/-- The squared tangent length from a point `X` of the tangent space `ℓ = s.orthRadius X₁`
to the tangency point, where `X` lies on line `PA` and `A`, `P` are on the sphere:
equals `dist X M ^ 2 - (dist A P / 2)^2` with `M` the midpoint of `AP`. -/
lemma dist_sq_tangent_sub {s : Sphere Pt} {A P X X₁ : Pt} {ℓ : AffineSubspace ℝ Pt}
    (hA : A ∈ s) (hP : P ∈ s) (hX₁ : X₁ ∈ s) (hℓ : ℓ = s.orthRadius X₁)
    (hXℓ : X ∈ ℓ) (hXline : X ∈ line[ℝ, P, A]) :
    dist X X₁ ^ 2 = dist X (midpoint ℝ A P) ^ 2 - (dist A P / 2) ^ 2 := by
  have htan : s.IsTangentAt X₁ ℓ := hℓ ▸ (Sphere.isTangentAt_orthRadius_iff_mem.2 hX₁)
  have hd : dist X s.center ^ 2 = s.radius ^ 2 + dist X X₁ ^ 2 := htan.dist_sq_eq_of_mem hXℓ
  have hdA : dist s.center A = s.radius := by rw [dist_comm]; exact mem_sphere.1 hA
  have hdP : dist s.center P = s.radius := by rw [dist_comm]; exact mem_sphere.1 hP
  have h1 : ⟪s.center -ᵥ P, A -ᵥ P⟫ = ‖A -ᵥ P‖ ^ 2 / 2 :=
    inner_vsub_eq_half_of_dist_eq (hdA.trans hdP.symm)
  have h2eq : (⅟2 : ℝ) = 1 / 2 := by rw [invOf_eq_inv, one_div]
  set M := midpoint ℝ A P with hM
  have hMP : M -ᵥ P = (1 / 2 : ℝ) • (A -ᵥ P) := by
    rw [hM, ← h2eq]
    exact midpoint_vsub_right A P
  have hOM : s.center -ᵥ M = (s.center -ᵥ P) - (1 / 2 : ℝ) • (A -ᵥ P) := by
    rw [← hMP, vsub_sub_vsub_cancel_right]
  have hperp : ⟪s.center -ᵥ M, A -ᵥ P⟫ = 0 := by
    rw [hOM, inner_sub_left, real_inner_smul_left, h1, real_inner_self_eq_norm_sq]
    ring
  have hperp' : ⟪A -ᵥ P, s.center -ᵥ M⟫ = 0 := inner_eq_zero_symm.mp hperp
  have hMline : M ∈ line[ℝ, P, A] := by
    have h1 : M ∈ line[ℝ, A, P] := by
      have h2 : M = (1 / 2 : ℝ) • (P -ᵥ A) +ᵥ A := by
        have h3 : M -ᵥ A = (1 / 2 : ℝ) • (P -ᵥ A) := by
          rw [hM, ← h2eq]
          exact midpoint_vsub_left A P
        rw [← h3, vsub_vadd]
      rw [h2, vadd_left_mem_affineSpan_pair]
      exact ⟨1 / 2, rfl⟩
    rw [Set.pair_comm A P] at h1
    exact h1
  have hXMd : X -ᵥ M ∈ (line[ℝ, P, A]).direction :=
    AffineSubspace.vsub_mem_direction hXline hMline
  rw [direction_affineSpan, vectorSpan_pair] at hXMd
  rw [Submodule.mem_span_singleton] at hXMd
  obtain ⟨τ, hτ⟩ := hXMd
  have hPA : P -ᵥ A = -(A -ᵥ P) := (neg_vsub_eq_vsub_rev _ _).symm
  have hperpX : ⟪X -ᵥ M, s.center -ᵥ M⟫ = 0 := by
    rw [← hτ, real_inner_smul_left, hPA, inner_neg_left, hperp', neg_zero, mul_zero]
  have hpy : dist X s.center ^ 2 = dist X M ^ 2 + dist M s.center ^ 2 :=
    dist_sq_eq_add_of_inner_eq_zero hperpX
  have hAvM : A -ᵥ M = (1 / 2 : ℝ) • (A -ᵥ P) := by
    rw [hM, ← h2eq]
    exact left_vsub_midpoint A P
  have hperpA : ⟪A -ᵥ M, s.center -ᵥ M⟫ = 0 := by
    rw [hAvM, real_inner_smul_left, hperp', mul_zero]
  have hpyA : dist A s.center ^ 2 = dist A M ^ 2 + dist M s.center ^ 2 :=
    dist_sq_eq_add_of_inner_eq_zero hperpA
  have hAM : dist A M = dist A P / 2 := by
    rw [dist_eq_norm_vsub, hAvM, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2), ← dist_eq_norm_vsub]
    ring
  have hdAsq : dist A s.center ^ 2 = s.radius ^ 2 := by rw [mem_sphere.1 hA]
  have hAMsq : dist A M ^ 2 = (dist A P / 2) ^ 2 := by rw [hAM]
  linear_combination -hd + hpy - hpyA + hdAsq - hAMsq

/-- The distance from `X` (intersection of a common external tangent with line `PA`) to
the midpoint `M` of `AP`: `XM² = (AP/2)² + (O₁O₂² - (R₁-R₂)²)/4`. -/
lemma dist_midpoint_sq_eq {s₁ s₂ : Sphere Pt} {A P X : Pt} {ℓ : AffineSubspace ℝ Pt}
    (hA₁ : A ∈ s₁) (hP₁ : P ∈ s₁) (hA₂ : A ∈ s₂) (hP₂ : P ∈ s₂) (hAP : A ≠ P)
    (hcenters : s₁.center ≠ s₂.center)
    (hℓ : ℓ ∈ s₁.commonExtTangents s₂) (hXℓ : X ∈ ℓ) (hXline : X ∈ line[ℝ, P, A]) :
    dist X (midpoint ℝ A P) ^ 2 = (dist A P / 2) ^ 2 +
      (dist s₁.center s₂.center ^ 2 - (s₁.radius - s₂.radius) ^ 2) / 4 := by
  obtain ⟨X₁, X₂, hX₁, hX₂, hℓ₁, hℓ₂, hρ, hmid⟩ :=
    exists_tangentPoints_of_mem_commonExtTangents hA₁ hP₁ hA₂ hP₂ hAP hcenters hℓ hXℓ hXline
  have hXX1 := dist_sq_tangent_sub hA₁ hP₁ hX₁ hℓ₁ hXℓ hXline
  have hR₁ : 0 < s₁.radius := by
    have h1 := s₁.radius_nonneg_of_mem hA₁
    have h2 : s₁.radius ≠ 0 := by
      intro hr
      rw [mem_sphere, hr, dist_eq_zero] at hA₁ hP₁
      exact hAP (hA₁.trans hP₁.symm)
    exact lt_of_le_of_ne h1 h2.symm
  -- the segment between tangency points: D² = d² - (R₁ - R₂)²
  have hchain : s₂.center -ᵥ s₁.center =
      (X₂ -ᵥ X₁) + (1 - s₂.radius / s₁.radius) • (X₁ -ᵥ s₁.center) := by
    have hρR : (1 - s₂.radius / s₁.radius) • (X₁ -ᵥ s₁.center) =
        (X₁ -ᵥ s₁.center) - (X₂ -ᵥ s₂.center) := by
      rw [hρ, sub_smul, one_smul]
    rw [hρR, ← add_sub_assoc, vsub_add_vsub_cancel X₂ X₁ s₁.center,
      vsub_sub_vsub_cancel_left]
  have hX₁ℓ : X₁ ∈ ℓ := hℓ₁ ▸ s₁.self_mem_orthRadius X₁
  have hX₂ℓ : X₂ ∈ ℓ := hℓ₂ ▸ s₂.self_mem_orthRadius X₂
  have hperp : ⟪X₂ -ᵥ X₁, X₁ -ᵥ s₁.center⟫ = 0 := by
    have hd : X₂ -ᵥ X₁ ∈ ℓ.direction := AffineSubspace.vsub_mem_direction hX₂ℓ hX₁ℓ
    rw [hℓ₁, Sphere.direction_orthRadius] at hd
    exact Submodule.inner_left_of_mem_orthogonal (Submodule.mem_span_singleton_self _) hd
  have hperp2 : ⟪X₂ -ᵥ X₁, (1 - s₂.radius / s₁.radius) • (X₁ -ᵥ s₁.center)⟫ = 0 := by
    rw [real_inner_smul_right, hperp, mul_zero]
  have h1 : ‖X₂ -ᵥ X₁‖ = dist X₁ X₂ := by
    rw [← neg_vsub_eq_vsub_rev, norm_neg, ← dist_eq_norm_vsub]
  have h1sq : ‖X₂ -ᵥ X₁‖ ^ 2 = dist X₁ X₂ ^ 2 := by rw [h1]
  have h2 : ‖(1 - s₂.radius / s₁.radius) • (X₁ -ᵥ s₁.center)‖ ^ 2 =
      (s₁.radius - s₂.radius) ^ 2 := by
    have hnu : ‖X₁ -ᵥ s₁.center‖ = s₁.radius := by
      rw [← dist_eq_norm_vsub]; exact mem_sphere.1 hX₁
    have h3 : ‖(1 - s₂.radius / s₁.radius) • (X₁ -ᵥ s₁.center)‖ ^ 2 =
        (1 - s₂.radius / s₁.radius) ^ 2 * s₁.radius ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hnu]
    have hρR : (s₂.radius / s₁.radius) * s₁.radius = s₂.radius :=
      div_mul_cancel₀ _ hR₁.ne'
    have hρR2 : (s₂.radius / s₁.radius) ^ 2 * s₁.radius ^ 2 = s₂.radius ^ 2 := by
      rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 hR₁.ne')]
    have hρR1 : (s₂.radius / s₁.radius) * s₁.radius ^ 2 = s₂.radius * s₁.radius := by
      rw [pow_two, ← mul_assoc, hρR]
    rw [h3]
    linear_combination hρR2 - 2 * hρR1
  have hdsq : dist s₁.center s₂.center ^ 2 =
      dist X₁ X₂ ^ 2 + (s₁.radius - s₂.radius) ^ 2 := by
    rw [dist_eq_norm_vsub, ← neg_vsub_eq_vsub_rev, norm_neg, hchain, norm_add_sq_real, hperp2,
      mul_zero, add_zero, h1sq, h2]
  -- X is the midpoint of X₁X₂, so dist X X₁ = D / 2
  have h2eq : (⅟2 : ℝ) = 1 / 2 := by rw [invOf_eq_inv, one_div]
  have hXX1D : dist X X₁ = dist X₁ X₂ / 2 := by
    have h1 : X -ᵥ X₁ = (1 / 2 : ℝ) • (X₂ -ᵥ X₁) := by
      rw [hmid, ← h2eq]
      exact midpoint_vsub_left X₁ X₂
    have h2 : ‖X₂ -ᵥ X₁‖ = dist X₁ X₂ := by
      rw [← neg_vsub_eq_vsub_rev, norm_neg, ← dist_eq_norm_vsub]
    rw [dist_eq_norm_vsub, h1, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2), h2]
    ring
  have hXX1sq : dist X X₁ ^ 2 = (dist X₁ X₂ / 2) ^ 2 := by rw [hXX1D]
  have hDsq : dist X₁ X₂ ^ 2 = dist s₁.center s₂.center ^ 2 - (s₁.radius - s₂.radius) ^ 2 := by
    linear_combination -hdsq
  linear_combination -hXX1 + hXX1sq + (1 / 4) * hDsq

omit hd2 in
/-- The center of a sphere through `A` and `P`, seen from the midpoint of `AP`, is
orthogonal to `AP`. -/
lemma inner_center_midpoint {s : Sphere Pt} {A P : Pt} (hA : A ∈ s) (hP : P ∈ s) :
    ⟪s.center -ᵥ midpoint ℝ A P, A -ᵥ P⟫ = 0 := by
  have hdA : dist s.center A = s.radius := by rw [dist_comm]; exact mem_sphere.1 hA
  have hdP : dist s.center P = s.radius := by rw [dist_comm]; exact mem_sphere.1 hP
  have h1 : ⟪s.center -ᵥ P, A -ᵥ P⟫ = ‖A -ᵥ P‖ ^ 2 / 2 :=
    inner_vsub_eq_half_of_dist_eq (hdA.trans hdP.symm)
  have h2eq : (⅟2 : ℝ) = 1 / 2 := by rw [invOf_eq_inv, one_div]
  have hMP : midpoint ℝ A P -ᵥ P = (1 / 2 : ℝ) • (A -ᵥ P) := by
    rw [← h2eq]
    exact midpoint_vsub_right A P
  have hOM : s.center -ᵥ midpoint ℝ A P = (s.center -ᵥ P) - (1 / 2 : ℝ) • (A -ᵥ P) := by
    rw [← hMP, vsub_sub_vsub_cancel_right]
  rw [hOM, inner_sub_left, real_inner_smul_left, h1, real_inner_self_eq_norm_sq]
  ring

omit hd2 in
/-- The difference of the centers of two spheres through `A` and `P` is orthogonal to
`AP`. -/
lemma inner_center_sub_center {s₁ s₂ : Sphere Pt} {A P : Pt} (hA₁ : A ∈ s₁) (hP₁ : P ∈ s₁)
    (hA₂ : A ∈ s₂) (hP₂ : P ∈ s₂) :
    ⟪s₂.center -ᵥ s₁.center, A -ᵥ P⟫ = 0 := by
  have hdA₁ : dist s₁.center A = s₁.radius := by rw [dist_comm]; exact mem_sphere.1 hA₁
  have hdP₁ : dist s₁.center P = s₁.radius := by rw [dist_comm]; exact mem_sphere.1 hP₁
  have hdA₂ : dist s₂.center A = s₂.radius := by rw [dist_comm]; exact mem_sphere.1 hA₂
  have hdP₂ : dist s₂.center P = s₂.radius := by rw [dist_comm]; exact mem_sphere.1 hP₂
  have h1 : ⟪s₁.center -ᵥ P, A -ᵥ P⟫ = ‖A -ᵥ P‖ ^ 2 / 2 :=
    inner_vsub_eq_half_of_dist_eq (hdA₁.trans hdP₁.symm)
  have h3 : ⟪s₂.center -ᵥ P, A -ᵥ P⟫ = ‖A -ᵥ P‖ ^ 2 / 2 :=
    inner_vsub_eq_half_of_dist_eq (hdA₂.trans hdP₂.symm)
  have e : s₂.center -ᵥ s₁.center = (s₂.center -ᵥ P) - (s₁.center -ᵥ P) := by
    rw [vsub_sub_vsub_cancel_right]
  rw [e, inner_sub_left, h1, h3, sub_self]

/-- For the two common external tangents and their intersection points `X`, `Y` with
line `PA`: `X` and `Y` are symmetric about the midpoint `M` of `AP`, so
`dist X Y = 2 * dist X M`. -/
lemma dist_eq_two_mul_dist_midpoint {s₁ s₂ : Sphere Pt} {A P X Y : Pt}
    {ℓX ℓY : AffineSubspace ℝ Pt}
    (hA₁ : A ∈ s₁) (hP₁ : P ∈ s₁) (hA₂ : A ∈ s₂) (hP₂ : P ∈ s₂) (hAP : A ≠ P)
    (hcenters : s₁.center ≠ s₂.center)
    (hℓX : ℓX ∈ s₁.commonExtTangents s₂) (hℓY : ℓY ∈ s₁.commonExtTangents s₂)
    (hℓne : ℓX ≠ ℓY)
    (hXℓ : X ∈ ℓX) (hXline : X ∈ line[ℝ, P, A])
    (hYℓ : Y ∈ ℓY) (hYline : Y ∈ line[ℝ, P, A]) :
    dist X Y = 2 * dist X (midpoint ℝ A P) := by
  set M := midpoint ℝ A P with hM
  have hXM := dist_midpoint_sq_eq hA₁ hP₁ hA₂ hP₂ hAP hcenters hℓX hXℓ hXline
  have hYM := dist_midpoint_sq_eq hA₁ hP₁ hA₂ hP₂ hAP hcenters hℓY hYℓ hYline
  have hXYM : dist X M = dist Y M := by
    have h : dist X M ^ 2 = dist Y M ^ 2 := by rw [hXM, hYM]
    exact (sq_eq_sq₀ dist_nonneg dist_nonneg).mp h
  -- the two intersection points are distinct
  have hXneY : X ≠ Y := by
    intro hXY
    subst hXY
    obtain ⟨X₁, X₂, hX₁, hX₂, hℓ₁X, hℓ₂X, hρX, -⟩ :=
      exists_tangentPoints_of_mem_commonExtTangents hA₁ hP₁ hA₂ hP₂ hAP hcenters hℓX hXℓ hXline
    obtain ⟨Y₁, Y₂, hY₁, hY₂, hℓ₁Y, hℓ₂Y, hρY, -⟩ :=
      exists_tangentPoints_of_mem_commonExtTangents hA₁ hP₁ hA₂ hP₂ hAP hcenters hℓY hYℓ hYline
    have hR₁ : 0 < s₁.radius := by
      have h1 := s₁.radius_nonneg_of_mem hA₁
      have h2 : s₁.radius ≠ 0 := by
        intro hr
        rw [mem_sphere, hr, dist_eq_zero] at hA₁ hP₁
        exact hAP (hA₁.trans hP₁.symm)
      exact lt_of_le_of_ne h1 h2.symm
    have hX₁ℓX : X₁ ∈ ℓX := hℓ₁X ▸ s₁.self_mem_orthRadius X₁
    have hX₂ℓX : X₂ ∈ ℓX := hℓ₂X ▸ s₂.self_mem_orthRadius X₂
    have hY₁ℓY : Y₁ ∈ ℓY := hℓ₁Y ▸ s₁.self_mem_orthRadius Y₁
    have hY₂ℓY : Y₂ ∈ ℓY := hℓ₂Y ▸ s₂.self_mem_orthRadius Y₂
    -- both directions are one-dimensional
    have huX : X₁ -ᵥ s₁.center ≠ 0 := by
      have hd : dist X₁ s₁.center = s₁.radius := mem_sphere.1 hX₁
      have hne : X₁ ≠ s₁.center := by
        intro hc
        rw [hc, dist_self] at hd
        exact hR₁.ne' hd.symm
      exact vsub_ne_zero.mpr hne
    have huY : Y₁ -ᵥ s₁.center ≠ 0 := by
      have hd : dist Y₁ s₁.center = s₁.radius := mem_sphere.1 hY₁
      have hne : Y₁ ≠ s₁.center := by
        intro hc
        rw [hc, dist_self] at hd
        exact hR₁.ne' hd.symm
      exact vsub_ne_zero.mpr hne
    have hdirfinX : Module.finrank ℝ ℓX.direction = 1 := by
      have hd : ℓX.direction = (ℝ ∙ (X₁ -ᵥ s₁.center) : Submodule ℝ V)ᗮ := by
        rw [hℓ₁X, Sphere.direction_orthRadius]
      rw [hd]
      have h1 := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ (X₁ -ᵥ s₁.center) : Submodule ℝ V)
      rw [finrank_span_singleton huX, hd2.out] at h1
      omega
    have hdirfinY : Module.finrank ℝ ℓY.direction = 1 := by
      have hd : ℓY.direction = (ℝ ∙ (Y₁ -ᵥ s₁.center) : Submodule ℝ V)ᗮ := by
        rw [hℓ₁Y, Sphere.direction_orthRadius]
      rw [hd]
      have h1 := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ (Y₁ -ᵥ s₁.center) : Submodule ℝ V)
      rw [finrank_span_singleton huY, hd2.out] at h1
      omega
    -- equal directions plus a common point give equal subspaces
    have heq_of_dir : ℓX.direction = ℓY.direction → ℓX = ℓY := by
      intro hdir
      apply le_antisymm
      · intro q hq
        have hqd : q -ᵥ X ∈ ℓY.direction := by
          rw [← hdir]
          exact AffineSubspace.vsub_mem_direction hq hXℓ
        have h1 : (q -ᵥ X) +ᵥ X ∈ ℓY := AffineSubspace.vadd_mem_of_mem_direction hqd hYℓ
        rwa [vsub_vadd] at h1
      · intro q hq
        have hqd : q -ᵥ X ∈ ℓX.direction := by
          rw [hdir]
          exact AffineSubspace.vsub_mem_direction hq hYℓ
        have h1 : (q -ᵥ X) +ᵥ X ∈ ℓX := AffineSubspace.vadd_mem_of_mem_direction hqd hXℓ
        rwa [vsub_vadd] at h1
    rcases eq_or_ne s₁.radius s₂.radius with hRR | hRR
    · -- equal radii: both tangent lines are parallel to the line of centers
      have hR2 : s₂.radius ≠ 0 := hRR ▸ hR₁.ne'
      have hXXdir : X₂ -ᵥ X₁ = s₂.center -ᵥ s₁.center := by
        have hρ1 : X₂ -ᵥ s₂.center = X₁ -ᵥ s₁.center := by
          rw [hρX, hRR, div_self hR2, one_smul]
        have e1 : X₂ -ᵥ s₁.center = (X₂ -ᵥ s₂.center) + (s₂.center -ᵥ s₁.center) := by
          rw [vsub_add_vsub_cancel]
        have e2 : X₂ -ᵥ s₁.center = (X₂ -ᵥ X₁) + (X₁ -ᵥ s₁.center) := by
          rw [vsub_add_vsub_cancel]
        rw [hρ1, e2] at e1
        rw [add_comm (X₁ -ᵥ s₁.center) (s₂.center -ᵥ s₁.center)] at e1
        exact add_right_cancel e1
      have hYYdir : Y₂ -ᵥ Y₁ = s₂.center -ᵥ s₁.center := by
        have hρ1 : Y₂ -ᵥ s₂.center = Y₁ -ᵥ s₁.center := by
          rw [hρY, hRR, div_self hR2, one_smul]
        have e1 : Y₂ -ᵥ s₁.center = (Y₂ -ᵥ s₂.center) + (s₂.center -ᵥ s₁.center) := by
          rw [vsub_add_vsub_cancel]
        have e2 : Y₂ -ᵥ s₁.center = (Y₂ -ᵥ Y₁) + (Y₁ -ᵥ s₁.center) := by
          rw [vsub_add_vsub_cancel]
        rw [hρ1, e2] at e1
        rw [add_comm (Y₁ -ᵥ s₁.center) (s₂.center -ᵥ s₁.center)] at e1
        exact add_right_cancel e1
      have hOO : s₂.center -ᵥ s₁.center ≠ 0 := vsub_ne_zero.mpr hcenters.symm
      have hdirX : ℓX.direction = ℝ ∙ (s₂.center -ᵥ s₁.center) := by
        have hle : (ℝ ∙ (s₂.center -ᵥ s₁.center) : Submodule ℝ V) ≤ ℓX.direction := by
          rw [Submodule.span_singleton_le_iff_mem, ← hXXdir]
          exact AffineSubspace.vsub_mem_direction hX₂ℓX hX₁ℓX
        have hfin : Module.finrank ℝ (ℝ ∙ (s₂.center -ᵥ s₁.center) : Submodule ℝ V) =
            Module.finrank ℝ ℓX.direction := by
          rw [finrank_span_singleton hOO, hdirfinX]
        exact (Submodule.eq_of_le_of_finrank_eq hle hfin).symm
      have hdirY : ℓY.direction = ℝ ∙ (s₂.center -ᵥ s₁.center) := by
        have hle : (ℝ ∙ (s₂.center -ᵥ s₁.center) : Submodule ℝ V) ≤ ℓY.direction := by
          rw [Submodule.span_singleton_le_iff_mem, ← hYYdir]
          exact AffineSubspace.vsub_mem_direction hY₂ℓY hY₁ℓY
        have hfin : Module.finrank ℝ (ℝ ∙ (s₂.center -ᵥ s₁.center) : Submodule ℝ V) =
            Module.finrank ℝ ℓY.direction := by
          rw [finrank_span_singleton hOO, hdirfinY]
        exact (Submodule.eq_of_le_of_finrank_eq hle hfin).symm
      exact hℓne (heq_of_dir (hdirX.trans hdirY.symm))
    · -- different radii: both tangent lines pass through the external center of similitude
      have hRdiff : s₁.radius - s₂.radius ≠ 0 := sub_ne_zero.mpr hRR
      set E := AffineMap.lineMap s₁.center s₂.center (s₁.radius / (s₁.radius - s₂.radius))
        with hE
      have hscalmul : (s₁.radius / (s₁.radius - s₂.radius)) * (1 - s₂.radius / s₁.radius) = 1 := by
        field_simp [hRdiff, hR₁.ne']
      have hEmemX : E ∈ ℓX := by
        have hE1 : E -ᵥ X₁ = (s₁.radius / (s₁.radius - s₂.radius)) • (X₂ -ᵥ X₁) := by
          rw [hE]
          have e1 : AffineMap.lineMap s₁.center s₂.center (s₁.radius / (s₁.radius - s₂.radius))
              -ᵥ X₁ = (s₁.radius / (s₁.radius - s₂.radius)) • (s₂.center -ᵥ s₁.center) +
              (s₁.center -ᵥ X₁) := by
            rw [← vsub_add_vsub_cancel
              (AffineMap.lineMap s₁.center s₂.center (s₁.radius / (s₁.radius - s₂.radius)))
              s₁.center X₁, AffineMap.lineMap_vsub_left]
          have hchain : s₂.center -ᵥ s₁.center =
              (X₂ -ᵥ X₁) + (1 - s₂.radius / s₁.radius) • (X₁ -ᵥ s₁.center) := by
            have hρR : (1 - s₂.radius / s₁.radius) • (X₁ -ᵥ s₁.center) =
                (X₁ -ᵥ s₁.center) - (X₂ -ᵥ s₂.center) := by
              rw [hρX, sub_smul, one_smul]
            rw [hρR, ← add_sub_assoc, vsub_add_vsub_cancel X₂ X₁ s₁.center,
              vsub_sub_vsub_cancel_left]
          rw [e1, hchain, smul_add, smul_smul, hscalmul, one_smul,
            show s₁.center -ᵥ X₁ = -(X₁ -ᵥ s₁.center) from (neg_vsub_eq_vsub_rev _ _).symm]
          module
        have h1 : (E -ᵥ X₁) +ᵥ X₁ ∈ ℓX := by
          apply AffineSubspace.vadd_mem_of_mem_direction _ hX₁ℓX
          rw [hE1]
          exact Submodule.smul_mem _ _ (AffineSubspace.vsub_mem_direction hX₂ℓX hX₁ℓX)
        rwa [vsub_vadd] at h1
      have hEmemY : E ∈ ℓY := by
        have hE1 : E -ᵥ Y₁ = (s₁.radius / (s₁.radius - s₂.radius)) • (Y₂ -ᵥ Y₁) := by
          rw [hE]
          have e1 : AffineMap.lineMap s₁.center s₂.center (s₁.radius / (s₁.radius - s₂.radius))
              -ᵥ Y₁ = (s₁.radius / (s₁.radius - s₂.radius)) • (s₂.center -ᵥ s₁.center) +
              (s₁.center -ᵥ Y₁) := by
            rw [← vsub_add_vsub_cancel
              (AffineMap.lineMap s₁.center s₂.center (s₁.radius / (s₁.radius - s₂.radius)))
              s₁.center Y₁, AffineMap.lineMap_vsub_left]
          have hchain : s₂.center -ᵥ s₁.center =
              (Y₂ -ᵥ Y₁) + (1 - s₂.radius / s₁.radius) • (Y₁ -ᵥ s₁.center) := by
            have hρR : (1 - s₂.radius / s₁.radius) • (Y₁ -ᵥ s₁.center) =
                (Y₁ -ᵥ s₁.center) - (Y₂ -ᵥ s₂.center) := by
              rw [hρY, sub_smul, one_smul]
            rw [hρR, ← add_sub_assoc, vsub_add_vsub_cancel Y₂ Y₁ s₁.center,
              vsub_sub_vsub_cancel_left]
          rw [e1, hchain, smul_add, smul_smul, hscalmul, one_smul,
            show s₁.center -ᵥ Y₁ = -(Y₁ -ᵥ s₁.center) from (neg_vsub_eq_vsub_rev _ _).symm]
          module
        have h1 : (E -ᵥ Y₁) +ᵥ Y₁ ∈ ℓY := by
          apply AffineSubspace.vadd_mem_of_mem_direction _ hY₁ℓY
          rw [hE1]
          exact Submodule.smul_mem _ _ (AffineSubspace.vsub_mem_direction hY₂ℓY hY₁ℓY)
        rwa [vsub_vadd] at h1
      -- E is not X (else X would be the midpoint M, contradicting XM > 0)
      have hEX : E ≠ X := by
        intro hEXX
        -- X ∈ line[O₁, O₂] (as E) and X ∈ line[P, A], so X = M
        have hEline : E ∈ line[ℝ, s₁.center, s₂.center] := by
          rw [hE, AffineMap.lineMap_apply]
          exact (vadd_left_mem_affineSpan_pair).2 ⟨_, rfl⟩
        have hXlineO : X ∈ line[ℝ, s₁.center, s₂.center] := hEXX ▸ hEline
        -- M ∈ line[O₁, O₂]
        have hspanOO : (ℝ ∙ (s₂.center -ᵥ s₁.center) : Submodule ℝ V) =
            (ℝ ∙ (A -ᵥ P) : Submodule ℝ V)ᗮ := by
          apply Submodule.eq_of_le_of_finrank_eq
          · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_orthogonal]
            intro w hw
            rw [Submodule.mem_span_singleton] at hw
            obtain ⟨r, rfl⟩ := hw
            rw [real_inner_smul_left,
              inner_eq_zero_symm.mp (inner_center_sub_center hA₁ hP₁ hA₂ hP₂), mul_zero]
          · rw [finrank_span_singleton (vsub_ne_zero.mpr hcenters.symm)]
            have h1 := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ (A -ᵥ P) : Submodule ℝ V)
            rw [finrank_span_singleton (vsub_ne_zero.mpr hAP), hd2.out] at h1
            omega
        have hperp1 : ⟪s₁.center -ᵥ M, A -ᵥ P⟫ = 0 := by
          rw [hM]
          exact inner_center_midpoint hA₁ hP₁
        have hperp1' : ⟪A -ᵥ P, s₁.center -ᵥ M⟫ = 0 := inner_eq_zero_symm.mp hperp1
        have hMMO : M -ᵥ s₁.center ∈ ℝ ∙ (s₂.center -ᵥ s₁.center) := by
          rw [hspanOO, Submodule.mem_orthogonal]
          intro w hw
          rw [Submodule.mem_span_singleton] at hw
          obtain ⟨r, rfl⟩ := hw
          rw [real_inner_smul_left, show M -ᵥ s₁.center = -(s₁.center -ᵥ M) from
            (neg_vsub_eq_vsub_rev _ _).symm, inner_neg_right, hperp1', neg_zero, mul_zero]
        have hMlineO : M ∈ line[ℝ, s₁.center, s₂.center] := by
          rw [Submodule.mem_span_singleton] at hMMO
          obtain ⟨r, hr⟩ := hMMO
          have h1 : (M -ᵥ s₁.center) +ᵥ s₁.center ∈ line[ℝ, s₁.center, s₂.center] := by
            rw [vadd_left_mem_affineSpan_pair]
            exact ⟨r, hr⟩
          rwa [vsub_vadd] at h1
        -- M ∈ line[ℝ, P, A]
        have hMline : M ∈ line[ℝ, P, A] := by
          have h1 : M ∈ line[ℝ, A, P] := by
            have h2eq : (⅟2 : ℝ) = 1 / 2 := by rw [invOf_eq_inv, one_div]
            have h2 : M = (1 / 2 : ℝ) • (P -ᵥ A) +ᵥ A := by
              have h3 : M -ᵥ A = (1 / 2 : ℝ) • (P -ᵥ A) := by
                rw [hM, ← h2eq]
                exact midpoint_vsub_left A P
              rw [← h3, vsub_vadd]
            rw [h2, vadd_left_mem_affineSpan_pair]
            exact ⟨1 / 2, rfl⟩
          rw [Set.pair_comm A P] at h1
          exact h1
        -- X -ᵥ M is orthogonal to itself
        have hXMdir : X -ᵥ M ∈ (line[ℝ, s₁.center, s₂.center]).direction :=
          AffineSubspace.vsub_mem_direction hXlineO hMlineO
        rw [direction_affineSpan, vectorSpan_pair] at hXMdir
        rw [Submodule.mem_span_singleton] at hXMdir
        obtain ⟨t, ht⟩ := hXMdir
        have hXMPA : X -ᵥ M ∈ (line[ℝ, P, A]).direction :=
          AffineSubspace.vsub_mem_direction hXline hMline
        rw [direction_affineSpan, vectorSpan_pair] at hXMPA
        rw [Submodule.mem_span_singleton] at hXMPA
        obtain ⟨τ, hτ⟩ := hXMPA
        -- compute ⟪X -ᵥ M, A -ᵥ P⟫ two ways
        have hperpM : ⟪X -ᵥ M, A -ᵥ P⟫ = 0 := by
          rw [← ht, real_inner_smul_left, show s₁.center -ᵥ s₂.center =
            -(s₂.center -ᵥ s₁.center) from (neg_vsub_eq_vsub_rev _ _).symm, inner_neg_left,
            inner_center_sub_center hA₁ hP₁ hA₂ hP₂, neg_zero, mul_zero]
        have hperpM2 : ⟪X -ᵥ M, A -ᵥ P⟫ = -τ * ‖A -ᵥ P‖ ^ 2 := by
          rw [← hτ, real_inner_smul_left, ← neg_vsub_eq_vsub_rev, inner_neg_left,
            real_inner_self_eq_norm_sq]
          ring
        have hτ0 : τ = 0 := by
          have hnorm : ‖A -ᵥ P‖ ^ 2 ≠ 0 := by
            have h1 : A -ᵥ P ≠ 0 := vsub_ne_zero.mpr hAP
            positivity [norm_pos_iff.mpr h1]
          rw [hperpM] at hperpM2
          rcases mul_eq_zero.mp hperpM2.symm with h | h
          · exact neg_eq_zero.mp h
          · exact absurd h hnorm
        have hXM0 : X -ᵥ M = 0 := by rw [← hτ, hτ0, zero_smul]
        have hXeM : X = M := vsub_eq_zero_iff_eq.mp hXM0
        -- but XM > 0
        have hXMpos : (0:ℝ) < dist X M ^ 2 := by
          rw [hXM]
          have hAPpos : (0:ℝ) < dist A P := dist_pos.mpr hAP
          have hD : 0 ≤ (dist s₁.center s₂.center ^ 2 - (s₁.radius - s₂.radius) ^ 2) / 4 := by
            have h1 := dist_sq_sub_sq_pos V hA₁ hP₁ hA₂ hP₂ hAP hcenters
            positivity
          positivity
        rw [hXeM, dist_self] at hXMpos
        norm_num at hXMpos
      -- two distinct shared points: the lines coincide, contradiction
      have hEXv : E -ᵥ X ≠ 0 := vsub_ne_zero.mpr hEX
      have hdirX : ℓX.direction = ℝ ∙ (E -ᵥ X) := by
        have hle : (ℝ ∙ (E -ᵥ X) : Submodule ℝ V) ≤ ℓX.direction := by
          rw [Submodule.span_singleton_le_iff_mem]
          exact AffineSubspace.vsub_mem_direction hEmemX hXℓ
        have hfin : Module.finrank ℝ (ℝ ∙ (E -ᵥ X) : Submodule ℝ V) =
            Module.finrank ℝ ℓX.direction := by
          rw [finrank_span_singleton hEXv, hdirfinX]
        exact (Submodule.eq_of_le_of_finrank_eq hle hfin).symm
      have hdirY : ℓY.direction = ℝ ∙ (E -ᵥ X) := by
        have hle : (ℝ ∙ (E -ᵥ X) : Submodule ℝ V) ≤ ℓY.direction := by
          rw [Submodule.span_singleton_le_iff_mem]
          exact AffineSubspace.vsub_mem_direction hEmemY hYℓ
        have hfin : Module.finrank ℝ (ℝ ∙ (E -ᵥ X) : Submodule ℝ V) =
            Module.finrank ℝ ℓY.direction := by
          rw [finrank_span_singleton hEXv, hdirfinY]
        exact (Submodule.eq_of_le_of_finrank_eq hle hfin).symm
      exact hℓne (heq_of_dir (hdirX.trans hdirY.symm))
  -- now the symmetry gives the distance formula
  have hMline : M ∈ line[ℝ, P, A] := by
    have h1 : M ∈ line[ℝ, A, P] := by
      have h2eq : (⅟2 : ℝ) = 1 / 2 := by rw [invOf_eq_inv, one_div]
      have h2 : M = (1 / 2 : ℝ) • (P -ᵥ A) +ᵥ A := by
        have h3 : M -ᵥ A = (1 / 2 : ℝ) • (P -ᵥ A) := by
          rw [hM, ← h2eq]
          exact midpoint_vsub_left A P
        rw [← h3, vsub_vadd]
      rw [h2, vadd_left_mem_affineSpan_pair]
      exact ⟨1 / 2, rfl⟩
    rw [Set.pair_comm A P] at h1
    exact h1
  have hXMd : X -ᵥ M ∈ (line[ℝ, P, A]).direction :=
    AffineSubspace.vsub_mem_direction hXline hMline
  rw [direction_affineSpan, vectorSpan_pair] at hXMd
  rw [Submodule.mem_span_singleton] at hXMd
  obtain ⟨τX, hτX⟩ := hXMd
  have hYMd : Y -ᵥ M ∈ (line[ℝ, P, A]).direction :=
    AffineSubspace.vsub_mem_direction hYline hMline
  rw [direction_affineSpan, vectorSpan_pair] at hYMd
  rw [Submodule.mem_span_singleton] at hYMd
  obtain ⟨τY, hτY⟩ := hYMd
  have hPAnorm : ‖P -ᵥ A‖ ≠ 0 := norm_ne_zero_iff.mpr (vsub_ne_zero.mpr hAP.symm)
  have hdistX : dist X M = |τX| * ‖P -ᵥ A‖ := by
    rw [dist_eq_norm_vsub, ← hτX, norm_smul, Real.norm_eq_abs]
  have hdistY : dist Y M = |τY| * ‖P -ᵥ A‖ := by
    rw [dist_eq_norm_vsub, ← hτY, norm_smul, Real.norm_eq_abs]
  have habs : |τX| = |τY| := by
    have h := hXYM
    rw [hdistX, hdistY] at h
    exact mul_right_cancel₀ hPAnorm h
  have hne : τX ≠ τY := by
    intro h
    apply hXneY
    have : X -ᵥ M = Y -ᵥ M := by rw [← hτX, ← hτY, h]
    exact (vsub_left_injective M).eq_iff.mp this
  have hsum : τX = -τY := by
    rw [abs_eq_abs] at habs
    rcases habs with h | h
    · exact absurd h hne
    · exact h
  have hdist : dist X Y = |τX - τY| * ‖P -ᵥ A‖ := by
    have e : X -ᵥ Y = (τX - τY) • (P -ᵥ A) := by
      have e1 : X -ᵥ Y = (X -ᵥ M) - (Y -ᵥ M) := by rw [vsub_sub_vsub_cancel_right]
      rw [e1, ← hτX, ← hτY]
      module
    rw [dist_eq_norm_vsub, e, norm_smul, Real.norm_eq_abs]
  have e2 : τX - τY = 2 * τX := by rw [hsum]; ring
  rw [hdist, e2, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), hdistX]
  ring

/-!
### The main ratio computation
-/

/-- The main geometric fact: the ratio `(PA/XY)²` does not depend on `P`, and equals
`1 - (BC/(AB+AC))²`. -/
lemma ratio_sq {A B C P : Pt} (hABC : ¬ Collinear ℝ ({A, B, C} : Set Pt))
    (hsbtw : Sbtw ℝ B P C) {s₁ s₂ : Sphere Pt}
    (hA₁ : A ∈ s₁) (hB₁ : B ∈ s₁) (hP₁ : P ∈ s₁)
    (hA₂ : A ∈ s₂) (hC₂ : C ∈ s₂) (hP₂ : P ∈ s₂)
    {ℓX ℓY : AffineSubspace ℝ Pt}
    (hℓX : ℓX ∈ s₁.commonExtTangents s₂) (hℓY : ℓY ∈ s₁.commonExtTangents s₂)
    (hℓne : ℓX ≠ ℓY)
    {X Y : Pt}
    (hXℓ : X ∈ ℓX) (hXline : X ∈ line[ℝ, P, A])
    (hYℓ : Y ∈ ℓY) (hYline : Y ∈ line[ℝ, P, A]) :
    (dist P A / dist X Y) ^ 2 = 1 - (dist B C / (dist A B + dist A C)) ^ 2 := by
  -- A ≠ P, else A would be on line BC
  have hAP : A ≠ P := by
    intro h
    apply hABC
    have hPline : P ∈ line[ℝ, B, C] := affineSegment_subset_affineSpan ℝ B C hsbtw.1
    rw [← h] at hPline
    exact collinear_insert_of_mem_affineSpan_pair hPline
  obtain ⟨K, hKpos, hR1, hR2, hd, hRR, hAPsq, hcenters⟩ :=
    center_relations hABC hsbtw hA₁ hB₁ hP₁ hA₂ hC₂ hP₂
  have hXY := dist_eq_two_mul_dist_midpoint hA₁ hP₁ hA₂ hP₂ hAP hcenters hℓX hℓY hℓne
    hXℓ hXline hYℓ hYline
  have hXM := dist_midpoint_sq_eq hA₁ hP₁ hA₂ hP₂ hAP hcenters hℓX hXℓ hXline
  -- positivity facts
  have ha : 0 < dist B C := dist_pos.mpr (ne_of_not_collinear₂₃ hABC)
  have hb : 0 < dist A C := dist_pos.mpr (ne_of_not_collinear₁₃ hABC)
  have hc : 0 < dist A B := dist_pos.mpr (ne_of_not_collinear₁₂ hABC)
  have hAPpos : 0 < dist A P := dist_pos.mpr hAP
  have hXMpos : (0:ℝ) < dist X (midpoint ℝ A P) ^ 2 := by
    rw [hXM]
    have hD : (0:ℝ) ≤ (dist s₁.center s₂.center ^ 2 - (s₁.radius - s₂.radius) ^ 2) / 4 := by
      have h1 := dist_sq_sub_sq_pos V hA₁ hP₁ hA₂ hP₂ hAP hcenters
      positivity
    positivity
  have hXMne : dist X (midpoint ℝ A P) ≠ 0 := by
    intro h
    rw [h] at hXMpos
    norm_num at hXMpos
  -- (R₁ - R₂)² = K (b - c)²
  have hDsq : (s₁.radius - s₂.radius) ^ 2 = K * (dist A C - dist A B) ^ 2 := by
    nlinarith [hR1, hR2, hRR]
  -- (2 XM)² = AP² + (d² - (R₁ - R₂)²)
  have h4 : (2 * dist X (midpoint ℝ A P)) ^ 2 = dist A P ^ 2 +
      (dist s₁.center s₂.center ^ 2 - (s₁.radius - s₂.radius) ^ 2) := by
    nlinarith [hXM]
  -- the key polynomial identity
  have key : dist A P ^ 2 * (dist A B + dist A C) ^ 2 =
      (dist A P ^ 2 + (dist s₁.center s₂.center ^ 2 - (s₁.radius - s₂.radius) ^ 2)) *
        ((dist A B + dist A C) ^ 2 - dist B C ^ 2) := by
    nlinarith [hAPsq, hd, hDsq]
  have hPA : dist P A = dist A P := dist_comm P A
  have hdenom : (2 * dist X (midpoint ℝ A P)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (mul_ne_zero (by norm_num) hXMne)
  have hdenom2 : dist A P ^ 2 + (dist s₁.center s₂.center ^ 2 - (s₁.radius - s₂.radius) ^ 2)
      ≠ 0 := by
    rw [← h4]
    exact hdenom
  have hbc : dist A B + dist A C ≠ 0 := by positivity
  rw [hPA, hXY, div_pow, div_pow, h4]
  rw [div_eq_iff hdenom2, ← mul_right_inj' (pow_ne_zero 2 hbc)]
  have expand : (dist A B + dist A C) ^ 2 *
        ((1 - dist B C ^ 2 / (dist A B + dist A C) ^ 2) *
          (dist A P ^ 2 + (dist s₁.center s₂.center ^ 2 - (s₁.radius - s₂.radius) ^ 2))) =
      ((dist A B + dist A C) ^ 2 - dist B C ^ 2) *
        (dist A P ^ 2 + (dist s₁.center s₂.center ^ 2 - (s₁.radius - s₂.radius) ^ 2)) := by
    field_simp [hbc]
  rw [expand]
  linear_combination key

/-!
### Existence of the two common external tangents
-/

/-- The two common external tangent lines of the two circumcircles exist, together with
their intersection points with line `PA`. -/
lemma exists_commonExtTangents {A B C P : Pt} (hABC : ¬ Collinear ℝ ({A, B, C} : Set Pt))
    (hsbtw : Sbtw ℝ B P C) {s₁ s₂ : Sphere Pt}
    (hA₁ : A ∈ s₁) (_hB₁ : B ∈ s₁) (hP₁ : P ∈ s₁)
    (hA₂ : A ∈ s₂) (_hC₂ : C ∈ s₂) (hP₂ : P ∈ s₂)
    (hcenters : s₁.center ≠ s₂.center) :
    ∃ ℓX ℓY : AffineSubspace ℝ Pt, ℓX ∈ s₁.commonExtTangents s₂ ∧
      ℓY ∈ s₁.commonExtTangents s₂ ∧ ℓX ≠ ℓY ∧
      ∃ X Y : Pt, X ∈ ℓX ∧ X ∈ line[ℝ, P, A] ∧ Y ∈ ℓY ∧ Y ∈ line[ℝ, P, A] := by
  have o : Orientation ℝ V (Fin 2) := (Module.finBasisOfFinrankEq ℝ V hd2.out).orientation
  -- A ≠ P, else A would be on line BC
  have hAP : A ≠ P := by
    intro h
    apply hABC
    have hPline : P ∈ line[ℝ, B, C] := affineSegment_subset_affineSpan ℝ B C hsbtw.1
    rw [← h] at hPline
    exact collinear_insert_of_mem_affineSpan_pair hPline
  -- radii are positive
  have hR₁ : 0 < s₁.radius := by
    have h1 := s₁.radius_nonneg_of_mem hA₁
    have h2 : s₁.radius ≠ 0 := by
      intro hr
      rw [mem_sphere, hr, dist_eq_zero] at hA₁ hP₁
      exact hAP (hA₁.trans hP₁.symm)
    exact lt_of_le_of_ne h1 h2.symm
  have hR₂ : 0 < s₂.radius := by
    have h1 := s₂.radius_nonneg_of_mem hA₂
    have h2 : s₂.radius ≠ 0 := by
      intro hr
      rw [mem_sphere, hr, dist_eq_zero] at hA₂ hP₂
      exact hAP (hA₂.trans hP₂.symm)
    exact lt_of_le_of_ne h1 h2.symm
  set v := s₂.center -ᵥ s₁.center with hv
  set a' := A -ᵥ P with ha'
  set d := dist s₁.center s₂.center with hd
  set Δ := d ^ 2 - (s₁.radius - s₂.radius) ^ 2 with hΔ
  have hd0 : d ≠ 0 := by rw [hd]; exact dist_ne_zero.mpr hcenters
  have hΔpos : 0 < Δ := by
    rw [hΔ, hd]
    exact sub_pos.mpr (dist_sq_sub_sq_pos V hA₁ hP₁ hA₂ hP₂ hAP hcenters)
  have hvsq : ‖v‖ = d := by
    rw [hv, hd, dist_eq_norm_vsub, ← neg_vsub_eq_vsub_rev, norm_neg]
  have hv0 : v ≠ 0 := vsub_ne_zero.mpr hcenters.symm
  have ha'0 : a' ≠ 0 := vsub_ne_zero.mpr hAP
  -- v is a multiple of J a'
  obtain ⟨μ, hμ⟩ := exists_smul_rightAngleRotation_of_inner_eq_zero (o := o) ha'0
    (inner_center_sub_center hA₁ hP₁ hA₂ hP₂)
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hμ
    exact hcenters (vsub_eq_zero_iff_eq.mp hμ |>.symm)
  have hJv : ⟪a', o.rightAngleRotation v⟫ = -μ * ‖a'‖ ^ 2 := by
    rw [hv, ha', hμ, map_smul, o.rightAngleRotation_rightAngleRotation, real_inner_smul_right,
      inner_neg_right, real_inner_self_eq_norm_sq]
    ring
  -- the normal vectors of the tangent lines
  set n : ℝ → V := fun σ => ((s₁.radius - s₂.radius) / d ^ 2) • v + σ • o.rightAngleRotation v with hn
  have hnnorm : ∀ σ : ℝ, σ ^ 2 = Δ / d ^ 4 → ‖n σ‖ = 1 := by
    intro σ hσ
    have h1 : ‖((s₁.radius - s₂.radius) / d ^ 2) • v‖ ^ 2 =
        (s₁.radius - s₂.radius) ^ 2 / d ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hvsq]
      field_simp [hd0]
    have h2 : ‖σ • o.rightAngleRotation v‖ ^ 2 = σ ^ 2 * d ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, norm_rightAngleRotation, hvsq]
    have h3 : ⟪((s₁.radius - s₂.radius) / d ^ 2) • v, σ • o.rightAngleRotation v⟫ = 0 := by
      rw [real_inner_smul_left, real_inner_smul_right,
        inner_eq_zero_symm.mp (o.inner_rightAngleRotation_self v), mul_zero, mul_zero]
    have hsq : ‖n σ‖ ^ 2 = 1 := by
      rw [hn]
      dsimp only
      rw [norm_add_sq_real, h3, h1, h2, hσ, hΔ]
      field_simp [hd0]
      ring
    have := sq_eq_sq₀ (norm_nonneg _) zero_le_one |>.mp (by rw [hsq]; ring)
    exact this
  have hinner_v : ∀ σ : ℝ, ⟪v, n σ⟫ = s₁.radius - s₂.radius := by
    intro σ
    rw [hn]
    dsimp only
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
      inner_eq_zero_symm.mp (o.inner_rightAngleRotation_self v), mul_zero, add_zero,
      real_inner_self_eq_norm_sq, hvsq]
    field_simp [hd0]
  have hinner_a : ∀ σ : ℝ, ⟪a', n σ⟫ = -σ * μ * ‖a'‖ ^ 2 := by
    intro σ
    rw [hn]
    dsimp only
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
      inner_eq_zero_symm.mp (inner_center_sub_center hA₁ hP₁ hA₂ hP₂), mul_zero, zero_add, hJv]
    ring
  -- the tangency points
  set X1 : ℝ → Pt := fun σ => s₁.radius • n σ +ᵥ s₁.center with hX1
  set X2 : ℝ → Pt := fun σ => s₂.radius • n σ +ᵥ s₂.center with hX2
  have hX1mem : ∀ σ : ℝ, σ ^ 2 = Δ / d ^ 4 → X1 σ ∈ s₁ := by
    intro σ hσ
    rw [mem_sphere, hX1, dist_eq_norm_vsub, vadd_vsub, norm_smul, Real.norm_eq_abs,
      abs_of_pos hR₁, hnnorm σ hσ, mul_one]
  have hX2mem : ∀ σ : ℝ, σ ^ 2 = Δ / d ^ 4 → X2 σ ∈ s₂ := by
    intro σ hσ
    rw [mem_sphere, hX2, dist_eq_norm_vsub, vadd_vsub, norm_smul, Real.norm_eq_abs,
      abs_of_pos hR₂, hnnorm σ hσ, mul_one]
  have hX2memℓ : ∀ σ : ℝ, σ ^ 2 = Δ / d ^ 4 → X2 σ ∈ s₁.orthRadius (X1 σ) := by
    intro σ hσ
    rw [Sphere.mem_orthRadius_iff_inner_left]
    have e1 : X2 σ -ᵥ X1 σ = v + (s₂.radius - s₁.radius) • n σ := by
      rw [hX2, hX1]
      dsimp only
      rw [← vsub_sub_vsub_cancel_right, vadd_vsub_assoc, vadd_vsub, ← hv]
      module
    have e3 : X1 σ -ᵥ s₁.center = s₁.radius • n σ := by rw [hX1, vadd_vsub]
    rw [e1, e3, inner_add_left, real_inner_smul_right, real_inner_smul_left,
      real_inner_smul_right, hinner_v σ, real_inner_self_eq_norm_sq, hnnorm σ hσ]
    ring
  -- the tangent space is also tangent to the second sphere
  have hℓeq : ∀ σ : ℝ, σ ^ 2 = Δ / d ^ 4 →
      s₂.orthRadius (X2 σ) = s₁.orthRadius (X1 σ) := by
    intro σ hσ
    have hdir1 : (s₁.orthRadius (X1 σ)).direction = (ℝ ∙ n σ : Submodule ℝ V)ᗮ := by
      rw [Sphere.direction_orthRadius]
      have e : X1 σ -ᵥ s₁.center = s₁.radius • n σ := by rw [hX1, vadd_vsub]
      rw [e, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hR₁.ne')]
    have hdir2 : (s₂.orthRadius (X2 σ)).direction = (ℝ ∙ n σ : Submodule ℝ V)ᗮ := by
      rw [Sphere.direction_orthRadius]
      have e : X2 σ -ᵥ s₂.center = s₂.radius • n σ := by rw [hX2, vadd_vsub]
      rw [e, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hR₂.ne')]
    apply AffineSubspace.eq_of_direction_eq_of_nonempty_of_le (hdir2.trans hdir1.symm)
      ⟨X2 σ, Sphere.self_mem_orthRadius _ _⟩
    intro q hq
    have hqd : q -ᵥ X2 σ ∈ (s₂.orthRadius (X2 σ)).direction :=
      AffineSubspace.vsub_mem_direction hq (Sphere.self_mem_orthRadius _ _)
    have h1 : (q -ᵥ X2 σ) +ᵥ X2 σ ∈ s₁.orthRadius (X1 σ) := by
      apply AffineSubspace.vadd_mem_of_mem_direction _ (hX2memℓ σ hσ)
      rwa [hdir2, ← hdir1] at hqd
    rwa [vsub_vadd] at h1
  -- the tangent lines are external
  have hext : ∀ σ : ℝ, σ ^ 2 = Δ / d ^ 4 → ∀ q ∈ s₁.orthRadius (X1 σ),
      ¬Sbtw ℝ s₁.center q s₂.center := by
    intro σ hσ q hq hsbtw
    obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hsbtw.1
    have e3 : X1 σ -ᵥ s₁.center = s₁.radius • n σ := by rw [hX1, vadd_vsub]
    have hcomp : ⟪AffineMap.lineMap s₁.center s₂.center t -ᵥ X1 σ, n σ⟫ = 0 := by
      have h1 := (Sphere.mem_orthRadius_iff_inner_left).mp hq
      rw [e3, real_inner_smul_right] at h1
      rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd h2 hR₁.ne'
      · exact h2
    have e4 : AffineMap.lineMap s₁.center s₂.center t -ᵥ X1 σ =
        t • v - s₁.radius • n σ := by
      have e5 : AffineMap.lineMap s₁.center s₂.center t -ᵥ X1 σ =
          (AffineMap.lineMap s₁.center s₂.center t -ᵥ s₁.center) - (X1 σ -ᵥ s₁.center) :=
        (vsub_sub_vsub_cancel_right _ _ _).symm
      rw [e5, AffineMap.lineMap_vsub_left, e3, hv]
    have hcalc : ⟪AffineMap.lineMap s₁.center s₂.center t -ᵥ X1 σ, n σ⟫ =
        -((1 - t) * s₁.radius + t * s₂.radius) := by
      rw [e4, inner_sub_left, real_inner_smul_left, real_inner_smul_left, hinner_v σ,
        real_inner_self_eq_norm_sq, hnnorm σ hσ]
      ring
    rw [hcalc, neg_eq_zero] at hcomp
    have hpos : (0:ℝ) < (1 - t) * s₁.radius + t * s₂.radius := by
      rcases eq_or_lt_of_le ht1 with h | h
      · subst h
        simpa using hR₂
      · exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) hR₁) (mul_nonneg ht0 hR₂.le)
    exact hpos.ne' hcomp
  -- the intersection point with line PA
  have hinner_a_ne : ∀ σ : ℝ, σ ≠ 0 → ⟪a', n σ⟫ ≠ 0 := by
    intro σ hσ0
    rw [hinner_a σ]
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hσ0) hμ0)
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr ha'0))
  set τ : ℝ → ℝ := fun σ => ⟪X1 σ -ᵥ P, n σ⟫ / ⟪a', n σ⟫ with hτ
  have hXmemℓ : ∀ σ : ℝ, σ ^ 2 = Δ / d ^ 4 → σ ≠ 0 →
      AffineMap.lineMap P A (τ σ) ∈ s₁.orthRadius (X1 σ) := by
    intro σ hσ hσ0
    rw [Sphere.mem_orthRadius_iff_inner_left]
    have e3 : X1 σ -ᵥ s₁.center = s₁.radius • n σ := by rw [hX1, vadd_vsub]
    rw [e3, real_inner_smul_right]
    have e4 : AffineMap.lineMap P A (τ σ) -ᵥ X1 σ = τ σ • a' - (X1 σ -ᵥ P) := by
      have e5 : AffineMap.lineMap P A (τ σ) -ᵥ X1 σ =
          (AffineMap.lineMap P A (τ σ) -ᵥ P) - (X1 σ -ᵥ P) :=
        (vsub_sub_vsub_cancel_right _ _ _).symm
      rw [e5, AffineMap.lineMap_vsub_left, ha']
    have hτmul : τ σ * ⟪a', n σ⟫ = ⟪X1 σ -ᵥ P, n σ⟫ := by
      rw [hτ]
      exact div_mul_cancel₀ _ (hinner_a_ne σ hσ0)
    rw [e4, inner_sub_left, real_inner_smul_left, hτmul, sub_self, mul_zero]
  -- the two tangent lines are distinct
  set σ₀ := Real.sqrt Δ / d ^ 2 with hσ₀
  have hσ₀pos : 0 < σ₀ := by
    rw [hσ₀]
    positivity [Real.sqrt_pos.mpr hΔpos, sq_pos_of_ne_zero hd0]
  have hσ₀0 : σ₀ ≠ 0 := hσ₀pos.ne'
  have hσ₀sq : σ₀ ^ 2 = Δ / d ^ 4 := by
    rw [hσ₀, div_pow, Real.sq_sqrt hΔpos.le]
    have h1 : (d ^ 2) ^ 2 = d ^ 4 := by ring
    rw [h1]
  have hσmsq : (-σ₀) ^ 2 = Δ / d ^ 4 := by rw [neg_sq, hσ₀sq]
  have hX1ne : X1 σ₀ ≠ X1 (-σ₀) := by
    intro h
    have hn_diff : n σ₀ - n (-σ₀) = (2 * σ₀) • o.rightAngleRotation v := by
      rw [hn]
      dsimp only
      module
    have e : X1 σ₀ -ᵥ X1 (-σ₀) = s₁.radius • (n σ₀ - n (-σ₀)) := by
      rw [hX1]
      dsimp only
      rw [← vsub_sub_vsub_cancel_right, vadd_vsub, vadd_vsub, ← smul_sub]
    rw [h, vsub_self, hn_diff] at e
    rcases smul_eq_zero.mp e.symm with h1 | h1
    · exact hR₁.ne' h1
    · rcases smul_eq_zero.mp h1 with h2 | h2
      · exact hσ₀0 (by linarith)
      · exact rightAngleRotation_ne_zero hv0 h2
  have hℓne : s₁.orthRadius (X1 σ₀) ≠ s₁.orthRadius (X1 (-σ₀)) := by
    intro h
    have h1 : s₁.IsTangentAt (X1 σ₀) (s₁.orthRadius (X1 σ₀)) :=
      Sphere.isTangentAt_orthRadius_iff_mem.2 (hX1mem σ₀ hσ₀sq)
    have h2 : s₁.IsTangentAt (X1 (-σ₀)) (s₁.orthRadius (X1 σ₀)) := by
      have h2' : s₁.IsTangentAt (X1 (-σ₀)) (s₁.orthRadius (X1 (-σ₀))) :=
        Sphere.isTangentAt_orthRadius_iff_mem.2 (hX1mem (-σ₀) hσmsq)
      rwa [← h] at h2'
    exact hX1ne (h1.eq_of_isTangentAt h2)
  -- assemble everything
  have hmemℓ : ∀ σ : ℝ, σ ^ 2 = Δ / d ^ 4 →
      s₁.orthRadius (X1 σ) ∈ s₁.commonExtTangents s₂ := by
    intro σ hσ
    rw [Sphere.mem_commonExtTangents_iff, Sphere.mem_commonTangents_iff]
    refine ⟨⟨⟨X1 σ, hX1mem σ hσ, rfl⟩, ⟨X2 σ, hX2mem σ hσ, hℓeq σ hσ⟩⟩, hext σ hσ⟩
  refine ⟨s₁.orthRadius (X1 σ₀), s₁.orthRadius (X1 (-σ₀)), hmemℓ σ₀ hσ₀sq,
    hmemℓ (-σ₀) hσmsq, hℓne, AffineMap.lineMap P A (τ σ₀), AffineMap.lineMap P A (τ (-σ₀)),
    hXmemℓ σ₀ hσ₀sq hσ₀0, ?_, hXmemℓ (-σ₀) hσmsq (neg_ne_zero.mpr hσ₀0), ?_⟩
  · rw [AffineMap.lineMap_apply, vadd_left_mem_affineSpan_pair]
    exact ⟨τ σ₀, rfl⟩
  · rw [AffineMap.lineMap_apply, vadd_left_mem_affineSpan_pair]
    exact ⟨τ (-σ₀), rfl⟩

/-!
### The algebraic characterization of the solutions
-/

omit hd2 in
/-- If `P` on segment `BC` satisfies `PB·PC = (a/(b+c))²·bc`, then `P` is one of the two
answer points. -/
lemma eq_answer_of_dist_mul_dist {A B C P : Pt} (hABC : ¬ Collinear ℝ ({A, B, C} : Set Pt))
    (hsbtw : Sbtw ℝ B P C)
    (h : dist P B * dist P C * (dist A B + dist A C) ^ 2 =
      dist B C ^ 2 * (dist A B * dist A C)) :
    P = AffineMap.lineMap B C (dist A B / (dist A C + dist A B)) ∨
      P = AffineMap.lineMap B C (dist A C / (dist A C + dist A B)) := by
  obtain ⟨s, hs0, hs1, rfl⟩ := exists_lineMap_of_sbtw hsbtw
  have hBC : B ≠ C := ne_of_not_collinear₂₃ hABC
  have ha : (0:ℝ) < dist B C := dist_pos.mpr hBC
  have hb : (0:ℝ) < dist A C := dist_pos.mpr (ne_of_not_collinear₁₃ hABC)
  have hc : (0:ℝ) < dist A B := dist_pos.mpr (ne_of_not_collinear₁₂ hABC)
  have hbc : (0:ℝ) < dist A C + dist A B := by positivity
  have hPB : dist (AffineMap.lineMap B C s) B = s * dist B C := by
    rw [dist_lineMap_left, Real.norm_eq_abs, abs_of_pos hs0]
  have hPC : dist (AffineMap.lineMap B C s) C = (1 - s) * dist B C := by
    rw [dist_lineMap_right, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  rw [hPB, hPC] at h
  have h2 : s * (1 - s) * (dist A B + dist A C) ^ 2 = dist A B * dist A C := by
    have h3 : (dist B C) ^ 2 * (s * (1 - s) * (dist A B + dist A C) ^ 2) =
        (dist B C) ^ 2 * (dist A B * dist A C) := by
      nlinarith [h]
    exact mul_left_cancel₀ (pow_ne_zero 2 ha.ne') h3
  have hkey : (s * (dist A B + dist A C) - dist A C) *
      (s * (dist A B + dist A C) - dist A B) = 0 := by
    nlinarith [h2]
  rcases mul_eq_zero.mp hkey with hcase | hcase
  · right
    have hs : s = dist A C / (dist A C + dist A B) := by
      rw [eq_div_iff hbc.ne']
      nlinarith [hcase]
    rw [hs]
  · left
    have hs : s = dist A B / (dist A C + dist A B) := by
      rw [eq_div_iff hbc.ne']
      nlinarith [hcase]
    rw [hs]

omit hd2 in
/-- The two answer points satisfy `PB·PC = (a/(b+c))²·bc`. -/
lemma dist_mul_dist_of_eq_answer {A B C P : Pt} (hABC : ¬ Collinear ℝ ({A, B, C} : Set Pt))
    (h : P = AffineMap.lineMap B C (dist A B / (dist A C + dist A B)) ∨
      P = AffineMap.lineMap B C (dist A C / (dist A C + dist A B))) :
    dist P B * dist P C * (dist A B + dist A C) ^ 2 =
      dist B C ^ 2 * (dist A B * dist A C) := by
  have hb : (0:ℝ) < dist A C := dist_pos.mpr (ne_of_not_collinear₁₃ hABC)
  have hc : (0:ℝ) < dist A B := dist_pos.mpr (ne_of_not_collinear₁₂ hABC)
  have hbc : (0:ℝ) < dist A C + dist A B := by positivity
  have hbc' : dist A C + dist A B ≠ 0 := hbc.ne'
  rcases h with rfl | rfl
  · have hPB : dist (AffineMap.lineMap B C (dist A B / (dist A C + dist A B))) B =
        dist A B / (dist A C + dist A B) * dist B C := by
      rw [dist_lineMap_left, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1t : 1 - dist A B / (dist A C + dist A B) = dist A C / (dist A C + dist A B) := by
      field_simp [hbc']
      ring
    have hPC : dist (AffineMap.lineMap B C (dist A B / (dist A C + dist A B))) C =
        dist A C / (dist A C + dist A B) * dist B C := by
      have h1nn : (0:ℝ) ≤ 1 - dist A B / (dist A C + dist A B) := by
        rw [h1t]
        positivity
      rw [dist_lineMap_right, Real.norm_eq_abs, abs_of_nonneg h1nn, h1t]
    rw [hPB, hPC]
    field_simp [hbc']
    ring
  · have hPB : dist (AffineMap.lineMap B C (dist A C / (dist A C + dist A B))) B =
        dist A C / (dist A C + dist A B) * dist B C := by
      rw [dist_lineMap_left, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1t : 1 - dist A C / (dist A C + dist A B) = dist A B / (dist A C + dist A B) := by
      field_simp [hbc']
      ring
    have hPC : dist (AffineMap.lineMap B C (dist A C / (dist A C + dist A B))) C =
        dist A B / (dist A C + dist A B) * dist B C := by
      have h1nn : (0:ℝ) ≤ 1 - dist A C / (dist A C + dist A B) := by
        rw [h1t]
        positivity
      rw [dist_lineMap_right, Real.norm_eq_abs, abs_of_nonneg h1nn, h1t]
    rw [hPB, hPC]
    field_simp [hbc']
    ring

omit hd2 in
/-- The two answer points lie strictly between `B` and `C`. -/
lemma sbtw_of_eq_answer {A B C P : Pt} (hABC : ¬ Collinear ℝ ({A, B, C} : Set Pt))
    (h : P = AffineMap.lineMap B C (dist A B / (dist A C + dist A B)) ∨
      P = AffineMap.lineMap B C (dist A C / (dist A C + dist A B))) :
    Sbtw ℝ B P C := by
  have hb : (0:ℝ) < dist A C := dist_pos.mpr (ne_of_not_collinear₁₃ hABC)
  have hc : (0:ℝ) < dist A B := dist_pos.mpr (ne_of_not_collinear₁₂ hABC)
  have hbc : (0:ℝ) < dist A C + dist A B := by positivity
  rcases h with rfl | rfl
  · rw [sbtw_lineMap_iff]
    refine ⟨ne_of_not_collinear₂₃ hABC, by positivity, ?_⟩
    rw [div_lt_one hbc]
    linarith
  · rw [sbtw_lineMap_iff]
    refine ⟨ne_of_not_collinear₂₃ hABC, by positivity, ?_⟩
    rw [div_lt_one hbc]
    linarith

omit hd2 in
/-- The two answer points are distinct from `B`. -/
lemma ne_left_of_eq_answer {A B C P : Pt} (hABC : ¬ Collinear ℝ ({A, B, C} : Set Pt))
    (h : P = AffineMap.lineMap B C (dist A B / (dist A C + dist A B)) ∨
      P = AffineMap.lineMap B C (dist A C / (dist A C + dist A B))) :
    P ≠ B :=
  (sbtw_of_eq_answer hABC h).2.1

omit hd2 in
/-- The two answer points are distinct from `C`. -/
lemma ne_right_of_eq_answer {A B C P : Pt} (hABC : ¬ Collinear ℝ ({A, B, C} : Set Pt))
    (h : P = AffineMap.lineMap B C (dist A B / (dist A C + dist A B)) ∨
      P = AffineMap.lineMap B C (dist A C / (dist A C + dist A B))) :
    P ≠ C :=
  (sbtw_of_eq_answer hABC h).2.2

snip end

/-- The property required of the point `P`: for the circumcircles of triangles `PAB` and
`PAC` (quantified over all spheres through the three vertices, the circumsphere being
unique), if `X` and `Y` are the intersections of line `PA` with the two common external
tangent lines of the circles, then `(PA/XY)² + PB·PC/(AB·AC) = 1`. -/
def ProblemProperty (V : Type*) (Pt : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace Pt] [NormedAddTorsor V Pt] (A B C P : Pt) : Prop :=
  ∀ s₁ s₂ : Sphere Pt, A ∈ s₁ → B ∈ s₁ → P ∈ s₁ → A ∈ s₂ → C ∈ s₂ → P ∈ s₂ →
    ∀ ℓX ℓY : AffineSubspace ℝ Pt,
      ℓX ∈ s₁.commonExtTangents s₂ → ℓY ∈ s₁.commonExtTangents s₂ → ℓX ≠ ℓY →
        ∀ X Y : Pt, X ∈ ℓX → X ∈ line[ℝ, P, A] → Y ∈ ℓY → Y ∈ line[ℝ, P, A] →
          (dist P A / dist X Y) ^ 2 + (dist P B * dist P C) / (dist A B * dist A C) = 1

/-- The answer: the foot of the internal bisector of angle `A`, and its reflection in the
midpoint of `BC`; equivalently the points `P` of `BC` with `PB = ac/(b+c)` or
`PB = ab/(b+c)`. -/
determine answer (V : Type*) (Pt : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace Pt] [NormedAddTorsor V Pt] (A B C : Pt) : Set Pt :=
  {AffineMap.lineMap B C (dist A B / (dist A C + dist A B)),
   AffineMap.lineMap B C (dist A C / (dist A C + dist A B))}

problem usa2013_p6 (A B C : Pt) (hABC : ¬ Collinear ℝ ({A, B, C} : Set Pt)) :
    {P : Pt | Wbtw ℝ B P C ∧ P ≠ B ∧ P ≠ C ∧ ProblemProperty V Pt A B C P} =
      answer V Pt A B C := by
  ext P
  simp only [Set.mem_setOf_eq, answer, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- forward: the property forces P to be one of the two answer points
    rintro ⟨hseg, hPB, hPC, hprop⟩
    have hsbtw : Sbtw ℝ B P C := sbtw_of_wbtw hseg hPB hPC
    have hPline : P ∈ line[ℝ, B, C] := affineSegment_subset_affineSpan ℝ B C hseg
    have hPAB : ¬ Collinear ℝ ({P, A, B} : Set Pt) := not_collinear_of_mem_line hABC hPline hPB
    have hPAC : ¬ Collinear ℝ ({P, A, C} : Set Pt) := by
      have hACB : ¬ Collinear ℝ ({A, C, B} : Set Pt) := by
        have : ({A, C, B} : Set Pt) = {A, B, C} := by
          ext x
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto
        rw [this]
        exact hABC
      have hPline2 : P ∈ line[ℝ, C, B] := by rwa [Set.pair_comm B C] at hPline
      exact not_collinear_of_mem_line hACB hPline2 hPC
    obtain ⟨s₁, hP₁, hA₁, hB₁⟩ := exists_sphere_through hPAB
    obtain ⟨s₂, hP₂, hA₂, hC₂⟩ := exists_sphere_through hPAC
    obtain ⟨K, hKpos, hR1, hR2, hd, hRR, hAPsq, hcenters⟩ :=
      center_relations hABC hsbtw hA₁ hB₁ hP₁ hA₂ hC₂ hP₂
    obtain ⟨ℓX, ℓY, hℓX, hℓY, hℓne, X, Y, hXℓ, hXline, hYℓ, hYline⟩ :=
      exists_commonExtTangents hABC hsbtw hA₁ hB₁ hP₁ hA₂ hC₂ hP₂ hcenters
    have hratio := ratio_sq hABC hsbtw hA₁ hB₁ hP₁ hA₂ hC₂ hP₂ hℓX hℓY hℓne hXℓ hXline
      hYℓ hYline
    have heq := hprop s₁ s₂ hA₁ hB₁ hP₁ hA₂ hC₂ hP₂ ℓX ℓY hℓX hℓY hℓne X Y hXℓ hXline
      hYℓ hYline
    rw [hratio] at heq
    -- so PB·PC·(b+c)² = a²·bc
    have hb : (0:ℝ) < dist A C := dist_pos.mpr (ne_of_not_collinear₁₃ hABC)
    have hc : (0:ℝ) < dist A B := dist_pos.mpr (ne_of_not_collinear₁₂ hABC)
    have hbc : (0:ℝ) < dist A B + dist A C := by positivity
    have key : dist P B * dist P C * (dist A B + dist A C) ^ 2 =
        dist B C ^ 2 * (dist A B * dist A C) := by
      have hbcne : dist A B * dist A C ≠ 0 := mul_ne_zero hc.ne' hb.ne'
      field_simp [hbc.ne', hbcne] at heq ⊢
      nlinarith [heq]
    exact eq_answer_of_dist_mul_dist hABC hsbtw key
  · -- backward: each answer point satisfies the property
    rintro (rfl | rfl)
    · have hans : AffineMap.lineMap B C (dist A B / (dist A C + dist A B)) =
          AffineMap.lineMap B C (dist A B / (dist A C + dist A B)) ∨
          AffineMap.lineMap B C (dist A B / (dist A C + dist A B)) =
            AffineMap.lineMap B C (dist A C / (dist A C + dist A B)) :=
        Or.inl rfl
      have hsbtw := sbtw_of_eq_answer hABC hans
      refine ⟨hsbtw.1, hsbtw.2.1, hsbtw.2.2, ?_⟩
      intro s₁ s₂ hA₁ hB₁ hP₁ hA₂ hC₂ hP₂ ℓX ℓY hℓX hℓY hℓne X Y hXℓ hXline hYℓ hYline
      have hratio := ratio_sq hABC hsbtw hA₁ hB₁ hP₁ hA₂ hC₂ hP₂ hℓX hℓY hℓne hXℓ hXline
        hYℓ hYline
      have hprod := dist_mul_dist_of_eq_answer hABC hans
      rw [hratio]
      have hb : (0:ℝ) < dist A C := dist_pos.mpr (ne_of_not_collinear₁₃ hABC)
      have hc : (0:ℝ) < dist A B := dist_pos.mpr (ne_of_not_collinear₁₂ hABC)
      have hbc' : (dist A B + dist A C) ^ 2 ≠ 0 := by positivity
      field_simp [hbc', mul_ne_zero hc.ne' hb.ne']
      nlinarith [hprod]
    · have hans : AffineMap.lineMap B C (dist A C / (dist A C + dist A B)) =
          AffineMap.lineMap B C (dist A B / (dist A C + dist A B)) ∨
          AffineMap.lineMap B C (dist A C / (dist A C + dist A B)) =
            AffineMap.lineMap B C (dist A C / (dist A C + dist A B)) :=
        Or.inr rfl
      have hsbtw := sbtw_of_eq_answer hABC hans
      refine ⟨hsbtw.1, hsbtw.2.1, hsbtw.2.2, ?_⟩
      intro s₁ s₂ hA₁ hB₁ hP₁ hA₂ hC₂ hP₂ ℓX ℓY hℓX hℓY hℓne X Y hXℓ hXline hYℓ hYline
      have hratio := ratio_sq hABC hsbtw hA₁ hB₁ hP₁ hA₂ hC₂ hP₂ hℓX hℓY hℓne hXℓ hXline
        hYℓ hYline
      have hprod := dist_mul_dist_of_eq_answer hABC hans
      rw [hratio]
      have hb : (0:ℝ) < dist A C := dist_pos.mpr (ne_of_not_collinear₁₃ hABC)
      have hc : (0:ℝ) < dist A B := dist_pos.mpr (ne_of_not_collinear₁₂ hABC)
      have hbc' : (dist A B + dist A C) ^ 2 ≠ 0 := by positivity
      field_simp [hbc', mul_ne_zero hc.ne' hb.ne']
      nlinarith [hprod]

end Usa2013P6
