/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Analysis.InnerProductSpace.TwoDim
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Geometry.Euclidean.Circumcenter
public import Mathlib.Geometry.Euclidean.Incenter
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 1989, Problem 4

Let ABC be an acute-angled triangle whose side lengths satisfy the inequalities
AB < AC < BC. If point I is the center of the inscribed circle of triangle ABC
and point O is the center of the circumscribed circle, prove that line IO
intersects segments AB and BC.
-/

open scoped Affine EuclideanGeometry Real RealInnerProductSpace

open Module

namespace Usa1989P4

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P] [Fact (finrank ℝ V = 2)]

set_option linter.unusedSectionVars false

/-- The incenter of the triangle `ABC`. -/
noncomputable abbrev I (A B C : P) (hABC : AffineIndependent ℝ ![A, B, C]) : P :=
  (⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ P).incenter

/-- The circumcenter of the triangle `ABC`. -/
noncomputable abbrev O (A B C : P) (hABC : AffineIndependent ℝ ![A, B, C]) : P :=
  (⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ P).circumcenter

snip begin

/-! ### Basic nondegeneracy facts -/

lemma range_pts {A B C : P} : Set.range ![A, B, C] = {A, B, C} := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · exact ⟨2, by simp⟩

lemma not_collinear {A B C : P} (hABC : AffineIndependent ℝ ![A, B, C]) :
    ¬ Collinear ℝ ({A, B, C} : Set P) :=
  affineIndependent_iff_not_collinear_set.mp hABC

lemma ne_AB {A B C : P} (hABC : AffineIndependent ℝ ![A, B, C]) : A ≠ B := by
  intro h
  have h2 : (0 : Fin 3) = 1 := AffineIndependent.injective hABC (by simpa using h)
  exact absurd h2 (by decide)

lemma ne_BC {A B C : P} (hABC : AffineIndependent ℝ ![A, B, C]) : B ≠ C := by
  intro h
  have h2 : (1 : Fin 3) = 2 := AffineIndependent.injective hABC (by simpa using h)
  exact absurd h2 (by decide)

lemma ne_AC {A B C : P} (hABC : AffineIndependent ℝ ![A, B, C]) : A ≠ C := by
  intro h
  have h2 : (0 : Fin 3) = 2 := AffineIndependent.injective hABC (by simpa using h)
  exact absurd h2 (by decide)

/-- The strict triangle inequality for non-collinear points. -/
lemma strict_tri {X Y Z : P} (h : ¬ Collinear ℝ ({X, Y, Z} : Set P)) :
    dist X Z < dist X Y + dist Y Z := by
  rw [dist_lt_dist_add_dist_iff]
  intro hw
  exact h hw.collinear

lemma lt_a {A B C : P} (hABC : AffineIndependent ℝ ![A, B, C]) :
    dist B C < dist A B + dist A C := by
  have hcol : ¬ Collinear ℝ ({B, A, C} : Set P) := by
    rw [Set.insert_comm B A {C}]
    exact not_collinear hABC
  have h := strict_tri hcol
  rwa [dist_comm B A] at h

lemma lt_b {A B C : P} (hABC : AffineIndependent ℝ ![A, B, C]) :
    dist A C < dist B C + dist A B := by
  have hcol : ¬ Collinear ℝ ({C, B, A} : Set P) := by
    have he : ({C, B, A} : Set P) = {A, B, C} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [he]
    exact not_collinear hABC
  have h := strict_tri hcol
  rwa [dist_comm C A, dist_comm C B, dist_comm B A] at h

lemma lt_c {A B C : P} (hABC : AffineIndependent ℝ ![A, B, C]) :
    dist A B < dist A C + dist B C := by
  have hcol : ¬ Collinear ℝ ({A, C, B} : Set P) := by
    have he : ({A, C, B} : Set P) = {A, B, C} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [he]
    exact not_collinear hABC
  have h := strict_tri hcol
  rwa [dist_comm C B] at h

/-- The vectors `u = A - B` and `v = C - B` span the whole (2-dimensional) space. -/
lemma span_uv_top {A B C : P} (hABC : AffineIndependent ℝ ![A, B, C]) :
    Submodule.span ℝ {A -ᵥ B, C -ᵥ B} = ⊤ := by
  haveI : FiniteDimensional ℝ V := FiniteDimensional.of_fact_finrank_eq_two
  have htop : affineSpan ℝ (Set.range ![A, B, C]) = ⊤ := by
    apply hABC.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
    rw [Fintype.card_fin, show finrank ℝ V = 2 from Fact.out]
  have hdir : vectorSpan ℝ (Set.range ![A, B, C]) = ⊤ := by
    rw [← direction_affineSpan, htop]
    exact AffineSubspace.direction_top ℝ V P
  rw [range_pts] at hdir
  have hle : vectorSpan ℝ ({A, B, C} : Set P) ≤ Submodule.span ℝ {A -ᵥ B, C -ᵥ B} := by
    rw [vectorSpan_eq_span_vsub_set_right ℝ (show B ∈ ({A, B, C} : Set P) by simp)]
    apply Submodule.span_le.mpr
    rintro x ⟨p, hp, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact Submodule.subset_span (Or.inl rfl)
    · simp
    · exact Submodule.subset_span (Or.inr rfl)
  rw [hdir] at hle
  exact top_le_iff.mp hle

/-- The signed area of `(A - B, C - B)` is nonzero. -/
lemma areaForm_ne_zero {A B C : P} (hABC : AffineIndependent ℝ ![A, B, C])
    (o : Orientation ℝ V (Fin 2)) :
    o.areaForm (A -ᵥ B) (C -ᵥ B) ≠ 0 := by
  intro hσ
  have h1 := o.inner_sq_add_areaForm_sq (A -ᵥ B) (C -ᵥ B)
  rw [hσ] at h1
  simp at h1
  have hu : A -ᵥ B ≠ 0 := vsub_ne_zero.mpr (ne_AB hABC)
  have hv : C -ᵥ B ≠ 0 := vsub_ne_zero.mpr (ne_BC hABC).symm
  have h2 : ⟪A -ᵥ B, C -ᵥ B⟫ ^ 2 = (‖A -ᵥ B‖ * ‖C -ᵥ B‖) ^ 2 := by
    rw [mul_pow]
    linarith [h1]
  have habs : ‖⟪A -ᵥ B, C -ᵥ B⟫‖ = ‖A -ᵥ B‖ * ‖C -ᵥ B‖ := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h3 | h3
    · rw [Real.norm_eq_abs, h3, abs_of_nonneg (by positivity)]
    · rw [Real.norm_eq_abs, h3, abs_neg, abs_of_nonneg (by positivity)]
  obtain ⟨r, hr0, hr⟩ := (norm_inner_eq_norm_iff hu hv).mp habs
  have hspan := span_uv_top hABC
  have hsub : Submodule.span ℝ {A -ᵥ B, C -ᵥ B} ≤ Submodule.span ℝ {A -ᵥ B} := by
    apply Submodule.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Submodule.subset_span (Set.mem_singleton _)
    · rw [hr]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  rw [hspan] at hsub
  have hfin : finrank ℝ (Submodule.span ℝ {A -ᵥ B}) = 1 := finrank_span_singleton hu
  have hfin2 : finrank ℝ (⊤ : Submodule ℝ V) = 2 := by
    rw [finrank_top, show finrank ℝ V = 2 from Fact.out]
  have := Submodule.finrank_mono hsub
  linarith

/-- The Gram relation: `2⟨u,v⟩ = a² + c² - b²`. -/
lemma hg {A B C : P} : 2 * ⟪A -ᵥ B, C -ᵥ B⟫ = dist B C ^ 2 + dist A B ^ 2 - dist A C ^ 2 := by
  have h1 : dist A C ^ 2 = ‖A -ᵥ B‖ ^ 2 - 2 * ⟪A -ᵥ B, C -ᵥ B⟫ + ‖C -ᵥ B‖ ^ 2 := by
    rw [dist_eq_norm_vsub, ← vsub_sub_vsub_cancel_right A C B]
    exact norm_sub_sq_real (A -ᵥ B) (C -ᵥ B)
  have hu : ‖A -ᵥ B‖ ^ 2 = dist A B ^ 2 := by rw [← dist_eq_norm_vsub]
  have hv : ‖C -ᵥ B‖ ^ 2 = dist B C ^ 2 := by rw [← dist_eq_norm_vsub, dist_comm C B]
  linarith

/-- The Gram determinant `Δ = a²c² - g² = σ²` is positive. -/
lemma hΔ {A B C : P} (hABC : AffineIndependent ℝ ![A, B, C])
    (o : Orientation ℝ V (Fin 2)) :
    0 < dist A B ^ 2 * dist B C ^ 2 - ⟪A -ᵥ B, C -ᵥ B⟫ ^ 2 := by
  have h1 := o.inner_sq_add_areaForm_sq (A -ᵥ B) (C -ᵥ B)
  have hσ := areaForm_ne_zero hABC o
  have e1 : dist A B ^ 2 * dist B C ^ 2 = ‖A -ᵥ B‖ ^ 2 * ‖C -ᵥ B‖ ^ 2 := by
    rw [← dist_eq_norm_vsub, ← dist_eq_norm_vsub, dist_comm C B]
  have e2 : dist A B ^ 2 * dist B C ^ 2 - ⟪A -ᵥ B, C -ᵥ B⟫ ^ 2 =
      (o.areaForm (A -ᵥ B) (C -ᵥ B)) ^ 2 := by
    rw [e1]
    linarith [h1]
  rw [e2]
  exact sq_pos_of_ne_zero hσ

/-! ### The circumcenter in coordinates relative to `B`. -/

lemma circumcenter_vsub {A B C : P} (hABC : AffineIndependent ℝ ![A, B, C])
    (o : Orientation ℝ V (Fin 2)) :
    (⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ P).circumcenter -ᵥ B =
      (dist B C ^ 2 * (dist A B ^ 2 - ⟪A -ᵥ B, C -ᵥ B⟫) /
        (2 * (dist A B ^ 2 * dist B C ^ 2 - ⟪A -ᵥ B, C -ᵥ B⟫ ^ 2))) • (A -ᵥ B) +
      (dist A B ^ 2 * (dist B C ^ 2 - ⟪A -ᵥ B, C -ᵥ B⟫) /
        (2 * (dist A B ^ 2 * dist B C ^ 2 - ⟪A -ᵥ B, C -ᵥ B⟫ ^ 2))) • (C -ᵥ B) := by
  set g := ⟪A -ᵥ B, C -ᵥ B⟫ with hg_def
  set Δ := dist A B ^ 2 * dist B C ^ 2 - g ^ 2 with hΔ_def
  set O' := (⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ P).circumcenter with hO'_def
  have hΔne : Δ ≠ 0 := (hΔ hABC o).ne'
  have huu : ⟪A -ᵥ B, A -ᵥ B⟫ = dist A B ^ 2 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm_vsub]
  have hvv : ⟪C -ᵥ B, C -ᵥ B⟫ = dist B C ^ 2 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm_vsub, dist_comm C B]
  have hpts : (⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ P).points = ![A, B, C] := rfl
  have eAB : dist A O' = dist B O' := by
    have e0 := (⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ P).dist_circumcenter_eq_circumradius 0
    have e1 := (⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ P).dist_circumcenter_eq_circumradius 1
    rw [hpts] at e0 e1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e0 e1
    exact e0.trans e1.symm
  have eCB : dist C O' = dist B O' := by
    have e2 := (⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ P).dist_circumcenter_eq_circumradius 2
    have e1 := (⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ P).dist_circumcenter_eq_circumradius 1
    rw [hpts] at e2 e1
    simp only [Matrix.cons_val_two, Matrix.cons_val_one] at e2 e1
    exact e2.trans e1.symm
  have key1 : 2 * ⟪O' -ᵥ B, A -ᵥ B⟫ = dist A B ^ 2 := by
    have h1 : ‖A -ᵥ O'‖ ^ 2 = ‖B -ᵥ O'‖ ^ 2 := by
      have h := congrArg (· ^ 2) eAB
      rwa [dist_eq_norm_vsub, dist_eq_norm_vsub] at h
    rw [← vsub_sub_vsub_cancel_right A O' B, ← vsub_sub_vsub_cancel_right B O' B, vsub_self,
      zero_sub, norm_neg] at h1
    rw [norm_sub_sq_real] at h1
    have e2 : ‖A -ᵥ B‖ ^ 2 = dist A B ^ 2 := by rw [← dist_eq_norm_vsub]
    have e3 : ⟪O' -ᵥ B, A -ᵥ B⟫ = ⟪A -ᵥ B, O' -ᵥ B⟫ := real_inner_comm _ _
    linarith [h1, e2, e3]
  have key2 : 2 * ⟪O' -ᵥ B, C -ᵥ B⟫ = dist B C ^ 2 := by
    have h1 : ‖C -ᵥ O'‖ ^ 2 = ‖B -ᵥ O'‖ ^ 2 := by
      have h := congrArg (· ^ 2) eCB
      rwa [dist_eq_norm_vsub, dist_eq_norm_vsub] at h
    rw [← vsub_sub_vsub_cancel_right C O' B, ← vsub_sub_vsub_cancel_right B O' B, vsub_self,
      zero_sub, norm_neg] at h1
    rw [norm_sub_sq_real] at h1
    have e2 : ‖C -ᵥ B‖ ^ 2 = dist B C ^ 2 := by rw [← dist_eq_norm_vsub, dist_comm C B]
    have e3 : ⟪O' -ᵥ B, C -ᵥ B⟫ = ⟪C -ᵥ B, O' -ᵥ B⟫ := real_inner_comm _ _
    linarith [h1, e2, e3]
  -- uniqueness: the difference is orthogonal to everything
  set lam := dist B C ^ 2 * (dist A B ^ 2 - g) / (2 * Δ) with hlam_def
  set mu := dist A B ^ 2 * (dist B C ^ 2 - g) / (2 * Δ) with hmu_def
  have hd1 : ⟪O' -ᵥ B - (lam • (A -ᵥ B) + mu • (C -ᵥ B)), A -ᵥ B⟫ = 0 := by
    rw [inner_sub_left, inner_add_left, real_inner_smul_left, real_inner_smul_left, huu,
      real_inner_comm (A -ᵥ B) (C -ᵥ B), ← hg_def]
    have e1 : lam * dist A B ^ 2 + mu * g = dist A B ^ 2 / 2 := by
      have h2 : 2 * Δ ≠ 0 := mul_ne_zero two_ne_zero hΔne
      rw [hlam_def, hmu_def]
      field_simp [h2]
      ring
    linarith [e1, key1]
  have hd2 : ⟪O' -ᵥ B - (lam • (A -ᵥ B) + mu • (C -ᵥ B)), C -ᵥ B⟫ = 0 := by
    rw [inner_sub_left, inner_add_left, real_inner_smul_left, real_inner_smul_left, hvv, ← hg_def]
    have e1 : lam * g + mu * dist B C ^ 2 = dist B C ^ 2 / 2 := by
      have h2 : 2 * Δ ≠ 0 := mul_ne_zero two_ne_zero hΔne
      rw [hlam_def, hmu_def]
      field_simp [h2]
      ring
    linarith [e1, key2]
  have hd : O' -ᵥ B - (lam • (A -ᵥ B) + mu • (C -ᵥ B)) = 0 := by
    have hspan := span_uv_top hABC
    have hd3 : ∀ w : V, ⟪O' -ᵥ B - (lam • (A -ᵥ B) + mu • (C -ᵥ B)), w⟫ = 0 := by
      intro w
      have hw : w ∈ (⊤ : Submodule ℝ V) := Submodule.mem_top
      rw [← hspan] at hw
      induction hw using Submodule.span_induction with
      | mem x hx =>
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl
          · exact hd1
          · exact hd2
      | zero => simp
      | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
      | smul a x _ hx => rw [inner_smul_right, hx, mul_zero]
    have hself := hd3 (O' -ᵥ B - (lam • (A -ᵥ B) + mu • (C -ᵥ B)))
    rwa [inner_self_eq_zero] at hself
  have hfinal : O' -ᵥ B = lam • (A -ᵥ B) + mu • (C -ᵥ B) := sub_eq_zero.mp hd
  rw [hfinal, hlam_def, hmu_def, hΔ_def, hg_def]

/-! ### The incenter in coordinates relative to `B`. -/

/-- Auxiliary: for `F` on the line `YZ` with `X - F ⟂ Y - Z`, the product
`dist X F * dist Y Z` equals the absolute value of the area form. -/
lemma dist_mul_dist_eq_abs_areaForm (o : Orientation ℝ V (Fin 2)) {X Y Z F : P}
    (hF : F ∈ affineSpan ℝ ({Y, Z} : Set P))
    (hortho : ⟪X -ᵥ F, Y -ᵥ Z⟫ = 0) :
    dist X F * dist Y Z = |o.areaForm (X -ᵥ Y) (Y -ᵥ Z)| := by
  have h1 : ‖X -ᵥ F‖ * ‖Y -ᵥ Z‖ = |o.areaForm (X -ᵥ F) (Y -ᵥ Z)| :=
    (o.abs_areaForm_of_orthogonal hortho).symm
  have h2 : o.areaForm (X -ᵥ F) (Y -ᵥ Z) = o.areaForm (X -ᵥ Y) (Y -ᵥ Z) := by
    have hF' : Y -ᵥ F ∈ (affineSpan ℝ ({Y, Z} : Set P)).direction :=
      AffineSubspace.vsub_mem_direction (mem_affineSpan ℝ (Set.mem_insert Y {Z})) hF
    rw [direction_affineSpan, vectorSpan_pair] at hF'
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hF'
    have h3 : X -ᵥ F = (X -ᵥ Y) + (Y -ᵥ F) := (vsub_add_vsub_cancel X Y F).symm
    rw [h3, map_add, ← ht, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      o.areaForm_apply_self, smul_zero, add_zero]
  rw [dist_eq_norm_vsub, dist_eq_norm_vsub, h1, h2]

lemma dist_altitudeFoot_zero_mul {A B C : P} (hABC : AffineIndependent ℝ ![A, B, C])
    (o : Orientation ℝ V (Fin 2)) :
    dist A ((⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ P).altitudeFoot 0) * dist B C =
      |o.areaForm (A -ᵥ B) (C -ᵥ B)| := by
  set T : Affine.Triangle ℝ P := ⟨![A, B, C], hABC⟩ with hT
  have hB1 : T.points (1 : Fin 3) = B := rfl
  have hC2 : T.points (2 : Fin 3) = C := rfl
  have hset : T.points '' ({0}ᶜ : Set (Fin 3)) = ({B, C} : Set P) := by
    have h01 : ({(0 : Fin 3)}ᶜ : Set (Fin 3)) = {1, 2} := by
      ext x
      fin_cases x <;> simp
    rw [h01, Set.image_insert_eq, Set.image_singleton, hB1, hC2]
  have hF : T.altitudeFoot 0 ∈ affineSpan ℝ ({B, C} : Set P) := by
    have h := T.altitudeFoot_mem_affineSpan_image_compl 0
    rwa [hset] at h
  have h2 : A -ᵥ T.altitudeFoot 0 ∈
      (affineSpan ℝ (Set.range (T.faceOpposite 0).points)).directionᗮ :=
    EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal
      (affineSpan ℝ (Set.range (T.faceOpposite 0).points)) (T.points 0)
  have hBm : B ∈ T.points '' ({0}ᶜ : Set (Fin 3)) := ⟨1, by decide, hB1⟩
  have hCm : C ∈ T.points '' ({0}ᶜ : Set (Fin 3)) := ⟨2, by decide, hC2⟩
  have hbc : B -ᵥ C ∈ (affineSpan ℝ (Set.range (T.faceOpposite 0).points)).direction := by
    rw [direction_affineSpan, Affine.Simplex.range_faceOpposite_points]
    exact vsub_mem_vectorSpan ℝ hBm hCm
  have hor : ⟪A -ᵥ T.altitudeFoot 0, B -ᵥ C⟫ = 0 :=
    (Submodule.mem_orthogonal' _ (A -ᵥ T.altitudeFoot 0)).mp h2 (B -ᵥ C) hbc
  rw [dist_mul_dist_eq_abs_areaForm o hF hor, ← neg_vsub_eq_vsub_rev C B, map_neg, abs_neg]

lemma dist_altitudeFoot_one_mul {A B C : P} (hABC : AffineIndependent ℝ ![A, B, C])
    (o : Orientation ℝ V (Fin 2)) :
    dist B ((⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ P).altitudeFoot 1) * dist C A =
      |o.areaForm (A -ᵥ B) (C -ᵥ B)| := by
  set T : Affine.Triangle ℝ P := ⟨![A, B, C], hABC⟩ with hT
  have hA0 : T.points (0 : Fin 3) = A := rfl
  have hC2 : T.points (2 : Fin 3) = C := rfl
  have hset : T.points '' ({1}ᶜ : Set (Fin 3)) = ({C, A} : Set P) := by
    have h01 : ({(1 : Fin 3)}ᶜ : Set (Fin 3)) = {0, 2} := by
      ext x
      fin_cases x <;> simp
    rw [h01, Set.image_insert_eq, Set.image_singleton, hA0, hC2, Set.pair_comm A C]
  have hF : T.altitudeFoot 1 ∈ affineSpan ℝ ({C, A} : Set P) := by
    have h := T.altitudeFoot_mem_affineSpan_image_compl 1
    rwa [hset] at h
  have h2 : B -ᵥ T.altitudeFoot 1 ∈
      (affineSpan ℝ (Set.range (T.faceOpposite 1).points)).directionᗮ :=
    EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal
      (affineSpan ℝ (Set.range (T.faceOpposite 1).points)) (T.points 1)
  have hAm : A ∈ T.points '' ({1}ᶜ : Set (Fin 3)) := ⟨0, by decide, hA0⟩
  have hCm : C ∈ T.points '' ({1}ᶜ : Set (Fin 3)) := ⟨2, by decide, hC2⟩
  have hca : C -ᵥ A ∈ (affineSpan ℝ (Set.range (T.faceOpposite 1).points)).direction := by
    rw [direction_affineSpan, Affine.Simplex.range_faceOpposite_points]
    exact vsub_mem_vectorSpan ℝ hCm hAm
  have hor : ⟪B -ᵥ T.altitudeFoot 1, C -ᵥ A⟫ = 0 :=
    (Submodule.mem_orthogonal' _ (B -ᵥ T.altitudeFoot 1)).mp h2 (C -ᵥ A) hca
  have h3 := dist_mul_dist_eq_abs_areaForm o hF hor
  rw [h3, ← neg_vsub_eq_vsub_rev C B, ← vsub_sub_vsub_cancel_right C A B, map_neg,
    LinearMap.neg_apply, map_sub, o.areaForm_apply_self, o.areaForm_swap (C -ᵥ B) (A -ᵥ B)]
  simp [abs_neg]

lemma dist_altitudeFoot_two_mul {A B C : P} (hABC : AffineIndependent ℝ ![A, B, C])
    (o : Orientation ℝ V (Fin 2)) :
    dist C ((⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ P).altitudeFoot 2) * dist A B =
      |o.areaForm (A -ᵥ B) (C -ᵥ B)| := by
  set T : Affine.Triangle ℝ P := ⟨![A, B, C], hABC⟩ with hT
  have hA0 : T.points (0 : Fin 3) = A := rfl
  have hB1 : T.points (1 : Fin 3) = B := rfl
  have hset : T.points '' ({2}ᶜ : Set (Fin 3)) = ({A, B} : Set P) := by
    have h01 : ({(2 : Fin 3)}ᶜ : Set (Fin 3)) = {0, 1} := by
      ext x
      fin_cases x <;> simp
    rw [h01, Set.image_insert_eq, Set.image_singleton, hA0, hB1]
  have hF : T.altitudeFoot 2 ∈ affineSpan ℝ ({A, B} : Set P) := by
    have h := T.altitudeFoot_mem_affineSpan_image_compl 2
    rwa [hset] at h
  have h2 : C -ᵥ T.altitudeFoot 2 ∈
      (affineSpan ℝ (Set.range (T.faceOpposite 2).points)).directionᗮ :=
    EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal
      (affineSpan ℝ (Set.range (T.faceOpposite 2).points)) (T.points 2)
  have hAm : A ∈ T.points '' ({2}ᶜ : Set (Fin 3)) := ⟨0, by decide, hA0⟩
  have hBm : B ∈ T.points '' ({2}ᶜ : Set (Fin 3)) := ⟨1, by decide, hB1⟩
  have hab : A -ᵥ B ∈ (affineSpan ℝ (Set.range (T.faceOpposite 2).points)).direction := by
    rw [direction_affineSpan, Affine.Simplex.range_faceOpposite_points]
    exact vsub_mem_vectorSpan ℝ hAm hBm
  have hor : ⟪C -ᵥ T.altitudeFoot 2, A -ᵥ B⟫ = 0 :=
    (Submodule.mem_orthogonal' _ (C -ᵥ T.altitudeFoot 2)).mp h2 (A -ᵥ B) hab
  have h3 := dist_mul_dist_eq_abs_areaForm o hF hor
  rw [h3, ← vsub_sub_vsub_cancel_right C A B, map_sub, LinearMap.sub_apply,
    o.areaForm_apply_self, o.areaForm_swap (C -ᵥ B) (A -ᵥ B), sub_zero, abs_neg]

/-- The incenter is the side-length weighted average of the vertices. -/
lemma incenter_vsub {A B C : P} (hABC : AffineIndependent ℝ ![A, B, C])
    (o : Orientation ℝ V (Fin 2)) :
    I A B C hABC -ᵥ B =
      (dist B C + dist A C + dist A B)⁻¹ •
        (dist B C • (A -ᵥ B) + dist A B • (C -ᵥ B)) := by
  rw [show I A B C hABC = (⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ P).incenter from rfl]
  have ha_pos : 0 < dist B C := dist_pos.mpr (ne_BC hABC)
  have hb_pos : 0 < dist A C := dist_pos.mpr (ne_AC hABC)
  have hc_pos : 0 < dist A B := dist_pos.mpr (ne_AB hABC)
  have hP'pos : 0 < dist B C + dist A C + dist A B := by positivity
  have hP'ne : dist B C + dist A C + dist A B ≠ 0 := hP'pos.ne'
  set T : Affine.Triangle ℝ P := ⟨![A, B, C], hABC⟩ with hT
  set w : Fin 3 → ℝ := ![dist B C / (dist B C + dist A C + dist A B),
      dist A C / (dist B C + dist A C + dist A B),
      dist A B / (dist B C + dist A C + dist A B)] with hw_def
  have hsum : ∑ i, w i = 1 := by
    rw [hw_def, Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    field_simp [hP'ne]
  set p := Finset.univ.affineCombination ℝ T.points w with hp_def
  have hp_mem : p ∈ affineSpan ℝ (Set.range T.points) :=
    affineCombination_mem_affineSpan hsum T.points
  have hsd : ∀ i : Fin 3, T.signedInfDist i p =
      |o.areaForm (A -ᵥ B) (C -ᵥ B)| / (dist B C + dist A C + dist A B) := by
    intro i
    rw [T.signedInfDist_affineCombination i hsum]
    fin_cases i
    · have hf := dist_altitudeFoot_zero_mul hABC o
      show (dist B C / (dist B C + dist A C + dist A B)) * ‖A -ᵥ T.altitudeFoot 0‖ = _
      rw [← dist_eq_norm_vsub, div_mul_eq_mul_div,
        mul_comm (dist B C) (dist A (T.altitudeFoot 0)), hf]
    · have hf := dist_altitudeFoot_one_mul hABC o
      rw [dist_comm C A] at hf
      show (dist A C / (dist B C + dist A C + dist A B)) * ‖B -ᵥ T.altitudeFoot 1‖ = _
      rw [← dist_eq_norm_vsub, div_mul_eq_mul_div,
        mul_comm (dist A C) (dist B (T.altitudeFoot 1)), hf]
    · have hf := dist_altitudeFoot_two_mul hABC o
      show (dist A B / (dist B C + dist A C + dist A B)) * ‖C -ᵥ T.altitudeFoot 2‖ = _
      rw [← dist_eq_norm_vsub, div_mul_eq_mul_div,
        mul_comm (dist A B) (dist C (T.altitudeFoot 2)), hf]
  have hp_eq : p = T.incenter :=
    (T.exists_forall_signedInfDist_eq_iff_eq_incenter hp_mem).mp
      ⟨|o.areaForm (A -ᵥ B) (C -ᵥ B)| / (dist B C + dist A C + dist A B), hsd⟩
  have h0 : T.points 0 = A := rfl
  have h1 : T.points 1 = B := rfl
  have h2 : T.points 2 = C := rfl
  rw [← hp_eq, hp_def,
    Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one Finset.univ w T.points hsum B,
    vadd_vsub, Finset.weightedVSubOfPoint_apply, Fin.sum_univ_three]
  simp only [hw_def, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [h0, h1, h2, vsub_self, smul_zero, add_zero, smul_add]
  congr 1
  · rw [div_eq_mul_inv, mul_smul, smul_comm (dist B C) _]
  · rw [div_eq_mul_inv, mul_smul, smul_comm (dist A B) _]

/-! ### Positivity of the perimeter and of the denominator -/

lemma hP'_pos {A B C : P} (hABC : AffineIndependent ℝ ![A, B, C]) :
    0 < dist B C + dist A C + dist A B := by
  have h1 : 0 < dist B C := dist_pos.mpr (ne_BC hABC)
  have h2 : 0 < dist A C := dist_pos.mpr (ne_AC hABC)
  have h3 : 0 < dist A B := dist_pos.mpr (ne_AB hABC)
  positivity

lemma hD2_pos {A B C : P} (hABC : AffineIndependent ℝ ![A, B, C])
    (o : Orientation ℝ V (Fin 2)) :
    0 < 2 * (dist A B ^ 2 * dist B C ^ 2 - ⟪A -ᵥ B, C -ᵥ B⟫ ^ 2) * (dist B C + dist A C + dist A B) := by
  have h1 := hΔ hABC o
  have h2 := hP'_pos hABC
  positivity

/-! ### Values of the area form `ω (O - I, X - I)` at the vertices -/

lemma fA {A B C : P} (hABC : AffineIndependent ℝ ![A, B, C])
    (o : Orientation ℝ V (Fin 2)) :
    o.areaForm (O A B C hABC -ᵥ I A B C hABC) (A -ᵥ I A B C hABC) =
      o.areaForm (A -ᵥ B) (C -ᵥ B) *
        (dist A C * dist A B * ((dist A C + dist A B) * ⟪A -ᵥ B, C -ᵥ B⟫ - dist B C ^ 2 * dist A B) /
          (2 * (dist A B ^ 2 * dist B C ^ 2 - ⟪A -ᵥ B, C -ᵥ B⟫ ^ 2) * (dist B C + dist A C + dist A B))) := by
  have hO1 : O A B C hABC = (⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ P).circumcenter := rfl
  have hI1 : I A B C hABC = (⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ P).incenter := rfl
  rw [hO1, hI1]
  set g := ⟪A -ᵥ B, C -ᵥ B⟫ with hg_def
  set σ := o.areaForm (A -ᵥ B) (C -ᵥ B) with hσ_def
  set Δ := dist A B ^ 2 * dist B C ^ 2 - g ^ 2 with hΔ_def
  set P' := dist B C + dist A C + dist A B with hP'_def
  have hΔne : Δ ≠ 0 := (hΔ hABC o).ne'
  have hΔne' : dist B C ^ 2 * dist A B ^ 2 - g ^ 2 ≠ 0 := by
    rw [mul_comm (dist B C ^ 2) (dist A B ^ 2)]
    exact hΔne
  have hP'ne : P' ≠ 0 := (hP'_pos hABC).ne'
  have hg' : 2 * g = dist B C ^ 2 + dist A B ^ 2 - dist A C ^ 2 := hg
  have e1 : (⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ P).circumcenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ P).incenter =
      ((⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ P).circumcenter -ᵥ B) -
        ((⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ P).incenter -ᵥ B) :=
    (vsub_sub_vsub_cancel_right _ _ _).symm
  have e2 : A -ᵥ (⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ P).incenter =
      (A -ᵥ B) - ((⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ P).incenter -ᵥ B) :=
    (vsub_sub_vsub_cancel_right _ _ _).symm
  rw [e1, e2, circumcenter_vsub hABC o, incenter_vsub hABC o]
  simp only [map_sub, map_add, map_smul, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, o.areaForm_apply_self,
    o.areaForm_swap (C -ᵥ B) (A -ᵥ B)]
  rw [← hg_def, ← hσ_def, ← hP'_def]
  have keyA : -(P' * (dist A B ^ 2 * (dist B C ^ 2 - g))) +
        (dist B C * (dist A B ^ 2 * (dist B C ^ 2 - g)) -
          dist A B * (dist B C ^ 2 * (dist A B ^ 2 - g)) +
            2 * (dist A B ^ 2 * dist B C ^ 2 - g ^ 2) * dist A B) =
      dist A C * dist A B * ((dist A C + dist A B) * g - dist B C ^ 2 * dist A B) := by
    linear_combination (-(dist A B * g)) * hg'
  have keyA2 : σ * (dist A C * dist A B * ((dist A C + dist A B) * g - dist B C ^ 2 * dist A B) /
        (2 * (dist A B ^ 2 * dist B C ^ 2 - g ^ 2) * P')) =
      σ * ((-(P' * (dist A B ^ 2 * (dist B C ^ 2 - g))) +
        (dist B C * (dist A B ^ 2 * (dist B C ^ 2 - g)) -
          dist A B * (dist B C ^ 2 * (dist A B ^ 2 - g)) +
            2 * (dist A B ^ 2 * dist B C ^ 2 - g ^ 2) * dist A B)) /
        (2 * (dist A B ^ 2 * dist B C ^ 2 - g ^ 2) * P')) := by
    rw [keyA]
  rw [keyA2]
  field_simp [hΔne', hP'ne]
  ring

lemma fB {A B C : P} (hABC : AffineIndependent ℝ ![A, B, C])
    (o : Orientation ℝ V (Fin 2)) :
    o.areaForm (O A B C hABC -ᵥ I A B C hABC) (B -ᵥ I A B C hABC) =
      o.areaForm (A -ᵥ B) (C -ᵥ B) *
        (dist B C * dist A B * (dist B C - dist A B) * (dist B C * dist A B + ⟪A -ᵥ B, C -ᵥ B⟫) /
          (2 * (dist A B ^ 2 * dist B C ^ 2 - ⟪A -ᵥ B, C -ᵥ B⟫ ^ 2) * (dist B C + dist A C + dist A B))) := by
  have hO1 : O A B C hABC = (⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ P).circumcenter := rfl
  have hI1 : I A B C hABC = (⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ P).incenter := rfl
  rw [hO1, hI1]
  set g := ⟪A -ᵥ B, C -ᵥ B⟫ with hg_def
  set σ := o.areaForm (A -ᵥ B) (C -ᵥ B) with hσ_def
  set Δ := dist A B ^ 2 * dist B C ^ 2 - g ^ 2 with hΔ_def
  set P' := dist B C + dist A C + dist A B with hP'_def
  have hΔne : Δ ≠ 0 := (hΔ hABC o).ne'
  have hΔne' : dist B C ^ 2 * dist A B ^ 2 - g ^ 2 ≠ 0 := by
    rw [mul_comm (dist B C ^ 2) (dist A B ^ 2)]
    exact hΔne
  have hP'ne : P' ≠ 0 := (hP'_pos hABC).ne'
  have e1 : (⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ P).circumcenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ P).incenter =
      ((⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ P).circumcenter -ᵥ B) -
        ((⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ P).incenter -ᵥ B) :=
    (vsub_sub_vsub_cancel_right _ _ _).symm
  have e2 : B -ᵥ (⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ P).incenter =
      -(((⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ P).incenter -ᵥ B)) :=
    (neg_vsub_eq_vsub_rev _ _).symm
  rw [e1, e2, circumcenter_vsub hABC o, incenter_vsub hABC o]
  simp only [map_sub, map_add, map_neg, map_smul, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, o.areaForm_apply_self,
    o.areaForm_swap (C -ᵥ B) (A -ᵥ B)]
  rw [← hg_def, ← hσ_def, ← hP'_def]
  field_simp [hΔne', hP'ne]
  ring

lemma fC {A B C : P} (hABC : AffineIndependent ℝ ![A, B, C])
    (o : Orientation ℝ V (Fin 2)) :
    o.areaForm (O A B C hABC -ᵥ I A B C hABC) (C -ᵥ I A B C hABC) =
      o.areaForm (A -ᵥ B) (C -ᵥ B) *
        (dist B C * dist A C * (dist B C * dist A B ^ 2 - (dist B C + dist A C) * ⟪A -ᵥ B, C -ᵥ B⟫) /
          (2 * (dist A B ^ 2 * dist B C ^ 2 - ⟪A -ᵥ B, C -ᵥ B⟫ ^ 2) * (dist B C + dist A C + dist A B))) := by
  have hO1 : O A B C hABC = (⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ P).circumcenter := rfl
  have hI1 : I A B C hABC = (⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ P).incenter := rfl
  rw [hO1, hI1]
  set g := ⟪A -ᵥ B, C -ᵥ B⟫ with hg_def
  set σ := o.areaForm (A -ᵥ B) (C -ᵥ B) with hσ_def
  set Δ := dist A B ^ 2 * dist B C ^ 2 - g ^ 2 with hΔ_def
  set P' := dist B C + dist A C + dist A B with hP'_def
  have hΔne : Δ ≠ 0 := (hΔ hABC o).ne'
  have hΔne' : dist B C ^ 2 * dist A B ^ 2 - g ^ 2 ≠ 0 := by
    rw [mul_comm (dist B C ^ 2) (dist A B ^ 2)]
    exact hΔne
  have hP'ne : P' ≠ 0 := (hP'_pos hABC).ne'
  have hg' : 2 * g = dist B C ^ 2 + dist A B ^ 2 - dist A C ^ 2 := hg
  have e1 : (⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ P).circumcenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ P).incenter =
      ((⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ P).circumcenter -ᵥ B) -
        ((⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ P).incenter -ᵥ B) :=
    (vsub_sub_vsub_cancel_right _ _ _).symm
  have e2 : C -ᵥ (⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ P).incenter =
      (C -ᵥ B) - ((⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ P).incenter -ᵥ B) :=
    (vsub_sub_vsub_cancel_right _ _ _).symm
  rw [e1, e2, circumcenter_vsub hABC o, incenter_vsub hABC o]
  simp only [map_sub, map_add, map_smul, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, o.areaForm_apply_self,
    o.areaForm_swap (C -ᵥ B) (A -ᵥ B)]
  rw [← hg_def, ← hσ_def, ← hP'_def]
  have keyC : P' * (dist B C ^ 2 * (dist A B ^ 2 - g)) -
        2 * (dist A B ^ 2 * dist B C ^ 2 - g ^ 2) * dist B C +
        (dist B C * (dist A B ^ 2 * (dist B C ^ 2 - g)) -
          dist A B * (dist B C ^ 2 * (dist A B ^ 2 - g))) =
      dist B C * dist A C * (dist B C * dist A B ^ 2 - (dist B C + dist A C) * g) := by
    linear_combination (dist B C * g) * hg'
  have keyC2 : σ * (dist B C * dist A C * (dist B C * dist A B ^ 2 - (dist B C + dist A C) * g) /
        (2 * (dist A B ^ 2 * dist B C ^ 2 - g ^ 2) * P')) =
      σ * ((P' * (dist B C ^ 2 * (dist A B ^ 2 - g)) -
        2 * (dist A B ^ 2 * dist B C ^ 2 - g ^ 2) * dist B C +
        (dist B C * (dist A B ^ 2 * (dist B C ^ 2 - g)) -
          dist A B * (dist B C ^ 2 * (dist A B ^ 2 - g)))) /
        (2 * (dist A B ^ 2 * dist B C ^ 2 - g ^ 2) * P')) := by
    rw [keyC]
  rw [keyC2]
  field_simp [hΔne', hP'ne]
  ring

lemma hacg {A B C : P} (hABC : AffineIndependent ℝ ![A, B, C]) :
    0 < dist B C * dist A B + ⟪A -ᵥ B, C -ᵥ B⟫ := by
  have hg2 : 2 * ⟪A -ᵥ B, C -ᵥ B⟫ = dist B C ^ 2 + dist A B ^ 2 - dist A C ^ 2 := hg
  have h1 : dist B C * dist A B + ⟪A -ᵥ B, C -ᵥ B⟫ =
      ((dist B C + dist A B) ^ 2 - dist A C ^ 2) / 2 := by
    linear_combination (1 / 2 : ℝ) * hg2
  rw [h1]
  have hlt := lt_b hABC
  have h2 : 0 < (dist B C + dist A B) ^ 2 - dist A C ^ 2 := by
    have h3 : dist A C ^ 2 < (dist B C + dist A B) ^ 2 := by
      apply sq_lt_sq' _ hlt
      have hbc : 0 < dist B C := dist_pos.mpr (ne_BC hABC)
      have hab : 0 < dist A B := dist_pos.mpr (ne_AB hABC)
      have hac : 0 < dist A C := dist_pos.mpr (ne_AC hABC)
      linarith
    linarith
  linarith

lemma hbrA {A B C : P} (hABC : AffineIndependent ℝ ![A, B, C]) (h1 : dist A B < dist A C) :
    (dist A C + dist A B) * ⟪A -ᵥ B, C -ᵥ B⟫ - dist B C ^ 2 * dist A B < 0 := by
  have hg2 : 2 * ⟪A -ᵥ B, C -ᵥ B⟫ = dist B C ^ 2 + dist A B ^ 2 - dist A C ^ 2 := hg
  have he : (dist A C + dist A B) * ⟪A -ᵥ B, C -ᵥ B⟫ - dist B C ^ 2 * dist A B =
      (dist A C - dist A B) * (dist B C ^ 2 - (dist A C + dist A B) ^ 2) / 2 := by
    linear_combination ((dist A C + dist A B) / 2) * hg2
  rw [he]
  have hbc : 0 < dist A C - dist A B := sub_pos.mpr h1
  have h3 : dist B C ^ 2 - (dist A C + dist A B) ^ 2 < 0 := by
    have hlt := lt_a hABC
    have h4 : dist B C ^ 2 < (dist A B + dist A C) ^ 2 := by
      apply sq_lt_sq' _ hlt
      have hbc2 : 0 < dist B C := dist_pos.mpr (ne_BC hABC)
      have hab : 0 < dist A B := dist_pos.mpr (ne_AB hABC)
      have hac : 0 < dist A C := dist_pos.mpr (ne_AC hABC)
      linarith
    have h5 : (dist A B + dist A C) ^ 2 = (dist A C + dist A B) ^ 2 := by ring
    rw [h5] at h4
    linarith
  have h6 : (dist A C - dist A B) * (dist B C ^ 2 - (dist A C + dist A B) ^ 2) < 0 :=
    mul_neg_of_pos_of_neg hbc h3
  linarith

lemma hbrC {A B C : P} (hABC : AffineIndependent ℝ ![A, B, C]) (h2 : dist A C < dist B C) :
    dist B C * dist A B ^ 2 - (dist B C + dist A C) * ⟪A -ᵥ B, C -ᵥ B⟫ < 0 := by
  have hg2 : 2 * ⟪A -ᵥ B, C -ᵥ B⟫ = dist B C ^ 2 + dist A B ^ 2 - dist A C ^ 2 := hg
  have he : dist B C * dist A B ^ 2 - (dist B C + dist A C) * ⟪A -ᵥ B, C -ᵥ B⟫ =
      (dist B C - dist A C) * (dist A B ^ 2 - (dist B C + dist A C) ^ 2) / 2 := by
    linear_combination (-((dist B C + dist A C) / 2)) * hg2
  rw [he]
  have hab : 0 < dist B C - dist A C := sub_pos.mpr h2
  have h3 : dist A B ^ 2 - (dist B C + dist A C) ^ 2 < 0 := by
    have hlt := lt_c hABC
    have h4 : dist A B ^ 2 < (dist A C + dist B C) ^ 2 := by
      apply sq_lt_sq' _ hlt
      have hbc2 : 0 < dist B C := dist_pos.mpr (ne_BC hABC)
      have hab2 : 0 < dist A B := dist_pos.mpr (ne_AB hABC)
      have hac : 0 < dist A C := dist_pos.mpr (ne_AC hABC)
      linarith
    have h5 : (dist A C + dist B C) ^ 2 = (dist B C + dist A C) ^ 2 := by ring
    rw [h5] at h4
    linarith
  have h6 : (dist B C - dist A C) * (dist A B ^ 2 - (dist B C + dist A C) ^ 2) < 0 :=
    mul_neg_of_pos_of_neg hab h3
  linarith

lemma hsA {A B C : P} (hABC : AffineIndependent ℝ ![A, B, C])
    (o : Orientation ℝ V (Fin 2)) (h1 : dist A B < dist A C) :
    dist A C * dist A B * ((dist A C + dist A B) * ⟪A -ᵥ B, C -ᵥ B⟫ - dist B C ^ 2 * dist A B) /
      (2 * (dist A B ^ 2 * dist B C ^ 2 - ⟪A -ᵥ B, C -ᵥ B⟫ ^ 2) * (dist B C + dist A C + dist A B)) < 0 := by
  have hnum : dist A C * dist A B * ((dist A C + dist A B) * ⟪A -ᵥ B, C -ᵥ B⟫ - dist B C ^ 2 * dist A B) < 0 := by
    have hb : 0 < dist A C := dist_pos.mpr (ne_AC hABC)
    have hc : 0 < dist A B := dist_pos.mpr (ne_AB hABC)
    exact mul_neg_of_pos_of_neg (mul_pos hb hc) (hbrA hABC h1)
  exact div_neg_of_neg_of_pos hnum (hD2_pos hABC o)

lemma hsB {A B C : P} (hABC : AffineIndependent ℝ ![A, B, C])
    (o : Orientation ℝ V (Fin 2)) (h1 : dist A B < dist A C) (h2 : dist A C < dist B C) :
    0 < dist B C * dist A B * (dist B C - dist A B) * (dist B C * dist A B + ⟪A -ᵥ B, C -ᵥ B⟫) /
      (2 * (dist A B ^ 2 * dist B C ^ 2 - ⟪A -ᵥ B, C -ᵥ B⟫ ^ 2) * (dist B C + dist A C + dist A B)) := by
  have hnum : 0 < dist B C * dist A B * (dist B C - dist A B) * (dist B C * dist A B + ⟪A -ᵥ B, C -ᵥ B⟫) := by
    have ha : 0 < dist B C := dist_pos.mpr (ne_BC hABC)
    have hc : 0 < dist A B := dist_pos.mpr (ne_AB hABC)
    have hac : 0 < dist B C - dist A B := sub_pos.mpr (lt_trans h1 h2)
    have hacg' := hacg hABC
    positivity
  exact div_pos hnum (hD2_pos hABC o)

lemma hsC {A B C : P} (hABC : AffineIndependent ℝ ![A, B, C])
    (o : Orientation ℝ V (Fin 2)) (h2 : dist A C < dist B C) :
    dist B C * dist A C * (dist B C * dist A B ^ 2 - (dist B C + dist A C) * ⟪A -ᵥ B, C -ᵥ B⟫) /
      (2 * (dist A B ^ 2 * dist B C ^ 2 - ⟪A -ᵥ B, C -ᵥ B⟫ ^ 2) * (dist B C + dist A C + dist A B)) < 0 := by
  have hnum : dist B C * dist A C * (dist B C * dist A B ^ 2 - (dist B C + dist A C) * ⟪A -ᵥ B, C -ᵥ B⟫) < 0 := by
    have ha : 0 < dist B C := dist_pos.mpr (ne_BC hABC)
    have hb : 0 < dist A C := dist_pos.mpr (ne_AC hABC)
    exact mul_neg_of_pos_of_neg (mul_pos ha hb) (hbrC hABC h2)
  exact div_neg_of_neg_of_pos hnum (hD2_pos hABC o)

lemma wIO_ne {A B C : P} (hABC : AffineIndependent ℝ ![A, B, C])
    (o : Orientation ℝ V (Fin 2)) (h1 : dist A B < dist A C) (h2 : dist A C < dist B C) :
    O A B C hABC -ᵥ I A B C hABC ≠ 0 := by
  intro hw
  have hB := fB hABC o
  rw [hw, map_zero, LinearMap.zero_apply] at hB
  have hσne := areaForm_ne_zero hABC o
  have hFB := hsB hABC o h1 h2
  exact (mul_ne_zero hσne hFB.ne') hB.symm

/-! ### The crossing argument -/

lemma crossing {A B C : P} (hABC : AffineIndependent ℝ ![A, B, C])
    (o : Orientation ℝ V (Fin 2))
    (hw : O A B C hABC -ᵥ I A B C hABC ≠ 0) {X Y : P}
    (h : o.areaForm (O A B C hABC -ᵥ I A B C hABC) (X -ᵥ I A B C hABC) *
          o.areaForm (O A B C hABC -ᵥ I A B C hABC) (Y -ᵥ I A B C hABC) < 0) :
    ∃ Q : P, Q ∈ line[ℝ, I A B C hABC, O A B C hABC] ∧ Wbtw ℝ X Q Y := by
  set I' := I A B C hABC with hI'_def
  set O' := O A B C hABC with hO'_def
  set w := O' -ᵥ I' with hw_def
  set fx := o.areaForm w (X -ᵥ I') with hfx_def
  set fy := o.areaForm w (Y -ᵥ I') with hfy_def
  have hne : fx - fy ≠ 0 := by
    intro h0
    have he : fx = fy := sub_eq_zero.mp h0
    have e : fx * fy = fx ^ 2 := by rw [← he]; ring
    rw [e] at h
    exact (not_lt_of_ge (sq_nonneg fx)) h
  set t := fx / (fx - fy) with ht_def
  have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := by
    rcases mul_neg_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have h3 : 0 < fx - fy := by linarith
      constructor
      · exact div_nonneg h1.le h3.le
      · rw [ht_def, div_le_one h3]
        linarith
    · have h3 : fx - fy < 0 := by linarith
      have e : fx / (fx - fy) = (-fx) / (fy - fx) := by
        rw [← neg_div_neg_eq]
        congr 1
        ring
      have h4 : 0 < fy - fx := by linarith
      constructor
      · rw [ht_def, e]
        exact div_nonneg (neg_pos.mpr h1).le h4.le
      · rw [ht_def, e, div_le_one h4]
        linarith
  refine ⟨AffineMap.lineMap X Y t, ?_, wbtw_lineMap_iff.mpr (Or.inr ht01)⟩
  have hfq : o.areaForm w ((AffineMap.lineMap X Y t : P) -ᵥ I') = 0 := by
    have e1 : (AffineMap.lineMap X Y t : P) -ᵥ I' = (1 - t) • (X -ᵥ I') + t • (Y -ᵥ I') := by
      rw [AffineMap.lineMap_apply]
      have e2v : (t • (Y -ᵥ X) +ᵥ X) -ᵥ I' = t • (Y -ᵥ X) + (X -ᵥ I') := by
        have h1 : t • (Y -ᵥ X) +ᵥ X = (t • (Y -ᵥ X) + (X -ᵥ I')) +ᵥ I' := by
          rw [← vadd_vadd, vsub_vadd]
        rw [h1, vadd_vsub]
      rw [e2v, ← vsub_sub_vsub_cancel_right Y X I']
      rw [smul_sub, sub_smul, one_smul]
      abel
    rw [e1, map_add, map_smul, map_smul, ← hfx_def, ← hfy_def, smul_eq_mul, smul_eq_mul, ht_def]
    field_simp [hne]
    ring
  by_cases hq : (AffineMap.lineMap X Y t : P) -ᵥ I' = 0
  · have hQI : AffineMap.lineMap X Y t = I' := vsub_eq_zero_iff_eq.mp hq
    rw [hQI]
    exact left_mem_affineSpan_pair _ _ _
  · have hcs := o.inner_sq_add_areaForm_sq w ((AffineMap.lineMap X Y t : P) -ᵥ I')
    rw [hfq] at hcs
    simp at hcs
    have h2 : ⟪w, (AffineMap.lineMap X Y t : P) -ᵥ I'⟫ ^ 2 =
        (‖w‖ * ‖(AffineMap.lineMap X Y t : P) -ᵥ I'‖) ^ 2 := by
      rw [mul_pow]
      linarith [hcs]
    have habs : ‖⟪w, (AffineMap.lineMap X Y t : P) -ᵥ I'⟫‖ =
        ‖w‖ * ‖(AffineMap.lineMap X Y t : P) -ᵥ I'‖ := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h3 | h3
      · rw [Real.norm_eq_abs, h3, abs_of_nonneg (by positivity)]
      · rw [Real.norm_eq_abs, h3, abs_neg, abs_of_nonneg (by positivity)]
    obtain ⟨r, _, hr⟩ := (norm_inner_eq_norm_iff hw hq).mp habs
    have hQ : AffineMap.lineMap I' O' r = AffineMap.lineMap X Y t := by
      rw [AffineMap.lineMap_apply, ← hw_def, ← hr, vsub_vadd]
    exact (mem_affineSpan_pair_iff_exists_lineMap_eq).mpr ⟨r, hQ⟩

snip end

problem usa1989_p4 (A B C : P)
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hacuteA : ∠ C A B < π / 2) (hacuteB : ∠ A B C < π / 2) (hacuteC : ∠ B C A < π / 2)
    (hc_lt_b : dist A B < dist A C) (hb_lt_a : dist A C < dist B C) :
    (∃ X : P, X ∈ line[ℝ, I A B C hABC, O A B C hABC] ∧ Wbtw ℝ A X B) ∧
    ∃ Y : P, Y ∈ line[ℝ, I A B C hABC, O A B C hABC] ∧ Wbtw ℝ B Y C := by
  -- Note: the conclusion in fact holds for any (not necessarily acute) triangle with
  -- `AB < AC < BC`; the acuteness hypotheses are recorded for faithfulness to the problem.
  have _ := hacuteA
  have _ := hacuteB
  have _ := hacuteC
  haveI : FiniteDimensional ℝ V := FiniteDimensional.of_fact_finrank_eq_two
  set o : Orientation ℝ V (Fin 2) :=
    (Module.finBasisOfFinrankEq ℝ V (show finrank ℝ V = 2 from Fact.out)).orientation with ho_def
  have hw := wIO_ne hABC o hc_lt_b hb_lt_a
  have hAv := fA hABC o
  have hBv := fB hABC o
  have hCv := fC hABC o
  have hsA' := hsA hABC o hc_lt_b
  have hsB' := hsB hABC o hc_lt_b hb_lt_a
  have hsC' := hsC hABC o hb_lt_a
  have hσne := areaForm_ne_zero hABC o
  constructor
  · apply crossing hABC o hw
    rw [hAv, hBv, mul_mul_mul_comm, ← pow_two]
    exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hσne) (mul_neg_of_neg_of_pos hsA' hsB')
  · apply crossing hABC o hw
    rw [hBv, hCv, mul_mul_mul_comm, ← pow_two]
    exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hσne) (mul_neg_of_pos_of_neg hsB' hsC')

end Usa1989P4
