/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.Analysis.InnerProductSpace.OfNorm
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 1996, Problem 3

Let ABC be a triangle. Prove that there is a line ℓ (in the plane of
triangle ABC) such that the intersection of the interior of triangle ABC
and the interior of its reflection A′B′C′ in ℓ has area more than 2/3
the area of triangle ABC.
-/

namespace Usa1996P3

open MeasureTheory

open scoped ENNReal InnerProductSpace


/-- The plane, seen both as the affine ambient space and as its vector space. -/
abbrev E := EuclideanSpace ℝ (Fin 2)

/-- The reflection of a point `x` in the line through `P` with direction `w`
(where `w ≠ 0`). -/
noncomputable def reflectionInLine (P w : E) (x : E) : E :=
  (Submodule.span ℝ {w}).reflection (x - P) + P

snip begin

/-- `Submodule.reflection` respects equality of subspaces (the instance is a proposition,
so proof irrelevance applies). -/
lemma reflection_congr {K₁ K₂ : Submodule ℝ E} [K₁.HasOrthogonalProjection]
    [K₂.HasOrthogonalProjection] (h : K₁ = K₂) : K₁.reflection = K₂.reflection := by
  subst h
  rfl

/-- Reflecting a unit vector `u` in the line spanned by `u + v` gives the unit vector `v`
(with `‖v‖ = ‖u‖`). This is the reflection computation behind the angle bisector. -/
lemma reflection_unit_sub (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : u ≠ v)
    (huv0 : u + v ≠ 0) :
    (Submodule.span ℝ {u + v}).reflection u = v := by
  have huv' : u - v ≠ 0 := sub_ne_zero.mpr huv
  have hmem : u + v ∈ (Submodule.span ℝ {u - v})ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_left, inner_add_right,
      inner_add_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hu, hv,
      real_inner_comm u v]
    ring
  have hfin1 : Module.finrank ℝ (Submodule.span ℝ {u + v}) = 1 := finrank_span_singleton huv0
  have hfin2 : Module.finrank ℝ (Submodule.span ℝ {u - v})ᗮ = 1 := by
    have h := Submodule.finrank_add_finrank_orthogonal (Submodule.span ℝ {u - v})
    rw [finrank_span_singleton huv', finrank_euclideanSpace, Fintype.card_fin] at h
    omega
  have hsub : Submodule.span ℝ {u + v} = (Submodule.span ℝ {u - v})ᗮ :=
    Submodule.eq_of_le_of_finrank_eq
      ((Submodule.span_singleton_le_iff_mem _ _).mpr hmem) (by rw [hfin1, hfin2])
  rw [reflection_congr hsub]
  exact Submodule.reflection_sub (by rw [hu, hv])

lemma measurePreserving_reflectionInLine (P w : E) :
    MeasurePreserving (reflectionInLine P w) volume volume :=
  ((measurePreserving_add_right volume P).comp
    (Submodule.reflection _).measurePreserving).comp (measurePreserving_add_right volume (-P))

lemma measurable_reflectionInLine (P w : E) : Measurable (reflectionInLine P w) :=
  ((Submodule.reflection _).continuous.measurable.comp
    (measurable_id.sub_const P)).add_const P

lemma reflectionInLine_involutive (P w : E) : Function.Involutive (reflectionInLine P w) := by
  intro x
  simp only [reflectionInLine]
  rw [add_sub_cancel_right, Submodule.reflection_reflection, sub_add_cancel]

lemma volume_reflectionInLine_image (P w : E) {s : Set E} (hs : MeasurableSet s) :
    volume (reflectionInLine P w '' s) = volume s := by
  have hMP : MeasurePreserving (reflectionInLine P w) volume volume :=
    measurePreserving_reflectionInLine P w
  have himg : reflectionInLine P w '' s = reflectionInLine P w ⁻¹' s :=
    congrFun (Set.image_eq_preimage_of_inverse (reflectionInLine_involutive P w)
      (reflectionInLine_involutive P w)) s
  calc volume (reflectionInLine P w '' s)
      = volume (reflectionInLine P w ⁻¹' s) := by rw [himg]
    _ = (volume.map (reflectionInLine P w)) s :=
        (MeasureTheory.Measure.map_apply (measurable_reflectionInLine P w) hs).symm
    _ = volume s := by rw [hMP.map_eq]

lemma volume_add_const_image (s : Set E) (hs : MeasurableSet s) (p : E) :
    volume ((fun x ↦ x + p) '' s) = volume s := by
  have himg : (fun x ↦ x + p) '' s = (fun x ↦ x + (-p)) ⁻¹' s :=
    congrFun (Set.image_eq_preimage_of_inverse (f := fun x ↦ x + p) (g := fun x ↦ x + (-p))
      (fun x ↦ by simp) (fun x ↦ by simp)) s
  calc volume ((fun x ↦ x + p) '' s)
      = volume ((fun x ↦ x + (-p)) ⁻¹' s) := by rw [himg]
    _ = (volume.map (fun x ↦ x + (-p))) s :=
        (MeasureTheory.Measure.map_apply
          (measurePreserving_add_right volume (-p)).measurable hs).symm
    _ = volume s := by rw [(measurePreserving_add_right volume (-p)).map_eq]

lemma reflectionInLine_image_convexHull (P w : E) (s : Set E) :
    reflectionInLine P w '' convexHull ℝ s = convexHull ℝ (reflectionInLine P w '' s) := by
  let f : E →ᵃ[ℝ] E := AffineMap.mk' (reflectionInLine P w)
    (Submodule.reflection (Submodule.span ℝ {w})).toLinearMap P
    (fun p' ↦ by simp [reflectionInLine])
  have hfeq : ⇑f = reflectionInLine P w := AffineMap.coe_mk' _ _ _ _
  rw [← hfeq, AffineMap.image_convexHull]

/-- The interior of the convex hull of a finite set has the same volume as the hull. -/
lemma volume_interior_convexHull {s : Set E} (hs : s.Finite) :
    volume (interior (convexHull ℝ s)) = volume (convexHull ℝ s) := by
  have hfront : volume (frontier (convexHull ℝ s)) = 0 :=
    Convex.addHaar_frontier volume (convex_convexHull ℝ s)
  have hcl : closure (convexHull ℝ s) = convexHull ℝ s :=
    (hs.isClosed_convexHull ℝ).closure_eq
  have hdisj : Disjoint (interior (convexHull ℝ s)) (frontier (convexHull ℝ s)) :=
    disjoint_sdiff_self_right
  calc volume (interior (convexHull ℝ s))
      = volume (interior (convexHull ℝ s) ∪ frontier (convexHull ℝ s)) := by
        rw [measure_union hdisj isClosed_frontier.measurableSet, hfront, add_zero]
    _ = volume (closure (convexHull ℝ s)) := by rw [← closure_eq_interior_union_frontier]
    _ = volume (convexHull ℝ s) := by rw [hcl]

lemma finite_convexHull_meas {s : Set E} (hs : s.Finite) : MeasurableSet (convexHull ℝ s) :=
  (hs.isClosed_convexHull ℝ).measurableSet

/-- A hyperplane in the plane has volume zero. -/
lemma volume_side_zero {z P : E} (hz : z ≠ 0) : volume {x : E | ⟪z, x - P⟫_ℝ = 0} = 0 := by
  have heq : {x : E | ⟪z, x - P⟫_ℝ = 0} =
      (fun x ↦ x + P) '' ((Submodule.span ℝ {z})ᗮ : Set E) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe]
    constructor
    · intro h
      exact ⟨x - P, by rwa [Submodule.mem_orthogonal_singleton_iff_inner_right], by simp⟩
    · rintro ⟨y, hy, rfl⟩
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hy
      simpa using hy
  rw [heq, volume_add_const_image _ (Submodule.closed_of_finiteDimensional _).measurableSet P]
  apply MeasureTheory.Measure.addHaar_submodule volume _ ?_
  intro htop
  apply hz
  have hmem : z ∈ (Submodule.span ℝ {z})ᗮ := by rw [htop]; exact Submodule.mem_top
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hmem
  exact inner_self_eq_zero.mp hmem

/-- If two sides of a triangle are linearly dependent, the vertices are collinear. -/
lemma collinear_of_smul_eq_smul {P Q R : E} {s t : ℝ} (hs : s ≠ 0)
    (h : s • (Q - P) = t • (R - P)) : Collinear ℝ {P, Q, R} := by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨P, R - P, fun p hp ↦ ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with h1 | h2 | h3
  · refine ⟨0, ?_⟩
    rw [h1]
    simp
  · refine ⟨s⁻¹ * t, ?_⟩
    rw [h2]
    have e : Q - P = (s⁻¹ * t) • (R - P) := by
      have e1 : Q - P = s⁻¹ • (s • (Q - P)) := (inv_smul_smul₀ hs _).symm
      rw [e1, h, smul_smul]
    rw [← e]
    simp
  · refine ⟨1, ?_⟩
    rw [h3]
    simp

/-- The linear independence of two sides of a genuine triangle. -/
lemma li_of_not_collinear (P Q R : E) (hnc : ¬ Collinear ℝ {P, Q, R}) :
    LinearIndependent ℝ ![Q - P, R - P] := by
  have hPRne : P ≠ R := by
    rintro rfl
    apply hnc
    have : ({P, Q, P} : Set E) = {Q, P} := by ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [this]
    exact collinear_pair ℝ Q P
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases hs : s = 0
  · subst hs
    simp only [zero_smul, zero_add] at hst
    exact ⟨rfl, (smul_eq_zero_iff_left (sub_ne_zero.mpr hPRne.symm)).mp hst⟩
  · exfalso
    have h2 : s • (Q - P) = - (t • (R - P)) := eq_neg_of_add_eq_zero_left hst
    rw [← neg_smul] at h2
    exact hnc (collinear_of_smul_eq_smul hs (t := -t) h2)

/-- From a triangle one can select a vertex `P` opposite to a shortest side, and label the
other two vertices `Q`, `R` so that `QR ≤ PQ ≤ PR`. -/
lemma pick_vertex (A B C : E) :
    ∃ P Q R : E, ({P, Q, R} : Set E) = {A, B, C} ∧ dist Q R ≤ dist P Q ∧ dist P Q ≤ dist P R := by
  rcases le_total (dist B C) (dist A B) with h1 | h1 <;>
    rcases le_total (dist B C) (dist C A) with h2 | h2 <;>
    rcases le_total (dist A B) (dist C A) with h3 | h3
  · exact ⟨A, B, C, rfl, h1, by rwa [dist_comm A C]⟩
  · exact ⟨A, C, B, by ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto, by rw [dist_comm C B, dist_comm A C]; exact h2,
      by rw [dist_comm A C]; exact h3⟩
  · exact ⟨A, B, C, rfl, h1, by rwa [dist_comm A C]⟩
  · exact ⟨B, C, A, by ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto, h2, by rw [dist_comm B A]; exact h1⟩
  · exact ⟨C, B, A, by ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto, by rw [dist_comm B A, dist_comm C B]; exact h1,
      by rw [dist_comm C B]; exact h2⟩
  · exact ⟨A, B, C, rfl, le_trans h2 h3, by rw [dist_comm A C]; exact le_trans h1 h2⟩
  · exact ⟨C, A, B, by ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto, h3, by rw [dist_comm C B]; exact h2⟩
  · exact ⟨B, A, C, by ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto, by rw [dist_comm A C, dist_comm B A]; exact h3,
      by rw [dist_comm B A]; exact h1⟩

/-- The geometric heart of the problem: if `QR` is a shortest side of the triangle `PQR`
and `PQ ≤ PR`, then reflection in the angle bisector at `P` produces an overlap whose
area exceeds `2/3` of the area of the triangle. -/
lemma reflection_overlap (P Q R : E) (hnc : ¬ Collinear ℝ {P, Q, R})
    (hQR : dist Q R ≤ dist P Q) (hPQ : dist P Q ≤ dist P R) :
    ∃ w : E, w ≠ 0 ∧
      (2 / 3 : ℝ≥0∞) * volume (interior (convexHull ℝ {P, Q, R})) <
        volume (interior (convexHull ℝ {P, Q, R}) ∩
          interior (convexHull ℝ (reflectionInLine P w '' {P, Q, R}))) := by
  -- The vertices are pairwise distinct.
  have hPQne : P ≠ Q := by
    rintro rfl
    apply hnc
    have : ({P, P, R} : Set E) = {P, R} := by ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [this]
    exact collinear_pair ℝ P R
  have hPRne : P ≠ R := by
    rintro rfl
    apply hnc
    have : ({P, Q, P} : Set E) = {Q, P} := by ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [this]
    exact collinear_pair ℝ Q P
  have hQRne : Q ≠ R := by
    rintro rfl
    apply hnc
    have : ({P, Q, Q} : Set E) = {P, Q} := by ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [this]
    exact collinear_pair ℝ P Q
  -- Notation for the side lengths.
  set c := ‖Q - P‖ with hc_def
  set b := ‖R - P‖ with hb_def
  have hc : 0 < c := norm_pos_iff.mpr (sub_ne_zero.mpr hPQne.symm)
  have hb : 0 < b := norm_pos_iff.mpr (sub_ne_zero.mpr hPRne.symm)
  have hcb : c ≤ b := by
    have e1 : dist P Q = c := by rw [hc_def, dist_comm, dist_eq_norm]
    have e2 : dist P R = b := by rw [hb_def, dist_comm, dist_eq_norm]
    rw [← e1, ← e2]
    exact hPQ
  have ha : ‖R - Q‖ ≤ c := by
    have e1 : dist Q R = ‖R - Q‖ := by rw [dist_comm, dist_eq_norm]
    have e2 : dist P Q = c := by rw [hc_def, dist_comm, dist_eq_norm]
    rw [← e1, ← e2]
    exact hQR
  have hLI : LinearIndependent ℝ ![Q - P, R - P] := li_of_not_collinear P Q R hnc
  -- The unit vectors along the two sides at `P`.
  set u := c⁻¹ • (Q - P) with hu_def
  set v := b⁻¹ • (R - P) with hv_def
  have hu1 : ‖u‖ = 1 := by
    rw [hu_def, norm_smul, norm_inv, Real.norm_of_nonneg hc.le, ← hc_def, inv_mul_cancel₀ hc.ne']
  have hv1 : ‖v‖ = 1 := by
    rw [hv_def, norm_smul, norm_inv, Real.norm_of_nonneg hb.le, ← hb_def, inv_mul_cancel₀ hb.ne']
  have hv1u : Q - P = c • u := by rw [hu_def, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  have hv2v : R - P = b • v := by rw [hv_def, smul_smul, mul_inv_cancel₀ hb.ne', one_smul]
  -- The two sides are not parallel.
  have hdep : ∀ r : ℝ, u ≠ r • v := by
    intro r h
    apply hnc
    apply collinear_of_smul_eq_smul (s := 1) one_ne_zero (t := c * r / b)
    rw [one_smul, hv1u, h, hv_def, smul_smul, smul_smul]
    congr 1
  have huv_ne : u ≠ v := by
    have h := hdep 1
    rwa [one_smul] at h
  have huv_neg_ne : u ≠ -v := by
    have h := hdep (-1)
    rwa [neg_smul, one_smul] at h
  -- The angle bisector direction at `P`.
  set w := u + v with hw_def
  have hw : w ≠ 0 := by
    intro h0
    apply huv_neg_ne
    rw [hw_def] at h0
    exact eq_neg_of_add_eq_zero_left h0
  have hσu : (Submodule.span ℝ {w}).reflection u = v := reflection_unit_sub u v hu1 hv1 huv_ne hw
  have hσv : (Submodule.span ℝ {w}).reflection v = u := by
    rw [← hσu, Submodule.reflection_reflection]
  -- The point `D` where the bisector meets `QR`, and the reflection `Q'` of `Q`.
  set τ := c / (b + c) with hτ_def
  set D := Q + τ • (R - Q) with hD_def
  set Q' := P + (c / b) • (R - P) with hQ'_def
  have hbc : (0 : ℝ) < b + c := add_pos hb hc
  have hτ0 : 0 < τ := div_pos hc hbc
  have hτ1 : τ ≤ 1 := (div_le_one hbc).mpr (le_add_of_nonneg_left hb.le)
  have hσP : reflectionInLine P w P = P := by simp [reflectionInLine]
  have hσQ : reflectionInLine P w Q = Q' := by
    rw [hQ'_def]
    simp only [reflectionInLine]
    rw [hv1u, map_smul, hσu]
    have e : c • v = (c / b) • (R - P) := by rw [hv_def, smul_smul, ← div_eq_mul_inv]
    rw [e, add_comm]
  have hDP : D - P = (c * b / (b + c)) • w := by
    have e1 : D - P = (Q - P) + τ • ((R - P) - (Q - P)) := by rw [hD_def]; module
    rw [e1, hv1u, hv2v, hw_def, smul_add]
    have e2 : c • u + τ • (b • v - c • u) =
        (c * b / (b + c)) • u + (c * b / (b + c)) • v := by
      rw [hτ_def, smul_sub]
      rw [show (c / (b + c)) • (b • v) = ((c / (b + c)) * b) • v from smul_smul _ _ _,
        show (c / (b + c)) • (c • u) = ((c / (b + c)) * c) • u from smul_smul _ _ _]
      have hcoef : c - c * c / (b + c) = c * b / (b + c) := by
        field_simp [hbc.ne']
        ring
      have e3 : (c / (b + c)) * b = c * b / (b + c) := by rw [div_mul_eq_mul_div₀]
      have e4 : (c / (b + c)) * c = c * c / (b + c) := by rw [div_mul_eq_mul_div₀]
      have e5 : c • u + ((c * b / (b + c)) • v - (c * c / (b + c)) • u) =
          (c • u - (c * c / (b + c)) • u) + (c * b / (b + c)) • v := by abel
      rw [e3, e4, e5, ← sub_smul, hcoef]
    rw [e2]
  have hσD : reflectionInLine P w D = D := by
    simp only [reflectionInLine]
    have hmem : D - P ∈ Submodule.span ℝ {w} := by
      rw [hDP]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
    rw [Submodule.reflection_mem_subspace_eq_self hmem, sub_add_cancel]
  -- `D` lies on the segment `QR` and `Q'` lies on the segment `PR`.
  have hDseg : D ∈ segment ℝ Q R := by
    refine ⟨1 - τ, τ, sub_nonneg.mpr hτ1, hτ0.le, sub_add_cancel 1 τ, ?_⟩
    rw [hD_def]
    module
  have hQ'seg : Q' ∈ segment ℝ P R := by
    have hcb1 : c / b ≤ 1 := (div_le_one hb).mpr hcb
    refine ⟨1 - c / b, c / b, sub_nonneg.mpr hcb1, div_nonneg hc.le hb.le,
      sub_add_cancel 1 _, ?_⟩
    rw [hQ'_def]
    module
  -- The triangle `T`, the two halves `T1`, `T2` of the overlap quadrilateral.
  set T := convexHull ℝ ({P, Q, R} : Set E) with hT_def
  set T1 := convexHull ℝ ({P, Q, D} : Set E) with hT1_def
  set T2 := convexHull ℝ ({P, Q', D} : Set E) with hT2_def
  have hmemP : P ∈ T := subset_convexHull ℝ _ (by simp)
  have hmemQ : Q ∈ T := subset_convexHull ℝ _ (by simp)
  have hmemR : R ∈ T := subset_convexHull ℝ _ (by simp)
  have hQRin : Q ∈ ({P, Q, R} : Set E) ∧ R ∈ ({P, Q, R} : Set E) := ⟨by simp, by simp⟩
  have hPRin : P ∈ ({P, Q, R} : Set E) ∧ R ∈ ({P, Q, R} : Set E) := ⟨by simp, by simp⟩
  have hmemD : D ∈ T := segment_subset_convexHull hQRin.1 hQRin.2 hDseg
  have hmemQ' : Q' ∈ T := segment_subset_convexHull hPRin.1 hPRin.2 hQ'seg
  have hT1T : T1 ⊆ T := by
    apply convexHull_min _ (convex_convexHull ℝ _)
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h
    · rw [h]; exact hmemP
    · rw [h]; exact hmemQ
    · rw [h]; exact hmemD
  have hT2T : T2 ⊆ T := by
    apply convexHull_min _ (convex_convexHull ℝ _)
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h
    · rw [h]; exact hmemP
    · rw [h]; exact hmemQ'
    · rw [h]; exact hmemD
  have hT12σ : T2 = reflectionInLine P w '' T1 := by
    rw [hT1_def, hT2_def, reflectionInLine_image_convexHull]
    congr 1
    simp only [Set.image_insert_eq, Set.image_singleton, hσP, hσQ, hσD]
  have hσT2 : reflectionInLine P w '' T2 = T1 := by
    rw [hT12σ, Set.image_image,
      show (fun x ↦ reflectionInLine P w (reflectionInLine P w x)) = id from
        (reflectionInLine_involutive P w).comp_self, Set.image_id]
  have hσU : reflectionInLine P w '' (T1 ∪ T2) = T1 ∪ T2 := by
    rw [Set.image_union, hσT2, hT12σ, Set.union_comm]
  have hUT : T1 ∪ T2 ⊆ T := Set.union_subset hT1T hT2T
  have hsub : interior (T1 ∪ T2) ⊆
      interior T ∩ interior (convexHull ℝ (reflectionInLine P w '' ({P, Q, R} : Set E))) := by
    refine Set.subset_inter ?_ ?_
    · exact interior_mono hUT
    · apply interior_mono
      have h1 : T1 ∪ T2 ⊆ reflectionInLine P w '' T := by
        rw [← hσU]
        exact Set.image_mono hUT
      rw [hT_def, reflectionInLine_image_convexHull] at h1
      exact h1
  -- Measurability.
  have hfinT : ({P, Q, R} : Set E).Finite := (Set.finite_singleton R).insert Q |>.insert P
  have hfinT1 : ({P, Q, D} : Set E).Finite := (Set.finite_singleton D).insert Q |>.insert P
  have hfinT2 : ({P, Q', D} : Set E).Finite := (Set.finite_singleton D).insert Q' |>.insert P
  have hT1m : MeasurableSet T1 := finite_convexHull_meas hfinT1
  have hT2m : MeasurableSet T2 := finite_convexHull_meas hfinT2
  have hTm : MeasurableSet T := finite_convexHull_meas hfinT
  have hTcomp : IsCompact T := hfinT.isCompact_convexHull ℝ
  -- The separating hyperplane (the line through `P` with direction `w`).
  set z := u - v with hz_def
  have hz : z ≠ 0 := sub_ne_zero.mpr huv_ne
  have hs_abs : |⟪u, v⟫_ℝ| ≤ 1 := by
    have h : ‖⟪u, v⟫_ℝ‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v
    rw [hu1, hv1, mul_one, Real.norm_eq_abs] at h
    exact h
  have hs_lt1 : ⟪u, v⟫_ℝ < 1 := by
    have hle : ⟪u, v⟫_ℝ ≤ 1 := le_trans (le_abs_self _) hs_abs
    refine lt_of_le_of_ne hle ?_
    intro h1
    apply huv_ne
    have hz2 : (‖u - v‖ : ℝ) ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right,
        real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hu1, hv1, real_inner_comm u v, h1]
      norm_num
    rw [pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0), norm_eq_zero, sub_eq_zero] at hz2
    exact hz2
  have hN0 : volume {x : E | ⟪z, x - P⟫_ℝ = 0} = 0 := volume_side_zero hz
  have hNm : MeasurableSet {x : E | ⟪z, x - P⟫_ℝ = 0} := by
    have hcont : Continuous (fun x : E ↦ ⟪z, x - P⟫_ℝ) :=
      Continuous.inner continuous_const (continuous_id.sub continuous_const)
    exact (isClosed_singleton.preimage hcont).measurableSet
  have hside_conv : Convex ℝ {x : E | 0 ≤ ⟪z, x - P⟫_ℝ} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    have e : ⟪z, a • x + b • y - P⟫_ℝ = a * ⟪z, x - P⟫_ℝ + b * ⟪z, y - P⟫_ℝ := by
      rw [inner_sub_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
        inner_sub_right, inner_sub_right]
      have hP : (a + b) * ⟪z, P⟫_ℝ = ⟪z, P⟫_ℝ := by rw [hab, one_mul]
      have e2 : a * (⟪z, x⟫_ℝ - ⟪z, P⟫_ℝ) + b * (⟪z, y⟫_ℝ - ⟪z, P⟫_ℝ) =
          a * ⟪z, x⟫_ℝ + b * ⟪z, y⟫_ℝ - (a + b) * ⟪z, P⟫_ℝ := by ring
      rw [e2, hP]
    rw [e]
    exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
  have hT1side : T1 ⊆ {x : E | 0 ≤ ⟪z, x - P⟫_ℝ} := by
    apply convexHull_min _ hside_conv
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq] at hx ⊢
    rcases hx with h | h | h
    · rw [h]; simp
    · rw [h]
      have e : ⟪z, Q - P⟫_ℝ = c * (1 - ⟪u, v⟫_ℝ) := by
        rw [hz_def, hv1u, real_inner_smul_right, inner_sub_left, real_inner_self_eq_norm_sq, hu1,
          real_inner_comm u v]
        ring
      rw [e]
      exact mul_nonneg hc.le (sub_nonneg.mpr hs_lt1.le)
    · rw [h]
      have e : ⟪z, D - P⟫_ℝ = 0 := by
        rw [hDP, hz_def, hw_def, real_inner_smul_right, inner_sub_left, inner_add_right,
          inner_add_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hu1, hv1,
          real_inner_comm u v]
        ring
      exact e.ge
  have hT2side : T2 ⊆ {x : E | ⟪z, x - P⟫_ℝ ≤ 0} := by
    have hconv : Convex ℝ {x : E | ⟪z, x - P⟫_ℝ ≤ 0} := by
      intro x hx y hy a b ha hb hab
      simp only [Set.mem_setOf_eq] at hx hy ⊢
      have e : ⟪z, a • x + b • y - P⟫_ℝ = a * ⟪z, x - P⟫_ℝ + b * ⟪z, y - P⟫_ℝ := by
        rw [inner_sub_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
          inner_sub_right, inner_sub_right]
        have hP : (a + b) * ⟪z, P⟫_ℝ = ⟪z, P⟫_ℝ := by rw [hab, one_mul]
        have e2 : a * (⟪z, x⟫_ℝ - ⟪z, P⟫_ℝ) + b * (⟪z, y⟫_ℝ - ⟪z, P⟫_ℝ) =
            a * ⟪z, x⟫_ℝ + b * ⟪z, y⟫_ℝ - (a + b) * ⟪z, P⟫_ℝ := by ring
        rw [e2, hP]
      rw [e]
      exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hx)
        (mul_nonpos_of_nonneg_of_nonpos hb hy)
    apply convexHull_min _ hconv
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq] at hx ⊢
    rcases hx with h | h | h
    · rw [h]; simp
    · rw [h]
      have e : ⟪z, Q' - P⟫_ℝ = c * (⟪u, v⟫_ℝ - 1) := by
        rw [hQ'_def, add_sub_cancel_left, hz_def, hv2v, real_inner_smul_right,
          real_inner_smul_right, inner_sub_left, real_inner_self_eq_norm_sq, hv1]
        field_simp [hb.ne']
      rw [e]
      exact mul_nonpos_of_nonneg_of_nonpos hc.le (sub_nonpos.mpr hs_lt1.le)
    · rw [h]
      have e : ⟪z, D - P⟫_ℝ = 0 := by
        rw [hDP, hz_def, hw_def, real_inner_smul_right, inner_sub_left, inner_add_right,
          inner_add_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hu1, hv1,
          real_inner_comm u v]
        ring
      exact e.le
  have hcap : T1 ∩ T2 ⊆ {x : E | ⟪z, x - P⟫_ℝ = 0} := by
    intro x hx
    have h1 := hT1side hx.1
    have h2 := hT2side hx.2
    exact le_antisymm h2 h1
  -- Volumes of the two halves.
  have hμU : volume (T1 ∪ T2) = volume T1 + volume T2 := by
    have hd : Disjoint (T1 \ {x : E | ⟪z, x - P⟫_ℝ = 0}) (T2 \ {x : E | ⟪z, x - P⟫_ℝ = 0}) := by
      rw [Set.disjoint_left]
      rintro x ⟨hx1, hxn⟩ ⟨hx2, -⟩
      exact hxn (hcap ⟨hx1, hx2⟩)
    calc volume (T1 ∪ T2) = volume ((T1 ∪ T2) \ {x : E | ⟪z, x - P⟫_ℝ = 0}) :=
          (measure_sdiff_null hN0).symm
      _ = volume ((T1 \ {x : E | ⟪z, x - P⟫_ℝ = 0}) ∪ (T2 \ {x : E | ⟪z, x - P⟫_ℝ = 0})) := by
          rw [Set.union_sdiff_distrib]
      _ = volume (T1 \ {x : E | ⟪z, x - P⟫_ℝ = 0}) + volume (T2 \ {x : E | ⟪z, x - P⟫_ℝ = 0}) :=
          measure_union hd (hT2m.diff hNm)
      _ = volume T1 + volume T2 := by rw [measure_sdiff_null hN0, measure_sdiff_null hN0]
  have hμT2 : volume T2 = volume T1 := by
    rw [hT12σ, volume_reflectionInLine_image P w hT1m]
  -- The ratio of areas `vol T1 = τ · vol T` via a determinant computation.
  have hcard : Fintype.card (Fin 2) = Module.finrank ℝ E := by
    rw [Fintype.card_fin, finrank_euclideanSpace, Fintype.card_fin]
  set bsis : Module.Basis (Fin 2) ℝ E := basisOfLinearIndependentOfCardEqFinrank' ![Q - P, R - P] hLI hcard
  have hcoe : ⇑bsis = ![Q - P, R - P] := coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _
  have hb0 : bsis 0 = Q - P := by rw [hcoe]; simp
  have hb1 : bsis 1 = R - P := by rw [hcoe]; simp
  set L : E →ₗ[ℝ] E := bsis.constr ℝ ![Q - P, (1 - τ) • (Q - P) + τ • (R - P)] with hL_def
  have hL1 : L (Q - P) = Q - P := by
    rw [← hb0, hL_def, Module.Basis.constr_basis]
    simp only [Matrix.cons_val_zero, hb0]
  have hL2 : L (R - P) = (1 - τ) • (Q - P) + τ • (R - P) := by
    rw [← hb1, hL_def, Module.Basis.constr_basis]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, hb1]
  have hdet : LinearMap.det L = τ := by
    have e0 : bsis.repr (Q - P) = Finsupp.single 0 1 := by rw [← hb0]; exact bsis.repr_self 0
    have e1 : bsis.repr (R - P) = Finsupp.single 1 1 := by rw [← hb1]; exact bsis.repr_self 1
    have e2 : bsis.repr ((1 - τ) • (Q - P) + τ • (R - P)) =
        (1 - τ) • Finsupp.single 0 1 + τ • Finsupp.single 1 1 := by
      rw [map_add, map_smul, map_smul, e0, e1]
    have e00 : (LinearMap.toMatrix bsis bsis L) 0 0 = 1 := by
      rw [LinearMap.toMatrix_apply, hb0, hL1, e0]
      simp [Finsupp.single_eq_same]
    have e10 : (LinearMap.toMatrix bsis bsis L) 1 0 = 0 := by
      rw [LinearMap.toMatrix_apply, hb0, hL1, e0]
      simp [Finsupp.single_eq_of_ne]
    have e01 : (LinearMap.toMatrix bsis bsis L) 0 1 = 1 - τ := by
      rw [LinearMap.toMatrix_apply, hb1, hL2, e2]
      simp [Finsupp.single_eq_of_ne]
    have e11 : (LinearMap.toMatrix bsis bsis L) 1 1 = τ := by
      rw [LinearMap.toMatrix_apply, hb1, hL2, e2]
      simp [Finsupp.single_eq_same, Finsupp.single_eq_of_ne]
    rw [← LinearMap.det_toMatrix bsis L, Matrix.det_fin_two, e00, e01, e10, e11]
    ring
  have hconvL : T1 = (fun x ↦ L (x - P) + P) '' T := by
    let g : E →ᵃ[ℝ] E := AffineMap.mk' (fun x ↦ L (x - P) + P) L P
      (fun p' ↦ by simp [map_sub])
    have hgeq : ⇑g = fun x ↦ L (x - P) + P := AffineMap.coe_mk' _ _ _ _
    rw [hT_def, hT1_def, ← hgeq, AffineMap.image_convexHull]
    congr 1
    have hgP : g P = P := by rw [hgeq]; simp
    have hgQ : g Q = Q := by
      rw [hgeq]
      show L (Q - P) + P = Q
      rw [hL1]
      exact sub_add_cancel Q P
    have hgR : g R = D := by
      rw [hgeq]
      show L (R - P) + P = D
      rw [hL2, hD_def]
      module
    simp only [Set.image_insert_eq, Set.image_singleton, hgP, hgQ, hgR]
  have hvol1 : volume ((fun x ↦ x - P) '' T) = volume T := by
    rw [show (fun x : E ↦ x - P) = (fun x ↦ x + (-P)) from funext fun x ↦ sub_eq_add_neg x P]
    exact volume_add_const_image T hTm (-P)
  have hvolL : volume ((fun x ↦ L (x - P) + P) '' T) = ENNReal.ofReal τ * volume T := by
    have hmeas2 : MeasurableSet (L '' ((fun x ↦ x - P) '' T)) :=
      ((hTcomp.image (continuous_id.sub continuous_const)).image
        (LinearMap.continuous_of_finiteDimensional L)).isClosed.measurableSet
    have e : (fun x ↦ L (x - P) + P) '' T =
        (fun x ↦ x + P) '' (L '' ((fun x ↦ x - P) '' T)) := by
      have e1 : (fun x ↦ L (x - P) + P) = (fun x ↦ x + P) ∘ L ∘ (fun x ↦ x - P) := rfl
      rw [e1, Set.image_comp, Set.image_comp]
    calc volume ((fun x ↦ L (x - P) + P) '' T)
        = volume ((fun x ↦ x + P) '' (L '' ((fun x ↦ x - P) '' T))) := by rw [e]
      _ = volume (L '' ((fun x ↦ x - P) '' T)) := volume_add_const_image _ hmeas2 P
      _ = ENNReal.ofReal |LinearMap.det L| * volume ((fun x ↦ x - P) '' T) :=
          MeasureTheory.Measure.addHaar_image_linearMap volume L _
      _ = ENNReal.ofReal τ * volume T := by rw [hdet, abs_of_pos hτ0, hvol1]
  have hratio : volume T1 = ENNReal.ofReal τ * volume T := by rw [hconvL, hvolL]
  -- Interior volumes.
  have hvolIntT : volume (interior T) = volume T := volume_interior_convexHull hfinT
  have hvolIntT1 : volume (interior T1) = volume T1 := volume_interior_convexHull hfinT1
  have hvolIntT2 : volume (interior T2) = volume T2 := volume_interior_convexHull hfinT2
  have hIntT : (interior T).Nonempty := by
    rw [hT_def, interior_convexHull_nonempty_iff_affineSpan_eq_top]
    have hAI : AffineIndependent ℝ ![P, Q, R] := affineIndependent_iff_not_collinear_set.mpr hnc
    have h1 : affineSpan ℝ (Set.range ![P, Q, R]) = ⊤ :=
      (hAI.affineSpan_eq_top_iff_card_eq_finrank_add_one).mpr (by
        rw [Fintype.card_fin, finrank_euclideanSpace, Fintype.card_fin])
    rwa [show Set.range ![P, Q, R] = ({P, Q, R} : Set E) from by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i <;> simp
      · intro hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl
        · exact ⟨0, by simp⟩
        · exact ⟨1, by simp⟩
        · exact ⟨2, by simp⟩] at h1
  have hTpos : 0 < volume T := by
    have h1 : (0 : ℝ≥0∞) < volume (interior T) :=
      IsOpen.measure_pos volume isOpen_interior hIntT
    exact lt_of_lt_of_le h1 (measure_mono interior_subset)
  have hTfin : volume T ≠ ∞ := (hTcomp.measure_lt_top).ne
  have hINT : volume T1 + volume T2 ≤ volume (interior (T1 ∪ T2)) := by
    have hsub2 : interior T1 ∪ interior T2 ⊆ interior (T1 ∪ T2) :=
      Set.union_subset (interior_mono Set.subset_union_left) (interior_mono Set.subset_union_right)
    have hcap0 : volume (interior T1 ∩ interior T2) = 0 :=
      measure_mono_null ((Set.inter_subset_inter interior_subset interior_subset).trans hcap) hN0
    have e1 : volume (interior T1 ∪ interior T2) = volume (interior T1) + volume (interior T2) := by
      have h : volume (interior T1 ∪ interior T2) + volume (interior T1 ∩ interior T2) =
          volume (interior T1) + volume (interior T2) :=
        measure_union_add_inter (interior T1) (isOpen_interior (s := T2)).measurableSet
      rw [hcap0, add_zero] at h
      exact h
    calc volume T1 + volume T2 = volume (interior T1) + volume (interior T2) := by
          rw [hvolIntT1, hvolIntT2]
      _ = volume (interior T1 ∪ interior T2) := e1.symm
      _ ≤ volume (interior (T1 ∪ T2)) := measure_mono hsub2
  -- The key strict inequality `b < 2c`: the longest side is less than twice the middle one.
  have hb2c : b < 2 * c := by
    have hnsr : ¬ SameRay ℝ (R - Q) (Q - P) := by
      intro hsr
      obtain ⟨t, ht0, htsm⟩ := hsr.exists_nonneg_left (sub_ne_zero.mpr hQRne.symm)
      apply hnc
      rw [collinear_iff_exists_forall_eq_smul_vadd]
      refine ⟨Q, R - Q, fun p hp ↦ ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with h | h | h
      · refine ⟨-t, ?_⟩
        rw [h]
        simp only [vadd_eq_add, neg_smul]
        rw [htsm, neg_sub]
        exact (sub_add_cancel P Q).symm
      · refine ⟨0, ?_⟩
        rw [h]
        simp
      · refine ⟨1, ?_⟩
        rw [h]
        simp
    have h1 : ‖(R - Q) + (Q - P)‖ < ‖R - Q‖ + ‖Q - P‖ := norm_add_lt_of_not_sameRay hnsr
    rw [sub_add_sub_cancel, ← hb_def, ← hc_def] at h1
    linarith [ha]
  -- Final assembly.
  refine ⟨w, hw, ?_⟩
  have hr : (2 : ℝ) / 3 < 2 * c / (b + c) := by
    rw [div_lt_div_iff₀ (by norm_num) hbc]
    linarith [hb2c]
  have h23 : (2 / 3 : ℝ≥0∞) = ENNReal.ofReal (2 / 3 : ℝ) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_ofNat]
  have hr2 : (2 / 3 : ℝ≥0∞) < ENNReal.ofReal (2 * c / (b + c)) := by
    rw [h23]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity : (0 : ℝ) < 2 * c / (b + c))).mpr hr
  calc (2 / 3 : ℝ≥0∞) * volume (interior T)
      = (2 / 3 : ℝ≥0∞) * volume T := by rw [hvolIntT]
    _ < ENNReal.ofReal (2 * c / (b + c)) * volume T := by
        rw [mul_comm ((2 : ℝ≥0∞) / 3) (volume T),
          mul_comm (ENNReal.ofReal (2 * c / (b + c))) (volume T)]
        exact ENNReal.mul_lt_mul_right hTpos.ne' hTfin hr2
    _ = 2 * (ENNReal.ofReal τ * volume T) := by
        have e : (2 : ℝ) * c / (b + c) = 2 * τ := by rw [hτ_def]; ring
        rw [e, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat, mul_assoc]
    _ = 2 * volume T1 := by rw [← hratio]
    _ = volume T1 + volume T1 := two_mul _
    _ = volume T1 + volume T2 := by rw [hμT2]
    _ ≤ volume (interior (T1 ∪ T2)) := hINT
    _ ≤ volume (interior T ∩ interior (convexHull ℝ (reflectionInLine P w '' {P, Q, R}))) :=
        measure_mono hsub

snip end

problem usa1996_p3 (A B C : E) (hABC : ¬ Collinear ℝ {A, B, C}) :
    ∃ P w : E, w ≠ 0 ∧
      (2 / 3 : ℝ≥0∞) * volume (interior (convexHull ℝ {A, B, C})) <
        volume (interior (convexHull ℝ {A, B, C}) ∩
          interior (convexHull ℝ (reflectionInLine P w '' {A, B, C}))) := by
  obtain ⟨P, Q, R, hset, hQR, hPQ⟩ := pick_vertex A B C
  have hnc : ¬ Collinear ℝ {P, Q, R} := by rwa [hset]
  obtain ⟨w, hw, hmain⟩ := reflection_overlap P Q R hnc hQR hPQ
  refine ⟨P, w, hw, ?_⟩
  rw [← hset]
  exact hmain

end Usa1996P3
