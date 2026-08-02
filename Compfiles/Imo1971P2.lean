/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.OpenPos
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1971, Problem 2

Let P₁ be a convex polyhedron with vertices A₁, A₂, ..., A₉. Let Pᵢ be the
polyhedron obtained from P₁ by a translation that moves A₁ to Aᵢ. Prove that at
least two of the polyhedra P₁, P₂, ..., P₉ have an interior point in common.
-/

namespace Imo1971P2

open MeasureTheory Set
open scoped ENNReal Pointwise Function

/-- The ambient space: Euclidean 3-space, modeled as `ℝ³`. -/
abbrev E := Fin 3 → ℝ

/-- The `i`-th polyhedron: the translate of the convex hull of the vertices
that moves `A 0` to `A i`. -/
def poly (A : Fin 9 → E) (i : Fin 9) : Set E :=
  (fun x => x + (A i - A 0)) '' (convexHull ℝ (Set.range A))

snip begin

/-- Translating a set on the right by `v` is the same as taking the preimage
under left translation by `-v`. -/
lemma image_add_right_eq_preimage (s : Set E) (v : E) :
    (fun x : E => x + v) '' s = ((-v + ·) : E → E) ⁻¹' s := by
  ext y
  simp only [Set.mem_image, Set.mem_preimage]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxy : -v + (x + v) = x := by abel
    rwa [hxy]
  · intro hy
    exact ⟨-v + y, hy, by show -v + y + v = y; abel⟩

/-- The volume of a translate of a measurable set equals the volume of the set. -/
lemma volume_image_add (s : Set E) (hs : MeasurableSet s) (v : E) :
    volume ((fun x : E => x + v) '' s) = volume s := by
  rw [image_add_right_eq_preimage]
  exact Measure.measure_preimage_of_map_eq_self
    (Measure.IsAddLeftInvariant.map_add_left_eq_self (-v)) hs.nullMeasurableSet

/-- A translate of a measurable set is measurable. -/
lemma measurableSet_image_add (s : Set E) (hs : MeasurableSet s) (v : E) :
    MeasurableSet ((fun x : E => x + v) '' s) := by
  rw [image_add_right_eq_preimage]
  exact hs.preimage (measurable_const_add (-v))

/-- The volume of the image of a measurable set under a homothety
`x ↦ r • (x - z) + z` is `|r|³` times the volume of the set. -/
lemma volume_image_homothety (s : Set E) (hs : MeasurableSet s) (z : E) (r : ℝ) :
    volume ((fun x : E => r • (x - z) + z) '' s) =
      ENNReal.ofReal (|r| ^ 3) * volume s := by
  have hcomp : (fun x : E => r • (x - z) + z) =
      (fun y : E => y + z) ∘ (fun w : E => r • w) ∘ (fun x : E => x - z) := by
    funext x
    simp only [Function.comp_apply]
  rw [hcomp, Set.image_comp, Set.image_comp]
  have h1 : volume ((fun x : E => x - z) '' s) = volume s := by
    simpa only [sub_eq_add_neg] using volume_image_add s hs (-z)
  have hm1 : MeasurableSet ((fun x : E => x - z) '' s) := by
    simpa only [sub_eq_add_neg] using measurableSet_image_add s hs (-z)
  have hm2 : MeasurableSet ((fun w : E => r • w) '' ((fun x : E => x - z) '' s)) := by
    rw [Set.image_smul]
    exact hm1.const_smul₀ r
  have h2 : volume ((fun w : E => r • w) '' ((fun x : E => x - z) '' s)) =
      ENNReal.ofReal (|r| ^ 3) * volume s := by
    rw [Set.image_smul, Measure.addHaar_smul]
    simp only [Module.finrank_pi, Fintype.card_fin, abs_pow]
    rw [h1]
  rw [volume_image_add _ hm2 z, h2]

/-- Every translate `poly A i` is contained in the doubling of `P₁` about `A 0`:
for `x ∈ P₁` the midpoint of `x` and `A i` lies in `P₁` by convexity. -/
lemma subset_doubled (A : Fin 9 → E) (i : Fin 9) :
    poly A i ⊆ (fun x : E => (2 : ℝ) • (x - A 0) + A 0) '' (convexHull ℝ (Set.range A)) := by
  rintro y ⟨x, hx, rfl⟩
  have hAi : A i ∈ convexHull ℝ (Set.range A) := subset_convexHull ℝ _ ⟨i, rfl⟩
  have hw : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • A i ∈ convexHull ℝ (Set.range A) :=
    convex_convexHull ℝ _ hx hAi (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)
  refine ⟨(1 / 2 : ℝ) • x + (1 / 2 : ℝ) • A i, hw, ?_⟩
  show (2 : ℝ) • ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • A i - A 0) + A 0 = x + (A i - A 0)
  module

/-- If `z` is an interior point of `P₁`, then `P₁` is contained in the image of
its own interior under any homothety about `z` with ratio `r > 1`, since the
open segment from an interior point to any point of a convex set stays in the
interior. -/
lemma subset_homothety_interior (A : Fin 9 → E) {z : E}
    (hz : z ∈ interior (convexHull ℝ (Set.range A))) {r : ℝ} (hr : 1 < r) :
    convexHull ℝ (Set.range A) ⊆
      (fun x : E => r • (x - z) + z) '' (interior (convexHull ℝ (Set.range A))) := by
  intro x hx
  have hr0 : (0 : ℝ) < r := zero_lt_one.trans hr
  have hri : (0 : ℝ) < r⁻¹ := inv_pos.mpr hr0
  have ha : (0 : ℝ) < 1 - r⁻¹ := by
    rw [sub_pos]
    exact (inv_lt_one₀ hr0).mpr hr
  refine ⟨(1 - r⁻¹ : ℝ) • z + r⁻¹ • x, ?_, ?_⟩
  · exact (convex_convexHull ℝ _).combo_interior_closure_mem_interior hz
      (subset_closure hx) ha hri.le (by ring)
  · show r • (((1 - r⁻¹ : ℝ) • z + r⁻¹ • x) - z) + z = x
    have heq : r • (((1 - r⁻¹ : ℝ) • z + r⁻¹ • x) - z) + z = (r * r⁻¹) • (x - z) + z := by
      module
    rwa [mul_inv_cancel₀ hr0.ne', one_smul, sub_add_cancel] at heq

snip end

problem imo1971_p2 (A : Fin 9 → E)
    (hA : (interior (convexHull ℝ (Set.range A))).Nonempty) :
    ∃ i j : Fin 9, i ≠ j ∧ (interior (poly A i) ∩ interior (poly A j)).Nonempty := by
  -- Basic measure-theoretic facts about P₁.
  have hPcomp : IsCompact (convexHull ℝ (Set.range A)) :=
    (Set.finite_range A).isCompact_convexHull ℝ
  have hPmeas : MeasurableSet (convexHull ℝ (Set.range A)) := hPcomp.isClosed.measurableSet
  obtain ⟨z, hz⟩ := hA
  -- The interior of a translate is the translate of the interior.
  have hinterior : ∀ i : Fin 9, interior (poly A i) =
      (fun x : E => x + (A i - A 0)) '' interior (convexHull ℝ (Set.range A)) := by
    intro i
    have h := (Homeomorph.addRight (A i - A 0)).image_interior (convexHull ℝ (Set.range A))
    simp only [Homeomorph.coe_addRight] at h
    exact h.symm
  -- All translates have the same volume.
  have hvol : ∀ i : Fin 9, volume (interior (poly A i)) =
      volume (interior (convexHull ℝ (Set.range A))) := by
    intro i
    rw [hinterior i]
    exact volume_image_add _ isOpen_interior.measurableSet _
  -- Every translate is contained in the doubling `D` of `P₁` about `A 0`.
  have hsub : ∀ i : Fin 9, interior (poly A i) ⊆
      (fun x : E => (2 : ℝ) • (x - A 0) + A 0) '' (convexHull ℝ (Set.range A)) := by
    intro i
    exact interior_subset.trans (subset_doubled A i)
  -- `vol D = 8 · vol P₁`.
  have hvolD : volume ((fun x : E => (2 : ℝ) • (x - A 0) + A 0) '' (convexHull ℝ (Set.range A))) =
      8 * volume (convexHull ℝ (Set.range A)) := by
    rw [volume_image_homothety _ hPmeas (A 0) 2, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      show (2 : ℝ) ^ 3 = 8 by norm_num, ENNReal.ofReal_ofNat]
  -- `vol P₁ ≤ (33/32)³ · vol (interior P₁)`.
  have hvolP_le : volume (convexHull ℝ (Set.range A)) ≤
      ENNReal.ofReal ((33 / 32 : ℝ) ^ 3) *
        volume (interior (convexHull ℝ (Set.range A))) := by
    calc volume (convexHull ℝ (Set.range A))
        ≤ volume ((fun x : E => (33 / 32 : ℝ) • (x - z) + z) ''
            (interior (convexHull ℝ (Set.range A)))) :=
          measure_mono (subset_homothety_interior A hz (by norm_num))
      _ = ENNReal.ofReal (|(33 / 32 : ℝ)| ^ 3) *
            volume (interior (convexHull ℝ (Set.range A))) :=
          volume_image_homothety _ isOpen_interior.measurableSet z (33 / 32)
      _ = ENNReal.ofReal ((33 / 32 : ℝ) ^ 3) *
            volume (interior (convexHull ℝ (Set.range A))) := by
          rw [abs_of_nonneg (by norm_num)]
  -- Suppose, for contradiction, that the interiors were pairwise disjoint.
  by_contra hcon
  push Not at hcon
  have hdis : Pairwise (Disjoint on fun i : Fin 9 => interior (poly A i)) := by
    intro i j hij
    exact Set.disjoint_iff_inter_eq_empty.mpr (hcon i j hij)
  -- Then `9 · vol (interior P₁) = vol (⋃ Pᵢ°) ≤ vol D ≤ 8 · (33/32)³ · vol (interior P₁)`.
  have hvolU : volume (⋃ i : Fin 9, interior (poly A i)) =
      9 * volume (interior (convexHull ℝ (Set.range A))) := by
    rw [measure_iUnion hdis fun i => isOpen_interior.measurableSet, tsum_fintype _]
    simp only [hvol]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  have hle1 : volume (⋃ i : Fin 9, interior (poly A i)) ≤
      volume ((fun x : E => (2 : ℝ) • (x - A 0) + A 0) '' (convexHull ℝ (Set.range A))) :=
    measure_mono (Set.iUnion_subset hsub)
  have h9le : (9 : ℝ≥0∞) * volume (interior (convexHull ℝ (Set.range A))) ≤
      ENNReal.ofReal (8 * (33 / 32 : ℝ) ^ 3) *
        volume (interior (convexHull ℝ (Set.range A))) := by
    calc (9 : ℝ≥0∞) * volume (interior (convexHull ℝ (Set.range A)))
        = volume (⋃ i : Fin 9, interior (poly A i)) := hvolU.symm
      _ ≤ volume ((fun x : E => (2 : ℝ) • (x - A 0) + A 0) ''
            (convexHull ℝ (Set.range A))) := hle1
      _ = 8 * volume (convexHull ℝ (Set.range A)) := hvolD
      _ ≤ 8 * (ENNReal.ofReal ((33 / 32 : ℝ) ^ 3) *
            volume (interior (convexHull ℝ (Set.range A)))) :=
          mul_le_mul_right hvolP_le 8
      _ = ENNReal.ofReal (8 * (33 / 32 : ℝ) ^ 3) *
            volume (interior (convexHull ℝ (Set.range A))) := by
          rw [← mul_assoc]
          congr 1
          rw [← ENNReal.ofReal_ofNat 8, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
  -- Cancelling the positive finite volume gives `9 ≤ 8·(33/32)³`, which is false.
  have hU0 : volume (interior (convexHull ℝ (Set.range A))) ≠ 0 :=
    (isOpen_interior.measure_pos volume ⟨z, hz⟩).ne'
  have hUT : volume (interior (convexHull ℝ (Set.range A))) ≠ ⊤ :=
    ((measure_mono interior_subset).trans_lt hPcomp.measure_lt_top).ne
  have hupos : 0 < (volume (interior (convexHull ℝ (Set.range A)))).toReal :=
    ENNReal.toReal_pos hU0 hUT
  have hle := (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top (by simp) hUT)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hUT)).mpr h9le
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 8 * (33 / 32 : ℝ) ^ 3)] at hle
  have h9 : (9 : ℝ≥0∞).toReal = 9 := by norm_num
  rw [h9] at hle
  have hc := le_of_mul_le_mul_right hle hupos
  norm_num at hc

end Imo1971P2
