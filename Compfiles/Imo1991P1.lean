/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Incenter
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry, .Inequality] }

/-!
# International Mathematical Olympiad 1991, Problem 1

Given a triangle ABC, let I be the incenter. The internal bisectors of angles
A, B, C meet the opposite sides in A′, B′, C′ respectively. Prove that

    1/4 < (AI · BI · CI) / (AA′ · BB′ · CC′) ≤ 8/27.
-/

namespace Imo1991P1

/-- The Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

noncomputable section

snip begin

/-!
The incenter `I` of a triangle is the affine combination of the vertices with
weights `w₀, w₁, w₂` (the `excenterWeights ∅` of Mathlib), which are positive,
sum to one and are each less than `1/2`.  The bisector from a vertex is the
line through that vertex and `I`; if it meets the line through the other two
vertices in `X`, then `I` divides the segment in the ratio
`dist Pᵢ I = (1 - wᵢ) * dist Pᵢ X`.  This is pure affine geometry:
`I -ᵥ Pᵢ = ∑ m, w m • (P m -ᵥ Pᵢ)`, while `X -ᵥ Pᵢ` is a scalar multiple of it
whose coefficient is forced by `X` lying in the span of the other two vertices
(and the affine independence of the vertices).  The problem therefore reduces
to the elementary inequality `1/4 < (1 - w₀)(1 - w₁)(1 - w₂) ≤ 8/27`.
-/

section

variable (t : Affine.Triangle ℝ Plane)

/-- The incenter weights sum to one. -/
lemma weight_sum : ∑ i, t.excenterWeights ∅ i = 1 :=
  t.excenterExists_empty.sum_excenterWeights_eq_one

/-- The incenter weights are positive. -/
lemma weight_pos (i : Fin 3) : 0 < t.excenterWeights ∅ i :=
  t.excenterWeights_empty_pos i

/-- The incenter weights are less than `1/2`. -/
lemma weight_lt (i : Fin 3) : t.excenterWeights ∅ i < 1 / 2 := by
  simpa using t.excenterWeights_empty_lt_inv_two i

/-- The line through two vertices `j, k` of a triangle does not contain the
third vertex `i`; hence any point `X` on it is at positive distance from `i`. -/
lemma dist_vertex_pos_of_mem_line (i j k : Fin 3) (hij : j ≠ i) (hik : k ≠ i) {X : Plane}
    (hX : X ∈ line[ℝ, t.points j, t.points k]) :
    0 < dist (t.points i) X := by
  have hnot : t.points i ∉ line[ℝ, t.points j, t.points k] := by
    have hle : (line[ℝ, t.points j, t.points k] : AffineSubspace ℝ Plane) ≤
        affineSpan ℝ (t.points '' (Set.univ \ {i})) := by
      rw [affineSpan_le]
      rintro q (rfl | rfl)
      · exact mem_affineSpan ℝ ⟨j, by simp [hij], rfl⟩
      · exact mem_affineSpan ℝ ⟨k, by simp [hik], rfl⟩
    exact fun h ↦ t.independent.notMem_affineSpan_sdiff i Set.univ (hle h)
  rw [dist_pos]
  exact fun h ↦ hnot (h.symm ▸ hX)

/-- If the line through vertex `i` and the incenter meets the line through the
other two vertices in `X`, the incenter divides the cevian in the ratio given
by the incenter weights. -/
lemma dist_incenter_eq (i j k : Fin 3) (hij : j ≠ i) (hik : k ≠ i) {X : Plane}
    (hX₁ : X ∈ line[ℝ, t.points i, t.incenter])
    (hX₂ : X ∈ line[ℝ, t.points j, t.points k]) :
    dist (t.points i) t.incenter = (1 - t.excenterWeights ∅ i) * dist (t.points i) X := by
  -- Since `X` lies on the line through `Pᵢ` and `I`, `X -ᵥ Pᵢ` is a scalar
  -- multiple of `I -ᵥ Pᵢ`.
  have hPi : t.points i ∈ (line[ℝ, t.points i, t.incenter] : AffineSubspace ℝ Plane) :=
    mem_affineSpan ℝ (Set.mem_insert _ _)
  have hvsub : X -ᵥ t.points i ∈ vectorSpan ℝ {t.points i, t.incenter} :=
    vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan hX₁ hPi
  rw [vectorSpan_pair_rev] at hvsub
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hvsub
  -- The incenter is the weighted average of the vertices.
  have hsum := weight_sum t
  have hIw : t.incenter =
      Finset.univ.weightedVSubOfPoint t.points (t.points i) (t.excenterWeights ∅) +ᵥ
        t.points i := by
    rw [t.incenter_eq_affineCombination,
      Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _ hsum (t.points i)]
  have hIv : t.incenter -ᵥ t.points i =
      ∑ m, t.excenterWeights ∅ m • (t.points m -ᵥ t.points i) := by
    rw [hIw, vadd_vsub, Finset.weightedVSubOfPoint_apply]
  have haX : X -ᵥ t.points i =
      ∑ m, (a * t.excenterWeights ∅ m) • (t.points m -ᵥ t.points i) := by
    rw [← ha, hIv, Finset.smul_sum]
    exact Finset.sum_congr rfl fun m _ ↦ by rw [mul_smul]
  -- The scalar `a` is determined by `X` lying in the span of the other two
  -- vertices: write `X` as an affine combination of the vertices and use the
  -- uniqueness of barycentric coordinates.
  have hsumv' : (∑ m, (a * t.excenterWeights ∅ m + if m = i then 1 - a else 0)) = 1 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, mul_one, Finset.sum_ite_eq',
      if_pos (Finset.mem_univ i), add_sub_cancel]
  have hXcomb : X = Finset.univ.affineCombination ℝ t.points
      (fun m ↦ a * t.excenterWeights ∅ m + if m = i then 1 - a else 0) := by
    have h3 : (∑ m, ((a * t.excenterWeights ∅ m + if m = i then 1 - a else 0) •
        (t.points m -ᵥ t.points i))) = X -ᵥ t.points i := by
      rw [haX]
      apply Finset.sum_congr rfl
      intro m _
      by_cases hm : m = i
      · subst hm; rw [if_pos rfl, vsub_self, smul_zero, smul_zero]
      · rw [if_neg hm, add_zero]
    rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _ hsumv'
        (t.points i),
      Finset.weightedVSubOfPoint_apply]
    show X = (∑ m, ((a * t.excenterWeights ∅ m + if m = i then 1 - a else 0) •
        (t.points m -ᵥ t.points i))) +ᵥ t.points i
    rw [h3, vsub_vadd]
  have himg : t.points '' ({j, k} : Set (Fin 3)) = ({t.points j, t.points k} : Set Plane) := by
    simp [Set.image_insert_eq, Set.image_singleton]
  have hXspan : Finset.univ.affineCombination ℝ t.points
        (fun m ↦ a * t.excenterWeights ∅ m + if m = i then 1 - a else 0) ∈
      affineSpan ℝ (t.points '' ({j, k} : Set (Fin 3))) := by
    rw [← hXcomb, himg]
    exact hX₂
  have his : i ∉ ({j, k} : Set (Fin 3)) := by simp [hij.symm, hik.symm]
  have hzero := t.independent.eq_zero_of_affineCombination_mem_affineSpan hsumv' hXspan
    (Finset.mem_univ i) his
  beta_reduce at hzero
  rw [if_pos rfl] at hzero
  -- `hzero : a * w i + (1 - a) = 0`
  have h2 : a * (1 - t.excenterWeights ∅ i) = 1 := by linarith [hzero]
  have hw1 : 0 < 1 - t.excenterWeights ∅ i := by have h := weight_lt t i; linarith
  have hapos : 0 < a := by
    by_contra hle
    have hle' : a ≤ 0 := le_of_not_gt hle
    have h3 : a * (1 - t.excenterWeights ∅ i) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hle' (le_of_lt hw1)
    linarith
  have hd : dist (t.points i) X = a * dist (t.points i) t.incenter := by
    rw [dist_eq_norm_vsub', ← ha, norm_smul, Real.norm_eq_abs, abs_of_pos hapos,
      dist_eq_norm_vsub']
  calc dist (t.points i) t.incenter
      = (a * (1 - t.excenterWeights ∅ i)) * dist (t.points i) t.incenter := by rw [h2, one_mul]
    _ = (1 - t.excenterWeights ∅ i) * (a * dist (t.points i) t.incenter) := by ring
    _ = (1 - t.excenterWeights ∅ i) * dist (t.points i) X := by rw [← hd]

/-- The elementary inequality behind the problem: for `x, y, z ∈ (0, 1/2)` with
`x + y + z = 1` one has `1/4 < (1-x)(1-y)(1-z) ≤ 8/27`.  The lower bound follows
by expanding around `1/2`; the upper bound is AM-GM. -/
lemma weight_ineq {x y z : ℝ} (hx : 0 < x) (_hy : 0 < y) (_hz : 0 < z)
    (hx2 : x < 1 / 2) (hy2 : y < 1 / 2) (hz2 : z < 1 / 2) (hsum : x + y + z = 1) :
    1 / 4 < (1 - x) * (1 - y) * (1 - z) ∧ (1 - x) * (1 - y) * (1 - z) ≤ 8 / 27 := by
  have hu : 0 < 1 / 2 - x := by linarith
  have hv : 0 < 1 / 2 - y := by linarith
  have hw : 0 < 1 / 2 - z := by linarith
  have huvw : (1 / 2 - x) + (1 / 2 - y) + (1 / 2 - z) = 1 / 2 := by linarith
  have hexp : (1 - x) * (1 - y) * (1 - z) =
      1 / 8 + ((1 / 2 - x) + (1 / 2 - y) + (1 / 2 - z)) / 4 +
        ((1 / 2 - x) * (1 / 2 - y) + (1 / 2 - y) * (1 / 2 - z) +
          (1 / 2 - z) * (1 / 2 - x)) / 2 +
        (1 / 2 - x) * (1 / 2 - y) * (1 / 2 - z) := by ring
  have h1 : 0 < (1 / 2 - x) * (1 / 2 - y) := mul_pos hu hv
  have h2 : 0 < (1 / 2 - y) * (1 / 2 - z) := mul_pos hv hw
  have h3 : 0 < (1 / 2 - z) * (1 / 2 - x) := mul_pos hw hu
  have h4 : 0 < (1 / 2 - x) * (1 / 2 - y) * (1 / 2 - z) := mul_pos h1 hw
  constructor
  · rw [hexp, huvw]; linarith
  · have e1 : (0 : ℝ) ≤ 1 - x := by linarith
    have e2 : (0 : ℝ) ≤ 1 - y := by linarith
    have e3 : (0 : ℝ) ≤ 1 - z := by linarith
    have amgm := Real.geom_mean_le_arith_mean3_weighted
      (show (0 : ℝ) ≤ 1 / 3 by norm_num) (show (0 : ℝ) ≤ 1 / 3 by norm_num)
      (show (0 : ℝ) ≤ 1 / 3 by norm_num) e1 e2 e3 (by norm_num)
    have hS' : (1 : ℝ) / 3 * (1 - x) + 1 / 3 * (1 - y) + 1 / 3 * (1 - z) = 2 / 3 := by linarith
    rw [hS'] at amgm
    have hmul : (1 - x) ^ ((1 : ℝ) / 3) * (1 - y) ^ ((1 : ℝ) / 3) * (1 - z) ^ ((1 : ℝ) / 3) =
        ((1 - x) * (1 - y) * (1 - z)) ^ ((1 : ℝ) / 3) := by
      rw [← Real.mul_rpow e1 e2, ← Real.mul_rpow (mul_nonneg e1 e2) e3]
    rw [hmul] at amgm
    have hcube : (1 - x) * (1 - y) * (1 - z) =
        (((1 - x) * (1 - y) * (1 - z)) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) := by
      have h5 : ((3 : ℕ) : ℝ) = 3 := by norm_num
      rw [← Real.rpow_natCast, h5, ← Real.rpow_mul (by positivity),
        show (1 : ℝ) / 3 * 3 = 1 by norm_num, Real.rpow_one]
    rw [hcube]
    have hnn : 0 ≤ ((1 - x) * (1 - y) * (1 - z)) ^ ((1 : ℝ) / 3) :=
      Real.rpow_nonneg (by positivity) _
    calc (((1 - x) * (1 - y) * (1 - z)) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ)
        ≤ (2 / 3) ^ (3 : ℕ) := pow_le_pow_left₀ hnn amgm 3
      _ = 8 / 27 := by norm_num

end

snip end

problem imo1991_p1 (t : Affine.Triangle ℝ Plane)
    (A' B' C' : Plane)
    (hA'₁ : A' ∈ line[ℝ, t.points 0, t.incenter]) (hA'₂ : A' ∈ line[ℝ, t.points 1, t.points 2])
    (hB'₁ : B' ∈ line[ℝ, t.points 1, t.incenter]) (hB'₂ : B' ∈ line[ℝ, t.points 2, t.points 0])
    (hC'₁ : C' ∈ line[ℝ, t.points 2, t.incenter]) (hC'₂ : C' ∈ line[ℝ, t.points 0, t.points 1]) :
    1 / 4 < dist (t.points 0) t.incenter * dist (t.points 1) t.incenter *
        dist (t.points 2) t.incenter /
      (dist (t.points 0) A' * dist (t.points 1) B' * dist (t.points 2) C') ∧
    dist (t.points 0) t.incenter * dist (t.points 1) t.incenter *
        dist (t.points 2) t.incenter /
      (dist (t.points 0) A' * dist (t.points 1) B' * dist (t.points 2) C') ≤ 8 / 27 := by
  have hA := dist_incenter_eq t 0 1 2 (by decide) (by decide) hA'₁ hA'₂
  have hB := dist_incenter_eq t 1 2 0 (by decide) (by decide) hB'₁ hB'₂
  have hC := dist_incenter_eq t 2 0 1 (by decide) (by decide) hC'₁ hC'₂
  have hdA := dist_vertex_pos_of_mem_line t 0 1 2 (by decide) (by decide) hA'₂
  have hdB := dist_vertex_pos_of_mem_line t 1 2 0 (by decide) (by decide) hB'₂
  have hdC := dist_vertex_pos_of_mem_line t 2 0 1 (by decide) (by decide) hC'₂
  have hden : dist (t.points 0) A' * dist (t.points 1) B' * dist (t.points 2) C' ≠ 0 :=
    ne_of_gt (by positivity)
  have hnum : dist (t.points 0) t.incenter * dist (t.points 1) t.incenter *
        dist (t.points 2) t.incenter =
      (1 - t.excenterWeights ∅ 0) * (1 - t.excenterWeights ∅ 1) *
        (1 - t.excenterWeights ∅ 2) *
      (dist (t.points 0) A' * dist (t.points 1) B' * dist (t.points 2) C') := by
    rw [hA, hB, hC]; ring
  have hratio : dist (t.points 0) t.incenter * dist (t.points 1) t.incenter *
        dist (t.points 2) t.incenter /
      (dist (t.points 0) A' * dist (t.points 1) B' * dist (t.points 2) C') =
      (1 - t.excenterWeights ∅ 0) * (1 - t.excenterWeights ∅ 1) *
        (1 - t.excenterWeights ∅ 2) := by
    rw [hnum, mul_div_assoc, div_self hden, mul_one]
  rw [hratio]
  have hsum3 : t.excenterWeights ∅ 0 + t.excenterWeights ∅ 1 + t.excenterWeights ∅ 2 = 1 := by
    have h := weight_sum t
    rwa [Fin.sum_univ_three] at h
  exact weight_ineq (weight_pos t 0) (weight_pos t 1) (weight_pos t 2)
    (weight_lt t 0) (weight_lt t 1) (weight_lt t 2) hsum3

end

end Imo1991P1
