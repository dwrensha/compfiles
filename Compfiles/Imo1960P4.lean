/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.AffineSpace.Midpoint
public import Mathlib.Geometry.Euclidean.Basic
public import Mathlib.Geometry.Euclidean.Projection
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1960, Problem 4

Construct a triangle ABC given the lengths of the altitudes from A and B
and the length of the median from A.

We formalize this construction problem as a characterization of the triples
(ha, hb, ma) for which such a triangle exists: writing `ha` and `hb` for the
lengths of the altitudes from `A` and `B`, and `ma` for the length of the
median from `A`, a (non-degenerate) triangle exists if and only if
`0 < ha`, `0 < hb`, `ha ≤ ma`, `hb ≤ 2 * ma`, and not both boundary cases
`ha = ma` and `hb = 2 * ma` hold at once. The sufficiency direction is the
construction itself; the necessity direction is the usual analysis of the
problem (the foot of the altitude is the closest point of the side line, and
the midpoint of `BC` is at distance `hb / 2` from the line `CA`).
-/

namespace Imo1960P4

open EuclideanGeometry
open scoped RealInnerProductSpace

snip begin

/-- Auxiliary constructor for points of the Euclidean plane with prescribed coordinates. -/
noncomputable def mk (a b : ℝ) : EuclideanSpace ℝ (Fin 2) := (WithLp.equiv 2 _).symm ![a, b]

@[simp] theorem mk_apply (a b : ℝ) (i : Fin 2) : mk a b i = ![a, b] i := rfl

theorem mk_ext {a b c d : ℝ} (h0 : a = c) (h1 : b = d) : mk a b = mk c d := by
  subst h0; subst h1; rfl

/-- Coordinatewise addition of `mk` points. -/
theorem mk_add (a b c d : ℝ) : mk a b + mk c d = mk (a + c) (b + d) := by
  ext i
  fin_cases i <;> rfl

/-- Coordinatewise subtraction of `mk` points. -/
theorem mk_sub (a b c d : ℝ) : mk a b - mk c d = mk (a - c) (b - d) := by
  ext i
  fin_cases i <;> rfl

/-- Coordinatewise scalar multiplication of `mk` points. -/
theorem mk_smul (r a b : ℝ) : r • mk a b = mk (r * a) (r * b) := by
  ext i
  fin_cases i <;> rfl

/-- The norm of a `mk` point. -/
theorem mk_norm (a b : ℝ) : ‖mk a b‖ = Real.sqrt (a^2 + b^2) := by
  simp [EuclideanSpace.norm_eq, Fin.sum_univ_two, mk_apply, Real.norm_eq_abs, sq_abs]

/-- In the Euclidean plane, if a nonzero vector `A -ᵥ M` is orthogonal to both
`B -ᵥ C` and `A -ᵥ C`, then `A`, `B`, `C` are collinear. -/
theorem collinear_of_inner_eq_zero {A B C M : EuclideanSpace ℝ (Fin 2)}
    (hu : A -ᵥ M ≠ 0) (h1 : ⟪A -ᵥ M, B -ᵥ C⟫ = 0) (h2 : ⟪A -ᵥ M, A -ᵥ C⟫ = 0) :
    Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))) := by
  -- In the plane, the vectors orthogonal to a nonzero vector `u` form the line
  -- spanned by the perpendicular vector `(u 1, -(u 0))`.
  have key : ∀ u v : EuclideanSpace ℝ (Fin 2), u ≠ 0 → ⟪u, v⟫ = 0 →
      ∃ t : ℝ, v = t • mk (u 1) (-(u 0)) := by
    intro u v hu0 huv
    have hsum : u 0 * v 0 + u 1 * v 1 = 0 := by
      have h := huv
      simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply,
        RCLike.conj_to_real] at h
      linear_combination h
    by_cases hu1 : u 1 = 0
    · have hu0' : u 0 ≠ 0 := by
        intro h00
        exact hu0 (PiLp.ext (Fin.forall_fin_two.2 ⟨by simpa using h00, by simpa using hu1⟩))
      have hv0 : v 0 = 0 := by
        have hmul : u 0 * v 0 = 0 := by simpa [hu1] using hsum
        rcases mul_eq_zero.mp hmul with h | h
        · exact absurd h hu0'
        · exact h
      refine ⟨-(v 1) / u 0, PiLp.ext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)⟩
      · simp [PiLp.smul_apply, hu1, hv0]
      · simp only [PiLp.smul_apply, mk_apply, Matrix.cons_val_one, Matrix.cons_val_zero,
          smul_eq_mul]
        field_simp
    · refine ⟨v 0 / u 1, PiLp.ext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)⟩
      · simp only [PiLp.smul_apply, mk_apply, Matrix.cons_val_zero, smul_eq_mul]
        field_simp
      · simp only [PiLp.smul_apply, mk_apply, Matrix.cons_val_one, Matrix.cons_val_zero,
          smul_eq_mul]
        field_simp
        linear_combination hsum
  -- `B -ᵥ A` is orthogonal to `A -ᵥ M` as well.
  have hBA : ⟪A -ᵥ M, B -ᵥ A⟫ = 0 := by
    have hsub : (B -ᵥ A : EuclideanSpace ℝ (Fin 2)) = (B -ᵥ C) - (A -ᵥ C) := by
      simp only [vsub_eq_sub]
      abel
    rw [hsub, inner_sub_right, h1, h2, sub_zero]
  obtain ⟨t₁, ht₁⟩ := key (A -ᵥ M) (B -ᵥ A) hu hBA
  obtain ⟨t₂, ht₂⟩ := key (A -ᵥ M) (A -ᵥ C) hu h2
  by_cases ht2 : t₂ = 0
  · -- Then `A = C` and the three points are trivially collinear.
    have hAC : A = C := vsub_eq_zero_iff_eq.mp (by rw [ht₂, ht2, zero_smul])
    subst hAC
    rw [Set.insert_eq_of_mem (show A ∈ ({B, A} : Set (EuclideanSpace ℝ (Fin 2))) by simp)]
    exact collinear_pair ℝ _ _
  · -- `B` lies on the line through `A` and `C`.
    have hB : B ∈ line[ℝ, A, C] := by
      have hCA : (C -ᵥ A : EuclideanSpace ℝ (Fin 2)) =
          -(t₂ • mk ((A -ᵥ M) 1) (-((A -ᵥ M) 0))) := by
        rw [← ht₂, neg_vsub_eq_vsub_rev]
      have hrw : (-(t₁) / t₂ : ℝ) • (-(t₂ • mk ((A -ᵥ M) 1) (-((A -ᵥ M) 0)))) =
          t₁ • mk ((A -ᵥ M) 1) (-((A -ᵥ M) 0)) := by
        rw [smul_neg, smul_smul]
        have hc : -(t₁) / t₂ * t₂ = -(t₁) := by field_simp
        rw [hc, neg_smul, neg_neg]
      have hB_eq : B = AffineMap.lineMap A C (-(t₁) / t₂) := by
        rw [AffineMap.lineMap_apply, eq_vadd_iff_vsub_eq, hCA, hrw, ht₁]
      rw [hB_eq]
      exact AffineMap.lineMap_mem_affineSpan_pair _ _ _
    rw [Set.insert_comm]
    exact (collinear_insert_iff_of_mem_affineSpan hB).2 (collinear_pair ℝ _ _)

/-- Necessity: the altitudes and median of any (non-degenerate) triangle satisfy
the constraints. -/
theorem constraints_of_triangle (ha hb ma : ℝ)
    (h : ∃ A B C : EuclideanSpace ℝ (Fin 2),
        ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))) ∧
        dist A (orthogonalProjection line[ℝ, B, C] A : EuclideanSpace ℝ (Fin 2)) = ha ∧
        dist B (orthogonalProjection line[ℝ, C, A] B : EuclideanSpace ℝ (Fin 2)) = hb ∧
        dist A (midpoint ℝ B C) = ma) :
    0 < ha ∧ 0 < hb ∧ ha ≤ ma ∧ hb ≤ 2 * ma ∧ (ha < ma ∨ hb < 2 * ma) := by
  obtain ⟨A, B, C, hcoll, hha, hhb, hma⟩ := h
  -- Memberships in the two side lines.
  have hmemB : B ∈ line[ℝ, B, C] := left_mem_affineSpan_pair _ _ _
  have hmemC2 : C ∈ line[ℝ, B, C] := right_mem_affineSpan_pair _ _ _
  have hmemA : A ∈ line[ℝ, C, A] := right_mem_affineSpan_pair _ _ _
  have hmemC : C ∈ line[ℝ, C, A] := left_mem_affineSpan_pair _ _ _
  have hmemM : midpoint ℝ B C ∈ line[ℝ, B, C] :=
    (line[ℝ, B, C]).convex.midpoint_mem hmemB hmemC2
  -- Non-memberships forced by non-collinearity.
  have hAnot : A ∉ line[ℝ, B, C] := by
    intro hA
    exact hcoll ((collinear_insert_iff_of_mem_affineSpan hA).2 (collinear_pair _ _ _))
  have hBnot : B ∉ line[ℝ, C, A] := by
    intro hB
    apply hcoll
    rw [Set.insert_comm, Set.pair_comm A C]
    exact (collinear_insert_iff_of_mem_affineSpan hB).2 (collinear_pair _ _ _)
  -- Positivity of the altitudes.
  have ha_pos : 0 < ha := by
    rw [← hha]
    exact lt_of_le_of_ne dist_nonneg
      (Ne.symm (dist_orthogonalProjection_ne_zero_of_notMem hAnot))
  have hb_pos : 0 < hb := by
    rw [← hhb]
    exact lt_of_le_of_ne dist_nonneg
      (Ne.symm (dist_orthogonalProjection_ne_zero_of_notMem hBnot))
  have hma' : dist (midpoint ℝ B C) A = ma := by rw [dist_comm]; exact hma
  -- `ha ≤ ma` by Pythagoras in the foot/midpoint right triangle.
  have hP := dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq
    (s := line[ℝ, B, C]) (p₂ := A) hmemM
  have ha_le : ha ≤ ma := by
    nlinarith [hP, hha, hma',
      mul_self_nonneg (dist (midpoint ℝ B C) ↑(orthogonalProjection line[ℝ, B, C] A)),
      ha_pos, (dist_nonneg : 0 ≤ dist (midpoint ℝ B C) A)]
  -- The foot of the perpendicular from the midpoint of `BC` to line `CA` is the
  -- midpoint of `C` and the foot from `B`.
  have hfoot : (↑(orthogonalProjection line[ℝ, C, A] (midpoint ℝ B C)) :
        EuclideanSpace ℝ (Fin 2))
      = midpoint ℝ (↑(orthogonalProjection line[ℝ, C, A] B) : EuclideanSpace ℝ (Fin 2)) C := by
    rw [coe_orthogonalProjection_eq_iff_mem]
    refine ⟨?_, ?_⟩
    · exact (line[ℝ, C, A]).convex.midpoint_mem (orthogonalProjection_mem _) hmemC
    · rw [midpoint_vsub_midpoint_same_right]
      exact (line[ℝ, C, A]).directionᗮ.smul_mem _
        (vsub_orthogonalProjection_mem_direction_orthogonal _ _)
  -- Hence the midpoint of `BC` is at distance `hb / 2` from line `CA`.
  have hdist : dist (midpoint ℝ B C) ↑(orthogonalProjection line[ℝ, C, A] (midpoint ℝ B C))
      = hb / 2 := by
    have h2 : (0 : ℝ) ≤ ⅟2 := by rw [invOf_eq_inv]; positivity
    rw [hfoot, dist_eq_norm_vsub, midpoint_vsub_midpoint_same_right, norm_smul,
      ← dist_eq_norm_vsub, hhb, Real.norm_eq_abs, abs_of_nonneg h2, invOf_eq_inv]
    ring
  -- That distance is at most the median length (Pythagoras again).
  have hclose : dist (midpoint ℝ B C) ↑(orthogonalProjection line[ℝ, C, A] (midpoint ℝ B C))
      ≤ dist (midpoint ℝ B C) A := by
    have hP2 := dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq
      (s := line[ℝ, C, A]) (p₂ := midpoint ℝ B C) hmemA
    nlinarith [hP2, dist_comm A (midpoint ℝ B C),
      mul_self_nonneg (dist A ↑(orthogonalProjection line[ℝ, C, A] (midpoint ℝ B C))),
      (dist_nonneg : 0 ≤ dist (midpoint ℝ B C) A)]
  have hb_le : hb ≤ 2 * ma := by linarith [hdist, hclose, hma']
  -- The two boundary equalities cannot hold simultaneously.
  have edge : ha < ma ∨ hb < 2 * ma := by
    by_contra hne
    push Not at hne
    have ham : ha = ma := le_antisymm ha_le hne.1
    have hbm : hb = 2 * ma := le_antisymm hb_le hne.2
    -- Then the foot from `A` is the midpoint, so `AM ⟂ BC`.
    have e1 : (↑(orthogonalProjection line[ℝ, B, C] A) : EuclideanSpace ℝ (Fin 2))
        = midpoint ℝ B C := by
      apply (dist_orthogonalProjection_eq_dist_iff_eq_of_mem hmemM).1
      rw [hha, hma, ham]
    have o1 : A -ᵥ midpoint ℝ B C ∈ (line[ℝ, B, C]).directionᗮ := by
      have h1 := vsub_orthogonalProjection_mem_direction_orthogonal line[ℝ, B, C] A
      rwa [e1] at h1
    have i1 : ⟪A -ᵥ midpoint ℝ B C, B -ᵥ C⟫ = 0 :=
      Submodule.inner_left_of_mem_orthogonal
        (AffineSubspace.vsub_mem_direction hmemB hmemC2) o1
    -- And the foot from the midpoint is `A`, so `AM ⟂ CA`.
    have e2 : (↑(orthogonalProjection line[ℝ, C, A] (midpoint ℝ B C)) :
          EuclideanSpace ℝ (Fin 2)) = A := by
      apply (dist_orthogonalProjection_eq_dist_iff_eq_of_mem hmemA).1
      rw [hdist, hbm, hma']
      ring
    have o2 : A -ᵥ midpoint ℝ B C ∈ (line[ℝ, C, A]).directionᗮ := by
      have h1 := vsub_orthogonalProjection_mem_direction_orthogonal line[ℝ, C, A]
        (midpoint ℝ B C)
      rw [e2] at h1
      have h2 := (line[ℝ, C, A]).directionᗮ.neg_mem h1
      rwa [neg_vsub_eq_vsub_rev] at h2
    have i2 : ⟪A -ᵥ midpoint ℝ B C, A -ᵥ C⟫ = 0 :=
      Submodule.inner_left_of_mem_orthogonal
        (AffineSubspace.vsub_mem_direction hmemA hmemC) o2
    have hne0 : A -ᵥ midpoint ℝ B C ≠ 0 := by
      rw [ne_eq, vsub_eq_zero_iff_eq]
      exact fun hAM => hAnot (hAM ▸ hmemM)
    exact hcoll (collinear_of_inner_eq_zero hne0 i1 i2)
  exact ⟨ha_pos, hb_pos, ha_le, hb_le, edge⟩

/-- Sufficiency: the construction. Given `ha`, `hb`, `ma` satisfying the constraints,
we exhibit a triangle with the prescribed altitudes and median. -/
theorem triangle_of_constraints (ha hb ma : ℝ)
    (hha : 0 < ha) (hhb : 0 < hb) (h1 : ha ≤ ma) (h2 : hb ≤ 2 * ma)
    (h3 : ha < ma ∨ hb < 2 * ma) :
    ∃ A B C : EuclideanSpace ℝ (Fin 2),
        ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))) ∧
        dist A (orthogonalProjection line[ℝ, B, C] A : EuclideanSpace ℝ (Fin 2)) = ha ∧
        dist B (orthogonalProjection line[ℝ, C, A] B : EuclideanSpace ℝ (Fin 2)) = hb ∧
        dist A (midpoint ℝ B C) = ma := by
  set k := hb / 2 with hk_def
  set d := Real.sqrt (ma^2 - ha^2) with hd_def
  set e := Real.sqrt (ma^2 - k^2) with he_def
  set D := ha * e + k * d with hD_def
  set c := ha * (d * e - k * ha) / D with hc_def
  have hk_pos : 0 < k := by rw [hk_def]; linarith
  have hma_pos : 0 < ma := lt_of_lt_of_le hha h1
  have hk_le : k ≤ ma := by rw [hk_def]; linarith
  have hd : d^2 = ma^2 - ha^2 := by
    rw [hd_def]
    exact Real.sq_sqrt (by nlinarith)
  have he : e^2 = ma^2 - k^2 := by
    rw [he_def]
    exact Real.sq_sqrt (by nlinarith)
  have hd0 : 0 ≤ d := by rw [hd_def]; exact Real.sqrt_nonneg _
  have he0 : 0 ≤ e := by rw [he_def]; exact Real.sqrt_nonneg _
  have hD : 0 < D := by
    rw [hD_def]
    rcases (add_nonneg (mul_nonneg hha.le he0) (mul_nonneg hk_pos.le hd0)).eq_or_lt
      with hzero | hpos
    · exfalso
      have hzero' : ha * e + k * d = 0 := hzero.symm
      rw [add_eq_zero_iff_of_nonneg (mul_nonneg hha.le he0) (mul_nonneg hk_pos.le hd0)] at hzero'
      obtain ⟨hhe, hkd⟩ := hzero'
      have heq : e = 0 := by
        rcases mul_eq_zero.mp hhe with h | h
        · linarith
        · exact h
      have hdq : d = 0 := by
        rcases mul_eq_zero.mp hkd with h | h
        · linarith
        · exact h
      have hsq1 : ma^2 = ha^2 := by rw [hdq] at hd; nlinarith
      have hsq2 : ma^2 = k^2 := by rw [heq] at he; nlinarith
      have hma_ha : ma = ha := (sq_eq_sq₀ hma_pos.le hha.le).mp hsq1
      have hma_k : ma = k := (sq_eq_sq₀ hma_pos.le hk_pos.le).mp hsq2
      rcases h3 with h | h <;> linarith
    · exact hpos
  have hDne : D ≠ 0 := hD.ne'
  have key1 : d - c = k * ma^2 / D := by
    rw [hc_def]
    field_simp
    rw [hD_def]
    linear_combination k * hd
  have key1_pos : 0 < d - c := by
    rw [key1]
    exact div_pos (mul_pos hk_pos (pow_pos hma_pos 2)) hD
  have key2 : c^2 + ha^2 = ha^2 * ma^4 / D^2 := by
    rw [hc_def]
    field_simp
    rw [hD_def]
    linear_combination (d^2 + ha^2) * he + ma^2 * hd
  have hkey : (d - c)^2 * ha^2 = k^2 * (c^2 + ha^2) := by
    rw [key1, key2]
    field_simp
  refine ⟨mk 0 ha, mk (2*d - c) 0, mk c 0, ?_, ?_, ?_, ?_⟩
  · -- The triangle is non-degenerate: its third vertex lies off the x-axis.
    intro hcoll
    have hBCne : mk (2*d - c) 0 ≠ mk c 0 := by
      intro h
      have h0 := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) h
      simp [mk_apply] at h0
      linarith [key1_pos]
    have hA : mk 0 ha ∈ line[ℝ, mk (2*d - c) 0, mk c 0] :=
      hcoll.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hBCne
    have hv : mk 0 ha -ᵥ mk c 0 ∈ ℝ ∙ (mk (2*d - c) 0 -ᵥ mk c 0) := by
      rw [← vectorSpan_pair]
      exact vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan hA
        (right_mem_affineSpan_pair _ _ _)
    rw [Submodule.mem_span_singleton] at hv
    obtain ⟨t, ht⟩ := hv
    have ht1 := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 1) ht
    simp only [vsub_eq_sub, mk_sub, mk_smul, mk_apply] at ht1
    simp at ht1
    exact hha.ne' ht1.symm
  · -- The altitude from `A`: the foot is the origin.
    have hO : mk 0 0 = AffineMap.lineMap (mk (2*d - c) 0) (mk c 0) ((2*d - c)/(2*(d - c))) := by
      have hdc : (2:ℝ)*(d - c) ≠ 0 := by linarith [key1_pos]
      rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, mk_sub, mk_smul, mk_add]
      apply mk_ext
      · have ht : (2*d - c)/(2*(d - c)) * (2*(d - c)) = 2*d - c := div_mul_cancel₀ _ hdc
        linear_combination ht
      · ring
    have hOmem : mk 0 0 ∈ line[ℝ, mk (2*d - c) 0, mk c 0] :=
      hO.symm ▸ AffineMap.lineMap_mem_affineSpan_pair _ _ _
    have hOorth : mk 0 ha -ᵥ mk 0 0 ∈ (line[ℝ, mk (2*d - c) 0, mk c 0]).directionᗮ := by
      rw [direction_affineSpan, vectorSpan_pair, Submodule.mem_orthogonal_singleton_iff_inner_left]
      simp only [vsub_eq_sub, mk_sub]
      rw [PiLp.inner_apply, Fin.sum_univ_two]
      simp [mk_apply]
    have hproj : (↑(orthogonalProjection line[ℝ, mk (2*d - c) 0, mk c 0] (mk 0 ha)) :
        EuclideanSpace ℝ (Fin 2)) = mk 0 0 :=
      (coe_orthogonalProjection_eq_iff_mem).2 ⟨hOmem, hOorth⟩
    rw [hproj]
    simp [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, mk_apply]
    exact Real.sqrt_sq hha.le
  · -- The altitude from `B`: the foot is `lineMap C A t₀`.
    set t₀ := 2*c*(c - d)/(c^2 + ha^2) with ht₀
    have hcs : c^2 + ha^2 ≠ 0 := by
      have hpos : 0 < c^2 + ha^2 := by nlinarith [sq_nonneg c, hha]
      exact hpos.ne'
    have e1 : ⟪mk (2*d - c) 0 -ᵥ mk c 0, mk 0 ha -ᵥ mk c 0⟫ = 2*c*(c - d) := by
      simp only [vsub_eq_sub, mk_sub]
      rw [PiLp.inner_apply, Fin.sum_univ_two]
      simp [mk_apply]
      ring
    have e2 : ⟪mk 0 ha -ᵥ mk c 0, mk 0 ha -ᵥ mk c 0⟫ = c^2 + ha^2 := by
      simp only [vsub_eq_sub, mk_sub]
      rw [PiLp.inner_apply, Fin.sum_univ_two]
      simp [mk_apply]
    have hFeq : AffineMap.lineMap (mk c 0) (mk 0 ha) t₀ = mk (t₀*(0 - c) + c) (t₀*(ha - 0) + 0) := by
      rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, mk_sub, mk_smul, mk_add]
    have hFmem : AffineMap.lineMap (mk c 0) (mk 0 ha) t₀ ∈ line[ℝ, mk c 0, mk 0 ha] :=
      AffineMap.lineMap_mem_affineSpan_pair _ _ _
    have hForth : mk (2*d - c) 0 -ᵥ AffineMap.lineMap (mk c 0) (mk 0 ha) t₀ ∈
        (line[ℝ, mk c 0, mk 0 ha]).directionᗮ := by
      rw [direction_affineSpan, vectorSpan_pair_rev,
        Submodule.mem_orthogonal_singleton_iff_inner_left]
      rw [show AffineMap.lineMap (mk c 0) (mk 0 ha) t₀ = t₀ • (mk 0 ha -ᵥ mk c 0) +ᵥ mk c 0 from
        AffineMap.lineMap_apply _ _ _, vsub_vadd_eq_vsub_sub, inner_sub_left, inner_smul_left]
      simp only [RCLike.conj_to_real]
      rw [e1, e2, ht₀]
      field_simp
      ring
    have hprojB : (↑(orthogonalProjection line[ℝ, mk c 0, mk 0 ha] (mk (2*d - c) 0)) :
        EuclideanSpace ℝ (Fin 2)) = AffineMap.lineMap (mk c 0) (mk 0 ha) t₀ :=
      (coe_orthogonalProjection_eq_iff_mem).2 ⟨hFmem, hForth⟩
    rw [hprojB, hFeq, dist_eq_norm, mk_sub, mk_norm]
    have hX : (2*d - c - (t₀*(0 - c) + c))^2 + (0 - (t₀*(ha - 0) + 0))^2 = (2*k)^2 := by
      have hX1 : 2*d - c - (t₀*(0 - c) + c) = 2*(d - c)*ha^2/(c^2 + ha^2) := by
        rw [ht₀]
        field_simp
        ring
      have hX2 : 0 - (t₀*(ha - 0) + 0) = 2*c*(d - c)*ha/(c^2 + ha^2) := by
        rw [ht₀]
        field_simp
        ring
      have hX3 : (2*(d - c)*ha^2/(c^2 + ha^2))^2 + (2*c*(d - c)*ha/(c^2 + ha^2))^2
          = 4*(d - c)^2*ha^2/(c^2 + ha^2) := by
        field_simp
        ring
      rw [hX1, hX2, hX3]
      field_simp
      linear_combination 4 * hkey
    rw [hX]
    have h2k : (2*k)^2 = hb^2 := by rw [hk_def]; ring
    rw [h2k]
    exact Real.sqrt_sq hhb.le
  · -- The median from `A`: the midpoint of `BC` is `mk d 0`.
    have hmid : midpoint ℝ (mk (2*d - c) 0) (mk c 0) = mk d 0 := by
      rw [show midpoint ℝ (mk (2*d - c) 0) (mk c 0) =
          AffineMap.lineMap (mk (2*d - c) 0) (mk c 0) (⅟2 : ℝ) from rfl]
      rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, mk_sub, mk_smul, mk_add,
        show (⅟2 : ℝ) = 2⁻¹ from rfl]
      apply mk_ext <;> field_simp <;> ring
    have hdsq : (0 - d)^2 + (ha - 0)^2 = d^2 + ha^2 := by ring
    rw [hmid, dist_eq_norm, mk_sub, mk_norm, hdsq, hd, sub_add_cancel]
    exact Real.sqrt_sq hma_pos.le

snip end

problem imo1960_p4 (ha hb ma : ℝ) :
    (∃ A B C : EuclideanSpace ℝ (Fin 2),
        ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))) ∧
        dist A (orthogonalProjection line[ℝ, B, C] A : EuclideanSpace ℝ (Fin 2)) = ha ∧
        dist B (orthogonalProjection line[ℝ, C, A] B : EuclideanSpace ℝ (Fin 2)) = hb ∧
        dist A (midpoint ℝ B C) = ma) ↔
      0 < ha ∧ 0 < hb ∧ ha ≤ ma ∧ hb ≤ 2 * ma ∧ (ha < ma ∨ hb < 2 * ma) :=
  ⟨constraints_of_triangle ha hb ma, fun h =>
    triangle_of_constraints ha hb ma h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2⟩

end Imo1960P4
