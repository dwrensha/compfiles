/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.TwoDim
public import Mathlib.Geometry.Euclidean.Sphere.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1998, Problem 1

In the convex quadrilateral ABCD, the diagonals AC and BD are perpendicular and
the opposite sides AB and DC are not parallel. The point P, where the
perpendicular bisectors of AB and DC meet, is inside ABCD. Prove that ABCD is
cyclic if and only if the triangles ABP and CDP have equal areas.

## Formalization notes

* That `ABCD` is a convex quadrilateral is formalized by asking that the
  diagonals `AC` and `BD` meet at a point `X` that lies strictly between the
  endpoints of each diagonal.
* "`P` is inside `ABCD`" is formalized as
  `P ∈ interior (convexHull ℝ {A, B, C, D})`.
* The area of a triangle is half the absolute value of its signed area
  (`Orientation.areaForm`).
-/

namespace Imo1998P1

open scoped RealInnerProductSpace

open EuclideanGeometry

/-- The Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨finrank_euclideanSpace_fin⟩

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

noncomputable local instance : Module.Oriented ℝ Plane (Fin 2) :=
  ⟨Module.Basis.orientation (Module.finBasisOfFinrankEq _ _
    (Fact.out : Module.finrank ℝ Plane = 2))⟩

/-- The signed area form coming from the orientation of the plane. -/
noncomputable abbrev ω : Plane →ₗ[ℝ] Plane →ₗ[ℝ] ℝ :=
  (positiveOrientation : Orientation ℝ Plane (Fin 2)).areaForm

snip begin

/-- The (unsigned) area of a triangle, as half the absolute value of its signed
area. -/
noncomputable def triangleArea (A B C : Plane) : ℝ := |ω (B - A) (C - A)| / 2

/-- Two orthonormal vectors span the plane. -/
lemma exists_coords {u₁ u₂ : Plane} (hu1 : ‖u₁‖ = 1) (hu2 : ‖u₂‖ = 1)
    (hu12 : ⟪u₁, u₂⟫ = 0) (v : Plane) :
    ∃ a b : ℝ, v = a • u₁ + b • u₂ := by
  have hon : Orthonormal ℝ ![u₁, u₂] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.mk_zero, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
        ↓reduceIte]
    · rw [real_inner_self_eq_norm_sq, hu1, one_pow]
    · exact hu12
    · rw [real_inner_comm]; exact hu12
    · rw [real_inner_self_eq_norm_sq, hu2, one_pow]
  have hli := hon.linearIndependent
  have hspan : Submodule.span ℝ (Set.range ![u₁, u₂]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin, finrank_euclideanSpace_fin])
  have hmem : v ∈ Submodule.span ℝ (Set.range ![u₁, u₂]) := by
    rw [hspan]; exact Submodule.mem_top
  rw [Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c, hc⟩ := hmem
  refine ⟨c 0, c 1, ?_⟩
  rw [Fin.sum_univ_two] at hc
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc
  exact hc.symm

/-- The squared norm of a combination of orthonormal vectors. -/
lemma inner_comb {u₁ u₂ : Plane} (hu1 : ‖u₁‖ = 1) (hu2 : ‖u₂‖ = 1)
    (hu12 : ⟪u₁, u₂⟫ = 0) (a b : ℝ) :
    ⟪a • u₁ + b • u₂, a • u₁ + b • u₂⟫ = a ^ 2 + b ^ 2 := by
  have h11 : ⟪u₁, u₁⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu1, one_pow]
  have h22 : ⟪u₂, u₂⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu2, one_pow]
  have h21 : ⟪u₂, u₁⟫ = 0 := by rw [real_inner_comm]; exact hu12
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    h11, h22, hu12, h21]
  ring

/-- The signed area of a parallelogram spanned by combinations of two vectors. -/
lemma areaForm_comb {u₁ u₂ : Plane} (a b c d : ℝ) :
    ω (a • u₁ + b • u₂) (c • u₁ + d • u₂) = (a * d - b * c) * ω u₁ u₂ := by
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    Orientation.areaForm_apply_self, smul_eq_mul, mul_zero, add_zero, zero_add]
  rw [Orientation.areaForm_swap _ u₂ u₁]
  ring

/-- A point strictly between `A` and `C` gives axis coordinates. -/
lemma sbtw_coords {A C X : Plane} (h : Sbtw ℝ A X C) :
    ∃ (u : Plane) (p q : ℝ), ‖u‖ = 1 ∧ 0 < p ∧ 0 < q ∧
      A = X - p • u ∧ C = X + q • u := by
  obtain ⟨hXAC, hXA, hXC⟩ := h
  obtain ⟨t, ⟨ht0, ht1⟩, hXt⟩ := hXAC
  rw [AffineMap.lineMap_apply_module] at hXt
  have ht0' : 0 < t := by
    rcases ht0.eq_or_lt with h0 | h0
    · exfalso
      rw [← h0, sub_zero, one_smul, zero_smul, add_zero] at hXt
      exact hXA hXt.symm
    · exact h0
  have ht1' : t < 1 := by
    rcases ht1.eq_or_lt with h1' | h1'
    · exfalso
      rw [h1', sub_self, zero_smul, one_smul, zero_add] at hXt
      exact hXC hXt.symm
    · exact h1'
  have hAC : A ≠ C := by
    rintro rfl
    rw [← add_smul, sub_add_cancel, one_smul] at hXt
    exact hXA hXt.symm
  set d := dist A C with hd
  have hd0 : 0 < d := dist_pos.mpr hAC
  have hnorm : ‖d⁻¹ • (C - A)‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd0), ← dist_eq_norm,
      dist_comm, inv_mul_cancel₀ (ne_of_gt hd0)]
  have hAeq : A = X - (t * d) • (d⁻¹ • (C - A)) := by
    rw [smul_smul, mul_inv_cancel_right₀ (ne_of_gt hd0), ← hXt]
    module
  have hCeq : C = X + ((1 - t) * d) • (d⁻¹ • (C - A)) := by
    rw [smul_smul, mul_inv_cancel_right₀ (ne_of_gt hd0), ← hXt]
    module
  exact ⟨d⁻¹ • (C - A), t * d, (1 - t) * d, hnorm, mul_pos ht0' hd0,
    mul_pos (sub_pos.mpr ht1') hd0, hAeq, hCeq⟩

/-- A nonzero linear function that is `≥ t` on a set is `> t` in the interior of
its convex hull. -/
lemma lt_of_mem_interior_convexHull {M : Plane →ₗ[ℝ] ℝ} {t : ℝ} {S : Set Plane}
    {P : Plane} (hM : M ≠ 0) (hP : P ∈ interior (convexHull ℝ S))
    (hS : ∀ z ∈ S, t ≤ M z) :
    t < M P := by
  by_contra hle
  push Not at hle
  have hconv_half : Convex ℝ {z : Plane | t ≤ M z} :=
    convex_halfSpace_ge ⟨M.map_add, M.map_smul⟩ t
  have hsub : convexHull ℝ S ⊆ {z : Plane | t ≤ M z} := convexHull_min hS hconv_half
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior P hP
  have hb : Metric.ball P ε ⊆ {z : Plane | t ≤ M z} :=
    hball.trans (interior_subset.trans hsub)
  obtain ⟨v, hv⟩ : ∃ v, M v ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hM (LinearMap.ext fun w => by rw [hall w, LinearMap.zero_apply])
  set w := (M v)⁻¹ • v with hw
  have hMw : M w = 1 := by rw [hw, map_smul, smul_eq_mul, inv_mul_cancel₀ hv]
  set δ := ε / (‖w‖ + 1) with hδdef
  have hδpos : 0 < δ := by positivity
  have hzball : P - δ • w ∈ Metric.ball P ε := by
    rw [Metric.mem_ball, dist_comm, dist_eq_norm, sub_sub_self, norm_smul, Real.norm_eq_abs,
      abs_of_pos hδpos, hδdef]
    calc ε / (‖w‖ + 1) * ‖w‖ = ε * (‖w‖ / (‖w‖ + 1)) := by ring
      _ < ε := by
          have h1 : ‖w‖ / (‖w‖ + 1) < 1 := by
            rw [div_lt_one (by positivity)]
            exact lt_add_of_pos_right _ zero_lt_one
          calc ε * (‖w‖ / (‖w‖ + 1)) < ε * 1 := by
                exact mul_lt_mul_of_pos_left h1 hε
            _ = ε := mul_one _
  have hzM : t ≤ M (P - δ • w) := hb hzball
  rw [map_sub, map_smul, hMw, smul_eq_mul, mul_one] at hzM
  linarith [hzM, hle, hδpos]

/-- Equality of squared distances as an equality of inner products. -/
lemma inner_self_eq_inner_self_of_dist_eq {X U V : Plane} (h : dist X U = dist X V) :
    ⟪X - U, X - U⟫ = ⟪X - V, X - V⟫ := by
  have h2 : (dist X U) ^ 2 = (dist X V) ^ 2 := by rw [h]
  rwa [dist_eq_norm, dist_eq_norm, ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq] at h2

/-- The algebraic heart of the problem. -/
lemma algebra_core {p q r s x y : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hs : 0 < s)
    (hW : q * r - p * s ≠ 0)
    (h1 : 2 * p * x - 2 * r * y = r ^ 2 - p ^ 2)
    (h2 : 2 * q * x - 2 * s * y = q ^ 2 - s ^ 2) :
    x * (r + s) + y * (p + q) = s * q - r * p ↔ p * q = r * s := by
  have hpq : (0:ℝ) < p + q := by linarith
  have hS : (0:ℝ) < (p + q) ^ 2 + (r + s) ^ 2 := by positivity
  have key : 2 * (q * r - p * s) * (x * (r + s) + y * (p + q) - (s * q - r * p)) -
      (p * q - r * s) * ((p + q) ^ 2 + (r + s) ^ 2)
      = (r * (r + s) + p * (p + q)) * (2 * q * x - 2 * s * y - (q ^ 2 - s ^ 2)) -
        (s * (r + s) + q * (p + q)) * (2 * p * x - 2 * r * y - (r ^ 2 - p ^ 2)) := by
    ring
  have eq1 : 2 * p * x - 2 * r * y - (r ^ 2 - p ^ 2) = 0 := by linarith [h1]
  have eq2 : 2 * q * x - 2 * s * y - (q ^ 2 - s ^ 2) = 0 := by linarith [h2]
  rw [eq1, eq2] at key
  simp only [mul_zero, sub_zero] at key
  constructor
  · intro hL
    have hL0 : x * (r + s) + y * (p + q) - (s * q - r * p) = 0 := by linarith [hL]
    rw [hL0, mul_zero, zero_sub, neg_eq_zero] at key
    rcases mul_eq_zero.mp key with hR | hS0
    · linarith [hR]
    · linarith [hS0, hS]
  · intro hR
    have hR0 : p * q - r * s = 0 := by linarith [hR]
    rw [hR0, zero_mul, sub_zero] at key
    rcases mul_eq_zero.mp key with h2W | hL'
    · exact absurd (by linarith [h2W] : q * r - p * s = 0) hW
    · linarith [hL']

/-- In the coordinate setup, cocircularity is equivalent to `p * q = r * s`. -/
lemma cospherical_iff {X u₁ u₂ : Plane} {p q r s : ℝ}
    (hu1 : ‖u₁‖ = 1) (hu2 : ‖u₂‖ = 1) (hu12 : ⟪u₁, u₂⟫ = 0)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hs : 0 < s)
    {A B C D : Plane}
    (hA : A = X - p • u₁) (hB : B = X - r • u₂)
    (hC : C = X + q • u₁) (hD : D = X + s • u₂) :
    Cospherical ({A, B, C, D} : Set Plane) ↔ p * q = r * s := by
  have hpq0 : (p:ℝ) + q ≠ 0 := by positivity
  have hrs0 : (r:ℝ) + s ≠ 0 := by positivity
  constructor
  · rintro ⟨O, R, hO⟩
    have hOA : dist A O = R := hO A (by simp)
    have hOB : dist B O = R := hO B (by simp)
    have hOC : dist C O = R := hO C (by simp)
    have hOD : dist D O = R := hO D (by simp)
    obtain ⟨h, k, hOX⟩ := exists_coords hu1 hu2 hu12 (O - X)
    have hAX : A - X = -(p • u₁) := by rw [hA]; module
    have hBX : B - X = -(r • u₂) := by rw [hB]; module
    have hCX : C - X = q • u₁ := by rw [hC]; module
    have hDX : D - X = s • u₂ := by rw [hD]; module
    have hAO : A - O = (-p - h) • u₁ + (-k) • u₂ := by
      rw [show A - O = (A - X) - (O - X) from by abel, hAX, hOX]; module
    have hBO : B - O = (-h) • u₁ + (-r - k) • u₂ := by
      rw [show B - O = (B - X) - (O - X) from by abel, hBX, hOX]; module
    have hCO : C - O = (q - h) • u₁ + (-k) • u₂ := by
      rw [show C - O = (C - X) - (O - X) from by abel, hCX, hOX]; module
    have hDO : D - O = (-h) • u₁ + (s - k) • u₂ := by
      rw [show D - O = (D - X) - (O - X) from by abel, hDX, hOX]; module
    have iac : ⟪A - O, A - O⟫ = ⟪C - O, C - O⟫ := by
      have h1 : (dist A O) ^ 2 = (dist C O) ^ 2 := by rw [hOA, hOC]
      rwa [dist_eq_norm, dist_eq_norm, ← real_inner_self_eq_norm_sq,
        ← real_inner_self_eq_norm_sq] at h1
    have ibd : ⟪B - O, B - O⟫ = ⟪D - O, D - O⟫ := by
      have h1 : (dist B O) ^ 2 = (dist D O) ^ 2 := by rw [hOB, hOD]
      rwa [dist_eq_norm, dist_eq_norm, ← real_inner_self_eq_norm_sq,
        ← real_inner_self_eq_norm_sq] at h1
    have iab : ⟪A - O, A - O⟫ = ⟪B - O, B - O⟫ := by
      have h1 : (dist A O) ^ 2 = (dist B O) ^ 2 := by rw [hOA, hOB]
      rwa [dist_eq_norm, dist_eq_norm, ← real_inner_self_eq_norm_sq,
        ← real_inner_self_eq_norm_sq] at h1
    rw [hAO, hCO, inner_comb hu1 hu2 hu12, inner_comb hu1 hu2 hu12] at iac
    rw [hBO, hDO, inner_comb hu1 hu2 hu12, inner_comb hu1 hu2 hu12] at ibd
    rw [hAO, hBO, inner_comb hu1 hu2 hu12, inner_comb hu1 hu2 hu12] at iab
    have hh : (2 * h - (q - p)) * (p + q) = 0 := by linear_combination iac
    have hk : (2 * k - (s - r)) * (r + s) = 0 := by linear_combination ibd
    have h2h : 2 * h = q - p := by
      rcases mul_eq_zero.mp hh with h' | h'
      · linarith [h']
      · exact absurd h' hpq0
    have h2k : 2 * k = s - r := by
      rcases mul_eq_zero.mp hk with h' | h'
      · linarith [h']
      · exact absurd h' hrs0
    linear_combination iab - p * h2h + r * h2k
  · intro hpqrs
    refine ⟨X + ((q - p) / 2) • u₁ + ((s - r) / 2) • u₂,
      dist A (X + ((q - p) / 2) • u₁ + ((s - r) / 2) • u₂), fun z hz => ?_⟩
    have hAX : A - X = -(p • u₁) := by rw [hA]; module
    have hBX : B - X = -(r • u₂) := by rw [hB]; module
    have hCX : C - X = q • u₁ := by rw [hC]; module
    have hDX : D - X = s • u₂ := by rw [hD]; module
    have hOX : (X + ((q - p) / 2) • u₁ + ((s - r) / 2) • u₂) - X
        = ((q - p) / 2) • u₁ + ((s - r) / 2) • u₂ := by module
    have hAO : A - (X + ((q - p) / 2) • u₁ + ((s - r) / 2) • u₂)
        = (-p - (q - p) / 2) • u₁ + (-(s - r) / 2) • u₂ := by
      rw [show A - (X + ((q - p) / 2) • u₁ + ((s - r) / 2) • u₂)
          = (A - X) - ((X + ((q - p) / 2) • u₁ + ((s - r) / 2) • u₂) - X) from by abel,
        hAX, hOX]; module
    have hBO : B - (X + ((q - p) / 2) • u₁ + ((s - r) / 2) • u₂)
        = (-(q - p) / 2) • u₁ + (-r - (s - r) / 2) • u₂ := by
      rw [show B - (X + ((q - p) / 2) • u₁ + ((s - r) / 2) • u₂)
          = (B - X) - ((X + ((q - p) / 2) • u₁ + ((s - r) / 2) • u₂) - X) from by abel,
        hBX, hOX]; module
    have hCO : C - (X + ((q - p) / 2) • u₁ + ((s - r) / 2) • u₂)
        = (q - (q - p) / 2) • u₁ + (-(s - r) / 2) • u₂ := by
      rw [show C - (X + ((q - p) / 2) • u₁ + ((s - r) / 2) • u₂)
          = (C - X) - ((X + ((q - p) / 2) • u₁ + ((s - r) / 2) • u₂) - X) from by abel,
        hCX, hOX]; module
    have hDO : D - (X + ((q - p) / 2) • u₁ + ((s - r) / 2) • u₂)
        = (-(q - p) / 2) • u₁ + (s - (s - r) / 2) • u₂ := by
      rw [show D - (X + ((q - p) / 2) • u₁ + ((s - r) / 2) • u₂)
          = (D - X) - ((X + ((q - p) / 2) • u₁ + ((s - r) / 2) • u₂) - X) from by abel,
        hDX, hOX]; module
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · rfl
    · rw [← sq_eq_sq₀ dist_nonneg dist_nonneg, dist_eq_norm, dist_eq_norm,
        ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hBO, hAO,
        inner_comb hu1 hu2 hu12, inner_comb hu1 hu2 hu12]
      linear_combination -hpqrs
    · rw [← sq_eq_sq₀ dist_nonneg dist_nonneg, dist_eq_norm, dist_eq_norm,
        ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hCO, hAO,
        inner_comb hu1 hu2 hu12, inner_comb hu1 hu2 hu12]
      ring
    · rw [← sq_eq_sq₀ dist_nonneg dist_nonneg, dist_eq_norm, dist_eq_norm,
        ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hDO, hAO,
        inner_comb hu1 hu2 hu12, inner_comb hu1 hu2 hu12]
      linear_combination -hpqrs

/-- A point inside the quadrilateral lies strictly on the interior side of the
edges `AB` and `CD`. -/
lemma interior_pos {X u₁ u₂ : Plane} {p q r s x y : ℝ}
    (hu1 : ‖u₁‖ = 1) (hu2 : ‖u₂‖ = 1) (hu12 : ⟪u₁, u₂⟫ = 0)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hs : 0 < s)
    {A B C D P : Plane}
    (hA : A = X - p • u₁) (hB : B = X - r • u₂)
    (hC : C = X + q • u₁) (hD : D = X + s • u₂)
    (hPX : P - X = x • u₁ + y • u₂)
    (hP : P ∈ interior (convexHull ℝ ({A, B, C, D} : Set Plane))) :
    0 < p * y + r * x + r * p ∧ 0 < s * q - s * x - q * y := by
  have hσ : |ω u₁ u₂| = 1 := by
    have h : |ω u₁ u₂| = ‖u₁‖ * ‖u₂‖ := Orientation.abs_areaForm_of_orthogonal _ hu12
    rwa [hu1, hu2, mul_one] at h
  have hσ2 : (ω u₁ u₂) ^ 2 = 1 := by
    have h := congrArg (· ^ 2) hσ
    rwa [sq_abs, one_pow] at h
  have hpq : (0:ℝ) < p + q := by linarith
  -- vector combinations for all the differences we need
  have hXA : X - A = p • u₁ := by rw [hA]; module
  have hXC : X - C = -(q • u₁) := by rw [hC]; module
  have hXA0 : X - A = p • u₁ + (0:ℝ) • u₂ := by rw [hXA]; module
  have hXC0 : X - C = (-q) • u₁ + (0:ℝ) • u₂ := by rw [hXC]; module
  have hBA : B - A = p • u₁ + (-r) • u₂ := by rw [hA, hB]; module
  have hCA : C - A = (p + q) • u₁ + (0:ℝ) • u₂ := by rw [hA, hC]; module
  have hDA : D - A = p • u₁ + s • u₂ := by rw [hA, hD]; module
  have hDC : D - C = (-q) • u₁ + s • u₂ := by rw [hC, hD]; module
  have hAC : A - C = (-(p + q)) • u₁ + (0:ℝ) • u₂ := by rw [hA, hC]; module
  have hBC : B - C = (-q) • u₁ + (-r) • u₂ := by rw [hB, hC]; module
  have hPA : P - A = (x + p) • u₁ + y • u₂ := by
    rw [← sub_add_sub_cancel P X A, hPX, hXA]; module
  have hPC : P - C = (x - q) • u₁ + y • u₂ := by
    rw [← sub_add_sub_cancel P X C, hPX, hXC]; module
  -- signed areas of the relevant configurations
  have hf1C : ω (B - A) (C - A) = (r * (p + q)) * ω u₁ u₂ := by
    rw [hBA, hCA, areaForm_comb]; ring
  have hf1D : ω (B - A) (D - A) = (p * s + r * p) * ω u₁ u₂ := by
    rw [hBA, hDA, areaForm_comb]; ring
  have hf1P : ω (B - A) (P - A) = (p * y + r * x + r * p) * ω u₁ u₂ := by
    rw [hBA, hPA, areaForm_comb]; ring
  have hf2A : ω (D - C) (A - C) = (s * (p + q)) * ω u₁ u₂ := by
    rw [hDC, hAC, areaForm_comb]; ring
  have hf2B : ω (D - C) (B - C) = (q * r + s * q) * ω u₁ u₂ := by
    rw [hDC, hBC, areaForm_comb]; ring
  have hf2P : ω (D - C) (P - C) = (s * q - s * x - q * y) * ω u₁ u₂ := by
    rw [hDC, hPC, areaForm_comb]; ring
  -- first half-plane, supported on edge AB
  have hE1 : 0 < p * y + r * x + r * p := by
    set M : Plane →ₗ[ℝ] ℝ := (r * p * ω u₁ u₂) • ω (B - A) with hMdef
    have hdiff : ∀ z : Plane, M z - M A = (r * p * ω u₁ u₂) * ω (B - A) (z - A) := by
      intro z
      rw [hMdef, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul,
        ← mul_sub, ← map_sub]
    have hMC : M C - M A = (r * r * p * (p + q)) * (ω u₁ u₂) ^ 2 := by
      rw [hdiff, hf1C]; ring
    have hMne : M ≠ 0 := by
      intro h0
      have hz : M C - M A = 0 := by rw [h0]; simp
      rw [hMC, hσ2, mul_one] at hz
      have hpos : 0 < r * r * p * (p + q) := by positivity
      exact (ne_of_gt hpos) hz
    have hMA_le : ∀ z ∈ ({A, B, C, D} : Set Plane), M A ≤ M z := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz | hz | hz
      · rw [hz]
      · rw [hz]
        have hzz : M B - M A = 0 := by
          rw [hdiff, Orientation.areaForm_apply_self, mul_zero]
        linarith [hzz]
      · rw [hz]
        have hzz : M C - M A = r * r * p * (p + q) := by rw [hMC, hσ2, mul_one]
        have hpos : 0 < r * r * p * (p + q) := by positivity
        linarith [hzz, hpos]
      · rw [hz]
        have hzz : M D - M A = r * p * (p * s + r * p) := by
          rw [hdiff, hf1D]
          linear_combination (r * p * (p * s + r * p)) * hσ2
        have hpos : 0 < r * p * (p * s + r * p) := by positivity
        linarith [hzz, hpos]
    have hlt := lt_of_mem_interior_convexHull hMne hP hMA_le
    have hMP : M P - M A = (r * p) * (p * y + r * x + r * p) := by
      rw [hdiff, hf1P]
      linear_combination (r * p * (p * y + r * x + r * p)) * hσ2
    have hpos : 0 < (r * p) * (p * y + r * x + r * p) := by linarith [hlt, hMP]
    exact pos_of_mul_pos_right hpos (by positivity)
  -- second half-plane, supported on edge CD
  have hE2 : 0 < s * q - s * x - q * y := by
    set M : Plane →ₗ[ℝ] ℝ := (s * q * ω u₁ u₂) • ω (D - C) with hMdef
    have hdiff : ∀ z : Plane, M z - M C = (s * q * ω u₁ u₂) * ω (D - C) (z - C) := by
      intro z
      rw [hMdef, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul,
        ← mul_sub, ← map_sub]
    have hMA : M A - M C = (s * s * q * (p + q)) * (ω u₁ u₂) ^ 2 := by
      rw [hdiff, hf2A]; ring
    have hMne : M ≠ 0 := by
      intro h0
      have hz : M A - M C = 0 := by rw [h0]; simp
      rw [hMA, hσ2, mul_one] at hz
      have hpos : 0 < s * s * q * (p + q) := by positivity
      exact (ne_of_gt hpos) hz
    have hMC_le : ∀ z ∈ ({A, B, C, D} : Set Plane), M C ≤ M z := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz | hz | hz
      · rw [hz]
        have hzz : M A - M C = s * s * q * (p + q) := by rw [hMA, hσ2, mul_one]
        have hpos : 0 < s * s * q * (p + q) := by positivity
        linarith [hzz, hpos]
      · rw [hz]
        have hzz : M B - M C = s * q * (q * r + s * q) := by
          rw [hdiff, hf2B]
          linear_combination (s * q * (q * r + s * q)) * hσ2
        have hpos : 0 < s * q * (q * r + s * q) := by positivity
        linarith [hzz, hpos]
      · rw [hz]
      · rw [hz]
        have hzz : M D - M C = 0 := by
          rw [hdiff, Orientation.areaForm_apply_self, mul_zero]
        linarith [hzz]
    have hlt := lt_of_mem_interior_convexHull hMne hP hMC_le
    have hMP : M P - M C = (s * q) * (s * q - s * x - q * y) := by
      rw [hdiff, hf2P]
      linear_combination (s * q * (s * q - s * x - q * y)) * hσ2
    have hpos : 0 < (s * q) * (s * q - s * x - q * y) := by linarith [hlt, hMP]
    exact pos_of_mul_pos_right hpos (by positivity)
  exact ⟨hE1, hE2⟩

snip end

problem imo1998_p1
    (A B C D P : Plane)
    (hconv : ∃ X : Plane, Sbtw ℝ A X C ∧ Sbtw ℝ B X D)
    (hperp : ⟪C -ᵥ A, D -ᵥ B⟫ = 0)
    (hpara : vectorSpan ℝ ({A, B} : Set Plane) ≠ vectorSpan ℝ ({D, C} : Set Plane))
    (hbis1 : dist P A = dist P B)
    (hbis2 : dist P D = dist P C)
    (hinside : P ∈ interior (convexHull ℝ ({A, B, C, D} : Set Plane))) :
    Cospherical ({A, B, C, D} : Set Plane) ↔ triangleArea A B P = triangleArea C D P := by
  obtain ⟨X, hXAC, hXBD⟩ := hconv
  obtain ⟨u₁, p, q, hu1, hp, hq, hA, hC⟩ := sbtw_coords hXAC
  obtain ⟨u₂, r, s, hu2, hr, hs, hB, hD⟩ := sbtw_coords hXBD
  -- the two axes are perpendicular
  have hu12 : ⟪u₁, u₂⟫ = 0 := by
    have hCA : C - A = (p + q) • u₁ := by rw [hA, hC]; module
    have hDB : D - B = (r + s) • u₂ := by rw [hB, hD]; module
    have h0 : ⟪C - A, D - B⟫ = 0 := hperp
    rw [hCA, hDB, real_inner_smul_left, real_inner_smul_right] at h0
    rcases mul_eq_zero.mp h0 with h' | h'
    · exact absurd h' (ne_of_gt (by linarith : (0:ℝ) < p + q))
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact absurd h'' (ne_of_gt (by linarith : (0:ℝ) < r + s))
      · exact h''
  -- coordinates of P
  obtain ⟨x, y, hPX⟩ := exists_coords hu1 hu2 hu12 (P - X)
  have hXA : X - A = p • u₁ := by rw [hA]; module
  have hXB : X - B = r • u₂ := by rw [hB]; module
  have hXC : X - C = -(q • u₁) := by rw [hC]; module
  have hXD : X - D = -(s • u₂) := by rw [hD]; module
  have hPA : P - A = (x + p) • u₁ + y • u₂ := by
    rw [← sub_add_sub_cancel P X A, hPX, hXA]; module
  have hPB : P - B = x • u₁ + (y + r) • u₂ := by
    rw [← sub_add_sub_cancel P X B, hPX, hXB]; module
  have hPC : P - C = (x - q) • u₁ + y • u₂ := by
    rw [← sub_add_sub_cancel P X C, hPX, hXC]; module
  have hPD : P - D = x • u₁ + (y - s) • u₂ := by
    rw [← sub_add_sub_cancel P X D, hPX, hXD]; module
  have hBA : B - A = p • u₁ + (-r) • u₂ := by rw [hA, hB]; module
  have hDC : D - C = (-q) • u₁ + s • u₂ := by rw [hC, hD]; module
  -- the perpendicular bisector conditions
  have hdi1 : ⟪P - A, P - A⟫ = ⟪P - B, P - B⟫ := inner_self_eq_inner_self_of_dist_eq hbis1
  have hdi2 : ⟪P - D, P - D⟫ = ⟪P - C, P - C⟫ := inner_self_eq_inner_self_of_dist_eq hbis2
  rw [hPA, hPB, inner_comb hu1 hu2 hu12, inner_comb hu1 hu2 hu12] at hdi1
  rw [hPD, hPC, inner_comb hu1 hu2 hu12, inner_comb hu1 hu2 hu12] at hdi2
  have h1 : 2 * p * x - 2 * r * y = r ^ 2 - p ^ 2 := by linear_combination hdi1
  have h2 : 2 * q * x - 2 * s * y = q ^ 2 - s ^ 2 := by linear_combination hdi2
  -- AB is not parallel to DC
  have hW : q * r - p * s ≠ 0 := by
    intro hW0
    apply hpara
    rw [vectorSpan_pair, vectorSpan_pair]
    have hp0 : (p:ℝ) ≠ 0 := ne_of_gt hp
    have hqr : q * r = p * s := by linarith [hW0]
    have hscale : q / p * r = s := by
      rw [div_mul_eq_mul_div, div_eq_iff hp0]
      linear_combination hqr
    have hABv : A - B = (-p) • u₁ + r • u₂ := by rw [hA, hB]; module
    have hDCv : D - C = (-q) • u₁ + s • u₂ := by rw [hC, hD]; module
    have hscale2 : (-q) • u₁ + s • u₂ = (q / p) • ((-p) • u₁ + r • u₂) := by
      rw [smul_add]
      congr 1
      · rw [smul_smul]
        congr 1
        rw [mul_neg, div_mul_cancel₀ _ hp0]
      · rw [smul_smul]
        congr 1
        rw [hscale]
    show (ℝ ∙ (A - B)) = (ℝ ∙ (D - C))
    rw [hABv, hDCv, hscale2]
    apply le_antisymm
    · rw [Submodule.span_singleton_le_iff_mem]
      apply Submodule.mem_span_singleton.mpr ⟨(q / p)⁻¹, ?_⟩
      rw [smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
    · rw [Submodule.span_singleton_le_iff_mem]
      exact Submodule.mem_span_singleton.mpr ⟨q / p, rfl⟩
  -- sign facts from P lying inside the quadrilateral
  obtain ⟨hE1, hE2⟩ := interior_pos hu1 hu2 hu12 hp hq hr hs hA hB hC hD hPX hinside
  have hσ : |ω u₁ u₂| = 1 := by
    have h : |ω u₁ u₂| = ‖u₁‖ * ‖u₂‖ := Orientation.abs_areaForm_of_orthogonal _ hu12
    rwa [hu1, hu2, mul_one] at h
  -- the two triangle areas
  have harea1 : triangleArea A B P = (p * y + r * x + r * p) / 2 := by
    simp only [triangleArea]
    rw [hBA, hPA, areaForm_comb,
      show p * y - -r * (x + p) = p * y + r * x + r * p from by ring,
      abs_mul, hσ, mul_one, abs_of_pos hE1]
  have harea2 : triangleArea C D P = (s * q - s * x - q * y) / 2 := by
    simp only [triangleArea]
    rw [hDC, hPC, areaForm_comb,
      show -q * y - s * (x - q) = s * q - s * x - q * y from by ring,
      abs_mul, hσ, mul_one, abs_of_pos hE2]
  rw [harea1, harea2, cospherical_iff hu1 hu2 hu12 hp hq hr hs hA hB hC hD]
  have hLE : (p * y + r * x + r * p) / 2 = (s * q - s * x - q * y) / 2 ↔
      x * (r + s) + y * (p + q) = s * q - r * p := by
    constructor <;> intro h <;> linarith [h]
  rw [hLE]
  exact (algebra_core hp hq hr hs hW h1 h2).symm

end Imo1998P1
