/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Analysis.Convex.StrictConvexBetween
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Triangle
public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1968, Problem 1

Find all triangles whose side lengths are consecutive integers,
and one of whose angles is twice another.
-/

namespace Imo1968P1

open scoped EuclideanGeometry
open EuclideanGeometry

/-- The Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- One of the three angles of the triangle is twice another one. -/
abbrev Doubling (T : Affine.Triangle ℝ Plane) : Prop :=
  ∠ (T.points 1) (T.points 0) (T.points 2) = 2 * ∠ (T.points 0) (T.points 1) (T.points 2) ∨
  ∠ (T.points 1) (T.points 0) (T.points 2) = 2 * ∠ (T.points 0) (T.points 2) (T.points 1) ∨
  ∠ (T.points 0) (T.points 1) (T.points 2) = 2 * ∠ (T.points 1) (T.points 0) (T.points 2) ∨
  ∠ (T.points 0) (T.points 1) (T.points 2) = 2 * ∠ (T.points 0) (T.points 2) (T.points 1) ∨
  ∠ (T.points 0) (T.points 2) (T.points 1) = 2 * ∠ (T.points 1) (T.points 0) (T.points 2) ∨
  ∠ (T.points 0) (T.points 2) (T.points 1) = 2 * ∠ (T.points 0) (T.points 1) (T.points 2)

snip begin

lemma nc12 {a b c : Plane} (h : ¬Collinear ℝ ({a, b, c} : Set Plane)) :
    ¬Collinear ℝ ({b, a, c} : Set Plane) := by
  rwa [Set.insert_comm b a {c}]

lemma nc23 {a b c : Plane} (h : ¬Collinear ℝ ({a, b, c} : Set Plane)) :
    ¬Collinear ℝ ({a, c, b} : Set Plane) := by
  rwa [Set.pair_comm c b]

/-- Cosine of the angle opposite the side of length `x`, by the law of cosines. -/
lemma cosA_val (T : Affine.Triangle ℝ Plane) {x : ℝ} (hx : 0 < x)
    (h01 : dist (T.points 0) (T.points 1) = x + 2)
    (h12 : dist (T.points 1) (T.points 2) = x)
    (h20 : dist (T.points 2) (T.points 0) = x + 1) :
    Real.cos (∠ (T.points 1) (T.points 0) (T.points 2)) = (x + 5) / (2 * (x + 2)) := by
  have h := law_cos (T.points 1) (T.points 0) (T.points 2)
  rw [h12, dist_comm (T.points 1) (T.points 0), h01, h20] at h
  rw [eq_div_iff (by positivity : (2:ℝ) * (x + 2) ≠ 0)]
  have h2 : (x + 1) *
      (Real.cos (∠ (T.points 1) (T.points 0) (T.points 2)) * (2 * (x + 2)) - (x + 5)) = 0 := by
    linear_combination h
  exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left (by positivity))

/-- Cosine of the angle opposite the side of length `x + 1`, by the law of cosines. -/
lemma cosB_val (T : Affine.Triangle ℝ Plane) {x : ℝ} (hx : 0 < x)
    (h01 : dist (T.points 0) (T.points 1) = x + 2)
    (h12 : dist (T.points 1) (T.points 2) = x)
    (h20 : dist (T.points 2) (T.points 0) = x + 1) :
    Real.cos (∠ (T.points 0) (T.points 1) (T.points 2)) =
      (x ^ 2 + 2 * x + 3) / (2 * x * (x + 2)) := by
  have h := law_cos (T.points 0) (T.points 1) (T.points 2)
  rw [dist_comm (T.points 0) (T.points 2), h20, h01, dist_comm (T.points 2) (T.points 1), h12] at h
  rw [eq_div_iff (by positivity : (2:ℝ) * x * (x + 2) ≠ 0)]
  linear_combination h

/-- Cosine of the angle opposite the side of length `x + 2`, by the law of cosines. -/
lemma cosC_val (T : Affine.Triangle ℝ Plane) {x : ℝ} (hx : 0 < x)
    (h01 : dist (T.points 0) (T.points 1) = x + 2)
    (h12 : dist (T.points 1) (T.points 2) = x)
    (h20 : dist (T.points 2) (T.points 0) = x + 1) :
    Real.cos (∠ (T.points 0) (T.points 2) (T.points 1)) = (x - 3) / (2 * x) := by
  have h := law_cos (T.points 0) (T.points 2) (T.points 1)
  rw [h01, dist_comm (T.points 0) (T.points 2), h20, h12] at h
  rw [eq_div_iff (by positivity : (2:ℝ) * x ≠ 0)]
  have h2 : (x + 1) *
      (Real.cos (∠ (T.points 0) (T.points 2) (T.points 1)) * (2 * x) - (x - 3)) = 0 := by
    linear_combination h
  exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left (by positivity))

/-- Forward direction: a triangle with the required properties has sides `4, 5, 6`. -/
lemma forward (n : ℕ) (T : Affine.Triangle ℝ Plane)
    (h01 : dist (T.points 0) (T.points 1) = (n : ℝ) + 2)
    (h12 : dist (T.points 1) (T.points 2) = (n : ℝ))
    (h20 : dist (T.points 2) (T.points 0) = (n : ℝ) + 1)
    (hdbl : Doubling T) : n = 4 := by
  set x : ℝ := (n : ℝ) with hx_def
  have hcol : ¬Collinear ℝ ({T.points 0, T.points 1, T.points 2} : Set Plane) :=
    (affineIndependent_iff_not_collinear_of_ne (p := T.points) (by decide : (0 : Fin 3) ≠ 1)
      (by decide : (0 : Fin 3) ≠ 2) (by decide : (1 : Fin 3) ≠ 2)).mp T.independent
  have hcol102 : ¬Collinear ℝ ({T.points 1, T.points 0, T.points 2} : Set Plane) := nc12 hcol
  have hcol021 : ¬Collinear ℝ ({T.points 0, T.points 2, T.points 1} : Set Plane) := nc23 hcol
  have hcol210 : ¬Collinear ℝ ({T.points 2, T.points 1, T.points 0} : Set Plane) :=
    nc12 (nc23 (nc12 hcol))
  have hx : 0 < x := by
    rw [← h12]
    exact dist_pos.mpr (ne₂₃_of_not_collinear hcol)
  -- The strict triangle inequality forces `n ≥ 2`.
  have htri : x + 2 < (x + 1) + x := by
    have h1 : dist (T.points 0) (T.points 1) <
        dist (T.points 0) (T.points 2) + dist (T.points 2) (T.points 1) := by
      rw [dist_lt_dist_add_dist_iff]
      intro hw
      exact hcol021 hw.collinear
    rw [h01, dist_comm (T.points 0) (T.points 2), h20,
      dist_comm (T.points 2) (T.points 1), h12] at h1
    linarith
  have hn2 : 2 ≤ n := by
    have h1x : (1 : ℝ) < x := by linarith
    rw [hx_def] at h1x
    have h1n : 1 < n := by exact_mod_cast h1x
    omega
  have hx2 : (2 : ℝ) ≤ x := by rw [hx_def]; exact_mod_cast hn2
  have hcosA := cosA_val T hx h01 h12 h20
  have hcosB := cosB_val T hx h01 h12 h20
  have hcosC := cosC_val T hx h01 h12 h20
  -- Non-squared polynomial relations for the three cosines.
  have relA : Real.cos (∠ (T.points 1) (T.points 0) (T.points 2)) * (2 * (x + 2)) = x + 5 := by
    rw [hcosA, div_mul_cancel₀ _ (by positivity : (2:ℝ) * (x + 2) ≠ 0)]
  have relB : Real.cos (∠ (T.points 0) (T.points 1) (T.points 2)) * (2 * x * (x + 2)) =
      x ^ 2 + 2 * x + 3 := by
    rw [hcosB, div_mul_cancel₀ _ (by positivity : (2:ℝ) * x * (x + 2) ≠ 0)]
  have relC : Real.cos (∠ (T.points 0) (T.points 2) (T.points 1)) * (2 * x) = x - 3 := by
    rw [hcosC, div_mul_cancel₀ _ (by positivity : (2:ℝ) * x ≠ 0)]
  have relAsq : (Real.cos (∠ (T.points 1) (T.points 0) (T.points 2)) * (2 * (x + 2))) ^ 2 =
      (x + 5) ^ 2 := by rw [relA]
  have relBsq : (Real.cos (∠ (T.points 0) (T.points 1) (T.points 2)) * (2 * x * (x + 2))) ^ 2 =
      (x ^ 2 + 2 * x + 3) ^ 2 := by rw [relB]
  -- The three angles are positive and strictly increasing (larger side, larger angle).
  have hApos : 0 < ∠ (T.points 1) (T.points 0) (T.points 2) := angle_pos_of_not_collinear hcol102
  have hBpos : 0 < ∠ (T.points 0) (T.points 1) (T.points 2) := angle_pos_of_not_collinear hcol
  have hCpos : 0 < ∠ (T.points 0) (T.points 2) (T.points 1) := angle_pos_of_not_collinear hcol021
  have hAB : ∠ (T.points 1) (T.points 0) (T.points 2) < ∠ (T.points 0) (T.points 1) (T.points 2) := by
    have hd : dist (T.points 2) (T.points 1) < dist (T.points 2) (T.points 0) := by
      rw [dist_comm (T.points 2) (T.points 1), h12, h20]; linarith
    have h := (angle_lt_iff_dist_lt hcol210).mpr hd
    rwa [angle_comm (T.points 2) (T.points 0) (T.points 1),
      angle_comm (T.points 2) (T.points 1) (T.points 0)] at h
  have hBC : ∠ (T.points 0) (T.points 1) (T.points 2) < ∠ (T.points 0) (T.points 2) (T.points 1) := by
    have hd : dist (T.points 0) (T.points 2) < dist (T.points 0) (T.points 1) := by
      rw [dist_comm (T.points 0) (T.points 2), h20, h01]; linarith
    exact (angle_lt_iff_dist_lt hcol021).mpr hd
  rcases hdbl with hcase | hcase | hcase | hcase | hcase | hcase
  · -- `A = 2B` is impossible since `A < B`.
    exfalso; linarith
  · -- `A = 2C` is impossible since `A < C`.
    have hAC := lt_trans hAB hBC
    exfalso; linarith
  · -- `B = 2A` forces `n = 1`, contradicting `n ≥ 2`.
    exfalso
    have hcos : Real.cos (∠ (T.points 0) (T.points 1) (T.points 2)) =
        2 * Real.cos (∠ (T.points 1) (T.points 0) (T.points 2)) ^ 2 - 1 := by
      rw [hcase, Real.cos_two_mul]
    have key : (x ^ 2 + 2 * x + 3) * (2 * (x + 2)) ^ 2 =
        2 * (2 * x * (x + 2)) * (x + 5) ^ 2 - (2 * x * (x + 2)) * (2 * (x + 2)) ^ 2 := by
      linear_combination hcos * ((2 * x * (x + 2)) * (2 * (x + 2)) ^ 2) -
        relB * (2 * (x + 2)) ^ 2 + 2 * (2 * x * (x + 2)) * relAsq
    have hfact : (x - 1) ^ 2 * (x + 3) * (x + 2) = 0 := by linear_combination key / 8
    rcases mul_eq_zero.mp hfact with h1 | h2
    · rcases mul_eq_zero.mp h1 with h11 | h13
      · have hx1 : x = 1 := by
          have h0 := (pow_eq_zero_iff (show (2 : ℕ) ≠ 0 by norm_num)).mp h11
          linarith
        linarith
      · linarith
    · linarith
  · -- `B = 2C` is impossible since `B < C`.
    exfalso; linarith
  · -- `C = 2A` forces `n = 4`.
    have hcos : Real.cos (∠ (T.points 0) (T.points 2) (T.points 1)) =
        2 * Real.cos (∠ (T.points 1) (T.points 0) (T.points 2)) ^ 2 - 1 := by
      rw [hcase, Real.cos_two_mul]
    have key : (x - 3) * (2 * (x + 2)) ^ 2 =
        2 * (2 * x) * (x + 5) ^ 2 - (2 * x) * (2 * (x + 2)) ^ 2 := by
      linear_combination hcos * ((2 * x) * (2 * (x + 2)) ^ 2) -
        relC * (2 * (x + 2)) ^ 2 + 2 * (2 * x) * relAsq
    have hfact : (x - 4) * (2 * x ^ 2 + 7 * x + 3) = 0 := by linear_combination key / 4
    rcases mul_eq_zero.mp hfact with h4 | hq
    · have hx4 : x = 4 := by linarith
      rw [hx_def] at hx4
      exact_mod_cast hx4
    · exfalso
      nlinarith [hx2, hq]
  · -- `C = 2B` has no solution with `n ≥ 2`.
    exfalso
    have hcos : Real.cos (∠ (T.points 0) (T.points 2) (T.points 1)) =
        2 * Real.cos (∠ (T.points 0) (T.points 1) (T.points 2)) ^ 2 - 1 := by
      rw [hcase, Real.cos_two_mul]
    have key : (x - 3) * (2 * x * (x + 2)) ^ 2 =
        2 * (2 * x) * (x ^ 2 + 2 * x + 3) ^ 2 - (2 * x) * (2 * x * (x + 2)) ^ 2 := by
      linear_combination hcos * ((2 * x) * (2 * x * (x + 2)) ^ 2) -
        relC * (2 * x * (x + 2)) ^ 2 + 2 * (2 * x) * relBsq
    have hfact : x * ((x ^ 2 - x - 3) * (2 * x ^ 2 + 7 * x + 3)) = 0 := by
      linear_combination key / 4
    rcases mul_eq_zero.mp hfact with hx0 | hq
    · linarith
    · rcases mul_eq_zero.mp hq with hq1 | hq2
      · rcases (show n = 2 ∨ 3 ≤ n from by omega) with hn2eq | hn3
        · subst hn2eq
          rw [hx_def] at hq1
          norm_num at hq1
        · have hx3 : (3 : ℝ) ≤ x := by rw [hx_def]; exact_mod_cast hn3
          nlinarith [hx3, hq1]
      · nlinarith [hx2, hq2]

noncomputable def tri0 : Plane := !₂[0, 0]
noncomputable def tri1 : Plane := !₂[6, 0]
noncomputable def tri2 : Plane := !₂[15 / 4, 5 * Real.sqrt 7 / 4]

lemma dist_lit (a b c d : ℝ) :
    dist (!₂[a, b] : Plane) (!₂[c, d]) = Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) := by
  rw [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp [Real.norm_eq_abs, sq_abs]

lemma hs7 : (Real.sqrt 7) ^ 2 = 7 := Real.sq_sqrt (by norm_num)

lemma d01 : dist tri0 tri1 = 6 := by
  simp only [tri0, tri1]
  rw [dist_lit, show ((0 : ℝ) - 6) ^ 2 + (0 - 0) ^ 2 = 6 ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

lemma d20 : dist tri2 tri0 = 5 := by
  simp only [tri2, tri0]
  rw [dist_lit, show (15 / 4 - 0 : ℝ) ^ 2 + (5 * Real.sqrt 7 / 4 - 0) ^ 2 = 5 ^ 2 by
    linear_combination (25 / 16) * hs7]
  exact Real.sqrt_sq (by norm_num)

lemma d12 : dist tri1 tri2 = 4 := by
  simp only [tri1, tri2]
  rw [dist_lit, show (6 - 15 / 4 : ℝ) ^ 2 + (0 - 5 * Real.sqrt 7 / 4) ^ 2 = 4 ^ 2 by
    linear_combination (25 / 16) * hs7]
  exact Real.sqrt_sq (by norm_num)

lemma smul_vadd_apply (r : ℝ) (v w : Plane) (i : Fin 2) :
    (r • v +ᵥ w) i = r * v i + w i := by
  simp [vadd_eq_add, smul_eq_mul]

lemma hindep : AffineIndependent ℝ ![tri0, tri1, tri2] := by
  rw [affineIndependent_iff_not_collinear_set]
  intro hcoll
  rw [collinear_iff_of_mem (show tri0 ∈ ({tri0, tri1, tri2} : Set Plane) by simp)] at hcoll
  obtain ⟨v, hv⟩ := hcoll
  obtain ⟨r1, hr1⟩ := hv tri1 (by simp)
  obtain ⟨r2, hr2⟩ := hv tri2 (by simp)
  have e1x : r1 * v 0 = 6 := by
    have h1 : tri1 0 = (r1 • v +ᵥ tri0) 0 := by rw [hr1]
    rw [smul_vadd_apply] at h1
    have h2 : tri1 0 = 6 := by simp [tri1]
    have h3 : tri0 0 = 0 := by simp [tri0]
    rw [h2, h3, add_zero] at h1
    exact h1.symm
  have e1y : r1 * v 1 = 0 := by
    have h1 : tri1 1 = (r1 • v +ᵥ tri0) 1 := by rw [hr1]
    rw [smul_vadd_apply] at h1
    have h2 : tri1 1 = 0 := by simp [tri1]
    have h3 : tri0 1 = 0 := by simp [tri0]
    rw [h2, h3, add_zero] at h1
    exact h1.symm
  have e2y : r2 * v 1 = 5 * Real.sqrt 7 / 4 := by
    have h2 : tri2 1 = (r2 • v +ᵥ tri0) 1 := by rw [hr2]
    rw [smul_vadd_apply] at h2
    have h4 : tri2 1 = 5 * Real.sqrt 7 / 4 := by simp [tri2]
    have h3 : tri0 1 = 0 := by simp [tri0]
    rw [h4, h3, add_zero] at h2
    exact h2.symm
  have hr1ne : r1 ≠ 0 := by
    intro h
    rw [h, zero_mul] at e1x
    norm_num at e1x
  have hv1 : v 1 = 0 := (mul_eq_zero.mp e1y).resolve_left hr1ne
  rw [hv1, mul_zero] at e2y
  have hpos : (0 : ℝ) < 5 * Real.sqrt 7 / 4 := by
    have h7 := Real.sqrt_pos.mpr (show (0 : ℝ) < 7 by norm_num)
    positivity
  linarith

/-- The triangle with side lengths `4, 5, 6`. -/
noncomputable def tri456 : Affine.Triangle ℝ Plane := ⟨![tri0, tri1, tri2], hindep⟩

lemma tri456_p0 : tri456.points 0 = tri0 := rfl
lemma tri456_p1 : tri456.points 1 = tri1 := rfl
lemma tri456_p2 : tri456.points 2 = tri2 := rfl

/-- In the `4, 5, 6` triangle, the largest angle is twice the smallest one. -/
lemma angle_C_eq_two_mul_angle_A : ∠ tri0 tri2 tri1 = 2 * ∠ tri1 tri0 tri2 := by
  have hcosA : Real.cos (∠ tri1 tri0 tri2) = 3 / 4 := by
    have h := law_cos tri1 tri0 tri2
    rw [d12, dist_comm tri1 tri0, d01, d20] at h
    linear_combination h / 60
  have hcosC : Real.cos (∠ tri0 tri2 tri1) = 1 / 8 := by
    have h := law_cos tri0 tri2 tri1
    rw [d01, dist_comm tri0 tri2, d20, d12] at h
    linear_combination h / 40
  have hAle : ∠ tri1 tri0 tri2 ≤ Real.pi / 2 := by
    by_contra! hlt
    have hle : ∠ tri1 tri0 tri2 ≤ Real.pi + Real.pi / 2 := by
      have h := angle_le_pi tri1 tri0 tri2
      linarith [Real.pi_pos]
    have hcosle := Real.cos_nonpos_of_pi_div_two_le_of_le hlt.le hle
    rw [hcosA] at hcosle
    norm_num at hcosle
  have hmem1 : ∠ tri0 tri2 tri1 ∈ Set.Icc 0 Real.pi := ⟨angle_nonneg _ _ _, angle_le_pi _ _ _⟩
  have hmem2 : 2 * ∠ tri1 tri0 tri2 ∈ Set.Icc 0 Real.pi := by
    have h0 := angle_nonneg tri1 tri0 tri2
    constructor <;> linarith
  have hcos : Real.cos (∠ tri0 tri2 tri1) = Real.cos (2 * ∠ tri1 tri0 tri2) := by
    rw [Real.cos_two_mul, hcosA, hcosC]
    norm_num
  exact Real.injOn_cos hmem1 hmem2 hcos

/-- Backward direction: the `4, 5, 6` triangle has the required properties. -/
lemma tri456_witness :
    ∃ T : Affine.Triangle ℝ Plane,
      dist (T.points 0) (T.points 1) = (4 : ℝ) + 2 ∧
      dist (T.points 1) (T.points 2) = (4 : ℝ) ∧
      dist (T.points 2) (T.points 0) = (4 : ℝ) + 1 ∧
      Doubling T := by
  refine ⟨tri456, ?_, ?_, ?_, ?_⟩
  · rw [tri456_p0, tri456_p1]
    norm_num [d01]
  · rw [tri456_p1, tri456_p2]
    norm_num [d12]
  · rw [tri456_p2, tri456_p0]
    norm_num [d20]
  · unfold Doubling
    rw [tri456_p0, tri456_p1, tri456_p2]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl angle_C_eq_two_mul_angle_A))))

snip end

determine solution_set : Set ℕ := { 4 }

problem imo1968_p1 (n : ℕ) :
    n ∈ solution_set ↔
    ∃ T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)),
      dist (T.points 0) (T.points 1) = (n : ℝ) + 2 ∧
      dist (T.points 1) (T.points 2) = (n : ℝ) ∧
      dist (T.points 2) (T.points 0) = (n : ℝ) + 1 ∧
      Doubling T := by
  constructor
  · intro hn
    rw [Set.mem_singleton_iff] at hn
    subst hn
    exact tri456_witness
  · rintro ⟨T, h01, h12, h20, hdbl⟩
    rw [Set.mem_singleton_iff]
    exact forward n T h01 h12 h20 hdbl

end Imo1968P1
