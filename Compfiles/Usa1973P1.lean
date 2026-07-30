/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 1973, Problem 1

Show that if two points lie inside a regular tetrahedron the angle they subtend
at a vertex is less than π/3.
-/

namespace Usa1973P1

open Real Classical
open scoped EuclideanGeometry RealInnerProductSpace

snip begin

/-- The norm of a difference of two points, from their distance. -/
theorem norm_sub_of_dist {E : Type*} [NormedAddCommGroup E] {V X : E} {s : ℝ}
    (h : dist V X = s) : ‖X - V‖ = s := by
  rw [← dist_eq_norm, dist_comm]
  exact h

/-- In a regular tetrahedron of edge length `s`, two edges `VX`, `VY` issued
from the same vertex `V` make an angle of `π/3`; equivalently their inner
product is `s ^ 2 / 2`. -/
theorem inner_sub_sub_of_dist_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {V X Y : E} {s : ℝ} (hVX : dist V X = s) (hVY : dist V Y = s) (hXY : dist X Y = s) :
    ⟪X - V, Y - V⟫ = s ^ 2 / 2 := by
  have h1 : ‖X - V‖ = s := norm_sub_of_dist hVX
  have h2 : ‖Y - V‖ = s := norm_sub_of_dist hVY
  have h3 : ‖X - V - (Y - V)‖ = s := by
    have e : X - V - (Y - V) = X - Y := by abel
    rw [e, ← dist_eq_norm]
    exact hXY
  have h4 := norm_sub_sq_real (X - V) (Y - V)
  rw [h1, h2, h3] at h4
  linarith

/-- Key step: in a real inner product space, let `u₁ u₂ u₃` be three vectors of
the same positive length `s` whose pairwise inner products are all `s ^ 2 / 2`
(like the three edges of a regular tetrahedron issued from one vertex). Then any
two vectors in the *interior* of the cone they generate (i.e. all coefficients
strictly positive) subtend an angle strictly less than `π/3`.

Indeed, writing `p = a₁ • u₁ + a₂ • u₂ + a₃ • u₃` and `q = b₁ • u₁ + b₂ • u₂ + b₃ • u₃`,
one computes
  `⟪p, q⟫ = s ^ 2 / 2 * ((a₁ + a₂ + a₃) * (b₁ + b₂ + b₃) + (a₁ * b₁ + a₂ * b₂ + a₃ * b₃))`,
while the triangle inequality gives `‖p‖ ≤ s * (a₁ + a₂ + a₃)` and similarly for `q`.
Since the `aᵢ`, `bᵢ` are positive, `⟪p, q⟫ > ‖p‖ * ‖q‖ / 2` follows, and `arccos`
being antitone turns this into `angle p q < π / 3`. -/
theorem cone_angle_lt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u₁ u₂ u₃ : E} {s : ℝ} (hs : 0 < s)
    (hu₁ : ‖u₁‖ = s) (hu₂ : ‖u₂‖ = s) (hu₃ : ‖u₃‖ = s)
    (h₁₂ : ⟪u₁, u₂⟫ = s ^ 2 / 2) (h₁₃ : ⟪u₁, u₃⟫ = s ^ 2 / 2)
    (h₂₃ : ⟪u₂, u₃⟫ = s ^ 2 / 2)
    {a₁ a₂ a₃ b₁ b₂ b₃ : ℝ}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (ha₃ : 0 < a₃)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hb₃ : 0 < b₃) :
    InnerProductGeometry.angle (a₁ • u₁ + a₂ • u₂ + a₃ • u₃)
      (b₁ • u₁ + b₂ • u₂ + b₃ • u₃) < π / 3 := by
  set p := a₁ • u₁ + a₂ • u₂ + a₃ • u₃ with hp
  set q := b₁ • u₁ + b₂ • u₂ + b₃ • u₃ with hq
  -- inner products of reversed pairs
  have h₂₁ : ⟪u₂, u₁⟫ = s ^ 2 / 2 := by rw [real_inner_comm]; exact h₁₂
  have h₃₁ : ⟪u₃, u₁⟫ = s ^ 2 / 2 := by rw [real_inner_comm]; exact h₁₃
  have h₃₂ : ⟪u₃, u₂⟫ = s ^ 2 / 2 := by rw [real_inner_comm]; exact h₂₃
  -- expand ⟪p, q⟫
  have hinner : ⟪p, q⟫ = s ^ 2 / 2 * ((a₁ + a₂ + a₃) * (b₁ + b₂ + b₃)
      + (a₁ * b₁ + a₂ * b₂ + a₃ * b₃)) := by
    rw [hp, hq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hu₁, hu₂, hu₃, h₁₂, h₁₃, h₂₃, h₂₁, h₃₁, h₃₂]
    ring
  -- norm of each term
  have hn₁ : ‖a₁ • u₁‖ = a₁ * s := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha₁, hu₁]
  have hn₂ : ‖a₂ • u₂‖ = a₂ * s := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha₂, hu₂]
  have hn₃ : ‖a₃ • u₃‖ = a₃ * s := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha₃, hu₃]
  have hm₁ : ‖b₁ • u₁‖ = b₁ * s := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hb₁, hu₁]
  have hm₂ : ‖b₂ • u₂‖ = b₂ * s := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hb₂, hu₂]
  have hm₃ : ‖b₃ • u₃‖ = b₃ * s := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hb₃, hu₃]
  -- triangle inequality for p and q
  have hnorm_p : ‖p‖ ≤ s * (a₁ + a₂ + a₃) := by
    have t1 := norm_add_le (a₁ • u₁ + a₂ • u₂) (a₃ • u₃)
    have t2 := norm_add_le (a₁ • u₁) (a₂ • u₂)
    rw [hp]
    linarith [hn₁, hn₂, hn₃]
  have hnorm_q : ‖q‖ ≤ s * (b₁ + b₂ + b₃) := by
    have t1 := norm_add_le (b₁ • u₁ + b₂ • u₂) (b₃ • u₃)
    have t2 := norm_add_le (b₁ • u₁) (b₂ • u₂)
    rw [hq]
    linarith [hm₁, hm₂, hm₃]
  -- positivity facts
  have hA : 0 < a₁ + a₂ + a₃ := by positivity
  have hB : 0 < b₁ + b₂ + b₃ := by positivity
  have hσ : 0 < a₁ * b₁ + a₂ * b₂ + a₃ * b₃ := by positivity
  have hs2 : 0 < s ^ 2 := by positivity
  -- the main inequality ⟪p, q⟫ > ‖p‖ * ‖q‖ / 2
  have hmain : ‖p‖ * ‖q‖ / 2 < ⟪p, q⟫ := by
    have hpq : ‖p‖ * ‖q‖ ≤ s * (a₁ + a₂ + a₃) * (s * (b₁ + b₂ + b₃)) :=
      mul_le_mul hnorm_p hnorm_q (norm_nonneg _) (by positivity)
    rw [hinner]
    nlinarith [hpq, hσ, hs2]
  have hinner_pos : 0 < ⟪p, q⟫ := lt_of_le_of_lt (by positivity) hmain
  have hp0 : p ≠ 0 := by
    intro h
    rw [h, inner_zero_left] at hinner_pos
    exact absurd hinner_pos (lt_irrefl 0)
  have hq0 : q ≠ 0 := by
    intro h
    rw [h, inner_zero_right] at hinner_pos
    exact absurd hinner_pos (lt_irrefl 0)
  have hnorm_pos : 0 < ‖p‖ * ‖q‖ := mul_pos (norm_pos_iff.mpr hp0) (norm_pos_iff.mpr hq0)
  -- 1/2 < cos < 1
  have hratio_gt : 1 / 2 < ⟪p, q⟫ / (‖p‖ * ‖q‖) := by
    rw [lt_div_iff₀ hnorm_pos]
    linarith [hmain]
  have hratio_le : ⟪p, q⟫ / (‖p‖ * ‖q‖) ≤ 1 := by
    rw [div_le_one hnorm_pos]
    have h := norm_inner_le_norm (𝕜 := ℝ) p q
    rwa [Real.norm_eq_abs, abs_of_pos hinner_pos] at h
  -- conclude via antitonicity of arccos
  have hcos : Real.arccos (1 / 2 : ℝ) = π / 3 := by
    rw [← Real.cos_pi_div_three]
    exact Real.arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  unfold InnerProductGeometry.angle
  calc Real.arccos (⟪p, q⟫ / (‖p‖ * ‖q‖)) < Real.arccos (1 / 2) :=
        Real.arccos_lt_arccos (by norm_num) hratio_gt hratio_le
    _ = π / 3 := hcos

snip end

problem usa1973_p1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A B C D P Q : E} {s : ℝ} (hs : 0 < s)
    (hAB : dist A B = s) (hAC : dist A C = s) (hAD : dist A D = s)
    (hBC : dist B C = s) (hBD : dist B D = s) (hCD : dist C D = s)
    {a b c d a' b' c' d' : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hsum : a + b + c + d = 1) (hP : P = a • A + b • B + c • C + d • D)
    (ha' : 0 < a') (hb' : 0 < b') (hc' : 0 < c') (hd' : 0 < d')
    (hsum' : a' + b' + c' + d' = 1) (hQ : Q = a' • A + b' • B + c' • C + d' • D) :
    ∀ V ∈ ({A, B, C, D} : Finset E), ∠ P V Q < π / 3 := by
  -- barycentric coordinates of P and Q relative to any base point
  have key : ∀ w : E, P - w = a • (A - w) + b • (B - w) + c • (C - w) + d • (D - w) := by
    intro w
    have e : a • (A - w) + b • (B - w) + c • (C - w) + d • (D - w)
        = a • A + b • B + c • C + d • D - (a + b + c + d) • w := by module
    rw [e, hsum, one_smul, ← hP]
  have key' : ∀ w : E, Q - w = a' • (A - w) + b' • (B - w) + c' • (C - w) + d' • (D - w) := by
    intro w
    have e : a' • (A - w) + b' • (B - w) + c' • (C - w) + d' • (D - w)
        = a' • A + b' • B + c' • C + d' • D - (a' + b' + c' + d') • w := by module
    rw [e, hsum', one_smul, ← hQ]
  -- symmetric versions of the distance hypotheses
  have hBA : dist B A = s := by rw [dist_comm]; exact hAB
  have hCA : dist C A = s := by rw [dist_comm]; exact hAC
  have hDA : dist D A = s := by rw [dist_comm]; exact hAD
  have hCB : dist C B = s := by rw [dist_comm]; exact hBC
  have hDB : dist D B = s := by rw [dist_comm]; exact hBD
  have hDC : dist D C = s := by rw [dist_comm]; exact hCD
  -- P, Q as positive combinations of the three edges at each vertex
  have hPA : P - A = b • (B - A) + c • (C - A) + d • (D - A) := by
    simp only [key, sub_self, smul_zero, zero_add]
  have hQA : Q - A = b' • (B - A) + c' • (C - A) + d' • (D - A) := by
    simp only [key', sub_self, smul_zero, zero_add]
  have hPB : P - B = a • (A - B) + c • (C - B) + d • (D - B) := by
    simp only [key, sub_self, smul_zero, add_zero]
  have hQB : Q - B = a' • (A - B) + c' • (C - B) + d' • (D - B) := by
    simp only [key', sub_self, smul_zero, add_zero]
  have hPC : P - C = a • (A - C) + b • (B - C) + d • (D - C) := by
    simp only [key, sub_self, smul_zero, add_zero]
  have hQC : Q - C = a' • (A - C) + b' • (B - C) + d' • (D - C) := by
    simp only [key', sub_self, smul_zero, add_zero]
  have hPD : P - D = a • (A - D) + b • (B - D) + c • (C - D) := by
    simp only [key, sub_self, smul_zero, add_zero]
  have hQD : Q - D = a' • (A - D) + b' • (B - D) + c' • (C - D) := by
    simp only [key', sub_self, smul_zero, add_zero]
  intro V hV
  simp only [Finset.mem_insert, Finset.mem_singleton] at hV
  rcases hV with rfl | rfl | rfl | rfl
  · simp only [EuclideanGeometry.angle, vsub_eq_sub]
    rw [hPA, hQA]
    exact cone_angle_lt hs (norm_sub_of_dist hAB) (norm_sub_of_dist hAC) (norm_sub_of_dist hAD)
      (inner_sub_sub_of_dist_eq hAB hAC hBC) (inner_sub_sub_of_dist_eq hAB hAD hBD)
      (inner_sub_sub_of_dist_eq hAC hAD hCD) hb hc hd hb' hc' hd'
  · simp only [EuclideanGeometry.angle, vsub_eq_sub]
    rw [hPB, hQB]
    exact cone_angle_lt hs (norm_sub_of_dist hBA) (norm_sub_of_dist hBC) (norm_sub_of_dist hBD)
      (inner_sub_sub_of_dist_eq hBA hBC hAC) (inner_sub_sub_of_dist_eq hBA hBD hAD)
      (inner_sub_sub_of_dist_eq hBC hBD hCD) ha hc hd ha' hc' hd'
  · simp only [EuclideanGeometry.angle, vsub_eq_sub]
    rw [hPC, hQC]
    exact cone_angle_lt hs (norm_sub_of_dist hCA) (norm_sub_of_dist hCB) (norm_sub_of_dist hCD)
      (inner_sub_sub_of_dist_eq hCA hCB hAB) (inner_sub_sub_of_dist_eq hCA hCD hAD)
      (inner_sub_sub_of_dist_eq hCB hCD hBD) ha hb hd ha' hb' hd'
  · simp only [EuclideanGeometry.angle, vsub_eq_sub]
    rw [hPD, hQD]
    exact cone_angle_lt hs (norm_sub_of_dist hDA) (norm_sub_of_dist hDB) (norm_sub_of_dist hDC)
      (inner_sub_sub_of_dist_eq hDA hDB hAB) (inner_sub_sub_of_dist_eq hDA hDC hAC)
      (inner_sub_sub_of_dist_eq hDB hDC hBC) ha hb hc ha' hb' hc'

end Usa1973P1
