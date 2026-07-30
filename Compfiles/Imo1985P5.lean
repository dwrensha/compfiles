/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Geometry.Euclidean.Sphere.Basic
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1985, Problem 5

A circle center O passes through the vertices A and C of the triangle ABC and
intersects the segments AB and BC again at distinct points K and N respectively.
The circumcircles of ABC and KBN intersect at exactly two distinct points B
and M. Prove that angle OMB is a right angle.
-/

namespace Imo1985P5

open EuclideanGeometry

open scoped EuclideanGeometry Real RealInnerProductSpace

snip begin

/-- Coordinate formula for the squared distance in the Euclidean plane. -/
lemma dist_sq (x y : EuclideanSpace ℝ (Fin 2)) :
    dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [PiLp.dist_sq_eq_of_L2, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]

/-- Coordinate formula for the inner product in the Euclidean plane. -/
lemma realInner_eq (x y : EuclideanSpace ℝ (Fin 2)) :
    ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  ring

/-- A small division computation used in the cross-product lemma below. -/
lemma div_mul_cancel' {u₁ u₂ v₁ v₂ : ℝ} (hu : u₁ ≠ 0) (h : u₁ * v₂ = u₂ * v₁) :
    v₁ / u₁ * u₂ = v₂ := by
  field_simp [hu]
  linear_combination -h

/-- If three points of the Euclidean plane are not collinear, then the cross
product of the two side vectors (twice the signed area) is nonzero. -/
lemma cross_ne_zero_of_not_collinear {P₁ P₂ P₃ : EuclideanSpace ℝ (Fin 2)}
    (h : ¬ Collinear ℝ ({P₁, P₂, P₃} : Set (EuclideanSpace ℝ (Fin 2)))) :
    (P₂ 0 - P₁ 0) * (P₃ 1 - P₁ 1) - (P₂ 1 - P₁ 1) * (P₃ 0 - P₁ 0) ≠ 0 := by
  intro hc
  apply h
  rw [collinear_iff_of_mem (show P₁ ∈ ({P₁, P₂, P₃} : Set (EuclideanSpace ℝ (Fin 2))) by simp)]
  by_cases h12 : P₂ = P₁
  · refine ⟨P₃ - P₁, fun p hp => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with h | h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨0, by simp [h, h12]⟩
    · exact ⟨1, by simp [h]⟩
  · have hne : (P₂ 0 - P₁ 0) ≠ 0 ∨ (P₂ 1 - P₁ 1) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply h12
      apply PiLp.ext
      rw [Fin.forall_fin_two]
      exact ⟨sub_eq_zero.mp hcon.1, sub_eq_zero.mp hcon.2⟩
    rcases hne with h0 | h1
    · refine ⟨P₂ - P₁, fun p hp => ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with h | h | h
      · exact ⟨0, by simp [h]⟩
      · exact ⟨1, by simp [h]⟩
      · refine ⟨(P₃ 0 - P₁ 0) / (P₂ 0 - P₁ 0), ?_⟩
        rw [h]
        apply PiLp.ext
        rw [Fin.forall_fin_two]
        constructor
        · simp only [vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
          have key : (P₃ 0 - P₁ 0) / (P₂ 0 - P₁ 0) * (P₂ 0 - P₁ 0) = P₃ 0 - P₁ 0 :=
            div_mul_cancel' h0 rfl
          rw [key]
          ring
        · simp only [vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
          have key : (P₃ 0 - P₁ 0) / (P₂ 0 - P₁ 0) * (P₂ 1 - P₁ 1) = P₃ 1 - P₁ 1 :=
            div_mul_cancel' h0 (by linear_combination hc)
          rw [key]
          ring
    · refine ⟨P₂ - P₁, fun p hp => ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with h | h | h
      · exact ⟨0, by simp [h]⟩
      · exact ⟨1, by simp [h]⟩
      · refine ⟨(P₃ 1 - P₁ 1) / (P₂ 1 - P₁ 1), ?_⟩
        rw [h]
        apply PiLp.ext
        rw [Fin.forall_fin_two]
        constructor
        · simp only [vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
          have key : (P₃ 1 - P₁ 1) / (P₂ 1 - P₁ 1) * (P₂ 0 - P₁ 0) = P₃ 0 - P₁ 0 :=
            div_mul_cancel' h1 (by linear_combination -hc)
          rw [key]
          ring
        · simp only [vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
          have key : (P₃ 1 - P₁ 1) / (P₂ 1 - P₁ 1) * (P₂ 1 - P₁ 1) = P₃ 1 - P₁ 1 :=
            div_mul_cancel' h1 rfl
          rw [key]
          ring

/-- The algebraic core of the problem.  Work in coordinates relative to the
center `O` of the given circle: `a`, `c`, `k`, `n` lie on the circle of squared
radius `a₁² + a₂²` centered at the origin; `k` lies on line `ab`, `n` lies on
line `cb`; `g` is a common center of the circle through `a, b, c, m` and `h` a
common center of the circle through `k, b, n, m`.  The conclusion is the
orthogonality relation `m · (b - m) = 0`.

The key step of the proof is to show that the two centers satisfy
`h = b - g`: both vectors satisfy the two linear equations
`2 x · (k - b) = |a|² - |b|²` and `2 x · (n - b) = |a|² - |b|²`, and these
equations determine a unique vector since `k - b` and `n - b` are linearly
independent (the cross product hypothesis).  The orthogonality then follows
from `2 (h - g) · (m - b) = 0` (the common chord is perpendicular to the line
of centers). -/
lemma algebra_core
    (a₁ a₂ b₁ b₂ c₁ c₂ k₁ k₂ n₁ n₂ m₁ m₂ g₁ g₂ h₁ h₂ r₁ r₂ s t : ℝ)
    (H1 : a₁ ^ 2 + a₂ ^ 2 = c₁ ^ 2 + c₂ ^ 2)
    (H2 : a₁ ^ 2 + a₂ ^ 2 = k₁ ^ 2 + k₂ ^ 2)
    (H3 : a₁ ^ 2 + a₂ ^ 2 = n₁ ^ 2 + n₂ ^ 2)
    (H4 : k₁ = a₁ + s * (b₁ - a₁))
    (H5 : k₂ = a₂ + s * (b₂ - a₂))
    (H6 : n₁ = c₁ + t * (b₁ - c₁))
    (H7 : n₂ = c₂ + t * (b₂ - c₂))
    (H8 : (g₁ - a₁) ^ 2 + (g₂ - a₂) ^ 2 = r₁ ^ 2)
    (H9 : (g₁ - b₁) ^ 2 + (g₂ - b₂) ^ 2 = r₁ ^ 2)
    (H10 : (g₁ - c₁) ^ 2 + (g₂ - c₂) ^ 2 = r₁ ^ 2)
    (H11 : (g₁ - m₁) ^ 2 + (g₂ - m₂) ^ 2 = r₁ ^ 2)
    (H12 : (h₁ - k₁) ^ 2 + (h₂ - k₂) ^ 2 = r₂ ^ 2)
    (H13 : (h₁ - b₁) ^ 2 + (h₂ - b₂) ^ 2 = r₂ ^ 2)
    (H14 : (h₁ - n₁) ^ 2 + (h₂ - n₂) ^ 2 = r₂ ^ 2)
    (H15 : (h₁ - m₁) ^ 2 + (h₂ - m₂) ^ 2 = r₂ ^ 2)
    (hs0 : s ≠ 0) (ht0 : t ≠ 0)
    (hcross : (k₁ - b₁) * (n₂ - b₂) - (k₂ - b₂) * (n₁ - b₁) ≠ 0) :
    m₁ * (b₁ - m₁) + m₂ * (b₂ - m₂) = 0 := by
  -- The second intersection relations: since `k ≠ a`, the parameter `s` is
  -- determined by `2 a·(b - a) + s |b - a|² = 0`.
  have sX : s * (2 * (a₁ * (b₁ - a₁) + a₂ * (b₂ - a₂))
      + s * ((b₁ - a₁) ^ 2 + (b₂ - a₂) ^ 2)) = 0 := by
    linear_combination -H2 - (k₁ + a₁ + s * (b₁ - a₁)) * H4
      - (k₂ + a₂ + s * (b₂ - a₂)) * H5
  have E_a : 2 * (a₁ * (b₁ - a₁) + a₂ * (b₂ - a₂))
      + s * ((b₁ - a₁) ^ 2 + (b₂ - a₂) ^ 2) = 0 := by
    rcases mul_eq_zero.mp sX with h | h
    · exact absurd h hs0
    · exact h
  have tY : t * (2 * (c₁ * (b₁ - c₁) + c₂ * (b₂ - c₂))
      + t * ((b₁ - c₁) ^ 2 + (b₂ - c₂) ^ 2)) = 0 := by
    linear_combination H1 - H3 - (n₁ + c₁ + t * (b₁ - c₁)) * H6
      - (n₂ + c₂ + t * (b₂ - c₂)) * H7
  have E_c : 2 * (c₁ * (b₁ - c₁) + c₂ * (b₂ - c₂))
      + t * ((b₁ - c₁) ^ 2 + (b₂ - c₂) ^ 2) = 0 := by
    rcases mul_eq_zero.mp tY with h | h
    · exact absurd h ht0
    · exact h
  -- The circumcenter equations.
  have E_g1 : 2 * (g₁ * (a₁ - b₁) + g₂ * (a₂ - b₂))
      = (a₁ ^ 2 + a₂ ^ 2) - (b₁ ^ 2 + b₂ ^ 2) := by
    linear_combination H9 - H8
  have E_g2 : 2 * (g₁ * (c₁ - b₁) + g₂ * (c₂ - b₂))
      = (c₁ ^ 2 + c₂ ^ 2) - (b₁ ^ 2 + b₂ ^ 2) := by
    linear_combination H9 - H10
  have E_h1 : 2 * (h₁ * (k₁ - b₁) + h₂ * (k₂ - b₂))
      = (k₁ ^ 2 + k₂ ^ 2) - (b₁ ^ 2 + b₂ ^ 2) := by
    linear_combination H13 - H12
  have E_h2 : 2 * (h₁ * (n₁ - b₁) + h₂ * (n₂ - b₂))
      = (n₁ ^ 2 + n₂ ^ 2) - (b₁ ^ 2 + b₂ ^ 2) := by
    linear_combination H13 - H14
  -- The vector `b - g` also satisfies the two linear equations defining `h`.
  have E_hk : 2 * ((b₁ - g₁) * (k₁ - b₁) + (b₂ - g₂) * (k₂ - b₂))
      = (a₁ ^ 2 + a₂ ^ 2) - (b₁ ^ 2 + b₂ ^ 2) := by
    linear_combination 2 * (b₁ - g₁) * H4 + 2 * (b₂ - g₂) * H5 + E_a + (s - 1) * E_g1
  have E_hn : 2 * ((b₁ - g₁) * (n₁ - b₁) + (b₂ - g₂) * (n₂ - b₂))
      = (a₁ ^ 2 + a₂ ^ 2) - (b₁ ^ 2 + b₂ ^ 2) := by
    linear_combination 2 * (b₁ - g₁) * H6 + 2 * (b₂ - g₂) * H7 + E_c + (t - 1) * E_g2 - H1
  -- Hence `d := h - (b - g)` is orthogonal to both `k - b` and `n - b`.
  have Eq1 : (h₁ - (b₁ - g₁)) * (k₁ - b₁) + (h₂ - (b₂ - g₂)) * (k₂ - b₂) = 0 := by
    linear_combination (1 / 2) * E_h1 - (1 / 2) * H2 - (1 / 2) * E_hk
  have Eq2 : (h₁ - (b₁ - g₁)) * (n₁ - b₁) + (h₂ - (b₂ - g₂)) * (n₂ - b₂) = 0 := by
    linear_combination (1 / 2) * E_h2 - (1 / 2) * H3 - (1 / 2) * E_hn
  -- Since `k - b` and `n - b` are linearly independent, `d = 0`.
  have hd1c : (h₁ - (b₁ - g₁)) * ((k₁ - b₁) * (n₂ - b₂) - (k₂ - b₂) * (n₁ - b₁)) = 0 := by
    linear_combination (n₂ - b₂) * Eq1 - (k₂ - b₂) * Eq2
  have hd1 : h₁ - (b₁ - g₁) = 0 := by
    rcases mul_eq_zero.mp hd1c with h | h
    · exact h
    · exact absurd h hcross
  have hd2c : (h₂ - (b₂ - g₂)) * ((k₁ - b₁) * (n₂ - b₂) - (k₂ - b₂) * (n₁ - b₁)) = 0 := by
    linear_combination (k₁ - b₁) * Eq2 - (n₁ - b₁) * Eq1
  have hd2 : h₂ - (b₂ - g₂) = 0 := by
    rcases mul_eq_zero.mp hd2c with h | h
    · exact h
    · exact absurd h hcross
  -- The common chord `mb` is perpendicular to the line of centers `h - g`.
  have E_gm : 2 * (g₁ * (m₁ - b₁) + g₂ * (m₂ - b₂))
      = (m₁ ^ 2 + m₂ ^ 2) - (b₁ ^ 2 + b₂ ^ 2) := by
    linear_combination H9 - H11
  have E_hm : 2 * (h₁ * (m₁ - b₁) + h₂ * (m₂ - b₂))
      = (m₁ ^ 2 + m₂ ^ 2) - (b₁ ^ 2 + b₂ ^ 2) := by
    linear_combination H13 - H15
  have E_sub : 2 * ((h₁ - g₁) * (m₁ - b₁) + (h₂ - g₂) * (m₂ - b₂)) = 0 := by
    linear_combination E_hm - E_gm
  -- Substituting `h = b - g` gives the desired orthogonality.
  linear_combination E_gm + (1 / 2) * E_sub - (m₁ - b₁) * hd1 - (m₂ - b₂) * hd2

snip end

problem imo1985_p5
    (O A B C K N M : EuclideanSpace ℝ (Fin 2))
    (hOC : dist O A = dist O C) (hOK : dist O A = dist O K) (hON : dist O A = dist O N)
    (hKseg : K ∈ segment ℝ A B) (hNseg : N ∈ segment ℝ B C)
    (hKA : K ≠ A) (hNC : N ≠ C) (_hKN : K ≠ N)
    (_hABC : ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))))
    (hKBN : ¬ Collinear ℝ ({K, B, N} : Set (EuclideanSpace ℝ (Fin 2))))
    (hcyc : Cospherical ({A, B, C, M} : Set (EuclideanSpace ℝ (Fin 2))))
    (hcyc' : Cospherical ({K, B, N, M} : Set (EuclideanSpace ℝ (Fin 2))))
    (_hMB : M ≠ B) :
    ∠ O M B = π / 2 := by
  rw [EuclideanGeometry.angle, ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two,
    realInner_eq]
  show (O 0 - M 0) * (B 0 - M 0) + (O 1 - M 1) * (B 1 - M 1) = 0
  -- Unpack the segment hypotheses.
  obtain ⟨a₀, b₀, _, _, hab, hKeq⟩ := hKseg
  obtain ⟨c₀, d₀, _, _, hcd, hNeq⟩ := hNseg
  have hKc : ∀ i : Fin 2, a₀ * A i + b₀ * B i = K i := by
    intro i
    have h : (a₀ • A + b₀ • B) i = K i := by rw [hKeq]
    simpa [PiLp.add_apply, PiLp.smul_apply] using h
  have hNc : ∀ i : Fin 2, c₀ * B i + d₀ * C i = N i := by
    intro i
    have h : (c₀ • B + d₀ • C) i = N i := by rw [hNeq]
    simpa [PiLp.add_apply, PiLp.smul_apply] using h
  -- The second intersection points are genuine: the parameters are nonzero.
  have hs0 : b₀ ≠ 0 := by
    intro hb
    apply hKA
    rw [← hKeq, hb]
    have ha : a₀ = 1 := by linarith
    rw [ha]
    simp
  have ht0 : c₀ ≠ 0 := by
    intro hc0
    apply hNC
    rw [← hNeq, hc0]
    have hd : d₀ = 1 := by linarith
    rw [hd]
    simp
  -- Unpack the two circumcircles.
  obtain ⟨G, R, hR⟩ := hcyc
  obtain ⟨G', R', hR'⟩ := hcyc'
  have hRA : dist A G = R := hR A (by simp)
  have hRB : dist B G = R := hR B (by simp)
  have hRC : dist C G = R := hR C (by simp)
  have hRM : dist M G = R := hR M (by simp)
  have hK' : dist K G' = R' := hR' K (by simp)
  have hB' : dist B G' = R' := hR' B (by simp)
  have hN' : dist N G' = R' := hR' N (by simp)
  have hM' : dist M G' = R' := hR' M (by simp)
  -- Non-collinearity gives a nonzero cross product.
  have hset : ({K, B, N} : Set (EuclideanSpace ℝ (Fin 2)))
      = ({B, K, N} : Set (EuclideanSpace ℝ (Fin 2))) := by
    ext x
    simp
    tauto
  have hcross := cross_ne_zero_of_not_collinear (P₁ := B) (P₂ := K) (P₃ := N)
    (by rwa [hset] at hKBN)
  have hcross' : ((K 0 - O 0) - (B 0 - O 0)) * ((N 1 - O 1) - (B 1 - O 1))
      - ((K 1 - O 1) - (B 1 - O 1)) * ((N 0 - O 0) - (B 0 - O 0)) ≠ 0 := by
    intro hcon
    apply hcross
    linear_combination hcon
  -- Coordinate versions of all the metric hypotheses.
  have H1 : (A 0 - O 0) ^ 2 + (A 1 - O 1) ^ 2 = (C 0 - O 0) ^ 2 + (C 1 - O 1) ^ 2 := by
    have h2 : dist O A ^ 2 = dist O C ^ 2 := by rw [hOC]
    rw [dist_sq, dist_sq] at h2
    linear_combination h2
  have H2 : (A 0 - O 0) ^ 2 + (A 1 - O 1) ^ 2 = (K 0 - O 0) ^ 2 + (K 1 - O 1) ^ 2 := by
    have h2 : dist O A ^ 2 = dist O K ^ 2 := by rw [hOK]
    rw [dist_sq, dist_sq] at h2
    linear_combination h2
  have H3 : (A 0 - O 0) ^ 2 + (A 1 - O 1) ^ 2 = (N 0 - O 0) ^ 2 + (N 1 - O 1) ^ 2 := by
    have h2 : dist O A ^ 2 = dist O N ^ 2 := by rw [hON]
    rw [dist_sq, dist_sq] at h2
    linear_combination h2
  have H4 : (K 0 - O 0) = (A 0 - O 0) + b₀ * ((B 0 - O 0) - (A 0 - O 0)) := by
    linear_combination -hKc 0 + A 0 * hab
  have H5 : (K 1 - O 1) = (A 1 - O 1) + b₀ * ((B 1 - O 1) - (A 1 - O 1)) := by
    linear_combination -hKc 1 + A 1 * hab
  have H6 : (N 0 - O 0) = (C 0 - O 0) + c₀ * ((B 0 - O 0) - (C 0 - O 0)) := by
    linear_combination -hNc 0 + C 0 * hcd
  have H7 : (N 1 - O 1) = (C 1 - O 1) + c₀ * ((B 1 - O 1) - (C 1 - O 1)) := by
    linear_combination -hNc 1 + C 1 * hcd
  have H8 : ((G 0 - O 0) - (A 0 - O 0)) ^ 2 + ((G 1 - O 1) - (A 1 - O 1)) ^ 2 = R ^ 2 := by
    have h2 : dist A G ^ 2 = R ^ 2 := by rw [hRA]
    rw [dist_sq] at h2
    linear_combination h2
  have H9 : ((G 0 - O 0) - (B 0 - O 0)) ^ 2 + ((G 1 - O 1) - (B 1 - O 1)) ^ 2 = R ^ 2 := by
    have h2 : dist B G ^ 2 = R ^ 2 := by rw [hRB]
    rw [dist_sq] at h2
    linear_combination h2
  have H10 : ((G 0 - O 0) - (C 0 - O 0)) ^ 2 + ((G 1 - O 1) - (C 1 - O 1)) ^ 2 = R ^ 2 := by
    have h2 : dist C G ^ 2 = R ^ 2 := by rw [hRC]
    rw [dist_sq] at h2
    linear_combination h2
  have H11 : ((G 0 - O 0) - (M 0 - O 0)) ^ 2 + ((G 1 - O 1) - (M 1 - O 1)) ^ 2 = R ^ 2 := by
    have h2 : dist M G ^ 2 = R ^ 2 := by rw [hRM]
    rw [dist_sq] at h2
    linear_combination h2
  have H12 : ((G' 0 - O 0) - (K 0 - O 0)) ^ 2 + ((G' 1 - O 1) - (K 1 - O 1)) ^ 2
      = R' ^ 2 := by
    have h2 : dist K G' ^ 2 = R' ^ 2 := by rw [hK']
    rw [dist_sq] at h2
    linear_combination h2
  have H13 : ((G' 0 - O 0) - (B 0 - O 0)) ^ 2 + ((G' 1 - O 1) - (B 1 - O 1)) ^ 2
      = R' ^ 2 := by
    have h2 : dist B G' ^ 2 = R' ^ 2 := by rw [hB']
    rw [dist_sq] at h2
    linear_combination h2
  have H14 : ((G' 0 - O 0) - (N 0 - O 0)) ^ 2 + ((G' 1 - O 1) - (N 1 - O 1)) ^ 2
      = R' ^ 2 := by
    have h2 : dist N G' ^ 2 = R' ^ 2 := by rw [hN']
    rw [dist_sq] at h2
    linear_combination h2
  have H15 : ((G' 0 - O 0) - (M 0 - O 0)) ^ 2 + ((G' 1 - O 1) - (M 1 - O 1)) ^ 2
      = R' ^ 2 := by
    have h2 : dist M G' ^ 2 = R' ^ 2 := by rw [hM']
    rw [dist_sq] at h2
    linear_combination h2
  -- Apply the algebraic core.
  have hcore := algebra_core
    (a₁ := A 0 - O 0) (a₂ := A 1 - O 1) (b₁ := B 0 - O 0) (b₂ := B 1 - O 1)
    (c₁ := C 0 - O 0) (c₂ := C 1 - O 1) (k₁ := K 0 - O 0) (k₂ := K 1 - O 1)
    (n₁ := N 0 - O 0) (n₂ := N 1 - O 1) (m₁ := M 0 - O 0) (m₂ := M 1 - O 1)
    (g₁ := G 0 - O 0) (g₂ := G 1 - O 1) (h₁ := G' 0 - O 0) (h₂ := G' 1 - O 1)
    (r₁ := R) (r₂ := R') (s := b₀) (t := c₀)
    H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 hs0 ht0 hcross'
  linear_combination -hcore

end Imo1985P5
