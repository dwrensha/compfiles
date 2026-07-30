/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Geometry.Euclidean.Triangle
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1974, Problem 2

Let $ABC$ be a triangle. Prove that there is a point $D$ on the side $AB$
such that $CD$ is the geometric mean of $AD$ and $DB$ if and only if

$$\sin A \sin B \leq \sin^2 \frac{C}{2}.$$
-/

open scoped EuclideanGeometry

namespace Imo1974P2

snip begin

/-- Pure trigonometric core of the problem: for the angles `A B C` of a
triangle, the discriminant of the cevian quadratic is nonnegative if and only
if `sin A * sin B ≤ sin (C/2)^2`. The key algebraic identity is
`(2 sin B cos A + sin C)² - 8 sin² B = 1 - (3 sin A sin B - cos A cos B)²`,
and the second factor `1 + 3 sin A sin B - cos A cos B` is always positive. -/
theorem trig_core {A B C : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hsum : A + B + C = Real.pi) :
    0 ≤ (2 * Real.sin B * Real.cos A + Real.sin C) ^ 2 - 8 * Real.sin B ^ 2 ↔
      Real.sin A * Real.sin B ≤ Real.sin (C / 2) ^ 2 := by
  have hABpi : A + B = Real.pi - C := by linarith
  have hsinC : Real.sin C = Real.sin (A + B) := by rw [hABpi, Real.sin_pi_sub]
  have hcosC : Real.cos C = -Real.cos (A + B) := by
    rw [hABpi, Real.cos_pi_sub, neg_neg]
  have hsq : Real.sin (C / 2) ^ 2 = (1 - Real.cos C) / 2 := by
    have h1 := Real.abs_sin_half C
    rw [← sq_abs, h1, Real.sq_sqrt (by nlinarith [Real.cos_le_one C])]
  have key : (2 * Real.sin B * Real.cos A + Real.sin C) ^ 2 - 8 * Real.sin B ^ 2
      = 1 - (3 * Real.sin A * Real.sin B - Real.cos A * Real.cos B) ^ 2 := by
    rw [hsinC, Real.sin_add]
    linear_combination (Real.sin_sq_add_cos_sq A) *
      (9 * Real.sin B ^ 2 + Real.cos B ^ 2) + Real.sin_sq_add_cos_sq B
  have hub : -1 ≤ 3 * Real.sin A * Real.sin B - Real.cos A * Real.cos B := by
    have hform : 3 * Real.sin A * Real.sin B - Real.cos A * Real.cos B =
        Real.cos (A - B) + 2 * Real.cos C := by
      rw [Real.cos_sub, hcosC, Real.cos_add]; ring
    rw [hform]
    have hlt : Real.cos (A + B) < Real.cos (A - B) := by
      rcases le_total A B with hle | hle
      · rw [show A - B = -(B - A) by ring, Real.cos_neg]
        exact Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
      · exact Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
    have hCle : -1 < Real.cos C := by
      have hCpi : C < Real.pi := by linarith
      have h2 := Real.cos_lt_cos_of_nonneg_of_le_pi hC.le (le_refl Real.pi) hCpi
      rwa [Real.cos_pi] at h2
    linarith [hlt, hcosC, hCle]
  rw [key, hsq, hcosC, Real.cos_add]
  constructor
  · intro h
    have hu1 : 3 * Real.sin A * Real.sin B - Real.cos A * Real.cos B ≤ 1 := by
      nlinarith [h, hub, sq_nonneg (3 * Real.sin A * Real.sin B - Real.cos A * Real.cos B)]
    linarith [hu1]
  · intro h
    have hu1 : 3 * Real.sin A * Real.sin B - Real.cos A * Real.cos B ≤ 1 := by
      linarith [h]
    have h2 : 0 ≤ (1 - (3 * Real.sin A * Real.sin B - Real.cos A * Real.cos B)) *
        (1 + (3 * Real.sin A * Real.sin B - Real.cos A * Real.cos B)) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [h2]

/-- Pure algebra: for `b c > 0` and `u ∈ (-1, 1)`, the quadratic
`2t² - (2bu + c)t + b²` has a root in `[0, c]` if and only if its discriminant
`(2bu + c)² - 8b²` is nonnegative. -/
theorem quad_root_iff {b c u : ℝ} (hb : 0 < b) (hc : 0 < c) (hu1 : -1 < u)
    (hu2 : u < 1) :
    (∃ t ∈ Set.Icc 0 c, 2 * t ^ 2 - (2 * b * u + c) * t + b ^ 2 = 0) ↔
      0 ≤ (2 * b * u + c) ^ 2 - 8 * b ^ 2 := by
  constructor
  · rintro ⟨t, -, ht⟩
    nlinarith [sq_nonneg (4 * t - (2 * b * u + c))]
  · intro hΔ
    have hKpos : 0 < 2 * b * u + c := by
      by_contra hle
      push Not at hle
      have h1 : -(2 * b * u + c) < 2 * b := by
        nlinarith [mul_pos (show (0 : ℝ) < 2 * b by positivity) (by linarith : (0 : ℝ) < u + 1)]
      have h2 : (2 * b * u + c) ^ 2 < 4 * b ^ 2 := by
        calc (2 * b * u + c) ^ 2 = (-(2 * b * u + c)) ^ 2 := by ring
          _ < (2 * b) ^ 2 := sq_lt_sq' (by linarith) h1
          _ = 4 * b ^ 2 := by ring
      nlinarith [hΔ, h2, hb]
    have hKlt : 2 * b * u + c < 4 * c := by
      by_contra hge
      push Not at hge
      have h1 : 2 * b * u < 2 * b := by
        have h11 := mul_neg_of_pos_of_neg (show (0 : ℝ) < 2 * b by positivity)
          (by linarith : u - 1 < 0)
        nlinarith
      have h2 : 2 * b * u + c < 2 * b + c := by linarith
      have h3 : 3 * c < 2 * b := by linarith
      nlinarith [hΔ, h2, h3, hge, hb, hc, sq_nonneg (2 * b - 3 * c),
        mul_pos (sub_pos.mpr h2) (by positivity : (0 : ℝ) < 2 * b + c + (2 * b * u + c)),
        mul_pos (sub_pos.mpr h3) hc, sq_nonneg c]
    set K := 2 * b * u + c with hK
    have hsq : Real.sqrt (K ^ 2 - 8 * b ^ 2) ^ 2 = K ^ 2 - 8 * b ^ 2 :=
      Real.sq_sqrt hΔ
    have hslt : Real.sqrt (K ^ 2 - 8 * b ^ 2) < K := by
      have h4 : Real.sqrt (K ^ 2 - 8 * b ^ 2) ^ 2 < K ^ 2 := by
        rw [hsq]; nlinarith [hb]
      by_contra hge2
      push Not at hge2
      have h5 : K ^ 2 ≤ Real.sqrt (K ^ 2 - 8 * b ^ 2) ^ 2 := by
        nlinarith [Real.sqrt_nonneg (K ^ 2 - 8 * b ^ 2), hge2, hKpos]
      nlinarith [h4, h5]
    refine ⟨(K - Real.sqrt (K ^ 2 - 8 * b ^ 2)) / 4, ⟨?_, ?_⟩, ?_⟩
    · have := Real.sqrt_nonneg (K ^ 2 - 8 * b ^ 2)
      positivity
    · have h5 : K - Real.sqrt (K ^ 2 - 8 * b ^ 2) < 4 * c := by
        linarith [hKlt, Real.sqrt_nonneg (K ^ 2 - 8 * b ^ 2)]
      linarith
    · linear_combination (1 / 8 : ℝ) * hsq

/-- Geometric reduction: a point `D` on `AB` with `CD² = AD · DB` exists if
and only if the quadratic `2t² - (2b cos A + c) t + b² = 0` (where `b = CA`,
`c = AB`, `t = AD`) has a root in `[0, c]`. -/
theorem exists_quad_root_iff {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (A B C : V) (h : ¬ Collinear ℝ ({A, B, C} : Set V)) :
    (∃ D ∈ segment ℝ A B, dist C D ^ 2 = dist A D * dist D B) ↔
      ∃ t ∈ Set.Icc 0 (dist A B),
        2 * t ^ 2 - (2 * dist C A * Real.cos (∠ C A B) + dist A B) * t +
          dist C A ^ 2 = 0 := by
  have hAB : A ≠ B := by
    intro he
    subst he
    rw [show ({A, A, C} : Set V) = {A, C} by ext w; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at h
    exact h (collinear_pair ℝ A C)
  have hCA : C ≠ A := by
    intro he
    subst he
    rw [show ({C, B, C} : Set V) = {B, C} by ext w; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at h
    exact h (collinear_pair ℝ B C)
  constructor
  · rintro ⟨D, hDseg, hDeq⟩
    obtain ⟨a₁, a₂, ha₁, ha₂, hsum12, hD⟩ := hDseg
    have ha₁eq : a₁ = 1 - a₂ := by linarith
    have hs1 : a₂ ≤ 1 := by linarith
    have hD' : D = (1 - a₂) • A + a₂ • B := by rw [← hD, ha₁eq]
    have hAD : dist A D = a₂ * dist A B := by
      rw [dist_eq_norm, hD']
      have h1 : A - ((1 - a₂) • A + a₂ • B) = a₂ • (A - B) := by module
      rw [h1, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha₂, dist_eq_norm]
    have hDB : dist D B = (1 - a₂) * dist A B := by
      rw [dist_eq_norm, hD']
      have h2 : (1 - a₂) • A + a₂ • B - B = (1 - a₂) • (A - B) := by module
      rw [h2, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith), dist_eq_norm]
    have hspos : 0 < a₂ := by
      rcases eq_or_lt_of_le ha₂ with h0 | h0
      · exfalso
        have hAD0 : dist A D = 0 := by rw [hAD, ← h0, zero_mul]
        have hCD0 : dist C D = 0 := by
          have h2 : dist C D ^ 2 = 0 := by rw [hDeq, hAD0, zero_mul]
          exact sq_eq_zero_iff.mp h2
        have hDA : D = A := by
          rw [← h0] at hD'
          simpa using hD'
        exact hCA ((dist_eq_zero.mp hCD0).trans hDA)
      · exact h0
    have hDminus : D -ᵥ A = a₂ • (B -ᵥ A) := by
      rw [vsub_eq_sub, vsub_eq_sub, hD']
      module
    have hang : ∠ C A D = ∠ C A B := by
      unfold EuclideanGeometry.angle
      rw [hDminus, InnerProductGeometry.angle_smul_right_of_pos _ _ hspos]
    have hloc := EuclideanGeometry.law_cos C A D
    rw [hang, dist_comm D A, hAD] at hloc
    have hDeq2 : dist C D * dist C D = (a₂ * dist A B) * ((1 - a₂) * dist A B) := by
      rw [← hDB, ← hAD, ← hDeq]; ring
    refine ⟨a₂ * dist A B, ⟨?_, ?_⟩, ?_⟩
    · exact mul_nonneg ha₂ dist_nonneg
    · exact mul_le_of_le_one_left dist_nonneg hs1
    · linear_combination hDeq2 - hloc
  · rintro ⟨t, ⟨ht0, htc⟩, ht⟩
    have htpos : 0 < t := by
      rcases eq_or_lt_of_le ht0 with h0 | h0
      · exfalso
        rw [← h0] at ht
        nlinarith [ht, dist_pos.mpr hCA]
      · exact h0
    have hcpos : 0 < dist A B := dist_pos.mpr hAB
    have hs : 0 < t / dist A B := div_pos htpos hcpos
    have hs1 : t / dist A B ≤ 1 := by rwa [div_le_one hcpos]
    set D' := (1 - t / dist A B) • A + (t / dist A B) • B with hD'
    refine ⟨D', ?_, ?_⟩
    · exact ⟨1 - t / dist A B, t / dist A B, by linarith, hs.le, by ring, hD'.symm⟩
    · have hsc : t / dist A B * dist A B = t := div_mul_cancel₀ t hcpos.ne'
      have hAD : dist A D' = t / dist A B * dist A B := by
        rw [dist_eq_norm, hD']
        have h1 : A - ((1 - t / dist A B) • A + (t / dist A B) • B)
            = (t / dist A B) • (A - B) := by module
        rw [h1, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.le, dist_eq_norm]
      have hDB : dist D' B = (1 - t / dist A B) * dist A B := by
        rw [dist_eq_norm, hD']
        have h2 : (1 - t / dist A B) • A + (t / dist A B) • B - B
            = (1 - t / dist A B) • (A - B) := by module
        rw [h2, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith), dist_eq_norm]
      have hDminus : D' -ᵥ A = (t / dist A B) • (B -ᵥ A) := by
        rw [vsub_eq_sub, vsub_eq_sub, hD']
        module
      have hang : ∠ C A D' = ∠ C A B := by
        unfold EuclideanGeometry.angle
        rw [hDminus, InnerProductGeometry.angle_smul_right_of_pos _ _ hs]
      have hloc := EuclideanGeometry.law_cos C A D'
      rw [hang, dist_comm D' A, hAD] at hloc
      rw [← hsc] at ht
      have key : dist C D' * dist C D'
          = (t / dist A B * dist A B) * ((1 - t / dist A B) * dist A B) := by
        linear_combination hloc + ht
      rw [pow_two, hAD, hDB]
      exact key

snip end

/-- **IMO 1974 Problem 2.** There is a point `D` on the side `AB` of the
triangle `ABC` with `CD` the geometric mean of `AD` and `DB` if and only if
`sin A * sin B ≤ sin (C/2)²`. -/
problem imo1974_p2 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (A B C : V) (h : ¬ Collinear ℝ ({A, B, C} : Set V)) :
    (∃ D ∈ segment ℝ A B, dist C D ^ 2 = dist A D * dist D B) ↔
      Real.sin (∠ C A B) * Real.sin (∠ A B C) ≤ Real.sin (∠ B C A / 2) ^ 2 := by
  have hAB : A ≠ B := by
    intro he
    subst he
    rw [show ({A, A, C} : Set V) = {A, C} by ext w; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at h
    exact h (collinear_pair ℝ A C)
  have hBC : B ≠ C := by
    intro he
    subst he
    rw [show ({A, B, B} : Set V) = {A, B} by ext w; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at h
    exact h (collinear_pair ℝ A B)
  have hCA : C ≠ A := by
    intro he
    subst he
    rw [show ({C, B, C} : Set V) = {B, C} by ext w; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at h
    exact h (collinear_pair ℝ B C)
  have hperm : ∀ x y z : V, ({x, y, z} : Set V) = {z, x, y} := fun x y z => by
    ext w; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have h1 : ¬ Collinear ℝ ({C, A, B} : Set V) := hperm A B C ▸ h
  have h2 : ¬ Collinear ℝ ({B, C, A} : Set V) := hperm C A B ▸ h1
  have hsA : 0 < Real.sin (∠ C A B) := EuclideanGeometry.sin_pos_of_not_collinear h1
  have hApos : 0 < ∠ C A B := EuclideanGeometry.angle_pos_of_not_collinear h1
  have hBpos : 0 < ∠ A B C := EuclideanGeometry.angle_pos_of_not_collinear h
  have hCpos : 0 < ∠ B C A := EuclideanGeometry.angle_pos_of_not_collinear h2
  have hsum : ∠ C A B + ∠ A B C + ∠ B C A = Real.pi :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi B hCA.symm
  have hls1 := EuclideanGeometry.law_sin A B C
  have hls2 := EuclideanGeometry.law_sin A C B
  rw [EuclideanGeometry.angle_comm A C B, EuclideanGeometry.angle_comm B A C,
    dist_comm C B, dist_comm B A] at hls2
  have hb_eq : dist C A = dist B C * Real.sin (∠ A B C) / Real.sin (∠ C A B) := by
    field_simp [hsA.ne']
    linarith [hls1]
  have hc_eq : dist A B = dist B C * Real.sin (∠ B C A) / Real.sin (∠ C A B) := by
    field_simp [hsA.ne']
    linarith [hls2]
  have hApi : ∠ C A B < Real.pi := by linarith [hBpos, hCpos, hsum]
  have hcos1 : -1 < Real.cos (∠ C A B) := by
    have h3 := Real.cos_lt_cos_of_nonneg_of_le_pi (EuclideanGeometry.angle_nonneg _ _ _)
      (le_refl Real.pi) hApi
    rwa [Real.cos_pi] at h3
  have hcos2 : Real.cos (∠ C A B) < 1 := by
    have h3 := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0)
      (EuclideanGeometry.angle_le_pi _ _ _) hApos
    rwa [Real.cos_zero] at h3
  calc (∃ D ∈ segment ℝ A B, dist C D ^ 2 = dist A D * dist D B)
      ↔ ∃ t ∈ Set.Icc 0 (dist A B),
          2 * t ^ 2 - (2 * dist C A * Real.cos (∠ C A B) + dist A B) * t +
            dist C A ^ 2 = 0 := exists_quad_root_iff A B C h
    _ ↔ 0 ≤ (2 * dist C A * Real.cos (∠ C A B) + dist A B) ^ 2 - 8 * dist C A ^ 2 :=
        quad_root_iff (dist_pos.mpr hCA) (dist_pos.mpr hAB) hcos1 hcos2
    _ ↔ 0 ≤ (2 * Real.sin (∠ A B C) * Real.cos (∠ C A B) + Real.sin (∠ B C A)) ^ 2 -
          8 * Real.sin (∠ A B C) ^ 2 := by
        have hfac : (2 * dist C A * Real.cos (∠ C A B) + dist A B) ^ 2 -
              8 * dist C A ^ 2
            = (dist B C / Real.sin (∠ C A B)) ^ 2 *
              ((2 * Real.sin (∠ A B C) * Real.cos (∠ C A B) + Real.sin (∠ B C A)) ^ 2 -
                8 * Real.sin (∠ A B C) ^ 2) := by
          rw [hb_eq, hc_eq]
          field_simp [hsA.ne']
        rw [hfac, mul_nonneg_iff_of_pos_left
          (sq_pos_of_ne_zero (div_ne_zero (dist_pos.mpr hBC).ne' hsA.ne'))]
    _ ↔ Real.sin (∠ C A B) * Real.sin (∠ A B C) ≤ Real.sin (∠ B C A / 2) ^ 2 :=
        trig_core hApos hBpos hCpos hsum

end Imo1974P2
