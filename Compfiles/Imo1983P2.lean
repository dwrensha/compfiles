/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.LinearAlgebra.AffineSpace.Midpoint
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Geometry]
}

/-!
# International Mathematical Olympiad 1983, Problem 2

Let A be one of the two distinct points of intersection of two unequal
coplanar circles C1 and C2 with centers O1 and O2 respectively. One of the
common tangents to the circles touches C1 at P1 and C2 at P2, while the
other touches C1 at Q1 and C2 at Q2. Let M1 be the midpoint of P1Q1 and
M2 the midpoint of P2Q2. Prove that ∠O1AO2 = ∠M1AM2.
-/

namespace Imo1983P2

open scoped EuclideanGeometry RealInnerProductSpace

/-- The Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

snip begin

/-- Extensionality for points of the plane, by coordinates. -/
theorem Pt.ext {x y : Pt} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  apply WithLp.ofLp_injective (p := 2)
  funext i
  fin_cases i <;> assumption

/-- The inner product of two plane vectors, in coordinates. -/
theorem inner_pt (n x : Pt) : ⟪n, x⟫ = n 0 * x 0 + n 1 * x 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, RCLike.inner_apply]
  simp only [conj_trivial]
  ring

/-- The squared distance between two points, as an inner product. -/
lemma inner_self_eq_sq_of_dist {x y : Pt} {r : ℝ} (h : dist x y = r) :
    ⟪x - y, x - y⟫ = r ^ 2 := by
  rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, h]

/-- In the plane, two vectors `d` and `s` that are both perpendicular to the
same nonzero vector `w` must be parallel; the coefficient is the usual
projection coefficient of `s` onto `d`.  This is where the "coplanar"
hypothesis of the problem is used. -/
lemma eq_smul_of_inner_eq_zero {w d s : Pt} (hw : w ≠ 0) (hd : d ≠ 0)
    (hwd : ⟪w, d⟫ = 0) (hws : ⟪w, s⟫ = 0) :
    s = (⟪s, d⟫ / ⟪d, d⟫) • d := by
  simp only [inner_pt] at hwd hws ⊢
  have hw' : w 0 * w 0 + w 1 * w 1 ≠ 0 := by
    have h := mt (inner_self_eq_zero (𝕜 := ℝ)).mp hw
    rwa [inner_pt] at h
  have hd' : d 0 * d 0 + d 1 * d 1 ≠ 0 := by
    have h := mt (inner_self_eq_zero (𝕜 := ℝ)).mp hd
    rwa [inner_pt] at h
  have hdet0 : (d 0 * s 1 - d 1 * s 0) * w 0 = 0 := by
    linear_combination s 1 * hwd - d 1 * hws
  have hdet1 : (d 0 * s 1 - d 1 * s 0) * w 1 = 0 := by
    linear_combination -s 0 * hwd + d 0 * hws
  have hdet : d 0 * s 1 - d 1 * s 0 = 0 := by
    have h : (d 0 * s 1 - d 1 * s 0) * (w 0 * w 0 + w 1 * w 1) = 0 := by
      linear_combination w 0 * hdet0 + w 1 * hdet1
    exact (mul_eq_zero.mp h).resolve_right hw'
  refine Pt.ext ?_ ?_
  · simp only [PiLp.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div, eq_div_iff hd']
    linear_combination -d 1 * hdet
  · simp only [PiLp.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div, eq_div_iff hd']
    linear_combination d 0 * hdet

/-- Expansion of `⟪x - d, x - d⟫`. -/
lemma inner_sub_sub (x d : Pt) : ⟪x - d, x - d⟫ = ⟪x, x⟫ - 2 * ⟪x, d⟫ + ⟪d, d⟫ := by
  rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_comm d x]
  ring

/-- Expansion of `⟪x - c • d, x - c • d⟫`. -/
lemma inner_sub_smul_sub (x d : Pt) (c : ℝ) :
    ⟪x - c • d, x - c • d⟫ = ⟪x, x⟫ - 2 * c * ⟪x, d⟫ + c ^ 2 * ⟪d, d⟫ := by
  rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_smul_left,
    inner_smul_right, real_inner_smul_left, inner_smul_right, real_inner_comm d x]
  ring

/-- Expansion of `⟪c₁ • d - a, c₂ • d - a⟫`. -/
lemma inner_smul_sub_smul_sub (c₁ c₂ : ℝ) (d a : Pt) :
    ⟪c₁ • d - a, c₂ • d - a⟫ = c₁ * c₂ * ⟪d, d⟫ - (c₁ + c₂) * ⟪a, d⟫ + ⟪a, a⟫ := by
  rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_smul_left,
    real_inner_smul_left, inner_smul_right, inner_smul_right, real_inner_comm d a]
  ring

snip end

problem imo1983_p2
    (r₁ r₂ : ℝ) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hrr : r₁ ≠ r₂)
    (O₁ O₂ A X P₁ P₂ Q₁ Q₂ M₁ M₂ : Pt)
    (hA₁ : dist A O₁ = r₁) (hA₂ : dist A O₂ = r₂)
    (hX₁ : dist X O₁ = r₁) (hX₂ : dist X O₂ = r₂) (hXA : X ≠ A)
    (hP₁ : dist P₁ O₁ = r₁) (hP₂ : dist P₂ O₂ = r₂)
    (hPt : ⟪P₁ - O₁, P₂ - P₁⟫ = 0) (hPt₂ : ⟪P₂ - O₂, P₂ - P₁⟫ = 0)
    (hPpar : ∃ k : ℝ, 0 < k ∧ P₂ - O₂ = k • (P₁ - O₁))
    (hQ₁ : dist Q₁ O₁ = r₁) (hQ₂ : dist Q₂ O₂ = r₂)
    (hQt : ⟪Q₁ - O₁, Q₂ - Q₁⟫ = 0) (hQt₂ : ⟪Q₂ - O₂, Q₂ - Q₁⟫ = 0)
    (hQpar : ∃ k : ℝ, 0 < k ∧ Q₂ - O₂ = k • (Q₁ - O₁))
    (hP₁Q₁ : P₁ ≠ Q₁)
    (hM₁ : M₁ = midpoint ℝ P₁ Q₁) (hM₂ : M₂ = midpoint ℝ P₂ Q₂) :
    ∠ O₁ A O₂ = ∠ M₁ A M₂ := by
  -- The two centers are distinct: otherwise the two radii, both equal to the
  -- distance from the center to `A`, would coincide.
  have hO : O₁ ≠ O₂ := by
    intro h
    subst h
    exact hrr (hA₁.symm.trans hA₂)
  set d := O₂ - O₁ with hd_def
  have hd : d ≠ 0 := sub_ne_zero.mpr (Ne.symm hO)
  set D := ⟪d, d⟫ with hDd
  have hD : 0 < D := by
    rw [hDd, real_inner_self_eq_norm_sq]
    exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hd)
  have hD0 : D ≠ 0 := hD.ne'
  set a := A - O₁ with ha_def
  set u := P₁ - O₁ with hu_def
  set u' := Q₁ - O₁ with hu'_def
  have ha : ⟪a, a⟫ = r₁ ^ 2 := inner_self_eq_sq_of_dist hA₁
  have hu : ⟪u, u⟫ = r₁ ^ 2 := inner_self_eq_sq_of_dist hP₁
  have hu' : ⟪u', u'⟫ = r₁ ^ 2 := inner_self_eq_sq_of_dist hQ₁
  -- For any point on both circles, its inner product with `d` is determined.
  have inner_d_of_dist : ∀ p : Pt, dist p O₁ = r₁ → dist p O₂ = r₂ →
      ⟪p - O₁, d⟫ = (r₁ ^ 2 + D - r₂ ^ 2) / 2 := by
    intro p hp1 hp2
    have e1 : ⟪p - O₁, p - O₁⟫ = r₁ ^ 2 := inner_self_eq_sq_of_dist hp1
    have e2 : ⟪(p - O₁) - d, (p - O₁) - d⟫ = r₂ ^ 2 := by
      have h := inner_self_eq_sq_of_dist hp2
      rwa [show p - O₂ = (p - O₁) - d from by rw [hd_def]; abel] at h
    set x := p - O₁
    rw [inner_sub_sub, e1, ← hDd] at e2
    linarith
  have hK : ⟪a, d⟫ = (r₁ ^ 2 + D - r₂ ^ 2) / 2 := inner_d_of_dist A hA₁ hA₂
  -- `A` does not lie on the line `O₁O₂`: otherwise the two intersection
  -- points of the circles would coincide (the circles would be tangent).
  have hAoff : ∀ t : ℝ, a ≠ t • d := by
    intro t hat
    set x := X - O₁ with hx_def
    have hx1 : ⟪x, x⟫ = r₁ ^ 2 := inner_self_eq_sq_of_dist hX₁
    have hxd : ⟪x, d⟫ = (r₁ ^ 2 + D - r₂ ^ 2) / 2 := inner_d_of_dist X hX₁ hX₂
    have hat1 : ⟪a, d⟫ = t * D := by rw [hat, real_inner_smul_left, hDd]
    have hat2 : r₁ ^ 2 = t ^ 2 * D := by
      have haa : ⟪a, a⟫ = t ^ 2 * D := by
        rw [hat, real_inner_smul_left, inner_smul_right, hDd]; ring
      rwa [ha] at haa
    have hxt : ⟪x - t • d, x - t • d⟫ = 0 := by
      rw [inner_sub_smul_sub, hx1, hxd, ← hDd]
      have e1 : t * D = (r₁ ^ 2 + D - r₂ ^ 2) / 2 := hat1.symm.trans hK
      linear_combination hat2 + 2 * t * e1
    have hXeq : x = t • d := sub_eq_zero.mp ((inner_self_eq_zero (𝕜 := ℝ)).mp hxt)
    have hXeq' : X - O₁ = t • d := by rw [← hx_def]; exact hXeq
    have hXeqA : X - O₁ = A - O₁ := by rw [hXeq', ← hat, ha_def]
    exact hXA (sub_left_inj.mp hXeqA)
  -- The tangent data: the radii to the two touching points are parallel.
  obtain ⟨k, hk0, hP2k⟩ := hPpar
  obtain ⟨k₂, hk₂0, hQ2k₂⟩ := hQpar
  -- Taking norms, the ratio is `r₂ / r₁`.
  have hkr : k * r₁ = r₂ := by
    have h1 : ⟪P₂ - O₂, P₂ - O₂⟫ = r₂ ^ 2 := inner_self_eq_sq_of_dist hP₂
    rw [hP2k, real_inner_smul_left, inner_smul_right, hu] at h1
    have h2 : (k * r₁) ^ 2 = r₂ ^ 2 := by linear_combination h1
    exact (sq_eq_sq₀ (mul_nonneg hk0.le hr₁.le) hr₂.le).mp h2
  have hk₂k : k₂ = k := by
    have hk₂r : k₂ * r₁ = r₂ := by
      have h1 : ⟪Q₂ - O₂, Q₂ - O₂⟫ = r₂ ^ 2 := inner_self_eq_sq_of_dist hQ₂
      rw [hQ2k₂, real_inner_smul_left, inner_smul_right, hu'] at h1
      have h2 : (k₂ * r₁) ^ 2 = r₂ ^ 2 := by linear_combination h1
      exact (sq_eq_sq₀ (mul_nonneg hk₂0.le hr₁.le) hr₂.le).mp h2
    exact mul_right_cancel₀ hr₁.ne' (hk₂r.trans hkr.symm)
  subst k₂
  -- Perpendicularity of the radius and the tangent line determines `⟪u, d⟫`.
  have hP2P1 : P₂ - P₁ = d + (k - 1) • u := by
    have e1 : P₂ = O₂ + k • u := (sub_eq_iff_eq_add.mp hP2k).trans (add_comm _ _)
    have e2 : P₁ = O₁ + u := by rw [hu_def]; abel
    rw [e1, e2, hd_def]
    module
  have hud : ⟪u, d⟫ = r₁ * (r₁ - r₂) := by
    have hperp := hPt
    rw [hP2P1, inner_add_right, inner_smul_right, hu] at hperp
    linear_combination hperp - r₁ * hkr
  have hQ2Q1 : Q₂ - Q₁ = d + (k - 1) • u' := by
    have e1 : Q₂ = O₂ + k • u' := (sub_eq_iff_eq_add.mp hQ2k₂).trans (add_comm _ _)
    have e2 : Q₁ = O₁ + u' := by rw [hu'_def]; abel
    rw [e1, e2, hd_def]
    module
  have hu'd : ⟪u', d⟫ = r₁ * (r₁ - r₂) := by
    have hperp := hQt
    rw [hQ2Q1, inner_add_right, inner_smul_right, hu'] at hperp
    linear_combination hperp - r₁ * hkr
  -- The two touching points `P₁, Q₁` are mirror images about the line `O₁O₂`,
  -- so `u + u'` is parallel to `d` (the genuinely two-dimensional step).
  have huu' : u - u' ≠ 0 := by
    have h : u - u' = P₁ - Q₁ := by rw [hu_def, hu'_def]; abel
    rw [h]
    exact sub_ne_zero.mpr hP₁Q₁
  have hwd : ⟪u - u', d⟫ = 0 := by
    rw [inner_sub_left, hud, hu'd, sub_self]
  have hws : ⟪u - u', u + u'⟫ = 0 := by
    rw [inner_sub_left, inner_add_right, inner_add_right, real_inner_comm u' u, hu, hu']
    ring
  have hsd : ⟪u + u', d⟫ = 2 * (r₁ * (r₁ - r₂)) := by
    rw [inner_add_left, hud, hu'd]; ring
  have hsum : u + u' = (2 * (r₁ * (r₁ - r₂)) / D) • d := by
    have h := eq_smul_of_inner_eq_zero huu' hd hwd hws
    rwa [hsd, ← hDd] at h
  have hmsum : (1/2 : ℝ) • (u + u') = (r₁ * (r₁ - r₂) / D) • d := by
    rw [hsum, smul_smul]
    congr 1
    field_simp [hD0]
  -- The midpoints: `M₁ - O₁ = (r₁(r₁-r₂)/D) • d` and
  -- `M₂ - O₂ = (r₂(r₁-r₂)/D) • d`; in particular both lie on line `O₁O₂`.
  have hM1eq : M₁ - O₁ = (r₁ * (r₁ - r₂) / D) • d := by
    have g1 : M₁ - P₁ = (1/2 : ℝ) • (Q₁ - P₁) := by
      rw [hM₁, midpoint_sub_left, invOf_eq_inv, ← one_div]
    have g2 : Q₁ - P₁ = u' - u := by rw [hu'_def, hu_def]; abel
    have g3 : M₁ - O₁ = (1/2 : ℝ) • (u + u') := by
      have e : M₁ - O₁ = (M₁ - P₁) + u := by rw [hu_def]; abel
      rw [e, g1, g2]
      module
    exact g3.trans hmsum
  have hM2eq : M₂ - O₂ = (r₂ * (r₁ - r₂) / D) • d := by
    have g1 : M₂ - P₂ = (1/2 : ℝ) • (Q₂ - P₂) := by
      rw [hM₂, midpoint_sub_left, invOf_eq_inv, ← one_div]
    have g3 : M₂ - O₂ = (1/2 : ℝ) • ((P₂ - O₂) + (Q₂ - O₂)) := by
      have e : M₂ - O₂ = (M₂ - P₂) + (P₂ - O₂) := by abel
      rw [e, g1]
      have g2 : Q₂ - P₂ = (Q₂ - O₂) - (P₂ - O₂) := by abel
      rw [g2]
      module
    rw [g3, hP2k, hQ2k₂, ← smul_add, smul_smul (1/2 : ℝ) k, mul_comm (1/2 : ℝ) k,
      ← smul_smul, hmsum, smul_smul]
    congr 1
    rw [← mul_div_assoc]
    congr 1
    linear_combination (r₁ - r₂) * hkr
  -- Vectors from `A` to the midpoints.
  have hM1A : M₁ - A = (r₁ * (r₁ - r₂) / D) • d - a := by
    have e : M₁ - A = (M₁ - O₁) - a := by rw [ha_def]; abel
    rw [e, hM1eq]
  have hM2A : M₂ - A = (1 + r₂ * (r₁ - r₂) / D) • d - a := by
    have e : M₂ - A = (M₂ - O₂) + d - a := by rw [hd_def, ha_def]; abel
    have e2 : (r₂ * (r₁ - r₂) / D) • d + d = (1 + r₂ * (r₁ - r₂) / D) • d := by
      module
    rw [e, hM2eq, e2]
  have hM1Ane : M₁ - A ≠ 0 := by
    rw [hM1A]
    intro h
    exact hAoff _ (sub_eq_zero.mp h).symm
  -- The triangle `AM₁M₂` is isosceles: `AM₁ = AM₂`.
  have hSq1 : ⟪M₁ - A, M₁ - A⟫ =
      (r₁ * (r₁ - r₂) / D) ^ 2 * D - 2 * (r₁ * (r₁ - r₂) / D) * ⟪a, d⟫ + r₁ ^ 2 := by
    rw [hM1A, inner_smul_sub_smul_sub, ha, ← hDd]
    ring
  have hSq2 : ⟪M₂ - A, M₂ - A⟫ =
      (1 + r₂ * (r₁ - r₂) / D) ^ 2 * D - 2 * (1 + r₂ * (r₁ - r₂) / D) * ⟪a, d⟫ + r₁ ^ 2 := by
    rw [hM2A, inner_smul_sub_smul_sub, ha, ← hDd]
    ring
  have hAM1AM2 : ⟪M₁ - A, M₁ - A⟫ = ⟪M₂ - A, M₂ - A⟫ := by
    rw [hSq1, hSq2, hK]
    field_simp [hD0]
    ring
  have hAM : ‖M₁ - A‖ = ‖M₂ - A‖ := by
    have h1 : ‖M₁ - A‖ ^ 2 = ‖M₂ - A‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq (M₁ - A), ← real_inner_self_eq_norm_sq (M₂ - A)]
      exact hAM1AM2
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h1
  -- Both angles have the same cosine, hence they are equal.
  have hnumO : ⟪O₁ - A, O₂ - A⟫ = r₁ ^ 2 - ⟪a, d⟫ := by
    have e1 : O₁ - A = -a := by rw [ha_def]; abel
    have e2 : O₂ - A = d - a := by rw [hd_def, ha_def]; abel
    rw [e1, e2, inner_neg_left, inner_sub_right, ha]
    ring
  have hnumM : ⟪M₁ - A, M₂ - A⟫ =
      (r₁ * (r₁ - r₂) / D) * (1 + r₂ * (r₁ - r₂) / D) * D -
        ((r₁ * (r₁ - r₂) / D) + (1 + r₂ * (r₁ - r₂) / D)) * ⟪a, d⟫ + r₁ ^ 2 := by
    rw [hM1A, hM2A, inner_smul_sub_smul_sub, ha, ← hDd]
  have hnormO1 : ‖O₁ - A‖ = r₁ := by rw [norm_sub_rev, ← dist_eq_norm, hA₁]
  have hnormO2 : ‖O₂ - A‖ = r₂ := by rw [norm_sub_rev, ← dist_eq_norm, hA₂]
  have hSpos : 0 < ⟪M₁ - A, M₁ - A⟫ := by
    rw [real_inner_self_eq_norm_sq]
    exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hM1Ane)
  have hprod : ‖M₁ - A‖ * ‖M₂ - A‖ = ⟪M₁ - A, M₁ - A⟫ := by
    rw [← hAM, ← sq]
    exact (real_inner_self_eq_norm_sq (M₁ - A)).symm
  rw [EuclideanGeometry.angle, EuclideanGeometry.angle]
  simp only [vsub_eq_sub]
  simp only [InnerProductGeometry.angle]
  congr 1
  rw [hnormO1, hnormO2, hprod, hnumO, hnumM,
    div_eq_div_iff (mul_ne_zero hr₁.ne' hr₂.ne') hSpos.ne', hSq1, hK]
  field_simp [hD0]
  ring

end Imo1983P2
