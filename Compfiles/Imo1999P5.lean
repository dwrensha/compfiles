/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1999, Problem 5

The circles C₁ and C₂ lie inside the circle C, and are tangent to it at M and
N, respectively. C₁ passes through the center of C₂. The common chord of C₁ and
C₂, when extended, meets C at A and B. The lines MA and MB meet C₁ again at E
and F. Prove that the line EF is tangent to C₂.
-/

namespace Imo1999P5

open scoped RealInnerProductSpace

snip begin

/-- In the Euclidean plane, two vectors that are both orthogonal to the same
nonzero vector are parallel (with the first one nonzero). This is the only
genuinely two-dimensional step of the argument. -/
lemma exists_smul_of_inner_eq_zero {x y q : EuclideanSpace ℝ (Fin 2)}
    (hq : q ≠ 0) (hx : x ≠ 0) (hxq : ⟪x, q⟫ = 0) (hyq : ⟪y, q⟫ = 0) :
    ∃ t : ℝ, y = t • x := by
  have ic : ∀ u v : EuclideanSpace ℝ (Fin 2), ⟪u, v⟫ = u 0 * v 0 + u 1 * v 1 :=
    fun u v => by
      simp only [PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply]
  have nsq : ∀ u : EuclideanSpace ℝ (Fin 2), ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 :=
    fun u => by
      simp only [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  have e1 : x 0 * q 0 + x 1 * q 1 = 0 := by rw [← ic x q]; exact hxq
  have e2 : y 0 * q 0 + y 1 * q 1 = 0 := by rw [← ic y q]; exact hyq
  have hq2 : q 0 ^ 2 + q 1 ^ 2 ≠ 0 := by
    rw [← nsq q]; exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hq)
  have hx2 : x 0 ^ 2 + x 1 ^ 2 ≠ 0 := by
    rw [← nsq x]; exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  -- the cross product `x × q` is nonzero (Lagrange's identity)
  have hc : x 0 * q 1 - x 1 * q 0 ≠ 0 := by
    intro h
    have lag : (x 0 * q 0 + x 1 * q 1) ^ 2 + (x 0 * q 1 - x 1 * q 0) ^ 2
        = (x 0 ^ 2 + x 1 ^ 2) * (q 0 ^ 2 + q 1 ^ 2) := by ring
    rw [e1, h, zero_pow two_ne_zero, add_zero] at lag
    exact mul_ne_zero hx2 hq2 lag.symm
  -- the cross product `x × y` vanishes
  have hxy : x 0 * y 1 - x 1 * y 0 = 0 := by
    have h : (x 0 * y 1 - x 1 * y 0) * (q 0 ^ 2 + q 1 ^ 2) = 0 := by
      linear_combination (-(y 0 * q 1 - y 1 * q 0)) * e1 + (x 0 * q 1 - x 1 * q 0) * e2
    rcases mul_eq_zero.mp h with h | h
    · exact h
    · exact absurd h hq2
  refine ⟨(y 0 * q 1 - y 1 * q 0) / (x 0 * q 1 - x 1 * q 0), ?_⟩
  ext i
  fin_cases i <;> simp only [Fin.mk_zero, Fin.mk_one, PiLp.smul_apply, smul_eq_mul]
  · rw [div_mul_eq_mul_div, eq_div_iff hc]
    linear_combination q 0 * hxy
  · rw [div_mul_eq_mul_div, eq_div_iff hc]
    linear_combination q 1 * hxy

/-- The tangency point of two internally tangent circles lies on the line
through the centers: with `w = M - O` and `d = O₁ - O`, we get
`w = (r / (r - r₁)) • d`. -/
lemma eq_smul_of_tangent {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {w d : V} {r r₁ : ℝ} (hr : 0 < r) (hr₁r : r₁ < r)
    (hw : ‖w‖ = r) (hwd : ‖w - d‖ = r₁) (hd : ‖d‖ = r - r₁) :
    w = (r / (r - r₁)) • d := by
  have hrr₁ : (0 : ℝ) < r - r₁ := sub_pos.mpr hr₁r
  have h := norm_sub_sq_real w d
  rw [hwd, hw, hd] at h
  have hinner : ⟪w, d⟫ = r * (r - r₁) := by linear_combination h / 2
  have hz : ‖w - (r / (r - r₁)) • d‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real, real_inner_smul_right, hinner, hw, norm_smul,
      Real.norm_eq_abs, abs_of_pos (div_pos hr hrr₁), hd]
    field_simp [hrr₁.ne']
    ring
  have h0 : w - (r / (r - r₁)) • d = 0 :=
    norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hz)
  exact sub_eq_zero.mp h0

/-- The key computation. Let `C` have center `O` and radius `r`, and let `C₁`,
`C₂` have centers `O₁`, `O₂` and radii `r₁`, `r₂`, where `C₁` passes through
`O₂` and both small circles are internally tangent to `C`. Let `M` be the
tangency point of `C` and `C₁`. If `X` lies on `C` and on the radical axis of
`C₁` and `C₂` (encoded as `⟪X - O₂, O₁ - O₂⟫ = r₂² / 2`), and `G ≠ M` is the
second intersection of the line `MX` with `C₁`, then
`⟪G - O₂, O₁ - O₂⟫ = r₁ * r₂`; in other words `G` lies on the line
`⟪·, O₁ - O₂⟫ = r₁ * r₂`, which is tangent to `C₂`. -/
lemma key_inner (O O₁ O₂ M X G : EuclideanSpace ℝ (Fin 2)) (r r₁ r₂ : ℝ)
    (hr : 0 < r) (hr₁ : 0 < r₁) (hr₁r : r₁ < r)
    (hO₁ : ‖O - O₁‖ = r - r₁) (hO₁O₂ : ‖O₁ - O₂‖ = r₁) (hO₂ : ‖O - O₂‖ = r - r₂)
    (hM : M = O + (r / (r - r₁)) • (O₁ - O)) (hMO₁ : ‖M - O₁‖ = r₁)
    (hX : ‖X - O‖ = r)
    (hXrad : ⟪X - O₂, O₁ - O₂⟫ = r₂ ^ 2 / 2)
    (hXM : X ≠ M)
    (hG : ‖G - O₁‖ = r₁)
    (hGline : Collinear ℝ {M, X, G})
    (hGM : G ≠ M) :
    ⟪G - O₂, O₁ - O₂⟫ = r₁ * r₂ := by
  have hrr₁ : (0 : ℝ) < r - r₁ := sub_pos.mpr hr₁r
  set p := O - O₂ with hp
  set q := O₁ - O₂ with hq
  -- basic norm facts
  have hq2 : ‖q‖ ^ 2 = r₁ ^ 2 := by rw [hO₁O₂]
  have hp2 : ‖p‖ ^ 2 = (r - r₂) ^ 2 := by rw [hO₂]
  have hX2 : ‖X - O‖ ^ 2 = r ^ 2 := by rw [hX]
  have hu2 : ‖O₁ - O‖ ^ 2 = (r - r₁) ^ 2 := by rw [norm_sub_rev, hO₁]
  have hMO₁2 : ‖M - O₁‖ ^ 2 = r₁ ^ 2 := by rw [hMO₁]
  -- ⟪p, q⟫ from the three center distances
  have hpq : p - q = O - O₁ := by
    rw [hp, hq]; exact sub_sub_sub_cancel_right _ _ _
  have hs : ⟪p, q⟫ = r * r₁ - r * r₂ + r₂ ^ 2 / 2 := by
    have h := norm_sub_sq_real p q
    rw [hpq, hO₁, hp2, hq2] at h
    linear_combination h / 2
  -- consequences of the position formula for `M`
  have hO₁O : O₁ - O = q - p := by
    rw [hp, hq]; exact (sub_sub_sub_cancel_right _ _ _).symm
  have hc1 : r / (r - r₁) - 1 = r₁ / (r - r₁) := by
    field_simp [hrr₁.ne']
    ring
  have hM1 : M - O₁ = (r₁ / (r - r₁)) • (O₁ - O) := by
    rw [hM, ← hc1, sub_smul, one_smul]; abel
  have hMX : X - M = (X - O) - (r / (r - r₁)) • (O₁ - O) := by rw [hM]; abel
  have hM2 : M - O₂ = (r / (r - r₁)) • (q - p) + p := by
    rw [hM, hO₁O, hp]; abel
  -- the inner product ⟪M - O₂, q⟫ (in denominator-free form)
  have hinnerM : ⟪M - O₂, q⟫ = (r / (r - r₁)) * (‖q‖ ^ 2 - ⟪p, q⟫) + ⟪p, q⟫ := by
    rw [hM2, inner_add_left, real_inner_smul_left, inner_sub_left,
      real_inner_self_eq_norm_sq]
  have hinnerM' : (r - r₁) * ⟪M - O₂, q⟫
      = r * (‖q‖ ^ 2 - ⟪p, q⟫) + (r - r₁) * ⟪p, q⟫ := by
    rw [hinnerM]; field_simp [hrr₁.ne']
  have hMq : (r - r₁) * ⟪M - O₂, q⟫ = r₁ * r₂ * (r - r₂ / 2) := by
    linear_combination hinnerM' + r * hq2 - r₁ * hs
  -- expansions around `M` and `X` (in denominator-free form)
  have hnXM' : (r - r₁) ^ 2 * ‖X - M‖ ^ 2
      = (r - r₁) ^ 2 * ‖X - O‖ ^ 2 - 2 * ((r - r₁) * r) * ⟪X - O, O₁ - O⟫
        + r ^ 2 * ‖O₁ - O‖ ^ 2 := by
    rw [hMX, norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos hr hrr₁)]
    field_simp [hrr₁.ne']
  have hiXM' : (r - r₁) ^ 2 * ⟪M - O₁, X - M⟫
      = r₁ * ((r - r₁) * ⟪O₁ - O, X - O⟫ - r * ‖O₁ - O‖ ^ 2) := by
    rw [hM1, hMX, real_inner_smul_left, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    field_simp [hrr₁.ne']
  have hcomm : ⟪O₁ - O, X - O⟫ = ⟪X - O, O₁ - O⟫ := real_inner_comm _ _
  -- the fundamental relation: `G` as below lies on `C₁` iff the parameter
  -- `t` with `G = M + t • (X - M)` satisfies `2 * ⟪M - O₁, X - M⟫ + t * ‖X - M‖² = 0`;
  -- the homothecy at `M` sending `C` to `C₁` (ratio `r₁ / r`) gives the
  -- nonzero solution `t = r₁ / r`.
  have hR' : 2 * r * ⟪M - O₁, X - M⟫ + r₁ * ‖X - M‖ ^ 2 = 0 := by
    have h0 : (2 * r * ⟪M - O₁, X - M⟫ + r₁ * ‖X - M‖ ^ 2) * (r - r₁) ^ 2 = 0 := by
      linear_combination 2 * r * hiXM' + r₁ * hnXM' - r ^ 2 * r₁ * hu2
        + r₁ * (r - r₁) ^ 2 * hX2 + 2 * r * r₁ * (r - r₁) * hcomm
    rcases mul_eq_zero.mp h0 with h5 | h6
    · exact h5
    · exact absurd h6 (pow_ne_zero 2 hrr₁.ne')
  have hR2 : r₁ * ‖X - M‖ ^ 2 = -(2 * r) * ⟪M - O₁, X - M⟫ := by
    linear_combination hR'
  -- parametrize `G` on the line `MX`
  obtain ⟨v, hv⟩ :=
    (collinear_iff_of_mem (show M ∈ ({M, X, G} : Set (EuclideanSpace ℝ (Fin 2)))
      from by simp)).mp hGline
  obtain ⟨a, haX⟩ := hv X (by simp)
  obtain ⟨b, hbG⟩ := hv G (by simp)
  have ha : a ≠ 0 := by
    intro h0
    rw [h0, zero_smul, zero_vadd] at haX
    exact hXM haX
  have hb : b ≠ 0 := by
    intro h0
    rw [h0, zero_smul, zero_vadd] at hbG
    exact hGM hbG
  have hGt : G - M = (b / a) • (X - M) := by
    have hX' : X - M = a • v := by rw [haX, vadd_eq_add, add_sub_cancel_right]
    have hG' : G - M = b • v := by rw [hbG, vadd_eq_add, add_sub_cancel_right]
    rw [hX', hG', smul_smul, div_mul_cancel₀ _ ha]
  -- `G` on `C₁` gives a quadratic equation for the parameter `b / a`
  have hGO₁ : G - O₁ = (M - O₁) + (b / a) • (X - M) := by
    have h1 : G - O₁ = (G - M) + (M - O₁) := by abel
    rw [h1, hGt, add_comm]
  have hab : (|b / a| * ‖X - M‖) ^ 2 = (b / a) ^ 2 * ‖X - M‖ ^ 2 := by
    rw [mul_pow, sq_abs]
  have hG2exp : 2 * (b / a) * ⟪M - O₁, X - M⟫ + (b / a) ^ 2 * ‖X - M‖ ^ 2 = 0 := by
    have h := norm_add_sq_real (M - O₁) ((b / a) • (X - M))
    rw [← hGO₁, hG, hMO₁2, real_inner_smul_right, norm_smul, Real.norm_eq_abs] at h
    linear_combination -h - hab
  -- the parameter must be `r₁ / r` (the other root `0` would give `G = M`)
  have hXMn : ‖X - M‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hXM))
  have h2 : 2 * ⟪M - O₁, X - M⟫ + (b / a) * ‖X - M‖ ^ 2 = 0 := by
    have h0 : (b / a) * (2 * ⟪M - O₁, X - M⟫ + (b / a) * ‖X - M‖ ^ 2) = 0 := by
      linear_combination hG2exp
    exact (mul_eq_zero.mp h0).resolve_left (div_ne_zero hb ha)
  have h3 : (b / a) * r * ‖X - M‖ ^ 2 = r₁ * ‖X - M‖ ^ 2 := by
    linear_combination r * h2 - hR2
  have h4 : (b / a) * r = r₁ := by
    have h0 : ((b / a) * r - r₁) * ‖X - M‖ ^ 2 = 0 := by linear_combination h3
    rcases mul_eq_zero.mp h0 with h5 | h6
    · exact sub_eq_zero.mp h5
    · exact absurd h6 hXMn
  have ht : b / a = r₁ / r := (eq_div_iff hr.ne').mpr h4
  -- substitute back and compute ⟪G - O₂, q⟫
  have hGfin : G - O₂ = (M - O₂) + (r₁ / r) • ((X - O₂) - (M - O₂)) := by
    have h1 : G = M + (b / a) • (X - M) := by
      rw [add_comm M]; exact sub_eq_iff_eq_add.mp hGt
    rw [ht] at h1
    have h2 : X - M = (X - O₂) - (M - O₂) := by abel
    rw [h1, h2]; abel
  have hinnerG : ⟪G - O₂, q⟫
      = ⟪M - O₂, q⟫ + (r₁ / r) * (⟪X - O₂, q⟫ - ⟪M - O₂, q⟫) := by
    have h1 : ⟪(X - O₂) - (M - O₂), q⟫ = ⟪X - O₂, q⟫ - ⟪M - O₂, q⟫ :=
      inner_sub_left _ _ _
    rw [hGfin, inner_add_left, real_inner_smul_left, h1]
  have hinnerG' : r * ⟪G - O₂, q⟫
      = r * ⟪M - O₂, q⟫ + r₁ * (⟪X - O₂, q⟫ - ⟪M - O₂, q⟫) := by
    rw [hinnerG]; field_simp [hr.ne']
  have hfinal : r * ⟪G - O₂, q⟫ = r * (r₁ * r₂) := by
    linear_combination hinnerG' + hMq + r₁ * hXrad
  exact mul_left_cancel₀ hr.ne' hfinal

snip end

problem imo1999_p5
    (O O₁ O₂ M A B E F : EuclideanSpace ℝ (Fin 2))
    (r r₁ r₂ : ℝ)
    (hr : 0 < r) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hr₁r : r₁ < r) (_hr₂r : r₂ < r)
    -- `C₁` and `C₂` are internally tangent to `C`; since they lie inside `C`,
    -- the distances between the centers are the differences of the radii.
    (hO₁ : dist O O₁ = r - r₁) (hO₂ : dist O O₂ = r - r₂)
    -- `C₁` passes through the center of `C₂`.
    (hO₁O₂ : dist O₁ O₂ = r₁)
    -- `M` is the tangency point of `C` and `C₁`.
    (hM : dist O M = r ∧ dist O₁ M = r₁)
    (_hAB : A ≠ B)
    -- `A` and `B` lie on `C` and on the line extending the common chord of
    -- `C₁` and `C₂`, i.e. on the radical axis of `C₁` and `C₂`.
    (hA : dist O A = r) (hB : dist O B = r)
    (hArad : dist A O₁ ^ 2 - r₁ ^ 2 = dist A O₂ ^ 2 - r₂ ^ 2)
    (hBrad : dist B O₁ ^ 2 - r₁ ^ 2 = dist B O₂ ^ 2 - r₂ ^ 2)
    (hAM : A ≠ M) (hBM : B ≠ M)
    -- `E` resp. `F` is the second intersection of `MA` resp. `MB` with `C₁`.
    (hE : dist O₁ E = r₁) (hEline : Collinear ℝ {M, A, E}) (hEM : E ≠ M)
    (hF : dist O₁ F = r₁) (hFline : Collinear ℝ {M, B, F}) (hFM : F ≠ M) :
    -- the line `EF` is tangent to `C₂`: there is a point `W` on the line `EF`
    -- with `dist O₂ W = r₂` such that `O₂W` is perpendicular to `EF`.
    ∃ W : EuclideanSpace ℝ (Fin 2), Collinear ℝ {E, F, W} ∧
      dist O₂ W = r₂ ∧ ⟪W - O₂, F - E⟫ = 0 := by
  have hO₁' : ‖O - O₁‖ = r - r₁ := by rw [← dist_eq_norm]; exact hO₁
  have hO₂' : ‖O - O₂‖ = r - r₂ := by rw [← dist_eq_norm]; exact hO₂
  have hO₁O₂' : ‖O₁ - O₂‖ = r₁ := by rw [← dist_eq_norm]; exact hO₁O₂
  have hMO : ‖M - O‖ = r := by rw [← dist_eq_norm, dist_comm]; exact hM.1
  have hMO₁ : ‖M - O₁‖ = r₁ := by rw [← dist_eq_norm, dist_comm]; exact hM.2
  have hA' : ‖A - O‖ = r := by rw [← dist_eq_norm, dist_comm]; exact hA
  have hB' : ‖B - O‖ = r := by rw [← dist_eq_norm, dist_comm]; exact hB
  have hE' : ‖E - O₁‖ = r₁ := by rw [← dist_eq_norm, dist_comm]; exact hE
  have hF' : ‖F - O₁‖ = r₁ := by rw [← dist_eq_norm, dist_comm]; exact hF
  -- position of the tangency point `M`
  have hMO₁'' : ‖M - O - (O₁ - O)‖ = r₁ := by
    have h1 : M - O - (O₁ - O) = M - O₁ := by abel
    rw [h1]; exact hMO₁
  have hMw := eq_smul_of_tangent hr hr₁r hMO hMO₁'' (by rw [norm_sub_rev]; exact hO₁')
  have hMpos : M = O + (r / (r - r₁)) • (O₁ - O) := by
    rw [add_comm O, ← sub_eq_iff_eq_add]; exact hMw
  -- the radical axis condition in inner product form
  have hq2 : ‖O₁ - O₂‖ ^ 2 = r₁ ^ 2 := by rw [hO₁O₂']
  have hArad' : ⟪A - O₂, O₁ - O₂⟫ = r₂ ^ 2 / 2 := by
    have hsub : A - O₁ = (A - O₂) - (O₁ - O₂) := by abel
    rw [dist_eq_norm, dist_eq_norm, hsub, norm_sub_sq_real, hq2] at hArad
    linear_combination -hArad / 2
  have hBrad' : ⟪B - O₂, O₁ - O₂⟫ = r₂ ^ 2 / 2 := by
    have hsub : B - O₁ = (B - O₂) - (O₁ - O₂) := by abel
    rw [dist_eq_norm, dist_eq_norm, hsub, norm_sub_sq_real, hq2] at hBrad
    linear_combination -hBrad / 2
  -- the key computation, applied to `A, E` and to `B, F`
  have hEi := key_inner O O₁ O₂ M A E r r₁ r₂ hr hr₁ hr₁r hO₁' hO₁O₂' hO₂'
    hMpos hMO₁ hA' hArad' hAM hE' hEline hEM
  have hFi := key_inner O O₁ O₂ M B F r r₁ r₂ hr hr₁ hr₁r hO₁' hO₁O₂' hO₂'
    hMpos hMO₁ hB' hBrad' hBM hF' hFline hFM
  -- the tangency point `W`
  have hq0 : O₁ - O₂ ≠ 0 := by
    rw [← norm_ne_zero_iff, hO₁O₂']; exact hr₁.ne'
  have hW : O₂ + (r₂ / r₁) • (O₁ - O₂) - O₂ = (r₂ / r₁) • (O₁ - O₂) := by abel
  refine ⟨O₂ + (r₂ / r₁) • (O₁ - O₂), ?_, ?_, ?_⟩
  · -- `W` is on the line `EF`
    by_cases hFE : F = E
    · rw [hFE]
      have hset : ({E, E, O₂ + (r₂ / r₁) • (O₁ - O₂)} : Set (EuclideanSpace ℝ (Fin 2)))
          = {E, O₂ + (r₂ / r₁) • (O₁ - O₂)} :=
        Set.insert_eq_of_mem (Set.mem_insert _ _)
      rw [hset]
      exact collinear_pair ℝ E (O₂ + (r₂ / r₁) • (O₁ - O₂))
    · have hxq : ⟪F - E, O₁ - O₂⟫ = 0 := by
        rw [show F - E = (F - O₂) - (E - O₂) from by abel, inner_sub_left, hFi, hEi,
          sub_self]
      have hWq : ⟪O₂ + (r₂ / r₁) • (O₁ - O₂) - O₂, O₁ - O₂⟫ = r₁ * r₂ := by
        rw [hW, real_inner_smul_left, real_inner_self_eq_norm_sq, hq2,
          div_mul_eq_mul_div, div_eq_iff hr₁.ne']
        ring
      have hyq : ⟪O₂ + (r₂ / r₁) • (O₁ - O₂) - E, O₁ - O₂⟫ = 0 := by
        rw [show O₂ + (r₂ / r₁) • (O₁ - O₂) - E
            = (O₂ + (r₂ / r₁) • (O₁ - O₂) - O₂) - (E - O₂) from by abel,
          inner_sub_left, hWq, hEi, sub_self]
      obtain ⟨t, ht⟩ :=
        exists_smul_of_inner_eq_zero hq0 (sub_ne_zero.mpr hFE) hxq hyq
      rw [collinear_iff_of_mem
        (show E ∈ ({E, F, O₂ + (r₂ / r₁) • (O₁ - O₂)} : Set (EuclideanSpace ℝ (Fin 2)))
          from by simp)]
      refine ⟨F - E, fun p hp => ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
      · exact ⟨t, by rw [vadd_eq_add, ← sub_eq_iff_eq_add]; exact ht⟩
  · -- `dist O₂ W = r₂`
    rw [dist_eq_norm, norm_sub_rev, hW, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos hr₂ hr₁), hO₁O₂', div_mul_cancel₀ _ hr₁.ne']
  · -- `O₂W` is perpendicular to `EF`
    rw [hW, real_inner_smul_left,
      show F - E = (F - O₂) - (E - O₂) from by abel, inner_sub_right,
      real_inner_comm (F - O₂) _, real_inner_comm (E - O₂) _, hFi, hEi]
    ring

end Imo1999P5
