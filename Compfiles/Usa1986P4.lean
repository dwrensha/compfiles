/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 1986, Problem 4

A T-square allows you to construct a straight line through two points and a
line perpendicular to a given line through a given point. Circles C and C'
intersect at X and Y. XY is a diameter of C. P is a point on C' inside C.
Using only a T-square, find points Q,R on C such that QR is perpendicular to
XY and PQ is perpendicular to PR.
-/

namespace Usa1986P4

open RealInnerProductSpace

snip begin

lemma inner_coords (x y : EuclideanSpace ℝ (Fin 2)) :
    ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

def perp (d : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) := !₂[-d 1, d 0]

lemma inner_perp (d : EuclideanSpace ℝ (Fin 2)) : ⟪d, perp d⟫ = 0 := by
  simp [perp, inner_coords, mul_comm]

lemma norm_sq_coords (x : EuclideanSpace ℝ (Fin 2)) :
    ‖x‖ ^ 2 = (x 0)^2 + (x 1)^2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two]

lemma norm_perp (d : EuclideanSpace ℝ (Fin 2)) : ‖perp d‖ = ‖d‖ := by
  have h1 := norm_sq_coords (perp d)
  have h2 := norm_sq_coords d
  have h3 : ‖perp d‖^2 = ‖d‖^2 := by
    rw [h1, h2]
    simp only [perp, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have h4 : 0 ≤ ‖perp d‖ := norm_nonneg _
  have h5 : 0 ≤ ‖d‖ := norm_nonneg _
  nlinarith

lemma decomp (d p : EuclideanSpace ℝ (Fin 2)) (hd : d ≠ 0) :
    p = (⟪p, d⟫ / ⟪d, d⟫) • d + (⟪p, perp d⟫ / ⟪d, d⟫) • perp d := by
  have hdd : (d 0)^2 + (d 1)^2 ≠ 0 := by
    have h1 : ⟪d, d⟫ ≠ 0 := ne_of_gt (real_inner_self_pos.mpr hd)
    rwa [inner_coords, ← sq, ← sq] at h1
  have key : ∀ i : Fin 2, p i =
      ((⟪p, d⟫ / ⟪d, d⟫) • d + (⟪p, perp d⟫ / ⟪d, d⟫) • perp d) i := by
    rw [Fin.forall_fin_two]
    constructor
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      rw [inner_coords p d, inner_coords p (perp d), inner_coords d d]
      simp only [perp, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one]
      field_simp
      ring
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      rw [inner_coords p d, inner_coords p (perp d), inner_coords d d]
      simp only [perp, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one]
      field_simp
      ring
  ext i
  exact key i

/-- The heart of the construction: given a nonzero vector `d` (half of the
diameter `XY`) and a vector `p` strictly shorter than `d` (the position of `P`
relative to the center `O`), we produce two vectors `q` and `r` of length `‖d‖`,
symmetric about the span of `d`, such that `q - r ⟂ d` and `(q - p) ⟂ (r - p)`.
The choice of the parameter `t` below is what makes the right angle at `P` work;
it is one root of `2t² - 2αt + (α² + β² - 1) = 0`, whose discriminant
`2 - α² - 2β²` is positive because `α² + β² < 1`. -/
lemma exists_qr (d p : EuclideanSpace ℝ (Fin 2)) (hd : d ≠ 0) (hp : ‖p‖ < ‖d‖) :
    ∃ q r : EuclideanSpace ℝ (Fin 2),
      ‖q‖ = ‖d‖ ∧ ‖r‖ = ‖d‖ ∧ q ≠ r ∧
      ⟪q - r, d⟫ = 0 ∧ ⟪q - p, r - p⟫ = 0 := by
  set e := perp d with he_def
  have hdd_pos : 0 < ⟪d, d⟫ := real_inner_self_pos.mpr hd
  have hde : ⟪d, e⟫ = 0 := inner_perp d
  have hed : ⟪e, d⟫ = 0 := by rw [real_inner_comm]; exact hde
  have he_norm : ‖e‖ = ‖d‖ := norm_perp d
  have hee : ⟪e, e⟫ = ⟪d, d⟫ := by
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, he_norm]
  have he_ne : e ≠ 0 := by
    intro h
    rw [h, norm_zero] at he_norm
    exact hd (norm_eq_zero.mp he_norm.symm)
  set α := ⟪p, d⟫ / ⟪d, d⟫ with hα_def
  set β := ⟪p, e⟫ / ⟪d, d⟫ with hβ_def
  have hdecomp : p = α • d + β • e := decomp d p hd
  have hpp : ⟪p, p⟫ = (α^2 + β^2) * ⟪d, d⟫ := by
    rw [hdecomp]
    simp only [inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right]
    rw [hde, hed, hee]
    ring
  have hαβ : α^2 + β^2 < 1 := by
    have h1 : ‖p‖^2 < ‖d‖^2 := pow_lt_pow_left₀ hp (norm_nonneg _) two_ne_zero
    rw [← real_inner_self_eq_norm_sq, hpp, ← real_inner_self_eq_norm_sq d] at h1
    nlinarith
  -- the discriminant is positive
  have hΔ : (0:ℝ) < 2 - α^2 - 2*β^2 := by nlinarith
  set Δ := 2 - α^2 - 2*β^2 with hΔ_def
  -- choose the parameter along `d`
  set t := (α + Real.sqrt Δ)/2 with ht_def
  have ht2 : 2*t^2 - 2*α*t + (α^2+β^2-1) = 0 := by
    have h1 : (2*t - α)^2 = Δ := by
      have h2 : 2*t - α = Real.sqrt Δ := by rw [ht_def]; ring
      rw [h2, Real.sq_sqrt (le_of_lt hΔ)]
    have h3 : (2*t - α)^2 = 4*t^2 - 4*α*t + α^2 := by ring
    rw [h3, hΔ_def] at h1
    linarith
  have hα_bds : -1 < α ∧ α < 1 := by
    have hα2 : α^2 < 1 := by nlinarith [sq_nonneg β, hαβ]
    have h1 : α^2 < (1:ℝ)^2 := by rw [one_pow]; exact hα2
    exact abs_lt.mp (by rwa [sq_lt_sq, abs_one] at h1)
  have ht_lt_one : t < 1 := by
    have h1 : Real.sqrt Δ < 2 - α := by
      rw [Real.sqrt_lt' (by linarith [hα_bds.2])]
      rw [hΔ_def]
      have hpos : (0:ℝ) < (1-α)^2 + β^2 := by
        have h2 : (1:ℝ) - α ≠ 0 := by linarith [hα_bds.2]
        nlinarith [sq_pos_of_ne_zero h2, sq_nonneg β]
      nlinarith
    rw [ht_def]
    linarith
  have ht_gt_neg_one : -1 < t := by
    have h1 : 0 ≤ Real.sqrt Δ := Real.sqrt_nonneg _
    rw [ht_def]
    linarith [hα_bds.1]
  have ht_sq : t^2 < 1 := by nlinarith [ht_lt_one, ht_gt_neg_one]
  -- the parameter along `e`
  set s := Real.sqrt (1 - t^2) with hs_def
  have hs_pos : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hs_sq : s^2 = 1 - t^2 := Real.sq_sqrt (by linarith)
  have hbrack : (t-α)^2 + β^2 - s^2 = 0 := by linear_combination ht2 - hs_sq
  refine ⟨t • d + s • e, t • d - s • e, ?_, ?_, ?_, ?_, ?_⟩
  · -- ‖q‖ = ‖d‖
    have hqq : ⟪t • d + s • e, t • d + s • e⟫ = ⟪d, d⟫ := by
      simp only [inner_add_left, inner_add_right,
        real_inner_smul_left, real_inner_smul_right]
      rw [hde, hed, hee]
      linear_combination ⟪d, d⟫ * hs_sq
    have h1 : ‖t • d + s • e‖^2 = ‖d‖^2 := by
      rw [← real_inner_self_eq_norm_sq, hqq, real_inner_self_eq_norm_sq]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h1
  · -- ‖r‖ = ‖d‖
    have hrr : ⟪t • d - s • e, t • d - s • e⟫ = ⟪d, d⟫ := by
      simp only [inner_sub_left, inner_sub_right,
        real_inner_smul_left, real_inner_smul_right]
      rw [hde, hed, hee]
      linear_combination ⟪d, d⟫ * hs_sq
    have h1 : ‖t • d - s • e‖^2 = ‖d‖^2 := by
      rw [← real_inner_self_eq_norm_sq, hrr, real_inner_self_eq_norm_sq]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h1
  · -- q ≠ r
    have hsub : (t • d + s • e) - (t • d - s • e) = (2*s) • e := by module
    have hne : (2*s) • e ≠ 0 := smul_ne_zero (by linarith) he_ne
    intro hqr
    exact hne (by rw [← hsub, sub_eq_zero]; exact hqr)
  · -- ⟪q - r, d⟫ = 0
    have hsub : (t • d + s • e) - (t • d - s • e) = (2*s) • e := by module
    rw [hsub, real_inner_smul_left, hed, mul_zero]
  · -- ⟪q - p, r - p⟫ = 0
    have hqp : (t • d + s • e) - p = (t-α) • d + (s-β) • e := by
      rw [hdecomp]; module
    have hrp : (t • d - s • e) - p = (t-α) • d - (s+β) • e := by
      rw [hdecomp]; module
    rw [hqp, hrp]
    have hexp : ⟪(t-α) • d + (s-β) • e, (t-α) • d - (s+β) • e⟫
        = ⟪d, d⟫ * ((t-α)^2 + β^2 - s^2) := by
      simp only [inner_add_left, inner_sub_right,
        real_inner_smul_left, real_inner_smul_right]
      rw [hde, hed, hee]
      ring
    rw [hexp, hbrack, mul_zero]

snip end

-- Since the T-square construction process itself cannot be formalized directly,
-- we prove the existence of the required points `Q` and `R` on the circle `C`
-- (the circle `C'` only plays a role in the construction, not in the existence
-- statement). The explicit construction: write `P - O = α • (X - O) + β • e`,
-- where `e` is `(X - O)` rotated by 90°, and take `Q, R = O + t • (X - O) ± s • e`
-- with `t = (α + √(2 - α² - 2β²))/2` and `s = √(1 - t²)`; the condition that
-- `∠QPR` is right is exactly the quadratic equation satisfied by `t`.

problem usa1986_p4
    (O O' X Y P : EuclideanSpace ℝ (Fin 2))
    (r r' : ℝ)
    (hr : 0 < r)
    (hXC : dist X O = r) (_hYC : dist Y O = r)
    (_hXC' : dist X O' = r') (_hYC' : dist Y O' = r')
    (_hXY : X ≠ Y)
    (hdiam : midpoint ℝ X Y = O)
    (_hPC' : dist P O' = r')
    (hP : dist P O < r) :
    ∃ Q R : EuclideanSpace ℝ (Fin 2),
      dist Q O = r ∧ dist R O = r ∧ Q ≠ R ∧
      ⟪Q -ᵥ R, X -ᵥ Y⟫ = 0 ∧ ⟪Q -ᵥ P, R -ᵥ P⟫ = 0 := by
  have hYO : Y - O = -(X - O) := by
    have h2 : X + Y = O + O := by rw [← midpoint_add_self ℝ X Y, hdiam]
    linear_combination (norm := module) h2
  have hd_norm : ‖X - O‖ = r := by rw [← hXC, dist_eq_norm_vsub, vsub_eq_sub]
  have hd_ne : X - O ≠ 0 := by
    intro h
    rw [h, norm_zero] at hd_norm
    linarith
  have hp_norm : ‖P - O‖ < ‖X - O‖ := by
    have h1 : ‖P - O‖ = dist P O := by rw [dist_eq_norm_vsub, vsub_eq_sub]
    rw [h1, hd_norm]
    exact hP
  obtain ⟨q, rr, hq, hrr, hqr, horth, hporth⟩ := exists_qr (X - O) (P - O) hd_ne hp_norm
  refine ⟨q + O, rr + O, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : dist (q + O) O = ‖q‖ := by
      rw [dist_eq_norm_vsub, vsub_eq_sub]
      simp
    rw [h1, hq, hd_norm]
  · have h1 : dist (rr + O) O = ‖rr‖ := by
      rw [dist_eq_norm_vsub, vsub_eq_sub]
      simp
    rw [h1, hrr, hd_norm]
  · intro h
    exact hqr (add_right_cancel h)
  · have h1 : (q + O) -ᵥ (rr + O) = q - rr := by simp [vsub_eq_sub]
    have h2 : X -ᵥ Y = (2:ℝ) • (X - O) := by
      rw [vsub_eq_sub]
      linear_combination (norm := module) -hYO
    rw [h1, h2, real_inner_smul_right, horth, mul_zero]
  · have h1 : (q + O) -ᵥ P = q - (P - O) := by rw [vsub_eq_sub]; module
    have h2 : (rr + O) -ᵥ P = rr - (P - O) := by rw [vsub_eq_sub]; module
    rw [h1, h2, hporth]


end Usa1986P4
