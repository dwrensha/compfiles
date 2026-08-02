/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.AffineSpace.Midpoint
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1988, Problem 1

Consider two coplanar circles of radii R > r with the same center. Let P be a fixed
point on the smaller circle and B a variable point on the larger circle. The line BP
meets the larger circle again at C. The perpendicular to BP at P meets the smaller
circle again at A (if it is tangent to the circle at P, then A = P).

(i) Find the set of values of AB² + BC² + CA².
(ii) Find the locus of the midpoint of BC.
-/

namespace Imo1988P1

open scoped RealInnerProductSpace

/-- The ambient Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- The configuration described in the problem: two concentric circles centered at `O`
of radii `r < R`, a point `P` on the smaller circle, a point `B` on the larger circle,
`C` the second intersection of the line `BP` with the larger circle, and `A` the second
intersection with the smaller circle of the perpendicular to `BP` at `P`
(with `A = P` in the tangent case, i.e. when `O, P, B` are collinear). -/
structure Configuration (R r : ℝ) (O P B C A : Pt) : Prop where
  dist_P : dist P O = r
  dist_B : dist B O = R
  dist_C : dist C O = R
  dist_A : dist A O = r
  B_ne_P : B ≠ P
  C_ne_B : C ≠ B
  collinear_PBC : ∃ t : ℝ, C = P + t • (B - P)
  perp_AB : ⟪A - P, B - P⟫ = 0
  tangent_case : A ≠ P ∨ ∃ μ : ℝ, B - O = μ • (P - O)

/-- The answer to part (i): the only value attained by `AB² + BC² + CA²`. -/
noncomputable determine sumValue (R r : ℝ) : ℝ := 6 * R ^ 2 + 2 * r ^ 2

/-- The answer to part (ii): the locus of the midpoint of `BC` is the circle with
diameter `OP`. -/
noncomputable determine locus (O P : Pt) (r : ℝ) : Set Pt :=
  Metric.sphere (midpoint ℝ O P) (r / 2)

snip begin

/-! ### Coordinates in the plane -/

theorem Pt.ext {x y : Pt} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  apply WithLp.ofLp_injective (p := 2)
  funext i
  fin_cases i <;> assumption

theorem inner_pt (n x : Pt) : ⟪n, x⟫ = n 0 * x 0 + n 1 * x 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, RCLike.inner_apply]
  simp only [conj_trivial]
  ring

theorem norm_sq_pt (v : Pt) : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

/-- The midpoint of two points of the plane, as a vector expression. -/
theorem midpoint_half (x y : Pt) : midpoint ℝ x y = (1 / 2 : ℝ) • (x + y) := by
  rw [midpoint_eq_smul_add]
  congr 1
  exact eq_div_of_mul_eq (by norm_num) (invOf_mul_self (2 : ℝ))

/-- Rotation by 90 degrees. -/
def rot90 (v : Pt) : Pt := !₂[-(v 1), v 0]

@[simp] theorem rot90_apply0 (v : Pt) : rot90 v 0 = -(v 1) := rfl

@[simp] theorem rot90_apply1 (v : Pt) : rot90 v 1 = v 0 := rfl

theorem inner_rot90_self (v : Pt) : ⟪rot90 v, v⟫ = 0 := by
  rw [inner_pt, rot90_apply0, rot90_apply1]
  ring

theorem rot90_ne_zero {v : Pt} (hv : v ≠ 0) : rot90 v ≠ 0 := by
  intro h
  apply hv
  have h0 : rot90 v 0 = (0 : Pt) 0 := by rw [h]
  have h1 : rot90 v 1 = (0 : Pt) 1 := by rw [h]
  rw [rot90_apply0] at h0
  rw [rot90_apply1] at h1
  exact Pt.ext (by simpa using h1) (by simpa using h0)

theorem rot90_rot90 (v : Pt) : rot90 (rot90 v) = -v := by
  apply Pt.ext <;> simp [PiLp.neg_apply]

theorem norm_rot90 (v : Pt) : ‖rot90 v‖ = ‖v‖ := by
  have h : ‖rot90 v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [norm_sq_pt, norm_sq_pt]
    simp only [rot90_apply0, rot90_apply1]
    ring
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).mp h

/-- The two-dimensional Lagrange identity. -/
theorem inner_rot90_sq (x y : Pt) : ⟪x, rot90 y⟫ ^ 2 + ⟪x, y⟫ ^ 2 = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  rw [inner_pt, inner_pt, norm_sq_pt, norm_sq_pt]
  simp only [rot90_apply0, rot90_apply1]
  ring

theorem eq_smul_of_inner_rot90_eq_zero {v y : Pt} (hv : v ≠ 0)
    (h : ⟪rot90 v, y⟫ = 0) : ∃ t : ℝ, y = t • v := by
  rw [inner_pt, rot90_apply0, rot90_apply1] at h
  have hv' : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hv (Pt.ext (by simpa using hc.1) (by simpa using hc.2))
  rcases hv' with h0 | h1
  · refine ⟨y 0 / v 0, Pt.ext ?_ ?_⟩
    · rw [PiLp.smul_apply, smul_eq_mul]
      field_simp
    · rw [PiLp.smul_apply, smul_eq_mul]
      field_simp
      linarith
  · refine ⟨y 1 / v 1, Pt.ext ?_ ?_⟩
    · rw [PiLp.smul_apply, smul_eq_mul]
      field_simp
      linarith
    · rw [PiLp.smul_apply, smul_eq_mul]
      field_simp

/-! ### Scalar and vector algebra for the configuration -/

/-- The final scalar computation: with `D = ‖b - p‖²`, `e = ⟪p, b - p⟫`,
`ap = ‖a - p‖²` and `t` the parameter of `C` on the line `BP`, the sum of squares
`2·ap + 2·D·(t² - t + 1)` equals `6R² + 2r²`. -/
theorem scalar_core (D e t ap R r : ℝ) (hD : D ≠ 0)
    (h1 : 2 * e = R ^ 2 - r ^ 2 - D) (h2 : t * D = r ^ 2 - R ^ 2)
    (h3 : ap * D = 4 * (r ^ 2 * D - e ^ 2)) :
    2 * ap + 2 * D * (t ^ 2 - t + 1) = 6 * R ^ 2 + 2 * r ^ 2 := by
  have hSD : (2 * ap + 2 * D * (t ^ 2 - t + 1)) * D = (6 * R ^ 2 + 2 * r ^ 2) * D := by
    linear_combination 2 * h3 + (2 * (t * D + (r ^ 2 - R ^ 2)) - 2 * D) * h2
      - 2 * (2 * e + (R ^ 2 - r ^ 2 - D)) * h1
  exact mul_right_cancel₀ hD hSD

/-- Expanding the sum of squares `AB² + BC² + CA²` relative to the foot point `P`. -/
theorem sum_expand {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (p b c a : V) (t : ℝ) (hperp : ⟪a - p, b - p⟫ = 0) (hc : c = p + t • (b - p)) :
    ‖a - b‖ ^ 2 + ‖b - c‖ ^ 2 + ‖c - a‖ ^ 2
      = 2 * ‖a - p‖ ^ 2 + 2 * ‖b - p‖ ^ 2 * (t ^ 2 - t + 1) := by
  have e1 : a - b = (a - p) - (b - p) := by abel
  have e2 : b - c = (1 - t) • (b - p) := by rw [hc, sub_smul, one_smul]; abel
  have e3 : c - a = t • (b - p) - (a - p) := by rw [hc]; abel
  have h0 : ⟪b - p, a - p⟫ = 0 := by rw [real_inner_comm]; exact hperp
  rw [e1, e2, e3, norm_sub_sq_real (a - p) (b - p), norm_sub_sq_real (t • (b - p)) (a - p),
    hperp, norm_smul, norm_smul, real_inner_smul_left, h0, Real.norm_eq_abs,
    Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
  ring

/-- The second intersection `C` of a line through `P` with the outer circle:
the defining relations for its parameter. -/
theorem chord_param {p b c : Pt} {R r t : ℝ} (hp : ‖p‖ = r) (hb : ‖b‖ = R) (hc : ‖c‖ = R)
    (htc : c = p + t • (b - p)) (ht1 : t ≠ 1) :
    t * ‖b - p‖ ^ 2 = r ^ 2 - R ^ 2 ∧ 2 * ⟪p, b - p⟫ = R ^ 2 - r ^ 2 - ‖b - p‖ ^ 2 := by
  have hb2 : ‖b‖ ^ 2 = R ^ 2 := by rw [hb]
  have hp2 : ‖p‖ ^ 2 = r ^ 2 := by rw [hp]
  have hc2 : ‖c‖ ^ 2 = R ^ 2 := by rw [hc]
  have hD : ‖b - p‖ ^ 2 = R ^ 2 + r ^ 2 - 2 * ⟪p, b⟫ := by
    rw [norm_sub_sq_real, hb2, hp2, real_inner_comm p b]
    ring
  have hR1 : 2 * ⟪p, b - p⟫ = R ^ 2 - r ^ 2 - ‖b - p‖ ^ 2 := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq, hp2]
    linarith [hD]
  have hnormc : ‖c‖ ^ 2 = r ^ 2 + 2 * (t * ⟪p, b - p⟫) + t ^ 2 * ‖b - p‖ ^ 2 := by
    rw [htc, norm_add_sq_real, hp2, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs]
  have hcc : t ^ 2 * ‖b - p‖ ^ 2 + 2 * t * ⟪p, b - p⟫ + (r ^ 2 - R ^ 2) = 0 := by
    linarith [hnormc, hc2]
  have hfac : (t - 1) * (t * ‖b - p‖ ^ 2 + (R ^ 2 - r ^ 2)) = 0 := by
    linear_combination hcc - t * hR1
  have hR2 : t * ‖b - p‖ ^ 2 = r ^ 2 - R ^ 2 := by
    rcases mul_eq_zero.mp hfac with h0 | h0
    · exact absurd (eq_of_sub_eq_zero h0) ht1
    · linarith [h0]
  exact ⟨hR2, hR1⟩

/-- The key metric property of the second intersection `A` of the perpendicular
with the smaller circle: `‖a - p‖²·‖b - p‖² = 4(r²‖b - p‖² - ⟪p, b - p⟫²)`. -/
theorem second_inter_sq {p b a : Pt} {r : ℝ} (hp : ‖p‖ = r) (ha : ‖a‖ = r)
    (hperp : ⟪a - p, b - p⟫ = 0) (hu : b - p ≠ 0)
    (htan : a ≠ p ∨ ∃ μ : ℝ, b = μ • p) :
    ‖a - p‖ ^ 2 * ‖b - p‖ ^ 2 = 4 * (r ^ 2 * ‖b - p‖ ^ 2 - ⟪p, b - p⟫ ^ 2) := by
  have hp2 : ‖p‖ ^ 2 = r ^ 2 := by rw [hp]
  have ha2 : ‖a‖ ^ 2 = r ^ 2 := by rw [ha]
  by_cases hap : a = p
  · -- The tangent case: `b = μ • p`, and both sides vanish.
    obtain ⟨μ, hμ⟩ := htan.resolve_left (not_not_intro hap)
    have hu2 : b - p = (μ - 1) • p := by rw [hμ, sub_smul, one_smul]
    rw [hap, sub_self, norm_zero, hu2, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hp2,
      real_inner_smul_right, real_inner_self_eq_norm_sq, hp2]
    ring
  · -- The generic case: `a - p` is a multiple of `rot90 (b - p)`.
    have hkernel : ⟪rot90 (rot90 (b - p)), a - p⟫ = 0 := by
      rw [rot90_rot90, inner_neg_left, real_inner_comm (a - p) (b - p), hperp, neg_zero]
    obtain ⟨t, ht⟩ := eq_smul_of_inner_rot90_eq_zero (rot90_ne_zero hu) hkernel
    have ht0 : t ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at ht
      exact hap (sub_eq_zero.mp ht)
    have hnorm_w : ‖rot90 (b - p)‖ ^ 2 = ‖b - p‖ ^ 2 := by rw [norm_rot90]
    have hapsq : ‖a - p‖ ^ 2 = t ^ 2 * ‖b - p‖ ^ 2 := by
      rw [ht, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hnorm_w]
    have hkey : t * ‖b - p‖ ^ 2 = -2 * ⟪p, rot90 (b - p)⟫ := by
      have hexp : ‖a‖ ^ 2 = ‖p‖ ^ 2 + 2 * (t * ⟪p, rot90 (b - p)⟫) + t ^ 2 * ‖b - p‖ ^ 2 := by
        have ea : a = p + (a - p) := by abel
        rw [ea, ht, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
          mul_pow, sq_abs, hnorm_w]
      rw [ha2, hp2] at hexp
      have hfact : t * (2 * ⟪p, rot90 (b - p)⟫ + t * ‖b - p‖ ^ 2) = 0 := by
        linear_combination -hexp
      rcases mul_eq_zero.mp hfact with h0 | h0
      · exact absurd h0 ht0
      · linarith [h0]
    have hkey2 : (t * ‖b - p‖ ^ 2) ^ 2 = 4 * ⟪p, rot90 (b - p)⟫ ^ 2 := by rw [hkey]; ring
    have hlag := inner_rot90_sq p (b - p)
    rw [hp2] at hlag
    rw [hapsq, show t ^ 2 * ‖b - p‖ ^ 2 * ‖b - p‖ ^ 2 = (t * ‖b - p‖ ^ 2) ^ 2 from by ring,
      hkey2]
    linarith [hlag]

/-! ### Part (i) -/

theorem part1_forward {R r : ℝ} {O P B C A : Pt} (h : Configuration R r O P B C A) :
    dist A B ^ 2 + dist B C ^ 2 + dist C A ^ 2 = sumValue R r := by
  set p := P - O with hp_def
  set b := B - O with hb_def
  set c := C - O with hc_def
  set a := A - O with ha_def
  have hp : ‖p‖ = r := by rw [hp_def, ← dist_eq_norm]; exact h.dist_P
  have hb : ‖b‖ = R := by rw [hb_def, ← dist_eq_norm]; exact h.dist_B
  have hc : ‖c‖ = R := by rw [hc_def, ← dist_eq_norm]; exact h.dist_C
  have ha : ‖a‖ = r := by rw [ha_def, ← dist_eq_norm]; exact h.dist_A
  obtain ⟨t, ht⟩ := h.collinear_PBC
  have htc : c = p + t • (b - p) := by
    rw [hc_def, ht, hp_def, hb_def]
    have e : (B - O) - (P - O) = B - P := sub_sub_sub_cancel_right _ _ _
    rw [← e]
    abel
  have hperp' : ⟪a - p, b - p⟫ = 0 := by
    rw [ha_def, hp_def, hb_def, sub_sub_sub_cancel_right, sub_sub_sub_cancel_right]
    exact h.perp_AB
  have hu : b - p ≠ 0 := by
    intro h0
    apply h.B_ne_P
    have h1 : b = p := sub_eq_zero.mp h0
    rw [hb_def, hp_def] at h1
    exact sub_left_injective h1
  have hDne : ‖b - p‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hu)
  have ht1 : t ≠ 1 := by
    intro h1
    apply h.C_ne_B
    rw [h1, one_smul] at htc
    have h2 : c = b := by rw [htc]; abel
    rw [hc_def, hb_def] at h2
    exact sub_left_injective h2
  obtain ⟨hR2, hR1⟩ := chord_param hp hb hc htc ht1
  have hR3 : ‖a - p‖ ^ 2 * ‖b - p‖ ^ 2 = 4 * (r ^ 2 * ‖b - p‖ ^ 2 - ⟪p, b - p⟫ ^ 2) := by
    apply second_inter_sq hp ha hperp' hu
    rcases h.tangent_case with hnp | ⟨μ, hμ⟩
    · left
      intro hap
      apply hnp
      rw [ha_def, hp_def] at hap
      exact sub_left_injective hap
    · right
      exact ⟨μ, by rwa [hb_def, hp_def]⟩
  rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]
  have eAB : A - B = a - b := by rw [ha_def, hb_def]; abel
  have eBC : B - C = b - c := by rw [hb_def, hc_def]; abel
  have eCA : C - A = c - a := by rw [hc_def, ha_def]; abel
  rw [eAB, eBC, eCA, sum_expand p b c a t hperp' htc]
  exact scalar_core _ _ _ _ _ _ hDne hR1 hR2 hR3

/-- An explicit (tangent) configuration, showing the set of values is nonempty. -/
theorem config_exists {R r : ℝ} (hr : 0 < r) (hRr : r < R) :
    ∃ O P B C A : Pt, Configuration R r O P B C A := by
  have hR : 0 < R := hr.trans hRr
  have hr0 : (r : ℝ) ≠ 0 := ne_of_gt hr
  have hRr0 : R - r ≠ 0 := sub_ne_zero.mpr (ne_of_gt hRr)
  refine ⟨0, !₂[r, 0], !₂[R, 0], !₂[-R, 0], !₂[r, 0], ?_⟩
  have normPt : ∀ x : ℝ, 0 ≤ x → ‖(!₂[x, 0] : Pt)‖ = x := by
    intro x hx
    have h1 : ‖(!₂[x, 0] : Pt)‖ ^ 2 = x ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    exact (pow_left_inj₀ (norm_nonneg _) hx (by norm_num)).mp h1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [dist_eq_norm, sub_zero]
    exact normPt r hr.le
  · rw [dist_eq_norm, sub_zero]
    exact normPt R hR.le
  · rw [dist_eq_norm, sub_zero]
    have h1 : ‖(!₂[-R, 0] : Pt)‖ ^ 2 = R ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    exact (pow_left_inj₀ (norm_nonneg _) hR.le (by norm_num)).mp h1
  · rw [dist_eq_norm, sub_zero]
    exact normPt r hr.le
  · intro hbb
    have h0 : (!₂[R, 0] : Pt) 0 = (!₂[r, 0] : Pt) 0 := by rw [hbb]
    rw [PiLp.toLp_apply, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_zero] at h0
    linarith
  · intro hcb
    have h0 : (!₂[-R, 0] : Pt) 0 = (!₂[R, 0] : Pt) 0 := by rw [hcb]
    rw [PiLp.toLp_apply, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_zero] at h0
    linarith
  · refine ⟨(-R - r) / (R - r), ?_⟩
    apply Pt.ext
    · simp [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      field_simp
      ring
    · simp [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  · rw [sub_self, inner_zero_left]
  · right
    refine ⟨R / r, ?_⟩
    rw [sub_zero, sub_zero]
    apply Pt.ext
    · simp [PiLp.smul_apply, smul_eq_mul]
      field_simp
    · simp [PiLp.smul_apply, smul_eq_mul]

/-! ### Part (ii) -/

theorem part2_forward {R r : ℝ} (hr : 0 < r) {O P B C A : Pt}
    (h : Configuration R r O P B C A) :
    dist (midpoint ℝ B C) (midpoint ℝ O P) = r / 2 := by
  set p := P - O with hp_def
  set b := B - O with hb_def
  set c := C - O with hc_def
  have hp : ‖p‖ = r := by rw [hp_def, ← dist_eq_norm]; exact h.dist_P
  have hb : ‖b‖ = R := by rw [hb_def, ← dist_eq_norm]; exact h.dist_B
  have hc : ‖c‖ = R := by rw [hc_def, ← dist_eq_norm]; exact h.dist_C
  have hb2 : ‖b‖ ^ 2 = R ^ 2 := by rw [hb]
  have hp2 : ‖p‖ ^ 2 = r ^ 2 := by rw [hp]
  obtain ⟨t, ht⟩ := h.collinear_PBC
  have htc : c = p + t • (b - p) := by
    rw [hc_def, ht, hp_def, hb_def]
    have e : (B - O) - (P - O) = B - P := sub_sub_sub_cancel_right _ _ _
    rw [← e]
    abel
  have ht1 : t ≠ 1 := by
    intro h1
    apply h.C_ne_B
    rw [h1, one_smul] at htc
    have h2 : c = b := by rw [htc]; abel
    rw [hc_def, hb_def] at h2
    exact sub_left_injective h2
  obtain ⟨hR2, hR1⟩ := chord_param hp hb hc htc ht1
  have hbu : ⟪b, b - p⟫ = R ^ 2 - r ^ 2 - ⟪p, b - p⟫ := by
    rw [inner_sub_right b b p, inner_sub_right p b p, real_inner_self_eq_norm_sq b,
      real_inner_self_eq_norm_sq p, hb2, hp2, real_inner_comm p b]
    ring
  have hmq : midpoint ℝ B C - midpoint ℝ O P = (1 / 2 : ℝ) • (b + c - p) := by
    rw [midpoint_half, midpoint_half, hp_def, hb_def, hc_def]
    module
  have hdist2 : dist (midpoint ℝ B C) (midpoint ℝ O P) ^ 2 = (r / 2) ^ 2 := by
    rw [dist_eq_norm, hmq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have hbc : b + c - p = b + t • (b - p) := by rw [htc]; abel
    rw [hbc, norm_add_sq_real, hb2, real_inner_smul_right, hbu, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs]
    have h2t : t * (2 * ⟪p, b - p⟫) = t * (R ^ 2 - r ^ 2 - ‖b - p‖ ^ 2) :=
      congrArg (t * ·) hR1
    have h2tt : t * (t * ‖b - p‖ ^ 2) = t * (r ^ 2 - R ^ 2) := congrArg (t * ·) hR2
    nlinarith [h2t, h2tt, hR2]
  exact (pow_left_inj₀ dist_nonneg (by linarith) (by norm_num)).mp hdist2

theorem part2_backward {R r : ℝ} (hr : 0 < r) (hRr : r < R) {O P m : Pt}
    (hOP : dist P O = r) (hm : dist m (midpoint ℝ O P) = r / 2) :
    ∃ B C A : Pt, Configuration R r O P B C A ∧ m = midpoint ℝ B C := by
  have hR : 0 < R := hr.trans hRr
  have hr0 : (r : ℝ) ≠ 0 := ne_of_gt hr
  have hRr2 : 0 < R ^ 2 - r ^ 2 := by
    have h1 := mul_pos (sub_pos.mpr hRr) (show 0 < R + r by linarith)
    nlinarith [h1]
  set p := P - O with hp_def
  have hp : ‖p‖ = r := by rw [hp_def, ← dist_eq_norm]; exact hOP
  have hp2 : ‖p‖ ^ 2 = r ^ 2 := by rw [hp]
  have hp0 : p ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hp
    exact hr0 hp.symm
  set q := m - O with hq_def
  have hP : P = O + p := by rw [hp_def]; abel
  have hmq : m = O + q := by rw [hq_def]; abel
  have hMq : ⟪q, q - p⟫ = 0 := by
    have h1 : m - midpoint ℝ O P = q - (1 / 2 : ℝ) • p := by
      rw [midpoint_half, hq_def, hp_def]
      module
    have h2 : ‖q - (1 / 2 : ℝ) • p‖ ^ 2 = (r / 2) ^ 2 := by
      have hdn : dist m (midpoint ℝ O P) = ‖m - midpoint ℝ O P‖ := dist_eq_norm _ _
      rw [h1] at hdn
      rw [← hdn, hm]
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow,
      sq_abs, hp2] at h2
    rw [inner_sub_right, real_inner_self_eq_norm_sq]
    linarith [h2]
  by_cases hcase : q = p
  · -- The midpoint is `P` itself: take the chord perpendicular to `OP` at `P`.
    set k := Real.sqrt (R ^ 2 - r ^ 2) / r with hk_def
    have hk0 : k ≠ 0 := by
      have h1 : 0 < Real.sqrt (R ^ 2 - r ^ 2) := Real.sqrt_pos.mpr hRr2
      exact div_ne_zero (ne_of_gt h1) hr0
    have hk2 : k ^ 2 * ‖p‖ ^ 2 = R ^ 2 - r ^ 2 := by
      rw [hp2, hk_def, div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 hr0),
        Real.sq_sqrt hRr2.le]
    set v := k • rot90 p with hv_def
    have hv0 : v ≠ 0 := smul_ne_zero hk0 (rot90_ne_zero hp0)
    have hpv : ⟪p, v⟫ = 0 := by
      rw [hv_def, real_inner_smul_right, real_inner_comm (rot90 p) p, inner_rot90_self,
        mul_zero]
    have hv2 : ‖v‖ ^ 2 = R ^ 2 - r ^ 2 := by
      rw [hv_def, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, norm_rot90, hk2]
    have hPm : m = P := by
      have h4 : m - O = P - O := by rw [← hq_def, ← hp_def]; exact hcase
      exact sub_left_injective h4
    refine ⟨O + (p + v), O + (p - v), O + (-p), ?_, ?_⟩
    · refine ⟨hOP, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [dist_eq_norm, add_sub_cancel_left]
        have h1 : ‖p + v‖ ^ 2 = R ^ 2 := by rw [norm_add_sq_real, hp2, hpv, hv2]; ring
        exact (pow_left_inj₀ (norm_nonneg _) hR.le (by norm_num)).mp h1
      · rw [dist_eq_norm, add_sub_cancel_left]
        have h1 : ‖p - v‖ ^ 2 = R ^ 2 := by rw [norm_sub_sq_real, hp2, hpv, hv2]; ring
        exact (pow_left_inj₀ (norm_nonneg _) hR.le (by norm_num)).mp h1
      · rw [dist_eq_norm, add_sub_cancel_left, norm_neg]
        exact hp
      · intro hbb
        rw [hP] at hbb
        have h2 : p + v = p := add_right_injective O hbb
        have h3 : p + v = p + 0 := by rw [h2, add_zero]
        exact hv0 (add_left_cancel h3)
      · intro hcb
        have h2 : p - v = p + v := add_right_injective O hcb
        have h3 : p - v - (p + v) = 0 := sub_eq_zero.mpr h2
        have h4 : p - v - (p + v) = -(2 : ℝ) • v := by module
        rw [h4] at h3
        exact hv0 ((smul_eq_zero.mp h3).resolve_left (by norm_num))
      · refine ⟨-1, ?_⟩
        have h1 : (O + (p + v)) - (O + p) = v := by abel
        rw [hP, h1, neg_one_smul]
        abel
      · have e1 : (O + -p) - P = -(2 : ℝ) • p := by rw [hP]; module
        have e2 : (O + (p + v)) - P = v := by rw [hP]; abel
        rw [e1, e2, real_inner_smul_left, hpv, mul_zero]
      · left
        intro hap
        rw [hP] at hap
        have h2 : -p = p := add_right_injective O hap
        have h3 : -p - p = 0 := sub_eq_zero.mpr h2
        have h4 : -p - p = -(2 : ℝ) • p := by module
        rw [h4] at h3
        exact hp0 ((smul_eq_zero.mp h3).resolve_left (by norm_num))
    · rw [hPm, midpoint_half, hP]
      module
  · -- The general case: intersect the line through `P` and `m` with the outer circle.
    set d := q - p with hd_def
    have hd0 : d ≠ 0 := sub_ne_zero.mpr hcase
    have hd2 : 0 < ‖d‖ ^ 2 := pow_pos (norm_pos_iff.mpr hd0) 2
    have hd2' : ‖d‖ ^ 2 ≠ 0 := ne_of_gt hd2
    have hqp : q = p + d := by rw [hd_def]; abel
    have he : ⟪p, d⟫ = -‖d‖ ^ 2 := by
      have hpq : p = q - d := by rw [hd_def]; abel
      rw [hpq, inner_sub_left, real_inner_self_eq_norm_sq, hMq]
      ring
    set D' := ‖d‖ ^ 2 with hD'_def
    set e' := ⟪p, d⟫ with he'_def
    have he'' : e' = -D' := he
    set Disc := e' ^ 2 + D' * (R ^ 2 - r ^ 2) with hDisc_def
    have hDisc : 0 < Disc := by
      have h1 : 0 < D' * (R ^ 2 - r ^ 2) := mul_pos hd2 hRr2
      rw [hDisc_def]
      nlinarith [sq_nonneg e', h1]
    set s := Real.sqrt Disc with hs_def
    have hs : 0 < s := Real.sqrt_pos.mpr hDisc
    have hs2 : s ^ 2 = Disc := Real.sq_sqrt hDisc.le
    set t₁ := (-e' - s) / D' with ht₁_def
    set t₂ := (-e' + s) / D' with ht₂_def
    have ht₁0 : t₁ ≠ 0 := by
      intro h0
      rw [ht₁_def] at h0
      have h1 : -e' - s = 0 := by
        rcases div_eq_zero_iff.mp h0 with h2 | h2
        · exact h2
        · exact absurd h2 hd2'
      have he's : e' = -s := by linarith
      have h2 : e' ^ 2 = s ^ 2 := by rw [he's, neg_sq]
      nlinarith [h2, hs2, hDisc_def, mul_pos hd2 hRr2]
    have hts : t₁ ≠ t₂ := by
      rw [ht₁_def, ht₂_def]
      intro hcon
      rw [div_eq_div_iff hd2' hd2'] at hcon
      have h1 : -e' - s = -e' + s := mul_right_cancel₀ hd2' hcon
      nlinarith [hs]
    have hroot₁ : D' * t₁ ^ 2 + 2 * e' * t₁ = R ^ 2 - r ^ 2 := by
      have hf1 : D' * t₁ + e' = -s := by rw [ht₁_def]; field_simp; ring
      have hsq : (D' * t₁ + e') ^ 2 = s ^ 2 := by rw [hf1, neg_sq]
      rw [hDisc_def] at hs2
      have hexp : (D' * t₁ + e') ^ 2 = D' * (D' * t₁ ^ 2 + 2 * e' * t₁) + e' ^ 2 := by ring
      have h3 : D' * (D' * t₁ ^ 2 + 2 * e' * t₁) = D' * (R ^ 2 - r ^ 2) := by
        linear_combination hsq + hs2 - hexp
      exact mul_left_cancel₀ hd2' h3
    have hroot₂ : D' * t₂ ^ 2 + 2 * e' * t₂ = R ^ 2 - r ^ 2 := by
      have hf2 : D' * t₂ + e' = s := by rw [ht₂_def]; field_simp; ring
      have hsq : (D' * t₂ + e') ^ 2 = s ^ 2 := by rw [hf2]
      have hexp : (D' * t₂ + e') ^ 2 = D' * (D' * t₂ ^ 2 + 2 * e' * t₂) + e' ^ 2 := by ring
      have h3 : D' * (D' * t₂ ^ 2 + 2 * e' * t₂) = D' * (R ^ 2 - r ^ 2) := by
        linear_combination hsq + hs2 - hexp
      exact mul_left_cancel₀ hd2' h3
    have hsum : t₁ + t₂ = 2 := by
      rw [ht₁_def, ht₂_def, he'']
      field_simp
      ring
    set B₀ := O + (p + t₁ • d) with hB_def
    set C₀ := O + (p + t₂ • d) with hC_def
    have hB_norm : ‖p + t₁ • d‖ = R := by
      have h1 : ‖p + t₁ • d‖ ^ 2 = R ^ 2 := by
        rw [norm_add_sq_real, hp2, real_inner_smul_right, ← he'_def, norm_smul,
          Real.norm_eq_abs, mul_pow, sq_abs, ← hD'_def]
        linarith [hroot₁]
      exact (pow_left_inj₀ (norm_nonneg _) hR.le (by norm_num)).mp h1
    have hC_norm : ‖p + t₂ • d‖ = R := by
      have h1 : ‖p + t₂ • d‖ ^ 2 = R ^ 2 := by
        rw [norm_add_sq_real, hp2, real_inner_smul_right, ← he'_def, norm_smul,
          Real.norm_eq_abs, mul_pow, sq_abs, ← hD'_def]
        linarith [hroot₂]
      exact (pow_left_inj₀ (norm_nonneg _) hR.le (by norm_num)).mp h1
    set W := rot90 d with hW_def
    have hW0 : W ≠ 0 := rot90_ne_zero hd0
    have hW2 : ‖W‖ ^ 2 = D' := by rw [hW_def, norm_rot90, hD'_def]
    have hW2' : ‖W‖ ^ 2 ≠ 0 := by rw [hW2]; exact hd2'
    set sA := -2 * ⟪p, W⟫ / ‖W‖ ^ 2 with hsA_def
    have hA_norm : ‖p + sA • W‖ = r := by
      have hsAw : sA * ‖W‖ ^ 2 = -2 * ⟪p, W⟫ := by
        rw [hsA_def, div_mul_cancel₀ _ hW2']
      have h1 : ‖p + sA • W‖ ^ 2 = r ^ 2 := by
        rw [norm_add_sq_real, hp2, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
          mul_pow, sq_abs]
        linear_combination sA * hsAw
      exact (pow_left_inj₀ (norm_nonneg _) hr.le (by norm_num)).mp h1
    set A₀ := O + (p + sA • W) with hA_def
    have hBt : B₀ - O = p + t₁ • d := by rw [hB_def]; abel
    have hCt : C₀ - O = p + t₂ • d := by rw [hC_def]; abel
    have hAt : A₀ - O = p + sA • W := by rw [hA_def]; abel
    have hAP : A₀ - P = sA • W := by rw [hA_def, hP]; abel
    have hBP : B₀ - P = t₁ • d := by rw [hB_def, hP]; abel
    have hperp_AB : ⟪A₀ - P, B₀ - P⟫ = 0 := by
      rw [hAP, hBP, real_inner_smul_left, real_inner_smul_right, hW_def,
        inner_rot90_self, mul_zero, mul_zero]
    refine ⟨B₀, C₀, A₀, ⟨hOP, ?_, ?_, ?_, ?_, ?_, ?_, hperp_AB, ?_⟩, ?_⟩
    · rw [dist_eq_norm, hBt]
      exact hB_norm
    · rw [dist_eq_norm, hCt]
      exact hC_norm
    · rw [dist_eq_norm, hAt]
      exact hA_norm
    · intro hbb
      rw [hP, hB_def] at hbb
      have h2 : p + t₁ • d = p := add_right_injective O hbb
      have h3 : p + t₁ • d = p + 0 := by rw [h2, add_zero]
      have h4 := add_left_cancel h3
      exact ht₁0 ((smul_eq_zero.mp h4).resolve_right hd0)
    · intro hcb
      rw [hB_def, hC_def] at hcb
      have h2 : p + t₂ • d = p + t₁ • d := add_right_injective O hcb
      have h3 := add_left_cancel h2
      have h4 : (t₂ - t₁) • d = 0 := by rw [sub_smul]; exact sub_eq_zero.mpr h3
      exact hts ((sub_eq_zero.mp ((smul_eq_zero.mp h4).resolve_right hd0)).symm)
    · refine ⟨t₂ / t₁, ?_⟩
      rw [hBP, smul_smul, div_mul_cancel₀ _ ht₁0, hC_def, hP]
      abel
    · by_cases hsA0 : sA = 0
      · right
        have hpW : ⟪p, W⟫ = 0 := by
          rw [hsA_def] at hsA0
          rcases div_eq_zero_iff.mp hsA0 with h1 | h1
          · linarith [h1]
          · exact absurd h1 hW2'
        have hpd : ⟪rot90 d, p⟫ = 0 := by
          rw [hW_def] at hpW
          rw [real_inner_comm (rot90 d) p] at hpW
          exact hpW
        obtain ⟨l, hl⟩ := eq_smul_of_inner_rot90_eq_zero hd0 hpd
        by_cases hl0 : l = 0
        · rw [hl0, zero_smul] at hl
          exact absurd hl hp0
        · refine ⟨(l + t₁) / l, ?_⟩
          rw [← hp_def, hBt, hl, smul_smul, div_mul_cancel₀ _ hl0, add_smul]
      · left
        intro hap
        have h1 : A₀ - P = 0 := sub_eq_zero.mpr hap
        rw [hAP] at h1
        exact hsA0 ((smul_eq_zero.mp h1).resolve_right hW0)
    · rw [hmq, midpoint_half, hB_def, hC_def, hqp]
      have h2 : (O + (p + t₁ • d)) + (O + (p + t₂ • d)) = (2 : ℝ) • (O + p) + (t₁ + t₂) • d := by
        rw [add_smul, two_smul]
        abel
      rw [h2, hsum]
      module

snip end

problem imo1988_p1 (R r : ℝ) (hr : 0 < r) (hRr : r < R) :
    ({s : ℝ | ∃ O P B C A : Pt, Configuration R r O P B C A ∧
        s = dist A B ^ 2 + dist B C ^ 2 + dist C A ^ 2} = {sumValue R r}) ∧
    (∀ O P : Pt, dist P O = r →
      {m : Pt | ∃ B C A : Pt, Configuration R r O P B C A ∧ m = midpoint ℝ B C} =
        locus O P r) := by
  refine ⟨?_, ?_⟩
  · ext s
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨O, P, B, C, A, hcfg, rfl⟩
      exact part1_forward hcfg
    · intro hs
      obtain ⟨O, P, B, C, A, hcfg⟩ := config_exists hr hRr
      refine ⟨O, P, B, C, A, hcfg, ?_⟩
      rw [part1_forward hcfg]
      exact hs
  · intro O P hOP
    ext m
    simp only [Set.mem_setOf_eq]
    show (∃ B C A : Pt, Configuration R r O P B C A ∧ m = midpoint ℝ B C) ↔
      dist m (midpoint ℝ O P) = r / 2
    constructor
    · rintro ⟨B, C, A, hcfg, rfl⟩
      exact part2_forward hr hcfg
    · intro hm
      exact part2_backward hr hRr hOP hm

end Imo1988P1
