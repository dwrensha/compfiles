/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Order.IntermediateValue
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1962, Problem 5

Given three distinct points A, B, C on a circle K, construct a point D on K,
such that a circle can be inscribed in ABCD.
-/

namespace Imo1962P5

open Real

/-- Parametrization of the unit circle by angle. -/
noncomputable def pt (t : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![Real.cos t, Real.sin t]

snip begin

/-- Chord length on the unit circle, in absolute-value form. -/
theorem dist_pt (s t : ℝ) : dist (pt s) (pt t) = 2 * |Real.sin ((s - t) / 2)| := by
  have h1 : Real.cos s * Real.cos t + Real.sin s * Real.sin t = Real.cos (s - t) :=
    (Real.cos_sub s t).symm
  have h2 : Real.cos (s - t) = 1 - 2 * Real.sin ((s - t) / 2) ^ 2 := by
    have h := Real.cos_two_mul' ((s - t) / 2)
    rw [show 2 * ((s - t) / 2) = s - t by ring, Real.cos_sq'] at h
    linarith
  have h3 : (∑ i, dist (pt s i) (pt t i) ^ 2) = 2 ^ 2 * Real.sin ((s - t) / 2) ^ 2 := by
    have e1 := Real.cos_sq_add_sin_sq s
    have e2 := Real.cos_sq_add_sin_sq t
    simp only [Fin.sum_univ_two, pt, PiLp.toLp_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Real.dist_eq, sq_abs]
    linear_combination e1 + e2 - 2 * h1 - 2 * h2
  rw [EuclideanSpace.dist_eq, h3, ← mul_pow, Real.sqrt_sq_eq_abs, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- Chord length with the sign resolved, for `t ∈ [s, s + 2π]`. -/
theorem dist_pt_of_le {s t : ℝ} (h0 : s ≤ t) (h1 : t ≤ s + 2 * π) :
    dist (pt s) (pt t) = 2 * Real.sin ((t - s) / 2) := by
  have hnn : 0 ≤ Real.sin ((t - s) / 2) := by
    apply Real.sin_nonneg_of_mem_Icc
    exact ⟨by linarith, by linarith⟩
  rw [dist_pt, show (s - t) / 2 = -((t - s) / 2) by ring, Real.sin_neg, abs_neg,
    abs_of_nonneg hnn]

/-- Points on the unit circle at distinct angles (within one revolution) are
distinct. -/
theorem pt_ne {s t : ℝ} (h0 : s < t) (h1 : t < s + 2 * π) : pt s ≠ pt t := by
  have hpos : 0 < Real.sin ((t - s) / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith
  have hdist : 0 < dist (pt s) (pt t) := by
    rw [dist_pt_of_le h0.le h1.le]
    linarith
  exact dist_pos.mp hdist

/-- The strict triangle inequality, in trigonometric form: going from angle `0`
to angle `x + y` along the unit circle is shorter via the straight chord than
via an intermediate point, when the total arc is less than `π`. -/
theorem sin_sub_lt {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x + y < π) :
    Real.sin x - Real.sin y < Real.sin (x + y) := by
  have h2 := Real.sin_two_mul ((x + y) / 2)
  rw [show 2 * ((x + y) / 2) = x + y by ring] at h2
  rw [Real.sin_sub_sin, h2]
  have hcos : 0 < Real.cos ((x + y) / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    exact ⟨by linarith, by linarith⟩
  have hsin : Real.sin ((x - y) / 2) < Real.sin ((x + y) / 2) := by
    refine Real.strictMonoOn_sin ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
      (by linarith)
  have := mul_lt_mul_of_pos_right hsin hcos
  linarith

/-- `(AD - CD) / 2` for the point `D` at angle `d`, where `A` and `C` are at
angles `a` and `c` on the unit circle. -/
noncomputable def fval (a c d : ℝ) : ℝ := Real.sin ((d - a) / 2) - Real.sin ((d - c) / 2)

theorem fval_continuous (a c : ℝ) : Continuous (fval a c) := by
  unfold fval
  exact (Real.continuous_sin.comp ((continuous_id.sub continuous_const).div_const 2)).sub
    (Real.continuous_sin.comp ((continuous_id.sub continuous_const).div_const 2))

/-- Value of `fval` at the endpoint `d = c`: this is `AC / 2`. -/
theorem fval_left (a c : ℝ) : fval a c c = Real.sin ((c - a) / 2) := by
  unfold fval
  rw [show (c - c) / 2 = 0 by ring, Real.sin_zero, sub_zero]

/-- Value of `fval` at the endpoint `d = a + 2π`: this is `-AC / 2`. -/
theorem fval_right (a c : ℝ) : fval a c (a + 2 * π) = -Real.sin ((c - a) / 2) := by
  unfold fval
  rw [show (a + 2 * π - a) / 2 = π by ring,
    show (a + 2 * π - c) / 2 = π - (c - a) / 2 by ring, Real.sin_pi, Real.sin_pi_sub,
    zero_sub]

snip end

problem imo1962_p5 {a b c : ℝ} (hab : a < b) (hbc : b < c) (hca : c < a + 2 * π) :
    ∃ d : ℝ, c < d ∧ d < a + 2 * π ∧ pt d ≠ pt a ∧ pt d ≠ pt b ∧ pt d ≠ pt c ∧
      dist (pt a) (pt b) + dist (pt c) (pt d) =
        dist (pt b) (pt c) + dist (pt a) (pt d) := by
  have hx : 0 < (b - a) / 2 := by linarith
  have hy : 0 < (c - b) / 2 := by linarith
  have hub : Real.sin ((b - a) / 2) - Real.sin ((c - b) / 2) < Real.sin ((c - a) / 2) := by
    have h := sin_sub_lt hx hy (by linarith)
    rwa [show (b - a) / 2 + (c - b) / 2 = (c - a) / 2 by ring] at h
  have hlb : -Real.sin ((c - a) / 2) <
      Real.sin ((b - a) / 2) - Real.sin ((c - b) / 2) := by
    have h := sin_sub_lt hy hx (by linarith)
    rw [show (c - b) / 2 + (b - a) / 2 = (c - a) / 2 by ring] at h
    linarith
  have hmem : Real.sin ((b - a) / 2) - Real.sin ((c - b) / 2) ∈
      Set.Icc (fval a c (a + 2 * π)) (fval a c c) := by
    rw [fval_right, fval_left]
    exact ⟨hlb.le, hub.le⟩
  obtain ⟨d, hd, hfd⟩ :=
    intermediate_value_Icc' hca.le (fval_continuous a c).continuousOn hmem
  rw [Set.mem_Icc] at hd
  have hcd : c < d := by
    refine lt_of_le_of_ne hd.1 fun h => by rw [← h, fval_left] at hfd; linarith
  have hda : d < a + 2 * π := by
    refine lt_of_le_of_ne hd.2 fun h => by rw [h, fval_right] at hfd; linarith
  refine ⟨d, hcd, hda, (pt_ne (by linarith) hda).symm,
    (pt_ne (by linarith) (by linarith)).symm, (pt_ne hcd (by linarith)).symm, ?_⟩
  have h1 := dist_pt_of_le hab.le (by linarith)
  have h2 := dist_pt_of_le hcd.le (by linarith)
  have h3 := dist_pt_of_le hbc.le (by linarith)
  have h4 := dist_pt_of_le (by linarith : a ≤ d) hda.le
  rw [h1, h2, h3, h4]
  unfold fval at hfd
  linarith

end Imo1962P5
