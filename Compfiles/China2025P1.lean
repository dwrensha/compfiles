/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: sjfhsjfh
-/
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Topology.Algebra.Polynomial

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# China Mathematical Olympiad 2025, Problem 1

定义复数集 ℂ 的子集
  A = {z ∈ ℂ | z = re^{iθ}, r ≥ 0, θ ∈ [0, π/41]},
  B = {z ∈ ℂ | z = x + iy, x, y ∈ ℝ, |x − y| < 2025},
其中 i 是虚数单位，re^{iθ} = r(cos θ + i sin θ)。
求所有的一元复系数多项式 P(z)，使得对任意 z ∈ A，都有 P(z) ∈ B。
（说明：单项式也是多项式。）

Define the subsets of the complex numbers ℂ:
  A = {z ∈ ℂ | z = re^{iθ}, r ≥ 0, θ ∈ [0, π/41]},
  B = {z ∈ ℂ | z = x + iy, x, y ∈ ℝ, |x − y| < 2025},
where i is the imaginary unit, and re^{iθ} = r(cos θ + i sin θ).
Find all complex-coefficient polynomials P(z) such that for every z ∈ A,
we have P(z) ∈ B.
-/

namespace China2025P1

open Complex Polynomial

def A : Set ℂ := {z | arg z ∈ Set.Icc (0 : ℝ) (Real.pi / 41)}

def B : Set ℂ := {z | |z.re - z.im| < 2025}

snip begin

lemma apos : 0 < Real.pi / 41 := div_pos Real.pi_pos Nat.ofNat_pos

lemma mulMemA {r : ℝ} (c : ℂ) (hr : r ≥ 0) : c ∈ A → r • c ∈ A := by
  by_cases! hc : c = 0
  · subst hc; rewrite [smul_zero, imp_self]; trivial
  by_cases! hrc : r • c = 0
  · intro _; have h := smul_eq_zero.mp hrc |>.resolve_right hc
    subst h; simp [A]; exact apos.le
  simp only [A, Set.mem_setOf]; suffices h : c.arg = (r • c).arg by
    rewrite [h, imp_self]; trivial
  refine arg_eq_arg_iff hc hrc |>.mpr ?_; simp [abs_of_nonneg hr]; left
  refine Eq.symm <| eq_div_of_mul_eq ?_ rfl
  rewrite [ne_eq, ofReal_eq_zero, norm_eq_zero]; exact hc

lemma memBIff (z : ℂ) : z ∈ B ↔
  |inner ℝ (1 - I) z| < 2025 := by
  simp [B, Complex.inner]

lemma innerPolynomial {P : Polynomial ℂ} {c z : ℂ}
  : inner ℝ c (P.eval z) = P.sum fun e a ↦ inner ℝ c (a * z ^ e) := by
  rw [eval_eq_sum_range, sum_over_range P
    (by simp only [zero_mul, inner_zero_right, implies_true]), inner_sum]

lemma existsTheta (P : Polynomial ℂ) (hP : P ≠ 0) (hP' : ¬ IsUnit P)
  : ∃ (θ : ℝ), exp (I * θ) ∈ A
    ∧ inner ℝ (1 - I) (P.leadingCoeff * exp (I * θ * P.natDegree)) ≠ 0 := by
  simp only [mul_comm I _, A, Set.mem_setOf, arg_exp_mul_I, mul_ne_zero_iff,
    ← InnerProductGeometry.cos_angle_mul_norm_mul_norm, norm_ne_zero_iff, sub_ne_zero]
  have honeneI : (1 : ℂ) ≠ I := by
    by_contra h; have := congr_arg Complex.re h; simp at this
  simp [hP, honeneI, InnerProductGeometry.cos_eq_zero_iff_angle_eq_pi_div_two]
  suffices h : ∃ θ, θ ∈ Set.Icc (0 : ℝ) (Real.pi / 41)
    ∧ InnerProductGeometry.angle (1 - I) (P.leadingCoeff * cexp (↑θ * I * ↑P.natDegree))
      ≠ Real.pi / 2 by
    obtain ⟨θ, ⟨⟨hl, hr⟩, h2⟩⟩ := h; use θ; simp only [h2, not_false_eq_true, and_true]
    have hθ : θ ∈ Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) := by
      simp only [Set.mem_Ioc, le_neg_add_iff_add_le]; refine ⟨?_, ?_⟩
      · exact lt_of_lt_of_le (neg_neg_of_pos Real.pi_pos) hl
      refine le_sub_iff_add_le'.mp ?_; rewrite [two_mul, add_sub_cancel_left]
      refine le_trans hr <| div_le_iff₀ Nat.ofNat_pos |>.mpr ?_
      exact (le_mul_iff_one_le_right Real.pi_pos).mpr (by norm_num)
    rewrite [toIocMod_eq_self Real.two_pi_pos |>.mpr hθ]; exact ⟨hl, hr⟩
  have hc := leadingCoeff_ne_zero.mpr hP
  have hn := natDegree_pos_iff_degree_pos.mpr <|
    P.degree_pos_of_ne_zero_of_nonunit hP hP'
  set c := P.leadingCoeff; set n := P.natDegree
  by_cases! h : InnerProductGeometry.angle (1 - I) c ≠ Real.pi / 2
  · use 0; simp [apos.le, h]
  have := InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two _ _ |>.mpr h
  simp [sub_eq_zero] at this
  use 1 / 41; simp; refine ⟨?_, ?_⟩
  · refine (le_div_iff₀' Nat.ofNat_pos).mpr ?_
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_inv_cancel₀]
    exact le_trans one_le_two Real.two_le_pi
  rewrite [InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two _ _ |>.symm.not,
    mul_assoc, mul_comm I _, ← mul_assoc, mul_comm 41⁻¹ _, ← div_eq_mul_inv,
    ← ofReal_ofNat, ← ofReal_natCast, ← ofReal_div, ← Rat.cast_natCast, ← Rat.cast_ofNat,
    ← Rat.cast_div, exp_mul_I]; set q : ℚ := n / 41
  simp [this, mul_add, sub_eq_add_neg]
  simp only [← ofReal_ratCast, ← ofReal_sin, ← ofReal_cos, ofReal_im, ofReal_re]
  simp only [mul_zero, neg_zero, add_zero, zero_add]
  rewrite [add_comm (_ + _), add_assoc, ← add_assoc _ _ (-_), neg_add_cancel, zero_add,
    add_self_eq_zero, neg_eq_zero, ← ne_eq, mul_ne_zero_iff]; refine ⟨?_, ?_⟩
  · by_contra h; absurd hc; refine Complex.ext_iff.mpr ?_
    rewrite [this, h]; simp only [zero_re, zero_im, and_self]
  refine Real.sin_ne_zero_iff.mpr ?_; intro m
  by_cases! hm : m = 0
  · by_contra! h; subst hm; simp [q] at h
    have := div_eq_zero_iff.mp h.symm |>.resolve_right Nat.ofNat_pos.ne.symm
    simp only [Nat.cast_eq_zero] at this; simp only [this, lt_self_iff_false] at hn
  rewrite [ne_eq, mul_comm, ← div_eq_iff_mul_eq <| Int.cast_ne_zero.mpr hm,
    show (↑m : ℝ) = ↑(↑m : ℚ) by exact Real.ext_cauchy rfl, ← Rat.cast_div, Eq.comm]
  exact Irrational.ne_rat irrational_pi (q / ↑m)

lemma existsQ (P : Polynomial ℂ) (hPne : ∀ (r : ℂ), r.re = r.im → P ≠ C r)
  : ∃ Q : Polynomial ℝ, ∃ f : ℝ → ℂ, (∀ r ≥ 0, f r ∈ A) ∧ Q.degree = P.degree
    ∧ ∀ r : ℝ, P.sum (fun e a ↦ inner ℝ (1 - I) (a * f r ^ e)) = Q.eval r := by
  by_cases! hP : P = 0
  · subst hP; simp; use fun r ↦ r; intro r hr; simp [A, arg_ofReal_of_nonneg hr]
    exact apos.le
  by_cases! hP' : IsUnit P
  · obtain ⟨r, ⟨hr, hP''⟩⟩ := Polynomial.isUnit_iff.mp hP'
    use C (inner ℝ (1 - I) r), fun r ↦ r; simp [← hP'', A]
    refine ⟨by intro r hr; simp [arg_ofReal_of_nonneg hr]; exact apos.le, ?_⟩
    simp only [isUnit_iff_ne_zero] at hr; rewrite [degree_C hr, ← C_sub]
    refine degree_C <| sub_ne_zero_of_ne ?_; by_contra h; absurd hP''.symm
    exact hPne r h
  obtain ⟨θ, ⟨hθA, hθinner⟩⟩ := existsTheta P hP hP'
  let f : ℝ → ℂ := fun r ↦ r • exp (I * θ)
  have (r : ℝ) : r ≥ 0 → f r ∈ A := by
    intro hr; rewrite [show f r = r • f 1 by simp only [one_smul, f]]
    refine mulMemA _ hr ?_; simp only [f, one_smul]; exact hθA
  let qcoeff := fun (n : ℕ) ↦ inner ℝ (1 - I) (P.coeff n * exp (I * θ * n))
  let Q : Polynomial ℝ := ⟨.ofCoeff ⟨Finset.filter (fun n ↦ qcoeff n ≠ 0) P.support, qcoeff,
    fun a ↦ by simp; by_contra! h; obtain ⟨hqa, hPa⟩ := h; absurd hqa; simp [qcoeff, hPa]⟩⟩
  have hQ : Q ≠ 0 := by
    by_contra hQ
    have : Q.coeff P.natDegree = 0 := by simp [hQ]
    simp [Q, AddMonoidAlgebra.ofCoeff] at this; unfold qcoeff at this
    absurd hθinner; exact this
  use Q, f
  suffices h_deg : Q.degree = P.degree by
    refine ⟨this, h_deg, ?_⟩
    intro r;
    rewrite [eval_eq_sum_range, sum_over_range P (by simp), natDegree_eq_of_degree_eq h_deg]
    congr 1; ext n; unfold f; rewrite [real_smul, mul_pow, mul_comm, mul_assoc,
      ← ofReal_pow, ← real_smul, inner_smul_right, mul_comm]; congr 2
    rewrite [mul_comm _ (P.coeff n), mul_comm (_ * _), exp_nat_mul]; rfl
  have := degree_le_of_natDegree_le <| le_natDegree_of_ne_zero (p := Q) hθinner
  rewrite [← degree_eq_natDegree hQ] at this; refine eq_of_ge_of_le this ?_
  simp [degree, Q, AddMonoidAlgebra.ofCoeff]; push Not; intro n hPn hQn
  exact le_degree_of_ne_zero hPn

example (p : ℝ[X]) (hdeg : 0 < p.degree) (M : ℝ) :
    ∃ r : ℝ, M < |p.eval r| := by
  have htend := p.tendsto_norm_atTop hdeg Filter.tendsto_abs_atTop_atTop
  rw [Filter.tendsto_atTop] at htend; have hev := htend (M + 1)
  obtain ⟨r, ⟨hr, hrpos⟩⟩ := hev.and (Filter.eventually_gt_atTop (0 : ℝ)) |>.exists
  use r
  have : M < M + 1 := by exact lt_add_one M
  exact lt_of_lt_of_le this hr

snip end

determine answer : Set (Polynomial ℂ) := {P | ∃ c ∈ B, P = C c}

problem china2025_p1 (P : Polynomial ℂ)
  : P ∈ answer ↔ ∀ z ∈ A, P.eval z ∈ B := by
  refine ⟨?_, ?_⟩
  · intro hP _ _; simp only [answer, Set.mem_setOf] at hP
    obtain ⟨c, ⟨hc, hPc⟩⟩ := hP; rewrite [hPc, eval_C]; exact hc
  intro h; simp only [Set.mem_setOf]; use P.coeff 0
  by_cases! h_degree : P.degree ≤ 0
  · refine ⟨?_, eq_C_of_degree_le_zero h_degree⟩
    have h' := h 0; rewrite [eq_C_of_degree_le_zero h_degree] at h'; simp [A] at h'
    exact h' <| apos.le
  by_cases! hP : ∃ r : ℂ, r.re = r.im ∧ P = C r
  · obtain ⟨r, ⟨hr, hP⟩⟩ := hP; simp [hP, B, hr]
  exfalso; simp only [memBIff, innerPolynomial] at h
  obtain ⟨Q, z, ⟨hz, hQdeg, heq⟩⟩ := existsQ P hP; rewrite [← hQdeg] at h_degree
  have htend := Q.tendsto_norm_atTop h_degree Filter.tendsto_abs_atTop_atTop
  rewrite [Filter.tendsto_atTop] at htend; have hev := htend 2025
  obtain ⟨r, ⟨hr, hrpos⟩⟩ := hev.and (Filter.eventually_gt_atTop (0 : ℝ)) |>.exists
  absurd fun r hr ↦ h (z r) (hz r hr); push Not; use r; rewrite [Real.norm_eq_abs] at hr
  rewrite [heq r]; exact ⟨hrpos.le, hr⟩

end China2025P1
