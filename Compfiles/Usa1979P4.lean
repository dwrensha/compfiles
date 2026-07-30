/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.EuclideanDomain.Basic
public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 1979, Problem 4

P lies between the rays OA and OB. Find Q on OA and R on OB collinear with P
so that 1/PQ + 1/PR is as large as possible.

# Answer

1/PQ + 1/PR is as large as possible exactly when QR is perpendicular to OP.

# Formalization notes

We place O at the origin of an arbitrary real inner product space (the whole
configuration lives in the plane spanned by the two rays anyway).  Let `u` and
`v` be the unit vectors along the rays OA and OB, and write P = a • u + b • v.
The hypothesis `0 < a` and `0 < b` says precisely that P lies strictly between
the two rays.  Points Q on ray OA and R on ray OB are written as `q • u` and
`r • v` with `0 < q` and `0 < r`; collinearity with P is expressed by the
existence of a real number `t` with `P = (1 - t) • Q + t • R`.

The answer "QR ⟂ OP" is only achievable when the line through P perpendicular
to OP actually meets both rays in their positive direction.  Algebraically this
is the condition `0 < a + b * ⟪u, v⟫` and `0 < b + a * ⟪u, v⟫` (which is
automatic when the angle AOB is not obtuse, since then `0 ≤ ⟪u, v⟫`), and we
assume it as a hypothesis.  Under this hypothesis we prove that the maximum
value of `1/PQ + 1/PR` is
`Real.sqrt (a^2 + b^2 + 2*a*b*⟪u,v⟫) / (a * b * Real.sqrt (1 - ⟪u,v⟫^2))`
and that it is attained exactly for the configuration with QR perpendicular
to OP.
-/

namespace Usa1979P4

open scoped RealInnerProductSpace

snip begin

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {u v : E} {a b : ℝ}

/-- The cosine of the angle AOB is strictly between -1 and 1, since the two
rays are distinct and not opposite. -/
lemma inner_sq_lt_one (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : LinearIndependent ℝ ![u, v]) : ⟪u, v⟫ ^ 2 < 1 := by
  have hcs : |⟪u, v⟫| ≤ 1 := by
    have h := abs_real_inner_le_norm u v
    rwa [hu, hv, mul_one] at h
  have hle : ⟪u, v⟫ ^ 2 ≤ 1 := by
    have h1 := abs_le.mp hcs
    nlinarith [h1.1, h1.2, sq_nonneg ⟪u, v⟫]
  refine lt_of_le_of_ne hle fun heq => ?_
  rw [sq_eq_one_iff] at heq
  have hne : ∀ g : Fin 2 → ℝ, (∑ i, g i • ![u, v] i) = 0 → ∀ i, g i = 0 :=
    (Fintype.linearIndependent_iff).1 huv
  rcases heq with h1 | hm1
  · have h0 : u = v := by
      have h2 : ‖u - v‖ ^ 2 = 0 := by
        rw [norm_sub_sq_real, hu, hv, h1]
        norm_num
      rw [pow_eq_zero_iff two_ne_zero, norm_eq_zero] at h2
      exact sub_eq_zero.mp h2
    have h3 := hne ![1, -1] (by simp [Fin.sum_univ_two, h0]) 0
    simp at h3
  · have h0 : u = -v := by
      have h2 : ‖u + v‖ ^ 2 = 0 := by
        rw [norm_add_sq_real, hu, hv, hm1]
        norm_num
      rw [pow_eq_zero_iff two_ne_zero, norm_eq_zero] at h2
      exact eq_neg_of_add_eq_zero_left h2
    have h3 := hne ![1, 1] (by simp [Fin.sum_univ_two, h0]) 0
    simp at h3

/-- Coordinates with respect to the linearly independent pair `![u, v]` are
unique. -/
lemma coord_unique (huv : LinearIndependent ℝ ![u, v]) {x y x' y' : ℝ}
    (h : x • u + y • v = x' • u + y' • v) : x = x' ∧ y = y' := by
  have h2 : (x - x') • u + (y - y') • v = 0 := by
    have e : (x - x') • u + (y - y') • v = (x • u + y • v) - (x' • u + y' • v) := by
      module
    rw [h, sub_self] at e
    exact e
  have hli := (Fintype.linearIndependent_iff).1 huv ![x - x', y - y'] (by
    simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using h2)
  refine ⟨?_, ?_⟩
  · have h0 := hli 0
    simpa only [Matrix.cons_val_zero, sub_eq_zero] using h0
  · have h1 := hli 1
    simpa only [Matrix.cons_val_one, Matrix.cons_val_zero, sub_eq_zero] using h1

/-- The squared norm of a linear combination of the two unit vectors. -/
lemma norm_sq_combo (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (x y : ℝ) :
    ‖x • u + y • v‖ ^ 2 = x ^ 2 + y ^ 2 + 2 * x * y * ⟪u, v⟫ := by
  rw [norm_add_sq_real, norm_smul, norm_smul, hu, hv, mul_one, mul_one,
    Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs,
    real_inner_smul_left, real_inner_smul_right]
  ring

/-- The squared distance QR is always positive. -/
lemma qr_pos (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : LinearIndependent ℝ ![u, v])
    {q r : ℝ} (hq : 0 < q) (hr : 0 < r) :
    0 < q ^ 2 + r ^ 2 - 2 * q * r * ⟪u, v⟫ := by
  have hc : ⟪u, v⟫ < 1 := by nlinarith [inner_sq_lt_one hu hv huv]
  nlinarith [sq_nonneg (q - r), mul_pos hq hr, hc]

/-- The collinearity condition `P ∈ QR` in algebraic form: with
P = a • u + b • v, Q = q • u, R = r • v, the points Q, P, R are collinear
iff `a/q + b/r = 1`.  This is the key equation of the problem. -/
lemma hqr_of_constraint {q r : ℝ} (hq : 0 < q) (hr : 0 < r)
    (h : a / q + b / r = 1) : q * r = a * r + b * q := by
  have h1 := h
  rw [div_add_div _ _ hq.ne' hr.ne', div_eq_one_iff_eq (mul_ne_zero hq.ne' hr.ne')] at h1
  linarith

/-- The key algebraic identity behind the maximization: writing
`K = a^2 + b^2 + 2ab·c` (the squared length of OP) and
`D = q^2 + r^2 - 2qr·c` (the squared length of QR), the defect
`K·D - q²r²(1-c²)` is, up to the positive factor `(q/a)²`, a perfect square.
It vanishes exactly when `K = (b + ac)·r`, which is the perpendicularity
condition. -/
lemma key_identity {q r : ℝ} (hq : 0 < q) (hr : 0 < r)
    (h : a / q + b / r = 1) (c : ℝ) :
    a ^ 2 * ((a ^ 2 + b ^ 2 + 2 * a * b * c) * (q ^ 2 + r ^ 2 - 2 * q * r * c) -
        q ^ 2 * r ^ 2 * (1 - c ^ 2)) =
      q ^ 2 * ((a ^ 2 + b ^ 2 + 2 * a * b * c) - (b + a * c) * r) ^ 2 := by
  have hqr : q * r = a * r + b * q := hqr_of_constraint hq hr h
  have h3 : q * r - a * r - b * q = 0 := by linarith
  linear_combination
    (-(a ^ 2 + b ^ 2 + 2 * a * b * c) * ((q + a) * r - q * (b + 2 * a * c))) * h3

/-- Collinearity implies the algebraic constraint. -/
lemma constraint_of_collinear (huv : LinearIndependent ℝ ![u, v]) {q r : ℝ} (hq : 0 < q) (hr : 0 < r)
    (h : ∃ t : ℝ, a • u + b • v = (1 - t) • (q • u) + t • (r • v)) :
    a / q + b / r = 1 := by
  obtain ⟨t, ht⟩ := h
  rw [← mul_smul, ← mul_smul] at ht
  obtain ⟨ha', hb'⟩ := coord_unique huv ht
  rw [ha', hb', mul_div_cancel_right₀ (1 - t) hq.ne', mul_div_cancel_right₀ t hr.ne']
  ring

/-- The algebraic constraint implies collinearity. -/
lemma collinear_of_constraint {q r : ℝ} (hq : 0 < q) (hr : 0 < r)
    (h : a / q + b / r = 1) :
    ∃ t : ℝ, a • u + b • v = (1 - t) • (q • u) + t • (r • v) := by
  refine ⟨b / r, ?_⟩
  have h1 : (1 : ℝ) - b / r = a / q := by linarith
  rw [h1, ← mul_smul, ← mul_smul, div_mul_cancel₀ a hq.ne', div_mul_cancel₀ b hr.ne']

/-- The objective function `1/PQ + 1/PR` in terms of `q` and `r`:
it equals `q*r / (a*b*QR)`.  Indeed P divides QR with `PQ = (b/r)·QR` and
`PR = (a/q)·QR`, so `1/PQ + 1/PR = (r/b + q/a)/QR = qr/(ab·QR)` using
`ar + bq = qr`. -/
lemma objective_formula (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : LinearIndependent ℝ ![u, v])
    (ha : 0 < a) (hb : 0 < b) {q r : ℝ} (hq : 0 < q) (hr : 0 < r)
    (h : a / q + b / r = 1) :
    1 / dist (a • u + b • v) (q • u) + 1 / dist (a • u + b • v) (r • v) =
      q * r / (a * b * Real.sqrt (q ^ 2 + r ^ 2 - 2 * q * r * ⟪u, v⟫)) := by
  have hqr : q * r = a * r + b * q := hqr_of_constraint hq hr h
  have hD : 0 < Real.sqrt (q ^ 2 + r ^ 2 - 2 * q * r * ⟪u, v⟫) :=
    Real.sqrt_pos.mpr (qr_pos hu hv huv hq hr)
  have hbr : 0 < b / r := div_pos hb hr
  have haq : 0 < a / q := div_pos ha hq
  -- P - Q = (b/r) • (R - Q)
  have hPQ : (a • u + b • v) - q • u = (b / r) • (r • v - q • u) := by
    have hcoef0 : (a - q) * r + b * q = 0 := by linear_combination -hqr
    have hcoef : (a - q) + (b / r) * q = 0 := by
      rw [div_mul_eq_mul_div, add_div' (b * q) (a - q) r hr.ne', div_eq_zero_iff]
      exact Or.inl hcoef0
    have e : (a • u + b • v) - q • u = (a - q) • u + b • v := by module
    have e2 : (b / r) • (r • v - q • u) = (-(b / r) * q) • u + b • v := by
      rw [smul_sub, ← mul_smul, ← mul_smul, div_mul_cancel₀ b hr.ne']
      module
    rw [e, e2, show (a - q) = -(b / r) * q from by linarith [hcoef]]
  -- P - R = (a/q) • (Q - R)
  have hPR : (a • u + b • v) - r • v = (a / q) • (q • u - r • v) := by
    have hcoef0 : (b - r) * q + a * r = 0 := by linear_combination -hqr
    have hcoef : (b - r) + (a / q) * r = 0 := by
      rw [div_mul_eq_mul_div, add_div' (a * r) (b - r) q hq.ne', div_eq_zero_iff]
      exact Or.inl hcoef0
    have e : (a • u + b • v) - r • v = a • u + (b - r) • v := by module
    have e2 : (a / q) • (q • u - r • v) = (a / q * q) • u - (a / q * r) • v := by
      rw [smul_sub, ← mul_smul, ← mul_smul]
    rw [e, e2, div_mul_cancel₀ a hq.ne', show (b - r) = -(a / q * r) from by linarith [hcoef],
      neg_smul, sub_eq_add_neg]
  -- the length of QR
  have hnorm : ‖r • v - q • u‖ = Real.sqrt (q ^ 2 + r ^ 2 - 2 * q * r * ⟪u, v⟫) := by
    have hsq : ‖r • v - q • u‖ ^ 2 = q ^ 2 + r ^ 2 - 2 * q * r * ⟪u, v⟫ := by
      rw [sub_eq_add_neg, ← neg_smul, ← add_comm ((-q) • u) (r • v), norm_sq_combo hu hv]
      ring
    rw [← hsq]
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  rw [dist_eq_norm, dist_eq_norm, hPQ, hPR, norm_smul, norm_smul,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hbr, abs_of_pos haq,
    show q • u - r • v = -(r • v - q • u) by module, norm_neg, hnorm]
  have e1 : 1 / ((b / r) * Real.sqrt (q ^ 2 + r ^ 2 - 2 * q * r * ⟪u, v⟫)) =
      r / (b * Real.sqrt (q ^ 2 + r ^ 2 - 2 * q * r * ⟪u, v⟫)) := by
    field_simp [hD.ne', hb.ne', hr.ne']
  have e2 : 1 / ((a / q) * Real.sqrt (q ^ 2 + r ^ 2 - 2 * q * r * ⟪u, v⟫)) =
      q / (a * Real.sqrt (q ^ 2 + r ^ 2 - 2 * q * r * ⟪u, v⟫)) := by
    field_simp [hD.ne', ha.ne', hq.ne']
  rw [e1, e2]
  have h5 : r / b + q / a = q * r / (a * b) := by
    rw [div_add_div _ _ hb.ne' ha.ne', div_eq_div_iff (mul_ne_zero hb.ne' ha.ne')
      (mul_ne_zero ha.ne' hb.ne')]
    linear_combination (a * b) * hqr.symm
  rw [← div_div, ← div_div, ← add_div, ← div_div, h5]

/-- The perpendicularity inner product expands as
`r(b + ac) - q(a + bc)`. -/
lemma inner_qr_op (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) {q r : ℝ} :
    ⟪r • v - q • u, a • u + b • v⟫ =
      r * (b + a * ⟪u, v⟫) - q * (a + b * ⟪u, v⟫) := by
  simp only [inner_sub_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, hu, hv, real_inner_comm u v]
  ring

/-- The maximum is attained exactly when `K = (b + ac)·r`, which under the
constraint is the same as QR perpendicular to OP. -/
lemma objective_eq_iff (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : LinearIndependent ℝ ![u, v])
    (ha : 0 < a) (hb : 0 < b) {q r : ℝ} (hq : 0 < q) (hr : 0 < r)
    (h : a / q + b / r = 1) :
    1 / dist (a • u + b • v) (q • u) + 1 / dist (a • u + b • v) (r • v) =
      Real.sqrt (a ^ 2 + b ^ 2 + 2 * a * b * ⟪u, v⟫) /
        (a * b * Real.sqrt (1 - ⟪u, v⟫ ^ 2)) ↔
      (a ^ 2 + b ^ 2 + 2 * a * b * ⟪u, v⟫) = (b + a * ⟪u, v⟫) * r := by
  rw [objective_formula hu hv huv ha hb hq hr h]
  have hc : ⟪u, v⟫ ^ 2 < 1 := inner_sq_lt_one hu hv huv
  have h1c : 0 < 1 - ⟪u, v⟫ ^ 2 := by linarith
  have hK : 0 < a ^ 2 + b ^ 2 + 2 * a * b * ⟪u, v⟫ := by
    have hm1 : -1 < ⟪u, v⟫ := by nlinarith [hc]
    nlinarith [sq_nonneg (a - b), mul_pos ha hb, hm1]
  have hD : 0 < q ^ 2 + r ^ 2 - 2 * q * r * ⟪u, v⟫ := qr_pos hu hv huv hq hr
  have hD' : 0 < Real.sqrt (q ^ 2 + r ^ 2 - 2 * q * r * ⟪u, v⟫) := Real.sqrt_pos.mpr hD
  have h1c' : 0 < Real.sqrt (1 - ⟪u, v⟫ ^ 2) := Real.sqrt_pos.mpr h1c
  rw [div_eq_div_iff (mul_ne_zero (mul_ne_zero ha.ne' hb.ne') hD'.ne')
    (mul_ne_zero (mul_ne_zero ha.ne' hb.ne') h1c'.ne')]
  have key2 : q * r * (a * b * Real.sqrt (1 - ⟪u, v⟫ ^ 2)) =
        Real.sqrt (a ^ 2 + b ^ 2 + 2 * a * b * ⟪u, v⟫) *
          (a * b * Real.sqrt (q ^ 2 + r ^ 2 - 2 * q * r * ⟪u, v⟫)) ↔
      q * r * Real.sqrt (1 - ⟪u, v⟫ ^ 2) =
        Real.sqrt (a ^ 2 + b ^ 2 + 2 * a * b * ⟪u, v⟫) *
          Real.sqrt (q ^ 2 + r ^ 2 - 2 * q * r * ⟪u, v⟫) := by
    constructor
    · intro h2
      have h3 := mul_left_cancel₀ (mul_ne_zero ha.ne' hb.ne')
        (show a * b * (q * r * Real.sqrt (1 - ⟪u, v⟫ ^ 2)) =
          a * b * (Real.sqrt (a ^ 2 + b ^ 2 + 2 * a * b * ⟪u, v⟫) *
            Real.sqrt (q ^ 2 + r ^ 2 - 2 * q * r * ⟪u, v⟫)) by linear_combination h2)
      exact h3
    · intro h2
      linear_combination (a * b) * h2
  have key3 : q * r * Real.sqrt (1 - ⟪u, v⟫ ^ 2) =
        Real.sqrt (a ^ 2 + b ^ 2 + 2 * a * b * ⟪u, v⟫) *
          Real.sqrt (q ^ 2 + r ^ 2 - 2 * q * r * ⟪u, v⟫) ↔
      q ^ 2 * r ^ 2 * (1 - ⟪u, v⟫ ^ 2) =
        (a ^ 2 + b ^ 2 + 2 * a * b * ⟪u, v⟫) * (q ^ 2 + r ^ 2 - 2 * q * r * ⟪u, v⟫) := by
    constructor
    · intro h2
      have h3 := congrArg (· ^ 2) h2
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt h1c.le, Real.sq_sqrt hK.le,
        Real.sq_sqrt hD.le] at h3
      linear_combination h3
    · intro h2
      have h3 := congrArg Real.sqrt h2
      rwa [Real.sqrt_mul (mul_nonneg (sq_nonneg q) (sq_nonneg r)), Real.sqrt_mul (sq_nonneg q),
        Real.sqrt_sq hq.le, Real.sqrt_sq hr.le, Real.sqrt_mul hK.le] at h3
  have hid := key_identity hq hr h ⟪u, v⟫
  have key4 : q ^ 2 * r ^ 2 * (1 - ⟪u, v⟫ ^ 2) =
        (a ^ 2 + b ^ 2 + 2 * a * b * ⟪u, v⟫) * (q ^ 2 + r ^ 2 - 2 * q * r * ⟪u, v⟫) ↔
      (a ^ 2 + b ^ 2 + 2 * a * b * ⟪u, v⟫) = (b + a * ⟪u, v⟫) * r := by
    constructor
    · intro h2
      have h3 : q ^ 2 * ((a ^ 2 + b ^ 2 + 2 * a * b * ⟪u, v⟫) -
          (b + a * ⟪u, v⟫) * r) ^ 2 = 0 := by
        linear_combination -hid - a ^ 2 * h2
      have h4 : ((a ^ 2 + b ^ 2 + 2 * a * b * ⟪u, v⟫) - (b + a * ⟪u, v⟫) * r) ^ 2 = 0 :=
        (mul_eq_zero.mp h3).resolve_left (pow_ne_zero 2 hq.ne')
      have h5 : (a ^ 2 + b ^ 2 + 2 * a * b * ⟪u, v⟫) - (b + a * ⟪u, v⟫) * r = 0 :=
        (pow_eq_zero_iff two_ne_zero).mp h4
      exact sub_eq_zero.mp h5
    · intro h2
      have h2' : (a ^ 2 + b ^ 2 + 2 * a * b * ⟪u, v⟫) - (b + a * ⟪u, v⟫) * r = 0 :=
        sub_eq_zero.mpr h2
      have h3 : a ^ 2 * ((a ^ 2 + b ^ 2 + 2 * a * b * ⟪u, v⟫) *
          (q ^ 2 + r ^ 2 - 2 * q * r * ⟪u, v⟫) - q ^ 2 * r ^ 2 * (1 - ⟪u, v⟫ ^ 2)) = 0 := by
        linear_combination
          hid + (q ^ 2 * ((a ^ 2 + b ^ 2 + 2 * a * b * ⟪u, v⟫) - (b + a * ⟪u, v⟫) * r)) * h2'
      have h4 : (a ^ 2 + b ^ 2 + 2 * a * b * ⟪u, v⟫) *
          (q ^ 2 + r ^ 2 - 2 * q * r * ⟪u, v⟫) - q ^ 2 * r ^ 2 * (1 - ⟪u, v⟫ ^ 2) = 0 :=
        (mul_eq_zero.mp h3).resolve_left (pow_ne_zero 2 ha.ne')
      linear_combination -h4
  exact key2.trans (key3.trans key4)

/-- The upper bound: `1/PQ + 1/PR` never exceeds the claimed maximum. -/
lemma objective_le (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : LinearIndependent ℝ ![u, v])
    (ha : 0 < a) (hb : 0 < b) {q r : ℝ} (hq : 0 < q) (hr : 0 < r)
    (h : a / q + b / r = 1) :
    1 / dist (a • u + b • v) (q • u) + 1 / dist (a • u + b • v) (r • v) ≤
      Real.sqrt (a ^ 2 + b ^ 2 + 2 * a * b * ⟪u, v⟫) /
        (a * b * Real.sqrt (1 - ⟪u, v⟫ ^ 2)) := by
  rw [objective_formula hu hv huv ha hb hq hr h]
  have hc : ⟪u, v⟫ ^ 2 < 1 := inner_sq_lt_one hu hv huv
  have h1c : 0 < 1 - ⟪u, v⟫ ^ 2 := by linarith
  have hK : 0 < a ^ 2 + b ^ 2 + 2 * a * b * ⟪u, v⟫ := by
    have hm1 : -1 < ⟪u, v⟫ := by nlinarith [hc]
    nlinarith [sq_nonneg (a - b), mul_pos ha hb, hm1]
  have hD : 0 < q ^ 2 + r ^ 2 - 2 * q * r * ⟪u, v⟫ := qr_pos hu hv huv hq hr
  have hD' : 0 < Real.sqrt (q ^ 2 + r ^ 2 - 2 * q * r * ⟪u, v⟫) := Real.sqrt_pos.mpr hD
  have h1c' : 0 < Real.sqrt (1 - ⟪u, v⟫ ^ 2) := Real.sqrt_pos.mpr h1c
  have hsq : q ^ 2 * r ^ 2 * (1 - ⟪u, v⟫ ^ 2) ≤
      (a ^ 2 + b ^ 2 + 2 * a * b * ⟪u, v⟫) * (q ^ 2 + r ^ 2 - 2 * q * r * ⟪u, v⟫) := by
    have hid := key_identity hq hr h ⟪u, v⟫
    have hnn : 0 ≤ q ^ 2 * ((a ^ 2 + b ^ 2 + 2 * a * b * ⟪u, v⟫) -
        (b + a * ⟪u, v⟫) * r) ^ 2 := by positivity
    have h2 : 0 ≤ a ^ 2 * ((a ^ 2 + b ^ 2 + 2 * a * b * ⟪u, v⟫) *
        (q ^ 2 + r ^ 2 - 2 * q * r * ⟪u, v⟫) - q ^ 2 * r ^ 2 * (1 - ⟪u, v⟫ ^ 2)) := by
      rw [hid]
      exact hnn
    have hX : 0 ≤ (a ^ 2 + b ^ 2 + 2 * a * b * ⟪u, v⟫) *
        (q ^ 2 + r ^ 2 - 2 * q * r * ⟪u, v⟫) - q ^ 2 * r ^ 2 * (1 - ⟪u, v⟫ ^ 2) :=
      (mul_nonneg_iff_of_pos_left (sq_pos_of_pos ha)).mp h2
    linarith [hX]
  have hsqrt : q * r * Real.sqrt (1 - ⟪u, v⟫ ^ 2) ≤
      Real.sqrt (a ^ 2 + b ^ 2 + 2 * a * b * ⟪u, v⟫) *
        Real.sqrt (q ^ 2 + r ^ 2 - 2 * q * r * ⟪u, v⟫) := by
    have h2 := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_mul (mul_nonneg (sq_nonneg q) (sq_nonneg r)), Real.sqrt_mul (sq_nonneg q),
      Real.sqrt_sq hq.le, Real.sqrt_sq hr.le, Real.sqrt_mul hK.le] at h2
  rw [div_le_div_iff₀ (mul_pos (mul_pos ha hb) hD') (mul_pos (mul_pos ha hb) h1c')]
  nlinarith [mul_le_mul_of_nonneg_left hsqrt (mul_pos ha hb).le]

/-- Under the feasibility hypothesis, `K = (b+ac)·r` is equivalent to the
perpendicularity condition `r(b+ac) = q(a+bc)`, i.e. QR ⟂ OP. -/
lemma perp_iff_of_constraint (ha : 0 < a)
    (hfeas₁ : 0 < a + b * ⟪u, v⟫)
    (hfeas₂ : 0 < b + a * ⟪u, v⟫) {q r : ℝ} (hq : 0 < q) (hr : 0 < r)
    (h : a / q + b / r = 1) :
    (a ^ 2 + b ^ 2 + 2 * a * b * ⟪u, v⟫) = (b + a * ⟪u, v⟫) * r ↔
      r * (b + a * ⟪u, v⟫) = q * (a + b * ⟪u, v⟫) := by
  have hqr : q * r = a * r + b * q := hqr_of_constraint hq hr h
  have h3 : q * r - a * r - b * q = 0 := by linarith
  constructor
  · intro h2
    have h2' : (b + a * ⟪u, v⟫) * r - (a ^ 2 + b ^ 2 + 2 * a * b * ⟪u, v⟫) = 0 := by
      linarith [h2]
    have hrb : r - b ≠ 0 := by
      have h4 : (b + a * ⟪u, v⟫) * (r - b) = a * (a + b * ⟪u, v⟫) := by
        linear_combination h2'
      have h5 : 0 < (b + a * ⟪u, v⟫) * (r - b) := by
        rw [h4]
        exact mul_pos ha hfeas₁
      have h6 : 0 < r - b := (mul_pos_iff_of_pos_left hfeas₂).mp h5
      exact ne_of_gt h6
    have hid : (q * (a + b * ⟪u, v⟫) - (a ^ 2 + b ^ 2 + 2 * a * b * ⟪u, v⟫)) * (r - b) = 0 := by
      linear_combination (a + b * ⟪u, v⟫) * h3 - b * h2'
    have hx : q * (a + b * ⟪u, v⟫) - (a ^ 2 + b ^ 2 + 2 * a * b * ⟪u, v⟫) = 0 :=
      (mul_eq_zero.mp hid).resolve_right hrb
    have h5 : q * (a + b * ⟪u, v⟫) = (a ^ 2 + b ^ 2 + 2 * a * b * ⟪u, v⟫) := by
      linarith [hx]
    rw [mul_comm r (b + a * ⟪u, v⟫), ← h2, ← h5]
  · intro h2
    have h2' : r * (b + a * ⟪u, v⟫) - q * (a + b * ⟪u, v⟫) = 0 := by linarith [h2]
    have hid : ((b + a * ⟪u, v⟫) * r - (a ^ 2 + b ^ 2 + 2 * a * b * ⟪u, v⟫)) * r = 0 := by
      linear_combination (a + b * ⟪u, v⟫) * h3 + (r - b) * h2'
    have h4 : (b + a * ⟪u, v⟫) * r - (a ^ 2 + b ^ 2 + 2 * a * b * ⟪u, v⟫) = 0 :=
      (mul_eq_zero.mp hid).resolve_right hr.ne'
    linarith [h4]

end

snip end

/-- **USA Mathematical Olympiad 1979, Problem 4.**
P lies between the rays OA and OB.  The quantity `1/PQ + 1/PR`, over all
choices of Q on ray OA and R on ray OB collinear with P, attains its maximum
value `Real.sqrt (a^2+b^2+2*a*b*⟪u,v⟫) / (a*b*Real.sqrt (1-⟪u,v⟫^2))`, and it
is attained exactly when QR is perpendicular to OP. -/
problem usa1979_p4
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : LinearIndependent ℝ ![u, v])
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hfeas₁ : 0 < a + b * ⟪u, v⟫) (hfeas₂ : 0 < b + a * ⟪u, v⟫) :
    IsGreatest
      {x : ℝ | ∃ q r : ℝ, 0 < q ∧ 0 < r ∧
        (∃ t : ℝ, a • u + b • v = (1 - t) • (q • u) + t • (r • v)) ∧
        x = 1 / dist (a • u + b • v) (q • u) + 1 / dist (a • u + b • v) (r • v)}
      (Real.sqrt (a ^ 2 + b ^ 2 + 2 * a * b * ⟪u, v⟫) /
        (a * b * Real.sqrt (1 - ⟪u, v⟫ ^ 2))) ∧
    ∀ q r : ℝ, 0 < q → 0 < r →
      (∃ t : ℝ, a • u + b • v = (1 - t) • (q • u) + t • (r • v)) →
      (1 / dist (a • u + b • v) (q • u) + 1 / dist (a • u + b • v) (r • v) =
        Real.sqrt (a ^ 2 + b ^ 2 + 2 * a * b * ⟪u, v⟫) /
          (a * b * Real.sqrt (1 - ⟪u, v⟫ ^ 2)) ↔
        ⟪r • v - q • u, a • u + b • v⟫ = 0) := by
  have hc : ⟪u, v⟫ ^ 2 < 1 := inner_sq_lt_one hu hv huv
  have h1c : 0 < 1 - ⟪u, v⟫ ^ 2 := by linarith
  have hK : 0 < a ^ 2 + b ^ 2 + 2 * a * b * ⟪u, v⟫ := by
    have hm1 : -1 < ⟪u, v⟫ := by nlinarith [hc]
    nlinarith [sq_nonneg (a - b), mul_pos ha hb, hm1]
  -- The witness: the perpendicular configuration
  have hq' : 0 < (a ^ 2 + b ^ 2 + 2 * a * b * ⟪u, v⟫) / (a + b * ⟪u, v⟫) :=
    div_pos hK hfeas₁
  have hr' : 0 < (a ^ 2 + b ^ 2 + 2 * a * b * ⟪u, v⟫) / (b + a * ⟪u, v⟫) :=
    div_pos hK hfeas₂
  have hcon : a / ((a ^ 2 + b ^ 2 + 2 * a * b * ⟪u, v⟫) / (a + b * ⟪u, v⟫)) +
      b / ((a ^ 2 + b ^ 2 + 2 * a * b * ⟪u, v⟫) / (b + a * ⟪u, v⟫)) = 1 := by
    rw [div_div_eq_mul_div, div_div_eq_mul_div, ← add_div, div_eq_one_iff_eq hK.ne']
    ring
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- membership: the maximum value is attained at the perpendicular configuration
    refine ⟨(a ^ 2 + b ^ 2 + 2 * a * b * ⟪u, v⟫) / (a + b * ⟪u, v⟫),
      (a ^ 2 + b ^ 2 + 2 * a * b * ⟪u, v⟫) / (b + a * ⟪u, v⟫), hq', hr',
      collinear_of_constraint hq' hr' hcon, ?_⟩
    have hperp : (a ^ 2 + b ^ 2 + 2 * a * b * ⟪u, v⟫) =
        (b + a * ⟪u, v⟫) *
          ((a ^ 2 + b ^ 2 + 2 * a * b * ⟪u, v⟫) / (b + a * ⟪u, v⟫)) := by
      rw [mul_div_assoc', mul_comm (b + a * ⟪u, v⟫) (a ^ 2 + b ^ 2 + 2 * a * b * ⟪u, v⟫),
        mul_div_cancel_right₀ _ hfeas₂.ne']
    exact ((objective_eq_iff hu hv huv ha hb hq' hr' hcon).mpr hperp).symm
  · -- upper bound
    intro x hx
    obtain ⟨q, r, hq, hr, hcol, rfl⟩ := hx
    exact objective_le hu hv huv ha hb hq hr (constraint_of_collinear huv hq hr hcol)
  · -- the maximizer is exactly the perpendicular configuration
    intro q r hq hr hcol
    have hcon2 : a / q + b / r = 1 := constraint_of_collinear huv hq hr hcol
    rw [inner_qr_op hu hv, sub_eq_zero]
    exact (objective_eq_iff hu hv huv ha hb hq hr hcon2).trans
      (perp_iff_of_constraint ha hfeas₁ hfeas₂ hq hr hcon2)

end Usa1979P4
