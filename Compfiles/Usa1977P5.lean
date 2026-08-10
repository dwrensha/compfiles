/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra, .Inequality] }

/-!
# USA Mathematical Olympiad 1977, Problem 5

The positive reals v, w, x, y, z satisfy 0 < h ≤ v, w, x, y, z ≤ k.
Show that

  (v + w + x + y + z)(1/v + 1/w + 1/x + 1/y + 1/z) ≤ 25 + 6(√(h/k) - √(k/h))².

When do we have equality?
-/

namespace Usa1977P5

snip begin

/-- If `r ≥ 0` and `0 < a ≤ x ≤ b`, then `(r + x) * (s + 1 / x)` is bounded above by the
maximum of its values at the endpoints `x = a` and `x = b` (as a function of `x` it is a
sum of `rs + 1`, the linear function `s * x` and the convex function `r / x`, hence it
attains its maximum on `[a, b]` at an endpoint). -/
lemma le_max_endpoint {r s a b x : ℝ} (hr : 0 ≤ r) (ha : 0 < a) (hb : 0 < b)
    (hax : a ≤ x) (hxb : x ≤ b) :
    (r + x) * (s + 1 / x) ≤ max ((r + a) * (s + 1 / a)) ((r + b) * (s + 1 / b)) := by
  have hx : 0 < x := ha.trans_le hax
  have ha' : a ≠ 0 := ha.ne'
  have hb' : b ≠ 0 := hb.ne'
  have hx' : x ≠ 0 := hx.ne'
  rcases (le_trans hax hxb).eq_or_lt with hab | hab
  · subst hab
    have hxa : x = a := le_antisymm hxb hax
    subst hxa
    exact le_max_left _ _
  · have hba : (0:ℝ) < b - a := sub_pos.mpr hab
    have hba' : b - a ≠ 0 := hba.ne'
    -- Write `x` as the convex combination `x = λ * a + μ * b` with `λ = (b - x)/(b - a)`
    -- and `μ = (x - a)/(b - a)`. The key point is the exact identity
    -- `λ * f a + μ * f b - f x = r * λ * μ * (a - b)² / (a * b * x) ≥ 0`.
    have key : (r + x) * (s + 1 / x) ≤
        ((b - x) / (b - a)) * ((r + a) * (s + 1 / a)) +
        ((x - a) / (b - a)) * ((r + b) * (s + 1 / b)) := by
      have ident : ((b - x) / (b - a)) * ((r + a) * (s + 1 / a)) +
          ((x - a) / (b - a)) * ((r + b) * (s + 1 / b)) - (r + x) * (s + 1 / x)
          = r * ((b - x) * (x - a) * (a - b) ^ 2) / ((b - a) ^ 2 * a * b * x) := by
        field_simp
        ring
      have nonneg : 0 ≤ r * ((b - x) * (x - a) * (a - b) ^ 2) / ((b - a) ^ 2 * a * b * x) :=
        div_nonneg
          (mul_nonneg hr (mul_nonneg (mul_nonneg (sub_nonneg.mpr hxb) (sub_nonneg.mpr hax))
            (sq_nonneg _)))
          (mul_pos (mul_pos (mul_pos (pow_pos hba 2) ha) hb) hx).le
      linarith [ident, nonneg]
    have hlam : (0:ℝ) ≤ (b - x) / (b - a) := div_nonneg (sub_nonneg.mpr hxb) hba.le
    have hmu : (0:ℝ) ≤ (x - a) / (b - a) := div_nonneg (sub_nonneg.mpr hax) hba.le
    have hlamu : (b - x) / (b - a) + (x - a) / (b - a) = 1 := by
      rw [← add_div, sub_add_sub_cancel, div_self hba']
    calc (r + x) * (s + 1 / x)
        ≤ ((b - x) / (b - a)) * ((r + a) * (s + 1 / a)) +
          ((x - a) / (b - a)) * ((r + b) * (s + 1 / b)) := key
      _ ≤ ((b - x) / (b - a)) * max ((r + a) * (s + 1 / a)) ((r + b) * (s + 1 / b)) +
          ((x - a) / (b - a)) * max ((r + a) * (s + 1 / a)) ((r + b) * (s + 1 / b)) :=
        add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) hlam)
          (mul_le_mul_of_nonneg_left (le_max_right _ _) hmu)
      _ = max ((r + a) * (s + 1 / a)) ((r + b) * (s + 1 / b)) := by
        rw [← add_mul, hlamu, one_mul]

/-- `cornerMax h k r s n` is the maximum, over all ways of choosing each of `n` further
variables to be either `h` or `k`, of `(r + sum of the choices) * (s + sum of the
reciprocals of the choices)`. It is defined recursively; the leaves of the recursion are
exactly the `2 ^ n` "corner" values. -/
noncomputable def cornerMax (h k r s : ℝ) : ℕ → ℝ
  | 0 => r * s
  | n + 1 => max (cornerMax h k (r + h) (s + 1 / h) n) (cornerMax h k (r + k) (s + 1 / k) n)

/-- The product `(r + Σ f i) * (s + Σ 1 / f i)`, where each `f i ∈ [h, k]`, is bounded
above by the corresponding corner maximum. Proved by induction on `n`, applying
`le_max_endpoint` to one variable at a time. -/
lemma le_cornerMax (h k : ℝ) (hh : 0 < h) (hk : 0 < k) {n : ℕ} :
    ∀ (f : Fin n → ℝ) (_ : ∀ i, h ≤ f i ∧ f i ≤ k) (r s : ℝ) (_ : 0 ≤ r),
      (r + ∑ i, f i) * (s + ∑ i, 1 / f i) ≤ cornerMax h k r s n := by
  induction n with
  | zero =>
    intro f _ r s _
    have hz1 : ∑ i : Fin 0, f i = 0 := Fin.sum_univ_zero f
    have hz2 : ∑ i : Fin 0, 1 / f i = 0 := Fin.sum_univ_zero (fun i => 1 / f i)
    rw [hz1, hz2, add_zero, add_zero]
    exact le_of_eq rfl
  | succ n ih =>
    intro f hf r s hr
    have hpos : (0:ℝ) ≤ ∑ i : Fin n, f i.succ := by
      refine Finset.sum_nonneg (fun i _ => ?_)
      exact hh.le.trans (hf i.succ).1
    have e1 : ∑ i : Fin (n + 1), f i = f 0 + ∑ i : Fin n, f i.succ := Fin.sum_univ_succ f
    have e2 : ∑ i : Fin (n + 1), 1 / f i = 1 / f 0 + ∑ i : Fin n, 1 / f i.succ :=
      Fin.sum_univ_succ (fun i => 1 / f i)
    rw [e1, e2]
    rw [show (r + (f 0 + ∑ i : Fin n, f i.succ)) * (s + (1 / f 0 + ∑ i : Fin n, 1 / f i.succ)) =
        (r + ∑ i : Fin n, f i.succ + f 0) * (s + ∑ i : Fin n, 1 / f i.succ + 1 / f 0) by ring]
    have cMeq : cornerMax h k r s (n + 1) =
        max (cornerMax h k (r + h) (s + 1 / h) n) (cornerMax h k (r + k) (s + 1 / k) n) := rfl
    rw [cMeq]
    refine le_trans (le_max_endpoint (r := r + ∑ i : Fin n, f i.succ)
      (s := s + ∑ i : Fin n, 1 / f i.succ) (a := h) (b := k) (x := f 0)
      (add_nonneg hr hpos) hh hk (hf 0).1 (hf 0).2) ?_
    refine max_le_max ?_ ?_
    · rw [show (r + ∑ i : Fin n, f i.succ + h) * (s + ∑ i : Fin n, 1 / f i.succ + 1 / h) =
          (r + h + ∑ i : Fin n, f i.succ) * (s + 1 / h + ∑ i : Fin n, 1 / f i.succ) by ring]
      exact ih (fun i => f i.succ) (fun i => hf i.succ) (r + h) (s + 1 / h) (add_nonneg hr hh.le)
    · rw [show (r + ∑ i : Fin n, f i.succ + k) * (s + ∑ i : Fin n, 1 / f i.succ + 1 / k) =
          (r + k + ∑ i : Fin n, f i.succ) * (s + 1 / k + ∑ i : Fin n, 1 / f i.succ) by ring]
      exact ih (fun i => f i.succ) (fun i => hf i.succ) (r + k) (s + 1 / k) (add_nonneg hr hk.le)

snip end

problem usa1977_p5
    (h k v w x y z : ℝ)
    (hh : 0 < h)
    (hv : h ≤ v ∧ v ≤ k) (hw : h ≤ w ∧ w ≤ k) (hx : h ≤ x ∧ x ≤ k)
    (hy : h ≤ y ∧ y ≤ k) (hz : h ≤ z ∧ z ≤ k) :
    (v + w + x + y + z) * (1 / v + 1 / w + 1 / x + 1 / y + 1 / z) ≤
      25 + 6 * (√(h / k) - √(k / h)) ^ 2 := by
  have hk : 0 < k := hh.trans_le (hv.1.trans hv.2)
  have hh' : h ≠ 0 := hh.ne'
  have hk' : k ≠ 0 := hk.ne'
  have hsqrt : (√(h / k) - √(k / h)) ^ 2 = h / k + k / h - 2 := by
    have h2 : √(h / k) * √(k / h) = 1 := by
      rw [← Real.sqrt_mul (div_nonneg hh.le hk.le), div_mul_div_cancel₀ hk',
        div_self hh', Real.sqrt_one]
    calc (√(h / k) - √(k / h)) ^ 2
        = √(h / k) ^ 2 - 2 * (√(h / k) * √(k / h)) + √(k / h) ^ 2 := by ring
      _ = h / k - 2 * 1 + k / h := by
          rw [Real.sq_sqrt (div_nonneg hh.le hk.le), Real.sq_sqrt (div_nonneg hk.le hh.le), h2]
      _ = h / k + k / h - 2 := by ring
  rw [show (25:ℝ) + 6 * (√(h / k) - √(k / h)) ^ 2 = 13 + 6 * (h / k + k / h) by
    rw [hsqrt]; ring]
  have hf : ∀ i : Fin 5, h ≤ ![v, w, x, y, z] i ∧ ![v, w, x, y, z] i ≤ k := by
    intro i
    fin_cases i
    · exact hv
    · exact hw
    · exact hx
    · exact hy
    · exact hz
  have htree := le_cornerMax h k hh hk ![v, w, x, y, z] hf 0 0 (le_refl 0)
  simp only [zero_add] at htree
  have hsum : ∑ i : Fin 5, ![v, w, x, y, z] i = v + w + x + y + z := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
    ring
  have hsumi : ∑ i : Fin 5, 1 / ![v, w, x, y, z] i = 1 / v + 1 / w + 1 / x + 1 / y + 1 / z := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
    ring
  rw [← hsum, ← hsumi]
  refine le_trans htree ?_
  -- Only six corners are distinct up to `ring`: if `m` of the five variables equal `k`,
  -- the corner value is `((5 - m) * h + m * k) * ((5 - m) / h + m / k)`, which is
  -- `13 + 6 * (h/k + k/h) - (m - 2) * (m - 3) * (h - k)² / (h * k) ≤ 13 + 6 * (h/k + k/h)`.
  have c0 : (5 * h) * (5 / h) ≤ 13 + 6 * (h / k + k / h) := by
    field_simp
    nlinarith [sq_nonneg (h - k), mul_nonneg (sq_nonneg (h - k)) (mul_pos hh hk).le]
  have c1 : (4 * h + k) * (4 / h + 1 / k) ≤ 13 + 6 * (h / k + k / h) := by
    field_simp
    nlinarith [sq_nonneg (h - k), mul_nonneg (sq_nonneg (h - k)) (mul_pos hh hk).le]
  have c2 : (3 * h + 2 * k) * (3 / h + 2 / k) ≤ 13 + 6 * (h / k + k / h) := by
    field_simp
    nlinarith [sq_nonneg (h - k), mul_nonneg (sq_nonneg (h - k)) (mul_pos hh hk).le]
  have c3 : (2 * h + 3 * k) * (2 / h + 3 / k) ≤ 13 + 6 * (h / k + k / h) := by
    field_simp
    nlinarith [sq_nonneg (h - k), mul_nonneg (sq_nonneg (h - k)) (mul_pos hh hk).le]
  have c4 : (h + 4 * k) * (1 / h + 4 / k) ≤ 13 + 6 * (h / k + k / h) := by
    field_simp
    nlinarith [sq_nonneg (h - k), mul_nonneg (sq_nonneg (h - k)) (mul_pos hh hk).le]
  have c5 : (5 * k) * (5 / k) ≤ 13 + 6 * (h / k + k / h) := by
    field_simp
    nlinarith [sq_nonneg (h - k), mul_nonneg (sq_nonneg (h - k)) (mul_pos hh hk).le]
  simp only [cornerMax, max_le_iff]
  repeat' constructor
  -- the 32 leaves are enumerated in binary-counting order: the j-th leaf has
  -- `m = popcount j` of its variables equal to `k`
  · refine le_trans (le_of_eq ?_) c0; ring
  · refine le_trans (le_of_eq ?_) c1; ring
  · refine le_trans (le_of_eq ?_) c1; ring
  · refine le_trans (le_of_eq ?_) c2; ring
  · refine le_trans (le_of_eq ?_) c1; ring
  · refine le_trans (le_of_eq ?_) c2; ring
  · refine le_trans (le_of_eq ?_) c2; ring
  · refine le_trans (le_of_eq ?_) c3; ring
  · refine le_trans (le_of_eq ?_) c1; ring
  · refine le_trans (le_of_eq ?_) c2; ring
  · refine le_trans (le_of_eq ?_) c2; ring
  · refine le_trans (le_of_eq ?_) c3; ring
  · refine le_trans (le_of_eq ?_) c2; ring
  · refine le_trans (le_of_eq ?_) c3; ring
  · refine le_trans (le_of_eq ?_) c3; ring
  · refine le_trans (le_of_eq ?_) c4; ring
  · refine le_trans (le_of_eq ?_) c1; ring
  · refine le_trans (le_of_eq ?_) c2; ring
  · refine le_trans (le_of_eq ?_) c2; ring
  · refine le_trans (le_of_eq ?_) c3; ring
  · refine le_trans (le_of_eq ?_) c2; ring
  · refine le_trans (le_of_eq ?_) c3; ring
  · refine le_trans (le_of_eq ?_) c3; ring
  · refine le_trans (le_of_eq ?_) c4; ring
  · refine le_trans (le_of_eq ?_) c2; ring
  · refine le_trans (le_of_eq ?_) c3; ring
  · refine le_trans (le_of_eq ?_) c3; ring
  · refine le_trans (le_of_eq ?_) c4; ring
  · refine le_trans (le_of_eq ?_) c3; ring
  · refine le_trans (le_of_eq ?_) c4; ring
  · refine le_trans (le_of_eq ?_) c4; ring
  · refine le_trans (le_of_eq ?_) c5; ring

end Usa1977P5
