/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.EuclideanDomain.Basic
public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.Linarith
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Algebra, .Inequality]
}

/-!
# International Mathematical Olympiad 2003, Problem 5

Given n > 2 and reals x₁ ≤ x₂ ≤ ... ≤ xₙ, show that

  (∑ᵢⱼ |xᵢ - xⱼ|)² ≤ (2/3)(n² - 1) ∑ᵢⱼ (xᵢ - xⱼ)².

Show that we have equality iff the sequence is an arithmetic progression.
-/

namespace Imo2003P5

open Finset

snip begin

/-
## Solution

Since the inequality only involves differences of the `xᵢ`, we may replace `xᵢ` by
`xᵢ - m` where `m` is the mean of the `xᵢ`, i.e. we may assume `∑ xᵢ = 0`.
Using that the sequence is nondecreasing, the sum of absolute differences is

  ∑ᵢⱼ |xᵢ - xⱼ| = 2 ∑ᵢ (2i + 1 - n) xᵢ          (0 ≤ i < n)

(proved below by induction on `n`), while

  ∑ᵢⱼ (xᵢ - xⱼ)² = 2n ∑ᵢ xᵢ² - 2 (∑ᵢ xᵢ)² = 2n ∑ᵢ xᵢ².

Cauchy-Schwarz gives

  (∑ᵢ (2i + 1 - n) xᵢ)² ≤ (∑ᵢ (2i + 1 - n)²) (∑ᵢ xᵢ²) = (n(n² - 1)/3) ∑ᵢ xᵢ²,

and the claim follows.
-/

theorem sum_range_id_real (n : ℕ) :
    ∑ i ∈ range n, (i : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ k ih => rw [sum_range_succ, ih]; push_cast; ring

theorem sum_sq_range (n : ℕ) :
    ∑ i ∈ range n, (i : ℝ) ^ 2 = (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) / 6 := by
  induction n with
  | zero => simp
  | succ k ih => rw [sum_range_succ, ih]; push_cast; ring

/-- The coefficients `2i + 1 - n` are centered: their sum vanishes. -/
theorem sum_coeff (n : ℕ) : ∑ i ∈ range n, (2 * (i : ℝ) + 1 - (n : ℝ)) = 0 := by
  simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul,
    sum_range_id_real]
  ring

/-- The sum of the coefficients times the index. -/
theorem sum_coeff_mul (n : ℕ) :
    ∑ i ∈ range n, (2 * (i : ℝ) + 1 - (n : ℝ)) * (i : ℝ) = (n : ℝ) * ((n : ℝ) ^ 2 - 1) / 6 := by
  have exp : ∀ i : ℕ, (2 * (i : ℝ) + 1 - (n : ℝ)) * (i : ℝ)
      = 2 * (i : ℝ) ^ 2 + (1 - (n : ℝ)) * (i : ℝ) := fun i => by ring
  rw [sum_congr rfl fun i _ => exp i]
  simp only [sum_add_distrib, ← mul_sum, sum_sq_range, sum_range_id_real]
  ring

/-- The sum of the squared coefficients. -/
theorem sum_sq_coeff (n : ℕ) :
    ∑ i ∈ range n, (2 * (i : ℝ) + 1 - (n : ℝ)) ^ 2 = (n : ℝ) * ((n : ℝ) ^ 2 - 1) / 3 := by
  have exp : ∀ i : ℕ, (2 * (i : ℝ) + 1 - (n : ℝ)) ^ 2
      = 4 * (i : ℝ) ^ 2 + (4 - 4 * (n : ℝ)) * (i : ℝ) + (1 - (n : ℝ)) ^ 2 := fun i => by ring
  rw [sum_congr rfl fun i _ => exp i]
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul,
    sum_sq_range, sum_range_id_real]
  ring

/-- The key identity for the sum of absolute differences of a nondecreasing sequence. -/
theorem sum_abs_diff : ∀ (n : ℕ) {x : ℕ → ℝ}, MonotoneOn x (range n) →
    ∑ i ∈ range n, ∑ j ∈ range n, |x i - x j| =
      2 * ∑ i ∈ range n, (2 * (i : ℝ) + 1 - (n : ℝ)) * x i := by
  intro n
  induction n with
  | zero => intro x _; simp
  | succ k ih =>
    intro x hx
    have hsub : range k ⊆ range (k + 1) := fun a ha =>
      mem_range.mpr ((mem_range.mp ha).trans (Nat.lt_succ_self k))
    have hxk : MonotoneOn x (range k) := hx.mono hsub
    have habs : ∀ i ∈ range k, |x i - x k| = x k - x i := fun i hi => by
      have hle : x i ≤ x k := hx (mem_range.mpr ((mem_range.mp hi).trans (Nat.lt_succ_self k)))
        (mem_range.mpr (Nat.lt_succ_self k)) (mem_range.mp hi).le
      rw [abs_of_nonpos (sub_nonpos.mpr hle)]
      ring
    have habs' : ∀ j ∈ range k, |x k - x j| = x k - x j := fun j hj =>
      abs_of_nonneg (sub_nonneg.mpr (hx (mem_range.mpr ((mem_range.mp hj).trans
        (Nat.lt_succ_self k))) (mem_range.mpr (Nat.lt_succ_self k)) (mem_range.mp hj).le))
    have split : ∑ i ∈ range (k + 1), ∑ j ∈ range (k + 1), |x i - x j|
        = ∑ i ∈ range k, ∑ j ∈ range k, |x i - x j|
          + ∑ i ∈ range k, (x k - x i) + ∑ j ∈ range k, (x k - x j) := by
      calc ∑ i ∈ range (k + 1), ∑ j ∈ range (k + 1), |x i - x j|
          = (∑ i ∈ range k, (∑ j ∈ range k, |x i - x j| + |x i - x k|))
              + (∑ j ∈ range k, |x k - x j| + |x k - x k|) := by
            rw [sum_range_succ]
            congr 1
            · exact sum_congr rfl fun i _ => sum_range_succ _ _
            · exact sum_range_succ _ _
        _ = ∑ i ∈ range k, ∑ j ∈ range k, |x i - x j|
            + ∑ i ∈ range k, (x k - x i) + ∑ j ∈ range k, (x k - x j) := by
          rw [sum_add_distrib]
          have e3 : |x k - x k| = (0 : ℝ) := by rw [sub_self, abs_zero]
          rw [e3, add_zero, sum_congr rfl habs, sum_congr rfl habs', add_assoc]
    have rsplit : 2 * ∑ i ∈ range (k + 1), (2 * (i : ℝ) + 1 - ((k + 1 : ℕ) : ℝ)) * x i
        = 2 * (∑ i ∈ range k, (2 * (i : ℝ) + 1 - (k : ℝ)) * x i - ∑ i ∈ range k, x i
            + (k : ℝ) * x k) := by
      rw [sum_range_succ]
      have pt : ∀ i ∈ range k, (2 * (i : ℝ) + 1 - ((k + 1 : ℕ) : ℝ)) * x i
          = (2 * (i : ℝ) + 1 - (k : ℝ)) * x i - x i := fun i _ => by push_cast; ring
      rw [sum_congr rfl pt, sum_sub_distrib]
      push_cast
      ring
    have esum : ∑ i ∈ range k, (x k - x i) = (k : ℝ) * x k - ∑ i ∈ range k, x i := by
      rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    rw [split, rsplit, esum, ih hxk]
    ring

/-- Expansion of the sum of squared differences. -/
theorem sum_sq_diff (n : ℕ) (x : ℕ → ℝ) :
    ∑ i ∈ range n, ∑ j ∈ range n, (x i - x j) ^ 2
      = 2 * (n : ℝ) * ∑ i ∈ range n, x i ^ 2 - 2 * (∑ i ∈ range n, x i) ^ 2 := by
  have exp : ∀ i j : ℕ, (x i - x j) ^ 2 = x i ^ 2 - 2 * x i * x j + x j ^ 2 := fun i j => by ring
  rw [sum_congr rfl fun i _ => sum_congr rfl fun j _ => exp i j]
  simp only [sum_sub_distrib, sum_add_distrib, sum_const, card_range, nsmul_eq_mul,
    ← mul_sum, ← sum_mul]
  ring

snip end

problem imo2003_p5 (n : ℕ) (hn : 2 < n) (x : ℕ → ℝ) (hx : MonotoneOn x (range n)) :
    (∑ i ∈ range n, ∑ j ∈ range n, |x i - x j|) ^ 2 ≤
      2 / 3 * ((n : ℝ) ^ 2 - 1) * ∑ i ∈ range n, ∑ j ∈ range n, (x i - x j) ^ 2 := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  set S : ℝ := ∑ i ∈ range n, x i with hS
  set m : ℝ := S / (n : ℝ) with hm
  let y : ℕ → ℝ := fun i => x i - m
  have yeq : ∀ i : ℕ, y i = x i - m := fun _ => rfl
  have hmy : MonotoneOn y (range n) := fun i hi j hj hij => sub_le_sub_right (hx hi hj hij) m
  have hnm : (n : ℝ) * m = S := by
    rw [hm, mul_comm]
    exact div_mul_cancel₀ S hn0
  have hsumy : ∑ i ∈ range n, y i = 0 := by
    simp_rw [yeq, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, ← hS, hnm, sub_self]
  have habsy : ∑ i ∈ range n, ∑ j ∈ range n, |y i - y j|
      = 2 * ∑ i ∈ range n, (2 * (i : ℝ) + 1 - (n : ℝ)) * y i := sum_abs_diff n hmy
  have hsqy : ∑ i ∈ range n, ∑ j ∈ range n, (y i - y j) ^ 2
      = 2 * (n : ℝ) * ∑ i ∈ range n, y i ^ 2 := by
    have h := sum_sq_diff n y
    rw [hsumy] at h
    rw [h]
    ring
  have hcs : (∑ i ∈ range n, (2 * (i : ℝ) + 1 - (n : ℝ)) * y i) ^ 2
      ≤ (n : ℝ) * ((n : ℝ) ^ 2 - 1) / 3 * ∑ i ∈ range n, y i ^ 2 := by
    have h : (∑ i ∈ range n, (2 * (i : ℝ) + 1 - (n : ℝ)) * y i) ^ 2
        ≤ (∑ i ∈ range n, (2 * (i : ℝ) + 1 - (n : ℝ)) ^ 2) * ∑ i ∈ range n, y i ^ 2 :=
      sum_mul_sq_le_sq_mul_sq _ _ _
    rwa [sum_sq_coeff] at h
  calc (∑ i ∈ range n, ∑ j ∈ range n, |x i - x j|) ^ 2
      = (∑ i ∈ range n, ∑ j ∈ range n, |y i - y j|) ^ 2 := by
        congr 1
        exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by
          rw [yeq i, yeq j]; congr 1; ring
    _ = (2 * ∑ i ∈ range n, (2 * (i : ℝ) + 1 - (n : ℝ)) * y i) ^ 2 := by rw [habsy]
    _ ≤ 4 * ((n : ℝ) * ((n : ℝ) ^ 2 - 1) / 3 * ∑ i ∈ range n, y i ^ 2) := by
        rw [mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num]
        exact mul_le_mul_of_nonneg_left hcs (by norm_num)
    _ = 2 / 3 * ((n : ℝ) ^ 2 - 1) * (2 * (n : ℝ) * ∑ i ∈ range n, y i ^ 2) := by ring
    _ = 2 / 3 * ((n : ℝ) ^ 2 - 1) * ∑ i ∈ range n, ∑ j ∈ range n, (y i - y j) ^ 2 := by
        rw [← hsqy]
    _ = 2 / 3 * ((n : ℝ) ^ 2 - 1) * ∑ i ∈ range n, ∑ j ∈ range n, (x i - x j) ^ 2 := by
        congr 1
        exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by
          rw [yeq i, yeq j]; congr 1; ring

/-- The equality case: equality holds iff the sequence is an arithmetic progression.

For the forward direction, with `y i = x i - m` (so `∑ y = 0`) the equality rewrites as
`(∑ cᵢ yᵢ)² = (∑ cᵢ²)(∑ yᵢ²)` with `cᵢ = 2i + 1 - n`, i.e. equality in Cauchy-Schwarz.
With `t = (∑ cᵢ yᵢ)/(∑ cᵢ²)` we get `∑ (t cᵢ - yᵢ)² = 0`, hence `yᵢ = t cᵢ` for all `i`,
which says exactly that the `xᵢ` form an arithmetic progression. -/
problem imo2003_p5_equality (n : ℕ) (hn : 2 < n) (x : ℕ → ℝ) (hx : MonotoneOn x (range n)) :
    (∑ i ∈ range n, ∑ j ∈ range n, |x i - x j|) ^ 2 =
      2 / 3 * ((n : ℝ) ^ 2 - 1) * ∑ i ∈ range n, ∑ j ∈ range n, (x i - x j) ^ 2 ↔
    ∃ a d : ℝ, ∀ i ∈ range n, x i = a + d * (i : ℝ) := by
  constructor
  · intro heq
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    set S : ℝ := ∑ i ∈ range n, x i with hS
    set m : ℝ := S / (n : ℝ) with hm
    let y : ℕ → ℝ := fun i => x i - m
    have yeq : ∀ i : ℕ, y i = x i - m := fun _ => rfl
    have hmy : MonotoneOn y (range n) := fun i hi j hj hij => sub_le_sub_right (hx hi hj hij) m
    have hnm : (n : ℝ) * m = S := by
      rw [hm, mul_comm]
      exact div_mul_cancel₀ S hn0
    have hsumy : ∑ i ∈ range n, y i = 0 := by
      simp_rw [yeq, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, ← hS, hnm, sub_self]
    set C : ℝ := ∑ i ∈ range n, (2 * (i : ℝ) + 1 - (n : ℝ)) * y i with hC
    set D : ℝ := ∑ i ∈ range n, (2 * (i : ℝ) + 1 - (n : ℝ)) ^ 2 with hD
    set Q' : ℝ := ∑ i ∈ range n, y i ^ 2 with hQ'
    have habsy : ∑ i ∈ range n, ∑ j ∈ range n, |y i - y j| = 2 * C := sum_abs_diff n hmy
    have hsqy : ∑ i ∈ range n, ∑ j ∈ range n, (y i - y j) ^ 2 = 2 * (n : ℝ) * Q' := by
      have h := sum_sq_diff n y
      rw [hsumy] at h
      rw [h, ← hQ']
      ring
    have hdiff_abs : ∑ i ∈ range n, ∑ j ∈ range n, |y i - y j|
        = ∑ i ∈ range n, ∑ j ∈ range n, |x i - x j| :=
      sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [yeq i, yeq j]; congr 1; ring
    have hdiff_sq : ∑ i ∈ range n, ∑ j ∈ range n, (y i - y j) ^ 2
        = ∑ i ∈ range n, ∑ j ∈ range n, (x i - x j) ^ 2 :=
      sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [yeq i, yeq j]; congr 1; ring
    have hDval : D = (n : ℝ) * ((n : ℝ) ^ 2 - 1) / 3 := hD.trans (sum_sq_coeff n)
    -- the equality is exactly the equality case of Cauchy-Schwarz
    have key : C ^ 2 = D * Q' := by
      have h1 : (2 * C) ^ 2 = 2 / 3 * ((n : ℝ) ^ 2 - 1) * (2 * (n : ℝ) * Q') := by
        rw [habsy.symm, hsqy.symm, hdiff_abs, hdiff_sq]
        exact heq
      rw [hDval]
      linear_combination h1 / 4
    have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hDpos : 0 < D := by
      rw [hDval]
      have h1 : (0 : ℝ) < (n : ℝ) ^ 2 - 1 := by
        rw [sub_pos, one_lt_sq_iff₀ (Nat.cast_nonneg n)]
        exact_mod_cast (show 1 < n by omega)
      have h2 : (0 : ℝ) < (n : ℝ) := three_pos.trans_le hn3
      exact div_pos (mul_pos h2 h1) three_pos
    have hDne : D ≠ 0 := ne_of_gt hDpos
    set t : ℝ := C / D with ht
    have hQ'e : Q' = C ^ 2 / D := by
      rw [key]
      exact (mul_div_cancel_left₀ Q' hDne).symm
    have htD : t * D = C := by
      rw [ht]
      exact div_mul_cancel₀ C hDne
    have ht2D : t ^ 2 * D = t * C := by rw [pow_two, mul_assoc, htD]
    have htC : t * C = Q' := by rw [ht, div_mul_eq_mul_div, ← pow_two, ← hQ'e]
    have hzero : ∑ i ∈ range n, (t * (2 * (i : ℝ) + 1 - (n : ℝ)) - y i) ^ 2 = 0 := by
      have exp : ∀ i : ℕ, (t * (2 * (i : ℝ) + 1 - (n : ℝ)) - y i) ^ 2
          = t ^ 2 * (2 * (i : ℝ) + 1 - (n : ℝ)) ^ 2
            - 2 * t * ((2 * (i : ℝ) + 1 - (n : ℝ)) * y i) + y i ^ 2 := fun i => by ring
      rw [sum_congr rfl fun i _ => exp i]
      simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum]
      rw [← hD, ← hC, ← hQ']
      linarith [ht2D, htC]
    have hall : ∀ i ∈ range n, (t * (2 * (i : ℝ) + 1 - (n : ℝ)) - y i) ^ 2 = 0 :=
      (sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg _).mp hzero
    have hform : ∀ i ∈ range n, y i = t * (2 * (i : ℝ) + 1 - (n : ℝ)) := fun i hi => by
      have h := hall i hi
      rw [sq_eq_zero_iff] at h
      exact (sub_eq_zero.mp h).symm
    refine ⟨m + t * (1 - (n : ℝ)), 2 * t, fun i hi => ?_⟩
    have h1 : x i = y i + m := by rw [yeq i]; ring
    rw [h1, hform i hi]
    ring
  · rintro ⟨a, d, had⟩
    have habsx := sum_abs_diff n hx
    have hcx : ∑ i ∈ range n, (2 * (i : ℝ) + 1 - (n : ℝ)) * x i
        = d * ((n : ℝ) * ((n : ℝ) ^ 2 - 1) / 6) := by
      have h1 : ∀ i ∈ range n, (2 * (i : ℝ) + 1 - (n : ℝ)) * x i
          = a * (2 * (i : ℝ) + 1 - (n : ℝ)) + d * ((2 * (i : ℝ) + 1 - (n : ℝ)) * (i : ℝ)) :=
        fun i hi => by rw [had i hi]; ring
      rw [sum_congr rfl h1]
      simp only [sum_add_distrib, ← mul_sum, sum_coeff, sum_coeff_mul]
      ring
    have hsumx : ∑ i ∈ range n, x i = (n : ℝ) * a + d * ((n : ℝ) * ((n : ℝ) - 1) / 2) := by
      rw [sum_congr rfl had]
      simp only [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul,
        sum_range_id_real]
    have hsumx2 : ∑ i ∈ range n, x i ^ 2
        = (n : ℝ) * a ^ 2 + 2 * a * d * ((n : ℝ) * ((n : ℝ) - 1) / 2)
          + d ^ 2 * ((n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) / 6) := by
      have h1 : ∀ i ∈ range n, x i ^ 2
          = a ^ 2 + (2 * a * d) * (i : ℝ) + d ^ 2 * (i : ℝ) ^ 2 := fun i hi => by
        rw [had i hi]; ring
      rw [sum_congr rfl h1]
      simp only [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul,
        sum_range_id_real, sum_sq_range]
    have hsqx := sum_sq_diff n x
    rw [habsx, hcx, hsqx, hsumx, hsumx2]
    ring

end Imo2003P5
