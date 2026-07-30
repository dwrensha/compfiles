/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 1993, Problem 5

A sequence xₙ of positive reals satisfies xₙ₋₁xₙ₊₁ ≤ xₙ².
Let aₙ be the average of the terms x₀, x₁, ..., xₙ and bₙ be the average
of the terms x₁, x₂, ..., xₙ.
Show that aₙbₙ₋₁ ≥ aₙ₋₁bₙ.
-/

namespace Usa1993P5

/-- `a_avg x n` is the average of the terms `x 0, x 1, ..., x n`. -/
noncomputable def a_avg (x : ℕ → ℝ) (n : ℕ) : ℝ := (∑ i ∈ Finset.range (n + 1), x i) / (n + 1)

/-- `b_avg x n` is the average of the terms `x 1, x 2, ..., x n`. -/
noncomputable def b_avg (x : ℕ → ℝ) (n : ℕ) : ℝ := (∑ i ∈ Finset.range n, x (i + 1)) / n

snip begin

/-!
We follow the proof from https://prase.cz/kalva/usa/usoln/usol935.html .

The hypothesis `x n * x (n + 2) ≤ x (n + 1) ^ 2` says that the consecutive
ratios `x (j + 1) / x j` are nonincreasing in `j`. It follows that
`x 0 * x n ≤ x i * x (n - i)` for every `i ≤ n`, and pairing up `x i` with
`x (n - i)` then gives `k ≥ (n - 1) * √(x 0 * x n)`, where
`k = x 1 + x 2 + ... + x (n - 1)`. Together with AM–GM,
`x 0 + x n ≥ 2 * √(x 0 * x n)`, the claim follows by pure algebra.
-/

/-- Two-variable AM–GM. -/
theorem two_mul_sqrt_le_add {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    2 * Real.sqrt (u * v) ≤ u + v := by
  rw [Real.sqrt_mul hu]
  nlinarith [Real.sq_sqrt hu, Real.sq_sqrt hv, sq_nonneg (Real.sqrt u - Real.sqrt v)]

/-- The consecutive ratios are nonincreasing. -/
theorem ratio_antitone (x : ℕ → ℝ) (hx : ∀ n, 0 < x n)
    (h : ∀ n, x n * x (n + 2) ≤ x (n + 1) ^ 2) :
    Antitone (fun j ↦ x (j + 1) / x j) := by
  apply antitone_nat_of_succ_le
  intro j
  show x (j + 2) / x (j + 1) ≤ x (j + 1) / x j
  rw [div_le_div_iff₀ (hx (j + 1)) (hx j)]
  have h2 := h j
  rw [pow_two] at h2
  rw [mul_comm (x (j + 2)) (x j)]
  exact h2

/-- Moving two indices apart weakly decreases the product. -/
theorem prod_le_of_le (x : ℕ → ℝ) (hx : ∀ n, 0 < x n)
    (h : ∀ n, x n * x (n + 2) ≤ x (n + 1) ^ 2)
    {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    x (a - 1) * x (b + 1) ≤ x a * x b := by
  have hr := ratio_antitone x hx h (show a - 1 ≤ b by omega)
  dsimp only at hr
  rw [Nat.sub_add_cancel ha] at hr
  rw [div_le_div_iff₀ (hx b) (hx (a - 1))] at hr
  rw [mul_comm (x (b + 1)) (x (a - 1))] at hr
  exact hr

/-- Symmetric products: `x 0 * x n ≤ x i * x (n - i)`. -/
theorem x0_mul_xn_le (x : ℕ → ℝ) (hx : ∀ n, 0 < x n)
    (h : ∀ n, x n * x (n + 2) ≤ x (n + 1) ^ 2) :
    ∀ {i n : ℕ}, 2 * i ≤ n → x 0 * x n ≤ x i * x (n - i) := by
  intro i
  induction i with
  | zero => intro n _; simp
  | succ i ih =>
    intro n h2i
    have step := prod_le_of_le x hx h (a := i + 1) (b := n - i - 1) (by omega) (by omega)
    rw [Nat.add_sub_cancel, show n - i - 1 + 1 = n - i by omega] at step
    have IH : x 0 * x n ≤ x i * x (n - i) := ih (n := n) (by omega)
    rw [show n - (i + 1) = n - i - 1 by omega]
    exact le_trans IH step

/-- Each paired sum `x i + x (n - i)` is at least `2 * √(x 0 * x n)`. -/
theorem pair_ge (x : ℕ → ℝ) (hx : ∀ n, 0 < x n)
    (h : ∀ n, x n * x (n + 2) ≤ x (n + 1) ^ 2)
    {i n : ℕ} (hi : i ≤ n) :
    2 * Real.sqrt (x 0 * x n) ≤ x i + x (n - i) := by
  have hprod : x 0 * x n ≤ x i * x (n - i) := by
    by_cases h2i : 2 * i ≤ n
    · exact x0_mul_xn_le x hx h h2i
    · have h' := x0_mul_xn_le x hx h (i := n - i) (n := n) (by omega)
      rw [show n - (n - i) = i by omega, mul_comm (x (n - i)) (x i)] at h'
      exact h'
  have hsqrt : Real.sqrt (x 0 * x n) ≤ Real.sqrt (x i * x (n - i)) :=
    Real.sqrt_le_sqrt hprod
  have hamg : 2 * Real.sqrt (x i * x (n - i)) ≤ x i + x (n - i) :=
    two_mul_sqrt_le_add (hx i).le (hx (n - i)).le
  linarith

/-- The key estimate: `k ≥ (n - 1) * √(x 0 * x n)`, in doubled form. -/
theorem sum_pair_ge (x : ℕ → ℝ) (hx : ∀ n, 0 < x n)
    (h : ∀ n, x n * x (n + 2) ≤ x (n + 1) ^ 2)
    {n : ℕ} (hn : 2 ≤ n) :
    ((n : ℝ) - 1) * (2 * Real.sqrt (x 0 * x n)) ≤
      2 * ∑ i ∈ Finset.range (n - 1), x (i + 1) := by
  have h2sum : ∑ i ∈ Finset.range (n - 1), x (n - 1 - i) =
      ∑ i ∈ Finset.range (n - 1), x (i + 1) := by
    rw [← Finset.sum_range_reflect (fun i ↦ x (i + 1)) (n - 1)]
    refine Finset.sum_congr rfl (fun i hi ↦ ?_)
    rw [Finset.mem_range] at hi
    congr 1
    omega
  calc ((n : ℝ) - 1) * (2 * Real.sqrt (x 0 * x n))
      = ∑ i ∈ Finset.range (n - 1), (2 * Real.sqrt (x 0 * x n)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    _ ≤ ∑ i ∈ Finset.range (n - 1), (x (i + 1) + x (n - 1 - i)) := by
        refine Finset.sum_le_sum (fun i hi ↦ ?_)
        rw [Finset.mem_range] at hi
        have hpg := pair_ge x hx h (i := i + 1) (n := n) (by omega)
        rw [show n - (i + 1) = n - 1 - i by omega] at hpg
        exact hpg
    _ = 2 * ∑ i ∈ Finset.range (n - 1), x (i + 1) := by
        rw [Finset.sum_add_distrib, h2sum]
        ring

/-- Peeling off the first and last terms of a range sum. -/
theorem sum_decomp (x : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ Finset.range (m + 2), x i =
      x 0 + (∑ i ∈ Finset.range m, x (i + 1)) + x (m + 1) := by
  rw [(rfl : m + 2 = m + 1 + 1), Finset.sum_range_succ', Finset.sum_range_succ]
  ring

/-- The algebraic heart of the proof. -/
theorem final_algebra {N k x0 xn : ℝ} (hN : 2 ≤ N) (hN1 : 0 < N - 1)
    (hkey : (N ^ 2 - 1) * (x0 * xn) ≤ k * (k + x0 + xn)) :
    (x0 + k + xn) / (N + 1) * (k / (N - 1)) ≥ (x0 + k) / N * ((k + xn) / N) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hN10 : (0 : ℝ) < N + 1 := by linarith
  rw [ge_iff_le, div_mul_div_comm, div_mul_div_comm,
    div_le_div_iff₀ (mul_pos hN0 hN0) (mul_pos hN10 hN1)]
  nlinarith [hkey]

/-- The inequality `k * (k + x 0 + x n) ≥ (n ^ 2 - 1) * x 0 * x n`. -/
theorem key_ineq (x : ℕ → ℝ) (hx : ∀ n, 0 < x n)
    (h : ∀ n, x n * x (n + 2) ≤ x (n + 1) ^ 2)
    {n : ℕ} (hn : 2 ≤ n) :
    ((n : ℝ) ^ 2 - 1) * (x 0 * x n) ≤
      (∑ i ∈ Finset.range (n - 1), x (i + 1)) *
        ((∑ i ∈ Finset.range (n - 1), x (i + 1)) + x 0 + x n) := by
  set k := ∑ i ∈ Finset.range (n - 1), x (i + 1) with hk
  set s := Real.sqrt (x 0 * x n) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = x 0 * x n := Real.sq_sqrt (mul_nonneg (hx 0).le (hx n).le)
  have hN : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hk0 : 0 ≤ k := by
    rw [hk]
    exact Finset.sum_nonneg (fun i _ ↦ (hx (i + 1)).le)
  have hk_ge : ((n : ℝ) - 1) * s ≤ k := by
    have hsum := sum_pair_ge x hx h hn
    rw [← hs, ← hk] at hsum
    linarith
  have hsum_ge : ((n : ℝ) + 1) * s ≤ k + x 0 + x n := by
    have hamg : 2 * Real.sqrt (x 0 * x n) ≤ x 0 + x n :=
      two_mul_sqrt_le_add (hx 0).le (hx n).le
    rw [← hs] at hamg
    linarith
  have hmul : ((n : ℝ) - 1) * s * (((n : ℝ) + 1) * s) ≤ k * (k + x 0 + x n) :=
    mul_le_mul hk_ge hsum_ge (mul_nonneg (by linarith) hs0) hk0
  nlinarith [hmul, hs2]

snip end

problem usa1993_p5 (x : ℕ → ℝ) (hx : ∀ n, 0 < x n)
    (h : ∀ n, x n * x (n + 2) ≤ x (n + 1) ^ 2)
    (n : ℕ) (hn : 2 ≤ n) :
    a_avg x n * b_avg x (n - 1) ≥ a_avg x (n - 1) * b_avg x n := by
  have hN : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hN1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hkey := key_ineq x hx h hn
  have ha : ∑ i ∈ Finset.range (n + 1), x i =
      x 0 + (∑ i ∈ Finset.range (n - 1), x (i + 1)) + x n := by
    rw [show n + 1 = n - 1 + 2 by omega, sum_decomp x (n - 1),
      show n - 1 + 1 = n by omega]
  have hb : ∑ i ∈ Finset.range n, x (i + 1) =
      (∑ i ∈ Finset.range (n - 1), x (i + 1)) + x n := by
    conv_lhs => rw [show n = n - 1 + 1 by omega]
    rw [Finset.sum_range_succ, show n - 1 + 1 = n by omega]
  have ha1 : ∑ i ∈ Finset.range (n - 1 + 1), x i =
      x 0 + (∑ i ∈ Finset.range (n - 1), x (i + 1)) := by
    rw [Finset.sum_range_succ']
    ring
  simp only [a_avg, b_avg]
  rw [ha, hb, ha1]
  have cn : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one]
  rw [cn, sub_add_cancel]
  exact final_algebra hN hN1 hkey

end Usa1993P5
