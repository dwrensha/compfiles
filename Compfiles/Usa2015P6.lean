/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.PSeries
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Inequality, .Combinatorics] }

/-!
# USA Mathematical Olympiad 2015, Problem 6

Fix $0 < \lambda < 1$, and let $A$ be a multiset of positive integers. Let
$A_n = \{a \in A : a \le n\}$. Assume that for every $n \in \mathbb{N}$, the
multiset $A_n$ contains at most $n\lambda$ numbers. Show that there are
infinitely many $n \in \mathbb{N}$ for which the sum of the elements in $A_n$
is at most $\frac{n(n+1)}{2}\lambda$.
-/

namespace Usa2015P6

snip begin

/-- Rewrite a sum over `Finset.Icc 1 n` as a sum over `Finset.range n`. -/
lemma sum_Icc_one_eq_sum_range_add {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, f k = ∑ k ∈ Finset.range n, f (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/-- Abel summation identity: the sum of the elements of the multiset `A` not
exceeding `n` equals `n + 1` times their number minus the sum of the counts. -/
lemma sum_elements_sub_card (A : ℕ → ℕ) (n : ℕ) :
    ∑ m ∈ Finset.Icc 1 n, (m : ℝ) * (A m : ℝ)
      = (n + 1) * (∑ k ∈ Finset.Icc 1 n, (A k : ℝ))
        - ∑ k ∈ Finset.Icc 1 n, ∑ m ∈ Finset.Icc 1 k, (A m : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : (1 : ℕ) ≤ n + 1 := by omega
    rw [Finset.sum_Icc_succ_top h1 (fun m => ∑ m ∈ Finset.Icc 1 m, (A m : ℝ)),
      Finset.sum_Icc_succ_top h1 (fun m => (A m : ℝ)),
      Finset.sum_Icc_succ_top h1 (fun m => (m : ℝ) * (A m : ℝ)), ih]
    push_cast
    ring

/-- The partial sums of the harmonic series grow past any bound. -/
lemma harmonic_large (B : ℝ) : ∃ k : ℕ, B < ∑ i ∈ Finset.range k, (1 : ℝ) / (i + 1) :=
  (Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually_gt_atTop B).exists

/-- Core analytic lemma. A nonnegative real sequence for which, from some point
on, every term is smaller than the average of the previous terms, while
consecutive terms always differ by at least some fixed `ε > 0`, cannot exist:
its running average would eventually become negative. -/
lemma recurrent_averages_absurd
    (x : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε) (N : ℕ) (hN : 1 ≤ N)
    (hx_nonneg : ∀ n, 0 ≤ x n)
    (hx_avg : ∀ n ≥ N, (n : ℝ) * x n < ∑ k ∈ Finset.range n, x k)
    (hx_step : ∀ n, ε ≤ |x (n + 1) - x n|) :
    False := by
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  -- every term is below the average of the previous ones
  have hx_lt_avg : ∀ n ≥ N, x n < (∑ k ∈ Finset.range n, x k) / n := by
    intro n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le hN' (by exact_mod_cast hn)
    rw [lt_div_iff₀ hn0, mul_comm]
    exact hx_avg n hn
  -- hence the running average is strictly decreasing from `N` on
  have havg_lt : ∀ n ≥ N,
      (∑ k ∈ Finset.range (n + 1), x k) / (n + 1) < (∑ k ∈ Finset.range n, x k) / n := by
    intro n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le hN' (by exact_mod_cast hn)
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h2 := hx_lt_avg n hn
    rw [Finset.sum_range_succ, div_lt_iff₀ hn1, mul_add, div_mul_cancel₀ _ hn0.ne', mul_one]
    linarith [h2]
  -- the average drops by a definite amount every two steps
  have hF6 : ∀ n ≥ N,
      (∑ k ∈ Finset.range (n + 2), x k) / ((n : ℝ) + 2)
        < (∑ k ∈ Finset.range n, x k) / n - ε / ((n : ℝ) + 2) := by
    intro n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le hN' (by exact_mod_cast hn)
    have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have h2 := hx_lt_avg n hn
    have h4 := havg_lt n hn
    have h3 : x (n + 1) < (∑ k ∈ Finset.range n, x k) / n := by
      have h2' := hx_lt_avg (n + 1) (by omega)
      push_cast at h2'
      exact lt_trans h2' h4
    have hstep := hx_step n
    have hpair : x n + x (n + 1) < 2 * ((∑ k ∈ Finset.range n, x k) / n) - ε := by
      rcases le_total (x n) (x (n + 1)) with hle | hle
      · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x (n + 1) - x n)] at hstep
        linarith
      · rw [abs_of_nonpos (by linarith : x (n + 1) - x n ≤ (0 : ℝ))] at hstep
        linarith
    have hS2 : ∑ k ∈ Finset.range (n + 2), x k
        = (∑ k ∈ Finset.range n, x k) + x n + x (n + 1) := by
      rw [show n + 2 = n + 1 + 1 by omega, Finset.sum_range_succ, Finset.sum_range_succ]
    rw [hS2, div_lt_iff₀ hn2, sub_mul, div_mul_cancel₀ _ hn2.ne', mul_add,
      div_mul_cancel₀ _ hn0.ne']
    linarith [hpair]
  -- iterated bound on the average
  have hF7 : ∀ k : ℕ, (∑ i ∈ Finset.range (N + 2 * k), x i) / ((N : ℝ) + 2 * k)
      ≤ (∑ i ∈ Finset.range N, x i) / N
        - ε * ∑ j ∈ Finset.range k, 1 / ((N : ℝ) + 2 * j + 2) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h6 := hF6 (N + 2 * k) (by omega)
      rw [Finset.sum_range_succ (fun j => 1 / ((N : ℝ) + 2 * j + 2)) k,
        show N + 2 * (k + 1) = N + 2 * k + 2 by ring, mul_add, mul_one_div]
      push_cast at h6 ⊢
      ring_nf at h6 ih ⊢
      linarith [h6, ih]
  -- comparison with the harmonic series
  have hF8 : ∀ k : ℕ, (∑ i ∈ Finset.range k, (1 : ℝ) / (i + 1)) / (N + 2)
      ≤ ∑ j ∈ Finset.range k, 1 / ((N : ℝ) + 2 * j + 2) := by
    intro k
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro j _
    have h3 : (0 : ℝ) < (N : ℝ) + 2 * j + 2 := by positivity
    have h4 : (N : ℝ) + 2 * j + 2 ≤ ((N : ℝ) + 2) * (j + 1) := by
      have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      have hexp : ((N : ℝ) + 2) * (j + 1) = (N : ℝ) * j + ((N : ℝ) + 2 * j + 2) := by ring
      rw [hexp]
      exact le_add_of_nonneg_left (mul_nonneg hN0 hj0)
    rw [div_div, mul_comm ((j : ℝ) + 1) ((N : ℝ) + 2)]
    exact one_div_le_one_div_of_le h3 h4
  -- pick a large harmonic sum and derive the contradiction
  obtain ⟨k, hk⟩ := harmonic_large ((∑ i ∈ Finset.range N, x i) / N * ((N : ℝ) + 2) / ε)
  have hN2pos : (0 : ℝ) < (N : ℝ) + 2 := by positivity
  have hpos : (0 : ℝ) < ε / ((N : ℝ) + 2) := by positivity
  have hmul := mul_lt_mul_of_pos_left hk hpos
  have hN0' : (N : ℝ) ≠ 0 := hN'.ne'
  have hN20' : ((N : ℝ) + 2) ≠ 0 := hN2pos.ne'
  have hε0' : ε ≠ 0 := hε.ne'
  have hid : ε / ((N : ℝ) + 2) * ((∑ i ∈ Finset.range N, x i) / N * ((N : ℝ) + 2) / ε)
      = (∑ i ∈ Finset.range N, x i) / N := by
    field_simp
  rw [hid] at hmul
  have hbound : (∑ i ∈ Finset.range N, x i) / N
      < ε * ∑ j ∈ Finset.range k, 1 / ((N : ℝ) + 2 * j + 2) := by
    have hle := mul_le_mul_of_nonneg_left (hF8 k) (le_of_lt hε)
    have heq : ε / ((N : ℝ) + 2) * (∑ i ∈ Finset.range k, (1 : ℝ) / (i + 1))
        = ε * ((∑ i ∈ Finset.range k, (1 : ℝ) / (i + 1)) / ((N : ℝ) + 2)) := by
      rw [div_mul_eq_mul_div, mul_div_assoc]
    rw [heq] at hmul
    exact lt_of_lt_of_le hmul hle
  have h7 := hF7 k
  have hSnonneg : (0 : ℝ) ≤ ∑ i ∈ Finset.range (N + 2 * k), x i :=
    Finset.sum_nonneg (fun i _ => hx_nonneg i)
  have hdenom : (0 : ℝ) < (N : ℝ) + 2 * k :=
    lt_of_lt_of_le hN' (le_add_of_nonneg_right (by positivity))
  have hMnonneg : (0 : ℝ) ≤ (∑ i ∈ Finset.range (N + 2 * k), x i) / ((N : ℝ) + 2 * k) :=
    div_nonneg hSnonneg (le_of_lt hdenom)
  linarith [h7, hbound, hMnonneg]

snip end

problem usa2015_p6 {lam : ℝ} (hlam : 0 < lam ∧ lam < 1) (A : ℕ → ℕ)
    (hA : ∀ n : ℕ, ∑ m ∈ Finset.Icc 1 n, (A m : ℝ) ≤ lam * n) :
    Set.Infinite
      {n : ℕ | ∑ m ∈ Finset.Icc 1 n, m * (A m : ℝ) ≤ lam * n * (n + 1) / 2} := by
  by_contra hnot
  rw [Set.not_infinite] at hnot
  obtain ⟨N, hN⟩ := hnot.bddAbove
  -- every `n > N` violates the desired inequality
  have hsum : ∀ n ≥ N + 1,
      lam * n * (n + 1) / 2 < ∑ m ∈ Finset.Icc 1 n, m * (A m : ℝ) := by
    intro n hn
    by_contra hcon
    push Not at hcon
    have hle := hN hcon
    omega
  -- the defect sequence `x n = λ n - |A_n|`
  set x : ℕ → ℝ := fun n => lam * n - ∑ m ∈ Finset.Icc 1 n, (A m : ℝ) with hx
  have hx_nonneg : ∀ n, 0 ≤ x n := by
    intro n
    simp only [hx]
    exact sub_nonneg.mpr (hA n)
  have hCk : ∀ k, (∑ m ∈ Finset.Icc 1 k, (A m : ℝ)) = lam * k - x k := by
    intro k
    simp only [hx]
    ring
  -- Gauss's sum
  have hgauss : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, (k : ℝ) = (n : ℝ) * (n + 1) / 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega : (1 : ℕ) ≤ n + 1) (fun k => (k : ℝ)), ih]
      push_cast
      ring
  -- sum of the defects over `Icc 1 n`
  have h1 : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, (∑ m ∈ Finset.Icc 1 k, (A m : ℝ))
      = lam * (∑ k ∈ Finset.Icc 1 n, (k : ℝ)) - ∑ k ∈ Finset.Icc 1 n, x k := by
    intro n
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    exact hCk k
  have hx0 : x 0 = 0 := by
    simp only [hx]
    simp
  have hbridge : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, x k = ∑ k ∈ Finset.range (n + 1), x k := by
    intro n
    rw [sum_Icc_one_eq_sum_range_add x n, Finset.sum_range_succ', hx0, add_zero]
  -- every defect is less than the average of the previous defects
  have havg : ∀ n ≥ N + 1, (n : ℝ) * x n < ∑ k ∈ Finset.range n, x k := by
    intro n hn
    have hgt := hsum n hn
    have hid := sum_elements_sub_card A n
    rw [h1 n, hCk n, hgauss n, hbridge n, Finset.sum_range_succ] at hid
    ring_nf at hid hgt ⊢
    linarith [hid, hgt]
  -- consecutive defects differ by at least `min lam (1 - lam)`
  have hε : (0 : ℝ) < min lam (1 - lam) := by
    rw [lt_min_iff]
    exact ⟨hlam.1, by linarith [hlam.2]⟩
  have hx_step : ∀ n, min lam (1 - lam) ≤ |x (n + 1) - x n| := by
    intro n
    have hstep : x (n + 1) - x n = lam - (A (n + 1) : ℝ) := by
      have hsucc : (∑ m ∈ Finset.Icc 1 (n + 1), (A m : ℝ))
          = (∑ m ∈ Finset.Icc 1 n, (A m : ℝ)) + (A (n + 1) : ℝ) :=
        Finset.sum_Icc_succ_top (by omega) _
      simp only [hx]
      rw [hsucc]
      push_cast
      ring
    rw [hstep]
    rcases Nat.eq_zero_or_pos (A (n + 1)) with hz | hpos
    · rw [hz, Nat.cast_zero, sub_zero, abs_of_nonneg (le_of_lt hlam.1)]
      exact min_le_left _ _
    · have hk : (1 : ℝ) ≤ (A (n + 1) : ℝ) := by exact_mod_cast hpos
      have hneg : lam - (A (n + 1) : ℝ) < 0 := by linarith [hlam.2, hk]
      rw [abs_of_neg hneg]
      have hmin := min_le_right lam (1 - lam)
      linarith [hk, hlam.2, hmin]
  exact recurrent_averages_absurd x (min lam (1 - lam)) hε (N + 1) (by omega)
    hx_nonneg havg hx_step

end Usa2015P6
