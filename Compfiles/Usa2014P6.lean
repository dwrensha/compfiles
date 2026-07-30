/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Nat.Cast.Order.Field
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Rat.Star
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 2014, Problem 6

Prove that there is a constant c > 0 with the following property:
If a, b, n are positive integers such that gcd(a + i, b + j) > 1
for all i, j ∈ {0, 1, ..., n}, then min{a, b} > (cn)ⁿ.
-/

namespace Usa2014P6

open Finset

snip begin

/-- Dyadic bound for harmonic sums: the sum of `1/(k+1)` for `k < 2^m - 1` is at most `m`. -/
lemma sum_range_one_div_le_aux (m : ℕ) :
    ∑ k ∈ Finset.range (2 ^ m - 1), (1 : ℚ) / (k + 1) ≤ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hpow : (2 : ℕ) ^ (m + 1) = 2 ^ m * 2 := pow_succ 2 m
    have h2m : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by norm_num)
    have hab : 2 ^ m - 1 ≤ 2 ^ (m + 1) - 1 := by omega
    have hsplit : ∑ k ∈ Finset.range (2 ^ (m + 1) - 1), (1 : ℚ) / (k + 1)
        = ∑ k ∈ Finset.range (2 ^ m - 1), (1 : ℚ) / (k + 1)
          + ∑ k ∈ Finset.Ico (2 ^ m - 1 : ℕ) (2 ^ (m + 1) - 1 : ℕ), (1 : ℚ) / (k + 1) := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
      exact (Finset.sum_Ico_consecutive _ (Nat.zero_le _) hab).symm
    rw [hsplit]
    have hcard : (Finset.Ico (2 ^ m - 1 : ℕ) (2 ^ (m + 1) - 1 : ℕ)).card = 2 ^ m := by
      rw [Nat.card_Ico]; omega
    have hblock : ∑ k ∈ Finset.Ico (2 ^ m - 1 : ℕ) (2 ^ (m + 1) - 1 : ℕ), (1 : ℚ) / (k + 1) ≤ 1 := by
      calc ∑ k ∈ Finset.Ico (2 ^ m - 1 : ℕ) (2 ^ (m + 1) - 1 : ℕ), (1 : ℚ) / (k + 1)
          ≤ (Finset.Ico (2 ^ m - 1 : ℕ) (2 ^ (m + 1) - 1 : ℕ)).card • ((1 : ℚ) / 2 ^ m) := by
            apply Finset.sum_le_card_nsmul
            intro k hk
            rw [Finset.mem_Ico] at hk
            have h1 : 2 ^ m ≤ k + 1 := by omega
            have hkle : (2 : ℚ) ^ m ≤ (k : ℚ) + 1 := by exact_mod_cast h1
            exact one_div_le_one_div_of_le (by positivity) hkle
        _ = 1 := by
            rw [hcard, nsmul_eq_mul]
            have e : ((2 ^ m : ℕ) : ℚ) = (2 : ℚ) ^ m := by push_cast; ring
            rw [e, one_div]
            exact mul_inv_cancel₀ (by positivity)
    rw [Nat.cast_add, Nat.cast_one]
    linarith [ih, hblock]

/-- The harmonic sum `∑ k ∈ Icc 1 M, 1/k` is at most `Nat.clog 2 (M + 1)`. -/
lemma sum_Icc_one_div_le_clog (M : ℕ) :
    ∑ k ∈ Finset.Icc 1 M, (1 : ℚ) / k ≤ Nat.clog 2 (M + 1) := by
  have hle : M + 1 ≤ 2 ^ Nat.clog 2 (M + 1) := Nat.le_pow_clog (by norm_num) (M + 1)
  have hM : M ≤ 2 ^ Nat.clog 2 (M + 1) - 1 := by omega
  have hIcc : Finset.Icc 1 M = Finset.Ico 1 (M + 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have h1 : ∑ k ∈ Finset.Icc 1 M, (1 : ℚ) / k
      = ∑ j ∈ Finset.range M, (1 : ℚ) / ((1 + j : ℕ) : ℚ) := by
    rw [hIcc, Finset.sum_Ico_eq_sum_range, show M + 1 - 1 = M from by omega]
  rw [h1]
  have e : ∀ j : ℕ, (1 : ℚ) / ((1 + j : ℕ) : ℚ) = (1 : ℚ) / (j + 1) := by
    intro j
    rw [Nat.cast_add, Nat.cast_one, add_comm]
  calc ∑ j ∈ Finset.range M, (1 : ℚ) / ((1 + j : ℕ) : ℚ)
      = ∑ j ∈ Finset.range M, (1 : ℚ) / (j + 1) :=
        Finset.sum_congr rfl fun j _ => e j
    _ ≤ ∑ j ∈ Finset.range (2 ^ Nat.clog 2 (M + 1) - 1), (1 : ℚ) / (j + 1) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.range_subset_range.mpr hM
        · intro i _ _
          positivity
    _ ≤ Nat.clog 2 (M + 1) := sum_range_one_div_le_aux (Nat.clog 2 (M + 1))

/-- The sum of `1/p^2` over the primes `p ≤ M` is bounded away from `1/2`
(with room to spare for lower order terms). -/
lemma primesum_inv_sq_le (M : ℕ) (hM : 50 ≤ M) :
    ∑ p ∈ (Finset.range (M + 1)).filter Nat.Prime, (1 : ℚ) / p ^ 2 ≤ 47 / 100 := by
  have hsplit : ∑ p ∈ (Finset.range (M + 1)).filter Nat.Prime, (1 : ℚ) / p ^ 2
      = ∑ p ∈ ((Finset.range (M + 1)).filter Nat.Prime).filter (· < 50), (1 : ℚ) / p ^ 2
        + ∑ p ∈ ((Finset.range (M + 1)).filter Nat.Prime).filter (50 ≤ ·), (1 : ℚ) / p ^ 2 := by
    have hnot : ((Finset.range (M + 1)).filter Nat.Prime).filter (fun p => ¬ p < 50)
        = ((Finset.range (M + 1)).filter Nat.Prime).filter (50 ≤ ·) :=
      Finset.filter_congr fun x _ => Nat.not_lt
    rw [← hnot]
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  rw [hsplit]
  have hL : ∑ p ∈ (Finset.range 50).filter Nat.Prime, (1 : ℚ) / p ^ 2
      ≤ 47 / 100 - 1 / 49 := by
    decide +kernel
  have hP1 : ∑ p ∈ ((Finset.range (M + 1)).filter Nat.Prime).filter (· < 50), (1 : ℚ) / p ^ 2
      ≤ ∑ p ∈ (Finset.range 50).filter Nat.Prime, (1 : ℚ) / p ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
      exact ⟨hp.2, hp.1.2⟩
    · intro i _ _
      positivity
  have hP2 : ∑ p ∈ ((Finset.range (M + 1)).filter Nat.Prime).filter (50 ≤ ·), (1 : ℚ) / p ^ 2
      ≤ ∑ k ∈ Finset.Ico 50 (M + 1), (1 : ℚ) / k ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_range] at hp
      rw [Finset.mem_Ico]
      exact ⟨hp.2, hp.1.1⟩
    · intro i _ _
      positivity
  have htail : ∑ k ∈ Finset.Ico 50 (M + 1), (1 : ℚ) / k ^ 2 ≤ 1 / 49 := by
    have hpt : ∀ k : ℕ, 50 ≤ k → (1 : ℚ) / k ^ 2 ≤ (1 : ℚ) / (k - 1) - 1 / k := by
      intro k hk
      have hk1q : (1 : ℚ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
      have h2q : (2 : ℚ) ≤ k := by exact_mod_cast (by omega : 2 ≤ k)
      have hknz : (k : ℚ) ≠ 0 := by linarith
      have hk1nz : (k : ℚ) - 1 ≠ 0 := by linarith
      have hid : (1 : ℚ) / (k - 1) - 1 / k = 1 / ((k - 1) * k) := by
        field_simp
        ring
      rw [hid]
      apply one_div_le_one_div_of_le
      · exact mul_pos (by linarith) (by linarith)
      · nlinarith [hk1q, h2q]
    calc ∑ k ∈ Finset.Ico 50 (M + 1), (1 : ℚ) / k ^ 2
        ≤ ∑ k ∈ Finset.Ico 50 (M + 1), ((1 : ℚ) / (k - 1) - 1 / k) :=
          Finset.sum_le_sum fun k hk => hpt k (Finset.mem_Ico.mp hk).1
      _ = ∑ j ∈ Finset.range (M + 1 - 50),
            ((1 : ℚ) / (49 + (j : ℚ)) - 1 / (49 + ((j + 1 : ℕ) : ℚ))) := by
          rw [Finset.sum_Ico_eq_sum_range]
          refine Finset.sum_congr rfl fun j _ => ?_
          show (1 : ℚ) / (((50 + j : ℕ) : ℚ) - 1) - 1 / ((50 + j : ℕ) : ℚ)
              = (1 : ℚ) / (49 + (j : ℚ)) - 1 / (49 + ((j + 1 : ℕ) : ℚ))
          have h1 : ((50 + j : ℕ) : ℚ) = 50 + (j : ℚ) := by push_cast; ring
          have h2 : ((j + 1 : ℕ) : ℚ) = (j : ℚ) + 1 := by push_cast; ring
          rw [h1, h2]
          ring_nf
      _ = 1 / 49 - 1 / (M : ℚ) := by
          have e1 : ∑ j ∈ Finset.range (M + 1 - 50),
              ((1 : ℚ) / (49 + (j : ℚ)) - 1 / (49 + ((j + 1 : ℕ) : ℚ)))
              = (1 : ℚ) / (49 + ((0 : ℕ) : ℚ)) - (1 : ℚ) / (49 + ((M + 1 - 50 : ℕ) : ℚ)) :=
            Finset.sum_range_sub' _ _
          rw [e1]
          have hM' : (M + 1 - 50 : ℕ) = M - 49 := by omega
          rw [hM', Nat.cast_zero, add_zero]
          have hc : ((M - 49 : ℕ) : ℚ) = (M : ℚ) - 49 := by
            rw [Nat.cast_sub (by omega : 49 ≤ M)]
            norm_num
          rw [hc]
          ring_nf
      _ ≤ 1 / 49 := by
          have hMpos : (0 : ℚ) < M := by exact_mod_cast (by omega : 0 < M)
          have h1M : (0 : ℚ) ≤ 1 / (M : ℚ) := by positivity
          linarith
  linarith [hP1, hL, hP2, htail]

/-- The number of `i < N` with `p ∣ a + i` is at most `N / p + 1`, as a rational
inequality. -/
lemma card_filter_dvd_le (a N p : ℕ) (ha : 0 < a) (hp : 0 < p) :
    (((range N).filter (fun i => p ∣ a + i)).card : ℚ) ≤ (N : ℚ) / p + 1 := by
  have hbij : ((range N).filter (fun i => p ∣ a + i)).card =
      ((Ioc (a - 1) (a + N - 1)).filter (fun x => p ∣ x)).card := by
    apply Finset.card_bij (fun i _ => a + i)
    · intro i hi
      rw [Finset.mem_filter, Finset.mem_range] at hi
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨by omega, by omega⟩, hi.2⟩
    · intro i₁ _ i₂ _ h
      exact Nat.add_left_cancel h
    · intro x hx
      rw [Finset.mem_filter, Finset.mem_Ioc] at hx
      refine ⟨x - a, ?_, by omega⟩
      rw [Finset.mem_filter, Finset.mem_range]
      have h1 : x - a < N := by omega
      have h2 : p ∣ a + (x - a) := by
        have e : a + (x - a) = x := by omega
        rw [e]
        exact hx.2
      exact ⟨h1, h2⟩
  have h1 := Nat.Ioc_filter_dvd_card_eq_div (a + N - 1) p
  have h2 := Nat.Ioc_filter_dvd_card_eq_div (a - 1) p
  have h3 : ((Ioc 0 (a + N - 1)).filter (fun x => p ∣ x)).card =
      ((Ioc 0 (a - 1)).filter (fun x => p ∣ x)).card +
      ((Ioc (a - 1) (a + N - 1)).filter (fun x => p ∣ x)).card := by
    have hunion : Ioc 0 (a - 1) ∪ Ioc (a - 1) (a + N - 1) = Ioc 0 (a + N - 1) :=
      Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) (by omega)
    have hdisj : Disjoint (Ioc 0 (a - 1)) (Ioc (a - 1) (a + N - 1)) :=
      Finset.Ioc_disjoint_Ioc_of_le (le_refl _)
    rw [← hunion, Finset.filter_union,
      Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj)]
  have hcard : ((Ioc (a - 1) (a + N - 1)).filter (fun x => p ∣ x)).card =
      (a + N - 1) / p - (a - 1) / p := by omega
  rw [hbij, hcard]
  have hsub : (a - 1) / p ≤ (a + N - 1) / p := Nat.div_le_div_right (by omega)
  rw [Nat.cast_sub hsub]
  have hpQ : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp
  have e1 : ((a + N - 1 : ℕ) : ℚ) = (a : ℚ) + N - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ a + N)]
    push_cast
    ring
  have e2 : ((a - 1 : ℕ) : ℚ) = (a : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ a), Nat.cast_one]
  have hA : (((a + N - 1) / p : ℕ) : ℚ) ≤ ((a + N - 1 : ℕ) : ℚ) / (p : ℚ) := Nat.cast_div_le
  rw [e1] at hA
  have hB : ((a : ℚ) - 1) / p < (((a - 1) / p : ℕ) : ℚ) + 1 := by
    have keyN : a - 1 < ((a - 1) / p + 1) * p := by
      have h1 := Nat.div_add_mod (a - 1) p
      have h2 := Nat.mod_lt (a - 1) hp
      have e : ((a - 1) / p + 1) * p = p * ((a - 1) / p) + p := by ring
      rw [e]
      omega
    have keyQ : (a : ℚ) - 1 < (((a - 1) / p : ℕ) : ℚ) * (p : ℚ) + p := by
      have h1 : ((a - 1 : ℕ) : ℚ) < (((a - 1) / p + 1 : ℕ) : ℚ) * p := by exact_mod_cast keyN
      rw [e2] at h1
      have e3 : (((a - 1) / p + 1 : ℕ) : ℚ) = (((a - 1) / p : ℕ) : ℚ) + 1 := by
        push_cast
        ring
      rw [e3] at h1
      linarith [h1]
    rw [div_lt_iff₀ hpQ]
    linarith [keyQ]
  have hC : ((a : ℚ) + N - 1) / p - ((a : ℚ) - 1) / p = (N : ℚ) / p := by
    rw [← sub_div]
    congr 1
    ring
  linarith [hA, hB, hC.le]

/-- Auxiliary exponential bound used in the estimate `100 * clog 2 (n^2) ≤ n`. -/
lemma two_hundred_mul_succ_le_pow (k : ℕ) (hk : 15 ≤ k) : 200 * (k + 1) ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have h2 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
    have h200 : 200 ≤ 2 ^ k := le_trans (by norm_num) ih
    omega

/-- For `n ≥ 2^15` and `M + 1 ≤ n^2` we have `100 * Nat.clog 2 (M + 1) ≤ n`. -/
lemma hundred_clog_le (n M : ℕ) (hn : 2 ^ 15 ≤ n) (hM : M + 1 ≤ n ^ 2) :
    100 * Nat.clog 2 (M + 1) ≤ n := by
  have h2 : (1 : ℕ) < 2 := by norm_num
  have hk15 : 15 ≤ Nat.log 2 n := by
    have h : Nat.log 2 (2 ^ 15) ≤ Nat.log 2 n := Nat.log_mono_right hn
    rwa [Nat.log_pow h2 15] at h
  have hnpow : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self h2 n
  have hclog : Nat.clog 2 (M + 1) ≤ 2 * (Nat.log 2 n + 1) := by
    have h1 : Nat.clog 2 (M + 1) ≤ Nat.clog 2 (n ^ 2) := Nat.clog_mono_right 2 hM
    have hsq : n ^ 2 ≤ 2 ^ (2 * (Nat.log 2 n + 1)) := by
      have h := pow_le_pow_left₀ (Nat.zero_le _) (le_of_lt hnpow) 2
      rw [← pow_mul] at h
      have e : (Nat.log 2 n + 1) * 2 = 2 * (Nat.log 2 n + 1) := by ring
      rwa [e] at h
    have h2' : Nat.clog 2 (n ^ 2) ≤ 2 * (Nat.log 2 n + 1) := by
      rw [← Nat.clog_pow 2 (2 * (Nat.log 2 n + 1)) h2]
      exact Nat.clog_mono_right 2 hsq
    exact h1.trans h2'
  have h200 := two_hundred_mul_succ_le_pow (Nat.log 2 n) hk15
  have hkn : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  omega

/-- The final numerical inequality: for `n ≥ 2^15`,
`(n^2/1000)^((n+3)/2) > (n/65536)^n + n`. -/
lemma pow_gt_final (n : ℕ) (hn : 2 ^ 15 ≤ n) :
    (1 / 65536 * (n : ℝ)) ^ n + n < ((n : ℝ) ^ 2 / 1000) ^ ((n + 3) / 2) := by
  have hnR : (2 : ℝ) ^ 15 ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have h' : (0 : ℝ) < (2 : ℝ) ^ 15 := by positivity
    linarith
  have hn1ℕ : 1 ≤ n := by omega
  set X : ℝ := (n : ℝ) ^ 2 / 1000 with hXdef
  set e : ℕ := (n + 3) / 2 with he
  set u : ℝ := (1 / 65536 * (n : ℝ)) ^ n with hu
  have hX : (1 : ℝ) ≤ X := by
    have h1 : (1000 : ℝ) ≤ (n : ℝ) ^ 2 := by
      have h3 : ((2 : ℝ) ^ 15) ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hnR 2
      have e : ((2 : ℝ) ^ 15) ^ 2 = (2 : ℝ) ^ 30 := by
        rw [← pow_mul]
      rw [e] at h3
      have h4 : (1000 : ℝ) ≤ (2 : ℝ) ^ 30 := by norm_num
      linarith
    rw [hXdef, le_div_iff₀ (by norm_num : (0 : ℝ) < 1000)]
    linarith
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have h2e : n + 2 ≤ 2 * e := by omega
  have hpow : X ^ (n + 2) ≤ X ^ (2 * e) := pow_le_pow_right₀ hX h2e
  -- `X ^ (n+2)` dwarfs `4 * u ^ 2`
  have keyA : (n : ℝ) ^ 4 * (2 : ℝ) ^ (32 * n) > 4 * 1000 ^ (n + 2) := by
    have h1 : (n : ℝ) ^ 4 ≥ ((2 : ℝ) ^ 15) ^ 4 := pow_le_pow_left₀ (by positivity) hnR 4
    have h1' : (n : ℝ) ^ 4 ≥ 2 := by
      have e : ((2 : ℝ) ^ 15) ^ 4 = (2 : ℝ) ^ 60 := by
        rw [← pow_mul]
      rw [e] at h1
      have h60 : (2 : ℝ) ≤ (2 : ℝ) ^ 60 := by
        have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show 1 ≤ 60 by norm_num)
        simpa using h
      linarith
    have h2 : (2 : ℝ) ^ (32 * n) = ((2 : ℝ) ^ 32) ^ n := by rw [← pow_mul]
    have h3 : (4 * 10 ^ 6 * 1000 : ℝ) ≤ (2 : ℝ) ^ 32 := by norm_num
    have h4 : 4 * 10 ^ 6 * 1000 ^ n ≤ (2 : ℝ) ^ (32 * n) := by
      rw [h2]
      have h4b : (4 * 10 ^ 6 * 1000 : ℝ) ^ n ≤ ((2 : ℝ) ^ 32) ^ n :=
        pow_le_pow_left₀ (by norm_num) h3 n
      have h4a : (4 * 10 ^ 6 * 1000 : ℝ) ^ n = (4 * 10 ^ 6 : ℝ) ^ n * 1000 ^ n := by
        rw [mul_pow]
      have h4c : (4 * 10 ^ 6 : ℝ) ≤ (4 * 10 ^ 6 : ℝ) ^ n := by
        have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4 * 10 ^ 6) hn1ℕ
        simpa using h
      calc 4 * 10 ^ 6 * 1000 ^ n ≤ (4 * 10 ^ 6 : ℝ) ^ n * 1000 ^ n :=
            mul_le_mul_of_nonneg_right h4c (by positivity)
        _ = (4 * 10 ^ 6 * 1000 : ℝ) ^ n := h4a.symm
        _ ≤ ((2 : ℝ) ^ 32) ^ n := h4b
    have h6 : 2 * (4 * 10 ^ 6 * 1000 ^ n) ≤ (n : ℝ) ^ 4 * (2 : ℝ) ^ (32 * n) :=
      mul_le_mul h1' h4 (by positivity) (by positivity)
    have h7 : (4 : ℝ) * 1000 ^ (n + 2) = 4 * 10 ^ 6 * 1000 ^ n := by
      rw [pow_add]
      ring_nf
    have h8 : (0 : ℝ) < 4 * 10 ^ 6 * 1000 ^ n := by positivity
    linarith
  -- `X ^ (n+2)` dwarfs `4 * n ^ 2`
  have keyB : (n : ℝ) ^ (2 * n + 2) > 4 * 1000 ^ (n + 2) := by
    have h1 : ((2 : ℝ) ^ 15) ^ (2 * n + 2) ≤ (n : ℝ) ^ (2 * n + 2) :=
      pow_le_pow_left₀ (by positivity) hnR _
    have h1e : ((2 : ℝ) ^ 15) ^ (2 * n + 2) = (2 : ℝ) ^ (30 * n + 30) := by
      rw [← pow_mul]
      rw [show 15 * (2 * n + 2) = 30 * n + 30 by ring]
    have h2 : (2 : ℝ) ^ (12 * n + 22) ≤ (2 : ℝ) ^ (30 * n + 30) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h3 : (2 : ℝ) ^ (12 * n + 22) = (2 : ℝ) ^ (2 * n + 2) * (2 : ℝ) ^ (10 * n + 20) := by
      rw [← pow_add]
      rw [show 12 * n + 22 = (2 * n + 2) + (10 * n + 20) by ring]
    have h4 : 4 * 1000 ^ (n + 2) < (2 : ℝ) ^ (2 * n + 2) * (2 : ℝ) ^ (10 * n + 20) := by
      have h5 : (4 : ℝ) ≤ (2 : ℝ) ^ (2 * n + 2) := by
        have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show 2 ≤ 2 * n + 2 by omega)
        norm_num at h
        exact h
      have h6 : (1000 : ℝ) ^ (n + 2) < (2 : ℝ) ^ (10 * n + 20) := by
        have e : (1024 : ℝ) ^ (n + 2) = (2 : ℝ) ^ (10 * (n + 2)) := by
          have e10 : (2 : ℝ) ^ 10 = 1024 := by norm_num
          rw [pow_mul, e10]
        have e2 : (2 : ℝ) ^ (10 * (n + 2)) = (2 : ℝ) ^ (10 * n + 20) := by
          rw [show 10 * (n + 2) = 10 * n + 20 by ring]
        have h8 : (1000 : ℝ) ^ (n + 2) < (1024 : ℝ) ^ (n + 2) :=
          pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega : n + 2 ≠ 0)
        rw [e, e2] at h8
        exact h8
      have h9 : 4 * 1000 ^ (n + 2) < 4 * (2 : ℝ) ^ (10 * n + 20) :=
        mul_lt_mul_of_pos_left h6 (by norm_num)
      have h10 : 4 * (2 : ℝ) ^ (10 * n + 20) ≤ (2 : ℝ) ^ (2 * n + 2) * (2 : ℝ) ^ (10 * n + 20) :=
        mul_le_mul_of_nonneg_right h5 (by positivity)
      exact lt_of_lt_of_le h9 h10
    calc 4 * 1000 ^ (n + 2) < (2 : ℝ) ^ (2 * n + 2) * (2 : ℝ) ^ (10 * n + 20) := h4
      _ = (2 : ℝ) ^ (12 * n + 22) := h3.symm
      _ ≤ (2 : ℝ) ^ (30 * n + 30) := h2
      _ = ((2 : ℝ) ^ 15) ^ (2 * n + 2) := h1e.symm
      _ ≤ (n : ℝ) ^ (2 * n + 2) := h1
  have eX : X ^ (n + 2) = (n : ℝ) ^ (2 * n + 4) / 1000 ^ (n + 2) := by
    show ((n : ℝ) ^ 2 / 1000) ^ (n + 2) = _
    rw [div_pow, ← pow_mul]
    rw [show 2 * (n + 2) = 2 * n + 4 by ring]
  have e0 : (1 : ℝ) / 65536 * (n : ℝ) = (n : ℝ) / 65536 := by ring
  have e16 : (65536 : ℝ) = (2 : ℝ) ^ 16 := by norm_num
  have eU : 4 * u ^ 2 = 4 * (n : ℝ) ^ (2 * n) / (2 : ℝ) ^ (32 * n) := by
    show 4 * ((1 / 65536 * (n : ℝ)) ^ n) ^ 2 = _
    rw [e0, ← pow_mul, div_pow, e16, ← pow_mul]
    rw [show n * 2 = 2 * n by ring, show 16 * (2 * n) = 32 * n by ring]
    ring
  have hA : 4 * u ^ 2 < X ^ (2 * e) := by
    have hA' : 4 * u ^ 2 < X ^ (n + 2) := by
      rw [eX, eU, div_lt_div_iff₀ (by positivity) (by positivity)]
      have hf : (n : ℝ) ^ (2 * n + 4) = (n : ℝ) ^ (2 * n) * (n : ℝ) ^ 4 := by
        rw [← pow_add]
      rw [hf]
      have hn2n : (0 : ℝ) < (n : ℝ) ^ (2 * n) := pow_pos hnpos _
      calc (n : ℝ) ^ (2 * n) * (n : ℝ) ^ 4 * (2 : ℝ) ^ (32 * n)
          = (n : ℝ) ^ (2 * n) * ((n : ℝ) ^ 4 * (2 : ℝ) ^ (32 * n)) := by ring
        _ > (n : ℝ) ^ (2 * n) * (4 * 1000 ^ (n + 2)) := mul_lt_mul_of_pos_left keyA hn2n
        _ = 4 * (n : ℝ) ^ (2 * n) * 1000 ^ (n + 2) := by ring
    exact lt_of_lt_of_le hA' hpow
  have hB : 4 * (n : ℝ) ^ 2 < X ^ (2 * e) := by
    have hB' : 4 * (n : ℝ) ^ 2 < X ^ (n + 2) := by
      rw [eX, lt_div_iff₀ (by positivity)]
      have hf2 : (n : ℝ) ^ (2 * n + 4) = (n : ℝ) ^ 2 * (n : ℝ) ^ (2 * n + 2) := by
        rw [← pow_add]
        rw [show 2 * n + 4 = 2 + (2 * n + 2) by ring]
      rw [hf2]
      have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := pow_pos hnpos _
      calc (n : ℝ) ^ 2 * (n : ℝ) ^ (2 * n + 2)
          > (n : ℝ) ^ 2 * (4 * 1000 ^ (n + 2)) := mul_lt_mul_of_pos_left keyB hn2
        _ = 4 * (n : ℝ) ^ 2 * 1000 ^ (n + 2) := by ring
    exact lt_of_lt_of_le hB' hpow
  have hsq : (u + (n : ℝ)) ^ 2 < X ^ (2 * e) := by
    calc (u + (n : ℝ)) ^ 2 = u ^ 2 + 2 * u * (n : ℝ) + (n : ℝ) ^ 2 := by ring
      _ ≤ u ^ 2 + (u ^ 2 + (n : ℝ) ^ 2) + (n : ℝ) ^ 2 := by
          linarith [two_mul_le_add_sq u (n : ℝ)]
      _ = 2 * u ^ 2 + 2 * (n : ℝ) ^ 2 := by ring
      _ < X ^ (2 * e) := by linarith
  by_contra! hcon
  have hle : (X ^ e) ^ 2 ≤ (u + (n : ℝ)) ^ 2 := pow_le_pow_left₀ (pow_nonneg hX0 e) hcon 2
  have heq : (X ^ e) ^ 2 = X ^ (2 * e) := by
    rw [← pow_mul]
    rw [show e * 2 = 2 * e by ring]
  rw [heq] at hle
  linarith

/-- The heart of the proof: for `n ≥ 2^15`, some `a + i` (and symmetrically some
`b + j`) is divisible by more than `(n+1)/2` distinct primes exceeding `n^2/1000`,
which forces `a` to be huge. -/
lemma row_bound (a b n : ℕ) (ha : 0 < a) (hb : 0 < b) (hn : 2 ^ 15 ≤ n)
    (h : ∀ i ∈ range (n + 1), ∀ j ∈ range (n + 1), 1 < Nat.gcd (a + i) (b + j)) :
    ((n : ℝ) ^ 2 / 1000) ^ ((n + 3) / 2) ≤ (a : ℝ) + n := by
  classical
  set N := n + 1 with hN
  set M := n ^ 2 / 1000 with hM
  have hn1000 : 1000 ≤ n := le_trans (by norm_num) hn
  have hMn : n ≤ M := by
    rw [hM, Nat.le_div_iff_mul_le (by norm_num : (0:ℕ) < 1000)]
    have h1 : n * 1000 ≤ n * n := by gcongr
    have e : n ^ 2 = n * n := by ring
    omega
  have hM50 : 50 ≤ M := by
    have h1 : (2 ^ 15 : ℕ) ^ 2 ≤ n ^ 2 := by gcongr
    have h2 : (2 ^ 15) ^ 2 / 1000 ≤ n ^ 2 / 1000 := Nat.div_le_div_right h1
    have e : (2 ^ 15) ^ 2 / 1000 = 1073741 := by norm_num
    omega
  have hM1n2 : M + 1 ≤ n ^ 2 := by
    have h1 : n ^ 2 / 1000 < n ^ 2 :=
      Nat.div_lt_self (pow_pos (by omega : 0 < n) 2) (by norm_num)
    omega
  have hMlt : n ^ 2 < 1000 * (M + 1) := by
    have h1 := Nat.div_add_mod (n ^ 2) 1000
    have h2 := Nat.mod_lt (n ^ 2) (by norm_num : (0:ℕ) < 1000)
    omega
  have hNQ : (N : ℚ) = (n : ℚ) + 1 := by rw [hN]; push_cast; ring
  have hMQ : (n : ℝ) ^ 2 / 1000 ≤ (M : ℝ) + 1 := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 1000)]
    have h' : ((n ^ 2 : ℕ) : ℝ) < (1000 * (M + 1) : ℕ) := by exact_mod_cast hMlt
    push_cast at h'
    linarith
  -- the small primes and the "small" cells
  set P := (range (M + 1)).filter Nat.Prime with hP
  set S := (range N ×ˢ range N).filter
    (fun c => ∃ p ∈ P, p ∣ a + c.1 ∧ p ∣ b + c.2) with hS
  have hsub : S ⊆ P.biUnion (fun p =>
      ((range N).filter (fun i => p ∣ a + i)) ×ˢ ((range N).filter (fun j => p ∣ b + j))) := by
    intro c hc
    rw [hS, Finset.mem_filter] at hc
    obtain ⟨hc1, p, hpP, hpa, hpb⟩ := hc
    rw [Finset.mem_biUnion]
    refine ⟨p, hpP, ?_⟩
    rw [Finset.mem_product] at hc1
    simp only [Finset.mem_product, Finset.mem_filter]
    exact ⟨⟨hc1.1, hpa⟩, ⟨hc1.2, hpb⟩⟩
  have hcardS : (#S : ℚ) ≤ ∑ p ∈ P, ((N : ℚ) / p + 1) * (N / p + 1) := by
    have h1 : #S ≤ ∑ p ∈ P,
        (#((range N).filter (fun i => p ∣ a + i)) * #((range N).filter (fun j => p ∣ b + j))) := by
      calc #S ≤ #(P.biUnion (fun p =>
            ((range N).filter (fun i => p ∣ a + i)) ×ˢ
            ((range N).filter (fun j => p ∣ b + j)))) := Finset.card_le_card hsub
        _ ≤ ∑ p ∈ P, #(((range N).filter (fun i => p ∣ a + i)) ×ˢ
            ((range N).filter (fun j => p ∣ b + j))) := Finset.card_biUnion_le
        _ = ∑ p ∈ P, (#((range N).filter (fun i => p ∣ a + i)) *
            #((range N).filter (fun j => p ∣ b + j))) := by
            simp only [Finset.card_product]
    have h2 : (∑ p ∈ P, ((#((range N).filter (fun i => p ∣ a + i)) *
          #((range N).filter (fun j => p ∣ b + j)) : ℕ) : ℚ))
        ≤ ∑ p ∈ P, ((N : ℚ) / p + 1) * (N / p + 1) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [hP, Finset.mem_filter] at hp
      have hpp : 0 < p := hp.2.pos
      have hpa : (((range N).filter (fun i => p ∣ a + i)).card : ℚ) ≤ (N : ℚ) / p + 1 :=
        card_filter_dvd_le a N p ha hpp
      have hpb : (((range N).filter (fun j => p ∣ b + j)).card : ℚ) ≤ (N : ℚ) / p + 1 :=
        card_filter_dvd_le b N p hb hpp
      have h0 : (0 : ℚ) ≤ (N : ℚ) / p + 1 := by positivity
      push_cast
      exact mul_le_mul hpa hpb (by positivity) h0
    calc (#S : ℚ) ≤ (∑ p ∈ P, (#((range N).filter (fun i => p ∣ a + i)) *
          #((range N).filter (fun j => p ∣ b + j)) : ℕ) : ℚ) := by exact_mod_cast h1
      _ ≤ ∑ p ∈ P, ((N : ℚ) / p + 1) * (N / p + 1) := h2
  have hexpand : ∑ p ∈ P, ((N : ℚ) / p + 1) * (N / p + 1) =
      (N : ℚ) ^ 2 * (∑ p ∈ P, (1 : ℚ) / p ^ 2) + 2 * N * (∑ p ∈ P, (1 : ℚ) / p) + #P := by
    have hterm : ∀ p ∈ P, ((N : ℚ) / p + 1) * (N / p + 1) =
        (N : ℚ) ^ 2 * (1 / p ^ 2) + (2 * N * (1 / p) + 1) := by
      intro p hp
      rw [hP, Finset.mem_filter] at hp
      have hpp : (p : ℚ) ≠ 0 := by exact_mod_cast hp.2.pos.ne'
      field_simp
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one, add_assoc]
  have hsum1 : ∑ p ∈ P, (1 : ℚ) / p ^ 2 ≤ 47 / 100 := by
    rw [hP]
    exact primesum_inv_sq_le M hM50
  have hsum2 : ∑ p ∈ P, (1 : ℚ) / p ≤ Nat.clog 2 (M + 1) := by
    have hsub2 : P ⊆ Icc 1 M := by
      intro p hp
      rw [hP, Finset.mem_filter, Finset.mem_range] at hp
      rw [Finset.mem_Icc]
      exact ⟨hp.2.one_le, by omega⟩
    calc ∑ p ∈ P, (1 : ℚ) / p ≤ ∑ k ∈ Icc 1 M, (1 : ℚ) / k :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun i _ _ => by positivity)
      _ ≤ Nat.clog 2 (M + 1) := sum_Icc_one_div_le_clog M
  have hcardP : (#P : ℚ) ≤ M := by
    have hsub3 : P ⊆ Icc 2 M := by
      intro p hp
      rw [hP, Finset.mem_filter, Finset.mem_range] at hp
      rw [Finset.mem_Icc]
      exact ⟨hp.2.two_le, by omega⟩
    have h1 : #P ≤ #(Icc 2 M) := Finset.card_le_card hsub3
    rw [Nat.card_Icc] at h1
    have h2 : #P ≤ M := by omega
    exact_mod_cast h2
  have hclog : (Nat.clog 2 (M + 1) : ℚ) ≤ (n : ℚ) / 100 := by
    have h := hundred_clog_le n M hn hM1n2
    have h' : (100 : ℚ) * (Nat.clog 2 (M + 1) : ℚ) ≤ n := by exact_mod_cast h
    linarith
  have hMN : (M : ℚ) < (N : ℚ) ^ 2 / 100 := by
    have h1 : (M : ℚ) ≤ (n : ℚ) ^ 2 / 1000 := by
      have h := Nat.cast_div_le (m := n ^ 2) (n := 1000) (α := ℚ)
      rw [hM]
      push_cast at h
      exact h
    have h2 : (n : ℚ) ^ 2 / 1000 < ((n : ℚ) + 1) ^ 2 / 100 := by
      have hnpos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast (by omega : 0 < n)
      have h3 : (n : ℚ) ^ 2 < 10 * ((n : ℚ) + 1) ^ 2 := by nlinarith [sq_nonneg (n : ℚ), hnpos]
      nlinarith [h3, hnpos]
    rw [hNQ]
    nlinarith [h1, h2]
  have hsmall : (#S : ℚ) < (N : ℚ) ^ 2 / 2 := by
    have hcardS' : (#S : ℚ) ≤
        (N : ℚ) ^ 2 * (∑ p ∈ P, (1 : ℚ) / p ^ 2) + 2 * N * (∑ p ∈ P, (1 : ℚ) / p) + #P :=
      hcardS.trans (le_of_eq hexpand)
    have key2 : 2 * (N : ℚ) * ((n : ℚ) / 100) ≤ (N : ℚ) ^ 2 * (2 / 100) := by
      have hle : (n : ℚ) ≤ (N : ℚ) := by rw [hNQ]; linarith
      have e : (n : ℚ) / 100 ≤ (N : ℚ) / 100 := by gcongr
      have g : 2 * (N : ℚ) * ((n : ℚ) / 100) ≤ 2 * (N : ℚ) * ((N : ℚ) / 100) :=
        mul_le_mul_of_nonneg_left e (by positivity)
      have e2 : 2 * (N : ℚ) * ((N : ℚ) / 100) = (N : ℚ) ^ 2 * (2 / 100) := by ring
      rw [e2] at g
      exact g
    calc (#S : ℚ) ≤ (N : ℚ) ^ 2 * (∑ p ∈ P, (1 : ℚ) / p ^ 2) + 2 * N * (∑ p ∈ P, (1 : ℚ) / p) + #P := hcardS'
      _ ≤ (N : ℚ) ^ 2 * (47 / 100) + 2 * N * ((n : ℚ) / 100) + M := by
          have g1 : (N : ℚ) ^ 2 * (∑ p ∈ P, (1 : ℚ) / p ^ 2) ≤ (N : ℚ) ^ 2 * (47 / 100) :=
            mul_le_mul_of_nonneg_left hsum1 (by positivity)
          have g2 : 2 * (N : ℚ) * (∑ p ∈ P, (1 : ℚ) / p) ≤ 2 * (N : ℚ) * ((n : ℚ) / 100) :=
            mul_le_mul_of_nonneg_left (hsum2.trans hclog) (by positivity)
          linarith [g1, g2, hcardP]
      _ < (N : ℚ) ^ 2 * (47 / 100) + (N : ℚ) ^ 2 * (2 / 100) + (N : ℚ) ^ 2 / 100 := by
          linarith [key2, hMN]
      _ = (N : ℚ) ^ 2 / 2 := by ring
  -- the "big" cells
  set Big := (range N ×ˢ range N) \ S with hBig
  have hBigCard : (N : ℚ) ^ 2 / 2 < (#Big : ℚ) := by
    have hle' : #S ≤ N * N := by
      have h1 : #S ≤ #(range N ×ˢ range N) := Finset.card_filter_le _ _
      rwa [Finset.card_product, Finset.card_range] at h1
    have h1 : #Big = N * N - #S := by
      rw [hBig, Finset.card_sdiff_of_subset (Finset.filter_subset _ _),
        Finset.card_product, Finset.card_range]
    have h3 : (#Big : ℚ) = (N : ℚ) ^ 2 - #S := by
      rw [h1, Nat.cast_sub hle']
      push_cast
      ring
    rw [h3]
    linarith [hsmall]
  -- pigeonhole: some row has many big cells
  have hmaps : Set.MapsTo (Prod.fst : ℕ × ℕ → ℕ) (↑Big) (↑(range N) : Set ℕ) := by
    intro c hc
    rw [Finset.mem_coe, hBig, Finset.mem_sdiff] at hc
    exact Finset.mem_coe.2 (Finset.mem_product.1 hc.1).1
  have hfiber : ∀ i ∈ range N, #{c ∈ Big | c.1 = i} =
      #((range N).filter (fun j => (i, j) ∉ S)) := by
    intro i hi
    apply Finset.card_bij (fun c _ => c.2)
    · intro c hc
      rw [Finset.mem_filter] at hc
      rw [hBig, Finset.mem_sdiff, Finset.mem_product] at hc
      rw [Finset.mem_filter]
      refine ⟨hc.1.1.2, ?_⟩
      rw [← hc.2]
      exact hc.1.2
    · intro c₁ hc₁ c₂ hc₂ heq
      rw [Finset.mem_filter] at hc₁ hc₂
      exact Prod.ext_iff.2 ⟨by rw [hc₁.2, hc₂.2], heq⟩
    · intro j hj
      rw [Finset.mem_filter] at hj
      exact ⟨(i, j), by
        rw [Finset.mem_filter]
        exact ⟨by rw [hBig, Finset.mem_sdiff, Finset.mem_product]; exact ⟨⟨hi, hj.1⟩, hj.2⟩,
          rfl⟩, rfl⟩
  have hsumQ : (#Big : ℚ) =
      ∑ i ∈ range N, (#((range N).filter (fun j => (i, j) ∉ S)) : ℚ) := by
    have h1 : #Big = ∑ i ∈ range N, #((range N).filter (fun j => (i, j) ∉ S)) := by
      rw [Finset.card_eq_sum_card_fiberwise hmaps]
      exact Finset.sum_congr rfl hfiber
    rw [h1]
    norm_cast
  have hrows : ∃ i₀ ∈ range N, (N : ℚ) / 2 <
      (#((range N).filter (fun j => (i₀, j) ∉ S)) : ℚ) := by
    have hlt : ∑ _i ∈ range N, (N : ℚ) / 2 <
        ∑ i ∈ range N, (#((range N).filter (fun j => (i, j) ∉ S)) : ℚ) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← hsumQ]
      have e : (N : ℚ) * (N / 2) = (N : ℚ) ^ 2 / 2 := by ring
      rw [e]
      exact hBigCard
    exact Finset.exists_lt_of_sum_lt hlt
  obtain ⟨i₀, hi₀, hrow⟩ := hrows
  set R := (range N).filter (fun j => (i₀, j) ∉ S) with hR
  -- choose a large prime divisor for each big cell of the row
  have hex : ∀ j ∈ R, ∃ q : ℕ, q.Prime ∧ M + 1 ≤ q ∧ q ∣ a + i₀ ∧ q ∣ b + j := by
    intro j hj
    simp only [hR, Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨hjN, hjS⟩ := hj
    have hgcd : 1 < Nat.gcd (a + i₀) (b + j) := h i₀ hi₀ j (Finset.mem_range.2 hjN)
    have hne : Nat.gcd (a + i₀) (b + j) ≠ 1 := by omega
    obtain ⟨q, hqP, hqd⟩ := Nat.exists_prime_and_dvd hne
    have hqa : q ∣ a + i₀ := dvd_trans hqd (Nat.gcd_dvd_left _ _)
    have hqb : q ∣ b + j := dvd_trans hqd (Nat.gcd_dvd_right _ _)
    refine ⟨q, hqP, ?_, hqa, hqb⟩
    by_contra! hcon
    have hqPmem : q ∈ P := by
      rw [hP, Finset.mem_filter, Finset.mem_range]
      exact ⟨hcon, hqP⟩
    apply hjS
    rw [hS, Finset.mem_filter]
    exact ⟨by rw [Finset.mem_product]; exact ⟨hi₀, Finset.mem_range.2 hjN⟩, q, hqPmem, hqa, hqb⟩
  choose! q hq using hex
  have hinj : Set.InjOn q (↑R) := by
    intro j₁ hj₁ j₂ hj₂ heq
    have hj₁F : j₁ ∈ R := hj₁
    have hj₂F : j₂ ∈ R := hj₂
    obtain ⟨hp1, hM1, hd1a, hd1b⟩ := hq j₁ hj₁F
    obtain ⟨hp2, hM2, hd2a, hd2b⟩ := hq j₂ hj₂F
    have hj₁N : j₁ < N := by
      have h1 : j₁ ∈ (range N).filter (fun j => (i₀, j) ∉ S) := hj₁F
      rw [Finset.mem_filter, Finset.mem_range] at h1
      exact h1.1
    have hj₂N : j₂ < N := by
      have h2 : j₂ ∈ (range N).filter (fun j => (i₀, j) ∉ S) := hj₂F
      rw [Finset.mem_filter, Finset.mem_range] at h2
      exact h2.1
    rcases le_total j₁ j₂ with hle | hle
    · have hdvd : q j₁ ∣ j₂ - j₁ := by
        have h2 : q j₁ ∣ b + j₂ := by rw [heq]; exact hd2b
        have h3 := Nat.dvd_sub h2 hd1b
        rwa [show (b + j₂) - (b + j₁) = j₂ - j₁ by omega] at h3
      have hlt : j₂ - j₁ < q j₁ := by omega
      have hz : j₂ - j₁ = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
      omega
    · have hdvd : q j₂ ∣ j₁ - j₂ := by
        have h2 : q j₂ ∣ b + j₁ := by rw [← heq]; exact hd1b
        have h3 := Nat.dvd_sub h2 hd2b
        rwa [show (b + j₁) - (b + j₂) = j₁ - j₂ by omega] at h3
      have hlt : j₁ - j₂ < q j₂ := by omega
      have hz : j₁ - j₂ = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
      omega
  -- the product of these primes divides `a + i₀`
  set I := R.image q with hI
  have hcardI : #I = #R := Finset.card_image_of_injOn hinj
  have hprod_dvd : ∏ p ∈ I, p ∣ a + i₀ := by
    apply Finset.prod_primes_dvd
    · intro p hp
      rw [hI, Finset.mem_image] at hp
      obtain ⟨j, hj, rfl⟩ := hp
      exact (hq j hj).1.prime
    · intro p hp
      rw [hI, Finset.mem_image] at hp
      obtain ⟨j, hj, rfl⟩ := hp
      exact (hq j hj).2.2.1
  have hprod_ge : (M + 1) ^ #I ≤ ∏ p ∈ I, p := by
    rw [← Finset.prod_const]
    apply Finset.prod_le_prod
    · intro p hp
      positivity
    · intro p hp
      rw [hI, Finset.mem_image] at hp
      obtain ⟨j, hj, rfl⟩ := hp
      exact (hq j hj).2.1
  have hbig : (M + 1) ^ #I ≤ a + i₀ :=
    le_trans hprod_ge (Nat.le_of_dvd (by omega) hprod_dvd)
  -- wrap up
  have h2s : n + 2 ≤ 2 * #R := by
    have e : (n : ℚ) + 1 < 2 * (#R : ℚ) := by
      rw [hNQ] at hrow
      linarith
    have h' : n + 1 < 2 * #R := by exact_mod_cast e
    omega
  have hes : (n + 3) / 2 ≤ #R := by omega
  have hbig' : ((M : ℝ) + 1) ^ #R ≤ (a : ℝ) + i₀ := by
    have h1 : (M + 1 : ℕ) ^ #R ≤ a + i₀ := by rwa [hcardI] at hbig
    calc ((M : ℝ) + 1) ^ #R = (((M + 1 : ℕ) ^ #R : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((a + i₀ : ℕ) : ℝ) := by exact_mod_cast h1
      _ = (a : ℝ) + i₀ := by push_cast; ring
  have hi0n : (i₀ : ℝ) ≤ (n : ℝ) := by
    have h1 : i₀ ≤ n := by
      rw [hN, Finset.mem_range] at hi₀
      omega
    exact_mod_cast h1
  have hchain1 : ((n : ℝ) ^ 2 / 1000) ^ ((n + 3) / 2) ≤ ((M : ℝ) + 1) ^ ((n + 3) / 2) :=
    pow_le_pow_left₀ (by positivity) hMQ _
  have hM1 : (1 : ℝ) ≤ (M : ℝ) + 1 := by
    have h0 : (0 : ℝ) ≤ (M : ℝ) := by positivity
    linarith
  have hchain2 : ((M : ℝ) + 1) ^ ((n + 3) / 2) ≤ ((M : ℝ) + 1) ^ #R :=
    pow_le_pow_right₀ hM1 hes
  calc ((n : ℝ) ^ 2 / 1000) ^ ((n + 3) / 2) ≤ ((M : ℝ) + 1) ^ #R :=
        le_trans hchain1 hchain2
    _ ≤ (a : ℝ) + i₀ := hbig'
    _ ≤ (a : ℝ) + n := by linarith

snip end

problem usa2014_p6 :
    ∃ c : ℝ, 0 < c ∧
      ∀ a b n : ℕ, 0 < a → 0 < b → 0 < n →
        (∀ i ∈ range (n + 1), ∀ j ∈ range (n + 1), 1 < Nat.gcd (a + i) (b + j)) →
        (c * (n : ℝ)) ^ n < ((min a b : ℕ) : ℝ) := by
  refine ⟨1 / 65536, by norm_num, ?_⟩
  intro a b n ha hb hn h
  rcases lt_or_ge n (2 ^ 15) with hsmall | hlarge
  · -- small `n`: `min a b ≥ 2` beats anything below `1`
    have h0mem : (0 : ℕ) ∈ range (n + 1) := Finset.mem_range.2 (Nat.succ_pos n)
    have hgcd : 1 < Nat.gcd a b := by
      have h00 := h 0 h0mem 0 h0mem
      simpa using h00
    have ha2 : 2 ≤ a := le_trans hgcd (Nat.le_of_dvd ha (Nat.gcd_dvd_left a b))
    have hb2 : 2 ≤ b := le_trans hgcd (Nat.le_of_dvd hb (Nat.gcd_dvd_right a b))
    have hmin : (2 : ℝ) ≤ ((min a b : ℕ) : ℝ) := by
      have h' : 2 ≤ min a b := le_min_iff.2 ⟨ha2, hb2⟩
      exact_mod_cast h'
    have hpow : (1 / 65536 * (n : ℝ)) ^ n < 1 := by
      have hn65 : (n : ℝ) < 65536 := by
        have h' : n < 65536 := by
          have e : 2 ^ 15 = 32768 := by norm_num
          omega
        exact_mod_cast h'
      have h1lt : 1 / 65536 * (n : ℝ) < 1 := by linarith [hn65]
      exact pow_lt_one₀ (by positivity) h1lt (by omega)
    have hmin1 : (1 : ℝ) < ((min a b : ℕ) : ℝ) := by linarith [hmin]
    linarith [hpow, hmin1]
  · -- large `n`: the counting argument
    have hAB := row_bound a b n ha hb hlarge h
    have hBA : ((n : ℝ) ^ 2 / 1000) ^ ((n + 3) / 2) ≤ (b : ℝ) + n := by
      apply row_bound b a n hb ha hlarge
      intro i hi j hj
      have h' := h j hj i hi
      rwa [Nat.gcd_comm] at h'
    have hfin := pow_gt_final n hlarge
    have ha' : (1 / 65536 * (n : ℝ)) ^ n < (a : ℝ) := by linarith [hAB, hfin]
    have hb' : (1 / 65536 * (n : ℝ)) ^ n < (b : ℝ) := by linarith [hBA, hfin]
    rw [Nat.cast_min, lt_min_iff]
    exact ⟨ha', hb'⟩

end Usa2014P6
