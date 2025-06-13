/-
Copyright (c) 2025 Roozbeh Yousefzadeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Roozbeh Yousefzadeh
-/

import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic

import ProblemExtraction

problem_file {
  tags := [.NumberTheory]
  importedFrom := "https://github.com/roozbeh-yz/IMO-Steps/blob/main/Lean_v20/imo_proofs/imo_1967_p3.lean"
}

/-!
# International Mathematical Olympiad 1967, Problem 3

Let $k, m, n$ be natural numbers such that m + k + 1 is a prime greater than n + 1. Let c(s) = s * (s+1).
Prove that the product (c(m+1) - c(k)) * (c(m+2) - c(k)) * ... * (c(m+n) - c(k)) is divisible by the product c(1) * c(2) * ... * c(n).
-/

namespace Imo1967P3


problem imo_1967_p3
  (k m n : ℕ)
  (c : ℕ → ℕ)
  (h₀ : 0 < k ∧ 0 < m ∧ 0 < n)
  (h₁ : ∀ s, c s = s * (s + 1))
  (h₂ : Nat.Prime (k + m + 1))
  (h₃ : n + 1 < k + m + 1) :
  (∏ i ∈ Finset.Icc 1 n, c i) ∣ (∏ i ∈ Finset.Icc 1 n, (c (m + i) - c k)) := by
  have h₄: ∏ i ∈ Finset.Icc 1 n, c i = n.factorial * (n + 1).factorial := by
    have h₄₀ : ∀ i, c i = i * (i + 1) := by
      intro i
      specialize h₁ i
      simpa using h₁
    simp_rw [h₄₀]
    refine Nat.le_induction ?_ ?_ n h₀.2.2
    . simp
    . simp
      intros d hd₀ hd₁
      rw [Finset.prod_Icc_succ_top (by linarith), hd₁]
      rw [Nat.factorial_succ (d + (1 : ℕ))]
      rw [← mul_assoc, mul_comm _ (d + (1 : ℕ)), ← mul_assoc]
      rw [← Nat.factorial_succ]
      ring_nf
  have h₅: (∏ i ∈ Finset.Icc 1 n, (c (m + i) - c k)) = (∏ i ∈ Finset.Icc 1 n, (m + i + k + 1)) * (∏ i ∈ Finset.Icc 1 n, (m + i - k)) := by
    have h₅₀: ∀ a b, c a - c b = (a - b) * (a + b + 1) := by
      intros a b
      rw [h₁, h₁]
      ring_nf
      rw [Nat.mul_sub, Nat.mul_sub]
      ring_nf
      by_cases ha₀: b ≤ a
      . have ha₁: b ^ 2 ≤ a * b := by nlinarith
        have ha₂: a * b ≤ a ^ 2 := by nlinarith
        rw [← Nat.add_sub_assoc ha₁, Nat.sub_add_cancel ha₂]
        omega
      . push_neg at ha₀
        have ha₁ : a + a ^ (2 : ℕ) ≤ (b + b ^ (2 : ℕ)) := by
          refine Nat.add_le_add ?_ ?_
          . exact Nat.le_of_succ_le ha₀
          . refine Nat.pow_le_pow_left ?_ (2 : ℕ)
            exact Nat.le_of_succ_le ha₀
        have ha₂ : a ^ (2 : ℕ) ≤ a * b := by
          rw [pow_two]
          refine Nat.mul_le_mul ?_ ?_
          . exact Nat.le_refl a
          . exact Nat.le_of_succ_le ha₀
        have ha₃ : a * b ≤ b ^ (2 : ℕ) := by
          rw [pow_two]
          refine Nat.mul_le_mul ?_ ?_
          . exact Nat.le_of_succ_le ha₀
          . exact Nat.le_refl b
        rw [Nat.sub_eq_zero_of_le ha₁, Nat.sub_eq_zero_of_le ha₂]
        rw [Nat.sub_eq_zero_of_le (le_of_lt ha₀)]
        rw [Nat.sub_eq_zero_of_le ha₃]
    simp_rw [h₅₀]
    rw [Nat.mul_comm]
    exact Finset.prod_mul_distrib
  rw [h₄, h₅]
  by_cases hk₀: k ≤ m
  . have h₆: ∀ n m, 0 < n → n.factorial ∣ (∏ i ∈ Finset.Icc 1 n, (m + i)) := by
      intros s t hs₀
      have h₆₀ : ∏ i ∈ Finset.Icc (1 : ℕ) s, (t + i) = (t + s).factorial / t.factorial := by
        refine Nat.eq_div_of_mul_eq_right ?_ ?_
        . positivity
        . refine Nat.le_induction ?_ ?_ s hs₀
          . simp
            rw [Nat.mul_comm]
            exact rfl
          . simp
            intros d hd₀ hd₁
            rw [Finset.prod_Icc_succ_top (by linarith), ← mul_assoc, hd₁]
            rw [← add_assoc]
            rw [Nat.factorial_succ]
            exact Nat.mul_comm (t + d).factorial (t + d + (1 : ℕ))
      have h₆₁ : (∏ i ∈ Finset.Icc 1 s, (t + i)) = s.factorial * Nat.choose (t + s) (t) := by
        rw [h₆₀]
        have hk₁ : t ≤ t + s := by exact Nat.le_add_right t s
        rw [Nat.choose_eq_factorial_div_factorial hk₁]
        rw [Nat.add_sub_cancel_left]
        have hk₂: ((t).factorial * s.factorial) ∣ (t + s).factorial := by exact Nat.factorial_mul_factorial_dvd_factorial_add t s
        have ht₁: 0 < s.factorial := by exact Nat.factorial_pos s
        rw [← Nat.mul_div_assoc _ hk₂, mul_comm]
        rw [Nat.mul_div_mul_right _ _ ht₁]
      rw [h₆₁]
      exact Nat.dvd_mul_right s.factorial ((t + s).choose t)
    have h₇: n.factorial ∣ (∏ i ∈ Finset.Icc 1 n, (m + i - k)) := by
      have h₇₀: ∀ i, m + i - k = m - k + i := by
        intro i
        exact Nat.sub_add_comm hk₀
      simp_rw [h₇₀]
      exact h₆ n (m - k) h₀.2.2
    have h₈: (n + (1 : ℕ)).factorial ∣ (∏ i ∈ Finset.Icc (1 : ℕ) n, (m + i + k + (1 : ℕ))) := by
      have h₈₀: (n + (1 : ℕ)).factorial ∣ (k + m + 1) * (∏ i ∈ Finset.Icc (1 : ℕ) n, (m + i + k + (1 : ℕ))) := by
        have hn₀ : 0 < n + 1 := by exact Nat.zero_lt_succ n
        have h₈₁: ∀ i, m + i + k + (1 : ℕ) = m + k + (1 : ℕ) + i := by bound
        have h₈₂: (k + m + 1) * (∏ i ∈ Finset.Icc (1 : ℕ) n, (m + i + k + (1 : ℕ))) = ∏ i ∈ Finset.Ico (0 : ℕ) (n + 1), (m + i + k + (1 : ℕ)) := by
          simp_rw [h₈₁]
          rw [Finset.prod_eq_prod_Ico_succ_bot hn₀ (fun i ↦ m + k + (1 : ℕ) + i)]
          rw [add_zero, add_comm k m]
          exact rfl
        simp_rw [h₈₂]
        have h₈₃: ∏ i ∈ Finset.Ico (0 : ℕ) (n + (1 : ℕ)), (m + i + k + (1 : ℕ)) = ∏ i ∈ Finset.Ico (1 : ℕ) (n + 2), (m + i + k) := by
          rw [Finset.prod_Ico_eq_prod_range, Finset.prod_Ico_eq_prod_range]
          simp
          group
        have h₈₄: ∏ i ∈ Finset.Ico (1 : ℕ) (n + (2 : ℕ)), (m + i + k) = ∏ i ∈ Finset.Icc (1 : ℕ) (n + (1 : ℕ)), (m + i + k) := by rfl
        rw [h₈₃, h₈₄]
        have h₈₅: ∀ i, m + i + k = m + k + i := by exact fun (i : ℕ) ↦ Nat.add_right_comm m i k
        simp_rw [h₈₅]
        exact h₆ (n + 1) (m + k) hn₀
      refine Nat.Coprime.dvd_of_dvd_mul_left ?_ h₈₀
      refine Nat.Coprime.symm ?_
      refine (Nat.coprime_factorial_iff ?_).mpr ?_
      . exact Nat.Prime.ne_one h₂
      . rw [Nat.Prime.minFac_eq h₂]
        exact h₃
    rw [mul_comm]
    exact Nat.mul_dvd_mul h₈ h₇
  . push_neg at hk₀
    have h₆ : ∏ i ∈ Finset.Icc (1 : ℕ) n, (m + i - k) = 0 := by
      refine Nat.le_induction ?_ ?_ n h₀.2.2
      . simp
        rw [Nat.sub_eq_zero_of_le hk₀]
      . simp
        intros d hd₀ hd₁
        rw [Finset.prod_Icc_succ_top (by linarith), hd₁, zero_mul]
    rw [h₆, mul_zero]
    exact Nat.dvd_zero (n.factorial * (n + (1 : ℕ)).factorial)

