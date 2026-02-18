/-
Copyright (c) 2025 Roozbeh Yousefzadeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roozbeh Yousefzadeh
-/

import Mathlib

import ProblemExtraction

set_option backward.isDefEq.respectTransparency false


problem_file {
  tags := [.NumberTheory]
  solutionImportedFrom := "https://github.com/roozbeh-yz/IMO-Steps/blob/main/Lean_v20/imo_proofs/imo_1967_p3.lean"
}

/-!
# International Mathematical Olympiad 1967, Problem 3

Let $k, m, n$ be natural numbers such that m + k + 1 is a prime greater
than n + 1. Let c(s) = s * (s+1). Prove that the product
(c(m+1) - c(k)) * (c(m+2) - c(k)) * ... * (c(m+n) - c(k)) is divisible
by the product c(1) * c(2) * ... * c(n).
-/

namespace Imo1967P3


snip begin

lemma aux_1
    (c : ℕ → ℕ)
    (h₁ : ∀ (s : ℕ), c s = s * (s + 1)) :
    ∀ (a b : ℕ), c a - c b = (a - b) * (a + b + 1) := by
  intro a b
  rw [h₁, h₁]
  have h_factor : a + a^2 - (b + b^2) = (a - b) * (a + b + 1) := by rw [tsub_mul]; grind
  grind

lemma aux_1_mono
    (c : ℕ → ℕ)
    (h₁ : ∀ (s : ℕ), c s = s * (s + 1)) :
    Monotone c := by
  intro a b h
  simp only [h₁]
  have h1 : a * (a + 1) ≤ b * (a + 1) := Nat.mul_le_mul_right _ h
  have h2 : b * (a + 1) ≤ b * (b + 1) := Nat.mul_le_mul_left _ (Nat.succ_le_succ h)
  exact h1.trans h2

lemma aux_2 :
  ∀ (n m : ℕ), 0 < n → n.factorial ∣ ∏ i ∈ Finset.Icc 1 n, (m + i) := by
  intro s t _
  -- Product equals ascending factorial: (t+1)(t+2)...(t+s) = (t+1).ascFactorial s
  have hprod : ∏ i ∈ Finset.Icc 1 s, (t + i) = (t + 1).ascFactorial s := by
    rw [Nat.ascFactorial_eq_prod_range, ← Finset.Ico_succ_right_eq_Icc, Finset.prod_Ico_eq_prod_range]
    apply Finset.prod_congr rfl; intro i _; ring
  rw [hprod]
  exact Nat.factorial_dvd_ascFactorial (t + 1) s

lemma aux_3
  (k m n : ℕ)
  (h₀ : 0 < k ∧ 0 < m ∧ 0 < n)
  (h₁ : Nat.Prime (k + m + 1))
  (h₂ : n + 1 < k + m + 1) :
  (n + 1).factorial ∣ ∏ i ∈ Finset.Icc 1 n, (m + i + k + 1) := by
  have h₃: ∀ (n m : ℕ), 0 < n → n.factorial ∣ ∏ i ∈ Finset.Icc 1 n, (m + i) := by
    exact fun (n m : ℕ) (a : 0 < n) ↦ aux_2 n m a
  have h₄: (n + (1 : ℕ)).factorial ∣ (k + m + 1) * (∏ i ∈ Finset.Icc (1 : ℕ) n, (m + i + k + (1 : ℕ))) := by
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
    exact h₃ (n + 1) (m + k) hn₀
  refine Nat.Coprime.dvd_of_dvd_mul_left ?_ h₄
  refine Nat.Coprime.symm ?_
  exact Nat.Prime.coprime_factorial_of_lt h₁ h₂

lemma aux_4
    (k m n : ℕ)
    (_ : n ≤ k - (m + 1)) :
    ∏ i ∈ Finset.Icc 1 n, (k - (m + i)) = (k - (m + 1)).descFactorial n := by
  rw [Nat.descFactorial_eq_prod_range, ← Finset.Ico_succ_right_eq_Icc, Finset.prod_Ico_eq_prod_range]
  apply Finset.prod_congr rfl; intro i _; lia

snip end


problem imo1967_p3
  (k m n : ℕ)
  (c : ℕ → ℕ)
  (h₀ : 0 < k ∧ 0 < m ∧ 0 < n)
  (h₁ : ∀ s, c s = s * (s + 1))
  (h₂ : Nat.Prime (k + m + 1))
  (h₃ : n + 1 < k + m + 1) :
  (∏ i ∈ Finset.Icc 1 n, (↑(c i):ℤ)) ∣ (∏ i ∈ Finset.Icc 1 n, (((c (m + i)):ℤ) - ((c k):ℤ))) := by
  have h₄: ∏ i ∈ Finset.Icc 1 n, (↑(c i):ℤ) = n.factorial * (n + 1).factorial := by
    norm_cast
    have h₄₀ : ∀ i, c i = i * (i + 1) := by
      intro i
      specialize h₁ i
      simpa using h₁
    simp_rw [h₄₀]
    refine Nat.le_induction ?_ ?_ n h₀.2.2
    · simp
    · simp only [Nat.succ_eq_add_one, zero_add]
      intro d hd₀ hd₁
      rw [Finset.prod_Icc_succ_top (by lia), hd₁]
      rw [Nat.factorial_succ (d + (1 : ℕ))]
      rw [← mul_assoc, mul_comm _ (d + (1 : ℕ)), ← mul_assoc]
      rw [← Nat.factorial_succ]
      ring_nf
  rw [h₄]
  by_cases hk₀: k ≤ m
  · have h₅: (∏ i ∈ Finset.Icc 1 n, (((c (m + i)):ℤ) - ((c k):ℤ))) = (∏ i ∈ Finset.Icc 1 n, (m + i + k + 1)) * (∏ i ∈ Finset.Icc 1 n, (m + i - k)) := by
      have h₅₁: ∏ i ∈ Finset.Icc 1 n, (((c (m + i)):ℤ) - ((c k):ℤ)) = (↑(∏ i ∈ Finset.Icc 1 n, ((c (m + i)) - (c k))):ℤ) := by
        rw [@Nat.cast_prod]
        refine Finset.prod_congr rfl ?_
        intro x hx₀
        symm
        refine Nat.cast_sub ?_

        have hk_le_mx : k ≤ m + x := hk₀.trans (Nat.le_add_right _ _)
        exact aux_1_mono c h₁ hk_le_mx
      rw [h₅₁, ← Nat.cast_mul]
      norm_cast
      simp_rw [aux_1 c h₁]
      rw [Nat.mul_comm]
      exact Finset.prod_mul_distrib
    have h₇: n.factorial ∣ (∏ i ∈ Finset.Icc 1 n, (m + i - k)) := by
      have h₇₀: ∀ i, m + i - k = m - k + i := by
        intro i
        exact Nat.sub_add_comm hk₀
      simp_rw [h₇₀]
      exact aux_2 n (m - k) h₀.2.2
    have h₈: (n + (1 : ℕ)).factorial ∣ (∏ i ∈ Finset.Icc (1 : ℕ) n, (m + i + k + (1 : ℕ))) := by
      exact aux_3 k m n h₀ h₂ h₃
    rw [h₅, mul_comm]
    refine Nat.cast_dvd_cast ?_
    exact Nat.mul_dvd_mul h₈ h₇
  · push_neg at hk₀
    by_cases hk₁: k ≤ m + n
    · have h₆ : ∏ i ∈ Finset.Icc (1 : ℕ) n, ((↑(c (m + i)) : ℤ) - (↑(c k) : ℤ)) = 0 := by
        refine Finset.prod_eq_zero_iff.mpr ?_
        use (k - m)
        constructor
        · refine Finset.mem_Icc.mpr ?_
          lia
        · grind
      rw [h₆]
      exact Int.dvd_zero ((↑n.factorial : ℤ) * (↑(n + (1 : ℕ)).factorial : ℤ))
    · push_neg at hk₁
      have h₅: ∏ i ∈ Finset.Icc (1 : ℕ) n, ((↑(c (m + i)) : ℤ) - (↑(c k) : ℤ)) =
        ∏ i ∈ Finset.Icc (1 : ℕ) n, (((↑(c k) : ℤ) - (↑(c (m + i)) : ℤ)) * (-1:ℤ)) := by
        group
      have h₆: ∏ i ∈ Finset.Icc 1 n, ((↑(c k) : ℤ) - (↑(c (m + i)) : ℤ)) = (∏ i ∈ Finset.Icc 1 n, (k - (m + i))) * (∏ i ∈ Finset.Icc 1 n, (k + (m + i) + 1)) := by
        have h₅₁: ∏ i ∈ Finset.Icc 1 n, (((c k):ℤ) - ((c (m + i)):ℤ)) = (↑(∏ i ∈ Finset.Icc 1 n, (c k - c (m + i))):ℤ) := by
          rw [@Nat.cast_prod]
          refine Finset.prod_congr rfl ?_
          simp only [Finset.mem_Icc, and_imp]
          intro x hx₀ hx₁
          symm
          refine Nat.cast_sub ?_
          -- from x ≤ n and m + n < k, we get m + x ≤ k
          have hmx_le_k : m + x ≤ k := by
            have hx' : m + x ≤ m + n := Nat.add_le_add_left hx₁ m
            exact le_of_lt (lt_of_le_of_lt hx' hk₁)
          exact aux_1_mono c h₁ hmx_le_k
        rw [h₅₁, ← Nat.cast_mul]
        norm_cast
        simp_rw [aux_1 c h₁]
        exact Finset.prod_mul_distrib
      rw [h₅, Finset.prod_mul_distrib, h₆]
      have h₇: (↑n.factorial : ℤ) * (↑(n + 1).factorial : ℤ) ∣
        (↑(∏ i ∈ Finset.Icc 1 n, (k - (m + i))) : ℤ) * (↑(∏ i ∈ Finset.Icc 1 n, (k + (m + i) + 1)) : ℤ) := by
        rw [← Nat.cast_mul, ← Nat.cast_mul]
        refine Nat.cast_dvd_cast ?_
        refine Nat.mul_dvd_mul ?_ ?_
        · have h₇₀: n ≤ k - (m + 1) := by lia
          rw [aux_4 k m n h₇₀]
          exact Nat.factorial_dvd_descFactorial (k - (m + 1)) n
        · have h₇₀: ∏ i ∈ Finset.Icc 1 n, (k + (m + i) + 1) = ∏ i ∈ Finset.Icc 1 n, (m + i + k + 1) := by group
          rw [h₇₀]
          exact aux_3 k m n h₀ h₂ h₃
      exact Dvd.dvd.mul_right h₇ (∏ x ∈ Finset.Icc 1 n, -1)
