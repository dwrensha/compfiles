/-
Copyright (c) 2025 Roozbeh Yousefzadeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roozbeh Yousefzadeh
-/

import Mathlib

import ProblemExtraction


problem_file {
  tags := [.NumberTheory]
  importedFrom := "https://github.com/roozbeh-yz/IMO-Steps/blob/main/Lean_v20/imo_proofs/imo_1967_p3.lean"
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

lemma aux_2 :
  ∀ (n m : ℕ), 0 < n → n.factorial ∣ ∏ i ∈ Finset.Icc 1 n, (m + i) := by
  intro s t hs₀
  have h₆₀ : ∏ i ∈ Finset.Icc (1 : ℕ) s, (t + i) = (t + s).factorial / t.factorial := by
    refine Nat.eq_div_of_mul_eq_right ?_ ?_
    · positivity
    · refine Nat.le_induction ?_ ?_ s hs₀
      · simp
        rw [Nat.mul_comm]
        exact rfl
      · simp only [Nat.succ_eq_add_one, zero_add]
        intro d hd₀ hd₁
        rw [Finset.prod_Icc_succ_top (by omega), ← mul_assoc, hd₁]
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
  exact Dvd.intro ((t + s).choose t) h₆₁.symm

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
  refine (Nat.coprime_factorial_iff ?_).mpr ?_
  · exact Nat.Prime.ne_one h₁
  · rw [Nat.Prime.minFac_eq h₁]
    exact h₂

lemma aux_4
    (k m n : ℕ)
    (h₀ : 0 < k ∧ 0 < m ∧ 0 < n)
    (hk₀ : m < k)
    (hk₁ : m + n < k)
    (h₇₀ : n ≤ k - (m + 1)) :
    ∏ i ∈ Finset.Icc 1 n, (k - (m + i)) = (k - (m + 1)).factorial / (k - (m + 1) - n).factorial := by
  have h_prod : ∏ i ∈ Finset.Icc 1 n, (k - (m + i)) = Nat.descFactorial (k - (m + 1)) n := by
    rw [Nat.descFactorial_eq_prod_range, ←Finset.Ico_succ_right_eq_Icc,
        Finset.prod_Ico_eq_prod_range]
    simp [add_comm, add_left_comm, tsub_tsub]
  rw [h_prod, Nat.descFactorial_eq_factorial_mul_choose]
  refine (Nat.div_eq_of_eq_mul_left (Nat.factorial_pos _) ?_).symm
  have := Nat.choose_mul_factorial_mul_factorial h₇₀
  grind

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
      rw [Finset.prod_Icc_succ_top (by omega), hd₁]
      rw [Nat.factorial_succ (d + (1 : ℕ))]
      rw [← mul_assoc, mul_comm _ (d + (1 : ℕ)), ← mul_assoc]
      rw [← Nat.factorial_succ]
      ring_nf
  rw [h₄]
  by_cases hk₀: k ≤ m
  · have h₅: (∏ i ∈ Finset.Icc 1 n, (((c (m + i)):ℤ) - ((c k):ℤ))) = (∏ i ∈ Finset.Icc 1 n, (m + i + k + 1)) * (∏ i ∈ Finset.Icc 1 n, (m + i - k)) := by
      have h₅₀: ∀ a b, c a - c b = (a - b) * (a + b + 1) := by
        exact fun a b ↦ aux_1 c h₁ a b
      have h₅₁: ∏ i ∈ Finset.Icc 1 n, (((c (m + i)):ℤ) - ((c k):ℤ)) = (↑(∏ i ∈ Finset.Icc 1 n, ((c (m + i)) - (c k))):ℤ) := by
        rw [@Nat.cast_prod]
        refine Finset.prod_congr rfl ?_
        intro x hx₀
        symm
        refine Nat.cast_sub ?_

        -- grind used to work here
        have hk_le_mx : k ≤ m + x := hk₀.trans (Nat.le_add_right _ _)
        have hprod_le : k * (k + 1) ≤ (m + x) * (m + x + 1) := by
          have h1 : k * (k + 1) ≤ (m + x) * (k + 1) :=
            Nat.mul_le_mul_right _ hk_le_mx
          have h2 : (m + x) * (k + 1) ≤ (m + x) * (m + x + 1) :=
            Nat.mul_le_mul_left _ (Nat.succ_le_succ hk_le_mx)
          exact h1.trans h2

        simpa [h₁] using hprod_le
      rw [h₅₁, ← Nat.cast_mul]
      norm_cast
      simp_rw [h₅₀]
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
          omega
        · grind
      rw [h₆]
      exact Int.dvd_zero ((↑n.factorial : ℤ) * (↑(n + (1 : ℕ)).factorial : ℤ))
    · push_neg at hk₁
      have h₅: ∏ i ∈ Finset.Icc (1 : ℕ) n, ((↑(c (m + i)) : ℤ) - (↑(c k) : ℤ)) =
        ∏ i ∈ Finset.Icc (1 : ℕ) n, (((↑(c k) : ℤ) - (↑(c (m + i)) : ℤ)) * (-1:ℤ)) := by
        group
      have h₆: ∏ i ∈ Finset.Icc 1 n, ((↑(c k) : ℤ) - (↑(c (m + i)) : ℤ)) = (∏ i ∈ Finset.Icc 1 n, (k - (m + i))) * (∏ i ∈ Finset.Icc 1 n, (k + (m + i) + 1)) := by
        have h₅₀: ∀ a b, c a - c b = (a - b) * (a + b + 1) := by
          exact fun a b ↦ aux_1 c h₁ a b
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

          -- multiply the two sides by (m + x + 1) and then by k to compare products
          have hprod_le : (m + x) * (m + x + 1) ≤ k * (k + 1) := by
           have h1 : (m + x) * (m + x + 1) ≤ k * (m + x + 1) :=
            Nat.mul_le_mul_right _ hmx_le_k
           have h2 : k * (m + x + 1) ≤ k * (k + 1) :=
             Nat.mul_le_mul_left _ (Nat.succ_le_succ hmx_le_k)
           exact h1.trans h2

          -- rewrite c s = s * (s + 1)
          simpa [h₁] using hprod_le
        rw [h₅₁, ← Nat.cast_mul]
        norm_cast
        simp_rw [h₅₀]
        exact Finset.prod_mul_distrib
      rw [h₅, Finset.prod_mul_distrib, h₆]
      have h₇: (↑n.factorial : ℤ) * (↑(n + 1).factorial : ℤ) ∣
        (↑(∏ i ∈ Finset.Icc 1 n, (k - (m + i))) : ℤ) * (↑(∏ i ∈ Finset.Icc 1 n, (k + (m + i) + 1)) : ℤ) := by
        rw [← Nat.cast_mul, ← Nat.cast_mul]
        refine Nat.cast_dvd_cast ?_
        refine Nat.mul_dvd_mul ?_ ?_
        · have h₇₀: n ≤ k - (m + 1) := by omega
          have h₇₁: ∏ i ∈ Finset.Icc 1 n, (k - (m + i)) = (k - (m + 1)).factorial / (k - (m + 1) - n).factorial := aux_4 k m n h₀ hk₀ hk₁ h₇₀
          have h₇₂: n.factorial * (k - (m + 1) - n).factorial ∣ (k - (m + 1)).factorial := by exact Nat.factorial_mul_factorial_dvd_factorial h₇₀
          have h₇₃: ∏ i ∈ Finset.Icc 1 n, (k - (m + i)) = n.factorial * Nat.choose (k - (m + 1)) n := by
            rw [Nat.choose_eq_factorial_div_factorial h₇₀, h₇₁]
            rw [← Nat.mul_div_assoc _ h₇₂]
            symm
            refine Nat.mul_div_mul_left _ _ ?_
            exact Nat.factorial_pos n
          exact Dvd.intro _ h₇₃.symm
        · have h₇₀: ∏ i ∈ Finset.Icc 1 n, (k + (m + i) + 1) = ∏ i ∈ Finset.Icc 1 n, (m + i + k + 1) := by group
          rw [h₇₀]
          exact aux_3 k m n h₀ h₂ h₃
      exact Dvd.dvd.mul_right h₇ (∏ x ∈ Finset.Icc 1 n, -1)
