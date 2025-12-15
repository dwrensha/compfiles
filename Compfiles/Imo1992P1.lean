/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roozbeh Yousefzadeh
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file {
  tags := [.NumberTheory]
  importedFrom :=
    "https://github.com/roozbeh-yz/IMO-Steps/blob/main/imo_proofs/imo_1992_p1.lean"
}

/-!
# International Mathematical Olympiad 1992, Problem 1

Find all integers 1 < a < b < c such that
(a - 1)(b - 1)(c - 1) divides abc - 1.
-/

namespace Imo1992P1

snip begin

lemma mylemma_main_lt2
    (p q r : ℤ)
    (hpl : 4 ≤ p)
    (hql : 5 ≤ q)
    (hrl : 6 ≤ r) :
  (↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)):ℚ) ≤ ↑2 := by
  have h₁: (↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)):ℚ)
    = (↑p/↑(p-1)) * (↑q/↑(q-1)) * (↑r/↑(r-1)) := by
    field_simp
    simp
  have hp: (↑p/↑(p-1):ℚ) ≤ ((4/3):ℚ) := by
    have g₁: 0 < (↑(p - 1):ℚ) := by
      norm_cast
      linarith [hpl]
    have g₂: ↑p * ↑(3:ℚ) ≤ ↑(4:ℚ) * (↑(p - 1):ℚ) := by
      norm_cast
      omega
    refine (div_le_iff₀ g₁).mpr ?_
    rw [div_mul_eq_mul_div]
    refine (le_div_iff₀ ?_).mpr g₂
    norm_num
  have hq: (↑q/↑(q-1)) ≤ ((5/4):ℚ) := by
    have g₁: 0 < (↑(q - 1):ℚ) := by
      norm_cast
      linarith[hql]
    have g₂: ↑q * ↑(4:ℚ) ≤ ↑(5:ℚ) * (↑(q - 1):ℚ) := by
      norm_cast
      linarith
    refine (div_le_iff₀ g₁).mpr ?_
    rw [div_mul_eq_mul_div]
    refine (le_div_iff₀ ?_).mpr g₂
    norm_num
  have hr: (↑r/↑(r-1)) ≤ ((6/5):ℚ) := by
    have g₁: 0 < (↑(r - 1):ℚ) := by
      norm_cast
      linarith[hql]
    have g₂: ↑r * ↑(5:ℚ) ≤ ↑(6:ℚ) * (↑(r - 1):ℚ) := by
      norm_cast
      linarith
    refine (div_le_iff₀ g₁).mpr ?_
    rw [div_mul_eq_mul_div]
    refine (le_div_iff₀ ?_).mpr g₂
    norm_num
  have hub: (↑p/↑(p-1)) * (↑q/↑(q-1)) * (↑r/↑(r-1)) ≤ (4/3:ℚ) * ((5/4):ℚ) * ((6/5):ℚ) := by
    have hq_nonneg: 0 ≤ (↑q:ℚ) := by
      norm_cast
      linarith
    have hq_1_nonneg: 0 ≤ (↑(q - 1):ℚ) := by
      norm_cast
      linarith
    have h₂: 0 ≤ (((q:ℚ) / ↑(q - 1)):ℚ) := by
      exact div_nonneg hq_nonneg hq_1_nonneg
    have hub1: (↑p/↑(p-1)) * (↑q/↑(q-1)) ≤ ((4/3):ℚ) * ((5/4):ℚ) := by
      exact mul_le_mul hp hq h₂ (by norm_num)
    have hr_nonneg: 0 ≤ (↑r:ℚ) := by
      norm_cast
      linarith
    have hr_1_nonneg: 0 ≤ (↑(r - 1):ℚ) := by
      norm_cast
      linarith
    have h₃: 0 ≤ (((r:ℚ) / ↑(r - 1)):ℚ) := by
      exact div_nonneg hr_nonneg hr_1_nonneg
    exact mul_le_mul hub1 hr h₃ (by norm_num)
  norm_num at hub
  rw [h₁]
  norm_num
  exact hub


lemma mylemma_k_lt_2
  (p q r k: ℤ)
  (hk: p * q * r - 1 = (p - 1) * (q - 1) * (r - 1) * k)
  (hpl: 4 ≤ p)
  (hql: 5 ≤ q)
  (hrl: 6 ≤ r)
  (hden: 0 < (p - 1) * (q - 1) * (r - 1) ) :
  (k < 2) := by
  have h₁: (↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)):ℚ) ≤ ↑2 := by
    exact mylemma_main_lt2 p q r hpl hql hrl
  have h₂: ↑k = (↑(p * q * r - 1):ℚ) / (↑((p - 1) * (q - 1) * (r - 1)):ℚ) := by
    have g₁: ↑(p * q * r - 1) = ↑k * (↑((p - 1) * (q - 1) * (r - 1)):ℚ) := by
      norm_cast
      linarith
    symm
    have g₂: (↑((p - 1) * (q - 1) * (r - 1)):ℚ) ≠ 0 := by
      norm_cast
      linarith[hden]
    exact (div_eq_iff g₂).mpr g₁
  have h₃: ↑k < (↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)):ℚ) := by
    rw [h₂]
    have g₁: (↑(p * q * r - 1):ℚ) < (↑(p * q * r):ℚ) := by
      norm_cast
      exact sub_one_lt (p * q * r)
    have g₂: 0 < (↑((p - 1) * (q - 1) * (r - 1)):ℚ) := by
      norm_cast
    exact div_lt_div_of_pos_right g₁ g₂
  have h₄: (↑k:ℚ) < ↑2 := by
    exact lt_of_lt_of_le h₃ h₁
  norm_cast at h₄


lemma mylemma_main_lt4
  (p q r: ℤ)
  (hpl: 2 ≤ p)
  (hql: 3 ≤ q)
  (hrl: 4 ≤ r) :
  (↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)):ℚ) ≤ ↑4 := by
  have h₁: (↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)):ℚ)
      = (↑p/↑(p-1)) * (↑q/↑(q-1)) * (↑r/↑(r-1)) := by
    field_simp
    simp
  have hp: (↑p/↑(p-1):ℚ) ≤ ↑(2:ℚ) := by
    have g₁: 0 < (↑(p - 1):ℚ) := by
      norm_cast
      linarith[hpl]
    have g₂: ↑p ≤ ↑(2:ℚ) * (↑(p - 1):ℚ) := by
      norm_cast
      linarith
    exact (div_le_iff₀ g₁).mpr g₂
  have hq: (↑q/↑(q-1)) ≤ ((3/2):ℚ) := by
    have g₁: 0 < (↑(q - 1):ℚ) := by
      norm_cast
      linarith[hql]
    have g₂: ↑q * ↑(2:ℚ) ≤ ↑(3:ℚ) * (↑(q - 1):ℚ) := by
      norm_cast
      linarith
    refine (div_le_iff₀ g₁).mpr ?_
    rw [div_mul_eq_mul_div]
    refine (le_div_iff₀ ?_).mpr g₂
    norm_num
  have hr: (↑r/↑(r-1)) ≤ ((4/3):ℚ) := by
    have g₁: 0 < (↑(r - 1):ℚ) := by
      norm_cast
      linarith[hql]
    have g₂: ↑r * ↑(3:ℚ) ≤ ↑(4:ℚ) * (↑(r - 1):ℚ) := by
      norm_cast
      linarith
    refine (div_le_iff₀ g₁).mpr ?_
    rw [div_mul_eq_mul_div]
    refine (le_div_iff₀ ?_).mpr g₂
    norm_num
  have hub: (↑p/↑(p-1)) * (↑q/↑(q-1)) * (↑r/↑(r-1)) ≤ (2:ℚ) * ((3/2):ℚ) * ((4/3):ℚ) := by
    have hq_nonneg: 0 ≤ (↑q:ℚ) := by
      norm_cast
      linarith
    have hq_1_nonneg: 0 ≤ (↑(q - 1):ℚ) := by
      norm_cast
      linarith
    have h₂: 0 ≤ (((q:ℚ) / ↑(q - 1)):ℚ) := by
      exact div_nonneg hq_nonneg hq_1_nonneg
    have hub1: (↑p/↑(p-1)) * (↑q/↑(q-1)) ≤ (2:ℚ) * ((3/2):ℚ) := by
      exact mul_le_mul hp hq h₂ (by norm_num)
    have hr_nonneg: 0 ≤ (↑r:ℚ) := by
      norm_cast
      linarith
    have hr_1_nonneg: 0 ≤ (↑(r - 1):ℚ) := by
      norm_cast
      linarith
    have h₃: 0 ≤ (((r:ℚ) / ↑(r - 1)):ℚ) := by
      exact div_nonneg hr_nonneg hr_1_nonneg
    exact mul_le_mul hub1 hr h₃ (by norm_num)
  norm_num at hub
  rw [h₁]
  norm_num
  exact hub



lemma mylemma_k_lt_4
  (p q r k: ℤ)
  (hk: p * q * r - 1 = (p - 1) * (q - 1) * (r - 1) * k)
  (hpl: 2 ≤ p)
  (hql: 3 ≤ q)
  (hrl: 4 ≤ r)
  (hden: 0 < (p - 1) * (q - 1) * (r - 1) ) :
  (k < 4) := by
  have h₁: (↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)):ℚ) ≤ ↑4 := by
    exact mylemma_main_lt4 p q r hpl hql hrl
  have h₂: ↑k = (↑(p * q * r - 1):ℚ) / (↑((p - 1) * (q - 1) * (r - 1)):ℚ) := by
    have g₁: ↑(p * q * r - 1) = ↑k * (↑((p - 1) * (q - 1) * (r - 1)):ℚ) := by
      norm_cast
      linarith
    symm
    have g₂: (↑((p - 1) * (q - 1) * (r - 1)):ℚ) ≠ 0 := by
      norm_cast
      linarith [hden]
    exact (div_eq_iff g₂).mpr g₁
  have h₃: ↑k < (↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)):ℚ) := by
    rw [h₂]
    have g₁: (↑(p * q * r - 1):ℚ) < (↑(p * q * r):ℚ) := by
      norm_cast
      exact sub_one_lt (p * q * r)
    have g₂: 0 < (↑((p - 1) * (q - 1) * (r - 1)):ℚ) := by
      norm_cast
    exact div_lt_div_of_pos_right g₁ g₂
  have h₄: (↑k:ℚ) < ↑4 := by
    exact lt_of_lt_of_le h₃ h₁
  norm_cast at h₄



lemma mylemma_k_gt_1
  (p q r k: ℤ)
  (hk: p * q * r - 1 = (p - 1) * (q - 1) * (r - 1) * k)
  (h₁: ↑k = (↑(p * q * r - 1):ℚ) / (↑((p - 1) * (q - 1) * (r - 1)):ℚ))
  (hpl: 2 ≤ p)
  (hql: 3 ≤ q)
  (hrl: 4 ≤ r)
  (hden: 0 < (p - 1) * (q - 1) * (r - 1) ) :
  (1 < k) := by
  have hk0: 0 < (↑k:ℚ) := by
    have g₁: 2*3*4 ≤ p * q * r := by
      have g₂: 2*3 ≤ p * q := by
        exact mul_le_mul hpl hql (by norm_num) (by positivity)
      exact mul_le_mul g₂ hrl (by norm_num) (by positivity)
    have g₂: 0 < (↑(p * q * r - 1):ℚ) := by
      norm_cast
      linarith[g₁]
    have g₃: 0 < (↑((p - 1) * (q - 1) * (r - 1)):ℚ) := by
      norm_cast
    rw [h₁]
    exact div_pos g₂ g₃
  norm_cast at hk0
  by_contra hc
  push_neg at hc
  interval_cases k
  simp at hk
  exfalso
  have g₂: p < p*q := by exact lt_mul_right (by omega) (by omega)
  have g₃: q < q*r := by exact lt_mul_right (by omega) (by omega)
  have g₄: r < r*p := by exact lt_mul_right (by omega) (by omega)
  linarith

lemma mylemma_p_lt_4
  (p q r k: ℤ)
  (h₀ : 1 < p ∧ p < q ∧ q < r)
  (hk: p * q * r - 1 = (p - 1) * (q - 1) * (r - 1) * k)
  (h₁: ↑k = (↑(p * q * r - 1):ℚ) / (↑((p - 1) * (q - 1) * (r - 1)):ℚ))
  (hpl: 2 ≤ p)
  (hql: 3 ≤ q)
  (hrl: 4 ≤ r)
  (hden: 0 < (p - 1) * (q - 1) * (r - 1) ) :
  (p < 4) := by
  by_contra hcp
  push_neg at hcp
  have hcq: 5 ≤ q := by omega
  have hcr: 6 ≤ r := by omega
  have h₃: k < 2 := by exact mylemma_k_lt_2 p q r k hk hcp hcq hcr hden
  have h₄: 1 < k := by exact mylemma_k_gt_1 p q r k hk h₁ hpl hql hrl hden
  omega

lemma q_r_divisor_of_prime
  (q r : ℤ)
  (p: ℕ)
  (h₀ : q * r = ↑p)
  (h₁: Nat.Prime p) :
  q = -1 ∨ q = 1 ∨ q = -p ∨ q = p := by
  have hqr : abs q * abs r = p := by
    have h₃: abs q = q.natAbs := Int.abs_eq_natAbs q
    have h₄: abs r = r.natAbs := Int.abs_eq_natAbs r
    rw [h₃,h₄]
    norm_cast
    exact Int.natAbs_mul_natAbs_eq h₀
  have h_abs: abs (↑(q.natAbs):ℤ) = 1 ∨ abs q = p := by
    obtain h_1 | h_2 := Int.natAbs_eq q
    · rw [h_1] at hqr
      have h₂: abs (↑(q.natAbs):ℤ) ∣ p := by exact Dvd.intro (abs r) hqr
      have h₃: (↑(q.natAbs):ℕ) ∣ p := by
        norm_cast at *
      have h₄: (↑(q.natAbs):ℕ) = 1 ∨ (↑(q.natAbs):ℕ) = p := by
        exact Nat.Prime.eq_one_or_self_of_dvd h₁ (↑(q.natAbs):ℕ) h₃
      obtain h₄₀ | h₄₁ := h₄
      · left
        norm_cast at *
      have h₅: abs q = q.natAbs := Int.abs_eq_natAbs q
      right
      rw [h₅]
      norm_cast at *
    · rw [h_2] at hqr
      rw [abs_neg _] at hqr
      have h₂: abs (↑(q.natAbs):ℤ) ∣ p := by exact Dvd.intro (abs r) hqr
      have h₃: (↑(q.natAbs):ℕ) ∣ p := by
        norm_cast at *
      have h₄: (↑(q.natAbs):ℕ) = 1 ∨ (↑(q.natAbs):ℕ) = p := by
        exact Nat.Prime.eq_one_or_self_of_dvd h₁ (↑(q.natAbs):ℕ) h₃
      obtain h₄₀ | h₄₁ := h₄
      · left
        norm_cast at *
      · have h₅: abs q = q.natAbs := Int.abs_eq_natAbs q
        right
        rw [h₅]
        norm_cast
  obtain hq_abs | hq_abs := h_abs
  · norm_cast at *
    omega
  · right
    right
    exact Or.symm (eq_or_eq_neg_of_abs_eq hq_abs)

lemma mylemma_qr_11
  (q r: ℤ)
  (h₀: (4 - q) * (4 - r) = 11) :
  (4 - q = -1 ∨ 4 - q = 1 ∨ 4 - q = -11 ∨ 4 - q = 11) := by
  have h₁: Nat.Prime (11) := by decide
  exact q_r_divisor_of_prime (4-q) (4-r) 11 h₀ h₁

lemma mylemma_qr_5
  (q r: ℤ)
  (h₀: (q - 3) * (r - 3) = 5) :
  (q - 3 = -1 ∨ q - 3 = 1 ∨ q - 3 = -5 ∨ q - 3 = 5) := by
  have h₁: Nat.Prime (5) := by decide
  exact q_r_divisor_of_prime (q - 3) (r - 3) 5 h₀ h₁


lemma mylemma_63qr_5
  (q r: ℤ)
  (h₀: (6 - 3*q) * (2 - r) = 5) :
  (6 - 3*q = -1 ∨ 6 - 3*q = 1 ∨ 6 - 3*q = -5 ∨ 6 - 3*q = 5) := by
  have h₁: Nat.Prime (5) := by decide
  exact q_r_divisor_of_prime (6 - 3*q) (2 - r) 5 h₀ h₁


lemma mylemma_case_k_2
  (p q r: ℤ)
  (h₀: 1 < p ∧ p < q ∧ q < r)
  (hpl: 2 ≤ p)
  (hql: 3 ≤ q)
  (hpu: p < 4)
  (hk: p * q * r - 1 = (p - 1) * (q - 1) * (r - 1) * 2) :
  (p, q, r) = (2, 4, 8) ∨ (p, q, r) = (3, 5, 15) := by
  interval_cases p
  · grind
  · right
    have g₂: (4-q)*(4-r) = 11 := by linarith
    grind [mylemma_qr_11]

lemma mylemma_case_k_3
  (p q r: ℤ)
  (h₀: 1 < p ∧ p < q ∧ q < r)
  (hpl: 2 ≤ p)
  (hql: 3 ≤ q)
  (hpu: p < 4)
  (hk: p * q * r - 1 = (p - 1) * (q - 1) * (r - 1) * 3) :
  (p, q, r) = (2, 4, 8) ∨ (p, q, r) = (3, 5, 15) := by
  interval_cases p
  -- p = 2
  · have g₂: (q-3)*(r-3) = 5 := by linarith
    grind [mylemma_qr_5]
  -- p = 3
  · grind

snip end

determine solution_set : Set (ℤ × ℤ × ℤ) := {(2, 4, 8), (3, 5, 15)}

problem imo1992_p1 (a b c : ℤ) (ha : 1 < a) (hb : a < b) (hc : b < c) :
    ⟨a, b, c⟩ ∈ solution_set ↔
    (a - 1) * (b - 1) * (c - 1) ∣ a * b * c - 1 := by
  constructor
  · aesop
  intro ⟨k, hk⟩
  simp only [solution_set, Set.mem_insert_iff, Set.mem_singleton_iff]
  have hpl: 2 ≤ a := by omega
  have hql: 3 ≤ b := by omega
  have hrl: 4 ≤ c := by omega
  have hden: 0 < (a - 1) * (b - 1) * (c - 1) := by bound
  have h₁: ↑k = (↑(a * b * c - 1):ℚ) / (↑((a - 1) * (b - 1) * (c - 1)):ℚ) := by
    have g₁: ↑(a * b * c - 1) = ↑k * (↑((a - 1) * (b - 1) * (c - 1)):ℚ) := by
      norm_cast
      linarith
    symm
    have g₂: (↑((a - 1) * (b - 1) * (c - 1)):ℚ) ≠ 0 := by
      norm_cast
      linarith[hden]
    exact (div_eq_iff g₂).mpr g₁
  have hk4: k < 4 := mylemma_k_lt_4 a b c k hk hpl hql hrl hden
  have hk1: 1 < k := mylemma_k_gt_1 a b c k hk h₁ hpl hql hrl hden
  have hpu: a < 4 := mylemma_p_lt_4 a b c k ⟨ha, hb, hc⟩ hk h₁ hpl hql hrl hden
  interval_cases k
  · exact mylemma_case_k_2 a b c ⟨ha, hb, hc⟩ hpl hql hpu hk
  · exact mylemma_case_k_3 a b c ⟨ha, hb, hc⟩ hpl hql hpu hk


end Imo1992P1
