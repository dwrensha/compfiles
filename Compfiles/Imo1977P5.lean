/-
Copyright (c) 2025 Roozbeh Yousefzadeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roozbeh Yousefzadeh
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file {
  tags := [.NumberTheory]
  importedFrom := "https://github.com/roozbeh-yz/IMO-Steps/blob/main/Lean_v20/imo_proofs/imo_1977_p5.lean"
}

/-!
# International Mathematical Olympiad 1977, Problem 5

Let $a,b$ be two natural numbers. When we divide $a^2+b^2$ by $a+b$, we get the remainder $r$ and the quotient $q$. Determine all pairs $(a, b)$ for which $q^2 + r = 1977$.

-/

namespace Imo1977P5

determine solution_set : Set (ℕ×ℕ) := {(7,50), (37, 50), (50, 7), (50, 37)}


snip begin

lemma aux_1
  (a b : ℕ)
  (h₀ : Prime (1009:ℤ))
  (h₁ : ((↑b : ℤ) - 22) ^ 2 = 1009 - ((↑a : ℤ) - 22) ^ 2)
  (ha₀ : a ≤ 53) :
  (a, b) ∈ solution_set := by
  let s : ℤ := 1009 - (↑(a:ℤ) - 22) ^ 2
  have hs: s = 1009 - (↑(a:ℤ) - 22) ^ 2 := by rfl
  have h₈₀: IsSquare (((a:ℤ) - 22) ^ 2) := by exact IsSquare.sq ((a:ℤ) - 22)
  have h₈₁: IsSquare (((b:ℤ) - 22) ^ 2) := by exact IsSquare.sq ((b:ℤ) - 22)
  have h₈₂: IsSquare s := by
    rw [hs, ← h₁]
    exact h₈₁
  have ha₁: ∀ k n:ℤ, n^2 < k ∧ k < (n + 1) ^ 2 → ¬ IsSquare k := by
    intros k n hk₀
    cases' hk₀ with hk₀ hk₁
    by_contra hc₂
    apply (isSquare_iff_exists_sq k).mp at hc₂
    let ⟨d, hd₀⟩ := hc₂
    rw [hd₀] at hk₀ hk₁
    apply sq_lt_sq.mp at hk₀
    apply sq_lt_sq.mp at hk₁
    by_cases hn: 0 ≤ n
    . rw [abs_of_nonneg hn] at hk₀
      nth_rw 2 [abs_of_nonneg (by linarith)] at hk₁
      linarith
    . push_neg at hn
      have hn₁: n + 1 ≤ 0 := by linarith
      rw [abs_of_neg hn] at hk₀
      rw [abs_of_nonpos hn₁] at hk₁
      linarith
  have ha₂: ∀ k:ℤ, 31^2 < k ∧ k < 32 ^ 2 → ¬ IsSquare k := by exact fun k a => ha₁ k 31 a
  have ha₃: ∀ k:ℤ, 30^2 < k ∧ k < 31 ^ 2 → ¬ IsSquare k := by exact fun k a => ha₁ k 30 a
  have ha₄: ∀ k:ℤ, 29^2 < k ∧ k < 30 ^ 2 → ¬ IsSquare k := by exact fun k a => ha₁ k 29 a
  have ha₅: ∀ k:ℤ, 28^2 < k ∧ k < 29 ^ 2 → ¬ IsSquare k := by exact fun k a => ha₁ k 28 a
  have ha₆: ∀ k:ℤ, 27^2 < k ∧ k < 28 ^ 2 → ¬ IsSquare k := by exact fun k a => ha₁ k 27 a
  have ha₇: ∀ k:ℤ, 26^2 < k ∧ k < 27 ^ 2 → ¬ IsSquare k := by exact fun k a => ha₁ k 26 a
  have ha₈: ∀ k:ℤ, 25^2 < k ∧ k < 26 ^ 2 → ¬ IsSquare k := by exact fun k a => ha₁ k 25 a
  have ha₉: ∀ k:ℤ, 24^2 < k ∧ k < 25 ^ 2 → ¬ IsSquare k := by exact fun k a => ha₁ k 24 a
  have ha₁₀: ∀ k:ℤ, 23^2 < k ∧ k < 24 ^ 2 → ¬ IsSquare k := by exact fun k a => ha₁ k 23 a
  have ha₁₁: abs ((↑a : ℤ) - (22 : ℤ)) ≤ 31 := by
    refine abs_le.mpr ?_
    omega
  rw [← sq_abs ((↑a : ℤ) - (22 : ℤ))] at h₁ hs h₈₀
  have ha₁₂: 0 ≤ abs ((↑a : ℤ) - (22 : ℤ)) := by exact abs_nonneg ((↑a : ℤ) - (22 : ℤ))
  by_cases ha₁₃: abs ((↑a : ℤ) - (22 : ℤ)) < 15
  . exfalso
    interval_cases abs ((↑a : ℤ) - (22 : ℤ))
    . have hh₀: IsSquare (1009:ℤ) := by
        rw [zero_pow (by norm_num), sub_zero] at h₁
        rw [← h₁]
        exact h₈₁
      have hh₁: ¬ IsSquare (1009:ℤ) := by exact Prime.not_isSquare h₀
      exact hh₁ hh₀
    all_goals try exact (ha₂ s (by omega)) h₈₂
    all_goals try exact (ha₃ s (by omega)) h₈₂
    . exact (ha₄ s (by omega)) h₈₂
    . exact (ha₄ s (by omega)) h₈₂
    . exact (ha₅ s (by omega)) h₈₂
    . exact (ha₅ s (by omega)) h₈₂
  . push_neg at ha₁₃
    by_cases ha₁₄: abs ((↑a : ℤ) - (22 : ℤ)) = 15
    . apply (abs_eq (by norm_num)).mp at ha₁₄
      cases' ha₁₄ with ha₁₄ ha₁₄
      . right; left
        have hh₀: a = 37 := by bound
        rw [hh₀] at h₁
        simp at h₁
        have hh₁: (784:ℤ) = 28 ^ 2 := by bound
        rw [hh₁] at h₁
        apply pow_eq_pow_iff_cases.mp at h₁
        simp at h₁
        bound
      . left
        have hh₀: a = 7 := by bound
        rw [hh₀] at h₁
        simp at h₁
        have hh₁: (784:ℤ) = 28 ^ 2 := by bound
        rw [hh₁] at h₁
        apply pow_eq_pow_iff_cases.mp at h₁
        simp at h₁
        rw [hh₀]
        rw [@Prod.mk_right_inj]
        omega
    . by_cases ha₁₅: abs ((↑a : ℤ) - (22 : ℤ)) < 28
      . exfalso
        interval_cases abs ((↑a : ℤ) - (22 : ℤ))
        . exact (ha₅ s (by omega)) h₈₂
        . exact (ha₆ s (by omega)) h₈₂
        . exact (ha₇ s (by omega)) h₈₂
        . exact (ha₇ s (by omega)) h₈₂
        . exact (ha₈ s (by omega)) h₈₂
        . exact (ha₉ s (by omega)) h₈₂
        . exact (ha₁₀ s (by omega)) h₈₂
        . exact (ha₁ s 22 (by omega)) h₈₂
        . exact (ha₁ s 21 (by omega)) h₈₂
        . exact (ha₁ s 20 (by omega)) h₈₂
        . exact (ha₁ s 19 (by omega)) h₈₂
        . exact (ha₁ s 18 (by omega)) h₈₂
        . exact (ha₁ s 16 (by omega)) h₈₂
      . by_cases ha₁₆: abs ((↑a : ℤ) - (22 : ℤ)) = 28
        . right; right
          have ha₁₇: a = 50 := by
            apply (abs_eq (by norm_num)).mp at ha₁₆
            omega
          rw [ha₁₇]
          rw [ha₁₇] at h₁
          simp at h₁
          have hh₀: (225:ℤ) = 15 ^ 2 := by bound
          rw [hh₀] at h₁
          apply pow_eq_pow_iff_cases.mp at h₁
          simp at h₁
          cases' h₁ with h₁ h₁
          . simp
            right
            omega
          . simp
            left
            omega
        . exfalso
          interval_cases abs ((↑a : ℤ) - (22 : ℤ))
          . exact (ha₁ s 14 (by omega)) h₈₂
          . exact (ha₁ s 12 (by omega)) h₈₂
          . exact (ha₁ s 10 (by omega)) h₈₂
          . exact (ha₁ s 6 (by omega)) h₈₂

lemma aux_2
  (a b q r : ℕ)
  (hp: 0 < a ∧ 0 < b)
  (h₀ : r = (a ^ 2 + b ^ 2) % (a + b))
  (h₁ : q = (a ^ 2 + b ^ 2) / (a + b)) :
  q ^ 2 + r = 1977 → (a, b) ∈ solution_set := by
  intro h₂
  have hr₀: r = 1977 - q ^ 2 := by exact Nat.eq_sub_of_add_eq' h₂
  have h₅₁: 0 < a + b := by linarith
  have h₅₂: a ^ 2 + b ^ 2 = q * (a + b) + r := by
    rw [h₀, h₁,]
    exact Eq.symm (Nat.div_add_mod' (a ^ 2 + b ^ 2) (a + b))
  have h₅₃: q ≤ 44 := by
    by_contra hc₀
    push_neg at hc₀
    apply Nat.succ_le_iff.mpr at hc₀
    have hc₁: 45 ^ 2 ≤ q ^ 2 := by exact Nat.pow_le_pow_left hc₀ 2
    linarith
  have h₅₄: 43 < q := by
    have g₀: (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by exact add_sq_le
    have g₁: 2 * (a ^ 2 + b ^ 2) < 2 * (45 * (a + b)) := by
      refine (Nat.mul_lt_mul_left zero_lt_two).mpr ?_
      have g₁₀: 45 = 44 + 1 := by linarith
      rw [h₅₂, g₁₀, add_mul, one_mul]
      refine add_lt_add_of_le_of_lt ?_ ?_
      . exact Nat.mul_le_mul_right (a + b) h₅₃
      . rw [h₀]
        exact Nat.mod_lt (a ^ 2 + b ^ 2) h₅₁
    have g₂: a + b < 90 := by
      apply lt_of_le_of_lt g₀ at g₁
      rw [pow_two] at g₁
      rw [← mul_assoc] at g₁
      simp at g₁
      exact (Nat.mul_lt_mul_right h₅₁).mp g₁
    have g₃: r < 90 := by
      rw [h₀]
      refine lt_trans ?_ g₂
      exact Nat.mod_lt (a ^ 2 + b ^ 2) h₅₁
    by_contra hc₀
    push_neg at hc₀
    have hc₁: q ^ 2 ≤ 43 ^ 2 := by exact Nat.pow_le_pow_left hc₀ 2
    omega
  have hq₀: q = 44 := by omega
  rw [hq₀] at hr₀
  norm_num at hr₀
  rw [hq₀, hr₀] at h₅₂
  have h₆: ((a:ℤ) - 22) ^ 2 + ((b:ℤ) - 22) ^ 2 = 1009 := by
    ring_nf
    linarith
  have h₇: Prime (1009:ℤ) := by bound
  apply eq_sub_of_add_eq' at h₆
  by_cases ha₀: 53 < a
  . exfalso
    apply Nat.succ_le_iff.mpr at ha₀
    simp at ha₀
    have ha₁: 32 ^ 2 ≤ ((a:ℤ) - 22) ^ 2 := by
      refine pow_le_pow_left₀ (by omega) (by omega) 2
    have hb₁: 0 ≤ ((b:ℤ) - 22) ^ 2 := by positivity
    omega
  . push_neg at ha₀
    exact aux_1 a b h₇ h₆ ha₀

snip end

problem imo1977_p5
  (a b q r : ℕ)
  (hp: 0 < a ∧ 0 < b)
  (h₀ : r = (a ^ 2 + b ^ 2) % (a + b))
  (h₁ : q = (a ^ 2 + b ^ 2) / (a + b)) :
  q ^ 2 + r = 1977 ↔ (a, b) ∈ solution_set := by
  constructor
  . exact fun (a_1 : q ^ 2 + r = 1977) ↦ aux_2 a b q r hp h₀ h₁ a_1
  . simp
    intro h₂
    bound
