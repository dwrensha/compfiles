/-
Copyright (c) 2023 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roozbeh Yousefzadeh
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file {
  tags := [.NumberTheory]
  importedFrom :=
    "https://github.com/roozbeh-yz/IMO-Steps/blob/main/imo_proofs/imo_1997_p5.lean"
}

/-!
# International Mathematical Olympiad 1997, Problem 5

Determine all pairs of integers 1 ≤ a,b that satisfy a ^ (b ^ 2) = b ^ a.
-/

namespace Imo1997P5

snip begin

lemma mylemma_xy_le_y
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  (hxy : x ≤ y)
  (h₁ : (x ^ y) ^ y = y ^ x) :
  x ^ y ≤ y := by
  by_contra hc
  push_neg at hc
  have h₂: y^x ≤ y^y := Nat.pow_le_pow_right h₀.2 hxy
  have h₃: y^y < (x^y)^y := by
    refine Nat.pow_lt_pow_left hc ?_
    refine Nat.pos_iff_ne_zero.mp h₀.2
  rw [h₁] at h₃
  linarith [h₂, h₃]

lemma four_times_k_less_than_two_pow_k
  (k : ℕ)
  (hk : 5 ≤ k) :
  4 * k < 2 ^ k := by
  -- Proceed by induction on k
  induction' k using Nat.case_strong_induction_on with n ih
  -- Base case: k = 0 is not possible since 5 ≤ k
  -- so we start directly with k = 5 as the base case
  . norm_num
  by_cases h₀ : n < 5
  . have hn: n = 4 := by omega
    rw [hn]
    norm_num
  . push_neg at h₀
    have ih₁ : 4 * n < 2 ^ n := ih n (le_refl n) h₀
    rw [mul_add, pow_add, mul_one, pow_one, mul_two]
    refine Nat.add_lt_add ih₁ ?_
    refine lt_trans ?_ ih₁
    refine (Nat.lt_mul_iff_one_lt_right (by norm_num)).mpr ?_
    refine Nat.lt_of_lt_of_le ?_ h₀
    norm_num


lemma mylemma_case_xley
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : x^(y^2) = y^x)
  (g₁ : x^(y^2) = (x^y)^y)
  (hxy : x ≤ y) :
  (x, y) = (1, 1) ∨ (x, y) = (16, 2) ∨ (x, y) = (27, 3) := by
  rw [g₁] at h₁
  have g2: x^y ≤ y := by
    exact mylemma_xy_le_y x y h₀ hxy h₁
  have g3: x = 1 := by
    by_contra hc
    have g3: 2 ≤ x := by omega
    have g4: 2^y ≤ x^y := Nat.pow_le_pow_left g3 y
    have g5: y < 2^y := Nat.lt_two_pow_self
    omega
  rw [g3] at h₁
  simp at h₁
  left
  norm_num
  exact { left := g3, right := id h₁.symm }

lemma mylemma_exp_log
  (x: ℕ)
  (h₀: 0 < x):
  (↑x = Real.exp (Real.log ↑x)):= by
  have hx_pos : 0 < (↑x : ℝ) := by exact Nat.cast_pos.mpr h₀
  symm
  exact Real.exp_log hx_pos

lemma mylemma_y2_lt_x
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : x ^ y ^ 2 = y ^ x)
  (hxy : y < x) :
  y ^ 2 < x := by
  by_cases hy: 1 < y
  . have hx: 2 ≤ x := by omega
    have h₂: y ^ x < x ^ x := by
      refine Nat.pow_lt_pow_left hxy ?_
      exact Nat.ne_of_lt' h₀.1
    rw [← h₁] at h₂
    exact (Nat.pow_lt_pow_iff_right hx).mp h₂
  . push_neg at hy
    interval_cases y
    . simp
      exact h₀.1
    . simp at *
      assumption


lemma mylemma_5
  (x y: ℕ)
  (h₀: 0 < x ∧ 0 < y)
  (h₁: x ^ y ^ 2 = y ^ x) :
  (↑x / ↑y^2) ^ y ^ 2 = (↑y:ℝ)^ ((↑x:ℝ) - 2 * ↑y ^ 2) := by
  have g₁: (↑x:ℝ) ^ (↑y:ℝ) ^ 2 = (↑y:ℝ) ^ (↑x:ℝ) := by
    norm_cast
  have g₃: ((↑x:ℝ) ^ (↑y:ℝ) ^ 2) / ((↑y:ℝ) ^ (2 * (↑y:ℝ) ^ 2))
        = ((↑y:ℝ) ^ (↑x:ℝ)) / ((↑y:ℝ) ^ (2 * (↑y:ℝ) ^ 2)) := by
    refine (div_left_inj' ?_).mpr g₁
    norm_cast
    refine pow_ne_zero _ ?_
    linarith [h₀.2]
  have gy: 0 < (↑y:ℝ) := by
    norm_cast
    exact h₀.2
  rw [← Real.rpow_sub gy (↑x) (2 * ↑y ^ 2)] at g₃
  have g₄: ((↑x:ℝ) ^ (↑y:ℝ) ^ 2) / ((↑y:ℝ) ^ (2 * (↑y:ℝ) ^ 2))
        = (↑x / ↑y^2) ^ y ^ 2 := by
    have g₅: (↑y:ℝ) ^ (2 * (↑y:ℝ) ^ 2) = ((↑y:ℝ) ^ 2) ^ ((↑y:ℝ) ^ 2) := by
      norm_cast
      refine pow_mul y 2 (y^2)
    rw [g₅]
    symm
    norm_cast
    have g₆: ((↑x:ℝ) / ↑y ^ 2) ^ y ^ 2 = ↑x ^ y ^ 2 / (↑y ^ 2) ^ y ^ 2 := by
      refine div_pow (↑x:ℝ) ((↑y:ℝ) ^ 2) (y^2)
    norm_cast at *
  rw [g₄] at g₃
  norm_cast at *

lemma mylemma_2y2_lt_x
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : x ^ y ^ 2 = y ^ x)
  (hxy : y < x) :
  2 * y ^ 2 < x := by
  by_cases hy1: y = 1
  . rw [hy1]
    norm_num
    by_contra hc
    push_neg at hc
    interval_cases x
    . omega
    . omega
    . rw [hy1] at h₁
      simp at h₁
  . have hy: 1 < y := by omega
    clear hy1
    have h₂: (↑y:ℝ) ^ 2 < ↑x := by
      norm_cast
      exact mylemma_y2_lt_x x y h₀ h₁ hxy
    have h₃: 1 < ↑x / (↑y:ℝ) ^ 2 := by
      refine (one_lt_div ?_).mpr h₂
      norm_cast
      exact pow_pos h₀.2 2  -- rw ← one_mul ((↑y:ℝ)^2) at h₂, refine lt_div_iff_mul_lt.mpr h₂, },
    have h₄: 1 < (↑x / (↑y:ℝ)^2)^(y^2) := by
      refine one_lt_pow₀ h₃ ?_
      refine Nat.ne_of_gt ?_
      refine sq_pos_of_pos ?_
      exact Nat.lt_of_succ_lt hy
    have h₅: (↑x/ (↑y:ℝ)^2)^(y^2) = (↑y:ℝ)^((↑x:ℝ) - 2*(↑y:ℝ)^2) := by
      exact mylemma_5 x y h₀ h₁
    rw [h₅] at h₄
    have h₆: 0 < (↑x:ℝ) - 2 * (↑y:ℝ) ^ 2 := by
      by_contra hc
      push_neg at hc
      cases' lt_or_eq_of_le hc with hlt heq
      . have gy: 1 < (↑y:ℝ) := by
          norm_cast
        have glt: (↑x:ℝ) - 2*(↑y:ℝ)^2 < (↑0:ℝ) := by
          norm_cast at *
        have g₁: (↑y:ℝ) ^ ((↑x:ℝ) - 2*(↑y:ℝ)^2) < (↑y:ℝ) ^ (↑0:ℝ) := by
          exact Real.rpow_lt_rpow_of_exponent_lt gy glt
        simp at g₁
        linarith[ h₄,g₁]
      . rw [heq] at h₄
        simp at h₄
    simp at h₆
    norm_cast at h₆

lemma mylemma_castdvd
  (x y: ℕ)
  (h₀: 0 < x ∧ 0 < y)
  (h₁ : x ^ y ^ 2 = y ^ x)
  (hyx: y < x) :
  (y^2 ∣ x) := by
  have h₂: (x ^ y ^ 2).factorization = (y^x).factorization := by
    exact congr_arg Nat.factorization h₁
  simp at h₂
  symm at h₂
  have hxy1: 2 * y^2 ≤ x := by exact le_of_lt (mylemma_2y2_lt_x x y h₀ h₁ hyx)
  have hxy: 2 • y^2 ≤ x := by exact hxy1
  have h₃: 2 • y^2 • x.factorization ≤ x • x.factorization := by
    rw [← smul_assoc]
    refine nsmul_le_nsmul_left ?_ hxy
    norm_num
  rw [← h₂] at h₃
  have h₄: 2 • x • y.factorization = x • (2 • y.factorization) :=
    nsmul_left_comm y.factorization x 2
  rw [h₄] at h₃
  rw [← Nat.factorization_pow] at h₃
  rw [← Nat.factorization_pow] at h₃
  rw [← Nat.factorization_pow] at h₃
  have h₅: (y ^ 2) ^ x ∣ x^x := by
    have g₁: (y ^ 2) ^ x ≠ 0 := by
      refine pow_ne_zero x ?_
      refine pow_ne_zero 2 ?_
      omega
    have g₂: x ^ x ≠ 0 := by
      refine pow_ne_zero x ?_
      omega
    exact (Nat.factorization_le_iff_dvd g₁ g₂).mp h₃
  refine (Nat.pow_dvd_pow_iff ?_).mp h₅
  exact Nat.ne_of_gt h₀.1

lemma mylemma_xsuby_eq_2xy2_help
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : x ^ y ^ 2 = y ^ x)
  (h₂ : Real.log (↑x:ℝ)  = Real.log ↑y * ↑x / (↑(y ^ 2:ℕ ):ℝ) )
  (hxy : y < x) :
  x = y ^ (x / y ^ 2) := by
  have h_exp : Real.exp (Real.log ↑x)
            = Real.exp (Real.log ↑y * (↑x:ℝ)  / ((↑y:ℝ)) ^ 2) := by
    rw [h₂]
    norm_cast
  rw [← mylemma_exp_log x h₀.1] at h_exp
  rw [← mul_div] at h_exp
  rw [Real.exp_mul] at h_exp
  rw [← mylemma_exp_log y h₀.2] at h_exp
  have h₃: (↑x:ℝ) / ((↑y:ℝ)^2) = (↑(x / y^2:ℕ):ℝ) := by
    norm_cast
    symm
    have g₂: y^2 ∣ x := by
      exact mylemma_castdvd x y h₀ h₁ hxy
    exact Nat.cast_div_charZero g₂
  have h₄ : (↑(y ^ (x / y ^ (2:ℕ))):ℝ) = (↑y:ℝ)^((↑x:ℝ) / ((↑y:ℝ)^2)) := by
    rw [Nat.cast_pow, h₃]
    norm_cast
  rw [←h₄] at h_exp
  exact Nat.cast_inj.mp h_exp

theorem mylemma_xsuby_eq_2xy2
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : x ^ y ^ 2 = y ^ x)
  (hxy : y < x) :
  x = y ^ (x / y ^ 2) := by
  -- sketch: y^2 * log x = x * log y
  have h₃: Real.log (x^(y^2)) = Real.log (y^x) := by
    norm_cast
    rw [h₁]
  have h₄: (↑(y ^ (2:ℕ)):ℝ)  * Real.log x = ↑x * Real.log y := by
    have h41: Real.log (y^x) = (↑x:ℝ) * Real.log (y) := by
      exact Real.log_pow y x
    have h42: Real.log (x^(y^2)) = (↑(y ^ (2:ℕ)):ℝ) * Real.log x := by
      exact Real.log_pow x (y^2)
    rw [h41,h42] at h₃
    exact h₃
  ring_nf at h₄
  have h₅: Real.log ↑x = Real.log ↑y * ↑x / (↑(y ^ (2:ℕ)):ℝ) := by
    by_contra hc
    rw [mul_comm (Real.log ↑y) (↑x)] at hc
    rw [← h₄, mul_comm, ← mul_div] at hc
    rw [div_self, mul_one] at hc
    . apply hc
      norm_cast
    . norm_cast
      push_neg
      refine pow_ne_zero 2 ?_
      exact Nat.ne_of_gt h₀.2
  exact mylemma_xsuby_eq_2xy2_help x y h₀ h₁ h₅ hxy

snip end

determine solution_set : Set (ℕ × ℕ) := {(1, 1), (16, 2), (27, 3)}

problem imo1997_p5 (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ⟨a,b⟩ ∈ solution_set ↔ a ^ (b ^ 2) = b ^ a := by
  constructor
  · aesop
  intro h₁
  simp only [solution_set, Set.mem_insert_iff, Set.mem_singleton_iff]
  have g₁: a^(b^2) = (a^b)^b := by
    rw [Nat.pow_two]
    exact Nat.pow_mul a b b
  by_cases hxy: a ≤ b
  . exact mylemma_case_xley a b ⟨ha, hb⟩ h₁ g₁ hxy
  . push_neg at hxy
    right
    have h₃: a = b ^ (a / b ^ 2) := mylemma_xsuby_eq_2xy2 a b ⟨ha, hb⟩ h₁ hxy
    let k:ℕ  := a / b^2
    have hk_def: k = a / b^2 := rfl
    by_cases hk: k < 2
    . rw [← hk_def] at h₃
      interval_cases k
      . exfalso
        simp at h₃
        omega
      . exfalso
        simp at *
        omega
    . push_neg at hk
      rw [← hk_def] at h₃
      have h₅: k = b^(k-2) := by
        rw [h₃] at hk_def
        nth_rewrite 1 [hk_def]
        exact Nat.pow_div hk hb
      by_cases hk5: k < 5
      . interval_cases k
        . exfalso
          simp at h₅
        . right
          norm_num
          simp at h₅
          symm at h₅
          rw [h₅] at h₃
          norm_num at h₃
          exact { left := h₃, right := h₅ }
        . simp at h₅
          symm at h₅
          have g₂: b^4 = b^2 * b^2 := by ring_nf
          rw [g₂, h₅] at h₃
          norm_num at h₃
          left
          norm_num
          constructor
          . exact h₃
          . have h₆ : b ^ 2 = 2 ^ 2 := by
              norm_num
              exact h₅
            have h₇: 0 ≤ b := by omega
            exact (sq_eq_sq₀ h₇ (by omega)).mp (h₆)
      push_neg at hk5
      by_cases hy: 2 ≤ b
      . have h₅₁: k < b^(k-2) := by
          have h₆: 2^(k-2) ≤ b^(k-2) := Nat.pow_le_pow_left hy (k - 2)
          have h₇: 4*k < 2^k := by
            exact four_times_k_less_than_two_pow_k k hk5
          have h₇: k < 2^(k-2) := by
            have h₈ : k < 2 ^ k / 4 := by
              have h81: 4 ∣ 2^k := by
                have h82: 2^k = 4*2^(k-2) := by
                  nth_rewrite 1 [←Nat.add_sub_of_le hk]
                  rw [pow_add]
                  norm_num
                rw [h82]
                exact Nat.dvd_mul_right 4 (2^(k-2))
              exact (Nat.lt_div_iff_mul_lt' h81 k).mpr h₇
            have h₉: 2 ^ k / 4 = 2 ^ (k-2) := by
              have g2: k = k - 2 + 2 := by
                exact (Nat.sub_eq_iff_eq_add hk).mp rfl
              have h1: 2^k = 2^(k - 2 + 2) := by
                exact congrArg (HPow.hPow 2) g2
              have h2: 2 ^ (k - 2 + 2) = 2 ^ (k - 2) * 2 ^ 2 := by rw [pow_add]
              rw [h1, h2]
              ring_nf
              simp
            omega
          omega
        exfalso
        omega
      . push_neg at hy
        have hb : b = 1 := by omega
        simp only [hb, one_pow, pow_one] at h₁
        omega

end Imo1997P5
