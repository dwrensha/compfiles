/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Rydh
-/

import Mathlib.Tactic

import ProblemExtraction

set_option backward.isDefEq.respectTransparency false

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 1996, Problem 4

The positive integers a and b are such that the numbers 15a + 16b
and 16a − 15b are both squares of positive integers. What is the least
possible value that can be taken on by the smaller of these two squares?

-/

namespace Imo1996P4

determine solution : ℤ := 231361

def S := { l | ∃ a b m n : ℤ,
    0 < a ∧ 0 < b ∧ 0 < m ∧ 0 < n ∧
    15*a + 16*b = m^2 ∧
    16*a - 15*b = n^2 ∧
    l = min (m^2) (n^2) }

snip begin

lemma coprime {n : ℤ} {p : ℕ} (hp : p.Prime) (h_not_dvd : ¬(p : ℤ) ∣ n) : IsCoprime ↑p n := by
  rw [Int.isCoprime_iff_nat_coprime]
  simp only [Int.natAbs_natCast]
  apply hp.coprime_iff_not_dvd.mpr
  contrapose! h_not_dvd
  exact Int.ofNat_dvd_left.mpr h_not_dvd

lemma false_of_zero_eqMod_pos {p a : ℕ} (h₁ : 0 ≡ a [ZMOD p]) (h₂ : 0 < a) (h₃ : a < p) : False := by
  have h_p_dvd_one := Int.modEq_zero_iff_dvd.mp h₁.symm
  have : p ≤ a := Nat.le_of_dvd h₂ (Int.ofNat_dvd.mp h_p_dvd_one)
  exact Nat.not_le_of_lt h₃ this

snip end

problem imo1996P4 : solution ∈ S ∧ ∀ x ∈ S, solution ≤ x := by
  have h_pos : ∀ x ∈ S, 0 < x := by
    intro x hx
    unfold S at hx
    aesop

  have h_sol : 481^2 ∈ S := by
    unfold S
    use 14911, 481, 481, 481
    norm_num

  have h_div : ∀ x ∈ S, 481^2 ∣ x := by
    intro x hx
    unfold S at hx
    obtain ⟨a, b, m, n, ha, hb, hm, hn, h1, h2, h3, rfl⟩ := hx
    have h : 13 * 37 * (a^2 + b^2) = m^4 + n^4 := by grind

    have h_4_div_13 : 13 ∣ m^4 + n^4 := by grind
    have h_4_div_37 : 37 ∣ m^4 + n^4 := by grind

    have h_4_mod_13 : m^4 + n^4 ≡ 0 [ZMOD 13] := Int.ModEq.symm (Dvd.dvd.zero_modEq_int h_4_div_13)
    have h_4_mod_37 : m^4 + n^4 ≡ 0 [ZMOD 37] := Int.ModEq.symm (Dvd.dvd.zero_modEq_int h_4_div_37)

    have aux₁ {p : ℕ} {A B C : ℤ} (h₁ : A = B * C) (h₂ : B ≡ 0 [ZMOD p]) : A ≡ 0 [ZMOD p] := by
      have := h₂.mul_right C
      simp at this
      simp [h₁, this]

    have h_12 : m^12 + n^12 = (m^4 + n^4)*(m^8 - m^4*n^4 + n^8) := by linarith
    have h_12_mod_13 : m^12 + n^12 ≡ 0 [ZMOD 13] := aux₁ h_12 h_4_mod_13
    have h_12_mod_37 : m^12 + n^12 ≡ 0 [ZMOD 37] := aux₁ h_12 h_4_mod_37

    have h_36 : m^36 + n^36 = (m^12 + n^12)*(m^24 - m^12*n^12 + n^24) := by linarith
    have h_36_mod_37 : m^36 + n^36 ≡ 0 [ZMOD 37] := aux₁ h_36 h_12_mod_37

    /-
      Using Fermat's little theorem, show that if m^(p-1) + n^(p-1) ≡ 0 (mod p) then
      both m and n are congruent to 0 mod p.
    -/
    have aux₂ (p : ℕ) (h₁ : Nat.Prime p) (h₂ : 2 < p) (h₃ : m^(p-1) + n^(p-1) ≡ 0 [ZMOD p]) :
        m ≡ 0 [ZMOD p] ∧ n ≡ 0 [ZMOD p] := by
      have hp_pred_ne_zero : p - 1 ≠ 0 := by
        have := Nat.Prime.one_lt h₁
        grind
      by_cases h_m_zero : m ≡ 0 [ZMOD p]
      · have h_n_zero : n ≡ 0 [ZMOD p] := by
          by_contra h_n_nonzero
          rw [Int.modEq_zero_iff_dvd] at h_n_nonzero
          have h_coprime : IsCoprime ↑p n := coprime h₁ h_n_nonzero
          have h_eq_zero_m_pow: m^(p-1) ≡ 0 [ZMOD p] := by
            have : m^(p-1) ≡ 0 ^ (p-1) [ZMOD p] := Int.ModEq.pow (p-1) h_m_zero
            rw [zero_pow hp_pred_ne_zero] at this
            exact this
          have h_eq_zero_n_pow: n^(p-1) ≡ 0 [ZMOD p] := by
            have := h₃.sub h_eq_zero_m_pow
            simp_all

          have h_eq_one_n_pow := Int.ModEq.pow_card_sub_one_eq_one h₁ h_coprime.symm
          have h_zero_eq_one := h_eq_zero_n_pow.symm.trans h_eq_one_n_pow
          exact false_of_zero_eqMod_pos h_zero_eq_one Nat.one_pos (Nat.Prime.one_lt h₁)
        exact ⟨h_m_zero, h_n_zero⟩
      · by_contra h_ne_zero
        rw [Int.modEq_zero_iff_dvd] at h_m_zero
        have h_coprime : IsCoprime ↑p m := coprime h₁ h_m_zero
        have h_eq_one_m_pow := Int.ModEq.pow_card_sub_one_eq_one h₁ h_coprime.symm
        have h_eq_neg_one := h₃.sub h_eq_one_m_pow
        simp at h_eq_neg_one

        have : n^(p-1) ≡ 1 [ZMOD p] := by
          by_cases h_n_zero : n ≡ 0 [ZMOD p]
          · by_contra
            have : n^(p-1) ≡ 0 ^ (p-1) [ZMOD p] := Int.ModEq.pow (p-1) h_n_zero
            rw [zero_pow hp_pred_ne_zero] at this
            have := Int.ModEq.add_right 1 (this.symm.trans h_eq_neg_one).symm
            simp at this
            exact false_of_zero_eqMod_pos this Nat.one_pos (Nat.Prime.one_lt h₁)
          · rw [Int.modEq_zero_iff_dvd] at h_n_zero
            have h_coprime : IsCoprime ↑p n := coprime h₁ h_n_zero
            have h_eq_one_n_pow := Int.ModEq.pow_card_sub_one_eq_one h₁ h_coprime.symm
            exact h_eq_one_n_pow

        have := Int.ModEq.add_right 1 (h_eq_neg_one.symm.trans this)
        simp at this
        exact false_of_zero_eqMod_pos this Nat.zero_lt_two (Nat.lt_of_succ_le h₂)

    have h_m_n_modEq_zero_13 : m ≡ 0 [ZMOD 13] ∧ n ≡ 0 [ZMOD 13] := aux₂ 13 (by norm_num) (by norm_num) h_12_mod_13
    have h_m_n_modEq_zero_37 : m ≡ 0 [ZMOD 37] ∧ n ≡ 0 [ZMOD 37] := aux₂ 37 (by norm_num) (by norm_num) h_36_mod_37

    -- Now we know that both m and n are divisible by 13 and 37, so by 481, or 481^2 divides both m^2 and n^2

    have h_dvd_m : 481 ∣ m := by
      have h0 : 13 ∣ m := Int.modEq_zero_iff_dvd.mp h_m_n_modEq_zero_13.left
      have h1 : 37 ∣ m := Int.modEq_zero_iff_dvd.mp h_m_n_modEq_zero_37.left
      grind
    have h_dvd_m_sqr : 481^2 ∣ m^2 := pow_dvd_pow_of_dvd h_dvd_m 2

    have h_dvd_n : 481 ∣ n := by
      have h0 : 13 ∣ n := Int.modEq_zero_iff_dvd.mp h_m_n_modEq_zero_13.right
      have h1 : 37 ∣ n := Int.modEq_zero_iff_dvd.mp h_m_n_modEq_zero_37.right
      grind
    have h_dvd_n_sqr : 481^2 ∣ n^2 := pow_dvd_pow_of_dvd h_dvd_n 2

    -- Applying this to min concludes the proof of the lemma
    have h_dvd_min : 481^2 ∣ m^2 ∧ 481^2 ∣ n^2 := by grind
    have h_dvd_min_either {x y n : ℤ} (h₁ : n ∣ x) (h₂ : n ∣ y) : n ∣ min x y := by grind
    exact h_dvd_min_either h_dvd_min.left h_dvd_min.right

  -- Finally use the above to finish the problem
  constructor
  · exact h_sol
  · intro x hx
    have h1 : 0 < x := h_pos x hx
    have h2 : 481^2 ∣ x := h_div x hx
    exact Int.le_of_dvd h1 h2

end Imo1996P4
