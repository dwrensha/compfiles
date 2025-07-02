/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roozbeh Yousefzadeh, David Renshaw
-/

import Mathlib.NumberTheory.Multiplicity
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 1990, Problem 3

Find all integers n > 1 such that n² divides 2ⁿ + 1.
-/

namespace Imo1990P3

determine solution_set : Set ℕ := { 3 }

snip begin

lemma aux_1
    (n : ℕ) :
    (2 : ℕ) ^ n ≡ (1 : ℕ) [MOD (7 : ℕ)] ∨
    (2 : ℕ) ^ n ≡ (2 : ℕ) [MOD (7 : ℕ)] ∨
    (2 : ℕ) ^ n ≡ (4 : ℕ) [MOD (7 : ℕ)] := by
  have h₀ : n % 3 < 3 := Nat.mod_lt n (Nat.zero_lt_succ 2)
  rw [←Nat.div_add_mod n 3]
  generalize n % 3 = r at h₀ ⊢
  generalize n / 3 = d
  interval_cases r
  . left
    induction' d with t ht₀
    . rw [pow_zero]
    . simp only [mul_add, mul_one, pow_add, pow_zero]
      exact Nat.ModEq.mul ht₀ rfl
  . right; left
    induction' d with t ht₀
    . rw [pow_one]
    . rw [mul_add, mul_one, add_assoc, add_comm 3 1, ← add_assoc, pow_add]
      exact Nat.ModEq.mul ht₀ rfl
  . right; right
    induction' d with t ht₀
    . norm_num
      exact rfl
    . rw [mul_add, mul_one, add_assoc, add_comm 3 2, ← add_assoc, pow_add]
      exact Nat.ModEq.mul ht₀ rfl


lemma imo_1990_p3_forward
  (n : ℕ)
  (h₀ : 2 ≤ n)
  (h₁ : n^2 ∣ 2^n + 1) :
  n = 3 := by
  by_cases hn₀: n < 3
  . exfalso
    interval_cases n
    simp at h₁
  . push_neg at hn₀
    have h₂: Odd n := by
      by_contra hc
      apply Nat.not_odd_iff_even.mp at hc
      have h₂₀: Odd (2 ^ n + 1) := by
         refine Even.add_one ?_
         refine Even.pow_of_ne_zero ?_ (by omega)
         decide
      have h₂₁: Even (n ^ 2) := by
        exact (Nat.even_pow' (by omega)).mpr hc
      have h₂₂: Even (2 ^ n + 1) := by
        exact Dvd.dvd.even h₁ h₂₁
      apply Nat.not_odd_iff_even.mpr at h₂₂
      exact h₂₂ h₂₀
    have h₃: (2 : ℕ) ^ n + (1 : ℕ) ∣ (2 : ℕ) ^ ((2 : ℕ) * n) - (1 : ℕ) := by
      have h₃₀: (2 : ℕ) ^ ((2 : ℕ) * n) - (1 : ℕ) = ((2 : ℕ) ^ (n)) ^ (2 : ℕ) - ((1 : ℕ) ^ (n)) ^ (2 : ℕ) := by
        simp [Nat.pow_mul']
      rw [Nat.sq_sub_sq] at h₃₀
      rw [h₃₀, one_pow]
      exact Nat.dvd_mul_right ((2 : ℕ) ^ n + (1 : ℕ)) ((2 : ℕ) ^ n - (1 : ℕ))
    have h₄: ∀ p, Nat.Prime p → 3 ≤ p → p ∣ 2 ^ (p - 1) - 1 := by
      intros p hp₀ hp₁
      have hp₃: Odd p := by
        refine Nat.Prime.odd_of_ne_two hp₀ ?_
        exact Ne.symm (Nat.ne_of_lt hp₁)
      have hp₄: 2 ^ (p - 1) ≡ 1 [ZMOD p] := by
        refine Int.ModEq.pow_card_sub_one_eq_one hp₀ ?_
        refine Int.isCoprime_iff_gcd_eq_one.mpr ?_
        norm_cast
        exact Nat.coprime_two_left.mpr hp₃
      have hp₆₄: (p:ℤ) ∣ 2 ^ (↑p - 1) - 1 := by
        refine Int.modEq_iff_dvd.mp ?_
        exact Int.ModEq.symm hp₄
      rw [@Int.natCast_dvd] at hp₆₄
      refine dvd_trans hp₆₄ ?_
      refine dvd_of_eq ?_
      rw [@Int.natAbs_eq_iff]
      left
      norm_num
    let sp : Finset ℕ := n.primeFactors
    have hsp₁: sp.Nonempty := by
      refine Nat.nonempty_primeFactors.mpr ?_
      refine lt_trans ?_ hn₀
      exact Nat.one_lt_two
    let p : ℕ := Finset.min' sp hsp₁
    have hp₀: p ∈ sp := by exact Finset.min'_mem sp hsp₁
    have hp₁: Nat.Prime p := Nat.prime_of_mem_primeFactors hp₀
    have hp₂: ∀ x ∈ sp, x ≠ p → p < x := by
      intro x hx₀ hx₁
      refine lt_of_le_of_ne ?_ hx₁.symm
      exact Finset.min'_le sp x hx₀
    have hp₃: p = 3 := by
      have hp₄: p ∣ 2 ^ n + 1 := by
        refine dvd_trans ?_ h₁
        refine dvd_pow ?_ (by norm_num)
        exact Nat.dvd_of_mem_primeFactors hp₀
      have hp₅: p ∣ 2 ^ (2 * n) - 1 := by
        exact dvd_trans hp₄ h₃
      have hp₆: p ∣ 2 ^ (p - 1) - 1 := by
        refine h₄ p hp₁ ?_
        have hp₆₀: Odd p := by
          refine Odd.of_dvd_nat ?_ hp₄
          refine Even.add_one ?_
          refine (Nat.even_pow' ?_).mpr ?_
          . exact Nat.ne_zero_of_lt h₀
          . exact Nat.even_iff.mpr rfl
        have hp₆₁: 2 ≤ p := Nat.Prime.two_le hp₁
        by_contra! hh₀
        interval_cases p
        have hh₁: ¬ Odd 2 := by norm_num
        exact hh₁ hp₆₀
      have hp₇: p ∣ Nat.gcd (2 ^ (2 * n) - 1) (2 ^ (p - 1) - 1) := by
        exact Nat.dvd_gcd hp₅ hp₆
      have hp₈: p ∣ 2 ^ (Nat.gcd (2 * n) (p - 1)) - 1 := by
        simp_all only [ne_eq, Nat.pow_sub_one_gcd_pow_sub_one]
      have hp₉: p ≤ (2 : ℕ) ^ ((2 : ℕ) * n).gcd (p - (1 : ℕ)) - (1 : ℕ) := by
        refine Nat.le_of_dvd ?_ hp₈
        refine Nat.sub_pos_of_lt ?_
        refine Nat.one_lt_pow ?_ ?_
        . refine Nat.ne_of_gt ?_
          refine Nat.gcd_pos_of_pos_left _ ?_
          positivity
        . exact Nat.one_lt_two
      have hp₁₀: p ≤ 3 := by
        refine le_trans hp₉ ?_
        refine Nat.sub_le_of_le_add ?_
        have hh₀: (3 : ℕ) + (1 : ℕ) = 2 ^ 2 := by norm_num
        rw [hh₀]
        clear hh₀
        refine Nat.pow_le_pow_right ?_ ?_
        . exact Nat.zero_lt_two
        . refine le_of_eq ?_
          have hh₀: Nat.gcd n (p - 1) = 1 := by
            have g₀: n ≠ (0 : ℕ) := by exact Nat.ne_zero_of_lt h₀
            have g₁: p - (1 : ℕ) ≠ (0 : ℕ) := by
              have g₁₀: 2 ≤ p := Nat.Prime.two_le hp₁
              omega
            have hh₀₀: ((n).gcd (p - (1 : ℕ))).primeFactors = ∅ := by
              rw [Nat.primeFactors_gcd g₀ g₁]
              refine Finset.disjoint_iff_inter_eq_empty.mp ?_
              have g₂: ∀ x ∈ n.primeFactors, p ≤ x := by
                intros x hx₀
                exact Finset.min'_le sp x hx₀
              have g₃: ∀ x ∈ (p - (1 : ℕ)).primeFactors, x < p := by
                intros x hx₀
                refine Nat.lt_of_le_pred hp₁.pos ?_
                . exact Nat.le_of_mem_primeFactors hx₀
              refine Finset.disjoint_left.mpr ?_
              intros x hx₀
              have hx₁: p ≤ x := by exact g₂ x hx₀
              contrapose! hx₁
              exact g₃ x hx₁
            apply Nat.primeFactors_eq_empty.mp at hh₀₀
            cases' hh₀₀ with hh₀₀ hh₀₀
            . exfalso
              have hh₀₁: n.gcd (p - (1 : ℕ)) ≠ (0 : ℕ) := by exact Nat.gcd_ne_zero_left g₀
              exact hh₀₁ hh₀₀
            . exact hh₀₀
          rw [Nat.gcd_comm]
          have hh₁ : Nat.Coprime (2 : ℕ) n := by
            exact Nat.coprime_two_left.mpr h₂
          rw [Nat.gcd_comm] at hh₀
          rw [Nat.Coprime.gcd_mul _ hh₁, hh₀, mul_one]
          refine Nat.gcd_eq_right ?_
          refine Even.two_dvd ?_
          refine Nat.Prime.even_sub_one hp₁ ?_
          refine Odd.ne_two_of_dvd_nat h₂ ?_
          exact Nat.dvd_of_mem_primeFactors hp₀
      have hp₁₁: 2 ≤ p := Nat.Prime.two_le hp₁
      interval_cases p
      . omega
      . exact rfl
    let k : ℕ := multiplicity 3 n
    have hp₆: ∃ d:ℕ, n = d * p ^ k ∧ ¬ 3 ∣ d := by
      rw [hp₃]
      use n / 3 ^ k
      have hp₆₀: (3 : ℕ) ^ k ∣ n := by exact pow_multiplicity_dvd (3 : ℕ) n
      constructor
      . exact (Nat.div_mul_cancel hp₆₀).symm
      . by_contra! hh₀
        have hh₁: (3 : ℕ) * (3 : ℕ) ^ k ∣ n := by
          rw [mul_comm]
          exact (Nat.dvd_div_iff_mul_dvd hp₆₀).mp hh₀
        rw [← Nat.pow_succ'] at hh₁
        have hh₂: ¬ (3 : ℕ) ^ k.succ ∣ n := by
          refine (FiniteMultiplicity.multiplicity_lt_iff_not_dvd ?_).mp ?_
          . refine Nat.finiteMultiplicity_iff.mpr ?_
            simp
            exact Nat.zero_lt_of_lt h₀
          . exact Nat.lt_add_one (multiplicity (3 : ℕ) n)
        exact hh₂ hh₁
    obtain ⟨d, hn₁, hd₀⟩ := hp₆
    have hk₀ : 0 < k := by
      refine dvd_iff_multiplicity_pos.mpr ?_
      rw [← hp₃]
      exact Nat.dvd_of_mem_primeFactors hp₀
    have hk₁: k = 1 := by
      have hp₄: _root_.Prime (3 : ℕ) := by
        rw [← @Nat.prime_iff]
        exact Nat.prime_three
      rw [hp₃] at hp₁
      have hn₂: FiniteMultiplicity (3 : ℕ) n := by
        refine FiniteMultiplicity.of_prime_left hp₄ ?_
        exact Nat.ne_zero_of_lt h₀
      have hn₃: FiniteMultiplicity (3 : ℕ) ((2 : ℕ) ^ n + (1 : ℕ) ^ n) := by
        refine FiniteMultiplicity.of_prime_left hp₄ ?_
        exact Ne.symm (NeZero.ne' ((2 : ℕ) ^ n + (1 : ℕ) ^ n))
      have hk₂: multiplicity 3 (2 ^ n + 1 ^ n) = k + 1 := by
        have hk₂₀: k = multiplicity (3 : ℕ) n := by rfl
        rw [hk₂₀]
        have hk₂₁: emultiplicity 3 (2 ^ n + 1 ^ n) = emultiplicity 3 (2 + 1) + emultiplicity 3 n := by
          refine Nat.emultiplicity_pow_add_pow hp₁ ?_ ?_ ?_ h₂
          . exact Nat.odd_iff.mpr rfl
          . exact Nat.dvd_of_mod_eq_zero rfl
          . exact (Nat.Prime.coprime_iff_not_dvd hp₁).mp rfl
        rw [Nat.Prime.emultiplicity_self hp₁] at hk₂₁
        rw [FiniteMultiplicity.emultiplicity_eq_multiplicity hn₂] at hk₂₁
        rw [FiniteMultiplicity.emultiplicity_eq_multiplicity hn₃] at hk₂₁
        norm_cast at hk₂₁
        rw [hk₂₁]
        exact Nat.add_comm (1 : ℕ) (multiplicity (3 : ℕ) n)
      have hk₃: multiplicity 3 (n ^ 2) ≤ multiplicity 3 (2 ^ n + 1) := by
        refine (FiniteMultiplicity.multiplicity_le_multiplicity_iff ?_ ?_).mpr ?_
        . exact FiniteMultiplicity.pow hp₄ hn₂
        . refine FiniteMultiplicity.of_prime_left hp₄ ?_
          exact Ne.symm (Nat.zero_ne_add_one ((2 : ℕ) ^ n))
        . exact fun (n_2 : ℕ) (a : (3 : ℕ) ^ n_2 ∣ n ^ (2 : ℕ)) ↦ Nat.dvd_trans a h₁
      have hk₄: multiplicity 3 (n ^ 2) = 2 * k := by
        exact FiniteMultiplicity.multiplicity_pow hp₄ hn₂
      rw [one_pow] at hk₂
      rw [hk₄, hk₂] at hk₃
      have hk₅: k ≤ 1 := by bound
      exact (Nat.le_antisymm hk₅ hk₀)
    have hd : d = 1 := by
      by_contra! hd₁
      cases' lt_or_gt_of_ne hd₁ with hd₂ hd₂
      . interval_cases d
        rw [hn₁, zero_mul] at hn₀
        bound [hn₀]
      . let sq : Finset ℕ := d.primeFactors
        have hsq₁: sq.Nonempty := Nat.nonempty_primeFactors.mpr hd₂
        let q : ℕ := Finset.min' sq hsq₁
        have hq₀: q ∈ sq := by exact Finset.min'_mem sq hsq₁
        have hq₁: Nat.Prime q := Nat.prime_of_mem_primeFactors hq₀
        have hq₂: q ∣ d := Nat.dvd_of_mem_primeFactors hq₀
        have hq₃: q ∣ n := by
          refine dvd_trans hq₂ ?_
          exact Dvd.intro (p ^ k) hn₁.symm
        have hq₄: Odd q := Odd.of_dvd_nat h₂ hq₃
        have hq₅: 5 ≤ q := by
          by_contra! hh₀
          have hh₁: 2 ≤ q := Nat.Prime.two_le hq₁
          interval_cases q
          all_goals try tauto
        have hq₉: q = 7 := by
          have hh₀: Nat.gcd n (q - 1) = 1 ∨ Nat.gcd n (q - 1) = 3 := by
            have hh₀₁: ∀ x ∈ (q - 1).primeFactors, x ≤ q - 1 := by
              intros x hx₀
              . exact Nat.le_of_mem_primeFactors hx₀
            have hh₀₂: ∀ x ∈ d.primeFactors, q ≤ x := by
              intros x hx₀
              exact Finset.min'_le sq x hx₀
            have hh₀₃: Nat.gcd (q - 1) d = 1 := by
              have hh₀₃₀: q - (1 : ℕ) ≠ (0 : ℕ) := by omega
              have hh₀₃₁: d ≠ 0 := by exact Nat.ne_zero_of_lt hd₂
              have hh₀₃₂: ((q - 1).gcd d).primeFactors = ∅ := by
                rw [Nat.primeFactors_gcd hh₀₃₀ hh₀₃₁]
                refine Finset.disjoint_iff_inter_eq_empty.mp ?_
                refine Finset.disjoint_left.mpr ?_
                intros x hx₀
                have hx₁: x ≤ q - (1 : ℕ) := by exact hh₀₁ x hx₀
                contrapose! hx₁
                refine Nat.lt_of_succ_le ?_
                rw [Nat.succ_eq_add_one, Nat.sub_add_cancel (by bound)]
                exact hh₀₂ x hx₁
              apply Nat.primeFactors_eq_empty.mp at hh₀₃₂
              cases' hh₀₃₂ with hh₀₃₂ hh₀₃₂
              . exfalso
                have hh₀₁: (q - 1).gcd d ≠ (0 : ℕ) := by exact Nat.gcd_ne_zero_left hh₀₃₀
                exact hh₀₁ hh₀₃₂
              . exact hh₀₃₂
            have hh₀₄: Nat.Coprime d (p ^ k) := by
              refine (Nat.coprime_pow_right_iff hk₀ _ _).mpr ?_
              . refine Nat.Coprime.symm ?_
                refine (Nat.Prime.coprime_iff_not_dvd hp₁).mpr ?_
                rw [hp₃]
                exact hd₀
            rw [hn₁, Nat.gcd_comm]
            rw [Nat.Coprime.gcd_mul _ hh₀₄, hh₀₃, one_mul]
            rw [hk₁, pow_one, hp₃]
            let m : ℕ := (q - (1 : ℕ)).gcd (3 : ℕ)
            have hm₀: m ≤ 3 := by
              refine Nat.gcd_le_right (q - 1) ?_
              exact Nat.zero_lt_succ (2 : ℕ)
            have hm₁: 0 < m := by
              refine Nat.gcd_pos_of_pos_right _ ?_
              exact Nat.zero_lt_succ (2 : ℕ)
            have hm₂: m = (q - (1 : ℕ)).gcd (3 : ℕ) := by rfl
            rw [← hm₂]
            interval_cases m
            . left
              rfl
            . exfalso
              symm at hm₂
              apply Nat.gcd_eq_iff.mp at hm₂
              omega
            . right
              rfl
          have hh₁: q ∣ 2 ^ (2 * n) - 1 := by
            refine dvd_trans ?_ h₃
            refine dvd_trans ?_ h₁
            refine dvd_trans hq₃ ?_
            exact Dvd.intro_left (n ^ 1) rfl
          have hh₂: q ∣ 2 ^ (q - 1) - 1 := by
            refine h₄ q hq₁ ?_
            exact le_of_add_le_right hq₅
          have hh₃: q ∣ Nat.gcd (2 ^ (2 * n) - 1) (2 ^ (q - 1) - 1) := by
            exact Nat.dvd_gcd hh₁ hh₂
          have hh₄: q ∣ 2 ^ (2 * Nat.gcd n (q - 1)) - 1 := by
            have hh₄₀: q ∣ 2 ^ (Nat.gcd (2 * n) (q - 1)) - 1 := by
              simp_all only [Nat.pow_sub_one_gcd_pow_sub_one]
            have hh₄₁: 2 * Nat.gcd n (q - 1) = Nat.gcd (2 * n) (q - 1) := by
              have hh₄₂: Nat.Coprime (2 : ℕ) n := Nat.coprime_two_left.mpr h₂
              symm
              rw [Nat.gcd_comm, Nat.gcd_comm n, Nat.Coprime.gcd_mul _ hh₄₂]
              have hh₄₃: (q - (1 : ℕ)).gcd (2 : ℕ) = 2 := by
                refine Nat.gcd_eq_right ?_
                refine Even.two_dvd ?_
                refine Nat.Prime.even_sub_one hq₁ ?_
                exact Odd.ne_two_of_dvd_nat h₂ hq₃
              rw [hh₄₃]
            rw [hh₄₁]
            exact hh₄₀
          have hh₅: q ∣ 3 ^ 2 * 7 := by
            cases' hh₀ with hh₀ hh₀
            . exfalso
              rw [hh₀] at hh₄
              norm_num at hh₄
              have hh₅₀: q ≤ 3 := Nat.le_of_dvd (by norm_num) hh₄
              bound
            . rw [hh₀] at hh₄
              norm_num at hh₄
              exact hh₄
          have hh₆: q ∣ 7 := by
            refine Nat.Coprime.dvd_of_dvd_mul_left ?_ hh₅
            refine (Nat.coprime_pow_right_iff (by norm_num) _ _).mpr ?_
            refine (Nat.Prime.coprime_iff_not_dvd hq₁).mpr ?_
            refine Nat.not_dvd_of_pos_of_lt ?_ ?_
            . exact Nat.zero_lt_succ (2 : ℕ)
            . exact Nat.lt_of_add_left_lt hq₅
          have hh₇: q ≤ 7 := by exact Nat.le_of_dvd (by omega) hh₆
          interval_cases q
          . exfalso
            omega
          . exfalso
            omega
          . rfl
        have hq₁₀: 2 ^ n ≡ 6 [MOD 7] := by
          have hh₀: (2 : ℕ) ^ n + 1 ≡ (6 : ℕ) + 1 [MOD (7 : ℕ)] := by
            norm_num
            refine Nat.ModEq.symm ?_
            have hh₁: (7 : ℕ) ≤ (2 : ℕ) ^ n + (1 : ℕ) := by
              have hh₂: 2 ^ 3 ≤ 2 ^ n := by
                exact Nat.pow_le_pow_right (by norm_num) hn₀
              omega
            refine (Nat.modEq_iff_dvd' hh₁).mpr ?_
            refine Nat.dvd_sub ?_ ?_
            . rw [← hq₉]
              refine dvd_trans hq₃ ?_
              refine dvd_trans ?_ h₁
              exact Dvd.intro_left (n ^ 1) rfl
            . exact Nat.dvd_of_mod_eq_zero rfl
          exact Nat.ModEq.add_right_cancel' (1 : ℕ) hh₀
        have hq₁₁: ¬ 2 ^ n ≡ 6 [MOD 7] := by
          clear hq₁₀
          obtain hq₁₂ | hq₁₂ | hq₁₂ := aux_1 n
          . by_contra! hh₀
            have hh₁: 1 ≡ (6 : ℕ) [MOD (7 : ℕ)] := Nat.ModEq.trans hq₁₂.symm hh₀
            have hh₂: ¬ 1 ≡ (6 : ℕ) [MOD (7 : ℕ)] := by decide
            exact hh₂ hh₁
          . by_contra! hh₀
            have hh₁: 2 ≡ (6 : ℕ) [MOD (7 : ℕ)] := Nat.ModEq.trans hq₁₂.symm hh₀
            have hh₂: ¬ 2 ≡ (6 : ℕ) [MOD (7 : ℕ)] := by decide
            exact hh₂ hh₁
          . by_contra! hh₀
            have hh₁: 4 ≡ (6 : ℕ) [MOD (7 : ℕ)] := Nat.ModEq.trans hq₁₂.symm hh₀
            have hh₂: ¬ 4 ≡ (6 : ℕ) [MOD (7 : ℕ)] := by decide
            exact hh₂ hh₁
        exact hq₁₁ hq₁₀
    rw [hn₁, hk₁, hp₃, hd, pow_one, one_mul]


snip end

problem imo1990_p3 (n : ℕ) (hn : 1 < n) : n ∈ solution_set ↔ n^2 ∣ 2^n + 1 := by
  constructor
  · intro hs
    rw [Set.mem_singleton_iff] at hs
    rw [hs]
    norm_num
  · intro hnd
    exact imo_1990_p3_forward n hn hnd


end Imo1990P3
