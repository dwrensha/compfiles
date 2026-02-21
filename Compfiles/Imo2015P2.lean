/-
Copyright (c) 2023 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benpigchu
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 2015, Problem 2

Determine all triples of positive integers a, b, c such that each of
ab - c, bc - a, ca - b is a power of two.
-/

namespace Imo2012P2

determine SolutionSet : Set (ℤ × ℤ × ℤ) := {
  (2, 2, 2),
  (2, 2, 3), (2, 3, 2), (3, 2, 2),
  (2, 6, 11), (6, 11, 2), (11, 2, 6),
  (11, 6, 2), (6, 2, 11), (2, 11, 6),
  (3, 5, 7), (5, 7, 3), (7, 3, 5),
  (7, 5, 3), (5, 3, 7), (3, 7, 5)
}

def is_power_of_two (n : ℤ) : Prop := ∃ m : ℕ, n = 2 ^ m

snip begin

lemma pow_of_two_coprime_odd (m : ℕ) {a : ℤ} (ha : ¬2 ∣ a) :
    IsCoprime ((2 : ℤ) ^ m) a := by
  rw [Int.isCoprime_iff_nat_coprime, Int.natAbs_pow, ← Int.ofNat_two]
  rw [Int.natAbs_natCast, Nat.coprime_comm]
  apply Nat.Prime.coprime_pow_of_not_dvd Nat.prime_two
  rw [← Int.ofNat_dvd, Int.ofNat_two, Int.dvd_natAbs]
  exact ha

lemma pow_of_two_dvd_odd_mul_self_sub_1 {m : ℕ} {a : ℤ}
    (ha : ¬2 ∣ a) (ha' : 1 < a) (h : (2 : ℤ) ^ m ∣ a ^ 2 - 1) :
    (2 : ℤ) ^ m ≤ 2 * a + 2 := by
  rw [Int.two_dvd_ne_zero, ← Int.odd_iff, odd_iff_exists_bit1] at ha
  rcases ha with ⟨k, hk⟩
  rw [hk] at h ⊢
  by_cases! hk' : 2 ∣ k
  · rw [(by ring : (2 * k + 1) ^ 2 - 1 = 4 * k * (k + 1))] at h
    have h' : 2 ^ m ∣4 * k := by
      apply IsCoprime.dvd_of_dvd_mul_right _ h
      apply pow_of_two_coprime_odd m
      rw [← even_iff_two_dvd] at hk' ⊢
      rw [Int.not_even_iff_odd]
      exact Even.add_one hk'
    calc 2 ^ m
        ≤ 4 * k := Int.le_of_dvd (by lia) h'
      _ ≤ 2 * (2 * k + 1) + 2 := by lia
  · rw [(by ring : (2 * k + 1) ^ 2 - 1 = (4 * k + 4) * k)] at h
    have h' : 2 ^ m ∣4 * k + 4 := by
      apply IsCoprime.dvd_of_dvd_mul_right _ h
      exact pow_of_two_coprime_odd m hk'
    calc 2 ^ m
        ≤ 4 * k + 4 := Int.le_of_dvd (by lia) h'
      _ ≤ 2 * (2 * k + 1) + 2 := by lia

lemma dvd_pow_of_two {m : ℕ} {a : ℤ}
    (ha' : 0 ≤ a) (h : a ∣ 2 ^ m) : ∃ k : ℕ, a = 2 ^ k := by
    rw [← Int.natAbs_dvd_natAbs, Int.natAbs_pow] at h
    rw [← Int.ofNat_two, Int.natAbs_natCast] at h
    rw [Nat.dvd_prime_pow Nat.prime_two] at h
    rcases h with ⟨k, hk', hk⟩
    use k
    rw [← Int.natCast_inj, Int.natAbs_of_nonneg ha'] at hk
    rw [Int.natCast_pow, Int.ofNat_two] at hk
    exact hk

lemma odd_dvd_pow_of_two {m : ℕ} {a : ℤ}
    (ha : ¬2 ∣ a) (ha' : 0 ≤ a) (h : a ∣ 2 ^ m) : a = 1 := by
  rcases dvd_pow_of_two ha' h with ⟨k,  hk⟩
  rw [hk] at ha ⊢
  contrapose! ha
  apply dvd_pow_self
  contrapose! ha
  rw [ha]
  norm_num

lemma sq_pow_of_two_sub_two {m₁ m₂ : ℕ} {a : ℤ} (ha : 2 ≤ a)
    (h₁ : a ∣ 2 ^ m₁) (h₂ : a ^ 2 - 2 ∣ 2 ^ m₂)
    : a = 2 := by
  apply dvd_pow_of_two (by lia) at h₁
  have ha' : 0 ≤ a ^ 2 - 2 := by
    rw [sub_nonneg]
    calc 2
        ≤ 2 ^ 2 := by norm_num
      _ ≤ a ^ 2 := (pow_le_pow_iff_left₀ (by norm_num) (by lia) (by norm_num)).mpr ha
  apply dvd_pow_of_two ha' at h₂
  rcases h₁ with ⟨k₁, hk₁⟩
  rcases h₂ with ⟨k₂, hk₂⟩
  rw [hk₁] at ha hk₂ ⊢
  have hk₁' : k₁ ≠ 0 := by
    contrapose! ha with h'
    rw [h']
    norm_num
  apply Nat.exists_eq_add_one_of_ne_zero at hk₁'
  rcases hk₁' with ⟨k, hk⟩
  rw [hk] at hk₂ ⊢
  rw [(by ring : ((2 : ℤ) ^ (k + 1)) ^ 2 - 2 = 2 * (2 * 2 ^ (2 * k) - 1))] at hk₂
  have h' : ¬(2 : ℤ) ∣ 2 * 2 ^ (2 * k) - 1 := by
    rw [← even_iff_two_dvd, Int.not_even_iff_odd]
    exact Even.sub_odd (even_two_mul _) odd_one
  have h'' : (0 : ℤ) ≤ 2 * 2 ^ (2 * k) - 1 := by
    rw [sub_nonneg, ← zero_add 1, Int.add_one_le_iff]
    positivity
  have h''' := dvd_mul_left (2 * 2 ^ (2 * k) - 1) (2 : ℤ)
  rw [hk₂] at h'''
  apply odd_dvd_pow_of_two h' h'' at h'''
  have hk' : k = 0 := by
    contrapose! h'''
    apply ne_of_gt
    rw [lt_sub_iff_add_lt]
    norm_num
    calc (1 : ℤ)
      < 2 ^ (2 * 1) := by norm_num
    _ ≤ 2 ^ (2 * k) := by
      rw [pow_le_pow_iff_right₀ (by norm_num)]
      rw [mul_le_mul_iff_right₀ (by norm_num)]
      rw [Nat.one_le_iff_ne_zero]
      exact h'''
  rw [hk']
  norm_num

lemma swap_ab_solution (a b c : ℤ) : (a,b,c) ∈ SolutionSet ↔ (b,a,c) ∈ SolutionSet := by
  simp
  constructor <;> intro h <;> casesm* _ ∨ _
    <;> rcases h with ⟨ha, hb, hc⟩ <;> rw [ha, hb, hc] <;> norm_num

lemma swap_bc_solution (a b c : ℤ) : (a,b,c) ∈ SolutionSet ↔ (a,c,b) ∈ SolutionSet := by
  simp
  constructor <;> intro h <;> casesm* _ ∨ _
    <;> rcases h with ⟨ha, hb, hc⟩ <;> rw [ha, hb, hc] <;> norm_num

snip end

problem imo2015_p2 (a b c : ℤ) :
    (a,b,c) ∈ SolutionSet ↔
      0 < a ∧ 0 < b ∧ 0 < c ∧
      is_power_of_two (a * b - c) ∧
      is_power_of_two (b * c - a) ∧
      is_power_of_two (c * a - b) := by
  wlog hbc : c ≤ b generalizing a b c
  · have h := this a c b (by lia)
    nth_rw 2 [← and_assoc]
    nth_rw 3 [and_comm]
    nth_rw 3 [← and_rotate]
    nth_rw 5 [and_comm]
    rw [mul_comm c a, mul_comm b c, mul_comm a b, and_assoc, ← h, swap_bc_solution]
  wlog hab : b ≤ a generalizing a b c
  · by_cases! hac : a ≤ c
    · have h := this b c a (by lia) (by lia)
      nth_rw 2 [← and_assoc]
      nth_rw 1 [← and_assoc]
      nth_rw 2 [and_rotate]
      nth_rw 3 [and_rotate]
      rw [and_assoc, and_assoc, ← h, swap_ab_solution, swap_bc_solution]
    · have h := this b a c (by lia) (by lia)
      nth_rw 1 [← and_assoc]
      nth_rw 2 [and_comm]
      nth_rw 5 [and_comm]
      rw [mul_comm c a, mul_comm b c, mul_comm a b, and_assoc, ← h, swap_ab_solution]
  constructor
  · simp [is_power_of_two]
    have h_is_power_of_two_one :∃ m : ℕ, (1 : ℤ) = 2 ^ m := by use 0; norm_num
    have h_is_power_of_two_two :∃ m : ℕ, (2 : ℤ) = 2 ^ m := by use 1; norm_num
    have h_is_power_of_two_four :∃ m : ℕ, (4 : ℤ) = 2 ^ m := by use 2; norm_num
    have h_is_power_of_two_eight :∃ m : ℕ, (8 : ℤ) = 2 ^ m := by use 3; norm_num
    have h_is_power_of_two_sixteen :∃ m : ℕ, (16 : ℤ) = 2 ^ m := by use 4; norm_num
    have h_is_power_of_two_thirty_two :∃ m : ℕ, (32 : ℤ) = 2 ^ m := by use 5; norm_num
    have h_is_power_of_two_sixty_four :∃ m : ℕ, (64 : ℤ) = 2 ^ m := by use 6; norm_num
    intro h
    casesm* _ ∨ _  <;> rcases h with ⟨ha, hb, hc⟩ <;> rw [ha, hb, hc]
      <;> norm_num <;> try constructorm* _ ∧ _
    all_goals assumption
  · simp only [is_power_of_two]
    rintro ⟨ha, hb, hc, ⟨mabc, habc⟩, ⟨mbca, hbca⟩, ⟨mcab, hcab⟩⟩
    -- From here we use "the shortest solution I am aware of" in Evan Chen's writeup
    -- https://web.evanchen.cc/exams/IMO-2015-notes.pdf
    have h_c_one : c ≠ 1 := by
      intro hc'
      rw [hc', mul_one] at hbca
      rw [← sub_nonpos, hbca] at hab
      contrapose! hab
      positivity
    have h_bca_dvd_cab : b * c - a ∣ c * a - b := by
      rw [hbca, hcab]
      apply pow_dvd_pow
      rw [← pow_le_pow_iff_right₀ (by norm_num : 1 < (2 : ℤ))]
      rw [← hbca, ← hcab, sub_le_sub_iff]
      rw [(by ring : b * c + b = b * (c + 1)), (by ring : c * a + a = a * (c + 1))]
      rw [mul_le_mul_iff_left₀ (by lia)]
      exact hab
    have h_cab_dvd_abc : c * a - b ∣ a * b - c := by
      rw [habc, hcab]
      apply pow_dvd_pow
      rw [← pow_le_pow_iff_right₀ (by norm_num : 1 < (2 : ℤ))]
      rw [← habc, ← hcab, sub_le_sub_iff]
      rw [(by ring : c * a + c = c * (a + 1)), (by ring : a * b + b = b * (a + 1))]
      rw [mul_le_mul_iff_left₀ (by lia)]
      exact hbc
    have h_bca_dvd_abc : b * c - a ∣ a * b - c := dvd_trans h_bca_dvd_cab h_cab_dvd_abc
    have h₁ := dvd_add (h_cab_dvd_abc) (dvd_mul_of_dvd_right (dvd_refl _) a )
    rw [(by ring :a * b - c + a * (c * a - b) = c * (a ^ 2 - 1))] at h₁
    by_cases! ha' : 2 ∣ a
    · have h₂ : c * a - b ∣ c := by
        apply IsCoprime.dvd_of_dvd_mul_right _ h₁
        rw [hcab]
        apply pow_of_two_coprime_odd mcab
        intro h'
        rw [dvd_sub_right (dvd_trans ha' (dvd_pow_self a (by norm_num)))] at h'
        norm_num at h'
      have h₂' := Int.le_of_dvd hc h₂
      have hc_two : c = 2 := by
        contrapose! h₂'
        rw [lt_sub_iff_add_lt]
        calc c + b
            ≤ 2 * a := by lia
          _ < c * a := (mul_lt_mul_iff_left₀ ha).mpr (by lia)
      have ha_two : a = 2 := by lia
      have hb_two : b = 2 := by lia
      rw [ha_two, hb_two, hc_two]
      simp
    · have h_abc_even : 2 ∣ a * b - c := by
        rw [habc]
        apply dvd_pow_self
        rw [← Nat.one_le_iff_ne_zero, ← pow_le_pow_iff_right₀ (by norm_num : 1 < (2 : ℤ))]
        rw [← habc, pow_one, le_sub_iff_add_le]
        calc 2 + c
            ≤ a * 2 := by lia
          _ ≤ a * b := (mul_le_mul_iff_right₀ ha).mpr (by lia)
      have h_cab_even : 2 ∣ c * a - b := by
        rw [hcab]
        apply dvd_pow_self
        rw [← Nat.one_le_iff_ne_zero, ← pow_le_pow_iff_right₀ (by norm_num : 1 < (2 : ℤ))]
        rw [← hcab, pow_one, le_sub_iff_add_le]
        calc 2 + b
            ≤ 2 * a := by lia
          _ ≤ c * a := (mul_le_mul_iff_left₀ ha).mpr (by lia)
      by_cases! hb' : ¬2 ∣ b
      · have hc' : ¬2 ∣ c := by
          contrapose! h_abc_even with hc'
          rw [dvd_sub_left hc', Prime.dvd_mul Int.prime_two]
          push_neg
          exact ⟨ha', hb'⟩
        have h₂ : c * a - b ∣ a ^ 2 - 1 := by
          apply IsCoprime.dvd_of_dvd_mul_left _ h₁
          rw [hcab]
          exact pow_of_two_coprime_odd mcab hc'
        rw [hcab] at h₂
        apply pow_of_two_dvd_odd_mul_self_sub_1 ha' (by lia) at h₂
        have hc_ne_2 : c ≠ 2 := by
          contrapose! hc'
          rw [hc']
        have hb_ne_a : b ≠ a := by
          intro h'
          rw [h', (by ring : a * c - a = a * (c - 1))] at hbca
          apply dvd_of_mul_right_eq at hbca
          apply odd_dvd_pow_of_two ha' (by lia) at hbca
          lia
        have hb_add_1_ne_a : b + 1 ≠ a := by
          contrapose! ha'
          rw [← ha']
          rw [← even_iff_two_dvd] at hb' ⊢
          rw [Int.not_even_iff_odd] at hb'
          exact Odd.add_one hb'
        rw [← hcab] at h₂
        have hc_three : c = 3 := by
          contrapose! h₂ with h'
          rw [lt_sub_iff_add_lt]
          calc 2 * a + 2 + b
              ≤ 3 * a := by lia
            _ < c * a := (mul_lt_mul_iff_left₀ ha).mpr (by lia)
        have hb_add_two_a : b + 2 = a := by
          contrapose! h₂ with h'
          rw [lt_sub_iff_add_lt]
          calc 2 * a + 2 + b
              < 3 * a := by lia
            _ ≤ c * a := (mul_le_mul_iff_left₀ ha).mpr (by lia)
        have h₃ : mbca < mcab := by
          rw [← pow_lt_pow_iff_right₀ (by norm_num : 1 < (2 : ℤ))]
          rw [← hbca, ← hcab, sub_lt_sub_iff]
          rw [(by ring : b * c + b = b * (c + 1)), (by ring : c * a + a = a * (c + 1))]
          rw [mul_lt_mul_iff_left₀ (by lia)]
          lia
        rw [Nat.lt_iff_add_one_le] at h₃
        rw [← pow_le_pow_iff_right₀ (by norm_num : 1 < (2 : ℤ))] at h₃
        rw [pow_add, pow_one, ← hbca, ← hcab, hc_three, ← hb_add_two_a, ← sub_nonneg] at h₃
        rw [(by ring : 3 * (b + 2) - b - (b * 3 - (b + 2)) * 2 = 2 * (5 - b))] at h₃
        rw [mul_nonneg_iff_of_pos_left (by norm_num)] at h₃
        have hc_ne_4 : b ≠ 4 := by
          contrapose! hb'
          rw [hb']
          norm_num
        have hc_ne_b : c ≠ b := by
          intro h'
          rw [h', (by ring : b * a - b = b * (a - 1))] at hcab
          apply dvd_of_mul_right_eq at hcab
          apply odd_dvd_pow_of_two hb' (by lia) at hcab
          lia
        have hb_four : 4 < b := by lia
        have hb_five : b = 5 := by lia
        rw [hb_five] at hb_add_two_a
        norm_num at hb_add_two_a
        rw [hc_three, hb_five, ← hb_add_two_a]
        simp
      · have hc' : 2 ∣ c := by
          contrapose! h_cab_even with hc'
          rw [dvd_sub_left hb', Prime.dvd_mul Int.prime_two]
          push_neg
          exact ⟨hc', ha'⟩
        have h₂ := dvd_refl (b * c - a)
        nth_rw 2 [hbca] at h₂
        have hbca' : ¬2 ∣ b * c - a := by
          rw [← even_iff_two_dvd] at ha' hb' ⊢
          rw [Int.not_even_iff_odd] at ha' ⊢
          apply Even.sub_odd _ ha'
          apply Even.mul_right hb'
        have hbca'' : 0 ≤ b * c - a := by
          rw [hbca]
          positivity
        apply odd_dvd_pow_of_two hbca' hbca'' at h₂
        have h₃ : b * c ^ 2 - b - c = c * a - b := by
          rw [(by ring :  b * c ^ 2 - b - c =  (b * c - a) * c + a * c - b - c), h₂]
          ring
        have h₄ := dvd_add (dvd_mul_of_dvd_right (h_cab_dvd_abc) (1 - c ^ 2)) (dvd_mul_of_dvd_right (dvd_refl _) (a + 1))
        rw [add_mul] at h₄
        nth_rw 2 [← h₃] at h₄
        ring_nf at h₄
        rw [← h₃] at h₄
        by_cases! h' : -c + (c ^ 3 - b) ≠ 0
        · have h₅ := Int.natAbs_le_of_dvd_ne_zero h₄ h'
          rw [← Int.ofNat_le, Int.natCast_natAbs, Int.natCast_natAbs] at h₅
          have hcab'' : 0 ≤ c * a - b := by
            rw [hcab]
            positivity
          rw [← h₃] at hcab''
          rw [abs_of_nonneg hcab''] at h₅
          by_cases! h'' : -c + (c ^ 3 - b) < 0
          · rw [abs_of_neg h''] at h₅
            exfalso
            contrapose! h₅
            rw [sub_sub, lt_sub_iff_add_lt]
            calc -(-c + (c ^ 3 - b)) + (b + c)
                = 2 * b + 2 * c - c ^ 3 := by ring
              _ < 2 * b + 2 * c := Int.sub_lt_self _ (by positivity)
              _ ≤ b * 4 := by lia
              _ = b * 2 ^ 2 := by norm_num
              _ ≤ b * c ^ 2 := by
                  rw [mul_le_mul_iff_right₀ hb]
                  rw [pow_le_pow_iff_left₀ (by norm_num) (by lia) (by norm_num)]
                  lia
          · rw [abs_of_nonneg h''] at h₅
            rw [(by ring : -c + (c ^ 3 - b) = c * c ^ 2 - b - c)] at h₅
            rw [sub_sub, sub_sub] at h₅
            rw [sub_le_sub_iff_right (b + c)] at h₅
            rw [mul_le_mul_iff_left₀ (by positivity)] at h₅
            have hbc' := le_antisymm h₅ hbc
            rw [hbc', sub_eq_iff_eq_add, ← sub_eq_iff_eq_add'] at h₂
            rw [← h₂, hbc', (by ring : (c * c - 1) * c - c = c * (c ^ 2 - 2))] at habc
            have hc₁ := dvd_mul_right c (c ^ 2 - 2)
            have hc₂ := dvd_mul_left (c ^ 2 - 2) c
            rw [habc] at hc₁ hc₂
            have hc_two := sq_pow_of_two_sub_two (by lia) hc₁ hc₂
            rw [hc_two] at h₂ hbc'
            norm_num at h₂
            rw [← h₂, hbc', hc_two]
            simp
        · rw [add_sub, sub_eq_zero] at h'
          rw [← h', sub_eq_iff_eq_add, ← sub_eq_iff_eq_add'] at h₂
          rw [← h₂, ← h', (by ring : c * ((-c + c ^ 3) * c - 1) - (-c + c ^ 3) = c * c ^ 2 * (c ^ 2 - 2) )] at hcab
          have hc₁ := dvd_mul_of_dvd_left (dvd_mul_right c (c ^ 2)) (c ^ 2 - 2)
          have hc₂ := dvd_mul_left (c ^ 2 - 2) (c * c ^ 2)
          rw [hcab] at hc₁ hc₂
          have hc_two := sq_pow_of_two_sub_two (by lia) hc₁ hc₂
          rw [hc_two] at h₂ h'
          norm_num at h₂ h'
          rw [← h₂, ← h', hc_two]
          simp


end Imo2012P2
