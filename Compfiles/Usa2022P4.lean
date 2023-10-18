/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import Compfiles.Meta.ProblemExtraction

problem_file

/-!
# USA Mathematical Olympiad 2022, Problem 4

Determine all pairs of primes (p, q) where p - q and pq - q
are both perfect squares.
-/

namespace Usa2022P4

determine solution_set : Set (ℕ × ℕ) := {(3, 2)}

problem usa2022_p4 (p q : ℕ) :
    (p, q) ∈ solution_set ↔
    p.Prime ∧ q.Prime ∧
    ∃ a, a^2 + q = p ∧ ∃ b, b^2 + q = p * q := by
  constructor
  · -- easy direction
    intro hpq
    obtain ⟨rfl, rfl⟩ := hpq
    exact ⟨by norm_num, by norm_num, 1, by norm_num, 2, by norm_num⟩

  -- Informal proof outline taken from
  -- https://web.evanchen.cc/exams/USAMO-2022-notes.pdf
  rintro ⟨hpp, hpq, a, ha, b, hb⟩

  -- Note that 0 < p and 0 < q because they are prime.
  have hp_pos : 0 < p := Nat.Prime.pos hpp
  have hq_pos : 0 < q := Nat.Prime.pos hpq

  -- Note that we then have 0 < a < p, and 0 < b < p (because q ≤ p).
  have hqlep : q ≤ p := (Nat.le_add_left q (a ^ 2)).trans_eq ha

  have hbp : b < p := by
    by_contra' H
    have h2 : p^2 ≤ b^2 := Nat.pow_le_pow_of_le_left H 2
    have h6 :=
      calc p * p = p^2 := (Nat.pow_two p).symm
           _ < p^2 + q := Nat.lt_add_of_pos_right hq_pos
           _ ≤ _ := Nat.add_le_add_right h2 q
           _ = p * q := hb
    have h7 : p < q := (mul_lt_mul_left hp_pos).mp h6
    exact Nat.le_lt_antisymm hqlep h7

  -- Subtracting our equations gives (b - a)(b + a) = b² - a² = p(q - 1),
  have h1 : (b + a) * (b - a) = p * (q - 1) := by
    rw [←Nat.sq_sub_sq, Nat.mul_sub_left_distrib, mul_one]
    have h2 : (b^2 + q) - (a^2 + q) = p * q - p := hb ▸ ha ▸ rfl
    rw [Nat.add_sub_add_right] at h2
    exact h2

  have hba : a < b := by
    have h2 : p < p * q := lt_mul_right hp_pos (Nat.Prime.one_lt hpq)
    have h3 := calc
              a^2 + q = p := ha
              _ < p * q := h2
              _ = b^2 + q := hb.symm
    have h4 : a^2 < b^2 := (Nat.add_lt_add_iff_right q (a ^ 2) (b ^ 2)).mp h3
    exact lt_of_pow_lt_pow' 2 h4
  have hba' : 0 < b - a := Nat.sub_pos_of_lt hba

  -- Since b - a < p and p is prime, we have that p divides b + a.
  have h2 : b - a < p := tsub_lt_of_lt hbp
  have h3 : ¬ p ∣ b - a := Nat.not_dvd_of_pos_of_lt hba' h2

  have h4 : p ∣ p * (q - 1) := Nat.dvd_mul_right p (q - 1)
  rw [←h1, mul_comm] at h4
  have h5 : p ∣ b + a := Or.resolve_left ((Nat.Prime.dvd_mul hpp).mp h4) h3

  -- Since and b + a < 2p, we have that a + b must in fact equal p.
  have h6 : b + a < 2 * p := by linarith
  have h7 : b + a = p := by
    obtain ⟨k, hk⟩ := h5
    rw [mul_comm, hk] at h6
    have : k < 2 := (mul_lt_mul_left hp_pos).mp h6
    interval_cases k <;> linarith

  -- Hence q - 1 = b - a.
  have h8 : q - 1 = b - a := by
    rw [h7] at h1
    exact (Nat.eq_of_mul_eq_mul_left hp_pos h1).symm

  -- Note that b - a and b + a have the same parity.
  -- Therefore p and q - 1 have the same parity.
  -- If they are both even, then q > p, contradiction.
  -- Therefore, they are both odd, and q = 2.
  have h9 : q = 2 := by
    have h10 : (b + a) % 2 = (b - a) % 2 := by
      have h11 : b + a = b - a + 2 * a := by
        rw [Nat.two_mul, ←add_assoc, add_left_inj]
        exact Nat.eq_add_of_sub_eq (Nat.le_of_lt hba) rfl
      rw [h11, Nat.add_mod]
      simp only [Nat.mul_mod_right, add_zero, Nat.mod_mod]
    rw [h7, ←h8] at h10
    cases' h : p % 2 with p'
    · have h14 : p = 2 := by
        have h15 : 2 ∣ p := Nat.modEq_zero_iff_dvd.mp h
        cases' Nat.Prime.eq_one_or_self_of_dvd hpp _ h15 with h16 h16
        · norm_num at h16
        · exact h16.symm
      rw [h14] at hqlep
      interval_cases q
      · norm_num at h8
        rw [h8] at hba'
        norm_num at hba'
      · rfl
    · cases' p' with p''
      · norm_num at h
        rw [h] at h10
        apply_fun (fun x ↦ (x + (1%2))%2) at h10
        rw [←Nat.add_mod, Nat.sub_add_cancel hq_pos] at h10
        norm_num at h10
        have h15 : 2 ∣ q := Nat.modEq_zero_iff_dvd.mp h10.symm
        cases' Nat.Prime.eq_one_or_self_of_dvd hpq _ h15 with h16 h16
        · norm_num at h16
        · exact h16.symm
      · have h14 := Nat.mod_lt p zero_lt_two
        rw [h] at h14
        exact (not_lt_zero' (Nat.succ_lt_succ_iff.mp (Nat.succ_lt_succ_iff.mp h14))).elim

  have h11 : p = 3 := by
    have h20 : b - a = 1 := by rw [h9] at h8; exact h8.symm
    have h22 : a ≤ b := Nat.le_of_lt hba
    have h21 : b = 1 + a := Nat.eq_add_of_sub_eq h22 h20
    have h23 : p = 2 * a + 1 := by
      rw [h21, add_assoc, ←Nat.two_mul, add_comm] at h7
      exact h7.symm
    rw [h23, h9, Nat.succ_inj'] at ha
    have h30 : a = 1 := by
      zify at ha
      have h26 : ((a:ℤ) - 1)^2 = 0 := by linear_combination ha
      have h27 : (a:ℤ) - 1 = 0 := pow_eq_zero h26
      have h28 : (a:ℤ) = 1 := Int.sub_eq_zero.mp h27
      exact Int.ofNat_inj.mp h28
    rw [h30] at h23
    exact h23

  simp only [h9, h11]
