/-
Copyright (c) 2023 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Zhiyi Luo
-/

import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Prime

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 2003, Problem 6

Let p be a prime number. Prove that there exists a prime number q
such that for every integer n, the number nᵖ - p is not divisible
by q.
-/

namespace Imo2003P6

snip begin

lemma exists_prime_mod_m_ne_1_and_dvd
    {n m : Nat} (npos : n ≠ 0) (hn : n % m ≠ 1) (hm : m ≠ 1)
    : ∃ p : Nat, p.Prime ∧ p ∣ n ∧ p % m ≠ 1 := by
  by_contra! h
  let l := n.primeFactorsList
  have : ∀ p ∈ l, p % m = 1 := by
    intro p pl
    exact h _ (Nat.prime_of_mem_primeFactorsList pl) (Nat.dvd_of_mem_primeFactorsList pl)
  have : n % m = 1 := calc n % m
    _ = l.prod % m := by rw [Nat.prod_primeFactorsList npos]
    _ = (l.map (fun p ↦ p % m)).prod % m := List.prod_nat_mod l m
    _ = (l.map (fun p ↦ 1)).prod % m := by rw [List.map_inj_left.mpr this]
    _ = 1 % m := by rw [List.prod_eq_one (by simp)]
    _ = 1 := Nat.one_mod_eq_one.mpr hm
  contradiction

snip end

problem imo2003_p6 (p : ℕ) (hp : p.Prime) :
    ∃ q : ℕ, q.Prime ∧ ∀ n, ¬((q : ℤ) ∣ (n : ℤ)^p - (p : ℤ)) := by
  -- Direct translation of https://artofproblemsolving.com/community/c6h98p279

  open Finset in

  rcases Nat.Prime.eq_two_or_odd hp with rfl | p_odd

  · -- p = 2
    use 5
    constructor
    · exact Nat.prime_five

    intro n
    by_contra hdvd

    let m := n % 5
    have : 0 ≤ m := Int.emod_nonneg n (by norm_num)
    have : m < 5 := Int.emod_lt_of_pos n (by norm_num)

    have : 2 ≡ m ^ 2 [ZMOD 5] := calc
      2 ≡ n ^ 2 [ZMOD 5] := Int.modEq_iff_dvd.mpr hdvd
      _ ≡ m ^ 2 [ZMOD 5] := Int.ModEq.pow 2 (Int.mod_modEq n 5).symm
    have : 5 ∣ m ^ 2 - 2 := Int.dvd_self_sub_of_emod_eq (id (Int.ModEq.symm this))

    interval_cases m <;> norm_num at this

  -- p > 2
  let N := ∑ i ∈ range p, p^i
  have N_nz : N ≠ 0 := by
    apply Nat.ne_zero_iff_zero_lt.mpr
    apply sum_pos
    · exact fun _ _ ↦ Nat.pow_pos (Nat.Prime.pos hp)
    exact nonempty_range_iff.mpr hp.ne_zero

  have p_ge_3 : p - 1 > 1 := by
    by_contra h
    simp only [gt_iff_lt, not_lt, tsub_le_iff_right, Nat.reduceAdd] at h
    interval_cases p
    · norm_num at hp
    · norm_num at hp
    · norm_num at p_odd

  have N_mod_p_ne_1 : N % (p ^ 2) ≠ 1 := by
    have : (p + 1) % (p ^ 2) = p + 1 := by
      have : p + 1 < p ^ 2 := by
        suffices 1 < p ^ 2 - p by exact Nat.add_lt_of_lt_sub' this
        calc
          1 < p * (p - 1) := by
            apply Nat.one_lt_mul_iff.mpr
            exact ⟨Nat.Prime.pos hp, by simp [hp.one_lt], Or.inl hp.one_lt⟩
          _ = p ^ 2 - p := by simp [Nat.pow_two, Nat.mul_sub]
      exact Nat.mod_eq_of_lt this
    have : ∀ m ≥ 2, (∑ i ∈ range m, p^i) % (p ^ 2) = p + 1 := by
      intro m hm
      cases' m with m; norm_num at hm
      cases' m with m; norm_num at hm
      induction' m with m ih
      · simpa
      simp at *
      rw [sum_range_succ, Nat.add_mod, ih]
      rw [Nat.mod_eq_zero_of_dvd (pow_dvd_pow p (by simp))]
      simpa
    rw [this _ (Nat.Prime.two_le hp)]
    simp [Nat.Prime.ne_zero hp]

  have p_sq_ne_1 : p ^ 2 ≠ 1 := by
    refine Ne.symm (Nat.ne_of_lt ?_)
    apply one_lt_pow₀ (Nat.Prime.one_lt hp) (by norm_num)

  rcases exists_prime_mod_m_ne_1_and_dvd
    N_nz N_mod_p_ne_1 p_sq_ne_1 with ⟨q, ⟨hq, hqN, h3⟩⟩

  have q_dvd_pp_1 : q ∣ p^p - 1 := calc
    q ∣ N := hqN
    _ ∣ p^p - 1 := by
      use p - 1
      simp [N]
      apply Nat.add_one_inj.mp
      have : p^p - 1 + 1 = p^p := Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.pos)
      rw [this]
      have : p = p - 1 + 1 := (Nat.succ_pred_prime hp).symm
      nth_rw 1 [this]; nth_rw 4 [this]
      rw [geom_sum_mul_add (p - 1) p]

  use q
  constructor
  · exact hq

  intro n hn

  have np_congr_p : (n : ZMod q) ^ p = p := by
    rw [← Int.cast_pow, ← AddCommGroupWithOne.intCast_ofNat p]
    rw [← (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr hn]

  have pp_congr_1 : (p : ZMod q) ^ p = (1 : ZMod q) := by
    rw [← Nat.cast_pow, ← Nat.cast_one]
    apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
    apply Eq.symm
    apply (Nat.modEq_iff_dvd' _).mpr
    · exact q_dvd_pp_1
    exact hp.one_le.trans (Nat.le_self_pow hp.ne_zero _)

  have : (n : ZMod q) ^ (p ^ 2) = 1 := by
    rw [Nat.pow_two, pow_mul]
    rw [np_congr_p, pp_congr_1]

  let d := orderOf (n : ZMod q)

  have : d ∣ p ^ 2 := orderOf_dvd_of_pow_eq_one this
  rcases (Nat.dvd_prime_pow hp).mp this with ⟨k, ⟨k_le, d_eq_pk⟩⟩
  rcases Nat.lt_or_eq_of_le k_le with hk | rfl

  · -- k < 2
    have : (n : ZMod q) ^ p = ((1 : ℕ) : ZMod q) := by
      rw [Nat.cast_one]
      interval_cases k
      all_goals simp at d_eq_pk
      · -- k = 0
        simp [orderOf_eq_one_iff.mp d_eq_pk]
      · -- k = 1
        rw [← d_eq_pk]
        exact pow_orderOf_eq_one _
    have : (p : ZMod q) = ((1 : ℕ) : ZMod q) := by
      rw [← Nat.cast_one]
      exact (np_congr_p.symm).trans this
    have : p ≡ 1 [MOD q] := (ZMod.natCast_eq_natCast_iff _ _ _).mp this
    have q_dvd_p_1 : q ∣ p - 1 := (Nat.modEq_iff_dvd' hp.one_le).mp (id (Nat.ModEq.symm this))

    have one_mod_p_1 : 1 % (p - 1) = 1 :=
      (Nat.mod_eq_iff_lt (by omega)).mpr p_ge_3
    have p_mod_p_1 : p % (p - 1) = 1 := by
      rw [Nat.mod_eq_sub_mod]
      · have : p - (p - 1) = 1 := Nat.sub_sub_self hp.one_le
        simp [this, one_mod_p_1]
      · exact Nat.sub_le _ _
    have : N % (p - 1) = 1 := calc N % (p - 1)
      _ = (∑ i ∈ range p, (p^i) % (p - 1)) % (p - 1) := Finset.sum_nat_mod _ _ _
      _ = (∑ i ∈ range p, 1) % (p - 1) := by
        congr; funext i
        simp [Nat.pow_mod, one_mod_p_1, p_mod_p_1]
      _ = 1 := by simp [p_mod_p_1]
    have : Nat.gcd N (p - 1) = 1 :=
      calc Nat.gcd N (p - 1)
        _ = Nat.gcd (N % (p - 1)) (p - 1) := (Nat.mod_modEq _ _).symm.gcd_eq
        _ = 1 := by
          rw [this]
          exact Nat.gcd_one_left _

    have : q ≤ 1 := by
      apply Nat.le_of_dvd (by norm_num)
      rw [← this]
      exact Nat.dvd_gcd hqN q_dvd_p_1

    linarith [this, hq.one_lt]

  -- k = 2
  rcases eq_zero_or_neZero (n : ZMod q) with hn0 | hn0
  · -- n = 0 (mod q)
    have q_dvd_p : (p : ZMod q) = 0 :=
      calc (p : ZMod q)
        _ = (n : ZMod q) ^ p := by rw [np_congr_p]
        _ = 0 := by
          rw [hn0, zero_pow (Nat.Prime.ne_zero hp)]
    rw [ZMod.natCast_eq_zero_iff] at q_dvd_p

    have : N % p = 1 := calc N % p
      _ = (∑ i ∈ range p, (p^i) % p) % p := Finset.sum_nat_mod _ _ _
      _ = (∑ i ∈ range (p - 1 + 1), (p^i) % p) % p := by
        nth_rw 1 [← Nat.succ_pred_prime hp]
        simp
      _ = (∑ i ∈ range (p - 1), p^(i+1) % p + 1) % p := by
        simp [Finset.sum_range_succ']
      _ = (∑ i ∈ range (p - 1), 0 + 1) % p := by
        congr; funext i
        apply Nat.mod_eq_zero_of_dvd
        exact Dvd.intro_left (p.pow i) rfl
      _ = 1 := by
        simp
        rw [Nat.one_mod_eq_one.mpr (Nat.Prime.ne_one hp)]
    have : Nat.gcd N p = 1 :=
      calc Nat.gcd N p
        _ = Nat.gcd (N % p) p := (Nat.mod_modEq _ _).symm.gcd_eq
        _ = 1 := by rw [this, Nat.gcd_one_left]

    have : q ≤ 1 := by
      apply Nat.le_of_dvd (by norm_num)
      rw [← this]
      exact Nat.dvd_gcd hqN q_dvd_p

    linarith [this, hq.one_lt]

  · -- n ≠ 0 (mod q)
    have : p ^ 2 ∣ q - 1 := by
      rw [← d_eq_pk]
      apply orderOf_dvd_of_pow_eq_one
      apply @ZMod.pow_card_sub_one_eq_one _ (Fact.mk hq) _ hn0.out
    have : (q - 1) % (p ^ 2) = 0 := Nat.mod_eq_zero_of_dvd this
    have : q % (p ^ 2) = 1 := by
      rw [← Nat.succ_pred_prime hq]
      simp [Nat.add_mod, this]
      exact Nat.one_mod_eq_one.mpr p_sq_ne_1
    contradiction


end Imo2003P6
