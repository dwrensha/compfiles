/-
Copyright (c) 2025 The Compfiles Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elan Roth
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra, .NumberTheory] }

/-!
# International Mathematical Olympiad 2000, Problem 5

Does there exist a positive integer n such that n has exactly
2000 distinct prime divisors and n divides 2ⁿ + 1?

-/

namespace Imo2000P5

snip begin

open Nat Finset

lemma dvd_pow_add_one_of_dvd_add_one {a m : ℕ} (h : m ∣ a + 1) {p : ℕ} (hp : Odd p) :
    m ∣ a ^ p + 1 := by
  exact dvd_trans h (by simpa using hp.nat_add_dvd_pow_add_pow a 1)

lemma extend_divisibility {n : ℕ} (hn : n ∣ 2 ^ n + 1) (p : ℕ) (hp : Nat.Prime p)
    (hpodd : p ≠ 2) (hpdvd : p ∣ 2 ^ n + 1) :
    n * p ∣ 2 ^ (n * p) + 1 := by
  have h_even : ∃ k : ℕ, 2 ^ (n * p) + 1 = (2 ^ n + 1) * (∑ i ∈ Finset.range p, (-1 : ℤ) ^ i * (2 ^ n) ^ i) := by
    rcases Nat.even_or_odd' p with ⟨ c, rfl | rfl ⟩ <;> norm_num [pow_add, pow_mul, ← mul_pow] at *;
    · simp_all +decide [Nat.prime_mul_iff];
    · have := geom_sum_mul_neg (-2 ^ n : ℤ) (2 * c + 1) ; ring_nf at * ; aesop;
  have h_div : (p : ℤ) ∣ ∑ i ∈ Finset.range p, (-1 : ℤ) ^ i * (2 ^ n) ^ i := by
    haveI := Fact.mk hp; simp_all +decide [← ZMod.intCast_zmod_eq_zero_iff_dvd] ;
    simp_all +decide [← ZMod.natCast_eq_zero_iff];
    simp_all +decide [← mul_pow, add_eq_zero_iff_eq_neg];
  have h_mul_dvd : (n * p : ℤ) ∣ (2 ^ n + 1) * (∑ i ∈ Finset.range p, (-1 : ℤ) ^ i * (2 ^ n) ^ i) := by
    exact mul_dvd_mul (mod_cast hn) h_div;
  exact_mod_cast h_even.choose_spec.symm ▸ h_mul_dvd

lemma two_pow_add_one_gt (n : ℕ) : n < 2 ^ n + 1 := by
  have : n < 2 ^ n := Nat.lt_two_pow_self
  omega

lemma two_pow_add_one_odd {n : ℕ} (hn : 0 < n) : ¬ 2 ∣ (2 ^ n + 1) := by
  intro ⟨k, hk⟩
  have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 hn.ne'
  omega

lemma pow_mul_gt (n q : ℕ) (hn : 3 ≤ n) (hq : 3 ≤ q) :
    q * (2 ^ n + 1) < 2 ^ (n * q) + 1 := by
  have h_ineq : q * (2 ^ n + 1) ≤ q * 2 ^ (n + 1) := by
    exact Nat.mul_le_mul_left _ (by ring_nf; linarith [Nat.pow_le_pow_right two_pos hn]);
  have h_ineq2 : q * 2 ^ (n + 1) ≤ 2 ^ (q + n + 1) := by
    ring_nf at *
    gcongr
    linarith [show q ≤ 2 ^ q by
               exact le_of_lt (Nat.recOn q (by norm_num) fun n ihn => Nat.lt_two_pow_self)]
  refine lt_of_le_of_lt h_ineq (lt_of_le_of_lt h_ineq2 ?_);
  exact Nat.lt_succ_of_le (pow_le_pow_right₀ (by decide) (by nlinarith))

lemma quotient_not_dvd_of_ne {n q : ℕ} {p : ℕ} (hp : Nat.Prime p) (_hpodd : p ≠ 2)
    (hq_prime : Nat.Prime q) (hq_odd : q ≠ 2)
    (hpq : p ≠ q) (hpdvd : p ∣ 2 ^ n + 1) (_hdvd : (2 ^ n + 1) ∣ (2 ^ (n * q) + 1)) :
    ¬ p ∣ (2 ^ (n * q) + 1) / (2 ^ n + 1) := by
  have h_phi : (2 ^ (n * q) + 1) / (2 ^ n + 1) ≡ q [ZMOD p] := by
    have h_phi : (∑ i ∈ Finset.range q, (-1 : ℤ) ^ i * (2 ^ n) ^ (q - 1 - i)) ≡ q [ZMOD p] := by
      have h_phi : (∑ i ∈ Finset.range q, (-1 : ℤ) ^ i * (2 ^ n) ^ (q - 1 - i)) ≡ (∑ i ∈ Finset.range q, (-1 : ℤ) ^ i * (-1) ^ (q - 1 - i)) [ZMOD p] := by
        exact Int.ModEq.sum fun i hi => Int.ModEq.mul_left _ <| Int.ModEq.pow _ <| Int.ModEq.symm <| Int.modEq_of_dvd <| by simpa [← Int.natCast_dvd_natCast] using hpdvd;
      convert h_phi using 1;
      simp +decide [← pow_add, add_comm, ← Finset.sum_range_reflect];
      cases hq_prime.eq_two_or_odd' <;> simp_all +decide [Nat.even_sub hq_prime.pos];
    convert h_phi using 1;
    rw [Int.ediv_eq_of_eq_mul_right] <;> norm_cast ; norm_num [pow_mul];
    have := geom_sum₂_mul (-1 : ℤ) (2 ^ n) q; simp_all +decide [mul_comm] ;
    linarith [show (-1 : ℤ) ^ q = -1 from by rw [neg_one_pow_eq_pow_mod_two] ; norm_num [hq_prime.eq_two_or_odd.resolve_left hq_odd]];
  rw [← Int.natCast_dvd_natCast]
  simp only [Int.ModEq] at h_phi
  refine fun h => hpq ?_
  have := Int.dvd_of_emod_eq_zero (h_phi.symm.trans <| Int.emod_eq_zero_of_dvd h)
  norm_cast at this
  exact (Nat.prime_dvd_prime_iff_eq hp hq_prime).mp this

lemma quotient_val_q {n q : ℕ} (hq_prime : Nat.Prime q) (hq_odd : q ≠ 2)
    (hqdvd : q ∣ 2 ^ n + 1) (_hn_pos : 0 < n)
    (hdvd : (2 ^ n + 1) ∣ (2 ^ (n * q) + 1)) :
    emultiplicity q ((2 ^ (n * q) + 1) / (2 ^ n + 1)) = 1 := by
  haveI : Fact q.Prime := ⟨hq_prime⟩
  have hnum_pos : 0 < 2 ^ (n * q) + 1 := by positivity
  have hden_pos : 0 < 2 ^ n + 1 := by positivity
  have hnum_ne : 2 ^ (n * q) + 1 ≠ 0 := Nat.ne_of_gt hnum_pos
  have hden_fin : emultiplicity q (2 ^ n + 1) ≠ ⊤ := by
    exact finiteMultiplicity_iff_emultiplicity_ne_top.1 <|
      Nat.finiteMultiplicity_iff.mpr ⟨hq_prime.ne_one, hden_pos⟩
  have hq_fin : emultiplicity q q ≠ ⊤ := by
    exact finiteMultiplicity_iff_emultiplicity_ne_top.1 <|
      Nat.finiteMultiplicity_iff.mpr ⟨hq_prime.ne_one, hq_prime.pos⟩
  have h_emultiplicity : emultiplicity q (2 ^ (n * q) + 1) = emultiplicity q (2 ^ n + 1) + 1 := by
    have h_emultiplicity_pow : emultiplicity q ((2 ^ n) ^ q + 1 ^ q) = emultiplicity q (2 ^ n + 1) + emultiplicity q q := by
      apply_rules [Nat.emultiplicity_pow_add_pow];
      · exact hq_prime.odd_of_ne_two hq_odd;
      · exact mt hq_prime.dvd_of_dvd_pow <| Nat.not_dvd_of_pos_of_lt Nat.zero_lt_two <| lt_of_le_of_ne hq_prime.two_le <| Ne.symm hq_odd;
      · exact hq_prime.odd_of_ne_two hq_odd;
    simpa [pow_mul] using h_emultiplicity_pow.trans (by rw [Nat.Prime.emultiplicity_self hq_prime])
  have hnum_val : padicValNat q (2 ^ (n * q) + 1) = padicValNat q (2 ^ n + 1) + 1 := by
    have h := congrArg ENat.toNat h_emultiplicity
    rw [ENat.toNat_add hden_fin (by simp), Nat.toNat_emultiplicity, Nat.toNat_emultiplicity] at h
    simpa using h
  have hquot_ne : ((2 ^ (n * q) + 1) / (2 ^ n + 1)) ≠ 0 := by
    exact Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd hnum_pos hdvd) hden_pos)
  calc
    emultiplicity q ((2 ^ (n * q) + 1) / (2 ^ n + 1))
        = padicValNat q ((2 ^ (n * q) + 1) / (2 ^ n + 1)) := by
          symm
          exact padicValNat_eq_emultiplicity (p := q) hquot_ne
    _ = 1 := by
          rw [padicValNat.div_of_dvd hdvd, hnum_val]
          have hsub : padicValNat q (2 ^ n + 1) + 1 - padicValNat q (2 ^ n + 1) = 1 := by
            omega
          simp [hsub]

lemma exists_new_prime_factor {n q : ℕ} (hn : 3 ≤ n)
    (hq_prime : Nat.Prime q) (hq_odd : q ≠ 2)
    (hqdvd : q ∣ 2 ^ n + 1) :
    ∃ r, Nat.Prime r ∧ r ∣ 2 ^ (n * q) + 1 ∧ ¬ r ∣ (2 ^ n + 1) := by
  set Φ := (2 ^ (n * q) + 1) / (2 ^ n + 1) with hΦ_def
  have hΦ_pos : 0 < Φ := by
    norm_num +zetaDelta at *;
    exact pow_le_pow_right₀ (by decide) (by nlinarith [hq_prime.two_le])
  have hΦ_gt_q : Φ > q := by
    refine' Nat.le_div_iff_mul_le (Nat.succ_pos _) |>.2 _;
    rw [pow_mul];
    rcases q with (_ | _ | q) <;> simp_all +decide [pow_succ];
    nlinarith [Nat.mul_le_mul_left (2 ^ n) (show (2 ^ n) ^ q ≥ q + 1 from Nat.recOn q (by norm_num) fun q ih => by rw [pow_succ'] ; nlinarith [Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hn]), Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hn, Nat.mul_le_mul_left (2 ^ n) (show (2 ^ n) ^ q ≥ 1 from Nat.one_le_pow _ _ (by norm_num))]
  have hΦ_dvd : (2 ^ n + 1) * Φ = 2 ^ (n * q) + 1 := by
    rw [Nat.mul_div_cancel'] ; exact_mod_cast by have := Nat.odd_iff.mpr (show (q : ℕ) % 2 = 1 from hq_prime.eq_two_or_odd.resolve_left hq_odd) ; simpa [*, Nat.pow_mul] using this.nat_add_dvd_pow_add_pow _ 1;
  have h_not_dvd : ∀ p : ℕ, Nat.Prime p → p ≠ q → p ∣ 2 ^ n + 1 → ¬ p ∣ Φ := by
    intros p hp hpq hpdiv hpdivΦ
    apply quotient_not_dvd_of_ne hp (by
    rintro rfl; simp_all +decide [← even_iff_two_dvd, parity_simps] ;) hq_prime hq_odd hpq hpdiv (by
    exact hΦ_dvd ▸ dvd_mul_right _ _) hpdivΦ;
  have h_emultiplicity_q : emultiplicity q Φ = 1 := by
    apply quotient_val_q hq_prime hq_odd hqdvd (by linarith) (by
    exact dvd_of_mul_right_eq _ hΦ_dvd);
  obtain ⟨m, hm⟩ : ∃ m : ℕ, Φ = q * m ∧ ¬ q ∣ m := by
    haveI : Fact q.Prime := ⟨hq_prime⟩
    have hΦ_ne : Φ ≠ 0 := by exact Nat.ne_of_gt hΦ_pos
    have hΦ_val : padicValNat q Φ = 1 := by
      simpa [Nat.toNat_emultiplicity] using congrArg ENat.toNat h_emultiplicity_q
    have hq_dvd_Φ : q ∣ Φ := by
      exact dvd_of_one_le_padicValNat (by simp [hΦ_val])
    have hq_sq_not_dvd_Φ : ¬ q ^ 2 ∣ Φ := by
      rw [padicValNat_dvd_iff_le (p := q) hΦ_ne, not_le]
      simp [hΦ_val]
    rcases hq_dvd_Φ with ⟨m, hm⟩
    refine ⟨m, hm, ?_⟩
    intro hm'
    apply hq_sq_not_dvd_Φ
    rcases hm' with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [Nat.pow_two, hm, ht, Nat.mul_assoc, Nat.mul_left_comm q q, ← Nat.mul_assoc]
  have h_coprime : ∀ p : ℕ, Nat.Prime p → p ∣ 2 ^ n + 1 → ¬ p ∣ m := by
    intro p pp dp; specialize h_not_dvd p pp; by_cases hpq : p = q <;> simp_all +decide ;
    exact fun h => h_not_dvd <| hΦ_def ▸ dvd_mul_of_dvd_right h _;
  obtain ⟨r, hr⟩ : ∃ r : ℕ, Nat.Prime r ∧ r ∣ m := by
    exact Nat.exists_prime_and_dvd (by nlinarith [hq_prime.two_le]);
  exact ⟨ r, hr.1, dvd_trans hr.2 (hm.1.symm ▸ dvd_mul_left _ _) |> fun x => x.trans (hΦ_dvd ▸ dvd_mul_left _ _), fun h => h_coprime r hr.1 h hr.2 ⟩

lemma increase_prime_factors (n : ℕ) (hn : 0 < n) (hd : n ∣ 2 ^ n + 1) :
    ∃ m, 0 < m ∧ m ∣ 2 ^ m + 1 ∧ n.primeFactors.card < m.primeFactors.card := by
  by_cases hn3 : n ≥ 3;
  · obtain ⟨q, hq_prime, hq_odd, hqdvd⟩ : ∃ q, Nat.Prime q ∧ q ∣ 2 ^ n + 1 ∧ q ≠ 2 := by
      exact ⟨ Nat.minFac (2 ^ n + 1), Nat.minFac_prime (by norm_num), Nat.minFac_dvd _, fun h => by simp_all +decide [← even_iff_two_dvd, parity_simps] ⟩;
    by_cases hq : q ∣ n <;> simp_all +decide;
    · obtain ⟨r, hr_prime, hr_dvd⟩ : ∃ r, Nat.Prime r ∧ r ∣ 2 ^ (n * q) + 1 ∧ ¬ r ∣ (2 ^ n + 1) := by
        apply exists_new_prime_factor hn3 hq_prime hqdvd hq_odd;
      set n' := n * q
      set m := n' * r
      use m
      have hm_pos : 0 < m := by
        exact Nat.mul_pos (Nat.mul_pos hn hq_prime.pos) hr_prime.pos
      have hm_div : m ∣ 2 ^ m + 1 := by
        apply_rules [extend_divisibility];
        · rintro rfl; simp_all +decide [← even_iff_two_dvd, parity_simps] ;
          aesop;
        · exact hr_dvd.1
      have hm_prime_factors : m.primeFactors = n.primeFactors ∪ {r} := by
        rw [Nat.primeFactors_mul, Nat.primeFactors_mul] <;> aesop
      have hm_card : m.primeFactors.card > n.primeFactors.card := by
        have hr_not_in_n : r∉n.primeFactors := by
          exact fun h => hr_dvd.2 <| dvd_trans (Nat.dvd_of_mem_primeFactors h) hd |> fun x => by simpa [← ZMod.natCast_eq_zero_iff] using x;
        exact (by
        grind)
      exact ⟨hm_pos, hm_div, hm_card⟩;
    · refine' ⟨ n * q, Nat.mul_pos hn hq_prime.pos, _, _ ⟩;
      · convert extend_divisibility hd q hq_prime hqdvd hq_odd using 1;
      · rw [Nat.primeFactors_mul] <;> aesop;
  · interval_cases n <;> simp_all +decide;
    exists 3

theorem exists_dvd_two_pow_add_one (k : ℕ) :
    ∃ n : ℕ, 0 < n ∧ n.primeFactors.card = k ∧ n ∣ 2 ^ n + 1 := by
  induction' k using Nat.strong_induction_on with k ih;
  by_cases hk : k = 0 ∨ k = 1;
  · cases hk <;> [exact ⟨ 1, by norm_num, by norm_num [‹k = 0›], by norm_num [‹k = 0›] ⟩ ; exact ⟨ 3, by norm_num, by norm_num [‹k = 1›], by norm_num [‹k = 1›] ⟩];
  · obtain ⟨ n, hn₁, hn₂, hn₃ ⟩ := ih (k - 1) (Nat.sub_lt (Nat.pos_of_ne_zero (by tauto)) zero_lt_one) ; rcases k with (_ | _ | k) <;> simp_all +decide;
    obtain ⟨ q, hq_prime, hq_dvd ⟩ : ∃ q : ℕ, Nat.Prime q ∧ q ∣ (2 ^ n + 1) / n := by
      refine Nat.exists_prime_and_dvd ?_;
      nlinarith [Nat.div_mul_cancel hn₃, two_pow_add_one_gt n];
    by_cases hq : q ∣ n <;> simp_all +decide [Nat.dvd_div_iff_mul_dvd];
    · obtain ⟨ r, hr_prime, hr_dvd ⟩ : ∃ r : ℕ, r.Prime ∧ r ∣ 2 ^ (n * q) + 1 ∧ ¬ r ∣ 2 ^ n + 1 := by
        apply exists_new_prime_factor;
        · contrapose! hn₂; interval_cases n <;> simp_all +decide ;
        · assumption;
        · rintro rfl; have := congr_arg Even hq_dvd.choose_spec; norm_num [hn₁.ne', parity_simps] at this;
        · exact dvd_of_mul_left_dvd hq_dvd;
      use n * q * r; simp_all +decide ; (
      have h_prime_factors : (n * q * r).primeFactors = n.primeFactors ∪ {r} := by
        have h_prime_factors_nq : (n * q).primeFactors = n.primeFactors := by
          rw [Nat.primeFactors_mul, Finset.union_eq_left.mpr] <;> aesop
        generalize_proofs at *; (
        rw [Nat.primeFactors_mul, h_prime_factors_nq] <;> aesop;)
      generalize_proofs at *; (
      have h_div : n * q * r ∣ 2 ^ (n * q * r) + 1 := by
        have h_div : n * q ∣ 2 ^ (n * q) + 1 := by
          exact dvd_trans hq_dvd (by have := Nat.Prime.odd_of_ne_two hq_prime (by rintro rfl; exact absurd (dvd_trans (dvd_mul_left _ _) hq_dvd) (by norm_num [Nat.dvd_add_right (dvd_pow_self _ hn₁.ne')])) ; simpa [*, pow_mul] using this.nat_add_dvd_pow_add_pow _ 1) ;
        generalize_proofs at *; (
        convert Nat.Coprime.mul_dvd_of_dvd_of_dvd _ _ _ using 1 <;> simp_all +decide [Nat.coprime_mul_iff_left];
        · exact ⟨ Nat.Coprime.symm <| hr_prime.coprime_iff_not_dvd.mpr fun h => hr_dvd.2 <| dvd_trans h hn₃, Nat.Coprime.symm <| hr_prime.coprime_iff_not_dvd.mpr fun h => hr_dvd.2 <| dvd_trans h <| dvd_of_mul_left_dvd hq_dvd ⟩ ;
        · exact dvd_trans h_div (by have := Nat.Prime.odd_of_ne_two hr_prime (by rintro rfl; simp_all +decide [← even_iff_two_dvd, parity_simps]) ; simpa [*, pow_mul] using this.nat_add_dvd_pow_add_pow _ 1) ;
        · haveI := Fact.mk hr_prime; simp_all +decide [← ZMod.natCast_eq_zero_iff, pow_mul] ;)
      generalize_proofs at *; (
      simp_all +decide;
      exact ⟨ ⟨ hq_prime.pos, hr_prime.pos ⟩, by rw [Finset.card_insert_of_notMem (fun h => hr_dvd.2 <| Nat.dvd_trans (Nat.dvd_of_mem_primeFactors h) hn₃), hn₂] ⟩ ;)));
    · refine' ⟨ n * q, Nat.mul_pos hn₁ hq_prime.pos, _, _ ⟩;
      · rw [Nat.primeFactors_mul, Finset.card_union] <;> aesop;
      · convert extend_divisibility hn₃ q hq_prime (by
          rintro rfl; replace hq_dvd := congr_arg Even hq_dvd.choose_spec; simp_all +decide [parity_simps] ;) (by
          exact dvd_of_mul_left_dvd hq_dvd) using 1

snip end

determine solution : Bool := true

problem imo2000P5 :
    ∃ n, 0 < n ∧ n.primeFactors.card = 2000 ∧ n ∣ 2 ^ n + 1
    ↔ solution := by
  obtain ⟨n, hn, hcard, hdvd⟩ := exists_dvd_two_pow_add_one 2000
  refine ⟨n, ?_⟩
  simp only [solution, iff_true]
  exact ⟨hn, hcard, hdvd⟩

end Imo2000P5
