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

lemma extend_divisibility {n : ℕ} (hn : n ∣ 2 ^ n + 1) (p : ℕ) (hp : Nat.Prime p)
    (hpodd : p ≠ 2) (hpdvd : p ∣ 2 ^ n + 1) :
    n * p ∣ 2 ^ (n * p) + 1 := by
  have hp_odd : Odd p := hp.odd_of_ne_two hpodd
  have h_factor : ((2 ^ (n * p) + 1 : ℕ) : ℤ) =
      (2 ^ n + 1) * ∑ i ∈ Finset.range p, (-1 : ℤ) ^ i * (2 ^ n) ^ i := by
    have h := geom_sum_mul (-(2 : ℤ) ^ n) p
    have hh : (∑ i ∈ Finset.range p, (-(2 : ℤ) ^ n) ^ i) =
        ∑ i ∈ Finset.range p, (-1) ^ i * (2 ^ n) ^ i :=
      Finset.sum_congr rfl (fun _ _ => by ring)
    rw [hh] at h
    have hodd : (-(2 : ℤ) ^ n) ^ p = -(2 ^ n) ^ p := hp_odd.neg_pow _
    push_cast
    rw [pow_mul]
    linarith
  have h_div : (p : ℤ) ∣ ∑ i ∈ Finset.range p, (-1 : ℤ) ^ i * (2 ^ n) ^ i := by
    have h_2n : (2 ^ n : ℤ) ≡ -1 [ZMOD p] := by
      have h : ((2 ^ n + 1 : ℤ)) ≡ 0 [ZMOD p] :=
        Int.modEq_zero_iff_dvd.mpr (by exact_mod_cast hpdvd)
      simpa using h.sub_right 1
    have h_sum : (∑ i ∈ Finset.range p, (-1 : ℤ) ^ i * (2 ^ n) ^ i) ≡ 0 [ZMOD p] := by
      calc ∑ i ∈ Finset.range p, (-1 : ℤ) ^ i * (2 ^ n) ^ i
          ≡ ∑ i ∈ Finset.range p, (-1 : ℤ) ^ i * (-1) ^ i [ZMOD p] :=
            Int.ModEq.sum fun _ _ => (Int.ModEq.pow _ h_2n).mul_left _
        _ = (p : ℤ) := by simp [← mul_pow]
        _ ≡ 0 [ZMOD p] := Int.modEq_zero_iff_dvd.mpr (dvd_refl _)
    exact Int.modEq_zero_iff_dvd.mp h_sum
  have h_mul_dvd : (n * p : ℤ) ∣ ((2 ^ (n * p) + 1 : ℕ) : ℤ) :=
    h_factor ▸ mul_dvd_mul (mod_cast hn) h_div
  exact_mod_cast h_mul_dvd

lemma quotient_not_dvd_of_ne {n q : ℕ} {p : ℕ} (hp : Nat.Prime p)
    (hq_prime : Nat.Prime q) (hq_odd : q ≠ 2)
    (hpq : p ≠ q) (hpdvd : p ∣ 2 ^ n + 1) :
    ¬ p ∣ (2 ^ (n * q) + 1) / (2 ^ n + 1) := by
  set ψ : ℤ := ∑ i ∈ Finset.range q, (-1) ^ i * (2 ^ n) ^ i with hψ_def
  have hq_odd' : Odd q := hq_prime.odd_of_ne_two hq_odd
  have h_factor : ((2 ^ (n * q) + 1 : ℕ) : ℤ) = (2 ^ n + 1) * ψ := by
    have h := geom_sum_mul (-(2 : ℤ) ^ n) q
    have hh : (∑ i ∈ Finset.range q, (-(2 : ℤ) ^ n) ^ i) = ψ :=
      Finset.sum_congr rfl (fun _ _ => by ring)
    rw [hh] at h
    have hodd : (-(2 : ℤ) ^ n) ^ q = -(2 ^ n) ^ q := hq_odd'.neg_pow _
    push_cast
    rw [pow_mul]
    linarith
  have h_2n : (2 ^ n : ℤ) ≡ -1 [ZMOD p] := by
    have : ((2 ^ n + 1 : ℤ)) ≡ 0 [ZMOD p] :=
      Int.modEq_zero_iff_dvd.mpr (by exact_mod_cast hpdvd)
    simpa using this.sub_right 1
  have hψ_mod : ψ ≡ q [ZMOD p] := by
    calc ψ ≡ ∑ i ∈ Finset.range q, (-1 : ℤ) ^ i * (-1) ^ i [ZMOD p] :=
            Int.ModEq.sum fun _ _ => (Int.ModEq.pow _ h_2n).mul_left _
      _ = (q : ℤ) := by simp [← mul_pow]
  have hdvd : (2 ^ n + 1) ∣ (2 ^ (n * q) + 1) := by
    simpa [pow_mul] using hq_odd'.nat_add_dvd_pow_add_pow (2 ^ n) 1
  have h_quot_eq : (((2 ^ (n * q) + 1) / (2 ^ n + 1) : ℕ) : ℤ) = ψ := by
    have hpos : (2 ^ n + 1 : ℤ) ≠ 0 := by positivity
    apply mul_left_cancel₀ hpos
    have h_nat : (2 ^ n + 1) * ((2 ^ (n * q) + 1) / (2 ^ n + 1)) = 2 ^ (n * q) + 1 :=
      Nat.mul_div_cancel' hdvd
    calc (2 ^ n + 1 : ℤ) * (((2 ^ (n * q) + 1) / (2 ^ n + 1) : ℕ) : ℤ)
        = (((2 ^ n + 1) * ((2 ^ (n * q) + 1) / (2 ^ n + 1)) : ℕ) : ℤ) := by push_cast; ring
      _ = ((2 ^ (n * q) + 1 : ℕ) : ℤ) := by exact_mod_cast h_nat
      _ = (2 ^ n + 1) * ψ := h_factor
  intro h
  apply hpq
  have hp_dvd_ψ : (p : ℤ) ∣ ψ := by
    rw [← h_quot_eq]; exact_mod_cast h
  have h_q_dvd : (p : ℤ) ∣ q :=
    Int.modEq_zero_iff_dvd.mp (hψ_mod.symm.trans (Int.modEq_zero_iff_dvd.mpr hp_dvd_ψ))
  exact (Nat.prime_dvd_prime_iff_eq hp hq_prime).mp (by exact_mod_cast h_q_dvd)

lemma quotient_val_q {n q : ℕ} (hq_prime : Nat.Prime q) (hq_odd : q ≠ 2)
    (hqdvd : q ∣ 2 ^ n + 1)
    (hdvd : (2 ^ n + 1) ∣ (2 ^ (n * q) + 1)) :
    emultiplicity q ((2 ^ (n * q) + 1) / (2 ^ n + 1)) = 1 := by
  have hden_pos : 0 < 2 ^ n + 1 := by positivity
  have hq_odd' : Odd q := hq_prime.odd_of_ne_two hq_odd
  have hq_not_dvd_pow : ¬ q ∣ 2 ^ n :=
    mt (fun h => (Nat.prime_dvd_prime_iff_eq hq_prime Nat.prime_two).mp
                  (hq_prime.dvd_of_dvd_pow h)) hq_odd
  have hden_fin : emultiplicity q (2 ^ n + 1) ≠ ⊤ :=
    finiteMultiplicity_iff_emultiplicity_ne_top.1 <|
      Nat.finiteMultiplicity_iff.mpr ⟨hq_prime.ne_one, hden_pos⟩
  have h_num : emultiplicity q (2 ^ (n * q) + 1) = emultiplicity q (2 ^ n + 1) + 1 := by
    have h := Nat.emultiplicity_pow_add_pow hq_prime hq_odd' hqdvd hq_not_dvd_pow hq_odd'
    simpa [pow_mul, Nat.Prime.emultiplicity_self hq_prime] using h
  have h_mul : emultiplicity q ((2 ^ n + 1) * ((2 ^ (n * q) + 1) / (2 ^ n + 1))) =
               emultiplicity q (2 ^ n + 1) + emultiplicity q ((2 ^ (n * q) + 1) / (2 ^ n + 1)) :=
    Nat.Prime.emultiplicity_mul hq_prime
  rw [Nat.mul_div_cancel' hdvd, h_num, add_comm _ 1,
      add_comm _ (emultiplicity q ((2 ^ (n * q) + 1) / (2 ^ n + 1)))] at h_mul
  exact (WithTop.add_right_cancel hden_fin h_mul).symm

lemma exists_new_prime_factor {n q : ℕ} (hn : 3 ≤ n)
    (hq_prime : Nat.Prime q) (hq_odd : q ≠ 2)
    (hqdvd : q ∣ 2 ^ n + 1) :
    ∃ r, Nat.Prime r ∧ r ∣ 2 ^ (n * q) + 1 ∧ ¬ r ∣ (2 ^ n + 1) := by
  set Φ := (2 ^ (n * q) + 1) / (2 ^ n + 1) with hΦ_def
  have hq3 : 3 ≤ q := by have := hq_prime.two_le; omega
  have hdvd : (2 ^ n + 1) ∣ (2 ^ (n * q) + 1) := by
    simpa [pow_mul] using (hq_prime.odd_of_ne_two hq_odd).nat_add_dvd_pow_add_pow (2 ^ n) 1
  have hΦ_pos : 0 < Φ :=
    Nat.div_pos (Nat.le_of_dvd (by positivity) hdvd) (by positivity)
  have hΦ_dvd : (2 ^ n + 1) * Φ = 2 ^ (n * q) + 1 := Nat.mul_div_cancel' hdvd
  have hΦ_gt_q : q < Φ := by
    rw [hΦ_def, Nat.lt_div_iff_mul_lt' hdvd]
    have h1 : (2 ^ n + 1) * q < 2 ^ (n + q + 1) := by
      have hq_pow : q < 2 ^ q := Nat.lt_two_pow_self
      have hn_pow : 2 ^ n + 1 ≤ 2 ^ (n + 1) := by
        rw [pow_succ]; nlinarith [Nat.one_le_two_pow (n := n)]
      calc (2 ^ n + 1) * q < 2 ^ (n + 1) * 2 ^ q :=
            Nat.mul_lt_mul_of_le_of_lt hn_pow hq_pow (by positivity)
        _ = 2 ^ (n + 1 + q) := by rw [← pow_add]
        _ = 2 ^ (n + q + 1) := by ring_nf
    have h2 : 2 ^ (n + q + 1) ≤ 2 ^ (n * q) :=
      Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    omega
  have h_not_dvd : ∀ p : ℕ, Nat.Prime p → p ≠ q → p ∣ 2 ^ n + 1 → ¬ p ∣ Φ :=
    fun p hp hpq hpdvd => quotient_not_dvd_of_ne hp hq_prime hq_odd hpq hpdvd
  have h_emultiplicity_q : emultiplicity q Φ = 1 :=
    quotient_val_q hq_prime hq_odd hqdvd (dvd_of_mul_right_eq _ hΦ_dvd)
  obtain ⟨m, hm_eq, hm_ndvd⟩ : ∃ m : ℕ, Φ = q * m ∧ ¬ q ∣ m := by
    have hq_dvd_Φ : q ∣ Φ := by
      have h : (1 : ℕ∞) ≤ emultiplicity q Φ := by rw [h_emultiplicity_q]
      simpa using pow_dvd_iff_le_emultiplicity.mpr h
    have hq_sq_not_dvd_Φ : ¬ q ^ 2 ∣ Φ := by
      rw [pow_dvd_iff_le_emultiplicity, h_emultiplicity_q]; decide
    obtain ⟨m, hm⟩ := hq_dvd_Φ
    exact ⟨m, hm, fun ⟨t, ht⟩ => hq_sq_not_dvd_Φ ⟨t, by rw [hm, ht]; ring⟩⟩
  have h_coprime : ∀ p : ℕ, Nat.Prime p → p ∣ 2 ^ n + 1 → ¬ p ∣ m := by
    intro p hp hp_dvd hp_dvd_m
    by_cases hpq : p = q
    · subst hpq; exact hm_ndvd hp_dvd_m
    · exact h_not_dvd p hp hpq hp_dvd (hm_eq ▸ dvd_mul_of_dvd_right hp_dvd_m _)
  have hm_ne_one : m ≠ 1 := fun h => by rw [h, mul_one] at hm_eq; omega
  obtain ⟨r, hr_prime, hr_dvd_m⟩ := Nat.exists_prime_and_dvd hm_ne_one
  refine ⟨r, hr_prime, ?_, fun h => h_coprime r hr_prime h hr_dvd_m⟩
  have h_r_dvd_Φ : r ∣ Φ := hm_eq ▸ dvd_mul_of_dvd_right hr_dvd_m _
  exact h_r_dvd_Φ.trans (hΦ_dvd ▸ dvd_mul_left _ _)

lemma increase_prime_factors (n : ℕ) (hn : 0 < n) (hd : n ∣ 2 ^ n + 1) :
    ∃ m, 0 < m ∧ m ∣ 2 ^ m + 1 ∧ m.primeFactors.card = n.primeFactors.card + 1 := by
  by_cases hn3 : 3 ≤ n
  · -- Pick the minimum prime factor q of 2^n + 1; it's odd since 2 ∤ 2^n + 1.
    have h_2n_pos : 1 < 2 ^ n + 1 := by have := Nat.one_le_two_pow (n := n); omega
    obtain ⟨q, hq_prime, hqdvd, hq_odd⟩ : ∃ q, Nat.Prime q ∧ q ∣ 2 ^ n + 1 ∧ q ≠ 2 := by
      refine ⟨Nat.minFac (2 ^ n + 1), Nat.minFac_prime h_2n_pos.ne',
             Nat.minFac_dvd _, fun h => ?_⟩
      have h2_dvd : (2 : ℕ) ∣ 2 ^ n + 1 := by
        have := Nat.minFac_dvd (2 ^ n + 1); rwa [h] at this
      have h2_pow : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
      omega
    by_cases hq : q ∣ n
    · -- q ∣ n: get a new prime r and let m = n * q * r
      obtain ⟨r, hr_prime, hr_dvd_pow, hr_not_dvd⟩ :=
        exists_new_prime_factor hn3 hq_prime hq_odd hqdvd
      have hnq_pos : 0 < n * q := Nat.mul_pos hn hq_prime.pos
      have hr_ne_2 : r ≠ 2 := by
        rintro rfl
        have h2_pow : 2 ∣ 2 ^ (n * q) := dvd_pow_self 2 (by positivity)
        omega
      have hr_not_n : ¬ r ∣ n := fun h => hr_not_dvd (h.trans hd)
      refine ⟨n * q * r, Nat.mul_pos hnq_pos hr_prime.pos,
              extend_divisibility (extend_divisibility hd q hq_prime hq_odd hqdvd)
                r hr_prime hr_ne_2 hr_dvd_pow, ?_⟩
      have hnq_factors : (n * q).primeFactors = n.primeFactors := by
        rw [Nat.primeFactors_mul hn.ne' hq_prime.ne_zero, hq_prime.primeFactors,
            Finset.union_eq_left]
        intro p hp
        rw [Finset.mem_singleton] at hp
        exact hp ▸ Nat.mem_primeFactors.mpr ⟨hq_prime, hq, hn.ne'⟩
      rw [Nat.primeFactors_mul hnq_pos.ne' hr_prime.ne_zero, hnq_factors,
          hr_prime.primeFactors, Finset.card_union_of_disjoint, Finset.card_singleton]
      simp only [Finset.disjoint_singleton_right]
      exact fun h => hr_not_n (Nat.dvd_of_mem_primeFactors h)
    · -- q ∤ n: let m = n * q
      refine ⟨n * q, Nat.mul_pos hn hq_prime.pos,
              extend_divisibility hd q hq_prime hq_odd hqdvd, ?_⟩
      rw [Nat.primeFactors_mul hn.ne' hq_prime.ne_zero, hq_prime.primeFactors,
          Finset.card_union_of_disjoint, Finset.card_singleton]
      simp only [Finset.disjoint_singleton_right]
      exact fun h => hq (Nat.dvd_of_mem_primeFactors h)
  · interval_cases n
    · exact ⟨3, by norm_num, by norm_num, by
        rw [Nat.Prime.primeFactors (by decide : Nat.Prime 3)]; simp⟩
    · omega

theorem exists_dvd_two_pow_add_one (k : ℕ) :
    ∃ n : ℕ, 0 < n ∧ n.primeFactors.card = k ∧ n ∣ 2 ^ n + 1 := by
  induction k with
  | zero => exact ⟨1, by norm_num, by norm_num, by norm_num⟩
  | succ k ih =>
    obtain ⟨n, hn_pos, hn_card, hn_dvd⟩ := ih
    obtain ⟨m, hm_pos, hm_dvd, hm_card⟩ := increase_prime_factors n hn_pos hn_dvd
    exact ⟨m, hm_pos, by omega, hm_dvd⟩

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
