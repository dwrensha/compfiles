/-
Copyright (c) 2023 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Adam Kurkiewicz
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
Bulgarian Mathematical Olympiad 1998, Problem 11

Let m,n be natural numbers such that

   A = ((m + 3)ⁿ + 1) / (3m)

is an integer. Prove that A is odd.
-/

namespace Bulgaria1998P11

snip begin

/-- A natural number that is 2 mod 3 has a prime factor that is 2 mod 3. -/
lemma exists_prime_fac_mod_three_eq_two (m : ℕ) (hm : m % 3 = 2) :
    ∃ p, p.Prime ∧ p ∣ m ∧ p % 3 = 2 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  obtain ⟨p, pp, q, rfl⟩ := Nat.exists_prime_and_dvd (show m ≠ 1 by lia)
  rw [Nat.mul_mod] at hm
  obtain h3 | h3 | h3 : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by lia
  · rw [h3] at hm; simp at hm
  · rw [h3] at hm
    have hq3 : q % 3 = 2 := by lia
    have hq : q < p * q := by nlinarith [pp.two_le, show 0 < q by lia]
    obtain ⟨r, rp, rdvd, hr⟩ := ih q hq hq3
    exact ⟨r, rp, rdvd.mul_left p, hr⟩
  · exact ⟨p, pp, dvd_mul_right p q, h3⟩

/-- If `-3` is a square mod an odd prime `p`, then `p` is not 2 mod 3:
the element `ω` with `2 * ω = a - 1` satisfies `ω² + ω + 1 = 0`, hence has
order three, so that `3 ∣ p - 1` by Fermat's little theorem. -/
lemma mod_three_ne_two_of_sq_eq_neg_three {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {a : ZMod p} (ha : a ^ 2 = -3) : p % 3 ≠ 2 := by
  intro hp3
  have hpi : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_cast,
        ZMod.natCast_eq_zero_iff,
        Nat.prime_dvd_prime_iff_eq hp Nat.prime_two] at h
    exact hp2 h
  obtain ⟨ω, h2ω⟩ : ∃ ω : ZMod p, 2 * ω = a - 1 := ⟨(a - 1) / 2, by field_simp⟩
  have hroot : ω ^ 2 + ω + 1 = 0 := by
    have h0 : (2 : ZMod p) * 2 * (ω ^ 2 + ω + 1) = 0 := by
      linear_combination (2 * ω + 1 + a) * h2ω + ha
    exact (mul_eq_zero.mp h0).resolve_left (mul_ne_zero h2 h2)
  have hω1 : ω ≠ 1 := by
    rintro rfl
    have h3 : ((3 : ℕ) : ZMod p) = 0 := by push_cast; linear_combination hroot
    rw [ZMod.natCast_eq_zero_iff,
        Nat.prime_dvd_prime_iff_eq hp Nat.prime_three] at h3
    lia
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hroot
  have h3dvd : (3 : ℕ) ∣ p - 1 := by
    rw [← orderOf_eq_prime (by linear_combination (ω - 1) * hroot : ω ^ 3 = 1) hω1]
    exact orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hω0)
  have := hp.two_le
  lia

lemma n_odd_and_m_mod_three {m n A : ℕ} (h : 3 * m * A = (m + 3) ^ n + 1) :
    Odd n ∧ m % 3 = 2 := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    norm_num at h
    lia
  have hcast : (m : ZMod 3) ^ n + 1 = 0 := by
    have hc : ((3 * m * A : ℕ) : ZMod 3) = (((m + 3) ^ n + 1 : ℕ) : ZMod 3) := by
      rw [h]
    push_cast at hc
    rw [show (3 : ZMod 3) = 0 by decide, add_zero, zero_mul, zero_mul] at hc
    linear_combination -hc
  have hmod : m % 3 = (m : ZMod 3).val := by rw [ZMod.val_natCast]
  obtain h0 | h1 | h2 : (m : ZMod 3) = 0 ∨ (m : ZMod 3) = 1 ∨ (m : ZMod 3) = 2 := by
    generalize (m : ZMod 3) = x; revert x; decide
  · rw [h0, zero_pow hn0] at hcast
    exact absurd hcast (by decide)
  · rw [h1, one_pow] at hcast
    exact absurd hcast (by decide)
  · refine ⟨?_, by rw [hmod, h2]; rfl⟩
    by_contra hodd
    rw [Nat.not_odd_iff_even] at hodd
    rw [h2, show (2 : ZMod 3) = -1 by decide, hodd.neg_one_pow] at hcast
    exact absurd hcast (by decide)

snip end

problem bulgaria1998_p11
    (m n A : ℕ)
    (h : 3 * m * A = (m + 3)^n + 1) : Odd A := by
  obtain ⟨⟨k, hk⟩, hm3⟩ := n_odd_and_m_mod_three h
  by_contra even_A
  rw [Nat.not_odd_iff_even, Nat.even_iff] at even_A
  -- The left-hand side is even, so (m + 3)ⁿ must be odd, whence m is even.
  have hL2 : ((m + 3) ^ n + 1) % 2 = 0 := by
    rw [← h, Nat.mul_mod, even_A, mul_zero, Nat.zero_mod]
  have hm2 : m % 2 = 0 := by
    by_contra hm2
    have h1 : (m + 3) ^ n % 2 = 0 := by
      rw [Nat.pow_mod, show (m + 3) % 2 = 0 by lia,
          Nat.zero_pow (show 0 < n by lia), Nat.zero_mod]
    lia
  -- Modulo m, the right-hand side is 3ⁿ + 1, so m ∣ 3ⁿ + 1.
  have hmd : m ∣ 3 ^ n + 1 := by
    have h1 : m ∣ (m + 3) ^ n + 1 := h ▸ ⟨3 * A, by ring⟩
    have e : (m + 3) ≡ 3 [MOD m] := Nat.add_mod_left m 3
    have h2 : (m + 3) ^ n + 1 ≡ 3 ^ n + 1 [MOD m] := (e.pow n).add_right 1
    exact Nat.modEq_zero_iff_dvd.mp
      (h2.symm.trans (Nat.modEq_zero_iff_dvd.mpr h1))
  -- Since n is odd, 3ⁿ + 1 is 4 mod 8.
  have h8 : (3 ^ n + 1) % 8 = 4 := by
    subst hk
    have h9 : 9 ^ k % 8 = 1 := by rw [Nat.pow_mod]; norm_num
    rw [show 3 ^ (2 * k + 1) = 9 ^ k * 3 by rw [pow_succ, pow_mul]; norm_num,
        Nat.add_mod, Nat.mul_mod, h9]
  obtain hm4 | hm4 : m % 4 = 0 ∨ m % 4 = 2 := by lia
  · -- The case 4 ∣ m: here we do not even need that A is even.
    obtain ⟨m₁, rfl⟩ : 4 ∣ m := Nat.dvd_of_mod_eq_zero hm4
    -- m₁ is odd: otherwise 8 ∣ m ∣ 3ⁿ + 1, contradicting h8.
    have hm₁odd : m₁ % 2 = 1 := by
      by_contra hodd
      obtain ⟨w, rfl⟩ : 2 ∣ m₁ := by lia
      have h4w : (8 : ℕ) ∣ 4 * (2 * w) := ⟨w, by ring⟩
      have h8d : (8 : ℕ) ∣ 3 ^ n + 1 := h4w.trans hmd
      lia
    have hm₁3 : m₁ % 3 = 2 := by lia
    -- Multiplying m₁ ∣ 3ⁿ + 1 by 3 shows that -3 is a square mod m₁.
    have hm₁d : m₁ ∣ 3 ^ (k + 1) * 3 ^ (k + 1) + 3 := by
      have e : 3 ^ (k + 1) * 3 ^ (k + 1) + 3 = 3 * (3 ^ n + 1) := by subst hk; ring
      rw [e]
      exact ((dvd_mul_left m₁ 4).trans hmd).mul_left 3
    -- But -3 is not a square modulo the prime factor p ≡ 2 (mod 3) of m₁.
    obtain ⟨p, pp, pdvd, hp3⟩ := exists_prime_fac_mod_three_eq_two m₁ hm₁3
    have hp2 : p ≠ 2 := by
      rintro rfl
      obtain ⟨w, rfl⟩ := pdvd
      lia
    have hpp : Fact p.Prime := ⟨pp⟩
    have hcast : ((3 ^ (k + 1) * 3 ^ (k + 1) + 3 : ℕ) : ZMod p) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact pdvd.trans hm₁d
    push_cast at hcast
    exact absurd hp3 (mod_three_ne_two_of_sq_eq_neg_three pp hp2
      (by linear_combination hcast : ((3 : ZMod p) ^ (k + 1)) ^ 2 = -3))
  · -- The case m ≡ 2 (mod 4): compare the two sides of h modulo 4.
    obtain ⟨a, rfl⟩ : 2 ∣ A := Nat.dvd_of_mod_eq_zero even_A
    obtain ⟨v, rfl⟩ : 2 ∣ m := Nat.dvd_of_mod_eq_zero hm2
    have hL4 : (4 : ℕ) ∣ 3 * (2 * v) * (2 * a) := ⟨3 * v * a, by ring⟩
    have hR4 : ((2 * v + 3) ^ n + 1) % 4 = 2 := by
      rw [Nat.add_mod, Nat.pow_mod, show (2 * v + 3) % 4 = 1 by lia, one_pow]
      decide
    lia
