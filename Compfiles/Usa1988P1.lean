/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 1988, Problem 1

The repeating decimal 0.ab ... k pq ... u = m/n, where m and n are
relatively prime integers, and there is at least one decimal before
the repeating part. Show that n is divisible by 2 or 5 (or both).
[For example, 0.01136̅ = 0.01136363636 ... = 1/88 and 88 is divisible
by 2.]
-/

namespace Usa1988P1

/-!
We model the repeating decimal `0.ab…k⟨pq…u⟩` as follows: `r ≥ 1` is the
number of digits before the repeating part, `s ≥ 1` is the length of the
repeating part, `a` is the integer formed by the digits `ab…k` and `b` is
the integer formed by the digits `pq…u`. The value of the decimal is then

  a / 10^r + b / (10^r * (10^s - 1)) = (a * (10^s - 1) + b) / (10^r * (10^s - 1)).

The last digits of `a` and `b` differ (`k ≠ u`), for otherwise the
repeating part could have been started one digit earlier.
-/

snip begin

-- Based on the solution by John Scholes (kalva):
-- https://prase.cz/kalva/usa/usoln/usol881.html

/-- The numerator `a * (10 ^ s - 1) + b` of the unreduced fraction is
congruent to `b - a` modulo 10, so it is not divisible by 10 when the
last digits of `a` and `b` differ. -/
lemma not_ten_dvd_num {a b s : ℕ} (hs : 1 ≤ s) (hab : a % 10 ≠ b % 10) :
    ¬ 10 ∣ a * (10 ^ s - 1) + b := by
  intro h
  have h1 : a * 10 ^ s ≡ 0 [MOD 10] :=
    Nat.modEq_zero_iff_dvd.mpr
      (dvd_mul_of_dvd_right (dvd_pow_self 10 (Nat.one_le_iff_ne_zero.mp hs)) a)
  have h2 : a * (10 ^ s - 1) + a = a * 10 ^ s := by
    conv_rhs => rw [← Nat.sub_add_cancel (Nat.one_le_pow s 10 (by norm_num))]
    rw [mul_add, mul_one]
  have h3 : a * (10 ^ s - 1) + b + a ≡ b [MOD 10] := by
    have e : a * (10 ^ s - 1) + b + a = a * 10 ^ s + b := by
      rw [add_right_comm, h2]
    rw [e]
    simpa using h1.add_right b
  have h4 : a * (10 ^ s - 1) + b + a ≡ a [MOD 10] := by
    have hN : a * (10 ^ s - 1) + b ≡ 0 [MOD 10] := Nat.modEq_zero_iff_dvd.mpr h
    simpa using hN.add_right a
  exact hab (h4.symm.trans h3)

snip end

problem usa1988_p1 {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) {a b : ℕ}
    (hab : a % 10 ≠ b % 10) {m n : ℕ} (hn : n ≠ 0) (hmn : m.Coprime n)
    (h : (m : ℚ) / (n : ℚ) = ((a * (10 ^ s - 1) + b : ℕ) : ℚ) /
        ((10 ^ r * (10 ^ s - 1) : ℕ) : ℚ)) :
    2 ∣ n ∨ 5 ∣ n := by
  have h10s : 0 < 10 ^ s - 1 := by
    have hle : (10 : ℕ) ≤ 10 ^ s := by
      calc (10 : ℕ) = 10 ^ 1 := (pow_one 10).symm
      _ ≤ 10 ^ s := Nat.pow_le_pow_right (by norm_num) hs
    omega
  have hDpos : 0 < 10 ^ r * (10 ^ s - 1) :=
    Nat.mul_pos (pow_pos (by norm_num) r) h10s
  -- Cross-multiply to get an equation over ℕ.
  have hmnQ : (m : ℚ) * ((10 ^ r * (10 ^ s - 1) : ℕ) : ℚ)
      = ((a * (10 ^ s - 1) + b : ℕ) : ℚ) * (n : ℚ) := by
    rw [div_eq_div_iff (by exact_mod_cast hn) (by exact_mod_cast hDpos.ne')] at h
    exact h
  have hmul : m * (10 ^ r * (10 ^ s - 1)) = (a * (10 ^ s - 1) + b) * n := by
    exact_mod_cast hmnQ
  -- Since gcd(m, n) = 1, n divides the unreduced denominator.
  have hnD : n ∣ 10 ^ r * (10 ^ s - 1) := by
    have hdvd : n ∣ m * (10 ^ r * (10 ^ s - 1)) :=
      ⟨a * (10 ^ s - 1) + b, by rw [hmul, mul_comm]⟩
    exact hmn.symm.dvd_of_dvd_mul_left hdvd
  obtain ⟨t, ht⟩ := hnD
  -- and m * t equals the numerator, so t divides the numerator.
  have hmt : m * t = a * (10 ^ s - 1) + b := by
    have e : m * (n * t) = (a * (10 ^ s - 1) + b) * n := by rw [← ht]; exact hmul
    have e2 : (m * t) * n = (a * (10 ^ s - 1) + b) * n := by rw [← e]; ring
    exact Nat.mul_right_cancel (Nat.pos_iff_ne_zero.mpr hn) e2
  -- 10 divides the unreduced denominator because r ≥ 1.
  have h10D : 10 ∣ 10 ^ r * (10 ^ s - 1) :=
    (dvd_pow_self 10 (Nat.one_le_iff_ne_zero.mp hr)).mul_right (10 ^ s - 1)
  -- If 2 ∤ n and 5 ∤ n, then 10 ∣ t, hence 10 divides the numerator:
  -- contradiction.
  by_contra hcon
  push Not at hcon
  obtain ⟨h2n, h5n⟩ := hcon
  have h2t : 2 ∣ t := by
    have h2D : 2 ∣ 10 ^ r * (10 ^ s - 1) := dvd_trans (by norm_num) h10D
    rw [ht] at h2D
    rcases (Nat.prime_two.dvd_mul).mp h2D with h2 | h2
    · exact absurd h2 h2n
    · exact h2
  have h5t : 5 ∣ t := by
    have h5D : 5 ∣ 10 ^ r * (10 ^ s - 1) := dvd_trans (by norm_num) h10D
    rw [ht] at h5D
    rcases (Nat.prime_five.dvd_mul).mp h5D with h5 | h5
    · exact absurd h5 h5n
    · exact h5
  have h10t : (10 : ℕ) ∣ t := by
    have hc : Nat.Coprime 2 5 := by norm_num
    have h25 := hc.mul_dvd_of_dvd_of_dvd h2t h5t
    norm_num at h25 ⊢
    exact h25
  have htN : t ∣ a * (10 ^ s - 1) + b := by
    rw [← hmt]
    exact dvd_mul_left t m
  exact not_ten_dvd_num hs hab (dvd_trans h10t htN)

end Usa1988P1
