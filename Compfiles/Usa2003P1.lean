/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Nat.Digits.Lemmas

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 2003, Problem 1

Prove that for every positive integer n there exists an n-digit
number divisible by 5ⁿ, all of whose digits are odd.
-/

namespace Usa2003P1

snip begin

lemma nat_mod_inv (a : ℕ) : ∃ b, (a + b) % 5 = 0 := ⟨5 - (a % 5), by omega⟩

lemma lemma2 (a b c : ℕ) (hb : 0 < b) (h : Nat.Coprime a b) : ∃ k, k < b ∧ a * k ≡ c [MOD b] := by
  let ⟨N, HN1, HN2⟩ := Nat.chineseRemainder h 0 c
  have ⟨x, hx⟩ : a ∣ N := Nat.modEq_zero_iff_dvd.mp HN1
  use x % b
  constructor
  · exact Nat.mod_lt _ hb
  · change N % b = c % b at HN2
    change (a * (x % b)) % b = c % b
    rw [← HN2, hx, Nat.mul_mod, Nat.mod_mod, ←Nat.mul_mod]

snip end

problem usa2003_p1 (n : ℕ) :
    ∃ m, (Nat.digits 10 m).length = n ∧
          5^n ∣ m ∧ (Nat.digits 10 m).all (Odd ·) := by
  -- Informal solution from artofproblemsolving.com
  --
  -- We proceed by induction.
  induction' n with n ih
  · -- For our base case, n=0, the digits are [] and the theorem
    -- is vacuously true.
    use 0; simp
  · --
    -- Now, suppose that there exists some number a·5ⁿ with n digits,
    -- all of which are odd.
    --
    obtain ⟨pm, hpm1, ⟨a, ha⟩, hpm3⟩ := ih

    -- It is then sufficient to prove that there exists
    -- an odd digit k such that 5ⁿ⬝a + 10ⁿ⬝k = 5ⁿ(k·2ⁿ + a) is
    -- divisible by 5ⁿ⁺¹.
    suffices h : ∃ k, Odd k ∧ k < 10 ∧ 5^(n + 1) ∣ 5 ^ n * a + 10 ^ n * k by
      obtain ⟨k, hk0, hk1, hk2⟩ := h
      use 5 ^ n * a + 10 ^ n * k
      have hkn : k ≠ 0 := Nat.ne_of_odd_add hk0
      have h1 := Nat.digits_append_digits (m := k) (n := pm) (Nat.succ_pos 9)
      rw[hpm1, ha, Nat.digits_of_lt 10 k hkn hk1] at h1
      grind

    -- This is equivalent to proving that there exists an odd digit k such that
    -- k·2ⁿ + a is divisible by 5...
    suffices h : ∃ k, Odd k ∧ k < 10 ∧ 5 ∣ (2^n * k + a) by
      obtain ⟨k, hk1, hk2, kk, hkk⟩ := h
      refine ⟨k, hk1, hk2, kk, ?_⟩
      rw [Nat.pow_succ, Nat.mul_assoc, ←hkk, Nat.mul_pow 5 2 n]
      ring

    -- ...which is true when k ≡ -3ⁿ⬝a MOD 5.
    -- Since there is an odd digit in each of the residue classes MOD 5,
    -- k exists and the induction is complete.

    suffices h : ∃ j, j < 5 ∧ 5 ∣ (2^n * (2 * j + 1) + a) by
      obtain ⟨j, hj1, hj2⟩ := h
      refine ⟨2 * j + 1, odd_two_mul_add_one j, ?_, hj2⟩
      · omega
    clear ha hpm1 hpm3

    obtain ⟨b, hb⟩ : ∃ b, ((2^n + a) + b) % 5 = 0 := nat_mod_inv (2^n + a)
    have h11 : ¬ 2^(n + 1) ≡ 0 [MOD 5] := by
      have h14 : Nat.Coprime 5 2 := by norm_num
      have h15 : Nat.Coprime 5 (2^(n+1)) := Nat.Coprime.pow_right (n + 1) h14
      have h16 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mp h15
      intro h17
      have h18 : 5 ∣ 2 ^ (n + 1) := Iff.mp Nat.modEq_zero_iff_dvd h17
      exact (h16 h18).elim
    obtain ⟨aa, haa1, haa2⟩ := lemma2 (2^(n + 1)) 5 b (Nat.succ_pos 4)
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr
        (Nat.modEq_zero_iff_dvd.not.mp h11)).symm
    use aa
    constructor
    · exact haa1
    · have h12 : (2^n + a + 2 ^ (n + 1) * aa) % 5 = (2^n + a + b) % 5 :=
        Nat.ModEq.add rfl haa2
      cutsat

end Usa2003P1
