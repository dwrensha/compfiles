/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Nat.Digits
import Mathlib.Data.Nat.Parity

import Mathlib.Tactic

/-!
# USA Mathematical Olympiad 2003, Problem 1

Prove that for every positive integer n there exists an n-digit
number divisible by 5ⁿ, all of whose digits are odd.
-/

namespace Usa2003Q1

-- lemma for mathlib?
theorem Nat.digits_add'
    (b : ℕ) (hb : 1 < b) (x y : ℕ) (hxb : x < b) (hx0 : x ≠ 0) :
    Nat.digits b (x * b ^ (Nat.digits b y).length + y) =
      Nat.digits b y ++ [x] := by
  have : x * b ^ (Nat.digits b y).length + y = Nat.ofDigits b (Nat.digits b y ++ [x])
  · simp [Nat.ofDigits_append, Nat.ofDigits_digits, add_comm, mul_comm]
  rw [this, Nat.digits_ofDigits _ hb]
  · simpa [forall_and, or_imp, hxb] using fun _ => Nat.digits_lt_base hb
  · simpa

lemma nat_mod_inv (a : ℕ) : ∃ b, (a + b) % 5 = 0 := by
  use (5 - (a % 5))
  have h : a % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have h' : a % 5 ≤ 5 := Nat.le_of_lt h
  rw[Nat.add_mod]
  have h2 : a % 5 = a % 5 % 5 := (Nat.mod_mod a 5).symm
  rw[h2, ← Nat.add_mod, Nat.mod_mod]
  rw[Nat.add_sub_of_le h']
  rfl

lemma lemma2 (a c : ℕ) (h : ¬ a ≡ 0 [MOD 5]) : ∃ k, k < 5 ∧ a * k ≡ c [MOD 5] := by
  -- use chinese remainder to find something that's
  -- 0 mod a and c MOD 5.
  have hc : Nat.coprime 5 a := by
    have h5 : Nat.Prime 5 := by norm_num
    refine' (Nat.Prime.coprime_iff_not_dvd h5).mpr _
    rw[Nat.modEq_zero_iff_dvd] at h
    exact h
  let ⟨N, HN2, HN1⟩ := Nat.chineseRemainder hc c 0
  have ⟨x, hx⟩ : a ∣ N := Iff.mp Nat.modEq_zero_iff_dvd HN1
  use x % 5
  constructor
  · exact Nat.mod_lt _ (by norm_num)
  · have h2 : N % 5 = c % 5 := HN2
    suffices h : (a * (x % 5)) % 5 = c % 5 by exact h
    rw[← h2, hx]
    rw[Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

theorem usa2003Q1 (n : ℕ) :
    ∃ m, ((Nat.digits 10 m).length = n ∧
          5^n ∣ m ∧
          (Nat.digits 10 m).all (λ d ↦ Odd d)) := by
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
    -- an odd digit k such that k·10ⁿ + a·5ⁿ = 5ⁿ(k·2ⁿ + a) is
    -- divisible by 5ⁿ⁺¹.
    suffices h : ∃ k, Odd k ∧ k < 10 ∧ 5^(n + 1) ∣ (10^n * k + 5^n * a) by
      obtain ⟨k, hk0, hk1, hk2⟩ := h
      use k * 10 ^ n  + 5 ^ n * a
      have hkn : k ≠ 0 := Nat.ne_of_odd_add hk0
      have h1 := Nat.digits_add' 10 (by norm_num) k pm hk1 hkn
      rw[hpm1, ha] at h1
      rw[h1]
      constructor
      · rw[←ha]; simp[hpm1]
      · constructor
        · rw[Nat.succ_eq_add_one]
          nth_rewrite 1 [Nat.mul_comm]
          exact hk2
        · rw[List.all_eq_true]
          rw[List.all_eq_true, ha] at hpm3
          intro x hx
          rw[List.mem_append] at hx
          cases' hx with hx hx
          · exact hpm3 x hx
          · simp at hx
            rw[hx]
            exact decide_eq_true hk0

    -- This is equivalent to proving that there exists an odd digit k such that
    -- k·2ⁿ + a is divisible by 5...
    suffices h : ∃ k, Odd k ∧ k < 10 ∧ 5 ∣ (2^n * k + a) by
      obtain ⟨k, hk1, hk2, kk, hkk⟩ := h
      refine' ⟨k, hk1, hk2, _⟩
      use kk
      rw[Nat.pow_succ, Nat.mul_assoc, ←hkk, Nat.mul_pow 5 2 n]
      ring

    -- ...which is true when k ≡ -3ⁿ⬝a MOD 5.
    -- Since there is an odd digit in each of the residue classes MOD 5,
    -- k exists and the induction is complete.

    suffices h : ∃ j, j < 5 ∧ 5 ∣ (2^n * (2 * j + 1) + a) by
      obtain ⟨j, hj1, hj2⟩ := h
      refine' ⟨2 * j + 1, odd_two_mul_add_one j, _, hj2⟩
      · linarith
    clear ha hpm1 hpm3

    obtain ⟨b, hb⟩ := nat_mod_inv (2^n + a)
    have h11 : ¬ 2^(n + 1) ≡ 0 [MOD 5] := by
      have h14 : Nat.coprime 5 2 := by norm_num
      have h15 : Nat.coprime (5^1) (2^(n+1)) := Nat.coprime.pow _ _ h14
      rw[Nat.pow_one] at h15
      have h5 : Nat.Prime 5 := by norm_num
      have h16 := (Nat.Prime.coprime_iff_not_dvd h5).mp h15
      intro h17
      have h18 : 5 ∣ 2 ^ (n + 1) := Iff.mp Nat.modEq_zero_iff_dvd h17
      exact (h16 h18).elim
    obtain ⟨aa, haa1, haa2⟩ := lemma2 (2^(n + 1)) b h11
    use aa
    constructor
    · exact haa1
    · have h12 : (2^n + a + 2 ^ (n + 1) * aa) % 5 = (2^n + a + b) % 5 := Nat.ModEq.add rfl haa2
      rw[hb] at h12
      have h13 : (2 ^ n + a + 2 ^ (n + 1) * aa) = 2 ^ n * (2 * aa + 1) + a := by ring
      rw[h13] at h12
      exact Iff.mp Nat.modEq_zero_iff_dvd h12
