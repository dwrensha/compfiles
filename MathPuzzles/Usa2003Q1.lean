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
    -- k·2ⁿ + a is divisible by 5,
    -- which is true when k ≡ -3ⁿ⬝a MOD 5.
    -- Since there is an odd digit in each of the residue classes MOD 5,
    -- k exists and the induction is complete.
    sorry
