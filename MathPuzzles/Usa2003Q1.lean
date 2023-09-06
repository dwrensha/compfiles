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
  have hd : ∃ ds, ds = Nat.digits b y := exists_eq
  obtain ⟨ds, hd⟩ := hd
  revert x y
  induction ds with
  | nil =>
    intros x y hx1 hx2 hy
    simp[Nat.digits_eq_nil_iff_eq_zero.mp hy.symm, Nat.digits_of_lt b x hx2 hx1]
  | cons d ds ih =>
    intros x y hx1 hx2 hd
    rw[←hd, List.length_cons, Nat.pow_succ, List.cons_append]
    have hyp : 0 < y := by
       by_contra H
       simp[Nat.eq_zero_of_nonpos y H] at hd
    have h3 := Nat.digits_def' hb hyp
    rw[h3] at hd
    have h4 : d = y % b := by aesop
    have h5 : ds = Nat.digits b (y/b) := by aesop
    have h2 := ih x (y/b) hx1 hx2 h5
    rw[←h5] at h2
    have h6 : 0 < x * (b ^ List.length ds * b) + y := by positivity
    rw[Nat.digits_def' hb h6, ←Nat.mul_assoc]
    congr
    · rw[Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod]
      exact h4.symm
    · rw[← h2]
      congr
      have hbz : 0 < b := Nat.zero_lt_one.trans hb
      rw[Nat.add_div hbz]
      have h6: ¬ (b ≤ y % b) := Nat.not_le.mpr (Nat.mod_lt y hbz)
      simp[h6]
      rw[Nat.mul_div_left _ hbz]


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
        · sorry-- exact hk2
        · sorry

    -- This is equivalent to proving that there exists an odd digit k such that
    -- k·2ⁿ + a is divisible by 5,
    -- which is true when k ≡ -3ⁿ⬝a MOD 5.
    -- Since there is an odd digit in each of the residue classes MOD 5,
    -- k exists and the induction is complete.
    sorry
