/-
Copyright (c) 2023 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.Parity
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

lemma mod_plus_pow (m n : ℕ) : (m + 3)^n % 3 = m^n % 3 := by
  induction' n with pn hpn
  · simp only [Nat.zero_eq, pow_zero, Nat.one_mod]
  · rw [Nat.pow_succ']
    have h1 : (m + 3) * (m + 3) ^ pn = m * (m + 3) ^ pn + 3 * (m + 3) ^ pn := by ring
    rw [h1]
    have h2 : 3 * (m + 3) ^ pn % 3 = 0 := Nat.mul_mod_right 3 _
    rw[Nat.add_mod, h2, add_zero, Nat.mod_mod, Nat.pow_succ']
    exact Nat.ModEq.mul rfl hpn

lemma foo1 (m n : ℕ) (ho : Odd m) : (m + 3) ^ n.succ % 2 = 0 := by
  cases' ho with w hw
  rw[hw, Nat.pow_succ, show 2 * w + 1 + 3 = 2 * (w + 2) by ring, Nat.mul_mod,
     Nat.mul_mod_right, mul_zero, Nat.zero_mod]

snip end

problem bulgaria1998_p11
    (m n A : ℕ)
    (h : 3 * m * A = (m + 3)^n + 1) : Odd A := by
  -- First show that n must be positive.
  cases n with
  | zero => exfalso
            simp only [Nat.zero_eq, pow_zero] at h
            apply_fun (· % 3) at h
            simp[Nat.mul_mod] at h
  | succ n =>

  -- We prove by contradiction.
  -- Assume, on the contrary, that A is even.
  by_contra hno
  -- Then m is even.
  have hae : Even A := Iff.mpr Nat.even_iff_not_odd hno
  have hme : Even m := by
    cases' hae with k hk
    rw [hk, show k + k = 2 * k by ring] at h
    by_contra hmo
    rw[←Nat.odd_iff_not_even] at hmo
    apply_fun (· % 2) at h
    simp[Nat.mul_mod, Nat.add_mod, foo1 m n hmo] at h

  -- Since A is an integer, 0 ≡ (m + 3)ⁿ + 1 ≡ mⁿ + 1 (mod 3)
  have h1 : 0 ≡ m ^ n.succ + 1 [MOD 3] := by
    calc 0 % 3
      = 3 * m * A % 3 := by rw[mul_assoc]; simp only [Nat.zero_mod, Nat.mul_mod_right]
    _ = ((m + 3) ^ n.succ + 1) % 3 := by rw[h];
    _ = (m ^ n.succ + 1) % 3 := Nat.ModEq.add_right _ (mod_plus_pow _ _)

  -- yields n = 2k + 1 and m = 3t + 2.
  have h2 := Nat.ModEq.add_right 2 h1
  rw[add_assoc, show 1 + 2 = 3 by rfl, zero_add] at h2
  have h5: 2 % 3 = (m ^ (Nat.succ n) + 3) % 3 := h2
  have h3 : m % 3 = 2 := by
    mod_cases hm : m % 3
    · change m % 3 = 0 % 3 at hm
      simp[Nat.pow_mod, hm] at h5
    · change m % 3 = 1 % 3 at hm
      simp (config := {decide := true}) [Nat.pow_mod, hm] at h5
    · change m % 3 = 2 % 3 at hm; exact hm

  have h6: Nat.succ n % 2 = 1 := by
    mod_cases hn : (Nat.succ n) % 2
    · exfalso
      change (Nat.succ n) % 2 = 0 % 2 at hn
      have h9: Even (Nat.succ n) := Iff.mpr Nat.even_iff hn
      cases' h9 with k hk
      rw[hk] at h1
      have h1' : 0 % 3 = ( m ^ (k + k) + 1) % 3 := h1
      rw[Nat.add_mod, Nat.pow_mod, h3, ←Nat.two_mul, pow_mul, Nat.pow_mod,
         show 2 ^ 2 % 3 = 1 by rfl] at h1'
      simp at h1'
    · exact hn

  -- Let m = 2ˡm₁, where l ≥ 1 and m₁ is odd.
  -- In fact, l > 1, as otherwise m ≡ 2 (mod 4),
  --   (m + 3)ⁿ + 1 ≡ (2 + 3)ⁿ + 1 ≡ 2 (mod 4)
  -- and
  --   A = ((m + 3)ⁿ + 1) / (2m')
  -- is odd.
  -- ...
  sorry

