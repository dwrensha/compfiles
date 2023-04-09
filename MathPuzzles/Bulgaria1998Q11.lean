import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Parity
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Algebra.Parity

import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.ModCases
import Mathlib.Tactic.Ring

/-
Bulgarian Mathematical Olympiad 1998, Problem 11

Let m,n be natural numbers such that

   A = ((m + 3)ⁿ + 1) / (3m)

is an integer. Prove that A is odd.
-/

namespace Bulgaria1998Q11

lemma mod_plus_pow (m n : ℕ) : (m + 3)^n % 3 = m^n % 3 := by
  induction' n with pn hpn
  · simp only [Nat.zero_eq, pow_zero, Nat.one_mod]
  · rw[pow_succ]
    have h1 : (m + 3) * (m + 3) ^ pn = m * (m + 3) ^ pn + 3 * (m + 3) ^ pn := by ring
    rw [h1]
    have h2 : 3 * (m + 3) ^ pn % 3 = 0 := Nat.mul_mod_right 3 _
    rw[Nat.add_mod, h2, add_zero, Nat.mod_mod, pow_succ]
    exact Nat.ModEq.mul rfl hpn


lemma foo1 (m n : ℕ) (ho : Odd m) : (m + 3) ^ n.succ % 2 = 0 := by
  cases' ho with w hw
  rw[hw]
  rw[Nat.pow_succ]
  have h1 : 2 * w + 1 + 3 = 2 * (w + 2) := by ring
  rw[h1, Nat.mul_mod]
  simp only [Nat.mul_mod_right, mul_zero, Nat.zero_mod]

theorem bulgaria1998_q11
    (m n A : ℕ)
    (h : 3 * m * A = (m + 3)^n + 1) : Odd A := by
  -- First show that n must be positive.
  cases n with
  | zero => exfalso
            simp only [Nat.zero_eq, pow_zero] at h
            have h1 : (3 * m * A) % 3 = (1 + 1) % 3 := congrFun (congrArg HMod.hMod h) 3
            simp[Nat.mul_mod] at h1
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
    have h1 : (3 * m * (2 * k)) % 2 = ((m + 3) ^ n.succ + 1) % 2 :=
      congrFun (congrArg HMod.hMod h) 2
    simp[Nat.mul_mod, Nat.add_mod, foo1 m n hmo] at h1

  -- Since A is an integer, 0 ≡ (m + 3)ⁿ + 1 ≡ mⁿ + 1 (mod 3)
  have h1 : 0 ≡ m ^ n.succ + 1 [MOD 3] := by
    calc 0 % 3
      = 3 * m * A % 3 := by rw[mul_assoc]; simp only [Nat.zero_mod, Nat.mul_mod_right]
    _ = ((m + 3) ^ n.succ + 1) % 3 := by rw[h];
    _ = (m ^ n.succ + 1) % 3 := Nat.ModEq.add_right _ (mod_plus_pow _ _)

  -- yields n = 2k + 1 and m = 3t + 2.
  have h2 : m % 3 = 2 := by
    sorry

  -- Let m = 2ˡm₁, where l ≥ 1 and m₁ is odd.
  -- In fact, l > 1, as otherwise m ≡ 2 (mod 4),
  --   (m + 3)ⁿ + 1 ≡ (2 + 3)ⁿ + 1 ≡ 2 (mod 4)
  -- and
  --   A = ((m + 3)ⁿ + 1) / (2m')
  -- is odd.
  -- ...
  sorry

