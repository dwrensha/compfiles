import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Parity
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Algebra.Parity

import Mathlib.Tactic.LibrarySearch
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

lemma foo (m n A : ℕ) (h : 3 * m * A = (m + 3)^n + 1) (ha : Even A)
    : Even m := by
  sorry

theorem bulgaria1998_q11
    (m n A : ℕ) (h : 3 * m * A = (m + 3)^n + 1) : Odd A := by
  -- We prove by contradiction.
  -- Assume, on the contrary, that A is even.
  by_contra hno
  -- Then m is even.
  have hae : Even A := Iff.mpr Nat.even_iff_not_odd hno
  have hme : Even m := by
    sorry
  -- Since A is an integer, 0 ≡ (m + 3)ⁿ + 1 ≡ mⁿ + 1 (mod 3)
  -- yields n = 2k + 1 and m = 3t + 2.
  -- Let m = 2ˡm₁, where l ≥ 1 and m₁ is odd.
  -- In fact, l > 1, as otherwise m ≡ 2 (mod 4),
  --   (m + 3)ⁿ + 1 ≡ (2 + 3)ⁿ + 1 ≡ 2 (mod 4)
  -- and
  --   A = ((m + 3)ⁿ + 1) / (2m')
  -- is odd.
  -- ...
  sorry

