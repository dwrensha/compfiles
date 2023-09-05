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

theorem usa2003Q1 (n : ℕ) (hn : 0 < n) :
    ∃ m, ((Nat.digits 10 m).length = n ∧
          (Nat.digits 10 m).all (λ d ↦ Odd d)) := by
  -- Informal solution from artofproblemsolving.com
  -- We proceed by induction.
  -- For our base case, n=1, we have the number 5.
  -- Now, suppose that there exists some number a·5ⁿ⁻¹ with n-1 digits,
  -- all of which are odd. It is then sufficient to prove that there exists
  -- an odd digit k such that k·10ⁿ⁻¹ + a·5ⁿ⁻¹ = 5ⁿ⁻¹(k·2ⁿ⁻¹ + a) is
  -- divisible by 5ⁿ.
  -- This is equivalent to proving that there exists an odd digit k such that
  -- k·2ⁿ⁻¹ + a is divisible by 5,
  -- which is true when k ≡ - 3ⁿ⁻¹a MOD 5.
  -- Since there is an odd digit in each of the residue classes mod 5,
  -- k exists and the induction is complete.
  sorry
