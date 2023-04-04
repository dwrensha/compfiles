import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.ModEq
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

theorem bulgaria1998_q11
    (m n A : ℕ) (h : 3 * m * A = (m + 3)^n + 1) : Odd A := by
  sorry

