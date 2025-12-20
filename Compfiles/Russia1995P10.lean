/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maximiliano Onofre Martínez
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.GCD.Basic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# Russian Mathematical Olympiad 1995, problem 10

Let m, n be positive integers such that

gcd(m, n) + lcm(m, n) = m + n.

Show that one of the two numbers is divisible by the other.
-/

namespace Russia1995P10

problem russia1995_p10 {m n : ℕ} (h₀ : n ≠ 0 ∧ m ≠ 0)
  (h : gcd m n + lcm m n = m + n) :
  m ∣ n ∨ n ∣ m := by
sorry

end Russia1995P10
