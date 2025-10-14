/-
Copyright (c) 2025 The Compfiles Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib

import ProblemExtraction

problem_file {
  tags := [.NumberTheory]
}

/-!
# International Mathematical Olympiad 1991, Problem 2

Let n > 6 be an integer and a₁, a₂, ..., aₖ be all the
natural numbers less than n and relatively prime to n.
If

  a₂ - a₁ = a₃ - a₂ = ... = aₖ - aₖ₋₁ > 0,

prove that n must either be a prime number of a power
of 2.
-/

namespace Imo1991P2

problem imo1991_p2 (n : ℕ) (hn : 6 < n)
    (k : ℕ) (a : Fin k → ℕ)
    (ha1 : ∀ i, Nat.Coprime (a i) n ∧ a i < n)
    (ha2 : ∀ m, Nat.Coprime m n ∧ m < n → (∃ i, a i = m))
    (d : ℕ) (hd : 0 < d)
    (ha3 : ∀ i : Fin k, (h : i + 1 < k) → a i + d = a ⟨i + 1, by cutsat⟩) :
    n.Prime ∨ n.isPowerOfTwo := by
  sorry

end Imo1991P2
