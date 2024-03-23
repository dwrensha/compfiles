/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 2009, Problem 6

Let a₁, a₂, ..., aₙ be distinct positive integers and let M
be a set of n - 1 positive integers not containing
s = a₁ + a₂ + ... + aₙ. A grasshopper is to jump along the
real axis, starting at the point 0 and making n jumps to
the right with lengths a₁, a₂, ..., aₙ in some order. Prove
that the order can be chosen in such a way that the
grasshopper never lands on any point in M.
-/

namespace Imo2009P6

open scoped BigOperators

problem imo2009_p6 (n : ℕ) (hn : 0 < n)
    (a : Fin n → ℤ)
    (apos : ∀ i, 0 < a i)
    (M : Finset ℤ)
    (Mpos : ∀ m ∈ M, 0 < m)
    (Mcard : M.card = n - 1)
    (hM : ∑ i, a i ∉ M)
    : ∃ p : Fin n → Fin n,
        p.Bijective ∧
        ∀ i : Fin n, ∑ j : Fin (i + 1), a (p ⟨j, by omega⟩) ∉ M := by
  sorry
