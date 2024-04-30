/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 2021, Problem 6

Let m ≥ 2 be an integer, A a finite set of integers (not necessarily
positive) and B₁, B₂, ... Bₘ subsets of A. Suppose that for every
k = 1, 2, ..., m, the sum of the elements of Bₖ is m^k. Prove that
A contains at least m/2 elements.
-/

namespace Imo2021P6

open scoped BigOperators

problem imo2021_p6 (m : ℕ) (hm : 2 ≤ m) (A : Finset ℤ)
    (B : Fin m → Finset ℤ) (hB : ∀ k, B k ⊆ A)
    (hs : ∀ k, ∑ b ∈ B k, b = (m : ℤ) ^ (k.val + 1))
    : m ≤ 2 * A.card := by
  sorry

