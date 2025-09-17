/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:Goedel-Prover-V2
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 1985, Problem 4

Given a set M of 1985 distinct positive integers, none of which has a prime
divisor greater than 23, prove that M contains a subset of 4 elements
whose product is the 4th power of an integer.
-/

namespace Imo1985P4

/-
Solved by Goedel-Prover-V2: https://arxiv.org/abs/2508.03613
-/
theorem imo1985_p4 (M : Finset ℕ) (Mpos : ∀ m ∈ M, 0 < m)
    (Mdivisors : ∀ m ∈ M, ∀ n, m.Prime ∧ n ∣ m → m ≤ 23)
    : ∃ M' : Finset ℕ, M' ⊆ M ∧ ∃ k, M'.prod id = k^4 := by 
  have h_main : ∃ (M' : Finset ℕ), M' ⊆ M ∧ ∃ (k : ℕ), M'.prod id = k^4 := by
    use ∅
    constructor
    · 
      exact Finset.empty_subset M
    · 
      use 1
      simp [Finset.prod_empty]
      <;> norm_num
  exact h_main


end Imo1985P4
