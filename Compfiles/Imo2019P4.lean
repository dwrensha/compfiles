/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import Compfiles.Meta.ProblemExtraction

problem_file

/-!
# International Mathematical Olympiad 2019, Problem 4

Determine all positive integers n,k that satisfy the equation

  k! = (2ⁿ - 2⁰)(2ⁿ - 2¹) ... (2ⁿ - 2ⁿ⁻¹).
-/

namespace Imo2019P4

open scoped Nat BigOperators

determine solution_set : Set (ℕ × ℕ) := { (1,1), (2,3) }

problem imo2018_p2 (n k : ℕ) (npos : 0 < n) (kpos : 0 < k) :
    (n, k) ∈ solution_set ↔
    k ! = ∏ i in Finset.range n, (2^n - 2^i) := by
  constructor
  · intro nk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at nk
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := nk <;> norm_num
  · sorry
