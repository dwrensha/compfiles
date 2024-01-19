/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 2023, Problem 3

For each integer k ≥ 2, determine all infinite sequences of positive
integers a₁, a₂, ... for which there exists a polynomial P of the form

  P(x) = xᵏ + cₖ₋₁xᵏ⁻¹ + ... + c₁x + c₀,

where c₀, c₁, ..., cₖ₋₁ are non-negative integers, such that

  P(aₙ) = aₙ₊₁aₙ₊₂⋯aₙ₊ₖ

for every integer n ≥ 1.
-/

namespace Imo2023P3

open BigOperators

determine solution_set {k : ℕ} (hk : 2 ≤ k) : Set (ℕ+ → ℕ+) := sorry

problem imo2023_p3 {k : ℕ} (hk : 2 ≤ k) (a : ℕ+ → ℕ+) :
    a ∈ solution_set hk ↔
    (∃ c : Fin (k+1) → ℕ+, c k = 1 ∧ ∀ n, (hn : 0 < n) →
      ∏ j : Fin k, a ⟨n + j.val + 1, Nat.succ_pos _⟩ =
      ∑ j : Fin (k + 1), ((a ⟨n, hn⟩).val)^j.val * c j) := by
  sorry
