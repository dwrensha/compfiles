/-
Copyright (c) 2023 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
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

determine SolutionSet {k : ℕ} (hk : 2 ≤ k) : Set (ℕ+ → ℕ+) := sorry

problem imo2023_p3 {k : ℕ} (hk : 2 ≤ k) (a : ℕ+ → ℕ+) :
    a ∈ SolutionSet hk ↔
    (∃ P : Polynomial ℤ, P.Monic ∧ P.degree = k ∧
     (∀ n, n ≤ k → 0 ≤ P.coeff n) ∧
      ∀ n : ℕ+,
        P.eval ((a n) : ℤ) =
        ∏ i ∈ Finset.range k, a ⟨n + i + 1, Nat.succ_pos _⟩) := by
  sorry
