/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file

/-!
# International Mathematical Olympiad 2014, Problem 1

Let a₀ < a₁ < a₂ < ... an infinite sequence of positive integers.
Prove that there exists a unique integer n ≥ 1 such that

  aₙ < (a₀ + a₁ + ... + aₙ)/n ≤ aₙ₊₁.
-/

namespace Imo2014P1

open scoped BigOperators

problem imo2014_p1 (a : ℕ → ℤ) (apos : ∀ i, 0 < a i) (ha : ∀ i, a i < a (i + 1)) :
    ∃! n : ℕ, 0 < a ∧
              a n < (∑ i in Finset.range (n + 1), a i)/n ∧
              (∑ i in Finset.range (n + 1), a i)/n ≤ a (n + 1) := by
  -- Informal solution by Fedor Petrov, via Evan Chen:
  -- https://web.evanchen.cc/exams/IMO-2014-notes.pdf

--  let b : ℕ → ℤ := fun i ↦ ∑ j in Finset.range i, (a (i + 1) - a (j + 1))
  let b : ℕ → ℤ := fun i ↦ i * a (i + 1) - ∑ j in Finset.range i, a (j + 1)
  have hb0 : b 0 = 0 := by norm_num
  have hm : ∀ i, b i < b (i + 1) := by
    intro i
    dsimp only [b]
    rw [Finset.sum_range_succ]
    have hi := ha i
    have his := ha (i + 1)
    push_cast
    nlinarith
  sorry
