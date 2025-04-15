/-
Copyright (c) 2025 the Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file {
  tags := [.NumberTheory]
}

/-!
# International Mathematical Olympiad 2022, Problem 3

Let k be a positive integer and let S be a finite set of odd prime
integers. Prove that there is at most one way (up to rotation and reflection)
to place the elements of S around a circle such that the product of any
two neighbors is of the form x² + x + k for some positive integer x.

-/

namespace Imo2022P3


open scoped Finset

/-- The condition of the problem on a placement of numbers round a circle. -/
def Condition (k : ℕ) (S : Finset ℕ) (p : ZMod #S ≃ S) : Prop :=
  ∀ i, ∃ x : ℕ, 0 < x ∧ ((p i : ℕ) * (p (i + 1) : ℕ)) = x ^ 2 + x + k

problem imo2023_p3
    {k : ℕ} (hk : 0 < k) (S : Finset ℕ) (hS : ∀ p ∈ S, Odd p ∧ Nat.Prime p)
    {p₁ p₂ : ZMod #S ≃ S} (hp₁ : Condition k S p₁) (hp₂ : Condition k S p₂) :
    (∃ i, ∀ j, p₂ j = p₁ (j + i)) ∨ ∃ i, ∀ j, p₂ j = p₁ (-j + i) := by
  sorry

end Imo2022P3
