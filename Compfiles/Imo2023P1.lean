/-
Copyright (c) 2023 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 2023, Problem 1

Determine all composite integers n>1 that satisfy the following property:
if d₁,d₂,...,dₖ are all the positive divisors of n with 1=d₁<d₂<...<dₖ=n,
then dᵢ divides dᵢ₊₁ + dᵢ₊₂ for every 1 ≤ i ≤ k-2.
-/

namespace Imo2023P1

determine solution_set : Set ℕ := { n | n.factors.length = 2 ∧ n.factors.Nodup }

abbrev P (n : ℕ) : Prop :=
  let divs := n.divisors.sort LE.le
  ∀ i, (h : i + 2 < divs.length) →
    divs.get ⟨i, Nat.lt_of_succ_lt (Nat.lt_of_succ_lt h)⟩ ∣
      divs.get ⟨i + 1, Nat.lt_of_succ_lt h⟩ + divs.get ⟨i + 2, h⟩

problem imo2023_p1 : solution_set = { n | 1 < n ∧ ¬n.Prime ∧ P n } := by
  ext x
  constructor
  · sorry
  · sorry
