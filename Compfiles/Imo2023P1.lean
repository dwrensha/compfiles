/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import Compfiles.Meta.ProblemExtraction

problem_file

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
  ∀ i, (hi2 : i + 2 < divs.length) →
    have hi1 : i + 1 < divs.length := Nat.lt_of_succ_lt hi2
    have hi : i < divs.length := Nat.lt_of_succ_lt hi1
    divs.get ⟨i, hi⟩ ∣ divs.get ⟨i + 1, hi1⟩ + divs.get ⟨i + 2, hi2⟩

problem imo2023_p1 : solution_set = { n | 1 < n ∧ ¬n.Prime ∧ P n } := by
  ext x
  constructor
  · sorry
  · sorry
