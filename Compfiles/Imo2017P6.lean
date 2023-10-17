/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import Compfiles.Meta.ProblemExtraction

problem_file

/-!
# International Mathematical Olympiad 2017, Problem 6

A point (x,y) ∈ ℤ × ℤ is called primitive if gcd(x,y) = 1.
Let S be a finite set of primitive points.
Prove that there exists n > 0 and integers a₀,a₁,...,aₙ
such that

  a₀xⁿ + a₁xⁿ⁻¹y + a₂xⁿ⁻²y² + ... + aₙ₋₁xyⁿ⁻¹ + aₙyⁿ = 1

for each (x,y) ∈ S.

-/

namespace Imo2017P6

open scoped BigOperators

problem imo2017_p6 (S : Finset (ℤ × ℤ)) (hS : ∀ s ∈ S, gcd s.1 s.2 = 1) :
    ∃ n : ℕ, 0 < n ∧ ∃ a : ℕ → ℤ,
      ∀ s ∈ S, ∑ i in Finset.range n, a i * s.1 ^ i * s.2 ^ (n - i) = 1 := by
  sorry
