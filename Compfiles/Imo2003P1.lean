/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 2003, Problem 1

Let A be a 101-element subset of S = {1,2,...10⁶}. Prove
that there exist numbers t₁, t₂, ..., t₁₀₀ such that the sets

     Aⱼ = {x + tⱼ | x ∈ A},     j = 1,2, ..., 100

are pairwise disjoint.
-/

namespace Imo2003P1

abbrev S : Finset ℕ := Finset.Icc 1 (10^6)

problem imo2003_p1 (A : Finset ℕ) (hA : A ⊆ S) :
    ∃ t : Fin 100 → S,
      ∀ i j, i ≠ j → {x + t i | x ∈ A} ≠ {x + t j | x ∈ A} := by
  sorry
