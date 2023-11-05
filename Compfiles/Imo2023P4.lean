/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import Compfiles.Meta.ProblemExtraction

problem_file

/-!
# International Mathematical Olympiad 2023, Problem 4

Let x₀, x₁, ... x₂₀₂₂ be distinct positive real numbers.
Define

   aₙ := √((x₀ + x₁ + ... + xₙ)(1/x₀ + 1/x₁ + ... + 1/xₙ)).

Suppose that aₙ is an integer for all n ∈ {0,1,...,2022}.
Prove that 3034 ≤ a₂₀₂₂.
-/

namespace Imo2023P4

open BigOperators

noncomputable def a (x : Fin 2023 → ℝ) (n : Fin 2023) : ℝ :=
  Real.sqrt ((∑ i : Fin n.val, x ⟨i, Nat.lt_trans i.prop n.prop⟩) *
             (∑ i : Fin n.val, (1 / x ⟨i, Nat.lt_trans i.prop n.prop⟩)))

problem imo2023_p4
    (x : Fin 2023 → ℝ)
    (hxp : ∀ i, 0 < x i)
    (hxi : x.Injective)
    (hxa : ∀ i, ∃ k : ℤ, a i = k)
    : 3034 ≤ a x ⟨2022, by norm_num⟩ := by
  sorry
