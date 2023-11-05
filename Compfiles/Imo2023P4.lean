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

Let x₁, x₂, ... x₂₀₂₃ be distinct positive real numbers.
Define

   aₙ := √((x₁ + x₂ + ... + xₙ)(1/x₁ + 1/x₂ + ... + 1/xₙ)).

Suppose that aₙ is an integer for all n ∈ {1,...,2023}.
Prove that 3034 ≤ a₂₀₂₃.
-/

namespace Imo2023P4

open BigOperators

def iccCastLE {k n m : ℕ} (hn : n ≤ m) (i : Finset.Icc k n) : Finset.Icc k m :=
  ⟨i.val, Finset.Icc_subset_Icc_right hn i.prop⟩

noncomputable def a (x : Finset.Icc 1 2023 → ℝ) (n : ℕ) (hn : n ≤ 2023) : ℝ :=
  Real.sqrt ((∑ i : Finset.Icc 1 n, x (iccCastLE hn i)) *
             (∑ i : Finset.Icc 1 n, (1 / x (iccCastLE hn i))))

problem imo2023_p4
    (x : Finset.Icc 1 2023 → ℝ)
    (hxp : ∀ i, 0 < x i)
    (hxi : x.Injective)
    (hxa : ∀ i : Finset.Icc 1 2023, ∃ k : ℤ, a x i.val (by aesop) = k)
    : 3034 ≤ a x 2023 (by norm_num) := by
  sorry
