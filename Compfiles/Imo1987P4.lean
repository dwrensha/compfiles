/-
Copyright (c) 2023 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1987, Problem 4

Prove that there is no function f : ℕ → ℕ such that f(f(n)) = n + 1987
for every n.
-/

namespace Imo1987P4

problem imo1987_p4 : ¬∃ f : ℕ → ℕ, ∀ n, f (f n) = n + 1987 := by
  -- Informal solution by Sawa Pavlov, listed at
  -- https://artofproblemsolving.com/wiki/index.php/1987_IMO_Problems/Problem_4

  -- We will prove a more general statement.
  suffices generalized : ∀ m : ℕ, ¬∃ f : ℕ → ℕ, ∀ n, f (f n) = n + (2 * m + 1) from
    generalized 993

  rintro m ⟨f, hf⟩

  -- Note that f is injective, because if f(x) = f(y),
  -- then f(f(x)) = f(f(y)), so x = y.
  have f_injective : f.Injective := by
    intro x y hxy;
    have hfx := hf x;
    rw [hxy, hf y] at hfx
    exact Nat.add_right_cancel hfx.symm

  -- Let A := ℕ - f(ℕ) and B := f(A).
  let A : Set ℕ := Set.univ \ (f '' Set.univ)
  let B : Set ℕ := f '' A

  -- A and B have union ℕ - f(f(ℕ)).
  have ab_union : A ∪ B = Set.univ \ (f '' (f '' Set.univ)) := by
    -- Note that B = f(ℕ) - f(f(ℕ)).
    simp only [B, Set.image_diff f_injective]
    exact Set.diff_union_diff_cancel
      (Set.subset_univ _) (Set.image_mono (Set.subset_univ _))

  -- ... which is {0, 1, ... , 2 * m}.
  have ab_range : A ∪ B = {n | n < 2 * m + 1} := by
    rw [ab_union]
    ext x
    rw [Set.mem_setOf_eq, ←not_iff_not, ←Set.compl_eq_univ_diff]
    rw [Set.not_mem_compl_iff, not_lt]
    simp only [Set.mem_image, Set.mem_univ, true_and, exists_exists_eq_and, hf]
    rw [le_iff_exists_add']
    simp_rw [eq_comm]

  -- A and B are disjoint.
  have ab_disjoint : Disjoint A B := by
    intro C hca hcb c hc
    exact Set.not_mem_of_mem_diff (hca hc) (Set.image_subset f sdiff_le (hcb hc))

  -- But since f is injective, A and B have the
  -- same number of elements, which is impossible since {0, 1, ... , 2 * m}
  -- has an odd number of elements.

  have ab_card : Set.ncard (A ∪ B) = 2 * m + 1 := by
    rw [ab_range, Set.Iio_def, ←Finset.coe_range, Set.ncard_coe_Finset]
    exact Finset.card_range (2 * m + 1)

  have ab_finite : (A ∪ B).Finite := by
    rw [ab_range]; exact Set.finite_lt_nat _
  obtain ⟨a_finite, b_finite⟩ := Set.finite_union.mp ab_finite

  rw [Set.ncard_union_eq ab_disjoint a_finite b_finite] at ab_card
  rw [Set.ncard_image_of_injective _ f_injective] at ab_card
  omega


end Imo1987P4
