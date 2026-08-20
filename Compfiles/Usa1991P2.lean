/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Rat.Star
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 1991, Problem 2

For each non-empty subset of {1, 2, ... , n} take the sum of the elements
divided by the product. Show that the sum of the resulting quantities is
n² + 2n - (n + 1)sₙ, where sₙ = 1 + 1/2 + 1/3 + ... + 1/n.
-/

namespace Usa1991P2

open Finset

snip begin

/-- `{1, ..., n+1}` is `{1, ..., n}` with `n + 1` adjoined. -/
lemma icc_one_succ (n : ℕ) : Icc 1 (n + 1) = insert (n + 1) (Icc 1 n) := by
  ext i
  simp only [mem_Icc, mem_insert]
  lia

lemma not_mem_icc_one (n : ℕ) : n + 1 ∉ Icc 1 n := by
  simp only [mem_Icc]
  lia

/-- Splitting the quantity attached to `insert (n + 1) T` for `T ⊆ {1, ..., n}`:
the sum of the elements increases by `n + 1` while the product is multiplied
by `n + 1`. -/
lemma sum_div_prod_insert (n : ℕ) {T : Finset ℕ} (hT : T ⊆ Icc 1 n) :
    (∑ i ∈ insert (n + 1) T, (i : ℚ)) / (∏ i ∈ insert (n + 1) T, (i : ℚ)) =
      (1 / (n + 1 : ℚ)) * ((∑ i ∈ T, (i : ℚ)) / (∏ i ∈ T, (i : ℚ))) +
        1 / (∏ i ∈ T, (i : ℚ)) := by
  have ha : n + 1 ∉ T := fun h ↦ not_mem_icc_one n (hT h)
  have hpos : 0 < ∏ i ∈ T, (i : ℚ) :=
    prod_pos (fun i hi ↦ by
      have h1 := hT hi
      simp only [mem_Icc] at h1
      exact_mod_cast h1.1)
  have hprod : ∏ i ∈ T, (i : ℚ) ≠ 0 := hpos.ne'
  have hn1 : ((n : ℚ) + 1) ≠ 0 := by positivity
  rw [sum_insert ha, prod_insert ha]
  push_cast
  field_simp
  ring

/-- The telescoping product `∏ (1 + 1/i) = n + 1`. -/
lemma prod_one_add_inv (n : ℕ) : ∏ i ∈ Icc 1 n, (1 + ((i : ℚ))⁻¹) = (n + 1 : ℚ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_Icc_succ_top (show 1 ≤ n + 1 by lia), ih]
    have hn : (n : ℚ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp

/-- The sum of `1 / ∏` over all subsets of `{1, ..., n}` (the empty set
contributes `1`) telescopes to `n + 1`. -/
lemma sum_powerset_one_div_prod (n : ℕ) :
    ∑ T ∈ (Icc 1 n).powerset, (1 : ℚ) / (∏ i ∈ T, (i : ℚ)) = (n + 1 : ℚ) := by
  have h1 : ∑ T ∈ (Icc 1 n).powerset, (1 : ℚ) / (∏ i ∈ T, (i : ℚ)) =
      ∑ T ∈ (Icc 1 n).powerset, ∏ i ∈ T, ((i : ℚ))⁻¹ := by
    refine sum_congr rfl fun T _ ↦ ?_
    rw [one_div, ← prod_inv_distrib]
  rw [h1, ← prod_one_add, prod_one_add_inv]

/-- Induction step for the main sum: a subset of `{1, ..., n+1}` either is a
subset of `{1, ..., n}` or has the form `insert (n+1) T` with `T ⊆ {1, ..., n}`. -/
lemma main_sum_succ (n : ℕ) :
    ∑ S ∈ (Icc 1 (n + 1)).powerset, (∑ i ∈ S, (i : ℚ)) / (∏ i ∈ S, (i : ℚ)) =
      (∑ S ∈ (Icc 1 n).powerset, (∑ i ∈ S, (i : ℚ)) / (∏ i ∈ S, (i : ℚ))) +
        ((1 / (n + 1 : ℚ)) *
            (∑ S ∈ (Icc 1 n).powerset, (∑ i ∈ S, (i : ℚ)) / (∏ i ∈ S, (i : ℚ))) +
          (n + 1 : ℚ)) := by
  have key : ∑ T ∈ (Icc 1 n).powerset,
        (∑ i ∈ insert (n + 1) T, (i : ℚ)) / (∏ i ∈ insert (n + 1) T, (i : ℚ)) =
      (1 / (n + 1 : ℚ)) *
          (∑ S ∈ (Icc 1 n).powerset, (∑ i ∈ S, (i : ℚ)) / (∏ i ∈ S, (i : ℚ))) +
        (n + 1 : ℚ) := by
    have h2 : ∀ T ∈ (Icc 1 n).powerset,
        (∑ i ∈ insert (n + 1) T, (i : ℚ)) / (∏ i ∈ insert (n + 1) T, (i : ℚ)) =
          (1 / (n + 1 : ℚ)) * ((∑ i ∈ T, (i : ℚ)) / (∏ i ∈ T, (i : ℚ))) +
            1 / (∏ i ∈ T, (i : ℚ)) := by
      intro T hT
      rw [mem_powerset] at hT
      exact sum_div_prod_insert n hT
    rw [sum_congr rfl h2, sum_add_distrib, ← mul_sum, sum_powerset_one_div_prod]
  rw [icc_one_succ, sum_powerset_insert (not_mem_icc_one n), key]

snip end

problem usa1991_p2 (n : ℕ) :
    ∑ S ∈ (Finset.Icc 1 n).powerset.erase ∅, (∑ i ∈ S, (i : ℚ)) / (∏ i ∈ S, (i : ℚ)) =
      (n : ℚ)^2 + 2 * n - (n + 1) * ∑ i ∈ Finset.Icc 1 n, (1 : ℚ) / i := by
  have herase : ∀ n : ℕ,
      ∑ S ∈ (Finset.Icc 1 n).powerset.erase ∅, (∑ i ∈ S, (i : ℚ)) / (∏ i ∈ S, (i : ℚ)) =
        ∑ S ∈ (Finset.Icc 1 n).powerset, (∑ i ∈ S, (i : ℚ)) / (∏ i ∈ S, (i : ℚ)) := by
    intro n
    refine Finset.sum_erase _ ?_
    simp
  rw [herase]
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit : ∑ i ∈ Finset.Icc 1 (n + 1), (1 : ℚ) / i =
        (∑ i ∈ Finset.Icc 1 n, (1 : ℚ) / i) + (1 : ℚ) / (n + 1 : ℕ) := by
      rw [sum_Icc_succ_top (show 1 ≤ n + 1 by lia)]
    rw [main_sum_succ, ih, hsplit]
    have hn : (n : ℚ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp
    ring

end Usa1991P2
