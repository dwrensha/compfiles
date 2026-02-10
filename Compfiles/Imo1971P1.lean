/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Francesco Cappetti
-/

import Mathlib.Tactic
import Mathlib.Data.Fin.Tuple.Sort

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1971, Problem 1

Prove that the following assertion is true for n = 3 and n = 5, and that it is
false for every other natural number n > 2:

If a1, a2, ..., an are arbitrary real numbers, then
(a1 − a2)(a1 − a3) · · · (a1 − an) + (a2 − a1)(a2 − a3) · · · (a2 − an)
+ · · · + (an − a1)(an − a2) · · · (an − an−1) ≥ 0
-/

namespace Imo1971P1

def E {n : ℕ} (a : Fin n → ℝ) : ℝ :=
  ∑ i, ∏ j ≠ i, (a i - a j)

def P (n : ℕ) : Prop :=
  ∀ (a : Fin n → ℝ), E a ≥ 0

snip begin

-- This makes working with the sum easier and simp more powerful.
lemma prod_ne_eq_prod_ite {n : ℕ} {i : Fin n} {a : Fin n → ℝ} : ∏ j ≠ i, (a i - a j) = ∏ j, if j = i then 1 else a i - a j := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  grind [Finset.prod_congr]

-- A proof that E a = E b, where b is obtained by permuting a's indices.
lemma E_equiv_perm {n : ℕ} {a b : Fin n → ℝ} (h : ∃ σ : Equiv.Perm (Fin n), b = a ∘ σ) : E a = E b := by
  obtain ⟨σ, hσ⟩ := h
  simp [E]
  apply Finset.sum_equiv (e := σ.symm) (by simp)
  intro i hi
  apply Finset.prod_equiv (e := σ.symm) (by simp)
  intro j hj
  simp [hσ, Equiv.apply_symm_apply]

-- This gets a permutation of the indices of a such that the resulting sequence is antitone.
-- Uses Tuple.sort (which gives monotone) composed with Fin.revPerm (which reverses) to get antitone.
lemma antitone_of_monotone_comp_rev {n : ℕ} (f : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (hm : Monotone (f ∘ σ)) : Antitone (f ∘ σ ∘ Fin.revPerm) := by
  intro i j hij
  simp only [Function.comp_apply]
  exact hm (by simp [Fin.revPerm_apply, Fin.rev_le_rev, hij])

lemma exists_antitone_perm {n : ℕ} (a : Fin n → ℝ) :
    ∃ b, ∃ σ : Equiv.Perm (Fin n), b = a ∘ σ ∧ Antitone b := by
  let σ : Equiv.Perm (Fin n) := Tuple.sort a * Fin.revPerm
  use a ∘ σ, σ
  constructor
  · rfl
  · simp only [σ, Equiv.Perm.coe_mul, Function.comp_def]
    exact antitone_of_monotone_comp_rev a _ (Tuple.monotone_sort a)

snip end

problem imo1971_p1 : P 3 ∧ P 5 ∧ ∀ n > 2, n ≠ 3 ∧ n ≠ 5 → ¬P n := by
  -- Solution from https://artofproblemsolving.com/wiki/index.php/1971_IMO_Problems/Problem_1

  -- Note that indices start from 0 in the formalization

  -- Show that P is false for even n > 2
  have h1 : ∀ n > 2, Even n → ¬P n := by
    intro n n_gt_2 n_even

    have n_pos : 0 < n := by lia

    -- Rewriting now lets us decompose the sum later
    rw [show n = n - 1 + 1 by lia]
    simp [P]

    -- Our counterexample
    let a : Fin (n - 1 + 1) → ℝ := fun i ↦ if i = 0 then -1 else 0
    use a

    rw [E, Fin.sum_univ_succ]

    -- Show that the first term is negative
    have h₀ : ∏ j ≠ 0, (a 0 - a j) = -1 := by
      rw [prod_ne_eq_prod_ite]
      simp [Finset.prod, a, Odd.neg_one_pow (Nat.Even.sub_odd n_pos n_even odd_one)]

    -- Show that the sum of the remaining terms is zero, by showing that every remaining term is zero
    have h₁ : ∑ i : Fin (n - 1), ∏ j ≠ i.succ, (a i.succ - a j) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.prod_eq_zero_iff]
      by_cases hi' : i.succ = ⟨2, by linarith [Nat.sub_one_add_one_eq_of_pos n_pos]⟩
      · use ⟨1, by linarith [Nat.sub_one_add_one_eq_of_pos n_pos]⟩
        simp [hi', a]
      · use ⟨2, by linarith [Nat.sub_one_add_one_eq_of_pos n_pos]⟩
        simp [hi', a, eq_comm]

    -- Close the goal
    linarith

  -- Show that P is false for n ≥ 7
  have h2 : ∀ n ≥ 7, Odd n → ¬P n := by
    intro n n_ge_7 n_odd

    have n_pos : 4 ≤ n := by lia

    -- Rewriting now lets us decompose the sum later
    rw [show n = n - 4 + 4 by lia]
    simp [P]

    -- Our counterexample
    let a : Fin (n - 4 + 4) → ℝ := fun i ↦ if i = 0 then 2 else if i = 1 ∨ i = 2 ∨ i = 3 then 1 else 3
    use a

    simp [E, Fin.sum_univ_succ]

    -- Show that the first term is negative
    have h₀ : ∏ j ≠ 0, (a 0 - a j) < 0 := by
      rw [prod_ne_eq_prod_ite]
      have h_0 : Fin.succ (2 : Fin (n - 4 + 3)) = 3 := rfl
      have h_1 {i : Fin (n - 4)} : i.succ.succ.succ.succ ≠ 1 := not_eq_of_beq_eq_false rfl
      have h_2 {i : Fin (n - 4)} : i.succ.succ.succ.succ ≠ 2 := not_eq_of_beq_eq_false rfl
      have h_3 {i : Fin (n - 4)} : i.succ.succ.succ.succ ≠ 3 := not_eq_of_beq_eq_false rfl
      simp [Fin.prod_univ_succ, a, h_0,  h_1, h_2, h_3]
      calc ((2 : ℝ) - 1) * ((2 - 1) * ((2 - 1) * (2 - 3) ^ (n - 4)))
        _ = (-1) ^ (n - 4) := by norm_num
        _ < 0 := by simp [(Nat.Odd.sub_even n_pos n_odd (show Even 4 by norm_num)).neg_one_pow]

    -- Prove that the second, third and fourth terms are zero
    have h₁ : ∏ j ≠ 1, (a 1 - a j) = 0 := by
      rw [Finset.prod_eq_zero_iff]
      use ⟨2, by lia⟩
      simp [a]
      norm_cast
    have h₂ : ∏ j ≠ 2, (a 2 - a j) = 0 := by
      rw [prod_ne_eq_prod_ite, Finset.prod_eq_zero_iff]
      use ⟨1, by lia⟩
      simp [a]
      norm_cast
    have h₃ : ∏ j ≠ Fin.succ 2, (a (Fin.succ 2) - a j) = 0 := by
      rw [prod_ne_eq_prod_ite, Finset.prod_eq_zero_iff]
      use ⟨1, by lia⟩
      simp [a]
      norm_cast

    -- Show that the sum of the remaining terms is zero, by showing that every remaining term is zero
    have h₄ : ∑ i : Fin (n - 4), ∏ j ≠ i.succ.succ.succ.succ, (a i.succ.succ.succ.succ - a j) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      apply Finset.prod_eq_zero_iff.mpr
      by_cases hi' : i.succ.succ.succ.succ = ⟨4, by lia⟩
      · use ⟨5, by lia⟩
        simp [hi', a]
        norm_cast
      · use ⟨4, by lia⟩
        simp [hi', a, eq_comm]
        norm_cast

    -- Close the goal
    linarith

  -- Case n = 3
  constructor
  · simp [P]
    intro a

    -- WLOG we assume that a is sorted in non-increasing order
    wlog h : a 0 ≥ a 1 ∧ a 1 ≥ a 2
    · -- We need to show that we can always "go back" to the sorted case
      obtain ⟨b, ⟨σ, ⟨hσ, b_Antitone⟩⟩⟩ := exists_antitone_perm a

      -- We can now prove that b is sorted
      have b0_ge_b1 : b 0 ≥ b 1 := b_Antitone (by simp)
      have b1_ge_b2 : b 1 ≥ b 2 := b_Antitone (by simp)

      rw [E_equiv_perm ⟨σ, hσ⟩]
      exact this h1 h2 b ⟨b0_ge_b1, b1_ge_b2⟩
    · -- Unfold the expression, as n is small
      simp [E, prod_ne_eq_prod_ite]
      simp [Finset.sum, Finset.prod]

      -- Show that the sum of the first two terms is non-negative
      have h₁ : 0 ≤ (a 0 - a 1) * (a 0 - a 2) + (a 1 - a 0) * (a 1 - a 2) := by
        rw [← sub_neg_eq_add, sub_nonneg]
        calc -((a 1 - a 0) * (a 1 - a 2))
          _ = (a 0 - a 1) * (a 1 - a 2) := by rw [← neg_sub, neg_mul, neg_neg]
          _ ≤ (a 0 - a 1) * (a 0 - a 2) := by apply mul_le_mul <;> lia

      -- Show that the third term is also non-negative
      have h₂ : 0 ≤ (a 2 - a 0) * (a 2 - a 1) := by apply mul_nonneg_of_nonpos_of_nonpos <;> linarith

      -- Close the goal
      linarith

  -- Case n = 5
  constructor
  · simp [P]

    -- WLOG we assume that a is sorted in non-increasing order
    intro a
    wlog h : a 0 ≥ a 1 ∧ a 1 ≥ a 2 ∧ a 2 ≥ a 3 ∧ a 3 ≥ a 4
    · -- We need to show that we can always "go back" to the sorted case
      obtain ⟨b, ⟨σ, ⟨hσ, b_Antitone⟩⟩⟩ := exists_antitone_perm a

      -- We can now prove that b is sorted
      have b0_ge_b1 : b 0 ≥ b 1 := b_Antitone (by simp)
      have b1_ge_b2 : b 1 ≥ b 2 := b_Antitone (by simp)
      have b2_ge_b3 : b 2 ≥ b 3 := b_Antitone (by simp)
      have b3_ge_b4 : b 3 ≥ b 4 := b_Antitone (by simp)

      rw [E_equiv_perm ⟨σ, hσ⟩]
      exact this h1 h2 b ⟨b0_ge_b1, ⟨b1_ge_b2, ⟨b2_ge_b3, b3_ge_b4⟩⟩⟩
    · -- Unfold the expression, as n is small
      simp [E, prod_ne_eq_prod_ite]
      simp [Finset.sum, Finset.prod]

      -- Show that the sum of the first two terms is non-negative
      have h₁ : 0 ≤ (a 0 - a 1) * ((a 0 - a 2) * ((a 0 - a 3) * (a 0 - a 4))) +
          (a 1 - a 0) * ((a 1 - a 2) * ((a 1 - a 3) * (a 1 - a 4))) := by
        rw [← neg_sub (a 0) (a 1), neg_mul, ← sub_eq_add_neg, ← mul_sub]
        apply mul_nonneg
        · linarith
        · rw [sub_nonneg]
          apply mul_le_mul
          · linarith
          · apply mul_le_mul <;> linarith
          · apply mul_nonneg <;> linarith
          · linarith

      -- Show that the third term is non-negative
      have h₂ : 0 ≤ (a 2 - a 0) * ((a 2 - a 1) * ((a 2 - a 3) * (a 2 - a 4))) := by
        rw [← neg_sub (a 0) (a 2), ← neg_sub (a 1) (a 2), ← mul_assoc, neg_mul_neg]
        apply mul_nonneg <;> apply mul_nonneg <;> linarith

      -- Show that the sum of the last two terms is non-negative
      have h₃ : 0 ≤ (a 3 - a 0) * ((a 3 - a 1) * ((a 3 - a 2) * (a 3 - a 4))) +
          (a 4 - a 0) * ((a 4 - a 1) * ((a 4 - a 2) * (a 4 - a 3))) := by
        simp [← mul_assoc]
        rw [← neg_sub (a 3) (a 4), mul_neg, ← sub_eq_add_neg, ← sub_mul]
        have hp : (a 3 - a 0) * (a 3 - a 1) * (a 3 - a 2) = -((a 0 - a 3) * (a 1 - a 3) * (a 2 - a 3)) := by linarith
        have hq : (a 4 - a 0) * (a 4 - a 1) * (a 4 - a 2) = -((a 0 - a 4) * (a 1 - a 4) * (a 2 - a 4)) := by linarith
        rw [hp, hq, sub_neg_eq_add, add_comm, ← sub_eq_add_neg]
        apply mul_nonneg
        · rw [sub_nonneg]
          apply mul_le_mul
          · apply mul_le_mul <;> linarith
          · linarith
          · linarith
          · apply mul_nonneg <;> linarith
        · lia

      -- Close the goal
      linarith

  -- Case n > 2
  · grind


end Imo1971P1
