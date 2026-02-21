/-
Copyright (c) 2025 Francesco Vercellesi· All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Francesco Vercellesi
-/

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Finite.Card
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 1989, Problem 1

Prove that the integers from 1 to 1989 can be partitioned in 117 sets
of 17 elements each, all with the same sum of elements.
-/

namespace Imo1989P1

abbrev S := Finset.Icc 1 1989

snip begin

def n : ℕ := 117

def row (j : ℕ) (i : Fin n) : ℕ :=
  if j < 14 then
    if j % 2 = 0 then j * n + i.val + 1
    else (j + 1) * n - i.val
  else if j = 14 then 14 * n + i.val + 1
  else if j = 15 then 15 * n + (i.val + 58) % n + 1
  else 16 * n + (2 * n - 1 - 2 * i.val) % n + 1

def A (i : Fin n) : Set ℕ := { row j i | j < 17 }

lemma row_quot (j : ℕ) (hj : j < 17) (i : Fin n) : (row j i - 1) / n = j := by
  unfold row; split_ifs <;> (simp [n] at *; omega)

lemma row_inj {j1 j2 : ℕ} {i1 i2 : Fin n} (hj1 : j1 < 17) (hj2 : j2 < 17) :
    row j1 i1 = row j2 i2 ↔ j1 = j2 ∧ i1 = i2 := by
  constructor
  · intro h
    have hj : j1 = j2 := by
      have h1 := row_quot j1 hj1 i1
      have h2 := row_quot j2 hj2 i2
      rw [h] at h1
      exact h1.symm.trans h2
    refine ⟨hj, ?_⟩; subst hj; apply Fin.ext; unfold row at h; split_ifs at h <;> (simp [n] at *; try omega)
  · rintro ⟨rfl, rfl⟩; rfl

lemma A_finite (i : Fin n) : (A i).Finite := by
  have : A i = (λ j ↦ row j i) '' Set.Iio 17 := by ext; simp [A, Set.Iio]
  rw [this]; exact (Set.finite_Iio 17).image _

lemma A_card (i : Fin n) : Set.ncard (A i) = 17 := by
  have : A i = (λ j ↦ row j i) '' Set.Iio 17 := by ext; simp [A, Set.Iio]
  rw [this]
  rw [Set.InjOn.ncard_image]
  · rw [Set.ncard_Iio_nat 17]
  · intro j1 hj1 j2 hj2 h
    exact ((row_inj hj1 hj2).1 h).1

lemma A_sum (i : Fin n) : ∑ᶠ a ∈ A i, a = 16915 := by
  have hA : A i = ↑(Finset.image (λ j ↦ row j i) (Finset.range 17)) := by
    ext x; simp [A]
  rw [hA, finsum_mem_coe_finset]
  rw [Finset.sum_image (fun j1 hj1 j2 hj2 h =>
    ((row_inj (Finset.mem_range.mp hj1) (Finset.mem_range.mp hj2)).1 h).1)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [row]
  norm_num [n]
  have hi := i.isLt; simp only [n] at hi
  by_cases h59 : i.val < 59
  · have h1 : (i.val + 58) % 117 = i.val + 58 := Nat.mod_eq_of_lt (by omega)
    have h2 : (233 - 2 * i.val) % 117 = 116 - 2 * i.val := by
      have : 233 - 2 * i.val = 117 + (116 - 2 * i.val) := by omega
      rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    omega
  · have h1 : (i.val + 58) % 117 = i.val - 59 := by
      have : i.val + 58 = 117 + (i.val - 59) := by omega
      rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    have h2 : (233 - 2 * i.val) % 117 = 233 - 2 * i.val := Nat.mod_eq_of_lt (by omega)
    omega

snip end

problem imo1989_p1 : ∃ (A : Fin 117 → Set ℕ),
    S = ⨆ i : Fin 117, A i ∧
    ∀ i j, i ≠ j → Disjoint (A i) (A j) ∧
    Set.ncard (A i) = 17 ∧
    ∑ᶠ a ∈ A i, a = ∑ᶠ a ∈ A j, a := by
  refine ⟨A, ?_, λ i j hij ↦ ⟨?_, A_card i, by rw [A_sum, A_sum]⟩⟩
  · symm; apply Set.eq_of_subset_of_ncard_le (ht := S.finite_toSet)
    · simp only [Set.iSup_eq_iUnion, Set.iUnion_subset_iff]; intro i x hx; rcases hx with ⟨j, hj, rfl⟩
      unfold row; simp [S]; split_ifs <;> (simp [n]; omega)
    · simp only [Set.iSup_eq_iUnion]
      have h := Set.ncard_iUnion_of_finite (λ i ↦ A_finite i) (λ i j h ↦ ?_)
      · rw [finsum_eq_sum_of_fintype] at h; simp [A_card, S, n] at h ⊢; omega
      · simp only [Function.onFun, Set.disjoint_left]
        intro x hx hy; rcases hx with ⟨j1, hj1, rfl⟩; rcases hy with ⟨j2, hj2, h_eq⟩
        exact h ((row_inj hj1 hj2).1 h_eq.symm).2
  · rw [Set.disjoint_left]; intro x hx hy; rcases hx with ⟨j1, hj1, rfl⟩; rcases hy with ⟨j2, hj2, h_eq⟩
    have h := (row_inj hj1 hj2).1 h_eq.symm
    exact hij h.2

end Imo1989P1
