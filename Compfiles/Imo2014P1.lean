/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file

/-!
# International Mathematical Olympiad 2014, Problem 1

Let a₀ < a₁ < a₂ < ... an infinite sequence of positive integers.
Prove that there exists a unique integer n ≥ 1 such that

  aₙ < (a₀ + a₁ + ... + aₙ)/n ≤ aₙ₊₁.
-/

namespace Imo2014P1

open scoped BigOperators

snip begin

lemma lemma1 (s : ℕ → ℤ) (hs : ∀ i, s i < s (i + 1)) (z : ℤ) (hs0 : s 0 < z) :
    ∃! i, s i < z ∧ z ≤ s (i + 1) := by
  have hmono : StrictMono s := strictMono_nat_of_lt_succ hs

  let S := { i | z ≤ s (i + 1) }
  have h3 : ∃ j, j ∈ S := by
    have h1 : 0 < z - s 0 := Int.sub_pos_of_lt hs0
    have h5 : ∀ i, s 0 + i ≤ s i := fun i ↦ by
      induction' i with i ih
      · simp
      · have h10 : (Nat.succ i : ℤ) = (i : ℤ) + 1 := by norm_cast
        rw [h10, ←add_assoc]
        have h10 : s i + 1 ≤ s (Nat.succ i) := hs i
        linarith
    use Int.toNat (z - s 0)
    rw [Set.mem_setOf_eq]
    have h8 := h5 (Int.toNat (z - s 0))
    have h6 : 0 ≤ z - s 0 := by linarith
    have h7 : ((Int.toNat (z - s 0)) :ℤ) = z - s 0 := Int.toNat_of_nonneg h6
    rw [h7] at h8
    rw [add_sub_cancel'_right] at h8
    have h12 : s (Int.toNat (z - s 0)) < s (Int.toNat (z - s 0) + 1) := hs _
    linarith
  use Nat.find h3
  dsimp
  refine' ⟨⟨_, _⟩, _⟩
  · have h4 := Nat.find_min h3 (m := (Nat.find h3 - 1))
    cases' Nat.eq_zero_or_pos (Nat.find h3) with h5 h5
    · rwa [h5]
    · have h6 : Nat.find h3 - 1 < Nat.find h3 := by
        suffices H : Nat.find h3 < Nat.find h3 + 1 by
          exact Nat.sub_lt_right_of_lt_add h5 H
        exact Nat.lt.base (Nat.find h3)
      have h7 := h4 h6
      rw [Set.mem_setOf_eq] at h7
      push_neg at h7
      rwa [Nat.sub_add_cancel h5] at h7
  · exact Nat.find_spec h3
  · rintro m ⟨hm1, hm2⟩
    symm
    rw [Nat.find_eq_iff]
    refine' ⟨hm2, _⟩
    intro k hk
    intro hkk
    have h9 : s (k + 1) ≤ s m := (StrictMono.le_iff_le hmono).mpr hk
    linarith

snip end

problem imo2014_p1 (a : ℕ → ℤ) (apos : ∀ i, 0 < a i) (ha : ∀ i, a i < a (i + 1)) :
    ∃! n : ℕ, 0 < n ∧
              n * a n < (∑ i in Finset.range (n + 1), a i) ∧
              (∑ i in Finset.range (n + 1), a i) ≤ n * a (n + 1) := by
  -- Informal solution by Fedor Petrov, via Evan Chen:
  -- https://web.evanchen.cc/exams/IMO-2014-notes.pdf

  let b : ℕ → ℤ := fun i ↦ ∑ j in Finset.range i, (a i - a (j + 1))
  have hb : ∀ i, b i = i * a i - ∑ j in Finset.range i, a (j + 1) := by
    intro i
    simp [b]
  have hb1 : b 1 = 0 := by norm_num
  have hm : ∀ i, 0 < i → b i < b (i + 1) := by
    intro i hi0
    rw [hb, hb]
    rw [Finset.sum_range_succ]
    have hi := ha i
    push_cast
    nlinarith

  have hm' : ∀ i, b (i + 1) < b (i + 1 + 1) := fun i ↦ hm (i + 1) (Nat.succ_pos _)
  have h1 : ∀ j, (j + 1) * a (j + 1) < (∑ i in Finset.range (j + 2), a i) ↔
                 b (j + 1) < a 0 := fun j ↦ by
    rw [hb]
    constructor
    · intro hj
      suffices H : (↑j + 1) * a (j + 1) < ∑ j in Finset.range (j + 1), a (j + 1) + a 0 by
        exact Int.sub_left_lt_of_lt_add H
      rwa [Finset.sum_range_succ'] at hj
    · intro hj
      have H := Int.lt_add_of_sub_left_lt hj
      rwa [Finset.sum_range_succ']

  have h2 : ∀ j, (∑ i in Finset.range (j + 2), a i) ≤ (j + 1) * a (j + 2)  ↔
                 a 0 ≤ b (j + 2) := fun j ↦ by
    rw [hb]
    constructor
    · intro hj
      rw [Finset.sum_range_succ'] at hj
      rw [Finset.sum_range_succ]
      push_cast
      linarith
    · intro hj
      rw [Finset.sum_range_succ']
      rw [Finset.sum_range_succ] at hj
      push_cast at hj
      linarith

  have h3 : ∃! n, b (n + 1) < a 0 ∧ a 0 ≤ b (n + 2) :=
    lemma1 (fun i ↦ b (i + 1)) hm' (a 0) (hb1.trans_lt (apos 0))
  obtain ⟨n, ⟨hn1, hn2⟩, hn3⟩ := h3
  use n + 1
  dsimp only
  constructor
  · constructor
    · exact Nat.succ_pos n
    · constructor
      · push_cast
        rw [h1]
        exact hn1
      · push_cast
        rw [h2]
        exact hn2
  · rintro m ⟨hm1, hm2, hm3⟩
    have h5 := hn3 (m - 1)
    have h6 := h1 (m - 1)
    have h7 := h2 (m - 1)
    dsimp only at h5 h6
    suffices H : m - 1 = n by exact Nat.eq_add_of_sub_eq hm1 H
    apply h5
    have h8 : m - 1 + 1 = m := Nat.sub_add_cancel hm1
    have h9 : m - 1 + 2 = m + 1 := Nat.succ_inj'.mpr h8
    have h10 : (((m - 1):ℕ):ℤ) + 1 = ↑ m := by norm_cast
    rw [h8, h9, h10] at h6
    have h11 := h6.mp hm2
    rw [h9, h10] at h7
    have h12 := h7.mp hm3
    rw [h8, h9]
    exact ⟨h11, h12⟩
