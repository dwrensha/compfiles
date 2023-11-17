/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file

/-!
# International Mathematical Olympiad 2016, Problem 5

The equation

  (x - 1)(x - 2) ... (x - 2016)  = (x - 1)(x - 2) ... (x - 2016)

is written on the board. What is the least possible value of k
for which it is possible to erase exactly k of these 4032 factors
such that at least one factor remains on each side and the resulting
equation has no real solutions?
-/

namespace Imo2016P5

open scoped BigOperators

determine solution_value : ℕ := 2016

problem imo2015_p5 :
    IsLeast { k | ∃ L R : Finset ℕ,
                  L ⊂ Finset.Icc 1 2016 ∧
                  R ⊂ Finset.Icc 1 2016 ∧
                  L.card + R.card = k ∧
                  ¬∃ x : ℝ,
                   ∏ i in Finset.Icc 1 2016, (if i ∈ L then 1 else (x - (i : ℝ))) =
                   ∏ i in Finset.Icc 1 2016, (if i ∈ R then 1 else (x - (i : ℝ))) }
            solution_value := by
  constructor
  · rw [Set.mem_setOf_eq]
    -- We follow the proof from Evan Chen:
    -- https://web.evanchen.cc/exams/IMO-2016-notes.pdf
    use (Finset.Icc 1 2016).filter (fun n ↦ n % 4 = 2 ∨ n % 4 = 3)
    use (Finset.Icc 1 2016).filter (fun n ↦ n % 4 = 0 ∨ n % 4 = 1)
    refine' ⟨_,_,_,_⟩
    · refine ⟨Finset.filter_subset _ _, ?_⟩
      intro h
      have h1 : 1 ∈ Finset.Icc 1 2016 := by
        simp (config := {decide := true}) only [Finset.mem_Icc]
      have h2 := h h1
      simp [Finset.mem_Icc, Finset.mem_filter] at h2
    · refine ⟨Finset.filter_subset _ _, ?_⟩
      intro h
      have h1 : 2 ∈ Finset.Icc 1 2016 := by
        simp (config := {decide := true}) only [Finset.mem_Icc]
      have h2 := h h1
      simp only [Finset.mem_Icc, Finset.mem_filter] at h2
      norm_num at h2
    · sorry
    · push_neg
      intro x
      sorry
  · rw [mem_lowerBounds]
    intro j hj
    by_contra' H
    rw [Set.mem_setOf_eq] at hj
    obtain ⟨L, R, hL, hR, hcard, hLR⟩ := hj
    have h1 : ∃ i, i ∈ Finset.Icc 1 2016 ∧ i ∉ L ∧ i ∉ R := by
      by_contra' H2
      have h2 : Finset.card (L ∪ R) ≤ L.card + R.card := Finset.card_union_le L R
      have h3 : Finset.Icc 1 2016 ⊆ (L ∪ R) := fun a ha ↦ by
        specialize H2 a ha
        rw [←or_iff_not_imp_left] at H2
        exact Finset.mem_union.mpr H2
      have h4 : (Finset.Icc 1 2016).card ≤ (L ∪ R).card := Finset.card_le_of_subset h3
      rw [Nat.card_Icc, add_tsub_cancel_right] at h4
      rw [←hcard] at H
      exact ((h4.trans h2).trans_lt H).false
    obtain ⟨i, hic, hiL, hiR⟩ := h1
    push_neg at hLR
    specialize hLR i
    rw [←Finset.prod_erase_mul _ _ hic, ←Finset.prod_erase_mul _ _ hic] at hLR
    simp (config := {decide := true}) only [sub_self, ite_false, hiL, hiR, mul_zero, ne_eq] at hLR
