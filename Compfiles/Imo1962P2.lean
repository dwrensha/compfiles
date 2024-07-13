/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1962, Problem 2

Determine all real numbers x which satisfy

  √(3 - x) - √(x + 1) > 1/2.
-/

namespace Imo1962P2

snip begin

lemma lemma1 (x : ℝ) :
    (15 / 8) ^ 2 - (3 - x) * (x + 1) =
    (x - (1 + Real.sqrt 31/8)) * (x - (1 - Real.sqrt 31/8)) := by
  have h1 : Real.sqrt 31 ^ 2 = 31 := Real.sq_sqrt (Nat.ofNat_nonneg _)
  ring_nf
  rw [h1]
  ring

lemma lemma2 {x : ℝ} (hx4 : 0 ≤ 3 - x) (hx5 : 0 ≤ x + 1) :
    (Real.sqrt (3 - x) - Real.sqrt (x + 1)) ^ 2 = 4 - 2 * Real.sqrt ((3 - x) * (x + 1)) :=
  calc
      (Real.sqrt (3 - x) - Real.sqrt (x + 1)) ^ 2
     = Real.sqrt (3 - x) ^2 - 2 * Real.sqrt (3 - x) * Real.sqrt (x + 1)
       + Real.sqrt (x + 1) ^2 := sub_sq _ _
   _ = (3 - x) - 2 * Real.sqrt (3 - x) * Real.sqrt (x + 1)
       + (x + 1) := by rw [Real.sq_sqrt hx4, add_left_cancel_iff, Real.sq_sqrt hx5]
   _ = 4 - 2 * (Real.sqrt (3 - x) * Real.sqrt (x + 1)) := by ring
   _ = 4 - 2 * Real.sqrt ((3 - x) * (x + 1)) := by rw[←Real.sqrt_mul hx4]

snip end

determine SolutionSet : Set ℝ := Set.Ico (-1) (1 - √31 / 8)

problem imo1962_p2 (x : ℝ) :
    x ∈ SolutionSet ↔
    x ≤ 3 ∧ -1 ≤ x ∧ 1/2 < √(3 - x) - √(x + 1) := by
  -- https://prase.cz/kalva/imo/isoln/isoln622.html
  rw [Set.mem_Ico]
  constructor
  · rintro ⟨hx1, hx2⟩
    have hx4 : x ≤ 3 := by
      have h1 : 0 < Real.sqrt 31 / 8 := by positivity
      linarith only [hx2, h1]
    have hx4' : 0 ≤ 3 - x := sub_nonneg.mpr hx4
    have hx1' : 0 ≤ x + 1 := neg_le_iff_add_nonneg.mp hx1
    refine ⟨hx4, hx1, ?_⟩
    · have h30 : 0 ≤ Real.sqrt 31 / 8 := by positivity
      have h3 : x + 1 < 3 - x := by linarith
      suffices H : (1 / 2)^2 < (Real.sqrt (3 - x) - Real.sqrt (x + 1))^2
      · have h31 : 0 ≤ Real.sqrt (3 - x) - Real.sqrt (x + 1) := by
          rw [sub_nonneg]
          apply le_of_lt
          exact Real.sqrt_lt_sqrt hx1' h3
        exact lt_of_pow_lt_pow_left 2 h31 H
      rw [lemma2 hx4' hx1', lt_sub_comm]
      suffices H : Real.sqrt ((3 - x) * (x + 1)) < 15 / 8 by
        linarith only [H]
      suffices H : (Real.sqrt ((3 - x) * (x + 1)))^2 < (15/8)^2 from
        lt_of_pow_lt_pow_left 2 (by norm_num) H
      rw [Real.sq_sqrt (by positivity)]
      suffices H : 0 < (15 / 8) ^ 2 - (3 - x) * (x + 1) from sub_pos.mp H
      rw [lemma1 x]
      nlinarith
  rintro ⟨hx1, hx2, hx3⟩
  refine ⟨hx2, ?_⟩
  have h0 : (0:ℝ) ≤ (1:ℝ) / 2 := by norm_num
  have h1 := pow_lt_pow_left hx3 h0 two_ne_zero
  have hx4 : 0 ≤ 3 - x := sub_nonneg.mpr hx1
  have hx5 : 0 ≤ x + 1 := neg_le_iff_add_nonneg.mp hx2

  rw [lemma2 hx4 hx5] at h1
  have h3 : Real.sqrt ((3 - x) * (x + 1)) < 15 / 8 := by linarith only [h1]
  have h4 : 0 ≤ Real.sqrt ((3 - x) * (x + 1)) := Real.sqrt_nonneg _
  have h5 := pow_lt_pow_left h3 h4 two_ne_zero
  rw [Real.sq_sqrt (by positivity)] at h5
  replace h5 : 0 < (15 / 8) ^ 2 - (3 - x) * (x + 1) := sub_pos.mpr h5
  rw [lemma1 x] at h5
  obtain ⟨h6a, h6b⟩ | ⟨_, h7b⟩ := mul_pos_iff.mp h5
  · have h40 : Real.sqrt (3 - x) - Real.sqrt (x + 1) < 0 := by
      have h3 : 3 - x <  x + 1 := by linarith
      rw [sub_neg]
      exact Real.sqrt_lt_sqrt hx4 h3
    linarith
  · exact sub_neg.mp h7b


end Imo1962P2
