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

lemma lemma1 {a b : ℝ} (ha : 0 ≤ a) (h : a < b) : a^2 < b^2 := by nlinarith

snip end

determine SolutionSet : Set ℝ := Set.Icc (-1) (1 - Real.sqrt 31 / 8)

problem imo1962_p2 (x : ℝ) :
    x ∈ SolutionSet ↔
    x ≤ 3 ∧ -1 ≤ x ∧ 1/2 < Real.sqrt (3 - x) - Real.sqrt (x + 1) := by
  -- https://prase.cz/kalva/imo/isoln/isoln622.html
  rw [Set.mem_Icc]
  constructor
  · rintro ⟨hx1, hx2⟩
    refine ⟨?_, hx1, ?_⟩
    · have h1 : 0 < Real.sqrt 31 / 8 := by positivity
      linarith only [hx2, h1]
    · have : x + 1 < 3 - x := by sorry
      sorry
  rintro ⟨hx1, hx2, hx3⟩
  refine ⟨hx2, ?_⟩
  have h0 : (0:ℝ) ≤ (1:ℝ) / 2 := by norm_num
  have h1 := lemma1 h0 hx3
  have hx4 : 0 ≤ 3 - x := by linarith
  have hx5 : 0 ≤ x + 1 := by linarith
  have h2 := calc
      (Real.sqrt (3 - x) - Real.sqrt (x + 1)) ^ 2
     = Real.sqrt (3 - x) ^2 - 2 * Real.sqrt (3 - x) * Real.sqrt (x + 1)
       + Real.sqrt (x + 1) ^2 := by ring
   _ = (3 - x) - 2 * Real.sqrt (3 - x) * Real.sqrt (x + 1)
       + (x + 1) := by rw [Real.sq_sqrt hx4, add_left_cancel_iff, Real.sq_sqrt hx5]
   _ = 4 - 2 * (Real.sqrt (3 - x) * Real.sqrt (x + 1)) := by ring
   _ = 4 - 2 * Real.sqrt ((3 - x) * (x + 1)) := by rw[←Real.sqrt_mul hx4]

  rw [h2] at h1; clear h2
  have h3 : Real.sqrt ((3 - x) * (x + 1)) < 15 / 8 := by linarith only [h1]
  have h4 : 0 ≤ Real.sqrt ((3 - x) * (x + 1)) := Real.sqrt_nonneg _
  have h5 := lemma1 h4 h3
  rw [Real.sq_sqrt (by positivity)] at h5
  sorry
