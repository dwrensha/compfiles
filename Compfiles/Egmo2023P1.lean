/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ansar Azharov
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# European Girls' Mathematical Olympiad 2023, Problem 1

There are n ≥ 3 positive real numbers a_1, a_2, . . . , a_n. For each 1 ≤ i ≤ n we let
b_i = (a_(i-1) + a_(i+1)) / a_i (here we define a_0 to be a_n and a_(n+1) to be a_1).
Assume that for all i and j in the range 1 to n, we have a_i ≤ a_j if and only if b_i ≤ b_j.
Prove that a_1 = a_2 = ... = a_n.
-/

namespace Egmo2023P1

-- The solution was adapted from here: https://www.youtube.com/watch?v=PNFh789P31E.
-- Note that indexing starts from 0 in the formalized statement.
problem egmo2023_p1 (n : ℕ) [NeZero n] (_ : n ≥ 3) (a : Fin n → ℝ) (ha : ∀ i, a i > 0)
    (b : Fin n → ℝ) (hb : ∀ i, b i = (a (i - 1) + a (i + 1)) / (a i))
    (h : ∀ i j, a i ≤ a j ↔ b i ≤ b j) : ∀ i j, a i = a j := by
  obtain ⟨m, hm⟩ := Finite.exists_min a
  obtain ⟨M, hM⟩ := Finite.exists_max a
  have h1 : b m ≥ 2 := calc b m
    _ ≥ (a m + a m) / (a m) := by
      rw [hb m]
      gcongr
      · exact le_of_lt (ha m)
      · exact hm (m - 1)
      · exact hm (m + 1)
    _ ≥ 2 := by
      rw [← two_mul, mul_div_cancel_right₀]
      positivity [ha m]
  have h2 : b M ≤ 2 := calc b M
    _ ≤ (a M + a M) / (a M) := by
      rw [hb M]
      gcongr
      · exact le_of_lt (ha M)
      · exact hM (M - 1)
      · exact hM (M + 1)
    _ ≤ 2 := by
      rw [← two_mul, mul_div_cancel_right₀]
      positivity [ha M]
  have h3 : ∀ i, b i = 2 := by
    intro i
    apply eq_of_le_of_ge
    · exact le_trans ((h i M).mp (hM i)) h2
    · exact le_trans h1 ((h m i).mp (hm i))
  intro i j
  apply eq_of_le_of_ge
  · rw [h i j, h3 i, h3 j]
  · rw [h j i, h3 j, h3 i]

end Egmo2023P1
