/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

import MathPuzzles.Meta.Attributes

#[problem_setup]/-!
Bulgarian Mathematical Olympiad 1998, Problem 1

Find the least natural number n (n ≥ 3) with the following property:
for any coloring in 2 colors of n distinct collinear points A₁, A₂, ..., Aₙ,
there exist three points Aᵢ, Aⱼ, A₂ⱼ₋ᵢ, 1 ≤ i < 2j - i ≤ n, which are colored
the same color.
-/

#[problem_setup] namespace Bulgaria1998Q1

#[problem_setup]
def coloring_has_desired_points (m : ℕ) (color : Set.Icc 1 m → Fin 2) : Prop :=
  ∃ i j : Set.Icc 1 m,
    i < j ∧
    ∃ h3 : 2 * j.val - i ∈ Set.Icc 1 m,
    color i = color j ∧ color i = color ⟨2 * j - i, h3⟩

fill_in_the_blank n := 9

def coloring_of_eight : Set.Icc 1 8 → Fin 2
| ⟨1, _⟩ => 0
| ⟨2, _⟩ => 1
| ⟨3, _⟩ => 0
| ⟨4, _⟩ => 1
| ⟨5, _⟩ => 1
| ⟨6, _⟩ => 0
| ⟨7, _⟩ => 1
| ⟨8, _⟩ => 0
| _ => 0 -- unreachable

problem bulgaria1998_q1a :
    ∃ f: Set.Icc 1 (n - 1) → Fin 2, ¬coloring_has_desired_points (n - 1) f := by
  use coloring_of_eight
  intro h
  obtain ⟨⟨i, hi1, hi2⟩, ⟨j, hj1, hj2⟩, hij1, hij2, hc1, hc2⟩ := h
  have hn1 : n - 1 = 8 := by simp[n]
  rw[hn1] at hi2 hj2
  dsimp[coloring_of_eight] at *
  interval_cases i <;> interval_cases j <;> aesop

problem bulgaria1998_q1b (color : Set.Icc 1 n → Fin 2) : coloring_has_desired_points n f := by
  sorry
