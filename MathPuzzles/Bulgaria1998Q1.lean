/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
Bulgarian Mathematical Olympiad 1998, Problem 1

Find the least natural number n (n ≥ 3) with the following property:
for any coloring in 2 colors of n distinct collinear points A₁, A₂, ..., Aₙ,
there exist three points Aᵢ, Aⱼ, A₂ⱼ₋ᵢ, 1 ≤ i < 2j - i ≤ n, which are colored
the same color.
-/

namespace Bulgaria1998Q1

def coloring_has_desired_points (m : ℕ) (color : Set.Icc 1 m → Fin 2) : Prop :=
  ∃ i j : Set.Icc 1 m,
    i < j ∧
    ∃ h3 : 2 * j.val - i ∈ Set.Icc 1 m,
    color i = color j ∧ color i = color ⟨2 * j - i, h3⟩

def n := 9

theorem bulgaria1998_q1a (color : Set.Icc 1 n → Fin 2) : coloring_has_desired_points n f := by
    sorry

def coloring_of_eight : Set.Icc 1 8 → Fin 2
| ⟨0, _⟩ => 0
| ⟨1, _⟩ => 1
| ⟨2, _⟩ => 0
| ⟨3, _⟩ => 1
| ⟨4, _⟩ => 1
| ⟨5, _⟩ => 0
| ⟨6, _⟩ => 1
| ⟨7, _⟩ => 0
| _ => 0 -- unreachable

theorem bulgaria1998_q1b :
  ∃ f: Set.Icc 1 (n - 1) → Fin 2, ¬coloring_has_desired_points (n - 1) f := by
  use coloring_of_eight
  intro h
  obtain ⟨i, j, hij1, hij2, hc1, hc2⟩ := h
  sorry

