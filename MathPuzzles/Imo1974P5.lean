/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import MathPuzzles.Meta.ProblemExtraction

#[problem_setup]/-!
# International Mathematical Olympiad 1974, Problem 5

What are the possible values of

 a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d)

as a,b,c,d range over the positive real numbers?
-/

#[problem_setup] namespace Imo1974P5

determine solution_set : Set ℝ := Set.Ioo 1 2

lemma easy_direction (s : ℝ)
    (h : ∃ a b c d : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
     s = a / (a + b + d) + b / (a + b + c) +
         c / (b + c + d) + d / (a + c + d)) :
    s ∈ solution_set := by
  obtain ⟨a, b, c, d, ha, hb, hc, hd, hs⟩ := h
  have h1 : 1 = a / (a + b + c + d) + b / (a + b + c + d) +
                c / (a + b + c + d) + d / (a + b + c + d) := by field_simp
  have h2 : a / (a + b) + b / (a + b) +
              c / (c + d) + d / (c + d) = 2 := by field_simp; ring
  have h3 : a / (a + b + d) < a / (a + b) :=
     div_lt_div_of_lt_left ha (add_pos ha hb) (lt_add_of_pos_right _ hd)
  have h4 : b / (a + b + c) < b / (a + b) :=
     div_lt_div_of_lt_left hb (add_pos ha hb) (lt_add_of_pos_right _ hc)
  have h5 : c / (b + c + d) < c / (c + d) :=
     div_lt_div_of_lt_left hc (add_pos hc hd) (by linarith)
  have h6 : d / (a + c + d) < d / (c + d) :=
     div_lt_div_of_lt_left hd (add_pos hc hd) (by linarith)

  have h7 : a / (a + b + d) + b / (a + b + c) +
       c / (b + c + d) + d / (a + c + d) <
        a / (a + b) + b / (a + b) + c / (c + d) + d / (c + d) := by gcongr

  have h8 : a / (a + b + c + d) < a / (a + b + d) :=
     div_lt_div_of_lt_left ha (by linarith) (by linarith)
  have h9 : b / (a + b + c + d) < b / (a + b + c) :=
     div_lt_div_of_lt_left hb (by linarith) (by linarith)
  have h10 : c / (a + b + c + d) < c / (b + c + d) :=
     div_lt_div_of_lt_left hc (by linarith) (by linarith)
  have h11 : d / (a + b + c + d) < d / (a + c + d) :=
     div_lt_div_of_lt_left hd (by linarith) (by linarith)

  have h12 : a / (a + b + c + d) + b / (a + b + c + d) +
       c / (a + b + c + d) + d / (a + b + c + d) <
         a / (a + b + d) + b / (a + b + c) +
           c / (b + c + d) + d / (a + c + d) := by gcongr

  rw [←hs] at h7 h12
  rw [Set.mem_Ioo]
  rw [←h1] at h12
  rw [h2] at h7
  exact ⟨h12, h7⟩

problem imo1974_p5 (s : ℝ) :
    s ∈ solution_set ↔
    ∃ a b c d : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
     s = a / (a + b + d) + b / (a + b + c) +
         c / (b + c + d) + d / (a + c + d) := by
  constructor
  · intro hx
    sorry
  · intro hs; exact easy_direction s hs
