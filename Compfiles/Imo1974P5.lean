/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1974, Problem 5

What are the possible values of

 a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d)

as a,b,c,d range over the positive real numbers?
-/

namespace Imo1974P5

determine solution_set : Set ℝ := Set.Ioo 1 2

snip begin

lemma condition_implies_solution_set (s : ℝ)
    (h : ∃ a b c d : ℝ,
            0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
            s = a / (a + b + d) + b / (a + b + c) +
                c / (b + c + d) + d / (a + c + d)) :
    s ∈ solution_set := by
  rw [Set.mem_Ioo]
  obtain ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩ := h

  constructor
  · have h8 : a / (a + b + c + d) < a / (a + b + d) :=
       div_lt_div_of_lt_left ha (by linarith) (by linarith)
    have h9 : b / (a + b + c + d) < b / (a + b + c) :=
       div_lt_div_of_lt_left hb (by linarith) (lt_add_of_pos_right _ hd)
    have h10 : c / (a + b + c + d) < c / (b + c + d) :=
       div_lt_div_of_lt_left hc (by linarith) (by linarith)
    have h11 : d / (a + b + c + d) < d / (a + c + d) :=
       div_lt_div_of_lt_left hd (by linarith) (by linarith)

    calc 1 = a / (a + b + c + d) + b / (a + b + c + d) +
             c / (a + b + c + d) + d / (a + b + c + d) := by field_simp
         _ < _ := by gcongr

  · have h3 : a / (a + b + d) < a / (a + b) :=
       div_lt_div_of_lt_left ha (add_pos ha hb) (lt_add_of_pos_right _ hd)
    have h4 : b / (a + b + c) < b / (a + b) :=
       div_lt_div_of_lt_left hb (add_pos ha hb) (lt_add_of_pos_right _ hc)
    have h5 : c / (b + c + d) < c / (c + d) :=
       div_lt_div_of_lt_left hc (add_pos hc hd) (by linarith)
    have h6 : d / (a + c + d) < d / (c + d) :=
       div_lt_div_of_lt_left hd (add_pos hc hd) (by linarith)

    calc
      _ < a / (a + b) + b / (a + b) + c / (c + d) + d / (c + d) := by gcongr
      _ = 2 := by field_simp; ring

noncomputable def S (a b c d : ℝ) : ℝ :=
    a / (a + b + d) + b / (a + b + c) +
    c / (b + c + d) + d / (a + c + d)

noncomputable def T (t : ℝ) : ℝ := S 1 (1 - t) t (t * (1 - t))

theorem T_continuous : ContinuousOn T (Set.Icc 0 1) := by
  unfold T S
  fun_prop (disch := (rintro x ⟨a,b⟩; nlinarith))

lemma T0 : T 0 = 1 := by norm_num [T, S]
lemma T1 : T 1 = 2 := by norm_num [T, S]

snip end

problem imo1974_p5 (s : ℝ) :
    s ∈ solution_set ↔
    ∃ a b c d : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
     s = a / (a + b + d) + b / (a + b + c) +
         c / (b + c + d) + d / (a + c + d) := by
  constructor
  · intro hx
    have h2 := intermediate_value_Ioo zero_le_one T_continuous
    rw [T0, T1] at h2
    have h4 := h2 hx
    rw [Set.mem_image] at h4
    obtain ⟨t, ht, hts⟩ := h4
    rw [Set.mem_Ioo] at ht
    obtain ⟨hta, htb⟩ := ht

    use 1, 1 - t, t, (t * (1 - t))
    exact ⟨zero_lt_one, sub_pos.mpr htb, hta, by nlinarith, hts.symm⟩
  · intro hs; exact condition_implies_solution_set s hs
