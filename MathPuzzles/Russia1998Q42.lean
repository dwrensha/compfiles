/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Real.Basic

import MathPuzzles.Meta.Attributes

/-
 Russian Mathematical Olympiad 1998, problem 42

 A binary operation ⋆ on real numbers has the property that
 (a ⋆ b) ⋆ c = a + b + c.

 Prove that a ⋆ b = a + b.

-/

namespace Russia1998Q42

variable (star : ℝ → ℝ → ℝ)

@[problem_setup]
local infixl:80 " ⋆ " => star

@[problem_statement]
theorem russia1998_q42
  (stardef : ∀ a b c, a ⋆ b ⋆ c = a + b + c) :
  (∀ a b, a ⋆ b = a + b) :=
by
  have lemma2 : ∀ a b d, a ⋆ b = d ⋆ b → a = d := by
    intros a b d hab
    have := calc a + b + a
        = a ⋆ b ⋆ a := (stardef _ _ _).symm
      _ = d ⋆ b ⋆ a := by rw [hab]
      _ = d + b + a := stardef _ _ _
    have : a + b = d + b := (add_left_inj a).mp this
    have : a = d := (add_left_inj b).mp this
    exact this

  have lemma3 : ∀ a b, a ⋆ b = b ⋆ a := by
    intros a b
    let d1 := a ⋆ b
    let d2 := b ⋆ a
    have h1 := calc d1 ⋆ 1 = a + b + 1 := stardef _ _ _
                    _ = b + a + 1 := by rw [add_comm a b]
                    _ = d2 ⋆ 1 := (stardef _ _ _).symm
    exact lemma2 d1 1 d2 h1

  have lemma4 : ∀ a, a ⋆ 0 = a := by
    intro a
    let x := a ⋆ 0
    have h1 := calc x ⋆ 0
        = a + 0 + 0 := stardef a 0 0
      _ = a := by rw [add_zero, add_zero]

    have h2 := calc 2 * x
        = x + x := two_mul x
      _ = x + 0 + x := by rw [add_zero]
      _ = x ⋆ 0 ⋆ x := (stardef _ _ _).symm
      _ = a ⋆ x := by rw [h1]
      _ = x ⋆ a := lemma3 _ _
      _ = a ⋆ 0 ⋆ a := rfl
      _ = a + 0 + a := stardef _ _ _
      _ = a + a := by rw [add_zero]
      _ = 2 * a := (two_mul a).symm
    have h3 : (2:ℝ) ≠ 0 := two_ne_zero
    have h4 : x = a := (mul_right_inj' h3).mp h2
    exact h4

  intros a b

  have := calc a + b = a + b + 0 := by rw [add_zero]
                   _ = a ⋆ b ⋆ 0 := (stardef _ _ _).symm
                   _ = a ⋆ b := lemma4 _
  exact this.symm
