/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Nat.Digits
import Mathlib.Tactic

import Compfiles.Meta.ProblemExtraction

problem_file

/-!
# International Mathematical Olympiad 1968, Problem 2

Determine the set of natural numbers x such that
the sum of the decimal digits of x is equal to x² - 10x - 22.
-/

namespace Imo1968P2

snip begin

lemma lemma0 {α β : Type} {f : ℕ → α → β} (l : List α)
     (h1 : List.mapIdx f l ≠ []) (h2 : l ≠ []) :
     List.getLast (List.mapIdx f l) h1 =
    f (l.dropLast).length (List.getLast l h2) := by
  induction' l with x xs ih
  · exfalso; exact h1 rfl
  · cases' xs with y ys
    · simp
    · simp_rw [List.mapIdx_cons]; sorry

lemma lemma1 (x : ℕ) (xpos : 0 < x) : List.prod (Nat.digits 10 x) ≤ x := by
  have h1 : Nat.digits 10 x ≠ [] :=
    Nat.digits_ne_nil_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp xpos)
  rw [←List.dropLast_append_getLast h1, List.prod_append, List.prod_singleton]

  have h3 := Nat.ofDigits_digits 10 x
  rw [Nat.ofDigits_eq_sum_mapIdx] at h3
  have h4 : List.mapIdx (fun i a => a * 10 ^ i) (Nat.digits 10 x) ≠ [] := by
    rw [Nat.digits_of_two_le_of_pos (by norm_num) xpos, List.mapIdx_cons];
    exact List.cons_ne_nil _ _
  have h5 := List.dropLast_append_getLast h4
  rw [←h5, List.sum_append, List.sum_singleton] at h3; clear h5
  have h6 : List.getLast (List.mapIdx (fun i a => a * 10 ^ i) (Nat.digits 10 x)) h4 ≤ x :=
     by nth_rewrite 2 [←h3]; exact Nat.le_add_left _ _
  have h7 : List.getLast (List.mapIdx (fun i a => a * 10 ^ i) (Nat.digits 10 x)) h4 =
       10 ^ (List.dropLast (Nat.digits 10 x)).length * List.getLast (Nat.digits 10 x) h1 := by
    rw [lemma0 _ h4 h1]
    rw [mul_comm]
  rw [h7] at h6; clear h7

  have h8 : List.prod (List.dropLast (Nat.digits 10 x)) ≤
            10^(List.length (List.dropLast (Nat.digits 10 x))) := by
    sorry

  calc _ ≤ _ := Nat.mul_le_mul_right _ h8
       _ ≤ _ := h6

snip end

determine solution_set : Set ℕ := { 12 }

problem imo1968_p2 (x : ℕ) :
    x ∈ solution_set ↔
    x^2 = 10 * x + 22 + (Nat.digits 10 x).prod := by
  constructor
  · rintro rfl; norm_num
  · intro hs
    sorry
