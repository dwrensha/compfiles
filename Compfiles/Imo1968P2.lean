/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Nat.Digits
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 1968, Problem 2

Determine the set of natural numbers x such that
the sum of the decimal digits of x is equal to x² - 10x - 22.
-/

namespace Imo1968P2

snip begin

lemma lemma0 {α β : Type} {f : ℕ → α → β} (l : List α) (h2 : l ≠ []) :
    List.getLast (List.mapIdx f l) (List.mapIdx_ne_nil_iff.mpr h2) =
    f (l.dropLast).length (List.getLast l h2) := by
  rw [List.getLast_mapIdx, List.length_dropLast]

lemma prod_digits_le {x b : ℕ} (hb : 2 ≤ b) (xpos : 0 < x) :
    List.prod (Nat.digits b x) ≤ x := by
  have h1 : Nat.digits b x ≠ [] :=
    Nat.digits_ne_nil_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp xpos)
  rw [←List.dropLast_append_getLast h1, List.prod_append, List.prod_singleton]

  have h3 := Nat.ofDigits_digits b x
  rw [Nat.ofDigits_eq_sum_mapIdx] at h3
  have h4 : List.mapIdx (fun i a => a * b ^ i) (Nat.digits b x) ≠ [] :=
    List.mapIdx_ne_nil_iff.mpr h1

  rw [←List.dropLast_append_getLast (List.mapIdx_ne_nil_iff.mpr h1),
      List.sum_append, List.sum_singleton] at h3
  have h6 : List.getLast (List.mapIdx (fun i a => a * b ^ i) (Nat.digits b x)) h4 ≤ x :=
     by nth_rewrite 2 [←h3]; exact Nat.le_add_left _ _
  have h7 : List.getLast (List.mapIdx (fun i a => a * b ^ i) (Nat.digits b x)) h4 =
       b ^ (List.dropLast (Nat.digits b x)).length * List.getLast (Nat.digits b x) h1 := by
    rw [lemma0 _ h1, mul_comm]
  rw [h7] at h6; clear h7

  have h8 : List.prod (List.dropLast (Nat.digits b x)) ≤
            b^(List.length (List.dropLast (Nat.digits b x))) := by
    have h10 : ∀ d ∈ List.dropLast (Nat.digits b x), d ≤ b := fun d hd ↦
      Nat.le_of_lt (Nat.digits_lt_base hb (List.mem_of_mem_dropLast hd))
    exact List.prod_le_pow_card (List.dropLast (Nat.digits b x)) b h10

  exact mul_le_of_mul_le_right h6 h8

snip end

determine solution_set : Set ℕ := { 12 }

problem imo1968_p2 (x : ℕ) :
    x ∈ solution_set ↔
    x^2 = 10 * x + 22 + (Nat.digits 10 x).prod := by
  -- Follows Solution 1 at
  -- https://artofproblemsolving.com/wiki/index.php/1968_IMO_Problems/Problem_2
  constructor
  · rintro rfl; norm_num
  · intro hs
    have h0 : 0 < x := (Nat.eq_zero_or_pos x).resolve_left (fun H ↦ by norm_num [H] at hs)
    have h2 : x^2 ≤ 10 * x + 22 + x := le_add_of_le_add_left (le_of_eq hs)
      (prod_digits_le (by norm_num) h0)
    have h3 : x < 13 := by nlinarith
    rw [Set.mem_singleton_iff]
    interval_cases x <;> norm_num at hs ⊢


end Imo1968P2
