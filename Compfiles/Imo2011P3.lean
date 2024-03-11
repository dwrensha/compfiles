/-
Copyright (c) 2021 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 2011, Problem 3

Let f : ℝ → ℝ be a function that satisfies

   f(x + y) ≤ y * f(x) + f(f(x))

for all x and y. Prove that f(x) = 0 for all x ≤ 0.
-/

namespace Imo2011P3

problem imo2011_p3 (f : ℝ → ℝ) (hf : ∀ x y, f (x + y) ≤ y * f x + f (f x)) :
    ∀ x ≤ 0, f x = 0 := by
  -- Direct translation of the solution found in
  -- https://www.imo-official.org/problems/IMO2011SL.pdf

  -- reparameterize
  replace hf : ∀ x t, f t ≤ t * f x - x * f x + f (f x) := by
    intro x t
    calc f t = f (x + (t - x))             := by rw [add_eq_of_eq_sub' rfl]
           _ ≤ (t - x) * f x + f (f x)     := hf x (t - x)
           _ = t * f x - x * f x + f (f x) := by rw [sub_mul]

  have hab : ∀ a b, a * f a + b * f b ≤ 2 * f a * f b := by
    intro a b
    linarith [hf b (f a), hf a (f b)]

  have f_nonneg_of_pos : ∀ a < 0, 0 ≤ f a := by
    intro a han
    have : a * f a ≤ 0 := add_le_iff_nonpos_left.mp (hab a (2 * f a))
    exact nonneg_of_mul_nonpos_right this han

  have f_nonpos : ∀ x, f x ≤ 0 := by
    intro x
    by_contra! hp
    -- If we choose a small enough argument for f, then we get a contradiction.
    let s := (x * f x - f (f x)) / (f x)
    have hm : min 0 s - 1 < s := (sub_one_lt _).trans_le (min_le_right 0 s)
    have hml : min 0 s - 1 < 0 := (sub_one_lt _).trans_le (min_le_left 0 s)
    suffices f (min 0 s - 1) < 0 from
      not_le.mpr this (f_nonneg_of_pos (min 0 s - 1) hml)

    calc f (min 0 s - 1)
         ≤ (min 0 s - 1) * f x - x * f x + f (f x) := hf x (min 0 s - 1)
       _ < s * f x - x * f x + f (f x) :=
               by linarith [(mul_lt_mul_right hp).mpr hm]
       _ = 0 := by rw [(eq_div_iff hp.ne.symm).mp rfl]; linarith

  have f_zero_of_neg : ∀ x < 0, f x = 0 := by
    intro x hxz
    exact (f_nonpos x).antisymm (f_nonneg_of_pos x hxz)

  intro x hx
  obtain (h_x_neg : x < 0) | (rfl : x = 0) := hx.lt_or_eq
  · exact f_zero_of_neg _ h_x_neg
  · suffices 0 ≤ f 0 from (f_nonpos 0).antisymm this
    have hno : f (-1) = 0 := f_zero_of_neg (-1) neg_one_lt_zero
    have hp := hf (-1) (-1)
    rw [hno, mul_zero, sub_zero, zero_add] at hp
    exact hp
