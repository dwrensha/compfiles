/-
Copyright (c) 2023 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 2015, Problem 5

Determine all functions f : ℝ → ℝ that satisfy

  f(x + f(x + y)) + f(xy) = x + f(x + y) + yf(x)

for all x,y.
-/

namespace Imo2015P5

determine SolutionSet : Set (ℝ → ℝ) := { fun x ↦ x, fun x ↦ 2 - x }

problem imo2015_p5 (f : ℝ → ℝ) :
    f ∈ SolutionSet ↔
    ∀ x y, f (x + f (x + y)) + f (x * y) = x + f (x + y) + y * f x := by
  -- https://web.evanchen.cc/exams/IMO-2015-notes.pdf
  constructor
  · rintro (rfl | rfl) x y <;> ring
  intro hf
  rw [Set.mem_insert_iff, Set.mem_singleton_iff]
  let S : Set ℝ := {t | f t = t}
  have h1 : f (f 0) = 0 := by
    have := hf 0 0
    simp only [add_zero, zero_add, mul_zero, zero_mul, add_eq_right] at this
    exact this
  have h2 : f 0 = 2 ∨ f 0 = 0 := by
    have h3 := hf 0 (f 0)
    simp only [zero_add, h1, zero_mul] at h3
    have h4 : f 0 * (f 0 - 2) = 0 := by linarith only [h3]
    obtain h5 | h5 := mul_eq_zero.mp h4
    · right; exact h5
    · left; linarith only [h5]
  have h3 : ∀ x, x + f (x + 1) ∈ S := fun x ↦ by
    have h4 := hf x 1
    simp only [mul_one, one_mul] at h4
    rw [add_right_cancel_iff] at h4
    exact h4
  obtain h4 | h4 := h2
  · right
    have h7 : ∀ t ∈ S, t = 1 := fun t ht ↦ by
      simp only [S, Set.mem_setOf_eq] at ht
      have h6 := hf 0 t
      simp only [zero_add, zero_mul, ht, h4] at h6
      linarith only [h6]
    have h8 : ∀ x, x + f (x + 1) = 1 := fun x ↦ by
      have h9 := h3 x
      exact h7 _ h9
    ext x
    have h10 := h8 (x - 1)
    rw [sub_add_cancel] at h10
    linarith only [h10]
  left
  have h5 : ∀ x, f (-x) = - f x := fun x ↦ by
    have h6 := hf 1 (-1)
    have h7 := hf (-1) 1
    simp only [add_neg_cancel, mul_neg, mul_one, neg_mul,
               one_mul, h4, add_zero] at h6
    simp only [neg_add_cancel, mul_one, one_mul, add_left_inj, h4, add_zero] at h7
    rw [h7] at h6
    replace h6 : f 1 = 1 := by linarith only [h6]
    have h8 : ∀ x, x + f x ∈ S := fun x ↦ by
      have h9 := hf x 0
      simp only [add_zero, mul_zero, zero_mul, h4] at h9
      exact h9
    have h9 : ∀ x, x - 1 + f x ∈ S := fun x ↦ by
      have h10 := hf (x - 1) 1
      simp only [sub_add_cancel, mul_one, one_mul, add_left_inj] at h10
      exact h10
    have h10 : ∀ x, x + 1 + f x ∈ S := fun x ↦ by
      have h11 := hf 1 (f x + x - 1)
      have h12 := h8 x
      simp only [Set.mem_setOf_eq, S] at h12 ⊢
      rw [add_comm] at h12
      have h13 := h9 x
      simp only [Set.mem_setOf_eq, S] at h13
      rw [show x - 1 + f x = f x + x - 1 by ring] at h13
      simp only [add_sub_cancel, one_mul, h12, h13, h6, mul_one] at h11
      rw [show 1 + (f x + x) = x + 1 + f x by ring] at h11
      linarith only [h11]
    have h11 := hf x (-1)
    have h12 := h10 (x + -1)
    simp only [neg_add_cancel_right, S, Set.mem_setOf_eq] at h12
    simp only [mul_neg, mul_one, neg_mul, one_mul, h12,
               add_left_cancel_iff] at h11
    exact h11
  ext x
  have h11 := hf x (-x)
  simp only [add_neg_cancel, h4, add_zero, mul_neg, neg_mul, h5] at h11
  have h12 := hf (-x) x
  simp only [neg_add_cancel, h4, add_zero, neg_mul, h5] at h12
  linarith


end Imo2015P5
