/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 2002, Problem 5

Determine all functions f : ℝ → ℝ such that

  (f(x) + f(z))(f(y) + f(t)) = f(xy - zt) + f(xt + yz)

for all real numbers x,y,z,t.
-/

namespace Imo2002P5

determine SolutionSet : Set (ℝ → ℝ) :=
  { fun x ↦ 0, fun x ↦ 1/2, fun x ↦ x^2 }

problem imo2002_p5 (f : ℝ → ℝ) :
    f ∈ SolutionSet ↔
    ∀ x y z t, (f x + f z) * (f y + f t) =
               f (x * y - z * t) + f (x * t + y * z) := by
  -- solution from https://web.evanchen.cc/exams/IMO-2002-notes.pdf
  simp only [Set.mem_insert_iff, one_div, Set.mem_singleton_iff]
  constructor
  · intro hf x y z t
    obtain rfl | rfl | rfl := hf
    · simp
    · norm_num1
    · ring
  let P x y z t : Prop :=
    (f x + f z) * (f y + f t) = f (x * y - z * t) + f (x * t + y * z)
  intro hf
  have h1 : ∀ x, f x = f (-x) := fun x ↦ by
    have h2 := hf x 1 0 0
    have h3 := hf 0 0 1 x
    ring_nf at h2 h3
    linarith
  by_cases h2 : ∃ y, ∀ x, f x = y
  · -- f is constant
    obtain ⟨y, hy⟩ := h2
    have h3 := hf 0 0 0 0
    simp only [hy] at h3
    suffices h4 : y = 0 ∨ y = 1/2 by
      obtain rfl | rfl := h4
      · left; ext x
        exact hy x
      · right; left; ext x
        simp only [hy x, one_div]
    have h5 : y * (2 * y - 1) = 0 := by linarith only [h3]
    rw [mul_eq_zero] at h5
    cases' h5 with h6 h6
    · left; exact h6
    · right; linarith
  right; right
  push_neg at h2
  have h3 : f 0 = 0 := by
    obtain ⟨y1, hy1⟩ := h2 (1/2)
    have h4 : ∀ y t, P 0 y 0 t := fun y t ↦ hf 0 y 0 t
    unfold_let P at h4
    simp at h4
    have h5 : f y1 + f y1 ≠ 1 := by
      intro H
      apply_fun (·/2) at H
      field_simp at H
      have H' : f y1 = 1 /2 := by linarith
      contradiction
    contrapose! h5
    replace h5 : f 0 + f 0 ≠ 0 := by
      contrapose! h5; linarith only [h5]
    have h6 := h4 y1 y1
    rw [mul_eq_left₀ h5] at h6
    exact h6
  have h4 : ∀ x y, f (x * y) = f x * f y := fun x y ↦ by
    have h5 := hf x y 0 0
    simp only [mul_zero, sub_zero, add_zero, h3] at h5
    exact h5.symm
  have h5 : ∀ x, 0 ≤ f x := fun x ↦ by
    have h6 : f x = f |x| := by
      obtain h7 | h7 := abs_choice x
      · rw [h7]
      · rw [h7, h1]
    have h8 : |x| = (Real.sqrt |x|)^2 := by
      exact (Real.sq_sqrt (by positivity)).symm
    rw [h6, h8, sq, h4, ←sq]
    positivity
  have h6 : ∀ u v, 0 < v → v < u → f v ≤ f u := by
    intro u v hv0 hvu
    have h7 : ∀ x y, (f x + f y)^2 = f (x^2 + y^2) := fun x y ↦ by
      have h8 := hf x y y x
      have h9 : x * y - y * x = 0 := by ring
      rw [h9, h3, zero_add, ←sq, ←sq] at h8
      linarith only [h8]
    have h8 := h7 (Real.sqrt v) (Real.sqrt (u - v))
    have h9 : 0 < u - v := sub_pos.mpr hvu
    rw [Real.sq_sqrt (by positivity)] at h8
    rw [Real.sq_sqrt (by positivity)] at h8
    rw [add_sub_cancel] at h8
    have h10 : (f √v) ^2 + (f √(u - v))^2 + 2 * f √v * f √(u - v) =
              (f √v + f √(u - v)) ^ 2 := by ring
    have h11 : (f √v) ^2 ≤ (f √v + f √(u - v)) ^ 2 := by
      rw[←h10]
      have h12 := h5 (√v)
      have h13 := h5 (√(u - v))
      nlinarith
    rw [h8, sq, ←h4, ←sq, Real.sq_sqrt (by positivity)] at h11
    exact h11
  sorry
