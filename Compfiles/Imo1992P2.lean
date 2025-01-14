/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1992, Problem 2

Determine all functions f : ℝ → ℝ such that
for all x,y ∈ ℝ, f(x² + f(y)) = y + (f(x))².
-/

namespace Imo1992P2

determine solution_set : Set (ℝ → ℝ) := { fun x ↦ x }

problem imo1992_p2 (f : ℝ → ℝ) :
    f ∈ solution_set ↔
    ∀ x y, f (x^2 + f y) = y + f x ^ 2 := by
  -- https://prase.cz/kalva/imo/isoln/isoln922.html
  rw [Set.mem_singleton_iff]
  constructor
  · rintro rfl x y; dsimp only; ac_rfl
  intro hf
  have h1 : f 0 = 0 := by
    have h0 := hf 0 0
    simp only [zero_pow two_ne_zero, zero_add] at h0
    let t := f 0
    have ht1 : f t = t^2 := h0
    have ht2 : ∀ x, f (x^2 + t) = (f x)^2 := fun x ↦ by
      simp only [hf, zero_add, t]
    have ht3 : ∀ x, f (f x) = x + t^2 := fun x ↦ by
      simp only [←hf, zero_pow two_ne_zero, zero_add, t]
    have ht4 :=
      calc 1 + t + 2 * t^2 + t^4
         = t + (1 + t^2)^2 := by ring
       _ = t + (f (f 1))^2 := by rw [ht3 1]
       _ = f (t^2 + (f 1)^2) := by rw [←ht1, ←hf, add_comm]
       _ = f (t^2 + f (1 + t)) := by rw [← ht2 1, one_pow]
       _ = 1 + t + (f t)^2 := hf t (1 + t)
       _ = 1 + t + t^4 := by rw[ht1]; ring

    nlinarith
  have h2 : ∀ x, f (f x) = x := fun x ↦ by
    have h2' := hf 0 x
    simp only [zero_pow two_ne_zero, zero_add, h1, add_zero] at h2'
    exact h2'
  have h3 : ∀ x, f (x^2) = f x^2 := fun x ↦ by
    have h3' := hf x 0
    simp only [h1, zero_add, add_zero] at h3'
    exact h3'
  have h4 : ∀ x y, f (x^2 + y) = f y + (f x)^2 := fun x y ↦ by
    have h4' := hf x (f y)
    rw [h2] at h4'
    exact h4'
  have h5 : ∀ x, 0 ≤ x → ∀ y, f (x + y) = f x + f y := fun x hx y ↦ by
    calc _ = f ((Real.sqrt x)^2 + y) := by rw[Real.sq_sqrt hx]
         _ = f y + f (Real.sqrt x)^2 := h4 (Real.sqrt x) y
         _ = f y + f (Real.sqrt x^2) := by rw [h3]
         _ = f y + f x := by rw[Real.sq_sqrt hx]
         _ = _ := add_comm _ _
  have h6 : ∀ x, f (-x) = - f x := fun x ↦ by
    obtain hx | hx := le_total 0 x
    · have h6' := h5 x hx (-x)
      rw [add_neg_cancel, h1] at h6'
      exact eq_neg_of_add_eq_zero_right h6'.symm
    · have hx' : 0 ≤ -x := by linarith
      have h6' := h5 (-x) hx' x
      rw [neg_add_cancel, h1] at h6'
      exact add_eq_zero_iff_eq_neg.mp h6'.symm
  have h7 : ∀ x y, f (x + y) = f x + f y := fun x y ↦ by
    obtain hx | hx := le_total 0 x
    · exact h5 x hx y
    · have hx' : 0 ≤ -x := by linarith
      have h8 := h5 (-x) hx' (-y)
      rw [show -x + -y = - (x + y) by ring, h6, h6, h6] at h8
      linarith only [h8]
  have h8 : ∀ x y, f (x - y) = f x - f y := fun x y ↦ by
    rw [show x - y = x + -y by ring, show f x - f y = f x + -f y by ring, ← h6]
    exact h7 x (-y)
  ext x
  by_contra H
  obtain ⟨z, hz⟩ : ∃ z, 0 < z ∧ f z < 0 := by
    obtain h9 | h9 := Ne.lt_or_lt H
    · use x - f x
      constructor
      · linarith
      · rw [h8, h2]; linarith
    · use f x - x
      constructor
      · linarith
      · rw [h8, h2]; linarith
  have h10 :=
    calc f z
       = f (Real.sqrt z ^ 2) := by rw[Real.sq_sqrt (le_of_lt hz.1)]
     _ = f (Real.sqrt z)^2 := h3 (Real.sqrt z)
     _ ≥ 0 := sq_nonneg _
  linarith only [h10, hz]


end Imo1992P2
