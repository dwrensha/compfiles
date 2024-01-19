/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Gian Sanjaya
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 2010, Problem 1

Determine all functions f : ℝ → ℝ such that for all x,y ∈ ℝ,

               f(⌊x⌋y) = f(x)⌊f(y)⌋.
-/

namespace Imo2010P1

determine solution_set : Set (ℝ → ℝ) :=
  { f | (∃ C, ⌊C⌋ = 1 ∧ f = Function.const _ C) ∨ f = Function.const _ 0 }

problem imo2010_p1 (f : ℝ → ℝ) :
    f ∈ solution_set ↔ ∀ x y, f (⌊x⌋ * y) = f x * ⌊f y⌋ :=
  -- Solution adapted from
  -- https://github.com/mortarsanjaya/imo-A-and-N/blob/main/src/IMO2010/A1/A1.lean
---- `→`
⟨λ h x y ↦ h.elim
  (λ h ↦ Exists.elim h $ λ C h ↦ h.2.symm ▸ h.1.symm ▸
    (Int.cast_one : ((1 : ℤ) : ℝ) = 1).symm ▸ (mul_one C).symm)
  (λ h ↦  h.symm ▸ (zero_mul _).symm),
---- `←`
 λ h ↦ (mul_right_eq_self₀.mp ((congr_arg f (mul_zero _).symm).trans (h 0 0)).symm).imp
  ---- Case 1: `⌊f(0)⌋ = 1`
  (λ h0 ↦ ⟨f 0, Int.cast_eq_one.mp h0, funext $ λ x ↦
    (mul_one _).symm.trans $ h0 ▸ (h x 0).symm.trans $ congr_arg f (mul_zero _)⟩)
  ---- Case 2: `f(0) = 0`
  -- First reduce to `f(1) = 0`
  (λ h0 ↦ suffices f 1 = 0
      from funext $ λ y ↦ let h1 := (h 1 y).trans (mul_eq_zero_of_left this _)
                          suffices (⌊(1 : ℝ)⌋ : ℝ) = 1 from one_mul y ▸ this ▸ h1
    Int.cast_eq_one.mpr Int.floor_one
    -- Now reduce to `⌊f(1/2)⌋ = 0`
    suffices ⌊f 2⁻¹⌋ = 0
      from let h1 := (h 2 2⁻¹).trans (mul_eq_zero_of_right _ $ Int.cast_eq_zero.mpr this)
           suffices (⌊(2 : ℝ)⌋ : ℝ) * 2⁻¹ = 1 from this ▸ h1
      (mul_inv_eq_one₀ two_ne_zero).mpr $
        (Int.cast_two (R := ℝ) ▸ Int.floor_intCast (α := ℝ) _ ▸ rfl)
    -- Now prove that `⌊f(1/2)⌋ = 0`
    (mul_eq_zero.mp $ (h 2⁻¹ 2⁻¹).symm.trans $ (congr_arg f $ mul_eq_zero_of_left
        (by norm_num) _).trans h0).elim
      (λ h1 ↦ h1.symm ▸ Int.floor_zero) Int.cast_eq_zero.mp)⟩
