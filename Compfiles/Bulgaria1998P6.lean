/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Data.Int.Basic
import Mathlib.Order.WellFounded
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Ring

import ProblemExtraction

problem_file

/-!
Bulgarian Mathematical Olympiad 1998, Problem 6

Prove that the equation

     x²y² = z²(z² - x² - y²)

has no solutions in positive integers.

-/

namespace Bulgaria1998P6

snip begin

lemma lemma_0
    (a b c x : ℤ)
    (h : a * x^2 + b * x + c = 0) :
    (∃ d : ℤ, d^2 = b^2 - 4 * a * c) := by
  by_cases ha : a ≠ 0
  · use 2 * a * x + b
    refine' ((quadratic_eq_zero_iff_discrim_eq_sq ha x).mp _).symm
    rw [←h, pow_two, mul_assoc]
  · rw [not_not] at ha
    simp only [ha, mul_zero, zero_mul, sub_zero, ge_iff_le, exists_apply_eq_apply] at *

lemma lemma_1'
    (s t u : ℕ)
    (hs : 0 < s)
    (ht : 0 < t)
    (hu : 0 < u)
    (h : s^4 = t^4 + u^2) : False := by
  induction' s using Nat.strongInductionOn with s ih
  sorry

lemma lemma_1
    (s t u : ℤ)
    (hs : 0 < s)
    (ht : 0 < t)
    (hu : 0 < u)
    (h : s^4 - t^4 = u^2) : False := by
  replace h : s^4 = t^4 + u^2 := eq_add_of_sub_eq' h
  lift s to ℕ using Int.le_of_lt hs
  lift t to ℕ using Int.le_of_lt ht
  lift u to ℕ using Int.le_of_lt hu
  replace hs : 0 < s := Int.ofNat_pos.mp hs
  replace ht : 0 < t := Int.ofNat_pos.mp ht
  replace hy : 0 < u := Int.ofNat_pos.mp hu
  have h' : s ^ 4 = t ^ 4 + u ^ 2 := by exact Int.ofNat_inj.mp h
  exact lemma_1' s t u hs ht hy h'

snip end

problem bulgaria1998_p6
    (x y z : ℤ)
    (hx : 0 < x)
    (hy : 0 < y)
    (hz : 0 < z)
    (h : x^2 * y^2 = z^2 * (z^2 - x^2 - y^2)) :
    False := by
  have : 0 = (z^2)^2 - z^2 * (x^2 + y^2) - x^2 * y^2 := by rw[h]; ring
  sorry
