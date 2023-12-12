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

lemma lemma_1'
    (s t u : ℕ)
    (hs : 0 < s)
    (ht : 0 < t)
    (hu : 0 < u)
    (h : s^4 = t^4 + u^2) : False := by
  induction' s using Nat.strongInductionOn with s ih
  sorry

lemma lemma_1
    {s t u : ℤ}
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
  -- Follows the informal solution in _Mathematical Olympiads 1998-1999_
  -- (edited by Titu Andreescu and Zuming Feng)

  have h1 : 1 * (z^2) * (z^2) + (- (x^2 + y^2)) * z^2 + - (x^2 * y^2) = 0 := by
    rw[h]; ring
  have : NeZero (2 : ℤ) := CharZero.NeZero.two ℤ
  have h2 := (quadratic_eq_zero_iff_discrim_eq_sq one_ne_zero (z^2)).mp h1
  dsimp [discrim] at h2
  let a := x^2 + y^2
  let b := 2 * x * y
  have h3 : a^2 + b^2  = (2 * z ^ 2 - (x ^ 2 + y ^ 2)) ^ 2 :=
     by linear_combination h2
  have h4 : IsSquare (a^2 + b^2) := by use 2 * z ^ 2 - (x ^ 2 + y ^ 2); rwa [←sq]
  have h5 : IsSquare (a^2 - b^2) := by use (x^2 - y^2); ring
  have h6 : IsSquare ((a^2 + b^2) * (a^2 - b^2)) := IsSquare.mul h4 h5
  rw [show (a^2 + b^2) * (a^2 - b^2) = a^4 - b^4 by ring] at h6
  obtain ⟨c, hc⟩ := h6
  rw [←sq, ←sq_abs] at hc
  obtain ⟨c', rfl⟩ := @exists_eq _ |c|
  have ha' : 0 < a := by positivity
  have hb' : 0 < b := by positivity
  have hc' : 0 < |c| := by
    obtain hc1 | hc2 | hc3 := lt_trichotomy 0 |c|
    · exact hc1
    · have hab : a^2 = b^2 := by sorry
      rw [hab] at h4
      obtain ⟨r, hr⟩ := h4
      sorry
    · exact (Int.not_lt.mpr (abs_nonneg c) hc3).elim
  exact lemma_1 ha' hb' hc' hc
