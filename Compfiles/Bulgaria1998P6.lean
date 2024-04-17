/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# Bulgarian Mathematical Olympiad 1998, Problem 6

Prove that the equation

     x²y² = z²(z² - x² - y²)

has no solutions in positive integers.

-/

namespace Bulgaria1998P6

snip begin

lemma lemma_1'
    (a b c : ℕ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (h : a^4 = b^4 + c^2) : False := by
  induction' a using Nat.strongInductionOn with a ih
  have hab : Nat.gcd a b = 1 := sorry
  obtain c_even | c_odd := Nat.even_or_odd c
  · have a_odd : Odd a := sorry
    have b_odd : Odd b := sorry
    sorry
  · sorry

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
    (_hz : 0 < z)
    (h : x^2 * y^2 = z^2 * (z^2 - x^2 - y^2)) :
    False := by
  -- Follows the informal solution in _Mathematical Olympiads 1998-1999_
  -- (edited by Titu Andreescu and Zuming Feng)

  have h1 : 1 * (z^2) * (z^2) + (- (x^2 + y^2)) * z^2 + - (x^2 * y^2) = 0 := by
    rw[h]; ring
  have : NeZero (2 : ℤ) := CharZero.NeZero.two
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
  have ha' : 0 < a := by positivity
  have hb' : 0 < b := by positivity
  have hc' : 0 < |c| := by
    obtain hc1 | hc2 | hc3 := lt_trichotomy 0 |c|
    · exact hc1
    · have hab : a^2 = b^2 := by
        rw [← hc2, zero_pow (by norm_num)] at hc
        have hc3 : (a^2)^2 = (b^2)^2 := by linear_combination hc
        have hap : 0 ≤ a^2 := by positivity
        have hbp : 0 ≤ b^2 := by positivity
        exact (pow_left_inj hap hbp two_ne_zero).mp hc3
      rw [hab] at h4
      obtain ⟨r, hr⟩ := h4
      rw [←two_mul, ←sq] at hr
      have h10 : b^2 ∣ r^2 := Dvd.intro_left _ hr
      rw [Int.pow_dvd_pow_iff two_ne_zero] at h10
      obtain ⟨e, rfl⟩ := h10
      rw [show (b * e)^2 = e^2 * b^2 by ring] at hr
      have h11 : b^2 ≠ 0 := by positivity
      have h12 : 2 = e^2 := (Int.mul_eq_mul_right_iff h11).mp hr
      clear h h1 h3 h5 hab
      have h13 : e < 2 := by
        by_contra! H
        have h20 : 2^2 ≤ e^2 := by gcongr
        rw [←h12] at h20
        norm_num at h20
      have h14 : -2 < e := by
        by_contra! H
        replace H : 2 ≤ -e := Int.le_neg_of_le_neg H
        have h20 : 2^2 ≤ (-e)^2 := by gcongr
        rw [neg_sq, ←h12] at h20
        norm_num at h20
      interval_cases e <;> linarith
    · exact (Int.not_lt.mpr (abs_nonneg c) hc3).elim
  exact lemma_1 ha' hb' hc' hc
