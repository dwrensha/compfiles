/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 1989, Problem 5

Let u and v be real numbers such that

(u + u² + u³ + ⋯ + u⁸) + 10u⁹ = (v + v² + v³ + ⋯ + v¹⁰) + 10v¹¹ = 8.

Determine, with proof, which of the two numbers, u or v, is larger.
-/

namespace Usa1989P5

open scoped BigOperators

determine u_is_larger : Bool := false

problem usa1989_p5
    (u v : ℝ)
    (hu : (∑ i in Finset.range 8, u^(i + 1)) + 10 * u^9 = 8)
    (hv : (∑ i in Finset.range 10, v^(i + 1)) + 10 * v^11 = 8) :
    if u_is_larger then v < u else u < v := by
  -- solution from
  -- https://artofproblemsolving.com/wiki/index.php/1989_USAMO_Problems/Problem_5
  simp only [ite_false]

  let U (x : ℝ) : ℝ := (∑ i in Finset.range 8, x^(i + 1)) + 10 * x^9
  let V (x : ℝ) : ℝ := (∑ i in Finset.range 10, x^(i + 1)) + 10 * x^11

  change U u = 8 at hu
  change V v = 8 at hv

  have hU : ∀ x, x ≠ 1 → U x = (x^10 - x) / (x - 1) + 9 * x^9 := fun x hx ↦ by
    convert_to U x = x * ((x^9 - 1) / (x - 1)) + 9 * x^9
    · ring
    rw [←geom_sum_eq hx 9, Finset.mul_sum]
    have h1 : ∀ i, i ∈ Finset.range 9 → x * x^i = x ^(i + 1) := fun i _ ↦ (pow_succ' x i).symm
    rw [Finset.sum_congr rfl h1, Finset.sum_range_succ]
    ring

  have hV : ∀ x, x ≠ 1 → V x = (x^12 - x) / (x - 1) + 9 * x^11 := fun x hx ↦ by
    convert_to V x = x * ((x^11 - 1) / (x - 1)) + 9 * x^11
    · ring
    rw [←geom_sum_eq hx 11, Finset.mul_sum]
    have h1 : ∀ i, i ∈ Finset.range 11 → x * x^i = x ^(i + 1) := fun i _ ↦ (pow_succ' x i).symm
    rw [Finset.sum_congr rfl h1, Finset.sum_range_succ]
    ring

  have h1 : ∀ x : ℝ, x ≤ 0 → (U x ≤ 0 ∧ V x ≤ 0) := fun x hx ↦ by
    have h2 : 0 ≤ -x := neg_nonneg.mpr hx
    have h4 : x - 1 < 0 := sub_neg.mpr (lt_of_le_of_lt hx zero_lt_one)
    have h6 : x ≠ 1 := by linarith
    constructor
    · have h3 : 0 ≤ x^10 - x := by change 0 ≤ x^10 + - x; positivity
      rw [hU x h6]
      have h8 : (x ^ 10 - x) / (x - 1) ≤ 0 := by
        obtain h7 | h7 : x^10 - x = 0 ∨ 0 < x^10 - x := h3.eq_or_gt
        · rw [h7]; simp
        · exact (div_neg_of_pos_of_neg h7 h4).le
      have h5 : 9 * x^9 ≤ 0 := by
        suffices H : 0 ≤ (-x)^9 by linarith
        positivity
      exact add_nonpos h8 h5
    · have h3 : 0 ≤ x^12 - x := by change 0 ≤ x^12 + - x; positivity
      rw [hV x h6]
      have h8 : (x ^ 12 - x) / (x - 1) ≤ 0 := by
        obtain h7 | h7 : x^12 - x = 0 ∨ 0 < x^12 - x := h3.eq_or_gt
        · rw [h7]; simp
        · exact (div_neg_of_pos_of_neg h7 h4).le
      have h5 : 9 * x^11 ≤ 0 := by
        suffices H : 0 ≤ (-x)^11 by linarith
        positivity
      exact add_nonpos h8 h5

  have h1u : ¬ u ≤ 0 := fun hun ↦ by linarith[(h1 u hun).1]
  have h1v : ¬ v ≤ 0 := fun hvn ↦ by linarith[(h1 v hvn).2]

  have h2 : ¬ 9/10 ≤ u := by
    intro hu9
    have : 8 < U u := by
      have h6 : U (9 / 10) ≤ U u := by dsimp only [U]; gcongr
      norm_num at h6
      dsimp only [U]
      linarith
    linarith

  have h5 : 0 < u := not_le.mp h1u
  have h5' : 0 < u^9 := pow_pos h5 9
  have h6 : u^9 * (10 * u - 9) < 0 := by nlinarith
  have h8 : u^9 * (10 * u - 9) * (u + 1) < 0 := by nlinarith

  have h9 : V u - U u = 10 * u^11 + u^10 - 9 * u^9 := by
    dsimp only [V, U]
    nth_rw 1 [Finset.sum_range_succ]
    nth_rw 1 [Finset.sum_range_succ]
    ring

  have h3 : V u < U u := by
    calc _ = U u + (V u - U u) := by ring
         _ = U u + (10 * u^11 + u^10 - 9 * u^9) := by rw [h9]
         _ = U u + u^9 * (10 * u - 9) * (u + 1) := by ring
         _ < _ := by linarith
  have h10 : V u < V v := by
    calc _ < _ := h3
         _ = 8 := hu
         _ = _ := hv.symm

  by_contra! H

  have h11 : 0 < v := not_le.mp h1v
  have h16 : V v ≤ V u := by dsimp only [V]; gcongr

  exact (not_lt.mpr h16 h10).elim
