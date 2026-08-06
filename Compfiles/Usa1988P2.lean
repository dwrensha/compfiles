/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Polynomial.Derivative
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 1988, Problem 2

The cubic x^3 + ax^2 + bx + c has real coefficients and three real roots
r ≥ s ≥ t. Show that k = a^2 - 3b ≥ 0 and that √k ≤ r - t.
-/

namespace Usa1988P2

open Polynomial

snip begin

-- Solution adapted from https://prase.cz/kalva/usa/usoln/usol882.html
-- By Vieta's formulas a = -(r + s + t) and b = rs + st + tr, so
-- a^2 - 3b = r^2 + s^2 + t^2 - (rs + st + tr), a sum of squares,
-- and (r - t)^2 - (a^2 - 3b) = (r - s)(s - t) ≥ 0.

-- Vieta's formulas for a and b, obtained by differentiating the
-- polynomial identity once resp. twice and evaluating at 0.
lemma vieta (a b c r s t : ℝ)
    (h : (X - C r) * (X - C s) * (X - C t) = X ^ 3 + C a * X ^ 2 + C b * X + C c) :
    a = -(r + s + t) ∧ b = r * s + s * t + t * r := by
  constructor
  · apply_fun (·.derivative.derivative.eval 0) at h
    simp at h
    linarith
  · apply_fun (·.derivative.eval 0) at h
    simp at h
    linarith

snip end

problem usa1988_p2 (a b c r s t : ℝ) (hrs : s ≤ r) (hst : t ≤ s)
    (hroots : (X - C r) * (X - C s) * (X - C t)
      = X ^ 3 + C a * X ^ 2 + C b * X + C c) :
    0 ≤ a ^ 2 - 3 * b ∧ Real.sqrt (a ^ 2 - 3 * b) ≤ r - t := by
  obtain ⟨ha, hb⟩ := vieta a b c r s t hroots
  have hk : a ^ 2 - 3 * b = r ^ 2 + s ^ 2 + t ^ 2 - (r * s + s * t + t * r) := by
    rw [ha, hb]; ring
  refine ⟨?_, ?_⟩
  · -- a^2 - 3b = ½((r - s)^2 + (s - t)^2 + (r - t)^2) ≥ 0
    rw [hk]
    nlinarith [sq_nonneg (r - s), sq_nonneg (s - t), sq_nonneg (r - t)]
  · have hle : a ^ 2 - 3 * b ≤ (r - t) ^ 2 := by
      -- (r - t)^2 - (a^2 - 3b) = (r - s)(s - t) ≥ 0
      rw [hk]
      nlinarith [mul_nonneg (sub_nonneg.mpr hrs) (sub_nonneg.mpr hst)]
    have hrt : 0 ≤ r - t := by linarith
    calc Real.sqrt (a ^ 2 - 3 * b) ≤ Real.sqrt ((r - t) ^ 2) :=
          Real.sqrt_le_sqrt hle
      _ = r - t := Real.sqrt_sq hrt

end Usa1988P2
