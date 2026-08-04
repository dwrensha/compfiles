/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pacmanboss256
-/

module

public import Mathlib.Tactic

public import ProblemExtraction

@[expose] public section


problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 1988, Problem 2
The cubic polynomial $x^3+ax^2+bx+c$ has real coefficients and three real roots $r\ge s\ge t$. Show that $k=a^2-3b\ge 0$ and that $\sqrt k\le r-t$.
-/

namespace USA1988P2
open Polynomial

snip begin
lemma vieta (a b c r s t :ℝ)
    (hpol : X^3 + C a * X^2 + C b * X + C c = (X - C r) * (X - C s) * (X - C t)) :
    a = - (r + s + t) ∧ b = (r*s + s*t + r*t) := by
    constructor
    · apply_fun (·.derivative.derivative.eval 0) at hpol
      simp at hpol
      ring_nf at hpol
      rw [sub_sub, neg_sub_left,  ←add_mul, ←add_mul, ← neg_mul] at hpol
      simp at hpol
      rwa [← neg_add, ← neg_add, add_comm] at hpol
    apply_fun (·.derivative.eval 0) at hpol
    simp at hpol
    ring_nf at hpol
    rwa [mul_comm] at hpol


snip end

problem usa1988_p2 (a b c r s t k : ℝ) (hk : k = a^2 - 3*b)(hpol: X^3 + C a * X^2 + C b * X + C c = (X - C r) * (X - C s) * (X - C t))(hrs: s ≤ r)(hst : t ≤ s) : 0 ≤ k ∧ Real.sqrt k ≤ r - t := by
  have hab := vieta a b c r s t hpol
  obtain ⟨ha, hb⟩ := hab
  rw [ha, hb] at hk
  ring_nf at hk
  have two_k : 2*k = (r-s)^2+(s-t)^2 +(r-t)^2 := by
    rw [hk]
    ring_nf
  constructor
  · have k_nonneg : 0 ≤ (r-s)^2+(s-t)^2 +(r-t)^2 := by
      apply add_nonneg
      · apply add_nonneg
        · apply sq_nonneg
        apply sq_nonneg
      apply sq_nonneg
    linarith
  rw [Real.sqrt_le_iff]
  constructor
  · linarith
  rw [hk]
  suffices h : 0 ≤ (r-s)*(s-t) by linear_combination h
  refine mul_nonneg ?_ ?_ <;> linarith


end USA1988P2
