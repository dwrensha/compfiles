/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pedro Duailibe
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1966, Problem 4

Prove that for every natural number n and for every real
number x that is not of the form kπ/2ᵗ for t a non-negative
integer and k any integer,

 1 / (sin 2x) + 1 / (sin 4x) + ... + 1 / (sin 2ⁿx) = cot x - cot 2ⁿ x.
-/

namespace Imo1966P4

problem imo1966_p4 (n : ℕ) (x : ℝ)
    (hx : ∀ t : ℕ, ∀ k : ℤ, x ≠ k * Real.pi / 2^t) :
    ∑ i ∈ Finset.range n, 1 / Real.sin (2^(i + 1) * x) =
    Real.cot x - Real.cot (2^n * x) := by
  induction n with
  | zero =>
      rw [Finset.range_zero, Finset.sum_empty, pow_zero, one_mul, sub_self]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      let θ := 2 ^ n * x
      have hθ : θ = 2 ^ n * x := by rfl
      have h₀ : Real.sin (2^(n+1) * x) ≠ 0 := by
        intro h
        rw [Real.sin_eq_zero_iff] at h
        obtain ⟨k, hk⟩ := h
        apply hx (n+1) k
        rw [eq_div_iff (pow_ne_zero (n+1) (by norm_num)), mul_comm, ← hk]
      have h₁ : Real.sin θ ≠ 0 ∧ Real.cos θ ≠ 0 := by
        rw [pow_succ, mul_comm (2^n) 2, mul_assoc, ← hθ] at h₀
        rw [Real.sin_two_mul] at h₀
        constructor
        · rw [mul_comm 2, mul_assoc] at h₀
          apply left_ne_zero_of_mul h₀
        · exact right_ne_zero_of_mul h₀
      have h : 1 / Real.sin (2 * θ) = Real.cot θ - Real.cot (2 * θ) := by
        simp only [Real.cot_eq_cos_div_sin]
        rw [Real.sin_two_mul, Real.cos_two_mul]
        field_simp [h₁]
        ring
      rw [pow_succ, mul_comm (2^n) 2, mul_assoc, ← hθ, h]
      abel

end Imo1966P4
