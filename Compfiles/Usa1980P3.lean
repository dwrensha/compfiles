/-
Copyright (c) 2026 pacmanboss256. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pacmanboss256
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file {
  tags := [.Algebra]
}

/-!
# USA Mathematical Olympiad 1980, Problem 3

A + B + C is an integral multiple of π. x, y, z are real numbers. If x sin A + y sin B + z sin C = x^2 sin 2A + y^2 sin 2B + z^2 sin 2C = 0, show that x^n sin nA + y^n sin n^B + z^n sin nC = 0 for any positive integer n.
-/

snip begin
-- Solution adapted from Art of Problem Solving.
-- The statement asks for positive integer n, but the proof also needs the base case of n = 0.
-- Newton's Identities
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/MvPolynomial/Symmetric/NewtonIdentities.html#MvPolynomial.mul_esymm_eq_sum
-- MvPolynomial.mul_esymm_eq_sum

-- de Movire's Theorem
-- Complex.cos_add_sin_mul_I_pow
open MvPolynomial

snip end

namespace Usa1980P3

open Real

problem usa1980_p3 (x y z A B C: ℝ) (habc: ∃ k : ℤ, A + B + C = k * π)
  (h1: x*sin A + y*sin B + z*sin C = 0)
  (h2: x^2 * sin (2*A) + y^2 * sin (2*B) + z^2 * sin (2*C) = 0)
  : ∀ n : ℕ, x^n * sin (n*A) + y^n * sin (n*B) + z^n * sin (n*C) = 0 := by
  have h_Movire := Complex.cos_add_sin_mul_I_pow
  simp_rw [Complex.cos_add_sin_I] at h_Movire
  let a := x * Complex.exp (A * Complex.I)
  let b := y * Complex.exp (B * Complex.I)
  let c := z * Complex.exp (C * Complex.I)
  -- We don't actually need to name these
  let s₁ := a + b + c
  let s₂ := a * b + b * c + c * a
  let s₃ := a * b * c
  lift s₃ to ℝ with s₃' hs₃
  · rcases habc with ⟨k, h⟩
    refine Complex.sq_nonneg_iff.mp ?_
    simp only [s₃, a, b, c]
    -- need to do this awkward maneuver instead of using `suffices` to avoid invoking LE ℂ
    have :
      ↑x * Complex.exp (↑A * Complex.I) * (↑y * Complex.exp (↑B * Complex.I)) * (↑z * Complex.exp (↑C * Complex.I))
       = ↑x * ↑y * ↑z * (Complex.exp (↑A * Complex.I) * Complex.exp (↑B * Complex.I) * Complex.exp (↑C * Complex.I)) := by field_simp
    rw [this, mul_pow]
    norm_cast
    simp_rw [← Complex.exp_add, ← Complex.exp_nat_mul]
    rw [Complex.exp_eq_one_iff.mpr ⟨k, ?_⟩]
    · norm_cast; simpa using sq_nonneg _
    · simp_rw [← add_mul, ← Complex.ofReal_add, h]
      push_cast
      field_simp
  lift s₁ to ℝ with s₁' hs₁
  · simp only [s₁, a, b, c]
    rw [Complex.exp_eq_exp_re_mul_sin_add_cos (A * _),Complex.exp_eq_exp_re_mul_sin_add_cos (B * _), Complex.exp_eq_exp_re_mul_sin_add_cos (C * _)]
    simp [Complex.sin_ofReal_re, h1]
  lift a^2 + b^2 + c^2 to ℝ with s₄' hs₄
  · simp only [a, b, c, mul_pow, h_Movire]
    simp_rw [← Complex.cos_add_sin_I]
    norm_cast
    simp [-Complex.ofReal_cos, -Complex.ofReal_sin]
    norm_cast
    linarith
  lift s₂ to ℝ with s₂' hs₂
  · suffices h : s₂ = (s₁' ^ 2 - s₄') / 2 by rw [h]; norm_cast
    simp only [hs₁, s₁, s₂, hs₄]
    ring_nf
  let p (k : ℕ) := a ^ k + b ^ k + c ^ k
  let σ := ({a, b, c} : Finset ℂ)
  --   sorry
  have sum (i : ℕ) : p (i+3) = s₁ * p (i+2) - s₂ * p (i+1) + s₃ * p i := by
    -- have := MvPolynomial.sum_antidiagonal_card_esymm_psum_eq_zero ({a, b, c} : Finset ℂ) ℂ
    have := psum_eq_mul_esymm_sub_sum ({a, b, c} : Finset ℂ) ℂ 3 (by lia)
    rw [MvPolynomial.ext_iff] at this
    -- simp [Finset.sum] at this
    sorry
  have h_equiv (n : ℕ) : x^n * sin (n*A) + y^n * sin (n*B) + z^n * sin (n*C) = 0 ↔ (p n).im = 0 := by
    simp [p, a, b, c, mul_pow, h_Movire]
    norm_cast at ⊢
    simp
    norm_cast
    simp only [Complex.exp_ofReal_mul_I_im]
  intro n
  induction n using Nat.stepInduction 3 with
  | base n hn =>
    rcases n with (rfl | rfl | rfl | _) <;> try lia
    simp [↓h_equiv, p]
  | step n ih =>
    rw [h_equiv]
    norm_cast at ih
    simp_rw [h_equiv] at ih
    simpa [sum n, ← hs₁, ← hs₂, ← hs₃, ih] using Or.inr $ ih 0 (by lia)

end Usa1980P3
