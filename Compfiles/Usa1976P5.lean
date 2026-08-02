/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 1976, Problem 5

The polynomials a(x), b(x), c(x), d(x) satisfy
a(x⁵) + x·b(x⁵) + x²·c(x⁵) = (1 + x + x² + x³ + x⁴)·d(x).
Show that a(x) has the factor (x - 1).
-/

namespace Usa1976P5

open Polynomial

snip begin

/-- A primitive fifth root of unity in `ℂ`. -/
noncomputable abbrev ω : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (5 : ℂ)⁻¹)

lemma isPrimitiveRoot_ω : IsPrimitiveRoot ω 5 := by
  have h := Complex.isPrimitiveRoot_exp_of_coprime 1 5 (by norm_num) (by decide)
  simpa using h

lemma ω_pow_five : ω ^ 5 = 1 := isPrimitiveRoot_ω.pow_eq_one

lemma ω_ne_zero : ω ≠ 0 := Complex.exp_ne_zero _

/-- Distinct low powers of `ω` are distinct: if `0 ≤ i < j < 5` then `ω^i ≠ ω^j`. -/
lemma ω_pow_ne_pow {i j : ℕ} (hij : i < j) (hj : j < 5) : ω ^ i ≠ ω ^ j := by
  intro heq
  have hmul : ω ^ (j - i) * ω ^ i = 1 * ω ^ i := by
    rw [← pow_add, Nat.sub_add_cancel hij.le, heq, one_mul]
  have hpow : ω ^ (j - i) = 1 := mul_right_cancel₀ (pow_ne_zero _ ω_ne_zero) hmul
  obtain ⟨k, hk⟩ := isPrimitiveRoot_ω.dvd_of_pow_eq_one (j - i) hpow
  omega

/-- The geometric sum `1 + ζ + ζ² + ζ³ + ζ⁴` vanishes at any nontrivial fifth root of unity. -/
lemma geom_sum_eq_zero {ζ : ℂ} (h5 : ζ ^ 5 = 1) (hne : ζ ≠ 1) :
    1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 = 0 := by
  have h : (1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4) * (ζ - 1) = ζ ^ 5 - 1 := by ring
  rw [h5, sub_self] at h
  rcases mul_eq_zero.mp h with h' | h''
  · exact h'
  · exact absurd (eq_of_sub_eq_zero h'') hne

snip end

problem usa1976_p5 (a b c d : Polynomial ℂ)
    (h : a.comp (X ^ 5) + X * b.comp (X ^ 5) + X ^ 2 * c.comp (X ^ 5) =
        (1 + X + X ^ 2 + X ^ 3 + X ^ 4) * d) :
    X - C 1 ∣ a := by
  -- The trick: `t ↦ a(1) + b(1)·t + c(1)·t²` has degree at most 2 but vanishes at
  -- the three points `ω`, `ω²`, `ω³`, so it must be the zero polynomial.
  set f : Polynomial ℂ := C (a.eval 1) + C (b.eval 1) * X + C (c.eval 1) * X ^ 2 with hf_def
  -- Evaluating the given identity at `x = ω^j` (for `0 < j < 5`) kills the right-hand side.
  have key : ∀ j : ℕ, 0 < j → j < 5 → f.eval (ω ^ j) = 0 := by
    intro j hj0 hj5
    have hζ5 : (ω ^ j) ^ 5 = 1 := by
      rw [← pow_mul, Nat.mul_comm j 5, pow_mul, ω_pow_five, one_pow]
    have hζ1 : ω ^ j ≠ 1 := by
      intro heq
      obtain ⟨k, hk⟩ := isPrimitiveRoot_ω.dvd_of_pow_eq_one j heq
      omega
    have hgeom : 1 + ω ^ j + (ω ^ j) ^ 2 + (ω ^ j) ^ 3 + (ω ^ j) ^ 4 = 0 :=
      geom_sum_eq_zero hζ5 hζ1
    have heval := congrArg (fun p : Polynomial ℂ => p.eval (ω ^ j)) h
    simp only [eval_add, eval_mul, eval_pow, eval_comp, eval_X, eval_one] at heval
    rw [hζ5, hgeom, zero_mul] at heval
    -- `heval : a.eval 1 + ω^j * b.eval 1 + (ω^j)^2 * c.eval 1 = 0`
    have hfe : f.eval (ω ^ j) = a.eval 1 + ω ^ j * b.eval 1 + (ω ^ j) ^ 2 * c.eval 1 := by
      rw [hf_def]
      simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow]
      ring
    rw [hfe]
    exact heval
  -- `ω`, `ω²`, `ω³` are three distinct points.
  have hcard : ({ω ^ 1, ω ^ 2, ω ^ 3} : Finset ℂ).card = 3 := by
    have d12 : ω ≠ ω ^ 2 := by
      simpa using ω_pow_ne_pow (show (1 : ℕ) < 2 by norm_num) (by norm_num)
    have d13 : ω ≠ ω ^ 3 := by
      simpa using ω_pow_ne_pow (show (1 : ℕ) < 3 by norm_num) (by norm_num)
    have d23 : ω ^ 2 ≠ ω ^ 3 := ω_pow_ne_pow (by norm_num) (by norm_num)
    rw [Finset.card_insert_of_notMem (by simp [d12, d13]),
        Finset.card_insert_of_notMem (by simp [d23]),
        Finset.card_singleton]
  -- A polynomial of degree at most 2 with three roots is zero.
  have hdeg : f.natDegree ≤ 2 := by
    rw [hf_def, Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    have h0 : N ≠ 0 := by omega
    have h1 : (1 : ℕ) ≠ N := by omega
    have h2 : N ≠ 2 := by omega
    simp [coeff_add, coeff_C, coeff_C_mul, coeff_X, coeff_X_pow, h0, h1, h2]
  have hf0 : f = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' f {ω ^ 1, ω ^ 2, ω ^ 3}
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact key 1 (by norm_num) (by norm_num)
      · exact key 2 (by norm_num) (by norm_num)
      · exact key 3 (by norm_num) (by norm_num)
    · rw [hcard]
      exact lt_of_le_of_lt hdeg (by norm_num)
  -- In particular its constant coefficient `a(1)` is zero.
  have hA : a.eval 1 = 0 := by
    have hc : f.coeff 0 = a.eval 1 := by simp [hf_def]
    rw [hf0, coeff_zero] at hc
    exact hc.symm
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def]
  exact hA

end Usa1976P5
