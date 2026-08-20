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
    have hcop : j.Coprime 5 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr
        (Nat.not_dvd_of_pos_of_lt hj0 hj5)).symm
    have hζ : IsPrimitiveRoot (ω ^ j) 5 := isPrimitiveRoot_ω.pow_of_coprime j hcop
    have hζ5 : (ω ^ j) ^ 5 = 1 := hζ.pow_eq_one
    have hgeom : 1 + ω ^ j + (ω ^ j) ^ 2 + (ω ^ j) ^ 3 + (ω ^ j) ^ 4 = 0 :=
      by simpa [Finset.sum_range_succ] using hζ.geom_sum_eq_zero (by norm_num : 1 < 5)
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
  -- The powers `ω¹`, `ω²`, `ω³` are distinct because exponentiation by a
  -- primitive fifth root is injective on exponents below `5`.
  let roots := (Finset.Icc 1 3).image (ω ^ ·)
  have hcard : roots.card = 3 := by
    rw [show roots = (Finset.Icc 1 3).image (ω ^ ·) from rfl,
      Finset.card_image_iff.mpr (isPrimitiveRoot_ω.injOn_pow.mono (by
        intro j hj
        simp only [Finset.coe_Icc, Set.mem_Icc, Finset.coe_range, Set.mem_Iio] at hj ⊢
        lia)), Nat.card_Icc]
  -- A polynomial of degree at most 2 with three roots is zero.
  have hdeg : f.natDegree ≤ 2 := by
    rw [hf_def]
    apply Polynomial.natDegree_add_le_of_degree_le
    · apply Polynomial.natDegree_add_le_of_degree_le
      · simp
      · exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
    · exact Polynomial.natDegree_C_mul_X_pow_le _ _
  have hf0 : f = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' f roots
    · intro x hx
      change x ∈ (Finset.Icc 1 3).image (ω ^ ·) at hx
      rw [Finset.mem_image] at hx
      obtain ⟨j, hj, rfl⟩ := hx
      rw [Finset.mem_Icc] at hj
      exact key j (by lia) (by lia)
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
