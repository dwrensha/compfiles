/-
Copyright (c) 2026 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 1989, Problem 3

Let P(z) = zⁿ + c₁zⁿ⁻¹ + ⋯ + cₙ be a polynomial in the complex variable z,
with real coefficients cₖ. Suppose that |P(i)| < 1. Prove that there exist
real numbers a and b such that P(a + bi) = 0 and (a² + b² + 1)² < 4b² + 1.
-/

namespace Usa1989P3

open Polynomial

snip begin

/-- Evaluating a polynomial whose coefficients are all real at the conjugate
of `z` is the same as conjugating its value at `z`. -/
theorem star_eval {P : ℂ[X]} (hreal : ∀ n : ℕ, (P.coeff n).im = 0) (z : ℂ) :
    star (P.eval z) = P.eval (star z) := by
  have h : (starRingEnd ℂ) (P.eval z) = P.eval ((starRingEnd ℂ) z) := by
    rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range, map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_mul, map_pow]
    congr 1
    rw [starRingEnd_apply, Complex.star_def, Complex.conj_eq_iff_im]
    exact hreal k
  exact h

/-- For a complex number `r`, the product of the squared distances from `r`
to `i` and to `-i` equals `(r.re² + r.im² + 1)² - 4 r.im²`. -/
theorem normSq_I_sub_mul_normSq_I_add (r : ℂ) :
    Complex.normSq (Complex.I - r) * Complex.normSq (Complex.I + r) =
      (r.re ^ 2 + r.im ^ 2 + 1) ^ 2 - 4 * r.im ^ 2 := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.I_re, Complex.I_im]
  ring

/-- The squared distances from the roots of a monic polynomial to a point `z`
multiply to the squared norm of the value of the polynomial at `z`. -/
theorem prod_normSq_sub_roots {P : ℂ[X]} (hsplit : P.Splits) (hmonic : P.Monic) (z : ℂ) :
    (P.roots.map fun r ↦ Complex.normSq (z - r)).prod =
      Complex.normSq (P.eval z) := by
  rw [hsplit.eval_eq_prod_roots_of_monic hmonic, map_multiset_prod, Multiset.map_map]
  rfl

/-- The squared distances from the roots of a monic polynomial to a point `z`,
with signs flipped, again multiply to the squared norm of the value of the
polynomial at `-z`. -/
theorem prod_normSq_add_roots {P : ℂ[X]} (hsplit : P.Splits) (hmonic : P.Monic) (z : ℂ) :
    (P.roots.map fun r ↦ Complex.normSq (z + r)).prod =
      Complex.normSq (P.eval (-z)) := by
  have h1 : (fun r : ℂ ↦ Complex.normSq (z + r)) = fun r ↦ Complex.normSq (-z - r) := by
    funext r
    have h2 : z + r = -(-z - r) := by ring
    rw [h2, Complex.normSq_neg]
  rw [h1, prod_normSq_sub_roots hsplit hmonic (-z)]

snip end

problem usa1989_p3
    (P : ℂ[X]) (hmonic : P.Monic)
    (hreal : ∀ n : ℕ, (P.coeff n).im = 0)
    (hP : ‖P.eval Complex.I‖ < 1) :
    ∃ a b : ℝ, P.eval (a + b * Complex.I) = 0 ∧
      (a ^ 2 + b ^ 2 + 1) ^ 2 < 4 * b ^ 2 + 1 := by
  -- Solution: factor P over ℂ as ∏ (z - rⱼ). Then
  -- |P(i)|² |P(-i)|² = ∏ⱼ |i - rⱼ|² |i + rⱼ|² = ∏ⱼ ((aⱼ² + bⱼ² + 1)² - 4bⱼ²).
  -- Since P has real coefficients, P(-i) = conj(P(i)), so the left side
  -- is |P(i)|⁴ < 1. Hence some factor is less than 1, i.e. some root
  -- a + bi satisfies (a² + b² + 1)² < 4b² + 1.
  have hsplit : P.Splits := Complex.isAlgClosed.splits P
  have hne : P ≠ 0 := hmonic.ne_zero
  have hP2 : Complex.normSq (P.eval Complex.I) < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (P.eval Complex.I), hP]
  by_contra hcon
  push Not at hcon
  -- Every root contributes a factor that is at least 1.
  have hfactor : ∀ r ∈ P.roots,
      1 ≤ Complex.normSq (Complex.I - r) * Complex.normSq (Complex.I + r) := by
    intro r hr
    have hroot : P.eval r = 0 := (Polynomial.mem_roots hne).mp hr
    rw [← Complex.re_add_im r] at hroot
    have hge := hcon r.re r.im hroot
    rw [normSq_I_sub_mul_normSq_I_add]
    linarith [hge]
  have hprod_ge : 1 ≤ (P.roots.map fun r ↦
        Complex.normSq (Complex.I - r) * Complex.normSq (Complex.I + r)).prod := by
    apply Multiset.one_le_prod
    intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨r, hr, rfl⟩ := hx
    exact hfactor r hr
  -- But the product of all the factors equals ‖P.eval i‖⁴ < 1.
  have hstar : P.eval (-Complex.I) = star (P.eval Complex.I) := by
    rw [star_eval hreal]
    congr 1
    simp [Complex.conj_I]
  have hprod_eq : (P.roots.map fun r ↦
        Complex.normSq (Complex.I - r) * Complex.normSq (Complex.I + r)).prod =
      (Complex.normSq (P.eval Complex.I)) ^ 2 := by
    rw [Multiset.prod_map_mul, prod_normSq_sub_roots hsplit hmonic,
      prod_normSq_add_roots hsplit hmonic, hstar, Complex.star_def,
      Complex.normSq_conj, pow_two]
  rw [hprod_eq] at hprod_ge
  have hs0 : 0 ≤ Complex.normSq (P.eval Complex.I) := Complex.normSq_nonneg _
  nlinarith [hprod_ge, hP2, hs0]

end Usa1989P3
