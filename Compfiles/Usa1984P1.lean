/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 1984, Problem 1

Two roots of the real quartic x⁴ - 18x³ + ax² + 200x - 1984 = 0
have product -32. Find a.
-/

namespace Usa1984P1

open Polynomial

determine solution : ℝ := 86

snip begin

/-- A monic quadratic polynomial is determined by its lower coefficients. -/
theorem eq_X_sq_add_of_monic_of_natDegree_eq_two {R : Type*} [CommRing R] {q : R[X]}
    (hm : q.Monic) (hd : q.natDegree = 2) :
    q = X ^ 2 + C (q.coeff 1) * X + C (q.coeff 0) := by
  conv_lhs => rw [q.as_sum_range_C_mul_X_pow, hd]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  have hc2 : q.coeff 2 = 1 := by
    have h := hm.coeff_natDegree
    rwa [hd] at h
  simp only [hc2, map_one]
  ring

snip end

problem usa1984_p1 (a : ℝ) (P : ℝ[X])
    (hP : P = X ^ 4 - 18 * X ^ 3 + C a * X ^ 2 + 200 * X - 1984)
    (x₁ x₂ : ℂ) (hx : x₁ ≠ x₂)
    (h₁ : aeval x₁ P = 0) (h₂ : aeval x₂ P = 0) (hprod : x₁ * x₂ = -32) :
    a = solution := by
  -- Move everything to `ℂ[X]`.
  set Q : ℂ[X] := P.map (algebraMap ℝ ℂ) with hQdef
  have hQ : Q = X ^ 4 + C (-18) * X ^ 3 + C (a : ℂ) * X ^ 2 + C 200 * X + C (-1984) := by
    rw [hQdef, hP]
    simp [← C_ofNat, sub_eq_add_neg]
  -- The two given complex roots provide a quadratic factor of `Q`.
  have hroot₁ : Q.IsRoot x₁ := by
    rw [Polynomial.IsRoot.def, hQdef, ← eval₂_eq_eval_map]
    exact h₁
  have hroot₂ : Q.IsRoot x₂ := by
    rw [Polynomial.IsRoot.def, hQdef, ← eval₂_eq_eval_map]
    exact h₂
  have hdvd₁ : (X - C x₁ : ℂ[X]) ∣ Q := dvd_iff_isRoot.mpr hroot₁
  have hdvd₂ : (X - C x₂ : ℂ[X]) ∣ Q := dvd_iff_isRoot.mpr hroot₂
  have hcop : IsCoprime (X - C x₁ : ℂ[X]) (X - C x₂) :=
    isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hx))
  obtain ⟨q, hq⟩ := hcop.mul_dvd hdvd₁ hdvd₂
  -- Degree bookkeeping: the complementary factor `q` is a monic quadratic.
  have hfmonic : ((X - C x₁) * (X - C x₂) : ℂ[X]).Monic :=
    (monic_X_sub_C x₁).mul (monic_X_sub_C x₂)
  have hcoeff4 : Q.coeff 4 = 1 := by
    rw [hQ]
    simp [coeff_add, coeff_X_pow]
  have hQdeg : Q.natDegree = 4 := by
    apply le_antisymm
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro m hm
      rw [hQ]
      simp only [coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow, coeff_X_pow]
      rw [if_neg (show m ≠ 4 by omega), if_neg (show m ≠ 3 by omega),
        if_neg (show m ≠ 2 by omega), if_neg (show m ≠ 1 by omega),
        if_neg (show m ≠ 0 by omega)]
      simp
    · exact le_natDegree_of_ne_zero (hcoeff4 ▸ one_ne_zero)
  have hQmonic : Q.Monic := by
    show Q.leadingCoeff = 1
    rw [leadingCoeff, hQdeg]
    exact hcoeff4
  have hqmonic : q.Monic := by
    have h := hQmonic.leadingCoeff
    rw [hq, leadingCoeff_mul, hfmonic.leadingCoeff, one_mul] at h
    exact h
  have hqdeg : q.natDegree = 2 := by
    have hfdeg : ((X - C x₁) * (X - C x₂) : ℂ[X]).natDegree = 2 := by
      rw [natDegree_mul (X_sub_C_ne_zero x₁) (X_sub_C_ne_zero x₂),
        natDegree_X_sub_C, natDegree_X_sub_C]
    have h := hQdeg
    rw [hq, natDegree_mul hfmonic.ne_zero hqmonic.ne_zero, hfdeg] at h
    omega
  -- The factorization in standard form.
  have hfac : (X - C x₁) * (X - C x₂) = X ^ 2 - C (x₁ + x₂) * X + C (x₁ * x₂) := by
    simp [map_add, map_mul]
    ring
  rw [hprod] at hfac
  have hqform : q = X ^ 2 + C (q.coeff 1) * X + C (q.coeff 0) :=
    eq_X_sq_add_of_monic_of_natDegree_eq_two hqmonic hqdeg
  have hBig : Q = (X ^ 2 - C (x₁ + x₂) * X + C (-32 : ℂ)) *
      (X ^ 2 + C (q.coeff 1) * X + C (q.coeff 0)) := by
    rw [hq]
    conv_lhs => rw [hfac, hqform]
  have hexpand : (X ^ 2 - C (x₁ + x₂) * X + C (-32 : ℂ)) *
        (X ^ 2 + C (q.coeff 1) * X + C (q.coeff 0))
      = X ^ 4 + C (q.coeff 1 - (x₁ + x₂)) * X ^ 3
        + C (q.coeff 0 + (-32) - (x₁ + x₂) * q.coeff 1) * X ^ 2
        + C ((-32) * q.coeff 1 - (x₁ + x₂) * q.coeff 0) * X
        + C ((-32) * q.coeff 0) := by
    simp only [map_add, map_sub, map_mul, map_neg, map_ofNat]
    ring
  have hBig2 : X ^ 4 + C (-18) * X ^ 3 + C (a : ℂ) * X ^ 2 + C 200 * X + C (-1984)
      = X ^ 4 + C (q.coeff 1 - (x₁ + x₂)) * X ^ 3
        + C (q.coeff 0 + (-32) - (x₁ + x₂) * q.coeff 1) * X ^ 2
        + C ((-32) * q.coeff 1 - (x₁ + x₂) * q.coeff 0) * X
        + C ((-32) * q.coeff 0) :=
    hQ.symm.trans (hBig.trans hexpand)
  -- Compare coefficients of `X⁰, X¹, X², X³` on both sides.
  have e0 := congrArg (fun f : ℂ[X] => f.coeff 0) hBig2
  have e1 := congrArg (fun f : ℂ[X] => f.coeff 1) hBig2
  have e2 := congrArg (fun f : ℂ[X] => f.coeff 2) hBig2
  have e3 := congrArg (fun f : ℂ[X] => f.coeff 3) hBig2
  simp only [coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow, coeff_X_pow] at e0 e1 e2 e3
  norm_num at e0 e1 e2 e3
  -- Solve the resulting linear system.
  have hv62 : q.coeff 0 = 62 := by linear_combination -e0 / 32
  rw [hv62] at e1
  have hs4 : x₁ + x₂ = 4 := by linear_combination (e1 + 32 * e3) / 94
  have hu : q.coeff 1 = -14 := by linear_combination -e3 + hs4
  have h86 : (a : ℂ) = 86 := by
    linear_combination e2 + hv62 - q.coeff 1 * hs4 - 4 * hu
  show a = 86
  exact_mod_cast h86

end Usa1984P1
