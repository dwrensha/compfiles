/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.NormedSpace.PiLp

import MathPuzzles.Meta.Attributes

/-
Iranian Mathematical Olympiad 1998, Problem 9

Let x,y,z > 1 and 1/x + 1/y + 1/z = 2. Prove that

  √(x + y + z) ≥ √(x - 1) + √(y - 1) + √(z - 1).

-/

namespace Iran1998Q9
open BigOperators

-- This workaround is required to make exponent of `x ^ 2` be interpreted as type ℕ.
-- See https://github.com/leanprover/lean4/issues/2220.
local macro_rules | `($x ^ $y)  => `(HPow.hPow $x $y)

lemma compute_norm (v : EuclideanSpace ℝ (Fin 3)) : ‖v‖ = Real.sqrt (∑i : Fin 3, (v i)^2) := by
  rw[EuclideanSpace.norm_eq v]
  congr; ext
  rw [Real.norm_eq_abs, sq_abs]

@[problem_statement]
theorem iran1998_q9
    (x y z : ℝ)
    (hx : 1 < x)
    (hy : 1 < y)
    (hz : 1 < z)
    (h : 1/x + 1/y + 1/z = 2) :
    Real.sqrt (x - 1) + Real.sqrt (y - 1) + Real.sqrt (z - 1) ≤ Real.sqrt (x + y + z) := by
  -- By cauchy schwarz,
  -- √(x + y + z) √((x-1)/x + (y-1)/y + (z-1)/z) ≥ √(x - 1) + √(y - 1) + √(z - 1).
  --
  -- On the other hand, by hypothesis,
  -- (x-1)/x + (y-1)/y + (z-1)/z = 1.
  --
  -- The desired result follows.

  have hx0 : 0 ≤ x := by positivity
  have hy0 : 0 ≤ y := by positivity
  have hz0 : 0 ≤ z := by positivity

  have hx1 : 0 ≤ x - 1 := by linarith
  have hy1 : 0 ≤ y - 1 := by linarith
  have hz1 : 0 ≤ z - 1 := by linarith

  let v₁ : EuclideanSpace ℝ (Fin 3) := ![Real.sqrt x, Real.sqrt y, Real.sqrt z]
  let v₂ : EuclideanSpace ℝ (Fin 3) :=
      ![Real.sqrt ((x - 1)/x), Real.sqrt ((y-1)/y), Real.sqrt ((z-1)/z)]

  have cauchy_schwarz := abs_real_inner_le_norm v₁ v₂

  have hv₁ : ‖v₁‖ = Real.sqrt (x + y + z) := by
    have hn := compute_norm v₁
    have h1: ((∑ i : Fin 3, ((v₁ i) ^ 2)) : ℝ) = (v₁ 0)^2 + (v₁ 1)^2 + (v₁ 2)^2 := by
      rw[Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one]
      ring_nf
      norm_cast

    rw [h1] at hn
    have hv1 : v₁ 0 = Real.sqrt x := rfl
    have hv2 : v₁ 1 = Real.sqrt y := rfl
    have hv3 : v₁ 2 = Real.sqrt z := rfl
    rw [hv1, hv2, hv3] at hn
    have hxx : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx0
    have hyy : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy0
    have hzz : (Real.sqrt z) ^ 2 = z := Real.sq_sqrt hz0

    rwa [hxx, hyy, hzz] at hn

  have hv₂ : ‖v₂‖ = 1 := by
    have hn := compute_norm v₂
    have h2: ((∑ i : Fin 3, ((v₂ i) ^ 2)) : ℝ) = (v₂ 0)^2 + (v₂ 1)^2 + (v₂ 2)^2 := by
      rw[Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one]
      ring_nf
      norm_cast
    rw [h2] at hn
    have hv1 : v₂ 0 = Real.sqrt ((x-1)/x) := rfl
    have hv2 : v₂ 1 = Real.sqrt ((y-1)/y) := rfl
    have hv3 : v₂ 2 = Real.sqrt ((z-1)/z) := rfl
    rw [hv1, hv2, hv3] at hn
    have hxx : 0 ≤ (x-1)/x := div_nonneg hx1 hx0
    have hxx' : Real.sqrt (((x - 1) / x)) ^2 = (x - 1) / x := Real.sq_sqrt hxx

    have hyy : 0 ≤ (y-1)/y := div_nonneg hy1 hy0
    have hyy' : Real.sqrt (((y - 1) / y)) ^2 = (y - 1) / y := Real.sq_sqrt hyy

    have hzz : 0 ≤ (z-1)/z := div_nonneg hz1 hz0
    have hzz' : Real.sqrt (((z - 1) / z)) ^2 = (z - 1) / z := Real.sq_sqrt hzz

    rw[hxx', hyy', hzz'] at hn
    have hfs: (x - 1) / x + (y - 1) / y + (z - 1) / z = 3 - (1/x + 1/y + 1/z) := by {field_simp; ring}
    rw[hfs, h] at hn
    have ha: (3: ℝ) - 2 = 1 := by norm_num
    rw[hn, ha]
    exact Real.sqrt_one

  rw [hv₁, hv₂, mul_one] at cauchy_schwarz

  have hinner :=
    calc ((inner v₁ v₂): ℝ)
          = ∑ i : Fin 3, v₁ i * v₂ i := rfl
        _ = v₁ 0 * v₂ 0 + v₁ 1 * v₂ 1 + v₁ 2 * v₂ 2 :=
               by rw[Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one]; ring_nf; simp
        _ = Real.sqrt x * Real.sqrt ((x - 1) / x) +
            Real.sqrt y * Real.sqrt ((y - 1) / y) +
            Real.sqrt z * Real.sqrt ((z - 1) / z) := rfl

  have hxxx : x * ((x - 1) / x) = x - 1 := by field_simp; ring
  have hyyy : y * ((y - 1) / y) = y - 1 := by field_simp; ring
  have hzzz : z * ((z - 1) / z) = z - 1 := by field_simp; ring

  rw [←Real.sqrt_mul hx0 ((x - 1) / x),
      ←Real.sqrt_mul hy0 ((y - 1) / y),
      ←Real.sqrt_mul hz0 ((z - 1) / z),
      hxxx, hyyy, hzzz] at hinner

  rw [hinner] at cauchy_schwarz
  exact le_of_abs_le cauchy_schwarz
