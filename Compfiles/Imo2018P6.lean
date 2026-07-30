/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
public import Mathlib.Geometry.Euclidean.Triangle
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 2018, Problem 6

A convex quadrilateral ABCD satisfies AB · CD = BC · DA. Point X lies inside
ABCD so that ∠XAB = ∠XCD and ∠XBC = ∠XDA. Prove that ∠BXA + ∠DXC = 180°.
-/

namespace Imo2018P6

open scoped EuclideanGeometry Real

/-- The Euclidean plane. -/
abbrev E2 := EuclideanSpace ℝ (Fin 2)

/-- Twice the signed area of the parallelogram spanned by two planar vectors
(the 2-dimensional cross product `u₀ * v₁ - u₁ * v₀`). -/
def cross2 (u v : E2) : ℝ := u 0 * v 1 - u 1 * v 0

/-- `ConvexQuadCCW A B C D` asserts that `A B C D` is a convex quadrilateral,
labelled counterclockwise: each consecutive triple of vertices makes a left
turn. -/
def ConvexQuadCCW (A B C D : E2) : Prop :=
  0 < cross2 (B - A) (C - B) ∧ 0 < cross2 (C - B) (D - C) ∧
    0 < cross2 (D - C) (A - D) ∧ 0 < cross2 (A - D) (B - A)

/-- `InsideConvexQuad X A B C D` asserts that `X` lies strictly inside the
convex quadrilateral `A B C D` (it is on the left of every directed edge). -/
def InsideConvexQuad (X A B C D : E2) : Prop :=
  0 < cross2 (B - A) (X - A) ∧ 0 < cross2 (C - B) (X - B) ∧
    0 < cross2 (D - C) (X - C) ∧ 0 < cross2 (A - D) (X - D)

snip begin

lemma cross2_self (u : E2) : cross2 u u = 0 := by
  simp only [cross2]; ring

lemma cross2_zero_left (v : E2) : cross2 0 v = 0 := by
  simp only [cross2, PiLp.zero_apply, zero_mul, sub_zero]

lemma cross2_zero_right (u : E2) : cross2 u 0 = 0 := by
  simp only [cross2, PiLp.zero_apply, mul_zero, sub_zero]

lemma cross2_smul_right (r : ℝ) (u v : E2) : cross2 u (r • v) = r * cross2 u v := by
  simp only [cross2, PiLp.smul_apply, smul_eq_mul]; ring

lemma cross2_eq_zero_of_eq_smul {u v : E2} {r : ℝ} (h : v = r • u) : cross2 u v = 0 := by
  rw [h, cross2_smul_right, cross2_self, mul_zero]

/-- If the cross product of two planar vectors is nonzero, then the
(unoriented) angle between them lies strictly between `0` and `π`. -/
lemma angle_pos_and_lt_pi_of_cross2_ne {u v : E2} (h : cross2 u v ≠ 0) :
    0 < InnerProductGeometry.angle u v ∧ InnerProductGeometry.angle u v < π := by
  have hu : u ≠ 0 := by
    rintro rfl
    exact h (cross2_zero_left v)
  have hv : v ≠ 0 := by
    rintro rfl
    exact h (cross2_zero_right u)
  refine ⟨lt_of_le_of_ne (InnerProductGeometry.angle_nonneg u v) ?_,
    lt_of_le_of_ne (InnerProductGeometry.angle_le_pi u v) ?_⟩
  · symm
    rw [Ne, InnerProductGeometry.angle_eq_zero_iff]
    rintro ⟨_, r, _, hvr⟩
    exact h (cross2_eq_zero_of_eq_smul hvr)
  · rw [Ne, InnerProductGeometry.angle_eq_pi_iff]
    rintro ⟨_, r, _, hvr⟩
    exact h (cross2_eq_zero_of_eq_smul hvr)

/-- Cramer's rule in the plane: if `cross2 u v < 0` and `w` lies in the same
wedge (both relevant cross products negative), then `w` is a nonnegative
combination of `u` and `v`, so the angle at the apex splits. -/
lemma angle_split_of_cross2 {u v w : E2}
    (huv : cross2 u v < 0) (huw : cross2 u w < 0) (hwv : cross2 w v < 0) :
    InnerProductGeometry.angle u v =
      InnerProductGeometry.angle u w + InnerProductGeometry.angle w v := by
  have hw : w ≠ 0 := by
    rintro rfl
    rw [cross2_zero_right] at huw
    exact lt_irrefl _ huw
  rw [InnerProductGeometry.angle_eq_angle_add_add_angle_add_of_mem_span hw]
  rw [Submodule.mem_span_pair]
  have hden : cross2 u v ≠ 0 := ne_of_lt huv
  refine ⟨⟨cross2 w v / cross2 u v, le_of_lt (div_pos_of_neg_of_neg hwv huv)⟩,
    ⟨cross2 u w / cross2 u v, le_of_lt (div_pos_of_neg_of_neg huw huv)⟩, ?_⟩
  show (cross2 w v / cross2 u v : ℝ) • u + (cross2 u w / cross2 u v : ℝ) • v = w
  apply PiLp.ext
  rw [Fin.forall_fin_two]
  constructor <;>
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] <;>
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hden] <;>
    simp only [cross2] <;>
    ring

/-- A convenient packaged form of `angle_pos_and_lt_pi_of_cross2_ne` with a
negative cross product hypothesis. -/
lemma angle_mem_Ioo_of_cross2_neg {u v : E2} (h : cross2 u v < 0) :
    0 < InnerProductGeometry.angle u v ∧ InnerProductGeometry.angle u v < π :=
  angle_pos_and_lt_pi_of_cross2_ne (ne_of_lt h)

/-- Product-to-sum: twice a product of sines is a difference of cosines. -/
lemma two_mul_sin_mul_sin (x y : ℝ) :
    2 * Real.sin x * Real.sin y = Real.cos (x - y) - Real.cos (x + y) := by
  have h := Real.cos_sub_cos (x - y) (x + y)
  rw [show x - y + (x + y) = 2 * x by ring,
    show 2 * x / 2 = x by ring,
    show x - y - (x + y) = -2 * y by ring,
    show -2 * y / 2 = -y by ring, Real.sin_neg] at h
  linarith [h]

/-- An auxiliary trigonometric identity used in the squeeze argument below. -/
lemma sin_mul_sin_add_sin_mul_sin (a u bp : ℝ) :
    Real.sin bp * Real.sin (2 * a + u) + Real.sin (2 * a + 2 * u + bp) * Real.sin u
      = Real.sin (2 * a + 2 * u) * Real.sin (u + bp) := by
  have h1 := two_mul_sin_mul_sin bp (2 * a + u)
  have h2 := two_mul_sin_mul_sin (2 * a + 2 * u + bp) u
  have h3 := two_mul_sin_mul_sin (2 * a + 2 * u) (u + bp)
  rw [show bp - (2 * a + u) = -((2 * a + 2 * u) - (u + bp)) by ring, Real.cos_neg] at h1
  rw [show bp + (2 * a + u) = (2 * a + 2 * u + bp) - u by ring] at h1
  rw [show (2 * a + 2 * u) + (u + bp) = (2 * a + 2 * u + bp) + u by ring] at h3
  linear_combination h1 / 2 + h2 / 2 - h3 / 2

/-- The trigonometric heart of the problem.  Suppose that angles
`a, bp` (each in `(0, π)`), a positive `s` with `s + 2 * bp < 2π` and a real
`r` satisfy `cos s < cos r` and the relation

  `sin bp * ((cos r - cos (2a+s))/2 - sin²a) = - sin (2a+s+bp) * (cos r - cos s)/2`,

which is what remains of the hypotheses `AB·CD = BC·DA`, `∠XAB = ∠XCD` and
`∠XBC = ∠XDA` after applying the law of sines in the four triangles
`XAB, XBC, XCD, XDA` and eliminating the four distances `XA, XB, XC, XD`.
Here `2a+s` plays the role of `∠XAB + ∠XBA + ∠XDC + ∠XCD`... actually of
`2∠XAB + ∠XBA + ∠XDC`, and the conclusion `2a+s = π` is equivalent to
`∠BXA + ∠DXC = π`.  The proof is a squeeze: writing `D` and `N` for the two
sides of the relation solved for `cos r`, the trivial bounds
`cos s < cos r ≤ 1` force `D = 0`, which gives `2a+s = π`. -/
theorem trig_core {a bp s r : ℝ}
    (ha0 : 0 < a) (hap : a < π)
    (hbp0 : 0 < bp) (hbpp : bp < π)
    (hs0 : 0 < s) (_hs2bp : s + 2 * bp < 2 * π)
    (hP2bp : 2 * a + s + 2 * bp < 2 * π)
    (hcos : Real.cos s < Real.cos r)
    (hstar : Real.sin bp * ((Real.cos r - Real.cos (2 * a + s)) / 2 - (Real.sin a) ^ 2)
      = -Real.sin (2 * a + s + bp) * (Real.cos r - Real.cos s) / 2) :
    2 * a + s = π := by
  have hpi : 0 < π := Real.pi_pos
  have hP0 : 0 < 2 * a + s := by linarith
  have hP2 : 2 * a + s < 2 * π := by linarith
  have hsa : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha0 hap
  have hsb : 0 < Real.sin bp := Real.sin_pos_of_pos_of_lt_pi hbp0 hbpp
  have hss : 0 < Real.sin (s / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith
  have hsubp : 0 < Real.sin (s / 2 + bp) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith
  -- The two key identities for `D - N` and `N - D * cos s`, where
  -- `D = sin bp + sin (2a+s+bp)` and `N = sin bp (cos (2a+s) + 2 sin²a) + sin (2a+s+bp) cos s`.
  have hid1 : (Real.sin bp + Real.sin (2 * a + s + bp))
      - (Real.sin bp * (Real.cos (2 * a + s) + 2 * (Real.sin a) ^ 2)
        + Real.sin (2 * a + s + bp) * Real.cos s)
      = 2 * Real.sin (s / 2) * Real.sin (2 * a + s) * Real.sin (s / 2 + bp) := by
    have hc1 : Real.cos (2 * a) = 1 - 2 * (Real.sin a) ^ 2 := by
      rw [Real.cos_two_mul, Real.sin_sq]; ring
    have hc2 : Real.cos (2 * a) - Real.cos (2 * a + s)
        = 2 * Real.sin (s / 2) * Real.sin (2 * a + s / 2) := by
      rw [Real.cos_sub_cos]
      rw [show (2 * a + (2 * a + s)) / 2 = 2 * a + s / 2 by ring,
        show (2 * a - (2 * a + s)) / 2 = -(s / 2) by ring, Real.sin_neg]
      ring
    have hc3 : 1 - Real.cos s = 2 * (Real.sin (s / 2)) ^ 2 := by
      have h : Real.cos s = 1 - 2 * (Real.sin (s / 2)) ^ 2 := by
        rw [show s = 2 * (s / 2) by ring, Real.cos_two_mul, Real.sin_sq]; ring
      linarith [h]
    have hc4 := sin_mul_sin_add_sin_mul_sin a (s / 2) bp
    rw [show 2 * a + 2 * (s / 2) + bp = 2 * a + s + bp by ring,
      show 2 * a + 2 * (s / 2) = 2 * a + s by ring] at hc4
    linear_combination -Real.sin bp * hc1 + Real.sin bp * hc2
      + Real.sin (2 * a + s + bp) * hc3 + 2 * Real.sin (s / 2) * hc4
  have hid2 : (Real.sin bp * (Real.cos (2 * a + s) + 2 * (Real.sin a) ^ 2)
      + Real.sin (2 * a + s + bp) * Real.cos s)
      - (Real.sin bp + Real.sin (2 * a + s + bp)) * Real.cos s
      = -4 * Real.sin a * Real.sin bp * Real.cos ((2 * a + s) / 2) * Real.sin (s / 2) := by
    have hc1 : Real.cos (2 * a + s) - Real.cos s = -2 * Real.sin (a + s) * Real.sin a := by
      rw [Real.cos_sub_cos]
      rw [show (2 * a + s + s) / 2 = a + s by ring,
        show (2 * a + s - s) / 2 = a by ring]
    have hc2 : Real.sin a - Real.sin (a + s)
        = -2 * Real.sin (s / 2) * Real.cos ((2 * a + s) / 2) := by
      rw [Real.sin_sub_sin]
      rw [show (a - (a + s)) / 2 = -(s / 2) by ring,
        show (a + (a + s)) / 2 = (2 * a + s) / 2 by ring, Real.sin_neg]
      ring
    linear_combination Real.sin bp * hc1 + 2 * Real.sin a * Real.sin bp * hc2
  -- The relation `hstar` solved for `cos r`: `cos r * D = N`.
  have hEq : Real.cos r * (Real.sin bp + Real.sin (2 * a + s + bp))
      = Real.sin bp * (Real.cos (2 * a + s) + 2 * (Real.sin a) ^ 2)
        + Real.sin (2 * a + s + bp) * Real.cos s := by
    linear_combination 2 * hstar
  have hcosr1 : Real.cos r ≤ 1 := Real.cos_le_one r
  rcases lt_trichotomy (Real.sin bp + Real.sin (2 * a + s + bp)) 0 with hDneg | hDzero | hDpos
  · -- If `D < 0`, then `cos r ≤ 1` gives `π ≤ 2a+s` and `cos s < cos r` gives
    -- `2a+s < π`: contradiction.
    have h1 : 2 * Real.sin (s / 2) * Real.sin (2 * a + s) * Real.sin (s / 2 + bp) ≤ 0 := by
      rw [← hid1]
      have hle : Real.sin bp + Real.sin (2 * a + s + bp)
          ≤ Real.sin bp * (Real.cos (2 * a + s) + 2 * (Real.sin a) ^ 2)
            + Real.sin (2 * a + s + bp) * Real.cos s := by
        have h3 := mul_le_mul_of_nonpos_right hcosr1 (le_of_lt hDneg)
        rw [one_mul, hEq] at h3
        exact h3
      linarith [hle]
    have hsinP : Real.sin (2 * a + s) ≤ 0 := by
      have h2pos : 0 < 2 * Real.sin (s / 2) * Real.sin (s / 2 + bp) :=
        mul_pos (mul_pos (by norm_num) hss) hsubp
      have h1' : 2 * Real.sin (s / 2) * Real.sin (s / 2 + bp) * Real.sin (2 * a + s) ≤ 0 := by
        linarith [h1]
      exact nonpos_of_mul_nonpos_right h1' h2pos
    have hPge : π ≤ 2 * a + s := by
      by_contra hlt
      push Not at hlt
      have hpos := Real.sin_pos_of_pos_of_lt_pi hP0 hlt
      linarith
    have h2 : -4 * Real.sin a * Real.sin bp * Real.cos ((2 * a + s) / 2)
        * Real.sin (s / 2) < 0 := by
      have h3 := mul_lt_mul_of_neg_right hcos hDneg
      rw [hEq] at h3
      have h4 : (Real.sin bp * (Real.cos (2 * a + s) + 2 * (Real.sin a) ^ 2)
          + Real.sin (2 * a + s + bp) * Real.cos s)
          - (Real.sin bp + Real.sin (2 * a + s + bp)) * Real.cos s < 0 := by
        linarith [h3]
      rw [hid2] at h4
      exact h4
    have hcospos : 0 < Real.cos ((2 * a + s) / 2) := by
      have h4 : (0:ℝ) < 4 * Real.sin a * Real.sin bp * Real.sin (s / 2) :=
        mul_pos (mul_pos (mul_pos (by norm_num) hsa) hsb) hss
      by_contra hcos0
      push Not at hcos0
      have hnn : (0:ℝ) ≤ 4 * Real.sin a * Real.sin bp * Real.sin (s / 2)
          * (-Real.cos ((2 * a + s) / 2)) := mul_nonneg h4.le (by linarith [hcos0])
      linarith [h2, hnn]
    have hPlt : 2 * a + s < π := by
      by_contra hge
      push Not at hge
      have hcosle : Real.cos ((2 * a + s) / 2) ≤ 0 := by
        apply Real.cos_nonpos_of_pi_div_two_le_of_le <;> linarith
      linarith
    linarith
  · -- If `D = 0`, then `sin (2a+s+bp) = -sin bp = sin (-bp)`, which with the
    -- bounds forces `2a+s = π`.
    have hsin : Real.sin (2 * a + s + bp) = Real.sin (-bp) := by
      have h2 : Real.sin (2 * a + s + bp) = -Real.sin bp := by linarith [hDzero]
      rw [h2, Real.sin_neg]
    rw [Real.sin_eq_sin_iff] at hsin
    rcases hsin with ⟨k, hk | hk⟩
    · -- `-bp = 2πk + (2a+s+bp)`: then `2a+s+2bp = -2πk`, impossible in `(0, 2π)`.
      exfalso
      have heq : 2 * a + s + 2 * bp = -(2 * π * k) := by linarith [hk]
      have hgt : 0 < 2 * a + s + 2 * bp := by linarith
      rw [heq] at hgt hP2bp
      have h1 : (-1:ℝ) < k := by
        by_contra hle
        push Not at hle
        have hle' := mul_le_mul_of_nonneg_left hle (by positivity : (0:ℝ) ≤ 2 * π)
        linarith [hle', hP2bp, Real.pi_pos]
      have h2 : (k:ℝ) < 0 := by
        by_contra hge
        push Not at hge
        have hge' := mul_nonneg (by positivity : (0:ℝ) ≤ 2 * π) hge
        linarith [hge', hgt, Real.pi_pos]
      have h3 : -1 < k := by exact_mod_cast h1
      have h4 : k < 0 := by exact_mod_cast h2
      omega
    · -- `-bp = (2k+1)π - (2a+s+bp)`: then `2a+s = π + 2πk = π`.
      have heq : 2 * a + s = π + 2 * π * k := by linarith [hk]
      have hk0 : k = 0 := by
        have habs : |2 * a + s - π| < π := by
          rw [abs_lt]
          constructor <;> linarith
        have heq2 : 2 * a + s - π = 2 * π * k := by linarith [heq]
        rw [heq2] at habs
        have hk1 : |(k : ℝ)| < 1 := by
          have hrew : |(2:ℝ) * π * k| = 2 * π * |(k : ℝ)| := by
            rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * π)]
          rw [hrew] at habs
          nlinarith [Real.pi_pos, habs]
        have h1 : (-1:ℝ) < k := by
          have := neg_lt_of_abs_lt hk1
          linarith
        have h2 : (k:ℝ) < 1 := lt_of_abs_lt hk1
        have h3 : -1 < k := by exact_mod_cast h1
        have h4 : k < 1 := by exact_mod_cast h2
        omega
      subst hk0
      simp at heq
      exact heq
  · -- If `D > 0`, then `cos r ≤ 1` gives `2a+s ≤ π` and `cos s < cos r` gives
    -- `π < 2a+s`: contradiction.
    have h1 : 0 ≤ 2 * Real.sin (s / 2) * Real.sin (2 * a + s) * Real.sin (s / 2 + bp) := by
      rw [← hid1]
      have hle : Real.sin bp * (Real.cos (2 * a + s) + 2 * (Real.sin a) ^ 2)
          + Real.sin (2 * a + s + bp) * Real.cos s
          ≤ Real.sin bp + Real.sin (2 * a + s + bp) := by
        have h3 := mul_le_mul_of_nonneg_right hcosr1 (le_of_lt hDpos)
        rw [hEq, one_mul] at h3
        exact h3
      linarith [hle]
    have hsinP : 0 ≤ Real.sin (2 * a + s) := by
      have h2pos : 0 < 2 * Real.sin (s / 2) * Real.sin (s / 2 + bp) :=
        mul_pos (mul_pos (by norm_num) hss) hsubp
      have h1' : 0 ≤ 2 * Real.sin (s / 2) * Real.sin (s / 2 + bp) * Real.sin (2 * a + s) := by
        linarith [h1]
      exact nonneg_of_mul_nonneg_right h1' h2pos
    have hPle : 2 * a + s ≤ π := by
      by_contra hgt
      push Not at hgt
      have hsinneg : Real.sin (2 * a + s) < 0 := by
        rw [show 2 * a + s = (2 * a + s - π) + π by ring, Real.sin_add_pi]
        have hpos : 0 < Real.sin (2 * a + s - π) := by
          apply Real.sin_pos_of_pos_of_lt_pi <;> linarith
        linarith
      linarith
    have h2 : 0 < -4 * Real.sin a * Real.sin bp * Real.cos ((2 * a + s) / 2)
        * Real.sin (s / 2) := by
      have h3 := mul_lt_mul_of_pos_right hcos hDpos
      rw [hEq] at h3
      have h4 : 0 < (Real.sin bp * (Real.cos (2 * a + s) + 2 * (Real.sin a) ^ 2)
          + Real.sin (2 * a + s + bp) * Real.cos s)
          - (Real.sin bp + Real.sin (2 * a + s + bp)) * Real.cos s := by
        linarith [h3]
      rw [hid2] at h4
      exact h4
    have hcosneg : Real.cos ((2 * a + s) / 2) < 0 := by
      have h4 : (0:ℝ) < 4 * Real.sin a * Real.sin bp * Real.sin (s / 2) :=
        mul_pos (mul_pos (mul_pos (by norm_num) hsa) hsb) hss
      by_contra hcos0
      push Not at hcos0
      have hnn : (0:ℝ) ≤ 4 * Real.sin a * Real.sin bp * Real.sin (s / 2)
          * Real.cos ((2 * a + s) / 2) := mul_nonneg h4.le hcos0
      linarith [h2, hnn]
    have hPgt : π < 2 * a + s := by
      by_contra hle
      push Not at hle
      have hmem : (2 * a + s) / 2 ∈ Set.Icc (-(π / 2)) (π / 2) := by
        constructor <;> linarith
      have := Real.cos_nonneg_of_mem_Icc hmem
      linarith
    linarith

snip end

problem imo2018_p6
    (A B C D X : E2)
    (hconv : ConvexQuadCCW A B C D)
    (hXin : InsideConvexQuad X A B C D)
    (hside : dist A B * dist C D = dist B C * dist D A)
    (h1 : ∠ X A B = ∠ X C D)
    (h2 : ∠ X B C = ∠ X D A) :
    ∠ B X A + ∠ D X C = π := by
  obtain ⟨hC1, hC2, hC3, hC4⟩ := hconv
  obtain ⟨hX1, hX2, hX3, hX4⟩ := hXin
  -- Distinctness of points, read off from the nonzero cross products.
  have hBA : B ≠ A := by
    rintro rfl
    rw [sub_self, cross2_zero_left] at hX1
    exact lt_irrefl _ hX1
  have hXA : X ≠ A := by
    rintro rfl
    rw [sub_self, cross2_zero_right] at hX1
    exact lt_irrefl _ hX1
  have hBX : B ≠ X := by
    rintro rfl
    rw [cross2_self] at hX1
    exact lt_irrefl _ hX1
  have hCB : C ≠ B := by
    rintro rfl
    rw [sub_self, cross2_zero_left] at hX2
    exact lt_irrefl _ hX2
  have hXB : X ≠ B := by
    rintro rfl
    rw [sub_self, cross2_zero_right] at hX2
    exact lt_irrefl _ hX2
  have hCX : C ≠ X := by
    rintro rfl
    rw [cross2_self] at hX2
    exact lt_irrefl _ hX2
  have hDC : D ≠ C := by
    rintro rfl
    rw [sub_self, cross2_zero_left] at hX3
    exact lt_irrefl _ hX3
  have hXC : X ≠ C := by
    rintro rfl
    rw [sub_self, cross2_zero_right] at hX3
    exact lt_irrefl _ hX3
  have hDX : D ≠ X := by
    rintro rfl
    rw [cross2_self] at hX3
    exact lt_irrefl _ hX3
  have hAD : A ≠ D := by
    rintro rfl
    rw [sub_self, cross2_zero_left] at hX4
    exact lt_irrefl _ hX4
  have hXD : X ≠ D := by
    rintro rfl
    rw [sub_self, cross2_zero_right] at hX4
    exact lt_irrefl _ hX4
  have hCA : C ≠ A := by
    intro h
    rw [h] at hC1
    have e : cross2 (B - A) (A - B) = 0 := by
      simp only [cross2, PiLp.sub_apply]; ring
    rw [e] at hC1
    exact lt_irrefl _ hC1
  -- The sixteen sign facts needed for the six angle splits.
  have sgB1 : cross2 (A - B) (C - B) < 0 := by
    have e : cross2 (A - B) (C - B) = -cross2 (B - A) (C - B) := by
      simp only [cross2, PiLp.sub_apply]; ring
    linarith [e, hC1]
  have sgB2 : cross2 (A - B) (X - B) < 0 := by
    have e : cross2 (A - B) (X - B) = -cross2 (B - A) (X - A) := by
      simp only [cross2, PiLp.sub_apply]; ring
    linarith [e, hX1]
  have sgB3 : cross2 (X - B) (C - B) < 0 := by
    have e : cross2 (X - B) (C - B) = -cross2 (C - B) (X - B) := by
      simp only [cross2, PiLp.sub_apply]; ring
    linarith [e, hX2]
  have sgD1 : cross2 (C - D) (A - D) < 0 := by
    have e : cross2 (C - D) (A - D) = -cross2 (D - C) (A - D) := by
      simp only [cross2, PiLp.sub_apply]; ring
    linarith [e, hC3]
  have sgD2 : cross2 (C - D) (X - D) < 0 := by
    have e : cross2 (C - D) (X - D) = -cross2 (D - C) (X - C) := by
      simp only [cross2, PiLp.sub_apply]; ring
    linarith [e, hX3]
  have sgD3 : cross2 (X - D) (A - D) < 0 := by
    have e : cross2 (X - D) (A - D) = -cross2 (A - D) (X - D) := by
      simp only [cross2, PiLp.sub_apply]; ring
    linarith [e, hX4]
  have sgA1 : cross2 (D - A) (B - A) < 0 := by
    have e : cross2 (D - A) (B - A) = -cross2 (A - D) (B - A) := by
      simp only [cross2, PiLp.sub_apply]; ring
    linarith [e, hC4]
  have sgA2 : cross2 (D - A) (X - A) < 0 := by
    have e : cross2 (D - A) (X - A) = -cross2 (A - D) (X - D) := by
      simp only [cross2, PiLp.sub_apply]; ring
    linarith [e, hX4]
  have sgA3 : cross2 (X - A) (B - A) < 0 := by
    have e : cross2 (X - A) (B - A) = -cross2 (B - A) (X - A) := by
      simp only [cross2, PiLp.sub_apply]; ring
    linarith [e, hX1]
  have sgC1 : cross2 (B - C) (D - C) < 0 := by
    have e : cross2 (B - C) (D - C) = -cross2 (C - B) (D - C) := by
      simp only [cross2, PiLp.sub_apply]; ring
    linarith [e, hC2]
  have sgC2 : cross2 (B - C) (X - C) < 0 := by
    have e : cross2 (B - C) (X - C) = -cross2 (C - B) (X - B) := by
      simp only [cross2, PiLp.sub_apply]; ring
    linarith [e, hX2]
  have sgC3 : cross2 (X - C) (D - C) < 0 := by
    have e : cross2 (X - C) (D - C) = -cross2 (D - C) (X - C) := by
      simp only [cross2, PiLp.sub_apply]; ring
    linarith [e, hX3]
  have sgDA2 : cross2 (D - A) (C - A) < 0 := by
    have e : cross2 (D - A) (C - A) = -cross2 (D - C) (A - D) := by
      simp only [cross2, PiLp.sub_apply]; ring
    linarith [e, hC3]
  have sgDA3 : cross2 (C - A) (B - A) < 0 := by
    have e : cross2 (C - A) (B - A) = -cross2 (B - A) (C - B) := by
      simp only [cross2, PiLp.sub_apply]; ring
    linarith [e, hC1]
  have sgDC2 : cross2 (B - C) (A - C) < 0 := by
    have e : cross2 (B - C) (A - C) = -cross2 (B - A) (C - B) := by
      simp only [cross2, PiLp.sub_apply]; ring
    linarith [e, hC1]
  have sgDC3 : cross2 (A - C) (D - C) < 0 := by
    have e : cross2 (A - C) (D - C) = -cross2 (D - C) (A - D) := by
      simp only [cross2, PiLp.sub_apply]; ring
    linarith [e, hC3]
  -- The six angle splits: four at the vertices through `X`, two along the
  -- diagonal `A C`.
  have splitA : ∠ D A B = ∠ D A X + ∠ X A B := angle_split_of_cross2 sgA1 sgA2 sgA3
  have splitB : ∠ A B C = ∠ A B X + ∠ X B C := angle_split_of_cross2 sgB1 sgB2 sgB3
  have splitC : ∠ B C D = ∠ B C X + ∠ X C D := angle_split_of_cross2 sgC1 sgC2 sgC3
  have splitD : ∠ C D A = ∠ C D X + ∠ X D A := angle_split_of_cross2 sgD1 sgD2 sgD3
  have splitDA : ∠ D A B = ∠ D A C + ∠ C A B := angle_split_of_cross2 sgA1 sgDA2 sgDA3
  have splitDC : ∠ B C D = ∠ B C A + ∠ A C D := angle_split_of_cross2 sgC1 sgDC2 sgDC3
  -- The six triangle angle sums.
  have triXAB : ∠ X A B + ∠ A B X + ∠ B X A = π :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi B hXA.symm
  have triXBC : ∠ X B C + ∠ B C X + ∠ C X B = π :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi C hXB.symm
  have triXCD : ∠ X C D + ∠ C D X + ∠ D X C = π :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi D hXC.symm
  have triXDA : ∠ X D A + ∠ D A X + ∠ A X D = π :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi A hXD.symm
  have triABC : ∠ A B C + ∠ B C A + ∠ C A B = π :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi C hBA
  have triACD : ∠ A C D + ∠ C D A + ∠ D A C = π :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi D hCA
  -- The law of sines in the four triangles around `X`, with all distances
  -- normalized to the form `dist X _`.
  have hL1 := EuclideanGeometry.law_sin A B X
  have hL2 := EuclideanGeometry.law_sin B C X
  have hL3 := EuclideanGeometry.law_sin C D X
  have hL4 := EuclideanGeometry.law_sin D A X
  have hAB := EuclideanGeometry.law_sin X A B
  have hBC := EuclideanGeometry.law_sin X B C
  have hCD := EuclideanGeometry.law_sin X C D
  have hDA := EuclideanGeometry.law_sin X D A
  rw [dist_comm B X] at hL1 hAB
  rw [dist_comm C X] at hL2 hBC
  rw [dist_comm D X] at hL3 hCD
  rw [dist_comm A X] at hL4 hDA
  -- Abbreviations for the six angles.
  set a := ∠ X A B with ha
  set ap := ∠ D A X with hap
  set b := ∠ A B X with hb
  set bp := ∠ X B C with hbp
  set g := ∠ B C X with hg
  set d := ∠ C D X with hd
  rw [← h1] at hL3 hCD triXCD splitC
  rw [← h2] at hL4 hDA triXDA splitD
  -- Sines of the angles at `X` in terms of the other two angles.
  have hsinBXA : Real.sin (∠ B X A) = Real.sin (a + b) := by
    have h : ∠ B X A = π - (a + b) := by linarith [triXAB]
    rw [h, Real.sin_pi_sub]
  have hsinCXB : Real.sin (∠ C X B) = Real.sin (bp + g) := by
    have h : ∠ C X B = π - (bp + g) := by linarith [triXBC]
    rw [h, Real.sin_pi_sub]
  have hsinDXC : Real.sin (∠ D X C) = Real.sin (a + d) := by
    have h : ∠ D X C = π - (a + d) := by linarith [triXCD]
    rw [h, Real.sin_pi_sub]
  have hsinAXD : Real.sin (∠ A X D) = Real.sin (ap + bp) := by
    have h : ∠ A X D = π - (ap + bp) := by linarith [triXDA]
    rw [h, Real.sin_pi_sub]
  rw [hsinBXA] at hAB
  rw [hsinCXB] at hBC
  rw [hsinDXC] at hCD
  rw [hsinAXD] at hDA
  -- The total angle sum: `2a + 2bp + ap + b + g + d = 2π`.
  have h4sum : 2 * a + 2 * bp + ap + b + g + d = 2 * π := by
    linarith [splitA, splitB, splitC, splitD, splitDA, splitDC, triABC, triACD]
  -- Positivity facts.
  have haI := angle_mem_Ioo_of_cross2_neg sgA3
  have hapI := angle_mem_Ioo_of_cross2_neg sgA2
  have hbI := angle_mem_Ioo_of_cross2_neg sgB2
  have hbpI := angle_mem_Ioo_of_cross2_neg sgB3
  have hgI := angle_mem_Ioo_of_cross2_neg sgC2
  have hdI := angle_mem_Ioo_of_cross2_neg sgD2
  have hsa : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi haI.1 haI.2
  have hsb : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hbI.1 hbI.2
  have hsbp : 0 < Real.sin bp := Real.sin_pos_of_pos_of_lt_pi hbpI.1 hbpI.2
  have hsg : 0 < Real.sin g := Real.sin_pos_of_pos_of_lt_pi hgI.1 hgI.2
  have hsd : 0 < Real.sin d := Real.sin_pos_of_pos_of_lt_pi hdI.1 hdI.2
  have hp : 0 < dist X A := dist_pos.mpr hXA
  have hq : 0 < dist X B := dist_pos.mpr hXB
  have hr : 0 < dist X C := dist_pos.mpr hXC
  have hs : 0 < dist X D := dist_pos.mpr hXD
  -- The trigonometric Ceva relation `♦`.
  have hceva : (Real.sin a)^2 * (Real.sin bp)^2
      = Real.sin ap * Real.sin b * Real.sin g * Real.sin d := by
    have hpqrs : dist X A * dist X B * dist X C * dist X D ≠ 0 := by positivity
    apply mul_right_cancel₀ hpqrs
    have e : (Real.sin a)^2 * (Real.sin bp)^2 * (dist X A * dist X B * dist X C * dist X D)
        = (Real.sin a * dist X A) * (Real.sin a * dist X C)
          * (Real.sin bp * dist X B) * (Real.sin bp * dist X D) := by ring
    rw [e, ← hL1, ← hL3, ← hL2, ← hL4]; ring
  -- The side condition `AB·CD = BC·DA` in trigonometric form (`KEY`).
  have hKEY : Real.sin g * Real.sin ap * Real.sin (a + b) * Real.sin (a + d)
      = (Real.sin a)^2 * Real.sin (bp + g) * Real.sin (ap + bp) := by
    have hpqrs : dist X A * dist X B * dist X C * dist X D ≠ 0 := by positivity
    apply mul_right_cancel₀ hpqrs
    have eL : Real.sin g * Real.sin ap * Real.sin (a + b) * Real.sin (a + d)
        * (dist X A * dist X B * dist X C * dist X D)
        = (Real.sin g * dist X C) * (Real.sin ap * dist X A)
          * (Real.sin (a + b) * dist X B) * (Real.sin (a + d) * dist X D) := by ring
    have eR : (Real.sin a)^2 * Real.sin (bp + g) * Real.sin (ap + bp)
        * (dist X A * dist X B * dist X C * dist X D)
        = (Real.sin a)^2 * (Real.sin (bp + g) * dist X C)
          * (Real.sin (ap + bp) * dist X A) * (dist X B * dist X D) := by ring
    rw [eL, eR, hL2, hL4, ← hAB, ← hCD, ← hBC, ← hDA]
    linear_combination ((Real.sin bp)^2 * (Real.sin a)^2 * (dist X B * dist X D)) * hside
  -- `★`: the relation `hstar1`, obtained from `KEY` and `♦`.
  have hstar1 : (Real.sin bp)^2 * Real.sin (a + b) * Real.sin (a + d)
      = Real.sin b * Real.sin d * Real.sin (bp + g) * Real.sin (ap + bp) := by
    have hsag : 0 < Real.sin ap * Real.sin g := mul_pos
      (Real.sin_pos_of_pos_of_lt_pi hapI.1 hapI.2) hsg
    apply mul_left_cancel₀ (ne_of_gt hsag)
    linear_combination ((Real.sin bp)^2) * hKEY
      + (Real.sin (bp + g) * Real.sin (ap + bp)) * hceva
  -- Subtracting `♦` kills the mixed term and leaves the core relation.
  have hdiff : (Real.sin bp)^2 * (Real.sin (a + b) * Real.sin (a + d) - (Real.sin a)^2)
      = Real.sin b * Real.sin d
        * (Real.sin (bp + g) * Real.sin (ap + bp) - Real.sin ap * Real.sin g) := by
    linear_combination hstar1 - hceva
  have hbrk : Real.sin (bp + g) * Real.sin (ap + bp) - Real.sin ap * Real.sin g
      = Real.sin (ap + g + bp) * Real.sin bp := by
    have t1 := two_mul_sin_mul_sin (bp + g) (ap + bp)
    have t2 := two_mul_sin_mul_sin ap g
    have t3 := two_mul_sin_mul_sin (ap + g + bp) bp
    rw [show (bp + g) - (ap + bp) = g - ap by ring, show g - ap = -(ap - g) by ring,
      Real.cos_neg, show (bp + g) + (ap + bp) = ap + g + 2 * bp by ring] at t1
    rw [show (ap + g + bp) - bp = ap + g by ring,
      show (ap + g + bp) + bp = ap + g + 2 * bp by ring] at t3
    linear_combination t1 / 2 - t2 / 2 - t3 / 2
  have hsinM : Real.sin (ap + g + bp) = -Real.sin (2 * a + (b + d) + bp) := by
    have hMeq : ap + g + bp = 2 * π - (2 * a + (b + d) + bp) := by linarith [h4sum]
    rw [hMeq, Real.sin_two_pi_sub]
  have hstar' : Real.sin bp * (Real.sin (a + b) * Real.sin (a + d) - (Real.sin a)^2)
      = -Real.sin (2 * a + (b + d) + bp) * (Real.sin b * Real.sin d) := by
    apply mul_left_cancel₀ (ne_of_gt hsbp)
    have e : Real.sin bp * (Real.sin bp
        * (Real.sin (a + b) * Real.sin (a + d) - (Real.sin a)^2))
        = (Real.sin bp)^2 * (Real.sin (a + b) * Real.sin (a + d) - (Real.sin a)^2) := by
      ring
    rw [e, hdiff, hbrk, hsinM]; ring
  have hstar : Real.sin bp * ((Real.cos (b - d) - Real.cos (2 * a + (b + d))) / 2
      - (Real.sin a)^2)
      = -Real.sin (2 * a + (b + d) + bp) * (Real.cos (b - d) - Real.cos (b + d)) / 2 := by
    have t1 := two_mul_sin_mul_sin (a + b) (a + d)
    rw [show (a + b) - (a + d) = b - d by ring,
      show (a + b) + (a + d) = 2 * a + (b + d) by ring] at t1
    have t2 := two_mul_sin_mul_sin b d
    linear_combination hstar' - (Real.sin bp / 2) * t1
      - (Real.sin (2 * a + (b + d) + bp) / 2) * t2
  -- Ranges for the squeeze.
  have hb_bp : b + bp < π := by
    have hI2 : ∠ A B C < π := (angle_mem_Ioo_of_cross2_neg sgB1).2
    linarith [splitB, hI2]
  have hd_bp : d + bp < π := by
    have hI2 : ∠ C D A < π := (angle_mem_Ioo_of_cross2_neg sgD1).2
    linarith [splitD, hI2]
  have hb0 : 0 < b := hbI.1
  have hd0 : 0 < d := hdI.1
  have hap0 : 0 < ap := hapI.1
  have hg0 : 0 < g := hgI.1
  have hs0 : 0 < b + d := by linarith [hb0, hd0]
  have hs2bp : b + d + 2 * bp < 2 * π := by linarith [hb_bp, hd_bp]
  have hP2bp : 2 * a + (b + d) + 2 * bp < 2 * π := by
    linarith [h4sum, hap0, hg0]
  have hcos : Real.cos (b + d) < Real.cos (b - d) := by
    have t2 := two_mul_sin_mul_sin b d
    have hpos : 0 < Real.sin b * Real.sin d := mul_pos hsb hsd
    linarith [t2, hpos]
  -- The trigonometric core: `2a + (b + d) = π`.
  have hscore : 2 * a + (b + d) = π :=
    trig_core haI.1 haI.2 hbpI.1 hbpI.2 hs0 hs2bp hP2bp hcos hstar
  linarith [hscore, triXAB, triXCD]

end Imo2018P6

