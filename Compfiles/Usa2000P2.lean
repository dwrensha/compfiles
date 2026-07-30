/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.LinearCombination.Lemmas
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 2000, Problem 2

Let S be the set of all triangles ABC for which

    5(1/AP + 1/BQ + 1/CR) − 3/min{AP, BQ, CR} = 6/r,

where r is the inradius and P, Q, R are the points of tangency of the
incircle with sides AB, BC, CA respectively. Prove that all triangles
in S are isosceles and similar to one another.
-/

/-!
## Formalization notes

A triangle is encoded by the three *tangent lengths* determined by the
incircle contact points: since tangents from a vertex to the incircle are
equal, we have AP = AR, BP = BQ and CQ = CR, so with

    x := AP,   y := BQ,   z := CR

the three side lengths of the triangle are x + y, y + z and z + x.

The inradius of a triangle with tangent lengths x, y, z satisfies

    r²(x + y + z) = xyz

(by Heron's formula: with s = x + y + z the area K satisfies K = r·s and
K² = s·(s−a)(s−b)(s−c) = s·xyz). This relation, together with positivity
of x, y, z, r, is the only geometric content needed for the proof.

Under the substitution u = r/x, v = r/y, w = r/z (these are the tangents
of the half-angles at A, B, C) the two hypotheses become uv+vw+wu = 1 and,
in the case where x is the minimum, 2u+5v+5w = 6. These two equations
force u = 4/3 and v = w = 1/3, because eliminating u leaves

    4(3v+3w−2)² + (3v−1)² + (3w−1)² = 0,

a sum of squares. Hence {x, y, z} = {3r/4, 3r, 3r}: two tangent lengths
coincide (so the triangle is isosceles) and the side lengths are
15r/4, 15r/4, 6r, i.e. in the ratio 5 : 5 : 8 (so all triangles in S are
similar to one another).
-/

namespace Usa2000P2

snip begin

/-- Core algebraic step. If `u v w : ℝ` satisfy `uv + vw + wu = 1` and
`2u + 5v + 5w = 6`, then `u = 4/3` and `v = w = 1/3`: eliminating `u` from
the first equation leaves `4(3v+3w−2)² + (3v−1)² + (3w−1)² = 0`,
a sum of squares. -/
lemma tangent_core {u v w : ℝ}
    (h1 : u * v + v * w + w * u = 1) (h2 : 2 * u + 5 * v + 5 * w = 6) :
    u = 4 / 3 ∧ v = 1 / 3 ∧ w = 1 / 3 := by
  have hu : u = 3 - 5 / 2 * (v + w) := by linarith
  rw [hu] at h1
  have key : 4 * (3 * v + 3 * w - 2) ^ 2 + (3 * v - 1) ^ 2 + (3 * w - 1) ^ 2 = 0 := by
    linear_combination -18 * h1
  have hv0 : (3 * v - 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (3 * v + 3 * w - 2), sq_nonneg (3 * v - 1), sq_nonneg (3 * w - 1)]
  have hw0 : (3 * w - 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (3 * v + 3 * w - 2), sq_nonneg (3 * v - 1), sq_nonneg (3 * w - 1)]
  have hvz : 3 * v - 1 = 0 := (pow_eq_zero_iff two_ne_zero).mp hv0
  have hwz : 3 * w - 1 = 0 := (pow_eq_zero_iff two_ne_zero).mp hw0
  have hv : v = 1 / 3 := by linarith
  have hw : w = 1 / 3 := by linarith
  rw [hv, hw] at hu
  exact ⟨by linarith, hv, hw⟩

/-- One case of the main argument: the tangent length `m` attains the
minimum, so the `min` term in the problem condition contributes `−3/m`,
leaving `2/m + 5/a + 5/b = 6/r`. With `u = r/m`, `v = r/a`, `w = r/b`
the inradius relation turns into `uv + vw + wu = 1` and `tangent_core`
applies. -/
lemma tangent_case {m a b r : ℝ}
    (hm : 0 < m) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (hheron : r ^ 2 * (m + a + b) = m * a * b)
    (hcond : 2 / m + 5 / a + 5 / b = 6 / r) :
    m = 3 * r / 4 ∧ a = 3 * r ∧ b = 3 * r := by
  have hm' : m ≠ 0 := ne_of_gt hm
  have ha' : a ≠ 0 := ne_of_gt ha
  have hb' : b ≠ 0 := ne_of_gt hb
  have hr' : r ≠ 0 := ne_of_gt hr
  -- the half-angle-tangent relation uv + vw + wu = 1
  have h1 : r / m * (r / a) + r / a * (r / b) + r / b * (r / m) = 1 := by
    have h5 : r / m * (r / a) + r / a * (r / b) + r / b * (r / m)
        = r ^ 2 * (m + a + b) / (m * a * b) := by
      field_simp
      ring
    rw [h5, hheron]
    exact div_self (mul_ne_zero (mul_ne_zero hm' ha') hb')
  -- the problem condition becomes 2u + 5v + 5w = 6
  have h2 : 2 * (r / m) + 5 * (r / a) + 5 * (r / b) = 6 := by
    have h4 : 2 * (r / m) + 5 * (r / a) + 5 * (r / b)
        = r * (2 / m + 5 / a + 5 / b) := by
      field_simp
    rw [h4, hcond]
    field_simp
  obtain ⟨hu, hv, hw⟩ := tangent_core h1 h2
  refine ⟨?_, ?_, ?_⟩
  · rw [div_eq_div_iff hm' (by norm_num : (3 : ℝ) ≠ 0)] at hu
    linarith
  · rw [div_eq_div_iff ha' (by norm_num : (3 : ℝ) ≠ 0)] at hv
    linarith
  · rw [div_eq_div_iff hb' (by norm_num : (3 : ℝ) ≠ 0)] at hw
    linarith

/-- Full determination of the tangent lengths: the smallest one equals
`3r/4` and the other two equal `3r`. -/
lemma tangent_determine {x y z r : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hr : 0 < r)
    (hheron : r ^ 2 * (x + y + z) = x * y * z)
    (hcond : 5 * (1 / x + 1 / y + 1 / z) - 3 / min (min x y) z = 6 / r) :
    (x = 3 * r / 4 ∧ y = 3 * r ∧ z = 3 * r) ∨
      (x = 3 * r ∧ y = 3 * r / 4 ∧ z = 3 * r) ∨
        (x = 3 * r ∧ y = 3 * r ∧ z = 3 * r / 4) := by
  have hx' : x ≠ 0 := ne_of_gt hx
  have hy' : y ≠ 0 := ne_of_gt hy
  have hz' : z ≠ 0 := ne_of_gt hz
  rcases le_total x y with hxy | hxy
  · rcases le_total x z with hxz | hxz
    · -- here `x` is the minimum tangent length
      rw [min_eq_left hxy, min_eq_left hxz] at hcond
      have hc : 2 / x + 5 / y + 5 / z = 6 / r := by
        have h0 : 5 * (1 / x + 1 / y + 1 / z) - 3 / x = 2 / x + 5 / y + 5 / z := by
          field_simp
          ring
        rwa [h0] at hcond
      exact Or.inl (tangent_case hx hy hz hr hheron hc)
    · -- here `z` is the minimum tangent length (z ≤ x ≤ y)
      rw [min_eq_left hxy, min_eq_right hxz] at hcond
      have hheron' : r ^ 2 * (z + x + y) = z * x * y := by linear_combination hheron
      have hc : 2 / z + 5 / x + 5 / y = 6 / r := by
        have h0 : 5 * (1 / x + 1 / y + 1 / z) - 3 / z = 2 / z + 5 / x + 5 / y := by
          field_simp
          ring
        rwa [h0] at hcond
      obtain ⟨h1, h2, h3⟩ := tangent_case hz hx hy hr hheron' hc
      exact Or.inr (Or.inr ⟨h2, h3, h1⟩)
  · rcases le_total y z with hyz | hyz
    · -- here `y` is the minimum tangent length
      rw [min_eq_right hxy, min_eq_left hyz] at hcond
      have hheron' : r ^ 2 * (y + x + z) = y * x * z := by linear_combination hheron
      have hc : 2 / y + 5 / x + 5 / z = 6 / r := by
        have h0 : 5 * (1 / x + 1 / y + 1 / z) - 3 / y = 2 / y + 5 / x + 5 / z := by
          field_simp
          ring
        rwa [h0] at hcond
      obtain ⟨h1, h2, h3⟩ := tangent_case hy hx hz hr hheron' hc
      exact Or.inr (Or.inl ⟨h2, h1, h3⟩)
    · -- here `z` is the minimum tangent length (z ≤ y ≤ x)
      rw [min_eq_right hxy, min_eq_right hyz] at hcond
      have hheron' : r ^ 2 * (z + x + y) = z * x * y := by linear_combination hheron
      have hc : 2 / z + 5 / x + 5 / y = 6 / r := by
        have h0 : 5 * (1 / x + 1 / y + 1 / z) - 3 / z = 2 / z + 5 / x + 5 / y := by
          field_simp
          ring
        rwa [h0] at hcond
      obtain ⟨h1, h2, h3⟩ := tangent_case hz hx hy hr hheron' hc
      exact Or.inr (Or.inr ⟨h2, h3, h1⟩)

snip end

problem usa2000_p2
    (x y z r : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hr : 0 < r)
    (hheron : r ^ 2 * (x + y + z) = x * y * z)
    (hcond : 5 * (1 / x + 1 / y + 1 / z) - 3 / min (min x y) z = 6 / r) :
    (x = y ∨ y = z ∨ z = x) ∧
      ((x + y) * 8 = (y + z) * 5 ∨ (y + z) * 8 = (z + x) * 5 ∨
        (z + x) * 8 = (x + y) * 5) := by
  -- The first conjunct says two tangent lengths coincide, hence two side
  -- lengths coincide (the triangle is isosceles); the second says that the
  -- equal sides and the remaining side are in the ratio 5 : 8, so the side
  -- lengths are in the ratio 5 : 5 : 8 (all such triangles are similar).
  rcases tangent_determine hx hy hz hr hheron hcond with
    ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · refine ⟨Or.inr (Or.inl (h2.trans h3.symm)), Or.inl ?_⟩
    rw [h1, h2, h3]
    ring
  · refine ⟨Or.inr (Or.inr (h3.trans h1.symm)), Or.inr (Or.inl ?_)⟩
    rw [h1, h2, h3]
    ring
  · refine ⟨Or.inl (h1.trans h2.symm), Or.inr (Or.inr ?_)⟩
    rw [h1, h2, h3]
    ring

end Usa2000P2
