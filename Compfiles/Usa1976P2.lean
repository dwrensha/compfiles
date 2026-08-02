/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 1976, Problem 2

AB is a fixed chord of a circle, not a diameter. CD is a variable diameter.
Find the locus of the intersection of AC and BD.

# Formalization notes

We work in Cartesian coordinates. Since the locus is preserved by rigid
motions and scaling, we normalize: the circle is the unit circle centered at
the origin and the fixed chord is vertical, so `A = (a, b)` and `B = (a, -b)`
with `a² + b² = 1`. The hypothesis that `AB` is not a diameter becomes
`a ≠ 0`, while `A ≠ B` becomes `b ≠ 0`. A diameter `CD` is parametrized by
its endpoint `C = (c, s)` on the unit circle, with `D = -C`; the positions
`C = A` and `D = B` are excluded since then `AC` or `BD` is not a
well-defined line.

The answer: the locus is the circle through `A` and `B` that is orthogonal to
the given circle — center `(1/a, 0)`, radius `|b / a|` — with the two points
`((1 + b²)/a, ±b)` removed; those two points correspond to the excluded
degenerate diameters. (Indeed, the distance from the origin to `(1/a, 0)`
squared is `1/a² = 1 + (b/a)²`, the sum of the squares of the two radii.)
-/

namespace Usa1976P2

/-- Collinearity of three points in the Cartesian plane, in determinant form. -/
def Collinear3 (P Q R : ℝ × ℝ) : Prop :=
  (Q.1 - P.1) * (R.2 - P.2) = (R.1 - P.1) * (Q.2 - P.2)

/-- The answer: the circle through `A = (a, b)` and `B = (a, -b)` orthogonal to
the unit circle (center `(1/a, 0)`, radius squared `(b/a)²`), minus the two
points `((1 + b²)/a, ±b)` coming from the degenerate diameters `C = A` and
`D = B` where `AC` or `BD` is not a well-defined line. -/
determine locus (a b : ℝ) : Set (ℝ × ℝ) :=
  {X | (X.1 - 1 / a)^2 + X.2^2 = (b / a)^2 ∧
       X ≠ ((1 + b^2) / a, -b) ∧ X ≠ ((1 + b^2) / a, b)}

snip begin

/-- The explicit intersection point of the lines `AC` and `BD`. -/
noncomputable def xpt (a b c s : ℝ) : ℝ × ℝ := ((1 + b * s) / a, -b * c / a)

/-- With `C = (c, s)`, `D = (-c, -s)`, the lines `AC` and `BD` fail to
intersect only when `s = b`, which is exactly the two excluded degenerate
positions `C = A` and `D = B`. -/
lemma s_ne_b {a b c s : ℝ} (hunit : a^2 + b^2 = 1) (hcs : c^2 + s^2 = 1)
    (hcA : (c, s) ≠ (a, b)) (hdB : (-c, -s) ≠ (a, -b)) : s ≠ b := by
  intro hsb
  subst hsb
  have hc2 : c^2 = a^2 := by linarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hc2 with h | h
  · subst h; exact hcA rfl
  · subst h; exact hdB (by simp)

/-- The intersection point lies on the line through `A` and `C`. -/
lemma collinear_ac_xpt {a b c s : ℝ} (ha : a ≠ 0)
    (hunit : a^2 + b^2 = 1) (hcs : c^2 + s^2 = 1) :
    Collinear3 (a, b) (c, s) (xpt a b c s) := by
  simp only [Collinear3, xpt]
  have e1 : (1 + b * s) / a - a = b * (b + s) / a := by
    field_simp
    linear_combination -hunit
  have e2 : -b * c / a - b = -b * (c + a) / a := by field_simp; ring
  rw [e1, e2]
  field_simp
  linear_combination b * hunit - b * hcs

/-- The intersection point lies on the line through `B` and `D`. -/
lemma collinear_bd_xpt {a b c s : ℝ} (ha : a ≠ 0)
    (hunit : a^2 + b^2 = 1) (hcs : c^2 + s^2 = 1) :
    Collinear3 (a, -b) (-c, -s) (xpt a b c s) := by
  simp only [Collinear3, xpt]
  have e1 : (1 + b * s) / a - a = b * (b + s) / a := by
    field_simp
    linear_combination -hunit
  have e2 : -b * c / a - -b = b * (a - c) / a := by field_simp; ring
  rw [e1, e2]
  field_simp
  linear_combination b * hcs - b * hunit

/-- The intersection point lies on the circle through `A` and `B` orthogonal
to the unit circle. -/
lemma mem_circle_xpt {a b c s : ℝ} (ha : a ≠ 0) (hcs : c^2 + s^2 = 1) :
    ((xpt a b c s).1 - 1 / a)^2 + (xpt a b c s).2^2 = (b / a)^2 := by
  simp only [xpt]
  have e : (1 + b * s) / a - 1 / a = b * s / a := by field_simp; ring
  rw [e]
  field_simp
  linear_combination b^2 * hcs

/-- Any common point of the two lines equals the explicit intersection point:
the intersection is unique. -/
lemma eq_xpt {a b c s : ℝ} (ha : a ≠ 0)
    (hunit : a^2 + b^2 = 1) (hcs : c^2 + s^2 = 1) (hsb : s ≠ b)
    {X : ℝ × ℝ}
    (hAC : Collinear3 (a, b) (c, s) X) (hBD : Collinear3 (a, -b) (-c, -s) X) :
    X = xpt a b c s := by
  simp only [Collinear3] at hAC hBD
  -- add the two collinearity equations to eliminate `X.1`
  have h : 2 * a * X.2 = -(2 * b * c) := by linear_combination -hAC - hBD
  have h2 : a * X.2 = -(b * c) := by linear_combination h / 2
  have hv : X.2 = -b * c / a := by
    rw [eq_div_iff ha]
    linear_combination h2
  have hsb' : s - b ≠ 0 := sub_ne_zero.mpr hsb
  -- substitute back to get `X.1`
  have e : (X.1 - a) * (s - b) = b * (s + b) * (s - b) / a := by
    rw [← hAC, hv]
    field_simp
    linear_combination (-b) * hcs + b * hunit
  have e2 : (X.1 - a) * a = b * (s + b) := by
    have h1 := e
    field_simp at h1
    linear_combination h1
  have e3 : X.1 * a = 1 + b * s := by linear_combination e2 + hunit
  have hu : X.1 = (1 + b * s) / a := by
    rw [eq_div_iff ha]
    exact e3
  exact Prod.ext_iff.mpr ⟨hu, hv⟩

snip end

problem usa1976_p2 (a b : ℝ) (hunit : a^2 + b^2 = 1) (ha : a ≠ 0) (hb : b ≠ 0)
    (X : ℝ × ℝ) :
    X ∈ locus a b ↔
      ∃ c s : ℝ, c^2 + s^2 = 1 ∧ (c, s) ≠ (a, b) ∧ (-c, -s) ≠ (a, -b) ∧
        Collinear3 (a, b) (c, s) X ∧ Collinear3 (a, -b) (-c, -s) X := by
  constructor
  · -- every point of the locus arises from a diameter:
    -- recover `C = (c, s)` from `X` via `(s, -c) = (a/b) * (X - (1/a, 0))`
    rintro ⟨hcirc, hX1, hX2⟩
    -- clear denominators in the circle equation, to get a polynomial identity
    have hcirc2 : (a * X.1 - 1)^2 + (a * X.2)^2 = b^2 := by
      have h : a^2 * ((X.1 - 1 / a)^2 + X.2^2) = a^2 * (b / a)^2 := by rw [hcirc]
      have h2 : a^2 * (b / a)^2 = b^2 := by field_simp
      rw [h2] at h
      have h3 : a * (X.1 - 1 / a) = a * X.1 - 1 := by field_simp
      have h4 : a^2 * ((X.1 - 1 / a)^2 + X.2^2) = (a * (X.1 - 1 / a))^2 + (a * X.2)^2 := by
        ring
      rwa [h4, h3] at h
    refine ⟨-(a / b) * X.2, (a / b) * (X.1 - 1 / a), ?_, ?_, ?_, ?_, ?_⟩
    · -- `C` lies on the unit circle
      have e : (-(a / b) * X.2)^2 + ((a / b) * (X.1 - 1 / a))^2 =
          (a / b)^2 * ((X.1 - 1 / a)^2 + X.2^2) := by ring
      rw [e, hcirc]
      have e2 : (a / b)^2 * (b / a)^2 = 1 := by field_simp
      exact e2
    · -- `C ≠ A`, since `X` is not the first excluded point
      intro h
      simp only [Prod.mk.injEq] at h
      obtain ⟨hc, hs⟩ := h
      have hy : X.2 = -b := by
        have h' : (a / b) * X.2 = -a := by linear_combination -hc
        field_simp at h'
        exact h'
      have hx : X.1 = (1 + b^2) / a := by
        rw [eq_div_iff ha]
        have h' : X.1 * a - 1 = b * b := by
          have step : (a / b) * (X.1 - 1 / a) = (X.1 * a - 1) / b := by
            field_simp
          rw [step] at hs
          exact (div_eq_iff hb).mp hs
        linear_combination h'
      exact hX1 (Prod.ext_iff.mpr ⟨hx, hy⟩)
    · -- `D ≠ B`, since `X` is not the second excluded point
      intro h
      simp only [Prod.mk.injEq] at h
      obtain ⟨hc, hs⟩ := h
      have hy : X.2 = b := by
        field_simp at hc
        exact hc
      have hx : X.1 = (1 + b^2) / a := by
        rw [eq_div_iff ha]
        have h' : X.1 * a - 1 = b * b := by
          have step : (a / b) * (X.1 - 1 / a) = (X.1 * a - 1) / b := by
            field_simp
          have hs' : (a / b) * (X.1 - 1 / a) = b := by linear_combination -hs
          rw [step] at hs'
          exact (div_eq_iff hb).mp hs'
        linear_combination h'
      exact hX2 (Prod.ext_iff.mpr ⟨hx, hy⟩)
    · -- `X` lies on the line `AC`
      simp only [Collinear3]
      -- first prove the equation obtained by clearing denominators by hand
      have key : a * (-a * (X.2^2 - b^2)) = a * ((X.1 - a) * (a * X.1 - 1 - b^2)) := by
        linear_combination -hcirc2 + (a * X.1 - 1) * hunit
      have key' : -a * (X.2^2 - b^2) = (X.1 - a) * (a * X.1 - 1 - b^2) :=
        mul_left_cancel₀ ha key
      field_simp
      linear_combination key'
    · -- `X` lies on the line `BD`
      simp only [Collinear3]
      -- first prove the equation obtained by clearing denominators by hand
      have key : a * (a * (X.2^2 - b^2)) = a * ((X.1 - a) * (-(a * X.1) + 1 + b^2)) := by
        linear_combination hcirc2 + (1 - a * X.1) * hunit
      have key' : a * (X.2^2 - b^2) = (X.1 - a) * (-(a * X.1) + 1 + b^2) :=
        mul_left_cancel₀ ha key
      field_simp
      linear_combination key'
  · -- every diameter produces a point of the locus
    rintro ⟨c, s, hcs, hcA, hdB, hAC, hBD⟩
    have hsb : s ≠ b := s_ne_b hunit hcs hcA hdB
    have hX : X = xpt a b c s := eq_xpt ha hunit hcs hsb hAC hBD
    refine ⟨?_, ?_, ?_⟩
    · -- the intersection lies on the circle
      rw [hX]
      exact mem_circle_xpt ha hcs
    · -- it is not the first excluded point (else `C = A`)
      intro h
      rw [hX] at h
      have h1 : (1 + b * s) / a = (1 + b^2) / a := congrArg Prod.fst h
      have h2 : -b * c / a = -b := congrArg Prod.snd h
      have hc : c = a := by
        field_simp at h2
        exact neg_inj.mp h2
      have hs : s = b := by
        have e1 : 1 + b * s = 1 + b^2 := by
          rw [div_eq_div_iff ha ha] at h1
          exact mul_right_cancel₀ ha h1
        have e2 : s * b = b * b := by linear_combination e1
        exact (mul_left_inj' hb).mp e2
      exact hcA (Prod.ext_iff.mpr ⟨hc, hs⟩)
    · -- it is not the second excluded point (else `D = B`)
      intro h
      rw [hX] at h
      have h1 : (1 + b * s) / a = (1 + b^2) / a := congrArg Prod.fst h
      have h2 : -b * c / a = b := congrArg Prod.snd h
      have hc : c = -a := by
        field_simp at h2
        linear_combination -h2
      have hs : s = b := by
        have e1 : 1 + b * s = 1 + b^2 := by
          rw [div_eq_div_iff ha ha] at h1
          exact mul_right_cancel₀ ha h1
        have e2 : s * b = b * b := by linear_combination e1
        exact (mul_left_inj' hb).mp e2
      subst hc
      subst hs
      exact hdB (by simp)

end Usa1976P2
