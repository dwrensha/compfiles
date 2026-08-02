/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 2004, Problem 6

A circle ω is inscribed in a quadrilateral ABCD. Let I be the center of ω.
Suppose that (AI + DI)² + (BI + CI)² = (AB + CD)².
Prove that ABCD is an isosceles trapezoid.

## Formalization

We follow the completely algebraic solution from
https://web.evanchen.cc/exams/USAMO-2004-notes.pdf .

By similarity we may assume that ω has radius `1`. Let `a`, `b`, `c`, `d` be the
lengths of the tangents from `A`, `B`, `C`, `D` to ω. Each vertex together with `I`
and an adjacent tangency point forms a right triangle with legs `1` and the tangent
length, so `AI = √(a² + 1)`, `BI = √(b² + 1)`, `CI = √(c² + 1)`, `DI = √(d² + 1)`,
while the sides split at the tangency points into `AB = a + b` and `CD = c + d`.
Since `tan(A/2) = 1/a` etc. and `A/2 + B/2 + C/2 + D/2 = π`, the tangent
addition formula gives the constraint
`a + b + c + d = a·b·c + a·b·d + a·c·d + b·c·d`.
Conversely, any positive reals `a, b, c, d` satisfying this constraint arise from
such a quadrilateral.

The conclusion "ABCD is an isosceles trapezoid" becomes `a = d ∧ b = c`: indeed,
`a = d` and `b = c` mean `∠A = ∠D` and `∠B = ∠C` (since `tan(A/2) = 1/a` etc.),
the constraint then gives `a·b = 1`, hence `∠A + ∠B = π`, so `AD ∥ BC`, and
`AB = a + b = c + d = CD`.

The hypothesis of the problem is `(AI + DI)² + (BI + CI)² = (AB + CD)²`, i.e.
`(√(a²+1) + √(d²+1))² + (√(b²+1) + √(c²+1))² = (a + b + c + d)²`.
-/

namespace Usa2004P6

snip begin

/-- If `x, y, z, w` are positive reals satisfying the tangent-length constraint
(split into the pairs `(x, y)` and `(z, w)`), then `1 - x·y` and `1 - z·w` have
opposite signs, i.e. `(1 - x·y)(1 - z·w) ≤ 0`. -/
lemma pair_ineq {x y z w : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hw : 0 < w)
    (h : x + y + z + w = x * y * z + x * y * w + x * z * w + y * z * w) :
    (1 - x * y) * (1 - z * w) ≤ 0 := by
  have hxy : 0 < x + y := by positivity
  have hzw : 0 < z + w := by positivity
  have key : (x + y) * (1 - z * w) = (x * y - 1) * (z + w) := by linear_combination h
  have h2 : (1 - x * y) * (1 - z * w) * (x + y) = -((1 - x * y) ^ 2) * (z + w) := by
    linear_combination (1 - x * y) * key
  have h3 : (1 - x * y) * (1 - z * w) * (x + y) ≤ 0 := by
    rw [h2]
    apply mul_nonpos_of_nonpos_of_nonneg
    · exact neg_nonpos.mpr (sq_nonneg _)
    · exact hzw.le
  exact nonpos_of_mul_nonpos_left h3 hxy

/-- Summing the three pair inequalities gives a lower bound for the pair-sum
`S = a·b + a·c + a·d + b·c + b·d + c·d`. In particular `S > 3` and
`S - a·b·c·d - 1 > 0`, which will supply the signs needed for squaring. -/
lemma s_lower {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a + b + c + d = a * b * c + a * b * d + a * c * d + b * c * d) :
    3 + 3 * (a * b * c * d) ≤ a * b + a * c + a * d + b * c + b * d + c * d := by
  have p1 : (1 - a * b) * (1 - c * d) ≤ 0 := pair_ineq ha hb hc hd h
  have p2 : (1 - a * c) * (1 - b * d) ≤ 0 :=
    pair_ineq ha hc hb hd (by linear_combination h)
  have p3 : (1 - a * d) * (1 - b * c) ≤ 0 :=
    pair_ineq ha hd hb hc (by linear_combination h)
  nlinarith only [p1, p2, p3]

/-- The square of the pair-sum `S` expands, modulo the constraint, into squares of
the pair products. This is the identity
`S² = Σ (aᵢaⱼ)² + 2 Σ aᵢ² + 4S - 2abcd`. -/
lemma s_sq {a b c d : ℝ}
    (h : a + b + c + d = a * b * c + a * b * d + a * c * d + b * c * d) :
    (a * b + a * c + a * d + b * c + b * d + c * d) ^ 2 =
      (a * b) ^ 2 + (a * c) ^ 2 + (a * d) ^ 2 + (b * c) ^ 2 + (b * d) ^ 2 + (c * d) ^ 2
        + 2 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2)
        + 4 * (a * b + a * c + a * d + b * c + b * d + c * d) - 2 * (a * b * c * d) := by
  linear_combination (-2 * (a + b + c + d)) * h

/-- The polynomial identity `Π(aᵢ² + 1) = (S - abcd - 1)² + (e₁ - e₃)²`
(compare `|P(i)|²` for `P(t) = Π(t - aᵢ)`), specialized by the constraint `e₁ = e₃`. -/
lemma prod_eq_sq {a b c d : ℝ}
    (h : a + b + c + d = a * b * c + a * b * d + a * c * d + b * c * d) :
    ((a ^ 2 + 1) * (d ^ 2 + 1)) * ((b ^ 2 + 1) * (c ^ 2 + 1)) =
      (a * b + a * c + a * d + b * c + b * d + c * d - a * b * c * d - 1) ^ 2 := by
  linear_combination
    (a + b + c + d - (a * b * c + a * b * d + a * c * d + b * c * d)) * h

/-- The heart of the solution: modulo the constraint, the difference between the
two squared quantities is a sum of six squares. Hence the problem's inequality
holds for every tangential quadrilateral, with equality iff all six squares
vanish, in particular iff `a = d` and `b = c`. -/
lemma key_sq {a b c d : ℝ}
    (h : a + b + c + d = a * b * c + a * b * d + a * c * d + b * c * d) :
    (a * b + a * c + a * d + b * c + b * d + c * d - 2) ^ 2
      - ((a ^ 2 + 1) * (d ^ 2 + 1) + (b ^ 2 + 1) * (c ^ 2 + 1)
        + 2 * (a * b + a * c + a * d + b * c + b * d + c * d - a * b * c * d - 1))
      = (a * b - 1) ^ 2 + (a * c - 1) ^ 2 + (b * d - 1) ^ 2 + (c * d - 1) ^ 2
        + (a - d) ^ 2 + (b - c) ^ 2 := by
  have hS := s_sq h
  linear_combination hS

/-- The a priori inequality `(AI·DI cross term) + (BI·CI cross term) ≤ S - 2`,
valid for every tangential quadrilateral. -/
lemma sqrt_sum_le {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a + b + c + d = a * b * c + a * b * d + a * c * d + b * c * d) :
    Real.sqrt ((a ^ 2 + 1) * (d ^ 2 + 1)) + Real.sqrt ((b ^ 2 + 1) * (c ^ 2 + 1))
      ≤ a * b + a * c + a * d + b * c + b * d + c * d - 2 := by
  have hS := s_lower ha hb hc hd h
  have habcd : 0 < a * b * c * d := by positivity
  have hP : 0 < a * b + a * c + a * d + b * c + b * d + c * d - a * b * c * d - 1 := by
    linarith only [hS, habcd]
  have hS2 : 0 < a * b + a * c + a * d + b * c + b * d + c * d - 2 := by
    linarith only [hS, habcd]
  have hX2 : (Real.sqrt ((a ^ 2 + 1) * (d ^ 2 + 1))) ^ 2 = (a ^ 2 + 1) * (d ^ 2 + 1) :=
    Real.sq_sqrt (by positivity)
  have hY2 : (Real.sqrt ((b ^ 2 + 1) * (c ^ 2 + 1))) ^ 2 = (b ^ 2 + 1) * (c ^ 2 + 1) :=
    Real.sq_sqrt (by positivity)
  have hXY : Real.sqrt ((a ^ 2 + 1) * (d ^ 2 + 1)) * Real.sqrt ((b ^ 2 + 1) * (c ^ 2 + 1))
      = a * b + a * c + a * d + b * c + b * d + c * d - a * b * c * d - 1 := by
    rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (a ^ 2 + 1) * (d ^ 2 + 1)),
      prod_eq_sq h, Real.sqrt_sq hP.le]
  have hsumsq : 0 ≤ (a * b - 1) ^ 2 + (a * c - 1) ^ 2 + (b * d - 1) ^ 2 + (c * d - 1) ^ 2
      + (a - d) ^ 2 + (b - c) ^ 2 := by positivity
  have hkey := key_sq h
  have expand : (Real.sqrt ((a ^ 2 + 1) * (d ^ 2 + 1))
        + Real.sqrt ((b ^ 2 + 1) * (c ^ 2 + 1))) ^ 2
      = (a ^ 2 + 1) * (d ^ 2 + 1) + (b ^ 2 + 1) * (c ^ 2 + 1)
        + 2 * (a * b + a * c + a * d + b * c + b * d + c * d - a * b * c * d - 1) := by
    linear_combination hX2 + hY2 + 2 * hXY
  have hsq : (Real.sqrt ((a ^ 2 + 1) * (d ^ 2 + 1))
        + Real.sqrt ((b ^ 2 + 1) * (c ^ 2 + 1))) ^ 2
      ≤ (a * b + a * c + a * d + b * c + b * d + c * d - 2) ^ 2 := by
    rw [expand]
    linarith only [hkey, hsumsq]
  have hsum_pos : 0 < (a * b + a * c + a * d + b * c + b * d + c * d - 2)
      + (Real.sqrt ((a ^ 2 + 1) * (d ^ 2 + 1)) + Real.sqrt ((b ^ 2 + 1) * (c ^ 2 + 1))) := by
    have hx := Real.sqrt_nonneg ((a ^ 2 + 1) * (d ^ 2 + 1))
    have hy := Real.sqrt_nonneg ((b ^ 2 + 1) * (c ^ 2 + 1))
    linarith only [hS2, hx, hy]
  have hfactor : 0 ≤ ((a * b + a * c + a * d + b * c + b * d + c * d - 2)
        - (Real.sqrt ((a ^ 2 + 1) * (d ^ 2 + 1)) + Real.sqrt ((b ^ 2 + 1) * (c ^ 2 + 1))))
      * ((a * b + a * c + a * d + b * c + b * d + c * d - 2)
        + (Real.sqrt ((a ^ 2 + 1) * (d ^ 2 + 1)) + Real.sqrt ((b ^ 2 + 1) * (c ^ 2 + 1)))) := by
    nlinarith only [hsq]
  have hle := nonneg_of_mul_nonneg_left hfactor hsum_pos
  linarith only [hle]

/-- The equality case: if the inequality of `sqrt_sum_le` holds with equality,
then the last two squares of `key_sq` vanish, giving `a = d` and `b = c`. -/
lemma eq_of_sqrt_sum_eq {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a + b + c + d = a * b * c + a * b * d + a * c * d + b * c * d)
    (heq : Real.sqrt ((a ^ 2 + 1) * (d ^ 2 + 1)) + Real.sqrt ((b ^ 2 + 1) * (c ^ 2 + 1))
      = a * b + a * c + a * d + b * c + b * d + c * d - 2) :
    a = d ∧ b = c := by
  have hS := s_lower ha hb hc hd h
  have habcd : 0 < a * b * c * d := by positivity
  have hP : 0 < a * b + a * c + a * d + b * c + b * d + c * d - a * b * c * d - 1 := by
    linarith only [hS, habcd]
  have hX2 : (Real.sqrt ((a ^ 2 + 1) * (d ^ 2 + 1))) ^ 2 = (a ^ 2 + 1) * (d ^ 2 + 1) :=
    Real.sq_sqrt (by positivity)
  have hY2 : (Real.sqrt ((b ^ 2 + 1) * (c ^ 2 + 1))) ^ 2 = (b ^ 2 + 1) * (c ^ 2 + 1) :=
    Real.sq_sqrt (by positivity)
  have hXY : Real.sqrt ((a ^ 2 + 1) * (d ^ 2 + 1)) * Real.sqrt ((b ^ 2 + 1) * (c ^ 2 + 1))
      = a * b + a * c + a * d + b * c + b * d + c * d - a * b * c * d - 1 := by
    rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (a ^ 2 + 1) * (d ^ 2 + 1)),
      prod_eq_sq h, Real.sqrt_sq hP.le]
  have expand : (Real.sqrt ((a ^ 2 + 1) * (d ^ 2 + 1))
        + Real.sqrt ((b ^ 2 + 1) * (c ^ 2 + 1))) ^ 2
      = (a ^ 2 + 1) * (d ^ 2 + 1) + (b ^ 2 + 1) * (c ^ 2 + 1)
        + 2 * (a * b + a * c + a * d + b * c + b * d + c * d - a * b * c * d - 1) := by
    linear_combination hX2 + hY2 + 2 * hXY
  have hsq : (Real.sqrt ((a ^ 2 + 1) * (d ^ 2 + 1))
        + Real.sqrt ((b ^ 2 + 1) * (c ^ 2 + 1))) ^ 2
      = (a * b + a * c + a * d + b * c + b * d + c * d - 2) ^ 2 := by rw [heq]
  have hkey := key_sq h
  have hzero : (a * b - 1) ^ 2 + (a * c - 1) ^ 2 + (b * d - 1) ^ 2 + (c * d - 1) ^ 2
      + (a - d) ^ 2 + (b - c) ^ 2 = 0 := by linarith only [hkey, hsq, expand]
  have had : (a - d) ^ 2 = 0 := by
    linarith only [hzero, sq_nonneg (a * b - 1), sq_nonneg (a * c - 1),
      sq_nonneg (b * d - 1), sq_nonneg (c * d - 1), sq_nonneg (b - c), sq_nonneg (a - d)]
  have hbc : (b - c) ^ 2 = 0 := by
    linarith only [hzero, sq_nonneg (a * b - 1), sq_nonneg (a * c - 1),
      sq_nonneg (b * d - 1), sq_nonneg (c * d - 1), sq_nonneg (b - c), sq_nonneg (a - d)]
  exact ⟨sub_eq_zero.mp (sq_eq_zero_iff.mp had), sub_eq_zero.mp (sq_eq_zero_iff.mp hbc)⟩

snip end

problem usa2004_p6 {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a + b + c + d = a * b * c + a * b * d + a * c * d + b * c * d)
    (heq : (Real.sqrt (a ^ 2 + 1) + Real.sqrt (d ^ 2 + 1)) ^ 2
        + (Real.sqrt (b ^ 2 + 1) + Real.sqrt (c ^ 2 + 1)) ^ 2 = (a + b + c + d) ^ 2) :
    a = d ∧ b = c := by
  have h1 : (Real.sqrt (a ^ 2 + 1) + Real.sqrt (d ^ 2 + 1)) ^ 2
      = (a ^ 2 + 1) + (d ^ 2 + 1) + 2 * Real.sqrt ((a ^ 2 + 1) * (d ^ 2 + 1)) := by
    linear_combination Real.sq_sqrt (show (0 : ℝ) ≤ a ^ 2 + 1 by positivity)
      + Real.sq_sqrt (show (0 : ℝ) ≤ d ^ 2 + 1 by positivity)
      - 2 * Real.sqrt_mul (show (0 : ℝ) ≤ a ^ 2 + 1 by positivity) (d ^ 2 + 1)
  have h2 : (Real.sqrt (b ^ 2 + 1) + Real.sqrt (c ^ 2 + 1)) ^ 2
      = (b ^ 2 + 1) + (c ^ 2 + 1) + 2 * Real.sqrt ((b ^ 2 + 1) * (c ^ 2 + 1)) := by
    linear_combination Real.sq_sqrt (show (0 : ℝ) ≤ b ^ 2 + 1 by positivity)
      + Real.sq_sqrt (show (0 : ℝ) ≤ c ^ 2 + 1 by positivity)
      - 2 * Real.sqrt_mul (show (0 : ℝ) ≤ b ^ 2 + 1 by positivity) (c ^ 2 + 1)
  have h3 : (a + b + c + d) ^ 2
      = (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2)
        + 2 * (a * b + a * c + a * d + b * c + b * d + c * d) := by ring
  rw [h1, h2, h3] at heq
  have heq2 : Real.sqrt ((a ^ 2 + 1) * (d ^ 2 + 1)) + Real.sqrt ((b ^ 2 + 1) * (c ^ 2 + 1))
      = a * b + a * c + a * d + b * c + b * d + c * d - 2 := by linarith only [heq]
  exact eq_of_sqrt_sum_eq ha hb hc hd h heq2

end Usa2004P6
