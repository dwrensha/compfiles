/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Geometry]
}

/-!
# USA Mathematical Olympiad 2002, Problem 2

Let $ABC$ be a triangle such that

$$\left(\cot\frac{A}{2}\right)^2 + \left(2\cot\frac{B}{2}\right)^2 +
\left(3\cot\frac{C}{2}\right)^2 = \left(\frac{6s}{7r}\right)^2,$$

where $s$ and $r$ denote its semiperimeter and its inradius, respectively.
Show that triangle $ABC$ is similar to a triangle $T$ whose side lengths are
all positive integers with no common divisor and determine those integers.
-/

namespace Usa2002P2

/-!
### Algebraic encoding

We work with the side lengths `a`, `b`, `c` of the triangle (positive reals
satisfying the strict triangle inequalities), with `a` opposite to the angle
`A` etc. The semiperimeter is `s = (a + b + c) / 2`, the inradius is given by
Heron's formula `r = √((s - a)(s - b)(s - c) / s)`, and the half-angle formula
gives `cot (A / 2) = (s - a) / r` (and similarly for `B` and `C`). This turns
the given trigonometric relation into a polynomial condition on `a`, `b`, `c`.
-/

/-- The semiperimeter of a triangle with side lengths `a`, `b`, `c`. -/
noncomputable def semiperimeter (a b c : ℝ) : ℝ := (a + b + c) / 2

/-- The inradius of a triangle with side lengths `a`, `b`, `c`, given by
Heron's formula `r = √((s - a)(s - b)(s - c) / s)` where `s` is the
semiperimeter. -/
noncomputable def inradius (a b c : ℝ) : ℝ :=
  Real.sqrt ((semiperimeter a b c - a) * (semiperimeter a b c - b) *
    (semiperimeter a b c - c) / semiperimeter a b c)

/-- The relation assumed in the problem, with `cot (A / 2) = (s - a) / r` etc.
by the half-angle formula. -/
noncomputable def relation (a b c : ℝ) : Prop :=
  ((semiperimeter a b c - a) / inradius a b c)^2 +
  (2 * ((semiperimeter a b c - b) / inradius a b c))^2 +
  (3 * ((semiperimeter a b c - c) / inradius a b c))^2 =
  (6 * semiperimeter a b c / (7 * inradius a b c))^2

/-- The side lengths of the triangle `T`: 13, 40, 45. -/
determine solution : ℕ × ℕ × ℕ := (13, 40, 45)

snip begin

-- Following the solution by John Scholes
-- (https://www.kalva.demon.co.uk/usa/usol022.html).
--
-- With `d = s - a`, `e = s - b`, `f = s - c` (so that `s = d + e + f`),
-- the relation rewrites as `49 * (d² + 4e² + 9f²) = 36 * (d + e + f)²`,
-- which is the sum of squares
-- `(2d - 18f)² + (3d - 12e)² + (4e - 9f)² = 0`.
-- Hence `d = 9f` and `4e = 9f`, so `d : e : f = 36 : 9 : 4` and
-- `a : b : c = (e + f) : (d + f) : (d + e) = 13 : 40 : 45`.

/-- The key sum-of-squares identity. -/
lemma scholes_sos (d e f : ℝ) :
    49 * (d^2 + 4 * e^2 + 9 * f^2) - 36 * (d + e + f)^2 =
    (2*d - 18*f)^2 + (3*d - 12*e)^2 + (4*e - 9*f)^2 := by
  ring

/-- The inradius of a genuine triangle is positive. -/
lemma inradius_pos {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a < b + c) (hbc : b < c + a) (hca : c < a + b) :
    0 < inradius a b c := by
  have h1 : 0 < semiperimeter a b c - a := by
    simp only [semiperimeter]; linarith
  have h2 : 0 < semiperimeter a b c - b := by
    simp only [semiperimeter]; linarith
  have h3 : 0 < semiperimeter a b c - c := by
    simp only [semiperimeter]; linarith
  have h4 : 0 < semiperimeter a b c := by
    simp only [semiperimeter]; linarith
  exact Real.sqrt_pos.mpr (div_pos (mul_pos (mul_pos h1 h2) h3) h4)

/-- The forward direction: the relation forces the side lengths to be
proportional to `13 : 40 : 45`. -/
lemma forward {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a < b + c) (hbc : b < c + a) (hca : c < a + b)
    (h : relation a b c) :
    ∃ k : ℝ, 0 < k ∧ a = 13 * k ∧ b = 40 * k ∧ c = 45 * k := by
  simp only [relation] at h
  set s := semiperimeter a b c with hs
  set r := inradius a b c with hr
  set d := s - a with hd
  set e := s - b with he
  set f := s - c with hf
  have hd_pos : 0 < d := by rw [hd, hs]; simp only [semiperimeter]; linarith
  have he_pos : 0 < e := by rw [he, hs]; simp only [semiperimeter]; linarith
  have hf_pos : 0 < f := by rw [hf, hs]; simp only [semiperimeter]; linarith
  have hr_pos : 0 < r := by rw [hr]; exact inradius_pos ha hb hc hab hbc hca
  have hr_ne : r ≠ 0 := hr_pos.ne'
  -- Clear the denominators in the given relation.
  have h1 : 49 * (d^2 + 4 * e^2 + 9 * f^2) = 36 * s^2 := by
    calc 49 * (d^2 + 4 * e^2 + 9 * f^2)
        = ((d / r)^2 + (2 * (e / r))^2 + (3 * (f / r))^2) * (49 * r^2) := by
          field_simp; ring
      _ = (6 * s / (7 * r))^2 * (49 * r^2) := by rw [h]
      _ = 36 * s^2 := by field_simp; ring
  -- Since `s = d + e + f`, the relation is a sum of squares.
  have hs_def : s = d + e + f := by
    have habc : a + b + c = 2 * s := by rw [hs]; simp only [semiperimeter]; ring
    linarith [hd, he, hf]
  have hSOS : (2*d - 18*f)^2 + (3*d - 12*e)^2 + (4*e - 9*f)^2 = 0 := by
    have hkey := scholes_sos d e f
    rw [← hs_def, h1] at hkey
    simp only [sub_self] at hkey
    exact hkey.symm
  -- Each square must vanish.
  have h2d : (2*d - 18*f)^2 = 0 := by
    have s2 := sq_nonneg (3*d - 12*e)
    have s3 := sq_nonneg (4*e - 9*f)
    nlinarith [hSOS]
  have h3d : (3*d - 12*e)^2 = 0 := by
    have s1 := sq_nonneg (2*d - 18*f)
    have s3 := sq_nonneg (4*e - 9*f)
    nlinarith [hSOS]
  have h4e : (4*e - 9*f)^2 = 0 := by
    have s1 := sq_nonneg (2*d - 18*f)
    have s2 := sq_nonneg (3*d - 12*e)
    nlinarith [hSOS]
  have r1 : 2 * d = 18 * f := by rw [sq_eq_zero_iff] at h2d; linarith
  have r2 : 3 * d = 12 * e := by rw [sq_eq_zero_iff] at h3d; linarith
  have r3 : 4 * e = 9 * f := by rw [sq_eq_zero_iff] at h4e; linarith
  -- Back-substitute: `a = e + f`, `b = d + f`, `c = d + e`.
  have ha_eq : a = e + f := by linarith [hd, hs_def]
  have hb_eq : b = d + f := by linarith [he, hs_def]
  have hc_eq : c = d + e := by linarith [hf, hs_def]
  refine ⟨f / 4, by linarith, ?_, ?_, ?_⟩
  · rw [ha_eq]; linarith [r1, r3]
  · rw [hb_eq]; linarith [r1]
  · rw [hc_eq]; linarith [r1, r3]

/-- The backward direction: any triangle with side lengths proportional to
`13 : 40 : 45` satisfies the relation. -/
lemma backward {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a < b + c) (hbc : b < c + a) (hca : c < a + b)
    (h : ∃ k : ℝ, 0 < k ∧ a = 13 * k ∧ b = 40 * k ∧ c = 45 * k) :
    relation a b c := by
  obtain ⟨k, hk, rfl, rfl, rfl⟩ := h
  have hk0 : (k : ℝ) ≠ 0 := hk.ne'
  have hs : semiperimeter (13 * k) (40 * k) (45 * k) = 49 * k := by
    simp only [semiperimeter]; ring
  have hr : inradius (13 * k) (40 * k) (45 * k) = 36 * k / 7 := by
    rw [inradius, hs]
    have h4 : (49 * k - 13 * k) * (49 * k - 40 * k) * (49 * k - 45 * k) / (49 * k)
        = (36 * k / 7)^2 := by
      field_simp; ring
    rw [h4, Real.sqrt_sq (by linarith [hk.le])]
  simp only [relation]
  rw [hs, hr]
  have e1 : (49 * k - 13 * k) / (36 * k / 7) = 7 := by field_simp; ring
  have e2 : (49 * k - 40 * k) / (36 * k / 7) = 7 / 4 := by field_simp; ring
  have e3 : (49 * k - 45 * k) / (36 * k / 7) = 7 / 9 := by field_simp; ring
  have e4 : 6 * (49 * k) / (7 * (36 * k / 7)) = 49 / 6 := by field_simp; ring
  rw [e1, e2, e3, e4]
  norm_num

snip end

problem usa2002_p2 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a < b + c) (hbc : b < c + a) (hca : c < a + b) :
    relation a b c ↔
      ∃ k : ℝ, 0 < k ∧ a = (solution.1 : ℝ) * k ∧ b = (solution.2.1 : ℝ) * k ∧
        c = (solution.2.2 : ℝ) * k := by
  constructor
  · intro h
    obtain ⟨k, hk, h1, h2, h3⟩ := forward ha hb hc hab hbc hca h
    exact ⟨k, hk, by simpa using h1, by simpa using h2, by simpa using h3⟩
  · intro h
    obtain ⟨k, hk, h1, h2, h3⟩ := h
    have h1' : a = 13 * k := by simpa using h1
    have h2' : b = 40 * k := by simpa using h2
    have h3' : c = 45 * k := by simpa using h3
    exact backward ha hb hc hab hbc hca ⟨k, hk, h1', h2', h3'⟩

/-- The integers 13, 40, 45 have no common divisor, as claimed. -/
problem usa2002_p2_no_common_divisor :
    Nat.gcd (Nat.gcd solution.1 solution.2.1) solution.2.2 = 1 := by
  decide

end Usa2002P2
