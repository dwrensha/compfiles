/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry, .NumberTheory] }

/-!
# USA Mathematical Olympiad 1991, Problem 1

An obtuse angled triangle has integral sides and one acute angle is twice
the other. Find the smallest possible perimeter.

## Formalization note

We encode the angle condition algebraically, following the standard
solution. Order the side lengths as `a < b < c`; this is no loss of
generality: in an obtuse triangle the obtuse angle is the unique largest
angle, so the longest side is unique, and the two acute angles are
distinct (one is twice the other), so the two shorter sides are distinct
as well. The three lengths form a triangle iff `c < a + b`, and the
triangle is obtuse iff `a^2 + b^2 < c^2` (the obtuse angle is opposite the
longest side `c`; the angles opposite `a` and `b` are then automatically
acute). Since `a < b`, the angle opposite `b` exceeds the angle opposite
`a`, so "one acute angle is twice the other" means that the angle
opposite `b` is twice the angle opposite `a`. By the law of sines and the
law of cosines, in any triangle the latter condition is equivalent to
`b^2 = a * (a + c)`.
-/

namespace Usa1991P1

snip begin

/-- Over `ℤ`: the obtuseness condition `a^2 + b^2 < c^2` together with the
angle-doubling condition `b^2 = a * (a + c)` implies `3 * a^2 < b^2`. -/
lemma obtuse_sq_aux {a b c : ℤ} (ha : 0 < a) (hc : 0 ≤ c)
    (hangle : b^2 = a * (a + c)) (hobt : a^2 + b^2 < c^2) :
    3 * a^2 < b^2 := by
  have ha2 : (0 : ℤ) < a^2 := by positivity
  have hac : (0 : ℤ) < a + c := by linarith
  have hb2 : (0 : ℤ) < b^2 := by rw [hangle]; exact mul_pos ha hac
  have h6 : a^4 + a^2 * b^2 < a^2 * c^2 := by
    have h := mul_pos (sub_pos.mpr hobt) ha2
    linarith
  have h5 : a^2 * b^2 = a^4 + a^3 * c := by rw [hangle]; ring
  have hb4 : b^4 = a^4 + 2 * a^3 * c + a^2 * c^2 := by
    rw [show b^4 = (b^2)^2 from by ring, hangle]; ring
  have h7 : 3 * a^2 * b^2 < b^4 := by linarith
  by_contra h
  push Not at h
  have h8 : b^4 ≤ 3 * a^2 * b^2 := by
    have h9 := mul_le_mul_of_nonneg_right h hb2.le
    linarith
  linarith

/-- Over `ℤ`: the triangle inequality `c < a + b` together with the
angle-doubling condition `b^2 = a * (a + c)` implies `b < 2 * a`. -/
lemma tri_sq_aux {a b c : ℤ} (ha : 0 < a) (_hb : 0 < b)
    (hangle : b^2 = a * (a + c)) (htri : c < a + b) :
    b < 2 * a := by
  have h1 : (0 : ℤ) < a * (a + b - c) := mul_pos ha (by linarith)
  have h2 : a * c = b^2 - a^2 := by linarith
  by_contra h
  push Not at h
  have h3 : (0 : ℤ) ≤ (b - 2 * a) * (a + b) :=
    mul_nonneg (sub_nonneg.mpr h) (by linarith)
  linarith

/-- Natural-number version of `obtuse_sq_aux`. -/
lemma obtuse_sq {a b c : ℕ} (ha : 0 < a) (hangle : b^2 = a * (a + c))
    (hobt : a^2 + b^2 < c^2) : 3 * a^2 < b^2 := by
  have h := obtuse_sq_aux (a := (a : ℤ)) (b := (b : ℤ)) (c := (c : ℤ))
    (by exact_mod_cast ha) (by positivity) (by exact_mod_cast hangle)
    (by exact_mod_cast hobt)
  exact_mod_cast h

/-- Natural-number version of `tri_sq_aux`. -/
lemma tri_sq {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hangle : b^2 = a * (a + c))
    (htri : c < a + b) : b < 2 * a := by
  have h := tri_sq_aux (a := (a : ℤ)) (b := (b : ℤ)) (c := (c : ℤ))
    (by exact_mod_cast ha) (by exact_mod_cast hb) (by exact_mod_cast hangle)
    (by exact_mod_cast htri)
  exact_mod_cast h

snip end

determine min_perimeter : ℕ := 77

problem usa1991_p1 :
    IsLeast {n : ℕ | ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ c < a + b ∧
        a^2 + b^2 < c^2 ∧ b^2 = a * (a + c) ∧ n = a + b + c} min_perimeter := by
  constructor
  · -- The triangle with sides 16, 28, 33 attains perimeter 77.
    show ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ c < a + b ∧
        a^2 + b^2 < c^2 ∧ b^2 = a * (a + c) ∧ min_perimeter = a + b + c
    exact ⟨16, 28, 33, by decide⟩
  · rw [mem_lowerBounds]
    rintro n ⟨a, b, c, ha, hab, hbc, htri, hobt, hangle, rfl⟩
    show (77 : ℕ) ≤ a + b + c
    by_contra hper
    push Not at hper
    have ha24 : a ≤ 24 := by omega
    have key1 : 3 * a^2 < b^2 := obtuse_sq ha hangle hobt
    have key2 : b < 2 * a := tri_sq ha (lt_trans ha hab) hangle htri
    clear hobt
    simp only [pow_two] at hangle key1
    interval_cases a <;> interval_cases b <;> omega

end Usa1991P1
