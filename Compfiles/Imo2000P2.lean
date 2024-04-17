/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra, .Inequality] }

/-!
# International Mathematical Olympiad 2000, Problem 2

Let a, b, c be positive real numbers such that abc = 1. Show that

    (a - 1 + 1/b)(b - 1 + 1/c)(c - 1 + 1/a) ≤ 1.
-/

namespace Imo2000P2

snip begin

lemma schur (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a^2 * b + a^2 * c + b^2 * a + b^2 * c + c^2 * a + c^2 * b ≤
    a^3 + b^3 + c^3 + 3 * a * b * c := by
  wlog Hcb : c ≤ b with h1
  · have h3 : b ≤ c := le_of_not_le Hcb
    linarith [h1 a c b ha hc hb h3]
  wlog Hba : b ≤ a with h2
  · have h4 : a ≤ b := le_of_not_le Hba
    obtain hca | hac : c ≤ a ∨ a ≤ c := le_total c a
    · have := h2 b a c hb ha hc hca h4
      linarith only [this]
    · have := h2 b c a hb hc ha hac Hcb
      linarith only [this]
  have h5 :=
    calc a * (a - b) * (a - c) + b * (b - a) * (b - c)
       = a * (a - b) * (a - c) - b * (a - b) * (b - c) := by ring
     _ = (a - b) * (a * (a - c)- b * (b - c)) := by ring

  have h6 : 0 ≤ (a - b) * (a * (a - c) - b * (b - c)) := by
    apply mul_nonneg
    · exact sub_nonneg_of_le Hba
    · rw [sub_nonneg]; nlinarith

  rw [← h5] at h6
  have h12 : 0 ≤ (c - a) * (c - b) := by nlinarith only [Hba, Hcb]
  have h13 : 0 ≤ c * (c - a) * (c - b) := by nlinarith only [hc, h12]
  linarith

lemma lemma1 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (-x + y + z) * (x - y + z) * (x + y - z) ≤ x * y * z := by
  linarith [schur x y z (le_of_lt hx) (le_of_lt hy) (le_of_lt hz)]

lemma lemma2 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b)
    (habc : a * b * c = 1) :
    ∃ x y z : ℝ, 0 < x ∧ 0 < y ∧ 0 < z ∧
                 a = x / y ∧ b = y / z ∧ c = z / x := by
  refine ⟨a, 1, (1/b), ha, zero_lt_one, ?_, ?_, ?_, ?_⟩
  · exact one_div_pos.mpr hb
  · exact (div_one a).symm
  · exact (one_div_one_div b).symm
  · field_simp; linarith

snip end

problem imo2000_p2 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    (a - 1 + 1 / b) * (b - 1 + 1 / c) * (c - 1 + 1 / a) ≤ 1 := by
  -- we follow the solution from
  -- https://web.evanchen.cc/exams/IMO-2000-notes.pdf

  -- Let a = x/y, b = y/z, c = z/x for x, y, z > 0.
  obtain ⟨x,y,z, hx, hy, hz, rfl, rfl, rfl⟩ := lemma2 a b c ha hb habc
  have h1 := lemma1 x y z hx hy hz
  have h2 : 0 < y * z * x := by positivity
  suffices H :
      (x - y + z) * (y - z + x) * (z - x + y) ≤ (y * z * x) by
    field_simp
    exact (div_le_one h2).mpr H
  linarith
