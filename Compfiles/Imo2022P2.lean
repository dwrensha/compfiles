/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Positive.Field
import Mathlib.Tactic

import Compfiles.Meta.ProblemExtraction

problem_file

/-!
# International Mathematical Olympiad 2022, Problem 2

Let ℝ+ be the set of positive real numbers.
Determine all functions f: ℝ+ → ℝ+ such that
for each x ∈ ℝ+, there is exactly one y ∈ ℝ+
satisfying

  x·f(y) + y·f(x) ≤ 2
-/

namespace Imo2022P2

snip begin

lemma lemma1 {α : Type} {p : α → α → Prop}
    (h1 : ∀ x, ∃! y, p x y) (h2 : ∀ y, ∃! x, p x y) :
    ∀ x, Classical.choose (h1 (Classical.choose (h1 x).exists)).exists = x := by
  intro x
  obtain ⟨y, h1e, h1u⟩ := h1 x
  have h2' : Classical.choose (h1 x).exists = y := by
    apply h1u
    exact Classical.choose_spec (h1 x).exists

  rw [h2']
  obtain ⟨w, h1e', h1u'⟩ := h1 y
  obtain ⟨z, h3e, h3u⟩ := h2 y
  dsimp at h3u h1u'
  have hxz : x = z := h3u x h1e
  rw [←hxz] at h3u
  apply h3u

  have hxw : x = w := by
    apply h1u'
    have := Classical.choose_spec (h1 y).exists
    sorry
  have := Classical.choose_spec (h1 y).exists
  sorry

snip end

abbrev PosReal : Type := { x : ℝ // 0 < x }

notation "ℝ+" => PosReal

determine solution_set : Set (ℝ+ → ℝ+) := { fun x ↦ 1 / x }

problem imo2022_p2 (f : ℝ+ → ℝ+) :
    f ∈ solution_set ↔
    ∀ x, ∃! y, x * f y + y * f x ≤ ⟨2, two_pos⟩ := by
  constructor
  · intro hf
    simp only [Set.mem_singleton_iff] at hf
    rw [hf] at *; clear hf
    intro x
    use x
    constructor
    · suffices h : (1:ℝ+) + 1 = ⟨2, two_pos⟩ by
        simp only [one_div, mul_right_inv, ge_iff_le]
        exact Eq.le h
      norm_num [Subtype.ext_iff]
    · intro y hxy
      change (x * (1 / y) + y * (1 / x)).val ≤ _  at hxy
      obtain ⟨x, hx⟩ := x
      obtain ⟨y, hy⟩ := y
      simp only [Positive.coe_add, Positive.val_mul, one_div, Positive.coe_inv] at hxy
      rw [Subtype.mk_eq_mk]
      have hxyp : 0 < y * x := Real.mul_pos hy hx
      have hxynz : y * x ≠ 0 := ne_of_gt hxyp
      field_simp at hxy
      have h1 : (x * x + y * y) ≤ 2 * (y * x) := (div_le_iff hxyp).mp hxy
      nlinarith
  · intro hf
    rw [Set.mem_singleton_iff]
    -- We follow Evan Chen's writeup: https://web.evanchen.cc/exams/IMO-2022-notes.pdf
    let friend : ℝ+ → ℝ+ := fun x ↦ Classical.choose (hf x).exists
    have h10 : ∀ y, ∃! x, x * f y + y * f x ≤ ⟨2, two_pos⟩ := by
      intro y
      obtain ⟨x, hx1, hx2⟩ := hf y
      rw [add_comm] at hx1
      refine' ⟨x, hx1, _⟩
      intro z hz
      have hz1 := hx2 z
      dsimp only at hz1
      rw [add_comm] at hz1
      exact hz1 hz
    have h0 : ∀ x, friend (friend x) = x := fun x ↦ by
      simp only [friend]
      exact lemma1 hf h10 x
    have h1 : ∀ x, friend x = x := fun x ↦ by
      by_contra' H
      have h2 : ⟨2, two_pos⟩ < x * f x + x * f x := by
        obtain ⟨y, hy1, hy2⟩ := hf x
        by_contra' H2
        have h3 := hy2 x H2
        have h4 : y = friend x := by
          have h5 := Classical.choose_spec (hf x).exists
          exact (hy2 (friend x) h5).symm
        rw [h4] at h3
        exact H h3.symm
      have h6' : 1 < x * f x := by
        change 2 < (x * f x).val + (x * f x).val at h2
        change 1 < (x * f x).val
        linarith
      have h6 : 1 / x < f x := div_lt_iff_lt_mul'.mpr h6'
      sorry
    sorry
