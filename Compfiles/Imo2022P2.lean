/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Positive.Field
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 2022, Problem 2

Let ℝ+ be the set of positive real numbers.
Determine all functions f: ℝ+ → ℝ+ such that
for each x ∈ ℝ+, there is exactly one y ∈ ℝ+
satisfying

  x·f(y) + y·f(x) ≤ 2
-/

namespace Imo2022P2

abbrev PosReal : Type := { x : ℝ // 0 < x }

notation "ℝ+" => PosReal

snip begin

lemma lemma0 {α : Type} {p : α → α → Prop}
    (h1 : ∀ x, ∃! y, p x y) (h2 : ∀ x y, p x y ↔ p y x) :
    ∀ x, Classical.choose (h1 (Classical.choose (h1 x).exists)).exists = x := by
  intro x
  obtain ⟨y, h1e, h1u⟩ := h1 x
  have h2' : Classical.choose (h1 x).exists = y :=
    h1u _ (Classical.choose_spec (h1 x).exists)
  rw [h2']

  obtain ⟨w, h1e', h1u'⟩ := h1 y
  have h4 := Classical.choose_spec (h1 y).exists
  have hxw : x = w := by
    apply h1u'
    rw [h2]
    exact h1e
  rw [hxw]
  exact h1u' _ h4

lemma amgm (a b : ℝ+) : ⟨2, two_pos⟩ ≤ a / b + b / a := by
  change 2 ≤ a.val/b.val + b.val/a.val
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  dsimp only
  field_simp
  have h1 : 0 < b * a := Real.mul_pos hb ha
  suffices H : 2 * (b * a) ≤ a * a + b * b by exact (le_div_iff h1).mpr H
  suffices H : 0 ≤ (a - b)^2 by linarith
  exact sq_nonneg (a - b)

lemma lemma1 (a : ℝ+) : a + a = ⟨2, two_pos⟩ * a := by
  obtain ⟨a, ha⟩ := a
  apply Subtype.val_injective
  dsimp
  exact (two_mul a).symm

snip end

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
        simp only [one_div, mul_right_inv]
        exact Eq.le h
      norm_num [Subtype.ext_iff]
    · intro y hxy
      change (x * (1 / y) + y * (1 / x)).val ≤ _  at hxy
      obtain ⟨x, hx⟩ := x
      obtain ⟨y, hy⟩ := y
      simp only [Positive.coe_add, Positive.val_mul, one_div, Positive.coe_inv] at hxy
      rw [Subtype.mk_eq_mk]
      have hxyp : 0 < y * x := Real.mul_pos hy hx
      field_simp at hxy
      have h1 : (x * x + y * y) ≤ 2 * (y * x) := (div_le_iff hxyp).mp hxy
      nlinarith
  · intro hf
    rw [Set.mem_singleton_iff]
    -- We follow Evan Chen's writeup: https://web.evanchen.cc/exams/IMO-2022-notes.pdf
    let friend : ℝ+ → ℝ+ := fun x ↦ Classical.choose (hf x).exists
    have h10 : ∀ x y, x * f y + y * f x ≤ ⟨2, two_pos⟩ ↔
                      y * f x + x * f y ≤ ⟨2, two_pos⟩ := by
      intro x y
      constructor <;> intro h <;> rwa [add_comm]
    have h11 : ∀ x, x * f (friend x) + friend x * f x ≤ ⟨2, two_pos⟩ :=
      fun  x ↦ Classical.choose_spec (hf x).exists

    have h0 : ∀ x, friend (friend x) = x := fun x ↦ by
      simp only [friend]
      exact lemma0 hf h10 x
    have h1 : ∀ x, friend x = x := fun x ↦ by
      by_contra! H
      have h2 : ⟨2, two_pos⟩ < x * f x + x * f x := by
        obtain ⟨y, _, hy2⟩ := hf x
        by_contra! H2
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
      have h7 : 1 / friend x < f (friend x) := by
        have h8 : ⟨2, two_pos⟩ < (friend x) * f (friend x) + (friend x) * f (friend x) := by
          obtain ⟨y, _, hy2⟩ := hf (friend x)
          by_contra! H2
          have h3 := hy2 (friend x) H2
          have h4 : y = (friend (friend x)) := by
            have h5 := Classical.choose_spec (hf (friend x)).exists
            exact (hy2 (friend (friend x)) h5).symm
          rw [h0] at h4
          rw [h4] at h3
          exact H h3
        have h9 : 1 < friend x * f (friend x) := by
          change 2 < (friend x * f (friend x)).val + (friend x * f (friend x)).val at h8
          change 1 < (friend x * f (friend x)).val
          linarith
        exact div_lt_iff_lt_mul'.mpr h9
      have := calc ⟨2, two_pos⟩ ≤ x / friend x + friend x / x := amgm x (friend x)
                   _ = x * (1 / friend x) + friend x * (1 / x) := by
                       rw [mul_one_div, add_left_cancel_iff, mul_one_div]
                   _ < x * f (friend x) + friend x * f x := by gcongr
                   _ ≤ ⟨2, two_pos⟩ := h11 _
      exact LT.lt.false this
    have hf' : ∀ x, f x ≤ 1 / x := fun x ↦ by
      have h12 := h11 x
      rw [h1] at h12
      suffices H : x * f x ≤ 1 by exact le_div_iff_mul_le'.mpr H
      have h14 : (⟨2, two_pos⟩ : ℝ+) = ⟨2, two_pos⟩ * 1 := self_eq_mul_right.mpr rfl
      have h13 : x * f x + x * f x = ⟨2, two_pos⟩ * (x * f x) := lemma1 _
      rw [h14, h13] at h12
      exact (mul_le_mul_iff_left _).mp h12
    have hf1' : ∀ x y, x ≠ y → ⟨2, two_pos⟩ < x * f y + y * f x := fun x y hxy ↦ by
      by_contra! H
      obtain ⟨y1, _, hy2⟩ := hf x
      have h15 := hy2 (friend x) (h11 x)
      rw [← hy2 y H] at h15
      rw [← h15] at hxy
      exact hxy (h1 x).symm
    funext x
    by_contra! H
    have H' : x ≠ 1 / f x := fun hxfx ↦ by
      nth_rw 2 [hxfx] at H
      rw [one_div_one_div] at H
      exact H rfl
    have h17 := hf1' x (1 / f x) H'
    rw [div_mul_cancel'] at h17
    have h19 := hf' (1 / f x)
    rw [one_div_one_div] at h19
    have h20 := calc ⟨2, two_pos⟩ < x * f (1 / f x) + 1 := h17
                 _ ≤ x * f x + 1 := by gcongr
                 _ ≤ x * (1 / x) + 1 := by have := hf' x; gcongr
                 _ = 1 + 1 := by rw [add_right_cancel_iff, mul_one_div, div_eq_one]
                 _ = ⟨2, two_pos⟩ := by apply Subtype.val_injective; norm_num
    exact LT.lt.false h20
