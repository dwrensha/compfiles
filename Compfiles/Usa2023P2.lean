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
# USA Mathematical Olympiad 2023, Problem 2

Let ℝ+ be the set of positive real numbers.
Find all functions f: ℝ+ → ℝ+ that satisfy the equation

  f(x⬝y + f(x)) = x⬝f(y) + 2

for all x,y ∈ ℝ+.
-/

namespace Usa2023P2

abbrev PosReal : Type := { x : ℝ // 0 < x }

notation "ℝ+" => PosReal

snip begin

-- Should this be in mathlib as `Positive.val_div`?
lemma val_div (a b : ℝ+) : (a / b).val = a.val / b.val := by rfl

lemma lemma_1 (a b c : ℝ+) : (a + b)/c = a/c + b/c := by
  rw [division_def, add_mul, ←division_def, ←division_def]

lemma lemma_3 {a b c : ℝ+} (h : a = b + c) : c < a := by
  rw [h]
  obtain ⟨b, hb⟩ := b
  obtain ⟨c, hc⟩ := c
  rw [←Subtype.coe_lt_coe, Positive.coe_add]
  exact lt_add_of_pos_left c hb

snip end

determine solution_set : Set (ℝ+ → ℝ+) := { fun x ↦ x + 1 }

problem usa2023_p2 (f : ℝ+ → ℝ+) :
    f ∈ solution_set ↔
    ∀ x y, f (x * y + (f x)) = x * (f y) + ⟨2, two_pos⟩ := by
  constructor
  · intro hf
    rw [solution_set, Set.mem_singleton_iff] at hf
    intro x y
    rw [hf]
    dsimp only
    rw [mul_add, ←add_assoc (x*y), mul_one, add_assoc (x * y + x)]
    congr
    rw [Subtype.mk_eq_mk]
    norm_num
  · -- proof outline megarnie on AOPS:
    -- https://artofproblemsolving.com/community/c5h3038298p27349430

    -- It suffices to show that f must be a linear function.
    intro P
    suffices h : ∃ a b : ℝ, 0 < a ∧ ∀ x, (f x).val = a * x.val + b by
      rw [solution_set, Set.mem_singleton_iff]
      obtain ⟨a, b, ha, hab⟩ := h
      funext x
      rw [←Subtype.coe_inj]

      suffices h : a = 1 ∧ b = 1 by simp [hab, h]

      have P1 : ∀ x : ℝ+, a^2 * x.val + a * b + b = b * x.val + 2 := by
        intro x
        have P2 := P x 1
        simp only at P2
        rw [←Subtype.coe_inj] at P2
        simp only [mul_one, Positive.coe_add, Positive.val_mul, hab, Positive.val_one] at P2
        linarith

      have P3 : ∀ x : ℝ, 0 < x → a^2 * x + a * b + b = b * x + 2 := by
        intro x hx
        have hp1 := P1 ⟨x, hx⟩
        simp only [Positive.coe_add, Positive.val_mul, Positive.val_pow] at hp1
        exact hp1

      have hp1 := P3 1 zero_lt_one
      have hp2 := P3 2 zero_lt_two

      have h0 : a^2 = b := by linear_combination hp2 - hp1

      rw [←h0] at hp1 hp2
      have h1 : a = 1 := by nlinarith
      rw [h1, sq, mul_one] at h0
      exact ⟨h1, h0.symm⟩

    let c := f 1

    have h6 : ∀ y, f (y + c) = f y + ⟨2, two_pos⟩ := by
      intro y
      have h7 := P 1 y
      rw [one_mul, one_mul] at h7
      exact h7

    have h5 : ∀ x, f (x + f x) = x * c + ⟨2, two_pos⟩ := by
      intro x
      have h7 := P x 1
      rw [mul_one] at h7
      exact h7

    have h7 : ∀ x, f (x + f x) = x * f (c / x + 1) := by
      intro x
      have h8 := P x (c / x + 1)
      have h9 : x * (c / x + 1) + f x = x + f x + c := by
        rw [mul_add, mul_div_cancel, mul_one]
        ac_rfl
      rw [h9] at h8; clear h9
      rw [h6 (x + f x), add_left_inj] at h8
      rw [h8]

    have h8 : ∀ x, f (c / x + 1) = c + ⟨2, two_pos⟩ / x := by
      intro x
      have h9 := h7 x
      rw [h5 x] at h9
      apply_fun (· / x) at h9
      rw [mul_div_cancel_left] at h9
      rw [← h9]; clear h9
      rw [lemma_1, mul_div_cancel_left]

    have h9 : ∀ x, f (x + 1) = c + ⟨2,two_pos⟩ * x / c := by
      intro x
      have h10 := h8 (c/x)
      rwa [div_div_cancel, div_div_eq_mul_div] at h10

    have h10 : 1 ≤ c := by
      by_contra! H
      have h11 : 0 < 1 - (f 1).val := Iff.mpr sub_pos H
      have h12 := P 1 ⟨1 - (f 1).val, h11⟩
      rw [one_mul, one_mul] at h12
      have h13 : ⟨1 - (f 1).val, h11⟩ + f 1 = 1 := by
        rw [←Subtype.coe_inj]; simp only [Positive.coe_add, sub_add_cancel, Positive.val_one]
      rw [h13] at h12; clear h13
      have h14 : ⟨2, two_pos⟩ < f 1 := lemma_3 h12
      have h15 : (1:ℝ+) < ⟨2, two_pos⟩ := by rw [Subtype.mk_lt_mk]; exact one_lt_two
      exact ((H.trans h15).trans h14).false

    have h11 : ∀ x : ℝ+, 0 < (x + c).val - 1 := by
      intro x
      obtain ⟨c, hc⟩ := c
      obtain ⟨x, hx⟩ := x
      change 1 ≤ c at h10
      simp only [Positive.coe_add, sub_pos]
      exact lt_add_of_pos_of_le hx h10

    have h12 : ∀ x, c + ⟨2,two_pos⟩ * ⟨(x + c).val - 1, h11 _⟩ / c = f x + ⟨2, two_pos⟩ := by
      intro x
      rw [← h6]
      symm
      have h20 := h9 ⟨(x + c).val - 1, h11 _⟩
      have h21 : (⟨(x + c).val - 1, h11 _⟩ : ℝ+) + 1 = x + c := by
        obtain ⟨x, hx⟩ := x
        obtain ⟨cc, hcc⟩ := c
        rw [←Subtype.coe_inj]
        simp
      rw [h21] at h20
      exact h20

    refine' ⟨2 / c.val, c.val - 2 / c.val, div_pos two_pos c.prop, _⟩
    intro x

    have h15 := h12 x
    rw [←Subtype.coe_inj] at h15
    rw [Positive.coe_add] at h15
    rw [val_div, Positive.val_mul, @Subtype.coe_mk _ _ 2] at h15
    rw [Subtype.coe_mk]
    obtain ⟨x, hx⟩ := x
    simp only [Positive.coe_add] at h15
    simp only
    obtain ⟨cc, rfl⟩ : ∃ cc, cc = f 1 := exists_eq
    rw [mul_sub, mul_add, mul_one, sub_div, add_div] at h15
    have h18 : (f 1).val ≠ 0 := ne_of_gt (f 1).prop
    rw [mul_div_cancel_right₀ 2 h18] at h15
    symm
    linear_combination h15
