/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhiyi Luo
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Algebra.Order.Positive.Field
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 2022, Problem 3

Let ℝ+ be the set of all positive real numbers. Find all
functions ℝ+ → ℝ+ such that for all x, y ∈ ℝ+ we have

   f(x) = f(f(f(x)) + y) + f(xf(y))f(x+y).
-/

namespace Usa2022P3

abbrev PosReal : Type := { x : ℝ // 0 < x }
notation "ℝ+" => PosReal

snip begin

lemma PosReal.lt_add (a b : ℝ+) : a < a + b := by
  obtain ⟨b, bpos⟩ := b
  apply Subtype.mk_lt_mk.mpr
  linarith

@[simp]
theorem PosReal.coe_mul (a b : ℝ+) : (a * b).val = a.val * b.val := rfl

@[simp]
theorem PosReal.coe_add (a b : ℝ+) : (a + b).val = a.val + b.val := rfl

@[simp]
theorem PosReal.coe_div (a b : ℝ+) : (a / b).val = a.val / b.val := rfl

-- noncomputable instance PosReal.instSub : Sub ℝ+ where
--   sub := sorry

-- lemma PosReal.add_sub_cancel {a b : ℝ+} (h : a < b): a + (b - a) = b := sorry

snip end

determine solution_set : Set (ℝ+ → ℝ+) :=
  { f : ℝ+ → ℝ+ | ∃ c : ℝ+, f = fun x ↦ c / x }

problem usa2022_p3 (f : ℝ+ → ℝ+) :
  f ∈ solution_set ↔
    (∀ x y : ℝ+, f x = f (f (f x) + y) + f (x * f y) * f (x + y)) := by
  -- https://artofproblemsolving.com/community/c5h2808852p24774911

  constructor
  · rintro ⟨c, rfl⟩ x y
    obtain ⟨c, cpos⟩ := c
    obtain ⟨x, xpos⟩ := x
    obtain ⟨y, ypos⟩ := y
    apply Subtype.mk_eq_mk.mpr
    simp
    field_simp
    ring

  intro hf
  change ∀ x y : ℝ+, f x = f (f^[2] x + y) + f (x * f y) * f (x + y) at hf
  have h1 : ∀ x y : ℝ+, f x > f (f^[2] x + y) := by
    intro x y
    rw [hf x y]
    exact PosReal.lt_add _ _

  have h2 : ∀ c x : ℝ+, c > f^[2] x → f c < f x := by
    intro c x hcx

    -- have := h1 x (c - f^[2] x)
    -- rw [PosReal.add_sub_cancel h] at this

    let x' : ℝ+ := ⟨c - f^[2] x, sub_pos_of_lt hcx⟩
    have hx' : f^[2] x + x' = c := by
      apply Subtype.mk_eq_mk.mpr
      simp [x']
    have h := h1 x x'
    rw [hx'] at h

    exact h

  have h3 : ∀ x : ℝ+, f^[2] x ≥ x := by
    by_contra! h
    rcases h with ⟨x, hx⟩
    have : f x < f x := h2 x x hx
    exact lt_irrefl (f x) this

  have h4 : ∀ c x : ℝ+, f c ≥ f x → c ≤ f^[2] x := by
    intro c x
    contrapose!
    exact h2 c x

  have h5 : ∀ x : ℝ+, f^[2] x = f^[4] x := by
    intro x
    have : f^[5] x ≥ f x := calc
      f^[5] x ≥ f^[3] x := h3 _
      _ ≥ f x := h3 _
    have : f^[4] x ≤ f^[2] x := h4 _ _ this
    exact eq_of_le_of_le (h3 _) this

  have h6 : f.Injective := by
    intro a b h
    wlog hab : b > a
    · push_neg at hab
      rcases lt_or_eq_of_le hab with hab | hab
      · rw [this f hf h1 h2 h3 h4 h5 h.symm hab]
      · rw [hab]
    have (n : ℝ+) : ∀ y : ℝ+, f^[3] n = f (f^[2] n + y) * (1 + f (f^[2] n * f y)) := by
      intro y
      calc f^[3] n
        _ = f (f^[4] n + y) + f (f^[2] n * f y) * f (f^[2] n + y) := hf (f (f n)) y
        _ = f (f^[2] n + y) * (1 + f (f^[2] n * f y)) := by simp [← h5, mul_add, mul_comm]
    have (n : ℝ+) : f (f^[2] n + a) = f (f^[2] n + b) := by
      have := (this n a).symm.trans (this n b)
      rw [h] at this
      apply mul_right_cancel at this
      exact this
    have (n : ℝ+) : f (n + a) = f (n + b) := by
      have hh := (hf n a).symm.trans (hf n b)
      rw [this, h] at hh
      apply add_left_cancel at hh
      apply mul_left_cancel at hh
      exact hh

    let c : ℝ := b.val - a.val
    have cpos : c > 0 := sub_pos_of_lt hab
    have f_periodic : ∀ x > a, f x = f (x + (⟨c, cpos⟩)) := by
      rintro ⟨x, xpos⟩ hx
      let x' : ℝ+ := ⟨x - a.val, sub_pos_of_lt hx⟩
      simp [c]
      have eq1 : ⟨x, xpos⟩ = x' + a := by
        simp only [x']
        apply Subtype.mk_eq_mk.mpr
        simp
      have eq2 : ⟨x, xpos⟩ + ⟨c, cpos⟩ = x' + b := by
        simp only [c, x']
        apply Subtype.mk_eq_mk.mpr
        simp
        linarith
      nth_rw 1 [eq1, eq2]
      exact this x'

    have : ∀ n : ℕ, f (a + a) = f (a + a + ⟨↑(n + 1) • c, nsmul_pos cpos n.succ_ne_zero⟩)
      := by
      intro n
      induction' n with n ih
      · simp
        exact f_periodic (a + a) (PosReal.lt_add _ _)
      have :
        (⟨(n + 1 + 1) • c, nsmul_pos cpos (n + 1).succ_ne_zero⟩ : ℝ+)
      = (⟨(n + 1) • c, nsmul_pos cpos n.succ_ne_zero⟩ : ℝ+) + (⟨c, cpos⟩ : ℝ+) := rfl
      rw [ih, this]
      simp only [← add_assoc]
      apply f_periodic _
      rw [add_assoc]
      exact PosReal.lt_add _ _

    have : ∃ b : ℝ+, f (a + a) = f (a + a + b) ∧ a + a + b > f^[2] (a + a) := by
      suffices
        h : ∃ n : ℕ, a + a + ⟨(n + 1) • c, nsmul_pos cpos n.succ_ne_zero⟩ > f^[2] (a + a) by
        rcases h with ⟨n, hn⟩
        use ⟨(n + 1) • c, nsmul_pos cpos n.succ_ne_zero⟩
        exact ⟨this n, hn⟩
      have : ∃ n : ℕ, n • c ≥ f^[2] (a + a) - (a + a) := Archimedean.arch _ cpos
      rcases this with ⟨n, hn⟩
      have : (n + 1) • c > (f^[2] (a + a) - (a + a) : ℝ) := calc
        (n + 1) • c = n • c + c := rfl
        _ > ((f^[2] (a + a)) - (a + a) : ℝ) + 0 := add_lt_add_of_le_of_lt hn cpos
        _ = f^[2] (a + a) - (a + a) := by rw [add_zero]
      use n + 1
      apply Subtype.mk_lt_mk.mpr
      simp
      simp at this
      linarith

    rcases this with ⟨b, ⟨hb1, hb2⟩⟩
    have : f (a + a + b) < f (a + a + b) := by
      nth_rw 2 [← hb1]
      exact h2 (a + a + b) (a + a) hb2
    apply Subtype.mk_lt_mk.mp at this
    linarith

  have h7 : ∀ x : ℝ+, f^[2] x = x := by
    intro x
    apply h6
    apply h6
    change f^[4] x = f^[2] x
    rw [h5]

  let c := f 1
  have h8 : ∀ x y : ℝ+, f x = f (x + y) * (1 + f (x * f y)) := by
    intro x y
    simp only [mul_add, mul_comm, mul_one, h7 x, hf x y]

  have h9 : ∀ x > 1, f x = c / x := by
    intro x hx

    -- have := h8 1 (x - 1)
    -- simp [PosReal.add_sub_cancel hx] at this
    -- change c = f x * (1 + f^[2] (x - 1)) at this
    -- simp [PosReal.add_sub_cancel hx, h7] at this

    let x' : ℝ+ := ⟨x.val - 1, sub_pos_of_lt hx⟩
    have hx' : 1 + x' = x := by
      apply Subtype.mk_eq_mk.mpr
      simp
    have h := h8 1 x'
    simp [hx'] at h
    change c = f x * (1 + f^[2] x') at h
    simp [hx', h7] at h

    rw [h]
    nth_rw 1 [mul_div_cancel_right]

  have h10 : ∀ x < c, f x = c / x := by
    intro x hx
    have : c / x > 1 := one_lt_div'.mpr hx
    have : f (c / x) = x := by
      rw [h9 (c / x) this]
      field_simp
    calc f x
      _ = f (f (c / x)) := by rw [this]
      _ = c / x := h7 _

  have h11 : ∀ x ≤ 1, f x = c / x := by
    intro x hx
    let two : ℝ+ := ⟨2, by norm_num⟩
    rw [h8 x two]

    have : two > 1 := by
      apply Subtype.coe_lt_coe.mp
      norm_num
    rw [h9 two this]

    have : x + two > 1 := by
      apply Subtype.coe_lt_coe.mp
      obtain ⟨x, xpos⟩ := x
      simp
      linarith
    rw [h9 (x + two) this]

    have : x * (c / two) < c := by
      apply Subtype.coe_lt_coe.mp
      obtain ⟨x, xpos⟩ := x
      obtain ⟨c, cpos⟩ := c
      simp
      change x ≤ 1 at hx
      calc x * (c / 2)
        _ ≤ c / 2 := by
          apply (mul_le_iff_le_one_left (by linarith [cpos])).mpr
          exact hx
        _ < c := by linarith
    rw [h10 (x * (c / two)) this]

    apply Subtype.mk_eq_mk.mpr
    obtain ⟨x, xpos⟩ := x
    obtain ⟨c, cpos⟩ := c
    simp
    field_simp
    ring

  use c
  funext x

  rcases le_or_lt x 1 with hx | hx
  · exact h11 x hx
  · exact h9 x hx


end Usa2022P3
