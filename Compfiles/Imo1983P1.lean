/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Algebra.Order.Positive.Field
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1983, Problem 1

Let ℝ+ be the set of positive real numbers.

Determine all functions f : ℝ+ → ℝ+ which satisfy:
 i) f(xf(y)) = yf(x) for all x y ∈ ℝ+.
 ii) f(x) → 0 as x → ∞.
-/

namespace Imo1983P1

abbrev PosReal : Type := { x : ℝ // 0 < x }

notation "ℝ+" => PosReal

determine SolutionSet : Set (ℝ+ → ℝ+) := { fun x ↦ 1 / x }

problem imo1983_p1 (f : ℝ+ → ℝ+) :
    f ∈ SolutionSet ↔
    ((∀ x y, f (x * f y) = y * f x) ∧
     (∀ ε, ∃ x, ∀ y, x < y → f y < ε)) := by
  -- following the informal solution at
  -- https://artofproblemsolving.com/wiki/index.php/1983_IMO_Problems/Problem_1
  constructor
  · rintro rfl
    constructor
    · intro x y; field_simp
    · intro x
      use 1/x
      intro y hy
      dsimp
      exact div_lt_comm.mp hy
  rintro ⟨hi, hii⟩
  rw [Set.mem_singleton_iff]
  have h1 : f 1 = 1 := by
    have h2 := hi 1 1
    have h3 := hi 1 (f 1)
    simp only [one_mul] at h2 h3
    rw [h2, h2, self_eq_mul_right] at h3
    exact h3
  suffices h3 : ∀ a, f a = a → a = 1 by
    funext x
    exact eq_one_div_of_mul_eq_one_right (h3 (x * f x) (hi x x))
  intro a ha
  by_contra! H
  have hi1 : ∀ x, f (x * a) = a * f x := fun x ↦ by
    have := hi x a
    rwa [ha] at this
  have h4 : f (1 / a) = 1 / a := by
    have h5 := hi1 (1 / a)
    rw [one_div, mul_left_inv, h1, ← one_div] at h5
    replace h5 := div_eq_iff_eq_mul'.mpr h5
    exact h5.symm
  wlog H1 : 1 < a with h
  · refine h f hi hii h1 (1/a) h4 ?_ ?_ ?_ ?_
    · exact div_ne_one.mpr (Ne.symm H)
    · intro x
      have h7 := hi x (1/a)
      rwa [h4] at h7
    · simp [ha]
    · have h6 : a < 1 := by
        push_neg at H1
        exact lt_of_le_of_ne H1 H
      exact one_lt_div'.mpr h6
  have h8 : f (a^2) = a^2 := by
    have h9 := hi1 a
    rw [ha] at h9
    rwa [←sq] at h9
  have hi3 : ∀ m, f (a^m) = a^m := by
    intro m
    induction' m with pm ih
    · simp [h1]
    · rw [pow_succ]
      nth_rewrite 1 [mul_comm]
      rw [hi1, ih]

  -- a > 1, so a^m approaches ∞ as m → ∞
  -- but a^m = f (a^m), so that contracts ii
  obtain ⟨x0, hx0⟩ := hii 1
  have h12 : ∃ m, x0 < a^m := by
    -- 1 + (a-1) * m ≤ (1 + (a-1)) ^ m
    -- suffices to choose k such that
    -- x0 < 1 + (a-1) * m
    -- suffices to choose k such that
    -- x0 < (a-1) * m
    -- x0 / (a - 1) < m
    -- choose m = Ceil((x0 / (a - 1))

    obtain ⟨x, hx⟩ := x0
    obtain ⟨a, ha0⟩ := a

    use Nat.ceil (x / (a - 1))

    change x < a ^ ⌈ _⌉₊
    change 1 < a at H1
    clear f hi hii h1 hx0 ha H hi1 h4 hi3 h8
    nth_rewrite 1 [show a = 1 + (a - 1) by ring]
    have h20 : 1 + ((⌈(x / (a - 1))⌉₊:ℕ):ℝ) * (a - 1) ≤
             (1 + (a - 1)) ^ ⌈x / (a - 1)⌉₊
           := by
      have h30 : -2 ≤ a - 1 := by linarith
      exact one_add_mul_le_pow h30 _

    suffices x < 1 + (((⌈(x / (a - 1))⌉₊):ℕ):ℝ) * (a - 1)
      from gt_of_ge_of_gt h20 this
    push_cast
    have h21 := Nat.le_ceil (x / (a - 1))
    suffices x < 1 + (x / (a - 1)) * (a - 1) by
      clear h20
      have h24 : 0 < a - 1 := sub_pos.mpr H1
      have h25 := (mul_le_mul_iff_of_pos_right h24).mpr h21
      exact lt_add_of_lt_add_left this h25

    have : a - 1 ≠ 0 := by linarith
    simp [this]

  obtain ⟨m0, hm1⟩ := h12
  have h13 := hx0 (a ^ m0) hm1
  rw [hi3] at h13
  have h14 : 1 ≤ a ^ m0 :=
    one_le_pow_of_one_le' (le_of_lt H1) m0
  rw [lt_iff_not_le] at h13
  contradiction
