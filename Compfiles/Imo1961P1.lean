/-
Copyright (c) 2020 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Roozbeh Yousefzadeh
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1961, Problem 1.

Given constants a and b, solve the system of equations

             x + y + z = a
          x² + y² + z² = b²
                    xy = z²

for x,y,z. Give the conditions that a and b must satisfy so that
the solutions x,y,z are distinct positive numbers.
-/

namespace Imo1961P1

abbrev IsSolution (a b x y z : ℝ) : Prop :=
    x + y + z = a ∧
    x^2 + y^2 + z^2 = b^2 ∧
    x * y = z^2

determine xyz_of_ab (a b : ℝ) : Set (ℝ × ℝ × ℝ) :=
  { p | let ⟨x,y,z⟩ := p
        (a ≠ 0 ∧
        z = (a^2 - b^2) / (2 * a) ∧
        ∀ m, (m - x) * (m - y) =
              m^2 - (a^2 + b^2) / (2 * a) * m + ((a^2 - b^2) / (2 * a))^2) ∨ (a = 0 ∧ b = 0 ∧ x  = 0 ∧ y = 0 ∧ z = 0) }

determine ab_that_make_xyz_positive_distinct : Set (ℝ × ℝ) :=
  { q | let ⟨a,b⟩ := q
        0 < a ∧ b^2 < a^2 ∧ a^2 < 3 * b ^ 2 }

snip begin

lemma aux_1
  (x y z a b : ℝ)
  (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
  (h₁ : [x, y, z].Nodup)
  (h₂ : x + y + z = a)
  (h₃ : x^2 + y^2 + z^2 = b^2)
  (h₄ : x * y = z^2) :
  0 < a ∧ b^2 < a^2 ∧ a^2 < 3 * b^2 := by
  have ha: 0 < a := by linarith
  refine ⟨ha,?_⟩
  have h₇: (x + y + z) * (x + y - z) = b ^ 2 := by
    rw [← sq_sub_sq, ← h₄, add_sq]
    linarith
  have h₈: (x + y - z) = b ^ 2 / a := by
    rw [h₂] at h₇
    refine (eq_div_iff ?_).mpr ?_
    · exact Ne.symm (ne_of_lt ha)
    · rw [mul_comm] at h₇
      exact h₇
  have h₉: z = (a ^ 2 - b ^ 2) / (2 * a) := by
    have g₀: x + y = (a + b ^ 2 / a) / 2 := by linarith
    rw [g₀, add_div, div_div] at h₂
    rw [sub_div, mul_comm 2 a, ← div_div, pow_two, mul_self_div_self]
    linarith
  have h₁₀: b ^ 2 < a ^ 2 := by
    apply and_assoc.mpr at h₀
    obtain ⟨-, hz⟩ := h₀
    rw [h₉] at hz
    apply div_pos_iff.mp at hz
    refine lt_of_sub_pos ?_
    obtain hzc | hzf := hz
    · exact hzc.1
    · exfalso
      linarith
  have h₁₁: y ^ 2 + (-(a ^ 2 + b ^ 2) / (2 * a)) * y + ((a ^ 2 - b ^ 2) / (2 * a)) ^ 2 = 0 := by
    have g₀: x + y = (a + b ^ 2 / a) / 2 := by linarith
    rw [add_div, div_div] at g₀
    have g₁: x = a / 2 + b ^ 2 / (a * 2) - y := by linarith
    rw [g₁, h₉, sub_mul, add_mul, ← pow_two y] at h₄
    rw [neg_add', sub_div, neg_div, pow_two a, mul_div_mul_right a 2 (by positivity), sub_mul, neg_mul]
    rw [add_sub_assoc', ← sub_eq_add_neg, add_comm]
    refine add_eq_of_eq_sub ?_
    rw [zero_sub, ← pow_two a, ← h₄]
    ring_nf
  let aq : ℝ := 1
  let bq : ℝ := (-(a ^ 2 + b ^ 2) / (2 * a))
  let cq : ℝ := ((a ^ 2 - b ^ 2) / (2 * a)) ^ 2
  have haq : aq = 1 := by rfl
  have hbq : bq = (-(a ^ 2 + b ^ 2) / (2 * a)) := by rfl
  have hcq : cq = ((a ^ 2 - b ^ 2) / (2 * a)) ^ 2 := by rfl
  have h₁₂: aq * y ^ 2 + bq * y + cq = 0 := by
    rw [one_mul]
    exact h₁₁
  rw [pow_two] at h₁₂
  have h₁₃: (2 * aq * y + bq) ^ 2 = bq ^ 2 - 4 * aq * cq := by
    rw [add_sq]
    have g₀: (2 * aq * y) ^ 2 + 2 * (2 * aq * y) * bq = 4 * aq * (y ^ 2 + bq * y) := by
      rw [haq, hbq]
      ring_nf
    have g₁: aq = 1 := by rfl
    have g₂: y ^ 2 + bq * y = - cq := (neg_eq_of_add_eq_zero_left h₁₁).symm
    rw [g₀, g₂]
    linarith
  let s : ℝ := ((3 * a ^ 2 - b ^ 2) * (3 * b ^ 2 - a ^ 2)) / (4 * a ^ 2)
  have hs : s = ((3 * a ^ 2 - b ^ 2) * (3 * b ^ 2 - a ^ 2)) / (4 * a ^ 2) := by rfl
  have h₁₄: discrim aq bq cq = s := by
    have g₀: aq ≠ 0 := by exact Ne.symm (zero_ne_one' ℝ)
    apply (quadratic_eq_zero_iff_discrim_eq_sq g₀ y).mp at h₁₂
    rw [h₁₂, h₁₃]
    rw [haq, hbq, hcq, hs]
    ring_nf
  rw [← one_mul (y ^ 2), pow_two] at h₁₁
  apply (quadratic_eq_zero_iff_discrim_eq_sq one_ne_zero y).mp at h₁₁
  constructor
  · exact h₁₀
  · by_contra! hc
    have hc₀: (3 * b ^ 2 - a ^ 2) ≤ 0 := by linarith
    have hc₁: 0 < (3 * a ^ 2 - b ^ 2) := by
      refine sub_pos_of_lt ?_
      refine lt_trans h₁₀ ?_
      refine lt_mul_left ?_ (by linarith)
      exact sq_pos_of_pos ha
    have hc₂: (3 * a ^ 2 - b ^ 2) * (3 * b ^ 2 - a ^ 2) ≤ 0 := by
      refine mul_nonpos_of_nonneg_of_nonpos ?_ hc₀
      exact le_of_lt hc₁
    have hc₃: s ≤ 0 := by
      refine div_nonpos_iff.mpr ?_
      right
      constructor
      · exact hc₂
      · positivity
    rw [← h₁₄] at hc₃
    have h₁₅: aq ≠ 0 := by exact Ne.symm (zero_ne_one' ℝ)
    by_cases hc₄: s < 0
    · have hc₅: ∀ d:ℝ , discrim aq bq cq ≠ d ^ 2 := by
        intro d
        rw [h₁₄]
        have hc₆: 0 ≤ d ^ 2 := by exact sq_nonneg d
        linarith
      exfalso
      exact hc₅ ((2 : ℝ) * (1 : ℝ) * y + -(a ^ (2 : ℕ) + b ^ (2 : ℕ)) / ((2 : ℝ) * a)) h₁₁
    · have hc₅: s = 0 := by linarith
      grind

snip end

problem imo1961_p1a (a b x y z : ℝ) :
  ⟨x,y,z⟩ ∈ xyz_of_ab a b ↔ IsSolution a b x y z := by
  simp
  constructor
  · grind
  · intro h₀
    obtain ⟨h₀, h₁, h₂⟩ := h₀
    have h₃: (x + y) ^ 2 - z ^ 2 = b ^ 2 := by
      rw [add_sq, mul_assoc 2, h₂, ← h₁]
      group
    by_cases ha₀: a = 0
    · right
      have hb₀ : b = 0 := by grind
      rw [hb₀, zero_pow two_ne_zero, ← h₂, add_sq] at h₃
      ring_nf at h₃
      have h₄ : x ^ 3 = y ^ 3 := by grind
      have h₅: x = y := by
        refine (Odd.pow_inj ?_).mp h₄
        exact Nat.odd_iff.mpr rfl
      rw [← h₅] at h₃
      have h₆ : x = 0 := by
        ring_nf at h₃
        refine (pow_eq_zero_iff two_ne_zero).mp ?_
        refine eq_zero_of_ne_zero_of_mul_right_eq_zero ?_ h₃
        exact three_ne_zero
      bound
    · left
      refine ⟨ha₀, ?_⟩
      have h₄: (x + y) ^ 2 - z ^ 2 = (x + y + z) * (x + y - z) := by exact sq_sub_sq (x + y) z
      have h₅: z = (a ^ 2 - b ^ 2) / (2 * a) := by grind
      refine ⟨h₅, ?_⟩
      intro m
      rw [← h₅, ← h₂]
      grind


problem imo1961_p1b (a b x y z : ℝ) (h₀ : IsSolution a b x y z) :
    ⟨a,b⟩ ∈ ab_that_make_xyz_positive_distinct ↔
      (0 < x ∧ 0 < y ∧ 0 < z ∧ [x,y,z].Nodup) := by
  obtain ⟨h₀, h₁, h₂⟩ := h₀
  constructor
  · simp
    intro h₃ h₄ h₅
    rw [← h₀, ← h₁, add_sq, add_sq] at h₄ h₅
    have h₆: 0 < x * y + (x + y) * z := by linarith
    have h₇: x * y + (x + y) * z < (x ^ 2 + y ^ 2 + z ^ 2) := by linarith
    rw [add_comm (x * y), h₂, pow_two, ← add_mul, h₀] at h₆
    have hz₀: 0 < z := by exact (pos_iff_pos_of_mul_pos h₆).mp h₃
    have h₈: 0 < x ∧ 0 < y := by
      have hx₀: 0 < x * y := by rw [h₂]; exact sq_pos_of_pos hz₀
      by_cases hx₁: 0 < x
      · refine ⟨hx₁, ?_⟩
        exact (pos_iff_pos_of_mul_pos hx₀).mp hx₁
      · push_neg at hx₁
        exfalso
        have h₈₀: (x + y) ^ 2 - z ^ 2 = b ^ 2 := by
          rw [add_sq, mul_assoc 2, h₂, ← h₁]
          group
        have hy₀: y < 0 := by exact neg_of_mul_pos_right hx₀ hx₁
        have h₈₁: z ^ 2 < (x + y) ^ 2 := by
          refine lt_of_sub_pos ?_
          rw [h₈₀, ← h₁]
          positivity
        have h₈₂: x + y + z < 0 := by
          refine add_lt_of_lt_sub_left ?_
          apply sq_lt_sq.mp at h₈₁
          rw [zero_sub]
          have hx₂ : x + y < 0 := by exact Right.add_neg_of_nonpos_of_neg hx₁ hy₀
          rw [abs_of_pos hz₀, abs_of_neg hx₂] at h₈₁
          exact h₈₁
        order
    refine ⟨h₈.1, h₈.2, ?_⟩
    refine ⟨hz₀, ?_⟩
    constructor
    · constructor
      · by_contra! hh₀
        have hh₁: z = y := by
          rw [hh₀, ← pow_two] at h₂
          symm
          refine (pow_left_inj₀ ?_ ?_ two_ne_zero).mp h₂
          · exact le_of_lt h₈.2
          · exact le_of_lt hz₀
        rw [hh₀, hh₁] at h₇
        linarith
      · by_contra! hh₀
        have hh₁: y = z := by
          rw [hh₀, pow_two] at h₂
          symm
          apply mul_eq_mul_left_iff.mp at h₂
          bound
        rw [hh₀, hh₁] at h₇
        linarith
    · by_contra! hh₀
      have hh₁: x = z := by
        rw [hh₀, pow_two] at h₂
        apply mul_eq_mul_right_iff.mp at h₂
        bound
      rw [hh₀, hh₁] at h₇
      linarith
  · intro h₃
    simp
    refine aux_1 x y z a b ?_ h₃.2.2.2 h₀ h₁ h₂
    bound

end Imo1961P1
