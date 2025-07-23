/-
Copyright (c) 2025 Roozbeh Yousefzadeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roozbeh Yousefzadeh
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file {
  tags := [.Algebra]
  importedFrom := "https://github.com/roozbeh-yz/IMO-Steps/blob/main/Lean_v20/imo_proofs/imo_1973_p3.lean"
}

/-!
# International Mathematical Olympiad 1973, Problem 3

Let $a$ and $b$ be real numbers for which the equation $x^4 + ax^3 + bx^2 + ax + 1 = 0$ has at least one real solution. For all such pairs $(a, b)$, find the minimum value of $a^2 + b^2$.

-/

namespace Imo1973P3

noncomputable abbrev solution : ℝ := (4:ℝ)/5

snip begin

lemma aux_1
  (a b : ℝ)
  (h₀ : ∃ (x:ℝ), x^4 + a * x^3 + b * x^2 + a * x + 1 = 0) :
  4 / 5 ≤ a^2 + b^2 := by
  obtain ⟨x, h₁⟩ := h₀
  let t :=  x + 1 / x
  have ht₀: t = x + 1 / x := by rfl
  have hx: x ≠ 0 := by
    by_contra hc
    rw [hc] at h₁
    simp at h₁
  have h₂: t ^ 2 + a * t + (b - 2) = 0 := by
    rw [ht₀]
    ring_nf
    rw [mul_inv_cancel₀ hx]
    simp
    have h₂₀: (x ^ 4 + a * x ^ 3 + b * x ^ 2 + a * x + 1) / (x ^ 2) = 0 / (x ^ 2) := by
      exact congrFun (congrArg HDiv.hDiv h₁) (x ^ 2)
    ring_nf at h₂₀
    have hx₁: x ^ 2 ≠ 0 := by exact pow_ne_zero 2 hx
    rw [mul_comm (x ^ 2), mul_assoc b, inv_pow, mul_inv_cancel₀ hx₁, mul_one] at h₂₀
    rw [mul_comm x a, mul_assoc a, pow_two, mul_inv, ← mul_assoc x, mul_inv_cancel₀ hx, one_mul] at h₂₀
    rw [mul_comm _ a, mul_assoc a, ← pow_two, inv_pow, ← pow_sub₀, ← pow_sub₀] at h₂₀
    simp at h₂₀
    all_goals try assumption
    all_goals try linarith
  have ht₁: 2 ≤ abs t := by
    have g₀: 1 * (x * x) + (-t) * x + 1 = 0 := by
      rw [ht₀]
      ring_nf
      rw [mul_inv_cancel₀ hx]
      exact sub_eq_zero_of_eq rfl
    have g₁: discrim 1 (-t) 1 = (-t) ^ 2 - 4 * 1 * 1 := by exact rfl
    simp at g₁
    by_contra hc₀
    push_neg at hc₀
    have hc₁: t ^ 2 < 2 ^ 2 := by
      refine sq_lt_sq.mpr ?_
      refine lt_of_lt_of_le hc₀ ?_
      rw [abs_of_nonneg]
      norm_num
    apply sub_neg_of_lt at hc₁
    have hc₂: ∀ (s : ℝ), discrim 1 (-t) 1 ≠ s ^ 2 := by
      intro s
      have hs: 0 ≤ s ^ 2 := by exact sq_nonneg s
      linarith
    have hc₃: 1 * (x * x) + -t * x + 1 ≠ 0 := by
      exact quadratic_ne_zero_of_discrim_ne_sq hc₂ x
    exact hc₃ g₀
  have ht₂: 0 < t ^ 2 := by
    refine sq_pos_iff.mpr ?_
    by_contra hc
    rw [hc] at ht₁
    simp at ht₁
    linarith
  have h₃: (a * t + b * 1) ^ 2 ≤ (a ^ 2 + b ^ 2) * (t ^ 2 + 1 ^ 2) := by
    let s := Finset.range 2
    let f : ℕ → ℝ := fun x => a * (1 - x) + b * x
    let g : ℕ → ℝ := fun x => t * (1 - x) + 1 * x
    have hhf: f = fun x:ℕ => a * (1 - x) + b * x := by rfl
    have hhg: g = fun x:ℕ => t * (1 - x) + 1 * x := by rfl
    have h₃₀: f 0 = a := by rw [hhf]; bound
    have h₃₁: f 1 = b := by rw [hhf]; ring_nf
    have h₃₂: g 0 = t := by rw [hhg]; ring_nf
    have h₃₃: g 1 = 1 := by rw [hhg]; ring_nf
    have h₃₄: a * t + b * 1 = ∑ i ∈ s, f i * g i := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
      rw [h₃₀, h₃₁, h₃₂, h₃₃, zero_add]
    rw [h₃₄]
    have h₃₅: (∑ i ∈ s, f i * g i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * ∑ i ∈ s, g i ^ 2 := by
      exact Finset.sum_mul_sq_le_sq_mul_sq s f g
    refine le_trans h₃₅ ?_
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    simp
    rw [h₃₀, h₃₁, h₃₂, h₃₃]
    linarith
  rw [mul_one, one_pow] at h₃
  have h₄: (a * t + b) ^ 2 = (t ^ 2 - 2) ^ 2 := by
    refine (pow_eq_pow_iff_of_ne_zero two_ne_zero).mpr ?_
    right
    constructor
    . linarith
    . decide
  have h₅: 4 / 5 ≤ (t ^ 2 - 2) ^ 2 / (t ^ 2 + 1) := by
    refine (div_le_div_iff₀ (by norm_num) ?_).mpr ?_
    . positivity
    . rw [mul_add, mul_one, sub_sq, add_mul, sub_mul, ← pow_mul]
      norm_num
      have h₅₀: 0 ≤ 5 * t ^ 4 + 16 - 24 * t ^ 2 := by
        have h₅₁: 5 * t ^ 4 + 16 - 24 * t ^ 2 = (5 * t ^ 2 - 4) * (t ^ 2 - 4) := by ring_nf
        have h₅₂: 2 ^ 2 ≤ t ^ 2 := by
          refine sq_le_sq.mpr ?_
          refine le_trans ?_ ht₁
          rw [abs_of_nonneg]
          positivity
        have h₅₃: 0 ≤ t ^ 2 - 4 := by linarith
        have h₅₄: 0 ≤ 5 * t ^ 2 - 4 := by linarith
        rw [h₅₁]
        exact Left.mul_nonneg h₅₄ h₅₃
      linarith
  refine le_trans h₅ ?_
  rw [h₄] at h₃
  refine (div_le_iff₀ ?_).mpr h₃
  positivity

snip end

problem imo1973_p3
  (S : Set (ℝ × ℝ))
  (hS : S = {(a, b) | ∃ x : ℝ, x ^ 4 + a * x ^ 3 + b * x ^ 2 + a * x + 1 = 0}) :
  IsLeast { x.1 ^ 2 + x.2 ^ 2 | x ∈ S } solution := by
  constructor
  . simp only [Prod.exists, Set.mem_setOf_eq]
    use 4/5
    use -2/5
    constructor
    . simp only [hS, Set.mem_setOf_eq]
      use -1
      group
    . group
  . refine mem_lowerBounds.mpr ?_
    simp only [Prod.exists, Set.mem_setOf_eq, forall_exists_index, and_imp]
    intro x a b h₀ h₁
    rw [←h₁]
    refine aux_1 a b ?_
    bound
