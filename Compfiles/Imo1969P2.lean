/-
Copyright (c) 2023 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roozbeh Yousefzadeh
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

import ProblemExtraction

problem_file {
  tags := [.Algebra]
  importedFrom :=
    "https://github.com/roozbeh-yz/IMO-Steps/blob/main/imo_proofs/imo_1969_p2.lean"
}

/-!
# International Mathematical Olympiad 1969, Problem 2

Let a₁, a₂, ..., aₙ be real constants, x be a real variable, and

  f(x) = cos(a₁ + x) + (1/2)cos(a₂ + x) + (1/4)cos(a₃ + x) + ...
         + (1/2ⁿ⁻¹)cos(aₙ + x).

Given that f(x₁) = f(x₂) = 0 for some x₁, x₂, prove that
x₂ - x₁ = mπ for some integer m.
-/

namespace Imo1969P2

open scoped Real

problem imo1969_p2
    (x₁ x₂ : ℝ)
    (n : ℕ)
    (a : ℕ → ℝ)
    (f : ℝ → ℝ)
    (h₁ : ∀ x, f x = ∑ i ∈ Finset.range n, (Real.cos (a i + x)) / (2^i))
    (h₂ : f x₂ = 0)
    (h₃ : f x₁ = 0)
    (h₄: ∑ i ∈ Finset.range n, (Real.cos (a i) / (2 ^ i)) ≠ 0) :
    ∃ m : ℤ, x₂ - x₁ = m * π := by
  let Ccos := ∑ i ∈ Finset.range n, (Real.cos (a i) / (2 ^ i))
  let Csin := ∑ i ∈ Finset.range n, (Real.sin (a i) / (2 ^ i))
  have hCcos: Ccos = ∑ i ∈ Finset.range n, (Real.cos (a i) / (2 ^ i)) := rfl
  have hCsin: Csin = ∑ i ∈ Finset.range n, (Real.sin (a i) / (2 ^ i)) := rfl
  have h₅: ∀ x, f x = Ccos * Real.cos x - Csin * Real.sin x := by
    intro x
    rw [h₁ x]
    have h₅₀: ∑ i ∈ Finset.range n, (Real.cos (a i + x) / 2 ^ i)
              = ∑ i ∈ Finset.range n, (((Real.cos (a i) * Real.cos (x) - Real.sin (a i) * Real.sin (x)) / (2^i))) := by
      refine Finset.sum_congr (by rfl) ?_
      intros i _
      rw [Real.cos_add]
    rw [h₅₀]
    ring_nf
    rw [Finset.sum_sub_distrib]
    have h₅₂: ∑ i ∈ Finset.range n, Real.cos (a i) * Real.cos x * (2⁻¹) ^ i
            = ∑ i ∈ Finset.range n, (Real.cos (a i) * (2⁻¹) ^ i) * Real.cos x := by
      refine Finset.sum_congr (by rfl) ?_
      intro i _
      ring
    have h₅₃: ∑ x_1 ∈ Finset.range n, Real.sin (a x_1) * Real.sin x * (2⁻¹) ^ x_1
            = ∑ x_1 ∈ Finset.range n, ((Real.sin (a x_1) * (2⁻¹) ^ x_1) * Real.sin x) := by
      refine Finset.sum_congr (by rfl) ?_
      intro i _
      ring
    rw [h₅₂, ← Finset.sum_mul _ _ (Real.cos x)]
    rw [h₅₃, ← Finset.sum_mul _ _ (Real.sin x)]
    ring_nf at hCcos
    ring_nf at hCsin
    rw [hCcos, hCsin]
    ring
  have h₆: (∃ x, (f x = 0 ∧ Real.cos x = 0)) → ∀ y, f y = Ccos * Real.cos y := by
    intro g₀
    obtain ⟨x, hx₀, hx₁⟩ := g₀
    have g₁: ∑ i ∈ Finset.range n, (Real.sin (a i) / (2 ^ i)) = 0 := by
      rw [h₅ x, hx₁] at hx₀
      simp at hx₀
      cases' hx₀ with hx₂ hx₃
      . exact hx₂
      . exfalso
        apply Real.sin_eq_zero_iff_cos_eq.mp at hx₃
        cases' hx₃ with hx₃ hx₄
        . linarith
        . linarith
    intro y
    rw [h₅ y]
    have g₂: Csin = 0 := by linarith
    rw [g₂, zero_mul]
    exact sub_zero (Ccos * Real.cos y)
  by_cases hmn: (Real.cos x₂ = 0) ∨ (Real.cos x₁ = 0)
  . have h₇: ∀ (x : ℝ), f x = Ccos * Real.cos x := by
      refine h₆ ?_
      cases' hmn with hm hn
      . use x₂
      . use x₁
    have h₈: ∀ x, f x = 0 → Real.cos x = 0 := by
      intros x hx₀
      rw [h₇ x] at hx₀
      refine eq_zero_of_ne_zero_of_mul_left_eq_zero ?_ hx₀
      exact h₄
    have hm₀: ∃ t:ℤ , x₂ = (2 * ↑ t + 1) * π / 2 := by
      refine Real.cos_eq_zero_iff.mp ?_
      exact h₈ x₂ h₂
    have hn₀: ∃ t:ℤ , x₁ = (2 * ↑ t + 1) * π / 2 := by
      refine Real.cos_eq_zero_iff.mp ?_
      exact h₈ x₁ h₃
    obtain ⟨tm, hm₁⟩ := hm₀
    obtain ⟨tn, hn₁⟩ := hn₀
    rw [hm₁, hn₁]
    use (tm - tn)
    rw [Int.cast_sub]
    ring_nf
  . push_neg at hmn
    have h₇: Real.tan x₂ = Real.tan x₁ := by
      have h₇₀: ∀ (x:ℝ), (f x = 0 ∧ Real.cos x ≠ 0) → Real.tan x = Ccos / Csin := by
        intro x hx₀
        rw [Real.tan_eq_sin_div_cos]
        symm
        refine (div_eq_div_iff ?_ ?_).mp ?_
        . simp
          exact hx₀.2
        . simp
          have hx₁: Ccos * Real.cos x ≠ 0 := by
            refine mul_ne_zero ?_ hx₀.2
            exact h₄
          have hx₂: Ccos * Real.cos x = Csin * Real.sin x := by
            rw [h₅ x] at hx₀
            refine eq_of_sub_eq_zero ?_
            exact hx₀.1
          have hx₃: Csin * Real.sin x ≠ 0 := by
            rw [← hx₂]
            exact hx₁
          exact left_ne_zero_of_mul hx₃
        . rw [h₅ x, sub_eq_zero] at hx₀
          simp only [div_inv_eq_mul, mul_comm (Real.sin x) _]
          exact hx₀.1
      have h₇₁: Real.tan x₂ = Ccos / Csin := by
        refine h₇₀ x₂ ?_
        constructor
        . exact h₂
        . exact hmn.1
      have h₇₂: Real.tan x₁ = Ccos / Csin := by
        refine h₇₀ x₁ ?_
        constructor
        . exact h₃
        · exact hmn.2
      rw [h₇₁, h₇₂]
    have h₈: Real.sin (x₂ - x₁) = 0 := by
      have h₈₂: Real.sin (x₂ - x₁) / (Real.cos x₂ * Real.cos x₁) = 0 := by
        rw [Real.sin_sub]
        rw [← div_sub_div (Real.sin x₂) (Real.sin x₁) hmn.1 hmn.2]
        simp only [← Real.tan_eq_sin_div_cos]
        exact sub_eq_zero_of_eq h₇
      have h_nonzero : Real.cos x₂ * Real.cos x₁ ≠ 0 := mul_ne_zero hmn.1 hmn.2
      rw [div_eq_zero_iff, or_iff_left h_nonzero] at h₈₂
      exact h₈₂
    apply Real.sin_eq_zero_iff.mp at h₈
    let ⟨t, ht⟩ := h₈
    use t
    exact ht.symm

end Imo1969P2
