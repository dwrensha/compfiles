/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InternLM-MATH LEAN Formalizer v0.1, Goedel-Prover-V2
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1977, Problem 4

Define f(x) = 1 - a cos x - b sin x - A cos 2x - B sin 2x,
where a, b, A, B are real constants.
Suppose that f(x) ≥ 0 for all real x.
Prove that a^2 + b^2 ≤ 2 and A^2 + B^2 ≤ 1.
-/

namespace Imo1977P4

set_option maxHeartbeats 0

problem imo1977_p4 (f : ℝ → ℝ) (a b A B : ℝ)
  (h₀ : ∀ x, f x =
             1 - a * Real.cos x - b * Real.sin x - A * Real.cos (2 * x) - B * Real.sin (2 * x))
  (h₁ : ∀ x, f x ≥ 0) :
    a ^ 2 + b ^ 2 ≤ 2 ∧ A ^ 2 + B ^ 2 ≤ 1 := by
  have h₂ : A ^ 2 + B ^ 2 ≤ 1 := by
    by_contra! h
    have h₅ : 0 < A ^ 2 + B ^ 2 := by positivity

    set R : ℝ := Real.sqrt (A ^ 2 + B ^ 2) with hR_def
    have hR_pos : 0 < R := Real.sqrt_pos.mpr h₅
    have hR_sq : R ^ 2 = A ^ 2 + B ^ 2 := Real.sq_sqrt (by positivity)

    set p : ℝ := A / R with hp_def
    set q : ℝ := B / R with hq_def
    have hpq_sq : p ^ 2 + q ^ 2 = 1 := by
      calc
        p ^ 2 + q ^ 2 = (A / R) ^ 2 + (B / R) ^ 2 := by rw [hp_def, hq_def]
        _ = (A ^ 2 + B ^ 2) / R ^ 2 := by
          field_simp [hR_pos.ne']
        _ = 1 := by
          rw [hR_sq]
          field_simp [hR_pos.ne']

    have hθ : ∃ (θ : ℝ), Real.cos θ = p ∧ Real.sin θ = q := by

      have h₆ : p ^ 2 + q ^ 2 = 1 := hpq_sq

      by_cases hq_nonneg : q ≥ 0
      · use Real.arccos p
        have h₇ : Real.cos (Real.arccos p) = p := by
          rw [Real.cos_arccos] <;>
            (try { nlinarith [Real.cos_le_one p, Real.neg_one_le_cos p] })
        have h₈ : Real.sin (Real.arccos p) = Real.sqrt (1 - p ^ 2) := by
          rw [Real.sin_arccos]
        have h₉ : Real.sqrt (1 - p ^ 2) = q := by
          have h₁₀ : q ≥ 0 := hq_nonneg
          have h₁₁ : q ^ 2 = 1 - p ^ 2 := (sub_eq_of_eq_add' hpq_sq.symm).symm
          have h₁₂ : Real.sqrt (1 - p ^ 2) = q := by
            rw [Real.sqrt_eq_iff_eq_sq] <;> nlinarith [Real.sqrt_nonneg (1 - p ^ 2)]
          exact h₁₂
        exact ⟨h₇, by linarith⟩
      · use -Real.arccos p
        have h₇ : Real.cos (-Real.arccos p) = p := by
          rw [Real.cos_neg, Real.cos_arccos] <;>
            (try { nlinarith [Real.cos_le_one p, Real.neg_one_le_cos p] })
        have h₈ : Real.sin (-Real.arccos p) = -Real.sqrt (1 - p ^ 2) := by
          rw [Real.sin_neg, Real.sin_arccos]
        have h₉ : -Real.sqrt (1 - p ^ 2) = q := by
          have h₁₀ : q < 0 := by linarith
          have h₁₁ : q ^ 2 = 1 - p ^ 2 := (sub_eq_of_eq_add' hpq_sq.symm).symm
          have h₁₂ : Real.sqrt (1 - p ^ 2) = -q := by
            rw [Real.sqrt_eq_iff_eq_sq] <;> nlinarith [Real.sqrt_nonneg (1 - p ^ 2)]
          linarith
        exact ⟨h₇, by linarith⟩
    obtain ⟨θ, hθ_cos, hθ_sin⟩ := hθ

    have h₁₀ : A * Real.cos θ + B * Real.sin θ = R := by
      calc
        A * Real.cos θ + B * Real.sin θ = R * p * Real.cos θ + R * q * Real.sin θ := by
          rw [hp_def, hq_def]
          field_simp [hR_pos.ne']
        _ = R * (p * Real.cos θ + q * Real.sin θ) := by ring
        _ = R * (p * p + q * q) := by
          rw [hθ_cos, hθ_sin]
        _ = R * 1 := by
          have h₁₁ : p ^ 2 + q ^ 2 = 1 := hpq_sq
          have h₁₂ : p * p + q * q = 1 := by
            nlinarith
          rw [h₁₂]
        _ = R := by ring

    have h₁₁ : A * Real.cos θ + B * Real.sin θ > 1 := by
      have h₁₂ : R > 1 := by
        have h₁₃ : R ^ 2 = A ^ 2 + B ^ 2 := hR_sq
        nlinarith [Real.sqrt_nonneg (A ^ 2 + B ^ 2)]
      linarith

    have h₁₂ : A * Real.cos (2 * (θ / 2)) + B * Real.sin (2 * (θ / 2)) > 1 := by
      have h₁₃ : Real.cos (2 * (θ / 2)) = Real.cos θ := by ring_nf
      have h₁₄ : Real.sin (2 * (θ / 2)) = Real.sin θ := by ring_nf
      cutsat
    have h₁₃ : A * Real.cos (2 * (θ / 2)) + B * Real.sin (2 * (θ / 2)) ≤ 1 := by
      have h₁₄ : f (θ / 2) + f (θ / 2 + Real.pi) ≥ 0 := by
        have h₁₅ : f (θ / 2) ≥ 0 := h₁ (θ / 2)
        have h₁₆ : f (θ / 2 + Real.pi) ≥ 0 := h₁ (θ / 2 + Real.pi)
        positivity
      have h₁₅ : f (θ / 2) + f (θ / 2 + Real.pi) = 2 - 2 * (A * Real.cos (2 * (θ / 2)) + B * Real.sin (2 * (θ / 2))) := by
        have h₁₆ : f (θ / 2) = 1 - a * Real.cos (θ / 2) - b * Real.sin (θ / 2) - A * Real.cos (2 * (θ / 2)) - B * Real.sin (2 * (θ / 2)) := by
          rw [h₀]
        have h₁₇ : f (θ / 2 + Real.pi) = 1 - a * Real.cos (θ / 2 + Real.pi) - b * Real.sin (θ / 2 + Real.pi) - A * Real.cos (2 * (θ / 2 + Real.pi)) - B * Real.sin (2 * (θ / 2 + Real.pi)) := by
          rw [h₀]
        rw [h₁₆, h₁₇]
        have h₁₈ : Real.cos (θ / 2 + Real.pi) = -Real.cos (θ / 2) := by
          rw [Real.cos_add]
          simp [Real.cos_pi, Real.sin_pi]
        have h₁₉ : Real.sin (θ / 2 + Real.pi) = -Real.sin (θ / 2) := by
          rw [Real.sin_add]
          simp [Real.cos_pi, Real.sin_pi]
        have h₂₀ : Real.cos (2 * (θ / 2 + Real.pi)) = Real.cos (2 * (θ / 2)) := by
          have h₂₁ : 2 * (θ / 2 + Real.pi) = 2 * (θ / 2) + 2 * Real.pi := by ring_nf
          rw [h₂₁]
          exact Real.cos_add_two_pi (2 * (θ / 2))
        have h₂₁ : Real.sin (2 * (θ / 2 + Real.pi)) = Real.sin (2 * (θ / 2)) := by
          have h₂₂ : 2 * (θ / 2 + Real.pi) = 2 * (θ / 2) + 2 * Real.pi := by ring_nf
          rw [h₂₂]
          exact Real.sin_add_two_pi (2 * (θ / 2))
        rw [h₁₈, h₁₉, h₂₀, h₂₁]
        ring_nf
      rw [h₁₅] at h₁₄
      linarith
    linarith

  have h₃ : a ^ 2 + b ^ 2 ≤ 2 := by
    by_contra! h

    set C : ℝ := a + b with hC_def
    set D : ℝ := a - b with hD_def
    have hC_sq_add_D_sq : C ^ 2 + D ^ 2 = 2 * (a ^ 2 + b ^ 2) := by
      calc
        C ^ 2 + D ^ 2 = (a + b) ^ 2 + (a - b) ^ 2 := by rw [hC_def, hD_def]
        _ = 2 * (a ^ 2 + b ^ 2) := by ring
    have hC_sq_add_D_sq_gt_4 : C ^ 2 + D ^ 2 > 4 := by
      have h₅ : 2 * (a ^ 2 + b ^ 2) > 4 := by linarith
      linarith

    set R : ℝ := Real.sqrt (C ^ 2 + D ^ 2) with hR_def
    have hR_pos : 0 < R := by positivity
    have hR_sq : R ^ 2 = C ^ 2 + D ^ 2 := Real.sq_sqrt (by positivity)

    set p : ℝ := C / R with hp_def
    set q : ℝ := D / R with hq_def
    have hpq_sq : p ^ 2 + q ^ 2 = 1 := by
      calc
        p ^ 2 + q ^ 2 = (C / R) ^ 2 + (D / R) ^ 2 := by rw [hp_def, hq_def]
        _ = (C ^ 2 + D ^ 2) / R ^ 2 := by
          field_simp [hR_pos.ne']
        _ = 1 := by
          rw [hR_sq]
          field_simp [hR_pos.ne']

    have hθ : ∃ (θ : ℝ), Real.cos θ = p ∧ Real.sin θ = -q := by
      by_cases hq_nonneg : q ≥ 0
      · use -Real.arccos p
        have h₅ : Real.cos (-Real.arccos p) = p := by
          rw [Real.cos_neg, Real.cos_arccos] <;>
            (try { nlinarith [Real.cos_le_one p, Real.neg_one_le_cos p] })
        have h₆ : Real.sin (-Real.arccos p) = -Real.sqrt (1 - p ^ 2) := by
          rw [Real.sin_neg, Real.sin_arccos]
        have h₇ : -Real.sqrt (1 - p ^ 2) = -q := by
          have h₈ : q ≥ 0 := hq_nonneg
          have h₉ : q ^ 2 = 1 - p ^ 2 := (sub_eq_of_eq_add' hpq_sq.symm).symm
          have h₁₀ : Real.sqrt (1 - p ^ 2) = q := by
            rw [Real.sqrt_eq_iff_eq_sq] <;> nlinarith [Real.sqrt_nonneg (1 - p ^ 2)]
          linarith
        exact ⟨h₅, by linarith⟩
      · use Real.arccos p
        have h₅ : Real.cos (Real.arccos p) = p := by
          rw [Real.cos_arccos] <;>
            (try { nlinarith [Real.cos_le_one p, Real.neg_one_le_cos p] })
        have h₆ : Real.sin (Real.arccos p) = Real.sqrt (1 - p ^ 2) := by
          rw [Real.sin_arccos]
        have h₇ : Real.sqrt (1 - p ^ 2) = -q := by
          have h₈ : q < 0 := by linarith
          have h₉ : q ^ 2 = 1 - p ^ 2 := (sub_eq_of_eq_add' hpq_sq.symm).symm
          have h₁₀ : Real.sqrt (1 - p ^ 2) = -q := by
            rw [Real.sqrt_eq_iff_eq_sq] <;> nlinarith [Real.sqrt_nonneg (1 - p ^ 2)]
          linarith
        exact ⟨h₅, by linarith⟩
    obtain ⟨θ, hθ_cos, hθ_sin⟩ := hθ

    have h₅ : C * Real.cos θ - D * Real.sin θ = R := by
      calc
        C * Real.cos θ - D * Real.sin θ = R * p * Real.cos θ - R * q * Real.sin θ := by
          rw [hp_def, hq_def]
          ring_nf
          field_simp [hR_pos.ne']
        _ = R * (p * Real.cos θ - q * Real.sin θ) := by ring
        _ = R * (p * p + q * q) := by
          rw [hθ_cos, hθ_sin]
          ring_nf
        _ = R * 1 := by
          have h₆ : p ^ 2 + q ^ 2 = 1 := hpq_sq
          have h₇ : p * p + q * q = 1 := by
            nlinarith
          rw [h₇]
        _ = R := by ring

    have h₆ : C * Real.cos θ - D * Real.sin θ > 2 := by
      have h₇ : R > 2 := by
        have h₈ : R ^ 2 = C ^ 2 + D ^ 2 := hR_sq
        have h₉ : C ^ 2 + D ^ 2 > 4 := hC_sq_add_D_sq_gt_4
        nlinarith [Real.sqrt_nonneg (C ^ 2 + D ^ 2)]
      cutsat

    have h₇ : C * Real.cos θ - D * Real.sin θ ≤ 2 := by
      have h₈ : f θ + f (θ + Real.pi / 2) ≥ 0 := by
        exact Left.add_nonneg (h₁ θ) (h₁ (θ + Real.pi / 2))
      have h₉ : f θ + f (θ + Real.pi / 2) = 2 - (C * Real.cos θ - D * Real.sin θ) := by
        have h₁₀ : f θ = 1 - a * Real.cos θ - b * Real.sin θ - A * Real.cos (2 * θ) - B * Real.sin (2 * θ) := by
          rw [h₀]
        have h₁₁ : f (θ + Real.pi / 2) = 1 - a * Real.cos (θ + Real.pi / 2) - b * Real.sin (θ + Real.pi / 2) - A * Real.cos (2 * (θ + Real.pi / 2)) - B * Real.sin (2 * (θ + Real.pi / 2)) := by
          rw [h₀]
        rw [h₁₀, h₁₁]
        have h₁₂ : Real.cos (θ + Real.pi / 2) = -Real.sin θ := by
          rw [Real.cos_add]
          simp [Real.cos_pi_div_two, Real.sin_pi_div_two]
        have h₁₃ : Real.sin (θ + Real.pi / 2) = Real.cos θ := by
          rw [Real.sin_add]
          simp [Real.cos_pi_div_two, Real.sin_pi_div_two]
        have h₁₄ : Real.cos (2 * (θ + Real.pi / 2)) = -Real.cos (2 * θ) := by
          have h₁₅ : 2 * (θ + Real.pi / 2) = 2 * θ + Real.pi := by ring_nf
          rw [h₁₅]
          exact Real.cos_add_pi _
        have h₁₅ : Real.sin (2 * (θ + Real.pi / 2)) = -Real.sin (2 * θ) := by
          have h₁₆ : 2 * (θ + Real.pi / 2) = 2 * θ + Real.pi := by ring_nf
          rw [h₁₆]
          exact Real.sin_add_pi _
        rw [h₁₂, h₁₃, h₁₄, h₁₅]
        have h₁₆ : C = a + b := by rw [hC_def]
        have h₁₇ : D = a - b := by rw [hD_def]
        simp only [h₁₆, h₁₇] at *
        ring_nf at *
      rw [h₉] at h₈
      linarith
    linarith

  exact ⟨h₃, h₂⟩


end Imo1977P4
