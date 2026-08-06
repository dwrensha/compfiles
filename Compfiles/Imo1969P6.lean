/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.Real.Sqrt
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Algebra, .Inequality]
  }

/-!
# International Mathematical Olympiad 1969, Problem 6

Given real numbers x₁, x₂, y₁, y₂, z₁, z₂ satisfying x₁ > 0, x₂ > 0,
x₁y₁ > z₁², and x₂y₂ > z₂², prove that

  8 / ((x₁ + x₂)(y₁ + y₂) - (z₁ + z₂)²) ≤ 1 / (x₁y₁ - z₁²) + 1 / (x₂y₂ - z₂²).

Give necessary and sufficient conditions for equality.
-/

namespace Imo1969P6

snip begin

-- Solution formalized from https://prase.cz/kalva/imo/isoln/isoln696.html

/-- The core AM–GM chain of the solution: with `p² = x₁y₁ - z₁²` and `q² = x₂y₂ - z₂²`
we have `pq + z₁z₂ ≤ √(x₁y₁ · x₂y₂) = √(x₁y₂) · √(x₂y₁)` and
`2 √(x₁y₂) √(x₂y₁) ≤ x₁y₂ + x₂y₁` (AM–GM). -/
theorem amgm_chain {x₁ x₂ y₁ y₂ z₁ z₂ p q : ℝ}
    (hx₁ : 0 < x₁) (hy₁ : 0 < y₁) (hx₂ : 0 < x₂) (hy₂ : 0 < y₂)
    (hp₂ : p ^ 2 = x₁ * y₁ - z₁ ^ 2) (hq₂ : q ^ 2 = x₂ * y₂ - z₂ ^ 2) :
    p * q + z₁ * z₂ ≤ Real.sqrt (x₁ * y₁ * (x₂ * y₂)) ∧
      Real.sqrt (x₁ * y₁ * (x₂ * y₂)) = Real.sqrt (x₁ * y₂) * Real.sqrt (x₂ * y₁) ∧
        2 * (Real.sqrt (x₁ * y₂) * Real.sqrt (x₂ * y₁)) ≤ x₁ * y₂ + x₂ * y₁ := by
  have hx₁y₁ : x₁ * y₁ = p ^ 2 + z₁ ^ 2 := by linarith only [hp₂]
  have hx₂y₂ : x₂ * y₂ = q ^ 2 + z₂ ^ 2 := by linarith only [hq₂]
  have hpos₁ : (0 : ℝ) ≤ x₁ * y₂ := (mul_pos hx₁ hy₂).le
  have hpos₂ : (0 : ℝ) ≤ x₂ * y₁ := (mul_pos hx₂ hy₁).le
  have hs1 : (p * q + z₁ * z₂) ^ 2 ≤ x₁ * y₁ * (x₂ * y₂) := by
    have e : x₁ * y₁ * (x₂ * y₂) = (p ^ 2 + z₁ ^ 2) * (q ^ 2 + z₂ ^ 2) := by
      rw [hx₁y₁, hx₂y₂]
    rw [e]
    linarith only [sq_nonneg (p * z₂ - q * z₁)]
  refine ⟨Real.le_sqrt_of_sq_le hs1, ?_, ?_⟩
  · rw [show x₁ * y₁ * (x₂ * y₂) = x₁ * y₂ * (x₂ * y₁) by ring,
      Real.sqrt_mul hpos₁]
  · have h := two_mul_le_add_sq (Real.sqrt (x₁ * y₂)) (Real.sqrt (x₂ * y₁))
    rw [Real.sq_sqrt hpos₁, Real.sq_sqrt hpos₂] at h
    linarith only [h]

snip end

/-- The condition for equality to hold. -/
determine eqCondition (x₁ x₂ y₁ y₂ z₁ z₂ : ℝ) : Prop := x₁ = x₂ ∧ y₁ = y₂ ∧ z₁ = z₂

problem imo1969_p6 (x₁ x₂ y₁ y₂ z₁ z₂ : ℝ)
    (hx₁ : 0 < x₁) (hx₂ : 0 < x₂)
    (h₁ : z₁ ^ 2 < x₁ * y₁) (h₂ : z₂ ^ 2 < x₂ * y₂) :
    8 / ((x₁ + x₂) * (y₁ + y₂) - (z₁ + z₂) ^ 2) ≤
        1 / (x₁ * y₁ - z₁ ^ 2) + 1 / (x₂ * y₂ - z₂ ^ 2) ∧
      (8 / ((x₁ + x₂) * (y₁ + y₂) - (z₁ + z₂) ^ 2) =
          1 / (x₁ * y₁ - z₁ ^ 2) + 1 / (x₂ * y₂ - z₂ ^ 2) ↔
        eqCondition x₁ x₂ y₁ y₂ z₁ z₂) := by
  have ha : 0 < x₁ * y₁ - z₁ ^ 2 := sub_pos.mpr h₁
  have hb : 0 < x₂ * y₂ - z₂ ^ 2 := sub_pos.mpr h₂
  have hy₁ : 0 < y₁ := pos_of_mul_pos_right (lt_of_le_of_lt (sq_nonneg z₁) h₁) hx₁.le
  have hy₂ : 0 < y₂ := pos_of_mul_pos_right (lt_of_le_of_lt (sq_nonneg z₂) h₂) hx₂.le
  set a := x₁ * y₁ - z₁ ^ 2 with ha_def
  set b := x₂ * y₂ - z₂ ^ 2 with hb_def
  set D := (x₁ + x₂) * (y₁ + y₂) - (z₁ + z₂) ^ 2 with hD_def
  set p := Real.sqrt a with hp_def
  set q := Real.sqrt b with hq_def
  have hp : 0 < p := Real.sqrt_pos_of_pos ha
  have hq : 0 < q := Real.sqrt_pos_of_pos hb
  have hp₂ : p ^ 2 = a := Real.sq_sqrt ha.le
  have hq₂ : q ^ 2 = b := Real.sq_sqrt hb.le
  obtain ⟨hle, hsqrt, h2st⟩ := amgm_chain hx₁ hy₁ hx₂ hy₂ hp₂ hq₂
  have hAM : 2 * (p * q + z₁ * z₂) ≤ x₁ * y₂ + x₂ * y₁ := by
    linarith only [hle, hsqrt, h2st]
  have hx₁y₁ : x₁ * y₁ = p ^ 2 + z₁ ^ 2 := by linarith only [hp₂]
  have hx₂y₂ : x₂ * y₂ = q ^ 2 + z₂ ^ 2 := by linarith only [hq₂]
  have hD : (p + q) ^ 2 ≤ D := by
    rw [hD_def]
    linarith only [hAM, hx₁y₁, hx₂y₂]
  have hDpos : 0 < D := lt_of_lt_of_le (sq_pos_of_pos (add_pos hp hq)) hD
  have hkey₁ : 8 * (a * b) ≤ (a + b) * (p + q) ^ 2 := by
    have hprod : (0 : ℝ) ≤ (p - q) ^ 2 * ((p + q) ^ 2 + 2 * (p * q)) :=
      mul_nonneg (sq_nonneg _) (by linarith only [mul_pos hp hq, sq_nonneg (p + q)])
    rw [← hp₂, ← hq₂]
    linarith only [hprod]
  have hkey : 8 * (a * b) ≤ (a + b) * D :=
    le_trans hkey₁ (mul_le_mul_of_nonneg_left hD (add_pos ha hb).le)
  have hmain : 8 / D ≤ 1 / a + 1 / b := by
    rw [div_add_div 1 1 ha.ne' hb.ne', div_le_div_iff₀ hDpos (mul_pos ha hb)]
    linarith only [hkey]
  refine ⟨hmain, ?_⟩
  constructor
  · intro heq
    rw [div_add_div 1 1 ha.ne' hb.ne',
      div_eq_div_iff hDpos.ne' (mul_pos ha hb).ne'] at heq
    have heq1 : 8 * (a * b) = (a + b) * D := by linear_combination heq
    have h1 : (a + b) * (p + q) ^ 2 = (a + b) * D := by
      have h2 := mul_le_mul_of_nonneg_left hD (add_pos ha hb).le
      linarith only [heq1, hkey₁, h2]
    have hD_eq : D = (p + q) ^ 2 := (mul_left_cancel₀ (add_pos ha hb).ne' h1).symm
    have hpq_eq : p = q := by
      have h3 : (p - q) ^ 2 * ((p + q) ^ 2 + 2 * (p * q)) = 0 := by
        have h4 : (a + b) * (p + q) ^ 2 = 8 * (a * b) := by linarith only [heq1, h1]
        rw [← hp₂, ← hq₂] at h4
        linear_combination h4
      have hpos : (0 : ℝ) < (p + q) ^ 2 + 2 * (p * q) :=
        add_pos (sq_pos_of_pos (add_pos hp hq)) (mul_pos two_pos (mul_pos hp hq))
      have h5 : (p - q) ^ 2 = 0 := by
        rcases mul_eq_zero.mp h3 with h | h
        · exact h
        · exact absurd h (ne_of_gt hpos)
      exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h5)
    have hAMeq : 2 * (p * q + z₁ * z₂) = x₁ * y₂ + x₂ * y₁ := by
      linarith only [hD_eq, hD_def, hx₁y₁, hx₂y₂]
    have h2st_eq : 2 * (Real.sqrt (x₁ * y₂) * Real.sqrt (x₂ * y₁)) = x₁ * y₂ + x₂ * y₁ := by
      linarith only [hAMeq, hle, hsqrt, h2st]
    have hst : Real.sqrt (x₁ * y₂) = Real.sqrt (x₂ * y₁) := by
      have hsq1 : Real.sqrt (x₁ * y₂) ^ 2 = x₁ * y₂ := Real.sq_sqrt (mul_pos hx₁ hy₂).le
      have hsq2 : Real.sqrt (x₂ * y₁) ^ 2 = x₂ * y₁ := Real.sq_sqrt (mul_pos hx₂ hy₁).le
      have h0 : (Real.sqrt (x₁ * y₂) - Real.sqrt (x₂ * y₁)) ^ 2 = 0 := by
        linarith only [h2st_eq, hsq1, hsq2]
      exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h0)
    have hxy : x₁ * y₂ = x₂ * y₁ := by
      have h8 := congrArg (· ^ 2) hst
      rwa [Real.sq_sqrt (mul_pos hx₁ hy₂).le, Real.sq_sqrt (mul_pos hx₂ hy₁).le] at h8
    have hpqz : p * q + z₁ * z₂ = Real.sqrt (x₁ * y₁ * (x₂ * y₂)) := by
      linarith only [hAMeq, h2st_eq, hsqrt]
    have hz : z₁ = z₂ := by
      have h9 := congrArg (· ^ 2) hpqz
      rw [Real.sq_sqrt (mul_pos (mul_pos hx₁ hy₁) (mul_pos hx₂ hy₂)).le, hx₁y₁, hx₂y₂] at h9
      have h10 : (p * z₂ - q * z₁) ^ 2 = 0 := by linarith only [h9]
      have h11 : p * z₂ - q * z₁ = 0 := (pow_eq_zero_iff two_ne_zero).mp h10
      rw [hpq_eq] at h11
      have h12 : q * (z₂ - z₁) = 0 := by linear_combination h11
      rcases mul_eq_zero.mp h12 with hq0 | hzz
      · exact absurd hq0 (ne_of_gt hq)
      · exact (sub_eq_zero.mp hzz).symm
    have hab : a = b := by
      have hpq2 : p ^ 2 = q ^ 2 := by rw [hpq_eq]
      linarith only [hp₂, hq₂, hpq2]
    rw [ha_def, hb_def] at hab
    have hz_sq : z₁ ^ 2 = z₂ ^ 2 := by rw [hz]
    have hxy1 : x₁ * y₁ = x₂ * y₂ := by linarith only [hab, hz_sq]
    have hx : x₁ = x₂ := by
      have hmul : (x₁ * y₁) * (x₁ * y₂) = (x₂ * y₂) * (x₂ * y₁) := by rw [hxy1, hxy]
      have hyy : (0 : ℝ) < y₁ * y₂ := mul_pos hy₁ hy₂
      have h13 : x₁ ^ 2 * (y₁ * y₂) = x₂ ^ 2 * (y₁ * y₂) := by linear_combination hmul
      have h14 : x₁ ^ 2 = x₂ ^ 2 := mul_right_cancel₀ hyy.ne' h13
      have h15 : (x₁ - x₂) * (x₁ + x₂) = 0 := by linear_combination h14
      rcases mul_eq_zero.mp h15 with hsub | hsum
      · exact sub_eq_zero.mp hsub
      · exact absurd hsum (ne_of_gt (add_pos hx₁ hx₂))
    have hy : y₁ = y₂ := by
      rw [hx] at hxy1
      exact mul_left_cancel₀ hx₂.ne' hxy1
    exact ⟨hx, hy, hz⟩
  · rintro ⟨rfl, rfl, rfl⟩
    have hb2 : b = a := by rw [hb_def, ha_def]
    have hD2 : D = 4 * a := by rw [hD_def, ha_def]; ring
    rw [hD2, hb2]
    field_simp [ha.ne']
    ring

end Imo1969P6
