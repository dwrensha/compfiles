/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roozbeh Yousefzadeh, Zheng Yuan
-/

import Mathlib.Data.Real.GoldenRatio
import Mathlib.Tactic

import ProblemExtraction

problem_file {
  tags := [.Algebra]
  importedFrom := "https://github.com/roozbeh-yz/IMO-Steps/blob/main/Lean_v20/imo_proofs/imo_1993_p5.lean"
}

/-!
# International Mathematical Olympiad 1993, Problem 5

Does there exist a function f : ℕ → ℕ such that
  i) f(1) = 2
  ii) f(f(n)) = f(n) + n for all n ∈ ℕ
  iii) f(n + 1) > f(n) for all n ∈ ℕ?
-/

namespace Imo1993P5

determine DoesExist : Bool := True

abbrev Good (f : ℕ → ℕ) : Prop := f 1 = 2 ∧ ∀ n, f (f n) = f n + n ∧ ∀ n, f n < f (n + 1)

snip begin

lemma imo_1993_p5_N:
  ∃ f : ℕ → ℕ, f 1 = 2 ∧ (∀ n, f (f n) = f n + n) ∧ (∀ n, f n < f (n + 1)) := by
  let G : ℝ := Real.goldenRatio
  have hG : G = Real.goldenRatio := by rfl
  have h₀: ∀ n : ℕ, G ^ 2 * n = G * n + n := by
    intro n
    nth_rw 3 [← one_mul n]
    rw [Nat.cast_mul, ← add_mul]
    norm_cast
    by_cases hn: 0 < n
    . refine (mul_left_inj' ?_).mpr ?_
      . positivity
      . exact Real.goldenRatio_sq
    . interval_cases n
      simp
  let f: ℕ → ℕ := fun x => (Int.natAbs (round (G * x)))
  let fz: ℤ → ℤ := fun x => round (G * x)
  have hf₀: f = fun x:ℕ => (Int.natAbs (round (G * (↑x:ℝ)))) := by rfl
  have hf₁: fz = fun x:ℤ => round (G * x) := by rfl
  have h₁: ∀ n:ℕ, 0 ≤ round (G * (↑n:ℝ)) := by
    intro n
    rw [round_eq]
    positivity
  have hf₂: ∀ n:ℕ, f n = fz n := by
    intro n
    rw [hf₀, hf₁]
    simp
    exact h₁ n
  have hg₀: 2 < √5 := by
    have g₀: 0 ≤ (2:ℝ) := zero_le_two
    have g₁: 0 ≤ √5 := by exact Real.sqrt_nonneg 5
    rw [← abs_of_nonneg g₀, ← abs_of_nonneg g₁]
    refine sq_lt_sq.mp ?_
    rw [Real.sq_sqrt (by positivity)]
    linarith
  have hg₁: 0 < G - 1 := by
    rw [hG]
    ring_nf
    norm_num
    linarith
  have hg₂: √5 < 3 := by
    have g₀: 0 ≤ (3:ℝ) := by positivity
    have g₁: 0 ≤ √5 := Real.sqrt_nonneg 5
    rw [← abs_of_nonneg g₀, ← abs_of_nonneg g₁]
    refine sq_lt_sq.mp ?_
    rw [Real.sq_sqrt (by positivity)]
    linarith
  use f
  constructor
  . rw [hf₀]
    simp
    have g₀: round G = 2 := by
      rw [round_eq]
      refine Int.floor_eq_iff.mpr ?_
      norm_cast
      rw [hG]
      constructor
      . ring_nf
        apply le_of_lt at hg₀
        linarith
      . ring_nf
        linarith
    rw [g₀]
    exact rfl
  constructor
  . intro n
    have h₂: fz (fz n) = fz n + n := by
      have h₂₀: ∀ m, abs ((↑(fz m):ℝ) - G * (↑m:ℝ)) ≤ 1 / 2 := by
        intro m
        rw [hf₁]
        rw [abs_sub_comm]
        exact abs_sub_round (G * ↑m)
      refine eq_of_abs_sub_eq_zero ?_
      have h₂₁: |(fz (fz ↑n) - G * fz ↑n) + (G - 1) * (fz ↑n - G * ↑n)| < 1 := by
        refine lt_of_le_of_lt (abs_add_le ((fz (fz ↑n) - G * fz ↑n)) ((G - 1) * (fz ↑n - G * ↑n))) ?_
        rw [abs_mul]
        have g₀: |↑(fz (fz ↑n)) - G * ↑(fz ↑n)| ≤ 1 / 2 := by exact h₂₀ (fz ↑n)
        have g₁: |(G - 1)| * |(↑(fz ↑n) - G * ↑n)| ≤ (G - 1) * (1 / 2) := by
          rw [abs_of_nonneg ?_]
          . refine (_root_.mul_le_mul_left ?_).mpr ?_
            . exact hg₁
            . exact h₂₀ ↑n
          . exact le_of_lt hg₁
        have g₂: 1 / 2 * G = 1 / 2 + (G - 1) * (1 / 2) := by linarith
        have g₃: 1 / 2 * G < 1 := by
          rw [hG]
          ring_nf
          linarith
        refine lt_of_le_of_lt ?_ g₃
        rw [g₂]
        exact _root_.add_le_add g₀ g₁
      have h₂₂: fz (fz ↑n) - (fz ↑n + ↑n) =
        (fz (fz ↑n) - G * fz ↑n) + (G - 1) * (fz ↑n - G * ↑n) := by
        rw [sub_mul, one_mul, mul_sub]
        rw [← mul_assoc G G, ← pow_two, h₀ n]
        ring_nf
      have h₂₃: |fz (fz ↑n) - (fz ↑n + (↑n:ℤ))| < 1 := by
        rw [← h₂₂] at h₂₁
        norm_cast at h₂₁
      have h₂₄: 0 ≤ |fz (fz ↑n) - (fz ↑n + (↑n:ℤ))| := by
        exact abs_nonneg (fz (fz ↑n) - (fz ↑n + (↑n:ℤ)))
      linarith
    rw [← hf₂ n, ← hf₂] at h₂
    norm_cast at h₂
  . intro m
    rw [hf₀]
    simp
    refine Int.natAbs_lt_natAbs_of_nonneg_of_lt ?h.right.right.w₁ ?h.right.right.w₂
    . exact h₁ m
    . rw [mul_add, mul_one]
      have g₀: round (G * ↑m + 1) ≤ round (G * ↑m + G) := by
        rw [round_eq, round_eq]
        refine Int.floor_le_floor ?_
        simp only [one_div, add_le_add_iff_right, add_le_add_iff_left]
        refine le_of_lt ?_
        exact Real.one_lt_goldenRatio
      refine lt_of_lt_of_le ?_ g₀
      rw [round_add_one]
      exact Int.lt_succ (round (G * (↑m:ℝ)))

snip end

problem imo1993_p5 :
    if DoesExist then ∃ f, Good f else ¬∃ f, Good f := by
  have h₀: ∃ f : ℕ → ℕ, f 1 = 2 ∧ (∀ n, f (f n) = f n + n) ∧ (∀ n, f n < f (n + 1)) := by
    exact imo_1993_p5_N
  obtain ⟨f₀, hf₀, hf₁, hf₂⟩ := h₀
  use f₀
  constructor
  . exact hf₀
  . exact fun n ↦ ⟨hf₁ n, hf₂⟩


end Imo1993P5
