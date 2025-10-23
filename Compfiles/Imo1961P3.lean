/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Tactic

import ProblemExtraction

problem_file {
  tags := [.Algebra]
  importedFrom := "https://github.com/leanprover-community/mathlib4/blob/master/Archive/Imo/Imo1961Q3.lean"
}

/-!
# International Mathematical Olympiad 1961, Problem 3

Solve the equation

  cosⁿ x - sinⁿ x = 1,

where n is a given positive integer.
-/

namespace Imo1961P3

open Real

determine solutionSet (n : ℕ+) : Set ℝ :=
 { x | (∃ k : ℤ, k * π = x) ∧ Even n.val ∨ (∃ k : ℤ, k * (2 * π) = x) ∧ Odd n.val ∨
          (∃ k : ℤ, -(π / 2) + k * (2 * π) = x) ∧ Odd n.val }

problem imo1961_p3 {n : ℕ} {x : ℝ} (npos : 0 < n) :
    x ∈ solutionSet ⟨n, npos⟩ ↔
    (cos x) ^ n - (sin x) ^ n = 1 := by
  -- This solution is based on
  -- https://artofproblemsolving.com/wiki/index.php/1961_IMO_Problems/Problem_3
  have h₀ : n ≠ 0 := Nat.ne_zero_of_lt npos
  constructor
  · rintro (⟨⟨k, rfl⟩, hn⟩ | ⟨⟨k, rfl⟩, -⟩ | ⟨⟨k, rfl⟩, hn⟩)
    · dsimp at hn
      rw [sin_int_mul_pi, zero_pow h₀, sub_zero, ← hn.pow_abs, abs_cos_int_mul_pi, one_pow]
    · have : sin (k * (2 * π)) = 0 := by simpa [mul_assoc] using sin_int_mul_pi (k * 2)
      simp [h₀, this]
    · dsimp at hn; simp [hn.neg_pow, h₀]
  · intro h
    rcases eq_or_ne (sin x) 0 with hsinx | hsinx
    · rw [hsinx, zero_pow h₀, sub_zero, pow_eq_one_iff_of_ne_zero h₀, cos_eq_one_iff,
        cos_eq_neg_one_iff] at h
      rcases h with ⟨k, rfl⟩ | ⟨⟨k, rfl⟩, hn⟩
      · cases n.even_or_odd with
        | inl hn => refine .inl ⟨⟨k * 2, ?_⟩, hn⟩; simp [mul_assoc]
        | inr hn => exact .inr <| .inl ⟨⟨_, rfl⟩, hn⟩
      · exact .inl ⟨⟨2 * k + 1, by push_cast; ring⟩, hn⟩
    · rcases eq_or_ne (cos x) 0 with hcosx | hcosx
      · right; right
        rw [hcosx, zero_pow h₀, zero_sub, ← neg_inj, neg_neg, pow_eq_neg_one_iff,
          sin_eq_neg_one_iff] at h
        exact h
      · have hcos1 : |cos x| < 1 := by
          rw [abs_cos_eq_sqrt_one_sub_sin_sq, sqrt_lt' one_pos]
          simp [sq_pos_of_ne_zero hsinx]
        have hsin1 : |sin x| < 1 := by
          rw [abs_sin_eq_sqrt_one_sub_cos_sq, sqrt_lt' one_pos]
          simp [sq_pos_of_ne_zero hcosx]
        match n with
        | 1 =>
          rw [pow_one, pow_one, sub_eq_iff_eq_add] at h
          have : 2 * sin x * cos x = 0 := by
            simpa [h, add_sq, add_assoc, ← two_mul, mul_add, mul_assoc, ← sq]
              using cos_sq_add_sin_sq x
          simp [hsinx, hcosx] at this
        | 2 =>
          rw [← cos_sq_add_sin_sq x, sub_eq_add_neg, add_right_inj, CharZero.neg_eq_self_iff] at h
          exact absurd (eq_zero_of_pow_eq_zero h) hsinx
        | (n + 1 + 2) =>
          set m := n + 1
          refine absurd ?_ h.not_lt
          calc
            (cos x) ^ (m + 2) - (sin x) ^ (m + 2) ≤ |cos x| ^ (m + 2) + |sin x| ^ (m + 2) := by
              simp only [← abs_pow, sub_eq_add_neg]
              gcongr
              exacts [le_abs_self _, neg_le_abs _]
            _ = |cos x| ^ m * cos x ^ 2 + |sin x| ^ m * sin x ^ 2 := by simp [pow_add]
            _ < 1 ^ m * cos x ^ 2 + 1 ^ m * sin x ^ 2 := by gcongr
            _ = 1 := by simp

end Imo1961P3
