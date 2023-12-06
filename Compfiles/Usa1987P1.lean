/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic

import ProblemExtraction

problem_file

/-!
# USA Mathematical Olympiad 1987, Problem 1

Determine all solutions to

     (m² + n)(m + n²) = (m - n)³

where m and n are non-zero integers.
-/

namespace Usa1987P1

snip begin

lemma lemma2 {a b c : ℤ} (h : a * b^2 = c^2) : IsSquare a ∨ b = 0 := by
  obtain rfl | hb := eq_or_ne b 0
  · simp
  simp only [hb, or_false]
  -- from Eric Wieser on Zulip
  -- https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/a.20*.20b.5E2.20.3D.20c.5E2.20implies.20IsSquare.20a/near/406203283
  have h1 : b^2 ∣ c^2 := Dvd.intro_left a h
  rw [Int.pow_dvd_pow_iff two_pos] at h1
  obtain ⟨k, rfl⟩ := h1
  rw [mul_pow, mul_comm, mul_right_inj' (pow_ne_zero _ hb)] at h
  rw [h]
  exact ⟨k, sq k⟩

snip end

determine solution_set : Set (ℤ × ℤ) :=
  { (-1, -1), (8, -10), (9, -6), (9, -21) }

problem usa2001_p1 (m n : ℤ) :
    (m, n) ∈ solution_set ↔
    m ≠ 0 ∧ n ≠ 0 ∧ (m^2 + n) * (m + n^2) = (m - n)^3 := by
  -- Follows the informal solution at
  -- https://artofproblemsolving.com/wiki/index.php/1987_USAMO_Problems/Problem_1
  constructor
  · aesop
  · rintro ⟨h1, h2, h3⟩
    have h4 : n * (m  + m^2 * n + n^2) =
              n * (- 3* m^2 + 3 * m * n - n^2) := by linear_combination h3
    replace h4 : (m  + m^2 * n + n^2) =
              (- 3 * m^2 + 3 * m * n - n^2) := (Int.mul_eq_mul_left_iff h2).mp h4
    have h5 : 2 * n * n  + (m^2 - 3 * m) * n + (3 * m^2 + m) = 0 := by
      linarith
    have h6 := (quadratic_eq_zero_iff_discrim_eq_sq two_ne_zero n).mp h5
    have h7 : discrim 2 (m ^ 2 - 3 * m) (3 * m ^ 2 + m) =
              m * (m - 8) * (m + 1)^2 := by rw [discrim]; ring
    rw [h7] at h6; clear h7
    have h8 : IsSquare (m * (m - 8)) ∨ m + 1 = 0 := lemma2 h6
    obtain rfl | hm := eq_or_ne m (-1)
    · norm_num at h6
      obtain rfl : n = -1 := by linarith [pow_eq_zero h6.symm]
      simp
    obtain rfl | hm8 := eq_or_ne m 8
    · norm_num at h6
      obtain rfl : n = -10 := by linarith [pow_eq_zero h6.symm]
      simp

    have h9 : m + 1 ≠ 0 := by intro hm1
                              have : m = -1 := by linarith
                              contradiction
    replace h8 := Or.resolve_right h8 h9
    obtain ⟨k, hk⟩ := h8
    have h10 : (m - 4 + k) * (m - 4 - k) = 16 := by linarith
    sorry
