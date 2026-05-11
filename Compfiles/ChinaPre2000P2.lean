/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: sjfhsjfh & deepseek-v4-pro@claude-code
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# China Pre-CMO (National High School Math League, Second Round) 2000, Problem 2

设数列 {aₙ} 和 {bₙ} 满足 a₀ = 1, b₀ = 0，且
  ⎧ aₙ₊₁ = 7aₙ + 6bₙ − 3
  ⎨
  ⎩ bₙ₊₁ = 8aₙ + 7bₙ − 4  , n = 0,1,2,…
证明：aₙ（n = 0,1,2,…）是完全平方数。

Define the sequences `a_n` and `b_n` for `n ≥ 0` by
`a_0 = 1`, `a_1 = 4`, `a_2 = 49`, and for `n ≥ 0`:
`a_{n+1} = 7a_n + 6b_n - 3`,
`b_{n+1} = 8a_n + 7b_n - 4`.
Prove that for any non-negative integer `n`, `a_n` is a perfect square.
-/

namespace ChinaPre2000P2

snip begin

def c : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | n + 2 => 4 * c (n + 1) - c n

lemma c_rec (n : ℕ) : c (n + 2) = 4 * c (n + 1) - c n := rfl

lemma c_sq_identity (n : ℕ) : c (n + 1) ^ 2 = 4 * c (n + 1) * c n - c n ^ 2 - 3 := by
  induction' n with k ih
  · norm_num [c]
  · rw [c_rec k]
    nlinarith

snip end

problem chinaPre2000_p2 (a b : ℕ → ℤ) (ha0 : a 0 = 1)
  (ha1 : a 1 = 4) (ha2 : a 2 = 49)
  (ha_rec : ∀ n, a (n + 1) = 7 * a n + 6 * b n - 3)
  (hb_rec : ∀ n, b (n + 1) = 8 * a n + 7 * b n - 4)
  : ∀ n, ∃ k : ℤ, a n = k ^ 2 := by
  have _ := ha2 -- Fix the unused warning
  have hb0 : b 0 = 0 := by
    have := sub_eq_zero_of_eq (ha_rec 0).symm
    conv at this => rewrite [ha0, ha1]; ring_nf
    exact mul_eq_zero_iff_right (by norm_num) |>.mp this
  have : ∀ n, a n = c n ^ 2 ∧ 3 * b n = 2 * c n * (c (n + 1) - 2 * c n) := by
    intro n; induction' n with m ih
    · rewrite [ha0, hb0]; norm_num [c]
    obtain ⟨iha, ihb⟩ := ih
    rewrite [c_rec, ha_rec m, hb_rec m, iha, mul_sub (2 * c (m + 1)),
      mul_mul_mul_comm, ← sq (c (m + 1)), c_sq_identity m]
    refine ⟨?ia, ?ib⟩
    case ia =>  apply eq_of_sub_eq_zero
                rewrite [show (6 : ℤ) = 2 * 3 by norm_num, mul_assoc, ihb]; ring
    apply eq_of_sub_eq_zero
    ring_nf; rewrite [show (21 : ℤ) = 3 * 7 by norm_num, ← mul_assoc (b m),
      mul_comm (b m) 3, ihb, add_comm 1 m, c_sq_identity m]; ring
  intro n; use c n; exact this n |>.left

end ChinaPre2000P2
