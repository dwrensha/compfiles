/-
Copyright (c) 2025 lean-tom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-tom (with assistance from Gemini)
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

import ProblemExtraction

open Nat BigOperators Finset

problem_file

/-!
# International Mathematical Olympiad 1968, Problem 6

For every natural number n, evaluate the sum
∑_{k=0}^{∞} [(n + 2^k) / 2^(k+1)]
where [x] denotes the greatest integer less than or equal to x.

The answer is n.
-/

namespace Imo1968P6

snip begin

-- Lemma for the telescoping term structure
lemma term_telescope (n k : ℕ) :
    (n + 2^k) / 2^(k+1) = n / 2^k - n / 2^(k+1) := by
  rw [pow_succ, ← Nat.div_div_eq_div_mul]
  have h_pos : 0 < 2^k := pow_pos (by norm_num) k
  rw [Nat.add_div_right n h_pos]
  -- Use the identity (a + 1) / 2 = a - a / 2
  have identity (a : ℕ) : (a + 1) / 2 = a - a / 2 := by omega
  rw [identity]
  rw [Nat.div_div_eq_div_mul, ← pow_succ]

snip end

problem imo1968_p6 (n : ℕ) : ∑' k, (n + 2^k) / 2^(k+1) = determine n_ans n := by
  determine n_ans n
  -- We truncate the sum at k_max = n + 1, since terms are zero afterwards.
  let k_max := n + 1

  have sum_eq_finite : ∑' k, (n + 2^k) / 2^(k+1) = ∑ k ∈ range k_max, (n + 2^k) / 2^(k+1) := by
    apply tsum_eq_sum
    intro k hk
    simp only [mem_range, not_lt] at hk
    apply Nat.div_eq_of_lt
    calc
      n + 2^k < 2^k + 2^k := by
        apply add_lt_add_left
        calc
          n < 2^n := n.lt_two_pow_self
          _ < 2^(n + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
          _ ≤ 2^k_max := le_refl _
          _ ≤ 2^k := Nat.pow_le_pow_right (by norm_num) hk
      _ = 2^(k+1) := by rw [pow_succ, mul_two]
  rw [sum_eq_finite]

  -- Rewrite the sum using the telescoping lemma
  have sum_rewrite : ∑ k ∈ range k_max, (n + 2^k) / 2^(k+1) =
                     ∑ k ∈ range k_max, (n / 2^k - n / 2^(k+1)) := by
    apply sum_congr rfl
    intro k hk
    rw [term_telescope]
  rw [sum_rewrite]

  -- Prove the telescoping sum formula for natural numbers (requiring decreasing terms)
  have telescoping (m : ℕ) : ∑ k ∈ range m, (n / 2^k - n / 2^(k+1)) = n - n / 2^m := by
    induction m with
    | zero => simp
    | succ m hm =>
      rw [sum_range_succ, hm, Nat.sub_add_sub_cancel]
      · apply Nat.div_le_self
      · gcongr
        · norm_num
        · norm_num

  rw [telescoping k_max]

  -- Show that the remainder term is zero
  have term_vanish : n / 2^k_max = 0 := by
    apply Nat.div_eq_of_lt
    calc
      n < 2^n := n.lt_two_pow_self
      _ < 2^(n+1) := Nat.pow_lt_pow_right (by norm_num) (by omega)

  rw [term_vanish, Nat.sub_zero]

end Imo1968P6
