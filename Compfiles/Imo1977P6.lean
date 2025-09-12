/-
Copyright (c) 2021 Tian Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tian Chen
-/
import Mathlib.Data.PNat.Basic

import ProblemExtraction

problem_file {
  tags := [.Algebra],
  importedFrom :=
    "https://github.com/leanprover-community/mathlib4/blob/master/Archive/Imo/Imo1977Q6.lean",
}

/-!
# International Mathematical Olympiad 1977, Problem 6

Suppose `f : ℕ+ → ℕ+` satisfies `f(f(n)) < f(n + 1)` for all `n`.
Prove that `f(n) = n` for all `n`.
-/

namespace Imo1977P6

snip begin

/-
We first prove the problem statement for `f : ℕ → ℕ`
then we use it to prove the statement for positive naturals.
-/

theorem imo1977_p6_nat (f : ℕ → ℕ) (h : ∀ n, f (f n) < f (n + 1)) : ∀ n, f n = n := by
  have h' : ∀ k n : ℕ, k ≤ n → k ≤ f n := by
    intro k
    induction k with
    | zero => intros; exact Nat.zero_le _
    | succ k h_ind =>
      intro n hk
      apply Nat.succ_le_of_lt
      calc
        k ≤ f (f (n - 1)) := h_ind _ (h_ind (n - 1) (le_tsub_of_add_le_right hk))
        _ < f n := tsub_add_cancel_of_le (le_trans (Nat.succ_le_succ (Nat.zero_le _)) hk) ▸ h _
  have hf : ∀ n, n ≤ f n := fun n => h' n n rfl.le
  have hf_mono : StrictMono f := strictMono_nat_of_lt_succ fun _ => lt_of_le_of_lt (hf _) (h _)
  intro
  exact Nat.eq_of_le_of_lt_succ (hf _) (hf_mono.lt_iff_lt.mp (h _))

snip end

problem imo1977_p6 (f : ℕ+ → ℕ+) (h : ∀ n, f (f n) < f (n + 1)) : ∀ n, f n = n := by
  intro n
  have := by
    refine imo1977_p6_nat (fun m => if 0 < m then f m.toPNat' else 0) ?_ n
    intro x; cases x
    · simp
    · simpa using h _
  simpa


end Imo1977P6
