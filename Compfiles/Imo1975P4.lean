/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Constantin Seebach
-/

import Mathlib
import ProblemExtraction


problem_file

/-!
# International Mathematical Olympiad 1975, Problem 4

When $4444^{4444}$ is written in decimal notation, the sum of its digits is $A$.
Let $B$ be the sum of the digits of $A$.
Find the sum of the digits of $B$. ($A$ and $B$ are written in decimal notation.)
-/

namespace Imo1975P4

def A : ℕ := (Nat.digits 10 (4444^4444)).sum

def B : ℕ := (Nat.digits 10 A).sum

determine sum_digits_B : ℕ := 7

snip begin

/-!
We follow the proof from https://prase.cz/kalva/imo/isoln/isoln754.html
-/

/-!
I'd love to have the following theorems in Mathlib :)
-/

theorem Nat.mod_eq_iff_eq {n a b : ℕ} (h : a < n) :
    a % n = b ↔ a = b := by
  rw [(Nat.mod_eq_iff_lt _).mpr h]
  exact Nat.ne_zero_of_lt h

theorem Nat.modEq_iff_eq_lt (n : ℕ) {a b : ℕ} (ha : a < n) (hb : b < n) :
    a ≡ b [MOD n] ↔ a = b := by
  rw [Nat.ModEq]
  rw [(Nat.mod_eq_iff_lt _).mpr hb]
  · exact mod_eq_iff_eq ha
  · exact Nat.ne_zero_of_lt hb


theorem Nat.digits_sum_le_mul_digits_length (n b : ℕ) (hb : 1 < b) : (Nat.digits b n).sum ≤ (Nat.digits b n).length * (b-1) := by
  apply List.sum_le_card_nsmul
  intro x xh
  rw [Nat.le_sub_one_iff_lt (Nat.zero_lt_of_lt hb)]
  apply Nat.digits_lt_base hb xh

theorem Nat.digits_sum_le_log (n b : ℕ) (hn : n ≠ 0) (hb : 1 < b) : (Nat.digits b n).sum ≤ (Nat.log b n + 1) * (b-1) := by
  rw [<-Nat.digits_len _ _ hb hn]
  exact digits_sum_le_mul_digits_length n b hb

theorem Nat.digits_sum_le_of_le (n b u : ℕ) (hb : 1 < b) (hn : n ≤ u) : (Nat.digits b n).sum ≤ (Nat.clog b u + 1) * (b-1) := by
  by_cases nz : n = 0
  · subst n
    simp
  trans (Nat.log b n + 1) * (b-1)
  · apply Nat.digits_sum_le_log _ _ nz hb
  · rw [mul_le_mul_iff_left₀ (by lia), add_le_add_iff_right]
    apply le_trans (Nat.log_le_clog _ _)
    apply Nat.clog_mono_right _ hn


theorem Nat.clog_pow_le_clog_mul (a b c : ℕ) (hb : 1 < b) : Nat.clog b (a ^ c) ≤ Nat.clog b a * c := by
  by_cases hc : c = 0
  · subst c
    simp
  rw [Nat.clog_le_iff_le_pow hb, pow_mul, Nat.pow_le_pow_iff_left hc]
  apply Nat.le_pow_clog hb

snip end


problem imo1975_p4 : sum_digits_B = (Nat.digits 10 B).sum := by

  have sumBmod : sum_digits_B ≡ 4444 ^ 4444 [MOD 9] := by
    rw [Nat.ModEq, Nat.pow_mod]
    rw [show 4444%9 = 7 by simp]
    rw [show 4444 = 3*1481+1 by simp]
    simp only [pow_add, pow_mul, pow_one]
    rw [Nat.mul_mod, Nat.pow_mod]
    simp only [show 7 ^ 3 % 9 = 1 by simp, one_pow]
    unfold sum_digits_B
    rfl
  have sumBmod' : (Nat.digits 10 B).sum ≡ 4444 ^ 4444 [MOD 9] := by
    unfold B A
    rw [Nat.ModEq, Eq.comm]
    iterate 3 rw [Nat.modEq_nine_digits_sum]
  have sumBmod'' : (Nat.digits 10 B).sum ≡ sum_digits_B [MOD 9] := by
    grw [sumBmod, sumBmod']

  have : A ≤ 159993 := by
    unfold A
    apply le_trans (Nat.digits_sum_le_of_le _ _ _ (by simp) le_rfl)
    calc
      _ ≤ (Nat.clog 10 4444 * 4444 + 1) * 9 := by
        simp only [Nat.add_one_sub_one, Nat.ofNat_pos, mul_le_mul_iff_left₀, add_le_add_iff_right]
        apply Nat.clog_pow_le_clog_mul
        simp
      _ = (4 * 4444 + 1) * 9 := by
        rfl
      _ = _ := by
        rfl
  have : B ≤ 63 := by
    unfold B
    apply le_trans (Nat.digits_sum_le_of_le _ _ _ (by simp) this)
    rfl

  generalize B = x at ⊢ this sumBmod''
  revert x
  decide

end Imo1975P4
