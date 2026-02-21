/-
Copyright (c) 2025 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shalev Wengrowsky
-/

import Mathlib.Tactic
import Mathlib.Tactic.NthRewrite
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fin.Basic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 1989, Problem 1

For each positive integer n, let
  Sn = 1 + 1/2 + 1/3 + ··· + 1/n
  Tn = S1 + S2 + S3 + ··· + Sn
  Un = T1/2 + T2/3 + T3/4 + ··· + Tn/(n+1)
Find, with proof, integers 0 < a, b, c, d < 1000000 such that
  T1988 = a * S1989 - b
  U1988 = c * S1989 - d
-/

namespace Usa1989P1

def s (n : ℕ) : ℚ := ∑i ∈ Finset.Icc 1 n, 1 / i
def t (n : ℕ) : ℚ := ∑i ∈ Finset.Icc 1 n, s i
def u (n : ℕ) : ℚ := ∑i ∈ Finset.Icc 1 n, t i / (i + 1)

snip begin
-- based on solution from
-- https://artofproblemsolving.com/wiki/index.php/1989_USAMO_Problems/Problem_1

def extract_one {n : ℕ} {f : ℕ → ℚ} :
    (Finset.Icc 1 (n + 1)).sum f = f (n + 1) + (Finset.Icc 1 n).sum f := by
  rw [← Finset.insert_Icc_right_eq_Icc_add_one (by simp)]
  rw [Finset.sum_insert (by simp)]



lemma l1 (n : ℕ) : t (n - 1) = n * s n - n := by
  induction n with
  | zero => simp [t]
  | succ n ih =>
    by_cases h : n = 0
    · simp [t, s, h]
    · rw [Nat.sub_add_comm (Nat.one_le_iff_ne_zero.mpr h)]
      rw [t, extract_one, ← t]
      have h1 : ↑(n + 1) * s (n + 1) = s n + n * s n + 1 := by
        rw [s, extract_one, ← s]
        rw [mul_add, mul_one_div_cancel (by apply NeZero.ne)]
        grind
      grind [t]

lemma l2 (n : ℕ) : u (n - 1) = (n + 1) * s n - 2 * n := by
  induction n with
  | zero => simp [u, t, s]
  | succ n ih =>
    by_cases h : n = 0
    · simp [u, s, h]; ring
    · rw [Nat.sub_add_comm (Nat.one_le_iff_ne_zero.mpr h), u, extract_one, ← u]
      rw [ih]
      rw [← Nat.sub_add_comm (Nat.one_le_iff_ne_zero.mpr h), l1]
      rw [(by rfl : n + 1 - 1 = n), ← Nat.cast_add_one]
      nth_rewrite 2 [← mul_one ((@Nat.cast ℚ Rat.instNatCast) (n + 1))]
      rw [← mul_sub, mul_comm, Rat.mul_div_cancel (by apply NeZero.ne)]
      rw [add_mul]
      nth_rewrite 3 [s]
      rw [extract_one, ← s, mul_add, mul_one_div_cancel (by apply NeZero.ne)]
      grind

snip end

determine solutions : (ℕ × ℕ × ℕ × ℕ) := (1989, 1989, 1990, 2*1989)

problem usa1989_p1 :
    t 1988 = solutions.1 * s 1989 - solutions.2.1 ∧
    u 1988 = solutions.2.2.1 * s 1989 - solutions.2.2.2 := by
  unfold solutions
  simp
  constructor
  · change t (1989 - 1) = 1989 * s 1989 - 1989
    exact l1 1989
  · change u (1989 - 1) = 1990 * s 1989 - 3978
    rw [(by grind : (3978:ℚ) = 2 * 1989)]
    rw [l2 1989]
    simp
    left
    ring


end Usa1989P1
