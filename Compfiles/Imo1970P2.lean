/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra, .Inequality] }

/-!
# International Mathematical Olympiad 1970, Problem 2

Let a, b and n be integers greater than 1, and let a and b be the bases of two
number systems. A_{n-1} and A_n are numbers in the system with base a, and
B_{n-1} and B_n are numbers in the system with base b; these are related as
follows:

  A_n     = x_n x_{n-1} ⋯ x_0,   A_{n-1} = x_{n-1} x_{n-2} ⋯ x_0,
  B_n     = x_n x_{n-1} ⋯ x_0,   B_{n-1} = x_{n-1} x_{n-2} ⋯ x_0,

(written as digit strings in the respective systems) with x_n ≠ 0 and
x_{n-1} ≠ 0.

Prove that A_{n-1}/A_n < B_{n-1}/B_n if and only if a > b.
-/

namespace Imo1970P2

/-- The real number whose base-`c` digit string is `x m, x (m-1), ..., x 0`,
i.e. `∑ i ≤ m, x i * c ^ i`. -/
def value (x : ℕ → ℕ) (c : ℕ) (m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (m + 1), (x i : ℝ) * (c : ℝ) ^ i

snip begin

/-- For `i < n` and `b < a` we have `bⁿ aⁱ < aⁿ bⁱ`. -/
lemma pow_cross_lt {a b : ℕ} (hb : 1 < b) (hab : b < a) {i n : ℕ} (hin : i < n) :
    (b : ℝ) ^ n * (a : ℝ) ^ i < (a : ℝ) ^ n * (b : ℝ) ^ i := by
  have hb0 : (0 : ℝ) < (b : ℝ) := Nat.cast_pos.mpr (by omega)
  have ha0 : (0 : ℝ) < (a : ℝ) := Nat.cast_pos.mpr (by omega)
  have hpow : (b : ℝ) ^ (n - i) < (a : ℝ) ^ (n - i) :=
    pow_lt_pow_left₀ (by exact_mod_cast hab) hb0.le (by omega)
  have hsplit : ∀ {c : ℕ}, (c : ℝ) ^ n = (c : ℝ) ^ (n - i) * (c : ℝ) ^ i := by
    intro c
    rw [← pow_add, Nat.sub_add_cancel hin.le]
  rw [hsplit, hsplit]
  have hpos : (0 : ℝ) < (a : ℝ) ^ i * (b : ℝ) ^ i :=
    mul_pos (pow_pos ha0 i) (pow_pos hb0 i)
  calc (b : ℝ) ^ (n - i) * (b : ℝ) ^ i * (a : ℝ) ^ i
      = (b : ℝ) ^ (n - i) * ((a : ℝ) ^ i * (b : ℝ) ^ i) := by ring
    _ < (a : ℝ) ^ (n - i) * ((a : ℝ) ^ i * (b : ℝ) ^ i) :=
        mul_lt_mul_of_pos_right hpow hpos
    _ = (a : ℝ) ^ (n - i) * (a : ℝ) ^ i * (b : ℝ) ^ i := by ring

/-- Splitting off the leading digit: `value x c n = value x c (n-1) + x n * cⁿ`. -/
lemma value_succ (x : ℕ → ℕ) (c n : ℕ) (hn : 1 ≤ n) :
    value x c n = value x c (n - 1) + (x n : ℝ) * (c : ℝ) ^ n := by
  simp only [value, Nat.sub_add_cancel hn, Finset.sum_range_succ]

/-- The full number is positive since its leading digit is nonzero. -/
lemma value_pos (x : ℕ → ℕ) {c n : ℕ} (hc : 1 < c) (hn : 1 ≤ n) (hxn : x n ≠ 0) :
    0 < value x c n := by
  rw [value_succ x c n hn]
  have h1 : (0 : ℝ) ≤ value x c (n - 1) := by
    simp only [value]
    exact Finset.sum_nonneg
      fun i _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)
  positivity

/-- The crux: `bⁿ · B' < aⁿ · A'`, where `A'` and `B'` are the numbers obtained
by stripping the leading digit. Each term of `bⁿ · A'` is at most the matching
term of `aⁿ · B'`, and the `i = n-1` term is strict since `x_{n-1} ≠ 0`. -/
lemma pow_mul_value_lt (x : ℕ → ℕ) {a b n : ℕ} (hb : 1 < b) (hab : b < a)
    (hn : 1 ≤ n) (hxn1 : x (n - 1) ≠ 0) :
    (b : ℝ) ^ n * value x a (n - 1) < (a : ℝ) ^ n * value x b (n - 1) := by
  have hnn : n - 1 < n := by omega
  simp only [value, Finset.mul_sum, Nat.sub_add_cancel hn]
  apply Finset.sum_lt_sum
  · intro i hi
    rw [Finset.mem_range] at hi
    calc (b : ℝ) ^ n * ((x i : ℝ) * (a : ℝ) ^ i)
        = (x i : ℝ) * ((b : ℝ) ^ n * (a : ℝ) ^ i) := by ring
      _ ≤ (x i : ℝ) * ((a : ℝ) ^ n * (b : ℝ) ^ i) :=
          mul_le_mul_of_nonneg_left (pow_cross_lt hb hab hi).le (Nat.cast_nonneg _)
      _ = (a : ℝ) ^ n * ((x i : ℝ) * (b : ℝ) ^ i) := by ring
  · refine ⟨n - 1, Finset.mem_range.mpr hnn, ?_⟩
    calc (b : ℝ) ^ n * ((x (n - 1) : ℝ) * (a : ℝ) ^ (n - 1))
        = (x (n - 1) : ℝ) * ((b : ℝ) ^ n * (a : ℝ) ^ (n - 1)) := by ring
      _ < (x (n - 1) : ℝ) * ((a : ℝ) ^ n * (b : ℝ) ^ (n - 1)) :=
          mul_lt_mul_of_pos_left (pow_cross_lt hb hab hnn)
            (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hxn1))
      _ = (a : ℝ) ^ n * ((x (n - 1) : ℝ) * (b : ℝ) ^ (n - 1)) := by ring

/-- Cross-multiplied form of the inequality: `A' · B < B' · A`. Indeed,
`B' · A - A' · B = x n * (aⁿ · B' - bⁿ · A') > 0`. -/
lemma value_mul_lt (x : ℕ → ℕ) {a b n : ℕ} (hb : 1 < b) (hn : 1 ≤ n)
    (hxn : x n ≠ 0) (hxn1 : x (n - 1) ≠ 0) (hab : b < a) :
    value x a (n - 1) * value x b n < value x b (n - 1) * value x a n := by
  rw [value_succ x a n hn, value_succ x b n hn]
  have key := pow_mul_value_lt x hb hab hn hxn1
  have hmul : (x n : ℝ) * ((b : ℝ) ^ n * value x a (n - 1))
      < (x n : ℝ) * ((a : ℝ) ^ n * value x b (n - 1)) :=
    mul_lt_mul_of_pos_left key (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hxn))
  linarith [hmul]

/-- If `b < a` then `A'/A < B'/B`. -/
lemma value_div_lt (x : ℕ → ℕ) {a b n : ℕ} (ha : 1 < a) (hb : 1 < b) (hn : 1 ≤ n)
    (hxn : x n ≠ 0) (hxn1 : x (n - 1) ≠ 0) (hab : b < a) :
    value x a (n - 1) / value x a n < value x b (n - 1) / value x b n := by
  rw [div_lt_div_iff₀ (value_pos x ha hn hxn) (value_pos x hb hn hxn)]
  exact value_mul_lt x hb hn hxn hxn1 hab

snip end

problem imo1970_p2 (a b n : ℕ) (ha : 1 < a) (hb : 1 < b) (hn : 1 < n) (x : ℕ → ℕ)
    (hdig : ∀ i ≤ n, x i < min a b) (hxn : x n ≠ 0) (hxn1 : x (n - 1) ≠ 0) :
    value x a (n - 1) / value x a n < value x b (n - 1) / value x b n ↔ b < a := by
  constructor
  · intro h
    rcases lt_trichotomy b a with hab | hab | hab
    · exact hab
    · subst hab
      exact absurd h (lt_irrefl _)
    · exact absurd (h.trans (value_div_lt x hb ha hn.le hxn hxn1 hab)) (lt_irrefl _)
  · exact value_div_lt x ha hb hn.le hxn hxn1

end Imo1970P2
