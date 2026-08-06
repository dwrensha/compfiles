/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Int.Star
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Zify
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 1994, Problem 1

a₁, a₂, a₃, ... are positive integers such that aₙ > aₙ₋₁ + 1.
Put bₙ = a₁ + a₂ + ... + aₙ. Show that there is always a square in the
range bₙ, bₙ+1, bₙ+2, ... , bₙ₊₁-1.
-/

namespace Usa1994P1

snip begin

/-- If consecutive terms of `a` differ by more than one, then terms that are
`k` indices apart differ by at least `2 * k`. -/
lemma gap_lemma {a : ℕ → ℕ} (h : ∀ i, a i + 1 < a (i + 1)) (i k : ℕ) :
    a i + 2 * k ≤ a (i + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h1 := h (i + k)
      calc a i + 2 * (k + 1) = a i + 2 * k + 2 := by ring
        _ ≤ a (i + k) + 2 := Nat.add_le_add_right ih 2
        _ ≤ a (i + k + 1) := by omega
        _ = a (i + (k + 1)) := by rw [Nat.add_assoc]

/-- The sum of the first `n + 1` terms is at most
`(n + 1) * (a n + 1) - (n + 1)^2`; we state it in an addition-only form. -/
lemma sum_bound {a : ℕ → ℕ} (h : ∀ i, a i + 1 < a (i + 1)) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), a i) + (n + 1) * (n + 1) ≤
      (n + 1) * (a n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h2 : (n + 1) * (a n + 2) ≤ (n + 1) * a (n + 1) :=
        mul_le_mul_right (gap_lemma h n 1) (n + 1)
      rw [Finset.sum_range_succ]
      nlinarith [ih, h2]

/-- The key estimate: `4 * bₙ ≤ (aₙ + 1)²`. -/
lemma key {a : ℕ → ℕ} (h : ∀ i, a i + 1 < a (i + 1)) (n : ℕ) :
    4 * (∑ i ∈ Finset.range (n + 1), a i) ≤ (a n + 1) ^ 2 := by
  have h2 := sum_bound h n
  zify at h2 ⊢
  nlinarith [sq_nonneg ((a n : ℤ) + 1 - 2 * ((n : ℤ) + 1))]

snip end

problem usa1994_p1 (a : ℕ → ℕ) (ha : ∀ i, 0 < a i)
    (h : ∀ i, a i + 1 < a (i + 1)) (n : ℕ) (hn : 1 ≤ n) :
    ∃ m : ℕ, (∑ i ∈ Finset.range n, a i) ≤ m ^ 2 ∧
      m ^ 2 < ∑ i ∈ Finset.range (n + 1), a i := by
  -- We follow the informal proof from
  -- https://prase.cz/kalva/usa/usoln/usol941.html
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  -- Take `m₀` to be the integer square root of `b (k + 1)`.
  set m₀ := Nat.sqrt (∑ i ∈ Finset.range (k + 1), a i) with hm₀
  have hm₀le : m₀ ^ 2 ≤ ∑ i ∈ Finset.range (k + 1), a i := Nat.sqrt_le' _
  rcases eq_or_lt_of_le hm₀le with heq | hlt
  · -- If `b (k + 1)` is itself a square, we are done.
    refine ⟨m₀, le_of_eq heq.symm, ?_⟩
    rw [Finset.sum_range_succ, ← heq]
    exact Nat.lt_add_of_pos_right (ha (k + 1))
  · -- Otherwise `(m₀ + 1)²` lies in the required range.
    have hlt' : (∑ i ∈ Finset.range (k + 1), a i) < (m₀ + 1) ^ 2 := by
      have hs := Nat.lt_succ_sqrt' (∑ i ∈ Finset.range (k + 1), a i)
      rwa [← hm₀, Nat.succ_eq_add_one] at hs
    refine ⟨m₀ + 1, le_of_lt hlt', ?_⟩
    rw [Finset.sum_range_succ]
    -- It suffices to show `2 * m₀ ≤ a k + 1`, which follows from `key`.
    have h4 : 4 * m₀ ^ 2 ≤ (a k + 1) ^ 2 :=
      le_trans (mul_le_mul_right hm₀le 4) (key h k)
    have h2m₀ : 2 * m₀ ≤ a k + 1 := by
      by_contra! hcon
      have hsq : (a k + 2) ^ 2 ≤ (2 * m₀) ^ 2 :=
        Nat.pow_le_pow_left (by omega) 2
      nlinarith [h4, hsq, hcon]
    have hk : a k + 2 ≤ a (k + 1) := h k
    nlinarith [hlt]

end Usa1994P1
