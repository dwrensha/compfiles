/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Defs
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.LinearCombination
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 1986, Problem 3

What is the smallest n > 1 for which the average of the first n
(non-zero) squares is a square?
-/

namespace Usa1986P3

determine solution : ℕ := 337

snip begin

/-- Six times the sum of the first `n` non-zero squares. -/
lemma six_mul_sum_sq (n : ℕ) :
    6 * ∑ i ∈ Finset.range n, (i + 1)^2 = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    ring

/-- The `GCDMonoid` gcd of coprime naturals is a unit. -/
lemma isUnit_gcd_of_coprime {a b : ℕ} (h : Nat.Coprime a b) : IsUnit (gcd a b) := by
  have h1 : gcd a b = 1 := by
    rw [gcd_eq_nat_gcd]
    exact h
  rw [h1]
  exact isUnit_one

/-- If coprime naturals have a square product, the left factor is a square. -/
lemma eq_sq_of_coprime_mul_eq_sq {a b k : ℕ} (hcop : Nat.Coprime a b)
    (h : a * b = k^2) : ∃ u, a = u^2 :=
  exists_eq_pow_of_mul_eq_pow (isUnit_gcd_of_coprime hcop) h

/-- Finite check: the Pell-type equation `4u² = 3w² + 1` has no solution
with `2 ≤ u ≤ 12` and `w ≤ 13`. -/
lemma no_small_solution :
    ∀ u < 13, ∀ w < 14, 2 ≤ u → 4 * u^2 ≠ 3 * w^2 + 1 := by
  decide

/-- Minimality: if `n > 1` and `(n+1)(2n+1) = 6m²`, then `337 ≤ n`. -/
lemma ge_337 {n m : ℕ} (hn : 1 < n) (h : (n+1) * (2*n+1) = 6 * m^2) :
    337 ≤ n := by
  by_contra hlt
  have hlt' : n < 337 := by omega
  clear hlt
  have cop : Nat.Coprime (n+1) (2*n+1) := by
    rw [← Nat.isCoprime_iff_coprime]
    exact ⟨2, -1, by push_cast; ring⟩
  by_cases h3 : 3 ∣ n + 1
  · -- Case `3 ∣ n+1`: then `n+1 = 6u²` and `2n+1 = w²`, impossible modulo 4.
    obtain ⟨a, ha⟩ := h3
    rw [ha] at h
    have h1 : a * (2*n+1) = 2 * m^2 := by
      have e : 3 * (a * (2*n+1)) = 3 * (2 * m^2) := by linear_combination h
      exact mul_left_cancel₀ (by norm_num : (3:ℕ) ≠ 0) e
    have h2a : 2 ∣ a := by
      have h2dvd : 2 ∣ a * (2*n+1) := ⟨m^2, h1⟩
      rcases Nat.prime_two.dvd_mul.mp h2dvd with hA | hB
      · exact hA
      · omega
    obtain ⟨b, hb⟩ := h2a
    rw [hb] at h1
    have h2 : b * (2*n+1) = m^2 := by
      have e : 2 * (b * (2*n+1)) = 2 * m^2 := by linear_combination h1
      exact mul_left_cancel₀ (by norm_num : (2:ℕ) ≠ 0) e
    have hdvd6 : b ∣ n + 1 := ⟨6, by rw [ha, hb]; ring⟩
    have cop2 : Nat.Coprime b (2*n+1) := cop.coprime_dvd_left hdvd6
    obtain ⟨u, hu⟩ := eq_sq_of_coprime_mul_eq_sq cop2 h2
    obtain ⟨w, hw⟩ := eq_sq_of_coprime_mul_eq_sq cop2.symm (by rwa [mul_comm])
    have hnA : n + 1 = 6 * u^2 := by
      rw [ha, hb, hu]; ring
    have hw2 : w^2 + 1 = 12 * u^2 := by omega
    have hcast : (w : ZMod 4)^2 + 1 = 0 := by
      have h' : ((w^2 + 1 : ℕ) : ZMod 4) = ((12 * u^2 : ℕ) : ZMod 4) := by
        rw [hw2]
      push_cast at h'
      have h12 : (12 : ZMod 4) = 0 := by decide
      rwa [h12, zero_mul] at h'
    exact absurd hcast ((by decide : ∀ x : ZMod 4, x^2 + 1 ≠ 0) w)
  · -- Case `3 ∤ n+1`: then `3 ∣ 2n+1`, so `n+1 = 2u²` and `2n+1 = 3w²`,
    -- hence `4u² = 3w² + 1`, which has no solution below `u = 13`.
    have h3B : 3 ∣ 2*n+1 := by
      have h3dvd : 3 ∣ (n+1) * (2*n+1) := by
        rw [h]
        exact ⟨2 * m^2, by ring⟩
      rcases Nat.prime_three.dvd_mul.mp h3dvd with hA | hB
      · exact absurd hA h3
      · exact hB
    obtain ⟨b₁, hb₁⟩ := h3B
    rw [hb₁] at h
    have hdvd3 : b₁ ∣ 2*n+1 := ⟨3, by rw [hb₁]; ring⟩
    have h1 : (n+1) * b₁ = 2 * m^2 := by
      have e : 3 * ((n+1) * b₁) = 3 * (2 * m^2) := by linear_combination h
      exact mul_left_cancel₀ (by norm_num : (3:ℕ) ≠ 0) e
    have h2a : 2 ∣ n+1 := by
      have h2dvd : 2 ∣ (n+1) * b₁ := ⟨m^2, h1⟩
      rcases Nat.prime_two.dvd_mul.mp h2dvd with hA | hB
      · exact hA
      · have h2B₁ : 2 ∣ 2*n+1 := dvd_trans hB hdvd3
        omega
    obtain ⟨a₁, ha₁⟩ := h2a
    rw [ha₁] at h1
    have h2 : a₁ * b₁ = m^2 := by
      have e : 2 * (a₁ * b₁) = 2 * m^2 := by linear_combination h1
      exact mul_left_cancel₀ (by norm_num : (2:ℕ) ≠ 0) e
    have hdvd2 : a₁ ∣ n + 1 := ⟨2, by rw [ha₁]; ring⟩
    have cop2 : Nat.Coprime a₁ b₁ :=
      (cop.coprime_dvd_left hdvd2).coprime_dvd_right hdvd3
    obtain ⟨u, hu⟩ := eq_sq_of_coprime_mul_eq_sq cop2 h2
    obtain ⟨w, hw⟩ := eq_sq_of_coprime_mul_eq_sq cop2.symm (by rwa [mul_comm])
    have hnA : n + 1 = 2 * u^2 := by
      rw [ha₁, hu]
    have hnB : 2*n+1 = 3 * w^2 := by
      rw [hb₁, hw]
    have hu2 : 2 ≤ u := by
      by_contra hc
      have hult : u < 2 := by omega
      interval_cases u <;> omega
    have hrel : 4 * u^2 = 3 * w^2 + 1 := by omega
    have hu12 : u ≤ 12 := by
      by_contra hc
      have h13 : 13 ≤ u := by omega
      have h169 : 13^2 ≤ u^2 := Nat.pow_le_pow_left h13 2
      omega
    have hw13 : w ≤ 13 := by
      by_contra hc
      have h14 : 14 ≤ w := by omega
      have h196 : 14^2 ≤ w^2 := Nat.pow_le_pow_left h14 2
      have hu144 : u^2 ≤ 12^2 := Nat.pow_le_pow_left hu12 2
      omega
    exact no_small_solution u (by omega) w (by omega) hu2 hrel

snip end

problem usa1986_p3 :
    IsLeast {n : ℕ | 1 < n ∧ ∃ m, ∑ i ∈ Finset.range n, (i+1)^2 = n * m^2}
      solution := by
  constructor
  · refine ⟨by norm_num [solution], 195, ?_⟩
    show ∑ i ∈ Finset.range 337, (i+1)^2 = 337 * 195^2
    have h6 : 6 * (∑ i ∈ Finset.range 337, (i+1)^2) = 6 * (337 * 195^2) := by
      rw [six_mul_sum_sq]
      norm_num
    exact mul_left_cancel₀ (by norm_num) h6
  · rw [mem_lowerBounds]
    intro n hn
    obtain ⟨hn1, m, hm⟩ := hn
    have h6 := six_mul_sum_sq n
    rw [hm] at h6
    have h : (n+1) * (2*n+1) = 6 * m^2 := by
      have h6' : n * (6 * m^2) = n * ((n+1) * (2*n+1)) := by
        linear_combination h6
      exact (mul_left_cancel₀ (by omega : n ≠ 0) h6').symm
    exact ge_337 hn1 h

end Usa1986P3
