/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra, .Inequality] }

/-!
Canadian Mathematical Olympiad 1998, Problem 3

Let n be a natural number such that n ≥ 2. Show that

  (1/(n + 1))(1 + 1/3 + ... + 1/(2n - 1)) > (1/n)(1/2 + 1/4 + ... + 1/2n).
-/

namespace Canada1998P3

problem canada1998_p3 (n : ℕ) (hn : 2 ≤ n) :
    (1/(n:ℝ)) * ∑ i ∈ Finset.range n, (1/(2 * (i:ℝ) + 2)) <
    (1/((n:ℝ) + 1)) * ∑ i ∈ Finset.range n, (1/(2 * (i:ℝ) + 1)) := by
  -- Follows the proof in _Mathematical Olympiads 1998-1999_
  -- by Titu Andreescu and Zuming Feng

  -- It suffices to prove
  -- (n + 1)(1/2 + 1/4 + ... + 1/2n) < n(1 + 1/3 + ... + 1/(2n - 1)).
  suffices h : ((n:ℝ) + 1) * ∑ i ∈ Finset.range n, (1/(2 * (i:ℝ) + 2)) <
      (n:ℝ) * ∑ i ∈ Finset.range n, (1/(2 * (i:ℝ) + 1)) by
    have hn0 : (0:ℝ) < n := by exact_mod_cast Nat.zero_lt_two.trans_le hn
    rw [div_mul_eq_mul_div₀, one_mul, div_mul_eq_mul_div₀, one_mul,
        div_lt_div_iff₀ hn0 (by positivity)]
    linarith

  induction n, hn using Nat.le_induction with
  | base => norm_num [Finset.sum_range_succ]
  | succ k hk ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    push_cast

    -- The odd sum exceeds the even sum by at least its first term, 1/2.
    have key : ∑ i ∈ Finset.range k, (1/(2 * (i:ℝ) + 2)) + 1/2 ≤
        ∑ i ∈ Finset.range k, (1/(2 * (i:ℝ) + 1)) := by
      have h1 : ∀ i ∈ Finset.range k,
          (0:ℝ) ≤ 1/(2 * (i:ℝ) + 1) - 1/(2 * (i:ℝ) + 2) := fun i _ => by
        have := one_div_le_one_div_of_le (by positivity : (0:ℝ) < 2 * i + 1)
          (by linarith : 2 * (i:ℝ) + 1 ≤ 2 * i + 2)
        linarith
      have h2 := Finset.single_le_sum h1 (Finset.mem_range.mpr (by lia : 0 < k))
      rw [Finset.sum_sub_distrib] at h2
      push_cast at h2
      linarith

    -- The new odd term is not much smaller than the new even term,
    -- because (k + 2)/(2k + 2) ≤ 1 and (k + 1)/(2k + 1) ≥ 1/2.
    have hfrac : ((k:ℝ) + 2) / (2 * k + 2) - ((k:ℝ) + 1) / (2 * k + 1) ≤ 1/2 := by
      have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
      have h3 : ((k:ℝ) + 2) / (2 * k + 2) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      have h4 : (1:ℝ)/2 ≤ ((k:ℝ) + 1) / (2 * k + 1) := by
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
      linarith

    ring_nf at ih key hfrac ⊢
    linarith

end Canada1998P3
