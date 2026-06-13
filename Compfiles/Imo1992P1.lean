/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roozbeh Yousefzadeh
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file {
  tags := [.NumberTheory]
  solutionImportedFrom :=
    "https://github.com/roozbeh-yz/IMO-Steps/blob/main/imo_proofs/imo_1992_p1.lean"
}

/-!
# International Mathematical Olympiad 1992, Problem 1

Find all integers 1 < a < b < c such that
(a - 1)(b - 1)(c - 1) divides abc - 1.
-/

namespace Imo1992P1

determine solution_set : Set (ℤ × ℤ × ℤ) := {(2, 4, 8), (3, 5, 15)}

problem imo1992_p1 (a b c : ℤ) (ha : 1 < a) (hb : a < b) (hc : b < c) :
    ⟨a, b, c⟩ ∈ solution_set ↔
    (a - 1) * (b - 1) * (c - 1) ∣ a * b * c - 1 := by
  constructor
  · -- Each candidate solution satisfies the divisibility.
    intro h
    simp only [solution_set, Set.mem_insert_iff, Set.mem_singleton_iff,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ := h <;> norm_num
  intro ⟨k, hk⟩
  -- `hk : a * b * c - 1 = (a - 1) * (b - 1) * (c - 1) * k`.
  simp only [solution_set, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
  have ha2 : 2 ≤ a := by linarith
  have hb3 : 3 ≤ b := by linarith
  have hc4 : 4 ≤ c := by linarith
  have ha1 : 0 < a - 1 := by linarith
  have hb1 : 0 < b - 1 := by linarith
  have hc1 : 0 < c - 1 := by linarith
  have hden : 0 < (a - 1) * (b - 1) * (c - 1) := mul_pos (mul_pos ha1 hb1) hc1
  have hA : (0 : ℤ) ≤ a - 2 := by linarith
  have hB : (0 : ℤ) ≤ b - 3 := by linarith
  have hC : (0 : ℤ) ≤ c - 4 := by linarith
  have e3 : 0 ≤ (a - 2) * (b - 3) * (c - 4) := mul_nonneg (mul_nonneg hA hB) hC
  have eab : 0 ≤ (a - 2) * (b - 3) := mul_nonneg hA hB
  have eac : 0 ≤ (a - 2) * (c - 4) := mul_nonneg hA hC
  have ebc : 0 ≤ (b - 3) * (c - 4) := mul_nonneg hB hC
  have habc : 24 ≤ a * b * c := by
    have key : a * b * c = (a - 2) * (b - 3) * (c - 4) + 4 * ((a - 2) * (b - 3))
        + 3 * ((a - 2) * (c - 4)) + 2 * ((b - 3) * (c - 4))
        + 12 * (a - 2) + 8 * (b - 3) + 6 * (c - 4) + 24 := by ring
    linarith
  -- The quotient `k` satisfies `2 ≤ k < 4`.
  have hk1 : 1 ≤ k := by
    by_contra h
    push Not at h
    have hk0 : k ≤ 0 := by omega
    linarith [mul_nonpos_of_nonneg_of_nonpos hden.le hk0, hk, habc]
  have hk_ne1 : k ≠ 1 := by
    rintro rfl
    rw [mul_one] at hk
    -- `k = 1` would force `ab + bc + ca = a + b + c`, impossible for `a,b,c ≥ 2`.
    have iab : (a - 1) * (b - 1) = a * b - a - b + 1 := by ring
    have ibc : (b - 1) * (c - 1) = b * c - b - c + 1 := by ring
    have iac : (a - 1) * (c - 1) = a * c - a - c + 1 := by ring
    have hexp : (a - 1) * (b - 1) * (c - 1)
        = a * b * c - a * b - a * c - b * c + a + b + c - 1 := by ring
    linarith [mul_pos ha1 hb1, mul_pos hb1 hc1, mul_pos ha1 hc1,
      hexp, iab, ibc, iac]
  have hk2 : 2 ≤ k := by omega
  -- Since `a/(a-1) · b/(b-1) · c/(c-1) ≤ 2·(3/2)·(4/3) = 4`, we get `k < 4`.
  have hk4 : k < 4 := by
    have hub : a * b * c ≤ 4 * ((a - 1) * (b - 1) * (c - 1)) := by
      have key : 4 * ((a - 1) * (b - 1) * (c - 1)) - a * b * c
          = 3 * ((a - 2) * (b - 3) * (c - 4)) + 8 * ((a - 2) * (b - 3))
            + 5 * ((a - 2) * (c - 4)) + 2 * ((b - 3) * (c - 4))
            + 12 * (a - 2) + 4 * (b - 3) + 2 * (c - 4) := by ring
      linarith
    have hlt : (a - 1) * (b - 1) * (c - 1) * k <
               (a - 1) * (b - 1) * (c - 1) * 4 := by linarith [hub, hk]
    exact lt_of_mul_lt_mul_left hlt hden.le
  -- If `a ≥ 4` then the ratio drops below `4/3 · 5/4 · 6/5 = 2`, forcing `k < 2`.
  have ha4 : a < 4 := by
    by_contra h
    push Not at h
    have hb5 : 5 ≤ b := by linarith
    have hc6 : 6 ≤ c := by linarith
    have hA' : (0 : ℤ) ≤ a - 4 := by linarith
    have hB' : (0 : ℤ) ≤ b - 5 := by linarith
    have hC' : (0 : ℤ) ≤ c - 6 := by linarith
    have hub2 : a * b * c ≤ 2 * ((a - 1) * (b - 1) * (c - 1)) := by
      have key : 2 * ((a - 1) * (b - 1) * (c - 1)) - a * b * c
          = (a - 4) * (b - 5) * (c - 6) + 4 * ((a - 4) * (b - 5))
            + 3 * ((a - 4) * (c - 6)) + 2 * ((b - 5) * (c - 6))
            + 10 * (a - 4) + 6 * (b - 5) + 4 * (c - 6) := by ring
      have e3' : 0 ≤ (a - 4) * (b - 5) * (c - 6) :=
        mul_nonneg (mul_nonneg hA' hB') hC'
      have eab' : 0 ≤ (a - 4) * (b - 5) := mul_nonneg hA' hB'
      have eac' : 0 ≤ (a - 4) * (c - 6) := mul_nonneg hA' hC'
      have ebc' : 0 ≤ (b - 5) * (c - 6) := mul_nonneg hB' hC'
      linarith
    have hge : (a - 1) * (b - 1) * (c - 1) * 2 ≤
               (a - 1) * (b - 1) * (c - 1) * k :=
      mul_le_mul_of_nonneg_left hk2 hden.le
    linarith [hk, hub2, hge]
  -- Finitely many `(a, k)`; solve each by reducing to a product equal to a prime.
  interval_cases a <;> interval_cases k
  · -- a = 2, k = 2: forces `2b + 2c = 3`, impossible.
    have key : 2 * b + 2 * c = 3 := by linear_combination hk
    omega
  · -- a = 2, k = 3: `(b - 3)(c - 3) = 5`, so `b = 4, c = 8`.
    have key : (b - 3) * (c - 3) = 5 := by linear_combination -hk
    -- `5 = (b-3)(c-4) + (b-3) ≥ b - 3`, so `b` is bounded.
    have hp : 0 ≤ (b - 3) * (c - 4) := mul_nonneg (by linarith) (by linarith)
    have hid : (b - 3) * (c - 3) = (b - 3) * (c - 4) + (b - 3) := by ring
    have hbu : b ≤ 8 := by linarith
    interval_cases b <;> omega
  · -- a = 3, k = 2: `(b - 4)(c - 4) = 11`, so `b = 5, c = 15`.
    have key : (b - 4) * (c - 4) = 11 := by linear_combination -hk
    -- `11 = (b-4)(c-5) + (b-4) ≥ b - 4`, so `b` is bounded.
    have hp : 0 ≤ (b - 4) * (c - 5) := mul_nonneg (by linarith) (by linarith)
    have hid : (b - 4) * (c - 4) = (b - 4) * (c - 5) + (b - 4) := by ring
    have hbu : b ≤ 15 := by linarith
    interval_cases b <;> omega
  · -- a = 3, k = 3: forces `3·(bc) = 6b + 6c - 7`, impossible mod 3.
    have key : 3 * (b * c) = 6 * b + 6 * c - 7 := by linear_combination -hk
    omega

end Imo1992P1
