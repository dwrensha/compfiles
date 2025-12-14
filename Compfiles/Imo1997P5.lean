/-
Copyright (c) 2023 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roozbeh Yousefzadeh, Ilmārs Cīrulis
-/

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Tactic.IntervalCases

import ProblemExtraction

problem_file {
  tags := [.NumberTheory]
  importedFrom :=
    "https://github.com/roozbeh-yz/IMO-Steps/blob/main/imo_proofs/imo_1997_p5.lean"
}

/-!
# International Mathematical Olympiad 1997, Problem 5

Determine all pairs of integers 1 ≤ a,b that satisfy a ^ (b ^ 2) = b ^ a.
-/

namespace Imo1997P5

snip begin

lemma ineq₁ {n b : ℕ} (hb : 2 ≤ b) (hn : 5 ≤ n) : n < b ^ (n - 2) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num; linarith [Nat.pow_le_pow_left hb 3]
  | succ n hn iH => rw [show n + 1 - 2 = n - 2 + 1 by lia, Nat.pow_succ]; nlinarith

lemma ineq₂ {n b : ℕ} (hb : 2 ≤ b) (hn : 5 ≤ n) : n * b ^ 2 < b ^ n := by
  nth_rw 2 [show n = n - 2 + 2 by lia]
  rw [Nat.pow_add]
  nlinarith [ineq₁ hb hn]

lemma ineq₃ {x y b : ℕ} (hb : 2 ≤ b) (hxy : x < y) : b + x < b ^ 2 * y := by
  induction b, hb using Nat.le_induction <;> nlinarith

lemma ineq₄ {b : ℕ} (n : ℕ) (hb : 2 ≤ b) : b * n < (b ^ n) ^ 2 := by
  induction n with
  | zero => simp
  | succ n iH => ring_nf at *; exact ineq₃ hb iH

lemma aux₁ {n b : ℕ} (h : n * b ^ 2 = b ^ n) : b ≤ 1 ∨ n ≤ 4 := by grind [ineq₂]

lemma aux₂ {n b : ℕ} (h : b * n = (b ^ n) ^ 2) : b ≤ 1 := by grind [ineq₄]

lemma aux₃ {n a b c d : ℕ} (hb : b ≠ 0) (h : c ^ b = d ^ b * n ^ a) : d ∣ c :=
  (Nat.pow_dvd_pow_iff hb).mp (Dvd.intro (n ^ a) h.symm)

snip end

determine solution_set : Set (ℕ × ℕ) := {(1, 1), (16, 2), (27, 3)}

theorem imo1997_p5 (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    a ^ (b ^ 2) = b ^ a ↔ (a, b) ∈ solution_set := by
  simp [solution_set]; constructor <;> intro H
  · by_cases h₁ : 2 * b ^ 2 ≤ a
    · have h₂ : b ^ a = (b ^ 2) ^ (b ^ 2) * b ^ (a - 2 * b ^ 2) := by
        rw [← pow_mul, ← pow_add]; congr; lia
      have h₃ : b ^ 2 ∣ a := by
        rw [h₂] at H
        exact aux₃ (by nlinarith) H
      obtain ⟨d, hd⟩ := h₃
      rw [hd, mul_comm, pow_mul, Nat.pow_left_inj (pow_ne_zero 2 (Nat.ne_zero_of_lt hb))] at H
      obtain h₄ | h₄ := aux₁ H
      · interval_cases b; grind
      · interval_cases d
        · simp at H
        · have h₃ : b = 1 := by nlinarith
          grind
        · nlinarith
        · have h₃ : b = 3 := by nlinarith
          grind
        · have h₃ : b = 2 := by
            rw [show b ^ 4 = b ^ 2 * b ^ 2 by ring] at H
            have h₄ : b ^ 2 = 4 := by nlinarith
            nlinarith
          grind
    · simp at h₁
      have h₂ : (b ^ 2) ^ (b ^ 2) = a ^ (b ^ 2) * b ^ (2 * b ^ 2 - a) := by
        rw [H, ← pow_add, ← pow_mul]; congr; lia
      have h₃ : a ∣ b ^ 2 := aux₃ (by nlinarith) h₂
      obtain ⟨d, hd⟩ := h₃
      rw [hd, mul_comm, pow_mul, Nat.pow_left_inj (Nat.ne_zero_of_lt ha)] at H
      rw [← H] at hd
      have h₄ := aux₂ hd.symm
      interval_cases a; grind
  · grind

end Imo1997P5
