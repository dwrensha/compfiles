/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shalev Wengrowsky, Maximiliano Onofre Martínez
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Basic

import ProblemExtraction

problem_file { tags := [.Algebra, .NumberTheory] }

/-!
# USA Mathematical Olympiad 1973, Problem 2

The sequence an is defined by a1 = a2 = 1, an+2 = an+1 + 2an.
The sequence bn is defined by b1 = 1, b2 = 7, bn+2 = 2bn+1 + 3bn.

Show that the only integer in both sequences is 1.
-/

namespace Usa1973P2

-- reindexed to start at 0
def a : ℕ → ℕ
| 0 => 1
| 1 => 1
| n + 2 => a (n + 1) + 2 * a n

def b : ℕ → ℕ
| 0 => 1
| 1 => 7
| n + 2 => 2 * b (n + 1) + 3 * b n

lemma b_mod_8_eq (n : ℕ) : (Even n → b n % 8 = 1) ∧ (Odd n → b n % 8 = 7) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [b]
  | one => simp [b]
  | more k hk hk1 => constructor <;> intro _ <;> rw [b] <;> grind

lemma b_mod_8_mem (m : ℕ) : b m % 8 = 1 ∨ b m % 8 = 7 := by
  cases Nat.even_or_odd m with
  | inl h => left; exact (b_mod_8_eq m).1 h
  | inr h => right; exact (b_mod_8_eq m).2 h

lemma a_add_2_mod_8_eq (k : ℕ) : (Even k → a (k + 2) % 8 = 3) ∧ (Odd k → a (k + 2) % 8 = 5) := by
  induction k using Nat.twoStepInduction with
  | zero => simp [a]
  | one => simp [a]
  | more n hn hn1 =>
  constructor
  · intro he
    simp only [Nat.even_add_one, not_not] at he
    have ho : Odd (n + 1) := Even.add_one he
    rw [a, Nat.add_mod, Nat.mul_mod]
    rw [hn1.2 ho, hn.1 he]
  intro ho
  simp only [Nat.odd_add_one, not_not] at ho
  have he : Even (n + 1) := Odd.add_one ho
  rw [a, Nat.add_mod, Nat.mul_mod]
  rw [hn1.1 he, hn.2 ho]

lemma a_add_2_mod_8_mem (k : ℕ) : a (k + 2) % 8 = 3 ∨ a (k + 2) % 8 = 5 := by
  cases Nat.even_or_odd k with
  | inl h => left; exact (a_add_2_mod_8_eq k).1 h
  | inr h => right; exact (a_add_2_mod_8_eq k).2 h

problem usa1973_p2 (n m : ℕ) (h : a n = b m): a n = 1 := by
  by_cases hn : n < 2
  · interval_cases n <;> rfl
  push_neg at hn
  have ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
  rw [hk] at h
  rw [Nat.add_comm 2 k] at h
  have ha := a_add_2_mod_8_mem k
  have hb := b_mod_8_mem m
  rw [h] at ha
  grind

end Usa1973P2
