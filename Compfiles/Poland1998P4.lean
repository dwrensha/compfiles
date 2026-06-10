/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
Polish Mathematical Olympiad 1998, Problem 4

Prove that the sequence {a_n} defined by a_1 = 1 and

     a_n = a_{n - 1} + a_{⌊n/2⌋}        n = 2,3,4,...

contains infinitely many integers divisible by 7.

-/

namespace Poland1998P4

def a : ℕ → ℕ
| 0 => 1 -- unused dummy value
| 1 => 1
| Nat.succ n =>
    have _ : (n.succ / 2) < n.succ := Nat.div_lt_self' n 0
    a n + a (n.succ / 2)

snip begin

lemma a_recurrence (n : ℕ) (hn : 2 ≤ n) : a n = a (n - 1) + a (n / 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by lia⟩
  simp only [a]
  rfl

def a' (n : ℕ) : ZMod 7 := (a n : ZMod 7)

lemma a'_recurrence (n : ℕ) (hn : 2 ≤ n) : a' n = a' (n - 1) + a' (n / 2) := by
  simp [a', a_recurrence n hn]

lemma lemma3
    (N0 : ℕ)
    (k : ZMod 7)
    (hk : k ≠ 0)
    (hN : ∀ i : ℕ, i < 7 → a' (N0 + i) = a' N0 + k * i) :
    (∃ i : ℕ, i < 7 ∧ a' (N0 + i) = 0) := by
  have hp : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine ⟨(- (a' N0) / k).val, ZMod.val_lt _, ?_⟩
  rw [hN _ (ZMod.val_lt _), ZMod.natCast_val, ZMod.cast_id]
  field_simp
  ring

lemma can_get_a_later_one_zmod :
    (∀ N : ℕ, a' N = 0 → (∃ M : ℕ, N < M ∧ a' M = 0)) := by
  intro n hn

  obtain (hlt : n < 2) | (hlte : 2 ≤ n) := lt_or_ge n 2
  · exact ⟨5, by lia, by simp +decide [a', a]⟩

  obtain ⟨m, hm, rfl⟩ : ∃ m, 1 ≤ m ∧ n = m + 1 := ⟨n - 1, by lia, by lia⟩

  -- a' (2 * m + 1), a' (2 * m + 2), and a' (2 * m + 3) are all equal,
  -- because a' (m + 1) = 0.

  have ha1 : a' (2 * m + 2) = a' (2 * m + 1) := by
    have h := a'_recurrence (2 * m + 2) (by lia)
    grind

  have ha2 : a' (2 * m + 3) = a' (2 * m + 1) := by
    have h := a'_recurrence (2 * m + 3) (by lia)
    grind

  -- Therefore, the seven elements beginning with a' (4 * m + 1) form an
  -- arithmetic progression with common difference a' (2 * m + 1).

  have hii : ∀ i, i < 6 →
      a' (4 * m + 1 + i + 1) = a' (4 * m + 1 + i) + a' (2 * m + 1) := by
    intro i hi
    have h := a'_recurrence (4 * m + 1 + i + 1) (by lia)
    grind

  have hik : ∀ i, i < 7 → a' (4 * m + 1 + i) = a' (4 * m + 1) + a' (2 * m + 1) * i := by
    intro i
    induction i with
    | zero => simp
    | succ p ih =>
      intro hp
      rw [show 4 * m + 1 + (p + 1) = 4 * m + 1 + p + 1 from rfl,
          hii p (by lia), ih (by lia)]
      push_cast
      ring

  obtain (haez : a' (2 * m + 1) = 0) | (hanez : ¬ a' (2 * m + 1) = 0) :=
    em (a' (2 * m + 1) = 0)
  · exact ⟨2 * m + 1, by lia, haez⟩
  · obtain ⟨i, _, hia'⟩ := lemma3 (4 * m + 1) (a' (2 * m + 1)) hanez hik
    exact ⟨4 * m + 1 + i, by lia, hia'⟩

lemma can_get_a_later_one : (∀ N : ℕ, 7 ∣ a N → (∃ M : ℕ, N < M ∧ 7 ∣ a M)) := by
  intro n hn
  obtain ⟨m, hmgt, hm7⟩ :=
    can_get_a_later_one_zmod n ((ZMod.natCast_eq_zero_iff _ _).mpr hn)
  exact ⟨m, hmgt, (ZMod.natCast_eq_zero_iff _ _).mp hm7⟩

lemma strengthen
    {P : ℕ → Prop}
    (h : ∀ N : ℕ, P N → (∃ M : ℕ, N < M ∧ P M))
    (he : ∃ N : ℕ, P N) :
    (∀ N : ℕ, ∃ M : ℕ, N < M ∧ P M) := by
  obtain ⟨N0, hn0⟩ := he
  intro N
  induction' N with pn hpn
  · obtain ⟨M, left, right⟩ := h N0 hn0
    exact ⟨M, pos_of_gt left, right⟩
  · obtain ⟨m, hm, hmp⟩ := hpn
    obtain ⟨M, left, right⟩ := h m hmp
    exact ⟨M, by lia, right⟩

theorem poland1998_p4' : (∀ N : ℕ, ∃ M : ℕ, N < M ∧ 7 ∣ a M) := by
  have he : 7 ∣ a 5 := by simp [a]
  exact strengthen can_get_a_later_one ⟨5, he⟩

snip end

problem poland1998_p4 : Set.Infinite { n | 7 ∣ a n } := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨M, hM, h7⟩ := poland1998_p4' N
  exact ⟨M, h7, hM⟩


end Poland1998P4
