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
  cases n with
  | zero => exact (Nat.not_succ_le_zero _ hn).elim
  | succ n =>
    cases n
    · exact (Nat.not_succ_le_self _ hn).elim
    · simp only [a, Nat.succ_sub_succ_eq_sub, tsub_zero]

def a' : ℕ → ZMod 7
| n => ⟨(a n) % 7, Nat.mod_lt _ (by norm_num)⟩

lemma a'_recurrence (n : ℕ) (hn : 2 ≤ n) : a' n = a' (n - 1) + a' (n / 2) := by
  have : (a' n).val = (a' (n - 1) + a' (n / 2)).val := by
    rw [ZMod.val_add]
    simp_rw [a', a_recurrence n hn]
    rw [ZMod.val]
    simp
  exact ZMod.val_injective 7 this

lemma lemma3
    (N0 : ℕ)
    (k : ZMod 7)
    (hk : k ≠ 0)
    (hN : ∀ i : ℕ, i < 7 → a' (N0 + i) = a' N0 + k * i) :
    (∃ i : ℕ, i < 7 ∧ a' (N0 + i) = 0) := by
  have hp : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let ii := - (a' N0) / k
  use ii.val
  constructor
  · exact ZMod.val_lt ii
  · have := hN ii.val (ZMod.val_lt ii)
    rw [this, ZMod.natCast_val, ZMod.cast_id', id_def, mul_div_cancel₀ _ hk]
    exact add_neg_cancel (a' N0)

lemma can_get_a_later_one_zmod :
    (∀ N : ℕ, a' N = 0 → (∃ M : ℕ, N < M ∧ a' M = 0)) := by
  intro n hn

  obtain (hlt : n < 2) | (hlte : 2 ≤ n) := lt_or_ge n 2
  · exact ⟨5, Nat.le.step <| Nat.le.step <| Nat.le.step hlt, by simp [a', a]⟩

  let n1 : ℕ := 2 * (n - 1) + 1

  -- a' (2 * n - 1), a' (2 * n), and a' (2 * n + 1) are all equal

  have hn1v : n1 = 2 * n - 1 := by lia
  have hn2 : 2 ≤ n1 + 1 := Nat.succ_le_succ le_add_self

  let an1 := a' n1

  have hn1 : (n1 + 1) = 2 * n := by lia

  have ha1 : a' (n1 + 1) = an1 + a' n := by
    have haa : a' (n1 + 1) = a' n1 + a' (n1.succ / 2) := a'_recurrence (n1 + 1) hn2
    have h2n1 : 2 * n / 2 = n := by norm_num
    have h2n1' : (n1 + 1) / 2 = n := by rw [hn1, h2n1]
    rw [haa, h2n1']

  have ha2 : a' (n1 + 2) = a' (n1 + 1) +  a' n := by
    have haa : a' (n1 + 2) = a' (n1 + 1) + a' (n1.succ.succ / 2) :=
      a'_recurrence (n1 + 2) le_add_self
    have h1 : (2 * n + 1) / 2 = n := by lia
    have hn1v' : 2 * n = n1 + 1 := hn1.symm
    rw [haa]
    congr
    have : n1.succ.succ = (n1 + 1 + 1) := rfl
    rw [this, ←hn1v', h1]

  have ha1' : a' (n1 + 1) = a' n1 := by grind
  have ha2' : a' (n1 + 2) = a' n1 := by grind

  clear ha1 ha2

  -- then the seven elements beginning with a (4 * n - 3) will all have different
  -- residues mod 7.

/-

  let n4 := 4 * n - 3,
  -- a (n4 + 1) = a n4 + a n1
  -- a (n4 + 2) = a (n4 + 1) + a n1
  -- a (n4 + 3) = a (n4 + 2) + a (n1 + 1)
  -- a (n4 + 4) = a (n4 + 3) + a (n1 + 1)
  -- a (n4 + 5) = a (n4 + 4) + a (n1 + 2)
  -- a (n4 + 6) = a (n4 + 5) + a (n1 + 2)

-/

  -- n2 = 4 * n - 3
  --   = 4 * (n - 1) + 1
  let n2 : ℕ := 4 * (n - 1) + 1

  have hii : ∀ i, i < 6 → a' (n2 + i + 1) = a' (n2 + i) + a' n1 := by
    intro i hi
    have hn2ge2 : 2 ≤ n2 + i + 1 := by lia
    have hr := a'_recurrence (n2 + i + 1) hn2ge2
    grind

  have hik : ∀ i, i < 7 → a' (n2 + i) = a' n2 + a' n1 * i := by
    intro i
    induction' i with p hp
    · simp
    · intro hpi7
      have hpi6 : p < 6 := Nat.succ_lt_succ_iff.mp hpi7
      have hinc := hii p hpi6
      have hadd : n2 + p + 1 = n2 + p.succ := rfl
      have hi6 : p < 7 := Nat.lt_succ_of_lt hpi6
      have hpp := hp hi6
      have hp1: (p.succ : ZMod 7) = (p : ZMod 7) + 1 := Nat.cast_succ p
      rw [←hadd, hinc, hpp, hp1]
      ring

  obtain (haez : a' n1 = 0) | (hanez : ¬ a' n1 = 0) := em (a' n1 = 0)
  · use n1
    constructor
    · lia
    · exact haez

  · have := lemma3 n2 (a' n1) hanez hik
    obtain ⟨ii, _, hia'⟩ := this
    use (n2 + ii)
    constructor
    · lia
    · assumption

lemma can_get_a_later_one : (∀ N : ℕ, 7 ∣ a N → (∃ M : ℕ, N < M ∧ 7 ∣ a M)) := by
  intro n hn
  have ha' : a' n = 0 := by
    have : a' n = ⟨a n % 7, Nat.mod_lt _ (Nat.succ_pos _)⟩ := by simp[a']
    rw [this]
    simp only [Nat.mod_eq_zero_of_dvd hn, Fin.mk_zero]
  obtain ⟨m, hmgt, hm7⟩ := can_get_a_later_one_zmod n ha'
  use m
  use hmgt
  exact Fin.natCast_eq_zero.mp hm7

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
  apply Set.infinite_of_not_bddAbove
  intro h
  rw [bddAbove_def] at h
  obtain ⟨x, hx⟩ := h
  obtain ⟨y, hy1, hy2⟩ := poland1998_p4' x
  exact Nat.lt_le_asymm hy1 (hx y hy2)


end Poland1998P4
