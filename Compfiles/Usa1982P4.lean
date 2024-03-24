/-
Copyright (c) 2023 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongyu Ouyang
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 1982, Problem 4

Prove that there exists a positive integer k such that
k⬝2ⁿ + 1 is composite for every integer n.
-/

namespace Usa1982P4

snip begin

lemma not_prime_of_dvd : ∀ n : ℕ, n ≥ 2 → (∃ m, m ≥ 2 ∧ m ≠ n ∧ m ∣ n) → ¬ Prime n := by
  intro n hn h p
  have ngt0 : 0 < n := by linarith
  have p := (Nat.prime_iff).mpr p
  obtain ⟨m, ⟨h1, ⟨h2, h3⟩⟩⟩ := h
  apply (Nat.not_prime_iff_minFac_lt hn).mpr _ p
  have h4 : m < n := lt_of_le_of_ne (Nat.le_of_dvd ngt0 h3) h2
  have h5 : Nat.minFac n ≤ m := Nat.minFac_le_of_dvd h1 h3
  apply lt_of_le_of_lt h5 h4

lemma some_useful_mod_lemma : ∀ (n a b c d : ℕ),
  n ≡ a [MOD b] → d ^ b ≡ 1 [MOD c] → d ^ n ≡ d ^ a [MOD c] := by
  intros n a b c d h1 h2
  wlog h : n ≤ a with H
  · have han : a ≤ n := (Nat.le_total n a).resolve_left h
    symm
    apply H a n b c d h1.symm h2 han
  · rw [(by simp : d ^ n = 1 * d ^ n)]
    have ann : a = (a - n + n) := by exact (Nat.sub_eq_iff_eq_add h).mp rfl
    rw [←(zero_add n : 0 + n = n)] at h1
    rw [ann] at h1
    apply Nat.ModEq.add_right_cancel' at h1
    rw [ann, pow_add]
    apply Nat.ModEq.mul; swap; rfl
    unfold Nat.ModEq
    unfold Nat.ModEq at h2
    rw [←(Nat.div_add_mod' (a - n) b)]
    rw [←h1]
    simp only [Nat.zero_mod, add_zero]
    rw [mul_comm, pow_mul, Nat.pow_mod, h2, ←Nat.pow_mod, one_pow]

def usa1982_p4_lemma (e a b)
    (he :
      (⟨e, ⟨a, b⟩⟩ : ℕ × ℕ × ℕ) = ⟨3, ⟨1, 2⟩⟩ ∨
      (⟨e, ⟨a, b⟩⟩ : ℕ × ℕ × ℕ) = ⟨5, ⟨2, 4⟩⟩ ∨
      (⟨e, ⟨a, b⟩⟩ : ℕ × ℕ × ℕ) = ⟨17, ⟨4, 8⟩⟩ ∨
      (⟨e, ⟨a, b⟩⟩ : ℕ × ℕ × ℕ) = ⟨257, ⟨8, 16⟩⟩ ∨
      (⟨e, ⟨a, b⟩⟩ : ℕ × ℕ × ℕ) = ⟨65537, 16, 32⟩ ∨
      (⟨e, ⟨a, b⟩⟩ : ℕ × ℕ × ℕ) = ⟨6700417, 32, 64⟩ ∨
      (⟨e, ⟨a, b⟩⟩ : ℕ × ℕ × ℕ) = ⟨641, 0, 64⟩)
  :
  ∀ n : ℕ, n ≡ a [MOD b] → ¬ Prime (2935363331541925531 * (2 ^ n) + 1) := by
  obtain he | he | he | he | he | he | he := he
  all_goals {
    injections he _ ha hb
    intro n hn
    apply not_prime_of_dvd
    · apply Nat.succ_le_succ
      trans 1 * 2 ^ n
      · rw [one_mul]; exact Nat.one_le_two_pow
      · gcongr; decide
    · use e; rw [he]
      constructor; omega
      constructor; omega
      apply Nat.modEq_zero_iff_dvd.mp
      -- trans (a ? 1 : -1) * (a ? -1 : 1) + 1
      trans  (a / a * 1 + (1 - a / a) * (e - 1)) * (a / a * (e - 1) + (1 - a / a) * 1) + 1 <;> rw [he] <;> rw [ha]
      swap; rfl
      gcongr
      focus rfl
      trans 2 ^ a; swap; focus rw [ha]; rfl
      rw [←he]
      apply some_useful_mod_lemma n a b e 2 hn
      rw [hb, he]; rfl
  }


def usa1982_mod_lemma {n r r' q : ℕ} (hm : n % 64 = r') (p : ℕ) (hpq : p * q = 64) (hrr : r' ≡ r [MOD q]) : n ≡ r [MOD q] := by
  trans r'; swap; exact hrr
  rw [Nat.ModEq, ←hm, ←hpq, Nat.mod_mul_left_mod]

snip end

problem usa1982_p4 :
    ∃ k : ℕ, 0 < k ∧ ∀ n : ℕ, ¬ Prime (k * (2 ^ n) + 1) := by
  -- solution from
  -- https://artofproblemsolving.com/wiki/index.php/1982_USAMO_Problems/Problem_4
  refine ⟨2935363331541925531, by norm_num, ?_⟩
  intro n
  set m := n % 64 with hm
  have : m < 64 := by rw [hm]; apply Nat.mod_lt; omega
  match m with
  | m + 64 => omega
  |  0 => _|  1 => _|  2 => _|  3 => _|  4 => _|  5 => _|  6 => _|  7 => _|  8 => _|  9 => _
  | 10 => _| 11 => _| 12 => _| 13 => _| 14 => _| 15 => _| 16 => _| 17 => _| 18 => _| 19 => _
  | 20 => _| 21 => _| 22 => _| 23 => _| 24 => _| 25 => _| 26 => _| 27 => _| 28 => _| 29 => _
  | 30 => _| 31 => _| 32 => _| 33 => _| 34 => _| 35 => _| 36 => _| 37 => _| 38 => _| 39 => _
  | 40 => _| 41 => _| 42 => _| 43 => _| 44 => _| 45 => _| 46 => _| 47 => _| 48 => _| 49 => _
  | 50 => _| 51 => _| 52 => _| 53 => _| 54 => _| 55 => _| 56 => _| 57 => _| 58 => _| 59 => _
  | 60 => _| 61 => _| 62 => _| 63 => _
  all_goals try exact usa1982_p4_lemma     641  0 64 (by trivial) n (usa1982_mod_lemma hm.symm (64 / 64) rfl rfl)
  all_goals try exact usa1982_p4_lemma       3  1  2 (by trivial) n (usa1982_mod_lemma hm.symm (64 /  2) rfl rfl)
  all_goals try exact usa1982_p4_lemma       5  2  4 (by trivial) n (usa1982_mod_lemma hm.symm (64 /  4) rfl rfl)
  all_goals try exact usa1982_p4_lemma      17  4  8 (by trivial) n (usa1982_mod_lemma hm.symm (64 /  8) rfl rfl)
  all_goals try exact usa1982_p4_lemma     257  8 16 (by trivial) n (usa1982_mod_lemma hm.symm (64 / 16) rfl rfl)
  all_goals try exact usa1982_p4_lemma   65537 16 32 (by trivial) n (usa1982_mod_lemma hm.symm (64 / 32) rfl rfl)
  all_goals try exact usa1982_p4_lemma 6700417 32 64 (by trivial) n (usa1982_mod_lemma hm.symm (64 / 64) rfl rfl)
