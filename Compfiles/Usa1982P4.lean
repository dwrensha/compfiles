/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
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

lemma it_ge_2 : ∀ n : ℕ, 2 ≤ 2935363331541925531 * (2 ^ n) + 1 := fun n ↦ calc
  2 = 1 + 1 := by decide
  _ ≤ 2935363331541925531 * 1 + 1 := by gcongr; decide
  _ ≤ 2935363331541925531 * (2 ^ 0) + 1 := by simp
  _ ≤ 2935363331541925531 * (2 ^ n) + 1 := by gcongr <;> simp

lemma not_prime_of_dvd : ∀ n : ℕ, n ≥ 2 → (∃ m, m ≥ 2 ∧ m ≠ n ∧ m ∣ n) → ¬ Prime n := by
  intro n hn h p
  have ngt0 : 0 < n := by linarith
  have p := (Nat.prime_iff).mpr p
  obtain ⟨m, ⟨h1, ⟨h2, h3⟩⟩⟩ := h
  apply (Nat.not_prime_iff_minFac_lt hn).mpr _ p
  have h4 : m < n := lt_of_le_of_ne (Nat.le_of_dvd ngt0 h3) h2
  have h5 : Nat.minFac n ≤ m := Nat.minFac_le_of_dvd h1 h3
  apply lt_of_le_of_lt h5 h4

lemma usa1982_p4_lemma_ge : ∀ n : ℕ, 2935363331541925531 * (2 ^ n) + 1 ≥ 2935363331541925531 := by
  intro n
  have : (2 ^ n ≥ 1) := Nat.one_le_two_pow
  calc
    2935363331541925531 * (2 ^ n) + 1 ≥ 2935363331541925531 * 1 + 1 := by gcongr
    _ = 2935363331541925531 + 1 := by norm_num
    _ ≥ 2935363331541925531 := by norm_num

lemma usa1982_mod : ∀ (n a b c d : ℕ),
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


-- lemma usa1982_p4_lemma_2_1 : ∀ n : ℕ,  n ≡ 1 [MOD 2] → ¬ Prime (2935363331541925531 * (2 ^ n) + 1) := by
--   intro n hn
--   apply not_prime_of_dvd
--   · trans 2935363331541925531
--     apply (usa1982_p4_lemma_ge n)
--     norm_num
--   · use 3
--     constructor; norm_num
--     constructor; omega
--     apply Nat.modEq_zero_iff_dvd.mp
--     trans 1 * 2 + 1 <;> try rfl
--     gcongr
--     · rfl
--     · apply usa1982_mod n 1 2 _ _ hn
--       rfl

-- lemma usa1982_p4_lemma_2_2 : ∀ n : ℕ,  n ≡ 2 [MOD 4] → ¬ Prime (2935363331541925531 * (2 ^ n) + 1) := by
--   intro n hn
--   apply not_prime_of_dvd
--   · trans 2935363331541925531
--     apply (usa1982_p4_lemma_ge n)
--     norm_num
--   · use 5
--     constructor; norm_num
--     constructor; omega
--     apply Nat.modEq_zero_iff_dvd.mp
--     trans 1 * 4 + 1 <;> try rfl
--     gcongr
--     · rfl
--     · apply usa1982_mod n 2 4 _ _ hn
--       rfl

def usa1982_p4_lemma (e a b)
    (he :
      (⟨e, ⟨a, b⟩⟩ : ℕ × ℕ × ℕ) = ⟨3, ⟨1, 2⟩⟩ ∨
      (⟨e, ⟨a, b⟩⟩ : ℕ × ℕ × ℕ) = ⟨5, ⟨2, 4⟩⟩ ∨
      (⟨e, ⟨a, b⟩⟩ : ℕ × ℕ × ℕ) = ⟨17, ⟨4, 8⟩⟩ ∨
      (⟨e, ⟨a, b⟩⟩ : ℕ × ℕ × ℕ) = ⟨257, ⟨8, 16⟩⟩ ∨
      (⟨e, ⟨a, b⟩⟩ : ℕ × ℕ × ℕ) = ⟨65537, 16, 32⟩)
  :
  ∀ n : ℕ, n ≡ a [MOD b] → ¬ Prime (2935363331541925531 * (2 ^ n) + 1) := by
  obtain he | he | he | he | he := he
  all_goals {
    injections he _ ha hb
    intro n hn
    apply not_prime_of_dvd
    · trans 2935363331541925531
      apply (usa1982_p4_lemma_ge n)
      norm_num
    · use e; rw [he]
      constructor; omega
      constructor; omega
      apply Nat.modEq_zero_iff_dvd.mp
      trans 1 * (e - 1) + 1 <;> rw [he]
      gcongr <;> try rfl
      trans 2 ^ a; swap; focus rw [ha]; rfl
      rw [←he]
      apply usa1982_mod n a b e 2 hn
      · rw [hb, he]; rfl
      · rfl
  }
  
problem usa1982_p4 :
    ∃ k : ℕ, 0 < k ∧ ∀ n : ℕ, ¬ Prime (k * (2 ^ n) + 1) := by
  -- solution from
  -- https://artofproblemsolving.com/wiki/index.php/1982_USAMO_Problems/Problem_4
  refine ⟨2935363331541925531, by norm_num, ?_⟩
  intro n
  set m := n % 4 with hm
  have : m < 4 := by rw [hm]; apply Nat.mod_lt; omega
  match h : m with
  | 0 => sorry
  | 1 => apply usa1982_p4_lemma 3 1 2 (by trivial) n;
         unfold Nat.ModEq;
         rw [←Nat.mod_mul_left_mod _ 2]; rw [←hm]
  | 2 => apply usa1982_p4_lemma 5 2 4 (by trivial) n;
         exact hm.symm
  | 3 => sorry
  | h + 4 => contradiction
