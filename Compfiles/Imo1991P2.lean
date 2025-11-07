/-
Copyright (c) 2025 The Compfiles Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benpigchu
-/

import Mathlib

import ProblemExtraction

problem_file {
  tags := [.NumberTheory]
}

/-!
# International Mathematical Olympiad 1991, Problem 2

Let n > 6 be an integer and a₁, a₂, ..., aₖ be all the
natural numbers less than n and relatively prime to n.
If

  a₂ - a₁ = a₃ - a₂ = ... = aₖ - aₖ₋₁ > 0,

prove that n must either be a prime number of a power
of 2.
-/

namespace Imo1991P2

snip begin

lemma exists_powerOfTwo_mul_odd (n : ℕ) (hn : 0 < n) :
  ∃ t l : ℕ, n = 2 ^ t * l ∧ ¬2 ∣ l := by
  induction' n using Nat.case_strong_induction_on with n' hn'
  · cutsat
  · by_cases! hn'' : 2 ∣ n' + 1
    · rcases exists_eq_mul_left_of_dvd hn'' with ⟨m, hm⟩
      rcases hn' m (by cutsat : _) (by cutsat : _) with ⟨t', l', ht'l', hl'⟩
      use t' + 1, l'
      constructor
      · rw [hm, ht'l']
        ring
      · exact hl'
    · use 0, n' + 1
      constructor
      · ring
      · exact hn''

lemma aux {l n s t: ℕ} (hl : ¬2 ∣ l) (hs : s ≠ 0) (hn : n = 2 ^ t * l) :
  Nat.Coprime (l + 2 ^ s) n := by
  by_contra h'
  rw [Nat.Prime.not_coprime_iff_dvd] at h'
  rcases h' with ⟨p, hp, hp', hp''⟩
  rw [hn] at hp''
  have hp2 := dvd_mul_of_dvd_right hp' (2 ^ t)
  rw [mul_add, ← Nat.dvd_add_iff_right hp'', ← pow_add] at hp2
  apply Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_two at hp2
  have h2s := dvd_pow_self 2 hs
  rw [hp2, ← Nat.dvd_add_iff_left h2s] at hp'
  contrapose! hl
  exact hp'

snip end

problem imo1991_p2 (n : ℕ) (hn : 6 < n)
    (k : ℕ) (a : Fin k → ℕ)
    (ha1 : { a i | i } = { m | Nat.Coprime m n ∧ m < n })
    (d : ℕ) (hd : 0 < d)
    (ha2 : ∀ i : Fin k, (h : i + 1 < k) → a i + d = a ⟨i + 1, h⟩) :
    n.Prime ∨ n.isPowerOfTwo := by
  have hk : k ≠ 0 := by
    intro hk'
    have h': { a i | i } = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro x
      dsimp
      push_neg
      intro i
      rw [hk'] at i
      apply finZeroElim i
    rw [h'] at ha1
    contrapose! ha1
    use 1
    constructor
    · exact Nat.coprime_one_left n
    · cutsat
  haveI : NeZero k := { out := hk }
  have ha : ∀ (i : ℕ) (hi : i < k), a ⟨i, hi⟩ = a 0 + i * d := by
    intro i hi
    induction' i with i' hi'
    · rw [zero_mul, add_zero]
      rfl
    · have hi'' : i' < k := lt_trans' hi (lt_add_one i')
      rw [← ha2 ⟨i', hi''⟩, hi' hi'']
      ring
  have h : ∃ a₀ : ℕ, ∀ m : ℕ, (Nat.Coprime m n ∧ m < n ↔ ∃ (i : ℕ), i < k ∧ m = a₀ + i * d) := by
    use a 0
    intro m
    constructor
    · rintro hm
      have hm'' : m ∈ {m | m.Coprime n ∧ m < n} := hm
      rw [← ha1] at hm''
      rcases hm'' with ⟨i, hi⟩
      use i.val
      constructor
      · exact Fin.isLt i
      · rw [← hi]
        apply ha
    · rintro ⟨i, hik, hi⟩
      have hm : m ∈ { a i | i } := by
        use ⟨i, hik⟩
        rw [hi]
        apply ha
      rw [ha1] at hm
      exact hm
  rcases h with ⟨a₀, ha₀⟩
  have h1 : Nat.Coprime 1 n ∧ 1 < n := by
    constructor
    · apply Nat.coprime_one_left
    · cutsat
  have hn_sub_1 : Nat.Coprime (n - 1) n ∧ (n - 1) < n := by
    constructor
    · rw [Nat.coprime_self_sub_left (by cutsat : _)]
      apply Nat.coprime_one_left
    · cutsat
  rw [ha₀] at h1 hn_sub_1
  rcases h1 with ⟨i1, hi1k, hi1⟩
  rcases hn_sub_1 with ⟨in_sub_1, hin_sub_1k, hin_sub_1⟩
  have h' : ∀ m : ℕ, 0 < m ∧ m < n → (Nat.Coprime m n ↔ m ≡ 1 [MOD d]):= by
    rintro m ⟨hm, hm'⟩
    constructor
    · intro hm''
      rcases (ha₀ m).mp ⟨hm'', hm'⟩ with ⟨i, hik, hi⟩
      rw [hi, hi1]
      rw [Nat.add_mul_modulus_modEq_iff, Nat.modEq_add_mul_modulus_iff]
    · intro hm''
      rw [Nat.ModEq.comm, Nat.modEq_iff_dvd' (by cutsat : _), dvd_iff_exists_eq_mul_left] at hm''
      rcases hm'' with ⟨i', hi'⟩
      rw [Nat.sub_eq_iff_eq_add (by cutsat : _), hi1, add_left_comm, ← add_mul] at hi'
      have him: ∃ i < k, m = a₀ + i * d := by
        use i' + i1
        constructor
        · apply lt_of_lt_of_le' hin_sub_1k
          rw [← Nat.mul_le_mul_right_iff hd, ← @Nat.add_le_add_iff_left _ _ a₀]
          rw [← hi', ← hin_sub_1]
          cutsat
        · exact hi'
      exact ((ha₀ m).mpr him).left
  by_cases! hn' : 2 ∣ n
  · right
    rcases exists_powerOfTwo_mul_odd n (by cutsat : _) with ⟨t, l, htl, hl⟩
    by_cases! hl' : l = 1
    · rw [hl', mul_one] at htl
      rw [htl]
      use t
    · exfalso
      have ht : 0 < t := by cutsat
      have hl'' : l + 4 < n := by
        by_cases! ht' : t = 1
        · cutsat
        · rw [htl]
          calc l + 4
              < 2 ^ 2 * l := by cutsat
            _ ≤ 2 ^ t * l := by
              apply Nat.mul_le_mul_right
              exact Nat.pow_le_pow_right (by norm_num : _) (by cutsat : _)
      have hl_add_2 : Nat.Coprime (l + 2 ^ 1) n := aux hl (by norm_num : 1 ≠ 0) htl
      have hl_add_4 : Nat.Coprime (l + 2 ^ 2) n := aux hl (by norm_num : 2 ≠ 0) htl
      norm_num at hl_add_2 hl_add_4
      rw [h' (l + 2) (by cutsat : _)] at hl_add_2
      rw [h' (l + 4) (by cutsat : _), Nat.ModEq.comm] at hl_add_4
      have hl2 := Nat.ModEq.trans hl_add_2 hl_add_4
      rw [Nat.modEq_iff_dvd' (by cutsat : _), Nat.sub_add_eq, add_comm, Nat.add_sub_cancel] at hl2
      norm_num at hl2
      rw [dvd_iff_exists_eq_mul_left] at hl2
      rcases hl2 with ⟨c, hc⟩
      rw [hc, Nat.add_mul_modulus_modEq_iff] at hl_add_2
      rw [← h' l (by cutsat : _)] at hl_add_2
      contrapose hl_add_2
      apply Nat.not_coprime_of_dvd_of_dvd (by cutsat : 1 < l) (dvd_rfl)
      rw [htl]
      apply dvd_mul_left
  · left
    apply Nat.prime_of_coprime n (by cutsat : _)
    intro m hm hm'
    have h2 : Nat.Coprime 2 n := by
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
      exact hn'
    rw [h' 2 (by cutsat : _), Nat.ModEq.comm, Nat.modEq_iff_dvd' (by cutsat : _)] at h2
    norm_num at h2
    rw [Nat.coprime_comm, h' m (by cutsat : _)]
    rw [h2]
    apply Nat.modEq_one

end Imo1991P2
