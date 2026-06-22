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

lemma aux {l n s t : ℕ} (hl : Odd l) (hs : s ≠ 0) (hn : n = 2 ^ t * l) :
    Nat.Coprime (l + 2 ^ s) n := by
  have h2 : Odd (l + 2 ^ s) := hl.add_even (Nat.even_pow.mpr ⟨even_two, hs⟩)
  rw [hn]
  refine Nat.Coprime.mul_right (h2.coprime_two_right.pow_right t) ?_
  rw [add_comm, Nat.coprime_add_self_left]
  exact hl.coprime_two_left.pow_left s

snip end

problem imo1991_p2 (n : ℕ) (hn : 6 < n)
    (k : ℕ) (a : Fin k → ℕ)
    (ha1 : { a i | i } = { m | Nat.Coprime m n ∧ m < n })
    (d : ℕ) (hd : 0 < d)
    (ha2 : ∀ i : Fin k, (h : i + 1 < k) → a i + d = a ⟨i + 1, h⟩) :
    n.Prime ∨ n.isPowerOfTwo := by
  have hset := Set.ext_iff.mp ha1

  -- The set contains 1, so k is positive.
  obtain ⟨i0, -⟩ := (hset 1).mpr ⟨Nat.coprime_one_left n, by lia⟩
  have : NeZero k := ⟨i0.pos.ne'⟩

  have ha : ∀ (i : ℕ) (hi : i < k), a ⟨i, hi⟩ = a 0 + i * d := by
    intro i hi
    induction' i with i' ih
    · rw [zero_mul, add_zero]
      rfl
    · have hi'' : i' < k := by lia
      rw [← ha2 ⟨i', hi''⟩, ih hi'']
      ring

  -- The set consists exactly of a 0, a 0 + d, ..., a 0 + (k - 1) * d.
  have hmem : ∀ m : ℕ, (Nat.Coprime m n ∧ m < n) ↔ ∃ i < k, m = a 0 + i * d := by
    intro m
    constructor
    · intro hm
      obtain ⟨i, rfl⟩ := (hset m).mpr hm
      exact ⟨i, i.isLt, ha i i.isLt⟩
    · rintro ⟨i, hik, rfl⟩
      exact (hset _).mp ⟨⟨i, hik⟩, ha i hik⟩

  -- The set contains the endpoints 1 and n - 1.
  obtain ⟨i1, hi1k, hi1⟩ := (hmem 1).mp ⟨Nat.coprime_one_left n, by lia⟩
  obtain ⟨j, hjk, hj⟩ := (hmem (n - 1)).mp
    ⟨by rw [Nat.coprime_self_sub_left (by lia)]; exact Nat.coprime_one_left n, by lia⟩

  -- A number 0 < m < n is coprime to n iff it is ≡ 1 mod d.
  have h' : ∀ m : ℕ, 0 < m → m < n → (Nat.Coprime m n ↔ m ≡ 1 [MOD d]) := by
    intro m hm hm'
    constructor
    · intro hc
      obtain ⟨i, hik, rfl⟩ := (hmem m).mp ⟨hc, hm'⟩
      rw [hi1, Nat.add_mul_modulus_modEq_iff, Nat.modEq_add_mul_modulus_iff]
    · intro hm''
      rw [Nat.ModEq.comm, Nat.modEq_iff_dvd' (by lia : 1 ≤ m),
          dvd_iff_exists_eq_mul_left] at hm''
      obtain ⟨i', hi'⟩ := hm''
      rw [Nat.sub_eq_iff_eq_add (by lia), hi1, add_left_comm, ← add_mul] at hi'
      have hik : i' + i1 < k := by
        apply lt_of_lt_of_le' hjk
        rw [← Nat.mul_le_mul_right_iff hd, ← @Nat.add_le_add_iff_left _ _ (a 0)]
        lia
      exact ((hmem m).mpr ⟨i' + i1, hik, hi'⟩).1

  by_cases! hn' : 2 ∣ n
  · right
    obtain ⟨t, l, hl, htl⟩ := Nat.exists_eq_two_pow_mul_odd (show n ≠ 0 by lia)
    by_cases! hl1 : l = 1
    · exact ⟨t, by rw [htl, hl1, mul_one]⟩
    exfalso
    have hl2 : l % 2 = 1 := Nat.odd_iff.mp hl
    have ht : t ≠ 0 := by
      rintro rfl
      rw [pow_zero, one_mul] at htl
      lia
    have h4l : l + 4 < n := by
      rcases eq_or_ne t 1 with rfl | ht1
      · rw [pow_one] at htl
        lia
      · have h4t : 4 ≤ 2 ^ t := by
          calc (4:ℕ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) (by lia)
        have := Nat.mul_le_mul_right l h4t
        lia
    -- l + 2 and l + 4 are coprime to n, hence both ≡ 1 mod d, hence d ∣ 2,
    -- hence l is also ≡ 1 mod d, hence coprime to n. But l divides n.
    have hm2 : l + 2 ≡ 1 [MOD d] := (h' (l + 2) (by lia) (by lia)).mp
      (by simpa using aux hl one_ne_zero htl)
    have hm4 : l + 4 ≡ 1 [MOD d] := (h' (l + 4) (by lia) (by lia)).mp
      (by simpa using aux hl two_ne_zero htl)
    have hd2 : d ∣ 2 := by
      have h24 := (Nat.modEq_iff_dvd' (by lia : l + 2 ≤ l + 4)).mp (hm2.trans hm4.symm)
      rwa [show l + 4 - (l + 2) = 2 by lia] at h24
    have hml : l ≡ 1 [MOD d] := by
      have h0 : l + 2 ≡ l + 0 [MOD d] := Nat.ModEq.add_left l (Nat.modEq_zero_iff_dvd.mpr hd2)
      rw [add_zero] at h0
      exact h0.symm.trans hm2
    have hcl : Nat.Coprime l n := (h' l (by lia) (by lia)).mpr hml
    have hdvd : l ∣ n := by
      rw [htl]
      exact dvd_mul_left l (2 ^ t)
    exact hl1 ((Nat.gcd_eq_left hdvd).symm.trans hcl)
  · left
    have h2 : Nat.Coprime 2 n := Nat.prime_two.coprime_iff_not_dvd.mpr hn'
    have hd1 : d = 1 := by
      have h21 := (h' 2 (by lia) (by lia)).mp h2
      have hdd := (Nat.modEq_iff_dvd' (by lia : 1 ≤ 2)).mp h21.symm
      rw [show (2:ℕ) - 1 = 1 by lia] at hdd
      exact Nat.dvd_one.mp hdd
    subst hd1
    apply Nat.prime_of_coprime n (by lia)
    intro m hm hm0
    exact Nat.coprime_comm.mp ((h' m (by lia) hm).mpr (Nat.modEq_one))

end Imo1991P2
