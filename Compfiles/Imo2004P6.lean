/-
Copyright (c) 2021 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Mathlib

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 2004, Problem 6

We call a positive integer *alternating* if every two consecutive
digits in its decimal representation are of different parity.

Find all positive integers n such that n has a multiple that is
alternating.
-/

namespace Imo2004P6

determine SolutionSet : Set ℕ := {n | 0 < n ∧ ¬ 20 ∣ n}

abbrev Alternating (n : Nat) : Prop :=
  0 < n ∧ (Nat.digits 10 n).IsChain (fun k l ↦ ¬ k ≡ l [MOD 2])

snip begin

lemma not_alternating_of_dvd_twenty {M : ℕ} (h : 20 ∣ M) : ¬ Alternating M := by
  rintro ⟨hpos, hchain⟩
  obtain ⟨q, rfl⟩ := h
  rw [Nat.digits_def' (by norm_num : (1:ℕ) < 10) hpos] at hchain
  have h1 : 20 * q % 10 = 0 := by omega
  have h2 : 20 * q / 10 = 2 * q := by omega
  rw [h1, h2] at hchain
  rw [Nat.digits_def' (by norm_num : (1:ℕ) < 10) (by omega : 0 < 2 * q)] at hchain
  rw [List.isChain_cons_cons] at hchain
  exact hchain.1 (show 0 % 2 = (2 * q % 10) % 2 by omega)

/-- Digit lists (little-endian) whose entry at each position has the parity
of the position, so that consecutive digits have different parity. -/
def Nice (L : List ℕ) : Prop :=
  (∀ d ∈ L, d < 10) ∧ ∀ (i : ℕ) (h : i < L.length), L[i] % 2 = i % 2

lemma Nice.append {L M : List ℕ} (hL : Nice L) (hM : Nice M)
    (hlen : L.length % 2 = 0) : Nice (L ++ M) := by
  refine ⟨fun d hd ↦ ?_, fun i h ↦ ?_⟩
  · rcases List.mem_append.mp hd with h' | h'
    · exact hL.1 d h'
    · exact hM.1 d h'
  · rcases Nat.lt_or_ge i L.length with hi | hi
    · rw [List.getElem_append_left hi]
      exact hL.2 i hi
    · rw [List.getElem_append_right hi]
      have h' : i - L.length < M.length := by
        rw [List.length_append] at h; omega
      have := hM.2 (i - L.length) h'
      omega

lemma Nice.snoc {L : List ℕ} (hL : Nice L) {e : ℕ} (he : e < 10)
    (hp : e % 2 = L.length % 2) : Nice (L ++ [e]) := by
  refine ⟨fun d hd ↦ ?_, fun i h ↦ ?_⟩
  · rcases List.mem_append.mp hd with h' | h'
    · exact hL.1 d h'
    · simp only [List.mem_singleton] at h'
      omega
  · rcases Nat.lt_or_ge i L.length with hi | hi
    · rw [List.getElem_append_left hi]
      exact hL.2 i hi
    · have h' : (L ++ [e]).length = L.length + 1 := by simp
      have hieq : i = L.length := by omega
      rw [List.getElem_append_right hi, List.getElem_singleton]
      omega

lemma Nice.isChain {L : List ℕ} (hL : Nice L) :
    L.IsChain (fun k l ↦ ¬ k ≡ l [MOD 2]) := by
  rw [List.isChain_iff_getElem]
  intro i h
  have h1 := hL.2 i (by omega)
  have h2 := hL.2 (i + 1) h
  intro hc
  have hc' : L[i] % 2 = L[i + 1] % 2 := hc
  omega

/-- If `u` is coprime to `x` and `2 ≤ x`, then `u` divides some sum
`1 + x + x ^ 2 + ⋯ + x ^ (t - 1)` with `0 < t`. -/
lemma dvd_geom_sum {u x : ℕ} (hux : Nat.Coprime x u) (hx : 2 ≤ x) :
    ∃ t, 0 < t ∧ u ∣ ∑ i ∈ Finset.range t, x ^ i := by
  have hu0 : 0 < u := Nat.pos_of_ne_zero fun h ↦ by simp [h, Nat.Coprime] at hux; omega
  have hU0 : 0 < u * (x - 1) := Nat.mul_pos hu0 (by omega)
  have hcop : Nat.Coprime x (u * (x - 1)) := by
    refine Nat.Coprime.mul_right hux ?_
    have h1 := Nat.dvd_sub (Nat.gcd_dvd_left x (x - 1)) (Nat.gcd_dvd_right x (x - 1))
    rw [show x - (x - 1) = 1 by omega] at h1
    exact Nat.dvd_one.mp h1
  refine ⟨(u * (x - 1)).totient, Nat.totient_pos.mpr hU0, ?_⟩
  have h2 : x ^ (u * (x - 1)).totient ≡ 1 [MOD u * (x - 1)] :=
    Nat.ModEq.pow_totient hcop
  have h4 : u * (x - 1) ∣ x ^ (u * (x - 1)).totient - 1 :=
    (Nat.modEq_iff_dvd' (pow_pos (by omega : 0 < x) _)).mp h2.symm
  rw [← geom_sum_mul_of_one_le (by omega : 1 ≤ x) (u * (x - 1)).totient] at h4
  exact (Nat.mul_dvd_mul_iff_right (by omega : 0 < x - 1)).mp h4

lemma nice_flatten_replicate {L : List ℕ} (hL : Nice L) (hlen : L.length % 2 = 0)
    (t : ℕ) :
    Nice ((List.replicate t L).flatten) ∧
      ((List.replicate t L).flatten).length = t * L.length ∧
      Nat.ofDigits 10 ((List.replicate t L).flatten) =
        Nat.ofDigits 10 L * ∑ i ∈ Finset.range t, (10 ^ L.length) ^ i := by
  induction t with
  | zero => refine ⟨⟨by simp, by simp⟩, by simp, by simp⟩
  | succ t ih =>
    rw [List.replicate_succ, List.flatten_cons]
    refine ⟨hL.append ih.1 hlen, ?_, ?_⟩
    · rw [List.length_append, ih.2.1]; ring
    · rw [Nat.ofDigits_append, ih.2.2, geom_sum_succ]
      ring

/-- Repeating a `Nice` digit block of even length enough times produces an
alternating multiple of `n * u`, where `n` divides the block and `u` is
coprime to `10`. -/
lemma exists_alternating_multiple {n u : ℕ} (hu : Nat.Coprime u 10)
    (hnu : Nat.Coprime n u) {L : List ℕ} (hne : L ≠ [])
    (hlen : L.length % 2 = 0) (hnice : Nice L)
    (hdvd : n ∣ Nat.ofDigits 10 L) :
    ∃ M, Alternating M ∧ n * u ∣ M := by
  have hlpos : 0 < L.length := List.length_pos_of_ne_nil hne
  have hx10 : 10 ≤ 10 ^ L.length := by
    calc (10:ℕ) = 10 ^ 1 := (pow_one 10).symm
    _ ≤ 10 ^ L.length := Nat.pow_le_pow_right (by norm_num) hlpos
  obtain ⟨t, ht0, huS⟩ := dvd_geom_sum (hu.symm.pow_left L.length) (by omega)
  obtain ⟨hniceJ, hlenJ, hofJ⟩ := nice_flatten_replicate hnice hlen t
  have hJlen : 0 < ((List.replicate t L).flatten).length := by
    rw [hlenJ]
    exact Nat.mul_pos ht0 hlpos
  have hJne : (List.replicate t L).flatten ≠ [] := List.ne_nil_of_length_pos hJlen
  have hlast : ∀ h : (List.replicate t L).flatten ≠ [],
      ((List.replicate t L).flatten).getLast h ≠ 0 := by
    intro h
    rw [List.getLast_eq_getElem]
    have hJeven : ((List.replicate t L).flatten).length % 2 = 0 := by
      rw [hlenJ, Nat.mul_mod, hlen]
      simp
    have hp := hniceJ.2 (((List.replicate t L).flatten).length - 1) (by omega)
    omega
  have hdigits : Nat.digits 10 (Nat.ofDigits 10 ((List.replicate t L).flatten)) =
      (List.replicate t L).flatten :=
    Nat.digits_ofDigits 10 (by norm_num) _ hniceJ.1 hlast
  refine ⟨Nat.ofDigits 10 ((List.replicate t L).flatten), ⟨?_, ?_⟩, ?_⟩
  · rw [Nat.pos_iff_ne_zero, ← Nat.digits_ne_nil_iff_ne_zero (b := 10), hdigits]
    exact hJne
  · rw [hdigits]
    exact hniceJ.isChain
  · rw [hofJ]
    exact hnu.mul_dvd_of_dvd_of_dvd (Dvd.dvd.mul_right hdvd _) (Dvd.dvd.mul_left huS _)

/-- Any `n` dividing `2 ^ i * 5 ^ j * u`, where `u` avoids `2` and `5` and
some `Nice` block of even length is divisible by `2 ^ i * 5 ^ j`, has an
alternating multiple. -/
lemma exists_alt_multiple_of_dvd {u n i j : ℕ} (hu2 : ¬ 2 ∣ u) (hu5 : ¬ 5 ∣ u)
    {L : List ℕ} (hne : L ≠ []) (hlen : L.length % 2 = 0) (hnice : Nice L)
    (hdvd : 2 ^ i * 5 ^ j ∣ Nat.ofDigits 10 L) (hn : n ∣ 2 ^ i * 5 ^ j * u) :
    ∃ M, Alternating M ∧ n ∣ M := by
  have c2 : Nat.Coprime 2 u := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hu2
  have c5 : Nat.Coprime 5 u := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hu5
  have hu10 : Nat.Coprime u 10 := by
    rw [show (10:ℕ) = 2 * 5 by norm_num]
    exact (Nat.Coprime.mul_left c2 c5).symm
  have hcop : Nat.Coprime (2 ^ i * 5 ^ j) u :=
    Nat.Coprime.mul_left (c2.pow_left _) (c5.pow_left _)
  obtain ⟨M, hM, hMdvd⟩ := exists_alternating_multiple hu10 hcop hne hlen hnice hdvd
  exact ⟨M, hM, hn.trans hMdvd⟩

/-- For every `k` there is a `Nice` digit block of length `2 * k + 2`
divisible by `2 ^ (2 * k + 3)`. -/
lemma two_block (k : ℕ) : ∃ L : List ℕ, L.length = 2 * k + 2 ∧ Nice L ∧
    2 ^ (2 * k + 3) ∣ Nat.ofDigits 10 L := by
  induction k with
  | zero => exact ⟨[6, 1], by simp, ⟨by decide, by decide⟩, by decide⟩
  | succ k ih =>
    obtain ⟨L, hlen, hnice, m, hm⟩ := ih
    set d : ℕ := (14 - 2 * m % 8) % 8 with hd
    have hd8 : d < 8 := by omega
    have hd2 : d % 2 = 0 := by omega
    have hnice2 : Nice [d, 1] := by
      refine ⟨?_, ?_⟩
      · intro e he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        omega
      · intro i h
        simp only [List.length_cons, List.length_nil] at h
        interval_cases i
        · simpa using hd2
        · simp
    refine ⟨L ++ [d, 1], ?_, hnice.append hnice2 (by omega), ?_⟩
    · simp only [List.length_append, List.length_cons, List.length_nil, hlen]
      ring
    · rw [Nat.ofDigits_append, hlen, hm]
      have hof : Nat.ofDigits 10 [d, 1] = d + 10 := by
        norm_num [Nat.ofDigits]
      rw [hof]
      have h58 : (5:ℕ) ^ (2 * k + 2) % 8 = 1 := by
        have h5 : (5:ℕ) ^ (2 * k + 2) = 25 ^ (k + 1) := by
          rw [show 2 * k + 2 = 2 * (k + 1) by ring, pow_mul]
          norm_num
        rw [h5, Nat.pow_mod]
        norm_num
      obtain ⟨p, hp⟩ : ∃ p, (5:ℕ) ^ (2 * k + 2) = 8 * p + 1 :=
        ⟨5 ^ (2 * k + 2) / 8, by omega⟩
      have key : 2 ^ 3 ∣ 2 * m + 5 ^ (2 * k + 2) * (d + 10) := by
        rw [hp, show (8 * p + 1) * (d + 10) = 8 * (p * (d + 10)) + d + 10 by ring]
        show 8 ∣ _
        omega
      have heq : 2 ^ (2 * k + 3) * m + 10 ^ (2 * k + 2) * (d + 10)
          = 2 ^ (2 * k + 2) * (2 * m + 5 ^ (2 * k + 2) * (d + 10)) := by
        rw [show (10:ℕ) ^ (2 * k + 2) = 2 ^ (2 * k + 2) * 5 ^ (2 * k + 2) by
              rw [← Nat.mul_pow],
            pow_succ]
        ring
      rw [heq, show 2 * (k + 1) + 3 = (2 * k + 2) + 3 by ring, pow_add]
      exact Nat.mul_dvd_mul_left _ key

lemma five_digit_choice : ∀ c < 5, 0 < c → ∀ m' < 5, ∀ s < 2,
    ∃ e ∈ Finset.range 10, e % 2 = s ∧ (m' + e * c) % 5 = 0 := by decide

/-- For every `b` there is a `Nice` digit block of length `b + 1`
divisible by `10 * 5 ^ b` (its bottom digit is `0`). -/
lemma five_block (b : ℕ) : ∃ L : List ℕ, L.length = b + 1 ∧ Nice L ∧
    10 * 5 ^ b ∣ Nat.ofDigits 10 L := by
  induction b with
  | zero => exact ⟨[0], by simp, ⟨by decide, by decide⟩, by decide⟩
  | succ b ih =>
    obtain ⟨L, hlen, hnice, m, hm⟩ := ih
    have hc5 : 2 ^ b % 5 < 5 := Nat.mod_lt _ (by norm_num)
    have hc0 : 0 < 2 ^ b % 5 := by
      rw [Nat.pos_iff_ne_zero]
      intro h
      have h1 : (5:ℕ) ∣ 2 ^ b := Nat.dvd_of_mod_eq_zero h
      have h2 : (5:ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num) h1
      omega
    obtain ⟨e, he10, hepar, hemod⟩ := five_digit_choice (2 ^ b % 5) hc5 hc0
      (m % 5) (Nat.mod_lt _ (by norm_num)) ((b + 1) % 2) (Nat.mod_lt _ (by norm_num))
    rw [Finset.mem_range] at he10
    refine ⟨L ++ [e], by simp [hlen], hnice.snoc he10 (by omega), ?_⟩
    rw [Nat.ofDigits_append, hlen, hm]
    have hof : Nat.ofDigits 10 [e] = e := by
      norm_num [Nat.ofDigits]
    rw [hof]
    have key : 5 ∣ m + e * 2 ^ b := by
      have h1 : (e * 2 ^ b) % 5 = (e * (2 ^ b % 5)) % 5 :=
        (Nat.ModEq.mul_left e (Nat.mod_modEq (2 ^ b) 5)).symm
      omega
    have heq : 10 * 5 ^ b * m + 10 ^ (b + 1) * e
        = 10 * 5 ^ b * (m + e * 2 ^ b) := by
      rw [show (10:ℕ) ^ (b + 1) = 10 * (2 ^ b * 5 ^ b) by
            rw [← Nat.mul_pow, pow_succ, mul_comm]]
      ring
    rw [heq, show 10 * 5 ^ (b + 1) = 10 * 5 ^ b * 5 by rw [pow_succ]; ring]
    exact Nat.mul_dvd_mul_left _ key

lemma exists_alternating_multiple' {n : ℕ} (hn : 0 < n) (h20 : ¬ 20 ∣ n) :
    ∃ M, Alternating M ∧ n ∣ M := by
  by_cases h5 : 5 ∣ n
  · have h4 : ¬ 4 ∣ n := by
      intro h4
      exact h20 ((Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) h4 h5))
    obtain ⟨b, c, hc5, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' 5 (by norm_num)
    have hb : 0 < b := by
      rcases Nat.eq_zero_or_pos b with rfl | h
      · rw [pow_zero, one_mul] at h5
        exact absurd h5 hc5
      · exact h
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    -- use a block of even length `k + 1` for some `k ≥ b'`
    obtain ⟨k, hbk, hkeven⟩ : ∃ k, b' ≤ k ∧ (k + 1) % 2 = 0 := by
      by_cases hpar : (b' + 1) % 2 = 0
      · exact ⟨b', Nat.le_refl _, hpar⟩
      · exact ⟨b' + 1, Nat.le_succ _, by omega⟩
    obtain ⟨L, hlen, hnice, hdvd⟩ := five_block k
    have hdvd' : 2 ^ 1 * 5 ^ (b' + 1) ∣ Nat.ofDigits 10 L := by
      refine dvd_trans ?_ hdvd
      rw [show (10:ℕ) * 5 ^ k = 2 ^ 1 * 5 ^ (k + 1) by rw [pow_succ]; ring]
      exact Nat.mul_dvd_mul_left _ (pow_dvd_pow 5 (by omega))
    obtain ⟨v, hv2, hv5, hvdvd⟩ : ∃ v, ¬ 2 ∣ v ∧ ¬ 5 ∣ v ∧
        5 ^ (b' + 1) * c ∣ 2 ^ 1 * 5 ^ (b' + 1) * v := by
      rcases Nat.even_or_odd c with ⟨v, hv⟩ | hco
      · exact ⟨v, fun h2 ↦ h4 (Dvd.dvd.mul_left (by omega : (4:ℕ) ∣ c) _),
          fun h5' ↦ hc5 (by omega), ⟨1, by rw [hv]; ring⟩⟩
      · exact ⟨c, by have := Nat.odd_iff.mp hco; omega, hc5, ⟨2, by ring⟩⟩
    exact exists_alt_multiple_of_dvd hv2 hv5
      (List.ne_nil_of_length_pos (by omega)) (by omega) hnice hdvd' hvdvd
  · obtain ⟨a, u, hu2, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' 2 (by norm_num)
    have hu5 : ¬ 5 ∣ u := fun h ↦ h5 (h.mul_left _)
    obtain ⟨L, hlen, hnice, hdvd⟩ := two_block a
    have h2a : (2:ℕ) ^ a * 5 ^ 0 ∣ Nat.ofDigits 10 L := by
      rw [pow_zero, mul_one]
      exact (pow_dvd_pow 2 (by omega)).trans hdvd
    exact exists_alt_multiple_of_dvd hu2 hu5
      (List.ne_nil_of_length_pos (by omega)) (by omega) hnice h2a
      (dvd_of_eq (by rw [pow_zero, mul_one]))

snip end

problem imo2004_p6 (n : ℕ) :
    n ∈ SolutionSet ↔ 0 < n ∧ ∃ k, Alternating (n * k) := by
  constructor
  · rintro ⟨hnpos, h20⟩
    refine ⟨hnpos, ?_⟩
    obtain ⟨M, hM, k, rfl⟩ := exists_alternating_multiple' hnpos h20
    exact ⟨k, hM⟩
  · rintro ⟨hnpos, k, halt⟩
    exact ⟨hnpos, fun h20 ↦ not_alternating_of_dvd_twenty (h20.mul_right k) halt⟩

end Imo2004P6
