/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ansar Azhdarov
-/

import Mathlib.Tactic

import ProblemExtraction

set_option backward.isDefEq.respectTransparency false

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 2014, Problem 2

Let ℤ be the set of integers. Find all functions f : ℤ → ℤ such that
x * f(2 * f(y) - x) + y ^ 2 * f(2 * x - f(y)) = (f(x) ^ 2) / x + f(y * f(y))
for all x, y ∈ ℤ with x ≠ 0.
-/

namespace Usa2014P2

def P (f : ℤ → ℤ) :=
    ∀ x y, x ≠ 0 → x * f (2 * f y - x) + y ^ 2 * f (2 * x - f y) = (f x ^ 2 : ℚ) / x + f (y * f y)

determine S : Set (ℤ → ℤ) := {0, fun x ↦ x ^ 2}

snip begin

lemma mpr {f : ℤ → ℤ} : f ∈ S → P f := by
  intro h x y hx
  rcases h with rfl | rfl
  · simp
  · grind

lemma exists_prime_and_not_dvd {n : ℤ} (hn : n ≠ 0) : ∃ p, Prime p ∧ ¬ p ∣ n := by
  obtain ⟨p, hp1, hp2⟩ := Nat.exists_infinite_primes (n.natAbs + 1)
  refine ⟨p, Nat.prime_iff_prime_int.mp hp2, ?_⟩
  rw [Nat.succ_le_iff] at hp1
  intro hpn
  rw [← Int.dvd_natAbs, Int.ofNat_dvd] at hpn
  apply Nat.le_of_dvd (Int.natAbs_pos.mpr hn) at hpn
  lia

snip end

problem usa2014_p2 {f : ℤ → ℤ} : P f ↔ f ∈ S := by
  -- The solution is adapted from https://web.evanchen.cc/exams/USAMO-2014-notes.pdf
  refine ⟨?_ , mpr⟩
  intro h

  have h1 : f 0 = 0 := by
    by_contra! hg
    obtain ⟨p, hp, hp1⟩ := exists_prime_and_not_dvd hg
    have hp2 : p ≠ 0 := Prime.ne_zero hp
    specialize h p 0 hp2
    simp at h
    field_simp at h
    have : p ∣ f p := by
      have : p ∣ f p ^ 2:= by
        use p * f (2 * f 0 - p) - f 0
        qify
        linarith
      exact Prime.dvd_of_dvd_pow hp this
    obtain ⟨k, hk⟩ := this
    apply congrArg (· / (p : ℚ)) at h
    simp [hk] at h
    field_simp at h
    have : p ∣ f 0 := by
      use f (2 * f 0 - p) - k ^ 2
      qify
      linarith
    contradiction

  have h2 (x : ℤ) : x ^ 2 * f (-x) = f x ^ 2 := by
    by_cases! hx : x = 0
    · simp [hx, h1]
    · specialize h x 0 hx
      simp [h1] at h
      field_simp at h
      qify
      lia

  have h3 (x : ℤ) : x ^ 2 * f x = f (-x) ^ 2 := by
    specialize h2 (-x)
    rw [neg_neg] at h2
    linarith

  have h4 (x : ℤ) : f x = f (-x) := by
    by_cases! hx : x = 0
    · simp [hx, h1]
    · by_contra! hg
      have := congrArg₂ (fun x y ↦ x - y) (h2 x) (h3 x)
      have : f x + f (-x) = - x ^ 2 := by
        simp only at this
        rw [← mul_sub, sq_sub_sq, ← neg_sub, ← neg_mul_comm] at this
        apply Int.eq_of_mul_eq_mul_right (sub_ne_zero_of_ne hg) at this
        lia
      have hx1 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
      have : 0 ≤ f x := by
        apply nonneg_of_mul_nonneg_right _ hx1
        simp [h3 x, sq_nonneg]
      have : 0 ≤ f (-x) := by
        apply nonneg_of_mul_nonneg_right _ hx1
        simp [h2 x, sq_nonneg]
      lia

  have h5 (x : ℤ) (hx : f x ≠ 0) : f x = x ^ 2 := by
    simpa [← h4, pow_two (f x), hx] using (h3 x).symm

  wlog h6 : ∃ t, t ≠ 0 ∧ f t = 0
  · push_neg at h6
    right
    funext x
    by_cases! hx : x = 0
    · simp [hx, h1]
    · exact h5 x (h6 x hx)

  left

  have h7 (x : ℤ) : f (2 * x) = 0 := by
    by_cases! hx : x = 0
    · simp [hx, h1]
    · obtain ⟨t, ht, ht1⟩ := h6
      specialize h x t hx
      apply congrArg ((x : ℚ) * ·) at h
      field_simp at h
      qify at h2
      rw [mul_add, ← mul_assoc, ← pow_two] at h
      simpa [ht1, h1, h2, hx, ht] using h

  funext m
  by_contra! hm
  rw [Pi.zero_apply] at hm

  have hm1 : m ≠ 0 := by
    contrapose! hm
    simp [hm, h1]

  have hm2 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm1

  have hm3 : f m = m ^ 2 := h5 m hm

  have hm4 : Odd m := by
    by_contra! hg
    rw [Int.not_odd_iff_even, even_iff_exists_two_mul] at hg
    obtain ⟨k, rfl⟩ := hg
    exact hm (h7 k)

  have h8 (k y : ℤ) (hk : k ≠ 0) : y ^ 2 * f (4 * k - f y) = f (y * f y) := by
    qify
    specialize h (2 * k) y (mul_ne_zero two_ne_zero hk)
    rw [← mul_sub, ← mul_assoc, ← pow_two] at h
    simpa [h7] using h

  have h9 (k : ℤ) (hk : k ≠ 0) : m ^ 2 * f (4 * k - m ^ 2) = f (m ^ 3) := by
    simpa [hm3, ← Int.pow_succ'] using h8 k m hk

  have h10 : f (m ^ 3) = 0 := by
    by_contra! hg
    have _h (k : ℤ) (hk : k ≠ 0) : f (4 * k - m ^ 2) = (4 * k - m ^ 2) ^ 2 := by
      specialize h9 k hk
      rw [← h9, mul_ne_zero_iff] at hg
      exact h5 (4 * k - m ^ 2) hg.right
    have _hm : f (m ^ 3) = m ^ 6 := by
      simpa [← pow_mul] using h5 (m ^ 3) hg
    specialize h9 (m ^ 2) hm2
    simp [_h, _hm, hm2] at h9
    ring_nf at h9
    lia

  have h11 (k : ℤ) (hk : k ≠ 0) : f (4 * k - m ^ 2) = 0 := by
    specialize h9 k hk
    simpa [h10, hm2] using h9

  have h12 (k : ℤ) (hk : k ≠ 0) : f (m ^ 2 - 4 * k) = 0 := by
    rw [← neg_sub, ← h4, h11 k hk]

  have hm5 : ∃ k, 4 * k + 1 = m ^ 2 := by
    obtain ⟨k, hk⟩ := hm4
    use k ^ 2 + k
    rw [hk]
    ring

  obtain ⟨l, hl⟩ := hm5

  have h13 (k : ℤ) (hk : l ≠ k) : f (4 * k + 1) = 0 := by
    specialize h12 (l - k) (sub_ne_zero_of_ne hk)
    simp [← hl] at h12
    ring_nf at h12
    rw [add_comm, mul_comm, h12]

  have h14 (k : ℤ) (hk : l + (k + 1) ≠ 0) : f (4 * k + 3) = 0 := by
    specialize h11 (l + (k + 1)) hk
    simp [← hl] at h11
    ring_nf at h11
    rw [add_comm, mul_comm, h11]

  have hm6 : ∃ k, 4 * k + 1 = m ∨ 4 * k + 3 = m := by
    obtain ⟨k, rfl⟩ := hm4
    rcases Int.even_or_odd k with ⟨n, rfl⟩ | ⟨n, rfl⟩
    · exact ⟨n, by left; ring⟩
    · exact ⟨n, by right; ring⟩

  obtain ⟨n, hn⟩ := hm6

  rcases hn with hn | hn
  · have : l = n := by
      by_contra! hg
      specialize h13 n hg
      rw [hn] at h13
      contradiction
    have : m = m ^ 2 := by
      rw [← hl, ← hn, this]
    grind
  · have : l + (n + 1) = 0 := by
      by_contra! hg
      specialize h14 n hg
      rw [hn] at h14
      contradiction
    have : m = - m ^ 2 := by
      rw [← hl, ← hn]
      lia
    grind

end Usa2014P2
