/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roozbeh Yousefzadeh
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file {
  tags := [.NumberTheory]
  solutionImportedFrom :=
    "https://github.com/roozbeh-yz/IMO-Steps/blob/main/imo_proofs/imo_1984_p6.lean"
}

/-!
# International Mathematical Olympiad 1984, Problem 6

Let a, b, c, and d be odd integers such that 0 < a < b < c < d and ad = bc.
Prove that if a + d = 2ᵏ and b + c = 2ᵐ for some integers k and m, then
a = 1.
-/

namespace Imo1984P6

snip begin

/-- If `2^m` divides `(y - x) * (y + x)` for odd `x < y`, then almost all of
the factors of 2 land in one of the two factors, since
`gcd (y - x) (y + x) = 2`. -/
lemma two_pow_dvd_or {x y m : ℕ} (hx : Odd x) (hy : Odd y) (hxy : x < y)
    (hdvd : 2 ^ m ∣ (y - x) * (y + x)) :
    2 ^ (m - 1) ∣ y - x ∨ 2 ^ (m - 1) ∣ y + x := by
  obtain hm | hm : m ≤ 1 ∨ 2 ≤ m := by lia
  · -- for m ≤ 1 the claim is trivial, since then 2 ^ (m - 1) = 1
    left
    have h0 : m - 1 = 0 := by lia
    rw [h0, pow_zero]
    exact one_dvd _
  obtain ⟨u, hu⟩ := Nat.Odd.sub_odd hy hx
  obtain ⟨v, hv⟩ := Odd.add_odd hy hx
  obtain ⟨t, ht⟩ := hdvd
  -- u * v = 2 ^ (m - 2) * t, and u + v = y is odd
  have h4 : 2 ^ m = 4 * 2 ^ (m - 2) := by
    rw [show m = 2 + (m - 2) by lia, pow_add]
    norm_num
  have h44 : 4 * (u * v) = 4 * (2 ^ (m - 2) * t) := by
    rw [show 4 * (2 ^ (m - 2) * t) = (4 * 2 ^ (m - 2)) * t by ring, ← h4, ← ht]
    rw [hu, hv]
    ring
  have huv : u * v = 2 ^ (m - 2) * t := Nat.eq_of_mul_eq_mul_left (by norm_num) h44
  have hy2 := Nat.odd_iff.mp hy
  have hm1 : m - 1 = (m - 2) + 1 := by lia
  obtain hu2 | hu2 := Nat.even_or_odd u
  · -- u even forces v odd, so 2^(m-2) ∣ u and hence 2^(m-1) ∣ y - x
    have hv2 : Odd v := by
      rw [Nat.odd_iff]
      have h1 := Nat.even_iff.mp hu2
      lia
    have hco : Nat.Coprime (2 ^ (m - 2)) v :=
      Nat.Coprime.pow_left _ hv2.coprime_two_left
    obtain ⟨s, hs⟩ := hco.dvd_of_dvd_mul_right ⟨t, huv⟩
    exact Or.inl ⟨s, by rw [hu, hs, hm1, pow_succ]; ring⟩
  · -- u odd, so 2^(m-2) ∣ v and hence 2^(m-1) ∣ y + x
    have hco : Nat.Coprime (2 ^ (m - 2)) u :=
      Nat.Coprime.pow_left _ hu2.coprime_two_left
    obtain ⟨s, hs⟩ := hco.dvd_of_dvd_mul_left ⟨t, huv⟩
    exact Or.inr ⟨s, by rw [hv, hs, hm1, pow_succ]; ring⟩

snip end

problem imo_1984_p6
    (a b c d k m : ℕ)
    (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
    (h₁ : Odd a ∧ Odd b ∧ Odd c ∧ Odd d)
    (h₂ : a < b ∧ b < c ∧ c < d)
    (h₃ : a * d = b * c)
    (h₄ : a + d = 2^k)
    (h₅ : b + c = 2^m) :
    a = 1 := by
  obtain ⟨ha0, hb0, hc0, hd0⟩ := h₀
  obtain ⟨ha, hb, hc, hd⟩ := h₁
  obtain ⟨hab, hbc, hcd⟩ := h₂
  have ha2 := Nat.odd_iff.mp ha
  have hb2 := Nat.odd_iff.mp hb
  have hc2 := Nat.odd_iff.mp hc
  -- since b + c ≥ 8, we have m ≥ 3
  have hm3 : 3 ≤ m := by
    by_contra hcon
    interval_cases m <;> lia
  -- a + d > b + c, since ad = bc and the pair {a, d} is more spread out;
  -- hence m < k
  have h₃' : (a : ℤ) * d = b * c := by exact_mod_cast h₃
  have hmk : m < k := by
    have h1 : (0 : ℤ) < ((b : ℤ) - a) * (c - a) := by
      have hab' : (a : ℤ) < b := by exact_mod_cast hab
      have hac' : (a : ℤ) < c := by exact_mod_cast lt_trans hab hbc
      exact mul_pos (by lia) (by lia)
    have h2 : (a : ℤ) * (b + c) < a * (a + d) := by nlinarith
    have h3 : ((b : ℤ) + c) < a + d :=
      lt_of_mul_lt_mul_left h2 (by positivity)
    have h4 : b + c < a + d := by exact_mod_cast h3
    rw [h₄, h₅] at h4
    exact (Nat.pow_lt_pow_iff_right one_lt_two).mp h4
  -- the key identity: b² - a² = 2^m b - 2^k a
  have hkey : (b : ℤ) ^ 2 - a ^ 2 = 2 ^ m * b - 2 ^ k * a := by
    have hcz : (c : ℤ) = 2 ^ m - b := by
      have : ((b + c : ℕ) : ℤ) = ((2 ^ m : ℕ) : ℤ) := by exact_mod_cast h₅
      push_cast at this
      lia
    have hdz : (d : ℤ) = 2 ^ k - a := by
      have : ((a + d : ℕ) : ℤ) = ((2 ^ k : ℕ) : ℤ) := by exact_mod_cast h₄
      push_cast at this
      lia
    rw [hcz, hdz] at h₃'
    linear_combination h₃'
  -- hence 2^m divides (b - a) * (b + a)
  have hdvd : 2 ^ m ∣ (b - a) * (b + a) := by
    have h2k : (2 : ℤ) ^ k = 2 ^ m * 2 ^ (k - m) := by
      rw [← pow_add]
      congr 1
      lia
    have hcast : (((b - a) * (b + a) : ℕ) : ℤ) =
        ((2 ^ m : ℕ) : ℤ) * ((b : ℤ) - 2 ^ (k - m) * a) := by
      rw [Nat.cast_mul, Nat.cast_sub hab.le, Nat.cast_add]
      push_cast
      rw [h2k] at hkey
      linear_combination hkey
    exact Int.natCast_dvd_natCast.mp ⟨_, hcast⟩
  -- 2^(m-1) cannot divide b - a, because 0 < b - a < 2^(m-1)
  have h2m : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']
    congr 1
    lia
  obtain hd1 | hd2 := two_pow_dvd_or ha hb hab hdvd
  · exfalso
    have h1 := Nat.le_of_dvd (by lia) hd1
    lia
  -- so b + a = 2^(m-1), being a multiple of 2^(m-1) less than 2^m
  obtain ⟨q, hq⟩ := hd2
  have hp1 := Nat.two_pow_pos (m - 1)
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hq
    lia
  have hq2 : q < 2 := by
    by_contra hq2
    push Not at hq2
    have h1 : 2 ^ (m - 1) * 2 ≤ 2 ^ (m - 1) * q := Nat.mul_le_mul_left _ hq2
    lia
  have hq1 : q = 1 := by lia
  subst hq1
  rw [mul_one] at hq
  have hba : b + a = 2 ^ (m - 1) := hq
  -- substituting b = 2^(m-1) - a into the key identity gives
  -- a * 2^k = (2^(m-1))²
  have hfin : (a : ℤ) * 2 ^ k = 2 ^ (m - 1) * 2 ^ (m - 1) := by
    have hbz : (b : ℤ) = 2 ^ (m - 1) - a := by
      have : ((b + a : ℕ) : ℤ) = ((2 ^ (m - 1) : ℕ) : ℤ) := by exact_mod_cast hba
      push_cast at this
      lia
    have h2m' : (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) := by exact_mod_cast h2m
    rw [hbz, h2m'] at hkey
    linear_combination hkey
  -- so the odd number a divides a power of 2, whence a = 1
  have hfinN : a * 2 ^ k = 2 ^ (m - 1) * 2 ^ (m - 1) := by exact_mod_cast hfin
  have hdvda : a ∣ 2 ^ ((m - 1) + (m - 1)) := ⟨2 ^ k, by rw [pow_add]; lia⟩
  exact Nat.Coprime.eq_one_of_dvd
    (Nat.Coprime.pow_right _ ha.coprime_two_right) hdvda

end Imo1984P6
