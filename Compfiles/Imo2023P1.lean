/-
Copyright (c) 2023 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clayton Knittel
-/

module

public import Mathlib.Tactic

public import ProblemExtraction

@[expose] public section

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 2023, Problem 1

Determine all composite integers n>1 that satisfy the following property:
if d₁,d₂,...,dₖ are all the positive divisors of n with
1 = d₁ < d₂ < ... < dₖ = n, then dᵢ divides dᵢ₊₁ + dᵢ₊₂ for every
1 ≤ i ≤ k - 2.
-/

namespace Imo2023P1

abbrev ConsecutiveFactors (n a b : ℕ) :=
  a ∣ n ∧ b ∣ n ∧ a < b ∧ ¬∃ c, (c ∣ n ∧ a < c ∧ c < b)

abbrev Dividable (n : ℕ) :=
  ∀ {a b c : ℕ},
    ConsecutiveFactors n a b ∧ ConsecutiveFactors n b c
    → a ∣ b + c

snip begin

/-- The complementary divisors of consecutive factors of `n` are themselves
 consecutive factors of `n`. -/
lemma consecutiveFactors_div {n a b : ℕ} (hn : 0 < n) (h : ConsecutiveFactors n a b) :
    ConsecutiveFactors n (n / b) (n / a) := by
  obtain ⟨ha, hb, hab, hc⟩ := h
  refine ⟨Nat.div_dvd_of_dvd hb, Nat.div_dvd_of_dvd ha,
    (Nat.div_lt_div_left hn.ne' hb ha).mpr hab, fun ⟨c, hcn, hbc, hca⟩ ↦ hc ⟨n / c, ?_⟩⟩
  have hc' := Nat.div_dvd_of_dvd hcn
  rw [← Nat.div_div_self hcn hn.ne'] at hbc hca
  exact ⟨hc', (Nat.div_lt_div_left hn.ne' hc' ha).mp hca,
    (Nat.div_lt_div_left hn.ne' hb hc').mp hbc⟩

/-- The divisors of a prime power form a chain under divisibility, so every prime
 power is `Dividable`. -/
lemma isPrimePow_dividable {n : ℕ} (h : IsPrimePow n) : Dividable n := by
  obtain ⟨p, k, hp, -, rfl⟩ := h
  have chain : ∀ {x y}, x ∣ p ^ k → y ∣ p ^ k → x < y → x ∣ y := by
    intro x y hx hy hxy
    obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow hp.nat_prime).mp hx
    obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp.nat_prime).mp hy
    exact pow_dvd_pow p ((Nat.pow_lt_pow_iff_right hp.nat_prime.one_lt).mp hxy).le
  rintro a b c ⟨⟨ha, hb, hab, -⟩, ⟨-, hc, hbc, -⟩⟩
  exact dvd_add (chain ha hb hab) (chain ha hc (hab.trans hbc))

/-- All `Dividable` numbers `> 1` are prime powers.

 Let `p` be the smallest prime factor of `n` and suppose that `q` is the smallest
 divisor of `n` that is not a power of `p`. The divisors of `n` below `q` are
 `1, p, ..., p ^ (m + 1)`, so `p ^ m`, `p ^ (m + 1)`, `q` are consecutive
 factors. Applying the hypothesis to their complementary divisors gives
 `p ^ (m + 1) ∣ q * (p + 1)`, hence `p ∣ q`. But then `q / p` is a smaller
 divisor of `n`, so it is a power of `p`, and therefore so is `q`. -/
lemma dividable_isPrimePow {n : ℕ} (hn : 1 < n) (hd : Dividable n) : IsPrimePow n := by
  classical
  have hn0 : 0 < n := by lia
  set p := n.minFac
  have hp : p.Prime := Nat.minFac_prime hn.ne'
  by_contra hnp
  -- Let `q` be the least divisor of `n` that is not a power of `p`.
  have hex : ∃ q, q ∣ n ∧ ∀ i, q ≠ p ^ i := by
    refine ⟨n, dvd_rfl, fun i hi ↦ hnp ?_⟩
    rw [hi]
    exact hp.prime.isPrimePow.pow (by rintro rfl; simp at hi; lia)
  obtain ⟨⟨hqn, hq⟩, hmin⟩ := Nat.find_spec hex, @Nat.find_min _ _ hex
  set q := Nat.find hex
  replace hmin : ∀ d, d ∣ n → d < q → ∃ i, d = p ^ i := by
    intro d hdn hdq
    by_contra! hd'
    exact hmin hdq ⟨hdn, hd'⟩
  have hq0 : 0 < q := Nat.pos_of_dvd_of_pos hqn hn0
  have hq1 : q ≠ 1 := by simpa using hq 0
  have hpq : p < q :=
    lt_of_le_of_ne (Nat.minFac_le_of_dvd (by lia) hqn) (by simpa using (hq 1).symm)
  -- Let `p ^ (m + 1)` be the largest power of `p` that divides `n` and is less than `q`.
  have hex' : ∃ j, ¬(p ^ (j + 1) ∣ n ∧ p ^ (j + 1) < q) :=
    ⟨q, fun h ↦ absurd h.2 (by have := Nat.lt_pow_self hp.one_lt (n := q + 1); lia)⟩
  obtain ⟨m, hm⟩ : ∃ m, Nat.find hex' = m + 1 :=
    Nat.exists_eq_succ_of_ne_zero fun h0 ↦
      ((Nat.find_eq_zero hex').mp h0) ⟨by simpa using n.minFac_dvd, by simpa using hpq⟩
  have hm1 : p ^ (m + 1) ∣ n ∧ p ^ (m + 1) < q := by
    have := Nat.find_min hex' (m := m) (by lia)
    tauto
  have hm2 : ¬(p ^ (m + 2) ∣ n ∧ p ^ (m + 2) < q) := by
    have := Nat.find_spec hex'
    rwa [hm] at this
  have pow_lt {i j : ℕ} : p ^ i < p ^ j ↔ i < j := Nat.pow_lt_pow_iff_right hp.one_lt
  have c1 : ConsecutiveFactors n (p ^ m) (p ^ (m + 1)) := by
    refine ⟨(pow_dvd_pow p m.le_succ).trans hm1.1, hm1.1, pow_lt.mpr m.lt_succ_self, ?_⟩
    rintro ⟨c, hcn, hc1, hc2⟩
    obtain ⟨i, rfl⟩ := hmin c hcn (hc2.trans hm1.2)
    rw [pow_lt] at hc1 hc2
    lia
  have c2 : ConsecutiveFactors n (p ^ (m + 1)) q := by
    refine ⟨hm1.1, hqn, hm1.2, ?_⟩
    rintro ⟨c, hcn, hc1, hc2⟩
    obtain ⟨i, rfl⟩ := hmin c hcn hc2
    rw [pow_lt] at hc1
    have h := pow_dvd_pow p (show m + 2 ≤ i by lia)
    exact hm2 ⟨h.trans hcn, (Nat.le_of_dvd (pow_pos hp.pos _) h).trans_lt hc2⟩
  -- Apply the hypothesis to the complementary divisors.
  have key := hd ⟨consecutiveFactors_div hn0 c2, consecutiveFactors_div hn0 c1⟩
  obtain ⟨t, ht⟩ := id hqn
  obtain ⟨u, hu⟩ := hm1.1
  have hu0 : 0 < u := Nat.pos_of_ne_zero (by rintro rfl; lia)
  have h1 : n / q = t := by rw [ht]; exact Nat.mul_div_cancel_left t hq0
  have h2 : n / p ^ (m + 1) = u := by rw [hu]; exact Nat.mul_div_cancel_left u (pow_pos hp.pos _)
  have h3 : n / p ^ m = p * u := by
    rw [hu, pow_succ, mul_assoc]; exact Nat.mul_div_cancel_left _ (pow_pos hp.pos _)
  rw [h1, h2, h3] at key
  have h4 : p ^ (m + 1) * u ∣ q * (p + 1) * u :=
    calc p ^ (m + 1) * u = q * t := by rw [← hu, ht]
      _ ∣ q * (u + p * u) := mul_dvd_mul_left q key
      _ = q * (p + 1) * u := by ring
  have h5 : p ∣ q * (p + 1) :=
    (dvd_pow_self p m.succ_ne_zero).trans (Nat.dvd_of_mul_dvd_mul_right hu0 h4)
  -- So `p ∣ q`, and `q / p` is a smaller divisor of `n`, hence a power of `p`.
  obtain ⟨q', hq'⟩ : p ∣ q := (Nat.Coprime.dvd_of_dvd_mul_right (by simp) h5)
  obtain ⟨i, rfl⟩ := hmin q' ((Dvd.intro_left p hq'.symm).trans hqn)
    (by have := hp.one_lt; nlinarith)
  exact hq (i + 1) (by rw [hq', pow_succ'])

snip end

determine solution_set : Set ℕ := { n | ¬n.Prime ∧ IsPrimePow n }

problem imo2023_p1 : solution_set = { n | 1 < n ∧ ¬n.Prime ∧ Dividable n } := by
  ext x
  exact ⟨fun ⟨hx₁, hx₂⟩ ↦ ⟨hx₂.one_lt, hx₁, isPrimePow_dividable hx₂⟩,
    fun ⟨hx₁, hx₂, hx₃⟩ ↦ ⟨hx₂, dividable_isPrimePow hx₁ hx₃⟩⟩

end Imo2023P1
