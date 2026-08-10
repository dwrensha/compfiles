/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Kimi K3
-/

module

public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.NumberTheory.PythagoreanTriples
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.NumberTheory] }

/-!
# Bulgarian Mathematical Olympiad 1998, Problem 6

Prove that the equation

     x²y² = z²(z² - x² - y²)

has no solutions in positive integers.

-/

namespace Bulgaria1998P6

snip begin

/-- The square of an odd integer is `1` modulo `4`. -/
lemma sq_mod_four_of_odd {z : ℤ} (hz : z % 2 = 1) : z ^ 2 % 4 = 1 := by
  obtain ⟨k, rfl⟩ : Odd z := Int.odd_iff.mpr hz
  have h : (2 * k + 1) ^ 2 = 1 + 4 * (k ^ 2 + k) := by ring
  omega

/-- The descent step for the case where the even leg is a square: from coprime `p`, `q`
of opposite parity with `a = p ^ 2 + q ^ 2` and `b ^ 2 = 4 * p * q * (p ^ 2 - q ^ 2)` we
produce a smaller solution of `A ^ 4 = B ^ 4 + C ^ 2` in positive naturals. -/
lemma descent_aux {a b p q : ℤ} (ha : 0 < a) (_hb : 0 < b)
    (hp : 0 < p) (hq : 0 < q) (hpq : q < p)
    (hgcd : Int.gcd p q = 1)
    (hpar : (p % 2 = 0 ∧ q % 2 = 1) ∨ (p % 2 = 1 ∧ q % 2 = 0))
    (haeq : a = p ^ 2 + q ^ 2)
    (hbeq : b ^ 2 = 4 * (p * q * (p ^ 2 - q ^ 2)))
    (hb2 : 2 ∣ b) :
    ∃ A B C : ℕ, 0 < A ∧ 0 < B ∧ 0 < C ∧ A < Int.natAbs a ∧ A ^ 4 = B ^ 4 + C ^ 2 := by
  obtain ⟨b', hb'⟩ := hb2
  have hb'2 : b' ^ 2 = p * q * (p ^ 2 - q ^ 2) := by
    apply (mul_right_inj' (by norm_num : (4 : ℤ) ≠ 0)).mp
    linear_combination hbeq - (b + 2 * b') * hb'
  -- pairwise coprimality of `p`, `q`, `p - q`, `p + q`
  have g2 : Int.gcd p (p - q) = 1 := by
    have h1 : ((Int.gcd p (p - q) : ℕ) : ℤ) ∣ p := Int.gcd_dvd_left p (p - q)
    have h2 : ((Int.gcd p (p - q) : ℕ) : ℤ) ∣ p - q := Int.gcd_dvd_right p (p - q)
    have h3 : ((Int.gcd p (p - q) : ℕ) : ℤ) ∣ q := by
      have h := dvd_sub h1 h2
      rwa [show p - (p - q) = q by ring] at h
    have h4 := Int.dvd_coe_gcd h1 h3
    rw [hgcd] at h4
    exact Nat.dvd_one.mp (Int.natCast_dvd.mp h4)
  have g3 : Int.gcd p (p + q) = 1 := by
    have h1 : ((Int.gcd p (p + q) : ℕ) : ℤ) ∣ p := Int.gcd_dvd_left p (p + q)
    have h2 : ((Int.gcd p (p + q) : ℕ) : ℤ) ∣ p + q := Int.gcd_dvd_right p (p + q)
    have h3 : ((Int.gcd p (p + q) : ℕ) : ℤ) ∣ q := by
      have h := dvd_sub h2 h1
      rwa [show p + q - p = q by ring] at h
    have h4 := Int.dvd_coe_gcd h1 h3
    rw [hgcd] at h4
    exact Nat.dvd_one.mp (Int.natCast_dvd.mp h4)
  have g4 : Int.gcd q (p - q) = 1 := by
    have h1 : ((Int.gcd q (p - q) : ℕ) : ℤ) ∣ q := Int.gcd_dvd_left q (p - q)
    have h2 : ((Int.gcd q (p - q) : ℕ) : ℤ) ∣ p - q := Int.gcd_dvd_right q (p - q)
    have h3 : ((Int.gcd q (p - q) : ℕ) : ℤ) ∣ p := by
      have h := dvd_add h2 h1
      rwa [show p - q + q = p by ring] at h
    have h4 := Int.dvd_coe_gcd h3 h1
    rw [hgcd] at h4
    exact Nat.dvd_one.mp (Int.natCast_dvd.mp h4)
  have g5 : Int.gcd q (p + q) = 1 := by
    have h1 : ((Int.gcd q (p + q) : ℕ) : ℤ) ∣ q := Int.gcd_dvd_left q (p + q)
    have h2 : ((Int.gcd q (p + q) : ℕ) : ℤ) ∣ p + q := Int.gcd_dvd_right q (p + q)
    have h3 : ((Int.gcd q (p + q) : ℕ) : ℤ) ∣ p := by
      have h := dvd_sub h2 h1
      rwa [show p + q - q = p by ring] at h
    have h4 := Int.dvd_coe_gcd h3 h1
    rw [hgcd] at h4
    exact Nat.dvd_one.mp (Int.natCast_dvd.mp h4)
  have g6 : Int.gcd (p - q) (p + q) = 1 := by
    have h1 : ((Int.gcd (p - q) (p + q) : ℕ) : ℤ) ∣ p - q := Int.gcd_dvd_left (p - q) (p + q)
    have h2 : ((Int.gcd (p - q) (p + q) : ℕ) : ℤ) ∣ p + q := Int.gcd_dvd_right (p - q) (p + q)
    have h3 : ((Int.gcd (p - q) (p + q) : ℕ) : ℤ) ∣ 2 * p := by
      have h := dvd_add h2 h1
      rwa [show p + q + (p - q) = 2 * p by ring] at h
    have h4 : ((Int.gcd (p - q) (p + q) : ℕ) : ℤ) ∣ 2 * q := by
      have h := dvd_sub h2 h1
      rwa [show p + q - (p - q) = 2 * q by ring] at h
    obtain ⟨u, v, huv⟩ := Int.isCoprime_iff_gcd_eq_one.mpr hgcd
    have h5 : ((Int.gcd (p - q) (p + q) : ℕ) : ℤ) ∣ 2 := by
      have h6 : ((Int.gcd (p - q) (p + q) : ℕ) : ℤ) ∣ u * (2 * p) + v * (2 * q) :=
        dvd_add (dvd_mul_of_dvd_right h3 u) (dvd_mul_of_dvd_right h4 v)
      have h7 : u * (2 * p) + v * (2 * q) = 2 := by linear_combination 2 * huv
      rwa [h7] at h6
    have h8 : Int.gcd (p - q) (p + q) ∣ 2 := by exact_mod_cast h5
    have h9 : Int.gcd (p - q) (p + q) ≤ 2 := Nat.le_of_dvd (by norm_num) h8
    have hodd : (p + q) % 2 = 1 := by
      rcases hpar with ⟨hp1, hq1⟩ | ⟨hp1, hq1⟩ <;> omega
    have hpos : 0 < Int.gcd (p - q) (p + q) := by
      rcases Nat.eq_zero_or_pos (Int.gcd (p - q) (p + q)) with h | h
      · exfalso
        rw [Int.gcd_eq_zero_iff] at h
        linarith [h.1]
      · exact h
    rcases (by omega : Int.gcd (p - q) (p + q) = 1 ∨ Int.gcd (p - q) (p + q) = 2) with h | h
    · exact h
    · exfalso
      rw [h] at h2
      have h2' : (2 : ℤ) ∣ p + q := by exact_mod_cast h2
      omega
  -- extracting the squares from `(b / 2) ^ 2 = p * q * (p - q) * (p + q)`
  have hs1 : p * (q * ((p - q) * (p + q))) = b' ^ 2 := by linear_combination -hb'2
  have gA : Int.gcd p (q * ((p - q) * (p + q))) = 1 := by
    apply Int.isCoprime_iff_gcd_eq_one.mp
    exact (Int.isCoprime_iff_gcd_eq_one.mpr hgcd).mul_right
      ((Int.isCoprime_iff_gcd_eq_one.mpr g2).mul_right (Int.isCoprime_iff_gcd_eq_one.mpr g3))
  obtain ⟨r, hr⟩ := Int.sq_of_gcd_eq_one gA hs1
  have hr' : p = r ^ 2 := by
    rcases hr with h | h
    · exact h
    · exfalso; linarith [sq_nonneg r, hp]
  have hr0 : r ≠ 0 := by rintro rfl; simp at hr'; linarith
  have hs2 : (q * ((p - q) * (p + q))) * p = b' ^ 2 := by rw [mul_comm]; exact hs1
  have gA' : Int.gcd (q * ((p - q) * (p + q))) p = 1 := by rw [Int.gcd_comm]; exact gA
  obtain ⟨d0, hd0⟩ := Int.sq_of_gcd_eq_one gA' hs2
  have hpos1 : (0 : ℤ) < q * ((p - q) * (p + q)) :=
    mul_pos hq (mul_pos (sub_pos.mpr hpq) (add_pos hp hq))
  have hd0' : q * ((p - q) * (p + q)) = d0 ^ 2 := by
    rcases hd0 with h | h
    · exact h
    · exfalso; linarith [sq_nonneg d0, hpos1]
  have gB : Int.gcd q ((p - q) * (p + q)) = 1 := by
    apply Int.isCoprime_iff_gcd_eq_one.mp
    exact (Int.isCoprime_iff_gcd_eq_one.mpr g4).mul_right (Int.isCoprime_iff_gcd_eq_one.mpr g5)
  obtain ⟨s, hs⟩ := Int.sq_of_gcd_eq_one gB hd0'
  have hs' : q = s ^ 2 := by
    rcases hs with h | h
    · exact h
    · exfalso; linarith [sq_nonneg s, hq]
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs'; linarith
  have hs4 : ((p - q) * (p + q)) * q = d0 ^ 2 := by rw [mul_comm]; exact hd0'
  have gB' : Int.gcd ((p - q) * (p + q)) q = 1 := by rw [Int.gcd_comm]; exact gB
  obtain ⟨e0, he0⟩ := Int.sq_of_gcd_eq_one gB' hs4
  have hpos2 : (0 : ℤ) < (p - q) * (p + q) := mul_pos (sub_pos.mpr hpq) (add_pos hp hq)
  have he0' : (p - q) * (p + q) = e0 ^ 2 := by
    rcases he0 with h | h
    · exact h
    · exfalso; linarith [sq_nonneg e0, hpos2]
  obtain ⟨w, hw⟩ := Int.sq_of_gcd_eq_one g6 he0'
  have hw' : p - q = w ^ 2 := by
    rcases hw with h | h
    · exact h
    · exfalso; linarith [sq_nonneg w, sub_pos.mpr hpq]
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw'; linarith [sub_pos.mpr hpq]
  have hs6 : (p + q) * (p - q) = e0 ^ 2 := by rw [mul_comm]; exact he0'
  have gC' : Int.gcd (p + q) (p - q) = 1 := by rw [Int.gcd_comm]; exact g6
  obtain ⟨t, ht⟩ := Int.sq_of_gcd_eq_one gC' hs6
  have ht' : p + q = t ^ 2 := by
    rcases ht with h | h
    · exact h
    · exfalso; linarith [sq_nonneg t, add_pos hp hq]
  have ht0 : t ≠ 0 := by rintro rfl; simp at ht'; linarith [add_pos hp hq]
  -- assembling the smaller solution `(r, s, w * t)`
  refine ⟨Int.natAbs r, Int.natAbs s, Int.natAbs (w * t),
    Int.natAbs_pos.mpr hr0, Int.natAbs_pos.mpr hs0,
    Int.natAbs_pos.mpr (mul_ne_zero hw0 ht0), ?_, ?_⟩
  · have e1 : ((Int.natAbs r : ℕ) : ℤ) ≤ p := by
      have h3 := Int.natAbs_le_self_sq r
      rw [← hr'] at h3
      exact h3
    have e2 : p < (Int.natAbs a : ℤ) := by
      rw [Int.natAbs_of_nonneg (le_of_lt ha), haeq]
      have h1 : p ≤ p ^ 2 := Int.le_self_sq p
      have h2 : (0 : ℤ) < q ^ 2 := sq_pos_of_pos hq
      linarith
    exact Int.ofNat_lt.mp (lt_of_le_of_lt e1 e2)
  · have key : p ^ 2 = q ^ 2 + (w * t) ^ 2 := by
      linear_combination (p + q) * hw' + w ^ 2 * ht'
    have e4 : ((Int.natAbs r : ℕ) : ℤ) ^ 4 = p ^ 2 := by
      rw [show ((Int.natAbs r : ℕ) : ℤ) ^ 4 = (((Int.natAbs r : ℕ) : ℤ) ^ 2) ^ 2 by ring,
        Int.natAbs_sq, ← hr']
    have e5 : ((Int.natAbs s : ℕ) : ℤ) ^ 4 = q ^ 2 := by
      rw [show ((Int.natAbs s : ℕ) : ℤ) ^ 4 = (((Int.natAbs s : ℕ) : ℤ) ^ 2) ^ 2 by ring,
        Int.natAbs_sq, ← hs']
    have e6 : ((Int.natAbs (w * t) : ℕ) : ℤ) ^ 2 = (w * t) ^ 2 := Int.natAbs_sq _
    have e : ((Int.natAbs r : ℕ) : ℤ) ^ 4 =
        ((Int.natAbs s : ℕ) : ℤ) ^ 4 + ((Int.natAbs (w * t) : ℕ) : ℤ) ^ 2 := by
      rw [e4, e5, e6]; exact key
    exact_mod_cast e

lemma lemma_1'
    (a b c : ℕ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (h : a^4 = b^4 + c^2) : False := by
  induction' a using Nat.strongRecOn with a ih generalizing b c
  have hz : (a : ℤ) ^ 4 = (b : ℤ) ^ 4 + (c : ℤ) ^ 2 := by exact_mod_cast h
  by_cases hgcd : Nat.gcd a b = 1
  · -- coprime case: first show that `b` and `c` are coprime as well
    have hbc : Nat.Coprime b c := by
      by_contra hbc
      obtain ⟨p, hp, hpb, hpc⟩ := Nat.Prime.not_coprime_iff_dvd.mp hbc
      have hpa : p ∣ a := by
        have e1 : p ^ 2 ∣ b ^ 4 :=
          dvd_trans (pow_dvd_pow p (by norm_num)) (pow_dvd_pow_of_dvd hpb 4)
        have e2 : p ^ 2 ∣ c ^ 2 := pow_dvd_pow_of_dvd hpc 2
        have e3 : p ^ 2 ∣ a ^ 4 := by rw [h]; exact dvd_add e1 e2
        have e4 : p ∣ p ^ 2 := by rw [pow_two]; exact dvd_mul_right p p
        exact hp.dvd_of_dvd_pow (dvd_trans e4 e3)
      have h5 : p ∣ Nat.gcd a b := Nat.dvd_gcd hpa hpb
      rw [hgcd] at h5
      exact hp.ne_one (Nat.dvd_one.mp h5)
    have hpos_a : (0 : ℤ) < a := by exact_mod_cast ha
    have hpos_b : (0 : ℤ) < b := by exact_mod_cast hb
    have hpos_c : (0 : ℤ) < c := by exact_mod_cast hc
    have hpos_a2 : (0 : ℤ) < (a : ℤ) ^ 2 := sq_pos_of_pos hpos_a
    rcases Nat.even_or_odd c with hce | hco
    · -- Case `c` even (hence `b` odd): one classification step suffices
      have hbo : Odd b := by
        by_contra hbne
        rw [Nat.not_odd_iff_even] at hbne
        exact absurd hbc (Nat.Prime.not_coprime_iff_dvd.mpr
          ⟨2, Nat.prime_two, even_iff_two_dvd.mp hbne, even_iff_two_dvd.mp hce⟩)
      have htr : PythagoreanTriple ((b : ℤ) ^ 2) (c : ℤ) ((a : ℤ) ^ 2) := by
        delta PythagoreanTriple
        linear_combination -hz
      have hg2 : Int.gcd ((b : ℤ) ^ 2) (c : ℤ) = 1 := by
        rw [← Int.isCoprime_iff_gcd_eq_one, Int.isCoprime_iff_nat_coprime, Int.natAbs_pow,
          Int.natAbs_natCast, Int.natAbs_natCast]
        exact (Nat.coprime_pow_left_iff (by norm_num) b c).mpr hbc
      have hp2 : (b : ℤ) ^ 2 % 2 = 1 := Int.odd_iff.mp (Odd.natCast hbo).pow
      obtain ⟨m, n, ht1, ht2, ht3, ht4, ht5, ht6⟩ :=
        htr.coprime_classification' hg2 hp2 hpos_a2
      have hm : 0 < m := by
        rcases eq_or_ne m 0 with h0 | h0
        · exfalso
          rw [h0] at ht2
          simp at ht2
          exact absurd ht2 (ne_of_gt hc)
        · exact lt_of_le_of_ne ht6 (Ne.symm h0)
      have hn : 0 < n := by
        have hpos : (0 : ℤ) < 2 * m * n := by rw [← ht2]; exact hpos_c
        exact pos_of_mul_pos_right hpos (by linarith)
      -- the new solution `(m, n, a * b)` is smaller since `m < a`
      have key : m ^ 4 = n ^ 4 + ((a : ℤ) * b) ^ 2 := by
        linear_combination -((a : ℤ) ^ 2 * ht1) - (m ^ 2 - n ^ 2) * ht3
      have hm' : ((Int.natAbs m : ℕ) : ℤ) = m := Int.natAbs_of_nonneg (le_of_lt hm)
      have hn' : ((Int.natAbs n : ℕ) : ℤ) = n := Int.natAbs_of_nonneg (le_of_lt hn)
      have keyN : Int.natAbs m ^ 4 = Int.natAbs n ^ 4 + (a * b) ^ 2 := by
        rw [← hm', ← hn'] at key
        exact_mod_cast key
      have hlt : Int.natAbs m < a := by
        have e1 : m ^ 2 < (a : ℤ) ^ 2 := by linarith [ht3, sq_pos_of_pos hn]
        have e2 : m < (a : ℤ) := by
          by_contra hle
          push Not at hle
          have e3 : (a : ℤ) ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ (le_of_lt hpos_a) hle 2
          linarith
        have e4 : ((Int.natAbs m : ℕ) : ℤ) < (a : ℤ) := by rw [hm']; exact e2
        exact Int.ofNat_lt.mp e4
      exact ih (Int.natAbs m) hlt (Int.natAbs n) (a * b)
        (Int.natAbs_pos.mpr (ne_of_gt hm)) (Int.natAbs_pos.mpr (ne_of_gt hn))
        (Nat.mul_pos ha hb) keyN
    · -- Case `c` odd: then `b` must be even (else `a ^ 4 ≡ 2 (mod 4)`)
      have hbe : Even b := by
        by_contra hbne
        rw [Nat.not_even_iff_odd] at hbne
        have hbo2 : (b : ℤ) % 2 = 1 := Int.odd_iff.mp (Odd.natCast hbne)
        have hco2 : (c : ℤ) % 2 = 1 := Int.odd_iff.mp (Odd.natCast hco)
        have hb4 : (b : ℤ) ^ 4 % 4 = 1 := by
          rw [show (b : ℤ) ^ 4 = ((b : ℤ) ^ 2) ^ 2 by ring]
          exact sq_mod_four_of_odd (Int.odd_iff.mp (Odd.natCast hbne).pow)
        have hc4 : (c : ℤ) ^ 2 % 4 = 1 := sq_mod_four_of_odd hco2
        have ha4 : (a : ℤ) ^ 4 % 4 = 2 := by
          rw [hz, Int.add_emod, hb4, hc4]
          omega
        have h44 : (a : ℤ) ^ 4 = (a : ℤ) ^ 2 * (a : ℤ) ^ 2 := by ring
        rw [h44] at ha4
        exact Int.sq_ne_two_mod_four ((a : ℤ) ^ 2) ha4
      have hpos_b2 : (0 : ℤ) < (b : ℤ) ^ 2 := sq_pos_of_pos hpos_b
      have htr : PythagoreanTriple (c : ℤ) ((b : ℤ) ^ 2) ((a : ℤ) ^ 2) := by
        delta PythagoreanTriple
        linear_combination -hz
      have hg2 : Int.gcd (c : ℤ) ((b : ℤ) ^ 2) = 1 := by
        rw [← Int.isCoprime_iff_gcd_eq_one, Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast,
          Int.natAbs_pow, Int.natAbs_natCast]
        exact ((Nat.coprime_pow_left_iff (by norm_num) b c).mpr hbc).symm
      have hp2 : (c : ℤ) % 2 = 1 := Int.odd_iff.mp (Odd.natCast hco)
      obtain ⟨m, n, ht1, ht2, ht3, ht4, ht5, ht6⟩ :=
        htr.coprime_classification' hg2 hp2 hpos_a2
      have hm : 0 < m := by
        rcases eq_or_ne m 0 with h0 | h0
        · exfalso
          rw [h0] at ht2
          simp at ht2
          exact absurd ht2 (ne_of_gt hb)
        · exact lt_of_le_of_ne ht6 (Ne.symm h0)
      have hn : 0 < n := by
        have hpos : (0 : ℤ) < 2 * m * n := by rw [← ht2]; exact hpos_b2
        exact pos_of_mul_pos_right hpos (by linarith)
      have htr2 : PythagoreanTriple m n (a : ℤ) := by
        delta PythagoreanTriple
        linear_combination -ht3
      obtain ⟨b0, hb0⟩ := hbe
      have hb2 : 2 ∣ (b : ℤ) := by
        use (b0 : ℤ)
        have hb20 : b = 2 * b0 := by omega
        exact_mod_cast hb20
      rcases ht5 with ⟨hm0, hn1⟩ | ⟨hm1, hn0⟩
      · -- `m` even, `n` odd: classify the triple `(n, m, a)`
        obtain ⟨p, q, hu1, hu2, hu3, hu4, hu5, hu6⟩ :=
          (pythagoreanTriple_comm.mp htr2).coprime_classification'
            (by rw [Int.gcd_comm]; exact ht4) hn1 hpos_a
        have hp : 0 < p := by
          rcases eq_or_ne p 0 with h0 | h0
          · exfalso
            rw [h0] at hu2
            simp at hu2
            linarith
          · exact lt_of_le_of_ne hu6 (Ne.symm h0)
        have hq : 0 < q := by
          have hpos : (0 : ℤ) < 2 * p * q := by rw [← hu2]; exact hm
          exact pos_of_mul_pos_right hpos (by linarith)
        have hpq : q < p := by
          have e1 : q ^ 2 < p ^ 2 := by linarith [hu1, hn]
          by_contra hle
          push Not at hle
          have e2 : p ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ (le_of_lt hp) hle 2
          linarith
        have hbeq : (b : ℤ) ^ 2 = 4 * (p * q * (p ^ 2 - q ^ 2)) := by
          linear_combination ht2 + 4 * p * q * hu1 + 2 * n * hu2
        obtain ⟨A, B, C, hA, hB, hC, hlt, hABC⟩ :=
          descent_aux hpos_a hpos_b hp hq hpq hu4 hu5 hu3 hbeq hb2
        rw [Int.natAbs_natCast] at hlt
        exact ih A hlt B C hA hB hC hABC
      · -- `m` odd, `n` even: classify the triple `(m, n, a)`
        obtain ⟨p, q, hu1, hu2, hu3, hu4, hu5, hu6⟩ :=
          htr2.coprime_classification' ht4 hm1 hpos_a
        have hp : 0 < p := by
          rcases eq_or_ne p 0 with h0 | h0
          · exfalso
            rw [h0] at hu2
            simp at hu2
            linarith
          · exact lt_of_le_of_ne hu6 (Ne.symm h0)
        have hq : 0 < q := by
          have hpos : (0 : ℤ) < 2 * p * q := by rw [← hu2]; exact hn
          exact pos_of_mul_pos_right hpos (by linarith)
        have hpq : q < p := by
          have e1 : q ^ 2 < p ^ 2 := by linarith [hu1, hm]
          by_contra hle
          push Not at hle
          have e2 : p ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ (le_of_lt hp) hle 2
          linarith
        have hbeq : (b : ℤ) ^ 2 = 4 * (p * q * (p ^ 2 - q ^ 2)) := by
          linear_combination ht2 + 4 * p * q * hu1 + 2 * m * hu2
        obtain ⟨A, B, C, hA, hB, hC, hlt, hABC⟩ :=
          descent_aux hpos_a hpos_b hp hq hpq hu4 hu5 hu3 hbeq hb2
        rw [Int.natAbs_natCast] at hlt
        exact ih A hlt B C hA hB hC hABC
  · -- non-coprime case: divide out a prime factor of `gcd a b` and descend
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hgcd
    have hpa : p ∣ a := dvd_trans hpd (Nat.gcd_dvd_left a b)
    have hpb : p ∣ b := dvd_trans hpd (Nat.gcd_dvd_right a b)
    obtain ⟨a1, rfl⟩ := hpa
    obtain ⟨b1, rfl⟩ := hpb
    have ha1 : 0 < a1 := by
      rcases Nat.eq_zero_or_pos a1 with h0 | h0
      · simp [h0] at ha
      · exact h0
    have hb1 : 0 < b1 := by
      rcases Nat.eq_zero_or_pos b1 with h0 | h0
      · simp [h0] at hb
      · exact h0
    have hpc : p ^ 2 ∣ c := by
      have hzc : ((p : ℤ) * a1) ^ 4 = ((p : ℤ) * b1) ^ 4 + (c : ℤ) ^ 2 := by exact_mod_cast h
      have e1 : (p : ℤ) ^ 4 ∣ ((p : ℤ) * a1) ^ 4 :=
        pow_dvd_pow_of_dvd (dvd_mul_right (p : ℤ) (a1 : ℤ)) 4
      have e2 : (p : ℤ) ^ 4 ∣ ((p : ℤ) * b1) ^ 4 :=
        pow_dvd_pow_of_dvd (dvd_mul_right (p : ℤ) (b1 : ℤ)) 4
      have e3 : (p : ℤ) ^ 4 ∣ (c : ℤ) ^ 2 := by
        have hsub : (c : ℤ) ^ 2 = ((p : ℤ) * a1) ^ 4 - ((p : ℤ) * b1) ^ 4 := by
          linear_combination -hzc
        rw [hsub]
        exact dvd_sub e1 e2
      have e4 : (p : ℤ) ^ 2 ∣ (c : ℤ) := by
        rw [← Int.pow_dvd_pow_iff two_ne_zero]
        have e5 : ((p : ℤ) ^ 2) ^ 2 = (p : ℤ) ^ 4 := by ring
        rw [e5]
        exact e3
      exact Int.natCast_dvd.mp e4
    obtain ⟨c1, rfl⟩ := hpc
    have hc1 : 0 < c1 := by
      rcases Nat.eq_zero_or_pos c1 with h0 | h0
      · simp [h0] at hc
      · exact h0
    have heq : a1 ^ 4 = b1 ^ 4 + c1 ^ 2 := by
      have h2 : p ^ 4 * a1 ^ 4 = p ^ 4 * (b1 ^ 4 + c1 ^ 2) := by
        calc p ^ 4 * a1 ^ 4 = (p * a1) ^ 4 := by ring
        _ = (p * b1) ^ 4 + (p ^ 2 * c1) ^ 2 := h
        _ = p ^ 4 * (b1 ^ 4 + c1 ^ 2) := by ring
      exact mul_left_cancel₀ (pow_ne_zero 4 hp.ne_zero) h2
    have hlt : a1 < p * a1 := lt_mul_of_one_lt_left ha1 hp.one_lt
    exact ih a1 hlt b1 c1 ha1 hb1 hc1 heq

lemma lemma_1
    {s t u : ℤ}
    (hs : 0 < s)
    (ht : 0 < t)
    (hu : 0 < u)
    (h : s^4 - t^4 = u^2) : False := by
  replace h : s^4 = t^4 + u^2 := eq_add_of_sub_eq' h
  lift s to ℕ using Int.le_of_lt hs
  lift t to ℕ using Int.le_of_lt ht
  lift u to ℕ using Int.le_of_lt hu
  replace hs : 0 < s := Int.natCast_pos.mp hs
  replace ht : 0 < t := Int.natCast_pos.mp ht
  replace hy : 0 < u := Int.natCast_pos.mp hu
  have h' : s ^ 4 = t ^ 4 + u ^ 2 := by exact Int.ofNat_inj.mp h
  exact lemma_1' s t u hs ht hy h'

snip end

problem bulgaria1998_p6
    (x y z : ℤ)
    (hx : 0 < x)
    (hy : 0 < y)
    (_hz : 0 < z)
    (h : x^2 * y^2 = z^2 * (z^2 - x^2 - y^2)) :
    False := by
  -- Follows the informal solution in _Mathematical Olympiads 1998-1999_
  -- (edited by Titu Andreescu and Zuming Feng)

  have h1 : 1 * (z^2 * z^2) + (- (x^2 + y^2)) * z^2 + -(x^2 * y^2) = 0 := by
    rw[h]; ring
  have : NeZero (2 : ℤ) := CharZero.NeZero.two
  have h2 := (quadratic_eq_zero_iff_discrim_eq_sq one_ne_zero (z^2)).mp h1
  dsimp [discrim] at h2
  let a := x^2 + y^2
  let b := 2 * x * y
  have h3 : a^2 + b^2  = (2 * z ^ 2 - (x ^ 2 + y ^ 2)) ^ 2 :=
     by linear_combination h2
  have h4 : IsSquare (a^2 + b^2) := by use 2 * z ^ 2 - (x ^ 2 + y ^ 2); rwa [←sq]
  have h5 : IsSquare (a^2 - b^2) := by use (x^2 - y^2); ring
  have h6 : IsSquare ((a^2 + b^2) * (a^2 - b^2)) := IsSquare.mul h4 h5
  rw [show (a^2 + b^2) * (a^2 - b^2) = a^4 - b^4 by ring] at h6
  obtain ⟨c, hc⟩ := h6
  rw [←sq, ←sq_abs] at hc
  have ha' : 0 < a := by positivity
  have hb' : 0 < b := by positivity
  have hc' : 0 < |c| := by
    obtain hc1 | hc2 | hc3 := lt_trichotomy 0 |c|
    · exact hc1
    · have hab : a^2 = b^2 := by
        rw [← hc2, zero_pow (by norm_num)] at hc
        have hc3 : (a^2)^2 = (b^2)^2 := by linear_combination hc
        have hap : 0 ≤ a^2 := by positivity
        have hbp : 0 ≤ b^2 := by positivity
        exact (pow_left_inj₀ hap hbp two_ne_zero).mp hc3
      rw [hab] at h4
      obtain ⟨r, hr⟩ := h4
      rw [←two_mul, ←sq] at hr
      have h10 : b^2 ∣ r^2 := Dvd.intro_left _ hr
      rw [Int.pow_dvd_pow_iff two_ne_zero] at h10
      obtain ⟨e, rfl⟩ := h10
      rw [show (b * e)^2 = e^2 * b^2 by ring] at hr
      have h11 : b^2 ≠ 0 := by positivity
      have h12 : 2 = e^2 := (Int.mul_eq_mul_right_iff h11).mp hr
      clear h h1 h3 h5 hab
      have h13 : e < 2 := by
        by_contra! H
        have h20 : 2^2 ≤ e^2 := by gcongr
        rw [←h12] at h20
        norm_num at h20
      have h14 : -2 < e := by
        by_contra! H
        replace H : 2 ≤ -e := Int.le_neg_of_le_neg H
        have h20 : 2^2 ≤ (-e)^2 := by gcongr
        rw [neg_sq, ←h12] at h20
        norm_num at h20
      interval_cases e <;> linarith
    · exact (Int.not_lt.mpr (abs_nonneg c) hc3).elim
  exact lemma_1 ha' hb' hc' hc


end Bulgaria1998P6
