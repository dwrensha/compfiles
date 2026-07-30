/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.ZMod.Units
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 2013, Problem 5

Given positive integers m and n, prove that there is a positive integer c
such that the numbers cm and cn have the same number of occurrences of each
non-zero digit when written in base ten.
-/

namespace Usa2013P5

snip begin

/-- `digitCount t x d` counts the occurrences of the digit `d` among the
first `t` decimal digits of `x` (least significant first), i.e. the digits of
`x` padded with leading zeros to length `t`. -/
def digitCount (t x d : ℕ) : ℕ :=
  ∑ i ∈ Finset.range t, (if (x / 10^i) % 10 = d then 1 else 0)

/-- The `j`-th decimal digit of `x` only depends on `x % 10^(j+1)`, hence
taking `x` modulo a higher power of `10` does not change that digit. -/
lemma mod_pow_div_mod (x j k : ℕ) (h : j + 1 ≤ k) :
    (x % 10^k) / 10^j % 10 = (x / 10^j) % 10 := by
  have e1 : (x % 10^k) / 10^j % 10 = ((x % 10^k) % 10^(j+1)) / 10^j := by
    rw [pow_succ 10 j]
    exact (Nat.mod_mul_right_div_self (x % 10^k) (10^j) 10).symm
  rw [e1, Nat.mod_mod_of_dvd _ (pow_dvd_pow 10 h), pow_succ 10 j,
    Nat.mod_mul_right_div_self]

/-- Multiplication by `10` modulo `10^t - 1` rotates the (padded) `t`-digit
representation of `x` by one place, so it preserves all digit counts. -/
lemma digitCount_mul_ten_mod (t x d : ℕ) (ht : 0 < t) (hx : x < 10^t - 1) :
    digitCount t ((10 * x) % (10^t - 1)) d = digitCount t x d := by
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, (Nat.sub_add_cancel ht).symm⟩
  set P := 10 ^ t' with hP
  have hPpos : 0 < P := pow_pos (by norm_num) _
  have h10t : 10 ^ (t' + 1) = P * 10 := by rw [pow_succ, ← hP]
  set b := x / P with hb
  set w := x % P with hw
  have hxbw : x = b * P + w := by
    rw [hb, hw, Nat.mul_comm (x / P) P]
    exact (Nat.div_add_mod x P).symm
  have hwle : w + 1 ≤ P := Nat.mod_lt x hPpos
  have hble : b ≤ 9 := by
    have hx2 : x < 10 ^ (t' + 1) := Nat.lt_of_lt_of_le hx (Nat.sub_le _ _)
    have h3 : x < 10 * P := by rwa [h10t, Nat.mul_comm P 10] at hx2
    have h4 : b < 10 := (Nat.div_lt_iff_lt_mul hPpos).mpr h3
    omega
  have hkey : b + 10 * w < P * 10 - 1 := by
    have hx' : x < P * 10 - 1 := by rw [← h10t]; exact hx
    by_contra hcon
    push Not at hcon
    have hb9 : b = 9 := by omega
    have hw9 : w = P - 1 := by omega
    have hxe : x = 9 * P + (P - 1) := by rw [hxbw, hb9, hw9]
    have h5 : 9 * P + (P - 1) = P * 10 - 1 := by omega
    omega
  have h10x : 10 * x = (b + 10 * w) + (10 ^ (t' + 1) - 1) * b := by
    have h1 : (10 : ℕ) ^ (t' + 1) = 10 ^ (t' + 1) - 1 + 1 :=
      (Nat.sub_add_cancel (Nat.one_le_pow _ _ (by norm_num))).symm
    have h2 : b * (10 ^ (t' + 1)) = (10 ^ (t' + 1) - 1) * b + b := by
      nth_rewrite 1 [h1]
      ring
    calc 10 * x = b * (10 ^ (t' + 1)) + 10 * w := by rw [hxbw, h10t]; ring
      _ = (b + 10 * w) + (10 ^ (t' + 1) - 1) * b := by rw [h2]; ring
  have hy : (10 * x) % (10 ^ (t' + 1) - 1) = b + 10 * w := by
    rw [h10x, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (show b + 10 * w < 10 ^ (t' + 1) - 1 by rw [h10t]; exact hkey)]
  have hdiv10 : (b + 10 * w) / 10 = w := by
    rw [Nat.add_mul_div_left b w (by norm_num : 0 < 10),
      Nat.div_eq_of_lt (by omega : b < 10), zero_add]
  have hmod0term : (if ((b + 10 * w) / 10 ^ 0) % 10 = d then 1 else 0)
      = (if b = d then 1 else 0) := by
    rw [pow_zero, Nat.div_one, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (by omega : b < 10)]
  have hblastterm : (if (x / 10 ^ t') % 10 = d then 1 else 0)
      = (if b = d then 1 else 0) := by
    rw [← hP, ← hb, Nat.mod_eq_of_lt (by omega : b < 10)]
  have hcongsum :
      (∑ i ∈ Finset.range t', (if ((b + 10 * w) / 10 ^ (i + 1)) % 10 = d then 1 else 0))
        = ∑ i ∈ Finset.range t', (if (x / 10 ^ i) % 10 = d then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have h1 : (b + 10 * w) / 10 ^ (i + 1) = w / 10 ^ i := by
      rw [pow_succ', ← Nat.div_div_eq_div_mul, hdiv10]
    have h2 : (w / 10 ^ i) % 10 = (x / 10 ^ i) % 10 := by
      show ((x % 10 ^ t') / 10 ^ i) % 10 = (x / 10 ^ i) % 10
      exact mod_pow_div_mod x i t' hi
    rw [h1, h2]
  rw [hy]
  simp only [digitCount]
  rw [Finset.sum_range_succ', Finset.sum_range_succ, hmod0term, hblastterm, hcongsum]

/-- Iterating the one-place rotation: multiplication by `10^e` modulo
`10^t - 1` preserves all digit counts. -/
lemma digitCount_pow_ten_mul_mod (t : ℕ) (ht : 0 < t) (x e d : ℕ) (hx : x < 10^t - 1) :
    digitCount t ((10^e * x) % (10^t - 1)) d = digitCount t x d := by
  have hT : 0 < 10^t - 1 :=
    Nat.sub_pos_of_lt (Nat.one_lt_pow (Nat.pos_iff_ne_zero.mp ht) (by norm_num))
  induction e with
  | zero => simp [Nat.mod_eq_of_lt hx]
  | succ e ih =>
    have h1 : (10 ^ (e + 1) * x) % (10^t - 1)
        = (10 * ((10^e * x) % (10^t - 1))) % (10^t - 1) := by
      have h2 : 10 ^ (e + 1) * x = 10 * (10^e * x) := by rw [pow_succ']; ring
      rw [h2]
      exact (Nat.ModEq.mul_left 10 (Nat.mod_modEq _ _)).symm
    rw [h1, digitCount_mul_ten_mod t _ d ht (Nat.mod_lt _ hT), ih]

/-- For a nonzero digit `d`, the number of occurrences of `d` in the decimal
representation of `x` equals `digitCount t x d` whenever `t` is large enough. -/
lemma count_digits_eq_digitCount (x t d : ℕ) (hd : d ≠ 0) (hx : x < 10^t) :
    (Nat.digits 10 x).count d = digitCount t x d := by
  induction t generalizing x with
  | zero =>
    have hx0 : x = 0 := by simpa using hx
    simp [hx0, digitCount]
  | succ t ih =>
    obtain rfl | hxpos := Nat.eq_zero_or_pos x
    · rw [Nat.digits_zero, List.count_nil]
      refine (Finset.sum_eq_zero fun i _ => ?_).symm
      simp [show ¬((0 : ℕ) = d) from mt Eq.symm hd]
    · rw [Nat.digits_def' (by norm_num) hxpos]
      have hcc : ((x % 10) :: Nat.digits 10 (x / 10)).count d
          = (Nat.digits 10 (x / 10)).count d + (if x % 10 = d then 1 else 0) := by
        by_cases h : x % 10 = d <;> simp [h]
      have hxt : x / 10 < 10 ^ t := by
        have h1 : x < 10 ^ t * 10 := by rw [← pow_succ]; exact hx
        exact (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 10)).mpr h1
      rw [hcc, ih (x / 10) hxt]
      have hsum :
          (∑ i ∈ Finset.range t, (if ((x / 10) / 10 ^ i) % 10 = d then 1 else 0))
            = ∑ i ∈ Finset.range t, (if (x / 10 ^ (i + 1)) % 10 = d then 1 else 0) := by
        exact Finset.sum_congr rfl fun i _ => by
          rw [Nat.div_div_eq_div_mul, ← pow_succ']
      simp only [digitCount]
      rw [Finset.sum_range_succ',
        show (if (x / 10 ^ 0) % 10 = d then 1 else 0)
          = (if x % 10 = d then 1 else 0) by simp,
        ← hsum]

lemma two_pow_ge_add_one (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
    rw [pow_succ]
    omega

snip end

problem usa2013_p5 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ∃ c : ℕ, 0 < c ∧ ∀ d ∈ Finset.Icc 1 9,
      (Nat.digits 10 (c * m)).count d = (Nat.digits 10 (c * n)).count d := by
  -- Strip the factors of 2 and 5 from `m`: write `m = 2^r * 5^s * k`.
  set r := m.factorization 2 with hr
  set s := m.factorization 5 with hs
  have hm0 : m ≠ 0 := Nat.ne_of_gt hm
  have h2r : 2 ^ r ∣ m :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hm0).mpr le_rfl
  have h5s : 5 ^ s ∣ m :=
    (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) hm0).mpr le_rfl
  have h25 : 2 ^ r * 5 ^ s ∣ m :=
    (Nat.Coprime.pow r s (by norm_num : Nat.Coprime 2 5)).mul_dvd_of_dvd_of_dvd h2r h5s
  set k := m / (2 ^ r * 5 ^ s) with hk
  have hmk : m = 2 ^ r * 5 ^ s * k := by
    rw [hk, Nat.mul_comm (2 ^ r * 5 ^ s) (m / (2 ^ r * 5 ^ s))]
    exact (Nat.div_mul_cancel h25).symm
  have h2k : ¬ 2 ∣ k := by
    rintro ⟨k', hk'⟩
    have h1 : 2 ^ (r + 1) * 5 ^ s ∣ m := ⟨k', by rw [hmk, hk', pow_succ]; ring⟩
    have h2 : 2 ^ (r + 1) ∣ m := (dvd_mul_right _ _).trans h1
    exact Nat.pow_succ_factorization_not_dvd hm0 Nat.prime_two h2
  have h5k : ¬ 5 ∣ k := by
    rintro ⟨k', hk'⟩
    have h1 : 2 ^ r * 5 ^ (s + 1) ∣ m := ⟨k', by rw [hmk, hk', pow_succ]; ring⟩
    have h2 : 5 ^ (s + 1) ∣ m := (dvd_mul_left _ _).trans h1
    exact Nat.pow_succ_factorization_not_dvd hm0 (by norm_num) h2
  -- Choose the exponent `e` large enough.
  set e := m + m * max m n + 1 with he
  have hre : r + 1 ≤ e := by
    have h1 : r + 1 ≤ 2 ^ r := two_pow_ge_add_one r
    have h2 : 2 ^ r ≤ m := Nat.le_of_dvd hm h2r
    have h3 : m ≤ e := by rw [he]; omega
    exact (h1.trans h2).trans h3
  have hse : s + 1 ≤ e := by
    have h1 : s + 1 ≤ 2 ^ s := two_pow_ge_add_one s
    have h2 : 2 ^ s ≤ 5 ^ s := Nat.pow_le_pow_left (by norm_num) s
    have h3 : 5 ^ s ≤ m := Nat.le_of_dvd hm h5s
    have h4 : m ≤ e := by rw [he]; omega
    exact ((h1.trans h2).trans h3).trans h4
  have hbig : m + 2 ^ r * 5 ^ s * max m n < 10 ^ e * n := by
    have h25m : 2 ^ r * 5 ^ s ≤ m := Nat.le_of_dvd hm h25
    have h10e : m + m * max m n + 1 < 10 ^ e := by
      have h1 : e + 1 ≤ 2 ^ e := two_pow_ge_add_one e
      have h2 : 2 ^ e ≤ 10 ^ e := Nat.pow_le_pow_left (by norm_num) e
      have h3 : m + m * max m n + 1 < e + 1 := by rw [he]; omega
      exact (h3.trans_le h1).trans_le h2
    have h3 : m + 2 ^ r * 5 ^ s * max m n ≤ m + m * max m n := by
      have h4 : 2 ^ r * 5 ^ s * max m n ≤ m * max m n := mul_le_mul_left h25m _
      omega
    have h5 : 10 ^ e ≤ 10 ^ e * n := Nat.le_mul_of_pos_right _ hn
    omega
  have hmn : m ≤ 10 ^ e * n := (Nat.le_add_right _ _).trans (le_of_lt hbig)
  -- The modulus `D`.
  have hA2 : 2 ^ r ∣ 10 ^ e * n - m := by
    apply Nat.dvd_sub _ h2r
    exact ((pow_dvd_pow 2 (by omega : r ≤ e)).trans
      ⟨5 ^ e, by rw [← mul_pow]; norm_num⟩).trans (dvd_mul_right _ _)
  have hA5 : 5 ^ s ∣ 10 ^ e * n - m := by
    apply Nat.dvd_sub _ h5s
    exact ((pow_dvd_pow 5 (by omega : s ≤ e)).trans
      ⟨2 ^ e, by rw [← mul_pow]; norm_num⟩).trans (dvd_mul_right _ _)
  have hA25 : 2 ^ r * 5 ^ s ∣ 10 ^ e * n - m :=
    (Nat.Coprime.pow r s (by norm_num : Nat.Coprime 2 5)).mul_dvd_of_dvd_of_dvd hA2 hA5
  set D := (10 ^ e * n - m) / (2 ^ r * 5 ^ s) with hD
  have hAD : 10 ^ e * n - m = 2 ^ r * 5 ^ s * D := by
    rw [hD, Nat.mul_comm (2 ^ r * 5 ^ s) ((10 ^ e * n - m) / (2 ^ r * 5 ^ s))]
    exact (Nat.div_mul_cancel hA25).symm
  have hDmax : max m n < D := by
    have h1 : 2 ^ r * 5 ^ s * max m n < 10 ^ e * n - m := by omega
    rw [hAD] at h1
    exact lt_of_mul_lt_mul_left h1 (Nat.zero_le _)
  have hD2 : ¬ 2 ∣ D := by
    rintro ⟨D', hD'⟩
    have h1 : 2 ^ (r + 1) * 5 ^ s ∣ 10 ^ e * n - m :=
      ⟨D', by rw [hAD, hD', pow_succ]; ring⟩
    have h2 : 2 ^ (r + 1) ∣ 10 ^ e * n := ((pow_dvd_pow 2 hre).trans
      ⟨5 ^ e, by rw [← mul_pow]; norm_num⟩).trans (dvd_mul_right _ _)
    have h3 : 2 ^ (r + 1) ∣ m := by
      have h4 : 10 ^ e * n - (10 ^ e * n - m) = m := Nat.sub_sub_self hmn
      exact h4 ▸ Nat.dvd_sub h2 ((dvd_mul_right _ _).trans h1)
    exact Nat.pow_succ_factorization_not_dvd hm0 Nat.prime_two h3
  have hD5 : ¬ 5 ∣ D := by
    rintro ⟨D', hD'⟩
    have h1 : 2 ^ r * 5 ^ (s + 1) ∣ 10 ^ e * n - m :=
      ⟨D', by rw [hAD, hD', pow_succ]; ring⟩
    have h2 : 5 ^ (s + 1) ∣ 10 ^ e * n := ((pow_dvd_pow 5 hse).trans
      ⟨2 ^ e, by rw [← mul_pow]; norm_num⟩).trans (dvd_mul_right _ _)
    have h3 : 5 ^ (s + 1) ∣ m := by
      have h4 : 10 ^ e * n - (10 ^ e * n - m) = m := Nat.sub_sub_self hmn
      exact h4 ▸ Nat.dvd_sub h2 ((dvd_mul_left _ _).trans h1)
    exact Nat.pow_succ_factorization_not_dvd hm0 (by norm_num) h3
  have hD10 : Nat.Coprime D 10 := by
    have h2 : Nat.Coprime D 2 := (Nat.prime_two.coprime_iff_not_dvd.mpr hD2).symm
    have h5 : Nat.Coprime D 5 := ((by norm_num : Nat.Prime 5).coprime_iff_not_dvd.mpr hD5).symm
    show Nat.Coprime D (2 * 5)
    exact h2.mul_right h5
  have hD0 : 0 < D := (lt_of_lt_of_le hm (Nat.le_max_left m n)).trans hDmax
  haveI : NeZero D := ⟨Nat.ne_of_gt hD0⟩
  -- The order of 10 modulo `D`.
  set u := ZMod.unitOfCoprime 10 hD10.symm with hu
  set t := orderOf u with ht
  have ht0 : 0 < t := orderOf_pos u
  have hut : (u : ZMod D) ^ t = 1 := by
    rw [ht, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
  have h10t : (10 : ZMod D) ^ t = 1 := by
    have hcoe : (u : ZMod D) = 10 := by rw [hu]; exact ZMod.coe_unitOfCoprime 10 hD10.symm
    rw [← hcoe]; exact hut
  have hmod : 10 ^ t ≡ 1 [MOD D] := by
    have h1 : ((10 ^ t : ℕ) : ZMod D) = ((1 : ℕ) : ZMod D) := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using h10t
    exact (ZMod.natCast_eq_natCast_iff (10 ^ t) 1 D).mp h1
  have hDdvd : D ∣ 10 ^ t - 1 :=
    (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp hmod.symm
  -- The multiplier `c`.
  set c := (10 ^ t - 1) / D with hc
  have hT : c * D = 10 ^ t - 1 := by rw [hc]; exact Nat.div_mul_cancel hDdvd
  have hc0 : 0 < c := by
    have h1 : 1 < 10 ^ t := Nat.one_lt_pow (Nat.pos_iff_ne_zero.mp ht0) (by norm_num)
    have hDT : D ≤ 10 ^ t - 1 := Nat.le_of_dvd (Nat.sub_pos_of_lt h1) hDdvd
    rw [hc]
    exact (Nat.le_div_iff_mul_le hD0).mpr (by simpa using hDT)
  refine ⟨c, hc0, fun d hd => ?_⟩
  rw [Finset.mem_Icc] at hd
  have hd0 : d ≠ 0 := by omega
  have hcmT : c * m < 10 ^ t - 1 := by
    have h1 : m < D := lt_of_le_of_lt (Nat.le_max_left m n) hDmax
    have h2 : c * m < c * D := mul_lt_mul_of_pos_left h1 hc0
    rwa [hT] at h2
  have hcnT : c * n < 10 ^ t - 1 := by
    have h1 : n < D := lt_of_le_of_lt (Nat.le_max_right m n) hDmax
    have h2 : c * n < c * D := mul_lt_mul_of_pos_left h1 hc0
    rwa [hT] at h2
  have hcm10 : c * m < 10 ^ t := lt_of_lt_of_le hcmT (Nat.sub_le _ _)
  have hcn10 : c * n < 10 ^ t := lt_of_lt_of_le hcnT (Nat.sub_le _ _)
  have hcong : 10 ^ e * (c * n) = c * m + (10 ^ t - 1) * (2 ^ r * 5 ^ s) := by
    have h1 : 10 ^ e * n = m + 2 ^ r * 5 ^ s * D := by
      have h2 : 10 ^ e * n - m + m = 10 ^ e * n := Nat.sub_add_cancel hmn
      rw [hAD] at h2
      rw [← h2]; ring
    calc 10 ^ e * (c * n) = c * (10 ^ e * n) := by ring
      _ = c * (m + 2 ^ r * 5 ^ s * D) := by rw [h1]
      _ = c * m + (2 ^ r * 5 ^ s) * (c * D) := by ring
      _ = c * m + (10 ^ t - 1) * (2 ^ r * 5 ^ s) := by rw [hT]; ring
  have hmod2 : (10 ^ e * (c * n)) % (10 ^ t - 1) = c * m := by
    rw [hcong, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hcmT]
  rw [count_digits_eq_digitCount _ t _ hd0 hcm10, ← hmod2,
    digitCount_pow_ten_mul_mod t ht0 (c * n) e d hcnT,
    ← count_digits_eq_digitCount _ t _ hd0 hcn10]

end Usa2013P5
