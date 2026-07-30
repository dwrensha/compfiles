/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Data.Int.Star
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.LinearCombination.Lemmas
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 2009, Problem 6

Let $s_1, s_2, s_3, \ldots$ be an infinite, nonconstant sequence of rational numbers, meaning it
is not the case that $s_1 = s_2 = s_3 = \ldots$. Suppose that $t_1, t_2, t_3, \ldots$ is also an
infinite, nonconstant sequence of rational numbers with the property that $(s_i - s_j)(t_i - t_j)$
is an integer for all $i$ and $j$. Prove that there exists a rational number $r$ such that
$(s_i - s_j) r$ and $(t_i - t_j)/r$ are integers for all $i$ and $j$.
-/

namespace Usa2009P6

snip begin

/-- The predicate that a rational number is an integer. -/
def IsInt (x : ℚ) : Prop := ∃ k : ℤ, x = k

lemma IsInt.of_int (k : ℤ) : IsInt (k : ℚ) := ⟨k, rfl⟩

lemma IsInt.add {x y : ℚ} (hx : IsInt x) (hy : IsInt y) : IsInt (x + y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  exact ⟨a + b, by rw [ha, hb, Int.cast_add]⟩

lemma IsInt.sub {x y : ℚ} (hx : IsInt x) (hy : IsInt y) : IsInt (x - y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  exact ⟨a - b, by rw [ha, hb, Int.cast_sub]⟩

/-- An integer has nonnegative `p`-adic valuation. -/
lemma IsInt.val_nonneg {x : ℚ} (hx : IsInt x) (p : ℕ) : 0 ≤ padicValRat p x := by
  obtain ⟨k, rfl⟩ := hx
  rw [padicValRat.of_int]
  exact Nat.cast_nonneg _

/-- A rational number whose `p`-adic valuation is nonnegative for every prime `p`
is an integer. -/
lemma isInt_of_val_nonneg {q : ℚ} (h : ∀ p : ℕ, p.Prime → 0 ≤ padicValRat p q) : IsInt q := by
  suffices hden : q.den = 1 by
    exact ⟨q.num, ((Rat.den_eq_one_iff q).mp hden).symm⟩
  by_contra hden
  obtain ⟨p, hpp, hpd⟩ := Nat.exists_prime_and_dvd hden
  have hnum : padicValInt p q.num = 0 := by
    rw [padicValInt.eq_zero_iff]
    refine Or.inr (Or.inr ?_)
    intro hdiv
    have hp1 : p ∣ q.num.natAbs := Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hdiv)
    have hcop : Nat.gcd q.num.natAbs q.den = 1 := Rat.reduced q
    have hp2 : p ∣ 1 := hcop ▸ Nat.dvd_gcd hp1 hpd
    exact hpp.ne_one (Nat.dvd_one.mp hp2)
  have hden_pos : 0 < padicValNat p q.den := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    rw [padicValNat.eq_zero_iff] at h0
    rcases h0 with h1 | h1 | h1
    · exact hpp.ne_one h1
    · exact Rat.den_nz q h1
    · exact h1 hpd
  have hval : padicValRat p q < 0 := by
    rw [padicValRat_def, hnum, Nat.cast_zero, zero_sub, neg_lt_zero]
    exact_mod_cast hden_pos
  exact absurd (h p hpp) (not_le_of_gt hval)

/-- Key integrality step: if `a * b` and `n * a + b` are integers (with `n` a nonzero
integer), then `b` (and hence `n * a`) is an integer. This is the `p`-adic heart of the
proof that every `tᵢ` is an integer. -/
lemma isInt_of_mul_add_int {n : ℤ} (hn : n ≠ 0) {a b : ℚ}
    (h1 : IsInt (a * b)) (h2 : IsInt ((n : ℚ) * a + b)) :
    IsInt b ∧ IsInt ((n : ℚ) * a) := by
  suffices hb : IsInt b by
    obtain ⟨kb, hkb⟩ := hb
    obtain ⟨k2, hk2⟩ := h2
    have hna : (n : ℚ) * a = (k2 : ℚ) - b := by rw [← hk2]; ring
    exact ⟨⟨kb, hkb⟩, ⟨k2 - kb, by rw [hna, hkb, Int.cast_sub]⟩⟩
  by_contra hb
  obtain ⟨p, hpp, hpv⟩ : ∃ p : ℕ, p.Prime ∧ padicValRat p b < 0 := by
    by_contra hcon
    push Not at hcon
    exact hb (isInt_of_val_nonneg hcon)
  haveI := Fact.mk hpp
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [padicValRat.zero] at hpv
    exact lt_irrefl 0 hpv
  obtain ⟨k2, hk2⟩ := h2
  have hna : (n : ℚ) * a = (k2 : ℚ) - b := by rw [← hk2]; ring
  have hval : padicValRat p ((n : ℚ) * a) = padicValRat p b := by
    rw [hna]
    rcases eq_or_ne k2 0 with hk | hk
    · rw [hk, Int.cast_zero, zero_sub, padicValRat.neg]
    · have hkv : (0 : ℤ) ≤ padicValRat p (k2 : ℚ) := IsInt.val_nonneg ⟨k2, rfl⟩ p
      have hlt : padicValRat p (-b) < padicValRat p (k2 : ℚ) := by
        rw [padicValRat.neg]
        exact lt_of_lt_of_le hpv hkv
      have hqr : -b + (k2 : ℚ) ≠ 0 := by
        intro h0
        have hbeq : b = (k2 : ℚ) := by linear_combination -h0
        exact hb ⟨k2, hbeq⟩
      have hrew : (k2 : ℚ) - b = -b + (k2 : ℚ) := by ring
      rw [hrew, padicValRat.add_eq_of_lt hqr (neg_ne_zero.mpr hb0) (by exact_mod_cast hk) hlt,
        padicValRat.neg]
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [mul_zero, padicValRat.zero] at hval
    rw [← hval] at hpv
    exact lt_irrefl 0 hpv
  have hva : padicValRat p a < 0 := by
    have hmul : padicValRat p ((n : ℚ) * a) = padicValRat p (n : ℚ) + padicValRat p a :=
      padicValRat.mul (by exact_mod_cast hn) ha0
    rw [hval, padicValRat.of_int] at hmul
    have hnn : (0 : ℤ) ≤ (padicValInt p n : ℤ) := Nat.cast_nonneg _
    linarith [hpv, hmul, hnn]
  obtain ⟨k1, hk1⟩ := h1
  have hkv1 : (0 : ℤ) ≤ padicValRat p (k1 : ℚ) := IsInt.val_nonneg ⟨k1, rfl⟩ p
  have hmul1 : padicValRat p (a * b) = padicValRat p a + padicValRat p b :=
    padicValRat.mul ha0 hb0
  rw [hk1] at hmul1
  linarith [hmul1, hva, hpv, hkv1]

/-- The gcd of `|T 0|, |T 1|, ..., |T k|`. -/
def seqGcd (T : ℕ → ℤ) (k : ℕ) : ℕ := (Finset.range (k + 1)).gcd fun i => (T i).natAbs

lemma seqGcd_dvd (T : ℕ → ℤ) {i k : ℕ} (hi : i ≤ k) : seqGcd T k ∣ (T i).natAbs :=
  Finset.gcd_dvd (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))

lemma seqGcd_ne_zero (T : ℕ → ℤ) {b k : ℕ} (hb : b ≤ k) (hT : T b ≠ 0) : seqGcd T k ≠ 0 := by
  intro h0
  exact hT (Int.natAbs_eq_zero.mp (Nat.eq_zero_of_zero_dvd (h0 ▸ seqGcd_dvd T hb)))

lemma seqGcd_succ_le (T : ℕ → ℤ) {b k : ℕ} (hb : b ≤ k) (hT : T b ≠ 0) :
    seqGcd T (k + 1) ≤ seqGcd T k := by
  apply Nat.le_of_dvd (Nat.pos_of_ne_zero (seqGcd_ne_zero T hb hT))
  apply Finset.dvd_gcd
  intro i hi
  exact seqGcd_dvd T (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) (Nat.le_succ k))

/-- Any sequence of integers containing a nonzero term has a greatest common divisor: a
positive natural `d` dividing every term, and such that for every prime `p` the `p`-adic
valuation of `d` is attained at some nonzero term of the sequence. -/
lemma gcd_seq (T : ℕ → ℤ) {b : ℕ} (hb : T b ≠ 0) :
    ∃ d : ℕ, d ≠ 0 ∧ (∀ i, (d : ℤ) ∣ T i) ∧
      ∀ p : ℕ, p.Prime → ∃ j, T j ≠ 0 ∧ padicValInt p (T j) = padicValNat p d := by
  classical
  -- The sequence `k ↦ seqGcd T (b + k)` is antitone, hence eventually constant.
  have hanti : Antitone (fun k => seqGcd T (b + k)) :=
    antitone_nat_of_succ_le fun k => seqGcd_succ_le T (Nat.le_add_right b k) hb
  have hne : (Set.range fun k => seqGcd T (b + k)).Nonempty := Set.range_nonempty _
  obtain ⟨n₀, hn₀⟩ := Nat.sInf_mem hne
  have hstable : ∀ m, n₀ ≤ m → seqGcd T (b + m) = seqGcd T (b + n₀) := by
    intro m hm
    refine le_antisymm (hanti hm) ?_
    calc seqGcd T (b + n₀)
      _ = sInf (Set.range fun k => seqGcd T (b + k)) := hn₀
      _ ≤ seqGcd T (b + m) := Nat.sInf_le ⟨m, rfl⟩
  refine ⟨seqGcd T (b + n₀), seqGcd_ne_zero T (Nat.le_add_right b n₀) hb, ?_, ?_⟩
  · -- `d` divides every term.
    intro i
    have h1 : seqGcd T (b + max n₀ i) = seqGcd T (b + n₀) := hstable _ (le_max_left _ _)
    have h2 : seqGcd T (b + max n₀ i) ∣ (T i).natAbs :=
      seqGcd_dvd T (le_trans (le_max_right n₀ i) (Nat.le_add_left _ b))
    exact Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr (h1 ▸ h2))
  · -- The valuation of `d` is attained at some nonzero term.
    intro p hpp
    haveI := Fact.mk hpp
    have hd0 : seqGcd T (b + n₀) ≠ 0 := seqGcd_ne_zero T (Nat.le_add_right b n₀) hb
    have hdvdN : ∀ i, seqGcd T (b + n₀) ∣ (T i).natAbs := fun i => by
      have h1 : seqGcd T (b + max n₀ i) = seqGcd T (b + n₀) := hstable _ (le_max_left _ _)
      have h2 : seqGcd T (b + max n₀ i) ∣ (T i).natAbs :=
        seqGcd_dvd T (le_trans (le_max_right n₀ i) (Nat.le_add_left _ b))
      exact h1 ▸ h2
    by_contra hcon
    push Not at hcon
    -- Every nonzero term has valuation `≥ padicValNat p d + 1`, so `p ^ (e + 1)` divides `d`.
    have hge : ∀ j, T j ≠ 0 →
        padicValNat p (seqGcd T (b + n₀)) + 1 ≤ padicValNat p (T j).natAbs := by
      intro j hTj
      obtain ⟨m, hm⟩ := hdvdN j
      have hm0 : m ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hm
        exact hTj (Int.natAbs_eq_zero.mp hm)
      have hle : padicValNat p (seqGcd T (b + n₀)) ≤ padicValNat p (T j).natAbs := by
        rw [hm, padicValNat.mul hd0 hm0]
        exact Nat.le_add_right _ _
      have hne' : padicValNat p (seqGcd T (b + n₀)) ≠ padicValNat p (T j).natAbs :=
        (hcon j hTj).symm
      exact Nat.succ_le_of_lt (lt_of_le_of_ne hle hne')
    have hfinal : p ^ (padicValNat p (seqGcd T (b + n₀)) + 1) ∣ seqGcd T (b + n₀) := by
      apply Finset.dvd_gcd
      intro i _
      by_cases hTi : T i = 0
      · simp [hTi]
      · exact (padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr hTi)).mpr (hge i hTi)
    have := (padicValNat_dvd_iff_le hd0).mp hfinal
    omega

/-- The key valuation bound: if `tⱼ` is a nonzero integer of `p`-adic valuation `e` (the
minimum among the `t`'s), then every `sᵢ` has `p`-adic valuation at least `-e`. -/
lemma s_val_ge {p : ℕ} (hp : p.Prime) {e : ℤ} (he : 0 ≤ e) {sj tj si ti : ℚ}
    (hstj : IsInt (sj * tj)) (hsti : IsInt (si * ti))
    (hcross : IsInt (si * tj + sj * ti)) (htj : tj ≠ 0) (htjv : padicValRat p tj = e) :
    -e ≤ padicValRat p si := by
  haveI := Fact.mk hp
  rcases eq_or_ne si 0 with hsi | hsi
  · simp only [hsi, padicValRat.zero]
    exact neg_nonpos.mpr he
  by_contra hcon
  push Not at hcon
  have hsj : -e ≤ padicValRat p sj := by
    rcases eq_or_ne sj 0 with hsj0 | hsj0
    · simp only [hsj0, padicValRat.zero]
      exact neg_nonpos.mpr he
    obtain ⟨kj, hkj⟩ := hstj
    have h1 : (0 : ℤ) ≤ padicValRat p (kj : ℚ) := IsInt.val_nonneg ⟨kj, rfl⟩ p
    have h2 : padicValRat p (sj * tj) = padicValRat p sj + padicValRat p tj :=
      padicValRat.mul hsj0 htj
    rw [hkj, htjv] at h2
    linarith [h1, h2]
  rcases eq_or_ne ti 0 with hti | hti
  · obtain ⟨kc, hkc⟩ := hcross
    rw [hti, mul_zero, add_zero] at hkc
    have h1 : (0 : ℤ) ≤ padicValRat p (kc : ℚ) := IsInt.val_nonneg ⟨kc, rfl⟩ p
    have h2 : padicValRat p (si * tj) = padicValRat p si + padicValRat p tj :=
      padicValRat.mul hsi htj
    rw [hkc, htjv] at h2
    linarith [h1, h2, hcon]
  · obtain ⟨ki, hki⟩ := hsti
    have h1 : (0 : ℤ) ≤ padicValRat p (ki : ℚ) := IsInt.val_nonneg ⟨ki, rfl⟩ p
    have h2 : padicValRat p (si * ti) = padicValRat p si + padicValRat p ti :=
      padicValRat.mul hsi hti
    rw [hki] at h2
    have hvti : e < padicValRat p ti := by linarith [h1, h2, hcon]
    obtain ⟨kc, hkc⟩ := hcross
    have hv1 : padicValRat p (si * tj) = padicValRat p si + e := by
      rw [padicValRat.mul hsi htj, htjv]
    rcases eq_or_ne sj 0 with hsj0 | hsj0
    · rw [hsj0, zero_mul, add_zero] at hkc
      have h3 : (0 : ℤ) ≤ padicValRat p (kc : ℚ) := IsInt.val_nonneg ⟨kc, rfl⟩ p
      rw [← hkc, hv1] at h3
      linarith [h3, hcon]
    · have hv2 : padicValRat p (sj * ti) = padicValRat p sj + padicValRat p ti :=
        padicValRat.mul hsj0 hti
      have hlt : padicValRat p (si * tj) < padicValRat p (sj * ti) := by
        rw [hv1, hv2]
        linarith [hcon, hsj, hvti]
      have hK0 : si * tj + sj * ti ≠ 0 := by
        intro hK
        have hneg : si * tj = -(sj * ti) := by linear_combination hK
        rw [hneg, padicValRat.neg] at hlt
        exact lt_irrefl _ hlt
      have hvK : padicValRat p (si * tj + sj * ti) = padicValRat p (si * tj) :=
        padicValRat.add_eq_of_lt hK0 (mul_ne_zero hsi htj) (mul_ne_zero hsj0 hti) hlt
      have h3 : (0 : ℤ) ≤ padicValRat p (kc : ℚ) := IsInt.val_nonneg ⟨kc, rfl⟩ p
      rw [← hkc, hvK, hv1] at h3
      linarith [h3, hcon]

/-- The heart of the problem, for normalized sequences: `s a = t a = 0`, `s b = 1` and
`t b = n` for a nonzero integer `n`. Then `r = d`, the gcd of all the `tᵢ` (which are
integers), works. -/
lemma normalized {s t : ℕ → ℚ} {a b : ℕ} {n : ℤ} (hn : n ≠ 0)
    (hsa : s a = 0) (hta : t a = 0) (hsb : s b = 1) (htb : t b = n)
    (h : ∀ i j, IsInt ((s i - s j) * (t i - t j))) :
    ∃ r : ℚ, r ≠ 0 ∧ (∀ i, IsInt (s i * r)) ∧ (∀ i, IsInt (t i / r)) := by
  -- `sᵢ tᵢ ∈ ℤ`, taking `j = a`.
  have st : ∀ i, IsInt (s i * t i) := by
    intro i
    obtain ⟨k, hk⟩ := h i a
    rw [hsa, hta, sub_zero, sub_zero] at hk
    exact ⟨k, hk⟩
  -- The cross terms `sᵢ tⱼ + sⱼ tᵢ` are integers.
  have cross : ∀ i j, IsInt (s i * t j + s j * t i) := by
    intro i j
    obtain ⟨ki, hki⟩ := st i
    obtain ⟨kj, hkj⟩ := st j
    obtain ⟨k, hk⟩ := h i j
    have h3 : s i * t j + s j * t i = (s i * t i) + (s j * t j) - (s i - s j) * (t i - t j) := by
      ring
    exact ⟨ki + kj - k, by rw [h3, hki, hkj, hk]; push_cast; ring⟩
  -- `n sᵢ + tᵢ ∈ ℤ`, taking `j = b`.
  have nst : ∀ i, IsInt ((n : ℚ) * s i + t i) := by
    intro i
    obtain ⟨ki, hki⟩ := st i
    obtain ⟨k, hk⟩ := h i b
    rw [hsb, htb] at hk
    have h3 : (n : ℚ) * s i + t i = (s i * t i) + (n : ℚ) - (s i - 1) * (t i - (n : ℚ)) := by ring
    exact ⟨ki + n - k, by rw [h3, hki, hk]; push_cast; ring⟩
  -- Every `tᵢ` is an integer.
  have ti_int : ∀ i, IsInt (t i) := fun i => (isInt_of_mul_add_int hn (st i) (nst i)).1
  choose T hT using ti_int
  have hTb : T b = n := by
    have h1 : (T b : ℚ) = (n : ℚ) := by rw [← hT b, htb]
    exact_mod_cast h1
  have hb0 : T b ≠ 0 := hTb ▸ hn
  -- Let `d` be the gcd of all the `tᵢ`; then `r = d` works.
  obtain ⟨d, hd0, hdvd, hmin⟩ := gcd_seq T hb0
  have hd0' : (d : ℚ) ≠ 0 := by exact_mod_cast hd0
  refine ⟨(d : ℚ), hd0', ?_, ?_⟩
  · intro i
    rcases eq_or_ne (s i) 0 with hsi | hsi
    · exact ⟨0, by simp [hsi]⟩
    apply isInt_of_val_nonneg
    intro p hpp
    haveI := Fact.mk hpp
    obtain ⟨j, hTj0, hTjv⟩ := hmin p hpp
    have htj : t j ≠ 0 := by rw [hT j]; exact_mod_cast hTj0
    have htjv : padicValRat p (t j) = (padicValNat p d : ℤ) := by
      rw [hT j, padicValRat.of_int, hTjv]
    have hbound := s_val_ge hpp (Nat.cast_nonneg _) (st j) (st i) (cross i j) htj htjv
    rw [padicValRat.mul hsi hd0', padicValRat.of_nat]
    linarith [hbound]
  · intro i
    obtain ⟨m, hm⟩ := hdvd i
    exact ⟨m, by rw [hT i, div_eq_iff hd0', hm]; push_cast; ring⟩

snip end

problem usa2009_p6 (s t : ℕ → ℚ) (hs : ¬ ∀ i j, s i = s j) (ht : ¬ ∀ i j, t i = t j)
    (h : ∀ i j, ∃ k : ℤ, (s i - s j) * (t i - t j) = k) :
    ∃ r : ℚ, r ≠ 0 ∧ (∀ i j, ∃ k : ℤ, (s i - s j) * r = k) ∧
      ∀ i j, ∃ k : ℤ, (t i - t j) / r = k := by
  -- Some pair of indices has a nonzero product of differences.
  obtain ⟨a, b, hab⟩ : ∃ a b, (s a - s b) * (t a - t b) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    push Not at hs
    push Not at ht
    obtain ⟨i₀, i₁, h01⟩ := hs
    have ht01 : t i₀ = t i₁ := by
      rcases mul_eq_zero.mp (hcon i₀ i₁) with h' | h'
      · exact absurd (sub_eq_zero.mp h') h01
      · exact sub_eq_zero.mp h'
    obtain ⟨j₀, j₁, hj⟩ := ht
    have hj0 : t j₀ ≠ t i₀ ∨ t j₁ ≠ t i₀ := by
      by_contra h2
      push Not at h2
      exact hj (h2.1.trans h2.2.symm)
    rcases hj0 with hj0 | hj0
    · have hs1 : s j₀ = s i₀ := by
        rcases mul_eq_zero.mp (hcon j₀ i₀) with h' | h'
        · exact sub_eq_zero.mp h'
        · exact absurd (sub_eq_zero.mp h') hj0
      have hs2 : s j₀ = s i₁ := by
        rcases mul_eq_zero.mp (hcon j₀ i₁) with h' | h'
        · exact sub_eq_zero.mp h'
        · exact absurd (sub_eq_zero.mp h') (ht01 ▸ hj0)
      exact h01 (hs1 ▸ hs2)
    · have hs1 : s j₁ = s i₀ := by
        rcases mul_eq_zero.mp (hcon j₁ i₀) with h' | h'
        · exact sub_eq_zero.mp h'
        · exact absurd (sub_eq_zero.mp h') hj0
      have hs2 : s j₁ = s i₁ := by
        rcases mul_eq_zero.mp (hcon j₁ i₁) with h' | h'
        · exact sub_eq_zero.mp h'
        · exact absurd (sub_eq_zero.mp h') (ht01 ▸ hj0)
      exact h01 (hs1 ▸ hs2)
  -- Shift and scale to normalize: `s' a = t' a = 0`, `s' b = 1`, `t' b = N`.
  have hsb_ne : s b ≠ s a := fun h0 => hab (by rw [h0, sub_self, zero_mul])
  have htb_ne : t b ≠ t a := fun h0 => hab (by rw [h0, sub_self, mul_zero])
  obtain ⟨N, hN⟩ := h b a
  have hN0 : N ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero] at hN
    rcases mul_eq_zero.mp hN with h' | h'
    · exact hsb_ne (sub_eq_zero.mp h')
    · exact htb_ne (sub_eq_zero.mp h')
  set w := s b - s a with hwdef
  have hw : w ≠ 0 := sub_ne_zero.mpr hsb_ne
  set s' : ℕ → ℚ := fun i => (s i - s a) / w with hs'def
  set t' : ℕ → ℚ := fun i => (t i - t a) * w with ht'def
  have hs'a : s' a = 0 := by simp [hs'def]
  have ht'a : t' a = 0 := by simp [ht'def]
  have hs'b : s' b = 1 := by
    simp only [hs'def]
    rw [← hwdef, div_self hw]
  have ht'b : t' b = (N : ℚ) := by
    simp only [ht'def]
    rw [mul_comm]
    exact hN
  have h' : ∀ i j, IsInt ((s' i - s' j) * (t' i - t' j)) := by
    intro i j
    obtain ⟨k, hk⟩ := h i j
    refine ⟨k, ?_⟩
    rw [← hk]
    simp only [hs'def, ht'def]
    field_simp
    ring
  obtain ⟨r', hr'0, h1', h2'⟩ := normalized hN0 hs'a ht'a hs'b ht'b h'
  refine ⟨r' / w, div_ne_zero hr'0 hw, fun i j => ?_, fun i j => ?_⟩
  · obtain ⟨k1, hk1⟩ := h1' i
    obtain ⟨k2, hk2⟩ := h1' j
    have e1 : (s i - s j) * (r' / w) = (s' i - s' j) * r' := by
      simp only [hs'def]
      field_simp
      ring
    exact ⟨k1 - k2, by rw [e1, sub_mul, hk1, hk2, Int.cast_sub]⟩
  · obtain ⟨k1, hk1⟩ := h2' i
    obtain ⟨k2, hk2⟩ := h2' j
    have e2 : (t i - t j) / (r' / w) = (t' i - t' j) / r' := by
      simp only [ht'def]
      field_simp
      ring
    exact ⟨k1 - k2, by rw [e2, sub_div, hk1, hk2, Int.cast_sub]⟩

end Usa2009P6
