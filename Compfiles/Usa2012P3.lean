/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Data.Int.Star
public import Mathlib.NumberTheory.Bertrand
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 2012, Problem 3

Determine which integers n > 1 have the property that there exists an infinite
sequence a₁, a₂, a₃, ... of nonzero integers such that the equality

  aₖ + 2a₂ₖ + ⋯ + naₙₖ = 0

holds for every positive integer k.
-/

namespace Usa2012P3

snip begin

/-- A completely multiplicative sequence built from values assigned on a
finite set of primes: `mulSeq P c j = ∏ r ∈ P, c r ^ (Nat.factorization j r)`. -/
def mulSeq (P : Finset ℕ) (c : ℕ → ℤ) (j : ℕ) : ℤ :=
  ∏ r ∈ P, c r ^ (Nat.factorization j r)

lemma mulSeq_mul (P : Finset ℕ) (c : ℕ → ℤ) {u v : ℕ} (hu : u ≠ 0) (hv : v ≠ 0) :
    mulSeq P c (u * v) = mulSeq P c u * mulSeq P c v := by
  simp only [mulSeq, Nat.factorization_mul hu hv, Finsupp.add_apply, pow_add,
    Finset.prod_mul_distrib]

lemma mulSeq_ne_zero (P : Finset ℕ) (c : ℕ → ℤ) (hc : ∀ r ∈ P, c r ≠ 0) (j : ℕ) :
    mulSeq P c j ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun r hr => pow_ne_zero _ (hc r hr)

/-- If the sum `∑ j ∈ [1, n], j * a j` vanishes for a completely multiplicative
sequence `a`, then `a` satisfies all the required identities. -/
lemma condition_of_sum_eq_zero {n : ℕ} {P : Finset ℕ} {c : ℕ → ℤ}
    (h : ∑ j ∈ Finset.Icc 1 n, (j : ℤ) * mulSeq P c j = 0) (k : ℕ) (hk : 1 ≤ k) :
    ∑ j ∈ Finset.Icc 1 n, (j : ℤ) * mulSeq P c (j * k) = 0 := by
  have hk0 : k ≠ 0 := by omega
  calc ∑ j ∈ Finset.Icc 1 n, (j : ℤ) * mulSeq P c (j * k)
      = ∑ j ∈ Finset.Icc 1 n, mulSeq P c k * ((j : ℤ) * mulSeq P c j) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hj0 : j ≠ 0 := by
          have h1 := (Finset.mem_Icc.mp hj).1
          omega
        rw [mulSeq_mul P c hj0 hk0]; ring
    _ = mulSeq P c k * ∑ j ∈ Finset.Icc 1 n, (j : ℤ) * mulSeq P c j := by
        rw [Finset.mul_sum]
    _ = 0 := by rw [h, mul_zero]

/-- Bézout's identity, arranged so that both coefficients are nonzero. -/
lemma bezout_nonzero {A B c : ℤ} (hA : 0 < A) (hB : 0 < B) (h : IsCoprime A B) :
    ∃ x y : ℤ, x ≠ 0 ∧ y ≠ 0 ∧ A * x + B * y = c := by
  obtain ⟨u, v, huv⟩ := h
  have huc2 : -((u * c).natAbs : ℤ) ≤ u * c := by
    have h1 := Int.le_natAbs (a := -(u * c))
    rw [Int.natAbs_neg] at h1
    omega
  have hvc1 : v * c ≤ ((v * c).natAbs : ℤ) := Int.le_natAbs
  set t : ℤ := ((u * c).natAbs : ℤ) + ((v * c).natAbs : ℤ) + 1 with ht
  have ht0 : 0 < t := by omega
  have hBt : ((u * c).natAbs : ℤ) < B * t := by
    have h1 : t ≤ B * t := by
      have h2 : (1 : ℤ) * t ≤ B * t :=
        mul_le_mul_of_nonneg_right (by omega) (le_of_lt ht0)
      rwa [one_mul] at h2
    omega
  have hAt : ((v * c).natAbs : ℤ) < A * t := by
    have h1 : t ≤ A * t := by
      have h2 : (1 : ℤ) * t ≤ A * t :=
        mul_le_mul_of_nonneg_right (by omega) (le_of_lt ht0)
      rwa [one_mul] at h2
    omega
  refine ⟨u * c + B * t, v * c - A * t, by omega, by omega, ?_⟩
  have e : A * (u * c + B * t) + B * (v * c - A * t) = c * (u * A + v * B) := by ring
  rw [e, huv, mul_one]

/-- The case `n = 2` is impossible: the relation `a k + 2 * a (2 * k) = 0`
forces `2 ^ j ∣ a 1` for every `j`, so `a 1 = 0`. -/
lemma not_property_two {a : ℕ → ℤ} (ha : ∀ i, 1 ≤ i → a i ≠ 0)
    (h : ∀ k, 1 ≤ k → a k + 2 * a (2 * k) = 0) : False := by
  have key : ∀ j : ℕ, a 1 = (-2 : ℤ) ^ j * a (2 ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have h2j : 1 ≤ 2 ^ j := Nat.one_le_two_pow
      have hk := h (2 ^ j) h2j
      have e : (2 : ℕ) * 2 ^ j = 2 ^ (j + 1) := by ring
      rw [e] at hk
      have hstep : a (2 ^ j) = -2 * a (2 ^ (j + 1)) := by linarith [hk]
      rw [ih, hstep]; ring
  have hdvd : ∀ j : ℕ, (2 : ℤ) ^ j ∣ a 1 := by
    intro j
    refine ⟨(-1 : ℤ) ^ j * a (2 ^ j), ?_⟩
    have h2j : (-2 : ℤ) ^ j = (-1 : ℤ) ^ j * 2 ^ j := by
      rw [← mul_pow]; norm_num
    rw [key j, h2j]; ring
  have hdvdn : ∀ j : ℕ, (2 : ℕ) ^ j ∣ (a 1).natAbs := by
    intro j
    have h2 : ((2 : ℤ) ^ j).natAbs = 2 ^ j := by
      rw [Int.natAbs_pow]; simp
    rw [← h2]
    exact Int.natAbs_dvd_natAbs.mpr (hdvd j)
  have hpos : 0 < (a 1).natAbs := by
    rw [Nat.pos_iff_ne_zero, ne_eq, Int.natAbs_eq_zero]
    exact ha 1 le_rfl
  have hj : (a 1).natAbs < 2 ^ (a 1).natAbs := Nat.lt_two_pow_self
  have hle := Nat.le_of_dvd hpos (hdvdn (a 1).natAbs)
  omega

/-- The coefficient function assigning `x` to `p`, `y` to `q`, and `1` to
everything else. -/
def cfun (p q : ℕ) (x y : ℤ) (r : ℕ) : ℤ := if r = p then x else if r = q then y else 1

lemma mulSeq_cfun_apply {p q : ℕ} {x y : ℤ} (hpq : p ≠ q) (j : ℕ) :
    mulSeq {p, q} (cfun p q x y) j
      = x ^ (Nat.factorization j p) * y ^ (Nat.factorization j q) := by
  have hmem : p ∉ ({q} : Finset ℕ) := by
    simp only [Finset.mem_singleton]
    exact hpq
  rw [mulSeq, Finset.prod_insert hmem, Finset.prod_singleton]
  simp [cfun, hpq.symm]

lemma mulSeq_cfun_p {p q : ℕ} {x y : ℤ} (hp : p.Prime) (hplt : p < q) :
    mulSeq {p, q} (cfun p q x y) p = x := by
  have hpq : p ≠ q := ne_of_lt hplt
  rw [mulSeq_cfun_apply hpq, hp.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt hp.pos hplt)]
  simp

lemma mulSeq_cfun_2p {p q : ℕ} {x y : ℤ} (hp : p.Prime) (hq : q.Prime) (hp5 : 5 ≤ p)
    (hq7 : 7 ≤ q) (hplt : p < q) :
    mulSeq {p, q} (cfun p q x y) (2 * p) = x := by
  have hpq : p ≠ q := ne_of_lt hplt
  have hfac1 : Nat.factorization (2 * p) p = 1 := by
    rw [Nat.factorization_mul (by norm_num) hp.ne_zero, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd
        (Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)),
      hp.factorization_self]
  have hfac2 : Nat.factorization (2 * p) q = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro h
    rcases hq.dvd_mul.mp h with h2 | hp'
    · exact Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega) h2
    · exact Nat.not_dvd_of_pos_of_lt hp.pos hplt hp'
  rw [mulSeq_cfun_apply hpq, hfac1, hfac2]
  simp

lemma mulSeq_cfun_3p {p q : ℕ} {x y : ℤ} (hp : p.Prime) (hq : q.Prime) (hp5 : 5 ≤ p)
    (hq7 : 7 ≤ q) (hplt : p < q) :
    mulSeq {p, q} (cfun p q x y) (3 * p) = x := by
  have hpq : p ≠ q := ne_of_lt hplt
  have hfac1 : Nat.factorization (3 * p) p = 1 := by
    rw [Nat.factorization_mul (by norm_num) hp.ne_zero, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd
        (Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)),
      hp.factorization_self]
  have hfac2 : Nat.factorization (3 * p) q = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro h
    rcases hq.dvd_mul.mp h with h3 | hp'
    · exact Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega) h3
    · exact Nat.not_dvd_of_pos_of_lt hp.pos hplt hp'
  rw [mulSeq_cfun_apply hpq, hfac1, hfac2]
  simp

lemma mulSeq_cfun_q {p q : ℕ} {x y : ℤ} (hp : p.Prime) (hq : q.Prime) (hplt : p < q) :
    mulSeq {p, q} (cfun p q x y) q = y := by
  have hpq : p ≠ q := ne_of_lt hplt
  have hfac : Nat.factorization q p = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro h
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)
  rw [mulSeq_cfun_apply hpq, hfac, hq.factorization_self]
  simp

/-- Terms `j * (a j - 1)` vanish when `j ∈ [1, n]` is none of `p, 2p, 3p, q`:
such a `j` is divisible by neither `p` nor `q`, so `a j = 1`. -/
lemma term_eq_zero {n p q j : ℕ} {x y : ℤ} (hplt : p < q)
    (h2q : n < 2 * q) (h4p : n < 4 * p) (hj1 : 1 ≤ j) (hjn : j ≤ n)
    (h1 : j ≠ p) (h2 : j ≠ 2 * p) (h3 : j ≠ 3 * p) (h4 : j ≠ q) :
    (j : ℤ) * (mulSeq {p, q} (cfun p q x y) j - 1) = 0 := by
  have hpq : p ≠ q := ne_of_lt hplt
  have h4p' : n < p * 4 := by omega
  have h2q' : n < q * 2 := by omega
  have hpdvd : ¬ p ∣ j := by
    rintro ⟨e, rfl⟩
    have he1 : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with he | he
      · subst he; simp at hj1
      · exact he
    have he4 : e < 4 := Nat.lt_of_mul_lt_mul_left (lt_of_le_of_lt hjn h4p')
    interval_cases e
    · exact h1 (by ring)
    · exact h2 (by ring)
    · exact h3 (by ring)
  have hqdvd : ¬ q ∣ j := by
    rintro ⟨e, rfl⟩
    have he1 : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with he | he
      · subst he; simp at hj1
      · exact he
    have he2 : e < 2 := Nat.lt_of_mul_lt_mul_left (lt_of_le_of_lt hjn h2q')
    interval_cases e
    · exact h4 (by ring)
  rw [mulSeq_cfun_apply hpq, Nat.factorization_eq_zero_of_not_dvd hpdvd,
    Nat.factorization_eq_zero_of_not_dvd hqdvd]
  simp

/-- The correction terms in `∑ j ∈ [1,n], j * (a j - 1)`: the only nonzero
contributions come from `j ∈ {p, 2p, 3p, q} ∩ [1, n]`. -/
lemma sum_mulSeq_cfun_sub_one {n p q : ℕ} {x y : ℤ} (hp : p.Prime) (hq : q.Prime)
    (hp5 : 5 ≤ p) (hq7 : 7 ≤ q) (hplt : p < q)
    (h2q : n < 2 * q) (h4p : n < 4 * p) (hpn : p ≤ n) (hqn : q ≤ n) :
    ∑ j ∈ Finset.Icc 1 n, (j : ℤ) * (mulSeq {p, q} (cfun p q x y) j - 1)
      = (p : ℤ) * (x - 1)
        + (if 2 * p ≤ n then ((2 * p : ℕ) : ℤ) * (x - 1) else 0)
        + (if 3 * p ≤ n then ((3 * p : ℕ) : ℤ) * (x - 1) else 0)
        + (q : ℤ) * (y - 1) := by
  have hpq : p ≠ q := ne_of_lt hplt
  have h2p_ne : 2 * p ≠ q := by
    have hqodd : q % 2 = 1 := by
      rcases hq.eq_two_or_odd with h | h
      · omega
      · exact h
    omega
  have h3p_ne : 3 * p ≠ q := by
    intro h
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp ⟨3, by rw [mul_comm]; exact h.symm⟩)
  by_cases h2 : 2 * p ≤ n
  · by_cases h3 : 3 * p ≤ n
    · -- case `3 * p ≤ n`: multiples of `p` in `[1, n]` are `p, 2p, 3p`
      rw [if_pos h2, if_pos h3]
      have hss : ({p, 2 * p, 3 * p, q} : Finset ℕ) ⊆ Finset.Icc 1 n := by
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rw [Finset.mem_Icc]
        rcases hj with rfl | rfl | rfl | rfl
        · exact ⟨by omega, hpn⟩
        · exact ⟨by omega, h2⟩
        · exact ⟨by omega, h3⟩
        · exact ⟨by omega, hqn⟩
      have hvan : ∀ j ∈ Finset.Icc 1 n, j ∉ ({p, 2 * p, 3 * p, q} : Finset ℕ) →
          (j : ℤ) * (mulSeq {p, q} (cfun p q x y) j - 1) = 0 := by
        intro j hj hjs
        simp only [Finset.mem_insert, Finset.mem_singleton] at hjs
        rw [Finset.mem_Icc] at hj
        push Not at hjs
        exact term_eq_zero hplt h2q h4p hj.1 hj.2 hjs.1 hjs.2.1 hjs.2.2.1 hjs.2.2.2
      have hsub := (Finset.sum_subset hss hvan).symm
      rw [hsub, Finset.sum_insert (by simp; omega),
        Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp; omega),
        Finset.sum_singleton, mulSeq_cfun_p hp hplt, mulSeq_cfun_2p hp hq hp5 hq7 hplt,
        mulSeq_cfun_3p hp hq hp5 hq7 hplt, mulSeq_cfun_q hp hq hplt]
      ring
    · -- case `2 * p ≤ n < 3 * p`: multiples of `p` in `[1, n]` are `p, 2p`
      rw [if_pos h2, if_neg h3]
      have hss : ({p, 2 * p, q} : Finset ℕ) ⊆ Finset.Icc 1 n := by
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rw [Finset.mem_Icc]
        rcases hj with rfl | rfl | rfl
        · exact ⟨by omega, hpn⟩
        · exact ⟨by omega, h2⟩
        · exact ⟨by omega, hqn⟩
      have hvan : ∀ j ∈ Finset.Icc 1 n, j ∉ ({p, 2 * p, q} : Finset ℕ) →
          (j : ℤ) * (mulSeq {p, q} (cfun p q x y) j - 1) = 0 := by
        intro j hj hjs
        simp only [Finset.mem_insert, Finset.mem_singleton] at hjs
        rw [Finset.mem_Icc] at hj
        push Not at hjs
        exact term_eq_zero hplt h2q h4p hj.1 hj.2 hjs.1 hjs.2.1 (by omega) hjs.2.2
      have hsub := (Finset.sum_subset hss hvan).symm
      rw [hsub, Finset.sum_insert (by simp; omega),
        Finset.sum_insert (by simp; omega), Finset.sum_singleton,
        mulSeq_cfun_p hp hplt, mulSeq_cfun_2p hp hq hp5 hq7 hplt,
        mulSeq_cfun_q hp hq hplt]
      ring
  · by_cases h3 : 3 * p ≤ n
    · omega
    · -- case `n < 2 * p`: the only multiple of `p` in `[1, n]` is `p`
      rw [if_neg h2, if_neg h3]
      have hss : ({p, q} : Finset ℕ) ⊆ Finset.Icc 1 n := by
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rw [Finset.mem_Icc]
        rcases hj with rfl | rfl
        · exact ⟨by omega, hpn⟩
        · exact ⟨by omega, hqn⟩
      have hvan : ∀ j ∈ Finset.Icc 1 n, j ∉ ({p, q} : Finset ℕ) →
          (j : ℤ) * (mulSeq {p, q} (cfun p q x y) j - 1) = 0 := by
        intro j hj hjs
        simp only [Finset.mem_insert, Finset.mem_singleton] at hjs
        rw [Finset.mem_Icc] at hj
        push Not at hjs
        exact term_eq_zero hplt h2q h4p hj.1 hj.2 hjs.1 (by omega) (by omega) hjs.2
      have hsub := (Finset.sum_subset hss hvan).symm
      rw [hsub, Finset.sum_insert (by simp; omega), Finset.sum_singleton,
        mulSeq_cfun_p hp hplt, mulSeq_cfun_q hp hq hplt]
      ring

/-- Construction for `9 ≤ n`: pick primes `p`, `q` via Bertrand's postulate with
`⌈n/2⌉ < q ≤ 2⌈n/2⌉` and `(q-1)/2 < p ≤ q-1`, take `a r = 1` for primes `r ∉ {p, q}`,
and choose nonzero `a p`, `a q` by Bézout so that `∑ j ∈ [1,n], j * a j = 0`. -/
lemma exists_good_seq_of_nine_le {n : ℕ} (hn : 9 ≤ n) :
    ∃ a : ℕ → ℤ, (∀ i, 1 ≤ i → a i ≠ 0) ∧
      ∀ k, 1 ≤ k → ∑ j ∈ Finset.Icc 1 n, (j : ℤ) * a (j * k) = 0 := by
  obtain ⟨q, hq, hm_lt, hq_le⟩ :=
    Nat.exists_prime_lt_and_le_two_mul ((n + 1) / 2) (by omega)
  have hq6 : 6 ≤ q := by omega
  have hq7 : 7 ≤ q := by
    rcases lt_or_ge q 7 with h | h
    · interval_cases q
      · norm_num at hq
    · exact h
  have hqodd : q % 2 = 1 := by
    rcases hq.eq_two_or_odd with h | h
    · omega
    · exact h
  have h2q : n < 2 * q := by omega
  have hq_le_n : q ≤ n := by
    by_contra hlt
    push Not at hlt
    have hqn1 : q = n + 1 := by omega
    subst hqn1
    omega
  obtain ⟨p, hp, hp_gt, hp_le⟩ :=
    Nat.exists_prime_lt_and_le_two_mul ((q - 1) / 2) (by omega)
  have hp4 : 4 ≤ p := by omega
  have hp5 : 5 ≤ p := by
    rcases lt_or_ge p 5 with h | h
    · interval_cases p
      · norm_num at hp
    · exact h
  have hplt : p < q := by omega
  have h2p_ge : q ≤ 2 * p := by omega
  have h4p : n < 4 * p := by omega
  have hpn : p ≤ n := by omega
  set S : ℤ := ∑ j ∈ Finset.Icc 1 n, (j : ℤ) with hS
  have build : ∀ m : ℕ, 0 < m → Nat.Coprime m q →
      (m : ℤ) = (p : ℤ) + (if 2 * p ≤ n then ((2 * p : ℕ) : ℤ) else 0)
        + (if 3 * p ≤ n then ((3 * p : ℕ) : ℤ) else 0) →
      ∃ a : ℕ → ℤ, (∀ i, 1 ≤ i → a i ≠ 0) ∧
        ∀ k, 1 ≤ k → ∑ j ∈ Finset.Icc 1 n, (j : ℤ) * a (j * k) = 0 := by
    intro m hm0 hcop_nat hm_eq
    have hcop : IsCoprime (m : ℤ) (q : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
      exact hcop_nat
    obtain ⟨x, y, hx, hy, hbez⟩ := bezout_nonzero (A := (m : ℤ)) (B := (q : ℤ))
      (c := (m : ℤ) + q - S) (Nat.cast_pos.mpr hm0) (Nat.cast_pos.mpr hq.pos) hcop
    refine ⟨mulSeq {p, q} (cfun p q x y), ?_, ?_⟩
    · intro i _
      apply mulSeq_ne_zero
      intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with hrp | hrq
      · rw [hrp]
        show (if p = p then x else if p = q then y else 1) ≠ 0
        rw [if_pos rfl]
        exact hx
      · rw [hrq]
        show (if q = p then x else if q = q then y else 1) ≠ 0
        rw [if_neg (ne_of_lt hplt).symm, if_pos rfl]
        exact hy
    · intro k hk
      apply condition_of_sum_eq_zero _ k hk
      have hsplit : ∑ j ∈ Finset.Icc 1 n, (j : ℤ) * mulSeq {p, q} (cfun p q x y) j
          = S + ∑ j ∈ Finset.Icc 1 n,
              (j : ℤ) * (mulSeq {p, q} (cfun p q x y) j - 1) := by
        rw [hS, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [hsplit, sum_mulSeq_cfun_sub_one hp hq hp5 hq7 hplt h2q h4p hpn hq_le_n]
      by_cases h3 : 3 * p ≤ n
      · have h2 : 2 * p ≤ n := by omega
        simp only [if_pos h2, if_pos h3] at hm_eq hbez ⊢
        rw [hm_eq] at hbez
        linear_combination hbez
      · by_cases h2 : 2 * p ≤ n
        · simp only [if_neg h3, if_pos h2] at hm_eq hbez ⊢
          rw [hm_eq] at hbez
          linear_combination hbez
        · simp only [if_neg h3, if_neg h2] at hm_eq hbez ⊢
          rw [hm_eq] at hbez
          linear_combination hbez
  rcases lt_or_ge n (3 * p) with h3 | h3
  · rcases lt_or_ge n (2 * p) with h2 | h2
    · -- here the only multiple of `p` in `[1, n]` is `p`, and `p` is coprime to `q`
      have hcop : Nat.Coprime p q := by
        apply Nat.Coprime.symm
        rw [hq.coprime_iff_not_dvd]
        exact Nat.not_dvd_of_pos_of_lt hp.pos hplt
      exact build p (by omega) hcop (by
        rw [if_neg (by omega : ¬ 2 * p ≤ n), if_neg (by omega : ¬ 3 * p ≤ n)]
        ring)
    · -- here the multiples of `p` in `[1, n]` are `p, 2p`, and `3 * p` is coprime to `q`
      have hcop : Nat.Coprime (3 * p) q := by
        apply Nat.Coprime.symm
        rw [hq.coprime_iff_not_dvd]
        intro h
        rcases hq.dvd_mul.mp h with h3' | hp'
        · exact Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega) h3'
        · exact Nat.not_dvd_of_pos_of_lt hp.pos hplt hp'
      exact build (3 * p) (by omega) hcop (by
        rw [if_pos h2, if_neg (by omega : ¬ 3 * p ≤ n)]
        push_cast
        ring)
  · -- here the multiples of `p` in `[1, n]` are `p, 2p, 3p`, and `6 * p` is coprime to `q`
    have hcop : Nat.Coprime (6 * p) q := by
      apply Nat.Coprime.symm
      rw [hq.coprime_iff_not_dvd]
      intro h
      rcases hq.dvd_mul.mp h with h6 | hp'
      · exact Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega) h6
      · exact Nat.not_dvd_of_pos_of_lt hp.pos hplt hp'
    exact build (6 * p) (by omega) hcop (by
      have h2 : 2 * p ≤ n := by omega
      rw [if_pos h2, if_pos h3]
      push_cast
      ring)

/-- The small cases `3 ≤ n ≤ 8`, each given by an explicit completely
multiplicative sequence. -/
lemma small_case (n : ℕ) (P : Finset ℕ) (c : ℕ → ℤ) (hc : ∀ r ∈ P, c r ≠ 0)
    (hsum : ∑ j ∈ Finset.Icc 1 n, (j : ℤ) * mulSeq P c j = 0) :
    ∃ a : ℕ → ℤ, (∀ i, 1 ≤ i → a i ≠ 0) ∧
      ∀ k, 1 ≤ k → ∑ j ∈ Finset.Icc 1 n, (j : ℤ) * a (j * k) = 0 :=
  ⟨mulSeq P c, fun i _ => mulSeq_ne_zero P c hc i,
   fun k hk => condition_of_sum_eq_zero hsum k hk⟩

snip end

determine SolutionSet : Set ℕ := { n | 2 < n }

problem usa2012_p3 (n : ℕ) (hn : 1 < n) :
    n ∈ SolutionSet ↔ ∃ a : ℕ → ℤ, (∀ i, 1 ≤ i → a i ≠ 0) ∧
      ∀ k, 1 ≤ k → ∑ j ∈ Finset.Icc 1 n, (j : ℤ) * a (j * k) = 0 := by
  show (2 < n) ↔ _
  constructor
  · intro h2n
    rcases lt_or_ge n 9 with h9 | h9
    · interval_cases n
      · exact small_case 3 {3} (fun _ => -1) (by decide) (by
          have m1 : mulSeq {3} (fun _ => -1) 1 = 1 := by simp [mulSeq]
          have m2 : mulSeq {3} (fun _ => -1) 2 = 1 := by
            simp [mulSeq, Nat.factorization_eq_zero_of_not_dvd (show ¬ (3 : ℕ) ∣ 2 by decide)]
          have m3 : mulSeq {3} (fun _ => -1) 3 = -1 := by
            simp [mulSeq, Nat.prime_three.factorization_self]
          rw [show Finset.Icc (1 : ℕ) 3 = ({1, 2, 3} : Finset ℕ) by decide,
            Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
            m1, m2, m3]
          norm_num)
      · exact small_case 4 {2, 3} (fun _ => -1) (by decide) (by
          have f42 : Nat.factorization 4 2 = 2 := by
            rw [show (4 : ℕ) = 2 * 2 from rfl,
              Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
              Nat.prime_two.factorization_self]
          have m1 : mulSeq {2, 3} (fun _ => -1) 1 = 1 := by simp [mulSeq]
          have m2 : mulSeq {2, 3} (fun _ => -1) 2 = -1 := by
            simp [mulSeq, Nat.prime_two.factorization_self,
              Nat.factorization_eq_zero_of_not_dvd (show ¬ (3 : ℕ) ∣ 2 by decide)]
          have m3 : mulSeq {2, 3} (fun _ => -1) 3 = -1 := by
            simp [mulSeq, Nat.prime_three.factorization_self,
              Nat.factorization_eq_zero_of_not_dvd (show ¬ (2 : ℕ) ∣ 3 by decide)]
          have m4 : mulSeq {2, 3} (fun _ => -1) 4 = 1 := by
            simp [mulSeq, f42,
              Nat.factorization_eq_zero_of_not_dvd (show ¬ (3 : ℕ) ∣ 4 by decide)]
          rw [show Finset.Icc (1 : ℕ) 4 = ({1, 2, 3, 4} : Finset ℕ) by decide,
            Finset.sum_insert (by decide), Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton, m1, m2, m3, m4]
          norm_num)
      · exact small_case 5 {5} (fun _ => -2) (by decide) (by
          have m1 : mulSeq {5} (fun _ => -2) 1 = 1 := by simp [mulSeq]
          have m2 : mulSeq {5} (fun _ => -2) 2 = 1 := by
            simp [mulSeq, Nat.factorization_eq_zero_of_not_dvd (show ¬ (5 : ℕ) ∣ 2 by decide)]
          have m3 : mulSeq {5} (fun _ => -2) 3 = 1 := by
            simp [mulSeq, Nat.factorization_eq_zero_of_not_dvd (show ¬ (5 : ℕ) ∣ 3 by decide)]
          have m4 : mulSeq {5} (fun _ => -2) 4 = 1 := by
            simp [mulSeq, Nat.factorization_eq_zero_of_not_dvd (show ¬ (5 : ℕ) ∣ 4 by decide)]
          have m5 : mulSeq {5} (fun _ => -2) 5 = -2 := by
            simp [mulSeq, Nat.prime_five.factorization_self]
          rw [show Finset.Icc (1 : ℕ) 5 = ({1, 2, 3, 4, 5} : Finset ℕ) by decide,
            Finset.sum_insert (by decide), Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_insert (by decide),
            Finset.sum_singleton, m1, m2, m3, m4, m5]
          norm_num)
      · exact small_case 6 {2, 3, 5} (fun r => if r = 2 then 5 else if r = 3 then 3 else -42)
          (by decide) (by
          have f42 : Nat.factorization 4 2 = 2 := by
            rw [show (4 : ℕ) = 2 * 2 from rfl,
              Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
              Nat.prime_two.factorization_self]
          have f62 : Nat.factorization 6 2 = 1 := by
            rw [show (6 : ℕ) = 2 * 3 from rfl,
              Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
              Nat.prime_two.factorization_self,
              Nat.factorization_eq_zero_of_not_dvd (show ¬ (2 : ℕ) ∣ 3 by decide)]
          have f63 : Nat.factorization 6 3 = 1 := by
            rw [show (6 : ℕ) = 2 * 3 from rfl,
              Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
              Nat.prime_three.factorization_self,
              Nat.factorization_eq_zero_of_not_dvd (show ¬ (3 : ℕ) ∣ 2 by decide)]
          have m1 : mulSeq {2, 3, 5} (fun r => if r = 2 then 5 else if r = 3 then 3 else -42) 1
              = 1 := by simp [mulSeq]
          have m2 : mulSeq {2, 3, 5} (fun r => if r = 2 then 5 else if r = 3 then 3 else -42) 2
              = 5 := by
            simp [mulSeq, Nat.prime_two.factorization_self,
              Nat.factorization_eq_zero_of_not_dvd (show ¬ (3 : ℕ) ∣ 2 by decide),
              Nat.factorization_eq_zero_of_not_dvd (show ¬ (5 : ℕ) ∣ 2 by decide)]
          have m3 : mulSeq {2, 3, 5} (fun r => if r = 2 then 5 else if r = 3 then 3 else -42) 3
              = 3 := by
            simp [mulSeq, Nat.prime_three.factorization_self,
              Nat.factorization_eq_zero_of_not_dvd (show ¬ (2 : ℕ) ∣ 3 by decide),
              Nat.factorization_eq_zero_of_not_dvd (show ¬ (5 : ℕ) ∣ 3 by decide)]
          have m4 : mulSeq {2, 3, 5} (fun r => if r = 2 then 5 else if r = 3 then 3 else -42) 4
              = 25 := by
            simp [mulSeq, f42,
              Nat.factorization_eq_zero_of_not_dvd (show ¬ (3 : ℕ) ∣ 4 by decide),
              Nat.factorization_eq_zero_of_not_dvd (show ¬ (5 : ℕ) ∣ 4 by decide)]
          have m5 : mulSeq {2, 3, 5} (fun r => if r = 2 then 5 else if r = 3 then 3 else -42) 5
              = -42 := by
            simp [mulSeq, Nat.prime_five.factorization_self,
              Nat.factorization_eq_zero_of_not_dvd (show ¬ (2 : ℕ) ∣ 5 by decide),
              Nat.factorization_eq_zero_of_not_dvd (show ¬ (3 : ℕ) ∣ 5 by decide)]
          have m6 : mulSeq {2, 3, 5} (fun r => if r = 2 then 5 else if r = 3 then 3 else -42) 6
              = 15 := by
            simp [mulSeq, f62, f63,
              Nat.factorization_eq_zero_of_not_dvd (show ¬ (5 : ℕ) ∣ 6 by decide)]
          rw [show Finset.Icc (1 : ℕ) 6 = ({1, 2, 3, 4, 5, 6} : Finset ℕ) by decide,
            Finset.sum_insert (by decide), Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton,
            m1, m2, m3, m4, m5, m6]
          norm_num)
      · exact small_case 7 {7} (fun _ => -3) (by decide) (by
          have m1 : mulSeq {7} (fun _ => -3) 1 = 1 := by simp [mulSeq]
          have m2 : mulSeq {7} (fun _ => -3) 2 = 1 := by
            simp [mulSeq, Nat.factorization_eq_zero_of_not_dvd (show ¬ (7 : ℕ) ∣ 2 by decide)]
          have m3 : mulSeq {7} (fun _ => -3) 3 = 1 := by
            simp [mulSeq, Nat.factorization_eq_zero_of_not_dvd (show ¬ (7 : ℕ) ∣ 3 by decide)]
          have m4 : mulSeq {7} (fun _ => -3) 4 = 1 := by
            simp [mulSeq, Nat.factorization_eq_zero_of_not_dvd (show ¬ (7 : ℕ) ∣ 4 by decide)]
          have m5 : mulSeq {7} (fun _ => -3) 5 = 1 := by
            simp [mulSeq, Nat.factorization_eq_zero_of_not_dvd (show ¬ (7 : ℕ) ∣ 5 by decide)]
          have m6 : mulSeq {7} (fun _ => -3) 6 = 1 := by
            simp [mulSeq, Nat.factorization_eq_zero_of_not_dvd (show ¬ (7 : ℕ) ∣ 6 by decide)]
          have m7 : mulSeq {7} (fun _ => -3) 7 = -3 := by
            simp [mulSeq, Nat.prime_seven.factorization_self]
          rw [show Finset.Icc (1 : ℕ) 7 = ({1, 2, 3, 4, 5, 6, 7} : Finset ℕ) by decide,
            Finset.sum_insert (by decide), Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_insert (by decide),
            Finset.sum_singleton, m1, m2, m3, m4, m5, m6, m7]
          norm_num)
      · exact small_case 8 {5, 7} (fun _ => -2) (by decide) (by
          have m1 : mulSeq {5, 7} (fun _ => -2) 1 = 1 := by simp [mulSeq]
          have m2 : mulSeq {5, 7} (fun _ => -2) 2 = 1 := by
            simp [mulSeq,
              Nat.factorization_eq_zero_of_not_dvd (show ¬ (5 : ℕ) ∣ 2 by decide),
              Nat.factorization_eq_zero_of_not_dvd (show ¬ (7 : ℕ) ∣ 2 by decide)]
          have m3 : mulSeq {5, 7} (fun _ => -2) 3 = 1 := by
            simp [mulSeq,
              Nat.factorization_eq_zero_of_not_dvd (show ¬ (5 : ℕ) ∣ 3 by decide),
              Nat.factorization_eq_zero_of_not_dvd (show ¬ (7 : ℕ) ∣ 3 by decide)]
          have m4 : mulSeq {5, 7} (fun _ => -2) 4 = 1 := by
            simp [mulSeq,
              Nat.factorization_eq_zero_of_not_dvd (show ¬ (5 : ℕ) ∣ 4 by decide),
              Nat.factorization_eq_zero_of_not_dvd (show ¬ (7 : ℕ) ∣ 4 by decide)]
          have m5 : mulSeq {5, 7} (fun _ => -2) 5 = -2 := by
            simp [mulSeq, Nat.prime_five.factorization_self,
              Nat.factorization_eq_zero_of_not_dvd (show ¬ (7 : ℕ) ∣ 5 by decide)]
          have m6 : mulSeq {5, 7} (fun _ => -2) 6 = 1 := by
            simp [mulSeq,
              Nat.factorization_eq_zero_of_not_dvd (show ¬ (5 : ℕ) ∣ 6 by decide),
              Nat.factorization_eq_zero_of_not_dvd (show ¬ (7 : ℕ) ∣ 6 by decide)]
          have m7 : mulSeq {5, 7} (fun _ => -2) 7 = -2 := by
            simp [mulSeq, Nat.prime_seven.factorization_self,
              Nat.factorization_eq_zero_of_not_dvd (show ¬ (5 : ℕ) ∣ 7 by decide)]
          have m8 : mulSeq {5, 7} (fun _ => -2) 8 = 1 := by
            simp [mulSeq,
              Nat.factorization_eq_zero_of_not_dvd (show ¬ (5 : ℕ) ∣ 8 by decide),
              Nat.factorization_eq_zero_of_not_dvd (show ¬ (7 : ℕ) ∣ 8 by decide)]
          rw [show Finset.Icc (1 : ℕ) 8 = ({1, 2, 3, 4, 5, 6, 7, 8} : Finset ℕ) by decide,
            Finset.sum_insert (by decide), Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton,
            m1, m2, m3, m4, m5, m6, m7, m8]
          norm_num)
    · exact exists_good_seq_of_nine_le (by omega)
  · rintro ⟨a, ha, hsum⟩
    by_contra hlt
    push Not at hlt
    have hn2 : n = 2 := by omega
    subst hn2
    have h2 : ∀ k, 1 ≤ k → a k + 2 * a (2 * k) = 0 := by
      intro k hk
      have hk0 := hsum k hk
      rw [show Finset.Icc (1 : ℕ) 2 = {1, 2} by decide,
        Finset.sum_insert (by decide : (1 : ℕ) ∉ ({2} : Finset ℕ)),
        Finset.sum_singleton] at hk0
      simp only [Nat.cast_one, Nat.cast_two, one_mul] at hk0
      exact hk0
    exact not_property_two ha h2
