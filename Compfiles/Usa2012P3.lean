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
  have hk0 : k ≠ 0 := by lia
  calc ∑ j ∈ Finset.Icc 1 n, (j : ℤ) * mulSeq P c (j * k)
      = ∑ j ∈ Finset.Icc 1 n, mulSeq P c k * ((j : ℤ) * mulSeq P c j) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hj0 : j ≠ 0 := by
          have h1 := (Finset.mem_Icc.mp hj).1
          lia
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
    lia
  have hvc1 : v * c ≤ ((v * c).natAbs : ℤ) := Int.le_natAbs
  set t : ℤ := ((u * c).natAbs : ℤ) + ((v * c).natAbs : ℤ) + 1 with ht
  have ht0 : 0 < t := by lia
  have hBt : ((u * c).natAbs : ℤ) < B * t := by
    have h1 : t ≤ B * t := by
      have h2 : (1 : ℤ) * t ≤ B * t :=
        mul_le_mul_of_nonneg_right (by lia) (le_of_lt ht0)
      rwa [one_mul] at h2
    lia
  have hAt : ((v * c).natAbs : ℤ) < A * t := by
    have h1 : t ≤ A * t := by
      have h2 : (1 : ℤ) * t ≤ A * t :=
        mul_le_mul_of_nonneg_right (by lia) (le_of_lt ht0)
      rwa [one_mul] at h2
    lia
  refine ⟨u * c + B * t, v * c - A * t, by lia, by lia, ?_⟩
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
  lia

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
        (Nat.not_dvd_of_pos_of_lt (by norm_num) (by lia)),
      hp.factorization_self]
  have hfac2 : Nat.factorization (2 * p) q = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro h
    rcases hq.dvd_mul.mp h with h2 | hp'
    · exact Nat.not_dvd_of_pos_of_lt (by norm_num) (by lia) h2
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
        (Nat.not_dvd_of_pos_of_lt (by norm_num) (by lia)),
      hp.factorization_self]
  have hfac2 : Nat.factorization (3 * p) q = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro h
    rcases hq.dvd_mul.mp h with h3 | hp'
    · exact Nat.not_dvd_of_pos_of_lt (by norm_num) (by lia) h3
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
  have h4p' : n < p * 4 := by lia
  have h2q' : n < q * 2 := by lia
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
      · lia
      · exact h
    lia
  have h3p_ne : 3 * p ≠ q := by
    intro h
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp ⟨3, by rw [mul_comm]; exact h.symm⟩)
  by_cases h2 : 2 * p ≤ n
  · by_cases h3 : 3 * p ≤ n
    · -- case `3 * p ≤ n`: multiples of `p` in `[1, n]` are `p, 2p, 3p`
      rw [ite_eq_left h2, ite_eq_left h3]
      have hss : ({p, 2 * p, 3 * p, q} : Finset ℕ) ⊆ Finset.Icc 1 n := by
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rw [Finset.mem_Icc]
        rcases hj with rfl | rfl | rfl | rfl
        · exact ⟨by lia, hpn⟩
        · exact ⟨by lia, h2⟩
        · exact ⟨by lia, h3⟩
        · exact ⟨by lia, hqn⟩
      have hvan : ∀ j ∈ Finset.Icc 1 n, j ∉ ({p, 2 * p, 3 * p, q} : Finset ℕ) →
          (j : ℤ) * (mulSeq {p, q} (cfun p q x y) j - 1) = 0 := by
        intro j hj hjs
        simp only [Finset.mem_insert, Finset.mem_singleton] at hjs
        rw [Finset.mem_Icc] at hj
        push Not at hjs
        exact term_eq_zero hplt h2q h4p hj.1 hj.2 hjs.1 hjs.2.1 hjs.2.2.1 hjs.2.2.2
      have hsub := (Finset.sum_subset hss hvan).symm
      rw [hsub, Finset.sum_insert (by simp; lia),
        Finset.sum_insert (by simp; lia), Finset.sum_insert (by simp; lia),
        Finset.sum_singleton, mulSeq_cfun_p hp hplt, mulSeq_cfun_2p hp hq hp5 hq7 hplt,
        mulSeq_cfun_3p hp hq hp5 hq7 hplt, mulSeq_cfun_q hp hq hplt]
      ring
    · -- case `2 * p ≤ n < 3 * p`: multiples of `p` in `[1, n]` are `p, 2p`
      rw [ite_eq_left h2, ite_eq_right h3]
      have hss : ({p, 2 * p, q} : Finset ℕ) ⊆ Finset.Icc 1 n := by
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rw [Finset.mem_Icc]
        rcases hj with rfl | rfl | rfl
        · exact ⟨by lia, hpn⟩
        · exact ⟨by lia, h2⟩
        · exact ⟨by lia, hqn⟩
      have hvan : ∀ j ∈ Finset.Icc 1 n, j ∉ ({p, 2 * p, q} : Finset ℕ) →
          (j : ℤ) * (mulSeq {p, q} (cfun p q x y) j - 1) = 0 := by
        intro j hj hjs
        simp only [Finset.mem_insert, Finset.mem_singleton] at hjs
        rw [Finset.mem_Icc] at hj
        push Not at hjs
        exact term_eq_zero hplt h2q h4p hj.1 hj.2 hjs.1 hjs.2.1 (by lia) hjs.2.2
      have hsub := (Finset.sum_subset hss hvan).symm
      rw [hsub, Finset.sum_insert (by simp; lia),
        Finset.sum_insert (by simp; lia), Finset.sum_singleton,
        mulSeq_cfun_p hp hplt, mulSeq_cfun_2p hp hq hp5 hq7 hplt,
        mulSeq_cfun_q hp hq hplt]
      ring
  · by_cases h3 : 3 * p ≤ n
    · lia
    · -- case `n < 2 * p`: the only multiple of `p` in `[1, n]` is `p`
      rw [ite_eq_right h2, ite_eq_right h3]
      have hss : ({p, q} : Finset ℕ) ⊆ Finset.Icc 1 n := by
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rw [Finset.mem_Icc]
        rcases hj with rfl | rfl
        · exact ⟨by lia, hpn⟩
        · exact ⟨by lia, hqn⟩
      have hvan : ∀ j ∈ Finset.Icc 1 n, j ∉ ({p, q} : Finset ℕ) →
          (j : ℤ) * (mulSeq {p, q} (cfun p q x y) j - 1) = 0 := by
        intro j hj hjs
        simp only [Finset.mem_insert, Finset.mem_singleton] at hjs
        rw [Finset.mem_Icc] at hj
        push Not at hjs
        exact term_eq_zero hplt h2q h4p hj.1 hj.2 hjs.1 (by lia) (by lia) hjs.2
      have hsub := (Finset.sum_subset hss hvan).symm
      rw [hsub, Finset.sum_insert (by simp; lia), Finset.sum_singleton,
        mulSeq_cfun_p hp hplt, mulSeq_cfun_q hp hq hplt]
      ring

/-- Construction for `9 ≤ n`: pick primes `p`, `q` via Bertrand's postulate with
`⌈n/2⌉ < q ≤ 2⌈n/2⌉` and `(q-1)/2 < p ≤ q-1`, take `a r = 1` for primes `r ∉ {p, q}`,
and choose nonzero `a p`, `a q` by Bézout so that `∑ j ∈ [1,n], j * a j = 0`. -/
lemma exists_good_seq_of_nine_le {n : ℕ} (hn : 9 ≤ n) :
    ∃ a : ℕ → ℤ, (∀ i, 1 ≤ i → a i ≠ 0) ∧
      ∀ k, 1 ≤ k → ∑ j ∈ Finset.Icc 1 n, (j : ℤ) * a (j * k) = 0 := by
  obtain ⟨q, hq, hm_lt, hq_le⟩ :=
    Nat.exists_prime_lt_and_le_two_mul ((n + 1) / 2) (by lia)
  have hq6 : 6 ≤ q := by lia
  have hq7 : 7 ≤ q := by
    rcases lt_or_ge q 7 with h | h
    · interval_cases q
      · norm_num at hq
    · exact h
  have hqodd : q % 2 = 1 := by
    rcases hq.eq_two_or_odd with h | h
    · lia
    · exact h
  have h2q : n < 2 * q := by lia
  have hq_le_n : q ≤ n := by
    by_contra hlt
    push Not at hlt
    have hqn1 : q = n + 1 := by lia
    subst hqn1
    lia
  obtain ⟨p, hp, hp_gt, hp_le⟩ :=
    Nat.exists_prime_lt_and_le_two_mul ((q - 1) / 2) (by lia)
  have hp4 : 4 ≤ p := by lia
  have hp5 : 5 ≤ p := by
    rcases lt_or_ge p 5 with h | h
    · interval_cases p
      · norm_num at hp
    · exact h
  have hplt : p < q := by lia
  have h2p_ge : q ≤ 2 * p := by lia
  have h4p : n < 4 * p := by lia
  have hpn : p ≤ n := by lia
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
        rw [ite_eq_left rfl]
        exact hx
      · rw [hrq]
        show (if q = p then x else if q = q then y else 1) ≠ 0
        rw [ite_eq_right (ne_of_lt hplt).symm, ite_eq_left rfl]
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
      · have h2 : 2 * p ≤ n := by lia
        simp only [ite_eq_left h2, ite_eq_left h3] at hm_eq hbez ⊢
        rw [hm_eq] at hbez
        linear_combination hbez
      · by_cases h2 : 2 * p ≤ n
        · simp only [ite_eq_right h3, ite_eq_left h2] at hm_eq hbez ⊢
          rw [hm_eq] at hbez
          linear_combination hbez
        · simp only [ite_eq_right h3, ite_eq_right h2] at hm_eq hbez ⊢
          rw [hm_eq] at hbez
          linear_combination hbez
  rcases lt_or_ge n (3 * p) with h3 | h3
  · rcases lt_or_ge n (2 * p) with h2 | h2
    · -- here the only multiple of `p` in `[1, n]` is `p`, and `p` is coprime to `q`
      have hcop : Nat.Coprime p q := by
        apply Nat.Coprime.symm
        rw [hq.coprime_iff_not_dvd]
        exact Nat.not_dvd_of_pos_of_lt hp.pos hplt
      exact build p (by lia) hcop (by
        rw [ite_eq_right (by lia : ¬ 2 * p ≤ n), ite_eq_right (by lia : ¬ 3 * p ≤ n)]
        ring)
    · -- here the multiples of `p` in `[1, n]` are `p, 2p`, and `3 * p` is coprime to `q`
      have hcop : Nat.Coprime (3 * p) q := by
        apply Nat.Coprime.symm
        rw [hq.coprime_iff_not_dvd]
        intro h
        rcases hq.dvd_mul.mp h with h3' | hp'
        · exact Nat.not_dvd_of_pos_of_lt (by norm_num) (by lia) h3'
        · exact Nat.not_dvd_of_pos_of_lt hp.pos hplt hp'
      exact build (3 * p) (by lia) hcop (by
        rw [ite_eq_left h2, ite_eq_right (by lia : ¬ 3 * p ≤ n)]
        push_cast
        ring)
  · -- here the multiples of `p` in `[1, n]` are `p, 2p, 3p`, and `6 * p` is coprime to `q`
    have hcop : Nat.Coprime (6 * p) q := by
      apply Nat.Coprime.symm
      rw [hq.coprime_iff_not_dvd]
      intro h
      rcases hq.dvd_mul.mp h with h6 | hp'
      · exact Nat.not_dvd_of_pos_of_lt (by norm_num) (by lia) h6
      · exact Nat.not_dvd_of_pos_of_lt hp.pos hplt hp'
    exact build (6 * p) (by lia) hcop (by
      have h2 : 2 * p ≤ n := by lia
      rw [ite_eq_left h2, ite_eq_left h3]
      push_cast
      ring)

/-- The small cases `3 ≤ n ≤ 8`, each given by an explicit completely
multiplicative sequence. -/
lemma small_case (n : ℕ) (P : Finset ℕ) (c : ℕ → ℤ) (hc : ∀ r ∈ P, c r ≠ 0)
    (hsum : ∑ j ∈ Finset.range n, (j + 1 : ℤ) * mulSeq P c (j + 1) = 0) :
    ∃ a : ℕ → ℤ, (∀ i, 1 ≤ i → a i ≠ 0) ∧
      ∀ k, 1 ≤ k → ∑ j ∈ Finset.range n, (j + 1 : ℤ) * a ((j + 1) * k) = 0 := by
  refine ⟨mulSeq P c, fun i _ => mulSeq_ne_zero P c hc i, fun k hk => ?_⟩
  replace hsum : ∑ j ∈ Finset.Icc 1 n, (j : ℤ) * mulSeq P c j = 0 := by
    simpa [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, add_comm] using hsum
  have := condition_of_sum_eq_zero hsum k hk
  simpa [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, add_comm]

/-! Lemmas for factorization of small numbres. -/
namespace factorization

open Nat

lemma f22 : factorization 2 2 = 1 := by norm_num

lemma f23 : factorization 2 3 = 0 := by norm_num

lemma f25 : factorization 2 5 = 0 := by norm_num

lemma f27 : factorization 2 7 = 0 := by norm_num

lemma f32 : factorization 3 2 = 0 := by norm_num

lemma f33 : factorization 3 3 = 1 := by norm_num

lemma f35 : factorization 3 5 = 0 := by norm_num

lemma f37 : factorization 3 7 = 0 := by norm_num

lemma f42 : factorization 4 2 = 2 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, factorization_mul, Finsupp.add_apply, f22]
  all_goals norm_num

lemma f43 : factorization 4 3 = 0 := by
  rw [Nat.factorization_eq_zero_of_not_dvd]
  norm_num

lemma f45 : factorization 4 5 = 0 := by
  rw [Nat.factorization_eq_zero_of_not_dvd]
  norm_num

lemma f47 : factorization 4 7 = 0 := by
  rw [Nat.factorization_eq_zero_of_not_dvd]
  norm_num

lemma f52 : factorization 5 2 = 0 := by norm_num

lemma f53 : factorization 5 3 = 0 := by norm_num

lemma f55 : factorization 5 5 = 1 := by norm_num

lemma f57 : factorization 5 7 = 0 := by norm_num

lemma f62 : factorization 6 2 = 1 := by
  rw [show 6 = 2 * 3 by norm_num, factorization_mul]
  all_goals norm_num

lemma f63 : factorization 6 3 = 1 := by
  rw [show 6 = 2 * 3 by norm_num, factorization_mul]
  all_goals norm_num

lemma f65 : factorization 6 5 = 0 := by
  rw [Nat.factorization_eq_zero_of_not_dvd]
  norm_num

lemma f67 : factorization 6 7 = 0 := by
  rw [Nat.factorization_eq_zero_of_not_dvd]
  norm_num

lemma f75 : factorization 7 5 = 0 := by
  rw [Nat.factorization_eq_zero_of_not_dvd]
  norm_num

lemma f77 : factorization 7 7 = 1 := by norm_num

lemma f85 : factorization 8 5 = 0 := by
  rw [Nat.factorization_eq_zero_of_not_dvd]
  norm_num

lemma f87 : factorization 8 7 = 0 := by
  rw [Nat.factorization_eq_zero_of_not_dvd]
  norm_num

end factorization

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
      open factorization in
      · refine small_case 3 {3} (fun _ => -1) (by decide) ?_
        simp [Finset.sum_range_succ, mulSeq, f23, f33]
      · refine small_case 4 {2, 3} (fun _ => -1) (by decide) ?_
        simp [Finset.sum_range_succ, mulSeq, f22, f23, f32, f33, f42, f43]
      · refine small_case 5 {5} (fun _ => -2) (by decide) ?_
        simp [Finset.sum_range_succ, mulSeq, f25, f35, f45, f55]
      · refine small_case 6 {2, 3, 5} (fun r => if r = 2 then 5 else if r = 3 then 3 else -42) (by decide) ?_
        simp [Finset.sum_range_succ, mulSeq,
          f22, f23, f25, f32, f33, f35, f42, f43, f45, f52, f53, f55, f62, f63, f65]
      · refine small_case 7 {7} (fun _ => -3) (by decide) ?_
        simp [Finset.sum_range_succ, mulSeq, f27, f37, f47, f57, f67, f77]
      · refine small_case 8 {5, 7} (fun _ => -2) (by decide) ?_
        simp [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, mulSeq,
          f25, f27, f35, f37, f45, f47, f55, f57, f65, f67, f75, f77, f85, f87]
    · exact exists_good_seq_of_nine_le (by lia)
  · rintro ⟨a, ha, hsum⟩
    by_contra hlt
    push Not at hlt
    have hn2 : n = 2 := by lia
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
