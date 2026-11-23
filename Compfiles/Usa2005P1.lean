/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Finset.NatDivisors
public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Zify
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 2005, Problem 1

Determine all composite positive integers n for which it is possible to arrange
all divisors of n that are greater than 1 in a circle so that no two adjacent
divisors are relatively prime.
-/

namespace Usa2005P1

/-- The adjacency condition required of neighboring divisors in the circle:
they must not be relatively prime. -/
def R (a b : ℕ) : Prop := ¬ Nat.Coprime a b

/-- `GoodCircle n` says that all divisors of `n` that are greater than `1`
can be arranged in a circle so that no two adjacent divisors are relatively
prime.  The circle is represented by a list `l` containing each such divisor
exactly once; adjacency means "consecutive in `l`" (via `l.IsChain R`) plus the
wrap-around pair (`l.getLast?` with `l.head?`). -/
def GoodCircle (n : ℕ) : Prop :=
  ∃ l : List ℕ, l.Nodup ∧ l ≠ [] ∧
    (∀ d : ℕ, d ∈ l ↔ d ∣ n ∧ 1 < d) ∧
    l.IsChain R ∧
    ∀ a ∈ l.getLast?, ∀ b ∈ l.head?, R a b

/-- The answer: all composite positive integers other than products of two
distinct primes. -/
determine SolutionSet : Set ℕ :=
  {n | 1 < n ∧ ¬ n.Prime ∧ ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ n = p * q}

snip begin

/-- Numbers sharing a common factor `≥ 2` are not coprime. -/
lemma R_of_dvd_of_dvd {d a b : ℕ} (hd : 2 ≤ d) (ha : d ∣ a) (hb : d ∣ b) : R a b := by
  intro hc
  have h1 : d ∣ 1 := hc ▸ Nat.dvd_gcd ha hb
  have := Nat.le_of_dvd one_pos h1
  lia

/-- If `2 ≤ a` and `a ∣ b`, then `a` and `b` are not coprime. -/
lemma R_of_dvd {a b : ℕ} (ha : 2 ≤ a) (hb : a ∣ b) : R a b :=
  R_of_dvd_of_dvd ha dvd_rfl hb

/-- `R` is symmetric. -/
lemma R_symm {a b : ℕ} (h : R a b) : R b a := fun hc => h hc.symm

/-- A list whose elements are all divisible by some `r ≥ 2` is an `R`-chain. -/
lemma isChain_of_forall_dvd {r : ℕ} (hr : 2 ≤ r) :
    ∀ {l : List ℕ}, (∀ x ∈ l, r ∣ x) → l.IsChain R
  | [], _ => .nil
  | [a], _ => .singleton a
  | a :: b :: t, h =>
      .cons_cons (R_of_dvd_of_dvd hr (h a (by simp)) (h b (by simp)))
        (isChain_of_forall_dvd hr (fun x hx => h x (by simp [hx])))

/-- For distinct primes `p` and `q`, the divisors of `p * q` greater than `1`
are exactly `p`, `q` and `p * q`. -/
lemma dvd_mul_prime_prime {p q x : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hxdvd : x ∣ p * q) (hx1 : 1 < x) : x = p ∨ x = q ∨ x = p * q := by
  have hpq0 : p * q ≠ 0 := mul_ne_zero hp.ne_zero hq.ne_zero
  have hx : x ∈ (p * q).divisors := Nat.mem_divisors.mpr ⟨hxdvd, hpq0⟩
  rw [Nat.divisors_mul, hp.divisors, hq.divisors] at hx
  rw [Finset.mem_mul] at hx
  obtain ⟨a, ha, b, hb, hax⟩ := hx
  rw [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exfalso; rw [← hax, one_mul] at hx1; exact lt_irrefl 1 hx1
  · exact Or.inr (Or.inl (by rw [← hax, one_mul]))
  · exact Or.inl (by rw [← hax, mul_one])
  · exact Or.inr (Or.inr hax.symm)

/-- For distinct primes `p q`, no circle exists: in any circle the coprime
pair `p, q` would have to be adjacent. -/
lemma not_goodCircle_mul {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ¬ GoodCircle (p * q) := by
  rintro ⟨l, hnodup, hlne, hmem, hchain, hwrap⟩
  have hset : ∀ x : ℕ, x ∈ l ↔ x = p ∨ x = q ∨ x = p * q := by
    intro x
    rw [hmem x]
    constructor
    · rintro ⟨hxdvd, hx1⟩
      exact dvd_mul_prime_prime hp hq hxdvd hx1
    · rintro (rfl | rfl | rfl)
      · exact ⟨dvd_mul_right _ _, hp.one_lt⟩
      · exact ⟨dvd_mul_left _ _, hq.one_lt⟩
      · exact ⟨dvd_refl _, lt_of_lt_of_le hp.one_lt
          (Nat.le_mul_of_pos_right _ hq.pos)⟩
  have htf : l.toFinset = {p, q, p * q} := by
    ext x
    simp only [List.mem_toFinset, Finset.mem_insert, Finset.mem_singleton]
    exact hset x
  have hcard3 : l.length = 3 := by
    have hne1 : p ≠ p * q := by simpa [hp.ne_zero] using hq.ne_one
    have hne2 : q ≠ p * q := by simpa [hq.ne_zero] using hp.ne_one
    have h1 : l.toFinset.card = 3 := by
      rw [htf, Finset.card_insert_of_notMem (by simp [hpq, hne1]),
        Finset.card_insert_of_notMem (by simp [hne2]), Finset.card_singleton]
    rw [← h1, List.toFinset_card_of_nodup hnodup]
  obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp hcard3
  -- adjacency facts
  have hRab : R a b := (List.isChain_cons_cons.mp hchain).1
  have hRbc : R b c := (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp hchain).2).1
  have hRca : R c a := hwrap c (by simp) a (by simp)
  have hcop : p.Coprime q := (Nat.coprime_primes hp hq).mpr hpq
  have hp_mem : p ∈ [a, b, c] := (hset p).mpr (Or.inl rfl)
  have hq_mem : q ∈ [a, b, c] := (hset q).mpr (Or.inr (Or.inl rfl))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp_mem hq_mem
  rcases hp_mem with rfl | rfl | rfl <;> rcases hq_mem with rfl | rfl | rfl
  · exact hpq rfl
  · exact hRab hcop
  · exact hRca hcop.symm
  · exact hRab hcop.symm
  · exact hpq rfl
  · exact hRbc hcop
  · exact hRca hcop
  · exact hRbc hcop.symm
  · exact hpq rfl

/-- A *path* for `m`: a list containing each divisor of `m` greater than `1`
exactly once, in which adjacent entries are not coprime. -/
def IsPath (m : ℕ) (l : List ℕ) : Prop :=
  l.Nodup ∧ (∀ d : ℕ, d ∈ l ↔ d ∣ m ∧ 1 < d) ∧ l.IsChain R

/-- A finite set can be listed starting with any given element. -/
lemma exists_list_head (S : Finset ℕ) {x : ℕ} (hx : x ∈ S) :
    ∃ L : List ℕ, L.Nodup ∧ (∀ d, d ∈ L ↔ d ∈ S) ∧ L.head? = some x := by
  refine ⟨x :: (S.erase x).toList, ?_, fun d ↦ ?_, rfl⟩
  · simp [Finset.nodup_toList]
  · by_cases hd : d = x <;> simp [hd, hx]

/-- A finite set can be listed starting and ending with any two given distinct elements. -/
lemma exists_list_head_getLast (S : Finset ℕ) {x y : ℕ} (hx : x ∈ S) (hy : y ∈ S)
    (hxy : x ≠ y) :
    ∃ L : List ℕ, L.Nodup ∧ (∀ d, d ∈ L ↔ d ∈ S) ∧ L.head? = some x ∧ L.getLast? = some y := by
  obtain ⟨L, h1, h2, h3⟩ := exists_list_head (S.erase y) (Finset.mem_erase.mpr ⟨hxy, hx⟩)
  refine ⟨L ++ [y], ?_, fun d ↦ ?_, ?_, by simp⟩
  · simpa [List.nodup_append, h1, h2] using fun a ha _ ↦ ha
  · by_cases hd : d = y <;> simp [h2, hd, hy]
  · cases L <;> simp_all

/-- If `z` divides the `p`-free part of `n`, then `p * z` divides `n`. -/
lemma mul_dvd_of_dvd_ordCompl {n p z : ℕ} (hn : n ≠ 0) (hp : p.Prime) (hpn : p ∣ n)
    (hz : z ∣ ordCompl[p] n) : p * z ∣ n := by
  rw [← Nat.ordProj_mul_ordCompl_eq_self n p]
  exact mul_dvd_mul (dvd_pow_self p (hp.factorization_pos_of_dvd hn hpn).ne') hz

/-- A path for the `p`-free part of `n`, followed by the multiples of `p` dividing `n`
in any order, is a path for `n`, as long as the two parts fit together. -/
lemma IsPath.append {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) {l L : List ℕ}
    (hl : IsPath (ordCompl[p] n) l) (hL : L.Nodup) (hmem : ∀ d, d ∈ L ↔ d ∣ n ∧ p ∣ d)
    (hj : ∀ z ∈ l.getLast?, ∀ x ∈ L.head?, R z x) : IsPath n (l ++ L) := by
  obtain ⟨hl1, hl2, hl3⟩ := hl
  refine ⟨List.nodup_append'.mpr ⟨hl1, hL, fun d hd hd' ↦ ?_⟩, fun d ↦ ?_, ?_⟩
  · exact Nat.not_dvd_ordCompl hp hn (((hmem d).mp hd').2.trans ((hl2 d).mp hd).1)
  · rw [List.mem_append, hl2, hmem]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1.trans (Nat.ordCompl_dvd n p), h2⟩
      · exact ⟨h1, hp.one_lt.trans_le
          (Nat.le_of_dvd (Nat.pos_of_dvd_of_pos h1 (Nat.pos_of_ne_zero hn)) h2)⟩
    · rintro ⟨h1, h2⟩
      by_cases hpd : p ∣ d
      · exact .inr ⟨h1, hpd⟩
      · have hc : Nat.Coprime d (p ^ n.factorization p) :=
          ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd).symm.pow_right _
        exact .inl ⟨hc.dvd_of_dvd_mul_left (by rwa [Nat.ordProj_mul_ordCompl_eq_self]), h2⟩
  · exact hl3.append (isChain_of_forall_dvd hp.two_le fun x hx ↦ ((hmem x).mp hx).2) hj

/-- Every positive integer has a path: take a path for the part of `n` coprime to
its smallest prime factor `p`, and then list the multiples of `p`, starting with
`p` times the last entry so far. -/
lemma exists_isPath (n : ℕ) (hn : n ≠ 0) : ∃ l, IsPath n l := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  obtain rfl | hn1 := eq_or_ne n 1
  · exact ⟨[], List.nodup_nil, fun d ↦ by simp; lia, .nil⟩
  have hp := Nat.minFac_prime hn1
  have hpn := n.minFac_dvd
  set p := n.minFac
  obtain ⟨l, hl⟩ := ih (ordCompl[p] n)
    (Nat.div_lt_self (Nat.pos_of_ne_zero hn)
      (Nat.one_lt_pow (hp.factorization_pos_of_dvd hn hpn).ne' hp.one_lt))
    (Nat.ordCompl_pos p hn).ne'
  obtain ⟨x, hxn, hpx, hzx⟩ : ∃ x, x ∣ n ∧ p ∣ x ∧ ∀ z ∈ l.getLast?, R z x := by
    rcases h : l.getLast? with _ | z
    · exact ⟨p, hpn, dvd_rfl, by simp⟩
    · have hz := (hl.2.1 z).mp (List.mem_of_getLast? h)
      exact ⟨p * z, mul_dvd_of_dvd_ordCompl hn hp hpn hz.1, dvd_mul_right _ _,
        by simpa using R_of_dvd hz.2 (dvd_mul_left z p)⟩
  obtain ⟨L, hL1, hL2, hL3⟩ :=
    exists_list_head (n.divisors.filter (p ∣ ·)) (x := x) (by simp [hxn, hpx, hn])
  exact ⟨l ++ L, hl.append hn hp hL1 (fun d ↦ by simp [hL2, hn])
    (fun z hz x' hx' ↦ by simp_all)⟩

/-- Let `p` be the smallest prime factor of `n` and take any path `l` for the part of
`n` coprime to `p`. Choose distinct multiples `x`, `y` of `p` such that `x` shares a
factor with the last entry of `l` and `y` shares a factor with the first entry of `l`.
Then `l`, followed by the multiples of `p` listed from `x` to `y`, is a good circle. -/
lemma goodCircle_of_not_pq {n : ℕ} (hn : 1 < n) (hnp : ¬ n.Prime)
    (h : ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ n = p * q) : GoodCircle n := by
  have hn0 : n ≠ 0 := by lia
  have hp := Nat.minFac_prime hn.ne'
  have hpn := n.minFac_dvd
  set p := n.minFac
  obtain ⟨l, hl⟩ := exists_isPath (ordCompl[p] n) (Nat.ordCompl_pos p hn0).ne'
  have hmul : ∀ z ∈ l, p * z ∣ n ∧ R z (p * z) ∧ R (p * z) z := fun z hz ↦
    have hz' := (hl.2.1 z).mp hz
    have hR := R_of_dvd hz'.2 (dvd_mul_left z p)
    ⟨mul_dvd_of_dvd_ordCompl hn0 hp hpn hz'.1, hR, R_symm hR⟩
  obtain ⟨x, y, hxn, hpx, hyn, hpy, hxy, hzx, hya⟩ : ∃ x y, x ∣ n ∧ p ∣ x ∧ y ∣ n ∧ p ∣ y ∧
      x ≠ y ∧ (∀ z ∈ l.getLast?, R z x) ∧ (∀ a ∈ l.head?, R y a) := by
    match l, hl, hmul with
    | [], _, _ =>
      -- `n` is a prime power: use `p` and `n`.
      exact ⟨p, n, hpn, dvd_rfl, dvd_rfl, hpn, fun h' ↦ hnp (h' ▸ hp), by simp, by simp⟩
    | [q], hl, hmul =>
      -- `n = p ^ k * q` with `q` prime: use `p * q` and `n`, which are distinct as `k ≥ 2`.
      have hq := (hl.2.1 q).mp (by simp)
      obtain ⟨h1, h2, -⟩ := hmul q (by simp)
      refine ⟨p * q, n, h1, dvd_mul_right _ _, dvd_rfl, hpn, fun hpq ↦ ?_, by simpa using h2,
        by simpa using R_symm (R_of_dvd hq.2 (hq.1.trans (Nat.ordCompl_dvd n p)))⟩
      have hqm : q.minFac = q := by
        simpa using (hl.2.1 q.minFac).mpr
          ⟨(Nat.minFac_dvd q).trans hq.1, (Nat.minFac_prime (by lia)).one_lt⟩
      have hqp : q.Prime := hqm ▸ Nat.minFac_prime (by lia)
      exact h ⟨p, q, hp, hqp, fun hpq' ↦ Nat.not_dvd_ordCompl hp hn0 (hpq' ▸ hq.1), hpq.symm⟩
    | a :: b :: t, hl, hmul =>
      -- Otherwise the path has distinct endpoints `a` and `z`: use `p * z` and `p * a`.
      have hz := List.getLast?_eq_getLast_of_ne_nil (l := b :: t) (by simp)
      set z := (b :: t).getLast (by simp)
      have hzt : z ∈ b :: t := List.mem_of_getLast? hz
      have hza : z ≠ a := fun h' ↦ (List.nodup_cons.mp hl.1).1 (h' ▸ hzt)
      obtain ⟨h1, h2, -⟩ := hmul z (List.mem_cons_of_mem a hzt)
      obtain ⟨h3, -, h4⟩ := hmul a (by simp)
      exact ⟨p * z, p * a, h1, dvd_mul_right _ _, h3, dvd_mul_right _ _,
        fun h' ↦ hza (Nat.eq_of_mul_eq_mul_left hp.pos h'),
        by simpa [List.getLast?_cons_cons, hz] using h2, by simpa using h4⟩
  obtain ⟨L, hL1, hL2, hL3, hL4⟩ := exists_list_head_getLast (n.divisors.filter (p ∣ ·))
    (x := x) (y := y) (by simp [hxn, hpx, hn0]) (by simp [hyn, hpy, hn0]) hxy
  have hL0 : L ≠ [] := by rintro rfl; simp at hL3
  have hpath := hl.append hn0 hp hL1 (fun d ↦ by simp [hL2, hn0])
    (fun z hz x' hx' ↦ by simp_all)
  refine ⟨l ++ L, hpath.1, by simp [hL0], hpath.2.1, hpath.2.2, fun a ha b hb ↦ ?_⟩
  rw [List.getLast?_append_of_ne_nil _ hL0, hL4] at ha
  obtain rfl : y = a := by simpa using ha
  cases l with
  | nil =>
    obtain rfl : x = b := by simpa [hL3] using hb
    exact R_of_dvd_of_dvd hp.two_le hpy hpx
  | cons c t => exact hya b (by simpa using hb)

snip end

/-- USA Mathematical Olympiad 2005, Problem 1:
the composite positive integers whose divisors greater than `1` can be arranged
in a circle with no two adjacent divisors relatively prime are exactly the
composite numbers that are not products of two distinct primes. -/
problem usa2005_p1 (n : ℕ) (hn : 1 < n) (hnp : ¬ n.Prime) :
    GoodCircle n ↔ n ∈ SolutionSet := by
  constructor
  · intro hgc
    refine ⟨hn, hnp, ?_⟩
    rintro ⟨p, q, hp, hq, hpq, rfl⟩
    exact not_goodCircle_mul hp hq hpq hgc
  · rintro ⟨-, -, h⟩
    exact goodCircle_of_not_pq hn hnp h

end Usa2005P1
