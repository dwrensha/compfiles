/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Data.Nat.Squarefree
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.NumberTheory]
  problemImportedFrom :=
    "https://github.com/humanfia/imo2026"
}

/-!
# International Mathematical Olympiad 2026, Problem 6

Let a₁, a₂, a₃, … be an infinite sequence of positive integers greater
than 1. Suppose that for all positive integers n, the number a_{n+1} is the
smallest positive integer greater than a_n such that gcd(a_{n+1}, a_i) > 1
for every i = 1, 2, …, n.

Prove that there exist positive integers T and L such that a_{n+T} = a_n + L
for every positive integer n.

(Note that gcd(x, y) denotes the greatest common divisor of positive integers
x and y.)

Statement formalization adapted from AxiomMath/IMO2026; proof adapted from Humanfia's Kimi-K3 solutions (https://github.com/humanfia/imo2026).
-/

namespace Imo2026P6

/-- The predicate stating that `a : ℕ → ℕ` (0-indexed) is a sequence satisfying Definition 1:
each term exceeds `1`, and each subsequent term is the smallest integer strictly larger than the
previous one that shares a common factor with every earlier term. -/
def IsValidSeq (a : ℕ → ℕ) : Prop :=
  (∀ n, 1 < a n) ∧
  (∀ n, a n < a (n + 1) ∧
        (∀ i ≤ n, 1 < Nat.gcd (a (n + 1)) (a i)) ∧
        (∀ b, a n < b → b < a (n + 1) → ∃ i ≤ n, Nat.gcd b (a i) = 1))

/-- For any sequence satisfying Definition 1, there exist positive integers `T` and `L` such that
`a (n + T) = a n + L` for every `n`. Equivalently, the sequence of consecutive differences is
purely periodic. -/
problem imo2026_p6 (a : ℕ → ℕ) (ha : IsValidSeq a) :
    ∃ T L : ℕ, 0 < T ∧ 0 < L ∧ ∀ n, a (n + T) = a n + L := by
  -- Any later term shares a common factor with every earlier term.
  have hgcd : ∀ i j : ℕ, i < j → 1 < Nat.gcd (a j) (a i) := by
    intro i j hij
    have hj : 1 ≤ j := by lia
    have h := (ha.2 (j - 1)).2.1 i (by lia : i ≤ j - 1)
    rwa [Nat.sub_add_cancel hj] at h
  -- The sequence is strictly increasing.
  have hmono : StrictMono a := strictMono_nat_of_lt_succ fun n => (ha.2 n).1
  -- Growth bound: `a n` is at least `a 0 + n`.
  have hge : ∀ n : ℕ, a 0 + n ≤ a n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h := (ha.2 n).1
      lia
  -- Every term belongs to `V = {b > 1 | ∀ i, 1 < gcd b (a i)}`.
  have haV : ∀ n : ℕ, 1 < a n ∧ ∀ i : ℕ, 1 < Nat.gcd (a n) (a i) := by
    intro n
    refine ⟨ha.1 n, fun i => ?_⟩
    rcases lt_trichotomy i n with h | h | h
    · exact hgcd i n h
    · subst h
      rw [Nat.gcd_self]
      exact ha.1 i
    · rw [Nat.gcd_comm]
      exact hgcd n i h
  -- Every member of `V` that is at least `a 0` is a term: the sequence is exactly the
  -- increasing enumeration of `V ∩ [a 0, ∞)`.
  have hVenum : ∀ b : ℕ, 1 < b → (∀ i : ℕ, 1 < Nat.gcd b (a i)) → a 0 ≤ b → ∃ n, a n = b := by
    intro b hb1 hbgcd hb0
    have hex : ∃ n, b ≤ a n := ⟨b, le_trans (by lia : b ≤ a 0 + b) (hge b)⟩
    generalize hn_def : Nat.find hex = n
    have hn : b ≤ a n := by
      rw [← hn_def]
      exact Nat.find_spec hex
    have hmin' : ∀ m, m < n → ¬ b ≤ a m := by
      intro m hm
      rw [← hn_def] at hm
      exact Nat.find_min hex hm
    by_cases h0 : n = 0
    · subst h0
      exact ⟨0, by lia⟩
    · have h1 : 1 ≤ n := by lia
      have hlt : a (n - 1) < b := by
        have h2 := hmin' (n - 1) (by lia : n - 1 < n)
        lia
      have hmin := (ha.2 (n - 1)).2.2
      rw [Nat.sub_add_cancel h1] at hmin
      by_contra hne
      have hblt : b < a n := lt_of_le_of_ne hn fun h => hne ⟨n, h.symm⟩
      obtain ⟨i, hi, hgcdi⟩ := hmin b hlt hblt
      have hgi := hbgcd i
      lia
  -- Key lemma: if a prime `p` divides `a n` but no earlier term, then writing
  -- `a n = p * m` we have `m ≥ 2`, `m` shares a common factor with every earlier term,
  -- and `(p - 1) * m ≤ a (n - 1)` (every multiple `k * m` with `k < p` still meets all
  -- earlier terms, so the greedy minimality of `a n` forces `a (n - 1) ≥ (p - 1) * m`).
  have hnpl : ∀ n : ℕ, 1 ≤ n → ∀ p : ℕ, Nat.Prime p → p ∣ a n →
      (∀ i : ℕ, i < n → ¬ p ∣ a i) →
      ∃ m, a n = p * m ∧ 2 ≤ m ∧ (∀ i : ℕ, i < n → 1 < Nat.gcd m (a i)) ∧
        (p - 1) * m ≤ a (n - 1) := by
    intro n hn p hp hpn hnew
    obtain ⟨m, hm⟩ := hpn
    have hp2 : 2 ≤ p := hp.two_le
    have ha1 : 1 < a n := ha.1 n
    have hm1 : 1 ≤ m := by
      by_contra h
      push Not at h
      have h0 : m = 0 := by lia
      rw [h0, mul_zero] at hm
      lia
    have hm2 : 2 ≤ m := by
      by_contra h
      push Not at h
      have hm_eq : m = 1 := by lia
      rw [hm_eq, mul_one] at hm
      have h0 : (0 : ℕ) < n := by lia
      have hg : 1 < Nat.gcd (a n) (a 0) := hgcd 0 n h0
      rw [hm] at hg
      have hg2 : Nat.gcd p (a 0) ∣ p := Nat.gcd_dvd_left _ _
      rcases (Nat.dvd_prime hp).mp hg2 with h3 | h3
      · lia
      · have hpdiv : p ∣ a 0 := by
          rw [← h3]
          exact Nat.gcd_dvd_right _ _
        exact hnew 0 h0 hpdiv
    have hmgcd : ∀ i : ℕ, i < n → 1 < Nat.gcd m (a i) := by
      intro i hi
      have hg : 1 < Nat.gcd (a n) (a i) := hgcd i n hi
      rw [hm] at hg
      obtain ⟨q, hq, hqdiv⟩ := Nat.exists_prime_and_dvd (by lia : Nat.gcd (p * m) (a i) ≠ 1)
      have hqp : q ∣ p * m := dvd_trans hqdiv (Nat.gcd_dvd_left _ _)
      have hqai : q ∣ a i := dvd_trans hqdiv (Nat.gcd_dvd_right _ _)
      rcases (hq.dvd_mul).mp hqp with h3 | h3
      · have hqeq : q = p := by
          rcases (Nat.dvd_prime hp).mp h3 with h4 | h4
          · exact absurd h4 hq.ne_one
          · exact h4
        rw [hqeq] at hqai
        exact absurd hqai (hnew i hi)
      · have h4 : q ∣ Nat.gcd m (a i) := Nat.dvd_gcd h3 hqai
        have hpos : 0 < Nat.gcd m (a i) := Nat.gcd_pos_of_pos_left _ (by lia : 0 < m)
        exact lt_of_lt_of_le hq.one_lt (Nat.le_of_dvd hpos h4)
    have hfinal : (p - 1) * m ≤ a (n - 1) := by
      by_contra h
      push Not at h
      have hlt2 : (p - 1) * m < a n := by
        have hpm : p * m = (p - 1) * m + m := by
          nth_rewrite 1 [← Nat.sub_add_cancel (show 1 ≤ p by lia)]
          rw [Nat.add_mul, Nat.one_mul]
        lia
      have hmin := (ha.2 (n - 1)).2.2
      rw [Nat.sub_add_cancel hn] at hmin
      obtain ⟨i, hi, hgcdi⟩ := hmin _ h hlt2
      have hdvd : Nat.gcd m (a i) ∣ Nat.gcd ((p - 1) * m) (a i) :=
        Nat.dvd_gcd (dvd_trans (Nat.gcd_dvd_left _ _) (Nat.dvd_mul_left _ _))
          (Nat.gcd_dvd_right _ _)
      rw [hgcdi] at hdvd
      have h6 : Nat.gcd m (a i) = 1 := Nat.dvd_one.mp hdvd
      have h7 := hmgcd i (by lia : i < n)
      lia
    exact ⟨m, hm, hm2, hmgcd, hfinal⟩
  -- **Finiteness of minimal supports.**  Write `S i = (a i).primeFactors`; call index
  -- `i` *minimal* when no actual support is a strict subset of `S i`.  Every prime `p`
  -- occurring in a minimal support either satisfies `p < a 0`, or else a least-radical
  -- minimal support through `p` has cofactor `M` with `∏ q ∈ M, q < a 0`, and some term
  -- support is disjoint from `M`, forcing `p` into that support.  Hence all minimal
  -- supports lie in the finite universe `U` below and cover every term support.
  have hfin : ∃ F : Finset (Finset ℕ),
      (∀ M ∈ F, ∃ j, M = (a j).primeFactors) ∧
      (∀ i, ∃ M ∈ F, M ⊆ (a i).primeFactors) := by
    classical
    have ha0 : 1 < a 0 := ha.1 0
    -- Any two term supports share a prime.
    have hpair : ∀ i j : ℕ, ((a i).primeFactors ∩ (a j).primeFactors).Nonempty := by
      intro i j
      have hne : Nat.gcd (a i) (a j) ≠ 1 := by
        rcases lt_trichotomy i j with h | h | h
        · rw [Nat.gcd_comm]; have hg := hgcd i j h; lia
        · subst h; rw [Nat.gcd_self]; have h1 := ha.1 i; lia
        · have hg := hgcd j i h; lia
      obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
      refine ⟨p, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · exact Nat.mem_primeFactors.mpr
          ⟨hp, hpdvd.trans (Nat.gcd_dvd_left _ _), by have h1 := ha.1 i; lia⟩
      · exact Nat.mem_primeFactors.mpr
          ⟨hp, hpdvd.trans (Nat.gcd_dvd_right _ _), by have h1 := ha.1 j; lia⟩
    -- Prefix enumeration: a prefix-admissible `b < a n` is an earlier term.
    have hPrefix : ∀ n b : ℕ, a 0 ≤ b → b < a n →
        (∀ i : ℕ, i < n → 1 < Nat.gcd b (a i)) → ∃ k : ℕ, k < n ∧ a k = b := by
      intro n b hb0 hbn hbgcd
      have hex : ∃ k, b ≤ a k := ⟨n, hbn.le⟩
      have hbk : b ≤ a (Nat.find hex) := Nat.find_spec hex
      have hkn : Nat.find hex ≤ n := Nat.find_min' hex hbn.le
      have heq : a (Nat.find hex) = b := by
        by_cases hk0 : Nat.find hex = 0
        · rw [hk0] at hbk ⊢; lia
        · have hkpos : 1 ≤ Nat.find hex := by lia
          have hprev : a (Nat.find hex - 1) < b := by
            have hnot := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by lia)
            lia
          by_contra hne
          have hlt : b < a (Nat.find hex) := lt_of_le_of_ne hbk fun h => hne h.symm
          have hmin := (ha.2 (Nat.find hex - 1)).2.2
          rw [Nat.sub_add_cancel hkpos] at hmin
          obtain ⟨i, hi, hcop⟩ := hmin b hprev hlt
          have hig : 1 < Nat.gcd b (a i) := hbgcd i (by lia)
          lia
      refine ⟨Nat.find hex, ?_, heq⟩
      have haklt : a (Nat.find hex) < a n := by lia
      exact (hmono.lt_iff_lt).mp haklt
    -- Every actual support contains a minimal actual support.
    have hminSupport : ∀ i : ℕ, ∃ j, (a j).primeFactors ⊆ (a i).primeFactors ∧
        ∀ k, (a k).primeFactors ⊆ (a j).primeFactors →
          (a j).primeFactors ⊆ (a k).primeFactors := by
      intro i
      let P : ℕ → Prop := fun d => ∃ j, (a j).primeFactors ⊆ (a i).primeFactors ∧
        ((a j).primeFactors).card = d
      have hex : ∃ d, P d := ⟨((a i).primeFactors).card, i, Finset.Subset.rfl, rfl⟩
      obtain ⟨j, hji, hjcard⟩ := Nat.find_spec hex
      refine ⟨j, hji, ?_⟩
      intro k hkj
      have hki : (a k).primeFactors ⊆ (a i).primeFactors := hkj.trans hji
      have hkcard : ((a k).primeFactors).card = Nat.find hex := by
        have hle : ((a k).primeFactors).card ≤ Nat.find hex := by
          rw [← hjcard]
          exact Finset.card_le_card hkj
        have hge : Nat.find hex ≤ ((a k).primeFactors).card := by
          by_contra hlt
          have hlt' : ((a k).primeFactors).card < Nat.find hex := lt_of_not_ge hlt
          exact Nat.find_min hex hlt' ⟨k, hki, rfl⟩
        lia
      have heq : (a k).primeFactors = (a j).primeFactors :=
        Finset.eq_of_subset_of_card_le hkj (by lia)
      exact heq.symm.subset
    -- The finite universe of primes, and a disjoint-support selector.
    let W : Finset ℕ → Finset ℕ := fun M =>
      if h : ∃ k, Disjoint M (a k).primeFactors then (a h.choose).primeFactors else ∅
    let U : Finset ℕ := Finset.range (a 0) ∪ (Finset.range (a 0)).powerset.biUnion W
    -- Every minimal support is contained in `U`.
    have hsubU : ∀ i : ℕ,
        (∀ k, (a k).primeFactors ⊆ (a i).primeFactors →
          (a i).primeFactors ⊆ (a k).primeFactors) →
        (a i).primeFactors ⊆ U := by
      intro i hMini p hp
      by_cases hpsmall : p < a 0
      · exact Finset.mem_union_left _ (Finset.mem_range.mpr hpsmall)
      · have hpbig : a 0 ≤ p := le_of_not_gt hpsmall
        have hpprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
        -- Select a least-radical minimal support containing `p`.
        let P : ℕ → Prop := fun r => ∃ j,
          (∀ k, (a k).primeFactors ⊆ (a j).primeFactors →
            (a j).primeFactors ⊆ (a k).primeFactors) ∧
          p ∈ (a j).primeFactors ∧ (∏ q ∈ (a j).primeFactors, q) = r
        have hex : ∃ r, P r := ⟨∏ q ∈ (a i).primeFactors, q, i, hMini, hp, rfl⟩
        obtain ⟨j, hMinj, hpj, hjprod⟩ := Nat.find_spec hex
        have hleast : ∀ k : ℕ, (∀ l, (a l).primeFactors ⊆ (a k).primeFactors →
              (a k).primeFactors ⊆ (a l).primeFactors) →
            p ∈ (a k).primeFactors →
            (∏ q ∈ (a j).primeFactors, q) ≤ ∏ q ∈ (a k).primeFactors, q := by
          intro k hMink hpk
          have hkP : P (∏ q ∈ (a k).primeFactors, q) := ⟨k, hMink, hpk, rfl⟩
          have hrle : Nat.find hex ≤ ∏ q ∈ (a k).primeFactors, q :=
            Nat.find_min' hex hkP
          lia
        have hprime_j : ∀ q ∈ (a j).primeFactors, q.Prime :=
          fun q hq => (Nat.mem_primeFactors.mp hq).1
        have hMprime : ∀ q ∈ (a j).primeFactors.erase p, q.Prime :=
          fun q hq => hprime_j q (Finset.mem_of_mem_erase hq)
        have hMpos : 0 < ∏ q ∈ (a j).primeFactors.erase p, q :=
          Finset.prod_pos fun q hq => (hMprime q hq).pos
        -- The radical `∏ q ∈ (a j).primeFactors, q` is a term `a n`.
        have hrad_pos : 0 < ∏ q ∈ (a j).primeFactors, q :=
          Finset.prod_pos fun q hq => (hprime_j q hq).pos
        have hrad_ge : a 0 ≤ ∏ q ∈ (a j).primeFactors, q := by
          have hpdvd : p ∣ ∏ q ∈ (a j).primeFactors, q := Finset.dvd_prod_of_mem _ hpj
          have hple : p ≤ ∏ q ∈ (a j).primeFactors, q := Nat.le_of_dvd hrad_pos hpdvd
          lia
        have hrad_gt1 : 1 < ∏ q ∈ (a j).primeFactors, q := by lia
        have hrad_gcd : ∀ l : ℕ, 1 < Nat.gcd (∏ q ∈ (a j).primeFactors, q) (a l) := by
          intro l
          obtain ⟨q, hq⟩ := hpair j l
          obtain ⟨hqj, hql⟩ := Finset.mem_inter.mp hq
          have hqprime := hprime_j q hqj
          have hqdvd1 : q ∣ ∏ r ∈ (a j).primeFactors, r := Finset.dvd_prod_of_mem _ hqj
          have hqdvd2 : q ∣ a l := Nat.dvd_of_mem_primeFactors hql
          have hqdvdg : q ∣ Nat.gcd (∏ r ∈ (a j).primeFactors, r) (a l) :=
            Nat.dvd_gcd hqdvd1 hqdvd2
          have hgpos : 0 < Nat.gcd (∏ r ∈ (a j).primeFactors, r) (a l) :=
            Nat.gcd_pos_of_pos_left _ hrad_pos
          exact hqprime.one_lt.trans_le (Nat.le_of_dvd hgpos hqdvdg)
        obtain ⟨n, hn⟩ := hVenum _ hrad_gt1 hrad_gcd hrad_ge
        -- The cofactor `M = support ∖ {p}` meets every support before index `n`.
        have hMgcd : ∀ l : ℕ, l < n →
            1 < Nat.gcd (∏ q ∈ (a j).primeFactors.erase p, q) (a l) := by
          intro l hl
          by_contra hcon
          have hgcd1 : Nat.gcd (∏ q ∈ (a j).primeFactors.erase p, q) (a l) = 1 := by
            have hpos : 0 < Nat.gcd (∏ q ∈ (a j).primeFactors.erase p, q) (a l) :=
              Nat.gcd_pos_of_pos_right _ (by have h1 := ha.1 l; lia)
            lia
          have hdisj : Disjoint ((a j).primeFactors.erase p) (a l).primeFactors := by
            rw [Finset.disjoint_left]
            intro q hqM hql
            have hqprime := hMprime q hqM
            have hqdvd1 : q ∣ ∏ r ∈ (a j).primeFactors.erase p, r :=
              Finset.dvd_prod_of_mem _ hqM
            have hqdvd2 : q ∣ a l := Nat.dvd_of_mem_primeFactors hql
            have hqdvdg : q ∣ Nat.gcd (∏ r ∈ (a j).primeFactors.erase p, r) (a l) :=
              Nat.dvd_gcd hqdvd1 hqdvd2
            rw [hgcd1] at hqdvdg
            exact hqprime.ne_one (Nat.dvd_one.mp hqdvdg)
          have hpl : p ∈ (a l).primeFactors := by
            obtain ⟨q, hq⟩ := hpair j l
            obtain ⟨hqj, hql⟩ := Finset.mem_inter.mp hq
            by_cases hqp : q = p
            · rw [hqp] at hql; exact hql
            · exfalso
              exact Finset.disjoint_left.mp hdisj (Finset.mem_erase.mpr ⟨hqp, hqj⟩) hql
          obtain ⟨k, hkl, hMink⟩ := hminSupport l
          have hpk : p ∈ (a k).primeFactors := by
            obtain ⟨q, hq⟩ := hpair k j
            obtain ⟨hqk, hqj⟩ := Finset.mem_inter.mp hq
            by_cases hqp : q = p
            · rw [hqp] at hqk; exact hqk
            · exfalso
              have hql : q ∈ (a l).primeFactors := hkl hqk
              exact Finset.disjoint_left.mp hdisj (Finset.mem_erase.mpr ⟨hqp, hqj⟩) hql
          have hle := hleast k hMink hpk
          have hsubdvd : (∏ q ∈ (a k).primeFactors, q) ∣
              ∏ q ∈ (a l).primeFactors, q :=
            Finset.prod_dvd_prod_of_subset _ _ (fun q => q) hkl
          have hkle : (∏ q ∈ (a k).primeFactors, q) ≤ a l :=
            Nat.le_of_dvd (by have h1 := ha.1 l; lia)
              (hsubdvd.trans (Nat.prod_primeFactors_dvd _))
          have hlt : a l < ∏ q ∈ (a j).primeFactors, q := by
            have h1 : a l < a n := (hmono.lt_iff_lt).mpr hl
            rw [hn] at h1
            exact h1
          lia
        -- Hence `∏ q ∈ M, q < a 0`.
        have hMlt : (∏ q ∈ (a j).primeFactors.erase p, q) < a 0 := by
          by_contra hcon
          have hMge : a 0 ≤ ∏ q ∈ (a j).primeFactors.erase p, q := le_of_not_gt hcon
          have hrad_eq : p * (∏ q ∈ (a j).primeFactors.erase p, q) =
              ∏ q ∈ (a j).primeFactors, q :=
            Finset.mul_prod_erase _ (fun q => q) hpj
          have hMn : (∏ q ∈ (a j).primeFactors.erase p, q) < a n := by
            calc ∏ q ∈ (a j).primeFactors.erase p, q
                = 1 * ∏ q ∈ (a j).primeFactors.erase p, q := (Nat.one_mul _).symm
              _ < p * ∏ q ∈ (a j).primeFactors.erase p, q :=
                  Nat.mul_lt_mul_of_pos_right hpprime.one_lt hMpos
              _ = ∏ q ∈ (a j).primeFactors, q := hrad_eq
              _ = a n := hn.symm
          obtain ⟨k, -, hk⟩ := hPrefix n _ hMge hMn hMgcd
          have hsk : (a k).primeFactors = (a j).primeFactors.erase p := by
            rw [hk]
            exact Nat.primeFactors_prod hMprime
          have hsub : (a k).primeFactors ⊆ (a j).primeFactors := by
            rw [hsk]
            exact Finset.erase_subset _ _
          have hpback : p ∈ (a k).primeFactors := hMinj k hsub hpj
          rw [hsk] at hpback
          exact Finset.notMem_erase _ _ hpback
        -- Every element of `M` is `< a 0`.
        have hMrange : (a j).primeFactors.erase p ⊆ Finset.range (a 0) := by
          intro q hq
          have hqdvd : q ∣ ∏ r ∈ (a j).primeFactors.erase p, r :=
            Finset.dvd_prod_of_mem _ hq
          have hqle : q ≤ ∏ r ∈ (a j).primeFactors.erase p, r :=
            Nat.le_of_dvd hMpos hqdvd
          exact Finset.mem_range.mpr (by lia)
        -- Some term support is disjoint from `M`.
        have hexdisj : ∃ k, Disjoint ((a j).primeFactors.erase p) (a k).primeFactors := by
          by_contra hcon
          have hmeet : ∀ l : ℕ, ∃ q ∈ (a j).primeFactors.erase p,
              q ∈ (a l).primeFactors := by
            intro l
            by_contra hnm
            apply hcon
            refine ⟨l, ?_⟩
            rw [Finset.disjoint_left]
            intro q hqM hqS
            exact hnm ⟨q, hqM, hqS⟩
          by_cases hMempty : (a j).primeFactors.erase p = ∅
          · obtain ⟨q, hq, -⟩ := hmeet 0
            rw [hMempty] at hq
            exact Finset.notMem_empty _ hq
          · have hMne : ((a j).primeFactors.erase p).Nonempty :=
              Finset.nonempty_iff_ne_empty.mpr hMempty
            have hMprod2 : 2 ≤ ∏ q ∈ (a j).primeFactors.erase p, q := by
              obtain ⟨q, hq⟩ := hMne
              have hrest : 0 < ∏ r ∈ ((a j).primeFactors.erase p).erase q, r :=
                Finset.prod_pos fun r hr =>
                  (hMprime r (Finset.mem_of_mem_erase hr)).pos
              calc 2 ≤ q := (hMprime q hq).two_le
                _ ≤ q * ∏ r ∈ ((a j).primeFactors.erase p).erase q, r :=
                    Nat.le_mul_of_pos_right q hrest
                _ = ∏ r ∈ (a j).primeFactors.erase p, r :=
                    Finset.mul_prod_erase _ (fun r => r) hq
            -- The power `(∏ q ∈ M, q) ^ (a 0)` is a term whose support is exactly `M`.
            have hbge : a 0 ≤ (∏ q ∈ (a j).primeFactors.erase p, q) ^ a 0 := by
              calc a 0 = 1 * a 0 := by simp
                _ ≤ (∏ q ∈ (a j).primeFactors.erase p, q) * a 0 :=
                    Nat.mul_le_mul_right _ (by lia)
                _ ≤ (∏ q ∈ (a j).primeFactors.erase p, q) ^ a 0 :=
                    Nat.mul_le_pow (by lia) _
            have hbgt1 : 1 < (∏ q ∈ (a j).primeFactors.erase p, q) ^ a 0 := by lia
            have hbgcd : ∀ l : ℕ, 1 < Nat.gcd
                ((∏ q ∈ (a j).primeFactors.erase p, q) ^ a 0) (a l) := by
              intro l
              obtain ⟨q, hqM, hql⟩ := hmeet l
              have hqprime := hMprime q hqM
              have hqdvd1 : q ∣ (∏ r ∈ (a j).primeFactors.erase p, r) ^ a 0 :=
                (Finset.dvd_prod_of_mem _ hqM).trans (dvd_pow_self _ (by lia))
              have hqdvd2 : q ∣ a l := Nat.dvd_of_mem_primeFactors hql
              have hqdvdg : q ∣ Nat.gcd ((∏ r ∈ (a j).primeFactors.erase p, r) ^ a 0)
                  (a l) := Nat.dvd_gcd hqdvd1 hqdvd2
              have hbpos : 0 < (∏ r ∈ (a j).primeFactors.erase p, r) ^ a 0 :=
                pow_pos (by lia) _
              have hgpos : 0 < Nat.gcd ((∏ r ∈ (a j).primeFactors.erase p, r) ^ a 0)
                  (a l) := Nat.gcd_pos_of_pos_left _ hbpos
              exact hqprime.one_lt.trans_le (Nat.le_of_dvd hgpos hqdvdg)
            obtain ⟨m, hm⟩ := hVenum _ hbgt1 hbgcd hbge
            have hsm : (a m).primeFactors = (a j).primeFactors.erase p := by
              rw [hm, Nat.primeFactors_pow _ (by lia : a 0 ≠ 0)]
              exact Nat.primeFactors_prod hMprime
            have hsub : (a m).primeFactors ⊆ (a j).primeFactors := by
              rw [hsm]
              exact Finset.erase_subset _ _
            have hpback : p ∈ (a m).primeFactors := hMinj m hsub hpj
            rw [hsm] at hpback
            exact Finset.notMem_erase _ _ hpback
        -- Conclude `p ∈ U` via the disjoint support `W M`.
        have hMem : (a j).primeFactors.erase p ∈ (Finset.range (a 0)).powerset :=
          Finset.mem_powerset.mpr hMrange
        have hWmem : p ∈ W ((a j).primeFactors.erase p) := by
          show p ∈ if h : ∃ k, Disjoint ((a j).primeFactors.erase p) (a k).primeFactors
            then (a h.choose).primeFactors else ∅
          rw [dite_eq_left hexdisj]
          obtain ⟨q, hq⟩ := hpair j hexdisj.choose
          obtain ⟨hqj, hqk⟩ := Finset.mem_inter.mp hq
          by_cases hqp : q = p
          · rw [hqp] at hqk; exact hqk
          · exfalso
            exact Finset.disjoint_left.mp hexdisj.choose_spec
              (Finset.mem_erase.mpr ⟨hqp, hqj⟩) hqk
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨(a j).primeFactors.erase p, hMem, hWmem⟩)
    -- The requested finite family: the minimal supports, all contained in `U`.
    refine ⟨U.powerset.filter (fun R => ∃ i, R = (a i).primeFactors ∧
      ∀ k, (a k).primeFactors ⊆ (a i).primeFactors →
        (a i).primeFactors ⊆ (a k).primeFactors), ?_, ?_⟩
    · intro M hM
      obtain ⟨-, i, rfl, -⟩ := Finset.mem_filter.mp hM
      exact ⟨i, rfl⟩
    · intro i
      obtain ⟨j, hji, hMinj⟩ := hminSupport i
      exact ⟨(a j).primeFactors,
        Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr (hsubU j hMinj), j, rfl, hMinj⟩, hji⟩
  obtain ⟨F, hFreal, hFcover⟩ := hfin
  -- Step A: from the finiteness, the gcd-condition defining `V` is periodic with
  -- period `L = ∏ M ∈ F, ∏ p ∈ M, p`.
  obtain ⟨L, hLpos, hper⟩ : ∃ L : ℕ, 0 < L ∧
      ∀ b : ℕ, (∀ i, 1 < Nat.gcd b (a i)) ↔ (∀ i, 1 < Nat.gcd (b + L) (a i)) := by
    refine ⟨∏ M ∈ F, ∏ p ∈ M, p, ?_, ?_⟩
    · apply Finset.prod_pos
      intro M hM
      apply Finset.prod_pos
      intro p hp
      obtain ⟨j, rfl⟩ := hFreal M hM
      exact (Nat.mem_primeFactors.mp hp).1.pos
    · -- The gcd-condition is equivalent to "`b` meets every `M ∈ F`".
      have hkey : ∀ c : ℕ, (∀ i, 1 < Nat.gcd c (a i)) ↔
          (∀ M ∈ F, ∃ p ∈ M, p ∣ c) := by
        intro c
        constructor
        · intro hc M hM
          obtain ⟨j, rfl⟩ := hFreal M hM
          have hg := hc j
          have haj := (haV j).1
          obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd (by lia : Nat.gcd c (a j) ≠ 1)
          exact ⟨q, Nat.mem_primeFactors.mpr ⟨hq, dvd_trans hqdvd (Nat.gcd_dvd_right _ _),
            by lia⟩, dvd_trans hqdvd (Nat.gcd_dvd_left _ _)⟩
        · intro hc i
          obtain ⟨M, hMF, hMsub⟩ := hFcover i
          obtain ⟨p, hpM, hpc⟩ := hc M hMF
          have hp' := Nat.mem_primeFactors.mp (hMsub hpM)
          have hpdvd : p ∣ Nat.gcd c (a i) := Nat.dvd_gcd hpc hp'.2.1
          have hpos : 0 < Nat.gcd c (a i) :=
            Nat.gcd_pos_of_pos_right _ (by have := (haV i).1; lia)
          exact lt_of_lt_of_le hp'.1.one_lt (Nat.le_of_dvd hpos hpdvd)
      -- Both sides only depend on divisibility by primes dividing `L`.
      have hshift : ∀ c : ℕ, (∀ M ∈ F, ∃ p ∈ M, p ∣ c) →
          (∀ M ∈ F, ∃ p ∈ M, p ∣ c + ∏ M ∈ F, ∏ p ∈ M, p) := by
        intro c hc M hM
        obtain ⟨p, hpM, hpc⟩ := hc M hM
        refine ⟨p, hpM, dvd_add hpc ?_⟩
        exact dvd_trans (Finset.dvd_prod_of_mem _ hpM) (Finset.dvd_prod_of_mem _ hM)
      have hshift' : ∀ c : ℕ, (∀ M ∈ F, ∃ p ∈ M, p ∣ c + ∏ M ∈ F, ∏ p ∈ M, p) →
          (∀ M ∈ F, ∃ p ∈ M, p ∣ c) := by
        intro c hc M hM
        obtain ⟨p, hpM, hpc⟩ := hc M hM
        have hpL : p ∣ ∏ M ∈ F, ∏ p ∈ M, p :=
          dvd_trans (Finset.dvd_prod_of_mem _ hpM) (Finset.dvd_prod_of_mem _ hM)
        exact ⟨p, hpM, (Nat.dvd_add_iff_left hpL).mpr hpc⟩
      intro b
      rw [hkey b, hkey (b + _)]
      exact ⟨hshift b, hshift' b⟩
  -- Step B: `a 0 + L` is itself a term, say `a T₀`; then shifting by `L` commutes with
  -- the enumeration, giving `a (n + T₀) = a n + L` for all `n`.
  obtain ⟨T₀, hT₀⟩ := hVenum (a 0 + L) (by have h1 := (haV 0).1; lia)
      ((hper (a 0)).mp (haV 0).2) (by lia)
  have hT₀pos : 0 < T₀ := by
    rcases Nat.eq_zero_or_pos T₀ with h | h
    · exfalso
      rw [h] at hT₀
      lia
    · exact h
  have hmain : ∀ n : ℕ, a (n + T₀) = a n + L := by
    intro n
    induction n with
    | zero =>
      rw [Nat.zero_add]
      exact hT₀
    | succ n ih =>
      -- Forward: `a (n+1) + L` is a term, so it is at least the next term after
      -- `a (n + T₀) = a n + L`.
      have h1 : 1 < a (n + 1) + L := by have := (haV (n + 1)).1; lia
      have h2 : ∀ i, 1 < Nat.gcd (a (n + 1) + L) (a i) := (hper (a (n + 1))).mp (haV (n + 1)).2
      have h3 : a 0 ≤ a (n + 1) + L := by have := hge (n + 1); lia
      obtain ⟨k, hk⟩ := hVenum _ h1 h2 h3
      have hlt1 : a (n + T₀) < a k := by
        rw [hk, ih]
        have h := (ha.2 n).1
        lia
      have hkg : n + T₀ + 1 ≤ k := by
        have h := (hmono.lt_iff_lt).mp hlt1
        lia
      have hle1 : a (n + T₀ + 1) ≤ a (n + 1) + L := by
        have h := hmono.monotone hkg
        rw [hk] at h
        exact h
      -- Backward: `a (n + T₀ + 1) - L` is a term strictly above `a n`.
      have hy : a n + L < a (n + T₀ + 1) := by
        have h : a (n + T₀) < a (n + T₀ + 1) := hmono (by lia)
        lia
      have hLle : L ≤ a (n + T₀ + 1) := by lia
      have h1' : 1 < a (n + T₀ + 1) - L := by
        have h0 := (haV 0).1
        have hn := hge n
        lia
      have h2' : ∀ i, 1 < Nat.gcd (a (n + T₀ + 1) - L) (a i) := by
        apply (hper (a (n + T₀ + 1) - L)).mpr
        rw [Nat.sub_add_cancel hLle]
        exact (haV (n + T₀ + 1)).2
      have h3' : a 0 ≤ a (n + T₀ + 1) - L := by
        have hn := hge n
        lia
      obtain ⟨m, hm⟩ := hVenum _ h1' h2' h3'
      have hmg : n + 1 ≤ m := by
        have hlt2 : a n < a m := by
          rw [hm]
          lia
        have h := (hmono.lt_iff_lt).mp hlt2
        lia
      have hle2 : a (n + 1) + L ≤ a (n + T₀ + 1) := by
        have h := hmono.monotone hmg
        rw [hm] at h
        lia
      have heq : a (n + T₀ + 1) = a (n + 1) + L := le_antisymm hle1 hle2
      rw [show n + 1 + T₀ = n + T₀ + 1 by lia]
      exact heq
  exact ⟨T₀, L, hT₀pos, hLpos, hmain⟩

end Imo2026P6
