/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Finset.NatDivisors
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Int.Star
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
  omega

/-- If `2 ≤ a` and `a ∣ b`, then `a` and `b` are not coprime. -/
lemma R_of_dvd {a b : ℕ} (ha : 2 ≤ a) (hb : a ∣ b) : R a b :=
  R_of_dvd_of_dvd ha dvd_rfl hb

/-- `R` transfers along divisibility on the left. -/
lemma R_of_dvd_left {a b c : ℕ} (h : R a b) (hac : a ∣ c) : R c b :=
  fun hc => h (hc.coprime_dvd_left hac)

/-- `R` transfers along divisibility on the right. -/
lemma R_of_dvd_right {a b c : ℕ} (h : R a b) (hbc : b ∣ c) : R a c :=
  fun hc => h (hc.coprime_dvd_right hbc)

/-- `R` is symmetric. -/
lemma R_symm {a b : ℕ} (h : R a b) : R b a := fun hc => h hc.symm

/-- Appending two chains gives a chain when the boundary elements are related. -/
lemma isChain_append {α : Type*} {R' : α → α → Prop} : ∀ (l₁ l₂ : List α),
    l₁.IsChain R' → l₂.IsChain R' →
    (∀ a ∈ l₁.getLast?, ∀ b ∈ l₂.head?, R' a b) → (l₁ ++ l₂).IsChain R'
  | [], l₂, _, h₂, _ => by simpa using h₂
  | [a], [], _, _, _ => by simp [List.IsChain.singleton]
  | [a], b :: t, _, h₂, h => .cons_cons (h a (by simp) b (by simp)) h₂
  | a :: b :: s, l₂, h₁, h₂, h =>
      .cons_cons (List.isChain_cons_cons.mp h₁).1
        (isChain_append (b :: s) l₂ (List.isChain_cons_cons.mp h₁).2 h₂ (by simpa using h))

/-- A list whose elements are all divisible by some `r ≥ 2` is an `R`-chain. -/
lemma isChain_of_forall_dvd {r : ℕ} (hr : 2 ≤ r) :
    ∀ {l : List ℕ}, (∀ x ∈ l, r ∣ x) → l.IsChain R
  | [], _ => .nil
  | [a], _ => .singleton a
  | a :: b :: t, h =>
      .cons_cons (R_of_dvd_of_dvd hr (h a (by simp)) (h b (by simp)))
        (isChain_of_forall_dvd hr (fun x hx => h x (by simp [hx])))

/-- The list `[d, d*q, d*q^2, ..., d*q^e]`. -/
def powChain (d q : ℕ) : ℕ → List ℕ
  | 0 => [d]
  | e + 1 => powChain d q e ++ [d * q ^ (e + 1)]

lemma powChain_ne_nil (d q e : ℕ) : powChain d q e ≠ [] := by
  induction e with
  | zero => simp [powChain]
  | succ e ih => simp [powChain, ih]

@[simp] lemma mem_powChain {d q e x : ℕ} :
    x ∈ powChain d q e ↔ ∃ j ≤ e, x = d * q ^ j := by
  induction e with
  | zero => simp [powChain]
  | succ e ih =>
    simp only [powChain, List.mem_append, List.mem_singleton, ih]
    constructor
    · rintro (⟨j, hj, rfl⟩ | rfl)
      · exact ⟨j, le_trans hj (Nat.le_succ e), rfl⟩
      · exact ⟨e + 1, le_refl _, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      rcases eq_or_lt_of_le hj with rfl | hj
      · exact Or.inr rfl
      · exact Or.inl ⟨j, Nat.lt_succ_iff.mp hj, rfl⟩

@[simp] lemma head?_powChain (d q e : ℕ) : (powChain d q e).head? = some d := by
  induction e with
  | zero => simp [powChain]
  | succ e ih => rw [powChain, List.head?_append, ih]; rfl

@[simp] lemma getLast?_powChain (d q e : ℕ) :
    (powChain d q e).getLast? = some (d * q ^ e) := by
  induction e with
  | zero => simp [powChain]
  | succ e ih => rw [powChain, List.getLast?_append]; simp

lemma isChain_powChain {d q : ℕ} (hd : 2 ≤ d) (e : ℕ) : (powChain d q e).IsChain R := by
  induction e with
  | zero => exact .singleton d
  | succ e ih =>
    rw [powChain]
    exact isChain_append _ _ ih (.singleton _)
      (fun a ha b hb => by
        simp only [getLast?_powChain, Option.mem_def, Option.some.injEq] at ha
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
        subst ha; subst hb
        exact R_of_dvd_of_dvd hd (dvd_mul_right d _) (dvd_mul_right d _))

lemma nodup_powChain {d q : ℕ} (hd : 1 ≤ d) (hq : 2 ≤ q) (e : ℕ) :
    (powChain d q e).Nodup := by
  have key : ∀ j j' : ℕ, d * q ^ j = d * q ^ j' → j = j' := by
    intro j j' h
    have h' : q ^ j = q ^ j' := Nat.mul_left_cancel (by omega) h
    exact Nat.pow_right_injective hq h'
  induction e with
  | zero => simp [powChain]
  | succ e ih =>
    rw [powChain, List.nodup_append]
    refine ⟨ih, by simp, ?_⟩
    intro x hx
    rw [mem_powChain] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    intro b hb
    rw [List.eq_of_mem_singleton hb]
    intro h
    exact absurd (key _ _ h) (by omega)

/-- If `d * q^j = d' * q^j'` with `d, d'` dividing `m` and `q ∤ m` prime,
then `d = d'` and `j = j'`. -/
lemma eq_of_mul_pow_eq {m q : ℕ} (hq : q.Prime) (hqm : ¬ q ∣ m)
    {d d' j j' : ℕ} (hd : d ∣ m) (hd' : d' ∣ m) (hd0 : d ≠ 0) (hd'0 : d' ≠ 0)
    (h : d * q ^ j = d' * q ^ j') : d = d' ∧ j = j' := by
  have hqd : d.factorization q = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (fun h1 => hqm (dvd_trans h1 hd))
  have hqd' : d'.factorization q = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (fun h1 => hqm (dvd_trans h1 hd'))
  have hjp : q ^ j ≠ 0 := pow_ne_zero _ hq.ne_zero
  have hjp' : q ^ j' ≠ 0 := pow_ne_zero _ hq.ne_zero
  have hj : j = j' := by
    have h1 := congrArg (fun x => x.factorization q) h
    rw [Nat.factorization_mul hd0 hjp, Nat.factorization_mul hd'0 hjp'] at h1
    rw [hq.factorization_pow, hq.factorization_pow] at h1
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, hqd, hqd', zero_add] at h1
    exact h1
  subst hj
  exact ⟨Nat.mul_right_cancel (pow_pos hq.pos j) h, rfl⟩

/-- Chains, heads and lasts of `flatMap (powChain · q e)` over a chain `l`. -/
lemma isChain_flatMap_powChain {q e : ℕ} :
    ∀ {l : List ℕ}, l.IsChain R → (∀ x ∈ l, 2 ≤ x) →
      (l.flatMap (fun d => powChain d q e)).IsChain R ∧
      ((l.flatMap (fun d => powChain d q e)).head? = l.head?) ∧
      ((l.flatMap (fun d => powChain d q e)).getLast? =
        (l.getLast?).map (fun d => d * q ^ e))
  | [], _, _ => by simp
  | [d], _, h2 =>
      ⟨by simpa using isChain_powChain (h2 d (by simp)) e, by simp, by simp⟩
  | d₁ :: d₂ :: t, hchain, h2 => by
    have hd₁ : 2 ≤ d₁ := h2 d₁ (by simp)
    have hchain' : (d₂ :: t).IsChain R := hchain.of_cons
    have hR : R d₁ d₂ := (List.isChain_cons_cons.mp hchain).1
    obtain ⟨ih_chain, ih_head, ih_last⟩ :=
      isChain_flatMap_powChain hchain' (fun x hx => h2 x (by simp [hx]))
    rw [List.flatMap_cons]
    refine ⟨?_, ?_, ?_⟩
    · exact isChain_append _ _ (isChain_powChain hd₁ e) ih_chain (fun a ha b hb => by
        rw [getLast?_powChain, Option.mem_def, Option.some.injEq] at ha
        rw [ih_head, List.head?_cons, Option.mem_def, Option.some.injEq] at hb
        subst ha; subst hb
        exact R_of_dvd_left hR (dvd_mul_right d₁ _))
    · rw [List.head?_append, head?_powChain]; rfl
    · rw [List.getLast?_append, ih_last]
      have hne : (d₂ :: t).getLast? ≠ none := by cases t <;> simp
      rw [List.getLast?_cons_cons]
      cases hgl : (d₂ :: t).getLast? with
      | none => exact absurd hgl hne
      | some v => simp

/-- **Key construction step**: if the divisors `> 1` of `m` admit a good
circle and `q` is a prime not dividing `m`, then for any `e ≥ 1` the divisors
`> 1` of `m * q^e` admit a good circle. -/
lemma goodCircle_mul_prime_pow {m q : ℕ} (hq : q.Prime) (hqm : ¬ q ∣ m)
    {l : List ℕ} (hnodup : l.Nodup) (hl2 : 2 ≤ l.length)
    (hmem : ∀ d : ℕ, d ∈ l ↔ d ∣ m ∧ 1 < d)
    (hchain : l.IsChain R)
    (hwrap : ∀ a ∈ l.getLast?, ∀ b ∈ l.head?, R a b)
    (e : ℕ) (he : 1 ≤ e) : GoodCircle (m * q ^ e) := by
  have hlne : l ≠ [] := by rintro rfl; simp at hl2
  obtain ⟨d₁, rest, rfl⟩ := List.ne_nil_iff_exists_cons.mp hlne
  have hrest : rest ≠ [] := by rintro rfl; simp at hl2
  obtain ⟨d₂, mid, rfl⟩ := List.ne_nil_iff_exists_cons.mp hrest
  -- basic facts about the pieces of `l`
  have hd₁ : d₁ ∈ d₁ :: d₂ :: mid := by simp
  have hd₂ : d₂ ∈ d₁ :: d₂ :: mid := by simp
  obtain ⟨hd₁m, hd₁1⟩ := (hmem d₁).mp hd₁
  obtain ⟨hd₂m, hd₂1⟩ := (hmem d₂).mp hd₂
  have hd₁2 : 2 ≤ d₁ := hd₁1
  have hd₂2 : 2 ≤ d₂ := hd₂1
  have hd₂q : 2 ≤ d₂ * q := by nlinarith [hd₂2, hq.two_le]
  have hmid_mem : ∀ x ∈ mid, x ∈ d₁ :: d₂ :: mid := fun x hx => by simp [hx]
  have hmid2 : ∀ x ∈ mid, 2 ≤ x := fun x hx => ((hmem x).mp (hmid_mem x hx)).2
  have hmidm : ∀ x ∈ mid, x ∣ m := fun x hx => ((hmem x).mp (hmid_mem x hx)).1
  have hchain_rest : (d₂ :: mid).IsChain R := hchain.of_cons
  have hchain_mid : mid.IsChain R := hchain_rest.of_cons
  obtain ⟨hd₁_notin, hnodup'⟩ := List.nodup_cons.mp hnodup
  obtain ⟨hd₂_notin, hnodup_mid⟩ := List.nodup_cons.mp hnodup'
  have hd₁_ne_d₂ : d₁ ≠ d₂ := fun h => hd₁_notin (h ▸ by simp)
  have hd₁_notin_mid : d₁ ∉ mid := fun h => hd₁_notin (by simp [h])
  have hwrap' : ∀ a ∈ (d₂ :: mid).getLast?, R a d₁ := by
    intro a ha
    apply hwrap a _ d₁ (by simp)
    rwa [List.getLast?_cons_cons]
  obtain ⟨hFchain, hFhead, hFlast⟩ := isChain_flatMap_powChain hchain_mid hmid2
  -- boundaries between consecutive blocks of the new circle
  have hb1 : ∀ a ∈ ([d₂]).getLast?, ∀ b ∈ (mid.flatMap (fun d => powChain d q e) ++
      (powChain d₁ q e ++ (powChain q q (e - 1) ++ powChain (d₂ * q) q (e - 1)))).head?,
      R a b := by
    intro a ha b hb
    simp at ha; subst ha
    rw [List.head?_append, hFhead] at hb
    cases mid with
    | nil =>
      rw [List.head?_append, head?_powChain] at hb
      simp at hb; subst hb
      apply hwrap'; simp [List.getLast?_cons]
    | cons d₃ t =>
      simp at hb; subst hb
      exact (List.isChain_cons_cons.mp hchain_rest).1
  have hb2 : ∀ a ∈ (mid.flatMap (fun d => powChain d q e)).getLast?,
      ∀ b ∈ (powChain d₁ q e ++ (powChain q q (e - 1) ++ powChain (d₂ * q) q (e - 1))).head?,
      R a b := by
    intro a ha b hb
    rw [List.head?_append, head?_powChain] at hb
    simp at hb; subst hb
    rw [hFlast] at ha
    cases hgm : mid.getLast? with
    | none => rw [hgm] at ha; simp at ha
    | some dm =>
      rw [hgm] at ha; simp at ha; subst ha
      apply R_of_dvd_left _ (dvd_mul_right dm _)
      apply hwrap'
      cases mid with
      | nil => simp at hgm
      | cons b t => rwa [List.getLast?_cons_cons]
  have hb3 : ∀ a ∈ (powChain d₁ q e).getLast?,
      ∀ b ∈ (powChain q q (e - 1) ++ powChain (d₂ * q) q (e - 1)).head?, R a b := by
    intro a ha b hb
    rw [getLast?_powChain] at ha; simp at ha; subst ha
    rw [List.head?_append, head?_powChain] at hb; simp at hb; subst hb
    exact R_of_dvd_of_dvd hq.two_le
      (dvd_mul_of_dvd_right (dvd_pow_self q (by omega)) d₁) dvd_rfl
  have hb4 : ∀ a ∈ (powChain q q (e - 1)).getLast?,
      ∀ b ∈ (powChain (d₂ * q) q (e - 1)).head?, R a b := by
    intro a ha b hb
    rw [getLast?_powChain, Option.mem_def, Option.some.injEq] at ha
    rw [head?_powChain, Option.mem_def, Option.some.injEq] at hb
    subst ha; subst hb
    exact R_of_dvd_of_dvd hq.two_le (dvd_mul_right q _)
      (mul_comm q d₂ ▸ dvd_mul_right q d₂)
  refine ⟨d₂ :: (mid.flatMap (fun d => powChain d q e) ++ (powChain d₁ q e ++
      (powChain q q (e - 1) ++ powChain (d₂ * q) q (e - 1)))), ?_, ?_, ?_, ?_, ?_⟩
  · -- nodup
    have hnq : 1 ≤ q := hq.one_lt.le
    have hFnodup : (mid.flatMap (fun d => powChain d q e)).Nodup := by
      rw [List.nodup_flatMap]
      refine ⟨fun d hd => nodup_powChain (by have := hmid2 d hd; omega) hq.two_le e, ?_⟩
      apply hnodup_mid.pairwise_of_forall_ne
      intro d hd d' hd' hne x hx
      rw [mem_powChain] at hx
      obtain ⟨j, hj, rfl⟩ := hx
      intro hb
      rw [mem_powChain] at hb
      obtain ⟨j', hj', hbj⟩ := hb
      obtain ⟨h1, -⟩ := eq_of_mul_pow_eq hq hqm (hmidm d hd) (hmidm d' hd')
        (by have := hmid2 d hd; omega) (by have := hmid2 d' hd'; omega) hbj
      exact hne h1
    have hAnodup : (powChain d₁ q e).Nodup :=
      nodup_powChain (by omega) hq.two_le e
    have hBnodup : (powChain q q (e - 1)).Nodup :=
      nodup_powChain hnq hq.two_le (e - 1)
    have hCnodup : (powChain (d₂ * q) q (e - 1)).Nodup :=
      nodup_powChain (by omega) hq.two_le (e - 1)
    rw [List.nodup_cons]
    refine ⟨?_, ?_⟩
    · -- `d₂` is not in the other blocks
      intro hy
      simp only [List.mem_append] at hy
      rcases hy with hy | hy | hy | hy
      · rw [List.mem_flatMap] at hy
        obtain ⟨d, hd, hdy⟩ := hy
        rw [mem_powChain] at hdy
        obtain ⟨j, hj, hdy⟩ := hdy
        have h2 : d₂ * q ^ 0 = d * q ^ j := by simpa using hdy
        obtain ⟨h3, -⟩ := eq_of_mul_pow_eq hq hqm hd₂m (hmidm d hd)
          (by omega) (by have := hmid2 d hd; omega) h2
        exact hd₂_notin (h3 ▸ hd)
      · rw [mem_powChain] at hy
        obtain ⟨j, hj, hdy⟩ := hy
        have h2 : d₂ * q ^ 0 = d₁ * q ^ j := by simpa using hdy
        obtain ⟨h3, -⟩ := eq_of_mul_pow_eq hq hqm hd₂m hd₁m (by omega) (by omega) h2
        exact hd₁_ne_d₂ h3.symm
      · rw [mem_powChain] at hy
        obtain ⟨j, hj, hdy⟩ := hy
        have e1 : (1 : ℕ) * q ^ (j + 1) = q * q ^ j := by rw [one_mul, pow_succ']
        have h2 : d₂ * q ^ 0 = 1 * q ^ (j + 1) := by
          rw [pow_zero, mul_one, e1]; exact hdy
        obtain ⟨h3, -⟩ := eq_of_mul_pow_eq hq hqm hd₂m (one_dvd m) (by omega)
          one_ne_zero h2
        omega
      · rw [mem_powChain] at hy
        obtain ⟨j, hj, hdy⟩ := hy
        have e2 : d₂ * q ^ (j + 1) = d₂ * q * q ^ j := by rw [pow_succ', mul_assoc]
        have h2 : d₂ * q ^ 0 = d₂ * q ^ (j + 1) := by
          rw [pow_zero, mul_one, e2]; exact hdy
        obtain ⟨-, h3⟩ := eq_of_mul_pow_eq hq hqm hd₂m hd₂m (by omega) (by omega) h2
        omega
    · rw [List.nodup_append]
      refine ⟨hFnodup, ?_, ?_⟩
      · rw [List.nodup_append]
        refine ⟨hAnodup, ?_, ?_⟩
        · rw [List.nodup_append]
          refine ⟨hBnodup, hCnodup, ?_⟩
          intro x hx y hy
          rw [mem_powChain] at hx
          obtain ⟨j, hj, hdx⟩ := hx
          rw [mem_powChain] at hy
          obtain ⟨i, hi, hdy⟩ := hy
          intro h
          have e1 : (1 : ℕ) * q ^ (j + 1) = q * q ^ j := by rw [one_mul, pow_succ']
          have e2 : d₂ * q ^ (i + 1) = d₂ * q * q ^ i := by rw [pow_succ', mul_assoc]
          obtain ⟨h3, -⟩ := eq_of_mul_pow_eq hq hqm (one_dvd m) hd₂m one_ne_zero
            (by omega) (e1.trans (hdx.symm.trans (h.trans (hdy.trans e2.symm))))
          omega
        · intro x hx y hy
          rw [mem_powChain] at hx
          obtain ⟨j, hj, hdx⟩ := hx
          simp only [List.mem_append] at hy
          rcases hy with hy | hy
          · rw [mem_powChain] at hy
            obtain ⟨i, hi, hdy⟩ := hy
            intro h
            have e1 : (1 : ℕ) * q ^ (i + 1) = q * q ^ i := by rw [one_mul, pow_succ']
            obtain ⟨h3, -⟩ := eq_of_mul_pow_eq hq hqm hd₁m (one_dvd m) (by omega)
              one_ne_zero ((hdx.symm.trans (h.trans hdy)).trans e1.symm)
            omega
          · rw [mem_powChain] at hy
            obtain ⟨i, hi, hdy⟩ := hy
            intro h
            have e2 : d₂ * q ^ (i + 1) = d₂ * q * q ^ i := by rw [pow_succ', mul_assoc]
            obtain ⟨h3, -⟩ := eq_of_mul_pow_eq hq hqm hd₁m hd₂m (by omega) (by omega)
              ((hdx.symm.trans (h.trans hdy)).trans e2.symm)
            exact hd₁_ne_d₂ h3
      · intro x hx y hy
        rw [List.mem_flatMap] at hx
        obtain ⟨d, hd, hdx⟩ := hx
        rw [mem_powChain] at hdx
        obtain ⟨j, hj, hdx⟩ := hdx
        simp only [List.mem_append] at hy
        rcases hy with hy | hy | hy
        · rw [mem_powChain] at hy
          obtain ⟨i, hi, hdy⟩ := hy
          intro h
          obtain ⟨h3, -⟩ := eq_of_mul_pow_eq hq hqm (hmidm d hd) hd₁m
            (by have := hmid2 d hd; omega) (by omega) (hdx.symm.trans (h.trans hdy))
          exact hd₁_notin_mid (h3 ▸ hd)
        · rw [mem_powChain] at hy
          obtain ⟨i, hi, hdy⟩ := hy
          intro h
          have e1 : (1 : ℕ) * q ^ (i + 1) = q * q ^ i := by rw [one_mul, pow_succ']
          obtain ⟨h3, -⟩ := eq_of_mul_pow_eq hq hqm (hmidm d hd) (one_dvd m)
            (by have := hmid2 d hd; omega) one_ne_zero
            ((hdx.symm.trans (h.trans hdy)).trans e1.symm)
          have := hmid2 d hd; omega
        · rw [mem_powChain] at hy
          obtain ⟨i, hi, hdy⟩ := hy
          intro h
          have e2 : d₂ * q ^ (i + 1) = d₂ * q * q ^ i := by rw [pow_succ', mul_assoc]
          obtain ⟨h3, -⟩ := eq_of_mul_pow_eq hq hqm (hmidm d hd) hd₂m
            (by have := hmid2 d hd; omega) (by omega)
            ((hdx.symm.trans (h.trans hdy)).trans e2.symm)
          exact hd₂_notin (h3.symm ▸ hd)
  · -- nonempty
    simp
  · -- membership
    intro x
    simp only [List.mem_cons, List.mem_append]
    constructor
    · rintro (rfl | hF | hA | hB | hC)
      · exact ⟨dvd_trans hd₂m (dvd_mul_right m _), hd₂1⟩
      · rw [List.mem_flatMap] at hF
        obtain ⟨d, hd, hdx⟩ := hF
        rw [mem_powChain] at hdx
        obtain ⟨j, hj, rfl⟩ := hdx
        exact ⟨Nat.mul_dvd_mul (hmidm d hd) (pow_dvd_pow q hj),
          lt_of_lt_of_le (hmid2 d hd) (Nat.le_mul_of_pos_right _ (pow_pos hq.pos j))⟩
      · rw [mem_powChain] at hA
        obtain ⟨j, hj, rfl⟩ := hA
        exact ⟨Nat.mul_dvd_mul hd₁m (pow_dvd_pow q hj),
          lt_of_lt_of_le hd₁2 (Nat.le_mul_of_pos_right _ (pow_pos hq.pos j))⟩
      · rw [mem_powChain] at hB
        obtain ⟨j, hj, rfl⟩ := hB
        have h1 : q * q ^ j = q ^ (j + 1) := (pow_succ' q j).symm
        have h2 : q ^ (j + 1) ∣ q ^ e := pow_dvd_pow q (by omega)
        exact ⟨h1 ▸ (mul_comm (q ^ e) m ▸ dvd_trans h2 (dvd_mul_right (q ^ e) m)),
          lt_of_lt_of_le hq.one_lt (Nat.le_mul_of_pos_right _ (pow_pos hq.pos j))⟩
      · rw [mem_powChain] at hC
        obtain ⟨j, hj, rfl⟩ := hC
        have h1 : d₂ * q * q ^ j = d₂ * q ^ (j + 1) := by rw [mul_assoc, pow_succ']
        have h2 : q ^ (j + 1) ∣ q ^ e := pow_dvd_pow q (by omega)
        exact ⟨h1 ▸ Nat.mul_dvd_mul hd₂m h2,
          lt_of_lt_of_le hd₂q (Nat.le_mul_of_pos_right _ (pow_pos hq.pos j))⟩
    · rintro ⟨hxdvd, hx1⟩
      have hx0 : x ≠ 0 := by omega
      have hdecomp : ∃ j d : ℕ, q ^ j * d = x ∧ d ≠ 0 ∧ ¬ q ∣ d :=
        ⟨x.factorization q, ordCompl[q] x, Nat.ordProj_mul_ordCompl_eq_self x q,
          (Nat.ordCompl_pos q hx0).ne', Nat.not_dvd_ordCompl hq hx0⟩
      obtain ⟨j, d, hproj, hd0, hd_ndvd⟩ := hdecomp
      have hdvd : d ∣ m := by
        have hdx : d ∣ x := hproj ▸ dvd_mul_left d (q ^ j)
        have h1 : d ∣ m * q ^ e := dvd_trans hdx hxdvd
        have h3 : Nat.Coprime d (q ^ e) :=
          ((hq.coprime_iff_not_dvd).mpr hd_ndvd).symm.pow_right e
        exact h3.dvd_of_dvd_mul_right (mul_comm m (q ^ e) ▸ h1)
      have hje : j ≤ e := by
        have hqdvd : q ^ j ∣ m * q ^ e :=
          dvd_trans (hproj ▸ dvd_mul_right (q ^ j) d) hxdvd
        have h4 : Nat.Coprime (q ^ j) m := ((hq.coprime_iff_not_dvd).mpr hqm).pow_left j
        have h5 : q ^ j ∣ q ^ e := h4.dvd_of_dvd_mul_left hqdvd
        have h6 : (q ^ j).factorization ≤ (q ^ e).factorization :=
          (Nat.factorization_le_iff_dvd (pow_ne_zero j hq.ne_zero)
            (pow_ne_zero e hq.ne_zero)).mpr h5
        have h7 := Finsupp.le_def.mp h6 q
        rw [hq.factorization_pow, hq.factorization_pow, Finsupp.single_eq_same,
          Finsupp.single_eq_same] at h7
        exact h7
      rcases eq_or_lt_of_le (Nat.zero_le j) with hj0 | hj1
      · -- `j = 0`, so `x = d` divides `m`
        have hx_eq : x = d := by rw [← hproj, ← hj0, pow_zero, one_mul]
        have hxl : d ∈ d₁ :: d₂ :: mid := (hmem d).mpr ⟨hdvd, hx_eq ▸ hx1⟩
        subst hx_eq
        rcases List.mem_cons.mp hxl with rfl | hrest
        · exact Or.inr (Or.inr (Or.inl (mem_powChain.mpr ⟨0, Nat.zero_le _, by simp⟩)))
        rcases List.mem_cons.mp hrest with rfl | hmid
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (List.mem_flatMap.mpr ⟨_, hmid, mem_powChain.mpr ⟨0, Nat.zero_le _, by simp⟩⟩))
      · -- `j ≥ 1`
        have hx_eq : x = d * q ^ j := by rw [← hproj, mul_comm]
        subst hx_eq
        by_cases hd1 : d = 1
        · subst hd1
          refine Or.inr (Or.inr (Or.inr (Or.inl (mem_powChain.mpr ⟨j - 1, by omega, ?_⟩))))
          rw [← pow_succ', Nat.sub_add_cancel hj1]
          simp
        · have hd1' : 1 < d := by
            rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hd0) with h | h
            · exact absurd h.symm hd1
            · exact h
          have hxl : d ∈ d₁ :: d₂ :: mid := (hmem d).mpr ⟨hdvd, hd1'⟩
          rcases List.mem_cons.mp hxl with rfl | hmid₁
          · exact Or.inr (Or.inr (Or.inl (mem_powChain.mpr ⟨j, hje, rfl⟩)))
          rcases List.mem_cons.mp hmid₁ with rfl | hmid
          · refine Or.inr (Or.inr (Or.inr (Or.inr (mem_powChain.mpr ⟨j - 1, by omega, ?_⟩))))
            rw [mul_assoc _ q _, ← pow_succ', Nat.sub_add_cancel hj1]
          · exact Or.inr (Or.inl (List.mem_flatMap.mpr ⟨_, hmid, mem_powChain.mpr ⟨j, hje, rfl⟩⟩))
  · -- chain
    exact isChain_append _ _ (.singleton d₂)
      (isChain_append _ _ hFchain
        (isChain_append _ _ (isChain_powChain hd₁2 e)
          (isChain_append _ _ (isChain_powChain hq.two_le (e - 1))
            (isChain_powChain hd₂q (e - 1)) hb4)
          hb3)
        hb2)
      hb1
  · -- wrap-around
    have hRESTne : (mid.flatMap (fun d => powChain d q e) ++
        (powChain d₁ q e ++ (powChain q q (e - 1) ++ powChain (d₂ * q) q (e - 1)))) ≠ [] := by
      simp [powChain_ne_nil]
    intro a ha b hb
    rw [List.getLast?_cons_of_ne_nil hRESTne] at ha
    simp at ha
    subst ha
    rw [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
    subst hb
    exact R_of_dvd_of_dvd hd₂2
      (dvd_trans (dvd_mul_right d₂ q) (dvd_mul_right (d₂ * q) _)) dvd_rfl

/-- The divisors `> 1` of a prime power `p ^ a` with `2 ≤ a` admit a good
circle: any arrangement works, since every such divisor is divisible by `p`. -/
lemma goodCircle_prime_pow {p : ℕ} (hp : p.Prime) {a : ℕ} (ha : 2 ≤ a) :
    GoodCircle (p ^ a) := by
  have hpa : p ^ a ≠ 0 := pow_ne_zero a hp.ne_zero
  have hl : ∀ x : ℕ, x ∈ ((p ^ a).divisors.filter (fun d => 1 < d)).sort (· ≤ ·) ↔
      x ∣ p ^ a ∧ 1 < x := by
    intro x
    rw [Finset.mem_sort, Finset.mem_filter, Nat.mem_divisors]
    tauto
  refine ⟨((p ^ a).divisors.filter (fun d => 1 < d)).sort (· ≤ ·),
    Finset.sort_nodup _ _, ?_, hl, ?_, ?_⟩
  · -- nonempty: `p` is in the list
    have hp_mem : p ∈ ((p ^ a).divisors.filter (fun d => 1 < d)).sort (· ≤ ·) :=
      (hl p).mpr ⟨dvd_pow_self p (by omega), hp.one_lt⟩
    intro hnil
    rw [hnil] at hp_mem
    simp at hp_mem
  · -- chain: every element is divisible by `p`
    apply isChain_of_forall_dvd hp.two_le
    intro x hx
    obtain ⟨hxdvd, hx1⟩ := (hl x).mp hx
    obtain ⟨r, hrp, hrd⟩ := Nat.exists_prime_and_dvd (by omega : x ≠ 1)
    have hrp' : r = p := by
      have h1 : r ∣ p := hrp.dvd_of_dvd_pow (dvd_trans hrd hxdvd)
      exact (Nat.prime_dvd_prime_iff_eq hrp hp).mp h1
    exact hrp' ▸ hrd
  · -- wrap-around
    intro x hx y hy
    have hxl : x ∈ ((p ^ a).divisors.filter (fun d => 1 < d)).sort (· ≤ ·) :=
      List.mem_of_getLast? hx
    have hyl : y ∈ ((p ^ a).divisors.filter (fun d => 1 < d)).sort (· ≤ ·) := by
      cases l : ((p ^ a).divisors.filter (fun d => 1 < d)).sort (· ≤ ·) with
      | nil => simp [l] at hy
      | cons b t =>
        rw [l, List.head?_cons, Option.mem_def, Option.some.injEq] at hy
        subst hy
        simp
    obtain ⟨hxdvd, hx1⟩ := (hl x).mp hxl
    obtain ⟨hydvd, hy1⟩ := (hl y).mp hyl
    have hxp : p ∣ x := by
      obtain ⟨r, hrp, hrd⟩ := Nat.exists_prime_and_dvd (by omega : x ≠ 1)
      have hrp' : r = p :=
        (Nat.prime_dvd_prime_iff_eq hrp hp).mp (hrp.dvd_of_dvd_pow (dvd_trans hrd hxdvd))
      exact hrp' ▸ hrd
    have hyp : p ∣ y := by
      obtain ⟨r, hrp, hrd⟩ := Nat.exists_prime_and_dvd (by omega : y ≠ 1)
      have hrp' : r = p :=
        (Nat.prime_dvd_prime_iff_eq hrp hp).mp (hrp.dvd_of_dvd_pow (dvd_trans hrd hydvd))
      exact hrp' ▸ hrd
    exact R_of_dvd_of_dvd hp.two_le hxp hyp

/-- A circle for a composite number has at least two elements. -/
lemma two_le_length_of_composite_circle {n : ℕ} (hn : 1 < n) (hnp : ¬ n.Prime)
    {l : List ℕ} (hnodup : l.Nodup) (hmem : ∀ d : ℕ, d ∈ l ↔ d ∣ n ∧ 1 < d) :
    2 ≤ l.length := by
  obtain ⟨r, hrp, hrd⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
  have hr : r ∈ l := (hmem r).mpr ⟨hrd, hrp.one_lt⟩
  have hnl : n ∈ l := (hmem n).mpr ⟨dvd_refl n, hn⟩
  have hrn : r ≠ n := by rintro rfl; exact hnp hrp
  have hsub : ({r, n} : Finset ℕ) ⊆ l.toFinset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · simpa using hr
    · simpa using hnl
  have h2 : 2 ≤ l.toFinset.card := Finset.card_pair hrn ▸ Finset.card_le_card hsub
  rwa [List.toFinset_card_of_nodup hnodup] at h2

/-- If `m` has a prime factor whose exponent in `m` is at least `2`,
then `m` is not a product of two distinct primes. -/
lemma not_pq_of_factorization_ge_two {m p : ℕ} (_hp : p.Prime)
    (hp2 : 2 ≤ m.factorization p) :
    ¬ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ r ≠ s ∧ m = r * s := by
  rintro ⟨r, s, hr, hs, hrs, hrm⟩
  have h1 : m.factorization p = (r.factorization + s.factorization) p := by
    rw [hrm, Nat.factorization_mul hr.ne_zero hs.ne_zero]
  rw [hr.factorization, hs.factorization] at h1
  have hle : m.factorization p ≤ 1 := by
    rw [h1]
    by_cases h2 : p = r
    · rw [h2, Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne hrs]
      try omega
    · by_cases h3 : p = s
      · rw [h3, Finsupp.add_apply, Finsupp.single_eq_same,
          Finsupp.single_eq_of_ne hrs.symm]
        try omega
      · rw [Finsupp.add_apply, Finsupp.single_eq_of_ne h2,
          Finsupp.single_eq_of_ne h3]
        try omega
  omega

/-- If `m` has at least three distinct prime factors, then `m` is not a
product of two distinct primes. -/
lemma not_pq_of_three_le_card {m : ℕ} (h3 : 3 ≤ m.primeFactors.card) :
    ¬ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ r ≠ s ∧ m = r * s := by
  rintro ⟨r, s, hr, hs, hrs, hrm⟩
  have h1 : m.primeFactors = {s, r} := by
    rw [hrm, Nat.primeFactors_mul hr.ne_zero hs.ne_zero, hr.primeFactors,
      hs.primeFactors, Finset.union_singleton]
  rw [h1] at h3
  have hle : ({s, r} : Finset ℕ).card ≤ 2 := by
    by_cases h2 : s = r
    · subst h2; simp
    · simp [Finset.card_pair h2]
  omega

/-- For `a` non-zero and `b ≥ 2`, neither `a * b` nor `b * a` equals `a`. -/
lemma mul_ne_self {a b : ℕ} (ha : 0 < a) (hb : 2 ≤ b) : a * b ≠ a ∧ b * a ≠ a := by
  constructor
  · intro h
    have h2 : a * 1 = a * b := by rw [mul_one]; exact h.symm
    have h3 : 1 = b := Nat.mul_left_cancel ha h2
    omega
  · intro h
    have h2 : 1 * a = b * a := by rw [one_mul]; exact h.symm
    have h3 : 1 = b := Nat.mul_right_cancel ha h2
    omega

/-- Cancelling a common positive factor on the right preserves inequality. -/
lemma mul_ne_mul_of_ne {a b c : ℕ} (ha : 0 < a) (h : b ≠ c) : b * a ≠ c * a := by
  intro h'
  exact h (Nat.mul_right_cancel ha h')

/-- A prime cannot equal a product with another prime on the left. -/
lemma ne_of_prime_mul {a b c : ℕ} (ha : a.Prime) (hb : b.Prime) (h : a ≠ b) :
    a ≠ b * c := by
  intro h'
  exact h ((Nat.prime_dvd_prime_iff_eq hb ha).mp (h' ▸ dvd_mul_right b c)).symm

/-- A prime cannot equal a product of three numbers when the first is a
different prime. -/
lemma ne_of_prime_mul_mul {a b : ℕ} (ha : a.Prime) (hb : b.Prime) (h : a ≠ b)
    (c d : ℕ) : a ≠ b * c * d := by
  intro h'
  have hd : b ∣ a := h'.symm ▸ dvd_mul_of_dvd_left (dvd_mul_right b c) d
  exact h ((Nat.prime_dvd_prime_iff_eq hb ha).mp hd).symm

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
    have hne1 : p ≠ p * q := (mul_ne_self hp.pos hq.two_le).1.symm
    have hne2 : q ≠ p * q := (mul_ne_self hq.pos hp.two_le).2.symm
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

/-- For pairwise distinct primes `p q r`, the circle
`[p*q, q, q*r, r, r*p, p, p*q*r]` works. -/
lemma goodCircle_three_primes {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r) :
    GoodCircle (p * q * r) := by
  have hpqr0 : p * q * r ≠ 0 := mul_ne_zero (mul_ne_zero hp.ne_zero hq.ne_zero) hr.ne_zero
  have h1pq : 1 < p * q := lt_of_lt_of_le hp.one_lt (Nat.le_mul_of_pos_right _ hq.pos)
  have h1qr : 1 < q * r := lt_of_lt_of_le hq.one_lt (Nat.le_mul_of_pos_right _ hr.pos)
  have h1rp : 1 < r * p := lt_of_lt_of_le hr.one_lt (Nat.le_mul_of_pos_right _ hp.pos)
  refine ⟨[p * q, q, q * r, r, r * p, p, p * q * r], ?_, by simp, ?_, ?_, ?_⟩
  · -- nodup: all seven entries are distinct
    have e1 : p * q ≠ q := (mul_ne_self hq.pos hp.two_le).2
    have e2 : p * q ≠ q * r := by
      rw [mul_comm q r]; exact mul_ne_mul_of_ne hq.pos hpr
    have e3 : p * q ≠ r := (ne_of_prime_mul hr hp hpr.symm).symm
    have e4 : p * q ≠ r * p := by
      rw [mul_comm p q]; exact mul_ne_mul_of_ne hp.pos hqr
    have e5 : p * q ≠ p := (mul_ne_self hp.pos hq.two_le).1
    have e6 : p * q ≠ p * q * r := by
      intro h
      have h2 : p * q * 1 = p * q * r := by rw [mul_one]; exact h
      have h3 : 1 = r := Nat.mul_left_cancel (mul_pos hp.pos hq.pos) h2
      exact hr.ne_one h3.symm
    have e7 : q ≠ q * r := (mul_ne_self hq.pos hr.two_le).1.symm
    have e8 : q ≠ r := hqr
    have e9 : q ≠ r * p := ne_of_prime_mul hq hr hqr
    have e10 : q ≠ p := hpq.symm
    have e11 : q ≠ p * q * r := ne_of_prime_mul_mul hq hp hpq.symm q r
    have e12 : q * r ≠ r := (mul_ne_self hr.pos hq.two_le).2
    have e13 : q * r ≠ r * p := by
      rw [mul_comm r p]; exact mul_ne_mul_of_ne hr.pos hpq.symm
    have e14 : q * r ≠ p := (ne_of_prime_mul hp hq hpq).symm
    have e15 : q * r ≠ p * q * r := by
      rw [show p * q * r = q * r * p by ring]
      intro h
      have h2 : q * r * 1 = q * r * p := by rw [mul_one]; exact h
      have h3 : 1 = p := Nat.mul_left_cancel (mul_pos hq.pos hr.pos) h2
      exact hp.ne_one h3.symm
    have e16 : r ≠ r * p := (mul_ne_self hr.pos hp.two_le).1.symm
    have e17 : r ≠ p := hpr.symm
    have e18 : r ≠ p * q * r := by
      rw [show p * q * r = q * p * r by ring]
      exact ne_of_prime_mul_mul hr hq hqr.symm p r
    have e19 : r * p ≠ p := (mul_ne_self hp.pos hr.two_le).2
    have e20 : r * p ≠ p * q * r := by
      rw [show p * q * r = r * p * q by ring]
      intro h
      have h2 : r * p * 1 = r * p * q := by rw [mul_one]; exact h
      have h3 : 1 = q := Nat.mul_left_cancel (mul_pos hr.pos hp.pos) h2
      exact hq.ne_one h3.symm
    have e21 : p ≠ p * q * r := by
      rw [show p * q * r = q * p * r by ring]
      exact ne_of_prime_mul_mul hp hq hpq p r
    simp only [List.nodup_cons, List.mem_cons, not_or]
    exact ⟨⟨e1, e2, e3, e4, e5, e6, by simp⟩, ⟨e7, e8, e9, e10, e11, by simp⟩,
      ⟨e12, e13, e14, e15, by simp⟩, ⟨e16, e17, e18, by simp⟩,
      ⟨e19, e20, by simp⟩, ⟨e21, by simp⟩, by simp⟩
  · -- membership
    intro x
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · exact ⟨dvd_mul_right _ _, h1pq⟩
      · exact ⟨dvd_trans (dvd_mul_left _ _) (dvd_mul_right _ _), hq.one_lt⟩
      · exact ⟨by rw [show p * q * r = q * r * p by ring]; exact dvd_mul_right _ _, h1qr⟩
      · exact ⟨dvd_mul_of_dvd_right dvd_rfl _, hr.one_lt⟩
      · exact ⟨by rw [show p * q * r = r * p * q by ring]; exact dvd_mul_right _ _, h1rp⟩
      · exact ⟨dvd_trans (dvd_mul_right _ _) (dvd_mul_right _ _), hp.one_lt⟩
      · exact ⟨dvd_refl _, lt_of_lt_of_le h1pq (Nat.le_mul_of_pos_right _ hr.pos)⟩
    · rintro ⟨hxdvd, hx1⟩
      have hx : x ∈ (p * q * r).divisors := Nat.mem_divisors.mpr ⟨hxdvd, hpqr0⟩
      rw [Nat.divisors_mul, Nat.divisors_mul, hp.divisors, hq.divisors, hr.divisors] at hx
      rw [Finset.mem_mul] at hx
      obtain ⟨u, hu, w, hw, hux⟩ := hx
      rw [Finset.mem_mul] at hu
      obtain ⟨a, ha, b, hb, hab⟩ := hu
      rw [Finset.mem_insert, Finset.mem_singleton] at ha hb hw
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hw with rfl | rfl
      · exfalso
        rw [← hux, ← hab, one_mul, one_mul] at hx1
        exact lt_irrefl 1 hx1
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [← hux, ← hab, one_mul, one_mul]))))
      · exact Or.inr (Or.inl (by rw [← hux, ← hab, one_mul, mul_one]))
      · exact Or.inr (Or.inr (Or.inl (by rw [← hux, ← hab, one_mul])))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          (by rw [← hux, ← hab, mul_one, mul_one]))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          (by rw [← hux, ← hab, mul_one, mul_comm])))))
      · exact Or.inl (by rw [← hux, ← hab, mul_one])
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by rw [← hux, ← hab]))))))
  · -- chain
    rw [List.isChain_cons_cons, List.isChain_cons_cons, List.isChain_cons_cons,
      List.isChain_cons_cons, List.isChain_cons_cons, List.isChain_cons_cons]
    exact ⟨R_of_dvd_of_dvd hq.two_le (dvd_mul_left _ _) dvd_rfl,
      R_of_dvd_of_dvd hq.two_le dvd_rfl (dvd_mul_right _ _),
      R_of_dvd_of_dvd hr.two_le (dvd_mul_left _ _) dvd_rfl,
      R_of_dvd_of_dvd hr.two_le dvd_rfl (dvd_mul_right _ _),
      R_of_dvd_of_dvd hp.two_le (dvd_mul_left _ _) dvd_rfl,
      R_of_dvd_of_dvd hp.two_le dvd_rfl
        (dvd_trans (dvd_mul_right _ _) (dvd_mul_right _ _)),
      List.IsChain.singleton _⟩
  · -- wrap-around
    intro x hx y hy
    simp at hx hy
    subst hx; subst hy
    exact R_of_dvd_of_dvd h1pq (dvd_mul_right _ _) dvd_rfl

/-- **Main induction**: every composite `n` that is not a product of two
distinct primes admits a good circle. -/
lemma goodCircle_of_not_pq : ∀ (k : ℕ) (n : ℕ), n.primeFactors.card = k →
    1 < n → ¬ n.Prime →
    (¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ n = p * q) → GoodCircle n := by
  intro k
  induction k with
  | zero =>
    intro n hk hn hnp h
    rw [Finset.card_eq_zero] at hk
    rw [Nat.primeFactors_eq_empty] at hk
    rcases hk with rfl | rfl <;> simp at hn
  | succ k ih =>
    intro n hk hn hnp h
    have hn0 : n ≠ 0 := by omega
    have key : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
      have h1 := Nat.prod_factorization_pow_eq_self hn0
      show ∏ p ∈ n.factorization.support, p ^ n.factorization p = n
      exact h1
    rcases k with - | - | k
    · -- exactly one prime factor: `n` is a prime power `p ^ a` with `a ≥ 2`
      obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hk
      have hpm : p ∈ n.primeFactors := by rw [hp]; simp
      obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactors.mp hpm
      have ha1 : 1 ≤ n.factorization p := hpp.factorization_pos_of_dvd hn0 hpd
      have hne : n = p ^ n.factorization p := by
        conv_lhs => rw [← key, hp, Finset.prod_singleton]
      have ha2 : 2 ≤ n.factorization p := by
        by_contra hc
        push Not at hc
        have h1 : n.factorization p = 1 := by omega
        rw [hne, h1, pow_one] at hnp
        exact hnp hpp
      rw [hne]
      exact goodCircle_prime_pow hpp ha2
    · -- exactly two prime factors
      obtain ⟨p, q, hpq, hpf⟩ := Finset.card_eq_two.mp hk
      have hpm : p ∈ n.primeFactors := by rw [hpf]; simp
      have hqm : q ∈ n.primeFactors := by rw [hpf]; simp
      obtain ⟨hp, hpd, -⟩ := Nat.mem_primeFactors.mp hpm
      obtain ⟨hq, hqd, -⟩ := Nat.mem_primeFactors.mp hqm
      have ha : 1 ≤ n.factorization p := hp.factorization_pos_of_dvd hn0 hpd
      have hb : 1 ≤ n.factorization q := hq.factorization_pos_of_dvd hn0 hqd
      have hne : n = p ^ n.factorization p * q ^ n.factorization q := by
        conv_lhs => rw [← key, hpf, Finset.prod_pair hpq]
      have hab : ¬ (n.factorization p = 1 ∧ n.factorization q = 1) := by
        rintro ⟨ha1, hb1⟩
        exact h ⟨p, q, hp, hq, hpq, by rw [hne, ha1, hb1, pow_one, pow_one]⟩
      rcases (by omega : 2 ≤ n.factorization p ∨ 2 ≤ n.factorization q) with h2 | h2
      · -- circle of `p ^ a`, then adjoin `q ^ b`
        obtain ⟨l, hnodup, hlne, hmem, hchain, hwrap⟩ := goodCircle_prime_pow hp h2
        have hlt : 1 < p ^ n.factorization p := Nat.one_lt_pow (by omega) hp.one_lt
        have hpa_prime : ¬ (p ^ n.factorization p).Prime := by
          intro hppa
          have hd : p ∣ p ^ n.factorization p := dvd_pow_self p (by omega)
          rcases hppa.eq_one_or_self_of_dvd p hd with h1 | h1
          · exact hp.ne_one h1
          · have h3 : n.factorization p = 1 := by
              have h4 : p ^ 1 = p ^ n.factorization p := by rw [pow_one]; exact h1
              exact (Nat.pow_right_injective hp.two_le h4).symm
            omega
        have hl2 : 2 ≤ l.length :=
          two_le_length_of_composite_circle hlt hpa_prime hnodup hmem
        have hqnpa : ¬ q ∣ p ^ n.factorization p := fun hqq =>
          hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hqq)).symm
        have hgc := goodCircle_mul_prime_pow hq hqnpa hnodup hl2 hmem hchain hwrap
          (n.factorization q) hb
        rwa [hne]
      · -- circle of `q ^ b`, then adjoin `p ^ a`
        obtain ⟨l, hnodup, hlne, hmem, hchain, hwrap⟩ := goodCircle_prime_pow hq h2
        have hlt : 1 < q ^ n.factorization q := Nat.one_lt_pow (by omega) hq.one_lt
        have hqb_prime : ¬ (q ^ n.factorization q).Prime := by
          intro hqqa
          have hd : q ∣ q ^ n.factorization q := dvd_pow_self q (by omega)
          rcases hqqa.eq_one_or_self_of_dvd q hd with h1 | h1
          · exact hq.ne_one h1
          · have h3 : n.factorization q = 1 := by
              have h4 : q ^ 1 = q ^ n.factorization q := by rw [pow_one]; exact h1
              exact (Nat.pow_right_injective hq.two_le h4).symm
            omega
        have hl2 : 2 ≤ l.length :=
          two_le_length_of_composite_circle hlt hqb_prime hnodup hmem
        have hpnqb : ¬ p ∣ q ^ n.factorization q := fun hpp =>
          hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hpp))
        have hgc := goodCircle_mul_prime_pow hp hpnqb hnodup hl2 hmem hchain hwrap
          (n.factorization p) ha
        rw [hne, mul_comm (p ^ n.factorization p) (q ^ n.factorization q)]
        exact hgc
    · -- three or more prime factors
      have hk3 : 3 ≤ n.primeFactors.card := by omega
      by_cases hsq : ∃ p ∈ n.primeFactors, 2 ≤ n.factorization p
      · -- some prime factor `ps` has exponent `≥ 2`; peel off a different prime
        obtain ⟨ps, hps_mem, hps2⟩ := hsq
        obtain ⟨hps, -, -⟩ := Nat.mem_primeFactors.mp hps_mem
        have hcard' : 2 ≤ (n.primeFactors \ {ps}).card := by
          rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hps_mem]; omega
        obtain ⟨q, hq_mem⟩ := Finset.card_pos.mp (by omega : 0 < (n.primeFactors \ {ps}).card)
        rw [Finset.mem_sdiff] at hq_mem
        obtain ⟨hqm, hqne⟩ := hq_mem
        have hqps : q ≠ ps := by
          intro hqq; subst hqq; simp at hqne
        obtain ⟨hq, hqd, -⟩ := Nat.mem_primeFactors.mp hqm
        -- the peeled number `m`
        set m := ordCompl[q] n with hm_def
        have hqe : ordProj[q] n * m = n := Nat.ordProj_mul_ordCompl_eq_self n q
        have hqm' : ¬ q ∣ m := Nat.not_dvd_ordCompl hq hn0
        have hm0 : m ≠ 0 := by
          intro hmz; rw [hmz, mul_zero] at hqe; exact hn0 hqe.symm
        have hpf_m : m.primeFactors = n.primeFactors \ {q} := by
          rw [hm_def, ← Nat.support_factorization, Nat.factorization_ordCompl,
            Finsupp.support_erase, Nat.support_factorization,
            Finset.sdiff_singleton_eq_erase]
        have hcard_m : m.primeFactors.card = k + 2 := by
          rw [hpf_m, Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hqm]; omega
        have hps_m : 2 ≤ m.factorization ps := by
          have h1 : m.factorization ps = n.factorization ps := by
            rw [hm_def, Nat.factorization_ordCompl, Finsupp.erase_ne hqps.symm]
          rw [h1]; exact hps2
        have hpsm : ps ∈ m.primeFactors := by
          rw [hpf_m, Finset.mem_sdiff]
          exact ⟨hps_mem, by simp [hqps.symm]⟩
        obtain ⟨-, hpsd, -⟩ := Nat.mem_primeFactors.mp hpsm
        have h1m : 1 < m := lt_of_lt_of_le hps.one_lt (Nat.le_of_dvd hm0.bot_lt hpsd)
        have hnpm : ¬ m.Prime := by
          intro hmp
          have h1 : m.factorization ps ≤ 1 := by
            rw [hmp.factorization]
            by_cases h2 : ps = m
            · subst h2; rw [Finsupp.single_eq_same]; try omega
            · rw [Finsupp.single_eq_of_ne h2]; try omega
          omega
        have hmnpq : ¬ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ r ≠ s ∧ m = r * s :=
          not_pq_of_factorization_ge_two hps hps_m
        obtain ⟨l, hnodup, hlne, hmem, hchain, hwrap⟩ := ih m hcard_m h1m hnpm hmnpq
        have hl2 : 2 ≤ l.length := two_le_length_of_composite_circle h1m hnpm hnodup hmem
        have hgc := goodCircle_mul_prime_pow hq hqm' hnodup hl2 hmem hchain hwrap
          (n.factorization q) (hq.factorization_pos_of_dvd hn0 hqd)
        rw [← hqe]
        exact mul_comm m _ ▸ hgc
      · -- all exponents are `1`
        push Not at hsq
        have hf1 : ∀ x ∈ n.primeFactors, n.factorization x = 1 := by
          intro x hx
          have h1 : x ∣ n ∧ x.Prime := by
            have := Nat.mem_primeFactors.mp hx
            exact ⟨this.2.1, this.1⟩
          have h2 : 1 ≤ n.factorization x := h1.2.factorization_pos_of_dvd hn0 h1.1
          have h3 := hsq x hx
          omega
        by_cases hk3' : n.primeFactors.card = 3
        · -- `n = p * q * r`, a product of three distinct primes
          obtain ⟨p, q, r, hpq, hpr, hqr, h3⟩ := Finset.card_eq_three.mp hk3'
          have hpm : p ∈ n.primeFactors := by rw [h3]; simp
          have hqm : q ∈ n.primeFactors := by rw [h3]; simp
          have hrm : r ∈ n.primeFactors := by rw [h3]; simp
          obtain ⟨hp, -, -⟩ := Nat.mem_primeFactors.mp hpm
          obtain ⟨hq, -, -⟩ := Nat.mem_primeFactors.mp hqm
          obtain ⟨hr, -, -⟩ := Nat.mem_primeFactors.mp hrm
          have hne : n = p * q * r := by
            conv_lhs => rw [← key, h3, Finset.prod_insert (by simp [hpq, hpr]),
              Finset.prod_insert (by simp [hqr]), Finset.prod_singleton]
            rw [hf1 p (by simp [h3]), hf1 q (by simp [h3]), hf1 r (by simp [h3]),
              pow_one, pow_one, pow_one, mul_assoc]
          rw [hne]
          exact goodCircle_three_primes hp hq hr hpq hqr hpr
        · -- at least four prime factors; peel off any of them
          obtain ⟨q, hq_mem⟩ := Finset.card_pos.mp (by omega : 0 < n.primeFactors.card)
          obtain ⟨hq, hqd, -⟩ := Nat.mem_primeFactors.mp hq_mem
          set m := ordCompl[q] n with hm_def
          have hqe : ordProj[q] n * m = n := Nat.ordProj_mul_ordCompl_eq_self n q
          have hqm' : ¬ q ∣ m := Nat.not_dvd_ordCompl hq hn0
          have hm0 : m ≠ 0 := by
            intro hmz; rw [hmz, mul_zero] at hqe; exact hn0 hqe.symm
          have hpf_m : m.primeFactors = n.primeFactors \ {q} := by
            rw [hm_def, ← Nat.support_factorization, Nat.factorization_ordCompl,
              Finsupp.support_erase, Nat.support_factorization,
              Finset.sdiff_singleton_eq_erase]
          have hcard_m : m.primeFactors.card = k + 2 := by
            rw [hpf_m, Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hq_mem]; omega
          have hcard3 : 3 ≤ m.primeFactors.card := by
            rw [hpf_m, Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hq_mem]; omega
          have h1m : 1 < m := by
            have hne2 : m.primeFactors.Nonempty := Finset.card_pos.mp (by omega)
            obtain ⟨r, hrm⟩ := hne2
            obtain ⟨hrp, hrd, -⟩ := Nat.mem_primeFactors.mp hrm
            exact lt_of_lt_of_le hrp.one_lt (Nat.le_of_dvd hm0.bot_lt hrd)
          have hnpm : ¬ m.Prime := by
            intro hmp
            rw [hmp.primeFactors] at hcard3
            simp at hcard3
          have hmnpq : ¬ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ r ≠ s ∧ m = r * s :=
            not_pq_of_three_le_card hcard3
          obtain ⟨l, hnodup, hlne, hmem, hchain, hwrap⟩ := ih m hcard_m h1m hnpm hmnpq
          have hl2 : 2 ≤ l.length := two_le_length_of_composite_circle h1m hnpm hnodup hmem
          have hgc := goodCircle_mul_prime_pow hq hqm' hnodup hl2 hmem hchain hwrap
            (n.factorization q) (hq.factorization_pos_of_dvd hn0 hqd)
          rw [← hqe]
          exact mul_comm m _ ▸ hgc

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
    exact goodCircle_of_not_pq _ n rfl hn hnp h

end Usa2005P1
