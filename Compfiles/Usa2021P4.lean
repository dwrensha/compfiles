/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Data.Nat.Nth
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 2021, Problem 4

A finite set S of positive integers has the property that, for each s ∈ S,
and each positive integer divisor d of s, there exists a unique element t ∈ S
satisfying gcd(s, t) = d. (The elements s and t could be equal.)

Given this information, find all possible values for the number of elements of S.
-/

namespace Usa2021P4

/-- The property from the problem statement: `S` is a finite set of positive integers
such that for every `s ∈ S` and every positive divisor `d` of `s` there exists a unique
`t ∈ S` with `Nat.gcd s t = d`. -/
def IsValid (S : Finset ℕ) : Prop :=
  (∀ s ∈ S, 0 < s) ∧ ∀ s ∈ S, ∀ d : ℕ, 0 < d → d ∣ s → ∃! t : ℕ, t ∈ S ∧ Nat.gcd s t = d

determine solution_set : Set ℕ := {n | ∃ k : ℕ, n = 2 ^ k}

snip begin

/-- For `s ∈ S`, the map `t ↦ Nat.gcd s t` is a bijection from `S` onto the divisors
of `s`; in particular `#S = τ(s)`. -/
theorem card_eq_card_divisors {S : Finset ℕ} (hS : IsValid S) {s : ℕ} (hs : s ∈ S) :
    S.card = s.divisors.card := by
  obtain ⟨hpos, huniq⟩ := hS
  have hs0 : s ≠ 0 := (hpos s hs).ne'
  refine Finset.card_bij (fun t _ => Nat.gcd s t) ?_ ?_ ?_
  · intro t ht
    exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left s t, hs0⟩
  · intro t₁ ht₁ t₂ ht₂ hgcd
    obtain ⟨u, -, hu⟩ := huniq s hs (Nat.gcd s t₁)
      (Nat.gcd_pos_of_pos_left t₁ (hpos s hs)) (Nat.gcd_dvd_left s t₁)
    exact (hu t₁ ⟨ht₁, rfl⟩).trans (hu t₂ ⟨ht₂, hgcd.symm⟩).symm
  · intro d hd
    obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hd
    obtain ⟨t, ⟨htS, htg⟩, -⟩ := huniq s hs d (Nat.pos_of_mem_divisors hd) hdvd
    exact ⟨t, htS, htg⟩

/-- The same bijection identifies the elements of `S` divisible by `p` with the
divisors of `s` divisible by `p` (for `p ∣ s`). -/
theorem card_filter_dvd {S : Finset ℕ} (hS : IsValid S) {s : ℕ} (hs : s ∈ S) {p : ℕ}
    (hps : p ∣ s) :
    (S.filter (fun t => p ∣ t)).card = (s.divisors.filter (fun d => p ∣ d)).card := by
  obtain ⟨hpos, huniq⟩ := hS
  have hs0 : s ≠ 0 := (hpos s hs).ne'
  refine Finset.card_bij (fun t _ => Nat.gcd s t) ?_ ?_ ?_
  · intro t ht
    obtain ⟨htS, hpt⟩ := Finset.mem_filter.mp ht
    exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left s t, hs0⟩,
      Nat.dvd_gcd hps hpt⟩
  · intro t₁ ht₁ t₂ ht₂ hgcd
    obtain ⟨ht₁S, -⟩ := Finset.mem_filter.mp ht₁
    obtain ⟨ht₂S, -⟩ := Finset.mem_filter.mp ht₂
    obtain ⟨u, -, hu⟩ := huniq s hs (Nat.gcd s t₁)
      (Nat.gcd_pos_of_pos_left t₁ (hpos s hs)) (Nat.gcd_dvd_left s t₁)
    exact (hu t₁ ⟨ht₁S, rfl⟩).trans (hu t₂ ⟨ht₂S, hgcd.symm⟩).symm
  · intro d hd
    obtain ⟨hdS, hpd⟩ := Finset.mem_filter.mp hd
    obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hdS
    obtain ⟨t, ⟨htS, htg⟩, -⟩ := huniq s hs d (Nat.pos_of_mem_divisors hdS) hdvd
    have hpt : p ∣ t := by
      rw [← htg] at hpd
      exact Nat.dvd_trans hpd (Nat.gcd_dvd_right s t)
    exact ⟨t, Finset.mem_filter.mpr ⟨htS, hpt⟩, htg⟩

/-- The divisors of `s` divisible by a prime `p ∣ s` are in bijection (via `d ↦ d / p`)
with the divisors of `s / p`. -/
theorem card_divisors_filter_dvd {s p : ℕ} (hp : p.Prime) (hs0 : s ≠ 0) (hps : p ∣ s) :
    (s.divisors.filter (fun d => p ∣ d)).card = (s / p).divisors.card := by
  have hsp0 : s / p ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr hs0) hps) hp.pos).ne'
  refine Finset.card_bij (fun d _ => d / p) ?_ ?_ ?_
  · intro d hd
    obtain ⟨hdS, hpd⟩ := Finset.mem_filter.mp hd
    obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hdS
    obtain ⟨e, rfl⟩ := hpd
    obtain ⟨c, hc⟩ := hdvd
    rw [Nat.mul_div_cancel_left _ hp.pos]
    refine Nat.mem_divisors.mpr ⟨?_, hsp0⟩
    have hspc : (p * e * c) / p = e * c := by
      rw [mul_assoc]
      exact Nat.mul_div_cancel_left _ hp.pos
    rw [hc, hspc]
    exact Nat.dvd_mul_right e c
  · intro d₁ hd₁ d₂ hd₂ hdiv
    obtain ⟨hd₁S, hpd₁⟩ := Finset.mem_filter.mp hd₁
    obtain ⟨hd₂S, hpd₂⟩ := Finset.mem_filter.mp hd₂
    rw [← Nat.mul_div_cancel' hpd₁, ← Nat.mul_div_cancel' hpd₂, hdiv]
  · intro e he
    obtain ⟨hedvd, -⟩ := Nat.mem_divisors.mp he
    refine ⟨p * e, Finset.mem_filter.mpr ⟨?_, Nat.dvd_mul_right p e⟩,
      Nat.mul_div_cancel_left e hp.pos⟩
    refine Nat.mem_divisors.mpr ⟨?_, hs0⟩
    rw [← Nat.mul_div_cancel' hps]
    exact Nat.mul_dvd_mul_left p hedvd

/-- The ratio identity for the divisor counting function: if `p ∣ s` is prime and
`e = νₚ(s)`, then `(e + 1) * τ(s / p) = e * τ(s)`. -/
theorem card_divisors_div_mul {s p : ℕ} (hp : p.Prime) (hs0 : s ≠ 0) (hps : p ∣ s) :
    (s.factorization p + 1) * (s / p).divisors.card = s.factorization p * s.divisors.card := by
  set e := s.factorization p with he
  have he1 : 1 ≤ e := hp.factorization_pos_of_dvd hs0 hps
  set m := s / p ^ e with hm
  have hpow : p ^ e ∣ s := (hp.pow_dvd_iff_le_factorization hs0).mpr le_rfl
  have hsm : s = p ^ e * m := (Nat.mul_div_cancel' hpow).symm
  have hpm : ¬ p ∣ m := by
    intro hpm
    have h1 : p ^ e * p ∣ p ^ e * m := mul_dvd_mul_left (p ^ e) hpm
    rw [← hsm, ← pow_succ] at h1
    have h2 := (hp.pow_dvd_iff_le_factorization hs0).mp h1
    omega
  have hcard : ∀ k : ℕ, (p ^ k * m).divisors.card = (k + 1) * m.divisors.card := by
    intro k
    have hcop : Nat.Coprime (p ^ k) m := (hp.coprime_pow_of_not_dvd hpm).symm
    rw [Nat.Coprime.card_divisors_mul hcop, Nat.divisors_prime_pow hp k, Finset.card_map,
      Finset.card_range]
  obtain ⟨e', he'⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  have hsp : s / p = p ^ e' * m := by
    rw [hsm, he', pow_succ]
    have hrw : p ^ e' * p * m = p * (p ^ e' * m) := by ring
    rw [hrw, Nat.mul_div_cancel_left _ hp.pos]
  have h1 : s.divisors.card = (e + 1) * m.divisors.card := by
    rw [hsm]
    exact hcard e
  have h2 : (s / p).divisors.card = e * m.divisors.card := by
    rw [hsp, hcard e', he']
  rw [h1, h2]
  ring

/-- The key claim: in a valid set every element is squarefree, i.e. every prime appears
with exponent at most one. Otherwise the density of multiples of `p` in `S` would have
to equal both `e / (e + 1)` and `1 / 2`. -/
theorem factorization_le_one {S : Finset ℕ} (hS : IsValid S) {x : ℕ} (hx : x ∈ S) {p : ℕ}
    (hp : p.Prime) :
    x.factorization p ≤ 1 := by
  have hpos := hS.1
  have huniq := hS.2
  have hx0 : x ≠ 0 := (hpos x hx).ne'
  by_contra h
  have he2 : 2 ≤ x.factorization p := lt_of_not_ge h
  set e := x.factorization p with he
  have hpx : p ∣ x := by
    have h1 : p ^ 1 ∣ x := (hp.pow_dvd_iff_le_factorization hx0).mpr (by omega)
    rwa [pow_one] at h1
  -- Counting the multiples of `p` in `S` via `x`: `(e + 1) * A = e * #S`.
  have hA1 := card_filter_dvd hS hx hpx
  have hB1 := card_divisors_filter_dvd hp hx0 hpx
  have hC1 := card_divisors_div_mul hp hx0 hpx
  have hN1 := card_eq_card_divisors hS hx
  -- Take `y ∈ S` with `gcd x y = p`; then `νₚ(y) = 1`.
  obtain ⟨y, ⟨hyS, hyg⟩, -⟩ := huniq x hx p hp.pos hpx
  have hy0 : y ≠ 0 := (hpos y hyS).ne'
  have hpy : p ∣ y := by
    rw [← hyg]
    exact Nat.gcd_dvd_right x y
  have hfy1 : 1 ≤ y.factorization p := hp.factorization_pos_of_dvd hy0 hpy
  have hfy : y.factorization p = 1 := by
    refine le_antisymm ?_ hfy1
    by_contra h2
    have h2' : 2 ≤ y.factorization p := lt_of_not_ge h2
    have hp2x : p ^ 2 ∣ x := (hp.pow_dvd_iff_le_factorization hx0).mpr he2
    have hp2y : p ^ 2 ∣ y := (hp.pow_dvd_iff_le_factorization hy0).mpr h2'
    have hp2g : p ^ 2 ∣ p := by
      have hgg : p ^ 2 ∣ Nat.gcd x y := Nat.dvd_gcd hp2x hp2y
      rwa [hyg] at hgg
    have hle : p ^ 2 ≤ p := Nat.le_of_dvd hp.pos hp2g
    have hle' : p ^ 2 ≤ p ^ 1 := by rwa [pow_one]
    have h21 : 2 ≤ 1 := (Nat.pow_le_pow_iff_right hp.one_lt).mp hle'
    omega
  -- Counting via `y` instead gives `2 * A = #S`.
  have hA2 := card_filter_dvd hS hyS hpy
  have hB2 := card_divisors_filter_dvd hp hy0 hpy
  have hC2 := card_divisors_div_mul hp hy0 hpy
  have hN2 := card_eq_card_divisors hS hyS
  -- Combine: `(e + 1) * A = 2 * e * A` with `A > 0`, so `e = 1`, a contradiction.
  set A := (S.filter (fun t => p ∣ t)).card with hA
  have hApos : 0 < A := Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hpx⟩⟩
  have hE1 : (e + 1) * A = e * S.card := by
    rw [← hB1, ← hA1, ← hN1, ← he] at hC1
    exact hC1
  have hE2 : 2 * A = S.card := by
    rw [← hB2, ← hA2, ← hN2, hfy] at hC2
    omega
  rw [← hE2] at hE1
  have heq : e + 1 = 2 * e := by
    have h' : (e + 1) * A = (2 * e) * A := by
      rw [hE1]
      ring
    exact Nat.mul_right_cancel hApos h'
  omega

/-- Any valid nonempty set has cardinality a power of two: `#S = τ(x) = 2^{ω(x)}`
for any `x ∈ S`. -/
theorem card_eq_two_pow {S : Finset ℕ} (hS : IsValid S) (hne : S.Nonempty) :
    ∃ k : ℕ, S.card = 2 ^ k := by
  obtain ⟨x, hx⟩ := hne
  have hpos := hS.1
  have hx0 : x ≠ 0 := (hpos x hx).ne'
  refine ⟨x.primeFactors.card, ?_⟩
  rw [card_eq_card_divisors hS hx, Nat.card_divisors hx0, ← Finset.prod_const 2]
  refine Finset.prod_congr rfl ?_
  intro p hpm
  have hpp := Nat.prime_of_mem_primeFactors hpm
  have hpd := Nat.dvd_of_mem_primeFactors hpm
  have h1 : 1 ≤ x.factorization p := hpp.factorization_pos_of_dvd hx0 hpd
  have h2 := factorization_le_one hS hx hpp
  have h3 : x.factorization p = 1 := le_antisymm h2 h1
  rw [h3]

/-- The `2k` primes used in the construction: in slot `i`, the "true" choice is the
`(2 * i)`-th prime and the "false" choice is the `(2 * i + 1)`-th prime. -/
noncomputable def constr_r (k : ℕ) (b : Fin k → Bool) (i : Fin k) : ℕ :=
  if b i then Nat.nth Nat.Prime (2 * i.val) else Nat.nth Nat.Prime (2 * i.val + 1)

/-- The flipped choice function: keep `b i` exactly when the `i`-th prime divides `d`. -/
noncomputable def constr_b' (k : ℕ) (b : Fin k → Bool) (d : ℕ) : Fin k → Bool :=
  fun i => if constr_r k b i ∣ d then b i else !(b i)

/-- Every value of `constr_r` is prime. -/
theorem constr_r_prime {k : ℕ} (b : Fin k → Bool) (i : Fin k) : Nat.Prime (constr_r k b i) := by
  unfold constr_r
  split <;> exact Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _

/-- The primes in different slots are distinct: `constr_r k b₁ i = constr_r k b₂ j`
forces `i = j`. -/
theorem constr_r_inj {k : ℕ} {b₁ b₂ : Fin k → Bool} {i j : Fin k}
    (h : constr_r k b₁ i = constr_r k b₂ j) : i = j := by
  have hinj := Nat.nth_injective Nat.infinite_setOfPred_prime
  unfold constr_r at h
  split at h <;> split at h
  · exact Fin.ext (by have h3 := hinj h; omega)
  · exact absurd (hinj h) (by omega)
  · exact absurd (hinj h) (by omega)
  · exact Fin.ext (by have h3 := hinj h; omega)

/-- Equal primes in the same slot force equal Booleans. -/
theorem constr_r_inj_bool {k : ℕ} {b₁ b₂ : Fin k → Bool} {i : Fin k}
    (h : constr_r k b₁ i = constr_r k b₂ i) : b₁ i = b₂ i := by
  have hinj := Nat.nth_injective Nat.infinite_setOfPred_prime
  unfold constr_r at h
  split at h <;> split at h
  · rename_i hb1 hb2
    rw [hb1, hb2]
  · exact absurd (hinj h) (by omega)
  · exact absurd (hinj h) (by omega)
  · rename_i hb1 hb2
    rw [Bool.not_eq_true _] at hb1 hb2
    rw [hb1, hb2]

/-- No Boolean equals its own negation. -/
theorem constr_bool_not_ne (c : Bool) : (!c) ≠ c := by
  cases c <;> simp

/-- The product map `b ↦ ∏ i, constr_r k b i` is injective. -/
theorem constr_prod_inj {k : ℕ} {b₁ b₂ : Fin k → Bool}
    (h : (∏ i : Fin k, constr_r k b₁ i) = ∏ i : Fin k, constr_r k b₂ i) : b₁ = b₂ := by
  funext i₀
  apply constr_r_inj_bool
  have hdvd : constr_r k b₁ i₀ ∣ ∏ i : Fin k, constr_r k b₂ i := by
    rw [← h]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i₀)
  obtain ⟨j, -, hjdvd⟩ := (Prime.dvd_finsetProd_iff (constr_r_prime b₁ i₀).prime _).mp hdvd
  have heq : constr_r k b₁ i₀ = constr_r k b₂ j :=
    (Nat.prime_dvd_prime_iff_eq (constr_r_prime b₁ i₀) (constr_r_prime b₂ j)).mp hjdvd
  obtain rfl : j = i₀ := (constr_r_inj heq).symm
  exact heq

/-- The flipped prime equals the original one exactly when the original divides `d`. -/
theorem constr_r_flip {k : ℕ} {b : Fin k → Bool} {d : ℕ} {i : Fin k} :
    constr_r k (constr_b' k b d) i = constr_r k b i ↔ constr_r k b i ∣ d := by
  constructor
  · intro h
    by_contra hnd
    have hb : constr_b' k b d i = !(b i) := if_neg hnd
    have h2 := constr_r_inj_bool h
    rw [hb] at h2
    exact constr_bool_not_ne _ h2
  · intro hdvd
    have hb : constr_b' k b d i = b i := if_pos hdvd
    unfold constr_r
    rw [hb]

/-- If every slot prime in `J` divides `d`, then so does their product. -/
theorem constr_prod_dvd_of_forall {k : ℕ} {b : Fin k → Bool} {d : ℕ}
    {J : Finset (Fin k)} (hJ : ∀ i ∈ J, constr_r k b i ∣ d) :
    (∏ i ∈ J, constr_r k b i) ∣ d := by
  revert hJ
  induction J using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    intro hJ
    rw [Finset.prod_insert has]
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ (hJ a (Finset.mem_insert_self a s)) (ih ?_)
    · refine Nat.Coprime.prod_right fun i hi => ?_
      refine (Nat.coprime_primes (constr_r_prime b a) (constr_r_prime b i)).mpr fun heq => ?_
      obtain rfl : a = i := constr_r_inj heq
      exact has hi
    · exact fun i hi => hJ i (Finset.mem_insert_of_mem hi)

/-- Support representation: a divisor of the full product is the product over the slots
whose primes divide it. -/
theorem constr_dvd_eq_prod_filter {k : ℕ} {b : Fin k → Bool} {d : ℕ}
    (hd : d ∣ ∏ i : Fin k, constr_r k b i) :
    d = ∏ i ∈ Finset.univ.filter (fun i => constr_r k b i ∣ d), constr_r k b i := by
  refine Nat.dvd_antisymm ?_ ?_
  · have hcop : Nat.Coprime d
        (∏ i ∈ Finset.univ.filter (fun i => ¬ constr_r k b i ∣ d), constr_r k b i) := by
      refine Nat.Coprime.prod_right fun i hi => ?_
      exact ((constr_r_prime b i).coprime_iff_not_dvd.mpr (Finset.mem_filter.mp hi).2).symm
    have hd2 : d ∣
        (∏ i ∈ Finset.univ.filter (fun i => ¬ constr_r k b i ∣ d), constr_r k b i) *
          (∏ i ∈ Finset.univ.filter (fun i => constr_r k b i ∣ d), constr_r k b i) := by
      rw [Finset.prod_filter_not_mul_prod_filter]
      exact hd
    exact hcop.dvd_of_dvd_mul_left hd2
  · exact constr_prod_dvd_of_forall fun i hi => (Finset.mem_filter.mp hi).2

/-- The gcd of the full product with the flipped product is exactly `d`. -/
theorem constr_gcd {k : ℕ} {b : Fin k → Bool} {d : ℕ}
    (hds : d ∣ ∏ i : Fin k, constr_r k b i) :
    Nat.gcd (∏ i : Fin k, constr_r k b i) (∏ i : Fin k, constr_r k (constr_b' k b d) i) = d := by
  have hg1 := constr_dvd_eq_prod_filter (b := b)
    (Nat.gcd_dvd_left (∏ i : Fin k, constr_r k b i) (∏ i : Fin k, constr_r k (constr_b' k b d) i))
  refine Nat.dvd_antisymm ?_ ?_
  · rw [hg1]
    refine dvd_trans (Finset.prod_dvd_prod_of_subset _ _ _ ?_)
      (dvd_of_eq (constr_dvd_eq_prod_filter hds).symm)
    intro i hi
    obtain ⟨-, hi2⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hit : constr_r k b i ∣ ∏ j : Fin k, constr_r k (constr_b' k b d) j :=
      dvd_trans hi2 (Nat.gcd_dvd_right _ _)
    obtain ⟨j, -, hjdvd⟩ := (Prime.dvd_finsetProd_iff (constr_r_prime b i).prime _).mp hit
    have heq : constr_r k b i = constr_r k (constr_b' k b d) j :=
      (Nat.prime_dvd_prime_iff_eq (constr_r_prime b i)
        (constr_r_prime (constr_b' k b d) j)).mp hjdvd
    obtain rfl : j = i := (constr_r_inj heq).symm
    exact constr_r_flip.mp heq.symm
  · refine Nat.dvd_gcd hds ?_
    have hd_eq : d = ∏ i ∈ Finset.univ.filter (fun i => constr_r k b i ∣ d),
        constr_r k (constr_b' k b d) i := by
      refine (constr_dvd_eq_prod_filter hds).trans (Finset.prod_congr rfl fun i hi => ?_)
      exact (constr_r_flip.mpr ((Finset.mem_filter.mp hi).2)).symm
    exact dvd_trans (dvd_of_eq hd_eq)
      (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _))

/-- Uniqueness: any product of slot primes having gcd `d` with the full product must be
the flipped product. -/
theorem constr_gcd_unique {k : ℕ} {b b'' : Fin k → Bool} {d : ℕ}
    (h : Nat.gcd (∏ i : Fin k, constr_r k b i) (∏ i : Fin k, constr_r k b'' i) = d) :
    (∏ i : Fin k, constr_r k b'' i) = ∏ i : Fin k, constr_r k (constr_b' k b d) i := by
  have hkey : ∀ i : Fin k, b'' i = constr_b' k b d i := by
    intro i
    have hA : constr_r k b i ∣ ∏ j : Fin k, constr_r k b'' j ↔ b'' i = b i := by
      constructor
      · intro hdvd
        obtain ⟨j, -, hjdvd⟩ := (Prime.dvd_finsetProd_iff (constr_r_prime b i).prime _).mp hdvd
        have heq : constr_r k b i = constr_r k b'' j :=
          (Nat.prime_dvd_prime_iff_eq (constr_r_prime b i) (constr_r_prime b'' j)).mp hjdvd
        obtain rfl : j = i := (constr_r_inj heq).symm
        exact (constr_r_inj_bool heq).symm
      · intro hbi
        have heq : constr_r k b i = constr_r k b'' i := by
          unfold constr_r
          rw [hbi]
        rw [heq]
        exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    have hB : constr_r k b i ∣ d ↔ constr_r k b i ∣ ∏ j : Fin k, constr_r k b'' j := by
      rw [← h, Nat.dvd_gcd_iff]
      exact ⟨fun hh => hh.2, fun hh => ⟨Finset.dvd_prod_of_mem _ (Finset.mem_univ i), hh⟩⟩
    have hC : constr_r k b i ∣ d ↔ constr_b' k b d i = b i := by
      constructor
      · intro hdvd
        exact if_pos hdvd
      · intro hbi
        by_contra hnd
        have h1 : constr_b' k b d i = !(b i) := if_neg hnd
        rw [h1] at hbi
        exact constr_bool_not_ne _ hbi
    have hQS : b'' i = b i ↔ constr_b' k b d i = b i := hA.symm.trans (hB.symm.trans hC)
    cases hb1 : b'' i <;> cases hb2 : constr_b' k b d i <;> cases hb3 : b i <;> simp_all
  rw [funext hkey]

/-- Construction: for `2k` distinct primes `p₁, q₁, …, pₖ, qₖ`, the set of all products
`r₁ * … * rₖ` with `rᵢ ∈ {pᵢ, qᵢ}` is valid and has cardinality `2ᵏ`. -/
theorem exists_isValid (k : ℕ) : ∃ S : Finset ℕ, IsValid S ∧ S.Nonempty ∧ S.card = 2 ^ k := by
  classical
  refine ⟨Finset.univ.image (fun b : Fin k → Bool => ∏ i : Fin k, constr_r k b i),
    ⟨?_, ?_⟩, ?_, ?_⟩
  · intro s hs
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hs
    exact Finset.prod_pos fun i _ => (constr_r_prime b i).pos
  · intro s hs d _hd0 hds
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hs
    refine ⟨∏ i : Fin k, constr_r k (constr_b' k b d) i, ⟨?_, ?_⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨constr_b' k b d, Finset.mem_univ _, rfl⟩
    · exact constr_gcd hds
    · intro t' ht'
      obtain ⟨ht'mem, ht'gcd⟩ := ht'
      obtain ⟨b'', -, rfl⟩ := Finset.mem_image.mp ht'mem
      exact constr_gcd_unique ht'gcd
  · exact Finset.image_nonempty.mpr Finset.univ_nonempty
  · have hinj : Function.Injective (fun b : Fin k → Bool => ∏ i : Fin k, constr_r k b i) := by
      intro b₁ b₂ h
      exact constr_prod_inj h
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ,
      Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

snip end

problem usa2021_p4 (n : ℕ) :
    n ∈ solution_set ↔ ∃ S : Finset ℕ, IsValid S ∧ S.Nonempty ∧ S.card = n := by
  show (∃ k : ℕ, n = 2 ^ k) ↔ ∃ S : Finset ℕ, IsValid S ∧ S.Nonempty ∧ S.card = n
  constructor
  · rintro ⟨k, rfl⟩
    obtain ⟨S, hS, hne, hcard⟩ := exists_isValid k
    exact ⟨S, hS, hne, hcard⟩
  · rintro ⟨S, hS, hne, hcard⟩
    obtain ⟨k, hk⟩ := card_eq_two_pow hS hne
    exact ⟨k, hcard ▸ hk⟩

end Usa2021P4
