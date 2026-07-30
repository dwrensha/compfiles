/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.LinearCombination.Lemmas
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 2025, Problem 5

Find all positive integers $k$ such that: for every positive integer $n$, the sum
$$\binom{n}{0}^k + \binom{n}{1}^k + \cdots + \binom{n}{n}^k$$
is divisible by $n + 1$.
-/

namespace Usa2025P5

open Finset
open scoped Nat

/-- The answer to the problem: all even positive integers `k`. -/
determine solution_set : Set ℕ := { k | Even k }

snip begin

/-!
We follow the solution in Evan Chen's *USAMO 2025 Solution Notes* (§2.2).
The answer is: all even `k`.

* Necessity (`even_of_dvd`): taking `n = 2` gives `3 ∣ 2 + 2 ^ k`, which forces `k` even.
* Sufficiency (`dvd_sum_of_even`): for a prime power `p ^ e ∣ n + 1` with `p * M = n + 1`,
  the key congruence `choose_cast_zmod`,
  `n.choose i ≡ (-1) ^ (i - i / p) * (M - 1).choose (i / p) (mod p ^ e)`,
  is proved by splitting the product `n.choose i * (i)! = ∏ j ∈ range i, (n - j)`
  into the factors with `p ∣ j + 1` and those with `p ∤ j + 1`.
  Summing over blocks of `p` consecutive indices (`sum_modEq`) gives
  `S(n) ≡ p * S(M - 1) (mod p ^ e)`, and strong induction on `n` finishes the proof.
-/

/-- Split a sum over `range (p * M)` into `M` blocks of `p` consecutive terms. -/
lemma sum_range_mul {M' : Type*} [AddCommMonoid M'] (f : ℕ → M') (p M : ℕ) :
    ∑ i ∈ range (p * M), f i = ∑ m ∈ range M, ∑ r ∈ range p, f (p * m + r) := by
  induction M with
  | zero => simp
  | succ M ih => rw [Nat.mul_succ, Finset.sum_range_add, ih, sum_range_succ]

/-- The elements `j` of `range i` with `p ∣ j + 1` are exactly the numbers
`p * (ℓ + 1) - 1` with `ℓ ∈ range (i / p)`. -/
lemma filter_dvd_succ_range (p i : ℕ) (hp : 0 < p) :
    (range i).filter (fun j => p ∣ j + 1)
      = (range (i / p)).image (fun ℓ => p * (ℓ + 1) - 1) := by
  ext j
  simp only [mem_filter, mem_range, mem_image]
  constructor
  · rintro ⟨hji, c, hc⟩
    have hcpos : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with h0 | h0
      · rw [h0, mul_zero] at hc
        exact absurd hc (Nat.succ_ne_zero j)
      · exact h0
    refine ⟨c - 1, ?_, ?_⟩
    · have hcm : c ≤ i / p := by
        rw [Nat.le_div_iff_mul_le hp, mul_comm c p, ← hc]
        exact hji
      exact lt_of_lt_of_le (Nat.sub_lt hcpos one_pos) hcm
    · rw [Nat.sub_add_cancel hcpos]
      omega
  · rintro ⟨ℓ, hℓ, rfl⟩
    have hpos : 0 < p * (ℓ + 1) := Nat.mul_pos hp (Nat.succ_pos ℓ)
    have hle : p * (ℓ + 1) ≤ i := by
      have h2 := mul_le_mul_right hℓ p
      have h3 : p * (i / p) ≤ i := by
        rw [mul_comm]
        exact Nat.div_mul_le_self i p
      exact le_trans h2 h3
    constructor
    · omega
    · exact ⟨ℓ + 1, by omega⟩

/-- The map `ℓ ↦ p * (ℓ + 1) - 1` is injective on `range M`. -/
lemma injOn_mul_succ_sub_one (p M : ℕ) (hp : 0 < p) :
    Set.InjOn (fun ℓ => p * (ℓ + 1) - 1) ↑(range M) := by
  intro a _ b _ hab
  dsimp only at hab
  have ha1 : 0 < p * (a + 1) := Nat.mul_pos hp (Nat.succ_pos a)
  have hb1 : 0 < p * (b + 1) := Nat.mul_pos hp (Nat.succ_pos b)
  have h3 : p * (a + 1) = p * (b + 1) := by omega
  have h4 := Nat.mul_left_cancel hp h3
  omega

/-- There are exactly `i / p` elements `j < i` with `p ∣ j + 1`. -/
lemma card_filter_dvd_succ_range (p i : ℕ) (hp : 0 < p) :
    ((range i).filter (fun j => p ∣ j + 1)).card = i / p := by
  rw [filter_dvd_succ_range p i hp, card_image_of_injOn (injOn_mul_succ_sub_one p (i / p) hp),
    card_range]

/-- Splitting `n.choose i * (i)! = ∏ j ∈ range i, (n - j)` into the factors with `p ∣ j + 1`
and those with `p ∤ j + 1`, and cancelling the common factor `p ^ (i / p) * (i / p)!`,
gives `n.choose i * P = (M - 1).choose (i / p) * R`, where `P = ∏ j, (j + 1)` and
`R = ∏ j, (n - j)` are the products over the `j < i` with `p ∤ j + 1`. -/
lemma choose_mul_prod_filter_eq {p n M i : ℕ} (hp : 0 < p) (hM : p * M = n + 1) (hi : i ≤ n) :
    n.choose i * ∏ j ∈ (range i).filter (fun j => ¬ p ∣ j + 1), (j + 1)
      = (M - 1).choose (i / p) * ∏ j ∈ (range i).filter (fun j => ¬ p ∣ j + 1), (n - j) := by
  have hprod : ∀ f : ℕ → ℕ,
      ∏ j ∈ (range i).filter (fun j => p ∣ j + 1), f j
        = ∏ ℓ ∈ range (i / p), f (p * (ℓ + 1) - 1) := by
    intro f
    rw [filter_dvd_succ_range p i hp, prod_image (injOn_mul_succ_sub_one p (i / p) hp)]
  have hchoose : n.choose i * (i)! = ∏ j ∈ range i, (n - j) := by
    have h := Nat.descFactorial_eq_factorial_mul_choose n i
    rw [Nat.descFactorial_eq_prod_range] at h
    rw [h, mul_comm]
  have hfact : (i)! = ∏ j ∈ range i, (j + 1) := Nat.factorial_eq_prod_range_add_one i
  have hsplit1 : (∏ j ∈ (range i).filter (fun j => p ∣ j + 1), (j + 1))
        * (∏ j ∈ (range i).filter (fun j => ¬ p ∣ j + 1), (j + 1))
      = ∏ j ∈ range i, (j + 1) := prod_filter_mul_prod_filter_not _ _ _
  have hsplit2 : (∏ j ∈ (range i).filter (fun j => p ∣ j + 1), (n - j))
        * (∏ j ∈ (range i).filter (fun j => ¬ p ∣ j + 1), (n - j))
      = ∏ j ∈ range i, (n - j) := prod_filter_mul_prod_filter_not _ _ _
  have hdvd1 : ∏ j ∈ (range i).filter (fun j => p ∣ j + 1), (j + 1)
      = p ^ (i / p) * (i / p)! := by
    rw [hprod]
    trans (∏ ℓ ∈ range (i / p), p * (ℓ + 1))
    · exact prod_congr rfl
        (fun ℓ _ => Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.mul_pos hp (Nat.succ_pos ℓ))))
    · rw [prod_mul_distrib, prod_const, card_range, ← Nat.factorial_eq_prod_range_add_one]
  have hdvd2 : ∏ j ∈ (range i).filter (fun j => p ∣ j + 1), (n - j)
      = p ^ (i / p) * ((i / p)! * (M - 1).choose (i / p)) := by
    rw [hprod]
    have step : ∀ ℓ ∈ range (i / p), n - (p * (ℓ + 1) - 1) = p * (M - 1 - ℓ) := by
      intro ℓ hℓ
      have hle : p * (ℓ + 1) ≤ i := by
        have h2 := mul_le_mul_right (mem_range.mp hℓ) p
        have h3 : p * (i / p) ≤ i := by
          rw [mul_comm]
          exact Nat.div_mul_le_self i p
        exact le_trans h2 h3
      have hpos : 0 < p * (ℓ + 1) := Nat.mul_pos hp (Nat.succ_pos ℓ)
      have h1 : n - (p * (ℓ + 1) - 1) = n + 1 - p * (ℓ + 1) := by omega
      rw [h1, ← hM, ← Nat.mul_sub_left_distrib, Nat.sub_sub, add_comm 1 ℓ]
    trans (∏ ℓ ∈ range (i / p), p * (M - 1 - ℓ))
    · exact prod_congr rfl step
    · rw [prod_mul_distrib, prod_const, card_range]
      congr 1
      have h2 := Nat.descFactorial_eq_factorial_mul_choose (M - 1) (i / p)
      rw [Nat.descFactorial_eq_prod_range] at h2
      exact h2
  rw [hfact, ← hsplit1, hdvd1, ← hsplit2, hdvd2] at hchoose
  apply Nat.mul_left_cancel (Nat.mul_pos (pow_pos hp _) (Nat.factorial_pos _))
  calc (p ^ (i / p) * (i / p)!)
        * (n.choose i * ∏ j ∈ (range i).filter (fun j => ¬ p ∣ j + 1), (j + 1))
      = n.choose i
        * ((p ^ (i / p) * (i / p)!) * ∏ j ∈ (range i).filter (fun j => ¬ p ∣ j + 1), (j + 1)) :=
        by ring
    _ = (p ^ (i / p) * ((i / p)! * (M - 1).choose (i / p)))
        * ∏ j ∈ (range i).filter (fun j => ¬ p ∣ j + 1), (n - j) := hchoose
    _ = (p ^ (i / p) * (i / p)!)
        * ((M - 1).choose (i / p) * ∏ j ∈ (range i).filter (fun j => ¬ p ∣ j + 1), (n - j)) :=
        by ring

/-- The key congruence: if the prime power `p ^ e` divides `n + 1` and `p * M = n + 1`,
then `n.choose i ≡ (-1) ^ (i - i / p) * (M - 1).choose (i / p)` modulo `p ^ e`. -/
lemma choose_cast_zmod {p e n M i : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hdvd : p ^ e ∣ n + 1)
    (hM : p * M = n + 1) (hi : i ≤ n) :
    ((n.choose i : ℕ) : ZMod (p ^ e))
      = (-1) ^ (i - i / p) * (((M - 1).choose (i / p) : ℕ) : ZMod (p ^ e)) := by
  have hn1 : ((n + 1 : ℕ) : ZMod (p ^ e)) = 0 := by
    rw [← Nat.cast_zero, ZMod.natCast_eq_natCast_iff, Nat.modEq_zero_iff_dvd]
    exact hdvd
  have hprod := choose_mul_prod_filter_eq hp.pos hM hi
  have hcard : ((range i).filter (fun j => ¬ p ∣ j + 1)).card = i - i / p := by
    have h1 : ((range i).filter (fun j => p ∣ j + 1)).card
        + ((range i).filter (fun j => ¬ p ∣ j + 1)).card = (range i).card :=
      card_filter_add_card_filter_not _
    rw [card_range, card_filter_dvd_succ_range p i hp.pos] at h1
    omega
  have hcast : ((∏ j ∈ (range i).filter (fun j => ¬ p ∣ j + 1), (n - j) : ℕ) : ZMod (p ^ e))
      = (-1) ^ (i - i / p)
        * ((∏ j ∈ (range i).filter (fun j => ¬ p ∣ j + 1), (j + 1) : ℕ) : ZMod (p ^ e)) := by
    have hterm : ∀ j ∈ (range i).filter (fun j => ¬ p ∣ j + 1),
        ((n - j : ℕ) : ZMod (p ^ e)) = -(((j + 1 : ℕ)) : ZMod (p ^ e)) := by
      intro j hj
      have hj' : j ≤ n := le_trans (Nat.le_of_lt (mem_range.mp (mem_filter.mp hj).1)) hi
      have hn : ((n : ℕ) : ZMod (p ^ e)) = -1 := by
        have h := hn1
        rw [Nat.cast_add, Nat.cast_one] at h
        exact eq_neg_of_add_eq_zero_left h
      rw [Nat.cast_sub hj', hn]
      push_cast
      ring
    rw [Nat.cast_prod, Nat.cast_prod, ← hcard, ← prod_const, ← prod_mul_distrib]
    exact prod_congr rfl (fun j hj => by rw [hterm j hj, neg_eq_neg_one_mul])
  have hcastprod : ((n.choose i : ℕ) : ZMod (p ^ e))
        * ((∏ j ∈ (range i).filter (fun j => ¬ p ∣ j + 1), (j + 1) : ℕ) : ZMod (p ^ e))
      = (((M - 1).choose (i / p) : ℕ) : ZMod (p ^ e))
        * ((∏ j ∈ (range i).filter (fun j => ¬ p ∣ j + 1), (n - j) : ℕ) : ZMod (p ^ e)) := by
    rw [← Nat.cast_mul, ← Nat.cast_mul, hprod]
  rw [hcast] at hcastprod
  have hcop : (∏ j ∈ (range i).filter (fun j => ¬ p ∣ j + 1), (j + 1)).Coprime (p ^ e) := by
    rw [Nat.coprime_prod_left_iff]
    intro j hj
    rw [Nat.coprime_pow_right_iff he, Nat.coprime_comm]
    exact (hp.coprime_iff_not_dvd).mpr (mem_filter.mp hj).2
  have hunit : IsUnit
      (((∏ j ∈ (range i).filter (fun j => ¬ p ∣ j + 1), (j + 1)) : ℕ) : ZMod (p ^ e)) := by
    rw [← ZMod.coe_unitOfCoprime _ hcop]
    exact Units.isUnit _
  have key : ((∏ j ∈ (range i).filter (fun j => ¬ p ∣ j + 1), (j + 1) : ℕ) : ZMod (p ^ e))
        * ((n.choose i : ℕ) : ZMod (p ^ e))
      = ((∏ j ∈ (range i).filter (fun j => ¬ p ∣ j + 1), (j + 1) : ℕ) : ZMod (p ^ e))
        * ((-1) ^ (i - i / p) * (((M - 1).choose (i / p) : ℕ) : ZMod (p ^ e))) := by
    linear_combination hcastprod
  exact hunit.mul_left_cancel key

/-- Summing the key congruence over blocks of `p` consecutive indices: if `k` is even,
`p ^ e ∣ n + 1` and `p * M = n + 1`, then
`∑ i, (n.choose i) ^ k ≡ p * ∑ m, ((M - 1).choose m) ^ k` modulo `p ^ e`. -/
lemma sum_modEq {p e n M k : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hdvd : p ^ e ∣ n + 1)
    (hk : Even k) (hM : p * M = n + 1) :
    (∑ i ∈ range (n + 1), (n.choose i) ^ k)
      ≡ p * (∑ m ∈ range M, ((M - 1).choose m) ^ k) [MOD p ^ e] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast [Nat.cast_sum, Nat.cast_pow]
  rw [← hM]
  calc ∑ i ∈ range (p * M), ((n.choose i : ℕ) : ZMod (p ^ e)) ^ k
      = ∑ m ∈ range M, ∑ r ∈ range p, ((n.choose (p * m + r) : ℕ) : ZMod (p ^ e)) ^ k :=
        sum_range_mul _ _ _
    _ = ∑ m ∈ range M,
          ((p : ℕ) : ZMod (p ^ e)) * (((M - 1).choose m : ℕ) : ZMod (p ^ e)) ^ k := by
        apply sum_congr rfl
        intro m' hm'
        have hnr : ∀ r ∈ range p, p * m' + r ≤ n := by
          intro r hr
          have hmM : p * (m' + 1) ≤ p * M := mul_le_mul_right (mem_range.mp hm') p
          have h1 : p * m' + r < p * (m' + 1) := by
            have hr' : r < p := mem_range.mp hr
            have heq : p * (m' + 1) = p * m' + p := by rw [mul_add, mul_one]
            omega
          have h2 : p * (m' + 1) ≤ n + 1 := hM ▸ hmM
          omega
        have hdiv : ∀ r ∈ range p, (p * m' + r) / p = m' := by
          intro r hr
          rw [Nat.mul_add_div hp.pos, Nat.div_eq_of_lt (mem_range.mp hr), add_zero]
        have hterm : ∀ r ∈ range p, ((n.choose (p * m' + r) : ℕ) : ZMod (p ^ e)) ^ k
            = (((M - 1).choose m' : ℕ) : ZMod (p ^ e)) ^ k := by
          intro r hr
          rw [choose_cast_zmod hp he hdvd hM (hnr r hr), hdiv r hr, mul_pow, ← pow_mul,
            Even.neg_one_pow (hk.mul_left _), one_mul]
        calc ∑ r ∈ range p, ((n.choose (p * m' + r) : ℕ) : ZMod (p ^ e)) ^ k
            = ∑ r ∈ range p, (((M - 1).choose m' : ℕ) : ZMod (p ^ e)) ^ k :=
              sum_congr rfl hterm
          _ = (range p).card • (((M - 1).choose m' : ℕ) : ZMod (p ^ e)) ^ k := sum_const _
          _ = ((p : ℕ) : ZMod (p ^ e)) * (((M - 1).choose m' : ℕ) : ZMod (p ^ e)) ^ k := by
              rw [card_range, nsmul_eq_mul]
    _ = ((p : ℕ) : ZMod (p ^ e))
          * ∑ m ∈ range M, (((M - 1).choose m : ℕ) : ZMod (p ^ e)) ^ k := by
        rw [← Finset.mul_sum]

/-- Sufficiency: for even `k`, `n + 1` divides `∑ i ∈ range (n + 1), (n.choose i) ^ k`
for every positive `n`. Proof by strong induction on `n`: for each prime `p` with `p ^ e`
exactly dividing `n + 1`, `sum_modEq` reduces the claim modulo `p ^ e` to the induction
hypothesis at `M - 1`, where `p * M = n + 1`. -/
lemma dvd_sum_of_even {k : ℕ} (hk : Even k) (n : ℕ) :
    0 < n → (n + 1) ∣ ∑ i ∈ range (n + 1), (n.choose i) ^ k := by
  refine Nat.strong_induction_on n (fun n IH hn => ?_)
  have hN : n + 1 ≠ 0 := by omega
  have hSpos : 0 < ∑ i ∈ range (n + 1), (n.choose i) ^ k := by
    have h1 : (n.choose 0) ^ k = 1 := by rw [Nat.choose_zero_right, one_pow]
    have h2 : (n.choose 0) ^ k ≤ ∑ i ∈ range (n + 1), (n.choose i) ^ k :=
      Finset.single_le_sum (f := fun i => (n.choose i) ^ k) (fun i _ => Nat.zero_le _)
        (mem_range.mpr (by omega : 0 < n + 1))
    omega
  rw [← Nat.factorization_le_iff_dvd hN (Nat.pos_iff_ne_zero.mp hSpos), Finsupp.le_def]
  intro p
  by_cases hpp : p.Prime
  · by_cases hpd : p ∣ n + 1
    · have hpos : 0 < (n + 1).factorization p := hpp.factorization_pos_of_dvd hN hpd
      rw [← Nat.Prime.pow_dvd_iff_le_factorization hpp (Nat.pos_iff_ne_zero.mp hSpos)]
      set e := (n + 1).factorization p with he
      have hdvd : p ^ e ∣ n + 1 := Nat.ordProj_dvd _ _
      set M := (n + 1) / p
      have hM : p * M = n + 1 := Nat.mul_div_cancel' hpd
      have hMpos : 0 < M := Nat.div_pos (Nat.le_of_dvd (by omega : 0 < n + 1) hpd) hpp.pos
      have hmod := sum_modEq hpp (by omega : 1 ≤ e) hdvd hk hM
      have hprev : p ^ (e - 1) ∣ ∑ m ∈ range M, ((M - 1).choose m) ^ k := by
        by_cases he1 : e = 1
        · rw [he1, Nat.sub_self, pow_zero]
          exact one_dvd _
        · have hpe1 : p ^ (e - 1) ∣ M := by
            have h1 : p * p ^ (e - 1) = p ^ e := by
              rw [mul_comm, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ e)]
            have h2 : p * p ^ (e - 1) ∣ p * M := by
              rw [h1, hM]
              exact hdvd
            exact (Nat.mul_dvd_mul_iff_left hpp.pos).mp h2
          have hM2 : 2 ≤ M := by
            have h4 : p ^ 1 ≤ p ^ (e - 1) := Nat.pow_le_pow_right hpp.pos (by omega)
            rw [pow_one] at h4
            exact le_trans (le_trans hpp.two_le h4) (Nat.le_of_dvd hMpos hpe1)
          have hMn : M - 1 < n := by
            have h2M : 2 * M ≤ n + 1 := by
              rw [← hM]
              exact mul_le_mul_left hpp.two_le M
            omega
          have hIH := IH (M - 1) hMn (by omega)
          rw [Nat.sub_add_cancel (by omega : 1 ≤ M)] at hIH
          exact dvd_trans hpe1 hIH
      have hpe : p * p ^ (e - 1) = p ^ e := by
        rw [mul_comm, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ e)]
      have hdvd2 : p ^ e ∣ p * (∑ m ∈ range M, ((M - 1).choose m) ^ k) := by
        rw [← hpe]
        exact mul_dvd_mul_left p hprev
      exact Nat.modEq_zero_iff_dvd.mp (hmod.trans (Nat.modEq_zero_iff_dvd.mpr hdvd2))
    · rw [Nat.factorization_eq_zero_of_not_dvd hpd]
      exact Nat.zero_le _
  · have h0 : (n + 1).factorization p = 0 :=
      (Nat.factorization_eq_zero_iff _ _).mpr (Or.inl hpp)
    rw [h0]
    exact Nat.zero_le _

/-- Necessity: taking `n = 2`, the divisibility `3 ∣ 2 + 2 ^ k` forces `k` to be even. -/
lemma even_of_dvd {k : ℕ}
    (h : ∀ n : ℕ, 0 < n → (n + 1) ∣ ∑ i ∈ range (n + 1), (n.choose i) ^ k) :
    Even k := by
  by_contra hne
  rw [Nat.not_even_iff_odd] at hne
  have h2 : (3 : ℕ) ∣ ∑ i ∈ range 3, ((2 : ℕ).choose i) ^ k := h 2 (by omega)
  have hS : ∑ i ∈ range 3, ((2 : ℕ).choose i) ^ k = 2 + 2 ^ k := by
    have h0 : ∑ i ∈ range 0, ((2 : ℕ).choose i) ^ k = 0 := sum_range_zero _
    have h1 : ∑ i ∈ range 1, ((2 : ℕ).choose i) ^ k = ((2 : ℕ).choose 0) ^ k := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, sum_range_succ, h0, zero_add]
    have h2' : ∑ i ∈ range 2, ((2 : ℕ).choose i) ^ k
        = ((2 : ℕ).choose 0) ^ k + ((2 : ℕ).choose 1) ^ k := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, sum_range_succ, h1]
    rw [show (3 : ℕ) = 2 + 1 from rfl, sum_range_succ, h2',
      Nat.choose_zero_right, Nat.choose_one_right, Nat.choose_self, one_pow]
    ring
  rw [hS] at h2
  have h3 : ((2 + 2 ^ k : ℕ) : ZMod 3) = 0 := by
    rw [← Nat.cast_zero, ZMod.natCast_eq_natCast_iff, Nat.modEq_zero_iff_dvd]
    exact h2
  have h2k : ((2 : ℕ) : ZMod 3) ^ k = -1 := by
    have h2eq : ((2 : ℕ) : ZMod 3) = -1 := by decide
    rw [h2eq, hne.neg_one_pow]
  rw [Nat.cast_add, Nat.cast_pow, h2k, Nat.cast_ofNat] at h3
  exact absurd h3 (by decide)

snip end

problem usa2025_p5 (k : ℕ) (_hk : 0 < k) :
    k ∈ solution_set ↔ ∀ n : ℕ, 0 < n → (n + 1) ∣ ∑ i ∈ range (n + 1), (n.choose i) ^ k := by
  constructor
  · intro hkev
    exact dvd_sum_of_even hkev
  · intro h
    exact even_of_dvd h

end Usa2025P5
