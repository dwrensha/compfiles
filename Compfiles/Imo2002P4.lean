/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Rat.Star
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Preprocessing
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 2002, Problem 4

The positive divisors of the integer n > 1 are d₁ < d₂ < ... < dₖ, so that
d₁ = 1 and dₖ = n. Let d = d₁d₂ + d₂d₃ + ... + dₖ₋₁dₖ.
Show that d < n² and find all n for which d divides n².
-/

namespace Imo2002P4

open Finset

/-- The `i`-th smallest positive divisor of `n` (meaningful for `i < n.divisors.card`). -/
noncomputable def nthDiv (n i : ℕ) : ℕ :=
  if h : i < n.divisors.card then n.divisors.orderEmbOfFin rfl ⟨i, h⟩ else 1

/-- The sum `d₁d₂ + d₂d₃ + ... + dₖ₋₁dₖ` over the ordered positive divisors of `n`. -/
noncomputable def pairSum (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n.divisors.card - 1), nthDiv n i * nthDiv n (i + 1)

snip begin

lemma nthDiv_eq (n i : ℕ) (h : i < n.divisors.card) :
    nthDiv n i = n.divisors.orderEmbOfFin rfl ⟨i, h⟩ := by
  unfold nthDiv
  rw [dite_eq_left h]

lemma pairSum_eq (n : ℕ) :
    pairSum n = ∑ i ∈ Finset.range (n.divisors.card - 1), nthDiv n i * nthDiv n (i + 1) :=
  rfl

lemma card_divisors_ge_two (n : ℕ) (hn : 1 < n) : 2 ≤ n.divisors.card := by
  have hsub : ({1, n} : Finset ℕ) ⊆ n.divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h
    · rw [h]; exact Nat.mem_divisors.mpr ⟨one_dvd n, by omega⟩
    · rw [h]; exact Nat.mem_divisors.mpr ⟨dvd_refl n, by omega⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_pair (show (1 : ℕ) ≠ n by omega)] at hle
  exact hle

lemma nthDiv_zero (n : ℕ) (hn : 1 < n) : nthDiv n 0 = 1 := by
  have hk : 0 < n.divisors.card := by have h2 := card_divisors_ge_two n hn; omega
  rw [nthDiv_eq n 0 hk, Finset.orderEmbOfFin_zero rfl hk]
  apply le_antisymm
  · exact Finset.min'_le _ 1 (Nat.mem_divisors.mpr ⟨one_dvd n, by omega⟩)
  · exact Finset.le_min' _ _ 1 (fun y hy ↦ Nat.pos_of_mem_divisors hy)

lemma nthDiv_last (n : ℕ) (hn : 1 < n) (h : n.divisors.card - 1 < n.divisors.card) :
    nthDiv n (n.divisors.card - 1) = n := by
  have hk : 0 < n.divisors.card := by omega
  rw [nthDiv_eq n _ h, Finset.orderEmbOfFin_last rfl hk]
  apply le_antisymm
  · exact Finset.max'_le _ _ _ (fun y hy ↦ Nat.le_of_dvd (by omega) (Nat.mem_divisors.mp hy).1)
  · exact Finset.le_max' _ n (Nat.mem_divisors.mpr ⟨dvd_refl n, by omega⟩)

lemma nthDiv_ge (n : ℕ) (_hn : 1 < n) : ∀ i, i < n.divisors.card → i + 1 ≤ nthDiv n i := by
  intro i
  induction i with
  | zero =>
    intro h
    rw [nthDiv_eq n 0 h]
    exact Nat.pos_of_mem_divisors (Finset.orderEmbOfFin_mem n.divisors rfl ⟨0, h⟩)
  | succ m ih =>
    intro h
    have hm : m < n.divisors.card := by omega
    have h1 := ih hm
    rw [nthDiv_eq n (m + 1) h]
    have h2 : n.divisors.orderEmbOfFin rfl ⟨m, hm⟩ < n.divisors.orderEmbOfFin rfl ⟨m + 1, h⟩ :=
      (n.divisors.orderEmbOfFin rfl).strictMono (Fin.lt_def.mpr (Nat.lt_succ_self m))
    rw [nthDiv_eq n m hm] at h1
    exact Nat.succ_le_of_lt (lt_of_le_of_lt h1 h2)

/-- Division is strictly antitone on the divisors of a positive integer. -/
lemma div_lt_div_of_dvd_of_lt {a b n : ℕ} (hn0 : 0 < n) (ha : a ∣ n) (hb : b ∣ n)
    (ha0 : 0 < a) (hab : a < b) : n / b < n / a := by
  have hb0 : 0 < b := ha0.trans hab
  have hpos : 0 < n / b := Nat.div_pos (Nat.le_of_dvd hn0 hb) hb0
  have h1 : a * (n / a) = n := Nat.mul_div_cancel' ha
  have h2 : b * (n / b) = n := Nat.mul_div_cancel' hb
  by_contra hcon
  push Not at hcon
  have h3 : a * (n / a) ≤ a * (n / b) := mul_le_mul_right hcon a
  have h4 : a * (n / b) < b * (n / b) := mul_lt_mul_of_pos_right hab hpos
  omega

/-- Pairing of divisors: the `i`-th smallest times the `i`-th largest equals `n`. -/
lemma nthDiv_pair (n : ℕ) (hn : 1 < n) (i : ℕ) (hi : i < n.divisors.card) :
    nthDiv n i * nthDiv n (n.divisors.card - 1 - i) = n := by
  have hn0 : 0 < n := by omega
  have hk2 := card_divisors_ge_two n hn
  have hrev : ∀ j : Fin n.divisors.card, n.divisors.card - 1 - j.val < n.divisors.card := by
    intro j
    have hj := j.2
    omega
  have hfs : ∀ j : Fin n.divisors.card,
      n / n.divisors.orderEmbOfFin rfl ⟨n.divisors.card - 1 - j.val, hrev j⟩ ∈ n.divisors := by
    intro j
    have hd : n.divisors.orderEmbOfFin rfl ⟨n.divisors.card - 1 - j.val, hrev j⟩ ∣ n :=
      (Nat.mem_divisors.mp (Finset.orderEmbOfFin_mem n.divisors rfl _)).1
    exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hd, hn0.ne'⟩
  have hmono : StrictMono (fun j : Fin n.divisors.card ↦
      n / n.divisors.orderEmbOfFin rfl ⟨n.divisors.card - 1 - j.val, hrev j⟩) := by
    intro a b hab
    show n / n.divisors.orderEmbOfFin rfl ⟨n.divisors.card - 1 - a.val, hrev a⟩ <
      n / n.divisors.orderEmbOfFin rfl ⟨n.divisors.card - 1 - b.val, hrev b⟩
    have hval : n.divisors.card - 1 - b.val < n.divisors.card - 1 - a.val := by
      have ha2 := a.2
      have hb2 := b.2
      have habv : a.val < b.val := Fin.lt_def.mp hab
      omega
    have hlt : n.divisors.orderEmbOfFin rfl ⟨n.divisors.card - 1 - b.val, hrev b⟩ <
        n.divisors.orderEmbOfFin rfl ⟨n.divisors.card - 1 - a.val, hrev a⟩ :=
      (n.divisors.orderEmbOfFin rfl).strictMono (Fin.lt_def.mpr hval)
    exact div_lt_div_of_dvd_of_lt hn0
      (Nat.mem_divisors.mp (Finset.orderEmbOfFin_mem n.divisors rfl _)).1
      (Nat.mem_divisors.mp (Finset.orderEmbOfFin_mem n.divisors rfl _)).1
      (Nat.pos_of_mem_divisors (Finset.orderEmbOfFin_mem n.divisors rfl _))
      hlt
  have hu := Finset.orderEmbOfFin_unique (rfl : n.divisors.card = n.divisors.card) hfs hmono
  have hi2 : n.divisors.card - 1 - i < n.divisors.card := by omega
  have happ : n / n.divisors.orderEmbOfFin rfl
        ⟨n.divisors.card - 1 - (n.divisors.card - 1 - i), hrev ⟨n.divisors.card - 1 - i, hi2⟩⟩ =
      n.divisors.orderEmbOfFin rfl ⟨n.divisors.card - 1 - i, hi2⟩ :=
    congrFun hu ⟨n.divisors.card - 1 - i, hi2⟩
  have hval : (⟨n.divisors.card - 1 - (n.divisors.card - 1 - i),
        hrev ⟨n.divisors.card - 1 - i, hi2⟩⟩ : Fin n.divisors.card) = ⟨i, hi⟩ := by
    apply Fin.ext
    show n.divisors.card - 1 - (n.divisors.card - 1 - i) = i
    omega
  rw [hval] at happ
  rw [nthDiv_eq n i hi, nthDiv_eq n (n.divisors.card - 1 - i) hi2, ← happ]
  exact Nat.mul_div_cancel' (Nat.mem_divisors.mp (Finset.orderEmbOfFin_mem n.divisors rfl ⟨i, hi⟩)).1

/-- The second smallest divisor of `n > 1` is its least prime factor. -/
lemma nthDiv_one (n : ℕ) (hn : 1 < n) : nthDiv n 1 = n.minFac := by
  have hn0 : 0 < n := by omega
  have hk2 := card_divisors_ge_two n hn
  have h1k : 1 < n.divisors.card := by omega
  have h0k : 0 < n.divisors.card := by omega
  rw [nthDiv_eq n 1 h1k]
  apply le_antisymm
  · -- `e ⟨1⟩ ≤ n.minFac`: `n.minFac` is a divisor `≥ 2`, hence has index `≥ 1`.
    have hmin : n.minFac ∈ n.divisors := Nat.mem_divisors.mpr ⟨Nat.minFac_dvd n, hn0.ne'⟩
    have hmin' : n.minFac ∈ Set.range ⇑(n.divisors.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact hmin
    obtain ⟨j, hj⟩ := hmin'
    have he0 : n.divisors.orderEmbOfFin rfl ⟨0, h0k⟩ = 1 := by
      rw [← nthDiv_eq n 0 h0k]
      exact nthDiv_zero n hn
    have hj0 : j ≠ ⟨0, h0k⟩ := by
      intro hcon
      rw [hcon, he0] at hj
      have hmf2 : 2 ≤ n.minFac := (Nat.minFac_prime (show n ≠ 1 by omega)).two_le
      omega
    have hle : (⟨1, h1k⟩ : Fin n.divisors.card) ≤ j := by
      by_contra hc
      push Not at hc
      have hc' : j.val < 1 := Fin.lt_def.mp hc
      have hz : j.val = 0 := by omega
      exact hj0 (Fin.ext hz)
    have hmono : n.divisors.orderEmbOfFin rfl ⟨1, h1k⟩ ≤ n.divisors.orderEmbOfFin rfl j := by
      rcases eq_or_lt_of_le hle with h | h
      · rw [h]
      · exact le_of_lt ((n.divisors.orderEmbOfFin rfl).strictMono h)
    rw [hj] at hmono
    exact hmono
  · -- `n.minFac ≤ e ⟨1⟩`: `e ⟨1⟩` is a divisor that is `≥ 2`.
    have hdvd : n.divisors.orderEmbOfFin rfl ⟨1, h1k⟩ ∣ n :=
      (Nat.mem_divisors.mp (Finset.orderEmbOfFin_mem n.divisors rfl _)).1
    have hge : 2 ≤ n.divisors.orderEmbOfFin rfl ⟨1, h1k⟩ := by
      have h := nthDiv_ge n hn 1 h1k
      rw [nthDiv_eq n 1 h1k] at h
      exact h
    exact Nat.minFac_le_of_dvd hge hdvd

/-- Telescoping sum used in part (a). -/
lemma tele (m : ℕ) :
    ∑ j ∈ Finset.range m, (1 / ((j : ℚ) + 1) - 1 / ((j : ℚ) + 1 + 1)) =
      1 - 1 / ((m : ℚ) + 1) := by
  have ht := Finset.sum_range_sub' (fun j : ℕ ↦ (1 : ℚ) / ((j : ℚ) + 1)) m
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] at ht
  rw [ht]
  norm_num

/-- Part (a): the sum is less than `n ^ 2`. -/
lemma pairSum_lt (n : ℕ) (hn : 1 < n) : pairSum n < n ^ 2 := by
  have hn0 : 0 < n := by omega
  have hk2 := card_divisors_ge_two n hn
  have hQ : (pairSum n : ℚ) < (n : ℚ) ^ 2 := by
    have h1 : (pairSum n : ℚ) = ∑ i ∈ Finset.range (n.divisors.card - 1),
        (nthDiv n i : ℚ) * (nthDiv n (i + 1) : ℚ) := by
      rw [pairSum_eq]
      norm_cast
    rw [h1]
    have hb : ∀ i ∈ Finset.range (n.divisors.card - 1),
        (nthDiv n i : ℚ) * (nthDiv n (i + 1) : ℚ) ≤
          (n : ℚ) ^ 2 / (((n.divisors.card - i) * (n.divisors.card - 1 - i) : ℕ) : ℚ) := by
      intro i hi
      rw [Finset.mem_range] at hi
      have hsub : n.divisors.card - 1 - (i + 1) = n.divisors.card - 2 - i := by omega
      have hnat : nthDiv n i * nthDiv n (i + 1) *
          ((n.divisors.card - i) * (n.divisors.card - 1 - i)) ≤ n ^ 2 := by
        have hp1 := nthDiv_pair n hn i (by omega)
        have hp2 := nthDiv_pair n hn (i + 1) (by omega)
        rw [hsub] at hp2
        have hg1 := nthDiv_ge n hn (n.divisors.card - 1 - i) (by omega)
        have hg2 := nthDiv_ge n hn (n.divisors.card - 2 - i) (by omega)
        have h1a : n.divisors.card - 1 - i + 1 = n.divisors.card - i := by omega
        have h2a : n.divisors.card - 2 - i + 1 = n.divisors.card - 1 - i := by omega
        rw [h1a] at hg1
        rw [h2a] at hg2
        calc nthDiv n i * nthDiv n (i + 1) * ((n.divisors.card - i) * (n.divisors.card - 1 - i))
            ≤ nthDiv n i * nthDiv n (i + 1) *
                (nthDiv n (n.divisors.card - 1 - i) * nthDiv n (n.divisors.card - 2 - i)) :=
              mul_le_mul_right (mul_le_mul hg1 hg2 (Nat.zero_le _) (Nat.zero_le _)) _
          _ = (nthDiv n i * nthDiv n (n.divisors.card - 1 - i)) *
                (nthDiv n (i + 1) * nthDiv n (n.divisors.card - 2 - i)) := by ring
          _ = n * n := by rw [hp1, hp2]
          _ = n ^ 2 := by rw [pow_two]
      have hM : (0 : ℚ) < (((n.divisors.card - i) * (n.divisors.card - 1 - i) : ℕ) : ℚ) := by
        have hM0 : 0 < (n.divisors.card - i) * (n.divisors.card - 1 - i) :=
          Nat.mul_pos (by omega) (by omega)
        exact_mod_cast hM0
      rw [le_div_iff₀ hM]
      exact_mod_cast hnat
    have hsum1 : (∑ i ∈ Finset.range (n.divisors.card - 1),
          (nthDiv n i : ℚ) * (nthDiv n (i + 1) : ℚ)) ≤
        ∑ i ∈ Finset.range (n.divisors.card - 1),
          (n : ℚ) ^ 2 / (((n.divisors.card - i) * (n.divisors.card - 1 - i) : ℕ) : ℚ) :=
      Finset.sum_le_sum hb
    have hsum2 : (∑ i ∈ Finset.range (n.divisors.card - 1),
          (n : ℚ) ^ 2 / (((n.divisors.card - i) * (n.divisors.card - 1 - i) : ℕ) : ℚ)) =
        ∑ j ∈ Finset.range (n.divisors.card - 1),
          (n : ℚ) ^ 2 / (((j + 2) * (j + 1) : ℕ) : ℚ) := by
      rw [← Finset.sum_range_reflect (fun j ↦ (n : ℚ) ^ 2 / (((j + 2) * (j + 1) : ℕ) : ℚ))
          (n.divisors.card - 1)]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      show (n : ℚ) ^ 2 / (((n.divisors.card - i) * (n.divisors.card - 1 - i) : ℕ) : ℚ) =
        (n : ℚ) ^ 2 /
          ((((n.divisors.card - 1 - 1 - i) + 2) * ((n.divisors.card - 1 - 1 - i) + 1) : ℕ) : ℚ)
      have e1 : n.divisors.card - 1 - 1 - i + 2 = n.divisors.card - i := by omega
      have e2 : n.divisors.card - 1 - 1 - i + 1 = n.divisors.card - 1 - i := by omega
      rw [e1, e2]
    have hsum3 : (∑ j ∈ Finset.range (n.divisors.card - 1),
          (n : ℚ) ^ 2 / (((j + 2) * (j + 1) : ℕ) : ℚ)) =
        ∑ j ∈ Finset.range (n.divisors.card - 1),
          (n : ℚ) ^ 2 * (1 / ((j : ℚ) + 1) - 1 / ((j : ℚ) + 1 + 1)) := by
      apply Finset.sum_congr rfl
      intro j _
      have h1p : ((j : ℚ) + 1) ≠ 0 := by positivity
      have h2p : ((j : ℚ) + 1 + 1) ≠ 0 := by positivity
      have h3p : ((j : ℚ) + 2) ≠ 0 := by positivity
      push_cast
      field_simp [h1p, h2p, h3p]
      ring
    have hsum4 : (∑ j ∈ Finset.range (n.divisors.card - 1),
          (n : ℚ) ^ 2 * (1 / ((j : ℚ) + 1) - 1 / ((j : ℚ) + 1 + 1))) =
          (n : ℚ) ^ 2 * (1 - 1 / (n.divisors.card : ℚ)) := by
      rw [← Finset.mul_sum]
      congr 1
      have htele := tele (n.divisors.card - 1)
      rw [htele]
      have hkc : ((n.divisors.card - 1 : ℕ) : ℚ) + 1 = (n.divisors.card : ℚ) := by
        rw [Nat.cast_sub (show 1 ≤ n.divisors.card by omega)]
        push_cast
        ring
      rw [hkc]
    have hsum5 : (n : ℚ) ^ 2 * (1 - 1 / (n.divisors.card : ℚ)) < (n : ℚ) ^ 2 := by
      have hkn : (0 : ℚ) < (n.divisors.card : ℚ) := by
        exact_mod_cast (by omega : 0 < n.divisors.card)
      have hn2 : (0 : ℚ) < (n : ℚ) ^ 2 := by
        have hn0' : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn0
        positivity
      have hpos : (0 : ℚ) < (n : ℚ) ^ 2 / (n.divisors.card : ℚ) := div_pos hn2 hkn
      have heq : (n : ℚ) ^ 2 * (1 - 1 / (n.divisors.card : ℚ)) =
          (n : ℚ) ^ 2 - (n : ℚ) ^ 2 / (n.divisors.card : ℚ) := by
        field_simp [hkn.ne']
      rw [heq]
      linarith
    calc (∑ i ∈ Finset.range (n.divisors.card - 1),
            (nthDiv n i : ℚ) * (nthDiv n (i + 1) : ℚ))
        ≤ ∑ i ∈ Finset.range (n.divisors.card - 1),
            (n : ℚ) ^ 2 / (((n.divisors.card - i) * (n.divisors.card - 1 - i) : ℕ) : ℚ) := hsum1
      _ = ∑ j ∈ Finset.range (n.divisors.card - 1),
            (n : ℚ) ^ 2 / (((j + 2) * (j + 1) : ℕ) : ℚ) := hsum2
      _ = ∑ j ∈ Finset.range (n.divisors.card - 1),
            (n : ℚ) ^ 2 * (1 / ((j : ℚ) + 1) - 1 / ((j : ℚ) + 1 + 1)) := hsum3
      _ = (n : ℚ) ^ 2 * (1 - 1 / (n.divisors.card : ℚ)) := hsum4
      _ < (n : ℚ) ^ 2 := hsum5
  exact_mod_cast hQ

lemma pairSum_eq_of_prime (n : ℕ) (hn : 1 < n) (hp : n.Prime) : pairSum n = n := by
  have hdiv : n.divisors = {1, n} := hp.divisors
  rw [pairSum_eq, hdiv, Finset.card_pair (show (1 : ℕ) ≠ n by omega),
    show (2 : ℕ) - 1 = 1 from rfl, Finset.sum_range_one]
  show nthDiv n 0 * nthDiv n 1 = n
  rw [nthDiv_zero n hn]
  have h1 : nthDiv n 1 = n := by
    have hlast := nthDiv_last n hn (by
      rw [hdiv, Finset.card_pair (show (1 : ℕ) ≠ n by omega)]
      norm_num)
    rw [hdiv, Finset.card_pair (show (1 : ℕ) ≠ n by omega)] at hlast
    exact hlast
  rw [h1, one_mul]

/-- Composite `n` does not work: `n ^ 2 / n.minFac < d ≤ n ^ 2 / n.minFac`. -/
lemma pairSum_not_dvd_of_not_prime (n : ℕ) (hn : 1 < n) (hnp : ¬ n.Prime)
    (ha : pairSum n < n ^ 2) (hdvd : pairSum n ∣ n ^ 2) : False := by
  have hn0 : 0 < n := by omega
  have hmf2 : 2 ≤ n.minFac := (Nat.minFac_prime (show n ≠ 1 by omega)).two_le
  have hpn : n.minFac < n := by
    rcases eq_or_lt_of_le (Nat.minFac_le hn0) with h | h
    · exact absurd (h ▸ Nat.minFac_prime (show n ≠ 1 by omega)) hnp
    · exact h
  have hk3 : 3 ≤ n.divisors.card := by
    have hsub : ({1, n.minFac, n} : Finset ℕ) ⊆ n.divisors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with h | h | h
      · rw [h]; exact Nat.mem_divisors.mpr ⟨one_dvd n, hn0.ne'⟩
      · rw [h]; exact Nat.mem_divisors.mpr ⟨Nat.minFac_dvd n, hn0.ne'⟩
      · rw [h]; exact Nat.mem_divisors.mpr ⟨dvd_refl n, hn0.ne'⟩
    have hcard : ({1, n.minFac, n} : Finset ℕ).card = 3 := by
      rw [Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          omega),
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_singleton]
          omega),
        Finset.card_singleton]
    have hle := Finset.card_le_card hsub
    omega
  have hfirst : nthDiv n 0 * nthDiv n 1 = n.minFac := by
    rw [nthDiv_zero n hn, one_mul, nthDiv_one n hn]
  have hpair1 : n.minFac * nthDiv n (n.divisors.card - 2) = n := by
    have h := nthDiv_pair n hn 1 (by omega)
    have esub : n.divisors.card - 1 - 1 = n.divisors.card - 2 := by omega
    rw [nthDiv_one n hn, esub] at h
    exact h
  have hk2v : nthDiv n (n.divisors.card - 2) = n / n.minFac := by
    symm
    calc n / n.minFac = n.minFac * nthDiv n (n.divisors.card - 2) / n.minFac := by rw [hpair1]
      _ = nthDiv n (n.divisors.card - 2) :=
        Nat.mul_div_cancel_left _ (by omega : 0 < n.minFac)
  have hlast : nthDiv n (n.divisors.card - 2) * nthDiv n (n.divisors.card - 1) =
      n ^ 2 / n.minFac := by
    rw [hk2v, nthDiv_last n hn (by omega), pow_two, Nat.mul_div_assoc n (Nat.minFac_dvd n),
      Nat.mul_comm]
  have hlb : nthDiv n 0 * nthDiv n 1 +
      nthDiv n (n.divisors.card - 2) * nthDiv n (n.divisors.card - 1) ≤ pairSum n := by
    rw [pairSum_eq]
    have hsub : ({0, n.divisors.card - 2} : Finset ℕ) ⊆ Finset.range (n.divisors.card - 1) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> rw [Finset.mem_range] <;> omega
    have hle := Finset.sum_le_sum_of_subset (f := fun i ↦ nthDiv n i * nthDiv n (i + 1)) hsub
    rw [Finset.sum_insert (show (0 : ℕ) ∉ ({n.divisors.card - 2} : Finset ℕ) by
        simp only [Finset.mem_singleton]
        omega),
      Finset.sum_singleton] at hle
    have e2 : n.divisors.card - 2 + 1 = n.divisors.card - 1 := by omega
    rw [e2] at hle
    exact hle
  have hd_pos : 0 < nthDiv n 0 * nthDiv n 1 := by rw [hfirst]; omega
  have hd0 : 0 < pairSum n := by omega
  have hgt : n ^ 2 / n.minFac < pairSum n := by
    rw [← hlast]
    omega
  have hq1 : 1 ≤ n ^ 2 / pairSum n :=
    (Nat.one_le_div_iff hd0).mpr (Nat.le_of_dvd (Nat.pow_pos hn0) hdvd)
  have hqne1 : n ^ 2 / pairSum n ≠ 1 := by
    intro hcon
    have h2 := Nat.div_mul_cancel hdvd
    rw [hcon, one_mul] at h2
    omega
  have hq : 2 ≤ n ^ 2 / pairSum n := by omega
  have hn2ne1 : n ^ 2 ≠ 1 := by
    have h4 : 4 ≤ n ^ 2 := by
      rw [pow_two]
      exact mul_le_mul (by omega : (2 : ℕ) ≤ n) (by omega : (2 : ℕ) ≤ n)
        (Nat.zero_le _) (Nat.zero_le _)
    omega
  have hmf : (n ^ 2).minFac = n.minFac := by
    apply le_antisymm
    · exact Nat.minFac_le_of_dvd hmf2
        (dvd_trans (Nat.minFac_dvd n) (dvd_pow_self n (show (2 : ℕ) ≠ 0 by norm_num)))
    · have hq2 : (n ^ 2).minFac.Prime := Nat.minFac_prime hn2ne1
      have hqd : (n ^ 2).minFac ∣ n := hq2.dvd_of_dvd_pow (Nat.minFac_dvd _)
      exact Nat.minFac_le_of_dvd hq2.two_le hqd
  have hle : pairSum n ≤ n ^ 2 / n.minFac := by
    have h1 : (n ^ 2).minFac ≤ n ^ 2 / pairSum n :=
      Nat.minFac_le_of_dvd hq (Nat.div_dvd_of_dvd hdvd)
    have h2 : pairSum n = n ^ 2 / (n ^ 2 / pairSum n) :=
      (Nat.div_div_self hdvd (Nat.pow_pos hn0).ne').symm
    rw [h2, ← hmf]
    exact Nat.div_le_div_left h1 (Nat.minFac_pos _)
  omega

snip end

determine SolutionSet : Set ℕ := {n | n.Prime}

problem imo2002_p4 (n : ℕ) (hn : 1 < n) :
    pairSum n < n ^ 2 ∧ (pairSum n ∣ n ^ 2 ↔ n ∈ SolutionSet) := by
  refine ⟨pairSum_lt n hn, ?_⟩
  constructor
  · intro hdvd
    by_contra hnp
    exact pairSum_not_dvd_of_not_prime n hn hnp (pairSum_lt n hn) hdvd
  · intro hp
    rw [pairSum_eq_of_prime n hn hp]
    exact dvd_pow_self n (show (2 : ℕ) ≠ 0 by norm_num)

end Imo2002P4
