/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Topology.Algebra.Polynomial
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 2002, Problem 3

Prove that any monic polynomial (a polynomial with leading coefficient 1)
of degree n with real coefficients is the average of two monic polynomials
of degree n with n real roots.
-/

namespace Usa2002P3

open Polynomial Filter Asymptotics

snip begin

/-- If `ξ` is strictly increasing at consecutive arguments below `n`,
then it is injective on `Finset.range n`. -/
theorem injOn_range_of_step {n : ℕ} {ξ : ℕ → ℝ}
    (h : ∀ i, i + 1 < n → ξ i < ξ (i + 1)) :
    Set.InjOn ξ (Finset.range n) := by
  have key : ∀ k : ℕ, ∀ i : ℕ, i + (k + 1) < n → ξ i < ξ (i + (k + 1)) := by
    intro k
    induction k with
    | zero =>
      intro i hi
      exact h i (by simpa using hi)
    | succ k ih =>
      intro i hi
      have h1 : i + (k + 1) < n := by omega
      exact (ih i h1).trans (h (i + (k + 1)) (by omega))
  intro i hi j hj hij
  rw [Finset.coe_range, Set.mem_Iio] at hi hj
  rcases lt_trichotomy i j with hlt | heq | hgt
  · have hji : j = i + (j - i - 1 + 1) := by omega
    have hlt' := key (j - i - 1) i (by omega)
    rw [← hji] at hlt'
    exact absurd hij (ne_of_lt hlt')
  · exact heq
  · have hji : i = j + (i - j - 1 + 1) := by omega
    have hlt' := key (i - j - 1) j (by omega)
    rw [← hji] at hlt'
    exact absurd hij (ne_of_gt hlt')

/-- A nonzero real polynomial of degree `n` that has `n` distinct real roots
has exactly `n` roots (counted with multiplicity), and in particular it splits. -/
theorem card_roots_eq_n {p : ℝ[X]} {n : ℕ} (hp0 : p ≠ 0) (hn : p.natDegree = n)
    {ξ : ℕ → ℝ} (hinj : Set.InjOn ξ (Finset.range n))
    (hroot : ∀ i ∈ Finset.range n, p.eval (ξ i) = 0) :
    p.roots.card = n ∧ p.Splits := by
  have hsub : ((Finset.range n).image ξ).val ≤ p.roots := by
    rw [Multiset.le_iff_subset (Finset.nodup _)]
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (show a ∈ (Finset.range n).image ξ from ha)
    exact (p.mem_roots hp0).mpr (hroot i hi)
  have hcard : ((Finset.range n).image ξ).card = n := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have h1 : n ≤ p.roots.card := by
    have hle := Multiset.card_le_card hsub
    rw [← hcard]
    exact hle
  have h2 : p.roots.card ≤ n := hn ▸ p.card_roots'
  exact ⟨le_antisymm h2 h1, splits_iff_card_roots.mpr (by rw [le_antisymm h2 h1, hn])⟩

/-- A nonzero real polynomial of degree `n` that has a root in each of `n`
open intervals `(L i, R i)` arranged in increasing order (`R i ≤ L (i+1)`)
has exactly `n` real roots and splits. -/
theorem card_roots_eq_n_of_intervals {p : ℝ[X]} {n : ℕ} (hp0 : p ≠ 0) (hn : p.natDegree = n)
    {L R : ℕ → ℝ} (hstep : ∀ i, i + 1 < n → R i ≤ L (i + 1))
    (hex : ∀ i, i < n → ∃ x ∈ Set.Ioo (L i) (R i), p.eval x = 0) :
    p.roots.card = n ∧ p.Splits := by
  obtain ⟨ξ, hξ⟩ : ∃ ξ : ℕ → ℝ, ∀ i (hi : i < n),
      ξ i ∈ Set.Ioo (L i) (R i) ∧ p.eval (ξ i) = 0 := by
    refine ⟨fun i => if h : i < n then Classical.choose (hex i h) else 0, fun i hi => ?_⟩
    simp only [dite_eq_left hi]
    exact Classical.choose_spec (hex i hi)
  have hmono : ∀ i, i + 1 < n → ξ i < ξ (i + 1) := by
    intro i hi
    have h1 := ((hξ i (by omega)).1).2
    have h2 := ((hξ (i + 1) hi).1).1
    exact lt_trans (lt_of_lt_of_le h1 (hstep i hi)) h2
  exact card_roots_eq_n hp0 hn (injOn_range_of_step hmono)
    (fun i hi => (hξ i (Finset.mem_range.mp hi)).2)

/-- Intermediate value theorem for polynomials: if `p` changes sign between
`a` and `b`, then `p` has a root in the open interval `(a, b)`. -/
theorem exists_root_of_eval_mul_neg {p : ℝ[X]} {a b : ℝ} (hab : a < b)
    (h : p.eval a * p.eval b < 0) : ∃ c ∈ Set.Ioo a b, p.eval c = 0 := by
  rcases mul_neg_iff.mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · obtain ⟨c, hc, hce⟩ := intermediate_value_Ioo' hab.le p.continuousOn ⟨hb, ha⟩
    exact ⟨c, hc, hce⟩
  · obtain ⟨c, hc, hce⟩ := intermediate_value_Ioo hab.le p.continuousOn ⟨ha, hb⟩
    exact ⟨c, hc, hce⟩

/-- Let `p` be a nonzero real polynomial of degree `n` whose values at the
integers `1, ..., n` alternate in sign, so that `p` has a root in each of the
`n - 1` intervals `(i, i+1)`. If moreover `p` changes sign on one of the two
"tails" `(-∞, 1)` or `(n, ∞)`, then `p` has exactly `n` real roots and splits. -/
theorem card_roots_and_splits {p : ℝ[X]} {n : ℕ} (hp0 : p ≠ 0) (hn : p.natDegree = n)
    (hmul : ∀ i : ℕ, 1 ≤ i → i + 1 ≤ n →
      p.eval (i : ℝ) * p.eval ((i + 1 : ℕ) : ℝ) < 0)
    (htail : (∃ a₁ : ℝ, a₁ < 1 ∧ p.eval a₁ * p.eval 1 < 0) ∨
             (∃ a₂ : ℝ, (n : ℝ) < a₂ ∧ p.eval (n : ℝ) * p.eval a₂ < 0)) :
    p.roots.card = n ∧ p.Splits := by
  rcases htail with ⟨a₁, ha₁, hmul₁⟩ | ⟨a₂, ha₂, hmul₂⟩
  · -- The extra root lies in `(a₁, 1)`, to the left of all the integer points.
    refine card_roots_eq_n_of_intervals hp0 hn (L := fun i : ℕ => if i = 0 then a₁ else (i : ℝ))
      (R := fun i : ℕ => ((i + 1 : ℕ) : ℝ)) ?_ ?_
    · intro i _
      rw [ite_eq_right (by omega : i + 1 ≠ 0)]
    · intro i hi
      by_cases hi0 : i = 0
      · subst hi0
        rw [ite_eq_left rfl]
        obtain ⟨c, hc, hce⟩ := exists_root_of_eval_mul_neg ha₁ hmul₁
        refine ⟨c, ?_, hce⟩
        rw [show ((0 + 1 : ℕ) : ℝ) = 1 by simp]
        exact hc
      · rw [ite_eq_right hi0]
        exact exists_root_of_eval_mul_neg
          (show (i : ℝ) < ((i + 1 : ℕ) : ℝ) by exact_mod_cast Nat.lt_add_one i)
          (hmul i (by omega) (by omega))
  · -- The extra root lies in `(n, a₂)`, to the right of all the integer points.
    refine card_roots_eq_n_of_intervals hp0 hn (L := fun i : ℕ => ((i + 1 : ℕ) : ℝ))
      (R := fun i : ℕ => if i < n - 1 then ((i + 2 : ℕ) : ℝ) else a₂) ?_ ?_
    · intro i hi
      rw [ite_eq_left (by omega : i < n - 1)]
    · intro i hi
      by_cases hi' : i < n - 1
      · rw [ite_eq_left hi']
        exact exists_root_of_eval_mul_neg
          (show ((i + 1 : ℕ) : ℝ) < ((i + 2 : ℕ) : ℝ) by exact_mod_cast Nat.lt_add_one (i + 1))
          (hmul (i + 1) (by omega) (by omega))
      · rw [ite_eq_right hi']
        have hieq : i + 1 = n := by omega
        obtain ⟨c, hc, hce⟩ := exists_root_of_eval_mul_neg ha₂ hmul₂
        refine ⟨c, ?_, hce⟩
        rw [hieq]
        exact hc

/-- A monic real polynomial of positive degree takes arbitrarily large
positive values. -/
theorem exists_eval_pos {p : ℝ[X]} (hm : p.Monic) (hd : 1 ≤ p.natDegree) (B : ℝ) :
    ∃ c : ℝ, B < c ∧ 0 < p.eval c := by
  have hdeg : 0 < p.degree := natDegree_pos_iff_degree_pos.mp (by omega)
  have hnn : 0 ≤ p.leadingCoeff := by
    have hlc : p.leadingCoeff = 1 := hm
    rw [hlc]
    exact zero_le_one
  have hT : Tendsto (fun x : ℝ => p.eval x) atTop atTop :=
    p.tendsto_atTop_of_leadingCoeff_nonneg hdeg hnn
  obtain ⟨c, hc1, hcB⟩ := ((hT.eventually_ge_atTop (1 : ℝ)).and (eventually_gt_atTop B)).exists
  exact ⟨c, hcB, by linarith⟩

/-- A monic real polynomial `p` of degree `n`, multiplied by `(-1)^n`, takes
arbitrarily large positive values at large negative arguments. -/
theorem exists_eval_neg_one_pow_pos {p : ℝ[X]} (hm : p.Monic) (hd : 1 ≤ p.natDegree) (B : ℝ) :
    ∃ a : ℝ, a < B ∧ 0 < (-1 : ℝ) ^ p.natDegree * p.eval a := by
  have hn0 : p.natDegree ≠ 0 := by omega
  have hlc : p.leadingCoeff = 1 := hm
  have hE : (fun x : ℝ => p.eval x) ~[atBot] fun x : ℝ => x ^ p.natDegree := by
    have h := p.isEquivalent_atBot_lead
    rw [hlc] at h
    simpa using h
  have hE2 : (fun x : ℝ => (-1 : ℝ) ^ p.natDegree * p.eval x) ~[atBot]
      fun x : ℝ => (-1 : ℝ) ^ p.natDegree * x ^ p.natDegree := by
    have h := (IsEquivalent.refl (u := fun _ : ℝ => (-1 : ℝ) ^ p.natDegree)).mul hE
    exact h
  have hT : Tendsto (fun x : ℝ => (-1 : ℝ) ^ p.natDegree * x ^ p.natDegree) atBot atTop := by
    have h1 : Tendsto (fun x : ℝ => (-x) ^ p.natDegree) atBot atTop :=
      (tendsto_pow_atTop hn0).comp tendsto_neg_atBot_atTop
    refine h1.congr' ?_
    filter_upwards with x
    rw [neg_pow]
  have hT2 : Tendsto (fun x : ℝ => (-1 : ℝ) ^ p.natDegree * p.eval x) atBot atTop :=
    hE2.symm.tendsto_atTop hT
  obtain ⟨a, ha1, haB⟩ := ((hT2.eventually_ge_atTop (1 : ℝ)).and (eventually_lt_atBot B)).exists
  exact ⟨a, haB, by linarith⟩

snip end

problem usa2002_p3 (n : ℕ) (p : ℝ[X]) (hpm : p.Monic) (hpn : p.natDegree = n) :
    ∃ q r : ℝ[X], q.Monic ∧ r.Monic ∧ q.natDegree = n ∧ r.natDegree = n ∧
      q.roots.card = n ∧ r.roots.card = n ∧
      q.Splits ∧ r.Splits ∧ p = (q + r) / 2 := by
  rcases eq_or_ne n 0 with rfl | hn0
  · -- If `n = 0`, then `p = 1` and we may take `q = r = 1`.
    have hp1 : p = 1 := by
      have h0 : p.natDegree = 0 := hpn
      have h1 : p.coeff p.natDegree = 1 := hpm
      rw [h0] at h1
      rw [eq_C_of_natDegree_eq_zero h0, h1]
      exact C_1
    subst hp1
    have h2 : (2 : ℝ[X]) ≠ 0 := two_ne_zero
    refine ⟨1, 1, monic_one, monic_one, ?_, ?_, ?_, ?_, Splits.one, Splits.one, ?_⟩
    · simp
    · simp
    · simp [roots_one]
    · simp [roots_one]
    · rw [show (1 : ℝ[X]) + 1 = 2 * (1 : ℝ[X]) by ring, mul_div_cancel_left₀ _ h2]
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    -- A bound `M` on the values of `p` at the integers `1, ..., n`.
    set M : ℝ := (∑ i ∈ Finset.Icc 1 n, |p.eval (i : ℝ)|) + 1 with hMdef
    have hM : ∀ i ∈ Finset.Icc 1 n, |p.eval (i : ℝ)| < M := by
      intro i hi
      have hle : |p.eval (i : ℝ)| ≤ ∑ j ∈ Finset.Icc 1 n, |p.eval (j : ℝ)| :=
        Finset.single_le_sum (s := Finset.Icc 1 n) (f := fun j : ℕ => |p.eval (j : ℝ)|)
          (fun j _ => abs_nonneg _) hi
      rw [hMdef]
      exact lt_of_le_of_lt hle (lt_add_one _)
    -- The perturbation `u` of degree `< n` with alternating values `± M`
    -- at the integers `1, ..., n`.
    set u : ℝ[X] := Lagrange.interpolate (Finset.Icc 1 n) (fun i : ℕ => (i : ℝ))
      (fun i : ℕ => (-1 : ℝ) ^ (i + 1) * M) with hudef
    have hinj : Set.InjOn (fun i : ℕ => (i : ℝ)) (Finset.Icc 1 n) := Nat.cast_injective.injOn
    have hpdeg : p.degree = (n : WithBot ℕ) := by
      rw [degree_eq_natDegree hpm.ne_zero, hpn]
    have hudeg : u.degree < p.degree := by
      have h := Lagrange.degree_interpolate_lt (fun i : ℕ => (-1 : ℝ) ^ (i + 1) * M) hinj
      rw [Nat.card_Icc, Nat.add_sub_cancel] at h
      rw [hpdeg]
      exact h
    have hudeg' : (-u).degree < p.degree := by rwa [degree_neg]
    set q : ℝ[X] := p + u with hqdef
    set r : ℝ[X] := p - u with hrdef
    have hqmonic : q.Monic := hpm.add_of_left hudeg
    have hrmonic : r.Monic := by
      rw [hrdef, sub_eq_add_neg]
      exact hpm.add_of_left hudeg'
    have hqdeg : q.natDegree = n := by
      have h1 : q.degree = p.degree := degree_add_eq_left_of_degree_lt hudeg
      rw [degree_eq_natDegree hqmonic.ne_zero, hpdeg] at h1
      exact WithBot.coe_eq_coe.mp h1
    have hrdeg : r.natDegree = n := by
      have h1 : r.degree = p.degree := by
        rw [hrdef, sub_eq_add_neg]
        exact degree_add_eq_left_of_degree_lt hudeg'
      rw [degree_eq_natDegree hrmonic.ne_zero, hpdeg] at h1
      exact WithBot.coe_eq_coe.mp h1
    -- The values of `u` at the integer points.
    have huval : ∀ i ∈ Finset.Icc 1 n, u.eval (i : ℝ) = (-1 : ℝ) ^ (i + 1) * M := by
      intro i hi
      exact Lagrange.eval_interpolate_at_node (fun i : ℕ => (-1 : ℝ) ^ (i + 1) * M) hinj hi
    -- The sign of `q = p + u` at the integer `i` is that of `(-1)^(i+1)`.
    have hqsign : ∀ i ∈ Finset.Icc 1 n, 0 < q.eval (i : ℝ) * (-1 : ℝ) ^ (i + 1) := by
      intro i hi
      have hui : u.eval (i : ℝ) = (-1 : ℝ) ^ (i + 1) * M := huval i hi
      have hMi : |p.eval (i : ℝ)| < M := hM i hi
      have hqe : q.eval (i : ℝ) = p.eval (i : ℝ) + u.eval (i : ℝ) := by simp [hqdef, eval_add]
      rcases Nat.even_or_odd i with hev | hodd
      · have hpow : (-1 : ℝ) ^ (i + 1) = -1 := hev.add_one.neg_one_pow
        rw [hqe, hui, hpow, neg_one_mul, mul_neg, mul_one, neg_pos]
        have habs := le_abs_self (p.eval (i : ℝ))
        linarith
      · have hpow : (-1 : ℝ) ^ (i + 1) = 1 := hodd.add_one.neg_one_pow
        rw [hqe, hui, hpow, one_mul, mul_one]
        have habs := neg_abs_le (p.eval (i : ℝ))
        linarith
    -- The sign of `r = p - u` at the integer `i` is that of `(-1)^i`.
    have hrsign : ∀ i ∈ Finset.Icc 1 n, 0 < r.eval (i : ℝ) * (-1 : ℝ) ^ i := by
      intro i hi
      have hui : u.eval (i : ℝ) = (-1 : ℝ) ^ (i + 1) * M := huval i hi
      have hMi : |p.eval (i : ℝ)| < M := hM i hi
      have hre : r.eval (i : ℝ) = p.eval (i : ℝ) - u.eval (i : ℝ) := by simp [hrdef, eval_sub]
      rcases Nat.even_or_odd i with hev | hodd
      · have hpow : (-1 : ℝ) ^ i = 1 := hev.neg_one_pow
        have hpow1 : (-1 : ℝ) ^ (i + 1) = -1 := hev.add_one.neg_one_pow
        rw [hre, hui, hpow1, neg_one_mul, hpow, mul_one, sub_neg_eq_add]
        have habs := neg_abs_le (p.eval (i : ℝ))
        linarith
      · have hpow : (-1 : ℝ) ^ i = -1 := hodd.neg_one_pow
        have hpow1 : (-1 : ℝ) ^ (i + 1) = 1 := hodd.add_one.neg_one_pow
        rw [hre, hui, hpow1, one_mul, hpow, mul_neg, mul_one, neg_pos]
        have habs := le_abs_self (p.eval (i : ℝ))
        linarith
    -- Hence `q` and `r` change sign between any two consecutive integers.
    have hqmul : ∀ i : ℕ, 1 ≤ i → i + 1 ≤ n →
        q.eval (i : ℝ) * q.eval ((i + 1 : ℕ) : ℝ) < 0 := by
      intro i hi1 hi2
      have h1 := hqsign i (Finset.mem_Icc.mpr ⟨hi1, by omega⟩)
      have h2 := hqsign (i + 1) (Finset.mem_Icc.mpr ⟨by omega, hi2⟩)
      rcases Nat.even_or_odd i with hev | hodd
      · have hs1 : (-1 : ℝ) ^ (i + 1) = -1 := hev.add_one.neg_one_pow
        have hs2 : (-1 : ℝ) ^ (i + 1 + 1) = 1 := hev.add_one.add_one.neg_one_pow
        rw [hs1, mul_neg, mul_one] at h1
        rw [hs2, mul_one] at h2
        exact mul_neg_of_neg_of_pos (neg_pos.mp h1) h2
      · have hs1 : (-1 : ℝ) ^ (i + 1) = 1 := hodd.add_one.neg_one_pow
        have hs2 : (-1 : ℝ) ^ (i + 1 + 1) = -1 := hodd.add_one.add_one.neg_one_pow
        rw [hs1, mul_one] at h1
        rw [hs2, mul_neg, mul_one] at h2
        exact mul_neg_of_pos_of_neg h1 (neg_pos.mp h2)
    have hrmul : ∀ i : ℕ, 1 ≤ i → i + 1 ≤ n →
        r.eval (i : ℝ) * r.eval ((i + 1 : ℕ) : ℝ) < 0 := by
      intro i hi1 hi2
      have h1 := hrsign i (Finset.mem_Icc.mpr ⟨hi1, by omega⟩)
      have h2 := hrsign (i + 1) (Finset.mem_Icc.mpr ⟨by omega, hi2⟩)
      rcases Nat.even_or_odd i with hev | hodd
      · have hs1 : (-1 : ℝ) ^ i = 1 := hev.neg_one_pow
        have hs2 : (-1 : ℝ) ^ (i + 1) = -1 := hev.add_one.neg_one_pow
        rw [hs1, mul_one] at h1
        rw [hs2, mul_neg, mul_one] at h2
        exact mul_neg_of_pos_of_neg h1 (neg_pos.mp h2)
      · have hs1 : (-1 : ℝ) ^ i = -1 := hodd.neg_one_pow
        have hs2 : (-1 : ℝ) ^ (i + 1) = 1 := hodd.add_one.neg_one_pow
        rw [hs1, mul_neg, mul_one] at h1
        rw [hs2, mul_one] at h2
        exact mul_neg_of_neg_of_pos (neg_pos.mp h1) h2
    -- The values of `q` and `r` at the tails of the integers `1, ..., n`.
    obtain ⟨a₁, ha₁lt, ha₁s⟩ := exists_eval_neg_one_pow_pos hqmonic (hqdeg ▸ hn1) 1
    rw [hqdeg] at ha₁s
    obtain ⟨a₂, ha₂lt, ha₂s⟩ := exists_eval_pos hqmonic (hqdeg ▸ hn1) (n : ℝ)
    obtain ⟨b₁, hb₁lt, hb₁s⟩ := exists_eval_neg_one_pow_pos hrmonic (hrdeg ▸ hn1) 1
    rw [hrdeg] at hb₁s
    obtain ⟨b₂, hb₂lt, hb₂s⟩ := exists_eval_pos hrmonic (hrdeg ▸ hn1) (n : ℝ)
    -- Hence each of `q` and `r` changes sign on one of the two tails.
    have hqtail : (∃ a₁ : ℝ, a₁ < 1 ∧ q.eval a₁ * q.eval 1 < 0) ∨
        (∃ a₂ : ℝ, (n : ℝ) < a₂ ∧ q.eval (n : ℝ) * q.eval a₂ < 0) := by
      rcases Nat.even_or_odd n with hev | hodd
      · refine Or.inr ⟨a₂, ha₂lt, mul_neg_of_neg_of_pos ?_ ha₂s⟩
        have h := hqsign n (Finset.mem_Icc.mpr ⟨hn1, le_refl n⟩)
        have hpow : (-1 : ℝ) ^ (n + 1) = -1 := hev.add_one.neg_one_pow
        rw [hpow, mul_neg, mul_one] at h
        exact neg_pos.mp h
      · refine Or.inl ⟨a₁, ha₁lt, mul_neg_of_neg_of_pos ?_ ?_⟩
        · have hpow : (-1 : ℝ) ^ n = -1 := hodd.neg_one_pow
          rw [hpow, neg_one_mul] at ha₁s
          exact neg_pos.mp ha₁s
        · have h := hqsign 1 (Finset.mem_Icc.mpr ⟨le_refl 1, hn1⟩)
          rw [Nat.cast_one, show (-1 : ℝ) ^ (1 + 1) = 1 by norm_num, mul_one] at h
          exact h
    have hrtail : (∃ b₁ : ℝ, b₁ < 1 ∧ r.eval b₁ * r.eval 1 < 0) ∨
        (∃ b₂ : ℝ, (n : ℝ) < b₂ ∧ r.eval (n : ℝ) * r.eval b₂ < 0) := by
      rcases Nat.even_or_odd n with hev | hodd
      · refine Or.inl ⟨b₁, hb₁lt, ?_⟩
        have hrb : 0 < r.eval b₁ := by
          have hpow : (-1 : ℝ) ^ n = 1 := hev.neg_one_pow
          rw [hpow, one_mul] at hb₁s
          exact hb₁s
        have hr1 : r.eval (1 : ℝ) < 0 := by
          have h := hrsign 1 (Finset.mem_Icc.mpr ⟨le_refl 1, hn1⟩)
          rw [Nat.cast_one, show (-1 : ℝ) ^ (1 : ℕ) = -1 by norm_num, mul_neg, mul_one] at h
          exact neg_pos.mp h
        exact mul_neg_of_pos_of_neg hrb hr1
      · refine Or.inr ⟨b₂, hb₂lt, mul_neg_of_neg_of_pos ?_ hb₂s⟩
        have h := hrsign n (Finset.mem_Icc.mpr ⟨hn1, le_refl n⟩)
        have hpow : (-1 : ℝ) ^ n = -1 := hodd.neg_one_pow
        rw [hpow, mul_neg, mul_one] at h
        exact neg_pos.mp h
    -- Count the roots of `q` and `r`.
    obtain ⟨hqcard, hqsplit⟩ := card_roots_and_splits hqmonic.ne_zero hqdeg hqmul hqtail
    obtain ⟨hrcard, hrsplit⟩ := card_roots_and_splits hrmonic.ne_zero hrdeg hrmul hrtail
    refine ⟨q, r, hqmonic, hrmonic, hqdeg, hrdeg, hqcard, hrcard, hqsplit, hrsplit, ?_⟩
    have hsum : q + r = 2 * p := by rw [hqdef, hrdef]; ring
    rw [hsum]
    exact (mul_div_cancel_left₀ p two_ne_zero).symm

end Usa2002P3
