/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 1984, Problem 2

Can one find a set of n distinct positive integers such that the
geometric mean of any (non-empty, finite) subset is an integer?
Can one find an infinite set with this property?
-/

namespace Usa1984P2

open scoped Nat

snip begin

/-- The key divisibility fact for the second part: if `y * C` and `z * C`
(with `y`, `z`, `C` positive) are both `k`-th powers, then `k` divides the
difference of the multiplicities of any number `p` in the prime
factorizations of `y` and `z`. -/
theorem factorization_eq_of_pow (k : ℕ) (hk : 0 < k) (y z C : ℕ)
    (hy : y ≠ 0) (hz : z ≠ 0) (hC : C ≠ 0)
    (u : ℕ) (hu : u ^ k = y * C) (v : ℕ) (hv : v ^ k = z * C) (p : ℕ) :
    (k : ℤ) ∣ (Nat.factorization y p : ℤ) - Nat.factorization z p := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [zero_pow hk.ne'] at hu
    exact mul_ne_zero hy hC hu.symm
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [zero_pow hk.ne'] at hv
    exact mul_ne_zero hz hC hv.symm
  have eu : Nat.factorization (u ^ k) p = k * Nat.factorization u p := by
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  have ev : Nat.factorization (v ^ k) p = k * Nat.factorization v p := by
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  rw [hu, Nat.factorization_mul hy hC, Finsupp.add_apply] at eu
  rw [hv, Nat.factorization_mul hz hC, Finsupp.add_apply] at ev
  use (Nat.factorization u p : ℤ) - Nat.factorization v p
  have e1 : (k : ℤ) * Nat.factorization u p =
      Nat.factorization y p + Nat.factorization C p := by
    exact_mod_cast eu.symm
  have e2 : (k : ℤ) * Nat.factorization v p =
      Nat.factorization z p + Nat.factorization C p := by
    exact_mod_cast ev.symm
  linear_combination e2 - e1

snip end

problem usa1984_p2a (n : ℕ) :
    ∃ s : Finset ℕ, s.card = n ∧ (∀ x ∈ s, 0 < x) ∧
      ∀ t : Finset ℕ, t ⊆ s → t.Nonempty → ∃ m : ℕ, m ^ t.card = ∏ x ∈ t, x := by
  classical
  have hinj : Function.Injective (· ^ n !) := Nat.pow_left_injective (Nat.factorial_ne_zero n)
  refine ⟨(Finset.Icc 1 n).image (· ^ n !), ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn hinj.injOn]
    simp [Nat.card_Icc]
  · intro x hx
    simp only [Finset.mem_image, Finset.mem_Icc] at hx
    obtain ⟨i, ⟨hi1, -⟩, rfl⟩ := hx
    exact pow_pos hi1 _
  · intro t hts ht
    rw [Finset.subset_image_iff] at hts
    obtain ⟨u, hu, rfl⟩ := hts
    have hinju : Set.InjOn (· ^ n !) ↑u := hinj.injOn
    rw [Finset.card_image_of_injOn hinju, Finset.prod_image hinju, Finset.prod_pow]
    have hcard : 0 < u.card := by
      have h := Finset.card_pos.mpr ht
      rwa [Finset.card_image_of_injOn hinju] at h
    have hle : u.card ≤ n := by
      have h := Finset.card_le_card hu
      rwa [Nat.card_Icc, Nat.add_sub_cancel] at h
    have hdvd : u.card ∣ n ! := Nat.dvd_factorial hcard hle
    exact ⟨(∏ x ∈ u, x) ^ (n ! / u.card), by rw [← pow_mul, Nat.div_mul_cancel hdvd]⟩

problem usa1984_p2b :
    ¬ ∃ S : Set ℕ, S.Infinite ∧ (∀ x ∈ S, 0 < x) ∧
      ∀ s : Finset ℕ, s.Nonempty → ↑s ⊆ S → ∃ m : ℕ, m ^ s.card = ∏ x ∈ s, x := by
  rintro ⟨S, hSinf, hSpos, hS⟩
  -- Pick two distinct elements `a`, `b` of `S`.
  obtain ⟨a, haS⟩ := hSinf.nonempty
  obtain ⟨b, hb⟩ := (hSinf.sdiff (Set.finite_singleton a)).nonempty
  rw [Set.mem_sdiff, Set.mem_singleton_iff] at hb
  obtain ⟨hbS, hba⟩ := hb
  have hab : a ≠ b := Ne.symm hba
  have ha0 : a ≠ 0 := (hSpos a haS).ne'
  have hb0 : b ≠ 0 := (hSpos b hbS).ne'
  -- Their prime factorizations differ at some number `p`.
  have hfab : Nat.factorization a ≠ Nat.factorization b := fun h =>
    hab (Nat.factorization_inj ha0 hb0 h)
  obtain ⟨p, hp⟩ := DFunLike.ne_iff.mp hfab
  -- Set `k - 1 = |ν_p a - ν_p b|` and find `k - 1` further elements of `S`.
  set d := Int.natAbs ((Nat.factorization a p : ℤ) - Nat.factorization b p) with hd
  have hd0 : 0 < d := by
    have hne : (Nat.factorization a p : ℤ) ≠ Nat.factorization b p := by
      exact_mod_cast hp
    rw [hd, Int.natAbs_pos]
    exact sub_ne_zero.mpr hne
  obtain ⟨c, hcsub, hccard⟩ :=
    (hSinf.sdiff ((Set.finite_singleton a).union (Set.finite_singleton b))).exists_subset_card_eq d
  have hcS : ∀ x ∈ c, x ∈ S := fun x hx => (hcsub (Finset.mem_coe.mpr hx)).1
  have hac : a ∉ c := fun h =>
    (hcsub (Finset.mem_coe.mpr h)).2 (Set.mem_union_left _ (Set.mem_singleton a))
  have hbc : b ∉ c := fun h =>
    (hcsub (Finset.mem_coe.mpr h)).2 (Set.mem_union_right _ (Set.mem_singleton b))
  have hc0 : ∀ x ∈ c, x ≠ 0 := fun x hx => (hSpos x (hcS x hx)).ne'
  have hC0 : ∏ x ∈ c, x ≠ 0 := Finset.prod_ne_zero_iff.mpr hc0
  have hsubS : ↑c ⊆ S := fun x hx => hcS x (Finset.mem_coe.mp hx)
  -- Apply the hypothesis to `{a} ∪ c` and to `{b} ∪ c`; both have card `d + 1`.
  have hcarda : (insert a c).card = d + 1 := by rw [Finset.card_insert_of_notMem hac, hccard]
  have hcardb : (insert b c).card = d + 1 := by rw [Finset.card_insert_of_notMem hbc, hccard]
  obtain ⟨u, hu⟩ := hS (insert a c) (Finset.insert_nonempty a c)
    (by rw [Finset.coe_insert]; exact Set.insert_subset haS hsubS)
  obtain ⟨v, hv⟩ := hS (insert b c) (Finset.insert_nonempty b c)
    (by rw [Finset.coe_insert]; exact Set.insert_subset hbS hsubS)
  rw [hcarda, Finset.prod_insert hac] at hu
  rw [hcardb, Finset.prod_insert hbc] at hv
  -- So `d + 1` divides `ν_p a - ν_p b`, whose absolute value is `d`: impossible.
  have hdvd := factorization_eq_of_pow (d + 1) (Nat.succ_pos d) a b (∏ x ∈ c, x) ha0 hb0 hC0 u hu v hv p
  have hle : d + 1 ≤ d := by
    have h2 : d + 1 ∣ d := by
      rw [hd, ← Int.natCast_dvd_natCast]
      exact Int.dvd_natAbs.mpr hdvd
    exact Nat.le_of_dvd hd0 h2
  exact Nat.not_succ_le_self d hle

end Usa1984P2
