/-
Copyright (c) 2026 Constantin Seebach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Constantin Seebach
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file {
  tags := [.Algebra]
}

/-!
# International Mathematical Olympiad 2005, Problem 2

Let $a_1, a_2, \dots$ be a sequence of integers with infinitely many positive and negative terms.
Suppose that for every positive integer $n$ the numbers $a_1, a_2, \dots, a_n$ leave $n$ different remainders upon division by $n$.
Prove that every integer occurs exactly once in the sequence.
-/

namespace Imo2005P2

snip begin

/-
For every n, the first n terms of the sequence are n distinct integers
whose pairwise differences are smaller than n: if two of them differed by
d ≥ n, they would agree modulo d, contradicting the hypothesis for d.
Hence the first n terms form an interval of n consecutive integers. Since
the sequence takes arbitrarily large positive and negative values, every
integer lies in one of these intervals, and uniqueness follows from
injectivity.
-/

lemma a_injective (a : ℕ → ℤ)
    (rem : ∀ n > 0, ((Finset.range n).image (fun i => a i % n)).card = n) :
    Function.Injective a := by
  intro i j hij
  by_contra hne
  set n := max i j + 1 with hn
  have hinj : Set.InjOn (fun k => a k % (n : ℤ)) (Finset.range n) :=
    Finset.injOn_of_card_image_eq (by rw [rem n (by lia), Finset.card_range])
  exact hne (hinj
    (Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.lt_succ_of_le (le_max_left i j))))
    (Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.lt_succ_of_le (le_max_right i j))))
    (congrArg (· % (n : ℤ)) hij))

/-- Any two of the first `n` terms differ by less than `n`. -/
lemma abs_sub_lt (a : ℕ → ℤ)
    (rem : ∀ n > 0, ((Finset.range n).image (fun i => a i % n)).card = n)
    {i j n : ℕ} (hi : i < n) (hj : j < n) : |a i - a j| < n := by
  rcases eq_or_ne i j with rfl | hne
  · simp only [sub_self, abs_zero]
    exact_mod_cast Nat.zero_lt_of_lt hi
  by_contra hcon
  push Not at hcon
  set d := (a i - a j).natAbs with hd
  have hnd : n ≤ d := by
    have : ((n:ℤ)) ≤ (d:ℤ) := by rwa [hd, ← Int.abs_eq_natAbs]
    exact_mod_cast this
  have hinj : Set.InjOn (fun k => a k % d) (Finset.range d) :=
    Finset.injOn_of_card_image_eq (by rw [rem d (by lia), Finset.card_range])
  have hmod : a i % (d:ℤ) = a j % (d:ℤ) := by
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
    exact Int.emod_eq_zero_of_dvd (Int.natAbs_dvd.mpr dvd_rfl)
  exact hne (hinj (Finset.mem_coe.mpr (Finset.mem_range.mpr (by lia)))
    (Finset.mem_coe.mpr (Finset.mem_range.mpr (by lia))) hmod)

/-- The first `n` terms form a set of `n` consecutive integers, so any
integer sandwiched between two of them is itself one of them. -/
lemma mem_of_between (a : ℕ → ℤ)
    (rem : ∀ n > 0, ((Finset.range n).image (fun i => a i % n)).card = n)
    {n : ℕ} {z : ℤ} {i j : ℕ} (hi : i < n) (hj : j < n)
    (hzi : z ≤ a i) (hjz : a j ≤ z) :
    ∃ k, a k = z := by
  set S := (Finset.range n).image a with hS
  have hmem : ∀ {m : ℕ}, m < n → a m ∈ S :=
    fun hm => Finset.mem_image.mpr ⟨_, Finset.mem_range.mpr hm, rfl⟩
  have hne : S.Nonempty := ⟨a i, hmem hi⟩
  have hcard : S.card = n := by
    rw [hS, Finset.card_image_of_injOn (a_injective a rem).injOn, Finset.card_range]
  obtain ⟨p, hp, hpmax⟩ := Finset.mem_image.mp (S.max'_mem hne)
  obtain ⟨q, hq, hqmin⟩ := Finset.mem_image.mp (S.min'_mem hne)
  have hwidth : S.max' hne - S.min' hne < n := by
    rw [← hpmax, ← hqmin]
    calc a p - a q ≤ |a p - a q| := le_abs_self _
      _ < n := abs_sub_lt a rem (Finset.mem_range.mp hp) (Finset.mem_range.mp hq)
  have hSIcc : S = Finset.Icc (S.min' hne) (S.max' hne) := by
    refine Finset.eq_of_subset_of_card_le
      (fun x hx => Finset.mem_Icc.mpr ⟨S.min'_le x hx, S.le_max' x hx⟩) ?_
    rw [Int.card_Icc, hcard]
    lia
  have hzmem : z ∈ S := by
    rw [hSIcc, Finset.mem_Icc]
    exact ⟨(S.min'_le (a j) (hmem hj)).trans hjz,
      hzi.trans (S.le_max' (a i) (hmem hi))⟩
  obtain ⟨k, -, hak⟩ := Finset.mem_image.mp hzmem
  exact ⟨k, hak⟩

snip end

problem imo2005_p2 (a : ℕ → ℤ)
  (pos_inf : Set.Infinite {i | 0 < a i})
  (neg_inf : Set.Infinite {i | a i < 0})
  (rem : ∀ n > 0, ((Finset.range n).image (fun i => a i % n)).card = n)
    : ∀ z : ℤ, ∃! i, a i = z := by
  intro z
  -- the sequence takes a value ≥ z, since it takes infinitely many
  -- distinct positive values
  have hexi : ∃ i, z ≤ a i := by
    by_contra hcon
    push Not at hcon
    refine pos_inf (Set.Finite.subset
      ((Set.finite_Ioo 0 z).preimage (a_injective a rem).injOn) ?_)
    exact fun i hi => Set.mem_preimage.mpr (Set.mem_Ioo.mpr ⟨hi, hcon i⟩)
  -- likewise it takes a value ≤ z
  have hexj : ∃ j, a j ≤ z := by
    by_contra hcon
    push Not at hcon
    refine neg_inf (Set.Finite.subset
      ((Set.finite_Ioo z 0).preimage (a_injective a rem).injOn) ?_)
    exact fun i hi => Set.mem_preimage.mpr (Set.mem_Ioo.mpr ⟨hcon i, hi⟩)
  obtain ⟨i, hi⟩ := hexi
  obtain ⟨j, hj⟩ := hexj
  obtain ⟨k, hk⟩ := mem_of_between a rem
    (Nat.lt_succ_of_le (le_max_left i j)) (Nat.lt_succ_of_le (le_max_right i j)) hi hj
  exact ⟨k, hk, fun y hy => a_injective a rem (hy.trans hk.symm)⟩

end Imo2005P2
