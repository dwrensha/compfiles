/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Algebra.Polynomial.Roots
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1974, Problem 6

Let $P$ be a non-constant polynomial with integer coefficients. If $n(P)$ is
the number of different integers $k$ such that $(P(k))^2 = 1$, prove that
$n(P) - \deg(P) \leq 2$.

We formalize $n(P)$ as the cardinality (`Set.ncard`) of the set of integers
`k` with `P.eval k ^ 2 = 1`, and prove the equivalent inequality
`n(P) ≤ deg(P) + 2`.
-/

namespace Imo1974P6

open Polynomial

snip begin

/-- The integers `k` with `Q.eval k = 0` are exactly the roots of `Q`. -/
theorem setOf_eval_eq_zero {Q : Polynomial ℤ} (hQ : Q ≠ 0) :
    {k : ℤ | Q.eval k = 0} = ↑(Q.roots.toFinset) := by
  ext k
  simp only [Set.mem_setOf_eq, Finset.mem_coe, Multiset.mem_toFinset]
  rw [mem_roots hQ, IsRoot.def]

/-- A nonzero integer polynomial has only finitely many integer roots. -/
theorem finite_eval_eq_zero {Q : Polynomial ℤ} (hQ : Q ≠ 0) :
    {k : ℤ | Q.eval k = 0}.Finite := by
  rw [setOf_eval_eq_zero hQ]
  exact Finset.finite_toSet _

/-- A nonzero integer polynomial has at most `natDegree` distinct integer
roots. -/
theorem ncard_eval_eq_zero_le {Q : Polynomial ℤ} (hQ : Q ≠ 0) :
    {k : ℤ | Q.eval k = 0}.ncard ≤ Q.natDegree := by
  rw [setOf_eval_eq_zero hQ, Set.ncard_coe_finset]
  exact (Multiset.toFinset_card_le _).trans (card_roots' _)

/-- `P k = 1` means that `k` is a root of `P - 1`. -/
theorem setOf_eval_eq_one (P : Polynomial ℤ) :
    {k : ℤ | P.eval k = 1} = {k : ℤ | (P - 1).eval k = 0} := by
  ext k
  simp only [Set.mem_setOf_eq, eval_sub, eval_one, sub_eq_zero]

/-- `P k = -1` means that `k` is a root of `P + 1`. -/
theorem setOf_eval_eq_neg_one (P : Polynomial ℤ) :
    {k : ℤ | P.eval k = -1} = {k : ℤ | (P + 1).eval k = 0} := by
  ext k
  simp only [Set.mem_setOf_eq, eval_add, eval_one, add_eq_zero_iff_eq_neg]

/-- Key divisibility: if `P r = 1` and `P k = -1`, then `k - r ∣ 2`. -/
theorem sub_dvd_two {P : Polynomial ℤ} {r k : ℤ} (hr : P.eval r = 1)
    (hk : P.eval k = -1) : k - r ∣ 2 := by
  have h0 := sub_dvd_eval_sub k r P
  rw [hk, hr] at h0
  norm_num at h0
  exact h0

/-- Main step: if `r` is a least integer with `P r = ±1` and `P r = 1`, then
at most `deg P + 2` integers satisfy `P k = ±1`. -/
theorem ncard_le_of_exists_min {P : Polynomial ℤ} (hP : 0 < P.natDegree) {r : ℤ}
    (hmin : ∀ k : ℤ, P.eval k = 1 ∨ P.eval k = -1 → r ≤ k) (hr : P.eval r = 1) :
    ({k : ℤ | P.eval k = 1} ∪ {k : ℤ | P.eval k = -1}).ncard ≤ P.natDegree + 2 := by
  have hP1 : P - 1 ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    rw [h, natDegree_one] at hP
    exact (Nat.lt_irrefl 0 hP).elim
  have hdeg1 : (P - 1).natDegree = P.natDegree := by
    refine natDegree_sub_eq_left_of_natDegree_lt ?_
    rw [natDegree_one]
    exact hP
  -- At most `deg P` integers satisfy `P k = 1`.
  have hA : {k : ℤ | P.eval k = 1}.ncard ≤ P.natDegree := by
    rw [setOf_eval_eq_one, ← hdeg1]
    exact ncard_eval_eq_zero_le hP1
  -- At most two integers satisfy `P k = -1`, namely `r + 1` and `r + 2`.
  have hsub : {k : ℤ | P.eval k = -1} ⊆ {r + 1, r + 2} := by
    intro k hk
    simp only [Set.mem_setOf_eq] at hk
    have hle : r ≤ k := hmin k (Or.inr hk)
    have hne : k ≠ r := by
      rintro rfl
      rw [hr] at hk
      norm_num at hk
    have hdvd : k - r ∣ 2 := sub_dvd_two hr hk
    have hpos : 0 < k - r := by omega
    have hle2 : k - r ≤ 2 := Int.le_of_dvd (by norm_num) hdvd
    have hmem : k = r + 1 ∨ k = r + 2 := by omega
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  have hB : {k : ℤ | P.eval k = -1}.ncard ≤ 2 :=
    (Set.ncard_le_ncard hsub ((Set.finite_singleton _).insert _)).trans
      (le_of_eq (Set.ncard_pair (by omega)))
  calc ({k : ℤ | P.eval k = 1} ∪ {k : ℤ | P.eval k = -1}).ncard
      ≤ {k : ℤ | P.eval k = 1}.ncard + {k : ℤ | P.eval k = -1}.ncard :=
        Set.ncard_union_le _ _
    _ ≤ P.natDegree + 2 := Nat.add_le_add hA hB

snip end

problem imo1974_p6 (P : Polynomial ℤ) (hP : 0 < P.natDegree) :
    {k : ℤ | P.eval k ^ 2 = 1}.ncard ≤ P.natDegree + 2 := by
  -- Unpack `(P k)^2 = 1` as `P k = 1 ∨ P k = -1`.
  have hset : {k : ℤ | P.eval k ^ 2 = 1}
      = {k : ℤ | P.eval k = 1} ∪ {k : ℤ | P.eval k = -1} := by
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_union]
    exact sq_eq_one_iff
  rw [hset]
  by_cases hne : ({k : ℤ | P.eval k = 1} ∪ {k : ℤ | P.eval k = -1}).Nonempty
  · -- Take the least integer `r` with `P r = ±1`.
    have hfin : ({k : ℤ | P.eval k = 1} ∪ {k : ℤ | P.eval k = -1}).Finite := by
      apply Set.Finite.union
      · rw [setOf_eval_eq_one]
        refine finite_eval_eq_zero ?_
        intro h
        rw [sub_eq_zero] at h
        rw [h, natDegree_one] at hP
        exact (Nat.lt_irrefl 0 hP).elim
      · rw [setOf_eval_eq_neg_one]
        refine finite_eval_eq_zero ?_
        intro h
        have h1 : P = -1 := eq_neg_of_add_eq_zero_left h
        rw [h1, natDegree_neg, natDegree_one] at hP
        exact (Nat.lt_irrefl 0 hP).elim
    obtain ⟨x0, hx0⟩ := hne
    obtain ⟨r, hrmem, hrmin⟩ :=
      Finset.exists_min_image hfin.toFinset id ⟨x0, hfin.mem_toFinset.mpr hx0⟩
    rw [Set.Finite.mem_toFinset] at hrmem
    have hrmin' : ∀ k : ℤ, P.eval k = 1 ∨ P.eval k = -1 → r ≤ k := by
      intro k hk
      have hmk : k ∈ {k : ℤ | P.eval k = 1} ∪ {k : ℤ | P.eval k = -1} := by
        simpa only [Set.mem_union, Set.mem_setOf_eq] using hk
      simpa only [id_eq] using hrmin k (hfin.mem_toFinset.mpr hmk)
    rcases hrmem with hr1 | hr1
    · simp only [Set.mem_setOf_eq] at hr1
      exact ncard_le_of_exists_min hP hrmin' hr1
    · -- Symmetric case `P r = -1`: apply the previous case to `-P`.
      simp only [Set.mem_setOf_eq] at hr1
      have hmin' : ∀ k : ℤ, (-P).eval k = 1 ∨ (-P).eval k = -1 → r ≤ k := by
        intro k hk
        rw [eval_neg] at hk
        rcases hk with h | h
        · exact hrmin' k (Or.inr (neg_eq_iff_eq_neg.mp h))
        · exact hrmin' k (Or.inl (by simpa using neg_eq_iff_eq_neg.mp h))
      have hr' : (-P).eval r = 1 := by simp [eval_neg, hr1]
      have hP' : 0 < (-P).natDegree := by rwa [natDegree_neg]
      have hres := ncard_le_of_exists_min hP' hmin' hr'
      have hneg : ({k : ℤ | (-P).eval k = 1} ∪ {k : ℤ | (-P).eval k = -1})
          = {k : ℤ | P.eval k = 1} ∪ {k : ℤ | P.eval k = -1} := by
        ext k
        simp only [eval_neg, Set.mem_union, Set.mem_setOf_eq, neg_eq_iff_eq_neg, neg_neg]
        exact or_comm
      rwa [hneg, natDegree_neg] at hres
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Set.ncard_empty]
    exact Nat.zero_le _

end Imo1974P6
