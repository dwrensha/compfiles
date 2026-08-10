/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Int.Star
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 1994, Problem 5

Let |U|, σ(U) and π(U) denote the number of elements, the sum, and the
product, respectively, of a finite set U of positive integers. (If U is the
empty set, |U| = 0, σ(U) = 0, π(U) = 1.) Let S be a finite set of positive
integers. As usual, we define (n k) = n! / (k! (n-k)!) for 0 ≤ k ≤ n and
(n k) = 0 otherwise. Prove that

  ∑_{U ⊆ S} (-1)^{|U|} (m - σ(U) choose |S|) = π(S)

for all integers m ≥ σ(S).
-/

namespace Usa1994P5

snip begin

/-- The alternating sum `∑_{U ⊆ s} (-1)^{|U|} (m - σ(U)).choose k`,
viewed as an integer. -/
def altSum (s : Finset ℕ) (k m : ℕ) : ℤ :=
  ∑ U ∈ s.powerset, (-1 : ℤ) ^ U.card * ((m - ∑ i ∈ U, i).choose k : ℤ)

/-- Splitting off the element `x`: summing over subsets of `insert x s`
separates the subsets not containing `x` from those containing it. -/
theorem altSum_insert {s : Finset ℕ} {x : ℕ} (hx : x ∉ s) (k m : ℕ) :
    altSum (insert x s) k m = altSum s k m - altSum s k (m - x) := by
  have hdisj : Disjoint s.powerset ((s.powerset).image (insert x)) := by
    rw [Finset.disjoint_left]
    intro U hU hU2
    rw [Finset.mem_image] at hU2
    obtain ⟨V, -, hVU⟩ := hU2
    have hxU : x ∈ U := hVU ▸ Finset.mem_insert_self x V
    exact hx (Finset.mem_powerset.mp hU hxU)
  have hinj : ∀ U ∈ s.powerset, ∀ V ∈ s.powerset, insert x U = insert x V → U = V := by
    intro U hU V hV h
    have hU' : x ∉ U := fun hmem ↦ hx (Finset.mem_powerset.mp hU hmem)
    have hV' : x ∉ V := fun hmem ↦ hx (Finset.mem_powerset.mp hV hmem)
    have e1 : (insert x U).erase x = U := Finset.erase_insert hU'
    have e2 : (insert x V).erase x = V := Finset.erase_insert hV'
    rw [← e1, ← e2, h]
  have hterm : ∀ U ∈ s.powerset,
      (-1 : ℤ) ^ (insert x U).card * ((m - ∑ i ∈ insert x U, i).choose k : ℤ)
        = -((-1 : ℤ) ^ U.card * ((m - x - ∑ i ∈ U, i).choose k : ℤ)) := by
    intro U hU
    have hU' : x ∉ U := fun hmem ↦ hx (Finset.mem_powerset.mp hU hmem)
    rw [Finset.card_insert_of_notMem hU', Finset.sum_insert hU', pow_succ,
      show m - (x + ∑ i ∈ U, i) = m - x - ∑ i ∈ U, i from (Nat.sub_sub m x _).symm]
    ring
  simp only [altSum]
  rw [Finset.powerset_insert, Finset.sum_union hdisj, Finset.sum_image hinj,
    Finset.sum_congr rfl hterm, Finset.sum_neg_distrib]
  ring

/-- Pascal's rule applied termwise: the forward difference of `altSum s (k+1)`
at `m` equals `altSum s k (m-1)`. -/
theorem altSum_sub_one (s : Finset ℕ) (k m : ℕ) (h : ∑ i ∈ s, i < m) :
    altSum s (k + 1) m - altSum s (k + 1) (m - 1) = altSum s k (m - 1) := by
  simp only [altSum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro U hU
  rw [← mul_sub]
  congr 1
  have hsub : ∑ i ∈ U, i ≤ ∑ i ∈ s, i :=
    Finset.sum_le_sum_of_subset (Finset.mem_powerset.mp hU)
  have hσ : ∑ i ∈ U, i < m := lt_of_le_of_lt hsub h
  have hx1 : 0 < m - ∑ i ∈ U, i := Nat.sub_pos_of_lt hσ
  obtain ⟨x, hxx⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hx1)
  have h2 : m - 1 - ∑ i ∈ U, i = x := by omega
  rw [h2, hxx]
  have hc : ((x + 1).choose (k + 1) : ℤ) = (x.choose k : ℤ) + (x.choose (k + 1) : ℤ) := by
    exact_mod_cast Nat.choose_succ_succ x k
  linarith

/-- Telescoping the forward differences over `j ∈ range x`. -/
theorem telescope (s : Finset ℕ) (k m x : ℕ) :
    altSum s k m - altSum s k (m - x)
      = ∑ j ∈ Finset.range x, (altSum s k (m - j) - altSum s k (m - j - 1)) := by
  have h := Finset.sum_range_sub' (fun j ↦ altSum s k (m - j)) x
  simp only [Nat.sub_zero] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro j _
  rw [Nat.sub_sub]

/-- The main identity, by induction on the finite set `s`. -/
theorem altSum_card (s : Finset ℕ) :
    ∀ m : ℕ, ∑ i ∈ s, i ≤ m → altSum s s.card m = ∏ i ∈ s, (i : ℤ) := by
  induction s using Finset.induction_on with
  | empty =>
    intro m _
    simp [altSum]
  | @insert x s hx ih =>
    intro m hm
    rw [Finset.sum_insert hx] at hm
    rw [Finset.card_insert_of_notMem hx, Finset.prod_insert hx, altSum_insert hx, telescope]
    trans ∑ _j ∈ Finset.range x, ∏ i ∈ s, (i : ℤ)
    · apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      rw [altSum_sub_one s s.card (m - j) (by omega),
        ih (m - j - 1) (by omega)]
    · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

snip end

problem usa1994_p5 (S : Finset ℕ) (_hS : ∀ s ∈ S, 0 < s) (m : ℕ) (hm : ∑ s ∈ S, s ≤ m) :
    ∑ U ∈ S.powerset, (-1 : ℤ) ^ U.card * ((m - ∑ s ∈ U, s).choose S.card : ℤ)
      = ∏ s ∈ S, s := by
  rw [Nat.cast_prod]
  exact altSum_card S m hm

end Usa1994P5
