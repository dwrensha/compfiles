/-
Copyright (c) 2026 The Compfiles Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 2000, Problem 3

Let n ≥ 2 be a positive integer and λ a positive real number. Initially there are n fleas
on a horizontal line, not all at the same point. We define a move as choosing two fleas at
some points A and B, with A to the left of B, and letting the flea from A jump over the
flea from B to the point C so that BC/AB = λ.

Determine all values of λ such that, for any point M on the line and for any initial
position of the n fleas, there exists a sequence of moves that will take them all to
the right of M.
-/

namespace Imo2000P3

open Finset

/-- A single move with jump ratio `lam`: flea `i`, sitting at some point `A = x i`,
jumps over flea `j` at `B = x j` (with `A` to the left of `B`) and lands at the point
`C = B + lam * (B - A)`, so that `BC / AB = lam`. All other fleas stay put. -/
def Move (lam : ℝ) {n : ℕ} (x y : Fin n → ℝ) : Prop :=
  ∃ i j, x i < x j ∧ y = Function.update x i (x j + lam * (x j - x i))

/-- `Reachable lam x y` means that configuration `y` can be reached from configuration
`x` by a finite sequence of moves with jump ratio `lam`. -/
def Reachable (lam : ℝ) {n : ℕ} (x y : Fin n → ℝ) : Prop :=
  Relation.ReflTransGen (Move lam) x y

/-- The property of `lam` in the problem: starting from any initial configuration in
which the fleas are not all at the same point, for every point `M` on the line there is
a finite sequence of moves taking all the fleas strictly to the right of `M`. -/
def AllRightOf {n : ℕ} (lam : ℝ) : Prop :=
  ∀ x : Fin n → ℝ, (∃ i j, x i ≠ x j) → ∀ M : ℝ,
    ∃ y : Fin n → ℝ, Reachable lam x y ∧ ∀ i, M < y i

snip begin

/-- The position of the rightmost flea. -/
noncomputable def rightmost {n : ℕ} (x : Fin n → ℝ) : ℝ := ⨆ i, x i

/-- The position of the leftmost flea. -/
noncomputable def leftmost {n : ℕ} (x : Fin n → ℝ) : ℝ := ⨅ i, x i

/-- Gerhard Woeginger's potential function: the sum of the distances of the fleas from
the rightmost flea. -/
noncomputable def potential {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ i, (rightmost x - x i)

section

variable {n : ℕ}

lemma bddAbove_range (x : Fin n → ℝ) : BddAbove (Set.range x) :=
  Set.Finite.bddAbove (Set.finite_range x)

lemma bddBelow_range (x : Fin n → ℝ) : BddBelow (Set.range x) :=
  Set.Finite.bddBelow (Set.finite_range x)

lemma le_rightmost (x : Fin n → ℝ) (i : Fin n) : x i ≤ rightmost x :=
  le_ciSup (bddAbove_range x) i

lemma leftmost_le (x : Fin n → ℝ) (i : Fin n) : leftmost x ≤ x i :=
  ciInf_le (bddBelow_range x) i

lemma exists_eq_rightmost [Nonempty (Fin n)] (x : Fin n → ℝ) :
    ∃ m, x m = rightmost x := by
  obtain ⟨m, -, hm⟩ := univ.exists_max_image x univ_nonempty
  exact ⟨m, le_antisymm (le_rightmost x m) (ciSup_le fun k => hm k (mem_univ k))⟩

lemma exists_eq_leftmost [Nonempty (Fin n)] (x : Fin n → ℝ) :
    ∃ m, x m = leftmost x := by
  obtain ⟨m, -, hm⟩ := univ.exists_min_image x univ_nonempty
  exact ⟨m, le_antisymm (le_ciInf fun k => hm k (mem_univ k)) (leftmost_le x m)⟩

lemma potential_eq (x : Fin n → ℝ) :
    potential x = (n : ℝ) * rightmost x - ∑ i, x i := by
  show ∑ i, (rightmost x - x i) = _
  rw [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma potential_nonneg (x : Fin n → ℝ) : 0 ≤ potential x :=
  sum_nonneg fun i _ => sub_nonneg.mpr (le_rightmost x i)

lemma exists_lt_rightmost (x : Fin n → ℝ) (h : 0 < potential x) :
    ∃ k, x k < rightmost x := by
  by_contra hcon
  push Not at hcon
  have h0 : potential x = 0 :=
    sum_eq_zero fun i _ => sub_eq_zero.mpr (le_antisymm (le_rightmost x i) (hcon i)).symm
  linarith

lemma potential_pos (x : Fin n → ℝ) (h : ∃ i j, x i ≠ x j) :
    0 < potential x := by
  obtain ⟨k, hk⟩ : ∃ k, x k < rightmost x := by
    by_contra hcon
    push Not at hcon
    obtain ⟨i, j, hij⟩ := h
    exact hij ((le_antisymm (le_rightmost x i) (hcon i)).trans
      (le_antisymm (le_rightmost x j) (hcon j)).symm)
  exact sum_pos' (fun i _ => sub_nonneg.mpr (le_rightmost x i))
    ⟨k, mem_univ k, sub_pos.mpr hk⟩

lemma sum_update (x : Fin n → ℝ) (i : Fin n) (c : ℝ) :
    ∑ k, Function.update x i c k = ∑ k, x k + (c - x i) := by
  have h2 : ∑ k ∈ univ.erase i, Function.update x i c k = ∑ k ∈ univ.erase i, x k :=
    sum_congr rfl fun k hk => Function.update_of_ne (ne_of_mem_erase hk) c x
  have h3 : Function.update x i c i + ∑ k ∈ univ.erase i, Function.update x i c k =
      ∑ k, Function.update x i c k := add_sum_erase _ _ (mem_univ i)
  have h4 : x i + ∑ k ∈ univ.erase i, x k = ∑ k, x k := add_sum_erase _ _ (mem_univ i)
  rw [Function.update_self] at h3
  linarith

lemma rightmost_update_of_le [Nonempty (Fin n)] (x : Fin n → ℝ) (i : Fin n) {c : ℝ}
    (hc : ∀ k, x k ≤ c) : rightmost (Function.update x i c) = c := by
  apply le_antisymm
  · apply ciSup_le
    intro k
    by_cases hki : k = i
    · rw [hki]
      exact le_of_eq (Function.update_self i c x)
    · rw [Function.update_of_ne hki]
      exact hc k
  · have h := le_rightmost (Function.update x i c) i
    rw [Function.update_self] at h
    exact h

/-- The key inequality for the necessity direction: a single move decreases the potential
by at least `(1 / lam - (n - 1))` times the amount by which the rightmost flea advances. -/
lemma move_potential_bound (hn : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    {x y : Fin n → ℝ} (h : Move lam x y) :
    (1 / lam - ((n : ℝ) - 1)) * (rightmost y - rightmost x) ≤
      potential x - potential y := by
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨i, j, hij, rfl⟩ := h
  set c := x j + lam * (x j - x i) with hc
  have hci : 0 < c - x i := by
    have h2 := mul_pos hlam (sub_pos.mpr hij)
    linarith
  have hrmax : rightmost (Function.update x i c) = max (rightmost x) c := by
    apply le_antisymm
    · apply ciSup_le
      intro k
      by_cases hki : k = i
      · rw [hki]
        rw [Function.update_self]
        exact le_max_right _ _
      · rw [Function.update_of_ne hki]
        exact (le_rightmost x k).trans (le_max_left _ _)
    · apply max_le
      · obtain ⟨m, hm⟩ := exists_eq_rightmost x
        have hmi : m ≠ i := by
          rintro rfl
          have hle : x j ≤ rightmost x := le_rightmost x j
          rw [← hm] at hle
          exact not_le.mpr hij hle
        calc rightmost x = x m := hm.symm
          _ = Function.update x i c m := (Function.update_of_ne hmi c x).symm
          _ ≤ rightmost _ := le_rightmost _ m
      · have h3 := le_rightmost (Function.update x i c) i
        rw [Function.update_self] at h3
        exact h3
  have hsum : ∑ k, Function.update x i c k = ∑ k, x k + (c - x i) := sum_update x i c
  have hpot : potential x - potential (Function.update x i c) =
      (c - x i) - (n : ℝ) * (rightmost (Function.update x i c) - rightmost x) := by
    rw [potential_eq x, potential_eq (Function.update x i c), hsum]
    ring
  by_cases hcase : c ≤ rightmost x
  · -- the rightmost flea does not move
    have hr : rightmost (Function.update x i c) = rightmost x := by
      rw [hrmax, max_eq_left hcase]
    rw [hr] at hpot
    rw [hr]
    simp only [sub_self, mul_zero]
    linarith
  · -- the rightmost flea moves to `c`
    have hcr : rightmost x < c := lt_of_not_ge hcase
    have hr : rightmost (Function.update x i c) = c := by
      rw [hrmax, max_eq_right (le_of_lt hcr)]
    have hz : c - rightmost x ≤ lam * (rightmost x - x i) := by
      have h2 := le_rightmost x j
      have h3 : lam * (x j - x i) ≤ lam * (rightmost x - x i) :=
        mul_le_mul_of_nonneg_left (sub_le_sub_right (le_rightmost x j) _) (le_of_lt hlam)
      linarith
    have hd : (c - rightmost x) / lam ≤ rightmost x - x i :=
      (div_le_iff₀ hlam).mpr (by linarith [hz])
    have hk0 : (1 / lam - ((n : ℝ) - 1)) * (c - rightmost x) =
        (c - rightmost x) / lam - ((n : ℝ) - 1) * (c - rightmost x) := by
      rw [sub_mul, div_eq_mul_inv, one_mul]
      ring
    rw [hr] at hpot
    rw [hr, hk0]
    linarith [hd]

/-- The inequality of `move_potential_bound` telescopes along any sequence of moves. -/
lemma reachable_potential_bound (hn : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    {x y : Fin n → ℝ} (h : Reachable lam x y) :
    (1 / lam - ((n : ℝ) - 1)) * (rightmost y - rightmost x) ≤
      potential x - potential y := by
  unfold Reachable at h
  induction h with
  | refl => simp
  | tail _ hmove ih =>
    have h1 := move_potential_bound hn hlam hmove
    linarith

/-- Necessity: if `0 < lam < 1 / (n - 1)`, then the rightmost flea stays bounded, so the
fleas cannot all be moved arbitrarily far to the right. -/
lemma not_allRightOf_of_lt (hn : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hlt : lam < 1 / ((n : ℝ) - 1)) : ¬ AllRightOf (n := n) lam := by
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have h2 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le one_lt_two hn
    linarith
  have hk0 : (0 : ℝ) < 1 / lam - ((n : ℝ) - 1) := by
    have h2 : 1 / (1 / ((n : ℝ) - 1)) < 1 / lam := one_div_lt_one_div_of_lt hlam hlt
    rw [one_div_one_div] at h2
    linarith
  set x₀ : Fin n → ℝ := fun k => (k : ℝ) with hx₀
  have hnc : ∃ i j, x₀ i ≠ x₀ j := by
    refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ?_⟩
    intro hcon
    rw [hx₀] at hcon
    have h2 : ((⟨0, by omega⟩ : Fin n).val : ℝ) = ((⟨1, by omega⟩ : Fin n).val : ℝ) := hcon
    have h3 : (⟨0, by omega⟩ : Fin n).val = (⟨1, by omega⟩ : Fin n).val :=
      Nat.cast_injective h2
    exact Nat.zero_ne_one h3
  intro hPA
  obtain ⟨y, hyreach, hyM⟩ := hPA x₀ hnc
    (rightmost x₀ + potential x₀ / (1 / lam - ((n : ℝ) - 1)))
  have hb := reachable_potential_bound hn hlam hyreach
  have hp0 := potential_nonneg y
  have hr : rightmost y ≤ rightmost x₀ + potential x₀ / (1 / lam - ((n : ℝ) - 1)) := by
    have h3 : (1 / lam - ((n : ℝ) - 1)) * (rightmost y - rightmost x₀) ≤ potential x₀ := by
      linarith
    have h4 : rightmost y - rightmost x₀ ≤ potential x₀ / (1 / lam - ((n : ℝ) - 1)) := by
      rw [le_div_iff₀ hk0]
      linarith
    linarith
  have h5 := hyM ⟨0, by omega⟩
  have h6 := le_rightmost y ⟨0, by omega⟩
  linarith

/-- One step of Woeginger's strategy: move the leftmost flea over the rightmost flea.
The rightmost flea advances by at least `lam * potential x / (n - 1)`, and the potential
does not decrease. -/
lemma strat_step (hn : 2 ≤ n) {lam : ℝ} (hlam : 1 / ((n : ℝ) - 1) ≤ lam)
    (x : Fin n → ℝ) (hp : 0 < potential x) :
    ∃ y, Move lam x y ∧
      rightmost x + lam * potential x / ((n : ℝ) - 1) ≤ rightmost y ∧
      potential x ≤ potential y := by
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have h2 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le one_lt_two hn
    linarith
  have hlampos : 0 < lam := lt_of_lt_of_le (one_div_pos.mpr hn1) hlam
  have h1 : (1 : ℝ) ≤ lam * ((n : ℝ) - 1) := (div_le_iff₀ hn1).mp hlam
  obtain ⟨i, hi⟩ := exists_eq_leftmost x
  obtain ⟨j, hj⟩ := exists_eq_rightmost x
  obtain ⟨k, hk⟩ := exists_lt_rightmost x hp
  have hik : x i ≤ x k := by
    rw [hi]
    exact leftmost_le x k
  have hkj : x k < x j := by
    rw [hj]
    exact hk
  have hgap : (0 : ℝ) < x j - x i := by linarith
  set c := x j + lam * (x j - x i) with hc
  have hcgt : x j < c := by
    have h2 := mul_pos hlampos hgap
    linarith
  have hry : rightmost (Function.update x i c) = c := by
    apply rightmost_update_of_le
    intro l
    exact (le_rightmost x l).trans (by rw [← hj]; exact le_of_lt hcgt)
  have hsum : ∑ l, Function.update x i c l = ∑ l, x l + (c - x i) := sum_update x i c
  have hpot : potential (Function.update x i c) - potential x =
      (((n : ℝ) - 1) * lam - 1) * (x j - x i) := by
    rw [potential_eq x, potential_eq (Function.update x i c), hry, hsum, ← hj, hc]
    ring
  have hcoeff : (0 : ℝ) ≤ ((n : ℝ) - 1) * lam - 1 := by linarith
  have hgapge : potential x ≤ ((n : ℝ) - 1) * (x j - x i) := by
    have h5 : (n : ℝ) * x j - ∑ l, x l = ∑ l, (x j - x l) := by
      rw [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h6 : ∑ l, (x j - x l) = ∑ l ∈ univ.erase j, (x j - x l) := by
      have h7 := add_sum_erase univ (fun l => x j - x l) (mem_univ j)
      simp only [sub_self, zero_add] at h7
      exact h7.symm
    have h8 : ∑ l ∈ univ.erase j, (x j - x l) ≤ (univ.erase j).card • (x j - x i) := by
      apply sum_le_card_nsmul
      intro l _
      have h9 : x i ≤ x l := by
        rw [hi]
        exact leftmost_le x l
      linarith
    rw [card_erase_of_mem (mem_univ j), card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] at h8
    rw [potential_eq x, ← hj]
    linarith
  have hz : lam * potential x / ((n : ℝ) - 1) ≤ lam * (x j - x i) := by
    have h9 : potential x / ((n : ℝ) - 1) ≤ x j - x i :=
      (div_le_iff₀ hn1).mpr (by linarith)
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left h9 (le_of_lt hlampos)
  refine ⟨Function.update x i c, ⟨i, j, by linarith, by rw [hc]⟩, ?_, ?_⟩
  · rw [hry, ← hj]
    linarith
  · have h9 : (0 : ℝ) ≤ (((n : ℝ) - 1) * lam - 1) * (x j - x i) :=
      mul_nonneg hcoeff (le_of_lt hgap)
    linarith

/-- Phase 1 of the strategy: after `t` moves of `strat_step`, the rightmost flea has
advanced by at least `t` times the fixed positive amount `lam * potential x / (n - 1)`. -/
lemma phase1 (hn : 2 ≤ n) {lam : ℝ} (hlam : 1 / ((n : ℝ) - 1) ≤ lam)
    (x : Fin n → ℝ) (hp : 0 < potential x) (t : ℕ) :
    ∃ y, Reachable lam x y ∧ potential x ≤ potential y ∧
      rightmost x + (t : ℝ) * (lam * potential x / ((n : ℝ) - 1)) ≤ rightmost y := by
  induction t with
  | zero => exact ⟨x, Relation.ReflTransGen.refl, le_rfl, by simp⟩
  | succ t ih =>
    obtain ⟨y, hyreach, hyp, hyr⟩ := ih
    obtain ⟨z, hmove, hzr, hzp⟩ := strat_step hn hlam y (lt_of_lt_of_le hp hyp)
    have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
      have h2 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le one_lt_two hn
      linarith
    have hlampos : 0 < lam := lt_of_lt_of_le (one_div_pos.mpr hn1) hlam
    have hδ : lam * potential x / ((n : ℝ) - 1) ≤ lam * potential y / ((n : ℝ) - 1) := by
      have h1 := mul_le_mul_of_nonneg_left hyp (le_of_lt hlampos)
      exact (div_le_div_iff_of_pos_right hn1).mpr h1
    refine ⟨z, hyreach.trans (Relation.ReflTransGen.single hmove), le_trans hyp hzp, ?_⟩
    push_cast
    linarith

/-- Phase 2 of the strategy: if the rightmost flea is already to the right of `M`, then
one can move every remaining flea to the right of `M`, one at a time, by jumping it over
the rightmost flea. -/
lemma phase2 (hn : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam) (M : ℝ) :
    ∀ m : ℕ, ∀ y : Fin n → ℝ, (univ.filter fun k => y k ≤ M).card ≤ m →
      M < rightmost y → ∃ z, Reachable lam y z ∧ ∀ l, M < z l := by
  intro m
  induction m with
  | zero =>
    intro y hcard _
    have hempty : univ.filter (fun k => y k ≤ M) = ∅ :=
      card_eq_zero.mp (Nat.le_zero.mp hcard)
    refine ⟨y, Relation.ReflTransGen.refl, fun l => ?_⟩
    have hl : l ∉ univ.filter (fun k => y k ≤ M) := by
      rw [hempty]
      simp
    simp only [mem_filter, mem_univ, true_and, not_le] at hl
    exact hl
  | succ m ih =>
    intro y hcard hrM
    by_cases hempty : (univ.filter fun k => y k ≤ M).Nonempty
    · obtain ⟨k, hk⟩ := hempty
      rw [mem_filter] at hk
      obtain ⟨-, hkM⟩ := hk
      have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
      obtain ⟨j, hj⟩ := exists_eq_rightmost y
      have hkj : y k < y j := by
        rw [hj]
        exact lt_of_le_of_lt hkM hrM
      set c := y j + lam * (y j - y k) with hc
      have hcgt : y j < c := by
        have h2 := mul_pos hlam (sub_pos.mpr hkj)
        linarith
      have hry : rightmost (Function.update y k c) = c := by
        apply rightmost_update_of_le
        intro l
        exact (le_rightmost y l).trans (by rw [← hj]; exact le_of_lt hcgt)
      have hcard' : (univ.filter fun l => Function.update y k c l ≤ M).card ≤ m := by
        have hsub : univ.filter (fun l => Function.update y k c l ≤ M) ⊆
            (univ.filter fun l => y l ≤ M).erase k := by
          intro l hl
          rw [mem_filter] at hl
          obtain ⟨-, hlM⟩ := hl
          have hlk : l ≠ k := by
            rintro rfl
            rw [Function.update_self] at hlM
            linarith
          rw [Function.update_of_ne hlk] at hlM
          rw [mem_erase, mem_filter]
          exact ⟨hlk, mem_univ l, hlM⟩
        have hcle := card_le_card hsub
        rw [card_erase_of_mem (by rw [mem_filter]; exact ⟨mem_univ k, hkM⟩)] at hcle
        have hpos : 0 < (univ.filter fun l => y l ≤ M).card :=
          card_pos.mpr ⟨k, by rw [mem_filter]; exact ⟨mem_univ k, hkM⟩⟩
        omega
      obtain ⟨z, hzreach, hzM⟩ :=
        ih (Function.update y k c) hcard' (by rw [hry]; linarith)
      exact ⟨z, (Relation.ReflTransGen.single ⟨k, j, hkj, by rw [hc]⟩).trans hzreach, hzM⟩
    · rw [not_nonempty_iff_eq_empty] at hempty
      refine ⟨y, Relation.ReflTransGen.refl, fun l => ?_⟩
      have hl : l ∉ univ.filter (fun k => y k ≤ M) := by
        rw [hempty]
        simp
      simp only [mem_filter, mem_univ, true_and, not_le] at hl
      exact hl

/-- Sufficiency: if `1 / (n - 1) ≤ lam`, then Woeginger's strategy (first move the
rightmost flea far enough to the right by repeatedly jumping the leftmost flea over it,
then jump every other flea over the rightmost flea) takes all fleas to the right of any
given point `M`. -/
lemma allRightOf_of_ge (hn : 2 ≤ n) {lam : ℝ} (hlam : 1 / ((n : ℝ) - 1) ≤ lam) :
    AllRightOf (n := n) lam := by
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have h2 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le one_lt_two hn
    linarith
  have hlampos : 0 < lam := lt_of_lt_of_le (one_div_pos.mpr hn1) hlam
  intro x hnonconst M
  have hp : 0 < potential x := potential_pos x hnonconst
  have hδpos : 0 < lam * potential x / ((n : ℝ) - 1) :=
    div_pos (mul_pos hlampos hp) hn1
  obtain ⟨t, ht⟩ := exists_nat_gt ((M - rightmost x) / (lam * potential x / ((n : ℝ) - 1)))
  obtain ⟨y, hyreach, hyp, hyr⟩ := phase1 hn hlam x hp t
  have htδ : M - rightmost x < (t : ℝ) * (lam * potential x / ((n : ℝ) - 1)) := by
    rw [div_lt_iff₀ hδpos] at ht
    exact ht
  have hrM : M < rightmost y := by linarith
  obtain ⟨z, hzreach, hzM⟩ :=
    phase2 hn hlampos M (univ.filter (fun k => y k ≤ M)).card y le_rfl hrM
  exact ⟨z, hyreach.trans hzreach, hzM⟩

end

snip end

determine solution_set (n : ℕ) : Set ℝ := Set.Ici (1 / ((n : ℝ) - 1))

problem imo2000_p3 (n : ℕ) (hn : 2 ≤ n) (lam : ℝ) :
    lam ∈ solution_set n ↔ (0 < lam ∧ AllRightOf (n := n) lam) := by
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have h2 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le one_lt_two hn
    linarith
  unfold solution_set
  rw [Set.mem_Ici]
  constructor
  · intro hge
    exact ⟨lt_of_lt_of_le (one_div_pos.mpr hn1) hge, allRightOf_of_ge hn hge⟩
  · rintro ⟨hpos, hP⟩
    by_contra hnot
    rw [not_le] at hnot
    exact not_allRightOf_of_lt hn hpos hnot hP

end Imo2000P3
