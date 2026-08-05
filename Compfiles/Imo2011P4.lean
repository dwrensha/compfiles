/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.Order.Lattice.Nat
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Lemmas
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 2011, Problem 4

Let n > 0 be an integer. We are given a balance and n weights of weight
2^0, 2^1, . . . , 2^(n−1). We are to place each of the n weights on the
balance, one after another, in such a way that the right pan is never
heavier than the left pan. At each step we choose one of the weights that
has not yet been placed on the balance, and place it on either the left
pan or the right pan, until all of the weights have been placed.
Determine the number of ways in which this can be done.
-/

namespace Imo2011P4

open scoped Nat
open scoped List

/-- The imbalance (left pan minus right pan) after a sequence of placements.
A pair `(i, b)` denotes one placement of the weight `2^i`; the boolean is
`true` if the weight is placed on the left pan and `false` if it is placed
on the right pan. -/
def Balance (l : List (ℕ × Bool)) : ℤ :=
  ((l.map fun p ↦ if p.2 then (2 : ℤ) ^ p.1 else -((2 : ℤ) ^ p.1))).sum

/-- A sequence of placements is *valid* if after every step the right pan is
not heavier than the left pan. -/
def ValidSeq (l : List (ℕ × Bool)) : Prop :=
  ∀ pre : List (ℕ × Bool), pre <+: l → 0 ≤ Balance pre

/-- The set of ways to carry out the process with the weights
`2^0, 2^1, ..., 2^(n-1)`: sequences of placements in which every weight is
used exactly once and the right pan is never heavier than the left pan. -/
def Ways (n : ℕ) : Type :=
  { l : List (ℕ × Bool) // l.map Prod.fst ~ List.range n ∧ ValidSeq l }

snip begin

/-!
## Solution sketch

We follow Evan Chen's notes: deleting the weight `2^0 = 1` from a valid
sequence and halving the remaining weights gives a bijection between valid
sequences for `n + 1` weights and pairs of a valid sequence for `n` weights
with one of `2n + 1` insertion choices (insert `2^0` anywhere, on either
pan, except on the right pan at the very beginning). Hence the number of
valid sequences satisfies `a (n+1) = (2n + 1) * a n`, so it is `(2n - 1)‼`.
-/

@[simp] lemma balance_nil : Balance [] = 0 := rfl

@[simp] lemma balance_cons (p : ℕ × Bool) (l : List (ℕ × Bool)) :
    Balance (p :: l) = (if p.2 then (2 : ℤ) ^ p.1 else -((2 : ℤ) ^ p.1)) + Balance l := by
  simp [Balance]

@[simp] lemma balance_append (l₁ l₂ : List (ℕ × Bool)) :
    Balance (l₁ ++ l₂) = Balance l₁ + Balance l₂ := by
  simp [Balance, List.sum_append]

/-- Doubling all weights doubles the imbalance. -/
lemma balance_map_succ (l : List (ℕ × Bool)) :
    Balance (l.map fun p : ℕ × Bool ↦ (p.1 + 1, p.2)) = 2 * Balance l := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, balance_cons, ih]
    by_cases hp2 : p.2 = true <;> simp [hp2, pow_succ] <;> ring

/-- Halving all weights halves the imbalance (all weights here are even). -/
lemma balance_map_pred (l : List (ℕ × Bool)) (h : ∀ p ∈ l, 1 ≤ p.1) :
    2 * Balance (l.map fun p : ℕ × Bool ↦ (p.1 - 1, p.2)) = Balance l := by
  induction l with
  | nil => simp
  | cons p l ih =>
    have hp : 1 ≤ p.1 := h p List.mem_cons_self
    have hl : ∀ q ∈ l, 1 ≤ q.1 := fun q hq ↦ h q (List.mem_cons_of_mem p hq)
    have hpow : (2 : ℤ) ^ p.1 = 2 * (2 : ℤ) ^ (p.1 - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hp]
      rw [pow_succ]
      ring
    simp only [List.map_cons, balance_cons, mul_add, ih hl]
    by_cases hp2 : p.2 = true <;> simp [hp2, hpow]

/-- Key nonzero fact: a nonempty signed sum of *distinct* powers of two is
nonzero. -/
lemma balance_ne_zero {l : List (ℕ × Bool)} (hne : l ≠ []) (hnd : (l.map Prod.fst).Nodup) :
    Balance l ≠ 0 := by
  classical
  -- Triangle inequality bound on the signed sum.
  have htri : ∀ m : List (ℕ × Bool),
      |Balance m| ≤ (m.map fun p ↦ (2 : ℤ) ^ p.1).sum := by
    intro m
    induction m with
    | nil => simp
    | cons p m ihm =>
      simp only [balance_cons, List.map_cons, List.sum_cons]
      refine (abs_add_le ..).trans (add_le_add ?_ ihm)
      have hpow : (0 : ℤ) ≤ (2 : ℤ) ^ p.1 := pow_nonneg (by norm_num) _
      by_cases hp2 : p.2 = true
      · rw [if_pos hp2]
        exact (abs_of_nonneg hpow).le
      · rw [if_neg hp2, abs_neg]
        exact (abs_of_nonneg hpow).le
  -- A nodup list of weights all `< M` has total weight `< 2^M`.
  have hgeom : ∀ (m : List (ℕ × Bool)) (M : ℕ),
      (m.map Prod.fst).Nodup → (∀ p ∈ m, p.1 < M) → |Balance m| < (2 : ℤ) ^ M := by
    intro m M hndm hltM
    have hsum_eq : (m.map fun p ↦ (2 : ℤ) ^ p.1).sum
        = ((m.map Prod.fst).toFinset).sum (fun i ↦ (2 : ℤ) ^ i) := by
      rw [List.sum_toFinset (fun i ↦ (2 : ℤ) ^ i) hndm, List.map_map]
      rfl
    have h2 : ((m.map Prod.fst).toFinset).sum (fun i ↦ (2 : ℤ) ^ i)
        ≤ (Finset.range M).sum (fun i ↦ (2 : ℤ) ^ i) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi
        rw [List.mem_toFinset] at hi
        obtain ⟨p, hpm, rfl⟩ := List.mem_map.mp hi
        rw [Finset.mem_range]
        exact hltM p hpm
      · intro i _ _
        exact pow_nonneg (by norm_num) _
    have h3 : (Finset.range M).sum (fun i ↦ (2 : ℤ) ^ i) = (2 : ℤ) ^ M - 1 := by
      have hmul := geom_sum_mul (2 : ℤ) M
      linarith
    calc |Balance m| ≤ (m.map fun p ↦ (2 : ℤ) ^ p.1).sum := htri m
      _ = ((m.map Prod.fst).toFinset).sum (fun i ↦ (2 : ℤ) ^ i) := hsum_eq
      _ ≤ (Finset.range M).sum (fun i ↦ (2 : ℤ) ^ i) := h2
      _ = (2 : ℤ) ^ M - 1 := h3
      _ < (2 : ℤ) ^ M := by
        have hpos : (0 : ℤ) < (2 : ℤ) ^ M := pow_pos (by norm_num) M
        omega
  -- The largest weight `2^M` dominates the sum of all the others.
  have hSne0 : (l.map Prod.fst).toFinset.Nonempty := by
    cases l with
    | nil => exact absurd rfl hne
    | cons p t => exact ⟨Prod.fst p, List.mem_toFinset.mpr List.mem_cons_self⟩
  set S := (l.map Prod.fst).toFinset with hS
  obtain ⟨M, hM_S, hM_le⟩ : ∃ M ∈ S, ∀ i ∈ S, i ≤ M :=
    ⟨S.max' hSne0, Finset.max'_mem S hSne0, fun i hi ↦ Finset.le_max' S i hi⟩
  rw [hS] at hM_S
  obtain ⟨⟨a, b⟩, hab_mem, habM⟩ := List.mem_map.mp (List.mem_toFinset.mp hM_S)
  dsimp only at habM
  subst a
  obtain ⟨l₁, l₂, hsplit⟩ := List.mem_iff_append.mp hab_mem
  subst l
  simp only [List.map_append, List.map_cons] at hnd
  obtain ⟨hnd₁, hnd₂c, hdisj⟩ := List.nodup_append.mp hnd
  obtain ⟨hM₂, hnd₂⟩ := List.nodup_cons.mp hnd₂c
  have hM₁ : M ∉ l₁.map Prod.fst := fun hx ↦ hdisj _ hx _ List.mem_cons_self rfl
  have hnd_m : ((l₁ ++ l₂).map Prod.fst).Nodup := by
    rw [List.map_append]
    exact List.nodup_append.mpr
      ⟨hnd₁, hnd₂, fun x hx₁ y hy₂ ↦ hdisj x hx₁ y (List.mem_cons_of_mem M hy₂)⟩
  have hlt : ∀ p ∈ l₁ ++ l₂, p.1 < M := by
    intro p hp
    have hpS : p.1 ∈ S := by
      rw [hS, List.mem_toFinset]
      have hpl : p ∈ l₁ ++ (M, b) :: l₂ := by
        rw [List.mem_append] at hp ⊢
        rcases hp with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
      exact List.mem_map_of_mem hpl
    have hle : p.1 ≤ M := hM_le p.1 hpS
    have hneM : p.1 ≠ M := by
      intro hEq
      have hMem : M ∈ (l₁ ++ l₂).map Prod.fst := by
        rw [← hEq]
        exact List.mem_map_of_mem hp
      rw [List.map_append, List.mem_append] at hMem
      rcases hMem with h | h
      · exact hM₁ h
      · exact hM₂ h
    exact lt_of_le_of_ne hle hneM
  have hbal : |Balance l₁ + Balance l₂| < (2 : ℤ) ^ M := by
    have h := hgeom (l₁ ++ l₂) M hnd_m hlt
    rwa [balance_append] at h
  rw [abs_lt] at hbal
  simp only [balance_append, balance_cons]
  intro hzero
  split at hzero <;> omega

/-- A prefix of an append either lies in the first part or extends it. -/
lemma prefix_append_cases {α : Type*} {pre X Y : List α} (h : pre <+: X ++ Y) :
    pre <+: X ∨ ∃ pre', pre = X ++ pre' ∧ pre' <+: Y := by
  obtain ⟨s, hs⟩ := h
  rcases List.append_eq_append_iff.mp hs with ⟨a, hX, hs'⟩ | ⟨a, hpre, hY⟩
  · exact Or.inl ⟨a, hX.symm⟩
  · exact Or.inr ⟨a, hpre, ⟨s, hY.symm⟩⟩

/-- A prefix of a cons is either empty or starts with the head. -/
lemma prefix_cons_cases {α : Type*} {pre : List α} {x : α} {Y : List α}
    (h : pre <+: x :: Y) : pre = [] ∨ ∃ pre', pre = x :: pre' ∧ pre' <+: Y := by
  obtain ⟨s, hs⟩ := h
  cases pre with
  | nil => exact Or.inl rfl
  | cons y pre' =>
    rw [List.cons_append, List.cons.injEq] at hs
    exact Or.inr ⟨pre', hs.1 ▸ rfl, ⟨s, hs.2⟩⟩

lemma map_down_map_up (l : List (ℕ × Bool)) :
    (l.map fun p : ℕ × Bool ↦ (p.1 + 1, p.2)).map (fun p : ℕ × Bool ↦ (p.1 - 1, p.2)) = l := by
  induction l with
  | nil => rfl
  | cons p l ih => simp_all

lemma map_up_map_down (l : List (ℕ × Bool)) (h : ∀ p ∈ l, 1 ≤ p.1) :
    (l.map fun p : ℕ × Bool ↦ (p.1 - 1, p.2)).map (fun p : ℕ × Bool ↦ (p.1 + 1, p.2)) = l := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    have hp : 1 ≤ p.1 := h p List.mem_cons_self
    have hpl : ∀ q ∈ l, 1 ≤ q.1 := fun q hq ↦ h q (List.mem_cons_of_mem _ hq)
    simp only [List.map_cons, List.cons.injEq]
    refine ⟨?_, ih hpl⟩
    show (p.1 - 1 + 1, p.2) = p
    have h1 : p.1 - 1 + 1 = p.1 := by omega
    rw [h1]

lemma ways_length {n : ℕ} (w : Ways n) : w.1.length = n := by
  have h := List.Perm.length_eq w.2.1
  rwa [List.length_map, List.length_range] at h

lemma ways_nodup {n : ℕ} (w : Ways n) : (w.1.map Prod.fst).Nodup :=
  (List.Perm.nodup_iff w.2.1).mpr List.nodup_range

/-- The position of the weight `2^0` in a valid sequence. -/
abbrev removeIdx {n : ℕ} (w : Ways (n + 1)) : ℕ := w.1.findIdx fun p ↦ p.1 == 0

lemma ways_findIdx_lt {n : ℕ} (w : Ways (n + 1)) :
    (w.1.findIdx fun p ↦ p.1 == 0) < w.1.length := by
  rw [List.findIdx_lt_length]
  have h0 : (0 : ℕ) ∈ List.range (n + 1) := List.mem_range.mpr (Nat.succ_pos n)
  have h0' : (0 : ℕ) ∈ w.1.map Prod.fst := (List.Perm.mem_iff w.2.1).mpr h0
  obtain ⟨p, hp, hp0⟩ := List.mem_map.mp h0'
  exact ⟨p, hp, beq_iff_eq.mpr hp0⟩

/-- The pan on which the weight `2^0` was placed. -/
abbrev removePan {n : ℕ} (w : Ways (n + 1)) : Bool :=
  (w.1[(removeIdx w)]'(ways_findIdx_lt w)).2

lemma ways_getElem_fst {n : ℕ} (w : Ways (n + 1)) :
    (w.1[(w.1.findIdx fun p ↦ p.1 == 0)]'(ways_findIdx_lt w)).1 = 0 := by
  have h := List.findIdx_getElem (p := fun p : ℕ × Bool ↦ p.1 == 0) (xs := w.1)
    (w := ways_findIdx_lt w)
  exact beq_iff_eq.mp h

/-- A valid sequence splits around its `2^0` weight. -/
lemma ways_split {n : ℕ} (w : Ways (n + 1)) :
    w.1 = w.1.take (removeIdx w) ++ (0, removePan w) :: w.1.drop (removeIdx w + 1) := by
  have helem : (w.1[(removeIdx w)]'(ways_findIdx_lt w)) = (0, removePan w) :=
    Prod.ext (ways_getElem_fst w) rfl
  conv_lhs => rw [← List.take_append_drop (removeIdx w) w.1]
  rw [← List.getElem_cons_drop (ways_findIdx_lt w)]
  rw [helem]

/-- The weights before and after the `2^0` weight are all even. -/
lemma ways_fst_pos {n : ℕ} (w : Ways (n + 1)) :
    (∀ p ∈ w.1.take (removeIdx w), 1 ≤ p.1) ∧
    (∀ p ∈ w.1.drop (removeIdx w + 1), 1 ≤ p.1) := by
  have hnd : (w.1.map Prod.fst).Nodup :=
    (List.Perm.nodup_iff w.2.1).mpr List.nodup_range
  rw [ways_split w, List.map_append, List.map_cons, List.nodup_append, List.nodup_cons] at hnd
  dsimp only at hnd
  obtain ⟨hnd1, ⟨h0not, hnd3⟩, hdisj⟩ := hnd
  have h0₁ : (0 : ℕ) ∉ (w.1.take (removeIdx w)).map Prod.fst :=
    fun hx ↦ hdisj _ hx _ List.mem_cons_self rfl
  refine ⟨fun p hp ↦ Nat.one_le_iff_ne_zero.mpr fun hp0 ↦ h0₁ (List.mem_map.mpr ⟨p, hp, hp0⟩),
          fun p hp ↦ Nat.one_le_iff_ne_zero.mpr fun hp0 ↦ h0not (List.mem_map.mpr ⟨p, hp, hp0⟩)⟩

/-- The list of placements with the `2^0` weight removed and the remaining
weights halved. -/
abbrev removeList {n : ℕ} (w : Ways (n + 1)) : List (ℕ × Bool) :=
  (w.1.take (removeIdx w) ++ w.1.drop (removeIdx w + 1)).map fun p : ℕ × Bool ↦ (p.1 - 1, p.2)

/-- Inserting a fresh `2^0` weight at position `k` on pan `b` into a list of
placements whose weights are all doubled. -/
abbrev insertList (lr : List (ℕ × Bool)) (k : ℕ) (b : Bool) : List (ℕ × Bool) :=
  (lr.map fun p : ℕ × Bool ↦ (p.1 + 1, p.2)).take k ++ (0, b) :: (lr.map fun p : ℕ × Bool ↦ (p.1 + 1, p.2)).drop k

/-- Removing the weight `2^0` and halving preserves validity: before the
removed weight the imbalances are unchanged, and afterwards the (even)
imbalance without the `±1` contribution can only drop by `1`, so it stays
nonnegative. -/
lemma validSeq_remove {b : Bool} {l₁ l₂ : List (ℕ × Bool)}
    (hfst₁ : ∀ p ∈ l₁, 1 ≤ p.1) (hfst₂ : ∀ p ∈ l₂, 1 ≤ p.1)
    (hval : ValidSeq (l₁ ++ (0, b) :: l₂)) :
    ValidSeq ((l₁ ++ l₂).map fun p : ℕ × Bool ↦ (p.1 - 1, p.2)) := by
  intro pre hpre
  have hfstX : ∀ p ∈ l₁ ++ l₂, 1 ≤ p.1 := fun p hp ↦
    (List.mem_append.mp hp).elim (hfst₁ p) (hfst₂ p)
  have hpre_eq : pre = ((l₁ ++ l₂).take pre.length).map (fun p : ℕ × Bool ↦ (p.1 - 1, p.2)) := by
    have h1 := (List.prefix_iff_eq_take).mp hpre
    nth_rewrite 1 [h1]
    rw [← List.map_take]
  set q := (l₁ ++ l₂).take pre.length with hq
  have hfstq : ∀ p ∈ q, 1 ≤ p.1 := fun p hp ↦ hfstX p ((List.take_prefix _ _).subset hp)
  have h2 := balance_map_pred q hfstq
  have hpreB : Balance pre = Balance (q.map fun p : ℕ × Bool ↦ (p.1 - 1, p.2)) := by rw [hpre_eq]
  by_cases hlen : pre.length ≤ l₁.length
  · have hqeq : q = l₁.take pre.length := by rw [hq, List.take_append_of_le_length hlen]
    have h0 : 0 ≤ Balance q := by
      apply hval
      rw [hqeq]
      exact (List.take_prefix _ _).trans (List.prefix_append _ _)
    omega
  · push Not at hlen
    have hqeq : q = l₁ ++ l₂.take (pre.length - l₁.length) := by
      rw [hq, List.take_append, List.take_of_length_le (le_of_lt hlen)]
    have hqB : Balance q = Balance l₁ + Balance (l₂.take (pre.length - l₁.length)) := by
      rw [hqeq, balance_append]
    rw [hqB] at h2
    have hPpre : l₁ ++ (0, b) :: l₂.take (pre.length - l₁.length) <+: l₁ ++ (0, b) :: l₂ := by
      obtain ⟨s, hs⟩ := List.take_prefix (pre.length - l₁.length) l₂
      exact ⟨s, by simp only [List.append_assoc, List.cons_append]; rw [hs]⟩
    have h0 := hval _ hPpre
    have h0e : Balance (l₁ ++ (0, b) :: l₂.take (pre.length - l₁.length)) =
        Balance l₁ + ((if b then (2 : ℤ) ^ 0 else -((2 : ℤ) ^ 0)) +
          Balance (l₂.take (pre.length - l₁.length))) := by
      rw [balance_append, balance_cons]
    have hε : (if b then (2 : ℤ) ^ 0 else -((2 : ℤ) ^ 0)) = 1 ∨
        (if b then (2 : ℤ) ^ 0 else -((2 : ℤ) ^ 0)) = -1 := by
      cases b <;> simp
    omega

lemma removeList_perm {n : ℕ} (w : Ways (n + 1)) :
    (removeList w).map Prod.fst ~ List.range n := by
  have hfst := ways_fst_pos w
  have h1 : (w.1.take (removeIdx w) ++ w.1.drop (removeIdx w + 1)).map Prod.fst ~
      (List.range (n + 1)).erase 0 := by
    have hperme := List.Perm.erase 0 w.2.1
    rw [ways_split w, List.map_append, List.map_cons] at hperme
    dsimp only at hperme
    have h0₁ : (0 : ℕ) ∉ (w.1.take (removeIdx w)).map Prod.fst := by
      rintro hmem
      obtain ⟨p, hp, hp0⟩ := List.mem_map.mp hmem
      have := hfst.1 p hp; omega
    have h0₂ : (0 : ℕ) ∉ (w.1.drop (removeIdx w + 1)).map Prod.fst := by
      rintro hmem
      obtain ⟨p, hp, hp0⟩ := List.mem_map.mp hmem
      have := hfst.2 p hp; omega
    rw [List.erase_append_right _ h0₁, List.erase_cons_head] at hperme
    rw [List.map_append]
    exact hperme
  have h2 : (List.range (n + 1)).erase 0 = (List.range n).map Nat.succ := by
    rw [List.range_succ_eq_map, List.erase_cons_head]
  unfold removeList
  rw [List.map_map]
  have h3 : (Prod.fst ∘ fun p : ℕ × Bool ↦ (p.1 - 1, p.2)) = (fun x ↦ x - 1) ∘ Prod.fst := rfl
  rw [h3, ← List.map_map]
  calc ((w.1.take (removeIdx w) ++ w.1.drop (removeIdx w + 1)).map Prod.fst).map (· - 1)
      ~ ((List.range n).map Nat.succ).map (· - 1) := List.Perm.map _ (h2 ▸ h1)
    _ = List.range n := by
        rw [List.map_map]
        have h4 : ((fun x : ℕ ↦ x - 1) ∘ Nat.succ) = id := rfl
        rw [h4, List.map_id]

lemma removeList_valid {n : ℕ} (w : Ways (n + 1)) : ValidSeq (removeList w) := by
  have hval : ValidSeq (w.1.take (removeIdx w) ++ (0, removePan w) :: w.1.drop (removeIdx w + 1)) := by
    rw [← ways_split w]; exact w.2.2
  exact validSeq_remove (ways_fst_pos w).1 (ways_fst_pos w).2 hval

/-- Inserting the weight `2^0` into a valid sequence of doubled weights
preserves validity: prefixes before the insertion point keep their
(nonnegative, doubled) imbalance; later prefixes have imbalance
`2d ± 1` with `d ≥ 0`, and when the new weight goes on the right pan the
insertion is not at the beginning, so `d ≠ 0` (a nonempty signed sum of
distinct powers of two), hence `d ≥ 1`. -/
lemma validSeq_insert {lr : List (ℕ × Bool)} (hnd : (lr.map Prod.fst).Nodup)
    (hval : ValidSeq lr) {k : ℕ} (hk : k ≤ lr.length) {b : Bool} (hb : b = false → 1 ≤ k) :
    ValidSeq (insertList lr k b) := by
  unfold insertList
  intro pre hpre
  rcases prefix_append_cases hpre with hp | ⟨pre', hpre_eq, hp'⟩
  · have hpm : pre <+: (lr.map fun p : ℕ × Bool ↦ (p.1 + 1, p.2)) := hp.trans (List.take_prefix _ _)
    have hpre_eq : pre = (lr.take pre.length).map (fun p : ℕ × Bool ↦ (p.1 + 1, p.2)) := by
      have h1 := (List.prefix_iff_eq_take).mp hpm
      nth_rewrite 1 [h1]
      rw [← List.map_take]
    rw [hpre_eq, balance_map_succ]
    have h0 := hval _ (List.take_prefix pre.length lr)
    omega
  · rcases prefix_cons_cases hp' with rfl | ⟨pre'', hpre'_eq, hp''⟩
    · rw [List.append_nil] at hpre_eq
      have hpm : pre <+: (lr.map fun p : ℕ × Bool ↦ (p.1 + 1, p.2)) := by
        rw [hpre_eq]; exact List.take_prefix _ _
      have hpre_eq2 : pre = (lr.take pre.length).map (fun p : ℕ × Bool ↦ (p.1 + 1, p.2)) := by
        have h1 := (List.prefix_iff_eq_take).mp hpm
        nth_rewrite 1 [h1]
        rw [← List.map_take]
      rw [hpre_eq2, balance_map_succ]
      have h0 := hval _ (List.take_prefix pre.length lr)
      omega
    · have hpre''_eq : pre'' = ((lr.drop k).take pre''.length).map (fun p : ℕ × Bool ↦ (p.1 + 1, p.2)) := by
        have h1 := (List.prefix_iff_eq_take).mp hp''
        nth_rewrite 1 [h1]
        rw [← List.map_drop, ← List.map_take]
      have hb1 : Balance ((lr.map fun p : ℕ × Bool ↦ (p.1 + 1, p.2)).take k) = 2 * Balance (lr.take k) := by
        rw [← List.map_take, balance_map_succ]
      have hb2 : Balance pre'' = 2 * Balance ((lr.drop k).take pre''.length) := by
        nth_rewrite 1 [hpre''_eq]
        rw [balance_map_succ]
      have hmerge : Balance (lr.take (k + pre''.length)) =
          Balance (lr.take k) + Balance ((lr.drop k).take pre''.length) := by
        have hcomb : lr.take k ++ (lr.drop k).take pre''.length = lr.take (k + pre''.length) := by
          rw [List.take_add]
        rw [← hcomb, balance_append]
      have hq : 0 ≤ Balance (lr.take (k + pre''.length)) := hval _ (List.take_prefix (k + pre''.length) lr)
      have hpreB : Balance pre = Balance ((lr.map fun p : ℕ × Bool ↦ (p.1 + 1, p.2)).take k) +
          ((if b then (2 : ℤ) ^ 0 else -((2 : ℤ) ^ 0)) + Balance pre'') := by
        rw [hpre_eq, hpre'_eq, balance_append, balance_cons]
      cases b with
      | true =>
        simp at hpreB
        omega
      | false =>
        have hk1 : 1 ≤ k := hb rfl
        have hqnz : Balance (lr.take (k + pre''.length)) ≠ 0 := by
          apply balance_ne_zero
          · intro h
            have hl := congrArg List.length h
            rw [List.length_take, List.length_nil] at hl
            omega
          · exact List.Sublist.nodup ((List.take_prefix _ _).sublist.map _) hnd
        simp at hpreB
        omega

lemma insertZero_perm {n : ℕ} {lr : List (ℕ × Bool)}
    (hperm : lr.map Prod.fst ~ List.range n) {k : ℕ} (b : Bool) :
    (insertList lr k b).map Prod.fst ~ List.range (n + 1) := by
  have hmfst : (lr.map fun p : ℕ × Bool ↦ (p.1 + 1, p.2)).map Prod.fst =
      (lr.map Prod.fst).map Nat.succ := by
    rw [List.map_map, List.map_map]
    congr 1
  calc (insertList lr k b).map Prod.fst
      = ((lr.map fun p : ℕ × Bool ↦ (p.1 + 1, p.2)).take k).map Prod.fst ++ 0 ::
          ((lr.map fun p : ℕ × Bool ↦ (p.1 + 1, p.2)).drop k).map Prod.fst := by
        unfold insertList
        rw [List.map_append, List.map_cons]
    _ ~ 0 :: (((lr.map fun p : ℕ × Bool ↦ (p.1 + 1, p.2)).take k).map Prod.fst ++
          ((lr.map fun p : ℕ × Bool ↦ (p.1 + 1, p.2)).drop k).map Prod.fst) := List.perm_middle
    _ = 0 :: (((lr.map fun p : ℕ × Bool ↦ (p.1 + 1, p.2)).take k ++
          (lr.map fun p : ℕ × Bool ↦ (p.1 + 1, p.2)).drop k).map Prod.fst) := by rw [List.map_append]
    _ = 0 :: (lr.map fun p : ℕ × Bool ↦ (p.1 + 1, p.2)).map Prod.fst := by rw [List.take_append_drop]
    _ = 0 :: (lr.map Prod.fst).map Nat.succ := by rw [hmfst]
    _ ~ 0 :: (List.range n).map Nat.succ := List.Perm.cons 0 (List.Perm.map Nat.succ hperm)
    _ = List.range (n + 1) := List.range_succ_eq_map.symm

/-- The insertion data: where and on which pan the weight `2^0` is inserted.
`Sum.inl k` (with `k : Fin (n + 1)`) inserts it on the left pan at position
`k`; `Sum.inr k` (with `k : Fin n`) inserts it on the right pan at position
`k + 1` (the right pan is forbidden at the very beginning). -/
abbrev IData (n : ℕ) : Type := Fin (n + 1) ⊕ Fin n

/-- The weight `2^0` cannot be the first placement if it goes on the right
pan. -/
lemma removePan_false_idx {n : ℕ} (w : Ways (n + 1)) (hp : removePan w = false) :
    1 ≤ removeIdx w := by
  by_contra h
  push Not at h
  have hk0 : removeIdx w = 0 := by omega
  have hsplit := ways_split w
  rw [hk0, hp, List.take_zero, List.nil_append] at hsplit
  have hpre : [(0, false)] <+: w.1 := ⟨w.1.drop 1, hsplit.symm⟩
  have hbal := w.2.2 [(0, false)] hpre
  simp [Balance] at hbal

/-- The valid sequence obtained by removing the weight `2^0` and halving. -/
def removeZeroWays {n : ℕ} (w : Ways (n + 1)) : Ways n :=
  ⟨removeList w, removeList_perm w, removeList_valid w⟩

/-- The insertion data describing where the weight `2^0` sits in a valid
sequence. -/
def removeZeroData {n : ℕ} (w : Ways (n + 1)) : IData n :=
  if hp : removePan w = true then
    Sum.inl ⟨removeIdx w, by
      have h1 := ways_findIdx_lt w; have h2 := ways_length w
      show w.1.findIdx (fun p ↦ p.1 == 0) < n + 1
      omega⟩
  else
    Sum.inr ⟨removeIdx w - 1, by
      have h1 := ways_findIdx_lt w
      have h2 := ways_length w
      have h3 : 1 ≤ w.1.findIdx (fun p ↦ p.1 == 0) :=
        removePan_false_idx w (Eq.mp (Bool.not_eq_true _) hp)
      show w.1.findIdx (fun p ↦ p.1 == 0) - 1 < n
      omega⟩

/-- The valid sequence obtained by inserting the weight `2^0` according to
the given insertion data. -/
def insertZeroWays {n : ℕ} (w : Ways n) (d : IData n) : Ways (n + 1) :=
  d.rec (motive := fun _ ↦ Ways (n + 1))
    (fun k ↦ ⟨insertList w.1 k.1 true,
      insertZero_perm w.2.1 true,
      validSeq_insert (ways_nodup w) w.2.2 (by have h := ways_length w; have := k.2; omega) (by simp)⟩)
    (fun k ↦ ⟨insertList w.1 (k.1 + 1) false,
      insertZero_perm w.2.1 false,
      validSeq_insert (ways_nodup w) w.2.2 (by have h := ways_length w; have := k.2; omega) (by simp)⟩)

@[simp] lemma insertZeroWays_inl_val {n : ℕ} (w : Ways n) (k : Fin (n + 1)) :
    (insertZeroWays w (Sum.inl k)).1 = insertList w.1 k.1 true := rfl

@[simp] lemma insertZeroWays_inr_val {n : ℕ} (w : Ways n) (k : Fin n) :
    (insertZeroWays w (Sum.inr k)).1 = insertList w.1 (k.1 + 1) false := rfl

/-- Removal followed by insertion reconstructs the original sequence. -/
lemma insertList_removeList {n : ℕ} (w : Ways (n + 1)) :
    insertList (removeList w) (removeIdx w) (removePan w) = w.1 := by
  have hfst := ways_fst_pos w
  have hlen1 : (w.1.take (removeIdx w)).length = removeIdx w := by
    rw [List.length_take]; exact min_eq_left (le_of_lt (ways_findIdx_lt w))
  unfold insertList removeList
  rw [map_up_map_down _ (fun p hp ↦ by
    rw [List.mem_append] at hp
    exact hp.elim (hfst.1 p) (hfst.2 p))]
  have htake : (w.1.take (removeIdx w) ++ w.1.drop (removeIdx w + 1)).take (removeIdx w) =
      w.1.take (removeIdx w) := by
    rw [List.take_append_of_le_length (by omega)]
    exact List.take_of_length_le (by omega)
  have hdrop : (w.1.take (removeIdx w) ++ w.1.drop (removeIdx w + 1)).drop (removeIdx w) =
      w.1.drop (removeIdx w + 1) := by
    rw [List.drop_append_of_le_length (by omega)]
    rw [List.drop_eq_nil_of_le (by omega), List.nil_append]
  rw [htake, hdrop]
  exact (ways_split w).symm

/-- The element of an inserted list at the insertion position is the new
`2^0` weight. -/
lemma insertList_getElem {n : ℕ} (w : Ways n) {k : ℕ} (hk : k ≤ w.1.length) (b : Bool)
    (h : k < (insertList w.1 k b).length) : (insertList w.1 k b)[k]'h = (0, b) := by
  unfold insertList
  rw [List.getElem_append_right (by simp only [List.length_take, List.length_map]; omega)]
  have h2 : k - ((w.1.map fun p : ℕ × Bool ↦ (p.1 + 1, p.2)).take k).length = 0 := by
    simp only [List.length_take, List.length_map]; omega
  simp only [h2, List.getElem_cons_zero]

/-- The position of the `2^0` weight in an inserted list is exactly the
insertion position. -/
lemma insertList_findIdx {n : ℕ} (w : Ways n) {k : ℕ} (hk : k ≤ w.1.length) (b : Bool) :
    (insertList w.1 k b).findIdx (fun p ↦ p.1 == 0) = k := by
  have hlen : (insertList w.1 k b).length = w.1.length + 1 := by
    unfold insertList
    rw [List.length_append, List.length_cons, List.length_take, List.length_drop, List.length_map]
    omega
  have hk' : k < (insertList w.1 k b).length := by rw [hlen]; omega
  apply (List.findIdx_eq hk').mpr
  refine ⟨?_, ?_⟩
  · rw [insertList_getElem w hk b]
    rfl
  · intro j hj
    have he : (insertList w.1 k b)[j]'(Nat.lt_trans hj hk') =
        (w.1.map fun p : ℕ × Bool ↦ (p.1 + 1, p.2))[j]'(by simp only [List.length_map]; omega) := by
      unfold insertList
      rw [List.getElem_append_left (by simp only [List.length_take, List.length_map]; omega)]
      rw [List.getElem_take]
    rw [he, List.getElem_map]
    show ((w.1[j]'(by omega)).1 + 1 == 0) = false
    rw [beq_eq_false_iff_ne]
    omega

/-- The key bijection: valid sequences for `n + 1` weights correspond to
valid sequences for `n` weights together with insertion data for the
weight `2^0`. -/
def stepEquiv (n : ℕ) : Ways (n + 1) ≃ Ways n × IData n where
  toFun w := (removeZeroWays w, removeZeroData w)
  invFun p := insertZeroWays p.1 p.2
  left_inv w := by
    apply Subtype.ext
    show (insertZeroWays (removeZeroWays w) (removeZeroData w)).1 = w.1
    cases hp : removePan w with
    | true =>
      obtain ⟨h, hd⟩ : ∃ h, removeZeroData w = Sum.inl ⟨removeIdx w, h⟩ := ⟨_, dif_pos hp⟩
      rw [hd, insertZeroWays_inl_val]
      show insertList (removeList w) (removeIdx w) true = w.1
      have hrl := insertList_removeList w
      rw [hp] at hrl
      exact hrl
    | false =>
      obtain ⟨h, hd⟩ : ∃ h, removeZeroData w = Sum.inr ⟨removeIdx w - 1, h⟩ := ⟨_, dif_neg (by simp [hp])⟩
      rw [hd, insertZeroWays_inr_val]
      show insertList (removeList w) (removeIdx w - 1 + 1) false = w.1
      have h1 := removePan_false_idx w hp
      have h2 : removeIdx w - 1 + 1 = removeIdx w := by omega
      rw [h2]
      have hrl := insertList_removeList w
      rw [hp] at hrl
      exact hrl
  right_inv p := by
    obtain ⟨w', d⟩ := p
    show (removeZeroWays (insertZeroWays w' d), removeZeroData (insertZeroWays w' d)) = (w', d)
    rcases d with k | k
    · have hk : k.1 ≤ w'.1.length := by have h := ways_length w'; have := k.2; omega
      have hidx : removeIdx (insertZeroWays w' (Sum.inl k)) = k.1 := by
        show (insertZeroWays w' (Sum.inl k)).1.findIdx (fun p ↦ p.1 == 0) = k.1
        rw [insertZeroWays_inl_val]
        exact insertList_findIdx w' hk true
      have hpan : removePan (insertZeroWays w' (Sum.inl k)) = true := by
        show ((insertZeroWays w' (Sum.inl k)).1[(removeIdx (insertZeroWays w' (Sum.inl k)))]'
          (ways_findIdx_lt _)).2 = true
        simp only [insertZeroWays_inl_val, hidx]
        rw [insertList_getElem w' hk true]
      apply Prod.ext
      · apply Subtype.ext
        show removeList (insertZeroWays w' (Sum.inl k)) = w'.1
        unfold removeList
        rw [insertZeroWays_inl_val, hidx]
        have htake : (insertList w'.1 k.1 true).take k.1 =
            (w'.1.map fun p : ℕ × Bool ↦ (p.1 + 1, p.2)).take k.1 := by
          unfold insertList
          rw [List.take_append_of_le_length (by rw [List.length_take, List.length_map]; omega)]
          exact List.take_of_length_le (by rw [List.length_take, List.length_map]; omega)
        have hdrop : (insertList w'.1 k.1 true).drop (k.1 + 1) =
            (w'.1.map fun p : ℕ × Bool ↦ (p.1 + 1, p.2)).drop k.1 := by
          unfold insertList
          have h1 : (((w'.1.map fun p : ℕ × Bool ↦ (p.1 + 1, p.2)).take k.1) ++ [(0, true)]).length = k.1 + 1 := by
            rw [List.length_append, List.length_take, List.length_map]
            simp
            omega
          conv_lhs => rw [show (w'.1.map fun p : ℕ × Bool ↦ (p.1 + 1, p.2)).take k.1 ++ (0, true) ::
              (w'.1.map fun p : ℕ × Bool ↦ (p.1 + 1, p.2)).drop k.1 =
              ((w'.1.map fun p : ℕ × Bool ↦ (p.1 + 1, p.2)).take k.1 ++ [(0, true)]) ++
              (w'.1.map fun p : ℕ × Bool ↦ (p.1 + 1, p.2)).drop k.1 by
            rw [List.append_assoc, List.singleton_append]]
          rw [← h1, List.drop_left]
        rw [htake, hdrop, List.take_append_drop, map_down_map_up]
      · show removeZeroData (insertZeroWays w' (Sum.inl k)) = Sum.inl k
        unfold removeZeroData
        rw [dif_pos hpan]
        simp only [hidx]
    · have hk : k.1 + 1 ≤ w'.1.length := by have h := ways_length w'; have := k.2; omega
      have hidx : removeIdx (insertZeroWays w' (Sum.inr k)) = k.1 + 1 := by
        show (insertZeroWays w' (Sum.inr k)).1.findIdx (fun p ↦ p.1 == 0) = k.1 + 1
        rw [insertZeroWays_inr_val]
        exact insertList_findIdx w' hk false
      have hpan : removePan (insertZeroWays w' (Sum.inr k)) = false := by
        show ((insertZeroWays w' (Sum.inr k)).1[(removeIdx (insertZeroWays w' (Sum.inr k)))]'
          (ways_findIdx_lt _)).2 = false
        simp only [insertZeroWays_inr_val, hidx]
        rw [insertList_getElem w' hk false]
      apply Prod.ext
      · apply Subtype.ext
        show removeList (insertZeroWays w' (Sum.inr k)) = w'.1
        unfold removeList
        rw [insertZeroWays_inr_val, hidx]
        have htake : (insertList w'.1 (k.1 + 1) false).take (k.1 + 1) =
            (w'.1.map fun p : ℕ × Bool ↦ (p.1 + 1, p.2)).take (k.1 + 1) := by
          unfold insertList
          rw [List.take_append_of_le_length (by rw [List.length_take, List.length_map]; omega)]
          exact List.take_of_length_le (by rw [List.length_take, List.length_map]; omega)
        have hdrop : (insertList w'.1 (k.1 + 1) false).drop (k.1 + 1 + 1) =
            (w'.1.map fun p : ℕ × Bool ↦ (p.1 + 1, p.2)).drop (k.1 + 1) := by
          unfold insertList
          have h1 : (((w'.1.map fun p : ℕ × Bool ↦ (p.1 + 1, p.2)).take (k.1 + 1)) ++ [(0, false)]).length =
              k.1 + 1 + 1 := by
            rw [List.length_append, List.length_take, List.length_map]
            simp
            omega
          conv_lhs => rw [show (w'.1.map fun p : ℕ × Bool ↦ (p.1 + 1, p.2)).take (k.1 + 1) ++ (0, false) ::
              (w'.1.map fun p : ℕ × Bool ↦ (p.1 + 1, p.2)).drop (k.1 + 1) =
              ((w'.1.map fun p : ℕ × Bool ↦ (p.1 + 1, p.2)).take (k.1 + 1) ++ [(0, false)]) ++
              (w'.1.map fun p : ℕ × Bool ↦ (p.1 + 1, p.2)).drop (k.1 + 1) by
            rw [List.append_assoc, List.singleton_append]]
          rw [← h1, List.drop_left]
        rw [htake, hdrop, List.take_append_drop, map_down_map_up]
      · show removeZeroData (insertZeroWays w' (Sum.inr k)) = Sum.inr k
        have hnt : ¬ removePan (insertZeroWays w' (Sum.inr k)) = true := by rw [hpan]; decide
        unfold removeZeroData
        rw [dif_neg hnt]
        simp only [hidx]
        congr 1

lemma card_idata (n : ℕ) : Nat.card (IData n) = 2 * n + 1 := by
  show Nat.card (Fin (n + 1) ⊕ Fin n) = 2 * n + 1
  rw [Nat.card_sum, Nat.card_fin, Nat.card_fin]
  ring

lemma card_ways_zero : Nat.card (Ways 0) = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b ↦ Subtype.ext ?_⟩, ⟨⟨[], ?_, ?_⟩⟩⟩
  · have ha : a.1 = [] := by
      have h := a.2.1
      simp only [List.range_zero] at h
      exact List.map_eq_nil_iff.mp (List.perm_nil.mp h)
    have hb : b.1 = [] := by
      have h := b.2.1
      simp only [List.range_zero] at h
      exact List.map_eq_nil_iff.mp (List.perm_nil.mp h)
    rw [ha, hb]
  · exact List.Perm.refl []
  · intro pre hpre
    rw [List.prefix_nil] at hpre
    rw [hpre]
    exact le_rfl

lemma card_ways_succ (n : ℕ) :
    Nat.card (Ways (n + 1)) = (2 * n + 1) * Nat.card (Ways n) := by
  rw [Nat.card_congr (stepEquiv n), Nat.card_prod, card_idata]
  ring

lemma card_ways (n : ℕ) : Nat.card (Ways (n + 1)) = (2 * n + 1)‼ := by
  induction n with
  | zero => rw [card_ways_succ 0, card_ways_zero]; rfl
  | succ n ih =>
    rw [card_ways_succ (n + 1), ih]
    have h : 2 * (n + 1) + 1 = (2 * n + 1) + 2 := by ring
    rw [h, Nat.doubleFactorial_add_two]

snip end

determine solution_value : ℕ → ℕ := fun n ↦ (2 * n - 1)‼

problem imo2011_p4 (n : ℕ) (hn : 0 < n) :
    Nat.card (Ways n) = solution_value n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  show Nat.card (Ways (m + 1)) = (2 * (m + 1) - 1)‼
  have h : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  rw [h]
  exact card_ways m

end Imo2011P4
