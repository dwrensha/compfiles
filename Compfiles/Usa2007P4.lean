/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Int.Interval
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2007, Problem 4

An animal with n cells is a connected figure consisting of n equal-sized
square cells (equivalently, a polyomino with n cells). A dinosaur is an
animal with at least 2007 cells. It is said to be primitive if its cells
cannot be partitioned into two or more dinosaurs. Find with proof the
maximum number of cells in a primitive dinosaur.
-/

namespace Usa2007P4

/-- Two cells of the integer lattice are adjacent when they share an edge,
i.e. their Manhattan distance is `1`. -/
def gridAdj (a b : ℤ × ℤ) : Prop := (a.1 - b.1).natAbs + (a.2 - b.2).natAbs = 1

/-- The infinite grid graph on `ℤ × ℤ`: vertices are cells, edges join
edge-adjacent cells. -/
def gridGraph : SimpleGraph (ℤ × ℤ) where
  Adj := gridAdj
  symm := ⟨fun a b h => by
    have e1 : b.1 - a.1 = -(a.1 - b.1) := by ring
    have e2 : b.2 - a.2 = -(a.2 - b.2) := by ring
    show (b.1 - a.1).natAbs + (b.2 - a.2).natAbs = 1
    rw [e1, e2, Int.natAbs_neg, Int.natAbs_neg]
    exact h⟩
  loopless := ⟨fun a h => by simp [gridAdj] at h⟩

/-- An *animal* is a nonempty finite set of cells whose induced subgraph of
the grid graph is connected. -/
structure IsAnimal (s : Finset (ℤ × ℤ)) : Prop where
  nonempty : s.Nonempty
  preconnected : (gridGraph.induce (s : Set (ℤ × ℤ))).Preconnected

/-- A *dinosaur* is an animal with at least `2007` cells. -/
def IsDinosaur (s : Finset (ℤ × ℤ)) : Prop := IsAnimal s ∧ 2007 ≤ s.card

/-- `parts` is a partition of the animal `d` into two or more dinosaurs:
at least two pairwise disjoint dinosaurs whose union is `d`. -/
def IsDinoPartition (d : Finset (ℤ × ℤ)) (parts : Finset (Finset (ℤ × ℤ))) : Prop :=
  2 ≤ parts.card ∧
  (∀ p ∈ parts, IsDinosaur p) ∧
  (∀ p ∈ parts, ∀ q ∈ parts, p ≠ q → Disjoint p q) ∧
  parts.biUnion id = d

/-- A dinosaur is *primitive* if its cells cannot be partitioned into two or
more dinosaurs. -/
def IsPrimitive (d : Finset (ℤ × ℤ)) : Prop :=
  IsDinosaur d ∧ ¬ ∃ parts, IsDinoPartition d parts

snip begin

/-! ### Basic facts about the grid graph -/

lemma gridAdj_iff (a b : ℤ × ℤ) :
    gridAdj a b ↔ (a.1 - b.1).natAbs + (a.2 - b.2).natAbs = 1 := Iff.rfl

lemma gridAdj_of_gridAdj {a b : ℤ × ℤ} (h : gridAdj a b) : gridAdj b a :=
  gridGraph.adj_symm h

lemma ne_of_gridAdj {a b : ℤ × ℤ} (h : gridAdj a b) : a ≠ b := gridGraph.ne_of_adj h

/-- A cell adjacent to `a` is one of its four neighbours. -/
lemma gridAdj_cases {a b : ℤ × ℤ} (h : gridAdj a b) :
    (b.1 = a.1 + 1 ∧ b.2 = a.2) ∨ (b.1 = a.1 - 1 ∧ b.2 = a.2) ∨
    (b.1 = a.1 ∧ b.2 = a.2 + 1) ∨ (b.1 = a.1 ∧ b.2 = a.2 - 1) := by
  unfold gridAdj at h
  lia

/-- The explicit four-element finset of neighbours of a cell. -/
def neighbors4 (a : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  {(a.1 + 1, a.2), (a.1 - 1, a.2), (a.1, a.2 + 1), (a.1, a.2 - 1)}

lemma mem_neighbors4_of_gridAdj {a b : ℤ × ℤ} (h : gridAdj a b) : b ∈ neighbors4 a := by
  rcases gridAdj_cases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    simp [neighbors4, Prod.ext_iff, h1, h2]

lemma card_neighbors4_le (a : ℤ × ℤ) : (neighbors4 a).card ≤ 4 := by
  have h1 := Finset.card_insert_le (a.1 + 1, a.2)
    ({(a.1 - 1, a.2), (a.1, a.2 + 1), (a.1, a.2 - 1)} : Finset (ℤ × ℤ))
  have h2 := Finset.card_insert_le (a.1 - 1, a.2)
    ({(a.1, a.2 + 1), (a.1, a.2 - 1)} : Finset (ℤ × ℤ))
  have h3 := Finset.card_insert_le (a.1, a.2 + 1)
    ({(a.1, a.2 - 1)} : Finset (ℤ × ℤ))
  have h4 : ({(a.1, a.2 - 1)} : Finset (ℤ × ℤ)).card = 1 := Finset.card_singleton _
  unfold neighbors4
  lia

lemma card_erase_neighbors4_le {a x : ℤ × ℤ} (hx : x ∈ neighbors4 a) :
    ((neighbors4 a).erase x).card ≤ 3 := by
  rw [Finset.card_erase_of_mem hx]
  have h := card_neighbors4_le a
  lia

/-- If every cell of `T` reaches a fixed cell `v ∈ T` in the induced subgraph
on `T`, then that subgraph is preconnected. -/
lemma preconnected_of_forall_reachable (T : Finset (ℤ × ℤ)) {v : ℤ × ℤ} (hv : v ∈ T)
    (h : ∀ c : ℤ × ℤ, ∀ hc : c ∈ T,
      (gridGraph.induce (T : Set (ℤ × ℤ))).Reachable ⟨c, hc⟩ ⟨v, hv⟩) :
    (gridGraph.induce (T : Set (ℤ × ℤ))).Preconnected := by
  intro a b
  exact (h a a.2).trans (h b b.2).symm

/-! ### The depth function and parent map of an animal

Fix an animal `D` and a root cell `r ∈ D`. We measure the depth `dw c` of a
cell `c` as the length of a shortest walk from `r` to `c` in the induced
subgraph on `D`, and choose for every `c ≠ r` a *parent* cell adjacent to `c`
of strictly smaller depth. Following parents from any cell eventually reaches
`r`, so `D` is organized as a tree rooted at `r`. -/

section Tree

variable (D : Finset (ℤ × ℤ)) (r : ℤ × ℤ) (hr : r ∈ D)
  (hpre : (gridGraph.induce (D : Set (ℤ × ℤ))).Preconnected)

include hpre r hr

open Classical

lemma exists_walk_length (c : ℤ × ℤ) (hc : c ∈ D) :
    ∃ n : ℕ, ∃ w : (gridGraph.induce (D : Set (ℤ × ℤ))).Walk ⟨r, hr⟩ ⟨c, hc⟩,
      w.length = n := by
  obtain ⟨w⟩ := hpre ⟨r, hr⟩ ⟨c, hc⟩
  exact ⟨w.length, w, rfl⟩

/-- The depth of a cell: length of a shortest walk from the root `r` inside
`D` (defined to be `0` outside `D`). -/
noncomputable def dw (c : ℤ × ℤ) : ℕ :=
  if hc : c ∈ D then Nat.find (exists_walk_length D r hr hpre c hc) else 0

lemma dw_spec {c : ℤ × ℤ} (hc : c ∈ D) :
    ∃ w : (gridGraph.induce (D : Set (ℤ × ℤ))).Walk ⟨r, hr⟩ ⟨c, hc⟩,
      w.length = dw D r hr hpre c := by
  simp only [dw, dite_eq_left hc]
  exact Nat.find_spec (exists_walk_length D r hr hpre c hc)

lemma dw_le {c : ℤ × ℤ} (hc : c ∈ D)
    (w : (gridGraph.induce (D : Set (ℤ × ℤ))).Walk ⟨r, hr⟩ ⟨c, hc⟩) :
    dw D r hr hpre c ≤ w.length := by
  simp only [dw, dite_eq_left hc]
  exact Nat.find_le ⟨w, rfl⟩

lemma dw_root : dw D r hr hpre r = 0 := by
  simp only [dw, dite_eq_left hr]
  exact Nat.eq_zero_of_le_zero (Nat.find_le ⟨.nil, rfl⟩)

lemma eq_of_dw_eq_zero {c : ℤ × ℤ} (hc : c ∈ D) (h : dw D r hr hpre c = 0) :
    c = r := by
  simp only [dw, dite_eq_left hc] at h
  obtain ⟨w, hw⟩ := Nat.find_spec (exists_walk_length D r hr hpre c hc)
  rw [h] at hw
  have he := SimpleGraph.Walk.exists_length_eq_zero_iff.mp ⟨w, hw⟩
  exact (congrArg Subtype.val he).symm

/-- Any cell `c ≠ r` of `D` has a neighbour of strictly smaller depth:
the penultimate cell of a shortest walk from `r` to `c`. -/
lemma parent_exists {c : ℤ × ℤ} (hc : c ∈ D) (hcr : c ≠ r) :
    ∃ u ∈ D, gridAdj c u ∧ dw D r hr hpre u < dw D r hr hpre c := by
  obtain ⟨w, hw⟩ := dw_spec D r hr hpre hc
  have hpos : 0 < w.length := by
    rcases Nat.eq_zero_or_pos w.length with h0 | h0
    · exfalso
      have he := SimpleGraph.Walk.exists_length_eq_zero_iff.mp ⟨w, h0⟩
      exact hcr (congrArg Subtype.val he).symm
    · exact h0
  refine ⟨(w.getVert (w.length - 1) : ℤ × ℤ), (w.getVert (w.length - 1)).2, ?_, ?_⟩
  · have hadj := w.adj_getVert_succ (i := w.length - 1) (by lia)
    have h1 : w.length - 1 + 1 = w.length := by lia
    rw [h1, SimpleGraph.Walk.getVert_length] at hadj
    exact gridAdj_of_gridAdj (SimpleGraph.induce_adj.mp hadj)
  · have hlt := dw_le D r hr hpre (w.getVert (w.length - 1)).2 (w.take (w.length - 1))
    rw [SimpleGraph.Walk.take_length] at hlt
    rw [← hw]
    exact lt_of_le_of_lt (le_trans hlt (Nat.min_le_left _ _)) (by lia)

/-- The parent map: for `c ∈ D`, `c ≠ r` a chosen neighbour of `c` of smaller
depth; anything else is mapped to itself. -/
noncomputable def parent (c : ℤ × ℤ) : ℤ × ℤ :=
  if h : c ∈ D ∧ c ≠ r then (parent_exists D r hr hpre h.1 h.2).choose else c

lemma parent_mem {c : ℤ × ℤ} (hc : c ∈ D) : parent D r hr hpre c ∈ D := by
  simp only [parent]
  by_cases h : c ∈ D ∧ c ≠ r
  · rw [dite_eq_left h]
    exact (parent_exists D r hr hpre h.1 h.2).choose_spec.1
  · rw [dite_eq_right h]
    exact hc

lemma gridAdj_parent {c : ℤ × ℤ} (hc : c ∈ D) (hcr : c ≠ r) :
    gridAdj c (parent D r hr hpre c) := by
  simp only [parent]
  rw [dite_eq_left ⟨hc, hcr⟩]
  exact (parent_exists D r hr hpre hc hcr).choose_spec.2.1

lemma dw_parent_lt {c : ℤ × ℤ} (hc : c ∈ D) (hcr : c ≠ r) :
    dw D r hr hpre (parent D r hr hpre c) < dw D r hr hpre c := by
  simp only [parent]
  rw [dite_eq_left ⟨hc, hcr⟩]
  exact (parent_exists D r hr hpre hc hcr).choose_spec.2.2

lemma parent_root : parent D r hr hpre r = r := by
  simp only [parent]
  rw [dite_eq_right (fun h => h.2 rfl)]

lemma parent_ne_self {c : ℤ × ℤ} (hc : c ∈ D) (hcr : c ≠ r) :
    parent D r hr hpre c ≠ c :=
  (ne_of_gridAdj (gridAdj_parent D r hr hpre hc hcr)).symm

lemma iterate_parent_mem {c : ℤ × ℤ} (hc : c ∈ D) (i : ℕ) :
    (parent D r hr hpre)^[i] c ∈ D := by
  induction i generalizing c with
  | zero => exact hc
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact parent_mem D r hr hpre (ih hc)

lemma iterate_parent_root (i : ℕ) : (parent D r hr hpre)^[i] r = r := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply', ih, parent_root]

lemma dw_iterate_parent_lt {c : ℤ × ℤ} (hc : c ∈ D) (hcr : c ≠ r) {i : ℕ}
    (hi : 1 ≤ i) :
    dw D r hr hpre ((parent D r hr hpre)^[i] c) < dw D r hr hpre c := by
  induction i generalizing c with
  | zero => exact absurd hi (by lia)
  | succ i ih =>
    by_cases hi0 : i = 0
    · subst hi0
      exact dw_parent_lt D r hr hpre hc hcr
    · have hi1 : 1 ≤ i := by lia
      rw [Function.iterate_succ_apply']
      by_cases hcr2 : (parent D r hr hpre)^[i] c = r
      · rw [hcr2, parent_root, dw_root]
        have hne : dw D r hr hpre c ≠ 0 :=
          fun h => hcr (eq_of_dw_eq_zero D r hr hpre hc h)
        lia
      · have hmem : (parent D r hr hpre)^[i] c ∈ D := iterate_parent_mem D r hr hpre hc i
        exact lt_trans (dw_parent_lt D r hr hpre hmem hcr2) (ih hc hcr hi1)

/-- Following parents from any cell of `D` eventually reaches the root. -/
lemma exists_iterate_parent_eq_root {c : ℤ × ℤ} (hc : c ∈ D) :
    ∃ i, (parent D r hr hpre)^[i] c = r := by
  have key : ∀ n : ℕ, ∀ c : ℤ × ℤ, c ∈ D → dw D r hr hpre c ≤ n →
      ∃ i, (parent D r hr hpre)^[i] c = r := by
    intro n
    induction n with
    | zero =>
      intro c hc hdw
      have h0 : dw D r hr hpre c = 0 := by lia
      exact ⟨0, eq_of_dw_eq_zero D r hr hpre hc h0⟩
    | succ n ih =>
      intro c hc hdw
      by_cases hle : dw D r hr hpre c ≤ n
      · exact ih c hc hle
      · have hcr : c ≠ r := by
          intro hceq
          subst hceq
          rw [dw_root] at hle
          exact hle (Nat.zero_le _)
        obtain ⟨i, hi⟩ := ih (parent D r hr hpre c) (parent_mem D r hr hpre hc) (by
          have hlt := dw_parent_lt D r hr hpre hc hcr
          lia)
        exact ⟨i + 1, by rw [Function.iterate_succ_apply]; exact hi⟩
  exact key (dw D r hr hpre c) c hc (le_refl _)

/-- The subtree rooted at `v`: all cells of `D` whose parent chain hits `v`. -/
noncomputable def subtree (v : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  D.filter (fun c => ∃ i, (parent D r hr hpre)^[i] c = v)

lemma mem_subtree {v c : ℤ × ℤ} :
    c ∈ subtree D r hr hpre v ↔ c ∈ D ∧ ∃ i, (parent D r hr hpre)^[i] c = v :=
  Finset.mem_filter

lemma mem_subtree_self {v : ℤ × ℤ} (hv : v ∈ D) : v ∈ subtree D r hr hpre v := by
  rw [mem_subtree]
  exact ⟨hv, 0, rfl⟩

lemma iterate_parent_mem_subtree_of_le {v c : ℤ × ℤ} (hc : c ∈ subtree D r hr hpre v)
    {i : ℕ} (hi : (parent D r hr hpre)^[i] c = v) {j : ℕ} (hj : j ≤ i) :
    (parent D r hr hpre)^[j] c ∈ subtree D r hr hpre v := by
  rw [mem_subtree] at hc
  rw [mem_subtree]
  refine ⟨iterate_parent_mem D r hr hpre hc.1 j, i - j, ?_⟩
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel hj]
  exact hi

lemma not_mem_subtree_iterate {v c : ℤ × ℤ} (hcD : c ∈ D)
    (hc : c ∉ subtree D r hr hpre v) (j : ℕ) :
    (parent D r hr hpre)^[j] c ∉ subtree D r hr hpre v := by
  intro h
  rw [mem_subtree] at h
  obtain ⟨_, m, hm⟩ := h
  apply hc
  rw [mem_subtree]
  exact ⟨hcD, m + j, by rw [Function.iterate_add_apply]; exact hm⟩

lemma subtree_root : subtree D r hr hpre r = D := by
  ext c
  rw [mem_subtree]
  constructor
  · exact And.left
  · intro hc
    exact ⟨hc, exists_iterate_parent_eq_root D r hr hpre hc⟩

/-- The children of `v`: cells of `D` whose parent is `v`. -/
noncomputable def children (v : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  D.filter (fun c => parent D r hr hpre c = v ∧ c ≠ v)

lemma mem_children {v c : ℤ × ℤ} :
    c ∈ children D r hr hpre v ↔ c ∈ D ∧ parent D r hr hpre c = v ∧ c ≠ v :=
  Finset.mem_filter

lemma children_ne_root {v c : ℤ × ℤ} (h : c ∈ children D r hr hpre v) : c ≠ r := by
  rw [mem_children] at h
  intro hcr
  subst hcr
  rw [parent_root] at h
  exact h.2.2 h.2.1

lemma dw_child {v c : ℤ × ℤ} (h : c ∈ children D r hr hpre v) :
    dw D r hr hpre v < dw D r hr hpre c := by
  have hcr := children_ne_root D r hr hpre h
  have h2 := dw_parent_lt D r hr hpre ((mem_children D r hr hpre).mp h).1 hcr
  rwa [((mem_children D r hr hpre).mp h).2.1] at h2

lemma children_subset_neighbors {v c : ℤ × ℤ} (h : c ∈ children D r hr hpre v) :
    c ∈ neighbors4 v := by
  have hcr := children_ne_root D r hr hpre h
  have hadj := gridAdj_parent D r hr hpre ((mem_children D r hr hpre).mp h).1 hcr
  rw [((mem_children D r hr hpre).mp h).2.1] at hadj
  exact mem_neighbors4_of_gridAdj (gridAdj_of_gridAdj hadj)

lemma child_ne_parent {v c : ℤ × ℤ} (hv : v ∈ D) (hvr : v ≠ r)
    (h : c ∈ children D r hr hpre v) : c ≠ parent D r hr hpre v := by
  obtain ⟨hcD, hpc, -⟩ := (mem_children D r hr hpre).mp h
  intro hcp
  have h1 : dw D r hr hpre v < dw D r hr hpre c := dw_child D r hr hpre h
  have h3 : dw D r hr hpre (parent D r hr hpre v) < dw D r hr hpre v :=
    dw_parent_lt D r hr hpre hv hvr
  rw [hcp] at h1
  exact absurd (lt_trans h3 h1) (lt_irrefl _)

lemma card_children_le_three {v : ℤ × ℤ} (hv : v ∈ D) (hvr : v ≠ r) :
    (children D r hr hpre v).card ≤ 3 := by
  have hsub : children D r hr hpre v ⊆ (neighbors4 v).erase (parent D r hr hpre v) := by
    intro c hc
    rw [Finset.mem_erase]
    exact ⟨child_ne_parent D r hr hpre hv hvr hc,
      children_subset_neighbors D r hr hpre hc⟩
  exact le_trans (Finset.card_le_card hsub) (card_erase_neighbors4_le
    (mem_neighbors4_of_gridAdj (gridAdj_parent D r hr hpre hv hvr)))

lemma card_children_le_four {v : ℤ × ℤ} : (children D r hr hpre v).card ≤ 4 :=
  le_trans (Finset.card_le_card (fun _ hc => children_subset_neighbors D r hr hpre hc))
    (card_neighbors4_le v)

/-- The subtree of `v` decomposes as `v` together with the subtrees of its
children. -/
lemma subtree_eq {v : ℤ × ℤ} (hv : v ∈ D) :
    subtree D r hr hpre v =
      insert v ((children D r hr hpre v).biUnion (subtree D r hr hpre)) := by
  ext c
  simp only [mem_subtree, Finset.mem_insert, Finset.mem_biUnion, mem_children]
  constructor
  · rintro ⟨hcD, i, hi⟩
    by_cases hcv : c = v
    · exact Or.inl hcv
    · right
      have hP : ∃ i, (parent D r hr hpre)^[i] c = v := ⟨i, hi⟩
      have hmin : (parent D r hr hpre)^[Nat.find hP] c = v := Nat.find_spec hP
      have hne0 : Nat.find hP ≠ 0 := by
        intro h0
        rw [h0, Function.iterate_zero_apply] at hmin
        exact hcv hmin
      obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hne0
      rw [hj, Function.iterate_succ_apply'] at hmin
      refine ⟨(parent D r hr hpre)^[j] c,
        ⟨iterate_parent_mem D r hr hpre hcD j, hmin, ?_⟩, hcD, j, rfl⟩
      intro hjv
      have hle := Nat.find_min' hP hjv
      lia
  · rintro (rfl | ⟨u, ⟨huD, hpu, -⟩, hcD, j, hj⟩)
    · exact ⟨hv, 0, rfl⟩
    · exact ⟨hcD, j + 1, by rw [Function.iterate_succ_apply', hj, hpu]⟩

/-- The subtrees of distinct children of `v` are disjoint. -/
lemma disjoint_subtree_children {v : ℤ × ℤ} (hv : v ∈ D) :
    ((children D r hr hpre v) : Set (ℤ × ℤ)).PairwiseDisjoint (subtree D r hr hpre) := by
  intro u₁ hu₁ u₂ hu₂ hne
  show Disjoint (subtree D r hr hpre u₁) (subtree D r hr hpre u₂)
  rw [Finset.disjoint_left]
  rintro c hc1 hc2
  obtain ⟨hcD, i₁, hi₁⟩ := (mem_subtree D r hr hpre).mp hc1
  obtain ⟨_, i₂, hi₂⟩ := (mem_subtree D r hr hpre).mp hc2
  have key : ∀ {u₁ u₂ : ℤ × ℤ}, u₁ ∈ children D r hr hpre v →
      u₂ ∈ children D r hr hpre v → ∀ {i₁ i₂ : ℕ},
      (parent D r hr hpre)^[i₁] c = u₁ → (parent D r hr hpre)^[i₂] c = u₂ →
      i₁ < i₂ → False := by
    intro u₁ u₂ hu₁ hu₂ i₁ i₂ hi₁ hi₂ hlt
    have h2 : (parent D r hr hpre)^[i₂ - i₁] u₁ = u₂ := by
      have h : (parent D r hr hpre)^[i₂ - i₁] ((parent D r hr hpre)^[i₁] c) =
          (parent D r hr hpre)^[i₂] c := by
        rw [← Function.iterate_add_apply, Nat.sub_add_cancel (Nat.le_of_lt hlt)]
      rw [hi₁] at h
      exact h.trans hi₂
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (n := i₂ - i₁) (by lia)
    rw [hj, Function.iterate_succ_apply] at h2
    obtain ⟨hu₁D, hpu₁, -⟩ := (mem_children D r hr hpre).mp hu₁
    rw [hpu₁] at h2
    obtain ⟨hu₂D, -, hu₂ne⟩ := (mem_children D r hr hpre).mp hu₂
    by_cases hvr : v = r
    · subst hvr
      rw [iterate_parent_root] at h2
      exact hu₂ne h2.symm
    · by_cases hj0 : j = 0
      · subst hj0
        exact hu₂ne h2.symm
      · have hdw : dw D r hr hpre u₂ < dw D r hr hpre v := by
          rw [← h2]
          exact dw_iterate_parent_lt D r hr hpre hv hvr (by lia)
        have hdw2 := dw_child D r hr hpre hu₂
        lia
  rcases lt_trichotomy i₁ i₂ with h | h | h
  · exact key hu₁ hu₂ hi₁ hi₂ h
  · exact hne ((h ▸ hi₁).symm.trans hi₂)
  · exact key hu₂ hu₁ hi₂ hi₁ h

/-- The size of a subtree is one more than the sum of the sizes of the
subtrees of its children. -/
lemma card_subtree {v : ℤ × ℤ} (hv : v ∈ D) :
    (subtree D r hr hpre v).card =
      1 + ∑ u ∈ children D r hr hpre v, (subtree D r hr hpre u).card := by
  have hnot : v ∉ (children D r hr hpre v).biUnion (subtree D r hr hpre) := by
    intro hmem
    rw [Finset.mem_biUnion] at hmem
    obtain ⟨u, hu, hvu⟩ := hmem
    obtain ⟨_, j, hj⟩ := (mem_subtree D r hr hpre).mp hvu
    obtain ⟨huD, hpu, hune⟩ := (mem_children D r hr hpre).mp hu
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · subst hj0
      exact hune hj.symm
    · by_cases hvr : v = r
      · subst hvr
        rw [iterate_parent_root] at hj
        exact hune hj.symm
      · have hdw : dw D r hr hpre u < dw D r hr hpre v := by
          rw [← hj]
          exact dw_iterate_parent_lt D r hr hpre hv hvr hj0
        have hdw2 := dw_child D r hr hpre hu
        lia
  rw [subtree_eq D r hr hpre hv, Finset.card_insert_of_notMem hnot,
    Finset.card_biUnion (disjoint_subtree_children D r hr hpre hv)]
  lia

/-- If the parent chain from `c` stays inside `T` and reaches `v`, then `c`
reaches `v` in the induced subgraph on `T`. -/
lemma reachable_of_chain (T : Finset (ℤ × ℤ)) (hTD : T ⊆ D) {c v : ℤ × ℤ}
    (hc : c ∈ T) (hv : v ∈ T) (i : ℕ)
    (hchain : ∀ j ≤ i, (parent D r hr hpre)^[j] c ∈ T)
    (hiv : (parent D r hr hpre)^[i] c = v) :
    (gridGraph.induce (T : Set (ℤ × ℤ))).Reachable ⟨c, hc⟩ ⟨v, hv⟩ := by
  induction i generalizing c with
  | zero =>
    simp only [Function.iterate_zero_apply] at hiv
    subst hiv
    exact SimpleGraph.Reachable.refl _
  | succ i ih =>
    by_cases hcv : c = v
    · subst hcv
      exact SimpleGraph.Reachable.refl _
    · have hcr : c ≠ r := by
        intro hceq
        subst hceq
        rw [iterate_parent_root] at hiv
        exact hcv hiv
      have hcD : c ∈ D := hTD hc
      have hpc : parent D r hr hpre c ∈ T := hchain 1 (by lia)
      have hadj : gridAdj c (parent D r hr hpre c) := gridAdj_parent D r hr hpre hcD hcr
      have hchain' : ∀ j ≤ i, (parent D r hr hpre)^[j] (parent D r hr hpre c) ∈ T := by
        intro j hj
        have h := hchain (j + 1) (by lia)
        rwa [Function.iterate_succ_apply] at h
      have hiv' : (parent D r hr hpre)^[i] (parent D r hr hpre c) = v := by
        rwa [Function.iterate_succ_apply] at hiv
      have hreach := ih hpc hchain' hiv'
      have hadjT : (gridGraph.induce (T : Set (ℤ × ℤ))).Adj
          ⟨c, hc⟩ ⟨parent D r hr hpre c, hpc⟩ :=
        SimpleGraph.induce_adj.mpr hadj
      exact Nonempty.map (SimpleGraph.Walk.cons hadjT) hreach

/-- The subtree rooted at any cell of `D` is an animal. -/
lemma isAnimal_subtree {v : ℤ × ℤ} (hv : v ∈ D) : IsAnimal (subtree D r hr hpre v) := by
  refine ⟨⟨v, mem_subtree_self D r hr hpre hv⟩,
    preconnected_of_forall_reachable (subtree D r hr hpre v)
      (mem_subtree_self D r hr hpre hv) ?_⟩
  intro c hc
  obtain ⟨hcD, i, hi⟩ := (mem_subtree D r hr hpre).mp hc
  exact reachable_of_chain D r hr hpre (subtree D r hr hpre v) (Finset.filter_subset _ _) hc
    (mem_subtree_self D r hr hpre hv) i
    (fun j hj => iterate_parent_mem_subtree_of_le D r hr hpre hc hi hj) hi

/-- Removing a rooted subtree (with `v ≠ r`) from `D` leaves an animal. -/
lemma isAnimal_sdiff_subtree {v : ℤ × ℤ} (_hv : v ∈ D) (hvr : v ≠ r) :
    IsAnimal (D \ subtree D r hr hpre v) := by
  have hrmem : r ∈ D \ subtree D r hr hpre v := by
    rw [Finset.mem_sdiff]
    refine ⟨hr, ?_⟩
    intro hcon
    obtain ⟨_, i, hi⟩ := (mem_subtree D r hr hpre).mp hcon
    rw [iterate_parent_root] at hi
    exact hvr hi.symm
  refine ⟨⟨r, hrmem⟩, preconnected_of_forall_reachable (D \ subtree D r hr hpre v)
    hrmem ?_⟩
  intro c hc
  obtain ⟨i, hi⟩ := exists_iterate_parent_eq_root D r hr hpre (Finset.mem_sdiff.mp hc).1
  exact reachable_of_chain D r hr hpre (D \ subtree D r hr hpre v) Finset.sdiff_subset hc
    hrmem i (fun j hj => by
      rw [Finset.mem_sdiff]
      exact ⟨iterate_parent_mem D r hr hpre (Finset.mem_sdiff.mp hc).1 j,
        not_mem_subtree_iterate D r hr hpre (Finset.mem_sdiff.mp hc).1
          (Finset.mem_sdiff.mp hc).2 j⟩) hi

/-- **Splitting lemma.** Any animal with at least `4 * 2007 - 2` cells can be
partitioned into two dinosaurs; in particular it is not primitive. -/
lemma exists_split (hcard : 4 * 2007 - 2 ≤ D.card) :
    ∃ A B : Finset (ℤ × ℤ), IsDinosaur A ∧ IsDinosaur B ∧ Disjoint A B ∧ A ∪ B = D := by
  set S := D.filter (fun v => 2007 ≤ (subtree D r hr hpre v).card) with hS
  have hrS : r ∈ S := by
    rw [hS, Finset.mem_filter]
    refine ⟨hr, ?_⟩
    rw [subtree_root]
    lia
  obtain ⟨v, hvS, hmax⟩ := Finset.exists_max_image S (fun c => dw D r hr hpre c) ⟨r, hrS⟩
  rw [hS, Finset.mem_filter] at hvS
  obtain ⟨hvD, hkv⟩ := hvS
  have hchild : ∀ u ∈ children D r hr hpre v, (subtree D r hr hpre u).card ≤ 2006 := by
    intro u hu
    by_contra hcon
    have hcon : 2006 < (subtree D r hr hpre u).card := Nat.lt_of_not_le hcon
    have huS : u ∈ S := by
      rw [hS, Finset.mem_filter]
      exact ⟨((mem_children D r hr hpre).mp hu).1, by lia⟩
    have hle := hmax u huS
    have hlt := dw_child D r hr hpre hu
    lia
  have hcardv := card_subtree D r hr hpre hvD
  by_cases hvr : v = r
  · subst v
    have h4 : (children D r hr hpre r).card ≤ 4 := card_children_le_four D r hr hpre
    have hsum : ∑ u ∈ children D r hr hpre r, (subtree D r hr hpre u).card ≤ 4 * 2006 := by
      have h := Finset.sum_le_card_nsmul (children D r hr hpre r)
        (fun u => (subtree D r hr hpre u).card) 2006 hchild
      rw [nsmul_eq_mul] at h
      exact le_trans h (Nat.mul_le_mul h4 (le_refl 2006))
    rw [subtree_root] at hcardv
    exfalso
    lia
  · have h3 := card_children_le_three D r hr hpre hvD hvr
    have hsum : ∑ u ∈ children D r hr hpre v, (subtree D r hr hpre u).card ≤ 3 * 2006 := by
      have h := Finset.sum_le_card_nsmul (children D r hr hpre v)
        (fun u => (subtree D r hr hpre u).card) 2006 hchild
      rw [nsmul_eq_mul] at h
      exact le_trans h (Nat.mul_le_mul h3 (le_refl 2006))
    have hAv : (subtree D r hr hpre v).card ≤ 6019 := by lia
    have hsub : subtree D r hr hpre v ⊆ D := Finset.filter_subset _ _
    refine ⟨subtree D r hr hpre v, D \ subtree D r hr hpre v,
      ⟨isAnimal_subtree D r hr hpre hvD, hkv⟩,
      ⟨isAnimal_sdiff_subtree D r hr hpre hvD hvr, ?_⟩, ?_, ?_⟩
    · rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]
      lia
    · exact Finset.disjoint_sdiff
    · exact Finset.union_sdiff_of_subset hsub

end Tree

/-! ### The cross construction (lower bound) -/

/-- The body of `cross`, kept reducible so that membership and cardinality can
be unfolded in the auxiliary lemmas `mem_aux` and `card_aux`. (In this
environment, `Finset.Icc` on `ℤ` records a `Preorder ℤ` instance whose term
contains the noncomputable `Int.instConditionallyCompleteLinearOrder`, hence
the `noncomputable` keyword.) -/
noncomputable def crossAux : Finset (ℤ × ℤ) :=
  (Finset.Icc (-2006) 2006).product {(0 : ℤ)} ∪
    Finset.product {(0 : ℤ)} (Finset.Icc (-2006) 2006)

/-- The cross with center `(0,0)` and four arms of length `2006`.

Marked `irreducible`: the `Preorder ℤ` instance recorded in the `Finset.Icc`
terms of the body is a very large term, and any definitional unfolding of
`cross` (as happens when checking `x ∈ cross` against `x ∈ ↑cross` for the
coercion to `Set`, e.g. when building elements of `↥(↑cross)`) exceeds the
elaborator's recursion depth limit. Unfold instead via `cross_def`, `mem_aux`
and `card_aux` where needed. -/
@[irreducible]
noncomputable def cross : Finset (ℤ × ℤ) := crossAux

/-- Unfolding lemma for `cross`. Do not use `simp only [cross]` or
`cross.eq_unfold`: re-elaborating the auto-generated equation lemma hits the
recursion depth limit. -/
lemma cross_def : cross = crossAux := by
  with_unfolding_all rfl

/-- Coordinate characterization of membership in `crossAux`. -/
lemma mem_aux {c : ℤ × ℤ} :
    c ∈ crossAux ↔ (c.2 = 0 ∧ -2006 ≤ c.1 ∧ c.1 ≤ 2006) ∨
      (c.1 = 0 ∧ -2006 ≤ c.2 ∧ c.2 ≤ 2006) := by
  simp only [crossAux, Finset.product_eq_sprod, Finset.mem_union, Finset.mem_product,
    Finset.mem_Icc, Finset.mem_singleton]
  constructor
  · rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨h4, h5, h6⟩)
    · exact Or.inl ⟨h3, h1, h2⟩
    · exact Or.inr ⟨h4, h5, h6⟩
  · rintro (⟨h3, h1, h2⟩ | ⟨h4, h5, h6⟩)
    · exact Or.inl ⟨⟨h1, h2⟩, h3⟩
    · exact Or.inr ⟨h4, h5, h6⟩

/-- Coordinate characterization of membership in `cross`. -/
lemma mem_cross_iff {c : ℤ × ℤ} :
    c ∈ cross ↔ (c.2 = 0 ∧ -2006 ≤ c.1 ∧ c.1 ≤ 2006) ∨
      (c.1 = 0 ∧ -2006 ≤ c.2 ∧ c.2 ≤ 2006) := by
  rw [cross_def]
  exact mem_aux

lemma mem_center_cross : ((0, 0) : ℤ × ℤ) ∈ cross := by
  rw [mem_cross_iff]
  exact Or.inl ⟨rfl, by decide, by decide⟩

/-- The four arm points at distance `n` from the center lie in `cross`
when `n ≤ 2006`. -/
lemma mem_cross_of_nat {n : ℕ} (hn : n ≤ 2006) :
    (((n : ℤ), 0) ∈ cross) ∧ ((-((n : ℤ)), 0) ∈ cross) ∧
      (((0 : ℤ), (n : ℤ)) ∈ cross) ∧ (((0 : ℤ), -((n : ℤ))) ∈ cross) := by
  have h0 : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
  have hn' : (n : ℤ) ≤ 2006 := by exact_mod_cast hn
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [mem_cross_iff] <;> dsimp only <;> lia

lemma card_aux : crossAux.card = 8025 := by
  have cardprod : ∀ (s t : Finset ℤ), (Finset.product s t).card = s.card * t.card :=
    fun s t => Finset.card_product s t
  have hA : ((Finset.Icc (-2006) 2006).product {(0 : ℤ)}).card = 4013 := by
    rw [cardprod, Int.card_Icc, Finset.card_singleton]
    decide
  have hB : (Finset.product {(0 : ℤ)} (Finset.Icc (-2006) 2006)).card = 4013 := by
    rw [cardprod, Int.card_Icc, Finset.card_singleton]
    decide
  have hinter : (Finset.Icc (-2006) 2006).product {(0 : ℤ)} ∩
      (Finset.product {(0 : ℤ)} (Finset.Icc (-2006) 2006)) = {((0, 0) : ℤ × ℤ)} := by
    ext ⟨x, y⟩
    simp only [Finset.mem_inter, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc,
      Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨_, _⟩, h3⟩, ⟨h4, _, _⟩⟩
      exact ⟨h4, h3⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨⟨⟨by decide, by decide⟩, rfl⟩, ⟨rfl, by decide, by decide⟩⟩
  have hu := Finset.card_union_add_card_inter ((Finset.Icc (-2006) 2006).product {(0 : ℤ)})
    (Finset.product {(0 : ℤ)} (Finset.Icc (-2006) 2006))
  rw [hinter, Finset.card_singleton, hA, hB] at hu
  have hcross : crossAux = (Finset.Icc (-2006) 2006).product {(0 : ℤ)} ∪
      Finset.product {(0 : ℤ)} (Finset.Icc (-2006) 2006) := rfl
  rw [hcross]
  lia

lemma card_cross : cross.card = 8025 := by
  rw [cross_def]
  exact card_aux

/-- Walking down the positive x-arm: `((n,0))` reaches the center. -/
lemma reach_right :
    ∀ n : ℕ, n ≤ 2006 → ∀ h : (((n : ℤ), 0) ∈ cross),
      (gridGraph.induce (cross : Set (ℤ × ℤ))).Reachable ⟨((n : ℤ), 0), h⟩
        ⟨(0, 0), mem_center_cross⟩ := by
  intro n
  induction n with
  | zero =>
    intro _ h
    exact SimpleGraph.Reachable.refl _
  | succ n ih =>
    intro hn h
    have hn' : n ≤ 2006 := by lia
    have hmem : ((n : ℤ), 0) ∈ cross := (mem_cross_of_nat hn').1
    have hadj : gridAdj (((n + 1 : ℕ) : ℤ), 0) ((n : ℤ), 0) := by
      unfold gridAdj
      dsimp only
      rw [Nat.cast_add, Nat.cast_one]
      have e : ((n : ℤ) + 1) - (n : ℤ) = 1 := by ring
      rw [e]
      decide
    have hadj2 : (gridGraph.induce (cross : Set (ℤ × ℤ))).Adj
        ⟨(((n + 1 : ℕ) : ℤ), 0), h⟩ ⟨((n : ℤ), 0), hmem⟩ := hadj
    exact ⟨SimpleGraph.Walk.cons hadj2 (ih hn' hmem).some⟩

/-- Walking down the negative x-arm: `((-n,0))` reaches the center. -/
lemma reach_left :
    ∀ n : ℕ, n ≤ 2006 → ∀ h : ((-((n : ℤ)), 0) ∈ cross),
      (gridGraph.induce (cross : Set (ℤ × ℤ))).Reachable ⟨(-((n : ℤ)), 0), h⟩
        ⟨(0, 0), mem_center_cross⟩ := by
  intro n
  induction n with
  | zero =>
    intro _ h
    exact SimpleGraph.Reachable.refl _
  | succ n ih =>
    intro hn h
    have hn' : n ≤ 2006 := by lia
    have hmem : (-((n : ℤ)), 0) ∈ cross := (mem_cross_of_nat hn').2.1
    have hadj : gridAdj ((-(((n + 1 : ℕ)) : ℤ)), 0) (-((n : ℤ)), 0) := by
      unfold gridAdj
      dsimp only
      rw [Nat.cast_add, Nat.cast_one]
      have e : (-(((n : ℤ)) + 1)) - (-((n : ℤ))) = -1 := by ring
      rw [e]
      decide
    have hadj2 : (gridGraph.induce (cross : Set (ℤ × ℤ))).Adj
        ⟨(-(((n + 1 : ℕ)) : ℤ), 0), h⟩ ⟨(-((n : ℤ)), 0), hmem⟩ := hadj
    exact ⟨SimpleGraph.Walk.cons hadj2 (ih hn' hmem).some⟩

/-- Walking down the positive y-arm: `((0,n))` reaches the center. -/
lemma reach_up :
    ∀ n : ℕ, n ≤ 2006 → ∀ h : (((0 : ℤ), (n : ℤ)) ∈ cross),
      (gridGraph.induce (cross : Set (ℤ × ℤ))).Reachable ⟨((0 : ℤ), (n : ℤ)), h⟩
        ⟨(0, 0), mem_center_cross⟩ := by
  intro n
  induction n with
  | zero =>
    intro _ h
    exact SimpleGraph.Reachable.refl _
  | succ n ih =>
    intro hn h
    have hn' : n ≤ 2006 := by lia
    have hmem : ((0 : ℤ), (n : ℤ)) ∈ cross := (mem_cross_of_nat hn').2.2.1
    have hadj : gridAdj ((0 : ℤ), (((n + 1 : ℕ)) : ℤ)) ((0 : ℤ), (n : ℤ)) := by
      unfold gridAdj
      dsimp only
      rw [Nat.cast_add, Nat.cast_one]
      have e : ((n : ℤ) + 1) - (n : ℤ) = 1 := by ring
      rw [e]
      decide
    have hadj2 : (gridGraph.induce (cross : Set (ℤ × ℤ))).Adj
        ⟨((0 : ℤ), (((n + 1 : ℕ)) : ℤ)), h⟩ ⟨((0 : ℤ), (n : ℤ)), hmem⟩ := hadj
    exact ⟨SimpleGraph.Walk.cons hadj2 (ih hn' hmem).some⟩

/-- Walking down the negative y-arm: `((0,-n))` reaches the center. -/
lemma reach_down :
    ∀ n : ℕ, n ≤ 2006 → ∀ h : (((0 : ℤ), -((n : ℤ))) ∈ cross),
      (gridGraph.induce (cross : Set (ℤ × ℤ))).Reachable ⟨((0 : ℤ), -((n : ℤ))), h⟩
        ⟨(0, 0), mem_center_cross⟩ := by
  intro n
  induction n with
  | zero =>
    intro _ h
    exact SimpleGraph.Reachable.refl _
  | succ n ih =>
    intro hn h
    have hn' : n ≤ 2006 := by lia
    have hmem : ((0 : ℤ), -((n : ℤ))) ∈ cross := (mem_cross_of_nat hn').2.2.2
    have hadj : gridAdj ((0 : ℤ), -(((n + 1 : ℕ)) : ℤ)) ((0 : ℤ), -((n : ℤ))) := by
      unfold gridAdj
      dsimp only
      rw [Nat.cast_add, Nat.cast_one]
      have e : (-(((n : ℤ)) + 1)) - (-((n : ℤ))) = -1 := by ring
      rw [e]
      decide
    have hadj2 : (gridGraph.induce (cross : Set (ℤ × ℤ))).Adj
        ⟨((0 : ℤ), -(((n + 1 : ℕ)) : ℤ)), h⟩ ⟨((0 : ℤ), -((n : ℤ))), hmem⟩ := hadj
    exact ⟨SimpleGraph.Walk.cons hadj2 (ih hn' hmem).some⟩

lemma isAnimal_cross : IsAnimal cross := by
  refine ⟨⟨(0, 0), mem_center_cross⟩, ?_⟩
  intro u v
  have key : ∀ c : (cross : Set (ℤ × ℤ)),
      (gridGraph.induce (cross : Set (ℤ × ℤ))).Reachable c ⟨(0, 0), mem_center_cross⟩ := by
    rintro ⟨⟨x, y⟩, hc⟩
    have hc' := mem_cross_iff.mp hc
    dsimp only at hc'
    rcases hc' with ⟨hy, hxl, hxu⟩ | ⟨hx, hyl, hyu⟩
    · subst hy
      rcases Int.natAbs_eq x with heq | heq
      · generalize hn : Int.natAbs x = n
        rw [hn] at heq
        subst heq
        have hnle : n ≤ 2006 := by lia
        exact reach_right n hnle hc
      · generalize hn : Int.natAbs x = n
        rw [hn] at heq
        subst heq
        have hnle : n ≤ 2006 := by lia
        exact reach_left n hnle hc
    · subst hx
      rcases Int.natAbs_eq y with heq | heq
      · generalize hn : Int.natAbs y = n
        rw [hn] at heq
        subst heq
        have hnle : n ≤ 2006 := by lia
        exact reach_up n hnle hc
      · generalize hn : Int.natAbs y = n
        rw [hn] at heq
        subst heq
        have hnle : n ≤ 2006 := by lia
        exact reach_down n hnle hc
  exact (key u).trans (key v).symm

/-- `b` lies in the same arm of the cross as `a` (meaningful when `a` is not
the center). -/
def InSameArm (a b : ℤ × ℤ) : Prop :=
  (0 < a.2 → b.1 = 0 ∧ 0 < b.2) ∧ (a.2 < 0 → b.1 = 0 ∧ b.2 < 0) ∧
    (0 < a.1 → b.2 = 0 ∧ 0 < b.1) ∧ (a.1 < 0 → b.2 = 0 ∧ b.1 < 0)

lemma inSameArm_refl {a : ℤ × ℤ} (ha : a ∈ cross) : InSameArm a a := by
  have ha' := mem_cross_iff.mp ha
  rcases ha' with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
    exact ⟨fun hx => by lia, fun hx => by lia, fun hx => by lia, fun hx => by lia⟩

lemma inSameArm_trans {a b c : ℤ × ℤ} (hab : InSameArm a b) (hbc : InSameArm b c) :
    InSameArm a c := by
  obtain ⟨h1, h2, h3, h4⟩ := hab
  obtain ⟨g1, g2, g3, g4⟩ := hbc
  exact ⟨fun h => g1 (h1 h).2, fun h => g2 (h2 h).2, fun h => g3 (h3 h).2,
    fun h => g4 (h4 h).2⟩

/-- A step along the cross between two cells, the target not being the center,
stays in the same arm. -/
lemma inSameArm_of_gridAdj {a b : ℤ × ℤ} (ha : a ∈ cross) (hb : b ∈ cross)
    (hb0 : b ≠ (0, 0)) (h : gridAdj a b) : InSameArm a b := by
  have ha' := mem_cross_iff.mp ha
  have hb' := mem_cross_iff.mp hb
  have hb0' : ¬ (b.1 = 0 ∧ b.2 = 0) := fun e => hb0 (Prod.ext e.1 e.2)
  rcases gridAdj_cases h with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
    rcases ha' with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
    rcases hb' with ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ <;>
    exact ⟨fun hx => by lia, fun hx => by lia, fun hx => by lia, fun hx => by lia⟩

/-- Any walk inside a center-free subset of the cross stays in one arm. -/
lemma inSameArm_walk {T : Finset (ℤ × ℤ)} (hsub : T ⊆ cross) (h0 : ((0, 0) : ℤ × ℤ) ∉ T)
    {u v : (T : Set (ℤ × ℤ))}
    (w : (gridGraph.induce (T : Set (ℤ × ℤ))).Walk u v) :
    InSameArm (u : ℤ × ℤ) (v : ℤ × ℤ) := by
  induction w with
  | nil =>
    rename_i u
    exact inSameArm_refl (hsub (Finset.mem_coe.mp u.2))
  | cons h p ih =>
    rename_i u v w
    exact inSameArm_trans
      (inSameArm_of_gridAdj (hsub (Finset.mem_coe.mp u.2)) (hsub (Finset.mem_coe.mp v.2))
        (fun e => h0 (Finset.mem_coe.mp (e ▸ v.2))) (SimpleGraph.induce_adj.mp h)) ih

lemma mem_center_of_dinosaur_subset {T : Finset (ℤ × ℤ)} (hT : IsDinosaur T)
    (hsub : T ⊆ cross) : ((0, 0) : ℤ × ℤ) ∈ T := by
  by_contra h0
  have hcard : 2007 ≤ T.card := hT.2
  obtain ⟨a, ha⟩ := hT.1.nonempty
  have ha0 : a ≠ (0, 0) := fun e => h0 (e ▸ ha)
  have key : ∀ b ∈ T, InSameArm a b := fun b hb =>
    inSameArm_walk hsub h0 (hT.1.preconnected ⟨a, Finset.mem_coe.mpr ha⟩
      ⟨b, Finset.mem_coe.mpr hb⟩).some
  have ha' := mem_cross_iff.mp (hsub ha)
  rcases ha' with ⟨h2, h1l, h1u⟩ | ⟨h1, h2l, h2u⟩
  · rcases Int.lt_or_gt_of_ne (fun e => ha0 (Prod.ext e h2)) with hlt | hgt
    · have hsub2 : T ⊆ (Finset.Icc (-2006) (-1)).product {(0 : ℤ)} := by
        intro b hb
        have hb2 := (key b hb).2.2.2 hlt
        have hbc := mem_cross_iff.mp (hsub hb)
        simp only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_singleton,
          Finset.mem_Icc]
        rcases hbc with ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ <;> lia
      have cardprod : ∀ (s t : Finset ℤ), (Finset.product s t).card = s.card * t.card :=
        fun s t => Finset.card_product s t
      have hc : ((Finset.Icc (-2006) (-1)).product {(0 : ℤ)}).card = 2006 := by
        rw [cardprod, Finset.card_singleton, Int.card_Icc]
        decide
      have e := Finset.card_le_card hsub2
      rw [hc] at e
      exact absurd (le_trans hcard e) (by decide)
    · have hsub2 : T ⊆ (Finset.Icc 1 2006).product {(0 : ℤ)} := by
        intro b hb
        have hb2 := (key b hb).2.2.1 hgt
        have hbc := mem_cross_iff.mp (hsub hb)
        simp only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_singleton,
          Finset.mem_Icc]
        rcases hbc with ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ <;> lia
      have cardprod : ∀ (s t : Finset ℤ), (Finset.product s t).card = s.card * t.card :=
        fun s t => Finset.card_product s t
      have hc : ((Finset.Icc (1 : ℤ) 2006).product {(0 : ℤ)}).card = 2006 := by
        rw [cardprod, Finset.card_singleton, Int.card_Icc]
        decide
      have e := Finset.card_le_card hsub2
      rw [hc] at e
      exact absurd (le_trans hcard e) (by decide)
  · rcases Int.lt_or_gt_of_ne (fun e => ha0 (Prod.ext h1 e)) with hlt | hgt
    · have hsub2 : T ⊆ Finset.product {(0 : ℤ)} (Finset.Icc (-2006) (-1)) := by
        intro b hb
        have hb2 := (key b hb).2.1 hlt
        have hbc := mem_cross_iff.mp (hsub hb)
        simp only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_singleton,
          Finset.mem_Icc]
        rcases hbc with ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ <;> lia
      have cardprod : ∀ (s t : Finset ℤ), (Finset.product s t).card = s.card * t.card :=
        fun s t => Finset.card_product s t
      have hc : (Finset.product {(0 : ℤ)} (Finset.Icc (-2006) (-1))).card = 2006 := by
        rw [cardprod, Finset.card_singleton, Int.card_Icc]
        decide
      have e := Finset.card_le_card hsub2
      rw [hc] at e
      exact absurd (le_trans hcard e) (by decide)
    · have hsub2 : T ⊆ Finset.product {(0 : ℤ)} (Finset.Icc 1 2006) := by
        intro b hb
        have hb2 := (key b hb).1 hgt
        have hbc := mem_cross_iff.mp (hsub hb)
        simp only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_singleton,
          Finset.mem_Icc]
        rcases hbc with ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ <;> lia
      have cardprod : ∀ (s t : Finset ℤ), (Finset.product s t).card = s.card * t.card :=
        fun s t => Finset.card_product s t
      have hc : (Finset.product {(0 : ℤ)} (Finset.Icc (1 : ℤ) 2006)).card = 2006 := by
        rw [cardprod, Finset.card_singleton, Int.card_Icc]
        decide
      have e := Finset.card_le_card hsub2
      rw [hc] at e
      exact absurd (le_trans hcard e) (by decide)

lemma isPrimitive_cross : IsPrimitive cross := by
  refine ⟨⟨isAnimal_cross, by rw [card_cross]; norm_num⟩, ?_⟩
  rintro ⟨parts, h2, hall, hdisj, hunion⟩
  obtain ⟨p, hp, q, hq, hne⟩ := Finset.one_lt_card.mp h2
  have hsubp : p ⊆ cross := by
    intro x hx
    have hxb : x ∈ parts.biUnion id := Finset.mem_biUnion.mpr ⟨p, hp, hx⟩
    rwa [hunion] at hxb
  have hsubq : q ⊆ cross := by
    intro x hx
    have hxb : x ∈ parts.biUnion id := Finset.mem_biUnion.mpr ⟨q, hq, hx⟩
    rwa [hunion] at hxb
  have hp0 := mem_center_of_dinosaur_subset (hall p hp) hsubp
  have hq0 := mem_center_of_dinosaur_subset (hall q hq) hsubq
  exact Finset.disjoint_left.mp (hdisj p hp q hq hne) hp0 hq0


snip end

/-- The answer to USAMO 2007 Problem 4. -/
determine answer : ℕ := 8025

problem usa2007_p4 :
    IsGreatest {n : ℕ | ∃ d : Finset (ℤ × ℤ), IsPrimitive d ∧ d.card = n} answer := by
  refine ⟨⟨cross, isPrimitive_cross, card_cross⟩, ?_⟩
  intro n hn
  obtain ⟨d, hprim, rfl⟩ := hn
  obtain ⟨hdino, hnot⟩ := hprim
  obtain ⟨hAni, -⟩ := hdino
  by_contra hle
  have hle' : 8025 < d.card := Nat.lt_of_not_le hle
  have hcard : 4 * 2007 - 2 ≤ d.card := by lia
  obtain ⟨r, hr⟩ := hAni.nonempty
  obtain ⟨A, B, hA, hB, hdisj, hunion⟩ :=
    exists_split d r hr hAni.preconnected hcard
  apply hnot
  have hne : A ≠ B := by
    intro heq
    subst heq
    rw [Finset.disjoint_self_iff_empty] at hdisj
    obtain ⟨a, ha⟩ := hA.1.nonempty
    rw [hdisj] at ha
    exact Finset.notMem_empty a ha
  have hcard2 : ({A, B} : Finset (Finset (ℤ × ℤ))).card = 2 :=
    Finset.card_pair_eq_two_iff.mpr hne
  refine ⟨{A, B}, by lia, ?_, ?_, ?_⟩
  · intro p hp
    rw [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact hA
    · exact hB
  · intro p hp q hq hpq
    rw [Finset.mem_insert, Finset.mem_singleton] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · exact absurd rfl hpq
    · exact hdisj
    · exact hdisj.symm
    · exact absurd rfl hpq
  · rw [show ({A, B} : Finset (Finset (ℤ × ℤ))).biUnion id = A ∪ B by
      ext x
      simp]
    exact hunion

end Usa2007P4
