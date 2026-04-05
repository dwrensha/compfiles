/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Benpigchu
-/
import Mathlib

import ProblemExtraction

problem_file {
  problemImportedFrom :=
    "https://github.com/jsm28/IMOLean/blob/main/IMO/IMO2020P4.lean"
}

/-!
# International Mathematical Olympiad 2020, Problem 4

There is an integer n > 1. There are n² stations on a slope of
a mountain, all at different altitudes. Each of two cable car
companies, A and B, operates k cable cars; each cable car
provides a transfer from one of the stations to a higher one
(with no intermediate stops). The k cable cars of A have k
different starting points and k different finishing points,
and a cable car which starts higher also finishes higher. The
same conditions hold for B. We say that two stations are linked
by a company if one can start from the lower station and reach
the higher one by using one or more cars of that company (no
other movements between stations are allowed). Determine the
smallest positive integer k for which one can guarantee that
there are two stations that are linked by both companies.
-/

namespace Imo2020P4

/-- A cable car's starting and finishing points. -/
structure Car (n : ℕ) : Type where
  /-- The starting point. -/
  start : Fin (n ^ 2)
  /-- The finishing point. -/
  finish : Fin (n ^ 2)
  start_lt_finish : start < finish

/-- The cable cars of a company. -/
structure Company (n k : ℕ) : Type where
  /-- The individual cars. -/
  cars : Fin k → Car n
  injective_start : Function.Injective fun i ↦ (cars i).start
  injective_finish : Function.Injective fun i ↦ (cars i).finish
  monovary_start_finish : Monovary (fun i ↦ (cars i).start) (fun i ↦ (cars i).finish)

/-- A linkage between two stations. -/
structure Company.linkage {n k : ℕ} (c : Company n k) : Type where
  /-- The sequence of cars used. -/
  cars : List (Fin k)
  nonempty : cars ≠ []
  valid : cars.IsChain fun i j ↦ (c.cars i).finish = (c.cars j).start

/-- The first station in a linkage. -/
def Company.linkage.start {n k : ℕ} {c : Company n k} (x : c.linkage) : Fin (n ^ 2) :=
  (c.cars (x.cars.head x.nonempty)).start

/-- The last station in a linkage. -/
def Company.linkage.finish {n k : ℕ} {c : Company n k} (x : c.linkage) : Fin (n ^ 2) :=
  (c.cars (x.cars.getLast x.nonempty)).finish

/-- The property of two stations being linked (in the given order). -/
def Company.linked {n k : ℕ} (c : Company n k) (l h : Fin (n ^ 2)) : Prop :=
  ∃ x : c.linkage, x.start = l ∧ x.finish = h

snip begin

universe u

lemma Sym2.exists_mk {α : Type u} (z : Sym2 α) : ∃ x y : α, z = s(x, y) := by
  have h := Sym2.out_fst_mem z
  rw [Sym2.mem_iff_exists] at h
  rcases h with ⟨y, hy⟩
  use (Quot.out z).1
  use y

lemma SimpleGraph.sum_card_connectedComponent_eq_card
  {V : Type u} [Fintype V] {G : SimpleGraph V}
  : ∑ (c : G.ConnectedComponent), Nat.card c = Fintype.card V := by
    have h₁ : ∑ (c : G.ConnectedComponent), Nat.card c = ∑ (c : G.ConnectedComponent), c.supp.ncard := by
      apply Finset.sum_congr rfl
      intro c _
      rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
      congr
    rw [h₁]
    have h_finite : ∀ (c : G.ConnectedComponent), (c.supp).Finite := by
      intro c
      apply Set.Finite.subset Set.finite_univ (Set.subset_univ _)
    have h_disjoint : Pairwise (Function.onFun Disjoint (@SimpleGraph.ConnectedComponent.supp _ G)) := by
      apply SimpleGraph.pairwise_disjoint_supp_connectedComponent
    have h₂ := Set.ncard_iUnion_of_finite h_finite h_disjoint
    rw [finsum_eq_sum_of_fintype] at h₂
    rw [← h₂]
    rw [SimpleGraph.iUnion_connectedComponentSupp G]
    rw [Set.ncard_univ, Fintype.card_eq_nat_card]

lemma SimpleGraph.sum_card_edgeFinset_toSimpleGraph_connectedComponent_eq_edgeFinset_card
  {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
  : ∑ (c : G.ConnectedComponent), c.toSimpleGraph.edgeFinset.card = G.edgeFinset.card := by
    set f := fun c : G.ConnectedComponent ↦ c.toSimpleGraph.edgeFinset.image (fun e ↦ e.map fun v ↦ v.val) with hf
    have h₁ : ∑ (c : G.ConnectedComponent),c.toSimpleGraph.edgeFinset.card = ∑ (c : G.ConnectedComponent), (f c).card := by
      apply Finset.sum_congr rfl
      intro c _
      rw [hf]
      dsimp
      symm
      apply Finset.card_image_of_injective
      apply Sym2.map.injective
      apply Subtype.val_injective
    rw [h₁]
    have h_disjoint : (SetLike.coe Finset.univ).PairwiseDisjoint f := by
      intro a ha b hb hab
      rw [Function.onFun,]
      contrapose! hab
      rw [Finset.not_disjoint_iff] at hab
      rcases hab with ⟨e, hea, heb⟩
      rw [hf] at hea heb
      dsimp at hea heb
      rw [Finset.mem_image] at hea heb
      rcases hea with ⟨e₁, he₁, hee₁⟩
      rcases heb with ⟨e₂, he₂, hee₂⟩
      rcases Sym2.exists_mk e with ⟨v, u, rfl⟩
      have hv₁ := Sym2.mem_mk_left v u
      nth_rw 1 [← hee₁] at hv₁
      have hv₂ := Sym2.mem_mk_left v u
      nth_rw 1 [← hee₂] at hv₂
      rw [Sym2.mem_map] at hv₁ hv₂
      rcases hv₁ with ⟨v₁, hv₁, hvv₁⟩
      rcases hv₂ with ⟨v₂, hv₂, hvv₂⟩
      rcases v₁ with ⟨v₁', hv₁'⟩
      rcases v₂ with ⟨v₂', hv₂'⟩
      rw [← SetLike.mem_coe] at hv₁' hv₂'
      rw [(by congr : ↑a = a.supp)] at hv₁'
      rw [(by congr : ↑b = b.supp)] at hv₂'
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hv₁' hv₂'
      simp only at hvv₁ hvv₂
      rw [← hv₁', ← hv₂', hvv₁, hvv₂]
    have h₂ := Finset.card_biUnion h_disjoint
    rw [← h₂]
    congr
    ext e
    rw [Finset.mem_biUnion, hf]
    dsimp
    constructor
    · rintro ⟨c, _, hce⟩
      rw [Finset.mem_image] at hce
      rcases hce with ⟨e', he', hee'⟩
      rcases Sym2.exists_mk e' with ⟨v, u, rfl⟩
      rw [Sym2.map_mk] at hee'
      rw [← hee']
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he' ⊢
      rw [SimpleGraph.ConnectedComponent.toSimpleGraph_adj] at he'
      exact he'
    · intro he
      rcases Sym2.exists_mk e with ⟨v, u, rfl⟩
      use G.connectedComponentMk v
      rw [and_iff_right (Finset.mem_univ _)]
      rw [Finset.mem_image]
      have hv := @SimpleGraph.ConnectedComponent.connectedComponentMk_mem _ G v
      have hu : u ∈ G.connectedComponentMk v := by
        rw [← SetLike.mem_coe] at hv ⊢
        rw [(by congr : ↑(G.connectedComponentMk v) = (G.connectedComponentMk v).supp)] at hv ⊢
        apply SimpleGraph.ConnectedComponent.mem_supp_of_adj_mem_supp _ hv
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
        exact he
      use s(⟨v, hv⟩, ⟨u, hu⟩)
      constructor
      · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he ⊢
        rw [SimpleGraph.ConnectedComponent.toSimpleGraph_adj]
        exact he
      · dsimp

lemma SimpleGraph.card_connectedComponent_add_card_edge_eq_card_vertex_of_acyclic
  {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} (h : G.IsAcyclic)
  : Fintype.card G.ConnectedComponent + G.edgeFinset.card = Fintype.card V := by
    have h₁ : ∀ (c : G.ConnectedComponent) (_ : c ∈ Finset.univ), c.toSimpleGraph.edgeFinset.card + 1 = Nat.card c := by
      intro c _
      rw [← (SimpleGraph.isTree_iff_connected_and_card.mp (SimpleGraph.IsAcyclic.isTree_connectedComponent h c)).right]
      congr
      rw [SimpleGraph.edgeFinset_card, Fintype.card_eq_nat_card]
    have h₂ := Finset.sum_congr (@rfl _ Finset.univ) h₁
    rw [Finset.sum_add_distrib, ← Finset.card_eq_sum_ones, Finset.card_univ, add_comm] at h₂
    rw [SimpleGraph.sum_card_connectedComponent_eq_card] at h₂
    rw [SimpleGraph.sum_card_edgeFinset_toSimpleGraph_connectedComponent_eq_edgeFinset_card] at h₂
    exact h₂

def Company.graph {n k : ℕ} (c : Company n k) : SimpleGraph (Fin (n ^ 2)) where
  Adj := fun a b ↦ ∃ i : Fin k, s((c.cars i).start, (c.cars i).finish) = s(a, b)
  symm := by
    intro a b
    dsimp
    rintro ⟨i, h⟩
    use i
    rw [h, Sym2.eq_swap]
  loopless := by
    apply Std.Irrefl.mk
    intro a
    push Not
    intro i
    rw [ne_eq, Sym2.eq_iff, not_or]
    have h := (c.cars i).start_lt_finish
    constructor <;> contrapose! h <;> rw [h.left, h.right]

lemma Company.graph_edgeFinset_card {n k : ℕ} (c : Company n k)
  : c.graph.edgeFinset.card = k := by
    set f := fun i : Fin k ↦ s((c.cars i).start, (c.cars i).finish) with hf
    have h : c.graph.edgeFinset = Finset.image f Finset.univ := by
      ext e
      rcases Sym2.exists_mk e with ⟨v, u, rfl⟩
      rw [Finset.mem_image, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      rw [Company.graph, hf]
      dsimp
      constructor
      · rintro ⟨i, hi⟩
        use i
        rw [and_iff_right (Finset.mem_univ _)]
        exact hi
      · rintro ⟨i, hi⟩
        use i
        exact hi.right
    have h' : Function.Injective f := by
      intro i j hij
      rw [hf] at hij
      dsimp at hij
      rw [Sym2.eq_iff] at hij
      rcases hij with (hij|hij)
      · apply c.injective_start
        dsimp
        exact hij.left
      · have h := (c.cars i).start_lt_finish
        contrapose! h
        rw [hij.left, hij.right]
        apply le_of_lt
        exact (c.cars j).start_lt_finish
    rw [h, Finset.card_image_of_injective _ h', Finset.card_univ, Fintype.card_fin]

lemma Company.graph_isAcyclic {n k : ℕ} {c : Company n k}
  : c.graph.IsAcyclic := by
    intro v w hw
    have hw' := SimpleGraph.Walk.support_ne_nil w
    set v' := w.support.min hw' with hv'
    rcases (List.min_eq_iff _).mp hv' with ⟨h'v', h''v'⟩
    have h := SimpleGraph.Walk.IsCycle.ncard_neighborSet_toSubgraph_eq_two hw h'v'
    rw [Set.ncard_eq_two] at h
    rcases h with ⟨x, y, hxy, hv'xy⟩
    have hx' : x ∈ w.toSubgraph.neighborSet v' := by
      rw [hv'xy]
      apply Set.mem_insert
    have hy' : y ∈ w.toSubgraph.neighborSet v' := by
      rw [hv'xy]
      apply Set.mem_insert_of_mem
      apply Set.mem_singleton
    rw [SimpleGraph.Subgraph.mem_neighborSet] at hx' hy'
    have hx'' := SimpleGraph.Subgraph.adj_sub _ hx'
    have hy'' := SimpleGraph.Subgraph.adj_sub _ hy'
    rw [Company.graph] at hx'' hy''
    dsimp at hx'' hy''
    rw [SimpleGraph.Subgraph.adj_comm] at hx' hy'
    apply SimpleGraph.Walk.mem_support_of_adj_toSubgraph at hx'
    apply SimpleGraph.Walk.mem_support_of_adj_toSubgraph at hy'
    rcases hx'' with ⟨i, hi⟩
    rcases hy'' with ⟨j, hj⟩
    rw [Sym2.eq_iff] at hi hj
    have hv'x := h''v' x hx'
    have hv'y := h''v' y hy'
    rw [← hv'] at hv'x hv'y
    have hi' : ¬((c.cars i).start = x ∧ (c.cars i).finish = v') := by
      contrapose! hv'x
      rw [← hv'x.left, ← hv'x.right]
      exact (c.cars i).start_lt_finish
    have hj' : ¬((c.cars j).start = y ∧ (c.cars j).finish = v') := by
      contrapose! hv'y
      rw [← hv'y.left, ← hv'y.right]
      exact (c.cars j).start_lt_finish
    rw [or_iff_left hi'] at hi
    rw [or_iff_left hj'] at hj
    contrapose! hxy
    rw [← hi.right, ← hj.right]
    congr
    apply c.injective_start
    dsimp
    rw [hi.left, hj.left]

lemma Company.low_le_of_mem_path {n k : ℕ} {c : Company n k} {l h : Fin (n ^ 2)} (hlh : l < h)
  {p : c.graph.Walk l h} (hp : p.IsPath) {x : Fin (n ^ 2)} (hx : x ∈ p.support)
  : l ≤ x := by
    have hp' := SimpleGraph.Walk.support_ne_nil p
    set v' := p.support.min hp' with hv'
    rcases (List.min_eq_iff _).mp hv' with ⟨h'v', h''v'⟩
    rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp h'v' with ⟨i, hiv', hi⟩
    by_cases! hi' : i = 0
    · rw [hi', SimpleGraph.Walk.getVert_zero] at hiv'
      rw [hiv']
      apply h''v'
      exact hx
    · have hi'' : i < p.length := by
        apply lt_of_le_of_ne hi
        contrapose! h''v'
        refine ⟨l,SimpleGraph.Walk.start_mem_support p, ?_⟩
        rw [← hiv', h''v', SimpleGraph.Walk.getVert_length]
        exact hlh
      have h := SimpleGraph.Walk.IsPath.ncard_neighborSet_toSubgraph_internal_eq_two hp hi' hi''
      rw [Set.ncard_eq_two] at h
      rcases h with ⟨x, y, hxy, hv'xy⟩
      rw [hiv', ← hv'] at hv'xy
      have hx' : x ∈ p.toSubgraph.neighborSet v' := by
        rw [hv'xy]
        apply Set.mem_insert
      have hy' : y ∈ p.toSubgraph.neighborSet v' := by
        rw [hv'xy]
        apply Set.mem_insert_of_mem
        apply Set.mem_singleton
      rw [SimpleGraph.Subgraph.mem_neighborSet] at hx' hy'
      have hx'' := SimpleGraph.Subgraph.adj_sub _ hx'
      have hy'' := SimpleGraph.Subgraph.adj_sub _ hy'
      rw [Company.graph] at hx'' hy''
      dsimp at hx'' hy''
      rw [SimpleGraph.Subgraph.adj_comm] at hx' hy'
      apply SimpleGraph.Walk.mem_support_of_adj_toSubgraph at hx'
      apply SimpleGraph.Walk.mem_support_of_adj_toSubgraph at hy'
      rcases hx'' with ⟨i, hi⟩
      rcases hy'' with ⟨j, hj⟩
      rw [Sym2.eq_iff] at hi hj
      have hv'x := h''v' x hx'
      have hv'y := h''v' y hy'
      rw [← hv'] at hv'x hv'y
      have hi' : ¬((c.cars i).start = x ∧ (c.cars i).finish = v') := by
        contrapose! hv'x
        rw [← hv'x.left, ← hv'x.right]
        exact (c.cars i).start_lt_finish
      have hj' : ¬((c.cars j).start = y ∧ (c.cars j).finish = v') := by
        contrapose! hv'y
        rw [← hv'y.left, ← hv'y.right]
        exact (c.cars j).start_lt_finish
      rw [or_iff_left hi'] at hi
      rw [or_iff_left hj'] at hj
      contrapose! hxy
      rw [← hi.right, ← hj.right]
      congr
      apply c.injective_start
      dsimp
      rw [hi.left, hj.left]

lemma Company.le_high_of_mem_path {n k : ℕ} {c : Company n k} {l h : Fin (n ^ 2)} (hlh : l < h)
  {p : c.graph.Walk l h} (hp : p.IsPath) {x : Fin (n ^ 2)} (hx : x ∈ p.support)
  : x ≤ h := by
    have hp' := SimpleGraph.Walk.support_ne_nil p
    set v' := p.support.max hp' with hv'
    rcases (List.max_eq_iff _).mp hv' with ⟨h'v', h''v'⟩
    rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp h'v' with ⟨i, hiv', hi⟩
    by_cases! hi' : i = p.length
    · rw [hi', SimpleGraph.Walk.getVert_length] at hiv'
      rw [hiv']
      apply h''v'
      exact hx
    · have hi'' : i < p.length := by
        apply lt_of_le_of_ne hi hi'
      have hi''' : i ≠ 0 := by
        contrapose! h''v'
        refine ⟨h, SimpleGraph.Walk.end_mem_support p, ?_⟩
        rw [← hiv', h''v', SimpleGraph.Walk.getVert_zero]
        exact hlh
      have h := SimpleGraph.Walk.IsPath.ncard_neighborSet_toSubgraph_internal_eq_two hp hi''' hi''
      rw [Set.ncard_eq_two] at h
      rcases h with ⟨x, y, hxy, hv'xy⟩
      rw [hiv', ← hv'] at hv'xy
      have hx' : x ∈ p.toSubgraph.neighborSet v' := by
        rw [hv'xy]
        apply Set.mem_insert
      have hy' : y ∈ p.toSubgraph.neighborSet v' := by
        rw [hv'xy]
        apply Set.mem_insert_of_mem
        apply Set.mem_singleton
      rw [SimpleGraph.Subgraph.mem_neighborSet] at hx' hy'
      have hx'' := SimpleGraph.Subgraph.adj_sub _ hx'
      have hy'' := SimpleGraph.Subgraph.adj_sub _ hy'
      rw [Company.graph] at hx'' hy''
      dsimp at hx'' hy''
      rw [SimpleGraph.Subgraph.adj_comm] at hx' hy'
      apply SimpleGraph.Walk.mem_support_of_adj_toSubgraph at hx'
      apply SimpleGraph.Walk.mem_support_of_adj_toSubgraph at hy'
      rcases hx'' with ⟨i, hi⟩
      rcases hy'' with ⟨j, hj⟩
      rw [Sym2.eq_iff] at hi hj
      have hv'x := h''v' x hx'
      have hv'y := h''v' y hy'
      rw [← hv'] at hv'x hv'y
      have hi' : ¬((c.cars i).start = v' ∧ (c.cars i).finish = x) := by
        contrapose! hv'x
        rw [← hv'x.left, ← hv'x.right]
        exact (c.cars i).start_lt_finish
      have hj' : ¬((c.cars j).start = v' ∧ (c.cars j).finish = y) := by
        contrapose! hv'y
        rw [← hv'y.left, ← hv'y.right]
        exact (c.cars j).start_lt_finish
      rw [or_iff_right hi'] at hi
      rw [or_iff_right hj'] at hj
      contrapose! hxy
      rw [← hi.left, ← hj.left]
      congr
      apply c.injective_finish
      dsimp
      rw [hi.right, hj.right]

lemma Company.linked_of_graph_reachable {n k : ℕ} {c : Company n k} {l h : Fin (n ^ 2)}
  (h₁ : c.graph.Reachable l h) (h₂ : l < h)
  : c.linked l h := by
    apply SimpleGraph.Reachable.exists_isPath at h₁
    rcases h₁ with ⟨p, hp⟩
    induction' p with v l l' h hll' p' hp'
    · contrapose! h₂
      apply le_refl
    · have hl'p : l' ∈ (SimpleGraph.Walk.cons hll' p').support := by
        rw [SimpleGraph.Walk.support_cons]
        apply List.mem_cons_of_mem
        rw [SimpleGraph.Walk.mem_support_iff]
        left
        rfl
      have h'll' := c.low_le_of_mem_path h₂ hp hl'p
      have h'l'h := c.le_high_of_mem_path h₂ hp hl'p
      rw [le_iff_eq_or_lt] at h'l'h
      rw [Company.graph] at hll'
      dsimp at hll'
      rcases hll' with ⟨i, hi⟩
      rw [Sym2.eq_iff] at hi
      have hi' : ¬((c.cars i).start = l' ∧ (c.cars i).finish = l) := by
        contrapose! h'll'
        rw [← h'll'.left, ← h'll'.right]
        exact (c.cars i).start_lt_finish
      rw [or_iff_left hi'] at hi
      rcases h'l'h with (h'l'h|h'l'h)
      · use {
          cars := [i],
          nonempty := List.cons_ne_nil _ _,
          valid := List.IsChain.singleton i
        }
        constructor
        · rw [Company.linkage.start]
          dsimp
          exact hi.left
        · rw [Company.linkage.finish]
          dsimp
          rw [← h'l'h]
          exact hi.right
      · have h' := hp' h'l'h hp.of_cons
        rw [Company.linked] at h' ⊢
        rcases h' with ⟨link', h_link'_l', h_link'_h⟩
        rcases link' with ⟨cars', h_cars', h'_cars'⟩
        rw [Company.linkage.start] at h_link'_l'
        rw [Company.linkage.finish] at h_link'_h
        dsimp at h_link'_l' h_link'_h
        use {
          cars := i :: cars',
          nonempty := List.cons_ne_nil _ _,
          valid := by
            rw [List.isChain_cons, and_iff_left h'_cars']
            intro head hhead
            rw [Option.mem_def] at hhead
            rw [(List.head_eq_iff_head?_eq_some _).mpr hhead] at h_link'_l'
            rw [h_link'_l']
            exact hi.right
        }
        constructor
        · rw [Company.linkage.start]
          dsimp
          exact hi.left
        · rw [Company.linkage.finish]
          dsimp
          rw [List.getLast_cons h_cars']
          apply h_link'_h

lemma Company.lt_of_linked {n k : ℕ} {c : Company n k} {l h : Fin (n ^ 2)} (hlh : c.linked l h)
  : l < h := by
    rw [Company.linked] at hlh
    rcases hlh with ⟨link, h_link_l, h_link_h⟩
    rcases link with ⟨cars, hcars', hcars⟩
    induction' cars with head tail h' generalizing l h
    · have h'' := hcars'
      contrapose! h''
      rfl
    · rw [Company.linkage.start] at h_link_l
      rw [Company.linkage.finish] at h_link_h
      dsimp at h_link_l h_link_h
      by_cases! h_tail : tail = []
      · simp only [h_tail, List.getLast_singleton] at h_link_h
        rw [← h_link_l, ← h_link_h]
        apply (c.cars head).start_lt_finish
      · have hcars'' := List.isChain_cons.mp hcars
        have h_tail_start : ({ cars := tail, nonempty := h_tail, valid := hcars''.right } : c.linkage).start = (c.cars head).finish := by
          rw [Company.linkage.start]
          dsimp
          symm
          apply hcars''.left
          apply List.head_mem_head?
        have h_tail_end : ({ cars := tail, nonempty := h_tail, valid := hcars''.right } : c.linkage).finish = h := by
          rw [Company.linkage.finish]
          dsimp
          rw [List.getLast_cons h_tail] at h_link_h
          rw [h_link_h]
        have h'' := h' h_tail hcars''.right h_tail_start h_tail_end
        apply lt_trans' h''
        rw [← h_link_l]
        apply (c.cars head).start_lt_finish

lemma aux_succ (n : Set.Ioi 1) : ((↑n - 1 + 1) : ℕ) = ↑n := by
  have hn := Subtype.property n
  rw [Set.mem_Ioi] at hn
  apply Nat.sub_add_cancel
  apply le_of_lt hn

lemma aux_pow (n : Set.Ioi 1) : ((↑n * ↑n) : ℕ) = ↑n ^ 2 := by
  rw [pow_two]

lemma aux_A (n : Set.Ioi 1) : ((↑n * ↑n - ↑n) : ℕ) = (↑n - 1) * ↑n := by
  rw [Nat.sub_mul, one_mul]

lemma aux_B (n : Set.Ioi 1) : ((↑n * ↑n - ↑n) : ℕ) = ↑n * (↑n - 1) := by
  rw [Nat.mul_sub, mul_one]

def constructCompanyA (n : Set.Ioi 1) : Company ↑n (↑n * ↑n - ↑n) where
  cars := fun i ↦ {
    start := Fin.cast (aux_pow n) (Fin.mkDivMod (Fin.cast (aux_succ n) (Fin.cast (aux_A n) i).divNat.castSucc) (Fin.cast (aux_A n) i).modNat)
    finish := Fin.cast (aux_pow n) (Fin.mkDivMod (Fin.cast (aux_succ n) (Fin.cast (aux_A n) i).divNat.succ) (Fin.cast (aux_A n) i).modNat)
    start_lt_finish := by
      rw [← Fin.val_fin_lt, Fin.val_cast, Fin.val_cast]
      rw [Fin.coe_mkDivMod, Fin.coe_mkDivMod, Fin.val_cast, Fin.val_cast]
      rw [Fin.val_succ, Fin.val_castSucc]
      lia
  }
  injective_start := by
    intro x y hxy
    dsimp at hxy
    rw [← Fin.cast_inj (aux_A n), ← Fin.val_inj]
    rw [← Fin.divNat_mkDivMod_modNat (Fin.cast _ x), ← Fin.divNat_mkDivMod_modNat (Fin.cast _ y)]
    rw [← Fin.val_inj, Fin.val_cast, Fin.val_cast, Fin.val_inj] at hxy
    have h_div : (Fin.cast (aux_A n) x).divNat = (Fin.cast (aux_A n) y).divNat := by
      rw [← Fin.castSucc_inj, ← Fin.cast_inj (aux_succ n)]
      rw [← Fin.divNat_mkDivMod (Fin.cast (aux_succ n) (Fin.cast (aux_A n) x).divNat.castSucc) (Fin.cast (aux_A n) x).modNat]
      rw [← Fin.divNat_mkDivMod (Fin.cast (aux_succ n) (Fin.cast (aux_A n) y).divNat.castSucc) (Fin.cast (aux_A n) y).modNat]
      rw [hxy]
    have h_mod : (Fin.cast (aux_A n) x).modNat = (Fin.cast (aux_A n) y).modNat := by
      rw [← Fin.modNat_mkDivMod (Fin.cast (aux_succ n) (Fin.cast (aux_A n) x).divNat.castSucc) (Fin.cast (aux_A n) x).modNat]
      rw [← Fin.modNat_mkDivMod (Fin.cast (aux_succ n) (Fin.cast (aux_A n) y).divNat.castSucc) (Fin.cast (aux_A n) y).modNat]
      rw [hxy]
    rw [h_div, h_mod]
  injective_finish := by
    intro x y hxy
    dsimp at hxy
    rw [← Fin.cast_inj (aux_A n), ← Fin.val_inj]
    rw [← Fin.divNat_mkDivMod_modNat (Fin.cast _ x), ← Fin.divNat_mkDivMod_modNat (Fin.cast _ y)]
    rw [← Fin.val_inj, Fin.val_cast, Fin.val_cast, Fin.val_inj] at hxy
    have h_div : (Fin.cast (aux_A n) x).divNat = (Fin.cast (aux_A n) y).divNat := by
      rw [← Fin.succ_inj, ← Fin.cast_inj (aux_succ n)]
      rw [← Fin.divNat_mkDivMod (Fin.cast (aux_succ n) (Fin.cast (aux_A n) x).divNat.succ) (Fin.cast (aux_A n) x).modNat]
      rw [← Fin.divNat_mkDivMod (Fin.cast (aux_succ n) (Fin.cast (aux_A n) y).divNat.succ) (Fin.cast (aux_A n) y).modNat]
      rw [hxy]
    have h_mod : (Fin.cast (aux_A n) x).modNat = (Fin.cast (aux_A n) y).modNat := by
      rw [← Fin.modNat_mkDivMod (Fin.cast (aux_succ n) (Fin.cast (aux_A n) x).divNat.succ) (Fin.cast (aux_A n) x).modNat]
      rw [← Fin.modNat_mkDivMod (Fin.cast (aux_succ n) (Fin.cast (aux_A n) y).divNat.succ) (Fin.cast (aux_A n) y).modNat]
      rw [hxy]
    rw [h_div, h_mod]
  monovary_start_finish := by
    intro x y hxy
    dsimp at hxy ⊢
    rw [Fin.le_iff_val_le_val, Fin.val_cast, Fin.val_cast]
    rw [Fin.coe_mkDivMod, Fin.coe_mkDivMod, Fin.val_cast, Fin.val_cast]
    rw [Fin.val_castSucc, Fin.val_castSucc]
    rw [Fin.lt_def, Fin.val_cast, Fin.val_cast] at hxy
    rw [Fin.coe_mkDivMod, Fin.coe_mkDivMod, Fin.val_cast, Fin.val_cast] at hxy
    rw [Fin.val_succ, Fin.val_succ, mul_add, mul_add] at hxy
    rw [mul_one, add_right_comm _ n.val _, add_right_comm _ n.val _] at hxy
    rw [add_lt_add_iff_right] at hxy
    apply le_of_lt hxy

def constructCompanyB (n : Set.Ioi 1) : Company ↑n (↑n * ↑n - ↑n) where
  cars := fun i ↦ {
    start := Fin.cast (aux_pow n) (Fin.mkDivMod (Fin.cast (aux_B n) i).divNat (Fin.cast (aux_succ n) (Fin.cast (aux_B n) i).modNat.castSucc))
    finish := Fin.cast (aux_pow n) (Fin.mkDivMod (Fin.cast (aux_B n) i).divNat (Fin.cast (aux_succ n) (Fin.cast (aux_B n) i).modNat.succ))
    start_lt_finish := by
      rw [← Fin.val_fin_lt, Fin.val_cast, Fin.val_cast]
      rw [Fin.coe_mkDivMod, Fin.coe_mkDivMod, Fin.val_cast, Fin.val_cast]
      rw [Fin.val_succ, Fin.val_castSucc]
      lia
  }
  injective_start := by
    intro x y hxy
    dsimp at hxy
    rw [← Fin.cast_inj (aux_B n), ← Fin.val_inj]
    rw [← Fin.divNat_mkDivMod_modNat (Fin.cast _ x), ← Fin.divNat_mkDivMod_modNat (Fin.cast _ y)]
    rw [← Fin.val_inj, Fin.val_cast, Fin.val_cast, Fin.val_inj] at hxy
    have h_div : (Fin.cast (aux_B n) x).divNat = (Fin.cast (aux_B n) y).divNat := by
      rw [← Fin.divNat_mkDivMod (Fin.cast (aux_B n) x).divNat (Fin.cast (aux_succ n) (Fin.cast (aux_B n) x).modNat.castSucc)]
      rw [← Fin.divNat_mkDivMod (Fin.cast (aux_B n) y).divNat (Fin.cast (aux_succ n) (Fin.cast (aux_B n) y).modNat.castSucc)]
      rw [hxy]
    have h_mod : (Fin.cast (aux_B n) x).modNat = (Fin.cast (aux_B n) y).modNat := by
      rw [← Fin.castSucc_inj, ← Fin.cast_inj (aux_succ n)]
      rw [← Fin.modNat_mkDivMod (Fin.cast (aux_B n) x).divNat (Fin.cast (aux_succ n) (Fin.cast (aux_B n) x).modNat.castSucc)]
      rw [← Fin.modNat_mkDivMod (Fin.cast (aux_B n) y).divNat (Fin.cast (aux_succ n) (Fin.cast (aux_B n) y).modNat.castSucc)]
      rw [hxy]
    rw [h_div, h_mod]
  injective_finish := by
    intro x y hxy
    dsimp at hxy
    rw [← Fin.cast_inj (aux_B n), ← Fin.val_inj]
    rw [← Fin.divNat_mkDivMod_modNat (Fin.cast _ x), ← Fin.divNat_mkDivMod_modNat (Fin.cast _ y)]
    rw [← Fin.val_inj, Fin.val_cast, Fin.val_cast, Fin.val_inj] at hxy
    have h_div : (Fin.cast (aux_B n) x).divNat = (Fin.cast (aux_B n) y).divNat := by
      rw [← Fin.divNat_mkDivMod (Fin.cast (aux_B n) x).divNat (Fin.cast (aux_succ n) (Fin.cast (aux_B n) x).modNat.succ)]
      rw [← Fin.divNat_mkDivMod (Fin.cast (aux_B n) y).divNat (Fin.cast (aux_succ n) (Fin.cast (aux_B n) y).modNat.succ)]
      rw [hxy]
    have h_mod : (Fin.cast (aux_B n) x).modNat = (Fin.cast (aux_B n) y).modNat := by
      rw [← Fin.succ_inj, ← Fin.cast_inj (aux_succ n)]
      rw [← Fin.modNat_mkDivMod (Fin.cast (aux_B n) x).divNat (Fin.cast (aux_succ n) (Fin.cast (aux_B n) x).modNat.succ)]
      rw [← Fin.modNat_mkDivMod (Fin.cast (aux_B n) y).divNat (Fin.cast (aux_succ n) (Fin.cast (aux_B n) y).modNat.succ)]
      rw [hxy]
    rw [h_div, h_mod]
  monovary_start_finish := by
    intro x y hxy
    dsimp at hxy ⊢
    rw [Fin.le_iff_val_le_val, Fin.val_cast, Fin.val_cast]
    rw [Fin.coe_mkDivMod, Fin.coe_mkDivMod, Fin.val_cast, Fin.val_cast]
    rw [Fin.val_castSucc, Fin.val_castSucc]
    rw [Fin.lt_def, Fin.val_cast, Fin.val_cast] at hxy
    rw [Fin.coe_mkDivMod, Fin.coe_mkDivMod, Fin.val_cast, Fin.val_cast] at hxy
    rw [Fin.val_succ, Fin.val_succ, ] at hxy
    rw [← add_assoc _ _ 1, ← add_assoc _ _ 1] at hxy
    rw [add_lt_add_iff_right] at hxy
    apply le_of_lt hxy

lemma cast_modNat_eq_of_linked_constructCompanyA {n : Set.Ioi 1}
  {l h : Fin (↑n ^ 2)} (hlh : (constructCompanyA n).linked l h)
  : (Fin.cast (aux_pow n).symm l).modNat = (Fin.cast (aux_pow n).symm h).modNat := by
    rw [Company.linked] at hlh
    rcases hlh with ⟨link, h_link_l, h_link_h⟩
    rcases link with ⟨cars, hcars', hcars⟩
    induction' cars with head tail h' generalizing l h
    · have h'' := hcars'
      contrapose! h''
      rfl
    · rw [Company.linkage.start] at h_link_l
      rw [Company.linkage.finish] at h_link_h
      dsimp at h_link_l h_link_h
      by_cases! h_tail : tail = []
      · simp only [h_tail, List.getLast_singleton] at h_link_h
        rw [← h_link_l, ← h_link_h]
        rw [constructCompanyA]
        dsimp
        rw [Fin.modNat_mkDivMod, Fin.modNat_mkDivMod]
      · have hcars'' := List.isChain_cons.mp hcars
        have h_tail_start : ({ cars := tail, nonempty := h_tail, valid := hcars''.right } : (constructCompanyA n).linkage).start = ((constructCompanyA n).cars head).finish := by
          rw [Company.linkage.start]
          dsimp
          symm
          apply hcars''.left
          apply List.head_mem_head?
        have h_tail_end : ({ cars := tail, nonempty := h_tail, valid := hcars''.right } : (constructCompanyA n).linkage).finish = h := by
          rw [Company.linkage.finish]
          dsimp
          rw [List.getLast_cons h_tail] at h_link_h
          rw [h_link_h]
        have h'' := h' h_tail hcars''.right h_tail_start h_tail_end
        rw [← h'', ← h_link_l]
        rw [constructCompanyA]
        dsimp
        rw [Fin.modNat_mkDivMod, Fin.modNat_mkDivMod]

lemma cast_divNat_eq_of_linked_constructCompanyB {n : Set.Ioi 1}
  {l h : Fin (↑n ^ 2)} (hlh : (constructCompanyB n).linked l h)
  : (Fin.cast (aux_pow n).symm l).divNat = (Fin.cast (aux_pow n).symm h).divNat := by
    rw [Company.linked] at hlh
    rcases hlh with ⟨link, h_link_l, h_link_h⟩
    rcases link with ⟨cars, hcars', hcars⟩
    induction' cars with head tail h' generalizing l h
    · have h'' := hcars'
      contrapose! h''
      rfl
    · rw [Company.linkage.start] at h_link_l
      rw [Company.linkage.finish] at h_link_h
      dsimp at h_link_l h_link_h
      by_cases! h_tail : tail = []
      · simp only [h_tail, List.getLast_singleton] at h_link_h
        rw [← h_link_l, ← h_link_h]
        rw [constructCompanyB]
        dsimp
        rw [Fin.divNat_mkDivMod, Fin.divNat_mkDivMod]
      · have hcars'' := List.isChain_cons.mp hcars
        have h_tail_start : ({ cars := tail, nonempty := h_tail, valid := hcars''.right } : (constructCompanyB n).linkage).start = ((constructCompanyB n).cars head).finish := by
          rw [Company.linkage.start]
          dsimp
          symm
          apply hcars''.left
          apply List.head_mem_head?
        have h_tail_end : ({ cars := tail, nonempty := h_tail, valid := hcars''.right } : (constructCompanyB n).linkage).finish = h := by
          rw [Company.linkage.finish]
          dsimp
          rw [List.getLast_cons h_tail] at h_link_h
          rw [h_link_h]
        have h'' := h' h_tail hcars''.right h_tail_start h_tail_end
        rw [← h'', ← h_link_l]
        rw [constructCompanyB]
        dsimp
        rw [Fin.divNat_mkDivMod, Fin.divNat_mkDivMod]

def Company.subCompany {n k : ℕ} (c : Company n k) {k' : ℕ} (hk' : k' ≤ k) : Company n k' where
  cars := fun i ↦ c.cars (Fin.castLE hk' i)
  injective_start := by
    intro x y hxy
    dsimp at hxy
    apply c.injective_start at hxy
    rw [Fin.castLE_inj] at hxy
    exact hxy
  injective_finish := by
    intro x y hxy
    dsimp at hxy
    apply c.injective_finish at hxy
    rw [Fin.castLE_inj] at hxy
    exact hxy
  monovary_start_finish := by
    intro x y hxy
    dsimp at hxy ⊢
    apply c.monovary_start_finish
    dsimp
    exact hxy

lemma Company.linked_of_subCompany_linked {n k : ℕ} (c : Company n k) {k' : ℕ} (hk' : k' ≤ k)
  (l h : Fin (n ^ 2)) (hlh : (c.subCompany hk').linked l h)
  : c.linked l h := by
    rw [Company.linked] at hlh ⊢
    rcases hlh with ⟨link, h_link_l, h_link_h⟩
    use {
      cars := link.cars.map (Fin.castLE hk')
      nonempty := by
        rw [List.map_eq_nil_iff.ne]
        exact link.nonempty
      valid := by
        apply List.isChain_map_of_isChain _ _ link.valid
        intro x y hxy
        rw [Company.subCompany] at hxy
        dsimp at hxy
        exact hxy
    }
    constructor
    · rw [Company.linkage.start] at ⊢ h_link_l
      simp only [Company.subCompany] at h_link_l
      dsimp
      rw [← h_link_l]
      rw [List.head_map]
    · rw [Company.linkage.finish] at ⊢ h_link_h
      simp only [Company.subCompany] at h_link_h
      dsimp
      rw [← h_link_h]
      rw [List.getLast_map]

snip end

determine answer : (Set.Ioi 1) → ℕ := fun n ↦ n * n - n + 1

problem imo2020_p4 (n : Set.Ioi 1) :
    IsLeast
      {k : ℕ | ∀ A B : Company n k, ∃ i j, A.linked i j ∧ B.linked i j}
      (answer n) := by
  have hn := Subtype.property n
  rw [Set.mem_Ioi] at hn
  rw [answer, IsLeast, lowerBounds]
  dsimp
  constructor
  · intro A B
    have hA := SimpleGraph.card_connectedComponent_add_card_edge_eq_card_vertex_of_acyclic A.graph_isAcyclic
    have hB := SimpleGraph.card_connectedComponent_add_card_edge_eq_card_vertex_of_acyclic B.graph_isAcyclic
    rw [Fintype.card_fin, A.graph_edgeFinset_card] at hA
    rw [Fintype.card_fin, B.graph_edgeFinset_card] at hB
    apply Nat.eq_sub_of_add_eq at hA
    apply Nat.eq_sub_of_add_eq at hB
    simp only [pow_two] at hA hB
    rw [← Nat.sub_sub, Nat.sub_sub_self (Nat.le_mul_self _)] at hA hB
    have h₁' :  Fintype.card A.graph.ConnectedComponent * n < Fintype.card (Fin (n ^ 2)) := by
      rw [Fintype.card_fin, hA, pow_two]
      rw [Nat.mul_lt_mul_right (by lia)]
      lia
    haveI : DecidableEq A.graph.ConnectedComponent := by
      intro a b
      use Classical.propDecidable _
    have h₁ := Fintype.exists_lt_card_fiber_of_mul_lt_card (fun v : Fin (n ^ 2) ↦ A.graph.connectedComponentMk v) h₁'
    rcases h₁ with ⟨CC_A, hCC_A⟩
    dsimp at hCC_A
    have h₂' : Fintype.card B.graph.ConnectedComponent < Fintype.card ({x | A.graph.connectedComponentMk x = CC_A} : Finset _) := by
      rw [Fintype.card_coe]
      lia
    have h₂ := Fintype.exists_ne_map_eq_of_card_lt (fun v : ({x | A.graph.connectedComponentMk x = CC_A} : Finset _) ↦ B.graph.connectedComponentMk v) h₂'
    rcases h₂ with ⟨x, y, hxy₁, hxy₂⟩
    dsimp at hxy₂
    have hx := Subtype.property x
    have hy := Subtype.property y
    rw [Finset.mem_filter] at hx hy
    have hxyA : A.graph.Reachable x y := by
      rw [← SimpleGraph.ConnectedComponent.eq, hx.right, hy.right]
    have hxyB : B.graph.Reachable x y := by
      rw [← SimpleGraph.ConnectedComponent.eq]
      exact hxy₂
    by_cases! hxy₃ : x < y
    · rw [Subtype.mk_lt_mk] at hxy₃
      use x
      use y
      constructor
      · apply Company.linked_of_graph_reachable hxyA hxy₃
      · apply Company.linked_of_graph_reachable hxyB hxy₃
    · have hxy₃' : y < x := lt_of_le_of_ne hxy₃ hxy₁.symm
      rw [Subtype.mk_lt_mk] at hxy₃'
      rw [SimpleGraph.reachable_comm] at hxyA hxyB
      use y
      use x
      constructor
      · apply Company.linked_of_graph_reachable hxyA hxy₃'
      · apply Company.linked_of_graph_reachable hxyB hxy₃'
  · intro a ha
    contrapose! +distrib ha
    rw [Nat.lt_succ_iff] at ha
    use (constructCompanyA n).subCompany ha
    use (constructCompanyB n).subCompany ha
    intro x y
    by_contra! h
    rcases h with ⟨hA, hB⟩
    apply Company.linked_of_subCompany_linked at hA
    apply Company.linked_of_subCompany_linked at hB
    have h := Company.lt_of_linked hA
    contrapose! h
    apply le_of_eq
    rw [← Fin.cast_inj (aux_pow n).symm]
    rw [← Fin.divNat_mkDivMod_modNat (Fin.cast _ x), ← Fin.divNat_mkDivMod_modNat (Fin.cast _ y)]
    rw [cast_modNat_eq_of_linked_constructCompanyA hA]
    rw [cast_divNat_eq_of_linked_constructCompanyB hB]

end Imo2020P4
