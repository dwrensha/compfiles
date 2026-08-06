/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Combinatorics.SimpleGraph.Girth
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Combinatorics]
}

/-!
# International Mathematical Olympiad 2019, Problem 3

A social network has 2019 users, some pairs of which are friends (friendship is
symmetric). If A, B, C are three users such that AB are friends and AC are friends
but BC is not, then the administrator may perform the following operation: change
the friendships such that BC are friends, but AB and AC are no longer friends.
Initially, 1009 users have 1010 friends and 1010 users have 1009 friends. Prove
that the administrator can make a sequence of operations such that all users have
at most 1 friend.
-/

namespace Imo2019P3

open SimpleGraph Finset

attribute [local instance] Classical.propDecidable

attribute [-instance] SimpleGraph.Sup.adjDecidable SimpleGraph.Inf.adjDecidable
  SimpleGraph.Sdiff.adjDecidable SimpleGraph.Bot.adjDecidable
  SimpleGraph.Top.adjDecidable SimpleGraph.Compl.adjDecidable
  SimpleGraph.fintypeEdgeSetSup SimpleGraph.fintypeEdgeSetInf
  SimpleGraph.fintypeEdgeSetSdiff SimpleGraph.fintypeEdgeSetBot

/-- The operation of the problem: if `a` is friends with both `b` and `c`, but `b` and
`c` are not friends, then the friendships `ab` and `ac` are deleted and the friendship
`bc` is created.  `Toggle G G'` says that `G'` is obtained from `G` by one such
operation. -/
def Toggle {V : Type*} (G G' : SimpleGraph V) : Prop :=
  ∃ a b c : V, b ≠ c ∧ G.Adj a b ∧ G.Adj a c ∧ ¬ G.Adj b c ∧
    G' = (G.deleteEdges {s(a, b), s(a, c)}) ⊔ fromEdgeSet {s(b, c)}

snip begin

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- Adjacency in a toggled graph. -/
lemma toggle_adj {G : SimpleGraph V} {a b c x y : V} :
    ((G.deleteEdges {s(a, b), s(a, c)}) ⊔ fromEdgeSet {s(b, c)}).Adj x y ↔
      (G.Adj x y ∧ s(x, y) ≠ s(a, b) ∧ s(x, y) ≠ s(a, c)) ∨ (s(x, y) = s(b, c) ∧ x ≠ y) := by
  rw [sup_adj, deleteEdges_adj, fromEdgeSet_adj]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]

omit [Fintype V] [DecidableEq V] in
/-- A helper for `Sym2` inequality: to show `s(x, y) ≠ s(z, w)` it suffices to
discharge both pairings. -/
lemma sym2_ne {x y z w : V} (h1 : x ≠ z ∨ y ≠ w) (h2 : x ≠ w ∨ y ≠ z) :
    s(x, y) ≠ s(z, w) := by
  intro heq
  rw [Sym2.eq_iff] at heq
  rcases heq with (⟨hxz, hyw⟩ | ⟨hxw, hyz⟩)
  · exact h1.elim (fun g => g hxz) (fun g => g hyw)
  · exact h2.elim (fun g => g hxw) (fun g => g hyz)

omit [Fintype V] [DecidableEq V] in
/-- Adjacency with `a` in a toggled graph: `a` keeps exactly its neighbors
different from `b` and `c`. -/
lemma toggle_adj_a {G : SimpleGraph V} {a b c : V}
    (hab : G.Adj a b) (hac : G.Adj a c) (w : V) :
    ((G.deleteEdges {s(a, b), s(a, c)}) ⊔ fromEdgeSet {s(b, c)}).Adj a w ↔
      G.Adj a w ∧ w ≠ b ∧ w ≠ c := by
  have hab' : a ≠ b := G.ne_of_adj hab
  have hac' : a ≠ c := G.ne_of_adj hac
  rw [toggle_adj]
  constructor
  · intro h
    rcases h with h | h
    · obtain ⟨hadj, h1, h2⟩ := h
      exact ⟨hadj, fun hwb => h1 (by rw [hwb]), fun hwc => h2 (by rw [hwc])⟩
    · obtain ⟨h1, -⟩ := h
      rw [Sym2.eq_iff] at h1
      rcases h1 with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact absurd h1 hab'
      · exact absurd h1 hac'
  · intro h
    obtain ⟨hadj, hwb, hwc⟩ := h
    exact Or.inl ⟨hadj, sym2_ne (Or.inr hwb) (Or.inl hab'),
      sym2_ne (Or.inr hwc) (Or.inl hac')⟩

omit [Fintype V] [DecidableEq V] in
/-- Adjacency with `b` in a toggled graph: `b` loses `a` and gains `c`. -/
lemma toggle_adj_b {G : SimpleGraph V} {a b c : V} (hbc : b ≠ c)
    (hab : G.Adj a b) (w : V) :
    ((G.deleteEdges {s(a, b), s(a, c)}) ⊔ fromEdgeSet {s(b, c)}).Adj b w ↔
      (w = c ∨ (G.Adj b w ∧ w ≠ a)) := by
  have hab' : a ≠ b := G.ne_of_adj hab
  rw [toggle_adj]
  constructor
  · intro h
    rcases h with h | h
    · obtain ⟨hadj, h1, -⟩ := h
      exact Or.inr ⟨hadj, fun hwa => h1 (hwa ▸ Sym2.eq_swap)⟩
    · obtain ⟨h1, -⟩ := h
      rw [Sym2.eq_iff] at h1
      rcases h1 with ⟨-, rfl⟩ | ⟨h1, -⟩
      · exact Or.inl rfl
      · exact absurd h1 hbc
  · intro h
    rcases h with rfl | h
    · exact Or.inr ⟨rfl, hbc⟩
    · obtain ⟨hadj, hwa⟩ := h
      exact Or.inl ⟨hadj, sym2_ne (Or.inl hab'.symm) (Or.inr hwa),
        sym2_ne (Or.inl hab'.symm) (Or.inl hbc)⟩

omit [Fintype V] [DecidableEq V] in
/-- Adjacency with `c` in a toggled graph: `c` loses `a` and gains `b`. -/
lemma toggle_adj_c {G : SimpleGraph V} {a b c : V} (hbc : b ≠ c)
    (hac : G.Adj a c) (w : V) :
    ((G.deleteEdges {s(a, b), s(a, c)}) ⊔ fromEdgeSet {s(b, c)}).Adj c w ↔
      (w = b ∨ (G.Adj c w ∧ w ≠ a)) := by
  have hac' : a ≠ c := G.ne_of_adj hac
  rw [toggle_adj]
  constructor
  · intro h
    rcases h with h | h
    · obtain ⟨hadj, -, h2⟩ := h
      exact Or.inr ⟨hadj, fun hwa => h2 (hwa ▸ Sym2.eq_swap)⟩
    · obtain ⟨h1, -⟩ := h
      rw [Sym2.eq_iff] at h1
      rcases h1 with ⟨h1, rfl⟩ | ⟨-, rfl⟩
      · exact absurd h1 hbc.symm
      · exact Or.inl rfl
  · intro h
    rcases h with rfl | h
    · exact Or.inr ⟨Sym2.eq_swap, hbc.symm⟩
    · obtain ⟨hadj, hwa⟩ := h
      exact Or.inl ⟨hadj, sym2_ne (Or.inl hac'.symm) (Or.inl hbc.symm),
        sym2_ne (Or.inl hac'.symm) (Or.inr hwa)⟩

omit [Fintype V] [DecidableEq V] in
/-- Adjacency with a vertex different from `a`, `b`, `c` is unchanged by a toggle. -/
lemma toggle_adj_of_ne {G : SimpleGraph V} {a b c v : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hvc : v ≠ c) (w : V) :
    ((G.deleteEdges {s(a, b), s(a, c)}) ⊔ fromEdgeSet {s(b, c)}).Adj v w ↔ G.Adj v w := by
  rw [toggle_adj]
  constructor
  · intro h
    rcases h with h | h
    · obtain ⟨hadj, -, -⟩ := h
      exact hadj
    · obtain ⟨h1, -⟩ := h
      rw [Sym2.eq_iff] at h1
      rcases h1 with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact absurd h1 hvb
      · exact absurd h1 hvc
  · intro hadj
    exact Or.inl ⟨hadj, sym2_ne (Or.inl hva) (Or.inl hvb),
      sym2_ne (Or.inl hva) (Or.inl hvc)⟩

omit [DecidableEq V] in
/-- Degree as the cardinality of a filter.  Stated with an explicit decidability
instance so that all synthesized instances agree. -/
lemma degree_eq_card_filter (H : SimpleGraph V) [DecidableRel H.Adj] (v : V) :
    H.degree v = #(Finset.univ.filter (H.Adj v)) := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree H v, SimpleGraph.neighborFinset_eq_filter H]

/-- A toggle preserves the parity of every degree. -/
lemma Toggle.degree_parity {G G' : SimpleGraph V} (hT : Toggle G G') (v : V) :
    G'.degree v % 2 = G.degree v % 2 := by
  obtain ⟨a, b, c, hbc, hab, hac, hnbc, rfl⟩ := hT
  have key : ∀ v : V,
      #(Finset.univ.filter
        ((G.deleteEdges {s(a, b), s(a, c)} ⊔ fromEdgeSet {s(b, c)}).Adj v)) % 2
        = #(Finset.univ.filter (G.Adj v)) % 2 := by
    intro v
    by_cases hva : v = a
    · rw [hva]
      have hN : Finset.univ.filter
            ((G.deleteEdges {s(a, b), s(a, c)} ⊔ fromEdgeSet {s(b, c)}).Adj a)
          = ((Finset.univ.filter (G.Adj a)).erase b).erase c := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, toggle_adj_a hab hac,
          Finset.mem_erase]
        tauto
      have hb_mem : b ∈ Finset.univ.filter (G.Adj a) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ b, hab⟩
      have hc_mem : c ∈ Finset.univ.filter (G.Adj a) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ c, hac⟩
      have h2 : 2 ≤ (Finset.univ.filter (G.Adj a)).card :=
        Finset.one_lt_card_iff.mpr ⟨b, c, hb_mem, hc_mem, hbc⟩
      rw [hN, Finset.card_erase_of_mem (show c ∈ (Finset.univ.filter (G.Adj a)).erase b by
          simp [Finset.mem_erase, hbc.symm, hc_mem]),
        Finset.card_erase_of_mem hb_mem]
      omega
    · by_cases hvb : v = b
      · rw [hvb]
        have hN : Finset.univ.filter
              ((G.deleteEdges {s(a, b), s(a, c)} ⊔ fromEdgeSet {s(b, c)}).Adj b)
            = insert c ((Finset.univ.filter (G.Adj b)).erase a) := by
          ext w
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, toggle_adj_b hbc hab,
            Finset.mem_insert, Finset.mem_erase]
          tauto
        have ha_mem : a ∈ Finset.univ.filter (G.Adj b) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ a, hab.symm⟩
        have hpos : 0 < (Finset.univ.filter (G.Adj b)).card :=
          Finset.card_pos.mpr ⟨a, ha_mem⟩
        rw [hN, Finset.card_insert_of_notMem (by
            simp [Finset.mem_erase, Finset.mem_filter, hnbc]),
          Finset.card_erase_of_mem ha_mem]
        omega
      · by_cases hvc : v = c
        · rw [hvc]
          have hN : Finset.univ.filter
                ((G.deleteEdges {s(a, b), s(a, c)} ⊔ fromEdgeSet {s(b, c)}).Adj c)
              = insert b ((Finset.univ.filter (G.Adj c)).erase a) := by
            ext w
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, toggle_adj_c hbc hac,
              Finset.mem_insert, Finset.mem_erase]
            tauto
          have ha_mem : a ∈ Finset.univ.filter (G.Adj c) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ a, hac.symm⟩
          have hpos : 0 < (Finset.univ.filter (G.Adj c)).card :=
            Finset.card_pos.mpr ⟨a, ha_mem⟩
          rw [hN, Finset.card_insert_of_notMem (by
              simp [Finset.mem_erase, Finset.mem_filter, show ¬ G.Adj c b from fun h => hnbc h.symm]),
            Finset.card_erase_of_mem ha_mem]
          omega
        · have hN : Finset.univ.filter
                ((G.deleteEdges {s(a, b), s(a, c)} ⊔ fromEdgeSet {s(b, c)}).Adj v)
              = Finset.univ.filter (G.Adj v) := by
            ext w
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, toggle_adj_of_ne hva hvb hvc]
          rw [hN]
  rw [degree_eq_card_filter, degree_eq_card_filter]
  exact key v

/-- A toggle preserves the existence of a vertex of odd degree. -/
lemma Toggle.exists_odd_degree {G G' : SimpleGraph V} (hT : Toggle G G') :
    (∃ v, Odd (G.degree v)) → ∃ v, Odd (G'.degree v) := by
  rintro ⟨v, hv⟩
  exact ⟨v, by rwa [Nat.odd_iff, hT.degree_parity v, ← Nat.odd_iff]⟩

omit [Fintype V] [DecidableEq V] in
/-- The edge set of a toggled graph. -/
lemma edgeSet_toggle {G : SimpleGraph V} {a b c : V} (hbc : b ≠ c) :
    ((G.deleteEdges {s(a, b), s(a, c)}) ⊔ fromEdgeSet {s(b, c)}).edgeSet
      = (G.edgeSet \ {s(a, b), s(a, c)}) ∪ {s(b, c)} := by
  rw [edgeSet_sup, edgeSet_deleteEdges, edgeSet_fromEdgeSet]
  ext e
  simp only [Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_insert_iff]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, -⟩)
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr h1
  · rintro (⟨h1, h2⟩ | h1)
    · exact Or.inl ⟨h1, h2⟩
    · subst h1
      exact Or.inr ⟨rfl, by simp [Sym2.diagSet, Sym2.mk_isDiag_iff, hbc]⟩

omit [DecidableEq V] in
/-- A toggle removes exactly one edge. -/
lemma Toggle.edgeFinset_card {G G' : SimpleGraph V} (hT : Toggle G G') :
    G'.edgeFinset.card + 1 = G.edgeFinset.card := by
  obtain ⟨a, b, c, hbc, hab, hac, hnbc, rfl⟩ := hT
  have conv : ∀ H : SimpleGraph V, H.edgeFinset.card = H.edgeSet.ncard := fun H =>
    (Set.ncard_eq_toFinset_card' H.edgeSet).symm
  rw [conv, conv, edgeSet_toggle hbc]
  have h1 : s(a, b) ∈ G.edgeSet := (mem_edgeSet _).mpr hab
  have h2 : s(a, c) ∈ G.edgeSet := (mem_edgeSet _).mpr hac
  have h12 : s(a, b) ≠ s(a, c) := sym2_ne (Or.inr hbc) (Or.inl (G.ne_of_adj hac))
  have h3 : s(b, c) ∉ G.edgeSet := fun h => hnbc ((mem_edgeSet _).mp h)
  have hsub : ({s(a, b), s(a, c)} : Set (Sym2 V)) ⊆ G.edgeSet := by
    intro e he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl <;> assumption
  rw [Set.ncard_union_eq (by
      rw [Set.disjoint_left]
      rintro e ⟨he, -⟩ heq
      rw [Set.mem_singleton_iff] at heq
      exact h3 (heq ▸ he)),
    Set.ncard_singleton, Set.ncard_sdiff hsub, Set.ncard_pair h12]
  have hcard2 : 2 ≤ G.edgeSet.ncard := by
    have hle := Set.ncard_le_ncard hsub
    rwa [Set.ncard_pair h12] at hle
  omega

omit [Fintype V] [DecidableEq V] in
/-- A graph obtained by a toggle is never complete: `a` and `b` are no longer friends. -/
lemma Toggle.ne_top {G G' : SimpleGraph V} (hT : Toggle G G') : G' ≠ ⊤ := by
  obtain ⟨a, b, c, hbc, hab, hac, hnbc, rfl⟩ := hT
  intro hG'
  have hadj : ((G.deleteEdges {s(a, b), s(a, c)}) ⊔ fromEdgeSet {s(b, c)}).Adj a b := by
    rw [hG']
    exact (top_adj _ _).mpr (G.ne_of_adj hab)
  rw [toggle_adj_a hab hac] at hadj
  exact hadj.2.1 rfl

omit [Fintype V] [DecidableEq V] in
/-- Lifting reachability along adjacencies that remain reachable. -/
lemma reachable_of_forall_adj_reachable {G H : SimpleGraph V} (a : V)
    (hlift : ∀ x y : V, G.Adj x y → H.Reachable x y) :
    ∀ x : V, G.Reachable x a → H.Reachable x a := by
  intro x h
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact ⟨Walk.nil⟩
  | cons hxy p ih => exact (hlift _ _ hxy).trans ih

omit [Fintype V] in
/-- If the endpoints `a, c` of the deleted edges of a toggle remain reachable in the
twice-deleted graph, then the toggle preserves connectedness. -/
lemma connected_toggle {G : SimpleGraph V} {a b c : V} (hbc : b ≠ c)
    (hconn : G.Connected)
    (hr : (G.deleteEdges {s(a, b), s(a, c)}).Reachable a c) :
    ((G.deleteEdges {s(a, b), s(a, c)}) ⊔ fromEdgeSet {s(b, c)}).Connected := by
  have hr' : ((G.deleteEdges {s(a, b), s(a, c)}) ⊔ fromEdgeSet {s(b, c)}).Reachable a c :=
    hr.mono le_sup_left
  have hbc' : ((G.deleteEdges {s(a, b), s(a, c)}) ⊔ fromEdgeSet {s(b, c)}).Adj b c :=
    (sup_adj _ _ _ _).mpr (Or.inr ((fromEdgeSet_adj _).mpr ⟨Set.mem_singleton _, hbc⟩))
  have hab' : ((G.deleteEdges {s(a, b), s(a, c)}) ⊔ fromEdgeSet {s(b, c)}).Reachable a b :=
    hr'.trans hbc'.reachable.symm
  have lift : ∀ x y : V, G.Adj x y →
      ((G.deleteEdges {s(a, b), s(a, c)}) ⊔ fromEdgeSet {s(b, c)}).Reachable x y := by
    intro x y hxy
    by_cases h1 : s(x, y) = s(a, b)
    · rw [Sym2.eq_iff] at h1
      rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hab'
      · exact hab'.symm
    · by_cases h2 : s(x, y) = s(a, c)
      · rw [Sym2.eq_iff] at h2
        rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hr'
        · exact hr'.symm
      · exact ((sup_adj _ _ _ _).mpr (Or.inl (deleteEdges_adj.mpr
          ⟨hxy, by simp [Set.mem_insert_iff, Set.mem_singleton_iff, h1, h2]⟩))).reachable
  have base : ∀ x : V, ((G.deleteEdges {s(a, b), s(a, c)}) ⊔ fromEdgeSet {s(b, c)}).Reachable
      x a := fun x =>
    reachable_of_forall_adj_reachable a lift x (hconn.preconnected x a)
  exact (connected_iff_exists_forall_reachable _).mpr ⟨a, fun w => (base w).symm⟩

omit [Fintype V] [DecidableEq V] in
/-- A walk from outside a set `S` to inside `S` crosses the boundary of `S`. -/
lemma exists_adj_crossing {G : SimpleGraph V} (S : Set V) {u v : V} (p : G.Walk u v) :
    u ∉ S → v ∈ S → ∃ b a : V, b ∉ S ∧ a ∈ S ∧ G.Adj b a := by
  induction p with
  | nil => intro hu hv; exact absurd hv hu
  | @cons u' w' v' hxy p ih =>
    intro hu hv
    by_cases hw : w' ∈ S
    · exact ⟨u', w', hu, hw, hxy⟩
    · exact ih hw hv

omit [Fintype V] [DecidableEq V] in
/-- IsPath is preserved by `Walk.transfer`. -/
lemma isPath_transfer {G H : SimpleGraph V} {u v : V} {p : G.Walk u v}
    (hp : ∀ e, e ∈ p.edges → e ∈ H.edgeSet) :
    (p.transfer H hp).IsPath ↔ p.IsPath := by
  rw [Walk.isPath_def, Walk.isPath_def, Walk.support_transfer]

omit [Fintype V] [DecidableEq V] in
/-- IsCycle is preserved by `Walk.transfer`. -/
lemma isCycle_transfer {G H : SimpleGraph V} {u : V} {p : G.Walk u u}
    (hp : ∀ e, e ∈ p.edges → e ∈ H.edgeSet) :
    (p.transfer H hp).IsCycle ↔ p.IsCycle := by
  have hnil : p.transfer H hp = Walk.nil ↔ p = Walk.nil := by
    rw [Walk.eq_nil_iff_nil, Walk.eq_nil_iff_nil, ← Walk.length_eq_zero_iff,
      ← Walk.length_eq_zero_iff, Walk.length_transfer]
  rw [Walk.isCycle_def, Walk.isCycle_def, Walk.isTrail_def, Walk.isTrail_def,
    Walk.edges_transfer, Walk.support_transfer, ne_eq, ne_eq, hnil]

omit [Fintype V] in
/-- Taking a cycle at `x` until a different vertex `y` gives a path. -/
lemma isPath_takeUntil_of_isCycle {G : SimpleGraph V} {x : V} {C : G.Walk x x} (hC : C.IsCycle)
    {y : V} (hy : y ∈ C.support) (hxy : y ≠ x) :
    (C.takeUntil y hy).IsPath := by
  rw [Walk.isPath_def]
  have hspec := congr_arg Walk.support (C.take_spec hy)
  rw [Walk.support_append] at hspec
  have hT : (C.dropUntil y hy).support.tail ≠ [] := by
    have hnn : ¬ (C.dropUntil y hy).Nil := Walk.not_nil_of_ne hxy
    have hlen := (C.dropUntil y hy).length_support
    have hlen' : (C.dropUntil y hy).length ≠ 0 :=
      fun hz => hnn (Walk.length_eq_zero_iff.mp hz)
    intro ht
    have h1 := congr_arg List.length ht
    rw [List.length_tail, List.length_nil] at h1
    omega
  have hdrop : C.support.dropLast =
      (C.takeUntil y hy).support ++ (C.dropUntil y hy).support.tail.dropLast := by
    conv_lhs => rw [← hspec]
    rw [List.dropLast_append_of_ne_nil hT]
  have hpre : (C.takeUntil y hy).support <+: C.support.dropLast :=
    ⟨(C.dropUntil y hy).support.tail.dropLast, hdrop.symm⟩
  exact (hC.nodup_dropLast_support).sublist hpre.sublist

omit [Fintype V] [DecidableEq V] in
/-- If the second vertex of a cycle `C` at `x` is `y`, then deleting the first edge
leaves a path from `x` to `y` avoiding it. -/
lemma exists_isPath_of_snd_eq {G : SimpleGraph V} {x y : V} {C : G.Walk x x}
    (hC : C.IsCycle) (hy : C.snd = y) :
    ∃ q : G.Walk x y, q.IsPath ∧ s(x, y) ∉ q.edges ∧ ∀ e ∈ q.edges, e ∈ C.edges := by
  subst hy
  have hnnil : ¬ C.Nil := hC.not_nil
  obtain ⟨hp_path, hp_edge⟩ :=
    (Walk.cons_isCycle_iff _ _).mp ((Walk.cons_tail_eq C hnnil).symm ▸ hC)
  refine ⟨C.tail.reverse, hp_path.reverse, ?_, ?_⟩
  · rw [Walk.edges_reverse, List.mem_reverse]
    exact hp_edge
  · intro e he
    rw [Walk.edges_reverse, List.mem_reverse] at he
    rw [← Walk.cons_tail_eq C hnnil, Walk.edges_cons]
    exact List.mem_cons_of_mem _ he

omit [Fintype V] in
/-- Removing an edge from a cycle leaves a path between its endpoints,
avoiding that edge. -/
lemma exists_isPath_of_mem_edges_of_isCycle {G : SimpleGraph V} {v : V} {C : G.Walk v v}
    (hC : C.IsCycle) {x y : V} (he : s(x, y) ∈ C.edges) (_hxy : x ≠ y) :
    ∃ q : G.Walk x y, q.IsPath ∧ s(x, y) ∉ q.edges ∧ ∀ e ∈ q.edges, e ∈ C.edges := by
  have hx : x ∈ C.support := C.fst_mem_support_of_mem_edges he
  have hγ₁ : (C.rotate x hx).IsCycle := hC.rotate hx
  have he₁ : s(x, y) ∈ (C.rotate x hx).edges := (C.rotate_edges x hx).perm.mem_iff.mpr he
  have hsub : ∀ e ∈ (C.rotate x hx).edges, e ∈ C.edges :=
    fun e he => (C.rotate_edges x hx).perm.mem_iff.mp he
  have hnnil : ¬ (C.rotate x hx).Nil := hγ₁.not_nil
  have hedges : (C.rotate x hx).edges
      = s(x, (C.rotate x hx).snd) :: (C.rotate x hx).tail.edges := by
    conv_lhs => rw [← Walk.cons_tail_eq _ hnnil]
    rw [Walk.edges_cons]
  rw [hedges, List.mem_cons] at he₁
  rcases he₁ with he₁ | he₁
  · have hy : (C.rotate x hx).snd = y := by
      rw [Sym2.eq_iff] at he₁
      rcases he₁ with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact h2.symm
      · exact absurd h1 (G.ne_of_adj (Walk.adj_snd hnnil))
    obtain ⟨q, hq1, hq2, hq3⟩ := exists_isPath_of_snd_eq hγ₁ hy
    exact ⟨q, hq1, hq2, fun e he => hsub e (hq3 e he)⟩
  · have htailpath : (C.rotate x hx).tail.IsPath := hγ₁.isPath_tail
    have hy : y = (C.rotate x hx).tail.penultimate :=
      htailpath.eq_penultimate_of_mem_edges he₁
    have hpn : ¬ (C.rotate x hx).tail.Nil :=
      Walk.not_nil_of_isCycle_cons ((Walk.cons_tail_eq _ hnnil).symm ▸ hγ₁)
    have hrev : (C.rotate x hx).reverse.IsCycle := hγ₁.reverse
    have hsnd : (C.rotate x hx).reverse.snd = y := by
      rw [Walk.snd_reverse]
      conv_lhs => rw [← Walk.cons_tail_eq _ hnnil]
      rw [Walk.penultimate_cons_of_not_nil _ _ hpn]
      exact hy.symm
    obtain ⟨q, hq1, hq2, hq3⟩ := exists_isPath_of_snd_eq hrev hsnd
    refine ⟨q, hq1, hq2, fun e he => hsub e ?_⟩
    have h1 := hq3 e he
    rw [Walk.edges_reverse, List.mem_reverse] at h1
    exact h1

omit [Fintype V] [DecidableEq V] in
/-- A length-1 walk from `x` to `y` contains the edge `s(x, y)`. -/
lemma mem_edges_of_length_eq_one {G : SimpleGraph V} {x y : V} {q : G.Walk x y}
    (hxy : x ≠ y) (hl : q.length = 1) : s(x, y) ∈ q.edges := by
  have hnnil : ¬ q.Nil := Walk.not_nil_of_ne hxy
  have htail : q.tail.length = 0 := by
    have h1 := Walk.length_tail_add_one hnnil
    omega
  have hsnd : q.snd = y := Walk.exists_length_eq_zero_iff.mp ⟨q.tail, htail⟩
  have h := q.mk_start_snd_mem_edges hnnil
  rwa [hsnd] at h

omit [Fintype V] in
/-- A cycle of length equal to the girth is chordless: every edge of `G` between two
vertices of the cycle is already an edge of the cycle. -/
lemma IsCycle.mem_edges_of_adj {G : SimpleGraph V} {v : V} {C : G.Walk v v}
    (hC : C.IsCycle) (hg : G.girth = C.length) {x y : V}
    (hx : x ∈ C.support) (hy : y ∈ C.support) (hxy : G.Adj x y) :
    s(x, y) ∈ C.edges := by
  by_contra hcontra
  have hxy' : x ≠ y := G.ne_of_adj hxy
  have hγ₁ : (C.rotate x hx).IsCycle := hC.rotate hx
  have hy₁ : y ∈ (C.rotate x hx).support := by
    rwa [Walk.mem_support_rotate_iff]
  have hpath := isPath_takeUntil_of_isCycle hγ₁ hy₁ hxy'.symm
  set q := (C.rotate x hx).takeUntil y hy₁ with hq
  set r := (C.rotate x hx).dropUntil y hy₁ with hr
  have hspec := (C.rotate x hx).take_spec hy₁
  have hlen : q.length + r.length = C.length := by
    have h1 := congr_arg Walk.length hspec
    rw [Walk.length_append, Walk.length_rotate] at h1
    exact h1
  have hq_edges : ∀ e ∈ q.edges, e ∈ C.edges := by
    intro e he
    have h2 := congr_arg Walk.edges hspec
    rw [Walk.edges_append] at h2
    have h3 : e ∈ (C.rotate x hx).edges := by
      rw [← h2]; exact List.mem_append_left _ he
    exact (C.rotate_edges x hx).perm.mem_iff.mp h3
  have hr_edges : ∀ e ∈ r.edges, e ∈ C.edges := by
    intro e he
    have h2 := congr_arg Walk.edges hspec
    rw [Walk.edges_append] at h2
    have h3 : e ∈ (C.rotate x hx).edges := by
      rw [← h2]; exact List.mem_append_right _ he
    exact (C.rotate_edges x hx).perm.mem_iff.mp h3
  have hq2 : 2 ≤ q.length := by
    rcases Nat.lt_or_ge q.length 2 with hlt | hge
    · have hq1 : q.length = 1 := by
        have hqne : q.length ≠ 0 :=
          fun hz => (Walk.not_nil_of_ne hxy') (Walk.length_eq_zero_iff.mp hz)
        omega
      exact absurd (hq_edges _ (mem_edges_of_length_eq_one hxy' hq1)) hcontra
    · exact hge
  have hr2 : 2 ≤ r.length := by
    rcases Nat.lt_or_ge r.length 2 with hlt | hge
    · have hr1 : r.length = 1 := by
        have hrne : r.length ≠ 0 :=
          fun hz => (Walk.not_nil_of_ne hxy'.symm) (Walk.length_eq_zero_iff.mp hz)
        omega
      exact absurd (hr_edges _ (Sym2.eq_swap ▸ mem_edges_of_length_eq_one hxy'.symm hr1))
        hcontra
    · exact hge
  have hnew : (Walk.cons hxy.symm q).IsCycle := by
    rw [Walk.cons_isCycle_iff]
    refine ⟨hpath, ?_⟩
    intro hmem
    exact hcontra (hq_edges _ (Sym2.eq_swap ▸ hmem))
  have hle := SimpleGraph.girth_le_length hnew
  rw [Walk.length_cons] at hle
  omega

/-- On a chordless cycle that spans all vertices, every vertex has degree `2`. -/
lemma degree_eq_two_of_forall_mem_support {G : SimpleGraph V} {v : V} {C : G.Walk v v}
    (hC : C.IsCycle)
    (hchord : ∀ x y : V, x ∈ C.support → y ∈ C.support → G.Adj x y → s(x, y) ∈ C.edges)
    (hspan : ∀ z : V, z ∈ C.support) (z : V) :
    G.degree z = 2 := by
  have hγ : (C.rotate z (hspan z)).IsCycle := hC.rotate (hspan z)
  have hnnil : ¬ (C.rotate z (hspan z)).Nil := hγ.not_nil
  have hchord' : ∀ x y : V, G.Adj x y → s(x, y) ∈ (C.rotate z (hspan z)).edges := by
    intro x y hxy
    exact (C.rotate_edges z (hspan z)).perm.mem_iff.mpr (hchord x y (hspan x) (hspan y) hxy)
  have hedges : (C.rotate z (hspan z)).edges
      = s(z, (C.rotate z (hspan z)).snd) :: (C.rotate z (hspan z)).tail.edges := by
    conv_lhs => rw [← Walk.cons_tail_eq _ hnnil]
    rw [Walk.edges_cons]
  have htailpath : (C.rotate z (hspan z)).tail.IsPath := hγ.isPath_tail
  have hpn : ¬ (C.rotate z (hspan z)).tail.Nil :=
    Walk.not_nil_of_isCycle_cons ((Walk.cons_tail_eq _ hnnil).symm ▸ hγ)
  have hp : (C.rotate z (hspan z)).penultimate = (C.rotate z (hspan z)).tail.penultimate := by
    conv_lhs => rw [← Walk.cons_tail_eq _ hnnil]
    exact Walk.penultimate_cons_of_not_nil _ _ hpn
  have hN : G.neighborFinset z
      = {(C.rotate z (hspan z)).snd, (C.rotate z (hspan z)).penultimate} := by
    ext w
    rw [mem_neighborFinset]
    constructor
    · intro hw
      have h1 := hchord' z w hw
      rw [hedges, List.mem_cons] at h1
      rcases h1 with h1 | h1
      · rw [Sym2.eq_iff] at h1
        rcases h1 with ⟨-, rfl⟩ | ⟨h2, -⟩
        · exact Finset.mem_insert_self _ _
        · exact absurd h2 (G.ne_of_adj (Walk.adj_snd hnnil))
      · have hw' := htailpath.eq_penultimate_of_mem_edges h1
        rw [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inr (by rw [hw', hp])
    · intro hw
      rw [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact Walk.adj_snd hnnil
      · exact (Walk.adj_of_mem_edges _
          ((C.rotate z (hspan z)).mk_penultimate_end_mem_edges hnnil)).symm
  rw [← SimpleGraph.card_neighborFinset_eq_degree G z, hN,
    Finset.card_pair hγ.snd_ne_penultimate]

omit [Fintype V] [DecidableEq V] in
/-- Three pairwise adjacent vertices form a cycle of length `3`. -/
lemma isCycle_triangle {G : SimpleGraph V} {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hca : G.Adj c a) :
    (Walk.cons hab (Walk.cons hbc (Walk.cons hca Walk.nil))).IsCycle
      ∧ (Walk.cons hab (Walk.cons hbc (Walk.cons hca Walk.nil))).length = 3 := by
  have hne1 : a ≠ b := G.ne_of_adj hab
  have hne2 : b ≠ c := G.ne_of_adj hbc
  have hne3 : c ≠ a := G.ne_of_adj hca
  constructor
  · apply (Walk.cons_isCycle_iff _ _).mpr
    constructor
    · rw [Walk.isPath_def]
      simp [Walk.support_cons, Walk.support_nil, hne2, hne3, hne1.symm]
    · simp only [Walk.edges_cons, Walk.edges_nil, List.mem_cons, List.not_mem_nil,
        or_false, Sym2.eq_iff]
      rintro ((⟨h1, -⟩ | ⟨h1, -⟩) | (⟨h1, -⟩ | ⟨-, h1⟩))
      · exact hne1 h1
      · exact hne3 h1.symm
      · exact hne3 h1.symm
      · exact hne2 h1
  · simp [Walk.length_cons, Walk.length_nil]

/-- If `G` has a vertex of odd degree, a girth-realizing cycle cannot span all vertices. -/
lemma exists_notMem_support_of_isCycle {G : SimpleGraph V} {v : V} {C : G.Walk v v}
    (hC : C.IsCycle) (hg : G.girth = C.length) (hodd : ∃ z, Odd (G.degree z)) :
    ∃ z, z ∉ C.support := by
  by_contra h
  push Not at h
  obtain ⟨z, hz⟩ := hodd
  have h2 := degree_eq_two_of_forall_mem_support hC
    (fun x y hx hy hxy => IsCycle.mem_edges_of_adj hC hg hx hy hxy) h z
  rw [h2] at hz
  exact (by decide : ¬ Odd 2) hz

/-- **Key claim**: a connected graph that is not a tree, has a vertex of odd degree,
and is not complete admits a toggle after which it is still connected. -/
lemma exists_toggle_connected (G : SimpleGraph V) (hconn : G.Connected) (htree : ¬ G.IsTree)
    (hodd : ∃ v, Odd (G.degree v)) (hne : G ≠ ⊤) :
    ∃ G', Toggle G G' ∧ G'.Connected := by
  have hacyc : ¬ G.IsAcyclic := fun hA => htree ⟨hconn, hA⟩
  obtain ⟨v₀, C, hC, hg⟩ := SimpleGraph.exists_girth_eq_length.mpr hacyc
  have h3 : 3 ≤ C.length := hC.three_le_length
  rcases Nat.lt_or_ge C.length 4 with hl | h4
  · -- `C` is a triangle: use a maximal clique.
    have hC3 : C.length = 3 := by omega
    -- decompose `C` into three edges
    have hnnil : ¬ C.Nil := hC.not_nil
    have h1 : C.tail.length = 2 := by
      have h := Walk.length_tail_add_one hnnil
      omega
    have hnnil2 : ¬ C.tail.Nil := by
      intro hnil
      have := Walk.length_eq_zero_iff.mpr hnil
      omega
    have h2 : C.tail.tail.length = 1 := by
      have h := Walk.length_tail_add_one hnnil2
      omega
    -- the three relevant vertices
    set x := C.snd with hx
    set y := C.tail.snd with hy
    have he1 : G.Adj v₀ x := Walk.adj_snd hnnil
    have he2 : G.Adj x y := Walk.adj_snd hnnil2
    have he3 : G.Adj y v₀ := by
      have h31 : C.tail.tail.tail.length = 0 := by
        have hnnil3 : ¬ C.tail.tail.Nil := by
          intro hnil
          have := Walk.length_eq_zero_iff.mpr hnil
          omega
        have h := Walk.length_tail_add_one hnnil3
        omega
      have hsnd : C.tail.tail.snd = v₀ := Walk.exists_length_eq_zero_iff.mp ⟨C.tail.tail.tail, h31⟩
      have h := C.tail.tail.adj_snd (by
        intro hnil
        have := Walk.length_eq_zero_iff.mpr hnil
        omega)
      rwa [hsnd] at h
    have hne1 : v₀ ≠ x := G.ne_of_adj he1
    have hne2 : x ≠ y := G.ne_of_adj he2
    have hne3 : y ≠ v₀ := G.ne_of_adj he3
    -- the triangle is a 3-clique
    have htri : G.IsClique ({v₀, x, y} : Finset V) := by
      rw [SimpleGraph.isClique_iff]
      intro a ha b hb hab'
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
      · exact absurd rfl hab'
      · exact he1
      · exact he3.symm
      · exact he1.symm
      · exact absurd rfl hab'
      · exact he2
      · exact he3
      · exact he2.symm
      · exact absurd rfl hab'
    have hcardtri : ({v₀, x, y} : Finset V).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hne1, hne3.symm]),
        Finset.card_pair hne2]
    -- pick a clique of maximal cardinality
    have hne_cliques : (Finset.univ.filter (fun K : Finset V => G.IsClique ↑K)).Nonempty :=
      ⟨{v₀, x, y}, Finset.mem_filter.mpr ⟨Finset.mem_univ _, htri⟩⟩
    obtain ⟨K, hK_mem, hK_max⟩ :=
      Finset.exists_max_image _ (fun K : Finset V => K.card) hne_cliques
    have hK_clique : G.IsClique ↑K := (Finset.mem_filter.mp hK_mem).2
    have hK3 : 3 ≤ K.card := by
      have h1 := hK_max _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, htri⟩)
      omega
    have hK_ne : K ≠ Finset.univ := by
      intro hKu
      apply hne
      rw [← SimpleGraph.isClique_univ]
      rw [hKu, Finset.coe_univ] at hK_clique
      exact hK_clique
    obtain ⟨z, hz⟩ : ∃ z, z ∉ K := by
      by_contra hzall
      push Not at hzall
      exact hK_ne (Finset.eq_univ_of_forall hzall)
    obtain ⟨k₀, hk₀⟩ : ∃ k₀, k₀ ∈ K :=
      Finset.card_pos.mp (by omega)
    obtain ⟨p⟩ := hconn.preconnected z k₀
    obtain ⟨b, a, hb, ha, hba⟩ := exists_adj_crossing (↑K) p hz hk₀
    obtain ⟨c, hcK, hbc'⟩ : ∃ c ∈ K, ¬ G.Adj b c := by
      by_contra hcc
      push Not at hcc
      have hcl : G.IsClique ↑(insert b K) := by
        rw [Finset.coe_insert, SimpleGraph.isClique_insert]
        exact ⟨hK_clique, fun c hc _ => hcc c hc⟩
      have hle := hK_max (insert b K) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcl⟩)
      rw [Finset.card_insert_of_notMem hb] at hle
      omega
    have hac' : a ≠ c := fun h => hbc' (h ▸ hba)
    obtain ⟨d, hdK, hd⟩ : ∃ d ∈ K, d ∉ ({a, c} : Finset V) := by
      by_contra hd'
      have hsub : K ⊆ {a, c} := fun x hx => by
        by_contra hx'
        exact hd' ⟨x, hx, hx'⟩
      have hcle := Finset.card_le_card hsub
      rw [Finset.card_pair hac'] at hcle
      omega
    rw [Finset.mem_insert, Finset.mem_singleton] at hd
    push Not at hd
    obtain ⟨hda, hdc⟩ := hd
    have hbc : b ≠ c := fun h => hb (h ▸ hcK)
    have hadj_ac : G.Adj a c := hK_clique ha hcK hac'
    have hab : G.Adj a b := hba.symm
    refine ⟨(G.deleteEdges {s(a, b), s(a, c)}) ⊔ fromEdgeSet {s(b, c)},
      ⟨a, b, c, hbc, hab, hadj_ac, hbc', rfl⟩,
      connected_toggle hbc hconn ?_⟩
    -- `a` and `c` stay connected through `d`
    have had : G.Adj a d := hK_clique ha hdK hda.symm
    have hdc' : G.Adj d c := hK_clique hdK hcK hdc
    have hdb : d ≠ b := fun h => hb (h ▸ hdK)
    have e1 : (G.deleteEdges {s(a, b), s(a, c)}).Adj a d :=
      deleteEdges_adj.mpr ⟨had, by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨sym2_ne (Or.inr hdb) (Or.inl (G.ne_of_adj hab)),
          sym2_ne (Or.inr hdc) (Or.inl hac')⟩⟩
    have e2 : (G.deleteEdges {s(a, b), s(a, c)}).Adj d c :=
      deleteEdges_adj.mpr ⟨hdc', by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨sym2_ne (Or.inl hda) (Or.inl hdb),
          sym2_ne (Or.inl hda) (Or.inl hdc)⟩⟩
    exact ⟨Walk.cons e1 (Walk.cons e2 Walk.nil)⟩
  · -- `C` has length at least 4: `G` is triangle-free, use the cycle directly.
    have htf : ∀ x y z : V, G.Adj x y → G.Adj y z → G.Adj z x → False := by
      intro x y z hxy hyz hzx
      obtain ⟨hc3, hlen3⟩ := isCycle_triangle hxy hyz hzx
      have hle := SimpleGraph.girth_le_length hc3
      rw [hlen3, hg] at hle
      omega
    obtain ⟨z₀, hz₀⟩ := exists_notMem_support_of_isCycle hC hg hodd
    obtain ⟨p⟩ := hconn.preconnected z₀ v₀
    obtain ⟨b, a, hb, ha, hba⟩ :=
      exists_adj_crossing {x | x ∈ C.support} p hz₀ (Walk.start_mem_support _)
    have hγ : (C.rotate a ha).IsCycle := hC.rotate ha
    have hnnil : ¬ (C.rotate a ha).Nil := hγ.not_nil
    set c := (C.rotate a ha).snd with hc
    have hac : G.Adj a c := Walk.adj_snd hnnil
    have hnbc : ¬ G.Adj b c := fun hbc' => htf a b c hba.symm hbc' hac.symm
    have hc_mem : c ∈ C.support := by
      have h1 := (C.rotate a ha).mk_start_snd_mem_edges hnnil
      have h2 := (C.rotate_edges a ha).perm.mem_iff.mp h1
      exact C.snd_mem_support_of_mem_edges h2
    have hbc : b ≠ c := fun h => hb (h ▸ hc_mem)
    refine ⟨(G.deleteEdges {s(a, b), s(a, c)}) ⊔ fromEdgeSet {s(b, c)},
      ⟨a, b, c, hbc, hba.symm, hac, hnbc, rfl⟩,
      connected_toggle hbc hconn ?_⟩
    -- the cycle minus the edge `ac` connects `a` and `c`, avoiding `ab` as well
    obtain ⟨q, hq_path, hq_edge, hq_sub⟩ := exists_isPath_of_snd_eq hγ rfl
    have hq_sub' : ∀ e ∈ q.edges, e ∈ C.edges :=
      fun e he => (C.rotate_edges a ha).perm.mem_iff.mp (hq_sub e he)
    have hq_avoid : ∀ e ∈ q.edges, e ∉ ({s(a, b), s(a, c)} : Set (Sym2 V)) := by
      intro e he
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      refine ⟨?_, ?_⟩
      · intro heq
        subst heq
        exact hb (C.snd_mem_support_of_mem_edges (hq_sub' _ he))
      · intro heq
        subst heq
        exact hq_edge he
    exact ⟨q.toDeleteEdges {s(a, b), s(a, c)} hq_avoid⟩

/-- **Phase 1**: any connected graph with a vertex of odd degree that is not complete
can be toggled to a tree. -/
lemma exists_isTree_of_connected (G : SimpleGraph V) (hconn : G.Connected)
    (hodd : ∃ v, Odd (G.degree v)) (hne : G ≠ ⊤) :
    ∃ G', Relation.ReflTransGen Toggle G G' ∧ G'.IsTree := by
  have aux : ∀ n : ℕ, ∀ G : SimpleGraph V, G.edgeFinset.card ≤ n → G.Connected →
      (∃ v, Odd (G.degree v)) → G ≠ ⊤ →
      ∃ G', Relation.ReflTransGen Toggle G G' ∧ G'.IsTree := by
    intro n
    induction n with
    | zero =>
      intro G hcard hconn hodd hne
      obtain ⟨v, hv⟩ := hodd
      have h0 : G.degree v = 0 := by
        have hle := G.degree_le_card_edgeFinset (v := v)
        omega
      rw [h0] at hv
      exact absurd hv (by decide)
    | succ n ih =>
      intro G hcard hconn hodd hne
      by_cases htree : G.IsTree
      · exact ⟨G, .refl, htree⟩
      · obtain ⟨G', hT, hconn'⟩ := exists_toggle_connected G hconn htree hodd hne
        have hcard' : G'.edgeFinset.card ≤ n := by
          have h := hT.edgeFinset_card
          omega
        obtain ⟨G'', hseq, htree''⟩ :=
          ih G' hcard' hconn' (hT.exists_odd_degree hodd) hT.ne_top
        exact ⟨G'', .head hT hseq, htree''⟩
  exact aux _ G (Nat.le_refl _) hconn hodd hne

omit [Fintype V] in
/-- Taking a path until a vertex gives a path. -/
lemma IsPath.takeUntil {G : SimpleGraph V} {u v : V} {p : G.Walk u v} (hp : p.IsPath)
    {w : V} (hw : w ∈ p.support) : (p.takeUntil w hw).IsPath := by
  rw [Walk.isPath_def] at hp ⊢
  have hspec := congr_arg Walk.support (p.take_spec hw)
  rw [Walk.support_append] at hspec
  have hpre : (p.takeUntil w hw).support <+: p.support :=
    ⟨(p.dropUntil w hw).support.tail, hspec⟩
  exact hp.sublist hpre.sublist

omit [Fintype V] in
/-- A toggle preserves acyclicity. -/
lemma isAcyclic_toggle {G G' : SimpleGraph V} (hT : Toggle G G') (hacyc : G.IsAcyclic) :
    G'.IsAcyclic := by
  obtain ⟨a, b, c, hbc, hab, hac, hnbc, rfl⟩ := hT
  intro v γ hγ
  by_cases hmem : s(b, c) ∈ γ.edges
  · -- `γ` uses the new edge `bc`: removing it gives a path from `b` to `c` in `G`
    obtain ⟨q, hq_path, hq_bc, hq_sub⟩ := exists_isPath_of_mem_edges_of_isCycle hγ hmem hbc
    have hqG : ∀ e ∈ q.edges, e ∈ G.edgeSet ∧ e ≠ s(a, b) ∧ e ≠ s(a, c) := by
      intro e he
      have h1 : e ∈ ((G.deleteEdges {s(a, b), s(a, c)}) ⊔ fromEdgeSet {s(b, c)}).edgeSet :=
        γ.edges_subset_edgeSet (hq_sub e he)
      rw [edgeSet_sup, edgeSet_deleteEdges, edgeSet_fromEdgeSet] at h1
      rcases h1 with ⟨h1, h2⟩ | ⟨h1, -⟩
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h2
        exact ⟨h1, h2.1, h2.2⟩
      · rw [Set.mem_singleton_iff] at h1
        exact absurd (h1 ▸ he) hq_bc
    have hqG' : ∀ e ∈ q.edges, e ∈ G.edgeSet := fun e he => (hqG e he).1
    have hqG_path : (q.transfer G hqG').IsPath := (isPath_transfer hqG').mpr hq_path
    by_cases ha_mem : a ∈ (q.transfer G hqG').support
    · -- the path from `b` to `a` along `q`, closed by the edge `ab`, is a cycle in `G`
      have hcycle : (Walk.cons hab.symm
          (((q.transfer G hqG').takeUntil a ha_mem).reverse)).IsCycle := by
        rw [Walk.cons_isCycle_iff]
        constructor
        · exact (IsPath.takeUntil hqG_path ha_mem).reverse
        · rw [Walk.edges_reverse, List.mem_reverse]
          intro hmem'
          have h1 : s(b, a) ∈ (q.transfer G hqG').edges := by
            have h2 := congr_arg Walk.edges ((q.transfer G hqG').take_spec ha_mem)
            rw [Walk.edges_append] at h2
            rw [← h2]
            exact List.mem_append_left _ hmem'
          rw [Walk.edges_transfer] at h1
          exact (hqG _ h1).2.1 Sym2.eq_swap
      exact hacyc _ hcycle
    · -- `b ~> c ~> a ~> b` is a cycle in `G`
      have hcycle : (Walk.cons hab.symm
          (Walk.cons hac (q.transfer G hqG').reverse)).IsCycle := by
        rw [Walk.cons_isCycle_iff]
        constructor
        · rw [Walk.cons_isPath_iff]
          refine ⟨hqG_path.reverse, ?_⟩
          rw [Walk.support_reverse, List.mem_reverse]
          exact ha_mem
        · -- s(b, a) ∉ (cons hac qG.reverse).edges
          rw [Walk.edges_cons, List.mem_cons, not_or]
          constructor
          · exact sym2_ne (Or.inl (G.ne_of_adj hab).symm) (Or.inl hbc)
          · rw [Walk.edges_reverse, List.mem_reverse, Walk.edges_transfer]
            intro hmem'
            exact (hqG _ hmem').2.1 Sym2.eq_swap
      exact hacyc _ hcycle
  · -- `γ` avoids the new edge `bc`: it is already a cycle in `G`
    have hsub : ∀ e ∈ γ.edges, e ∈ G.edgeSet := by
      intro e he
      have h1 : e ∈ ((G.deleteEdges {s(a, b), s(a, c)}) ⊔ fromEdgeSet {s(b, c)}).edgeSet :=
        γ.edges_subset_edgeSet he
      rw [edgeSet_sup, edgeSet_deleteEdges, edgeSet_fromEdgeSet] at h1
      rcases h1 with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact h1
      · rw [Set.mem_singleton_iff] at h1
        exact absurd (h1 ▸ he) hmem
    exact hacyc _ ((isCycle_transfer hsub).mpr hγ)

/-- **Phase 2**: any forest can be toggled to a graph in which every vertex has degree
at most `1`. -/
lemma exists_matching_of_isAcyclic (G : SimpleGraph V) (hacyc : G.IsAcyclic) :
    ∃ G', Relation.ReflTransGen Toggle G G' ∧ ∀ v, G'.degree v ≤ 1 := by
  have aux : ∀ n : ℕ, ∀ G : SimpleGraph V, G.edgeFinset.card ≤ n → G.IsAcyclic →
      ∃ G', Relation.ReflTransGen Toggle G G' ∧ ∀ v, G'.degree v ≤ 1 := by
    intro n
    induction n with
    | zero =>
      intro G hcard hacyc
      refine ⟨G, .refl, fun v => ?_⟩
      have hle := G.degree_le_card_edgeFinset (v := v)
      omega
    | succ n ih =>
      intro G hcard hacyc
      by_cases hmax : ∀ v, G.degree v ≤ 1
      · exact ⟨G, .refl, hmax⟩
      · simp only [not_forall, not_le] at hmax
        obtain ⟨a, ha⟩ := hmax
        rw [SimpleGraph.degree, Finset.one_lt_card_iff] at ha
        obtain ⟨b, c, hb, hc, hbc⟩ := ha
        rw [SimpleGraph.mem_neighborFinset] at hb hc
        have hnbc : ¬ G.Adj b c := by
          intro hbc'
          exact hacyc _ (isCycle_triangle hb hbc' hc.symm).1
        set G' := (G.deleteEdges {s(a, b), s(a, c)}) ⊔ fromEdgeSet {s(b, c)} with hG'
        have hT : Toggle G G' := ⟨a, b, c, hbc, hb, hc, hnbc, rfl⟩
        have hacyc' : G'.IsAcyclic := isAcyclic_toggle hT hacyc
        have hcard' : G'.edgeFinset.card ≤ n := by
          have h := hT.edgeFinset_card
          omega
        obtain ⟨G'', hseq, hmatch⟩ := ih G' hcard' hacyc'
        exact ⟨G'', .head hT hseq, hmatch⟩
  exact aux _ G (Nat.le_refl _) hacyc

snip end

problem imo2019_p3 (G : SimpleGraph (Fin 2019))
    (h1009 : (Finset.univ.filter (fun v => G.degree v = 1009)).card = 1010)
    (h1010 : (Finset.univ.filter (fun v => G.degree v = 1010)).card = 1009) :
    ∃ G' : SimpleGraph (Fin 2019), Relation.ReflTransGen Toggle G G' ∧
      ∀ v, G'.degree v ≤ 1 := by
  -- every vertex has degree `1009` or `1010`
  have hdeg : ∀ v : Fin 2019, G.degree v = 1009 ∨ G.degree v = 1010 := by
    intro v
    have hdisj : Disjoint (Finset.univ.filter (fun v => G.degree v = 1009))
        (Finset.univ.filter (fun v => G.degree v = 1010)) := by
      rw [Finset.disjoint_left]
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [Finset.mem_filter]
      rintro ⟨_, h⟩
      omega
    have hunion : Finset.univ.filter (fun v => G.degree v = 1009) ∪
        Finset.univ.filter (fun v => G.degree v = 1010) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Finset.card_union_of_disjoint hdisj, h1009, h1010, Fintype.card_fin]
    have hv : v ∈ Finset.univ.filter (fun v => G.degree v = 1009) ∪
        Finset.univ.filter (fun v => G.degree v = 1010) := by
      rw [hunion]; exact Finset.mem_univ v
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at hv
    rcases hv with ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inl h
    · exact Or.inr h
  have hdeg_le : ∀ v : Fin 2019, 1009 ≤ G.degree v := by
    intro v; rcases hdeg v with h | h <;> omega
  -- there is a vertex of odd degree
  obtain ⟨z, hz⟩ : ∃ z, Odd (G.degree z) := by
    have hne1009 : (Finset.univ.filter (fun v => G.degree v = 1009)).Nonempty :=
      Finset.card_pos.mp (by rw [h1009]; norm_num)
    obtain ⟨z, hz⟩ := hne1009
    rw [Finset.mem_filter] at hz
    exact ⟨z, hz.2 ▸ ⟨504, by norm_num⟩⟩
  -- `G` is not complete
  have hnetop : G ≠ ⊤ := by
    intro htop
    obtain ⟨z, hz'⟩ : ∃ z, G.degree z = 1009 := by
      have hne1009 : (Finset.univ.filter (fun v => G.degree v = 1009)).Nonempty :=
        Finset.card_pos.mp (by rw [h1009]; norm_num)
      obtain ⟨z, hz⟩ := hne1009
      exact ⟨z, (Finset.mem_filter.mp hz).2⟩
    have htopdeg : G.degree z = 2018 := by
      rw [htop, ← SimpleGraph.card_neighborFinset_eq_degree]
      have hN : (⊤ : SimpleGraph (Fin 2019)).neighborFinset z = Finset.univ.erase z := by
        ext w
        simp [mem_neighborFinset, SimpleGraph.top_adj, Finset.mem_erase, ne_comm]
      rw [hN, Finset.card_erase_of_mem (Finset.mem_univ z), Finset.card_univ,
        Fintype.card_fin]
    omega
  -- `G` is connected: any two non-adjacent vertices have a common neighbor
  have hconn : G.Connected := by
    rw [SimpleGraph.connected_iff]
    refine ⟨?_, ⟨0⟩⟩
    intro u v
    by_cases huv : u = v
    · subst huv
      exact ⟨Walk.nil⟩
    · by_cases hadj : G.Adj u v
      · exact hadj.reachable
      · have hsub : G.neighborFinset u ∪ G.neighborFinset v ⊆
            (Finset.univ.erase u).erase v := by
          intro x hx
          rw [Finset.mem_union, mem_neighborFinset, mem_neighborFinset] at hx
          simp only [Finset.mem_erase, Finset.mem_univ, and_true]
          rcases hx with h | h
          · exact ⟨fun hxv => hadj (hxv ▸ h), (G.ne_of_adj h).symm⟩
          · exact ⟨(G.ne_of_adj h).symm, fun hxu => hadj (hxu ▸ h.symm)⟩
        have hcard : ((Finset.univ.erase u).erase v).card = 2017 := by
          rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨fun h => huv h.symm, Finset.mem_univ v⟩),
            Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ, Fintype.card_fin]
        have hcu := Finset.card_union_add_card_inter (G.neighborFinset u)
          (G.neighborFinset v)
        have hle := Finset.card_le_card hsub
        rw [hcard] at hle
        have hu : 1009 ≤ (G.neighborFinset u).card := by
          rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hdeg_le u
        have hv : 1009 ≤ (G.neighborFinset v).card := by
          rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hdeg_le v
        have hpos : 0 < (G.neighborFinset u ∩ G.neighborFinset v).card := by
          omega
        obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
        rw [Finset.mem_inter, mem_neighborFinset, mem_neighborFinset] at hw
        exact ⟨Walk.cons hw.1 (Walk.cons hw.2.symm Walk.nil)⟩
  -- assemble the two phases
  obtain ⟨T, hGT, hTtree⟩ := exists_isTree_of_connected G hconn ⟨z, hz⟩ hnetop
  obtain ⟨M, hTM, hM⟩ := exists_matching_of_isAcyclic T hTtree.isAcyclic
  exact ⟨M, hGT.trans hTM, hM⟩

end Imo2019P3
