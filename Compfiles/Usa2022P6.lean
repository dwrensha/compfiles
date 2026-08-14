/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Combinatorics.SimpleGraph.Operations
public import Mathlib.Data.Set.Card
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2022, Problem 6

There are 2022 users on a social network called Mathbook, and some of them are
Mathbook-friends. (On Mathbook, friendship is always mutual and permanent.)
Starting now, Mathbook will only allow a new friendship to be formed between
two users if they have at least two friends in common. What is the minimum
number of friendships that must already exist so that every user could
eventually become friends with every other user?
-/

namespace Usa2022P6

snip begin

open SimpleGraph

variable {V : Type*} [DecidableEq V] [Fintype V]

/-! ### The reachability relation -/

/-- A new friendship may be formed between `u` and `v`: they are distinct, not yet
friends, and have at least two common friends. -/
structure CanAdd (G : SimpleGraph V) (u v : V) : Prop where
  ne : u ≠ v
  not_adj : ¬ G.Adj u v
  common : ∃ p q : V, p ≠ q ∧ G.Adj u p ∧ G.Adj v p ∧ G.Adj u q ∧ G.Adj v q

/-- `Reachable G H` means that the graph `H` can be obtained from `G` by a sequence
of legal moves (each adding one friendship between users with two common friends). -/
inductive Reachable : SimpleGraph V → SimpleGraph V → Prop
  | refl (G : SimpleGraph V) : Reachable G G
  | step {G H : SimpleGraph V} {u v : V} (h : Reachable G H) (hc : CanAdd H u v) :
      Reachable G (H ⊔ SimpleGraph.edge u v)

/-- The graph `G` can be completed so that every user becomes friends with every
other user. -/
def Completable (G : SimpleGraph V) : Prop := Reachable G ⊤

omit [DecidableEq V] [Fintype V] in
lemma reachable_trans {G H J : SimpleGraph V} (h₁ : Reachable G H) (h₂ : Reachable H J) :
    Reachable G J := by
  induction h₂ with
  | refl => exact h₁
  | step _ hc ih => exact ih.step hc

omit [DecidableEq V] [Fintype V] in
lemma reachable_le {G H : SimpleGraph V} (h : Reachable G H) : G ≤ H := by
  induction h with
  | refl => exact le_refl _
  | step _ _ ih => exact le_trans ih le_sup_left

omit [DecidableEq V] [Fintype V] in
lemma reachable_sup_left {G H : SimpleGraph V} (h : Reachable G H) (J : SimpleGraph V) :
    Reachable (J ⊔ G) (J ⊔ H) := by
  induction h with
  | refl => exact Reachable.refl _
  | step h hc ih =>
    rename_i H' u v
    by_cases hadj : (J ⊔ H').Adj u v
    · have hle : SimpleGraph.edge u v ≤ J ⊔ H' := (SimpleGraph.edge_le_iff ..).mpr (Or.inr hadj)
      rw [← sup_assoc, sup_eq_left.mpr hle]
      exact ih
    · have hc' : CanAdd (J ⊔ H') u v := by
        refine ⟨hc.ne, hadj, ?_⟩
        obtain ⟨p, q, hpq, hup, hvp, huq, hvq⟩ := hc.common
        exact ⟨p, q, hpq, Or.inr hup, Or.inr hvp, Or.inr huq, Or.inr hvq⟩
      rw [← sup_assoc]
      exact ih.step hc'

omit [DecidableEq V] [Fintype V] in
lemma completable_mono {G H : SimpleGraph V} (hle : G ≤ H) (h : Completable G) :
    Completable H := by
  have h2 := reachable_sup_left h H
  rw [sup_of_le_left hle, sup_of_le_right le_top] at h2
  exact h2

omit [DecidableEq V] [Fintype V] in
/-- If no legal move is possible from `G`, then any graph reachable from `G` is `G`
itself. -/
lemma reachable_eq_of_no_canAdd {G H : SimpleGraph V} (h : Reachable G H)
    (hno : ∀ u v : V, ¬ CanAdd G u v) : H = G := by
  induction h with
  | refl => rfl
  | step hr hc ih =>
    rename_i u v
    exact absurd (ih ▸ hc) (hno u v)

omit [DecidableEq V] [Fintype V] in
/-- Adding a single friendship between two users with two distinct common friends
is a legal move (or a no-op if they are already friends). -/
lemma reachable_add_edge_of_common {G : SimpleGraph V} {u v p q : V} (huv : u ≠ v)
    (hpq : p ≠ q) (hup : G.Adj u p) (hvp : G.Adj v p) (huq : G.Adj u q)
    (hvq : G.Adj v q) :
    Reachable G (G ⊔ SimpleGraph.edge u v) := by
  by_cases hadj : G.Adj u v
  · rw [sup_eq_left.mpr ((SimpleGraph.edge_le_iff ..).mpr (Or.inr hadj))]
    exact Reachable.refl G
  · exact (Reachable.refl G).step ⟨huv, hadj, p, q, hpq, hup, hvp, huq, hvq⟩

/-! ### The clique-cover argument -/

/-- The vertex set of an element of `Sym2 V`, as a `Finset`. -/
def Sym2.toFinsetV (e : Sym2 V) : Finset V :=
  Sym2.lift ⟨fun a b => {a, b}, fun a b => by ext x; simp [or_comm]⟩ e

omit [Fintype V] in
@[simp] lemma Sym2.toFinsetV_mk (a b : V) : Sym2.toFinsetV s(a, b) = {a, b} := rfl

omit [Fintype V] in
lemma Sym2.mem_toFinsetV {v : V} {e : Sym2 V} : v ∈ Sym2.toFinsetV e ↔ v ∈ e :=
  Sym2.inductionOn e (fun a b => by simp [Sym2.mem_iff])

omit [Fintype V] in
lemma Sym2.toFinsetV_eq {e : Sym2 V} {u v : V} (h : Sym2.toFinsetV e = {u, v})
    (huv : u ≠ v) : e = s(u, v) := by
  refine Sym2.inductionOn e ?_ h
  intro a b h
  rw [Sym2.toFinsetV_mk] at h
  have hu : u = a ∨ u = b := by
    have : u ∈ ({a, b} : Finset V) := h ▸ by simp
    simpa using this
  have hv : v = a ∨ v = b := by
    have : v ∈ ({a, b} : Finset V) := h ▸ by simp
    simpa using this
  have ha : a = u ∨ a = v := by
    have : a ∈ ({u, v} : Finset V) := h ▸ by simp
    simpa using this
  have hb : b = u ∨ b = v := by
    have : b ∈ ({u, v} : Finset V) := h ▸ by simp
    simpa using this
  rw [Sym2.eq_iff]
  rcases ha with hau | hav
  · have hbv : b = v := by
      rcases hb with hbu | hbv
      · exfalso
        rcases hv with hva | hvb
        · exact huv (hva.trans hau).symm
        · exact huv (hvb.trans hbu).symm
      · exact hbv
    exact Or.inl ⟨hau, hbv⟩
  · have hbu : b = u := by
      rcases hb with hbu | hbv
      · exact hbu
      · exfalso
        rcases hu with hua | hub
        · exact huv (hua.trans hav)
        · exact huv (hub.trans hbv)
    exact Or.inr ⟨hav, hbu⟩

/-- The complete graph on the finite set `S` of vertices, seen as a graph on `V`. -/
def completeOn (S : Finset V) : SimpleGraph V where
  Adj u w := u ∈ S ∧ w ∈ S ∧ u ≠ w
  symm := ⟨fun _u _w h => ⟨h.2.1, h.1, h.2.2.symm⟩⟩
  loopless := ⟨fun _u h => h.2.2 rfl⟩

/-- A *cover* of `G'` relative to the original graph `G`: a finite collection `C`
of cliques of `G'` together with a labeling `ℓ` assigning to every edge of `G'` a
clique containing its endpoints, such that every clique `K` "owns" at least
`3|K|/2 - 2` edges of the original graph `G` (this is the quantity `θ(K)` appearing
in `theta_bound`).  This is the data maintained by the clique-merging algorithm used
in the lower bound proof. -/
structure Cover (G G' : SimpleGraph V) [DecidableRel G.Adj] where
  C : Finset (Finset V)
  ℓ : Sym2 V → Finset V
  le : G ≤ G'
  clique : ∀ K ∈ C, ∀ u ∈ K, ∀ w ∈ K, u ≠ w → G'.Adj u w
  label_mem : ∀ e ∈ G'.edgeSet, ℓ e ∈ C
  label_sub : ∀ e ∈ G'.edgeSet, ∀ v ∈ e, v ∈ ℓ e
  theta_bound : ∀ K ∈ C,
    3 * K.card ≤ 2 * (G.edgeFinset.filter (fun e => ℓ e = K)).card + 4
  assigned : ∀ K ∈ C, ∃ e ∈ G'.edgeSet, ℓ e = K

/-- The initial cover of `G`: one `K₂` per edge. -/
def initialCover (G : SimpleGraph V) [DecidableRel G.Adj] : Cover G G where
  C := G.edgeFinset.image Sym2.toFinsetV
  ℓ := Sym2.toFinsetV
  le := le_refl G
  clique := by
    intro K hK u hu w hw huw
    simp only [Finset.mem_image, SimpleGraph.mem_edgeFinset] at hK
    obtain ⟨e, he, rfl⟩ := hK
    induction e using Sym2.ind with
    | h a b =>
      rw [Sym2.toFinsetV_mk, Finset.mem_insert, Finset.mem_singleton] at hu hw
      rw [SimpleGraph.mem_edgeSet] at he
      rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
      · exact absurd rfl huw
      · exact he
      · exact he.symm
      · exact absurd rfl huw
  label_mem := by
    intro e he
    simp only [Finset.mem_image, SimpleGraph.mem_edgeFinset]
    exact ⟨e, he, rfl⟩
  label_sub := by
    intro e he v hv
    exact Sym2.mem_toFinsetV.mpr hv
  theta_bound := by
    intro K hK
    simp only [Finset.mem_image, SimpleGraph.mem_edgeFinset] at hK
    obtain ⟨e, he, rfl⟩ := hK
    induction e using Sym2.ind with
    | h a b =>
      rw [SimpleGraph.mem_edgeSet] at he
      have hab : a ≠ b := he.ne
      rw [Sym2.toFinsetV_mk, Finset.card_pair hab]
      have hfilter : G.edgeFinset.filter (fun e' => Sym2.toFinsetV e' = ({a, b} : Finset V))
          = {s(a, b)} := by
        ext e'
        simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset, Finset.mem_singleton]
        constructor
        · rintro ⟨he', hfl⟩
          exact Sym2.toFinsetV_eq hfl hab
        · intro rfl
          exact ⟨he, Sym2.toFinsetV_mk a b⟩
      rw [hfilter, Finset.card_singleton]
  assigned := by
    intro K hK
    simp only [Finset.mem_image, SimpleGraph.mem_edgeFinset] at hK
    obtain ⟨e, he, rfl⟩ := hK
    exact ⟨e, he, rfl⟩

omit [Fintype V] in
/-- Any family `F` of at most three of the four edges of the 4-cycle `abcd` has at
least `|F| + 1` distinct endpoints. -/
lemma card_biUnion_toFinsetV_ge {G' : SimpleGraph V} {a b c d : V}
    (hac : a ≠ c) (hbd : b ≠ d)
    (hab : G'.Adj a b) (hbc : G'.Adj b c) (hcd : G'.Adj c d) (hda : G'.Adj d a)
    {F : Finset (Sym2 V)} (hsub : F ⊆ {s(a, b), s(b, c), s(c, d), s(d, a)})
    (hne : F.Nonempty) (hcard : F.card ≤ 3) :
    F.card + 1 ≤ (F.biUnion Sym2.toFinsetV).card := by
  have hab' : a ≠ b := hab.ne
  have hbc' : b ≠ c := hbc.ne
  have hcd' : c ≠ d := hcd.ne
  have had : a ≠ d := hda.ne.symm
  -- the four edges are distinct
  have n12 : s(a, b) ≠ s(b, c) := by simp [hab', hbc', hac]
  have n13 : s(a, b) ≠ s(c, d) := by simp [hbc', had, hac, hbd]
  have n14 : s(a, b) ≠ s(d, a) := by simp [had, hbd, Ne.symm hab']
  have n23 : s(b, c) ≠ s(c, d) := by simp [hbc', hcd', hbd]
  have n24 : s(b, c) ≠ s(d, a) := by simp [hcd', hbd, Ne.symm hab', Ne.symm hac]
  have n34 : s(c, d) ≠ s(d, a) := by simp [hcd', Ne.symm had, Ne.symm hac]
  -- so the set of edges has cardinality 4
  have hE4card : ({s(a, b), s(b, c), s(c, d), s(d, a)} : Finset (Sym2 V)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [n12, n13, n14]),
        Finset.card_insert_of_notMem (by simp [n23, n24]),
        Finset.card_insert_of_notMem (by simp [n34]),
        Finset.card_singleton]
  -- endpoint finsets have card 2
  have hc1 : (Sym2.toFinsetV s(a, b)).card = 2 := Finset.card_pair hab'
  have hc2 : (Sym2.toFinsetV s(b, c)).card = 2 := Finset.card_pair hbc'
  have hc3 : (Sym2.toFinsetV s(c, d)).card = 2 := Finset.card_pair hcd'
  have hc4 : (Sym2.toFinsetV s(d, a)).card = 2 := Finset.card_pair (Ne.symm had)
  have hpos : 0 < F.card := Finset.card_pos.mpr hne
  have h123 : F.card = 1 ∨ F.card = 2 ∨ F.card = 3 := by omega
  rcases h123 with hFc | hFc | hFc
  · -- one edge: two endpoints
    obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hFc
    rw [Finset.singleton_biUnion]
    have hx := hsub (Finset.mem_singleton_self x)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · simp [Finset.card_singleton, Finset.card_pair hab']
    · simp [Finset.card_singleton, Finset.card_pair hbc']
    · simp [Finset.card_singleton, Finset.card_pair hcd']
    · simp [Finset.card_singleton, Finset.card_pair (Ne.symm had)]
  · -- two distinct edges: at least three endpoints
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hFc
    rw [Finset.biUnion_insert, Finset.singleton_biUnion]
    have hxE := hsub (Finset.mem_insert_self x {y})
    have hyE := hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self y))
    have hcardx : (Sym2.toFinsetV x).card = 2 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxE
      rcases hxE with rfl | rfl | rfl | rfl
      · exact hc1
      · exact hc2
      · exact hc3
      · exact hc4
    have hcardy : (Sym2.toFinsetV y).card = 2 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hyE
      rcases hyE with rfl | rfl | rfl | rfl
      · exact hc1
      · exact hc2
      · exact hc3
      · exact hc4
    have hne2 : Sym2.toFinsetV x ≠ Sym2.toFinsetV y := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxE hyE
      rcases hxE with rfl | rfl | rfl | rfl <;> rcases hyE with rfl | rfl | rfl | rfl
      all_goals
        first
        | exact absurd rfl hxy
        | (intro h
           rw [Sym2.toFinsetV_mk, Sym2.toFinsetV_mk, Finset.ext_iff] at h
           simp only [Finset.mem_insert, Finset.mem_singleton] at h
           have h1 := h a; have h2 := h b; have h3 := h c; have h4 := h d
           simp at h1 h2 h3 h4
           aesop)
    have hss : Sym2.toFinsetV x ⊂ Sym2.toFinsetV x ∪ Sym2.toFinsetV y := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨Finset.subset_union_left, ?_⟩
      intro h
      have hsub' : Sym2.toFinsetV y ⊆ Sym2.toFinsetV x := h ▸ Finset.subset_union_right
      exact hne2 ((Finset.eq_of_subset_of_card_le hsub' (hcardx.trans hcardy.symm).le).symm)
    have hlt := Finset.card_lt_card hss
    omega
  · -- three edges: contain a pair of opposite (disjoint) edges, hence four endpoints
    have hcardcompl : (({s(a, b), s(b, c), s(c, d), s(d, a)} : Finset (Sym2 V)) \ F).card = 1 := by
      rw [Finset.card_sdiff_of_subset hsub, hE4card, hFc]
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcardcompl
    have hxE : x ∈ ({s(a, b), s(b, c), s(c, d), s(d, a)} : Finset (Sym2 V)) := by
      have hxm : x ∈ ({s(a, b), s(b, c), s(c, d), s(d, a)} : Finset (Sym2 V)) \ F := by
        rw [hx]; exact Finset.mem_singleton_self x
      exact (Finset.mem_sdiff.mp hxm).1
    have hFeq : F = ({s(a, b), s(b, c), s(c, d), s(d, a)} : Finset (Sym2 V)).erase x := by
      ext y
      rw [Finset.mem_erase]
      constructor
      · intro hy
        refine ⟨fun hyx => ?_, hsub hy⟩
        rw [hyx] at hy
        have hxm : x ∈ ({s(a, b), s(b, c), s(c, d), s(d, a)} : Finset (Sym2 V)) \ F := by
          rw [hx]; exact Finset.mem_singleton_self x
        exact (Finset.mem_sdiff.mp hxm).2 hy
      · rintro ⟨hyx, hyE⟩
        by_contra hyF
        have hym : y ∈ ({s(a, b), s(b, c), s(c, d), s(d, a)} : Finset (Sym2 V)) \ F :=
          Finset.mem_sdiff.mpr ⟨hyE, hyF⟩
        rw [hx] at hym
        exact hyx (Finset.mem_singleton.mp hym)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxE
    have hge : 4 ≤ (F.biUnion Sym2.toFinsetV).card := by
      have hcase : (∀ p q : Sym2 V, p ≠ x → q ≠ x → p ≠ q →
          p ∈ ({s(a, b), s(b, c), s(c, d), s(d, a)} : Finset (Sym2 V)) →
          q ∈ ({s(a, b), s(b, c), s(c, d), s(d, a)} : Finset (Sym2 V)) →
          Disjoint (Sym2.toFinsetV p) (Sym2.toFinsetV q) →
          (Sym2.toFinsetV p).card = 2 → (Sym2.toFinsetV q).card = 2 →
          4 ≤ (F.biUnion Sym2.toFinsetV).card) := by
        intro p q hpx hqx hpq hpE hqE hdis hcp hcq
        have hpF : p ∈ F := by rw [hFeq, Finset.mem_erase]; exact ⟨hpx, hpE⟩
        have hqF : q ∈ F := by rw [hFeq, Finset.mem_erase]; exact ⟨hqx, hqE⟩
        have hsub2 : ({p, q} : Finset (Sym2 V)) ⊆ F := by
          intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl
          · exact hpF
          · exact hqF
        have hmono := Finset.biUnion_subset_biUnion_of_subset_left Sym2.toFinsetV hsub2
        have hcardu : (({p, q} : Finset (Sym2 V)).biUnion Sym2.toFinsetV).card = 4 := by
          rw [Finset.biUnion_insert, Finset.singleton_biUnion,
            Finset.card_union_of_disjoint hdis, hcp, hcq]
        calc 4 = (({p, q} : Finset (Sym2 V)).biUnion Sym2.toFinsetV).card := hcardu.symm
          _ ≤ (F.biUnion Sym2.toFinsetV).card := Finset.card_le_card hmono
      rcases hxE with rfl | rfl | rfl | rfl
      · exact hcase s(b, c) s(d, a) n12.symm n14.symm n24 (by simp) (by simp)
          (by
            rw [Sym2.toFinsetV_mk, Sym2.toFinsetV_mk, Finset.disjoint_iff_ne]
            intro x' hx' y' hy'
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx' hy'
            rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
            · exact hbd
            · exact (Ne.symm hab')
            · exact hcd'
            · exact (Ne.symm hac))
          hc2 hc4
      · exact hcase s(a, b) s(c, d) n12 n23.symm n13 (by simp) (by simp)
          (by
            rw [Sym2.toFinsetV_mk, Sym2.toFinsetV_mk, Finset.disjoint_iff_ne]
            intro x' hx' y' hy'
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx' hy'
            rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
            · exact hac
            · exact had
            · exact hbc'
            · exact hbd)
          hc1 hc3
      · exact hcase s(b, c) s(d, a) n23 n34.symm n24 (by simp) (by simp)
          (by
            rw [Sym2.toFinsetV_mk, Sym2.toFinsetV_mk, Finset.disjoint_iff_ne]
            intro x' hx' y' hy'
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx' hy'
            rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
            · exact hbd
            · exact (Ne.symm hab')
            · exact hcd'
            · exact (Ne.symm hac))
          hc2 hc4
      · exact hcase s(a, b) s(c, d) n14 n34 n13 (by simp) (by simp)
          (by
            rw [Sym2.toFinsetV_mk, Sym2.toFinsetV_mk, Finset.disjoint_iff_ne]
            intro x' hx' y' hy'
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx' hy'
            rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
            · exact hac
            · exact had
            · exact hbc'
            · exact hbd)
          hc1 hc3
    omega

/-- One merge step of the clique-cover algorithm: if the four edges of some
4-cycle `abcd` in `G'` do not all carry the same label, we may add all missing edges
inside the union `V'` of the (two to four) cliques labeling those edges and merge
those cliques into a single clique `V'`, obtaining a new valid cover with strictly
fewer cliques. -/
lemma Cover.merge {G G' : SimpleGraph V} [DecidableRel G.Adj] (cov : Cover G G')
    {a b c d : V} (hac : a ≠ c) (hbd : b ≠ d)
    (hab : G'.Adj a b) (hbc : G'.Adj b c) (hcd : G'.Adj c d) (hda : G'.Adj d a)
    (hdiff : ¬ (cov.ℓ s(a, b) = cov.ℓ s(b, c) ∧ cov.ℓ s(b, c) = cov.ℓ s(c, d) ∧
      cov.ℓ s(c, d) = cov.ℓ s(d, a))) :
    ∃ (G'' : SimpleGraph V) (cov' : Cover G G''), G' ≤ G'' ∧ cov'.C.card < cov.C.card := by
  -- the four edges and their labels
  set e1 : Sym2 V := s(a, b) with he1
  set e2 : Sym2 V := s(b, c) with he2
  set e3 : Sym2 V := s(c, d) with he3
  set e4 : Sym2 V := s(d, a) with he4
  set L1 := cov.ℓ e1 with hL1
  set L2 := cov.ℓ e2 with hL2
  set L3 := cov.ℓ e3 with hL3
  set L4 := cov.ℓ e4 with hL4
  set S : Finset (Finset V) := {L1, L2, L3, L4} with hS
  set V' : Finset V := S.biUnion id with hV'
  set D : Finset V := {a, b, c, d} with hD
  set E4 : Finset (Sym2 V) := {e1, e2, e3, e4} with hE4
  have hab' : a ≠ b := hab.ne
  have hbc' : b ≠ c := hbc.ne
  have hcd' : c ≠ d := hcd.ne
  have had : a ≠ d := hda.ne.symm
  have he1E : e1 ∈ G'.edgeSet := by rw [he1]; exact hab
  have he2E : e2 ∈ G'.edgeSet := by rw [he2]; exact hbc
  have he3E : e3 ∈ G'.edgeSet := by rw [he3]; exact hcd
  have he4E : e4 ∈ G'.edgeSet := by rw [he4]; exact hda
  have hL1C : L1 ∈ cov.C := cov.label_mem e1 he1E
  have hL2C : L2 ∈ cov.C := cov.label_mem e2 he2E
  have hL3C : L3 ∈ cov.C := cov.label_mem e3 he3E
  have hL4C : L4 ∈ cov.C := cov.label_mem e4 he4E
  have hL1S : L1 ∈ S := by rw [hS]; exact Finset.mem_insert_self _ _
  have hL2S : L2 ∈ S := by rw [hS]; simp
  have hL3S : L3 ∈ S := by rw [hS]; simp
  have hL4S : L4 ∈ S := by rw [hS]; simp
  have hSC : S ⊆ cov.C := by
    intro K hK
    rw [hS] at hK
    simp only [Finset.mem_insert, Finset.mem_singleton] at hK
    rcases hK with rfl | rfl | rfl | rfl
    · exact hL1C
    · exact hL2C
    · exact hL3C
    · exact hL4C
  -- membership of the cycle vertices in their labels
  have haL1 : a ∈ L1 := cov.label_sub e1 he1E a (by rw [he1, Sym2.mem_iff]; exact Or.inl rfl)
  have hbL1 : b ∈ L1 := cov.label_sub e1 he1E b (by rw [he1, Sym2.mem_iff]; exact Or.inr rfl)
  have hbL2 : b ∈ L2 := cov.label_sub e2 he2E b (by rw [he2, Sym2.mem_iff]; exact Or.inl rfl)
  have hcL2 : c ∈ L2 := cov.label_sub e2 he2E c (by rw [he2, Sym2.mem_iff]; exact Or.inr rfl)
  have hcL3 : c ∈ L3 := cov.label_sub e3 he3E c (by rw [he3, Sym2.mem_iff]; exact Or.inl rfl)
  have hdL3 : d ∈ L3 := cov.label_sub e3 he3E d (by rw [he3, Sym2.mem_iff]; exact Or.inr rfl)
  have hdL4 : d ∈ L4 := cov.label_sub e4 he4E d (by rw [he4, Sym2.mem_iff]; exact Or.inl rfl)
  have haL4 : a ∈ L4 := cov.label_sub e4 he4E a (by rw [he4, Sym2.mem_iff]; exact Or.inr rfl)
  -- the four cycle vertices all lie in `V'`
  have hDV' : D ⊆ V' := by
    intro v hv
    rw [hD] at hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rw [hV', Finset.mem_biUnion]
    rcases hv with rfl | rfl | rfl | rfl
    · exact ⟨L1, hL1S, haL1⟩
    · exact ⟨L1, hL1S, hbL1⟩
    · exact ⟨L2, hL2S, hcL2⟩
    · exact ⟨L3, hL3S, hdL3⟩
  -- cardinality facts
  have hDcard : D.card = 4 := by
    rw [hD, Finset.card_insert_of_notMem (by simp [hab', hac, had]),
      Finset.card_insert_of_notMem (by simp [hbc', hbd]),
      Finset.card_insert_of_notMem (by simp [hcd']), Finset.card_singleton]
  have hScard1 : 1 ≤ S.card := Finset.card_pos.mpr ⟨L1, hL1S⟩
  have hScard2 : 2 ≤ S.card := by
    by_contra hlt
    push Not at hlt
    have h1 : S.card = 1 := by omega
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h1
    have hmem : ∀ K ∈ S, K = x := by
      intro K hK
      rw [hx] at hK
      exact Finset.mem_singleton.mp hK
    have h12 : L1 = L2 := by rw [hmem L1 hL1S, hmem L2 hL2S]
    have h23 : L2 = L3 := by rw [hmem L2 hL2S, hmem L3 hL3S]
    have h34 : L3 = L4 := by rw [hmem L3 hL3S, hmem L4 hL4S]
    exact hdiff ⟨h12, h23, h34⟩
  have hScard4 : S.card ≤ 4 := by
    rw [hS]
    exact Finset.card_le_four
  -- the set `E4` of the four edges has cardinality 4
  have he1E4 : e1 ∈ E4 := by rw [hE4]; exact Finset.mem_insert_self _ _
  have he2E4 : e2 ∈ E4 := by rw [hE4]; simp
  have he3E4 : e3 ∈ E4 := by rw [hE4]; simp
  have he4E4 : e4 ∈ E4 := by rw [hE4]; simp
  have hE4card : E4.card = 4 := by
    have n12 : e1 ≠ e2 := by
      rw [he1, he2]; simp [hab', hbc', hac]
    have n13 : e1 ≠ e3 := by
      rw [he1, he3]; simp [hbc', had, hac, hbd]
    have n14 : e1 ≠ e4 := by
      rw [he1, he4]; simp [had, hbd, Ne.symm hab']
    have n23 : e2 ≠ e3 := by
      rw [he2, he3]; simp [hbc', hcd', hbd]
    have n24 : e2 ≠ e4 := by
      rw [he2, he4]; simp [hcd', hbd, Ne.symm hab', Ne.symm hac]
    have n34 : e3 ≠ e4 := by
      rw [he3, he4]; simp [hcd', Ne.symm had, Ne.symm hac]
    rw [hE4, Finset.card_insert_of_notMem (by simp [n12, n13, n14]),
      Finset.card_insert_of_notMem (by simp [n23, n24]),
      Finset.card_insert_of_notMem (by simp [n34]), Finset.card_singleton]
  -- the labels of edges of `G` form a subset of `cov.C`; edges of `G` are edges of `G'`
  have hedge_mono : ∀ e ∈ G.edgeSet, e ∈ G'.edgeSet := by
    intro e he
    induction e using Sym2.ind with
    | h x y => exact cov.le he
  have hedge_sup : ∀ e ∈ G'.edgeSet, e ∈ (G' ⊔ completeOn V').edgeSet := by
    intro e he
    induction e using Sym2.ind with
    | h x y => exact Or.inl he
  -- the families of cycle edges labeled by the cliques of `S` partition `E4`
  have hfib : ∑ K' ∈ S, (E4.filter (fun e => cov.ℓ e = K')).card = E4.card := by
    rw [← Finset.card_eq_sum_card_fiberwise (f := cov.ℓ) (s := E4) (t := S) (by
      intro e he
      rw [Finset.mem_coe, hE4] at he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rw [Finset.mem_coe]
      rcases he with rfl | rfl | rfl | rfl
      · simp only [← hL1]; exact hL1S
      · simp only [← hL2]; exact hL2S
      · simp only [← hL3]; exact hL3S
      · simp only [← hL4]; exact hL4S)]
  -- **the counting argument**: the sum of the sizes of the merged cliques exceeds
  -- the size of their union by at least the number of merged cliques
  have hcount : V'.card + S.card ≤ ∑ K ∈ S, K.card := by
    have hswap : ∑ K ∈ S, K.card = ∑ v ∈ V', (S.filter (fun K => v ∈ K)).card := by
      have h1 : ∀ K ∈ S, K.card = ∑ v ∈ V', (if v ∈ K then 1 else 0) := by
        intro K hK
        have hKV' : K ⊆ V' := Finset.subset_biUnion_of_mem id hK
        exact Finset.card_eq_sum_ite hKV'
      calc ∑ K ∈ S, K.card = ∑ K ∈ S, ∑ v ∈ V', (if v ∈ K then 1 else 0) :=
            Finset.sum_congr rfl h1
        _ = ∑ v ∈ V', ∑ K ∈ S, (if v ∈ K then 1 else 0) := Finset.sum_comm
        _ = ∑ v ∈ V', (S.filter (fun K => v ∈ K)).card :=
            Finset.sum_congr rfl (fun v _ => (Finset.card_filter _ _).symm)
    -- the sum over the four cycle vertices is at least `4 + |S|`
    have hswapD : ∑ v ∈ D, (S.filter (fun K => v ∈ K)).card
        = ∑ K ∈ S, (D.filter (· ∈ K)).card := by
      calc ∑ v ∈ D, (S.filter (fun K => v ∈ K)).card
          = ∑ v ∈ D, ∑ K ∈ S, (if v ∈ K then 1 else 0) :=
            Finset.sum_congr rfl (fun v _ => Finset.card_filter _ _)
        _ = ∑ K ∈ S, ∑ v ∈ D, (if v ∈ K then 1 else 0) := Finset.sum_comm
        _ = ∑ K ∈ S, (D.filter (· ∈ K)).card :=
            Finset.sum_congr rfl (fun K _ => (Finset.card_filter _ _).symm)
    -- for each `K ∈ S`, the edges of the cycle labeled `K` have at least one more
    -- endpoint in `K ∩ D` than their number
    have hKcard : ∀ K ∈ S, (E4.filter (fun e => cov.ℓ e = K)).card + 1 ≤
        (D.filter (· ∈ K)).card := by
      intro K hK
      set I := E4.filter (fun e => cov.ℓ e = K) with hI
      -- `I` is nonempty, since `K` is one of the four labels
      have hIne : I.Nonempty := by
        rw [hS] at hK
        simp only [Finset.mem_insert, Finset.mem_singleton] at hK
        rcases hK with rfl | rfl | rfl | rfl
        · exact ⟨e1, by rw [hI, Finset.mem_filter]; exact ⟨he1E4, hL1.symm⟩⟩
        · exact ⟨e2, by rw [hI, Finset.mem_filter]; exact ⟨he2E4, hL2.symm⟩⟩
        · exact ⟨e3, by rw [hI, Finset.mem_filter]; exact ⟨he3E4, hL3.symm⟩⟩
        · exact ⟨e4, by rw [hI, Finset.mem_filter]; exact ⟨he4E4, hL4.symm⟩⟩
      -- every `K' ∈ S` has a nonempty family of edges labeled `K'`
      have hK'ne : ∀ K' ∈ S, (E4.filter (fun e => cov.ℓ e = K')).Nonempty := by
        intro K' hK'
        rw [hS] at hK'
        simp only [Finset.mem_insert, Finset.mem_singleton] at hK'
        rcases hK' with rfl | rfl | rfl | rfl
        · exact ⟨e1, by rw [Finset.mem_filter]; exact ⟨he1E4, hL1.symm⟩⟩
        · exact ⟨e2, by rw [Finset.mem_filter]; exact ⟨he2E4, hL2.symm⟩⟩
        · exact ⟨e3, by rw [Finset.mem_filter]; exact ⟨he3E4, hL3.symm⟩⟩
        · exact ⟨e4, by rw [Finset.mem_filter]; exact ⟨he4E4, hL4.symm⟩⟩
      -- hence `I` has at most three elements
      have hIcard : I.card ≤ 3 := by
        have hsplit : I.card + ∑ K' ∈ S.erase K, (E4.filter (fun e => cov.ℓ e = K')).card
            = E4.card := by
          rw [hI]
          have h1 := Finset.sum_insert (Finset.notMem_erase K S)
            (f := fun K' => (E4.filter (fun e => cov.ℓ e = K')).card)
          rw [Finset.insert_erase hK] at h1
          rw [← h1]
          exact hfib
        have hsumge : (S.erase K).card ≤
            ∑ K' ∈ S.erase K, (E4.filter (fun e => cov.ℓ e = K')).card := by
          have h2 := Finset.sum_le_sum (s := S.erase K)
            (f := fun _ => (1 : ℕ)) (g := fun K' => (E4.filter (fun e => cov.ℓ e = K')).card)
            (fun K' hK' => Finset.card_pos.mpr
              (hK'ne K' ((Finset.erase_subset K S) hK')))
          rwa [Finset.sum_const, smul_eq_mul, Nat.mul_one] at h2
        have herase : (S.erase K).card = S.card - 1 := Finset.card_erase_of_mem hK
        rw [hE4card] at hsplit
        omega
      -- the endpoints of the edges of `I` lie in `K ∩ D`
      have hIsub : I.biUnion Sym2.toFinsetV ⊆ D.filter (· ∈ K) := by
        intro v hv
        rw [Finset.mem_biUnion] at hv
        obtain ⟨e, heI, hv⟩ := hv
        rw [hI, Finset.mem_filter] at heI
        have hv2 : v ∈ e := Sym2.mem_toFinsetV.mp hv
        rw [Finset.mem_filter]
        refine ⟨?_, ?_⟩
        · -- v ∈ D
          rw [hE4] at heI
          simp only [Finset.mem_insert, Finset.mem_singleton] at heI
          rw [hD]
          rcases heI.1 with rfl | rfl | rfl | rfl
          · rw [he1, Sym2.mem_iff] at hv2
            rcases hv2 with rfl | rfl <;> simp
          · rw [he2, Sym2.mem_iff] at hv2
            rcases hv2 with rfl | rfl <;> simp
          · rw [he3, Sym2.mem_iff] at hv2
            rcases hv2 with rfl | rfl <;> simp
          · rw [he4, Sym2.mem_iff] at hv2
            rcases hv2 with rfl | rfl <;> simp
        · -- v ∈ K
          have heE : e ∈ G'.edgeSet := by
            rw [hE4] at heI
            simp only [Finset.mem_insert, Finset.mem_singleton] at heI
            rcases heI.1 with rfl | rfl | rfl | rfl
            · exact he1E
            · exact he2E
            · exact he3E
            · exact he4E
          have h3 := cov.label_sub e heE v hv2
          rwa [heI.2] at h3
      calc I.card + 1 ≤ (I.biUnion Sym2.toFinsetV).card :=
            card_biUnion_toFinsetV_ge hac hbd hab hbc hcd hda
              (by rw [hI]; exact Finset.filter_subset _ _) hIne hIcard
        _ ≤ (D.filter (· ∈ K)).card := Finset.card_le_card hIsub
    have hDge : 4 + S.card ≤ ∑ v ∈ D, (S.filter (fun K => v ∈ K)).card := by
      rw [hswapD]
      have h := Finset.sum_le_sum (s := S)
        (f := fun K => (E4.filter (fun e => cov.ℓ e = K)).card + 1)
        (g := fun K => (D.filter (· ∈ K)).card) hKcard
      rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Nat.mul_one, hfib,
        hE4card] at h
      exact h
    have hVDge : (V' \ D).card ≤ ∑ v ∈ V' \ D, (S.filter (fun K => v ∈ K)).card := by
      have h := Finset.sum_le_sum (s := V' \ D) (f := fun _ => (1 : ℕ))
        (g := fun v => (S.filter (fun K => v ∈ K)).card) (fun v hv => by
          rw [Finset.mem_sdiff] at hv
          rw [hV', Finset.mem_biUnion] at hv
          obtain ⟨K, hK, hvK⟩ := hv.1
          exact Finset.card_pos.mpr ⟨K, Finset.mem_filter.mpr ⟨hK, hvK⟩⟩)
      rwa [Finset.sum_const, smul_eq_mul, Nat.mul_one] at h
    have hsplit : ∑ v ∈ V', (S.filter (fun K => v ∈ K)).card
        = ∑ v ∈ D, (S.filter (fun K => v ∈ K)).card
          + ∑ v ∈ V' \ D, (S.filter (fun K => v ∈ K)).card := by
      conv_lhs => rw [← Finset.union_sdiff_of_subset hDV']
      rw [Finset.sum_union Finset.disjoint_sdiff]
    have hV'D : (V' \ D).card = V'.card - 4 := by
      rw [Finset.card_sdiff_of_subset hDV', hDcard]
    have hDleV' : D.card ≤ V'.card := Finset.card_le_card hDV'
    rw [hswap, hsplit]
    omega
  -- the new graph and the new cover
  set G'' := G' ⊔ completeOn V' with hG''
  classical
  set ℓ' : Sym2 V → Finset V :=
    fun e => if e ∈ G'.edgeSet then (if cov.ℓ e ∈ S then V' else cov.ℓ e) else V' with hℓ'
  set C' : Finset (Finset V) := insert V' (cov.C \ S) with hC'
  have hcardC : C'.card < cov.C.card := by
    have h1 : C'.card ≤ (cov.C \ S).card + 1 := Finset.card_insert_le _ _
    have h2 : (cov.C \ S).card = cov.C.card - S.card := Finset.card_sdiff_of_subset hSC
    have h3 : S.card ≤ cov.C.card := Finset.card_le_card hSC
    omega
  -- labels of original edges
  have hℓ'G : ∀ e ∈ G.edgeFinset, ℓ' e = if cov.ℓ e ∈ S then V' else cov.ℓ e := by
    intro e he
    rw [hℓ']
    have heG' : e ∈ G'.edgeSet := hedge_mono e (by rwa [SimpleGraph.mem_edgeFinset] at he)
    simp [heG']
  refine ⟨G'', ⟨C', ℓ', ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, hcardC⟩
  · -- `G ≤ G''`
    exact le_trans cov.le le_sup_left
  · -- cliques of the new cover are cliques of `G''`
    intro K hK u hu w hw huw
    rw [hC', Finset.mem_insert, Finset.mem_sdiff] at hK
    rcases hK with rfl | ⟨hK, -⟩
    · exact Or.inr ⟨hu, hw, huw⟩
    · exact Or.inl (cov.clique K hK u hu w hw huw)
  · -- every edge of `G''` has a label in the new cover
    intro e he
    by_cases heG' : e ∈ G'.edgeSet
    · rw [hℓ']
      simp only [heG', ↓reduceIte]
      by_cases hS' : cov.ℓ e ∈ S
      · rw [ite_eq_left hS', hC']
        exact Finset.mem_insert_self _ _
      · rw [ite_eq_right hS', hC']
        exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨cov.label_mem e heG', hS'⟩)
    · rw [hℓ']
      simp only [heG', ↓reduceIte, hC']
      exact Finset.mem_insert_self _ _
  · -- the label of an edge contains its endpoints
    intro e he v hv
    by_cases heG' : e ∈ G'.edgeSet
    · rw [hℓ']
      simp only [heG', ↓reduceIte]
      have hv2 := cov.label_sub e heG' v hv
      by_cases hS' : cov.ℓ e ∈ S
      · rw [ite_eq_left hS']
        exact Finset.subset_biUnion_of_mem id hS' hv2
      · rw [ite_eq_right hS']
        exact hv2
    · rw [hℓ']
      simp only [heG', ↓reduceIte]
      -- `e` is a new edge, so both endpoints lie in `V'`
      rw [hG'', SimpleGraph.edgeSet_sup] at he
      rcases he with he' | he'
      · exact absurd he' heG'
      · obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hv
        have hvw : (completeOn V').Adj v w := he'
        exact hvw.1
  · -- the theta bound
    intro K hK
    by_cases hKV' : K = V'
    · -- the merged clique
      subst hKV'
      by_cases hV'C : V' ∈ cov.C
      · -- `V'` was already a clique of the old cover: it only gains edges
        have hsub : G.edgeFinset.filter (fun e => cov.ℓ e = V') ⊆
            G.edgeFinset.filter (fun e => ℓ' e = V') := by
          intro e he
          rw [Finset.mem_filter] at he ⊢
          refine ⟨he.1, ?_⟩
          rw [hℓ'G e he.1]
          by_cases hS' : cov.ℓ e ∈ S
          · rw [ite_eq_left hS']
          · rw [ite_eq_right hS', he.2]
        have hle := Finset.card_le_card hsub
        have hθ := cov.theta_bound V' hV'C
        omega
      · -- `V'` is new: its original edges are exactly those labeled by cliques of `S`
        have hfilter_eq : G.edgeFinset.filter (fun e => ℓ' e = V') =
            G.edgeFinset.filter (fun e => cov.ℓ e ∈ S) := by
          ext e
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨he, hℓe⟩
            rw [hℓ'G e he] at hℓe
            by_cases hS' : cov.ℓ e ∈ S
            · exact ⟨he, hS'⟩
            · rw [ite_eq_right hS'] at hℓe
              exact absurd (hℓe ▸ cov.label_mem e (hedge_mono e
                (by rwa [SimpleGraph.mem_edgeFinset] at he))) hV'C
          · rintro ⟨he, hS'⟩
            exact ⟨he, by rw [hℓ'G e he, ite_eq_left hS']⟩
        have hfib2 : (G.edgeFinset.filter (fun e => cov.ℓ e ∈ S)).card
            = ∑ K' ∈ S, (G.edgeFinset.filter (fun e => cov.ℓ e = K')).card := by
          exact (Finset.sum_card_fiberwise_eq_card_filter G.edgeFinset S cov.ℓ).symm
        have hsumθ : 3 * (∑ K' ∈ S, K'.card)
            ≤ 2 * (∑ K' ∈ S, (G.edgeFinset.filter (fun e => cov.ℓ e = K')).card)
              + S.card * 4 := by
          have h := Finset.sum_le_sum (s := S) (f := fun K' => 3 * K'.card)
            (g := fun K' => 2 * (G.edgeFinset.filter (fun e => cov.ℓ e = K')).card + 4)
            (fun K' hK' => cov.theta_bound K' (hSC hK'))
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            Finset.sum_const, smul_eq_mul] at h
          exact h
        rw [hfilter_eq, hfib2]
        omega
    · -- an old clique: its label set is unchanged
      have hKC : K ∈ cov.C := by
        rw [hC', Finset.mem_insert, Finset.mem_sdiff] at hK
        rcases hK with rfl | ⟨hK, -⟩
        · exact absurd rfl hKV'
        · exact hK
      have hKS : K ∉ S := by
        rw [hC', Finset.mem_insert, Finset.mem_sdiff] at hK
        rcases hK with rfl | ⟨-, hK⟩
        · exact absurd rfl hKV'
        · exact hK
      have hfilter_eq : G.edgeFinset.filter (fun e => ℓ' e = K) =
          G.edgeFinset.filter (fun e => cov.ℓ e = K) := by
        apply Finset.filter_congr
        intro e he
        rw [hℓ'G e he]
        by_cases hS' : cov.ℓ e ∈ S
        · rw [ite_eq_left hS']
          constructor
          · intro hKK
            exact absurd hKK (Ne.symm hKV')
          · intro hKK
            rw [hKK] at hS'
            exact absurd hS' hKS
        · rw [ite_eq_right hS']
      rw [hfilter_eq]
      exact cov.theta_bound K hKC
  · -- every clique of the new cover labels some edge
    intro K hK
    rw [hC', Finset.mem_insert, Finset.mem_sdiff] at hK
    rcases hK with rfl | ⟨hK, hKS'⟩
    · exact ⟨e1, hedge_sup e1 he1E,
        by simp only [hℓ']; rw [ite_eq_left he1E, ← hL1, ite_eq_left hL1S]⟩
    · obtain ⟨e, he, hℓe⟩ := cov.assigned K hK
      exact ⟨e, hedge_sup e he,
        by simp only [hℓ']; rw [ite_eq_left he, ite_eq_right (by rw [hℓe]; exact hKS'), hℓe]⟩
  · -- `G' ≤ G''`
    exact le_sup_left

/-- Running the merge algorithm of `Cover.merge`, starting from any cover, yields a
cover in which the four edges of every 4-cycle `abcd` with `a ≠ c` and `b ≠ d` all
carry the same label. -/
lemma exists_terminal_cover (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∀ (n : ℕ) (G' : SimpleGraph V) (cov : Cover G G'), cov.C.card ≤ n →
    ∃ (G'' : SimpleGraph V) (cov' : Cover G G''), G' ≤ G'' ∧
      ∀ (a b c d : V), a ≠ c → b ≠ d →
        G''.Adj a b → G''.Adj b c → G''.Adj c d → G''.Adj d a →
        cov'.ℓ s(a, b) = cov'.ℓ s(b, c) ∧ cov'.ℓ s(b, c) = cov'.ℓ s(c, d) ∧
        cov'.ℓ s(c, d) = cov'.ℓ s(d, a) := by
  intro n
  induction n with
  | zero =>
    intro G' cov hn
    by_cases hterm : ∀ (a b c d : V), a ≠ c → b ≠ d →
        G'.Adj a b → G'.Adj b c → G'.Adj c d → G'.Adj d a →
        cov.ℓ s(a, b) = cov.ℓ s(b, c) ∧ cov.ℓ s(b, c) = cov.ℓ s(c, d) ∧
        cov.ℓ s(c, d) = cov.ℓ s(d, a)
    · exact ⟨G', cov, le_refl _, hterm⟩
    · push Not at hterm
      obtain ⟨a, b, c, d, hac, hbd, hab, hbc, hcd, hda, hdiff⟩ := hterm
      have hdiff' : ¬ (cov.ℓ s(a, b) = cov.ℓ s(b, c) ∧ cov.ℓ s(b, c) = cov.ℓ s(c, d) ∧
        cov.ℓ s(c, d) = cov.ℓ s(d, a)) := fun h => hdiff h.1 h.2.1 h.2.2
      obtain ⟨G₁, cov₁, hle₁, hcard₁⟩ := cov.merge hac hbd hab hbc hcd hda hdiff'
      omega
  | succ n ih =>
    intro G' cov hn
    by_cases hterm : ∀ (a b c d : V), a ≠ c → b ≠ d →
        G'.Adj a b → G'.Adj b c → G'.Adj c d → G'.Adj d a →
        cov.ℓ s(a, b) = cov.ℓ s(b, c) ∧ cov.ℓ s(b, c) = cov.ℓ s(c, d) ∧
        cov.ℓ s(c, d) = cov.ℓ s(d, a)
    · exact ⟨G', cov, le_refl _, hterm⟩
    · push Not at hterm
      obtain ⟨a, b, c, d, hac, hbd, hab, hbc, hcd, hda, hdiff⟩ := hterm
      have hdiff' : ¬ (cov.ℓ s(a, b) = cov.ℓ s(b, c) ∧ cov.ℓ s(b, c) = cov.ℓ s(c, d) ∧
        cov.ℓ s(c, d) = cov.ℓ s(d, a)) := fun h => hdiff h.1 h.2.1 h.2.2
      obtain ⟨G₁, cov₁, hle₁, hcard₁⟩ := cov.merge hac hbd hab hbc hcd hda hdiff'
      obtain ⟨G'', cov', hle₂, hterm'⟩ := ih G₁ cov₁ (by omega)
      exact ⟨G'', cov', le_trans hle₁ hle₂, hterm'⟩

/-- If a cover of `G'` relative to `G` assigns the same label to the four edges of
every 4-cycle, and `G'` is completable, then the original graph `G` on `n` vertices
satisfies `3n ≤ 2·e(G) + 4`. -/
lemma lower_bound_of_terminal {G G' : SimpleGraph V} [DecidableRel G.Adj]
    (cov : Cover G G') (hn : 4 ≤ Fintype.card V)
    (hterm : ∀ (a b c d : V), a ≠ c → b ≠ d →
      G'.Adj a b → G'.Adj b c → G'.Adj c d → G'.Adj d a →
      cov.ℓ s(a, b) = cov.ℓ s(b, c) ∧ cov.ℓ s(b, c) = cov.ℓ s(c, d) ∧
      cov.ℓ s(c, d) = cov.ℓ s(d, a))
    (hcomp : Completable G') :
    3 * Fintype.card V ≤ 2 * G.edgeFinset.card + 4 := by
  -- no legal move is possible from `G'`: two common friends of `u`, `v` would form
  -- a 4-cycle whose single label is a clique containing both `u` and `v`
  have hno : ∀ u v : V, ¬ CanAdd G' u v := by
    intro u v hc
    obtain ⟨huv, hnadj, p, q, hpq, hup, hvp, huq, hvq⟩ := hc
    obtain ⟨h1, -⟩ := hterm u p v q huv hpq hup hvp.symm hvq huq.symm
    have hupE : s(u, p) ∈ G'.edgeSet := hup
    have huL : u ∈ cov.ℓ s(u, p) :=
      cov.label_sub s(u, p) hupE u (by rw [Sym2.mem_iff]; exact Or.inl rfl)
    have hvpE : s(p, v) ∈ G'.edgeSet := hvp.symm
    have hvL : v ∈ cov.ℓ s(p, v) :=
      cov.label_sub s(p, v) hvpE v (by rw [Sym2.mem_iff]; exact Or.inr rfl)
    rw [← h1] at hvL
    exact hnadj (cov.clique _ (cov.label_mem s(u, p) hupE) u huL v hvL huv)
  -- so `G' = ⊤`
  have htop : G' = ⊤ := (reachable_eq_of_no_canAdd hcomp hno).symm
  have hnontriv : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨u₀, v₀, huv₀⟩ := exists_pair_ne V
  set Kstar := cov.ℓ s(u₀, v₀) with hKstar
  -- two friendships sharing a user have the same label
  have key : ∀ x y z : V, x ≠ y → y ≠ z → cov.ℓ s(x, y) = cov.ℓ s(y, z) := by
    intro x y z hxy hyz
    by_cases hxz : x = z
    · subst hxz
      rw [Sym2.eq_swap]
    · obtain ⟨w, hw⟩ : ∃ w : V, w ∉ ({x, y, z} : Finset V) := by
        by_contra h
        push Not at h
        have hsub : (Finset.univ : Finset V) ⊆ {x, y, z} := fun w _ => h w
        have hcle := Finset.card_le_card hsub
        have h3 : ({x, y, z} : Finset V).card ≤ 3 := by
          exact Finset.card_le_three
        rw [Finset.card_univ] at hcle
        omega
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw
      obtain ⟨hwx, hwy, hwz⟩ := hw
      have hab : G'.Adj x y := by rw [htop]; exact (SimpleGraph.top_adj x y).mpr hxy
      have hbc : G'.Adj y z := by rw [htop]; exact (SimpleGraph.top_adj y z).mpr hyz
      have hcd : G'.Adj z w := by rw [htop]; exact (SimpleGraph.top_adj z w).mpr (Ne.symm hwz)
      have hda : G'.Adj w x := by rw [htop]; exact (SimpleGraph.top_adj w x).mpr hwx
      exact (hterm x y z w hxz (Ne.symm hwy) hab hbc hcd hda).1
  -- hence all friendships have label `Kstar`
  have hall : ∀ x y : V, x ≠ y → cov.ℓ s(x, y) = Kstar := by
    intro x y hxy
    by_cases hxu : x = u₀
    · rw [hxu]
      by_cases hyv : y = v₀
      · rw [hyv]
      · have h1 := key y u₀ v₀ (fun h => hxy (hxu.trans h.symm)) huv₀
        rw [Sym2.eq_swap, h1]
    · by_cases hxv : x = v₀
      · rw [hxv]
        by_cases hyu : y = u₀
        · rw [hyu, Sym2.eq_swap]
        · have h1 := key v₀ y u₀ (fun h => hxy (hxv.trans h)) hyu
          have h2 := key y u₀ v₀ hyu huv₀
          rw [h1, h2]
      · have h1 : cov.ℓ s(x, y) = cov.ℓ s(y, x) := by rw [Sym2.eq_swap]
        have h2 := key y x u₀ (Ne.symm hxy) hxu
        have h3 := key x u₀ v₀ hxu huv₀
        rw [h1, h2, h3]
  -- the cover consists of the single clique `Kstar`
  have huv₀E : s(u₀, v₀) ∈ G'.edgeSet := by
    rw [htop]
    exact (SimpleGraph.top_adj u₀ v₀).mpr huv₀
  have hKstarC : Kstar ∈ cov.C := cov.label_mem s(u₀, v₀) huv₀E
  have hCsingle : cov.C = {Kstar} := by
    ext K
    rw [Finset.mem_singleton]
    constructor
    · intro hK
      obtain ⟨e, he, hℓe⟩ := cov.assigned K hK
      induction e using Sym2.ind with
      | h x y =>
        have hadj : G'.Adj x y := he
        exact hℓe.symm.trans (hall x y hadj.ne)
    · intro rfl
      exact hKstarC
  -- `Kstar` is the whole vertex set
  have hKstaruniv : Kstar = Finset.univ := by
    ext v
    constructor
    · intro _
      exact Finset.mem_univ v
    · intro _
      obtain ⟨u, hu⟩ := exists_ne v
      have huvE : s(u, v) ∈ G'.edgeSet := by
        rw [htop]
        exact (SimpleGraph.top_adj u v).mpr hu
      have hvL : v ∈ cov.ℓ s(u, v) :=
        cov.label_sub s(u, v) huvE v (by rw [Sym2.mem_iff]; exact Or.inr rfl)
      rwa [hall u v hu] at hvL
  -- every original friendship has label `Kstar`
  have hθ : G.edgeFinset.filter (fun e => cov.ℓ e = Kstar) = G.edgeFinset := by
    apply Finset.filter_eq_self.mpr
    intro e he
    induction e using Sym2.ind with
    | h x y =>
      rw [SimpleGraph.mem_edgeFinset] at he
      have hadj : G.Adj x y := he
      exact hall x y hadj.ne
  have hbound := cov.theta_bound Kstar (by rw [hCsingle]; exact Finset.mem_singleton_self Kstar)
  rw [hθ, hKstaruniv, Finset.card_univ] at hbound
  exact hbound

/-- Lower bound: any completable graph on 2022 vertices has at least 3031 edges. -/
theorem lower_bound (G : SimpleGraph (Fin 2022)) (hcomp : Completable G) :
    3 * 2022 ≤ 2 * G.edgeSet.ncard + 4 := by
  classical
  rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  obtain ⟨G', cov', hle, hterm⟩ :=
    exists_terminal_cover G (initialCover G).C.card G (initialCover G) le_rfl
  have h : 3 * Fintype.card (Fin 2022) ≤ 2 * G.edgeFinset.card + 4 :=
    lower_bound_of_terminal cov' (by rw [Fintype.card_fin]; norm_num) hterm
      (completable_mono hle hcomp)
  have hfin : Fintype.card (Fin 2022) = 2022 := Fintype.card_fin 2022
  omega

/-! ### The construction -/

/-- The `i`-th "even" vertex `2i + 2` of the construction. -/
def xi (i : Fin 1010) : Fin 2022 := ⟨2 * i.val + 2, by omega⟩

/-- The `i`-th "odd" vertex `2i + 3` of the construction. -/
def yi (i : Fin 1010) : Fin 2022 := ⟨2 * i.val + 3, by omega⟩

lemma xi_val (i : Fin 1010) : (xi i).val = 2 * i.val + 2 := rfl

lemma yi_val (i : Fin 1010) : (yi i).val = 2 * i.val + 3 := rfl

lemma fin0_val : (0 : Fin 2022).val = 0 := by decide

lemma fin1_val : (1 : Fin 2022).val = 1 := by decide

lemma ne0x (i : Fin 1010) : (0 : Fin 2022) ≠ xi i := by
  intro h
  have hv := congr_arg Fin.val h
  rw [fin0_val, xi_val] at hv
  omega

lemma ne1x (i : Fin 1010) : (1 : Fin 2022) ≠ xi i := by
  intro h
  have hv := congr_arg Fin.val h
  rw [fin1_val, xi_val] at hv
  omega

lemma ne0y (i : Fin 1010) : (0 : Fin 2022) ≠ yi i := by
  intro h
  have hv := congr_arg Fin.val h
  rw [fin0_val, yi_val] at hv
  omega

lemma ne1y (i : Fin 1010) : (1 : Fin 2022) ≠ yi i := by
  intro h
  have hv := congr_arg Fin.val h
  rw [fin1_val, yi_val] at hv
  omega

lemma nexy (i : Fin 1010) : xi i ≠ yi i := by
  intro h
  have hv := congr_arg Fin.val h
  rw [xi_val, yi_val] at hv
  omega

lemma xex (i j : Fin 1010) (h : i ≠ j) : xi i ≠ xi j := by
  intro hh
  have hv := congr_arg Fin.val hh
  rw [xi_val, xi_val] at hv
  exact h (Fin.eq_of_val_eq (by omega))

lemma yey (i j : Fin 1010) (h : i ≠ j) : yi i ≠ yi j := by
  intro hh
  have hv := congr_arg Fin.val hh
  rw [yi_val, yi_val] at hv
  exact h (Fin.eq_of_val_eq (by omega))

lemma xey (i j : Fin 1010) : xi i ≠ yi j := by
  intro hh
  have hv := congr_arg Fin.val hh
  rw [xi_val, yi_val] at hv
  omega

/-- The edge set of the construction: the edge `0-1` together with, for each
`i < 1010`, the three further edges `1-xᵢ`, `xᵢ-yᵢ`, `yᵢ-0` of a 4-cycle
`0-1-xᵢ-yᵢ-0` sharing the edge `0-1`. -/
def constrEdges : Finset (Sym2 (Fin 2022)) :=
  {s(0, 1)} ∪ Finset.biUnion Finset.univ (fun i : Fin 1010 =>
    {s(1, xi i), s(xi i, yi i), s(yi i, 0)})

/-- The graph of the construction. -/
def constrGraph : SimpleGraph (Fin 2022) := SimpleGraph.fromEdgeSet ↑constrEdges

instance : DecidableRel constrGraph.Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromEdgeSet (↑constrEdges : Set (Sym2 (Fin 2022)))).Adj)

lemma adj01 : constrGraph.Adj 0 1 := by
  refine ⟨?_, by decide⟩
  rw [Sym2.toRel_prop, constrEdges, Finset.mem_coe, Finset.mem_union, Finset.mem_singleton]
  exact Or.inl rfl

lemma adj1x (i : Fin 1010) : constrGraph.Adj 1 (xi i) := by
  refine ⟨?_, ne1x i⟩
  rw [Sym2.toRel_prop, constrEdges, Finset.mem_coe, Finset.mem_union, Finset.mem_biUnion]
  exact Or.inr ⟨i, Finset.mem_univ i, Finset.mem_insert_self _ _⟩

lemma adjxy (i : Fin 1010) : constrGraph.Adj (xi i) (yi i) := by
  refine ⟨?_, nexy i⟩
  rw [Sym2.toRel_prop, constrEdges, Finset.mem_coe, Finset.mem_union, Finset.mem_biUnion]
  exact Or.inr ⟨i, Finset.mem_univ i, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩

lemma adjy0 (i : Fin 1010) : constrGraph.Adj (yi i) 0 := by
  refine ⟨?_, Ne.symm (ne0y i)⟩
  rw [Sym2.toRel_prop, constrEdges, Finset.mem_coe, Finset.mem_union, Finset.mem_biUnion]
  exact Or.inr ⟨i, Finset.mem_univ i,
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))⟩

/-- Phase 1 of the completion: for each `i`, add the friendships `0-xᵢ` and `1-yᵢ`
(each has two common friends). -/
lemma phase1 (T : Finset (Fin 1010)) :
    ∃ H : SimpleGraph (Fin 2022), Reachable constrGraph H ∧ constrGraph ≤ H ∧
      ∀ i ∈ T, H.Adj 0 (xi i) ∧ H.Adj 1 (yi i) := by
  induction T using Finset.induction with
  | empty => exact ⟨constrGraph, Reachable.refl _, le_refl _, fun i hi => by simp at hi⟩
  | @insert i T hiT ih =>
    obtain ⟨H, hreach, hle, hconn⟩ := ih
    have h01 : H.Adj 0 1 := hle adj01
    have hx1 : H.Adj (xi i) 1 := (hle (adj1x i)).symm
    have h0y : H.Adj 0 (yi i) := (hle (adjy0 i)).symm
    have hxy : H.Adj (xi i) (yi i) := hle (adjxy i)
    -- add the friendship `0-xᵢ` (common friends `1` and `yᵢ`)
    have hstep1 := reachable_add_edge_of_common (ne0x i) (ne1y i) h01 hx1 h0y hxy
    -- add the friendship `1-yᵢ` (common friends `0` and `xᵢ`)
    have h10 : (H ⊔ SimpleGraph.edge 0 (xi i)).Adj 1 0 := Or.inl h01.symm
    have hy0 : (H ⊔ SimpleGraph.edge 0 (xi i)).Adj (yi i) 0 := Or.inl h0y.symm
    have h1x : (H ⊔ SimpleGraph.edge 0 (xi i)).Adj 1 (xi i) := Or.inl hx1.symm
    have hyx : (H ⊔ SimpleGraph.edge 0 (xi i)).Adj (yi i) (xi i) := Or.inl hxy.symm
    have hstep2 := reachable_add_edge_of_common (ne1y i) (ne0x i) h10 hy0 h1x hyx
    refine ⟨H ⊔ SimpleGraph.edge 0 (xi i) ⊔ SimpleGraph.edge 1 (yi i),
      reachable_trans hreach (reachable_trans hstep1 hstep2),
      le_trans hle (le_trans le_sup_left le_sup_left), ?_⟩
    intro j hj
    rw [Finset.mem_insert] at hj
    rcases hj with hji | hj
    · rw [hji]
      constructor
      · exact Or.inl (Or.inr (by rw [SimpleGraph.edge_adj]; exact ⟨Or.inl ⟨rfl, rfl⟩, ne0x i⟩))
      · exact Or.inr (by rw [SimpleGraph.edge_adj]; exact ⟨Or.inl ⟨rfl, rfl⟩, ne1y i⟩)
    · exact ⟨Or.inl (Or.inl (hconn j hj).1), Or.inl (Or.inl (hconn j hj).2)⟩

/-- If `x` is friends with both `0` and `1`, we may successively make `x` friends
with every vertex of a set `T ∌ x` of vertices all of which are also friends with
both `0` and `1` (the pair `0, 1` always serves as the two common friends). -/
lemma reachable_connect_vertex {H : SimpleGraph (Fin 2022)} {x : Fin 2022}
    (hx0 : H.Adj x 0) (hx1 : H.Adj x 1) (T : Finset (Fin 2022))
    (hxT : x ∉ T) (hT : ∀ v ∈ T, H.Adj v 0 ∧ H.Adj v 1) :
    ∃ H' : SimpleGraph (Fin 2022), Reachable H H' ∧ H ≤ H' ∧ ∀ v ∈ T, H'.Adj x v := by
  induction T using Finset.induction with
  | empty => exact ⟨H, Reachable.refl _, le_refl _, fun v hv => by simp at hv⟩
  | @insert y T hyT ih =>
    have hxT' : x ∉ T := fun h => hxT (Finset.mem_insert_of_mem h)
    obtain ⟨H', hreach, hle, hconn⟩ := ih hxT' (fun v hv => hT v (Finset.mem_insert_of_mem hv))
    have hxy : x ≠ y := fun h => hxT (h ▸ Finset.mem_insert_self y T)
    have hy0 : H'.Adj y 0 := hle (hT y (Finset.mem_insert_self y T)).1
    have hy1 : H'.Adj y 1 := hle (hT y (Finset.mem_insert_self y T)).2
    have hx0' : H'.Adj x 0 := hle hx0
    have hx1' : H'.Adj x 1 := hle hx1
    have hstep := reachable_add_edge_of_common hxy (by decide : (0 : Fin 2022) ≠ 1)
      hx0' hy0 hx1' hy1
    refine ⟨H' ⊔ SimpleGraph.edge x y, reachable_trans hreach hstep, le_trans hle le_sup_left, ?_⟩
    intro v hv
    rw [Finset.mem_insert] at hv
    rcases hv with rfl | hv
    · exact Or.inr (by rw [SimpleGraph.edge_adj]; exact ⟨Or.inl ⟨rfl, rfl⟩, hxy⟩)
    · exact Or.inl (hconn v hv)

/-- If every vertex of `T` is friends with both `0` and `1`, we may make `T` into a
clique. -/
lemma reachable_complete_aux {H : SimpleGraph (Fin 2022)} (T : Finset (Fin 2022))
    (hT : ∀ v ∈ T, H.Adj v 0 ∧ H.Adj v 1) :
    ∃ H' : SimpleGraph (Fin 2022), Reachable H H' ∧ H ≤ H' ∧
      ∀ u ∈ T, ∀ w ∈ T, u ≠ w → H'.Adj u w := by
  induction T using Finset.induction with
  | empty => exact ⟨H, Reachable.refl _, le_refl _, fun u hu => by simp at hu⟩
  | @insert x T hxT ih =>
    obtain ⟨H', hreach, hle, hclique⟩ := ih (fun v hv => hT v (Finset.mem_insert_of_mem hv))
    have hx0 : H'.Adj x 0 := hle (hT x (Finset.mem_insert_self x T)).1
    have hx1 : H'.Adj x 1 := hle (hT x (Finset.mem_insert_self x T)).2
    obtain ⟨H'', hreach2, hle2, hconn⟩ := reachable_connect_vertex hx0 hx1 T hxT
      (fun v hv => ⟨hle (hT v (Finset.mem_insert_of_mem hv)).1,
        hle (hT v (Finset.mem_insert_of_mem hv)).2⟩)
    refine ⟨H'', reachable_trans hreach hreach2, le_trans hle hle2, ?_⟩
    intro u hu w hw huw
    rw [Finset.mem_insert] at hu hw
    rcases hu with rfl | hu <;> rcases hw with rfl | hw
    · exact absurd rfl huw
    · exact hconn w hw
    · exact (hconn u hu).symm
    · exact hle2 (hclique u hu w hw huw)

/-- After phase 1, every vertex other than `0` and `1` is of the form `xᵢ` or `yᵢ`
and is friends with both `0` and `1`. -/
lemma hnb {H₁ : SimpleGraph (Fin 2022)} (hle : constrGraph ≤ H₁)
    (hconn : ∀ i ∈ (Finset.univ : Finset (Fin 1010)), H₁.Adj 0 (xi i) ∧ H₁.Adj 1 (yi i))
    (v : Fin 2022) (hv : v ∉ ({0, 1} : Finset (Fin 2022))) :
    H₁.Adj v 0 ∧ H₁.Adj v 1 := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
  obtain ⟨hv0, hv1⟩ := hv
  have hv2 : 2 ≤ v.val := by
    by_contra h
    push Not at h
    have h01 : v.val = 0 ∨ v.val = 1 := by omega
    rcases h01 with h | h
    · exact hv0 (Fin.eq_of_val_eq (by rw [h, fin0_val]))
    · exact hv1 (Fin.eq_of_val_eq (by rw [h, fin1_val]))
  set i := (v.val - 2) / 2 with hi
  have hilt : i < 1010 := by omega
  have hvi : v.val = 2 * i + 2 ∨ v.val = 2 * i + 3 := by omega
  rcases hvi with h | h
  · have hvx : v = xi (⟨i, hilt⟩ : Fin 1010) := Fin.eq_of_val_eq (by rw [h, xi_val])
    rw [hvx]
    have hc := hconn (⟨i, hilt⟩ : Fin 1010) (Finset.mem_univ (⟨i, hilt⟩ : Fin 1010))
    exact ⟨hc.1.symm, (hle (adj1x (⟨i, hilt⟩ : Fin 1010))).symm⟩
  · have hvy : v = yi (⟨i, hilt⟩ : Fin 1010) := Fin.eq_of_val_eq (by rw [h, yi_val])
    rw [hvy]
    have hc := hconn (⟨i, hilt⟩ : Fin 1010) (Finset.mem_univ (⟨i, hilt⟩ : Fin 1010))
    exact ⟨hle (adjy0 (⟨i, hilt⟩ : Fin 1010)), hc.2.symm⟩

/-- The graph of the construction is completable: after phase 1, complete the
remaining `2020` vertices to a clique using `0, 1` as common friends. -/
lemma constr_completable : Completable constrGraph := by
  obtain ⟨H₁, hreach1, hle1, hconn1⟩ := phase1 Finset.univ
  obtain ⟨H₂, hreach2, hle2, hclique2⟩ := reachable_complete_aux (Finset.univ \ {0, 1})
    (fun v hv => hnb hle1 hconn1 v (Finset.mem_sdiff.mp hv).2)
  have htop : H₂ = ⊤ := by
    apply le_antisymm le_top
    rw [SimpleGraph.le_iff_adj]
    intro u w huw
    rw [SimpleGraph.top_adj] at huw
    by_cases hu : u ∈ ({0, 1} : Finset (Fin 2022)) <;>
      by_cases hw : w ∈ ({0, 1} : Finset (Fin 2022))
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hu hw
      rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
      · exact absurd rfl huw
      · exact hle2 (hle1 adj01)
      · exact (hle2 (hle1 adj01)).symm
      · exact absurd rfl huw
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      have hnbw := hnb hle1 hconn1 w hw
      rcases hu with rfl | rfl
      · exact (hle2 hnbw.1).symm
      · exact (hle2 hnbw.2).symm
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      have hnbu := hnb hle1 hconn1 u hu
      rcases hw with rfl | rfl
      · exact hle2 hnbu.1
      · exact hle2 hnbu.2
    · exact hclique2 u (Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, hu⟩) w
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hw⟩) huw
  show Reachable constrGraph ⊤
  rw [← htop]
  exact reachable_trans hreach1 hreach2

set_option linter.constructorNameAsVariable false in
/-- All edges of the construction are non-diagonal, so its edge set is exactly
`constrEdges`. -/
lemma constr_edgeSet : constrGraph.edgeSet = ↑constrEdges := by
  have h2 : constrGraph.edgeSet = (↑constrEdges : Set (Sym2 (Fin 2022))) \ Sym2.diagSet := by
    rw [show constrGraph = SimpleGraph.fromEdgeSet (↑constrEdges : Set (Sym2 (Fin 2022))) from rfl]
    exact SimpleGraph.edgeSet_fromEdgeSet _
  rw [h2, sdiff_eq_self_iff_disjoint, Set.disjoint_left]
  intro e he he2
  rw [Sym2.mem_diagSet] at he
  rw [Finset.mem_coe, constrEdges, Finset.mem_union, Finset.mem_singleton,
    Finset.mem_biUnion] at he2
  rcases he2 with rfl | ⟨i, -, hi⟩
  · rw [Sym2.mk_isDiag_iff] at he
    exact (by decide : (0 : Fin 2022) ≠ 1) he
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · rw [Sym2.mk_isDiag_iff] at he
      exact ne1x i he
    · rw [Sym2.mk_isDiag_iff] at he
      exact nexy i he
    · rw [Sym2.mk_isDiag_iff] at he
      exact Ne.symm (ne0y i) he

lemma constr_edgeFinset : constrGraph.edgeFinset = constrEdges := by
  apply Finset.coe_inj.mp
  rw [SimpleGraph.coe_edgeFinset, constr_edgeSet]

/-- If the first endpoint of `s(a, b)` differs from both endpoints of `s(c, d)`,
the two edges are distinct. -/
lemma sym2_ne_of_fst {a b c d : Fin 2022} (hac : a ≠ c) (had : a ≠ d) :
    s(a, b) ≠ s(c, d) := by
  intro h
  rw [Sym2.eq_iff] at h
  rcases h with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact hac h1
  · exact had h1

/-- If the second endpoint of `s(a, b)` differs from both endpoints of `s(c, d)`,
the two edges are distinct. -/
lemma sym2_ne_of_snd {a b c d : Fin 2022} (hbc : b ≠ c) (hbd : b ≠ d) :
    s(a, b) ≠ s(c, d) := by
  intro h
  rw [Sym2.eq_iff] at h
  rcases h with ⟨-, h1⟩ | ⟨-, h1⟩
  · exact hbd h1
  · exact hbc h1

/-- The construction has exactly `3031` friendships. -/
lemma constr_edge_ncard : constrGraph.edgeSet.ncard = 3031 := by
  rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset, constr_edgeFinset]
  -- the three edges of the `i`-th 4-cycle are distinct
  have hcard3 : ∀ i : Fin 1010,
      ({s(1, xi i), s(xi i, yi i), s(yi i, 0)} : Finset (Sym2 (Fin 2022))).card = 3 := by
    intro i
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [Finset.mem_singleton]
      exact sym2_ne_of_fst (nexy i) (Ne.symm (ne0x i))
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨sym2_ne_of_fst (ne1x i) (ne1y i), sym2_ne_of_fst (ne1y i) (by decide)⟩
  -- the edge families of two distinct 4-cycles are disjoint
  have hdisj : ∀ i ∈ (Finset.univ : Finset (Fin 1010)),
      ∀ j ∈ (Finset.univ : Finset (Fin 1010)), i ≠ j →
      Disjoint ({s(1, xi i), s(xi i, yi i), s(yi i, 0)} : Finset (Sym2 (Fin 2022)))
        {s(1, xi j), s(xi j, yi j), s(yi j, 0)} := by
    intro i _ j _ hij
    rw [Finset.disjoint_iff_ne]
    intro e he e' he'
    simp only [Finset.mem_insert, Finset.mem_singleton] at he he'
    rcases he with rfl | rfl | rfl <;> rcases he' with rfl | rfl | rfl
    · exact sym2_ne_of_snd (Ne.symm (ne1x i)) (xex i j hij)
    · exact sym2_ne_of_fst (ne1x j) (ne1y j)
    · exact sym2_ne_of_fst (ne1y j) (by decide)
    · exact sym2_ne_of_fst (Ne.symm (ne1x i)) (xex i j hij)
    · exact sym2_ne_of_fst (xex i j hij) (xey i j)
    · exact sym2_ne_of_fst (xey i j) (Ne.symm (ne0x i))
    · exact sym2_ne_of_fst (Ne.symm (ne1y i)) (Ne.symm (xey j i))
    · exact sym2_ne_of_fst (Ne.symm (xey j i)) (yey i j hij)
    · exact sym2_ne_of_fst (yey i j hij) (Ne.symm (ne0y i))
  -- the edge `0-1` belongs to no 4-cycle family
  have hnotmem : s(0, 1) ∉ Finset.biUnion (Finset.univ : Finset (Fin 1010))
      (fun i : Fin 1010 => ({s(1, xi i), s(xi i, yi i), s(yi i, 0)} :
        Finset (Sym2 (Fin 2022)))) := by
    rw [Finset.mem_biUnion]
    rintro ⟨i, -, hi⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with h | h | h
    · exact sym2_ne_of_fst (by decide) (ne0x i) h
    · exact sym2_ne_of_fst (ne0x i) (ne0y i) h
    · exact sym2_ne_of_snd (ne1y i) (by decide) h
  -- hence the `1010` families contribute `1010 * 3` edges
  have hbU : (Finset.biUnion (Finset.univ : Finset (Fin 1010)) (fun i : Fin 1010 =>
      ({s(1, xi i), s(xi i, yi i), s(yi i, 0)} : Finset (Sym2 (Fin 2022))))).card
        = 3030 := by
    rw [Finset.card_biUnion hdisj]
    trans ∑ _i ∈ (Finset.univ : Finset (Fin 1010)), (3 : ℕ)
    · exact Finset.sum_congr rfl (fun i _ => hcard3 i)
    · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  -- count: `1 + 1010 * 3 = 3031`
  unfold constrEdges
  rw [Finset.card_union_of_disjoint (by rwa [Finset.disjoint_singleton_left]),
    Finset.card_singleton, hbU]

snip end

determine answer : ℕ := 3031

problem usa2022_p6 :
    IsLeast {m : ℕ | ∃ G : SimpleGraph (Fin 2022), Completable G ∧ G.edgeSet.ncard = m}
      answer := by
  refine ⟨?_, ?_⟩
  · -- the construction: `3031` friendships suffice
    exact ⟨constrGraph, constr_completable, constr_edge_ncard⟩
  · -- the lower bound: fewer than `3031` friendships never suffice
    intro m hm
    obtain ⟨G, hcomp, hm⟩ := hm
    have h := lower_bound G hcomp
    show 3031 ≤ m
    omega

end Usa2022P6
