/-
Copyright (c) 2026 Constantin Seebach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Constantin Seebach
-/
import Mathlib

import ProblemExtraction

problem_file {
  tags := [.Combinatorics]
}

namespace Imo1981P2

/-!
# International Mathematical Olympiad 1981, Problem 2

Let $1 \le r \le n$ and consider all subsets of $r$ elements of the set $\{ 1, 2, \ldots , n \}$.
Each of these subsets has a smallest member. Let $F(n,r)$ denote the arithmetic mean of these smallest numbers; prove that
\[ F(n,r) = \frac{n+1}{r+1}. \]
-/

open Finset

variable (n r : ℕ)

def arith_mean (ms : Multiset ℕ) : ℚ := ms.sum / ms.card

def F : ℚ := arith_mean <| ((Icc 1 n).powersetCard r).val.map (fun s => s.min.getD 0)

snip begin

open SimpleGraph

def eraseMin (s : Finset ℕ) :=
  if h : s.Nonempty then
    s.erase (s.min' h)
  else
    s

@[simp]
theorem insert_min'_eraseMin {s : Finset ℕ} (hne : s.Nonempty) : insert (s.min' hne) (eraseMin s) = s := by
  unfold eraseMin
  simp only [hne, ↓reduceDIte]
  apply insert_erase
  exact min'_mem s hne

theorem eraseMin_insert {s : Finset ℕ} (x : ℕ) (h : ∀ y ∈ s, x < y) : eraseMin (insert x s) = s := by
  unfold eraseMin
  simp only [insert_nonempty, ↓reduceDIte]
  rw [show ∀ h, (insert x s).min' h = x by {
    simp only [insert_nonempty, forall_true_left]
    rw [min'_eq_iff]
    grind only [= mem_insert]
  }]
  apply erase_insert
  grind only

theorem eraseMin_mem_powersetCard {s : Finset ℕ} (h : s ∈ powersetCard (r + 1) (Icc 0 n)) : eraseMin s ∈ powersetCard r (Icc 1 n) := by
  suffices #(eraseMin s) = r ∧ 0 ∉ eraseMin s by
    grind [eraseMin]
  and_intros
  · unfold eraseMin
    split_ifs with sne
    · rw [card_erase_of_mem]
      · grind only [= mem_powersetCard]
      · exact min'_mem s sne
    · grind only [= mem_powersetCard, card_ne_zero]
  · unfold eraseMin
    split_ifs with sne
    · rw [mem_erase, not_and', not_ne_iff, eq_comm, min'_eq_iff]
      simp
    · grind only [= nonempty_def]


abbrev V := (powersetCard (r+1) (Icc 0 n)) ⊕ (powersetCard r (Icc 1 n))

def G : SimpleGraph (V n r) := {
  Adj u v := match (u, v) with
    | (.inl a, .inr b) | (.inr b, .inl a) => eraseMin a = b
    | _ => False
  symm := by
    grind only [swap_eq_iff]
}

instance : DecidableRel (G n r).Adj := fun u v =>
  match h : (u, v) with
  | (.inl a, .inr b) | (.inr b, .inl a) => if h' : eraseMin a = b then .isTrue (by simp_all [G]) else .isFalse (by simp_all [G])
  | (.inl a, .inl b) | (.inr b, .inr a) => .isFalse (by simp_all [G])


theorem bipartite_edge {α β : Type} {G : SimpleGraph (α ⊕ β)} (hbip : G ≤ completeBipartiteGraph α β) (e : Sym2 (α ⊕ β)) (he : e ∈ G.edgeSet)
    : ∃ (a : α) (b : β), e = s(Sum.inl a, Sum.inr b) := by
  obtain ⟨u,v,h⟩ : ∃ u v, e = s(u,v) := by
    rw [<-Sym2.exists]
    use e
  subst e
  rw [mem_edgeSet] at he
  have : (completeBipartiteGraph α β).Adj u v := by
    exact le_iff_adj.mp hbip _ _ he
  apply Or.elim this
  · intro ⟨h1, h2⟩
    use u.getLeft h1, v.getRight h2
    grind
  · intro ⟨h1, h2⟩
    use v.getLeft h2, u.getRight h1
    grind


theorem G.bipartite : G n r ≤ completeBipartiteGraph _ _ := by
  rw [le_iff_adj]
  intro u v hadj
  grind [G, completeBipartiteGraph_adj]

theorem G.card_edgeFinset : #(G n r).edgeFinset = Nat.choose (n+1) (r+1) := by
  rw [show n+1 = #(Icc 0 n) by simp, <-card_powersetCard, eq_comm]
  apply card_bij (fun s h => s(.inl ⟨s, h⟩, .inr ⟨eraseMin s, by grind only [eraseMin_mem_powersetCard]⟩))
  · intro s hs
    rw [mem_edgeFinset, mem_edgeSet]
    simp [G]
  · simp_all
  · intro e he
    rw [mem_edgeFinset] at he
    let ⟨a, b, h⟩ := bipartite_edge (G.bipartite n r) _ he
    subst e
    rw [mem_edgeSet, G] at he
    grind


theorem G.degree_b (rpos : 1 ≤ r) (b : powersetCard r (Icc 1 n)) : (G n r).degree (Sum.inr b) = b.val.min := by
  match hm : b.val.min with
  | none =>
    rw [WithTop.none_eq_top, Finset.min_eq_top] at hm
    grind only [= mem_powersetCard, = card_empty]
  | some m =>
    have h_bd : ∀ x ∈ b.val, m ≤ x := by
      intro x hx
      apply Finset.min_le_of_eq hx
      exact hm
    have mmem : m ∈ b.val := by
      apply Finset.mem_of_min
      exact hm
    have h_bd' : m ≤ n := by
      grind only [= mem_powersetCard, = subset_iff, = mem_Icc]
    congr
    rw [degree, <-Finset.card_range m, eq_comm]
    apply card_bij (fun i hi => Sum.inl ⟨insert i b.val, by grind⟩)
    · intro i hi
      rw [mem_neighborFinset, G]
      grind [eraseMin_insert]
    · intro i1 hi1 i2 hi2 e
      simp only [Sum.inl.injEq, Subtype.mk.injEq] at e
      apply (insert_inj _).mp e
      grind only [= mem_range]
    · intro v hv
      rw [mem_neighborFinset, G] at hv
      simp only at hv
      split at hv
      · simp_all
      · expose_names
        simp only [Prod.mk.injEq, Sum.inr.injEq] at heq
        have := heq.left
        have := heq.right
        subst b_1 v
        simp_rw [<-hv]
        have ane : a.val.Nonempty := by
          grind only [= mem_powersetCard, card_ne_zero]
        use a.val.min' ane, ?_
        · rw [Sum.inl.injEq, <-Subtype.val_inj]
          simp
        · simp only [mem_range]
          apply Finset.min'_lt_of_mem_erase_min'
          unfold eraseMin at hv
          simp only [ane, ↓reduceDIte] at hv
          simp_rw [hv]
          exact mmem
      · contradiction

snip end


problem imo1981_p2 (rpos : 1 ≤ r) (hrn : r ≤ n) : F n r = (n+1)/(r+1) := by
  have npos : 1 ≤ n := by lia
  unfold F arith_mean
  simp
  conv =>
    enter [1, 1]
    norm_cast
    arg 1
    rw [<-Finset.sum_attach]
    arg 2
    intro v
    rw [<-G.degree_b _ _ rpos, <-WithTop.coe_natCast, WithTop.some, Option.getD_some, Nat.cast_id, <-Function.Embedding.inr_apply]
  conv =>
    enter [1, 1, 1]
    rw [<-Finset.sum_map _ Function.Embedding.inr (fun v => (G n r).degree v)]
    rw [isBipartiteWith_sum_degrees_eq_card_edges' (s:=Finset.univ.map Function.Embedding.inl) ?bip]
    case bip => tactic =>
      unfold G
      constructor
      · simp [Set.disjoint_range_iff]
      · intro u v adj
        simp
        grind
  rw [G.card_edgeFinset]
  rw [<-mul_div_mul_left (c:=↑(n+1)) _ _ (by grind only), <-Nat.cast_mul, <-Nat.cast_mul, Nat.add_one_mul_choose_eq]
  qify
  have : (n + 1).choose (r + 1) ≠ 0 := by
    rw [Nat.choose_ne_zero_iff]
    lia
  field

end Imo1981P2
