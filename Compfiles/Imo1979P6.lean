/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Constantin Seebach
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 1979, Problem 6

Let $A$ and $E$ be opposite vertices of an octagon.
A frog starts at vertex $A.$ From any vertex except $E$ it jumps to one of the two adjacent vertices.
When it reaches $E$ it stops. Let $a_n$ be the number of distinct paths of exactly $n$ jumps ending at $E$.
Prove that: \[a_{2n-1}=0, \quad a_{2n}={(2+\sqrt2)^{n-1} - (2-\sqrt2)^{n-1} \over\sqrt2}.\]
-/

namespace Imo1979P6

open SimpleGraph

abbrev Octagon := cycleGraph 8
abbrev A : Fin 8 := 0
abbrev E : Fin 8 := 4

def isTerminalWalk {V : Type} {G : SimpleGraph V} {u v : V} (w : G.Walk u v) := v ∉ w.support.dropLast

noncomputable def a (n : ℕ) := Set.ncard {w : Octagon.Walk A E | isTerminalWalk w ∧ w.length = n}

snip begin

instance instFintypeAnd {α : Type} [DecidableEq α] (p q : α → Prop) [inst : Fintype (Subtype p)] [DecidablePred q] : Fintype (Subtype (fun x => q x ∧ p x)) := {
  elems := (inst.elems.filter (fun x => q x.val)).attach.image (fun x => ⟨x.val.val, by grind⟩)
  complete := by
    simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists, Finset.mem_filter,
      Subtype.forall, Subtype.mk.injEq, exists_prop, exists_and_right, exists_eq_right, and_imp]
    intro a h1 h2
    and_intros
    · use h2
      apply Fintype.complete
    · exact h1
}

instance Set.instFintypeElemOfSubtype {α : Type} (p: α → Prop) [inst : Fintype {x // p x}] : Fintype ({x | p x}) := {
  elems := inst.elems
  complete := by
    simp only [Set.coe_setOf, Subtype.forall]
    intro a h
    apply Fintype.complete
}


@[simp]
theorem Walk.append_getVert {V : Type} {G : SimpleGraph V} {u v w : V}
  (w1 : G.Walk u v) (w2 : G.Walk v w) : (w1.append w2).getVert w1.length = v
    := by simp [Walk.getVert_append]

@[simp]
theorem Walk.take_append {V : Type} {G : SimpleGraph V} {u v w : V}
  (w1 : G.Walk u v) (w2 : G.Walk v w) :
  (w1.append w2).take w1.length = w1.copy rfl (by simp) := by
    apply Walk.ext_support
    rw [Walk.take_support_eq_support_take_succ, Walk.support_append]
    simp

@[simp]
theorem Walk.drop_append_of_length_eq {V : Type} {G : SimpleGraph V} {u v w : V}
  (w1 : G.Walk u v) (w2 : G.Walk v w) :
  (w1.append w2).drop w1.length = w2.copy (by simp) rfl := by
    apply Walk.ext_support
    rw [Walk.drop_support_eq_support_drop_min, Walk.support_append_eq_support_dropLast_append]
    simp


theorem isTerminalWalk_copy {V : Type} {G : SimpleGraph V} {u v u' v' : V} (h1 : u = u') (h2 : v = v') (w : G.Walk u v) : isTerminalWalk w → isTerminalWalk (w.copy h1 h2) := by
  unfold isTerminalWalk
  intro h
  simp [<-h2, h]

theorem isTerminalWalk_map {V V' : Type} {G : SimpleGraph V} {G' : SimpleGraph V'} (f : G ↪g G') {u v : V} (w : G.Walk u v) :
    isTerminalWalk w → isTerminalWalk (w.map f.toHom) := by
  unfold isTerminalWalk
  intro h
  set_option backward.isDefEq.respectTransparency false in
  simp
  contrapose! h
  rw [List.dropLast_eq_take, List.mem_take_iff_getElem] at h ⊢
  simp only [List.getElem_map, EmbeddingLike.apply_eq_iff_eq] at h
  grind only [= List.length_map]

theorem isTerminalWalk_of_isSubwalk {V : Type} {G : SimpleGraph V} {u u' t : V} {w : G.Walk u t} {w' : G.Walk u' t} (htw : isTerminalWalk w) (hsub : w'.IsSubwalk w)
    : isTerminalWalk w' := by
  unfold isTerminalWalk at htw ⊢
  rw [Walk.isSubwalk_iff_support_isInfix, List.IsInfix] at hsub
  let ⟨ru, rv, h⟩ := hsub
  rw [<-h, List.append_assoc, List.dropLast_append_of_ne_nil (by simp), List.dropLast_append] at htw
  contrapose! htw
  split_ifs with h
  · exact List.mem_append_right ru htw
  · apply List.mem_append_right
    apply List.mem_append_left
    exact Walk.end_mem_support w'


instance instDecidableIsTerminalWalk {V : Type} [DecidableEq V] {G : SimpleGraph V} {u v : V} : DecidablePred (fun (w : G.Walk u v) => isTerminalWalk w) := fun w => by
  unfold isTerminalWalk
  use inferInstance


abbrev C : Fin 8 := 2
abbrev G : Fin 8 := 6

noncomputable def b (n : ℕ) := Set.ncard {w : Octagon.Walk C E | isTerminalWalk w ∧ w.length = n}

def Octagon.mirror : Octagon ≃g Octagon := {
  toFun x := -x
  invFun x := -x
  map_rel_iff' := by
    intro a b
    rw [Equiv.coe_fn_mk, Octagon, cycleGraph_adj', cycleGraph_adj']
    grind only [= Fin.val_sub]
  left_inv := by simp [Function.LeftInverse.eq_1]
  right_inv := by simp [Function.RightInverse.eq_1, Function.LeftInverse.eq_1]
}

def C_G_symm (n : ℕ) : {w : Octagon.Walk C E // isTerminalWalk w ∧ w.length = n} ≃ {w : Octagon.Walk G E // isTerminalWalk w ∧ w.length = n} := {
  toFun := fun ⟨w, h⟩ => ⟨(w.map Octagon.mirror.toHom).copy (by decide) (by decide), by {
    and_intros
    · apply isTerminalWalk_copy
      apply isTerminalWalk_map
      exact h.left
    · set_option backward.isDefEq.respectTransparency false in
      simp [h.right]
  }⟩
  invFun := fun ⟨w, h⟩ => ⟨(w.map Octagon.mirror.toHom).copy (by decide) (by decide), by {
    and_intros
    · apply isTerminalWalk_copy
      apply isTerminalWalk_map
      exact h.left
    · set_option backward.isDefEq.respectTransparency false in
      simp [h.right]
  }⟩
  left_inv := fun ⟨w, h⟩ => by
    set_option backward.isDefEq.respectTransparency false in
    simp only [RelEmbedding.coe_toRelHom, RelIso.coe_toRelEmbedding, Walk.copy_rfl_rfl,
      Walk.map_map, Subtype.mk.injEq]
    apply Walk.ext_support
    unfold Octagon.mirror
    simp
  right_inv := fun ⟨w, h⟩ => by
    set_option backward.isDefEq.respectTransparency false in
    simp only [RelEmbedding.coe_toRelHom, RelIso.coe_toRelEmbedding, Walk.copy_rfl_rfl,
      Walk.map_map, Subtype.mk.injEq]
    apply Walk.ext_support
    unfold Octagon.mirror
    simp
}

def isTerminalWalk_length_cons_equiv {V : Type} {G : SimpleGraph V} {u t : V} (m n : ℕ) (npos : 0 < n) :
    {w : G.Walk u t // isTerminalWalk w ∧ w.length = m+n} ≃ Σ (v:V), {w : G.Walk u v // t ∉ w.support ∧ w.length = m} × {w : G.Walk v t // isTerminalWalk w ∧ w.length = n}
  := {
    toFun := fun ⟨w, h⟩ => ⟨w.getVert m, ⟨w.take m, by {
      and_intros
      · unfold isTerminalWalk at h
        rw [Walk.take_support_eq_support_take_succ]
        rw [List.dropLast_eq_take] at h
        have : m+1 ≤ w.support.length - 1 := by
          rw [Walk.length_support]
          lia
        have := List.take_subset_take_left w.support this
        grind only [= List.subset_def]
      · simp [h.right]
    }⟩, ⟨w.drop m, by {
      and_intros
      · apply isTerminalWalk_of_isSubwalk h.left
        exact Walk.isSubwalk_drop w m
      · simp [h.right]
    }⟩⟩
    invFun := fun ⟨v, ⟨⟨w1, h1⟩, ⟨w2, h2⟩⟩⟩ => ⟨w1.append w2, by {
      and_intros
      · unfold isTerminalWalk at h2 ⊢
        rw [Walk.support_append_eq_support_dropLast_append, List.dropLast_append_of_ne_nil (by simp), List.mem_append, not_or]
        and_intros
        · grind only [List.mem_of_mem_dropLast]
        · exact h2.left
      · simp [h1.right, h2.right]
    }⟩
    left_inv := fun ⟨w, h⟩ => by
      simp
    right_inv := fun ⟨v, ⟨⟨w1, h1, h1'⟩, ⟨w2, h2, h2'⟩⟩⟩ => by
      subst m n
      simp only [Walk.take_append, Walk.drop_append_of_length_eq, Sigma.mk.injEq,
        Walk.append_getVert, true_and]
      congr! 1
      · rw [Walk.append_getVert]
      · rw [Walk.append_getVert]
      · congr! 1
        · simp
        · rw [Walk.append_getVert]
        · simp [Walk.copy]
      · congr! 1
        · simp
        · rw [Walk.append_getVert]
        · simp [Walk.copy]
  }

theorem a_b_recurrence_1 (n : ℕ) (npos : 0 < n) : a (n+2) = 2 * a n + 2 * b n := by
  have walks_from_A (v) : Fintype.card { w : Octagon.Walk A v // E ∉ w.support ∧ w.length = 2 } =
    match v with
    | 0 => 2
    | 2 => 1
    | 6 => 1
    | _ => 0
      := by
        decide +revert
  unfold a b
  set_option backward.isDefEq.respectTransparency false in
  calc
    _ = Fintype.card {w : Octagon.Walk A E // isTerminalWalk w ∧ w.length = 2 + n} := by
      rw [Set.ncard_eq_toFinset_card', add_comm]
      simp
    _ = ∑ v ∈ {A,C,G}, Fintype.card {w : Octagon.Walk A v // E ∉ w.support ∧ w.length = 2} * Fintype.card {w : Octagon.Walk v E // isTerminalWalk w ∧ w.length = n} := by
      rw [Fintype.card_eq.mpr (Nonempty.intro (isTerminalWalk_length_cons_equiv _ _ npos))]
      rw [Fintype.card_sigma]
      simp_rw [Fintype.card_prod]
      rw [eq_comm, Finset.sum_subset]
      · simp
      · intro _ _ _
        apply mul_eq_zero_of_left
        decide +revert
    _ = _ := by
      repeat rw [Finset.sum_insert (by decide)]
      rw [Finset.sum_singleton]
      repeat rw [walks_from_A]
      simp only [Set.ncard_eq_toFinset_card', Set.toFinset_card, Set.coe_setOf]
      rw [<-Fintype.card_eq.mpr (Nonempty.intro (C_G_symm _))]
      lia

theorem a_b_recurrence_2 (n : ℕ) (npos : 0 < n) : b (n+2) = a n + 2 * b n := by
  have walks_from_C (v) : Fintype.card { w : Octagon.Walk C v // E ∉ w.support ∧ w.length = 2 } =
    match v with
    | 0 => 1
    | 2 => 2
    | _ => 0
      := by
        decide +revert
  unfold a b
  set_option backward.isDefEq.respectTransparency false in
  calc
    _ = Fintype.card {w : Octagon.Walk C E // isTerminalWalk w ∧ w.length = 2 + n} := by
      rw [Set.ncard_eq_toFinset_card', add_comm]
      simp
    _ = ∑ v ∈ {A,C}, Fintype.card {w : Octagon.Walk C v // E ∉ w.support ∧ w.length = 2} * Fintype.card {w : Octagon.Walk v E // isTerminalWalk w ∧ w.length = n} := by
      rw [Fintype.card_eq.mpr (Nonempty.intro (isTerminalWalk_length_cons_equiv _ _ npos))]
      rw [Fintype.card_sigma]
      simp_rw [Fintype.card_prod]
      rw [eq_comm, Finset.sum_subset]
      · simp
      · intro _ _ _
        apply mul_eq_zero_of_left
        decide +revert
    _ = _ := by
      repeat rw [Finset.sum_insert (by decide)]
      rw [Finset.sum_singleton]
      repeat rw [walks_from_C]
      simp only [Set.ncard_eq_toFinset_card', Set.toFinset_card, Set.coe_setOf]
      lia


theorem a_even (n : ℕ) (npos : 0 < n) : a (2*n) = ((2+√2)^(n-1) - (2-√2)^(n-1)) / √2 := by
  suffices a (2*n) = ((2+√2)^(n-1) - (2-√2)^(n-1)) / √2 ∧ b (2*n) = ((2+√2)^(n-1) + (2-√2)^(n-1)) / 2 by exact this.left
  revert n
  apply Nat.le_induction
  · unfold a b
    simp [Set.ncard_eq_toFinset_card']
    decide
  · intro n npos ih
    rw [mul_add, mul_one]
    rw [show n + 1 - 1 = (n - 1 + 1) by lia]
    repeat rw [pow_succ]
    and_intros
    · rw [a_b_recurrence_1 _ (by lia)]
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, ih.left, ih.right]
      field
    · rw [a_b_recurrence_2 _ (by lia)]
      rw [Nat.cast_add, Nat.cast_mul, ih.left, ih.right]
      generalize (2+√2)^(n-1) = α, (2-√2)^(n-1) = β
      simp only [Nat.cast_ofNat]
      field_simp
      rw [show 2 * (α - β + √2 * (α + β)) = √2 * (2+√2) * α + √2 * (2-√2) * β by grind]
      field


theorem walk_even (w : Octagon.Walk A E) : Even w.length := by
  let coloring := cycleGraph.bicoloring_of_even 8 (by simp [Nat.even_iff])
  rw [coloring.even_length_iff_congr]
  decide

theorem a_odd (n : ℕ) (npos : 0 < n) : a (2*n-1) = 0 := by
  unfold a
  rw [Set.ncard_eq_toFinset_card', Finset.card_eq_zero]
  apply Finset.eq_empty_of_forall_notMem
  intro w
  have := walk_even w
  grind only [= Nat.even_iff, = Set.mem_toFinset, usr Set.mem_setOf_eq]

snip end


problem imo1979_p6 (n : ℕ) (npos : 0 < n) : a (2*n-1) = 0 ∧ a (2*n) = ((2+√2)^(n-1) - (2-√2)^(n-1)) / √2 := by
  and_intros
  · exact a_odd n npos
  · exact a_even n npos

end Imo1979P6
