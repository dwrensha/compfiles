/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InternLM-MATH LEAN Formalizer v0.1, Constantin Seebach
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 1978, Problem 6

An international society has its members from six different countries.
The list of members has 1978 names, numbered $1, 2, \ldots, 1978$.
Prove that there is at least one member whose number is
the sum of the numbers of two (not necessarily distinct) members from his own country.
-/

namespace Imo1978P6

snip begin

@[grind! .]
theorem Nat.ceilDiv_pos (a b : ℕ) (apos : 0 < a) (bpos : 0 < b) : 0 < a ⌈/⌉ b := by
  by_contra!
  rw [ceilDiv_le_iff_le_mul bpos] at this
  simp_all

variable {M N : ℕ}

abbrev Name : Type := Finset.Icc 1 M

variable (C : @Name M → Fin N)

noncomputable abbrev members_of (i : Fin N) : Finset (@Name M) := {k | C k = i}


def motive (Cdone : Finset (Fin N)) (k : ℕ) : Prop :=
  ∃ Δ : Finset Name,
      (∀ y ∈ Cdone, ∃ a0, C a0 = y ∧ ∀ x ∈ Δ, ∃ hb, C ⟨x.val+a0.val, hb⟩ = y)
    ∧ Disjoint (Δ.image C) Cdone
    ∧ k ≤ Δ.card

def motive' (n : ℕ) (k : ℕ) : Prop := ∃ Cdone, Cdone.card = n ∧ motive C Cdone k

theorem induction_begin : motive' C 0 M := by
  use ∅, by simp
  unfold motive
  use Finset.univ
  simp

theorem induction_end (k : ℕ) (kpos : 0 < k) : motive' C N k → False := by
  intro ih
  let ⟨Cdone, cc, Δ, h1, h2, h3⟩ := ih
  have : Cdone = Finset.univ := by
    apply Finset.eq_univ_of_card
    simp [cc]
  subst Cdone
  simp only [Finset.disjoint_iff_inter_eq_empty, Finset.inter_univ, Finset.image_eq_empty] at h2
  grind only [= Finset.card_empty]


theorem induction_step [NeZero N] (h : ∀ (j i k), C i = C j → C j = C k → i.val + k.val ≠ j.val)
    (n : ℕ) (k : ℕ) (kpos : 0 < k) (hu : n < N)
    : motive' C n k → motive' C (n+1) (k ⌈/⌉ (N-n) - 1) := by
  intro ih
  let ⟨Cdone, cc, Δ', ih1, ih2, ih3⟩ := ih
  have kcd_pos : 1 ≤ k ⌈/⌉ N := by grind only [!Nat.ceilDiv_pos, Nat.pos_of_neZero]
  have NsCdpos : 0 < N - Cdone.card := by lia
  have ddn_pos : 1 ≤ Δ'.card ⌈/⌉ (N - Cdone.card) := by grind only [!Nat.ceilDiv_pos]
  obtain ⟨y, hy1, hy2⟩ : ∃ y ∉ Cdone, (k ⌈/⌉ (N-Cdone.card)) ≤ (Δ' ∩ members_of C y).card := by
    let C' (x : Δ') : {y : Fin N // y ∈ (C '' Δ')} :=
      ⟨C x.val, by grind only [= Set.mem_image, = Finset.mem_coe]⟩
    let ⟨y, h⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card (n:=(Δ'.card ⌈/⌉ (N - Cdone.card) - 1)) C' ?_
    · use y
      and_intros
      · rw [Finset.disjoint_iff_inter_eq_empty] at ih2
        contrapose! ih2
        use y.val
        rw [Finset.mem_inter, <-SetLike.mem_coe]
        simp only [Finset.coe_image, Subtype.coe_prop, ih2, and_self]
      · calc
          _ ≤ Δ'.card ⌈/⌉ (N - Cdone.card) := by
            rw [Nat.ceilDiv_eq_add_pred_div, Nat.ceilDiv_eq_add_pred_div]
            apply Nat.div_le_div_right
            lia
          _ ≤ _ := by
            rw [tsub_lt_iff_left ddn_pos, Nat.lt_one_add_iff] at h
            apply le_trans h
            apply Finset.card_le_card_of_injOn (f:=Subtype.val)
            · unfold C' at *
              intro x hx
              simp [<-Subtype.val_inj] at hx ⊢
              exact hx
            · simp only [Finset.univ_eq_attach, Finset.coe_filter, Finset.mem_attach, true_and,
                SetLike.coe_eq_coe, implies_true, Set.injOn_of_eq_iff_eq]
    · apply lt_of_le_of_lt (b:=(N - Cdone.card) * (Δ'.card ⌈/⌉ (N - Cdone.card) - 1))
      · apply Nat.mul_le_mul_right
        rw [show N - Cdone.card = (Finset.univ \ Cdone).card by
          rw [Finset.card_sdiff_of_subset] <;> simp
        ]
        rw [Fintype.card_ofFinset, Finset.toFinset_coe]
        apply Finset.card_le_card
        rw [Finset.disjoint_iff_inter_eq_empty] at ih2
        intro y hy
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
        contrapose! ih2
        use y
        exact Finset.mem_inter_of_mem hy ih2
      · simp only [Fintype.card_coe]
        apply Nat.lt_of_add_one_le
        rw [Nat.ceilDiv_eq_add_pred_div, Nat.mul_sub, mul_one]
        have := Nat.mul_div_le (Δ'.card + (N - Cdone.card) - 1) (N - Cdone.card)
        rw [Nat.le_sub_iff_add_le, <-Nat.sub_le_iff_le_add, Nat.sub_add_comm] at this
        · exact this
        · suffices 1 ≤ (Δ'.card + (N - Cdone.card) - 1) / (N - Cdone.card) by exact Nat.le_mul_of_pos_right _ this
          rw [<-Nat.div_self NsCdpos]
          apply Nat.div_le_div_right
          rw [Nat.div_self NsCdpos]
          lia
        · lia
  have cc' : (Cdone ∪ {y}).card = n + 1 := by
    rw [Finset.union_singleton, Finset.card_insert_of_notMem hy1, cc]
  use Cdone ∪ {y}, cc'
  have Cyne : (Δ' ∩ members_of C y).Nonempty := by
    rw [<-Finset.card_pos, Nat.lt_iff_add_one_le]
    trans k ⌈/⌉ (N - Cdone.card)
    · by_contra!
      rw [add_comm, Nat.lt_one_add_iff] at this
      rw [ceilDiv_le_iff_le_mul NsCdpos] at this
      lia
    · exact hy2
  let xmin := (Δ' ∩ members_of C y).min' Cyne
  let Δ : Finset (@Name M) := ((Δ' ∩ members_of C y).erase xmin).attach.map (⟨fun x => ⟨x.val.val - xmin.val, by {
    rw [Finset.mem_Icc]
    and_intros
    · apply Nat.le_sub_of_add_le'
      rw [Nat.add_one_le_iff, Subtype.coe_lt_coe]
      apply Finset.min'_lt_of_mem_erase_min'
      apply SetLike.coe_mem
    · have := Finset.mem_Icc.mp xmin.prop
      have := Finset.mem_Icc.mp x.val.prop
      lia
  }⟩, by {
    intro x1 x2 e
    rw [Subtype.mk.injEq, tsub_left_inj, SetLike.coe_eq_coe, SetLike.coe_eq_coe] at e
    · trivial
    all_goals simp only [Subtype.coe_le_coe]; grind only [usr Subtype.property, = Finset.mem_erase, Finset.min'_le]
  }⟩)
  use Δ
  apply (show ∀ (a b c : Prop), (a ∧ (a → b) ∧ c) → (a ∧ b ∧ c) by grind only)
  and_intros
  · simp only [Finset.union_singleton, Finset.mem_insert, forall_eq_or_imp]
    and_intros
    · use xmin
      and_intros
      · grind only [!Finset.min'_mem, = Finset.mem_inter, = Finset.mem_filter]
      · intro x hx
        unfold Δ at hx
        simp only [Finset.mem_map, Finset.mem_attach, Function.Embedding.coeFn_mk, true_and,
          Subtype.exists, Finset.mem_erase, ne_eq, Finset.mem_inter, Finset.mem_filter,
          Finset.univ_eq_attach] at hx
        let ⟨a, ha1, ha2, ha3⟩ := hx
        subst x
        rw [Nat.sub_add_cancel]
        · simp_rw [ha2.right.right]
          simp only [ha1, exists_const]
        · rw [Subtype.coe_le_coe (y:=⟨a, ha1⟩)]
          grind only [= Finset.nonempty_def, Finset.min'_le, = Finset.mem_inter,
            = Finset.mem_filter, ← Finset.mem_univ]
    · intro y' hy'
      let ⟨b0, h1, h2⟩ := ih1 y' hy'
      use ⟨b0 + xmin, ?_⟩
      · and_intros
        · simp_rw [add_comm] at h2
          apply (h2 _ _).snd
          grind only [!Finset.min'_mem, = Finset.mem_inter]
        · intro x hx
          unfold Δ at hx
          simp only [Finset.mem_map, Finset.mem_attach, Function.Embedding.coeFn_mk, true_and,
            Subtype.exists, Finset.mem_erase, ne_eq, Finset.mem_inter, Finset.mem_filter,
            Finset.univ_eq_attach, Finset.mem_Icc] at hx
          have hs1 : ∀ (_h), ⟨x.val+xmin.val, _h⟩ ∈ Δ' := by
            grind only
          have xsx : x.val + xmin.val ∈ Finset.Icc 1 M := by
            lia
          use ?_
          · have := (h2 ⟨x.val+xmin.val, xsx⟩ ?_).snd
            · simp_rw [<-add_assoc, add_comm, add_assoc]
              simp_rw [add_comm] at this
              apply this
            · apply hs1
          · have := (h2 ⟨x.val+xmin.val, xsx⟩ ?_).snd
            · simp_rw [<-add_assoc, add_comm, add_assoc]
              simp_rw [add_comm] at this
              grind only
            · apply hs1
      · rw [add_comm]
        apply (h2 _ _).fst
        grind only [!Finset.min'_mem, = Finset.mem_inter]
  · intro hs
    suffices ∀ y' ∈ (Cdone ∪ {y}), Disjoint Δ (members_of C y') by
      grind only [= Finset.nonempty_def, Finset.disjoint_iff_ne, = Finset.mem_image,
        = Finset.mem_filter, ← Finset.mem_univ]
    intro y' hy'
    let ⟨b0, h1, h2⟩ := hs y' hy'
    rw [Finset.disjoint_iff_ne]
    intro x hx x' hx'
    have ⟨h2, h3⟩ := h2 _ hx
    by_cases! xvx'v : ¬ x'.val ≤ x.val
    · grind only
    have hb0 : b0.val + 1 < M := by grind only [= Finset.mem_Icc, = Finset.mem_filter]
    rw [Ne, Subtype.ext_iff, eq_comm, <-add_left_inj b0.val]
    rw [show x.val + b0.val = (⟨x.val+b0.val, h2⟩ : Name).val by simp]
    apply h <;> grind only [= Finset.mem_filter]
  · unfold Δ
    rw [Finset.card_map, Finset.card_attach, Finset.card_erase_of_mem (by apply Finset.min'_mem)]
    apply Nat.sub_le_sub_right
    rw [<-cc]
    apply le_trans hy2
    apply Finset.card_le_card
    simp


def compute_k (n: ℕ) : ℕ :=
  match n with
  | 0 => M
  | n+1 => ((compute_k n) ⌈/⌉ (N-n) - 1)

theorem compute_finite_induction [NeZero N] (hC : ∀ (j i k), C i = C j → C j = C k → i.val + k.val ≠ j.val)
  : 0 < @compute_k M N N → False := by
    intro hcom
    have hcom' : ∀ n ≤ N, 0 < @compute_k M N n := by
      clear hC
      intro n nb
      apply Nat.decreasingInduction' (P:=fun n => 0 < @compute_k M N n) _ nb hcom
      intro k _ _
      simp only
      intro h
      unfold compute_k at h
      contrapose! h
      rw [nonpos_iff_eq_zero] at h
      rw [h]
      simp
    apply induction_end C (compute_k N) hcom
    suffices ∀ n ≤ N, motive' C n (compute_k n) by exact this N le_rfl
    intro n
    induction n with
    | zero =>
      intro _
      apply induction_begin
    | succ n ih =>
      intro nb
      apply induction_step C hC _ _ (hcom' n _) _ (ih _) <;> lia


snip end

problem imo1978_p6 (C : Finset.Icc 1 1978 → Fin 6) :
  ∃ j i k, C i = C j ∧ C j = C k ∧ i.val + k.val = j.val := by
    by_contra! c
    apply compute_finite_induction C c
    decide

end Imo1978P6
