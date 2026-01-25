/-
Copyright (c) 2026 Constantin Seebach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Constantin Seebach
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file {
}

/-!
# International Mathematical Olympiad 1989, Problem 6

A permutation $\{x_1, \ldots, x_{2n}\}$ of the set $\{1,2, \ldots, 2n\}$ where $n$ is a positive integer,
is said to have property $T$ if $|x_i - x_{i + 1}| = n$ for at least one $i \in \{1,2, \ldots, 2n - 1\}$.
Show that, for each $n$, there are more permutations with property $T$ than without.
-/

namespace Imo1989P6

open Equiv

variable (n : ℕ)

def T (x : Perm (Finset.Icc 1 (2*n))) :=
  ∃ i, ∃ _ : i ∈ Finset.Icc 1 (2*n-1),
    |(x ⟨i, by grind⟩ : ℤ) - (x ⟨i+1, by grind⟩ : ℤ)| = n

snip begin

/-!
We implement Solution 3 from https://artofproblemsolving.com/wiki/index.php/1989_IMO_Problems/Problem_6 ,
trying to incorporate as much Perm(utation) machinery from Mathlib as possible.
-/

instance instOne [NeZero n] : OfNat ↥(Finset.Icc 1 (2 * n)) 1 := ⟨⟨1, by simpa using NeZero.one_le⟩⟩

noncomputable def A :=
  {x | ¬ T n x}

noncomputable def B :=
  {⟨x, k⟩ : Perm (Finset.Icc 1 (2*n)) × Finset.Icc 2 (2*n-1) | ∀ j : Finset.Icc 1 (2*n-1), k.val=j.val ↔ |(x ⟨j, by grind⟩ : ℤ) - (x ⟨j+1, by grind⟩ : ℤ)| = n}


theorem unique_ndiff (i j : Finset.Icc 1 (2*n)) : |(i:ℤ)-(j:ℤ)| = n ↔ j = (if i ≤ n then i+n else i-n) := by
  grind

def fin_equiv : Finset.Icc 1 (2*n) ≃ Fin (2*n) := {
  toFun x := ⟨x.val-1, by grind⟩
  invFun x := ⟨x.val+1, by grind⟩
  left_inv x := by grind
}

def perm_fin_equiv : Perm (Finset.Icc 1 (2*n)) ≃ Perm (Fin (2*n)) := equivCongr (fin_equiv n) (fin_equiv n)


@[simp]
theorem one_le_val (k : Finset.Icc 1 (2 * n)) : 1 ≤ k.val := by grind

@[simp]
theorem val_le_2n (k : Finset.Icc 1 (2 * n)) : k.val ≤ 2*n := by grind


def partial_cycle (k : Finset.Icc 1 (2 * n)) : Perm $ Perm $ Finset.Icc 1 (2 * n) := {
  toFun x := (perm_fin_equiv n).symm ((perm_fin_equiv n) x * Fin.cycleRange (fin_equiv n k))
  invFun x := (perm_fin_equiv n).symm ((perm_fin_equiv n) x * (Fin.cycleRange (fin_equiv n k)).symm)
  left_inv x := by
    simp only [apply_symm_apply]
    rw [mul_assoc]
    simp
  right_inv x := by
    simp only [apply_symm_apply]
    rw [mul_assoc]
    simp
}

theorem partial_cycle.apply_of_eq [NeZero n] (x : Perm $ Finset.Icc 1 (2 * n)) (k i : Finset.Icc 1 (2 * n)) (h : i = k)
    : (partial_cycle n k x) i = x 1 := by
  unfold partial_cycle perm_fin_equiv instOne
  simp only [equivCongr_symm, coe_fn_mk, equivCongr_apply_apply, symm_symm, Perm.coe_mul,
    Function.comp_apply, symm_apply_apply]
  rw [<-h, Fin.cycleRange_self]
  unfold fin_equiv
  simp

theorem partial_cycle.apply_of_gt [NeZero n] (x : Perm $ Finset.Icc 1 (2 * n)) (k i : Finset.Icc 1 (2 * n)) (h : k < i)
    : (partial_cycle n k x) i = x i := by
  unfold partial_cycle perm_fin_equiv
  simp only [equivCongr_symm, coe_fn_mk, equivCongr_apply_apply, symm_symm, Perm.coe_mul,
    Function.comp_apply, symm_apply_apply]
  rw [Fin.cycleRange_of_gt]
  · simp
  · unfold fin_equiv
    apply Nat.sub_lt_sub_right _ h
    apply one_le_val

theorem partial_cycle.apply_of_lt [NeZero n] (x : Perm $ Finset.Icc 1 (2 * n)) (k i : Finset.Icc 1 (2 * n)) (h : i < k)
    : (partial_cycle n k x) i = ⟨x ⟨i + 1, by rw [<-Subtype.coe_lt_coe] at h; grind⟩, by simp⟩ := by
  unfold partial_cycle perm_fin_equiv
  simp only [equivCongr_symm, coe_fn_mk, equivCongr_apply_apply, symm_symm, Perm.coe_mul,
    Function.comp_apply, symm_apply_apply]
  rw [Fin.cycleRange_of_lt]
  · unfold fin_equiv
    simp only [coe_fn_mk, coe_fn_symm_mk, Subtype.coe_eta, EmbeddingLike.apply_eq_iff_eq,
      Subtype.mk.injEq, Nat.add_right_cancel_iff]
    rw [Fin.val_add_one_of_lt']
    · simp
    · simp only [one_le_val, Nat.sub_add_cancel]
      rw [<-Subtype.coe_lt_coe] at h
      apply lt_of_lt_of_le h
      exact val_le_2n n k
  · unfold fin_equiv
    apply Nat.sub_lt_sub_right _ h
    apply one_le_val


theorem partial_cycle.symm.apply_of_eq [NeZero n] (x : Perm $ Finset.Icc 1 (2 * n)) (k i : Finset.Icc 1 (2 * n)) (h : i = 1)
    : ((partial_cycle n k).symm x) i = x k := by
  unfold partial_cycle perm_fin_equiv
  simp only [equivCongr_symm, coe_fn_symm_mk, equivCongr_apply_apply, symm_symm, Perm.coe_mul,
    Function.comp_apply, symm_apply_apply, EmbeddingLike.apply_eq_iff_eq]
  suffices (fin_equiv n) i = (((fin_equiv n) k).cycleRange) ((fin_equiv n) k) by grind
  rw [Fin.cycleRange_of_eq]
  · subst i
    unfold fin_equiv instOne
    simp
  · rfl

theorem partial_cycle.symm.apply_of_gt [NeZero n] (x : Perm $ Finset.Icc 1 (2 * n)) (k i : Finset.Icc 1 (2 * n)) (h : k < i)
    : ((partial_cycle n k).symm x) i = x i := by
  unfold partial_cycle perm_fin_equiv
  simp only [equivCongr_symm, coe_fn_symm_mk, equivCongr_apply_apply, symm_symm, Perm.coe_mul,
    Function.comp_apply, symm_apply_apply, EmbeddingLike.apply_eq_iff_eq]
  suffices (fin_equiv n) i = (((fin_equiv n) k).cycleRange) ((fin_equiv n) i) by grind
  rw [Fin.cycleRange_of_gt]
  unfold fin_equiv
  apply Nat.sub_lt_sub_right _ h
  apply one_le_val

theorem partial_cycle.symm.apply_of_le [NeZero n] (x : Perm $ Finset.Icc 1 (2 * n)) (k i : Finset.Icc 1 (2 * n)) (h1 : i ≤ k) (h2 : 1 < i)
    : ((partial_cycle n k).symm x) i = ⟨x ⟨i - 1, by rw [instOne, <-Subtype.coe_lt_coe] at h2; grind⟩, by simp⟩ := by
  unfold partial_cycle perm_fin_equiv
  simp only [equivCongr_symm, coe_fn_symm_mk, equivCongr_apply_apply, symm_symm, Perm.coe_mul,
    Function.comp_apply, symm_apply_apply]
  suffices (fin_equiv n) i = (((fin_equiv n) k).cycleRange) ((fin_equiv n) ⟨i - 1, by rw [instOne, <-Subtype.coe_lt_coe] at h2; grind⟩) by grind
  simp_rw [<-Subtype.coe_lt_coe] at h1 h2
  rw [Fin.cycleRange_of_lt]
  · unfold fin_equiv
    simp only [coe_fn_mk]
    apply Fin.val_injective
    rw [Fin.val_add_one_of_lt'] <;> grind
  · unfold fin_equiv
    simp only [coe_fn_mk, Fin.mk_lt_mk]
    apply Nat.sub_lt_sub_right
    · grind
    · apply Nat.lt_of_le_sub_one
      · grind
      · apply Nat.sub_le_sub_right
        exact Subtype.GCongr.coe_le_coe h1


def transform_A_to_B [NeZero n] : (A n) → (B n) := fun x ↦ by
  let x_1 := x.val 1
  let x_k : Finset.Icc 1 (2*n) := ⟨if x_1 ≤ n then x_1+n else x_1-n, by grind⟩
  have ndiff : |(x_1:ℤ) - x_k| = n := by rw [unique_ndiff]
  let k := x.val.symm x_k
  let k_sub_1 : Finset.Icc 2 (2*n-1) := ⟨k-1, by {
    suffices k.val ≠ 1 ∧ k.val ≠ 2 by
      let := one_le_val _ k
      grind
    and_intros
    · contrapose! ndiff
      replace ndiff : k = 1 := by exact SetLike.coe_eq_coe.mp ndiff
      rw [show x_1 = (x.val 1) by rfl]
      rw [show x_k = (x.val 1) by rw [<-ndiff]; unfold k; simp]
      simp
      grind only [= Finset.mem_Icc]
    · unfold A T at x
      let := (not_exists.mp $ Set.mem_setOf_eq.mp x.prop) 1
      simp only [Set.mem_setOf_eq, Nat.reduceAdd, Finset.mem_Icc, le_refl, true_and,
        not_exists] at this
      contrapose! this
      use (by grind)
      rw [show (x.val ⟨1, _⟩) = x_1 by rfl]
      rw [show (x.val ⟨2, _⟩) = x_k by unfold k at this; simp_rw [<-this]; simp]
      exact ndiff
  }⟩
  use ⟨(partial_cycle n ⟨k-1, by grind⟩) x, k_sub_1⟩
  intro j
  constructor
  · intro jeq
    simp_rw [<-jeq]
    nth_rw 1 [partial_cycle.apply_of_eq _ _ _ _ (by unfold k_sub_1; simp)]
    nth_rw 1 [partial_cycle.apply_of_gt _ _ _ _ (by rw [<-Subtype.coe_lt_coe]; grind)]
    unfold k_sub_1
    simp only [one_le_val, Nat.sub_add_cancel, Subtype.coe_eta]
    rw [show (x.val 1) = x_1 by rfl]
    rw [show (x.val k) = x_k by unfold k; simp]
    exact ndiff
  · intro e
    contrapose e
    unfold k_sub_1 at e
    simp only at e
    have : j.val = k.val-2 ∨ j.val < k.val-2 ∨ j.val ≥ k.val := by omega
    apply this.elim3
    · intro jeq
      simp_rw [jeq]
      nth_rw 1 [partial_cycle.apply_of_lt _ _ _ _ (by rw [<-Subtype.coe_lt_coe]; lia)]
      nth_rw 1 [partial_cycle.apply_of_eq _ _ _ _ (by lia)]
      unfold x_1 at ndiff
      rw [abs_sub_comm]
      rw [unique_ndiff] at ⊢ ndiff
      rw [<-ndiff]
      simp
      rw [show x_k = (x.val k) by unfold k; simp]
      have : ⟨k-2+1, by grind⟩ ≠ k := by rw [<-Subtype.coe_ne_coe]; grind
      contrapose! this
      apply x.val.injective this
    · intro jlt
      nth_rw 1 [partial_cycle.apply_of_lt _ _ _ _ (by rw [<-Subtype.coe_lt_coe]; simp; lia)]
      nth_rw 1 [partial_cycle.apply_of_lt _ _ _ _ (by rw [<-Subtype.coe_lt_coe]; simp; lia)]
      apply not_exists.mp $ (not_exists.mp $ Set.mem_setOf_eq.mp x.prop) _
      grind only [= Finset.mem_Icc]
    · intro jgt
      nth_rw 1 [partial_cycle.apply_of_gt _ _ _ _ (by rw [<-Subtype.coe_lt_coe]; simp; lia)]
      nth_rw 1 [partial_cycle.apply_of_gt _ _ _ _ (by rw [<-Subtype.coe_lt_coe]; simp; lia)]
      apply not_exists.mp $ (not_exists.mp $ Set.mem_setOf_eq.mp x.prop) _
      grind only [= Finset.mem_Icc]


def transform_B_to_A [NeZero n] : (B n) → (A n) := fun ⟨⟨x, k⟩, h⟩ ↦ by
  let x_k := x ⟨k, by grind⟩
  let x_k_1 := x ⟨k+1, by grind⟩
  have ndiff : |(x_k:ℤ) - x_k_1| = n := by
    unfold B at h
    simp only [Subtype.forall, Set.mem_setOf_eq] at h
    apply (h _ _).mp
    · rfl
    · grind only [= Finset.mem_Icc]
  use (partial_cycle n ⟨k, by grind⟩).symm x
  unfold A T
  simp only [Finset.mem_Icc, not_exists, forall_and_index, Set.mem_setOf_eq]
  intro i ib1 ib2
  by_cases c1 : i = 1
  · subst c1
    nth_rw 1 [partial_cycle.symm.apply_of_eq _ _ _ _ (by rfl)]
    nth_rw 1 [partial_cycle.symm.apply_of_le _ _ _ _ (by simp; grind) (by rw [<-Subtype.coe_lt_coe]; exact Nat.lt_add_one _)]
    simp only [Nat.reduceAdd, Nat.add_one_sub_one]
    rw [unique_ndiff] at ⊢ ndiff
    rw [<-ndiff]
    unfold x_k_1
    simp only [SetLike.coe_eq_coe]
    by_contra
    simp only [EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq, Nat.right_eq_add] at this
    grind only [= Finset.mem_Icc]
  have igt : 1 < i := by grind
  by_cases cik : i = k
  · subst cik
    nth_rw 1 [partial_cycle.symm.apply_of_le _ _ _ _ (by rfl) (by simpa using igt)]
    nth_rw 1 [partial_cycle.symm.apply_of_gt _ _ _ _ (by simp)]
    simp only [ne_eq]
    rw [abs_sub_comm] at ⊢ ndiff
    rw [unique_ndiff] at ⊢ ndiff
    rw [<-ndiff]
    unfold x_k
    simp
    rw [Nat.sub_one_eq_self]
    exact Nat.ne_zero_of_lt ib1
  by_cases c2 : i < k
  · nth_rw 1 [partial_cycle.symm.apply_of_le _ _ _ _ (by simp; grind) (by simpa using igt)]
    nth_rw 1 [partial_cycle.symm.apply_of_le _ _ _ _ (by simpa using c2) (by rw [<-Subtype.coe_lt_coe]; exact Nat.lt_add_of_pos_left ib1)]
    simp only [add_tsub_cancel_right]
    unfold B at h
    simp only [Subtype.forall, Set.mem_setOf_eq] at h
    have : ∀ h, (⟨i, h⟩ : Finset.Icc 1 (2 * n)) = ⟨i-1+1, by grind⟩ := by lia
    simp_rw [this]
    apply (h _ _).not.mp
    · grind only
    · grind only [= Finset.mem_Icc]
  · have c2 : k < i := by grind
    nth_rw 1 [partial_cycle.symm.apply_of_gt _ _ _ _ (by simpa using c2)]
    nth_rw 1 [partial_cycle.symm.apply_of_gt _ _ _ _ (by simp; lia)]
    unfold B at h
    simp only [Subtype.forall, Set.mem_setOf_eq] at h
    apply (h _ _).not.mp
    · exact Nat.ne_of_lt c2
    · grind only [= Finset.mem_Icc]


def A_equiv_B [NeZero n] : Equiv (A n) (B n) := {
  toFun := transform_A_to_B n
  invFun := transform_B_to_A n
  left_inv x := by
    unfold transform_A_to_B transform_B_to_A
    refine SetCoe.ext ?_
    simp only
    rw [<-Perm.mul_apply, Perm.mul_def, trans_eq_refl_iff_eq_symm.mpr] <;> simp
  right_inv := fun ⟨⟨x, k⟩, h⟩ ↦ by
    unfold transform_A_to_B transform_B_to_A
    simp only [Subtype.mk.injEq, Prod.mk.injEq]
    and_intros
    · rw [<-Perm.mul_apply, Perm.mul_def, trans_eq_refl_iff_eq_symm.mpr]
      · simp
      · congr
        simp_rw [partial_cycle.symm.apply_of_eq n _ _ 1 rfl]
        unfold B at h
        simp only [Subtype.forall, Set.mem_setOf_eq] at h
        replace h := (h k (by grind)).mp rfl
        rw [unique_ndiff] at h
        simp_rw [<-h]
        simp only [Subtype.coe_eta]
        refine (Nat.eq_sub_of_add_eq ?_)
        let k_add_1 : Finset.Icc 1 (2*n) := ⟨k+1, by grind⟩
        simp_rw [show ↑k + 1 = k_add_1.val by grind]
        simp only [Subtype.coe_eta, SetLike.coe_eq_coe]
        rw [Eq.comm, apply_eq_iff_eq_symm_apply, symm_symm]
        rw [partial_cycle.symm.apply_of_gt n _ _ _ (by unfold k_add_1; simp)]
    · simp_rw [partial_cycle.symm.apply_of_eq n _ _ 1 rfl]
      unfold B at h
      simp only [Subtype.forall, Set.mem_setOf_eq] at h
      replace h := (h k (by grind)).mp rfl
      rw [unique_ndiff] at h
      simp_rw [<-h]
      simp only [Subtype.coe_eta]
      rw [<-Subtype.val_inj]
      refine Eq.symm (Nat.eq_sub_of_add_eq ?_)
      let k_add_1 : Finset.Icc 1 (2*n) := ⟨k+1, by grind⟩
      simp_rw [show ↑k + 1 = k_add_1.val by grind]
      simp only [Subtype.coe_eta, SetLike.coe_eq_coe]
      rw [Eq.comm, apply_eq_iff_eq_symm_apply, symm_symm]
      rw [partial_cycle.symm.apply_of_gt n _ _ _ (by unfold k_add_1; simp)]
}

def embed_B : (B n) ↪ {x | T n x} := {
  toFun b := by
    let ⟨⟨x, k⟩, h⟩ := b
    use x
    unfold T
    use k, ?_
    · unfold B at h
      simp only [Subtype.forall, Set.mem_setOf_eq] at h
      apply (h _ _).mp rfl
      grind
    · grind
  inj' x1 x2 e := by
    simp at e
    have eq_perm : x1.val.1 = x2.val.1 := by exact Equiv.coe_inj.mp (congrArg DFunLike.coe e)
    apply Subtype.ext
    apply Prod.ext
    · exact eq_perm
    · let p1 := x1.prop
      let p2 := x2.prop
      unfold B at p1 p2
      simp only [Subtype.forall, Set.mem_setOf_eq] at p1 p2
      let := (p1 x2.val.2 (by grind))
      simp only [SetLike.coe_eq_coe] at this
      rw [this]
      let := (p1 x1.val.2 (by grind)).mp rfl
      rw [eq_perm]
      apply (p2 x2.val.2 (by grind)).mp
      rfl
}

theorem embed_B.not_Surjective [NeZero n] : ¬ Function.Surjective (embed_B n) := by
  let npos := Nat.pos_of_neZero n
  rw [Function.Surjective, not_forall]
  let swap2 (i : Finset.Icc 1 (2*n)) : Finset.Icc 1 (2*n) :=
    if i.val = 2 then
      ⟨1+n, by grind⟩
    else if i.val = 1+n then
      ⟨2, by grind⟩
    else
      i
  let x : Perm (Finset.Icc 1 (2*n)) := {
    toFun := swap2
    invFun := swap2
    left_inv i := by
      unfold swap2
      split_ifs <;> grind
    right_inv i := by
      unfold swap2
      split_ifs <;> grind
  }
  have Tx1 : |(x ⟨1, by grind⟩ : ℤ) - (x ⟨1+1, by grind⟩ : ℤ)| = n := by
    unfold x swap2
    simp only [coe_fn_mk, OfNat.one_ne_ofNat, ↓reduceIte, Nat.left_eq_add, Nat.reduceAdd,
      Nat.cast_add, Nat.cast_one]
    rw [ite_eq_right_iff.mpr (by grind)]
    simp
  use ⟨x, by unfold T; exists 1, (by grind)⟩
  by_contra ⟨⟨⟨y, k⟩, h⟩, h'⟩
  unfold embed_B at h'
  simp at h'
  subst y
  unfold B at h
  simp only [Subtype.forall, Set.mem_setOf_eq] at h
  let := (h k (by grind)).mp rfl
  unfold x swap2 at this
  simp only [coe_fn_mk, Nat.reduceEqDiff] at this
  split_ifs at this <;> grind

theorem embed_B.card [NeZero n] : (B n).ncard < {x | T n x}.ncard := by
  rw [<-Set.ncard_coe, <-Set.ncard_image_of_injective Set.univ (embed_B n).injective]
  apply Set.ncard_lt_card
  simp only [Set.coe_setOf, Set.image_univ, ne_eq]
  rw [Set.range_eq_univ]
  apply embed_B.not_Surjective

snip end


problem imo1989_p6 (npos : 0 < n) : {x | T n x}.ncard > {x | ¬ T n x}.ncard := by
  have : NeZero n := NeZero.of_pos npos
  calc
    _ > (B n).ncard := by
      exact embed_B.card n
    _ = (A n).ncard := by
      rw [Set.ncard_congr']
      exact (A_equiv_B n).symm
    _ = _ := by rw [A]


end Imo1989P6
