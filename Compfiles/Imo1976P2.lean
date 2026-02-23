/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Constantin Seebach
-/

import Mathlib
import ProblemExtraction


problem_file

/-!
# International Mathematical Olympiad 1976, Problem 2

Let $P_{1}(x) = x^{2} - 2$ and $P_{j}(x) = P_{1}(P_{j - 1}(x))$ for $j= 2,\ldots$.
Show that for any positive integer $n,$ the roots of the equation $P_{n}(x) = x$ are real and distinct.
-/

namespace Imo1976P2

open Polynomial

noncomputable def P (j : ℕ) : ℝ[X] :=
  match j with
  | 0 => 0
  | 1 => X^2 - 2
  | j+2 => (P 1).comp (P (j+1))


snip begin

theorem all_real_roots (P : ℝ[X]) (rs : Finset ℝ) (hrs : ∀ x ∈ rs, IsRoot P x) (hc : rs.card = P.natDegree) : P.aroots ℂ = (rs.image Complex.ofReal).val := by
  wlog nontrivial : P ≠ 0
  · rw [ne_eq, not_not] at nontrivial
    subst P
    simp at hc
    subst rs
    simp
  rw [eq_comm]
  apply Multiset.eq_of_le_of_card_le
  · rw [Multiset.le_iff_subset (by simp)]
    intro r hr
    simp only [Finset.image_val, Multiset.mem_dedup, Multiset.mem_map, Finset.mem_val] at hr
    let ⟨x, ⟨hx1, hx2⟩⟩ := hr
    refine mem_aroots.mpr ⟨nontrivial, ?_⟩
    rw [<-hx2, <-Complex.coe_algebraMap, aeval_algebraMap_apply_eq_algebraMap_eval, hrs _ hx1]
    simp
  · rw [IsAlgClosed.card_aroots_eq_natDegree]
    rw [Finset.image_val, Multiset.dedup_eq_self.mpr, Multiset.card_map, Finset.card_val]
    · rw [hc]
    · rw [Finset.nodup_map_iff_injOn]
      simp


theorem root_of_sign_flip {α : Type} [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]
  {δ : Type} [Ring δ] [LinearOrder δ] [TopologicalSpace δ] [OrderClosedTopology δ] [AddLeftMono δ] [MulPosMono δ] [PosMulMono δ] {a b : α}
  (hab : a ≤ b) {f : α → δ} (hf : ContinuousOn f (Set.Icc a b)) (hs : f a * f b < 0) : ∃ r ∈ Set.Ioo a b, f r = 0 := by
    if fafb : f a < f b then
      have := intermediate_value_Ioo hab hf
      have hz : 0 ∈ Set.Ioo (f a) (f b) := by
        simp
        contrapose! hs
        by_cases fann : 0 ≤ f a
        · apply le_mul_of_le_mul_of_nonneg_left _ (le_of_lt fafb) fann
          positivity
        · simp at fann
          have := hs fann
          rw [<-neg_mul_neg]
          apply le_mul_of_le_mul_of_nonneg_right (b:=-f b)
          · simp [<-sq]
            apply sq_nonneg
          · simp [le_of_lt fafb]
          · simp [this]
      exact this hz
    else
      simp at fafb
      have := intermediate_value_Ioo' hab hf
      have hz : 0 ∈ Set.Ioo (f b) (f a) := by
        simp
        contrapose! hs
        by_cases fann : 0 ≤ f b
        · apply le_mul_of_le_mul_of_nonneg_right _ fafb fann
          positivity
        · simp at fann
          have := hs fann
          rw [<-neg_mul_neg]
          apply le_mul_of_le_mul_of_nonneg_left (c:=-f a)
          · simp [<-sq]
            apply sq_nonneg
          · simp [fafb]
          · simp [this]
      exact this hz


theorem P_natDegree (n : ℕ) (npos : 0 < n) : (P n).natDegree = 2^n := by
  fun_induction P
  · simp at npos
  · simp [<-C_ofNat]
  · expose_names
    rw [natDegree_comp]
    rw [ih1, ih2, pow_succ _ (j+1)]
    · ring
    · simp
    · simp


structure NicePlotOfP (n : ℕ) (npos : 0 < n) where
  k : ℕ := (P n).natDegree + 1
  len : k = (P n).natDegree + 1 := by simp [P_natDegree]
  x : Fin k → ℝ
  strictMono : StrictMono x := by simp
  y_eq : ∀ i, (P n).eval (x i) = (-1)^i.val * 2
  x_first : x ⟨0, Nat.lt_of_sub_eq_succ len⟩ = -2 := by simp
  x_last : x ⟨k-1, by simp [len]⟩ = 2 := by simp


theorem NicePlotOfP.findRoot {n} {npos} (pl : NicePlotOfP n npos) (i:ℕ) (hi : i+1 < pl.k) :
    ∃ r ∈ Set.Ioo (pl.x ⟨i, by lia⟩) (pl.x ⟨i+1, hi⟩), IsRoot (P n) r := by
  let a := pl.x ⟨i, by lia⟩
  let b := pl.x ⟨i+1, hi⟩
  let f := fun x => (P n).eval x
  have f_cont : Continuous f := Polynomial.continuous_eval₂ _ _
  have aleb : a ≤ b := by
    unfold a b
    apply pl.strictMono.monotone
    simp
  have fafb : f a * f b < 0 := by
    unfold f a b
    rw [pl.y_eq, pl.y_eq, pow_succ]
    simp
  let ⟨r, hr1, hr2⟩ := root_of_sign_flip aleb f_cont.continuousOn fafb
  use r, hr1
  grind only [IsRoot]

theorem NicePlotOfP.findRoot.spec_gt {n} {npos} (pl : NicePlotOfP n npos) (i:ℕ) (hi : i+1 < pl.k) (i') (e : i'.val = i) :
    (pl.x i') < (NicePlotOfP.findRoot pl i hi).choose := by
  let := Exists.choose_spec (NicePlotOfP.findRoot pl i hi)
  conv =>
    lhs
    rw [show i' = ⟨i, by lia⟩ by simp_rw [<-e]]
  exact (Set.mem_Ioo.mpr this.left).left

theorem NicePlotOfP.findRoot.spec_lt {n} {npos} (pl : NicePlotOfP n npos) (i:ℕ) (hi : i+1 < pl.k) (i') (e : i'.val = i+1)  :
    (NicePlotOfP.findRoot pl i hi).choose < (pl.x i') := by
  let := Exists.choose_spec (NicePlotOfP.findRoot pl i hi)
  conv =>
    rhs
    rw [show i' = ⟨i+1, hi⟩ by simp_rw [<-e]]
  exact (Set.mem_Ioo.mpr this.left).right

theorem NicePlotOfP.findRoot.spec_root {n} {npos} (pl : NicePlotOfP n npos) (i:ℕ) (hi : i+1 < pl.k) :
    IsRoot (P n) (NicePlotOfP.findRoot pl i hi).choose := by
  let := Exists.choose_spec (NicePlotOfP.findRoot pl i hi)
  exact this.right


theorem Fin.val_orderSucc_of_notTop {n : ℕ} (i : Fin (n+1)) (hi : i ≠ ⊤) : (Order.succ i).val = i+1 := by
  rw [show i = (Fin.mk i (Fin.val_lt_last hi)).castSucc by simp]
  rw [Fin.orderSucc_castSucc]
  simp


noncomputable def makePlot (n : ℕ) (npos : 0 < n) : NicePlotOfP n npos :=
  match n with
  | 1 => {
    x := ![-2, 0, 2]
    y_eq := by
      intro i
      unfold P
      match i with
      | 0 => simp; field
      | 1 => simp
      | 2 => simp; field
  }
  | n+2 => {
    k : ℕ := (P (n+2)).natDegree + 1
    x := fun ⟨i, hi⟩ =>
      let pl' := (makePlot (n+1) (Nat.zero_lt_succ n))
      if pa : Even i then
        have : i/2 < pl'.k := by
          rw [pl'.len]
          rw [P_natDegree] at hi ⊢
          · grind only
          · exact Nat.zero_lt_succ n
          · exact Nat.lt_add_of_pos_left npos
        pl'.x ⟨i/2, this⟩
      else
        have : (i-1)/2+1 < pl'.k := by
          rw [pl'.len]
          rw [P_natDegree] at hi ⊢
          · grind only [Nat.pow_pos, = Nat.even_iff]
          · exact Nat.zero_lt_succ n
          · exact Nat.lt_add_of_pos_left npos
        (pl'.findRoot _ this).choose
    strictMono := by
      apply strictMono_of_lt_succ
      intro i hi
      rw [isMax_iff_eq_top] at hi
      if pa : Even i.val then
        simp_rw [Fin.val_orderSucc_of_notTop _ hi]
        have pa' : ¬ Even (i.val+1) := by grind only [= Nat.even_iff]
        simp only [pa, ↓reduceDIte, pa']
        apply NicePlotOfP.findRoot.spec_gt
        simp
      else
        simp_rw [Fin.val_orderSucc_of_notTop _ hi]
        have pa' :Even (i.val+1) := by grind only [= Nat.even_iff]
        simp only [pa, ↓reduceDIte, pa']
        apply NicePlotOfP.findRoot.spec_lt
        rw [<-mul_left_inj' (c:=2) (by simp), add_mul]
        rw [Nat.div_two_mul_two_of_even, Nat.div_two_mul_two_of_even] <;> grind only [= Nat.even_iff]
    y_eq := by
      intro i
      simp only [Set.mem_Ioo, IsRoot.def]
      split_ifs with pa
      · conv =>
          lhs
          arg 2
          unfold P
          arg 1
          unfold P
        rw [eval_comp]
        rw [@NicePlotOfP.y_eq (n+1)]
        simp only [eval_sub, eval_pow, eval_X, eval_ofNat]
        rw [(neg_one_pow_eq_one_iff_even (by linarith)).mpr pa]
        rw [mul_pow, <-pow_mul]
        rw [(neg_one_pow_eq_one_iff_even (by linarith)).mpr _]
        · linarith
        · simp
      · conv =>
          lhs
          arg 2
          unfold P
          arg 1
          unfold P
        rw [eval_comp]
        simp only [eval_sub, eval_pow, eval_X, eval_ofNat]
        rw [show eval _ (P (n + 1)) = 0 by {
          rw [<-IsRoot]
          apply NicePlotOfP.findRoot.spec_root
        }]
        rw [(neg_one_pow_eq_neg_one_iff_odd (by linarith)).mpr (Nat.not_even_iff_odd.mp pa)]
        simp
    x_first := by
      simp [NicePlotOfP.x_first]
    x_last := by
      simp only
      rw [dite_eq_left_iff.mpr]
      · rw [<-@NicePlotOfP.x_last (n+1) (Nat.zero_lt_succ n) ?_]
        · congr 2
          · rfl
          · rfl
          · rw [NicePlotOfP.len, P_natDegree, P_natDegree]
            · grind
            · simp
            · simp
          · apply proof_irrel_heq
      · intro h
        simp [P_natDegree] at h
        grind only [= Nat.odd_iff]
  }


theorem P_intersect_X {n : ℕ} {npos : 0 < n} (pl : NicePlotOfP n npos) (i : ℕ) (hi : i ∈ Finset.range ((P n).natDegree-1)) :
    ∃ r ∈ Set.Ioo (pl.x ⟨i, by grind [pl.len]⟩) (pl.x ⟨i+1, by grind [pl.len]⟩), (P n - X).eval r = 0 := by
  let a := pl.x ⟨i, by grind [pl.len]⟩
  let b := pl.x ⟨i+1, by grind [pl.len]⟩
  let f (x:ℝ) := (P n - X).eval x
  have f_cont : Continuous f := Polynomial.continuous_eval₂ _ _
  have aleb : a ≤ b := by
    unfold a b
    apply pl.strictMono.monotone
    grind
  have h1 : {(P n).eval a, (P n).eval b} = ({-2, 2} : Finset ℝ) := by
    rw [pl.y_eq, pl.y_eq]
    by_cases pa : Even i
    · rw [(neg_one_pow_eq_one_iff_even _).mpr _, (neg_one_pow_eq_neg_one_iff_odd _).mpr _] <;> grind
    · rw [(neg_one_pow_eq_neg_one_iff_odd _).mpr _, (neg_one_pow_eq_one_iff_even _).mpr _] <;> grind
  have : -2 ≤ a ∧ a < 2 := by
    rw [<-pl.x_first, <-pl.x_last]
    and_intros
    · apply pl.strictMono.monotone
      simp
    · apply pl.strictMono
      grind only [= Finset.mem_range, = Lean.Grind.toInt_fin]
  have : 0 < i → -2 < a  := by
    intro ih'
    rw [<-pl.x_first]
    apply pl.strictMono
    grind only [= Finset.mem_range, = Lean.Grind.toInt_fin]
  have : -2 < b ∧ b < 2 := by
    rw [<-pl.x_first, <-pl.x_last]
    and_intros <;> {
      apply pl.strictMono
      grind only [= Finset.mem_range, = Lean.Grind.toInt_fin, pl.len]
    }
  have fafb : f a * f b < 0 := by
    unfold f
    rw [eval_sub, eval_X, eval_sub, eval_X]
    if iz : i = 0 then
      subst i
      conv =>
        lhs
        args
        · args
          · rw [pl.y_eq]
          · unfold a
            rw [pl.x_first]
        · arg 1
          rw [pl.y_eq]
      simp
      nlinarith
    else
      suffices (eval a (P n) - a) < 0 ∧ (eval b (P n) - b) > 0 ∨ (eval a (P n) - a) > 0 ∧ (eval b (P n) - b) < 0 by
        apply this.elim <;> {intro _; nlinarith}
      suffices (P n).eval a = -2 ∧ (P n).eval b = 2 ∨ (P n).eval a = 2 ∧ (P n).eval b = -2 by
        grind
      repeat rw [pl.y_eq]
      by_cases pa : Even i
      · rw [(neg_one_pow_eq_one_iff_even _).mpr _, (neg_one_pow_eq_neg_one_iff_odd _).mpr _] <;> grind
      · rw [(neg_one_pow_eq_neg_one_iff_odd _).mpr _, (neg_one_pow_eq_one_iff_even _).mpr _] <;> grind
  let ⟨r, hr1, hr2⟩ := root_of_sign_flip aleb f_cont.continuousOn fafb
  use r

theorem P_intersect_X.spec_gt {n} {npos} (pl : NicePlotOfP n npos) (i:ℕ) (hi : i ∈ Finset.range ((P n).natDegree-1))(i') (e : i'.val = i) :
    (pl.x i') < (P_intersect_X pl i hi).choose := by
  let := Exists.choose_spec (P_intersect_X pl i hi)
  grind only [= Set.mem_Ioo]

theorem P_intersect_X.spec_lt {n} {npos} (pl : NicePlotOfP n npos) (i:ℕ) (hi : i ∈ Finset.range ((P n).natDegree-1)) (i') (e : i'.val = i+1) :
    (P_intersect_X pl i hi).choose < (pl.x i') := by
  let := Exists.choose_spec (P_intersect_X pl i hi)
  grind only [= Set.mem_Ioo]

theorem P_intersect_X.spec_root {n} {npos} (pl : NicePlotOfP n npos) (i:ℕ) (hi : i ∈ Finset.range ((P n).natDegree-1)) :
    IsRoot (P n - X) (P_intersect_X pl i hi).choose := by
  let := Exists.choose_spec (P_intersect_X pl i hi)
  exact this.right


snip end

problem imo1976_p2 (n : ℕ) (npos : 0 < n) :
    (∀ (r : ℂ), r ∈ aroots (P n - X) ℂ → r.im = 0) ∧ (aroots (P n - X) ℂ).Nodup := by
  suffices ∃ rs : Finset ℝ, rs.card = (P n - X).natDegree ∧ ∀ r ∈ rs, IsRoot (P n - X) r by
    let ⟨rs, h1, h2⟩ := this
    rw [all_real_roots (P n - X) rs h2 ?_] <;> simp [h1]
  let pl := makePlot n npos
  use {2} ∪ (Finset.range ((P n).natDegree-1)).attach.image (fun i => (P_intersect_X pl i.val i.prop).choose)
  and_intros
  · have : 2 ≤ (P n).natDegree := by
      rw [P_natDegree _ npos]
      exact Nat.le_pow npos
    rw [Finset.card_union_of_disjoint, Finset.card_image_of_injOn, natDegree_sub_eq_left_of_natDegree_lt]
    · rw [Finset.card_attach, Finset.card_range, Finset.card_singleton]
      lia
    · rw [natDegree_X]
      lia
    · simp only [Finset.coe_attach, Set.injOn_univ]
      apply StrictMono.injective
      intro i j iltj
      calc
        _ < pl.x ⟨i.val+1, by grind [NicePlotOfP.len]⟩ := by
          apply P_intersect_X.spec_lt _ _ i.prop
          simp
        _ ≤ pl.x ⟨j, by grind [NicePlotOfP.len]⟩ := by
          apply pl.strictMono.monotone
          simp [iltj]
        _ < _ := by
          apply P_intersect_X.spec_gt _ _ j.prop
          simp
    · simp only [Finset.mem_image, Finset.mem_attach, true_and,
        Subtype.exists, not_exists, Finset.disjoint_singleton_left]
      intro i hi
      apply ne_of_lt
      calc
        _ < pl.x ⟨i+1, by grind [NicePlotOfP.len]⟩ := by
          apply P_intersect_X.spec_lt _ _ hi
          simp
        _ ≤ pl.x ⟨pl.k-1, by grind [NicePlotOfP.len]⟩ := by
          apply pl.strictMono.monotone
          grind [NicePlotOfP.len]
        _ = _ := by
          rw [<-pl.x_last]
  · simp only [Set.mem_Ioo, Finset.singleton_union,
      Finset.mem_insert, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists,
      IsRoot.def, forall_eq_or_imp, forall_exists_index]
    and_intros
    · rw [eval_sub, eval_X]
      nth_rw 1 [<-pl.x_last, pl.y_eq]
      simp [pl.len, P_natDegree _ npos]
      rw [(neg_one_pow_eq_one_iff_even _).mpr] <;> grind only [= Nat.even_iff, usr Nat.div_pow_of_pos]
    · intro r i hi er
      subst r
      apply P_intersect_X.spec_root _ _ hi

end Imo1976P2
