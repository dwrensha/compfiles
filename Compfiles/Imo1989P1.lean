/-
Copyright (c) 2025 Francesco Vercellesi· All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Francesco Vercellesi
-/

import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Finite.Card
import Mathlib.Data.Int.Star
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Finset.Fin

import ProblemExtraction

set_option backward.isDefEq.respectTransparency false

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 1989, Problem 1

Prove that the integers from 1 to 1989 can be partitioned in 117 sets
of 17 elements each, all with the same sum of elements.
-/

namespace Imo1989P1

abbrev S := Finset.Icc 1 1989

snip begin

lemma s_equiv : S = Finset.Ioc 0 1989 := rfl

@[simp] def avg := 995

structure PreSolution where
  A : Fin 117 → Set ℕ
  center : ∃ i, avg ∈ A i
  disjoint (i j : Fin 117) (hij : i ≠ j) : Disjoint (A i) (A j)
  odd_card (i : Fin 117) : Odd (Set.ncard (A i))
  card_bound (i : Fin 117) : Set.ncard (A i) ≤ 17
  mean (i : Fin 117) : ∑ᶠ a ∈ A i, a = Set.ncard (A i) * avg
  symm (i : Fin 117) (k : ℕ) : k ∈ A i → ∃ ℓ, (2 * avg - k) ∈ A ℓ
  subset (i : Fin 117) : A i ⊆ S

structure PreSolution' (i : Fin 117) where
  presol : PreSolution
  fill : ∀ j > i, Set.ncard (presol.A j) = 17

structure PreSolution'' (i : Fin 117) where
  presol : PreSolution
  fill : ∀ j ≥ i, Set.ncard (presol.A j) = 17

def pre_solution : PreSolution := by
  let sol : Fin 117 → Set ℕ := λ i =>
    if i = 0
    then { avg }
    else if Odd i.val
    then { avg + i + 150, avg + i + 151, avg - 2 * i - 301 }
    else { avg - i - 149, avg - i - 150, avg + 2 * i + 299 }
  have card_sol (i : Fin 117) (hi : i ≠ 0) : Set.ncard (sol i) = 3 := by
    simp_all only [Fin.isValue, ne_eq, avg, ↓reduceIte, sol]
    split_ifs
    · refine Set.ncard_eq_three.mpr ⟨995 + ↑i + 150, 995 + ↑i + 151, 995 - 2 * ↑i - 301, ?_⟩
      split_ands; (any_goals omega); simp
    · refine Set.ncard_eq_three.mpr ⟨995 - ↑i - 149, 995 - ↑i - 150, 995 + 2 * ↑i + 299, ?_⟩
      split_ands; (any_goals omega); simp
  refine ⟨sol, ?_, λ i j h => ?_, λ i => ?_, λ i => ?_, λ i => ?_, λ i k => ?_, λ i => ?_⟩
  · exact ⟨0, by simp_all [sol]⟩
  · unfold sol
    split_ifs with _ _ _ hi _ hj
    any_goals (simp_all; try split_ands; any_goals omega)
    · exact mt (congr_arg (λ x => x % 2)) <| by
        conv => arg 1; lhs; rw [Nat.add_mod]; arg 1; arg 1; try rw [Nat.add_mod]
        conv => arg 1; rhs; rw [Nat.add_mod]; arg 1; arg 1; try rw [Nat.add_mod]
        simp [Nat.odd_iff.mp hi, Nat.odd_iff.mp hj]
    · exact mt (congr_arg (λ x => x % 2)) <| by
        conv => arg 1; lhs; rw [Nat.add_mod]; arg 1; arg 1; try rw [Nat.add_mod]
        conv => arg 1; rhs; rw [Nat.add_mod]; arg 1; arg 1; try rw [Nat.add_mod]
        simp [Nat.odd_iff.mp hi, Nat.odd_iff.mp hj]
    · exact mt (congr_arg (λ x => (Int.ofNat x) % 2)) <| by
        have eq₁ : 995 - (i : ℤ) - 150 = Int.ofNat (995 - i - 150) := by
          rw [sub_right_comm, Nat.sub_right_comm]
          simp only [Int.reduceSub, Nat.reduceSub, Int.ofNat_eq_natCast]
          exact (Int.ofNat_sub (by by_contra!; have := i.isLt; omega)).symm
        have eq₂ : 995 - (j : ℤ) - 149 = Int.ofNat (995 - j - 149) := by
          rw [sub_right_comm, Nat.sub_right_comm]
          simp only [Int.reduceSub, Nat.reduceSub, Int.ofNat_eq_natCast]
          exact (Int.ofNat_sub (by by_contra!; have := i.isLt; omega)).symm
        rw [←eq₁, ←eq₂]
        conv => arg 1; lhs; rw [Int.sub_emod]; arg 1; arg 1; try rw [Int.sub_emod]
        conv => arg 1; rhs; rw [Int.sub_emod]; arg 1; arg 1; try rw [Int.sub_emod]
        have ⟨v₁, h₁⟩ := hi
        have ⟨v₂, h₂⟩ := (by assumption : Even j.val)
        simp [Int.even_iff.mp (⟨v₁, by omega⟩ : Even (i : ℤ)), Int.even_iff.mp (⟨v₂, by omega⟩ : Even (j : ℤ))]
    · exact mt (congr_arg (λ x => (Int.ofNat x) % 2)) <| by
        have eq₁ : 995 - (i : ℤ) - 149 = Int.ofNat (995 - i - 149) := by
          rw [sub_right_comm, Nat.sub_right_comm]
          simp only [Int.reduceSub, Nat.reduceSub, Int.ofNat_eq_natCast]
          exact (Int.ofNat_sub (by by_contra!; have := i.isLt; omega)).symm
        have eq₂ : 995 - (j : ℤ) - 150 = Int.ofNat (995 - j - 150) := by
          rw [sub_right_comm, Nat.sub_right_comm]
          simp only [Int.reduceSub, Nat.reduceSub, Int.ofNat_eq_natCast]
          exact (Int.ofNat_sub (by by_contra!; have := i.isLt; omega)).symm
        rw [←eq₁, ←eq₂]
        conv => arg 1; lhs; rw [Int.sub_emod]; arg 1; arg 1; try rw [Int.sub_emod]
        conv => arg 1; rhs; rw [Int.sub_emod]; arg 1; arg 1; try rw [Int.sub_emod]
        have ⟨v₁, h₁⟩ := hi
        have ⟨v₂, h₂⟩ := (by assumption : Even j.val)
        simp [Int.even_iff.mp (⟨v₁, by omega⟩ : Even (i : ℤ)), Int.even_iff.mp (⟨v₂, by omega⟩ : Even (j : ℤ))]
  · exact if h : i = 0 then (by simp_all [sol]) else (by rw [card_sol i h]; exact ⟨1, rfl⟩)
  · exact if h : i = 0 then (by simp_all [sol]) else (by simp_all [card_sol i h])
  · exact if h : i = 0 then (by simp_all [sol]) else by
      rw [card_sol i h]
      simp only [Fin.isValue, avg, Nat.reduceMul, sol]
      split_ifs
      all_goals
        rw [finsum_mem_insert, finsum_mem_insert, finsum_mem_singleton]
        any_goals omega
        all_goals (simp; try omega)
  · exact if h : i = 0 then (by simp_all only [sol]; exact λ eq ↦ ⟨0, by simp_all⟩) else by
      simp only [Fin.isValue, avg, Nat.reduceMul, sol]
      split_ifs with hi
      · intro hk
        use i + 1
        have eq : (i + 1).val = i.val + 1 := by
          apply Fin.val_add_one_of_lt
          rw [Fin.lt_last_iff_ne_last]
          simp only [Nat.reduceAdd, Fin.reduceLast, ne_eq, Fin.isValue]
          by_contra abs
          rw [abs] at hi
          have : Even 116 := ⟨58, rfl⟩
          have := Nat.even_xor_odd 116
          contradiction
        simp_all only [Set.mem_insert_iff, Set.mem_singleton_iff]
        rcases hk with hk | hk | hk
        all_goals
          split_ifs with hz hp
          · rw [Fin.ext_iff, eq] at hz
            simp_all
          · have := Nat.odd_add_one.mp hp
            contradiction
          · rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff, hk]
            omega
      · intro hk
        use i - 1
        have eq : (i - 1).val = i.val - 1 := Fin.val_sub_one_of_ne_zero h
        simp_all only [Set.mem_insert_iff, Set.mem_singleton_iff]
        rcases hk with hk | hk | hk
        all_goals
          split_ifs with hz hp
          · rw [Fin.ext_iff, eq] at hz
            have : i.val = 1 := by omega
            have : Odd i.val := ⟨0, by omega⟩
            contradiction
          · rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff, hk]
            omega
          · have := (not_iff_not.mpr (Nat.odd_sub (by omega : 1 ≤ i))).mp hp
            simp_all
  · have : i.val ≥ 0 := i.zero_le
    have : i.val < 117 := i.isLt
    simp only [Fin.isValue, avg, Finset.coe_Icc, sol]
    split_ifs <;> (simp [Set.insert_subset_iff]; try omega)

set_option maxHeartbeats 400000 in
noncomputable def fill_element (i : Fin 117) (presol : PreSolution' i) : PreSolution'' i := by
  have ⟨presol, hpresol⟩ := presol
  refine if h : Set.ncard (presol.A i) = 17 then ⟨presol, λ j hj ↦ if h : i = j then (by simp_all) else by simp_all [hpresol j (by grind)]⟩ else ?_
  have finite (i : Fin 117) : (presol.A i).Finite := by
    apply Set.finite_of_ncard_pos
    apply Nat.zero_lt_of_ne_zero
    by_contra! abs
    have : Even (presol.A i).ncard := by simp_all
    have : Odd (presol.A i).ncard := presol.odd_card i
    simp_all
  let used := Finset.biUnion (Finset.Icc 0 116) (λ i => (finite i).toFinset)
  let rem := S \ used
  have hi₁ : i ≤ 116 := by grind

  have rem_symm (x : ℕ) (hx : x ≤ 1990) : x ∈ rem ↔ 2 * avg - x ∈ rem := by
    have arr (x : ℕ) : x ∈ rem → 2 * avg - x ∈ rem := by
      simp_all only [gt_iff_lt, Fin.isValue, Finset.mem_sdiff, Finset.mem_Icc, avg, Nat.reduceMul,
        tsub_le_iff_right, and_imp, rem]
      exact λ _ _ h₁ => ⟨by lia, λ h₂ ↦ by
        have ⟨w, ⟨hw, hw'⟩⟩ := Finset.mem_biUnion.mp h₂
        rw [Set.Finite.mem_toFinset] at hw'
        have ⟨ℓ, hℓ⟩ := presol.symm w (1990 - x) hw'
        simp_all only [Fin.isValue, Finset.mem_Icc, Fin.zero_le, true_and, avg, Nat.reduceMul,
          Nat.sub_sub_self (by lia : x ≤ 1990)]
        have : ℓ ≤ 116 := by grind
        have : x ∈ used := Finset.mem_biUnion.mpr ⟨ℓ, ⟨by simp_all, by simp_all⟩⟩
        contradiction⟩
    exact ⟨arr x, λ h ↦ by
      have res := arr (2 * avg - x)
      conv_rhs at res => rw [Nat.sub_sub_self (by simp_all : x ≤ 2 * avg)]
      exact res h⟩

  have n : rem.Nonempty := by
    by_contra! abs
    have : (presol.A i).ncard < 17 := lt_of_le_of_ne (presol.card_bound i) h
    have dq : used.card < S.card := calc
      used.card ≤ _ := Finset.card_biUnion_le
      _ < ∑ i ∈ Finset.Icc 0 116, 17 := Finset.sum_lt_sum
        (λ j hj ↦ by rw [←Set.ncard_eq_toFinset_card _ (finite j)]; exact presol.card_bound j)
        ⟨i, ⟨by simp_all, by rw [←Set.ncard_eq_toFinset_card _ (finite i)]; exact lt_of_le_of_ne (presol.card_bound i) h⟩⟩
      _ ≤ _ := by simp
    unfold rem at abs
    rw [Finset.sdiff_eq_empty_iff_subset, Finset.subset_iff_eq_of_card_le (le_of_lt dq)] at abs
    have : S ≠ used := mt (congr_arg Finset.card) (ne_of_gt dq)
    simp_all

  have n₁ : (rem ∩ Finset.Ioc avg 1989).Nonempty := by
    have ⟨v, hv⟩ := n
    have hv₁ : v < 1990 := by
      have : v ∈ S := by grind
      simp_all
      grind
    exact if h : v > avg then ⟨v, by simp_all [rem]⟩ else by
      have : 2 * avg - v ∉ used := λ abs ↦ by
        have ⟨w, ⟨hw₁, hw₂⟩⟩ := Finset.mem_biUnion.mp abs
        rw [Set.Finite.mem_toFinset] at hw₂
        have ⟨w', hw'⟩ := presol.symm w (2 * avg - v) hw₂
        have : w' ≤ 116 := by grind
        simp only [avg, Nat.reduceMul, Nat.sub_sub_self hv₁.le] at hw'
        have : v ∈ used := Finset.mem_biUnion.mpr ⟨w', ⟨by simp_all, by simpa [Set.Finite.mem_toFinset]⟩⟩
        have : v ∉ rem := by grind
        contradiction
      have : v < avg := by
        refine lt_of_le_of_ne (Nat.le_of_not_lt h) λ h ↦ ?_
        have : v ∉ used := by simp_all [used]
        have ⟨x, hx⟩ := presol.center
        have : x ≤ 116 := Fin.succ_le_succ_iff.mp x.prop
        have : avg ∈ used := Finset.mem_biUnion.mpr ⟨x, ⟨by simp_all, by aesop⟩⟩
        grind
      exact ⟨2 * avg - v, by simp_all [rem]; lia⟩
  have n₂ : (rem ∩ Finset.Ioo 0 avg).Nonempty := by
    have ⟨v, hv⟩ := n
    have : v < 1990 := by
      have : v ∈ S := by grind
      simp_all
      grind
    exact if h : v < avg then ⟨v, by simp_all [rem]; omega⟩ else by
      have : 2 * avg - v ∉ used := λ abs ↦ by
        have ⟨w, ⟨hw₁, hw₂⟩⟩ := Finset.mem_biUnion.mp abs
        rw [Set.Finite.mem_toFinset] at hw₂
        have ⟨w', hw'⟩ := presol.symm w (2 * avg - v) hw₂
        have : w' ≤ 116 := by grind
        simp only [avg, Nat.reduceMul, Nat.sub_sub_self (by omega : v ≤ 1990)] at hw'
        have : v ∈ used := Finset.mem_biUnion.mpr ⟨w', ⟨by simp_all, by simpa [Set.Finite.mem_toFinset]⟩⟩
        have : v ∉ rem := by grind
        contradiction
      have : v > avg := by
        refine lt_of_le_of_ne (by omega) λ h ↦ ?_
        have : v ∉ used := by grind
        have ⟨x, hx⟩ := presol.center
        have : x ≤ 116 := by grind
        have : avg ∈ used := Finset.mem_biUnion.mpr ⟨x, ⟨by simp_all, by aesop⟩⟩
        grind
      exact ⟨2 * avg - v, by simp_all [rem]; omega⟩
  let x₁ := (rem ∩ Finset.Ioc avg 1989).min' n₁
  let x₂ := (rem ∩ Finset.Ioo 0 avg).max' n₂

  have : x₁ ≠ x₂ := by
    have := (Finset.mem_inter.mp ((rem ∩ Finset.Ioc avg 1989).min'_mem n₁)).2
    have := (Finset.mem_inter.mp ((rem ∩ Finset.Ioo 0 avg).max'_mem n₂)).2
    have : x₁ > avg := by simp_all [x₁]
    have : x₂ < avg := by simp_all [x₂]
    omega

  have : x₁ + x₂ = 1990 := by
    have diff : x₂ = 1990 - x₁ := by
      simp_all only [gt_iff_lt, Fin.isValue, avg, Nat.reduceMul, ne_eq, x₁, x₂]
      rw [Finset.max'_eq_iff]
      constructor
      · refine Finset.mem_inter.mpr ⟨?_, ?_⟩
        · have mem := (Finset.mem_inter.mp ((rem ∩ Finset.Ioc avg 1989).min'_mem n₁)).1
          have := (Finset.mem_inter.mp ((rem ∩ Finset.Ioc avg 1989).min'_mem n₁)).2
          refine (rem_symm ((rem ∩ Finset.Ioc avg 1989).min' n₁) ?_).mp mem
          simp_all
          omega
        · have := (Finset.mem_inter.mp ((rem ∩ Finset.Ioc avg 1989).min'_mem n₁)).2
          refine Finset.mem_Ioc.mpr ⟨?_, ?_⟩
          · simp_all; omega
          · simp_all
            have : (rem ∩ Finset.Ioc 995 1989).min' n₁ > 995 := by simp_all
            omega
      · intro b hb
        by_contra! abs
        have ⟨hb₁, hb₂⟩ := Finset.mem_inter.mp hb
        have : 1990 - b > 995 := by simp_all; omega
        have : 1990 - b < (rem ∩ Finset.Ioc 995 1989).min' n₁ := by grind
        have := (((rem ∩ Finset.Ioc 995 1989).min'_eq_iff n₁ ((rem ∩ Finset.Ioc 995 1989).min' n₁)).mp rfl).2 (1990 - b) (by
          have := (rem_symm b (by grind)).mp hb₁
          simp
          grind)
        linarith
    have := (Finset.mem_inter.mp ((rem ∩ Finset.Ioc avg 1989).min'_mem n₁)).2
    have := (Nat.eq_add_of_sub_eq (by unfold x₁; simp_all; grind) (id diff.symm)).symm
    grind

  have not_in₁ : ∀ x ≤ 116, x₁ ∉ presol.A x := by
    have := (Finset.mem_inter.mp ((rem ∩ Finset.Ioc avg 1989).min'_mem n₁)).1
    have abs : x₁ ∉ used := by grind
    rw [Finset.mem_biUnion, not_exists] at abs
    simp_all
  have not_in₂ : ∀ x ≤ 116, x₂ ∉ presol.A x := by
    have := (Finset.mem_inter.mp ((rem ∩ Finset.Ioo 0 avg).max'_mem n₂)).1
    have abs : x₂ ∉ used := by grind
    rw [Finset.mem_biUnion, not_exists] at abs
    simp_all

  let merged_fun : Fin 117 → Set ℕ := λ j ↦ if i ≠ j then presol.A j else (presol.A j) ∪ { x₁, x₂ }
  let merge_presol : PreSolution := by
    refine ⟨merged_fun, ?_, λ i' j h => ?_, λ i' => ?_, λ i' => ?_, λ i' => ?_, λ i' k hk => ?_, λ i' => ?_⟩
    · have ⟨w, hw⟩ := presol.center
      use w
      exact if h : i ≠ w then (by simp_all [merged_fun]) else (by simp_all [merged_fun])
    · exact if hi' : i' = i then
        if hj : j = i then (by simp_all) else by
          simp_all [merged_fun, presol.disjoint i j (by grind), not_in₁ j (by grind), not_in₂ j (by grind)]
      else
        if hj : j = i
        then by
          have : ¬(i = i') := by grind
          simp_all [merged_fun, presol.disjoint i' i (by grind), not_in₁ i' (by grind), not_in₂ i' (by grind)]
        else by
          have : ¬(i = i') := by grind
          have : ¬(i = j) := Ne.intro fun a ↦ hj a.symm
          simp_all [merged_fun, presol.disjoint i' j h]
    · exact if hi' : i = i'
        then by
          have : (insert x₂ (presol.A i')).ncard = (presol.A i').ncard + 1 :=
            Set.ncard_insert_of_notMem (not_in₂ i' (Fin.succ_le_succ_iff.mp i'.prop)) (finite i')
          have : (insert x₁ (insert x₂ (presol.A i'))).ncard = (insert x₂ (presol.A i')).ncard + 1 :=
            Set.ncard_insert_of_notMem (by simp_all) (by simp_all)
          simp_all [merged_fun, presol.odd_card i']
        else by simp_all [merged_fun, presol.odd_card i']
    · exact if hi' : i = i'
        then by
          have : (presol.A i').ncard ≠ 16 := λ h ↦ by
            have := presol.odd_card i'
            have : Even (presol.A i').ncard := ⟨8, by simp_all⟩
            have := Nat.even_xor_odd 16
            simp_all
          have := presol.card_bound i'
          simp_all [merged_fun]
          omega
        else by simp_all [merged_fun, presol.card_bound i']
    · exact if hi' : i = i'
        then by
          simp_all only [gt_iff_lt, Fin.isValue, avg, Nat.reduceMul, ne_eq, Set.union_insert,
            Set.union_singleton, ite_not, ↓reduceIte, Set.mem_insert_iff, or_self,
            not_false_eq_true, Set.finite_insert, Set.ncard_insert_of_notMem, merged_fun]
          conv => arg 1; arg 1; intro a; rw [←Set.mem_insert_iff, ←Set.mem_insert_iff]
          rw [finsum_mem_insert _ (by simp_all [not_in₁ i']) (by simp_all)]
          rw [finsum_mem_insert _ (by simp_all [not_in₂ i']) (by simp_all)]
          rw [←add_assoc]
          simp_all [presol.mean i']
          omega
        else by simp_all [merged_fun, presol.mean i']
    · exact if hi' : i = i'
        then by
          simp_all only [gt_iff_lt, Fin.isValue, avg, Nat.reduceMul, ne_eq, Set.union_insert,
            Set.union_singleton, ite_not, ↓reduceIte, Set.mem_insert_iff, merged_fun]
          rcases hk with hk' | hk' | hk'
          · use i'; simp_all; omega
          · use i'; simp_all; omega
          · have ⟨ℓ, hℓ⟩ := presol.symm i' k (by simp_all)
            use ℓ
            simp_all
            split_ifs <;> simp_all
        else by
          have ⟨ℓ, hℓ⟩ := presol.symm i' k (by simp_all [merged_fun])
          use ℓ
          simp_all [merged_fun]
          split_ifs <;> simp_all
    · unfold merged_fun
      split_ifs
      · exact presol.subset i'
      · refine Set.union_subset (presol.subset i') <| by
          apply Set.insert_subset
          · unfold x₁
            have mem := (rem ∩ Finset.Ioc avg 1989).min'_mem n₁
            have inc : (rem ∩ Finset.Ioc avg 1989) ⊆ S := (λ v hv ↦ by
              exact (by rw [s_equiv]; exact Finset.Ioc_subset_Ioc (by simp) (by rfl) : Finset.Ioc avg 1989 ⊆ S) (Finset.mem_inter.mp hv).2)
            exact inc mem
          · unfold x₂
            have mem := (rem ∩ Finset.Ioo 0 avg).max'_mem n₂
            have inc : (rem ∩ Finset.Ioo 0 avg) ⊆ S := (λ v hv ↦ by
              exact (by rw [s_equiv]; exact Finset.Ioc_subset_Ioc (by rfl) (by simp) : Finset.Ioc 0 avg ⊆ S) (Finset.Ioo_subset_Ioc_self (Finset.mem_inter.mp hv).2))
            exact Set.singleton_subset_iff.mpr (inc mem)
  exact fill_element i ⟨merge_presol, λ j hj ↦ by
    simp_all only [gt_iff_lt, ne_eq, Set.union_insert, Set.union_singleton, ite_not, merged_fun,
      merge_presol]
    split_ifs
    · omega
    · exact hpresol j hj⟩
termination_by 17 - (presol.presol.A i).ncard
decreasing_by
  have eq₂ : (insert x₂ (presol.A i)).ncard = (presol.A i).ncard + 1 :=
    Set.ncard_insert_of_notMem (not_in₂ i (Fin.le_def.mpr hi₁)) (finite i)
  have eq₁ : (insert x₁ (insert x₂ (presol.A i))).ncard = (insert x₂ (presol.A i)).ncard + 1 :=
    Set.ncard_insert_of_notMem (by simp_all) (by simp_all)
  simp only [ne_eq, not_true_eq_false, ↓reduceDIte, Fin.isValue, avg, Set.union_insert,
    Set.union_singleton, gt_iff_lt]
  rw [eq₂] at eq₁
  unfold x₁ x₂ rem used avg at eq₁
  rw [eq₁]
  have := presol.card_bound i
  exact Nat.sub_lt_sub_left (Nat.lt_of_le_of_ne this h) (by omega)

noncomputable def fill (i : Fin 117) (presol : PreSolution) : PreSolution'' i :=
  if h : i = 116 then fill_element i ⟨presol, by grind⟩ else by
    have fill_next := fill (i + 1) presol
    have fill_next : PreSolution' i := ⟨fill_next.presol, λ j hj ↦ fill_next.fill j (by omega)⟩
    exact fill_element i fill_next
  termination_by 116 - i
  decreasing_by omega

snip end

problem imo1989_p1 : ∃ (A : Fin 117 → Set ℕ),
    S = ⨆ i : Fin 117, A i ∧
    ∀ i j, i ≠ j → Disjoint (A i) (A j) ∧
    Set.ncard (A i) = 17 ∧
    ∑ᶠ a ∈ A i, a = ∑ᶠ a ∈ A j, a := by
  have sol := fill 0 pre_solution
  refine ⟨sol.presol.A, ?_, λ i j hij ↦ ⟨?_, ?_, ?_⟩⟩
  · symm
    apply Set.Finite.eq_of_subset_of_card_le
    · simp [Set.finite_Icc 1 1989]
    · have := λ i ↦ sol.presol.subset i
      simp_all
    · have := Set.ncard_iUnion_of_finite (s := sol.presol.A)
        (λ i ↦ (Set.finite_Icc 1 1989).subset (by have := sol.presol.subset i; simp_all))
        (λ i j hij ↦ by simp [Function.onFun, sol.presol.disjoint i j hij])
      have : ∑ᶠ (i : Fin 117), 17 = 117 * 17 := by simp [finsum_eq_sum_of_fintype]
      simp_all [sol.fill]
  · exact sol.presol.disjoint i j hij
  · rw [sol.fill i (Fin.zero_le i)]
  · rw [sol.presol.mean i, sol.presol.mean j, sol.fill i (by grind), sol.fill j (by grind)]


end Imo1989P1
