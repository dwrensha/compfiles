/-
Copyright (c) 2025 Roozbeh Yousefzadeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roozbeh Yousefzadeh
-/

import Mathlib
import Mathlib.Tactic

import ProblemExtraction

problem_file {
  tags := [.Algebra]
  importedFrom :=
    "https://github.com/roozbeh-yz/IMO-Steps/blob/main/imo_proofs/imo_1978_p5.lean",
}


/-!
# International Mathematical Olympiad 1978, Problem 5

Let a_k be a sequence of distinct positive integers for k = 1,2,3, ...

Prove that for all natural numbers n, we have:

sum_{k=1}^{n} a(k)/(k^2) >= sum_{k=1}^{n} (1/k).
-/

open Finset

namespace Imo1978P5

snip begin

lemma aux_1
  (n : ℕ)
  (f : ℕ → ℕ)
  (h₀ : ∀ (m : ℕ), 0 < m → 0 < f m)
  (h₁ : ∀ (p q : ℕ), 0 < p → 0 < q → p ≠ q → f p ≠ f q)
  (h₂ : 0 < n) :
  ∑ k ∈ Finset.Icc 1 n, ((k):ℝ) / (k) ^ 2 ≤ ∑ k ∈ Finset.Icc 1 n, ((f k):ℝ) / (k) ^ 2 := by
  let s := Finset.Icc 1 n
  let f₀ : ℕ → ℝ := fun k => 1 / (k:ℝ) ^ 2
  let f₁ : ℕ → ℝ := fun k => (k:ℝ)
  let f₂ : ℕ → ℝ := fun k => ((f k):ℝ)
  have h₃: ∑ k ∈ Icc 1 n, ((k):ℝ) / (k) ^ 2 = ∑ k ∈ Icc 1 n, f₁ k • f₀ k := by
    refine Finset.sum_congr rfl ?_
    intro x _
    rw [div_eq_mul_one_div, smul_eq_mul]
  have h₄: ∑ k ∈ Icc 1 n, ((f k):ℝ) / (k) ^ 2 = ∑ k ∈ Icc 1 n, f₂ k • f₀ k := by
    refine Finset.sum_congr rfl ?_
    intro x _
    rw [div_eq_mul_one_div, smul_eq_mul]
  let sf : Finset ℝ := Finset.image f₂ (Finset.Icc 1 n)
  set sf_sorted : List ℝ := sf.sort (fun (x₁ x₂) => x₁ ≤ x₂) with hf₁
  let f₃: ℕ → ℝ := fun k => sf_sorted.getD (k - 1) 0
  have hf₀: ∀ k, f₃ k = sf_sorted.getD (k - 1) 0 := by exact fun k => rfl
  have hf₂: sf = Finset.image f₂ s := by rfl
  have hf₃: f₂ = fun k => ((f k):ℝ) := by rfl
  have hl₁: s.card = n := by
    have g₀: s = Icc 1 n := by rfl
    rw [g₀]
    refine Nat.le_induction ?_ ?_ n h₂
    · simp
    · simp
  have hf₄: sf_sorted.length = n ∧ (sort (image f s) (fun x₁ x₂ => x₁ ≤ x₂) ).length = n := by
    have hl₂: sf.card = n := by
      rw [← hl₁]
      refine Finset.card_image_of_injOn ?_
      intro p hp₀ q hq₀ hpq
      have hf₅: f₂ = fun k => ((f k):ℝ) := by rfl
      contrapose! hpq
      rw [hf₅]
      simp only [ne_eq, Nat.cast_inj]
      refine h₁ p q ?_ ?_ hpq
      · norm_cast at hp₀
        apply Finset.mem_Icc.mp at hp₀
        exact hp₀.1
      · norm_cast at hq₀
        apply Finset.mem_Icc.mp at hq₀
        exact hq₀.1
    have hl₃: (image f s).card = n := by
      rw [← hl₁]
      refine Finset.card_image_of_injOn ?_
      intro p hp₀ q hq₀ hpq
      contrapose! hpq
      refine h₁ p q ?_ ?_ hpq
      · norm_cast at hp₀
        apply Finset.mem_Icc.mp at hp₀
        exact hp₀.1
      · norm_cast at hq₀
        apply Finset.mem_Icc.mp at hq₀
        exact hq₀.1
    constructor
    · rw [← hl₂]
      exact length_sort fun x₁ x₂ => x₁ ≤ x₂
    · rw [← hl₃]
      exact length_sort fun x₁ x₂ => x₁ ≤ x₂
  have hf₅: ∀ a ∈ s, a - 1 < sf_sorted.length := by
    intro a ha₀
    rw [hf₄.1]
    apply Finset.mem_Icc.mp at ha₀
    omega
  have hf₆: ∀ k ∈ s, 1 ≤ f₃ k := by
    have hs₂: ∀ k ∈ sf_sorted, 1 ≤ k := by
      rw [hf₁, hf₂, hf₃]
      simp only [mem_sort, mem_image, forall_exists_index, and_imp,
                 forall_apply_eq_imp_iff₂, Nat.one_le_cast]
      intro k hk₀
      apply Finset.mem_Icc.mp at hk₀
      exact h₀ k hk₀.1
    have hs₃: ∀ k ∈ s, f₃ k ∈ sf_sorted := by
      intro k hk₀
      rw [hf₀]
      have hk₁: k - 1 < sf_sorted.length := by exact hf₅ k hk₀
      rw [List.getD_eq_getElem sf_sorted 0 hk₁]
      exact List.getElem_mem hk₁
    intro k hk₀
    exact hs₂ (f₃ k) (hs₃ k hk₀)
  have hf₇: ∀ a : ℕ, a ∈ Icc 1 n → ∀ b : ℕ, b ∈ Icc 1 n → a < b → f₃ a + 1 ≤ f₃ b := by
    intro a ha₀ b hb₀ hab
    rw [hf₀, hf₀]
    have ha₁: a - 1 < sf_sorted.length := by exact hf₅ a ha₀
    have hb₁: b - 1 < sf_sorted.length := by exact hf₅ b hb₀
    rw [hf₁, hf₂]
    let sfo : Finset ℕ := image f s
    have hso₂: ∀ k ∈ s, ((image f₂ s).sort (fun x₁ x₂ => x₁ ≤ x₂)).getD (k - 1) 0
      = ((image f s).sort (fun x₁ x₂ => x₁ ≤ x₂)).getD (k - 1) 0 := by
      intro k hk₀
      have hk₃: Function.Injective f₁ := CharZero.cast_injective
      let fe : ℕ ↪ ℝ := {toFun := f₁ , inj' := hk₃}
      have hk₅: ((image f₂ s).sort (fun x₁ x₂ => x₁ ≤ x₂)) =
        List.map f₁ ((image f s).sort (fun x₁ x₂ => x₁ ≤ x₂)) := by
        have hh₀: fe = {toFun := f₁ , inj' := hk₃} := by rfl
        have hh₁: (image f₂ s) = Finset.map fe (image f s) := by
          rw [hf₃, hh₀]
          refine Finset.induction_on_min s ?_ ?_
          · simp
          · intro z sz _ hz₁
            simp only [image_insert, map_insert, Function.Embedding.coeFn_mk]
            exact congrArg (insert ↑(f z)) hz₁
        rw [hh₁]
        refine Finset.induction_on_min (image f s) ?_ ?_
        · simp
        · intro z sz hz₀ hz₁
          have hz₂: z ∉ sz := by
            contrapose! hz₀
            use z
          simp only [map_insert]
          have hz₃: fe z = (z:ℝ) := by exact rfl
          rw [hz₃]
          have hz₄: ∀ b ∈ sz, (fun x₁ x₂ => x₁ ≤ x₂) z b := by
            intro b a
            exact Nat.le_of_succ_le (hz₀ b a)
          have hz₅: ∀ b ∈ map fe sz, (fun x₁ x₂ => x₁ ≤ x₂) (↑z:ℝ) b := by
            intro y hy₀
            have hy₁: ∃ d:ℕ, d ∈ sz ∧ (d:ℝ) = y := by exact Multiset.mem_map.mp hy₀
            obtain ⟨d, hd₀, hd₁⟩ := hy₁
            refine le_of_lt ?_
            rw [← hd₁]
            exact Nat.cast_lt.mpr (hz₀ d hd₀)
          have hz₆: (↑z:ℝ) ∉ map fe sz := by
            simp only [mem_map, not_exists, not_and]
            intro x hx₀
            rw [hh₀]
            simp only [Function.Embedding.coeFn_mk]
            have hx₁: ∀ x:ℕ, f₁ x = (x:ℝ) := by exact fun x => rfl
            rw [hx₁]
            norm_cast
            exact Nat.ne_of_lt' (hz₀ x hx₀)
          rw [Finset.sort_insert (fun x₁ x₂ => x₁ ≤ x₂) hz₄ hz₂]
          rw [Finset.sort_insert (fun x₁ x₂ => x₁ ≤ x₂) hz₅ hz₆]
          simp only [List.map_cons, List.cons.injEq]
          exact List.cons_eq_cons.mp (congrArg (List.cons ↑z) hz₁)
      have hk₁: k - 1 < (List.map f₁ (sfo.sort (fun x₁ x₂ => x₁ ≤ x₂))).length := by
        rw [← hk₅]
        exact hf₅ k hk₀
      have hk₂: k - 1 < (sfo.sort (fun x₁ x₂ => x₁ ≤ x₂)).length := by
        rw [hf₄.2, ← hf₄.1]
        exact hf₅ k hk₀
      rw [hk₅, List.getD_eq_getElem _ 0 hk₁, List.getD_eq_getElem _ 0 hk₂]
      exact List.getElem_map f₁
    rw [hso₂ a ha₀, hso₂ b hb₀]
    norm_cast
    refine Nat.succ_le_of_lt ?_
    have ha₂: a - 1 < ((image f s).sort (fun x₁ x₂ => x₁ ≤ x₂)).length := by
      rw [hf₄.2, ← hf₄.1]
      exact ha₁
    have hb₂: b - 1 < ((image f s).sort (fun x₁ x₂ => x₁ ≤ x₂)).length := by
      rw [hf₄.2, ← hf₄.1]
      exact hb₁
    rw [List.getD_eq_getElem _ 0 ha₂, List.getD_eq_getElem _ 0 hb₂]
    refine List.Pairwise.rel_get_of_lt ?_ ?_
    · have := Finset.sortedLT_sort (image f s)
      rw [List.sortedLT_iff_pairwise] at this
      exact this
    simp only [Fin.mk_lt_mk]
    apply Finset.mem_Icc.mp at ha₀
    apply Finset.mem_Icc.mp at hb₀
    lia
  have hρ: ∃ ρ: Equiv.Perm ℕ, (∀ a ∈ Icc 1 n, f₂ a = f₃ (ρ a)) ∧ ∀ a ∉ Icc 1 n, ρ a = a := by
    let so : Finset ℕ := image f (Icc 1 n)
    let lo_sorted : List ℕ := so.sort (fun x₁ x₂ => x₁ ≤ x₂)
    let sl := List.range' 1 n 1
    have hs₀: sl = List.range' 1 n 1 := by rfl
    let lo : List ℕ := List.map f sl
    let f₄ : ℕ → ℕ := fun k => lo_sorted.getD (k - 1) 0
    let f₅ : ℕ → ℕ := fun k => (List.findIdx (fun x => x = f k) lo_sorted) + 1
    let f₆ : ℕ → ℕ := fun k => ite (k ∈ s) (f₅ k) (k)
    let f₈ : ℕ → ℕ := fun k => (List.findIdx (fun x => x = f₄ k) lo) + 1
    let f₉ : ℕ → ℕ := fun k => ite (k ∈ s) (f₈ k) (k)
    have gg₀: f₄ = fun k => lo_sorted.getD (k - 1) 0 := by rfl
    have gg₁: f₅ = fun k => List.findIdx (fun x => decide (x = f k)) lo_sorted + 1 := by rfl
    have gg₂: f₆ = fun k => if k ∈ s then f₅ k else k := by rfl
    have gg₃: f₈ = fun k => (List.findIdx (fun x => x = f₄ k) lo) + 1 := by rfl
    have gg₄: f₉ = fun k => ite (k ∈ s) (f₈ k) (k) := by rfl
    have gg₅: ∀ k ∈ s, f₆ k = f₅ k := by
      intro k hk₀
      rw [gg₂]
      simp only [ite_eq_left_iff]
      intro hk₁
      exact False.elim (hk₁ hk₀)
    have gg₆: ∀ k ∈ s, f₉ k = f₈ k := by grind
    have gg₇: ∀ k ∉ s, f₆ k = k := by grind
    have gg₈: ∀ k ∉ s, f₉ k = k := by grind
    have gg₉: lo_sorted.length = n := by grind
    have gg₁₀: ∀ k ∈ s, f₅ k ∈ s := by
      intro k hk₀
      refine Finset.mem_Icc.mpr ?_
      constructor
      · exact Nat.le_add_left 1 (List.findIdx (fun y => decide (y = f k)) lo_sorted)
      · have hk₁: List.findIdx (fun x => decide (x = f k)) lo_sorted < lo_sorted.length := by
          refine List.findIdx_lt_length.mpr ?_
          use (f k)
          constructor
          · refine (mem_sort fun x₁ x₂ => x₁ ≤ x₂).mpr ?_
            exact mem_image_of_mem f hk₀
          · exact of_decide_eq_self_eq_true (f k)
        rw [gg₉] at hk₁
        refine Nat.le_of_lt_succ ?_
        exact Nat.add_lt_of_lt_sub hk₁
    have gg₁₁: lo.length = n := by
      have g₀: lo = List.map f sl := by rfl
      rw [g₀, hs₀]
      simp
    have gg₁₂: ∀ k ∈ s, f₈ k ∈ s := by
      intro k hk₀
      refine Finset.mem_Icc.mpr ?_
      constructor
      · exact Nat.le_add_left 1 (List.findIdx (fun x => decide (x = f₄ k)) lo)
      · have hk₁: List.findIdx (fun x => decide (x = f₄ k)) lo < lo.length := by
          refine List.findIdx_lt_length.mpr ?_
          use (f₄ k)
          constructor
          · have hk₁: k - 1 < lo.length := by
              rw [gg₁₁]
              apply Finset.mem_Icc.mp at hk₀
              exact Nat.sub_one_lt_of_le hk₀.1 hk₀.2
            have hk₂: lo_sorted = so.sort (fun x₁ x₂ => x₁ ≤ x₂) := by rfl
            have hk₃: lo = List.map f sl := by rfl
            rw [gg₀, hk₂, hk₃]
            ring_nf
            have hk₄: so = image f (Icc 1 n) := by rfl
            rw [gg₁₁, ← gg₉, hk₂, hk₄] at hk₁
            rw [List.getD_eq_getElem _ 0 hk₁]
            let j : ℕ := ((image f (Icc 1 n)).sort (fun x₁ x₂ => x₁ ≤ x₂))[k - 1]
            have hj₀: j = ((image f (Icc 1 n)).sort (fun x₁ x₂ => x₁ ≤ x₂))[k - 1] := by rfl
            have hj₁: j ∈ ((image f (Icc 1 n)).sort (fun x₁ x₂ => x₁ ≤ x₂)) := List.getElem_mem hk₁
            have hj₂: j ∈ image f s := by exact (mem_sort fun x₁ x₂ => x₁ ≤ x₂).mp hj₁
            rw [← hj₀]
            exact List.mem_dedup.mp hj₂
          · exact of_decide_eq_self_eq_true (f₄ k)
        rw [gg₁₁] at hk₁
        refine Nat.le_of_lt_succ ?_
        exact Nat.add_lt_of_lt_sub hk₁
    have gg₁₃: sf_sorted = List.map f₁ lo_sorted := by
      have g₀: Function.Injective f₁ := by exact CharZero.cast_injective
      let fe : ℕ ↪ ℝ := {toFun := f₁ , inj' := g₀}
      have hh₀: fe = {toFun := f₁ , inj' := g₀} := by rfl
      have hh₁: (image f₂ s) = Finset.map fe (image f s) := by
        rw [hf₃, hh₀]
        refine Finset.induction_on_min s ?_ ?_
        · simp
        · intro z sz _ hz₁
          simp only [image_insert, map_insert, Function.Embedding.coeFn_mk]
          exact congrArg (insert ↑(f z)) hz₁
      have g₁: lo_sorted = so.sort (fun x₁ x₂ => x₁ ≤ x₂) := by rfl
      have g₂: so = image f s := by rfl
      rw [hf₁, hf₂, g₁, g₂, hh₁]
      refine Finset.induction_on_min (image f s) ?_ ?_
      · simp
      · intro z sz hz₀ hz₁
        have hz₂: z ∉ sz := by
          contrapose! hz₀
          use z
        simp only [map_insert]
        have hz₃ : fe z = (z:ℝ) := rfl
        rw [hz₃]
        have hz₄: ∀ b ∈ sz, (fun x₁ x₂ => x₁ ≤ x₂) z b := by
          simp only
          exact fun b a => Nat.le_of_succ_le (hz₀ b a)
        have hz₅: ∀ b ∈ map fe sz, (fun x₁ x₂ => x₁ ≤ x₂) (↑z:ℝ) b := by
          intro y hy₀
          have hy₁: ∃ d:ℕ, d ∈ sz ∧ (d:ℝ) = y := by exact Multiset.mem_map.mp hy₀
          obtain ⟨d, hd₀, hd₁⟩ := hy₁
          refine le_of_lt ?_
          rw [← hd₁]
          exact Nat.cast_lt.mpr (hz₀ d hd₀)
        have hz₆: (↑z:ℝ) ∉ map fe sz := by
          simp only [mem_map, not_exists, not_and]
          intro x hx₀
          rw [hh₀]
          simp only [Function.Embedding.coeFn_mk]
          have hx₁: ∀ x:ℕ, f₁ x = (x:ℝ) := by exact fun x => rfl
          rw [hx₁]
          norm_cast
          exact Nat.ne_of_lt' (hz₀ x hx₀)
        rw [Finset.sort_insert (fun x₁ x₂ => x₁ ≤ x₂) hz₄ hz₂]
        rw [Finset.sort_insert (fun x₁ x₂ => x₁ ≤ x₂) hz₅ hz₆]
        simp only [List.map_cons, List.cons.injEq]
        exact List.cons_eq_cons.mp (congrArg (List.cons ↑z) hz₁)
    have gg₁₄: ∀ x y, x ∈ s → y ∈ s → f₄ x = f₄ y → x = y := by
      intro x y hx₀ hy₀ hx₁
      have hx₂: List.Nodup lo_sorted := by exact sort_nodup so (fun x₁ x₂ => x₁ ≤ x₂)
      rw [gg₀] at hx₁
      ring_nf at hx₁
      have hx₃: x - 1 < lo_sorted.length := by
        rw [gg₉]
        apply Finset.mem_Icc.mp at hx₀
        exact Nat.sub_one_lt_of_le hx₀.1 hx₀.2
      have hy₁: y - 1 < lo_sorted.length := by
        rw [gg₉]
        apply Finset.mem_Icc.mp at hy₀
        exact Nat.sub_one_lt_of_le hy₀.1 hy₀.2
      rw [List.getD_eq_getElem _ 0 hx₃, List.getD_eq_getElem _ 0 hy₁] at hx₁
      have hj₉: x - 1 = y - 1 := by
        exact (List.Nodup.getElem_inj_iff hx₂).mp hx₁
      apply Finset.mem_Icc.mp at hy₀
      apply Finset.mem_Icc.mp at hx₀
      rw [← Nat.sub_add_cancel hy₀.1, ← Nat.sub_add_cancel hx₀.1]
      exact congrFun (congrArg HAdd.hAdd hj₉) 1
    have hh₀: ∀ k ∈ s, f₄ (f₆ k) = f k := by
      intro k hk₀
      have g₀: f₆ k = f₅ k := gg₅ k hk₀
      rw [g₀, gg₁]
      simp only
      let j := List.findIdx (fun x => decide (x = f k)) lo_sorted
      have hj₀: j + 1 = List.findIdx (fun x => decide (x = f k)) lo_sorted + 1 := by rfl
      have hj₁: List.findIdx (fun x => decide (x = f k)) lo_sorted < lo_sorted.length := by
        refine List.findIdx_lt_length.mpr ?_
        simp only [decide_eq_true_eq, exists_eq_right]
        refine (mem_sort fun x₁ x₂ => x₁ ≤ x₂).mpr ?_
        exact mem_image_of_mem f hk₀
      have hj₂: f₄ (j + 1) = f k := by
        let p := (fun (x) => decide (x = f k))
        have hp₀: p = (fun (x) => decide (x = f k)) := by rfl
        rw [gg₀, hj₀]
        ring_nf
        rw [add_comm 1, Nat.add_sub_cancel]
        rw [← hp₀]
        rw [← hp₀] at hj₁
        rw [List.getD_eq_getElem _ 0 hj₁]
        have g₁: p lo_sorted[List.findIdx p lo_sorted] = true := by
          exact List.findIdx_getElem
        refine decide_eq_true_iff.mp g₁
      rw [← hj₀, hj₂]
    have gg₁₅: ∀ x y, x ∈ s → y ∈ s → (f₄ x = f y ↔ f₈ x = y) := by
      intro x y hx₀ hy₀
      have hy₁: y - 1 < lo.length := by
        rw [gg₁₁]
        apply Finset.mem_Icc.mp at hy₀
        exact Nat.sub_one_lt_of_le hy₀.1 hy₀.2
      have hy₃: y - 1 < (List.range' 1 n 1).length := by
        rw [List.length_range', ← gg₁₁]
        exact hy₁
      have hy₄: y - 1 < sl.length := by
        rw [hs₀]
        exact hy₃
      have gg₁₆: lo = List.map f sl := by rfl
      constructor
      · intro hx₁
        have hx₂: f₄ (f₆ y) = f y := by exact hh₀ y hy₀
        have hx₃: x = f₅ y := by
          rw [← hx₁, gg₅ y hy₀] at hx₂
          exact gg₁₄ x (f₅ y) hx₀ (gg₁₀ y hy₀) (id (Eq.symm hx₂))
        rw [hx₃]
        apply Finset.mem_Icc.mp at hx₀
        apply Finset.mem_Icc.mp at hy₀
        have hx₄: x - 1 < lo_sorted.length := by
          rw [gg₉]
          exact Nat.sub_one_lt_of_le hx₀.1 hx₀.2
        have hx₅: List.findIdx (fun x => decide (x = f y)) lo_sorted = x - 1 :=
          Nat.eq_sub_of_add_eq hx₃.symm
        apply (List.findIdx_eq hx₄).mp at hx₅
        obtain ⟨hx₅, hx₆⟩ := hx₅
        simp at hx₅ hx₆
        rw [gg₃]
        simp only
        rw [← Nat.sub_add_cancel hy₀.1]
        refine add_right_cancel_iff.mpr ?_
        refine (List.findIdx_eq hy₁).mpr ?_
        simp only [decide_eq_true_eq, decide_eq_false_iff_not]
        constructor
        · rw [Nat.sub_add_cancel hy₀.1]
          apply Finset.mem_Icc.mpr at hy₀
          rw [← gg₅ y hy₀, hh₀ y hy₀]
          rw [← List.getD_eq_getElem lo 0 hy₁, gg₁₆]
          rw [List.getD_eq_getElem (List.map f sl) 0 hy₁]
          simp only [List.getElem_map]
          refine congr rfl ?_
          have g₀: sl = List.range' 1 n 1 := by rfl
          rw [← List.getD_eq_getElem sl 0 hy₄, g₀]
          rw [List.getD_eq_getElem (List.range' 1 n 1) 0 hy₃]
          rw [List.getElem_range' hy₃]
          lia
        · intro j hj₀
          rw [Nat.sub_add_cancel hy₀.1]
          apply Finset.mem_Icc.mpr at hy₀
          rw [← gg₅ y hy₀, hh₀ y hy₀]
          have hj₁: j < lo.length := by exact Nat.lt_trans hj₀ hy₁
          have hj₂: j < (List.map f sl).length := by exact Nat.lt_trans hj₀ hy₁
          have hj₃: j < sl.length := by exact Nat.lt_trans hj₀ hy₃
          have hj₄: j < (List.range' 1 n 1).length := by exact Nat.lt_trans hj₀ hy₃
          rw [← List.getD_eq_getElem lo 0 hj₁, gg₁₆]
          rw [List.getD_eq_getElem (List.map f sl) 0 hj₂]
          simp only [List.getElem_map, ne_eq]
          refine h₁ sl[j] y ?_ ?_ ?_
          · have ht: ∀ t ∈ sl, 1 ≤ t := by
              intro t ht₀
              apply List.mem_range'.mp at ht₀
              omega
            refine ht sl[j] ?_
            exact List.getElem_mem hj₄
          · omega
          · rw [List.getElem_range' hj₃]
            omega
      · intro hx₁
        have hx₃: f (f₈ x) = f₄ x := by
          rw [hx₁]
          rw [gg₃] at hx₁
          simp only at hx₁
          have hy₅: List.findIdx (fun x_1 => decide (x_1 = f₄ x)) lo = y - 1 :=
            Nat.eq_sub_of_add_eq hx₁
          apply (List.findIdx_eq hy₁).mp at hy₅
          obtain ⟨hy₅, hy₆⟩ := hy₅
          simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hy₅ hy₆
          rw [← hy₅]
          have hy₇: lo[y - 1] = (List.map f sl)[y - 1] := by
            rw [← List.getD_eq_getElem (List.map f sl) 0 hy₁, ← gg₁₆]
          rw [hy₇]
          apply Finset.mem_Icc.mp at hy₀
          simp only [List.getElem_map]
          refine congr rfl ?_
          have g₀: sl = List.range' 1 n 1 := by rfl
          rw [← List.getD_eq_getElem sl 0 hy₄, g₀]
          rw [List.getD_eq_getElem (List.range' 1 n 1) 0 hy₃]
          rw [List.getElem_range' hy₃]
          rw [one_mul, add_comm 1, Nat.sub_add_cancel hy₀.1]
        rw [← hx₃]
        exact congrArg f hx₁
    have hh₁: ∀ x, (f₉ ∘ f₆) x = x := by
      intro x
      rw [Function.comp_def]
      simp only
      by_cases hx₀: x ∈ s
      · have g₀: f₅ x ∈ s := by exact gg₁₀ x hx₀
        rw [gg₅ x hx₀, gg₆ (f₅ x) g₀,]
        let j := f₅ x
        have hj₀: j = f₅ x := by rfl
        have hj₁: f₄ j = f x := by
          rw [hj₀, ← gg₅ x hx₀]
          exact hh₀ x hx₀
        exact (gg₁₅ j x (gg₁₀ x hx₀) hx₀).mp hj₁
      · have g₀: f₆ x = x := by exact gg₇ x hx₀
        have g₁: f₉ x = x := by exact gg₈ x hx₀
        rw [g₀, g₁]
    have hh₂: Function.LeftInverse f₉ f₆ := by
      refine Function.leftInverse_iff_comp.mpr ?_
      exact Function.RightInverse.id hh₁
    have hh₃: Function.RightInverse f₉ f₆ := by
      refine Function.rightInverse_iff_comp.mpr ?_
      have hh₄: ∀ x, (f₆ ∘ f₉) x = x := by
        intro x
        rw [Function.comp_def]
        simp only
        by_cases hx₀: x ∈ s
        · have g₀: f₈ x ∈ s := by exact gg₁₂ x hx₀
          rw [gg₆ x hx₀, gg₅ (f₈ x) g₀,]
          let j := f₈ x
          have hj₀: j = f₈ x := by rfl
          have hj₁: f₄ x = f j := by exact (gg₁₅ x j hx₀ (gg₁₂ x hx₀)).mpr hj₀.symm
          rw [← hj₀]
          have hj₂: j ∈ s := gg₁₂ x hx₀
          have hj₃: f₄ (f₅ j) = f j := by
            rw [← gg₅ j hj₂]
            exact hh₀ j hj₂
          rw [← hj₁] at hj₃
          exact gg₁₄ (f₅ j) x (gg₁₀ j g₀) hx₀ hj₃
        · have g₀: f₉ x = x := gg₈ x hx₀
          have g₁: f₆ x = x := gg₇ x hx₀
          rw [g₀, g₁]
      exact Function.RightInverse.id hh₄
    set ρ : Equiv.Perm ℕ := { toFun := f₆, invFun := f₉, left_inv := hh₂, right_inv := hh₃ }
    have hh₅: ∀ k ∈ s, ρ k ∈ s := by
      intro k hk₀
      have hk₁: f₆ k ∈ s := by
        rw [gg₅ k hk₀]
        exact gg₁₀ k hk₀
      exact hk₁
    use ρ
    constructor
    · intro a ha₀
      have ha₁: f₂ a = ((f a):ℝ) := by rfl
      have ha₂: f₃ (ρ a) = ((f₄ (ρ a)):ℝ) := by
        have ha₂: f₃ (ρ a) = sf_sorted.getD (ρ a - 1) 0 := by rfl
        have ha₃: f₄ (ρ a) = lo_sorted.getD (ρ a - 1) 0 := by rfl
        have ha₄: ρ a ∈ s := by exact hh₅ a ha₀
        have ha₅: ρ a - 1 < sf_sorted.length := by
          exact hf₅ (ρ a) (hh₅ a ha₀)
        have ha₆: ρ a - 1 < lo_sorted.length := by
          refine Nat.lt_of_succ_le ?_
          apply Finset.mem_Icc.mp at ha₄
          rw [gg₉, Nat.succ_eq_add_one, Nat.sub_add_cancel ha₄.1]
          exact ha₄.2
        rw [ha₂, ha₃]
        rw [gg₁₃]
        rw [gg₁₃] at ha₅
        rw [List.getD_eq_getElem _ 0 ha₅, List.getD_eq_getElem _ 0 ha₆]
        exact List.getElem_map f₁
      rw [ha₁, ha₂,]
      norm_cast
      rw [← hh₀ a ha₀]
      exact rfl
    · intro a ha₀
      exact gg₇ a ha₀
  obtain ⟨ρ, hρ₀, hρ₁⟩ := hρ
  have h₆: ∑ k ∈ Icc 1 n, f₃ k • f₀ k ≤ ∑ k ∈ Icc 1 n, f₂ k • f₀ k := by
    have h₆₀: ∑ k ∈ Icc 1 n, f₂ k • f₀ k = ∑ k ∈ Icc 1 n, f₃ (ρ k) • f₀ k := by
      refine Finset.sum_congr rfl ?_
      intro x hx₀
      rw [hρ₀ x hx₀]
    rw [h₆₀]
    refine AntivaryOn.sum_smul_le_sum_comp_perm_smul ?hfg ?hσ
    · refine MonotoneOn.antivaryOn ?hfg.hf ?hfg.hg
      · refine monotoneOn_iff_forall_lt.mpr ?hfg.hf.a
        norm_cast
        intro a ha₀ b hb₀ ha₁
        have ha₂: f₃ a + 1 ≤ f₃ b := by exact hf₇ a ha₀ b hb₀ ha₁
        refine le_trans ?_ ha₂
        refine le_of_lt ?_
        exact lt_add_one (f₃ a)
      · refine antitoneOn_iff_forall_lt.mpr ?hfg.hg.a
        norm_cast
        intro a ha₀ b hb₀ ha₁
        refine (one_div_le_one_div ?_ ?_).mpr ?_
        · apply Finset.mem_Icc.mp at hb₀
          norm_cast
          exact Nat.pow_pos hb₀.1
        · apply Finset.mem_Icc.mp at ha₀
          norm_cast
          exact Nat.pow_pos ha₀.1
        · norm_cast
          exact Nat.pow_le_pow_left (le_of_lt ha₁) 2
    · intro x hx₀
      contrapose! hx₀
      exact fun a => a (hρ₁ x hx₀)
  have h₇: ∑ k ∈ Icc 1 n, f₁ k • f₀ k ≤ ∑ k ∈ Icc 1 n, f₃ k • f₀ k := by
    refine Finset.sum_le_sum ?_
    intro x hx₀
    have hx₁: 1 ≤ x := by
      apply Finset.mem_Icc.mp at hx₀
      exact hx₀.1
    have hx₂: 0 < f₀ x := by
      ring_nf
      refine div_pos zero_lt_one ?_
      norm_cast
      exact Nat.pow_pos hx₁
    refine (smul_le_smul_iff_of_pos_right hx₂).mpr ?_
    have hh₀: f₁ = fun (k:ℕ) => (↑k:ℝ) := by rfl
    rw [hh₀]
    dsimp only
    have hi: x ≤ n → (↑x:ℝ) ≤ f₃ x := by
      refine Nat.le_induction ?_ ?_ x hx₁
      · intro _
        norm_cast
        refine hf₆ 1 ?_
        exact left_mem_Icc.mpr h₂
      · intro y hy₀ hy₁ hy₂
        have hy₃: y ≤ n := by omega
        have hy₄: f₃ y + 1 ≤ f₃ (y + 1) := by
          refine hf₇ y ?_ (y + 1) ?_ (by omega)
          · exact Finset.mem_Icc.mpr ⟨hy₀, hy₃⟩
          · refine Finset.mem_Icc.mpr ⟨Nat.le_add_right_of_le hy₀, hy₂⟩
        refine le_trans ?_ hy₄
        simp only [Nat.cast_add, Nat.cast_one, add_le_add_iff_right]
        exact hy₁ hy₃
    refine hi ?_
    apply Finset.mem_Icc.mp at hx₀
    exact hx₀.2
  rw [h₃, h₄]
  refine le_trans h₇ h₆

snip end

problem imo_1978_p5
  (n : ℕ)
  (f : ℕ → ℕ)
  (h₀ : ∀ (m : ℕ), 0 < m → 0 < f m)
  (h₁ : ∀ (p q : ℕ), 0 < p → 0 < q → p ≠ q → f p ≠ f q)
  (h₂ : 0 < n) :
  (∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / k) ≤ ∑ k ∈ Finset.Icc 1 n, ((f k):ℝ) / k ^ 2 := by
  have h₃: ∑ k ∈ Icc 1 n, ((k):ℝ) / (k) ^ 2 ≤ ∑ k ∈ Icc 1 n, ((f k):ℝ) / (k) ^ 2 := by
    exact aux_1 n f h₀ h₁ h₂
  refine le_trans ?_ h₃
  refine Finset.sum_le_sum ?_
  intro x hx₀
  rw [pow_two, ← div_div, div_self]
  apply Finset.mem_Icc.mp at hx₀
  norm_cast
  omega

end Imo1978P5
