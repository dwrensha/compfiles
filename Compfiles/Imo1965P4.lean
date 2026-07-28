/-
Copyright (c) 2025 The Compfiles Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Rydh
-/

module

public import Mathlib.Tactic

public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Algebra]
}

/-!
# International Mathematical Olympiad 1965, Problem 4

Find all sets of four real numbers x₁, x₂, x₃, x₄ such that the sum of any one
and the product of the other three is equal to 2.
-/

namespace Imo1965P4

determine solution : Set (Multiset ℝ) := {{1, 1, 1, 1}, {-1, -1, -1, 3}}

snip begin

lemma cubic {x : ℝ} (h : x^3 + x - 2 = 0) : x = 1 := by
  by_cases h : x = 1
  · exact h
  · nlinarith [sq_nonneg (x + 1/2)]

lemma multiset_erase {α : Type} [DecidableEq α] {s s' : Multiset α} (a : α) (ha : a ∈ s) :
  s.erase a = s' → s = a ::ₘ s' := fun _ ↦ by grind only [Multiset.cons_erase ha]

-- Simple lemmas about the order of elements in a specific multiset
syntax "multiset_order_tactic" : tactic
macro_rules
  | `(tactic| multiset_order_tactic) => `(tactic| (
    ext x
    by_cases h1 : x = 3 <;> simp [h1, show 3 ≠ (-1 : ℝ) by norm_num]
    by_cases h2 : x = -1 <;> simp [h1, h2, show (-1 : ℝ) ≠ 3 by norm_num]))
lemma multiset_order₁ : ({3, -1, -1, -1} : Multiset ℝ) = {-1, -1, -1, 3} := by multiset_order_tactic
lemma multiset_order₂ : ({-1, 3, -1, -1} : Multiset ℝ) = {-1, -1, -1, 3} := by multiset_order_tactic

snip end

problem imo1965_p4 : { S | S.card = 4 ∧ ∀ x ∈ S, x + (S.erase x).prod = 2 } = solution := by
  -- Solution based on https://prase.cz/kalva/imo/isoln/isoln654.html
  ext S
  constructor
  · intro ⟨hcard, hprod⟩
    have hS_nonempty : S ≠ ∅ := Multiset.card_pos.mp (by positivity)
    set t := S.prod
    have h_quadratic : ∀ x ∈ S, x^2 - 2*x + t = 0 := fun x hx ↦ by grind [Multiset.prod_erase hx]
    have ⟨x₁, hx₁⟩ := Multiset.exists_mem_of_ne_zero hS_nonempty
    by_cases h : ∀ x ∈ S, x = x₁
    --- First case: all elements are equal
    · have hS : S = {x₁, x₁, x₁, x₁} := by
        ext y
        by_cases hy : y = x₁
        · have : Multiset.count x₁ S = 4 := by grind only [Multiset.count_eq_card]
          simp [hy, this]
        · have : Multiset.count y S = 0 := by grind only [Multiset.count_eq_zero]
          simp [hy, this]
      have h_t_eq_1 : t = 1 := by
        have ht_eq : t = x₁ ^ 4 := by simp [t, hS, Multiset.prod_singleton]; ring
        have hx₁_ne_zero : x₁ ≠ 0 := by
          by_contra hz
          have : (S.erase x₁).prod = x₁^3 := by
            simp [hS, Multiset.prod_singleton]
            ring
          grind
        have h_cubic : x₁^3 + x₁ - 2 = 0 := by grind
        have h_x1_eq_1 : x₁ = 1 := cubic h_cubic
        grind
      have h_x_eq_1 : ∀ x ∈ S, x = 1 := by grind
      grind

    --- Second case: at least one element x₂ are not equal to x₁
    · -- Extract the other three elements x₂, x₃, x₄
      simp at h
      have ⟨x₂, hx₂, hx₂_ne_x₁⟩ := h
      set S₁ := S.erase x₁
      have hx₂_mem_S₁ : x₂ ∈ S₁ := (Multiset.mem_erase_of_ne hx₂_ne_x₁).mpr hx₂
      set S₂ := S₁.erase x₂
      have hS₂_card : S₂.card = 2 := by grind only [Multiset.card_erase_add_one]
      obtain ⟨x₃, hx₃⟩ := Multiset.exists_mem_of_ne_zero (Multiset.card_pos.mp (by rw [hS₂_card]; norm_num))
      have hx₃_mem_S : x₃ ∈ S := by grind only [Multiset.mem_erase_of_ne, Multiset.mem_of_mem_erase]
      set S₃ := S₂.erase x₃
      have hS₃_card : S₃.card = 1 := by grind only [Multiset.card_erase_add_one]
      obtain ⟨x₄, hS₃_eq⟩ := Multiset.card_eq_one.mp hS₃_card
      have hx₄_mem_S : x₄ ∈ S := by grind only [Multiset.erase_comm, Multiset.card_eq_zero, Multiset.erase_of_notMem, Multiset.erase_singleton]

      have hS : S = {x₁, x₂, x₃, x₄} := multiset_erase x₁ hx₁ (multiset_erase x₂ hx₂_mem_S₁ (multiset_erase x₃ hx₃ hS₃_eq))
      have ht_prod : t = x₁ * x₂ * x₃ * x₄ := by
        simp [t, hS, Multiset.prod_singleton]
        ring

      have h_t_ne_zero : t ≠ 0 := by
        by_contra ht_zero
        have h_sols : ∀ x ∈ S, x = 0 ∨ x = 2 := fun _ _ ↦ by grind
        obtain ⟨x, hx, hx_eq_zero⟩ : ∃ x ∈ S, x = 0 := by grind
        have h_ne_zero : ∀ y ∈ S.erase 0, y ≠ 0 := by
          intro y hy
          by_contra hy_zero
          rw [hy_zero] at hy
          have : (S.erase 0).prod = 0 := Multiset.prod_eq_zero hy
          grind
        have : ∀ y ∈ S.erase 0, y = 2 := fun y hy ↦ (h_sols y (Multiset.mem_of_mem_erase hy)).resolve_left (fun h_zero ↦ h_ne_zero y hy h_zero)
        have h_S_erase : S.erase 0 = {2, 2, 2} := by
          ext y
          by_cases hy : y = 2
          · have count_eq : Multiset.count 2 (S.erase 0) = (S.erase 0).card := Multiset.count_eq_card.mpr (by grind)
            simp [hy, count_eq]
            grind +suggestions
          · simp [hy]
            grind
        replace : (S.erase 0).prod = 2*2*2 := by
          simp [h_S_erase, Multiset.prod_singleton]
          ring
        have hprod_zero := hprod 0 (by grind)
        linarith

      have ht_eq_1_sol : t = 1 → S ∈ solution := fun _ ↦ (by grind)

      have h_x₃x₄_eq_one : x₃ * x₄ = 1 := by grind
      by_cases h_eq : x₃ = x₄
      · have : x₄ = 1 ∨ x₄ = -1 := by grind
        cases' this with h₄_eq_1 h₄_eq_neg1
        · exact ht_eq_1_sol (by grind)
        · have h_either : (x₁ = -1 ∧ x₂ = 3) ∨ (x₁ = 3 ∧ x₂ = -1) := by grind
          have h_S_eq : S = {-1, -1, -1, 3} := by
            rcases h_either with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [hS, h_eq, h₄_eq_neg1, h1, h2]
            · exact multiset_order₂
            · exact multiset_order₁
          grind
      · have h_x₃x₄_eq_t : x₃ * x₄ = t := by grind
        exact ht_eq_1_sol (by grind)

  --- Proof that all sets in the solution satisfy the condition
  · intro hS
    rcases hS with heq | heq <;> rw [heq] <;> norm_num [Multiset.mem_cons, Multiset.mem_singleton, Multiset.erase_cons_head]

end Imo1965P4
