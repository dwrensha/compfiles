/-
Copyright (c) 2025 Francesco Vercellesi· All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Francesco Vercellesi
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 1989, Problem 1

Prove that the integers from 1 to 1989 can be partitioned in 117 sets
of 17 elements each, all with the same sum of elements.
-/

namespace Imo1989P1

abbrev S := Finset.Icc 1 1989

snip begin

def n : ℕ := 117

def row (j : ℕ) (i : Fin n) : ℕ :=
  if j < 14 then
    if j % 2 = 0 then j * n + i.val + 1
    else (j + 1) * n - i.val
  else if j = 14 then 14 * n + i.val + 1
  else if j = 15 then 15 * n + (i.val + 58) % n + 1
  else 16 * n + (2 * n - 1 - 2 * i.val) % n + 1

def A (i : Fin n) : Finset ℕ := (Finset.range 17).image (λ j ↦ row j i)

lemma row_quot (j : ℕ) (hj : j < 17) (i : Fin n) : (row j i - 1) / n = j := by
  unfold row; split_ifs <;> (simp [n] at *; lia)

lemma row_inj {j₁ j₂ : ℕ} {i₁ i₂ : Fin n} (hj₁ : j₁ < 17) (hj₂ : j₂ < 17) :
    row j₁ i₁ = row j₂ i₂ ↔ j₁ = j₂ ∧ i₁ = i₂ := by
  refine ⟨fun h => ?_, fun ⟨rfl, rfl⟩ => rfl⟩
  have hj : j₁ = j₂ := by
    have h1 := row_quot j₁ hj₁ i₁; have h2 := row_quot j₂ hj₂ i₂
    rw [h] at h1; exact h1.symm.trans h2
  exact ⟨hj, by subst hj; ext; unfold row at h; split_ifs at h <;> (simp [n] at *; try lia)⟩

private lemma row_injOn (i : Fin n) :
    Set.InjOn (fun j => row j i) (Finset.range 17 : Set ℕ) :=
  fun _ hj₁ _ hj₂ h =>
    ((row_inj (Finset.mem_range.mp hj₁) (Finset.mem_range.mp hj₂)).1 h).1

private lemma row_image_inj {j₁ j₂ : ℕ} (hj₁ : j₁ ∈ Finset.range 17)
    (hj₂ : j₂ ∈ Finset.range 17) {i : Fin n} (h : row j₁ i = row j₂ i) : j₁ = j₂ :=
  ((row_inj (Finset.mem_range.mp hj₁) (Finset.mem_range.mp hj₂)).1 h).1

lemma A_card (i : Fin n) : (A i).card = 17 := by
  simp [A, Finset.card_image_of_injOn (row_injOn i)]

lemma A_sum (i : Fin n) : (A i).sum id = 16915 := by
  simp only [A]
  rw [Finset.sum_image fun _ h₁ _ h₂ h => row_image_inj h₁ h₂ h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, id, row]
  norm_num [n]
  have hi := i.isLt; simp only [n] at hi
  by_cases h59 : i.val < 59
  · have h1 : (i.val + 58) % 117 = i.val + 58 := Nat.mod_eq_of_lt (by lia)
    have h2 : (233 - 2 * i.val) % 117 = 116 - 2 * i.val := by
      have : 233 - 2 * i.val = 117 + (116 - 2 * i.val) := by lia
      rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by lia)]
    lia
  · have h1 : (i.val + 58) % 117 = i.val - 59 := by
      have : i.val + 58 = 117 + (i.val - 59) := by lia
      rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by lia)]
    have h2 : (233 - 2 * i.val) % 117 = 233 - 2 * i.val := Nat.mod_eq_of_lt (by lia)
    lia

lemma A_injective : Function.Injective A := by
  intro i₁ i₂ h
  have : row 0 i₁ ∈ A i₂ := h ▸ Finset.mem_image.mpr ⟨0, by simp, rfl⟩
  obtain ⟨j, hj, h_eq⟩ := Finset.mem_image.mp this
  exact ((row_inj (by lia) (Finset.mem_range.mp hj)).1 h_eq.symm).2

lemma A_le_S (i : Fin n) : A i ≤ S := by
  intro x hx; obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
  unfold row; simp [S]; split_ifs <;> (simp [n] at *; lia)

lemma A_disjoint {i₁ i₂ : Fin n} (h : i₁ ≠ i₂) : Disjoint (A i₁) (A i₂) := by
  rw [Finset.disjoint_left]
  rintro _ hx hy
  obtain ⟨j₁, hj₁, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j₂, hj₂, h_eq⟩ := Finset.mem_image.mp hy
  exact h ((row_inj (Finset.mem_range.mp hj₁) (Finset.mem_range.mp hj₂)).1 h_eq.symm).2

def P : Finpartition S where
  parts := Finset.univ.image A
  supIndep := by
    rw [Finset.supIndep_iff_pairwiseDisjoint]
    simp only [Set.PairwiseDisjoint, Set.Pairwise, Finset.mem_coe, Finset.mem_image,
      Finset.mem_univ, true_and, Function.onFun, id]
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ h
    exact A_disjoint fun hij => h (hij ▸ rfl)
  sup_parts := by
    rw [Finset.sup_image, Function.id_comp, Finset.sup_eq_biUnion]
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.biUnion_subset.mpr fun i _ => A_le_S i
    · rw [Finset.card_biUnion fun i _ j _ hij => A_disjoint hij]
      simp [A_card, S, n]
  bot_notMem := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    rintro ⟨i, hi⟩; exact absurd (hi ▸ A_card i) (by norm_num)

snip end

problem imo1989_p1 : ∃ (P : Finpartition S),
    P.parts.card = 117 ∧
    (∀ p ∈ P.parts, p.card = 17) ∧
    (∀ p ∈ P.parts, ∀ q ∈ P.parts, p.sum id = q.sum id) := by
  refine ⟨P, ?_, ?_, ?_⟩
  · simp [P, Finset.card_image_of_injective _ A_injective, n]
  · simp only [show P.parts = Finset.univ.image A from rfl, Finset.forall_mem_image]
    exact fun _ _ => A_card _
  · simp only [show P.parts = Finset.univ.image A from rfl, Finset.forall_mem_image]
    intros; rw [A_sum, A_sum]

end Imo1989P1
