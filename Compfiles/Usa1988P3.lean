/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Order.Interval.Finset.Nat
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 1988, Problem 3

Let X be the set {1, 2, ... , 20} and let P be the set of all 9-element
subsets of X. Show that for any map f : P → X we can find a 10-element
subset Y of X, such that f(Y - {k}) ≠ k for any k in Y.
-/

namespace Usa1988P3

open Finset

snip begin

/--
For any finite set `X`, the number of pairs `(Y, k)` where `Y` is a
10-element subset of `X`, `k ∈ Y`, and `f (Y.erase k) = k` is at most the
number of 9-element subsets of `X`: the map `(Y, k) ↦ Y.erase k` is
injective on such pairs, because `k = f (Y.erase k)` is determined by the
image, and then `Y = insert k (Y.erase k)` is determined as well.
-/
lemma card_bad_pairs_le (X : Finset ℕ) (f : Finset ℕ → ℕ) :
    ((X.powersetCard 10).sigma
        (fun Y ↦ Y.filter (fun k ↦ f (Y.erase k) = k))).card
      ≤ (X.powersetCard 9).card := by
  classical
  apply card_le_card_of_injOn (fun p : Σ _Y : Finset ℕ, ℕ ↦ p.1.erase p.2)
  · rintro ⟨Y, k⟩ hp
    simp only [mem_coe, mem_sigma, mem_powersetCard, mem_filter] at hp
    obtain ⟨⟨hYX, hYcard⟩, hkY, -⟩ := hp
    show Y.erase k ∈ X.powersetCard 9
    rw [mem_powersetCard]
    exact ⟨(erase_subset _ _).trans hYX, by rw [card_erase_of_mem hkY, hYcard]⟩
  · rintro ⟨Y₁, k₁⟩ hp₁ ⟨Y₂, k₂⟩ hp₂ h
    simp only [mem_coe, mem_sigma, mem_powersetCard, mem_filter] at hp₁ hp₂
    dsimp only at h
    have hk : k₁ = k₂ := by
      have e1 : f (Y₁.erase k₁) = k₁ := hp₁.2.2
      have e2 : f (Y₂.erase k₂) = k₂ := hp₂.2.2
      rw [h] at e1
      exact e1.symm.trans e2
    have hY : Y₁ = Y₂ := by
      rw [← insert_erase hp₁.2.1, ← insert_erase hp₂.2.1, h, hk]
    exact Sigma.ext hY (heq_of_eq hk)

snip end

problem usa1988_p3 (f : Finset ℕ → ℕ) :
    ∃ Y : Finset ℕ, Y ⊆ Finset.Icc 1 20 ∧ Y.card = 10 ∧
      ∀ k ∈ Y, f (Y.erase k) ≠ k := by
  classical
  by_contra hcon
  push Not at hcon
  -- Every 10-element subset Y of {1, ..., 20} has some k ∈ Y with
  -- f (Y.erase k) = k, so there are at least as many "bad pairs" (Y, k)
  -- as there are 10-element subsets.
  have h1 : ∀ Y ∈ (Finset.Icc 1 20).powersetCard 10,
      1 ≤ (Y.filter (fun k ↦ f (Y.erase k) = k)).card := by
    intro Y hY
    rw [mem_powersetCard] at hY
    obtain ⟨k, hkY, hkf⟩ := hcon Y hY.1 hY.2
    exact card_pos.mpr ⟨k, mem_filter.mpr ⟨hkY, hkf⟩⟩
  have h2 : ((Finset.Icc 1 20).powersetCard 10).card
      ≤ (((Finset.Icc 1 20).powersetCard 10).sigma
          (fun Y ↦ Y.filter (fun k ↦ f (Y.erase k) = k))).card := by
    rw [card_sigma, card_eq_sum_ones]
    exact sum_le_sum h1
  -- But there are at most C(20, 9) bad pairs, and C(20, 9) < C(20, 10).
  have hle : Nat.choose 20 10 ≤ Nat.choose 20 9 := by
    have h10 : ((Finset.Icc 1 20).powersetCard 10).card = Nat.choose 20 10 := by
      rw [card_powersetCard, Nat.card_Icc]
    have h9 : ((Finset.Icc 1 20).powersetCard 9).card = Nat.choose 20 9 := by
      rw [card_powersetCard, Nat.card_Icc]
    rw [← h10, ← h9]
    exact h2.trans (card_bad_pairs_le (Finset.Icc 1 20) f)
  exact absurd hle (by decide)

end Usa1988P3
