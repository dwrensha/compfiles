import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Algebra.Ring.Basic

import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Linarith

/-
Suppose f : ℝ -> ℝ is continuous in both the upper topology (where
the basic open sets are half-open intervals (a, b]) and lower topology
(where the basic open sets are half-open intervals [a,b)).
Then f is continuous in the usual topology (where the basic open sets are
open intervals (a,b)) and also monotone nondecreasing.
-/

namespace UpperLowerContinuous

lemma real_induction
    (S : Set ℝ)

    -- If x ∈ S, then we can find y > x such that [x, y) ⊆ S.
    (h1 : ∀ x ∈ S, ∃ y, x < y ∧ Set.Ico x y ⊆ S)

    -- If [x, y) ⊆ S, then y ∈ S.
    (h2 : ∀ x ∈ S, ∀ y, x < y → Set.Ico x y ⊆ S → y ∈ S)

    (z : ℝ)
    (hz : z ∈ S)

    -- then [z,∞) ⊆ S
    : Set.Ici z ⊆ S := by

  by_contra H; rw[Set.subset_def] at H; push_neg at H
  obtain ⟨w₁, hw₁, hw₁'⟩ := H

  -- take the set W = {w | z ≤ w ∧ w ∉ S}.
  let W : Set ℝ := {w | z ≤ w ∧ w ∉ S}

  have hwne' : Nonempty W := by aesop
  have hwne : Set.Nonempty W := Iff.mp Set.nonempty_coe_sort hwne'

  -- let w₀ be its greatest lower bound.
  let w₀ := infₛ W

  have h6 : z ∈ lowerBounds W := by rw[lowerBounds]; aesop

  have hwbb : BddBelow W := by
    rw[BddBelow]
    exact Set.nonempty_of_mem h6

  -- Note that [z, w₀) ⊆ S.
  have h7: Set.Ico z w₀ ⊆ S := by
    intros s₁ hs
    have h3: s₁ ∉ W := by
      intro hw
      have h5 : w₀ ≤ s₁ := by
        exact cinfₛ_le hwbb hw
      have h4 : s₁ < w₀ := by aesop
      linarith
    aesop

  have h9: ∀ w ∈ W, z ≤ w := by aesop
  have h10 : z ≤ w₀ := le_cinfₛ hwne h9

  have h13 := Real.is_glb_infₛ W hwne hwbb

  have h11 : z ≠ w₀ := by
    by_contra H
    obtain ⟨y, hy1, hy2⟩ := h1 z hz
    rw[H] at hy1 h6

    have h12 : y ∈ lowerBounds W := by
      intros a ha;
      by_contra H'; push_neg at H'
      rw [Set.mem_setOf_eq] at ha
      exact ha.2 (hy2 ⟨h9 a ha, H'⟩)
    exact (not_le.mpr hy1) ((isGLB_iff_le_iff.mp h13 y).mpr h12)

  have h15: z < w₀ := Ne.lt_of_le h11 h10

  -- So we can apply h2, to get that w₀ ∈ S.
  have h8 := h2 z hz w₀ h15 h7

  -- Then we can apply h1 to get some y
  -- such that w₀ < y and Set.Ico w₀ y ⊆ S.

  obtain ⟨y, hwy, hy⟩ := h1 w₀ h8

  have h12 : y ∈ lowerBounds W := by
    intros a ha;
    by_contra H'; push_neg at H'
    rw [Set.mem_setOf_eq] at ha
    obtain hlt | hle := lt_or_le a w₀
    · exact ha.2 (h7 ⟨ha.1, hlt⟩)
    · exact ha.2 (hy ⟨hle, H'⟩)

  exact (not_le.mpr hwy) ((isGLB_iff_le_iff.mp h13 y).mpr h12)


def ℝₗ : Type := ℝ
def ℝᵤ : Type := ℝ

instance : TopologicalSpace ℝₗ :=
  TopologicalSpace.generateFrom {s : Set ℝₗ | ∃ a b : ℝ, Set.Ico a b = s}

instance : TopologicalSpace ℝᵤ :=
  TopologicalSpace.generateFrom {s : Set ℝᵤ | ∃ a b : ℝ, Set.Ioc a b = s}

theorem upper_lower_continuous
    (f : ℝ → ℝ)
    (hlc : @Continuous ℝₗ ℝₗ _ _ f)
    (huc : @Continuous ℝᵤ ℝᵤ _ _ f)
    : @Continuous ℝ ℝ _ _ f ∧ Monotone f := by
  constructor
  · sorry
  · sorry
