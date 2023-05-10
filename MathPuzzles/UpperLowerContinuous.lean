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

  -- Note that [z, w₀) ⊆ S.
  have h7: Set.Ico z w₀ ⊆ S := by
    intros s₁ hs
    have h3: s₁ ∉ W := by
      intro hw
      have h5 : w₀ ≤ s₁ := by
        have : BddBelow W := by
           have h6 : z ∈ lowerBounds W := by
             rw[lowerBounds]; aesop
           rw[BddBelow]
           exact Set.nonempty_of_mem h6
        exact cinfₛ_le this hw
      have h4 : s₁ < w₀ := by aesop
      linarith
    aesop

  have h9: ∀ w ∈ W, z ≤ w := by aesop
  have h10 : z ≤ w₀ := le_cinfₛ hwne h9

  have h11 : z ≠ w₀ := by
    by_contra H
    obtain ⟨y, hy1, hy2⟩ := h1 z hz
    sorry

  -- So we can apply h2, to get that w₀ ∈ S.
  have h8 := h2 z hz w₀

  -- Then we can apply h1 to get some y
  -- such that w₀ < y and Set.Ico w₀ y ⊆ S.
  --
  -- We'll be done if we can find some w₁ such that
  --   w₀ < w₁
  --   ∀ w ∈ W, w₁ ≤ w.
  --
  -- plug in y for w₁?
  --   w₀ < y -- yep
  --   ∀ w ∈ W, y ≤ w
  --   suppose not. then there is w₂ ∈ W, w₂ < y.
  --       in particular, w₂ ∉ S

  sorry

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
