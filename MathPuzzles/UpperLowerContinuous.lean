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

/--
 Let S be a set of real numbers such that:
  1. If x ∈ S, then we can find y > x such that [x, y) ⊆ S.
  2. If [x, y) ⊆ S, then y ∈ S.
 Then, given z ∈ S, we have [z, ∞) ⊆ S.
-/
lemma real_induction
    (S : Set ℝ)
    (h1 : ∀ x ∈ S, ∃ y, x < y ∧ Set.Ico x y ⊆ S)
    (h2 : ∀ x ∈ S, ∀ y, x < y → Set.Ico x y ⊆ S → y ∈ S)
    (z : ℝ)
    (hz : z ∈ S)
    : Set.Ici z ⊆ S := by

  -- Suppose not. Then there is w₁ in [z,∞) that is not in S.
  by_contra H; rw[Set.subset_def] at H; push_neg at H
  obtain ⟨w₁, hw₁, hw₁'⟩ := H

  -- Take the set W = {w | z ≤ w ∧ w ∉ S}.
  let W : Set ℝ := {w | z ≤ w ∧ w ∉ S}

  -- Let w₀ be its greatest lower bound.
  let w₀ := sInf W

  -- W is nonempty.
  have hwne : Set.Nonempty W := ⟨w₁, hw₁, hw₁'⟩

  have h6 : z ∈ lowerBounds W := fun _ ha ↦ ha.1
  have hwbb : BddBelow W := Set.nonempty_of_mem h6

  -- Note that [z, w₀) ⊆ S.
  have h7: Set.Ico z w₀ ⊆ S := by
    intros s₁ hs
    by_contra H
    exact (not_le.mpr hs.2) (csInf_le hwbb ⟨hs.1, H⟩)

  have h9 : ∀ w ∈ W, z ≤ w := fun w h ↦ h.1
  have h10 : z ≤ w₀ := le_csInf hwne h9

  have h13 := Real.is_glb_sInf W hwne hwbb

  have h11 : z ≠ w₀ := by
    by_contra H
    obtain ⟨y, hy1, hy2⟩ := h1 z hz
    rw[H] at hy1 h6

    have h12 : y ∈ lowerBounds W := by
      intros a ha;
      by_contra H'; push_neg at H'
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
    apply ha.2
    obtain hlt | hle := lt_or_le a w₀
    · exact h7 ⟨ha.1, hlt⟩
    · exact hy ⟨hle, H'⟩

  exact (not_le.mpr hwy) ((isGLB_iff_le_iff.mp h13 y).mpr h12)

/-- newtypes for upper and lower topologies -/
def ℝᵤ : Type := ℝ
def ℝₗ : Type := ℝ

instance tᵤ : TopologicalSpace ℝᵤ :=
  TopologicalSpace.generateFrom {s : Set ℝᵤ | ∃ a b : ℝ, Set.Ioc a b = s}

instance tₗ : TopologicalSpace ℝₗ :=
  TopologicalSpace.generateFrom {s : Set ℝₗ | ∃ a b : ℝ, Set.Ico a b = s}

#check Continuous
#check continuous_generateFrom

-- activate the Continuous[t1, t2] notation
open Topology

lemma continuous_of_upper_lower_continuous
    (f : ℝ → ℝ)
    (huc : Continuous[tᵤ, tᵤ] f)
    (hlc : Continuous[tₗ, tₗ] f)
    : Continuous f := by
  /-
    Let an open set (a,b) be given. Let a point c ∈ f⁻¹(a,b) be given.
    To show f⁻¹(a,b) is open, we must show there's an open interval
    (a',b') containing c, and contained in f⁻¹(a,b). We know f(c) ∈ (a,b),
    so we can consider (a,f(c)] and [f(c),b). Because f is R- and L-continuous,
     - f⁻¹(a,f(c)] is R-open
     - f⁻¹[f(c),b) is L-open
    Note that also we know
     - c ∈ f⁻¹(a,f(c)]
     - c ∈ f⁻¹[f(c),b)
    therefore
     - There is a half-open interval (a', c] contained in f⁻¹(a,f(c)]
     - There is a half-open interval (c, b'] contained in f⁻¹[f(c),b)
    therefore
     - f(a', c] ⊆ (a,f(c)]
     - f(c, b'] ⊆ [f(c),b)
    hence
     f(a',b') ⊆ (a,b)
    as required.
  -/
  sorry

theorem upper_lower_continuous
    (f : ℝ → ℝ)
    (huc : Continuous[tᵤ, tᵤ] f)
    (hlc : Continuous[tₗ, tₗ] f)
    : Continuous f ∧ Monotone f := by
  constructor
  · exact continuous_of_upper_lower_continuous f huc hlc
  · sorry
