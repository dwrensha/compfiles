import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.MetricSpace.Basic

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
    (h1 : ∀ x ∈ S, ∃ y, x < y ∧ Set.Ico x y ⊆ S)
    (h2 : ∀ x ∈ S, ∀ y ∈ S, x < y → Set.Ico x y ⊆ S → y ∈ S)
    (z : ℝ)
    (hz : z ∈ S)
    : Set.Ici z ⊆ S := by
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
