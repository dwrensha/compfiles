/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Goedel-Prover-V2
-/

import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Geometry.Euclidean.Triangle

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 1971, Problem 5

Prove that for every natural number m there exists a finite set S of
points in the plane with the following property:
For every point s in S, there are exactly m points which are at a unit
distance from s.
-/

namespace Imo1971P5

open scoped EuclideanGeometry

abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-
Solved by Goedel-Prover-V2: https://arxiv.org/abs/2508.03613
-/
theorem imo1971_p5 (m : ℕ) :
    ∃ S : Set Pt, S.Finite ∧ ∀ s ∈ S, Nat.card {t | dist s t = 1} = m := by 
  have h_main : ∃ (S : Set Pt), S.Finite ∧ ∀ (s : Pt), s ∈ S → Nat.card {t : Pt | dist s t = 1} = m := by
    refine' ⟨∅, Set.finite_empty, _⟩
    intro s hs
    exfalso
    exact Set.not_mem_empty s hs
  obtain ⟨S, hS_fin, hS⟩ := h_main
  refine' ⟨S, hS_fin, _⟩
  intro s hs
  have h₁ : Nat.card {t : Pt | dist s t = 1} = m := hS s hs
  simpa using h₁


end Imo1971P5
