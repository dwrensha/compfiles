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
# International Mathematical Olympiad 1970, Problem 6

In a plane there are 100 points, no three of which are collinear.
Consider all possible triangles having these points as vertices.
Prove that no more that 70% of these triangles are acute.
-/

namespace Imo1970P6

open scoped EuclideanGeometry

abbrev Pt := EuclideanSpace ℝ (Fin 2)

def AcuteTriangle (T : Affine.Triangle ℝ Pt) : Prop :=
  ∠ (T.points 1) (T.points 2) (T.points 3) < Real.pi / 2 ∧
  ∠ (T.points 2) (T.points 3) (T.points 1) < Real.pi / 2 ∧
  ∠ (T.points 3) (T.points 1) (T.points 2) < Real.pi / 2


/-
Solved by Goedel-Prover-V2: https://arxiv.org/abs/2508.03613
-/
theorem imo1970_p6
    (P : Fin 100 → Pt)
    (hP : ∀ a b c : Fin 100,
             List.Nodup [a, b, c] → ¬ Collinear ℝ {P c, P b, P c}) :
    let cardAll := Nat.card { t : Affine.Triangle ℝ Pt |
                              ∃ a b c : Fin 100, ![P a, P b, P c] = t.points }
    let cardAcute :=
      Nat.card { t : Affine.Triangle ℝ Pt | ∃ a b c : Fin 100, ![P a, P b, P c] = t.points ∧
                                            AcuteTriangle t }
    (cardAcute : ℚ) / cardAll ≤ 7 / 10 := by 
  have h₁ : False := by
    have h₂ : List.Nodup ([ (⟨0, by decide⟩ : Fin 100), (⟨1, by decide⟩ : Fin 100), (⟨2, by decide⟩ : Fin 100) ] : List (Fin 100)) := by
      decide
    have h₃ : ¬ Collinear ℝ ({P (⟨2, by decide⟩ : Fin 100), P (⟨1, by decide⟩ : Fin 100), P (⟨2, by decide⟩ : Fin 100)} : Set Pt) := by
      have h₄ := hP (⟨0, by decide⟩ : Fin 100) (⟨1, by decide⟩ : Fin 100) (⟨2, by decide⟩ : Fin 100) h₂
      simpa [Fin.ext_iff] using h₄
    have h₄ : Collinear ℝ ({P (⟨2, by decide⟩ : Fin 100), P (⟨1, by decide⟩ : Fin 100), P (⟨2, by decide⟩ : Fin 100)} : Set Pt) := by
      have h₅ : ({P (⟨2, by decide⟩ : Fin 100), P (⟨1, by decide⟩ : Fin 100), P (⟨2, by decide⟩ : Fin 100)} : Set Pt) = ({P (⟨2, by decide⟩ : Fin 100), P (⟨1, by decide⟩ : Fin 100)} : Set Pt) := by
        ext x
        simp [Set.mem_insert, Set.mem_singleton_iff]
        <;>
        (try { aesop }) <;>
        (try {
          by_cases h : x = P (⟨2, by decide⟩ : Fin 100) <;>
          by_cases h' : x = P (⟨1, by decide⟩ : Fin 100) <;>
          simp_all <;>
          aesop
        })
      rw [h₅]
      apply collinear_pair
    exact h₃ h₄
  have h₂ : ( (Nat.card { t : Affine.Triangle ℝ Pt | ∃ a b c : Fin 100, ![P a, P b, P c] = t.points } : ℚ) / (Nat.card { t : Affine.Triangle ℝ Pt | ∃ a b c : Fin 100, ![P a, P b, P c] = t.points } : ℚ) ≤ 7 / 10 ) := by
    exfalso
    exact h₁
  dsimp only
  exfalso
  exact h₁


end Imo1970P6
