/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1965, Problem 2

Suppose that
  a₁₁x₁ + a₁₂x₂ + a₁₃x₃ = 0
  a₂₁x₁ + a₂₂x₂ + a₂₃x₃ = 0
  a₃₁x₁ + a₃₂x₂ + a₃₃x₃ = 0

where
 (A) a₁₁, a₂₂, a₃₃ are positive
 (B) the remaining aᵢⱼ are negative
 (C) in each row i, the sum of the coefficients aᵢⱼ is positive.

Prove that x₁ = x₂ = x₃ = 0.
-/

namespace Imo1965P2

snip begin

abbrev propsAB (a : Fin 3 → Fin 3 → ℝ) : Prop :=
       ∀ i j, if i = j then 0 < a i j else a i j < 0

lemma lemma1 (a : Fin 3 → Fin 3 → ℝ) (p : Fin 3 ↪ Fin 3)
    (hab : propsAB a) :
    propsAB (fun i j ↦ a (p i) (p j)) := by
  intro i j
  split_ifs with h1
  · subst h1
    have h0 := hab (p i) (p i)
    aesop
  · dsimp only
    have h3 := hab (p i) (p j)
    aesop

abbrev propC (a : Fin 3 → Fin 3 → ℝ) : Prop :=
       ∀ i, 0 < a i 0 + a i 1 + a i 2

lemma lemma2 (a : Fin 3 → Fin 3 → ℝ) (p : Fin 3 ↪ Fin 3)
    (hc : propC a) :
    propC (fun i j ↦ a (p i) (p j)) := by
  intro i
  dsimp only
  have h1 := hc (p i)
  sorry

snip end

problem imo1965_p2 (x : Fin 3 → ℝ) (a : Fin 3 → Fin 3 → ℝ)
    (hab : ∀ i j, if i = j then 0 < a i j else a i j < 0)
    (hc : ∀ i, 0 < a i 0 + a i 1 + a i 2) : ∀ i, x i = 0 := by
  -- https://prase.cz/kalva/imo/isoln/isoln652.html
  -- wlog, x 0 ≥ x 1 and x 0 ≥ x 2.
  wlog h1 : |x 1| ≤ |x 0| with H
  · have h2 := H ![x 1, x 0, x 2]
                 ![![a 1 1, a 1 0, a 1 2],
                   ![a 0 1, a 0 0, a 0 2],
                   ![a 2 1, a 2 0, a 2 2]]
    sorry
  sorry
