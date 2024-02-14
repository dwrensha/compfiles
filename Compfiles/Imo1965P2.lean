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

open scoped BigOperators

snip begin

abbrev propEqs (x : Fin 3 → ℝ) (a : Fin 3 → Fin 3 → ℝ) : Prop :=
   ∀ i, ∑ j : Fin 3, (a i j * x j) = 0

lemma lemma0 (x : Fin 3 → ℝ) (a : Fin 3 → Fin 3 → ℝ) (p : Fin 3 → Fin 3)
    (hp : p.Bijective)
    (he : propEqs x a) : propEqs (x ∘ p) (fun i j ↦ a (p i) (p j)) := by
  intro i
  dsimp
  have hi := he (p i)
  rwa [Function.Bijective.sum_comp hp (fun j ↦ a (p i) j * x j)]

abbrev propsAB (a : Fin 3 → Fin 3 → ℝ) : Prop :=
       ∀ i j, if i = j then 0 < a i j else a i j < 0

lemma lemma1 (a : Fin 3 → Fin 3 → ℝ) (p : Fin 3 → Fin 3)
    (hp : p.Bijective)
    (hab : propsAB a) :
    propsAB (fun i j ↦ a (p i) (p j)) := by
  intro i j
  split_ifs with h1
  · subst h1
    have h0 := hab (p i) (p i)
    aesop
  · dsimp only
    have h3 := hab (p i) (p j)
    have : p i ≠ p j := fun a ↦ h1 (hp.1 a)
    aesop

abbrev propC (a : Fin 3 → Fin 3 → ℝ) : Prop := ∀ i, 0 < ∑ j : Fin 3, a i j

lemma lemma2 (a : Fin 3 → Fin 3 → ℝ)
    (p : Fin 3 → Fin 3)
    (hp : p.Bijective)
    (hc : propC a) :
    propC (fun i j ↦ a (p i) (p j)) := by
  intro i
  have h1 := hc (p i)
  have h2 : ∑ j : Fin 3, a (p i) (p j) = ∑ j : Fin 3, a (p i) j :=
    Function.Bijective.sum_comp hp (a (p i))
  rwa [h2]

snip end

problem imo1965_p2 (x : Fin 3 → ℝ) (a : Fin 3 → Fin 3 → ℝ)
    (heqs : ∀ i, ∑ j : Fin 3, (a i j * x j) = 0)
    (hab : ∀ i j, if i = j then 0 < a i j else a i j < 0)
    (hc : ∀ i, 0 < ∑ j : Fin 3, a i j)
    : ∀ i, x i = 0 := by
  -- https://prase.cz/kalva/imo/isoln/isoln652.html
  -- wlog, |x 0| ≥ |x 1| and |x 0| ≥ |x 2|.
  wlog h1 : |x 1| ≤ |x 0| with H
  · let p : Fin 3 → Fin 3 := ![1, 0, 2]
    have hp : p.Bijective := by decide

    have h2 := H (x ∘ p) (fun i j ↦ a (p i) (p j))
                 (lemma0 x a p hp heqs)
                 (lemma1 _ p hp hab)
                 (lemma2 _ p hp hc)
    clear H
    dsimp at h2
    have h3 : |x 0| ≤ |x 1| := le_of_not_le h1
    replace h2 := h2 h3
    intro i
    fin_cases i
    · have := h2 1; aesop
    · have := h2 0; aesop
    · have := h2 2; aesop
  wlog h2 : |x 2| ≤ |x 0| with H
  · sorry
  have h3' : 0 < a 0 1 + a 0 2 + a 0 0 := by
    have h4 : ∑ j : Fin 3, a 0 j = a 0 1 + a 0 2 + a 0 0 := by
      rw [Fin.sum_univ_three, add_rotate]
    rw [←h4]
    exact hc 0
  have h4 : - a 0 1 + - a 0 2 < a 0 0 := by linarith only [h3']
  have h5 : 0 < - a 0 1 := by
    have := hab 0 1; simp at this; exact neg_pos.mpr this
  have h6 : 0 < - a 0 2 := by
    have := hab 0 2; simp at this; exact neg_pos.mpr this
  have h3 : |a 0 1| + |a 0 2| < |a 0 0| := by sorry
  sorry
