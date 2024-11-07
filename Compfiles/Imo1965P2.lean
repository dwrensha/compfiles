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
  have h0 := hab (p i) (p j)
  split_ifs with h1
  · subst h1
    simp only [reduceIte] at h0
    exact h0
  · have h2 : p i ≠ p j := fun a ↦ h1 (hp.1 a)
    simp only [h2] at h0
    exact h0

lemma lemma2 (a : Fin 3 → Fin 3 → ℝ)
    (p : Fin 3 → Fin 3)
    (hp : p.Bijective)
    (hc : ∀ i, 0 < ∑ j : Fin 3, a i j) :
    ∀ i, 0 < ∑ j : Fin 3, a (p i) (p j) := by
  intro i
  rw [Function.Bijective.sum_comp hp]
  exact hc (p i)

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
                 (le_of_not_le h1)
    intro i
    fin_cases i
    · exact h2 1
    · exact h2 0
    · exact h2 2
  wlog h2 : |x 2| ≤ |x 0| with H
  · have h2' : |x 0| ≤ |x 2| := le_of_not_le h2
    have h3 : |x 1| ≤ |x 2| := ge_trans h2' h1
    let p : Fin 3 → Fin 3 := ![2, 0, 1]
    have hp : p.Bijective := by decide
    have h4 := H (x ∘ p) (fun i j ↦ a (p i) (p j))
                 (lemma0 x a p hp heqs)
                 (lemma1 _ p hp hab)
                 (lemma2 _ p hp hc)
                 h2' h3
    intro i
    fin_cases i
    · exact h4 1
    · exact h4 2
    · exact h4 0
  have h3' : 0 < a 0 1 + a 0 2 + a 0 0 := by
    have h4 : ∑ j : Fin 3, a 0 j = a 0 1 + a 0 2 + a 0 0 := by
      rw [Fin.sum_univ_three, add_rotate]
    rw [←h4]
    exact hc 0
  have h4 : - a 0 1 + - a 0 2 < a 0 0 := by linarith only [h3']
  have h5 : 0 < - a 0 1 := neg_pos.mpr (hab 0 1)
  have h6 : 0 < - a 0 2 := neg_pos.mpr (hab 0 2)
  have h10 : 0 < a 0 0 := hab 0 0
  have h3 : |-a 0 1| + |-a 0 2| < |a 0 0| := by
    rw [abs_of_pos h5, abs_of_pos h6, abs_of_pos h10]
    exact h4
  have h7 := heqs 0
  rw [Fin.sum_univ_three] at h7
  by_contra! H
  obtain ⟨k, hk⟩ := H
  have h8 : 0 < |x k| := abs_pos.mpr hk
  have h9 : 0 < |x 0| := by
    (obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> aesop)
     <;> linarith only [h1, h2, h8]
  replace h7 : a 0 0 * x 0 = - a 0 1 * x 1 + - a 0 2 * x 2 := by linarith only [h7]

  apply_fun (|·|) at h7
  have h11 := calc
     |a 0 0| * |x 0|
       = |a 0 0 * x 0| := (abs_mul _ _).symm
     _ = _ := h7
     _ ≤ |-a 0 1 * x 1| + |-a 0 2 * x 2| := abs_add _ _
     _ = |-a 0 1| * |x 1| + |-a 0 2| * |x 2| := by simp only [abs_mul]
     _ ≤ |-a 0 1| * |x 0| + |-a 0 2| * |x 0| := by gcongr
     _ = (|-a 0 1| + |-a 0 2|) * |x 0| := (add_mul _ _ _).symm
  have h12 : |a 0 0| ≤ |-a 0 1| + |-a 0 2| := (mul_le_mul_right h9).mp h11
  exact not_lt.mpr h12 h3


end Imo1965P2
