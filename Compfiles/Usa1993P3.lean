/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 1993, Problem 3

Consider functions f : [0,1] → ℝ which satisfy

  (i)   f(x) ≥ 0 for all x ∈ [0,1]
  (ii)  f(1) = 1
  (iii) f(x) + f(y) ≤ f (x + y) whenever x, y and x + y are all in [0,1].

Determine the smallest constant c such that

       f(x) ≤ cx

for every function satisfying (i) - (iii) and every x ∈ [0,1].
-/

namespace Usa1993P3

def valid (f : Set.Icc (0 : ℝ) 1 → ℝ) : Prop :=
  (∀ x, 0 ≤ f x) ∧
  f 1 = 1 ∧
  ∀ x y, (h : x.val + y.val ∈ Set.Icc 0 1) → f x + f y ≤ f ⟨x.val + y.val, h⟩

determine min_c : ℝ := 2

problem usa1993_p5 :
    IsLeast {c | ∀ f, valid f → ∀ x, f x ≤ c * x } min_c := by
  simp only [Subtype.forall, Set.mem_Icc]
  constructor
  · simp only [Set.mem_setOf_eq]
    intro f hf x hx
    sorry
  · rw [mem_lowerBounds]
    intro c1 hc1
    simp only [Set.mem_setOf_eq] at hc1
    let f : Set.Icc (0 : ℝ) 1 → ℝ := fun x ↦ if x.val ≤ 1/2 then 0 else 1
    have hf : valid f := by
      refine ⟨?_, ?_, ?_⟩
      · intro x
        unfold f
        split <;> norm_num
      · unfold f; norm_num
      · intro x y hx
        obtain ⟨x, hxx⟩ := x
        obtain ⟨y, hyy⟩ := y
        simp only [Set.mem_Icc] at hx hxx hyy
        obtain ⟨hx1, hx2⟩ := hx
        unfold f
        split_ifs with h1 h2 h3 h4 h5 h6 <;> linarith
    specialize hc1 f hf
    by_contra! H
    --let a1 := 1/2 + (2 - c1)
    --have ha1 : 0 ≤ a1 ∧ a1 ≤ 1 := by sorry
    --specialize hc1 a1 ha1
    --unfold f at hc1
    sorry


end Usa1993P3
