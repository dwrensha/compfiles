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

snip begin

-- This lemma was proved automatically by Kimina-Prover 72B
theorem lemma1 (c1 : ℝ) :
  let f := fun x : (Set.Icc (0:ℝ) 1) ↦ if (x:ℝ) ≤ 1 / 2 then 0 else 1;
  (∀ (a : ℝ) (ha : 0 ≤ a ∧ a ≤ 1), f ⟨a, ha⟩ ≤ c1 * a) →
    (∀ (x : ↑(Set.Icc 0 1)), 0 ≤ f x) →
      f 1 = 1 → (∀ (x y : ↑(Set.Icc 0 1)) (h : (x:ℝ) + (y:ℝ) ∈ Set.Icc 0 1), f x + f y ≤ f ⟨↑x + ↑y, h⟩) → 2 ≤ c1 := by
  intro f h1 h2 h3 h4
  by_contra h
  push_neg at h
  have h7 : c1 < (2 : ℝ) := by linarith
  have hc1 : c1 ≥ 0 := by
    have h1' := h1 (1 / 2 : ℝ) (by norm_num)
    have h5 : f ⟨(1 / 2 : ℝ), by norm_num⟩ = (0 : ℝ) := by
      simp [f]
    have h6 : (0 : ℝ) ≤ c1 * (1 / 2 : ℝ) := by
      have h7 : f ⟨(1 / 2 : ℝ), by norm_num⟩ ≤ c1 * (1 / 2 : ℝ) := by
        simpa using h1'
      rw [h5] at h7
      linarith
    nlinarith
  have h9 : ∃ a : ℝ, a > (1 / 2 : ℝ) ∧ a ≤ (1 : ℝ) ∧ 1 > c1 * a := by
    use (1 + (2 - c1) / 4) / 2
    constructor
    · -- Show a > 1/2
      nlinarith
    constructor
    · -- Show a ≤ 1
      nlinarith
    · -- Show 1 > c1 * a
      nlinarith [sq_nonneg (c1 - 1), sq_nonneg ((1 + (2 - c1) / 4) / 2 - 1 / 2), h7, hc1]
  rcases h9 with ⟨a, ha1, ha2, h10⟩
  have h1' := h1 a ⟨by linarith, by linarith⟩
  have h5 : f ⟨a, ⟨by linarith, by linarith⟩⟩ = 1 := by
    simp [f]
    all_goals
      try { linarith }
  have h6 : (1 : ℝ) ≤ c1 * a := by
    have h7 : f ⟨a, ⟨by linarith, by linarith⟩⟩ ≤ c1 * a := by
      simpa using h1'
    rw [h5] at h7
    linarith
  linarith

snip end


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
    obtain ⟨h1, h2, h3⟩ := hf
    exact lemma1 c1 hc1 h1 h2 h3


end Usa1993P3
