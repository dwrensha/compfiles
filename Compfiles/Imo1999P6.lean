/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1999, Problem 6

Determine all functions f : ℝ → ℝ such that

  f(x - f(y)) = f(f(y)) + xf(y) + f(x) - 1

for all x,y ∈ ℝ.
-/

namespace Imo1999P6

determine SolutionSet : Set (ℝ → ℝ) := { fun x ↦ 1 - x^2 / 2 }

problem imo1999_p6 (f : ℝ → ℝ) :
    f ∈ SolutionSet ↔
    ∀ x y, f (x - f y) = f (f y) + x * f y + f x - 1 := by
  -- informal solution from
  -- https://prase.cz/kalva/imo/isoln/isoln996.html
  rw [Set.mem_singleton_iff]
  constructor
  · rintro rfl x y; field_simp; ring
  intro hf
  let c := f 0
  let A := Set.range f
  have h1 : ∀ a ∈ A, f a = (1 + c)/2 - a ^2 /2 := fun a ha ↦ by
    -- putting a = f(y) and x = a,
    obtain ⟨y, hy⟩ := ha
    -- we get f(a - a) = f(a) + a^2 + f(a) - 1,
    specialize hf a y
    rw [hy] at hf
    -- so f(a) = (1 + c)/2 - a^2/2 (*).
    rw [sub_self] at hf
    linarith only [hf]
  -- given any x in R, we may find a, b in A such that x = a - b
  have h2 : ∀ x, ∃ a b, a ∈ A ∧ b ∈ A ∧ x = a - b := fun x ↦ by
    -- Note first that c cannot be zero, for if it were,
    -- then putting y = 0, we get:
    --      f(x - c) = f(c) + xc + f(x) - 1 (**)
    -- and hence f(0) = f(c) = 1. Contradiction.

    have h3 := hf x 0
    have h4 : c ≠ 0 := fun hc ↦ by
      unfold c at hc
      rw [hc, sub_zero, mul_zero, add_zero] at h3
      linarith

    -- But (**) also shows that f(x - c) - f(x) = xc + (f(c) - 1).

    have h5 : ∀ x', f (x' - c) - f x' = x' * c + (f c - 1) := by
      intro x'
      linarith [hf x' 0]
    -- Here x is free to vary over R, so xc + (f(c) - 1)
    -- can take any value in R.

    -- want to choose x' such that x' * c + (f c - 1) = x
    let x' := (x - (f c - 1)) / c
    specialize h5 x'
    refine ⟨f (x' - c), f x', Set.mem_range_self _, Set.mem_range_self _, ?_⟩
    rw [h5]
    unfold x'
    field_simp
    simp
  -- Hence f(x) = f(a - b) = f(b) + ab + f(a) - 1.
  have h11 : ∀ x, f x = c - x^2 / 2 := fun x ↦ by
    obtain ⟨a, b, ha, hb, hab⟩ := h2 x
    grind

  ext x
  -- In particular, this is true for x in A.
  -- Comparing with (h1) we deduce that c = 1.
  -- So for all x in R we must have f(x) = 1 - x^2/2
  have h12 := h1 c (Set.mem_range_self 0)
  have h13 := h11 c
  have h14 : c = 1 := by linarith only [h12, h13]
  specialize h11 x
  rw [h14] at h11
  exact h11


end Imo1999P6
