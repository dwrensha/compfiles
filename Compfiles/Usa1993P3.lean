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

def valid (f : Set.Icc 0 1 → ℝ) : Prop :=
  (∀ x, 0 ≤ f x) ∧
  f 1 = 1 ∧
  ∀ x y, (h : x.val + y.val ∈ Set.Icc 0 1) → f x + f y ≤ f ⟨x.val + y.val, h⟩

determine min_c : ℝ := sorry

problem usa1993_p5 :
    IsLeast {c | ∀ f, valid f ∧ ∀ x, f x ≤ c * x } min_c := by
  sorry
