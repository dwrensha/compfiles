/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file

/-!
# USA Mathematical Olympiad 1985, Problem 1

Determine whether or not there are any positive integral solutions of
the simultaneous equations

          x₁² + x₂² + ⋯ + x₁₉₈₅² = y³
          x₁³ + x₂³ + ⋯ + x₁₉₈₅³ = z²

with distinct integers x₁, x₂, ⋯, x₁₉₈₅.
-/

namespace Usa1985P1

open scoped BigOperators

determine does_exist : Bool := true

abbrev is_valid (x : ℕ → ℤ) (y z : ℤ) : Prop :=
    (∀ i ∈ Finset.range 1985, 0 < x i) ∧
    0 < y ∧ 0 < z ∧
    ∑ i in Finset.range 1985, x i ^ 2 = y ^ 3 ∧
    ∑ i in Finset.range 1985, x i ^ 3 = z ^ 2 ∧
    ∀ i ∈ Finset.range 1985, ∀ j ∈ Finset.range 1985, i ≠ j → x i ≠ x j

problem usa1985_p1 :
    if does_exist
    then ∃ x y z, is_valid x y z
    else ¬ ∃ x y z, is_valid x y z := by
  -- solution from
  -- https://artofproblemsolving.com/wiki/index.php/1985_USAMO_Problems/Problem_1
  simp only [ite_true]
  let j := ∑ ii in Finset.range 1985, (ii + 1)
  let k := ∑ ii in Finset.range 1985, (ii + 1)^2
  let x := fun (ii : ℕ) ↦ ((ii + 1):ℤ) * k ^ 4
  use x, k, j
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ii hii
    dsimp [x]
    positivity
    sorry -- comment this out and you get "max recursion depth reached"

  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
