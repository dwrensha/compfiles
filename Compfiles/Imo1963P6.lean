/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Perm
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 1963, Problem 6

Five students A, B, C, D, E were placed 1 to 5 in a contest with no ties.
One prediction was that the result would be the order A, B, C, D, E.
But no student finished in the position predicted, and no two students
predicted to finish consecutively did so. For example, the outcome for
C and D was not 1, 2 (respectively), or 2, 3, or 3, 4, or 4, 5.
Another prediction was the order D, A, E, C, B. Exactly two students
finished in the places predicted, and two disjoint pairs of students
predicted to finish consecutively did so. Determine the outcome.
-/

namespace Imo1963P6

/-!
We identify the students with `Fin 5`, in the order A, B, C, D, E, and the
places of the contest with `Fin 5`, place `i` meaning `(i + 1)`-th place.
Since there were no ties, the outcome of the contest is described by a
permutation `π : Equiv.Perm (Fin 5)`, where `π s` is the place of student `s`.
-/

/-- The second prediction "D, A, E, C, B", given as the function sending
each student to the place in which it was predicted to finish. -/
def secondPrediction : Fin 5 → Fin 5 := ![1, 4, 3, 0, 2]

determine answer : Equiv.Perm (Fin 5) where
  toFun := ![2, 4, 3, 1, 0]
  invFun := ![4, 3, 0, 2, 1]
  left_inv := by intro x; fin_cases x <;> decide
  right_inv := by intro x; fin_cases x <;> decide

snip begin

-- The conditions of the problem determine the outcome uniquely: there are
-- only `5! = 120` possible outcomes, so they can be checked exhaustively.
set_option maxRecDepth 4000 in
lemma classification : ∀ π : Equiv.Perm (Fin 5),
    (∀ s : Fin 5, π s ≠ s) →
    (∀ i : Fin 4, (π i.succ : ℕ) ≠ (π i.castSucc : ℕ) + 1) →
    ((Finset.univ.filter (fun s => π s = secondPrediction s)).card = 2) →
    (((π 0 : ℕ) = (π 3 : ℕ) + 1 ∧ (π 2 : ℕ) = (π 4 : ℕ) + 1) ∨
     ((π 0 : ℕ) = (π 3 : ℕ) + 1 ∧ (π 1 : ℕ) = (π 2 : ℕ) + 1) ∨
     ((π 4 : ℕ) = (π 0 : ℕ) + 1 ∧ (π 1 : ℕ) = (π 2 : ℕ) + 1)) →
    π = answer := by
  decide

snip end

problem imo1963_p6 (π : Equiv.Perm (Fin 5))
    -- No student finished in the position predicted by the first prediction
    -- "A, B, C, D, E".
    (h1 : ∀ s : Fin 5, π s ≠ s)
    -- No two students predicted to finish consecutively did so; for example,
    -- the outcome for C and D was not 1, 2 (respectively), or 2, 3, or 3, 4,
    -- or 4, 5.
    (h2 : ∀ i : Fin 4, (π i.succ : ℕ) ≠ (π i.castSucc : ℕ) + 1)
    -- Exactly two students finished in the places predicted by the second
    -- prediction.
    (h3 : (Finset.univ.filter (fun s => π s = secondPrediction s)).card = 2)
    -- Two disjoint pairs of students predicted to finish consecutively did
    -- so. The consecutive pairs of the second prediction "D, A, E, C, B" are
    -- {D, A}, {A, E}, {E, C} and {C, B}; the disjoint pairs among them are
    -- {D, A} & {E, C}, {D, A} & {C, B}, and {A, E} & {C, B}.
    (h4 : ((π 0 : ℕ) = (π 3 : ℕ) + 1 ∧ (π 2 : ℕ) = (π 4 : ℕ) + 1) ∨
           ((π 0 : ℕ) = (π 3 : ℕ) + 1 ∧ (π 1 : ℕ) = (π 2 : ℕ) + 1) ∨
           ((π 4 : ℕ) = (π 0 : ℕ) + 1 ∧ (π 1 : ℕ) = (π 2 : ℕ) + 1)) :
    π = answer :=
  classification π h1 h2 h3 h4

end Imo1963P6
