/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib

import ProblemExtraction

problem_file {
  problemImportedFrom :=
    "https://github.com/jsm28/IMOLean/blob/main/IMO/IMO2020P4.lean"
}

/-!
# International Mathematical Olympiad 2020, Problem 4

There is an integer n > 1. There are n² stations on a slope of
a mountain, all at different altitudes. Each of two cable car
companies, A and B, operates k cable cars; each cable car
provides a transfer from one of the stations to a higher one
(with no intermediate stops). The k cable cars of A have k
different starting points and k different finishing points,
and a cable car which starts higher also finishes higher. The
same conditions hold for B. We say that two stations are linked
by a company if one can start from the lower station and reach
the higher one by using one or more cars of that company (no
other movements between stations are allowed). Determine the
smallest positive integer k for which one can guarantee that
there are two stations that are linked by both companies.
-/

namespace Imo2020P4

/-- A cable car's starting and finishing points. -/
structure Car (n : ℕ) : Type where
  /-- The starting point. -/
  start : Fin (n ^ 2)
  /-- The finishing point. -/
  finish : Fin (n ^ 2)
  start_lt_finish : start < finish

/-- The cable cars of a company. -/
structure Company (n k : ℕ) : Type where
  /-- The individual cars. -/
  cars : Fin k → Car n
  injective_start : Function.Injective fun i ↦ (cars i).start
  injective_finish : Function.Injective fun i ↦ (cars i).finish
  monovary_start_finish : Monovary (fun i ↦ (cars i).start) (fun i ↦ (cars i).finish)

/-- A linkage between two stations. -/
structure Company.linkage {n k : ℕ} (c : Company n k) : Type where
  /-- The sequence of cars used. -/
  cars : List (Fin k)
  nonempty : cars ≠ []
  valid : cars.IsChain fun i j ↦ (c.cars i).finish = (c.cars j).start

/-- The first station in a linkage. -/
def Company.linkage.start {n k : ℕ} {c : Company n k} (x : c.linkage) : Fin (n ^ 2) :=
  (c.cars (x.cars.head x.nonempty)).start

/-- The last station in a linkage. -/
def Company.linkage.finish {n k : ℕ} {c : Company n k} (x : c.linkage) : Fin (n ^ 2) :=
  (c.cars (x.cars.getLast x.nonempty)).finish

/-- The property of two stations being linked (in the given order). -/
def Company.linked {n k : ℕ} (c : Company n k) (l h : Fin (n ^ 2)) : Prop :=
  ∃ x : c.linkage, x.start = l ∧ x.finish = h

determine answer : (Set.Ioi 1) → ℕ := sorry

problem imo2020_p4 (n : Set.Ioi 1) :
    IsLeast
      {k : ℕ | ∀ A B : Company n k, ∃ i j, A.linked i j ∧ B.linked i j}
      (answer n) := by
  sorry

end Imo2020P4
