/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 2018, Problem 3

An anti-Pascal triangle is an equilateral triangular array of numbers such that,
except for the numbers in the bottom row, each number is the absolute value
of the difference of the two numbers immediately below it. For example,
the following array is an anti-Pascal triangle with four rows
which contains every integer from 1 to 10:

                  4
                2   6
              5   7   1
            8   3  10   9

Does there exist an anti-Pascal triangle with 2018 rows which contains every
integer from 1 to 1 + 2 + ... + 2018?
-/

namespace Imo2018P3

structure Coords where
(row : ℕ) (col : ℕ)

def left_child (c : Coords) : Coords :=
 ⟨c.row.succ, c.col⟩

def right_child (c : Coords) : Coords :=
  ⟨c.row.succ, c.col.succ⟩

/--
antipascal triangle with n rows
-/
structure antipascal_triangle (n : ℕ) where
(f : Coords → ℕ)
(antipascal : ∀ x : Coords, x.row + 1 < n ∧ x.col ≤ x.row →
  f x + f (left_child x) = f (right_child x) ∨
  f x + f (right_child x) = f (left_child x))

def exists_desired_triangle : Prop :=
   ∃ t : antipascal_triangle 2018,
     ∀ n, 1 ≤ n → n ≤ ∑ i ∈ Finset.range 2018, (i + 1) →
         ∃ r, r ≤ 2018 ∧ ∃ c, c < r ∧ t.f ⟨r,c⟩ = n

snip begin

structure a_and_b where
(a : Coords) (b : Coords)

snip end

determine does_exist : Bool := false

problem imo2018_p3 : does_exist ↔ exists_desired_triangle := by
  simp only [exists_desired_triangle, Bool.false_eq_true, false_iff]
  rintro ⟨t, ht⟩
  sorry


end Imo2018P3
