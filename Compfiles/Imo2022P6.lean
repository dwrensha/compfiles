/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib

import ProblemExtraction

problem_file {
  tags := [.Combinatorics]
  problemImportedFrom :=
    "https://github.com/jsm28/IMOLean/blob/main/IMO/IMO2022P6.lean"
}

/-!
# International Mathematical Olympiad 2022, Problem 6

Let n be a positive integer. A Nordic square is an n×n board containing
all the integers from 1 to n² so that each cell contains exactly one
number. Two different cells are considered adjacent if they share a
common side. Every cell that is adjacent only to cells containing larger
numbers is called a valley. An uphill path is a sequence of one or more
cells such that:

  (1) the first cell in the sequence is a valley,
  (2) each subsequent cell in the sequence is adjacent to the
      previous cell, and
  (3) the numbers written in the cells in the sequence are in
      increasing order.

Find, as a function of n, the smallest possible total number of uphill
paths in a Nordic square.
-/

open scoped Cardinal

namespace Imo2022P6

/-- A cell of the board. -/
abbrev Cell (n : ℕ) : Type := Fin n × Fin n

/-- A Nordic square. -/
abbrev NordicSquare (n : ℕ) : Type := Cell n ≃ Finset.Icc 1 (n ^ 2)

/-- Whether two cells are adjacent. -/
def Adjacent {n : ℕ} (x y : Cell n) : Prop :=
  Nat.dist x.1 y.1 + Nat.dist x.2 y.2 = 1

/-- The definition of a valley from the problem. -/
def NordicSquare.Valley {n : ℕ} (ns : NordicSquare n) (c : Cell n) : Prop :=
  ∀ c' : Cell n, Adjacent c c' → (ns c : ℕ) < (ns c' : ℕ)

/-- The definition of an uphill path from the problem. -/
structure NordicSquare.UphillPath {n : ℕ} (ns : NordicSquare n) where
  /-- The cells on the path. -/
  cells : List (Cell n)
  nonempty : cells ≠ []
  first_valley : ns.Valley (cells.head nonempty)
  adjacent : cells.IsChain Adjacent
  increasing : cells.IsChain fun x y ↦ (ns x : ℕ) < (ns y : ℕ)

determine answer : ℕ+ → ℕ := sorry

problem imo2022_p6 {n : ℕ+} :
    IsLeast {k : ℕ | ∃ ns : NordicSquare n, #ns.UphillPath = k} (answer n) := by
  sorry

end Imo2022P6
