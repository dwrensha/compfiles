/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 2014, Problem 2

Let $n \ge 2$ be an integer. Consider an $n \times n$ chessboard consisting of
$n^2$ unit squares. A configuration of $n$ rooks on this board is *peaceful* if
every row and every column contains exactly one rook. Find the greatest positive
integer $k$ such that, for each peaceful configuration of $n$ rooks, there is a
$k \times k$ square which does not contain a rook on any of its $k^2$ unit
squares.
-/

namespace Imo2014P2

variable {n : ℕ}

/-- A peaceful configuration of `n` rooks is a permutation `σ`: the rook in
row `i` sits in column `σ i`. Such a configuration has a rook-free `k × k`
square if there is a block of `k` consecutive rows and `k` consecutive columns
(fitting on the board) containing no rook. -/
def HasEmptySquare (σ : Equiv.Perm (Fin n)) (k : ℕ) : Prop :=
  ∃ r c : ℕ, r + k ≤ n ∧ c + k ≤ n ∧
    ∀ i : Fin n, r ≤ (i : ℕ) → (i : ℕ) < r + k →
      ¬ (c ≤ (σ i : ℕ) ∧ (σ i : ℕ) < c + k)

determine greatestK : ℕ → ℕ := fun n ↦ Nat.sqrt (n - 1)

problem imo2014_p2 (n : ℕ) (hn : 2 ≤ n) :
    IsGreatest {k : ℕ | ∀ σ : Equiv.Perm (Fin n), HasEmptySquare σ k} (greatestK n) := by
  sorry

end Imo2014P2
