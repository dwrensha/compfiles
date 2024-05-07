/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Batteries.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
USA Mathematical Olympiad 1999, Problem 1

Some checkers placed on an n × n checkerboard satisfy the following conditions:
 a. every square that does not contain a checker shares a side with one that does;
 b. given any pair of squares that contain checkers, there is a sequence of squares
    containing checkers, starting and ending with the given squares, such that
    every two consecutive squares of the sequence share a side.

Prove that at least (n²-2)/3 checkers have been placed on the board.
-/

namespace Usa1999P1

def checkerboard (n : ℕ) := Fin n × Fin n

def adjacent {n : ℕ} : checkerboard n → checkerboard n → Prop
| ⟨a1, a2⟩, ⟨b1, b2⟩ =>
  (a1.val = b1.val ∧ a2.val = b2.val + 1) ∨
  (a1.val = b1.val ∧ a2.val + 1 = b2.val) ∨
  (a2.val = b2.val ∧ a1.val = b1.val + 1) ∨
  (a2.val = b2.val ∧ a1.val + 1 = b1.val )

problem usa1999_p1 (n : ℕ) (c : Finset (checkerboard n))
    (ha : ∀ x : checkerboard n, x ∈ c ∨ (∃ y ∈ c, adjacent x y))
    (hb : ∀ x ∈ c, ∀ y ∈ c,
      ∃ p : List (checkerboard n),
        List.Chain' adjacent p ∧
        List.head? p = x ∧
        List.getLast? p = y) :
    n^2 ≤ c.card * 3 + 2 := by
  sorry
