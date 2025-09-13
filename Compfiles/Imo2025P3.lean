/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reuven Peleg (Problem statement)
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Bounds.Basic

import ProblemExtraction

problem_file {
  tags := [.NumberTheory]
}

/-!
# International Mathematical Olympiad 2025, Problem 3

Let N denote the set of positive integers.

A function f : N → N is said to be bonza if f(a) divides b ^ a − f(b) ^ f(a) for all positive integers a and b.

Determine the smallest real constant c such that f(n) ⩽ cn for all bonza functions f and all positive integers n.
-/
open Int

def Bonza (f : ℕ+ → ℕ+) : Prop :=
  ∀ a b : ℕ+,
    (f a : Int) ∣ ((b : Int) ^ (a: ℕ) - (f b : Int) ^ ((f a): ℕ))

def is_valid_c (c : ℝ) : Prop :=
  ∀ (f : ℕ+ → ℕ+), Bonza f → ∀ n, (f n : ℝ) ≤ c * (n : ℝ)

determine answer : ℝ := 4

problem imo2025_p3 :
  IsLeast {c: ℝ | is_valid_c c} answer := by
  sorry
