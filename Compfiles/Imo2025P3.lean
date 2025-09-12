/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reuven Peleg (Problem statement)
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic

/-!
# International Mathematical Olympiad 2025, Problem 3

Let N denote the set of positive integers.

A function f : N → N is said to be bonza if f(a) divides b ^ a − f(b) ^ f(a) for all positive integers a and b.

Determine the smallest real constant c such that f(n) ⩽ cn for all bonza functions f and all positive integers n.
-/
open Int

/-- A function f : ℕ → ℕ is `bonza` when for all positive a,b we have
    f(a) divides b^a - f(b)^{f(a)} (as integers). -/
def is_bonza (f : ℕ → ℕ) : Prop :=
  ∀ (a b : ℕ), a ≠ 0 → b ≠ 0 →
    (f a : Int) ∣ ((b : Int) ^ a - (f b : Int) ^ (f a))

def is_valid_c (c : ℝ) : Prop :=
  ∀ (f : ℕ → ℕ), is_bonza f → ∀ n, n ≠ 0 → (f n : ℝ) ≤ c * (n : ℝ)

def is_smallest_c (c : ℝ) : Prop :=
  is_valid_c c ∧
  ∀ c', is_valid_c c' → c' ≥ c

/-!
The answer is 4
-/
theorem smallest_c_is_4 : is_smallest_c 4 := by sorry
