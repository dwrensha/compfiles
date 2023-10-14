/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

import Compfiles.Meta.ProblemExtraction

#[problem_setup]/-!
# International Mathematical Olympiad 1981, Problem 6

Suppose that f : ℕ × ℕ → ℕ satisfies

 1) f (0, y) = y + 1
 2) f (x + 1, 0) = f (x, 1),
 3) f (x + 1, y + 1) = f (x, f (x + 1, y))

for all x y ∈ ℕ.

Determine f (4, 1981).

-/

#[problem_setup] namespace Imo1981P6

/--
Wrapper to prevent the Lean kernel from eagerly trying to normalize
the solution value, which happens to be way too large to normalize.
-/
def no_eval (x : ℕ) : ℕ := x

determine solution_value : ℕ := no_eval ((2^·)^[1984] 1 - 3)

problem imo1981_p6 (f : ℕ → ℕ → ℕ)
    (h1 : ∀ y, f 0 y = y + 1)
    (h2 : ∀ x, f (x + 1) 0 = f x 1)
    (h3 : ∀ x y, f (x + 1) (y + 1) = f x (f (x + 1) y)) :
    f 4 1981 = solution_value := by
  have h4 : ∀ y, f 1 y = y + 2 := by
    intro y
    induction' y using Nat.strongInductionOn with y ih
    cases' y with y
    · simp [h1, h2]
    · rw [h3 0 y, ih y (Nat.lt.base y)]
      rw [h1 (y + 2)]
  have h20 : ∀ y, f 2 y = 2 * y + 3 := by
    intro y;
    induction' y with y ih
    · simp [h1, h2, h3]
    · rw [h3, ih, h3, h3, h3, h4, h1, h1, h1, Nat.succ_eq_add_one]
      ring
  have h21 : ∀ y, f 3 y + 3 = 2^(y + 3) := by
    intro y
    induction' y with y ih
    · simp [h1, h2, h3, h4, h20]
    · rw [h3, h20]
      rw [show 2 * f (2 + 1) y + 3 + 3 = 2 * (f 3 y + 3) by ring]
      rw [ih, ←pow_succ]
  have h6 : ∀ y, f 4 (y + 1) + 3 = 2^(f 4 y + 3) := by
    intro y
    induction' y with y ih
    · rw [h3 3 0, h2 3, h21]
    · rw [h3, ih, h21, ih]
  have h7' : ∀ y, f 4 y + 3 = (2^·)^[y + 3] 1 := by
    intro y
    induction' y with y ih
    · simp [h1, h2, h3, h4]
    · rw [show Nat.succ y + 3 = Nat.succ (y + 3) by rfl]
      rw [Function.iterate_succ']
      rw [h6 y, ih]
      rfl
  have h7 : ∀ y, f 4 y = no_eval ((2^·)^[y + 3] 1 - 3) := by
    intro y
    exact eq_tsub_of_add_eq (h7' y)
  have h8 := h7 1981
  rw [show 1981 + 3 = 1984 by rfl] at h8
  exact h8
