/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import Compfiles.Meta.ProblemExtraction

problem_file

/-!
# International Mathematical Olympiad 1982, Problem 1

Let f be a function from positive integers to nonnegative integers such that
 1) f(2) = 0
 2) f(3) > 0
 3) f(9999) = 3333
 4) for all m,n > 0, f (m + n) - f (m) - f(n) = 1 or 0

Determine the value of f(1982).
-/

namespace Imo1982P1

determine solution_value : ℕ := 660

problem imo1982_p1 (f : ℕ → ℕ)
    (h2 : f 2 = 0)
    (h3 : 0 < f 3)
    (h9999 : f 9999 = 3333)
    (hf : ∀ m n, 0 < m → 0 < n → f (m + n) = f m + f n ∨ f (m + n) = f m + f n + 1) :
    f 1982 = solution_value := by
  sorry
