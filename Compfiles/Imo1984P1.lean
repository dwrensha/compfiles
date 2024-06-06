/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InternLM-MATH LEAN Formalizer v0.1
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1984, Problem 1

Let $x$, $y$, $z$ be nonnegative real numbers with $x + y + z = 1$.
Show that $0 \leq xy+yz+zx-2xyz \leq \frac{7}{27}$
-/

namespace Imo1984P1

problem imo1984_p1  (x y z : ℝ)
  (h₀ : 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z)
  (h₁ : x + y + z = 1) :
    0 ≤ x * y + y * z + z * x - 2 * x * y * z ∧ x * y + y * z + z * x - 2 * x * y * z ≤
      (7:ℝ) / 27 := by sorry
