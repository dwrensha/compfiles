/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1993, Problem 5

Let ℕ+ be the set of positive integers. Determine whether
there exists a function f : ℕ+ → ℕ+ such that
  i) f(1) = 2
  ii) f(f(n)) = f(n) + 2 for all n.
-/

namespace Imo1993P5

determine DoesExist : Bool := sorry

abbrev Good (f : ℕ+ → ℕ+) : Prop := f 1 = 2 ∧ ∀ n, f (f n) = f n + 2

problem imo1993_p5 :
    if DoesExist then ∃ f, Good f else ¬∃ f, Good f := by
  sorry
