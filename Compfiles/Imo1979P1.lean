/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file

/-!
# International Mathematical Olympiad 1979, Problem 1

Suppose that p and q are positive integers such that

  p / q = 1 - 1/2 + 1/3 - 1/4 + ... - 1/1318 + 1/1319.

Prove that p is divisible by 1979.
-/

namespace Imo1979P1

open scoped BigOperators

problem imo1979_p1 (p q : ℤ) (hp : 0 < p) (hq : 0 < q)
    (h : (p : ℚ) / q = ∑ i in Finset.range 1319, (-1)^i * (1:ℚ) / (i + 1)) :
    1979 ∣ p := by
  sorry
