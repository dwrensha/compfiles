/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file

/-!
# International Mathematical Olympiad 2003, Problem 6

Let p be a prime number. Prove that there exists a prime number q
such that for every integer n, the number nᵖ - p is not divisible
by q.
-/

namespace Imo2003P6

problem imo2003_p6 (p : Nat) (hp : p.Prime) :
    ∃ q : ℕ, q.Prime ∧ ∀ n, ¬((q : ℤ) ∣ (n : ℤ)^p - (p : ℤ)) := by
  sorry
