/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 2009, Problem 3

Suppose that $s_1, s_2, s_3, \ldots$ is a strictly increasing sequence of
positive integers such that the subsequences
$$s_{s_1}, s_{s_2}, s_{s_3}, \ldots \quad\text{and}\quad s_{s_1+1}, s_{s_2+1}, s_{s_3+1}, \ldots$$
are both arithmetic progressions. Prove that the sequence
$s_1, s_2, s_3, \ldots$ is itself an arithmetic progression.
-/

namespace Imo2009P3

/-- A sequence `f : ℕ → ℕ` is an arithmetic progression. -/
def IsArithProg (f : ℕ → ℕ) : Prop := ∃ d : ℕ, ∀ n, f (n + 1) = f n + d

problem imo2009_p3 (s : ℕ → ℕ) (hs : StrictMono s) (hpos : ∀ i, 0 < s i)
    (h1 : IsArithProg (fun n ↦ s (s n)))
    (h2 : IsArithProg (fun n ↦ s (s n + 1))) :
    IsArithProg s := by
  sorry

end Imo2009P3
