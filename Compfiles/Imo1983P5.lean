/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InternLM-MATH LEAN Formalizer v0.1. This is auto-formalized by InternLM-MATH LEAN Formalizer v0.1, modified and verified by InternLM-MATH team members.
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 1983, Problem 5

Is it possible to choose $1983$ distinct positive integers, all less than or equal to $10^5$, no three of which are consecutive terms of an arithmetic progression? Justify your answer.
-/

namespace Imo1983P5

problem imo1983_p5 :
    ∃ S : Finset ℕ, S.card = 1983 ∧ (∀ x ∈ S, x ≤ 10^5) ∧
    ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x < y ∧ y < z → x + z ≠ 2 * y := by sorry