/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra, .Inequality] }

/-!
# USA Mathematical Olympiad 1978, Problem 1

Given that a,b,c,d,e are real numbers such that

  a  + b  + c  + d  + e  = 8
  a² + b² + c² + d² + e² = 16,

determine the maximum value of e.
-/

namespace Usa1978P1

noncomputable determine max_e : ℝ := sorry

abbrev IsGood (a b c d e : ℝ) : Prop :=
  a + b + c + d + e = 8 ∧ a^2 + b^2 + c^2 + d^2 + e^2 = 16

problem usa1978_p1 :
    IsGreatest { e : ℝ | ∃ a b c d : ℝ, IsGood a b c d e } max_e := by
  sorry
