/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongyu Ouyang
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1963, Problem 5

Prove that cos(π/7) - cos(2π/7) + cos(3π/7) = 1/2.
-/

namespace Imo1963P5

open scoped Real

problem imo1963_p5 :
    Real.cos (π/7) - Real.cos (2*π/7) + Real.cos (3*π/7) = 1/2 := by
  sorry
