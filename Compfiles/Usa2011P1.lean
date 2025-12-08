/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Chen
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

import ProblemExtraction

problem_file { tags := [.Algebra, .Inequality] }

/-!
# USA Mathematical Olympiad 2011, Problem 1

Let a, b, c be positive reals such that a² + b² + c² + (a+b+c)² ≤ 4.
Prove that
(ab+1)/(a+b)² + (bc+1)/(b+c)² + (ca+1)/(c+a)² ≥ 3.
-/

open Real

namespace Usa2011P1

variable {a b c : ℝ}

snip begin

snip end

problem usa2011_p1 (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a ^ 2 + b ^ 2 + c ^ 2 + (a + b + c) ^ 2 ≤ 4) :
    (a * b + 1) / (a + b) ^ 2
    + (b * c + 1) / (b + c) ^ 2
    + (c * a + 1) / (c + a) ^ 2 ≥ 3 :=
  sorry


end Usa2011P1
