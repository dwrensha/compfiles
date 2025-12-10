/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Chen
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra, .Inequality] }

/-!
# USA Mathematical Olympiad 2004, Problem 5

Prove that for a,b,c > 0,
(a⁵ - a² + 3) (b⁵ - b² + 3) (c⁵ - c² + 3) ≥ (a + b + c)³.
-/

namespace Usa2004P5

variable {a b c : ℝ}

snip begin
snip end

problem usa2004_p5 (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a^5 - a^2 + 3) * (b^5 - b^2 + 3) * (c^5 - c^2 + 3) ≥ (a + b + c) ^ 3 :=  by
  sorry
end Usa2004P5
