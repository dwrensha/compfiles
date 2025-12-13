/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Chen
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

import ProblemExtraction

problem_file { tags := [.Algebra, .Inequality] }

/-!
# USA Mathematical Olympiad 2003, Problem 5

-/

namespace Usa2003P5

snip begin

-- This is the solution at https://web.evanchen.cc/exams/USAMO-2003-notes.pdf
-- We skip the homogenization step and directly encode it in the inequality
-- to make life easier on the Lean side

lemma bound {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (2*a+b+c)^2/(2*a^2+(b+c)^2) ≤ 4*a/(a+b+c) + 4/3 := by
  field_simp
  have h : 0 ≤ (2*a-b-c)^2 * (15*a+3*b+3*c) := by positivity
  linarith

snip end

problem usa2003_p5 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (2*a+b+c)^2/(2*a^2+(b+c)^2) + (2*b+c+a)^2/(2*b^2+(c+a)^2) +
    (2*c+a+b)^2/(2*c^2+(a+b)^2) ≤ 8 := by
  have h1 := bound ha hb hc
  have h2 := bound hb hc ha
  have h3 := bound hc ha hb
  have h := add_le_add h1 (add_le_add h2 h3)
  convert h using 1 <;> field

end Usa2003P5
