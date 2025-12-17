/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Chen
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

import ProblemExtraction

problem_file {
  tags := [.Algebra, .Inequality]
  videos := ["https://youtu.be/7AF_ekJfk30"]
}

/-!
# USA Mathematical Olympiad 2003, Problem 5

Prove that for a,b,c > 0:
(2a+b+c)² / (2a²+(b+c)²) + (2b+c+a)² / (2b²+(c+a)²) + (2c+a+b)² / (2c²+(a+b)²) ≤ 8
-/

namespace Usa2003P5

snip begin

-- This is the solution at https://web.evanchen.cc/exams/USAMO-2003-notes.pdf
-- We skip the homogenization step and directly encode it in the inequality with x=(a+b+c)/3
-- to make life easier on the Lean side

lemma bound {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (2*a+b+c)^2/(2*a^2+(b+c)^2) ≤ 4*a/(a+b+c) + 4/3 := by
  field_simp
  have h : 0 ≤ (2*a-b-c)^2 * (5*a+b+c) := by positivity
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
