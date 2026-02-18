/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Chen
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalities

import ProblemExtraction

set_option backward.isDefEq.respectTransparency false

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

-- Follows the solution at https://web.evanchen.cc/exams/USAMO-2011-notes.pdf
-- Get rid of the 1's on LHS by homogenizing the given condition away,
-- then simplify and use AM-GM on cyclic sum (c+a)(c+b)/(a+b)^2.

lemma bound (ha : 0 < a) (hb : 0 < b)
    (h : a ^ 2 + b ^ 2 + c ^ 2 + (a + b + c) ^ 2 ≤ 4) :
    1 / 2 * (1 + (c + a) * (c + b) / (a + b)^2) ≤ (a * b + 1) / (a + b)^2 := by
  field_simp
  linarith

lemma cube_root {p q : ℝ} (hp : 0 < p) (hq : 0 < q) : (p^3 * q^3)^(1 / 3 : ℝ) = p * q := by
  rw [show p^3 * q^3 = (p * q)^3 by ring, ← rpow_natCast, ← rpow_mul (by positivity)]
  norm_num

-- AM-GM: yz/x² + xz/y² + xy/z² ≥ 3 when x,y,z > 0
lemma AMGM {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    3 ≤ y * z / x^2 + x * z / y^2 + x * y / z^2 := by
  field_simp
  have amgm := geom_mean_le_arith_mean3_weighted
    (show 0 ≤ 1/3 by norm_num)
    (show 0 ≤ 1/3 by norm_num)
    (show 0 ≤ 1/3 by norm_num)
    (show 0 ≤ y^3 * z^3 by positivity)
    (show 0 ≤ z^3 * x^3 by positivity)
    (show 0 ≤ x^3 * y^3 by positivity)
    (show 1/3 + 1/3 + 1/3 = 1 by norm_num)
  rw [cube_root hx hy, cube_root hy hz, cube_root hz hx] at amgm
  linarith

snip end

problem usa2011_p1 (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a ^ 2 + b ^ 2 + c ^ 2 + (a + b + c) ^ 2 ≤ 4) :
    3 ≤ (a * b + 1) / (a + b) ^ 2 + (b * c + 1) / (b + c) ^ 2 + (c * a + 1) / (c + a) ^ 2 := by
  -- Apply AM-GM on a+b, b+c, c+a
  let S := (c+a)*(c+b)/(a+b)^2 + (a+b)*(a+c)/(b+c)^2 + (b+c)*(b+a)/(c+a)^2
  have hS : 3 ≤ S := by
    convert AMGM (add_pos ha hb) (add_pos hb hc) (add_pos hc ha) using 1
    ring
  have b1 := bound ha hb h
  have b2 := bound hb hc (show b ^ 2 + c ^ 2 + a ^ 2 + (b + c + a) ^ 2 ≤ 4 by linarith)
  have b3 := bound hc ha (show c ^ 2 + a ^ 2 + b ^ 2 + (c + a + b) ^ 2 ≤ 4 by linarith)
  linarith
end Usa2011P1
