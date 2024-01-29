/-
Copyright (c) 2021 Tian Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tian Chen
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

import ProblemExtraction

problem_file {
  tags := [.Algebra, .Inequality],
  importedFrom :=
    "https://github.com/leanprover-community/mathlib4/blob/master/Archive/Imo/Imo2001Q2.lean"
}

/-!
# International Mathematical Olympiad 2001, Problem 2

Let a, b, c be positive reals. Prove that

    a / √(a² + 8bc) + b / √(b² + 8ca) + c / √(c² + 8ab) ≥ 1.
-/

open Real

namespace Imo2001P2

variable {a b c : ℝ}

snip begin

/-
## Solution

This proof is based on the bound
$$
\frac{a}{\sqrt{a^2 + 8bc}} ≥
\frac{a^{\frac43}}{a^{\frac43} + b^{\frac43} + c^{\frac43}}.
$$
-/

theorem bound (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 4 / (a ^ 4 + b ^ 4 + c ^ 4) ≤ a ^ 3 / sqrt ((a ^ 3) ^ 2 + 8 * b ^ 3 * c ^ 3) := by
  rw [div_le_div_iff (by positivity) (by positivity)]
  calc a ^ 4 * sqrt ((a ^ 3) ^ 2 + (8:ℝ) * b ^ 3 * c ^ 3)
      = a ^ 3 * (a * sqrt ((a ^ 3) ^ 2 + (8:ℝ) * b ^ 3 * c ^ 3)) := by ring
    _ ≤ a ^ 3 * (a ^ 4 + b ^ 4 + c ^ 4) := ?_
  gcongr
  apply le_of_pow_le_pow_left two_ne_zero (by positivity)
  rw [mul_pow, sq_sqrt (by positivity), ← sub_nonneg]
  calc
    (a ^ 4 + b ^ 4 + c ^ 4) ^ 2 - a ^ 2 * ((a ^ 3) ^ 2 + 8 * b ^ 3 * c ^ 3)
      = 2 * (a ^ 2 * (b ^ 2 - c ^ 2)) ^ 2 + (b ^ 4 - c ^ 4) ^ 2 +
        (2 * (a ^ 2 * b * c - b ^ 2 * c ^ 2)) ^ 2 := by ring
    _ ≥ 0 := by positivity

theorem imo2001_p2' (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 ≤ a ^ 3 / sqrt ((a ^ 3) ^ 2 + 8 * b ^ 3 * c ^ 3) +
      b ^ 3 / sqrt ((b ^ 3) ^ 2 + 8 * c ^ 3 * a ^ 3) +
        c ^ 3 / sqrt ((c ^ 3) ^ 2 + 8 * a ^ 3 * b ^ 3) :=
  have H : a ^ 4 + b ^ 4 + c ^ 4 ≠ 0 := by positivity
  calc
    _ ≥ _ := add_le_add (add_le_add (bound ha hb hc) (bound hb hc ha)) (bound hc ha hb)
    _ = 1 := by ring_nf at H ⊢; field_simp

snip end

problem imo2001_p2 (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 ≤
    a / sqrt (a ^ 2 + 8 * b * c) + b / sqrt (b ^ 2 + 8 * c * a) +
    c / sqrt (c ^ 2 + 8 * a * b) :=
  have h3 : ∀ {x : ℝ}, 0 < x → (x ^ (3 : ℝ)⁻¹) ^ 3 = x := fun hx =>
    show ↑3 = (3 : ℝ) by norm_num ▸ rpow_inv_natCast_pow hx.le three_ne_zero
  calc
    1 ≤ _ := imo2001_p2' (rpow_pos_of_pos ha (3 : ℝ)⁻¹)
                         (rpow_pos_of_pos hb (3 : ℝ)⁻¹)
                         (rpow_pos_of_pos hc (3 : ℝ)⁻¹)
    _ = _ := by rw [h3 ha, h3 hb, h3 hc]
