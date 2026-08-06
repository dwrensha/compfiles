/- Copyright (c) 2026 The Compfiles Contributors. All rights reserved. Released under Apache 2.0 license as described in the file LICENSE. Authors: -/

module

public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1959, Problem 3

Let `a`, `b`, `c` be real numbers. Given the equation for `cos x`:

  a cos²x + b cos x + c = 0,

form a quadratic equation in `cos 2x` whose roots are the same values of `x`.
Compare the equations in `cos x` and `cos 2x` for `a = 4`, `b = 2`, `c = -1`.
-/

open Real

namespace Imo1959P3

/-- The coefficients of the quadratic equation in `cos (2 * x)` formed from
`a * cos x ^ 2 + b * cos x + c = 0`: writing `cos (2 * x) = 2 * cos x ^ 2 - 1`
and eliminating the odd power of `cos x` by squaring. -/
determine formedQuadratic (a b c : ℝ) : ℝ × ℝ × ℝ :=
  (a ^ 2, 2 * a ^ 2 + 4 * a * c - 2 * b ^ 2, a ^ 2 + 4 * a * c - 2 * b ^ 2 + 4 * c ^ 2)

/-- The formed quadratic evaluated at `t`, i.e. the quadratic with coefficients
`formedQuadratic a b c` applied to `t`. -/
def formedQuadraticEval (a b c : ℝ) (t : ℝ) : ℝ :=
  (formedQuadratic a b c).1 * t ^ 2 + (formedQuadratic a b c).2.1 * t +
    (formedQuadratic a b c).2.2

snip begin

/-- Squaring the rearranged equation `b * cos x = -(a * cos x ^ 2 + c)`
eliminates the odd power of `cos x`. -/
lemma sq_b_mul_cos (a b c x : ℝ) (h : a * cos x ^ 2 + b * cos x + c = 0) :
    b ^ 2 * cos x ^ 2 = (a * cos x ^ 2 + c) ^ 2 := by
  have h1 : b * cos x = -(a * cos x ^ 2 + c) := by linarith
  calc b ^ 2 * cos x ^ 2 = (b * cos x) ^ 2 := by ring
    _ = (a * cos x ^ 2 + c) ^ 2 := by rw [h1]; ring

/-- The formed quadratic evaluated at `cos (2 * x)`, expressed back in terms of
`cos x` via `cos (2 * x) = 2 * cos x ^ 2 - 1`. -/
lemma formedQuadratic_cos_two_mul (a b c x : ℝ) :
    formedQuadraticEval a b c (cos (2 * x)) =
      4 * ((a * cos x ^ 2 + c) ^ 2 - b ^ 2 * cos x ^ 2) := by
  unfold formedQuadraticEval formedQuadratic
  rw [cos_two_mul x]
  ring

snip end

problem imo1959_p3 (a b c x : ℝ) (h : a * cos x ^ 2 + b * cos x + c = 0) :
    formedQuadraticEval a b c (cos (2 * x)) = 0 := by
  rw [formedQuadratic_cos_two_mul, sq_b_mul_cos a b c x h]
  ring

/-- For `a = 4`, `b = 2`, `c = -1` the formed equation in `cos 2x` is four
times the original equation in `cos x`: the two equations are the same. -/
problem imo1959_p3_comparison (t : ℝ) :
    formedQuadraticEval 4 2 (-1) t = 4 * (4 * t ^ 2 + 2 * t - 1) := by
  unfold formedQuadraticEval formedQuadratic; ring

end Imo1959P3
