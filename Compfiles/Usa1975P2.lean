/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdelmouksit Sagueni
-/

module

public import Mathlib
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry, .Inequality] }

/-!
# USA Mathematical Olympiad 1975, Problem 2

Let A, B, C, D be four points in Euclidean space. Write AB for the
distance from A to B, and similarly for the other pairs. Prove that

  AC² + BD² + AD² + BC² ≥ AB² + CD².
-/

namespace Usa1975P2

problem usa1975_p2
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A B C D : E) :
    ‖A - C‖ ^ 2 + ‖B - D‖ ^ 2 + ‖A - D‖ ^ 2 + ‖B - C‖ ^ 2
      ≥ ‖A - B‖ ^ 2 + ‖C - D‖ ^ 2 := by
  have h :
      ‖A - C‖ ^ 2 + ‖B - D‖ ^ 2 + ‖A - D‖ ^ 2 + ‖B - C‖ ^ 2 =
        ‖A - B‖ ^ 2 + ‖C - D‖ ^ 2 + ‖(A + B) - (C + D)‖ ^ 2 := by
    simp only [norm_sub_sq_real, norm_add_sq_real, inner_add_left, inner_add_right]
    ring
  rw [h]
  exact le_add_of_nonneg_right (sq_nonneg _)
end Usa1975P2
