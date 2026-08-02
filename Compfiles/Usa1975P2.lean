/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry, .Inequality] }

/-!
# USA Mathematical Olympiad 1975, Problem 2

Show that for any tetrahedron the sum of the squares of the lengths of two
opposite edges is at most the sum of the squares of the other four.
-/

namespace Usa1975P2

open scoped RealInnerProductSpace

snip begin

/-- Vector form of the inequality: if `b`, `c`, `d` are the position vectors
of the vertices `B`, `C`, `D` of the tetrahedron relative to `A`, then the
right-hand side minus the left-hand side equals `‖b - c - d‖ ^ 2`, which is
nonnegative. (Solution from https://prase.cz/kalva/usa/usoln/usol752.html) -/
lemma norm_sq_add_norm_sq_sub_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (b c d : V) :
    ‖b‖ ^ 2 + ‖c - d‖ ^ 2 ≤ ‖c‖ ^ 2 + ‖d‖ ^ 2 + ‖b - c‖ ^ 2 + ‖b - d‖ ^ 2 := by
  have hbc : ‖b - c‖ ^ 2 = ‖b‖ ^ 2 - 2 * ⟪b, c⟫ + ‖c‖ ^ 2 := norm_sub_sq_real b c
  have hbd : ‖b - d‖ ^ 2 = ‖b‖ ^ 2 - 2 * ⟪b, d⟫ + ‖d‖ ^ 2 := norm_sub_sq_real b d
  have hcd : ‖c - d‖ ^ 2 = ‖c‖ ^ 2 - 2 * ⟪c, d⟫ + ‖d‖ ^ 2 := norm_sub_sq_real c d
  have hbcd : ‖b - c - d‖ ^ 2 = ‖b - c‖ ^ 2 - 2 * ⟪b - c, d⟫ + ‖d‖ ^ 2 :=
    norm_sub_sq_real (b - c) d
  rw [inner_sub_left] at hbcd
  have hnonneg : 0 ≤ ‖b - c - d‖ ^ 2 := sq_nonneg ‖b - c - d‖
  linarith

snip end

problem usa1975_p2
    {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [PseudoMetricSpace P] [NormedAddTorsor V P]
    (A B C D : P) :
    dist A B ^ 2 + dist C D ^ 2 ≤
      dist A C ^ 2 + dist A D ^ 2 + dist B C ^ 2 + dist B D ^ 2 := by
  -- Take `A` as the origin and apply the vector lemma to
  -- `b = B -ᵥ A`, `c = C -ᵥ A`, `d = D -ᵥ A`. Since the vertices are
  -- arbitrary, the same inequality for the other two pairs of opposite
  -- edges follows by relabelling.
  rw [dist_eq_norm_vsub' V A B, dist_eq_norm_vsub V C D, dist_eq_norm_vsub' V A C,
    dist_eq_norm_vsub' V A D, dist_eq_norm_vsub V B C, dist_eq_norm_vsub V B D,
    ← vsub_sub_vsub_cancel_right C D A, ← vsub_sub_vsub_cancel_right B C A,
    ← vsub_sub_vsub_cancel_right B D A]
  exact norm_sq_add_norm_sq_sub_le (B -ᵥ A) (C -ᵥ A) (D -ᵥ A)

end Usa1975P2
