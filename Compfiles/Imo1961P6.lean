/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.LinearAlgebra.AffineSpace.Midpoint
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1961, Problem 6

Given 3 non-collinear points A, B, C and a plane p not parallel to ABC and
such that A, B, C are all on the same side of p. Take three arbitrary points
A', B', C' in p. Let A'', B'', C'' be the midpoints of AA', BB', CC'
respectively, and let O be the centroid of A'', B'', C''. What is the locus
of O as A', B', C' vary?
-/

namespace Imo1961P6

/-- The ambient three-dimensional Euclidean space. -/
abbrev Pt := EuclideanSpace ℝ (Fin 3)

/-- The centroid of three points. -/
noncomputable abbrev centroid3 (X Y Z : Pt) : Pt := (1 / 3 : ℝ) • (X + Y + Z)

/-- The answer: the locus of `O` is the plane parallel to `p`
(a level set of the affine function `f` whose zero set is `p`)
that lies halfway between `p` and the centroid of `A`, `B`, `C`. -/
determine locus (f : Pt →ᵃ[ℝ] ℝ) (A B C : Pt) : Set Pt :=
  {O : Pt | f O = f (centroid3 A B C) / 2}

snip begin

/-- `(⅟2 : ℝ)` as an ordinary fraction. -/
lemma invOf_two_real : (⅟2 : ℝ) = 1 / 2 := invOf_eq_right_inv (by norm_num)

/-- The centroid of the midpoints of `X X'`, `Y Y'`, `Z Z'` is the midpoint of
the centroids of `X Y Z` and of `X' Y' Z'`. -/
lemma centroid3_midpoint (X Y Z X' Y' Z' : Pt) :
    centroid3 (midpoint ℝ X X') (midpoint ℝ Y Y') (midpoint ℝ Z Z') =
      midpoint ℝ (centroid3 X Y Z) (centroid3 X' Y' Z') := by
  simp only [centroid3, midpoint_eq_smul_add, invOf_two_real]
  module

/-- An affine function out of a vector space evaluates as `f x = f.linear x + f 0`. -/
lemma affine_eval (f : Pt →ᵃ[ℝ] ℝ) (x : Pt) : f x = f.linear x + f 0 := by
  have h := congrFun (AffineMap.decomp f) x
  simpa only [Pi.add_apply] using h

/-- The centroid of three points of the plane `f = 0` again lies in `f = 0`. -/
lemma f_centroid3_eq_zero {f : Pt →ᵃ[ℝ] ℝ} {X' Y' Z' : Pt}
    (hX : f X' = 0) (hY : f Y' = 0) (hZ : f Z' = 0) :
    f (centroid3 X' Y' Z') = 0 := by
  have hX' : f.linear X' = - f 0 := by linarith [affine_eval f X', hX]
  have hY' : f.linear Y' = - f 0 := by linarith [affine_eval f Y', hY]
  have hZ' : f.linear Z' = - f 0 := by linarith [affine_eval f Z', hZ]
  show f ((1 / 3 : ℝ) • (X' + Y' + Z')) = 0
  rw [affine_eval, map_smul, map_add, map_add, hX', hY', hZ']
  module

/-- Forward direction: every centroid `O` arising from points of `p` lies on the
mid-plane. This is the key computation `O = (G + G') / 2` where `G` and `G'` are
the centroids of `A B C` and `A' B' C'`. -/
lemma mem_locus {f : Pt →ᵃ[ℝ] ℝ} {A B C A' B' C' : Pt}
    (hA' : f A' = 0) (hB' : f B' = 0) (hC' : f C' = 0) :
    f (centroid3 (midpoint ℝ A A') (midpoint ℝ B B') (midpoint ℝ C C')) =
      f (centroid3 A B C) / 2 := by
  rw [centroid3_midpoint, AffineMap.map_midpoint, f_centroid3_eq_zero hA' hB' hC',
    midpoint_eq_smul_add, add_zero, invOf_two_real, smul_eq_mul]
  ring

/-- Reverse direction: every point `O` of the mid-plane arises from some choice
of `A' B' C'` in `p` (take all three equal to the reflection of the centroid of
`A B C` through `O`). -/
lemma locus_mem {f : Pt →ᵃ[ℝ] ℝ} {A B C O : Pt}
    (hO : f O = f (centroid3 A B C) / 2) :
    ∃ A' B' C' : Pt, f A' = 0 ∧ f B' = 0 ∧ f C' = 0 ∧
      O = centroid3 (midpoint ℝ A A') (midpoint ℝ B B') (midpoint ℝ C C') := by
  have hlinO : f.linear O = f O - f 0 := by rw [affine_eval]; ring
  have hlinG : f.linear (centroid3 A B C) = f (centroid3 A B C) - f 0 := by
    rw [affine_eval]; ring
  have key : f ((2 : ℝ) • O - centroid3 A B C) = 0 := by
    rw [affine_eval, map_sub, map_smul, hlinO, hlinG, hO, smul_eq_mul]
    ring
  refine ⟨_, _, _, key, key, key, ?_⟩
  simp only [centroid3, midpoint_eq_smul_add, invOf_two_real]
  module

snip end

/-- The plane `p` is represented as the zero set of an affine function `f` with
nonzero linear part; the sides of `p` are the regions where `f` is positive or
negative, and `p` is parallel to the plane `ABC` exactly when their directions
`f.linear.ker` and `vectorSpan ℝ {A, B, C}` coincide. Note that the conclusion
holds for *every* configuration; the geometric hypotheses (non-collinearity of
`A B C`, `p` not parallel to `ABC`, and `A B C` all on the same side of `p`)
only ensure that the configuration is non-degenerate, and are not needed for
the locus computation itself. -/
problem imo1961_p6
    (A B C : Pt)
    (_hABC : ¬ Collinear ℝ ({A, B, C} : Set Pt))
    (f : Pt →ᵃ[ℝ] ℝ)
    (_hf : f.linear ≠ 0)
    (_hside : (0 < f A ∧ 0 < f B ∧ 0 < f C) ∨ (f A < 0 ∧ f B < 0 ∧ f C < 0))
    (_hnotparallel : f.linear.ker ≠ vectorSpan ℝ ({A, B, C} : Set Pt)) :
    {O : Pt | ∃ A' B' C' : Pt, f A' = 0 ∧ f B' = 0 ∧ f C' = 0 ∧
        O = centroid3 (midpoint ℝ A A') (midpoint ℝ B B') (midpoint ℝ C C')} =
      locus f A B C := by
  ext O
  constructor
  · rintro ⟨A', B', C', hA', hB', hC', rfl⟩
    exact mem_locus hA' hB' hC'
  · intro hO
    exact locus_mem hO

end Imo1961P6
