/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1965, Problem 5

Suppose OAB is a triangle with acute angle AOB. Through a point M ≠ O
perpendiculars are drawn to OA and OB, the feet of which are P and Q
respectively. The point of intersection of the altitudes of △OPQ is H.
What is the locus of H if M is permitted to range over

(a) the side AB,

(b) the interior of △OAB?

Answer: (a) the segment XY, and (b) the interior of the triangle OXY,
where X is the foot of the perpendicular from B to the line OA and
Y is the foot of the perpendicular from A to the line OB.
-/

namespace Imo1965P5

open RealInnerProductSpace

/-- The Euclidean plane in which the problem takes place.  We place the
vertex `O` of the triangle at the origin. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The foot of the perpendicular from the point `u` to the line through the
origin `O` and the point `v` (for `v ≠ 0`). -/
noncomputable def foot (u v : Plane) : Plane := (⟪u, v⟫ / ⟪v, v⟫) • v

/-- `IsOrthocenter A B M H` says that `H` is the orthocenter of the triangle
`OPQ`, where `O` is the origin and `P`, `Q` are the feet of the perpendiculars
from `M` to the lines `OA` and `OB` respectively.  The two conditions say that
`H` lies on the altitude of `△OPQ` from `P` (which is perpendicular to `OQ`)
and on the altitude from `Q` (which is perpendicular to `OP`); when `P` and
`Q` are linearly independent these two conditions determine `H` uniquely
(see `IsOrthocenter.unique` below). -/
def IsOrthocenter (A B M H : Plane) : Prop :=
  ⟪H - foot M A, foot M B⟫ = 0 ∧ ⟪H - foot M B, foot M A⟫ = 0

/-- The answer to part (a): the locus of `H` is the open segment `XY`, where
`Y = foot A B` is the foot of the perpendicular from `A` to the line `OB` and
`X = foot B A` is the foot of the perpendicular from `B` to the line `OA`. -/
noncomputable determine locus_segment (A B : Plane) : Set Plane :=
  openSegment ℝ (foot A B) (foot B A)

/-- The answer to part (b): the locus of `H` is the interior of the triangle
`OXY`, expressed here in barycentric coordinates (which is what the interior
of a nondegenerate triangle with a vertex at the origin looks like). -/
noncomputable determine locus_interior (A B : Plane) : Set Plane :=
  {H : Plane | ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ α + β < 1 ∧
    H = α • foot A B + β • foot B A}

snip begin

/-- Two linearly independent vectors stay linearly independent when rescaled
by nonzero scalars. -/
lemma LinearIndependent.pair_smul {x y : Plane} {p q : ℝ}
    (h : LinearIndependent ℝ ![x, y]) (hp : p ≠ 0) (hq : q ≠ 0) :
    LinearIndependent ℝ ![p • x, q • y] := by
  rw [LinearIndependent.pair_iff] at h ⊢
  intro s t hst
  have hst' : (s * p) • x + (t * q) • y = 0 := by
    simpa only [smul_smul] using hst
  obtain ⟨h1, h2⟩ := h _ _ hst'
  exact ⟨by simpa [hp] using h1, by simpa [hq] using h2⟩

/-- When `M = α • A + β • B` is a positive combination of `A` and `B`, the feet
`P = foot M A` and `Q = foot M B` are linearly independent (so that `△OPQ` is
nondegenerate).  This is where the acuteness of the angle at `O` is used. -/
lemma linearIndependent_feet {A B : Plane} {α β : ℝ}
    (hind : LinearIndependent ℝ ![A, B]) (hacute : 0 < ⟪A, B⟫)
    (hα : 0 < α) (hβ : 0 < β) :
    LinearIndependent ℝ ![foot (α • A + β • B) A, foot (α • A + β • B) B] := by
  have hA : A ≠ 0 := hind.ne_zero 0
  have hB : B ≠ 0 := hind.ne_zero 1
  have ha : 0 < ⟪A, A⟫ := real_inner_self_pos.mpr hA
  have hb : 0 < ⟪B, B⟫ := real_inner_self_pos.mpr hB
  have hab : ⟪B, A⟫ = ⟪A, B⟫ := real_inner_comm A B
  have h1 : (0 : ℝ) < ⟪α • A + β • B, A⟫ := by
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hab]
    positivity
  have h2 : (0 : ℝ) < ⟪α • A + β • B, B⟫ := by
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    positivity
  show LinearIndependent ℝ ![(⟪α • A + β • B, A⟫ / ⟪A, A⟫) • A,
      (⟪α • A + β • B, B⟫ / ⟪B, B⟫) • B]
  exact LinearIndependent.pair_smul hind (div_pos h1 ha).ne' (div_pos h2 hb).ne'

/-- The key computation: for `M = α • A + β • B`, the point
`H = α • foot A B + β • foot B A` — the *same* barycentric combination of the
feet of the two altitudes of `△OAB` — satisfies the orthocenter conditions
for `△OPQ`. -/
lemma isOrthocenter_explicit {A B : Plane} (hA : A ≠ 0) (hB : B ≠ 0) (α β : ℝ) :
    IsOrthocenter A B (α • A + β • B) (α • foot A B + β • foot B A) := by
  have ha : ⟪A, A⟫ ≠ 0 := inner_self_ne_zero.mpr hA
  have hb : ⟪B, B⟫ ≠ 0 := inner_self_ne_zero.mpr hB
  have hab : ⟪B, A⟫ = ⟪A, B⟫ := real_inner_comm A B
  unfold IsOrthocenter foot
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left,
    real_inner_smul_right]
  rw [hab]
  constructor <;> field_simp [ha, hb] <;> ring

/-- The orthocenter conditions determine `H` uniquely whenever `P` and `Q`
are linearly independent. -/
lemma IsOrthocenter.unique {A B M H₁ H₂ : Plane}
    (hind : LinearIndependent ℝ ![foot M A, foot M B])
    (h₁ : IsOrthocenter A B M H₁) (h₂ : IsOrthocenter A B M H₂) : H₁ = H₂ := by
  have hP : ⟪H₁ - H₂, foot M A⟫ = 0 := by
    have e1 := h₁.2
    have e2 := h₂.2
    rw [inner_sub_left] at e1 e2 ⊢
    linarith
  have hQ : ⟪H₁ - H₂, foot M B⟫ = 0 := by
    have e1 := h₁.1
    have e2 := h₂.1
    rw [inner_sub_left] at e1 e2 ⊢
    linarith
  have hrange : Set.range ![foot M A, foot M B] = {foot M A, foot M B} := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
  have hspan : Submodule.span ℝ {foot M A, foot M B} = ⊤ := by
    have hcard := linearIndependent_iff_card_eq_finrank_span.mp hind
    rw [Fintype.card_fin, Set.finrank, hrange] at hcard
    apply Submodule.eq_top_of_finrank_eq
    rw [← hcard, finrank_euclideanSpace, Fintype.card_fin]
  have hmem : H₁ - H₂ ∈ Submodule.span ℝ {foot M A, foot M B} := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨s, t, hst⟩ := Submodule.mem_span_pair.mp hmem
  have hww : ⟪H₁ - H₂, H₁ - H₂⟫ = 0 := by
    nth_rewrite 2 [← hst]
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hP, hQ,
      mul_zero, mul_zero, add_zero]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hww)

snip end

/-- IMO 1965 Problem 5, part (a): as `M` ranges over the side `AB`, the locus
of the orthocenter `H` of `△OPQ` is the segment `XY`. -/
problem imo1965_p5a (A B : Plane)
    (hind : LinearIndependent ℝ ![A, B]) (hacute : 0 < ⟪A, B⟫) :
    {H : Plane | ∃ M ∈ openSegment ℝ A B, IsOrthocenter A B M H} =
      locus_segment A B := by
  ext H
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨M, hM, horth⟩
    obtain ⟨a, b, ha, hb, hab, hM_eq⟩ := hM
    rw [← hM_eq] at horth
    have hH := horth.unique (linearIndependent_feet hind hacute ha hb)
      (isOrthocenter_explicit (hind.ne_zero 0) (hind.ne_zero 1) a b)
    exact ⟨a, b, ha, hb, hab, hH.symm⟩
  · rintro ⟨a, b, ha, hb, hab, hH⟩
    refine ⟨a • A + b • B, ⟨a, b, ha, hb, hab, rfl⟩, ?_⟩
    rw [← hH]
    exact isOrthocenter_explicit (hind.ne_zero 0) (hind.ne_zero 1) a b

/-- IMO 1965 Problem 5, part (b): as `M` ranges over the interior of `△OAB`,
the locus of the orthocenter `H` of `△OPQ` is the interior of `△OXY`. -/
problem imo1965_p5b (A B : Plane)
    (hind : LinearIndependent ℝ ![A, B]) (hacute : 0 < ⟪A, B⟫) :
    {H : Plane | ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ α + β < 1 ∧
      IsOrthocenter A B (α • A + β • B) H} = locus_interior A B := by
  ext H
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨α, β, hα, hβ, hab, horth⟩
    exact ⟨α, β, hα, hβ, hab, horth.unique (linearIndependent_feet hind hacute hα hβ)
      (isOrthocenter_explicit (hind.ne_zero 0) (hind.ne_zero 1) α β)⟩
  · rintro ⟨α, β, hα, hβ, hab, hH⟩
    refine ⟨α, β, hα, hβ, hab, ?_⟩
    rw [hH]
    exact isOrthocenter_explicit (hind.ne_zero 0) (hind.ne_zero 1) α β

end Imo1965P5
