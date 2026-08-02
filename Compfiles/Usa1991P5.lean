/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Geometry.Euclidean.Sphere.Tangent
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Geometry]
}

/-!
# USA Mathematical Olympiad 1991, Problem 5

X is a point on the side BC of the triangle ABC. Take the other common tangent
(apart from BC) to the incircles of ABX and ACX which intersects the segments AB
and AC. Let it meet AX at Y. Show that the locus of Y, as X varies, is the arc
of a circle.

We prove that `AY = (AB + AC - BC) / 2`, which does not depend on X; hence Y
always lies on the circle centered at A with that radius, i.e. the locus of Y is
(an arc of) a circle.
-/

open scoped EuclideanGeometry Affine RealInnerProductSpace

namespace Usa1991P5

open EuclideanGeometry AffineSubspace RealInnerProductSpace

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)]

snip begin

lemma finiteDimensionalOfFact : FiniteDimensional ℝ V :=
  Module.finite_of_finrank_eq_succ (Fact.out : Module.finrank ℝ V = 2)

attribute [instance] finiteDimensionalOfFact

omit [Fact (Module.finrank ℝ V = 2)] in
/-- If `z ≠ p` are two points of a sphere, then `z -ᵥ p` makes an obtuse angle with
`p -ᵥ c` (the vector from `p` to the center): the sphere lies strictly on one side of
its tangent hyperplane at `p`. -/
lemma inner_vsub_neg_of_mem_sphere {s : Sphere P} {p z : P}
    (hp : p ∈ s) (hz : z ∈ s) (h : z ≠ p) :
    ⟪z -ᵥ p, p -ᵥ s.center⟫ < 0 := by
  have hdist : ‖z -ᵥ s.center‖ = ‖p -ᵥ s.center‖ := by
    have h1 : dist z s.center = s.radius := mem_sphere.1 hz
    have h2 : dist p s.center = s.radius := mem_sphere.1 hp
    rw [dist_eq_norm_vsub] at h1 h2
    rw [h1, h2]
  have hdecomp : z -ᵥ s.center = (z -ᵥ p) + (p -ᵥ s.center) := by
    rw [vsub_add_vsub_cancel]
  have hsq : ⟪z -ᵥ s.center, z -ᵥ s.center⟫ =
      ⟪z -ᵥ p, z -ᵥ p⟫ + 2 * ⟪z -ᵥ p, p -ᵥ s.center⟫ + ⟪p -ᵥ s.center, p -ᵥ s.center⟫ := by
    rw [hdecomp, real_inner_add_add_self]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    hdist] at hsq
  have hne : z -ᵥ p ≠ 0 := vsub_ne_zero.mpr h
  have hpos : (0:ℝ) < ‖z -ᵥ p‖ ^ 2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hne)
  linarith

omit [Fact (Module.finrank ℝ V = 2)] in
/-- The "side functional" of a line is affine: evaluating `⟪· -ᵥ t, n⟫` on a point of
the line through `a b` gives the corresponding affine combination of values. -/
lemma inner_lineMap_vsub (t : P) {a b : P} (n : V) (c : ℝ) :
    ⟪AffineMap.lineMap a b c -ᵥ t, n⟫ =
      (1 - c) * ⟪a -ᵥ t, n⟫ + c * ⟪b -ᵥ t, n⟫ := by
  rw [AffineMap.lineMap_apply, vadd_vsub_assoc]
  have h : b -ᵥ a = (b -ᵥ t) - (a -ᵥ t) := by
    rw [vsub_sub_vsub_cancel_right]
  rw [h]
  simp only [inner_add_left, inner_smul_left, inner_sub_left, conj_trivial]
  ring

omit [Fact (Module.finrank ℝ V = 2)] in
/-- A point strictly between two others is a line map with parameter in `(0, 1)`. -/
lemma lineMap_of_sbtw {a y b : P} (h : Sbtw ℝ a y b) :
    ∃ c ∈ Set.Ioo (0:ℝ) 1, AffineMap.lineMap a b c = y := by
  obtain ⟨hw, hya, hyb⟩ := h
  obtain ⟨c, hc, hline⟩ := hw
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [AffineMap.lineMap_apply_zero] at hline
    exact hya hline.symm
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [AffineMap.lineMap_apply_one] at hline
    exact hyb hline.symm
  exact ⟨c, ⟨lt_of_le_of_ne hc.1 hc0.symm, lt_of_le_of_ne hc.2 hc1⟩, hline⟩

omit [Fact (Module.finrank ℝ V = 2)] in
/-- Crossing lemma: if an affine side-functional vanishes at `y` on the line through
`a b` and takes values of opposite strict sign at `a` and at `b`, then `y` is strictly
between `a` and `b`. -/
lemma sbtw_of_inner_of_mem_line {t y a b : P} {n : V} (hab : a ≠ b)
    (hy : y ∈ line[ℝ, a, b]) (h0 : ⟪y -ᵥ t, n⟫ = 0)
    (ha : 0 < ⟪a -ᵥ t, n⟫) (hb : ⟪b -ᵥ t, n⟫ < 0) :
    Sbtw ℝ a y b := by
  have hmem : y -ᵥ a ∈ vectorSpan ℝ ({a, b} : Set P) :=
    vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan hy
      (left_mem_affineSpan_pair _ _ _)
  rw [vectorSpan_pair] at hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
  have hy_eq : y = AffineMap.lineMap a b (-c) := by
    rw [AffineMap.lineMap_apply]
    have h1 : y -ᵥ a = (-c) • (b -ᵥ a) := by
      rw [← hc, ← neg_vsub_eq_vsub_rev, smul_neg, neg_smul]
    rw [← h1, vsub_vadd]
  have key : ⟪y -ᵥ t, n⟫ = (1 - (-c)) * ⟪a -ᵥ t, n⟫ + (-c) * ⟪b -ᵥ t, n⟫ := by
    rw [hy_eq, inner_lineMap_vsub]
  rw [h0] at key
  have hcI : -c ∈ Set.Ioo (0:ℝ) 1 := by
    constructor <;> nlinarith [key, ha, hb]
  have hW : Wbtw ℝ a y b := ⟨-c, Set.Ioo_subset_Icc_self hcI, hy_eq.symm⟩
  refine ⟨hW, ?_, ?_⟩
  · -- y ≠ a
    intro hya
    have ha0 : AffineMap.lineMap a b (0:ℝ) = a := by
      rw [AffineMap.lineMap_apply, zero_smul, zero_vadd]
    have h1 : AffineMap.lineMap a b (-c) = AffineMap.lineMap a b (0:ℝ) := by
      rw [ha0, ← hy_eq, hya]
    rw [AffineMap.lineMap_apply, AffineMap.lineMap_apply] at h1
    have h2 : (-c) • (b -ᵥ a) = (0:ℝ) • (b -ᵥ a) := by
      have h3 := congrArg (· -ᵥ a) h1
      rwa [vadd_vsub, vadd_vsub] at h3
    rw [zero_smul] at h2
    rcases smul_eq_zero.1 h2 with hc' | hc'
    · nlinarith [hcI.1]
    · exact absurd hc' (vsub_ne_zero.mpr hab.symm)
  · -- y ≠ b
    intro hyb
    have hb1 : AffineMap.lineMap a b (1:ℝ) = b := by
      rw [AffineMap.lineMap_apply, one_smul, vsub_vadd]
    have h1 : AffineMap.lineMap a b (-c) = AffineMap.lineMap a b (1:ℝ) := by
      rw [hb1, ← hy_eq, hyb]
    rw [AffineMap.lineMap_apply, AffineMap.lineMap_apply] at h1
    have h2 : (-c) • (b -ᵥ a) = (1:ℝ) • (b -ᵥ a) := by
      have h3 := congrArg (· -ᵥ a) h1
      rwa [vadd_vsub, vadd_vsub] at h3
    have hb'a : b -ᵥ a ≠ 0 := vsub_ne_zero.mpr hab.symm
    have hc' : -c = 1 := by
      have h4 : (-c - 1) • (b -ᵥ a) = 0 := by
        rw [sub_smul, h2, sub_self]
      rcases smul_eq_zero.1 h4 with h5 | h5
      · linarith
      · exact absurd h5 hb'a
    nlinarith [hcI.2]

/-- A tangent "line" (given by two distinct points) to a sphere in a 2-dimensional
space is the full tangent hyperplane. -/
lemma tangent_line_eq_orthRadius {s : Sphere P} {t a b : P}
    (ht : s.IsTangentAt t (line[ℝ, a, b])) (hr : s.radius ≠ 0) (hab : a ≠ b) :
    line[ℝ, a, b] = s.orthRadius t := by
  have hfd : Module.finrank ℝ line[ℝ, a, b].direction = 1 := by
    rw [direction_affineSpan, vectorSpan_pair]
    exact finrank_span_singleton (vsub_ne_zero.mpr hab)
  exact ht.eq_orthRadius_of_finrank_add_one_eq hr (by rw [hfd, (Fact.out : Module.finrank ℝ V = 2)])

/-- The zero set of the side functional of a tangent line is exactly the line. -/
lemma mem_tangent_line_of_inner_eq_zero {s : Sphere P} {t a b x : P}
    (ht : s.IsTangentAt t (line[ℝ, a, b])) (hr : s.radius ≠ 0) (hab : a ≠ b)
    (hx : ⟪x -ᵥ t, t -ᵥ s.center⟫ = 0) : x ∈ line[ℝ, a, b] := by
  rw [tangent_line_eq_orthRadius ht hr hab]
  exact (Sphere.mem_orthRadius_iff_inner_left).2 hx

omit [Fact (Module.finrank ℝ V = 2)] in
/-- Two points of a collinear configuration determine the same line. -/
lemma line_eq_line_of_wbtw {a b c : P} (h : Wbtw ℝ a b c) (hab : a ≠ b) (hbc : b ≠ c) :
    line[ℝ, a, b] = line[ℝ, a, c] := by
  have hb : b ∈ line[ℝ, a, c] := affineSegment_subset_affineSpan ℝ a c h
  have hc : c ∈ line[ℝ, a, b] := by
    have hcoll : Collinear ℝ ({a, b, c} : Set P) := h.collinear
    exact hcoll.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hab
  apply le_antisymm
  · rw [affineSpan_le]
    rintro x (rfl | rfl)
    · exact left_mem_affineSpan_pair _ _ _
    · exact hb
  · rw [affineSpan_le]
    rintro x (rfl | rfl)
    · exact left_mem_affineSpan_pair _ _ _
    · exact hc

/-- The external common tangent segment squared between two spheres tangent to a common
line, with centers on the same side, equals `d² - (r₁ - r₂)²`. -/
lemma dist_touchpoint_sq_eq_of_same_side {ω₁ ω₂ : Sphere P} {as : AffineSubspace ℝ P}
    {t₁ t₂ : P} (h₁ : ω₁.IsTangentAt t₁ as) (h₂ : ω₂.IsTangentAt t₂ as)
    (hr₁ : ω₁.radius ≠ 0) (hfr : Module.finrank ℝ as.direction = 1)
    (hside : 0 < ⟪ω₂.center -ᵥ t₂, ω₁.center -ᵥ t₁⟫) :
    dist t₁ t₂ ^ 2 = dist ω₁.center ω₂.center ^ 2 - (ω₁.radius - ω₂.radius) ^ 2 := by
  have hd₁ : ω₁.center -ᵥ t₁ ∈ as.directionᗮ := by
    rw [Submodule.mem_orthogonal]
    intro v hv
    have hle : as.direction ≤ (ω₁.orthRadius t₁).direction := direction_le h₁.le_orthRadius
    rw [Sphere.direction_orthRadius] at hle
    have hv2 : ⟪v, t₁ -ᵥ ω₁.center⟫ =
        0 := Submodule.inner_left_of_mem_orthogonal (Submodule.mem_span_singleton_self _) (hle hv)
    rw [← neg_vsub_eq_vsub_rev, inner_neg_right, hv2, neg_zero]
  have hd₂ : ω₂.center -ᵥ t₂ ∈ as.directionᗮ := by
    rw [Submodule.mem_orthogonal]
    intro v hv
    have hle : as.direction ≤ (ω₂.orthRadius t₂).direction := direction_le h₂.le_orthRadius
    rw [Sphere.direction_orthRadius] at hle
    have hv2 : ⟪v, t₂ -ᵥ ω₂.center⟫ =
        0 := Submodule.inner_left_of_mem_orthogonal (Submodule.mem_span_singleton_self _) (hle hv)
    rw [← neg_vsub_eq_vsub_rev, inner_neg_right, hv2, neg_zero]
  have hfr' : Module.finrank ℝ as.directionᗮ = 1 := by
    have h := Submodule.finrank_add_finrank_orthogonal as.direction
    rw [hfr, (Fact.out : Module.finrank ℝ V = 2)] at h
    omega
  have hne₁ : ω₁.center -ᵥ t₁ ≠ 0 := by
    rw [ne_eq, vsub_eq_zero_iff_eq]
    intro hcc
    have hd : dist t₁ ω₁.center = ω₁.radius := mem_sphere.1 h₁.mem_sphere
    rw [← hcc, dist_self] at hd
    exact hr₁ hd.symm
  have hspan : as.directionᗮ = ℝ ∙ (ω₁.center -ᵥ t₁) :=
    (Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).2 hd₁)
      (by rw [finrank_span_singleton hne₁, hfr'])).symm
  obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.1 (hspan ▸ hd₂)
  have hμpos : 0 < μ := by
    have hnormpos : (0:ℝ) < ⟪ω₁.center -ᵥ t₁, ω₁.center -ᵥ t₁⟫ := by
      rw [real_inner_self_eq_norm_sq]
      exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hne₁)
    have heq : ⟪ω₂.center -ᵥ t₂, ω₁.center -ᵥ t₁⟫ =
        μ * ⟪ω₁.center -ᵥ t₁, ω₁.center -ᵥ t₁⟫ := by
      rw [← hμ, inner_smul_left, conj_trivial]
    nlinarith [hside, hnormpos]
  have hn₁ : ‖ω₁.center -ᵥ t₁‖ = ω₁.radius := by
    have hd : dist ω₁.center t₁ = ω₁.radius := mem_sphere'.1 h₁.mem_sphere
    rw [dist_eq_norm_vsub] at hd
    exact hd
  have hn₂ : ‖ω₂.center -ᵥ t₂‖ = ω₂.radius := by
    have hd : dist ω₂.center t₂ = ω₂.radius := mem_sphere'.1 h₂.mem_sphere
    rw [dist_eq_norm_vsub] at hd
    exact hd
  have hμr : μ * ω₁.radius = ω₂.radius := by
    rw [← hn₂, ← hμ, norm_smul, Real.norm_eq_abs, abs_of_pos hμpos, hn₁]
  have hdecomp : ω₂.center -ᵥ ω₁.center =
      (t₂ -ᵥ t₁) + ((ω₂.center -ᵥ t₂) - (ω₁.center -ᵥ t₁)) := by
    rw [← add_sub_assoc, add_comm (t₂ -ᵥ t₁) (ω₂.center -ᵥ t₂), vsub_add_vsub_cancel, vsub_sub_vsub_cancel_right]
  have hint : ⟪t₂ -ᵥ t₁, (ω₂.center -ᵥ t₂) - (ω₁.center -ᵥ t₁)⟫ = 0 := by
    have hmem : t₂ -ᵥ t₁ ∈ as.direction := vsub_mem_direction h₂.mem_space h₁.mem_space
    rw [inner_sub_right, Submodule.inner_right_of_mem_orthogonal hmem hd₂,
      Submodule.inner_right_of_mem_orthogonal hmem hd₁, sub_zero]
  have hnorm := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hint
  rw [← hdecomp] at hnorm
  have hnorm₂ : ‖(ω₂.center -ᵥ t₂) - (ω₁.center -ᵥ t₁)‖ ^ 2 =
      (ω₂.radius - ω₁.radius) ^ 2 := by
    have hsub : (ω₂.center -ᵥ t₂) - (ω₁.center -ᵥ t₁) = (μ - 1) • (ω₁.center -ᵥ t₁) := by
      rw [← hμ, sub_smul, one_smul]
    rw [hsub, norm_smul, Real.norm_eq_abs, hn₁, mul_pow, sq_abs]
    have h3 : (μ - 1) * ω₁.radius = ω₂.radius - ω₁.radius := by
      nlinarith [hμr]
    rw [← h3]
    ring
  have hd1 : dist ω₁.center ω₂.center = ‖ω₂.center -ᵥ ω₁.center‖ := by
    rw [dist_eq_norm_vsub, ← norm_neg, neg_vsub_eq_vsub_rev]
  have hd2 : dist t₁ t₂ = ‖t₂ -ᵥ t₁‖ := by
    rw [dist_eq_norm_vsub, ← norm_neg, neg_vsub_eq_vsub_rev]
  rw [hd1, hd2]
  have hrr : (ω₂.radius - ω₁.radius) ^ 2 = (ω₁.radius - ω₂.radius) ^ 2 := by ring
  linarith [hnorm, hnorm₂, hrr]

omit [Fact (Module.finrank ℝ V = 2)] in
/-- The radius vector from a touchpoint to the center is orthogonal to the tangent
subspace. -/
lemma center_vsub_mem_direction_orthogonal {s : Sphere P} {as : AffineSubspace ℝ P} {t : P}
    (h : s.IsTangentAt t as) : s.center -ᵥ t ∈ as.directionᗮ := by
  rw [Submodule.mem_orthogonal]
  intro v hv
  have hle : as.direction ≤ (s.orthRadius t).direction := direction_le h.le_orthRadius
  rw [Sphere.direction_orthRadius] at hle
  have hv2 : ⟪v, t -ᵥ s.center⟫ =
      0 := Submodule.inner_left_of_mem_orthogonal (Submodule.mem_span_singleton_self _) (hle hv)
  rw [← neg_vsub_eq_vsub_rev, inner_neg_right, hv2, neg_zero]

/-- In a 1-dimensional direction-orthogonal, any two elements are parallel. -/
lemma exists_smul_of_finrank_direction_eq_one {as : AffineSubspace ℝ P} {u v : V}
    (hfr : Module.finrank ℝ as.direction = 1) (hu : u ∈ as.directionᗮ) (hu0 : u ≠ 0)
    (hv : v ∈ as.directionᗮ) : ∃ μ : ℝ, μ • u = v := by
  have hfr' : Module.finrank ℝ as.directionᗮ = 1 := by
    have h := Submodule.finrank_add_finrank_orthogonal as.direction
    rw [hfr, (Fact.out : Module.finrank ℝ V = 2)] at h
    omega
  have hspan : as.directionᗮ = ℝ ∙ u :=
    (Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).2 hu)
      (by rw [finrank_span_singleton hu0, hfr'])).symm
  exact Submodule.mem_span_singleton.1 (hspan ▸ hv)

omit [Fact (Module.finrank ℝ V = 2)] in
/-- The direction of the line through two distinct points is 1-dimensional. -/
lemma finrank_direction_line {a b : P} (hab : a ≠ b) :
    Module.finrank ℝ line[ℝ, a, b].direction = 1 := by
  rw [direction_affineSpan, vectorSpan_pair]
  exact finrank_span_singleton (vsub_ne_zero.mpr hab)

omit [Fact (Module.finrank ℝ V = 2)] in
/-- Distance between two points on a line, in terms of their line-map parameters. -/
lemma dist_lineMap_lineMap {a b : P} (s t : ℝ) :
    dist (AffineMap.lineMap a b s) (AffineMap.lineMap a b t) = |s - t| * dist a b := by
  rw [dist_eq_norm_vsub, dist_eq_norm_vsub]
  have h : AffineMap.lineMap a b s -ᵥ AffineMap.lineMap a b t = (s - t) • (b -ᵥ a) := by
    rw [AffineMap.lineMap_apply, AffineMap.lineMap_apply]
    rw [vadd_vsub_vadd_cancel_right, sub_smul]
  rw [h, norm_smul, Real.norm_eq_abs, ← norm_neg (a -ᵥ b), neg_vsub_eq_vsub_rev]

snip end

set_option maxHeartbeats 800000 in
/-- **USA Mathematical Olympiad 1991, Problem 5.**

The two spheres `ω₁` and `ω₂` are the incircles of `ABX` and `AXC` respectively
(a sphere tangent to the three side lines at interior points of the sides), and `ℓ`
is the common tangent of the two incircles other than `BC`, meeting the segments
`AB` and `AC` at `D` and `E` and meeting `AX` at `Y`. Then
`AY = (AB + AC - BC) / 2`; in particular `AY` does not depend on `X`, so the locus
of `Y` is an arc of the circle centered at `A` with radius `(AB + AC - BC) / 2`. -/
problem usa1991_p5
    (A B C X Y : P)
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hX : Sbtw ℝ B X C)
    (ω₁ ω₂ : Sphere P)
    (K U P₁ L V₂ Q : P)
    (hK : Sbtw ℝ A K B) (hU : Sbtw ℝ B U X) (hP : Sbtw ℝ A P₁ X)
    (hL : Sbtw ℝ A L C) (hV : Sbtw ℝ X V₂ C) (hQ : Sbtw ℝ A Q X)
    (hω₁K : ω₁.IsTangentAt K (line[ℝ, A, B]))
    (hω₁U : ω₁.IsTangentAt U (line[ℝ, B, X]))
    (hω₁P : ω₁.IsTangentAt P₁ (line[ℝ, A, X]))
    (hω₂L : ω₂.IsTangentAt L (line[ℝ, A, C]))
    (hω₂V : ω₂.IsTangentAt V₂ (line[ℝ, X, C]))
    (hω₂Q : ω₂.IsTangentAt Q (line[ℝ, A, X]))
    (ℓ : AffineSubspace ℝ P)
    (D E R S : P)
    (hD : Sbtw ℝ A D B) (hE : Sbtw ℝ A E C)
    (hDℓ : D ∈ ℓ) (hEℓ : E ∈ ℓ) (hYℓ : Y ∈ ℓ)
    (hYAX : Y ∈ line[ℝ, A, X])
    (hω₁R : ω₁.IsTangentAt R ℓ)
    (hω₂S : ω₂.IsTangentAt S ℓ) :
    dist A Y = (dist A B + dist A C - dist B C) / 2 := by
  -- (0) Basic nondegeneracy of the triangle and of `X`.
  have hABC' : ¬ Collinear ℝ ({A, B, C} : Set P) :=
    affineIndependent_iff_not_collinear_set.1 hABC
  have hAB : A ≠ B := by
    have h := hABC.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
    simpa using h
  have hBC : B ≠ C := by
    have h := hABC.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
    simpa using h
  have hBX : B ≠ X := hX.left_ne
  have hXC : X ≠ C := hX.ne_right
  have hXseg : X ∈ line[ℝ, B, C] := affineSegment_subset_affineSpan ℝ B C hX.wbtw
  have hlineBX : line[ℝ, B, X] = line[ℝ, B, C] := line_eq_line_of_wbtw hX.wbtw hBX hXC
  have hlineXC : line[ℝ, X, C] = line[ℝ, B, C] := by
    have h1 : line[ℝ, X, C] = line[ℝ, C, X] := by rw [Set.pair_comm X C]
    have h2 : line[ℝ, C, X] = line[ℝ, C, B] :=
      line_eq_line_of_wbtw hX.wbtw.symm hXC.symm hBX.symm
    rw [h1, h2, Set.pair_comm C B]
  have hAnBC : A ∉ line[ℝ, B, C] := fun h => hABC' (collinear_insert_of_mem_affineSpan_pair h)
  have hAXne : A ≠ X := by
    rintro rfl
    exact hAnBC hXseg
  have hBnAX : B ∉ line[ℝ, A, X] := by
    intro h
    have hc : Collinear ℝ ({B, A, X} : Set P) := collinear_insert_of_mem_affineSpan_pair h
    have hA : A ∈ line[ℝ, B, X] := hc.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hBX
    exact hAnBC (hlineBX ▸ hA)
  have hCnAX : C ∉ line[ℝ, A, X] := by
    intro h
    have hc : Collinear ℝ ({C, A, X} : Set P) := collinear_insert_of_mem_affineSpan_pair h
    have hA : A ∈ line[ℝ, C, X] := hc.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hXC.symm
    have hA2 : A ∈ line[ℝ, B, C] := by
      have hx : line[ℝ, C, X] = line[ℝ, B, C] := by
        have h1 : line[ℝ, C, X] = line[ℝ, C, B] :=
          line_eq_line_of_wbtw hX.wbtw.symm hXC.symm hBX.symm
        rw [h1, Set.pair_comm C B]
      exact hx ▸ hA
    exact hAnBC hA2
  -- (1) The incircles have positive radius.
  have hKneU : K ≠ U := by
    intro hKU
    have hKAB : K ∈ line[ℝ, A, B] := hω₁K.mem_space
    have hKBX : K ∈ line[ℝ, B, X] := by rw [hKU]; exact hω₁U.mem_space
    have hKnB : K ≠ B := hK.right_ne.symm
    have hcoll : Collinear ℝ ({K, A, B} : Set P) := collinear_insert_of_mem_affineSpan_pair hKAB
    have hAKB : A ∈ line[ℝ, K, B] :=
      hcoll.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hKnB
    have hle : line[ℝ, K, B] ≤ line[ℝ, B, X] := by
      rw [affineSpan_le]
      rintro x (rfl | rfl)
      · exact hKBX
      · exact left_mem_affineSpan_pair _ _ _
    exact hAnBC (hlineBX ▸ hle hAKB)
  have hr₁ : ω₁.radius ≠ 0 := by
    intro hr
    have hKI : K = ω₁.center := by
      have hd : dist K ω₁.center = ω₁.radius := mem_sphere.1 hω₁K.mem_sphere
      rw [hr, dist_eq_zero] at hd
      exact hd
    have hUI : U = ω₁.center := by
      have hd : dist U ω₁.center = ω₁.radius := mem_sphere.1 hω₁U.mem_sphere
      rw [hr, dist_eq_zero] at hd
      exact hd
    exact hKneU (hKI.trans hUI.symm)
  have hLneV' : L ≠ V₂ := by
    intro h
    have hLBC : L ∈ line[ℝ, B, C] := by
      have hLXC : L ∈ line[ℝ, X, C] := by rw [h]; exact hω₂V.mem_space
      exact hlineXC ▸ hLXC
    have hALC : A ∈ line[ℝ, L, C] := by
      have hcoll : Collinear ℝ ({L, A, C} : Set P) :=
        collinear_insert_of_mem_affineSpan_pair hω₂L.mem_space
      exact hcoll.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hL.right_ne.symm
    have hBLC : B ∈ line[ℝ, L, C] := by
      have hcoll : Collinear ℝ ({L, B, C} : Set P) := collinear_insert_of_mem_affineSpan_pair hLBC
      exact hcoll.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hL.right_ne.symm
    have hcoll : Collinear ℝ ({A, B, L, C} : Set P) :=
      collinear_insert_insert_of_mem_affineSpan_pair hALC hBLC
    have hsub : ({A, B, C} : Set P) ⊆ {A, B, L, C} := by
      intro x' hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      tauto
    exact hABC' (hcoll.subset hsub)
  have hr₂ : ω₂.radius ≠ 0 := by
    intro hr
    have hLI : L = ω₂.center := by
      have hd : dist L ω₂.center = ω₂.radius := mem_sphere.1 hω₂L.mem_sphere
      rw [hr, dist_eq_zero] at hd
      exact hd
    have hVI : V₂ = ω₂.center := by
      have hd : dist V₂ ω₂.center = ω₂.radius := mem_sphere.1 hω₂V.mem_sphere
      rw [hr, dist_eq_zero] at hd
      exact hd
    exact hLneV' (hLI.trans hVI.symm)
  -- (2) Nondegeneracy of `ℓ`.
  have hDnE : D ≠ E := by
    intro h
    have hDAB : D ∈ line[ℝ, A, B] := affineSegment_subset_affineSpan ℝ A B hD.wbtw
    have hEAC : E ∈ line[ℝ, A, C] := affineSegment_subset_affineSpan ℝ A C hE.wbtw
    have hEAB : E ∈ line[ℝ, A, B] := by rw [← h]; exact hDAB
    have hDnA : D ≠ A := hD.left_ne.symm
    have hEnA : E ≠ A := by rw [← h]; exact hDnA
    have hBEA : B ∈ line[ℝ, E, A] := by
      have hcoll : Collinear ℝ ({E, A, B} : Set P) := collinear_insert_of_mem_affineSpan_pair hEAB
      exact hcoll.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hEnA
    have hCEA : C ∈ line[ℝ, E, A] := by
      have hcoll : Collinear ℝ ({E, A, C} : Set P) := collinear_insert_of_mem_affineSpan_pair hEAC
      exact hcoll.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hEnA
    have hcoll : Collinear ℝ ({B, C, E, A} : Set P) :=
      collinear_insert_insert_of_mem_affineSpan_pair hBEA hCEA
    have hsub : ({A, B, C} : Set P) ⊆ {B, C, E, A} := by
      intro x' hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      tauto
    exact hABC' (hcoll.subset hsub)
  have hRneI₁ : R ≠ ω₁.center := by
    intro h
    have hd : dist R ω₁.center = ω₁.radius := mem_sphere.1 hω₁R.mem_sphere
    rw [h, dist_self] at hd
    exact hr₁ hd.symm
  have hfrℓ : Module.finrank ℝ ℓ.direction = 1 := by
    have hle : ℓ.direction ≤ (ℝ ∙ (R -ᵥ ω₁.center))ᗮ := by
      have h1 : ℓ.direction ≤ (ω₁.orthRadius R).direction := direction_le hω₁R.le_orthRadius
      rwa [Sphere.direction_orthRadius] at h1
    have hDnE' : D -ᵥ E ≠ 0 := vsub_ne_zero.mpr hDnE
    have hss : ℝ ∙ (D -ᵥ E) ≤ ℓ.direction :=
      (Submodule.span_singleton_le_iff_mem _ _).2 (vsub_mem_direction hDℓ hEℓ)
    have h1 : Module.finrank ℝ (ℝ ∙ (D -ᵥ E)) = 1 := finrank_span_singleton hDnE'
    have h2 : (1:ℕ) ≤ Module.finrank ℝ ℓ.direction := h1 ▸ Submodule.finrank_mono hss
    have h3 : Module.finrank ℝ (ℝ ∙ (R -ᵥ ω₁.center))ᗮ = 1 := by
      have h4 := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ (R -ᵥ ω₁.center))
      rw [finrank_span_singleton (vsub_ne_zero.mpr hRneI₁),
        (Fact.out : Module.finrank ℝ V = 2)] at h4
      omega
    have h4 : Module.finrank ℝ ℓ.direction ≤ 1 := h3 ▸ Submodule.finrank_mono hle
    omega
  have hAnℓ : A ∉ ℓ := by
    intro hAℓ
    have hDAB : D ∈ line[ℝ, A, B] := affineSegment_subset_affineSpan ℝ A B hD.wbtw
    have hDnA : D ≠ A := hD.left_ne.symm
    have hB : B ∈ line[ℝ, A, D] := by
      have hcoll : Collinear ℝ ({D, A, B} : Set P) := collinear_insert_of_mem_affineSpan_pair hDAB
      exact hcoll.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hDnA.symm
    have hEAC : E ∈ line[ℝ, A, C] := affineSegment_subset_affineSpan ℝ A C hE.wbtw
    have hEnA : E ≠ A := hE.left_ne.symm
    have hC : C ∈ line[ℝ, A, E] := by
      have hcoll : Collinear ℝ ({E, A, C} : Set P) := collinear_insert_of_mem_affineSpan_pair hEAC
      exact hcoll.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hEnA.symm
    have hleAD : line[ℝ, A, D] ≤ ℓ := by
      rw [affineSpan_le]
      rintro x' (rfl | rfl)
      · exact hAℓ
      · exact hDℓ
    have hlineAD : line[ℝ, A, D] = ℓ := by
      have hdir : line[ℝ, A, D].direction = ℓ.direction :=
        Submodule.eq_of_le_of_finrank_eq (direction_le hleAD)
          (by rw [finrank_direction_line hDnA.symm, hfrℓ])
      exact eq_of_direction_eq_of_nonempty_of_le hdir ⟨A, left_mem_affineSpan_pair ℝ _ _⟩ hleAD
    have hE' : E ∈ line[ℝ, A, D] := by rw [hlineAD]; exact hEℓ
    have hCAD : C ∈ line[ℝ, A, D] := by
      have hle : line[ℝ, A, E] ≤ line[ℝ, A, D] := by
        rw [affineSpan_le]
        rintro x' (rfl | rfl)
        · exact left_mem_affineSpan_pair _ _ _
        · exact hE'
      exact hle hC
    have hcoll : Collinear ℝ ({B, C, A, D} : Set P) :=
      collinear_insert_insert_of_mem_affineSpan_pair hB hCAD
    have hsub : ({A, B, C} : Set P) ⊆ {B, C, A, D} := by
      intro x' hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      tauto
    exact hABC' (hcoll.subset hsub)
  -- (3) The tangent lines are the full tangent hyperplanes.
  have hℓeq : ℓ = ω₁.orthRadius R :=
    hω₁R.eq_orthRadius_of_finrank_add_one_eq hr₁ (by rw [hfrℓ, (Fact.out : Module.finrank ℝ V = 2)])
  have hℓeq₂ : ℓ = ω₂.orthRadius S :=
    hω₂S.eq_orthRadius_of_finrank_add_one_eq hr₂ (by rw [hfrℓ, (Fact.out : Module.finrank ℝ V = 2)])
  have hmemℓ : ∀ x' : P, x' ∈ ℓ ↔ ⟪x' -ᵥ R, R -ᵥ ω₁.center⟫ = 0 := by
    intro x'
    rw [hℓeq]
    exact Sphere.mem_orthRadius_iff_inner_left
  have hAXeq : line[ℝ, A, X] = ω₁.orthRadius P₁ := tangent_line_eq_orthRadius hω₁P hr₁ hAXne
  have hAXeq₂ : line[ℝ, A, X] = ω₂.orthRadius Q := tangent_line_eq_orthRadius hω₂Q hr₂ hAXne
  have hmemAX : ∀ x' : P, x' ∈ line[ℝ, A, X] ↔ ⟪x' -ᵥ P₁, P₁ -ᵥ ω₁.center⟫ = 0 := by
    intro x'
    rw [hAXeq]
    exact Sphere.mem_orthRadius_iff_inner_left
  have hBXeq : line[ℝ, B, X] = ω₁.orthRadius U := tangent_line_eq_orthRadius hω₁U hr₁ hBX
  -- (4) The relevant touchpoints are distinct.
  have hPneR : P₁ ≠ R := by
    intro h
    have h2 : line[ℝ, A, X] = ℓ := by rw [hAXeq, h, ← hℓeq]
    exact hAnℓ (h2 ▸ left_mem_affineSpan_pair ℝ A X)
  have hUneR : U ≠ R := by
    intro h
    have h2 : line[ℝ, B, X] = ℓ := by rw [hBXeq, h, ← hℓeq]
    have hBℓ : B ∈ ℓ := h2 ▸ left_mem_affineSpan_pair ℝ B X
    have hADB : A ∈ line[ℝ, B, D] := by
      have hDAB : D ∈ line[ℝ, A, B] := affineSegment_subset_affineSpan ℝ A B hD.wbtw
      have hcoll : Collinear ℝ ({D, A, B} : Set P) := collinear_insert_of_mem_affineSpan_pair hDAB
      exact hcoll.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hD.right_ne
    have hle : line[ℝ, B, D] ≤ ℓ := by
      rw [affineSpan_le]
      rintro x' (rfl | rfl)
      · exact hBℓ
      · exact hDℓ
    exact hAnℓ (hle hADB)
  have hQneS : Q ≠ S := by
    intro h
    have h2 : line[ℝ, A, X] = ℓ := by rw [hAXeq₂, h, ← hℓeq₂]
    exact hAnℓ (h2 ▸ left_mem_affineSpan_pair ℝ A X)
  have hVneS : V₂ ≠ S := by
    intro h
    have hVXeq : line[ℝ, X, C] = ω₂.orthRadius V₂ := tangent_line_eq_orthRadius hω₂V hr₂ hXC
    have h2 : line[ℝ, X, C] = ℓ := by rw [hVXeq, h, ← hℓeq₂]
    have hCℓ : C ∈ ℓ := h2 ▸ right_mem_affineSpan_pair ℝ X C
    have hAEC : A ∈ line[ℝ, C, E] := by
      have hEAC : E ∈ line[ℝ, A, C] := affineSegment_subset_affineSpan ℝ A C hE.wbtw
      have hcoll : Collinear ℝ ({E, A, C} : Set P) := collinear_insert_of_mem_affineSpan_pair hEAC
      exact hcoll.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hE.right_ne
    have hle : line[ℝ, C, E] ≤ ℓ := by
      rw [affineSpan_le]
      rintro x' (rfl | rfl)
      · exact hCℓ
      · exact hEℓ
    exact hAnℓ (hle hAEC)
  have hABX : ¬ Collinear ℝ ({A, B, X} : Set P) := by
    intro h3
    have hA : A ∈ line[ℝ, B, X] := h3.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hBX
    exact hAnBC (hlineBX ▸ hA)
  have hAXC : ¬ Collinear ℝ ({A, X, C} : Set P) := by
    intro h3
    have hA : A ∈ line[ℝ, X, C] := h3.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hXC
    exact hAnBC (hlineXC ▸ hA)
  have hUneP : U ≠ P₁ := by
    intro h
    have hUAX : U ∈ line[ℝ, A, X] := by rw [h]; exact hω₁P.mem_space
    have hAUX : A ∈ line[ℝ, U, X] := by
      have hcoll : Collinear ℝ ({U, A, X} : Set P) := collinear_insert_of_mem_affineSpan_pair hUAX
      exact hcoll.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hU.ne_right
    have hBUX : B ∈ line[ℝ, U, X] := by
      have hcoll : Collinear ℝ ({U, B, X} : Set P) :=
        collinear_insert_of_mem_affineSpan_pair hω₁U.mem_space
      exact hcoll.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hU.ne_right
    have hcoll : Collinear ℝ ({A, B, U, X} : Set P) :=
      collinear_insert_insert_of_mem_affineSpan_pair hAUX hBUX
    have hsub : ({A, B, X} : Set P) ⊆ {A, B, U, X} := by
      intro x' hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      tauto
    exact hABX (hcoll.subset hsub)
  have hVneQ : V₂ ≠ Q := by
    intro h
    have hVAX : V₂ ∈ line[ℝ, A, X] := by rw [h]; exact hω₂Q.mem_space
    have hAVX : A ∈ line[ℝ, V₂, X] := by
      have hcoll : Collinear ℝ ({V₂, A, X} : Set P) := collinear_insert_of_mem_affineSpan_pair hVAX
      exact hcoll.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hV.left_ne.symm
    have hCVX : C ∈ line[ℝ, V₂, X] := by
      have hcoll : Collinear ℝ ({V₂, X, C} : Set P) :=
        collinear_insert_of_mem_affineSpan_pair hω₂V.mem_space
      exact hcoll.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hV.left_ne.symm
    have hcoll : Collinear ℝ ({A, C, V₂, X} : Set P) :=
      collinear_insert_insert_of_mem_affineSpan_pair hAVX hCVX
    have hsub : ({A, X, C} : Set P) ⊆ {A, C, V₂, X} := by
      intro x' hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      tauto
    exact hAXC (hcoll.subset hsub)
  -- (5) Distance splits along the sides, recorded before the parameters are introduced.
  have d1 : dist A K + dist B K = dist A B := by
    have h := hK.wbtw.dist_add_dist
    rwa [dist_comm K B] at h
  have d2 : dist B U + dist X U = dist B X := by
    have h := hU.wbtw.dist_add_dist
    rwa [dist_comm U X] at h
  have d3 : dist A P₁ + dist X P₁ = dist A X := by
    have h := hP.wbtw.dist_add_dist
    rwa [dist_comm P₁ X] at h
  have d4 : dist A L + dist C L = dist A C := by
    have h := hL.wbtw.dist_add_dist
    rwa [dist_comm L C] at h
  have d5 : dist X V₂ + dist C V₂ = dist X C := by
    have h := hV.wbtw.dist_add_dist
    rwa [dist_comm V₂ C] at h
  have d6 : dist A Q + dist X Q = dist A X := by
    have h := hQ.wbtw.dist_add_dist
    rwa [dist_comm Q X] at h
  have d7 : dist B X + dist X C = dist B C := hX.wbtw.dist_add_dist
  -- (6) Introduce line-map parameters for the interior points.
  obtain ⟨d, hd, rfl⟩ := lineMap_of_sbtw hD
  obtain ⟨e, he, rfl⟩ := lineMap_of_sbtw hE
  obtain ⟨x, hx, rfl⟩ := lineMap_of_sbtw hX
  obtain ⟨u, hu, rfl⟩ := lineMap_of_sbtw hU
  obtain ⟨v, hv, rfl⟩ := lineMap_of_sbtw hV
  obtain ⟨k, hk, rfl⟩ := lineMap_of_sbtw hK
  obtain ⟨l, hl, rfl⟩ := lineMap_of_sbtw hL
  have hd0' : (0:ℝ) < d := hd.1
  have hd1' : d < 1 := hd.2
  have he0' : (0:ℝ) < e := he.1
  have he1' : e < 1 := he.2
  have hx0' : (0:ℝ) < x := hx.1
  have hx1' : x < 1 := hx.2
  have hu0' : (0:ℝ) < u := hu.1
  have hu1' : u < 1 := hu.2
  have hv0' : (0:ℝ) < v := hv.1
  have hv1' : v < 1 := hv.2
  have hk0' : (0:ℝ) < k := hk.1
  have hk1' : k < 1 := hk.2
  have hl0' : (0:ℝ) < l := hl.1
  have hl1' : l < 1 := hl.2
  -- (7) Signs with respect to `ℓ` (functional based at `R`).
  have hgD0 : (1 - d) * ⟪A -ᵥ R, R -ᵥ ω₁.center⟫ + d * ⟪B -ᵥ R, R -ᵥ ω₁.center⟫ = 0 := by
    have h1 : ⟪AffineMap.lineMap A B d -ᵥ R, R -ᵥ ω₁.center⟫ = 0 := (hmemℓ _).1 hDℓ
    rwa [inner_lineMap_vsub] at h1
  have hgE0 : (1 - e) * ⟪A -ᵥ R, R -ᵥ ω₁.center⟫ + e * ⟪C -ᵥ R, R -ᵥ ω₁.center⟫ = 0 := by
    have h1 : ⟪AffineMap.lineMap A C e -ᵥ R, R -ᵥ ω₁.center⟫ = 0 := (hmemℓ _).1 hEℓ
    rwa [inner_lineMap_vsub] at h1
  have hgX : ⟪AffineMap.lineMap B C x -ᵥ R, R -ᵥ ω₁.center⟫ =
      (1 - x) * ⟪B -ᵥ R, R -ᵥ ω₁.center⟫ + x * ⟪C -ᵥ R, R -ᵥ ω₁.center⟫ :=
    inner_lineMap_vsub _ _ _
  have hgU : ⟪AffineMap.lineMap B (AffineMap.lineMap B C x) u -ᵥ R, R -ᵥ ω₁.center⟫ =
      (1 - u) * ⟪B -ᵥ R, R -ᵥ ω₁.center⟫ +
        u * ⟪AffineMap.lineMap B C x -ᵥ R, R -ᵥ ω₁.center⟫ :=
    inner_lineMap_vsub _ _ _
  have hgV : ⟪AffineMap.lineMap (AffineMap.lineMap B C x) C v -ᵥ R, R -ᵥ ω₁.center⟫ =
      (1 - v) * ⟪AffineMap.lineMap B C x -ᵥ R, R -ᵥ ω₁.center⟫ +
        v * ⟪C -ᵥ R, R -ᵥ ω₁.center⟫ :=
    inner_lineMap_vsub _ _ _
  have hgUneg : ⟪AffineMap.lineMap B (AffineMap.lineMap B C x) u -ᵥ R, R -ᵥ ω₁.center⟫ < 0 :=
    inner_vsub_neg_of_mem_sphere hω₁R.mem_sphere hω₁U.mem_sphere hUneR
  have hgBeq : ⟪B -ᵥ R, R -ᵥ ω₁.center⟫ = (-(1 - d) * ⟪A -ᵥ R, R -ᵥ ω₁.center⟫) / d := by
    have hd' : d ≠ 0 := ne_of_gt hd0'
    have h1 : d * ⟪B -ᵥ R, R -ᵥ ω₁.center⟫ = -(1 - d) * ⟪A -ᵥ R, R -ᵥ ω₁.center⟫ := by
      linarith only [hgD0]
    rw [eq_div_iff hd']
    linarith only [h1]
  have hgCeq : ⟪C -ᵥ R, R -ᵥ ω₁.center⟫ = (-(1 - e) * ⟪A -ᵥ R, R -ᵥ ω₁.center⟫) / e := by
    have he' : e ≠ 0 := ne_of_gt he0'
    have h1 : e * ⟪C -ᵥ R, R -ᵥ ω₁.center⟫ = -(1 - e) * ⟪A -ᵥ R, R -ᵥ ω₁.center⟫ := by
      linarith only [hgE0]
    rw [eq_div_iff he']
    linarith only [h1]
  have hgUexp : ⟪AffineMap.lineMap B (AffineMap.lineMap B C x) u -ᵥ R, R -ᵥ ω₁.center⟫ =
      ((1 - u) + u * (1 - x)) * ⟪B -ᵥ R, R -ᵥ ω₁.center⟫ +
        (u * x) * ⟪C -ᵥ R, R -ᵥ ω₁.center⟫ := by
    rw [hgU, hgX]
    ring
  have hgApos : 0 < ⟪A -ᵥ R, R -ᵥ ω₁.center⟫ := by
    have hgAne : ⟪A -ᵥ R, R -ᵥ ω₁.center⟫ ≠ 0 := by
      intro h
      exact hAnℓ ((hmemℓ _).2 h)
    rw [hgUexp, hgBeq, hgCeq] at hgUneg
    have hfact : ((1 - u) + u * (1 - x)) * ((-(1 - d) * ⟪A -ᵥ R, R -ᵥ ω₁.center⟫) / d) +
        (u * x) * ((-(1 - e) * ⟪A -ᵥ R, R -ᵥ ω₁.center⟫) / e) =
        -((((1 - u) + u * (1 - x)) * ((1 - d) / d) + (u * x) * ((1 - e) / e)) *
          ⟪A -ᵥ R, R -ᵥ ω₁.center⟫) := by
      ring
    rw [hfact] at hgUneg
    have hM : (0:ℝ) < ((1 - u) + u * (1 - x)) * ((1 - d) / d) + (u * x) * ((1 - e) / e) := by
      have h1 : (0:ℝ) < 1 - d := sub_pos.mpr hd1'
      have h2 : (0:ℝ) < 1 - e := sub_pos.mpr he1'
      have h3 : (0:ℝ) < 1 - u := sub_pos.mpr hu1'
      have h4 : (0:ℝ) < 1 - x := sub_pos.mpr hx1'
      positivity
    have hM' : (0:ℝ) < (((1 - u) + u * (1 - x)) * ((1 - d) / d) + (u * x) * ((1 - e) / e)) *
        ⟪A -ᵥ R, R -ᵥ ω₁.center⟫ := by linarith only [hgUneg]
    exact pos_of_mul_pos_right hM' hM.le
  have hgBneg : ⟪B -ᵥ R, R -ᵥ ω₁.center⟫ < 0 := by
    rw [hgBeq]
    have h1 : (0:ℝ) < (1 - d) * ⟪A -ᵥ R, R -ᵥ ω₁.center⟫ / d := by
      have h2 : (0:ℝ) < 1 - d := sub_pos.mpr hd1'
      positivity
    have h3 : (-(1 - d) * ⟪A -ᵥ R, R -ᵥ ω₁.center⟫) / d =
        -((1 - d) * ⟪A -ᵥ R, R -ᵥ ω₁.center⟫ / d) := by ring
    rw [h3]
    linarith only [h1]
  have hgCneg : ⟪C -ᵥ R, R -ᵥ ω₁.center⟫ < 0 := by
    rw [hgCeq]
    have h1 : (0:ℝ) < (1 - e) * ⟪A -ᵥ R, R -ᵥ ω₁.center⟫ / e := by
      have h2 : (0:ℝ) < 1 - e := sub_pos.mpr he1'
      positivity
    have h3 : (-(1 - e) * ⟪A -ᵥ R, R -ᵥ ω₁.center⟫) / e =
        -((1 - e) * ⟪A -ᵥ R, R -ᵥ ω₁.center⟫ / e) := by ring
    rw [h3]
    linarith only [h1]
  have hgXneg : ⟪AffineMap.lineMap B C x -ᵥ R, R -ᵥ ω₁.center⟫ < 0 := by
    rw [hgX, hgBeq, hgCeq]
    have hfact : (1 - x) * ((-(1 - d) * ⟪A -ᵥ R, R -ᵥ ω₁.center⟫) / d) +
        x * ((-(1 - e) * ⟪A -ᵥ R, R -ᵥ ω₁.center⟫) / e) =
        -(((1 - x) * ((1 - d) / d) + x * ((1 - e) / e)) * ⟪A -ᵥ R, R -ᵥ ω₁.center⟫) := by
      ring
    rw [hfact]
    have hM : (0:ℝ) < ((1 - x) * ((1 - d) / d) + x * ((1 - e) / e)) * ⟪A -ᵥ R, R -ᵥ ω₁.center⟫ := by
      have h1 : (0:ℝ) < 1 - d := sub_pos.mpr hd1'
      have h2 : (0:ℝ) < 1 - e := sub_pos.mpr he1'
      have h3 : (0:ℝ) < 1 - x := sub_pos.mpr hx1'
      positivity
    linarith only [hM]
  have hgVneg : ⟪AffineMap.lineMap (AffineMap.lineMap B C x) C v -ᵥ R, R -ᵥ ω₁.center⟫ < 0 := by
    rw [hgV, hgX, hgBeq, hgCeq]
    have hfact : (1 - v) * ((1 - x) * ((-(1 - d) * ⟪A -ᵥ R, R -ᵥ ω₁.center⟫) / d) +
        x * ((-(1 - e) * ⟪A -ᵥ R, R -ᵥ ω₁.center⟫) / e)) +
        v * ((-(1 - e) * ⟪A -ᵥ R, R -ᵥ ω₁.center⟫) / e) =
        -(((1 - v) * ((1 - x) * ((1 - d) / d) + x * ((1 - e) / e)) + v * ((1 - e) / e)) *
          ⟪A -ᵥ R, R -ᵥ ω₁.center⟫) := by
      ring
    rw [hfact]
    have hM : (0:ℝ) < ((1 - v) * ((1 - x) * ((1 - d) / d) + x * ((1 - e) / e)) +
        v * ((1 - e) / e)) * ⟪A -ᵥ R, R -ᵥ ω₁.center⟫ := by
      have h1 : (0:ℝ) < 1 - d := sub_pos.mpr hd1'
      have h2 : (0:ℝ) < 1 - e := sub_pos.mpr he1'
      have h3 : (0:ℝ) < 1 - x := sub_pos.mpr hx1'
      have h4 : (0:ℝ) < 1 - v := sub_pos.mpr hv1'
      positivity
    linarith only [hM]
  have hgPneg : ⟪P₁ -ᵥ R, R -ᵥ ω₁.center⟫ < 0 :=
    inner_vsub_neg_of_mem_sphere hω₁R.mem_sphere hω₁P.mem_sphere hPneR
  -- (8) The two incircle centers are on the same side of `ℓ`; sign of `⟪Q -ᵥ R, ·⟫`.
  have hd₁orth : ω₁.center -ᵥ R ∈ ℓ.directionᗮ := center_vsub_mem_direction_orthogonal hω₁R
  have hd₂orth : ω₂.center -ᵥ S ∈ ℓ.directionᗮ := center_vsub_mem_direction_orthogonal hω₂S
  obtain ⟨σ, hσ⟩ := exists_smul_of_finrank_direction_eq_one hfrℓ hd₁orth
    (vsub_ne_zero.mpr hRneI₁.symm) hd₂orth
  have hSvec : S -ᵥ ω₂.center = σ • (R -ᵥ ω₁.center) := by
    rw [← neg_vsub_eq_vsub_rev, ← hσ, ← smul_neg, neg_vsub_eq_vsub_rev]
  have hRorth : ⟪R -ᵥ S, R -ᵥ ω₁.center⟫ = 0 := by
    have h5 : ⟪S -ᵥ R, R -ᵥ ω₁.center⟫ = 0 := hω₁R.inner_left_eq_zero_of_mem hω₂S.mem_space
    rw [← neg_vsub_eq_vsub_rev, inner_neg_left, h5, neg_zero]
  have hσpos : 0 < σ := by
    have hside : ⟪AffineMap.lineMap (AffineMap.lineMap B C x) C v -ᵥ S, S -ᵥ ω₂.center⟫ < 0 :=
      inner_vsub_neg_of_mem_sphere hω₂S.mem_sphere hω₂V.mem_sphere hVneS
    have hconv : ⟪AffineMap.lineMap (AffineMap.lineMap B C x) C v -ᵥ S, S -ᵥ ω₂.center⟫ =
        σ * ⟪AffineMap.lineMap (AffineMap.lineMap B C x) C v -ᵥ R, R -ᵥ ω₁.center⟫ := by
      rw [hSvec, inner_smul_right]
      congr 1
      have h3 : AffineMap.lineMap (AffineMap.lineMap B C x) C v -ᵥ S =
          (AffineMap.lineMap (AffineMap.lineMap B C x) C v -ᵥ R) + (R -ᵥ S) := by
        rw [vsub_add_vsub_cancel]
      rw [h3, inner_add_left, hRorth, add_zero]
    rw [hconv] at hside
    rcases mul_neg_iff.1 hside with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h1
    · exact absurd h2 (not_lt.mpr hgVneg.le)
  have hgQneg : ⟪Q -ᵥ R, R -ᵥ ω₁.center⟫ < 0 := by
    have hside : ⟪Q -ᵥ S, S -ᵥ ω₂.center⟫ < 0 :=
      inner_vsub_neg_of_mem_sphere hω₂S.mem_sphere hω₂Q.mem_sphere hQneS
    have hconv : ⟪Q -ᵥ S, S -ᵥ ω₂.center⟫ = σ * ⟪Q -ᵥ R, R -ᵥ ω₁.center⟫ := by
      rw [hSvec, inner_smul_right]
      congr 1
      have h3 : Q -ᵥ S = (Q -ᵥ R) + (R -ᵥ S) := by
        rw [vsub_add_vsub_cancel]
      rw [h3, inner_add_left, hRorth, add_zero]
    rw [hconv] at hside
    rcases mul_neg_iff.1 hside with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2
    · exact absurd h1 (not_lt.mpr hσpos.le)
  have hsideℓ : 0 < ⟪ω₂.center -ᵥ S, ω₁.center -ᵥ R⟫ := by
    rw [← hσ, inner_smul_left, conj_trivial]
    have hn : (0:ℝ) < ⟪ω₁.center -ᵥ R, ω₁.center -ᵥ R⟫ := by
      rw [real_inner_self_eq_norm_sq]
      exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (vsub_ne_zero.mpr hRneI₁.symm))
    exact mul_pos hσpos hn
  -- (9) `Y` is strictly between `A` and the touchpoints on `AX`.
  have hYP : Sbtw ℝ A Y P₁ := by
    have hline : line[ℝ, A, P₁] = line[ℝ, A, AffineMap.lineMap B C x] :=
      line_eq_line_of_wbtw hP.wbtw hP.left_ne hP.ne_right
    have hy : Y ∈ line[ℝ, A, P₁] := by rw [hline]; exact hYAX
    exact sbtw_of_inner_of_mem_line hP.left_ne hy ((hmemℓ _).1 hYℓ) hgApos hgPneg
  have hYQ : Sbtw ℝ A Y Q := by
    have hline : line[ℝ, A, Q] = line[ℝ, A, AffineMap.lineMap B C x] :=
      line_eq_line_of_wbtw hQ.wbtw hQ.left_ne hQ.ne_right
    have hy : Y ∈ line[ℝ, A, Q] := by rw [hline]; exact hYAX
    exact sbtw_of_inner_of_mem_line hQ.left_ne hy ((hmemℓ _).1 hYℓ) hgApos hgQneg
  -- (10) Signs with respect to `AX` (functional based at `P₁`).
  have hgAXX0 : ⟪AffineMap.lineMap B C x -ᵥ P₁, P₁ -ᵥ ω₁.center⟫ = 0 :=
    hω₁P.inner_left_eq_zero_of_mem (right_mem_affineSpan_pair ℝ _ _)
  have hgAXU : ⟪AffineMap.lineMap B (AffineMap.lineMap B C x) u -ᵥ P₁, P₁ -ᵥ ω₁.center⟫ =
      (1 - u) * ⟪B -ᵥ P₁, P₁ -ᵥ ω₁.center⟫ +
        u * ⟪AffineMap.lineMap B C x -ᵥ P₁, P₁ -ᵥ ω₁.center⟫ :=
    inner_lineMap_vsub _ _ _
  have hgAXUneg : ⟪AffineMap.lineMap B (AffineMap.lineMap B C x) u -ᵥ P₁, P₁ -ᵥ ω₁.center⟫ < 0 :=
    inner_vsub_neg_of_mem_sphere hω₁P.mem_sphere hω₁U.mem_sphere hUneP
  have hgAXBneg : ⟪B -ᵥ P₁, P₁ -ᵥ ω₁.center⟫ < 0 := by
    rw [hgAXU, hgAXX0, mul_zero, add_zero] at hgAXUneg
    rcases mul_neg_iff.1 hgAXUneg with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2
    · exact absurd h1 (not_lt.mpr (sub_pos.mpr hu1').le)
  have hgAXRneg : ⟪R -ᵥ P₁, P₁ -ᵥ ω₁.center⟫ < 0 :=
    inner_vsub_neg_of_mem_sphere hω₁P.mem_sphere hω₁R.mem_sphere hPneR.symm
  have hgAXX : ⟪AffineMap.lineMap B C x -ᵥ P₁, P₁ -ᵥ ω₁.center⟫ =
      (1 - x) * ⟪B -ᵥ P₁, P₁ -ᵥ ω₁.center⟫ + x * ⟪C -ᵥ P₁, P₁ -ᵥ ω₁.center⟫ :=
    inner_lineMap_vsub _ _ _
  have hgAXCpos : 0 < ⟪C -ᵥ P₁, P₁ -ᵥ ω₁.center⟫ := by
    rw [hgAXX0] at hgAXX
    have h1 : (0:ℝ) < x * ⟪C -ᵥ P₁, P₁ -ᵥ ω₁.center⟫ := by
      have h2 : (1 - x) * ⟪B -ᵥ P₁, P₁ -ᵥ ω₁.center⟫ < 0 :=
        mul_neg_of_pos_of_neg (sub_pos.mpr hx1') hgAXBneg
      linarith only [hgAXX, h2]
    exact pos_of_mul_pos_right h1 hx0'.le
  have hgAXVpos : 0 < ⟪AffineMap.lineMap (AffineMap.lineMap B C x) C v -ᵥ P₁, P₁ -ᵥ ω₁.center⟫ := by
    have h1 : ⟪AffineMap.lineMap (AffineMap.lineMap B C x) C v -ᵥ P₁, P₁ -ᵥ ω₁.center⟫ =
        (1 - v) * ⟪AffineMap.lineMap B C x -ᵥ P₁, P₁ -ᵥ ω₁.center⟫ +
          v * ⟪C -ᵥ P₁, P₁ -ᵥ ω₁.center⟫ :=
      inner_lineMap_vsub _ _ _
    rw [h1, hgAXX0, mul_zero, zero_add]
    exact mul_pos hv0' hgAXCpos
  -- (11) The two incircle centers are on opposite sides of `AX`; sign of `⟪S -ᵥ P₁, ·⟫`.
  have hfrAX : Module.finrank ℝ line[ℝ, A, AffineMap.lineMap B C x].direction = 1 := finrank_direction_line hAXne
  have hd₁orthAX : ω₁.center -ᵥ P₁ ∈ line[ℝ, A, AffineMap.lineMap B C x].directionᗮ :=
    center_vsub_mem_direction_orthogonal hω₁P
  have hd₂orthAX : ω₂.center -ᵥ Q ∈ line[ℝ, A, AffineMap.lineMap B C x].directionᗮ :=
    center_vsub_mem_direction_orthogonal hω₂Q
  have hIneP : ω₁.center -ᵥ P₁ ≠ 0 := by
    rw [ne_eq, vsub_eq_zero_iff_eq]
    intro hcc
    have hd : dist P₁ ω₁.center = ω₁.radius := mem_sphere.1 hω₁P.mem_sphere
    rw [← hcc, dist_self] at hd
    exact hr₁ hd.symm
  obtain ⟨τ, hτ⟩ := exists_smul_of_finrank_direction_eq_one hfrAX hd₁orthAX hIneP hd₂orthAX
  have hQvec : Q -ᵥ ω₂.center = τ • (P₁ -ᵥ ω₁.center) := by
    rw [← neg_vsub_eq_vsub_rev, ← hτ, ← smul_neg, neg_vsub_eq_vsub_rev]
  have hPorth : ⟪P₁ -ᵥ Q, P₁ -ᵥ ω₁.center⟫ = 0 := by
    have h5 : ⟪Q -ᵥ P₁, P₁ -ᵥ ω₁.center⟫ = 0 := hω₁P.inner_left_eq_zero_of_mem hω₂Q.mem_space
    rw [← neg_vsub_eq_vsub_rev, inner_neg_left, h5, neg_zero]
  have hτneg : τ < 0 := by
    have hside : ⟪AffineMap.lineMap (AffineMap.lineMap B C x) C v -ᵥ Q, Q -ᵥ ω₂.center⟫ < 0 :=
      inner_vsub_neg_of_mem_sphere hω₂Q.mem_sphere hω₂V.mem_sphere hVneQ
    have hconv : ⟪AffineMap.lineMap (AffineMap.lineMap B C x) C v -ᵥ Q, Q -ᵥ ω₂.center⟫ =
        τ * ⟪AffineMap.lineMap (AffineMap.lineMap B C x) C v -ᵥ P₁, P₁ -ᵥ ω₁.center⟫ := by
      rw [hQvec, inner_smul_right]
      congr 1
      have h3 : AffineMap.lineMap (AffineMap.lineMap B C x) C v -ᵥ Q =
          (AffineMap.lineMap (AffineMap.lineMap B C x) C v -ᵥ P₁) + (P₁ -ᵥ Q) := by
        rw [vsub_add_vsub_cancel]
      rw [h3, inner_add_left, hPorth, add_zero]
    rw [hconv] at hside
    rcases mul_neg_iff.1 hside with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd h2 (not_lt.mpr hgAXVpos.le)
    · exact h1
  have hgAXSpos : 0 < ⟪S -ᵥ P₁, P₁ -ᵥ ω₁.center⟫ := by
    have hside : ⟪S -ᵥ Q, Q -ᵥ ω₂.center⟫ < 0 :=
      inner_vsub_neg_of_mem_sphere hω₂Q.mem_sphere hω₂S.mem_sphere hQneS.symm
    have hconv : ⟪S -ᵥ Q, Q -ᵥ ω₂.center⟫ = τ * ⟪S -ᵥ P₁, P₁ -ᵥ ω₁.center⟫ := by
      rw [hQvec, inner_smul_right]
      congr 1
      have h3 : S -ᵥ Q = (S -ᵥ P₁) + (P₁ -ᵥ Q) := by
        rw [vsub_add_vsub_cancel]
      rw [h3, inner_add_left, hPorth, add_zero]
    rw [hconv] at hside
    rcases mul_neg_iff.1 hside with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd h1 (not_lt.mpr hτneg.le)
    · exact h2
  -- (12) Distances along `BC` in terms of the parameters.
  have hUeq : AffineMap.lineMap B (AffineMap.lineMap B C x) u = AffineMap.lineMap B C (u * x) := by
    simp only [AffineMap.lineMap_apply]
    rw [vadd_vsub, smul_smul]
  have hVeq : AffineMap.lineMap (AffineMap.lineMap B C x) C v = AffineMap.lineMap B C (x + v * (1 - x)) := by
    simp only [AffineMap.lineMap_apply]
    rw [vsub_vadd_eq_vsub_sub, vadd_vadd]
    have h1 : v • ((C -ᵥ B) - x • (C -ᵥ B)) + x • (C -ᵥ B) = (x + v * (1 - x)) • (C -ᵥ B) := by
      module
    rw [h1]
  have hdistBU : dist B (AffineMap.lineMap B (AffineMap.lineMap B C x) u) = (u * x) * dist B C := by
    rw [hUeq]
    have h1 := dist_lineMap_lineMap (a := B) (b := C) (0:ℝ) (u * x)
    rw [AffineMap.lineMap_apply_zero] at h1
    rw [h1, zero_sub, abs_neg, abs_of_nonneg (by positivity)]
  have hdistCV : dist C (AffineMap.lineMap (AffineMap.lineMap B C x) C v) =
      ((1 - x) * (1 - v)) * dist B C := by
    rw [hVeq]
    have h1 := dist_lineMap_lineMap (a := B) (b := C) (1:ℝ) (x + v * (1 - x))
    rw [AffineMap.lineMap_apply_one] at h1
    have hp : (0:ℝ) ≤ 1 - (x + v * (1 - x)) := by nlinarith only [hx0', hx1', hv0', hv1']
    have h2 : (1:ℝ) - (x + v * (1 - x)) = (1 - x) * (1 - v) := by ring
    rw [h1, abs_of_nonneg hp, h2]
  have hdistUV : dist (AffineMap.lineMap B (AffineMap.lineMap B C x) u)
      (AffineMap.lineMap (AffineMap.lineMap B C x) C v) =
      (x + v * (1 - x) - u * x) * dist B C := by
    rw [hUeq, hVeq]
    have h1 := dist_lineMap_lineMap (a := B) (b := C) (u * x) (x + v * (1 - x))
    have hp : (0:ℝ) ≤ x + v * (1 - x) - u * x := by nlinarith only [hx0', hx1', hu0', hu1', hv0', hv1']
    rw [h1, abs_sub_comm, abs_of_nonneg hp]
  have hUVpos : (0:ℝ) < dist (AffineMap.lineMap B (AffineMap.lineMap B C x) u)
      (AffineMap.lineMap (AffineMap.lineMap B C x) C v) := by
    rw [hdistUV]
    have hp : (0:ℝ) < x + v * (1 - x) - u * x := by nlinarith only [hx0', hx1', hu0', hu1', hv0', hv1']
    exact mul_pos hp (dist_pos.mpr hBC)
  -- (13) The two external tangent segments `RS` and `UV` are equal.
  have hfrBX : Module.finrank ℝ line[ℝ, B, AffineMap.lineMap B C x].direction = 1 :=
    finrank_direction_line hBX
  have hω₂V' : ω₂.IsTangentAt (AffineMap.lineMap (AffineMap.lineMap B C x) C v)
      (line[ℝ, B, AffineMap.lineMap B C x]) := by
    rw [hlineXC, ← hlineBX] at hω₂V
    exact hω₂V
  have hIneU : ω₁.center -ᵥ (AffineMap.lineMap B (AffineMap.lineMap B C x) u) ≠ 0 := by
    rw [ne_eq, vsub_eq_zero_iff_eq]
    intro hcc
    have hd : dist (AffineMap.lineMap B (AffineMap.lineMap B C x) u) ω₁.center = ω₁.radius :=
      mem_sphere.1 hω₁U.mem_sphere
    rw [← hcc, dist_self] at hd
    exact hr₁ hd.symm
  have hsideBC : 0 < ⟪ω₂.center -ᵥ (AffineMap.lineMap (AffineMap.lineMap B C x) C v),
      ω₁.center -ᵥ (AffineMap.lineMap B (AffineMap.lineMap B C x) u)⟫ := by
    obtain ⟨ν, hν⟩ := exists_smul_of_finrank_direction_eq_one hfrBX
      (center_vsub_mem_direction_orthogonal hω₁U) hIneU
      (center_vsub_mem_direction_orthogonal hω₂V')
    have hside : ⟪AffineMap.lineMap A C l -ᵥ (AffineMap.lineMap (AffineMap.lineMap B C x) C v),
        (AffineMap.lineMap (AffineMap.lineMap B C x) C v) -ᵥ ω₂.center⟫ < 0 :=
      inner_vsub_neg_of_mem_sphere hω₂V.mem_sphere hω₂L.mem_sphere hLneV'
    have h1 : (AffineMap.lineMap (AffineMap.lineMap B C x) C v) -ᵥ ω₂.center =
        ν • ((AffineMap.lineMap B (AffineMap.lineMap B C x) u) -ᵥ ω₁.center) := by
      rw [← neg_vsub_eq_vsub_rev, ← hν, ← smul_neg, neg_vsub_eq_vsub_rev]
    have hUorth : ⟪(AffineMap.lineMap B (AffineMap.lineMap B C x) u) -ᵥ
        (AffineMap.lineMap (AffineMap.lineMap B C x) C v),
        (AffineMap.lineMap B (AffineMap.lineMap B C x) u) -ᵥ ω₁.center⟫ = 0 := by
      have h5 : ⟪(AffineMap.lineMap (AffineMap.lineMap B C x) C v) -ᵥ
          (AffineMap.lineMap B (AffineMap.lineMap B C x) u),
          (AffineMap.lineMap B (AffineMap.lineMap B C x) u) -ᵥ ω₁.center⟫ = 0 :=
        hω₁U.inner_left_eq_zero_of_mem hω₂V'.mem_space
      rw [← neg_vsub_eq_vsub_rev, inner_neg_left, h5, neg_zero]
    have hconv : ⟪AffineMap.lineMap A C l -ᵥ (AffineMap.lineMap (AffineMap.lineMap B C x) C v),
        (AffineMap.lineMap (AffineMap.lineMap B C x) C v) -ᵥ ω₂.center⟫ =
        ν * ⟪AffineMap.lineMap A C l -ᵥ (AffineMap.lineMap B (AffineMap.lineMap B C x) u),
          (AffineMap.lineMap B (AffineMap.lineMap B C x) u) -ᵥ ω₁.center⟫ := by
      rw [h1, inner_smul_right]
      congr 1
      have h3 : AffineMap.lineMap A C l -ᵥ (AffineMap.lineMap (AffineMap.lineMap B C x) C v) =
          (AffineMap.lineMap A C l -ᵥ (AffineMap.lineMap B (AffineMap.lineMap B C x) u)) +
            ((AffineMap.lineMap B (AffineMap.lineMap B C x) u) -ᵥ
              (AffineMap.lineMap (AffineMap.lineMap B C x) C v)) := by
        rw [vsub_add_vsub_cancel]
      rw [h3, inner_add_left, hUorth, add_zero]
    have hgA'neg : ⟪A -ᵥ (AffineMap.lineMap B (AffineMap.lineMap B C x) u),
        (AffineMap.lineMap B (AffineMap.lineMap B C x) u) -ᵥ ω₁.center⟫ < 0 := by
      have hK0 : ⟪AffineMap.lineMap A B k -ᵥ (AffineMap.lineMap B (AffineMap.lineMap B C x) u),
          (AffineMap.lineMap B (AffineMap.lineMap B C x) u) -ᵥ ω₁.center⟫ < 0 :=
        inner_vsub_neg_of_mem_sphere hω₁U.mem_sphere hω₁K.mem_sphere hKneU
      have hKexp : ⟪AffineMap.lineMap A B k -ᵥ (AffineMap.lineMap B (AffineMap.lineMap B C x) u),
          (AffineMap.lineMap B (AffineMap.lineMap B C x) u) -ᵥ ω₁.center⟫ =
          (1 - k) * ⟪A -ᵥ (AffineMap.lineMap B (AffineMap.lineMap B C x) u),
            (AffineMap.lineMap B (AffineMap.lineMap B C x) u) -ᵥ ω₁.center⟫ +
            k * ⟪B -ᵥ (AffineMap.lineMap B (AffineMap.lineMap B C x) u),
              (AffineMap.lineMap B (AffineMap.lineMap B C x) u) -ᵥ ω₁.center⟫ :=
        inner_lineMap_vsub _ _ _
      have hB0 : ⟪B -ᵥ (AffineMap.lineMap B (AffineMap.lineMap B C x) u),
          (AffineMap.lineMap B (AffineMap.lineMap B C x) u) -ᵥ ω₁.center⟫ = 0 :=
        hω₁U.inner_left_eq_zero_of_mem (left_mem_affineSpan_pair ℝ _ _)
      rw [hKexp, hB0, mul_zero, add_zero] at hK0
      rcases mul_neg_iff.1 hK0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h2
      · exact absurd h1 (not_lt.mpr (sub_pos.mpr hk1').le)
    have hgL'neg : ⟪AffineMap.lineMap A C l -ᵥ (AffineMap.lineMap B (AffineMap.lineMap B C x) u),
        (AffineMap.lineMap B (AffineMap.lineMap B C x) u) -ᵥ ω₁.center⟫ < 0 := by
      have hLexp : ⟪AffineMap.lineMap A C l -ᵥ (AffineMap.lineMap B (AffineMap.lineMap B C x) u),
          (AffineMap.lineMap B (AffineMap.lineMap B C x) u) -ᵥ ω₁.center⟫ =
          (1 - l) * ⟪A -ᵥ (AffineMap.lineMap B (AffineMap.lineMap B C x) u),
            (AffineMap.lineMap B (AffineMap.lineMap B C x) u) -ᵥ ω₁.center⟫ +
            l * ⟪C -ᵥ (AffineMap.lineMap B (AffineMap.lineMap B C x) u),
              (AffineMap.lineMap B (AffineMap.lineMap B C x) u) -ᵥ ω₁.center⟫ :=
        inner_lineMap_vsub _ _ _
      have hC0 : ⟪C -ᵥ (AffineMap.lineMap B (AffineMap.lineMap B C x) u),
          (AffineMap.lineMap B (AffineMap.lineMap B C x) u) -ᵥ ω₁.center⟫ = 0 := by
        have hCmem : C ∈ line[ℝ, B, AffineMap.lineMap B C x] := by
          rw [hlineBX]
          exact right_mem_affineSpan_pair ℝ _ _
        exact hω₁U.inner_left_eq_zero_of_mem hCmem
      rw [hLexp, hC0, mul_zero, add_zero]
      exact mul_neg_of_pos_of_neg (sub_pos.mpr hl1') hgA'neg
    have hνpos : 0 < ν := by
      rw [hconv] at hside
      rcases mul_neg_iff.1 hside with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h1
      · exact absurd h2 (not_lt.mpr hgL'neg.le)
    rw [← hν, inner_smul_left, conj_trivial]
    have hn : (0:ℝ) < ⟪ω₁.center -ᵥ (AffineMap.lineMap B (AffineMap.lineMap B C x) u),
        ω₁.center -ᵥ (AffineMap.lineMap B (AffineMap.lineMap B C x) u)⟫ := by
      rw [real_inner_self_eq_norm_sq]
      exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hIneU)
    exact mul_pos hνpos hn
  have hL5BC := dist_touchpoint_sq_eq_of_same_side hω₁U hω₂V' hr₁ hfrBX hsideBC
  have hL5ℓ := dist_touchpoint_sq_eq_of_same_side hω₁R hω₂S hr₁ hfrℓ hsideℓ
  have hRSUV : dist R S = dist (AffineMap.lineMap B (AffineMap.lineMap B C x) u)
      (AffineMap.lineMap (AffineMap.lineMap B C x) C v) := by
    have h2 : dist R S ^ 2 = dist (AffineMap.lineMap B (AffineMap.lineMap B C x) u)
        (AffineMap.lineMap (AffineMap.lineMap B C x) C v) ^ 2 := by
      rw [hL5ℓ, hL5BC]
    exact (sq_eq_sq₀ dist_nonneg dist_nonneg).1 h2
  have hRneS : R ≠ S := by
    intro h
    rw [h, dist_self] at hRSUV
    linarith [hUVpos, hRSUV]
  -- (14) `Y` is strictly between `R` and `S`.
  have hlineRS : line[ℝ, R, S] = ℓ := by
    have hle : line[ℝ, R, S] ≤ ℓ := by
      rw [affineSpan_le]
      rintro x' (rfl | rfl)
      · exact hω₁R.mem_space
      · exact hω₂S.mem_space
    have hdir : line[ℝ, R, S].direction = ℓ.direction :=
      Submodule.eq_of_le_of_finrank_eq (direction_le hle)
        (by rw [finrank_direction_line hRneS, hfrℓ])
    exact eq_of_direction_eq_of_nonempty_of_le hdir ⟨R, left_mem_affineSpan_pair ℝ _ _⟩ hle
  have hYRS : Sbtw ℝ R Y S := by
    have hy : Y ∈ line[ℝ, S, R] := by
      rw [Set.pair_comm S R, hlineRS]
      exact hYℓ
    have h0 : ⟪Y -ᵥ P₁, P₁ -ᵥ ω₁.center⟫ = 0 := (hmemAX _).1 hYAX
    have h := sbtw_of_inner_of_mem_line hRneS.symm hy h0 hgAXSpos hgAXRneg
    exact sbtw_comm.1 h
  -- (15) Tangent lengths and the final bookkeeping.
  have e1 : dist A (AffineMap.lineMap A B k) = dist A P₁ :=
    hω₁K.dist_eq_of_mem_of_mem hω₁P (left_mem_affineSpan_pair ℝ _ _) (left_mem_affineSpan_pair ℝ _ _)
  have e2 : dist B (AffineMap.lineMap A B k) = dist B (AffineMap.lineMap B (AffineMap.lineMap B C x) u) :=
    hω₁K.dist_eq_of_mem_of_mem hω₁U (right_mem_affineSpan_pair ℝ _ _) (left_mem_affineSpan_pair ℝ _ _)
  have e3 : dist (AffineMap.lineMap B C x) (AffineMap.lineMap B (AffineMap.lineMap B C x) u) =
      dist (AffineMap.lineMap B C x) P₁ :=
    hω₁U.dist_eq_of_mem_of_mem hω₁P (right_mem_affineSpan_pair ℝ _ _) (right_mem_affineSpan_pair ℝ _ _)
  have e4 : dist A (AffineMap.lineMap A C l) = dist A Q :=
    hω₂L.dist_eq_of_mem_of_mem hω₂Q (left_mem_affineSpan_pair ℝ _ _) (left_mem_affineSpan_pair ℝ _ _)
  have e5 : dist C (AffineMap.lineMap A C l) = dist C (AffineMap.lineMap (AffineMap.lineMap B C x) C v) :=
    hω₂L.dist_eq_of_mem_of_mem hω₂V (right_mem_affineSpan_pair ℝ _ _) (right_mem_affineSpan_pair ℝ _ _)
  have e6 : dist (AffineMap.lineMap B C x) (AffineMap.lineMap (AffineMap.lineMap B C x) C v) =
      dist (AffineMap.lineMap B C x) Q :=
    hω₂V.dist_eq_of_mem_of_mem hω₂Q (left_mem_affineSpan_pair ℝ _ _) (right_mem_affineSpan_pair ℝ _ _)
  have e7 : dist Y P₁ = dist Y R := hω₁P.dist_eq_of_mem_of_mem hω₁R hYAX hYℓ
  have e8 : dist Y Q = dist Y S := hω₂Q.dist_eq_of_mem_of_mem hω₂S hYAX hYℓ
  have d9 : dist A Y + dist Y P₁ = dist A P₁ := hYP.wbtw.dist_add_dist
  have d10 : dist A Y + dist Y Q = dist A Q := hYQ.wbtw.dist_add_dist
  have d11 : dist Y R + dist Y S = dist R S := by
    have h := hYRS.wbtw.dist_add_dist
    rwa [dist_comm R Y] at h
  have hUV : dist (AffineMap.lineMap B (AffineMap.lineMap B C x) u)
      (AffineMap.lineMap (AffineMap.lineMap B C x) C v) =
      dist B C - dist B (AffineMap.lineMap B (AffineMap.lineMap B C x) u) -
        dist C (AffineMap.lineMap (AffineMap.lineMap B C x) C v) := by
    linarith only [hdistBU, hdistCV, hdistUV]
  linarith only [e1, e2, e3, e4, e5, e6, e7, e8, d1, d2, d3, d4, d5, d6, d7, d9, d10, d11, hUV, hRSUV]

end Usa1991P5
