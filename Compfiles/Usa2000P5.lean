/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Geometry.Euclidean.Sphere.Tangent
import Mathlib.Geometry.Euclidean.PerpBisector
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine

import ProblemExtraction

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 2000, Problem 5

Let A₁A₂A₃ be a triangle, and let ω₁ be a circle in its plane
passing through A₁ and A₂. Suppose there exist circles ω₂,ω₃,⋯,ω₇
such that for k=2,3,⋯,7, circle ωₖ is externally tangent to ωₖ₋₁
and passes through Aₖ and Aₖ₊₁ (indices mod 3).

Prove that ω₇ = ω₁.
-/

namespace Usa2000P5

abbrev Circle := EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2))

def ExternallyTangent (c1 c2 : Circle) : Prop :=
  dist c1.center c2.center = c1.radius + c2.radius

snip begin

abbrev Point := EuclideanSpace ℝ (Fin 2)

abbrev leftVertex (A : ZMod 3 → Point) (i : Fin 7) : Point :=
  A (i : ZMod 3)

abbrev rightVertex (A : ZMod 3 → Point) (i : Fin 7) : Point :=
  A ((i : ZMod 3) + 1)

abbrev circleCenter (ω : Fin 7 → Circle) (i : Fin 7) : Point :=
  (ω i).center

noncomputable instance : Module.Oriented ℝ Point (Fin 2) where
  positiveOrientation :=
    (Orientation.map (Fin 2) (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ))).symm
      (Pi.basisFun ℝ (Fin 2)).orientation

instance : Fact (Module.finrank ℝ Point = 2) where
  out := by
    simp [Point]

noncomputable abbrev sideAngle (A : ZMod 3 → Point) (ω : Fin 7 → Circle) (i : Fin 7) :
    Real.Angle :=
  EuclideanGeometry.oangle (rightVertex A i) (leftVertex A i) (circleCenter ω i)

noncomputable abbrev turnAngle (A : ZMod 3 → Point) (i : Fin 7) : Real.Angle :=
  EuclideanGeometry.oangle (leftVertex A i) (rightVertex A i) (rightVertex A (i + 1))

lemma external_tangent_at_shared_point
    {s₁ s₂ : Circle} {p : Point}
    (hp₁ : p ∈ s₁) (hp₂ : p ∈ s₂)
    (h : ExternallyTangent s₁ s₂) :
    s₁.IsExtTangentAt s₂ p := by
  refine ⟨hp₁, hp₂, ?_⟩
  rw [← dist_add_dist_eq_iff]
  rw [EuclideanGeometry.mem_sphere'.mp hp₁, EuclideanGeometry.mem_sphere.mp hp₂]
  exact h.symm

lemma center_mem_perpBisector
    {A : ZMod 3 → Point} {ω : Fin 7 → Circle}
    (hA : ∀ i : Fin 7, (A i ∈ ω i ∧ A (i + 1) ∈ ω i)) (i : Fin 7) :
    circleCenter ω i ∈ AffineSubspace.perpBisector (leftVertex A i) (rightVertex A i) := by
  refine AffineSubspace.mem_perpBisector_iff_dist_eq'.2 ?_
  exact EuclideanGeometry.dist_center_eq_dist_center_of_mem_sphere (hA i).1 (hA i).2

lemma side_oangle_add_eq_zero {p q C : Point}
    (hC : C ∈ AffineSubspace.perpBisector p q) :
    EuclideanGeometry.oangle q p C + EuclideanGeometry.oangle p q C = 0 := by
  have hdist : dist C p = dist C q :=
    AffineSubspace.mem_perpBisector_iff_dist_eq.mp hC
  have hbase : EuclideanGeometry.oangle C p q = EuclideanGeometry.oangle p q C :=
    EuclideanGeometry.oangle_eq_oangle_of_dist_eq hdist
  rw [← hbase]
  exact EuclideanGeometry.oangle_add_oangle_rev q p C

lemma fin_succ_cast_zmod3 (i : Fin 7) (hi : i < 6) :
    ((i : ZMod 3) + 1) = (((i + 1 : Fin 7) : ZMod 3)) := by
  rw [← Nat.cast_one, ← Nat.cast_add, ZMod.natCast_eq_natCast_iff']
  omega

lemma rightVertex_eq_leftVertex_succ
    (A : ZMod 3 → Point) (i : Fin 7) (hi : i < 6) :
    rightVertex A i = leftVertex A (i + 1) := by
  simp [leftVertex, rightVertex, fin_succ_cast_zmod3 i hi]

lemma leftVertex_mem_circle
    {A : ZMod 3 → Point} {ω : Fin 7 → Circle}
    (hA : ∀ i : Fin 7, (A i ∈ ω i ∧ A (i + 1) ∈ ω i)) (i : Fin 7) :
    leftVertex A i ∈ ω i := by
  simpa [leftVertex] using (hA i).1

lemma rightVertex_mem_circle
    {A : ZMod 3 → Point} {ω : Fin 7 → Circle}
    (hA : ∀ i : Fin 7, (A i ∈ ω i ∧ A (i + 1) ∈ ω i)) (i : Fin 7) :
    rightVertex A i ∈ ω i := by
  simpa [rightVertex] using (hA i).2

lemma rightVertex_mem_next_circle
    {A : ZMod 3 → Point} {ω : Fin 7 → Circle}
    (hA : ∀ i : Fin 7, (A i ∈ ω i ∧ A (i + 1) ∈ ω i))
    (i : Fin 7) (hi : i < 6) :
    rightVertex A i ∈ ω (i + 1) := by
  rw [rightVertex_eq_leftVertex_succ A i hi]
  exact leftVertex_mem_circle hA (i + 1)

lemma tangent_at_shared_vertex
    {A : ZMod 3 → Point} {ω : Fin 7 → Circle}
    (hTangent : ∀ i, i < 6 → ExternallyTangent (ω i) (ω (i + 1)))
    (hA : ∀ i : Fin 7, (A i ∈ ω i ∧ A (i + 1) ∈ ω i))
    (i : Fin 7) (hi : i < 6) :
    (ω i).IsExtTangentAt (ω (i + 1)) (rightVertex A i) := by
  exact external_tangent_at_shared_point
    (rightVertex_mem_circle hA i) (rightVertex_mem_next_circle hA i hi) (hTangent i hi)

lemma vertex_ne_01 {A : ZMod 3 → Point}
    (hABC : AffineIndependent ℝ ![A 0, A 1, A 2]) : A 0 ≠ A 1 := by
  simpa using hABC.injective.ne (by decide : (0 : Fin 3) ≠ 1)

lemma vertex_ne_12 {A : ZMod 3 → Point}
    (hABC : AffineIndependent ℝ ![A 0, A 1, A 2]) : A 1 ≠ A 2 := by
  simpa using hABC.injective.ne (by decide : (1 : Fin 3) ≠ 2)

lemma vertex_ne_20 {A : ZMod 3 → Point}
    (hABC : AffineIndependent ℝ ![A 0, A 1, A 2]) : A 2 ≠ A 0 := by
  simpa using hABC.injective.ne (by decide : (2 : Fin 3) ≠ 0)

lemma adjacent_vertices_ne {A : ZMod 3 → Point}
    (hABC : AffineIndependent ℝ ![A 0, A 1, A 2]) (i : Fin 7) :
    leftVertex A i ≠ rightVertex A i := by
  fin_cases i <;> first
    | simpa [leftVertex, rightVertex] using vertex_ne_01 hABC
    | simpa [leftVertex, rightVertex] using vertex_ne_12 hABC
    | simpa [leftVertex, rightVertex] using vertex_ne_20 hABC

lemma sphere_center_ne_of_mem_of_ne {s : Circle} {p q : Point}
    (hp : p ∈ s) (hq : q ∈ s) (hpq : p ≠ q) : s.center ≠ p := by
  intro hcenter
  have hradius : s.radius = 0 := by
    have hcenter_mem : s.center ∈ s := by
      simpa [hcenter] using hp
    exact EuclideanGeometry.Sphere.center_mem_iff.mp hcenter_mem
  have hq_dist : dist q p = 0 := by
    simpa [hcenter, hradius] using EuclideanGeometry.mem_sphere.mp hq
  exact hpq (dist_eq_zero.mp hq_dist).symm

-- A line intersects a nondegenerate perpendicular bisector at most once.
lemma collinear_perpBisector_eq {a b p q : Point}
    (hab : a ≠ b)
    (hp : p ∈ AffineSubspace.perpBisector a b)
    (hq : q ∈ AffineSubspace.perpBisector a b)
    (hcol : Collinear ℝ ({p, a, q} : Set Point)) :
    p = q := by
  by_contra hpq
  have hspan_pair_le : affineSpan ℝ ({p, q} : Set Point) ≤ AffineSubspace.perpBisector a b := by
    rw [affineSpan_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hp
    · exact hq
  have ha_span : a ∈ affineSpan ℝ ({p, q} : Set Point) := by
    exact hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hpq
  have ha_perp : a ∈ AffineSubspace.perpBisector a b := hspan_pair_le ha_span
  exact hab (AffineSubspace.left_mem_perpBisector.mp ha_perp)

-- Equal side angles force equal centers.
lemma centers_eq_of_oangle_eq
    {A : ZMod 3 → Point} {ω : Fin 7 → Circle}
    (hABC : AffineIndependent ℝ ![A 0, A 1, A 2])
    (hA : ∀ i : Fin 7, (A i ∈ ω i ∧ A (i + 1) ∈ ω i))
    (hangle : EuclideanGeometry.oangle (A 1) (A 0) (ω 0).center =
      EuclideanGeometry.oangle (A 1) (A 0) (ω 6).center) :
    (ω 0).center = (ω 6).center := by
  have hside : A 1 ≠ A 0 := (vertex_ne_01 hABC).symm
  have hcenter0 : (ω 0).center ≠ A 0 :=
    sphere_center_ne_of_mem_of_ne (hA 0).1 (hA 0).2 (vertex_ne_01 hABC)
  have hcenter6 : (ω 6).center ≠ A 0 := by
    have hp : A 0 ∈ ω 6 := by
      simpa using (hA 6).1
    have hq : A 1 ∈ ω 6 := by
      simpa using (hA 6).2
    exact sphere_center_ne_of_mem_of_ne hp hq (vertex_ne_01 hABC)
  have ho0 : EuclideanGeometry.oangle (ω 0).center (A 0) (ω 6).center = 0 := by
    have hadd := EuclideanGeometry.oangle_add hside hcenter0 hcenter6
    exact add_left_cancel
      (a := EuclideanGeometry.oangle (A 1) (A 0) (ω 0).center)
      (by simpa [hangle] using hadd)
  have hcol : Collinear ℝ ({(ω 0).center, A 0, (ω 6).center} : Set Point) :=
    EuclideanGeometry.oangle_eq_zero_or_eq_pi_iff_collinear.1 (Or.inl ho0)
  have hp : (ω 0).center ∈ AffineSubspace.perpBisector (A 0) (A 1) := by
    simpa [leftVertex, rightVertex, circleCenter] using center_mem_perpBisector hA 0
  have hq : (ω 6).center ∈ AffineSubspace.perpBisector (A 0) (A 1) := by
    simpa [leftVertex, rightVertex, circleCenter] using center_mem_perpBisector hA 6
  exact collinear_perpBisector_eq (vertex_ne_01 hABC) hp hq hcol

-- The shared vertex lies strictly between tangent centers.
lemma shared_vertex_sbtw
    {A : ZMod 3 → Point} {ω : Fin 7 → Circle}
    (hABC : AffineIndependent ℝ ![A 0, A 1, A 2])
    (hTangent : ∀ i, i < 6 → ExternallyTangent (ω i) (ω (i + 1)))
    (hA : ∀ i : Fin 7, (A i ∈ ω i ∧ A (i + 1) ∈ ω i))
    (i : Fin 7) (hi : i < 6) :
    Sbtw ℝ (circleCenter ω i) (rightVertex A i) (circleCenter ω (i + 1)) := by
  refine ⟨(tangent_at_shared_vertex hTangent hA i hi).wbtw, ?_, ?_⟩
  · exact (sphere_center_ne_of_mem_of_ne
      (rightVertex_mem_circle hA i) (leftVertex_mem_circle hA i)
      (adjacent_vertices_ne hABC i).symm).symm
  · have hpq : rightVertex A i ≠ rightVertex A (i + 1) := by
      rw [rightVertex_eq_leftVertex_succ A i hi]
      exact adjacent_vertices_ne hABC (i + 1)
    exact (sphere_center_ne_of_mem_of_ne
      (rightVertex_mem_next_circle hA i hi) (rightVertex_mem_circle hA (i + 1)) hpq).symm

-- One straight-center step for directed angles.
lemma directed_angle_step {a b c u v : Point}
    (hab : a ≠ b) (hcb : c ≠ b)
    (hu : u ∈ AffineSubspace.perpBisector a b)
    (hsbtw : Sbtw ℝ u b v) :
    EuclideanGeometry.oangle b a u + EuclideanGeometry.oangle c b v +
      EuclideanGeometry.oangle a b c = (Real.pi : Real.Angle) := by
  have hside : EuclideanGeometry.oangle b a u + EuclideanGeometry.oangle a b u = 0 :=
    side_oangle_add_eq_zero hu
  have htangent_sum :
      EuclideanGeometry.oangle a b u + (Real.pi : Real.Angle) =
        EuclideanGeometry.oangle a b v := by
    have hadd := EuclideanGeometry.oangle_add hab hsbtw.left_ne hsbtw.right_ne
    rw [hsbtw.oangle₁₂₃_eq_pi] at hadd
    exact hadd
  have htriangle_sum :
      EuclideanGeometry.oangle a b c + EuclideanGeometry.oangle c b v =
        EuclideanGeometry.oangle a b v :=
    EuclideanGeometry.oangle_add hab hcb hsbtw.right_ne
  have hx :
      EuclideanGeometry.oangle a b u + (Real.pi : Real.Angle) =
        EuclideanGeometry.oangle a b c + EuclideanGeometry.oangle c b v :=
    htangent_sum.trans htriangle_sum.symm
  calc
    EuclideanGeometry.oangle b a u + EuclideanGeometry.oangle c b v +
          EuclideanGeometry.oangle a b c
        = EuclideanGeometry.oangle b a u +
            (EuclideanGeometry.oangle a b c + EuclideanGeometry.oangle c b v) := by
          abel
    _ = EuclideanGeometry.oangle b a u +
        (EuclideanGeometry.oangle a b u + (Real.pi : Real.Angle)) := by
          rw [← hx]
    _ = (EuclideanGeometry.oangle b a u + EuclideanGeometry.oangle a b u) +
        (Real.pi : Real.Angle) := by
          abel
    _ = 0 + (Real.pi : Real.Angle) := by
          rw [hside]
    _ = (Real.pi : Real.Angle) := zero_add _

-- One tangency advances the side angle.
lemma directed_angle_recurrence
    {A : ZMod 3 → Point} {ω : Fin 7 → Circle}
    (hABC : AffineIndependent ℝ ![A 0, A 1, A 2])
    (hTangent : ∀ i, i < 6 → ExternallyTangent (ω i) (ω (i + 1)))
    (hA : ∀ i : Fin 7, (A i ∈ ω i ∧ A (i + 1) ∈ ω i))
    (i : Fin 7) (hi : i < 6) :
    sideAngle A ω i +
        EuclideanGeometry.oangle (rightVertex A (i + 1)) (rightVertex A i)
          (circleCenter ω (i + 1)) +
      turnAngle A i = (Real.pi : Real.Angle) := by
  have hcb : rightVertex A (i + 1) ≠ rightVertex A i := by
    rw [rightVertex_eq_leftVertex_succ A i hi]
    exact (adjacent_vertices_ne hABC (i + 1)).symm
  simpa [sideAngle, turnAngle] using
    directed_angle_step (adjacent_vertices_ne hABC i) hcb
      (center_mem_perpBisector hA i) (shared_vertex_sbtw hABC hTangent hA i hi)

lemma side_oangle_eq_after_six
    {A : ZMod 3 → Point} {ω : Fin 7 → Circle}
    (hABC : AffineIndependent ℝ ![A 0, A 1, A 2])
    (hTangent : ∀ i, i < 6 → ExternallyTangent (ω i) (ω (i + 1)))
    (hA : ∀ i : Fin 7, (A i ∈ ω i ∧ A (i + 1) ∈ ω i)) :
    sideAngle A ω 0 = sideAngle A ω 6 := by
  -- Pair recurrences three apart and telescope.
  let θ : Fin 7 → Real.Angle := fun i => sideAngle A ω i
  let τ : Fin 7 → Real.Angle := fun i => turnAngle A i
  have step (i : Fin 7) (hi : i < 6) :
      θ i + θ (i + 1) + τ i = (Real.pi : Real.Angle) := by
    have hshared : leftVertex A (i + 1) = rightVertex A i :=
      (rightVertex_eq_leftVertex_succ A i hi).symm
    simpa [θ, τ, sideAngle, turnAngle, hshared] using
      directed_angle_recurrence hABC hTangent hA i hi
  have h01 : θ 0 + θ 1 + τ 0 = (Real.pi : Real.Angle) := by
    simpa using step 0 (by decide)
  have h12 : θ 1 + θ 2 + τ 1 = (Real.pi : Real.Angle) := by
    simpa using step 1 (by decide)
  have h23 : θ 2 + θ 3 + τ 2 = (Real.pi : Real.Angle) := by
    simpa using step 2 (by decide)
  have h34 : θ 3 + θ 4 + τ 0 = (Real.pi : Real.Angle) := by
    simpa [τ, turnAngle, leftVertex, rightVertex] using step 3 (by decide)
  have h45 : θ 4 + θ 5 + τ 1 = (Real.pi : Real.Angle) := by
    simpa [τ, turnAngle, leftVertex, rightVertex] using step 4 (by decide)
  have h56 : θ 5 + θ 6 + τ 2 = (Real.pi : Real.Angle) := by
    simpa [τ, turnAngle, leftVertex, rightVertex] using step 5 (by decide)
  have samePair {x y z w t : Real.Angle}
      (hxy : x + y + t = (Real.pi : Real.Angle))
      (hzw : z + w + t = (Real.pi : Real.Angle)) :
      x + y = z + w := by
    apply add_right_cancel (b := t)
    rw [hxy, hzw]
  have h04 : θ 0 + θ 1 = θ 3 + θ 4 := samePair h01 h34
  have h15 : θ 1 + θ 2 = θ 4 + θ 5 := samePair h12 h45
  have h26 : θ 2 + θ 3 = θ 5 + θ 6 := samePair h23 h56
  have hbig : θ 0 + (θ 1 + θ 2 + θ 3) =
      θ 6 + (θ 1 + θ 2 + θ 3) := by
    calc
      θ 0 + (θ 1 + θ 2 + θ 3) =
        (θ 0 + θ 1) + (θ 2 + θ 3) := by
            abel
      _ =
        (θ 3 + θ 4) + (θ 5 + θ 6) := by
            rw [h04, h26]
      _ =
        θ 6 + (θ 1 + θ 2 + θ 3) := by
            rw [h15]
            abel
  change θ 0 = θ 6
  exact add_right_cancel hbig

lemma circle_eq_of_center_eq
    {A : ZMod 3 → Point} {ω : Fin 7 → Circle}
    (hA : ∀ i : Fin 7, (A i ∈ ω i ∧ A (i + 1) ∈ ω i))
    (hcenter : (ω 0).center = (ω 6).center) :
    ω 0 = ω 6 := by
  refine (EuclideanGeometry.Sphere.center_eq_iff_eq_of_mem (hA 0).1 ?_).mp hcenter
  simpa using (hA 6).1

snip end

problem usa2000_p5
    (A : ZMod 3 → EuclideanSpace ℝ (Fin 2))
    (hABC : AffineIndependent ℝ ![A 0, A 1, A 2])
    (ω : Fin 7 → Circle)
    (hTangent : ∀ i, i < 6 → ExternallyTangent (ω i) (ω (i + 1)))
    (hA : ∀ i : Fin 7, (A i ∈ ω i ∧ A (i + 1) ∈ ω i))
    : ω 0 = ω 6 := by
  apply circle_eq_of_center_eq hA
  apply centers_eq_of_oangle_eq hABC hA
  simpa [sideAngle, leftVertex, rightVertex, circleCenter] using
    side_oangle_eq_after_six hABC hTangent hA

end Usa2000P5
