/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.OfNorm
public import Mathlib.Geometry.Euclidean.Circumcenter
public import Mathlib.Geometry.Euclidean.Sphere.Power
public import Mathlib.Geometry.Euclidean.Sphere.SecondInter
public import Mathlib.Geometry.Euclidean.Triangle
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 2010, Problem 4

Let P be a point interior to triangle ABC (with CA ≠ CB). The lines AP, BP
and CP meet again its circumcircle Γ at K, L, M, respectively. The tangent
line at C to Γ meets the line AB at S. Show that from SC = SP follows MK = ML.
-/

open Affine EuclideanGeometry

open scoped EuclideanGeometry Real

variable (V : Type*) (Pt : Type*)
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt] [NormedAddTorsor V Pt]

namespace Imo2010P4

snip begin

/-!
We follow the classical solution (compare e.g. the second solution in Evan
Chen's notes), but recast it in a purely metric form that avoids oriented
angles entirely:

* By the tangent-secant theorem, `SC² = SA · SB`, and `SC = SP` is given.
* Since `S` lies on the tangent line at `C`, it is outside the circle, so `A`
  and `B` lie on the same ray from `S`; hence `∠BSP = ∠ASP` and
  `∠BSC = ∠ASC`.
* The law of cosines in triangles `SAP`/`SBP` and `SAC`/`SBC` then yields the
  similarity relations `SA · PB² = SB · PA²` and `SA · BC² = SB · AC²`, from
  which `AC · PB = BC · PA`.
* The intersecting chords theorem gives `AP · PK = BP · PL = CP · PM`, and with
  vertical angles `∠KPM = ∠APC`, `∠LPM = ∠BPC`, a final law-of-cosines
  computation gives `MK² · AP² · BP² = ML² · AP² · BP²`, hence `MK = ML`.
-/

/-- The main geometric content of the problem, stated over an arbitrary sphere
through `A`, `B`, `C`. -/
theorem dist_mk_eq_dist_ml {V : Type*} {Pt : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt] [NormedAddTorsor V Pt]
    {s : Sphere Pt} {A B C P K L M S : Pt}
    (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s)
    (hncol : ¬ Collinear ℝ ({A, B, C} : Set Pt))
    (hP_in : dist P s.center < s.radius)
    (hK : K = s.secondInter A (P -ᵥ A))
    (hL : L = s.secondInter B (P -ᵥ B))
    (hM : M = s.secondInter C (P -ᵥ C))
    (hSAB : S ∈ line[ℝ, A, B])
    (hSTan : s.IsTangentAt C line[ℝ, S, C])
    (hSC : dist S C = dist S P) :
    dist M K = dist M L := by
  -- Non-degeneracy of the triangle vertices.
  have hA_ne_C : A ≠ C := by
    intro h
    apply hncol
    rw [h]
    simpa using collinear_pair ℝ B C
  have hB_ne_C : B ≠ C := by
    intro h
    apply hncol
    rw [h]
    simpa using collinear_pair ℝ A C
  -- `S` is not a vertex of the triangle.
  have hS_ne_C : S ≠ C := by
    intro h
    apply hncol
    have hCline : C ∈ line[ℝ, A, B] := by rwa [h] at hSAB
    exact (collinear_insert_of_mem_affineSpan_pair hCline).subset (by grind)
  have hS_ne_A : S ≠ A := by
    intro h
    have hAline : A ∈ line[ℝ, S, C] := by
      rw [h]
      exact left_mem_affineSpan_pair ℝ A C
    exact hA_ne_C (hSTan.mem_and_mem_iff_eq.mp ⟨hA, hAline⟩)
  have hS_ne_B : S ≠ B := by
    intro h
    have hBline : B ∈ line[ℝ, S, C] := by
      rw [h]
      exact left_mem_affineSpan_pair ℝ B C
    exact hB_ne_C (hSTan.mem_and_mem_iff_eq.mp ⟨hB, hBline⟩)
  -- `S` lies outside the circle, hence not strictly between `A` and `B`.
  have hSr : s.radius < dist S s.center :=
    hSTan.radius_lt_dist_center (left_mem_affineSpan_pair ℝ S C) hS_ne_C
  have hnotSbtw : ¬ Sbtw ℝ A S B := by
    intro h
    have hlt := h.dist_lt_max_dist s.center
    rw [mem_sphere.mp hA, mem_sphere.mp hB, max_self] at hlt
    linarith
  -- So `A` and `B` lie on the same ray from `S`.
  have hray : SameRay ℝ (A -ᵥ S) (B -ᵥ S) := by
    have hcol : Collinear ℝ ({S, A, B} : Set Pt) :=
      collinear_insert_of_mem_affineSpan_pair hSAB
    rcases hcol.wbtw_or_wbtw_or_wbtw with h | h | h
    · exact h.sameRay_vsub_left
    · exact (h.symm.sameRay_vsub_left).symm
    · exact absurd (sbtw_comm.mpr ⟨h, hS_ne_B, hS_ne_A⟩) hnotSbtw
  -- Hence the angle coincidences at `S`.
  obtain ⟨r₁, r₂, hr₁, hr₂, hrr⟩ :=
    hray.exists_pos (vsub_ne_zero.mpr hS_ne_A.symm) (vsub_ne_zero.mpr hS_ne_B.symm)
  have hrr₂ : (r₁ / r₂) • (A -ᵥ S) = B -ᵥ S := by
    have h2 := congrArg (fun v => (r₂⁻¹ : ℝ) • v) hrr
    simp only [smul_smul, inv_mul_cancel₀ hr₂.ne', one_smul] at h2
    rwa [mul_comm, ← div_eq_mul_inv] at h2
  have hAngP : ∠ B S P = ∠ A S P := angle_smul_left_of_pos P (div_pos hr₁ hr₂) hrr₂
  have hAngC : ∠ B S C = ∠ A S C := angle_smul_left_of_pos C (div_pos hr₁ hr₂) hrr₂
  -- The second intersections `K`, `L`, `M` lie on the sphere, and `P` lies
  -- strictly between each vertex and its second intersection.
  have hsK : Sbtw ℝ A P K := by
    rw [hK]
    exact Sphere.sbtw_secondInter hA hP_in
  have hsL : Sbtw ℝ B P L := by
    rw [hL]
    exact Sphere.sbtw_secondInter hB hP_in
  have hsM : Sbtw ℝ C P M := by
    rw [hM]
    exact Sphere.sbtw_secondInter hC hP_in
  have hKmem : K ∈ s := by
    rw [hK]
    exact (Sphere.secondInter_mem _).mpr hA
  have hLmem : L ∈ s := by
    rw [hL]
    exact (Sphere.secondInter_mem _).mpr hB
  have hMmem : M ∈ s := by
    rw [hM]
    exact (Sphere.secondInter_mem _).mpr hC
  -- Straight angles at `P`.
  have hAPK : ∠ A P K = π := hsK.angle₁₂₃_eq_pi
  have hBPL : ∠ B P L = π := hsL.angle₁₂₃_eq_pi
  have hCPM : ∠ C P M = π := hsM.angle₁₂₃_eq_pi
  have hKPA : ∠ K P A = π := by rw [angle_comm]; exact hAPK
  have hLPB : ∠ L P B = π := by rw [angle_comm]; exact hBPL
  have hMPC : ∠ M P C = π := by rw [angle_comm]; exact hCPM
  -- Vertical angles at `P`.
  have hVertK : ∠ K P M = ∠ A P C :=
    angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi hKPA hMPC
  have hVertL : ∠ L P M = ∠ B P C :=
    angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi hLPB hMPC
  -- The intersecting chords theorem.
  have hCosph1 : Cospherical ({A, K, C, M} : Set Pt) := by
    refine ⟨s.center, s.radius, fun x hx => ?_⟩
    rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact mem_sphere.mp hA
    · exact mem_sphere.mp hKmem
    · exact mem_sphere.mp hC
    · exact mem_sphere.mp hMmem
  have hCosph2 : Cospherical ({B, L, C, M} : Set Pt) := by
    refine ⟨s.center, s.radius, fun x hx => ?_⟩
    rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact mem_sphere.mp hB
    · exact mem_sphere.mp hLmem
    · exact mem_sphere.mp hC
    · exact mem_sphere.mp hMmem
  have hChordK : dist A P * dist K P = dist C P * dist M P :=
    mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi hCosph1 hAPK hCPM
  have hChordL : dist B P * dist L P = dist C P * dist M P :=
    mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi hCosph2 hBPL hCPM
  -- The tangent-secant theorem, together with `SC = SP`.
  have hPow : dist P S ^ 2 = dist A S * dist B S := by
    have h := Sphere.dist_sq_eq_mul_dist_of_tangent_and_secant hA hB hSAB hSTan
    rw [hSC, dist_comm S P, dist_comm S A, dist_comm S B] at h
    exact h
  -- The law of cosines, in all relevant triangles.
  have hE2 := dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle A S P
  have hE3 := dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle B S P
  rw [hAngP] at hE3
  have hE4 := dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle A S C
  have hE5 := dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle B S C
  rw [hAngC] at hE5
  rw [dist_comm C S, hSC, dist_comm S P] at hE4 hE5
  have hE6 := dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle K P M
  rw [hVertK] at hE6
  have hE7 := dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle L P M
  rw [hVertL] at hE7
  have hE8 := dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle A P C
  have hE9 := dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle B P C
  -- The similarity relations.
  have h₁ : dist A S * (dist B P * dist B P) = dist B S * (dist A P * dist A P) := by
    linear_combination dist A S * hE3 - dist B S * hE2 + (dist A S - dist B S) * hPow
  have h₂ : dist A S * (dist B C * dist B C) = dist B S * (dist A C * dist A C) := by
    linear_combination dist A S * hE5 - dist B S * hE4 + (dist A S - dist B S) * hPow
  have h₃a : dist A S * ((dist A C * dist A C) * (dist B P * dist B P)) =
      dist A S * ((dist B C * dist B C) * (dist A P * dist A P)) := by
    linear_combination (dist A C * dist A C) * h₁ - (dist A P * dist A P) * h₂
  have h₃ : (dist A C * dist A C) * (dist B P * dist B P) =
      (dist B C * dist B C) * (dist A P * dist A P) :=
    mul_left_cancel₀ (dist_ne_zero.mpr hS_ne_A.symm) h₃a
  have h₄ : dist A C * dist B P = dist B C * dist A P := by
    have h₄sq : (dist A C * dist B P) ^ 2 = (dist B C * dist A P) ^ 2 := by
      linear_combination h₃
    exact (sq_eq_sq₀ (by positivity) (by positivity)).mp h₄sq
  -- The final computation.
  have hG : (dist K M * dist K M) * ((dist A P * dist A P) * (dist B P * dist B P)) =
      (dist L M * dist L M) * ((dist A P * dist A P) * (dist B P * dist B P)) := by
    linear_combination
      (dist A P * dist A P) * (dist B P * dist B P) * hE6
        - (dist A P * dist A P) * (dist B P * dist B P) * hE7
        + ((dist B P * dist B P) * (dist A P * dist K P + dist C P * dist M P)
          - 2 * dist M P * dist A P * (dist B P * dist B P) * Real.cos (∠ A P C)) * hChordK
        - ((dist A P * dist A P) * (dist B P * dist L P + dist C P * dist M P)
          - 2 * dist M P * dist B P * (dist A P * dist A P) * Real.cos (∠ B P C)) * hChordL
        + (dist M P * dist M P) * ((dist A P * dist A P) * hE9 - (dist B P * dist B P) * hE8
          + (dist A C * dist B P + dist B C * dist A P) * h₄)
  have hpA : dist A P ≠ 0 := dist_ne_zero.mpr hsK.left_ne
  have hpB : dist B P ≠ 0 := dist_ne_zero.mpr hsL.left_ne
  have hQ : (dist A P * dist A P) * (dist B P * dist B P) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hpA hpA) (mul_ne_zero hpB hpB)
  have huv : dist K M * dist K M = dist L M * dist L M := mul_right_cancel₀ hQ hG
  have h2 : dist K M ^ 2 = dist L M ^ 2 := by linear_combination huv
  have hfin : dist K M = dist L M := (sq_eq_sq₀ dist_nonneg dist_nonneg).mp h2
  rw [dist_comm M K, dist_comm M L]
  exact hfin

snip end

problem imo2010_p4
    {A B C P K L M S : Pt}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (_hCA : dist C A ≠ dist C B)
    (hP : P ∈ (⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ Pt).interior)
    (hK : K = (⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ Pt).circumsphere.secondInter A (P -ᵥ A))
    (hL : L = (⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ Pt).circumsphere.secondInter B (P -ᵥ B))
    (hM : M = (⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ Pt).circumsphere.secondInter C (P -ᵥ C))
    (hSAB : S ∈ line[ℝ, A, B])
    (hSTan : (⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ Pt).circumsphere.IsTangentAt C
      line[ℝ, S, C])
    (hSC : dist S C = dist S P) :
    dist M K = dist M L := by
  have hA : A ∈ (⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ Pt).circumsphere :=
    Affine.Simplex.mem_circumsphere _ 0
  have hB : B ∈ (⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ Pt).circumsphere :=
    Affine.Simplex.mem_circumsphere _ 1
  have hC : C ∈ (⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ Pt).circumsphere :=
    Affine.Simplex.mem_circumsphere _ 2
  have hncol : ¬ Collinear ℝ ({A, B, C} : Set Pt) :=
    affineIndependent_iff_not_collinear_set.mp hABC
  have hP_in : dist P (⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ Pt).circumsphere.center
      < (⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ Pt).circumsphere.radius := by
    rw [Affine.Simplex.circumsphere_center, Affine.Simplex.circumsphere_radius]
    exact Affine.Simplex.dist_lt_of_mem_interior_of_strictConvexSpace _ hP fun i => by
      have hi := Affine.Simplex.mem_circumsphere (⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ Pt) i
      rw [mem_sphere, Affine.Simplex.circumsphere_center,
        Affine.Simplex.circumsphere_radius] at hi
      exact hi.le
  exact dist_mk_eq_dist_ml hA hB hC hncol hP_in hK hL hM hSAB hSTan hSC

end Imo2010P4
