/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Geometry.Euclidean.Circumcenter
public import Mathlib.Geometry.Euclidean.Sphere.SecondInter
public import Mathlib.Geometry.Euclidean.Triangle
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 2003, Problem 4

Let ABCD be a cyclic quadrilateral. Let P, Q and R be the feet of the
perpendiculars from D to the lines BC, CA and AB, respectively. Show that
PQ = QR if and only if the bisectors of the angles ∠ABC and ∠ADC meet on AC.
-/

namespace Imo2003P4

open scoped EuclideanGeometry RealInnerProductSpace Real

open EuclideanGeometry Affine

local instance planeFiniteDim :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
  ⟨finrank_euclideanSpace_fin⟩

snip begin

/-- The 2-dimensional Binet–Cauchy (Lagrange) identity for inner products. -/
lemma inner_binet_cauchy (x u w : EuclideanSpace ℝ (Fin 2)) :
    ⟪x, u⟫ * ⟪x, u⟫ * ⟪w, w⟫ + ⟪x, w⟫ * ⟪x, w⟫ * ⟪u, u⟫
        - 2 * ⟪x, u⟫ * ⟪x, w⟫ * ⟪u, w⟫
      = ⟪x, x⟫ * (⟪u, u⟫ * ⟪w, w⟫ - ⟪u, w⟫ * ⟪u, w⟫) := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, starRingEnd_apply,
    star_trivial]
  ring

/-- The metric fact behind the Simson line: the distance between the feet of
the perpendiculars from `D` to the lines `AB` and `AC` equals
`dist A D * sin (∠BAC)`. No nondegeneracy of the feet is needed. -/
lemma simson_dist (A B C D : EuclideanSpace ℝ (Fin 2)) (hB : B ≠ A) (hC : C ≠ A) :
    dist (orthogonalProjection (line[ℝ, A, B]) D : EuclideanSpace ℝ (Fin 2))
        (orthogonalProjection (line[ℝ, A, C]) D : EuclideanSpace ℝ (Fin 2))
      = dist A D * Real.sin (∠ B A C) := by
  set R := (orthogonalProjection (line[ℝ, A, B]) D : EuclideanSpace ℝ (Fin 2)) with hR
  set Q := (orthogonalProjection (line[ℝ, A, C]) D : EuclideanSpace ℝ (Fin 2)) with hQ
  set u := B -ᵥ A with hu
  set w := C -ᵥ A with hw
  set d := D -ᵥ A with hd
  have hu0 : u ≠ 0 := vsub_ne_zero.mpr hB
  have hw0 : w ≠ 0 := vsub_ne_zero.mpr hC
  have huu0 : ⟪u, u⟫ ≠ 0 := inner_self_ne_zero.mpr hu0
  have hww0 : ⟪w, w⟫ ≠ 0 := inner_self_ne_zero.mpr hw0
  -- The foot `R`: `R -ᵥ A = t • u` with `t * ⟪u, u⟫ = ⟪u, d⟫`.
  have hRAdir : R -ᵥ A ∈ ℝ ∙ u := by
    have h : R -ᵥ A ∈ (line[ℝ, A, B]).direction :=
      AffineSubspace.vsub_mem_direction (orthogonalProjection_mem _)
        (left_mem_affineSpan_pair ℝ A B)
    rwa [direction_affineSpan, vectorSpan_pair_rev] at h
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hRAdir
  have htorth : ⟪u, D -ᵥ R⟫ = 0 :=
    Submodule.inner_right_of_mem_orthogonal (K := (line[ℝ, A, B]).direction)
      (by rw [direction_affineSpan, vectorSpan_pair_rev]
          exact Submodule.mem_span_singleton_self u)
      (vsub_orthogonalProjection_mem_direction_orthogonal _ _)
  have htDR : D -ᵥ R = d - t • u := by rw [hd, ht, vsub_sub_vsub_cancel_right]
  have htval : t * ⟪u, u⟫ = ⟪u, d⟫ := by
    rw [htDR, inner_sub_right, real_inner_smul_right, sub_eq_zero] at htorth
    exact htorth.symm
  -- The foot `Q`: `Q -ᵥ A = s • w` with `s * ⟪w, w⟫ = ⟪w, d⟫`.
  have hQAdir : Q -ᵥ A ∈ ℝ ∙ w := by
    have h : Q -ᵥ A ∈ (line[ℝ, A, C]).direction :=
      AffineSubspace.vsub_mem_direction (orthogonalProjection_mem _)
        (left_mem_affineSpan_pair ℝ A C)
    rwa [direction_affineSpan, vectorSpan_pair_rev] at h
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hQAdir
  have hsorth : ⟪w, D -ᵥ Q⟫ = 0 :=
    Submodule.inner_right_of_mem_orthogonal (K := (line[ℝ, A, C]).direction)
      (by rw [direction_affineSpan, vectorSpan_pair_rev]
          exact Submodule.mem_span_singleton_self w)
      (vsub_orthogonalProjection_mem_direction_orthogonal _ _)
  have hsDQ : D -ᵥ Q = d - s • w := by rw [hd, hs, vsub_sub_vsub_cancel_right]
  have hsval : s * ⟪w, w⟫ = ⟪w, d⟫ := by
    rw [hsDQ, inner_sub_right, real_inner_smul_right, sub_eq_zero] at hsorth
    exact hsorth.symm
  -- Compute `dist R Q ^ 2`.
  have hRQv : R -ᵥ Q = t • u - s • w := by rw [ht, hs, vsub_sub_vsub_cancel_right]
  have hdist : dist R Q = ‖t • u - s • w‖ := by rw [dist_eq_norm_vsub _ R Q, hRQv]
  have hnorm : ‖t • u - s • w‖ ^ 2
      = t * t * ⟪u, u⟫ - 2 * (t * s) * ⟪u, w⟫ + s * s * ⟪w, w⟫ := by
    rw [norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
      Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs,
      ← real_inner_self_eq_norm_sq u, ← real_inner_self_eq_norm_sq w]
    ring
  have hnum : (t * t * ⟪u, u⟫ - 2 * (t * s) * ⟪u, w⟫ + s * s * ⟪w, w⟫)
        * (⟪u, u⟫ * ⟪w, w⟫)
      = ⟪d, d⟫ * (⟪u, u⟫ * ⟪w, w⟫ - ⟪u, w⟫ * ⟪u, w⟫) := by
    have hbc := inner_binet_cauchy d u w
    rw [← real_inner_comm d u, ← real_inner_comm d w] at hbc
    linear_combination
      htval * ((t * ⟪u, u⟫ + ⟪u, d⟫) * ⟪w, w⟫)
        + hsval * ((s * ⟪w, w⟫ + ⟪w, d⟫) * ⟪u, u⟫)
        + htval * (-2 * (s * ⟪w, w⟫) * ⟪u, w⟫)
        + hsval * (-2 * ⟪u, d⟫ * ⟪u, w⟫)
        + hbc
  have hL : dist R Q ^ 2 * (⟪u, u⟫ * ⟪w, w⟫)
      = ⟪d, d⟫ * (⟪u, u⟫ * ⟪w, w⟫ - ⟪u, w⟫ * ⟪u, w⟫) := by
    rw [hdist, hnorm, hnum]
  -- Compute the right-hand side squared.
  have hsin : Real.sin (∠ B A C)
      = √(⟪u, u⟫ * ⟪w, w⟫ - ⟪u, w⟫ * ⟪u, w⟫) / (‖u‖ * ‖w‖) := by
    unfold EuclideanGeometry.angle
    rw [← hu, ← hw]
    exact InnerProductGeometry.sin_angle hu0 hw0
  have hX0 : (0:ℝ) ≤ ⟪u, u⟫ * ⟪w, w⟫ - ⟪u, w⟫ * ⟪u, w⟫ := by
    have h2 := abs_real_inner_le_norm u w
    rw [abs_le] at h2
    rw [real_inner_self_eq_norm_sq u, real_inner_self_eq_norm_sq w]
    nlinarith [h2.1, h2.2, mul_nonneg (norm_nonneg u) (norm_nonneg w)]
  have hdAD : dist A D = ‖d‖ := by rw [hd]; exact dist_eq_norm_vsub' _ A D
  have hR' : (dist A D * Real.sin (∠ B A C)) ^ 2 * (⟪u, u⟫ * ⟪w, w⟫)
      = ⟪d, d⟫ * (⟪u, u⟫ * ⟪w, w⟫ - ⟪u, w⟫ * ⟪u, w⟫) := by
    rw [mul_pow, hsin, div_pow, Real.sq_sqrt hX0, hdAD, mul_pow,
      ← real_inner_self_eq_norm_sq d, ← real_inner_self_eq_norm_sq u,
      ← real_inner_self_eq_norm_sq w]
    field_simp [huu0, hww0]
  have hsq : dist R Q ^ 2 = (dist A D * Real.sin (∠ B A C)) ^ 2 :=
    mul_right_cancel₀ (mul_ne_zero huu0 hww0) (by rw [hL, hR'])
  have hsin0 : (0:ℝ) ≤ Real.sin (∠ B A C) :=
    Real.sin_nonneg_of_mem_Icc ⟨angle_nonneg B A C, angle_le_pi B A C⟩
  have hsq2 : dist R Q * dist R Q
      = (dist A D * Real.sin (∠ B A C)) * (dist A D * Real.sin (∠ B A C)) := by
    rw [← pow_two, ← pow_two]
    exact hsq
  exact (mul_self_inj dist_nonneg (mul_nonneg dist_nonneg hsin0)).mp hsq2

/-- A version of the law of sines. -/
lemma sin_angle_mul_dist_eq (A B C : EuclideanSpace ℝ (Fin 2))
    (h : ¬Collinear ℝ ({A, B, C} : Set _)) :
    Real.sin (∠ B A C) * dist A B = Real.sin (∠ B C A) * dist B C := by
  have e1 : Real.sin (∠ A B C) * dist B C = Real.sin (∠ C A B) * dist C A := law_sin A B C
  have e2 : Real.sin (∠ B C A) * dist C A = Real.sin (∠ A B C) * dist A B := law_sin B C A
  rw [angle_comm C A B] at e1
  have hsin : Real.sin (∠ A B C) ≠ 0 := sin_ne_zero_of_not_collinear h
  have hg : Real.sin (∠ A B C)
      * (Real.sin (∠ B A C) * dist A B - Real.sin (∠ B C A) * dist B C) = 0 := by
    linear_combination -(Real.sin (∠ B A C)) * e2 - (Real.sin (∠ B C A)) * e1
  rcases mul_eq_zero.mp hg with h0 | h0
  · exact absurd h0 hsin
  · exact sub_eq_zero.mp h0

/-- The angle bisector theorem: a point of the open segment `AC` on the bisector of
`∠ABC` divides it in the ratio `AB : BC`. -/
lemma dist_mul_dist_of_bisect {A B C X : EuclideanSpace ℝ (Fin 2)}
    (hX : Sbtw ℝ A X C) (hABC : ¬Collinear ℝ ({A, B, C} : Set _))
    (hbis : ∠ A B X = ∠ X B C) :
    dist A X * dist B C = dist A B * dist X C := by
  have hXB : X ≠ B := by
    intro h
    subst h
    exact hABC hX.1.collinear
  have hBA : B ≠ A := by
    intro h
    apply hABC
    rw [h]
    simpa using collinear_pair ℝ A C
  have hBC : B ≠ C := by
    intro h
    apply hABC
    rw [h]
    simpa using collinear_pair ℝ A C
  have hncolBAC : ¬Collinear ℝ ({B, A, C} : Set _) := by
    rw [Set.insert_comm B A]
    exact hABC
  have e1 : Real.sin (∠ A B X) * dist B X = Real.sin (∠ X A B) * dist X A := law_sin A B X
  have e2 : Real.sin (∠ C B X) * dist B X = Real.sin (∠ X C B) * dist X C := law_sin C B X
  have h1 : ∠ X A B = ∠ C A B := Sbtw.angle_eq_left B hX
  have h2 : ∠ X C B = ∠ A C B := Sbtw.angle_eq_left B hX.symm
  rw [h1, angle_comm C A B, dist_comm X A] at e1
  rw [h2, angle_comm A C B] at e2
  have hbis2 : Real.sin (∠ A B X) = Real.sin (∠ C B X) := by rw [hbis, angle_comm X B C]
  rw [hbis2] at e1
  have e3 : Real.sin (∠ B A C) * dist A X = Real.sin (∠ B C A) * dist X C := e1.symm.trans e2
  have eS1 : Real.sin (∠ B A C) * dist A B = Real.sin (∠ B C A) * dist B C :=
    sin_angle_mul_dist_eq A B C hABC
  have hsinA : Real.sin (∠ B A C) ≠ 0 := sin_ne_zero_of_not_collinear hncolBAC
  have hg : Real.sin (∠ B A C) * (dist A X * dist B C - dist A B * dist X C) = 0 := by
    linear_combination e3 * dist B C - eS1 * dist X C
  rcases mul_eq_zero.mp hg with h0 | h0
  · exact absurd h0 hsinA
  · exact sub_eq_zero.mp h0

/-- The converse of the angle bisector theorem. -/
lemma bisect_of_dist_mul_dist {A B C X : EuclideanSpace ℝ (Fin 2)}
    (hX : Sbtw ℝ A X C) (hABC : ¬Collinear ℝ ({A, B, C} : Set _))
    (hratio : dist A X * dist B C = dist A B * dist X C) :
    ∠ A B X = ∠ X B C := by
  have hXB : X ≠ B := by
    intro h
    subst h
    exact hABC hX.1.collinear
  have hBA : B ≠ A := by
    intro h
    apply hABC
    rw [h]
    simpa using collinear_pair ℝ A C
  have hBC : B ≠ C := by
    intro h
    apply hABC
    rw [h]
    simpa using collinear_pair ℝ A C
  have hncolBAC : ¬Collinear ℝ ({B, A, C} : Set _) := by
    rw [Set.insert_comm B A]
    exact hABC
  have e1 : Real.sin (∠ A B X) * dist B X = Real.sin (∠ X A B) * dist X A := law_sin A B X
  have e2 : Real.sin (∠ C B X) * dist B X = Real.sin (∠ X C B) * dist X C := law_sin C B X
  have h1 : ∠ X A B = ∠ C A B := Sbtw.angle_eq_left B hX
  have h2 : ∠ X C B = ∠ A C B := Sbtw.angle_eq_left B hX.symm
  rw [h1, angle_comm C A B, dist_comm X A] at e1
  rw [h2, angle_comm A C B] at e2
  have eS1 : Real.sin (∠ B A C) * dist A B = Real.sin (∠ B C A) * dist B C :=
    sin_angle_mul_dist_eq A B C hABC
  have hsin : Real.sin (∠ A B X) = Real.sin (∠ C B X) := by
    have hBX0 : dist B X ≠ 0 := dist_ne_zero.mpr hXB.symm
    have hBC0 : dist B C ≠ 0 := dist_ne_zero.mpr hBC
    have hg : Real.sin (∠ A B X) * (dist B X * dist B C)
        = Real.sin (∠ C B X) * (dist B X * dist B C) := by
      linear_combination e1 * dist B C - e2 * dist B C
        + hratio * Real.sin (∠ B A C) + eS1 * dist X C
    exact mul_right_cancel₀ (mul_ne_zero hBX0 hBC0) hg
  have hsum : ∠ A B X + ∠ X B C = ∠ A B C := angle_add_of_ne_of_ne hBA hBC hX.1
  have hlt : ∠ A B C < π := angle_lt_pi_of_not_collinear hABC
  have hsinc : Real.sin (∠ A B X) = Real.sin (∠ X B C) := by rw [hsin, angle_comm C B X]
  rcases Real.sin_eq_sin_iff.mp hsinc with ⟨k, hk | hk⟩
  · -- `∠XBC = 2kπ + ∠ABX` forces `k = 0`.
    have ha1 := angle_nonneg A B X
    have ha2 := angle_le_pi A B X
    have ha3 := angle_nonneg X B C
    have ha4 := angle_le_pi X B C
    have hk0 : k = 0 := by
      have h1 : -π ≤ 2 * (k:ℝ) * π := by linarith
      have h2 : 2 * (k:ℝ) * π ≤ π := by linarith
      have h1' : (-1:ℝ) ≤ 2 * k := by
        have h3 : (0:ℝ) ≤ (2 * (k:ℝ) + 1) * π := by linarith [Real.pi_pos]
        have h4 := nonneg_of_mul_nonneg_left h3 Real.pi_pos
        linarith
      have h2' : (2:ℝ) * k ≤ 1 := by
        have h5 : (2 * (k:ℝ) - 1) * π ≤ 0 := by linarith [Real.pi_pos]
        have h6 := nonpos_of_mul_nonpos_left h5 Real.pi_pos
        linarith
      have h1i : (-1:ℤ) ≤ 2 * k := by exact_mod_cast h1'
      have h2i : (2:ℤ) * k ≤ 1 := by exact_mod_cast h2'
      omega
    rw [hk0] at hk
    simp at hk
    exact hk.symm
  · -- `∠XBC = (2k+1)π - ∠ABX` contradicts `∠ABX + ∠XBC < π`.
    exfalso
    have hsum2 : ∠ A B X + ∠ X B C = (2 * (k:ℝ) + 1) * π := by linarith
    have hpos : (0:ℝ) ≤ 2 * k + 1 := by
      have h5 : (0:ℝ) ≤ (2 * (k:ℝ) + 1) * π := by
        rw [← hsum2]
        have := angle_nonneg A B X
        have := angle_nonneg X B C
        linarith
      have h6 := nonneg_of_mul_nonneg_left h5 Real.pi_pos
      linarith
    have hlt3 : (2:ℝ) * k + 1 < 1 := by
      have h7 : (2 * (k:ℝ) + 1) * π < π := by rw [← hsum2]; linarith [hsum, hlt]
      have h8 : (2 * (k:ℝ)) * π < 0 := by linarith [Real.pi_pos]
      have h9 : (2:ℝ) * k < 0 := by
        have h8' : (2 * (k:ℝ)) * π < (0:ℝ) * π := by simpa using h8
        exact lt_of_mul_lt_mul_right h8' Real.pi_pos.le
      linarith
    have hposi : (0:ℤ) ≤ 2 * k + 1 := by exact_mod_cast hpos
    have hlti : (2:ℤ) * k + 1 < 1 := by exact_mod_cast hlt3
    omega

/-- A point of the circumcircle of a nondegenerate triangle `ABC` that differs from
`A` and `C` does not lie on the line `AC`. -/
lemma not_collinear_of_concyclic {A B C D : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C]) (hcyc : Concyclic {A, B, C, D})
    (hDA : D ≠ A) (hDC : D ≠ C) :
    ¬Collinear ℝ ({A, D, C} : Set _) := by
  intro hcol
  have hAC : A ≠ C := hABC.injective.ne (by decide : (0 : Fin 3) ≠ 2)
  have hDline : D ∈ line[ℝ, A, C] :=
    Collinear.mem_affineSpan_of_mem_of_ne hcol (by simp) (by simp) (by simp) hAC
  obtain ⟨s, hs⟩ := cospherical_iff_exists_sphere.mp hcyc.Cospherical
  set T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)) := ⟨![A, B, C], hABC⟩ with hT
  have hs_eq : s = T.circumsphere := by
    apply (Affine.Simplex.circumsphere_unique_dist_eq T).2 s
    constructor
    · rw [Affine.Simplex.span_eq_top T planeFiniteDim.out]
      apply AffineSubspace.mem_top
    · intro x hx
      obtain ⟨i, rfl⟩ := hx
      fin_cases i <;> simp [hT] <;> apply hs <;> simp
  have hDmem : D ∈ T.circumsphere := by
    rw [← hs_eq]
    exact hs (by simp)
  have hAmem : A ∈ T.circumsphere := by
    have h := Affine.Simplex.mem_circumsphere T 0
    simpa [hT] using h
  have hCmem : C ∈ T.circumsphere := by
    have h := Affine.Simplex.mem_circumsphere T 2
    simpa [hT] using h
  have hCD : C = T.circumsphere.secondInter A (C -ᵥ A) := by
    have hiff := Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
      (s := T.circumsphere) (p := A) (q := C) hAmem (p' := C)
      (right_mem_affineSpan_pair ℝ A C)
    rcases hiff.mpr hCmem with h | h
    · exact absurd h hAC.symm
    · exact h
  have hDAC : D = A ∨ D = C := by
    have hiff := Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
      (s := T.circumsphere) (p := A) (q := C) hAmem (p' := D) hDline
    rcases hiff.mpr hDmem with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans hCD.symm)
  rcases hDAC with h | h
  · exact hDA h
  · exact hDC h

snip end

problem imo2003_p4
    (A B C D P Q R : EuclideanSpace ℝ (Fin 2))
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hcyc : Concyclic {A, B, C, D})
    (hDA : D ≠ A) (_hDB : D ≠ B) (hDC : D ≠ C)
    (hP : P = (orthogonalProjection (line[ℝ, B, C]) D : EuclideanSpace ℝ (Fin 2)))
    (hQ : Q = (orthogonalProjection (line[ℝ, C, A]) D : EuclideanSpace ℝ (Fin 2)))
    (hR : R = (orthogonalProjection (line[ℝ, A, B]) D : EuclideanSpace ℝ (Fin 2))) :
    dist P Q = dist Q R ↔
      ∃ X : EuclideanSpace ℝ (Fin 2),
        Sbtw ℝ A X C ∧ ∠ A B X = ∠ X B C ∧ ∠ A D X = ∠ X D C := by
  have hAB : A ≠ B := hABC.injective.ne (by decide : (0 : Fin 3) ≠ 1)
  have hAC : A ≠ C := hABC.injective.ne (by decide : (0 : Fin 3) ≠ 2)
  have hBC : B ≠ C := hABC.injective.ne (by decide : (1 : Fin 3) ≠ 2)
  have hncolABC : ¬Collinear ℝ ({A, B, C} : Set _) :=
    affineIndependent_iff_not_collinear_set.mp hABC
  have hncolADC : ¬Collinear ℝ ({A, D, C} : Set _) :=
    not_collinear_of_concyclic hABC hcyc hDA hDC
  -- The Simson distance formulas.
  have hlineBC : (line[ℝ, B, C] : AffineSubspace ℝ _) = line[ℝ, C, B] := by
    rw [Set.pair_comm]
  have hP' : P = (orthogonalProjection (line[ℝ, C, B]) D : EuclideanSpace ℝ (Fin 2)) := by
    rw [hP, orthogonalProjection_congr hlineBC rfl]
  have hlineCA : (line[ℝ, C, A] : AffineSubspace ℝ _) = line[ℝ, A, C] := by
    rw [Set.pair_comm]
  have hQ' : Q = (orthogonalProjection (line[ℝ, A, C]) D : EuclideanSpace ℝ (Fin 2)) := by
    rw [hQ, orthogonalProjection_congr hlineCA rfl]
  have key1 : dist P Q = dist C D * Real.sin (∠ B C A) := by
    rw [hP', hQ]
    exact simson_dist C B A D hBC hAC
  have key2 : dist Q R = dist A D * Real.sin (∠ B A C) := by
    rw [dist_comm Q R, hR, hQ']
    exact simson_dist A B C D hAB.symm hAC.symm
  have eS1 : Real.sin (∠ B A C) * dist A B = Real.sin (∠ B C A) * dist B C :=
    sin_angle_mul_dist_eq A B C hncolABC
  have hncolBCA : ¬Collinear ℝ ({B, C, A} : Set _) := by
    rw [Set.pair_comm C A, Set.insert_comm B A]
    exact hncolABC
  have hsinC : Real.sin (∠ B C A) ≠ 0 := sin_ne_zero_of_not_collinear hncolBCA
  -- `PQ = QR` is equivalent to `AB·CD = BC·AD`.
  have hstep : (dist C D * Real.sin (∠ B C A) = dist A D * Real.sin (∠ B A C))
      ↔ (dist A B * dist C D = dist B C * dist A D) := by
    constructor
    · intro h
      have hg : Real.sin (∠ B C A) * (dist C D * dist A B - dist A D * dist B C) = 0 := by
        linear_combination h * dist A B + eS1 * dist A D
      rcases mul_eq_zero.mp hg with h0 | h0
      · exact absurd h0 hsinC
      · have h1 := sub_eq_zero.mp h0
        rw [mul_comm (dist A B) (dist C D), h1, mul_comm (dist A D) (dist B C)]
    · intro h
      have hg : dist A B * (dist C D * Real.sin (∠ B C A) - dist A D * Real.sin (∠ B A C))
          = 0 := by
        linear_combination h * Real.sin (∠ B C A) - eS1 * dist A D
      rcases mul_eq_zero.mp hg with h0 | h0
      · exact absurd h0 (dist_ne_zero.mpr hAB)
      · exact sub_eq_zero.mp h0
  rw [key1, key2, hstep]
  constructor
  · -- From `AB·CD = BC·AD`, exhibit the meeting point on `AC`.
    intro hratio
    have hAB0 : (0:ℝ) < dist A B := dist_pos.mpr hAB
    have hBC0 : (0:ℝ) < dist B C := dist_pos.mpr hBC
    have hAC0 : (0:ℝ) < dist A C := dist_pos.mpr hAC
    have hden : (0:ℝ) < dist A B + dist B C := by linarith
    set r := dist A B / (dist A B + dist B C) with hr
    have hr0 : (0:ℝ) < r := div_pos hAB0 hden
    have hr1 : r < 1 := by
      rw [hr, div_lt_one hden]
      linarith
    set X := AffineMap.lineMap A C r with hXdef
    have hX : Sbtw ℝ A X C := by
      refine ⟨?_, ?_, ?_⟩
      · rw [← mem_segment_iff_wbtw, segment_eq_image_lineMap]
        exact ⟨r, ⟨hr0.le, hr1.le⟩, rfl⟩
      · intro h
        have hd0 := dist_lineMap_left A C r
        rw [← hXdef, h, dist_self, Real.norm_of_nonneg hr0.le] at hd0
        exact mul_ne_zero hr0.ne' hAC0.ne' hd0.symm
      · intro h
        have hd0 := dist_lineMap_right A C r
        rw [← hXdef, h, dist_self, Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ 1 - r)] at hd0
        have h1r : (1:ℝ) - r ≠ 0 := by linarith
        exact mul_ne_zero h1r hAC0.ne' hd0.symm
    have hdAX : dist A X = r * dist A C := by
      rw [hXdef, dist_comm, dist_lineMap_left, Real.norm_of_nonneg hr0.le]
    have hdXC : dist X C = (1 - r) * dist A C := by
      rw [hXdef, dist_lineMap_right, Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ 1 - r)]
    refine ⟨X, hX, ?_, ?_⟩
    · apply bisect_of_dist_mul_dist hX hncolABC
      rw [hdAX, hdXC, hr]
      field_simp [hden.ne']
      ring
    · apply bisect_of_dist_mul_dist hX hncolADC
      rw [hdAX, hdXC, hr]
      have hratio' : dist A B * dist D C = dist B C * dist A D := by
        rw [dist_comm D C]
        exact hratio
      field_simp [hden.ne']
      linear_combination hratio'
  · -- From a meeting point on `AC`, get `AB·CD = BC·AD`.
    rintro ⟨X, hX, hbB, hbD⟩
    have eB : dist A X * dist B C = dist A B * dist X C :=
      dist_mul_dist_of_bisect hX hncolABC hbB
    have eD : dist A X * dist D C = dist A D * dist X C :=
      dist_mul_dist_of_bisect hX hncolADC hbD
    have hXC0 : dist X C ≠ 0 := dist_ne_zero.mpr hX.2.2
    have hg : dist X C * (dist A B * dist D C - dist A D * dist B C) = 0 := by
      linear_combination -eB * dist D C + eD * dist B C
    rcases mul_eq_zero.mp hg with h0 | h0
    · exact absurd h0 hXC0
    · have h1 := sub_eq_zero.mp h0
      rw [show dist C D = dist D C from dist_comm C D, h1, mul_comm (dist A D) (dist B C)]

end Imo2003P4
