/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 2012, Problem 5

Let P be a point in the plane of △ABC, and γ a line through P. Let A′, B′, C′
be the points where the reflections of lines PA, PB, PC with respect to γ
intersect lines BC, CA, AB respectively. Prove that A′, B′, C′ are collinear.
-/

namespace Usa2012P5

/-- The Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- The two-dimensional cross product (determinant) of two plane vectors,
`cross u w = u₀ w₁ - u₁ w₀`. It vanishes iff `u` and `w` are parallel. -/
def cross (u w : Pt) : ℝ := u 0 * w 1 - u 1 * w 0

/-- The dot product of two plane vectors, written in coordinates. -/
def dot (u w : Pt) : ℝ := u 0 * w 0 + u 1 * w 1

/-- The reflection of the point `X` in the line through `P` with direction `v`,
given by the formula `P + 2 • proj_v (X - P) - (X - P)`. -/
noncomputable def reflect (P v X : Pt) : Pt :=
  P + (2 * dot (X - P) v / dot v v) • v - (X - P)

snip begin

/-!
### Proof outline

We prove the theorem by a direct computation in Cartesian coordinates.  The
line γ is described by a nonzero direction vector `v` (so γ is the line
through `P` parallel to `v`), and we work with the following relative data:
for `X ∈ {A, B, C}` let `qX = reflect P v X - P` be the direction of the
reflection of the line `PX` in γ, and set

* `dA = cross qA (C - B)`, `dB = cross qB (A - C)`, `dC = cross qC (B - A)`
  (nonvanishing of these is exactly the hypothesis that the reflected lines
  meet the side lines `BC`, `CA`, `AB` in a single point), and
* `nA = cross (B - P) (C - B)`, `nB = cross (C - P) (A - C)`,
  `nC = cross (A - P) (B - A)`.

Writing `A' = P + sA • qA` etc., the incidences `A' ∈ BC`, `B' ∈ CA`,
`C' ∈ AB` become the linear constraints `sA * dA = nA` etc.  The key
algebraic fact (`key_identity`) is that `dA + dB + dC = 0` — this is where the
reflection enters.  Since `sX = nX / dX`, the collinearity determinant
`cross (B' - A') (C' - A')` simplifies, using `cross (qB) (qC) = -nA` etc.
(reflection has determinant `-1`), to

  `-(nA * sB * sC + nB * sC * sA + nC * sA * sB)
    = -(nA * nB * nC) * (dA + dB + dC) / (dA * dB * dC) = 0`. -/

/-- The squared length of a nonzero plane vector is nonzero. -/
lemma dot_self_ne_zero {v : Pt} (hv : v ≠ 0) : dot v v ≠ 0 := by
  simp only [dot]
  intro h
  obtain ⟨e0, e1⟩ :=
    (add_eq_zero_iff_of_nonneg (mul_self_nonneg (v 0)) (mul_self_nonneg (v 1))).mp h
  have z0 : v 0 = 0 := mul_self_eq_zero.mp e0
  have z1 : v 1 = 0 := mul_self_eq_zero.mp e1
  apply hv
  rw [WithLp.ext_iff, funext_iff, Fin.forall_fin_two]
  exact ⟨by simpa using z0, by simpa using z1⟩

/-- Points on the line through `Y` and `Z` are parametrized by `ℝ`. -/
lemma eq_smul_add_of_mem_line {X Y Z : Pt} (h : X ∈ line[ℝ, Y, Z]) :
    ∃ r : ℝ, X = r • (Z - Y) + Y :=
  let ⟨r, hr⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp h
  ⟨r, hr ▸ AffineMap.lineMap_apply_module' Y Z r⟩

/-- Eliminating `X` and `t` from the two parametrizations of a point `X` that
lies both on the line through `P` with direction `q` and on the line `BC`. -/
lemma mul_cross_of_eq_smul_add {X B C P q : Pt} {s t : ℝ}
    (h1 : X = s • q + P) (h2 : X = t • (C - B) + B) :
    s * cross q (C - B) = cross (B - P) (C - B) := by
  have e1 := congrArg (fun X : Pt => X 0) h1
  have e2 := congrArg (fun X : Pt => X 1) h1
  have f1 := congrArg (fun X : Pt => X 0) h2
  have f2 := congrArg (fun X : Pt => X 1) h2
  simp only [cross, WithLp.ofLp_add, WithLp.ofLp_sub, WithLp.ofLp_smul, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 f1 f2 ⊢
  linear_combination -(C 1 - B 1) * e1 + (C 1 - B 1) * f1 + (C 0 - B 0) * e2 -
    (C 0 - B 0) * f2

/-- The heart of the proof: the three cross products of the reflected
directions with the side directions sum to zero.  Geometrically, reflection in
γ is a symmetric linear map of trace `0` (and determinant `-1`), which is
exactly what makes this cyclic sum vanish. -/
lemma key_identity (A B C P v : Pt) (hv : v ≠ 0) :
    cross (reflect P v A - P) (C - B) + cross (reflect P v B - P) (A - C) +
    cross (reflect P v C - P) (B - A) = 0 := by
  have hN : dot v v ≠ 0 := dot_self_ne_zero hv
  simp only [cross, dot, reflect, WithLp.ofLp_add, WithLp.ofLp_sub, WithLp.ofLp_smul,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at ⊢
  rw [show v 0 * v 0 + v 1 * v 1 = dot v v from rfl] at ⊢
  field_simp [hN]
  rw [show dot v v = v 0 * v 0 + v 1 * v 1 from rfl] at ⊢
  ring

/-- The vanishing of the determinant is a collinearity criterion. -/
lemma collinear_of_cross {X Y Z : Pt} (h : cross (Y - X) (Z - X) = 0) :
    Collinear ℝ ({X, Y, Z} : Set Pt) := by
  by_cases hYX : Y = X
  · rw [hYX, Set.insert_idem]
    exact collinear_pair ℝ X Z
  rw [collinear_iff_of_mem (Set.mem_insert X {Y, Z})]
  refine ⟨Y - X, fun p hp => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  have hu : Y - X ≠ 0 := sub_ne_zero.mpr hYX
  have h' := h
  simp only [cross, WithLp.ofLp_sub, Pi.sub_apply] at h'
  -- h' : (Y 0 - X 0) * (Z 1 - X 1) - (Y 1 - X 1) * (Z 0 - X 0) = 0
  have hcomp : (Y 0 - X 0) ≠ 0 ∨ (Y 1 - X 1) ≠ 0 := by
    by_contra hc
    push Not at hc
    apply hu
    rw [WithLp.ext_iff, funext_iff, Fin.forall_fin_two]
    exact ⟨by simpa using hc.1, by simpa using hc.2⟩
  rcases hcomp with h0 | h1
  · rcases hp with rfl | rfl | hpZ
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · rw [hpZ]
      refine ⟨(Z 0 - X 0) / (Y 0 - X 0), ?_⟩
      have hvec : ((Z 0 - X 0) / (Y 0 - X 0)) • (Y - X) = Z - X := by
        rw [WithLp.ext_iff, funext_iff, Fin.forall_fin_two]
        simp only [WithLp.ofLp_smul, WithLp.ofLp_sub, Pi.smul_apply, Pi.sub_apply,
          smul_eq_mul]
        refine ⟨div_mul_cancel₀ _ h0, ?_⟩
        field_simp [h0]
        linear_combination -h'
      rw [hvec]
      simp
  · rcases hp with rfl | rfl | hpZ
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · rw [hpZ]
      refine ⟨(Z 1 - X 1) / (Y 1 - X 1), ?_⟩
      have hvec : ((Z 1 - X 1) / (Y 1 - X 1)) • (Y - X) = Z - X := by
        rw [WithLp.ext_iff, funext_iff, Fin.forall_fin_two]
        simp only [WithLp.ofLp_smul, WithLp.ofLp_sub, Pi.smul_apply, Pi.sub_apply,
          smul_eq_mul]
        refine ⟨?_, div_mul_cancel₀ _ h1⟩
        field_simp [h1]
        linear_combination h'
      rw [hvec]
      simp

snip end

problem usa2012_p5
    {A B C P : Pt} {v : Pt} (hv : v ≠ 0)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Pt))
    {A' B' C' : Pt}
    (hdA : cross (reflect P v A - P) (C - B) ≠ 0)
    (hdB : cross (reflect P v B - P) (A - C) ≠ 0)
    (hdC : cross (reflect P v C - P) (B - A) ≠ 0)
    (hA₁ : A' ∈ line[ℝ, B, C]) (hA₂ : A' ∈ line[ℝ, P, reflect P v A])
    (hB₁ : B' ∈ line[ℝ, C, A]) (hB₂ : B' ∈ line[ℝ, P, reflect P v B])
    (hC₁ : C' ∈ line[ℝ, A, B]) (hC₂ : C' ∈ line[ℝ, P, reflect P v C]) :
    Collinear ℝ ({A', B', C'} : Set Pt) := by
  -- Parametrize the three intersection points on their respective lines.
  obtain ⟨sA, hsA⟩ := eq_smul_add_of_mem_line hA₂
  obtain ⟨tA, htA⟩ := eq_smul_add_of_mem_line hA₁
  obtain ⟨sB, hsB⟩ := eq_smul_add_of_mem_line hB₂
  obtain ⟨tB, htB⟩ := eq_smul_add_of_mem_line hB₁
  obtain ⟨sC, hsC⟩ := eq_smul_add_of_mem_line hC₂
  obtain ⟨tC, htC⟩ := eq_smul_add_of_mem_line hC₁
  -- The side-line incidences become the constraints `sX * dX = nX`.
  have hAcon : sA * cross (reflect P v A - P) (C - B) = cross (B - P) (C - B) :=
    mul_cross_of_eq_smul_add hsA htA
  have hBcon : sB * cross (reflect P v B - P) (A - C) = cross (C - P) (A - C) :=
    mul_cross_of_eq_smul_add hsB htB
  have hCcon : sC * cross (reflect P v C - P) (B - A) = cross (A - P) (B - A) :=
    mul_cross_of_eq_smul_add hsC htC
  have hsA' : sA = cross (B - P) (C - B) / cross (reflect P v A - P) (C - B) :=
    (eq_div_iff_mul_eq hdA).mpr hAcon
  have hsB' : sB = cross (C - P) (A - C) / cross (reflect P v B - P) (A - C) :=
    (eq_div_iff_mul_eq hdB).mpr hBcon
  have hsC' : sC = cross (A - P) (B - A) / cross (reflect P v C - P) (B - A) :=
    (eq_div_iff_mul_eq hdC).mpr hCcon
  have hkey := key_identity A B C P v hv
  apply collinear_of_cross
  -- The collinearity determinant reduces to a monomial in the `sX` and `nX`.
  have expand : cross (B' - A') (C' - A') =
      -(cross (B - P) (C - B) * (sB * sC) + cross (C - P) (A - C) * (sC * sA) +
        cross (A - P) (B - A) * (sA * sB)) := by
    rw [hsA, hsB, hsC]
    have hN : dot v v ≠ 0 := dot_self_ne_zero hv
    simp only [cross, dot, reflect, WithLp.ofLp_add, WithLp.ofLp_sub, WithLp.ofLp_smul,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at ⊢
    rw [show v 0 * v 0 + v 1 * v 1 = dot v v from rfl] at ⊢
    field_simp [hN]
    rw [show dot v v = v 0 * v 0 + v 1 * v 1 from rfl] at ⊢
    ring
  rw [expand]
  -- The remaining expression vanishes since `dA + dB + dC = 0`.
  have hG : cross (B - P) (C - B) * (sB * sC) + cross (C - P) (A - C) * (sC * sA) +
      cross (A - P) (B - A) * (sA * sB) = 0 := by
    have hd : cross (reflect P v A - P) (C - B) * cross (reflect P v B - P) (A - C) *
        cross (reflect P v C - P) (B - A) ≠ 0 := mul_ne_zero (mul_ne_zero hdA hdB) hdC
    have big : (cross (reflect P v A - P) (C - B) * cross (reflect P v B - P) (A - C) *
        cross (reflect P v C - P) (B - A)) *
        (cross (B - P) (C - B) * (sB * sC) + cross (C - P) (A - C) * (sC * sA) +
         cross (A - P) (B - A) * (sA * sB)) =
        cross (B - P) (C - B) * cross (C - P) (A - C) * cross (A - P) (B - A) *
        (cross (reflect P v A - P) (C - B) + cross (reflect P v B - P) (A - C) +
         cross (reflect P v C - P) (B - A)) := by
      rw [hsA', hsB', hsC']
      field_simp [hdA, hdB, hdC]
    rw [hkey, mul_zero] at big
    exact (mul_eq_zero.mp big).resolve_left hd
  rw [hG, neg_zero]

end Usa2012P5
