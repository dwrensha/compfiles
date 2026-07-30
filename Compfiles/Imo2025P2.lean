/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.Convex.BetweenList
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.MongePoint
public import Mathlib.Geometry.Euclidean.Sphere.Tangent
public import ProblemExtraction

@[expose] public section

set_option maxHeartbeats 600000

problem_file {
  tags := [.Geometry]
  problemImportedFrom :=
    "https://github.com/jsm28/IMOLean/blob/main/IMO/IMO2025P2.lean"
}

/-!
# International Mathematical Olympiad 2025, Problem 2

Let Ω and Γ be circles with centres M and N, respectively, such that
the radius of Ω is less than the radius of Γ. Suppose Ω and Γ intersect
at two distinct points A and B. Line MN intersects Ω at C and Γ at D,
so that C, M, N, D lie on MN in that order. Let P be the circumcentre
of triangle ACD. Line AP meets Ω again at E ≠ A and meets Γ again at
F ≠ A. Let H be the orthocentre of triangle PMN.

Prove that the line through H parallel to AP is tangent to the circumcircle
of triangle BEF.
-/

open scoped Real
open Affine EuclideanGeometry Module
open RealInnerProductSpace

namespace Imo2025P2

variable {V Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt] [Fact (finrank ℝ V = 2)]

snip begin

noncomputable section

/-- Inner product in `EuclideanSpace ℝ (Fin 2)` in coordinates. -/
lemma inner_e2 (x y : EuclideanSpace ℝ (Fin 2)) : ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, RCLike.conj_to_real, Fin.sum_univ_two,
    mul_comm]

/-- Distance in `EuclideanSpace ℝ (Fin 2)` in coordinates. -/
lemma dist_e2 (x y : EuclideanSpace ℝ (Fin 2)) :
    dist x y = √((x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2) := by
  rw [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs,
    sq_abs, sq_abs, PiLp.sub_apply, PiLp.sub_apply]

/-- Rotation by 90 degrees in the plane. -/
def jrot (v : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) := !₂[-v 1, v 0]

lemma jrot_zero (v : EuclideanSpace ℝ (Fin 2)) : jrot v 0 = -v 1 := rfl
lemma jrot_one (v : EuclideanSpace ℝ (Fin 2)) : jrot v 1 = v 0 := rfl

/-- The rotation is orthogonal to the original vector. -/
lemma inner_jrot_self (v : EuclideanSpace ℝ (Fin 2)) : ⟪v, jrot v⟫ = 0 := by
  simp only [inner_e2, jrot_zero, jrot_one]
  ring

/-- The rotation preserves the inner product with itself. -/
lemma inner_jrot_jrot (v : EuclideanSpace ℝ (Fin 2)) : ⟪jrot v, jrot v⟫ = ⟪v, v⟫ := by
  simp only [inner_e2, jrot_zero, jrot_one]
  ring

/-!
## The coordinate setup

The proof is by coordinates.  We use an orthonormal coordinate system whose
x-axis is the line `MN`.  In these coordinates:

* `M = (mx, 0)`, `N = (nx, 0)`, `C = (c, 0)`, `D = (e, 0)` with
  `c < mx < nx < e` (from the `Sbtw` hypothesis),
* `A = (a, b)` and `B = (a, -b)` with `b ≠ 0` (the two intersection points of
  the circles are reflections of each other in the line `MN`).

The equidistance of `M` from `A` and `C` (both on `Ω`) and of `N` from `A`
and `D` (both on `Γ`) determines
`mx = (a²+b²-c²)/(2(a-c))` and `nx = (a²+b²-e²)/(2(a-e))`, after which every
remaining point has rational coordinates in `a b c e` and all the required
identities are plain rational identities, verified in `algebra_core` below.
The tangency point is `T = M + N - A` (so that `AMTN` is a parallelogram);
compare the remark in Evan Chen's solution notes that `AMTN` is a
parallelogram.
-/

/-- The x-coordinate of the circumcenter `P` of `ACD`. -/
def coordPx (c e : ℝ) : ℝ := (c + e) / 2

/-- The y-coordinate of the circumcenter `P` of `ACD`. -/
def coordPy (a b c e : ℝ) : ℝ := (a ^ 2 - a * c - a * e + b ^ 2 + c * e) / (2 * b)

/-- The x-coordinate of the direction `u = P - A` of the line `AP`. -/
def coordUx (a c e : ℝ) : ℝ := (c + e) / 2 - a

/-- The y-coordinate of the direction `u = P - A` of the line `AP`. -/
def coordUy (a b c e : ℝ) : ℝ := (a ^ 2 - a * c - a * e - b ^ 2 + c * e) / (2 * b)

/-- The parameter `t` with `E = A + t • u`. -/
def coordTE (a b c e mx : ℝ) : ℝ :=
  -2 * ((a - mx) * coordUx a c e + b * coordUy a b c e) /
    (coordUx a c e ^ 2 + coordUy a b c e ^ 2)

/-- The parameter `t` with `F = A + t • u`. -/
def coordTF (a b c e nx : ℝ) : ℝ :=
  -2 * ((a - nx) * coordUx a c e + b * coordUy a b c e) /
    (coordUx a c e ^ 2 + coordUy a b c e ^ 2)

/-- The x-coordinate of `E`. -/
def coordEx (a b c e mx : ℝ) : ℝ := a + coordTE a b c e mx * coordUx a c e

/-- The y-coordinate of `E`. -/
def coordEy (a b c e mx : ℝ) : ℝ := b + coordTE a b c e mx * coordUy a b c e

/-- The x-coordinate of `F`. -/
def coordFx (a b c e nx : ℝ) : ℝ := a + coordTF a b c e nx * coordUx a c e

/-- The y-coordinate of `F`. -/
def coordFy (a b c e nx : ℝ) : ℝ := b + coordTF a b c e nx * coordUy a b c e

/-- The x-coordinate of the orthocenter `H` of `PMN`. -/
def coordHx (c e : ℝ) : ℝ := (c + e) / 2

/-- The y-coordinate of the orthocenter `H` of `PMN`. -/
def coordHy (a b c e : ℝ) : ℝ :=
  -b * (a ^ 2 - a * c - a * e + b ^ 2 + c * e) / (2 * (a - c) * (a - e))

/-- The x-coordinate of the circumcenter `O` of `BEF`. -/
def coordOx (a b c e : ℝ) : ℝ :=
  (2 * a ^ 3 - a ^ 2 * c - a ^ 2 * e + 2 * a * b ^ 2 - a * c ^ 2 - a * e ^ 2 - b ^ 2 * c -
    b ^ 2 * e + c ^ 2 * e + c * e ^ 2) / (4 * (a - c) * (a - e))

/-- The y-coordinate of the circumcenter `O` of `BEF`. -/
def coordOy (a b c e : ℝ) : ℝ := b * (c - e) ^ 2 / (4 * (a - c) * (a - e))

/-- The x-coordinate of the tangency point `T = M + N - A`. -/
def coordTx (a mx nx : ℝ) : ℝ := mx + nx - a

/-- The y-coordinate of the tangency point `T = M + N - A`. -/
def coordTy (b : ℝ) : ℝ := -b

/-- The scalar `lam` with `T - H = lam • u`. -/
def coordLam (a b c e : ℝ) : ℝ := -b ^ 2 / ((a - c) * (a - e))

set_option maxRecDepth 8000

/-- The algebraic heart of the proof: all the required coordinate identities
are rational identities in `a b c e mx nx`. -/
theorem algebra_core {a b c e mx nx : ℝ}
    (hb : b ≠ 0) (hac : a ≠ c) (hae : a ≠ e)
    (hMc : (a - mx) ^ 2 + b ^ 2 = (c - mx) ^ 2)
    (hNe : (a - nx) ^ 2 + b ^ 2 = (e - nx) ^ 2)
    (hmn : mx < nx) (hrR : mx - c < e - nx) :
    -- `mx` and `nx` are determined.
    mx = (a ^ 2 + b ^ 2 - c ^ 2) / (2 * (a - c)) ∧
    nx = (a ^ 2 + b ^ 2 - e ^ 2) / (2 * (a - e)) ∧
    -- `u ≠ 0`.
    coordUx a c e ^ 2 + coordUy a b c e ^ 2 ≠ 0 ∧
    -- `ux ≠ 0` (used for the non-collinearity of `B E F`).
    coordUx a c e ≠ 0 ∧
    -- `B, E, F` are not collinear (a determinant computation).
    (coordEx a b c e mx - a) * (coordFy a b c e nx + b) -
      (coordEy a b c e mx + b) * (coordFx a b c e nx - a) ≠ 0 ∧
    -- `T - H = lam • u`.
    coordTx a mx nx - coordHx c e = coordLam a b c e * coordUx a c e ∧
    coordTy b - coordHy a b c e = coordLam a b c e * coordUy a b c e ∧
    -- `u ⊥ (T - O)`.
    coordUx a c e * (coordTx a mx nx - coordOx a b c e) +
      coordUy a b c e * (coordTy b - coordOy a b c e) = 0 ∧
    -- `dist T O = dist B O`.
    (coordTx a mx nx - coordOx a b c e) ^ 2 + (coordTy b - coordOy a b c e) ^ 2 =
      (a - coordOx a b c e) ^ 2 + (-b - coordOy a b c e) ^ 2 ∧
    -- `dist E O = dist B O`.
    (coordEx a b c e mx - coordOx a b c e) ^ 2 + (coordEy a b c e mx - coordOy a b c e) ^ 2 =
      (a - coordOx a b c e) ^ 2 + (-b - coordOy a b c e) ^ 2 ∧
    -- `dist F O = dist B O`.
    (coordFx a b c e nx - coordOx a b c e) ^ 2 + (coordFy a b c e nx - coordOy a b c e) ^ 2 =
      (a - coordOx a b c e) ^ 2 + (-b - coordOy a b c e) ^ 2 := by
  have hac' : a - c ≠ 0 := sub_ne_zero.mpr hac
  have hae' : a - e ≠ 0 := sub_ne_zero.mpr hae
  have hb2pos : 0 < b ^ 2 := sq_pos_of_ne_zero hb
  have hsq1pos : 0 < (a - c) ^ 2 + b ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg _) hb2pos
  have hsq2pos : 0 < (a - e) ^ 2 + b ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg _) hb2pos
  have hsq1 : ((a - c) ^ 2 + b ^ 2) ≠ 0 := ne_of_gt hsq1pos
  have hsq2 : ((a - e) ^ 2 + b ^ 2) ≠ 0 := ne_of_gt hsq2pos
  -- `mx` and `nx` are determined by the equidistance constraints.
  have h1 : 2 * mx * (a - c) = a ^ 2 + b ^ 2 - c ^ 2 := by linear_combination -hMc
  have h2 : 2 * nx * (a - e) = a ^ 2 + b ^ 2 - e ^ 2 := by linear_combination -hNe
  have hmx : mx = (a ^ 2 + b ^ 2 - c ^ 2) / (2 * (a - c)) := by
    rw [eq_div_iff_mul_eq (mul_ne_zero two_ne_zero hac')]
    linear_combination h1
  have hnx : nx = (a ^ 2 + b ^ 2 - e ^ 2) / (2 * (a - e)) := by
    rw [eq_div_iff_mul_eq (mul_ne_zero two_ne_zero hae')]
    linear_combination h2
  -- `|u|²` in factored form.
  have hu2e_id : ((c + e) / 2 - a) ^ 2 + ((a ^ 2 - a * c - a * e - b ^ 2 + c * e) / (2 * b)) ^ 2
      = ((a - c) ^ 2 + b ^ 2) * ((a - e) ^ 2 + b ^ 2) / (4 * b ^ 2) := by
    field_simp [hb, hac', hae']
    ring
  have hu2 : coordUx a c e ^ 2 + coordUy a b c e ^ 2 ≠ 0 := by
    unfold coordUx coordUy
    rw [hu2e_id]
    exact ne_of_gt (by positivity)
  -- The radius difference `r - R` factors; since `r < R` and `Py ≠ 0` we get `ux ≠ 0`.
  have hrR_id : (mx - c) - (e - nx)
      = (2 * a - c - e) * (a ^ 2 - a * c - a * e + b ^ 2 + c * e) / (2 * (a - c) * (a - e)) := by
    rw [hmx, hnx]
    field_simp [hb, hac', hae']
    ring
  have hux : coordUx a c e ≠ 0 := by
    intro hz
    have h2a : 2 * a - c - e = 0 := by
      have hz' : (c + e) / 2 - a = 0 := hz
      linarith
    have hr0 : (mx - c) - (e - nx) = 0 := by
      rw [hrR_id, h2a]
      simp
    linarith
  -- The determinant in factored form.
  have hdet_id : (coordEx a b c e mx - a) * (coordFy a b c e nx + b) -
        (coordEy a b c e mx + b) * (coordFx a b c e nx - a)
      = -4 * b * (nx - mx) * coordUx a c e ^ 2 / (coordUx a c e ^ 2 + coordUy a b c e ^ 2) := by
    unfold coordEx coordEy coordFx coordFy coordTE coordTF
    field_simp [hu2, hb, hac', hae']
    ring
  have hdet : (coordEx a b c e mx - a) * (coordFy a b c e nx + b) -
        (coordEy a b c e mx + b) * (coordFx a b c e nx - a) ≠ 0 := by
    rw [hdet_id]
    exact div_ne_zero
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr four_ne_zero) hb)
        (sub_ne_zero.mpr (ne_of_gt hmn))) (pow_ne_zero 2 hux)) hu2
  refine ⟨hmx, hnx, hu2, hux, hdet, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `T - H = lam • u`, x-component.
    unfold coordTx coordHx coordLam coordUx
    rw [hmx, hnx]
    field_simp [hb, hac', hae']
    ring
  · -- `T - H = lam • u`, y-component.
    unfold coordTy coordHy coordLam coordUy
    field_simp [hb, hac', hae']
    ring
  · -- `u ⊥ (T - O)`.
    unfold coordUx coordUy coordTx coordTy coordOx coordOy
    rw [hmx, hnx]
    field_simp [hb, hac', hae']
    ring
  · -- `dist T O = dist B O`.
    unfold coordTx coordTy coordOx coordOy
    rw [hmx, hnx]
    field_simp [hb, hac', hae']
    ring
  · -- `dist E O = dist B O`.
    -- Factor the quadratic in `coordTE` first: with `K = (a - mx) * ux + b * uy`,
    -- `G = ux * (a - Ox) + uy * (b - Oy)` and `D = ux ^ 2 + uy ^ 2`, the identity
    -- is `t * (t * D + 2 * G) = 4 * b * Oy` at `t = -2 * K / D`, i.e. `K * (K - G) =
    -- b * Oy * D`.  Proving that crux directly keeps `ring` off the huge
    -- denominator-clearing normal form.
    have hcrux : ((a - mx) * coordUx a c e + b * coordUy a b c e) *
          (coordUx a c e * (coordOx a b c e - mx) + coordUy a b c e * coordOy a b c e)
        = b * coordOy a b c e * (coordUx a c e ^ 2 + coordUy a b c e ^ 2) := by
      unfold coordUx coordUy coordOx coordOy
      rw [hmx]
      field_simp [hb, hac', hae']
      ring
    have hfac : (coordEx a b c e mx - coordOx a b c e) ^ 2 +
          (coordEy a b c e mx - coordOy a b c e) ^ 2 -
          ((a - coordOx a b c e) ^ 2 + (-b - coordOy a b c e) ^ 2)
        = coordTE a b c e mx * (coordTE a b c e mx * (coordUx a c e ^ 2 + coordUy a b c e ^ 2)
            + 2 * (coordUx a c e * (a - coordOx a b c e) +
              coordUy a b c e * (b - coordOy a b c e)))
          - 4 * b * coordOy a b c e := by
      unfold coordEx coordEy
      ring
    have hexp : coordTE a b c e mx * (coordTE a b c e mx * (coordUx a c e ^ 2 + coordUy a b c e ^ 2)
          + 2 * (coordUx a c e * (a - coordOx a b c e) + coordUy a b c e * (b - coordOy a b c e)))
        - 4 * b * coordOy a b c e = 0 := by
      unfold coordTE
      field_simp [hu2]
      linear_combination 4 * hcrux
    linear_combination hfac + hexp
  · -- `dist F O = dist B O`.
    have hcrux : ((a - nx) * coordUx a c e + b * coordUy a b c e) *
          (coordUx a c e * (coordOx a b c e - nx) + coordUy a b c e * coordOy a b c e)
        = b * coordOy a b c e * (coordUx a c e ^ 2 + coordUy a b c e ^ 2) := by
      unfold coordUx coordUy coordOx coordOy
      rw [hnx]
      field_simp [hb, hac', hae']
      ring
    have hfac : (coordFx a b c e nx - coordOx a b c e) ^ 2 +
          (coordFy a b c e nx - coordOy a b c e) ^ 2 -
          ((a - coordOx a b c e) ^ 2 + (-b - coordOy a b c e) ^ 2)
        = coordTF a b c e nx * (coordTF a b c e nx * (coordUx a c e ^ 2 + coordUy a b c e ^ 2)
            + 2 * (coordUx a c e * (a - coordOx a b c e) +
              coordUy a b c e * (b - coordOy a b c e)))
          - 4 * b * coordOy a b c e := by
      unfold coordFx coordFy
      ring
    have hexp : coordTF a b c e nx * (coordTF a b c e nx * (coordUx a c e ^ 2 + coordUy a b c e ^ 2)
          + 2 * (coordUx a c e * (a - coordOx a b c e) + coordUy a b c e * (b - coordOy a b c e)))
        - 4 * b * coordOy a b c e = 0 := by
      unfold coordTF
      field_simp [hu2]
      linear_combination 4 * hcrux
    linear_combination hfac + hexp

/-- The nonzero root of the quadratic giving the second intersection of a line
through a circle point with the circle. -/
lemma t_eq_of_quadratic {t k1 k2 : ℝ} (hu2 : k2 ≠ 0)
    (h : t * (t * k2 + 2 * k1) = 0) (ht : t ≠ 0) : t = -2 * k1 / k2 := by
  have h4 : t * k2 + 2 * k1 = 0 := by
    rcases mul_eq_zero.1 h with h5 | h5
    · exact absurd h5 ht
    · exact h5
  rw [eq_div_iff_mul_eq hu2, neg_mul]
  exact (neg_eq_of_add_eq_zero_left h4).symm

/-- `coordTE` at `mx = 0` in the form produced by `t_eq_of_quadratic`. -/
lemma coordTE_zero (a b c e : ℝ) :
    coordTE a b c e 0 = -2 * (a * coordUx a c e + b * coordUy a b c e) /
      (coordUx a c e ^ 2 + coordUy a b c e ^ 2) := by
  unfold coordTE
  congr 1
  congr 1
  rw [sub_zero]

/-- The algebraic identity behind the second altitude condition for `H`. -/
lemma horth2_algebra {a b c e : ℝ} (hb : b ≠ 0) (hac : a ≠ c) (hae : a ≠ e)
    (hMc : a ^ 2 + b ^ 2 = c ^ 2) :
    ((c + e) / 2 - (a ^ 2 + b ^ 2 - e ^ 2) / (2 * (a - e))) * ((c + e) / 2) +
      coordPy a b c e * coordHy a b c e = 0 := by
  have hac' : a - c ≠ 0 := sub_ne_zero.mpr hac
  have hae' : a - e ≠ 0 := sub_ne_zero.mpr hae
  unfold coordPy coordHy
  field_simp [hb, hac', hae']
  linear_combination -(a ^ 2 - a * c - a * e + b ^ 2 + c * e) * hMc

/-- The 2-dimensional coordinate version of the problem. -/
theorem imo2025_p2_coord {M N A B C D P E F H : EuclideanSpace ℝ (Fin 2)} {Ω Γ : Sphere (EuclideanSpace ℝ (Fin 2))}
    (Ω_center_eq_M : Ω.center = M) (Γ_center_eq_N : Γ.center = N)
    (Ω_radius_lt_Γ_radius : Ω.radius < Γ.radius)
    (A_mem_inter : A ∈ (Ω ∩ Γ : Set (EuclideanSpace ℝ (Fin 2))))
    (B_mem_inter : B ∈ (Ω ∩ Γ : Set (EuclideanSpace ℝ (Fin 2))))
    (A_ne_B : A ≠ B) (M_ne_N : M ≠ N)
    (C_mem_inter : C ∈ (line[ℝ, M, N] ∩ Ω : Set (EuclideanSpace ℝ (Fin 2))))
    (D_mem_inter : D ∈ (line[ℝ, M, N] ∩ Γ : Set (EuclideanSpace ℝ (Fin 2))))
    (sbtw_C_M_N_D : [C, M, N, D].Sbtw ℝ)
    (affineIndependent_ACD : AffineIndependent ℝ ![A, C, D])
    (P_eq_circumcenter :
      P = (⟨_, affineIndependent_ACD⟩ : Triangle ℝ (EuclideanSpace ℝ (Fin 2))).circumcenter)
    (E_mem_inter : E ∈ (line[ℝ, A, P] ∩ Ω : Set (EuclideanSpace ℝ (Fin 2)))) (E_ne_A : E ≠ A)
    (F_mem_inter : F ∈ (line[ℝ, A, P] ∩ Γ : Set (EuclideanSpace ℝ (Fin 2)))) (F_ne_A : F ≠ A)
    (affineIndependent_PMN : AffineIndependent ℝ ![P, M, N])
    (H_eq_orthocenter :
      H = Triangle.orthocenter (⟨_, affineIndependent_PMN⟩ : Triangle ℝ (EuclideanSpace ℝ (Fin 2)))) :
    ∃ affineIndependent_BEF : AffineIndependent ℝ ![B, E, F],
      (⟨_, affineIndependent_BEF⟩ : Triangle ℝ (EuclideanSpace ℝ (Fin 2))).circumsphere.IsTangent
        (AffineSubspace.mk' H line[ℝ, A, P].direction) := by
  obtain ⟨hAΩ, hAΓ⟩ := A_mem_inter
  obtain ⟨hBΩ, hBΓ⟩ := B_mem_inter
  obtain ⟨hCMN, hCΩ⟩ := C_mem_inter
  obtain ⟨hDMN, hDΓ⟩ := D_mem_inter
  obtain ⟨hEAP, hEΩ⟩ := E_mem_inter
  obtain ⟨hFAP, hFΓ⟩ := F_mem_inter
  simp only [Ω_center_eq_M] at hAΩ hBΩ hCΩ hEΩ
  simp only [Γ_center_eq_N] at hAΓ hBΓ hDΓ hFΓ
  -- The orthonormal frame along `MN`.
  have hd : 0 < dist M N := dist_pos.mpr M_ne_N
  set d := dist M N with hd_def
  set u : EuclideanSpace ℝ (Fin 2) := d⁻¹ • (N - M) with hu_def
  have hd' : d ≠ 0 := ne_of_gt hd
  have hNM : N - M = d • u := by
    rw [hu_def, smul_smul, mul_inv_cancel₀ hd', one_smul]
  have huu : ⟪u, u⟫ = 1 := by
    rw [hu_def, inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq]
    simp only [RCLike.conj_to_real]
    have h1 : ‖N - M‖ = d := by rw [← dist_eq_norm, dist_comm]
    rw [h1]
    field_simp
  have huJ : ⟪u, jrot u⟫ = 0 := inner_jrot_self u
  have hJu : ⟪jrot u, u⟫ = 0 := inner_eq_zero_symm.1 huJ
  have hJuJ : ⟪jrot u, jrot u⟫ = 1 := by rw [inner_jrot_jrot, huu]
  -- Coordinate vector constructor.
  set mkv : ℝ → ℝ → EuclideanSpace ℝ (Fin 2) := fun x y => x • u + y • jrot u with hmkv
  have inner_mkv (x₁ y₁ x₂ y₂ : ℝ) : ⟪mkv x₁ y₁, mkv x₂ y₂⟫ = x₁ * x₂ + y₁ * y₂ := by
    simp only [hmkv, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      RCLike.conj_to_real, huu, huJ, hJu, hJuJ]
    ring
  have mkv_sub (x₁ y₁ x₂ y₂ : ℝ) : mkv x₁ y₁ - mkv x₂ y₂ = mkv (x₁ - x₂) (y₁ - y₂) := by
    simp only [hmkv, sub_smul]
    abel
  have dist_eq (Q : EuclideanSpace ℝ (Fin 2)) (x₁ y₁ x₂ y₂ : ℝ) :
      dist (Q + mkv x₁ y₁) (Q + mkv x₂ y₂) = √((x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2) := by
    rw [dist_eq_norm]
    have hsub : Q + mkv x₁ y₁ - (Q + mkv x₂ y₂) = mkv x₁ y₁ - mkv x₂ y₂ := by abel
    rw [hsub, mkv_sub, ← Real.sqrt_sq (norm_nonneg _), ← real_inner_self_eq_norm_sq, inner_mkv,
      ← sq, ← sq]
  have eq_zero_of_inner (v : EuclideanSpace ℝ (Fin 2)) (h1 : ⟪v, u⟫ = 0)
      (h2 : ⟪v, jrot u⟫ = 0) : v = 0 := by
    have hu01 : u 0 ^ 2 + u 1 ^ 2 = 1 := by
      have h := huu
      simp only [inner_e2] at h
      nlinarith
    simp only [inner_e2, jrot_zero, jrot_one] at h1 h2
    refine PiLp.ext fun i => ?_
    fin_cases i
    · have h0 : v 0 = (v 0 * u 0 + v 1 * u 1) * u 0 - (v 0 * -u 1 + v 1 * u 0) * u 1 := by
        linear_combination -v 0 * hu01
      rw [h1, h2] at h0
      simpa using h0
    · have h1' : v 1 = (v 0 * u 0 + v 1 * u 1) * u 1 + (v 0 * -u 1 + v 1 * u 0) * u 0 := by
        linear_combination -v 1 * hu01
      rw [h1, h2] at h1'
      simpa using h1'
  have decomp (X : EuclideanSpace ℝ (Fin 2)) :
      X = M + mkv ⟪X - M, u⟫ ⟪X - M, jrot u⟫ := by
    have hv : X - (M + mkv ⟪X - M, u⟫ ⟪X - M, jrot u⟫) = 0 := by
      apply eq_zero_of_inner
      · simp only [sub_add_eq_sub_sub, inner_sub_left, hmkv, inner_smul_left,
          RCLike.conj_to_real, huu, hJu]
        ring
      · simp only [sub_add_eq_sub_sub, inner_sub_left, hmkv, inner_smul_left,
          RCLike.conj_to_real, huJ, hJuJ]
        ring
    rwa [sub_eq_zero] at hv
  -- A variant of `dist_eq` for the distance from a coordinate point to the origin `M`.
  have dist_mkv_left (Q : EuclideanSpace ℝ (Fin 2)) (x y : ℝ) :
      dist (Q + mkv x y) Q = √(x ^ 2 + y ^ 2) := by
    have h : dist (Q + mkv x y) (Q + mkv 0 0) = √((x - 0) ^ 2 + (y - 0) ^ 2) := dist_eq Q x y 0 0
    have hQ : Q + mkv 0 0 = Q := by simp [hmkv]
    rw [hQ] at h
    rw [h]
    congr 1
    ring
  -- Points on the line `MN`.
  have hMmem : M ∈ line[ℝ, M, N] := left_mem_affineSpan_pair ℝ M N
  have hNmem : N ∈ line[ℝ, M, N] := right_mem_affineSpan_pair ℝ M N
  have hMNv : M -ᵥ N = (-d) • u := by
    rw [← neg_vsub_eq_vsub_rev N M, vsub_eq_sub, hNM, neg_smul]
  -- Coordinates of `C`.
  have hCvs : C -ᵥ M ∈ vectorSpan ℝ ({M, N} : Set (EuclideanSpace ℝ (Fin 2))) := by
    have h := AffineSubspace.vsub_mem_direction hCMN hMmem
    rwa [direction_affineSpan] at h
  rw [mem_vectorSpan_pair] at hCvs
  obtain ⟨sC, hsC⟩ := hCvs
  set c := -sC * d with hc_def
  have hCeq : C = M + mkv c 0 := by
    have h1 : C -ᵥ M = c • u := by
      rw [← hsC, hMNv, smul_smul, hc_def]
      congr 1
      ring
    rw [← vsub_vadd C M, h1, vadd_eq_add, add_comm (c • u) M]
    simp [hmkv]
  -- Coordinates of `D`.
  have hDvs : D -ᵥ M ∈ vectorSpan ℝ ({M, N} : Set (EuclideanSpace ℝ (Fin 2))) := by
    have h := AffineSubspace.vsub_mem_direction hDMN hMmem
    rwa [direction_affineSpan] at h
  rw [mem_vectorSpan_pair] at hDvs
  obtain ⟨sD, hsD⟩ := hDvs
  set e := -sD * d with he_def
  have hDeq : D = M + mkv e 0 := by
    have h1 : D -ᵥ M = e • u := by
      rw [← hsD, hMNv, smul_smul, he_def]
      congr 1
      ring
    rw [← vsub_vadd D M, h1, vadd_eq_add, add_comm (e • u) M]
    simp [hmkv]
  -- Coordinates of `N` and `A`.
  have hNeq : N = M + mkv d 0 := by
    rw [show mkv d 0 = d • u by simp [hmkv], ← hNM]
    abel
  set a := ⟪A - M, u⟫ with ha_def
  set b := ⟪A - M, jrot u⟫ with hb_def
  have hAeq : A = M + mkv a b := decomp A
  -- The circle constraints.
  have hdCM : dist C M = √(c ^ 2) := by
    rw [hCeq]
    have h := dist_mkv_left M c 0
    rw [show c ^ 2 + 0 ^ 2 = c ^ 2 by ring] at h
    exact h
  have hdAM : dist A M = √(a ^ 2 + b ^ 2) := by
    rw [hAeq]
    exact dist_mkv_left M a b
  have hdDN : dist D N = √((e - d) ^ 2) := by
    rw [hDeq, hNeq]
    have h := dist_eq M e 0 d 0
    rw [show (e - d) ^ 2 + (0 - 0) ^ 2 = (e - d) ^ 2 by ring] at h
    exact h
  have hdAN : dist A N = √((a - d) ^ 2 + b ^ 2) := by
    rw [hAeq, hNeq]
    have h := dist_eq M a b d 0
    rw [show (a - d) ^ 2 + (b - 0) ^ 2 = (a - d) ^ 2 + b ^ 2 by ring] at h
    exact h
  have hMc : a ^ 2 + b ^ 2 = c ^ 2 := by
    have h1 : dist C M = dist A M := by rw [hCΩ, hAΩ]
    rw [hdCM, hdAM] at h1
    have h2 := (Real.sqrt_inj (sq_nonneg c) (add_nonneg (sq_nonneg a) (sq_nonneg b))).1 h1
    linarith [h2]
  have hNe : (a - d) ^ 2 + b ^ 2 = (e - d) ^ 2 := by
    have h1 : dist D N = dist A N := by rw [hDΓ, hAΓ]
    rw [hdDN, hdAN] at h1
    have h2 := (Real.sqrt_inj (sq_nonneg (e - d)) (add_nonneg (sq_nonneg (a - d))
      (sq_nonneg b))).1 h1
    linarith [h2]
  -- The order constraints from `Sbtw`.
  obtain ⟨hs1, -, -, hs4⟩ := (List.sbtw_four).1 sbtw_C_M_N_D
  obtain ⟨tC, htCI, htCeq⟩ := hs1.mem_image_Ioo
  obtain ⟨tD, htDI, htDeq⟩ := hs4.mem_image_Ioo
  rw [Set.mem_Ioo] at htCI htDI
  have hordC : (1 - tC) * c + tC * d = 0 := by
    have h2 : M - M = (1 - tC) • (C - M) + tC • (N - M) := by
      have h3 : M = (1 - tC) • C + tC • N := by
        rw [← htCeq, AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub]
        module
      rw [h3]
      module
    have hCM : C - M = c • u := by
      rw [hCeq]
      simp [hmkv]
    rw [hCM, hNM] at h2
    have h4 : ((1 - tC) * c + tC * d) • u = 0 := by
      have h5 : (1 - tC) • (c • u) + tC • (d • u) = ((1 - tC) * c + tC * d) • u := by module
      rw [← h5, ← h2]
      simp
    have h6 := congrArg (fun v => ⟪v, u⟫) h4
    simp only [inner_smul_left, RCLike.conj_to_real, huu, inner_zero_left, mul_one] at h6
    linarith [h6]
  have hordD : d = tD * e := by
    have h2 : N - M = (1 - tD) • (M - M) + tD • (D - M) := by
      have h3 : N = (1 - tD) • M + tD • D := by
        rw [← htDeq, AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub]
        module
      rw [h3]
      module
    have hDM : D - M = e • u := by
      rw [hDeq]
      simp [hmkv]
    rw [hDM] at h2
    simp at h2
    have h4 : (tD * e) • u = d • u := by
      have h5 : tD • (e • u) = (tD * e) • u := by module
      rw [← h5, ← h2]
      exact hNM
    have h6 := congrArg (fun v => ⟪v, u⟫) h4
    simp only [inner_smul_left, RCLike.conj_to_real, huu, mul_one] at h6
    linarith [h6]
  have hc_neg : c < 0 := by
    have h1 : 0 < tC := htCI.1
    have h2 : tC < 1 := htCI.2
    have h3 : (1 - tC) * c < 0 := by nlinarith [hordC, mul_pos h1 hd]
    rcases mul_neg_iff.1 h3 with ⟨-, hc⟩ | ⟨h4, -⟩
    · exact hc
    · linarith [h2, h4]
  have he_pos : 0 < e := by
    have h1 : 0 < tD := htDI.1
    have h3 : 0 < tD * e := by linarith [hd, hordD]
    rcases mul_pos_iff.1 h3 with ⟨-, he⟩ | ⟨h4, -⟩
    · exact he
    · linarith [h1, h4]
  have hd_lt_e : d < e := by
    have h1 : 0 < tD := htDI.1
    have h2 : tD < 1 := htDI.2
    have h3 : 0 < (1 - tD) * e := mul_pos (sub_pos.mpr h2) he_pos
    linarith [h3, hordD]
  have hrR : (0 : ℝ) - c < e - d := by
    have h1 : dist C M < dist D N := by rw [hCΩ, hDΓ]; exact Ω_radius_lt_Γ_radius
    rw [hdCM, hdDN, Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, abs_of_neg hc_neg,
      abs_of_pos (sub_pos.mpr hd_lt_e)] at h1
    linarith [h1]
  -- `A` is off the line `MN`.
  have hb : b ≠ 0 := by
    intro hbz
    have hcol : Collinear ℝ ({A, C, D} : Set (EuclideanSpace ℝ (Fin 2))) := by
      rw [collinear_iff_exists_forall_eq_smul_vadd]
      refine ⟨C, u, fun p hp => ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl
      · refine ⟨a - c, ?_⟩
        rw [hAeq, hCeq, hbz]
        simp [hmkv, vadd_eq_add]
        module
      · exact ⟨0, by simp⟩
      · refine ⟨e - c, ?_⟩
        rw [hDeq, hCeq]
        simp [hmkv, vadd_eq_add]
        module
    exact (affineIndependent_iff_not_collinear_set.1 affineIndependent_ACD) hcol
  have hac : a ≠ c := by
    intro h
    rw [h] at hMc
    have h1 : b ^ 2 = 0 := by linarith [hMc]
    exact hb (sq_eq_zero_iff.1 h1)
  have hae : a ≠ e := by
    intro h
    rw [h] at hNe
    have h1 : b ^ 2 = 0 := by linarith [hNe]
    exact hb (sq_eq_zero_iff.1 h1)
  have hac' : a - c ≠ 0 := sub_ne_zero.mpr hac
  have hae' : a - e ≠ 0 := sub_ne_zero.mpr hae
  -- The circumcenter `P` of `ACD`.
  set px := (c + e) / 2 with hpx_def
  set py := coordPy a b c e with hpy_def
  have hPdist : ∀ i : Fin 3, dist (![A, C, D] i) (M + mkv px py) = dist A (M + mkv px py) := by
    intro i
    fin_cases i
    · rfl
    · show dist C (M + mkv px py) = dist A (M + mkv px py)
      rw [hAeq, hCeq, dist_eq M a b px py, dist_eq M c 0 px py]
      congr 1
      rw [hpx_def, hpy_def]
      unfold coordPy
      field_simp [hb]
      ring
    · show dist D (M + mkv px py) = dist A (M + mkv px py)
      rw [hAeq, hDeq, dist_eq M a b px py, dist_eq M e 0 px py]
      congr 1
      rw [hpx_def, hpy_def]
      unfold coordPy
      field_simp [hb]
      ring
  have hPspan : M + mkv px py ∈ affineSpan ℝ
      (Set.range (![A, C, D] : Fin 3 → EuclideanSpace ℝ (Fin 2))) := by
    have htop : affineSpan ℝ (Set.range (![A, C, D] : Fin 3 → EuclideanSpace ℝ (Fin 2))) = ⊤ := by
      refine (AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one
        affineIndependent_ACD).2 ?_
      rw [Fintype.card_fin, finrank_euclideanSpace_fin]
    rw [htop]
    trivial
  have hPeq : P = M + mkv px py := by
    rw [P_eq_circumcenter]
    exact (Simplex.eq_circumcenter_of_dist_eq (⟨_, affineIndependent_ACD⟩ : Triangle ℝ _)
      hPspan hPdist).symm
  -- Apply the algebraic core.
  have hMc0 : (a - 0) ^ 2 + b ^ 2 = (c - 0) ^ 2 := by
    rw [sub_zero, sub_zero]
    exact hMc
  obtain ⟨hmx, hnx, hu2, hux, hdet, hT1, hT2, hperp, hdTO, hdEO, hdFO⟩ :=
    algebra_core (mx := 0) (nx := d) hb hac hae hMc0 hNe hd hrR
  -- The direction of the line `AP`.
  have hPA : P - A = mkv (coordUx a c e) (coordUy a b c e) := by
    rw [hPeq, hAeq]
    have h1 : M + mkv px py - (M + mkv a b) = mkv (px - a) (py - b) := by
      rw [← mkv_sub]
      abel
    rw [h1]
    have hx : px - a = coordUx a c e := rfl
    have hy : py - b = coordUy a b c e := by
      have h2 : coordPy a b c e - b = coordUy a b c e := by
        unfold coordPy coordUy
        field_simp [hb]
        ring
      rwa [hpy_def]
    rw [hx, hy]
  have hAvP : A -ᵥ P = -(P - A) := by
    rw [← neg_vsub_eq_vsub_rev P A, vsub_eq_sub]
  -- The second intersection `E` of line `AP` with `Ω`.
  have hAdirE : E -ᵥ A ∈ (line[ℝ, A, P]).direction :=
    AffineSubspace.vsub_mem_direction hEAP (left_mem_affineSpan_pair ℝ A P)
  rw [direction_affineSpan, mem_vectorSpan_pair] at hAdirE
  obtain ⟨sE, hsE⟩ := hAdirE
  set tE := -sE with htE_def
  have hEeq' : E = A + tE • mkv (coordUx a c e) (coordUy a b c e) := by
    have h1 : E -ᵥ A = tE • mkv (coordUx a c e) (coordUy a b c e) := by
      rw [← hsE, htE_def, ← hPA, hAvP]
      module
    rw [← vsub_vadd E A, h1, vadd_eq_add]
    exact add_comm _ _
  have hEeq : E = M + mkv (a + tE * coordUx a c e) (b + tE * coordUy a b c e) := by
    rw [hEeq', hAeq]
    have h2 : M + mkv a b + tE • mkv (coordUx a c e) (coordUy a b c e) =
        M + mkv (a + tE * coordUx a c e) (b + tE * coordUy a b c e) := by
      simp only [hmkv, smul_add, smul_smul]
      module
    rw [h2]
  have htE0 : tE * (tE * (coordUx a c e ^ 2 + coordUy a b c e ^ 2) +
      2 * (a * coordUx a c e + b * coordUy a b c e)) = 0 := by
    have h1 : dist E M = dist A M := by rw [hEΩ, hAΩ]
    rw [hEeq, dist_mkv_left, hdAM] at h1
    have h3 := (Real.sqrt_inj (add_nonneg (sq_nonneg _) (sq_nonneg _))
      (add_nonneg (sq_nonneg _) (sq_nonneg _))).1 h1
    linear_combination h3
  have htE_ne : tE ≠ 0 := by
    intro hz
    rw [hz, zero_smul, add_zero] at hEeq'
    exact E_ne_A hEeq'
  have htE_val : tE = coordTE a b c e 0 := by
    rw [coordTE_zero]
    exact t_eq_of_quadratic hu2 htE0 htE_ne
  have hEfinal : E = M + mkv (coordEx a b c e 0) (coordEy a b c e 0) := by
    rw [hEeq, htE_val]
    simp only [coordEx, coordEy]
  -- The second intersection `F` of line `AP` with `Γ`.
  have hAdirF : F -ᵥ A ∈ (line[ℝ, A, P]).direction :=
    AffineSubspace.vsub_mem_direction hFAP (left_mem_affineSpan_pair ℝ A P)
  rw [direction_affineSpan, mem_vectorSpan_pair] at hAdirF
  obtain ⟨sF, hsF⟩ := hAdirF
  set tF := -sF with htF_def
  have hFeq' : F = A + tF • mkv (coordUx a c e) (coordUy a b c e) := by
    have h1 : F -ᵥ A = tF • mkv (coordUx a c e) (coordUy a b c e) := by
      rw [← hsF, htF_def, ← hPA, hAvP]
      module
    rw [← vsub_vadd F A, h1, vadd_eq_add]
    exact add_comm _ _
  have hFeq : F = M + mkv (a + tF * coordUx a c e) (b + tF * coordUy a b c e) := by
    rw [hFeq', hAeq]
    have h2 : M + mkv a b + tF • mkv (coordUx a c e) (coordUy a b c e) =
        M + mkv (a + tF * coordUx a c e) (b + tF * coordUy a b c e) := by
      simp only [hmkv, smul_add, smul_smul]
      module
    rw [h2]
  have htF0 : tF * (tF * (coordUx a c e ^ 2 + coordUy a b c e ^ 2) +
      2 * ((a - d) * coordUx a c e + b * coordUy a b c e)) = 0 := by
    have h1 : dist F N = dist A N := by rw [hFΓ, hAΓ]
    rw [hdAN, hFeq, hNeq, dist_eq] at h1
    have h3 := (Real.sqrt_inj (add_nonneg (sq_nonneg _) (sq_nonneg _))
      (add_nonneg (sq_nonneg _) (sq_nonneg _))).1 h1
    linear_combination h3
  have htF_ne : tF ≠ 0 := by
    intro hz
    rw [hz, zero_smul, add_zero] at hFeq'
    exact F_ne_A hFeq'
  have htF_val : tF = coordTF a b c e d :=
    t_eq_of_quadratic hu2 htF0 htF_ne
  have hFfinal : F = M + mkv (coordFx a b c e d) (coordFy a b c e d) := by
    rw [hFeq, htF_val]
    simp only [coordFx, coordFy]
  -- Inner products with the frame vectors.
  have inner_mkv_u (x y : ℝ) : ⟪mkv x y, u⟫ = x := by
    have h1 : u = mkv 1 0 := by simp [hmkv]
    rw [h1, inner_mkv]
    simp
  have inner_mkv_Ju (x y : ℝ) : ⟪mkv x y, jrot u⟫ = y := by
    have h1 : jrot u = mkv 0 1 := by simp [hmkv]
    rw [h1, inner_mkv]
    simp
  -- Coordinates of `B`.
  set aB := ⟪B - M, u⟫ with haB_def
  set bB := ⟪B - M, jrot u⟫ with hbB_def
  have hBeq0 : B = M + mkv aB bB := decomp B
  have hdBM : dist B M = √(aB ^ 2 + bB ^ 2) := by
    rw [hBeq0]
    exact dist_mkv_left M aB bB
  have hdBN : dist B N = √((aB - d) ^ 2 + bB ^ 2) := by
    rw [hBeq0, hNeq]
    have h := dist_eq M aB bB d 0
    rw [show (aB - d) ^ 2 + (bB - 0) ^ 2 = (aB - d) ^ 2 + bB ^ 2 by ring] at h
    exact h
  have heqB1 : aB ^ 2 + bB ^ 2 = a ^ 2 + b ^ 2 := by
    have h1 : dist B M = dist A M := by rw [hBΩ, hAΩ]
    rw [hdBM, hdAM] at h1
    exact (Real.sqrt_inj (add_nonneg (sq_nonneg _) (sq_nonneg _))
      (add_nonneg (sq_nonneg _) (sq_nonneg _))).1 h1
  have heqB2 : (aB - d) ^ 2 + bB ^ 2 = (a - d) ^ 2 + b ^ 2 := by
    have h1 : dist B N = dist A N := by rw [hBΓ, hAΓ]
    rw [hdBN, hdAN] at h1
    exact (Real.sqrt_inj (add_nonneg (sq_nonneg _) (sq_nonneg _))
      (add_nonneg (sq_nonneg _) (sq_nonneg _))).1 h1
  have haB : aB = a := by
    have h1 : aB ^ 2 - (aB - d) ^ 2 = a ^ 2 - (a - d) ^ 2 := by linarith [heqB1, heqB2]
    have h2 : aB ^ 2 - (aB - d) ^ 2 = d * (2 * aB - d) := by ring
    have h3 : a ^ 2 - (a - d) ^ 2 = d * (2 * a - d) := by ring
    have h4 : d * (2 * aB - d) = d * (2 * a - d) := by linarith [h1, h2, h3]
    rcases mul_eq_mul_left_iff.1 h4 with h6 | h6
    · linarith [h6]
    · exact absurd h6 hd'
  have hbB : bB = -b := by
    have h1 : bB ^ 2 = b ^ 2 := by
      rw [haB] at heqB1
      linarith [heqB1]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h2 | h2
    · exfalso
      have h3 : B = A := by
        rw [hBeq0, haB, h2]
        exact hAeq.symm
      exact A_ne_B h3.symm
    · exact h2
  have hBeq : B = M + mkv a (-b) := by
    rw [hBeq0, haB, hbB]
  -- `B, E, F` are not collinear.
  have aiBEF : AffineIndependent ℝ ![B, E, F] := by
    rw [affineIndependent_iff_not_collinear_set]
    intro hcol
    rw [collinear_iff_exists_forall_eq_smul_vadd] at hcol
    obtain ⟨p₀, v, hv⟩ := hcol
    have hBmem : B ∈ ({B, E, F} : Set (EuclideanSpace ℝ (Fin 2))) := by simp
    have hEmem : E ∈ ({B, E, F} : Set (EuclideanSpace ℝ (Fin 2))) := by simp
    have hFmem : F ∈ ({B, E, F} : Set (EuclideanSpace ℝ (Fin 2))) := by simp
    obtain ⟨rB, hrB⟩ := hv B hBmem
    obtain ⟨rE, hrE⟩ := hv E hEmem
    obtain ⟨rF, hrF⟩ := hv F hFmem
    have hEB : E -ᵥ B = (rE - rB) • v := by
      rw [hrE, hrB]
      simp only [vadd_eq_add, vsub_eq_sub]
      module
    have hFB : F -ᵥ B = (rF - rB) • v := by
      rw [hrF, hrB]
      simp only [vadd_eq_add, vsub_eq_sub]
      module
    have hEBc : E -ᵥ B = mkv (coordEx a b c e 0 - a) (coordEy a b c e 0 - -b) := by
      rw [vsub_eq_sub, hEfinal, hBeq, ← mkv_sub]
      abel
    have hFBc : F -ᵥ B = mkv (coordFx a b c e d - a) (coordFy a b c e d - -b) := by
      rw [vsub_eq_sub, hFfinal, hBeq, ← mkv_sub]
      abel
    have hξE : coordEx a b c e 0 - a = (rE - rB) * ⟪v, u⟫ := by
      have h1 := congrArg (fun w => ⟪w, u⟫) (hEBc.symm.trans hEB)
      rw [inner_mkv_u, inner_smul_left, RCLike.conj_to_real] at h1
      exact h1
    have hηE : coordEy a b c e 0 - -b = (rE - rB) * ⟪v, jrot u⟫ := by
      have h1 := congrArg (fun w => ⟪w, jrot u⟫) (hEBc.symm.trans hEB)
      rw [inner_mkv_Ju, inner_smul_left, RCLike.conj_to_real] at h1
      exact h1
    have hξF : coordFx a b c e d - a = (rF - rB) * ⟪v, u⟫ := by
      have h1 := congrArg (fun w => ⟪w, u⟫) (hFBc.symm.trans hFB)
      rw [inner_mkv_u, inner_smul_left, RCLike.conj_to_real] at h1
      exact h1
    have hηF : coordFy a b c e d - -b = (rF - rB) * ⟪v, jrot u⟫ := by
      have h1 := congrArg (fun w => ⟪w, jrot u⟫) (hFBc.symm.trans hFB)
      rw [inner_mkv_Ju, inner_smul_left, RCLike.conj_to_real] at h1
      exact h1
    have hdet0 : (coordEx a b c e 0 - a) * (coordFy a b c e d - -b) -
        (coordEy a b c e 0 - -b) * (coordFx a b c e d - a) = 0 := by
      rw [hξE, hξF, hηE, hηF]
      ring
    have hdet0' : (coordEx a b c e 0 - a) * (coordFy a b c e d + b) -
        (coordEy a b c e 0 + b) * (coordFx a b c e d - a) = 0 := by
      have h1 : coordFy a b c e d + b = coordFy a b c e d - -b := by ring
      have h2 : coordEy a b c e 0 + b = coordEy a b c e 0 - -b := by ring
      rw [h1, h2]
      exact hdet0
    exact hdet hdet0'
  -- The orthocenter `H` of `PMN`.
  set tPMN : Triangle ℝ (EuclideanSpace ℝ (Fin 2)) := ⟨_, affineIndependent_PMN⟩ with htPMN_def
  have hpoints0 : tPMN.points 0 = P := rfl
  have hpoints1 : tPMN.points 1 = M := rfl
  have hpoints2 : tPMN.points 2 = N := rfl
  have himg0 : tPMN.points '' ({(0 : Fin 3)}ᶜ : Set (Fin 3)) = {M, N} := by
    have h01 : ({(0 : Fin 3)}ᶜ : Set (Fin 3)) = {1, 2} := by
      ext i
      fin_cases i <;> decide
    rw [h01, Set.image_insert_eq, Set.image_singleton, hpoints1, hpoints2]
  have himg1 : tPMN.points '' ({(1 : Fin 3)}ᶜ : Set (Fin 3)) = {P, N} := by
    have h01 : ({(1 : Fin 3)}ᶜ : Set (Fin 3)) = {0, 2} := by
      ext i
      fin_cases i <;> decide
    rw [h01, Set.image_insert_eq, Set.image_singleton, hpoints0, hpoints2]
  have htopPMN : affineSpan ℝ (Set.range tPMN.points) = ⊤ := by
    refine (AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one
      affineIndependent_PMN).2 ?_
    rw [Fintype.card_fin, finrank_euclideanSpace_fin]
  have horth1 : ⟪M -ᵥ N, M + mkv (coordHx c e) (coordHy a b c e) -ᵥ P⟫ = 0 := by
    rw [vsub_eq_sub, vsub_eq_sub]
    have h1 : M - N = (-d) • u := by
      have h2 : M - N = -(N - M) := by abel
      rw [h2, hNM, neg_smul]
    have h3 : M + mkv (coordHx c e) (coordHy a b c e) - P =
        mkv (coordHx c e - px) (coordHy a b c e - py) := by
      rw [hPeq, ← mkv_sub]
      abel
    have h4 : (-d) • u = mkv (-d) 0 := by simp [hmkv]
    have h5 : coordHx c e - px = 0 := by
      rw [hpx_def]
      exact sub_self _
    rw [h1, h3, h4, h5, inner_mkv]
    simp
  have hmem0 : M + mkv (coordHx c e) (coordHy a b c e) ∈ tPMN.altitude 0 := by
    rw [Simplex.altitude_def, AffineSubspace.mem_inf_iff]
    refine ⟨?_, ?_⟩
    · rw [hpoints0, direction_affineSpan, himg0, AffineSubspace.mem_mk']
      rw [Submodule.mem_orthogonal]
      intro v hv
      rw [vectorSpan_pair, Submodule.mem_span_singleton] at hv
      obtain ⟨rv, hrv⟩ := hv
      rw [← hrv, inner_smul_left, RCLike.conj_to_real, horth1, mul_zero]
    · rw [htopPMN]
      trivial
  have horth2 : ⟪P -ᵥ N, M + mkv (coordHx c e) (coordHy a b c e) -ᵥ M⟫ = 0 := by
    rw [vsub_eq_sub, vsub_eq_sub]
    have h1 : P - N = mkv (px - d) py := by
      rw [hPeq, hNeq]
      have h2 : M + mkv px py - (M + mkv d 0) = mkv px py - mkv d 0 := by abel
      rw [h2, mkv_sub, sub_zero]
    have h2 : M + mkv (coordHx c e) (coordHy a b c e) - M =
        mkv (coordHx c e) (coordHy a b c e) := by abel
    rw [h1, h2, inner_mkv]
    have h3 : coordHx c e = px := by
      rw [hpx_def]
      rfl
    rw [h3, hpy_def, hnx, hpx_def]
    exact horth2_algebra hb hac hae hMc
  have hmem1 : M + mkv (coordHx c e) (coordHy a b c e) ∈ tPMN.altitude 1 := by
    rw [Simplex.altitude_def, AffineSubspace.mem_inf_iff]
    refine ⟨?_, ?_⟩
    · rw [hpoints1, direction_affineSpan, himg1, AffineSubspace.mem_mk']
      rw [Submodule.mem_orthogonal]
      intro v hv
      rw [vectorSpan_pair, Submodule.mem_span_singleton] at hv
      obtain ⟨rv, hrv⟩ := hv
      rw [← hrv, inner_smul_left, RCLike.conj_to_real, horth2, mul_zero]
    · rw [htopPMN]
      trivial
  have hHeq : H = M + mkv (coordHx c e) (coordHy a b c e) := by
    rw [H_eq_orthocenter]
    exact (Triangle.eq_orthocenter_of_forall_mem_altitude (i₁ := 0) (i₂ := 1) (by decide)
      hmem0 hmem1).symm
  -- The circumcenter `O` of `BEF`.
  set tBEF : Triangle ℝ (EuclideanSpace ℝ (Fin 2)) := ⟨_, aiBEF⟩ with htBEF_def
  have htopBEF : affineSpan ℝ (Set.range tBEF.points) = ⊤ := by
    refine (AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one aiBEF).2 ?_
    rw [Fintype.card_fin, finrank_euclideanSpace_fin]
  have hOdist : ∀ i : Fin 3, dist (tBEF.points i) (M + mkv (coordOx a b c e) (coordOy a b c e)) =
      dist B (M + mkv (coordOx a b c e) (coordOy a b c e)) := by
    intro i
    fin_cases i
    · rfl
    · show dist E (M + mkv (coordOx a b c e) (coordOy a b c e)) =
        dist B (M + mkv (coordOx a b c e) (coordOy a b c e))
      rw [hEfinal, hBeq, dist_eq, dist_eq]
      exact congrArg Real.sqrt hdEO
    · show dist F (M + mkv (coordOx a b c e) (coordOy a b c e)) =
        dist B (M + mkv (coordOx a b c e) (coordOy a b c e))
      rw [hFfinal, hBeq, dist_eq, dist_eq]
      exact congrArg Real.sqrt hdFO
  have hOeq : tBEF.circumcenter = M + mkv (coordOx a b c e) (coordOy a b c e) :=
    (Simplex.eq_circumcenter_of_dist_eq tBEF (by rw [htopBEF]; trivial) hOdist).symm
  have hOrad : dist B tBEF.circumcenter = tBEF.circumradius :=
    Simplex.dist_circumcenter_eq_circumradius tBEF 0
  -- The tangency point `T = M + N - A`.
  set Tx := coordTx a 0 d with hTx_def
  set Ty := coordTy b with hTy_def
  set T : EuclideanSpace ℝ (Fin 2) := M + mkv Tx Ty with hT_def
  have hTH : T -ᵥ H = coordLam a b c e • (P - A) := by
    rw [vsub_eq_sub, hT_def, hHeq, hTx_def, hTy_def]
    have h1 : M + mkv (coordTx a 0 d) (coordTy b) - (M + mkv (coordHx c e) (coordHy a b c e)) =
        mkv (coordTx a 0 d - coordHx c e) (coordTy b - coordHy a b c e) := by
      rw [← mkv_sub]
      abel
    rw [h1, hPA, hT1, hT2]
    simp only [hmkv]
    module
  have hTO : T -ᵥ (M + mkv (coordOx a b c e) (coordOy a b c e)) =
      mkv (Tx - coordOx a b c e) (Ty - coordOy a b c e) := by
    rw [vsub_eq_sub, hT_def, ← mkv_sub]
    abel
  have hinner : ⟪P - A, T -ᵥ (M + mkv (coordOx a b c e) (coordOy a b c e))⟫ = 0 := by
    rw [hTO, hPA, inner_mkv]
    exact hperp
  -- The tangency.
  refine ⟨aiBEF, T, ?_, ?_, ?_⟩
  · rw [EuclideanGeometry.mem_sphere, Simplex.circumsphere_center, Simplex.circumsphere_radius,
      hOeq, ← hOrad, hOeq, hT_def, hBeq, dist_eq, dist_eq]
    exact congrArg Real.sqrt hdTO
  · rw [AffineSubspace.mem_mk', direction_affineSpan, mem_vectorSpan_pair]
    refine ⟨-coordLam a b c e, ?_⟩
    rw [hAvP, hTH]
    module
  · rw [SetLike.le_def]
    intro q hq
    rw [Sphere.mem_orthRadius_iff_inner_left, Simplex.circumsphere_center, hOeq]
    rw [AffineSubspace.mem_mk', direction_affineSpan, mem_vectorSpan_pair] at hq
    obtain ⟨μ, hμ⟩ := hq
    rw [hAvP] at hμ
    have hqT : q -ᵥ T = (-μ - coordLam a b c e) • (P - A) := by
      rw [← vsub_sub_vsub_cancel_right q T H, ← hμ, hTH]
      module
    rw [hqT, inner_smul_left, RCLike.conj_to_real, hinner, mul_zero]

/-- The transfer of the coordinate version to a general 2-dimensional space. -/
theorem imo2025_p2_transfer
    (h2d : ∀ {M N A B C D P E F H : EuclideanSpace ℝ (Fin 2)}
      {Ω Γ : Sphere (EuclideanSpace ℝ (Fin 2))},
      Ω.center = M → Γ.center = N → Ω.radius < Γ.radius →
      A ∈ (Ω ∩ Γ : Set (EuclideanSpace ℝ (Fin 2))) →
      B ∈ (Ω ∩ Γ : Set (EuclideanSpace ℝ (Fin 2))) → A ≠ B → M ≠ N →
      C ∈ (line[ℝ, M, N] ∩ Ω : Set (EuclideanSpace ℝ (Fin 2))) →
      D ∈ (line[ℝ, M, N] ∩ Γ : Set (EuclideanSpace ℝ (Fin 2))) →
      [C, M, N, D].Sbtw ℝ →
      ∀ (aiACD : AffineIndependent ℝ ![A, C, D]),
      P = (⟨_, aiACD⟩ : Triangle ℝ (EuclideanSpace ℝ (Fin 2))).circumcenter →
      E ∈ (line[ℝ, A, P] ∩ Ω : Set (EuclideanSpace ℝ (Fin 2))) → E ≠ A →
      F ∈ (line[ℝ, A, P] ∩ Γ : Set (EuclideanSpace ℝ (Fin 2))) → F ≠ A →
      ∀ (aiPMN : AffineIndependent ℝ ![P, M, N]),
      H = Triangle.orthocenter (⟨_, aiPMN⟩ : Triangle ℝ (EuclideanSpace ℝ (Fin 2))) →
      ∃ ai : AffineIndependent ℝ ![B, E, F],
        (⟨_, ai⟩ : Triangle ℝ (EuclideanSpace ℝ (Fin 2))).circumsphere.IsTangent
          (AffineSubspace.mk' H line[ℝ, A, P].direction))
    {M N A B C D P E F H : Pt} {Ω Γ : Sphere Pt}
    (Ω_center_eq_M : Ω.center = M) (Γ_center_eq_N : Γ.center = N)
    (Ω_radius_lt_Γ_radius : Ω.radius < Γ.radius)
    (A_mem_inter : A ∈ (Ω ∩ Γ : Set Pt)) (B_mem_inter : B ∈ (Ω ∩ Γ : Set Pt))
    (A_ne_B : A ≠ B) (M_ne_N : M ≠ N)
    (C_mem_inter : C ∈ (line[ℝ, M, N] ∩ Ω : Set Pt))
    (D_mem_inter : D ∈ (line[ℝ, M, N] ∩ Γ : Set Pt))
    (sbtw_C_M_N_D : [C, M, N, D].Sbtw ℝ)
    (affineIndependent_ACD : AffineIndependent ℝ ![A, C, D])
    (P_eq_circumcenter :
      P = (⟨_, affineIndependent_ACD⟩ : Triangle ℝ Pt).circumcenter)
    (E_mem_inter : E ∈ (line[ℝ, A, P] ∩ Ω : Set Pt)) (E_ne_A : E ≠ A)
    (F_mem_inter : F ∈ (line[ℝ, A, P] ∩ Γ : Set Pt)) (F_ne_A : F ≠ A)
    (affineIndependent_PMN : AffineIndependent ℝ ![P, M, N])
    (H_eq_orthocenter :
      H = Triangle.orthocenter (⟨_, affineIndependent_PMN⟩ : Triangle ℝ Pt)) :
    ∃ affineIndependent_BEF : AffineIndependent ℝ ![B, E, F],
      (⟨_, affineIndependent_BEF⟩ : Triangle ℝ Pt).circumsphere.IsTangent
        (AffineSubspace.mk' H line[ℝ, A, P].direction) := by
  -- The affine isometry equivalence onto the model plane `EuclideanSpace ℝ (Fin 2)`.
  have hfr : Module.finrank ℝ V = 2 := Fact.out
  haveI : FiniteDimensional ℝ V := FiniteDimensional.of_finrank_pos (by rw [hfr]; norm_num)
  let ob : OrthonormalBasis (Fin 2) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr hfr)
  let lie : V ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    ob.equiv (EuclideanSpace.basisFun (Fin 2) ℝ) (Equiv.refl _)
  let Φ : Pt ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    (AffineIsometryEquiv.constVSub ℝ M).trans lie.toAffineIsometryEquiv
  -- Sphere membership transports along `Φ`.
  have hmemΩ' {X : Pt} (hX : X ∈ Ω) :
      Φ X ∈ (⟨Φ M, Ω.radius⟩ : Sphere (EuclideanSpace ℝ (Fin 2))) := by
    rw [EuclideanGeometry.mem_sphere] at hX ⊢
    rw [Ω_center_eq_M] at hX
    rw [Sphere.mk_center, Sphere.mk_radius, AffineIsometryEquiv.dist_map]
    exact hX
  have hmemΓ' {X : Pt} (hX : X ∈ Γ) :
      Φ X ∈ (⟨Φ N, Γ.radius⟩ : Sphere (EuclideanSpace ℝ (Fin 2))) := by
    rw [EuclideanGeometry.mem_sphere] at hX ⊢
    rw [Γ_center_eq_N] at hX
    rw [Sphere.mk_center, Sphere.mk_radius, AffineIsometryEquiv.dist_map]
    exact hX
  -- Lines through pairs of points transport along `Φ`.
  have hlineMN : (line[ℝ, M, N]).map Φ.toAffineIsometry.toAffineMap = line[ℝ, Φ M, Φ N] := by
    rw [AffineSubspace.map_span, Set.image_insert_eq, Set.image_singleton,
      AffineIsometry.coe_toAffineMap, AffineIsometryEquiv.coe_toAffineIsometry]
  have hlineAP : (line[ℝ, A, P]).map Φ.toAffineIsometry.toAffineMap = line[ℝ, Φ A, Φ P] := by
    rw [AffineSubspace.map_span, Set.image_insert_eq, Set.image_singleton,
      AffineIsometry.coe_toAffineMap, AffineIsometryEquiv.coe_toAffineIsometry]
  have hlineC : Φ C ∈ line[ℝ, Φ M, Φ N] := by
    rw [← hlineMN]
    exact AffineSubspace.mem_map_of_mem (f := Φ.toAffineIsometry.toAffineMap) C_mem_inter.1
  have hlineD : Φ D ∈ line[ℝ, Φ M, Φ N] := by
    rw [← hlineMN]
    exact AffineSubspace.mem_map_of_mem (f := Φ.toAffineIsometry.toAffineMap) D_mem_inter.1
  have hlineE : Φ E ∈ line[ℝ, Φ A, Φ P] := by
    rw [← hlineAP]
    exact AffineSubspace.mem_map_of_mem (f := Φ.toAffineIsometry.toAffineMap) E_mem_inter.1
  have hlineF : Φ F ∈ line[ℝ, Φ A, Φ P] := by
    rw [← hlineAP]
    exact AffineSubspace.mem_map_of_mem (f := Φ.toAffineIsometry.toAffineMap) F_mem_inter.1
  -- Strict betweenness of the quadruple transports along `Φ`.
  have hsbtw' : [Φ C, Φ M, Φ N, Φ D].Sbtw ℝ := by
    have sbtw_map {x y z : Pt} (h : Sbtw ℝ x y z) : Sbtw ℝ (Φ x) (Φ y) (Φ z) :=
      ⟨h.wbtw.map Φ.toAffineIsometry.toAffineMap, Φ.injective.ne h.ne_left,
        Φ.injective.ne h.ne_right⟩
    rw [List.sbtw_four] at sbtw_C_M_N_D ⊢
    obtain ⟨h1, h2, h3, h4⟩ := sbtw_C_M_N_D
    exact ⟨sbtw_map h1, sbtw_map h2, sbtw_map h3, sbtw_map h4⟩
  -- Affine independence of the triples transports along `Φ`.
  have hcomp {X Y Z : Pt} :
      (Φ.toAffineIsometry.toAffineMap ∘ ![X, Y, Z] : Fin 3 → EuclideanSpace ℝ (Fin 2)) =
        ![Φ X, Φ Y, Φ Z] := by
    funext i
    fin_cases i <;> simp
  have aiACD' : AffineIndependent ℝ ![Φ A, Φ C, Φ D] := by
    have h := affineIndependent_ACD.map' Φ.toAffineIsometry.toAffineMap
      Φ.toAffineIsometry.injective
    rwa [hcomp] at h
  have aiPMN' : AffineIndependent ℝ ![Φ P, Φ M, Φ N] := by
    have h := affineIndependent_PMN.map' Φ.toAffineIsometry.toAffineMap
      Φ.toAffineIsometry.injective
    rwa [hcomp] at h
  -- The circumcenter of triangle `ACD` transports along `Φ`.
  have htmapACD :
      (⟨_, affineIndependent_ACD⟩ : Triangle ℝ Pt).map Φ.toAffineIsometry.toAffineMap
          Φ.toAffineIsometry.injective =
        (⟨_, aiACD'⟩ : Triangle ℝ (EuclideanSpace ℝ (Fin 2))) :=
    Simplex.ext fun i => by fin_cases i <;> simp
  have hPc : Φ P = (⟨_, aiACD'⟩ : Triangle ℝ (EuclideanSpace ℝ (Fin 2))).circumcenter := by
    rw [← htmapACD, Simplex.circumcenter_map, ← P_eq_circumcenter,
      AffineIsometryEquiv.coe_toAffineIsometry]
  -- The orthocenter of triangle `PMN` transports along `Φ`.
  have htmapPMN :
      (⟨_, affineIndependent_PMN⟩ : Triangle ℝ Pt).map Φ.toAffineIsometry.toAffineMap
          Φ.toAffineIsometry.injective =
        (⟨_, aiPMN'⟩ : Triangle ℝ (EuclideanSpace ℝ (Fin 2))) :=
    Simplex.ext fun i => by fin_cases i <;> simp
  have horth :
      Φ H = Triangle.orthocenter (⟨_, aiPMN'⟩ : Triangle ℝ (EuclideanSpace ℝ (Fin 2))) := by
    have hmem : ∀ i : Fin 3,
        Φ H ∈ (⟨_, aiPMN'⟩ : Triangle ℝ (EuclideanSpace ℝ (Fin 2))).altitude i := by
      intro i
      rw [← htmapPMN, Simplex.altitude_map]
      refine AffineSubspace.mem_map_of_mem (f := Φ.toAffineIsometry.toAffineMap) (x := H)
        (s := (⟨_, affineIndependent_PMN⟩ : Triangle ℝ Pt).altitude i) ?_
      rw [H_eq_orthocenter]
      exact Triangle.orthocenter_mem_altitude _
    exact Triangle.eq_orthocenter_of_forall_mem_altitude (i₁ := 0) (i₂ := 1) (by decide)
      (hmem 0) (hmem 1)
  -- Apply the 2-dimensional statement to the image configuration.
  obtain ⟨ai', htan'⟩ := h2d (M := Φ M) (N := Φ N) (A := Φ A) (B := Φ B) (C := Φ C) (D := Φ D)
    (P := Φ P) (E := Φ E) (F := Φ F) (H := Φ H)
    (Ω := (⟨Φ M, Ω.radius⟩ : Sphere (EuclideanSpace ℝ (Fin 2))))
    (Γ := (⟨Φ N, Γ.radius⟩ : Sphere (EuclideanSpace ℝ (Fin 2))))
    rfl rfl Ω_radius_lt_Γ_radius
    ⟨hmemΩ' A_mem_inter.1, hmemΓ' A_mem_inter.2⟩ ⟨hmemΩ' B_mem_inter.1, hmemΓ' B_mem_inter.2⟩
    (Φ.injective.ne A_ne_B) (Φ.injective.ne M_ne_N)
    ⟨hlineC, hmemΩ' C_mem_inter.2⟩ ⟨hlineD, hmemΓ' D_mem_inter.2⟩
    hsbtw' aiACD' hPc
    ⟨hlineE, hmemΩ' E_mem_inter.2⟩ (Φ.injective.ne E_ne_A)
    ⟨hlineF, hmemΓ' F_mem_inter.2⟩ (Φ.injective.ne F_ne_A)
    aiPMN' horth
  -- Pull affine independence of `BEF` back along `Φ.symm`.
  have hcompS : (Φ.symm.toAffineIsometry.toAffineMap ∘ ![Φ B, Φ E, Φ F] : Fin 3 → Pt) =
      ![B, E, F] := by
    funext i
    fin_cases i <;> simp
  have ai : AffineIndependent ℝ ![B, E, F] := by
    have h := ai'.map' Φ.symm.toAffineIsometry.toAffineMap Φ.symm.toAffineIsometry.injective
    rwa [hcompS] at h
  -- The image triangle is the pushforward of the triangle in `Pt`.
  have htBEF : (⟨_, ai⟩ : Triangle ℝ Pt).map Φ.toAffineIsometry.toAffineMap
        Φ.toAffineIsometry.injective =
      (⟨_, ai'⟩ : Triangle ℝ (EuclideanSpace ℝ (Fin 2))) :=
    Simplex.ext fun i => by fin_cases i <;> simp
  have hcenter : (⟨_, ai'⟩ : Triangle ℝ (EuclideanSpace ℝ (Fin 2))).circumsphere.center =
      Φ (⟨_, ai⟩ : Triangle ℝ Pt).circumsphere.center := by
    rw [← htBEF, Simplex.circumsphere_center, Simplex.circumcenter_map,
      Simplex.circumsphere_center, AffineIsometryEquiv.coe_toAffineIsometry]
  have hradius : (⟨_, ai'⟩ : Triangle ℝ (EuclideanSpace ℝ (Fin 2))).circumsphere.radius =
      (⟨_, ai⟩ : Triangle ℝ Pt).circumsphere.radius := by
    rw [← htBEF, Simplex.circumsphere_radius, Simplex.circumradius_map,
      Simplex.circumsphere_radius]
  -- The tangent subspace is the preimage of its image under `Φ`.
  have hlineAP_dir : line[ℝ, A, P].direction.map Φ.toAffineIsometry.toAffineMap.linear =
      line[ℝ, Φ A, Φ P].direction := by
    rw [← AffineSubspace.map_direction, hlineAP]
  have hmk'map : (AffineSubspace.mk' H line[ℝ, A, P].direction).map
        Φ.toAffineIsometry.toAffineMap =
      AffineSubspace.mk' (Φ H) line[ℝ, Φ A, Φ P].direction := by
    rw [AffineSubspace.map_mk', hlineAP_dir, AffineIsometry.coe_toAffineMap,
      AffineIsometryEquiv.coe_toAffineIsometry]
  -- Unpack the tangency in the model plane and transport it back along `Φ.symm`.
  obtain ⟨p', hp'mem, hp'space, hle⟩ := htan'
  refine ⟨ai, Φ.symm p', ?_, ?_, ?_⟩
  · -- `Φ.symm p'` lies on the circumsphere of `BEF`.
    rw [EuclideanGeometry.mem_sphere] at hp'mem ⊢
    rw [hcenter, hradius] at hp'mem
    rw [← Φ.dist_map (Φ.symm p') (⟨_, ai⟩ : Triangle ℝ Pt).circumsphere.center,
      AffineIsometryEquiv.apply_symm_apply]
    exact hp'mem
  · -- `Φ.symm p'` lies on the candidate tangent subspace.
    have h1 : Φ.toAffineIsometry.toAffineMap (Φ.symm p') ∈
        (AffineSubspace.mk' H line[ℝ, A, P].direction).map Φ.toAffineIsometry.toAffineMap := by
      rw [hmk'map]
      simpa using hp'space
    exact (AffineSubspace.mem_map_iff_mem_of_injective Φ.toAffineIsometry.injective).mp h1
  · -- The candidate tangent subspace is contained in the orthRadius at `Φ.symm p'`.
    intro q hq
    rw [Sphere.mem_orthRadius_iff_inner_left]
    have hq' : Φ q ∈ AffineSubspace.mk' (Φ H) line[ℝ, Φ A, Φ P].direction := by
      rw [← hmk'map]
      exact AffineSubspace.mem_map_of_mem (f := Φ.toAffineIsometry.toAffineMap) hq
    have hqorth := hle hq'
    rw [Sphere.mem_orthRadius_iff_inner_left] at hqorth
    rw [hcenter] at hqorth
    rw [← AffineIsometryEquiv.apply_symm_apply Φ p'] at hqorth
    rw [← Φ.map_vsub, ← Φ.map_vsub] at hqorth
    rw [LinearIsometryEquiv.inner_map_map] at hqorth
    exact hqorth

end -- noncomputable section

snip end

problem imo2025_p2 {M N A B C D P E F H : Pt} {Ω Γ : Sphere Pt}
    (Ω_center_eq_M : Ω.center = M) (Γ_center_eq_N : Γ.center = N)
    (Ω_radius_lt_Γ_radius : Ω.radius < Γ.radius)
    (A_mem_inter : A ∈ (Ω ∩ Γ : Set Pt)) (B_mem_inter : B ∈ (Ω ∩ Γ : Set Pt))
    (A_ne_B : A ≠ B) (M_ne_N : M ≠ N)
    (C_mem_inter : C ∈ (line[ℝ, M, N] ∩ Ω : Set Pt))
    (D_mem_inter : D ∈ (line[ℝ, M, N] ∩ Γ : Set Pt))
    (sbtw_C_M_N_D : [C, M, N, D].Sbtw ℝ)
    (affineIndependent_ACD : AffineIndependent ℝ ![A, C, D])
    (P_eq_circumcenter :
      P = (⟨_, affineIndependent_ACD⟩ : Triangle ℝ Pt).circumcenter)
    (E_mem_inter : E ∈ (line[ℝ, A, P] ∩ Ω : Set Pt)) (E_ne_A : E ≠ A)
    (F_mem_inter : F ∈ (line[ℝ, A, P] ∩ Γ : Set Pt)) (F_ne_A : F ≠ A)
    (affineIndependent_PMN : AffineIndependent ℝ ![P, M, N])
    (H_eq_orthocenter :
      H = Triangle.orthocenter (⟨_, affineIndependent_PMN⟩ : Triangle ℝ Pt)) :
    ∃ affineIndependent_BEF : AffineIndependent ℝ ![B, E, F],
      (⟨_, affineIndependent_BEF⟩ : Triangle ℝ Pt).circumsphere.IsTangent
        (AffineSubspace.mk' H line[ℝ, A, P].direction) :=
  imo2025_p2_transfer imo2025_p2_coord Ω_center_eq_M Γ_center_eq_N Ω_radius_lt_Γ_radius
    A_mem_inter B_mem_inter A_ne_B M_ne_N C_mem_inter D_mem_inter sbtw_C_M_N_D
    affineIndependent_ACD P_eq_circumcenter E_mem_inter E_ne_A F_mem_inter F_ne_A
    affineIndependent_PMN H_eq_orthocenter

end Imo2025P2
