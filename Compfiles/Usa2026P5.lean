/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.FieldTheory.Perfect
public import Mathlib.Geometry.Euclidean.Angle.Sphere
public import Mathlib.Geometry.Euclidean.Sphere.SecondInter
public import Mathlib.Geometry.Euclidean.Triangle
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 2026, Problem 5

Let ABC be a triangle. Points D, E, and F lie on sides BC, CA, and AB,
respectively, such that ∠AFE = ∠BDF = ∠CED. Let OA, OB, and OC be the
circumcenters of triangles AFE, BDF, and CED, respectively. Let M, N, and O
be the circumcenters of triangles ABC, DEF, and OAOBOC, respectively.
Prove that OM = ON.
-/

namespace Usa2026P5

open EuclideanGeometry

/-- The circumcenter of a (non-degenerate) triangle with vertices `x y z : ℂ`,
given as the circumcenter of the corresponding `2`-simplex. -/
noncomputable def triCircumcenter {x y z : ℂ} (h : ¬Collinear ℝ {x, y, z}) : ℂ :=
  (⟨![x, y, z], affineIndependent_iff_not_collinear_set.mpr h⟩ :
    Affine.Simplex ℝ ℂ 2).circumcenter

/-- The circumcircle of a (non-degenerate) triangle with vertices `x y z : ℂ`,
given as the circumsphere of the corresponding `2`-simplex. -/
noncomputable def triCircumsphere {x y z : ℂ} (h : ¬Collinear ℝ {x, y, z}) : Sphere ℂ :=
  (⟨![x, y, z], affineIndependent_iff_not_collinear_set.mpr h⟩ :
    Affine.Simplex ℝ ℂ 2).circumsphere

snip begin

/-
Mathematical solution (Evan Chen, USAMO 2026 Solution Notes,
https://web.evanchen.cc/exams/USAMO-2026-notes.pdf):

By Miquel's theorem, the circumcircles of AEF, BFD, and CDE meet at a point Q
(the second Brocard point of ABC).  Write
  α = ∠AFE = ∠BDF = ∠CED,
  β = ∠QEA = ∠QEC = ∠QDC = ∠QDB = ∠QFB = ∠QFA.
Then there are spiral similarities centered at Q
  △QAE ~ △QBF ~ △QCD,
which extend to the circumcenters:
  △A OA E ~ △B OB F ~ △C OC D ~ △M O N.
In particular OM = ON (corresponding to OA A = OA E in the isosceles
triangle A OA E).

Formally, we work in the complex plane.  With σ₁(z) = Q + λ₁(z - Q) the direct
similarity sending A ↦ B, E ↦ F, and σ₂ the one sending B ↦ C, F ↦ D, the
circumcenter map
  f(z) := circumcenter(z, σ₁(z), σ₂(σ₁(z)))
is itself a direct similarity f(z) = Q + c(z - Q), and M = f(A), N = f(E),
O = f(OA).  Hence OM = |c|·|OA - A| = |c|·|OA - E| = ON.
-/

section SnipScope

open Real RealInnerProductSpace ComplexConjugate

local instance : Fact (Module.finrank ℝ ℂ = 2) := Complex.finrank_real_complex_fact

@[reducible]
noncomputable def instComplexOriented : Module.Oriented ℝ ℂ (Fin 2) :=
  ⟨Complex.orientation⟩

attribute [local instance] instComplexOriented

section AlgebraicCore

open ComplexConjugate

/-- Denominator of the circumcenter formula: `2i` times the signed area
(vanishes iff the three points are collinear). -/
noncomputable def ccDenom (z₁ z₂ z₃ : ℂ) : ℂ :=
  conj z₁ * (z₂ - z₃) + conj z₂ * (z₃ - z₁) + conj z₃ * (z₁ - z₂)

/-- Numerator of the circumcenter formula. -/
noncomputable def ccNum (z₁ z₂ z₃ : ℂ) : ℂ :=
  z₁ * conj z₁ * (z₂ - z₃) + z₂ * conj z₂ * (z₃ - z₁) + z₃ * conj z₃ * (z₁ - z₂)

/-- The circumcenter of the triangle `z₁ z₂ z₃`, given by the determinant formula. -/
noncomputable def cc (z₁ z₂ z₃ : ℂ) : ℂ :=
  ccNum z₁ z₂ z₃ / ccDenom z₁ z₂ z₃

lemma cc_eq (z₁ z₂ z₃ : ℂ) : cc z₁ z₂ z₃ = ccNum z₁ z₂ z₃ / ccDenom z₁ z₂ z₃ := rfl

/-- 1. The denominator as a single determinant. -/
lemma ccDenom_eq (z₁ z₂ z₃ : ℂ) :
    ccDenom z₁ z₂ z₃ = conj (z₂ - z₁) * (z₃ - z₁) - conj (z₃ - z₁) * (z₂ - z₁) := by
  simp only [ccDenom, map_sub]
  ring

/-- 2. Non-collinearity implies the denominator is nonzero. -/
lemma ccDenom_ne_zero_of_not_collinear (z₁ z₂ z₃ : ℂ)
    (h : ¬Collinear ℝ ({z₁, z₂, z₃} : Set ℂ)) : ccDenom z₁ z₂ z₃ ≠ 0 := by
  intro hd0
  rw [ccDenom_eq z₁ z₂ z₃] at hd0
  apply h
  by_cases h21 : z₂ = z₁
  · subst h21
    rw [Set.insert_eq_of_mem (Set.mem_insert z₂ {z₃})]
    exact collinear_pair ℝ z₂ z₃
  · have hd21 : z₂ - z₁ ≠ 0 := sub_ne_zero.mpr h21
    set w := conj (z₂ - z₁) * (z₃ - z₁) with hw_def
    have hconj_w : conj w = conj (z₃ - z₁) * (z₂ - z₁) := by
      rw [hw_def]
      simp only [map_mul, map_sub, starRingEnd_self_apply]
      ring
    have hw : w = conj w := by
      have hsub : w - conj w = 0 := by
        rw [hconj_w]
        exact hd0
      exact sub_eq_zero.mp hsub
    have hwre : (w.re : ℂ) = w := Complex.conj_eq_iff_re.mp hw.symm
    have hn : ‖z₂ - z₁‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hd21)
    have hca : conj (z₂ - z₁) ≠ 0 := by
      simp only [starRingEnd_apply, star_ne_zero]
      exact hd21
    set t : ℝ := w.re / ‖z₂ - z₁‖ ^ 2 with ht
    have key : z₃ - z₁ = (t : ℂ) * (z₂ - z₁) := by
      apply mul_right_cancel₀ hca
      calc (z₃ - z₁) * conj (z₂ - z₁)
          = conj (z₂ - z₁) * (z₃ - z₁) := mul_comm _ _
        _ = w := hw_def.symm
        _ = (w.re : ℂ) := hwre.symm
        _ = (t : ℂ) * ((‖z₂ - z₁‖ ^ 2 : ℝ) : ℂ) := by
            rw [← Complex.ofReal_mul, ht, div_mul_cancel₀ _ hn]
        _ = (t : ℂ) * (conj (z₂ - z₁) * (z₂ - z₁)) := by
            rw [Complex.conj_mul', ← Complex.ofReal_pow]
        _ = (↑t * (z₂ - z₁)) * conj (z₂ - z₁) := by ring
    rw [collinear_iff_of_mem (Set.mem_insert z₁ _)]
    refine ⟨z₂ - z₁, fun p hp => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · refine ⟨t, ?_⟩
      have hsmul : (t • (z₂ - z₁) : ℂ) = (t : ℂ) * (z₂ - z₁) :=
        RCLike.real_smul_eq_coe_mul t (z₂ - z₁)
      rw [vadd_eq_add, hsmul, ← key, sub_add_cancel]

/-- 3. Difference of the circumcenter and a vertex. -/
lemma cc_sub_left (z₁ z₂ z₃ : ℂ) (h : ccDenom z₁ z₂ z₃ ≠ 0) :
    cc z₁ z₂ z₃ - z₁ = (z₃ - z₁) * (z₂ - z₁) * (conj z₂ - conj z₃) / ccDenom z₁ z₂ z₃ := by
  rw [cc_eq, eq_div_iff h, sub_mul, div_mul_cancel₀ _ h]
  simp only [ccNum, ccDenom]
  ring

lemma cc_sub_mid (z₁ z₂ z₃ : ℂ) (h : ccDenom z₁ z₂ z₃ ≠ 0) :
    cc z₁ z₂ z₃ - z₂ = (z₁ - z₂) * (z₃ - z₂) * (conj z₃ - conj z₁) / ccDenom z₁ z₂ z₃ := by
  rw [cc_eq, eq_div_iff h, sub_mul, div_mul_cancel₀ _ h]
  simp only [ccNum, ccDenom]
  ring

lemma cc_sub_right (z₁ z₂ z₃ : ℂ) (h : ccDenom z₁ z₂ z₃ ≠ 0) :
    cc z₁ z₂ z₃ - z₃ = (z₁ - z₃) * (z₂ - z₃) * (conj z₁ - conj z₂) / ccDenom z₁ z₂ z₃ := by
  rw [cc_eq, eq_div_iff h, sub_mul, div_mul_cancel₀ _ h]
  simp only [ccNum, ccDenom]
  ring

/-- 4. Distance from the circumcenter to each vertex. -/
lemma dist_cc_left (z₁ z₂ z₃ : ℂ) (h : ccDenom z₁ z₂ z₃ ≠ 0) :
    dist (cc z₁ z₂ z₃) z₁ = dist z₁ z₂ * dist z₂ z₃ * dist z₃ z₁ / ‖ccDenom z₁ z₂ z₃‖ := by
  rw [Complex.dist_eq, cc_sub_left z₁ z₂ z₃ h, norm_div, norm_mul, norm_mul, ← map_sub,
    Complex.norm_conj, Complex.dist_eq, Complex.dist_eq, Complex.dist_eq, norm_sub_rev z₁ z₂]
  ring

lemma dist_cc_mid (z₁ z₂ z₃ : ℂ) (h : ccDenom z₁ z₂ z₃ ≠ 0) :
    dist (cc z₁ z₂ z₃) z₂ = dist z₁ z₂ * dist z₂ z₃ * dist z₃ z₁ / ‖ccDenom z₁ z₂ z₃‖ := by
  rw [Complex.dist_eq, cc_sub_mid z₁ z₂ z₃ h, norm_div, norm_mul, norm_mul, ← map_sub,
    Complex.norm_conj, Complex.dist_eq, Complex.dist_eq, Complex.dist_eq, norm_sub_rev z₃ z₂]

lemma dist_cc_right (z₁ z₂ z₃ : ℂ) (h : ccDenom z₁ z₂ z₃ ≠ 0) :
    dist (cc z₁ z₂ z₃) z₃ = dist z₁ z₂ * dist z₂ z₃ * dist z₃ z₁ / ‖ccDenom z₁ z₂ z₃‖ := by
  rw [Complex.dist_eq, cc_sub_right z₁ z₂ z₃ h, norm_div, norm_mul, norm_mul, ← map_sub,
    Complex.norm_conj, Complex.dist_eq, Complex.dist_eq, Complex.dist_eq, norm_sub_rev z₁ z₃]
  ring

lemma dist_cc_eq (z₁ z₂ z₃ : ℂ) (h : ccDenom z₁ z₂ z₃ ≠ 0) :
    dist (cc z₁ z₂ z₃) z₁ = dist (cc z₁ z₂ z₃) z₂ ∧
      dist (cc z₁ z₂ z₃) z₂ = dist (cc z₁ z₂ z₃) z₃ := by
  rw [dist_cc_left z₁ z₂ z₃ h, dist_cc_mid z₁ z₂ z₃ h, dist_cc_right z₁ z₂ z₃ h]
  exact ⟨rfl, rfl⟩

/-- 5. The formula indeed gives the circumcenter of the simplex. -/
lemma cc_eq_circumcenter (z₁ z₂ z₃ : ℂ) (h : ¬Collinear ℝ ({z₁, z₂, z₃} : Set ℂ)) :
    cc z₁ z₂ z₃ =
      (⟨![z₁, z₂, z₃], affineIndependent_iff_not_collinear_set.mpr h⟩ :
        Affine.Simplex ℝ ℂ 2).circumcenter := by
  have hd : ccDenom z₁ z₂ z₃ ≠ 0 := ccDenom_ne_zero_of_not_collinear z₁ z₂ z₃ h
  obtain ⟨h12, h23⟩ := dist_cc_eq z₁ z₂ z₃ hd
  apply Affine.Simplex.eq_circumcenter_of_dist_eq (r := dist (cc z₁ z₂ z₃) z₁)
  · rw [Affine.Simplex.span_eq_top _ Complex.finrank_real_complex]
    exact AffineSubspace.mem_top ℝ ℂ _
  · intro i
    fin_cases i <;> dsimp only
    · exact dist_comm _ _
    · rw [dist_comm]; exact h12.symm
    · rw [dist_comm]; exact h23.symm.trans h12.symm

/-- 6. Behavior of denominator and numerator under `z ↦ a * z + b`. -/
lemma ccDenom_smul_add (a b z₁ z₂ z₃ : ℂ) :
    ccDenom (a * z₁ + b) (a * z₂ + b) (a * z₃ + b) = a * conj a * ccDenom z₁ z₂ z₃ := by
  simp only [ccDenom, map_add, map_mul]
  ring

lemma ccNum_smul_add (a b z₁ z₂ z₃ : ℂ) :
    ccNum (a * z₁ + b) (a * z₂ + b) (a * z₃ + b) =
      a ^ 2 * conj a * ccNum z₁ z₂ z₃ + a * conj a * b * ccDenom z₁ z₂ z₃ := by
  simp only [ccNum, ccDenom, map_add, map_mul]
  ring

/-- 7. The circumcenter is equivariant under `z ↦ a * z + b`. -/
lemma cc_smul_add {a b z₁ z₂ z₃ : ℂ} (ha : a ≠ 0) (hd : ccDenom z₁ z₂ z₃ ≠ 0) :
    cc (a * z₁ + b) (a * z₂ + b) (a * z₃ + b) = a * cc z₁ z₂ z₃ + b := by
  have hca : conj a ≠ 0 := by simpa using ha
  have hprod : a * conj a * ccDenom z₁ z₂ z₃ ≠ 0 := mul_ne_zero (mul_ne_zero ha hca) hd
  rw [cc_eq, cc_eq, ccNum_smul_add, ccDenom_smul_add]
  field_simp

/-- 8. Permutation behavior. -/
lemma ccDenom_perm_cycle (z₁ z₂ z₃ : ℂ) : ccDenom z₁ z₂ z₃ = ccDenom z₂ z₃ z₁ := by
  simp only [ccDenom]
  ring

lemma ccNum_perm_cycle (z₁ z₂ z₃ : ℂ) : ccNum z₁ z₂ z₃ = ccNum z₂ z₃ z₁ := by
  simp only [ccNum]
  ring

lemma cc_perm_cycle (z₁ z₂ z₃ : ℂ) (hd : ccDenom z₁ z₂ z₃ ≠ 0) :
    cc z₁ z₂ z₃ = cc z₂ z₃ z₁ := by
  have hd' : ccDenom z₂ z₃ z₁ ≠ 0 := by rwa [← ccDenom_perm_cycle z₁ z₂ z₃]
  rw [cc_eq, cc_eq]
  field_simp
  simp only [ccNum, ccDenom]
  ring

lemma ccDenom_perm_swap (z₁ z₂ z₃ : ℂ) : ccDenom z₁ z₂ z₃ = -ccDenom z₂ z₁ z₃ := by
  simp only [ccDenom]
  ring

lemma ccNum_perm_swap (z₁ z₂ z₃ : ℂ) : ccNum z₁ z₂ z₃ = -ccNum z₂ z₁ z₃ := by
  simp only [ccNum]
  ring

lemma cc_perm_swap (z₁ z₂ z₃ : ℂ) (hd : ccDenom z₁ z₂ z₃ ≠ 0) :
    cc z₁ z₂ z₃ = cc z₂ z₁ z₃ := by
  have hd' : ccDenom z₂ z₁ z₃ ≠ 0 := by
    rw [ccDenom_perm_swap z₂ z₁ z₃]
    exact neg_ne_zero.mpr hd
  rw [cc_eq, cc_eq]
  field_simp
  simp only [ccNum, ccDenom]
  ring

/-- 9. The endgame: the circumcenter construction preserves the "same-radius" relation
along the two rays from `Q`. -/
lemma endgame {Q lam1 lam2 OA A E : ℂ}
    (hA : A ≠ Q) (hE : E ≠ Q) (hOA : OA ≠ Q)
    (hd : ccDenom 1 lam1 (lam2 * lam1) ≠ 0)
    (hR : dist OA A = dist OA E) :
    dist (cc OA (Q + lam1 * (OA - Q)) (Q + lam2 * lam1 * (OA - Q)))
        (cc A (Q + lam1 * (A - Q)) (Q + lam2 * lam1 * (A - Q)))
    =
    dist (cc OA (Q + lam1 * (OA - Q)) (Q + lam2 * lam1 * (OA - Q)))
        (cc E (Q + lam1 * (E - Q)) (Q + lam2 * lam1 * (E - Q))) := by
  set c := cc 1 lam1 (lam2 * lam1) with hc
  have hAw : A - Q ≠ 0 := sub_ne_zero.mpr hA
  have hEw : E - Q ≠ 0 := sub_ne_zero.mpr hE
  have hOw : OA - Q ≠ 0 := sub_ne_zero.mpr hOA
  have hA' : cc A (Q + lam1 * (A - Q)) (Q + lam2 * lam1 * (A - Q)) = (A - Q) * c + Q := by
    have h := cc_smul_add (b := Q) hAw hd
    rw [show (A - Q) * 1 + Q = A by ring,
      show (A - Q) * lam1 + Q = Q + lam1 * (A - Q) by ring,
      show (A - Q) * (lam2 * lam1) + Q = Q + lam2 * lam1 * (A - Q) by ring] at h
    exact h
  have hE' : cc E (Q + lam1 * (E - Q)) (Q + lam2 * lam1 * (E - Q)) = (E - Q) * c + Q := by
    have h := cc_smul_add (b := Q) hEw hd
    rw [show (E - Q) * 1 + Q = E by ring,
      show (E - Q) * lam1 + Q = Q + lam1 * (E - Q) by ring,
      show (E - Q) * (lam2 * lam1) + Q = Q + lam2 * lam1 * (E - Q) by ring] at h
    exact h
  have hO' : cc OA (Q + lam1 * (OA - Q)) (Q + lam2 * lam1 * (OA - Q)) = (OA - Q) * c + Q := by
    have h := cc_smul_add (b := Q) hOw hd
    rw [show (OA - Q) * 1 + Q = OA by ring,
      show (OA - Q) * lam1 + Q = Q + lam1 * (OA - Q) by ring,
      show (OA - Q) * (lam2 * lam1) + Q = Q + lam2 * lam1 * (OA - Q) by ring] at h
    exact h
  rw [hA', hE', hO']
  have key : ∀ x y : ℂ, dist ((x - Q) * c + Q) ((y - Q) * c + Q) = ‖c‖ * dist x y := by
    intro x y
    rw [Complex.dist_eq, Complex.dist_eq]
    have hxy : (x - Q) * c + Q - ((y - Q) * c + Q) = c * (x - y) := by ring
    rw [hxy, norm_mul]
  rw [key OA A, key OA E, hR]

end AlgebraicCore

section GeometricFrontend

/-!
### C1: the Miquel point
-/

/-- Circumcircle of `AFE`. -/
noncomputable def miquelS₁ {A F E : ℂ} (hAFE : ¬Collinear ℝ {A, F, E}) : Sphere ℂ :=
  triCircumsphere hAFE
/-- Circumcircle of `BDF`. -/
noncomputable def miquelS₂ {B D F : ℂ} (hBDF : ¬Collinear ℝ {B, D, F}) : Sphere ℂ :=
  triCircumsphere hBDF
/-- Circumcircle of `CED`. -/
noncomputable def miquelS₃ {C E D : ℂ} (hCED : ¬Collinear ℝ {C, E, D}) : Sphere ℂ :=
  triCircumsphere hCED

/-- Direction perpendicular to the line of centers of s₁ and s₂. -/
noncomputable def miquelV {A F E B D : ℂ} (hAFE : ¬Collinear ℝ {A, F, E})
    (hBDF : ¬Collinear ℝ {B, D, F}) : ℂ :=
  (Complex.orientation).rightAngleRotation
    ((miquelS₂ hBDF).center - (miquelS₁ hAFE).center)

/-- The Miquel point: second intersection of the circumcircles of AFE and BDF. -/
noncomputable def miquelQ {A F E B D : ℂ} (hAFE : ¬Collinear ℝ {A, F, E})
    (hBDF : ¬Collinear ℝ {B, D, F}) : ℂ :=
  Sphere.secondInter (miquelS₁ hAFE) F (miquelV hAFE hBDF)

lemma F_mem_miquelS₁ {A F E : ℂ} (hAFE : ¬Collinear ℝ {A, F, E}) :
    F ∈ miquelS₁ hAFE :=
  Affine.Simplex.mem_circumsphere _ 1

lemma A_mem_miquelS₁ {A F E : ℂ} (hAFE : ¬Collinear ℝ {A, F, E}) :
    A ∈ miquelS₁ hAFE :=
  Affine.Simplex.mem_circumsphere _ 0

lemma E_mem_miquelS₁ {A F E : ℂ} (hAFE : ¬Collinear ℝ {A, F, E}) :
    E ∈ miquelS₁ hAFE :=
  Affine.Simplex.mem_circumsphere _ 2

lemma B_mem_miquelS₂ {B D F : ℂ} (hBDF : ¬Collinear ℝ {B, D, F}) :
    B ∈ miquelS₂ hBDF :=
  Affine.Simplex.mem_circumsphere _ 0

lemma D_mem_miquelS₂ {B D F : ℂ} (hBDF : ¬Collinear ℝ {B, D, F}) :
    D ∈ miquelS₂ hBDF :=
  Affine.Simplex.mem_circumsphere _ 1

lemma F_mem_miquelS₂ {B D F : ℂ} (hBDF : ¬Collinear ℝ {B, D, F}) :
    F ∈ miquelS₂ hBDF :=
  Affine.Simplex.mem_circumsphere _ 2

lemma C_mem_miquelS₃ {C E D : ℂ} (hCED : ¬Collinear ℝ {C, E, D}) :
    C ∈ miquelS₃ hCED :=
  Affine.Simplex.mem_circumsphere _ 0

lemma E_mem_miquelS₃ {C E D : ℂ} (hCED : ¬Collinear ℝ {C, E, D}) :
    E ∈ miquelS₃ hCED :=
  Affine.Simplex.mem_circumsphere _ 1

lemma D_mem_miquelS₃ {C E D : ℂ} (hCED : ¬Collinear ℝ {C, E, D}) :
    D ∈ miquelS₃ hCED :=
  Affine.Simplex.mem_circumsphere _ 2

/-- The circumcenters of `AFE` and `BDF` are distinct: a common center would
be equidistant from the three collinear points `A`, `B`, `F`. -/
lemma miquel_centers_ne {A F E B D : ℂ} (hAFE : ¬Collinear ℝ {A, F, E})
    (hBDF : ¬Collinear ℝ {B, D, F}) (hF : Wbtw ℝ A F B) :
    (miquelS₁ hAFE).center ≠ (miquelS₂ hBDF).center := by
  intro h
  have hAF : A ≠ F := ne₁₂_of_not_collinear hAFE
  have hBF : B ≠ F := ne₁₃_of_not_collinear hBDF
  have hAB : A ≠ B := by
    intro hAB
    apply hAF
    have hs := hF.mem_segment
    rw [hAB, segment_same] at hs
    rw [Set.mem_singleton_iff] at hs
    exact hAB.trans hs.symm
  have hd1 : dist (miquelS₁ hAFE).center A = dist (miquelS₁ hAFE).center F :=
    dist_center_eq_dist_center_of_mem_sphere' (A_mem_miquelS₁ hAFE) (F_mem_miquelS₁ hAFE)
  have hd2 : dist (miquelS₂ hBDF).center B = dist (miquelS₂ hBDF).center F :=
    dist_center_eq_dist_center_of_mem_sphere' (B_mem_miquelS₂ hBDF) (F_mem_miquelS₂ hBDF)
  rw [← h] at hd2
  -- three collinear points `A B F` on the sphere centered at `c` with radius `dist c F`
  set c := (miquelS₁ hAFE).center with hc
  set r := dist c F with hr
  have hAs : A ∈ (⟨c, r⟩ : Sphere ℂ) := by
    rw [mem_sphere]
    exact dist_comm A c ▸ hd1
  have hBs : B ∈ (⟨c, r⟩ : Sphere ℂ) := by
    rw [mem_sphere]
    exact dist_comm B c ▸ hd2
  have hFs : F ∈ (⟨c, r⟩ : Sphere ℂ) := by
    rw [mem_sphere]
    show dist F c = r
    rw [hr]
    exact dist_comm F c
  -- on a sphere, a point of the line through `F` is `F` or the second intersection
  have hA' := (Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair hFs
    (right_mem_affineSpan_pair ℝ F A)).mpr hAs
  have hcol := hF.collinear
  have hBline : B ∈ line[ℝ, F, A] := by
    have h1 : affineSpan ℝ ({A, F, B} : Set ℂ) = line[ℝ, A, F] :=
      (hcol.affineSpan_eq_of_ne (Set.mem_insert A _)
        (Set.mem_insert_of_mem _ (Set.mem_insert F _)) hAF).symm
    have h2 : B ∈ affineSpan ℝ ({A, F, B} : Set ℂ) :=
      subset_affineSpan ℝ _
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton B)))
    rw [h1, Set.pair_comm A F] at h2
    exact h2
  have hB' := (Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair hFs hBline).mpr hBs
  rcases hA' with hA' | hA'
  · exact hAF hA'
  rcases hB' with hB' | hB'
  · exact hBF hB'
  exact hAB (hA'.trans hB'.symm)

lemma miquelV_ne_zero {A F E B D : ℂ} (hAFE : ¬Collinear ℝ {A, F, E})
    (hBDF : ¬Collinear ℝ {B, D, F}) (hF : Wbtw ℝ A F B) :
    miquelV hAFE hBDF ≠ 0 := by
  have hc := miquel_centers_ne hAFE hBDF hF
  rw [miquelV]
  have hx : (miquelS₂ hBDF).center - (miquelS₁ hAFE).center ≠ 0 :=
    sub_ne_zero.mpr hc.symm
  exact fun hv => hx (((Complex.orientation).rightAngleRotation.map_eq_zero_iff).mp hv)

lemma miquelQ_mem_s₁ {A F E B D : ℂ} (hAFE : ¬Collinear ℝ {A, F, E})
    (hBDF : ¬Collinear ℝ {B, D, F}) :
    miquelQ hAFE hBDF ∈ miquelS₁ hAFE := by
  rw [miquelQ, Sphere.secondInter_mem]
  exact F_mem_miquelS₁ hAFE

lemma miquelQ_mem_s₂ {A F E B D : ℂ} (hAFE : ¬Collinear ℝ {A, F, E})
    (hBDF : ¬Collinear ℝ {B, D, F}) :
    miquelQ hAFE hBDF ∈ miquelS₂ hBDF := by
  have key : Sphere.secondInter (miquelS₁ hAFE) F (miquelV hAFE hBDF)
      = Sphere.secondInter (miquelS₂ hBDF) F (miquelV hAFE hBDF) := by
    have hin : ⟪miquelV hAFE hBDF, F -ᵥ (miquelS₁ hAFE).center⟫
        = ⟪miquelV hAFE hBDF, F -ᵥ (miquelS₂ hBDF).center⟫ := by
      rw [← sub_eq_zero, ← inner_sub_right]
      have hvec : (F -ᵥ (miquelS₁ hAFE).center) - (F -ᵥ (miquelS₂ hBDF).center)
          = (miquelS₂ hBDF).center -ᵥ (miquelS₁ hAFE).center := by
        rw [vsub_sub_vsub_cancel_left]
      rw [hvec, vsub_eq_sub, miquelV, Orientation.inner_rightAngleRotation_self]
    rw [Sphere.secondInter, Sphere.secondInter, hin]
  rw [miquelQ, key, Sphere.secondInter_mem]
  exact F_mem_miquelS₂ hBDF


lemma mem_line_of_collinear {X Y Z : ℂ} (h : Collinear ℝ {X, Y, Z}) (hne : Y ≠ Z) :
    X ∈ line[ℝ, Y, Z] := by
  have h1 : affineSpan ℝ ({X, Y, Z} : Set ℂ) = line[ℝ, Y, Z] :=
    (h.affineSpan_eq_of_ne (Set.mem_insert_of_mem _ (Set.mem_insert Y _))
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton Z))) hne).symm
  have h2 : X ∈ affineSpan ℝ ({X, Y, Z} : Set ℂ) := subset_affineSpan ℝ _ (Set.mem_insert X _)
  rwa [h1] at h2

lemma mem_line_of_wbtw_right {A F B : ℂ} (hF : Wbtw ℝ A F B) (hAF : A ≠ F) :
    B ∈ line[ℝ, F, A] := by
  have hcol := hF.collinear
  have h1 : affineSpan ℝ ({A, F, B} : Set ℂ) = line[ℝ, A, F] :=
    (hcol.affineSpan_eq_of_ne (Set.mem_insert A _)
      (Set.mem_insert_of_mem _ (Set.mem_insert F _)) hAF).symm
  have h2 : B ∈ affineSpan ℝ ({A, F, B} : Set ℂ) :=
    subset_affineSpan ℝ _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton B)))
  rw [h1, Set.pair_comm A F] at h2
  exact h2

lemma miquelQ_ne_A {A F E B D : ℂ} (hAFE : ¬Collinear ℝ {A, F, E})
    (hBDF : ¬Collinear ℝ {B, D, F}) (hF : Wbtw ℝ A F B) :
    miquelQ hAFE hBDF ≠ A := by
  intro hQA
  have hAF : A ≠ F := ne₁₂_of_not_collinear hAFE
  have hBF : B ≠ F := ne₁₃_of_not_collinear hBDF
  have hAs : A ∈ miquelS₂ hBDF := hQA ▸ miquelQ_mem_s₂ hAFE hBDF
  -- `A` and `B` both lie on circle `BDF` and on the line `FB`
  have hA' := (Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
    (F_mem_miquelS₂ hBDF) (mem_line_of_collinear hF.collinear hBF.symm)).mpr hAs
  have hB' := (Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
    (F_mem_miquelS₂ hBDF) (right_mem_affineSpan_pair ℝ F B)).mpr (B_mem_miquelS₂ hBDF)
  rcases hB' with hB' | hB'
  · exact absurd hB' hBF
  rcases hA' with hA' | hA'
  · exact hAF hA'
  · have hAB : A = B := hA'.trans hB'.symm
    rw [hAB] at hF
    have hs := hF.mem_segment
    rw [segment_same, Set.mem_singleton_iff] at hs
    exact hBF hs.symm

lemma miquelQ_ne_B {A F E B D : ℂ} (hAFE : ¬Collinear ℝ {A, F, E})
    (hBDF : ¬Collinear ℝ {B, D, F}) (hF : Wbtw ℝ A F B) :
    miquelQ hAFE hBDF ≠ B := by
  intro hQB
  have hAF : A ≠ F := ne₁₂_of_not_collinear hAFE
  have hBF : B ≠ F := ne₁₃_of_not_collinear hBDF
  have hBs : B ∈ miquelS₁ hAFE := hQB ▸ miquelQ_mem_s₁ hAFE hBDF
  -- `B` and `A` both lie on circle `AFE` and on the line `FA`
  have hB' := (Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
    (F_mem_miquelS₁ hAFE) (mem_line_of_wbtw_right hF hAF)).mpr hBs
  have hA' := (Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
    (F_mem_miquelS₁ hAFE) (right_mem_affineSpan_pair ℝ F A)).mpr (A_mem_miquelS₁ hAFE)
  rcases hA' with hA' | hA'
  · exact absurd hA' hAF
  rcases hB' with hB' | hB'
  · exact hBF hB'
  · have hBA : B = A := hB'.trans hA'.symm
    rw [hBA] at hF
    have hs := hF.mem_segment
    rw [segment_same, Set.mem_singleton_iff] at hs
    exact hBF (hBA.trans hs.symm)

lemma miquelQ_ne_C {A F E B D C : ℂ} (hABC : ¬Collinear ℝ {A, B, C})
    (hAFE : ¬Collinear ℝ {A, F, E}) (hCED : ¬Collinear ℝ {C, E, D})
    (hBDF : ¬Collinear ℝ {B, D, F}) (hE : Wbtw ℝ C E A) :
    miquelQ hAFE hBDF ≠ C := by
  intro hQC
  have hCA : C ≠ A := (ne₁₃_of_not_collinear hABC).symm
  have hCE : C ≠ E := ne₁₂_of_not_collinear hCED
  have hAE : A ≠ E := ne₁₃_of_not_collinear hAFE
  have hCs : C ∈ miquelS₁ hAFE := hQC ▸ miquelQ_mem_s₁ hAFE hBDF
  -- `C` and `E` both lie on circle `AFE` and on the line `AE`
  have hcol : Collinear ℝ ({C, A, E} : Set ℂ) := by
    have h2 := hE.collinear
    rwa [Set.pair_comm E A] at h2
  have hC' := (Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
    (A_mem_miquelS₁ hAFE) (mem_line_of_collinear hcol hAE)).mpr hCs
  have hE' := (Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
    (A_mem_miquelS₁ hAFE) (right_mem_affineSpan_pair ℝ A E)).mpr (E_mem_miquelS₁ hAFE)
  rcases hE' with hE' | hE'
  · exact absurd hE' hAE.symm
  rcases hC' with hC' | hC'
  · exact hCA hC'
  · exact hCE (hC'.trans hE'.symm)



/-!
### Sign machinery: the cross product `cprod` and signs of oriented angles
-/

/-- The cross product `Im(conj v * w)` of two complex numbers (twice the
signed area of the parallelogram they span). -/
def cprod (v w : ℂ) : ℝ := (conj v * w).im

lemma cprod_eq (v w : ℂ) : cprod v w = v.re * w.im - v.im * w.re := by
  simp [cprod, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

lemma oangle_eq_arg (v w : ℂ) :
    Complex.orientation.oangle v w = (Complex.arg (w * conj v) : Real.Angle) := by
  rw [Orientation.oangle, Complex.kahler]

/-- The sign of the oriented angle from `v` to `w` is the sign of their
cross product.  This is the bridge between angle signs and algebra. -/
lemma oangle_sign_eq_sign_cprod (v w : ℂ) (hv : v ≠ 0) (hw : w ≠ 0) :
    (Complex.orientation.oangle v w).sign = SignType.sign (cprod v w) := by
  have hz : w * conj v ≠ 0 := mul_ne_zero hw (by simp [hv])
  rw [oangle_eq_arg, Real.Angle.sign, Real.Angle.sin_coe, Complex.sin_arg]
  show SignType.sign ((w * conj v).im / ‖w * conj v‖) = SignType.sign ((conj v * w).im)
  rw [div_eq_mul_inv, sign_mul, sign_pos (inv_pos.mpr (norm_pos_iff.mpr hz)), mul_one,
    mul_comm (conj v) w]

/-- The positive orientation on `ℂ` used for oriented angles. -/
lemma positiveOrientation_eq_complex :
    (Module.Oriented.positiveOrientation : Orientation ℝ ℂ (Fin 2)) = Complex.orientation := rfl

/-- The sign of the oriented angle `∡ x y z` is the sign of the cross
product of the two leg vectors. -/
lemma oangle'_sign (x y z : ℂ) (hx : x ≠ y) (hz : z ≠ y) :
    (∡ x y z).sign = SignType.sign (cprod (x - y) (z - y)) := by
  have h : ∡ x y z = Complex.orientation.oangle (x - y) (z - y) := by
    rw [oangle, vsub_eq_sub, vsub_eq_sub]
    rfl
  rw [h]
  exact oangle_sign_eq_sign_cprod _ _ (sub_ne_zero.mpr hx) (sub_ne_zero.mpr hz)

lemma cprod_self (v : ℂ) : cprod v v = 0 := by simp [cprod_eq]; ring
lemma cprod_add_left (a b c : ℂ) : cprod (a + b) c = cprod a c + cprod b c := by
  simp [cprod_eq, Complex.add_re, Complex.add_im]; ring
lemma cprod_add_right (a b c : ℂ) : cprod a (b + c) = cprod a b + cprod a c := by
  simp [cprod_eq, Complex.add_re, Complex.add_im]; ring
lemma cprod_neg_left (a b : ℂ) : cprod (-a) b = -cprod a b := by
  simp [cprod_eq, Complex.neg_re, Complex.neg_im]; ring
lemma cprod_neg_right (a b : ℂ) : cprod a (-b) = -cprod a b := by
  simp [cprod_eq, Complex.neg_re, Complex.neg_im]; ring
lemma cprod_smul_left (t : ℝ) (v w : ℂ) : cprod (t • v) w = t * cprod v w := by
  rw [RCLike.real_smul_eq_coe_mul]
  simp [cprod_eq, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring
lemma cprod_smul_right (t : ℝ) (v w : ℂ) : cprod v (t • w) = t * cprod v w := by
  rw [RCLike.real_smul_eq_coe_mul]
  simp [cprod_eq, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The denominator `ccDenom A B C` is `2i` times the cross product of the
two sides of the triangle at `A`. -/
lemma ccDenom_eq_two_mul_I_mul_cprod (A B C : ℂ) :
    ccDenom A B C = 2 * Complex.I * (cprod (B - A) (C - A) : ℂ) := by
  rw [ccDenom_eq]
  apply Complex.ext <;>
    simp [cprod_eq, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im] <;> ring

lemma cprod_ne_zero_of_not_collinear {A B C : ℂ} (h : ¬Collinear ℝ {A, B, C}) :
    cprod (B - A) (C - A) ≠ 0 := by
  have hd := ccDenom_ne_zero_of_not_collinear _ _ _ h
  rw [ccDenom_eq_two_mul_I_mul_cprod] at hd
  intro hz
  rw [hz, Complex.ofReal_zero, mul_zero] at hd
  exact hd rfl

/-- Extract the ratio of a point on an open segment. -/
lemma wbtw_param {A F B : ℂ} (hF : Wbtw ℝ A F B) (hAF : A ≠ F) (hBF : B ≠ F) :
    ∃ f : ℝ, 0 < f ∧ f < 1 ∧ F = (1 - f) • A + f • B := by
  have hs := hF.mem_segment
  rw [segment_eq_image_lineMap] at hs
  obtain ⟨f, hfi, hfl⟩ := hs
  rw [Set.mem_Icc] at hfi
  have hf0 : f ≠ 0 := by
    intro hf0
    rw [hf0, AffineMap.lineMap_apply_zero] at hfl
    exact hAF hfl
  have hf1 : f ≠ 1 := by
    intro hf1
    rw [hf1, AffineMap.lineMap_apply_one] at hfl
    exact hBF hfl
  have hval : F = (1 - f) • A + f • B := by
    rw [← hfl, AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub]
    module
  exact ⟨f, lt_of_le_of_ne hfi.1 hf0.symm, lt_of_le_of_ne hfi.2 hf1, hval⟩

/-- The oriented angle `∠` at `A` of the triangle is nonzero. -/
lemma oangle_sign_ne_zero_of_not_collinear {A B C : ℂ} (h : ¬Collinear ℝ {A, B, C}) :
    (∡ B A C).sign ≠ 0 := by
  rw [oangle'_sign _ _ _ (ne₁₂_of_not_collinear h).symm (ne₁₃_of_not_collinear h).symm]
  exact sign_ne_zero.mpr (cprod_ne_zero_of_not_collinear h)

lemma oangle_eq_of_angle_eq_of_sign_eq {x y z x' y' z' : ℂ}
    (h : ∠ x y z = ∠ x' y' z') (hs : (∡ x y z).sign = (∡ x' y' z').sign)
    (hx : x ≠ y) (hz : z ≠ y) (hx' : x' ≠ y') (hz' : z' ≠ y') :
    ∡ x y z = ∡ x' y' z' := by
  rw [Real.Angle.eq_iff_sign_eq_and_abs_toReal_eq]
  refine ⟨hs, ?_⟩
  rw [← angle_eq_abs_oangle_toReal hx hz, ← angle_eq_abs_oangle_toReal hx' hz', h]

lemma cprod_skew (v w : ℂ) : cprod w v = -cprod v w := by simp [cprod_eq]; ring

lemma real_smul_re' (t : ℝ) (z : ℂ) : (t • z).re = t * z.re := by
  rw [RCLike.real_smul_eq_coe_mul]
  show ((t : ℂ) * z).re = t * z.re
  rw [Complex.re_ofReal_mul]

lemma real_smul_im' (t : ℝ) (z : ℂ) : (t • z).im = t * z.im := by
  rw [RCLike.real_smul_eq_coe_mul]
  show ((t : ℂ) * z).im = t * z.im
  rw [Complex.im_ofReal_mul]

/-- Cross product of two vectors given in a common basis. -/
lemma cprod_mk (a₁ a₂ b₁ b₂ : ℝ) (u w : ℂ) :
    cprod (a₁ • u + a₂ • w) (b₁ • u + b₂ • w) = (a₁ * b₂ - a₂ * b₁) * cprod u w := by
  rw [cprod_eq, cprod_eq]
  simp only [real_smul_re', real_smul_im', Complex.add_re, Complex.add_im]
  ring

/-- Sign of the oriented angle in terms of the cross product of a common
basis: auxiliary bundle for the corner computations. -/
lemma sign_oangle_of_cprod {x y z A B C : ℂ} {a₁ a₂ b₁ b₂ : ℝ}
    (hx : x ≠ y) (hz : z ≠ y)
    (h1 : x - y = a₁ • (B - A) + a₂ • (C - A))
    (h2 : z - y = b₁ • (B - A) + b₂ • (C - A)) :
    (∡ x y z).sign = SignType.sign ((a₁ * b₂ - a₂ * b₁) * cprod (B - A) (C - A)) := by
  rw [oangle'_sign _ _ _ hx hz, h1, h2, cprod_mk]

/-- The sign of `∡ B A C` is the sign of the cross product of the sides. -/
lemma sign_oangle_BAC {A B C : ℂ} (hBA : B ≠ A) (hCA : C ≠ A) :
    (∡ B A C).sign = SignType.sign (cprod (B - A) (C - A)) :=
  oangle'_sign _ _ _ hBA hCA

lemma sign_oangle_AFE {A B C E F : ℂ}
    (hF : Wbtw ℝ A F B) (hE : Wbtw ℝ C E A)
    (hAF : A ≠ F) (hBF : B ≠ F) (hCE : C ≠ E) (hAE : A ≠ E) (hFE : F ≠ E)
    (hBA : B ≠ A) (hCA : C ≠ A) :
    (∡ A F E).sign = -(∡ B A C).sign := by
  obtain ⟨f, hf0, hf1, hF'⟩ := wbtw_param hF hAF hBF
  obtain ⟨e, he0, he1, hE'⟩ := wbtw_param hE hCE hAE
  rw [sign_oangle_of_cprod hAF hFE.symm
    (show A - F = (-f) • (B - A) + (0 : ℝ) • (C - A) by rw [hF']; module)
    (show E - F = (-f) • (B - A) + (1 - e) • (C - A) by rw [hF', hE']; module)]
  rw [sign_oangle_BAC hBA hCA]
  have hc : (-f) * (1 - e) - (0 : ℝ) * (-f) < 0 := by nlinarith
  rw [sign_mul, sign_eq_neg_one_iff.mpr hc, neg_mul, one_mul]

lemma sign_oangle_FEA {A B C E F : ℂ}
    (hF : Wbtw ℝ A F B) (hE : Wbtw ℝ C E A)
    (hAF : A ≠ F) (hBF : B ≠ F) (hCE : C ≠ E) (hAE : A ≠ E) (hFE : F ≠ E)
    (hBA : B ≠ A) (hCA : C ≠ A) :
    (∡ F E A).sign = -(∡ B A C).sign := by
  obtain ⟨f, hf0, hf1, hF'⟩ := wbtw_param hF hAF hBF
  obtain ⟨e, he0, he1, hE'⟩ := wbtw_param hE hCE hAE
  rw [sign_oangle_of_cprod hFE hAE
    (show F - E = f • (B - A) + (-(1 - e)) • (C - A) by rw [hF', hE']; module)
    (show A - E = (0 : ℝ) • (B - A) + (-(1 - e)) • (C - A) by rw [hE']; module)]
  rw [sign_oangle_BAC hBA hCA]
  have hc : f * (-(1 - e)) - (-(1 - e)) * (0 : ℝ) < 0 := by nlinarith
  rw [sign_mul, sign_eq_neg_one_iff.mpr hc, neg_mul, one_mul]

lemma sign_oangle_BDF {A B C D F : ℂ}
    (hD : Wbtw ℝ B D C) (hF : Wbtw ℝ A F B)
    (hBD : B ≠ D) (hCD : C ≠ D) (hAF : A ≠ F) (hBF : B ≠ F) (hDF : D ≠ F)
    (hBA : B ≠ A) (hCA : C ≠ A) :
    (∡ B D F).sign = -(∡ B A C).sign := by
  obtain ⟨d, hd0, hd1, hD'⟩ := wbtw_param hD hBD hCD
  obtain ⟨f, hf0, hf1, hF'⟩ := wbtw_param hF hAF hBF
  rw [sign_oangle_of_cprod hBD hDF.symm
    (show B - D = d • (B - A) + (-d) • (C - A) by rw [hD']; module)
    (show F - D = (f - 1 + d) • (B - A) + (-d) • (C - A) by rw [hD', hF']; module)]
  rw [sign_oangle_BAC hBA hCA]
  have hc : d * (-d) - (-d) * (f - 1 + d) < 0 := by nlinarith
  rw [sign_mul, sign_eq_neg_one_iff.mpr hc, neg_mul, one_mul]

lemma sign_oangle_BFD {A B C D F : ℂ}
    (hD : Wbtw ℝ B D C) (hF : Wbtw ℝ A F B)
    (hBD : B ≠ D) (hCD : C ≠ D) (hAF : A ≠ F) (hBF : B ≠ F) (hDF : D ≠ F)
    (hBA : B ≠ A) (hCA : C ≠ A) :
    (∡ B F D).sign = (∡ B A C).sign := by
  obtain ⟨d, hd0, hd1, hD'⟩ := wbtw_param hD hBD hCD
  obtain ⟨f, hf0, hf1, hF'⟩ := wbtw_param hF hAF hBF
  rw [sign_oangle_of_cprod hBF hDF
    (show B - F = (1 - f) • (B - A) + (0 : ℝ) • (C - A) by rw [hF']; module)
    (show D - F = (1 - f - d) • (B - A) + d • (C - A) by rw [hD', hF']; module)]
  rw [sign_oangle_BAC hBA hCA]
  have hc : 0 < (1 - f) * d - (0 : ℝ) * (1 - f - d) := by nlinarith
  rw [sign_mul, sign_pos hc, one_mul]

lemma sign_oangle_CED {A B C D E : ℂ}
    (hD : Wbtw ℝ B D C) (hE : Wbtw ℝ C E A)
    (hBD : B ≠ D) (hCD : C ≠ D) (hCE : C ≠ E) (hAE : A ≠ E) (hDE : D ≠ E)
    (hBA : B ≠ A) (hCA : C ≠ A) :
    (∡ C E D).sign = -(∡ B A C).sign := by
  obtain ⟨d, hd0, hd1, hD'⟩ := wbtw_param hD hBD hCD
  obtain ⟨e, he0, he1, hE'⟩ := wbtw_param hE hCE hAE
  rw [sign_oangle_of_cprod hCE hDE
    (show C - E = (0 : ℝ) • (B - A) + e • (C - A) by rw [hE']; module)
    (show D - E = (1 - d) • (B - A) + (d - 1 + e) • (C - A) by rw [hD', hE']; module)]
  rw [sign_oangle_BAC hBA hCA]
  have hc : (0 : ℝ) * (d - 1 + e) - e * (1 - d) < 0 := by nlinarith
  rw [sign_mul, sign_eq_neg_one_iff.mpr hc, neg_mul, one_mul]

lemma sign_oangle_EDC {A B C D E : ℂ}
    (hD : Wbtw ℝ B D C) (hE : Wbtw ℝ C E A)
    (hBD : B ≠ D) (hCD : C ≠ D) (hCE : C ≠ E) (hAE : A ≠ E) (hDE : D ≠ E)
    (hBA : B ≠ A) (hCA : C ≠ A) :
    (∡ E D C).sign = -(∡ B A C).sign := by
  obtain ⟨d, hd0, hd1, hD'⟩ := wbtw_param hD hBD hCD
  obtain ⟨e, he0, he1, hE'⟩ := wbtw_param hE hCE hAE
  rw [sign_oangle_of_cprod hDE.symm hCD
    (show E - D = (d - 1) • (B - A) + (1 - d - e) • (C - A) by rw [hD', hE']; module)
    (show C - D = (d - 1) • (B - A) + (1 - d) • (C - A) by rw [hD']; module)]
  rw [sign_oangle_BAC hBA hCA]
  have hc : (d - 1) * (1 - d) - (1 - d - e) * (d - 1) < 0 := by nlinarith
  rw [sign_mul, sign_eq_neg_one_iff.mpr hc, neg_mul, one_mul]

/-- Twice an oriented angle negated is twice the reversed angle. -/
lemma two_zsmul_neg_oangle_rev (x y z : ℂ) : (-2 : ℤ) • ∡ x y z = (2 : ℤ) • ∡ z y x := by
  rw [neg_smul, oangle_rev x y z, smul_neg]

/-- Ray equality of oriented angles: replacing the first leg vector by a
positive scalar multiple of it does not change the oriented angle. -/
lemma oangle_eq_of_smul_left_pos {x y z w : ℂ} (_hx : x ≠ y) (_hz : z ≠ y) (_hw : w ≠ y)
    {t : ℝ} (ht : 0 < t) (h : x - y = t • (z - y)) : ∡ x y w = ∡ z y w := by
  have e1 : ∡ x y w = Complex.orientation.oangle (t • (z - y)) (w - y) := by
    rw [oangle, vsub_eq_sub, vsub_eq_sub, h]
    rfl
  have e2 : ∡ z y w = Complex.orientation.oangle (z - y) (w - y) := by
    rw [oangle, vsub_eq_sub, vsub_eq_sub]
    rfl
  rw [e1, e2, Orientation.oangle_smul_left_of_pos Complex.orientation _ _ ht]

/-- Ray equality of oriented angles: replacing the second leg vector by a
positive scalar multiple of it does not change the oriented angle. -/
lemma oangle_eq_of_smul_right_pos {x y z w : ℂ} (_hx : x ≠ y) (_hz : z ≠ y) (_hw : w ≠ y)
    {t : ℝ} (ht : 0 < t) (h : w - y = t • (z - y)) : ∡ x y w = ∡ x y z := by
  have e1 : ∡ x y w = Complex.orientation.oangle (x - y) (t • (z - y)) := by
    rw [oangle, vsub_eq_sub, vsub_eq_sub, h]
    rfl
  have e2 : ∡ x y z = Complex.orientation.oangle (x - y) (z - y) := by
    rw [oangle, vsub_eq_sub, vsub_eq_sub]
    rfl
  rw [e1, e2, Orientation.oangle_smul_right_of_pos Complex.orientation _ _ ht]

/-- The `2 •` version of `oangle_eq_of_smul_left_pos`, allowing any nonzero
scalar (in particular negative scalars). -/
lemma two_zsmul_oangle_eq_of_smul_left {x y z w : ℂ} (_hx : x ≠ y) (_hz : z ≠ y) (_hw : w ≠ y)
    {t : ℝ} (ht : t ≠ 0) (h : x - y = t • (z - y)) :
    (2 : ℤ) • ∡ x y w = (2 : ℤ) • ∡ z y w := by
  have e1 : ∡ x y w = Complex.orientation.oangle (t • (z - y)) (w - y) := by
    rw [oangle, vsub_eq_sub, vsub_eq_sub, h]
    rfl
  have e2 : ∡ z y w = Complex.orientation.oangle (z - y) (w - y) := by
    rw [oangle, vsub_eq_sub, vsub_eq_sub]
    rfl
  rw [e1, e2, Orientation.two_zsmul_oangle_smul_left_of_ne_zero Complex.orientation _ _ ht]

/-- The `2 •` version of `oangle_eq_of_smul_right_pos`. -/
lemma two_zsmul_oangle_eq_of_smul_right {x y z w : ℂ} (_hx : x ≠ y) (_hz : z ≠ y) (_hw : w ≠ y)
    {t : ℝ} (ht : t ≠ 0) (h : w - y = t • (z - y)) :
    (2 : ℤ) • ∡ x y w = (2 : ℤ) • ∡ x y z := by
  have e1 : ∡ x y w = Complex.orientation.oangle (x - y) (t • (z - y)) := by
    rw [oangle, vsub_eq_sub, vsub_eq_sub, h]
    rfl
  have e2 : ∡ x y z = Complex.orientation.oangle (x - y) (z - y) := by
    rw [oangle, vsub_eq_sub, vsub_eq_sub]
    rfl
  rw [e1, e2, Orientation.two_zsmul_oangle_smul_right_of_ne_zero Complex.orientation _ _ ht]

/-- If the cross product of `x` and `y` vanishes and `x ≠ 0`, then `y` is a
real scalar multiple of `x`. -/
lemma exists_smul_of_cprod_eq_zero_right {x y : ℂ} (hx : x ≠ 0) (h : cprod x y = 0) :
    ∃ t : ℝ, y = t • x := by
  set w := conj x * y with hw_def
  have hwim : w.im = 0 := h
  have hwre : (w.re : ℂ) = w := by
    apply Complex.ext
    · simp
    · simp [hwim]
  have hn : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  have hcx : conj x ≠ 0 := by simp [hx]
  refine ⟨w.re / ‖x‖ ^ 2, ?_⟩
  apply mul_left_cancel₀ hcx
  have hsmul : ((w.re / ‖x‖ ^ 2 : ℝ) • x : ℂ) = ((w.re / ‖x‖ ^ 2 : ℝ) : ℂ) * x :=
    RCLike.real_smul_eq_coe_mul _ _
  rw [hsmul, ← hw_def]
  have h2 : conj x * (↑(w.re / ‖x‖ ^ 2) * x) = ↑(w.re / ‖x‖ ^ 2) * (conj x * x) := by
    ring
  rw [h2, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    div_mul_cancel₀ _ hn]
  exact hwre.symm

/-- The hypothesis `∠ A F E = ∠ B D F` upgraded to oriented angles (the two
oriented angles have the same sign by the corner computations). -/
lemma hα₁o {A B C D E F : ℂ}
    (hABC : ¬Collinear ℝ {A, B, C})
    (hD : Wbtw ℝ B D C) (hE : Wbtw ℝ C E A) (hF : Wbtw ℝ A F B)
    (hα₁ : ∠ A F E = ∠ B D F)
    (hAFE : ¬Collinear ℝ {A, F, E}) (hBDF : ¬Collinear ℝ {B, D, F})
    (hCED : ¬Collinear ℝ {C, E, D}) (hDEF : ¬Collinear ℝ {D, E, F}) :
    ∡ A F E = ∡ B D F := by
  have hAF : A ≠ F := ne₁₂_of_not_collinear hAFE
  have hAE : A ≠ E := ne₁₃_of_not_collinear hAFE
  have hFE : F ≠ E := (ne₂₃_of_not_collinear hDEF).symm
  have hBD : B ≠ D := ne₁₂_of_not_collinear hBDF
  have hCD : C ≠ D := ne₁₃_of_not_collinear hCED
  have hBF : B ≠ F := ne₁₃_of_not_collinear hBDF
  have hDF : D ≠ F := ne₂₃_of_not_collinear hBDF
  have hCE : C ≠ E := ne₁₂_of_not_collinear hCED
  have hBA : B ≠ A := (ne₁₂_of_not_collinear hABC).symm
  have hCA : C ≠ A := (ne₁₃_of_not_collinear hABC).symm
  have hs1 := sign_oangle_AFE hF hE hAF hBF hCE hAE hFE hBA hCA
  have hs2 := sign_oangle_BDF hD hF hBD hCD hAF hBF hDF hBA hCA
  exact oangle_eq_of_angle_eq_of_sign_eq hα₁ (hs1.trans hs2.symm) hAF hFE.symm hBD hDF.symm

/-- The hypothesis `∠ B D F = ∠ C E D` upgraded to oriented angles. -/
lemma hα₂o {A B C D E F : ℂ}
    (hABC : ¬Collinear ℝ {A, B, C})
    (hD : Wbtw ℝ B D C) (hE : Wbtw ℝ C E A) (hF : Wbtw ℝ A F B)
    (hα₂ : ∠ B D F = ∠ C E D)
    (hAFE : ¬Collinear ℝ {A, F, E}) (hBDF : ¬Collinear ℝ {B, D, F})
    (hCED : ¬Collinear ℝ {C, E, D}) (hDEF : ¬Collinear ℝ {D, E, F}) :
    ∡ B D F = ∡ C E D := by
  have hAF : A ≠ F := ne₁₂_of_not_collinear hAFE
  have hAE : A ≠ E := ne₁₃_of_not_collinear hAFE
  have hFE : F ≠ E := (ne₂₃_of_not_collinear hDEF).symm
  have hBD : B ≠ D := ne₁₂_of_not_collinear hBDF
  have hCD : C ≠ D := ne₁₃_of_not_collinear hCED
  have hBF : B ≠ F := ne₁₃_of_not_collinear hBDF
  have hDF : D ≠ F := ne₂₃_of_not_collinear hBDF
  have hCE : C ≠ E := ne₁₂_of_not_collinear hCED
  have hAE' : A ≠ E := hAE
  have hDE : D ≠ E := ne₁₂_of_not_collinear hDEF
  have hBA : B ≠ A := (ne₁₂_of_not_collinear hABC).symm
  have hCA : C ≠ A := (ne₁₃_of_not_collinear hABC).symm
  have hs2 := sign_oangle_BDF hD hF hBD hCD hAF hBF hDF hBA hCA
  have hs3 := sign_oangle_CED hD hE hBD hCD hCE hAE hDE hBA hCA
  exact oangle_eq_of_angle_eq_of_sign_eq hα₂ (hs2.trans hs3.symm) hBD hDF.symm hCE hDE

/-- The Miquel point is not `F`: otherwise the circumcircles of `AFE` and
`BDF` would be tangent at `F`, and the resulting angle relation is
incompatible with the non-degeneracy of triangle `AFE`. -/
lemma miquelQ_ne_F {A B C D E F : ℂ} (_hABC : ¬Collinear ℝ {A, B, C})
    (_hD : Wbtw ℝ B D C) (_hE : Wbtw ℝ C E A) (hF : Wbtw ℝ A F B)
    (hα₁o : ∡ A F E = ∡ B D F)
    (hAFE : ¬Collinear ℝ {A, F, E}) (hBDF : ¬Collinear ℝ {B, D, F})
    (_hCED : ¬Collinear ℝ {C, E, D}) (hDEF : ¬Collinear ℝ {D, E, F}) :
    miquelQ hAFE hBDF ≠ F := by
  intro hQF
  have hAF : A ≠ F := ne₁₂_of_not_collinear hAFE
  have hAE : A ≠ E := ne₁₃_of_not_collinear hAFE
  have hFE : F ≠ E := (ne₂₃_of_not_collinear hDEF).symm
  have hBD : B ≠ D := ne₁₂_of_not_collinear hBDF
  have hBF : B ≠ F := ne₁₃_of_not_collinear hBDF
  have hDF : D ≠ F := ne₂₃_of_not_collinear hBDF
  -- the tangency condition `⟪v, F -ᵥ c₁⟫ = 0`
  have htan : ⟪miquelV hAFE hBDF, F -ᵥ (miquelS₁ hAFE).center⟫ = 0 := by
    rw [← Sphere.secondInter_eq_self_iff]
    exact hQF
  rw [miquelV, Orientation.inner_rightAngleRotation_left] at htan
  -- so `F - c₁ = t • (c₂ - c₁)` for some real `t`
  have hc12 : (miquelS₂ hBDF).center - (miquelS₁ hAFE).center ≠ 0 :=
    sub_ne_zero.mpr (miquel_centers_ne hAFE hBDF hF).symm
  have htan' : cprod ((miquelS₂ hBDF).center - (miquelS₁ hAFE).center)
      (F -ᵥ (miquelS₁ hAFE).center) = 0 := by
    have h := htan
    rwa [Complex.areaForm] at h
  obtain ⟨t, ht⟩ := exists_smul_of_cprod_eq_zero_right hc12 htan'
  -- `t ≠ 0` and `t ≠ 1`
  have hFc1 : F -ᵥ (miquelS₁ hAFE).center ≠ 0 := by
    rw [vsub_ne_zero]
    intro hc
    have hr : 0 < (miquelS₁ hAFE).radius := by
      rw [miquelS₁, triCircumsphere, Affine.Simplex.circumsphere_radius]
      exact Affine.Simplex.circumradius_pos _
    have hmem : dist F (miquelS₁ hAFE).center = (miquelS₁ hAFE).radius :=
      mem_sphere.mp (F_mem_miquelS₁ hAFE)
    have h0 : dist F (miquelS₁ hAFE).center = 0 := by
      rw [congrArg (dist · (miquelS₁ hAFE).center) hc, dist_self]
    rw [h0] at hmem
    exact hr.ne' hmem.symm
  have ht0 : t ≠ 0 := by
    intro ht0
    rw [ht0, zero_smul] at ht
    exact hFc1 (by rw [vsub_eq_sub]; exact ht)
  have ht1 : t ≠ 1 := by
    intro ht1
    rw [ht1, one_smul] at ht
    rw [vsub_eq_sub] at ht
    have hF2 : F = (miquelS₂ hBDF).center := by linear_combination ht
    have hr : 0 < (miquelS₂ hBDF).radius := by
      rw [miquelS₂, triCircumsphere, Affine.Simplex.circumsphere_radius]
      exact Affine.Simplex.circumradius_pos _
    have hmem : dist F (miquelS₂ hBDF).center = (miquelS₂ hBDF).radius :=
      mem_sphere.mp (F_mem_miquelS₂ hBDF)
    have h0 : dist F (miquelS₂ hBDF).center = 0 := by
      rw [congrArg (dist · (miquelS₂ hBDF).center) hF2, dist_self]
    rw [h0] at hmem
    exact hr.ne' hmem.symm
  -- `c₂ - F = ((t-1)/t) • (c₁ - F)` with `(t-1)/t ≠ 0`
  have hs_ne : (t - 1)/t ≠ 0 :=
    div_ne_zero (sub_ne_zero.mpr ht1) ht0
  have hscale : (miquelS₂ hBDF).center - F =
      ((t - 1)/t) • ((miquelS₁ hAFE).center - F) := by
    have h1 : (miquelS₂ hBDF).center - F =
        (1 - t) • ((miquelS₂ hBDF).center - (miquelS₁ hAFE).center) := by
      have h2 : F -ᵥ (miquelS₁ hAFE).center =
          t • ((miquelS₂ hBDF).center - (miquelS₁ hAFE).center) := ht
      rw [vsub_eq_sub] at h2
      have h3 : (miquelS₂ hBDF).center - F =
          ((miquelS₂ hBDF).center - (miquelS₁ hAFE).center) - (F - (miquelS₁ hAFE).center) := by
        ring
      rw [h3, h2]
      module
    have h4 : (miquelS₁ hAFE).center - F =
        (-t) • ((miquelS₂ hBDF).center - (miquelS₁ hAFE).center) := by
      rw [vsub_eq_sub] at ht
      rw [(neg_sub _ _).symm, ht, ← neg_smul]
    rw [h1, h4, smul_smul]
    congr 1
    field_simp [ht0]
    ring
  -- chain A: `2∡FEA = π + 2∡c₁FA`
  have hchainA : (2 : ℤ) • ∡ F E A = π + (2 : ℤ) • ∡ (miquelS₁ hAFE).center F A := by
    have hcent : ∡ F (miquelS₁ hAFE).center A = (2 : ℤ) • ∡ F E A :=
      Sphere.oangle_center_eq_two_zsmul_oangle (F_mem_miquelS₁ hAFE) (E_mem_miquelS₁ hAFE)
        (A_mem_miquelS₁ hAFE) hFE.symm hAE.symm
    have hiso : ∡ F (miquelS₁ hAFE).center A =
        π - (2 : ℤ) • ∡ (miquelS₁ hAFE).center A F :=
      Sphere.oangle_eq_pi_sub_two_zsmul_oangle_center_left (F_mem_miquelS₁ hAFE)
        (A_mem_miquelS₁ hAFE) hAF.symm
    have hbase : ∡ (miquelS₁ hAFE).center A F = ∡ A F (miquelS₁ hAFE).center :=
      EuclideanGeometry.oangle_eq_oangle_of_dist_eq
        (dist_center_eq_dist_center_of_mem_sphere' (A_mem_miquelS₁ hAFE) (F_mem_miquelS₁ hAFE))
    have hrev : ∡ A F (miquelS₁ hAFE).center = -∡ (miquelS₁ hAFE).center F A := by
      rw [oangle_rev A F (miquelS₁ hAFE).center, neg_neg]
    rw [← hcent, hiso, hbase, hrev, smul_neg, sub_neg_eq_add]
  -- chain B: `2∡FDB = π + 2∡c₂FB`
  have hchainB : (2 : ℤ) • ∡ F D B = π + (2 : ℤ) • ∡ (miquelS₂ hBDF).center F B := by
    have hcent : ∡ F (miquelS₂ hBDF).center B = (2 : ℤ) • ∡ F D B :=
      Sphere.oangle_center_eq_two_zsmul_oangle (F_mem_miquelS₂ hBDF) (D_mem_miquelS₂ hBDF)
        (B_mem_miquelS₂ hBDF) hDF hBD.symm
    have hiso : ∡ F (miquelS₂ hBDF).center B =
        π - (2 : ℤ) • ∡ (miquelS₂ hBDF).center B F :=
      Sphere.oangle_eq_pi_sub_two_zsmul_oangle_center_left (F_mem_miquelS₂ hBDF)
        (B_mem_miquelS₂ hBDF) hBF.symm
    have hbase : ∡ (miquelS₂ hBDF).center B F = ∡ B F (miquelS₂ hBDF).center :=
      EuclideanGeometry.oangle_eq_oangle_of_dist_eq
        (dist_center_eq_dist_center_of_mem_sphere' (B_mem_miquelS₂ hBDF) (F_mem_miquelS₂ hBDF))
    have hrev : ∡ B F (miquelS₂ hBDF).center = -∡ (miquelS₂ hBDF).center F B := by
      rw [oangle_rev B F (miquelS₂ hBDF).center, neg_neg]
    rw [← hcent, hiso, hbase, hrev, smul_neg, sub_neg_eq_add]
  -- transfer through the collinear centers
  have htransfer : (2 : ℤ) • ∡ (miquelS₂ hBDF).center F B =
      (2 : ℤ) • ∡ (miquelS₁ hAFE).center F B := by
    have h1 : ∡ (miquelS₂ hBDF).center F B =
        Complex.orientation.oangle ((miquelS₂ hBDF).center - F) (B - F) := by
      rw [oangle, vsub_eq_sub, vsub_eq_sub]
      rfl
    have h2 : ∡ (miquelS₁ hAFE).center F B =
        Complex.orientation.oangle ((miquelS₁ hAFE).center - F) (B - F) := by
      rw [oangle, vsub_eq_sub, vsub_eq_sub]
      rfl
    rw [h1, hscale, h2]
    exact Orientation.two_zsmul_oangle_smul_left_of_ne_zero Complex.orientation
      ((miquelS₁ hAFE).center - F) (B - F) hs_ne
  -- combine: `2∡FDB = 2∡FEA`
  have hAB0 : (2 : ℤ) • ∡ (miquelS₁ hAFE).center F B =
      (2 : ℤ) • ∡ (miquelS₁ hAFE).center F A := by
    have hadd : ∡ (miquelS₁ hAFE).center F A + ∡ A F B = ∡ (miquelS₁ hAFE).center F B :=
      EuclideanGeometry.oangle_add (vsub_ne_zero.mp hFc1).symm hAF hBF
    have hzero : (2 : ℤ) • ∡ A F B = 0 := by
      rcases oangle_eq_zero_or_eq_pi_iff_collinear.mpr hF.collinear with h | h <;> rw [h] <;> simp
    rw [← hadd, smul_add, hzero, add_zero]
  have heq : (2 : ℤ) • ∡ F D B = (2 : ℤ) • ∡ F E A := by
    rw [hchainB, htransfer, hAB0, ← hchainA]
  -- conclude `2∡EAF = 0`
  have hsum : ∡ A F E + ∡ F E A + ∡ E A F = π :=
    oangle_add_oangle_add_oangle_eq_pi hAF.symm hFE.symm hAE
  have hs : (2 : ℤ) • ∡ A F E + (2 : ℤ) • ∡ F E A + (2 : ℤ) • ∡ E A F = 0 := by
    have h2pi : (2 : ℤ) • (π : Real.Angle) = 0 :=
      Real.Angle.two_zsmul_eq_zero_iff.mpr (Or.inr rfl)
    rw [← h2pi, ← hsum, smul_add, smul_add]
  have hfin : (2 : ℤ) • ∡ E A F = 0 := by
    have h1 : (2 : ℤ) • ∡ F D B = -((2 : ℤ) • ∡ B D F) := by
      rw [oangle_rev B D F, smul_neg]
    rw [← heq, h1, hα₁o] at hs
    rw [add_neg_cancel, zero_add] at hs
    exact hs
  -- collinearity contradiction
  have hcol : Collinear ℝ ({E, A, F} : Set ℂ) := by
    rw [← oangle_eq_zero_or_eq_pi_iff_collinear]
    exact Real.Angle.two_zsmul_eq_zero_iff.mp hfin
  have hperm : ({E, A, F} : Set ℂ) = {A, F, E} := by
    ext x
    simp [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [hperm] at hcol
  exact hAFE hcol

/-- A point lying on both lines `AC` and `BC` of a non-degenerate triangle
is `C`. -/
lemma eq_of_mem_line_line {A B C P : ℂ} (hABC : ¬Collinear ℝ {A, B, C})
    (hP1 : P ∈ line[ℝ, A, C]) (hP2 : P ∈ line[ℝ, B, C]) : P = C := by
  have hdir1 : P -ᵥ A ∈ ℝ ∙ (A -ᵥ C) := by
    have h := AffineSubspace.vsub_mem_direction hP1 (left_mem_affineSpan_pair ℝ A C)
    rwa [direction_affineSpan, vectorSpan_pair] at h
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hdir1
  have hdir2 : P -ᵥ B ∈ ℝ ∙ (B -ᵥ C) := by
    have h := AffineSubspace.vsub_mem_direction hP2 (left_mem_affineSpan_pair ℝ B C)
    rwa [direction_affineSpan, vectorSpan_pair] at h
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hdir2
  -- eliminate `P`: `(1 + r) • (A -ᵥ B) = (r - s) • (A -ᵥ C)`
  have hrel : (1 + r) • (A -ᵥ B) = (r - s) • (A -ᵥ C) := by
    have h4 : B -ᵥ C = (A -ᵥ C) - (A -ᵥ B) := by
      simp only [vsub_eq_sub]
      module
    rw [show (1 + r) • (A -ᵥ B) = (A -ᵥ B) + r • (A -ᵥ B) from by module]
    nth_rw 1 [show A -ᵥ B = (P -ᵥ B) - (P -ᵥ A) from by
      simp only [vsub_eq_sub]; module]
    rw [← hr, ← hs, h4]
    simp only [vsub_eq_sub]
    module
  by_cases hr1 : r = -1
  · rw [hr1, add_neg_cancel, zero_smul] at hrel
    have hs0 : -1 - s = 0 := by
      rcases smul_eq_zero.mp hrel.symm with h | h
      · exact h
      · exfalso
        rw [vsub_eq_sub, sub_eq_zero] at h
        exact ne₁₃_of_not_collinear hABC h
    have hs' : s = -1 := by linarith
    have hPA : P -ᵥ A = C -ᵥ A := by
      rw [← hs, hs', neg_smul, one_smul, neg_vsub_eq_vsub_rev]
    rw [vsub_eq_sub, vsub_eq_sub] at hPA
    calc P = P - A + A := (sub_add_cancel P A).symm
      _ = C - A + A := by rw [hPA]
      _ = C := sub_add_cancel C A
  · exfalso
    apply hABC
    have hr1' : (1 + r) ≠ 0 := by
      intro h'
      exact hr1 (by linarith)
    have hAB : A -ᵥ B = ((r - s)/(1 + r)) • (A -ᵥ C) := by
      have e : A -ᵥ B = (1 + r)⁻¹ • ((1 + r) • (A -ᵥ B)) :=
        (inv_smul_smul₀ hr1' (A -ᵥ B)).symm
      rw [e, hrel, smul_smul]
      congr 1
      field_simp [hr1']
    have hBl : B ∈ line[ℝ, A, C] := by
      have hline : line[ℝ, A, C] = AffineSubspace.mk' A (vectorSpan ℝ {A, C}) :=
        (AffineSubspace.eq_iff_direction_eq_of_mem (left_mem_affineSpan_pair ℝ A C)
          (AffineSubspace.self_mem_mk' A _)).mpr
          ((direction_affineSpan ℝ {A, C}).trans (AffineSubspace.direction_mk' A _).symm)
      rw [hline, AffineSubspace.mem_mk', vectorSpan_pair]
      have hBv : A -ᵥ B ∈ ℝ ∙ (A -ᵥ C) := by
        rw [hAB]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      have hBv2 : -(A -ᵥ B) ∈ ℝ ∙ (A -ᵥ C) := Submodule.neg_mem _ hBv
      rwa [neg_vsub_eq_vsub_rev] at hBv2
    have h2 : Collinear ℝ ({B, A, C} : Set ℂ) :=
      collinear_insert_iff_of_mem_affineSpan hBl |>.mpr (collinear_pair ℝ A C)
    have h3 : ({B, A, C} : Set ℂ) = {A, B, C} := by
      ext x
      simp [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [h3] at h2
    exact h2

/-- The Miquel point is not `D`. -/
lemma miquelQ_ne_D {A B C D E F : ℂ} (hABC : ¬Collinear ℝ {A, B, C})
    (hD : Wbtw ℝ B D C) (hE : Wbtw ℝ C E A) (_hF : Wbtw ℝ A F B)
    (hα₁o : ∡ A F E = ∡ B D F) (hα₂o : ∡ B D F = ∡ C E D)
    (hAFE : ¬Collinear ℝ {A, F, E}) (hBDF : ¬Collinear ℝ {B, D, F})
    (hCED : ¬Collinear ℝ {C, E, D}) (hDEF : ¬Collinear ℝ {D, E, F}) :
    miquelQ hAFE hBDF ≠ D := by
  intro hQD
  have hAF : A ≠ F := ne₁₂_of_not_collinear hAFE
  have hAE : A ≠ E := ne₁₃_of_not_collinear hAFE
  have hFE : F ≠ E := (ne₂₃_of_not_collinear hDEF).symm
  have hBD : B ≠ D := ne₁₂_of_not_collinear hBDF
  have hCD : C ≠ D := ne₁₃_of_not_collinear hCED
  have hCE : C ≠ E := ne₁₂_of_not_collinear hCED
  have hDE : D ≠ E := ne₁₂_of_not_collinear hDEF
  have hCA : C ≠ A := (ne₁₃_of_not_collinear hABC).symm
  have hBC : B ≠ C := ne₂₃_of_not_collinear hABC
  have hCB : C ≠ B := hBC.symm
  -- `D ≠ A` since `D` lies on line `BC`
  have hDA : D ≠ A := by
    intro h
    apply hABC
    have hDl : D ∈ line[ℝ, B, C] := by
      have hcol : Collinear ℝ ({D, B, C} : Set ℂ) := by
        have h2 := hD.collinear
        rwa [Set.insert_comm B D {C}] at h2
      exact mem_line_of_collinear hcol hBC
    rw [← h]
    exact collinear_insert_iff_of_mem_affineSpan hDl |>.mpr (collinear_pair ℝ B C)
  have hDs : D ∈ miquelS₁ hAFE := hQD ▸ miquelQ_mem_s₁ hAFE hBDF
  obtain ⟨d, hd0, hd1, hD'⟩ := wbtw_param hD hBD hCD
  -- concyclicity: `2∡ADE = 2∡AFE`
  have h1 : (2 : ℤ) • ∡ A D E = (2 : ℤ) • ∡ A F E :=
    Sphere.two_zsmul_oangle_eq (A_mem_miquelS₁ hAFE) hDs (F_mem_miquelS₁ hAFE)
      (E_mem_miquelS₁ hAFE) hDA hDE hAF.symm hFE
  -- angle sums around `D`
  have hadd : ∡ A D E + ∡ E D C = ∡ A D C :=
    EuclideanGeometry.oangle_add hDA.symm hDE.symm hCD
  have hsumADC : ∡ A D C + ∡ D C A + ∡ C A D = π :=
    oangle_add_oangle_add_oangle_eq_pi hDA hCD hCA.symm
  have hsumCED : ∡ C E D + ∡ E D C + ∡ D C E = π :=
    oangle_add_oangle_add_oangle_eq_pi hCE.symm hDE hCD
  -- ray equalities at `C`
  have hray1 : ∡ D C A = ∡ B C A :=
    oangle_eq_of_smul_left_pos hCD.symm hBC hCA.symm (sub_pos.mpr hd1)
      (show D - C = (1 - d) • (B - C) from by rw [hD']; module)
  have hray2 : ∡ D C E = ∡ B C A := by
    obtain ⟨e, he0, he1, hE'⟩ := wbtw_param hE hCE hAE
    have h1 : D - C = (1 - d) • (B - C) := by rw [hD']; module
    have h2 : E - C = e • (A - C) := by rw [hE']; module
    have e1 := oangle_eq_of_smul_left_pos hCD.symm hBC hCE.symm (sub_pos.mpr hd1) h1
    have e2 := oangle_eq_of_smul_right_pos hBC hCA.symm hCE.symm he0 h2
    exact e1.trans e2
  -- conclude `2∡CAD = 0`
  have h2 : (2 : ℤ) • ∡ C A D = 0 := by
    have hs : (2 : ℤ) • ∡ A D E =
        (2 : ℤ) • ∡ A D C - (2 : ℤ) • ∡ E D C := by
      rw [← hadd, smul_add, add_sub_cancel_right]
    rw [h1, hα₁o, hα₂o] at hs
    -- `2∡ADC = -2∡DCA - 2∡CAD` and `2∡EDC = -2∡DCE - 2∡CED`
    have hADC : (2 : ℤ) • ∡ A D C = -((2 : ℤ) • ∡ D C A) - (2 : ℤ) • ∡ C A D := by
      have h : (2 : ℤ) • ∡ A D C + (2 : ℤ) • ∡ D C A + (2 : ℤ) • ∡ C A D = 0 := by
        have h2pi : (2 : ℤ) • (π : Real.Angle) = 0 :=
          Real.Angle.two_zsmul_eq_zero_iff.mpr (Or.inr rfl)
        rw [← h2pi, ← hsumADC, smul_add, smul_add]
      rw [show (2 : ℤ) • ∡ A D C = (2 : ℤ) • ∡ A D C + (2 : ℤ) • ∡ D C A + (2 : ℤ) • ∡ C A D - (2 : ℤ) • ∡ D C A - (2 : ℤ) • ∡ C A D from by abel, h]
      abel
    have hEDC : (2 : ℤ) • ∡ E D C = -((2 : ℤ) • ∡ D C E) - (2 : ℤ) • ∡ C E D := by
      have h : (2 : ℤ) • ∡ C E D + (2 : ℤ) • ∡ E D C + (2 : ℤ) • ∡ D C E = 0 := by
        have h2pi : (2 : ℤ) • (π : Real.Angle) = 0 :=
          Real.Angle.two_zsmul_eq_zero_iff.mpr (Or.inr rfl)
        rw [← h2pi, ← hsumCED, smul_add, smul_add]
      rw [show (2 : ℤ) • ∡ E D C = (2 : ℤ) • ∡ C E D + (2 : ℤ) • ∡ E D C + (2 : ℤ) • ∡ D C E - (2 : ℤ) • ∡ D C E - (2 : ℤ) • ∡ C E D from by abel, h]
      abel
    rw [hADC, hEDC, hray1, hray2] at hs
    have h0 : (2 : ℤ) • ∡ C E D - (2 : ℤ) • ∡ C E D = -(2 : ℤ) • ∡ C A D := by
      nth_rw 1 [hs]
      abel
    rw [sub_self] at h0
    exact neg_eq_zero.mp h0.symm
  -- collinearity of `C, A, D`, forcing `D ∈ line AC`
  have hcol : Collinear ℝ ({C, A, D} : Set ℂ) := by
    rw [← oangle_eq_zero_or_eq_pi_iff_collinear]
    exact Real.Angle.two_zsmul_eq_zero_iff.mp h2
  have hperm : ({C, A, D} : Set ℂ) = {A, C, D} := by
    ext x
    simp [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [hperm] at hcol
  have hDl : D ∈ line[ℝ, A, C] := by
    have h1 : affineSpan ℝ ({A, C, D} : Set ℂ) = line[ℝ, A, C] :=
      (hcol.affineSpan_eq_of_ne (Set.mem_insert A _)
        (Set.mem_insert_of_mem _ (Set.mem_insert C _)) hCA.symm).symm
    have h2 : D ∈ affineSpan ℝ ({A, C, D} : Set ℂ) :=
      subset_affineSpan ℝ _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
        (Set.mem_singleton D)))
    rwa [h1] at h2
  have hcol2 : Collinear ℝ ({D, B, C} : Set ℂ) := by
    have h2 := hD.collinear
    rwa [Set.insert_comm B D {C}] at h2
  exact hCD (eq_of_mem_line_line hABC hDl (mem_line_of_collinear hcol2 hBC)).symm

/-- The Miquel point is not `E`. -/
lemma miquelQ_ne_E {A B C D E F : ℂ} (hABC : ¬Collinear ℝ {A, B, C})
    (hD : Wbtw ℝ B D C) (hE : Wbtw ℝ C E A) (hF : Wbtw ℝ A F B)
    (hα₁o : ∡ A F E = ∡ B D F) (_hα₂o : ∡ B D F = ∡ C E D)
    (hAFE : ¬Collinear ℝ {A, F, E}) (hBDF : ¬Collinear ℝ {B, D, F})
    (hCED : ¬Collinear ℝ {C, E, D}) (hDEF : ¬Collinear ℝ {D, E, F}) :
    miquelQ hAFE hBDF ≠ E := by
  intro hQE
  have hAF : A ≠ F := ne₁₂_of_not_collinear hAFE
  have hAE : A ≠ E := ne₁₃_of_not_collinear hAFE
  have hFE : F ≠ E := (ne₂₃_of_not_collinear hDEF).symm
  have hBD : B ≠ D := ne₁₂_of_not_collinear hBDF
  have hCD : C ≠ D := ne₁₃_of_not_collinear hCED
  have hCE : C ≠ E := ne₁₂_of_not_collinear hCED
  have hDE : D ≠ E := ne₁₂_of_not_collinear hDEF
  have hDF : D ≠ F := ne₂₃_of_not_collinear hBDF
  have hBF : B ≠ F := ne₁₃_of_not_collinear hBDF
  have hAB : A ≠ B := ne₁₂_of_not_collinear hABC
  have hCA : C ≠ A := (ne₁₃_of_not_collinear hABC).symm
  have hCB : C ≠ B := (ne₂₃_of_not_collinear hABC).symm
  have hBC : B ≠ C := ne₂₃_of_not_collinear hABC
  -- `B ≠ E` since `E` lies on line `AC`
  have hBE : B ≠ E := by
    intro h
    apply hABC
    have hcol : Collinear ℝ ({E, A, C} : Set ℂ) := by
      have h2 := hE.collinear
      rwa [Set.insert_comm C E, Set.pair_comm C A] at h2
    have hEl : E ∈ line[ℝ, A, C] := mem_line_of_collinear hcol hCA.symm
    rw [← h] at hEl
    have h2 := collinear_insert_iff_of_mem_affineSpan hEl
    rw [Set.insert_comm A B, h2]
    exact collinear_pair ℝ A C
  have hEs : E ∈ miquelS₂ hBDF := hQE ▸ miquelQ_mem_s₂ hAFE hBDF
  obtain ⟨d, hd0, hd1, hD'⟩ := wbtw_param hD hBD hCD
  obtain ⟨f, hf0, hf1, hF'⟩ := wbtw_param hF hAF hBF
  -- concyclicity: `2∡DBE = 2∡DFE`
  have h1 : (2 : ℤ) • ∡ D B E = (2 : ℤ) • ∡ D F E :=
    Sphere.two_zsmul_oangle_eq (D_mem_miquelS₂ hBDF) (B_mem_miquelS₂ hBDF)
      (F_mem_miquelS₂ hBDF) hEs hBD hBE hDF.symm hFE
  -- ray equality: `∡DBE = ∡CBE`
  have hray1 : ∡ D B E = ∡ C B E :=
    oangle_eq_of_smul_left_pos hBD.symm hCB hBE.symm hd0
      (show D - B = d • (C - B) from by rw [hD']; module)
  -- the around-point computation at `F`: `2∡EFD = 2∡ABC`
  have hpi : ∡ A F B = π := by
    rw [oangle]
    apply (Orientation.oangle_eq_pi_iff_sameRay_neg _).mpr
    rw [vsub_eq_sub, vsub_eq_sub]
    refine ⟨sub_ne_zero.mpr hAF, sub_ne_zero.mpr hBF, ?_⟩
    have h1 : A - F = f • (A - B) := by rw [hF']; module
    have h2 : -(B - F) = (1 - f) • (A - B) := by rw [hF']; module
    rw [h1, h2]
    exact (SameRay.sameRay_pos_smul_left (A - B) hf0).nonneg_smul_right (sub_pos.mpr hf1).le
  have hadd1 : ∡ A F E + ∡ E F B = ∡ A F B :=
    EuclideanGeometry.oangle_add hAF hFE.symm hBF
  have hadd2 : ∡ E F D + ∡ D F B = ∡ E F B :=
    EuclideanGeometry.oangle_add hFE.symm hDF hBF
  have hsumBFD : ∡ B F D + ∡ F D B + ∡ D B F = π :=
    oangle_add_oangle_add_oangle_eq_pi hBF.symm hDF hBD
  have h3 : (2 : ℤ) • ∡ D F B = (2 : ℤ) • ∡ F D B + (2 : ℤ) • ∡ D B F := by
    have h2pi : (2 : ℤ) • (π : Real.Angle) = 0 :=
      Real.Angle.two_zsmul_eq_zero_iff.mpr (Or.inr rfl)
    have hrev : ∡ D F B = -∡ B F D := oangle_rev B F D
    have hbfd : ∡ B F D = π - ∡ F D B - ∡ D B F := by
      rw [← hsumBFD]
      abel
    rw [hrev, hbfd, smul_neg, smul_sub, smul_sub, h2pi]
    abel
  have h4 : (2 : ℤ) • ∡ A F E + (2 : ℤ) • ∡ E F D + (2 : ℤ) • ∡ D F B = 0 := by
    have h2pi : (2 : ℤ) • (π : Real.Angle) = 0 :=
      Real.Angle.two_zsmul_eq_zero_iff.mpr (Or.inr rfl)
    rw [← h2pi, ← hpi, ← hadd1, ← hadd2]
    simp only [smul_add]
    abel
  have h5 : (2 : ℤ) • ∡ D B F = (2 : ℤ) • ∡ C B A := by
    have h6 : ∡ D B F = ∡ C B F :=
      oangle_eq_of_smul_left_pos hBD.symm hCB hBF.symm hd0
        (show D - B = d • (C - B) from by rw [hD']; module)
    rw [h6]
    exact two_zsmul_oangle_eq_of_smul_right hCB hAB hBF.symm (sub_ne_zero.mpr hf1.ne')
      (show F - B = (1 - f) • (A - B) from by rw [hF']; module)
  have h2 : (2 : ℤ) • ∡ E F D = (2 : ℤ) • ∡ A B C := by
    have h9 : (2 : ℤ) • ∡ E F D = -((2 : ℤ) • ∡ A F E) - ((2 : ℤ) • ∡ D F B) := by
      calc (2 : ℤ) • ∡ E F D = (2 : ℤ) • ∡ A F E + (2 : ℤ) • ∡ E F D + (2 : ℤ) • ∡ D F B - ((2 : ℤ) • ∡ A F E) - ((2 : ℤ) • ∡ D F B) := by abel
        _ = 0 - ((2 : ℤ) • ∡ A F E) - ((2 : ℤ) • ∡ D F B) := by rw [h4]
        _ = -((2 : ℤ) • ∡ A F E) - ((2 : ℤ) • ∡ D F B) := by abel
    have h10 : -((2 : ℤ) • ∡ A F E) = (2 : ℤ) • ∡ F D B := by
      rw [hα₁o, ← neg_smul, two_zsmul_neg_oangle_rev B D F]
    rw [h9, h10, h3, h5,
      show (2 : ℤ) • ∡ F D B - ((2 : ℤ) • ∡ F D B + (2 : ℤ) • ∡ C B A) = (-2 : ℤ) • ∡ C B A from by abel,
      two_zsmul_neg_oangle_rev C B A]
  -- final: `2∡CBE = 2∡CBA` forces `E` onto line `AB`
  have hfin : (2 : ℤ) • ∡ C B E = (2 : ℤ) • ∡ C B A := by
    have h11 : (2 : ℤ) • ∡ D F E = -((2 : ℤ) • ∡ E F D) := by
      rw [oangle_rev E F D, smul_neg]
    rw [← hray1, h1, h11, h2, ← neg_smul, two_zsmul_neg_oangle_rev A B C]
  have hdiff : (2 : ℤ) • (∡ C B E - ∡ C B A) = 0 := by
    rw [smul_sub, hfin, sub_self]
  have hcol : Collinear ℝ ({A, B, E} : Set ℂ) := by
    have hsub : ∡ A B E = ∡ C B E - ∡ C B A :=
      (EuclideanGeometry.oangle_sub_left hCB hAB hBE.symm).symm
    rw [← oangle_eq_zero_or_eq_pi_iff_collinear, hsub]
    exact Real.Angle.two_zsmul_eq_zero_iff.mp hdiff
  have hEl : E ∈ line[ℝ, B, A] := by
    have hcol' : Collinear ℝ ({E, B, A} : Set ℂ) := by
      have h2 := hcol
      rwa [show ({A, B, E} : Set ℂ) = {E, B, A} from by
        ext x; simp [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at h2
    exact mem_line_of_collinear hcol' hAB.symm
  have hEl2 : E ∈ line[ℝ, C, A] := mem_line_of_collinear
    (by have h2 := hE.collinear; rwa [Set.insert_comm C E] at h2) hCA
  have hABC' : ¬Collinear ℝ {B, C, A} := by
    have h2 := hABC
    rwa [show ({A, B, C} : Set ℂ) = {B, C, A} from by
      ext x; simp [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at h2
  exact hAE ((eq_of_mem_line_line hABC' hEl hEl2).symm)

/-- **Miquel's theorem**: the three circumcircles meet at the Miquel point. -/
lemma miquelQ_mem_s₃ {A B C D E F : ℂ} (hABC : ¬Collinear ℝ {A, B, C})
    (hD : Wbtw ℝ B D C) (hE : Wbtw ℝ C E A) (hF : Wbtw ℝ A F B)
    (hα₁o : ∡ A F E = ∡ B D F) (hα₂o : ∡ B D F = ∡ C E D)
    (hAFE : ¬Collinear ℝ {A, F, E}) (hBDF : ¬Collinear ℝ {B, D, F})
    (hCED : ¬Collinear ℝ {C, E, D}) (hDEF : ¬Collinear ℝ {D, E, F}) :
    miquelQ hAFE hBDF ∈ miquelS₃ hCED := by
  have hAF : A ≠ F := ne₁₂_of_not_collinear hAFE
  have hAE : A ≠ E := ne₁₃_of_not_collinear hAFE
  have hFE : F ≠ E := (ne₂₃_of_not_collinear hDEF).symm
  have hBD : B ≠ D := ne₁₂_of_not_collinear hBDF
  have hCD : C ≠ D := ne₁₃_of_not_collinear hCED
  have hCE : C ≠ E := ne₁₂_of_not_collinear hCED
  have hDE : D ≠ E := ne₁₂_of_not_collinear hDEF
  have hDF : D ≠ F := ne₂₃_of_not_collinear hBDF
  have hBF : B ≠ F := ne₁₃_of_not_collinear hBDF
  have hAB : A ≠ B := ne₁₂_of_not_collinear hABC
  have hBC : B ≠ C := ne₂₃_of_not_collinear hABC
  have hCA : C ≠ A := (ne₁₃_of_not_collinear hABC).symm
  have hQE : miquelQ hAFE hBDF ≠ E :=
    miquelQ_ne_E hABC hD hE hF hα₁o hα₂o hAFE hBDF hCED hDEF
  have hQF : miquelQ hAFE hBDF ≠ F := miquelQ_ne_F hABC hD hE hF hα₁o hAFE hBDF hCED hDEF
  have hQD : miquelQ hAFE hBDF ≠ D :=
    miquelQ_ne_D hABC hD hE hF hα₁o hα₂o hAFE hBDF hCED hDEF
  obtain ⟨d, hd0, hd1, hD'⟩ := wbtw_param hD hBD hCD
  obtain ⟨e, he0, he1, hE'⟩ := wbtw_param hE hCE hAE
  obtain ⟨f, hf0, hf1, hF'⟩ := wbtw_param hF hAF hBF
  -- the angle chase: `2∡EQD = 2∡EAF + 2∡FBD = 2∡ECD`
  have hadd : ∡ E (miquelQ hAFE hBDF) F + ∡ F (miquelQ hAFE hBDF) D =
      ∡ E (miquelQ hAFE hBDF) D :=
    EuclideanGeometry.oangle_add hQE.symm hQF.symm hQD.symm
  have h1 : (2 : ℤ) • ∡ E (miquelQ hAFE hBDF) F = (2 : ℤ) • ∡ E A F :=
    Sphere.two_zsmul_oangle_eq (E_mem_miquelS₁ hAFE) (miquelQ_mem_s₁ hAFE hBDF)
      (A_mem_miquelS₁ hAFE) (F_mem_miquelS₁ hAFE) hQE hQF hAE hAF
  have h2 : (2 : ℤ) • ∡ F (miquelQ hAFE hBDF) D = (2 : ℤ) • ∡ F B D :=
    Sphere.two_zsmul_oangle_eq (F_mem_miquelS₂ hBDF) (miquelQ_mem_s₂ hAFE hBDF)
      (B_mem_miquelS₂ hBDF) (D_mem_miquelS₂ hBDF) hQF hQD hBF hBD
  have hray1 : ∡ E A F = ∡ C A B := by
    have e1 := oangle_eq_of_smul_left_pos hAE.symm hCA hAF.symm (sub_pos.mpr he1)
      (show E - A = (1 - e) • (C - A) from by rw [hE']; module)
    have e2 := oangle_eq_of_smul_right_pos hCA hAB.symm hAF.symm hf0
      (show F - A = f • (B - A) from by rw [hF']; module)
    exact e1.trans e2
  have hray2 : (2 : ℤ) • ∡ F B D = (2 : ℤ) • ∡ A B C := by
    have e1 := two_zsmul_oangle_eq_of_smul_left hBF.symm hAB hBD.symm
      (sub_ne_zero.mpr hf1.ne')
      (show F - B = (1 - f) • (A - B) from by rw [hF']; module)
    have e2 := two_zsmul_oangle_eq_of_smul_right hAB hBC.symm hBD.symm hd0.ne'
      (show D - B = d • (C - B) from by rw [hD']; module)
    exact e1.trans e2
  have hsum : ∡ B A C + ∡ A C B + ∡ C B A = π :=
    oangle_add_oangle_add_oangle_eq_pi hAB hCA hBC
  have hray3 : ∡ E C D = ∡ A C B := by
    have e1 := oangle_eq_of_smul_left_pos hCE.symm hCA.symm hCD.symm he0
      (show E - C = e • (A - C) from by rw [hE']; module)
    have e2 := oangle_eq_of_smul_right_pos hCA.symm hBC hCD.symm (sub_pos.mpr hd1)
      (show D - C = (1 - d) • (B - C) from by rw [hD']; module)
    exact e1.trans e2
  have heq : (2 : ℤ) • ∡ E (miquelQ hAFE hBDF) D = (2 : ℤ) • ∡ E C D := by
    have h2pi : (2 : ℤ) • (π : Real.Angle) = 0 :=
      Real.Angle.two_zsmul_eq_zero_iff.mpr (Or.inr rfl)
    have h : (2 : ℤ) • ∡ B A C + (2 : ℤ) • ∡ A C B + (2 : ℤ) • ∡ C B A = 0 := by
      rw [← h2pi, ← hsum, smul_add, smul_add]
    have h4 : (2 : ℤ) • ∡ A C B = (2 : ℤ) • ∡ C A B + (2 : ℤ) • ∡ A B C := by
      have h5 : (2 : ℤ) • ∡ A C B = -((2 : ℤ) • ∡ B A C + (2 : ℤ) • ∡ C B A) := by
        have h6 := h
        rw [show (2 : ℤ) • ∡ A C B = (2 : ℤ) • ∡ B A C + (2 : ℤ) • ∡ A C B + (2 : ℤ) • ∡ C B A - ((2 : ℤ) • ∡ B A C + (2 : ℤ) • ∡ C B A) from by abel, h6]
        abel
      rw [h5, neg_add, ← neg_smul, ← neg_smul, two_zsmul_neg_oangle_rev B A C,
        two_zsmul_neg_oangle_rev C B A]
    rw [← hadd, smul_add, h1, h2, hray1, hray2, hray3, h4]

  -- apply the "fourth point on the circumsphere" criterion
  have hsphere : miquelS₃ hCED =
      (⟨![C, E, D], affineIndependent_iff_not_collinear_set.mpr hCED⟩ :
        Affine.Triangle ℝ ℂ).circumsphere := rfl
  rw [hsphere]
  exact Affine.Triangle.mem_circumsphere_of_two_zsmul_oangle_eq (show (1 : Fin 3) ≠ 0 by decide)
    (show (1 : Fin 3) ≠ 2 by decide) (show (0 : Fin 3) ≠ 2 by decide)
    (show (2 : ℤ) • ∡ ((⟨![C, E, D], affineIndependent_iff_not_collinear_set.mpr hCED⟩ :
        Affine.Triangle ℝ ℂ).points 1) (miquelQ hAFE hBDF)
      ((⟨![C, E, D], affineIndependent_iff_not_collinear_set.mpr hCED⟩ :
        Affine.Triangle ℝ ℂ).points 2) =
      (2 : ℤ) • ∡ ((⟨![C, E, D], affineIndependent_iff_not_collinear_set.mpr hCED⟩ :
        Affine.Triangle ℝ ℂ).points 1) ((⟨![C, E, D], affineIndependent_iff_not_collinear_set.mpr hCED⟩ :
        Affine.Triangle ℝ ℂ).points 0) ((⟨![C, E, D], affineIndependent_iff_not_collinear_set.mpr hCED⟩ :
        Affine.Triangle ℝ ℂ).points 2) from heq)

/-!
### C2: the `β` relations and the Brocard-type relations at `Q`
-/

/-- The circumcenters of `AFE`, `BDF`, `CED` are the centers of the three
Miquel circles. -/
lemma miquelS₁_center {A F E : ℂ} (hAFE : ¬Collinear ℝ {A, F, E}) :
    (miquelS₁ hAFE).center = triCircumcenter hAFE :=
  Affine.Simplex.circumsphere_center _

lemma miquelS₂_center {B D F : ℂ} (hBDF : ¬Collinear ℝ {B, D, F}) :
    (miquelS₂ hBDF).center = triCircumcenter hBDF :=
  Affine.Simplex.circumsphere_center _

lemma miquelS₃_center {C E D : ℂ} (hCED : ¬Collinear ℝ {C, E, D}) :
    (miquelS₃ hCED).center = triCircumcenter hCED :=
  Affine.Simplex.circumsphere_center _

/-- The radius of the Miquel circle `s₁` is positive. -/
lemma miquelS₁_radius_pos {A F E : ℂ} (hAFE : ¬Collinear ℝ {A, F, E}) :
    0 < (miquelS₁ hAFE).radius := by
  rw [miquelS₁, triCircumsphere, Affine.Simplex.circumsphere_radius]
  exact Affine.Simplex.circumradius_pos _

/-- The Miquel point is different from the circumcenter of `AFE`. -/
lemma miquelQ_ne_circumcenter {A B C D E F : ℂ}
    (_hABC : ¬Collinear ℝ {A, B, C})
    (_hD : Wbtw ℝ B D C) (_hE : Wbtw ℝ C E A) (_hF : Wbtw ℝ A F B)
    (hAFE : ¬Collinear ℝ {A, F, E}) (hBDF : ¬Collinear ℝ {B, D, F}) :
    triCircumcenter hAFE ≠ miquelQ hAFE hBDF := by
  intro h
  have hr := miquelS₁_radius_pos hAFE
  have hmem : dist (miquelQ hAFE hBDF) (miquelS₁ hAFE).center = (miquelS₁ hAFE).radius :=
    mem_sphere.mp (miquelQ_mem_s₁ hAFE hBDF)
  rw [miquelS₁_center, ← h, dist_self] at hmem
  exact hr.ne' hmem.symm

/-- The `β` chain, first link: `2∡QEA = 2∡QFA`. -/
lemma beta_QEA_QFA {A B D E F : ℂ}
    (hAFE : ¬Collinear ℝ {A, F, E}) (hBDF : ¬Collinear ℝ {B, D, F})
    (_hDEF : ¬Collinear ℝ {D, E, F})
    (hQE : miquelQ hAFE hBDF ≠ E) (hQF : miquelQ hAFE hBDF ≠ F) :
    (2 : ℤ) • ∡ (miquelQ hAFE hBDF) E A = (2 : ℤ) • ∡ (miquelQ hAFE hBDF) F A := by
  exact Sphere.two_zsmul_oangle_eq (miquelQ_mem_s₁ hAFE hBDF) (E_mem_miquelS₁ hAFE)
    (F_mem_miquelS₁ hAFE) (A_mem_miquelS₁ hAFE) hQE.symm
    (ne₁₃_of_not_collinear hAFE).symm hQF.symm (ne₁₂_of_not_collinear hAFE).symm

/-- The `β` chain, second link: `2∡QFB = 2∡QDB`. -/
lemma beta_QFB_QDB {A B D E F : ℂ}
    (hAFE : ¬Collinear ℝ {A, F, E}) (hBDF : ¬Collinear ℝ {B, D, F})
    (hQF : miquelQ hAFE hBDF ≠ F) (hQD : miquelQ hAFE hBDF ≠ D)
    (_hF : Wbtw ℝ A F B) :
    (2 : ℤ) • ∡ (miquelQ hAFE hBDF) F B = (2 : ℤ) • ∡ (miquelQ hAFE hBDF) D B := by
  exact Sphere.two_zsmul_oangle_eq (miquelQ_mem_s₂ hAFE hBDF) (F_mem_miquelS₂ hBDF)
    (D_mem_miquelS₂ hBDF) (B_mem_miquelS₂ hBDF) hQF.symm
    (ne₁₃_of_not_collinear hBDF).symm hQD.symm (ne₁₂_of_not_collinear hBDF).symm

/-- The `β` chain, third link: `2∡QDC = 2∡QEC`. -/
lemma beta_QDC_QEC {A B C D E F : ℂ}
    (hABC : ¬Collinear ℝ {A, B, C})
    (hD : Wbtw ℝ B D C) (hE : Wbtw ℝ C E A) (hF : Wbtw ℝ A F B)
    (hα₁o : ∡ A F E = ∡ B D F) (hα₂o : ∡ B D F = ∡ C E D)
    (hAFE : ¬Collinear ℝ {A, F, E}) (hBDF : ¬Collinear ℝ {B, D, F})
    (hCED : ¬Collinear ℝ {C, E, D}) (hDEF : ¬Collinear ℝ {D, E, F})
    (hQD : miquelQ hAFE hBDF ≠ D) (hQE : miquelQ hAFE hBDF ≠ E) :
    (2 : ℤ) • ∡ (miquelQ hAFE hBDF) D C = (2 : ℤ) • ∡ (miquelQ hAFE hBDF) E C := by
  exact Sphere.two_zsmul_oangle_eq (miquelQ_mem_s₃ hABC hD hE hF hα₁o hα₂o hAFE hBDF hCED hDEF)
    (D_mem_miquelS₃ hCED) (E_mem_miquelS₃ hCED) (C_mem_miquelS₃ hCED) hQD.symm
    (ne₁₃_of_not_collinear hCED).symm hQE.symm (ne₁₂_of_not_collinear hCED).symm

/-- The `β` chain, collinear bridge at `F`. -/
lemma beta_QFA_QFB {A B D E F : ℂ}
    (hAFE : ¬Collinear ℝ {A, F, E}) (hBDF : ¬Collinear ℝ {B, D, F})
    (hF : Wbtw ℝ A F B) (hQF : miquelQ hAFE hBDF ≠ F) :
    (2 : ℤ) • ∡ (miquelQ hAFE hBDF) F A = (2 : ℤ) • ∡ (miquelQ hAFE hBDF) F B := by
  have hAF : A ≠ F := ne₁₂_of_not_collinear hAFE
  have hBF : B ≠ F := ne₁₃_of_not_collinear hBDF
  obtain ⟨f, hf0, hf1, hF'⟩ := wbtw_param hF hAF hBF
  have h1 : A - F = ((-f)/(1 - f)) • (B - F) := by
    have h2 : A - F = (-f) • (B - A) := by rw [hF']; module
    have h3 : B - F = (1 - f) • (B - A) := by rw [hF']; module
    rw [h2, h3, smul_smul, div_mul_cancel₀ _ (sub_ne_zero.mpr (LT.lt.ne' hf1))]
  exact two_zsmul_oangle_eq_of_smul_right hQF hBF hAF
    (div_ne_zero (neg_ne_zero.mpr hf0.ne') (sub_ne_zero.mpr hf1.ne')) h1

/-- The `β` chain, collinear bridge at `D`. -/
lemma beta_QDB_QDC {A B C D E F : ℂ}
    (hAFE : ¬Collinear ℝ {A, F, E}) (hBDF : ¬Collinear ℝ {B, D, F}) (hCED : ¬Collinear ℝ {C, E, D})
    (hD : Wbtw ℝ B D C) (hQD : miquelQ hAFE hBDF ≠ D) :
    (2 : ℤ) • ∡ (miquelQ hAFE hBDF) D B = (2 : ℤ) • ∡ (miquelQ hAFE hBDF) D C := by
  have hBD : B ≠ D := ne₁₂_of_not_collinear hBDF
  have hCD : C ≠ D := ne₁₃_of_not_collinear hCED
  obtain ⟨d, hd0, hd1, hD'⟩ := wbtw_param hD hBD hCD
  have h1 : B - D = (d/(d - 1)) • (C - D) := by
    have h2 : B - D = d • (B - C) := by rw [hD']; module
    have h3 : C - D = (d - 1) • (B - C) := by rw [hD']; module
    rw [h2, h3, smul_smul, div_mul_cancel₀ _ (sub_ne_zero.mpr (ne_of_lt hd1))]
  exact two_zsmul_oangle_eq_of_smul_right hQD hCD hBD
    (div_ne_zero hd0.ne' (sub_ne_zero.mpr (ne_of_lt hd1))) h1

/-- The `β` chain, collinear bridge at `E`. -/
lemma beta_QEC_QEA {A B C D E F : ℂ}
    (hAFE : ¬Collinear ℝ {A, F, E}) (hBDF : ¬Collinear ℝ {B, D, F}) (hCED : ¬Collinear ℝ {C, E, D})
    (hE : Wbtw ℝ C E A) (hQE : miquelQ hAFE hBDF ≠ E) :
    (2 : ℤ) • ∡ (miquelQ hAFE hBDF) E C = (2 : ℤ) • ∡ (miquelQ hAFE hBDF) E A := by
  have hAE : A ≠ E := ne₁₃_of_not_collinear hAFE
  have hCE : C ≠ E := ne₁₂_of_not_collinear hCED
  obtain ⟨e, he0, he1, hE'⟩ := wbtw_param hE hCE hAE
  have h1 : C - E = (e/(e - 1)) • (A - E) := by
    have h2 : C - E = e • (C - A) := by rw [hE']; module
    have h3 : A - E = (e - 1) • (C - A) := by rw [hE']; module
    rw [h2, h3, smul_smul, div_mul_cancel₀ _ (sub_ne_zero.mpr (ne_of_lt he1))]
  exact two_zsmul_oangle_eq_of_smul_right hQE hAE hCE
    (div_ne_zero he0.ne' (sub_ne_zero.mpr (ne_of_lt he1))) h1

/-!
### C3: sine bridge, the Brocard relations, and the modulus ratios
-/

/-- The sine of an unoriented angle is the absolute value of the sine of the
oriented angle. -/
lemma sin_angle_eq_abs_sin_oangle {x y z : ℂ} (hx : x ≠ y) (hz : z ≠ y) :
    Real.sin (∠ x y z) = |Real.Angle.sin (∡ x y z)| := by
  rw [angle_eq_abs_oangle_toReal hx hz, ← Real.Angle.sin_toReal,
    Real.abs_sin_eq_sin_abs_of_abs_le_pi (Real.Angle.abs_toReal_le_pi _)]

/-- Twice-oriented-angle equality implies equality of unoriented sines. -/
lemma sin_eq_of_two_zsmul {x y z x' y' z' : ℂ}
    (h : (2 : ℤ) • ∡ x y z = (2 : ℤ) • ∡ x' y' z')
    (hx : x ≠ y) (hz : z ≠ y) (hx' : x' ≠ y') (hz' : z' ≠ y') :
    Real.sin (∠ x y z) = Real.sin (∠ x' y' z') := by
  rw [sin_angle_eq_abs_sin_oangle hx hz, sin_angle_eq_abs_sin_oangle hx' hz',
    Real.Angle.abs_sin_eq_of_two_zsmul_eq h]

/-- The Brocard relation at `A` and `B`: `2∡QAE = 2∡QBF`. -/
lemma brocard_QAE_QBF {A B D E F : ℂ}
    (hAFE : ¬Collinear ℝ {A, F, E}) (hBDF : ¬Collinear ℝ {B, D, F})
    (hDEF : ¬Collinear ℝ {D, E, F})
    (hα₁o : ∡ A F E = ∡ B D F)
    (hQA : miquelQ hAFE hBDF ≠ A) (_hQE : miquelQ hAFE hBDF ≠ E)
    (hQF : miquelQ hAFE hBDF ≠ F) (hQD : miquelQ hAFE hBDF ≠ D)
    (hQB : miquelQ hAFE hBDF ≠ B)
    (hbeta2 : (2 : ℤ) • ∡ (miquelQ hAFE hBDF) F A = (2 : ℤ) • ∡ (miquelQ hAFE hBDF) F B)
    (hbeta3 : (2 : ℤ) • ∡ (miquelQ hAFE hBDF) F B = (2 : ℤ) • ∡ (miquelQ hAFE hBDF) D B) :
    (2 : ℤ) • ∡ (miquelQ hAFE hBDF) A E = (2 : ℤ) • ∡ (miquelQ hAFE hBDF) B F := by
  have hAE : A ≠ E := ne₁₃_of_not_collinear hAFE
  have hAF : A ≠ F := ne₁₂_of_not_collinear hAFE
  have hFE : F ≠ E := (ne₂₃_of_not_collinear hDEF).symm
  have hBD : B ≠ D := ne₁₂_of_not_collinear hBDF
  have hDF : D ≠ F := ne₂₃_of_not_collinear hBDF
  have hBF : B ≠ F := ne₁₃_of_not_collinear hBDF
  have h1 : (2 : ℤ) • ∡ (miquelQ hAFE hBDF) A E = (2 : ℤ) • ∡ (miquelQ hAFE hBDF) F E :=
    Sphere.two_zsmul_oangle_eq (miquelQ_mem_s₁ hAFE hBDF) (A_mem_miquelS₁ hAFE)
      (F_mem_miquelS₁ hAFE) (E_mem_miquelS₁ hAFE) hQA.symm hAE hQF.symm hFE
  have hadd1 : ∡ (miquelQ hAFE hBDF) F A + ∡ A F E = ∡ (miquelQ hAFE hBDF) F E :=
    EuclideanGeometry.oangle_add hQF hAF hFE.symm
  have h2 : (2 : ℤ) • ∡ (miquelQ hAFE hBDF) D F = (2 : ℤ) • ∡ (miquelQ hAFE hBDF) B F :=
    Sphere.two_zsmul_oangle_eq (miquelQ_mem_s₂ hAFE hBDF) (D_mem_miquelS₂ hBDF)
      (B_mem_miquelS₂ hBDF) (F_mem_miquelS₂ hBDF) hQD.symm hDF hQB.symm hBF
  have hadd2 : ∡ (miquelQ hAFE hBDF) D B + ∡ B D F = ∡ (miquelQ hAFE hBDF) D F :=
    EuclideanGeometry.oangle_add hQD hBD hDF.symm
  rw [h1, ← hadd1, smul_add, hbeta2, hbeta3, hα₁o, ← smul_add, hadd2, h2]

/-- The Brocard relation at `C` and `D`: `2∡QCD = 2∡QDF`. -/
lemma brocard_QCD_QDF {A B C D E F : ℂ}
    (hABC : ¬Collinear ℝ {A, B, C})
    (hD : Wbtw ℝ B D C) (hE : Wbtw ℝ C E A) (hF : Wbtw ℝ A F B)
    (hα₁o : ∡ A F E = ∡ B D F) (hα₂o : ∡ B D F = ∡ C E D)
    (hAFE : ¬Collinear ℝ {A, F, E}) (hBDF : ¬Collinear ℝ {B, D, F})
    (hCED : ¬Collinear ℝ {C, E, D}) (hDEF : ¬Collinear ℝ {D, E, F})
    (hQC : miquelQ hAFE hBDF ≠ C) (hQE : miquelQ hAFE hBDF ≠ E)
    (hQD : miquelQ hAFE hBDF ≠ D) (_hQF : miquelQ hAFE hBDF ≠ F)
    (hbeta1 : (2 : ℤ) • ∡ (miquelQ hAFE hBDF) E A = (2 : ℤ) • ∡ (miquelQ hAFE hBDF) F A)
    (hbeta2 : (2 : ℤ) • ∡ (miquelQ hAFE hBDF) F A = (2 : ℤ) • ∡ (miquelQ hAFE hBDF) F B)
    (hbeta3 : (2 : ℤ) • ∡ (miquelQ hAFE hBDF) F B = (2 : ℤ) • ∡ (miquelQ hAFE hBDF) D B)
    (hbeta6 : (2 : ℤ) • ∡ (miquelQ hAFE hBDF) E C = (2 : ℤ) • ∡ (miquelQ hAFE hBDF) E A) :
    (2 : ℤ) • ∡ (miquelQ hAFE hBDF) C D = (2 : ℤ) • ∡ (miquelQ hAFE hBDF) D F := by
  have hCD : C ≠ D := ne₁₃_of_not_collinear hCED
  have hCE : C ≠ E := ne₁₂_of_not_collinear hCED
  have hDE : D ≠ E := ne₁₂_of_not_collinear hDEF
  have hBD : B ≠ D := ne₁₂_of_not_collinear hBDF
  have hDF : D ≠ F := ne₂₃_of_not_collinear hBDF
  have h1 : (2 : ℤ) • ∡ (miquelQ hAFE hBDF) C D = (2 : ℤ) • ∡ (miquelQ hAFE hBDF) E D :=
    Sphere.two_zsmul_oangle_eq (miquelQ_mem_s₃ hABC hD hE hF hα₁o hα₂o hAFE hBDF hCED hDEF)
      (C_mem_miquelS₃ hCED) (E_mem_miquelS₃ hCED) (D_mem_miquelS₃ hCED)
      hQC.symm hCD hQE.symm hDE.symm
  have hadd1 : ∡ (miquelQ hAFE hBDF) E C + ∡ C E D = ∡ (miquelQ hAFE hBDF) E D :=
    EuclideanGeometry.oangle_add hQE hCE hDE
  rw [h1, ← hadd1, smul_add, hbeta6, hbeta1, hbeta2, hbeta3, hα₂o.symm, ← smul_add,
    EuclideanGeometry.oangle_add hQD hBD hDF.symm]

/-- `2∡QBD = 2∡QFD` (circle `s₂`, chord `QD`). -/
lemma two_zsmul_QBD_QFD {A B D E F : ℂ}
    (hAFE : ¬Collinear ℝ {A, F, E}) (hBDF : ¬Collinear ℝ {B, D, F})
    (hQB : miquelQ hAFE hBDF ≠ B) (_hQD : miquelQ hAFE hBDF ≠ D)
    (hQF : miquelQ hAFE hBDF ≠ F) :
    (2 : ℤ) • ∡ (miquelQ hAFE hBDF) B D = (2 : ℤ) • ∡ (miquelQ hAFE hBDF) F D := by
  have hBD : B ≠ D := ne₁₂_of_not_collinear hBDF
  have hBF : B ≠ F := ne₁₃_of_not_collinear hBDF
  have hDF : D ≠ F := ne₂₃_of_not_collinear hBDF
  exact Sphere.two_zsmul_oangle_eq (miquelQ_mem_s₂ hAFE hBDF) (B_mem_miquelS₂ hBDF)
    (F_mem_miquelS₂ hBDF) (D_mem_miquelS₂ hBDF) hQB.symm hBD hQF.symm hDF.symm

/-- `Q` is not collinear with `E` and `A` (else it would coincide with `A` or
`E`, the two intersections of line `AE` with circle `AFE`). -/
lemma not_collinear_QEA {A B D E F : ℂ} (hAFE : ¬Collinear ℝ {A, F, E})
    (hBDF : ¬Collinear ℝ {B, D, F})
    (hQA : miquelQ hAFE hBDF ≠ A) (hQE : miquelQ hAFE hBDF ≠ E) :
    ¬Collinear ℝ ({miquelQ hAFE hBDF, E, A} : Set ℂ) := by
  intro hcol
  have hAE : A ≠ E := ne₁₃_of_not_collinear hAFE
  rw [Set.pair_comm E A] at hcol
  have hQmem := mem_line_of_collinear hcol hAE
  have hQ2 := (Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
    (A_mem_miquelS₁ hAFE) hQmem).mpr (miquelQ_mem_s₁ hAFE hBDF)
  have hE2 := (Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
    (A_mem_miquelS₁ hAFE) (right_mem_affineSpan_pair ℝ A E)).mpr (E_mem_miquelS₁ hAFE)
  rcases hQ2 with h | h
  · exact hQA h
  rcases hE2 with hE2 | hE2
  · exact hAE hE2.symm
  exact hQE (h.trans hE2.symm)

/-- `Q` is not collinear with `B` and `F`. -/
lemma not_collinear_QBF {A B D E F : ℂ} (hAFE : ¬Collinear ℝ {A, F, E})
    (hBDF : ¬Collinear ℝ {B, D, F})
    (hQB : miquelQ hAFE hBDF ≠ B) (hQF : miquelQ hAFE hBDF ≠ F) :
    ¬Collinear ℝ ({miquelQ hAFE hBDF, B, F} : Set ℂ) := by
  intro hcol
  have hBF : B ≠ F := ne₁₃_of_not_collinear hBDF
  have hQmem := mem_line_of_collinear hcol hBF
  have hQ2 := (Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
    (B_mem_miquelS₂ hBDF) hQmem).mpr (miquelQ_mem_s₂ hAFE hBDF)
  have hF2 := (Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
    (B_mem_miquelS₂ hBDF) (right_mem_affineSpan_pair ℝ B F)).mpr (F_mem_miquelS₂ hBDF)
  rcases hQ2 with h | h
  · exact hQB h
  rcases hF2 with hF2 | hF2
  · exact hBF hF2.symm
  exact hQF (h.trans hF2.symm)

/-- `Q` is not collinear with `C` and `B`. -/
lemma not_collinear_QCB {A B C D E F : ℂ} (hABC : ¬Collinear ℝ {A, B, C})
    (hD : Wbtw ℝ B D C) (hAFE : ¬Collinear ℝ {A, F, E}) (hBDF : ¬Collinear ℝ {B, D, F})
    (hQB : miquelQ hAFE hBDF ≠ B) (hQD : miquelQ hAFE hBDF ≠ D) :
    ¬Collinear ℝ ({miquelQ hAFE hBDF, C, B} : Set ℂ) := by
  intro hcol
  have hBC : B ≠ C := ne₂₃_of_not_collinear hABC
  have hBD : B ≠ D := ne₁₂_of_not_collinear hBDF
  rw [Set.pair_comm C B] at hcol
  have hQmem := mem_line_of_collinear hcol hBC
  have hcolD := hD.collinear
  rw [Set.insert_comm] at hcolD
  have hDmem := mem_line_of_collinear hcolD hBC
  have hQ2 := (Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
    (B_mem_miquelS₂ hBDF) hQmem).mpr (miquelQ_mem_s₂ hAFE hBDF)
  have hD2 := (Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
    (B_mem_miquelS₂ hBDF) hDmem).mpr (D_mem_miquelS₂ hBDF)
  rcases hQ2 with h | h
  · exact hQB h
  rcases hD2 with hD2 | hD2
  · exact hBD hD2.symm
  exact hQD (h.trans hD2.symm)

/-- `Q` is not collinear with `D` and `F`. -/
lemma not_collinear_QDF {A B D E F : ℂ} (hAFE : ¬Collinear ℝ {A, F, E})
    (hBDF : ¬Collinear ℝ {B, D, F})
    (hQD : miquelQ hAFE hBDF ≠ D) (hQF : miquelQ hAFE hBDF ≠ F) :
    ¬Collinear ℝ ({miquelQ hAFE hBDF, D, F} : Set ℂ) := by
  intro hcol
  have hDF : D ≠ F := ne₂₃_of_not_collinear hBDF
  have hQmem := mem_line_of_collinear hcol hDF
  have hQ2 := (Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
    (D_mem_miquelS₂ hBDF) hQmem).mpr (miquelQ_mem_s₂ hAFE hBDF)
  have hF2 := (Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
    (D_mem_miquelS₂ hBDF) (right_mem_affineSpan_pair ℝ D F)).mpr (F_mem_miquelS₂ hBDF)
  rcases hQ2 with h | h
  · exact hQD h
  rcases hF2 with hF2 | hF2
  · exact hDF hF2.symm
  exact hQF (h.trans hF2.symm)

/-- The modulus ratio along the first spiral similarity:
`dist Q E * dist Q B = dist Q F * dist Q A`. -/
lemma dist_QE_mul_dist_QB {A B D E F : ℂ}
    (hAFE : ¬Collinear ℝ {A, F, E}) (hBDF : ¬Collinear ℝ {B, D, F})
    (hDEF : ¬Collinear ℝ {D, E, F})
    (hα₁o : ∡ A F E = ∡ B D F)
    (hQA : miquelQ hAFE hBDF ≠ A) (hQE : miquelQ hAFE hBDF ≠ E)
    (hQF : miquelQ hAFE hBDF ≠ F) (hQD : miquelQ hAFE hBDF ≠ D)
    (hQB : miquelQ hAFE hBDF ≠ B)
    (hbeta1 : (2 : ℤ) • ∡ (miquelQ hAFE hBDF) E A = (2 : ℤ) • ∡ (miquelQ hAFE hBDF) F A)
    (hbeta2 : (2 : ℤ) • ∡ (miquelQ hAFE hBDF) F A = (2 : ℤ) • ∡ (miquelQ hAFE hBDF) F B)
    (hbeta3 : (2 : ℤ) • ∡ (miquelQ hAFE hBDF) F B = (2 : ℤ) • ∡ (miquelQ hAFE hBDF) D B) :
    dist (miquelQ hAFE hBDF) E * dist (miquelQ hAFE hBDF) B =
      dist (miquelQ hAFE hBDF) F * dist (miquelQ hAFE hBDF) A := by
  set Q := miquelQ hAFE hBDF with hQdef
  have hAE : A ≠ E := ne₁₃_of_not_collinear hAFE
  have hBF : B ≠ F := ne₁₃_of_not_collinear hBDF
  have hbro := brocard_QAE_QBF hAFE hBDF hDEF hα₁o hQA hQE hQF hQD hQB hbeta2 hbeta3
  have hsAB : Real.sin (∠ Q A E) = Real.sin (∠ Q B F) :=
    sin_eq_of_two_zsmul hbro hQA hAE.symm hQB hBF.symm
  have hsEF : Real.sin (∠ Q E A) = Real.sin (∠ Q F B) :=
    sin_eq_of_two_zsmul (hbeta1.trans hbeta2) hQE hAE hQF hBF
  have hnc1 : ¬Collinear ℝ ({Q, E, A} : Set ℂ) := not_collinear_QEA hAFE hBDF hQA hQE
  have hnc2 : ¬Collinear ℝ ({Q, B, F} : Set ℂ) := not_collinear_QBF hAFE hBDF hQB hQF
  have hsE : Real.sin (∠ Q E A) ≠ 0 :=
    ne_of_gt (EuclideanGeometry.sin_pos_of_not_collinear hnc1)
  have hsB : Real.sin (∠ Q B F) ≠ 0 :=
    ne_of_gt (EuclideanGeometry.sin_pos_of_not_collinear hnc2)
  have hI := EuclideanGeometry.sin_angle_mul_dist_eq_sin_angle_mul_dist E A Q
  rw [EuclideanGeometry.angle_comm E A Q] at hI
  have hII := EuclideanGeometry.sin_angle_mul_dist_eq_sin_angle_mul_dist F B Q
  rw [EuclideanGeometry.angle_comm F B Q] at hII
  have hI' : Real.sin (∠ Q A E) * dist Q A = Real.sin (∠ Q E A) * dist Q E := by
    rw [dist_comm Q A]; exact hI
  have hII' : Real.sin (∠ Q B F) * dist Q B = Real.sin (∠ Q F B) * dist Q F := by
    rw [dist_comm Q B]; exact hII
  have key : dist Q E * dist Q B * (Real.sin (∠ Q E A) * Real.sin (∠ Q B F)) =
      dist Q F * dist Q A * (Real.sin (∠ Q E A) * Real.sin (∠ Q B F)) := by
    calc dist Q E * dist Q B * (Real.sin (∠ Q E A) * Real.sin (∠ Q B F))
        = (Real.sin (∠ Q E A) * dist Q E) * (Real.sin (∠ Q B F) * dist Q B) := by ring
      _ = (Real.sin (∠ Q A E) * dist Q A) * (Real.sin (∠ Q F B) * dist Q F) := by
            rw [← hI', ← hII']
      _ = (Real.sin (∠ Q B F) * dist Q A) * (Real.sin (∠ Q E A) * dist Q F) := by
            rw [hsAB, ← hsEF]
      _ = dist Q F * dist Q A * (Real.sin (∠ Q E A) * Real.sin (∠ Q B F)) := by ring
  exact mul_right_cancel₀ (mul_ne_zero hsE hsB) key

/-- The modulus ratio along the second spiral similarity:
`dist Q C * dist Q F = dist Q D * dist Q B`. -/
lemma dist_QC_mul_dist_QF {A B C D E F : ℂ}
    (hABC : ¬Collinear ℝ {A, B, C})
    (hD : Wbtw ℝ B D C) (hE : Wbtw ℝ C E A) (hF : Wbtw ℝ A F B)
    (hα₁o : ∡ A F E = ∡ B D F) (hα₂o : ∡ B D F = ∡ C E D)
    (hAFE : ¬Collinear ℝ {A, F, E}) (hBDF : ¬Collinear ℝ {B, D, F})
    (hCED : ¬Collinear ℝ {C, E, D}) (hDEF : ¬Collinear ℝ {D, E, F})
    (hQC : miquelQ hAFE hBDF ≠ C) (hQE : miquelQ hAFE hBDF ≠ E)
    (hQD : miquelQ hAFE hBDF ≠ D) (hQF : miquelQ hAFE hBDF ≠ F)
    (hQB : miquelQ hAFE hBDF ≠ B)
    (hbeta1 : (2 : ℤ) • ∡ (miquelQ hAFE hBDF) E A = (2 : ℤ) • ∡ (miquelQ hAFE hBDF) F A)
    (hbeta2 : (2 : ℤ) • ∡ (miquelQ hAFE hBDF) F A = (2 : ℤ) • ∡ (miquelQ hAFE hBDF) F B)
    (hbeta3 : (2 : ℤ) • ∡ (miquelQ hAFE hBDF) F B = (2 : ℤ) • ∡ (miquelQ hAFE hBDF) D B)
    (hbeta6 : (2 : ℤ) • ∡ (miquelQ hAFE hBDF) E C = (2 : ℤ) • ∡ (miquelQ hAFE hBDF) E A) :
    dist (miquelQ hAFE hBDF) C * dist (miquelQ hAFE hBDF) F =
      dist (miquelQ hAFE hBDF) D * dist (miquelQ hAFE hBDF) B := by
  set Q := miquelQ hAFE hBDF with hQdef
  have hBC : B ≠ C := ne₂₃_of_not_collinear hABC
  have hBD : B ≠ D := ne₁₂_of_not_collinear hBDF
  have hCD : C ≠ D := ne₁₃_of_not_collinear hCED
  have hDF : D ≠ F := ne₂₃_of_not_collinear hBDF
  obtain ⟨d, hd0, hd1, hD'⟩ := wbtw_param hD hBD hCD
  -- bridge along ray `BC`: `2∡QBC = 2∡QFD`
  have hCB1 : C - B = (1 / d) • (D - B) := by
    have h2 : D - B = d • (C - B) := by rw [hD']; module
    rw [h2, smul_smul, one_div_mul_cancel hd0.ne', one_smul]
  have ho1 : ∡ Q B C = ∡ Q B D :=
    oangle_eq_of_smul_right_pos hQB hBD.symm hBC.symm (one_div_pos.mpr hd0) hCB1
  have h2a : (2 : ℤ) • ∡ Q B C = (2 : ℤ) • ∡ Q F D := by
    rw [ho1]; exact two_zsmul_QBD_QFD hAFE hBDF hQB hQD hQF
  have hs1 : Real.sin (∠ Q B C) = Real.sin (∠ Q F D) :=
    sin_eq_of_two_zsmul h2a hQB hBC.symm hQF hDF
  -- bridge along ray `CB`: `2∡QCB = 2∡QDF`
  have hCB2 : B - C = (1 / (1 - d)) • (D - C) := by
    have h2 : D - C = (1 - d) • (B - C) := by rw [hD']; module
    rw [h2, smul_smul, one_div_mul_cancel (sub_pos.mpr hd1).ne', one_smul]
  have ho2 : ∡ Q C B = ∡ Q C D :=
    oangle_eq_of_smul_right_pos hQC hCD.symm hBC (one_div_pos.mpr (sub_pos.mpr hd1)) hCB2
  have h2b : (2 : ℤ) • ∡ Q C B = (2 : ℤ) • ∡ Q D F := by
    rw [ho2]
    exact brocard_QCD_QDF hABC hD hE hF hα₁o hα₂o hAFE hBDF hCED hDEF hQC hQE hQD hQF
      hbeta1 hbeta2 hbeta3 hbeta6
  have hs2 : Real.sin (∠ Q C B) = Real.sin (∠ Q D F) :=
    sin_eq_of_two_zsmul h2b hQC hBC hQD hDF.symm
  have hnc1 : ¬Collinear ℝ ({Q, C, B} : Set ℂ) := not_collinear_QCB hABC hD hAFE hBDF hQB hQD
  have hnc2 : ¬Collinear ℝ ({Q, D, F} : Set ℂ) := not_collinear_QDF hAFE hBDF hQD hQF
  have hsCB : Real.sin (∠ Q C B) ≠ 0 :=
    ne_of_gt (EuclideanGeometry.sin_pos_of_not_collinear hnc1)
  have hsDF : Real.sin (∠ Q D F) ≠ 0 :=
    ne_of_gt (EuclideanGeometry.sin_pos_of_not_collinear hnc2)
  have hI := EuclideanGeometry.sin_angle_mul_dist_eq_sin_angle_mul_dist C B Q
  rw [EuclideanGeometry.angle_comm C B Q] at hI
  have hII := EuclideanGeometry.sin_angle_mul_dist_eq_sin_angle_mul_dist D F Q
  rw [EuclideanGeometry.angle_comm D F Q] at hII
  have hI' : Real.sin (∠ Q B C) * dist Q B = Real.sin (∠ Q C B) * dist Q C := by
    rw [dist_comm Q B]; exact hI
  have hII' : Real.sin (∠ Q F D) * dist Q F = Real.sin (∠ Q D F) * dist Q D := by
    rw [dist_comm Q F]; exact hII
  have key : dist Q C * dist Q F * (Real.sin (∠ Q C B) * Real.sin (∠ Q D F)) =
      dist Q D * dist Q B * (Real.sin (∠ Q C B) * Real.sin (∠ Q D F)) := by
    calc dist Q C * dist Q F * (Real.sin (∠ Q C B) * Real.sin (∠ Q D F))
        = (Real.sin (∠ Q C B) * dist Q C) * (Real.sin (∠ Q D F) * dist Q F) := by ring
      _ = (Real.sin (∠ Q B C) * dist Q B) * (Real.sin (∠ Q D F) * dist Q F) := by rw [← hI']
      _ = (Real.sin (∠ Q F D) * dist Q B) * (Real.sin (∠ Q D F) * dist Q F) := by rw [hs1]
      _ = (Real.sin (∠ Q F D) * dist Q B) * (Real.sin (∠ Q C B) * dist Q F) := by rw [← hs2]
      _ = (Real.sin (∠ Q F D) * dist Q F) * (Real.sin (∠ Q C B) * dist Q B) := by ring
      _ = (Real.sin (∠ Q D F) * dist Q D) * (Real.sin (∠ Q C B) * dist Q B) := by rw [← hII']
      _ = dist Q D * dist Q B * (Real.sin (∠ Q C B) * Real.sin (∠ Q D F)) := by ring
  exact mul_right_cancel₀ (mul_ne_zero hsCB hsDF) key

/-!
### C4: position arguments — the values and signs of the angles at `Q`
-/

/-- Auxiliary: `-(π - θ) = π - (-θ)` for oriented angles (since `-π = π`). -/
lemma neg_pi_sub' (θ : Real.Angle) : -(π - θ) = π - (-θ) := by
  have hπ : -(π : Real.Angle) = π :=
    neg_eq_iff_add_eq_zero.mpr Real.Angle.coe_pi_add_coe_pi
  rw [neg_sub, sub_eq_add_neg, hπ, sub_eq_add_neg, neg_neg, add_comm]

/-- The three vertices of a triangle see the same orientation:
`sign ∡CBA = sign ∡BAC`. -/
lemma sign_oangle_CBA {A B C : ℂ} (hCB : C ≠ B) (hAB : A ≠ B) (hBA : B ≠ A)
    (hCA : C ≠ A) :
    (∡ C B A).sign = (∡ B A C).sign := by
  rw [oangle'_sign _ _ _ hCB hAB, oangle'_sign _ _ _ hBA hCA]
  have he : cprod (C - B) (A - B) = cprod (B - A) (C - A) := by
    simp only [cprod_eq, Complex.sub_re, Complex.sub_im]
    ring
  rw [he]

/-- `sign ∡ACB = sign ∡BAC`. -/
lemma sign_oangle_ACB {A B C : ℂ} (hAC : A ≠ C) (hBC : B ≠ C) (hBA : B ≠ A)
    (hCA : C ≠ A) :
    (∡ A C B).sign = (∡ B A C).sign := by
  rw [oangle'_sign _ _ _ hAC hBC, oangle'_sign _ _ _ hBA hCA]
  have he : cprod (A - C) (B - C) = cprod (B - A) (C - A) := by
    simp only [cprod_eq, Complex.sub_re, Complex.sub_im]
    ring
  rw [he]

/-- Ray equality: `∡EAF = -∡BAC`. -/
lemma oangle_EAF {A B C E F : ℂ} (hF : Wbtw ℝ A F B) (hE : Wbtw ℝ C E A)
    (hBA : B ≠ A) (hCA : C ≠ A) (hAE : A ≠ E) (hAF : A ≠ F) (hCE : C ≠ E)
    (hBF : B ≠ F) :
    ∡ E A F = -∡ B A C := by
  obtain ⟨e, he0, he1, hE'⟩ := wbtw_param hE hCE hAE
  obtain ⟨f, hf0, hf1, hF'⟩ := wbtw_param hF hAF hBF
  have h1 : E - A = (1 - e) • (C - A) := by rw [hE']; module
  have h2 : F - A = f • (B - A) := by rw [hF']; module
  have h3 : ∡ E A F = ∡ C A B := by
    rw [oangle_eq_of_smul_left_pos hAE.symm hCA hAF.symm (sub_pos.mpr he1) h1]
    exact oangle_eq_of_smul_right_pos hCA hBA hAF.symm hf0 h2
  rw [h3]
  exact EuclideanGeometry.oangle_rev B A C

/-- Ray equality: `∡FBD = -∡CBA`. -/
lemma oangle_FBD {A B C D F : ℂ} (hF : Wbtw ℝ A F B) (hD : Wbtw ℝ B D C)
    (hAF : A ≠ F) (hBF : B ≠ F) (hBD : B ≠ D) (hCD : C ≠ D) (hBA : B ≠ A)
    (hBC : B ≠ C) :
    ∡ F B D = -∡ C B A := by
  obtain ⟨f, hf0, hf1, hF'⟩ := wbtw_param hF hAF hBF
  obtain ⟨d, hd0, hd1, hD'⟩ := wbtw_param hD hBD hCD
  have h1 : F - B = (1 - f) • (A - B) := by rw [hF']; module
  have h2 : D - B = d • (C - B) := by rw [hD']; module
  have h3 : ∡ F B D = ∡ A B C := by
    rw [oangle_eq_of_smul_left_pos hBF.symm hBA.symm hBD.symm (sub_pos.mpr hf1) h1]
    exact oangle_eq_of_smul_right_pos hBA.symm hBC.symm hBD.symm hd0 h2
  rw [h3]
  exact EuclideanGeometry.oangle_rev C B A

/-- Ray equality: `∡DCE = -∡ACB`. -/
lemma oangle_DCE {A B C D E : ℂ} (hD : Wbtw ℝ B D C) (hE : Wbtw ℝ C E A)
    (hBD : B ≠ D) (hCD : C ≠ D) (hCE : C ≠ E) (hAE : A ≠ E) (hBC : B ≠ C)
    (hCA : C ≠ A) :
    ∡ D C E = -∡ A C B := by
  obtain ⟨d, hd0, hd1, hD'⟩ := wbtw_param hD hBD hCD
  obtain ⟨e, he0, he1, hE'⟩ := wbtw_param hE hCE hAE
  have h1 : D - C = (1 - d) • (B - C) := by rw [hD']; module
  have h2 : E - C = e • (A - C) := by rw [hE']; module
  have h3 : ∡ D C E = ∡ B C A := by
    rw [oangle_eq_of_smul_left_pos hCD.symm hBC hCE.symm (sub_pos.mpr hd1) h1]
    exact oangle_eq_of_smul_right_pos hBC hCA.symm hCE.symm he0 h2
  rw [h3]
  exact EuclideanGeometry.oangle_rev A C B

/-- Value: `∡AEF + ∡FDB = π - ∡BAC`. -/
lemma val_AEF_FDB {A B C D E F : ℂ}
    (hE : Wbtw ℝ C E A) (hF : Wbtw ℝ A F B) (hα₁o : ∡ A F E = ∡ B D F)
    (hAF : A ≠ F) (hAE : A ≠ E) (hFE : F ≠ E) (hBA : B ≠ A) (hCA : C ≠ A)
    (hCE : C ≠ E) (hBF : B ≠ F) :
    ∡ A E F + ∡ F D B = π - ∡ B A C := by
  have htri : ∡ A F E + ∡ F E A + ∡ E A F = π :=
    EuclideanGeometry.oangle_add_oangle_add_oangle_eq_pi hAF.symm hFE.symm hAE
  have h2 : ∡ A F E + ∡ F E A = π - ∡ E A F := by rw [← htri]; abel
  have hEAF : ∡ E A F = -∡ B A C := oangle_EAF hF hE hBA hCA hAE hAF hCE hBF
  rw [EuclideanGeometry.oangle_rev F E A, EuclideanGeometry.oangle_rev B D F, ← hα₁o,
    ← neg_add_rev, h2, hEAF, neg_pi_sub', neg_neg]

/-- Value: `∡EFA + ∡AEF = π - ∡BAC`. -/
lemma val_EFA_AEF {A B C E F : ℂ}
    (hE : Wbtw ℝ C E A) (hF : Wbtw ℝ A F B)
    (hAF : A ≠ F) (hAE : A ≠ E) (hFE : F ≠ E) (hBA : B ≠ A) (hCA : C ≠ A)
    (hCE : C ≠ E) (hBF : B ≠ F) :
    ∡ E F A + ∡ A E F = π - ∡ B A C := by
  have htri : ∡ A F E + ∡ F E A + ∡ E A F = π :=
    EuclideanGeometry.oangle_add_oangle_add_oangle_eq_pi hAF.symm hFE.symm hAE
  have h2 : ∡ F E A + ∡ A F E = π - ∡ E A F := by rw [← htri]; abel
  have hEAF : ∡ E A F = -∡ B A C := oangle_EAF hF hE hBA hCA hAE hAF hCE hBF
  rw [EuclideanGeometry.oangle_rev A F E, EuclideanGeometry.oangle_rev F E A,
    ← neg_add_rev, h2, hEAF, neg_pi_sub', neg_neg]

/-- Value: `∡BFD + ∡DEC = π - ∡CBA`. -/
lemma val_BFD_DEC {A B C D E F : ℂ}
    (hD : Wbtw ℝ B D C) (hF : Wbtw ℝ A F B) (hα₂o : ∡ B D F = ∡ C E D)
    (hBD : B ≠ D) (hDF : D ≠ F) (hBF : B ≠ F) (hBA : B ≠ A) (hCD : C ≠ D)
    (hBC : B ≠ C) (hAF : A ≠ F) :
    ∡ B F D + ∡ D E C = π - ∡ C B A := by
  have htri : ∡ B D F + ∡ D F B + ∡ F B D = π :=
    EuclideanGeometry.oangle_add_oangle_add_oangle_eq_pi hBD.symm hDF.symm hBF
  have h2 : ∡ B D F + ∡ D F B = π - ∡ F B D := by rw [← htri]; abel
  have hFBD : ∡ F B D = -∡ C B A := oangle_FBD hF hD hAF hBF hBD hCD hBA hBC
  rw [EuclideanGeometry.oangle_rev D F B, EuclideanGeometry.oangle_rev C E D, ← hα₂o,
    ← neg_add_rev, h2, hFBD, neg_pi_sub', neg_neg]

/-- Value: `∡FDB + ∡BFD = π - ∡CBA`. -/
lemma val_FDB_BFD {A B C D F : ℂ}
    (hD : Wbtw ℝ B D C) (hF : Wbtw ℝ A F B)
    (hBD : B ≠ D) (hDF : D ≠ F) (hBF : B ≠ F) (hBA : B ≠ A) (hCD : C ≠ D)
    (hBC : B ≠ C) (hAF : A ≠ F) :
    ∡ F D B + ∡ B F D = π - ∡ C B A := by
  have htri : ∡ B D F + ∡ D F B + ∡ F B D = π :=
    EuclideanGeometry.oangle_add_oangle_add_oangle_eq_pi hBD.symm hDF.symm hBF
  have h2 : ∡ D F B + ∡ B D F = π - ∡ F B D := by rw [← htri]; abel
  have hFBD : ∡ F B D = -∡ C B A := oangle_FBD hF hD hAF hBF hBD hCD hBA hBC
  rw [EuclideanGeometry.oangle_rev B D F, EuclideanGeometry.oangle_rev D F B,
    ← neg_add_rev, h2, hFBD, neg_pi_sub', neg_neg]

/-- Value: `∡CDE + ∡EFA = π - ∡ACB`. -/
lemma val_CDE_EFA {A B C D E F : ℂ}
    (hD : Wbtw ℝ B D C) (hE : Wbtw ℝ C E A)
    (hα₁o : ∡ A F E = ∡ B D F) (hα₂o : ∡ B D F = ∡ C E D)
    (hCE : C ≠ E) (hDE : D ≠ E) (hCD : C ≠ D) (hBC : B ≠ C) (hCA : C ≠ A)
    (hBD : B ≠ D) (hAE : A ≠ E) :
    ∡ C D E + ∡ E F A = π - ∡ A C B := by
  have htri : ∡ C E D + ∡ E D C + ∡ D C E = π :=
    EuclideanGeometry.oangle_add_oangle_add_oangle_eq_pi hCE.symm hDE hCD
  have h2 : ∡ C E D + ∡ E D C = π - ∡ D C E := by rw [← htri]; abel
  have hDCE : ∡ D C E = -∡ A C B := oangle_DCE hD hE hBD hCD hCE hAE hBC hCA
  have hα : ∡ A F E = ∡ C E D := hα₁o.trans hα₂o
  rw [EuclideanGeometry.oangle_rev E D C, EuclideanGeometry.oangle_rev A F E, hα,
    ← neg_add_rev, h2, hDCE, neg_pi_sub', neg_neg]

/-- Betweenness sign: `sign ∡AQF = sign ∡AQB`. -/
lemma sign_oangle_AQF {A B F Q : ℂ} (hF : Wbtw ℝ A F B)
    (hAF : A ≠ F) (hBF : B ≠ F) (hAQ : A ≠ Q) (hFQ : F ≠ Q) (hBQ : B ≠ Q) :
    (∡ A Q F).sign = (∡ A Q B).sign := by
  obtain ⟨f, hf0, hf1, hF'⟩ := wbtw_param hF hAF hBF
  rw [oangle'_sign _ _ _ hAQ hFQ, oangle'_sign _ _ _ hAQ hBQ]
  have h1 : F - Q = f • (B - Q) + (1 - f) • (A - Q) := by rw [hF']; module
  rw [h1, cprod_add_right, cprod_smul_right, cprod_smul_right, cprod_self, mul_zero,
    add_zero, sign_mul, sign_pos hf0, one_mul]

/-- Betweenness sign: `sign ∡FQB = sign ∡AQB`. -/
lemma sign_oangle_FQB {A B F Q : ℂ} (hF : Wbtw ℝ A F B)
    (hAF : A ≠ F) (hBF : B ≠ F) (hAQ : A ≠ Q) (hFQ : F ≠ Q) (hBQ : B ≠ Q) :
    (∡ F Q B).sign = (∡ A Q B).sign := by
  obtain ⟨f, hf0, hf1, hF'⟩ := wbtw_param hF hAF hBF
  rw [oangle'_sign _ _ _ hFQ hBQ, oangle'_sign _ _ _ hAQ hBQ]
  have h1 : F - Q = f • (B - Q) + (1 - f) • (A - Q) := by rw [hF']; module
  rw [h1, cprod_add_left, cprod_smul_left, cprod_smul_left, cprod_self, mul_zero,
    zero_add, sign_mul, sign_pos (sub_pos.mpr hf1), one_mul]

/-- Betweenness sign: `sign ∡BQD = sign ∡BQC`. -/
lemma sign_oangle_BQD {B C D Q : ℂ} (hD : Wbtw ℝ B D C)
    (hBD : B ≠ D) (hCD : C ≠ D) (hBQ : B ≠ Q) (hDQ : D ≠ Q) (hCQ : C ≠ Q) :
    (∡ B Q D).sign = (∡ B Q C).sign := by
  obtain ⟨d, hd0, hd1, hD'⟩ := wbtw_param hD hBD hCD
  rw [oangle'_sign _ _ _ hBQ hDQ, oangle'_sign _ _ _ hBQ hCQ]
  have h1 : D - Q = (1 - d) • (B - Q) + d • (C - Q) := by rw [hD']; module
  rw [h1, cprod_add_right, cprod_smul_right, cprod_smul_right, cprod_self, mul_zero,
    zero_add, sign_mul, sign_pos hd0, one_mul]

/-- Betweenness sign: `sign ∡DQC = sign ∡BQC`. -/
lemma sign_oangle_DQC {B C D Q : ℂ} (hD : Wbtw ℝ B D C)
    (hBD : B ≠ D) (hCD : C ≠ D) (hBQ : B ≠ Q) (hDQ : D ≠ Q) (hCQ : C ≠ Q) :
    (∡ D Q C).sign = (∡ B Q C).sign := by
  obtain ⟨d, hd0, hd1, hD'⟩ := wbtw_param hD hBD hCD
  rw [oangle'_sign _ _ _ hDQ hCQ, oangle'_sign _ _ _ hBQ hCQ]
  have h1 : D - Q = (1 - d) • (B - Q) + d • (C - Q) := by rw [hD']; module
  rw [h1, cprod_add_left, cprod_smul_left, cprod_smul_left, cprod_self, mul_zero,
    add_zero, sign_mul, sign_pos (sub_pos.mpr hd1), one_mul]

/-- Betweenness sign: `sign ∡CQE = sign ∡CQA`. -/
lemma sign_oangle_CQE {A C E Q : ℂ} (hE : Wbtw ℝ C E A)
    (hCE : C ≠ E) (hAE : A ≠ E) (hCQ : C ≠ Q) (hEQ : E ≠ Q) (hAQ : A ≠ Q) :
    (∡ C Q E).sign = (∡ C Q A).sign := by
  obtain ⟨e, he0, he1, hE'⟩ := wbtw_param hE hCE hAE
  rw [oangle'_sign _ _ _ hCQ hEQ, oangle'_sign _ _ _ hCQ hAQ]
  have h1 : E - Q = (1 - e) • (C - Q) + e • (A - Q) := by rw [hE']; module
  rw [h1, cprod_add_right, cprod_smul_right, cprod_smul_right, cprod_self, mul_zero,
    zero_add, sign_mul, sign_pos he0, one_mul]

/-- Betweenness sign: `sign ∡EQA = sign ∡CQA`. -/
lemma sign_oangle_EQA {A C E Q : ℂ} (hE : Wbtw ℝ C E A)
    (hCE : C ≠ E) (hAE : A ≠ E) (hCQ : C ≠ Q) (hEQ : E ≠ Q) (hAQ : A ≠ Q) :
    (∡ E Q A).sign = (∡ C Q A).sign := by
  obtain ⟨e, he0, he1, hE'⟩ := wbtw_param hE hCE hAE
  rw [oangle'_sign _ _ _ hEQ hAQ, oangle'_sign _ _ _ hCQ hAQ]
  have h1 : E - Q = (1 - e) • (C - Q) + e • (A - Q) := by rw [hE']; module
  rw [h1, cprod_add_left, cprod_smul_left, cprod_smul_left, cprod_self, mul_zero,
    add_zero, sign_mul, sign_pos (sub_pos.mpr he1), one_mul]

/-- The sign and value of `∡AQB`: `sign ∡AQB = sign ∡BAC` and
`∡AQB = π - ∡BAC`. The proof is the case analysis on `2∡AQB = -2∡BAC`:
the `-∡BAC` branch contradicts the betweenness signs. -/
lemma sign_oangle_AQB {A B C D E F : ℂ}
    (hABC : ¬Collinear ℝ {A, B, C})
    (hD : Wbtw ℝ B D C) (hE : Wbtw ℝ C E A) (hF : Wbtw ℝ A F B)
    (hα₁o : ∡ A F E = ∡ B D F)
    (hAFE : ¬Collinear ℝ {A, F, E}) (hBDF : ¬Collinear ℝ {B, D, F})
    (hCED : ¬Collinear ℝ {C, E, D}) (hDEF : ¬Collinear ℝ {D, E, F})
    (hQA : miquelQ hAFE hBDF ≠ A) (hQB : miquelQ hAFE hBDF ≠ B)
    (hQF : miquelQ hAFE hBDF ≠ F) (_hQD : miquelQ hAFE hBDF ≠ D) :
    (∡ A (miquelQ hAFE hBDF) B).sign = (∡ B A C).sign ∧
      ∡ A (miquelQ hAFE hBDF) B = π - ∡ B A C := by
  have hAF : A ≠ F := ne₁₂_of_not_collinear hAFE
  have hAE : A ≠ E := ne₁₃_of_not_collinear hAFE
  have hFE : F ≠ E := (ne₂₃_of_not_collinear hDEF).symm
  have hBD : B ≠ D := ne₁₂_of_not_collinear hBDF
  have hDF : D ≠ F := ne₂₃_of_not_collinear hBDF
  have hBF : B ≠ F := ne₁₃_of_not_collinear hBDF
  have hBA : B ≠ A := (ne₁₂_of_not_collinear hABC).symm
  have hCA : C ≠ A := (ne₁₃_of_not_collinear hABC).symm
  have hCE : C ≠ E := ne₁₂_of_not_collinear hCED
  have hCD : C ≠ D := ne₁₃_of_not_collinear hCED
  set Q := miquelQ hAFE hBDF with hQdef
  have hP1 : (2 : ℤ) • ∡ A Q F = (2 : ℤ) • ∡ A E F :=
    Sphere.two_zsmul_oangle_eq (A_mem_miquelS₁ hAFE) (miquelQ_mem_s₁ hAFE hBDF)
      (E_mem_miquelS₁ hAFE) (F_mem_miquelS₁ hAFE) hQA hQF hAE.symm hFE.symm
  have hP2 : (2 : ℤ) • ∡ F Q B = (2 : ℤ) • ∡ F D B :=
    Sphere.two_zsmul_oangle_eq (F_mem_miquelS₂ hBDF) (miquelQ_mem_s₂ hAFE hBDF)
      (D_mem_miquelS₂ hBDF) (B_mem_miquelS₂ hBDF) hQF hQB hDF hBD.symm
  have hP3 : ∡ A Q F + ∡ F Q B = ∡ A Q B :=
    EuclideanGeometry.oangle_add hQA.symm hQF.symm hQB.symm
  have hP4 : ∡ A E F + ∡ F D B = π - ∡ B A C :=
    val_AEF_FDB hE hF hα₁o hAF hAE hFE hBA hCA hCE hBF
  have h2 : (2 : ℤ) • ∡ A Q B = (2 : ℤ) • (-∡ B A C) := by
    have h2a : (2 : ℤ) • ∡ A Q B = (2 : ℤ) • (π - ∡ B A C) := by
      rw [← hP3, smul_add, hP1, hP2, ← smul_add, hP4]
    rw [smul_sub, Real.Angle.two_zsmul_coe_pi, zero_sub] at h2a
    rw [smul_neg]; exact h2a
  have hσ : (∡ B A C).sign ≠ 0 := by
    rw [sign_oangle_BAC hBA hCA]
    exact sign_ne_zero.mpr (cprod_ne_zero_of_not_collinear hABC)
  have hbet1 : (∡ A Q F).sign = (∡ A Q B).sign :=
    sign_oangle_AQF hF hAF hBF hQA.symm hQF.symm hQB.symm
  have hbet2 : (∡ F Q B).sign = (∡ A Q B).sign :=
    sign_oangle_FQB hF hAF hBF hQA.symm hQF.symm hQB.symm
  have hsignAEF : (∡ A E F).sign = (∡ B A C).sign := by
    rw [EuclideanGeometry.oangle_rev F E A, Real.Angle.sign_neg,
      sign_oangle_FEA hF hE hAF hBF hCE hAE hFE hBA hCA, neg_neg]
  have hsignFDB : (∡ F D B).sign = (∡ B A C).sign := by
    rw [EuclideanGeometry.oangle_rev B D F, Real.Angle.sign_neg,
      sign_oangle_BDF hD hF hBD hCD hAF hBF hDF hBA hCA, neg_neg]
  rcases Real.Angle.two_zsmul_eq_iff.mp h2 with hcase | hcase
  · -- the branch `∡AQB = -∡BAC` contradicts the betweenness signs
    have hsAQB : (∡ A Q B).sign = -(∡ B A C).sign := by
      rw [hcase, Real.Angle.sign_neg]
    have h1 : ∡ A Q F = ∡ A E F + π := by
      rcases Real.Angle.two_zsmul_eq_iff.mp hP1 with h1 | h1
      · exfalso
        have hs : (∡ A Q F).sign = (∡ B A C).sign := by rw [h1]; exact hsignAEF
        rw [hbet1, hsAQB] at hs
        exact hσ (SignType.neg_eq_self_iff.mp hs)
      · exact h1
    have h2' : ∡ F Q B = ∡ F D B + π := by
      rcases Real.Angle.two_zsmul_eq_iff.mp hP2 with h2' | h2'
      · exfalso
        have hs : (∡ F Q B).sign = (∡ B A C).sign := by rw [h2']; exact hsignFDB
        rw [hbet2, hsAQB] at hs
        exact hσ (SignType.neg_eq_self_iff.mp hs)
      · exact h2'
    have hval : ∡ A Q B = π - ∡ B A C := by
      rw [← hP3, h1, h2']
      calc ∡ A E F + π + (∡ F D B + π) = (∡ A E F + ∡ F D B) + (π + π) := by abel
        _ = ∡ A E F + ∡ F D B := by rw [Real.Angle.coe_pi_add_coe_pi, add_zero]
        _ = π - ∡ B A C := hP4
    rw [hcase] at hval
    have hπ0 : (π : Real.Angle) = 0 := by
      rw [sub_eq_add_neg] at hval
      have h4 : π + (-∡ B A C) = 0 + (-∡ B A C) := by rw [← hval, zero_add]
      exact add_right_cancel_iff.mp h4
    exact absurd hπ0 Real.Angle.pi_ne_zero
  · have hval : ∡ A Q B = π - ∡ B A C := by
      rw [hcase, sub_eq_add_neg, add_comm]
    exact ⟨by rw [hval, Real.Angle.sign_pi_sub], hval⟩

/-- The sign and value of `∡BQC`. -/
lemma sign_oangle_BQC {A B C D E F : ℂ}
    (hABC : ¬Collinear ℝ {A, B, C})
    (hD : Wbtw ℝ B D C) (hE : Wbtw ℝ C E A) (hF : Wbtw ℝ A F B)
    (hα₁o : ∡ A F E = ∡ B D F) (hα₂o : ∡ B D F = ∡ C E D)
    (hAFE : ¬Collinear ℝ {A, F, E}) (hBDF : ¬Collinear ℝ {B, D, F})
    (hCED : ¬Collinear ℝ {C, E, D}) (hDEF : ¬Collinear ℝ {D, E, F})
    (hQB : miquelQ hAFE hBDF ≠ B) (hQC : miquelQ hAFE hBDF ≠ C)
    (hQD : miquelQ hAFE hBDF ≠ D) (_hQF : miquelQ hAFE hBDF ≠ F) :
    (∡ B (miquelQ hAFE hBDF) C).sign = (∡ B A C).sign ∧
      ∡ B (miquelQ hAFE hBDF) C = π - ∡ C B A := by
  have hBD : B ≠ D := ne₁₂_of_not_collinear hBDF
  have hDF : D ≠ F := ne₂₃_of_not_collinear hBDF
  have hBF : B ≠ F := ne₁₃_of_not_collinear hBDF
  have hCD : C ≠ D := ne₁₃_of_not_collinear hCED
  have hCE : C ≠ E := ne₁₂_of_not_collinear hCED
  have hDE : D ≠ E := ne₁₂_of_not_collinear hDEF
  have hBC : B ≠ C := ne₂₃_of_not_collinear hABC
  have hBA : B ≠ A := (ne₁₂_of_not_collinear hABC).symm
  have hCA : C ≠ A := (ne₁₃_of_not_collinear hABC).symm
  have hAF : A ≠ F := ne₁₂_of_not_collinear hAFE
  have hAE : A ≠ E := ne₁₃_of_not_collinear hAFE
  set Q := miquelQ hAFE hBDF with hQdef
  have hP1 : (2 : ℤ) • ∡ B Q D = (2 : ℤ) • ∡ B F D :=
    Sphere.two_zsmul_oangle_eq (B_mem_miquelS₂ hBDF) (miquelQ_mem_s₂ hAFE hBDF)
      (F_mem_miquelS₂ hBDF) (D_mem_miquelS₂ hBDF) hQB hQD hBF.symm hDF.symm
  have hP2 : (2 : ℤ) • ∡ D Q C = (2 : ℤ) • ∡ D E C :=
    Sphere.two_zsmul_oangle_eq (D_mem_miquelS₃ hCED)
      (miquelQ_mem_s₃ hABC hD hE hF hα₁o hα₂o hAFE hBDF hCED hDEF)
      (E_mem_miquelS₃ hCED) (C_mem_miquelS₃ hCED) hQD hQC hDE.symm hCE.symm
  have hP3 : ∡ B Q D + ∡ D Q C = ∡ B Q C :=
    EuclideanGeometry.oangle_add hQB.symm hQD.symm hQC.symm
  have hP4 : ∡ B F D + ∡ D E C = π - ∡ C B A :=
    val_BFD_DEC hD hF hα₂o hBD hDF hBF hBA hCD hBC hAF
  have h2 : (2 : ℤ) • ∡ B Q C = (2 : ℤ) • (-∡ C B A) := by
    have h2a : (2 : ℤ) • ∡ B Q C = (2 : ℤ) • (π - ∡ C B A) := by
      rw [← hP3, smul_add, hP1, hP2, ← smul_add, hP4]
    rw [smul_sub, Real.Angle.two_zsmul_coe_pi, zero_sub] at h2a
    rw [smul_neg]; exact h2a
  have hσ : (∡ B A C).sign ≠ 0 := by
    rw [sign_oangle_BAC hBA hCA]
    exact sign_ne_zero.mpr (cprod_ne_zero_of_not_collinear hABC)
  have hbet1 : (∡ B Q D).sign = (∡ B Q C).sign :=
    sign_oangle_BQD hD hBD hCD hQB.symm hQD.symm hQC.symm
  have hbet2 : (∡ D Q C).sign = (∡ B Q C).sign :=
    sign_oangle_DQC hD hBD hCD hQB.symm hQD.symm hQC.symm
  have hsignBFD : (∡ B F D).sign = (∡ B A C).sign :=
    sign_oangle_BFD hD hF hBD hCD hAF hBF hDF hBA hCA
  have hsignDEC : (∡ D E C).sign = (∡ B A C).sign := by
    rw [EuclideanGeometry.oangle_rev C E D, Real.Angle.sign_neg,
      sign_oangle_CED hD hE hBD hCD hCE hAE hDE hBA hCA, neg_neg]
  have hsignCBA : (∡ C B A).sign = (∡ B A C).sign :=
    sign_oangle_CBA hBC.symm hBA.symm hBA hCA
  rcases Real.Angle.two_zsmul_eq_iff.mp h2 with hcase | hcase
  · have hsBQC : (∡ B Q C).sign = -(∡ B A C).sign := by
      rw [hcase, Real.Angle.sign_neg, hsignCBA]
    have h1 : ∡ B Q D = ∡ B F D + π := by
      rcases Real.Angle.two_zsmul_eq_iff.mp hP1 with h1 | h1
      · exfalso
        have hs : (∡ B Q D).sign = (∡ B A C).sign := by rw [h1]; exact hsignBFD
        rw [hbet1, hsBQC] at hs
        exact hσ (SignType.neg_eq_self_iff.mp hs)
      · exact h1
    have h2' : ∡ D Q C = ∡ D E C + π := by
      rcases Real.Angle.two_zsmul_eq_iff.mp hP2 with h2' | h2'
      · exfalso
        have hs : (∡ D Q C).sign = (∡ B A C).sign := by rw [h2']; exact hsignDEC
        rw [hbet2, hsBQC] at hs
        exact hσ (SignType.neg_eq_self_iff.mp hs)
      · exact h2'
    have hval : ∡ B Q C = π - ∡ C B A := by
      rw [← hP3, h1, h2']
      calc ∡ B F D + π + (∡ D E C + π) = (∡ B F D + ∡ D E C) + (π + π) := by abel
        _ = ∡ B F D + ∡ D E C := by rw [Real.Angle.coe_pi_add_coe_pi, add_zero]
        _ = π - ∡ C B A := hP4
    rw [hcase] at hval
    have hπ0 : (π : Real.Angle) = 0 := by
      rw [sub_eq_add_neg] at hval
      have h4 : π + (-∡ C B A) = 0 + (-∡ C B A) := by rw [← hval, zero_add]
      exact add_right_cancel_iff.mp h4
    exact absurd hπ0 Real.Angle.pi_ne_zero
  · have hval : ∡ B Q C = π - ∡ C B A := by
      rw [hcase, sub_eq_add_neg, add_comm]
    exact ⟨by rw [hval, Real.Angle.sign_pi_sub, hsignCBA], hval⟩

/-- The sign and value of `∡CQA`. -/
lemma sign_oangle_CQA {A B C D E F : ℂ}
    (hABC : ¬Collinear ℝ {A, B, C})
    (hD : Wbtw ℝ B D C) (hE : Wbtw ℝ C E A) (hF : Wbtw ℝ A F B)
    (hα₁o : ∡ A F E = ∡ B D F) (hα₂o : ∡ B D F = ∡ C E D)
    (hAFE : ¬Collinear ℝ {A, F, E}) (hBDF : ¬Collinear ℝ {B, D, F})
    (hCED : ¬Collinear ℝ {C, E, D}) (hDEF : ¬Collinear ℝ {D, E, F})
    (hQC : miquelQ hAFE hBDF ≠ C) (hQE : miquelQ hAFE hBDF ≠ E)
    (hQA : miquelQ hAFE hBDF ≠ A) :
    (∡ C (miquelQ hAFE hBDF) A).sign = (∡ B A C).sign ∧
      ∡ C (miquelQ hAFE hBDF) A = π - ∡ A C B := by
  have hCD : C ≠ D := ne₁₃_of_not_collinear hCED
  have hCE : C ≠ E := ne₁₂_of_not_collinear hCED
  have hDE : D ≠ E := ne₁₂_of_not_collinear hDEF
  have hFE : F ≠ E := (ne₂₃_of_not_collinear hDEF).symm
  have hAF : A ≠ F := ne₁₂_of_not_collinear hAFE
  have hAE : A ≠ E := ne₁₃_of_not_collinear hAFE
  have hBC : B ≠ C := ne₂₃_of_not_collinear hABC
  have hBA : B ≠ A := (ne₁₂_of_not_collinear hABC).symm
  have hCA : C ≠ A := (ne₁₃_of_not_collinear hABC).symm
  have hBD : B ≠ D := ne₁₂_of_not_collinear hBDF
  have hDF : D ≠ F := ne₂₃_of_not_collinear hBDF
  have hBF : B ≠ F := ne₁₃_of_not_collinear hBDF
  set Q := miquelQ hAFE hBDF with hQdef
  have hP1 : (2 : ℤ) • ∡ C Q E = (2 : ℤ) • ∡ C D E :=
    Sphere.two_zsmul_oangle_eq (C_mem_miquelS₃ hCED)
      (miquelQ_mem_s₃ hABC hD hE hF hα₁o hα₂o hAFE hBDF hCED hDEF)
      (D_mem_miquelS₃ hCED) (E_mem_miquelS₃ hCED) hQC hQE hCD.symm hDE
  have hP2 : (2 : ℤ) • ∡ E Q A = (2 : ℤ) • ∡ E F A :=
    Sphere.two_zsmul_oangle_eq (E_mem_miquelS₁ hAFE) (miquelQ_mem_s₁ hAFE hBDF)
      (F_mem_miquelS₁ hAFE) (A_mem_miquelS₁ hAFE) hQE hQA hFE hAF.symm
  have hP3 : ∡ C Q E + ∡ E Q A = ∡ C Q A :=
    EuclideanGeometry.oangle_add hQC.symm hQE.symm hQA.symm
  have hP4 : ∡ C D E + ∡ E F A = π - ∡ A C B :=
    val_CDE_EFA hD hE hα₁o hα₂o hCE hDE hCD hBC hCA hBD hAE
  have h2 : (2 : ℤ) • ∡ C Q A = (2 : ℤ) • (-∡ A C B) := by
    have h2a : (2 : ℤ) • ∡ C Q A = (2 : ℤ) • (π - ∡ A C B) := by
      rw [← hP3, smul_add, hP1, hP2, ← smul_add, hP4]
    rw [smul_sub, Real.Angle.two_zsmul_coe_pi, zero_sub] at h2a
    rw [smul_neg]; exact h2a
  have hσ : (∡ B A C).sign ≠ 0 := by
    rw [sign_oangle_BAC hBA hCA]
    exact sign_ne_zero.mpr (cprod_ne_zero_of_not_collinear hABC)
  have hbet1 : (∡ C Q E).sign = (∡ C Q A).sign :=
    sign_oangle_CQE hE hCE hAE hQC.symm hQE.symm hQA.symm
  have hbet2 : (∡ E Q A).sign = (∡ C Q A).sign :=
    sign_oangle_EQA hE hCE hAE hQC.symm hQE.symm hQA.symm
  have hsignCDE : (∡ C D E).sign = (∡ B A C).sign := by
    rw [EuclideanGeometry.oangle_rev E D C, Real.Angle.sign_neg,
      sign_oangle_EDC hD hE hBD hCD hCE hAE hDE hBA hCA, neg_neg]
  have hsignEFA : (∡ E F A).sign = (∡ B A C).sign := by
    rw [EuclideanGeometry.oangle_rev A F E, Real.Angle.sign_neg,
      sign_oangle_AFE hF hE hAF hBF hCE hAE hFE hBA hCA, neg_neg]
  have hsignACB : (∡ A C B).sign = (∡ B A C).sign :=
    sign_oangle_ACB hCA.symm hBC hBA hCA
  rcases Real.Angle.two_zsmul_eq_iff.mp h2 with hcase | hcase
  · have hsCQA : (∡ C Q A).sign = -(∡ B A C).sign := by
      rw [hcase, Real.Angle.sign_neg, hsignACB]
    have h1 : ∡ C Q E = ∡ C D E + π := by
      rcases Real.Angle.two_zsmul_eq_iff.mp hP1 with h1 | h1
      · exfalso
        have hs : (∡ C Q E).sign = (∡ B A C).sign := by rw [h1]; exact hsignCDE
        rw [hbet1, hsCQA] at hs
        exact hσ (SignType.neg_eq_self_iff.mp hs)
      · exact h1
    have h2' : ∡ E Q A = ∡ E F A + π := by
      rcases Real.Angle.two_zsmul_eq_iff.mp hP2 with h2' | h2'
      · exfalso
        have hs : (∡ E Q A).sign = (∡ B A C).sign := by rw [h2']; exact hsignEFA
        rw [hbet2, hsCQA] at hs
        exact hσ (SignType.neg_eq_self_iff.mp hs)
      · exact h2'
    have hval : ∡ C Q A = π - ∡ A C B := by
      rw [← hP3, h1, h2']
      calc ∡ C D E + π + (∡ E F A + π) = (∡ C D E + ∡ E F A) + (π + π) := by abel
        _ = ∡ C D E + ∡ E F A := by rw [Real.Angle.coe_pi_add_coe_pi, add_zero]
        _ = π - ∡ A C B := hP4
    rw [hcase] at hval
    have hπ0 : (π : Real.Angle) = 0 := by
      rw [sub_eq_add_neg] at hval
      have h4 : π + (-∡ A C B) = 0 + (-∡ A C B) := by rw [← hval, zero_add]
      exact add_right_cancel_iff.mp h4
    exact absurd hπ0 Real.Angle.pi_ne_zero
  · have hval : ∡ C Q A = π - ∡ A C B := by
      rw [hcase, sub_eq_add_neg, add_comm]
    exact ⟨by rw [hval, Real.Angle.sign_pi_sub, hsignACB], hval⟩

/-- The first key angle equality: `∡EQF = ∡AQB`. -/
lemma oangle_EQF_eq_AQB {A B C D E F : ℂ}
    (hABC : ¬Collinear ℝ {A, B, C})
    (hD : Wbtw ℝ B D C) (hE : Wbtw ℝ C E A) (hF : Wbtw ℝ A F B)
    (hα₁o : ∡ A F E = ∡ B D F) (hα₂o : ∡ B D F = ∡ C E D)
    (hAFE : ¬Collinear ℝ {A, F, E}) (hBDF : ¬Collinear ℝ {B, D, F})
    (hCED : ¬Collinear ℝ {C, E, D}) (hDEF : ¬Collinear ℝ {D, E, F})
    (hQA : miquelQ hAFE hBDF ≠ A) (hQB : miquelQ hAFE hBDF ≠ B)
    (hQC : miquelQ hAFE hBDF ≠ C) (hQD : miquelQ hAFE hBDF ≠ D)
    (hQE : miquelQ hAFE hBDF ≠ E) (hQF : miquelQ hAFE hBDF ≠ F) :
    ∡ E (miquelQ hAFE hBDF) F = ∡ A (miquelQ hAFE hBDF) B := by
  have hAF : A ≠ F := ne₁₂_of_not_collinear hAFE
  have hAE : A ≠ E := ne₁₃_of_not_collinear hAFE
  have hFE : F ≠ E := (ne₂₃_of_not_collinear hDEF).symm
  have hBA : B ≠ A := (ne₁₂_of_not_collinear hABC).symm
  have hCA : C ≠ A := (ne₁₃_of_not_collinear hABC).symm
  have hCE : C ≠ E := ne₁₂_of_not_collinear hCED
  have hBF : B ≠ F := ne₁₃_of_not_collinear hBDF
  set Q := miquelQ hAFE hBDF with hQdef
  obtain ⟨hsAQB, hvalAQB⟩ := sign_oangle_AQB hABC hD hE hF hα₁o hAFE hBDF hCED hDEF
    hQA hQB hQF hQD
  obtain ⟨hsCQA, -⟩ := sign_oangle_CQA hABC hD hE hF hα₁o hα₂o hAFE hBDF hCED hDEF
    hQC hQE hQA
  have hσ : (∡ B A C).sign ≠ 0 := by
    rw [sign_oangle_BAC hBA hCA]
    exact sign_ne_zero.mpr (cprod_ne_zero_of_not_collinear hABC)
  have hP1 : (2 : ℤ) • ∡ E Q A = (2 : ℤ) • ∡ E F A :=
    Sphere.two_zsmul_oangle_eq (E_mem_miquelS₁ hAFE) (miquelQ_mem_s₁ hAFE hBDF)
      (F_mem_miquelS₁ hAFE) (A_mem_miquelS₁ hAFE) hQE hQA hFE hAF.symm
  have hsEQA : (∡ E Q A).sign = (∡ B A C).sign :=
    (sign_oangle_EQA hE hCE hAE hQC.symm hQE.symm hQA.symm).trans hsCQA
  have hsEFA : (∡ E F A).sign = (∡ B A C).sign := by
    rw [EuclideanGeometry.oangle_rev A F E, Real.Angle.sign_neg,
      sign_oangle_AFE hF hE hAF hBF hCE hAE hFE hBA hCA, neg_neg]
  have hsEQA0 : (∡ E Q A).sign ≠ 0 := by rwa [hsEQA]
  have hrep1 : ∡ E Q A = ∡ E F A :=
    (Real.Angle.two_zsmul_eq_iff_eq hsEQA0 (by rw [hsEQA, hsEFA])).mp hP1
  have hP2 : (2 : ℤ) • ∡ A Q F = (2 : ℤ) • ∡ A E F :=
    Sphere.two_zsmul_oangle_eq (A_mem_miquelS₁ hAFE) (miquelQ_mem_s₁ hAFE hBDF)
      (E_mem_miquelS₁ hAFE) (F_mem_miquelS₁ hAFE) hQA hQF hAE.symm hFE.symm
  have hsAQF : (∡ A Q F).sign = (∡ B A C).sign :=
    (sign_oangle_AQF hF hAF hBF hQA.symm hQF.symm hQB.symm).trans hsAQB
  have hsAEF : (∡ A E F).sign = (∡ B A C).sign := by
    rw [EuclideanGeometry.oangle_rev F E A, Real.Angle.sign_neg,
      sign_oangle_FEA hF hE hAF hBF hCE hAE hFE hBA hCA, neg_neg]
  have hsAQF0 : (∡ A Q F).sign ≠ 0 := by rwa [hsAQF]
  have hrep2 : ∡ A Q F = ∡ A E F :=
    (Real.Angle.two_zsmul_eq_iff_eq hsAQF0 (by rw [hsAQF, hsAEF])).mp hP2
  have hadd : ∡ E Q A + ∡ A Q F = ∡ E Q F :=
    EuclideanGeometry.oangle_add hQE.symm hQA.symm hQF.symm
  have hval : ∡ E Q F = π - ∡ B A C := by
    rw [← hadd, hrep1, hrep2]
    exact val_EFA_AEF hE hF hAF hAE hFE hBA hCA hCE hBF
  rw [hval, hvalAQB]

/-- The second key angle equality: `∡FQD = ∡BQC`. -/
lemma oangle_FQD_eq_BQC {A B C D E F : ℂ}
    (hABC : ¬Collinear ℝ {A, B, C})
    (hD : Wbtw ℝ B D C) (hE : Wbtw ℝ C E A) (hF : Wbtw ℝ A F B)
    (hα₁o : ∡ A F E = ∡ B D F) (hα₂o : ∡ B D F = ∡ C E D)
    (hAFE : ¬Collinear ℝ {A, F, E}) (hBDF : ¬Collinear ℝ {B, D, F})
    (hCED : ¬Collinear ℝ {C, E, D}) (hDEF : ¬Collinear ℝ {D, E, F})
    (hQA : miquelQ hAFE hBDF ≠ A) (hQB : miquelQ hAFE hBDF ≠ B)
    (hQC : miquelQ hAFE hBDF ≠ C) (hQD : miquelQ hAFE hBDF ≠ D)
    (_hQE : miquelQ hAFE hBDF ≠ E) (hQF : miquelQ hAFE hBDF ≠ F) :
    ∡ F (miquelQ hAFE hBDF) D = ∡ B (miquelQ hAFE hBDF) C := by
  have hBD : B ≠ D := ne₁₂_of_not_collinear hBDF
  have hDF : D ≠ F := ne₂₃_of_not_collinear hBDF
  have hBF : B ≠ F := ne₁₃_of_not_collinear hBDF
  have hCD : C ≠ D := ne₁₃_of_not_collinear hCED
  have hBC : B ≠ C := ne₂₃_of_not_collinear hABC
  have hBA : B ≠ A := (ne₁₂_of_not_collinear hABC).symm
  have hCA : C ≠ A := (ne₁₃_of_not_collinear hABC).symm
  have hAF : A ≠ F := ne₁₂_of_not_collinear hAFE
  set Q := miquelQ hAFE hBDF with hQdef
  obtain ⟨hsAQB, -⟩ := sign_oangle_AQB hABC hD hE hF hα₁o hAFE hBDF hCED hDEF
    hQA hQB hQF hQD
  obtain ⟨hsBQC, hvalBQC⟩ := sign_oangle_BQC hABC hD hE hF hα₁o hα₂o hAFE hBDF hCED
    hDEF hQB hQC hQD hQF
  have hσ : (∡ B A C).sign ≠ 0 := by
    rw [sign_oangle_BAC hBA hCA]
    exact sign_ne_zero.mpr (cprod_ne_zero_of_not_collinear hABC)
  have hP1 : (2 : ℤ) • ∡ F Q B = (2 : ℤ) • ∡ F D B :=
    Sphere.two_zsmul_oangle_eq (F_mem_miquelS₂ hBDF) (miquelQ_mem_s₂ hAFE hBDF)
      (D_mem_miquelS₂ hBDF) (B_mem_miquelS₂ hBDF) hQF hQB hDF hBD.symm
  have hsFQB : (∡ F Q B).sign = (∡ B A C).sign :=
    (sign_oangle_FQB hF hAF hBF hQA.symm hQF.symm hQB.symm).trans hsAQB
  have hsFDB : (∡ F D B).sign = (∡ B A C).sign := by
    rw [EuclideanGeometry.oangle_rev B D F, Real.Angle.sign_neg,
      sign_oangle_BDF hD hF hBD hCD hAF hBF hDF hBA hCA, neg_neg]
  have hsFQB0 : (∡ F Q B).sign ≠ 0 := by rwa [hsFQB]
  have hrep1 : ∡ F Q B = ∡ F D B :=
    (Real.Angle.two_zsmul_eq_iff_eq hsFQB0 (by rw [hsFQB, hsFDB])).mp hP1
  have hP2 : (2 : ℤ) • ∡ B Q D = (2 : ℤ) • ∡ B F D :=
    Sphere.two_zsmul_oangle_eq (B_mem_miquelS₂ hBDF) (miquelQ_mem_s₂ hAFE hBDF)
      (F_mem_miquelS₂ hBDF) (D_mem_miquelS₂ hBDF) hQB hQD hBF.symm hDF.symm
  have hsBQD : (∡ B Q D).sign = (∡ B A C).sign :=
    (sign_oangle_BQD hD hBD hCD hQB.symm hQD.symm hQC.symm).trans hsBQC
  have hsBFD : (∡ B F D).sign = (∡ B A C).sign :=
    sign_oangle_BFD hD hF hBD hCD hAF hBF hDF hBA hCA
  have hsBQD0 : (∡ B Q D).sign ≠ 0 := by rwa [hsBQD]
  have hrep2 : ∡ B Q D = ∡ B F D :=
    (Real.Angle.two_zsmul_eq_iff_eq hsBQD0 (by rw [hsBQD, hsBFD])).mp hP2
  have hadd : ∡ F Q B + ∡ B Q D = ∡ F Q D :=
    EuclideanGeometry.oangle_add hQF.symm hQB.symm hQD.symm
  have hval : ∡ F Q D = π - ∡ C B A := by
    rw [← hadd, hrep1, hrep2]
    exact val_FDB_BFD hD hF hBD hDF hBF hBA hCD hBC hAF
  rw [hval, hvalBQC]

/-!
### C5: the spiral similarities at `Q` and the circumcenter relations
-/

/-- Collinear points have vanishing cross product. -/
lemma cprod_eq_zero_of_collinear {X Y Z : ℂ} (h : Collinear ℝ {X, Y, Z}) :
    cprod (Y - X) (Z - X) = 0 := by
  by_cases h1 : X = Y
  · subst h1; simp [cprod_eq]
  by_cases h2 : X = Z
  · subst h2; simp [cprod_eq]
  have h' : Collinear ℝ ({Y, X, Z} : Set ℂ) := by rwa [Set.insert_comm] at h
  have hs : (∡ Y X Z).sign = 0 :=
    EuclideanGeometry.oangle_sign_eq_zero_iff_collinear.mpr h'
  rw [oangle'_sign _ _ _ (Ne.symm h1) (Ne.symm h2)] at hs
  exact sign_eq_zero_iff.mp hs

/-- Two nonzero complex numbers with equal norm and equal (coerced) argument
are equal. -/
lemma eq_of_norm_eq_of_coe_arg_eq {z w : ℂ} (hn : ‖z‖ = ‖w‖)
    (ha : (Complex.arg z : Real.Angle) = Complex.arg w) :
    z = w := by
  have hc : Complex.cos (Complex.arg z) = Complex.cos (Complex.arg w) := by
    rw [← Complex.ofReal_cos, ← Complex.ofReal_cos, ← Real.Angle.cos_coe,
      ← Real.Angle.cos_coe, ha]
  have hs : Complex.sin (Complex.arg z) = Complex.sin (Complex.arg w) := by
    rw [← Complex.ofReal_sin, ← Complex.ofReal_sin, ← Real.Angle.sin_coe,
      ← Real.Angle.sin_coe, ha]
  rw [← Complex.norm_mul_exp_arg_mul_I z, ← Complex.norm_mul_exp_arg_mul_I w, hn]
  congr 1
  rw [← Complex.cos_add_sin_I, ← Complex.cos_add_sin_I, hc, hs]

/-- The oriented angle `oangle x y` is the coerced argument of `y / x`. -/
lemma oangle_eq_coe_arg_div (x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) :
    Complex.orientation.oangle x y = (Complex.arg (y / x) : Real.Angle) := by
  rw [oangle_eq_arg]
  have hcx : conj x ≠ 0 := by simpa using hx
  have h1 : y * conj x = (y / x) * (x * conj x) := by field_simp [hx]
  rw [h1, Complex.arg_mul_coe_angle (div_ne_zero hy hx) (mul_ne_zero hx hcx)]
  rw [Complex.mul_conj, Complex.arg_ofReal_of_nonneg (Complex.normSq_nonneg _),
    Real.Angle.coe_zero, add_zero]

/-- Scaling both leg vectors by a common nonzero complex factor preserves the
oriented angle. -/
lemma oangle_smul_complex (lam : ℂ) (hl : lam ≠ 0) (u v : ℂ) :
    Complex.orientation.oangle (lam * u) (lam * v) = Complex.orientation.oangle u v := by
  rw [oangle_eq_arg, oangle_eq_arg]
  have h1 : (lam * v) * conj (lam * u) = (lam * conj lam) * (v * conj u) := by
    rw [map_mul]; ring
  rw [h1, Complex.mul_conj, Complex.arg_real_mul _ (Complex.normSq_pos.mpr hl)]

/-- The spiral similarity `z ↦ lam * z + b` (with `lam ≠ 0`) preserves
oriented angles. -/
lemma oangle_smul_sub (lam b : ℂ) (hl : lam ≠ 0) (x y z : ℂ) :
    ∡ (lam * x + b) (lam * y + b) (lam * z + b) = ∡ x y z := by
  have e1 : ∡ (lam * x + b) (lam * y + b) (lam * z + b) =
      Complex.orientation.oangle ((lam * x + b) - (lam * y + b))
        ((lam * z + b) - (lam * y + b)) := by
    rw [oangle, vsub_eq_sub, vsub_eq_sub]; rfl
  have e2 : ∡ x y z = Complex.orientation.oangle (x - y) (z - y) := by
    rw [oangle, vsub_eq_sub, vsub_eq_sub]; rfl
  have hsub1 : (lam * x + b) - (lam * y + b) = lam * (x - y) := by ring
  have hsub2 : (lam * z + b) - (lam * y + b) = lam * (z - y) := by ring
  rw [e1, e2, hsub1, hsub2, oangle_smul_complex lam hl]

/-- The first spiral similarity: `F = Q + lam1 * (E - Q)` where
`lam1 = (B - Q) / (A - Q)`. -/
lemma spiral_R1 {A B D E F : ℂ}
    (hAFE : ¬Collinear ℝ {A, F, E}) (hBDF : ¬Collinear ℝ {B, D, F})
    (hQA : miquelQ hAFE hBDF ≠ A) (hQB : miquelQ hAFE hBDF ≠ B)
    (hQE : miquelQ hAFE hBDF ≠ E) (hQF : miquelQ hAFE hBDF ≠ F)
    (hdist : dist (miquelQ hAFE hBDF) E * dist (miquelQ hAFE hBDF) B =
      dist (miquelQ hAFE hBDF) F * dist (miquelQ hAFE hBDF) A)
    (hang : ∡ E (miquelQ hAFE hBDF) F = ∡ A (miquelQ hAFE hBDF) B) :
    F = miquelQ hAFE hBDF +
      ((B - miquelQ hAFE hBDF) / (A - miquelQ hAFE hBDF)) * (E - miquelQ hAFE hBDF) := by
  set Q := miquelQ hAFE hBDF with hQdef
  have hu : A - Q ≠ 0 := sub_ne_zero.mpr hQA.symm
  have hv : B - Q ≠ 0 := sub_ne_zero.mpr hQB.symm
  have hx : E - Q ≠ 0 := sub_ne_zero.mpr hQE.symm
  have hy : F - Q ≠ 0 := sub_ne_zero.mpr hQF.symm
  have e1 : ∡ E Q F = Complex.orientation.oangle (E - Q) (F - Q) := by
    rw [oangle, vsub_eq_sub, vsub_eq_sub]; rfl
  have e2 : ∡ A Q B = Complex.orientation.oangle (A - Q) (B - Q) := by
    rw [oangle, vsub_eq_sub, vsub_eq_sub]; rfl
  have harg : (Complex.arg ((F - Q) / (E - Q)) : Real.Angle) =
      (Complex.arg ((B - Q) / (A - Q)) : Real.Angle) := by
    rw [← oangle_eq_coe_arg_div _ _ hx hy, ← oangle_eq_coe_arg_div _ _ hu hv,
      ← e1, ← e2, hang]
  have hnorm : ‖(F - Q) / (E - Q)‖ = ‖(B - Q) / (A - Q)‖ := by
    rw [norm_div, norm_div]
    have h : ‖E - Q‖ * ‖B - Q‖ = ‖F - Q‖ * ‖A - Q‖ := by
      have h2 := hdist
      simp only [dist_eq_norm] at h2
      rwa [norm_sub_rev Q E, norm_sub_rev Q B, norm_sub_rev Q F, norm_sub_rev Q A] at h2
    rw [div_eq_div_iff (norm_pos_iff.mpr hx).ne' (norm_pos_iff.mpr hu).ne',
      mul_comm ‖B - Q‖ ‖E - Q‖]
    exact h.symm
  have hEq : (F - Q) / (E - Q) = (B - Q) / (A - Q) :=
    eq_of_norm_eq_of_coe_arg_eq hnorm harg
  have hy' : F - Q = (B - Q) / (A - Q) * (E - Q) := by
    have h2 := congrArg (· * (E - Q)) hEq
    rwa [div_mul_cancel₀ _ hx] at h2
  rw [← hy']
  exact (add_sub_cancel Q F).symm

/-- The second spiral similarity: `D = Q + lam2 * (F - Q)` where
`lam2 = (C - Q) / (B - Q)`. -/
lemma spiral_R2 {A B C D E F : ℂ}
    (hAFE : ¬Collinear ℝ {A, F, E}) (hBDF : ¬Collinear ℝ {B, D, F})
    (hQB : miquelQ hAFE hBDF ≠ B) (hQC : miquelQ hAFE hBDF ≠ C)
    (hQD : miquelQ hAFE hBDF ≠ D) (hQF : miquelQ hAFE hBDF ≠ F)
    (hdist : dist (miquelQ hAFE hBDF) C * dist (miquelQ hAFE hBDF) F =
      dist (miquelQ hAFE hBDF) D * dist (miquelQ hAFE hBDF) B)
    (hang : ∡ F (miquelQ hAFE hBDF) D = ∡ B (miquelQ hAFE hBDF) C) :
    D = miquelQ hAFE hBDF +
      ((C - miquelQ hAFE hBDF) / (B - miquelQ hAFE hBDF)) * (F - miquelQ hAFE hBDF) := by
  set Q := miquelQ hAFE hBDF with hQdef
  have hu : B - Q ≠ 0 := sub_ne_zero.mpr hQB.symm
  have hv : C - Q ≠ 0 := sub_ne_zero.mpr hQC.symm
  have hx : F - Q ≠ 0 := sub_ne_zero.mpr hQF.symm
  have hy : D - Q ≠ 0 := sub_ne_zero.mpr hQD.symm
  have e1 : ∡ F Q D = Complex.orientation.oangle (F - Q) (D - Q) := by
    rw [oangle, vsub_eq_sub, vsub_eq_sub]; rfl
  have e2 : ∡ B Q C = Complex.orientation.oangle (B - Q) (C - Q) := by
    rw [oangle, vsub_eq_sub, vsub_eq_sub]; rfl
  have harg : (Complex.arg ((D - Q) / (F - Q)) : Real.Angle) =
      (Complex.arg ((C - Q) / (B - Q)) : Real.Angle) := by
    rw [← oangle_eq_coe_arg_div _ _ hx hy, ← oangle_eq_coe_arg_div _ _ hu hv,
      ← e1, ← e2, hang]
  have hnorm : ‖(D - Q) / (F - Q)‖ = ‖(C - Q) / (B - Q)‖ := by
    rw [norm_div, norm_div]
    have h : ‖C - Q‖ * ‖F - Q‖ = ‖D - Q‖ * ‖B - Q‖ := by
      have h2 := hdist
      simp only [dist_eq_norm] at h2
      rwa [norm_sub_rev Q C, norm_sub_rev Q F, norm_sub_rev Q D, norm_sub_rev Q B] at h2
    rw [div_eq_div_iff (norm_pos_iff.mpr hx).ne' (norm_pos_iff.mpr hu).ne']
    exact h.symm
  have hEq : (D - Q) / (F - Q) = (C - Q) / (B - Q) :=
    eq_of_norm_eq_of_coe_arg_eq hnorm harg
  have hy' : D - Q = (C - Q) / (B - Q) * (F - Q) := by
    have h2 := congrArg (· * (F - Q)) hEq
    rwa [div_mul_cancel₀ _ hx] at h2
  rw [← hy']
  exact (add_sub_cancel Q D).symm

/-- The circumcenter of `BDF` is the image of the circumcenter of `AFE` under
the first spiral similarity. -/
lemma circumcenter_spiral1 {A B D E F : ℂ}
    (hAFE : ¬Collinear ℝ {A, F, E}) (hBDF : ¬Collinear ℝ {B, D, F})
    (hDEF : ¬Collinear ℝ {D, E, F})
    (hα₁o : ∡ A F E = ∡ B D F)
    (hQA : miquelQ hAFE hBDF ≠ A) (hQB : miquelQ hAFE hBDF ≠ B)
    (hQE : miquelQ hAFE hBDF ≠ E) (hQF : miquelQ hAFE hBDF ≠ F)
    (hR1 : F = miquelQ hAFE hBDF +
      ((B - miquelQ hAFE hBDF) / (A - miquelQ hAFE hBDF)) * (E - miquelQ hAFE hBDF)) :
    triCircumcenter hBDF = miquelQ hAFE hBDF +
      ((B - miquelQ hAFE hBDF) / (A - miquelQ hAFE hBDF)) *
        (triCircumcenter hAFE - miquelQ hAFE hBDF) := by
  set Q := miquelQ hAFE hBDF with hQdef
  set lam1 := (B - Q) / (A - Q) with hlam1def
  set b := Q - lam1 * Q with hbdef
  have hAF : A ≠ F := ne₁₂_of_not_collinear hAFE
  have hAE : A ≠ E := ne₁₃_of_not_collinear hAFE
  have hFE : F ≠ E := (ne₂₃_of_not_collinear hDEF).symm
  have hBF : B ≠ F := ne₁₃_of_not_collinear hBDF
  have hu : A - Q ≠ 0 := sub_ne_zero.mpr hQA.symm
  have hv : B - Q ≠ 0 := sub_ne_zero.mpr hQB.symm
  have hlam1 : lam1 ≠ 0 := div_ne_zero hv hu
  have hσ1A : lam1 * A + b = B := by
    have h1 : lam1 * A + (Q - lam1 * Q) = B := by
      rw [hlam1def]; field_simp [hu]; ring
    rw [hbdef]; exact h1
  have hσ1E : lam1 * E + b = F := by
    have h1 : lam1 * E + (Q - lam1 * Q) = Q + lam1 * (E - Q) := by ring
    rw [hbdef, h1, ← hR1]
  have hσ1Q : lam1 * Q + b = Q := by rw [hbdef]; ring
  set σ1F := lam1 * F + b with hσ1Fdef
  -- the three pairwise inequalities of `B, σ1F, F`
  have hσ1F_ne_B : σ1F ≠ B := by
    intro h
    have h2 : lam1 * F + b = lam1 * A + b := by rw [← hσ1Fdef, h, hσ1A]
    have hFA : F = A := mul_left_cancel₀ hlam1 (add_right_cancel_iff.mp h2)
    exact hAF hFA.symm
  have hσ1F_ne_F : σ1F ≠ F := by
    intro h
    have h2 : lam1 * F + b = lam1 * E + b := by rw [← hσ1Fdef, h, hσ1E]
    have hFE' : F = E := mul_left_cancel₀ hlam1 (add_right_cancel_iff.mp h2)
    exact hFE hFE'
  have hσ1F_ne_Q : σ1F ≠ Q := by
    intro h
    have h2 : lam1 * F + b = lam1 * Q + b := by rw [← hσ1Fdef, h, hσ1Q]
    have hFQ : F = Q := mul_left_cancel₀ hlam1 (add_right_cancel_iff.mp h2)
    exact hQF hFQ.symm
  -- `B, σ1F, F` are not collinear
  have hnc : ¬Collinear ℝ ({B, σ1F, F} : Set ℂ) := by
    intro hcol
    have hc0 : cprod (F - B) (σ1F - B) = 0 := by
      have h := cprod_eq_zero_of_collinear hcol
      rwa [cprod_skew, neg_eq_zero] at h
    obtain ⟨r, hr⟩ := exists_smul_of_cprod_eq_zero_right (sub_ne_zero.mpr hBF.symm) hc0
    have hσ1Feq : lam1 * F + b = B + r • (F - B) := by
      rw [← hσ1Fdef, ← hr]; ring
    have hstep1 : lam1 * (F - Q) = (1 - r) • (B - Q) + r • (F - Q) := by
      have h3 : lam1 * F + b - Q = B + r • (F - B) - Q := by rw [hσ1Feq]
      rw [hbdef] at h3
      have h4 : lam1 * F + (Q - lam1 * Q) - Q = lam1 * (F - Q) := by ring
      have h5 : B + r • (F - B) - Q = (B - Q) + r • (F - B) := by ring
      rw [h4, h5] at h3
      rw [h3]; module
    have hinv1 : lam1⁻¹ * (B - Q) = A - Q := by
      rw [hlam1def]; field_simp [hv]
    have hinv2 : lam1⁻¹ * (F - Q) = E - Q := by
      have h2 : F - Q = lam1 * (E - Q) := by rw [hR1]; ring
      rw [h2]; field_simp [hlam1]
    have hstep2 : F - Q = (1 - r) • (A - Q) + r • (E - Q) := by
      have h3 := congrArg (lam1⁻¹ * ·) hstep1
      have h4 : lam1⁻¹ * (lam1 * (F - Q)) = F - Q := by
        rw [← mul_assoc, inv_mul_cancel₀ hlam1, one_mul]
      have h5 : lam1⁻¹ * ((1 - r) • (B - Q) + r • (F - Q)) =
          (1 - r) • (A - Q) + r • (E - Q) := by
        rw [mul_add]
        have e1 : lam1⁻¹ * ((1 - r) • (B - Q)) = (1 - r) • (A - Q) := by
          rw [RCLike.real_smul_eq_coe_mul, mul_left_comm, hinv1,
            RCLike.real_smul_eq_coe_mul]
        have e2 : lam1⁻¹ * (r • (F - Q)) = r • (E - Q) := by
          rw [RCLike.real_smul_eq_coe_mul, mul_left_comm, hinv2,
            RCLike.real_smul_eq_coe_mul]
        rw [e1, e2]
      rw [h4, h5] at h3
      exact h3
    have hFAE : F = (1 - r) • A + r • E := by
      have h6 : (1 - r) • (A - Q) + r • (E - Q) = (1 - r) • A + r • E - Q := by
        module
      rw [h6] at hstep2
      rw [sub_eq_iff_eq_add] at hstep2
      rw [sub_add_cancel] at hstep2
      exact hstep2
    have hc : cprod (F - A) (E - A) ≠ 0 := cprod_ne_zero_of_not_collinear hAFE
    have hFsub : F - A = r • (E - A) := by rw [hFAE]; module
    rw [hFsub, cprod_smul_left, cprod_self, mul_zero] at hc
    exact hc rfl
  -- the angle chain putting `σ1F` on circle `BDF`
  have hadd1 : ∡ B σ1F Q + ∡ Q σ1F F = ∡ B σ1F F :=
    EuclideanGeometry.oangle_add hσ1F_ne_B.symm hσ1F_ne_Q.symm hσ1F_ne_F.symm
  have hang1 : ∡ B σ1F Q = ∡ A F Q := by
    have h := oangle_smul_sub lam1 b hlam1 A F Q
    rw [hσ1A, ← hσ1Fdef, hσ1Q] at h
    exact h
  have hang2 : ∡ Q σ1F F = ∡ Q F E := by
    have h := oangle_smul_sub lam1 b hlam1 Q F E
    rw [hσ1Q, ← hσ1Fdef, hσ1E] at h
    exact h
  have hadd2 : ∡ A F Q + ∡ Q F E = ∡ A F E :=
    EuclideanGeometry.oangle_add hAF hQF hFE.symm
  have h2ang : (2 : ℤ) • ∡ B σ1F F = (2 : ℤ) • ∡ B D F := by
    rw [← hadd1, hang1, hang2, hadd2, hα₁o]
  -- `σ1F` lies on circle `BDF`
  have hmemS : σ1F ∈ miquelS₂ hBDF := by
    have hsphere : miquelS₂ hBDF =
        (⟨![B, D, F], affineIndependent_iff_not_collinear_set.mpr hBDF⟩ :
          Affine.Triangle ℝ ℂ).circumsphere := rfl
    rw [hsphere]
    exact Affine.Triangle.mem_circumsphere_of_two_zsmul_oangle_eq
      (show (0 : Fin 3) ≠ 1 by decide) (show (0 : Fin 3) ≠ 2 by decide)
      (show (1 : Fin 3) ≠ 2 by decide)
      (show (2 : ℤ) • ∡ ((⟨![B, D, F], affineIndependent_iff_not_collinear_set.mpr hBDF⟩ :
          Affine.Triangle ℝ ℂ).points 0) σ1F
        ((⟨![B, D, F], affineIndependent_iff_not_collinear_set.mpr hBDF⟩ :
          Affine.Triangle ℝ ℂ).points 2) =
        (2 : ℤ) • ∡ ((⟨![B, D, F], affineIndependent_iff_not_collinear_set.mpr hBDF⟩ :
          Affine.Triangle ℝ ℂ).points 0)
        ((⟨![B, D, F], affineIndependent_iff_not_collinear_set.mpr hBDF⟩ :
          Affine.Triangle ℝ ℂ).points 1)
        ((⟨![B, D, F], affineIndependent_iff_not_collinear_set.mpr hBDF⟩ :
          Affine.Triangle ℝ ℂ).points 2) from h2ang)
  have hdist1 : dist σ1F (triCircumcenter hBDF) = dist B (triCircumcenter hBDF) := by
    have h2 := B_mem_miquelS₂ hBDF
    rw [EuclideanGeometry.mem_sphere, miquelS₂_center hBDF] at hmemS h2
    rw [hmemS, h2]
  have hdist2 : dist F (triCircumcenter hBDF) = dist B (triCircumcenter hBDF) := by
    have h1 := F_mem_miquelS₂ hBDF
    have h2 := B_mem_miquelS₂ hBDF
    rw [EuclideanGeometry.mem_sphere, miquelS₂_center hBDF] at h1 h2
    rw [h1, h2]
  -- the circumcenters coincide
  have hccS : triCircumcenter hBDF =
      (⟨![B, σ1F, F], affineIndependent_iff_not_collinear_set.mpr hnc⟩ :
        Affine.Simplex ℝ ℂ 2).circumcenter := by
    apply Affine.Simplex.eq_circumcenter_of_dist_eq (p := triCircumcenter hBDF)
      (r := dist (triCircumcenter hBDF) B)
    · rw [Affine.Simplex.span_eq_top _ Complex.finrank_real_complex]
      exact AffineSubspace.mem_top ℝ ℂ _
    · intro i
      fin_cases i <;> dsimp only
      · exact dist_comm _ _
      · exact hdist1.trans (dist_comm _ _)
      · exact hdist2.trans (dist_comm _ _)
  have hcc2 : cc B σ1F F =
      (⟨![B, σ1F, F], affineIndependent_iff_not_collinear_set.mpr hnc⟩ :
        Affine.Simplex ℝ ℂ 2).circumcenter := cc_eq_circumcenter _ _ _ hnc
  have hcc1 : lam1 * cc A F E + b = cc (lam1 * A + b) (lam1 * F + b) (lam1 * E + b) :=
    (cc_smul_add hlam1 (ccDenom_ne_zero_of_not_collinear _ _ _ hAFE)).symm
  rw [hσ1A, ← hσ1Fdef, hσ1E] at hcc1
  have hOA : triCircumcenter hAFE = cc A F E := (cc_eq_circumcenter _ _ _ hAFE).symm
  rw [hccS, ← hcc2, ← hcc1, hOA, hbdef]
  ring

/-- The circumcenter of `CED` is the image of the circumcenter of `BDF` under
the second spiral similarity. -/
lemma circumcenter_spiral2 {A B C D E F : ℂ}
    (hAFE : ¬Collinear ℝ {A, F, E}) (hBDF : ¬Collinear ℝ {B, D, F})
    (hCED : ¬Collinear ℝ {C, E, D})
    (hα₂o : ∡ B D F = ∡ C E D)
    (hQB : miquelQ hAFE hBDF ≠ B) (hQC : miquelQ hAFE hBDF ≠ C)
    (hQD : miquelQ hAFE hBDF ≠ D) (hQF : miquelQ hAFE hBDF ≠ F)
    (hR2 : D = miquelQ hAFE hBDF +
      ((C - miquelQ hAFE hBDF) / (B - miquelQ hAFE hBDF)) * (F - miquelQ hAFE hBDF)) :
    triCircumcenter hCED = miquelQ hAFE hBDF +
      ((C - miquelQ hAFE hBDF) / (B - miquelQ hAFE hBDF)) *
        (triCircumcenter hBDF - miquelQ hAFE hBDF) := by
  set Q := miquelQ hAFE hBDF with hQdef
  set lam2 := (C - Q) / (B - Q) with hlam2def
  set b := Q - lam2 * Q with hbdef
  have hBD : B ≠ D := ne₁₂_of_not_collinear hBDF
  have hDF : D ≠ F := ne₂₃_of_not_collinear hBDF
  have hCD : C ≠ D := ne₁₃_of_not_collinear hCED
  have hu : B - Q ≠ 0 := sub_ne_zero.mpr hQB.symm
  have hv : C - Q ≠ 0 := sub_ne_zero.mpr hQC.symm
  have hlam2 : lam2 ≠ 0 := div_ne_zero hv hu
  have hσ2B : lam2 * B + b = C := by
    have h1 : lam2 * B + (Q - lam2 * Q) = C := by
      rw [hlam2def]; field_simp [hu]; ring
    rw [hbdef]; exact h1
  have hσ2F : lam2 * F + b = D := by
    have h1 : lam2 * F + (Q - lam2 * Q) = Q + lam2 * (F - Q) := by ring
    rw [hbdef, h1, ← hR2]
  have hσ2Q : lam2 * Q + b = Q := by rw [hbdef]; ring
  set σ2D := lam2 * D + b with hσ2Ddef
  have hσ2D_ne_C : σ2D ≠ C := by
    intro h
    have h2 : lam2 * D + b = lam2 * B + b := by rw [← hσ2Ddef, h, hσ2B]
    have hDB : D = B := mul_left_cancel₀ hlam2 (add_right_cancel_iff.mp h2)
    exact hBD hDB.symm
  have hσ2D_ne_D : σ2D ≠ D := by
    intro h
    have h2 : lam2 * D + b = lam2 * F + b := by rw [← hσ2Ddef, h, hσ2F]
    have hDF' : D = F := mul_left_cancel₀ hlam2 (add_right_cancel_iff.mp h2)
    exact hDF hDF'
  have hσ2D_ne_Q : σ2D ≠ Q := by
    intro h
    have h2 : lam2 * D + b = lam2 * Q + b := by rw [← hσ2Ddef, h, hσ2Q]
    have hDQ : D = Q := mul_left_cancel₀ hlam2 (add_right_cancel_iff.mp h2)
    exact hQD hDQ.symm
  have hnc : ¬Collinear ℝ ({C, σ2D, D} : Set ℂ) := by
    intro hcol
    have hc0 : cprod (D - C) (σ2D - C) = 0 := by
      have h := cprod_eq_zero_of_collinear hcol
      rwa [cprod_skew, neg_eq_zero] at h
    obtain ⟨r, hr⟩ := exists_smul_of_cprod_eq_zero_right (sub_ne_zero.mpr hCD.symm) hc0
    have hσ2Deq : lam2 * D + b = C + r • (D - C) := by
      rw [← hσ2Ddef, ← hr]; ring
    have hstep1 : lam2 * (D - Q) = (1 - r) • (C - Q) + r • (D - Q) := by
      have h3 : lam2 * D + b - Q = C + r • (D - C) - Q := by rw [hσ2Deq]
      rw [hbdef] at h3
      have h4 : lam2 * D + (Q - lam2 * Q) - Q = lam2 * (D - Q) := by ring
      have h5 : C + r • (D - C) - Q = (C - Q) + r • (D - C) := by ring
      rw [h4, h5] at h3
      rw [h3]; module
    have hinv1 : lam2⁻¹ * (C - Q) = B - Q := by
      rw [hlam2def]; field_simp [hv]
    have hinv2 : lam2⁻¹ * (D - Q) = F - Q := by
      have h2 : D - Q = lam2 * (F - Q) := by rw [hR2]; ring
      rw [h2]; field_simp [hlam2]
    have hstep2 : D - Q = (1 - r) • (B - Q) + r • (F - Q) := by
      have h3 := congrArg (lam2⁻¹ * ·) hstep1
      have h4 : lam2⁻¹ * (lam2 * (D - Q)) = D - Q := by
        rw [← mul_assoc, inv_mul_cancel₀ hlam2, one_mul]
      have h5 : lam2⁻¹ * ((1 - r) • (C - Q) + r • (D - Q)) =
          (1 - r) • (B - Q) + r • (F - Q) := by
        rw [mul_add]
        have e1 : lam2⁻¹ * ((1 - r) • (C - Q)) = (1 - r) • (B - Q) := by
          rw [RCLike.real_smul_eq_coe_mul, mul_left_comm, hinv1,
            RCLike.real_smul_eq_coe_mul]
        have e2 : lam2⁻¹ * (r • (D - Q)) = r • (F - Q) := by
          rw [RCLike.real_smul_eq_coe_mul, mul_left_comm, hinv2,
            RCLike.real_smul_eq_coe_mul]
        rw [e1, e2]
      rw [h4, h5] at h3
      exact h3
    have hDBF : D = (1 - r) • B + r • F := by
      have h6 : (1 - r) • (B - Q) + r • (F - Q) = (1 - r) • B + r • F - Q := by
        module
      rw [h6] at hstep2
      rw [sub_eq_iff_eq_add] at hstep2
      rw [sub_add_cancel] at hstep2
      exact hstep2
    have hc : cprod (D - B) (F - B) ≠ 0 := cprod_ne_zero_of_not_collinear hBDF
    have hDsub : D - B = r • (F - B) := by rw [hDBF]; module
    rw [hDsub, cprod_smul_left, cprod_self, mul_zero] at hc
    exact hc rfl
  have hadd1 : ∡ C σ2D Q + ∡ Q σ2D D = ∡ C σ2D D :=
    EuclideanGeometry.oangle_add hσ2D_ne_C.symm hσ2D_ne_Q.symm hσ2D_ne_D.symm
  have hang1 : ∡ C σ2D Q = ∡ B D Q := by
    have h := oangle_smul_sub lam2 b hlam2 B D Q
    rw [hσ2B, ← hσ2Ddef, hσ2Q] at h
    exact h
  have hang2 : ∡ Q σ2D D = ∡ Q D F := by
    have h := oangle_smul_sub lam2 b hlam2 Q D F
    rw [hσ2Q, ← hσ2Ddef, hσ2F] at h
    exact h
  have hadd2 : ∡ B D Q + ∡ Q D F = ∡ B D F :=
    EuclideanGeometry.oangle_add hBD hQD hDF.symm
  have h2ang : (2 : ℤ) • ∡ C σ2D D = (2 : ℤ) • ∡ C E D := by
    rw [← hadd1, hang1, hang2, hadd2, hα₂o]
  have hmemS : σ2D ∈ miquelS₃ hCED := by
    have hsphere : miquelS₃ hCED =
        (⟨![C, E, D], affineIndependent_iff_not_collinear_set.mpr hCED⟩ :
          Affine.Triangle ℝ ℂ).circumsphere := rfl
    rw [hsphere]
    exact Affine.Triangle.mem_circumsphere_of_two_zsmul_oangle_eq
      (show (0 : Fin 3) ≠ 1 by decide) (show (0 : Fin 3) ≠ 2 by decide)
      (show (1 : Fin 3) ≠ 2 by decide)
      (show (2 : ℤ) • ∡ ((⟨![C, E, D], affineIndependent_iff_not_collinear_set.mpr hCED⟩ :
          Affine.Triangle ℝ ℂ).points 0) σ2D
        ((⟨![C, E, D], affineIndependent_iff_not_collinear_set.mpr hCED⟩ :
          Affine.Triangle ℝ ℂ).points 2) =
        (2 : ℤ) • ∡ ((⟨![C, E, D], affineIndependent_iff_not_collinear_set.mpr hCED⟩ :
          Affine.Triangle ℝ ℂ).points 0)
        ((⟨![C, E, D], affineIndependent_iff_not_collinear_set.mpr hCED⟩ :
          Affine.Triangle ℝ ℂ).points 1)
        ((⟨![C, E, D], affineIndependent_iff_not_collinear_set.mpr hCED⟩ :
          Affine.Triangle ℝ ℂ).points 2) from h2ang)
  have hdist1 : dist σ2D (triCircumcenter hCED) = dist C (triCircumcenter hCED) := by
    have h2 := C_mem_miquelS₃ hCED
    rw [EuclideanGeometry.mem_sphere, miquelS₃_center hCED] at hmemS h2
    rw [hmemS, h2]
  have hdist2 : dist D (triCircumcenter hCED) = dist C (triCircumcenter hCED) := by
    have h1 := D_mem_miquelS₃ hCED
    have h2 := C_mem_miquelS₃ hCED
    rw [EuclideanGeometry.mem_sphere, miquelS₃_center hCED] at h1 h2
    rw [h1, h2]
  have hccS : triCircumcenter hCED =
      (⟨![C, σ2D, D], affineIndependent_iff_not_collinear_set.mpr hnc⟩ :
        Affine.Simplex ℝ ℂ 2).circumcenter := by
    apply Affine.Simplex.eq_circumcenter_of_dist_eq (p := triCircumcenter hCED)
      (r := dist (triCircumcenter hCED) C)
    · rw [Affine.Simplex.span_eq_top _ Complex.finrank_real_complex]
      exact AffineSubspace.mem_top ℝ ℂ _
    · intro i
      fin_cases i <;> dsimp only
      · exact dist_comm _ _
      · exact hdist1.trans (dist_comm _ _)
      · exact hdist2.trans (dist_comm _ _)
  have hcc2 : cc C σ2D D =
      (⟨![C, σ2D, D], affineIndependent_iff_not_collinear_set.mpr hnc⟩ :
        Affine.Simplex ℝ ℂ 2).circumcenter := cc_eq_circumcenter _ _ _ hnc
  have hcc1 : lam2 * cc B D F + b = cc (lam2 * B + b) (lam2 * D + b) (lam2 * F + b) :=
    (cc_smul_add hlam2 (ccDenom_ne_zero_of_not_collinear _ _ _ hBDF)).symm
  rw [hσ2B, ← hσ2Ddef, hσ2F] at hcc1
  have hOB : triCircumcenter hBDF = cc B D F := (cc_eq_circumcenter _ _ _ hBDF).symm
  rw [hccS, ← hcc2, ← hcc1, hOB, hbdef]
  ring

/-- `dist (circumcenter AFE) A = dist (circumcenter AFE) E` (both equal the
circumradius). -/
lemma dist_triCircumcenter_left_eq_right {A F E : ℂ} (hAFE : ¬Collinear ℝ {A, F, E}) :
    dist (triCircumcenter hAFE) A = dist (triCircumcenter hAFE) E := by
  have h1 := Affine.Simplex.dist_circumcenter_eq_circumradius
    (⟨![A, F, E], affineIndependent_iff_not_collinear_set.mpr hAFE⟩ :
      Affine.Simplex ℝ ℂ 2) 0
  have h2 := Affine.Simplex.dist_circumcenter_eq_circumradius
    (⟨![A, F, E], affineIndependent_iff_not_collinear_set.mpr hAFE⟩ :
      Affine.Simplex ℝ ℂ 2) 2
  show dist (⟨![A, F, E], affineIndependent_iff_not_collinear_set.mpr hAFE⟩ :
      Affine.Simplex ℝ ℂ 2).circumcenter A =
    dist (⟨![A, F, E], affineIndependent_iff_not_collinear_set.mpr hAFE⟩ :
      Affine.Simplex ℝ ℂ 2).circumcenter E
  rw [dist_comm, dist_comm _ E]
  exact h1.trans h2.symm

/-- The geometric front-end output, bundled: the relations needed by the
algebraic endgame.  Here `Q` is the Miquel point (second intersection of the
circumcircles of `AFE` and `BDF`), and `lam1 lam2` are the ratios of the two
spiral similarities at `Q` sending `A ↦ B`, `E ↦ F` and `B ↦ C`, `F ↦ D`. -/
lemma frontend
    {A B C D E F : ℂ}
    (hABC : ¬Collinear ℝ {A, B, C})
    (hD : Wbtw ℝ B D C) (hE : Wbtw ℝ C E A) (hF : Wbtw ℝ A F B)
    (hα₁ : ∠ A F E = ∠ B D F) (hα₂ : ∠ B D F = ∠ C E D)
    (hAFE : ¬Collinear ℝ {A, F, E}) (hBDF : ¬Collinear ℝ {B, D, F})
    (hCED : ¬Collinear ℝ {C, E, D}) (hDEF : ¬Collinear ℝ {D, E, F}) :
    ∃ Q lam1 lam2 : ℂ,
      lam1 = (B - Q) / (A - Q) ∧ lam2 = (C - Q) / (B - Q) ∧
      A ≠ Q ∧ B ≠ Q ∧ C ≠ Q ∧ E ≠ Q ∧ triCircumcenter hAFE ≠ Q ∧
      dist (triCircumcenter hAFE) A = dist (triCircumcenter hAFE) E ∧
      F = Q + lam1 * (E - Q) ∧ D = Q + lam2 * (F - Q) ∧
      triCircumcenter hBDF = Q + lam1 * (triCircumcenter hAFE - Q) ∧
      triCircumcenter hCED = Q + lam2 * (triCircumcenter hBDF - Q) := by
  have hα₁o' : ∡ A F E = ∡ B D F := hα₁o hABC hD hE hF hα₁ hAFE hBDF hCED hDEF
  have hα₂o' : ∡ B D F = ∡ C E D := hα₂o hABC hD hE hF hα₂ hAFE hBDF hCED hDEF
  have hQA : miquelQ hAFE hBDF ≠ A := miquelQ_ne_A hAFE hBDF hF
  have hQB : miquelQ hAFE hBDF ≠ B := miquelQ_ne_B hAFE hBDF hF
  have hQC : miquelQ hAFE hBDF ≠ C := miquelQ_ne_C hABC hAFE hCED hBDF hE
  have hQD : miquelQ hAFE hBDF ≠ D :=
    miquelQ_ne_D hABC hD hE hF hα₁o' hα₂o' hAFE hBDF hCED hDEF
  have hQE : miquelQ hAFE hBDF ≠ E :=
    miquelQ_ne_E hABC hD hE hF hα₁o' hα₂o' hAFE hBDF hCED hDEF
  have hQF : miquelQ hAFE hBDF ≠ F := miquelQ_ne_F hABC hD hE hF hα₁o' hAFE hBDF hCED hDEF
  have hβ1 := beta_QEA_QFA hAFE hBDF hDEF hQE hQF
  have hβ2 := beta_QFA_QFB hAFE hBDF hF hQF
  have hβ3 := beta_QFB_QDB hAFE hBDF hQF hQD hF
  have hβ6 := beta_QEC_QEA hAFE hBDF hCED hE hQE
  have hang1 := oangle_EQF_eq_AQB hABC hD hE hF hα₁o' hα₂o' hAFE hBDF hCED hDEF
    hQA hQB hQC hQD hQE hQF
  have hang2 := oangle_FQD_eq_BQC hABC hD hE hF hα₁o' hα₂o' hAFE hBDF hCED hDEF
    hQA hQB hQC hQD hQE hQF
  have hd1 := dist_QE_mul_dist_QB hAFE hBDF hDEF hα₁o' hQA hQE hQF hQD hQB hβ1 hβ2 hβ3
  have hd2 := dist_QC_mul_dist_QF hABC hD hE hF hα₁o' hα₂o' hAFE hBDF hCED hDEF
    hQC hQE hQD hQF hQB hβ1 hβ2 hβ3 hβ6
  have hR1 := spiral_R1 hAFE hBDF hQA hQB hQE hQF hd1 hang1
  have hR2 := spiral_R2 hAFE hBDF hQB hQC hQD hQF hd2 hang2
  have hR3a := circumcenter_spiral1 hAFE hBDF hDEF hα₁o' hQA hQB hQE hQF hR1
  have hR3b := circumcenter_spiral2 hAFE hBDF hCED hα₂o' hQB hQC hQD hQF hR2
  exact ⟨miquelQ hAFE hBDF, _, _, rfl, rfl, hQA.symm, hQB.symm, hQC.symm, hQE.symm,
    miquelQ_ne_circumcenter hABC hD hE hF hAFE hBDF,
    dist_triCircumcenter_left_eq_right hAFE, hR1, hR2, hR3a, hR3b⟩

end GeometricFrontend
end SnipScope

snip end

problem usa2026_p5
    {A B C D E F : ℂ}
    (hABC : ¬Collinear ℝ {A, B, C})
    (hD : Wbtw ℝ B D C) (hE : Wbtw ℝ C E A) (hF : Wbtw ℝ A F B)
    (hα₁ : ∠ A F E = ∠ B D F) (hα₂ : ∠ B D F = ∠ C E D)
    (hAFE : ¬Collinear ℝ {A, F, E}) (hBDF : ¬Collinear ℝ {B, D, F})
    (hCED : ¬Collinear ℝ {C, E, D}) (hDEF : ¬Collinear ℝ {D, E, F})
    (hO : ¬Collinear ℝ {triCircumcenter hAFE, triCircumcenter hBDF,
                        triCircumcenter hCED}) :
    dist (triCircumcenter hO) (triCircumcenter hABC) =
      dist (triCircumcenter hO) (triCircumcenter hDEF) := by
  haveI : Fact (Module.finrank ℝ ℂ = 2) := Complex.finrank_real_complex_fact
  haveI : Module.Oriented ℝ ℂ (Fin 2) := instComplexOriented
  obtain ⟨Q, lam1, lam2, hlam1, hlam2, hAQ, hBQ', hCQ', hEQ, hOAQ, hR, hR1, hR2,
    hR3a, hR3b⟩ := frontend hABC hD hE hF hα₁ hα₂ hAFE hBDF hCED hDEF
  -- rewrite the three circumcenters via the complex formula
  have hccA : triCircumcenter hABC = cc A B C := (cc_eq_circumcenter _ _ _ hABC).symm
  have hccD : triCircumcenter hDEF = cc D E F := (cc_eq_circumcenter _ _ _ hDEF).symm
  have hccO : triCircumcenter hO =
      cc (triCircumcenter hAFE) (triCircumcenter hBDF) (triCircumcenter hCED) :=
    (cc_eq_circumcenter _ _ _ hO).symm
  -- algebraic relations
  have hBQ : B - Q ≠ 0 := sub_ne_zero.mpr hBQ'
  have hlam1A : Q + lam1 * (A - Q) = B := by
    rw [hlam1]; field_simp [sub_ne_zero.mpr hAQ]; ring
  have hlam2A : Q + lam2 * (B - Q) = C := by
    rw [hlam2]; field_simp [hBQ]; ring
  have hlam21A : Q + lam2 * lam1 * (A - Q) = C := by
    have h1 : lam1 * (A - Q) = B - Q := by rw [hlam1]; field_simp [sub_ne_zero.mpr hAQ]
    rw [mul_assoc, h1]; exact hlam2A
  have hD' : D = Q + lam2 * lam1 * (E - Q) := by
    have h1 : lam1 * (E - Q) = F - Q := by rw [hR1]; ring
    rw [hR2, mul_assoc, h1]
  -- the denominator
  have hdABC : ccDenom A B C ≠ 0 := ccDenom_ne_zero_of_not_collinear _ _ _ hABC
  have hd : ccDenom 1 lam1 (lam2 * lam1) ≠ 0 := by
    have h1 : A = (A - Q) * 1 + Q := by ring
    have h2 : B = (A - Q) * lam1 + Q := by
      rw [hlam1]; field_simp [sub_ne_zero.mpr hAQ]; ring
    have h3 : C = (A - Q) * (lam2 * lam1) + Q := by
      rw [hlam1, hlam2]; field_simp [sub_ne_zero.mpr hAQ, hBQ]; ring
    have hde := ccDenom_smul_add (A - Q) Q 1 lam1 (lam2 * lam1)
    rw [← h1, ← h2, ← h3] at hde
    rw [hde] at hdABC
    exact (mul_ne_zero_iff.mp hdABC).2
  -- compute M, N, O as complex circumcenters
  have hM : cc A B C = cc A (Q + lam1 * (A - Q)) (Q + lam2 * lam1 * (A - Q)) := by
    rw [hlam1A, hlam21A]
  have hN : cc D E F = cc E (Q + lam1 * (E - Q)) (Q + lam2 * lam1 * (E - Q)) := by
    have hpd : ccDenom D E F ≠ 0 := ccDenom_ne_zero_of_not_collinear _ _ _ hDEF
    rw [cc_perm_cycle D E F hpd, hR1, hD']
  have hO' : cc (triCircumcenter hAFE) (triCircumcenter hBDF) (triCircumcenter hCED)
      = cc (triCircumcenter hAFE) (Q + lam1 * (triCircumcenter hAFE - Q))
          (Q + lam2 * lam1 * (triCircumcenter hAFE - Q)) := by
    rw [hR3b, hR3a, add_sub_cancel_left, ← mul_assoc]
  rw [hccA, hccD, hccO, hM, hN, hO']
  exact endgame hAQ hEQ hOAQ hd hR

end Usa2026P5
