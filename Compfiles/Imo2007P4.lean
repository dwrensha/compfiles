/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Geometry.Euclidean.Sphere.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 2007, Problem 4

In triangle ABC the bisector of ∠BCA meets the circumcircle again at R, the
perpendicular bisector of BC at P, and the perpendicular bisector of AC at Q.
The midpoint of BC is K and the midpoint of AC is L. Prove that the triangles
RPK and RQL have the same area.
-/

namespace Imo2007P4

open scoped Real EuclideanGeometry

/-- The Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- The unsigned area of the triangle `XYZ`, via the determinant formula. -/
noncomputable def triangleArea (X Y Z : Pt) : ℝ :=
  |(Y 0 - X 0) * (Z 1 - X 1) - (Y 1 - X 1) * (Z 0 - X 0)| / 2

/-- The data determining the configuration of the problem up to a rigid motion:
`a = |BC|`, `b = |CA|` and `γ = ∠BCA / 2`. -/
structure Cfg where
  a : ℝ
  b : ℝ
  γ : ℝ
  ha : 0 < a
  hb : 0 < b
  hγ : γ ∈ Set.Ioo 0 (Real.pi / 2)

namespace Cfg

variable (cfg : Cfg)

/-! We place `C` at the origin and the internal bisector of `∠BCA` along the
positive `x`-axis, so that `A = (b cos γ, b sin γ)` and `B = (a cos γ, -a sin γ)`.
The points `R`, `P`, `Q`, `K`, `L` of the problem are then *defined* by explicit
coordinates; the lemmas in the `snip` section below verify that these points
enjoy the geometric properties stated in the problem (for instance, `R` lies on
the circumcircle of `ABC` and `P` lies on the perpendicular bisector of `BC`). -/

/-- The vertex `C`, placed at the origin. -/
noncomputable def C : Pt := !₂[0, 0]

/-- The vertex `A`, with `|CA| = b`, at angle `γ` above the bisector. -/
noncomputable def A : Pt := !₂[cfg.b * Real.cos cfg.γ, cfg.b * Real.sin cfg.γ]

/-- The vertex `B`, with `|CB| = a`, at angle `γ` below the bisector. -/
noncomputable def B : Pt := !₂[cfg.a * Real.cos cfg.γ, -(cfg.a * Real.sin cfg.γ)]

/-- The second meeting of the bisector of `∠BCA` with the circumcircle. -/
noncomputable def R : Pt := !₂[(cfg.a + cfg.b) / (2 * Real.cos cfg.γ), 0]

/-- The meeting of the bisector of `∠BCA` with the perpendicular bisector of `BC`. -/
noncomputable def P : Pt := !₂[cfg.a / (2 * Real.cos cfg.γ), 0]

/-- The meeting of the bisector of `∠BCA` with the perpendicular bisector of `AC`. -/
noncomputable def Q : Pt := !₂[cfg.b / (2 * Real.cos cfg.γ), 0]

/-- The midpoint of `BC`. -/
noncomputable def K : Pt := !₂[cfg.a * Real.cos cfg.γ / 2, -(cfg.a * Real.sin cfg.γ) / 2]

/-- The midpoint of `AC`. -/
noncomputable def L : Pt := !₂[cfg.b * Real.cos cfg.γ / 2, cfg.b * Real.sin cfg.γ / 2]

end Cfg

snip begin

namespace Cfg

variable (cfg : Cfg)

/-! ### Sign facts -/

lemma cos_pos : 0 < Real.cos cfg.γ := by
  refine Real.cos_pos_of_mem_Ioo ⟨?_, cfg.hγ.2⟩
  linarith [cfg.hγ.1, Real.pi_pos]

lemma sin_pos : 0 < Real.sin cfg.γ :=
  Real.sin_pos_of_pos_of_lt_pi cfg.hγ.1 (by linarith [cfg.hγ.2, Real.pi_pos])

lemma cos_ne_zero : Real.cos cfg.γ ≠ 0 := cfg.cos_pos.ne'

lemma sin_ne_zero : Real.sin cfg.γ ≠ 0 := cfg.sin_pos.ne'

lemma a_ne_zero : cfg.a ≠ 0 := cfg.ha.ne'

lemma b_ne_zero : cfg.b ≠ 0 := cfg.hb.ne'

lemma ab_pos : 0 < cfg.a + cfg.b := add_pos cfg.ha cfg.hb

/-! ### Coordinate computation helpers -/

lemma pt_eq (x₁ y₁ x₂ y₂ : ℝ) : (!₂[x₁, y₁] : Pt) = !₂[x₂, y₂] ↔ x₁ = x₂ ∧ y₁ = y₂ := by
  simp

@[simp]
lemma pt_apply_zero (x y : ℝ) : (!₂[x, y] : Pt) 0 = x := by simp

@[simp]
lemma pt_apply_one (x y : ℝ) : (!₂[x, y] : Pt) 1 = y := by simp

/-! ### The area computation -/

/-- The (signed) determinant for the triangle `RPK`. -/
lemma det_RPK :
    (cfg.P 0 - cfg.R 0) * (cfg.K 1 - cfg.R 1) - (cfg.P 1 - cfg.R 1) * (cfg.K 0 - cfg.R 0) =
    cfg.a * cfg.b * Real.sin cfg.γ / (4 * Real.cos cfg.γ) := by
  have hc := cfg.cos_ne_zero
  simp only [Cfg.R, Cfg.P, Cfg.K, pt_apply_zero, pt_apply_one]
  field_simp
  ring

/-- The (signed) determinant for the triangle `RQL`. -/
lemma det_RQL :
    (cfg.Q 0 - cfg.R 0) * (cfg.L 1 - cfg.R 1) - (cfg.Q 1 - cfg.R 1) * (cfg.L 0 - cfg.R 0) =
    -(cfg.a * cfg.b * Real.sin cfg.γ / (4 * Real.cos cfg.γ)) := by
  have hc := cfg.cos_ne_zero
  simp only [Cfg.R, Cfg.Q, Cfg.L, pt_apply_zero, pt_apply_one]
  field_simp
  ring

/-- The area of `RPK`: it equals `(ab/8) tan γ`. -/
lemma area_RPK : triangleArea cfg.R cfg.P cfg.K =
    cfg.a * cfg.b * Real.sin cfg.γ / (8 * Real.cos cfg.γ) := by
  have hc := cfg.cos_pos; have hs := cfg.sin_pos; have ha := cfg.ha; have hb := cfg.hb
  simp only [triangleArea]
  rw [cfg.det_RPK, abs_of_nonneg (by positivity)]
  ring

/-- The area of `RQL`: it equals `(ab/8) tan γ`. -/
lemma area_RQL : triangleArea cfg.R cfg.Q cfg.L =
    cfg.a * cfg.b * Real.sin cfg.γ / (8 * Real.cos cfg.γ) := by
  have hc := cfg.cos_pos; have hs := cfg.sin_pos; have ha := cfg.ha; have hb := cfg.hb
  simp only [triangleArea]
  rw [cfg.det_RQL, abs_neg, abs_of_nonneg (by positivity)]
  ring

/-- The two areas coincide. -/
theorem areas_equal : triangleArea cfg.R cfg.P cfg.K = triangleArea cfg.R cfg.Q cfg.L := by
  rw [cfg.area_RPK, cfg.area_RQL]

/-! ### Geometric characterizations of the defined points -/

lemma pt_add (x₁ y₁ x₂ y₂ : ℝ) : (!₂[x₁, y₁] : Pt) + !₂[x₂, y₂] = !₂[x₁ + x₂, y₁ + y₂] := by
  ext i; fin_cases i <;> simp

lemma pt_smul (t x y : ℝ) : t • (!₂[x, y] : Pt) = !₂[t * x, t * y] := by
  ext i; fin_cases i <;> simp

lemma pt_vsub (x₁ y₁ x₂ y₂ : ℝ) : (!₂[x₁, y₁] : Pt) -ᵥ !₂[x₂, y₂] = !₂[x₁ - x₂, y₁ - y₂] := by
  ext i; fin_cases i <;> simp [vsub_eq_sub]

lemma pt_vadd (x₁ y₁ x₂ y₂ : ℝ) : (!₂[x₁, y₁] : Pt) +ᵥ !₂[x₂, y₂] = !₂[x₁ + x₂, y₁ + y₂] := by
  ext i; fin_cases i <;> simp [vadd_eq_add]

lemma dist_pt (x₁ y₁ x₂ y₂ : ℝ) :
    dist (!₂[x₁, y₁] : Pt) (!₂[x₂, y₂]) = Real.sqrt ((x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp [Real.dist_eq, sq_abs]

/-- `K` is indeed the midpoint of `BC`. -/
lemma K_eq_midpoint : cfg.K = midpoint ℝ cfg.B Cfg.C := by
  have h2 : (⅟2 : ℝ) = 1 / 2 := by rw [invOf_eq_inv]; norm_num
  simp only [Cfg.K, Cfg.B, Cfg.C, midpoint_eq_smul_add, h2, pt_smul, pt_add, pt_eq]
  constructor <;> ring

/-- `L` is indeed the midpoint of `AC`. -/
lemma L_eq_midpoint : cfg.L = midpoint ℝ cfg.A Cfg.C := by
  have h2 : (⅟2 : ℝ) = 1 / 2 := by rw [invOf_eq_inv]; norm_num
  simp only [Cfg.L, Cfg.A, Cfg.C, midpoint_eq_smul_add, h2, pt_smul, pt_add, pt_eq]
  constructor <;> ring

/-- `P` lies on the perpendicular bisector of `BC`. -/
lemma dist_PB_eq_dist_PC : dist cfg.P cfg.B = dist cfg.P Cfg.C := by
  have hc := cfg.cos_ne_zero
  simp only [Cfg.P, Cfg.B, Cfg.C, dist_pt]
  rw [Real.sqrt_inj (by positivity) (by positivity), sub_zero, sub_zero, zero_sub, neg_neg,
    zero_pow two_ne_zero, add_zero]
  have h2 : 2 * (cfg.a / (2 * Real.cos cfg.γ)) * (cfg.a * Real.cos cfg.γ) = cfg.a ^ 2 := by
    field_simp
  have e : (cfg.a / (2 * Real.cos cfg.γ) - cfg.a * Real.cos cfg.γ) ^ 2 =
      (cfg.a / (2 * Real.cos cfg.γ)) ^ 2 - 2 * (cfg.a / (2 * Real.cos cfg.γ)) *
        (cfg.a * Real.cos cfg.γ) + (cfg.a * Real.cos cfg.γ) ^ 2 := by ring
  have e3 : (cfg.a * Real.cos cfg.γ) ^ 2 + (cfg.a * Real.sin cfg.γ) ^ 2 = cfg.a ^ 2 := by
    rw [mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one]
  rw [e, h2]
  linarith [e3]

/-- `Q` lies on the perpendicular bisector of `AC`. -/
lemma dist_QA_eq_dist_QC : dist cfg.Q cfg.A = dist cfg.Q Cfg.C := by
  have hc := cfg.cos_ne_zero
  simp only [Cfg.Q, Cfg.A, Cfg.C, dist_pt]
  rw [Real.sqrt_inj (by positivity) (by positivity), sub_zero, sub_zero, zero_sub,
    zero_pow two_ne_zero, add_zero]
  have h2 : 2 * (cfg.b / (2 * Real.cos cfg.γ)) * (cfg.b * Real.cos cfg.γ) = cfg.b ^ 2 := by
    field_simp
  have e : (cfg.b / (2 * Real.cos cfg.γ) - cfg.b * Real.cos cfg.γ) ^ 2 =
      (cfg.b / (2 * Real.cos cfg.γ)) ^ 2 - 2 * (cfg.b / (2 * Real.cos cfg.γ)) *
        (cfg.b * Real.cos cfg.γ) + (cfg.b * Real.cos cfg.γ) ^ 2 := by ring
  have e3 : (cfg.b * Real.cos cfg.γ) ^ 2 + (cfg.b * Real.sin cfg.γ) ^ 2 = cfg.b ^ 2 := by
    rw [mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one]
  rw [e, h2]
  linarith [e3]

/-- `R` differs from `C` (the bisector meets the circumcircle *again* at `R`). -/
lemma R_ne_C : cfg.R ≠ Cfg.C := by
  have hc := cfg.cos_pos; have hab := cfg.ab_pos
  intro h
  simp only [Cfg.R, Cfg.C, pt_eq] at h
  have hne : (cfg.a + cfg.b) / (2 * Real.cos cfg.γ) ≠ 0 := by positivity
  exact hne h.1

/-! ### The circumcircle -/

/-- The four points `A`, `B`, `C`, `R` are cospherical: `R` lies on the
circumcircle of `ABC`. The circle has equation `x² + y² + Dx + Ey = 0` with
`D = -(a+b)/(2 cos γ)` and `E = (a-b)/(2 sin γ)`; we exhibit its center. -/
lemma cospherical_ABCR : EuclideanGeometry.Cospherical {cfg.A, cfg.B, Cfg.C, cfg.R} := by
  have hc := cfg.cos_ne_zero; have hs := cfg.sin_ne_zero
  refine ⟨!₂[(cfg.a + cfg.b) / (4 * Real.cos cfg.γ), (cfg.b - cfg.a) / (4 * Real.sin cfg.γ)],
    dist Cfg.C !₂[(cfg.a + cfg.b) / (4 * Real.cos cfg.γ),
      (cfg.b - cfg.a) / (4 * Real.sin cfg.γ)], fun p hp => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · -- the vertex `A`
    simp only [Cfg.A, Cfg.C, dist_pt]
    rw [Real.sqrt_inj (by positivity) (by positivity)]
    have e1 : (cfg.b * Real.cos cfg.γ - (cfg.a + cfg.b) / (4 * Real.cos cfg.γ)) ^ 2 =
        (cfg.b * Real.cos cfg.γ) ^ 2 -
          2 * (cfg.b * Real.cos cfg.γ) * ((cfg.a + cfg.b) / (4 * Real.cos cfg.γ)) +
        ((cfg.a + cfg.b) / (4 * Real.cos cfg.γ)) ^ 2 := by ring
    have e2 : (cfg.b * Real.sin cfg.γ - (cfg.b - cfg.a) / (4 * Real.sin cfg.γ)) ^ 2 =
        (cfg.b * Real.sin cfg.γ) ^ 2 -
          2 * (cfg.b * Real.sin cfg.γ) * ((cfg.b - cfg.a) / (4 * Real.sin cfg.γ)) +
        ((cfg.b - cfg.a) / (4 * Real.sin cfg.γ)) ^ 2 := by ring
    rw [e1, e2, zero_sub, zero_sub, neg_sq, neg_sq]
    have e3 : (cfg.b * Real.cos cfg.γ) ^ 2 + (cfg.b * Real.sin cfg.γ) ^ 2 = cfg.b ^ 2 := by
      rw [mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one]
    have e4 : 2 * (cfg.b * Real.cos cfg.γ) * ((cfg.a + cfg.b) / (4 * Real.cos cfg.γ)) +
        2 * (cfg.b * Real.sin cfg.γ) * ((cfg.b - cfg.a) / (4 * Real.sin cfg.γ)) =
        cfg.b ^ 2 := by field_simp; ring
    linarith [e3, e4]
  · -- the vertex `B`
    simp only [Cfg.B, Cfg.C, dist_pt]
    rw [Real.sqrt_inj (by positivity) (by positivity)]
    have e1 : (cfg.a * Real.cos cfg.γ - (cfg.a + cfg.b) / (4 * Real.cos cfg.γ)) ^ 2 =
        (cfg.a * Real.cos cfg.γ) ^ 2 -
          2 * (cfg.a * Real.cos cfg.γ) * ((cfg.a + cfg.b) / (4 * Real.cos cfg.γ)) +
        ((cfg.a + cfg.b) / (4 * Real.cos cfg.γ)) ^ 2 := by ring
    have e2 : (-(cfg.a * Real.sin cfg.γ) - (cfg.b - cfg.a) / (4 * Real.sin cfg.γ)) ^ 2 =
        (cfg.a * Real.sin cfg.γ) ^ 2 +
          2 * (cfg.a * Real.sin cfg.γ) * ((cfg.b - cfg.a) / (4 * Real.sin cfg.γ)) +
        ((cfg.b - cfg.a) / (4 * Real.sin cfg.γ)) ^ 2 := by ring
    rw [e1, e2, zero_sub, zero_sub, neg_sq, neg_sq]
    have e3 : (cfg.a * Real.cos cfg.γ) ^ 2 + (cfg.a * Real.sin cfg.γ) ^ 2 = cfg.a ^ 2 := by
      rw [mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one]
    have e4 : 2 * (cfg.a * Real.cos cfg.γ) * ((cfg.a + cfg.b) / (4 * Real.cos cfg.γ)) -
        2 * (cfg.a * Real.sin cfg.γ) * ((cfg.b - cfg.a) / (4 * Real.sin cfg.γ)) =
        cfg.a ^ 2 := by field_simp; ring
    linarith [e3, e4]
  · -- the vertex `C` itself
    rfl
  · -- the point `R`
    simp only [Cfg.R, Cfg.C, dist_pt]
    rw [Real.sqrt_inj (by positivity) (by positivity)]
    have e1 : ((cfg.a + cfg.b) / (2 * Real.cos cfg.γ) - (cfg.a + cfg.b) / (4 * Real.cos cfg.γ)) ^ 2 =
        ((cfg.a + cfg.b) / (2 * Real.cos cfg.γ)) ^ 2 -
          2 * ((cfg.a + cfg.b) / (2 * Real.cos cfg.γ)) * ((cfg.a + cfg.b) / (4 * Real.cos cfg.γ)) +
        ((cfg.a + cfg.b) / (4 * Real.cos cfg.γ)) ^ 2 := by ring
    rw [e1, zero_sub, zero_sub, neg_sq, neg_sq]
    have e4 : ((cfg.a + cfg.b) / (2 * Real.cos cfg.γ)) ^ 2 =
        2 * ((cfg.a + cfg.b) / (2 * Real.cos cfg.γ)) * ((cfg.a + cfg.b) / (4 * Real.cos cfg.γ)) := by
      field_simp; ring
    linarith [e4]

local instance : Fact (Module.finrank ℝ Pt = 2) := ⟨finrank_euclideanSpace_fin⟩

/-- The four points `A`, `B`, `C`, `R` are concyclic. -/
lemma concyclic_ABCR : EuclideanGeometry.Concyclic {cfg.A, cfg.B, Cfg.C, cfg.R} :=
  ⟨cfg.cospherical_ABCR, coplanar_of_fact_finrank_eq_two _⟩

/-! ### `P`, `Q`, `R` lie on the bisector line -/

/-- `P` lies on the line `CR` (the bisector of `∠BCA`). -/
lemma collinear_CPR : Collinear ℝ {Cfg.C, cfg.P, cfg.R} := by
  have hc := cfg.cos_ne_zero; have hab := cfg.ab_pos.ne'
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨Cfg.C, cfg.R -ᵥ Cfg.C, fun p hp => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · refine ⟨cfg.a / (cfg.a + cfg.b), ?_⟩
    simp only [Cfg.P, Cfg.R, Cfg.C, pt_vsub, pt_smul, pt_vadd, pt_eq]
    constructor <;> field_simp <;> ring
  · exact ⟨1, by simp⟩

/-- `Q` lies on the line `CR` (the bisector of `∠BCA`). -/
lemma collinear_CQR : Collinear ℝ {Cfg.C, cfg.Q, cfg.R} := by
  have hc := cfg.cos_ne_zero; have hab := cfg.ab_pos.ne'
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨Cfg.C, cfg.R -ᵥ Cfg.C, fun p hp => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · refine ⟨cfg.b / (cfg.a + cfg.b), ?_⟩
    simp only [Cfg.Q, Cfg.R, Cfg.C, pt_vsub, pt_smul, pt_vadd, pt_eq]
    constructor <;> field_simp <;> ring
  · exact ⟨1, by simp⟩

/-! ### `CR` bisects `∠BCA` -/

lemma norm_pt (x y : ℝ) : ‖(!₂[x, y] : Pt)‖ = Real.sqrt (x ^ 2 + y ^ 2) := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp [Real.norm_eq_abs, sq_abs]

lemma inner_pt (x₁ y₁ x₂ y₂ : ℝ) :
    @inner ℝ Pt _ (!₂[x₁, y₁] : Pt) (!₂[x₂, y₂]) = x₁ * x₂ + y₁ * y₂ := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp only [RCLike.inner_apply, RCLike.conj_to_real, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

lemma norm_A_vsub_C : ‖cfg.A -ᵥ Cfg.C‖ = cfg.b := by
  have hb := cfg.hb
  simp only [Cfg.A, Cfg.C, pt_vsub, norm_pt]
  rw [sub_zero, sub_zero]
  have e : (cfg.b * Real.cos cfg.γ) ^ 2 + (cfg.b * Real.sin cfg.γ) ^ 2 = cfg.b ^ 2 := by
    rw [mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one]
  rw [e, Real.sqrt_sq hb.le]

lemma norm_B_vsub_C : ‖cfg.B -ᵥ Cfg.C‖ = cfg.a := by
  have ha := cfg.ha
  simp only [Cfg.B, Cfg.C, pt_vsub, norm_pt]
  rw [sub_zero, sub_zero]
  have e : (cfg.a * Real.cos cfg.γ) ^ 2 + (-(cfg.a * Real.sin cfg.γ)) ^ 2 = cfg.a ^ 2 := by
    rw [neg_sq, mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one]
  rw [e, Real.sqrt_sq ha.le]

lemma norm_R_vsub_C : ‖cfg.R -ᵥ Cfg.C‖ = (cfg.a + cfg.b) / (2 * Real.cos cfg.γ) := by
  have hc := cfg.cos_pos; have hab := cfg.ab_pos
  simp only [Cfg.R, Cfg.C, pt_vsub, norm_pt]
  rw [sub_zero, sub_zero, zero_pow two_ne_zero, add_zero, Real.sqrt_sq (by positivity)]

lemma inner_BR : @inner ℝ Pt _ (cfg.B -ᵥ Cfg.C) (cfg.R -ᵥ Cfg.C) =
    cfg.a * Real.cos cfg.γ * ((cfg.a + cfg.b) / (2 * Real.cos cfg.γ)) := by
  simp only [Cfg.B, Cfg.R, Cfg.C, pt_vsub, inner_pt]
  ring

lemma inner_RA : @inner ℝ Pt _ (cfg.R -ᵥ Cfg.C) (cfg.A -ᵥ Cfg.C) =
    cfg.b * Real.cos cfg.γ * ((cfg.a + cfg.b) / (2 * Real.cos cfg.γ)) := by
  simp only [Cfg.R, Cfg.A, Cfg.C, pt_vsub, inner_pt]
  ring

lemma cos_angle_BCR : Real.cos (∠ cfg.B Cfg.C cfg.R) = Real.cos cfg.γ := by
  have hc := cfg.cos_ne_zero; have ha := cfg.a_ne_zero; have hab := cfg.ab_pos.ne'
  rw [show ∠ cfg.B Cfg.C cfg.R =
      InnerProductGeometry.angle (cfg.B -ᵥ Cfg.C) (cfg.R -ᵥ Cfg.C) from rfl,
    InnerProductGeometry.cos_angle, cfg.inner_BR, cfg.norm_B_vsub_C, cfg.norm_R_vsub_C]
  field_simp

lemma cos_angle_RCA : Real.cos (∠ cfg.R Cfg.C cfg.A) = Real.cos cfg.γ := by
  have hc := cfg.cos_ne_zero; have hb := cfg.b_ne_zero; have hab := cfg.ab_pos.ne'
  rw [show ∠ cfg.R Cfg.C cfg.A =
      InnerProductGeometry.angle (cfg.R -ᵥ Cfg.C) (cfg.A -ᵥ Cfg.C) from rfl,
    InnerProductGeometry.cos_angle, cfg.inner_RA, cfg.norm_R_vsub_C, cfg.norm_A_vsub_C]
  field_simp

/-- The line `CR` indeed bisects `∠BCA`. -/
lemma angle_BCR_eq_angle_RCA : ∠ cfg.B Cfg.C cfg.R = ∠ cfg.R Cfg.C cfg.A := by
  apply Real.injOn_cos
    ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
    ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
  rw [cfg.cos_angle_BCR, cfg.cos_angle_RCA]

end Cfg

snip end

problem imo2007_p4 (cfg : Cfg) :
    triangleArea cfg.R cfg.P cfg.K = triangleArea cfg.R cfg.Q cfg.L := by
  exact cfg.areas_equal

end Imo2007P4
