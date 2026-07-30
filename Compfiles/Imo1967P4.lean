/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Real.Sign
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1967, Problem 4

Let $A_0B_0C_0$ and $A_1B_1C_1$ be acute-angled triangles. Construct the
triangle $ABC$ with the largest possible area which is circumscribed about
$A_0B_0C_0$ ($BC$ contains $A_0$, $CA$ contains $B_0$, and $AB$ contains
$C_0$) and similar to $A_1B_1C_1$.
-/

namespace Imo1967P4

open scoped EuclideanGeometry

/-- The Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- Dot product on the plane, in coordinates. -/
def vdot (u v : Pt) : ℝ := u 0 * v 0 + u 1 * v 1

/-- Scalar cross product (determinant) on the plane, in coordinates. -/
def vcr (u v : Pt) : ℝ := u 0 * v 1 - u 1 * v 0

/-- Rotation by a right angle (counterclockwise), in coordinates. -/
def vrot (u : Pt) : Pt := WithLp.toLp 2 (![ - u 1, u 0 ] : Fin 2 → ℝ)

/-- The area of a triangle, via the determinant formula. -/
noncomputable def area (A B C : Pt) : ℝ := |vcr (B - A) (C - A)| / 2

/-- Similarity of two triangles, with the correspondence `A ↔ A₁`, `B ↔ B₁`,
`C ↔ C₁` (all pairs of corresponding sides have a common ratio). -/
def Similar (A B C A₁ B₁ C₁ : Pt) : Prop :=
  ∃ r : ℝ, 0 < r ∧ dist A B = r * dist A₁ B₁ ∧ dist B C = r * dist B₁ C₁ ∧
    dist C A = r * dist C₁ A₁

/-- Triangle `ABC` is circumscribed about `A₀B₀C₀`: the points `A₀`, `B₀`, `C₀`
lie strictly on the sides `BC`, `CA`, `AB` respectively. -/
def Circumscribed (A₀ B₀ C₀ A B C : Pt) : Prop :=
  Sbtw ℝ B A₀ C ∧ Sbtw ℝ C B₀ A ∧ Sbtw ℝ A C₀ B

/-- The largest possible area: the answer to the problem. Written
`K / (2 * |cr₁|)` where `K` is the sum of the six products of the vertex dot
products of the two triangles plus `2 * |cr₀| * |cr₁|`. -/
noncomputable determine maxArea (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) : ℝ :=
  (vdot (B₀ - A₀) (C₀ - A₀) * vdot (A₁ - B₁) (C₁ - B₁) +
   vdot (B₀ - A₀) (C₀ - A₀) * vdot (A₁ - C₁) (B₁ - C₁) +
   vdot (A₀ - B₀) (C₀ - B₀) * vdot (B₁ - A₁) (C₁ - A₁) +
   vdot (A₀ - B₀) (C₀ - B₀) * vdot (A₁ - C₁) (B₁ - C₁) +
   vdot (A₀ - C₀) (B₀ - C₀) * vdot (B₁ - A₁) (C₁ - A₁) +
   vdot (A₀ - C₀) (B₀ - C₀) * vdot (A₁ - B₁) (C₁ - B₁) +
   2 * |vcr (B₀ - A₀) (C₀ - A₀)| * |vcr (B₁ - A₁) (C₁ - A₁)|) /
    (2 * |vcr (B₁ - A₁) (C₁ - A₁)|)

snip begin

lemma vrot_zero (u : Pt) : vrot u 0 = - u 1 := by simp [vrot]

lemma vrot_one (u : Pt) : vrot u 1 = u 0 := by simp [vrot]

lemma inner_eq_vdot (u v : Pt) : @inner ℝ _ _ u v = vdot u v := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp [vdot, RCLike.inner_apply, mul_comm]

lemma norm_sq_eq_vdot (u : Pt) : ‖u‖^2 = vdot u u := by
  rw [pow_two, ← real_inner_self_eq_norm_mul_norm, inner_eq_vdot]

lemma dist_sq (A B : Pt) : (dist A B)^2 = vdot (A - B) (A - B) := by
  rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  simp [vdot]
  ring

/-- The two-dimensional Lagrange identity. -/
lemma lagrange (u v : Pt) : vdot u u * vdot v v = (vdot u v)^2 + (vcr u v)^2 := by
  simp [vdot, vcr]
  ring

lemma sign_mul_self_eq_abs (r : ℝ) : Real.sign r * r = |r| := by
  rcases lt_trichotomy r 0 with h | h | h
  · rw [Real.sign_of_neg h, abs_of_neg h]
    ring
  · rw [h, Real.sign_zero, abs_zero]
    ring
  · rw [Real.sign_of_pos h, abs_of_pos h]
    ring

lemma sign_mul_abs_eq_self (r : ℝ) : Real.sign r * |r| = r := by
  rcases lt_trichotomy r 0 with h | h | h
  · rw [Real.sign_of_neg h, abs_of_neg h]
    ring
  · rw [h, Real.sign_zero, abs_zero]
    ring
  · rw [Real.sign_of_pos h, abs_of_pos h]
    ring

/-- If an angle is acute and non-degenerate, its vertex rays are distinct. -/
lemma ne_left_of_angle_mem {X Y Z : Pt} (h : ∠ X Y Z ∈ Set.Ioo 0 (Real.pi / 2)) :
    X ≠ Y := by
  intro he
  subst he
  rw [EuclideanGeometry.angle, vsub_self, InnerProductGeometry.angle_zero_left] at h
  simp at h

lemma ne_right_of_angle_mem {X Y Z : Pt} (h : ∠ X Y Z ∈ Set.Ioo 0 (Real.pi / 2)) :
    Z ≠ Y := by
  intro he
  subst he
  rw [EuclideanGeometry.angle, vsub_self, InnerProductGeometry.angle_zero_right] at h
  simp at h

lemma cos_pos_of_angle_mem {X Y Z : Pt} (h : ∠ X Y Z ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.cos (∠ X Y Z) := by
  have hmem : ∠ X Y Z ∈ Set.Icc 0 Real.pi :=
    ⟨InnerProductGeometry.angle_nonneg _ _, InnerProductGeometry.angle_le_pi _ _⟩
  have hz : Real.pi / 2 ∈ Set.Icc 0 Real.pi := by
    constructor <;> linarith [Real.pi_pos]
  have hlt : ∠ X Y Z < Real.pi / 2 := h.2
  have := Real.strictAntiOn_cos hmem hz hlt
  rwa [Real.cos_pi_div_two] at this

lemma cos_lt_one_of_angle_mem {X Y Z : Pt} (h : ∠ X Y Z ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.cos (∠ X Y Z) < 1 := by
  have hmem : ∠ X Y Z ∈ Set.Icc 0 Real.pi :=
    ⟨InnerProductGeometry.angle_nonneg _ _, InnerProductGeometry.angle_le_pi _ _⟩
  have hz : (0 : ℝ) ∈ Set.Icc 0 Real.pi := Set.left_mem_Icc.mpr Real.pi_pos.le
  have := Real.strictAntiOn_cos hz hmem h.1
  rwa [Real.cos_zero] at this

/-- An acute angle has positive dot product. -/
lemma acute_dot {X Y Z : Pt} (h : ∠ X Y Z ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < vdot (X - Y) (Z - Y) := by
  have h1 : X ≠ Y := ne_left_of_angle_mem h
  have h2 : Z ≠ Y := ne_right_of_angle_mem h
  have hcos := cos_pos_of_angle_mem h
  rw [EuclideanGeometry.angle, vsub_eq_sub, vsub_eq_sub, InnerProductGeometry.cos_angle,
    inner_eq_vdot] at hcos
  have hn : 0 < ‖X - Y‖ * ‖Z - Y‖ :=
    mul_pos (norm_pos_iff.mpr (sub_ne_zero.mpr h1)) (norm_pos_iff.mpr (sub_ne_zero.mpr h2))
  exact (div_pos_iff_of_pos_right hn).mp hcos

/-- A non-degenerate acute angle has nonzero cross product. -/
lemma acute_vcr_ne {X Y Z : Pt} (h : ∠ X Y Z ∈ Set.Ioo 0 (Real.pi / 2)) :
    vcr (X - Y) (Z - Y) ≠ 0 := by
  have h1 : X ≠ Y := ne_left_of_angle_mem h
  have h2 : Z ≠ Y := ne_right_of_angle_mem h
  have hdot : 0 < vdot (X - Y) (Z - Y) := acute_dot h
  have hcos := cos_lt_one_of_angle_mem h
  rw [EuclideanGeometry.angle, vsub_eq_sub, vsub_eq_sub, InnerProductGeometry.cos_angle,
    inner_eq_vdot] at hcos
  have hn : 0 < ‖X - Y‖ * ‖Z - Y‖ :=
    mul_pos (norm_pos_iff.mpr (sub_ne_zero.mpr h1)) (norm_pos_iff.mpr (sub_ne_zero.mpr h2))
  rw [div_lt_one hn] at hcos
  have hsq : (vdot (X - Y) (Z - Y))^2 < (‖X - Y‖ * ‖Z - Y‖)^2 := by
    nlinarith [hcos, hdot]
  rw [mul_pow, norm_sq_eq_vdot, norm_sq_eq_vdot, lagrange] at hsq
  have hne : (vcr (X - Y) (Z - Y))^2 ≠ 0 := by linarith
  exact fun hz => hne (by simp [hz])

/-- The "median" vector identity used to compare dot products of similar
triangles. -/
lemma vdot_mid (A B C : Pt) :
    2 * vdot (B - A) (C - A) =
      vdot (B - A) (B - A) + vdot (C - A) (C - A) - vdot (C - B) (C - B) := by
  simp only [vdot, PiLp.sub_apply]
  ring

/-- The cross products of two SSS-similar triangles are related by the square
of the ratio. -/
lemma similar_abs_vcr {A B C A₁ B₁ C₁ : Pt} (h : Similar A B C A₁ B₁ C₁) :
    |vcr (B - A) (C - A)| * (dist A₁ B₁)^2 = |vcr (B₁ - A₁) (C₁ - A₁)| * (dist A B)^2 := by
  obtain ⟨r, hr, hAB, hBC, hCA⟩ := h
  have e2 : vdot (B - A) (B - A) = r^2 * vdot (B₁ - A₁) (B₁ - A₁) := by
    have h := dist_sq B A
    have h1 := dist_sq B₁ A₁
    rw [dist_comm B A, hAB] at h
    rw [dist_comm B₁ A₁] at h1
    linear_combination r^2 * h1 - h
  have e3 : vdot (C - A) (C - A) = r^2 * vdot (C₁ - A₁) (C₁ - A₁) := by
    have h := dist_sq C A
    have h1 := dist_sq C₁ A₁
    rw [hCA] at h
    linear_combination r^2 * h1 - h
  have e5 : vdot (C - B) (C - B) = r^2 * vdot (C₁ - B₁) (C₁ - B₁) := by
    have h := dist_sq C B
    have h1 := dist_sq C₁ B₁
    rw [dist_comm C B, hBC] at h
    rw [dist_comm C₁ B₁] at h1
    linear_combination r^2 * h1 - h
  have e4 : vdot (B - A) (C - A) = r^2 * vdot (B₁ - A₁) (C₁ - A₁) := by
    have emid := vdot_mid A B C
    have emid1 := vdot_mid A₁ B₁ C₁
    linear_combination emid / 2 - r^2 * emid1 / 2 + e2 / 2 + e3 / 2 - e5 / 2
  have e1 : (vcr (B - A) (C - A))^2 =
      vdot (B - A) (B - A) * vdot (C - A) (C - A) - (vdot (B - A) (C - A))^2 := by
    have := lagrange (B - A) (C - A)
    linarith
  have hsq : (vcr (B - A) (C - A))^2 = (r^2)^2 * (vcr (B₁ - A₁) (C₁ - A₁))^2 := by
    rw [e1, e2, e3, e4]
    have lag1 := lagrange (B₁ - A₁) (C₁ - A₁)
    linear_combination (r^2)^2 * lag1
  have habs : |vcr (B - A) (C - A)| = r^2 * |vcr (B₁ - A₁) (C₁ - A₁)| := by
    have h1 : |vcr (B - A) (C - A)|^2 = (r^2 * |vcr (B₁ - A₁) (C₁ - A₁)|)^2 := by
      rw [sq_abs, hsq, mul_pow, sq_abs]
    exact (pow_left_inj₀ (abs_nonneg _) (by positivity) (by norm_num)).mp h1
  rw [habs, hAB]
  ring

/-- If `ABC` is circumscribed about `A₀B₀C₀` (with parameters `la`, `mu`),
then `A` sees the directed segment `B₀C₀` on the opposite side from the
interior: an algebraic identity. -/
lemma circum_vcr_left {A B C B₀ C₀ : Pt} {la mu : ℝ}
    (eB0 : B₀ = (1 - mu) • C + mu • A) (eC0 : C₀ = (1 - la) • A + la • B) :
    vcr (C₀ - B₀) (A - B₀) = -la * (1 - mu) * vcr (B - A) (C - A) := by
  rw [eB0, eC0]
  simp only [vcr, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- The signed area of `A₀B₀C₀` computed from the side `B₀C₀` towards `A₀`
equals a positive multiple of the signed area of `ABC`. -/
lemma circum_vcr_mid {A B C A₀ B₀ C₀ : Pt} {la mu t : ℝ}
    (eA0 : A₀ = (1 - t) • B + t • C) (eB0 : B₀ = (1 - mu) • C + mu • A)
    (eC0 : C₀ = (1 - la) • A + la • B) :
    vcr (C₀ - B₀) (A₀ - B₀) =
      ((1 - la) * (1 - mu) * (1 - t) + la * mu * t) * vcr (B - A) (C - A) := by
  rw [eA0, eB0, eC0]
  simp only [vcr, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- All ways to compute twice the signed area of a triangle agree. -/
lemma vcr_area_id (A₀ B₀ C₀ : Pt) :
    vcr (C₀ - B₀) (A₀ - B₀) = vcr (B₀ - A₀) (C₀ - A₀) := by
  simp only [vcr, PiLp.sub_apply]
  ring

lemma vdot_comm (u v : Pt) : vdot u v = vdot v u := by
  simp [vdot]
  ring

lemma vdot_zero_left (v : Pt) : vdot 0 v = 0 := by simp [vdot]

lemma vdot_zero_right (u : Pt) : vdot u 0 = 0 := by simp [vdot]

lemma vdot_self_pos {u : Pt} (hu : u ≠ 0) : 0 < vdot u u := by
  rw [← norm_sq_eq_vdot]
  exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hu)

/-- If `X, Y` are on a common circle centered at `O`, the chord relation. -/
lemma vdot_chord {X Y O : Pt} (h : vdot (X - O) (X - O) = vdot (Y - O) (Y - O)) :
    vdot (X - Y) (X - Y) + 2 * vdot (X - Y) (Y - O) = 0 := by
  have h1 : vdot (X - Y + (Y - O)) (X - Y + (Y - O)) =
      vdot (X - Y) (X - Y) + 2 * vdot (X - Y) (Y - O) + vdot (Y - O) (Y - O) := by
    simp only [vdot, PiLp.add_apply, PiLp.sub_apply]
    ring
  rw [← sub_add_sub_cancel X Y O, h1] at h
  linarith

/-- A sign of a positive multiple is the sign of the base. -/
lemma sign_of_mul_pos {a b : ℝ} (ha : 0 < a) : Real.sign (a * b) = Real.sign b := by
  rcases lt_trichotomy b 0 with hb | hb | hb
  · rw [Real.sign_of_neg hb, Real.sign_of_neg (mul_neg_of_pos_of_neg ha hb)]
  · rw [hb, mul_zero, Real.sign_zero]
  · rw [Real.sign_of_pos hb, Real.sign_of_pos (mul_pos ha hb)]

/-- The variant of `circum_vcr_left` at vertex `B`. -/
lemma circum_vcr_left2 {A B C A₀ C₀ : Pt} {la t : ℝ}
    (eA0 : A₀ = (1 - t) • B + t • C) (eC0 : C₀ = (1 - la) • A + la • B) :
    vcr (A₀ - C₀) (B - C₀) = -t * (1 - la) * vcr (B - A) (C - A) := by
  rw [eA0, eC0]
  simp only [vcr, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- The vertex dot products of two SSS-similar triangles are related by the
square of the ratio. -/
lemma similar_vdots {A B C A₁ B₁ C₁ : Pt} (h : Similar A B C A₁ B₁ C₁) :
    ∃ r : ℝ, 0 < r ∧ dist A B = r * dist A₁ B₁ ∧
      vdot (B - A) (C - A) = r^2 * vdot (B₁ - A₁) (C₁ - A₁) ∧
      vdot (A - B) (C - B) = r^2 * vdot (A₁ - B₁) (C₁ - B₁) ∧
      vdot (A - C) (B - C) = r^2 * vdot (A₁ - C₁) (B₁ - C₁) := by
  obtain ⟨r, hr, hAB, hBC, hCA⟩ := h
  have e2 : vdot (B - A) (B - A) = r^2 * vdot (B₁ - A₁) (B₁ - A₁) := by
    have h := dist_sq B A
    have h1 := dist_sq B₁ A₁
    rw [dist_comm B A, hAB] at h
    rw [dist_comm B₁ A₁] at h1
    linear_combination r^2 * h1 - h
  have e3 : vdot (C - A) (C - A) = r^2 * vdot (C₁ - A₁) (C₁ - A₁) := by
    have h := dist_sq C A
    have h1 := dist_sq C₁ A₁
    rw [hCA] at h
    linear_combination r^2 * h1 - h
  have e5 : vdot (C - B) (C - B) = r^2 * vdot (C₁ - B₁) (C₁ - B₁) := by
    have h := dist_sq C B
    have h1 := dist_sq C₁ B₁
    rw [dist_comm C B, hBC] at h
    rw [dist_comm C₁ B₁] at h1
    linear_combination r^2 * h1 - h
  have e4 : vdot (B - A) (C - A) = r^2 * vdot (B₁ - A₁) (C₁ - A₁) := by
    have emid := vdot_mid A B C
    have emid1 := vdot_mid A₁ B₁ C₁
    linear_combination emid / 2 - r^2 * emid1 / 2 + e2 / 2 + e3 / 2 - e5 / 2
  have e6 : vdot (A - B) (C - B) = r^2 * vdot (A₁ - B₁) (C₁ - B₁) := by
    have emid : 2 * vdot (A - B) (C - B) =
        vdot (A - B) (A - B) + vdot (C - B) (C - B) - vdot (C - A) (C - A) := by
      simp only [vdot, PiLp.sub_apply]
      ring
    have emid1 : 2 * vdot (A₁ - B₁) (C₁ - B₁) =
        vdot (A₁ - B₁) (A₁ - B₁) + vdot (C₁ - B₁) (C₁ - B₁) - vdot (C₁ - A₁) (C₁ - A₁) := by
      simp only [vdot, PiLp.sub_apply]
      ring
    have e2' : vdot (A - B) (A - B) = r^2 * vdot (A₁ - B₁) (A₁ - B₁) := by
      have h := dist_sq A B
      have h1 := dist_sq A₁ B₁
      rw [hAB] at h
      linear_combination r^2 * h1 - h
    linear_combination emid / 2 - r^2 * emid1 / 2 + e2' / 2 + e5 / 2 - e3 / 2
  have e7 : vdot (A - C) (B - C) = r^2 * vdot (A₁ - C₁) (B₁ - C₁) := by
    have emid : 2 * vdot (A - C) (B - C) =
        vdot (A - C) (A - C) + vdot (B - C) (B - C) - vdot (B - A) (B - A) := by
      simp only [vdot, PiLp.sub_apply]
      ring
    have emid1 : 2 * vdot (A₁ - C₁) (B₁ - C₁) =
        vdot (A₁ - C₁) (A₁ - C₁) + vdot (B₁ - C₁) (B₁ - C₁) - vdot (B₁ - A₁) (B₁ - A₁) := by
      simp only [vdot, PiLp.sub_apply]
      ring
    have e3' : vdot (A - C) (A - C) = r^2 * vdot (A₁ - C₁) (A₁ - C₁) := by
      have h := dist_sq A C
      have h1 := dist_sq A₁ C₁
      rw [dist_comm A C, hCA] at h
      rw [dist_comm A₁ C₁] at h1
      linear_combination r^2 * h1 - h
    have e5' : vdot (B - C) (B - C) = r^2 * vdot (B₁ - C₁) (B₁ - C₁) := by
      have h := dist_sq B C
      have h1 := dist_sq B₁ C₁
      rw [hBC] at h
      linear_combination r^2 * h1 - h
    have e2' : vdot (B - A) (B - A) = r^2 * vdot (B₁ - A₁) (B₁ - A₁) := e2
    linear_combination emid / 2 - r^2 * emid1 / 2 + e3' / 2 + e5' / 2 - e2' / 2
  exact ⟨r, hr, hAB, e4, e6, e7⟩

noncomputable def octr (P Q : Pt) (s : ℝ) : Pt := (2 : ℝ)⁻¹ • (P + Q) + s • vrot (Q - P)

noncomputable def offp (sig q cr : ℝ) : ℝ := -(sig * q) / (2 * cr)


lemma octr_zero (P Q : Pt) (s : ℝ) :
    (octr P Q s) 0 = (2:ℝ)⁻¹ * (P 0 + Q 0) - s * (Q 1 - P 1) := by
  simp only [octr, vrot_zero, vrot_one, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
    smul_eq_mul, PiLp.neg_apply]
  ring

lemma octr_one (P Q : Pt) (s : ℝ) :
    (octr P Q s) 1 = (2:ℝ)⁻¹ * (P 1 + Q 1) + s * (Q 0 - P 0) := by
  simp only [octr, vrot_zero, vrot_one, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
    smul_eq_mul, PiLp.neg_apply]

lemma vdotE (u v : Pt) : vdot u v = u 0 * v 0 + u 1 * v 1 := rfl

lemma vcrE (u v : Pt) : vcr u v = u 0 * v 1 - u 1 * v 0 := rfl

lemma pt_sub_zero (u v : Pt) : (u - v) 0 = u 0 - v 0 := rfl

lemma pt_sub_one (u v : Pt) : (u - v) 1 = u 1 - v 1 := rfl

lemma pt_add_zero (u v : Pt) : (u + v) 0 = u 0 + v 0 := rfl

lemma pt_add_one (u v : Pt) : (u + v) 1 = u 1 + v 1 := rfl

lemma pt_smul_zero (s : ℝ) (u : Pt) : (s • u) 0 = s * u 0 := rfl

lemma pt_smul_one (s : ℝ) (u : Pt) : (s • u) 1 = s * u 1 := rfl

noncomputable def cenA (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) : Pt :=
  octr B₀ C₀ (offp sig (vdot (B₁ - A₁) (C₁ - A₁)) (vcr (B₁ - A₁) (C₁ - A₁)))
noncomputable def cenB (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) : Pt :=
  octr C₀ A₀ (offp sig (vdot (A₁ - B₁) (C₁ - B₁)) (vcr (B₁ - A₁) (C₁ - A₁)))
noncomputable def cenC (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) : Pt :=
  octr A₀ B₀ (offp sig (vdot (A₁ - C₁) (B₁ - C₁)) (vcr (B₁ - A₁) (C₁ - A₁)))
noncomputable def dab2 (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) : ℝ :=
  vdot (cenB A₀ B₀ C₀ A₁ B₁ C₁ sig - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig)
    (cenB A₀ B₀ C₀ A₁ B₁ C₁ sig - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig)
noncomputable def dbc2 (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) : ℝ :=
  vdot (cenC A₀ B₀ C₀ A₁ B₁ C₁ sig - cenB A₀ B₀ C₀ A₁ B₁ C₁ sig)
    (cenC A₀ B₀ C₀ A₁ B₁ C₁ sig - cenB A₀ B₀ C₀ A₁ B₁ C₁ sig)
noncomputable def dca2 (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) : ℝ :=
  vdot (cenA A₀ B₀ C₀ A₁ B₁ C₁ sig - cenC A₀ B₀ C₀ A₁ B₁ C₁ sig)
    (cenA A₀ B₀ C₀ A₁ B₁ C₁ sig - cenC A₀ B₀ C₀ A₁ B₁ C₁ sig)
noncomputable def rasq (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) : ℝ :=
  vdot (B₀ - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) (B₀ - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig)
noncomputable def rbsq (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) : ℝ :=
  vdot (C₀ - cenB A₀ B₀ C₀ A₁ B₁ C₁ sig) (C₀ - cenB A₀ B₀ C₀ A₁ B₁ C₁ sig)
noncomputable def rcsq (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) : ℝ :=
  vdot (A₀ - cenC A₀ B₀ C₀ A₁ B₁ C₁ sig) (A₀ - cenC A₀ B₀ C₀ A₁ B₁ C₁ sig)
noncomputable def kval (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) : ℝ :=
  vdot (B₀ - A₀) (C₀ - A₀) * vdot (A₁ - B₁) (C₁ - B₁) +
  vdot (B₀ - A₀) (C₀ - A₀) * vdot (A₁ - C₁) (B₁ - C₁) +
  vdot (A₀ - B₀) (C₀ - B₀) * vdot (B₁ - A₁) (C₁ - A₁) +
  vdot (A₀ - B₀) (C₀ - B₀) * vdot (A₁ - C₁) (B₁ - C₁) +
  vdot (A₀ - C₀) (B₀ - C₀) * vdot (B₁ - A₁) (C₁ - A₁) +
  vdot (A₀ - C₀) (B₀ - C₀) * vdot (A₁ - B₁) (C₁ - B₁) +
  2 * sig * vcr (B₀ - A₀) (C₀ - A₀) * vcr (B₁ - A₁) (C₁ - A₁)

lemma ext2 {X Y : Pt} (h0 : X 0 = Y 0) (h1 : X 1 = Y 1) : X = Y := by
  rw [WithLp.ext_iff]
  funext i
  fin_cases i
  · exact h0
  · exact h1


noncomputable def ptA (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) : Pt :=
  C₀ + (2 * vdot (cenA A₀ B₀ C₀ A₁ B₁ C₁ sig - C₀)
      (cenB A₀ B₀ C₀ A₁ B₁ C₁ sig - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) /
    dab2 A₀ B₀ C₀ A₁ B₁ C₁ sig) •
    (cenB A₀ B₀ C₀ A₁ B₁ C₁ sig - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig)

noncomputable def ptB (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) : Pt :=
  C₀ + (2 * vdot (cenB A₀ B₀ C₀ A₁ B₁ C₁ sig - C₀)
      (cenB A₀ B₀ C₀ A₁ B₁ C₁ sig - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) /
    dab2 A₀ B₀ C₀ A₁ B₁ C₁ sig) •
    (cenB A₀ B₀ C₀ A₁ B₁ C₁ sig - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig)

noncomputable def ptC (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) : Pt :=
  ptB A₀ B₀ C₀ A₁ B₁ C₁ sig +
    (2 : ℝ) • (cenC A₀ B₀ C₀ A₁ B₁ C₁ sig - cenB A₀ B₀ C₀ A₁ B₁ C₁ sig)

noncomputable def esqA1 (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) : ℝ :=
  rasq A₀ B₀ C₀ A₁ B₁ C₁ sig + dab2 A₀ B₀ C₀ A₁ B₁ C₁ sig - rbsq A₀ B₀ C₀ A₁ B₁ C₁ sig

noncomputable def esqA2 (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) : ℝ :=
  rbsq A₀ B₀ C₀ A₁ B₁ C₁ sig + dab2 A₀ B₀ C₀ A₁ B₁ C₁ sig - rasq A₀ B₀ C₀ A₁ B₁ C₁ sig

noncomputable def esqB1 (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) : ℝ :=
  rbsq A₀ B₀ C₀ A₁ B₁ C₁ sig + dbc2 A₀ B₀ C₀ A₁ B₁ C₁ sig - rcsq A₀ B₀ C₀ A₁ B₁ C₁ sig

noncomputable def esqB2 (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) : ℝ :=
  rcsq A₀ B₀ C₀ A₁ B₁ C₁ sig + dbc2 A₀ B₀ C₀ A₁ B₁ C₁ sig - rbsq A₀ B₀ C₀ A₁ B₁ C₁ sig

noncomputable def esqC1 (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) : ℝ :=
  rcsq A₀ B₀ C₀ A₁ B₁ C₁ sig + dca2 A₀ B₀ C₀ A₁ B₁ C₁ sig - rasq A₀ B₀ C₀ A₁ B₁ C₁ sig

noncomputable def esqC2 (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) : ℝ :=
  rasq A₀ B₀ C₀ A₁ B₁ C₁ sig + dca2 A₀ B₀ C₀ A₁ B₁ C₁ sig - rcsq A₀ B₀ C₀ A₁ B₁ C₁ sig

lemma cenA_shift (A₀ B₀ C₀ A₁ B₁ C₁ t : Pt) (sig : ℝ) :
    cenA (A₀ + t) (B₀ + t) (C₀ + t) A₁ B₁ C₁ sig = cenA A₀ B₀ C₀ A₁ B₁ C₁ sig + t := by
  apply ext2 <;>
    simp only [cenA, offp, vdotE, vcrE, pt_add_zero, pt_add_one, pt_sub_zero, pt_sub_one,
      pt_smul_zero, pt_smul_one, octr_zero, octr_one] <;>
    ring

lemma cenA_shift1 (A₀ B₀ C₀ A₁ B₁ C₁ t : Pt) (sig : ℝ) :
    cenA A₀ B₀ C₀ (A₁ + t) (B₁ + t) (C₁ + t) sig = cenA A₀ B₀ C₀ A₁ B₁ C₁ sig := by
  apply ext2 <;>
    simp only [cenA, offp, vdotE, vcrE, pt_add_zero, pt_add_one, pt_sub_zero, pt_sub_one,
      pt_smul_zero, pt_smul_one, octr_zero, octr_one] <;>
    ring_nf


lemma cenB_shift (A₀ B₀ C₀ A₁ B₁ C₁ t : Pt) (sig : ℝ) :
    cenB (A₀ + t) (B₀ + t) (C₀ + t) A₁ B₁ C₁ sig = cenB A₀ B₀ C₀ A₁ B₁ C₁ sig + t := by
  apply ext2 <;>
    simp only [cenB, offp, vdotE, vcrE, pt_add_zero, pt_add_one, pt_sub_zero, pt_sub_one,
      pt_smul_zero, pt_smul_one, octr_zero, octr_one] <;>
    ring

lemma cenB_shift1 (A₀ B₀ C₀ A₁ B₁ C₁ t : Pt) (sig : ℝ) :
    cenB A₀ B₀ C₀ (A₁ + t) (B₁ + t) (C₁ + t) sig = cenB A₀ B₀ C₀ A₁ B₁ C₁ sig := by
  apply ext2 <;>
    simp only [cenB, offp, vdotE, vcrE, pt_add_zero, pt_add_one, pt_sub_zero, pt_sub_one,
      pt_smul_zero, pt_smul_one, octr_zero, octr_one] <;>
    ring_nf


lemma cenC_shift (A₀ B₀ C₀ A₁ B₁ C₁ t : Pt) (sig : ℝ) :
    cenC (A₀ + t) (B₀ + t) (C₀ + t) A₁ B₁ C₁ sig = cenC A₀ B₀ C₀ A₁ B₁ C₁ sig + t := by
  apply ext2 <;>
    simp only [cenC, offp, vdotE, vcrE, pt_add_zero, pt_add_one, pt_sub_zero, pt_sub_one,
      pt_smul_zero, pt_smul_one, octr_zero, octr_one] <;>
    ring

lemma cenC_shift1 (A₀ B₀ C₀ A₁ B₁ C₁ t : Pt) (sig : ℝ) :
    cenC A₀ B₀ C₀ (A₁ + t) (B₁ + t) (C₁ + t) sig = cenC A₀ B₀ C₀ A₁ B₁ C₁ sig := by
  apply ext2 <;>
    simp only [cenC, offp, vdotE, vcrE, pt_add_zero, pt_add_one, pt_sub_zero, pt_sub_one,
      pt_smul_zero, pt_smul_one, octr_zero, octr_one] <;>
    ring_nf


lemma cenA_inv (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) :
    cenA A₀ B₀ C₀ A₁ B₁ C₁ sig =
      cenA 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig + A₀ := by
  have h1 := cenA_shift1 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) A₁ sig
  rw [zero_add, sub_add_cancel, sub_add_cancel] at h1
  rw [← h1]
  have h0 := cenA_shift A₀ B₀ C₀ A₁ B₁ C₁ (-A₀) sig
  simp only [← sub_eq_add_neg, sub_self] at h0
  rw [h0]
  module


lemma cenB_inv (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) :
    cenB A₀ B₀ C₀ A₁ B₁ C₁ sig =
      cenB 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig + A₀ := by
  have h1 := cenB_shift1 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) A₁ sig
  rw [zero_add, sub_add_cancel, sub_add_cancel] at h1
  rw [← h1]
  have h0 := cenB_shift A₀ B₀ C₀ A₁ B₁ C₁ (-A₀) sig
  simp only [← sub_eq_add_neg, sub_self] at h0
  rw [h0]
  module


lemma cenC_inv (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) :
    cenC A₀ B₀ C₀ A₁ B₁ C₁ sig =
      cenC 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig + A₀ := by
  have h1 := cenC_shift1 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) A₁ sig
  rw [zero_add, sub_add_cancel, sub_add_cancel] at h1
  rw [← h1]
  have h0 := cenC_shift A₀ B₀ C₀ A₁ B₁ C₁ (-A₀) sig
  simp only [← sub_eq_add_neg, sub_self] at h0
  rw [h0]
  module


lemma dab2_inv (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) :
    dab2 A₀ B₀ C₀ A₁ B₁ C₁ sig = dab2 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig := by
  have hX : cenB A₀ B₀ C₀ A₁ B₁ C₁ sig =
      cenB 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig + A₀ := cenB_inv A₀ B₀ C₀ A₁ B₁ C₁ sig
  have hY : cenA A₀ B₀ C₀ A₁ B₁ C₁ sig =
      cenA 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig + A₀ := cenA_inv A₀ B₀ C₀ A₁ B₁ C₁ sig
  simp only [dab2]
  rw [hX, hY]
  simp only [vdotE, pt_sub_zero, pt_sub_one, pt_add_zero, pt_add_one, PiLp.zero_apply]
  ring


lemma dbc2_inv (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) :
    dbc2 A₀ B₀ C₀ A₁ B₁ C₁ sig = dbc2 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig := by
  have hX : cenC A₀ B₀ C₀ A₁ B₁ C₁ sig =
      cenC 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig + A₀ := cenC_inv A₀ B₀ C₀ A₁ B₁ C₁ sig
  have hY : cenB A₀ B₀ C₀ A₁ B₁ C₁ sig =
      cenB 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig + A₀ := cenB_inv A₀ B₀ C₀ A₁ B₁ C₁ sig
  simp only [dbc2]
  rw [hX, hY]
  simp only [vdotE, pt_sub_zero, pt_sub_one, pt_add_zero, pt_add_one, PiLp.zero_apply]
  ring


lemma dca2_inv (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) :
    dca2 A₀ B₀ C₀ A₁ B₁ C₁ sig = dca2 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig := by
  have hX : cenA A₀ B₀ C₀ A₁ B₁ C₁ sig =
      cenA 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig + A₀ := cenA_inv A₀ B₀ C₀ A₁ B₁ C₁ sig
  have hY : cenC A₀ B₀ C₀ A₁ B₁ C₁ sig =
      cenC 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig + A₀ := cenC_inv A₀ B₀ C₀ A₁ B₁ C₁ sig
  simp only [dca2]
  rw [hX, hY]
  simp only [vdotE, pt_sub_zero, pt_sub_one, pt_add_zero, pt_add_one, PiLp.zero_apply]
  ring


lemma rasq_inv (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) :
    rasq A₀ B₀ C₀ A₁ B₁ C₁ sig = rasq 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig := by
  have hX : cenA A₀ B₀ C₀ A₁ B₁ C₁ sig =
      cenA 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig + A₀ := cenA_inv A₀ B₀ C₀ A₁ B₁ C₁ sig
  simp only [rasq]
  rw [hX]
  simp only [vdotE, pt_sub_zero, pt_sub_one, pt_add_zero, pt_add_one, PiLp.zero_apply]
  ring


lemma rbsq_inv (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) :
    rbsq A₀ B₀ C₀ A₁ B₁ C₁ sig = rbsq 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig := by
  have hX : cenB A₀ B₀ C₀ A₁ B₁ C₁ sig =
      cenB 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig + A₀ := cenB_inv A₀ B₀ C₀ A₁ B₁ C₁ sig
  simp only [rbsq]
  rw [hX]
  simp only [vdotE, pt_sub_zero, pt_sub_one, pt_add_zero, pt_add_one, PiLp.zero_apply]
  ring


lemma rcsq_inv (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) :
    rcsq A₀ B₀ C₀ A₁ B₁ C₁ sig = rcsq 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig := by
  have hX : cenC A₀ B₀ C₀ A₁ B₁ C₁ sig =
      cenC 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig + A₀ := cenC_inv A₀ B₀ C₀ A₁ B₁ C₁ sig
  simp only [rcsq]
  rw [hX]
  simp only [vdotE, pt_sub_zero, pt_sub_one, pt_add_zero, pt_add_one, PiLp.zero_apply]
  ring


set_option maxRecDepth 8000 in
lemma kval_inv (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) :
    kval A₀ B₀ C₀ A₁ B₁ C₁ sig = kval 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig := by
  simp only [kval, sub_zero, vdotE, vcrE, pt_sub_zero, pt_sub_one, PiLp.zero_apply]
  ring


lemma esqA1_inv (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) :
    esqA1 A₀ B₀ C₀ A₁ B₁ C₁ sig = esqA1 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig := by
  simp only [esqA1, rasq_inv A₀ B₀ C₀ A₁ B₁ C₁ sig, dab2_inv A₀ B₀ C₀ A₁ B₁ C₁ sig, rbsq_inv A₀ B₀ C₀ A₁ B₁ C₁ sig]


lemma esqA2_inv (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) :
    esqA2 A₀ B₀ C₀ A₁ B₁ C₁ sig = esqA2 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig := by
  simp only [esqA2, rbsq_inv A₀ B₀ C₀ A₁ B₁ C₁ sig, dab2_inv A₀ B₀ C₀ A₁ B₁ C₁ sig, rasq_inv A₀ B₀ C₀ A₁ B₁ C₁ sig]


lemma esqB1_inv (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) :
    esqB1 A₀ B₀ C₀ A₁ B₁ C₁ sig = esqB1 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig := by
  simp only [esqB1, rbsq_inv A₀ B₀ C₀ A₁ B₁ C₁ sig, dbc2_inv A₀ B₀ C₀ A₁ B₁ C₁ sig, rcsq_inv A₀ B₀ C₀ A₁ B₁ C₁ sig]


lemma esqB2_inv (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) :
    esqB2 A₀ B₀ C₀ A₁ B₁ C₁ sig = esqB2 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig := by
  simp only [esqB2, rcsq_inv A₀ B₀ C₀ A₁ B₁ C₁ sig, dbc2_inv A₀ B₀ C₀ A₁ B₁ C₁ sig, rbsq_inv A₀ B₀ C₀ A₁ B₁ C₁ sig]


lemma esqC1_inv (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) :
    esqC1 A₀ B₀ C₀ A₁ B₁ C₁ sig = esqC1 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig := by
  simp only [esqC1, rcsq_inv A₀ B₀ C₀ A₁ B₁ C₁ sig, dca2_inv A₀ B₀ C₀ A₁ B₁ C₁ sig, rasq_inv A₀ B₀ C₀ A₁ B₁ C₁ sig]


lemma esqC2_inv (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) :
    esqC2 A₀ B₀ C₀ A₁ B₁ C₁ sig = esqC2 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig := by
  simp only [esqC2, rasq_inv A₀ B₀ C₀ A₁ B₁ C₁ sig, dca2_inv A₀ B₀ C₀ A₁ B₁ C₁ sig, rcsq_inv A₀ B₀ C₀ A₁ B₁ C₁ sig]

set_option maxRecDepth 8000 in
lemma dab2_eq
    (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) (hsig : sig = 1 ∨ sig = -1)
    (hcr1 : vcr (B₁ - A₁) (C₁ - A₁) ≠ 0) :
    4 * (vcr (B₁ - A₁) (C₁ - A₁))^2 * dab2 A₀ B₀ C₀ A₁ B₁ C₁ sig = (vdot (B₁ - A₁) (B₁ - A₁)) * kval A₀ B₀ C₀ A₁ B₁ C₁ sig := by
  unfold dab2 kval cenA cenB offp
  set qA := vdot (B₁ - A₁) (C₁ - A₁) with hqA
  set qB := vdot (A₁ - B₁) (C₁ - B₁) with hqB
  set qC := vdot (A₁ - C₁) (B₁ - C₁) with hqC
  set cr1 := vcr (B₁ - A₁) (C₁ - A₁) with hcr1d
  have huB : vdot (B₁ - A₁) (B₁ - A₁) = qA + qB := by
    rw [hqA, hqB]
    simp only [vdotE, pt_sub_zero, pt_sub_one, PiLp.zero_apply]
    ring
  rw [huB]
  have hR : (qA + qB) * (qA + qC) = qA ^ 2 + cr1 ^ 2 := by
    rw [hqA, hqB, hqC, hcr1d]
    simp only [vdotE, vcrE, pt_sub_zero, pt_sub_one, PiLp.zero_apply]
    ring
  have hcr1'' : cr1 ≠ 0 := by
    rw [hcr1d]
    exact hcr1
  unfold octr vrot
  simp only [WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one, PiLp.zero_apply, vdotE, vcrE,
    pt_sub_zero, pt_sub_one, pt_add_zero, pt_add_one, pt_smul_zero, pt_smul_one]
  field_simp [hcr1'']
  rcases hsig with rfl | rfl <;> linear_combination (- 4 * (A₀ 0) ^ 2 + 8 * (A₀ 0) * (B₀ 0) - 4 * (A₀ 1) ^ 2 + 8 * (A₀ 1) * (B₀ 1) - 4 * (B₀ 0) ^ 2 - 4 * (B₀ 1) ^ 2) * hR
set_option maxRecDepth 8000 in
lemma dbc2_eq
    (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) (hsig : sig = 1 ∨ sig = -1)
    (hcr1 : vcr (B₁ - A₁) (C₁ - A₁) ≠ 0) :
    4 * (vcr (B₁ - A₁) (C₁ - A₁))^2 * dbc2 A₀ B₀ C₀ A₁ B₁ C₁ sig = (vdot (C₁ - B₁) (C₁ - B₁)) * kval A₀ B₀ C₀ A₁ B₁ C₁ sig := by
  unfold dbc2 kval cenB cenC offp
  set qA := vdot (B₁ - A₁) (C₁ - A₁) with hqA
  set qB := vdot (A₁ - B₁) (C₁ - B₁) with hqB
  set qC := vdot (A₁ - C₁) (B₁ - C₁) with hqC
  set cr1 := vcr (B₁ - A₁) (C₁ - A₁) with hcr1d
  have huBC : vdot (C₁ - B₁) (C₁ - B₁) = qB + qC := by
    rw [hqB, hqC]
    simp only [vdotE, pt_sub_zero, pt_sub_one, PiLp.zero_apply]
    ring
  rw [huBC]
  have hR : (qA + qB) * (qA + qC) = qA ^ 2 + cr1 ^ 2 := by
    rw [hqA, hqB, hqC, hcr1d]
    simp only [vdotE, vcrE, pt_sub_zero, pt_sub_one, PiLp.zero_apply]
    ring
  have hcr1'' : cr1 ≠ 0 := by
    rw [hcr1d]
    exact hcr1
  unfold octr vrot
  simp only [WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one, PiLp.zero_apply, vdotE, vcrE,
    pt_sub_zero, pt_sub_one, pt_add_zero, pt_add_one, pt_smul_zero, pt_smul_one]
  field_simp [hcr1'']
  rcases hsig with rfl | rfl <;> linear_combination (- 4 * (B₀ 0) ^ 2 + 8 * (B₀ 0) * (C₀ 0) - 4 * (B₀ 1) ^ 2 + 8 * (B₀ 1) * (C₀ 1) - 4 * (C₀ 0) ^ 2 - 4 * (C₀ 1) ^ 2) * hR
set_option maxRecDepth 8000 in
lemma dca2_eq
    (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) (hsig : sig = 1 ∨ sig = -1)
    (hcr1 : vcr (B₁ - A₁) (C₁ - A₁) ≠ 0) :
    4 * (vcr (B₁ - A₁) (C₁ - A₁))^2 * dca2 A₀ B₀ C₀ A₁ B₁ C₁ sig = (vdot (C₁ - A₁) (C₁ - A₁)) * kval A₀ B₀ C₀ A₁ B₁ C₁ sig := by
  unfold dca2 kval cenA cenC offp
  set qA := vdot (B₁ - A₁) (C₁ - A₁) with hqA
  set qB := vdot (A₁ - B₁) (C₁ - B₁) with hqB
  set qC := vdot (A₁ - C₁) (B₁ - C₁) with hqC
  set cr1 := vcr (B₁ - A₁) (C₁ - A₁) with hcr1d
  have huC : vdot (C₁ - A₁) (C₁ - A₁) = qA + qC := by
    rw [hqA, hqC]
    simp only [vdotE, pt_sub_zero, pt_sub_one, PiLp.zero_apply]
    ring
  rw [huC]
  have hR : (qA + qB) * (qA + qC) = qA ^ 2 + cr1 ^ 2 := by
    rw [hqA, hqB, hqC, hcr1d]
    simp only [vdotE, vcrE, pt_sub_zero, pt_sub_one, PiLp.zero_apply]
    ring
  have hcr1'' : cr1 ≠ 0 := by
    rw [hcr1d]
    exact hcr1
  unfold octr vrot
  simp only [WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one, PiLp.zero_apply, vdotE, vcrE,
    pt_sub_zero, pt_sub_one, pt_add_zero, pt_add_one, pt_smul_zero, pt_smul_one]
  field_simp [hcr1'']
  rcases hsig with rfl | rfl <;> linear_combination (- 4 * (A₀ 0) ^ 2 + 8 * (A₀ 0) * (C₀ 0) - 4 * (A₀ 1) ^ 2 + 8 * (A₀ 1) * (C₀ 1) - 4 * (C₀ 0) ^ 2 - 4 * (C₀ 1) ^ 2) * hR
set_option maxRecDepth 8000 in
set_option maxHeartbeats 3200000 in
lemma eA1_eq
    (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) (hsig : sig = 1 ∨ sig = -1)
    (hcr1 : vcr (B₁ - A₁) (C₁ - A₁) ≠ 0) :
    2 * (vcr (B₁ - A₁) (C₁ - A₁))^2 * esqA1 A₀ B₀ C₀ A₁ B₁ C₁ sig = (vdot (B₁ - A₁) (B₁ - A₁)) * ((vdot (A₀ - B₀) (C₀ - B₀)) * (vdot (C₁ - A₁) (C₁ - A₁)) + (vdot (A₀ - C₀) (B₀ - C₀)) * (vdot (B₁ - A₁) (C₁ - A₁)) + sig * (vcr (B₀ - A₀) (C₀ - A₀)) * (vcr (B₁ - A₁) (C₁ - A₁))) := by
  unfold esqA1 rasq dab2 rbsq cenA cenB offp
  set qA := vdot (B₁ - A₁) (C₁ - A₁) with hqA
  set qB := vdot (A₁ - B₁) (C₁ - B₁) with hqB
  set qC := vdot (A₁ - C₁) (B₁ - C₁) with hqC
  set cr1 := vcr (B₁ - A₁) (C₁ - A₁) with hcr1d
  have huB : vdot (B₁ - A₁) (B₁ - A₁) = qA + qB := by
    rw [hqA, hqB]
    simp only [vdotE, pt_sub_zero, pt_sub_one, PiLp.zero_apply]
    ring
  have huC : vdot (C₁ - A₁) (C₁ - A₁) = qA + qC := by
    rw [hqA, hqC]
    simp only [vdotE, pt_sub_zero, pt_sub_one, PiLp.zero_apply]
    ring
  rw [huB, huC]
  have hR : (qA + qB) * (qA + qC) = qA ^ 2 + cr1 ^ 2 := by
    rw [hqA, hqB, hqC, hcr1d]
    simp only [vdotE, vcrE, pt_sub_zero, pt_sub_one, PiLp.zero_apply]
    ring
  have hcr1'' : cr1 ≠ 0 := by
    rw [hcr1d]
    exact hcr1
  unfold octr vrot
  simp only [WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one, PiLp.zero_apply, vdotE, vcrE,
    pt_sub_zero, pt_sub_one, pt_add_zero, pt_add_one, pt_smul_zero, pt_smul_one]
  field_simp [hcr1'']
  rcases hsig with rfl | rfl <;> linear_combination (2 * (A₀ 0) * (B₀ 0) - 2 * (A₀ 0) * (C₀ 0) + 2 * (A₀ 1) * (B₀ 1) - 2 * (A₀ 1) * (C₀ 1) - 2 * (B₀ 0) ^ 2 + 2 * (B₀ 0) * (C₀ 0) - 2 * (B₀ 1) ^ 2 + 2 * (B₀ 1) * (C₀ 1)) * hR
set_option maxRecDepth 8000 in
set_option maxHeartbeats 3200000 in
lemma eA2_eq
    (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) (hsig : sig = 1 ∨ sig = -1)
    (hcr1 : vcr (B₁ - A₁) (C₁ - A₁) ≠ 0) :
    2 * (vcr (B₁ - A₁) (C₁ - A₁))^2 * esqA2 A₀ B₀ C₀ A₁ B₁ C₁ sig = (vdot (B₁ - A₁) (B₁ - A₁)) * ((vdot (B₀ - A₀) (C₀ - A₀)) * (vdot (A₁ - C₁) (B₁ - C₁)) + ((vdot (B₀ - A₀) (C₀ - A₀)) + (vdot (A₀ - C₀) (B₀ - C₀))) * (vdot (A₁ - B₁) (C₁ - B₁)) + sig * (vcr (B₀ - A₀) (C₀ - A₀)) * (vcr (B₁ - A₁) (C₁ - A₁))) := by
  unfold esqA2 rasq dab2 rbsq cenA cenB offp
  set qA := vdot (B₁ - A₁) (C₁ - A₁) with hqA
  set qB := vdot (A₁ - B₁) (C₁ - B₁) with hqB
  set qC := vdot (A₁ - C₁) (B₁ - C₁) with hqC
  set cr1 := vcr (B₁ - A₁) (C₁ - A₁) with hcr1d
  have huB : vdot (B₁ - A₁) (B₁ - A₁) = qA + qB := by
    rw [hqA, hqB]
    simp only [vdotE, pt_sub_zero, pt_sub_one, PiLp.zero_apply]
    ring
  rw [huB]
  have hR : (qA + qB) * (qA + qC) = qA ^ 2 + cr1 ^ 2 := by
    rw [hqA, hqB, hqC, hcr1d]
    simp only [vdotE, vcrE, pt_sub_zero, pt_sub_one, PiLp.zero_apply]
    ring
  have hcr1'' : cr1 ≠ 0 := by
    rw [hcr1d]
    exact hcr1
  unfold octr vrot
  simp only [WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one, PiLp.zero_apply, vdotE, vcrE,
    pt_sub_zero, pt_sub_one, pt_add_zero, pt_add_one, pt_smul_zero, pt_smul_one]
  field_simp [hcr1'']
  rcases hsig with rfl | rfl <;> linear_combination (- 2 * (A₀ 0) ^ 2 + 2 * (A₀ 0) * (B₀ 0) + 2 * (A₀ 0) * (C₀ 0) - 2 * (A₀ 1) ^ 2 + 2 * (A₀ 1) * (B₀ 1) + 2 * (A₀ 1) * (C₀ 1) - 2 * (B₀ 0) * (C₀ 0) - 2 * (B₀ 1) * (C₀ 1)) * hR
set_option maxRecDepth 8000 in
set_option maxHeartbeats 3200000 in
lemma eB1_eq
    (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) (hsig : sig = 1 ∨ sig = -1)
    (hcr1 : vcr (B₁ - A₁) (C₁ - A₁) ≠ 0) :
    2 * (vcr (B₁ - A₁) (C₁ - A₁))^2 * esqB1 A₀ B₀ C₀ A₁ B₁ C₁ sig = (vdot (C₁ - B₁) (C₁ - B₁)) * ((vdot (B₀ - A₀) (C₀ - A₀)) * (vdot (A₁ - B₁) (C₁ - B₁)) + (vdot (A₀ - C₀) (B₀ - C₀)) * (vdot (B₁ - A₁) (B₁ - A₁)) + sig * (vcr (B₀ - A₀) (C₀ - A₀)) * (vcr (B₁ - A₁) (C₁ - A₁))) := by
  unfold esqB1 rbsq dbc2 rcsq cenB cenC offp
  set qA := vdot (B₁ - A₁) (C₁ - A₁) with hqA
  set qB := vdot (A₁ - B₁) (C₁ - B₁) with hqB
  set qC := vdot (A₁ - C₁) (B₁ - C₁) with hqC
  set cr1 := vcr (B₁ - A₁) (C₁ - A₁) with hcr1d
  have huBC : vdot (C₁ - B₁) (C₁ - B₁) = qB + qC := by
    rw [hqB, hqC]
    simp only [vdotE, pt_sub_zero, pt_sub_one, PiLp.zero_apply]
    ring
  have huB : vdot (B₁ - A₁) (B₁ - A₁) = qA + qB := by
    rw [hqA, hqB]
    simp only [vdotE, pt_sub_zero, pt_sub_one, PiLp.zero_apply]
    ring
  rw [huBC, huB]
  have hR : (qA + qB) * (qA + qC) = qA ^ 2 + cr1 ^ 2 := by
    rw [hqA, hqB, hqC, hcr1d]
    simp only [vdotE, vcrE, pt_sub_zero, pt_sub_one, PiLp.zero_apply]
    ring
  have hcr1'' : cr1 ≠ 0 := by
    rw [hcr1d]
    exact hcr1
  unfold octr vrot
  simp only [WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one, PiLp.zero_apply, vdotE, vcrE,
    pt_sub_zero, pt_sub_one, pt_add_zero, pt_add_one, pt_smul_zero, pt_smul_one]
  field_simp [hcr1'']
  rcases hsig with rfl | rfl <;> linear_combination (- 2 * (A₀ 0) * (B₀ 0) + 2 * (A₀ 0) * (C₀ 0) - 2 * (A₀ 1) * (B₀ 1) + 2 * (A₀ 1) * (C₀ 1) + 2 * (B₀ 0) * (C₀ 0) + 2 * (B₀ 1) * (C₀ 1) - 2 * (C₀ 0) ^ 2 - 2 * (C₀ 1) ^ 2) * hR
set_option maxRecDepth 8000 in
set_option maxHeartbeats 3200000 in
lemma eB2_eq
    (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) (hsig : sig = 1 ∨ sig = -1)
    (hcr1 : vcr (B₁ - A₁) (C₁ - A₁) ≠ 0) :
    2 * (vcr (B₁ - A₁) (C₁ - A₁))^2 * esqB2 A₀ B₀ C₀ A₁ B₁ C₁ sig = (vdot (C₁ - B₁) (C₁ - B₁)) * ((vdot (B₀ - A₀) (C₀ - A₀)) * (vdot (A₁ - C₁) (B₁ - C₁)) + (vdot (A₀ - B₀) (C₀ - B₀)) * (vdot (C₁ - A₁) (C₁ - A₁)) + sig * (vcr (B₀ - A₀) (C₀ - A₀)) * (vcr (B₁ - A₁) (C₁ - A₁))) := by
  unfold esqB2 rbsq dbc2 rcsq cenB cenC offp
  set qA := vdot (B₁ - A₁) (C₁ - A₁) with hqA
  set qB := vdot (A₁ - B₁) (C₁ - B₁) with hqB
  set qC := vdot (A₁ - C₁) (B₁ - C₁) with hqC
  set cr1 := vcr (B₁ - A₁) (C₁ - A₁) with hcr1d
  have huBC : vdot (C₁ - B₁) (C₁ - B₁) = qB + qC := by
    rw [hqB, hqC]
    simp only [vdotE, pt_sub_zero, pt_sub_one, PiLp.zero_apply]
    ring
  have huC : vdot (C₁ - A₁) (C₁ - A₁) = qA + qC := by
    rw [hqA, hqC]
    simp only [vdotE, pt_sub_zero, pt_sub_one, PiLp.zero_apply]
    ring
  rw [huBC, huC]
  have hR : (qA + qB) * (qA + qC) = qA ^ 2 + cr1 ^ 2 := by
    rw [hqA, hqB, hqC, hcr1d]
    simp only [vdotE, vcrE, pt_sub_zero, pt_sub_one, PiLp.zero_apply]
    ring
  have hcr1'' : cr1 ≠ 0 := by
    rw [hcr1d]
    exact hcr1
  unfold octr vrot
  simp only [WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one, PiLp.zero_apply, vdotE, vcrE,
    pt_sub_zero, pt_sub_one, pt_add_zero, pt_add_one, pt_smul_zero, pt_smul_one]
  field_simp [hcr1'']
  rcases hsig with rfl | rfl <;> linear_combination (2 * (A₀ 0) * (B₀ 0) - 2 * (A₀ 0) * (C₀ 0) + 2 * (A₀ 1) * (B₀ 1) - 2 * (A₀ 1) * (C₀ 1) - 2 * (B₀ 0) ^ 2 + 2 * (B₀ 0) * (C₀ 0) - 2 * (B₀ 1) ^ 2 + 2 * (B₀ 1) * (C₀ 1)) * hR
set_option maxRecDepth 8000 in
set_option maxHeartbeats 3200000 in
lemma eC1_eq
    (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) (hsig : sig = 1 ∨ sig = -1)
    (hcr1 : vcr (B₁ - A₁) (C₁ - A₁) ≠ 0) :
    2 * (vcr (B₁ - A₁) (C₁ - A₁))^2 * esqC1 A₀ B₀ C₀ A₁ B₁ C₁ sig = (vdot (C₁ - A₁) (C₁ - A₁)) * (((vdot (B₀ - A₀) (C₀ - A₀)) + (vdot (A₀ - B₀) (C₀ - B₀))) * (vdot (A₁ - C₁) (B₁ - C₁)) + (vdot (B₀ - A₀) (C₀ - A₀)) * (vdot (A₁ - B₁) (C₁ - B₁)) + sig * (vcr (B₀ - A₀) (C₀ - A₀)) * (vcr (B₁ - A₁) (C₁ - A₁))) := by
  unfold esqC1 rcsq dca2 rasq cenA cenC offp
  set qA := vdot (B₁ - A₁) (C₁ - A₁) with hqA
  set qB := vdot (A₁ - B₁) (C₁ - B₁) with hqB
  set qC := vdot (A₁ - C₁) (B₁ - C₁) with hqC
  set cr1 := vcr (B₁ - A₁) (C₁ - A₁) with hcr1d
  have huC : vdot (C₁ - A₁) (C₁ - A₁) = qA + qC := by
    rw [hqA, hqC]
    simp only [vdotE, pt_sub_zero, pt_sub_one, PiLp.zero_apply]
    ring
  rw [huC]
  have hR : (qA + qB) * (qA + qC) = qA ^ 2 + cr1 ^ 2 := by
    rw [hqA, hqB, hqC, hcr1d]
    simp only [vdotE, vcrE, pt_sub_zero, pt_sub_one, PiLp.zero_apply]
    ring
  have hcr1'' : cr1 ≠ 0 := by
    rw [hcr1d]
    exact hcr1
  unfold octr vrot
  simp only [WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one, PiLp.zero_apply, vdotE, vcrE,
    pt_sub_zero, pt_sub_one, pt_add_zero, pt_add_one, pt_smul_zero, pt_smul_one]
  field_simp [hcr1'']
  rcases hsig with rfl | rfl <;> linear_combination (- 2 * (A₀ 0) ^ 2 + 2 * (A₀ 0) * (B₀ 0) + 2 * (A₀ 0) * (C₀ 0) - 2 * (A₀ 1) ^ 2 + 2 * (A₀ 1) * (B₀ 1) + 2 * (A₀ 1) * (C₀ 1) - 2 * (B₀ 0) * (C₀ 0) - 2 * (B₀ 1) * (C₀ 1)) * hR
set_option maxRecDepth 8000 in
set_option maxHeartbeats 3200000 in
lemma eC2_eq
    (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) (hsig : sig = 1 ∨ sig = -1)
    (hcr1 : vcr (B₁ - A₁) (C₁ - A₁) ≠ 0) :
    2 * (vcr (B₁ - A₁) (C₁ - A₁))^2 * esqC2 A₀ B₀ C₀ A₁ B₁ C₁ sig = (vdot (C₁ - A₁) (C₁ - A₁)) * ((vdot (A₀ - B₀) (C₀ - B₀)) * (vdot (B₁ - A₁) (C₁ - A₁)) + (vdot (A₀ - C₀) (B₀ - C₀)) * (vdot (B₁ - A₁) (B₁ - A₁)) + sig * (vcr (B₀ - A₀) (C₀ - A₀)) * (vcr (B₁ - A₁) (C₁ - A₁))) := by
  unfold esqC2 rcsq dca2 rasq cenA cenC offp
  set qA := vdot (B₁ - A₁) (C₁ - A₁) with hqA
  set qB := vdot (A₁ - B₁) (C₁ - B₁) with hqB
  set qC := vdot (A₁ - C₁) (B₁ - C₁) with hqC
  set cr1 := vcr (B₁ - A₁) (C₁ - A₁) with hcr1d
  have huC : vdot (C₁ - A₁) (C₁ - A₁) = qA + qC := by
    rw [hqA, hqC]
    simp only [vdotE, pt_sub_zero, pt_sub_one, PiLp.zero_apply]
    ring
  have huB : vdot (B₁ - A₁) (B₁ - A₁) = qA + qB := by
    rw [hqA, hqB]
    simp only [vdotE, pt_sub_zero, pt_sub_one, PiLp.zero_apply]
    ring
  rw [huC, huB]
  have hR : (qA + qB) * (qA + qC) = qA ^ 2 + cr1 ^ 2 := by
    rw [hqA, hqB, hqC, hcr1d]
    simp only [vdotE, vcrE, pt_sub_zero, pt_sub_one, PiLp.zero_apply]
    ring
  have hcr1'' : cr1 ≠ 0 := by
    rw [hcr1d]
    exact hcr1
  unfold octr vrot
  simp only [WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one, PiLp.zero_apply, vdotE, vcrE,
    pt_sub_zero, pt_sub_one, pt_add_zero, pt_add_one, pt_smul_zero, pt_smul_one]
  field_simp [hcr1'']
  rcases hsig with rfl | rfl <;> linear_combination (- 2 * (A₀ 0) * (B₀ 0) + 2 * (A₀ 0) * (C₀ 0) - 2 * (A₀ 1) * (B₀ 1) + 2 * (A₀ 1) * (C₀ 1) + 2 * (B₀ 0) * (C₀ 0) + 2 * (B₀ 1) * (C₀ 1) - 2 * (C₀ 0) ^ 2 - 2 * (C₀ 1) ^ 2) * hR
lemma ne_zero_of_vdot_pos_left {u v : Pt} (h : 0 < vdot u v) : u ≠ 0 := by
  intro hh
  rw [hh, vdot_zero_left] at h
  exact (lt_irrefl 0 h).elim

/-- A nonzero right factor of a positive dot product. -/
lemma ne_zero_of_vdot_pos_right {u v : Pt} (h : 0 < vdot u v) : v ≠ 0 := by
  intro hh
  rw [hh, vdot_zero_right] at h
  exact (lt_irrefl 0 h).elim

/-- The shared setup: the sign choice and positivity of all the quantities
of the construction (the maximum-area expression and the E-factors that
witness the strict betweenness of the maximal triangle). -/
lemma setup_construction
    (A₀ B₀ C₀ A₁ B₁ C₁ : Pt)
    (hpA : 0 < vdot (B₀ - A₀) (C₀ - A₀)) (hpB : 0 < vdot (A₀ - B₀) (C₀ - B₀))
    (hpC : 0 < vdot (A₀ - C₀) (B₀ - C₀))
    (hqA : 0 < vdot (B₁ - A₁) (C₁ - A₁)) (hqB : 0 < vdot (A₁ - B₁) (C₁ - B₁))
    (hqC : 0 < vdot (A₁ - C₁) (B₁ - C₁))
    (hcr0 : vcr (B₀ - A₀) (C₀ - A₀) ≠ 0) (hcr1 : vcr (B₁ - A₁) (C₁ - A₁) ≠ 0) :
    ∃ sig : ℝ, sig = Real.sign (vcr (B₀ - A₀) (C₀ - A₀)) *
        Real.sign (vcr (B₁ - A₁) (C₁ - A₁)) ∧
      (sig = 1 ∨ sig = -1) ∧
      sig * vcr (B₀ - A₀) (C₀ - A₀) * vcr (B₁ - A₁) (C₁ - A₁) =
        |vcr (B₀ - A₀) (C₀ - A₀)| * |vcr (B₁ - A₁) (C₁ - A₁)| ∧
      0 < vdot (B₁ - A₁) (B₁ - A₁) ∧ 0 < vdot (C₁ - A₁) (C₁ - A₁) ∧
        0 < vdot (C₁ - B₁) (C₁ - B₁) ∧
      0 < kval A₀ B₀ C₀ A₁ B₁ C₁ sig ∧
      0 < dab2 A₀ B₀ C₀ A₁ B₁ C₁ sig ∧ 0 < dbc2 A₀ B₀ C₀ A₁ B₁ C₁ sig ∧
        0 < dca2 A₀ B₀ C₀ A₁ B₁ C₁ sig ∧
      0 < esqA1 A₀ B₀ C₀ A₁ B₁ C₁ sig ∧ 0 < esqA2 A₀ B₀ C₀ A₁ B₁ C₁ sig ∧
      0 < esqB1 A₀ B₀ C₀ A₁ B₁ C₁ sig ∧ 0 < esqB2 A₀ B₀ C₀ A₁ B₁ C₁ sig ∧
      0 < esqC1 A₀ B₀ C₀ A₁ B₁ C₁ sig ∧ 0 < esqC2 A₀ B₀ C₀ A₁ B₁ C₁ sig ∧
      maxArea A₀ B₀ C₀ A₁ B₁ C₁ =
        kval A₀ B₀ C₀ A₁ B₁ C₁ sig / (2 * |vcr (B₁ - A₁) (C₁ - A₁)|) := by
  have hneBA : B₁ - A₁ ≠ 0 := ne_zero_of_vdot_pos_left hqA
  have hneCB : C₁ - B₁ ≠ 0 := ne_zero_of_vdot_pos_right hqB
  have hneCA : C₁ - A₁ ≠ 0 := by
    have h : A₁ - C₁ ≠ 0 := ne_zero_of_vdot_pos_left hqC
    exact sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp h))
  have hc1sq : 0 < vdot (B₁ - A₁) (B₁ - A₁) := vdot_self_pos hneBA
  have hb1sq : 0 < vdot (C₁ - A₁) (C₁ - A₁) := vdot_self_pos hneCA
  have ha1sq : 0 < vdot (C₁ - B₁) (C₁ - B₁) := vdot_self_pos hneCB
  have hcr1sq : 0 < (vcr (B₁ - A₁) (C₁ - A₁))^2 := sq_pos_of_ne_zero hcr1
  have habs0 : 0 < |vcr (B₀ - A₀) (C₀ - A₀)| := abs_pos.mpr hcr0
  have habs1 : 0 < |vcr (B₁ - A₁) (C₁ - A₁)| := abs_pos.mpr hcr1
  set s0 := Real.sign (vcr (B₀ - A₀) (C₀ - A₀))
  set s1 := Real.sign (vcr (B₁ - A₁) (C₁ - A₁))
  have hsig : s0 * s1 = 1 ∨ s0 * s1 = -1 := by
    rcases Real.sign_apply_eq_of_ne_zero _ hcr0 with h | h <;>
    rcases Real.sign_apply_eq_of_ne_zero _ hcr1 with h' | h' <;> simp [s0, s1, h, h']
  have hsg : (s0 * s1) * vcr (B₀ - A₀) (C₀ - A₀) * vcr (B₁ - A₁) (C₁ - A₁) =
      |vcr (B₀ - A₀) (C₀ - A₀)| * |vcr (B₁ - A₁) (C₁ - A₁)| := by
    have e1 := sign_mul_self_eq_abs (vcr (B₀ - A₀) (C₀ - A₀))
    have e2 := sign_mul_self_eq_abs (vcr (B₁ - A₁) (C₁ - A₁))
    rw [← e1, ← e2]
    ring
  have hsgpos : 0 < (s0 * s1) * vcr (B₀ - A₀) (C₀ - A₀) * vcr (B₁ - A₁) (C₁ - A₁) := by
    rw [hsg]
    positivity
  have hK : 0 < kval A₀ B₀ C₀ A₁ B₁ C₁ (s0 * s1) := by
    have h2 : 2 * (s0 * s1) * vcr (B₀ - A₀) (C₀ - A₀) * vcr (B₁ - A₁) (C₁ - A₁) =
        2 * (|vcr (B₀ - A₀) (C₀ - A₀)| * |vcr (B₁ - A₁) (C₁ - A₁)|) := by
      linear_combination 2 * hsg
    simp only [kval]
    rw [h2]
    positivity
  have hdab2 : 0 < dab2 A₀ B₀ C₀ A₁ B₁ C₁ (s0 * s1) := by
    have h2 : 0 < 4 * (vcr (B₁ - A₁) (C₁ - A₁))^2 * dab2 A₀ B₀ C₀ A₁ B₁ C₁ (s0 * s1) := by
      rw [dab2_eq A₀ B₀ C₀ A₁ B₁ C₁ (s0 * s1) hsig hcr1]
      positivity
    exact (mul_pos_iff_of_pos_left (by positivity :
      0 < 4 * (vcr (B₁ - A₁) (C₁ - A₁))^2)).mp h2
  have hdbc2 : 0 < dbc2 A₀ B₀ C₀ A₁ B₁ C₁ (s0 * s1) := by
    have h2 : 0 < 4 * (vcr (B₁ - A₁) (C₁ - A₁))^2 * dbc2 A₀ B₀ C₀ A₁ B₁ C₁ (s0 * s1) := by
      rw [dbc2_eq A₀ B₀ C₀ A₁ B₁ C₁ (s0 * s1) hsig hcr1]
      positivity
    exact (mul_pos_iff_of_pos_left (by positivity :
      0 < 4 * (vcr (B₁ - A₁) (C₁ - A₁))^2)).mp h2
  have hdca2 : 0 < dca2 A₀ B₀ C₀ A₁ B₁ C₁ (s0 * s1) := by
    have h2 : 0 < 4 * (vcr (B₁ - A₁) (C₁ - A₁))^2 * dca2 A₀ B₀ C₀ A₁ B₁ C₁ (s0 * s1) := by
      rw [dca2_eq A₀ B₀ C₀ A₁ B₁ C₁ (s0 * s1) hsig hcr1]
      positivity
    exact (mul_pos_iff_of_pos_left (by positivity :
      0 < 4 * (vcr (B₁ - A₁) (C₁ - A₁))^2)).mp h2
  have heA1 : 0 < esqA1 A₀ B₀ C₀ A₁ B₁ C₁ (s0 * s1) := by
    have h2 : 0 < 2 * (vcr (B₁ - A₁) (C₁ - A₁))^2 * esqA1 A₀ B₀ C₀ A₁ B₁ C₁ (s0 * s1) := by
      rw [eA1_eq A₀ B₀ C₀ A₁ B₁ C₁ (s0 * s1) hsig hcr1]
      positivity
    exact (mul_pos_iff_of_pos_left (by positivity :
      0 < 2 * (vcr (B₁ - A₁) (C₁ - A₁))^2)).mp h2
  have heA2 : 0 < esqA2 A₀ B₀ C₀ A₁ B₁ C₁ (s0 * s1) := by
    have h2 : 0 < 2 * (vcr (B₁ - A₁) (C₁ - A₁))^2 * esqA2 A₀ B₀ C₀ A₁ B₁ C₁ (s0 * s1) := by
      rw [eA2_eq A₀ B₀ C₀ A₁ B₁ C₁ (s0 * s1) hsig hcr1]
      positivity
    exact (mul_pos_iff_of_pos_left (by positivity :
      0 < 2 * (vcr (B₁ - A₁) (C₁ - A₁))^2)).mp h2
  have heB1 : 0 < esqB1 A₀ B₀ C₀ A₁ B₁ C₁ (s0 * s1) := by
    have h2 : 0 < 2 * (vcr (B₁ - A₁) (C₁ - A₁))^2 * esqB1 A₀ B₀ C₀ A₁ B₁ C₁ (s0 * s1) := by
      rw [eB1_eq A₀ B₀ C₀ A₁ B₁ C₁ (s0 * s1) hsig hcr1]
      positivity
    exact (mul_pos_iff_of_pos_left (by positivity :
      0 < 2 * (vcr (B₁ - A₁) (C₁ - A₁))^2)).mp h2
  have heB2 : 0 < esqB2 A₀ B₀ C₀ A₁ B₁ C₁ (s0 * s1) := by
    have h2 : 0 < 2 * (vcr (B₁ - A₁) (C₁ - A₁))^2 * esqB2 A₀ B₀ C₀ A₁ B₁ C₁ (s0 * s1) := by
      rw [eB2_eq A₀ B₀ C₀ A₁ B₁ C₁ (s0 * s1) hsig hcr1]
      positivity
    exact (mul_pos_iff_of_pos_left (by positivity :
      0 < 2 * (vcr (B₁ - A₁) (C₁ - A₁))^2)).mp h2
  have heC1 : 0 < esqC1 A₀ B₀ C₀ A₁ B₁ C₁ (s0 * s1) := by
    have h2 : 0 < 2 * (vcr (B₁ - A₁) (C₁ - A₁))^2 * esqC1 A₀ B₀ C₀ A₁ B₁ C₁ (s0 * s1) := by
      rw [eC1_eq A₀ B₀ C₀ A₁ B₁ C₁ (s0 * s1) hsig hcr1]
      positivity
    exact (mul_pos_iff_of_pos_left (by positivity :
      0 < 2 * (vcr (B₁ - A₁) (C₁ - A₁))^2)).mp h2
  have heC2 : 0 < esqC2 A₀ B₀ C₀ A₁ B₁ C₁ (s0 * s1) := by
    have h2 : 0 < 2 * (vcr (B₁ - A₁) (C₁ - A₁))^2 * esqC2 A₀ B₀ C₀ A₁ B₁ C₁ (s0 * s1) := by
      rw [eC2_eq A₀ B₀ C₀ A₁ B₁ C₁ (s0 * s1) hsig hcr1]
      positivity
    exact (mul_pos_iff_of_pos_left (by positivity :
      0 < 2 * (vcr (B₁ - A₁) (C₁ - A₁))^2)).mp h2
  have hmax : maxArea A₀ B₀ C₀ A₁ B₁ C₁ =
      kval A₀ B₀ C₀ A₁ B₁ C₁ (s0 * s1) / (2 * |vcr (B₁ - A₁) (C₁ - A₁)|) := by
    simp only [maxArea, kval]
    rw [show 2 * (s0 * s1) * vcr (B₀ - A₀) (C₀ - A₀) * vcr (B₁ - A₁) (C₁ - A₁) =
      2 * (|vcr (B₀ - A₀) (C₀ - A₀)| * |vcr (B₁ - A₁) (C₁ - A₁)|) from by
        linear_combination 2 * hsg]
    ring
  exact ⟨s0 * s1, rfl, hsig, hsg, hc1sq, hb1sq, ha1sq, hK, hdab2, hdbc2, hdca2,
    heA1, heA2, heB1, heB2, heC1, heC2, hmax⟩

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 60000 in
lemma ptA_inv (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) :
    ptA A₀ B₀ C₀ A₁ B₁ C₁ sig = ptA 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig + A₀ := by
  have hA := cenA_inv A₀ B₀ C₀ A₁ B₁ C₁ sig
  have hB := cenB_inv A₀ B₀ C₀ A₁ B₁ C₁ sig
  simp only [ptA]
  rw [hA, hB, dab2_inv]
  rw [show cenA 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig + A₀ - C₀ = cenA 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig - (C₀ - A₀) from by module]
  rw [show cenB 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig + A₀ -
        (cenA 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig + A₀) =
      cenB 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig -
        cenA 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig from by module]
  module

lemma ptB_inv (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) :
    ptB A₀ B₀ C₀ A₁ B₁ C₁ sig = ptB 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig + A₀ := by
  have hA := cenA_inv A₀ B₀ C₀ A₁ B₁ C₁ sig
  have hB := cenB_inv A₀ B₀ C₀ A₁ B₁ C₁ sig
  simp only [ptB]
  rw [hA, hB, dab2_inv]
  rw [show cenB 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig + A₀ - C₀ = cenB 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig - (C₀ - A₀) from by module]
  rw [show cenB 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig + A₀ -
        (cenA 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig + A₀) =
      cenB 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig -
        cenA 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig from by module]
  module

lemma ptC_inv (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) :
    ptC A₀ B₀ C₀ A₁ B₁ C₁ sig = ptC 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig + A₀ := by
  have hB := ptB_inv A₀ B₀ C₀ A₁ B₁ C₁ sig
  have hC := cenC_inv A₀ B₀ C₀ A₁ B₁ C₁ sig
  have hB' := cenB_inv A₀ B₀ C₀ A₁ B₁ C₁ sig
  simp only [ptC]
  rw [hB, hC, hB']
  module

set_option maxHeartbeats 3200000 in
lemma cenA_through0
    (B₀ C₀ B₁ C₁ : Pt) (sig : ℝ) (_hsig : sig = 1 ∨ sig = -1)
    (_hcr1 : vcr (B₁ - 0) (C₁ - 0) ≠ 0) :
    vdot (C₀ - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) (C₀ - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) = vdot (B₀ - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) (B₀ - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) := by
  unfold cenA
  set sA := offp sig (vdot (B₁ - (0 : Pt)) (C₁ - (0 : Pt))) (vcr (B₁ - (0 : Pt)) (C₁ - (0 : Pt)))
  simp only [octr_zero, octr_one, vdotE, pt_sub_zero, pt_sub_one]
  ring


set_option maxHeartbeats 3200000 in
lemma vcr_cen_eq0
    (B₀ C₀ B₁ C₁ : Pt) (sig : ℝ) (hsig : sig = 1 ∨ sig = -1)
    (hcr1 : vcr (B₁ - 0) (C₁ - 0) ≠ 0) :
    4 * (vcr (B₁ - 0) (C₁ - 0)) *
        vcr (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) (cenC (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) =
      sig * kval (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig := by
  unfold kval cenA cenB cenC offp
  set qA := vdot (B₁ - (0 : Pt)) (C₁ - (0 : Pt)) with hqA
  set qB := vdot ((0 : Pt) - B₁) (C₁ - B₁) with hqB
  set qC := vdot ((0 : Pt) - C₁) (B₁ - C₁) with hqC
  set cr1 := vcr (B₁ - (0 : Pt)) (C₁ - (0 : Pt)) with hcr1d
  have hR : (qA + qB) * (qA + qC) = qA ^ 2 + cr1 ^ 2 := by
    rw [hqA, hqB, hqC, hcr1d]
    simp only [vdotE, vcrE, pt_sub_zero, pt_sub_one, PiLp.zero_apply]
    ring
  have hcr1'' : cr1 ≠ 0 := by
    rw [hcr1d]
    exact hcr1
  unfold octr vrot
  simp only [WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one, PiLp.zero_apply, vdotE, vcrE,
    pt_sub_zero, pt_sub_one, pt_add_zero, pt_add_one, pt_smul_zero, pt_smul_one]
  field_simp [hcr1'']
  rcases hsig with rfl | rfl <;> linear_combination (4 * ((B₀ 0) * (C₀ 1) - (B₀ 1) * (C₀ 0))) * hR


lemma C₀_sub_ptA0
    (B₀ C₀ B₁ C₁ : Pt) (sig : ℝ) (hsig : sig = 1 ∨ sig = -1)
    (hcr1 : vcr (B₁ - 0) (C₁ - 0) ≠ 0) (hd : dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig ≠ 0) :
    dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • (C₀ - ptA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) = esqA1 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) := by
  have h1 := cenA_through0 B₀ C₀ B₁ C₁ sig hsig hcr1
  have e1 : esqA1 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig =
      -(2 * vdot (cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - C₀)
        (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig)) := by
    rw [esqA1]
    rw [show rasq (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig =
        vdot (C₀ - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) (C₀ - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) from h1.symm]
    simp only [dab2, rbsq, vdotE, pt_sub_zero, pt_sub_one]
    ring
  rw [ptA]
  rw [show C₀ - (C₀ + (2 * vdot (cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - C₀)
          (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) /
        dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) •
        (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig)) =
      (-(2 * vdot (cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - C₀)
          (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) /
        dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig)) •
        (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) from by
    module]
  rw [← mul_smul, show dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig *
      (-(2 * vdot (cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - C₀)
        (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) /
      dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig)) =
      -(2 * vdot (cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - C₀)
        (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig)) from by
    rw [mul_neg, ← mul_div_assoc, mul_div_cancel_left₀ _ hd], e1]

lemma lagr (X Y : Pt) : (vdot Y Y) • X = (vdot X Y) • Y - (vcr X Y) • vrot Y := by
  apply ext2 <;>
    simp only [vdotE, vcrE, vrot, pt_sub_zero, pt_sub_one, pt_smul_zero, pt_smul_one,
      WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    ring

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 16000 in
lemma auxB_vcr
    (B₀ C₀ B₁ C₁ : Pt) (sig : ℝ) (hsig : sig = 1 ∨ sig = -1)
    (hcr1 : vcr (B₁ - (0 : Pt)) (C₁ - (0 : Pt)) ≠ 0) :
    vcr (dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • ((0 : Pt) - C₀) - (2 * vdot (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - C₀) (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig)) • (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig)) (cenC (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) = 0 := by
  unfold dab2 cenA cenB cenC
  set qA := vdot (B₁ - (0 : Pt)) (C₁ - (0 : Pt)) with hqA
  set qB := vdot ((0 : Pt) - B₁) (C₁ - B₁) with hqB
  set qC := vdot ((0 : Pt) - C₁) (B₁ - C₁) with hqC
  set cr1 := vcr (B₁ - (0 : Pt)) (C₁ - (0 : Pt)) with hcr1d
  have hR : (qA + qB) * (qA + qC) = qA ^ 2 + cr1 ^ 2 := by
    rw [hqA, hqB, hqC, hcr1d]
    simp only [vdotE, vcrE, pt_sub_zero, pt_sub_one, PiLp.zero_apply]
    ring
  have hcr1' : cr1 ≠ 0 := by
    rw [hcr1d]
    exact hcr1
  unfold offp
  simp only [octr_zero, octr_one, vdotE, vcrE, pt_sub_zero, pt_sub_one, pt_smul_zero,
    pt_smul_one, PiLp.zero_apply]
  field_simp [hcr1']
  rcases hsig with rfl | rfl
  · linear_combination (((B₀ 0) ^ 2 * cr1 - (B₀ 0) * (C₀ 0) * cr1 + (B₀ 0) * (C₀ 1) * qB + (B₀ 1) ^ 2 * cr1 - (B₀ 1) * (C₀ 0) * qB - (B₀ 1) * (C₀ 1) * cr1) * ((B₀ 0) * (C₀ 0) * qA - (B₀ 0) * (C₀ 1) * cr1 + (B₀ 1) * (C₀ 0) * cr1 + (B₀ 1) * (C₀ 1) * qA - (C₀ 0) ^ 2 * qA - (C₀ 0) ^ 2 * qB - (C₀ 1) ^ 2 * qA - (C₀ 1) ^ 2 * qB)) * hR
  · linear_combination (- ((B₀ 0) ^ 2 * cr1 - (B₀ 0) * (C₀ 0) * cr1 - (B₀ 0) * (C₀ 1) * qB + (B₀ 1) ^ 2 * cr1 + (B₀ 1) * (C₀ 0) * qB - (B₀ 1) * (C₀ 1) * cr1) * ((B₀ 0) * (C₀ 0) * qA + (B₀ 0) * (C₀ 1) * cr1 - (B₀ 1) * (C₀ 0) * cr1 + (B₀ 1) * (C₀ 1) * qA - (C₀ 0) ^ 2 * qA - (C₀ 0) ^ 2 * qB - (C₀ 1) ^ 2 * qA - (C₀ 1) ^ 2 * qB)) * hR

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 16000 in
lemma auxB_vdot
    (B₀ C₀ B₁ C₁ : Pt) (sig : ℝ) (hsig : sig = 1 ∨ sig = -1)
    (hcr1 : vcr (B₁ - (0 : Pt)) (C₁ - (0 : Pt)) ≠ 0) :
    vdot (dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • ((0 : Pt) - C₀) - (2 * vdot (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - C₀) (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig)) • (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig)) (cenC (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) = dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig * esqB1 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig := by
  unfold esqB1 dab2 dbc2 rbsq rcsq cenA cenB cenC
  set qA := vdot (B₁ - (0 : Pt)) (C₁ - (0 : Pt)) with hqA
  set qB := vdot ((0 : Pt) - B₁) (C₁ - B₁) with hqB
  set qC := vdot ((0 : Pt) - C₁) (B₁ - C₁) with hqC
  set cr1 := vcr (B₁ - (0 : Pt)) (C₁ - (0 : Pt)) with hcr1d
  have hR : (qA + qB) * (qA + qC) = qA ^ 2 + cr1 ^ 2 := by
    rw [hqA, hqB, hqC, hcr1d]
    simp only [vdotE, vcrE, pt_sub_zero, pt_sub_one, PiLp.zero_apply]
    ring
  have hcr1' : cr1 ≠ 0 := by
    rw [hcr1d]
    exact hcr1
  unfold offp
  simp only [octr_zero, octr_one, vdotE, vcrE, pt_sub_zero, pt_sub_one, pt_smul_zero,
    pt_smul_one, PiLp.zero_apply]
  field_simp [hcr1']
  rcases hsig with rfl | rfl
  · linear_combination (-2 * ((B₀ 0) * (C₀ 0) * cr1 + (B₀ 0) * (C₀ 1) * qA - (B₀ 1) * (C₀ 0) * qA + (B₀ 1) * (C₀ 1) * cr1) * ((B₀ 0) ^ 2 * cr1 - (B₀ 0) * (C₀ 0) * cr1 + (B₀ 0) * (C₀ 1) * qB + (B₀ 1) ^ 2 * cr1 - (B₀ 1) * (C₀ 0) * qB - (B₀ 1) * (C₀ 1) * cr1)) * hR
  · linear_combination (-2 * ((B₀ 0) * (C₀ 0) * cr1 - (B₀ 0) * (C₀ 1) * qA + (B₀ 1) * (C₀ 0) * qA + (B₀ 1) * (C₀ 1) * cr1) * ((B₀ 0) ^ 2 * cr1 - (B₀ 0) * (C₀ 0) * cr1 - (B₀ 0) * (C₀ 1) * qB + (B₀ 1) ^ 2 * cr1 + (B₀ 1) * (C₀ 0) * qB - (B₀ 1) * (C₀ 1) * cr1)) * hR

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 16000 in
lemma auxC_vcr
    (B₀ C₀ B₁ C₁ : Pt) (sig : ℝ) (hsig : sig = 1 ∨ sig = -1)
    (hcr1 : vcr (B₁ - (0 : Pt)) (C₁ - (0 : Pt)) ≠ 0) :
    vcr (dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • (B₀ - C₀) - (2 * vdot (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - C₀) (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig)) • (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) - (2 * dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) • (cenC (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig)) (cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenC (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) = 0 := by
  unfold dab2 cenA cenB cenC
  set qA := vdot (B₁ - (0 : Pt)) (C₁ - (0 : Pt)) with hqA
  set qB := vdot ((0 : Pt) - B₁) (C₁ - B₁) with hqB
  set qC := vdot ((0 : Pt) - C₁) (B₁ - C₁) with hqC
  set cr1 := vcr (B₁ - (0 : Pt)) (C₁ - (0 : Pt)) with hcr1d
  have hR : (qA + qB) * (qA + qC) = qA ^ 2 + cr1 ^ 2 := by
    rw [hqA, hqB, hqC, hcr1d]
    simp only [vdotE, vcrE, pt_sub_zero, pt_sub_one, PiLp.zero_apply]
    ring
  have hcr1' : cr1 ≠ 0 := by
    rw [hcr1d]
    exact hcr1
  unfold offp
  simp only [octr_zero, octr_one, vdotE, vcrE, pt_sub_zero, pt_sub_one, pt_smul_zero,
    pt_smul_one, PiLp.zero_apply]
  field_simp [hcr1']
  rcases hsig with rfl | rfl
  · linear_combination (- ((B₀ 0) * (C₀ 0) * cr1 + (B₀ 0) * (C₀ 1) * qA - (B₀ 1) * (C₀ 0) * qA + (B₀ 1) * (C₀ 1) * cr1) * ((B₀ 0) ^ 2 * qA - 2 * (B₀ 0) * (C₀ 0) * qA - (B₀ 0) * (C₀ 0) * qB + (B₀ 0) * (C₀ 1) * cr1 + (B₀ 1) ^ 2 * qA - (B₀ 1) * (C₀ 0) * cr1 - 2 * (B₀ 1) * (C₀ 1) * qA - (B₀ 1) * (C₀ 1) * qB + (C₀ 0) ^ 2 * qA + (C₀ 0) ^ 2 * qB + (C₀ 1) ^ 2 * qA + (C₀ 1) ^ 2 * qB)) * hR
  · linear_combination (((B₀ 0) * (C₀ 0) * cr1 - (B₀ 0) * (C₀ 1) * qA + (B₀ 1) * (C₀ 0) * qA + (B₀ 1) * (C₀ 1) * cr1) * ((B₀ 0) ^ 2 * qA - 2 * (B₀ 0) * (C₀ 0) * qA - (B₀ 0) * (C₀ 0) * qB - (B₀ 0) * (C₀ 1) * cr1 + (B₀ 1) ^ 2 * qA + (B₀ 1) * (C₀ 0) * cr1 - 2 * (B₀ 1) * (C₀ 1) * qA - (B₀ 1) * (C₀ 1) * qB + (C₀ 0) ^ 2 * qA + (C₀ 0) ^ 2 * qB + (C₀ 1) ^ 2 * qA + (C₀ 1) ^ 2 * qB)) * hR

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 16000 in
lemma auxC_vdot
    (B₀ C₀ B₁ C₁ : Pt) (sig : ℝ) (hsig : sig = 1 ∨ sig = -1)
    (hcr1 : vcr (B₁ - (0 : Pt)) (C₁ - (0 : Pt)) ≠ 0) :
    vdot (dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • (B₀ - C₀) - (2 * vdot (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - C₀) (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig)) • (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) - (2 * dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) • (cenC (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig)) (cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenC (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) = dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig * esqC1 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig := by
  unfold esqC1 dab2 dca2 rcsq rasq cenA cenB cenC
  set qA := vdot (B₁ - (0 : Pt)) (C₁ - (0 : Pt)) with hqA
  set qB := vdot ((0 : Pt) - B₁) (C₁ - B₁) with hqB
  set qC := vdot ((0 : Pt) - C₁) (B₁ - C₁) with hqC
  set cr1 := vcr (B₁ - (0 : Pt)) (C₁ - (0 : Pt)) with hcr1d
  have hR : (qA + qB) * (qA + qC) = qA ^ 2 + cr1 ^ 2 := by
    rw [hqA, hqB, hqC, hcr1d]
    simp only [vdotE, vcrE, pt_sub_zero, pt_sub_one, PiLp.zero_apply]
    ring
  have hcr1' : cr1 ≠ 0 := by
    rw [hcr1d]
    exact hcr1
  unfold offp
  simp only [octr_zero, octr_one, vdotE, vcrE, pt_sub_zero, pt_sub_one, pt_smul_zero,
    pt_smul_one, PiLp.zero_apply]
  field_simp [hcr1']
  rcases hsig with rfl | rfl
  · linear_combination (2 * ((B₀ 0) * (C₀ 0) * cr1 + (B₀ 0) * (C₀ 1) * qA - (B₀ 1) * (C₀ 0) * qA + (B₀ 1) * (C₀ 1) * cr1) * ((B₀ 0) ^ 2 * cr1 - (B₀ 0) * (C₀ 0) * cr1 + (B₀ 0) * (C₀ 1) * qB + (B₀ 1) ^ 2 * cr1 - (B₀ 1) * (C₀ 0) * qB - (B₀ 1) * (C₀ 1) * cr1)) * hR
  · linear_combination (2 * ((B₀ 0) * (C₀ 0) * cr1 - (B₀ 0) * (C₀ 1) * qA + (B₀ 1) * (C₀ 0) * qA + (B₀ 1) * (C₀ 1) * cr1) * ((B₀ 0) ^ 2 * cr1 - (B₀ 0) * (C₀ 0) * cr1 - (B₀ 0) * (C₀ 1) * qB + (B₀ 1) ^ 2 * cr1 + (B₀ 1) * (C₀ 0) * qB - (B₀ 1) * (C₀ 1) * cr1)) * hR

lemma A₀_sub_ptB0
    (B₀ C₀ B₁ C₁ : Pt) (sig : ℝ) (hsig : sig = 1 ∨ sig = -1)
    (hcr1 : vcr (B₁ - (0 : Pt)) (C₁ - (0 : Pt)) ≠ 0) (hd : dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig ≠ 0) :
    dbc2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • ((0 : Pt) - ptB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) = esqB1 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • (cenC (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) := by
  have hh : dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig * (2 * vdot (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - C₀) (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) / dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) = 2 * vdot (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - C₀) (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) := by
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hd]
  have hX : dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • ((0 : Pt) - ptB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) = dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • ((0 : Pt) - C₀) - (2 * vdot (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - C₀) (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig)) • (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) := by
    have e : dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • ((2 * vdot (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - C₀) (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) / dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) • (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig)) = (2 * vdot (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - C₀) (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig)) • (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) := by
      rw [← mul_smul, hh]
    rw [ptB, ← e]
    module
  have s1 := auxB_vcr B₀ C₀ B₁ C₁ sig hsig hcr1
  have s2 := auxB_vdot B₀ C₀ B₁ C₁ sig hsig hcr1
  have L := lagr (dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • ((0 : Pt) - C₀) - (2 * vdot (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - C₀) (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig)) • (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig)) (cenC (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig)
  rw [s1, s2, zero_smul, sub_zero] at L
  have L2 : dbc2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • (dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • ((0 : Pt) - C₀) - (2 * vdot (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - C₀) (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig)) • (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig)) = (dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig * esqB1 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) • (cenC (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) := L
  rw [← hX] at L2
  have h2 : dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • (dbc2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • ((0 : Pt) - ptB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig)) = dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • (esqB1 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • (cenC (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig)) := by
    rw [show dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • (dbc2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • ((0 : Pt) - ptB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig)) = dbc2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • (dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • ((0 : Pt) - ptB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig)) from by
      module, L2]
    module
  have h3 : (dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig)⁻¹ • (dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • (dbc2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • ((0 : Pt) - ptB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig))) =
      (dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig)⁻¹ • (dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • (esqB1 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • (cenC (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig))) := congrArg _ h2
  rw [inv_smul_smul₀ hd, inv_smul_smul₀ hd] at h3
  exact h3

lemma B₀_sub_ptC0
    (B₀ C₀ B₁ C₁ : Pt) (sig : ℝ) (hsig : sig = 1 ∨ sig = -1)
    (hcr1 : vcr (B₁ - (0 : Pt)) (C₁ - (0 : Pt)) ≠ 0) (hd : dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig ≠ 0) :
    dca2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • (B₀ - ptC (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) = esqC1 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • (cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenC (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) := by
  have hh : dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig * (2 * vdot (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - C₀) (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) / dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) = 2 * vdot (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - C₀) (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) := by
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hd]
  have hX : dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • (B₀ - ptC (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) = dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • (B₀ - C₀) - (2 * vdot (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - C₀) (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig)) • (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) - (2 * dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) • (cenC (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) := by
    have e : dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • ((2 * vdot (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - C₀) (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) / dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) • (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig)) = (2 * vdot (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - C₀) (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig)) • (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) := by
      rw [← mul_smul, hh]
    rw [ptC, ptB, ← e]
    module
  have s3 := auxC_vcr B₀ C₀ B₁ C₁ sig hsig hcr1
  have s4 := auxC_vdot B₀ C₀ B₁ C₁ sig hsig hcr1
  have L := lagr (dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • (B₀ - C₀) - (2 * vdot (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - C₀) (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig)) • (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) - (2 * dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) • (cenC (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig)) (cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenC (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig)
  rw [s3, s4, zero_smul, sub_zero] at L
  have L2 : dca2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • (dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • (B₀ - C₀) - (2 * vdot (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - C₀) (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig)) • (cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) - (2 * dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) • (cenC (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenB (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig)) = (dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig * esqC1 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) • (cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenC (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig) := L
  rw [← hX] at L2
  have h2 : dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • (dca2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • (B₀ - ptC (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig)) = dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • (esqC1 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • (cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenC (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig)) := by
    rw [show dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • (dca2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • (B₀ - ptC (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig)) = dca2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • (dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • (B₀ - ptC (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig)) from by
      module, L2]
    module
  have h3 : (dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig)⁻¹ • (dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • (dca2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • (B₀ - ptC (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig))) =
      (dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig)⁻¹ • (dab2 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • (esqC1 (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig • (cenA (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig - cenC (0 : Pt) B₀ C₀ (0 : Pt) B₁ C₁ sig))) := congrArg _ h2
  rw [inv_smul_smul₀ hd, inv_smul_smul₀ hd] at h3
  exact h3

set_option maxRecDepth 16000 in
lemma cenA_through
    (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) (hsig : sig = 1 ∨ sig = -1)
    (hcr1 : vcr (B₁ - A₁) (C₁ - A₁) ≠ 0) :
    vdot (C₀ - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) (C₀ - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) = vdot (B₀ - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) (B₀ - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) := by
  have h1 := cenA_through0 (B₀ - A₀) (C₀ - A₀) (B₁ - A₁) (C₁ - A₁) sig hsig (by simpa only [sub_zero] using hcr1)
  rw [cenA_inv]
  rw [show C₀ - (cenA 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig + A₀) = (C₀ - A₀) - cenA 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig from by module]
  rw [show B₀ - (cenA 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig + A₀) = (B₀ - A₀) - cenA 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig from by module]
  exact h1
set_option maxHeartbeats 1600000 in
lemma ptB_sub_ptA
    (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ)
    (hd : dab2 A₀ B₀ C₀ A₁ B₁ C₁ sig ≠ 0) :
    ptB A₀ B₀ C₀ A₁ B₁ C₁ sig - ptA A₀ B₀ C₀ A₁ B₁ C₁ sig = (2 : ℝ) • (cenB A₀ B₀ C₀ A₁ B₁ C₁ sig - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) := by
  have e1 : 2 * vdot (cenB A₀ B₀ C₀ A₁ B₁ C₁ sig - C₀) (cenB A₀ B₀ C₀ A₁ B₁ C₁ sig - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) - 2 * vdot (cenA A₀ B₀ C₀ A₁ B₁ C₁ sig - C₀) (cenB A₀ B₀ C₀ A₁ B₁ C₁ sig - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) =
      2 * dab2 A₀ B₀ C₀ A₁ B₁ C₁ sig := by
    rw [dab2]
    simp only [vdotE, pt_sub_zero, pt_sub_one]
    ring
  have e : (2 * vdot (cenB A₀ B₀ C₀ A₁ B₁ C₁ sig - C₀) (cenB A₀ B₀ C₀ A₁ B₁ C₁ sig - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) / dab2 A₀ B₀ C₀ A₁ B₁ C₁ sig) - (2 * vdot (cenA A₀ B₀ C₀ A₁ B₁ C₁ sig - C₀) (cenB A₀ B₀ C₀ A₁ B₁ C₁ sig - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) / dab2 A₀ B₀ C₀ A₁ B₁ C₁ sig) = 2 := by
    rw [← sub_div, e1, mul_div_cancel_right₀ _ hd]
  rw [ptB, ptA]
  have e3 : (C₀ + (2 * vdot (cenB A₀ B₀ C₀ A₁ B₁ C₁ sig - C₀) (cenB A₀ B₀ C₀ A₁ B₁ C₁ sig - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) / dab2 A₀ B₀ C₀ A₁ B₁ C₁ sig) • (cenB A₀ B₀ C₀ A₁ B₁ C₁ sig - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig)) - (C₀ + (2 * vdot (cenA A₀ B₀ C₀ A₁ B₁ C₁ sig - C₀) (cenB A₀ B₀ C₀ A₁ B₁ C₁ sig - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) / dab2 A₀ B₀ C₀ A₁ B₁ C₁ sig) • (cenB A₀ B₀ C₀ A₁ B₁ C₁ sig - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig)) =
      ((2 * vdot (cenB A₀ B₀ C₀ A₁ B₁ C₁ sig - C₀) (cenB A₀ B₀ C₀ A₁ B₁ C₁ sig - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) / dab2 A₀ B₀ C₀ A₁ B₁ C₁ sig) - (2 * vdot (cenA A₀ B₀ C₀ A₁ B₁ C₁ sig - C₀) (cenB A₀ B₀ C₀ A₁ B₁ C₁ sig - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) / dab2 A₀ B₀ C₀ A₁ B₁ C₁ sig)) • (cenB A₀ B₀ C₀ A₁ B₁ C₁ sig - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) := by
    module
  rw [e3, e]


lemma ptC_sub_ptA
    (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ)
    (hd : dab2 A₀ B₀ C₀ A₁ B₁ C₁ sig ≠ 0) :
    ptC A₀ B₀ C₀ A₁ B₁ C₁ sig - ptA A₀ B₀ C₀ A₁ B₁ C₁ sig = (2 : ℝ) • (cenC A₀ B₀ C₀ A₁ B₁ C₁ sig - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) := by
  rw [ptC]
  have h := ptB_sub_ptA A₀ B₀ C₀ A₁ B₁ C₁ sig hd
  rw [show ptB A₀ B₀ C₀ A₁ B₁ C₁ sig + (2 : ℝ) • (cenC A₀ B₀ C₀ A₁ B₁ C₁ sig - cenB A₀ B₀ C₀ A₁ B₁ C₁ sig) - ptA A₀ B₀ C₀ A₁ B₁ C₁ sig = (ptB A₀ B₀ C₀ A₁ B₁ C₁ sig - ptA A₀ B₀ C₀ A₁ B₁ C₁ sig) + (2 : ℝ) • (cenC A₀ B₀ C₀ A₁ B₁ C₁ sig - cenB A₀ B₀ C₀ A₁ B₁ C₁ sig) from by
    module, h]
  module


set_option maxHeartbeats 3200000 in
set_option maxRecDepth 16000 in
lemma C₀_sub_ptA
    (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) (hsig : sig = 1 ∨ sig = -1)
    (hcr1 : vcr (B₁ - A₁) (C₁ - A₁) ≠ 0) (hd : dab2 A₀ B₀ C₀ A₁ B₁ C₁ sig ≠ 0) :
    dab2 A₀ B₀ C₀ A₁ B₁ C₁ sig • (C₀ - ptA A₀ B₀ C₀ A₁ B₁ C₁ sig) = esqA1 A₀ B₀ C₀ A₁ B₁ C₁ sig • (cenB A₀ B₀ C₀ A₁ B₁ C₁ sig - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) := by
  rw [dab2_inv, esqA1_inv, ptA_inv, cenA_inv, cenB_inv]
  rw [show C₀ - (ptA 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig + A₀) =
      (C₀ - A₀) - ptA 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig from by module]
  rw [show cenB 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig + A₀ -
        (cenA 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig + A₀) =
      cenB 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig -
        cenA 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig from by module]
  exact C₀_sub_ptA0 (B₀ - A₀) (C₀ - A₀) (B₁ - A₁) (C₁ - A₁) sig hsig (by simpa only [sub_zero] using hcr1) (dab2_inv A₀ B₀ C₀ A₁ B₁ C₁ sig ▸ hd)
set_option maxHeartbeats 3200000 in
set_option maxRecDepth 16000 in
lemma A₀_sub_ptB
    (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) (hsig : sig = 1 ∨ sig = -1)
    (hcr1 : vcr (B₁ - A₁) (C₁ - A₁) ≠ 0) (hd : dab2 A₀ B₀ C₀ A₁ B₁ C₁ sig ≠ 0) :
    dbc2 A₀ B₀ C₀ A₁ B₁ C₁ sig • (A₀ - ptB A₀ B₀ C₀ A₁ B₁ C₁ sig) = esqB1 A₀ B₀ C₀ A₁ B₁ C₁ sig • (cenC A₀ B₀ C₀ A₁ B₁ C₁ sig - cenB A₀ B₀ C₀ A₁ B₁ C₁ sig) := by
  rw [dbc2_inv, esqB1_inv, ptB_inv, cenB_inv, cenC_inv]
  rw [show A₀ - (ptB 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig + A₀) =
      0 - ptB 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig from by module]
  rw [show cenC 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig + A₀ -
        (cenB 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig + A₀) =
      cenC 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig -
        cenB 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig from by module]
  exact A₀_sub_ptB0 (B₀ - A₀) (C₀ - A₀) (B₁ - A₁) (C₁ - A₁) sig hsig (by simpa only [sub_zero] using hcr1) (dab2_inv A₀ B₀ C₀ A₁ B₁ C₁ sig ▸ hd)
set_option maxHeartbeats 3200000 in
set_option maxRecDepth 16000 in
lemma B₀_sub_ptC
    (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) (hsig : sig = 1 ∨ sig = -1)
    (hcr1 : vcr (B₁ - A₁) (C₁ - A₁) ≠ 0) (hd : dab2 A₀ B₀ C₀ A₁ B₁ C₁ sig ≠ 0) :
    dca2 A₀ B₀ C₀ A₁ B₁ C₁ sig • (B₀ - ptC A₀ B₀ C₀ A₁ B₁ C₁ sig) = esqC1 A₀ B₀ C₀ A₁ B₁ C₁ sig • (cenA A₀ B₀ C₀ A₁ B₁ C₁ sig - cenC A₀ B₀ C₀ A₁ B₁ C₁ sig) := by
  rw [dca2_inv, esqC1_inv, ptC_inv, cenA_inv, cenC_inv]
  rw [show B₀ - (ptC 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig + A₀) =
      (B₀ - A₀) - ptC 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig from by module]
  rw [show cenA 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig + A₀ -
        (cenC 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig + A₀) =
      cenA 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig -
        cenC 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig from by module]
  exact B₀_sub_ptC0 (B₀ - A₀) (C₀ - A₀) (B₁ - A₁) (C₁ - A₁) sig hsig (by simpa only [sub_zero] using hcr1) (dab2_inv A₀ B₀ C₀ A₁ B₁ C₁ sig ▸ hd)
set_option maxHeartbeats 3200000 in
set_option maxRecDepth 16000 in
set_option maxHeartbeats 3200000 in
set_option maxRecDepth 16000 in
lemma locus_key
    (A₀ B₀ C₀ A₁ B₁ C₁ X : Pt) (sig : ℝ)
    (_hcr1 : vcr (B₁ - A₁) (C₁ - A₁) ≠ 0) :
    vdot (X - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) (X - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) - vdot (B₀ - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) (B₀ - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) =
      vdot (B₀ - X) (C₀ - X) -
        2 * offp sig (vdot (B₁ - A₁) (C₁ - A₁)) (vcr (B₁ - A₁) (C₁ - A₁)) *
          vcr (C₀ - B₀) (X - B₀) := by
  simp only [cenA]
  set sA := offp sig (vdot (B₁ - A₁) (C₁ - A₁)) (vcr (B₁ - A₁) (C₁ - A₁))
  simp only [octr_zero, octr_one, vdotE, vcrE, pt_sub_zero, pt_sub_one]
  ring

lemma locus_keyB
    (A₀ B₀ C₀ A₁ B₁ C₁ X : Pt) (sig : ℝ)
    (_hcr1 : vcr (B₁ - A₁) (C₁ - A₁) ≠ 0) :
    vdot (X - cenB A₀ B₀ C₀ A₁ B₁ C₁ sig) (X - cenB A₀ B₀ C₀ A₁ B₁ C₁ sig) -
        vdot (C₀ - cenB A₀ B₀ C₀ A₁ B₁ C₁ sig) (C₀ - cenB A₀ B₀ C₀ A₁ B₁ C₁ sig) =
      vdot (C₀ - X) (A₀ - X) -
        2 * offp sig (vdot (A₁ - B₁) (C₁ - B₁)) (vcr (B₁ - A₁) (C₁ - A₁)) *
          vcr (A₀ - C₀) (X - C₀) := by
  simp only [cenB]
  set sB := offp sig (vdot (A₁ - B₁) (C₁ - B₁)) (vcr (B₁ - A₁) (C₁ - A₁))
  simp only [octr_zero, octr_one, vdotE, vcrE, pt_sub_zero, pt_sub_one]
  ring
lemma upper_bound
    (A₀ B₀ C₀ A₁ B₁ C₁ : Pt)
    (hpA : 0 < vdot (B₀ - A₀) (C₀ - A₀)) (hpB : 0 < vdot (A₀ - B₀) (C₀ - B₀))
    (hpC : 0 < vdot (A₀ - C₀) (B₀ - C₀))
    (hqA : 0 < vdot (B₁ - A₁) (C₁ - A₁)) (hqB : 0 < vdot (A₁ - B₁) (C₁ - B₁))
    (hqC : 0 < vdot (A₁ - C₁) (B₁ - C₁))
    (hcr0 : vcr (B₀ - A₀) (C₀ - A₀) ≠ 0) (hcr1 : vcr (B₁ - A₁) (C₁ - A₁) ≠ 0)
    {A B C : Pt} (hsim : Similar A B C A₁ B₁ C₁)
    (hcirc : Circumscribed A₀ B₀ C₀ A B C) :
    area A B C ≤ maxArea A₀ B₀ C₀ A₁ B₁ C₁ := by
  obtain ⟨sig, hsigde, hsig, hsg, hc1sq, hb1sq, ha1sq, hK, hdab2, hdbc2, hdca2,
    heA1, heA2, heB1, heB2, heC1, heC2, hmax⟩ :=
    setup_construction A₀ B₀ C₀ A₁ B₁ C₁ hpA hpB hpC hqA hqB hqC hcr0 hcr1
  set s0 := Real.sign (vcr (B₀ - A₀) (C₀ - A₀))
  set s1 := Real.sign (vcr (B₁ - A₁) (C₁ - A₁))
  -- the circumscription parameters
  obtain ⟨⟨wA0, nA0l, nA0r⟩, ⟨wB0, nB0l, nB0r⟩, ⟨wC0, nC0l, nC0r⟩⟩ := hcirc
  obtain ⟨tA0, htA0, eA0⟩ := wA0
  obtain ⟨tB0, htB0, eB0⟩ := wB0
  obtain ⟨tC0, htC0, eC0⟩ := wC0
  rw [AffineMap.lineMap_apply_module] at eA0 eB0 eC0
  have eA0' : A₀ = (1 - tA0) • B + tA0 • C := eA0.symm
  have eB0' : B₀ = (1 - tB0) • C + tB0 • A := eB0.symm
  have eC0' : C₀ = (1 - tC0) • A + tC0 • B := eC0.symm
  have htA0i : 0 < tA0 ∧ tA0 < 1 := by
    rcases htA0 with ⟨h0, h1⟩
    have hne0 : tA0 ≠ 0 := by
      intro hz
      rw [hz] at eA0
      simp at eA0
      exact nA0l eA0.symm
    have hne1 : tA0 ≠ 1 := by
      intro hz
      rw [hz] at eA0
      simp at eA0
      exact nA0r eA0.symm
    exact ⟨lt_of_le_of_ne h0 (Ne.symm hne0), lt_of_le_of_ne h1 hne1⟩
  have htB0i : 0 < tB0 ∧ tB0 < 1 := by
    rcases htB0 with ⟨h0, h1⟩
    have hne0 : tB0 ≠ 0 := by
      intro hz
      rw [hz] at eB0
      simp at eB0
      exact nB0l eB0.symm
    have hne1 : tB0 ≠ 1 := by
      intro hz
      rw [hz] at eB0
      simp at eB0
      exact nB0r eB0.symm
    exact ⟨lt_of_le_of_ne h0 (Ne.symm hne0), lt_of_le_of_ne h1 hne1⟩
  have htC0i : 0 < tC0 ∧ tC0 < 1 := by
    rcases htC0 with ⟨h0, h1⟩
    have hne0 : tC0 ≠ 0 := by
      intro hz
      rw [hz] at eC0
      simp at eC0
      exact nC0l eC0.symm
    have hne1 : tC0 ≠ 1 := by
      intro hz
      rw [hz] at eC0
      simp at eC0
      exact nC0r eC0.symm
    exact ⟨lt_of_le_of_ne h0 (Ne.symm hne0), lt_of_le_of_ne h1 hne1⟩
  -- the similarity ratio
  obtain ⟨r, hr, hAB, hvdA, hvdB, hvdC⟩ := similar_vdots hsim
  have hc1d : 0 < dist A₁ B₁ := by
    have h2 : 0 < (dist A₁ B₁)^2 := by
      rw [dist_comm A₁ B₁, dist_sq B₁ A₁]
      exact hc1sq
    exact lt_of_le_of_ne dist_nonneg (by
      intro hz
      rw [← hz] at h2
      simp at h2)
  have hLd : 0 < dist A B := by
    rw [hAB]
    positivity
  have hV : |vcr (B - A) (C - A)| = r^2 * |vcr (B₁ - A₁) (C₁ - A₁)| := by
    have hsa := similar_abs_vcr hsim
    rw [hAB] at hsa
    have hc : (dist A₁ B₁)^2 ≠ 0 := ne_of_gt (sq_pos_of_ne_zero (ne_of_gt hc1d))
    apply mul_left_cancel₀ hc
    linear_combination hsa
  have hVpos : 0 < |vcr (B - A) (C - A)| := by
    rw [hV]
    have h1 : 0 < |vcr (B₁ - A₁) (C₁ - A₁)| := abs_pos.mpr hcr1
    positivity
  have hVne : vcr (B - A) (C - A) ≠ 0 := abs_pos.mp hVpos
  have hM : 0 < (1 - tC0) * (1 - tB0) * (1 - tA0) + tC0 * tB0 * tA0 := by
    have hp1 : 0 < 1 - tA0 := sub_pos.mpr htA0i.2
    have hp2 : 0 < 1 - tB0 := sub_pos.mpr htB0i.2
    have hp3 : 0 < 1 - tC0 := sub_pos.mpr htC0i.2
    have hq1 : 0 < tA0 := htA0i.1
    have hq2 : 0 < tB0 := htB0i.1
    have hq3 : 0 < tC0 := htC0i.1
    positivity
  have hsgnV : Real.sign (vcr (B - A) (C - A)) = s0 := by
    have e1 := circum_vcr_mid eA0' eB0' eC0'
    have e2 := vcr_area_id A₀ B₀ C₀
    have e3 : vcr (B₀ - A₀) (C₀ - A₀) =
        ((1 - tC0) * (1 - tB0) * (1 - tA0) + tC0 * tB0 * tA0) * vcr (B - A) (C - A) := by
      rw [← e2, e1]
    have e4 : Real.sign (vcr (B₀ - A₀) (C₀ - A₀)) = Real.sign (vcr (B - A) (C - A)) := by
      rw [e3, sign_of_mul_pos hM]
    exact e4.symm
  -- cos and sin relations at vertex A
  have hsubB₀A : B₀ - A = (1 - tB0) • (C - A) := by
    rw [eB0']
    module
  have hsubC₀A : C₀ - A = tC0 • (B - A) := by
    rw [eC0']
    module
  have hvdA' : vdot (C - A) (B - A) = r^2 * vdot (B₁ - A₁) (C₁ - A₁) := by
    rw [vdot_comm]
    exact hvdA
  have cosH : vdot (B₀ - A) (C₀ - A) = (1 - tB0) * tC0 * (r^2 * vdot (B₁ - A₁) (C₁ - A₁)) := by
    have e3 : vdot ((1 - tB0) • (C - A)) (tC0 • (B - A)) =
        (1 - tB0) * tC0 * vdot (C - A) (B - A) := by
      simp only [vdotE, pt_smul_zero, pt_smul_one, pt_sub_zero, pt_sub_one]
      ring
    rw [hsubB₀A, hsubC₀A, e3, hvdA']
  have hV2 : vcr (B - A) (C - A) = s0 * |vcr (B - A) (C - A)| := by
    rw [← hsgnV, sign_mul_abs_eq_self]
  have sinH : vcr (C₀ - B₀) (A - B₀) =
      -s0 * ((1 - tB0) * tC0 * (r^2 * |vcr (B₁ - A₁) (C₁ - A₁)|)) := by
    have e1 := circum_vcr_left eB0' eC0'
    rw [e1, hV2, hV]
    ring
  -- cos and sin relations at vertex B
  have hsubC₀B : C₀ - B = (1 - tC0) • (A - B) := by
    rw [eC0']
    module
  have hsubA₀B : A₀ - B = tA0 • (C - B) := by
    rw [eA0']
    module
  have cosHB : vdot (C₀ - B) (A₀ - B) = (1 - tC0) * tA0 * (r^2 * vdot (A₁ - B₁) (C₁ - B₁)) := by
    have e3 : vdot ((1 - tC0) • (A - B)) (tA0 • (C - B)) =
        (1 - tC0) * tA0 * vdot (A - B) (C - B) := by
      simp only [vdotE, pt_smul_zero, pt_smul_one, pt_sub_zero, pt_sub_one]
      ring
    rw [hsubC₀B, hsubA₀B, e3, hvdB]
  have sinHB : vcr (A₀ - C₀) (B - C₀) =
      -s0 * ((1 - tC0) * tA0 * (r^2 * |vcr (B₁ - A₁) (C₁ - A₁)|)) := by
    have e1 := circum_vcr_left2 eA0' eC0'
    rw [e1, hV2, hV]
    ring
  -- the sign relations
  have hs0 : s0 = 1 ∨ s0 = -1 := (Real.sign_apply_eq_of_ne_zero _ hcr0).symm
  have hs1 : s1 = 1 ∨ s1 = -1 := (Real.sign_apply_eq_of_ne_zero _ hcr1).symm
  -- locus: A and B on their circles
  have hss : sig * s0 = s1 := by
    rw [hsigde]
    rcases hs0 with h | h <;> rw [h] <;> ring
  have hlocA : vdot (A - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) (A - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) =
      vdot (B₀ - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) (B₀ - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) := by
    have hk := locus_key A₀ B₀ C₀ A₁ B₁ C₁ A sig hcr1
    have hR : vdot (B₀ - A) (C₀ - A) -
        2 * offp sig (vdot (B₁ - A₁) (C₁ - A₁)) (vcr (B₁ - A₁) (C₁ - A₁)) *
          vcr (C₀ - B₀) (A - B₀) = 0 := by
      have e : sig * s0 * |vcr (B₁ - A₁) (C₁ - A₁)| = vcr (B₁ - A₁) (C₁ - A₁) := by
        rw [hss]
        exact sign_mul_abs_eq_self _
      have e' : sig * vdot (B₁ - A₁) (C₁ - A₁) * s0 * |vcr (B₁ - A₁) (C₁ - A₁)| =
          vdot (B₁ - A₁) (C₁ - A₁) * vcr (B₁ - A₁) (C₁ - A₁) := by
        linear_combination e * vdot (B₁ - A₁) (C₁ - A₁)
      rw [cosH, sinH, offp]
      field_simp [hcr1]
      linear_combination - e' * ((1 - tB0) * tC0 * r^2)
    rw [hR] at hk
    linarith [hk]
  have hlocB : vdot (B - cenB A₀ B₀ C₀ A₁ B₁ C₁ sig) (B - cenB A₀ B₀ C₀ A₁ B₁ C₁ sig) =
      vdot (C₀ - cenB A₀ B₀ C₀ A₁ B₁ C₁ sig) (C₀ - cenB A₀ B₀ C₀ A₁ B₁ C₁ sig) := by
    have hk := locus_keyB A₀ B₀ C₀ A₁ B₁ C₁ B sig hcr1
    have hR : vdot (C₀ - B) (A₀ - B) -
        2 * offp sig (vdot (A₁ - B₁) (C₁ - B₁)) (vcr (B₁ - A₁) (C₁ - A₁)) *
          vcr (A₀ - C₀) (B - C₀) = 0 := by
      have e : sig * s0 * |vcr (B₁ - A₁) (C₁ - A₁)| = vcr (B₁ - A₁) (C₁ - A₁) := by
        rw [hss]
        exact sign_mul_abs_eq_self _
      have e' : sig * vdot (A₁ - B₁) (C₁ - B₁) * s0 * |vcr (B₁ - A₁) (C₁ - A₁)| =
          vdot (A₁ - B₁) (C₁ - B₁) * vcr (B₁ - A₁) (C₁ - A₁) := by
        linear_combination e * vdot (A₁ - B₁) (C₁ - B₁)
      rw [cosHB, sinHB, offp]
      field_simp [hcr1]
      linear_combination - e' * ((1 - tC0) * tA0 * r^2)
    rw [hR] at hk
    linarith [hk]
  -- circle incidences
  have hcircA : vdot (A - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) (A - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) =
      vdot (C₀ - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) (C₀ - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) := by
    have h1 := cenA_through A₀ B₀ C₀ A₁ B₁ C₁ sig hsig hcr1
    rw [hlocA, h1]
  -- chord relations
  have hsubA : A - C₀ = -tC0 • (B - A) := by
    rw [eC0']
    module
  have hsubB : B - C₀ = (1 - tC0) • (B - A) := by
    rw [eC0']
    module
  have hchord1 : tC0 * vdot (B - A) (B - A) = 2 * vdot (B - A) (C₀ - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) := by
    have h := vdot_chord hcircA
    rw [hsubA] at h
    have e1 : vdot (-tC0 • (B - A)) (-tC0 • (B - A)) = tC0^2 * vdot (B - A) (B - A) := by
      simp only [vdotE, pt_smul_zero, pt_smul_one, pt_sub_zero, pt_sub_one]
      ring
    have e2 : vdot (-tC0 • (B - A)) (C₀ - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) =
        -tC0 * vdot (B - A) (C₀ - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) := by
      simp only [vdotE, pt_smul_zero, pt_smul_one, pt_sub_zero, pt_sub_one]
      ring
    rw [e1, e2] at h
    have ht : tC0 ≠ 0 := ne_of_gt htC0i.1
    have h2 : tC0 * (tC0 * vdot (B - A) (B - A) - 2 * vdot (B - A) (C₀ - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig)) = 0 := by
      linear_combination h
    rcases mul_eq_zero.mp h2 with htc | hres
    · exact (ht htc).elim
    · linear_combination hres
  have hchord2 : (1 - tC0) * vdot (B - A) (B - A) = -2 * vdot (B - A) (C₀ - cenB A₀ B₀ C₀ A₁ B₁ C₁ sig) := by
    have h := vdot_chord hlocB
    rw [hsubB] at h
    have e1 : vdot ((1 - tC0) • (B - A)) ((1 - tC0) • (B - A)) =
        (1 - tC0)^2 * vdot (B - A) (B - A) := by
      simp only [vdotE, pt_smul_zero, pt_smul_one, pt_sub_zero, pt_sub_one]
      ring
    have e2 : vdot ((1 - tC0) • (B - A)) (C₀ - cenB A₀ B₀ C₀ A₁ B₁ C₁ sig) =
        (1 - tC0) * vdot (B - A) (C₀ - cenB A₀ B₀ C₀ A₁ B₁ C₁ sig) := by
      simp only [vdotE, pt_smul_zero, pt_smul_one, pt_sub_zero, pt_sub_one]
      ring
    rw [e1, e2] at h
    have ht : (1 - tC0) ≠ 0 := sub_ne_zero_of_ne (ne_of_gt htC0i.2)
    have h2 : (1 - tC0) * ((1 - tC0) * vdot (B - A) (B - A) + 2 * vdot (B - A) (C₀ - cenB A₀ B₀ C₀ A₁ B₁ C₁ sig)) = 0 := by
      linear_combination h
    rcases mul_eq_zero.mp h2 with htc | hres
    · exact (ht htc).elim
    · linear_combination hres
  -- the side bound
  have hLsq : vdot (B - A) (B - A) =
      2 * vdot (B - A) (cenB A₀ B₀ C₀ A₁ B₁ C₁ sig - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) := by
    have e : vdot (B - A) (C₀ - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) -
        vdot (B - A) (C₀ - cenB A₀ B₀ C₀ A₁ B₁ C₁ sig) =
        vdot (B - A) (cenB A₀ B₀ C₀ A₁ B₁ C₁ sig - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) := by
      simp only [vdotE, pt_sub_zero, pt_sub_one]
      ring
    linear_combination hchord1 + hchord2 + 2 * e
  have hL2 : (dist A B)^2 = vdot (B - A) (B - A) := by
    rw [dist_comm A B]
    exact dist_sq B A
  have hcs : vdot (B - A) (cenB A₀ B₀ C₀ A₁ B₁ C₁ sig - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) ≤
      dist A B * Real.sqrt (dab2 A₀ B₀ C₀ A₁ B₁ C₁ sig) := by
    have h1 : (vdot (B - A) (cenB A₀ B₀ C₀ A₁ B₁ C₁ sig - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig))^2 ≤
        vdot (B - A) (B - A) * dab2 A₀ B₀ C₀ A₁ B₁ C₁ sig := by
      have lag := lagrange (B - A) (cenB A₀ B₀ C₀ A₁ B₁ C₁ sig - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig)
      have hnn : 0 ≤ (vcr (B - A) (cenB A₀ B₀ C₀ A₁ B₁ C₁ sig - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig))^2 :=
        sq_nonneg _
      have hdab : dab2 A₀ B₀ C₀ A₁ B₁ C₁ sig =
          vdot (cenB A₀ B₀ C₀ A₁ B₁ C₁ sig - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig)
            (cenB A₀ B₀ C₀ A₁ B₁ C₁ sig - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) := rfl
      rw [hdab]
      linarith [lag, hnn]
    have h2 : vdot (B - A) (cenB A₀ B₀ C₀ A₁ B₁ C₁ sig - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) ≤
        Real.sqrt (vdot (B - A) (B - A) * dab2 A₀ B₀ C₀ A₁ B₁ C₁ sig) := by
      have h4 : vdot (B - A) (cenB A₀ B₀ C₀ A₁ B₁ C₁ sig - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) ≤
          Real.sqrt ((vdot (B - A) (cenB A₀ B₀ C₀ A₁ B₁ C₁ sig - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig))^2) := by
        rw [Real.sqrt_sq_eq_abs]
        exact le_abs_self _
      exact h4.trans (Real.sqrt_le_sqrt h1)
    have hs : Real.sqrt (vdot (B - A) (B - A)) = dist A B := by
      rw [← hL2]
      exact Real.sqrt_sq dist_nonneg
    have hvnn : 0 ≤ vdot (B - A) (B - A) := by
      rw [← norm_sq_eq_vdot]
      positivity
    rw [Real.sqrt_mul hvnn] at h2
    rw [hs] at h2
    exact h2
  have hbound : dist A B ≤ 2 * Real.sqrt (dab2 A₀ B₀ C₀ A₁ B₁ C₁ sig) := by
    have h3 : (dist A B)^2 ≤ 2 * (dist A B) * Real.sqrt (dab2 A₀ B₀ C₀ A₁ B₁ C₁ sig) := by
      rw [hL2, hLsq]
      linarith [hcs]
    rcases eq_or_lt_of_le (dist_nonneg : (0 : ℝ) ≤ dist A B) with hz | hz
    · rw [← hz]
      positivity
    · rw [pow_two] at h3
      have h3' : dist A B * dist A B ≤ (2 * Real.sqrt (dab2 A₀ B₀ C₀ A₁ B₁ C₁ sig)) * dist A B := by
        linear_combination h3
      exact le_of_mul_le_mul_right h3' hz
  -- the area comparison
  have harea : area A B C * (dist A₁ B₁)^2 = area A₁ B₁ C₁ * (dist A B)^2 := by
    have hsa := similar_abs_vcr hsim
    rw [area, area]
    linear_combination hsa / 2
  have harea1 : 0 ≤ area A₁ B₁ C₁ := by
    rw [area]
    positivity
  have hfin : area A B C * (dist A₁ B₁)^2 ≤ area A₁ B₁ C₁ * (2 * Real.sqrt (dab2 A₀ B₀ C₀ A₁ B₁ C₁ sig))^2 := by
    rw [harea]
    have h1 : (dist A B)^2 ≤ (2 * Real.sqrt (dab2 A₀ B₀ C₀ A₁ B₁ C₁ sig))^2 :=
      (sq_le_sq₀ dist_nonneg (by positivity)).mpr hbound
    exact mul_le_mul_of_nonneg_left h1 harea1
  have hcd2 : 0 < (dist A₁ B₁)^2 := by
    rw [dist_comm A₁ B₁, dist_sq B₁ A₁]
    exact hc1sq
  have hR : area A₁ B₁ C₁ * (2 * Real.sqrt (dab2 A₀ B₀ C₀ A₁ B₁ C₁ sig))^2 / (dist A₁ B₁)^2 =
      maxArea A₀ B₀ C₀ A₁ B₁ C₁ := by
    rw [hmax]
    have hd := dab2_eq A₀ B₀ C₀ A₁ B₁ C₁ sig hsig hcr1
    have hdsq : (dist A₁ B₁)^2 = vdot (B₁ - A₁) (B₁ - A₁) := by
      rw [dist_comm A₁ B₁]
      exact dist_sq B₁ A₁
    rw [area, hdsq, mul_pow, Real.sq_sqrt hdab2.le]
    have hsa2 : |vcr (B₁ - A₁) (C₁ - A₁)|^2 = (vcr (B₁ - A₁) (C₁ - A₁))^2 := sq_abs _
    have habs1 : 0 < |vcr (B₁ - A₁) (C₁ - A₁)| := abs_pos.mpr hcr1
    rw [div_eq_div_iff hc1sq.ne' (by positivity : (0 : ℝ) < 2 * |vcr (B₁ - A₁) (C₁ - A₁)|).ne']
    linear_combination hd + 4 * dab2 A₀ B₀ C₀ A₁ B₁ C₁ sig * hsa2
  rw [← hR]
  exact (le_div_iff₀ hcd2).mpr hfin

/-- The cross product scales on the left. -/
lemma vcr_smul_left (s : ℝ) (u v : Pt) : vcr (s • u) v = s * vcr u v := by
  simp only [vcrE, pt_smul_zero, pt_smul_one]
  ring

/-- The cross product scales on the right. -/
lemma vcr_smul_right (s : ℝ) (u v : Pt) : vcr u (s • v) = s * vcr u v := by
  simp only [vcrE, pt_smul_zero, pt_smul_one]
  ring

/-- The norm is the square root of the self dot product. -/
lemma norm_eq_sqrt_vdot (u : Pt) : ‖u‖ = Real.sqrt (vdot u u) := by
  rw [← norm_sq_eq_vdot]
  exact (Real.sqrt_sq (norm_nonneg u)).symm

/-- The distance between two points whose difference is `2 • u`. -/
lemma dist_eq_two_mul_norm {P Q u : Pt} (h : Q - P = (2 : ℝ) • u) :
    dist P Q = 2 * ‖u‖ := by
  rw [dist_eq_norm, norm_sub_rev, h, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 16000 in
/-- The cross product of the two center differences is, up to the sign, the
maximum-area numerator. This is the algebraic heart of the area computation
for the constructed triangle. -/
lemma vcr_cen_eq
    (A₀ B₀ C₀ A₁ B₁ C₁ : Pt) (sig : ℝ) (hsig : sig = 1 ∨ sig = -1)
    (hcr1 : vcr (B₁ - A₁) (C₁ - A₁) ≠ 0) :
    4 * (vcr (B₁ - A₁) (C₁ - A₁)) *
        vcr (cenB A₀ B₀ C₀ A₁ B₁ C₁ sig - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig)
          (cenC A₀ B₀ C₀ A₁ B₁ C₁ sig - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) =
      sig * kval A₀ B₀ C₀ A₁ B₁ C₁ sig := by
  rw [kval_inv, cenA_inv, cenB_inv, cenC_inv]
  rw [show cenB 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig + A₀ - (cenA 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig + A₀) = cenB 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig - cenA 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig from by module]
  rw [show cenC 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig + A₀ - (cenA 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig + A₀) = cenC 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig - cenA 0 (B₀ - A₀) (C₀ - A₀) 0 (B₁ - A₁) (C₁ - A₁) sig from by module]
  convert vcr_cen_eq0 (B₀ - A₀) (C₀ - A₀) (B₁ - A₁) (C₁ - A₁) sig hsig (by simpa only [sub_zero] using hcr1) using 1
  · simp only [sub_zero]

lemma sbtw_of_smul {P Q X : Pt} {d e e' : ℝ}
    (hd : 0 < d) (he : 0 < e) (he' : 0 < e') (hsum : e + e' = 2 * d)
    (h : (2 * d) • (X - P) = e • (Q - P)) (hne : Q - P ≠ 0) :
    Sbtw ℝ P X Q := by
  have h2d : (2 : ℝ) * d ≠ 0 := ne_of_gt (by positivity)
  have ht0 : 0 < e / (2 * d) := div_pos he (by positivity)
  have ht1 : e / (2 * d) < 1 := by
    rw [div_lt_one (by positivity : (0 : ℝ) < 2 * d)]
    linarith
  have hXsub : X - P = (e / (2 * d)) • (Q - P) := by
    rw [div_eq_mul_inv, mul_comm e (2 * d)⁻¹, mul_smul, ← h, inv_smul_smul₀ h2d]
  have heq : AffineMap.lineMap P Q (e / (2 * d)) = X := by
    rw [AffineMap.lineMap_apply_module, show X = P + (X - P) from by module, hXsub]
    module
  refine ⟨⟨e / (2 * d), ⟨ht0.le, ht1.le⟩, heq⟩, ?_, ?_⟩
  · intro hh
    rw [hh, sub_self] at hXsub
    rcases smul_eq_zero.mp hXsub.symm with h0 | h0
    · exact (ne_of_gt ht0) h0
    · exact hne h0
  · intro hh
    have hX2 : X - Q = (e / (2 * d) - 1) • (Q - P) := by
      rw [show X - Q = (X - P) - (Q - P) from by module, hXsub]
      module
    rw [hh, sub_self] at hX2
    rcases smul_eq_zero.mp hX2.symm with h0 | h0
    · have ht : e / (2 * d) = 1 := sub_eq_zero.mp h0
      linarith
    · exact hne h0

/-- The construction: the explicitly built triangle is similar to `A₁B₁C₁`,
is circumscribed about `A₀B₀C₀`, and realizes `maxArea`. -/
lemma construction_mem
    (A₀ B₀ C₀ A₁ B₁ C₁ : Pt)
    (hpA : 0 < vdot (B₀ - A₀) (C₀ - A₀)) (hpB : 0 < vdot (A₀ - B₀) (C₀ - B₀))
    (hpC : 0 < vdot (A₀ - C₀) (B₀ - C₀))
    (hqA : 0 < vdot (B₁ - A₁) (C₁ - A₁)) (hqB : 0 < vdot (A₁ - B₁) (C₁ - B₁))
    (hqC : 0 < vdot (A₁ - C₁) (B₁ - C₁))
    (hcr0 : vcr (B₀ - A₀) (C₀ - A₀) ≠ 0) (hcr1 : vcr (B₁ - A₁) (C₁ - A₁) ≠ 0) :
    ∃ A B C : Pt, Similar A B C A₁ B₁ C₁ ∧ Circumscribed A₀ B₀ C₀ A B C ∧
      maxArea A₀ B₀ C₀ A₁ B₁ C₁ = area A B C := by
  obtain ⟨sig, _, hsig, _, hc1sq, hb1sq, ha1sq, hK, hdab2, hdbc2, hdca2,
    heA1, heA2, heB1, heB2, heC1, heC2, hmax⟩ :=
    setup_construction A₀ B₀ C₀ A₁ B₁ C₁ hpA hpB hpC hqA hqB hqC hcr0 hcr1
  have hcr1pos : 0 < |vcr (B₁ - A₁) (C₁ - A₁)| := abs_pos.mpr hcr1
  have hdab2ne : dab2 A₀ B₀ C₀ A₁ B₁ C₁ sig ≠ 0 := hdab2.ne'
  -- side vectors of the constructed triangle
  have hsubAB : ptB A₀ B₀ C₀ A₁ B₁ C₁ sig - ptA A₀ B₀ C₀ A₁ B₁ C₁ sig =
      (2 : ℝ) • (cenB A₀ B₀ C₀ A₁ B₁ C₁ sig - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) :=
    ptB_sub_ptA A₀ B₀ C₀ A₁ B₁ C₁ sig hdab2ne
  have hsubAC : ptC A₀ B₀ C₀ A₁ B₁ C₁ sig - ptA A₀ B₀ C₀ A₁ B₁ C₁ sig =
      (2 : ℝ) • (cenC A₀ B₀ C₀ A₁ B₁ C₁ sig - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) :=
    ptC_sub_ptA A₀ B₀ C₀ A₁ B₁ C₁ sig hdab2ne
  have hsubBC : ptC A₀ B₀ C₀ A₁ B₁ C₁ sig - ptB A₀ B₀ C₀ A₁ B₁ C₁ sig =
      (2 : ℝ) • (cenC A₀ B₀ C₀ A₁ B₁ C₁ sig - cenB A₀ B₀ C₀ A₁ B₁ C₁ sig) := by
    rw [ptC]
    module
  have hsubCA : ptA A₀ B₀ C₀ A₁ B₁ C₁ sig - ptC A₀ B₀ C₀ A₁ B₁ C₁ sig =
      (2 : ℝ) • (cenA A₀ B₀ C₀ A₁ B₁ C₁ sig - cenC A₀ B₀ C₀ A₁ B₁ C₁ sig) := by
    rw [show ptA A₀ B₀ C₀ A₁ B₁ C₁ sig - ptC A₀ B₀ C₀ A₁ B₁ C₁ sig =
      -(ptC A₀ B₀ C₀ A₁ B₁ C₁ sig - ptA A₀ B₀ C₀ A₁ B₁ C₁ sig) from by module, hsubAC]
    module
  -- square-root computations for the side lengths
  have hs2 : Real.sqrt (4 * (vcr (B₁ - A₁) (C₁ - A₁))^2) =
      2 * |vcr (B₁ - A₁) (C₁ - A₁)| := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), Real.sqrt_sq_eq_abs,
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hs1A : Real.sqrt (vdot (B₁ - A₁) (B₁ - A₁)) = dist A₁ B₁ := by
    rw [← dist_sq B₁ A₁, Real.sqrt_sq dist_nonneg, dist_comm]
  have hs1B : Real.sqrt (vdot (C₁ - B₁) (C₁ - B₁)) = dist B₁ C₁ := by
    rw [← dist_sq C₁ B₁, Real.sqrt_sq dist_nonneg, dist_comm]
  have hs1C : Real.sqrt (vdot (C₁ - A₁) (C₁ - A₁)) = dist C₁ A₁ := by
    rw [← dist_sq C₁ A₁, Real.sqrt_sq dist_nonneg]
  have h4 : (0 : ℝ) < 4 * (vcr (B₁ - A₁) (C₁ - A₁))^2 := by positivity
  have h2c : (2 * |vcr (B₁ - A₁) (C₁ - A₁)| : ℝ) ≠ 0 := ne_of_gt (by positivity)
  -- the three side lengths: all share the ratio `√K / |cr₁|`
  have hsAB : dist (ptA A₀ B₀ C₀ A₁ B₁ C₁ sig) (ptB A₀ B₀ C₀ A₁ B₁ C₁ sig) =
      Real.sqrt (kval A₀ B₀ C₀ A₁ B₁ C₁ sig) / |vcr (B₁ - A₁) (C₁ - A₁)| *
        dist A₁ B₁ := by
    have hd := dab2_eq A₀ B₀ C₀ A₁ B₁ C₁ sig hsig hcr1
    simp only [dab2] at hd
    have hdeq : vdot (cenB A₀ B₀ C₀ A₁ B₁ C₁ sig - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig)
          (cenB A₀ B₀ C₀ A₁ B₁ C₁ sig - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) =
        vdot (B₁ - A₁) (B₁ - A₁) * kval A₀ B₀ C₀ A₁ B₁ C₁ sig /
          (4 * (vcr (B₁ - A₁) (C₁ - A₁))^2) := by
      rw [eq_div_iff h4.ne']
      linear_combination hd
    rw [dist_eq_two_mul_norm hsubAB, norm_eq_sqrt_vdot, hdeq,
      Real.sqrt_div' _ h4.le, Real.sqrt_mul hc1sq.le, hs1A, hs2,
      div_mul_eq_mul_div, mul_div_assoc', div_eq_div_iff h2c hcr1pos.ne']
    ring
  have hsBC : dist (ptB A₀ B₀ C₀ A₁ B₁ C₁ sig) (ptC A₀ B₀ C₀ A₁ B₁ C₁ sig) =
      Real.sqrt (kval A₀ B₀ C₀ A₁ B₁ C₁ sig) / |vcr (B₁ - A₁) (C₁ - A₁)| *
        dist B₁ C₁ := by
    have hd := dbc2_eq A₀ B₀ C₀ A₁ B₁ C₁ sig hsig hcr1
    simp only [dbc2] at hd
    have hdeq : vdot (cenC A₀ B₀ C₀ A₁ B₁ C₁ sig - cenB A₀ B₀ C₀ A₁ B₁ C₁ sig)
          (cenC A₀ B₀ C₀ A₁ B₁ C₁ sig - cenB A₀ B₀ C₀ A₁ B₁ C₁ sig) =
        vdot (C₁ - B₁) (C₁ - B₁) * kval A₀ B₀ C₀ A₁ B₁ C₁ sig /
          (4 * (vcr (B₁ - A₁) (C₁ - A₁))^2) := by
      rw [eq_div_iff h4.ne']
      linear_combination hd
    rw [dist_eq_two_mul_norm hsubBC, norm_eq_sqrt_vdot, hdeq,
      Real.sqrt_div' _ h4.le, Real.sqrt_mul ha1sq.le, hs1B, hs2,
      div_mul_eq_mul_div, mul_div_assoc', div_eq_div_iff h2c hcr1pos.ne']
    ring
  have hsCA : dist (ptC A₀ B₀ C₀ A₁ B₁ C₁ sig) (ptA A₀ B₀ C₀ A₁ B₁ C₁ sig) =
      Real.sqrt (kval A₀ B₀ C₀ A₁ B₁ C₁ sig) / |vcr (B₁ - A₁) (C₁ - A₁)| *
        dist C₁ A₁ := by
    have hd := dca2_eq A₀ B₀ C₀ A₁ B₁ C₁ sig hsig hcr1
    simp only [dca2] at hd
    have hdeq : vdot (cenA A₀ B₀ C₀ A₁ B₁ C₁ sig - cenC A₀ B₀ C₀ A₁ B₁ C₁ sig)
          (cenA A₀ B₀ C₀ A₁ B₁ C₁ sig - cenC A₀ B₀ C₀ A₁ B₁ C₁ sig) =
        vdot (C₁ - A₁) (C₁ - A₁) * kval A₀ B₀ C₀ A₁ B₁ C₁ sig /
          (4 * (vcr (B₁ - A₁) (C₁ - A₁))^2) := by
      rw [eq_div_iff h4.ne']
      linear_combination hd
    rw [dist_eq_two_mul_norm hsubCA, norm_eq_sqrt_vdot, hdeq,
      Real.sqrt_div' _ h4.le, Real.sqrt_mul hb1sq.le, hs1C, hs2,
      div_mul_eq_mul_div, mul_div_assoc', div_eq_div_iff h2c hcr1pos.ne']
    ring
  -- the similarity
  have hrrpos : 0 < Real.sqrt (kval A₀ B₀ C₀ A₁ B₁ C₁ sig) /
      |vcr (B₁ - A₁) (C₁ - A₁)| := div_pos (Real.sqrt_pos.mpr hK) hcr1pos
  have hsim : Similar (ptA A₀ B₀ C₀ A₁ B₁ C₁ sig) (ptB A₀ B₀ C₀ A₁ B₁ C₁ sig)
      (ptC A₀ B₀ C₀ A₁ B₁ C₁ sig) A₁ B₁ C₁ :=
    ⟨Real.sqrt (kval A₀ B₀ C₀ A₁ B₁ C₁ sig) / |vcr (B₁ - A₁) (C₁ - A₁)|, hrrpos,
      hsAB, hsBC, hsCA⟩
  -- non-degeneracy of the constructed triangle
  have hdA1B1 : 0 < dist A₁ B₁ := by
    have h2 : 0 < (dist A₁ B₁)^2 := by
      rw [dist_comm A₁ B₁, dist_sq B₁ A₁]
      exact hc1sq
    exact lt_of_le_of_ne dist_nonneg (by
      intro hz
      rw [← hz] at h2
      simp at h2)
  have hdB1C1 : 0 < dist B₁ C₁ := by
    have h2 : 0 < (dist B₁ C₁)^2 := by
      rw [dist_comm B₁ C₁, dist_sq C₁ B₁]
      exact ha1sq
    exact lt_of_le_of_ne dist_nonneg (by
      intro hz
      rw [← hz] at h2
      simp at h2)
  have hdC1A1 : 0 < dist C₁ A₁ := by
    have h2 : 0 < (dist C₁ A₁)^2 := by
      rw [dist_sq C₁ A₁]
      exact hb1sq
    exact lt_of_le_of_ne dist_nonneg (by
      intro hz
      rw [← hz] at h2
      simp at h2)
  have hneAB : ptB A₀ B₀ C₀ A₁ B₁ C₁ sig - ptA A₀ B₀ C₀ A₁ B₁ C₁ sig ≠ 0 := by
    have hpos : 0 < dist (ptA A₀ B₀ C₀ A₁ B₁ C₁ sig) (ptB A₀ B₀ C₀ A₁ B₁ C₁ sig) := by
      rw [hsAB]
      exact mul_pos hrrpos hdA1B1
    exact sub_ne_zero.mpr (dist_ne_zero.mp (ne_of_gt hpos)).symm
  have hneBC : ptC A₀ B₀ C₀ A₁ B₁ C₁ sig - ptB A₀ B₀ C₀ A₁ B₁ C₁ sig ≠ 0 := by
    have hpos : 0 < dist (ptB A₀ B₀ C₀ A₁ B₁ C₁ sig) (ptC A₀ B₀ C₀ A₁ B₁ C₁ sig) := by
      rw [hsBC]
      exact mul_pos hrrpos hdB1C1
    exact sub_ne_zero.mpr (dist_ne_zero.mp (ne_of_gt hpos)).symm
  have hneCA : ptA A₀ B₀ C₀ A₁ B₁ C₁ sig - ptC A₀ B₀ C₀ A₁ B₁ C₁ sig ≠ 0 := by
    have hpos : 0 < dist (ptC A₀ B₀ C₀ A₁ B₁ C₁ sig) (ptA A₀ B₀ C₀ A₁ B₁ C₁ sig) := by
      rw [hsCA]
      exact mul_pos hrrpos hdC1A1
    exact sub_ne_zero.mpr (dist_ne_zero.mp (ne_of_gt hpos)).symm
  -- the betweenness relations
  have hsumA : esqA1 A₀ B₀ C₀ A₁ B₁ C₁ sig + esqA2 A₀ B₀ C₀ A₁ B₁ C₁ sig =
      2 * dab2 A₀ B₀ C₀ A₁ B₁ C₁ sig := by
    simp only [esqA1, esqA2]
    ring
  have hsumB : esqB1 A₀ B₀ C₀ A₁ B₁ C₁ sig + esqB2 A₀ B₀ C₀ A₁ B₁ C₁ sig =
      2 * dbc2 A₀ B₀ C₀ A₁ B₁ C₁ sig := by
    simp only [esqB1, esqB2]
    ring
  have hsumC : esqC1 A₀ B₀ C₀ A₁ B₁ C₁ sig + esqC2 A₀ B₀ C₀ A₁ B₁ C₁ sig =
      2 * dca2 A₀ B₀ C₀ A₁ B₁ C₁ sig := by
    simp only [esqC1, esqC2]
    ring
  have hA2d : (2 * dab2 A₀ B₀ C₀ A₁ B₁ C₁ sig) •
        (C₀ - ptA A₀ B₀ C₀ A₁ B₁ C₁ sig) =
      esqA1 A₀ B₀ C₀ A₁ B₁ C₁ sig •
        (ptB A₀ B₀ C₀ A₁ B₁ C₁ sig - ptA A₀ B₀ C₀ A₁ B₁ C₁ sig) := by
    have h1 := C₀_sub_ptA A₀ B₀ C₀ A₁ B₁ C₁ sig hsig hcr1 hdab2ne
    have h2a : (2 : ℝ) • (dab2 A₀ B₀ C₀ A₁ B₁ C₁ sig •
          (C₀ - ptA A₀ B₀ C₀ A₁ B₁ C₁ sig)) =
        (2 : ℝ) • (esqA1 A₀ B₀ C₀ A₁ B₁ C₁ sig •
          (cenB A₀ B₀ C₀ A₁ B₁ C₁ sig - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig)) :=
      congrArg (fun v : Pt => (2 : ℝ) • v) h1
    rw [show (2 : ℝ) • (dab2 A₀ B₀ C₀ A₁ B₁ C₁ sig •
          (C₀ - ptA A₀ B₀ C₀ A₁ B₁ C₁ sig)) =
        (2 * dab2 A₀ B₀ C₀ A₁ B₁ C₁ sig) • (C₀ - ptA A₀ B₀ C₀ A₁ B₁ C₁ sig) from by
        module] at h2a
    rw [show (2 : ℝ) • (esqA1 A₀ B₀ C₀ A₁ B₁ C₁ sig •
          (cenB A₀ B₀ C₀ A₁ B₁ C₁ sig - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig)) =
        esqA1 A₀ B₀ C₀ A₁ B₁ C₁ sig •
          (ptB A₀ B₀ C₀ A₁ B₁ C₁ sig - ptA A₀ B₀ C₀ A₁ B₁ C₁ sig) from by
        rw [hsubAB]
        module] at h2a
    exact h2a
  have hB2d : (2 * dbc2 A₀ B₀ C₀ A₁ B₁ C₁ sig) •
        (A₀ - ptB A₀ B₀ C₀ A₁ B₁ C₁ sig) =
      esqB1 A₀ B₀ C₀ A₁ B₁ C₁ sig •
        (ptC A₀ B₀ C₀ A₁ B₁ C₁ sig - ptB A₀ B₀ C₀ A₁ B₁ C₁ sig) := by
    have h1 := A₀_sub_ptB A₀ B₀ C₀ A₁ B₁ C₁ sig hsig hcr1 hdab2ne
    have h2a : (2 : ℝ) • (dbc2 A₀ B₀ C₀ A₁ B₁ C₁ sig •
          (A₀ - ptB A₀ B₀ C₀ A₁ B₁ C₁ sig)) =
        (2 : ℝ) • (esqB1 A₀ B₀ C₀ A₁ B₁ C₁ sig •
          (cenC A₀ B₀ C₀ A₁ B₁ C₁ sig - cenB A₀ B₀ C₀ A₁ B₁ C₁ sig)) :=
      congrArg (fun v : Pt => (2 : ℝ) • v) h1
    rw [show (2 : ℝ) • (dbc2 A₀ B₀ C₀ A₁ B₁ C₁ sig •
          (A₀ - ptB A₀ B₀ C₀ A₁ B₁ C₁ sig)) =
        (2 * dbc2 A₀ B₀ C₀ A₁ B₁ C₁ sig) • (A₀ - ptB A₀ B₀ C₀ A₁ B₁ C₁ sig) from by
        module] at h2a
    rw [show (2 : ℝ) • (esqB1 A₀ B₀ C₀ A₁ B₁ C₁ sig •
          (cenC A₀ B₀ C₀ A₁ B₁ C₁ sig - cenB A₀ B₀ C₀ A₁ B₁ C₁ sig)) =
        esqB1 A₀ B₀ C₀ A₁ B₁ C₁ sig •
          (ptC A₀ B₀ C₀ A₁ B₁ C₁ sig - ptB A₀ B₀ C₀ A₁ B₁ C₁ sig) from by
        rw [hsubBC]
        module] at h2a
    exact h2a
  have hC2d : (2 * dca2 A₀ B₀ C₀ A₁ B₁ C₁ sig) •
        (B₀ - ptC A₀ B₀ C₀ A₁ B₁ C₁ sig) =
      esqC1 A₀ B₀ C₀ A₁ B₁ C₁ sig •
        (ptA A₀ B₀ C₀ A₁ B₁ C₁ sig - ptC A₀ B₀ C₀ A₁ B₁ C₁ sig) := by
    have h1 := B₀_sub_ptC A₀ B₀ C₀ A₁ B₁ C₁ sig hsig hcr1 hdab2ne
    have h2a : (2 : ℝ) • (dca2 A₀ B₀ C₀ A₁ B₁ C₁ sig •
          (B₀ - ptC A₀ B₀ C₀ A₁ B₁ C₁ sig)) =
        (2 : ℝ) • (esqC1 A₀ B₀ C₀ A₁ B₁ C₁ sig •
          (cenA A₀ B₀ C₀ A₁ B₁ C₁ sig - cenC A₀ B₀ C₀ A₁ B₁ C₁ sig)) :=
      congrArg (fun v : Pt => (2 : ℝ) • v) h1
    rw [show (2 : ℝ) • (dca2 A₀ B₀ C₀ A₁ B₁ C₁ sig •
          (B₀ - ptC A₀ B₀ C₀ A₁ B₁ C₁ sig)) =
        (2 * dca2 A₀ B₀ C₀ A₁ B₁ C₁ sig) • (B₀ - ptC A₀ B₀ C₀ A₁ B₁ C₁ sig) from by
        module] at h2a
    rw [show (2 : ℝ) • (esqC1 A₀ B₀ C₀ A₁ B₁ C₁ sig •
          (cenA A₀ B₀ C₀ A₁ B₁ C₁ sig - cenC A₀ B₀ C₀ A₁ B₁ C₁ sig)) =
        esqC1 A₀ B₀ C₀ A₁ B₁ C₁ sig •
          (ptA A₀ B₀ C₀ A₁ B₁ C₁ sig - ptC A₀ B₀ C₀ A₁ B₁ C₁ sig) from by
        rw [hsubCA]
        module] at h2a
    exact h2a
  have hcirc : Circumscribed A₀ B₀ C₀ (ptA A₀ B₀ C₀ A₁ B₁ C₁ sig)
      (ptB A₀ B₀ C₀ A₁ B₁ C₁ sig) (ptC A₀ B₀ C₀ A₁ B₁ C₁ sig) :=
    ⟨sbtw_of_smul hdbc2 heB1 heB2 hsumB hB2d hneBC,
      sbtw_of_smul hdca2 heC1 heC2 hsumC hC2d hneCA,
      sbtw_of_smul hdab2 heA1 heA2 hsumA hA2d hneAB⟩
  -- the area of the constructed triangle
  have harea : area (ptA A₀ B₀ C₀ A₁ B₁ C₁ sig) (ptB A₀ B₀ C₀ A₁ B₁ C₁ sig)
      (ptC A₀ B₀ C₀ A₁ B₁ C₁ sig) = maxArea A₀ B₀ C₀ A₁ B₁ C₁ := by
    have h4c : (4 : ℝ) * vcr (B₁ - A₁) (C₁ - A₁) ≠ 0 := mul_ne_zero (by norm_num) hcr1
    have hvc : vcr (cenB A₀ B₀ C₀ A₁ B₁ C₁ sig - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig)
          (cenC A₀ B₀ C₀ A₁ B₁ C₁ sig - cenA A₀ B₀ C₀ A₁ B₁ C₁ sig) =
        sig * kval A₀ B₀ C₀ A₁ B₁ C₁ sig / (4 * vcr (B₁ - A₁) (C₁ - A₁)) := by
      rw [eq_div_iff h4c]
      have hd := vcr_cen_eq A₀ B₀ C₀ A₁ B₁ C₁ sig hsig hcr1
      linear_combination hd
    have hsgabs : |sig| = 1 := by
      rcases hsig with h | h <;> simp [h]
    have hkabs : |kval A₀ B₀ C₀ A₁ B₁ C₁ sig| = kval A₀ B₀ C₀ A₁ B₁ C₁ sig :=
      abs_of_pos hK
    have e1 : (2 : ℝ) * (2 * (sig * kval A₀ B₀ C₀ A₁ B₁ C₁ sig /
        (4 * vcr (B₁ - A₁) (C₁ - A₁)))) =
        sig * kval A₀ B₀ C₀ A₁ B₁ C₁ sig / vcr (B₁ - A₁) (C₁ - A₁) := by
      field_simp [hcr1]
      ring
    rw [area, hsubAB, hsubAC, vcr_smul_left, vcr_smul_right, hvc, hmax, e1,
      abs_div, abs_mul, hsgabs, hkabs, one_mul, div_div,
      mul_comm |vcr (B₁ - A₁) (C₁ - A₁)| 2]
  exact ⟨ptA A₀ B₀ C₀ A₁ B₁ C₁ sig, ptB A₀ B₀ C₀ A₁ B₁ C₁ sig,
    ptC A₀ B₀ C₀ A₁ B₁ C₁ sig, hsim, hcirc, harea.symm⟩

snip end

problem imo1967_p4
    (A₀ B₀ C₀ A₁ B₁ C₁ : Pt)
    (hA₀ : ∠ B₀ A₀ C₀ ∈ Set.Ioo 0 (Real.pi / 2))
    (hB₀ : ∠ A₀ B₀ C₀ ∈ Set.Ioo 0 (Real.pi / 2))
    (hC₀ : ∠ B₀ C₀ A₀ ∈ Set.Ioo 0 (Real.pi / 2))
    (hA₁ : ∠ B₁ A₁ C₁ ∈ Set.Ioo 0 (Real.pi / 2))
    (hB₁ : ∠ A₁ B₁ C₁ ∈ Set.Ioo 0 (Real.pi / 2))
    (hC₁ : ∠ B₁ C₁ A₁ ∈ Set.Ioo 0 (Real.pi / 2)) :
    IsGreatest
      {x : ℝ | ∃ A B C : Pt, Similar A B C A₁ B₁ C₁ ∧
        Circumscribed A₀ B₀ C₀ A B C ∧ x = area A B C}
      (maxArea A₀ B₀ C₀ A₁ B₁ C₁) := by
  -- the acute angles give positive vertex dot products and nonzero areas
  have hpA : 0 < vdot (B₀ - A₀) (C₀ - A₀) := acute_dot hA₀
  have hpB : 0 < vdot (A₀ - B₀) (C₀ - B₀) := acute_dot hB₀
  have hpC : 0 < vdot (A₀ - C₀) (B₀ - C₀) := by
    have h := acute_dot hC₀
    rwa [vdot_comm] at h
  have hqA : 0 < vdot (B₁ - A₁) (C₁ - A₁) := acute_dot hA₁
  have hqB : 0 < vdot (A₁ - B₁) (C₁ - B₁) := acute_dot hB₁
  have hqC : 0 < vdot (A₁ - C₁) (B₁ - C₁) := by
    have h := acute_dot hC₁
    rwa [vdot_comm] at h
  have hcr0 : vcr (B₀ - A₀) (C₀ - A₀) ≠ 0 := acute_vcr_ne hA₀
  have hcr1 : vcr (B₁ - A₁) (C₁ - A₁) ≠ 0 := acute_vcr_ne hA₁
  refine ⟨?_, ?_⟩
  · -- the maximal triangle exists, by the explicit construction
    obtain ⟨A, B, C, hsim, hcirc, harea⟩ :=
      construction_mem A₀ B₀ C₀ A₁ B₁ C₁ hpA hpB hpC hqA hqB hqC hcr0 hcr1
    exact ⟨A, B, C, hsim, hcirc, harea⟩
  · -- no admissible triangle has a larger area
    intro x hx
    obtain ⟨A, B, C, hsim, hcirc, rfl⟩ := hx
    exact upper_bound A₀ B₀ C₀ A₁ B₁ C₁ hpA hpB hpC hqA hqB hqC hcr0 hcr1 hsim hcirc

end Imo1967P4
