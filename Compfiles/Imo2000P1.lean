/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 2000, Problem 1

Two circles G₁ and G₂ intersect at two points M and N. Let AB be the line
tangent to these circles at A and B, respectively, so that M lies closer to
AB than N. Let CD be the line parallel to AB and passing through the point M,
with C on G₁ and D on G₂. Lines AC and BD meet at E; lines AN and CD meet at P;
lines BN and CD meet at Q. Prove that EP = EQ.

-/

namespace Imo2000P1

open scoped RealInnerProductSpace

/-- The Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- The tangency point `A` of the first circle with the common tangent line. -/
def ptA (a : ℝ) : Pt := !₂[a, 1]

/-- The tangency point `B` of the second circle with the common tangent line. -/
def ptB (b : ℝ) : Pt := !₂[b, 1]

/-- The common point `M` of the two circles, placed at the origin. -/
def ptM : Pt := !₂[0, 0]

/-- `C` is the second intersection of the first circle with the `x`-axis. -/
def ptC (a : ℝ) : Pt := !₂[2 * a, 0]

/-- `D` is the second intersection of the second circle with the `x`-axis. -/
def ptD (b : ℝ) : Pt := !₂[2 * b, 0]

/-- `N` is the second intersection point of the two circles. -/
noncomputable def ptN (a b : ℝ) : Pt :=
  !₂[2 * (a + b) * (1 + a * b) / (4 + (a + b)^2), 4 * (1 + a * b) / (4 + (a + b)^2)]

/-- The center of the first circle (through `C`, `A`, `M`, `N`). -/
noncomputable def center₁ (a : ℝ) : Pt := !₂[a, (1 - a^2) / 2]

/-- The center of the second circle (through `D`, `B`, `M`, `N`). -/
noncomputable def center₂ (b : ℝ) : Pt := !₂[b, (1 - b^2) / 2]

/-- The radius of a circle tangent to the line `y = 1` at `(x, 1)` and
passing through the origin. -/
noncomputable def radius (x : ℝ) : ℝ := (1 + x^2) / 2

snip begin

lemma dist2 (x1 y1 x2 y2 : ℝ) :
    dist (!₂[x1, y1] : Pt) !₂[x2, y2]
      = Real.sqrt ((x1 - x2)^2 + (y1 - y2)^2) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.dist_eq, sq_abs]

lemma pt_eq (x : Pt) : x = !₂[x 0, x 1] := by
  ext i; fin_cases i <;> simp

lemma inner_pt (n x : Pt) : ⟪n, x⟫ = n 0 * x 0 + n 1 * x 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, RCLike.inner_apply]
  simp only [conj_trivial]
  ring

/-- The four points `C`, `A`, `M`, `N` are concyclic: they all lie on the
circle with center `center₁ a` and radius `radius a`. -/
lemma concyclic₁ (a b : ℝ) :
    dist (center₁ a) (ptC a) = radius a ∧
    dist (center₁ a) (ptA a) = radius a ∧
    dist (center₁ a) ptM = radius a ∧
    dist (center₁ a) (ptN a b) = radius a := by
  have hD : (4:ℝ) + (a + b)^2 ≠ 0 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [center₁, ptC, ptA, ptM, ptN, radius, dist2] <;>
    rw [Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)] <;>
    field_simp <;>
    ring

/-- The four points `D`, `B`, `M`, `N` are concyclic: they all lie on the
circle with center `center₂ b` and radius `radius b`. -/
lemma concyclic₂ (a b : ℝ) :
    dist (center₂ b) (ptD b) = radius b ∧
    dist (center₂ b) (ptB b) = radius b ∧
    dist (center₂ b) ptM = radius b ∧
    dist (center₂ b) (ptN a b) = radius b := by
  have hD : (4:ℝ) + (a + b)^2 ≠ 0 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [center₂, ptD, ptB, ptM, ptN, radius, dist2] <;>
    rw [Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)] <;>
    field_simp <;>
    ring

/-- The line `AB` is tangent to the first circle at `A`: the radius to `A`
is perpendicular to `AB`. -/
lemma tangent₁ (a b : ℝ) : ⟪ptA a - center₁ a, ptB b - ptA a⟫ = 0 := by
  rw [inner_pt]
  simp only [ptA, ptB, center₁, PiLp.sub_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

/-- The line `AB` is tangent to the second circle at `B`: the radius to `B`
is perpendicular to `AB`. -/
lemma tangent₂ (a b : ℝ) : ⟪ptB b - center₂ b, ptA a - ptB b⟫ = 0 := by
  rw [inner_pt]
  simp only [ptB, ptA, center₂, PiLp.sub_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

/-- `N ≠ M` as long as the two circles are not tangent to each other at `M`. -/
lemma ptN_ne_ptM {a b : ℝ} (h : 1 + a * b ≠ 0) : ptN a b ≠ ptM := by
  intro hn
  have h1 := congr_arg (fun x : Pt => x 1) hn
  have hD : (4:ℝ) + (a + b)^2 ≠ 0 := by positivity
  simp only [ptN, ptM, Matrix.cons_val_one, Matrix.cons_val_zero] at h1
  field_simp at h1
  apply h
  linarith

lemma ptN_y_sub_one (a b : ℝ) :
    ptN a b 1 - 1 = -((a - b)^2 / (4 + (a + b)^2)) := by
  have hD : (4:ℝ) + (a + b)^2 ≠ 0 := by positivity
  simp only [ptN, Matrix.cons_val_one, Matrix.cons_val_zero]
  field_simp
  ring

lemma ptN_x_sub_a (a b : ℝ) :
    ptN a b 0 - a = -((a - b) * (a^2 + a * b + 2) / (4 + (a + b)^2)) := by
  have hD : (4:ℝ) + (a + b)^2 ≠ 0 := by positivity
  simp only [ptN, Matrix.cons_val_zero]
  field_simp
  ring

lemma ptN_x_sub_b (a b : ℝ) :
    ptN a b 0 - b = (a - b) * (a * b + b^2 + 2) / (4 + (a + b)^2) := by
  have hD : (4:ℝ) + (a + b)^2 ≠ 0 := by positivity
  simp only [ptN, Matrix.cons_val_zero]
  field_simp
  ring

snip end

problem imo2000_p1 (a b : ℝ) (hab : a ≠ b) (hcloser : 1 + a * b < 0)
    (E P Q : Pt)
    (hE₁ : ∃ t : ℝ, E = ptA a + t • (ptC a - ptA a))
    (hE₂ : ∃ t : ℝ, E = ptB b + t • (ptD b - ptB b))
    (hP₁ : ∃ t : ℝ, P = ptA a + t • (ptN a b - ptA a))
    (hP₂ : P 1 = 0)
    (hQ₁ : ∃ t : ℝ, Q = ptB b + t • (ptN a b - ptB b))
    (hQ₂ : Q 1 = 0) :
    dist E P = dist E Q := by
  -- The configuration is nondegenerate: `N ≠ M`.
  have _hNM : ptN a b ≠ ptM := ptN_ne_ptM (ne_of_lt hcloser)
  have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hD : (4:ℝ) + (a + b)^2 ≠ 0 := by positivity
  obtain ⟨t₁, ht₁⟩ := hE₁
  obtain ⟨t₂, ht₂⟩ := hE₂
  -- Comparing the `y`-coordinates of the two expressions for `E`.
  have hy : t₁ = t₂ := by
    have h1 := congr_arg (fun x : Pt => x 1) ht₁
    have h2 := congr_arg (fun x : Pt => x 1) ht₂
    simp only [ptA, ptB, ptC, ptD, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul] at h1 h2
    linarith
  -- Comparing the `x`-coordinates gives `t₁ = -1`, using `a ≠ b`.
  have ht : t₁ = -1 := by
    have h1 := congr_arg (fun x : Pt => x 0) ht₁
    have h2 := congr_arg (fun x : Pt => x 0) ht₂
    simp only [ptA, ptB, ptC, ptD, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
      Matrix.cons_val_zero, smul_eq_mul] at h1 h2
    rw [← hy] at h2
    have h : (a - b) * (1 + t₁) = 0 := by linear_combination h2 - h1
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hab'
    · linarith
  -- Hence `E = (0, 2)`: the reflection of `M` in the line `AB`.
  have hE : E = !₂[(0:ℝ), 2] := by
    rw [ht₁, ht]
    ext i; fin_cases i <;> simp [ptA, ptC] <;> ring
  obtain ⟨u₁, hu₁⟩ := hP₁
  obtain ⟨u₂, hu₂⟩ := hQ₁
  -- The parameter of `P` on the line `AN`, determined by `P 1 = 0`.
  have key₁ : u₁ * (a - b)^2 = 4 + (a + b)^2 := by
    have h1 := congr_arg (fun x : Pt => x 1) hu₁
    simp only [ptA, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul, hP₂] at h1
    rw [ptN_y_sub_one] at h1
    field_simp at h1
    linear_combination h1
  -- The parameter of `Q` on the line `BN`, determined by `Q 1 = 0`.
  have key₂ : u₂ * (a - b)^2 = 4 + (a + b)^2 := by
    have h1 := congr_arg (fun x : Pt => x 1) hu₂
    simp only [ptB, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul, hQ₂] at h1
    rw [ptN_y_sub_one] at h1
    field_simp at h1
    linear_combination h1
  -- The `x`-coordinate of `P`.
  have hP0 : P 0 = -2 * (1 + a * b) / (a - b) := by
    have h0 := congr_arg (fun x : Pt => x 0) hu₁
    simp only [ptA, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
      Matrix.cons_val_zero, smul_eq_mul] at h0
    rw [ptN_x_sub_a] at h0
    have hu₁v : u₁ = (4 + (a + b)^2) / (a - b)^2 := by
      rw [eq_div_iff (pow_ne_zero 2 hab')]
      exact key₁
    rw [h0, hu₁v]
    field_simp
    ring
  -- The `x`-coordinate of `Q`.
  have hQ0 : Q 0 = 2 * (1 + a * b) / (a - b) := by
    have h0 := congr_arg (fun x : Pt => x 0) hu₂
    simp only [ptB, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
      Matrix.cons_val_zero, smul_eq_mul] at h0
    rw [ptN_x_sub_b] at h0
    have hu₂v : u₂ = (4 + (a + b)^2) / (a - b)^2 := by
      rw [eq_div_iff (pow_ne_zero 2 hab')]
      exact key₂
    rw [h0, hu₂v]
    field_simp
    ring
  -- `M` is the midpoint of `PQ` and `E` is on its perpendicular bisector.
  have hP : P = !₂[-2 * (1 + a * b) / (a - b), (0:ℝ)] := by
    rw [pt_eq P, hP0, hP₂]
  have hQ : Q = !₂[2 * (1 + a * b) / (a - b), (0:ℝ)] := by
    rw [pt_eq Q, hQ0, hQ₂]
  rw [hE, hP, hQ]
  simp only [dist2]
  congr 1
  ring

end Imo2000P1
