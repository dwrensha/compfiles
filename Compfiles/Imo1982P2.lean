/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Geometry]
  solutionImportedFrom := "https://prase.cz/kalva/imo/isoln/isoln822.html"
}

/-!
# International Mathematical Olympiad 1982, Problem 2

A non-isosceles triangle A₁A₂A₃ has sides a₁, a₂, a₃ with aᵢ opposite Aᵢ.
Mᵢ is the midpoint of side aᵢ and Tᵢ is the point where the incircle touches
side aᵢ. Denote by Sᵢ the reflection of Tᵢ in the interior bisector of ∠Aᵢ.
Prove that the lines M₁S₁, M₂S₂ and M₃S₃ are concurrent.

# Formal statement

The plane is coordinatized as `Point := Fin 2 → ℝ`. Concurrency of lines is
preserved by similarities of the plane, so we may place the incircle as the unit
circle centered at `O = (0, 0)` with `T₁ = (1, 0)`, and with the touchpoints in
counterclockwise order. Write `B := ∠A₂`, `C := ∠A₃`, and set
`u := tan (B/2) > 0`, `v := tan (C/2) > 0`. The condition `∠A₁ > 0` becomes
`u * v < 1`, and since `tan (∠A₁/2) = (1 - u * v)/(u + v)`, the triangle being
non-isosceles becomes `u ≠ v` (i.e. `∠A₂ ≠ ∠A₃`), `u ^ 2 + 2 * u * v ≠ 1`
(i.e. `∠A₁ ≠ ∠A₂`) and `v ^ 2 + 2 * u * v ≠ 1` (i.e. `∠A₁ ≠ ∠A₃`).

Since `OTᵢ` is perpendicular to the side containing `Tᵢ`, the quadrilateral at
each vertex gives `∠T₁OT₂ = π - C`, `∠T₂OT₃ = π - ∠A₁` and `∠T₃OT₁ = π - B`,
so with `T₁` at angle `0` the counterclockwise positions are: `T₂` at angle
`π - C` and `T₃` at angle `π + B`. With `cos B = (1 - u²)/(1 + u²)`,
`sin B = 2u/(1 + u²)` etc. this gives
`T₂ = (-cos C, sin C) = ((v² - 1)/(v² + 1), 2v/(v² + 1))` and
`T₃ = (-cos B, -sin B) = ((u² - 1)/(u² + 1), -2u/(u² + 1))`.
Each side of the triangle is the tangent line to the unit incircle at the
corresponding `Tᵢ` (the tangent at `(x₀, y₀)` is `x * x₀ + y * y₀ = 1`);
intersecting these tangents gives
`A₂ = (1, -1/u)`, `A₃ = (1, 1/v)` and
`A₁ = ((1 + u * v)/(u * v - 1), (u - v)/(u * v - 1))`.
The interior bisector of `∠Aᵢ` is the line `OAᵢ`, so `Sᵢ` is the reflection of
`Tᵢ` in the line through the origin spanned by `Aᵢ` (formula
`S = 2 * ⟨T, d⟩/⟨d, d⟩ • d - T` for the reflection of `T` in the line spanned
by `d`), and `Mᵢ = (Aⱼ + Aₖ)/2`.

The conclusion "the lines M₁S₁, M₂S₂, M₃S₃ are concurrent" is formalized as
"there exists a point `P` collinear with `Mᵢ` and `Sᵢ` for `i = 1, 2, 3`",
where collinearity of three points is the vanishing of the scalar cross
product `cr`.

# Solution

Following https://prase.cz/kalva/imo/isoln/isoln822.html one shows that
`S₂S₃ ∥ A₂A₃` etc., so the triangles `S₁S₂S₃` and `M₁M₂M₃` are homothetic and
the lines through corresponding vertices concur at the homothety center.
Computing that center explicitly gives
`P = ((3uv - u + v - 1)(3uv + u - v - 1)/D, 2(u - v)(3uv - 1)/D)` with
`D = 9u²v² + u² - 8uv + v² + 1`, which is strictly positive when `u ≠ v`
because `D * (9v² + 1) = ((9v² + 1)u - 4v)² + (3v² - 1)²` is a sum of squares
that can only vanish when `u = v`. The three collinearities are then rational
identities in `u` and `v`, verified by `field_simp` and `ring`.
-/

namespace Imo1982P2

/-- The Euclidean plane, coordinatized as `ℝ²`. -/
abbrev Point := Fin 2 → ℝ

/-- The scalar cross product (determinant) of two plane vectors; twice the
signed area of the triangle they span. -/
def cr (u v : Point) : ℝ := u 0 * v 1 - u 1 * v 0

/-- Three points of the plane are collinear: the scalar-cross-product
criterion (also correct in the degenerate case of coinciding points). -/
def Coll (X Y Z : Point) : Prop := cr (Y - X) (Z - X) = 0

/-- The vertex `A₁` of the triangle (intersection of the tangents at `T₂`
and `T₃`). -/
noncomputable def A1 (u v : ℝ) : Point := ![(1 + u * v)/(u * v - 1), (u - v)/(u * v - 1)]

/-- The vertex `A₂` of the triangle (intersection of the tangents at `T₁`
and `T₃`). -/
noncomputable def A2 (u : ℝ) : Point := ![1, -1/u]

/-- The vertex `A₃` of the triangle (intersection of the tangents at `T₁`
and `T₂`). -/
noncomputable def A3 (v : ℝ) : Point := ![1, 1/v]

/-- The touchpoint `T₁` of the incircle with the side `a₁ = A₂A₃`. -/
def T1 : Point := ![1, 0]

/-- The touchpoint `T₂` of the incircle with the side `a₂ = A₁A₃`:
the point `(-cos C, sin C)` of the unit circle. -/
noncomputable def T2 (v : ℝ) : Point := ![(v ^ 2 - 1)/(v ^ 2 + 1), 2 * v/(v ^ 2 + 1)]

/-- The touchpoint `T₃` of the incircle with the side `a₃ = A₁A₂`:
the point `(-cos B, -sin B)` of the unit circle. -/
noncomputable def T3 (u : ℝ) : Point := ![(u ^ 2 - 1)/(u ^ 2 + 1), -2 * u/(u ^ 2 + 1)]

/-- The reflection of the point `Q` in the line through the origin spanned
by the vector `d ≠ 0`. -/
noncomputable def reflLine (d Q : Point) : Point :=
  (2 * (Q 0 * d 0 + Q 1 * d 1)/(d 0 ^ 2 + d 1 ^ 2)) • d - Q

/-- The midpoint `M₁` of the side `a₁ = A₂A₃`. -/
noncomputable def M1 (u v : ℝ) : Point := (1/2 : ℝ) • (A2 u + A3 v)

/-- The midpoint `M₂` of the side `a₂ = A₁A₃`. -/
noncomputable def M2 (u v : ℝ) : Point := (1/2 : ℝ) • (A1 u v + A3 v)

/-- The midpoint `M₃` of the side `a₃ = A₁A₂`. -/
noncomputable def M3 (u v : ℝ) : Point := (1/2 : ℝ) • (A1 u v + A2 u)

/-- The reflection `S₁` of `T₁` in the interior bisector of `∠A₁`
(the line `OA₁`). -/
noncomputable def S1 (u v : ℝ) : Point := reflLine (A1 u v) T1

/-- The reflection `S₂` of `T₂` in the interior bisector of `∠A₂`
(the line `OA₂`). -/
noncomputable def S2 (u v : ℝ) : Point := reflLine (A2 u) (T2 v)

/-- The reflection `S₃` of `T₃` in the interior bisector of `∠A₃`
(the line `OA₃`). -/
noncomputable def S3 (u v : ℝ) : Point := reflLine (A3 v) (T3 u)

snip begin

/-- The midpoint `M₁` in coordinates. -/
lemma m1_eq (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    M1 u v = ![1, (u - v)/(2 * u * v)] := by
  funext i
  fin_cases i <;> simp only [M1, A2, A3, smul_eq_mul, Pi.add_apply, Pi.smul_apply,
    Fin.isValue, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  · field_simp
    ring
  · field_simp
    ring

/-- The midpoint `M₂` in coordinates. -/
lemma m2_eq (u v : ℝ) (hv : 0 < v) (huv : u * v - 1 ≠ 0) :
    M2 u v = ![u * v/(u * v - 1), (2 * u * v - v ^ 2 - 1)/(2 * v * (u * v - 1))] := by
  funext i
  fin_cases i <;> simp only [M2, A1, A3, smul_eq_mul, Pi.add_apply, Pi.smul_apply,
    Fin.isValue, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  · field_simp
    ring
  · field_simp
    ring

/-- The midpoint `M₃` in coordinates. -/
lemma m3_eq (u v : ℝ) (hu : 0 < u) (huv : u * v - 1 ≠ 0) :
    M3 u v = ![u * v/(u * v - 1), (u ^ 2 - 2 * u * v + 1)/(2 * u * (u * v - 1))] := by
  funext i
  fin_cases i <;> simp only [M3, A1, A2, smul_eq_mul, Pi.add_apply, Pi.smul_apply,
    Fin.isValue, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  · field_simp
    ring
  · field_simp
    ring

/-- The reflection `S₁` in coordinates. -/
lemma s1_eq (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (huv : u * v - 1 ≠ 0) :
    S1 u v = ![(u * v - u + v + 1) * (u * v + u - v + 1)/((u ^ 2 + 1) * (v ^ 2 + 1)),
              2 * (u - v) * (u * v + 1)/((u ^ 2 + 1) * (v ^ 2 + 1))] := by
  have hN : (0:ℝ) < (1 + u * v) ^ 2 + (u - v) ^ 2 := by positivity
  have hA1 : ((1 + u * v)/(u * v - 1)) ^ 2 + ((u - v)/(u * v - 1)) ^ 2 ≠ 0 := by
    rw [div_pow, div_pow, ← add_div]
    exact div_ne_zero hN.ne' (pow_ne_zero 2 huv)
  funext i
  fin_cases i <;> simp only [S1, reflLine, T1, A1, smul_eq_mul, Pi.sub_apply,
    Pi.smul_apply, Fin.isValue, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul, zero_mul, add_zero]
  · field_simp
    ring
  · field_simp
    ring

/-- The reflection `S₂` in coordinates. -/
lemma s2_eq (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    S2 u v = ![(u * v - u - v - 1) * (u * v + u + v - 1)/((u ^ 2 + 1) * (v ^ 2 + 1)),
              -2 * (u + v) * (u * v - 1)/((u ^ 2 + 1) * (v ^ 2 + 1))] := by
  have hA2 : (1:ℝ) ^ 2 + (-1/u) ^ 2 ≠ 0 := by positivity
  have hv2 : v ^ 2 + 1 ≠ 0 := (by positivity : (0:ℝ) < v ^ 2 + 1).ne'
  have hu2v2 : (u ^ 2 + 1) * (v ^ 2 + 1) ≠ 0 :=
    mul_ne_zero (by positivity : (0:ℝ) < u ^ 2 + 1).ne' hv2
  funext i
  fin_cases i <;> simp only [S2, reflLine, T2, A2, smul_eq_mul, Pi.sub_apply,
    Pi.smul_apply, Fin.isValue, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  · field_simp
    ring
  · field_simp
    ring

/-- The reflection `S₃` in coordinates. -/
lemma s3_eq (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    S3 u v = ![(u * v - u - v - 1) * (u * v + u + v - 1)/((u ^ 2 + 1) * (v ^ 2 + 1)),
              2 * (u + v) * (u * v - 1)/((u ^ 2 + 1) * (v ^ 2 + 1))] := by
  have hA3 : (1:ℝ) ^ 2 + (1/v) ^ 2 ≠ 0 := by positivity
  have hu2 : u ^ 2 + 1 ≠ 0 := (by positivity : (0:ℝ) < u ^ 2 + 1).ne'
  have hu2v2 : (u ^ 2 + 1) * (v ^ 2 + 1) ≠ 0 :=
    mul_ne_zero hu2 (by positivity : (0:ℝ) < v ^ 2 + 1).ne'
  funext i
  fin_cases i <;> simp only [S3, reflLine, T3, A3, smul_eq_mul, Pi.sub_apply,
    Pi.smul_apply, Fin.isValue, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  · field_simp
    ring
  · field_simp
    ring

/-- The common denominator `D = 9u²v² + u² - 8uv + v² + 1` of the coordinates of
the concurrency point. -/
noncomputable def dNom (u v : ℝ) : ℝ := 9 * u ^ 2 * v ^ 2 + u ^ 2 - 8 * u * v + v ^ 2 + 1

/-- The denominator of the concurrency point is strictly positive when
`u ≠ v`: `D * (9v² + 1)` is a sum of two squares that can only vanish together
when `u = v`. -/
lemma Dpos (u v : ℝ) (hne : u ≠ v) : 0 < dNom u v := by
  have key : dNom u v * (9 * v ^ 2 + 1) =
      ((9 * v ^ 2 + 1) * u - 4 * v) ^ 2 + (3 * v ^ 2 - 1) ^ 2 := by
    simp only [dNom]
    ring
  have hsq : 0 < ((9 * v ^ 2 + 1) * u - 4 * v) ^ 2 + (3 * v ^ 2 - 1) ^ 2 := by
    by_cases h1 : (9 * v ^ 2 + 1) * u - 4 * v = 0
    · have h3 : 3 * v ^ 2 - 1 ≠ 0 := by
        intro h3
        have hv2 : v ^ 2 = 1/3 := by linarith [h3]
        have h9 : 9 * v ^ 2 + 1 = 4 := by linarith [hv2]
        rw [h9] at h1
        exact hne (by linarith [h1])
      have p1 := sq_nonneg ((9 * v ^ 2 + 1) * u - 4 * v)
      have p2 := sq_pos_of_ne_zero h3
      linarith [p1, p2]
    · have p1 := sq_pos_of_ne_zero h1
      have p2 := sq_nonneg (3 * v ^ 2 - 1)
      linarith [p1, p2]
  have hw : (0:ℝ) < 9 * v ^ 2 + 1 := by positivity
  by_contra hD
  push Not at hD
  have hle := mul_nonpos_of_nonpos_of_nonneg hD hw.le
  linarith [key, hsq, hle]

/-- The candidate for the concurrency point: the center of the homothety
taking the triangle `S₁S₂S₃` to the medial triangle `M₁M₂M₃`. -/
noncomputable def Pcand (u v : ℝ) : Point :=
  ![((3 * u * v - u + v - 1) * (3 * u * v + u - v - 1))/(dNom u v),
    2 * (u - v) * (3 * u * v - 1)/(dNom u v)]

/-- `Pcand` is collinear with `M₁` and `S₁`. -/
lemma cr1 (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (huv : u * v - 1 ≠ 0)
    (hD : dNom u v ≠ 0) :
    cr (S1 u v - M1 u v) (Pcand u v - M1 u v) = 0 := by
  have hu2v2 : (u ^ 2 + 1) * (v ^ 2 + 1) ≠ 0 :=
    mul_ne_zero (by positivity : (0:ℝ) < u ^ 2 + 1).ne'
      (by positivity : (0:ℝ) < v ^ 2 + 1).ne'
  have h2uv : 2 * u * v ≠ 0 := (by positivity : (0:ℝ) < 2 * u * v).ne'
  rw [s1_eq u v hu hv huv, m1_eq u v hu hv]
  simp only [Pcand, cr, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  simp only [dNom]
  ring

/-- `Pcand` is collinear with `M₂` and `S₂`. -/
lemma cr2 (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (huv : u * v - 1 ≠ 0)
    (hD : dNom u v ≠ 0) :
    cr (S2 u v - M2 u v) (Pcand u v - M2 u v) = 0 := by
  have hu2v2 : (u ^ 2 + 1) * (v ^ 2 + 1) ≠ 0 :=
    mul_ne_zero (by positivity : (0:ℝ) < u ^ 2 + 1).ne'
      (by positivity : (0:ℝ) < v ^ 2 + 1).ne'
  have h2vu : 2 * v * (u * v - 1) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hv.ne') huv
  rw [s2_eq u v hu hv, m2_eq u v hv huv]
  simp only [Pcand, cr, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  simp only [dNom]
  ring

/-- `Pcand` is collinear with `M₃` and `S₃`. -/
lemma cr3 (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (huv : u * v - 1 ≠ 0)
    (hD : dNom u v ≠ 0) :
    cr (S3 u v - M3 u v) (Pcand u v - M3 u v) = 0 := by
  have hu2v2 : (u ^ 2 + 1) * (v ^ 2 + 1) ≠ 0 :=
    mul_ne_zero (by positivity : (0:ℝ) < u ^ 2 + 1).ne'
      (by positivity : (0:ℝ) < v ^ 2 + 1).ne'
  have h2uu : 2 * u * (u * v - 1) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hu.ne') huv
  rw [s3_eq u v hu hv, m3_eq u v hu huv]
  simp only [Pcand, cr, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  simp only [dNom]
  ring

snip end

problem imo1982_p2 (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (huv : u * v < 1)
    (hBC : u ≠ v) (_hAB : u ^ 2 + 2 * u * v ≠ 1) (_hAC : v ^ 2 + 2 * u * v ≠ 1) :
    ∃ P : Point, Coll (M1 u v) (S1 u v) P ∧ Coll (M2 u v) (S2 u v) P ∧
      Coll (M3 u v) (S3 u v) P := by
  have huv1 : u * v - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_lt huv)
  have hD : dNom u v ≠ 0 := (Dpos u v hBC).ne'
  exact ⟨Pcand u v, cr1 u v hu hv huv1 hD, cr2 u v hu hv huv1 hD, cr3 u v hu hv huv1 hD⟩

end Imo1982P2
