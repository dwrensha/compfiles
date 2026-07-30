/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Real.Sqrt
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1988, Problem 5

ABC is a triangle, right-angled at A, and D is the foot of the altitude from A.
The straight line joining the incenters of the triangles ABD and ACD intersects
the sides AB, AC at K, L respectively. Show that the area of the triangle ABC
is at least twice the area of the triangle AKL.
-/

namespace Imo1988P5

open scoped InnerProductSpace

/-- The Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

snip begin

/-!
We solve the problem by coordinates.  Place the right angle at the origin:
`A = (0, 0)`, `B = (p, 0)`, `C = (0, q)`, where `p = AB > 0` and `q = AC > 0`.
The hypotenuse has length `√(p² + q²)` and the foot of the altitude from `A`
is `D = (p q²/(p²+q²), p² q/(p²+q²))`.
-/

/-- Vertex `A`, at the origin. -/
def vtxA : Plane := !₂[0, 0]

/-- Vertex `B = (p, 0)`, where `p = AB`. -/
def vtxB (p : ℝ) : Plane := !₂[p, 0]

/-- Vertex `C = (0, q)`, where `q = AC`. -/
def vtxC (q : ℝ) : Plane := !₂[0, q]

/-- The foot of the altitude from `A` to the hypotenuse `BC`. -/
noncomputable def footD (p q : ℝ) : Plane := !₂[p * q^2 / (p^2 + q^2), p^2 * q / (p^2 + q^2)]

/-- The incenter of a triangle with vertices `P₁`, `P₂`, `P₃`, expressed as the
average of the vertices weighted by the lengths of the opposite sides. -/
noncomputable def incenter (P₁ P₂ P₃ : Plane) : Plane :=
  (dist P₂ P₃ + dist P₃ P₁ + dist P₁ P₂)⁻¹ •
    (dist P₂ P₃ • P₁ + dist P₃ P₁ • P₂ + dist P₁ P₂ • P₃)

/-- The incenter of triangle `ABD`. -/
noncomputable def inc₁ (p q : ℝ) : Plane := incenter vtxA (vtxB p) (footD p q)

/-- The incenter of triangle `ACD`. -/
noncomputable def inc₂ (p q : ℝ) : Plane := incenter vtxA (vtxC q) (footD p q)

/-- The point where the line through `P₁` and `P₂` meets the x-axis
(degenerate when `P₁` and `P₂` have the same y-coordinate). -/
noncomputable def xInt (P₁ P₂ : Plane) : Plane := P₁ + (P₁ 1 / (P₁ 1 - P₂ 1)) • (P₂ - P₁)

/-- The point where the line through `P₁` and `P₂` meets the y-axis
(degenerate when `P₁` and `P₂` have the same x-coordinate). -/
noncomputable def yInt (P₁ P₂ : Plane) : Plane := P₁ + (P₁ 0 / (P₁ 0 - P₂ 0)) • (P₂ - P₁)

/-- `K`: the point where the line through the incenters of `ABD` and `ACD`
meets `AB`. -/
noncomputable def ptK (p q : ℝ) : Plane := xInt (inc₁ p q) (inc₂ p q)

/-- `L`: the point where the line through the incenters of `ABD` and `ACD`
meets `AC`. -/
noncomputable def ptL (p q : ℝ) : Plane := yInt (inc₁ p q) (inc₂ p q)

/-- The area of triangle `ABC`. -/
noncomputable def areaABC (p q : ℝ) : ℝ := p * q / 2

/-- The area of triangle `AKL`. -/
noncomputable def areaAKL (p q : ℝ) : ℝ := ptK p q 0 * ptL p q 1 / 2

/-- Two vectors are equal iff their coordinates are equal. -/
lemma vec_eq (x₁ y₁ x₂ y₂ : ℝ) :
    (!₂[x₁, y₁] : Plane) = !₂[x₂, y₂] ↔ x₁ = x₂ ∧ y₁ = y₂ := by simp

lemma coord_x (x y : ℝ) : (!₂[x, y] : Plane) 0 = x := by simp

lemma coord_y (x y : ℝ) : (!₂[x, y] : Plane) 1 = y := by simp

lemma vec_smul (s x y : ℝ) : s • (!₂[x, y] : Plane) = !₂[s * x, s * y] := by
  ext i; fin_cases i <;> simp

lemma vec_add (x₁ y₁ x₂ y₂ : ℝ) :
    (!₂[x₁, y₁] : Plane) + !₂[x₂, y₂] = !₂[x₁ + x₂, y₁ + y₂] := by
  ext i; fin_cases i <;> simp

lemma vec_sub (x₁ y₁ x₂ y₂ : ℝ) :
    (!₂[x₁, y₁] : Plane) - !₂[x₂, y₂] = !₂[x₁ - x₂, y₁ - y₂] := by
  ext i; fin_cases i <;> simp

/-- Distance between two points given by their coordinates. -/
lemma dist_pts (x₁ y₁ x₂ y₂ : ℝ) :
    dist (!₂[x₁, y₁] : Plane) (!₂[x₂, y₂]) = √((x₁ - x₂)^2 + (y₁ - y₂)^2) := by
  simp [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs]

/-- The foot `D`, rewritten with denominator `(√(p²+q²))² = p² + q²`. -/
lemma footD' (p q : ℝ) :
    footD p q = !₂[p * q^2 / (√(p^2+q^2))^2, p^2 * q / (√(p^2+q^2))^2] := by
  simp only [footD]
  rw [Real.sq_sqrt (by positivity)]

/-- `D` indeed lies on the line `BC`. -/
lemma footD_on_BC (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    footD p q = vtxB p + (p^2 / (p^2 + q^2)) • (vtxC q - vtxB p) := by
  have hX : (0:ℝ) < p^2 + q^2 := by positivity
  simp only [footD, vtxB, vtxC, vec_sub, vec_smul, vec_add]
  rw [vec_eq]
  constructor <;> field_simp [hX.ne'] <;> ring

/-- `AD` is indeed perpendicular to `BC`. -/
lemma footD_perp (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    ⟪footD p q - vtxA, vtxC q - vtxB p⟫_ℝ = 0 := by
  have hX : (0:ℝ) < p^2 + q^2 := by positivity
  simp only [footD, vtxA, vtxB, vtxC, vec_sub, PiLp.inner_apply, Fin.sum_univ_two,
    RCLike.inner_apply, starRingEnd_apply, star_trivial, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  field_simp [hX.ne']
  ring

lemma dist_AB (p : ℝ) (hp : 0 < p) : dist vtxA (vtxB p) = p := by
  simp only [vtxA, vtxB]
  rw [dist_pts]
  have e : (0 - p)^2 + (0 - 0)^2 = p^2 := by ring
  rw [e, Real.sqrt_sq hp.le]

lemma dist_AC (q : ℝ) (hq : 0 < q) : dist vtxA (vtxC q) = q := by
  simp only [vtxA, vtxC]
  rw [dist_pts]
  have e : (0 - 0)^2 + (0 - q)^2 = q^2 := by ring
  rw [e, Real.sqrt_sq hq.le]

lemma dist_BC (p q : ℝ) : dist (vtxB p) (vtxC q) = √(p^2 + q^2) := by
  simp only [vtxB, vtxC]
  rw [dist_pts]
  have e : (p - 0)^2 + (0 - q)^2 = p^2 + q^2 := by ring
  rw [e]

lemma dist_DA (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    dist (footD p q) vtxA = p * q / √(p^2 + q^2) := by
  have hX : (0:ℝ) < p^2 + q^2 := by positivity
  simp only [footD, vtxA]
  rw [dist_pts]
  have e : (p * q^2 / (p^2 + q^2) - 0)^2 + (p^2 * q / (p^2 + q^2) - 0)^2
      = (p * q / √(p^2 + q^2))^2 := by
    rw [div_pow, Real.sq_sqrt hX.le]
    field_simp [hX.ne']
    ring
  rw [e, Real.sqrt_sq (by positivity)]

lemma dist_BD (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    dist (vtxB p) (footD p q) = p^2 / √(p^2 + q^2) := by
  have hX : (0:ℝ) < p^2 + q^2 := by positivity
  simp only [vtxB, footD]
  rw [dist_pts]
  have e : (p - p * q^2 / (p^2 + q^2))^2 + (0 - p^2 * q / (p^2 + q^2))^2
      = (p^2 / √(p^2 + q^2))^2 := by
    rw [div_pow, Real.sq_sqrt hX.le]
    field_simp [hX.ne']
    ring
  rw [e, Real.sqrt_sq (by positivity)]

lemma dist_CD (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    dist (vtxC q) (footD p q) = q^2 / √(p^2 + q^2) := by
  have hX : (0:ℝ) < p^2 + q^2 := by positivity
  simp only [vtxC, footD]
  rw [dist_pts]
  have e : (0 - p * q^2 / (p^2 + q^2))^2 + (q - p^2 * q / (p^2 + q^2))^2
      = (q^2 / √(p^2 + q^2))^2 := by
    rw [div_pow, Real.sq_sqrt hX.le]
    field_simp [hX.ne']
    ring
  rw [e, Real.sqrt_sq (by positivity)]

/-- The incenter of `ABD`, explicitly. -/
lemma inc₁_eq (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    inc₁ p q = !₂[p * q * (√(p^2+q^2) + q) / (√(p^2+q^2) * (√(p^2+q^2) + p + q)),
                  p^2 * q / (√(p^2+q^2) * (√(p^2+q^2) + p + q))] := by
  have hapos : (0:ℝ) < √(p^2+q^2) := by positivity
  have hsum : (0:ℝ) < √(p^2+q^2) + p + q := by positivity
  have hW : (0:ℝ) < p^2 / √(p^2+q^2) + p * q / √(p^2+q^2) + p := by positivity
  simp only [inc₁, incenter, dist_BD p q hp hq, dist_DA p q hp hq, dist_AB p hp]
  simp only [vtxA, vtxB, footD', vec_smul, vec_add, mul_zero, add_zero, zero_add]
  rw [vec_eq]
  constructor
  · field_simp [hapos.ne', hsum.ne', hW.ne']
    ring
  · field_simp [hapos.ne', hsum.ne', hW.ne']
    ring

/-- The incenter of `ACD`, explicitly. -/
lemma inc₂_eq (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    inc₂ p q = !₂[p * q^2 / (√(p^2+q^2) * (√(p^2+q^2) + p + q)),
                  p * q * (√(p^2+q^2) + p) / (√(p^2+q^2) * (√(p^2+q^2) + p + q))] := by
  have hapos : (0:ℝ) < √(p^2+q^2) := by positivity
  have hsum : (0:ℝ) < √(p^2+q^2) + p + q := by positivity
  have hW : (0:ℝ) < q^2 / √(p^2+q^2) + p * q / √(p^2+q^2) + q := by positivity
  simp only [inc₂, incenter, dist_CD p q hp hq, dist_DA p q hp hq, dist_AC q hq]
  simp only [vtxA, vtxC, footD', vec_smul, vec_add, mul_zero, add_zero, zero_add]
  rw [vec_eq]
  constructor
  · field_simp [hapos.ne', hsum.ne', hW.ne']
    ring
  · field_simp [hapos.ne', hsum.ne', hW.ne']
    ring

/-- The parameter at which the line through the incenters meets the x-axis. -/
lemma paramK (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    inc₁ p q 1 / (inc₁ p q 1 - inc₂ p q 1) = -p / √(p^2+q^2) := by
  have hapos : (0:ℝ) < √(p^2+q^2) := by positivity
  have hsum : (0:ℝ) < √(p^2+q^2) + p + q := by positivity
  have h1 : inc₁ p q 1 = p^2 * q / (√(p^2+q^2) * (√(p^2+q^2) + p + q)) := by
    rw [inc₁_eq p q hp hq]; exact coord_y _ _
  have h2 : inc₂ p q 1 = p * q * (√(p^2+q^2) + p) / (√(p^2+q^2) * (√(p^2+q^2) + p + q)) := by
    rw [inc₂_eq p q hp hq]; exact coord_y _ _
  rw [h1, h2]
  have hne : p^2 * q / (√(p^2+q^2) * (√(p^2+q^2) + p + q)) -
      p * q * (√(p^2+q^2) + p) / (√(p^2+q^2) * (√(p^2+q^2) + p + q)) ≠ 0 := by
    have e : p^2 * q / (√(p^2+q^2) * (√(p^2+q^2) + p + q)) -
        p * q * (√(p^2+q^2) + p) / (√(p^2+q^2) * (√(p^2+q^2) + p + q))
        = -(p * q * √(p^2+q^2) / (√(p^2+q^2) * (√(p^2+q^2) + p + q))) := by
      field_simp [hapos.ne', hsum.ne']
      ring
    have hpos : (0:ℝ) < p * q * √(p^2+q^2) / (√(p^2+q^2) * (√(p^2+q^2) + p + q)) := by
      positivity
    rw [e]
    exact (neg_lt_zero.mpr hpos).ne
  field_simp [hapos.ne', hsum.ne', hne]
  ring

/-- The parameter at which the line through the incenters meets the y-axis. -/
lemma paramL (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    inc₁ p q 0 / (inc₁ p q 0 - inc₂ p q 0) = (√(p^2+q^2) + q) / √(p^2+q^2) := by
  have hapos : (0:ℝ) < √(p^2+q^2) := by positivity
  have hsum : (0:ℝ) < √(p^2+q^2) + p + q := by positivity
  have h1 : inc₁ p q 0 = p * q * (√(p^2+q^2) + q) / (√(p^2+q^2) * (√(p^2+q^2) + p + q)) := by
    rw [inc₁_eq p q hp hq]; exact coord_x _ _
  have h2 : inc₂ p q 0 = p * q^2 / (√(p^2+q^2) * (√(p^2+q^2) + p + q)) := by
    rw [inc₂_eq p q hp hq]; exact coord_x _ _
  rw [h1, h2]
  have hne : p * q * (√(p^2+q^2) + q) / (√(p^2+q^2) * (√(p^2+q^2) + p + q)) -
      p * q^2 / (√(p^2+q^2) * (√(p^2+q^2) + p + q)) ≠ 0 := by
    have e : p * q * (√(p^2+q^2) + q) / (√(p^2+q^2) * (√(p^2+q^2) + p + q)) -
        p * q^2 / (√(p^2+q^2) * (√(p^2+q^2) + p + q))
        = p * q * √(p^2+q^2) / (√(p^2+q^2) * (√(p^2+q^2) + p + q)) := by
      field_simp [hapos.ne', hsum.ne']
      ring
    have hpos : (0:ℝ) < p * q * √(p^2+q^2) / (√(p^2+q^2) * (√(p^2+q^2) + p + q)) := by
      positivity
    rw [e]
    exact hpos.ne'
  field_simp [hapos.ne', hsum.ne', hne]
  ring

/-- The key computation: `K = (pq / √(p²+q²), 0)`, so `K` lies on `AB` with
`AK = pq / √(p²+q²) = AD`. -/
lemma ptK_eq (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    ptK p q = !₂[p * q / √(p^2+q^2), 0] := by
  have hapos : (0:ℝ) < √(p^2+q^2) := by positivity
  have hsum : (0:ℝ) < √(p^2+q^2) + p + q := by positivity
  simp only [ptK, xInt]
  rw [paramK p q hp hq, inc₁_eq p q hp hq, inc₂_eq p q hp hq]
  simp only [vec_sub, vec_smul, vec_add]
  rw [vec_eq]
  constructor
  · field_simp [hapos.ne', hsum.ne']
    ring
  · field_simp [hapos.ne', hsum.ne']
    ring

/-- The key computation: `L = (0, pq / √(p²+q²))`, so `L` lies on `AC` with
`AL = pq / √(p²+q²) = AD`. -/
lemma ptL_eq (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    ptL p q = !₂[0, p * q / √(p^2+q^2)] := by
  have hapos : (0:ℝ) < √(p^2+q^2) := by positivity
  have hsum : (0:ℝ) < √(p^2+q^2) + p + q := by positivity
  simp only [ptL, yInt]
  rw [paramL p q hp hq, inc₁_eq p q hp hq, inc₂_eq p q hp hq]
  simp only [vec_sub, vec_smul, vec_add]
  rw [vec_eq]
  constructor
  · field_simp [hapos.ne', hsum.ne']
    ring
  · field_simp [hapos.ne', hsum.ne']
    ring

lemma ptK_x (p q : ℝ) (hp : 0 < p) (hq : 0 < q) : ptK p q 0 = p * q / √(p^2+q^2) := by
  rw [ptK_eq p q hp hq]; exact coord_x _ _

lemma ptK_y (p q : ℝ) (hp : 0 < p) (hq : 0 < q) : ptK p q 1 = 0 := by
  rw [ptK_eq p q hp hq]; exact coord_y _ _

lemma ptL_x (p q : ℝ) (hp : 0 < p) (hq : 0 < q) : ptL p q 0 = 0 := by
  rw [ptL_eq p q hp hq]; exact coord_x _ _

lemma ptL_y (p q : ℝ) (hp : 0 < p) (hq : 0 < q) : ptL p q 1 = p * q / √(p^2+q^2) := by
  rw [ptL_eq p q hp hq]; exact coord_y _ _

snip end

problem imo1988_p5 (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    2 * areaAKL p q ≤ areaABC p q := by
  have hX : (0:ℝ) < p^2 + q^2 := by positivity
  have ha2 : (√(p^2+q^2))^2 = p^2 + q^2 := Real.sq_sqrt hX.le
  rw [areaAKL, areaABC, ptK_x p q hp hq, ptL_y p q hp hq]
  have e : 2 * (p * q / √(p^2+q^2) * (p * q / √(p^2+q^2)) / 2) = (p*q)^2 / (p^2+q^2) := by
    rw [div_mul_div_comm, ← pow_two, ← pow_two, ha2]
    field_simp [hX.ne']
  rw [e, div_le_iff₀ hX]
  have h4 : p * q / 2 * (p^2+q^2) - (p*q)^2 = p * q / 2 * (p - q)^2 := by ring
  have h3 : (0:ℝ) ≤ p * q / 2 * (p - q)^2 := by positivity
  linarith

end Imo1988P5
