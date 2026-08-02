/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.Convex.StrictConvexBetween
public import Mathlib.Analysis.InnerProductSpace.OfNorm
public import Mathlib.Geometry.Euclidean.Triangle
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 2016, Problem 3

Let ABC be an acute triangle and let I_B, I_C, and O denote its B-excenter,
C-excenter, and circumcenter, respectively. Points E and Y are selected on AC
such that ∠ABY = ∠CBY and BE ⊥ AC. Similarly, points F and Z are selected on
AB such that ∠ACZ = ∠BCZ and CF ⊥ AB.

Lines I_B F and I_C E meet at P. Prove that PO and YZ are perpendicular.
-/

namespace Usa2016P3

open EuclideanGeometry RealInnerProductSpace

/-- The ambient Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-!
### The constructed points

We record the constructed points of the problem through their barycentric
coordinates with respect to the reference triangle `ABC`.  Writing
`a = dist B C`, `b = dist A C`, `c = dist A B` for the side lengths:

* the `B`-excenter is `(a : -b : c)` and the `C`-excenter is `(a : b : -c)`;
* the foot `Y` of the internal bisector of `∠B` on `AC` is `(a : 0 : c)`
  (angle bisector theorem: `AY : YC = c : a`);
* the foot `Z` of the internal bisector of `∠C` on `AB` is `(a : b : 0)`;
* the foot `E` of the altitude from `B` on `AC` is `(S_C : 0 : S_A)` and the
  foot `F` of the altitude from `C` on `AB` is `(S_B : S_A : 0)`, where
  `S_A = (b² + c² − a²)/2` etc. are Conway's triangle symbols
  (so `S_A + S_B = c²`, `S_B + S_C = a²`, `S_C + S_A = b²`).
-/

/-- Conway's triangle symbol `S_A = (b² + c² − a²) / 2`. -/
noncomputable def conwayA (a b c : ℝ) : ℝ := (b ^ 2 + c ^ 2 - a ^ 2) / 2

/-- Conway's triangle symbol `S_B = (c² + a² − b²) / 2`. -/
noncomputable def conwayB (a b c : ℝ) : ℝ := (c ^ 2 + a ^ 2 - b ^ 2) / 2

/-- Conway's triangle symbol `S_C = (a² + b² − c²) / 2`. -/
noncomputable def conwayC (a b c : ℝ) : ℝ := (a ^ 2 + b ^ 2 - c ^ 2) / 2

/-- The `B`-excenter of the triangle `ABC`: barycentric coordinates
`(a : -b : c)`. -/
noncomputable def excenterB (A B C : Plane) : Plane :=
  (dist B C - dist A C + dist A B)⁻¹ • (dist B C • A - dist A C • B + dist A B • C)

/-- The `C`-excenter of the triangle `ABC`: barycentric coordinates
`(a : b : -c)`. -/
noncomputable def excenterC (A B C : Plane) : Plane :=
  (dist B C + dist A C - dist A B)⁻¹ • (dist B C • A + dist A C • B - dist A B • C)

/-- The foot of the internal angle bisector from `B` on the line `AC`:
barycentric coordinates `(a : 0 : c)`. -/
noncomputable def bisectorFootB (A B C : Plane) : Plane :=
  (dist B C + dist A B)⁻¹ • (dist B C • A + dist A B • C)

/-- The foot of the internal angle bisector from `C` on the line `AB`:
barycentric coordinates `(a : b : 0)`. -/
noncomputable def bisectorFootC (A B C : Plane) : Plane :=
  (dist B C + dist A C)⁻¹ • (dist B C • A + dist A C • B)

/-- The foot of the altitude from `B` on the line `AC`: barycentric
coordinates `(S_C : 0 : S_A)`. -/
noncomputable def altitudeFootB (A B C : Plane) : Plane :=
  (dist A C ^ 2)⁻¹ • (conwayC (dist B C) (dist A C) (dist A B) • A +
    conwayA (dist B C) (dist A C) (dist A B) • C)

/-- The foot of the altitude from `C` on the line `AB`: barycentric
coordinates `(S_B : S_A : 0)`. -/
noncomputable def altitudeFootC (A B C : Plane) : Plane :=
  (dist A B ^ 2)⁻¹ • (conwayB (dist B C) (dist A C) (dist A B) • A +
    conwayA (dist B C) (dist A C) (dist A B) • B)

snip begin

/-- The numerator `x`-coordinate of the point
`P(t) = (1 - t) • I_B + t • F`, with denominator `(a - b + c) * c²`. -/
noncomputable def coordX (a b c t : ℝ) : ℝ :=
  (1 - t) * a * (a - b + c)⁻¹ + t * conwayB a b c * (c ^ 2)⁻¹

/-- The numerator `y`-coordinate of `P(t) = (1 - t) • I_B + t • F`. -/
noncomputable def coordY (a b c t : ℝ) : ℝ :=
  -(1 - t) * b * (a - b + c)⁻¹ + t * conwayA a b c * (c ^ 2)⁻¹

/-- The numerator `z`-coordinate of `P(t) = (1 - t) • I_B + t • F`. -/
noncomputable def coordZ (a b c t : ℝ) : ℝ :=
  (1 - t) * c * (a - b + c)⁻¹

/-- The numerator `x`-coordinate of `P(s) = (1 - s) • I_C + s • E`, with
denominator `(a + b - c) * b²`. -/
noncomputable def coordXR (a b c s : ℝ) : ℝ :=
  (1 - s) * a * (a + b - c)⁻¹ + s * conwayC a b c * (b ^ 2)⁻¹

/-- The numerator `y`-coordinate of `P(s) = (1 - s) • I_C + s • E`. -/
noncomputable def coordYR (a b c s : ℝ) : ℝ :=
  (1 - s) * b * (a + b - c)⁻¹

/-- The numerator `z`-coordinate of `P(s) = (1 - s) • I_C + s • E`. -/
noncomputable def coordZR (a b c s : ℝ) : ℝ :=
  -(1 - s) * c * (a + b - c)⁻¹ + s * conwayA a b c * (b ^ 2)⁻¹

/-- The condition that `P(t)` lies on the line `I_C E`, cleared of
denominators: a polynomial of degree one in `t`. -/
noncomputable def h2poly (a b c t : ℝ) : ℝ :=
  b * conwayA a b c * ((1 - t) * a * c ^ 2 + t * conwayB a b c * (a - b + c))
  - (a * conwayA a b c + c * conwayC a b c)
    * (-(1 - t) * b * c ^ 2 + t * conwayA a b c * (a - b + c))
  - b * conwayC a b c * ((1 - t) * c * c ^ 2)

/-- The quantity `(a - b + c) * c² * (a + c) * (a + b)` times
`(dist P Y)² − (dist P Z)² − ((dist O Y)² − (dist O Z)²)`, again a polynomial
of degree one in `t`. -/
noncomputable def linPQ (a b c t : ℝ) : ℝ :=
  (a * b ^ 2 * c - a * b * c ^ 2 + b ^ 3 * c - b * c ^ 3)
    * ((1 - t) * a * c ^ 2 + t * conwayB a b c * (a - b + c))
  + (a ^ 3 * c + a ^ 2 * b * c + a * b * c ^ 2 - a * c ^ 3)
    * (-(1 - t) * b * c ^ 2 + t * conwayA a b c * (a - b + c))
  + (-a ^ 3 * b - a ^ 2 * b * c + a * b ^ 3 - a * b ^ 2 * c)
    * ((1 - t) * c * c ^ 2)

/-- `(a + c) * (a + b) * linPQ`. -/
noncomputable def gpoly (a b c t : ℝ) : ℝ := (a + c) * (a + b) * linPQ a b c t

/-- The numerator of the (signed) power difference of `Y` and `Z` with
respect to the circumcircle of `ABC`. -/
noncomputable def pownum (a b c : ℝ) : ℝ :=
  -a ^ 3 * b ^ 2 * c + a ^ 3 * b * c ^ 2 - 2 * a ^ 2 * b ^ 3 * c + 2 * a ^ 2 * b * c ^ 3
    - a * b ^ 4 * c + a * b * c ^ 4

/-- The square of the distance between two points given by normalized
barycentric coordinates, in terms of the side lengths of the reference
triangle. -/
lemma dist_sq_bary {A B C : Plane} (x₁ y₁ z₁ x₂ y₂ z₂ : ℝ)
    (h₁ : x₁ + y₁ + z₁ = 1) (h₂ : x₂ + y₂ + z₂ = 1) :
    dist (x₁ • A + y₁ • B + z₁ • C) (x₂ • A + y₂ • B + z₂ • C) ^ 2 =
      -(dist B C ^ 2) * (y₁ - y₂) * (z₁ - z₂)
        - (dist A C ^ 2) * (z₁ - z₂) * (x₁ - x₂)
        - (dist A B ^ 2) * (x₁ - x₂) * (y₁ - y₂) := by
  have hx : x₁ - x₂ = -(y₁ - y₂) - (z₁ - z₂) := by linarith
  have hvec : (x₁ • A + y₁ • B + z₁ • C) - (x₂ • A + y₂ • B + z₂ • C)
      = (y₁ - y₂) • (B - A) + (z₁ - z₂) • (C - A) := by
    calc (x₁ • A + y₁ • B + z₁ • C) - (x₂ • A + y₂ • B + z₂ • C)
        = (x₁ - x₂) • A + (y₁ - y₂) • B + (z₁ - z₂) • C := by module
      _ = (-(y₁ - y₂) - (z₁ - z₂)) • A + (y₁ - y₂) • B + (z₁ - z₂) • C := by rw [hx]
      _ = (y₁ - y₂) • (B - A) + (z₁ - z₂) • (C - A) := by module
  have h2in : 2 * ⟪B - A, C - A⟫ = ‖B - A‖ ^ 2 + ‖C - A‖ ^ 2 - ‖B - C‖ ^ 2 := by
    have h := norm_sub_sq_real (B - A) (C - A)
    rw [show B - A - (C - A) = B - C by abel] at h
    linarith
  rw [dist_eq_norm, hvec, norm_add_sq_real, norm_smul, norm_smul,
    Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs,
    real_inner_smul_left, real_inner_smul_right, dist_eq_norm, dist_eq_norm,
    dist_eq_norm, norm_sub_rev A C, norm_sub_rev A B, hx]
  linear_combination h2in * ((y₁ - y₂) * (z₁ - z₂))

/-- If `Y` lies on the line `AC` as `Y = A + k • (C - A)` and `O` is
equidistant from `A` and `C`, then `|OY|² − |OA|² = (k² − k) · |AC|²`: the
power of `Y` with respect to the circle centered at `O` through `A`. -/
lemma dist_sq_sub_sq_of_mem_line {O A C Y : Plane} (hO : dist O A = dist O C)
    (k : ℝ) (hY : Y = A + k • (C - A)) :
    dist O Y ^ 2 - dist O A ^ 2 = (k ^ 2 - k) * dist A C ^ 2 := by
  have hO2 : 2 * ⟪O, C⟫ - 2 * ⟪O, A⟫ = ⟪C, C⟫ - ⟪A, A⟫ := by
    have h2 : ‖O - A‖ ^ 2 = ‖O - C‖ ^ 2 := by
      rw [← dist_eq_norm, ← dist_eq_norm, hO]
    rw [norm_sub_sq_real, norm_sub_sq_real, ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq] at h2
    linarith
  rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, hY,
    show O - (A + k • (C - A)) = (O - A) - k • (C - A) by abel,
    norm_sub_sq_real, real_inner_smul_right, inner_sub_left,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, norm_sub_rev C A]
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right]
  rw [real_inner_comm A C, real_inner_comm O A]
  linear_combination (-k) * hO2

/-- `PO ⊥ YZ` detected by squared distances:
`2 ⟪P - O, Z - Y⟫ = ((PY)² − (PZ)²) − ((OY)² − (OZ)²)`. -/
lemma two_inner_eq (P O Y Z : Plane) :
    2 * ⟪P - O, Z - Y⟫ =
      (dist P Y ^ 2 - dist P Z ^ 2) - (dist O Y ^ 2 - dist O Z ^ 2) := by
  simp only [dist_eq_norm, norm_sub_sq_real, inner_sub_left, inner_sub_right]
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  ring

/-- Non-collinear points are pairwise distinct. -/
lemma ne_of_not_collinear {A B C : Plane} (h : ¬ Collinear ℝ ({A, B, C} : Set Plane)) :
    A ≠ B ∧ A ≠ C ∧ B ≠ C := by
  refine ⟨fun heq => h ?_, fun heq => h ?_, fun heq => h ?_⟩
  · rw [heq]
    convert collinear_pair ℝ A C using 1
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; rw [heq]; tauto
  · rw [heq]
    convert collinear_pair ℝ A B using 1
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; rw [heq]; tauto
  · rw [heq]
    convert collinear_pair ℝ A B using 1
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; rw [heq]; tauto

/-- The strict triangle inequality for non-collinear points. -/
lemma dist_lt_add_of_not_collinear {A B C : Plane}
    (h : ¬ Collinear ℝ ({A, B, C} : Set Plane)) :
    dist A C < dist A B + dist B C := by
  have hle : dist A C ≤ dist A B + dist B C := dist_triangle A B C
  rcases hle.eq_or_lt with heq | hlt
  · exfalso
    have hbtw : Wbtw ℝ A B C := dist_add_dist_eq_iff.mp heq.symm
    have hBmem : B ∈ line[ℝ, A, C] := hbtw.mem_affineSpan
    have hcoll : Collinear ℝ (insert B {A, C}) :=
      (collinear_insert_iff_of_mem_affineSpan hBmem).mpr (collinear_pair ℝ A C)
    apply h
    convert hcoll using 1
    ext x; simp; tauto
  · exact hlt

/-- For an acute angle at `A`, `a² ≠ b² + c²`. -/
lemma conway_ne_of_acute {A B C : Plane} (hAB : A ≠ B) (hAC : A ≠ C)
    (hA : ∠ B A C < Real.pi / 2) :
    dist B C ^ 2 - dist A C ^ 2 - dist A B ^ 2 ≠ 0 := by
  have hcos : 0 < Real.cos (∠ B A C) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [angle_nonneg B A C, Real.pi_pos], hA⟩
  have hlaw :=
    dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle B A C
  rw [dist_comm B A, dist_comm C A] at hlaw
  have hpos : 0 < dist A B * dist A C * Real.cos (∠ B A C) :=
    mul_pos (mul_pos (dist_pos.mpr hAB) (dist_pos.mpr hAC)) hcos
  have h1 : dist B C ^ 2 - dist A C ^ 2 - dist A B ^ 2
      = -2 * (dist A B * dist A C * Real.cos (∠ B A C)) := by
    rw [sq, sq, sq]
    linarith
  rw [h1]
  linarith [hpos]

/-- Barycentric coordinates with respect to an affinely independent triple of
points are unique. -/
lemma coords_unique {A B C : Plane} (h : AffineIndependent ℝ ![A, B, C])
    {x₁ y₁ z₁ x₂ y₂ z₂ : ℝ} (hs₁ : x₁ + y₁ + z₁ = 1) (hs₂ : x₂ + y₂ + z₂ = 1)
    (hvec : x₁ • A + y₁ • B + z₁ • C = x₂ • A + y₂ • B + z₂ • C) :
    x₁ = x₂ ∧ y₁ = y₂ ∧ z₁ = z₂ := by
  have hnc : ¬ Collinear ℝ ({A, B, C} : Set Plane) :=
    affineIndependent_iff_not_collinear_set.mp h
  have hLI : LinearIndependent ℝ ![B - A, C - A] := by
    rw [LinearIndependent.pair_iff]
    intro u v huv
    by_contra hcon
    rw [not_and_or] at hcon
    apply hnc
    rcases hcon with hu | hv
    · have h1 : u • (B - A) = (-v) • (C - A) := by
        rwa [add_eq_zero_iff_eq_neg, ← neg_smul] at huv
      have h3 : u • ((B - A) - ((-v / u) • (C - A))) = 0 := by
        rw [smul_sub, h1, smul_smul, div_eq_mul_inv, mul_comm u (-v * u⁻¹),
          mul_assoc, inv_mul_cancel₀ hu, mul_one, sub_self]
      have h4 : (B - A) - ((-v / u) • (C - A)) = 0 := by
        rcases smul_eq_zero.mp h3 with h5 | h5
        · exact absurd h5 hu
        · exact h5
      have h5 : B - A = (-v / u) • (C - A) := sub_eq_zero.mp h4
      have hB : B = A + (-v / u) • (C - A) := by
        rw [← h5]; abel
      have hBmem : B ∈ line[ℝ, A, C] :=
        mem_affineSpan_pair_iff_exists_lineMap_eq.mpr
          ⟨-v / u, by rw [AffineMap.lineMap_apply_module', ← h5]; abel⟩
      have hcoll : Collinear ℝ (insert B {A, C}) :=
        (collinear_insert_iff_of_mem_affineSpan hBmem).mpr (collinear_pair ℝ A C)
      convert hcoll using 1
      ext x; simp; tauto
    · have h1 : v • (C - A) = (-u) • (B - A) := by
        rw [add_comm] at huv
        rwa [add_eq_zero_iff_eq_neg, ← neg_smul] at huv
      have h3 : v • ((C - A) - ((-u / v) • (B - A))) = 0 := by
        rw [smul_sub, h1, smul_smul, div_eq_mul_inv, mul_comm v (-u * v⁻¹),
          mul_assoc, inv_mul_cancel₀ hv, mul_one, sub_self]
      have h4 : (C - A) - ((-u / v) • (B - A)) = 0 := by
        rcases smul_eq_zero.mp h3 with h5 | h5
        · exact absurd h5 hv
        · exact h5
      have h5 : C - A = (-u / v) • (B - A) := sub_eq_zero.mp h4
      have hC : C = A + (-u / v) • (B - A) := by
        rw [← h5]; abel
      have hCmem : C ∈ line[ℝ, A, B] :=
        mem_affineSpan_pair_iff_exists_lineMap_eq.mpr
          ⟨-u / v, by rw [AffineMap.lineMap_apply_module', ← h5]; abel⟩
      have hcoll : Collinear ℝ (insert C {A, B}) :=
        (collinear_insert_iff_of_mem_affineSpan hCmem).mpr (collinear_pair ℝ A B)
      convert hcoll using 1
      ext x; simp; tauto
  have h0 : (y₁ - y₂) • (B - A) + (z₁ - z₂) • (C - A) = 0 := by
    have hx : x₁ - x₂ = -(y₁ - y₂) - (z₁ - z₂) := by linarith
    have e1 : (x₁ - x₂) • A + (y₁ - y₂) • B + (z₁ - z₂) • C = 0 := by
      have e2 : (x₁ - x₂) • A + (y₁ - y₂) • B + (z₁ - z₂) • C
          = (x₁ • A + y₁ • B + z₁ • C) - (x₂ • A + y₂ • B + z₂ • C) := by module
      rw [e2, hvec, sub_self]
    rw [hx] at e1
    have e3 : (y₁ - y₂) • (B - A) + (z₁ - z₂) • (C - A)
        = (-(y₁ - y₂) - (z₁ - z₂)) • A + (y₁ - y₂) • B + (z₁ - z₂) • C := by module
    rw [e3, e1]
  obtain ⟨hy, hz⟩ := LinearIndependent.pair_iff.mp hLI (y₁ - y₂) (z₁ - z₂) h0
  exact ⟨by linarith, sub_eq_zero.mp hy, sub_eq_zero.mp hz⟩

/-- The coordinates of `P(t)` sum to one. -/
lemma coord_sum (a b c t : ℝ) (e1 : a - b + c ≠ 0) (e2 : c ≠ 0) :
    coordX a b c t + coordY a b c t + coordZ a b c t = 1 := by
  simp only [coordX, coordY, coordZ, conwayA, conwayB]
  field_simp
  ring

/-- The coordinates of `P(s)` sum to one. -/
lemma coordR_sum (a b c s : ℝ) (e4 : a + b - c ≠ 0) (e3 : b ≠ 0) :
    coordXR a b c s + coordYR a b c s + coordZR a b c s = 1 := by
  simp only [coordXR, coordYR, coordZR, conwayA, conwayC]
  field_simp
  ring

/-- Every point of the line `I_C E` satisfies the line equation (the
determinant cancels). -/
lemma h2raw_zero (a b c s : ℝ) :
    b * conwayA a b c * coordXR a b c s
    - (a * conwayA a b c + c * conwayC a b c) * coordYR a b c s
    - b * conwayC a b c * coordZR a b c s = 0 := by
  simp only [coordXR, coordYR, coordZR, conwayA, conwayC]
  ring

/-- The cleared line condition is `(a - b + c) * c²` times the raw one. -/
lemma h2poly_eq_smul_raw (a b c t : ℝ) (e1 : a - b + c ≠ 0) (e2 : c ≠ 0) :
    h2poly a b c t = (a - b + c) * c ^ 2 *
      (b * conwayA a b c * coordX a b c t
      - (a * conwayA a b c + c * conwayC a b c) * coordY a b c t
      - b * conwayC a b c * coordZ a b c t) := by
  simp only [h2poly, coordX, coordY, coordZ, conwayA, conwayB, conwayC]
  field_simp

/-- Decomposition of `(dist P Y)² − (dist P Z)²` into a part linear in the
coordinates of `P` and the power difference of `Y` and `Z`. -/
lemma dist_diff_eq (a b c t : ℝ) (e1 : a - b + c ≠ 0) (e2 : c ≠ 0)
    (e5 : a + c ≠ 0) (e6 : a + b ≠ 0) :
    (-(a ^ 2) * (coordY a b c t - 0) * (coordZ a b c t - c / (a + c))
      - (b ^ 2) * (coordZ a b c t - c / (a + c)) * (coordX a b c t - a / (a + c))
      - (c ^ 2) * (coordX a b c t - a / (a + c)) * (coordY a b c t - 0))
    - (-(a ^ 2) * (coordY a b c t - b / (a + b)) * (coordZ a b c t - 0)
      - (b ^ 2) * (coordZ a b c t - 0) * (coordX a b c t - a / (a + b))
      - (c ^ 2) * (coordX a b c t - a / (a + b)) * (coordY a b c t - b / (a + b)))
    = linPQ a b c t / ((a - b + c) * c ^ 2 * (a + c) * (a + b))
      + pownum a b c / ((a + c) ^ 2 * (a + b) ^ 2) := by
  simp only [coordX, coordY, coordZ, linPQ, pownum, conwayA, conwayB]
  field_simp
  ring

/-- The master polynomial identity: the two degree-one polynomials `h2poly`
and `gpoly` in `t` are proportional. -/
lemma key_algebra (a b c t : ℝ) :
    (h2poly a b c 1 - h2poly a b c 0) * gpoly a b c t
    = (gpoly a b c 1 - gpoly a b c 0) * h2poly a b c t := by
  simp only [h2poly, gpoly, linPQ, conwayA, conwayB, conwayC]
  ring

/-- The constant term of `h2poly` is `-a * b * c² * (a² − b² − c²)`. -/
lemma h2poly_zero (a b c : ℝ) :
    h2poly a b c 0 = -a * b * c ^ 2 * (a ^ 2 - b ^ 2 - c ^ 2) := by
  simp only [h2poly, conwayA, conwayB, conwayC]
  ring

/-- `h2poly` is affine in `t`. -/
lemma h2poly_affine (a b c u : ℝ) :
    h2poly a b c u = h2poly a b c 0 + (h2poly a b c 1 - h2poly a b c 0) * u := by
  simp only [h2poly, conwayA, conwayB, conwayC]
  ring

/-- The power difference in factored form. -/
lemma pownum_eq (a b c : ℝ) (e5 : a + c ≠ 0) (e6 : a + b ≠ 0) :
    pownum a b c / ((a + c) ^ 2 * (a + b) ^ 2)
    = -a * b ^ 2 * c / (a + c) ^ 2 + a * b * c ^ 2 / (a + b) ^ 2 := by
  simp only [pownum]
  field_simp
  ring

/-- The punchline of the computation: if `h2poly a b c t = 0` (the point
`P(t)` lies on the line `I_C E`), then `linPQ a b c t = 0` (the
perpendicularity conclusion).  The constant term of `h2poly` is nonzero for
an acute triangle, so `h2poly` cannot vanish identically; the master identity
`key_algebra` then forces `linPQ` to vanish at `t`. -/
lemma linPQ_eq_zero_of_h2poly (a b c t : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (e5 : a + c ≠ 0) (e6 : a + b ≠ 0) (econ : a ^ 2 - b ^ 2 - c ^ 2 ≠ 0)
    (h2 : h2poly a b c t = 0) :
    linPQ a b c t = 0 := by
  have master := key_algebra a b c t
  rw [h2, mul_zero] at master
  rcases mul_eq_zero.mp master with hα | hG
  · exfalso
    have hβ0 : h2poly a b c t = h2poly a b c 0 := by
      rw [h2poly_affine a b c t, hα, zero_mul, add_zero]
    rw [h2, h2poly_zero] at hβ0
    have hne : -a * b * c ^ 2 * (a ^ 2 - b ^ 2 - c ^ 2) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr ha) hb) (pow_ne_zero 2 hc)) econ
    exact hne hβ0.symm
  · have hG' : (a + c) * (a + b) * linPQ a b c t = 0 := hG
    rcases mul_eq_zero.mp hG' with h1 | h2
    · rcases mul_eq_zero.mp h1 with h1' | h1''
      · exact absurd h1' e5
      · exact absurd h1'' e6
    · exact h2

snip end

problem usa2016_p3
    (A B C IB IC O E F Y Z P : Plane)
    (htri : AffineIndependent ℝ ![A, B, C])
    (hacuteA : ∠ B A C < Real.pi / 2)
    (_hacuteB : ∠ A B C < Real.pi / 2)
    (_hacuteC : ∠ B C A < Real.pi / 2)
    (hIB : IB = excenterB A B C)
    (hIC : IC = excenterC A B C)
    (hO : dist O A = dist O B ∧ dist O B = dist O C)
    (hY : Y = bisectorFootB A B C)
    (hZ : Z = bisectorFootC A B C)
    (hE : E = altitudeFootB A B C)
    (hF : F = altitudeFootC A B C)
    (hP1 : P ∈ line[ℝ, IB, F])
    (hP2 : P ∈ line[ℝ, IC, E]) :
    ⟪P -ᵥ O, Z -ᵥ Y⟫ = 0 := by
  -- Non-degeneracy of the triangle.
  have hnc : ¬ Collinear ℝ ({A, B, C} : Set Plane) :=
    affineIndependent_iff_not_collinear_set.mp htri
  obtain ⟨hAB, hAC, hBC⟩ := ne_of_not_collinear hnc
  have ha0 : (0 : ℝ) < dist B C := dist_pos.mpr hBC
  have hb0 : (0 : ℝ) < dist A C := dist_pos.mpr hAC
  have hc0 : (0 : ℝ) < dist A B := dist_pos.mpr hAB
  have hac : dist A C < dist B C + dist A B := by
    have h := dist_lt_add_of_not_collinear hnc
    linarith
  have hab : dist A B < dist B C + dist A C := by
    have hnc' : ¬ Collinear ℝ ({B, C, A} : Set Plane) := by
      intro hc'
      apply hnc
      convert hc' using 1
      ext x; simp; tauto
    have h := dist_lt_add_of_not_collinear hnc'
    rw [dist_comm B A, dist_comm C A] at h
    linarith
  have e1 : dist B C - dist A C + dist A B ≠ 0 := by linarith
  have e4 : dist B C + dist A C - dist A B ≠ 0 := by linarith
  have hsum_ab : dist B C + dist A C ≠ 0 := ne_of_gt (add_pos ha0 hb0)
  have hsum_ac : dist B C + dist A B ≠ 0 := ne_of_gt (add_pos ha0 hc0)
  have e2 : dist A B ≠ 0 := ne_of_gt hc0
  have e3 : dist A C ≠ 0 := ne_of_gt hb0
  have e7 : dist B C ≠ 0 := ne_of_gt ha0
  have econ : dist B C ^ 2 - dist A C ^ 2 - dist A B ^ 2 ≠ 0 :=
    conway_ne_of_acute hAB hAC hacuteA
  -- The two line parameters for `P`.
  rw [hIB, hF] at hP1
  rw [hIC, hE] at hP2
  obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hP1
  obtain ⟨s, hs⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hP2
  rw [AffineMap.lineMap_apply_module] at ht hs
  -- Barycentric coordinates of `P`, in both parametrizations.
  have hvecP : P = coordX (dist B C) (dist A C) (dist A B) t • A
      + coordY (dist B C) (dist A C) (dist A B) t • B
      + coordZ (dist B C) (dist A C) (dist A B) t • C := by
    rw [← ht]
    simp only [excenterB, altitudeFootC, coordX, coordY, coordZ, conwayA, conwayB]
    module
  have hvecPR : P = coordXR (dist B C) (dist A C) (dist A B) s • A
      + coordYR (dist B C) (dist A C) (dist A B) s • B
      + coordZR (dist B C) (dist A C) (dist A B) s • C := by
    rw [← hs]
    simp only [excenterC, altitudeFootB, coordXR, coordYR, coordZR, conwayA, conwayC]
    module
  -- The point `P(t)` lies on the line `I_C E`: the cleared condition.
  have hcs := coords_unique htri (coord_sum (dist B C) (dist A C) (dist A B) t e1 e2)
    (coordR_sum (dist B C) (dist A C) (dist A B) s e4 e3) (hvecP.symm.trans hvecPR)
  obtain ⟨hx, hy, hz⟩ := hcs
  have hraw : dist A C * conwayA (dist B C) (dist A C) (dist A B)
        * coordX (dist B C) (dist A C) (dist A B) t
      - (dist B C * conwayA (dist B C) (dist A C) (dist A B)
          + dist A B * conwayC (dist B C) (dist A C) (dist A B))
        * coordY (dist B C) (dist A C) (dist A B) t
      - dist A C * conwayC (dist B C) (dist A C) (dist A B)
        * coordZ (dist B C) (dist A C) (dist A B) t = 0 := by
    rw [hx, hy, hz]
    exact h2raw_zero (dist B C) (dist A C) (dist A B) s
  have h2 : h2poly (dist B C) (dist A C) (dist A B) t = 0 := by
    rw [h2poly_eq_smul_raw (dist B C) (dist A C) (dist A B) t e1 e2, hraw, mul_zero]
  -- The algebraic heart: `linPQ` vanishes at `t`.
  have hL : linPQ (dist B C) (dist A C) (dist A B) t = 0 :=
    linPQ_eq_zero_of_h2poly (dist B C) (dist A C) (dist A B) t e7 e3 e2
      hsum_ac hsum_ab econ h2
  -- Barycentric coordinates of `Y` and `Z`.
  have hYk : Y = A + (dist A B / (dist B C + dist A B)) • (C - A) := by
    rw [hY, bisectorFootB, inv_smul_eq_iff₀ hsum_ac, div_eq_mul_inv, smul_add,
      smul_smul, mul_comm (dist B C + dist A B) (dist A B * (dist B C + dist A B)⁻¹),
      mul_assoc, inv_mul_cancel₀ hsum_ac, mul_one]
    module
  have hZk : Z = A + (dist A C / (dist B C + dist A C)) • (B - A) := by
    rw [hZ, bisectorFootC, inv_smul_eq_iff₀ hsum_ab, div_eq_mul_inv, smul_add,
      smul_smul, mul_comm (dist B C + dist A C) (dist A C * (dist B C + dist A C)⁻¹),
      mul_assoc, inv_mul_cancel₀ hsum_ab, mul_one]
    module
  have hvecY : Y = (dist B C / (dist B C + dist A B)) • A + (0 : ℝ) • B
      + (dist A B / (dist B C + dist A B)) • C := by
    have hsc : (1 : ℝ) - dist A B / (dist B C + dist A B)
        = dist B C / (dist B C + dist A B) := by
      field_simp
      ring
    rw [hYk, ← hsc]
    module
  have hvecZ : Z = (dist B C / (dist B C + dist A C)) • A
      + (dist A C / (dist B C + dist A C)) • B + (0 : ℝ) • C := by
    have hsc : (1 : ℝ) - dist A C / (dist B C + dist A C)
        = dist B C / (dist B C + dist A C) := by
      field_simp
      ring
    rw [hZk, ← hsc]
    module
  have hYsum : dist B C / (dist B C + dist A B) + 0 + dist A B / (dist B C + dist A B)
      = 1 := by
    field_simp
    ring
  have hZsum : dist B C / (dist B C + dist A C) + dist A C / (dist B C + dist A C) + 0
      = 1 := by
    field_simp
    ring
  -- The power of `Y` and `Z` with respect to the circumcircle.
  have hOAC : dist O A = dist O C := hO.1.trans hO.2
  have hOY : dist O Y ^ 2 - dist O A ^ 2
      = -dist B C * dist A C ^ 2 * dist A B / (dist B C + dist A B) ^ 2 := by
    have h := dist_sq_sub_sq_of_mem_line hOAC (dist A B / (dist B C + dist A B)) hYk
    rw [h]
    field_simp
    ring
  have hOZ : dist O Z ^ 2 - dist O A ^ 2
      = -dist B C * dist A C * dist A B ^ 2 / (dist B C + dist A C) ^ 2 := by
    have h := dist_sq_sub_sq_of_mem_line hO.1 (dist A C / (dist B C + dist A C)) hZk
    rw [h]
    field_simp
    ring
  -- Assembling the distance computations.
  have hPQ : dist P Y ^ 2 - dist P Z ^ 2 =
      linPQ (dist B C) (dist A C) (dist A B) t
        / ((dist B C - dist A C + dist A B) * (dist A B) ^ 2
          * (dist B C + dist A B) * (dist B C + dist A C))
      + pownum (dist B C) (dist A C) (dist A B)
        / ((dist B C + dist A B) ^ 2 * (dist B C + dist A C) ^ 2) := by
    have h1 : dist P Y ^ 2 =
        -(dist B C ^ 2) * (coordY (dist B C) (dist A C) (dist A B) t - 0) *
            (coordZ (dist B C) (dist A C) (dist A B) t - dist A B / (dist B C + dist A B))
          - dist A C ^ 2 * (coordZ (dist B C) (dist A C) (dist A B) t
              - dist A B / (dist B C + dist A B)) *
            (coordX (dist B C) (dist A C) (dist A B) t - dist B C / (dist B C + dist A B))
          - dist A B ^ 2 * (coordX (dist B C) (dist A C) (dist A B) t
              - dist B C / (dist B C + dist A B)) *
            (coordY (dist B C) (dist A C) (dist A B) t - 0) := by
      rw [hvecP, hvecY]
      exact dist_sq_bary (A := A) (B := B) (C := C)
        (coordX (dist B C) (dist A C) (dist A B) t)
        (coordY (dist B C) (dist A C) (dist A B) t)
        (coordZ (dist B C) (dist A C) (dist A B) t)
        (dist B C / (dist B C + dist A B)) 0 (dist A B / (dist B C + dist A B))
        (coord_sum (dist B C) (dist A C) (dist A B) t e1 e2) hYsum
    have h2 : dist P Z ^ 2 =
        -(dist B C ^ 2) * (coordY (dist B C) (dist A C) (dist A B) t
            - dist A C / (dist B C + dist A C)) * (coordZ (dist B C) (dist A C) (dist A B) t - 0)
          - dist A C ^ 2 * (coordZ (dist B C) (dist A C) (dist A B) t - 0) *
            (coordX (dist B C) (dist A C) (dist A B) t - dist B C / (dist B C + dist A C))
          - dist A B ^ 2 * (coordX (dist B C) (dist A C) (dist A B) t
              - dist B C / (dist B C + dist A C)) *
            (coordY (dist B C) (dist A C) (dist A B) t - dist A C / (dist B C + dist A C)) := by
      rw [hvecP, hvecZ]
      exact dist_sq_bary (A := A) (B := B) (C := C)
        (coordX (dist B C) (dist A C) (dist A B) t)
        (coordY (dist B C) (dist A C) (dist A B) t)
        (coordZ (dist B C) (dist A C) (dist A B) t)
        (dist B C / (dist B C + dist A C)) (dist A C / (dist B C + dist A C)) 0
        (coord_sum (dist B C) (dist A C) (dist A B) t e1 e2) hZsum
    rw [h1, h2]
    exact dist_diff_eq (dist B C) (dist A C) (dist A B) t e1 e2 hsum_ac hsum_ab
  have hOO : dist O Y ^ 2 - dist O Z ^ 2 =
      pownum (dist B C) (dist A C) (dist A B)
        / ((dist B C + dist A B) ^ 2 * (dist B C + dist A C) ^ 2) := by
    rw [pownum_eq (dist B C) (dist A C) (dist A B) hsum_ac hsum_ab]
    linear_combination hOY - hOZ
  have hGraw : (dist P Y ^ 2 - dist P Z ^ 2) - (dist O Y ^ 2 - dist O Z ^ 2) = 0 := by
    rw [hPQ, hOO, hL, zero_div]
    ring
  -- Back to the inner product.
  have hfin : 2 * ⟪P - O, Z - Y⟫ = 0 := by
    rw [two_inner_eq]
    exact hGraw
  have hfin' : ⟪P - O, Z - Y⟫ = 0 := by
    rcases mul_eq_zero.mp hfin with h2 | h'
    · norm_num at h2
    · exact h'
  rw [vsub_eq_sub, vsub_eq_sub]
  exact hfin'

end Usa2016P3
