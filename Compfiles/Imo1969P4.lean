/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Sphere.Tangent
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1969, Problem 4

`C` is a point on the semicircle with diameter `AB`, between `A` and `B`. `D`
is the foot of the perpendicular from `C` to `AB`. The circle `K1` is the
incircle of `ABC`, the circle `K2` touches `CD`, `DA` and the semicircle, and
the circle `K3` touches `CD`, `DB` and the semicircle. Prove that `K1`, `K2`
and `K3` have another common tangent apart from `AB`.
-/

namespace Imo1969P4

open EuclideanGeometry
open scoped InnerProductSpace Affine

/-- The Euclidean plane, in which we place the configuration. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Vertex `A`, placed at the origin. -/
def ptA : Plane := !₂[0, 0]

/-- Vertex `B`, placed at `(c, 0)`, where `c = AB`. -/
def ptB (c : ℝ) : Plane := !₂[c, 0]

/-- Vertex `C` on the semicircle. With `a = BC`, `b = CA` one has `AD = b²/c`
and `CD = ab/c` (similar triangles), where `D` is the foot of the
perpendicular from `C` to `AB`. -/
noncomputable def ptC (a b c : ℝ) : Plane := !₂[b ^ 2 / c, a * b / c]

/-- The foot `D` of the perpendicular from `C` to `AB`. -/
noncomputable def ptD (b c : ℝ) : Plane := !₂[b ^ 2 / c, 0]

/-- The midpoint of `AB`, i.e. the center of the semicircle. -/
noncomputable def ptO (c : ℝ) : Plane := !₂[c / 2, 0]

/-- The full circle of which the semicircle with diameter `AB` is a part. -/
noncomputable def bigCircle (c : ℝ) : Sphere Plane := ⟨ptO c, c / 2⟩

/-- The radius of the incircle `K1` of `ABC`: `r1 = (a + b - c)/2`. -/
noncomputable def r1 (a b c : ℝ) : ℝ := (a + b - c) / 2

/-- The radius of `K2`: `r2 = a - a²/c`. -/
noncomputable def r2 (a _b c : ℝ) : ℝ := a - a ^ 2 / c

/-- The radius of `K3`: `r3 = b - b²/c`. -/
noncomputable def r3 (_a b c : ℝ) : ℝ := b - b ^ 2 / c

/-- The center of the incircle `K1`. -/
noncomputable def O1 (a b c : ℝ) : Plane := !₂[(b + c - a) / 2, r1 a b c]

/-- The center of `K2`. -/
noncomputable def O2 (a b c : ℝ) : Plane := !₂[c - a, r2 a b c]

/-- The center of `K3`. -/
noncomputable def O3 (a b c : ℝ) : Plane := !₂[b, r3 a b c]

/-- The incircle of the triangle `ABC`. -/
noncomputable def K1 (a b c : ℝ) : Sphere Plane := ⟨O1 a b c, r1 a b c⟩

/-- The circle touching `CD`, `DA` and the semicircle. -/
noncomputable def K2 (a b c : ℝ) : Sphere Plane := ⟨O2 a b c, r2 a b c⟩

/-- The circle touching `CD`, `DB` and the semicircle. -/
noncomputable def K3 (a b c : ℝ) : Sphere Plane := ⟨O3 a b c, r3 a b c⟩

snip begin

variable {a b c : ℝ}

/-- Inner product of two plane vectors given by their coordinates. -/
theorem inner_mk (x₁ y₁ x₂ y₂ : ℝ) :
    ⟪(!₂[x₁, y₁] : Plane), (!₂[x₂, y₂] : Plane)⟫_ℝ = x₁ * x₂ + y₁ * y₂ := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- Coordinates of a difference of two plane vectors. -/
theorem mk_sub_mk (x₁ y₁ x₂ y₂ : ℝ) :
    (!₂[x₁, y₁] : Plane) - (!₂[x₂, y₂] : Plane) = !₂[x₁ - x₂, y₁ - y₂] := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [PiLp.sub_apply]

/-- The normalizing factor `N = r2² + r3²` of the normal vector `u`. -/
noncomputable def uN (a b c : ℝ) : ℝ := r2 a b c ^ 2 + r3 a b c ^ 2

/-- The unit normal vector of the second common tangent, pointing from the
line towards the three centers. -/
noncomputable def uVec (a b c : ℝ) : Plane :=
  !₂[(r2 a b c ^ 2 - r3 a b c ^ 2) / uN a b c,
     2 * r2 a b c * r3 a b c / uN a b c]

theorem r1_pos (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a ^ 2 + b ^ 2 = c ^ 2) :
    0 < r1 a b c := by
  have h1 : c ^ 2 < (a + b) ^ 2 := by nlinarith [h, mul_pos ha hb]
  have h2 : c < a + b := (sq_lt_sq₀ hc.le (by positivity)).mp h1
  simp only [r1]
  linarith

theorem r2_pos (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a ^ 2 + b ^ 2 = c ^ 2) :
    0 < r2 a b c := by
  have h1 : a ^ 2 < c ^ 2 := by nlinarith [h, sq_pos_of_pos hb]
  have h2 : a < c := (sq_lt_sq₀ ha.le hc.le).mp h1
  have h3 : r2 a b c = a * (c - a) / c := by
    simp only [r2]
    have hc' := hc.ne'
    field_simp
  rw [h3]
  positivity

theorem r3_pos (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a ^ 2 + b ^ 2 = c ^ 2) :
    0 < r3 a b c := by
  have h1 : b ^ 2 < c ^ 2 := by nlinarith [h, sq_pos_of_pos ha]
  have h2 : b < c := (sq_lt_sq₀ hb.le hc.le).mp h1
  have h3 : r3 a b c = b * (c - b) / c := by
    simp only [r3]
    have hc' := hc.ne'
    field_simp
  rw [h3]
  positivity

theorem uN_pos (hr2 : 0 < r2 a b c) (hr3 : 0 < r3 a b c) : 0 < uN a b c :=
  add_pos (sq_pos_of_pos hr2) (sq_pos_of_pos hr3)

/-- The fundamental relation between the three radii: `r1` is the average of
`r2` and `r3`. -/
theorem two_r1 (hc : 0 < c) (h : a ^ 2 + b ^ 2 = c ^ 2) :
    2 * r1 a b c = r2 a b c + r3 a b c := by
  have hc' : c ≠ 0 := hc.ne'
  simp only [r1, r2, r3]
  field_simp
  linear_combination h

theorem inner_uVec (hr2 : 0 < r2 a b c) (hr3 : 0 < r3 a b c) :
    ⟪uVec a b c, uVec a b c⟫_ℝ = 1 := by
  have hN : (0:ℝ) < r2 a b c ^ 2 + r3 a b c ^ 2 :=
    add_pos (sq_pos_of_pos hr2) (sq_pos_of_pos hr3)
  simp only [uVec, uN, inner_mk]
  field_simp [hN.ne']
  ring

theorem inner_O2_sub_O1 (hc : 0 < c) (h : a ^ 2 + b ^ 2 = c ^ 2)
    (hr2 : 0 < r2 a b c) (hr3 : 0 < r3 a b c) :
    ⟪O2 a b c - O1 a b c, uVec a b c⟫_ℝ = r1 a b c - r2 a b c := by
  have hN : (0:ℝ) < r2 a b c ^ 2 + r3 a b c ^ 2 :=
    add_pos (sq_pos_of_pos hr2) (sq_pos_of_pos hr3)
  have h1 : 2 * r1 a b c = r2 a b c + r3 a b c := two_r1 hc h
  have e : (O2 a b c - O1 a b c : Plane) =
      !₂[(c - a - b) / 2, r2 a b c - r1 a b c] := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [O1, O2, PiLp.sub_apply] <;> ring
  have hneg : (c - a - b) / 2 = -r1 a b c := by simp only [r1]; ring
  rw [e]
  simp only [uVec, uN, inner_mk]
  rw [hneg]
  field_simp [hN.ne']
  linear_combination (-(r2 a b c) * (r2 a b c + r3 a b c)) * h1

theorem inner_O3_sub_O2 (hc : 0 < c) (h : a ^ 2 + b ^ 2 = c ^ 2)
    (hr2 : 0 < r2 a b c) (hr3 : 0 < r3 a b c) :
    ⟪O3 a b c - O2 a b c, uVec a b c⟫_ℝ = r2 a b c - r3 a b c := by
  have hN : (0:ℝ) < r2 a b c ^ 2 + r3 a b c ^ 2 :=
    add_pos (sq_pos_of_pos hr2) (sq_pos_of_pos hr3)
  have h1 : 2 * r1 a b c = r2 a b c + r3 a b c := two_r1 hc h
  have e : (O3 a b c - O2 a b c : Plane) =
      !₂[a + b - c, r3 a b c - r2 a b c] := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [O2, O3, PiLp.sub_apply] <;> ring
  have hpos : a + b - c = 2 * r1 a b c := by simp only [r1]; ring
  rw [e]
  simp only [uVec, uN, inner_mk]
  rw [hpos]
  field_simp [hN.ne']
  linear_combination ((r2 a b c - r3 a b c) * (r2 a b c + r3 a b c)) * h1

theorem inner_O3_sub_O1 (hc : 0 < c) (h : a ^ 2 + b ^ 2 = c ^ 2)
    (hr2 : 0 < r2 a b c) (hr3 : 0 < r3 a b c) :
    ⟪O3 a b c - O1 a b c, uVec a b c⟫_ℝ = r1 a b c - r3 a b c := by
  have e : (O3 a b c - O1 a b c : Plane) =
      (O3 a b c - O2 a b c) + (O2 a b c - O1 a b c) := by abel
  rw [e, inner_add_left, inner_O2_sub_O1 hc h hr2 hr3, inner_O3_sub_O2 hc h hr2 hr3]
  ring

/-- The second coordinate of every point of the line `AB` vanishes. -/
theorem inner_e2_eq_zero_of_mem_lineAB {x : Plane} (hx : x ∈ line[ℝ, ptA, ptB c]) :
    ⟪x -ᵥ ptA, (!₂[0, 1] : Plane)⟫_ℝ = 0 := by
  have hdir : (x -ᵥ ptA : Plane) ∈ ℝ ∙ (ptA -ᵥ ptB c) := by
    have h1 := AffineSubspace.vsub_mem_direction hx
      (left_mem_affineSpan_pair ℝ ptA (ptB c))
    rwa [direction_affineSpan, vectorSpan_pair] at h1
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hdir
  rw [← ht, vsub_eq_sub]
  simp only [ptA, ptB, real_inner_smul_left]
  rw [mk_sub_mk, inner_mk]
  ring

/-- Any circle whose center `(q, r)` is at height equal to its radius `r > 0`
touches the line `AB` (the x-axis) at the point `(q, 0)`. -/
theorem isTangentAt_lineAB (q r : ℝ) (hr : 0 < r) (hc : 0 < c) :
    (⟨!₂[q, r], r⟩ : Sphere Plane).IsTangentAt !₂[q, 0] line[ℝ, ptA, ptB c] := by
  have hc' : c ≠ 0 := hc.ne'
  have e : (!₂[q, 0] - !₂[q, r] : Plane) = !₂[0, -r] := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [PiLp.sub_apply]
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_sphere]
    show dist !₂[q, 0] !₂[q, r] = r
    rw [dist_eq_norm_vsub, vsub_eq_sub, e, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, Real.sqrt_sq hr.le]
  · have h := AffineMap.lineMap_mem_affineSpan_pair (q / c) ptA (ptB c)
    rw [AffineMap.lineMap_apply] at h
    have e2 : ((q / c : ℝ) • (ptB c -ᵥ ptA) +ᵥ ptA : Plane) = !₂[q, 0] := by
      rw [vadd_eq_add, vsub_eq_sub]
      apply PiLp.ext
      intro i
      fin_cases i <;>
        simp [ptA, ptB, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply] <;>
        field_simp [hc']
    rwa [e2] at h
  · intro x hx
    rw [Sphere.mem_orthRadius_iff_inner_left]
    show ⟪x -ᵥ !₂[q, 0], !₂[q, 0] -ᵥ !₂[q, r]⟫_ℝ = 0
    rw [show (!₂[q, 0] -ᵥ !₂[q, r] : Plane) = !₂[q, 0] - !₂[q, r] from vsub_eq_sub _ _, e]
    rw [show (!₂[0, -r] : Plane) = (-r) • !₂[0, 1] by
      apply PiLp.ext
      intro i
      fin_cases i <;> simp [PiLp.smul_apply]]
    rw [real_inner_smul_right]
    have hx0 : ⟪x -ᵥ ptA, (!₂[0, 1] : Plane)⟫_ℝ = 0 :=
      inner_e2_eq_zero_of_mem_lineAB hx
    have hP0 : ⟪!₂[q, 0] -ᵥ ptA, (!₂[0, 1] : Plane)⟫_ℝ = 0 := by
      rw [vsub_eq_sub]
      simp only [ptA, mk_sub_mk]
      rw [inner_mk]
      ring
    have e3 : (x -ᵥ !₂[q, 0] : Plane) = (x -ᵥ ptA) - (!₂[q, 0] -ᵥ ptA) := by
      rw [vsub_eq_sub, vsub_eq_sub, vsub_eq_sub]
      abel
    rw [e3, inner_sub_left, hx0, hP0]
    ring

/-- The line `AB` is the known common tangent of the three circles: it touches
the incircle `K1` at `((b + c - a)/2, 0)`, `K2` at `(c - a, 0)` and `K3` at
`(b, 0)`. -/
theorem common_tangent_AB (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a ^ 2 + b ^ 2 = c ^ 2) :
    (K1 a b c).IsTangent line[ℝ, ptA, ptB c] ∧
    (K2 a b c).IsTangent line[ℝ, ptA, ptB c] ∧
    (K3 a b c).IsTangent line[ℝ, ptA, ptB c] := by
  have hr1 : 0 < r1 a b c := r1_pos ha hb hc h
  have hr2 : 0 < r2 a b c := r2_pos ha hb hc h
  have hr3 : 0 < r3 a b c := r3_pos ha hb hc h
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨!₂[(b + c - a) / 2, 0], isTangentAt_lineAB _ _ hr1 hc⟩
  · exact ⟨!₂[c - a, 0], isTangentAt_lineAB _ _ hr2 hc⟩
  · exact ⟨!₂[b, 0], isTangentAt_lineAB _ _ hr3 hc⟩

snip end

problem imo1969_p4 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a ^ 2 + b ^ 2 = c ^ 2) :
    ∃ L : AffineSubspace ℝ Plane,
      Module.finrank ℝ L.direction = 1 ∧ L ≠ line[ℝ, ptA, ptB c] ∧
      (K1 a b c).IsTangent L ∧ (K2 a b c).IsTangent L ∧
      (K3 a b c).IsTangent L := by
  have hr1 : 0 < r1 a b c := r1_pos ha hb hc h
  have hr2 : 0 < r2 a b c := r2_pos ha hb hc h
  have hr3 : 0 < r3 a b c := r3_pos ha hb hc h
  have hN : 0 < uN a b c := uN_pos hr2 hr3
  have hu : ⟪uVec a b c, uVec a b c⟫_ℝ = 1 := inner_uVec hr2 hr3
  have hunorm : ‖uVec a b c‖ = 1 := by
    rw [norm_eq_sqrt_real_inner, hu, Real.sqrt_one]
  have hu0 : uVec a b c ≠ 0 := by
    intro hz
    rw [hz, inner_zero_left] at hu
    exact zero_ne_one hu
  have h21 : ⟪O2 a b c - O1 a b c, uVec a b c⟫_ℝ = r1 a b c - r2 a b c :=
    inner_O2_sub_O1 hc h hr2 hr3
  have h32 : ⟪O3 a b c - O2 a b c, uVec a b c⟫_ℝ = r2 a b c - r3 a b c :=
    inner_O3_sub_O2 hc h hr2 hr3
  have h31 : ⟪O3 a b c - O1 a b c, uVec a b c⟫_ℝ = r1 a b c - r3 a b c :=
    inner_O3_sub_O1 hc h hr2 hr3
  -- The tangent points of the second common tangent on the three circles.
  set T1 : Plane := r1 a b c • uVec a b c +ᵥ O1 a b c with hT1def
  set T2 : Plane := r2 a b c • uVec a b c +ᵥ O2 a b c with hT2def
  set T3 : Plane := r3 a b c • uVec a b c +ᵥ O3 a b c with hT3def
  -- The second common tangent line: the tangent line of `K1` at `T1`.
  set L : AffineSubspace ℝ Plane := (K1 a b c).orthRadius T1 with hLdef
  have hT1K1 : T1 ∈ K1 a b c := by
    rw [mem_sphere, hT1def]
    show dist (r1 a b c • uVec a b c +ᵥ O1 a b c) (O1 a b c) = r1 a b c
    rw [dist_eq_norm_vsub, vadd_vsub, norm_smul, hunorm, mul_one]
    rw [Real.norm_eq_abs, abs_of_nonneg hr1.le]
  have hT2K2 : T2 ∈ K2 a b c := by
    rw [mem_sphere, hT2def]
    show dist (r2 a b c • uVec a b c +ᵥ O2 a b c) (O2 a b c) = r2 a b c
    rw [dist_eq_norm_vsub, vadd_vsub, norm_smul, hunorm, mul_one]
    rw [Real.norm_eq_abs, abs_of_nonneg hr2.le]
  have hT3K3 : T3 ∈ K3 a b c := by
    rw [mem_sphere, hT3def]
    show dist (r3 a b c • uVec a b c +ᵥ O3 a b c) (O3 a b c) = r3 a b c
    rw [dist_eq_norm_vsub, vadd_vsub, norm_smul, hunorm, mul_one]
    rw [Real.norm_eq_abs, abs_of_nonneg hr3.le]
  -- The differences of the tangent points, in terms of the centers.
  have e21 : (T2 -ᵥ T1 : Plane) =
      (O2 a b c - O1 a b c) + (r2 a b c - r1 a b c) • uVec a b c := by
    rw [hT2def, hT1def, vadd_eq_add, vadd_eq_add, vsub_eq_sub]
    module
  have e31 : (T3 -ᵥ T1 : Plane) =
      (O3 a b c - O1 a b c) + (r3 a b c - r1 a b c) • uVec a b c := by
    rw [hT3def, hT1def, vadd_eq_add, vadd_eq_add, vsub_eq_sub]
    module
  have hT2L : T2 ∈ L := by
    rw [hLdef, Sphere.mem_orthRadius_iff_inner_left]
    show ⟪T2 -ᵥ T1, T1 -ᵥ O1 a b c⟫_ℝ = 0
    rw [e21, hT1def, vadd_vsub]
    simp only [inner_add_left, real_inner_smul_left, real_inner_smul_right]
    rw [h21, hu]
    ring
  have hT3L : T3 ∈ L := by
    rw [hLdef, Sphere.mem_orthRadius_iff_inner_left]
    show ⟪T3 -ᵥ T1, T1 -ᵥ O1 a b c⟫_ℝ = 0
    rw [e31, hT1def, vadd_vsub]
    simp only [inner_add_left, real_inner_smul_left, real_inner_smul_right]
    rw [h31, hu]
    ring
  -- The line `L` is also the tangent line of `K2` at `T2` and of `K3` at `T3`.
  have hle2 : L ≤ (K2 a b c).orthRadius T2 := by
    intro x hx
    rw [hLdef, Sphere.mem_orthRadius_iff_inner_left] at hx
    replace hx : ⟪x -ᵥ T1, T1 -ᵥ O1 a b c⟫_ℝ = 0 := hx
    rw [hT1def, vadd_vsub, real_inner_smul_right] at hx
    have hx' : ⟪x -ᵥ T1, uVec a b c⟫_ℝ = 0 :=
      (mul_eq_zero.mp hx).resolve_left hr1.ne'
    rw [Sphere.mem_orthRadius_iff_inner_left]
    show ⟪x -ᵥ T2, T2 -ᵥ O2 a b c⟫_ℝ = 0
    have e2 : (x -ᵥ T2 : Plane) = (x -ᵥ T1) - (T2 -ᵥ T1) := by
      rw [vsub_eq_sub, vsub_eq_sub, vsub_eq_sub]
      abel
    rw [e2, e21, hT2def, vadd_vsub]
    rw [inner_sub_left]
    simp only [inner_add_left, real_inner_smul_left, real_inner_smul_right]
    rw [hx', h21, hu]
    ring
  have hle3 : L ≤ (K3 a b c).orthRadius T3 := by
    intro x hx
    rw [hLdef, Sphere.mem_orthRadius_iff_inner_left] at hx
    replace hx : ⟪x -ᵥ T1, T1 -ᵥ O1 a b c⟫_ℝ = 0 := hx
    rw [hT1def, vadd_vsub, real_inner_smul_right] at hx
    have hx' : ⟪x -ᵥ T1, uVec a b c⟫_ℝ = 0 :=
      (mul_eq_zero.mp hx).resolve_left hr1.ne'
    rw [Sphere.mem_orthRadius_iff_inner_left]
    show ⟪x -ᵥ T3, T3 -ᵥ O3 a b c⟫_ℝ = 0
    have e2 : (x -ᵥ T3 : Plane) = (x -ᵥ T1) - (T3 -ᵥ T1) := by
      rw [vsub_eq_sub, vsub_eq_sub, vsub_eq_sub]
      abel
    rw [e2, e31, hT3def, vadd_vsub]
    rw [inner_sub_left]
    simp only [inner_add_left, real_inner_smul_left, real_inner_smul_right]
    rw [hx', h31, hu]
    ring
  -- `L` is one-dimensional.
  have hfin : Module.finrank ℝ L.direction = 1 := by
    haveI : Fact (Module.finrank ℝ Plane = 1 + 1) :=
      ⟨by rw [finrank_euclideanSpace, Fintype.card_fin]⟩
    rw [hLdef, Sphere.direction_orthRadius]
    show Module.finrank ℝ ((ℝ ∙ (T1 -ᵥ O1 a b c))ᗮ : Submodule ℝ Plane) = 1
    rw [hT1def, vadd_vsub,
      Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hr1.ne')]
    exact Submodule.finrank_orthogonal_span_singleton hu0
  -- `L` differs from the line `AB`, because `T1 ∈ L` lies strictly above it.
  have hne : L ≠ line[ℝ, ptA, ptB c] := by
    intro hLeq
    have hT1L : T1 ∈ L := by
      rw [hLdef]
      exact Sphere.self_mem_orthRadius _ _
    have hT1in : T1 ∈ line[ℝ, ptA, ptB c] := hLeq ▸ hT1L
    have key : ⟪T1 -ᵥ ptA, (!₂[0, 1] : Plane)⟫_ℝ = 0 :=
      inner_e2_eq_zero_of_mem_lineAB hT1in
    have hpos : (0:ℝ) < ⟪T1 -ᵥ ptA, (!₂[0, 1] : Plane)⟫_ℝ := by
      have e : (T1 -ᵥ ptA : Plane) =
          !₂[(b + c - a) / 2 + r1 a b c * ((r2 a b c ^ 2 - r3 a b c ^ 2) / uN a b c),
             r1 a b c + r1 a b c * (2 * r2 a b c * r3 a b c / uN a b c)] := by
        rw [hT1def, vadd_eq_add, vsub_eq_sub]
        apply PiLp.ext
        intro i
        fin_cases i <;>
          simp [ptA, O1, uVec, PiLp.sub_apply, PiLp.add_apply,
            PiLp.smul_apply] <;> ring
      rw [e, inner_mk]
      simp only [mul_zero, mul_one]
      positivity
    rw [key] at hpos
    exact lt_irrefl 0 hpos
  exact ⟨L, hfin, hne,
    ⟨T1, Sphere.isTangentAt_orthRadius_iff_mem.mpr hT1K1⟩,
    ⟨T2, hT2K2, hT2L, hle2⟩,
    ⟨T3, hT3K3, hT3L, hle3⟩⟩

end Imo1969P4
