/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Geometry.Euclidean.Sphere.Tangent
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 2026, Problem 3

Let `ABC` be an acute scalene triangle with no angle equal to `60°`. Let `ω` be the
circumcircle of `ABC`. Let `ΔB` be the equilateral triangle with three vertices on `ω`,
one of which is `B`. Let `ℓB` be the line through the two vertices of `ΔB` other than `B`.
Let `ΔC` and `ℓC` be defined analogously. Let `Y` be the intersection of `AC` and `ℓB`,
and let `Z` be the intersection of `AB` and `ℓC`.
Let `N` be the midpoint of minor arc `BC` on `ω`. Let `R` be the triangle formed by `ℓB`,
`ℓC`, and the tangent to `ω` through `N`. Prove that the circumcircle of `AYZ` and the
incircle of `R` are tangent.

## Formalization

We work in Cartesian coordinates on `EuclideanSpace ℝ (Fin 2)`.  Every configuration
satisfying the hypotheses can be moved by a similarity transformation (a composition of a
translation, a rotation and a scaling, all of which preserve every construction and the
tangency assertion of the problem) to one in which `ω` is the unit circle centered at the
origin and `N = (1, 0)`.  Since `N` is the midpoint of the minor arc `BC`, the points `B`
and `C` are symmetric about the x-axis, and the central angle `∠BOC` equals `2α` where
`α = ∠A`.  Writing `δ = ∠C − ∠B`, the vertex `A` has argument `π + δ`.  Thus, with
`c = cos α`, `s = sin α`, `p = cos δ`, `q = sin δ`:

* `B = (c, s)`, `C = (c, -s)`, `A = (-p, -q)`, `N = (1, 0)`;
* the hypotheses "acute, scalene, no `60°` angle" become
  `0 < α < π/2`, `α ≠ π/3`, `|δ| < α`, `δ ≠ 0`, `δ ≠ ±(π - 3α)`, `δ ≠ ±(π/3 - α)`
  (note `∠B = (π - α - δ)/2` and `∠C = (π - α + δ)/2`);
* the other two vertices of the inscribed equilateral triangle on `B` are the rotations
  of `B` about the origin by `±120°`, and the line `ℓB` through them has equation
  `c * x + s * y = -1/2`; similarly `ℓC : c * x - s * y = -1/2`;
* the tangent to `ω` at `N` is the line `x = 1`.

The proof then follows the analytic solution (coordinates) attributed to GPT-5.5's
perfect-score attempt at the MathArena USAMO 2026 evaluation: the circumcircle of `AYZ`
has equation `x² + y² - 1 + λ * ((2cp - 1) * x + 2cq * y + 2c - p) = 0` with
`λ = (4c² - 1)/(p + cos 3α)`, the incircle of `R` has center `(1/(2(1+c)), 0)` and radius
`(2c+1)/(2(1+c))`, and the radical axis of the two circles is tangent to the incircle,
so the two circles meet in exactly one point.
-/

namespace Usa2026P3

open Real RealInnerProductSpace

/-- The Euclidean plane. -/
abbrev Pln := EuclideanSpace ℝ (Fin 2)

/-- Vertex `A` on the unit circle, at angle `π + δ`. -/
noncomputable def ptA (δ : ℝ) : Pln := !₂[-Real.cos δ, -Real.sin δ]

/-- Vertex `B` on the unit circle, at angle `α`. -/
noncomputable def ptB (α : ℝ) : Pln := !₂[Real.cos α, Real.sin α]

/-- Vertex `C` on the unit circle, at angle `-α`. -/
noncomputable def ptC (α : ℝ) : Pln := !₂[Real.cos α, -Real.sin α]

/-- The midpoint `N` of the minor arc `BC`, at angle `0`. -/
noncomputable def ptN : Pln := !₂[1, 0]

/-- The second vertex of the equilateral triangle inscribed in the unit circle with
vertex `B`: the rotation of `B` about the origin by `120°`. -/
noncomputable def rotB1 (α : ℝ) : Pln :=
  !₂[-Real.cos α / 2 - Real.sin α * Real.sqrt 3 / 2,
     Real.cos α * Real.sqrt 3 / 2 - Real.sin α / 2]

/-- The third vertex of the inscribed equilateral triangle on `B`: rotation by `-120°`. -/
noncomputable def rotB2 (α : ℝ) : Pln :=
  !₂[-Real.cos α / 2 + Real.sin α * Real.sqrt 3 / 2,
     -Real.cos α * Real.sqrt 3 / 2 - Real.sin α / 2]

/-- The second vertex of the inscribed equilateral triangle on `C`: rotation by `120°`. -/
noncomputable def rotC1 (α : ℝ) : Pln :=
  !₂[-Real.cos α / 2 + Real.sin α * Real.sqrt 3 / 2,
     Real.cos α * Real.sqrt 3 / 2 + Real.sin α / 2]

/-- The third vertex of the inscribed equilateral triangle on `C`: rotation by `-120°`. -/
noncomputable def rotC2 (α : ℝ) : Pln :=
  !₂[-Real.cos α / 2 - Real.sin α * Real.sqrt 3 / 2,
     -Real.cos α * Real.sqrt 3 / 2 + Real.sin α / 2]

/-- The line `ℓB` through the two vertices of `ΔB` other than `B`. -/
noncomputable def lineB (α : ℝ) : AffineSubspace ℝ Pln := affineSpan ℝ {rotB1 α, rotB2 α}

/-- The line `ℓC` through the two vertices of `ΔC` other than `C`. -/
noncomputable def lineC (α : ℝ) : AffineSubspace ℝ Pln := affineSpan ℝ {rotC1 α, rotC2 α}

/-- The tangent to the unit circle at `N`: the vertical line `x = 1`. -/
noncomputable def tangentN : AffineSubspace ℝ Pln :=
  AffineSubspace.mk' ptN (Submodule.span ℝ {!₂[0, 1]})

/-- The unit circle, i.e. the circumcircle `ω`. -/
noncomputable def unitω : EuclideanGeometry.Sphere Pln := ⟨0, 1⟩

/-- The parameter of `Y` on line `AC`, i.e. `Y = A + muY • (C - A)`. -/
noncomputable def muY (α δ : ℝ) : ℝ :=
  (Real.cos (α - δ) - 1 / 2) / (Real.cos (2 * α) + Real.cos (α - δ))

/-- The intersection `Y` of `AC` and `ℓB`. -/
noncomputable def ptY (α δ : ℝ) : Pln :=
  !₂[-Real.cos δ + muY α δ * (Real.cos α + Real.cos δ),
     -Real.sin δ + muY α δ * (Real.sin δ - Real.sin α)]

/-- The parameter of `Z` on line `AB`, i.e. `Z = A + muZ • (B - A)`. -/
noncomputable def muZ (α δ : ℝ) : ℝ :=
  (Real.cos (α + δ) - 1 / 2) / (Real.cos (2 * α) + Real.cos (α + δ))

/-- The intersection `Z` of `AB` and `ℓC`. -/
noncomputable def ptZ (α δ : ℝ) : Pln :=
  !₂[-Real.cos δ + muZ α δ * (Real.cos α + Real.cos δ),
     -Real.sin δ + muZ α δ * (Real.sin α + Real.sin δ)]

/-- The factor `λ = (4c² - 1)/(p + cos 3α)` in the equation of the circumcircle of
`AYZ`. -/
noncomputable def lam (α δ : ℝ) : ℝ :=
  (4 * Real.cos α ^ 2 - 1) / (Real.cos δ + Real.cos (3 * α))

/-- The `x`-coefficient of the normalized equation `x² + y² + D x + E y + F = 0` of the
circumcircle of `AYZ`. -/
noncomputable def coeffD (α δ : ℝ) : ℝ :=
  lam α δ * (2 * Real.cos α * Real.cos δ - 1)

/-- The `y`-coefficient of the circumcircle of `AYZ`. -/
noncomputable def coeffE (α δ : ℝ) : ℝ := lam α δ * (2 * Real.cos α * Real.sin δ)

/-- The constant term of the circumcircle of `AYZ`. -/
noncomputable def coeffF (α δ : ℝ) : ℝ :=
  -1 + lam α δ * (2 * Real.cos α - Real.cos δ)

/-- The circumcircle of `AYZ`. -/
noncomputable def circumΓ (α δ : ℝ) : EuclideanGeometry.Sphere Pln :=
  ⟨!₂[-coeffD α δ / 2, -coeffE α δ / 2],
    Real.sqrt (coeffD α δ ^ 2 / 4 + coeffE α δ ^ 2 / 4 - coeffF α δ)⟩

/-- The x-coordinate of the incenter of `R`. -/
noncomputable def inH (α : ℝ) : ℝ := 1 / (2 * (1 + Real.cos α))

/-- The inradius of `R`. -/
noncomputable def inR (α : ℝ) : ℝ := (2 * Real.cos α + 1) / (2 * (1 + Real.cos α))

/-- The incircle of the triangle `R` formed by `ℓB`, `ℓC` and the tangent at `N`. -/
noncomputable def incircleι (α : ℝ) : EuclideanGeometry.Sphere Pln := ⟨!₂[inH α, 0], inR α⟩

/-- The `x`-coefficient of the radical axis of `circumΓ` and `incircleι`. -/
noncomputable def radA (α δ : ℝ) : ℝ := coeffD α δ + 2 * inH α

/-- The `y`-coefficient of the radical axis. -/
noncomputable def radB (α δ : ℝ) : ℝ := coeffE α δ

/-- The constant term of the radical axis. -/
noncomputable def radC (α δ : ℝ) : ℝ := coeffF α δ - inH α ^ 2 + inR α ^ 2

snip begin

section helpers

lemma dist_eq_sqrt (P Q : Pln) :
    dist P Q = Real.sqrt ((P 0 - Q 0) ^ 2 + (P 1 - Q 1) ^ 2) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]

lemma inner_eq (P Q : Pln) : ⟪P, Q⟫ = P 0 * Q 0 + P 1 * Q 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp [RCLike.inner_apply]
  ring

lemma Pln_ext {P Q : Pln} (h : ∀ i, P i = Q i) : P = Q :=
  WithLp.ofLp_injective _ (funext h)

lemma mem_sphere_iff_sq {K : Pln} {ρ : ℝ} (hρ : 0 ≤ ρ) (P : Pln) :
    P ∈ (⟨K, ρ⟩ : EuclideanGeometry.Sphere Pln) ↔
    (P 0 - K 0) ^ 2 + (P 1 - K 1) ^ 2 = ρ ^ 2 := by
  rw [EuclideanGeometry.mem_sphere, dist_eq_sqrt]
  exact Real.sqrt_eq_iff_eq_sq (by positivity) hρ

lemma add_smul_sub_mem_affineSpan_pair {R S : Pln} (k : ℝ) :
    R + k • (S - R) ∈ affineSpan ℝ ({R, S} : Set Pln) := by
  have h : AffineMap.lineMap R S k ∈ affineSpan ℝ ({R, S} : Set Pln) :=
    AffineMap.lineMap_mem_affineSpan_pair _ _ _
  rwa [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm] at h

/-- A point on line `RS` differs from `R` by a multiple of `S -ᵥ R`
(copied from `Usa2025P4`). -/
lemma vsub_smul_of_mem_pair {R S Q : Pln}
    (hQ : Q ∈ affineSpan ℝ ({R, S} : Set Pln)) :
    ∃ k : ℝ, Q -ᵥ R = k • (S -ᵥ R) := by
  have hmem : Q -ᵥ R ∈ vectorSpan ℝ ({R, S} : Set Pln) := by
    rw [← direction_affineSpan]
    exact AffineSubspace.vsub_mem_direction hQ (left_mem_affineSpan_pair ℝ R S)
  rw [vectorSpan_pair] at hmem
  obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hmem
  exact ⟨-k, by rw [← hk, neg_smul, ← smul_neg, neg_vsub_eq_vsub_rev]⟩

end helpers

section trig

variable {α δ : ℝ}

lemma hcs : Real.cos α ^ 2 + Real.sin α ^ 2 = 1 := Real.cos_sq_add_sin_sq α

lemma hpq : Real.cos δ ^ 2 + Real.sin δ ^ 2 = 1 := Real.cos_sq_add_sin_sq δ

lemma hσ : Real.cos (α - δ) = Real.cos α * Real.cos δ + Real.sin α * Real.sin δ :=
  Real.cos_sub α δ

lemma hρ : Real.cos (α + δ) = Real.cos α * Real.cos δ - Real.sin α * Real.sin δ :=
  Real.cos_add α δ

lemma hτ : Real.cos (2 * α) = 2 * Real.cos α ^ 2 - 1 := Real.cos_two_mul α

lemma hg : Real.cos (3 * α) = 4 * Real.cos α ^ 3 - 3 * Real.cos α := Real.cos_three_mul α

lemma hc_pos (hα0 : 0 < α) (hα1 : α < Real.pi / 2) : 0 < Real.cos α := by
  apply Real.cos_pos_of_mem_Ioo
  rw [Set.mem_Ioo]
  constructor <;> linarith [Real.pi_pos]

lemma hs_pos (hα0 : 0 < α) (hα1 : α < Real.pi / 2) : 0 < Real.sin α := by
  apply Real.sin_pos_of_pos_of_lt_pi hα0
  linarith [Real.pi_pos]

lemma h1c_pos (hα0 : 0 < α) (hα1 : α < Real.pi / 2) : 0 < 1 + Real.cos α := by
  have := hc_pos hα0 hα1
  linarith

lemma hq_ne (hα1 : α < Real.pi / 2) (hδabs : |δ| < α) (hδ0 : δ ≠ 0) :
    Real.sin δ ≠ 0 := by
  have h1 : -Real.pi < δ := by
    have h2 : |δ| < Real.pi / 2 := lt_trans hδabs hα1
    rw [abs_lt] at h2
    linarith [Real.pi_pos]
  have h2 : δ < Real.pi := by
    have h3 : |δ| < Real.pi / 2 := lt_trans hδabs hα1
    rw [abs_lt] at h3
    linarith [Real.pi_pos]
  intro hsin
  rw [Real.sin_eq_zero_iff_of_lt_of_lt h1 h2] at hsin
  exact hδ0 hsin

lemma hT_ne (hα0 : 0 < α) (hα1 : α < Real.pi / 2) (hα60 : α ≠ Real.pi / 3) :
    4 * Real.cos α ^ 2 - 1 ≠ 0 := by
  have hc : 0 < Real.cos α := hc_pos hα0 hα1
  intro h
  have h2 : Real.cos α = 1 / 2 := by nlinarith [h]
  have h3 : α = Real.pi / 3 := by
    have e : Real.cos α = Real.cos (Real.pi / 3) := by rw [h2, Real.cos_pi_div_three]
    exact Real.injOn_cos (Set.mem_Icc.mpr ⟨le_of_lt hα0, by linarith [Real.pi_pos]⟩)
      (Set.mem_Icc.mpr ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩) e
  exact hα60 h3

lemma hpg_ne (hα0 : 0 < α) (hα1 : α < Real.pi / 2)
    (hδabs : |δ| < α) (hδβ : δ ≠ Real.pi - 3 * α) (hδγ : δ ≠ -(Real.pi - 3 * α)) :
    Real.cos δ + Real.cos (3 * α) ≠ 0 := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hδlt : |δ| < Real.pi / 2 := lt_trans hδabs hα1
  rw [abs_lt] at hδlt
  intro h
  have h1 : Real.cos δ = Real.cos (Real.pi - 3 * α) := by
    rw [Real.cos_pi_sub]; linarith [h]
  rw [Real.cos_eq_cos_iff] at h1
  obtain ⟨k, hk | hk⟩ := h1
  · rcases lt_trichotomy k 0 with hkn | hk0 | hkp
    · have hk' : (k : ℝ) ≤ -1 := by exact_mod_cast (by omega : (k : ℤ) ≤ -1)
      nlinarith [hα0, hα1]
    · subst hk0; simp at hk; exact hδβ (by linarith [hk])
    · have hk' : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : (1 : ℤ) ≤ k)
      nlinarith [hα0, hα1]
  · rcases lt_trichotomy k 0 with hkn | hk0 | hkp
    · have hk' : (k : ℝ) ≤ -1 := by exact_mod_cast (by omega : (k : ℤ) ≤ -1)
      nlinarith [hα0, hα1]
    · subst hk0; simp at hk; exact hδγ (by linarith [hk])
    · have hk' : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : (1 : ℤ) ≤ k)
      nlinarith [hα0, hα1]

lemma hts_ne (hα0 : 0 < α) (hα1 : α < Real.pi / 2)
    (hδabs : |δ| < α) (hδγ : δ ≠ -(Real.pi - 3 * α)) :
    Real.cos (2 * α) + Real.cos (α - δ) ≠ 0 := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hδlt : |δ| < Real.pi / 2 := lt_trans hδabs hα1
  rw [abs_lt] at hδlt
  intro h
  rw [Real.cos_add_cos] at h
  have e1 : (2 * α + (α - δ)) / 2 = (3 * α - δ) / 2 := by ring
  have e2 : (2 * α - (α - δ)) / 2 = (α + δ) / 2 := by ring
  rw [e1, e2] at h
  have h2 : Real.cos ((3 * α - δ) / 2) * Real.cos ((α + δ) / 2) = 0 := by linarith [h]
  have hpos : 0 < Real.cos ((α + δ) / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    rw [Set.mem_Ioo]
    constructor <;> linarith [hα0]
  have hz : Real.cos ((3 * α - δ) / 2) = 0 := by
    rcases mul_eq_zero.mp h2 with hzl | hzr
    · exact hzl
    · linarith [hpos]
  rw [Real.cos_eq_zero_iff] at hz
  obtain ⟨k, hk⟩ := hz
  have hδv : δ = 3 * α - (2 * k + 1) * Real.pi := by
    linarith [hk]
  rcases lt_trichotomy k 0 with hkn | hk0 | hkp
  · have hk' : (2 * k + 1 : ℝ) ≤ -1 := by
      exact_mod_cast (by omega : (2 * k + 1 : ℤ) ≤ -1)
    nlinarith [hα0, hα1]
  · subst hk0; simp at hδv; exact hδγ (by linarith [hδv])
  · have hk' : (3 : ℝ) ≤ 2 * k + 1 := by
      exact_mod_cast (by omega : (3 : ℤ) ≤ 2 * k + 1)
    nlinarith [hα0, hα1]

lemma htr_ne (hα0 : 0 < α) (hα1 : α < Real.pi / 2)
    (hδabs : |δ| < α) (hδβ : δ ≠ Real.pi - 3 * α) :
    Real.cos (2 * α) + Real.cos (α + δ) ≠ 0 := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hδlt : |δ| < Real.pi / 2 := lt_trans hδabs hα1
  rw [abs_lt] at hδlt
  intro h
  rw [Real.cos_add_cos] at h
  have e1 : (2 * α + (α + δ)) / 2 = (3 * α + δ) / 2 := by ring
  have e2 : (2 * α - (α + δ)) / 2 = (α - δ) / 2 := by ring
  rw [e1, e2] at h
  have h2 : Real.cos ((3 * α + δ) / 2) * Real.cos ((α - δ) / 2) = 0 := by linarith [h]
  have hpos : 0 < Real.cos ((α - δ) / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    rw [Set.mem_Ioo]
    constructor <;> linarith [hα0]
  have hz : Real.cos ((3 * α + δ) / 2) = 0 := by
    rcases mul_eq_zero.mp h2 with hzl | hzr
    · exact hzl
    · linarith [hpos]
  rw [Real.cos_eq_zero_iff] at hz
  obtain ⟨k, hk⟩ := hz
  have hδv : δ = (2 * k + 1) * Real.pi - 3 * α := by
    linarith [hk]
  rcases lt_trichotomy k 0 with hkn | hk0 | hkp
  · have hk' : (2 * k + 1 : ℝ) ≤ -1 := by
      exact_mod_cast (by omega : (2 * k + 1 : ℤ) ≤ -1)
    nlinarith [hα0, hα1]
  · subst hk0; simp at hδv; exact hδβ (by linarith [hδv])
  · have hk' : (3 : ℝ) ≤ 2 * k + 1 := by
      exact_mod_cast (by omega : (3 : ℤ) ≤ 2 * k + 1)
    nlinarith [hα0, hα1]

end trig

section distcerts

variable {α δ : ℝ}

lemma sqrt3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

lemma sqrt3_sq' : Real.sqrt 3 ^ 2 - 3 = 0 := sub_eq_zero_of_eq sqrt3_sq

lemma dist_ptA : dist (ptA δ) 0 = 1 := by
  rw [dist_eq_sqrt]
  have e : ((ptA δ) 0 - (0 : Pln) 0) ^ 2 + ((ptA δ) 1 - (0 : Pln) 1) ^ 2 = 1 := by
    simp [ptA]
  rw [e, Real.sqrt_one]

lemma dist_ptB : dist (ptB α) 0 = 1 := by
  rw [dist_eq_sqrt]
  have e : ((ptB α) 0 - (0 : Pln) 0) ^ 2 + ((ptB α) 1 - (0 : Pln) 1) ^ 2 = 1 := by
    simp [ptB]
  rw [e, Real.sqrt_one]

lemma dist_ptC : dist (ptC α) 0 = 1 := by
  rw [dist_eq_sqrt]
  have e : ((ptC α) 0 - (0 : Pln) 0) ^ 2 + ((ptC α) 1 - (0 : Pln) 1) ^ 2 = 1 := by
    simp [ptC]
  rw [e, Real.sqrt_one]

lemma dist_ptN : dist ptN 0 = 1 := by
  rw [dist_eq_sqrt]
  have e : (ptN 0 - (0 : Pln) 0) ^ 2 + (ptN 1 - (0 : Pln) 1) ^ 2 = 1 := by
    simp [ptN]
  rw [e, Real.sqrt_one]

lemma dist_rotB1 : dist (rotB1 α) 0 = 1 := by
  rw [dist_eq_sqrt]
  have e : ((rotB1 α) 0 - (0 : Pln) 0) ^ 2 + ((rotB1 α) 1 - (0 : Pln) 1) ^ 2 = 1 := by
    simp only [rotB1]
    simp
    linear_combination hcs (α := α) +
      (Real.cos α ^ 2 + Real.sin α ^ 2) / 4 * sqrt3_sq'
  rw [e, Real.sqrt_one]

lemma dist_rotB2 : dist (rotB2 α) 0 = 1 := by
  rw [dist_eq_sqrt]
  have e : ((rotB2 α) 0 - (0 : Pln) 0) ^ 2 + ((rotB2 α) 1 - (0 : Pln) 1) ^ 2 = 1 := by
    simp only [rotB2]
    simp
    linear_combination hcs (α := α) +
      (Real.cos α ^ 2 + Real.sin α ^ 2) / 4 * sqrt3_sq'
  rw [e, Real.sqrt_one]

lemma dist_rotC1 : dist (rotC1 α) 0 = 1 := by
  rw [dist_eq_sqrt]
  have e : ((rotC1 α) 0 - (0 : Pln) 0) ^ 2 + ((rotC1 α) 1 - (0 : Pln) 1) ^ 2 = 1 := by
    simp only [rotC1]
    simp
    linear_combination hcs (α := α) +
      (Real.cos α ^ 2 + Real.sin α ^ 2) / 4 * sqrt3_sq'
  rw [e, Real.sqrt_one]

lemma dist_rotC2 : dist (rotC2 α) 0 = 1 := by
  rw [dist_eq_sqrt]
  have e : ((rotC2 α) 0 - (0 : Pln) 0) ^ 2 + ((rotC2 α) 1 - (0 : Pln) 1) ^ 2 = 1 := by
    simp only [rotC2]
    simp
    linear_combination hcs (α := α) +
      (Real.cos α ^ 2 + Real.sin α ^ 2) / 4 * sqrt3_sq'
  rw [e, Real.sqrt_one]

lemma dist_ptB_rotB1 : dist (ptB α) (rotB1 α) = Real.sqrt 3 := by
  rw [dist_eq_sqrt]
  have e : ((ptB α) 0 - (rotB1 α) 0) ^ 2 + ((ptB α) 1 - (rotB1 α) 1) ^ 2 = 3 := by
    simp only [ptB, rotB1]
    simp
    linear_combination (3 : ℝ) * hcs (α := α) +
      (Real.cos α ^ 2 + Real.sin α ^ 2) / 4 * sqrt3_sq'
  rw [e]

lemma dist_ptB_rotB2 : dist (ptB α) (rotB2 α) = Real.sqrt 3 := by
  rw [dist_eq_sqrt]
  have e : ((ptB α) 0 - (rotB2 α) 0) ^ 2 + ((ptB α) 1 - (rotB2 α) 1) ^ 2 = 3 := by
    simp only [ptB, rotB2]
    simp
    linear_combination (3 : ℝ) * hcs (α := α) +
      (Real.cos α ^ 2 + Real.sin α ^ 2) / 4 * sqrt3_sq'
  rw [e]

lemma dist_rotB1_rotB2 : dist (rotB1 α) (rotB2 α) = Real.sqrt 3 := by
  rw [dist_eq_sqrt]
  have e : ((rotB1 α) 0 - (rotB2 α) 0) ^ 2 + ((rotB1 α) 1 - (rotB2 α) 1) ^ 2 = 3 := by
    simp only [rotB1, rotB2]
    simp
    linear_combination (3 : ℝ) * hcs (α := α) +
      (Real.cos α ^ 2 + Real.sin α ^ 2) * sqrt3_sq'
  rw [e]

lemma dist_ptC_rotC1 : dist (ptC α) (rotC1 α) = Real.sqrt 3 := by
  rw [dist_eq_sqrt]
  have e : ((ptC α) 0 - (rotC1 α) 0) ^ 2 + ((ptC α) 1 - (rotC1 α) 1) ^ 2 = 3 := by
    simp only [ptC, rotC1]
    simp
    linear_combination (3 : ℝ) * hcs (α := α) +
      (Real.cos α ^ 2 + Real.sin α ^ 2) / 4 * sqrt3_sq'
  rw [e]

lemma dist_ptC_rotC2 : dist (ptC α) (rotC2 α) = Real.sqrt 3 := by
  rw [dist_eq_sqrt]
  have e : ((ptC α) 0 - (rotC2 α) 0) ^ 2 + ((ptC α) 1 - (rotC2 α) 1) ^ 2 = 3 := by
    simp only [ptC, rotC2]
    simp
    linear_combination (3 : ℝ) * hcs (α := α) +
      (Real.cos α ^ 2 + Real.sin α ^ 2) / 4 * sqrt3_sq'
  rw [e]

lemma dist_rotC1_rotC2 : dist (rotC1 α) (rotC2 α) = Real.sqrt 3 := by
  rw [dist_eq_sqrt]
  have e : ((rotC1 α) 0 - (rotC2 α) 0) ^ 2 + ((rotC1 α) 1 - (rotC2 α) 1) ^ 2 = 3 := by
    simp only [rotC1, rotC2]
    simp
    linear_combination (3 : ℝ) * hcs (α := α) +
      (Real.cos α ^ 2 + Real.sin α ^ 2) * sqrt3_sq'
  rw [e]

lemma dist_ptN_ptB_ptC : dist ptN (ptB α) = dist ptN (ptC α) := by
  rw [dist_eq_sqrt, dist_eq_sqrt]
  congr 1
  simp [ptN, ptB, ptC]

lemma ptA_x_lt (hα0 : 0 < α) (hα1 : α < Real.pi / 2) (hδabs : |δ| < α) :
    (ptA δ) 0 < Real.cos α := by
  have hc : 0 < Real.cos α := hc_pos hα0 hα1
  have hd : 0 < Real.cos δ := by
    apply Real.cos_pos_of_mem_Ioo
    rw [Set.mem_Ioo, abs_lt] at *
    constructor <;> linarith [hδabs, Real.pi_pos, hc]
  simp only [ptA]
  simp
  linarith

end distcerts

section cores

/-- The normalized equation `x² + y² + D x + E y + F = 0` of the circumcircle of `AYZ`,
evaluated at `P`. -/
noncomputable def gammaEq (α δ : ℝ) (P : Pln) : ℝ :=
  P 0 ^ 2 + P 1 ^ 2 + coeffD α δ * P 0 + coeffE α δ * P 1 + coeffF α δ

/-- Algebraic core for `Y`: with `μ` and `λ` given by the cleared equations, `Y`
satisfies the circle equation.  The polynomial identities were verified symbolically;
the `linear_combination` certificates are exact. -/
lemma gammaEq_zero_Y {c s p q μ l : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (hpq : p ^ 2 + q ^ 2 = 1)
    (hμ : μ * (2 * c ^ 2 - 1 + (c * p + s * q)) = c * p + s * q - 1 / 2)
    (hl : l * (p + (4 * c ^ 3 - 3 * c)) = 4 * c ^ 2 - 1)
    (hts : 2 * c ^ 2 - 1 + (c * p + s * q) ≠ 0) (hpg : p + (4 * c ^ 3 - 3 * c) ≠ 0) :
    (-p + μ * (c + p)) ^ 2 + (-q + μ * (q - s)) ^ 2 +
      l * (2 * c * p - 1) * (-p + μ * (c + p)) + l * (2 * c * q) * (-q + μ * (q - s)) +
      (-1 + l * (2 * c - p)) = 0 := by
  have hcs' : c ^ 2 + s ^ 2 - 1 = 0 := by linarith [hcs]
  have hpq' : p ^ 2 + q ^ 2 - 1 = 0 := by linarith [hpq]
  have hμ' : μ * (2 * c ^ 2 - 1 + (c * p + s * q)) - (c * p + s * q - 1 / 2) = 0 := by
    linarith [hμ]
  have hl' : l * (p + (4 * c ^ 3 - 3 * c)) - (4 * c ^ 2 - 1) = 0 := by linarith [hl]
  have hPhi : (-p + μ * (c + p)) ^ 2 + (-q + μ * (q - s)) ^ 2 - 1 =
      2 * (1 + (c * p - s * q)) * μ * (μ - 1) := by
    linear_combination (μ ^ 2) * hcs' + ((μ - 1) ^ 2) * hpq'
  have hL : (2 * c * p - 1) * (-p + μ * (c + p)) + 2 * c * q * (-q + μ * (q - s)) +
      (2 * c - p) = μ * (2 * c * (c * p - s * q) + c - p) := by
    linear_combination (2 * c * μ - 2 * c) * hpq'
  have hbrK : (2 * (1 + (c * p - s * q)) * (μ - 1) + l * (2 * c * (c * p - s * q) + c - p)) *
      ((2 * c ^ 2 - 1 + (c * p + s * q)) * (p + (4 * c ^ 3 - 3 * c))) = 0 := by
    linear_combination ((4 * c ^ 2 - 1) * (-2 * c * q ^ 2)) * hcs' +
      ((4 * c ^ 2 - 1) * (2 * c ^ 3 - 2 * c)) * hpq' +
      (2 * (1 + (c * p - s * q)) * (p + (4 * c ^ 3 - 3 * c))) * hμ' +
      ((2 * c * (c * p - s * q) + c - p) * (2 * c ^ 2 - 1 + (c * p + s * q))) * hl'
  have hbr : 2 * (1 + (c * p - s * q)) * (μ - 1) + l * (2 * c * (c * p - s * q) + c - p) = 0 := by
    have hK : (2 * c ^ 2 - 1 + (c * p + s * q)) * (p + (4 * c ^ 3 - 3 * c)) ≠ 0 :=
      mul_ne_zero hts hpg
    rcases mul_eq_zero.mp hbrK with h | h
    · exact h
    · exact absurd h hK
  have hGeq : (-p + μ * (c + p)) ^ 2 + (-q + μ * (q - s)) ^ 2 +
      l * (2 * c * p - 1) * (-p + μ * (c + p)) + l * (2 * c * q) * (-q + μ * (q - s)) +
      (-1 + l * (2 * c - p)) =
      2 * (1 + (c * p - s * q)) * μ * (μ - 1) + l * (μ * (2 * c * (c * p - s * q) + c - p)) := by
    linear_combination hPhi + l * hL
  rw [hGeq]
  have e : 2 * (1 + (c * p - s * q)) * μ * (μ - 1) + l * (μ * (2 * c * (c * p - s * q) + c - p)) =
      μ * (2 * (1 + (c * p - s * q)) * (μ - 1) + l * (2 * c * (c * p - s * q) + c - p)) := by
    ring
  rw [e, hbr, mul_zero]

/-- Algebraic core for `Z` (the mirror image of `gammaEq_zero_Y`). -/
lemma gammaEq_zero_Z {c s p q μ l : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (hpq : p ^ 2 + q ^ 2 = 1)
    (hμ : μ * (2 * c ^ 2 - 1 + (c * p - s * q)) = c * p - s * q - 1 / 2)
    (hl : l * (p + (4 * c ^ 3 - 3 * c)) = 4 * c ^ 2 - 1)
    (hts : 2 * c ^ 2 - 1 + (c * p - s * q) ≠ 0) (hpg : p + (4 * c ^ 3 - 3 * c) ≠ 0) :
    (-p + μ * (c + p)) ^ 2 + (-q + μ * (s + q)) ^ 2 +
      l * (2 * c * p - 1) * (-p + μ * (c + p)) + l * (2 * c * q) * (-q + μ * (s + q)) +
      (-1 + l * (2 * c - p)) = 0 := by
  have hcs' : c ^ 2 + s ^ 2 - 1 = 0 := by linarith [hcs]
  have hpq' : p ^ 2 + q ^ 2 - 1 = 0 := by linarith [hpq]
  have hμ' : μ * (2 * c ^ 2 - 1 + (c * p - s * q)) - (c * p - s * q - 1 / 2) = 0 := by
    linarith [hμ]
  have hl' : l * (p + (4 * c ^ 3 - 3 * c)) - (4 * c ^ 2 - 1) = 0 := by linarith [hl]
  have hPhi : (-p + μ * (c + p)) ^ 2 + (-q + μ * (s + q)) ^ 2 - 1 =
      2 * (1 + (c * p + s * q)) * μ * (μ - 1) := by
    linear_combination (μ ^ 2) * hcs' + ((μ - 1) ^ 2) * hpq'
  have hL : (2 * c * p - 1) * (-p + μ * (c + p)) + 2 * c * q * (-q + μ * (s + q)) +
      (2 * c - p) = μ * (2 * c * (c * p + s * q) + c - p) := by
    linear_combination (2 * c * μ - 2 * c) * hpq'
  have hbrK : (2 * (1 + (c * p + s * q)) * (μ - 1) + l * (2 * c * (c * p + s * q) + c - p)) *
      ((2 * c ^ 2 - 1 + (c * p - s * q)) * (p + (4 * c ^ 3 - 3 * c))) = 0 := by
    linear_combination ((4 * c ^ 2 - 1) * (-2 * c * q ^ 2)) * hcs' +
      ((4 * c ^ 2 - 1) * (2 * c ^ 3 - 2 * c)) * hpq' +
      (2 * (1 + (c * p + s * q)) * (p + (4 * c ^ 3 - 3 * c))) * hμ' +
      ((2 * c * (c * p + s * q) + c - p) * (2 * c ^ 2 - 1 + (c * p - s * q))) * hl'
  have hbr : 2 * (1 + (c * p + s * q)) * (μ - 1) + l * (2 * c * (c * p + s * q) + c - p) = 0 := by
    have hK : (2 * c ^ 2 - 1 + (c * p - s * q)) * (p + (4 * c ^ 3 - 3 * c)) ≠ 0 :=
      mul_ne_zero hts hpg
    rcases mul_eq_zero.mp hbrK with h | h
    · exact h
    · exact absurd h hK
  have hGeq : (-p + μ * (c + p)) ^ 2 + (-q + μ * (s + q)) ^ 2 +
      l * (2 * c * p - 1) * (-p + μ * (c + p)) + l * (2 * c * q) * (-q + μ * (s + q)) +
      (-1 + l * (2 * c - p)) =
      2 * (1 + (c * p + s * q)) * μ * (μ - 1) + l * (μ * (2 * c * (c * p + s * q) + c - p)) := by
    linear_combination hPhi + l * hL
  rw [hGeq]
  have e : 2 * (1 + (c * p + s * q)) * μ * (μ - 1) + l * (μ * (2 * c * (c * p + s * q) + c - p)) =
      μ * (2 * (1 + (c * p + s * q)) * (μ - 1) + l * (2 * c * (c * p + s * q) + c - p)) := by
    ring
  rw [e, hbr, mul_zero]

/-- Algebraic core: the radical axis of the two circles is tangent to the incircle,
expressed as the equality of the squared distance from the incenter to the radical axis
with the squared inradius. -/
lemma incircle_tangent_core {c p q r h l : ℝ} (hpq : p ^ 2 + q ^ 2 = 1)
    (hU : (2 : ℝ) * (1 + c) ≠ 0)
    (hH : h * (2 * (1 + c)) = 1) (hR : r * (2 * (1 + c)) = 2 * c + 1)
    (hl : l * (p + (4 * c ^ 3 - 3 * c)) = 4 * c ^ 2 - 1) :
    ((l * (2 * c * p - 1) + 2 * h) * h + (-1 + l * (2 * c - p) - h ^ 2 + r ^ 2)) ^ 2 =
      r ^ 2 * ((l * (2 * c * p - 1) + 2 * h) ^ 2 + (l * (2 * c * q)) ^ 2) := by
  have hpq' : p ^ 2 + q ^ 2 - 1 = 0 := by linarith [hpq]
  have hH' : h * (2 * (1 + c)) - 1 = 0 := by linarith [hH]
  have hR' : r * (2 * (1 + c)) - (2 * c + 1) = 0 := by linarith [hR]
  have hl' : l * (p + (4 * c ^ 3 - 3 * c)) - (4 * c ^ 2 - 1) = 0 := by linarith [hl]
  have hrh : r + h - 1 = 0 := by
    have e : (r + h - 1) * (2 * (1 + c)) = 0 := by linear_combination hR' + hH'
    rcases mul_eq_zero.mp e with h1 | h2
    · linarith [h1]
    · exact absurd h2 hU
  have hC0 : 2 * h - 1 - h ^ 2 + r ^ 2 = 0 := by
    have e : (2 * h - 1 - h ^ 2 + r ^ 2) * (2 * (1 + c)) = 0 := by
      linear_combination (1 - h) * hH' + r * hR' + (2 * c + 1) * hrh
    rcases mul_eq_zero.mp e with h1 | h2
    · linarith [h1]
    · exact absurd h2 hU
  have hradC : -1 + l * (2 * c - p) - h ^ 2 + r ^ 2 = l * (2 * c - p) - 2 * h := by
    linear_combination hC0
  have hI4 : ((2 * c - 1) ^ 2 * (p + 1) - 2 * r * (2 * c - 1) * (2 * c * p - 1) -
      4 * r ^ 2 * c ^ 2 * (1 - p)) * (2 * (1 + c)) ^ 2 = 4 * (p + (4 * c ^ 3 - 3 * c)) := by
    linear_combination (-2 * (2 * c - 1) * (2 * c * p - 1) * (2 * (1 + c)) -
      4 * c ^ 2 * (1 - p) * (r * (2 * (1 + c)) + (2 * c + 1))) * hR'
  have hrU2 : h * r * (2 * (1 + c)) ^ 2 = 2 * c + 1 := by
    have e : (h * (2 * (1 + c))) * (r * (2 * (1 + c))) = 1 * (2 * c + 1) := by rw [hH, hR]
    linear_combination e
  set E := ((l * (2 * c * p - 1) + 2 * h) * h + (-1 + l * (2 * c - p) - h ^ 2 + r ^ 2)) ^ 2 -
    r ^ 2 * ((l * (2 * c * p - 1) + 2 * h) ^ 2 + (l * (2 * c * q)) ^ 2) with hEd
  have hE : E = l ^ 2 * (p + 1) * ((2 * c - 1) ^ 2 * (p + 1) - 2 * r * (2 * c - 1) * (2 * c * p - 1) -
      4 * r ^ 2 * c ^ 2 * (1 - p)) - 4 * h * r * l * (2 * c - 1) * (p + 1) -
      4 * l ^ 2 * c ^ 2 * r ^ 2 * (p ^ 2 + q ^ 2 - 1) := by
    rw [hEd, hradC]
    linear_combination ((l * (2 * c * p - 1) + 2 * h) * ((l * (2 * c * p - 1) + 2 * h) * (h + 1 - r) +
      2 * (l * (2 * c - p) - 2 * h))) * hrh
  have hEU : E * (2 * (1 + c)) ^ 2 = 0 := by
    rw [hE]
    have e1 : (l ^ 2 * (p + 1) * ((2 * c - 1) ^ 2 * (p + 1) - 2 * r * (2 * c - 1) * (2 * c * p - 1) -
        4 * r ^ 2 * c ^ 2 * (1 - p)) - 4 * h * r * l * (2 * c - 1) * (p + 1) -
        4 * l ^ 2 * c ^ 2 * r ^ 2 * (p ^ 2 + q ^ 2 - 1)) * (2 * (1 + c)) ^ 2 =
        l ^ 2 * (p + 1) * (((2 * c - 1) ^ 2 * (p + 1) - 2 * r * (2 * c - 1) * (2 * c * p - 1) -
        4 * r ^ 2 * c ^ 2 * (1 - p)) * (2 * (1 + c)) ^ 2) -
        4 * l * (2 * c - 1) * (p + 1) * (h * r * (2 * (1 + c)) ^ 2) -
        (4 * l ^ 2 * c ^ 2 * r ^ 2 * (2 * (1 + c)) ^ 2) * (p ^ 2 + q ^ 2 - 1) := by ring
    rw [e1, hI4, hrU2, hpq']
    have e2 : l ^ 2 * (p + 1) * (4 * (p + (4 * c ^ 3 - 3 * c))) =
        4 * l * (p + 1) * (4 * c ^ 2 - 1) := by
      linear_combination (4 * l * (p + 1)) * hl'
    rw [e2]
    ring
  have hE0 : E = 0 := by
    rcases mul_eq_zero.mp hEU with h1 | h2
    · exact h1
    · have h3 : (2 : ℝ) * (1 + c) = 0 := (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h2
      exact absurd h3 hU
  rw [hEd] at hE0
  linarith [hE0]

end cores

section bridges

variable {α δ : ℝ}

lemma gammaEq_ptA : gammaEq α δ (ptA δ) = 0 := by
  simp only [gammaEq, coeffD, coeffE, coeffF]
  show (-Real.cos δ) ^ 2 + (-Real.sin δ) ^ 2 +
      lam α δ * (2 * Real.cos α * Real.cos δ - 1) * (-Real.cos δ) +
      lam α δ * (2 * Real.cos α * Real.sin δ) * (-Real.sin δ) +
      (-1 + lam α δ * (2 * Real.cos α - Real.cos δ)) = 0
  have hpq0 : Real.cos δ ^ 2 + Real.sin δ ^ 2 - 1 = 0 := by linarith [hpq (δ := δ)]
  linear_combination (1 - 2 * Real.cos α * lam α δ) * hpq0

lemma gammaEq_ptY (hts : Real.cos (2 * α) + Real.cos (α - δ) ≠ 0)
    (hpg : Real.cos δ + Real.cos (3 * α) ≠ 0) :
    gammaEq α δ (ptY α δ) = 0 := by
  rw [hτ, hσ] at hts
  rw [hg] at hpg
  simp only [gammaEq, ptY, coeffD, coeffE, coeffF]
  simp
  simp only [muY, lam]
  rw [hσ, hτ, hg]
  exact gammaEq_zero_Y (hcs (α := α)) (hpq (δ := δ)) (div_mul_cancel₀ _ hts)
    (div_mul_cancel₀ _ hpg) hts hpg

lemma gammaEq_ptZ (hts : Real.cos (2 * α) + Real.cos (α + δ) ≠ 0)
    (hpg : Real.cos δ + Real.cos (3 * α) ≠ 0) :
    gammaEq α δ (ptZ α δ) = 0 := by
  rw [hτ, hρ] at hts
  rw [hg] at hpg
  simp only [gammaEq, ptZ, coeffD, coeffE, coeffF]
  simp
  simp only [muZ, lam]
  rw [hρ, hτ, hg]
  exact gammaEq_zero_Z (hcs (α := α)) (hpq (δ := δ)) (div_mul_cancel₀ _ hts)
    (div_mul_cancel₀ _ hpg) hts hpg

lemma rΓ_sq_nonneg : 0 ≤ coeffD α δ ^ 2 / 4 + coeffE α δ ^ 2 / 4 - coeffF α δ := by
  have e : coeffD α δ ^ 2 / 4 + coeffE α δ ^ 2 / 4 - coeffF α δ =
      ((ptA δ) 0 + coeffD α δ / 2) ^ 2 + ((ptA δ) 1 + coeffE α δ / 2) ^ 2 := by
    have h := gammaEq_ptA (α := α) (δ := δ)
    simp only [gammaEq] at h
    linear_combination -h
  rw [e]
  positivity

lemma mem_circumΓ_iff {P : Pln} : P ∈ circumΓ α δ ↔ gammaEq α δ P = 0 := by
  rw [circumΓ, mem_sphere_iff_sq (Real.sqrt_nonneg _) P, Real.sq_sqrt rΓ_sq_nonneg]
  simp only [gammaEq]
  simp
  constructor <;> intro h <;> linear_combination h

lemma mem_incircleι_iff {P : Pln} (hr : 0 < inR α) :
    P ∈ incircleι α ↔ (P 0 - inH α) ^ 2 + (P 1) ^ 2 = inR α ^ 2 := by
  rw [incircleι, mem_sphere_iff_sq (le_of_lt hr) P]
  simp

lemma rad_rel (P : Pln) :
    gammaEq α δ P = ((P 0 - inH α) ^ 2 + (P 1) ^ 2 - inR α ^ 2) +
      (radA α δ * P 0 + radB α δ * P 1 + radC α δ) := by
  simp only [gammaEq, radA, radB, radC, coeffD, coeffE, coeffF]
  ring

lemma tangency_id (h1c : (1 : ℝ) + Real.cos α ≠ 0)
    (hpg : Real.cos δ + Real.cos (3 * α) ≠ 0) :
    (radA α δ * inH α + radC α δ) ^ 2 =
      inR α ^ 2 * ((radA α δ) ^ 2 + (radB α δ) ^ 2) := by
  have hU : (2 : ℝ) * (1 + Real.cos α) ≠ 0 := mul_ne_zero (by norm_num) h1c
  have hH : inH α * (2 * (1 + Real.cos α)) = 1 := div_mul_cancel₀ _ hU
  have hR : inR α * (2 * (1 + Real.cos α)) = 2 * Real.cos α + 1 := div_mul_cancel₀ _ hU
  have hpg' : Real.cos δ + (4 * Real.cos α ^ 3 - 3 * Real.cos α) ≠ 0 := by rwa [hg] at hpg
  have hl : lam α δ * (Real.cos δ + (4 * Real.cos α ^ 3 - 3 * Real.cos α)) =
      4 * Real.cos α ^ 2 - 1 := by
    have e : lam α δ = (4 * Real.cos α ^ 2 - 1) /
        (Real.cos δ + (4 * Real.cos α ^ 3 - 3 * Real.cos α)) := by
      rw [← hg]
      rfl
    rw [e]
    exact div_mul_cancel₀ _ hpg'
  refine incircle_tangent_core (c := Real.cos α) (p := Real.cos δ) (q := Real.sin δ)
    (r := inR α) (h := inH α) (l := lam α δ) (hpq (δ := δ)) hU hH hR hl

lemma radB_ne (hc : 0 < Real.cos α) (hT : 4 * Real.cos α ^ 2 - 1 ≠ 0)
    (hpg : Real.cos δ + Real.cos (3 * α) ≠ 0) (hq : Real.sin δ ≠ 0) :
    radB α δ ≠ 0 := by
  have hlam : lam α δ ≠ 0 := by
    simp only [lam]
    exact div_ne_zero hT hpg
  simp only [radB, coeffE]
  exact mul_ne_zero hlam (mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt hc)) hq)

/-- A line whose distance from a point `K` equals the radius meets the circle around `K`
in exactly one point. -/
lemma line_circle_singleton {a b cc K0 K1 r : ℝ} (hr : 0 < r)
    (hnab : a ^ 2 + b ^ 2 ≠ 0) (htan : (a * K0 + b * K1 + cc) ^ 2 = r ^ 2 * (a ^ 2 + b ^ 2)) :
    ∃! P : Pln, (P 0 - K0) ^ 2 + (P 1 - K1) ^ 2 = r ^ 2 ∧ a * P 0 + b * P 1 + cc = 0 := by
  have hn2 : 0 < a ^ 2 + b ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hnab)
  set n2 := a ^ 2 + b ^ 2 with hn2d
  set d := a * K0 + b * K1 + cc with hd_def
  have hd : d ^ 2 = r ^ 2 * n2 := htan
  set F0 := K0 - d / n2 * a with hF0
  set F1 := K1 - d / n2 * b with hF1
  have hF_sph : (F0 - K0) ^ 2 + (F1 - K1) ^ 2 = r ^ 2 := by
    have e : (F0 - K0) ^ 2 + (F1 - K1) ^ 2 = d ^ 2 / n2 := by
      rw [hF0, hF1]
      field_simp [hnab]
      ring
    rw [e, hd]
    field_simp [hn2.ne']
  have hF_line : a * F0 + b * F1 + cc = 0 := by
    rw [hF0, hF1]
    have e : a * (K0 - d / n2 * a) + b * (K1 - d / n2 * b) + cc = d - d * n2 / n2 := by ring
    rw [e]
    field_simp [hn2.ne']
    ring
  refine ⟨!₂[F0, F1], ⟨?_, ?_⟩, ?_⟩
  · have e : ((!₂[F0, F1] : Pln) 0 - K0) ^ 2 + ((!₂[F0, F1] : Pln) 1 - K1) ^ 2 =
        (F0 - K0) ^ 2 + (F1 - K1) ^ 2 := by simp
    rw [e]
    exact hF_sph
  · have e : a * (!₂[F0, F1] : Pln) 0 + b * (!₂[F0, F1] : Pln) 1 + cc =
        a * F0 + b * F1 + cc := by simp
    rw [e]
    exact hF_line
  · intro P ⟨hPs, hPl⟩
    have hPF : a * (P 0 - F0) + b * (P 1 - F1) = 0 := by
      have hF_line' : a * F0 + b * F1 + cc = 0 := hF_line
      linarith [hPl, hF_line']
    obtain ⟨t, ht0, ht1⟩ : ∃ t : ℝ, P 0 - F0 = -b * t ∧ P 1 - F1 = a * t := by
      by_cases hb : b = 0
      · have ha : a ≠ 0 := by
          intro ha0
          apply hnab
          rw [hn2d, ha0, hb]
          norm_num
        have hx : P 0 - F0 = 0 := by
          rw [hb] at hPF
          have h0 : a * (P 0 - F0) = 0 := by linarith [hPF]
          rcases mul_eq_zero.mp h0 with h1 | h1
          · exact absurd h1 ha
          · exact h1
        refine ⟨(P 1 - F1) / a, ?_, ?_⟩
        · rw [hx, hb]
          ring
        · field_simp [ha]
      · refine ⟨-(P 0 - F0) / b, ?_, ?_⟩
        · field_simp [hb]
        · field_simp [hb]
          linarith [hPF]
    have hdist : (P 0 - K0) ^ 2 + (P 1 - K1) ^ 2 = r ^ 2 + t ^ 2 * n2 := by
      have e1 : P 0 - K0 = (F0 - K0) + (-b) * t := by
        have : P 0 = F0 + (P 0 - F0) := by ring
        rw [this, ht0]
        ring
      have e2 : P 1 - K1 = (F1 - K1) + a * t := by
        have : P 1 = F1 + (P 1 - F1) := by ring
        rw [this, ht1]
        ring
      rw [e1, e2]
      have hcross : (F0 - K0) * (-b) + (F1 - K1) * a = 0 := by
        rw [hF0, hF1]
        ring
      have e3 : ((F0 - K0) + (-b) * t) ^ 2 + ((F1 - K1) + a * t) ^ 2 =
          ((F0 - K0) ^ 2 + (F1 - K1) ^ 2) +
          2 * t * ((F0 - K0) * (-b) + (F1 - K1) * a) + t ^ 2 * (a ^ 2 + b ^ 2) := by ring
      rw [e3, hcross, hF_sph]
      ring
    have ht0' : t = 0 := by
      rw [hdist] at hPs
      have h0 : t ^ 2 * n2 = 0 := by linarith [hPs]
      rcases mul_eq_zero.mp h0 with h | h
      · exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h
      · exact absurd h hn2.ne'
    have e0 : P 0 = F0 := by
      have := ht0
      rw [ht0'] at this
      linarith [this]
    have e1 : P 1 = F1 := by
      have := ht1
      rw [ht0'] at this
      linarith [this]
    apply Pln_ext
    intro i
    fin_cases i <;> simp [e0, e1]

end bridges

section lines

variable {α δ : ℝ}

lemma rotB1_lBeq : Real.cos α * (rotB1 α) 0 + Real.sin α * (rotB1 α) 1 = -1 / 2 := by
  have hcs0 : Real.cos α ^ 2 + Real.sin α ^ 2 - 1 = 0 := by linarith [hcs (α := α)]
  simp only [rotB1]
  simp
  linear_combination (-1 / 2 : ℝ) * hcs0

lemma rotB2_lBeq : Real.cos α * (rotB2 α) 0 + Real.sin α * (rotB2 α) 1 = -1 / 2 := by
  have hcs0 : Real.cos α ^ 2 + Real.sin α ^ 2 - 1 = 0 := by linarith [hcs (α := α)]
  simp only [rotB2]
  simp
  linear_combination (-1 / 2 : ℝ) * hcs0

lemma rotC1_lCeq : Real.cos α * (rotC1 α) 0 - Real.sin α * (rotC1 α) 1 = -1 / 2 := by
  have hcs0 : Real.cos α ^ 2 + Real.sin α ^ 2 - 1 = 0 := by linarith [hcs (α := α)]
  simp only [rotC1]
  simp
  linear_combination (-1 / 2 : ℝ) * hcs0

lemma rotC2_lCeq : Real.cos α * (rotC2 α) 0 - Real.sin α * (rotC2 α) 1 = -1 / 2 := by
  have hcs0 : Real.cos α ^ 2 + Real.sin α ^ 2 - 1 = 0 := by linarith [hcs (α := α)]
  simp only [rotC2]
  simp
  linear_combination (-1 / 2 : ℝ) * hcs0

lemma mem_lineB_of_eq (hc : 0 < Real.cos α) (hs : 0 < Real.sin α) {P : Pln}
    (hP : Real.cos α * P 0 + Real.sin α * P 1 = -1 / 2) :
    P ∈ lineB α := by
  have hs3 : Real.sin α * Real.sqrt 3 ≠ 0 :=
    mul_ne_zero (ne_of_gt hs) (Real.sqrt_pos.mpr (by norm_num)).ne'
  set k := (P 0 - (rotB1 α) 0) / (Real.sin α * Real.sqrt 3) with hk
  have e : P = rotB1 α + k • (rotB2 α - rotB1 α) := by
    apply Pln_ext
    intro i
    fin_cases i
    · have e0 : (rotB2 α) 0 - (rotB1 α) 0 = Real.sin α * Real.sqrt 3 := by
        simp only [rotB1, rotB2, PiLp.toLp_apply, Matrix.cons_val_zero]
        ring
      simp only [Fin.mk_zero, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, e0, hk]
      rw [div_mul_cancel₀ _ hs3]
      ring
    · have e1 : (rotB2 α) 1 - (rotB1 α) 1 = -Real.cos α * Real.sqrt 3 := by
        simp only [rotB1, rotB2, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
        ring
      simp only [Fin.mk_one, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, e1, hk]
      have h1 : Real.cos α * (P 0 - (rotB1 α) 0) + Real.sin α * (P 1 - (rotB1 α) 1) = 0 := by
        have hB1 := rotB1_lBeq (α := α)
        linarith [hP, hB1]
      have e2 : ((P 0 - (rotB1 α) 0) / (Real.sin α * Real.sqrt 3)) *
          (-Real.cos α * Real.sqrt 3) = -(Real.cos α * (P 0 - (rotB1 α) 0)) / Real.sin α := by
        field_simp [hs3, ne_of_gt hs]
      rw [e2]
      have h3 : P 1 = (rotB1 α) 1 + -(Real.cos α * (P 0 - (rotB1 α) 0)) / Real.sin α := by
        field_simp [ne_of_gt hs]
        linarith [h1]
      rw [h3]
  rw [e]
  exact add_smul_sub_mem_affineSpan_pair _

lemma mem_lineC_of_eq (hc : 0 < Real.cos α) (hs : 0 < Real.sin α) {P : Pln}
    (hP : Real.cos α * P 0 - Real.sin α * P 1 = -1 / 2) :
    P ∈ lineC α := by
  have hs3 : Real.sin α * Real.sqrt 3 ≠ 0 :=
    mul_ne_zero (ne_of_gt hs) (Real.sqrt_pos.mpr (by norm_num)).ne'
  set k := ((rotC1 α) 0 - P 0) / (Real.sin α * Real.sqrt 3) with hk
  have e : P = rotC1 α + k • (rotC2 α - rotC1 α) := by
    apply Pln_ext
    intro i
    fin_cases i
    · have e0 : (rotC2 α) 0 - (rotC1 α) 0 = -Real.sin α * Real.sqrt 3 := by
        simp only [rotC1, rotC2, PiLp.toLp_apply, Matrix.cons_val_zero]
        ring
      simp only [Fin.mk_zero, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, e0, hk]
      have e4 : (((rotC1 α) 0 - P 0) / (Real.sin α * Real.sqrt 3)) * (-Real.sin α * Real.sqrt 3) =
          P 0 - (rotC1 α) 0 := by
        field_simp [hs3]
        ring
      rw [e4]
      ring
    · have e1 : (rotC2 α) 1 - (rotC1 α) 1 = -Real.cos α * Real.sqrt 3 := by
        simp only [rotC1, rotC2, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
        ring
      simp only [Fin.mk_one, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, e1, hk]
      have h1 : Real.cos α * (P 0 - (rotC1 α) 0) - Real.sin α * (P 1 - (rotC1 α) 1) = 0 := by
        have hC1 := rotC1_lCeq (α := α)
        linarith [hP, hC1]
      have e2 : (((rotC1 α) 0 - P 0) / (Real.sin α * Real.sqrt 3)) *
          (-Real.cos α * Real.sqrt 3) = (Real.cos α * (P 0 - (rotC1 α) 0)) / Real.sin α := by
        field_simp [hs3, ne_of_gt hs]
        ring
      rw [e2]
      have h3 : P 1 = (rotC1 α) 1 + (Real.cos α * (P 0 - (rotC1 α) 0)) / Real.sin α := by
        field_simp [ne_of_gt hs]
        linarith [h1]
      rw [h3]
  rw [e]
  exact add_smul_sub_mem_affineSpan_pair _

lemma ptY_eq : ptY α δ = ptA δ + muY α δ • (ptC α - ptA δ) := by
  apply Pln_ext
  intro i
  fin_cases i
  · have e : (ptY α δ) 0 = (ptA δ + muY α δ • (ptC α - ptA δ)) 0 := by
        simp only [ptY, ptA, ptC, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
          PiLp.toLp_apply, Matrix.cons_val_zero, smul_eq_mul]
        ring
    exact e
  · have e : (ptY α δ) 1 = (ptA δ + muY α δ • (ptC α - ptA δ)) 1 := by
        simp only [ptY, ptA, ptC, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
          PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]
        ring
    exact e

lemma ptY_mem_lineAC : ptY α δ ∈ affineSpan ℝ ({ptA δ, ptC α} : Set Pln) := by
  rw [ptY_eq]
  exact add_smul_sub_mem_affineSpan_pair _

lemma ptY_mem_lineB (hc : 0 < Real.cos α) (hs : 0 < Real.sin α)
    (hts : Real.cos (2 * α) + Real.cos (α - δ) ≠ 0) :
    ptY α δ ∈ lineB α := by
  apply mem_lineB_of_eq hc hs
  have hμ : muY α δ * (2 * Real.cos α ^ 2 - 1 + (Real.cos α * Real.cos δ + Real.sin α * Real.sin δ)) =
      Real.cos α * Real.cos δ + Real.sin α * Real.sin δ - 1 / 2 := by
    have e : muY α δ = (Real.cos α * Real.cos δ + Real.sin α * Real.sin δ - 1 / 2) /
        (2 * Real.cos α ^ 2 - 1 + (Real.cos α * Real.cos δ + Real.sin α * Real.sin δ)) := by
      rw [← hσ, ← hτ]
      rfl
    rw [e]
    rw [hτ, hσ] at hts
    exact div_mul_cancel₀ _ hts
  have hμ' : muY α δ * (2 * Real.cos α ^ 2 - 1 + (Real.cos α * Real.cos δ + Real.sin α * Real.sin δ)) -
      (Real.cos α * Real.cos δ + Real.sin α * Real.sin δ - 1 / 2) = 0 := by linarith [hμ]
  have hcs0 : Real.cos α ^ 2 + Real.sin α ^ 2 - 1 = 0 := by linarith [hcs (α := α)]
  simp only [ptY, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination hμ' + (-muY α δ) * hcs0

lemma ptZ_eq : ptZ α δ = ptA δ + muZ α δ • (ptB α - ptA δ) := by
  apply Pln_ext
  intro i
  fin_cases i
  · have e : (ptZ α δ) 0 = (ptA δ + muZ α δ • (ptB α - ptA δ)) 0 := by
        simp only [ptZ, ptA, ptB, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
          PiLp.toLp_apply, Matrix.cons_val_zero, smul_eq_mul]
        ring
    exact e
  · have e : (ptZ α δ) 1 = (ptA δ + muZ α δ • (ptB α - ptA δ)) 1 := by
        simp only [ptZ, ptA, ptB, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
          PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]
        ring
    exact e

lemma ptZ_mem_lineAB : ptZ α δ ∈ affineSpan ℝ ({ptA δ, ptB α} : Set Pln) := by
  rw [ptZ_eq]
  exact add_smul_sub_mem_affineSpan_pair _

lemma ptZ_mem_lineC (hc : 0 < Real.cos α) (hs : 0 < Real.sin α)
    (hts : Real.cos (2 * α) + Real.cos (α + δ) ≠ 0) :
    ptZ α δ ∈ lineC α := by
  apply mem_lineC_of_eq hc hs
  have hμ : muZ α δ * (2 * Real.cos α ^ 2 - 1 + (Real.cos α * Real.cos δ - Real.sin α * Real.sin δ)) =
      Real.cos α * Real.cos δ - Real.sin α * Real.sin δ - 1 / 2 := by
    have e : muZ α δ = (Real.cos α * Real.cos δ - Real.sin α * Real.sin δ - 1 / 2) /
        (2 * Real.cos α ^ 2 - 1 + (Real.cos α * Real.cos δ - Real.sin α * Real.sin δ)) := by
      rw [← hρ, ← hτ]
      rfl
    rw [e]
    rw [hτ, hρ] at hts
    exact div_mul_cancel₀ _ hts
  have hμ' : muZ α δ * (2 * Real.cos α ^ 2 - 1 + (Real.cos α * Real.cos δ - Real.sin α * Real.sin δ)) -
      (Real.cos α * Real.cos δ - Real.sin α * Real.sin δ - 1 / 2) = 0 := by linarith [hμ]
  have hcs0 : Real.cos α ^ 2 + Real.sin α ^ 2 - 1 = 0 := by linarith [hcs (α := α)]
  simp only [ptZ, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination hμ' + (-muZ α δ) * hcs0

end lines

section incircle

variable {α δ : ℝ}

lemma hr_pos (hc : 0 < Real.cos α) : 0 < inR α := by
  have h1 : (0 : ℝ) < 2 * Real.cos α + 1 := by linarith [hc]
  have h2 : (0 : ℝ) < 2 * (1 + Real.cos α) := by linarith [hc]
  exact div_pos h1 h2

lemma hrh (h1c : (1 : ℝ) + Real.cos α ≠ 0) : inR α + inH α = 1 := by
  have hU : (2 : ℝ) * (1 + Real.cos α) ≠ 0 := mul_ne_zero (by norm_num) h1c
  have hH : inH α * (2 * (1 + Real.cos α)) = 1 := div_mul_cancel₀ _ hU
  have hR : inR α * (2 * (1 + Real.cos α)) = 2 * Real.cos α + 1 := div_mul_cancel₀ _ hU
  have hR' : inR α * (2 * (1 + Real.cos α)) - (2 * Real.cos α + 1) = 0 := by linarith [hR]
  have hH' : inH α * (2 * (1 + Real.cos α)) - 1 = 0 := by linarith [hH]
  have e : (inR α + inH α - 1) * (2 * (1 + Real.cos α)) = 0 := by
    linear_combination hR' + hH'
  rcases mul_eq_zero.mp e with h1 | h2
  · linarith [h1]
  · exact absurd h2 hU

lemma hch (h1c : (1 : ℝ) + Real.cos α ≠ 0) :
    Real.cos α * inH α + 1 / 2 = inR α := by
  have hU : (2 : ℝ) * (1 + Real.cos α) ≠ 0 := mul_ne_zero (by norm_num) h1c
  have hH : inH α * (2 * (1 + Real.cos α)) = 1 := div_mul_cancel₀ _ hU
  have hR : inR α * (2 * (1 + Real.cos α)) = 2 * Real.cos α + 1 := div_mul_cancel₀ _ hU
  have hH' : inH α * (2 * (1 + Real.cos α)) - 1 = 0 := by linarith [hH]
  have hR' : inR α * (2 * (1 + Real.cos α)) - (2 * Real.cos α + 1) = 0 := by linarith [hR]
  have e : (Real.cos α * inH α + 1 / 2 - inR α) * (2 * (1 + Real.cos α)) = 0 := by
    linear_combination (Real.cos α) * hH' - hR'
  rcases mul_eq_zero.mp e with h1 | h2
  · linarith [h1]
  · exact absurd h2 hU

lemma incircle_isTangent_lineB (hc : 0 < Real.cos α) (hs : 0 < Real.sin α)
    (h1c : (1 : ℝ) + Real.cos α ≠ 0) :
    (incircleι α).IsTangent (lineB α) := by
  have hcs := hcs (α := α)
  have hcs0 : Real.cos α ^ 2 + Real.sin α ^ 2 - 1 = 0 := by linarith [hcs]
  have hrp := hr_pos hc
  have hch' := hch h1c
  have hch'' : Real.cos α * inH α + 1 / 2 - inR α = 0 := by linarith [hch']
  have hFB_eq : Real.cos α * (inH α - inR α * Real.cos α) + Real.sin α * (-inR α * Real.sin α) =
      -1 / 2 := by
    linear_combination hch'' + (-inR α) * hcs0
  refine ⟨!₂[inH α - inR α * Real.cos α, -inR α * Real.sin α], ?_, ?_, ?_⟩
  · rw [mem_incircleι_iff hrp]
    show (inH α - inR α * Real.cos α - inH α) ^ 2 + (-inR α * Real.sin α) ^ 2 = inR α ^ 2
    linear_combination (inR α ^ 2) * hcs0
  · exact mem_lineB_of_eq hc hs hFB_eq
  · rw [lineB]
    apply affineSpan_le.2
    rw [Set.insert_subset_iff, Set.singleton_subset_iff]
    constructor
    · show rotB1 α ∈ (incircleι α).orthRadius
          !₂[inH α - inR α * Real.cos α, -inR α * Real.sin α]
      rw [EuclideanGeometry.Sphere.mem_orthRadius_iff_inner_left, inner_eq]
      show ((rotB1 α) 0 - (inH α - inR α * Real.cos α)) * ((inH α - inR α * Real.cos α) - inH α) +
          ((rotB1 α) 1 - -inR α * Real.sin α) * (-inR α * Real.sin α - 0) = 0
      linear_combination (-inR α) * rotB1_lBeq + (inR α) * hFB_eq
    · show rotB2 α ∈ (incircleι α).orthRadius
          !₂[inH α - inR α * Real.cos α, -inR α * Real.sin α]
      rw [EuclideanGeometry.Sphere.mem_orthRadius_iff_inner_left, inner_eq]
      show ((rotB2 α) 0 - (inH α - inR α * Real.cos α)) * ((inH α - inR α * Real.cos α) - inH α) +
          ((rotB2 α) 1 - -inR α * Real.sin α) * (-inR α * Real.sin α - 0) = 0
      linear_combination (-inR α) * rotB2_lBeq + (inR α) * hFB_eq

lemma incircle_isTangent_lineC (hc : 0 < Real.cos α) (hs : 0 < Real.sin α)
    (h1c : (1 : ℝ) + Real.cos α ≠ 0) :
    (incircleι α).IsTangent (lineC α) := by
  have hcs := hcs (α := α)
  have hcs0 : Real.cos α ^ 2 + Real.sin α ^ 2 - 1 = 0 := by linarith [hcs]
  have hrp := hr_pos hc
  have hch' := hch h1c
  have hch'' : Real.cos α * inH α + 1 / 2 - inR α = 0 := by linarith [hch']
  have hFC_eq : Real.cos α * (inH α - inR α * Real.cos α) - Real.sin α * (inR α * Real.sin α) =
      -1 / 2 := by
    linear_combination hch'' + (-inR α) * hcs0
  refine ⟨!₂[inH α - inR α * Real.cos α, inR α * Real.sin α], ?_, ?_, ?_⟩
  · rw [mem_incircleι_iff hrp]
    show (inH α - inR α * Real.cos α - inH α) ^ 2 + (inR α * Real.sin α) ^ 2 = inR α ^ 2
    linear_combination (inR α ^ 2) * hcs0
  · exact mem_lineC_of_eq hc hs hFC_eq
  · rw [lineC]
    apply affineSpan_le.2
    rw [Set.insert_subset_iff, Set.singleton_subset_iff]
    constructor
    · show rotC1 α ∈ (incircleι α).orthRadius
          !₂[inH α - inR α * Real.cos α, inR α * Real.sin α]
      rw [EuclideanGeometry.Sphere.mem_orthRadius_iff_inner_left, inner_eq]
      show ((rotC1 α) 0 - (inH α - inR α * Real.cos α)) * ((inH α - inR α * Real.cos α) - inH α) +
          ((rotC1 α) 1 - inR α * Real.sin α) * (inR α * Real.sin α - 0) = 0
      linear_combination (-inR α) * rotC1_lCeq + (inR α) * hFC_eq
    · show rotC2 α ∈ (incircleι α).orthRadius
          !₂[inH α - inR α * Real.cos α, inR α * Real.sin α]
      rw [EuclideanGeometry.Sphere.mem_orthRadius_iff_inner_left, inner_eq]
      show ((rotC2 α) 0 - (inH α - inR α * Real.cos α)) * ((inH α - inR α * Real.cos α) - inH α) +
          ((rotC2 α) 1 - inR α * Real.sin α) * (inR α * Real.sin α - 0) = 0
      linear_combination (-inR α) * rotC2_lCeq + (inR α) * hFC_eq

lemma incircle_isTangent_tangentN (hc : 0 < Real.cos α) (h1c : (1 : ℝ) + Real.cos α ≠ 0) :
    (incircleι α).IsTangent tangentN := by
  have hrp := hr_pos hc
  have hrh' := hrh h1c
  refine ⟨ptN, ?_, AffineSubspace.self_mem_mk' _ _, ?_⟩
  · rw [mem_incircleι_iff hrp]
    show (1 - inH α) ^ 2 + (0 : ℝ) ^ 2 = inR α ^ 2
    have h1 : (1 : ℝ) - inH α = inR α := by linarith [hrh']
    rw [h1]
    ring
  · intro x hx
    rw [EuclideanGeometry.Sphere.mem_orthRadius_iff_inner_left]
    rw [tangentN, AffineSubspace.mem_mk'] at hx
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hx
    rw [← ht, real_inner_smul_left, inner_eq]
    show t * (0 * (1 - inH α) + 1 * (0 - 0)) = 0
    ring

lemma unitω_isTangent_tangentN : unitω.IsTangent tangentN := by
  refine ⟨ptN, ?_, AffineSubspace.self_mem_mk' _ _, ?_⟩
  · rw [EuclideanGeometry.mem_sphere]
    show dist ptN (0 : Pln) = 1
    exact dist_ptN
  · intro x hx
    rw [EuclideanGeometry.Sphere.mem_orthRadius_iff_inner_left]
    rw [tangentN, AffineSubspace.mem_mk'] at hx
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hx
    rw [← ht, real_inner_smul_left, inner_eq]
    show t * (0 * (1 - 0) + 1 * (0 - 0)) = 0
    ring

lemma inH_lt_one (hc : 0 < Real.cos α) : (incircleι α).center 0 < 1 := by
  have h1 : (0 : ℝ) < 2 * (1 + Real.cos α) := by linarith [hc]
  show inH α < 1
  rw [inH, div_lt_one h1]
  linarith [hc]

lemma incenter_inside1 (hc : 0 < Real.cos α) (h1c : (1 : ℝ) + Real.cos α ≠ 0) :
    -1 / 2 < Real.cos α * (incircleι α).center 0 + Real.sin α * (incircleι α).center 1 := by
  have hch' := hch h1c
  have hrp := hr_pos hc
  show -1 / 2 < Real.cos α * inH α + Real.sin α * 0
  linarith [hch', hrp]

lemma incenter_inside2 (hc : 0 < Real.cos α) (h1c : (1 : ℝ) + Real.cos α ≠ 0) :
    -1 / 2 < Real.cos α * (incircleι α).center 0 - Real.sin α * (incircleι α).center 1 := by
  have hch' := hch h1c
  have hrp := hr_pos hc
  show -1 / 2 < Real.cos α * inH α - Real.sin α * 0
  linarith [hch', hrp]

/-- The main geometric statement: the radical axis of the two circles is tangent to the
incircle, hence the two circles meet in exactly one point. -/
lemma tangent_existsUnique (hc : 0 < Real.cos α)
    (h1c : (1 : ℝ) + Real.cos α ≠ 0) (hT : 4 * Real.cos α ^ 2 - 1 ≠ 0)
    (hpg : Real.cos δ + Real.cos (3 * α) ≠ 0) (hq : Real.sin δ ≠ 0) :
    ∃! P : Pln, P ∈ circumΓ α δ ∧ P ∈ incircleι α := by
  have hrp := hr_pos hc
  have htan := tangency_id h1c hpg
  have hradB := radB_ne hc hT hpg hq
  have hnab : (radA α δ) ^ 2 + (radB α δ) ^ 2 ≠ 0 := by
    have h1 : 0 < (radB α δ) ^ 2 := sq_pos_of_ne_zero hradB
    have h2 : 0 ≤ (radA α δ) ^ 2 := sq_nonneg _
    nlinarith [h1, h2]
  have hι1 : (incircleι α).center 0 = inH α := by simp [incircleι]
  have hι2 : (incircleι α).center 1 = 0 := by simp [incircleι]
  have htan' : (radA α δ * (incircleι α).center 0 + radB α δ * (incircleι α).center 1 +
      radC α δ) ^ 2 = inR α ^ 2 * ((radA α δ) ^ 2 + (radB α δ) ^ 2) := by
    rw [hι1, hι2]
    simpa using htan
  have key := line_circle_singleton (K0 := (incircleι α).center 0)
    (K1 := (incircleι α).center 1) (a := radA α δ) (b := radB α δ) (cc := radC α δ)
    (r := inR α) hrp hnab htan'
  obtain ⟨P, ⟨⟨hPsph, hPrad⟩, huniq⟩⟩ := key
  refine ⟨P, ⟨?_, ?_⟩, ?_⟩
  · rw [mem_circumΓ_iff, rad_rel]
    have e2 : (P 0 - inH α) ^ 2 + (P 1) ^ 2 = inR α ^ 2 := by
      rw [hι1, hι2] at hPsph
      simpa using hPsph
    linarith [hPrad, e2]
  · rw [mem_incircleι_iff hrp]
    rw [hι1, hι2] at hPsph
    simpa using hPsph
  · intro Q hQ
    apply huniq Q
    rw [mem_circumΓ_iff, rad_rel] at hQ
    rw [mem_incircleι_iff hrp] at hQ
    have e1 : (Q 0 - (incircleι α).center 0) ^ 2 + (Q 1 - (incircleι α).center 1) ^ 2 =
        inR α ^ 2 := by
      rw [hι1, hι2]
      simpa using hQ.2
    have e2 : (Q 0 - inH α) ^ 2 + (Q 1) ^ 2 = inR α ^ 2 := hQ.2
    exact ⟨e1, by linarith [hQ.1, e2]⟩

end incircle

snip end

problem usa2026_p3 {α δ : ℝ}
    (hα0 : 0 < α) (hα1 : α < Real.pi / 2) (hα60 : α ≠ Real.pi / 3)
    (hδ0 : δ ≠ 0) (hδabs : |δ| < α)
    (hδβ : δ ≠ Real.pi - 3 * α) (hδγ : δ ≠ -(Real.pi - 3 * α))
    (_hβ60 : δ ≠ Real.pi / 3 - α) (_hγ60 : δ ≠ α - Real.pi / 3) :
    dist (ptB α) 0 = 1 ∧ dist (ptC α) 0 = 1 ∧ dist (ptA δ) 0 = 1 ∧ dist ptN 0 = 1 ∧
    dist (ptB α) (rotB1 α) = dist (rotB1 α) (rotB2 α) ∧
    dist (ptB α) (rotB2 α) = dist (rotB1 α) (rotB2 α) ∧
    dist (rotB1 α) 0 = 1 ∧ dist (rotB2 α) 0 = 1 ∧
    dist (ptC α) (rotC1 α) = dist (rotC1 α) (rotC2 α) ∧
    dist (ptC α) (rotC2 α) = dist (rotC1 α) (rotC2 α) ∧
    dist (rotC1 α) 0 = 1 ∧ dist (rotC2 α) 0 = 1 ∧
    dist ptN (ptB α) = dist ptN (ptC α) ∧ (ptA δ) 0 < Real.cos α ∧
    unitω.IsTangent tangentN ∧
    ptY α δ ∈ lineB α ∧ ptY α δ ∈ affineSpan ℝ {ptA δ, ptC α} ∧
    ptZ α δ ∈ lineC α ∧ ptZ α δ ∈ affineSpan ℝ {ptA δ, ptB α} ∧
    ptA δ ∈ circumΓ α δ ∧ ptY α δ ∈ circumΓ α δ ∧ ptZ α δ ∈ circumΓ α δ ∧
    (incircleι α).IsTangent (lineB α) ∧ (incircleι α).IsTangent (lineC α) ∧
    (incircleι α).IsTangent tangentN ∧
    0 < (incircleι α).radius ∧
    (incircleι α).center 0 < 1 ∧
    -1 / 2 < Real.cos α * (incircleι α).center 0 + Real.sin α * (incircleι α).center 1 ∧
    -1 / 2 < Real.cos α * (incircleι α).center 0 - Real.sin α * (incircleι α).center 1 ∧
    ∃! P : Pln, P ∈ circumΓ α δ ∧ P ∈ incircleι α := by
  have hc := hc_pos hα0 hα1
  have hs := hs_pos hα0 hα1
  have h1c : (1 : ℝ) + Real.cos α ≠ 0 := (h1c_pos hα0 hα1).ne'
  have hT := hT_ne hα0 hα1 hα60
  have hpg := hpg_ne hα0 hα1 hδabs hδβ hδγ
  have hts := hts_ne hα0 hα1 hδabs hδγ
  have htr := htr_ne hα0 hα1 hδabs hδβ
  have hq := hq_ne hα1 hδabs hδ0
  refine ⟨dist_ptB, dist_ptC, dist_ptA, dist_ptN, ?_, ?_, dist_rotB1, dist_rotB2, ?_, ?_,
    dist_rotC1, dist_rotC2, dist_ptN_ptB_ptC, ptA_x_lt hα0 hα1 hδabs,
    unitω_isTangent_tangentN, ptY_mem_lineB hc hs hts, ptY_mem_lineAC,
    ptZ_mem_lineC hc hs htr, ptZ_mem_lineAB, ?_, ?_, ?_,
    incircle_isTangent_lineB hc hs h1c, incircle_isTangent_lineC hc hs h1c,
    incircle_isTangent_tangentN hc h1c, hr_pos hc, inH_lt_one hc,
    incenter_inside1 hc h1c, incenter_inside2 hc h1c, ?_⟩
  · rw [dist_ptB_rotB1, dist_rotB1_rotB2]
  · rw [dist_ptB_rotB2, dist_rotB1_rotB2]
  · rw [dist_ptC_rotC1, dist_rotC1_rotC2]
  · rw [dist_ptC_rotC2, dist_rotC1_rotC2]
  · rw [mem_circumΓ_iff]
    exact gammaEq_ptA
  · rw [mem_circumΓ_iff]
    exact gammaEq_ptY hts hpg
  · rw [mem_circumΓ_iff]
    exact gammaEq_ptZ htr hpg
  · exact tangent_existsUnique hc h1c hT hpg hq

end Usa2026P3
