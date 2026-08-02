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
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 2016, Problem 1

In convex pentagon ABCDE with ∠B > 90°, let F be a point on AC such that
∠FBC = 90°. It is given that FA = FB, DA = DC, EA = ED, and rays AC and
AD trisect ∠BAE. Let M be the midpoint of CF. Let X be the point such that
AMXE is a parallelogram. Show that FX, EM, BD are concurrent.

## Note on the formalization

The statement formalized in `imo2016_p1` is faithful to the original problem:
the pentagon's convexity is expressed by the five consecutive turns having a
common strict sign, the trisection by `∠BAC = ∠CAD = ∠DAE` together with the
angle-sum relations expressing that the rays `AC`, `AD` lie in the interior of
the relevant angles, and the conclusion by three `Collinear` statements.

The proof is analytic. The hypotheses of the problem determine the
configuration uniquely up to similarity, with one free parameter: the
trisection angle `θ = ∠BAC = ∠CAD = ∠DAE`. In `geo_main` we build, formally
from the geometric hypotheses, an orthonormal coordinate frame with origin
`A` and `e₁` along `AC`, and derive the following coordinates, where
`r = AB`, `γ = AC`, `c = Real.cos θ`, `s` the (signed) sine of `θ` and
`k = 2 * c ^ 2 - 1 = Real.cos (2 * θ)` (each formula below is obtained by
multiplying the unit-`AB` formula by `r`):

* `B = (c, s)` since `AB = 1` and `∠BAC = θ`.
* `F = (1 / (2 * c), 0)`: writing `F = (f, 0)`, the condition `FA = FB`
  gives `f ^ 2 = (f - c) ^ 2 + s ^ 2`, hence `f = 1 / (2 * c)`.
* `C = (c / k, 0)`: writing `C = (γ, 0)`, the condition `∠FBC = 90°`, i.e.
  `(F - B) • (C - B) = 0`, gives `(1 / (2 * c) - c) * (γ - c) + s ^ 2 = 0`,
  hence `γ = c / k`.
* `D = (c / (2 * k), - s / (2 * k))`: `D` lies on the ray from `A` making
  angle `-θ` with `AC`, so `D = d * (c, -s)` with `d = AD`; the condition
  `DA = DC` gives `d = 1 / (2 * k)`.
* `E = (1 / (4 * c), - s / (2 * k))`: `E` lies on the ray from `A` making
  angle `-2 * θ` with `AC`, so `E = e * (k, -2 * s * c)` with `e = AE`; the
  condition `EA = ED` gives `e = 1 / (4 * c * k)`, which simplifies to the
  displayed coordinates.
* `M = ((4 * c ^ 2 - 1) / (4 * c * k), 0)`, the midpoint of `C` and `F`.
* `X = M + E = ((3 * c ^ 2 - 1) / (2 * c * k), - s / (2 * k))`, since `AMXE`
  being a parallelogram means `X - M = E - A`.

The hypotheses (convex pentagon, `∠B > 90°`, `F` strictly between `A` and `C`)
correspond to the range `0 < θ < π / 4`; in particular `c ≠ 0` and `k ≠ 0`.
The concurrency of `FX`, `EM` and `BD` is then a rational identity in `c`
and `s`, verified below by explicit computation: the point
`P = (1 / (2 * c) + 1 / (8 * c * k), - s / (8 * c ^ 2 * k))` lies on all three
lines. (This is the computational shadow of the classical synthetic proof,
which exhibits the three lines as the radical axes of the circles
`(AEDMB)`, `(BFDC)` and the isosceles trapezoid `EXMF`; see e.g. Evan Chen's
IMO 2016 solution notes.)
-/

namespace Imo2016P1

open scoped InnerProductSpace EuclideanGeometry

snip begin

/-- The plane, in which the configuration lives. -/
abbrev Plane := ℝ × ℝ

noncomputable section

variable (θ : ℝ)

/-- The coordinates of `B`, with `c = Real.cos θ` and `s = Real.sin θ`. -/
def coorB : Plane := (Real.cos θ, Real.sin θ)

/-- The coordinates of `F`, with `c = Real.cos θ`. -/
def coorF : Plane := (1 / (2 * Real.cos θ), 0)

/-- The coordinates of `C`, with `c = Real.cos θ` and `k = 2 * c ^ 2 - 1`. -/
def coorC : Plane := (Real.cos θ / (2 * Real.cos θ ^ 2 - 1), 0)

/-- The coordinates of `D`, with `c = Real.cos θ`, `s = Real.sin θ`,
`k = 2 * c ^ 2 - 1`. -/
def coorD : Plane :=
  (Real.cos θ / (2 * (2 * Real.cos θ ^ 2 - 1)), -Real.sin θ / (2 * (2 * Real.cos θ ^ 2 - 1)))

/-- The coordinates of `E`, with `c = Real.cos θ`, `s = Real.sin θ`,
`k = 2 * c ^ 2 - 1`. -/
def coorE : Plane :=
  (1 / (4 * Real.cos θ), -Real.sin θ / (2 * (2 * Real.cos θ ^ 2 - 1)))

/-- The coordinates of `M` (the midpoint of `C` and `F`), with
`c = Real.cos θ` and `k = 2 * c ^ 2 - 1`. -/
def coorM : Plane :=
  ((4 * Real.cos θ ^ 2 - 1) / (4 * Real.cos θ * (2 * Real.cos θ ^ 2 - 1)), 0)

/-- The coordinates of `X`, where `AMXE` is a parallelogram, with
`c = Real.cos θ`, `s = Real.sin θ` and `k = 2 * c ^ 2 - 1`. -/
def coorX : Plane :=
  ((3 * Real.cos θ ^ 2 - 1) / (2 * Real.cos θ * (2 * Real.cos θ ^ 2 - 1)),
   -Real.sin θ / (2 * (2 * Real.cos θ ^ 2 - 1)))

end

/-- The algebraic heart of the problem: with `c = Real.cos θ`,
`s = Real.sin θ` and `k = 2 * c ^ 2 - 1`, the three lines `FX`, `EM` and `BD`
pass through the common point
`P = (1 / (2 * c) + 1 / (8 * c * k), - s / (8 * c ^ 2 * k))`. Each membership
is a rational identity in `c` and `s`, proved by clearing denominators. -/
theorem concurrent_aux {c s : ℝ} (hc : c ≠ 0) (hk : 2 * c ^ 2 - 1 ≠ 0) :
    ∃ P : Plane, ∃ t₁ t₂ t₃ : ℝ,
      P - (1 / (2 * c), 0) =
        t₁ • (((3 * c ^ 2 - 1) / (2 * c * (2 * c ^ 2 - 1)),
               -s / (2 * (2 * c ^ 2 - 1))) - (1 / (2 * c), 0)) ∧
      P - (1 / (4 * c), -s / (2 * (2 * c ^ 2 - 1))) =
        t₂ • (((4 * c ^ 2 - 1) / (4 * c * (2 * c ^ 2 - 1)), 0) -
              (1 / (4 * c), -s / (2 * (2 * c ^ 2 - 1)))) ∧
      P - (c, s) =
        t₃ • ((c / (2 * (2 * c ^ 2 - 1)), -s / (2 * (2 * c ^ 2 - 1))) - (c, s)) := by
  refine ⟨(1 / (2 * c) + 1 / (8 * c * (2 * c ^ 2 - 1)),
           -s / (8 * c ^ 2 * (2 * c ^ 2 - 1))),
          1 / (4 * c ^ 2), (4 * c ^ 2 - 1) / (4 * c ^ 2), (4 * c ^ 2 - 1) / (4 * c ^ 2),
          ?_, ?_, ?_⟩ <;>
    apply Prod.ext <;>
    simp only [Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
    field_simp <;>
    field_simp <;>
    ring

/-!
## The bridge from geometry to coordinates

The remaining auxiliary material builds the coordinate parametrization used in
`concurrent_aux` from the geometric hypotheses of the problem. We work in the
concrete plane `V2 := EuclideanSpace ℝ (Fin 2)`. `J` is rotation by `π / 2`
(counterclockwise); `crss u v = ⟪J u, v⟫` is the 2D cross product (signed
area), used to express the convexity hypothesis.
-/

/-- The concrete plane. -/
abbrev V2 := EuclideanSpace ℝ (Fin 2)

set_option linter.unnecessarySeqFocus false in
/-- Rotation by `π / 2` counterclockwise. -/
def Jrot : V2 →ₗ[ℝ] V2 where
  toFun v := (WithLp.equiv 2 _).symm ![-v 1, v 0]
  map_add' u v := by ext i; fin_cases i <;> simp [PiLp.add_apply] <;> ring
  map_smul' r v := by ext i; fin_cases i <;> simp [PiLp.smul_apply]

lemma Jrot_apply_zero (v : V2) : Jrot v 0 = -v 1 := rfl
lemma Jrot_apply_one (v : V2) : Jrot v 1 = v 0 := rfl

lemma inner_fin2 (u v : V2) : ⟪u, v⟫_ℝ = v 0 * u 0 + v 1 * u 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]

lemma inner_Jrot (u v : V2) : ⟪Jrot u, Jrot v⟫_ℝ = ⟪u, v⟫_ℝ := by
  simp only [inner_fin2, Jrot_apply_zero, Jrot_apply_one]; ring

lemma inner_self_Jrot (u : V2) : ⟪u, Jrot u⟫_ℝ = 0 := by
  simp only [inner_fin2, Jrot_apply_zero, Jrot_apply_one]; ring

lemma inner_Jrot_swap (u v : V2) : ⟪Jrot u, v⟫_ℝ = -⟪u, Jrot v⟫_ℝ := by
  simp only [inner_fin2, Jrot_apply_zero, Jrot_apply_one]; ring

lemma Jrot_Jrot (u : V2) : Jrot (Jrot u) = -u := by
  ext i; fin_cases i <;> simp [Jrot_apply_zero, Jrot_apply_one]

/-- The 2D cross product (signed area), via rotation by `π / 2`. -/
noncomputable def crss (u v : V2) : ℝ := ⟪Jrot u, v⟫_ℝ

lemma crss_self (u : V2) : crss u u = 0 := by
  simp only [crss, inner_fin2, Jrot_apply_zero, Jrot_apply_one]; ring

lemma crss_antisymm (u v : V2) : crss u v = -crss v u := by
  simp only [crss, inner_fin2, Jrot_apply_zero, Jrot_apply_one]; ring

lemma crss_add (u v w : V2) : crss u (v + w) = crss u v + crss u w := by
  simp [crss, inner_add_right]

lemma crss_sub (u v w : V2) : crss u (v - w) = crss u v - crss u w := by
  simp [crss, inner_sub_right]

lemma add_crss (u v w : V2) : crss (u + v) w = crss u w + crss v w := by
  simp [crss, map_add, inner_add_left]

lemma sub_crss (u v w : V2) : crss (u - v) w = crss u w - crss v w := by
  simp [crss, map_sub, inner_sub_left]

lemma smul_crss (r : ℝ) (u v : V2) : crss (r • u) v = r * crss u v := by
  simp [crss, map_smul, inner_smul_left]

lemma crss_smul (r : ℝ) (u v : V2) : crss u (r • v) = r * crss u v := by
  simp [crss, inner_smul_right]

/-- Every vector is determined by its coordinates with respect to a unit
vector `e₁` and its rotation `Jrot e₁`: the basis representation in the
plane. -/
lemma eq_smul_smul_of_unit (e₁ : V2) (h : ⟪e₁, e₁⟫_ℝ = 1) (v : V2) :
    v = ⟪v, e₁⟫_ℝ • e₁ + ⟪v, Jrot e₁⟫_ℝ • Jrot e₁ := by
  have h' : e₁ 0 ^ 2 + e₁ 1 ^ 2 = 1 := by
    rw [inner_fin2] at h; nlinarith [h]
  rw [← (WithLp.equiv 2 (Fin 2 → ℝ)).apply_eq_iff_eq, funext_iff, Fin.forall_fin_two]
  constructor <;>
    simp only [WithLp.equiv_apply, PiLp.add_apply, PiLp.smul_apply, inner_fin2,
      Jrot_apply_zero, Jrot_apply_one, smul_eq_mul]
  · linear_combination (-(v 0)) * h'
  · linear_combination (-(v 1)) * h'

/-- Two vectors with equal `e₁`- and `Jrot e₁`-coordinates are equal. -/
lemma eq_of_inner_inner (e₁ : V2) (h : ⟪e₁, e₁⟫_ℝ = 1) {u v : V2}
    (h1 : ⟪u, e₁⟫_ℝ = ⟪v, e₁⟫_ℝ) (h2 : ⟪u, Jrot e₁⟫_ℝ = ⟪v, Jrot e₁⟫_ℝ) :
    u = v := by
  rw [eq_smul_smul_of_unit e₁ h u, eq_smul_smul_of_unit e₁ h v, h1, h2]

/-- Inner product in an orthonormal coordinate system: the workhorse turning
all metric computations into real arithmetic. -/
lemma inner_coord {e₁ e₂ : V2} (he1 : ⟪e₁, e₁⟫_ℝ = 1) (he2 : ⟪e₂, e₂⟫_ℝ = 1)
    (ho1 : ⟪e₁, e₂⟫_ℝ = 0) (ho2 : ⟪e₂, e₁⟫_ℝ = 0) (x₁ y₁ x₂ y₂ : ℝ) :
    ⟪x₁ • e₁ + y₁ • e₂, x₂ • e₁ + y₂ • e₂⟫_ℝ = x₁ * x₂ + y₁ * y₂ := by
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    he1, he2, ho1, ho2, starRingEnd_apply, star_trivial]
  ring

/-- `dist` squared, in coordinates. -/
lemma dist_sq_coord {e₁ e₂ : V2} (he1 : ⟪e₁, e₁⟫_ℝ = 1) (he2 : ⟪e₂, e₂⟫_ℝ = 1)
    (ho1 : ⟪e₁, e₂⟫_ℝ = 0) (ho2 : ⟪e₂, e₁⟫_ℝ = 0) {u v : V2}
    {x₁ y₁ x₂ y₂ : ℝ} (hu : u = x₁ • e₁ + y₁ • e₂) (hv : v = x₂ • e₁ + y₂ • e₂) :
    dist u v ^ 2 = (x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2 := by
  rw [dist_eq_norm, pow_two ‖u - v‖, ← real_inner_self_eq_norm_mul_norm]
  have h : u - v = (x₁ - x₂) • e₁ + (y₁ - y₂) • e₂ := by
    rw [hu, hv]; module
  rw [h, inner_coord he1 he2 ho1 ho2]
  ring

/-- Reading off the `e₁`-coordinate of a coordinate vector. -/
lemma inner_coord_left {e₁ e₂ : V2} (he1 : ⟪e₁, e₁⟫_ℝ = 1) (ho2 : ⟪e₂, e₁⟫_ℝ = 0)
    (x y : ℝ) : ⟪x • e₁ + y • e₂, e₁⟫_ℝ = x := by
  simp only [inner_add_left, inner_smul_left, he1, ho2, starRingEnd_apply, star_trivial]
  ring

/-- Reading off the `e₂`-coordinate of a coordinate vector. -/
lemma inner_coord_right {e₁ e₂ : V2} (he2 : ⟪e₂, e₂⟫_ℝ = 1) (ho1 : ⟪e₁, e₂⟫_ℝ = 0)
    (x y : ℝ) : ⟪x • e₁ + y • e₂, e₂⟫_ℝ = y := by
  simp only [inner_add_left, inner_smul_left, he2, ho1, starRingEnd_apply, star_trivial]
  ring

/-- The scalar parameter in `Sbtw`: a point strictly between `A` and `C` is a
strict convex combination. -/
lemma sbtw_smul {A C F : V2} (hF : Sbtw ℝ A F C) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ F - A = t • (C - A) := by
  obtain ⟨hw, hFA, hFC⟩ := hF
  rw [Wbtw, affineSegment] at hw
  obtain ⟨t, ht, hline⟩ := hw
  rw [Set.mem_Icc] at ht
  have ht0 : 0 < t := by
    refine lt_of_le_of_ne' ht.1 (fun h0 => hFA ?_)
    rw [h0] at hline
    rw [← hline]
    simp [AffineMap.lineMap_apply_module]
  have ht1 : t < 1 := by
    refine lt_of_le_of_ne ht.2 (fun h1 => hFC ?_)
    rw [h1] at hline
    rw [← hline]
    simp [AffineMap.lineMap_apply_module]
  exact ⟨t, ht0, ht1, by rw [← hline, ← vsub_eq_sub, AffineMap.lineMap_vsub_left, vsub_eq_sub]⟩

/-- The bridge from the geometric hypotheses to the coordinates used in
`concurrent_aux`, and hence to the concurrency conclusion. The hypotheses
are those of the problem: `∠BAC = ∠CAD = ∠DAE` (the trisection), with the
interiority of the rays `AC`, `AD` in the relevant angles expressed by the
angle-sum relations; `crss (B - A) (C - B) ≠ 0` is the nondegeneracy coming
from the convexity of the pentagon (it says `B` is off the line `AC`). -/
theorem geo_main
    (A B C D E F M X : V2)
    (hcr1 : crss (B - A) (C - B) ≠ 0)
    (hF : Sbtw ℝ A F C)
    (hFBC : ∠ F B C = Real.pi / 2)
    (hFA : dist F A = dist F B)
    (hDA : dist D A = dist D C)
    (hEA : dist E A = dist E D)
    (htri1 : ∠ B A C = ∠ C A D)
    (htri2 : ∠ C A D = ∠ D A E)
    (htri3 : ∠ B A C + ∠ C A E = ∠ B A E)
    (htri4 : ∠ C A D + ∠ D A E = ∠ C A E)
    (hM : M = midpoint ℝ C F)
    (hX : X - M = E - A)
    (hAB : A ≠ B) (hAC : A ≠ C) (hAD : A ≠ D) (hAE : A ≠ E) :
    ∃ P : V2, ∃ t₁ t₂ t₃ : ℝ,
      P - F = t₁ • (X - F) ∧ P - E = t₂ • (M - E) ∧ P - B = t₃ • (D - B) := by
  -- setup: orthonormal coordinate frame along `AC`
  obtain ⟨γ, hγdef⟩ : ∃ γ : ℝ, γ = ‖C - A‖ := ⟨‖C - A‖, rfl⟩
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = ‖B - A‖ := ⟨‖B - A‖, rfl⟩
  obtain ⟨e₁, he1def⟩ : ∃ e₁ : V2, e₁ = γ⁻¹ • (C - A) := ⟨γ⁻¹ • (C - A), rfl⟩
  obtain ⟨e₂, he2def⟩ : ∃ e₂ : V2, e₂ = Jrot e₁ := ⟨Jrot e₁, rfl⟩
  have hγ : γ ≠ 0 := hγdef ▸ norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm hAC))
  have hr : r ≠ 0 := hrdef ▸ norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm hAB))
  have hγpos : 0 < γ := lt_of_le_of_ne' (hγdef ▸ norm_nonneg _) hγ
  have hrpos : 0 < r := lt_of_le_of_ne' (hrdef ▸ norm_nonneg _) hr
  have he1u : ⟪e₁, e₁⟫_ℝ = 1 := by
    rw [he1def]
    simp only [inner_smul_left, inner_smul_right, real_inner_self_eq_norm_mul_norm,
      starRingEnd_apply, star_trivial]
    rw [← hγdef]
    field_simp
  have he2u : ⟪e₂, e₂⟫_ℝ = 1 := by
    rw [he2def, inner_Jrot]; exact he1u
  have ho1 : ⟪e₁, e₂⟫_ℝ = 0 := by
    rw [he2def]; exact inner_self_Jrot e₁
  have ho2 : ⟪e₂, e₁⟫_ℝ = 0 := by
    rw [he2def, inner_Jrot_swap, inner_self_Jrot, neg_zero]
  have hCA : C - A = γ • e₁ := by rw [he1def, smul_smul, mul_inv_cancel₀ hγ, one_smul]
  -- the trisection angle and the coordinate parameters
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = ∠ B A C := ⟨∠ B A C, rfl⟩
  have hθeq : θ = InnerProductGeometry.angle (B - A) (C - A) := by
    rw [hθdef]; unfold EuclideanGeometry.angle; rw [vsub_eq_sub, vsub_eq_sub]
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = Real.cos θ := ⟨Real.cos θ, rfl⟩
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = ⟪B - A, e₂⟫_ℝ / r := ⟨⟪B - A, e₂⟫_ℝ / r, rfl⟩
  obtain ⟨k, hkdef⟩ : ∃ k : ℝ, k = 2 * c ^ 2 - 1 := ⟨2 * c ^ 2 - 1, rfl⟩
  -- the coordinates of `B`
  have hxB : ⟪B - A, e₁⟫_ℝ = r * c := by
    have h1 : c = ⟪B - A, C - A⟫_ℝ / (r * γ) := by
      rw [hcdef, hθeq, InnerProductGeometry.cos_angle, ← hrdef, ← hγdef]
    have h2 : ⟪B - A, C - A⟫_ℝ = r * γ * c := by
      field_simp at h1; linarith [h1]
    rw [he1def, inner_smul_right, h2]
    field_simp
  have hyB : ⟪B - A, e₂⟫_ℝ = r * s := by
    rw [hsdef]; field_simp
  have hrepB : B - A = (r * c) • e₁ + (r * s) • e₂ := by
    have h := eq_smul_smul_of_unit e₁ he1u (B - A)
    rw [← he2def, hxB, hyB] at h
    exact h
  have hsq : r ^ 2 = (r * c) ^ 2 + (r * s) ^ 2 := by
    have hn : r ^ 2 = ⟪B - A, B - A⟫_ℝ := by
      rw [hrdef, pow_two, ← real_inner_self_eq_norm_mul_norm]
    rw [hn, hrepB, inner_coord he1u he2u ho1 ho2]
    ring
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    have h2 : r ^ 2 * (c ^ 2 + s ^ 2) = r ^ 2 * 1 := by linear_combination -hsq
    exact mul_left_cancel₀ (pow_ne_zero 2 hr) h2
  have hs2 : s ^ 2 = 1 - c ^ 2 := by linarith [hcs]
  have hcr : crss (B - A) (C - B) = -(γ * (r * s)) := by
    have hCB : C - B = (C - A) - (B - A) := by abel
    rw [hCB, crss_sub, crss_self, sub_zero, hCA, crss_smul]
    simp only [crss, inner_Jrot_swap, ← he2def, hyB]
    ring
  have hns : s ≠ 0 := by
    intro hz
    apply hcr1
    rw [hcr, hz, mul_zero, mul_zero, neg_zero]
  have hθ0 : θ ≠ 0 := by
    intro hz
    rw [hθeq, InnerProductGeometry.angle_eq_zero_iff] at hz
    obtain ⟨_, q, hq, hCq⟩ := hz
    apply hcr1
    have hCB : C - B = (C - A) - (B - A) := by abel
    rw [hCB, hCq, crss_sub, crss_smul, crss_self, mul_zero, sub_self]
  have hθpos : 0 < θ := by
    refine lt_of_le_of_ne' ?_ hθ0
    rw [hθeq]; exact InnerProductGeometry.angle_nonneg _ _
  rw [← hθdef] at htri1 htri3
  -- the coordinates of `F`
  obtain ⟨t, ht0, ht1, hFt⟩ := sbtw_smul hF
  have hrepF0 : F - A = (t * γ) • e₁ + (0 : ℝ) • e₂ := by
    rw [hFt, hCA, smul_smul, zero_smul, add_zero]
  have hrepF : F - A = (t * γ) • e₁ := by rw [hrepF0, zero_smul, add_zero]
  have hFA2 : ⟪F - A, F - A⟫_ℝ = ⟪F - B, F - B⟫_ℝ := by
    have h2 : dist F A ^ 2 = dist F B ^ 2 := by rw [hFA]
    rw [dist_eq_norm, dist_eq_norm, pow_two, pow_two,
      ← real_inner_self_eq_norm_mul_norm, ← real_inner_self_eq_norm_mul_norm] at h2
    exact h2
  have hFBv : F - B = (t * γ - r * c) • e₁ + (-(r * s)) • e₂ := by
    have h : F - B = (F - A) - (B - A) := by abel
    rw [h, hrepF, hrepB]; module
  rw [hrepF0, hFBv, inner_coord he1u he2u ho1 ho2, inner_coord he1u he2u ho1 ho2] at hFA2
  have hcsr : (r * c) ^ 2 + (r * s) ^ 2 = r ^ 2 := hsq.symm
  have hxFval : 2 * c * (t * γ) = r := by
    have e1 : 2 * (r * c) * (t * γ) = r ^ 2 := by linear_combination hFA2 + hcsr
    have e2 : r * (2 * c * (t * γ)) = r * r := by linear_combination e1
    exact mul_left_cancel₀ hr e2
  have htγ : 0 < t * γ := mul_pos ht0 hγpos
  have hcpos : 0 < c := by
    have h1 : (0:ℝ) < 2 * c * (t * γ) := by rw [hxFval]; exact hrpos
    have h2 : (0:ℝ) < 2 * c := by nlinarith only [h1, htγ]
    linarith [h2]
  have hc0 : c ≠ 0 := ne_of_gt hcpos
  have h4c : (4 : ℝ) * c ≠ 0 := mul_ne_zero (by norm_num) hc0
  have h2c : (2 : ℝ) * c ≠ 0 := mul_ne_zero two_ne_zero hc0
  have hxFe : t * γ = r / (2 * c) := by
    rw [eq_div_iff_mul_eq (mul_ne_zero two_ne_zero hc0)]
    linear_combination hxFval
  -- `∠FBC = 90°`: the coordinates of `C`
  have hperp : ⟪F - B, C - B⟫_ℝ = 0 := by
    have h : ∠ F B C = InnerProductGeometry.angle (F - B) (C - B) := by
      unfold EuclideanGeometry.angle; rw [vsub_eq_sub, vsub_eq_sub]
    rw [h] at hFBC
    exact (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two _ _).mpr hFBC
  have hCBv : C - B = (γ - r * c) • e₁ + (-(r * s)) • e₂ := by
    have h : C - B = (C - A) - (B - A) := by abel
    rw [h, hCA, hrepB]; module
  rw [hFBv, hCBv, inner_coord he1u he2u ho1 ho2] at hperp
  have hCeq : (t * γ - r * c) * (γ - r * c) + (r * s) * (r * s) = 0 := by
    linear_combination hperp
  have hkγ : k * γ = r * c := by
    have e1 : r * (k * γ) = r * (r * c) := by
      rw [hkdef]
      linear_combination (-2 * c) * hCeq + (γ - r * c) * hxFval + (2 * c * r ^ 2) * hcs
    exact mul_left_cancel₀ hr e1
  have hrcpos : 0 < r * c := mul_pos hrpos hcpos
  have hkpos : 0 < k := by
    have h : 0 < k * γ := by rw [hkγ]; exact hrcpos
    nlinarith only [h, hγpos]
  have hk0 : k ≠ 0 := ne_of_gt hkpos
  have hγval : γ = r * c / k := by
    rw [eq_div_iff_mul_eq hk0]
    linear_combination hkγ
  -- the coordinates of `D`
  obtain ⟨d, hddef⟩ : ∃ d : ℝ, d = ‖D - A‖ := ⟨‖D - A‖, rfl⟩
  have hd : d ≠ 0 := hddef ▸ norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm hAD))
  have hdpos : 0 < d := lt_of_le_of_ne' (hddef ▸ norm_nonneg _) hd
  have hCAD : ∠ C A D = θ := htri1.symm
  have hxD : ⟪D - A, e₁⟫_ℝ = d * c := by
    have hCAD' : InnerProductGeometry.angle (D - A) (C - A) = θ := by
      rw [← hCAD]; unfold EuclideanGeometry.angle
      rw [vsub_eq_sub, vsub_eq_sub, InnerProductGeometry.angle_comm]
    have h1 : c = ⟪D - A, C - A⟫_ℝ / (d * γ) := by
      rw [hcdef, ← hCAD', InnerProductGeometry.cos_angle, ← hddef, ← hγdef]
    have h2 : ⟪D - A, C - A⟫_ℝ = d * γ * c := by
      field_simp at h1; linarith [h1]
    rw [he1def, inner_smul_right, h2]
    field_simp
  obtain ⟨yD, hyDdef⟩ : ∃ yD : ℝ, yD = ⟪D - A, e₂⟫_ℝ := ⟨⟪D - A, e₂⟫_ℝ, rfl⟩
  have hrepD : D - A = (d * c) • e₁ + yD • e₂ := by
    have h := eq_smul_smul_of_unit e₁ he1u (D - A)
    rw [← he2def, hxD, ← hyDdef] at h
    exact h
  have hDAsq : ⟪D - A, D - A⟫_ℝ = ⟪D - C, D - C⟫_ℝ := by
    have h2 : dist D A ^ 2 = dist D C ^ 2 := by rw [hDA]
    rw [dist_eq_norm, dist_eq_norm, pow_two, pow_two,
      ← real_inner_self_eq_norm_mul_norm, ← real_inner_self_eq_norm_mul_norm] at h2
    exact h2
  have hDCv : D - C = (d * c - γ) • e₁ + yD • e₂ := by
    have h : D - C = (D - A) - (C - A) := by abel
    rw [h, hrepD, hCA]; module
  rw [hrepD, hDCv, inner_coord he1u he2u ho1 ho2, inner_coord he1u he2u ho1 ho2] at hDAsq
  have hdval : 2 * c * d = γ := by
    have e1 : γ * (2 * c * d) = γ * γ := by linear_combination hDAsq
    exact mul_left_cancel₀ hγ e1
  have h2dk : 2 * d * k = r := by
    have hkγ2 : k * γ = r * c := hkγ
    rw [← hdval] at hkγ2
    have e1 : c * (2 * d * k) = c * r := by linear_combination hkγ2
    exact mul_left_cancel₀ (ne_of_gt hcpos) e1
  have hdc : d * c = r * c / (2 * k) := by
    rw [eq_div_iff_mul_eq (mul_ne_zero two_ne_zero hk0)]
    linear_combination (c) * h2dk
  have hds : d * s = r * s / (2 * k) := by
    rw [eq_div_iff_mul_eq (mul_ne_zero two_ne_zero hk0)]
    linear_combination (s) * h2dk
  have hdsq : d ^ 2 = (d * c) ^ 2 + yD ^ 2 := by
    have hn : d ^ 2 = ⟪D - A, D - A⟫_ℝ := by
      rw [hddef, pow_two, ← real_inner_self_eq_norm_mul_norm]
    rw [hn, hrepD, inner_coord he1u he2u ho1 ho2]
    ring
  have hyDsq : yD ^ 2 = (d * s) ^ 2 := by
    linear_combination (-1 : ℝ) * hdsq + (-(d ^ 2)) * hs2
  have hyDcases : yD = d * s ∨ yD = -(d * s) := sq_eq_sq_iff_eq_or_eq_neg.mp hyDsq
  have hyDneg : yD ≠ d * s := by
    intro hy
    have hDr' : r • (D - A) = d • (B - A) := by
      rw [hrepD, hy, hrepB]; module
    have hDr : D - A = (d / r) • (B - A) := by
      have h2 : r⁻¹ • (r • (D - A)) = r⁻¹ • (d • (B - A)) := by rw [hDr']
      rwa [smul_smul, smul_smul, inv_mul_cancel₀ hr, one_smul, ← div_eq_inv_mul] at h2
    have hDAE : ∠ D A E = ∠ B A E := by
      have hdr : 0 < d / r := div_pos hdpos hrpos
      unfold EuclideanGeometry.angle
      rw [vsub_eq_sub, vsub_eq_sub, hDr, vsub_eq_sub,
        InnerProductGeometry.angle_smul_left_of_pos _ _ hdr]
    linarith [htri1, htri3, htri4, hDAE, hθpos]
  have hyD : yD = -(d * s) := by
    cases hyDcases with
    | inl h => exact absurd h hyDneg
    | inr h => exact h
  have hrepD2 : D - A = (r * c / (2 * k)) • e₁ + (-(r * s / (2 * k))) • e₂ := by
    rw [hrepD, hyD, hdc, hds]
  -- the coordinates of `E`
  obtain ⟨eE, hedef⟩ : ∃ eE : ℝ, eE = ‖E - A‖ := ⟨‖E - A‖, rfl⟩
  have heE : eE ≠ 0 := hedef ▸ norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm hAE))
  have heEpos : 0 < eE := lt_of_le_of_ne' (hedef ▸ norm_nonneg _) heE
  have hDAE2 : ∠ D A E = θ := (htri1.trans htri2).symm
  have hED : ⟪E - A, D - A⟫_ℝ = eE * d * c := by
    have h2 : InnerProductGeometry.angle (E - A) (D - A) = θ := by
      rw [← hDAE2]; unfold EuclideanGeometry.angle
      rw [vsub_eq_sub, vsub_eq_sub, InnerProductGeometry.angle_comm]
    have h1 : c = ⟪E - A, D - A⟫_ℝ / (eE * d) := by
      rw [hcdef, ← h2, InnerProductGeometry.cos_angle, ← hedef, ← hddef]
    field_simp at h1
    linarith [h1]
  obtain ⟨xE, hxEdef⟩ : ∃ xE : ℝ, xE = ⟪E - A, e₁⟫_ℝ := ⟨⟪E - A, e₁⟫_ℝ, rfl⟩
  obtain ⟨yE, hyEdef⟩ : ∃ yE : ℝ, yE = ⟪E - A, e₂⟫_ℝ := ⟨⟪E - A, e₂⟫_ℝ, rfl⟩
  have hrepE : E - A = xE • e₁ + yE • e₂ := by
    have h := eq_smul_smul_of_unit e₁ he1u (E - A)
    rw [← he2def, ← hxEdef, ← hyEdef] at h
    exact h
  have hEAsq : ⟪E - A, E - A⟫_ℝ = ⟪E - D, E - D⟫_ℝ := by
    have h2 : dist E A ^ 2 = dist E D ^ 2 := by rw [hEA]
    rw [dist_eq_norm, dist_eq_norm, pow_two, pow_two,
      ← real_inner_self_eq_norm_mul_norm, ← real_inner_self_eq_norm_mul_norm] at h2
    exact h2
  have hEDv : E - D = (xE - d * c) • e₁ + (yE - yD) • e₂ := by
    have h : E - D = (E - A) - (D - A) := by abel
    rw [h, hrepE, hrepD]; module
  have hE3 : xE * (d * c) + yE * yD = eE * d * c := by
    have h : ⟪E - A, D - A⟫_ℝ = xE * (d * c) + yE * yD := by
      rw [hrepE, hrepD, inner_coord he1u he2u ho1 ho2]
    rw [h] at hED
    exact hED
  have hE4 : xE ^ 2 + yE ^ 2 = (xE - d * c) ^ 2 + (yE - yD) ^ 2 := by
    have ha : ⟪E - A, E - A⟫_ℝ = xE * xE + yE * yE := by
      rw [hrepE, inner_coord he1u he2u ho1 ho2]
    have hb : ⟪E - D, E - D⟫_ℝ =
        (xE - d * c) * (xE - d * c) + (yE - yD) * (yE - yD) := by
      rw [hEDv, inner_coord he1u he2u ho1 ho2]
    rw [ha, hb] at hEAsq
    linear_combination hEAsq
  have hE5 : 2 * (xE * (d * c) + yE * yD) = d ^ 2 := by
    linear_combination hE4 + (-1 : ℝ) * hdsq
  have heEval : 2 * c * eE = d := by
    have e1 : d * (2 * c * eE) = d * d := by linear_combination hE5 + (-2 : ℝ) * hE3
    exact mul_left_cancel₀ hd e1
  have heEk : eE * k = r / (4 * c) := by
    rw [eq_div_iff_mul_eq (mul_ne_zero (by norm_num) hc0)]
    linear_combination (2 * k) * heEval + h2dk
  have heEsc : 2 * eE * s * c = r * s / (2 * k) := by
    have h1 : 2 * eE * s * c = d * s := by linear_combination (s) * heEval
    rw [h1]; exact hds
  have hCAE : ∠ C A E = 2 * θ := by
    have h1 : ∠ C A D = θ := htri1.symm
    linarith [htri4, h1, hDAE2]
  have hxEval : xE = eE * k := by
    have h1 : Real.cos (∠ C A E) = ⟪E - A, C - A⟫_ℝ / (eE * γ) := by
      have h2 : InnerProductGeometry.angle (E - A) (C - A) = ∠ C A E := by
        unfold EuclideanGeometry.angle
        rw [vsub_eq_sub, vsub_eq_sub, InnerProductGeometry.angle_comm]
      rw [← h2, InnerProductGeometry.cos_angle, ← hedef, ← hγdef]
    rw [hCAE, Real.cos_two_mul, ← hcdef, ← hkdef] at h1
    have h3 : ⟪E - A, C - A⟫_ℝ = eE * γ * k := by
      field_simp at h1
      linarith [h1]
    rw [hxEdef, he1def, inner_smul_right, h3]
    field_simp
  have hk2 : 1 - k ^ 2 = 4 * s ^ 2 * c ^ 2 := by
    rw [hkdef]; linear_combination (-4 * c ^ 2) * hcs
  have hyEsq : yE ^ 2 = (2 * eE * s * c) ^ 2 := by
    have h1 : eE ^ 2 = xE ^ 2 + yE ^ 2 := by
      have hn : eE ^ 2 = ⟪E - A, E - A⟫_ℝ := by
        rw [hedef, pow_two, ← real_inner_self_eq_norm_mul_norm]
      rw [hn, hrepE, inner_coord he1u he2u ho1 ho2]
      ring
    rw [hxEval] at h1
    linear_combination (-1 : ℝ) * h1 + (eE ^ 2) * hk2
  have hyEcases : yE = 2 * eE * s * c ∨ yE = -(2 * eE * s * c) :=
    sq_eq_sq_iff_eq_or_eq_neg.mp hyEsq
  have hyEneg : yE ≠ 2 * eE * s * c := by
    intro hy
    have hcos : Real.cos (∠ B A E) = c := by
      have h1 : InnerProductGeometry.angle (E - A) (B - A) = ∠ B A E := by
        unfold EuclideanGeometry.angle
        rw [vsub_eq_sub, vsub_eq_sub, InnerProductGeometry.angle_comm]
      rw [← h1, InnerProductGeometry.cos_angle, ← hedef, ← hrdef]
      have h2 : ⟪E - A, B - A⟫_ℝ = xE * (r * c) + yE * (r * s) := by
        rw [hrepE, hrepB, inner_coord he1u he2u ho1 ho2]
      rw [h2, hxEval, hy]
      have hk1 : k + 2 * s ^ 2 = 1 := by rw [hkdef]; linear_combination (2 : ℝ) * hcs
      rw [hkdef] at hk1 ⊢
      rw [div_eq_iff_mul_eq (mul_ne_zero heE hr)]
      linear_combination (-(eE * r * c)) * hk1
    have hBAE : ∠ B A E = θ := by
      have h2 : ∠ B A E ∈ Set.Icc 0 Real.pi := by
        refine ⟨?_, ?_⟩
        · unfold EuclideanGeometry.angle
          rw [vsub_eq_sub, vsub_eq_sub]; exact InnerProductGeometry.angle_nonneg _ _
        · unfold EuclideanGeometry.angle
          rw [vsub_eq_sub, vsub_eq_sub]; exact InnerProductGeometry.angle_le_pi _ _
      have h3 : θ ∈ Set.Icc 0 Real.pi := by
        rw [hθeq]; exact ⟨InnerProductGeometry.angle_nonneg _ _,
          InnerProductGeometry.angle_le_pi _ _⟩
      have h4 : Real.cos (∠ B A E) = Real.cos θ := by rw [hcos, ← hcdef]
      exact Real.injOn_cos h2 h3 h4
    rw [hCAE, hBAE] at htri3
    linarith [htri3, hθpos]
  have hyEval : yE = -(2 * eE * s * c) := by
    cases hyEcases with
    | inl h => exact absurd h hyEneg
    | inr h => exact h
  have hrepE2 : E - A = (r / (4 * c)) • e₁ + (-(r * s / (2 * k))) • e₂ := by
    rw [hrepE, hxEval, hyEval, heEk, heEsc]
  -- the coordinates of `M` and `X`
  have hrepM : M - A = (r * (4 * c ^ 2 - 1) / (4 * c * k)) • e₁ + (0 : ℝ) • e₂ := by
    have h1 : M = (2⁻¹ : ℝ) • (C + F) := by
      rw [hM, midpoint, AffineMap.lineMap_apply_module]
      simp only [invOf_eq_inv]
      module
    have h2 : M - A = (2⁻¹ : ℝ) • ((C - A) + (F - A)) := by
      rw [h1]; module
    have hid1 : r * c / k = (4 * c ^ 2 * r) / (4 * c * k) := by
      rw [div_eq_div_iff hk0 (mul_ne_zero h4c hk0)]
      ring
    have hid2 : r / (2 * c) = (2 * r * k) / (4 * c * k) := by
      rw [div_eq_div_iff h2c (mul_ne_zero h4c hk0)]
      ring
    have hid : (2⁻¹ : ℝ) * (r * c / k + r / (2 * c)) =
        r * (4 * c ^ 2 - 1) / (4 * c * k) := by
      rw [hid1, hid2, ← add_div, ← mul_div_assoc,
        div_eq_div_iff (mul_ne_zero h4c hk0) (mul_ne_zero h4c hk0)]
      linear_combination (4 * c * k * r) * hkdef
    rw [h2, hCA, hrepF, hxFe, hγval, zero_smul, add_zero, ← add_smul, smul_smul, hid]
  have hrepX : X - A =
      (r * (3 * c ^ 2 - 1) / (2 * c * k)) • e₁ + (-(r * s / (2 * k))) • e₂ := by
    have h1 : X - A = (M - A) + (E - A) := by
      rw [← hX]; abel
    have hid : r * (4 * c ^ 2 - 1) / (4 * c * k) + r / (4 * c) =
        r * (3 * c ^ 2 - 1) / (2 * c * k) := by
      have hid2 : r / (4 * c) = (r * k) / (4 * c * k) := by
        rw [div_eq_div_iff h4c (mul_ne_zero h4c hk0)]
        ring
      rw [hid2, ← add_div,
        div_eq_div_iff (mul_ne_zero h4c hk0) (mul_ne_zero h2c hk0)]
      linear_combination (2 * r * c * k) * hkdef
    rw [h1, hrepM, hrepE2, zero_smul, add_zero, ← add_assoc, ← add_smul, hid]
  -- the assembly: scale the algebraic concurrency point of `concurrent_aux`
  obtain ⟨P₀, t₁, t₂, t₃, h1, h2, h3⟩ := concurrent_aux (c := c) (s := s)
    (ne_of_gt hcpos) (hkdef ▸ hk0)
  have h1x : P₀.1 - 1 / (2 * c) =
      t₁ * ((3 * c ^ 2 - 1) / (2 * c * k) - 1 / (2 * c)) := by
    have hh := congrArg Prod.fst h1
    simp only [Prod.fst_sub, Prod.smul_fst, ← hkdef] at hh
    exact hh
  have h1y : P₀.2 - 0 = t₁ * (-s / (2 * k) - 0) := by
    have hh := congrArg Prod.snd h1
    simp only [Prod.snd_sub, Prod.smul_snd, ← hkdef] at hh
    exact hh
  have h2x : P₀.1 - 1 / (4 * c) =
      t₂ * ((4 * c ^ 2 - 1) / (4 * c * k) - 1 / (4 * c)) := by
    have hh := congrArg Prod.fst h2
    simp only [Prod.fst_sub, Prod.smul_fst, ← hkdef] at hh
    exact hh
  have h2y : P₀.2 - -s / (2 * k) = t₂ * (0 - -s / (2 * k)) := by
    have hh := congrArg Prod.snd h2
    simp only [Prod.snd_sub, Prod.smul_snd, ← hkdef] at hh
    exact hh
  have h3x : P₀.1 - c = t₃ * (c / (2 * k) - c) := by
    have hh := congrArg Prod.fst h3
    simp only [Prod.fst_sub, Prod.smul_fst, ← hkdef] at hh
    exact hh
  have h3y : P₀.2 - s = t₃ * (-s / (2 * k) - s) := by
    have hh := congrArg Prod.snd h3
    simp only [Prod.snd_sub, Prod.smul_snd, ← hkdef] at hh
    exact hh
  -- coordinate values of every point
  have hPA : (A + (r * P₀.1) • e₁ + (r * P₀.2) • e₂) - A =
      (r * P₀.1) • e₁ + (r * P₀.2) • e₂ := by abel
  have hxP1 : ⟪(A + (r * P₀.1) • e₁ + (r * P₀.2) • e₂) - A, e₁⟫_ℝ = r * P₀.1 := by
    rw [hPA, inner_coord_left he1u ho2]
  have hxP2 : ⟪(A + (r * P₀.1) • e₁ + (r * P₀.2) • e₂) - A, e₂⟫_ℝ = r * P₀.2 := by
    rw [hPA, inner_coord_right he2u ho1]
  have hFv : F - A = (r * (1 / (2 * c))) • e₁ + (0 : ℝ) • e₂ := by
    rw [hrepF, hxFe, zero_smul, add_zero, mul_one_div]
  have hxF1 : ⟪F - A, e₁⟫_ℝ = r * (1 / (2 * c)) := by
    rw [hFv, inner_coord_left he1u ho2]
  have hxF2 : ⟪F - A, e₂⟫_ℝ = 0 := by
    rw [hFv, inner_coord_right he2u ho1]
  have hxX1 : ⟪X - A, e₁⟫_ℝ = r * ((3 * c ^ 2 - 1) / (2 * c * k)) := by
    rw [hrepX, inner_coord_left he1u ho2, mul_div_assoc]
  have hxX2' : ⟪X - A, e₂⟫_ℝ = r * (-s / (2 * k)) := by
    rw [hrepX, inner_coord_right he2u ho1]
    field_simp
  have hxE1 : ⟪E - A, e₁⟫_ℝ = r * (1 / (4 * c)) := by
    rw [hrepE2, inner_coord_left he1u ho2]
    field_simp
  have hxE2 : ⟪E - A, e₂⟫_ℝ = r * (-s / (2 * k)) := by
    rw [hrepE2, inner_coord_right he2u ho1]
    field_simp
  have hxM1 : ⟪M - A, e₁⟫_ℝ = r * ((4 * c ^ 2 - 1) / (4 * c * k)) := by
    rw [hrepM, inner_coord_left he1u ho2, mul_div_assoc]
  have hxM2 : ⟪M - A, e₂⟫_ℝ = 0 := by
    rw [hrepM, inner_coord_right he2u ho1]
  have hxB1 : ⟪B - A, e₁⟫_ℝ = r * c := hxB
  have hxB2 : ⟪B - A, e₂⟫_ℝ = r * s := hyB
  have hxD1 : ⟪D - A, e₁⟫_ℝ = r * (c / (2 * k)) := by
    rw [hrepD2, inner_coord_left he1u ho2]
    field_simp
  have hxD2 : ⟪D - A, e₂⟫_ℝ = r * (-s / (2 * k)) := by
    rw [hrepD2, inner_coord_right he2u ho1]
    field_simp
  refine ⟨A + (r * P₀.1) • e₁ + (r * P₀.2) • e₂, t₁, t₂, t₃, ?_, ?_, ?_⟩
  · apply eq_of_inner_inner e₁ he1u
    · have e1 : ⟪(A + (r * P₀.1) • e₁ + (r * P₀.2) • e₂) - F, e₁⟫_ℝ =
          r * (P₀.1 - 1 / (2 * c)) := by
        rw [show (A + (r * P₀.1) • e₁ + (r * P₀.2) • e₂) - F =
            ((A + (r * P₀.1) • e₁ + (r * P₀.2) • e₂) - A) - (F - A) from by abel,
          inner_sub_left, hxP1, hxF1]
        ring
      have e2 : ⟪t₁ • (X - F), e₁⟫_ℝ =
          t₁ * (r * ((3 * c ^ 2 - 1) / (2 * c * k) - 1 / (2 * c))) := by
        rw [inner_smul_left, starRingEnd_apply, star_trivial,
          show X - F = (X - A) - (F - A) from by abel, inner_sub_left, hxX1, hxF1]
        ring
      rw [e1, e2]
      linear_combination (r) * h1x
    · rw [← he2def]
      have e1 : ⟪(A + (r * P₀.1) • e₁ + (r * P₀.2) • e₂) - F, e₂⟫_ℝ =
          r * (P₀.2 - 0) := by
        rw [show (A + (r * P₀.1) • e₁ + (r * P₀.2) • e₂) - F =
            ((A + (r * P₀.1) • e₁ + (r * P₀.2) • e₂) - A) - (F - A) from by abel,
          inner_sub_left, hxP2, hxF2]
        ring
      have e2 : ⟪t₁ • (X - F), e₂⟫_ℝ = t₁ * (r * (-s / (2 * k) - 0)) := by
        rw [inner_smul_left, starRingEnd_apply, star_trivial,
          show X - F = (X - A) - (F - A) from by abel, inner_sub_left,
          hxX2', hxF2]
        ring
      rw [e1, e2]
      linear_combination (r) * h1y
  · apply eq_of_inner_inner e₁ he1u
    · have e1 : ⟪(A + (r * P₀.1) • e₁ + (r * P₀.2) • e₂) - E, e₁⟫_ℝ =
          r * (P₀.1 - 1 / (4 * c)) := by
        rw [show (A + (r * P₀.1) • e₁ + (r * P₀.2) • e₂) - E =
            ((A + (r * P₀.1) • e₁ + (r * P₀.2) • e₂) - A) - (E - A) from by abel,
          inner_sub_left, hxP1, hxE1]
        ring
      have e2 : ⟪t₂ • (M - E), e₁⟫_ℝ =
          t₂ * (r * ((4 * c ^ 2 - 1) / (4 * c * k) - 1 / (4 * c))) := by
        rw [inner_smul_left, starRingEnd_apply, star_trivial,
          show M - E = (M - A) - (E - A) from by abel, inner_sub_left, hxM1, hxE1]
        ring
      rw [e1, e2]
      linear_combination (r) * h2x
    · rw [← he2def]
      have e1 : ⟪(A + (r * P₀.1) • e₁ + (r * P₀.2) • e₂) - E, e₂⟫_ℝ =
          r * (P₀.2 - -s / (2 * k)) := by
        rw [show (A + (r * P₀.1) • e₁ + (r * P₀.2) • e₂) - E =
            ((A + (r * P₀.1) • e₁ + (r * P₀.2) • e₂) - A) - (E - A) from by abel,
          inner_sub_left, hxP2, hxE2]
        ring
      have e2 : ⟪t₂ • (M - E), e₂⟫_ℝ = t₂ * (r * (0 - -s / (2 * k))) := by
        rw [inner_smul_left, starRingEnd_apply, star_trivial,
          show M - E = (M - A) - (E - A) from by abel, inner_sub_left,
          hxM2, hxE2]
        ring
      rw [e1, e2]
      linear_combination (r) * h2y
  · apply eq_of_inner_inner e₁ he1u
    · have e1 : ⟪(A + (r * P₀.1) • e₁ + (r * P₀.2) • e₂) - B, e₁⟫_ℝ =
          r * (P₀.1 - c) := by
        rw [show (A + (r * P₀.1) • e₁ + (r * P₀.2) • e₂) - B =
            ((A + (r * P₀.1) • e₁ + (r * P₀.2) • e₂) - A) - (B - A) from by abel,
          inner_sub_left, hxP1, hxB1]
        ring
      have e2 : ⟪t₃ • (D - B), e₁⟫_ℝ = t₃ * (r * (c / (2 * k) - c)) := by
        rw [inner_smul_left, starRingEnd_apply, star_trivial,
          show D - B = (D - A) - (B - A) from by abel, inner_sub_left, hxD1, hxB1]
        ring
      rw [e1, e2]
      linear_combination (r) * h3x
    · rw [← he2def]
      have e1 : ⟪(A + (r * P₀.1) • e₁ + (r * P₀.2) • e₂) - B, e₂⟫_ℝ =
          r * (P₀.2 - s) := by
        rw [show (A + (r * P₀.1) • e₁ + (r * P₀.2) • e₂) - B =
            ((A + (r * P₀.1) • e₁ + (r * P₀.2) • e₂) - A) - (B - A) from by abel,
          inner_sub_left, hxP2, hxB2]
        ring
      have e2 : ⟪t₃ • (D - B), e₂⟫_ℝ = t₃ * (r * (-s / (2 * k) - s)) := by
        rw [inner_smul_left, starRingEnd_apply, star_trivial,
          show D - B = (D - A) - (B - A) from by abel, inner_sub_left,
          hxD2, hxB2]
        ring
      rw [e1, e2]
      linear_combination (r) * h3y

snip end

problem imo2016_p1
    (A B C D E F M X : V2)
    -- convex pentagon `ABCDE`: the five consecutive turns have a common strict
    -- sign (either clockwise or counterclockwise)
    (hConvex : (0 < crss (B - A) (C - B) ∧ 0 < crss (C - B) (D - C) ∧
                  0 < crss (D - C) (E - D) ∧ 0 < crss (E - D) (A - E) ∧
                  0 < crss (A - E) (B - A)) ∨
                (crss (B - A) (C - B) < 0 ∧ crss (C - B) (D - C) < 0 ∧
                  crss (D - C) (E - D) < 0 ∧ crss (E - D) (A - E) < 0 ∧
                  crss (A - E) (B - A) < 0))
    -- `∠B > 90°` (in fact implied by the other hypotheses, see `geo_main`)
    (hB : Real.pi / 2 < ∠ A B C)
    -- `F` on `AC` with `∠FBC = 90°`
    (hF : Sbtw ℝ A F C)
    (hFBC : ∠ F B C = Real.pi / 2)
    (hFA : dist F A = dist F B)
    (hDA : dist D A = dist D C)
    (hEA : dist E A = dist E D)
    -- rays `AC` and `AD` trisect `∠BAE`
    (htri1 : ∠ B A C = ∠ C A D)
    (htri2 : ∠ C A D = ∠ D A E)
    (htri3 : ∠ B A C + ∠ C A E = ∠ B A E)
    (htri4 : ∠ C A D + ∠ D A E = ∠ C A E)
    -- `M` the midpoint of `CF`; `AMXE` a parallelogram
    (hM : M = midpoint ℝ C F)
    (hX : X - M = E - A)
    -- nondegeneracy implicit in the named angles and segments
    (hAB : A ≠ B) (hAC : A ≠ C) (hAD : A ≠ D) (hAE : A ≠ E) :
    ∃ P : V2, Collinear ℝ ({F, X, P} : Set V2) ∧ Collinear ℝ ({E, M, P} : Set V2) ∧
      Collinear ℝ ({B, D, P} : Set V2) := by
  have hcr1 : crss (B - A) (C - B) ≠ 0 := by
    rcases hConvex with ⟨h, _⟩ | ⟨h, _⟩
    · exact ne_of_gt h
    · exact ne_of_lt h
  obtain ⟨P, t₁, t₂, t₃, h1, h2, h3⟩ :=
    geo_main A B C D E F M X hcr1 hF hFBC hFA hDA hEA htri1 htri2 htri3 htri4 hM hX
      hAB hAC hAD hAE
  refine ⟨P, ?_, ?_, ?_⟩
  · rw [collinear_iff_exists_forall_eq_smul_vadd]
    refine ⟨F, X - F, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, by rw [zero_smul, zero_vadd]⟩
    · exact ⟨1, by rw [one_smul, vadd_eq_add]; abel⟩
    · exact ⟨t₁, by rw [vadd_eq_add, ← h1]; abel⟩
  · rw [collinear_iff_exists_forall_eq_smul_vadd]
    refine ⟨E, M - E, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, by rw [zero_smul, zero_vadd]⟩
    · exact ⟨1, by rw [one_smul, vadd_eq_add]; abel⟩
    · exact ⟨t₂, by rw [vadd_eq_add, ← h2]; abel⟩
  · rw [collinear_iff_exists_forall_eq_smul_vadd]
    refine ⟨B, D - B, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, by rw [zero_smul, zero_vadd]⟩
    · exact ⟨1, by rw [one_smul, vadd_eq_add]; abel⟩
    · exact ⟨t₃, by rw [vadd_eq_add, ← h3]; abel⟩

end Imo2016P1

/-!
# PROGRESS NOTES — status: COMPLETE

The bridge (`geo_main`) and the faithful statement (`imo2016_p1`) are proved;
The file compiles with no errors and no warnings (and no `sorry`).

Architecture (bottom-up):
* `concurrent_aux`: algebraic engine — for `c s : ℝ` with `c ≠ 0`,
  `2*c^2-1 ≠ 0`, the three lines through the unit-`AB` coordinate points
  (with `k := 2*c^2-1`)  B=(c,s) F=(1/(2c),0) C=(c/k,0) D=(c/(2k),-s/(2k))
  E=(1/(4c),-s/(2k)) M=((4c^2-1)/(4ck),0) X=((3c^2-1)/(2ck),-s/(2k))
  concur at P=(1/(2c)+1/(8ck), -s/(8c^2 k)) with affine parameters
  t₁=1/(4c^2), t₂=t₃=(4c^2-1)/(4c^2).  (field_simp; field_simp; ring.)
* Linear-algebra infrastructure on `V2 := EuclideanSpace ℝ (Fin 2)`:
  `Jrot` (rotation by π/2), `crss` (2D cross product), `inner_fin2`,
  `eq_smul_smul_of_unit` (basis representation), `eq_of_inner_inner`
  (a vector is determined by its two coordinates), `inner_coord`
  (inner product in an orthonormal frame — turns all metric computation
  into real arithmetic), `inner_coord_left/right`, `sbtw_smul`.
* `geo_main`: from the geometric hypotheses builds the frame
  `e₁ = (C-A)/‖C-A‖`, `e₂ = Jrot e₁` and derives all point coordinates
  (B, F, C, D, E, M, X) as explicit scalars times `r = ‖B-A‖`, with
  `c = cos θ`, `s` the signed sine, `k = 2c²-1`; the two sidedness
  exclusions (D on the opposite side of `AC` from `B`; `E` beyond `AD`)
  are proved from the angle-sum hypotheses, and `k > 0`, `c > 0`,
  `s ≠ 0` from betweenness and the convexity cross.  It then scales the
  `concurrent_aux` witnesses and checks line membership via
  `eq_of_inner_inner`.
* `imo2016_p1`: faithful statement; packages the vector equalities as
  `Collinear` via `collinear_iff_exists_forall_eq_smul_vadd`.

Gotchas encountered (mathlib v4.32):
* `0 • e₂` elaborates to ℕ-smul; write `(0 : ℝ) • e₂`.
* `set` (let-bound variables) confuses `ring`/`linear_combination`
  (inconsistent zeta-unfolding); use `obtain ⟨x, hx⟩` for plain fvars.
* `field_simp` needs `smul_eq_mul` to turn `•` into `*`, sometimes two
  passes, and its discharger only accepts ≠0-facts in matching
  (ring-normalized) form; `div_eq_iff_mul_eq`/`div_eq_div_iff` +
  `linear_combination` are the deterministic fallback.
* `ring` does not cancel `x * x⁻¹`, nor move `-` across `/`.
* `nlinarith` explodes in large contexts; use `nlinarith only [...]` or
  `linear_combination` with hand-computed coefficients.
* `midpoint_eq_smul_add` needs `Invertible (2:ℝ)` (numeral-instance
  mismatch); instead unfold `midpoint`/`lineMap_apply_module` and
  normalize `⅟2` with `invOf_eq_inv` to plain `2⁻¹`.
-/
