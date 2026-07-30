/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Geometry.Euclidean.Sphere.Power
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 2009, Problem 1

Given circles ω₁ and ω₂ intersecting at points X and Y, let ℓ₁ be a line
through the center of ω₁ intersecting ω₂ at points P and Q and let ℓ₂ be a
line through the center of ω₂ intersecting ω₁ at points R and S.
Prove that if P, Q, R and S lie on a circle then the center of this circle
lies on line XY.
-/

open Affine EuclideanGeometry Module

open scoped InnerProductSpace

namespace Usa2009P1

variable {V Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
  [NormedAddTorsor V Pt]

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

snip begin

/-- If two spheres both pass through the points `a` and `b`, then every point of
the line `ab` has the same power with respect to both spheres: the difference of
the two powers is an affine function on the line `ab` (the quadratic terms cancel),
and it vanishes at `a` and at `b`, hence on the whole line. This is the part of
"the radical axis of two circles meeting at `a` and `b` is the line `ab`" that holds
in any dimension. -/
theorem power_eq_power_of_mem_of_mem_line {s t : Sphere Pt} {a b p : Pt}
    (ha : a ∈ s) (hb : b ∈ s) (hat : a ∈ t) (hbt : b ∈ t)
    (hp : p ∈ line[ℝ, a, b]) :
    s.power p = t.power p := by
  rw [mem_sphere, dist_eq_norm_vsub V a s.center] at ha
  rw [mem_sphere, dist_eq_norm_vsub V b s.center] at hb
  rw [mem_sphere, dist_eq_norm_vsub V a t.center] at hat
  rw [mem_sphere, dist_eq_norm_vsub V b t.center] at hbt
  rw [← vsub_vadd p a, vadd_left_mem_affineSpan_pair] at hp
  obtain ⟨c, hc⟩ := hp
  -- The components of the two centers along `b -ᵥ a` coincide, since `a` and `b`
  -- are equidistant from each center.
  have hs_key : 2 * ⟪b -ᵥ a, a -ᵥ s.center⟫_ℝ = -‖b -ᵥ a‖ ^ 2 := by
    have h : ‖b -ᵥ s.center‖ ^ 2 = ‖a -ᵥ s.center‖ ^ 2 := by rw [hb, ha]
    rw [← vsub_add_vsub_cancel b a s.center, norm_add_sq_real] at h
    linarith
  have ht_key : 2 * ⟪b -ᵥ a, a -ᵥ t.center⟫_ℝ = -‖b -ᵥ a‖ ^ 2 := by
    have h : ‖b -ᵥ t.center‖ ^ 2 = ‖a -ᵥ t.center‖ ^ 2 := by rw [hbt, hat]
    rw [← vsub_add_vsub_cancel b a t.center, norm_add_sq_real] at h
    linarith
  have hs_r : ‖a -ᵥ s.center‖ ^ 2 = s.radius ^ 2 := by rw [ha]
  have ht_r : ‖a -ᵥ t.center‖ ^ 2 = t.radius ^ 2 := by rw [hat]
  have e1 : p -ᵥ s.center = c • (b -ᵥ a) + (a -ᵥ s.center) := by
    rw [← vsub_add_vsub_cancel p a s.center, ← hc]
  have e2 : p -ᵥ t.center = c • (b -ᵥ a) + (a -ᵥ t.center) := by
    rw [← vsub_add_vsub_cancel p a t.center, ← hc]
  have hnorm : ‖c • (b -ᵥ a)‖ ^ 2 = c ^ 2 * ‖b -ᵥ a‖ ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  show dist p s.center ^ 2 - s.radius ^ 2 = dist p t.center ^ 2 - t.radius ^ 2
  rw [dist_eq_norm_vsub V p s.center, dist_eq_norm_vsub V p t.center, e1, e2,
    norm_add_sq_real, norm_add_sq_real, hnorm, real_inner_smul_left, real_inner_smul_left]
  linear_combination c * hs_key - c * ht_key + hs_r - ht_r

/-- In the plane, the radical axis of two spheres with distinct centers meeting
at two distinct points `x` and `y` is the line `xy`: any point whose powers with
respect to the two spheres coincide lies on the line `xy`. -/
theorem mem_line_of_power_eq_power [Fact (finrank ℝ V = 2)] {s₁ s₂ : Sphere Pt} {x y z : Pt}
    (hs : s₁.center ≠ s₂.center)
    (hx : x ∈ s₁) (hx₂ : x ∈ s₂) (hy : y ∈ s₁) (hy₂ : y ∈ s₂)
    (hxy : x ≠ y) (hz : s₁.power z = s₂.power z) :
    z ∈ line[ℝ, x, y] := by
  set o := s₂.center -ᵥ s₁.center with ho
  have ho0 : o ≠ 0 := vsub_ne_zero.mpr hs.symm
  -- Equality of the two powers at `w` is a linear equation in `w -ᵥ s₁.center`.
  let L : V →ₗ[ℝ] ℝ :=
    { toFun := fun v => 2 * ⟪v, o⟫_ℝ
      map_add' := fun u v => by simp only [inner_add_left, mul_add]
      map_smul' := fun r v => by
        simp only [real_inner_smul_left, RingHom.id_apply, smul_eq_mul]; ring }
  have hL : ∀ v : V, L v = 2 * ⟪v, o⟫_ℝ := fun _ => rfl
  have hpw : ∀ w : Pt, s₁.power w = s₂.power w ↔
      L (w -ᵥ s₁.center) = ‖o‖ ^ 2 + s₁.radius ^ 2 - s₂.radius ^ 2 := by
    intro w
    have e : w -ᵥ s₂.center = (w -ᵥ s₁.center) - o :=
      (vsub_sub_vsub_cancel_right w s₂.center s₁.center).symm
    simp only [Sphere.power, dist_eq_norm_vsub V, e, norm_sub_sq_real, hL]
    constructor <;> intro h <;> linarith
  have hpx : s₁.power x = s₂.power x := by
    show dist x s₁.center ^ 2 - s₁.radius ^ 2 = dist x s₂.center ^ 2 - s₂.radius ^ 2
    rw [mem_sphere] at hx hx₂
    rw [hx, hx₂, sub_self, sub_self]
  have hpy : s₁.power y = s₂.power y := by
    show dist y s₁.center ^ 2 - s₁.radius ^ 2 = dist y s₂.center ^ 2 - s₂.radius ^ 2
    rw [mem_sphere] at hy hy₂
    rw [hy, hy₂, sub_self, sub_self]
  have hLx := (hpw x).mp hpx
  have hLy := (hpw y).mp hpy
  have hLz := (hpw z).mp hz
  -- Hence `y -ᵥ x` and `z -ᵥ x` both lie in the kernel of `L`.
  have hyx : y -ᵥ x ∈ LinearMap.ker L := by
    rw [LinearMap.mem_ker,
      show y -ᵥ x = (y -ᵥ s₁.center) - (x -ᵥ s₁.center) from
        (vsub_sub_vsub_cancel_right y x s₁.center).symm,
      map_sub, hLy, hLx, sub_self]
  have hzx : z -ᵥ x ∈ LinearMap.ker L := by
    rw [LinearMap.mem_ker,
      show z -ᵥ x = (z -ᵥ s₁.center) - (x -ᵥ s₁.center) from
        (vsub_sub_vsub_cancel_right z x s₁.center).symm,
      map_sub, hLz, hLx, sub_self]
  -- `L` is nonzero, so its kernel is one-dimensional.
  have hL0 : L o ≠ 0 := by
    rw [hL, real_inner_self_eq_norm_sq]
    exact mul_ne_zero two_ne_zero (pow_ne_zero 2 (norm_ne_zero_iff.mpr ho0))
  have hfd : finrank ℝ V = 2 := Fact.out
  have hrank1 : finrank ℝ ↥(LinearMap.range L) = 1 := by
    have hpos : 0 < finrank ℝ ↥(LinearMap.range L) := by
      haveI : Nontrivial ↥(LinearMap.range L) :=
        ⟨⟨L o, LinearMap.mem_range_self L o⟩, 0, fun he => hL0 (Subtype.ext_iff.mp he)⟩
      exact finrank_pos
    have hle : finrank ℝ ↥(LinearMap.range L) ≤ finrank ℝ ℝ := Submodule.finrank_le _
    rw [finrank_self] at hle
    omega
  have hker : finrank ℝ ↥(LinearMap.ker L) = 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker L
    omega
  -- So the kernel is spanned by the nonzero vector `y -ᵥ x`.
  have hyx0 : y -ᵥ x ≠ 0 := vsub_ne_zero.mpr hxy.symm
  have hspan : ℝ ∙ (y -ᵥ x) = LinearMap.ker L :=
    Submodule.eq_of_le_of_finrank_eq
      ((Submodule.span_singleton_le_iff_mem _ _).mpr hyx)
      (by rw [finrank_span_singleton hyx0, hker])
  obtain ⟨t, ht⟩ := (Submodule.mem_span_singleton).mp (hspan.symm ▸ hzx)
  have hfinal : t • (y -ᵥ x) +ᵥ x = z := by rw [ht, vsub_vadd]
  rw [← hfinal]
  exact smul_vsub_vadd_mem_affineSpan_pair t x y

snip end

/-- We follow the solution from
[Evan Chen's notes](https://web.evanchen.cc/exams/USAMO-2009-notes.pdf).
Let `r₁`, `r₂`, `r₃` be the radii of `ω₁`, `ω₂`, `ω₃`, where `ω₃` is the circle
through `P, Q, R, S`. Since `O₁` lies on the radical axis `PQ` of `ω₂` and `ω₃`,
`O₁O₂² - r₂² = O₁O₃² - r₃²`; similarly `O₁O₂² - r₁² = O₂O₃² - r₃²`. Subtracting
gives `O₁O₃² - r₁² = O₂O₃² - r₂²`, i.e. `O₃` has equal powers with respect to
`ω₁` and `ω₂`, so it lies on their radical axis, which is the line `XY`. -/
problem usa2009_p1 [Fact (finrank ℝ V = 2)] {ω₁ ω₂ ω₃ : Sphere Pt} {X Y P Q R S : Pt}
    (hω : ω₁ ≠ ω₂) (hXY : X ≠ Y)
    (hX₁ : X ∈ ω₁) (hX₂ : X ∈ ω₂) (hY₁ : Y ∈ ω₁) (hY₂ : Y ∈ ω₂)
    (hP : P ∈ ω₂) (hQ : Q ∈ ω₂) (_hPQ : P ≠ Q)
    (hℓ₁ : ω₁.center ∈ line[ℝ, P, Q])
    (hR : R ∈ ω₁) (hS : S ∈ ω₁) (_hRS : R ≠ S)
    (hℓ₂ : ω₂.center ∈ line[ℝ, R, S])
    (hP₃ : P ∈ ω₃) (hQ₃ : Q ∈ ω₃) (hR₃ : R ∈ ω₃) (hS₃ : S ∈ ω₃) :
    ω₃.center ∈ line[ℝ, X, Y] := by
  have hO : ω₁.center ≠ ω₂.center :=
    fun h => hω ((Sphere.center_eq_iff_eq_of_mem hX₁ hX₂).mp h)
  -- `O₁` has equal powers with respect to `ω₂` and `ω₃` (it lies on line `PQ`).
  have h1 : ω₂.power ω₁.center = ω₃.power ω₁.center :=
    power_eq_power_of_mem_of_mem_line hP hQ hP₃ hQ₃ hℓ₁
  -- `O₂` has equal powers with respect to `ω₁` and `ω₃` (it lies on line `RS`).
  have h2 : ω₁.power ω₂.center = ω₃.power ω₂.center :=
    power_eq_power_of_mem_of_mem_line hR hS hR₃ hS₃ hℓ₂
  -- Subtracting, `O₃` has equal powers with respect to `ω₁` and `ω₂`.
  have h3 : ω₁.power ω₃.center = ω₂.power ω₃.center := by
    show dist ω₃.center ω₁.center ^ 2 - ω₁.radius ^ 2 =
      dist ω₃.center ω₂.center ^ 2 - ω₂.radius ^ 2
    have h1' : dist ω₁.center ω₂.center ^ 2 - ω₂.radius ^ 2 =
        dist ω₁.center ω₃.center ^ 2 - ω₃.radius ^ 2 := h1
    have h2' : dist ω₂.center ω₁.center ^ 2 - ω₁.radius ^ 2 =
        dist ω₂.center ω₃.center ^ 2 - ω₃.radius ^ 2 := h2
    rw [dist_comm ω₂.center ω₁.center] at h2'
    rw [dist_comm ω₃.center ω₁.center, dist_comm ω₃.center ω₂.center]
    linarith
  exact mem_line_of_power_eq_power hO hX₁ hX₂ hY₁ hY₂ hXY h3

end Usa2009P1
