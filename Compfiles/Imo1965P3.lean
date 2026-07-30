/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.Separation.CompletelyRegular
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Geometry]
}

/-!
# International Mathematical Olympiad 1965, Problem 3

The tetrahedron ABCD is divided into two parts by a plane parallel to AB and CD.
The distance of the plane from AB is k times its distance from CD.
Find the ratio of the volumes of the two parts.

# Formalization notes

Write the ambient space as `E = (ℝ × ℝ) × ℝ`. Since `A, B, C, D` are affinely
independent (here expressed as the linear independence of `B - A`, `C - A`, `D - A`),
there is a unique affine function `f : E → ℝ` with `f = 0` on the line `AB` and
`f = 1` on the line `CD` (namely, the sum of the barycentric coordinates of `C`
and `D`). A plane parallel to both lines `AB` and `CD` is exactly a level set
`{f = t}` for some `0 < t < 1`, and because the level sets of `f` are parallel
planes, the distances from `{f = t}` to the lines `AB` and `CD` are proportional
to `t` and `1 - t` respectively. Hence the distance condition of the problem
amounts to `t / (1 - t) = k`, i.e. `t = k / (k + 1)`.

The affine map `L` sending the reference tetrahedron (the standard simplex) to
`ABCD` sends `{f ≤ t}` to `{y + z ≤ t}` in coordinates. All volumes scale by the
same factor `|det L|`, so the required ratio equals the ratio of the volumes of
the reference regions

  `R_le(t) = {((y, z), x) : x, y, z ≥ 0, y + z ≤ t, x + y + z ≤ 1}`,
  `R_ge(t) = {((y, z), x) : x, y, z ≥ 0, t ≤ y + z, x + y + z ≤ 1}`,

which are computed by Tonelli's theorem (Fubini for nonnegative functions):
the slice of `R_le(t)` at `y + z = s` is a rectangle of area `s (1 - s)`, so
`vol R_le(t) = ∫₀ᵗ s (1 - s) ds = t² / 2 - t³ / 3`. With `t = k / (k + 1)` the
ratio `vol R_le(t) / vol R_ge(t)` simplifies to `k² (k + 3) / (3 k + 1)`.
-/

namespace Imo1965P3

open MeasureTheory Set
open scoped ENNReal

/-- The ambient three-dimensional space, coordinatized as `((y, z), x)`. -/
abbrev E := (ℝ × ℝ) × ℝ

noncomputable determine ratio (k : ℝ) : ℝ := k ^ 2 * (k + 3) / (3 * k + 1)

snip begin

/-- The reference region `{((y, z), x) : x, y, z ≥ 0, y + z ≤ t, x + y + z ≤ 1}`:
the part of the reference simplex on the `AB` side of the cutting plane. -/
def refLe (t : ℝ) : Set E :=
  {p | 0 ≤ p.2 ∧ 0 ≤ p.1.1 ∧ 0 ≤ p.1.2 ∧ p.1.1 + p.1.2 ≤ t ∧ p.2 + p.1.1 + p.1.2 ≤ 1}

/-- The reference region `{((y, z), x) : x, y, z ≥ 0, t ≤ y + z, x + y + z ≤ 1}`:
the part of the reference simplex on the `CD` side of the cutting plane. -/
def refGe (t : ℝ) : Set E :=
  {p | 0 ≤ p.2 ∧ 0 ≤ p.1.1 ∧ 0 ≤ p.1.2 ∧ t ≤ p.1.1 + p.1.2 ∧ p.2 + p.1.1 + p.1.2 ≤ 1}

/-- The 2D reference region `{(y, z) : y, z ≥ 0, y + z ≤ t}`. -/
def ref2 (t : ℝ) : Set (ℝ × ℝ) := {q | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ t}

/-- The 2D reference segment `{(y, z) : y, z ≥ 0, y + z = t}`. -/
def line2 (t : ℝ) : Set (ℝ × ℝ) := {q | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 = t}

/-- The linear map sending the standard basis vectors to `u, v, w`. -/
def linMap (u v w : E) : E →ₗ[ℝ] E :=
  (LinearMap.snd ℝ (ℝ × ℝ) ℝ).smulRight u +
    ((LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.fst ℝ (ℝ × ℝ) ℝ)).smulRight v +
      ((LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.fst ℝ (ℝ × ℝ) ℝ)).smulRight w

/-- The affine map sending the reference tetrahedron to the tetrahedron `ABCD`. -/
def affMap (A B C D : E) : E → E := fun p => A + linMap (B - A) (C - A) (D - A) p

/-- The tetrahedron with vertices `A`, `B`, `C`, `D`. -/
def tetrahedron (A B C D : E) : Set E := affMap A B C D '' refLe 1

/-- The part of the tetrahedron `ABCD` on the `AB` side of the plane parallel to
`AB` and `CD` whose distance from `AB` is `k` times its distance from `CD`. -/
def partAB (A B C D : E) (k : ℝ) : Set E := affMap A B C D '' refLe (k / (k + 1))

/-- The part of the tetrahedron `ABCD` on the `CD` side of the plane parallel to
`AB` and `CD` whose distance from `AB` is `k` times its distance from `CD`. -/
def partCD (A B C D : E) (k : ℝ) : Set E := affMap A B C D '' refGe (k / (k + 1))

@[simp]
lemma linMap_apply (u v w p : E) :
    linMap u v w p = p.2 • u + p.1.1 • v + p.1.2 • w := by
  simp [linMap]

lemma measurableSet_refLe (t : ℝ) : MeasurableSet (refLe t) := by
  have h : refLe t =
      {p : E | (0 : ℝ) ≤ p.2} ∩ {p : E | (0 : ℝ) ≤ p.1.1} ∩ {p : E | (0 : ℝ) ≤ p.1.2} ∩
        {p : E | p.1.1 + p.1.2 ≤ t} ∩ {p : E | p.2 + p.1.1 + p.1.2 ≤ 1} := by
    ext p
    simp only [refLe, mem_setOf_eq, mem_inter_iff]
    tauto
  rw [h]
  exact ((((measurableSet_le (by fun_prop) (by fun_prop)).inter
    (measurableSet_le (by fun_prop) (by fun_prop))).inter
    (measurableSet_le (by fun_prop) (by fun_prop))).inter
    (measurableSet_le (by fun_prop) (by fun_prop))).inter
    (measurableSet_le (by fun_prop) (by fun_prop))

lemma measurableSet_refGe (t : ℝ) : MeasurableSet (refGe t) := by
  have h : refGe t =
      {p : E | (0 : ℝ) ≤ p.2} ∩ {p : E | (0 : ℝ) ≤ p.1.1} ∩ {p : E | (0 : ℝ) ≤ p.1.2} ∩
        {p : E | t ≤ p.1.1 + p.1.2} ∩ {p : E | p.2 + p.1.1 + p.1.2 ≤ 1} := by
    ext p
    simp only [refGe, mem_setOf_eq, mem_inter_iff]
    tauto
  rw [h]
  exact ((((measurableSet_le (by fun_prop) (by fun_prop)).inter
    (measurableSet_le (by fun_prop) (by fun_prop))).inter
    (measurableSet_le (by fun_prop) (by fun_prop))).inter
    (measurableSet_le (by fun_prop) (by fun_prop))).inter
    (measurableSet_le (by fun_prop) (by fun_prop))

lemma measurableSet_ref2 (t : ℝ) : MeasurableSet (ref2 t) := by
  have h : ref2 t =
      {q : ℝ × ℝ | (0 : ℝ) ≤ q.1} ∩ {q : ℝ × ℝ | (0 : ℝ) ≤ q.2} ∩
        {q : ℝ × ℝ | q.1 + q.2 ≤ t} := by
    ext q
    simp only [ref2, mem_setOf_eq, mem_inter_iff]
    tauto
  rw [h]
  exact ((measurableSet_le (by fun_prop) (by fun_prop)).inter
    (measurableSet_le (by fun_prop) (by fun_prop))).inter
    (measurableSet_le (by fun_prop) (by fun_prop))

lemma measurableSet_line2 (t : ℝ) : MeasurableSet (line2 t) := by
  have h : line2 t =
      {q : ℝ × ℝ | (0 : ℝ) ≤ q.1} ∩ {q : ℝ × ℝ | (0 : ℝ) ≤ q.2} ∩
        {q : ℝ × ℝ | q.1 + q.2 = t} := by
    ext q
    simp only [line2, mem_setOf_eq, mem_inter_iff]
    tauto
  rw [h]
  exact ((measurableSet_le (by fun_prop) (by fun_prop)).inter
    (measurableSet_le (by fun_prop) (by fun_prop))).inter
    (measurableSet_eq_fun (by fun_prop) (by fun_prop))

/-- For fixed `(y, z)`, the fiber of `refLe t` is the interval `Icc 0 (1 - y - z)`
whenever `(y, z) ∈ ref2 t`, so the innermost integral equals
`ENNReal.ofReal (1 - y - z)` on `ref2 t` and vanishes elsewhere. -/
lemma lintegral_indicator_refLe_fst (t : ℝ) (q : ℝ × ℝ) :
    ∫⁻ x : ℝ, (refLe t).indicator (1 : E → ℝ≥0∞) (q, x) ∂volume =
      (ref2 t).indicator (fun q => ENNReal.ofReal (1 - q.1 - q.2)) q := by
  by_cases hq : q ∈ ref2 t
  · have hset : (fun x : ℝ => (refLe t).indicator (1 : E → ℝ≥0∞) (q, x)) =
        (Icc 0 (1 - q.1 - q.2)).indicator (1 : ℝ → ℝ≥0∞) := by
      funext x
      by_cases hx : x ∈ Icc (0 : ℝ) (1 - q.1 - q.2)
      · obtain ⟨hx0, hx1⟩ := mem_Icc.mp hx
        rw [Set.indicator_of_mem hx,
          Set.indicator_of_mem (show (q, x) ∈ refLe t from
            ⟨hx0, hq.1, hq.2.1, hq.2.2, by linarith⟩)]
        rfl
      · rw [Set.indicator_of_notMem hx]
        exact Set.indicator_of_notMem (fun h => hx (mem_Icc.mpr ⟨h.1, by
          linarith [h.2.2.2.2]⟩)) 1
    rw [hset, lintegral_indicator_one measurableSet_Icc, Real.volume_Icc,
      Set.indicator_of_mem hq]
    simp
  · rw [Set.indicator_of_notMem hq]
    have hset : (fun x : ℝ => (refLe t).indicator (1 : E → ℝ≥0∞) (q, x)) = fun _ => 0 := by
      funext x
      exact Set.indicator_of_notMem (fun h => hq ⟨h.2.1, h.2.2.1, h.2.2.2.1⟩) 1
    rw [hset]
    simp

/-- For fixed `y ∈ Icc 0 t`, the inner integral over `z` equals
`ENNReal.ofReal ((1 - y) * (t - y) - (t - y) ^ 2 / 2)`. -/
lemma lintegral_indicator_ref2_snd (t : ℝ) (_ht0 : 0 ≤ t) (ht1 : t ≤ 1) (y : ℝ) :
    ∫⁻ z : ℝ, (ref2 t).indicator (fun q => ENNReal.ofReal (1 - q.1 - q.2)) (y, z) ∂volume =
      (Icc 0 t).indicator (fun y => ENNReal.ofReal ((1 - y) * (t - y) - (t - y) ^ 2 / 2)) y := by
  by_cases hy : y ∈ Icc (0 : ℝ) t
  · obtain ⟨hy0, hyt⟩ := mem_Icc.mp hy
    have hset : (fun z : ℝ =>
        (ref2 t).indicator (fun q => ENNReal.ofReal (1 - q.1 - q.2)) (y, z)) =
        (Icc 0 (t - y)).indicator (fun z => ENNReal.ofReal (1 - y - z)) := by
      funext z
      by_cases hz : z ∈ Icc (0 : ℝ) (t - y)
      · obtain ⟨hz0, hz1⟩ := mem_Icc.mp hz
        rw [Set.indicator_of_mem hz,
          Set.indicator_of_mem (show (y, z) ∈ ref2 t from ⟨hy0, hz0, by linarith⟩)]
      · rw [Set.indicator_of_notMem hz]
        exact Set.indicator_of_notMem (fun h => hz (mem_Icc.mpr ⟨h.2.1, by
          linarith [h.2.2]⟩)) _
    have hint : Integrable (fun z : ℝ => 1 - y - z) (volume.restrict (Icc 0 (t - y))) :=
      (continuous_const.sub continuous_id).integrableOn_Icc
    have hnn : 0 ≤ᵐ[volume.restrict (Icc 0 (t - y))] (fun z : ℝ => 1 - y - z) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
      obtain ⟨-, hz1⟩ := mem_Icc.mp hz
      show (0 : ℝ) ≤ 1 - y - z
      linarith
    rw [hset, lintegral_indicator measurableSet_Icc,
      ← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (sub_nonneg.mpr hyt), Set.indicator_of_mem hy]
    congr 1
    have hF : ∀ z : ℝ, HasDerivAt (fun z => (1 - y) * z - z ^ 2 / 2) ((1 - y) * 1 - z) z := by
      intro z
      have h1 : HasDerivAt (fun z : ℝ => (1 - y) * z) ((1 - y) * 1) z :=
        (hasDerivAt_id z).const_mul (1 - y)
      have h2 : HasDerivAt (fun z : ℝ => z ^ 2 / 2) z z := by
        have h := (hasDerivAt_pow 2 z).div_const 2
        rw [show z ^ (2 - 1) = z from pow_one z] at h
        simp only [Nat.cast_ofNat] at h
        rwa [show (2 : ℝ) * z / 2 = z by ring] at h
      exact h1.sub h2
    have hfg : ∀ z : ℝ, 1 - y - z = (1 - y) * 1 - z := fun z => by ring
    simp_rw [hfg]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z _ => hF z)
      ((continuous_const.sub continuous_id).intervalIntegrable _ _)]
    ring
  · rw [Set.indicator_of_notMem hy]
    have hset : (fun z : ℝ =>
        (ref2 t).indicator (fun q => ENNReal.ofReal (1 - q.1 - q.2)) (y, z)) = fun _ => 0 := by
      funext z
      exact Set.indicator_of_notMem (fun h => hy (mem_Icc.mpr ⟨h.1, by
        linarith [h.2.1, h.2.2]⟩)) _
    rw [hset]
    simp

/-- The volume of the reference region on the `AB` side. -/
lemma volume_refLe (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    volume (refLe t) = ENNReal.ofReal (t ^ 2 / 2 - t ^ 3 / 3) := by
  rw [← lintegral_indicator_one (measurableSet_refLe t)]
  have hmeas : AEMeasurable ((refLe t).indicator (1 : E → ℝ≥0∞)) (volume.prod volume) :=
    ((measurable_const.indicator (measurableSet_refLe t)).aemeasurable)
  rw [show (volume : Measure E) = volume.prod volume from rfl, lintegral_prod _ hmeas,
    lintegral_congr (lintegral_indicator_refLe_fst t)]
  have hmeas2 : AEMeasurable
      ((ref2 t).indicator (fun q : ℝ × ℝ => ENNReal.ofReal (1 - q.1 - q.2)))
      (volume.prod volume) :=
    ((ENNReal.measurable_ofReal.comp
      ((measurable_const.sub measurable_fst).sub measurable_snd)).indicator
      (measurableSet_ref2 t)).aemeasurable
  rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
    lintegral_prod _ hmeas2, lintegral_congr (lintegral_indicator_ref2_snd t ht0 ht1)]
  have hint : Integrable (fun y : ℝ => (1 - y) * (t - y) - (t - y) ^ 2 / 2)
      (volume.restrict (Icc 0 t)) :=
    (by fun_prop : Continuous fun y : ℝ => (1 - y) * (t - y) - (t - y) ^ 2 / 2).integrableOn_Icc
  have hnn : 0 ≤ᵐ[volume.restrict (Icc 0 t)]
      (fun y : ℝ => (1 - y) * (t - y) - (t - y) ^ 2 / 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    obtain ⟨hy0, hyt⟩ := mem_Icc.mp hy
    have h : (1 - y) * (t - y) - (t - y) ^ 2 / 2 = (t - y) * (1 - t / 2 - y / 2) := by ring
    rw [h]
    exact mul_nonneg (by linarith) (by linarith)
  rw [lintegral_indicator measurableSet_Icc,
    ← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le ht0]
  congr 1
  have hexp : ∀ y : ℝ, (1 - y) * (t - y) - (t - y) ^ 2 / 2 = t - t ^ 2 / 2 - y + y ^ 2 / 2 :=
    fun y => by ring
  simp_rw [hexp]
  have hF : ∀ y : ℝ, HasDerivAt (fun y => (t - t ^ 2 / 2) * y - y ^ 2 / 2 + y ^ 3 / 6)
      ((t - t ^ 2 / 2) * 1 - y + y ^ 2 / 2) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => (t - t ^ 2 / 2) * y) ((t - t ^ 2 / 2) * 1) y :=
      (hasDerivAt_id y).const_mul (t - t ^ 2 / 2)
    have h2 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) y y := by
      have h := (hasDerivAt_pow 2 y).div_const 2
      rw [show y ^ (2 - 1) = y from pow_one y] at h
      simp only [Nat.cast_ofNat] at h
      rwa [show (2 : ℝ) * y / 2 = y by ring] at h
    have h3 : HasDerivAt (fun y : ℝ => y ^ 3 / 6) (y ^ 2 / 2) y := by
      have h := (hasDerivAt_pow 3 y).div_const 6
      rw [show y ^ (3 - 1) = y ^ 2 from rfl] at h
      simp only [Nat.cast_ofNat] at h
      rwa [show (3 : ℝ) * y ^ 2 / 6 = y ^ 2 / 2 by ring] at h
    exact (h1.sub h2).add h3
  have hfg : ∀ y : ℝ, t - t ^ 2 / 2 - y + y ^ 2 / 2 = (t - t ^ 2 / 2) * 1 - y + y ^ 2 / 2 :=
    fun y => by ring
  simp_rw [hfg]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hF y)
    ((by fun_prop : Continuous fun y : ℝ => (t - t ^ 2 / 2) * 1 - y + y ^ 2 / 2).intervalIntegrable
      _ _)]
  ring

/-- The 2D reference segment has measure zero. -/
lemma volume_line2 (t : ℝ) : volume (line2 t) = 0 := by
  rw [← lintegral_indicator_one (measurableSet_line2 t)]
  have hmeas : AEMeasurable ((line2 t).indicator (1 : (ℝ × ℝ) → ℝ≥0∞)) (volume.prod volume) :=
    ((measurable_const.indicator (measurableSet_line2 t)).aemeasurable)
  rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl, lintegral_prod _ hmeas]
  apply le_antisymm _ bot_le
  calc ∫⁻ y : ℝ, ∫⁻ z : ℝ, (line2 t).indicator (1 : (ℝ × ℝ) → ℝ≥0∞) (y, z) ∂volume ∂volume
      ≤ ∫⁻ y : ℝ, ∫⁻ z : ℝ, ({t - y} : Set ℝ).indicator (1 : ℝ → ℝ≥0∞) z ∂volume ∂volume := by
        apply lintegral_mono
        intro y
        apply lintegral_mono
        intro z
        show (line2 t).indicator (1 : (ℝ × ℝ) → ℝ≥0∞) (y, z) ≤
          ({t - y} : Set ℝ).indicator (1 : ℝ → ℝ≥0∞) z
        by_cases hz : (y, z) ∈ line2 t
        · rw [Set.indicator_of_mem hz]
          exact le_of_eq (Set.indicator_of_mem
            (mem_singleton_iff.mpr (show z = t - y by linarith [hz.2.2])) (1 : ℝ → ℝ≥0∞)).symm
        · rw [Set.indicator_of_notMem hz]
          exact bot_le
    _ = ∫⁻ y : ℝ, volume ({t - y} : Set ℝ) ∂volume := by
        apply lintegral_congr
        intro y
        exact lintegral_indicator_one (measurableSet_singleton (t - y))
    _ = 0 := by simp

/-- The intersection `refLe t ∩ refGe t` is contained in a plane, hence has measure zero. -/
lemma volume_refLe_inter_refGe (t : ℝ) : volume (refLe t ∩ refGe t) = 0 := by
  have hset : refLe t ∩ refGe t =
      {p : E | (0 : ℝ) ≤ p.2 ∧ 0 ≤ p.1.1 ∧ 0 ≤ p.1.2 ∧ p.1.1 + p.1.2 = t ∧
        p.2 + p.1.1 + p.1.2 ≤ 1} := by
    ext p
    constructor
    · rintro ⟨⟨hx, hy, hz, hle, hsum⟩, -, -, -, hge, -⟩
      exact ⟨hx, hy, hz, le_antisymm hle hge, hsum⟩
    · rintro ⟨hx, hy, hz, heq, hsum⟩
      exact ⟨⟨hx, hy, hz, heq.le, hsum⟩, hx, hy, hz, heq.ge, hsum⟩
  rw [hset]
  have hmeas : MeasurableSet
      {p : E | (0 : ℝ) ≤ p.2 ∧ 0 ≤ p.1.1 ∧ 0 ≤ p.1.2 ∧ p.1.1 + p.1.2 = t ∧
        p.2 + p.1.1 + p.1.2 ≤ 1} := by
    have h : {p : E | (0 : ℝ) ≤ p.2 ∧ 0 ≤ p.1.1 ∧ 0 ≤ p.1.2 ∧ p.1.1 + p.1.2 = t ∧
        p.2 + p.1.1 + p.1.2 ≤ 1} =
        {p : E | (0 : ℝ) ≤ p.2} ∩ {p : E | (0 : ℝ) ≤ p.1.1} ∩ {p : E | (0 : ℝ) ≤ p.1.2} ∩
          {p : E | p.1.1 + p.1.2 = t} ∩ {p : E | p.2 + p.1.1 + p.1.2 ≤ 1} := by
      ext p
      simp only [mem_setOf_eq, mem_inter_iff]
      tauto
    rw [h]
    exact ((((measurableSet_le (by fun_prop) (by fun_prop)).inter
      (measurableSet_le (by fun_prop) (by fun_prop))).inter
      (measurableSet_le (by fun_prop) (by fun_prop))).inter
      (measurableSet_eq_fun (by fun_prop) (by fun_prop))).inter
      (measurableSet_le (by fun_prop) (by fun_prop))
  rw [← lintegral_indicator_one hmeas]
  have hmeas' : AEMeasurable
      ({p : E | (0 : ℝ) ≤ p.2 ∧ 0 ≤ p.1.1 ∧ 0 ≤ p.1.2 ∧ p.1.1 + p.1.2 = t ∧
        p.2 + p.1.1 + p.1.2 ≤ 1}.indicator (1 : E → ℝ≥0∞)) (volume.prod volume) :=
    (measurable_const.indicator hmeas).aemeasurable
  rw [show (volume : Measure E) = volume.prod volume from rfl, lintegral_prod _ hmeas']
  have hinner : ∀ q : ℝ × ℝ,
      ∫⁻ x : ℝ, {p : E | (0 : ℝ) ≤ p.2 ∧ 0 ≤ p.1.1 ∧ 0 ≤ p.1.2 ∧ p.1.1 + p.1.2 = t ∧
        p.2 + p.1.1 + p.1.2 ≤ 1}.indicator (1 : E → ℝ≥0∞) (q, x) ∂volume =
      (line2 t).indicator (fun _ => ENNReal.ofReal (1 - t)) q := by
    intro q
    by_cases hq : q ∈ line2 t
    · have hset2 : (fun x : ℝ =>
          {p : E | (0 : ℝ) ≤ p.2 ∧ 0 ≤ p.1.1 ∧ 0 ≤ p.1.2 ∧ p.1.1 + p.1.2 = t ∧
            p.2 + p.1.1 + p.1.2 ≤ 1}.indicator (1 : E → ℝ≥0∞) (q, x)) =
          (Icc 0 (1 - t)).indicator (1 : ℝ → ℝ≥0∞) := by
        funext x
        by_cases hx : x ∈ Icc (0 : ℝ) (1 - t)
        · obtain ⟨hx0, hx1⟩ := mem_Icc.mp hx
          rw [Set.indicator_of_mem hx,
            Set.indicator_of_mem (show (q, x) ∈
              {p : E | (0 : ℝ) ≤ p.2 ∧ 0 ≤ p.1.1 ∧ 0 ≤ p.1.2 ∧ p.1.1 + p.1.2 = t ∧
                p.2 + p.1.1 + p.1.2 ≤ 1} from
              ⟨hx0, hq.1, hq.2.1, hq.2.2, by show x + q.1 + q.2 ≤ 1; linarith [hq.2.2]⟩)]
          rfl
        · rw [Set.indicator_of_notMem hx]
          exact Set.indicator_of_notMem (fun h => hx (mem_Icc.mpr ⟨h.1, by
            linarith [h.2.2.2.1, h.2.2.2.2]⟩)) 1
      rw [hset2, lintegral_indicator_one measurableSet_Icc, Real.volume_Icc,
        Set.indicator_of_mem hq]
      simp
    · rw [Set.indicator_of_notMem hq]
      have hset2 : (fun x : ℝ =>
          {p : E | (0 : ℝ) ≤ p.2 ∧ 0 ≤ p.1.1 ∧ 0 ≤ p.1.2 ∧ p.1.1 + p.1.2 = t ∧
            p.2 + p.1.1 + p.1.2 ≤ 1}.indicator (1 : E → ℝ≥0∞) (q, x)) = fun _ => 0 := by
        funext x
        exact Set.indicator_of_notMem (fun h => hq ⟨h.2.1, h.2.2.1, h.2.2.2.1⟩) 1
      rw [hset2]
      simp
  rw [lintegral_congr hinner, lintegral_indicator_const (measurableSet_line2 t), volume_line2,
    mul_zero]

/-- The volume of the reference region on the `CD` side. -/
lemma volume_refGe (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    volume (refGe t) = ENNReal.ofReal ((1 - t) ^ 2 / 2 - (1 - t) ^ 3 / 3) := by
  have hunion : refLe 1 = refLe t ∪ refGe t := by
    ext p
    simp only [refLe, refGe, mem_setOf_eq, mem_union]
    constructor
    · rintro ⟨hx, hy, hz, -, hsum⟩
      rcases le_total (p.1.1 + p.1.2) t with h | h
      · exact Or.inl ⟨hx, hy, hz, h, hsum⟩
      · exact Or.inr ⟨hx, hy, hz, h, hsum⟩
    · rintro (⟨hx, hy, hz, h1, h2⟩ | ⟨hx, hy, hz, h1, h2⟩)
      · exact ⟨hx, hy, hz, by linarith, h2⟩
      · exact ⟨hx, hy, hz, by linarith, h2⟩
  have h := measure_union_add_inter (refLe t) (measurableSet_refGe t) (μ := volume)
  rw [volume_refLe_inter_refGe, add_zero, ← hunion, volume_refLe 1 zero_le_one le_rfl,
    volume_refLe t ht0 ht1] at h
  have h' : volume (refGe t) + ENNReal.ofReal (t ^ 2 / 2 - t ^ 3 / 3) =
      ENNReal.ofReal (1 ^ 2 / 2 - 1 ^ 3 / 3) := by
    rw [add_comm]
    exact h.symm
  have h2 := ENNReal.eq_sub_of_add_eq ENNReal.ofReal_ne_top h'
  have hnn : 0 ≤ t ^ 2 / 2 - t ^ 3 / 3 := by
    have hrw : t ^ 2 / 2 - t ^ 3 / 3 = t ^ 2 * (3 - 2 * t) / 6 := by ring
    rw [hrw]
    exact div_nonneg (mul_nonneg (sq_nonneg t) (by linarith)) (by norm_num)
  rw [h2, ← ENNReal.ofReal_sub _ hnn]
  congr 1
  ring

/-- If `B - A, C - A, D - A` are linearly independent, the map `linMap (B - A) (C - A) (D - A)`
has nonzero determinant. -/
lemma det_linMap_ne_zero {A B C D : E} (h : LinearIndependent ℝ ![B - A, C - A, D - A]) :
    LinearMap.det (linMap (B - A) (C - A) (D - A)) ≠ 0 := by
  have key : ∀ p : E, linMap (B - A) (C - A) (D - A) p = 0 → p = 0 := by
    intro p hp
    rw [linMap_apply] at hp
    have h2 := (Fintype.linearIndependent_iff.mp h) ![p.2, p.1.1, p.1.2] (by
      rw [Fin.sum_univ_three]
      simpa using hp)
    have e0 : p.2 = 0 := by simpa using h2 0
    have e1 : p.1.1 = 0 := by simpa using h2 1
    have e2 : p.1.2 = 0 := by simpa using h2 2
    exact Prod.ext (Prod.ext e1 e2) e0
  have hinj : Function.Injective (linMap (B - A) (C - A) (D - A)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    exact key
  have hbij : Function.Bijective (linMap (B - A) (C - A) (D - A)) :=
    ⟨hinj, LinearMap.surjective_of_injective hinj⟩
  have hdet : IsUnit (LinearMap.det (linMap (B - A) (C - A) (D - A))) :=
    LinearEquiv.isUnit_det' (LinearEquiv.ofBijective _ hbij)
  exact hdet.ne_zero

/-- The coercion of `LinearMap.equivOfDetNeZero` agrees with the original map. -/
lemma coe_equivOfDetNeZero (M : E →ₗ[ℝ] E) (hM : LinearMap.det M ≠ 0) :
    ((M.equivOfDetNeZero hM : E ≃ₗ[ℝ] E) : E → E) = (M : E → E) := by
  funext x
  exact LinearMap.congr_fun (LinearEquiv.coe_ofIsUnitDet _) x

/-- Volumes scale by `|det|` under the affine map `p ↦ A + M p`. -/
lemma volume_image_aff (A : E) (M : E →ₗ[ℝ] E) (hM : LinearMap.det M ≠ 0)
    (s : Set E) (hs : MeasurableSet s) :
    volume ((fun p => A + M p) '' s) = ENNReal.ofReal |LinearMap.det M| * volume s := by
  have himg : (fun p => A + M p) '' s = (fun q => A + q) '' (M '' s) := by
    ext y
    simp only [mem_image]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨M p, ⟨p, hp, rfl⟩, rfl⟩
    · rintro ⟨q, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨p, hp, rfl⟩
  have hpre : (fun q => A + q) '' (M '' s) = (fun q => q - A) ⁻¹' (M '' s) := by
    ext y
    simp only [mem_image, mem_preimage]
    constructor
    · rintro ⟨q, hq, rfl⟩
      simpa using hq
    · intro hy
      exact ⟨y - A, hy, by simp⟩
  have hmeas : MeasurableSet (M '' s) := by
    rw [← coe_equivOfDetNeZero M hM,
      Set.image_eq_preimage_of_inverse (fun x => (M.equivOfDetNeZero hM).symm_apply_apply x)
        (fun y => (M.equivOfDetNeZero hM).apply_symm_apply y)]
    exact (LinearMap.continuous_of_finiteDimensional
      ((M.equivOfDetNeZero hM).symm : E →ₗ[ℝ] E)).measurable hs
  have hf : (fun q : E => q - A) = (fun q => -A + q) := funext fun q => sub_eq_neg_add q A
  haveI : MeasureTheory.Measure.IsAddHaarMeasure (volume : Measure (ℝ × ℝ)) :=
    MeasureTheory.Measure.prod.instIsAddHaarMeasure _ _
  haveI : MeasureTheory.Measure.IsAddHaarMeasure (volume : Measure E) :=
    MeasureTheory.Measure.prod.instIsAddHaarMeasure _ _
  have hmp : MeasurePreserving (-A + ·) volume volume := measurePreserving_add_left volume (-A)
  have hvol : volume ((fun q => -A + q) ⁻¹' (M '' s)) = volume (M '' s) := by
    rw [← Measure.map_apply hmp.measurable hmeas, hmp.map_eq]
  rw [himg, hpre, hf, hvol]
  exact MeasureTheory.Measure.addHaar_image_linearMap volume M s

lemma volume_partAB {A B C D : E} (h : LinearIndependent ℝ ![B - A, C - A, D - A])
    (k : ℝ) (hk : 0 < k) :
    volume (partAB A B C D k) =
      ENNReal.ofReal |LinearMap.det (linMap (B - A) (C - A) (D - A))| *
        ENNReal.ofReal ((k / (k + 1)) ^ 2 / 2 - (k / (k + 1)) ^ 3 / 3) := by
  have hk1 : (0 : ℝ) < k + 1 := by linarith
  have ht0 : 0 ≤ k / (k + 1) := by positivity
  have ht1 : k / (k + 1) ≤ 1 := by
    rw [div_le_one hk1]
    linarith
  simp only [partAB, affMap]
  rw [volume_image_aff A _ (det_linMap_ne_zero h) _ (measurableSet_refLe _),
    volume_refLe _ ht0 ht1]

lemma volume_partCD {A B C D : E} (h : LinearIndependent ℝ ![B - A, C - A, D - A])
    (k : ℝ) (hk : 0 < k) :
    volume (partCD A B C D k) =
      ENNReal.ofReal |LinearMap.det (linMap (B - A) (C - A) (D - A))| *
        ENNReal.ofReal ((1 - k / (k + 1)) ^ 2 / 2 - (1 - k / (k + 1)) ^ 3 / 3) := by
  have hk1 : (0 : ℝ) < k + 1 := by linarith
  have ht0 : 0 ≤ k / (k + 1) := by positivity
  have ht1 : k / (k + 1) ≤ 1 := by
    rw [div_le_one hk1]
    linarith
  simp only [partCD, affMap]
  rw [volume_image_aff A _ (det_linMap_ne_zero h) _ (measurableSet_refGe _),
    volume_refGe _ ht0 ht1]

snip end

problem imo1965_p3 (A B C D : E) (h : LinearIndependent ℝ ![B - A, C - A, D - A])
    (k : ℝ) (hk : 0 < k) :
    volume (partAB A B C D k) / volume (partCD A B C D k) = ENNReal.ofReal (ratio k) := by
  have hk1 : (0 : ℝ) < k + 1 := by linarith
  have h3k : (0 : ℝ) < 3 * k + 1 := by positivity
  have hdet := det_linMap_ne_zero h
  have ht0 : 0 ≤ k / (k + 1) := by positivity
  have ht1 : k / (k + 1) < 1 := by
    rw [div_lt_one hk1]
    linarith
  have hv : 0 < (1 - k / (k + 1)) ^ 2 / 2 - (1 - k / (k + 1)) ^ 3 / 3 := by
    have h1t : (0 : ℝ) < 1 - k / (k + 1) := by linarith
    have hrw : (1 - k / (k + 1)) ^ 2 / 2 - (1 - k / (k + 1)) ^ 3 / 3 =
        (1 - k / (k + 1)) ^ 2 * (1 + 2 * (k / (k + 1))) / 6 := by ring
    rw [hrw]
    positivity
  have hpos : 0 < |LinearMap.det (linMap (B - A) (C - A) (D - A))| *
      ((1 - k / (k + 1)) ^ 2 / 2 - (1 - k / (k + 1)) ^ 3 / 3) :=
    mul_pos (abs_pos.mpr hdet) hv
  rw [volume_partAB h k hk, volume_partCD h k hk, ← ENNReal.ofReal_mul (abs_nonneg _),
    ← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_div_of_pos hpos]
  simp only [ratio]
  congr 1
  have hd0 : |LinearMap.det (linMap (B - A) (C - A) (D - A))| ≠ 0 := abs_ne_zero.mpr hdet
  have hk10 : k + 1 ≠ 0 := ne_of_gt hk1
  have h3k0 : 3 * k + 1 ≠ 0 := ne_of_gt h3k
  have hu : (k / (k + 1)) ^ 2 / 2 - (k / (k + 1)) ^ 3 / 3 = k ^ 2 * (k + 3) / (6 * (k + 1) ^ 3) := by
    field_simp
    ring
  have hv' : (1 - k / (k + 1)) ^ 2 / 2 - (1 - k / (k + 1)) ^ 3 / 3 =
      (3 * k + 1) / (6 * (k + 1) ^ 3) := by
    field_simp
    ring
  rw [hu, hv',
    div_eq_div_iff (mul_ne_zero hd0
      (ne_of_gt (show (0 : ℝ) < (3 * k + 1) / (6 * (k + 1) ^ 3) by positivity))) h3k0]
  field_simp

end Imo1965P3
