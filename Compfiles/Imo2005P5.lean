/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Geometry.Euclidean.Angle.Sphere
public import Mathlib.RingTheory.SimpleRing.Principal
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 2005, Problem 5

Let `ABCD` be a fixed convex quadrilateral with `BC = DA` and `BC ∦ DA`. Let two variable
points `E` and `F` lie on the sides `BC` and `DA`, respectively, and satisfy `BE = DF`.
The lines `AC` and `BD` meet at `P`, the lines `BD` and `EF` meet at `Q`, the lines `EF`
and `AC` meet at `R`. Prove that the circumcircles of the triangles `PQR`, as `E` and `F`
vary, have a common point other than `P`.
-/

namespace Imo2005P5

open EuclideanGeometry Complex

open scoped EuclideanGeometry ComplexConjugate

attribute [local instance] Complex.finrank_real_complex_fact

/-- The standard orientation of `ℂ`, used for the oriented-angle formulation of
concyclicity. -/
noncomputable local instance : Module.Oriented ℝ ℂ (Fin 2) := ⟨Complex.orientation⟩

snip begin

/-!
## Proof outline

We use complex numbers. Let `M` be the center of the (unique) orientation-preserving
similarity of ratio `1` (a rotation) sending the segment `DA` onto the segment `BC`;
concretely, with `ω := (B - C) / (D - A)` (which satisfies `‖ω‖ = 1`, `ω ≠ 1` and
`ω ≠ -1`) we set `m := (B - ω * D) / (1 - ω)`, so that `C - m = ω * (A - m)` and
`B - m = ω * (D - m)`. Writing `a := A - m`, `d := D - m`, and parametrizing
`E = B + s * (C - B)`, `F = D + s * (A - D)` (which is equivalent to `BE = DF` as
`BC = DA`), one has `F - m = f` and `E - m = ω * f` with `f := d + s * (a - d)`.

The line through the points `m + z` and `m + ω * z` (for `z ≠ 0`) is characterized by the
equation `(X - z) * conj ((ω - 1) * z) = conj (X - z) * ((ω - 1) * z)`, and the
intersection of the two lines for `z` and `w` is
`m + (1 + ω) * (z * w * (conj z - conj w)) / (conj z * w - conj w * z)`.
Hence `P - m`, `Q - m`, `R - m` are given by this formula applied to `(a, d)`, `(d, f)`,
`(f, a)` respectively. A (large) polynomial identity then shows that the cross-ratio
`(conj (Q - P) * (R - P)) / (conj (Q - M) * (R - M))` is real, which says that twice the
oriented angle `∡ Q P R` equals twice the oriented angle `∡ Q M R`, and the conclusion
`Concyclic {P, Q, R, M}` follows from
`EuclideanGeometry.cospherical_or_collinear_of_two_zsmul_oangle_eq`.
-/

section helpers

/-- Three points `0, x, y` in `ℂ` are collinear iff `y / x` is real, expressed
algebraically. -/
lemma collinear_zero_iff {x y : ℂ} (hx : x ≠ 0) :
    Collinear ℝ ({0, x, y} : Set ℂ) ↔ conj x * y = conj y * x := by
  constructor
  · intro h
    rw [collinear_iff_of_mem (Set.mem_insert 0 _)] at h
    obtain ⟨v, hv⟩ := h
    obtain ⟨r₁, hr₁⟩ := hv x (by simp)
    obtain ⟨r₂, hr₂⟩ := hv y (by simp)
    rw [hr₁, hr₂]
    simp only [vadd_eq_add, add_zero, Complex.real_smul, map_mul, Complex.conj_ofReal]
    ring
  · intro h
    rw [collinear_iff_of_mem (Set.mem_insert 0 _)]
    refine ⟨x, fun p hp => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | hy
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · rw [hy]
      have hcx : conj x ≠ 0 := by simp [hx]
      have hz : conj (y / x) = y / x := by
        rw [map_div₀]
        have e : conj y * x = y * conj x := by rw [← h]; ring
        field_simp [hcx]
        linear_combination e
      obtain ⟨t, ht⟩ := conj_eq_iff_real.mp hz
      refine ⟨t, ?_⟩
      simp only [vadd_eq_add, add_zero, Complex.real_smul]
      rw [← ht]
      field_simp [hx]

/-- If three points are collinear, the middle one is an affine combination of the other
two, in vector form. -/
lemma exists_smul_eq_of_collinear {x y z : ℂ} (hxz : x ≠ z)
    (h : Collinear ℝ ({x, y, z} : Set ℂ)) : ∃ t : ℝ, y - x = t • (z - x) := by
  rw [collinear_iff_of_mem (Set.mem_insert x _)] at h
  obtain ⟨v, hv⟩ := h
  obtain ⟨r₁, hr₁⟩ := hv y (by simp)
  obtain ⟨r₂, hr₂⟩ := hv z (by simp)
  have hr₂ne : r₂ ≠ 0 := by
    rintro rfl
    apply hxz
    rw [hr₂]
    simp
  refine ⟨r₁ / r₂, ?_⟩
  have e1 : y - x = r₁ • v := by
    rw [hr₁]
    simp
  have e2 : z - x = r₂ • v := by
    rw [hr₂]
    simp
  rw [e1, e2, smul_smul, div_mul_cancel₀ _ hr₂ne]

/-- `conj x = 0` implies `x = 0`. -/
lemma conj_eq_zero {x : ℂ} (h : conj x = 0) : x = 0 := by
  have e := congrArg conj h
  rw [starRingEnd_self_apply] at e
  have h0 : conj (0 : ℂ) = 0 := by simp
  rw [h0] at e
  exact e

/-- Conjugation preserves being nonzero. -/
lemma conj_ne_zero {x : ℂ} (hx : x ≠ 0) : conj x ≠ 0 := fun h => hx (conj_eq_zero h)

/-- The real multiple of a complex number has the same argument, up to a sign. -/
lemma two_zsmul_arg_of_real_mul {w : ℂ} (hw : w ≠ 0) {t : ℝ} (ht : t ≠ 0) :
    (2 : ℤ) • (Complex.arg ((t : ℂ) * w) : Real.Angle) =
      (2 : ℤ) • (Complex.arg w : Real.Angle) := by
  rcases lt_or_gt_of_ne ht with htn | htp
  · have e : (t : ℂ) * w = -(((-t : ℝ) : ℂ) * w) := by simp
    have hwx : ((-t : ℝ) : ℂ) * w ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr (neg_ne_zero.mpr htn.ne)) hw
    rw [e, Complex.arg_neg_coe_angle hwx,
      Complex.arg_real_mul _ (by linarith : (0 : ℝ) < -t), smul_add,
      Real.Angle.two_zsmul_coe_pi, add_zero]
  · rw [Complex.arg_real_mul _ htp]

end helpers

/-- The configuration of the problem: four points of the plane satisfying the
non-degeneracy conditions of a (not necessarily convex) quadrilateral with `BC = DA`
and `BC ∦ DA`, together with the condition `AC ∦ BD` ensuring that the intersection
point `P` of the diagonals is well defined. -/
structure Cfg where
  A : ℂ
  B : ℂ
  C : ℂ
  D : ℂ
  hAC : A ≠ C
  hBD : B ≠ D
  hAD : A ≠ D
  hBC : B ≠ C
  hlen : dist B C = dist D A
  hpar : ¬ Collinear ℝ ({0, A - D, B - C} : Set ℂ)
  hdiag : ¬ Collinear ℝ ({0, C - A, D - B} : Set ℂ)

namespace Cfg

variable (cfg : Cfg)

/-- The complex ratio of the rotation sending `DA` to `BC`. -/
noncomputable def ω : ℂ := (cfg.B - cfg.C) / (cfg.D - cfg.A)

/-- The center of the rotation sending `DA` to `BC`. -/
noncomputable def m : ℂ := (cfg.B - cfg.ω * cfg.D) / (1 - cfg.ω)

/-- The point `E` of the problem, parametrized by `s : ℝ` (for `s ∈ [0, 1]` it ranges
over the segment `BC`). -/
noncomputable def ptE (s : ℝ) : ℂ := cfg.B + (s : ℂ) * (cfg.C - cfg.B)

/-- The point `F` of the problem, parametrized by the same `s : ℝ`; the condition
`BC = DA` makes `BE = DF` automatic. -/
noncomputable def ptF (s : ℝ) : ℂ := cfg.D + (s : ℂ) * (cfg.A - cfg.D)

variable {cfg : Cfg}

lemma hDA : cfg.D - cfg.A ≠ 0 := sub_ne_zero.mpr (Ne.symm cfg.hAD)

lemma hBC' : cfg.B - cfg.C ≠ 0 := sub_ne_zero.mpr cfg.hBC

lemma ω_ne_zero : cfg.ω ≠ 0 := by
  simp only [Cfg.ω]
  exact div_ne_zero hBC' hDA

lemma hωc : cfg.ω * conj cfg.ω = 1 := by
  have h1 : cfg.ω * conj cfg.ω = Complex.normSq cfg.ω := Complex.mul_conj _
  have hlen2 : ‖cfg.B - cfg.C‖ = ‖cfg.D - cfg.A‖ := by
    have h := cfg.hlen
    rwa [dist_eq_norm, dist_eq_norm] at h
  have hDA2 : ‖cfg.D - cfg.A‖ ≠ 0 := norm_ne_zero_iff.mpr hDA
  rw [h1]
  simp only [Cfg.ω]
  rw [Complex.normSq_div]
  simp only [Complex.normSq_eq_norm_sq]
  rw [hlen2, div_self (pow_ne_zero 2 hDA2), Complex.ofReal_one]

lemma ω_ne_one : cfg.ω ≠ 1 := by
  intro h
  apply cfg.hpar
  have e : cfg.B - cfg.C = cfg.D - cfg.A := by
    have e1 : cfg.B - cfg.C = cfg.ω * (cfg.D - cfg.A) := by
      simp only [Cfg.ω]
      rw [div_mul_cancel₀ _ hDA]
    rw [h] at e1
    simpa using e1
  rw [collinear_zero_iff (sub_ne_zero.mpr cfg.hAD)]
  rw [e]
  have e2 : cfg.D - cfg.A = -(cfg.A - cfg.D) := by ring
  rw [e2, map_neg]
  ring

lemma ω_ne_neg_one : cfg.ω ≠ -1 := by
  intro h
  apply cfg.hpar
  have e : cfg.B - cfg.C = cfg.A - cfg.D := by
    have e1 : cfg.B - cfg.C = cfg.ω * (cfg.D - cfg.A) := by
      simp only [Cfg.ω]
      rw [div_mul_cancel₀ _ hDA]
    rw [h] at e1
    have e2 : cfg.B - cfg.C = -(cfg.D - cfg.A) := by
      rw [e1]
      simp
    linear_combination e2
  rw [collinear_zero_iff (sub_ne_zero.mpr cfg.hAD)]
  rw [e]

lemma hCB : cfg.C - cfg.B = cfg.ω * (cfg.A - cfg.D) := by
  simp only [Cfg.ω]
  field_simp [hDA]
  ring

lemma hmB : cfg.B - cfg.m = cfg.ω * (cfg.D - cfg.m) := by
  have h1 : (1 : ℂ) - cfg.ω ≠ 0 := sub_ne_zero.mpr (Ne.symm ω_ne_one)
  have e : cfg.m * (1 - cfg.ω) = cfg.B - cfg.ω * cfg.D := by
    simp only [Cfg.m]
    rw [div_mul_cancel₀ _ h1]
  linear_combination -e

lemma hmC : cfg.C - cfg.m = cfg.ω * (cfg.A - cfg.m) := by
  have h1 : (1 : ℂ) - cfg.ω ≠ 0 := sub_ne_zero.mpr (Ne.symm ω_ne_one)
  have e : cfg.m * (1 - cfg.ω) = cfg.B - cfg.ω * cfg.D := by
    simp only [Cfg.m]
    rw [div_mul_cancel₀ _ h1]
  linear_combination -e + hCB

lemma ha_ne : cfg.A - cfg.m ≠ 0 := by
  intro h
  have hA : cfg.A = cfg.m := sub_eq_zero.mp h
  have hC : cfg.C = cfg.m := by
    have hc : cfg.C - cfg.m = 0 := by
      rw [hmC, h]
      simp
    exact sub_eq_zero.mp hc
  exact cfg.hAC (hA.trans hC.symm)

lemma hd_ne : cfg.D - cfg.m ≠ 0 := by
  intro h
  have hD : cfg.D = cfg.m := sub_eq_zero.mp h
  have hB : cfg.B = cfg.m := by
    have hb : cfg.B - cfg.m = 0 := by
      rw [hmB, h]
      simp
    exact sub_eq_zero.mp hb
  exact cfg.hBD (hB.trans hD.symm)

lemma hD_ad : conj (cfg.A - cfg.m) * (cfg.D - cfg.m) -
    conj (cfg.D - cfg.m) * (cfg.A - cfg.m) ≠ 0 := by
  intro h
  apply cfg.hdiag
  have hcoll : Collinear ℝ ({0, cfg.A - cfg.m, cfg.D - cfg.m} : Set ℂ) :=
    (collinear_zero_iff ha_ne).mpr (sub_eq_zero.mp h)
  rw [Set.pair_comm (cfg.A - cfg.m) (cfg.D - cfg.m)] at hcoll
  obtain ⟨t, ht⟩ := exists_smul_eq_of_collinear ha_ne.symm hcoll
  rw [sub_zero, sub_zero] at ht
  rw [collinear_zero_iff (sub_ne_zero.mpr (Ne.symm cfg.hAC))]
  have eCA : cfg.C - cfg.A = (cfg.ω - 1) * (cfg.A - cfg.m) := by
    have e : cfg.C - cfg.A = (cfg.C - cfg.m) - (cfg.A - cfg.m) := by ring
    rw [e, hmC]
    ring
  have eDB : cfg.D - cfg.B = (1 - cfg.ω) * (cfg.D - cfg.m) := by
    have e : cfg.D - cfg.B = (cfg.D - cfg.m) - (cfg.B - cfg.m) := by ring
    rw [e, hmB]
    ring
  rw [eCA, eDB, ht, Complex.real_smul]
  simp only [map_mul, map_sub, map_one, Complex.conj_ofReal]
  ring

lemma hf_sub (s : ℝ) :
    cfg.ptF s - cfg.m = (cfg.D - cfg.m) + (s : ℂ) * ((cfg.A - cfg.m) - (cfg.D - cfg.m)) := by
  simp only [Cfg.ptF]
  ring

lemma he_sub (s : ℝ) :
    cfg.ptE s - cfg.m = cfg.ω * (cfg.ptF s - cfg.m) := by
  have e1 : cfg.B + (s : ℂ) * (cfg.C - cfg.B) - cfg.m =
      (cfg.B - cfg.m) + (s : ℂ) * (cfg.C - cfg.B) := by ring
  rw [hf_sub]
  simp only [Cfg.ptE]
  rw [e1, hmB, hCB]
  ring

lemma hf_ne (s : ℝ) : cfg.ptF s - cfg.m ≠ 0 := by
  intro h
  rw [hf_sub] at h
  have hf : (cfg.D - cfg.m) * (1 - (s : ℂ)) = -(s : ℂ) * (cfg.A - cfg.m) := by
    linear_combination h
  have hD0 : (1 - (s : ℂ)) * (conj (cfg.A - cfg.m) * (cfg.D - cfg.m) -
      conj (cfg.D - cfg.m) * (cfg.A - cfg.m)) = 0 := by
    have e : (1 - (s : ℂ)) * (conj (cfg.A - cfg.m) * (cfg.D - cfg.m) -
        conj (cfg.D - cfg.m) * (cfg.A - cfg.m)) =
        conj (cfg.A - cfg.m) * ((cfg.D - cfg.m) * (1 - (s : ℂ))) -
          conj ((cfg.D - cfg.m) * (1 - (s : ℂ))) * (cfg.A - cfg.m) := by
      simp only [map_mul, map_sub, map_one, Complex.conj_ofReal]
      ring
    rw [e, hf]
    simp only [map_neg, map_mul, Complex.conj_ofReal]
    ring
  rcases mul_eq_zero.mp hD0 with hs1 | hD0'
  · have h1 : s = 1 := by
      have h1s : (1 : ℂ) = (s : ℂ) := sub_eq_zero.mp hs1
      rw [← Complex.ofReal_one, Complex.ofReal_inj] at h1s
      exact h1s.symm
    rw [h1] at h
    simp at h
    have hAm : cfg.A - cfg.m = 0 := by linear_combination h
    exact ha_ne hAm
  · exact hD_ad hD0'

lemma hD_df {s : ℝ}
    (hn : ¬ Collinear ℝ ({0, cfg.ptF s - cfg.ptE s, cfg.D - cfg.B} : Set ℂ)) :
    conj (cfg.D - cfg.m) * (cfg.ptF s - cfg.m) -
      conj (cfg.ptF s - cfg.m) * (cfg.D - cfg.m) ≠ 0 := by
  have hFE : cfg.ptF s - cfg.ptE s ≠ 0 := by
    intro h0
    apply hn
    rw [h0]
    have hset : ({0, 0, cfg.D - cfg.B} : Set ℂ) = {0, cfg.D - cfg.B} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [hset]
    exact collinear_pair ℝ 0 (cfg.D - cfg.B)
  intro h
  apply hn
  have hcoll : Collinear ℝ ({0, cfg.D - cfg.m, cfg.ptF s - cfg.m} : Set ℂ) :=
    (collinear_zero_iff hd_ne).mpr (sub_eq_zero.mp h)
  rw [Set.pair_comm (cfg.D - cfg.m) (cfg.ptF s - cfg.m)] at hcoll
  obtain ⟨t, ht⟩ := exists_smul_eq_of_collinear hd_ne.symm hcoll
  rw [sub_zero, sub_zero] at ht
  rw [collinear_zero_iff hFE]
  have eFE : cfg.ptF s - cfg.ptE s = (1 - cfg.ω) * (cfg.ptF s - cfg.m) := by
    have e : cfg.ptF s - cfg.ptE s = (cfg.ptF s - cfg.m) - (cfg.ptE s - cfg.m) := by ring
    rw [e, he_sub]
    ring
  have eDB : cfg.D - cfg.B = (1 - cfg.ω) * (cfg.D - cfg.m) := by
    have e : cfg.D - cfg.B = (cfg.D - cfg.m) - (cfg.B - cfg.m) := by ring
    rw [e, hmB]
    ring
  rw [eFE, eDB, ht, Complex.real_smul]
  simp only [map_mul, map_sub, map_one, Complex.conj_ofReal]
  ring

lemma hD_fa {s : ℝ}
    (hn : ¬ Collinear ℝ ({0, cfg.ptF s - cfg.ptE s, cfg.C - cfg.A} : Set ℂ)) :
    conj (cfg.ptF s - cfg.m) * (cfg.A - cfg.m) -
      conj (cfg.A - cfg.m) * (cfg.ptF s - cfg.m) ≠ 0 := by
  have hFE : cfg.ptF s - cfg.ptE s ≠ 0 := by
    intro h0
    apply hn
    rw [h0]
    have hset : ({0, 0, cfg.C - cfg.A} : Set ℂ) = {0, cfg.C - cfg.A} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [hset]
    exact collinear_pair ℝ 0 (cfg.C - cfg.A)
  intro h
  apply hn
  have hcoll : Collinear ℝ ({0, cfg.ptF s - cfg.m, cfg.A - cfg.m} : Set ℂ) :=
    (collinear_zero_iff (hf_ne s)).mpr (sub_eq_zero.mp h)
  obtain ⟨t, ht⟩ := exists_smul_eq_of_collinear ha_ne.symm hcoll
  rw [sub_zero, sub_zero] at ht
  rw [collinear_zero_iff hFE]
  have eFE : cfg.ptF s - cfg.ptE s = (1 - cfg.ω) * (cfg.ptF s - cfg.m) := by
    have e : cfg.ptF s - cfg.ptE s = (cfg.ptF s - cfg.m) - (cfg.ptE s - cfg.m) := by ring
    rw [e, he_sub]
    ring
  have eCA : cfg.C - cfg.A = (cfg.ω - 1) * (cfg.A - cfg.m) := by
    have e : cfg.C - cfg.A = (cfg.C - cfg.m) - (cfg.A - cfg.m) := by ring
    rw [e, hmC]
    ring
  rw [eFE, eCA, ht, Complex.real_smul]
  simp only [map_mul, map_sub, map_one, Complex.conj_ofReal]
  ring

/-- The equation of the line through `m + z` and `m + ω * z`, in translated coordinates:
a point `X` (with `m` subtracted) lies on that line iff it satisfies `LineEq ω z X`. -/
def LineEq (ω z X : ℂ) : Prop :=
  (X - z) * conj ((ω - 1) * z) = conj (X - z) * ((ω - 1) * z)

lemma lineEq_of_param {ω z X : ℂ} {t : ℝ} (hX : X - z = (t : ℂ) * ((ω - 1) * z)) :
    LineEq ω z X := by
  rw [LineEq, hX]
  simp only [map_mul, Complex.conj_ofReal]
  ring

lemma lineEq_unique {ω a d X Y : ℂ} (hω : ω ≠ 1) (_ha : a ≠ 0) (_hd : d ≠ 0)
    (hD : conj a * d - conj d * a ≠ 0)
    (haX : LineEq ω a X) (hdX : LineEq ω d X)
    (haY : LineEq ω a Y) (hdY : LineEq ω d Y) : X = Y := by
  rw [LineEq] at haX hdX haY hdY
  have hΔa : (X - Y) * conj ((ω - 1) * a) = conj (X - Y) * ((ω - 1) * a) := by
    have e : X - a = X - Y + (Y - a) := by ring
    rw [e] at haX
    simp only [add_mul, map_add] at haX
    rw [haY] at haX
    exact add_right_cancel haX
  have hΔd : (X - Y) * conj ((ω - 1) * d) = conj (X - Y) * ((ω - 1) * d) := by
    have e : X - d = X - Y + (Y - d) := by ring
    rw [e] at hdX
    simp only [add_mul, map_add] at hdX
    rw [hdY] at hdX
    exact add_right_cancel hdX
  have e : (X - Y) * conj ((ω - 1) * a) * ((ω - 1) * d) =
      (X - Y) * conj ((ω - 1) * d) * ((ω - 1) * a) := by
    have m1 := congrArg (· * ((ω - 1) * d)) hΔa
    have m2 := congrArg (· * ((ω - 1) * a)) hΔd
    rw [m1, m2]
    ring
  have e2 : (X - Y) * ((ω - 1) * conj (ω - 1) * (conj a * d - conj d * a)) = 0 := by
    have fac : (ω - 1) * conj (ω - 1) * (conj a * d - conj d * a) =
        conj ((ω - 1) * a) * ((ω - 1) * d) - conj ((ω - 1) * d) * ((ω - 1) * a) := by
      simp only [map_mul, map_sub, map_one]
      ring
    rw [fac]
    linear_combination e
  rcases mul_eq_zero.mp e2 with hXY | hB
  · exact sub_eq_zero.mp hXY
  · have h1 : ω - 1 ≠ 0 := sub_ne_zero.mpr hω
    have h2 : conj (ω - 1) ≠ 0 := conj_ne_zero h1
    exact absurd hB (mul_ne_zero (mul_ne_zero h1 h2) hD)

/-- The intersection of the lines `LineEq ω a` and `LineEq ω d`, when it exists. -/
noncomputable def interPt (ω a d : ℂ) : ℂ :=
  (1 + ω) * (a * d * (conj a - conj d)) / (conj a * d - conj d * a)

lemma lineEq_inter {ω a d : ℂ} (_hω1 : ω ≠ 1) (hωc : ω * conj ω = 1)
    (ha : a ≠ 0) (hd : d ≠ 0) (hD : conj a * d - conj d * a ≠ 0) :
    LineEq ω a (interPt ω a d) ∧ LineEq ω d (interPt ω a d) := by
  have hDc : a * conj d - d * conj a ≠ 0 := by
    have e : a * conj d - d * conj a = -(conj a * d - conj d * a) := by ring
    exact e ▸ neg_ne_zero.mpr hD
  have hDD : (conj a * d - conj d * a) * (a * conj d - d * conj a) ≠ 0 :=
    mul_ne_zero hD hDc
  have hDXa : (conj a * d - conj d * a) * (interPt ω a d - a) =
      (1 + ω) * (a * d * (conj a - conj d)) - a * (conj a * d - conj d * a) := by
    rw [interPt]
    field_simp [hD]
  have hDXd : (conj a * d - conj d * a) * (interPt ω a d - d) =
      (1 + ω) * (a * d * (conj a - conj d)) - d * (conj a * d - conj d * a) := by
    rw [interPt]
    field_simp [hD]
  have hcon : (a * conj d - d * conj a) * conj (interPt ω a d - a) =
      (1 + conj ω) * (conj a * conj d * (a - d)) - conj a * (a * conj d - d * conj a) := by
    have e3 : a * conj d - d * conj a = conj (conj a * d - conj d * a) := by
      simp only [map_sub, map_mul, starRingEnd_self_apply]
    rw [e3, ← map_mul, hDXa]
    simp only [map_sub, map_mul, map_add, map_one, starRingEnd_self_apply]
  have hcond : (a * conj d - d * conj a) * conj (interPt ω a d - d) =
      (1 + conj ω) * (conj a * conj d * (a - d)) - conj d * (a * conj d - d * conj a) := by
    have e3 : a * conj d - d * conj a = conj (conj a * d - conj d * a) := by
      simp only [map_sub, map_mul, starRingEnd_self_apply]
    rw [e3, ← map_mul, hDXd]
    simp only [map_sub, map_mul, map_add, map_one, starRingEnd_self_apply]
  constructor
  · show (interPt ω a d - a) * conj ((ω - 1) * a) = conj (interPt ω a d - a) * ((ω - 1) * a)
    rw [← mul_left_inj' hDD]
    have eL : ((interPt ω a d - a) * conj ((ω - 1) * a)) *
        ((conj a * d - conj d * a) * (a * conj d - d * conj a)) =
        ((1 + ω) * (a * d * (conj a - conj d)) - a * (conj a * d - conj d * a)) *
          conj ((ω - 1) * a) * (a * conj d - d * conj a) := by
      have e : ((interPt ω a d - a) * conj ((ω - 1) * a)) *
          ((conj a * d - conj d * a) * (a * conj d - d * conj a)) =
          ((conj a * d - conj d * a) * (interPt ω a d - a)) *
            conj ((ω - 1) * a) * (a * conj d - d * conj a) := by ring
      rw [e, hDXa]
    have eR : (conj (interPt ω a d - a) * ((ω - 1) * a)) *
        ((conj a * d - conj d * a) * (a * conj d - d * conj a)) =
        ((1 + conj ω) * (conj a * conj d * (a - d)) - conj a * (a * conj d - d * conj a)) *
          ((ω - 1) * a) * (conj a * d - conj d * a) := by
      have e : (conj (interPt ω a d - a) * ((ω - 1) * a)) *
          ((conj a * d - conj d * a) * (a * conj d - d * conj a)) =
          ((a * conj d - d * conj a) * conj (interPt ω a d - a)) *
            ((ω - 1) * a) * (conj a * d - conj d * a) := by ring
      rw [e, hcon]
    rw [eL, eR]
    simp only [map_sub, map_mul, map_one]
    linear_combination
      (a^3 * conj a * (conj d)^2 - 2*a^2 * conj a * d * (conj d)^2 -
        a * (conj a)^3 * d^2 + 2*a*(conj a)^2*d^2*(conj d)) * hωc
  · show (interPt ω a d - d) * conj ((ω - 1) * d) = conj (interPt ω a d - d) * ((ω - 1) * d)
    rw [← mul_left_inj' hDD]
    have eL : ((interPt ω a d - d) * conj ((ω - 1) * d)) *
        ((conj a * d - conj d * a) * (a * conj d - d * conj a)) =
        ((1 + ω) * (a * d * (conj a - conj d)) - d * (conj a * d - conj d * a)) *
          conj ((ω - 1) * d) * (a * conj d - d * conj a) := by
      have e : ((interPt ω a d - d) * conj ((ω - 1) * d)) *
          ((conj a * d - conj d * a) * (a * conj d - d * conj a)) =
          ((conj a * d - conj d * a) * (interPt ω a d - d)) *
            conj ((ω - 1) * d) * (a * conj d - d * conj a) := by ring
      rw [e, hDXd]
    have eR : (conj (interPt ω a d - d) * ((ω - 1) * d)) *
        ((conj a * d - conj d * a) * (a * conj d - d * conj a)) =
        ((1 + conj ω) * (conj a * conj d * (a - d)) - conj d * (a * conj d - d * conj a)) *
          ((ω - 1) * d) * (conj a * d - conj d * a) := by
      have e : (conj (interPt ω a d - d) * ((ω - 1) * d)) *
          ((conj a * d - conj d * a) * (a * conj d - d * conj a)) =
          ((a * conj d - d * conj a) * conj (interPt ω a d - d)) *
            ((ω - 1) * d) * (conj a * d - conj d * a) := by ring
      rw [e, hcond]
    rw [eL, eR]
    simp only [map_sub, map_mul, map_one]
    linear_combination
      (2*a^2 * conj a * d * (conj d)^2 - a^2 * d * (conj d)^3 -
        2*a*(conj a)^2*d^2*(conj d) + (conj a)^2*d^3*(conj d)) * hωc

/-- The key polynomial identity: for the three translated intersection points
`p = interPt ω a d`, `q = interPt ω d f`, `r = interPt ω f a`, the cross-ratio
`conj (q - p) * (r - p) / (conj q * r)` is real. Here `u` plays the role of `1 + ω`;
the identity is in fact valid for arbitrary `u`. -/
lemma key_identity (u : ℂ) (s : ℝ) (a d : ℂ)
    (h1 : conj a * d - conj d * a ≠ 0)
    (h2 : conj d * (d + (s : ℂ) * (a - d)) - conj (d + (s : ℂ) * (a - d)) * d ≠ 0)
    (h3 : conj (d + (s : ℂ) * (a - d)) * a - conj a * (d + (s : ℂ) * (a - d)) ≠ 0) :
    let f := d + (s : ℂ) * (a - d)
    let p := u * (a * d * (conj a - conj d)) / (conj a * d - conj d * a)
    let q := u * (d * f * (conj d - conj f)) / (conj d * f - conj f * d)
    let r := u * (f * a * (conj f - conj a)) / (conj f * a - conj a * f)
    conj (q - p) * (r - p) * q * conj r = (q - p) * conj (r - p) * conj q * r := by
  intro f p q r
  have e1 : f = d + (s : ℂ) * (a - d) := rfl
  have e2 : p = u * (a * d * (conj a - conj d)) / (conj a * d - conj d * a) := rfl
  have e3 : q = u * (d * f * (conj d - conj f)) / (conj d * f - conj f * d) := rfl
  have e4 : r = u * (f * a * (conj f - conj a)) / (conj f * a - conj a * f) := rfl
  rw [e2, e3, e4]
  set N1 := a * d * (conj a - conj d) with hN1
  set D1 := conj a * d - conj d * a with hD1
  set N2 := d * f * (conj d - conj f) with hN2
  set D2 := conj d * f - conj f * d with hD2
  set N3 := f * a * (conj f - conj a) with hN3
  set D3 := conj f * a - conj a * f with hD3
  -- write the two differences of intersection points as single fractions
  have hqmp : u * N2 / D2 - u * N1 / D1 = (u * N2 * D1 - u * N1 * D2) / (D2 * D1) := by
    rw [div_sub_div _ _ h2 h1]; ring
  have hrmp : u * N3 / D3 - u * N1 / D1 = (u * N3 * D1 - u * N1 * D3) / (D3 * D1) := by
    rw [div_sub_div _ _ h3 h1]; ring
  rw [hqmp, hrmp]
  have eL : conj ((u * N2 * D1 - u * N1 * D2) / (D2 * D1)) *
      ((u * N3 * D1 - u * N1 * D3) / (D3 * D1)) * (u * N2 / D2) * conj (u * N3 / D3) =
    (conj u * (conj N2 * conj D1 - conj N1 * conj D2)) * (u * (N3 * D1 - N1 * D3)) *
      (u * N2) * (conj u * conj N3) /
      ((conj D2 * conj D1) * (D3 * D1) * D2 * conj D3) := by
    simp only [map_sub, map_mul, map_div₀]
    ring_nf
  have eR : ((u * N2 * D1 - u * N1 * D2) / (D2 * D1)) *
      conj ((u * N3 * D1 - u * N1 * D3) / (D3 * D1)) * conj (u * N2 / D2) * (u * N3 / D3) =
    (u * (N2 * D1 - N1 * D2)) * (conj u * (conj N3 * conj D1 - conj N1 * conj D3)) *
      (conj u * conj N2) * (u * N3) /
      ((conj D2 * conj D1) * (D3 * D1) * D2 * conj D3) := by
    simp only [map_sub, map_mul, map_div₀]
    ring_nf
  have poly : (conj u * (conj N2 * conj D1 - conj N1 * conj D2)) * (u * (N3 * D1 - N1 * D3)) *
      (u * N2) * (conj u * conj N3) =
    (u * (N2 * D1 - N1 * D2)) * (conj u * (conj N3 * conj D1 - conj N1 * conj D3)) *
      (conj u * conj N2) * (u * N3) := by
    rw [hN1, hD1, hN2, hD2, hN3, hD3, e1]
    simp only [map_add, map_sub, map_mul, starRingEnd_self_apply, Complex.conj_ofReal]
    ring
  rw [eL, eR, poly]

/-- If `conj x * y ≠ conj y * x` then `x ≠ y` even after applying `conj`. -/
lemma conj_sub_ne_zero {x y : ℂ} (h : conj x * y - conj y * x ≠ 0) : conj x - conj y ≠ 0 := by
  intro h0
  apply h
  have hxy : x = y := by
    have h1 := congrArg conj (sub_eq_zero.mp h0)
    rwa [starRingEnd_self_apply, starRingEnd_self_apply] at h1
  rw [hxy]
  simp

/-- The intersection point `P` of the diagonals, in coordinates translated by `m`. -/
lemma P_sub_m (cfg : Cfg) {P : ℂ}
    (hPAC : Collinear ℝ ({cfg.A, P, cfg.C} : Set ℂ))
    (hPBD : Collinear ℝ ({cfg.B, P, cfg.D} : Set ℂ)) :
    P - cfg.m = interPt cfg.ω (cfg.A - cfg.m) (cfg.D - cfg.m) := by
  obtain ⟨tP, htP⟩ := exists_smul_eq_of_collinear cfg.hAC hPAC
  have hPeq : (P - cfg.m) - (cfg.A - cfg.m) =
      (tP : ℂ) * ((cfg.ω - 1) * (cfg.A - cfg.m)) := by
    have e1 : P - cfg.A = (tP : ℂ) * (cfg.C - cfg.A) := by
      rw [htP, Complex.real_smul]
    have e2 : cfg.C - cfg.A = (cfg.ω - 1) * (cfg.A - cfg.m) := by
      have e : cfg.C - cfg.A = (cfg.C - cfg.m) - (cfg.A - cfg.m) := by ring
      rw [e, hmC]
      ring
    have e3 : (P - cfg.m) - (cfg.A - cfg.m) = P - cfg.A := by ring
    rw [e3, e1, e2]
  obtain ⟨tP2, htP2⟩ := exists_smul_eq_of_collinear cfg.hBD hPBD
  have hPeq2 : (P - cfg.m) - (cfg.D - cfg.m) =
      ((1 - tP2 : ℝ) : ℂ) * ((cfg.ω - 1) * (cfg.D - cfg.m)) := by
    have e1 : P - cfg.B = (tP2 : ℂ) * (cfg.D - cfg.B) := by
      rw [htP2, Complex.real_smul]
    have e2 : (cfg.ω - 1) * (cfg.D - cfg.m) = cfg.B - cfg.D := by
      have e : (cfg.ω - 1) * (cfg.D - cfg.m) = cfg.ω * (cfg.D - cfg.m) - (cfg.D - cfg.m) := by
        ring
      rw [e, ← hmB]
      ring
    have e3 : (P - cfg.m) - (cfg.D - cfg.m) = P - cfg.D := by ring
    rw [e3, e2]
    have e4 : P - cfg.D = (P - cfg.B) - (cfg.D - cfg.B) := by ring
    rw [e4, e1]
    push_cast
    ring
  exact lineEq_unique ω_ne_one ha_ne hd_ne hD_ad
    (lineEq_of_param hPeq) (lineEq_of_param hPeq2)
    (lineEq_inter ω_ne_one hωc ha_ne hd_ne hD_ad).1
    (lineEq_inter ω_ne_one hωc ha_ne hd_ne hD_ad).2

/-- The intersection point `Q` of `BD` and `EF`, in coordinates translated by `m`. -/
lemma Q_sub_m (cfg : Cfg) {s : ℝ} {Q : ℂ}
    (hQBD : Collinear ℝ ({cfg.B, Q, cfg.D} : Set ℂ))
    (hQEF : Collinear ℝ ({cfg.ptE s, Q, cfg.ptF s} : Set ℂ))
    (hn3 : ¬ Collinear ℝ ({0, cfg.ptF s - cfg.ptE s, cfg.D - cfg.B} : Set ℂ)) :
    Q - cfg.m = interPt cfg.ω (cfg.D - cfg.m) (cfg.ptF s - cfg.m) := by
  have hEF : cfg.ptE s ≠ cfg.ptF s := by
    intro h
    apply hn3
    have h0 : cfg.ptF s - cfg.ptE s = 0 := sub_eq_zero.mpr h.symm
    rw [h0]
    have hset : ({0, 0, cfg.D - cfg.B} : Set ℂ) = {0, cfg.D - cfg.B} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [hset]
    exact collinear_pair ℝ 0 (cfg.D - cfg.B)
  obtain ⟨tQ1, htQ1⟩ := exists_smul_eq_of_collinear cfg.hBD hQBD
  have hQeq1 : (Q - cfg.m) - (cfg.D - cfg.m) =
      ((1 - tQ1 : ℝ) : ℂ) * ((cfg.ω - 1) * (cfg.D - cfg.m)) := by
    have e1 : Q - cfg.B = (tQ1 : ℂ) * (cfg.D - cfg.B) := by
      rw [htQ1, Complex.real_smul]
    have e2 : (cfg.ω - 1) * (cfg.D - cfg.m) = cfg.B - cfg.D := by
      have e : (cfg.ω - 1) * (cfg.D - cfg.m) = cfg.ω * (cfg.D - cfg.m) - (cfg.D - cfg.m) := by
        ring
      rw [e, ← hmB]
      ring
    have e3 : (Q - cfg.m) - (cfg.D - cfg.m) = Q - cfg.D := by ring
    rw [e3, e2]
    have e4 : Q - cfg.D = (Q - cfg.B) - (cfg.D - cfg.B) := by ring
    rw [e4, e1]
    push_cast
    ring
  obtain ⟨tQ2, htQ2⟩ := exists_smul_eq_of_collinear hEF hQEF
  have hQeq2 : (Q - cfg.m) - (cfg.ptF s - cfg.m) =
      ((1 - tQ2 : ℝ) : ℂ) * ((cfg.ω - 1) * (cfg.ptF s - cfg.m)) := by
    have e1 : Q - cfg.ptF s = (Q - cfg.ptE s) - (cfg.ptF s - cfg.ptE s) := by ring
    have e2 : Q - cfg.ptE s = (tQ2 : ℂ) * (cfg.ptF s - cfg.ptE s) := by
      rw [htQ2, Complex.real_smul]
    have e3 : (cfg.ω - 1) * (cfg.ptF s - cfg.m) = cfg.ptE s - cfg.ptF s := by
      have e : cfg.ptE s - cfg.ptF s = (cfg.ptE s - cfg.m) - (cfg.ptF s - cfg.m) := by ring
      rw [e, he_sub]
      ring
    have e4 : (Q - cfg.m) - (cfg.ptF s - cfg.m) = Q - cfg.ptF s := by ring
    rw [e4, e1, e2, e3]
    push_cast
    ring
  exact lineEq_unique ω_ne_one hd_ne (hf_ne s) (hD_df hn3)
    (lineEq_of_param hQeq1) (lineEq_of_param hQeq2)
    (lineEq_inter ω_ne_one hωc hd_ne (hf_ne s) (hD_df hn3)).1
    (lineEq_inter ω_ne_one hωc hd_ne (hf_ne s) (hD_df hn3)).2

/-- The intersection point `R` of `EF` and `AC`, in coordinates translated by `m`. -/
lemma R_sub_m (cfg : Cfg) {s : ℝ} {R : ℂ}
    (hREF : Collinear ℝ ({cfg.ptE s, R, cfg.ptF s} : Set ℂ))
    (hRAC : Collinear ℝ ({cfg.A, R, cfg.C} : Set ℂ))
    (hn4 : ¬ Collinear ℝ ({0, cfg.ptF s - cfg.ptE s, cfg.C - cfg.A} : Set ℂ)) :
    R - cfg.m = interPt cfg.ω (cfg.ptF s - cfg.m) (cfg.A - cfg.m) := by
  have hEF : cfg.ptE s ≠ cfg.ptF s := by
    intro h
    apply hn4
    have h0 : cfg.ptF s - cfg.ptE s = 0 := sub_eq_zero.mpr h.symm
    rw [h0]
    have hset : ({0, 0, cfg.C - cfg.A} : Set ℂ) = {0, cfg.C - cfg.A} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [hset]
    exact collinear_pair ℝ 0 (cfg.C - cfg.A)
  obtain ⟨tR1, htR1⟩ := exists_smul_eq_of_collinear hEF hREF
  have hReq1 : (R - cfg.m) - (cfg.ptF s - cfg.m) =
      ((1 - tR1 : ℝ) : ℂ) * ((cfg.ω - 1) * (cfg.ptF s - cfg.m)) := by
    have e1 : R - cfg.ptF s = (R - cfg.ptE s) - (cfg.ptF s - cfg.ptE s) := by ring
    have e2 : R - cfg.ptE s = (tR1 : ℂ) * (cfg.ptF s - cfg.ptE s) := by
      rw [htR1, Complex.real_smul]
    have e3 : (cfg.ω - 1) * (cfg.ptF s - cfg.m) = cfg.ptE s - cfg.ptF s := by
      have e : cfg.ptE s - cfg.ptF s = (cfg.ptE s - cfg.m) - (cfg.ptF s - cfg.m) := by ring
      rw [e, he_sub]
      ring
    have e4 : (R - cfg.m) - (cfg.ptF s - cfg.m) = R - cfg.ptF s := by ring
    rw [e4, e1, e2, e3]
    push_cast
    ring
  obtain ⟨tR2, htR2⟩ := exists_smul_eq_of_collinear cfg.hAC hRAC
  have hReq2 : (R - cfg.m) - (cfg.A - cfg.m) =
      (tR2 : ℂ) * ((cfg.ω - 1) * (cfg.A - cfg.m)) := by
    have e1 : R - cfg.A = (tR2 : ℂ) * (cfg.C - cfg.A) := by
      rw [htR2, Complex.real_smul]
    have e2 : cfg.C - cfg.A = (cfg.ω - 1) * (cfg.A - cfg.m) := by
      have e : cfg.C - cfg.A = (cfg.C - cfg.m) - (cfg.A - cfg.m) := by ring
      rw [e, hmC]
      ring
    have e3 : (R - cfg.m) - (cfg.A - cfg.m) = R - cfg.A := by ring
    rw [e3, e1, e2]
  exact lineEq_unique ω_ne_one (hf_ne s) ha_ne (hD_fa hn4)
    (lineEq_of_param hReq1) (lineEq_of_param hReq2)
    (lineEq_inter ω_ne_one hωc (hf_ne s) ha_ne (hD_fa hn4)).1
    (lineEq_inter ω_ne_one hωc (hf_ne s) ha_ne (hD_fa hn4)).2
/-- The main step: for any admissible parameter `s` and any points `P Q R` on the
respective lines (with `P Q R` not collinear), the four points `P Q R m` are
concyclic. -/
lemma concyclic_of (cfg : Cfg) (s : ℝ) (P Q R : ℂ)
    (hPAC : Collinear ℝ ({cfg.A, P, cfg.C} : Set ℂ))
    (hPBD : Collinear ℝ ({cfg.B, P, cfg.D} : Set ℂ))
    (hQBD : Collinear ℝ ({cfg.B, Q, cfg.D} : Set ℂ))
    (hQEF : Collinear ℝ ({cfg.ptE s, Q, cfg.ptF s} : Set ℂ))
    (hREF : Collinear ℝ ({cfg.ptE s, R, cfg.ptF s} : Set ℂ))
    (hRAC : Collinear ℝ ({cfg.A, R, cfg.C} : Set ℂ))
    (hn3 : ¬ Collinear ℝ ({0, cfg.ptF s - cfg.ptE s, cfg.D - cfg.B} : Set ℂ))
    (hn4 : ¬ Collinear ℝ ({0, cfg.ptF s - cfg.ptE s, cfg.C - cfg.A} : Set ℂ))
    (hPQR : ¬ Collinear ℝ ({P, Q, R} : Set ℂ)) :
    Concyclic ({P, Q, R, cfg.m} : Set ℂ) := by
  have hpP := P_sub_m cfg hPAC hPBD
  have hqQ := Q_sub_m cfg hQBD hQEF hn3
  have hrR := R_sub_m cfg hREF hRAC hn4
  simp only [interPt] at hpP hqQ hrR
  have hω1 : 1 + cfg.ω ≠ 0 := by
    intro h
    apply ω_ne_neg_one
    linear_combination h
  -- nonvanishing of the translated intersection points
  have hpne : P - cfg.m ≠ 0 := by
    rw [hpP]
    exact div_ne_zero (mul_ne_zero hω1 (mul_ne_zero (mul_ne_zero ha_ne hd_ne)
      (conj_sub_ne_zero hD_ad))) hD_ad
  have hqne : Q - cfg.m ≠ 0 := by
    rw [hqQ]
    exact div_ne_zero (mul_ne_zero hω1 (mul_ne_zero (mul_ne_zero hd_ne (hf_ne s))
      (conj_sub_ne_zero (hD_df hn3)))) (hD_df hn3)
  have hrne : R - cfg.m ≠ 0 := by
    rw [hrR]
    exact div_ne_zero (mul_ne_zero hω1 (mul_ne_zero (mul_ne_zero (hf_ne s) ha_ne)
      (conj_sub_ne_zero (hD_fa hn4)))) (hD_fa hn4)
  -- the key identity, transported to `P Q R`
  have hkey : conj ((1 + cfg.ω) * ((cfg.D - cfg.m) * ((cfg.D - cfg.m) +
          (s : ℂ) * ((cfg.A - cfg.m) - (cfg.D - cfg.m))) * (conj (cfg.D - cfg.m) -
          conj ((cfg.D - cfg.m) + (s : ℂ) * ((cfg.A - cfg.m) - (cfg.D - cfg.m))))) /
        (conj (cfg.D - cfg.m) * ((cfg.D - cfg.m) + (s : ℂ) * ((cfg.A - cfg.m) - (cfg.D - cfg.m))) -
          conj ((cfg.D - cfg.m) + (s : ℂ) * ((cfg.A - cfg.m) - (cfg.D - cfg.m))) * (cfg.D - cfg.m)) -
      (1 + cfg.ω) * ((cfg.A - cfg.m) * (cfg.D - cfg.m) * (conj (cfg.A - cfg.m) - conj (cfg.D - cfg.m))) /
        (conj (cfg.A - cfg.m) * (cfg.D - cfg.m) - conj (cfg.D - cfg.m) * (cfg.A - cfg.m))) *
    ((1 + cfg.ω) * (((cfg.D - cfg.m) + (s : ℂ) * ((cfg.A - cfg.m) - (cfg.D - cfg.m))) * (cfg.A - cfg.m) *
          (conj ((cfg.D - cfg.m) + (s : ℂ) * ((cfg.A - cfg.m) - (cfg.D - cfg.m))) - conj (cfg.A - cfg.m))) /
        (conj ((cfg.D - cfg.m) + (s : ℂ) * ((cfg.A - cfg.m) - (cfg.D - cfg.m))) * (cfg.A - cfg.m) -
          conj (cfg.A - cfg.m) * ((cfg.D - cfg.m) + (s : ℂ) * ((cfg.A - cfg.m) - (cfg.D - cfg.m)))) -
      (1 + cfg.ω) * ((cfg.A - cfg.m) * (cfg.D - cfg.m) * (conj (cfg.A - cfg.m) - conj (cfg.D - cfg.m))) /
        (conj (cfg.A - cfg.m) * (cfg.D - cfg.m) - conj (cfg.D - cfg.m) * (cfg.A - cfg.m))) *
    ((1 + cfg.ω) * ((cfg.D - cfg.m) * ((cfg.D - cfg.m) + (s : ℂ) * ((cfg.A - cfg.m) - (cfg.D - cfg.m))) *
          (conj (cfg.D - cfg.m) - conj ((cfg.D - cfg.m) + (s : ℂ) * ((cfg.A - cfg.m) - (cfg.D - cfg.m))))) /
        (conj (cfg.D - cfg.m) * ((cfg.D - cfg.m) + (s : ℂ) * ((cfg.A - cfg.m) - (cfg.D - cfg.m))) -
          conj ((cfg.D - cfg.m) + (s : ℂ) * ((cfg.A - cfg.m) - (cfg.D - cfg.m))) * (cfg.D - cfg.m))) *
    conj ((1 + cfg.ω) * (((cfg.D - cfg.m) + (s : ℂ) * ((cfg.A - cfg.m) - (cfg.D - cfg.m))) * (cfg.A - cfg.m) *
          (conj ((cfg.D - cfg.m) + (s : ℂ) * ((cfg.A - cfg.m) - (cfg.D - cfg.m))) - conj (cfg.A - cfg.m))) /
        (conj ((cfg.D - cfg.m) + (s : ℂ) * ((cfg.A - cfg.m) - (cfg.D - cfg.m))) * (cfg.A - cfg.m) -
          conj (cfg.A - cfg.m) * ((cfg.D - cfg.m) + (s : ℂ) * ((cfg.A - cfg.m) - (cfg.D - cfg.m))))) =
    ((1 + cfg.ω) * ((cfg.D - cfg.m) * ((cfg.D - cfg.m) + (s : ℂ) * ((cfg.A - cfg.m) - (cfg.D - cfg.m))) *
          (conj (cfg.D - cfg.m) - conj ((cfg.D - cfg.m) + (s : ℂ) * ((cfg.A - cfg.m) - (cfg.D - cfg.m))))) /
        (conj (cfg.D - cfg.m) * ((cfg.D - cfg.m) + (s : ℂ) * ((cfg.A - cfg.m) - (cfg.D - cfg.m))) -
          conj ((cfg.D - cfg.m) + (s : ℂ) * ((cfg.A - cfg.m) - (cfg.D - cfg.m))) * (cfg.D - cfg.m)) -
      (1 + cfg.ω) * ((cfg.A - cfg.m) * (cfg.D - cfg.m) * (conj (cfg.A - cfg.m) - conj (cfg.D - cfg.m))) /
        (conj (cfg.A - cfg.m) * (cfg.D - cfg.m) - conj (cfg.D - cfg.m) * (cfg.A - cfg.m))) *
    conj ((1 + cfg.ω) * (((cfg.D - cfg.m) + (s : ℂ) * ((cfg.A - cfg.m) - (cfg.D - cfg.m))) * (cfg.A - cfg.m) *
          (conj ((cfg.D - cfg.m) + (s : ℂ) * ((cfg.A - cfg.m) - (cfg.D - cfg.m))) - conj (cfg.A - cfg.m))) /
        (conj ((cfg.D - cfg.m) + (s : ℂ) * ((cfg.A - cfg.m) - (cfg.D - cfg.m))) * (cfg.A - cfg.m) -
          conj (cfg.A - cfg.m) * ((cfg.D - cfg.m) + (s : ℂ) * ((cfg.A - cfg.m) - (cfg.D - cfg.m)))) -
      (1 + cfg.ω) * ((cfg.A - cfg.m) * (cfg.D - cfg.m) * (conj (cfg.A - cfg.m) - conj (cfg.D - cfg.m))) /
        (conj (cfg.A - cfg.m) * (cfg.D - cfg.m) - conj (cfg.D - cfg.m) * (cfg.A - cfg.m))) *
    conj ((1 + cfg.ω) * ((cfg.D - cfg.m) * ((cfg.D - cfg.m) + (s : ℂ) * ((cfg.A - cfg.m) - (cfg.D - cfg.m))) *
          (conj (cfg.D - cfg.m) - conj ((cfg.D - cfg.m) + (s : ℂ) * ((cfg.A - cfg.m) - (cfg.D - cfg.m))))) /
        (conj (cfg.D - cfg.m) * ((cfg.D - cfg.m) + (s : ℂ) * ((cfg.A - cfg.m) - (cfg.D - cfg.m))) -
          conj ((cfg.D - cfg.m) + (s : ℂ) * ((cfg.A - cfg.m) - (cfg.D - cfg.m))) * (cfg.D - cfg.m))) *
    ((1 + cfg.ω) * (((cfg.D - cfg.m) + (s : ℂ) * ((cfg.A - cfg.m) - (cfg.D - cfg.m))) * (cfg.A - cfg.m) *
          (conj ((cfg.D - cfg.m) + (s : ℂ) * ((cfg.A - cfg.m) - (cfg.D - cfg.m))) - conj (cfg.A - cfg.m))) /
        (conj ((cfg.D - cfg.m) + (s : ℂ) * ((cfg.A - cfg.m) - (cfg.D - cfg.m))) * (cfg.A - cfg.m) -
          conj (cfg.A - cfg.m) * ((cfg.D - cfg.m) + (s : ℂ) * ((cfg.A - cfg.m) - (cfg.D - cfg.m))))) :=
    key_identity (1 + cfg.ω) s (cfg.A - cfg.m) (cfg.D - cfg.m) hD_ad
      (by rw [← hf_sub]; exact hD_df hn3) (by rw [← hf_sub]; exact hD_fa hn4)
  rw [← hf_sub] at hkey
  rw [← hpP, ← hqQ, ← hrR] at hkey
  have eQP : (Q - cfg.m) - (P - cfg.m) = Q - P := by ring
  have eRP : (R - cfg.m) - (P - cfg.m) = R - P := by ring
  rw [eQP, eRP] at hkey
  -- the ratio of the two "angle" complex numbers is real
  have hw2 : conj (Q - cfg.m) * (R - cfg.m) ≠ 0 :=
    mul_ne_zero (conj_ne_zero hqne) hrne
  have hz : conj (conj (Q - P) * (R - P) / (conj (Q - cfg.m) * (R - cfg.m))) =
      conj (Q - P) * (R - P) / (conj (Q - cfg.m) * (R - cfg.m)) := by
    rw [map_div₀]
    have hw2c : conj (conj (Q - cfg.m) * (R - cfg.m)) ≠ 0 := conj_ne_zero hw2
    rw [div_eq_div_iff hw2c hw2]
    simp only [map_mul, starRingEnd_self_apply]
    linear_combination -hkey
  obtain ⟨t, ht⟩ := conj_eq_iff_real.mp hz
  have htne : t ≠ 0 := by
    intro h0
    rw [h0, Complex.ofReal_zero] at ht
    have hw1 : conj (Q - P) * (R - P) = 0 := by
      have h := (div_eq_zero_iff).mp ht
      rcases h with h | h
      · exact h
      · exact absurd h hw2
    rcases mul_eq_zero.mp hw1 with hQP | hRP
    · apply hPQR
      have hQPeq : Q = P := sub_eq_zero.mp (conj_eq_zero hQP)
      rw [hQPeq]
      have hset : ({P, P, R} : Set ℂ) = {P, R} := by
        ext x
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      rw [hset]
      exact collinear_pair ℝ P R
    · apply hPQR
      have hRPeq : R = P := sub_eq_zero.mp hRP
      rw [hRPeq]
      have hset : ({P, Q, P} : Set ℂ) = {P, Q} := by
        ext x
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      rw [hset]
      exact collinear_pair ℝ P Q
  have ht2 : conj (Q - P) * (R - P) = (t : ℂ) * (conj (Q - cfg.m) * (R - cfg.m)) := by
    rw [← ht, div_mul_cancel₀ _ hw2]
  have hangle : (2 : ℤ) • ∡ Q P R = (2 : ℤ) • ∡ Q cfg.m R := by
    have e1 : ∡ Q P R = Complex.arg (conj (Q - P) * (R - P)) := by
      show Complex.orientation.oangle (Q -ᵥ P) (R -ᵥ P) = _
      rw [vsub_eq_sub, vsub_eq_sub, Complex.oangle]
    have e2 : ∡ Q cfg.m R = Complex.arg (conj (Q - cfg.m) * (R - cfg.m)) := by
      show Complex.orientation.oangle (Q -ᵥ cfg.m) (R -ᵥ cfg.m) = _
      rw [vsub_eq_sub, vsub_eq_sub, Complex.oangle]
    rw [e1, e2, ht2]
    exact two_zsmul_arg_of_real_mul hw2 htne
  have hc := cospherical_or_collinear_of_two_zsmul_oangle_eq (p₁ := Q) (p₂ := P)
    (p₃ := cfg.m) (p₄ := R) hangle
  rcases hc with hcsp | hcoll
  · refine ⟨?_, coplanar_of_fact_finrank_eq_two _⟩
    have hset : ({P, Q, R, cfg.m} : Set ℂ) = {Q, P, cfg.m, R} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [hset]
    exact hcsp
  · exfalso
    apply hPQR
    apply hcoll.subset
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto

/-- The point `m` is not the intersection point of the diagonals (else `ABCD` would be
a parallelogram, contradicting `BC ∦ DA`). -/
lemma m_ne_of_mem_diagonals (cfg : Cfg) {P : ℂ}
    (hPAC : Collinear ℝ ({cfg.A, P, cfg.C} : Set ℂ))
    (hPBD : Collinear ℝ ({cfg.B, P, cfg.D} : Set ℂ)) : cfg.m ≠ P := by
  intro h
  have hpP := P_sub_m cfg hPAC hPBD
  simp only [interPt] at hpP
  have h0 : P - cfg.m = 0 := sub_eq_zero.mpr h.symm
  rw [hpP] at h0
  have hω1 : 1 + cfg.ω ≠ 0 := by
    intro h1
    apply ω_ne_neg_one
    linear_combination h1
  have hnum : (1 + cfg.ω) * ((cfg.A - cfg.m) * (cfg.D - cfg.m) *
      (conj (cfg.A - cfg.m) - conj (cfg.D - cfg.m))) = 0 := by
    rw [div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · exact h0
    · exact absurd h0 hD_ad
  have hconj : conj (cfg.A - cfg.m) - conj (cfg.D - cfg.m) = 0 := by
    rcases mul_eq_zero.mp hnum with h1 | h2
    · exact absurd h1 hω1
    · rcases mul_eq_zero.mp h2 with h3 | h4
      · rcases mul_eq_zero.mp h3 with h5 | h6
        · exact absurd h5 ha_ne
        · exact absurd h6 hd_ne
      · exact h4
  apply hD_ad
  · have had : cfg.A - cfg.m = cfg.D - cfg.m := by
      have h1 := congrArg conj (sub_eq_zero.mp hconj)
      rw [starRingEnd_self_apply, starRingEnd_self_apply] at h1
      exact h1
    rw [had]
    simp

end Cfg

snip end

problem imo2005_p5
    (A B C D : ℂ)
    (hAC : A ≠ C) (hBD : B ≠ D) (hAD : A ≠ D) (hBC : B ≠ C)
    (hlen : dist B C = dist D A)
    (hpar : ¬ Collinear ℝ ({0, A - D, B - C} : Set ℂ))
    (hdiag : ¬ Collinear ℝ ({0, C - A, D - B} : Set ℂ)) :
    ∃ M : ℂ,
      (∀ P : ℂ, Collinear ℝ ({A, P, C} : Set ℂ) → Collinear ℝ ({B, P, D} : Set ℂ) →
        M ≠ P) ∧
      ∀ E F : ℂ, E ∈ segment ℝ B C → F ∈ segment ℝ D A → dist B E = dist D F →
        ¬ Collinear ℝ ({0, F - E, D - B} : Set ℂ) →
        ¬ Collinear ℝ ({0, F - E, C - A} : Set ℂ) →
        ∀ P Q R : ℂ,
          Collinear ℝ ({A, P, C} : Set ℂ) → Collinear ℝ ({B, P, D} : Set ℂ) →
          Collinear ℝ ({B, Q, D} : Set ℂ) → Collinear ℝ ({E, Q, F} : Set ℂ) →
          Collinear ℝ ({E, R, F} : Set ℂ) → Collinear ℝ ({A, R, C} : Set ℂ) →
          ¬ Collinear ℝ ({P, Q, R} : Set ℂ) →
          Concyclic ({P, Q, R, M} : Set ℂ) := by
  set cfg : Cfg := ⟨A, B, C, D, hAC, hBD, hAD, hBC, hlen, hpar, hdiag⟩
  refine ⟨cfg.m, ?_, ?_⟩
  · intro P hPAC hPBD
    exact cfg.m_ne_of_mem_diagonals hPAC hPBD
  · intro E F hE hF hdist hn3 hn4 P Q R hPAC hPBD hQBD hQEF hREF hRAC hPQR
    rw [segment_eq_image_lineMap] at hE hF
    obtain ⟨sE, hsE, hEl⟩ := hE
    obtain ⟨sF, hsF, hFl⟩ := hF
    have hdE : dist B E = sE * dist B C := by
      rw [← hEl, dist_comm, dist_lineMap_left, Real.norm_of_nonneg hsE.1]
    have hdF : dist D F = sF * dist D A := by
      rw [← hFl, dist_comm, dist_lineMap_left, Real.norm_of_nonneg hsF.1]
    have hsEF : sE = sF := by
      have hBCne : dist B C ≠ 0 := ne_of_gt (dist_pos.mpr hBC)
      have e : sE * dist B C = sF * dist B C := by
        rw [← hdE, hdist, hdF, ← hlen]
      exact mul_right_cancel₀ hBCne e
    have hE' : E = cfg.ptE sE := by
      rw [← hEl]
      show AffineMap.lineMap B C sE = B + (sE : ℂ) * (C - B)
      rw [AffineMap.lineMap_apply]
      simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul]
      ring
    have hF' : F = cfg.ptF sE := by
      rw [← hFl, hsEF]
      show AffineMap.lineMap D A sF = D + (sF : ℂ) * (A - D)
      rw [AffineMap.lineMap_apply]
      simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul]
      ring
    rw [hE', hF'] at hQEF hREF hn3 hn4
    exact cfg.concyclic_of sE P Q R hPAC hPBD hQBD hQEF hREF hRAC hn3 hn4 hPQR

end Imo2005P5
