/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Data.List.GetD
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry, .Inequality] }

/-!
# International Mathematical Olympiad 2002, Problem 6

Let n ≥ 3 be a positive integer. Let C₁, C₂, ..., Cₙ be unit circles in the
plane, with centres O₁, O₂, ..., Oₙ. If no line meets more than two of the
circles, prove that

  ∑_{1 ≤ i < j ≤ n} 1/OᵢOⱼ ≤ (n - 1)π/4.
-/

namespace Imo2002P6

open Finset
open ComplexConjugate

/-- The hypothesis that no line meets more than two of the unit circles centred
at the points `O i` of the plane (identified with `ℂ`).  A line is parametrised
by a unit normal `u : ℂ` and an offset `c : ℝ` as `{z | (conj u * z).re = c}`;
it meets the unit circle centred at `O i` iff its distance to `O i` is at most
`1`, i.e. `|(conj u * O i).re - c| ≤ 1`. -/
def NoLineMeetsThree {n : ℕ} (O : Fin n → ℂ) : Prop :=
  ∀ u : ℂ, ‖u‖ = 1 → ∀ c : ℝ,
    ((univ : Finset (Fin n)).filter fun i => |(conj u * O i).re - c| ≤ 1).card ≤ 2

/-- `k` is a *vertex* of the configuration: all other centres lie in some open
half-plane through `k`.  These are exactly the vertices of the convex hull of
the centres. -/
def IsVertex {n : ℕ} (O : Fin n → ℂ) (k : Fin n) : Prop :=
  ∃ u : ℂ, u ≠ 0 ∧ ∀ j, j ≠ k → 0 < (conj u * (O j - O k)).re

/-- The (unoriented) angle between two complex numbers, in `[0, π]`. -/
noncomputable def uangle (x y : ℂ) : ℝ := |Complex.arg (x / y)|

/-- The angular spread of the other centres as seen from centre `k`:
the supremum of the angles between pairs of rays from `k`. -/
noncomputable def spread {n : ℕ} (O : Fin n → ℂ) (k : Fin n) : ℝ :=
  sSup (Set.range fun p : Fin n × Fin n => uangle (O p.1 - O k) (O p.2 - O k))

snip begin

variable {n : ℕ} {O : Fin n → ℂ}

lemma exists_ne_ne (hn : 3 ≤ n) (i j : Fin n) : ∃ k : Fin n, k ≠ i ∧ k ≠ j := by
  have h : 0 < (((univ : Finset (Fin n)).erase i).erase j).card := by
    by_cases hji : j = i
    · subst hji
      rw [Finset.erase_idem, Finset.card_erase_of_mem (mem_univ _), Finset.card_univ,
        Fintype.card_fin]
      omega
    · rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hji, mem_univ _⟩),
        Finset.card_erase_of_mem (mem_univ _), Finset.card_univ, Fintype.card_fin]
      omega
  obtain ⟨k, hk⟩ := Finset.card_pos.mp h
  rw [Finset.mem_erase, Finset.mem_erase] at hk
  exact ⟨k, hk.2.1, hk.1⟩

/-- Three distinct centres cannot all satisfy the same line inequality. -/
lemma not_three_mem (hlines : NoLineMeetsThree O) (u : ℂ) (hu : ‖u‖ = 1) (c : ℝ)
    {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : |(conj u * O i).re - c| ≤ 1) (hj : |(conj u * O j).re - c| ≤ 1)
    (hk : |(conj u * O k).re - c| ≤ 1) : False := by
  have h := hlines u hu c
  have hsub : ({i, j, k} : Finset (Fin n)) ⊆
      (univ : Finset (Fin n)).filter (fun l => |(conj u * O l).re - c| ≤ 1) := by
    intro x hx
    rw [mem_insert, mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact mem_filter.mpr ⟨mem_univ _, hi⟩
    · exact mem_filter.mpr ⟨mem_univ _, hj⟩
    · exact mem_filter.mpr ⟨mem_univ _, hk⟩
  have h3 : 3 ≤ ((univ : Finset (Fin n)).filter (fun l => |(conj u * O l).re - c| ≤ 1)).card :=
    calc 3 = ({i, j, k} : Finset (Fin n)).card := by
          rw [Finset.card_insert_of_notMem (by simp [hij, hik]),
            Finset.card_insert_of_notMem (by simp [hjk]), Finset.card_singleton]
      _ ≤ _ := card_le_card hsub
  omega

/-- The centres are at distance greater than `2` apart (the circles are disjoint). -/
lemma two_lt_dist (hn : 3 ≤ n) (hlines : NoLineMeetsThree O) {i j : Fin n} (hij : i ≠ j) :
    2 < ‖O i - O j‖ := by
  by_contra hle
  push Not at hle
  obtain ⟨k, hki, hkj⟩ := exists_ne_ne hn i j
  set m := (O i + O j) / 2 with hm
  have hmi : ‖O i - m‖ ≤ 1 := by
    have h1 : O i - m = (O i - O j) / 2 := by rw [hm]; ring
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h1, norm_div, h2]
    linarith
  have hmj : ‖O j - m‖ ≤ 1 := by
    have h1 : O j - m = (O j - O i) / 2 := by rw [hm]; ring
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h1, norm_div, h2, norm_sub_rev]
    linarith
  by_cases hkm : O k = m
  · -- any line through `m = O k` works; take the one with normal `1`
    refine not_three_mem hlines 1 (by simp) (O k).re hki hkj hij ?_ ?_ ?_
    · simp
    · calc |(conj 1 * O i).re - (O k).re| = |(O i - O k).re| := by simp
        _ ≤ ‖O i - O k‖ := Complex.abs_re_le_norm _
        _ ≤ 1 := by rw [hkm]; exact hmi
    · calc |(conj 1 * O j).re - (O k).re| = |(O j - O k).re| := by simp
        _ ≤ ‖O j - O k‖ := Complex.abs_re_le_norm _
        _ ≤ 1 := by rw [hkm]; exact hmj
  · -- use the line through `m` perpendicular to `O k - m`
    set w := O k - m with hw
    have hw0 : w ≠ 0 := sub_ne_zero.mpr hkm
    set u := Complex.I * w / ‖w‖ with hu
    have hu1 : ‖u‖ = 1 := by
      rw [hu, norm_div, norm_mul, Complex.norm_I, one_mul]
      have hnrm : ‖(↑‖w‖ : ℂ)‖ = ‖w‖ := by
        rw [Complex.norm_real]
        exact abs_of_nonneg (norm_nonneg _)
      rw [hnrm]
      exact div_self (norm_ne_zero_iff.mpr hw0)
    have hd : ∀ z : ℂ, (conj u * z).re - (conj u * m).re = (conj u * (z - m)).re := by
      intro z
      rw [← Complex.sub_re, ← mul_sub]
    have hck : (conj u * w).re = 0 := by
      have e1 : conj u * w = -Complex.I * (conj w * w) / ‖w‖ := by
        rw [hu, map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal]
        ring
      have hw' : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hw0
      have hcw : conj w * w = (‖w‖ : ℂ) ^ 2 := by
        rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
      have e2 : conj u * w = -Complex.I * ‖w‖ := by
        rw [e1, hcw, div_eq_iff hw', pow_two, mul_assoc]
      rw [e2]
      simp
    refine not_three_mem hlines u hu1 (conj u * m).re hki hkj hij ?_ ?_ ?_
    · rw [hd, hck]
      norm_num
    · rw [hd]
      calc |(conj u * (O i - m)).re| ≤ ‖conj u * (O i - m)‖ := Complex.abs_re_le_norm _
        _ = ‖O i - m‖ := by rw [norm_mul, Complex.norm_conj, hu1, one_mul]
        _ ≤ 1 := hmi
    · rw [hd]
      calc |(conj u * (O j - m)).re| ≤ ‖conj u * (O j - m)‖ := Complex.abs_re_le_norm _
        _ = ‖O j - m‖ := by rw [norm_mul, Complex.norm_conj, hu1, one_mul]
        _ ≤ 1 := hmj

/-- `|sin|` has period `π`. -/
lemma abs_sin_sub_zsmul_pi (x : ℝ) (m : ℤ) : |Real.sin (x - m • Real.pi)| = |Real.sin x| := by
  rw [zsmul_eq_mul, Real.sin_sub, Real.cos_int_mul_pi, Real.sin_int_mul_pi]
  simp

/-- The signed distance of a point `z` from the line through the origin and `w`,
measured with the unit normal `I * w / ‖w‖`. -/
lemma sdist_formula (w z : ℂ) (hw : w ≠ 0) :
    (conj (Complex.I * w / ‖w‖) * z).re = ‖z‖ * Real.sin (Complex.arg z - Complex.arg w) := by
  have hw' : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hw
  have e1 : conj (Complex.I * w / ‖w‖) * z = (-Complex.I) * (conj w * z) / ‖w‖ := by
    rw [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have e2 : conj w = ‖w‖ * Complex.exp (-(Complex.arg w * Complex.I)) := by
    have h1 : conj w = conj (‖w‖ * Complex.exp (Complex.arg w * Complex.I)) := by
      rw [Complex.norm_mul_exp_arg_mul_I]
    rw [h1, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
      Complex.conj_I]
    ring
  have e3 : (-Complex.I) * (conj w * z) / ‖w‖
      = (-Complex.I) * Complex.exp (-(Complex.arg w * Complex.I)) * z * (↑‖w‖ / ↑‖w‖) := by
    rw [e2]
    ring
  have e4 : (-Complex.I) * Complex.exp (-(Complex.arg w * Complex.I)) *
        (↑‖z‖ * Complex.exp (Complex.arg z * Complex.I))
      = ↑‖z‖ * ((-Complex.I) * Complex.exp ((Complex.arg z - Complex.arg w) * Complex.I)) := by
    rw [show (Complex.arg z - Complex.arg w) * Complex.I
        = Complex.arg z * Complex.I + (-(Complex.arg w * Complex.I)) by ring]
    rw [Complex.exp_add]
    ring
  have e5 : ((-Complex.I) * Complex.exp ((Complex.arg z - Complex.arg w) * Complex.I)).re
      = Real.sin (Complex.arg z - Complex.arg w) := by
    rw [Complex.exp_mul_I]
    simp only [← Complex.ofReal_sub, Complex.cos_ofReal_re, Complex.cos_ofReal_im,
      Complex.sin_ofReal_re, Complex.sin_ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
    ring
  calc (conj (Complex.I * w / ‖w‖) * z).re
      = ((-Complex.I) * Complex.exp (-(Complex.arg w * Complex.I)) * z).re := by
        rw [e1, e3, div_self hw', mul_one]
    _ = ((-Complex.I) * Complex.exp (-(Complex.arg w * Complex.I)) *
          (↑‖z‖ * Complex.exp (Complex.arg z * Complex.I))).re := by
        rw [Complex.norm_mul_exp_arg_mul_I]
    _ = (↑‖z‖ * ((-Complex.I) * Complex.exp ((Complex.arg z - Complex.arg w) * Complex.I))).re := by
        rw [e4]
    _ = ‖z‖ * ((-Complex.I) * Complex.exp ((Complex.arg z - Complex.arg w) * Complex.I)).re := by
        simp
    _ = ‖z‖ * Real.sin (Complex.arg z - Complex.arg w) := by rw [e5]

/-- The signed distance of a point `z` from the line through the origin with
direction angle `ψ`, measured with the unit normal `I * exp (ψ * I)`. -/
lemma sdist_exp_normal (ψ : ℝ) (z : ℂ) :
    (conj (Complex.I * Complex.exp (ψ * Complex.I)) * z).re =
      ‖z‖ * Real.sin (Complex.arg z - ψ) := by
  have e1 : conj (Complex.I * Complex.exp (ψ * Complex.I)) * z
      = (-Complex.I) * Complex.exp (-(ψ * Complex.I)) * z := by
    rw [map_mul, Complex.conj_I, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have e2 : (-Complex.I) * Complex.exp (-(ψ * Complex.I)) *
        (↑‖z‖ * Complex.exp (Complex.arg z * Complex.I))
      = ↑‖z‖ * ((-Complex.I) * Complex.exp ((Complex.arg z - ψ) * Complex.I)) := by
    rw [show (Complex.arg z - ψ) * Complex.I = Complex.arg z * Complex.I + (-(ψ * Complex.I)) by
      ring]
    rw [Complex.exp_add]
    ring
  have e5 : ((-Complex.I) * Complex.exp ((Complex.arg z - ψ) * Complex.I)).re
      = Real.sin (Complex.arg z - ψ) := by
    rw [Complex.exp_mul_I]
    simp only [← Complex.ofReal_sub, Complex.cos_ofReal_re, Complex.cos_ofReal_im,
      Complex.sin_ofReal_re, Complex.sin_ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
    ring
  calc (conj (Complex.I * Complex.exp (ψ * Complex.I)) * z).re
      = ((-Complex.I) * Complex.exp (-(ψ * Complex.I)) * z).re := by rw [e1]
    _ = ((-Complex.I) * Complex.exp (-(ψ * Complex.I)) *
          (↑‖z‖ * Complex.exp (Complex.arg z * Complex.I))).re := by
        rw [Complex.norm_mul_exp_arg_mul_I]
    _ = (↑‖z‖ * ((-Complex.I) * Complex.exp ((Complex.arg z - ψ) * Complex.I))).re := by rw [e2]
    _ = ‖z‖ * ((-Complex.I) * Complex.exp ((Complex.arg z - ψ) * Complex.I)).re := by simp
    _ = ‖z‖ * Real.sin (Complex.arg z - ψ) := by rw [e5]

/-- The `mod π` arguments of the directions from one centre to two distinct other
centres are different (otherwise the line through the three centres would meet
three circles). -/
lemma arg_toIocMod_ne (hn : 3 ≤ n) (hlines : NoLineMeetsThree O) {k i j : Fin n}
    (hki : k ≠ i) (hkj : k ≠ j) (hij : i ≠ j) :
    toIocMod Real.pi_pos 0 (Complex.arg (O i - O k)) ≠
      toIocMod Real.pi_pos 0 (Complex.arg (O j - O k)) := by
  intro hγ
  have hi0 : O i - O k ≠ 0 := by
    have h2 := two_lt_dist hn hlines hki
    rw [norm_sub_rev] at h2
    by_contra h
    rw [h, norm_zero] at h2
    linarith
  have hj0 : O j - O k ≠ 0 := by
    have h2 := two_lt_dist hn hlines hkj
    rw [norm_sub_rev] at h2
    by_contra h
    rw [h, norm_zero] at h2
    linarith
  have e1 := toIocMod_add_toIocDiv_zsmul Real.pi_pos 0 (Complex.arg (O i - O k))
  have e2 := toIocMod_add_toIocDiv_zsmul Real.pi_pos 0 (Complex.arg (O j - O k))
  rw [hγ] at e1
  set g := toIocMod Real.pi_pos 0 (Complex.arg (O j - O k)) with hg
  set z1 := toIocDiv Real.pi_pos 0 (Complex.arg (O i - O k)) with hz1
  set z2 := toIocDiv Real.pi_pos 0 (Complex.arg (O j - O k)) with hz2
  have hdiff : Complex.arg (O j - O k) = Complex.arg (O i - O k) + (z2 - z1) • Real.pi := by
    rw [← e1, ← e2, sub_zsmul]
    ring
  set u := Complex.I * (O i - O k) / ‖O i - O k‖ with hu
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_div, norm_mul, Complex.norm_I, one_mul]
    have hnrm : ‖(↑‖O i - O k‖ : ℂ)‖ = ‖O i - O k‖ := by
      rw [Complex.norm_real]
      exact abs_of_nonneg (norm_nonneg _)
    rw [hnrm]
    exact div_self (norm_ne_zero_iff.mpr hi0)
  have hck : (conj u * (O i - O k)).re = 0 := by
    rw [sdist_formula _ _ hi0]
    simp
  have hckj : (conj u * (O j - O k)).re = 0 := by
    rw [sdist_formula _ _ hi0, hdiff,
      show Complex.arg (O i - O k) + (z2 - z1) • Real.pi - Complex.arg (O i - O k)
        = (z2 - z1) • Real.pi by ring,
      zsmul_eq_mul, Real.sin_int_mul_pi, mul_zero]
  have hd : ∀ zz : ℂ, (conj u * zz).re - (conj u * O k).re = (conj u * (zz - O k)).re := by
    intro zz
    rw [← Complex.sub_re, ← mul_sub]
  exact not_three_mem hlines u hu1 (conj u * O k).re hki hkj hij
    (by simp) (by rw [hd, hck]; norm_num) (by rw [hd, hckj]; norm_num)

/-- Tangent constraint: if a line with unit normal `u` touches the unit circles at
`O k` and at `O i` (i.e. `re (conj u * (O i - O k)) = 2`, so the line is the common
internal tangent of the two circles), then the circle at `O j` misses it. -/
lemma tangent_constr (hlines : NoLineMeetsThree O) {k i j : Fin n}
    (hki : k ≠ i) (hkj : k ≠ j) (hij : i ≠ j)
    (u : ℂ) (hu : ‖u‖ = 1) (hu2 : (conj u * (O i - O k)).re = 2) :
    (conj u * (O j - O k)).re < 0 ∨ 2 < (conj u * (O j - O k)).re := by
  have hd : ∀ zz : ℂ, (conj u * zz).re - ((conj u * O k).re + 1)
      = (conj u * (zz - O k)).re - 1 := by
    intro zz
    have e : (conj u * zz).re - (conj u * O k).re = (conj u * (zz - O k)).re := by
      rw [← Complex.sub_re, ← mul_sub]
    linarith [e]
  have hmem_k : |(conj u * O k).re - ((conj u * O k).re + 1)| ≤ 1 := by
    rw [hd]
    simp
  have hmem_i : |(conj u * O i).re - ((conj u * O k).re + 1)| ≤ 1 := by
    rw [hd, hu2]
    norm_num
  have hmem_j : ¬|(conj u * O j).re - ((conj u * O k).re + 1)| ≤ 1 := by
    intro hj
    exact not_three_mem hlines u hu ((conj u * O k).re + 1) hki hkj hij hmem_k hmem_i hj
  have h1 : 1 < |(conj u * O j).re - ((conj u * O k).re + 1)| := lt_of_not_ge hmem_j
  rw [hd] at h1
  rw [lt_abs] at h1
  rcases h1 with h1 | h1
  · right
    linarith
  · left
    linarith

/-- The unit normal to a common internal tangent of the unit circles centred at `0`
and at `a` (for `2 < ‖a‖`).  The parameter `s = ±1` selects one of the two tangents:
the line with unit normal `u` at offset `1` touches both circles, and the signed
distance of any point `z` from it is given by the formula below. -/
lemma tangent_normal (a : ℂ) (ha : 2 < ‖a‖) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ (conj u * a).re = 2 ∧
      ∀ z : ℂ, (conj u * z).re =
        2 * (z / a).re - s * Real.sqrt (‖a‖ ^ 2 - 4) * (z / a).im := by
  have hA0 : 0 < ‖a‖ := by linarith [norm_nonneg a]
  have hA0' : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast hA0.ne'
  have ha0 : a ≠ 0 := norm_ne_zero_iff.mp hA0.ne'
  have hΔ : 0 ≤ ‖a‖ ^ 2 - 4 := by nlinarith [ha]
  have hA2' : (↑(‖a‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_ne_zero 2 hA0.ne')
  refine ⟨(a / ‖a‖ ^ 2) * (2 - s * Complex.I * Real.sqrt (‖a‖ ^ 2 - 4)), ?_, ?_, ?_⟩
  · -- the normal is a unit vector
    have e1 : ‖(2 : ℂ) - s * Complex.I * Real.sqrt (‖a‖ ^ 2 - 4)‖ = ‖a‖ := by
      have h1 : ‖(2 : ℂ) - s * Complex.I * Real.sqrt (‖a‖ ^ 2 - 4)‖ ^ 2 = ‖a‖ ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq]
        have e : (2 : ℂ) - s * Complex.I * Real.sqrt (‖a‖ ^ 2 - 4)
            = ((2 : ℝ) : ℂ) + ((-s * Real.sqrt (‖a‖ ^ 2 - 4) : ℝ) : ℂ) * Complex.I := by
          push_cast
          ring
        rw [e, Complex.normSq_add_mul_I]
        have hs2 : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
        have h4 : (-s * Real.sqrt (‖a‖ ^ 2 - 4)) ^ 2 = ‖a‖ ^ 2 - 4 := by
          rw [mul_pow, Real.sq_sqrt hΔ, show (-s) ^ 2 = s ^ 2 by ring, hs2, one_mul]
        rw [h4]
        ring
      have h2 := congr_arg Real.sqrt h1
      rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hA0.le] at h2
    rw [norm_mul, e1]
    rw [show ‖a / ‖a‖ ^ 2‖ = 1 / ‖a‖ by
      rw [norm_div]
      have hnr : ‖(‖a‖ ^ 2 : ℂ)‖ = ‖a‖ ^ 2 := by
        simp
      rw [hnr]
      field_simp [hA0.ne']]
    field_simp [hA0.ne']
  · -- `(conj u * a).re = 2`
    have e1 : conj ((a / ‖a‖ ^ 2) * (2 - s * Complex.I * Real.sqrt (‖a‖ ^ 2 - 4))) * a
        = 2 + s * Complex.I * Real.sqrt (‖a‖ ^ 2 - 4) := by
      rw [map_mul, map_div₀, map_pow, Complex.conj_ofReal, map_sub, map_ofNat, map_mul, map_mul,
        Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal]
      have key : conj a / (‖a‖ ^ 2 : ℂ) * a = 1 := by
        rw [div_mul_eq_mul_div, mul_comm (conj a) a, Complex.mul_conj, Complex.normSq_eq_norm_sq,
          ← Complex.ofReal_pow, div_self hA2']
      have e2 : conj a / (‖a‖ ^ 2 : ℂ) * (2 - ↑s * -Complex.I * ↑(Real.sqrt (‖a‖ ^ 2 - 4))) * a
          = (conj a / (‖a‖ ^ 2 : ℂ) * a) * (2 - ↑s * -Complex.I * ↑(Real.sqrt (‖a‖ ^ 2 - 4))) := by
        ring
      rw [e2, key, one_mul]
      ring
    rw [e1]
    simp
  · -- the signed-distance formula
    intro z
    have e1 : conj ((a / ‖a‖ ^ 2) * (2 - s * Complex.I * Real.sqrt (‖a‖ ^ 2 - 4))) * z
        = (z / a) * (2 + s * Complex.I * Real.sqrt (‖a‖ ^ 2 - 4)) := by
      rw [map_mul, map_div₀, map_pow, Complex.conj_ofReal, map_sub, map_ofNat, map_mul, map_mul,
        Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal]
      have key : conj a / (‖a‖ ^ 2 : ℂ) * z = z / a := by
        rw [div_mul_eq_mul_div, div_eq_div_iff (pow_ne_zero 2 hA0') ha0,
          show conj a * z * a = z * (a * conj a) by ring, Complex.mul_conj,
          Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow]
      have e2 : conj a / (‖a‖ ^ 2 : ℂ) * (2 - ↑s * -Complex.I * ↑(Real.sqrt (‖a‖ ^ 2 - 4))) * z
          = (conj a / (‖a‖ ^ 2 : ℂ) * z) * (2 - ↑s * -Complex.I * ↑(Real.sqrt (‖a‖ ^ 2 - 4))) := by
        ring
      rw [e2, key]
      ring
    rw [e1]
    have e3 : (2 + s * Complex.I * Real.sqrt (‖a‖ ^ 2 - 4) : ℂ).re = 2 := by
      simp
    have e4 : (2 + s * Complex.I * Real.sqrt (‖a‖ ^ 2 - 4) : ℂ).im
        = s * Real.sqrt (‖a‖ ^ 2 - 4) := by
      simp
    rw [Complex.mul_re, e3, e4]
    ring

/-- For `|x| ≤ π`, `|sin x| = sin |x|`. -/
lemma abs_sin_eq_sin_abs {x : ℝ} (hx : |x| ≤ Real.pi) : |Real.sin x| = Real.sin |x| := by
  by_cases h : 0 ≤ x
  · rw [abs_of_nonneg h, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h (abs_le.1 hx).2)]
  · push Not at h
    rcases (abs_le.1 hx).1.lt_or_eq with hlt | heq
    · rw [abs_of_neg h, abs_of_neg (Real.sin_neg_of_neg_of_neg_pi_lt h hlt), ← Real.sin_neg]
    · subst heq
      simp [Real.sin_neg, Real.sin_pi, abs_of_nonneg Real.pi_pos.le]

lemma uangle_comm (x y : ℂ) : uangle x y = uangle y x := by
  rw [uangle, uangle, ← Complex.abs_arg_inv, inv_div]

lemma uangle_mem_Icc (x y : ℂ) : uangle x y ∈ Set.Icc 0 Real.pi :=
  ⟨abs_nonneg _, Complex.abs_arg_le_pi _⟩

/-- The strong angle bound: the angle at `O k` between the rays to `O i` and `O j`
is at least `arcsin (2 / min dᵢ dⱼ)`, hence at least `2 / min dᵢ dⱼ` and at least
`1/dᵢ + 1/dⱼ`.  This is the "first key observation" of the official solution. -/
lemma strong_angle (hn : 3 ≤ n) (hlines : NoLineMeetsThree O) {k i j : Fin n}
    (hki : k ≠ i) (hkj : k ≠ j) (hij : i ≠ j) :
    Real.arcsin (2 / min ‖O i - O k‖ ‖O j - O k‖) ≤ uangle (O i - O k) (O j - O k) := by
  wlog hAB : ‖O i - O k‖ ≤ ‖O j - O k‖ generalizing i j
  · rw [min_comm, uangle_comm]
    exact this hkj hki hij.symm (le_of_not_ge hAB)
  have hd1 : 2 < ‖O i - O k‖ := by
    have h2 := two_lt_dist hn hlines hki
    rwa [norm_sub_rev] at h2
  have hd2 : 2 < ‖O j - O k‖ := by
    have h2 := two_lt_dist hn hlines hkj
    rwa [norm_sub_rev] at h2
  have hi0 : O i - O k ≠ 0 := by
    by_contra h
    rw [h, norm_zero] at hd1
    linarith
  have hj0 : O j - O k ≠ 0 := by
    by_contra h
    rw [h, norm_zero] at hd2
    linarith
  set a := O i - O k with ha
  set b := O j - O k with hb
  set A := ‖a‖ with hA
  set B := ‖b‖ with hB
  set Δ := A ^ 2 - 4 with hΔ
  set Δ' := B ^ 2 - 4 with hΔ'
  set θ := Real.arcsin (2 / A) with hθ
  set θ' := Real.arcsin (2 / B) with hθ'
  have hA0 : 0 < A := by rw [hA]; exact norm_pos_iff.mpr hi0
  have hB0 : 0 < B := by rw [hB]; exact norm_pos_iff.mpr hj0
  have hd1' : 2 < ‖a‖ := by rw [hA] at hd1; exact hd1
  have hd2' : 2 < ‖b‖ := by rw [hB] at hd2; exact hd2
  have hΔ0 : 0 ≤ Δ := by rw [hΔ, hA]; nlinarith [hd1']
  have hΔ'0 : 0 ≤ Δ' := by rw [hΔ', hB]; nlinarith [hd2']
  have hmin : min A B = A := min_eq_left hAB
  have hsinθ : Real.sin θ = 2 / A := by
    rw [hθ]
    apply Real.sin_arcsin
    · have h1 : (0:ℝ) < 2 / A := by positivity
      linarith
    · rw [div_le_one₀ hA0]
      linarith
  have hsinθ' : Real.sin θ' = 2 / B := by
    rw [hθ']
    apply Real.sin_arcsin
    · have h1 : (0:ℝ) < 2 / B := by positivity
      linarith
    · rw [div_le_one₀ hB0]
      linarith
  have hcosθ : Real.cos θ = Real.sqrt Δ / A := by
    rw [hθ, Real.cos_arcsin]
    rw [show (1:ℝ) - (2 / A) ^ 2 = (A ^ 2 - 4) / A ^ 2 by field_simp [hA0.ne']; ring]
    rw [Real.sqrt_div hΔ0, Real.sqrt_sq hA0.le, hΔ]
  have hcosθ' : Real.cos θ' = Real.sqrt Δ' / B := by
    rw [hθ', Real.cos_arcsin]
    rw [show (1:ℝ) - (2 / B) ^ 2 = (B ^ 2 - 4) / B ^ 2 by field_simp [hB0.ne']; ring]
    rw [Real.sqrt_div hΔ'0, Real.sqrt_sq hB0.le, hΔ']
  have hθ0 : 0 < θ := by rw [hθ, Real.arcsin_pos]; positivity
  have hθ'0 : 0 < θ' := by rw [hθ', Real.arcsin_pos]; positivity
  have hθπ : θ < Real.pi / 2 := by
    rw [hθ]
    have hlt : 2 / A < 1 := by
      rw [div_lt_one₀ hA0]
      linarith
    calc Real.arcsin (2 / A) < Real.arcsin 1 :=
        Real.arcsin_lt_arcsin (by
          have h1 : (0:ℝ) < 2 / A := by positivity
          linarith) hlt (le_refl 1)
      _ = Real.pi / 2 := Real.arcsin_one
  have hθ'π : θ' < Real.pi / 2 := by
    rw [hθ']
    have hlt : 2 / B < 1 := by
      rw [div_lt_one₀ hB0]
      linarith
    calc Real.arcsin (2 / B) < Real.arcsin 1 :=
        Real.arcsin_lt_arcsin (by
          have h1 : (0:ℝ) < 2 / B := by positivity
          linarith) hlt (le_refl 1)
      _ = Real.pi / 2 := Real.arcsin_one
  obtain ⟨u₁, hu₁, hu₁a, hu₁f⟩ := tangent_normal a hd1' 1 (Or.inl rfl)
  obtain ⟨u₂, hu₂, hu₂a, hu₂f⟩ := tangent_normal a hd1' (-1) (Or.inr rfl)
  obtain ⟨v₁, hv₁, hv₁b, hv₁f⟩ := tangent_normal b hd2' 1 (Or.inl rfl)
  obtain ⟨v₂, hv₂, hv₂a, hv₂f⟩ := tangent_normal b hd2' (-1) (Or.inr rfl)
  have c1 := tangent_constr hlines hki hkj hij u₁ hu₁ hu₁a
  have c2 := tangent_constr hlines hki hkj hij u₂ hu₂ hu₂a
  have c3 := tangent_constr hlines hkj hki hij.symm v₁ hv₁ hv₁b
  have c4 := tangent_constr hlines hkj hki hij.symm v₂ hv₂ hv₂a
  set q := b / a with hq
  set p := a / b with hp
  set φ₀ := Complex.arg q with hφ₀
  set φ := uangle a b with hφ
  have hq0 : q ≠ 0 := by
    rw [hq]
    exact div_ne_zero hj0 hi0
  have hpq : p = q⁻¹ := by rw [hp, hq, inv_div]
  have hnq : ‖q‖ = B / A := by rw [hq, norm_div, hA, hB]
  have hreq : q.re = (B / A) * Real.cos φ₀ := by
    rw [hφ₀, Complex.cos_arg hq0, hnq]
    field_simp [hA0.ne']
  have himq : q.im = (B / A) * Real.sin φ₀ := by
    rw [hφ₀, Complex.sin_arg, hnq]
    field_simp [hA0.ne']
  have hrep : p.re = (A / B) * Real.cos φ₀ := by
    rw [hpq, Complex.inv_re, hreq, Complex.normSq_eq_norm_sq, hnq]
    field_simp [hA0.ne', hB0.ne']
  have himp : p.im = -((A / B) * Real.sin φ₀) := by
    rw [hpq, Complex.inv_im, himq, Complex.normSq_eq_norm_sq, hnq]
    field_simp [hA0.ne', hB0.ne']
  have hφ_eq : φ = |φ₀| := by
    rw [hφ, uangle, ← hp, hpq, Complex.abs_arg_inv, ← hφ₀]
  have hcosφ : Real.cos φ = Real.cos φ₀ := by rw [hφ_eq, Real.cos_abs]
  have hsinφ : Real.sin φ = |Real.sin φ₀| := by
    rw [hφ_eq]
    exact (abs_sin_eq_sin_abs (Complex.abs_arg_le_pi _)).symm
  have him_abs : |q.im| = (B / A) * Real.sin φ := by
    rw [himq, abs_mul, abs_of_nonneg (by positivity), ← hsinφ]
  have him_abs' : |p.im| = (A / B) * Real.sin φ := by
    rw [himp, abs_neg, abs_mul, abs_of_nonneg (by positivity), ← hsinφ]
  have e1 : (conj u₁ * b).re = 2 * q.re - Real.sqrt Δ * q.im := by
    rw [hu₁f b, ← hq, show Real.sqrt (‖a‖ ^ 2 - 4) = Real.sqrt Δ by rw [hΔ, hA]]
    ring_nf
  have e2 : (conj u₂ * b).re = 2 * q.re + Real.sqrt Δ * q.im := by
    rw [hu₂f b, ← hq, show Real.sqrt (‖a‖ ^ 2 - 4) = Real.sqrt Δ by rw [hΔ, hA]]
    ring_nf
  have e3 : (conj v₁ * a).re = 2 * p.re - Real.sqrt Δ' * p.im := by
    rw [hv₁f a, ← hp, show Real.sqrt (‖b‖ ^ 2 - 4) = Real.sqrt Δ' by rw [hΔ', hB]]
    ring_nf
  have e4 : (conj v₂ * a).re = 2 * p.re + Real.sqrt Δ' * p.im := by
    rw [hv₂f a, ← hp, show Real.sqrt (‖b‖ ^ 2 - 4) = Real.sqrt Δ' by rw [hΔ', hB]]
    ring_nf
  have hV : B * Real.sin (θ - φ) = 2 * q.re - Real.sqrt Δ * |q.im| := by
    rw [Real.sin_sub, hsinθ, hcosθ, hreq, him_abs, hcosφ]
    field_simp [hA0.ne']
  have hW : A * Real.sin (θ' + φ) = 2 * p.re + Real.sqrt Δ' * |p.im| := by
    rw [Real.sin_add, hsinθ', hcosθ', hrep, him_abs', hcosφ]
    field_simp [hB0.ne']
  have hVc : B * Real.sin (θ - φ) < 0 ∨ 2 < B * Real.sin (θ - φ) := by
    by_cases hs : 0 ≤ q.im
    · rw [hV, abs_of_nonneg hs, ← e1]
      exact c1
    · push Not at hs
      rw [hV, abs_of_neg hs,
        show 2 * q.re - Real.sqrt Δ * -q.im = 2 * q.re + Real.sqrt Δ * q.im by ring, ← e2]
      exact c2
  have hWc : A * Real.sin (θ' + φ) < 0 ∨ 2 < A * Real.sin (θ' + φ) := by
    by_cases hs : 0 ≤ p.im
    · rw [hW, abs_of_nonneg hs, ← e4]
      exact c4
    · push Not at hs
      rw [hW, abs_of_neg hs,
        show 2 * p.re + Real.sqrt Δ' * -p.im = 2 * p.re - Real.sqrt Δ' * p.im by ring, ← e3]
      exact c3
  -- the final contradiction
  have hφ0' : 0 ≤ φ := by rw [hφ_eq]; exact abs_nonneg _
  by_contra hlt
  push Not at hlt
  rw [hmin, ← hθ] at hlt
  have hV0 : 0 < B * Real.sin (θ - φ) := by
    apply mul_pos hB0
    apply Real.sin_pos_of_mem_Ioo
    constructor
    · linarith [hlt]
    · linarith [Real.pi_pos, hθπ]
  have hV2 : 2 < B * Real.sin (θ - φ) := by
    rcases hVc with h | h
    · linarith [hV0]
    · exact h
  have hsin1 : Real.sin θ' < Real.sin (θ - φ) := by
    have h3 : 2 / B < Real.sin (θ - φ) := by
      rw [div_lt_iff₀ hB0]
      linarith [hV2]
    linarith [hsinθ', h3]
  have hlt1 : θ' < θ - φ := by
    have hθ'mem : θ' ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := Real.arcsin_mem_Icc _
    have hmem : θ - φ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor
      · linarith [Real.pi_pos, hlt]
      · linarith [Real.pi_pos, hθπ]
    exact (Real.strictMonoOn_sin.lt_iff_lt hθ'mem hmem).mp hsin1
  have hW0 : 0 < A * Real.sin (θ' + φ) := by
    apply mul_pos hA0
    apply Real.sin_pos_of_mem_Ioo
    constructor
    · linarith [hθ'0, hφ0']
    · linarith [hθ'π, hlt, hθπ, Real.pi_pos]
  have hW2 : 2 < A * Real.sin (θ' + φ) := by
    rcases hWc with h | h
    · linarith [hW0]
    · exact h
  have hsin2 : Real.sin θ < Real.sin (θ' + φ) := by
    have h3 : 2 / A < Real.sin (θ' + φ) := by
      rw [div_lt_iff₀ hA0]
      linarith [hW2]
    linarith [hsinθ, h3]
  have hlt2 : θ < θ' + φ := by
    by_cases hcase : θ' + φ ≤ Real.pi / 2
    · have h1 := (Real.strictMonoOn_sin.lt_iff_lt ?_ ?_).mp hsin2
      · exact h1
      · constructor
        · linarith [hθ0]
        · linarith [hθπ]
      · constructor
        · linarith [hθ'0, hφ0']
        · exact hcase
    · push Not at hcase
      linarith [hθπ, hcase]
  linarith [hlt1, hlt2]


/-- The angular gap between the directions from `O k` to two other centres
(measured either way around the `mod π` circle of directions) exceeds the sum
of the two tangent half-angles `arcsin (1/d)`.  Ordered version. -/
lemma sector_gap_ordered (hn : 3 ≤ n) (hlines : NoLineMeetsThree O) {k i j : Fin n}
    (hki : k ≠ i) (hkj : k ≠ j) (hij : i ≠ j)
    (hγ : toIocMod Real.pi_pos 0 (Complex.arg (O i - O k)) <
      toIocMod Real.pi_pos 0 (Complex.arg (O j - O k))) :
    Real.arcsin (1 / ‖O i - O k‖) + Real.arcsin (1 / ‖O j - O k‖) <
      toIocMod Real.pi_pos 0 (Complex.arg (O j - O k)) -
        toIocMod Real.pi_pos 0 (Complex.arg (O i - O k)) ∧
    Real.arcsin (1 / ‖O i - O k‖) + Real.arcsin (1 / ‖O j - O k‖) <
      Real.pi - (toIocMod Real.pi_pos 0 (Complex.arg (O j - O k)) -
        toIocMod Real.pi_pos 0 (Complex.arg (O i - O k))) := by
  have hd1 : 2 < ‖O i - O k‖ := by
    have h2 := two_lt_dist hn hlines hki
    rwa [norm_sub_rev] at h2
  have hd2 : 2 < ‖O j - O k‖ := by
    have h2 := two_lt_dist hn hlines hkj
    rwa [norm_sub_rev] at h2
  have hi0 : O i - O k ≠ 0 := by
    by_contra h
    rw [h, norm_zero] at hd1
    linarith
  have hj0 : O j - O k ≠ 0 := by
    by_contra h
    rw [h, norm_zero] at hd2
    linarith
  set γi := toIocMod Real.pi_pos 0 (Complex.arg (O i - O k)) with hγi
  set γj := toIocMod Real.pi_pos 0 (Complex.arg (O j - O k)) with hγj
  set di := ‖O i - O k‖ with hdi
  set dj := ‖O j - O k‖ with hdj
  set xi := Real.arcsin (1 / di) with hxi
  set xj := Real.arcsin (1 / dj) with hxj
  have hdi0 : 0 < di := by rw [hdi]; exact norm_pos_iff.mpr hi0
  have hdj0 : 0 < dj := by rw [hdj]; exact norm_pos_iff.mpr hj0
  have h1di : 0 < 1 / di := by positivity
  have h1dj : 0 < 1 / dj := by positivity
  have hxi0 : 0 < xi := by rw [hxi, Real.arcsin_pos]; positivity
  have hxj0 : 0 < xj := by rw [hxj, Real.arcsin_pos]; positivity
  have hxiπ : xi ≤ Real.pi / 2 := by
    rw [hxi]
    exact (Real.arcsin_mem_Icc _).2
  have hxjπ : xj ≤ Real.pi / 2 := by
    rw [hxj]
    exact (Real.arcsin_mem_Icc _).2
  have hsin_xi : Real.sin xi = 1 / di := by
    rw [hxi]
    apply Real.sin_arcsin
    · linarith
    · rw [div_le_one₀ hdi0]
      linarith
  have hsin_xj : Real.sin xj = 1 / dj := by
    rw [hxj]
    apply Real.sin_arcsin
    · linarith
    · rw [div_le_one₀ hdj0]
      linarith
  have e1 : Complex.arg (O i - O k) =
      γi + toIocDiv Real.pi_pos 0 (Complex.arg (O i - O k)) • Real.pi := by
    rw [hγi]
    exact (toIocMod_add_toIocDiv_zsmul Real.pi_pos 0 _).symm
  have e2 : Complex.arg (O j - O k) =
      γj + toIocDiv Real.pi_pos 0 (Complex.arg (O j - O k)) • Real.pi := by
    rw [hγj]
    exact (toIocMod_add_toIocDiv_zsmul Real.pi_pos 0 _).symm
  have hsin_i : ∀ ψ : ℝ, |Real.sin (ψ - Complex.arg (O i - O k))| = |Real.sin (ψ - γi)| := by
    intro ψ
    rw [e1, show ψ - (γi + toIocDiv Real.pi_pos 0 (Complex.arg (O i - O k)) • Real.pi)
        = (ψ - γi) - toIocDiv Real.pi_pos 0 (Complex.arg (O i - O k)) • Real.pi by ring,
      abs_sin_sub_zsmul_pi]
  have hsin_j : ∀ ψ : ℝ, |Real.sin (ψ - Complex.arg (O j - O k))| = |Real.sin (ψ - γj)| := by
    intro ψ
    rw [e2, show ψ - (γj + toIocDiv Real.pi_pos 0 (Complex.arg (O j - O k)) • Real.pi)
        = (ψ - γj) - toIocDiv Real.pi_pos 0 (Complex.arg (O j - O k)) • Real.pi by ring,
      abs_sin_sub_zsmul_pi]
  -- the line through `O k` with direction `ψ` meets circles `i` and `j`
  have line_bound : ∀ ψ : ℝ, |Real.sin (ψ - γi)| ≤ Real.sin xi →
      |Real.sin (ψ - γj)| ≤ Real.sin xj → False := by
    intro ψ hsi hsj
    set u := Complex.I * Complex.exp (ψ * Complex.I) with hu
    have hu1 : ‖u‖ = 1 := by
      rw [hu, norm_mul, Complex.norm_I, one_mul]
      exact Complex.norm_exp_ofReal_mul_I ψ
    have hd : ∀ zz : ℂ, (conj u * zz).re - (conj u * O k).re = (conj u * (zz - O k)).re := by
      intro zz
      rw [← Complex.sub_re, ← mul_sub]
    have hmem_i : |(conj u * O i).re - (conj u * O k).re| ≤ 1 := by
      rw [hd, sdist_exp_normal, abs_mul, abs_of_nonneg (norm_nonneg _),
        show Complex.arg (O i - O k) - ψ = -(ψ - Complex.arg (O i - O k)) by ring, Real.sin_neg,
        abs_neg, hsin_i]
      have hsi' : Real.sin (ψ - γi) ≤ 1 / di := by
        rw [abs_le] at hsi
        linarith [hsi.2]
      calc di * |Real.sin (ψ - γi)| ≤ di * Real.sin xi := by gcongr
        _ = di * (1 / di) := by rw [hsin_xi]
        _ = 1 := by rw [mul_one_div, div_self hdi0.ne']
    have hmem_j : |(conj u * O j).re - (conj u * O k).re| ≤ 1 := by
      rw [hd, sdist_exp_normal, abs_mul, abs_of_nonneg (norm_nonneg _),
        show Complex.arg (O j - O k) - ψ = -(ψ - Complex.arg (O j - O k)) by ring, Real.sin_neg,
        abs_neg, hsin_j]
      have hsj' : Real.sin (ψ - γj) ≤ 1 / dj := by
        rw [abs_le] at hsj
        linarith [hsj.2]
      calc dj * |Real.sin (ψ - γj)| ≤ dj * Real.sin xj := by gcongr
        _ = dj * (1 / dj) := by rw [hsin_xj]
        _ = 1 := by rw [mul_one_div, div_self hdj0.ne']
    exact not_three_mem hlines u hu1 (conj u * O k).re hki hkj hij (by simp) hmem_i hmem_j
  have hg0 : 0 < γj - γi := sub_pos.mpr hγ
  have hxixj : 0 < xi + xj := add_pos hxi0 hxj0
  have hγi_mem := toIocMod_mem_Ioc Real.pi_pos 0 (Complex.arg (O i - O k))
  have hγj_mem := toIocMod_mem_Ioc Real.pi_pos 0 (Complex.arg (O j - O k))
  rw [← hγi] at hγi_mem
  rw [← hγj] at hγj_mem
  have hpg0 : 0 < Real.pi - (γj - γi) := by
    have h1 := hγi_mem.1
    have h2 := hγj_mem.2
    linarith
  constructor
  · -- the internal gap: `xi + xj < γj - γi`
    by_contra h
    push Not at h
    have hei : γi + xi * (γj - γi) / (xi + xj) - γi = xi * (γj - γi) / (xi + xj) := by ring
    have hej : γj - (γi + xi * (γj - γi) / (xi + xj)) = xj * (γj - γi) / (xi + xj) := by
      field_simp
      ring
    set ψ := γi + xi * (γj - γi) / (xi + xj) with hψ
    have hψi0 : 0 ≤ ψ - γi := by
      rw [hψ, hei]
      positivity
    have hψi1 : ψ - γi ≤ xi := by
      rw [hψ, hei, div_le_iff₀ hxixj]
      nlinarith [h, hxi0]
    have hψj0 : 0 ≤ γj - ψ := by
      rw [hψ, hej]
      positivity
    have hψj1 : γj - ψ ≤ xj := by
      rw [hψ, hej, div_le_iff₀ hxixj]
      nlinarith [h, hxj0]
    refine line_bound ψ ?_ ?_
    · have habs : |ψ - γi| ≤ Real.pi := by
        rw [abs_of_nonneg hψi0]
        linarith [hxiπ, Real.pi_pos]
      rw [abs_sin_eq_sin_abs habs, abs_of_nonneg hψi0]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hxiπ hψi1
    · have habs : |ψ - γj| ≤ Real.pi := by
        rw [abs_sub_comm, abs_of_nonneg hψj0]
        linarith [hxjπ, Real.pi_pos]
      rw [abs_sin_eq_sin_abs habs, abs_sub_comm, abs_of_nonneg hψj0]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hxjπ hψj1
  · -- the wrap-around gap: `xi + xj < π - (γj - γi)`
    by_contra h
    push Not at h
    have hej : γj + xj * (Real.pi - (γj - γi)) / (xi + xj) - γj
        = xj * (Real.pi - (γj - γi)) / (xi + xj) := by ring
    have hei : Real.pi - (γj + xj * (Real.pi - (γj - γi)) / (xi + xj) - γi)
        = xi * (Real.pi - (γj - γi)) / (xi + xj) := by
      field_simp
      ring
    set ψ := γj + xj * (Real.pi - (γj - γi)) / (xi + xj) with hψ
    have hψj0 : 0 ≤ ψ - γj := by
      rw [hψ, hej]
      positivity
    have hψj1 : ψ - γj ≤ xj := by
      rw [hψ, hej, div_le_iff₀ hxixj]
      nlinarith [h, hxj0, hpg0]
    have hψi0 : 0 ≤ ψ - γi := by
      rw [hψ]
      have he' : γj + xj * (Real.pi - (γj - γi)) / (xi + xj) - γi
          = (γj - γi) + xj * (Real.pi - (γj - γi)) / (xi + xj) := by ring
      rw [he']
      positivity
    have hψiπ : ψ - γi ≤ Real.pi := by
      rw [hψ]
      have he' : γj + xj * (Real.pi - (γj - γi)) / (xi + xj) - γi
          = (γj - γi) + xj * (Real.pi - (γj - γi)) / (xi + xj) := by ring
      rw [he']
      have hxjle : xj * (Real.pi - (γj - γi)) / (xi + xj) ≤ Real.pi - (γj - γi) := by
        rw [div_le_iff₀ hxixj]
        nlinarith [hxi0, hpg0]
      linarith [hxjle]
    have hψi2 : Real.pi - (ψ - γi) ≤ xi := by
      rw [hψ, hei, div_le_iff₀ hxixj]
      exact mul_le_mul_of_nonneg_left h hxi0.le
    refine line_bound ψ ?_ ?_
    · have habs : |ψ - γi| ≤ Real.pi := by
        rw [abs_of_nonneg hψi0]
        linarith
      rw [abs_sin_eq_sin_abs habs, abs_of_nonneg hψi0, ← Real.sin_pi_sub (ψ - γi)]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hxiπ hψi2
    · have habs : |ψ - γj| ≤ Real.pi := by
        rw [abs_of_nonneg hψj0]
        linarith [hxjπ, Real.pi_pos]
      rw [abs_sin_eq_sin_abs habs, abs_of_nonneg hψj0]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hxjπ hψj1

/-- The angular gap between the directions from `O k` to two other centres
(measured either way around the `mod π` circle of directions) exceeds the sum
of the two tangent half-angles `arcsin (1/d)`. -/
lemma sector_gap (hn : 3 ≤ n) (hlines : NoLineMeetsThree O) {k i j : Fin n}
    (hki : k ≠ i) (hkj : k ≠ j) (hij : i ≠ j) :
    Real.arcsin (1 / ‖O i - O k‖) + Real.arcsin (1 / ‖O j - O k‖) <
      |toIocMod Real.pi_pos 0 (Complex.arg (O i - O k)) -
        toIocMod Real.pi_pos 0 (Complex.arg (O j - O k))| ∧
    Real.arcsin (1 / ‖O i - O k‖) + Real.arcsin (1 / ‖O j - O k‖) <
      Real.pi - |toIocMod Real.pi_pos 0 (Complex.arg (O i - O k)) -
        toIocMod Real.pi_pos 0 (Complex.arg (O j - O k))| := by
  have hγne := arg_toIocMod_ne hn hlines hki hkj hij
  rcases lt_trichotomy (toIocMod Real.pi_pos 0 (Complex.arg (O i - O k)))
    (toIocMod Real.pi_pos 0 (Complex.arg (O j - O k))) with h | h | h
  · obtain ⟨h1, h2⟩ := sector_gap_ordered hn hlines hki hkj hij h
    refine ⟨?_, ?_⟩ <;> rw [abs_of_neg (sub_neg.mpr h), neg_sub]
    · exact h1
    · exact h2
  · exact absurd h hγne
  · obtain ⟨h1, h2⟩ := sector_gap_ordered hn hlines hkj hki hij.symm h
    refine ⟨?_, ?_⟩ <;> rw [abs_of_pos (sub_pos.mpr h), add_comm]
    · exact h1
    · exact h2

variable {k : Fin n} {γ x : Fin n → ℝ}

/-- shared sorted-list setup: sort `univ.erase k` by the key `γ`. -/
lemma sorted_setup (hn : 3 ≤ n)
    (hdist : ∀ i j : Fin n, i ≠ k → j ≠ k → i ≠ j → γ i ≠ γ j) :
    ∃ (l : List {a // a ∈ univ.erase k}), l.length = n - 1 ∧
      l.Pairwise (fun a b => γ a.1 ≤ γ b.1) ∧ l.Nodup ∧
      l.toFinset = (univ.erase k).attach := by
  set s : Finset (Fin n) := univ.erase k with hs
  have hinj : ∀ a ∈ s, ∀ b ∈ s, γ a = γ b → a = b := by
    intro a ha b hb hab
    by_contra hne
    exact hdist a b (mem_erase.1 ha).1 (mem_erase.1 hb).1 hne hab
  set st : Finset {a // a ∈ s} := s.attach with hst
  set r : {a // a ∈ s} → {a // a ∈ s} → Prop := fun a b => γ a.1 ≤ γ b.1 with hr
  have _ : Std.Antisymm r :=
    ⟨fun a b h1 h2 => Subtype.ext (hinj a.1 a.2 b.1 b.2 (le_antisymm h1 h2))⟩
  have _ : Std.Total r := ⟨fun a b => le_total _ _⟩
  have _ : IsTrans {a // a ∈ s} r := ⟨fun a b c => le_trans⟩
  set l := st.sort r with hl
  refine ⟨l, ?_, ?_, ?_, ?_⟩
  · rw [hl, Finset.length_sort, hst, Finset.card_attach, hs,
      Finset.card_erase_of_mem (mem_univ _), Finset.card_univ, Fintype.card_fin]
  · rw [hl]
    exact Finset.pairwise_sort _ _
  · rw [hl]
    exact Finset.sort_nodup _ _
  · rw [hl]
    exact Finset.sort_toFinset _ _

/-- elements of the sorted list at distinct positions have distinct `γ` values. -/
lemma sorted_consec_lt {l : List {a // a ∈ univ.erase k}}
    (hdist : ∀ i j : Fin n, i ≠ k → j ≠ k → i ≠ j → γ i ≠ γ j)
    (hsort : l.Pairwise (fun a b => γ a.1 ≤ γ b.1)) (hnodup : l.Nodup)
    {i j : Fin l.length} (hij : i < j) :
    γ (l.get i).1 < γ (l.get j).1 := by
  have h1 := List.Pairwise.rel_get_of_lt hsort hij
  have h2 : l.get i ≠ l.get j := by
    intro heq
    have h2 := (List.Nodup.get_inj_iff hnodup).mp heq
    exact absurd h2 (ne_of_lt hij)
  have h3 : (l.get i).1 ≠ (l.get j).1 := fun heq => h2 (Subtype.ext heq)
  have h4 : γ (l.get i).1 ≠ γ (l.get j).1 := by
    intro heq
    exact h3 (by
      by_contra hne
      exact hdist _ _ (mem_erase.1 (l.get i).2).1 (mem_erase.1 (l.get j).2).1 hne heq)
  exact lt_of_le_of_ne h1 h4

/-- the sum over the sorted list equals the sum over `univ.erase k` -/
lemma sorted_sum_eq {l : List {a // a ∈ univ.erase k}}
    (hnodup : l.Nodup) (htf : l.toFinset = (univ.erase k).attach) (f : Fin n → ℝ) :
    (l.map (fun a => f a.1)).sum = ∑ j ∈ univ.erase k, f j := by
  rw [← List.sum_toFinset _ hnodup, htf, Finset.sum_attach]

/-- sum over a list as a range-sum of `getD`. -/
lemma list_sum_map_getD {α : Type*} (l : List α) (d : α) (f : α → ℝ) :
    (l.map f).sum = ∑ i ∈ Finset.range l.length, f (l.getD i d) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, List.length_cons, Finset.sum_range_succ']
    rw [ih, List.getD_cons_zero]
    have h2 : (∑ k_1 ∈ Finset.range l.length, f ((a :: l).getD (k_1 + 1) d))
        = ∑ i ∈ Finset.range l.length, f (l.getD i d) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [List.getD_cons_succ]
    rw [h2]
    ring

lemma row_bound_nonvertex_mock (hn : 3 ≤ n)
    (hdist : ∀ i j : Fin n, i ≠ k → j ≠ k → i ≠ j → γ i ≠ γ j)
    (hgap : ∀ i j : Fin n, i ≠ k → j ≠ k → i ≠ j →
      x i + x j < |γ i - γ j| ∧ x i + x j < Real.pi - |γ i - γ j|)
    (hγmem : ∀ j : Fin n, j ≠ k → γ j ∈ Set.Ioc 0 Real.pi) :
    2 * (∑ j ∈ univ.erase k, x j) < Real.pi := by
  obtain ⟨l, hlen, hsort, hnodup, htf⟩ := sorted_setup hn hdist
  have hl2 : 2 ≤ l.length := by rw [hlen]; omega
  set d := l.get ⟨0, by omega⟩ with hd
  -- consecutive gap lower bound
  have hbound : ∀ i : ℕ, i + 1 < l.length →
      x (l.getD i d).1 + x (l.getD (i + 1) d).1
        < γ (l.getD (i + 1) d).1 - γ (l.getD i d).1 := by
    intro i hi
    rw [List.getD_eq_getElem _ _ (by omega : i + 1 < l.length),
      List.getD_eq_getElem _ _ (by omega : i < l.length),
      show l[i]'(by omega : i < l.length) = l.get ⟨i, by omega⟩ from rfl,
      show l[i+1]'(by omega : i + 1 < l.length) = l.get ⟨i + 1, by omega⟩ from rfl]
    have hlt := sorted_consec_lt hdist hsort hnodup
      (show (⟨i, by omega⟩ : Fin l.length) < ⟨i + 1, by omega⟩ by simp)
    have hne : (l.get ⟨i, by omega⟩).1 ≠ (l.get ⟨i + 1, by omega⟩).1 := by
      intro heq
      have h2 := (List.Nodup.get_inj_iff hnodup).mp (Subtype.ext heq)
      simp at h2
    obtain ⟨hg1, -⟩ := hgap _ _ (mem_erase.1 (l.get ⟨i, by omega⟩).2).1
      (mem_erase.1 (l.get ⟨i + 1, by omega⟩).2).1 hne
    rwa [abs_of_neg (sub_neg.mpr hlt), neg_sub] at hg1
  -- the wrap-around gap lower bound
  have hwrap : x (l.getD 0 d).1 + x (l.getD (l.length - 1) d).1
      < (γ (l.getD 0 d).1 + Real.pi) - γ (l.getD (l.length - 1) d).1 := by
    have e0 : l.getD 0 d = l.get ⟨0, by omega⟩ := List.getD_eq_getElem _ _ (by omega)
    have e1 : l.getD (l.length - 1) d = l.get ⟨l.length - 1, by omega⟩ :=
      List.getD_eq_getElem _ _ (by omega)
    have hlt := sorted_consec_lt hdist hsort hnodup
      (show (⟨0, by omega⟩ : Fin l.length) < ⟨l.length - 1, by omega⟩ by
        simp only [Fin.lt_iff_val_lt_val]; omega)
    have hne : (l.get ⟨0, by omega⟩).1 ≠ (l.get ⟨l.length - 1, by omega⟩).1 := by
      intro heq
      have h2 := (List.Nodup.get_inj_iff hnodup).mp (Subtype.ext heq)
      simp only [Fin.ext_iff] at h2
      omega
    obtain ⟨-, hg2⟩ := hgap _ _ (mem_erase.1 (l.get ⟨0, by omega⟩).2).1
      (mem_erase.1 (l.get ⟨l.length - 1, by omega⟩).2).1 hne
    rw [abs_of_neg (sub_neg.mpr hlt), neg_sub] at hg2
    rw [e0, e1]
    linarith [hg2]
  -- telescoping sums
  have hs3 : (∑ i ∈ Finset.range (l.length - 1), (γ (l.getD (i + 1) d).1 - γ (l.getD i d).1))
      = γ (l.getD (l.length - 1) d).1 - γ (l.getD 0 d).1 :=
    Finset.sum_range_sub (fun i => γ (l.getD i d).1) (l.length - 1)
  have hlink : ∑ i ∈ Finset.range l.length, x (l.getD i d).1 = ∑ j ∈ univ.erase k, x j := by
    rw [← list_sum_map_getD l d (fun a => x a.1), sorted_sum_eq hnodup htf]
  have heq : (∑ i ∈ Finset.range (l.length - 1), (x (l.getD (i + 1) d).1 + x (l.getD i d).1))
      + (x (l.getD (l.length - 1) d).1 + x (l.getD 0 d).1)
      = 2 * (∑ j ∈ univ.erase k, x j) := by
    have e1 : (∑ i ∈ Finset.range (l.length - 1), x (l.getD (i + 1) d).1)
        = (∑ i ∈ Finset.range l.length, x (l.getD i d).1) - x (l.getD 0 d).1 := by
      have h1 := Finset.sum_range_succ' (fun i => x (l.getD i d).1) (l.length - 1)
      rw [show l.length - 1 + 1 = l.length by omega] at h1
      rw [h1]
      ring
    have e2 : (∑ i ∈ Finset.range (l.length - 1), x (l.getD i d).1)
        = (∑ i ∈ Finset.range l.length, x (l.getD i d).1) - x (l.getD (l.length - 1) d).1 := by
      have h2 := Finset.sum_range_succ (fun i => x (l.getD i d).1) (l.length - 1)
      rw [show l.length - 1 + 1 = l.length by omega] at h2
      rw [h2]
      ring
    rw [Finset.sum_add_distrib, e1, e2, hlink]
    ring
  have htot : 2 * (∑ j ∈ univ.erase k, x j) < Real.pi := by
    rw [← heq]
    have hs1 : (∑ i ∈ Finset.range (l.length - 1), (x (l.getD (i + 1) d).1 + x (l.getD i d).1))
        < ∑ i ∈ Finset.range (l.length - 1), (γ (l.getD (i + 1) d).1 - γ (l.getD i d).1) := by
      apply Finset.sum_lt_sum_of_nonempty
      · rw [Finset.nonempty_range_iff]
        omega
      · intro i hi
        rw [Finset.mem_range] at hi
        linarith [hbound i (by omega)]
    linarith [hs1, hwrap, hs3]
  exact htot

lemma row_bound_vertex_mock (hn : 3 ≤ n)
    (hdist : ∀ i j : Fin n, i ≠ k → j ≠ k → i ≠ j → γ i ≠ γ j)
    (hgap : ∀ i j : Fin n, i ≠ k → j ≠ k → i ≠ j → γ i < γ j →
      2 * x i < γ j - γ i ∧ 2 * x j < γ j - γ i)
    (hx0 : ∀ j : Fin n, j ≠ k → 0 < x j)
    (gmin gmax : ℝ)
    (hgmin : ∀ j : Fin n, j ≠ k → gmin ≤ γ j)
    (hgmax : ∀ j : Fin n, j ≠ k → γ j ≤ gmax)
    (hgmin_mem : ∃ i : Fin n, i ≠ k ∧ γ i = gmin)
    (hgmax_mem : ∃ i : Fin n, i ≠ k ∧ γ i = gmax) :
    2 * (∑ j ∈ univ.erase k, x j) < (gmax - gmin) * ((n : ℝ) - 1) / ((n : ℝ) - 2) := by
  obtain ⟨l, hlen, hsort, hnodup, htf⟩ := sorted_setup hn hdist
  have hl2 : 2 ≤ l.length := by rw [hlen]; omega
  set d := l.get ⟨0, by omega⟩ with hd
  -- the x-minimizer
  have hne_l : l ≠ [] := by
    have h1 : 0 < l.length := by omega
    exact List.ne_nil_of_length_pos h1
  set img := l.toFinset.image (fun a => x a.1) with himg
  have himg_ne : img.Nonempty := by
    rw [himg]
    apply Finset.Nonempty.image
    exact ⟨l.get ⟨0, by omega⟩, List.mem_toFinset.2 (List.get_mem _ _)⟩
  set m := img.min' himg_ne with hm
  obtain ⟨a, ha_tf, ha_eq⟩ := Finset.mem_image.1 (Finset.min'_mem img himg_ne)
  have ha_l : a ∈ l := List.mem_toFinset.1 ha_tf
  obtain ⟨fi, hfi⟩ := List.mem_iff_get.1 ha_l
  set f := fi.1 with hf
  have hfx : ∀ b ∈ l, x (l.get fi).1 ≤ x b.1 := by
    intro b hb
    have h1 : x b.1 ∈ img := Finset.mem_image.2 ⟨b, List.mem_toFinset.2 hb, rfl⟩
    have h2 := Finset.min'_le img _ h1
    rw [← ha_eq, ← hfi] at h2
    exact h2
  have hflt : f < l.length := by rw [hf]; exact fi.2
  -- gap function bounds
  have hbound : ∀ i : ℕ, i + 1 < l.length →
      2 * x (l.getD i d).1 < γ (l.getD (i + 1) d).1 - γ (l.getD i d).1 ∧
      2 * x (l.getD (i + 1) d).1 < γ (l.getD (i + 1) d).1 - γ (l.getD i d).1 := by
    intro i hi
    rw [List.getD_eq_getElem _ _ (by omega : i + 1 < l.length),
      List.getD_eq_getElem _ _ (by omega : i < l.length),
      show l[i]'(by omega : i < l.length) = l.get ⟨i, by omega⟩ from rfl,
      show l[i+1]'(by omega : i + 1 < l.length) = l.get ⟨i + 1, by omega⟩ from rfl]
    have hlt := sorted_consec_lt hdist hsort hnodup
      (show (⟨i, by omega⟩ : Fin l.length) < ⟨i + 1, by omega⟩ by
        simp only [Fin.lt_iff_val_lt_val]; omega)
    have hne : (l.get ⟨i, by omega⟩).1 ≠ (l.get ⟨i + 1, by omega⟩).1 := by
      intro heq
      have h2 := (List.Nodup.get_inj_iff hnodup).mp (Subtype.ext heq)
      simp only [Fin.ext_iff] at h2
      omega
    exact hgap _ _ (mem_erase.1 (l.get ⟨i, by omega⟩).2).1
      (mem_erase.1 (l.get ⟨i + 1, by omega⟩).2).1 hne hlt
  -- head/tail of the sorted list attain the min/max of `γ`
  have hle_all : ∀ a ∈ l, γ (l.get ⟨0, by omega⟩).1 ≤ γ a.1 := by
    intro a ha
    obtain ⟨j, hj⟩ := List.mem_iff_get.1 ha
    rw [← hj]
    by_cases hj0 : j = ⟨0, by omega⟩
    · rw [hj0]
    · have hlt : (⟨0, by omega⟩ : Fin l.length) < j := by
        rw [Fin.lt_iff_val_lt_val]
        show (0 : ℕ) < j.val
        have hjv : j.val ≠ 0 := by
          intro hz
          exact hj0 (Fin.ext hz)
        omega
      exact List.Pairwise.rel_get_of_lt hsort hlt
  have hge_all : ∀ a ∈ l, γ a.1 ≤ γ (l.get ⟨l.length - 1, by omega⟩).1 := by
    intro a ha
    obtain ⟨j, hj⟩ := List.mem_iff_get.1 ha
    rw [← hj]
    by_cases hj0 : j = ⟨l.length - 1, by omega⟩
    · rw [hj0]
    · have hlt : j < ⟨l.length - 1, by omega⟩ := by
        rw [Fin.lt_iff_val_lt_val]
        show j.val < l.length - 1
        have hjv : j.val ≠ l.length - 1 := by
          intro hz
          exact hj0 (Fin.ext hz)
        have hjv2 : j.val < l.length := j.2
        omega
      exact List.Pairwise.rel_get_of_lt hsort hlt
  -- the assignment sum bound
  have hassign : (∑ i ∈ Finset.range (l.length - 1),
      (if i < f then 2 * x (l.getD i d).1 else 2 * x (l.getD (i + 1) d).1))
      < γ (l.getD (l.length - 1) d).1 - γ (l.getD 0 d).1 := by
    have h1 : (∑ i ∈ Finset.range (l.length - 1),
        (if i < f then 2 * x (l.getD i d).1 else 2 * x (l.getD (i + 1) d).1))
        < ∑ i ∈ Finset.range (l.length - 1), (γ (l.getD (i + 1) d).1 - γ (l.getD i d).1) := by
      apply Finset.sum_lt_sum_of_nonempty
      · rw [Finset.nonempty_range_iff]
        omega
      · intro i hi
        rw [Finset.mem_range] at hi
        obtain ⟨hg1, hg2⟩ := hbound i (by omega)
        by_cases hcase : i < f
        · rw [if_pos hcase]
          exact hg1
        · rw [if_neg hcase]
          exact hg2
    rw [Finset.sum_range_sub (fun i => γ (l.getD i d).1) (l.length - 1)] at h1
    exact h1
  -- the assignment sum value
  have hcsum : (∑ i ∈ Finset.range (l.length - 1),
      (if i < f then 2 * x (l.getD i d).1 else 2 * x (l.getD (i + 1) d).1))
      = 2 * ((∑ i ∈ Finset.range l.length, x (l.getD i d).1) - x (l.getD f d).1) := by
    have hsplit : (∑ i ∈ Finset.range (l.length - 1),
        (if i < f then 2 * x (l.getD i d).1 else 2 * x (l.getD (i + 1) d).1))
        = (∑ i ∈ Finset.Ico 0 f, 2 * x (l.getD i d).1)
          + ∑ i ∈ Finset.Ico f (l.length - 1), 2 * x (l.getD (i + 1) d).1 := by
      rw [Finset.range_eq_Ico, ← Finset.Ico_union_Ico_eq_Ico (Nat.zero_le f) (by omega : f ≤ l.length - 1),
        Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive 0 f (l.length - 1))]
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_Ico] at hi
        rw [if_pos hi.2]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_Ico] at hi
        rw [if_neg (by omega)]
    have hright : ∑ i ∈ Finset.Ico f (l.length - 1), 2 * x (l.getD (i + 1) d).1
        = ∑ u ∈ Finset.Ico (f + 1) l.length, 2 * x (l.getD u d).1 := by
      rw [Finset.sum_Ico_eq_sum_range (fun i => 2 * x (l.getD (i + 1) d).1) f (l.length - 1),
        Finset.sum_Ico_eq_sum_range (fun u => 2 * x (l.getD u d).1) (f + 1) l.length]
      have hlen' : l.length - 1 - f = l.length - (f + 1) := by omega
      rw [hlen']
      apply Finset.sum_congr rfl
      intro j hj
      rw [show f + j + 1 = f + 1 + j by ring]
    have htotal : (∑ i ∈ Finset.Ico 0 f, 2 * x (l.getD i d).1)
        + (∑ u ∈ Finset.Ico (f + 1) l.length, 2 * x (l.getD u d).1)
        = (∑ i ∈ Finset.range l.length, 2 * x (l.getD i d).1) - 2 * x (l.getD f d).1 := by
      have h1 : Finset.Ico 0 f ∪ Finset.Ico f l.length = Finset.Ico 0 l.length :=
        Finset.Ico_union_Ico_eq_Ico (Nat.zero_le f) (by omega)
      have h2 : Finset.Ico f (f + 1) ∪ Finset.Ico (f + 1) l.length = Finset.Ico f l.length :=
        Finset.Ico_union_Ico_eq_Ico (by omega : f ≤ f + 1) (by omega : f + 1 ≤ l.length)
      have h3 : Finset.Ico f (f + 1) = {f} := Nat.Ico_succ_singleton f
      rw [Finset.range_eq_Ico, ← h1,
        Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive 0 f l.length), ← h2,
        Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive f (f + 1) l.length), h3,
        Finset.sum_singleton]
      ring
    rw [hsplit, hright, htotal, ← Finset.mul_sum]
    ring
  -- link to the big sum
  have hlink : ∑ i ∈ Finset.range l.length, x (l.getD i d).1 = ∑ j ∈ univ.erase k, x j := by
    rw [← list_sum_map_getD l d (fun a => x a.1), sorted_sum_eq hnodup htf]
  -- endpoint identification
  have hfirst : γ (l.getD 0 d).1 = gmin := by
    have e0 : l.getD 0 d = l.get ⟨0, by omega⟩ := List.getD_eq_getElem _ _ (by omega)
    rw [e0]
    apply le_antisymm
    · obtain ⟨i₀, hi₀k, hi₀⟩ := hgmin_mem
      have hi₀s : i₀ ∈ univ.erase k := mem_erase.2 ⟨hi₀k, mem_univ _⟩
      have hmem : (⟨i₀, hi₀s⟩ : {a // a ∈ univ.erase k}) ∈ l := by
        have h1 : (⟨i₀, hi₀s⟩ : {a // a ∈ univ.erase k}) ∈ l.toFinset := by
          rw [htf]
          exact Finset.mem_attach _ _
        exact List.mem_toFinset.1 h1
      have hle := hle_all _ hmem
      rw [hi₀] at hle
      exact hle
    · exact hgmin _ (mem_erase.1 (l.get ⟨0, by omega⟩).2).1
  have hlast : γ (l.getD (l.length - 1) d).1 = gmax := by
    have e1 : l.getD (l.length - 1) d = l.get ⟨l.length - 1, by omega⟩ :=
      List.getD_eq_getElem _ _ (by omega)
    rw [e1]
    apply le_antisymm
    · exact hgmax _ (mem_erase.1 (l.get ⟨l.length - 1, by omega⟩).2).1
    · obtain ⟨i₀, hi₀k, hi₀⟩ := hgmax_mem
      have hi₀s : i₀ ∈ univ.erase k := mem_erase.2 ⟨hi₀k, mem_univ _⟩
      have hmem : (⟨i₀, hi₀s⟩ : {a // a ∈ univ.erase k}) ∈ l := by
        have h1 : (⟨i₀, hi₀s⟩ : {a // a ∈ univ.erase k}) ∈ l.toFinset := by
          rw [htf]
          exact Finset.mem_attach _ _
        exact List.mem_toFinset.1 h1
      have hge := hge_all _ hmem
      rw [hi₀] at hge
      exact hge
  -- the missing term is small
  have h2x : 2 * x (l.getD f d).1
      ≤ (2 * ((∑ i ∈ Finset.range l.length, x (l.getD i d).1) - x (l.getD f d).1)) / ((n : ℝ) - 2) := by
    have hmin : ∀ b ∈ l, x (l.getD f d).1 ≤ x b.1 := by
      intro b hb
      rw [List.getD_eq_getElem _ _ (by omega : f < l.length)]
      exact hfx b hb
    have h2 : ((l.length : ℝ) - 1) * x (l.getD f d).1
        ≤ (∑ i ∈ Finset.range l.length, x (l.getD i d).1) - x (l.getD f d).1 := by
      have h3 : ∑ i ∈ Finset.range l.length, x (l.getD i d).1
          = ∑ i ∈ (Finset.range l.length).erase f, x (l.getD i d).1 + x (l.getD f d).1 :=
        (Finset.sum_erase_add _ _ (by
          rw [Finset.mem_range]; exact hflt)).symm
      have h4 : ∑ i ∈ (Finset.range l.length).erase f, x (l.getD i d).1
          ≥ ∑ i ∈ (Finset.range l.length).erase f, x (l.getD f d).1 := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_erase] at hi
        have hi' : i ≠ f ∧ i ∈ Finset.range l.length := hi
        have hthis : (l.getD i d) ∈ l := by
          rw [List.getD_eq_getElem _ _ (by rw [Finset.mem_range] at hi'; omega : i < l.length)]
          exact List.get_mem _ _
        exact hmin _ hthis
      rw [Finset.sum_const, Finset.card_erase_of_mem (by
        rw [Finset.mem_range]; exact hflt), Finset.card_range, nsmul_eq_mul,
        Nat.cast_sub (by omega : 1 ≤ l.length)] at h4
      push_cast at h4
      linarith [h3, h4]
    have h5 : (l.length : ℝ) - 1 = (n : ℝ) - 2 := by
      rw [hlen, Nat.cast_sub (by omega : 1 ≤ n)]
      ring
    have h6 : (0 : ℝ) < (n : ℝ) - 2 := by
      have h7 : (3:ℝ) ≤ n := by exact_mod_cast hn
      linarith
    rw [le_div_iff₀ h6, ← h5]
    linarith [h2]
  -- grand finale
  have h4 : 2 * ((∑ i ∈ Finset.range l.length, x (l.getD i d).1) - x (l.getD f d).1)
      < gmax - gmin := by
    rw [hcsum] at hassign
    linarith [hassign, hfirst, hlast]
  have h5 : (0 : ℝ) < (n : ℝ) - 2 := by
    have h7 : (3:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [← hlink]
  calc 2 * (∑ i ∈ Finset.range l.length, x (l.getD i d).1)
      = 2 * ((∑ i ∈ Finset.range l.length, x (l.getD i d).1) - x (l.getD f d).1)
        + 2 * x (l.getD f d).1 := by
        ring
    _ < (gmax - gmin) + (gmax - gmin) / ((n : ℝ) - 2) := by
      have h7 : 2 * x (l.getD f d).1 ≤ (gmax - gmin) / ((n : ℝ) - 2) := by
        have h10 : 2 * ((∑ i ∈ Finset.range l.length, x (l.getD i d).1) - x (l.getD f d).1)
            / ((n : ℝ) - 2) ≤ (gmax - gmin) / ((n : ℝ) - 2) := by
          apply div_le_div_of_nonneg_right
          · linarith [h4]
          · exact h5.le
        linarith [h2x, h10]
      linarith [h4, h7]
    _ = (gmax - gmin) * ((n : ℝ) - 1) / ((n : ℝ) - 2) := by
      field_simp [h5.ne']
      ring

/-- The inner product of `conj u` and `w` as a cosine of the direction difference. -/
lemma re_conj_eq (u w : ℂ) (hu : u ≠ 0) :
    (conj u * w).re = ‖u‖ * ‖w‖ * Real.cos (Complex.arg w - Complex.arg u) := by
  have e1 : conj u = ‖u‖ * Complex.exp (-(Complex.arg u * Complex.I)) := by
    have h1 : conj u = conj (‖u‖ * Complex.exp (Complex.arg u * Complex.I)) := by
      rw [Complex.norm_mul_exp_arg_mul_I]
    rw [h1, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
      Complex.conj_I]
    ring
  have e2 : conj u * w = ‖u‖ * ‖w‖ * Complex.exp ((Complex.arg w - Complex.arg u) * Complex.I) := by
    calc conj u * w = (‖u‖ * Complex.exp (-(Complex.arg u * Complex.I))) * w := by rw [e1]
      _ = (‖u‖ * Complex.exp (-(Complex.arg u * Complex.I))) *
          (‖w‖ * Complex.exp (Complex.arg w * Complex.I)) := by
        rw [Complex.norm_mul_exp_arg_mul_I]
      _ = ‖u‖ * ‖w‖ * Complex.exp ((Complex.arg w - Complex.arg u) * Complex.I) := by
        rw [show (Complex.arg w - Complex.arg u) * Complex.I
            = Complex.arg w * Complex.I + (-(Complex.arg u * Complex.I)) by ring]
        rw [Complex.exp_add]
        ring
  have e3 : (Complex.exp ((Complex.arg w - Complex.arg u) * Complex.I)).re
      = Real.cos (Complex.arg w - Complex.arg u) := by
    rw [Complex.exp_mul_I]
    simp only [← Complex.ofReal_sub, Complex.cos_ofReal_re, Complex.cos_ofReal_im,
      Complex.sin_ofReal_re, Complex.sin_ofReal_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.neg_re]
    ring
  rw [e2]
  rw [show (↑‖u‖ * ↑‖w‖ * Complex.exp ((Complex.arg w - Complex.arg u) * Complex.I)).re
      = ‖u‖ * ‖w‖ * (Complex.exp ((Complex.arg w - Complex.arg u) * Complex.I)).re by
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]]
  rw [e3]

/-- At a vertex with witnessing normal `u`, the directions from `O k` to the other
centres all lie in the open semicircle of directions `arg u ± π/2`. -/
lemma vertex_arg_window {k : Fin n} {u : ℂ} (hu0 : u ≠ 0)
    (hu : ∀ j, j ≠ k → 0 < (conj u * (O j - O k)).re) {j : Fin n} (hjk : j ≠ k)
    (hw : O j - O k ≠ 0) :
    toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (O j - O k)) ∈
      Set.Ioo (Complex.arg u - Real.pi / 2) (Complex.arg u + Real.pi / 2) := by
  have hcos : 0 < Real.cos (Complex.arg (O j - O k) - Complex.arg u) := by
    have h1 : 0 < ‖u‖ * ‖O j - O k‖ := mul_pos (norm_pos_iff.mpr hu0) (norm_pos_iff.mpr hw)
    have h2 : 0 < ‖u‖ * ‖O j - O k‖ * Real.cos (Complex.arg (O j - O k) - Complex.arg u) := by
      rw [← re_conj_eq u (O j - O k) hu0]
      exact hu j hjk
    exact (mul_pos_iff_of_pos_left h1).mp h2
  set α := toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (O j - O k)) with hα
  have hmem : α ∈ Set.Ioc (Complex.arg u - Real.pi / 2) (Complex.arg u - Real.pi / 2 + 2 * Real.pi) :=
    toIocMod_mem_Ioc Real.two_pi_pos _ _
  have hper : Real.cos (Complex.arg (O j - O k) - Complex.arg u) = Real.cos (α - Complex.arg u) := by
    have h1 : ((Complex.arg (O j - O k) - Complex.arg u : ℝ) : Real.Angle)
        = ((α - Complex.arg u : ℝ) : Real.Angle) := by
      rw [hα, Real.Angle.coe_sub, Real.Angle.coe_sub,
        Real.Angle.coe_toIocMod (Complex.arg (O j - O k)) (Complex.arg u - Real.pi / 2)]
    rw [← Real.Angle.cos_coe, ← Real.Angle.cos_coe, h1]
  have hlt : α < Complex.arg u + Real.pi / 2 := by
    by_contra hge
    push Not at hge
    have hge2 : Real.pi / 2 ≤ α - Complex.arg u := by linarith [hge]
    have hle2 : α - Complex.arg u ≤ Real.pi + Real.pi / 2 := by
      have h1 := hmem.2
      linarith
    have hcle : Real.cos (α - Complex.arg u) ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le hge2 hle2
    linarith [hcle, hcos, hper]
  exact ⟨hmem.1, hlt⟩

/-- The argument of the ratio equals the difference of the `toIocMod` representatives
as a `Real.Angle`. -/
lemma vertex_arg_ratio {k : Fin n} {u : ℂ} (i j : Fin n)
    (hi0 : O i - O k ≠ 0) (hj0 : O j - O k ≠ 0) :
    (Complex.arg ((O i - O k) / (O j - O k)) : Real.Angle) =
      ((toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (O i - O k)) -
        toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (O j - O k))) : ℝ) := by
  rw [Complex.arg_div_coe_angle hi0 hj0, ← Real.Angle.coe_toIocMod
    (Complex.arg (O i - O k)) (Complex.arg u - Real.pi / 2),
    ← Real.Angle.coe_toIocMod (Complex.arg (O j - O k)) (Complex.arg u - Real.pi / 2),
    Real.Angle.coe_sub]

/-- At a vertex, the angle between two rays equals the absolute difference of the
`toIocMod` representatives. -/
lemma vertex_uangle_eq (hn : 3 ≤ n) (hlines : NoLineMeetsThree O) {k : Fin n}
    {u : ℂ} (hu0 : u ≠ 0)
    (hu : ∀ j, j ≠ k → 0 < (conj u * (O j - O k)).re) (i j : Fin n)
    (hik : i ≠ k) (hjk : j ≠ k) :
    uangle (O i - O k) (O j - O k) =
      |toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (O i - O k)) -
        toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (O j - O k))| := by
  have hi0 : O i - O k ≠ 0 := by
    have h2 := two_lt_dist hn hlines hik
    by_contra h
    rw [h, norm_zero] at h2
    linarith
  have hj0 : O j - O k ≠ 0 := by
    have h2 := two_lt_dist hn hlines hjk
    by_contra h
    rw [h, norm_zero] at h2
    linarith
  have hmem_i := vertex_arg_window hu0 hu hik hi0
  have hmem_j := vertex_arg_window hu0 hu hjk hj0
  have hratio := vertex_arg_ratio (k := k) (u := u) i j hi0 hj0
  set αi := toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (O i - O k)) with hαi
  set αj := toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (O j - O k)) with hαj
  have h4 : toIocMod Real.two_pi_pos (-Real.pi) (αi - αj) = αi - αj := by
    rw [toIocMod_eq_self]
    constructor
    · have h1 := hmem_j.2
      have h2 := hmem_i.1
      linarith
    · have h1 := hmem_i.2
      have h2 := hmem_j.1
      linarith
  have e4 : Complex.arg ((O i - O k) / (O j - O k)) = αi - αj := by
    obtain ⟨m, hm⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 hratio
    have h2 : toIocMod Real.two_pi_pos (-Real.pi) (Complex.arg ((O i - O k) / (O j - O k)))
        = toIocMod Real.two_pi_pos (-Real.pi) (αi - αj) := by
      have e : Complex.arg ((O i - O k) / (O j - O k)) = (αi - αj) + m • (2 * Real.pi) := by
        rw [zsmul_eq_mul]
        linarith [hm]
      rw [e, toIocMod_add_zsmul]
    have h3 : toIocMod Real.two_pi_pos (-Real.pi) (Complex.arg ((O i - O k) / (O j - O k)))
        = Complex.arg ((O i - O k) / (O j - O k)) := by
      rw [toIocMod_eq_self Real.two_pi_pos]
      exact ⟨Complex.neg_pi_lt_arg _, by linarith [Complex.arg_le_pi ((O i - O k) / (O j - O k))]⟩
    rw [← h3, h2, h4]
  rw [uangle, e4]

/-- `t ≤ arcsin t` for `t ∈ [0, 1]`. -/
lemma arcsin_self_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : t ≤ Real.arcsin t := by
  have h3 : Real.sin (Real.arcsin t) = t := Real.sin_arcsin (by linarith) ht1
  have h4 : 0 ≤ Real.arcsin t := Real.arcsin_nonneg.2 ht0
  calc t = Real.sin (Real.arcsin t) := h3.symm
    _ ≤ Real.arcsin t := Real.sin_le h4

/-- `t < arcsin t` for `t ∈ (0, 1]`. -/
lemma arcsin_self_lt {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) : t < Real.arcsin t := by
  have h3 : Real.sin (Real.arcsin t) = t := Real.sin_arcsin (by linarith) ht1
  have h4 : 0 < Real.arcsin t := Real.arcsin_pos.2 ht0
  calc t = Real.sin (Real.arcsin t) := h3.symm
    _ < Real.arcsin t := Real.sin_lt h4

/-- The `mod 2π` representatives of the directions from a vertex are distinct. -/
lemma vertex_alpha_distinct (hn : 3 ≤ n) (hlines : NoLineMeetsThree O) {k : Fin n}
    {u : ℂ} (i j : Fin n) (hi : i ≠ k) (hj : j ≠ k) (hij : i ≠ j) :
    toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (O i - O k)) ≠
      toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (O j - O k)) := by
  intro h
  have h1 := arg_toIocMod_ne hn hlines hi.symm hj.symm hij
  have e1 := toIocMod_add_toIocDiv_zsmul Real.two_pi_pos (Complex.arg u - Real.pi / 2)
    (Complex.arg (O i - O k))
  have e2 := toIocMod_add_toIocDiv_zsmul Real.two_pi_pos (Complex.arg u - Real.pi / 2)
    (Complex.arg (O j - O k))
  rw [h] at e1
  set α := toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (O j - O k)) with hα
  set m1 := toIocDiv Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (O i - O k)) with hm1
  set m2 := toIocDiv Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (O j - O k)) with hm2
  have h2 : toIocMod Real.pi_pos 0 (Complex.arg (O i - O k))
      = toIocMod Real.pi_pos 0 (Complex.arg (O j - O k)) := by
    rw [← e1, ← e2,
      show (m1 • (2 * Real.pi)) = (2 * m1) • Real.pi by rw [zsmul_eq_mul, zsmul_eq_mul]; push_cast; ring,
      show (m2 • (2 * Real.pi)) = (2 * m2) • Real.pi by rw [zsmul_eq_mul, zsmul_eq_mul]; push_cast; ring,
      toIocMod_add_zsmul, toIocMod_add_zsmul]
  exact h1 h2

/-- The strong gap bound at a vertex. -/
lemma vertex_gap_strong (hn : 3 ≤ n) (hlines : NoLineMeetsThree O) {k : Fin n}
    {u : ℂ} (hu0 : u ≠ 0)
    (hu : ∀ j, j ≠ k → 0 < (conj u * (O j - O k)).re) (i j : Fin n)
    (hi : i ≠ k) (hj : j ≠ k) (hij : i ≠ j)
    (hlt : toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (O i - O k)) <
      toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (O j - O k))) :
    2 * (1 / ‖O i - O k‖) <
      toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (O j - O k)) -
        toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (O i - O k)) ∧
    2 * (1 / ‖O j - O k‖) <
      toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (O j - O k)) -
        toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (O i - O k)) := by
  have hgap_eq : toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (O j - O k)) -
        toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (O i - O k))
      = uangle (O i - O k) (O j - O k) := by
    rw [vertex_uangle_eq hn hlines hu0 hu i j hi hj, abs_sub_comm,
      abs_of_pos (sub_pos.mpr hlt)]
  have hd1 : 2 < ‖O i - O k‖ := two_lt_dist hn hlines hi
  have hd2 : 2 < ‖O j - O k‖ := two_lt_dist hn hlines hj
  have hstrong := strong_angle hn hlines hi.symm hj.symm hij
  have hmin2 : 2 < min ‖O i - O k‖ ‖O j - O k‖ := lt_min hd1 hd2
  have hmin20 : 0 < min ‖O i - O k‖ ‖O j - O k‖ := by linarith
  have ht0 : (0:ℝ) < 2 / min ‖O i - O k‖ ‖O j - O k‖ := by positivity
  have ht1 : 2 / min ‖O i - O k‖ ‖O j - O k‖ < 1 := by
    rw [div_lt_one₀ hmin20]
    exact hmin2
  have hstrong2 : 2 / min ‖O i - O k‖ ‖O j - O k‖ < uangle (O i - O k) (O j - O k) :=
    lt_of_lt_of_le (arcsin_self_lt ht0 ht1.le) hstrong
  constructor
  · calc 2 * (1 / ‖O i - O k‖) = 2 / ‖O i - O k‖ := by ring
      _ ≤ 2 / min ‖O i - O k‖ ‖O j - O k‖ := by
        have h1 := one_div_le_one_div_of_le hmin20 (min_le_left _ _)
        have h2 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ) ≤ 2)
        rw [show (2:ℝ) / ‖O i - O k‖ = 2 * (1 / ‖O i - O k‖) by ring,
          show (2:ℝ) / min ‖O i - O k‖ ‖O j - O k‖ = 2 * (1 / min ‖O i - O k‖ ‖O j - O k‖) by
            ring]
        exact h2
      _ < toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (O j - O k)) -
          toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (O i - O k)) := by
        rw [hgap_eq]
        exact hstrong2
  · calc 2 * (1 / ‖O j - O k‖) = 2 / ‖O j - O k‖ := by ring
      _ ≤ 2 / min ‖O i - O k‖ ‖O j - O k‖ := by
        have h1 := one_div_le_one_div_of_le hmin20 (min_le_right _ _)
        have h2 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ) ≤ 2)
        rw [show (2:ℝ) / ‖O j - O k‖ = 2 * (1 / ‖O j - O k‖) by ring,
          show (2:ℝ) / min ‖O i - O k‖ ‖O j - O k‖ = 2 * (1 / min ‖O i - O k‖ ‖O j - O k‖) by
            ring]
        exact h2
      _ < toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (O j - O k)) -
          toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (O i - O k)) := by
        rw [hgap_eq]
        exact hstrong2

/-- At a vertex, the spread of the directions equals the `spread` of the configuration. -/
lemma spread_eq_vertex (hn : 3 ≤ n) (hlines : NoLineMeetsThree O) {k : Fin n}
    {u : ℂ} (hu0 : u ≠ 0)
    (hu : ∀ j, j ≠ k → 0 < (conj u * (O j - O k)).re) :
    ∃ gmin gmax : ℝ,
      (∀ j : Fin n, j ≠ k → gmin ≤ toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2)
          (Complex.arg (O j - O k))) ∧
      (∀ j : Fin n, j ≠ k → toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2)
          (Complex.arg (O j - O k)) ≤ gmax) ∧
      (∃ i : Fin n, i ≠ k ∧ toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2)
          (Complex.arg (O i - O k)) = gmin) ∧
      (∃ i : Fin n, i ≠ k ∧ toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2)
          (Complex.arg (O i - O k)) = gmax) ∧
      spread O k = gmax - gmin := by
  set s : Finset (Fin n) := univ.erase k with hs
  set α : Fin n → ℝ := fun j => toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2)
    (Complex.arg (O j - O k)) with hα
  set img := s.image α with himg
  have hne : s.Nonempty := by
    apply Finset.card_pos.mp
    rw [hs, Finset.card_erase_of_mem (mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  have himg_ne : img.Nonempty := Finset.Nonempty.image hne _
  have hmin_le_max : img.min' himg_ne ≤ img.max' himg_ne :=
    Finset.min'_le img (img.max' himg_ne) (Finset.max'_mem _ _)
  refine ⟨img.min' himg_ne, img.max' himg_ne, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    exact Finset.min'_le img _ (Finset.mem_image.2 ⟨j, mem_erase.2 ⟨hj, mem_univ _⟩, rfl⟩)
  · intro j hj
    exact Finset.le_max' img _ (Finset.mem_image.2 ⟨j, mem_erase.2 ⟨hj, mem_univ _⟩, rfl⟩)
  · obtain ⟨g, hg_mem, hg_eq⟩ := Finset.mem_image.1 (Finset.min'_mem img himg_ne)
    exact ⟨g, (mem_erase.1 hg_mem).1, hg_eq⟩
  · obtain ⟨g, hg_mem, hg_eq⟩ := Finset.mem_image.1 (Finset.max'_mem img himg_ne)
    exact ⟨g, (mem_erase.1 hg_mem).1, hg_eq⟩
  · -- spread = max' − min'
    have h_bdd : BddAbove (Set.range fun p : Fin n × Fin n => uangle (O p.1 - O k) (O p.2 - O k)) := by
      refine ⟨Real.pi, ?_⟩
      intro y hy
      obtain ⟨p, hp⟩ := hy
      rw [← hp]
      exact (uangle_mem_Icc _ _).2
    apply le_antisymm
    · apply csSup_le
      · exact ⟨uangle (O k - O k) (O k - O k), Set.mem_range_self (k, k)⟩
      · intro y hy
        obtain ⟨⟨i, j⟩, rfl⟩ := hy
        show uangle (O i - O k) (O j - O k) ≤ img.max' himg_ne - img.min' himg_ne
        by_cases hik : i = k
        · rw [hik]
          rw [show O k - O k = 0 by ring]
          have h1 : uangle 0 (O j - O k) = 0 := by
            rw [uangle, zero_div, Complex.arg_zero, abs_zero]
          rw [h1]
          linarith [hmin_le_max]
        by_cases hjk : j = k
        · rw [hjk]
          rw [show O k - O k = 0 by ring]
          have h1 : uangle (O i - O k) 0 = 0 := by
            rw [uangle, div_zero, Complex.arg_zero, abs_zero]
          rw [h1]
          linarith [hmin_le_max]
        · rw [vertex_uangle_eq hn hlines hu0 hu i j hik hjk]
          have hi_mem : α i ∈ img := Finset.mem_image.2 ⟨i, mem_erase.2 ⟨hik, mem_univ _⟩, rfl⟩
          have hj_mem : α j ∈ img := Finset.mem_image.2 ⟨j, mem_erase.2 ⟨hjk, mem_univ _⟩, rfl⟩
          have h1 := Finset.min'_le img _ hi_mem
          have h2 := Finset.le_max' img _ hj_mem
          have h3 := Finset.min'_le img _ hj_mem
          have h4 := Finset.le_max' img _ hi_mem
          rw [abs_le]
          constructor <;> linarith
    · apply le_csSup
      · exact h_bdd
      · obtain ⟨i₁, hi₁k, hi₁⟩ := (show ∃ i : Fin n, i ≠ k ∧
            toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (O i - O k))
              = img.min' himg_ne from by
          obtain ⟨g, hg_mem, hg_eq⟩ := Finset.mem_image.1 (Finset.min'_mem img himg_ne)
          exact ⟨g, (mem_erase.1 hg_mem).1, hg_eq⟩)
        obtain ⟨i₂, hi₂k, hi₂⟩ := (show ∃ i : Fin n, i ≠ k ∧
            toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (O i - O k))
              = img.max' himg_ne from by
          obtain ⟨g, hg_mem, hg_eq⟩ := Finset.mem_image.1 (Finset.max'_mem img himg_ne)
          exact ⟨g, (mem_erase.1 hg_mem).1, hg_eq⟩)
        have heq : uangle (O i₁ - O k) (O i₂ - O k) = img.max' himg_ne - img.min' himg_ne := by
          rw [vertex_uangle_eq hn hlines hu0 hu i₁ i₂ hi₁k hi₂k]
          rw [hi₁, hi₂, abs_sub_comm, abs_of_nonneg (by linarith [hmin_le_max])]
        rw [← heq]
        exact Set.mem_range_self (i₁, i₂)

/-- Row bound at a vertex (kalva's convex-hull-vertex bound). -/
lemma row_bound_vertex (hn : 3 ≤ n) (hlines : NoLineMeetsThree O) {k : Fin n}
    (hk : IsVertex O k) :
    2 * (∑ j ∈ univ.erase k, 1 / ‖O j - O k‖) < spread O k * ((n : ℝ) - 1) / ((n : ℝ) - 2) := by
  obtain ⟨u, hu0, hu⟩ := hk
  obtain ⟨gmin, gmax, hgmin, hgmax, hgmin_mem, hgmax_mem, hspread⟩ :=
    spread_eq_vertex hn hlines hu0 hu
  rw [hspread]
  apply row_bound_vertex_mock (γ := fun j => toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2)
      (Complex.arg (O j - O k))) (x := fun j => 1 / ‖O j - O k‖) hn
  · exact vertex_alpha_distinct hn hlines
  · exact vertex_gap_strong hn hlines hu0 hu
  · intro j hj
    have h2 := two_lt_dist hn hlines hj
    positivity
  · exact hgmin
  · exact hgmax
  · exact hgmin_mem
  · exact hgmax_mem

/-- The 2D cross product (signed area) of two complex numbers. -/
noncomputable def cross (x y : ℂ) : ℝ := (conj x * y).im

/-- `cross` in terms of real and imaginary parts. -/
lemma cross_eq_re_im (x y : ℂ) : cross x y = x.re * y.im - x.im * y.re := by
  rw [cross, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- The imaginary part of a quotient as a cross product. -/
lemma im_div_eq_cross_div_normSq (x y : ℂ) : (y / x).im = cross x y / Complex.normSq x := by
  rw [Complex.div_im, ← sub_div, cross_eq_re_im]
  congr 1
  ring

lemma cross_self (x : ℂ) : cross x x = 0 := by
  rw [cross_eq_re_im]
  ring

lemma cross_qp_rp (p q r : ℂ) : cross (q - p) (r - p) = cross (r - q) (p - q) := by
  simp only [cross_eq_re_im, Complex.sub_re, Complex.sub_im]
  ring

lemma cross_rp_pr (p q r : ℂ) : cross (q - p) (r - p) = cross (p - r) (q - r) := by
  simp only [cross_eq_re_im, Complex.sub_re, Complex.sub_im]
  ring

lemma cos_uangle (x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) :
    Real.cos (uangle x y) = (x / y).re / ‖x / y‖ := by
  rw [uangle, Real.cos_abs, Complex.cos_arg (div_ne_zero hx hy)]

lemma triangle_uangle_sum {p q r : ℂ} (h : cross (q - p) (r - p) ≠ 0) :
    uangle (q - p) (r - p) + uangle (p - q) (r - q) + uangle (p - r) (q - r) = Real.pi := by
  have hqp : q - p ≠ 0 := fun hq => h (by rw [hq]; simp [cross])
  have hrp : r - p ≠ 0 := fun hr => h (by rw [hr]; simp [cross])
  have hrq : r - q ≠ 0 := fun hr => h ((cross_qp_rp p q r).trans (by rw [hr]; simp [cross]))
  have hpq : p - q ≠ 0 := fun hq => h ((cross_qp_rp p q r).trans (by rw [hq]; simp [cross]))
  have hpr : p - r ≠ 0 := fun hr => h ((cross_rp_pr p q r).trans (by rw [hr]; simp [cross]))
  have hqr : q - r ≠ 0 := fun hr => h ((cross_rp_pr p q r).trans (by rw [hr]; simp [cross]))
  have hρ1 : (r - p) / (q - p) ≠ 0 := div_ne_zero hrp hqp
  have hρ2 : (p - q) / (r - q) ≠ 0 := div_ne_zero hpq hrq
  have hρ3 : (q - r) / (p - r) ≠ 0 := div_ne_zero hqr hpr
  have hprod : (r - p) / (q - p) * ((p - q) / (r - q)) * ((q - r) / (p - r)) = -1 := by
    field_simp
    ring
  have hs : ((Complex.arg ((r - p) / (q - p)) + Complex.arg ((p - q) / (r - q)) +
        Complex.arg ((q - r) / (p - r)) : ℝ) : Real.Angle) = ((Real.pi : ℝ) : Real.Angle) := by
    rw [Real.Angle.coe_add, Real.Angle.coe_add,
      ← Complex.arg_mul_coe_angle hρ1 hρ2,
      ← Complex.arg_mul_coe_angle (mul_ne_zero hρ1 hρ2) hρ3,
      hprod, Complex.arg_neg_one]
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 hs
  rcases lt_or_gt_of_ne h with hneg | hpos
  · have him1 : ((r - p) / (q - p)).im < 0 := by
      rw [im_div_eq_cross_div_normSq]
      exact div_neg_of_neg_of_pos hneg (Complex.normSq_pos.2 hqp)
    have him2 : ((p - q) / (r - q)).im < 0 := by
      rw [im_div_eq_cross_div_normSq, ← cross_qp_rp]
      exact div_neg_of_neg_of_pos hneg (Complex.normSq_pos.2 hrq)
    have him3 : ((q - r) / (p - r)).im < 0 := by
      rw [im_div_eq_cross_div_normSq, ← cross_rp_pr]
      exact div_neg_of_neg_of_pos hneg (Complex.normSq_pos.2 hpr)
    have ha1 : Complex.arg ((r - p) / (q - p)) < 0 := Complex.arg_neg_iff.2 him1
    have ha2 : Complex.arg ((p - q) / (r - q)) < 0 := Complex.arg_neg_iff.2 him2
    have ha3 : Complex.arg ((q - r) / (p - r)) < 0 := Complex.arg_neg_iff.2 him3
    have hb1 : -Real.pi < Complex.arg ((r - p) / (q - p)) := Complex.neg_pi_lt_arg _
    have hb2 : -Real.pi < Complex.arg ((p - q) / (r - q)) := Complex.neg_pi_lt_arg _
    have hb3 : -Real.pi < Complex.arg ((q - r) / (p - r)) := Complex.neg_pi_lt_arg _
    have hu1 : uangle (q - p) (r - p) = -Complex.arg ((r - p) / (q - p)) := by
      rw [uangle, show (q - p) / (r - p) = ((r - p) / (q - p))⁻¹ by rw [inv_div],
        Complex.abs_arg_inv, abs_of_neg ha1]
    have hu2 : uangle (p - q) (r - q) = -Complex.arg ((p - q) / (r - q)) := by
      rw [uangle, abs_of_neg ha2]
    have hu3 : uangle (p - r) (q - r) = -Complex.arg ((q - r) / (p - r)) := by
      rw [uangle, show (p - r) / (q - r) = ((q - r) / (p - r))⁻¹ by rw [inv_div],
        Complex.abs_arg_inv, abs_of_neg ha3]
    have hs0 : Complex.arg ((r - p) / (q - p)) + Complex.arg ((p - q) / (r - q)) +
        Complex.arg ((q - r) / (p - r)) < 0 := add_neg (add_neg ha1 ha2) ha3
    have hs3 : -(3 * Real.pi) < Complex.arg ((r - p) / (q - p)) +
        Complex.arg ((p - q) / (r - q)) + Complex.arg ((q - r) / (p - r)) := by
      linarith [hb1, hb2, hb3, Real.pi_pos]
    have hk1 : (k : ℝ) < 0 := by
      have h1 : (2 : ℝ) * Real.pi * (k : ℝ) < 2 * Real.pi * (0 : ℝ) := by
        rw [← hk]
        linarith [Real.pi_pos, hs0]
      exact (mul_lt_mul_iff_of_pos_left Real.two_pi_pos).1 h1
    have hk2 : (-2 : ℝ) < (k : ℝ) := by
      have h2 : (2 : ℝ) * Real.pi * (-2 : ℝ) < 2 * Real.pi * (k : ℝ) := by
        rw [← hk]
        linarith [Real.pi_pos, hs3]
      exact (mul_lt_mul_iff_of_pos_left Real.two_pi_pos).1 h2
    have hkz : k = -1 := by
      have h1 : k < (0 : ℤ) := by exact_mod_cast hk1
      have h2 : (-2 : ℤ) < k := by exact_mod_cast hk2
      omega
    rw [hu1, hu2, hu3]
    rw [hkz, Int.cast_neg, Int.cast_one] at hk
    linarith [Real.pi_pos]
  · have him1 : 0 < ((r - p) / (q - p)).im := by
      rw [im_div_eq_cross_div_normSq]
      exact div_pos hpos (Complex.normSq_pos.2 hqp)
    have him2 : 0 < ((p - q) / (r - q)).im := by
      rw [im_div_eq_cross_div_normSq, ← cross_qp_rp]
      exact div_pos hpos (Complex.normSq_pos.2 hrq)
    have him3 : 0 < ((q - r) / (p - r)).im := by
      rw [im_div_eq_cross_div_normSq, ← cross_rp_pr]
      exact div_pos hpos (Complex.normSq_pos.2 hpr)
    have ha1 : 0 < Complex.arg ((r - p) / (q - p)) := by
      rw [lt_iff_le_and_ne]
      exact ⟨Complex.arg_nonneg_iff.2 him1.le,
        fun hz => ne_of_gt him1 (Complex.arg_eq_zero_iff.1 hz.symm).2⟩
    have ha2 : 0 < Complex.arg ((p - q) / (r - q)) := by
      rw [lt_iff_le_and_ne]
      exact ⟨Complex.arg_nonneg_iff.2 him2.le,
        fun hz => ne_of_gt him2 (Complex.arg_eq_zero_iff.1 hz.symm).2⟩
    have ha3 : 0 < Complex.arg ((q - r) / (p - r)) := by
      rw [lt_iff_le_and_ne]
      exact ⟨Complex.arg_nonneg_iff.2 him3.le,
        fun hz => ne_of_gt him3 (Complex.arg_eq_zero_iff.1 hz.symm).2⟩
    have hb1 : Complex.arg ((r - p) / (q - p)) < Real.pi := by
      rw [lt_iff_le_and_ne]
      exact ⟨Complex.arg_le_pi _,
        fun hz => ne_of_gt him1 (Complex.arg_eq_pi_iff.1 hz).2⟩
    have hb2 : Complex.arg ((p - q) / (r - q)) < Real.pi := by
      rw [lt_iff_le_and_ne]
      exact ⟨Complex.arg_le_pi _,
        fun hz => ne_of_gt him2 (Complex.arg_eq_pi_iff.1 hz).2⟩
    have hb3 : Complex.arg ((q - r) / (p - r)) < Real.pi := by
      rw [lt_iff_le_and_ne]
      exact ⟨Complex.arg_le_pi _,
        fun hz => ne_of_gt him3 (Complex.arg_eq_pi_iff.1 hz).2⟩
    have hu1 : uangle (q - p) (r - p) = Complex.arg ((r - p) / (q - p)) := by
      rw [uangle, show (q - p) / (r - p) = ((r - p) / (q - p))⁻¹ by rw [inv_div],
        Complex.abs_arg_inv, abs_of_pos ha1]
    have hu2 : uangle (p - q) (r - q) = Complex.arg ((p - q) / (r - q)) := by
      rw [uangle, abs_of_pos ha2]
    have hu3 : uangle (p - r) (q - r) = Complex.arg ((q - r) / (p - r)) := by
      rw [uangle, show (p - r) / (q - r) = ((q - r) / (p - r))⁻¹ by rw [inv_div],
        Complex.abs_arg_inv, abs_of_pos ha3]
    have hs0 : 0 < Complex.arg ((r - p) / (q - p)) + Complex.arg ((p - q) / (r - q)) +
        Complex.arg ((q - r) / (p - r)) := add_pos (add_pos ha1 ha2) ha3
    have hs3 : Complex.arg ((r - p) / (q - p)) + Complex.arg ((p - q) / (r - q)) +
        Complex.arg ((q - r) / (p - r)) < 3 * Real.pi := by
      linarith [hb1, hb2, hb3, Real.pi_pos]
    have hk1 : (k : ℝ) < 1 := by
      have h1 : (2 : ℝ) * Real.pi * (k : ℝ) < 2 * Real.pi * (1 : ℝ) := by
        rw [← hk]
        linarith [Real.pi_pos, hs3]
      exact (mul_lt_mul_iff_of_pos_left Real.two_pi_pos).1 h1
    have hk2 : (-1 : ℝ) < (k : ℝ) := by
      have h2 : (2 : ℝ) * Real.pi * (-1 : ℝ) < 2 * Real.pi * (k : ℝ) := by
        rw [← hk]
        linarith [Real.pi_pos, hs0]
      exact (mul_lt_mul_iff_of_pos_left Real.two_pi_pos).1 h2
    have hkz : k = 0 := by
      have h1 : k < (1 : ℤ) := by exact_mod_cast hk1
      have h2 : (-1 : ℤ) < k := by exact_mod_cast hk2
      omega
    rw [hu1, hu2, hu3]
    rw [hkz, Int.cast_zero, mul_zero] at hk
    linarith [Real.pi_pos]

/-- If `|2π * m| < 2π` for `m : ℤ`, then `m = 0`. -/
lemma int_eq_zero_of_abs_two_pi_mul_lt (m : ℤ) (h : |2 * Real.pi * m| < 2 * Real.pi) : m = 0 := by
  have h1 : |Real.pi * (m : ℝ)| < Real.pi := by
    have h2 : |2 * Real.pi * (m : ℝ)| = 2 * |Real.pi * (m : ℝ)| := by
      rw [show 2 * Real.pi * (m : ℝ) = 2 * (Real.pi * (m : ℝ)) by ring, abs_mul]
      norm_num
    rw [h2] at h
    linarith [h, Real.pi_pos]
  have h3 : |Real.pi * (m : ℝ)| = Real.pi * |(m : ℝ)| := by
    rw [abs_mul, abs_of_nonneg Real.pi_pos.le]
  rw [h3] at h1
  have h4 : |(m : ℝ)| < 1 := by
    have h5 : Real.pi * |(m : ℝ)| < Real.pi * 1 := by simpa using h1
    exact lt_of_mul_lt_mul_left h5 Real.pi_pos.le
  have h6 : |m| < 1 := by exact_mod_cast h4
  rw [abs_lt] at h6
  omega

/-- `y` is strictly to the left of the directed ray from `p` to `q` iff the direction
from `q` to `y` lies in the open semicircle starting at the direction from `p` to `q`. -/
lemma left_iff_arg_window (p q y : ℂ) (hpq : q ≠ p) (hyq : y ≠ q) (hyp : y ≠ p) :
    0 < cross (q - p) (y - p) ↔
      toIocMod Real.two_pi_pos (Complex.arg (q - p)) (Complex.arg (y - q)) ∈
        Set.Ioo (Complex.arg (q - p)) (Complex.arg (q - p) + Real.pi) := by
  have e1 : (y - q) / (q - p) = (y - p) / (q - p) - 1 := by
    field_simp [sub_ne_zero.mpr hpq]
    ring
  have him : ((y - q) / (q - p)).im = ((y - p) / (q - p)).im := by
    rw [e1]
    simp
  have h1 : 0 < cross (q - p) (y - p) ↔ 0 < ((y - p) / (q - p)).im := by
    rw [im_div_eq_cross_div_normSq]
    have hn : 0 < Complex.normSq (q - p) := Complex.normSq_pos.2 (sub_ne_zero.mpr hpq)
    constructor
    · intro h
      exact div_pos h hn
    · intro h
      have h6 := (lt_div_iff₀ hn).mp h
      simpa using h6
  have h2 : 0 < ((y - q) / (q - p)).im ↔ Complex.arg ((y - q) / (q - p)) ∈ Set.Ioo 0 Real.pi := by
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · rw [lt_iff_le_and_ne]
        exact ⟨Complex.arg_nonneg_iff.2 h.le, fun hz => ne_of_gt h (Complex.arg_eq_zero_iff.1 hz.symm).2⟩
      · rw [lt_iff_le_and_ne]
        exact ⟨Complex.arg_le_pi _, fun hz => ne_of_gt h (Complex.arg_eq_pi_iff.1 hz).2⟩
    · intro h
      by_contra him0
      push Not at him0
      rcases lt_or_eq_of_le him0 with him3 | him3
      · have h6 := Complex.arg_neg_iff.2 him3
        linarith [h.1, h6]
      · have h7 : 0 ≤ ((y - q) / (q - p)).re ∨ ((y - q) / (q - p)).re < 0 := le_or_gt _ _
        rcases h7 with h7 | h7
        · have h8 := (Complex.arg_eq_zero_iff).2 ⟨h7, him3⟩
          linarith [h.1, h8]
        · have h8 := (Complex.arg_eq_pi_iff).2 ⟨h7, him3⟩
          linarith [h.2, h8]
  -- the ratio's arg equals the shifted representative of the difference
  have h3 : toIocMod Real.two_pi_pos (-Real.pi) (Complex.arg (y - q) - Complex.arg (q - p))
      = Complex.arg ((y - q) / (q - p)) := by
    have h1 : (Complex.arg ((y - q) / (q - p)) : Real.Angle)
        = ((Complex.arg (y - q) - Complex.arg (q - p) : ℝ) : Real.Angle) := by
      rw [Complex.arg_div_coe_angle (sub_ne_zero.mpr hyq) (sub_ne_zero.mpr hpq),
        Real.Angle.coe_sub]
    have h4 : toIocMod Real.two_pi_pos (-Real.pi) (Complex.arg (y - q) - Complex.arg (q - p))
        = toIocMod Real.two_pi_pos (-Real.pi) (Complex.arg ((y - q) / (q - p))) := by
      obtain ⟨m, hm⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 h1
      rw [show Complex.arg ((y - q) / (q - p))
          = (Complex.arg (y - q) - Complex.arg (q - p)) + m • (2 * Real.pi) by
        rw [zsmul_eq_mul]
        linarith [hm]]
      rw [toIocMod_add_zsmul]
    rw [h4, toIocMod_eq_self Real.two_pi_pos]
    exact ⟨Complex.neg_pi_lt_arg _, by linarith [Complex.arg_le_pi ((y - q) / (q - p))]⟩
  -- toIocMod with anchor `c` of `x` equals `c + toIocMod` with anchor `0` of `x - c`
  have hshift : toIocMod Real.two_pi_pos (Complex.arg (q - p)) (Complex.arg (y - q))
      = Complex.arg (q - p) +
        toIocMod Real.two_pi_pos 0 (Complex.arg (y - q) - Complex.arg (q - p)) := by
    have hmem := toIocMod_mem_Ioc Real.two_pi_pos (Complex.arg (q - p)) (Complex.arg (y - q))
    have hmem0 := toIocMod_mem_Ioc Real.two_pi_pos 0 (Complex.arg (y - q) - Complex.arg (q - p))
    have hclass : ((toIocMod Real.two_pi_pos (Complex.arg (q - p)) (Complex.arg (y - q)) : ℝ) : Real.Angle)
        = ((Complex.arg (q - p) +
          toIocMod Real.two_pi_pos 0 (Complex.arg (y - q) - Complex.arg (q - p))) : ℝ) := by
      rw [Real.Angle.coe_toIocMod, Real.Angle.coe_add, Real.Angle.coe_toIocMod,
        Real.Angle.coe_sub, add_sub_cancel]
    obtain ⟨m, hm⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 hclass
    have hbound : |toIocMod Real.two_pi_pos (Complex.arg (q - p)) (Complex.arg (y - q)) -
        (Complex.arg (q - p) +
          toIocMod Real.two_pi_pos 0 (Complex.arg (y - q) - Complex.arg (q - p)))| < 2 * Real.pi := by
      rcases hmem with ⟨h4, h5⟩
      rcases hmem0 with ⟨h6, h7⟩
      rw [abs_lt]
      constructor <;> linarith [Real.pi_pos]
    have hm0 : m = 0 := by
      have e : toIocMod Real.two_pi_pos (Complex.arg (q - p)) (Complex.arg (y - q)) -
          (Complex.arg (q - p) +
            toIocMod Real.two_pi_pos 0 (Complex.arg (y - q) - Complex.arg (q - p)))
          = 2 * Real.pi * m := by linarith [hm]
      rw [e] at hbound
      exact int_eq_zero_of_abs_two_pi_mul_lt m hbound
    rw [hm0, Int.cast_zero, mul_zero] at hm
    linarith [hm]
  -- the ratio's arg is the mod-2π rep of the difference; connect the two representatives
  have hrep : toIocMod Real.two_pi_pos 0 (Complex.arg (y - q) - Complex.arg (q - p)) ∈ Set.Ioo 0 Real.pi
      ↔ Complex.arg ((y - q) / (q - p)) ∈ Set.Ioo 0 Real.pi := by
    rw [← h3]
    have h4 := toIocMod_mem_Ioc Real.two_pi_pos (-Real.pi) (Complex.arg (y - q) - Complex.arg (q - p))
    have h5 := toIocMod_mem_Ioc Real.two_pi_pos 0 (Complex.arg (y - q) - Complex.arg (q - p))
    -- the two reps differ by a multiple of 2π; within (0, π) they coincide
    have hclass : ((toIocMod Real.two_pi_pos (-Real.pi) (Complex.arg (y - q) - Complex.arg (q - p)) : ℝ) : Real.Angle)
        = ((toIocMod Real.two_pi_pos 0 (Complex.arg (y - q) - Complex.arg (q - p))) : ℝ) := by
      rw [Real.Angle.coe_toIocMod, Real.Angle.coe_toIocMod]
    obtain ⟨m, hm⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 hclass
    constructor
    · intro h
      -- toIocMod 0 d ∈ (0, π) ⟹ equal to toIocMod(−π) d
      have hm0 : m = 0 := by
        rcases h5 with ⟨h6, h7⟩
        rcases h4 with ⟨h8, h9⟩
        have e : toIocMod Real.two_pi_pos (-Real.pi) (Complex.arg (y - q) - Complex.arg (q - p)) -
            toIocMod Real.two_pi_pos 0 (Complex.arg (y - q) - Complex.arg (q - p)) = 2 * Real.pi * m := by
          linarith [hm]
        have hb : |toIocMod Real.two_pi_pos (-Real.pi) (Complex.arg (y - q) - Complex.arg (q - p)) -
            toIocMod Real.two_pi_pos 0 (Complex.arg (y - q) - Complex.arg (q - p))| < 2 * Real.pi := by
          rw [abs_lt]
          constructor <;> linarith [Real.pi_pos, h.1, h.2]
        rw [e] at hb
        exact int_eq_zero_of_abs_two_pi_mul_lt m hb
      rw [hm0, Int.cast_zero, mul_zero] at hm
      exact ⟨by linarith [hm, h.1], by linarith [hm, h.2]⟩
    · intro h
      -- arg ratio ∈ (0,π) ⟹ toIocMod(−π) d = toIocMod 0 d
      have hm0 : m = 0 := by
        rcases h5 with ⟨h6, h7⟩
        rcases h4 with ⟨h8, h9⟩
        have e : toIocMod Real.two_pi_pos (-Real.pi) (Complex.arg (y - q) - Complex.arg (q - p)) -
            toIocMod Real.two_pi_pos 0 (Complex.arg (y - q) - Complex.arg (q - p)) = 2 * Real.pi * m := by
          linarith [hm]
        have hb : |toIocMod Real.two_pi_pos (-Real.pi) (Complex.arg (y - q) - Complex.arg (q - p)) -
            toIocMod Real.two_pi_pos 0 (Complex.arg (y - q) - Complex.arg (q - p))| < 2 * Real.pi := by
          rw [abs_lt]
          constructor <;> linarith [Real.pi_pos, h.1, h.2]
        rw [e] at hb
        exact int_eq_zero_of_abs_two_pi_mul_lt m hb
      rw [hm0, Int.cast_zero, mul_zero] at hm
      exact ⟨by linarith [hm, h.1], by linarith [hm, h.2]⟩
  have hfinal : toIocMod Real.two_pi_pos 0 (Complex.arg (y - q) - Complex.arg (q - p)) ∈ Set.Ioo 0 Real.pi
      ↔ toIocMod Real.two_pi_pos (Complex.arg (q - p)) (Complex.arg (y - q)) ∈
        Set.Ioo (Complex.arg (q - p)) (Complex.arg (q - p) + Real.pi) := by
    rw [hshift]
    constructor
    · rintro ⟨h4, h5⟩
      exact ⟨by linarith [h4], by linarith [h5]⟩
    · rintro ⟨h4, h5⟩
      exact ⟨by linarith [h4], by linarith [h5]⟩
  rw [h1, ← him, h2, ← hrep, ← hfinal]

/-- From-`p` version: `y` strictly left of the ray from `p` to `q` iff the direction
from `p` to `y` lies in the open semicircle starting at the direction from `p` to `q`. -/
lemma left_iff_arg_window_from_p (p q y : ℂ) (hpq : q ≠ p) (hyp : y ≠ p) :
    0 < cross (q - p) (y - p) ↔
      toIocMod Real.two_pi_pos (Complex.arg (q - p)) (Complex.arg (y - p)) ∈
        Set.Ioo (Complex.arg (q - p)) (Complex.arg (q - p) + Real.pi) := by
  have h1 : 0 < cross (q - p) (y - p) ↔ 0 < ((y - p) / (q - p)).im := by
    rw [im_div_eq_cross_div_normSq]
    have hn : 0 < Complex.normSq (q - p) := Complex.normSq_pos.2 (sub_ne_zero.mpr hpq)
    constructor
    · intro h
      exact div_pos h hn
    · intro h
      have h6 := (lt_div_iff₀ hn).mp h
      simpa using h6
  have h2 : 0 < ((y - p) / (q - p)).im ↔ Complex.arg ((y - p) / (q - p)) ∈ Set.Ioo 0 Real.pi := by
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · rw [lt_iff_le_and_ne]
        exact ⟨Complex.arg_nonneg_iff.2 h.le, fun hz => ne_of_gt h (Complex.arg_eq_zero_iff.1 hz.symm).2⟩
      · rw [lt_iff_le_and_ne]
        exact ⟨Complex.arg_le_pi _, fun hz => ne_of_gt h (Complex.arg_eq_pi_iff.1 hz).2⟩
    · intro h
      by_contra him0
      push Not at him0
      rcases lt_or_eq_of_le him0 with him3 | him3
      · have h6 := Complex.arg_neg_iff.2 him3
        linarith [h.1, h6]
      · have h7 : 0 ≤ ((y - p) / (q - p)).re ∨ ((y - p) / (q - p)).re < 0 := le_or_gt _ _
        rcases h7 with h7 | h7
        · have h8 := (Complex.arg_eq_zero_iff).2 ⟨h7, him3⟩
          linarith [h.1, h8]
        · have h8 := (Complex.arg_eq_pi_iff).2 ⟨h7, him3⟩
          linarith [h.2, h8]
  have h3 : toIocMod Real.two_pi_pos (-Real.pi) (Complex.arg (y - p) - Complex.arg (q - p))
      = Complex.arg ((y - p) / (q - p)) := by
    have h1' : (Complex.arg ((y - p) / (q - p)) : Real.Angle)
        = ((Complex.arg (y - p) - Complex.arg (q - p) : ℝ) : Real.Angle) := by
      rw [Complex.arg_div_coe_angle (sub_ne_zero.mpr hyp) (sub_ne_zero.mpr hpq),
        Real.Angle.coe_sub]
    have h4 : toIocMod Real.two_pi_pos (-Real.pi) (Complex.arg (y - p) - Complex.arg (q - p))
        = toIocMod Real.two_pi_pos (-Real.pi) (Complex.arg ((y - p) / (q - p))) := by
      obtain ⟨m, hm⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 h1'
      rw [show Complex.arg ((y - p) / (q - p))
          = (Complex.arg (y - p) - Complex.arg (q - p)) + m • (2 * Real.pi) by
        rw [zsmul_eq_mul]
        linarith [hm]]
      rw [toIocMod_add_zsmul]
    rw [h4, toIocMod_eq_self Real.two_pi_pos]
    exact ⟨Complex.neg_pi_lt_arg _, by linarith [Complex.arg_le_pi ((y - p) / (q - p))]⟩
  have hshift : toIocMod Real.two_pi_pos (Complex.arg (q - p)) (Complex.arg (y - p))
      = Complex.arg (q - p) +
        toIocMod Real.two_pi_pos 0 (Complex.arg (y - p) - Complex.arg (q - p)) := by
    have hmem := toIocMod_mem_Ioc Real.two_pi_pos (Complex.arg (q - p)) (Complex.arg (y - p))
    have hmem0 := toIocMod_mem_Ioc Real.two_pi_pos 0 (Complex.arg (y - p) - Complex.arg (q - p))
    have hclass : ((toIocMod Real.two_pi_pos (Complex.arg (q - p)) (Complex.arg (y - p)) : ℝ) : Real.Angle)
        = ((Complex.arg (q - p) +
          toIocMod Real.two_pi_pos 0 (Complex.arg (y - p) - Complex.arg (q - p))) : ℝ) := by
      rw [Real.Angle.coe_toIocMod, Real.Angle.coe_add, Real.Angle.coe_toIocMod,
        Real.Angle.coe_sub, add_sub_cancel]
    obtain ⟨m, hm⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 hclass
    have hbound : |toIocMod Real.two_pi_pos (Complex.arg (q - p)) (Complex.arg (y - p)) -
        (Complex.arg (q - p) +
          toIocMod Real.two_pi_pos 0 (Complex.arg (y - p) - Complex.arg (q - p)))| < 2 * Real.pi := by
      rcases hmem with ⟨h4, h5⟩
      rcases hmem0 with ⟨h6, h7⟩
      rw [abs_lt]
      constructor <;> linarith [Real.pi_pos]
    have hm0 : m = 0 := by
      have e : toIocMod Real.two_pi_pos (Complex.arg (q - p)) (Complex.arg (y - p)) -
          (Complex.arg (q - p) +
            toIocMod Real.two_pi_pos 0 (Complex.arg (y - p) - Complex.arg (q - p)))
          = 2 * Real.pi * m := by linarith [hm]
      rw [e] at hbound
      exact int_eq_zero_of_abs_two_pi_mul_lt m hbound
    rw [hm0, Int.cast_zero, mul_zero] at hm
    linarith [hm]
  have hfinal : toIocMod Real.two_pi_pos 0 (Complex.arg (y - p) - Complex.arg (q - p)) ∈ Set.Ioo 0 Real.pi
      ↔ toIocMod Real.two_pi_pos (Complex.arg (q - p)) (Complex.arg (y - p)) ∈
        Set.Ioo (Complex.arg (q - p)) (Complex.arg (q - p) + Real.pi) := by
    rw [hshift]
    constructor
    · rintro ⟨h4, h5⟩
      exact ⟨by linarith [h4], by linarith [h5]⟩
    · rintro ⟨h4, h5⟩
      exact ⟨by linarith [h4], by linarith [h5]⟩
  have hrep : toIocMod Real.two_pi_pos 0 (Complex.arg (y - p) - Complex.arg (q - p)) ∈ Set.Ioo 0 Real.pi
      ↔ Complex.arg ((y - p) / (q - p)) ∈ Set.Ioo 0 Real.pi := by
    rw [← h3]
    constructor
    · intro h
      rcases h with ⟨h4, h5⟩
      have h6 := toIocMod_mem_Ioc Real.two_pi_pos (-Real.pi) (Complex.arg (y - p) - Complex.arg (q - p))
      have h7 := toIocMod_mem_Ioc Real.two_pi_pos 0 (Complex.arg (y - p) - Complex.arg (q - p))
      have hclass : ((toIocMod Real.two_pi_pos (-Real.pi) (Complex.arg (y - p) - Complex.arg (q - p)) : ℝ) : Real.Angle)
          = ((toIocMod Real.two_pi_pos 0 (Complex.arg (y - p) - Complex.arg (q - p))) : ℝ) := by
        rw [Real.Angle.coe_toIocMod, Real.Angle.coe_toIocMod]
      obtain ⟨m, hm⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 hclass
      have hm0 : m = 0 := by
        have e : toIocMod Real.two_pi_pos (-Real.pi) (Complex.arg (y - p) - Complex.arg (q - p)) -
            toIocMod Real.two_pi_pos 0 (Complex.arg (y - p) - Complex.arg (q - p)) = 2 * Real.pi * m := by
          linarith [hm]
        have hb : |toIocMod Real.two_pi_pos (-Real.pi) (Complex.arg (y - p) - Complex.arg (q - p)) -
            toIocMod Real.two_pi_pos 0 (Complex.arg (y - p) - Complex.arg (q - p))| < 2 * Real.pi := by
          rcases h6 with ⟨h8, h9⟩
          rcases h7 with ⟨h10, h11⟩
          rw [abs_lt]
          constructor <;> linarith [Real.pi_pos, h4, h5]
        rw [e] at hb
        exact int_eq_zero_of_abs_two_pi_mul_lt m hb
      rw [hm0, Int.cast_zero, mul_zero] at hm
      exact ⟨by linarith [hm, h4], by linarith [hm, h5]⟩
    · intro h
      have h6 := toIocMod_mem_Ioc Real.two_pi_pos (-Real.pi) (Complex.arg (y - p) - Complex.arg (q - p))
      have h7 := toIocMod_mem_Ioc Real.two_pi_pos 0 (Complex.arg (y - p) - Complex.arg (q - p))
      have hclass : ((toIocMod Real.two_pi_pos (-Real.pi) (Complex.arg (y - p) - Complex.arg (q - p)) : ℝ) : Real.Angle)
          = ((toIocMod Real.two_pi_pos 0 (Complex.arg (y - p) - Complex.arg (q - p))) : ℝ) := by
        rw [Real.Angle.coe_toIocMod, Real.Angle.coe_toIocMod]
      obtain ⟨m, hm⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 hclass
      have hm0 : m = 0 := by
        have e : toIocMod Real.two_pi_pos (-Real.pi) (Complex.arg (y - p) - Complex.arg (q - p)) -
            toIocMod Real.two_pi_pos 0 (Complex.arg (y - p) - Complex.arg (q - p)) = 2 * Real.pi * m := by
          linarith [hm]
        have hb : |toIocMod Real.two_pi_pos (-Real.pi) (Complex.arg (y - p) - Complex.arg (q - p)) -
            toIocMod Real.two_pi_pos 0 (Complex.arg (y - p) - Complex.arg (q - p))| < 2 * Real.pi := by
          rcases h6 with ⟨h8, h9⟩
          rcases h7 with ⟨h10, h11⟩
          rw [abs_lt]
          constructor <;> linarith [Real.pi_pos, h.1, h.2]
        rw [e] at hb
        exact int_eq_zero_of_abs_two_pi_mul_lt m hb
      rw [hm0, Int.cast_zero, mul_zero] at hm
      exact ⟨by linarith [hm, h.1], by linarith [hm, h.2]⟩
  rw [h1, h2, ← hrep, ← hfinal]

/-- The representative of `x` with anchor `a + k • 2π` is `k • 2π` plus the
representative with anchor `a`. -/
lemma toIocMod_anchor_add_two_pi_zsmul (x : ℝ) (a : ℝ) (k : ℤ) :
    toIocMod Real.two_pi_pos (a + (k : ℝ) * (2 * Real.pi)) x
      = toIocMod Real.two_pi_pos a x + (k : ℝ) * (2 * Real.pi) := by
  have hclass : ((toIocMod Real.two_pi_pos (a + (k : ℝ) * (2 * Real.pi)) x : ℝ) : Real.Angle)
      = ((toIocMod Real.two_pi_pos a x + (k : ℝ) * (2 * Real.pi)) : ℝ) := by
    rw [Real.Angle.coe_toIocMod, Real.Angle.coe_add, Real.Angle.coe_toIocMod]
    have hz : (((k : ℝ) * (2 * Real.pi)) : Real.Angle) = 0 :=
      Real.Angle.coe_eq_zero_iff.2 ⟨k, by rw [zsmul_eq_mul]⟩
    rw [hz, add_zero]
  obtain ⟨m, hm⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 hclass
  have hbound : |toIocMod Real.two_pi_pos (a + (k : ℝ) * (2 * Real.pi)) x -
      (toIocMod Real.two_pi_pos a x + (k : ℝ) * (2 * Real.pi))| < 2 * Real.pi := by
    have h4 := toIocMod_mem_Ioc Real.two_pi_pos (a + (k : ℝ) * (2 * Real.pi)) x
    have h5 := toIocMod_mem_Ioc Real.two_pi_pos a x
    rcases h4 with ⟨h6, h7⟩
    rcases h5 with ⟨h8, h9⟩
    rw [abs_lt]
    constructor <;> linarith [Real.pi_pos]
  have hm0 : m = 0 := by
    have e : toIocMod Real.two_pi_pos (a + (k : ℝ) * (2 * Real.pi)) x -
        (toIocMod Real.two_pi_pos a x + (k : ℝ) * (2 * Real.pi)) = 2 * Real.pi * m := by
      linarith [hm]
    rw [e] at hbound
    exact int_eq_zero_of_abs_two_pi_mul_lt m hbound
  rw [hm0, Int.cast_zero, mul_zero] at hm
  linarith [hm]

lemma toIocMod_anchor_add_two_pi (x : ℝ) (a : ℝ) :
    toIocMod Real.two_pi_pos (a + 2 * Real.pi) x = toIocMod Real.two_pi_pos a x + 2 * Real.pi := by
  have h := toIocMod_anchor_add_two_pi_zsmul x a 1
  rw [Int.cast_one, one_mul] at h
  exact h

/-- From-`p` negative version: `y` strictly right of the ray from `p` to `q` iff the
direction from `p` to `y` lies in the open semicircle ending at the direction from
`p` to `q`. -/
lemma right_iff_arg_window_from_p (p q y : ℂ) (hpq : q ≠ p) (hyp : y ≠ p) :
    cross (q - p) (y - p) < 0 ↔
      toIocMod Real.two_pi_pos (Complex.arg (q - p) - Real.pi) (Complex.arg (y - p)) ∈
        Set.Ioo (Complex.arg (q - p) - Real.pi) (Complex.arg (q - p)) := by
  have hswap : cross (q - p) (y - p) = -cross (p - q) (y - p) := by
    simp only [cross_eq_re_im, Complex.sub_re, Complex.sub_im]
    ring
  have hneg : cross (q - p) (y - p) < 0 ↔ 0 < cross (p - q) (y - p) := by
    rw [hswap]
    constructor <;> intro h <;> linarith
  have hpos := left_iff_arg_window_from_p p (2 * p - q) y (by
    intro h
    have h4 : p = q := by linear_combination h
    exact hpq h4.symm) hyp
  rw [show (2 : ℂ) * p - q - p = p - q by ring] at hpos
  rw [hneg, hpos]
  obtain ⟨m, hm⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1
    (Complex.arg_neg_coe_angle (sub_ne_zero.mpr hpq))
  have h2 : Complex.arg (p - q) = Complex.arg (q - p) + Real.pi + 2 * Real.pi * m := by
    have h3 : Complex.arg (-(q - p)) = Complex.arg (p - q) := by
      rw [neg_sub]
    rw [← h3]
    linarith [hm]
  have hm1 : m = 0 ∨ m = -1 := by
    have h4 : -Real.pi < Complex.arg (p - q) := Complex.neg_pi_lt_arg _
    have h5 : Complex.arg (p - q) ≤ Real.pi := Complex.arg_le_pi _
    have h6 : -Real.pi < Complex.arg (q - p) := Complex.neg_pi_lt_arg _
    have h7 : Complex.arg (q - p) ≤ Real.pi := Complex.arg_le_pi _
    have h8 : (0:ℝ) < 2 * Real.pi := by positivity
    by_contra hne
    push Not at hne
    rcases lt_or_gt_of_ne hne.1 with hm' | hm'
    · have hm'' : m ≤ (-2 : ℤ) := by
        have h9 : m ≠ -1 := hne.2
        omega
      have h11 : (m : ℝ) ≤ -2 := by exact_mod_cast hm''
      have h12 : (2:ℝ) * Real.pi * m ≤ (2:ℝ) * Real.pi * (-2 : ℝ) := by
        apply mul_le_mul_of_nonneg_left h11 (by positivity)
      nlinarith [h2, h4, h7, h8, h12]
    · have hm'' : (1 : ℤ) ≤ m := by omega
      have h11 : (1 : ℝ) ≤ m := by exact_mod_cast hm''
      have h12 : (2:ℝ) * Real.pi * 1 ≤ (2:ℝ) * Real.pi * m := by
        apply mul_le_mul_of_nonneg_left h11 (by positivity)
      nlinarith [h2, h5, h6, h8, h12]
  rcases hm1 with hm1 | hm1
  · have h9 : Complex.arg (p - q) = Complex.arg (q - p) - Real.pi + 2 * Real.pi := by
      rw [hm1, Int.cast_zero, mul_zero, add_zero] at h2
      linarith [h2]
    rw [h9, toIocMod_anchor_add_two_pi (Complex.arg (y - p)) (Complex.arg (q - p) - Real.pi)]
    constructor
    · rintro ⟨h4, h5⟩
      exact ⟨by linarith [h4], by linarith [h5]⟩
    · rintro ⟨h4, h5⟩
      exact ⟨by linarith [h4], by linarith [h5]⟩
  · have h9 : Complex.arg (p - q) = Complex.arg (q - p) - Real.pi := by
      rw [hm1, Int.cast_neg, Int.cast_one, mul_neg, mul_one] at h2
      linarith [h2]
    rw [h9]
    simp

/-- `arg (y / x)` is the representative of `arg y - arg x` in `(-π, π]`. -/
lemma arg_div_eq_toIocMod_sub (x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) :
    Complex.arg (y / x) = toIocMod Real.two_pi_pos (-Real.pi) (Complex.arg y - Complex.arg x) := by
  have h1 : (Complex.arg (y / x) : Real.Angle) = ((Complex.arg y - Complex.arg x : ℝ) : Real.Angle) := by
    rw [Complex.arg_div_coe_angle hy hx, Real.Angle.coe_sub]
  have h2 : toIocMod Real.two_pi_pos (-Real.pi) (Complex.arg y - Complex.arg x)
      = toIocMod Real.two_pi_pos (-Real.pi) (Complex.arg (y / x)) := by
    obtain ⟨m, hm⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 h1
    rw [show Complex.arg (y / x) = (Complex.arg y - Complex.arg x) + m • (2 * Real.pi) by
      rw [zsmul_eq_mul]
      linarith [hm]]
    rw [toIocMod_add_zsmul]
  have h3 : toIocMod Real.two_pi_pos (-Real.pi) (Complex.arg (y / x)) = Complex.arg (y / x) := by
    rw [toIocMod_eq_self Real.two_pi_pos]
    exact ⟨Complex.neg_pi_lt_arg _, by linarith [Complex.arg_le_pi (y / x)]⟩
  rw [← h3, h2]

/-- Positive cross product ⟺ direction of `w` in the open semicircle ahead of `u`. -/
lemma cross_pos_iff_arg_mem (u w : ℂ) (hu : u ≠ 0) (hw : w ≠ 0) :
    0 < cross u w ↔
      toIocMod Real.two_pi_pos (Complex.arg u) (Complex.arg w) ∈
        Set.Ioo (Complex.arg u) (Complex.arg u + Real.pi) := by
  have h := left_iff_arg_window_from_p (0 : ℂ) u w hu hw
  rwa [sub_zero, sub_zero] at h

/-- Negative cross product ⟺ direction of `w` in the open semicircle behind `u`. -/
lemma cross_neg_iff_arg_mem (u w : ℂ) (hu : u ≠ 0) (hw : w ≠ 0) :
    cross u w < 0 ↔
      toIocMod Real.two_pi_pos (Complex.arg u - Real.pi) (Complex.arg w) ∈
        Set.Ioo (Complex.arg u - Real.pi) (Complex.arg u) := by
  have h := right_iff_arg_window_from_p (0 : ℂ) u w hu hw
  rwa [sub_zero, sub_zero] at h

lemma toIocMod_zero_cases (d : ℝ) :
    toIocMod Real.two_pi_pos 0 d = toIocMod Real.two_pi_pos (-Real.pi) d ∨
      toIocMod Real.two_pi_pos 0 d = toIocMod Real.two_pi_pos (-Real.pi) d + 2 * Real.pi := by
  have hclass : ((toIocMod Real.two_pi_pos 0 d : ℝ) : Real.Angle)
      = ((toIocMod Real.two_pi_pos (-Real.pi) d) : ℝ) := by
    rw [Real.Angle.coe_toIocMod, Real.Angle.coe_toIocMod]
  obtain ⟨m, hm⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 hclass
  have h1 := toIocMod_mem_Ioc Real.two_pi_pos 0 d
  have h2 := toIocMod_mem_Ioc Real.two_pi_pos (-Real.pi) d
  rcases h1 with ⟨h3, h4⟩
  rcases h2 with ⟨h5, h6⟩
  have h7 : toIocMod Real.two_pi_pos 0 d - toIocMod Real.two_pi_pos (-Real.pi) d = 2 * Real.pi * m := by
    linarith [hm]
  have hm01 : m = 0 ∨ m = 1 := by
    have h8 : (0:ℝ) < 2 * Real.pi := by positivity
    by_contra hne
    push Not at hne
    rcases lt_or_gt_of_ne hne.1 with hm' | hm'
    · have hm'' : m ≤ (-1 : ℤ) := by omega
      have h11 : (m : ℝ) ≤ -1 := by exact_mod_cast hm''
      have h12 : (2:ℝ) * Real.pi * m ≤ (2:ℝ) * Real.pi * (-1 : ℝ) := by
        apply mul_le_mul_of_nonneg_left h11 (by positivity)
      nlinarith [h7, h3, h6, h8, h12]
    · have hm'' : (2 : ℤ) ≤ m := by omega
      have h11 : (2 : ℝ) ≤ m := by exact_mod_cast hm''
      have h12 : (2:ℝ) * Real.pi * 2 ≤ (2:ℝ) * Real.pi * m := by
        apply mul_le_mul_of_nonneg_left h11 (by positivity)
      nlinarith [h7, h4, h5, h8, h12]
  rcases hm01 with hm01 | hm01
  · left
    rw [hm01, Int.cast_zero, mul_zero] at h7
    linarith [h7]
  · right
    rw [hm01, Int.cast_one, mul_one] at h7
    linarith [h7]

lemma toIocMod_zero_neg_cases (d : ℝ) :
    toIocMod Real.two_pi_pos 0 (-d) + toIocMod Real.two_pi_pos 0 d = 2 * Real.pi ∨
      (toIocMod Real.two_pi_pos 0 (-d) = 2 * Real.pi ∧ toIocMod Real.two_pi_pos 0 d = 2 * Real.pi) := by
  have hclass : ((toIocMod Real.two_pi_pos 0 (-d) : ℝ) : Real.Angle)
      = (-(toIocMod Real.two_pi_pos 0 d) : ℝ) := by
    rw [Real.Angle.coe_toIocMod, Real.Angle.coe_neg, ← Real.Angle.coe_toIocMod,
      Real.Angle.coe_neg]
  obtain ⟨m, hm⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 hclass
  have h1 := toIocMod_mem_Ioc Real.two_pi_pos 0 (-d)
  have h2 := toIocMod_mem_Ioc Real.two_pi_pos 0 d
  rcases h1 with ⟨h3, h4⟩
  rcases h2 with ⟨h5, h6⟩
  have h7 : toIocMod Real.two_pi_pos 0 (-d) + toIocMod Real.two_pi_pos 0 d = 2 * Real.pi * m := by
    linarith [hm]
  have hm01 : m = 1 ∨ m = 2 := by
    have h8 : (0:ℝ) < 2 * Real.pi := by positivity
    by_contra hne
    push Not at hne
    rcases lt_or_gt_of_ne hne.1 with hm' | hm'
    · have hm'' : m ≤ (0 : ℤ) := by omega
      have h11 : (m : ℝ) ≤ 0 := by exact_mod_cast hm''
      have h12 : (2:ℝ) * Real.pi * m ≤ (2:ℝ) * Real.pi * 0 := by
        apply mul_le_mul_of_nonneg_left h11 (by positivity)
      nlinarith [h7, h3, h6, h8, h12]
    · have hm'' : (3 : ℤ) ≤ m := by omega
      have h11 : (3 : ℝ) ≤ m := by exact_mod_cast hm''
      have h12 : (2:ℝ) * Real.pi * 3 ≤ (2:ℝ) * Real.pi * m := by
        apply mul_le_mul_of_nonneg_left h11 (by positivity)
      nlinarith [h7, h4, h5, h8, h12]
  rcases hm01 with hm01 | hm01
  · left
    rw [hm01, Int.cast_one, mul_one] at h7
    exact h7
  · right
    rw [hm01, Int.cast_two] at h7
    constructor
    · linarith [h7, h4]
    · linarith [h7, h6]

/-- Positive cross product ⟺ the direction difference has representative in `(0, π)`. -/
lemma cross_pos_iff (u w : ℂ) (hu : u ≠ 0) (hw : w ≠ 0) :
    0 < cross u w ↔ toIocMod Real.two_pi_pos 0 (Complex.arg w - Complex.arg u) ∈ Set.Ioo 0 Real.pi := by
  have h1 : 0 < cross u w ↔ 0 < (w / u).im := by
    rw [im_div_eq_cross_div_normSq]
    have hn : 0 < Complex.normSq u := Complex.normSq_pos.2 hu
    constructor
    · intro h
      exact div_pos h hn
    · intro h
      have h6 := (lt_div_iff₀ hn).mp h
      simpa using h6
  have h2 : 0 < (w / u).im ↔ Complex.arg (w / u) ∈ Set.Ioo 0 Real.pi := by
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · rw [lt_iff_le_and_ne]
        exact ⟨Complex.arg_nonneg_iff.2 h.le, fun hz => ne_of_gt h (Complex.arg_eq_zero_iff.1 hz.symm).2⟩
      · rw [lt_iff_le_and_ne]
        exact ⟨Complex.arg_le_pi _, fun hz => ne_of_gt h (Complex.arg_eq_pi_iff.1 hz).2⟩
    · intro h
      by_contra him0
      push Not at him0
      rcases lt_or_eq_of_le him0 with him3 | him3
      · have h6 := Complex.arg_neg_iff.2 him3
        linarith [h.1, h6]
      · have h7 : 0 ≤ (w / u).re ∨ (w / u).re < 0 := le_or_gt _ _
        rcases h7 with h7 | h7
        · have h8 := (Complex.arg_eq_zero_iff).2 ⟨h7, him3⟩
          linarith [h.1, h8]
        · have h8 := (Complex.arg_eq_pi_iff).2 ⟨h7, him3⟩
          linarith [h.2, h8]
  have h3 : toIocMod Real.two_pi_pos 0 (Complex.arg w - Complex.arg u) ∈ Set.Ioo 0 Real.pi
      ↔ Complex.arg (w / u) ∈ Set.Ioo 0 Real.pi := by
    have h4 : toIocMod Real.two_pi_pos (-Real.pi) (Complex.arg w - Complex.arg u)
        = Complex.arg (w / u) := (arg_div_eq_toIocMod_sub u w hu hw).symm
    rcases toIocMod_zero_cases (Complex.arg w - Complex.arg u) with h5 | h5
    · rw [h5, h4]
    · rw [h5, h4]
      have h8 : (w / u).arg ≤ 0 := by
        have h9 := toIocMod_le_right Real.two_pi_pos 0 (Complex.arg w - Complex.arg u)
        rw [h5] at h9
        linarith [h9]
      constructor
      · intro h
        exfalso
        have h9 := Complex.neg_pi_lt_arg (w / u)
        rcases h with ⟨h10, h11⟩
        linarith [h9, h11]
      · intro h
        exfalso
        rcases h with ⟨h10, h11⟩
        linarith [h8, h10]
  rw [h1, h2, ← h3]

/-- Negative cross product ⟺ the direction difference has representative in `(π, 2π)`. -/
lemma cross_neg_iff (u w : ℂ) (hu : u ≠ 0) (hw : w ≠ 0) :
    cross u w < 0 ↔ toIocMod Real.two_pi_pos 0 (Complex.arg w - Complex.arg u) ∈
      Set.Ioo Real.pi (2 * Real.pi) := by
  have hswap : cross u w = -cross w u := by
    simp only [cross_eq_re_im]
    ring
  rw [hswap]
  have hpos : 0 < cross w u ↔ toIocMod Real.two_pi_pos 0 (Complex.arg u - Complex.arg w) ∈
      Set.Ioo 0 Real.pi := cross_pos_iff w u hw hu
  rw [show (-cross w u < 0) ↔ (0 < cross w u) from by constructor <;> intro h <;> linarith, hpos]
  -- toIocMod 0 (arg u − arg w) ∈ (0, π) ⟺ toIocMod 0 (arg w − arg u) ∈ (π, 2π)
  rcases toIocMod_zero_neg_cases (Complex.arg w - Complex.arg u) with h5 | h5
  · rw [neg_sub] at h5
    have h6 : toIocMod Real.two_pi_pos 0 (Complex.arg w - Complex.arg u)
        = 2 * Real.pi - toIocMod Real.two_pi_pos 0 (Complex.arg u - Complex.arg w) := by
      linarith [h5]
    rw [h6]
    constructor
    · rintro ⟨h7, h8⟩
      exact ⟨by linarith [h8], by linarith [h7]⟩
    · rintro ⟨h7, h8⟩
      exact ⟨by linarith [h8], by linarith [h7]⟩
  · rw [neg_sub] at h5
    rw [h5.1, h5.2]
    constructor
    · rintro ⟨h7, h8⟩
      exact absurd h8 (by linarith [Real.pi_pos] : ¬ (2 * Real.pi < Real.pi))
    · rintro ⟨h7, h8⟩
      exact absurd h8 (lt_irrefl (2 * Real.pi))
/-- The angular spread of a point set as seen from a point. -/
noncomputable def spreadIn (S : Finset ℂ) (p : ℂ) : ℝ :=
  sSup (((S ×ˢ S).image fun ab : ℂ × ℂ => uangle (ab.1 - p) (ab.2 - p)) : Set ℝ)

/-- At an exposed point, the directions to the other points lie in an open semicircle. -/
lemma arg_window_of_exposed {p q : ℂ} {u : ℂ} (hu0 : u ≠ 0)
    (h : 0 < (conj u * (q - p)).re) (hw : q - p ≠ 0) :
    toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (q - p)) ∈
      Set.Ioo (Complex.arg u - Real.pi / 2) (Complex.arg u + Real.pi / 2) := by
  have hcos : 0 < Real.cos (Complex.arg (q - p) - Complex.arg u) := by
    have h1 : 0 < ‖u‖ * ‖q - p‖ := mul_pos (norm_pos_iff.mpr hu0) (norm_pos_iff.mpr hw)
    have h2 : 0 < ‖u‖ * ‖q - p‖ * Real.cos (Complex.arg (q - p) - Complex.arg u) := by
      rw [← re_conj_eq u (q - p) hu0]
      exact h
    exact (mul_pos_iff_of_pos_left h1).mp h2
  set α := toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (q - p)) with hα
  have hmem : α ∈ Set.Ioc (Complex.arg u - Real.pi / 2) (Complex.arg u - Real.pi / 2 + 2 * Real.pi) :=
    toIocMod_mem_Ioc Real.two_pi_pos _ _
  have hper : Real.cos (Complex.arg (q - p) - Complex.arg u) = Real.cos (α - Complex.arg u) := by
    have h1 : ((Complex.arg (q - p) - Complex.arg u : ℝ) : Real.Angle)
        = ((α - Complex.arg u : ℝ) : Real.Angle) := by
      rw [hα, Real.Angle.coe_sub, Real.Angle.coe_sub,
        Real.Angle.coe_toIocMod (Complex.arg (q - p)) (Complex.arg u - Real.pi / 2)]
    rw [← Real.Angle.cos_coe, ← Real.Angle.cos_coe, h1]
  have hlt : α < Complex.arg u + Real.pi / 2 := by
    by_contra hge
    push Not at hge
    have hge2 : Real.pi / 2 ≤ α - Complex.arg u := by linarith [hge]
    have hle2 : α - Complex.arg u ≤ Real.pi + Real.pi / 2 := by
      have h1 := hmem.2
      linarith
    have hcle : Real.cos (α - Complex.arg u) ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le hge2 hle2
    linarith [hcle, hcos, hper]
  exact ⟨hmem.1, hlt⟩

/-- The angle between two rays from an exposed point equals the absolute difference of
the window arguments. -/
lemma uangle_in_window_eq {p x y : ℂ} {u : ℂ} (hu0 : u ≠ 0)
    (hx : 0 < (conj u * (x - p)).re) (hy : 0 < (conj u * (y - p)).re)
    (hx0 : x - p ≠ 0) (hy0 : y - p ≠ 0) :
    uangle (x - p) (y - p) =
      |toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (x - p)) -
        toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (y - p))| := by
  have hmem_i := arg_window_of_exposed hu0 hx hx0
  have hmem_j := arg_window_of_exposed hu0 hy hy0
  set αi := toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (x - p)) with hαi
  set αj := toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (y - p)) with hαj
  have hratio : (Complex.arg ((x - p) / (y - p)) : Real.Angle) =
      ((αi - αj : ℝ) : Real.Angle) := by
    rw [Complex.arg_div_coe_angle hx0 hy0, ← Real.Angle.coe_toIocMod
      (Complex.arg (x - p)) (Complex.arg u - Real.pi / 2),
      ← Real.Angle.coe_toIocMod (Complex.arg (y - p)) (Complex.arg u - Real.pi / 2),
      Real.Angle.coe_sub]
  have h4 : toIocMod Real.two_pi_pos (-Real.pi) (αi - αj) = αi - αj := by
    rw [toIocMod_eq_self Real.two_pi_pos]
    constructor
    · have h1 := hmem_j.2
      have h2 := hmem_i.1
      linarith
    · have h1 := hmem_i.2
      have h2 := hmem_j.1
      linarith
  have e4 : Complex.arg ((x - p) / (y - p)) = αi - αj := by
    obtain ⟨m, hm⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 hratio
    have h2 : toIocMod Real.two_pi_pos (-Real.pi) (Complex.arg ((x - p) / (y - p)))
        = toIocMod Real.two_pi_pos (-Real.pi) (αi - αj) := by
      have e : Complex.arg ((x - p) / (y - p)) = (αi - αj) + m • (2 * Real.pi) := by
        rw [zsmul_eq_mul]
        linarith [hm]
      rw [e, toIocMod_add_zsmul]
    have h3 : toIocMod Real.two_pi_pos (-Real.pi) (Complex.arg ((x - p) / (y - p)))
        = Complex.arg ((x - p) / (y - p)) := by
      rw [toIocMod_eq_self Real.two_pi_pos]
      exact ⟨Complex.neg_pi_lt_arg _, by linarith [Complex.arg_le_pi ((x - p) / (y - p))]⟩
    rw [← h3, h2, h4]
  rw [uangle, e4]

/-- At an exposed point of a point set, the spread equals the max minus min of the
window arguments. -/
lemma spreadIn_eq_arg {S : Finset ℂ} {p : ℂ} (hp : p ∈ S)
    {u : ℂ} (hu0 : u ≠ 0) (hu : ∀ q ∈ S, q ≠ p → 0 < (conj u * (q - p)).re)
    (hne : (S.erase p).Nonempty) :
    ∃ gmin gmax : ℝ,
      (∀ q ∈ S, q ≠ p → gmin ≤ toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2)
          (Complex.arg (q - p))) ∧
      (∀ q ∈ S, q ≠ p → toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2)
          (Complex.arg (q - p)) ≤ gmax) ∧
      (∃ q ∈ S, q ≠ p ∧ toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2)
          (Complex.arg (q - p)) = gmin) ∧
      (∃ q ∈ S, q ≠ p ∧ toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2)
          (Complex.arg (q - p)) = gmax) ∧
      spreadIn S p = gmax - gmin := by
  set s := S.erase p with hs
  set α : ℂ → ℝ := fun q => toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2)
    (Complex.arg (q - p)) with hα
  set img := s.image α with himg
  have himg_ne : img.Nonempty := Finset.Nonempty.image hne _
  have hmin_le_max : img.min' himg_ne ≤ img.max' himg_ne :=
    Finset.min'_le img (img.max' himg_ne) (Finset.max'_mem _ _)
  refine ⟨img.min' himg_ne, img.max' himg_ne, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq hqp
    exact Finset.min'_le img _ (Finset.mem_image.2 ⟨q, mem_erase.2 ⟨hqp, hq⟩, rfl⟩)
  · intro q hq hqp
    exact Finset.le_max' img _ (Finset.mem_image.2 ⟨q, mem_erase.2 ⟨hqp, hq⟩, rfl⟩)
  · obtain ⟨g, hg_mem, hg_eq⟩ := Finset.mem_image.1 (Finset.min'_mem img himg_ne)
    exact ⟨g, (mem_erase.1 hg_mem).2, (mem_erase.1 hg_mem).1, hg_eq⟩
  · obtain ⟨g, hg_mem, hg_eq⟩ := Finset.mem_image.1 (Finset.max'_mem img himg_ne)
    exact ⟨g, (mem_erase.1 hg_mem).2, (mem_erase.1 hg_mem).1, hg_eq⟩
  · -- spreadIn S p = max' − min'
    have h_bdd : BddAbove (((S ×ˢ S).image fun ab : ℂ × ℂ => uangle (ab.1 - p) (ab.2 - p)) : Set ℝ) := by
      refine ⟨Real.pi, ?_⟩
      intro y hy
      obtain ⟨ab, hab_mem, hab_eq⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
      rw [← hab_eq]
      exact (uangle_mem_Icc _ _).2
    apply le_antisymm
    · apply csSup_le
      · exact ⟨uangle (p - p) (p - p), Finset.mem_coe.2 (Finset.mem_image.2 ⟨(p, p),
          Finset.mem_product.2 ⟨hp, hp⟩, rfl⟩)⟩
      · intro y hy
        obtain ⟨⟨x, y'⟩, hxy_mem, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
        show uangle (x - p) (y' - p) ≤ img.max' himg_ne - img.min' himg_ne
        by_cases hx : x = p
        · rw [hx]
          rw [show p - p = 0 by ring]
          have h1 : uangle 0 (y' - p) = 0 := by
            rw [uangle, zero_div, Complex.arg_zero, abs_zero]
          rw [h1]
          linarith [hmin_le_max]
        by_cases hy' : y' = p
        · rw [hy']
          rw [show p - p = 0 by ring]
          have h1 : uangle (x - p) 0 = 0 := by
            rw [uangle, div_zero, Complex.arg_zero, abs_zero]
          rw [h1]
          linarith [hmin_le_max]
        · have hx_S : x ∈ S := (Finset.mem_product.1 hxy_mem).1
          have hy_S : y' ∈ S := (Finset.mem_product.1 hxy_mem).2
          have hx0 : x - p ≠ 0 := sub_ne_zero.mpr hx
          have hy0 : y' - p ≠ 0 := sub_ne_zero.mpr hy'
          have h1 := uangle_in_window_eq hu0 (hu x hx_S hx) (hu y' hy_S hy') hx0 hy0
          rw [h1]
          have hi_mem : α x ∈ img := Finset.mem_image.2 ⟨x, mem_erase.2 ⟨hx, hx_S⟩, rfl⟩
          have hj_mem : α y' ∈ img := Finset.mem_image.2 ⟨y', mem_erase.2 ⟨hy', hy_S⟩, rfl⟩
          have h2 := Finset.min'_le img _ hi_mem
          have h3 := Finset.le_max' img _ hj_mem
          have h4 := Finset.min'_le img _ hj_mem
          have h5 := Finset.le_max' img _ hi_mem
          rw [abs_le]
          constructor <;> linarith
    · apply le_csSup
      · exact h_bdd
      · obtain ⟨i₁, hi₁S, hi₁k, hi₁⟩ := (show ∃ q ∈ S, q ≠ p ∧ α q = img.min' himg_ne from by
          obtain ⟨g, hg_mem, hg_eq⟩ := Finset.mem_image.1 (Finset.min'_mem img himg_ne)
          exact ⟨g, (mem_erase.1 hg_mem).2, (mem_erase.1 hg_mem).1, hg_eq⟩)
        obtain ⟨i₂, hi₂S, hi₂k, hi₂⟩ := (show ∃ q ∈ S, q ≠ p ∧ α q = img.max' himg_ne from by
          obtain ⟨g, hg_mem, hg_eq⟩ := Finset.mem_image.1 (Finset.max'_mem img himg_ne)
          exact ⟨g, (mem_erase.1 hg_mem).2, (mem_erase.1 hg_mem).1, hg_eq⟩)
        have hi₁0 : i₁ - p ≠ 0 := sub_ne_zero.mpr hi₁k
        have hi₂0 : i₂ - p ≠ 0 := sub_ne_zero.mpr hi₂k
        have hi₁' : toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (i₁ - p))
            = img.min' himg_ne := hi₁
        have hi₂' : toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (i₂ - p))
            = img.max' himg_ne := hi₂
        have heq : uangle (i₁ - p) (i₂ - p) = img.max' himg_ne - img.min' himg_ne := by
          have h0 : 0 ≤ img.max' himg_ne - img.min' himg_ne := sub_nonneg.mpr hmin_le_max
          rw [uangle_in_window_eq hu0 (hu i₁ hi₁S hi₁k) (hu i₂ hi₂S hi₂k) hi₁0 hi₂0,
            hi₁', hi₂', abs_sub_comm]
          exact abs_of_nonneg h0
        rw [← heq]
        exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨(i₁, i₂),
          Finset.mem_product.2 ⟨hi₁S, hi₂S⟩, rfl⟩)

lemma cross_add_left (x y z : ℂ) : cross (x + y) z = cross x z + cross y z := by
  simp only [cross_eq_re_im, Complex.add_re, Complex.add_im]
  ring

lemma cross_sub_left (x y z : ℂ) : cross (x - y) z = cross x z - cross y z := by
  simp only [cross_eq_re_im, Complex.sub_re, Complex.sub_im]
  ring

lemma cross_neg_left (x y : ℂ) : cross (-x) y = -cross x y := by
  simp only [cross_eq_re_im, Complex.neg_re, Complex.neg_im]
  ring

lemma cross_smul_left (t : ℝ) (x y : ℂ) : cross ((t : ℂ) * x) y = t * cross x y := by
  simp only [cross_eq_re_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma cross_swap (x y : ℂ) : cross x y = -cross y x := by
  simp only [cross_eq_re_im]
  ring

lemma cross_add_right (x y z : ℂ) : cross x (y + z) = cross x y + cross x z := by
  simp only [cross_eq_re_im, Complex.add_re, Complex.add_im]
  ring

lemma cross_sub_right (x y z : ℂ) : cross x (y - z) = cross x y - cross x z := by
  simp only [cross_eq_re_im, Complex.sub_re, Complex.sub_im]
  ring

lemma cross_zero_left (y : ℂ) : cross 0 y = 0 := by
  simp [cross_eq_re_im]

lemma cross_zero_right (x : ℂ) : cross x 0 = 0 := by
  simp [cross_eq_re_im]

/-- A vector with cross `0` against both `u` and `w` is zero (when `cross u w ≠ 0`). -/
lemma cross_eq_zero_of_both_zero {u w y : ℂ} (huw : cross u w ≠ 0)
    (h1 : cross y u = 0) (h2 : cross y w = 0) : y = 0 := by
  rw [cross_eq_re_im] at h1 h2 huw
  have h5 : y.re = 0 := by
    have e1 : y.re * (u.im * w.re - w.im * u.re) = 0 := by
      have t1 := congrArg (· * w.re) h1
      have t2 := congrArg (· * u.re) h2
      nlinarith [t1, t2]
    have h6 : u.im * w.re - w.im * u.re ≠ 0 := by
      rw [show u.im * w.re - w.im * u.re = -(u.re * w.im - u.im * w.re) by ring]
      exact neg_ne_zero.mpr huw
    exact (mul_eq_zero.1 e1).resolve_right h6
  have h7 : y.im = 0 := by
    have e1 : y.im * (u.im * w.re - w.im * u.re) = 0 := by
      have t1 := congrArg (· * w.im) h1
      have t2 := congrArg (· * u.im) h2
      nlinarith [t1, t2]
    have h6 : u.im * w.re - w.im * u.re ≠ 0 := by
      rw [show u.im * w.re - w.im * u.re = -(u.re * w.im - u.im * w.re) by ring]
      exact neg_ne_zero.mpr huw
    exact (mul_eq_zero.1 e1).resolve_right h6
  exact Complex.ext (by simp [h5]) (by simp [h7])

/-- The Cramer decomposition of a vector in a nondegenerate basis. -/
lemma combo_of_wedge {u w z : ℂ} (huw : cross u w ≠ 0) :
    z = ((cross z w / cross u w : ℝ) : ℂ) * u + ((cross u z / cross u w : ℝ) : ℂ) * w := by
  have hne : cross u w ≠ 0 := huw
  have h1 : cross (((cross z w / cross u w : ℝ) : ℂ) * u + ((cross u z / cross u w : ℝ) : ℂ) * w - z) u
      = 0 := by
    rw [cross_sub_left, cross_add_left, cross_smul_left, cross_smul_left, cross_self,
      cross_swap w u, cross_swap z u]
    field_simp [hne]
    ring
  have h2 : cross (((cross z w / cross u w : ℝ) : ℂ) * u + ((cross u z / cross u w : ℝ) : ℂ) * w - z) w
      = 0 := by
    rw [cross_sub_left, cross_add_left, cross_smul_left, cross_smul_left, cross_self]
    field_simp [hne]
    ring
  have h3 := cross_eq_zero_of_both_zero huw h1 h2
  exact (sub_eq_zero.1 h3).symm

/-- The argument of a negation, modulo `2π`. -/
lemma arg_neg_eq_arg_add_pi_or_sub (y : ℂ) (hy : y ≠ 0) :
    (Complex.arg (-y) = Complex.arg y + Real.pi) ∨ (Complex.arg (-y) = Complex.arg y - Real.pi) := by
  obtain ⟨m, hm⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1
    (Complex.arg_neg_coe_angle hy)
  have h2 : Complex.arg (-y) = Complex.arg y + Real.pi + 2 * Real.pi * m := by
    linarith [hm]
  have hm1 : m = 0 ∨ m = -1 := by
    have h4 : -Real.pi < Complex.arg (-y) := Complex.neg_pi_lt_arg _
    have h5 : Complex.arg (-y) ≤ Real.pi := Complex.arg_le_pi _
    have h6 : -Real.pi < Complex.arg y := Complex.neg_pi_lt_arg _
    have h7 : Complex.arg y ≤ Real.pi := Complex.arg_le_pi _
    have h8 : (0:ℝ) < 2 * Real.pi := by positivity
    by_contra hne
    push Not at hne
    rcases lt_or_gt_of_ne hne.1 with hm' | hm'
    · have hm'' : m ≤ (-2 : ℤ) := by
        have h9 : m ≠ -1 := hne.2
        omega
      have h11 : (m : ℝ) ≤ -2 := by exact_mod_cast hm''
      have h12 : (2:ℝ) * Real.pi * m ≤ (2:ℝ) * Real.pi * (-2 : ℝ) := by
        apply mul_le_mul_of_nonneg_left h11 (by positivity)
      nlinarith [h2, h4, h7, h8, h12]
    · have hm'' : (1 : ℤ) ≤ m := by omega
      have h11 : (1 : ℝ) ≤ m := by exact_mod_cast hm''
      have h12 : (2:ℝ) * Real.pi * 1 ≤ (2:ℝ) * Real.pi * m := by
        apply mul_le_mul_of_nonneg_left h11 (by positivity)
      nlinarith [h2, h5, h6, h8, h12]
  rcases hm1 with hm1 | hm1
  · left
    rw [hm1, Int.cast_zero, mul_zero, add_zero] at h2
    exact h2
  · right
    rw [hm1, Int.cast_neg, Int.cast_one, mul_neg, mul_one] at h2
    linarith [h2]

/-- `arcsin t ≥ t` for `t ∈ [0, 1]`, applied to `t = 1/d`. -/
lemma one_div_le_arcsin_one_div {d : ℝ} (hd : 2 < d) : 1 / d ≤ Real.arcsin (1 / d) := by
  have hd0 : (0:ℝ) < d := by linarith
  have h1 : (0:ℝ) < 1 / d := by positivity
  have h2 : 1 / d ≤ 1 := by
    rw [div_le_one₀ hd0]
    linarith
  have h3 : Real.sin (Real.arcsin (1 / d)) = 1 / d := Real.sin_arcsin (by linarith) h2
  have h4 : 0 ≤ Real.arcsin (1 / d) := Real.arcsin_nonneg.2 h1.le
  calc 1 / d = Real.sin (Real.arcsin (1 / d)) := h3.symm
    _ ≤ Real.arcsin (1 / d) := Real.sin_le h4

/-- `arcsin t > t` for `t ∈ (0, 1]`, applied to `t = 1/d`. -/
lemma one_div_lt_arcsin_one_div {d : ℝ} (hd : 2 < d) : 1 / d < Real.arcsin (1 / d) := by
  have hd0 : (0:ℝ) < d := by linarith
  have h1 : (0:ℝ) < 1 / d := by positivity
  have h2 : 1 / d ≤ 1 := by
    rw [div_le_one₀ hd0]
    linarith
  have h3 : Real.sin (Real.arcsin (1 / d)) = 1 / d := Real.sin_arcsin (by linarith) h2
  have h4 : 0 < Real.arcsin (1 / d) := Real.arcsin_pos.2 h1
  calc 1 / d = Real.sin (Real.arcsin (1 / d)) := h3.symm
    _ < Real.arcsin (1 / d) := Real.sin_lt h4

/-- Row bound at any centre: the sum of `1/d` over the other centres, doubled,
is strictly less than `π` (kalva's "first paragraph" bound). -/
lemma row_bound_nonvertex (hn : 3 ≤ n) (hlines : NoLineMeetsThree O) (k : Fin n) :
    2 * (∑ j ∈ univ.erase k, 1 / ‖O j - O k‖) < Real.pi := by
  apply row_bound_nonvertex_mock hn
  · exact fun i j hi hj hij => arg_toIocMod_ne hn hlines hi.symm hj.symm hij
  · intro i j hi hj hij
    obtain ⟨h1, h2⟩ := sector_gap hn hlines hi.symm hj.symm hij
    have e1 := one_div_le_arcsin_one_div (two_lt_dist hn hlines hi)
    have e2 := one_div_le_arcsin_one_div (two_lt_dist hn hlines hj)
    exact ⟨by linarith [e1, e2, h1], by linarith [e1, e2, h2]⟩
  · intro j hj
    simpa using toIocMod_mem_Ioc Real.pi_pos 0 (Complex.arg (O j - O k))

snip end

lemma cross_smul_right (t : ℝ) (x y : ℂ) : cross x ((t : ℂ) * y) = t * cross x y := by
  simp only [cross_eq_re_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- If two directions from `v` lie in a common open half-circle window and the first
window representative is smaller than the second, then their cross product is positive. -/
lemma cross_pos_of_window_lt {v p q : ℂ} {A : ℝ}
    (hp0 : p - v ≠ 0) (hq0 : q - v ≠ 0)
    (hp : toIocMod Real.two_pi_pos A (Complex.arg (p - v)) ∈ Set.Ioo A (A + Real.pi))
    (hq : toIocMod Real.two_pi_pos A (Complex.arg (q - v)) ∈ Set.Ioo A (A + Real.pi))
    (hlt : toIocMod Real.two_pi_pos A (Complex.arg (p - v)) <
      toIocMod Real.two_pi_pos A (Complex.arg (q - v))) :
    0 < cross (p - v) (q - v) := by
  rw [cross_pos_iff _ _ hp0 hq0]
  set αp := toIocMod Real.two_pi_pos A (Complex.arg (p - v)) with hαp
  set αq := toIocMod Real.two_pi_pos A (Complex.arg (q - v)) with hαq
  set mp := toIocDiv Real.two_pi_pos A (Complex.arg (p - v)) with hmp
  set mq := toIocDiv Real.two_pi_pos A (Complex.arg (q - v)) with hmq
  have h1 : A < αp ∧ αp < A + Real.pi := hp
  have h2 : A < αq ∧ αq < A + Real.pi := hq
  have hlt' : αp < αq := hlt
  have e1 : αp + mp • (2 * Real.pi) = Complex.arg (p - v) :=
    toIocMod_add_toIocDiv_zsmul Real.two_pi_pos A (Complex.arg (p - v))
  have e2 : αq + mq • (2 * Real.pi) = Complex.arg (q - v) :=
    toIocMod_add_toIocDiv_zsmul Real.two_pi_pos A (Complex.arg (q - v))
  have hdiff : Complex.arg (q - v) - Complex.arg (p - v)
      = (αq - αp) + (mq - mp) • (2 * Real.pi) := by
    rw [← e1, ← e2, zsmul_eq_mul, zsmul_eq_mul, zsmul_eq_mul]
    push_cast
    ring
  rw [hdiff, toIocMod_add_zsmul]
  have h5 : toIocMod Real.two_pi_pos 0 (αq - αp) = αq - αp := by
    rw [toIocMod_eq_self Real.two_pi_pos]
    constructor
    · linarith [hlt']
    · linarith [h1.1, h2.2, Real.pi_pos]
  rw [h5]
  exact ⟨by linarith [hlt'], by linarith [h1.1, h2.2]⟩

/-- The angle between two rays equals the absolute difference of any window arguments,
provided that difference is less than `π`. -/
lemma uangle_eq_abs_sub_of_abs_lt {p x y : ℂ} {c : ℝ}
    (hx0 : x - p ≠ 0) (hy0 : y - p ≠ 0)
    (h : |toIocMod Real.two_pi_pos c (Complex.arg (x - p)) -
      toIocMod Real.two_pi_pos c (Complex.arg (y - p))| < Real.pi) :
    uangle (x - p) (y - p) =
      |toIocMod Real.two_pi_pos c (Complex.arg (x - p)) -
        toIocMod Real.two_pi_pos c (Complex.arg (y - p))| := by
  set αx := toIocMod Real.two_pi_pos c (Complex.arg (x - p)) with hαx
  set αy := toIocMod Real.two_pi_pos c (Complex.arg (y - p)) with hαy
  have hratio : (Complex.arg ((x - p) / (y - p)) : Real.Angle) =
      ((αx - αy : ℝ) : Real.Angle) := by
    rw [Complex.arg_div_coe_angle hx0 hy0, ← Real.Angle.coe_toIocMod
      (Complex.arg (x - p)) c,
      ← Real.Angle.coe_toIocMod (Complex.arg (y - p)) c,
      Real.Angle.coe_sub]
  have h4 : toIocMod Real.two_pi_pos (-Real.pi) (αx - αy) = αx - αy := by
    rw [toIocMod_eq_self Real.two_pi_pos]
    constructor
    · have h1 := (abs_lt.1 h).1
      linarith
    · have h2 := (abs_lt.1 h).2
      linarith
  have e4 : Complex.arg ((x - p) / (y - p)) = αx - αy := by
    obtain ⟨m, hm⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 hratio
    have h2 : toIocMod Real.two_pi_pos (-Real.pi) (Complex.arg ((x - p) / (y - p)))
        = toIocMod Real.two_pi_pos (-Real.pi) (αx - αy) := by
      have e : Complex.arg ((x - p) / (y - p)) = (αx - αy) + m • (2 * Real.pi) := by
        rw [zsmul_eq_mul]
        linarith [hm]
      rw [e, toIocMod_add_zsmul]
    have h3 : toIocMod Real.two_pi_pos (-Real.pi) (Complex.arg ((x - p) / (y - p)))
        = Complex.arg ((x - p) / (y - p)) := by
      rw [toIocMod_eq_self Real.two_pi_pos]
      exact ⟨Complex.neg_pi_lt_arg _, by linarith [Complex.arg_le_pi ((x - p) / (y - p))]⟩
    rw [← h3, h2, h4]
  rw [uangle, e4]

/-- If the pairwise unoriented angles from `p` equal the absolute differences of a real
function `f`, the spread equals the max minus min of `f` over `S.erase p`. -/
lemma spreadIn_eq_image_max_sub_min {S : Finset ℂ} {p : ℂ} (hp : p ∈ S)
    (hne : (S.erase p).Nonempty) {f : ℂ → ℝ}
    (hf : ∀ x ∈ S, ∀ y ∈ S, x ≠ p → y ≠ p → uangle (x - p) (y - p) = |f x - f y|) :
    spreadIn S p = ((S.erase p).image f).max' (Finset.Nonempty.image hne f) -
      ((S.erase p).image f).min' (Finset.Nonempty.image hne f) := by
  set s := S.erase p with hs
  set img := s.image f with himg
  have himg_ne : img.Nonempty := Finset.Nonempty.image hne _
  have hmin_le_max : img.min' himg_ne ≤ img.max' himg_ne :=
    Finset.min'_le img (img.max' himg_ne) (Finset.max'_mem _ _)
  show spreadIn S p = img.max' himg_ne - img.min' himg_ne
  have h_bdd : BddAbove (((S ×ˢ S).image fun ab : ℂ × ℂ => uangle (ab.1 - p) (ab.2 - p)) : Set ℝ) := by
    refine ⟨Real.pi, ?_⟩
    intro y hy
    obtain ⟨ab, hab_mem, hab_eq⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    rw [← hab_eq]
    exact (uangle_mem_Icc _ _).2
  apply le_antisymm
  · apply csSup_le
    · exact ⟨uangle (p - p) (p - p), Finset.mem_coe.2 (Finset.mem_image.2 ⟨(p, p),
        Finset.mem_product.2 ⟨hp, hp⟩, rfl⟩)⟩
    · intro y hy
      obtain ⟨⟨x, y'⟩, hxy_mem, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
      show uangle (x - p) (y' - p) ≤ img.max' himg_ne - img.min' himg_ne
      by_cases hx : x = p
      · rw [hx]
        rw [show p - p = 0 by ring]
        have h1 : uangle 0 (y' - p) = 0 := by
          rw [uangle, zero_div, Complex.arg_zero, abs_zero]
        rw [h1]
        linarith [hmin_le_max]
      by_cases hy' : y' = p
      · rw [hy']
        rw [show p - p = 0 by ring]
        have h1 : uangle (x - p) 0 = 0 := by
          rw [uangle, div_zero, Complex.arg_zero, abs_zero]
        rw [h1]
        linarith [hmin_le_max]
      · have hx_S : x ∈ S := (Finset.mem_product.1 hxy_mem).1
        have hy_S : y' ∈ S := (Finset.mem_product.1 hxy_mem).2
        rw [hf x hx_S y' hy_S hx hy']
        have hi_mem : f x ∈ img := Finset.mem_image.2 ⟨x, mem_erase.2 ⟨hx, hx_S⟩, rfl⟩
        have hj_mem : f y' ∈ img := Finset.mem_image.2 ⟨y', mem_erase.2 ⟨hy', hy_S⟩, rfl⟩
        have h2 := Finset.min'_le img _ hi_mem
        have h3 := Finset.le_max' img _ hj_mem
        have h4 := Finset.min'_le img _ hj_mem
        have h5 := Finset.le_max' img _ hi_mem
        rw [abs_le]
        constructor <;> linarith
  · apply le_csSup
    · exact h_bdd
    · obtain ⟨i₁, hi₁S, hi₁k, hi₁⟩ := (show ∃ q ∈ S, q ≠ p ∧ f q = img.min' himg_ne from by
        obtain ⟨g, hg_mem, hg_eq⟩ := Finset.mem_image.1 (Finset.min'_mem img himg_ne)
        exact ⟨g, (mem_erase.1 hg_mem).2, (mem_erase.1 hg_mem).1, hg_eq⟩)
      obtain ⟨i₂, hi₂S, hi₂k, hi₂⟩ := (show ∃ q ∈ S, q ≠ p ∧ f q = img.max' himg_ne from by
        obtain ⟨g, hg_mem, hg_eq⟩ := Finset.mem_image.1 (Finset.max'_mem img himg_ne)
        exact ⟨g, (mem_erase.1 hg_mem).2, (mem_erase.1 hg_mem).1, hg_eq⟩)
      have heq : uangle (i₁ - p) (i₂ - p) = img.max' himg_ne - img.min' himg_ne := by
        have h0 : 0 ≤ img.max' himg_ne - img.min' himg_ne := sub_nonneg.mpr hmin_le_max
        rw [hf i₁ hi₁S i₂ hi₂S hi₁k hi₂k, hi₁, hi₂, abs_sub_comm]
        exact abs_of_nonneg h0
      rw [← heq]
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨(i₁, i₂),
        Finset.mem_product.2 ⟨hi₁S, hi₂S⟩, rfl⟩)


lemma cross_pos_at_max {T : Finset ℂ} {v a : ℂ} {A : ℝ}
    (hwin : ∀ q ∈ T, toIocMod Real.two_pi_pos A (Complex.arg (q - v)) ∈ Set.Ioo A (A + Real.pi))
    (hinj : ∀ q₁ ∈ T, ∀ q₂ ∈ T,
      toIocMod Real.two_pi_pos A (Complex.arg (q₁ - v)) =
        toIocMod Real.two_pi_pos A (Complex.arg (q₂ - v)) → q₁ = q₂)
    (ha : a ∈ T)
    (hmax : ∀ q ∈ T, toIocMod Real.two_pi_pos A (Complex.arg (q - v)) ≤
      toIocMod Real.two_pi_pos A (Complex.arg (a - v)))
    (hv : v ∉ T) :
    ∀ q ∈ T, q ≠ a → 0 < cross (v - a) (q - a) := by
  intro q hq hqa
  have hav : a - v ≠ 0 := sub_ne_zero.mpr (fun h => hv (h ▸ ha))
  have hqv : q - v ≠ 0 := sub_ne_zero.mpr (fun h => hv (h ▸ hq))
  have hva : v - a ≠ 0 := by
    rw [show v - a = -(a - v) from by ring]
    exact neg_ne_zero.mpr hav
  have hne : toIocMod Real.two_pi_pos A (Complex.arg (q - v)) ≠
      toIocMod Real.two_pi_pos A (Complex.arg (a - v)) := by
    intro h
    exact hqa (hinj q hq a ha h)
  have hlt : toIocMod Real.two_pi_pos A (Complex.arg (q - v)) <
      toIocMod Real.two_pi_pos A (Complex.arg (a - v)) :=
    lt_of_le_of_ne (hmax q hq) hne
  have hkey : cross (v - a) (q - a) = -cross (q - v) (v - a) := by
    have e : q - a = (q - v) + (v - a) := by ring
    rw [e, cross_add_right, cross_self, add_zero, cross_swap (v - a) (q - v)]
  rw [hkey, neg_pos, cross_neg_iff _ _ hqv hva]
  set αa := toIocMod Real.two_pi_pos A (Complex.arg (a - v)) with hαa
  set αq := toIocMod Real.two_pi_pos A (Complex.arg (q - v)) with hαq
  set ma := toIocDiv Real.two_pi_pos A (Complex.arg (a - v)) with hma
  set mq := toIocDiv Real.two_pi_pos A (Complex.arg (q - v)) with hmq
  have e1 : αa + ma • (2 * Real.pi) = Complex.arg (a - v) :=
    toIocMod_add_toIocDiv_zsmul Real.two_pi_pos A (Complex.arg (a - v))
  have e2 : αq + mq • (2 * Real.pi) = Complex.arg (q - v) :=
    toIocMod_add_toIocDiv_zsmul Real.two_pi_pos A (Complex.arg (q - v))
  have h1 : A < αa ∧ αa < A + Real.pi := hwin a ha
  have h2 : A < αq ∧ αq < A + Real.pi := hwin q hq
  have hneg : v - a = -(a - v) := by ring
  rcases arg_neg_eq_arg_add_pi_or_sub (a - v) hav with harg | harg
  · have hdiff : Complex.arg (v - a) - Complex.arg (q - v)
        = (αa - αq + Real.pi) + (ma - mq) • (2 * Real.pi) := by
      rw [hneg, harg, ← e1, ← e2]
      simp only [zsmul_eq_mul]
      push_cast
      ring
    rw [hdiff, toIocMod_add_zsmul]
    have hself : toIocMod Real.two_pi_pos 0 (αa - αq + Real.pi) = αa - αq + Real.pi := by
      rw [toIocMod_eq_self Real.two_pi_pos]
      refine ⟨?_, ?_⟩ <;> linarith [hlt, h1.1, h1.2, h2.1, h2.2, Real.pi_pos]
    rw [hself]
    exact ⟨by linarith [hlt, h1.1, h1.2, h2.1, h2.2, Real.pi_pos],
      by linarith [hlt, h1.1, h1.2, h2.1, h2.2, Real.pi_pos]⟩
  · have hdiff : Complex.arg (v - a) - Complex.arg (q - v)
        = (αa - αq - Real.pi) + (ma - mq) • (2 * Real.pi) := by
      rw [hneg, harg, ← e1, ← e2]
      simp only [zsmul_eq_mul]
      push_cast
      ring
    rw [hdiff, toIocMod_add_zsmul]
    have hplus : toIocMod Real.two_pi_pos 0 ((αa - αq - Real.pi) + (1 : ℤ) • (2 * Real.pi))
        = toIocMod Real.two_pi_pos 0 (αa - αq - Real.pi) :=
      toIocMod_add_zsmul Real.two_pi_pos 0 (αa - αq - Real.pi) 1
    rw [one_zsmul] at hplus
    have hself : toIocMod Real.two_pi_pos 0 ((αa - αq - Real.pi) + 2 * Real.pi)
        = (αa - αq - Real.pi) + 2 * Real.pi := by
      rw [toIocMod_eq_self Real.two_pi_pos]
      refine ⟨?_, ?_⟩ <;> linarith [hlt, h1.1, h1.2, h2.1, h2.2, Real.pi_pos]
    have hrep : toIocMod Real.two_pi_pos 0 (αa - αq - Real.pi)
        = (αa - αq - Real.pi) + 2 * Real.pi := by
      rw [← hplus]
      exact hself
    rw [hrep]
    exact ⟨by linarith [hlt, h1.1, h1.2, h2.1, h2.2, Real.pi_pos],
      by linarith [hlt, h1.1, h1.2, h2.1, h2.2, Real.pi_pos]⟩

lemma cross_neg_at_min {T : Finset ℂ} {v b : ℂ} {A : ℝ}
    (hwin : ∀ q ∈ T, toIocMod Real.two_pi_pos A (Complex.arg (q - v)) ∈ Set.Ioo A (A + Real.pi))
    (hinj : ∀ q₁ ∈ T, ∀ q₂ ∈ T,
      toIocMod Real.two_pi_pos A (Complex.arg (q₁ - v)) =
        toIocMod Real.two_pi_pos A (Complex.arg (q₂ - v)) → q₁ = q₂)
    (hb : b ∈ T)
    (hmin : ∀ q ∈ T, toIocMod Real.two_pi_pos A (Complex.arg (b - v)) ≤
      toIocMod Real.two_pi_pos A (Complex.arg (q - v)))
    (hv : v ∉ T) :
    ∀ q ∈ T, q ≠ b → cross (v - b) (q - b) < 0 := by
  intro q hq hqb
  have hbv : b - v ≠ 0 := sub_ne_zero.mpr (fun h => hv (h ▸ hb))
  have hqv : q - v ≠ 0 := sub_ne_zero.mpr (fun h => hv (h ▸ hq))
  have hvb : v - b ≠ 0 := by
    rw [show v - b = -(b - v) from by ring]
    exact neg_ne_zero.mpr hbv
  have hne : toIocMod Real.two_pi_pos A (Complex.arg (b - v)) ≠
      toIocMod Real.two_pi_pos A (Complex.arg (q - v)) := by
    intro h
    exact hqb (hinj b hb q hq h).symm
  have hlt : toIocMod Real.two_pi_pos A (Complex.arg (b - v)) <
      toIocMod Real.two_pi_pos A (Complex.arg (q - v)) :=
    lt_of_le_of_ne (hmin q hq) hne
  have hkey : cross (v - b) (q - b) = -cross (q - v) (v - b) := by
    have e : q - b = (q - v) + (v - b) := by ring
    rw [e, cross_add_right, cross_self, add_zero, cross_swap (v - b) (q - v)]
  rw [hkey, neg_lt_zero, cross_pos_iff _ _ hqv hvb]
  set αb := toIocMod Real.two_pi_pos A (Complex.arg (b - v)) with hαb
  set αq := toIocMod Real.two_pi_pos A (Complex.arg (q - v)) with hαq
  set mb := toIocDiv Real.two_pi_pos A (Complex.arg (b - v)) with hmb
  set mq := toIocDiv Real.two_pi_pos A (Complex.arg (q - v)) with hmq
  have e1 : αb + mb • (2 * Real.pi) = Complex.arg (b - v) :=
    toIocMod_add_toIocDiv_zsmul Real.two_pi_pos A (Complex.arg (b - v))
  have e2 : αq + mq • (2 * Real.pi) = Complex.arg (q - v) :=
    toIocMod_add_toIocDiv_zsmul Real.two_pi_pos A (Complex.arg (q - v))
  have h1 : A < αb ∧ αb < A + Real.pi := hwin b hb
  have h2 : A < αq ∧ αq < A + Real.pi := hwin q hq
  have hneg : v - b = -(b - v) := by ring
  rcases arg_neg_eq_arg_add_pi_or_sub (b - v) hbv with harg | harg
  · have hdiff : Complex.arg (v - b) - Complex.arg (q - v)
        = (αb - αq + Real.pi) + (mb - mq) • (2 * Real.pi) := by
      rw [hneg, harg, ← e1, ← e2]
      simp only [zsmul_eq_mul]
      push_cast
      ring
    rw [hdiff, toIocMod_add_zsmul]
    have hself : toIocMod Real.two_pi_pos 0 (αb - αq + Real.pi) = αb - αq + Real.pi := by
      rw [toIocMod_eq_self Real.two_pi_pos]
      refine ⟨?_, ?_⟩ <;> linarith [hlt, h1.1, h1.2, h2.1, h2.2, Real.pi_pos]
    rw [hself]
    exact ⟨by linarith [hlt, h1.1, h1.2, h2.1, h2.2, Real.pi_pos],
      by linarith [hlt, h1.1, h1.2, h2.1, h2.2, Real.pi_pos]⟩
  · have hdiff : Complex.arg (v - b) - Complex.arg (q - v)
        = (αb - αq - Real.pi) + (mb - mq) • (2 * Real.pi) := by
      rw [hneg, harg, ← e1, ← e2]
      simp only [zsmul_eq_mul]
      push_cast
      ring
    rw [hdiff, toIocMod_add_zsmul]
    have hplus : toIocMod Real.two_pi_pos 0 ((αb - αq - Real.pi) + (1 : ℤ) • (2 * Real.pi))
        = toIocMod Real.two_pi_pos 0 (αb - αq - Real.pi) :=
      toIocMod_add_zsmul Real.two_pi_pos 0 (αb - αq - Real.pi) 1
    rw [one_zsmul] at hplus
    have hself : toIocMod Real.two_pi_pos 0 ((αb - αq - Real.pi) + 2 * Real.pi)
        = (αb - αq - Real.pi) + 2 * Real.pi := by
      rw [toIocMod_eq_self Real.two_pi_pos]
      refine ⟨?_, ?_⟩ <;> linarith [hlt, h1.1, h1.2, h2.1, h2.2, Real.pi_pos]
    have hrep : toIocMod Real.two_pi_pos 0 (αb - αq - Real.pi)
        = (αb - αq - Real.pi) + 2 * Real.pi := by
      rw [← hplus]
      exact hself
    rw [hrep]
    exact ⟨by linarith [hlt, h1.1, h1.2, h2.1, h2.2, Real.pi_pos],
      by linarith [hlt, h1.1, h1.2, h2.1, h2.2, Real.pi_pos]⟩


lemma exposed_of_cross_pos {S : Finset ℂ} {v c : ℂ} (hvc : v ≠ c)
    (h : ∀ q ∈ S, q ≠ c → q ≠ v → 0 < cross (v - c) (q - c)) :
    ∃ u : ℂ, u ≠ 0 ∧ ∀ q ∈ S, q ≠ c → 0 < (conj u * (q - c)).re := by
  classical
  have hwne : v - c ≠ 0 := sub_ne_zero.mpr hvc
  set T := (S.erase c).erase v with hTdef
  obtain ⟨ε, hε0, hεle⟩ : ∃ ε : ℝ, 0 < ε ∧
      ∀ q ∈ T, ε ≤ cross (v - c) (q - c) / (2 * |(conj (v - c) * (q - c)).re| + 1) := by
    by_cases hT : T.Nonempty
    · set E := T.image
        (fun q => cross (v - c) (q - c) / (2 * |(conj (v - c) * (q - c)).re| + 1)) with hEdef
      have hE : E.Nonempty := hT.image _
      refine ⟨min (E.min' hE) 1, lt_min_iff.2 ⟨?_, one_pos⟩, ?_⟩
      · rw [Finset.lt_min'_iff]
        rintro y hy
        rw [hEdef, Finset.mem_image] at hy
        obtain ⟨q, hqT, rfl⟩ := hy
        rw [hTdef] at hqT
        obtain ⟨hqv, hqS'⟩ := Finset.mem_erase.1 hqT
        obtain ⟨hqc, hqS⟩ := Finset.mem_erase.1 hqS'
        exact div_pos (h q hqS hqc hqv) (by positivity)
      · intro q hqT
        exact le_trans (min_le_left _ _)
          (Finset.min'_le _ _ (Finset.mem_image.2 ⟨q, hqT, rfl⟩))
    · exact ⟨1, one_pos, fun q hqT => absurd ⟨q, hqT⟩ hT⟩
  set u := Complex.I * (v - c) + (ε : ℂ) * (v - c) with hu
  have hid : ∀ z : ℂ, (conj u * z).re = cross (v - c) z + ε * (conj (v - c) * z).re := by
    intro z
    have hconj : conj u = (-Complex.I) * conj (v - c) + (ε : ℂ) * conj (v - c) := by
      rw [hu, map_add, map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal]
    rw [hconj]
    have hmul : ((-Complex.I) * conj (v - c) + (ε : ℂ) * conj (v - c)) * z
        = (-Complex.I) * (conj (v - c) * z) + (ε : ℂ) * (conj (v - c) * z) := by
      ring
    rw [hmul]
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_re,
      Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im]
    rw [cross]
    ring
  have hfact : Complex.I * (v - c) + (ε : ℂ) * (v - c) = (Complex.I + (ε : ℂ)) * (v - c) := by
    ring
  have hu0 : u ≠ 0 := by
    rw [hu, hfact]
    apply mul_ne_zero _ hwne
    intro hzero
    have hre : (Complex.I + (ε : ℂ)).re = 0 := by
      rw [hzero]
      simp
    simp only [Complex.add_re, Complex.I_re, Complex.ofReal_re] at hre
    linarith [hε0]
  refine ⟨u, hu0, ?_⟩
  intro q hqS hqc
  rw [hid]
  by_cases hqv : q = v
  · rw [hqv, cross_self]
    have hcomm : conj (v - c) * (v - c) = (v - c) * conj (v - c) := by ring
    have hnorm : (conj (v - c) * (v - c)).re = Complex.normSq (v - c) := by
      rw [hcomm, Complex.mul_conj, Complex.ofReal_re]
    rw [hnorm]
    have hpos : 0 < Complex.normSq (v - c) := Complex.normSq_pos.2 hwne
    have hmul0 : 0 < ε * Complex.normSq (v - c) := mul_pos hε0 hpos
    linarith [hmul0]
  · have hqT : q ∈ T := by
      rw [hTdef]
      exact Finset.mem_erase.2 ⟨hqv, Finset.mem_erase.2 ⟨hqc, hqS⟩⟩
    have hcross : 0 < cross (v - c) (q - c) := h q hqS hqc hqv
    have hle : ε ≤ cross (v - c) (q - c) / (2 * |(conj (v - c) * (q - c)).re| + 1) :=
      hεle q hqT
    set r := (conj (v - c) * (q - c)).re
    have hden : (0 : ℝ) < 2 * |r| + 1 := by positivity
    have hle' : ε * (2 * |r| + 1) ≤ cross (v - c) (q - c) := (le_div_iff₀ hden).1 hle
    have hεr : -ε * |r| ≤ ε * r := by
      rw [neg_mul]
      have h1 := mul_le_mul_of_nonneg_left (neg_abs_le r) hε0.le
      rwa [mul_neg] at h1
    have h3 : ε * |r| ≤ (cross (v - c) (q - c) - ε) / 2 := by linarith [hle']
    have h6 : (0 : ℝ) < (cross (v - c) (q - c) + ε) / 2 := by linarith [hcross, hε0]
    linarith [hεr, h3, h6]


lemma mod_pi_arg_eq_of_window_eq {p q₁ q₂ : ℂ} {A : ℝ}
    (h : toIocMod Real.two_pi_pos A (Complex.arg (q₁ - p)) =
      toIocMod Real.two_pi_pos A (Complex.arg (q₂ - p))) :
    toIocMod Real.pi_pos 0 (Complex.arg (q₁ - p)) =
      toIocMod Real.pi_pos 0 (Complex.arg (q₂ - p)) := by
  have e1 := toIocMod_add_toIocDiv_zsmul Real.two_pi_pos A (Complex.arg (q₁ - p))
  have e2 := toIocMod_add_toIocDiv_zsmul Real.two_pi_pos A (Complex.arg (q₂ - p))
  rw [h] at e1
  set α := toIocMod Real.two_pi_pos A (Complex.arg (q₂ - p)) with hα
  set m1 := toIocDiv Real.two_pi_pos A (Complex.arg (q₁ - p)) with hm1
  set m2 := toIocDiv Real.two_pi_pos A (Complex.arg (q₂ - p)) with hm2
  have hm1' : (m1 • (2 * Real.pi)) = (2 * m1) • Real.pi := by
    rw [zsmul_eq_mul, zsmul_eq_mul]; push_cast; ring
  have hm2' : (m2 • (2 * Real.pi)) = (2 * m2) • Real.pi := by
    rw [zsmul_eq_mul, zsmul_eq_mul]; push_cast; ring
  rw [← e1, ← e2, hm1', hm2', toIocMod_add_zsmul, toIocMod_add_zsmul]

lemma cross_ne_zero_of_arg_ne {p q r : ℂ}
    (hqp : q - p ≠ 0) (hrp : r - p ≠ 0)
    (hdist : toIocMod Real.pi_pos 0 (Complex.arg (q - p)) ≠
      toIocMod Real.pi_pos 0 (Complex.arg (r - p))) :
    cross (q - p) (r - p) ≠ 0 := by
  intro hc
  have him : ((r - p) / (q - p)).im = 0 := by
    rw [im_div_eq_cross_div_normSq, hc, zero_div]
  rcases le_or_gt 0 ((r - p) / (q - p)).re with hre | hre
  · have harg : Complex.arg ((r - p) / (q - p)) = 0 :=
      Complex.arg_eq_zero_iff.2 ⟨hre, him⟩
    have hratio : (Complex.arg ((r - p) / (q - p)) : Real.Angle) =
        ((Complex.arg (r - p) - Complex.arg (q - p) : ℝ) : Real.Angle) := by
      rw [Complex.arg_div_coe_angle hrp hqp, Real.Angle.coe_sub]
    rw [harg] at hratio
    obtain ⟨m, hm⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 hratio
    have h2 : Complex.arg (r - p) = Complex.arg (q - p) + (-2 * m) • Real.pi := by
      rw [zsmul_eq_mul]; push_cast; linarith [hm]
    exact hdist (by rw [h2, toIocMod_add_zsmul])
  · have harg : Complex.arg ((r - p) / (q - p)) = Real.pi :=
      Complex.arg_eq_pi_iff.2 ⟨hre, him⟩
    have hratio : (Complex.arg ((r - p) / (q - p)) : Real.Angle) =
        ((Complex.arg (r - p) - Complex.arg (q - p) : ℝ) : Real.Angle) := by
      rw [Complex.arg_div_coe_angle hrp hqp, Real.Angle.coe_sub]
    rw [harg] at hratio
    obtain ⟨m, hm⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 hratio
    have h2 : Complex.arg (r - p) = Complex.arg (q - p) + (-2 * m + 1) • Real.pi := by
      rw [zsmul_eq_mul]; push_cast; linarith [hm]
    exact hdist (by rw [h2, toIocMod_add_zsmul])


/-- If the representative of `x` relative to the anchor `a` lies in the window anchored
at `c`, then the two anchored representatives agree. -/
lemma toIocMod_anchor_shift (c a x : ℝ)
    (h : toIocMod Real.two_pi_pos a x ∈ Set.Ioc c (c + 2 * Real.pi)) :
    toIocMod Real.two_pi_pos c x = toIocMod Real.two_pi_pos a x := by
  have e := toIocMod_add_toIocDiv_zsmul Real.two_pi_pos a x
  conv_lhs => rw [← e]
  rw [toIocMod_add_zsmul, toIocMod_eq_self Real.two_pi_pos]
  exact h

/-- Coordinates at the left neighbor `a` of `v`: the anchored representatives of the
directions to the other points lie in the open semicircle ahead of `arg (v - a)`, the value
at `v` itself is `arg (v - a)`, and unoriented angles are absolute differences of the
representatives. -/
lemma coord_left {S : Finset ℂ} {v a : ℂ} (hva : v ≠ a)
    (hcross : ∀ x ∈ S, x ≠ a → x ≠ v → 0 < cross (v - a) (x - a)) :
    (∀ x ∈ S, x ≠ a → x ≠ v →
      toIocMod Real.two_pi_pos (Complex.arg (v - a) - Real.pi / 2) (Complex.arg (x - a)) ∈
        Set.Ioo (Complex.arg (v - a)) (Complex.arg (v - a) + Real.pi)) ∧
    (toIocMod Real.two_pi_pos (Complex.arg (v - a) - Real.pi / 2) (Complex.arg (v - a)) =
      Complex.arg (v - a)) ∧
    (∀ x ∈ S, ∀ y ∈ S, x ≠ a → y ≠ a →
      uangle (x - a) (y - a) =
        |toIocMod Real.two_pi_pos (Complex.arg (v - a) - Real.pi / 2) (Complex.arg (x - a)) -
          toIocMod Real.two_pi_pos (Complex.arg (v - a) - Real.pi / 2) (Complex.arg (y - a))|) := by
  have hva' : v - a ≠ 0 := sub_ne_zero.mpr hva
  have hself : toIocMod Real.two_pi_pos (Complex.arg (v - a) - Real.pi / 2)
      (Complex.arg (v - a)) = Complex.arg (v - a) := by
    rw [toIocMod_eq_self Real.two_pi_pos]
    constructor <;> linarith [Real.pi_pos]
  have hmem : ∀ z ∈ S, z ≠ a → z ≠ v →
      toIocMod Real.two_pi_pos (Complex.arg (v - a) - Real.pi / 2) (Complex.arg (z - a)) ∈
        Set.Ioo (Complex.arg (v - a)) (Complex.arg (v - a) + Real.pi) := by
    intro z hz hza hzv
    have hza' : z - a ≠ 0 := sub_ne_zero.mpr hza
    have h1 : 0 < cross (v - a) (z - a) := hcross z hz hza hzv
    have h2 := (cross_pos_iff_arg_mem (v - a) (z - a) hva' hza').1 h1
    have h3 : toIocMod Real.two_pi_pos (Complex.arg (v - a)) (Complex.arg (z - a)) ∈
        Set.Ioc (Complex.arg (v - a) - Real.pi / 2)
          (Complex.arg (v - a) - Real.pi / 2 + 2 * Real.pi) := by
      constructor <;> linarith [h2.1, h2.2, Real.pi_pos]
    have h4 := toIocMod_anchor_shift (Complex.arg (v - a) - Real.pi / 2)
      (Complex.arg (v - a)) (Complex.arg (z - a)) h3
    rw [h4]
    exact h2
  have hmem_Ico : ∀ z ∈ S, z ≠ a →
      toIocMod Real.two_pi_pos (Complex.arg (v - a) - Real.pi / 2) (Complex.arg (z - a)) ∈
        Set.Ico (Complex.arg (v - a)) (Complex.arg (v - a) + Real.pi) := by
    intro z hz hza
    by_cases hzv : z = v
    · subst hzv
      rw [hself]
      constructor <;> linarith [Real.pi_pos]
    · have h := hmem z hz hza hzv
      exact ⟨h.1.le, h.2⟩
  refine ⟨hmem, hself, ?_⟩
  intro x hx y hy hxa hya
  have hfx := hmem_Ico x hx hxa
  have hfy := hmem_Ico y hy hya
  have hbound : |toIocMod Real.two_pi_pos (Complex.arg (v - a) - Real.pi / 2)
        (Complex.arg (x - a)) -
      toIocMod Real.two_pi_pos (Complex.arg (v - a) - Real.pi / 2)
        (Complex.arg (y - a))| < Real.pi := by
    rw [abs_lt]
    constructor <;> linarith [hfx.1, hfx.2, hfy.1, hfy.2]
  exact uangle_eq_abs_sub_of_abs_lt (sub_ne_zero.mpr hxa) (sub_ne_zero.mpr hya) hbound

/-- Coordinates at the right neighbor `b` of `v`: the anchored representatives of the
directions to the other points lie in the open semicircle behind `arg (v - b)`, the value
at `v` itself is `arg (v - b)`, and unoriented angles are absolute differences of the
representatives. -/
lemma coord_right {S : Finset ℂ} {v b : ℂ} (hvb : v ≠ b)
    (hcross : ∀ x ∈ S, x ≠ b → x ≠ v → cross (v - b) (x - b) < 0) :
    (∀ x ∈ S, x ≠ b → x ≠ v →
      toIocMod Real.two_pi_pos (Complex.arg (v - b) - 3 * Real.pi / 2) (Complex.arg (x - b)) ∈
        Set.Ioo (Complex.arg (v - b) - Real.pi) (Complex.arg (v - b))) ∧
    (toIocMod Real.two_pi_pos (Complex.arg (v - b) - 3 * Real.pi / 2) (Complex.arg (v - b)) =
      Complex.arg (v - b)) ∧
    (∀ x ∈ S, ∀ y ∈ S, x ≠ b → y ≠ b →
      uangle (x - b) (y - b) =
        |toIocMod Real.two_pi_pos (Complex.arg (v - b) - 3 * Real.pi / 2) (Complex.arg (x - b)) -
          toIocMod Real.two_pi_pos (Complex.arg (v - b) - 3 * Real.pi / 2) (Complex.arg (y - b))|) := by
  have hvb' : v - b ≠ 0 := sub_ne_zero.mpr hvb
  have hself : toIocMod Real.two_pi_pos (Complex.arg (v - b) - 3 * Real.pi / 2)
      (Complex.arg (v - b)) = Complex.arg (v - b) := by
    rw [toIocMod_eq_self Real.two_pi_pos]
    constructor <;> linarith [Real.pi_pos]
  have hmem : ∀ z ∈ S, z ≠ b → z ≠ v →
      toIocMod Real.two_pi_pos (Complex.arg (v - b) - 3 * Real.pi / 2) (Complex.arg (z - b)) ∈
        Set.Ioo (Complex.arg (v - b) - Real.pi) (Complex.arg (v - b)) := by
    intro z hz hzb hzv
    have hzb' : z - b ≠ 0 := sub_ne_zero.mpr hzb
    have h1 : cross (v - b) (z - b) < 0 := hcross z hz hzb hzv
    have h2 := (cross_neg_iff_arg_mem (v - b) (z - b) hvb' hzb').1 h1
    have h3 : toIocMod Real.two_pi_pos (Complex.arg (v - b) - Real.pi) (Complex.arg (z - b)) ∈
        Set.Ioc (Complex.arg (v - b) - 3 * Real.pi / 2)
          (Complex.arg (v - b) - 3 * Real.pi / 2 + 2 * Real.pi) := by
      constructor <;> linarith [h2.1, h2.2, Real.pi_pos]
    have h4 := toIocMod_anchor_shift (Complex.arg (v - b) - 3 * Real.pi / 2)
      (Complex.arg (v - b) - Real.pi) (Complex.arg (z - b)) h3
    rw [h4]
    exact h2
  have hmem_Ioc : ∀ z ∈ S, z ≠ b →
      toIocMod Real.two_pi_pos (Complex.arg (v - b) - 3 * Real.pi / 2) (Complex.arg (z - b)) ∈
        Set.Ioc (Complex.arg (v - b) - Real.pi) (Complex.arg (v - b)) := by
    intro z hz hzb
    by_cases hzv : z = v
    · subst hzv
      rw [hself]
      constructor <;> linarith [Real.pi_pos]
    · have h := hmem z hz hzb hzv
      exact ⟨h.1, h.2.le⟩
  refine ⟨hmem, hself, ?_⟩
  intro x hx y hy hxb hyb
  have hfx := hmem_Ioc x hx hxb
  have hfy := hmem_Ioc y hy hyb
  have hbound : |toIocMod Real.two_pi_pos (Complex.arg (v - b) - 3 * Real.pi / 2)
        (Complex.arg (x - b)) -
      toIocMod Real.two_pi_pos (Complex.arg (v - b) - 3 * Real.pi / 2)
        (Complex.arg (y - b))| < Real.pi := by
    rw [abs_lt]
    constructor <;> linarith [hfx.1, hfx.2, hfy.1, hfy.2]
  exact uangle_eq_abs_sub_of_abs_lt (sub_ne_zero.mpr hxb) (sub_ne_zero.mpr hyb) hbound

/-- Betweenness at the left neighbor: if `b` and `x` are both strictly counterclockwise of
`v` around `a` and `x` is strictly counterclockwise of `b`, then the coordinate of `b` is
less than the coordinate of `x`. -/
lemma coord_left_lt {v a b x : ℂ} (hva : v ≠ a) (hba : b ≠ a) (hxa : x ≠ a)
    (h1 : 0 < cross (v - a) (b - a)) (h2 : 0 < cross (v - a) (x - a))
    (h3 : 0 < cross (b - a) (x - a)) :
    toIocMod Real.two_pi_pos (Complex.arg (v - a) - Real.pi / 2) (Complex.arg (b - a)) <
      toIocMod Real.two_pi_pos (Complex.arg (v - a) - Real.pi / 2) (Complex.arg (x - a)) := by
  have hva' : v - a ≠ 0 := sub_ne_zero.mpr hva
  have hba' : b - a ≠ 0 := sub_ne_zero.mpr hba
  have hxa' : x - a ≠ 0 := sub_ne_zero.mpr hxa
  set fb := toIocMod Real.two_pi_pos (Complex.arg (v - a) - Real.pi / 2)
    (Complex.arg (b - a)) with hfbdef
  set fx := toIocMod Real.two_pi_pos (Complex.arg (v - a) - Real.pi / 2)
    (Complex.arg (x - a)) with hfxdef
  set θ := toIocMod Real.two_pi_pos 0 (Complex.arg (x - a) - Complex.arg (b - a))
  set mb := toIocDiv Real.two_pi_pos (Complex.arg (v - a) - Real.pi / 2)
    (Complex.arg (b - a))
  set mx := toIocDiv Real.two_pi_pos (Complex.arg (v - a) - Real.pi / 2)
    (Complex.arg (x - a))
  set k := toIocDiv Real.two_pi_pos 0 (Complex.arg (x - a) - Complex.arg (b - a))
  have fb_mem : fb ∈ Set.Ioo (Complex.arg (v - a)) (Complex.arg (v - a) + Real.pi) := by
    have h1' := (cross_pos_iff_arg_mem (v - a) (b - a) hva' hba').1 h1
    have h1ioc : toIocMod Real.two_pi_pos (Complex.arg (v - a)) (Complex.arg (b - a)) ∈
        Set.Ioc (Complex.arg (v - a) - Real.pi / 2)
          (Complex.arg (v - a) - Real.pi / 2 + 2 * Real.pi) := by
      constructor <;> linarith [h1'.1, h1'.2, Real.pi_pos]
    have hshift := toIocMod_anchor_shift (Complex.arg (v - a) - Real.pi / 2)
      (Complex.arg (v - a)) (Complex.arg (b - a)) h1ioc
    rw [hfbdef, hshift]
    exact h1'
  have fx_mem : fx ∈ Set.Ioo (Complex.arg (v - a)) (Complex.arg (v - a) + Real.pi) := by
    have h2' := (cross_pos_iff_arg_mem (v - a) (x - a) hva' hxa').1 h2
    have h2ioc : toIocMod Real.two_pi_pos (Complex.arg (v - a)) (Complex.arg (x - a)) ∈
        Set.Ioc (Complex.arg (v - a) - Real.pi / 2)
          (Complex.arg (v - a) - Real.pi / 2 + 2 * Real.pi) := by
      constructor <;> linarith [h2'.1, h2'.2, Real.pi_pos]
    have hshift := toIocMod_anchor_shift (Complex.arg (v - a) - Real.pi / 2)
      (Complex.arg (v - a)) (Complex.arg (x - a)) h2ioc
    rw [hfxdef, hshift]
    exact h2'
  have hθ : θ ∈ Set.Ioo 0 Real.pi := (cross_pos_iff (b - a) (x - a) hba' hxa').1 h3
  have e1 : fx + mx • (2 * Real.pi) = Complex.arg (x - a) :=
    toIocMod_add_toIocDiv_zsmul Real.two_pi_pos (Complex.arg (v - a) - Real.pi / 2)
      (Complex.arg (x - a))
  have e2 : fb + mb • (2 * Real.pi) = Complex.arg (b - a) :=
    toIocMod_add_toIocDiv_zsmul Real.two_pi_pos (Complex.arg (v - a) - Real.pi / 2)
      (Complex.arg (b - a))
  have e3 : θ + k • (2 * Real.pi) = Complex.arg (x - a) - Complex.arg (b - a) :=
    toIocMod_add_toIocDiv_zsmul Real.two_pi_pos 0 (Complex.arg (x - a) - Complex.arg (b - a))
  have hdiff : fx - fb = θ + (k - mx + mb) • (2 * Real.pi) := by
    have h4 : (fx + mx • (2 * Real.pi)) - (fb + mb • (2 * Real.pi))
        = θ + k • (2 * Real.pi) := by
      rw [e1, e2]
      exact e3.symm
    simp only [zsmul_eq_mul] at h4 ⊢
    push_cast at h4 ⊢
    linear_combination h4
  have hdiff_mem : fx - fb ∈ Set.Ioo (-Real.pi) Real.pi := by
    constructor
    · linarith [fx_mem.1, fb_mem.2]
    · linarith [fx_mem.2, fb_mem.1]
  have hN : ((k - mx + mb : ℤ) : ℝ) * (2 * Real.pi) = (fx - fb) - θ := by
    have h := hdiff
    simp only [zsmul_eq_mul] at h
    linarith [h]
  have hNlt : ((k - mx + mb : ℤ) : ℝ) * (2 * Real.pi) < Real.pi := by
    rw [hN]
    linarith [hdiff_mem.2, hθ.1]
  have hNgt : -2 * Real.pi < ((k - mx + mb : ℤ) : ℝ) * (2 * Real.pi) := by
    rw [hN]
    linarith [hdiff_mem.1, hθ.2]
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hN1 : (-1 : ℝ) < ((k - mx + mb : ℤ) : ℝ) := by
    have h5 : (-1 : ℝ) * (2 * Real.pi) < ((k - mx + mb : ℤ) : ℝ) * (2 * Real.pi) := by
      linarith [hNgt]
    exact (mul_lt_mul_iff_left₀ h2pi).mp h5
  have hN2 : ((k - mx + mb : ℤ) : ℝ) < 1 := by
    have h5 : ((k - mx + mb : ℤ) : ℝ) * (2 * Real.pi) < (1 : ℝ) * (2 * Real.pi) := by
      linarith [hNlt, Real.pi_pos]
    exact (mul_lt_mul_iff_left₀ h2pi).mp h5
  have hN1' : (-1 : ℤ) < k - mx + mb := by exact_mod_cast hN1
  have hN2' : k - mx + mb < 1 := by exact_mod_cast hN2
  have hN0 : k - mx + mb = 0 := by omega
  have hfin : fx - fb = θ := by
    rw [hN0, zero_zsmul, add_zero] at hdiff
    exact hdiff
  linarith [hfin, hθ.1]

/-- Betweenness at the right neighbor: if `a` and `x` are both strictly clockwise of `v`
around `b` and `x` is strictly clockwise of `a`, then the coordinate of `x` is less than
the coordinate of `a`. -/
lemma coord_right_lt {v a b x : ℂ} (hvb : v ≠ b) (hab : a ≠ b) (hxb : x ≠ b)
    (h1 : cross (v - b) (a - b) < 0) (h2 : cross (v - b) (x - b) < 0)
    (h3 : cross (a - b) (x - b) < 0) :
    toIocMod Real.two_pi_pos (Complex.arg (v - b) - 3 * Real.pi / 2) (Complex.arg (x - b)) <
      toIocMod Real.two_pi_pos (Complex.arg (v - b) - 3 * Real.pi / 2) (Complex.arg (a - b)) := by
  have hvb' : v - b ≠ 0 := sub_ne_zero.mpr hvb
  have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hxb' : x - b ≠ 0 := sub_ne_zero.mpr hxb
  set ga := toIocMod Real.two_pi_pos (Complex.arg (v - b) - 3 * Real.pi / 2)
    (Complex.arg (a - b)) with hgadef
  set gx := toIocMod Real.two_pi_pos (Complex.arg (v - b) - 3 * Real.pi / 2)
    (Complex.arg (x - b)) with hgxdef
  set θ := toIocMod Real.two_pi_pos 0 (Complex.arg (x - b) - Complex.arg (a - b))
  set ma := toIocDiv Real.two_pi_pos (Complex.arg (v - b) - 3 * Real.pi / 2)
    (Complex.arg (a - b))
  set mx := toIocDiv Real.two_pi_pos (Complex.arg (v - b) - 3 * Real.pi / 2)
    (Complex.arg (x - b))
  set k := toIocDiv Real.two_pi_pos 0 (Complex.arg (x - b) - Complex.arg (a - b))
  have ga_mem : ga ∈ Set.Ioo (Complex.arg (v - b) - Real.pi) (Complex.arg (v - b)) := by
    have h1' := (cross_neg_iff_arg_mem (v - b) (a - b) hvb' hab').1 h1
    have h1ioc : toIocMod Real.two_pi_pos (Complex.arg (v - b) - Real.pi) (Complex.arg (a - b)) ∈
        Set.Ioc (Complex.arg (v - b) - 3 * Real.pi / 2)
          (Complex.arg (v - b) - 3 * Real.pi / 2 + 2 * Real.pi) := by
      constructor <;> linarith [h1'.1, h1'.2, Real.pi_pos]
    have hshift := toIocMod_anchor_shift (Complex.arg (v - b) - 3 * Real.pi / 2)
      (Complex.arg (v - b) - Real.pi) (Complex.arg (a - b)) h1ioc
    rw [hgadef, hshift]
    exact h1'
  have gx_mem : gx ∈ Set.Ioo (Complex.arg (v - b) - Real.pi) (Complex.arg (v - b)) := by
    have h2' := (cross_neg_iff_arg_mem (v - b) (x - b) hvb' hxb').1 h2
    have h2ioc : toIocMod Real.two_pi_pos (Complex.arg (v - b) - Real.pi) (Complex.arg (x - b)) ∈
        Set.Ioc (Complex.arg (v - b) - 3 * Real.pi / 2)
          (Complex.arg (v - b) - 3 * Real.pi / 2 + 2 * Real.pi) := by
      constructor <;> linarith [h2'.1, h2'.2, Real.pi_pos]
    have hshift := toIocMod_anchor_shift (Complex.arg (v - b) - 3 * Real.pi / 2)
      (Complex.arg (v - b) - Real.pi) (Complex.arg (x - b)) h2ioc
    rw [hgxdef, hshift]
    exact h2'
  have hθ : θ ∈ Set.Ioo Real.pi (2 * Real.pi) :=
    (cross_neg_iff (a - b) (x - b) hab' hxb').1 h3
  have e1 : gx + mx • (2 * Real.pi) = Complex.arg (x - b) :=
    toIocMod_add_toIocDiv_zsmul Real.two_pi_pos (Complex.arg (v - b) - 3 * Real.pi / 2)
      (Complex.arg (x - b))
  have e2 : ga + ma • (2 * Real.pi) = Complex.arg (a - b) :=
    toIocMod_add_toIocDiv_zsmul Real.two_pi_pos (Complex.arg (v - b) - 3 * Real.pi / 2)
      (Complex.arg (a - b))
  have e3 : θ + k • (2 * Real.pi) = Complex.arg (x - b) - Complex.arg (a - b) :=
    toIocMod_add_toIocDiv_zsmul Real.two_pi_pos 0 (Complex.arg (x - b) - Complex.arg (a - b))
  have hdiff : gx - ga = θ + (k - mx + ma) • (2 * Real.pi) := by
    have h4 : (gx + mx • (2 * Real.pi)) - (ga + ma • (2 * Real.pi))
        = θ + k • (2 * Real.pi) := by
      rw [e1, e2]
      exact e3.symm
    simp only [zsmul_eq_mul] at h4 ⊢
    push_cast at h4 ⊢
    linear_combination h4
  have hdiff_mem : gx - ga ∈ Set.Ioo (-Real.pi) Real.pi := by
    constructor
    · linarith [gx_mem.1, ga_mem.2]
    · linarith [gx_mem.2, ga_mem.1]
  have hN : ((k - mx + ma : ℤ) : ℝ) * (2 * Real.pi) = (gx - ga) - θ := by
    have h := hdiff
    simp only [zsmul_eq_mul] at h
    linarith [h]
  have hNlt : ((k - mx + ma : ℤ) : ℝ) * (2 * Real.pi) < 0 := by
    rw [hN]
    linarith [hdiff_mem.2, hθ.1]
  have hNgt : -3 * Real.pi < ((k - mx + ma : ℤ) : ℝ) * (2 * Real.pi) := by
    rw [hN]
    linarith [hdiff_mem.1, hθ.2]
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hN1 : (-2 : ℝ) < ((k - mx + ma : ℤ) : ℝ) := by
    have h5 : (-2 : ℝ) * (2 * Real.pi) < ((k - mx + ma : ℤ) : ℝ) * (2 * Real.pi) := by
      linarith [hNgt, Real.pi_pos]
    exact (mul_lt_mul_iff_left₀ h2pi).mp h5
  have hN2 : ((k - mx + ma : ℤ) : ℝ) < 0 := by
    have h5 : ((k - mx + ma : ℤ) : ℝ) * (2 * Real.pi) < (0 : ℝ) * (2 * Real.pi) := by
      linarith [hNlt]
    exact (mul_lt_mul_iff_left₀ h2pi).mp h5
  have hN1' : (-2 : ℤ) < k - mx + ma := by exact_mod_cast hN1
  have hN2' : k - mx + ma < 0 := by exact_mod_cast hN2
  have hNm1 : k - mx + ma = -1 := by omega
  have hfin : gx - ga = θ - 2 * Real.pi := by
    rw [hNm1, neg_one_zsmul] at hdiff
    linarith [hdiff]
  linarith [hfin, hθ.2]



lemma polygon_ear {S : Finset ℂ} {v a b x : ℂ} {A : ℝ}
    (hwin : ∀ q ∈ S, q ≠ v → toIocMod Real.two_pi_pos A (Complex.arg (q - v)) ∈
      Set.Ioo A (A + Real.pi))
    (hinj : ∀ q₁ ∈ S, q₁ ≠ v → ∀ q₂ ∈ S, q₂ ≠ v →
      toIocMod Real.two_pi_pos A (Complex.arg (q₁ - v)) =
        toIocMod Real.two_pi_pos A (Complex.arg (q₂ - v)) → q₁ = q₂)
    (ha : a ∈ S) (hb : b ∈ S) (hx : x ∈ S) (hvS : v ∈ S)
    (hav : a ≠ v) (hbv : b ≠ v) (hxv : x ≠ v) (hxa : x ≠ a) (hxb : x ≠ b) (hab : a ≠ b)
    (hmax : ∀ q ∈ S, q ≠ v → toIocMod Real.two_pi_pos A (Complex.arg (q - v)) ≤
      toIocMod Real.two_pi_pos A (Complex.arg (a - v)))
    (hmin : ∀ q ∈ S, q ≠ v → toIocMod Real.two_pi_pos A (Complex.arg (b - v)) ≤
      toIocMod Real.two_pi_pos A (Complex.arg (q - v)))
    (hxexp : ∃ u : ℂ, u ≠ 0 ∧ ∀ q ∈ S, q ≠ x → 0 < (conj u * (q - x)).re) :
    0 < cross (b - a) (x - a) ∧ cross (a - b) (x - b) < 0 ∧
      0 < cross (v - x) (b - x) ∧ cross (v - x) (a - x) < 0 := by
  have hbv0 : b - v ≠ 0 := sub_ne_zero.mpr hbv
  have hxv0 : x - v ≠ 0 := sub_ne_zero.mpr hxv
  have hav0 : a - v ≠ 0 := sub_ne_zero.mpr hav
  -- Step 1: strict window order `α b < α x < α a`.
  have hbαx : toIocMod Real.two_pi_pos A (Complex.arg (b - v)) <
      toIocMod Real.two_pi_pos A (Complex.arg (x - v)) := by
    have hne : toIocMod Real.two_pi_pos A (Complex.arg (b - v)) ≠
        toIocMod Real.two_pi_pos A (Complex.arg (x - v)) := by
      intro h
      exact hxb (hinj b hb hbv x hx hxv h).symm
    exact lt_of_le_of_ne (hmin x hx hxv) hne
  have hxαa : toIocMod Real.two_pi_pos A (Complex.arg (x - v)) <
      toIocMod Real.two_pi_pos A (Complex.arg (a - v)) := by
    have hne : toIocMod Real.two_pi_pos A (Complex.arg (x - v)) ≠
        toIocMod Real.two_pi_pos A (Complex.arg (a - v)) := by
      intro h
      exact hxa (hinj x hx hxv a ha hav h)
    exact lt_of_le_of_ne (hmax x hx hxv) hne
  -- Step 2: the three crosses at `v`.
  have hbx' : 0 < cross (b - v) (x - v) :=
    cross_pos_of_window_lt hbv0 hxv0 (hwin b hb hbv) (hwin x hx hxv) hbαx
  have hxa' : 0 < cross (x - v) (a - v) :=
    cross_pos_of_window_lt hxv0 hav0 (hwin x hx hxv) (hwin a ha hav) hxαa
  have hba' : 0 < cross (b - v) (a - v) :=
    cross_pos_of_window_lt hbv0 hav0 (hwin b hb hbv) (hwin a ha hav) (lt_trans hbαx hxαa)
  -- Step 3: the basis is oriented negatively.
  have hAB : cross (a - v) (b - v) < 0 := by
    rw [cross_swap (a - v) (b - v)]
    linarith [hba']
  have hAB0 : cross (a - v) (b - v) ≠ 0 := ne_of_lt hAB
  -- Step 4: Cramer decomposition of `x - v` in the basis `a - v`, `b - v`.
  have hcombo := combo_of_wedge (u := a - v) (w := b - v) (z := x - v) hAB0
  set α' := cross (x - v) (b - v) / cross (a - v) (b - v) with hα'def
  set β' := cross (a - v) (x - v) / cross (a - v) (b - v) with hβ'def
  have hx1 : x - v = (α' : ℂ) * (a - v) + (β' : ℂ) * (b - v) := hcombo
  have hxb'' : cross (x - v) (b - v) < 0 := by
    rw [cross_swap (x - v) (b - v)]
    linarith [hbx']
  have hxa'' : cross (a - v) (x - v) < 0 := by
    rw [cross_swap (a - v) (x - v)]
    linarith [hxa']
  have hα'pos : 0 < α' := by
    rw [hα'def]
    exact div_pos_of_neg_of_neg hxb'' hAB
  have hβ'pos : 0 < β' := by
    rw [hβ'def]
    exact div_pos_of_neg_of_neg hxa'' hAB
  -- Step 5: `1 < α' + β'`, else `x` is a convex combination of `v, a, b`,
  -- contradicting the strict exposure of `x`.
  have hsum : 1 < α' + β' := by
    by_contra hle
    push Not at hle
    have hx0 : x = v + (x - v) := by ring
    have hx2 : x = ((1 - α' - β' : ℝ) : ℂ) * v + (α' : ℂ) * a + (β' : ℂ) * b := by
      rw [hx0, hx1]
      push_cast
      ring
    have hzero : ((1 - α' - β' : ℝ) : ℂ) * (v - x) + (α' : ℂ) * (a - x) +
        (β' : ℂ) * (b - x) = 0 := by
      have hx2' := hx2
      push_cast at hx2'
      push_cast
      linear_combination -hx2'
    obtain ⟨u, _hu0, hu⟩ := hxexp
    have h0 : (conj u * (((1 - α' - β' : ℝ) : ℂ) * (v - x) + (α' : ℂ) * (a - x) +
        (β' : ℂ) * (b - x))).re = 0 := by
      have h := congrArg (fun w => (conj u * w).re) hzero
      simpa using h
    rw [mul_add, mul_add] at h0
    rw [show conj u * (((1 - α' - β' : ℝ) : ℂ) * (v - x)) =
        ((1 - α' - β' : ℝ) : ℂ) * (conj u * (v - x)) from by ring,
      show conj u * ((α' : ℂ) * (a - x)) = (α' : ℂ) * (conj u * (a - x)) from by ring,
      show conj u * ((β' : ℂ) * (b - x)) = (β' : ℂ) * (conj u * (b - x)) from by ring] at h0
    rw [Complex.add_re, Complex.add_re] at h0
    have hre : ∀ (c : ℝ) (z : ℂ), ((c : ℂ) * z).re = c * z.re := by
      intro c z
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [hre (1 - α' - β') (conj u * (v - x)), hre α' (conj u * (a - x)),
      hre β' (conj u * (b - x))] at h0
    have t1 : 0 ≤ (1 - α' - β') * (conj u * (v - x)).re :=
      mul_nonneg (by linarith [hle]) (hu v hvS hxv.symm).le
    have t2 : 0 < α' * (conj u * (a - x)).re := mul_pos hα'pos (hu a ha hxa.symm)
    have t3 : 0 < β' * (conj u * (b - x)).re := mul_pos hβ'pos (hu b hb hxb.symm)
    linarith [h0, t1, t2, t3]
  -- Step 6: the four cross identities, by pure cross algebra.
  have hid1 : cross (b - a) (x - a) = -(α' + β' - 1) * cross (a - v) (b - v) := by
    have e1 : x - a = (x - v) - (a - v) := by ring
    have e2 : b - a = (b - v) - (a - v) := by ring
    rw [e1, e2, hx1]
    simp only [cross_eq_re_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hid2 : cross (a - b) (x - b) = (α' + β' - 1) * cross (a - v) (b - v) := by
    have e1 : x - b = (x - v) - (b - v) := by ring
    have e2 : a - b = (a - v) - (b - v) := by ring
    rw [e1, e2, hx1]
    simp only [cross_eq_re_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hid3 : cross (v - x) (b - x) = -α' * cross (a - v) (b - v) := by
    have e1 : v - x = -(x - v) := by ring
    have e2 : b - x = (b - v) - (x - v) := by ring
    rw [e1, e2, hx1]
    simp only [cross_eq_re_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re,
      Complex.neg_im]
    ring
  have hid4 : cross (v - x) (a - x) = β' * cross (a - v) (b - v) := by
    have e1 : v - x = -(x - v) := by ring
    have e2 : a - x = (a - v) - (x - v) := by ring
    rw [e1, e2, hx1]
    simp only [cross_eq_re_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re,
      Complex.neg_im]
    ring
  -- Step 7: conclude the four signs.
  have hsum' : 0 < α' + β' - 1 := by linarith [hsum]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hid1]
    exact mul_pos_of_neg_of_neg (by linarith [hsum']) hAB
  · rw [hid2]
    exact mul_neg_of_pos_of_neg hsum' hAB
  · rw [hid3]
    exact mul_pos_of_neg_of_neg (by linarith [hα'pos]) hAB
  · rw [hid4]
    exact mul_neg_of_pos_of_neg hβ'pos hAB


lemma exists_exposed_window_max {T : Finset ℂ} {v : ℂ} (hv : v ∈ T) {u : ℂ} (hu0 : u ≠ 0)
    (hu : ∀ q ∈ T, q ≠ v → 0 < (conj u * (q - v)).re)
    (hdist : ∀ q₁ ∈ T, q₁ ≠ v → ∀ q₂ ∈ T, q₂ ≠ v → q₁ ≠ q₂ →
      toIocMod Real.pi_pos 0 (Complex.arg (q₁ - v)) ≠
        toIocMod Real.pi_pos 0 (Complex.arg (q₂ - v)))
    (hne : (T.erase v).Nonempty) :
    ∃ c ∈ T.erase v, (∀ q ∈ T.erase v,
        toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (q - v)) ≤
          toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (c - v))) ∧
      ∃ w : ℂ, w ≠ 0 ∧ ∀ q ∈ T, q ≠ c → 0 < (conj w * (q - c)).re := by
  set α : ℂ → ℝ := fun q => toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2)
    (Complex.arg (q - v))
  set img := (T.erase v).image α
  have himg_ne : img.Nonempty := Finset.Nonempty.image hne _
  obtain ⟨c, hc_mem, hc_eq⟩ := Finset.mem_image.1 (Finset.max'_mem img himg_ne)
  have hmax : ∀ q ∈ T.erase v, toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2)
      (Complex.arg (q - v)) ≤ toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2)
      (Complex.arg (c - v)) := by
    intro q hq
    exact (Finset.le_max' img (α q) (Finset.mem_image.2 ⟨q, hq, rfl⟩)).trans_eq hc_eq.symm
  refine ⟨c, hc_mem, hmax, ?_⟩
  have hvc : v ≠ c := (mem_erase.1 hc_mem).1.symm
  have hwin : ∀ q ∈ T.erase v, toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2)
      (Complex.arg (q - v)) ∈ Set.Ioo (Complex.arg u - Real.pi / 2)
      (Complex.arg u - Real.pi / 2 + Real.pi) := by
    intro q hq
    have hshift : Complex.arg u - Real.pi / 2 + Real.pi = Complex.arg u + Real.pi / 2 := by
      ring
    rw [hshift]
    exact arg_window_of_exposed hu0 (hu q (mem_erase.1 hq).2 (mem_erase.1 hq).1)
      (sub_ne_zero.mpr (mem_erase.1 hq).1)
  have hinj : ∀ q₁ ∈ T.erase v, ∀ q₂ ∈ T.erase v,
      toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (q₁ - v)) =
        toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (q₂ - v)) →
        q₁ = q₂ := by
    intro q₁ hq₁ q₂ hq₂ h
    by_contra hne2
    exact hdist q₁ (mem_erase.1 hq₁).2 (mem_erase.1 hq₁).1 q₂ (mem_erase.1 hq₂).2
      (mem_erase.1 hq₂).1 hne2 (mod_pi_arg_eq_of_window_eq h)
  refine exposed_of_cross_pos (S := T) (v := v) (c := c) hvc ?_
  intro q hqT hqc hqv
  exact cross_pos_at_max (T := T.erase v) (v := v) (a := c)
    (A := Complex.arg u - Real.pi / 2) hwin hinj hc_mem hmax
    (Finset.notMem_erase v T) q (mem_erase.2 ⟨hqv, hqT⟩) hqc

/-- Mirror of `exposed_of_cross_pos`: if every other point is strictly clockwise of the
directed line from `c` to `v`, then `c` is strictly exposed. -/
lemma exposed_of_cross_neg {S : Finset ℂ} {v c : ℂ} (hvc : v ≠ c)
    (h : ∀ q ∈ S, q ≠ c → q ≠ v → cross (v - c) (q - c) < 0) :
    ∃ u : ℂ, u ≠ 0 ∧ ∀ q ∈ S, q ≠ c → 0 < (conj u * (q - c)).re := by
  classical
  have hwne : v - c ≠ 0 := sub_ne_zero.mpr hvc
  set T := (S.erase c).erase v with hTdef
  obtain ⟨ε, hε0, hεle⟩ : ∃ ε : ℝ, 0 < ε ∧
      ∀ q ∈ T, ε ≤ -cross (v - c) (q - c) / (2 * |(conj (v - c) * (q - c)).re| + 1) := by
    by_cases hT : T.Nonempty
    · set E := T.image
        (fun q => -cross (v - c) (q - c) / (2 * |(conj (v - c) * (q - c)).re| + 1)) with hEdef
      have hE : E.Nonempty := hT.image _
      refine ⟨min (E.min' hE) 1, lt_min_iff.2 ⟨?_, one_pos⟩, ?_⟩
      · rw [Finset.lt_min'_iff]
        rintro y hy
        rw [hEdef, Finset.mem_image] at hy
        obtain ⟨q, hqT, rfl⟩ := hy
        rw [hTdef] at hqT
        obtain ⟨hqv, hqS'⟩ := Finset.mem_erase.1 hqT
        obtain ⟨hqc, hqS⟩ := Finset.mem_erase.1 hqS'
        exact div_pos (neg_pos.mpr (h q hqS hqc hqv)) (by positivity)
      · intro q hqT
        exact le_trans (min_le_left _ _)
          (Finset.min'_le _ _ (Finset.mem_image.2 ⟨q, hqT, rfl⟩))
    · exact ⟨1, one_pos, fun q hqT => absurd ⟨q, hqT⟩ hT⟩
  set u := -Complex.I * (v - c) + (ε : ℂ) * (v - c) with hu
  have hid : ∀ z : ℂ, (conj u * z).re = -cross (v - c) z + ε * (conj (v - c) * z).re := by
    intro z
    have hIc : conj (-Complex.I) = Complex.I := by simp
    have hconj : conj u = Complex.I * conj (v - c) + (ε : ℂ) * conj (v - c) := by
      rw [hu, map_add, map_mul, map_mul, hIc, Complex.conj_ofReal]
    rw [hconj]
    have hmul : (Complex.I * conj (v - c) + (ε : ℂ) * conj (v - c)) * z
        = Complex.I * (conj (v - c) * z) + (ε : ℂ) * (conj (v - c) * z) := by
      ring
    rw [hmul]
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    rw [cross]
    ring
  have hfact : -Complex.I * (v - c) + (ε : ℂ) * (v - c) = (-Complex.I + (ε : ℂ)) * (v - c) := by
    ring
  have hu0 : u ≠ 0 := by
    rw [hu, hfact]
    apply mul_ne_zero _ hwne
    intro hzero
    have hre : (-Complex.I + (ε : ℂ)).re = 0 := by
      rw [hzero]
      simp
    simp only [Complex.add_re, Complex.neg_re, Complex.I_re, Complex.ofReal_re] at hre
    linarith [hε0]
  refine ⟨u, hu0, ?_⟩
  intro q hqS hqc
  rw [hid]
  by_cases hqv : q = v
  · rw [hqv, cross_self]
    have hcomm : conj (v - c) * (v - c) = (v - c) * conj (v - c) := by ring
    have hnorm : (conj (v - c) * (v - c)).re = Complex.normSq (v - c) := by
      rw [hcomm, Complex.mul_conj, Complex.ofReal_re]
    rw [hnorm]
    have hpos : 0 < Complex.normSq (v - c) := Complex.normSq_pos.2 hwne
    have hmul0 : 0 < ε * Complex.normSq (v - c) := mul_pos hε0 hpos
    linarith [hmul0]
  · have hqT : q ∈ T := by
      rw [hTdef]
      exact Finset.mem_erase.2 ⟨hqv, Finset.mem_erase.2 ⟨hqc, hqS⟩⟩
    have hcross : cross (v - c) (q - c) < 0 := h q hqS hqc hqv
    have hle : ε ≤ -cross (v - c) (q - c) / (2 * |(conj (v - c) * (q - c)).re| + 1) :=
      hεle q hqT
    set r := (conj (v - c) * (q - c)).re
    have hden : (0 : ℝ) < 2 * |r| + 1 := by positivity
    have hle' : ε * (2 * |r| + 1) ≤ -cross (v - c) (q - c) := (le_div_iff₀ hden).1 hle
    have hεr : -ε * |r| ≤ ε * r := by
      rw [neg_mul]
      have h1 := mul_le_mul_of_nonneg_left (neg_abs_le r) hε0.le
      rwa [mul_neg] at h1
    have h3 : ε * |r| ≤ (-cross (v - c) (q - c) - ε) / 2 := by linarith [hle']
    have h6 : (0 : ℝ) < (-cross (v - c) (q - c) + ε) / 2 := by linarith [hcross, hε0]
    linarith [hεr, h3, h6]

/-- At an exposed point `v`, the window-min direction is attained at a point `c` that is
itself strictly exposed. -/
lemma exists_exposed_window_min {T : Finset ℂ} {v : ℂ} (hv : v ∈ T) {u : ℂ} (hu0 : u ≠ 0)
    (hu : ∀ q ∈ T, q ≠ v → 0 < (conj u * (q - v)).re)
    (hdist : ∀ q₁ ∈ T, q₁ ≠ v → ∀ q₂ ∈ T, q₂ ≠ v → q₁ ≠ q₂ →
      toIocMod Real.pi_pos 0 (Complex.arg (q₁ - v)) ≠
        toIocMod Real.pi_pos 0 (Complex.arg (q₂ - v)))
    (hne : (T.erase v).Nonempty) :
    ∃ c ∈ T.erase v, (∀ q ∈ T.erase v,
        toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (c - v)) ≤
          toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (q - v))) ∧
      ∃ w : ℂ, w ≠ 0 ∧ ∀ q ∈ T, q ≠ c → 0 < (conj w * (q - c)).re := by
  set α : ℂ → ℝ := fun q => toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2)
    (Complex.arg (q - v))
  set img := (T.erase v).image α
  have himg_ne : img.Nonempty := Finset.Nonempty.image hne _
  obtain ⟨c, hc_mem, hc_eq⟩ := Finset.mem_image.1 (Finset.min'_mem img himg_ne)
  have hmin : ∀ q ∈ T.erase v, α c ≤ α q := by
    intro q hq
    rw [hc_eq]
    exact Finset.min'_le img (α q) (Finset.mem_image.2 ⟨q, hq, rfl⟩)
  refine ⟨c, hc_mem, hmin, ?_⟩
  have hvc : v ≠ c := (mem_erase.1 hc_mem).1.symm
  have hwin : ∀ q ∈ T.erase v, toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2)
      (Complex.arg (q - v)) ∈ Set.Ioo (Complex.arg u - Real.pi / 2)
      (Complex.arg u - Real.pi / 2 + Real.pi) := by
    intro q hq
    have hshift : Complex.arg u - Real.pi / 2 + Real.pi = Complex.arg u + Real.pi / 2 := by
      ring
    rw [hshift]
    exact arg_window_of_exposed hu0 (hu q (mem_erase.1 hq).2 (mem_erase.1 hq).1)
      (sub_ne_zero.mpr (mem_erase.1 hq).1)
  have hinj : ∀ q₁ ∈ T.erase v, ∀ q₂ ∈ T.erase v,
      toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (q₁ - v)) =
        toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (q₂ - v)) →
        q₁ = q₂ := by
    intro q₁ hq₁ q₂ hq₂ h
    by_contra hne2
    exact hdist q₁ (mem_erase.1 hq₁).2 (mem_erase.1 hq₁).1 q₂ (mem_erase.1 hq₂).2
      (mem_erase.1 hq₂).1 hne2 (mod_pi_arg_eq_of_window_eq h)
  refine exposed_of_cross_neg (S := T) (v := v) (c := c) hvc ?_
  intro q hqT hqc hqv
  exact cross_neg_at_min (T := T.erase v) (v := v) (b := c)
    (A := Complex.arg u - Real.pi / 2) hwin hinj hc_mem hmin
    (Finset.notMem_erase v T) q (mem_erase.2 ⟨hqv, hqT⟩) hqc

/-- If `V ⊆ T` contains `v` and every strictly-exposed point of `T`, then the spread of
`T` at the exposed point `v` equals the spread of `V` at `v`. -/
lemma spreadIn_eq_spreadIn_of_vertex_subset {T V : Finset ℂ} (hVT : V ⊆ T) {v : ℂ}
    (hvV : v ∈ V) (hvT : v ∈ T) {u : ℂ} (hu0 : u ≠ 0)
    (hu : ∀ q ∈ T, q ≠ v → 0 < (conj u * (q - v)).re)
    (hdist : ∀ q₁ ∈ T, q₁ ≠ v → ∀ q₂ ∈ T, q₂ ≠ v → q₁ ≠ q₂ →
      toIocMod Real.pi_pos 0 (Complex.arg (q₁ - v)) ≠
        toIocMod Real.pi_pos 0 (Complex.arg (q₂ - v)))
    (hV2 : 2 ≤ V.card)
    (hVdef : ∀ p ∈ T, (∃ w : ℂ, w ≠ 0 ∧ ∀ q ∈ T, q ≠ p → 0 < (conj w * (q - p)).re) → p ∈ V) :
    spreadIn T v = spreadIn V v := by
  have h1card : 1 < V.card := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 h1card
  have hneV : (V.erase v).Nonempty := by
    by_cases hav : a = v
    · exact ⟨b, mem_erase.2 ⟨fun hbv => hab (hav.trans hbv.symm), hb⟩⟩
    · exact ⟨a, mem_erase.2 ⟨hav, ha⟩⟩
  have herase : V.erase v ⊆ T.erase v :=
    fun x hx => mem_erase.2 ⟨(mem_erase.1 hx).1, hVT (mem_erase.1 hx).2⟩
  have hneT : (T.erase v).Nonempty := hneV.mono herase
  obtain ⟨gminT, gmaxT, hgminT, hgmaxT, hgminT_mem, hgmaxT_mem, hspreadT⟩ :=
    spreadIn_eq_arg hvT hu0 hu hneT
  obtain ⟨gminV, gmaxV, hgminV, hgmaxV, hgminV_mem, hgmaxV_mem, hspreadV⟩ :=
    spreadIn_eq_arg hvV hu0 (fun q hq hqv => hu q (hVT hq) hqv) hneV
  obtain ⟨c, hc_mem, hc_max, hc_exp⟩ := exists_exposed_window_max hvT hu0 hu hdist hneT
  have hcT : c ∈ T := (mem_erase.1 hc_mem).2
  have hcv : c ≠ v := (mem_erase.1 hc_mem).1
  have hcV : c ∈ V := hVdef c hcT hc_exp
  have hcgmax : gmaxT = toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2)
      (Complex.arg (c - v)) := by
    apply le_antisymm
    · obtain ⟨q₀, hq₀T, hq₀v, hq₀eq⟩ := hgmaxT_mem
      rw [← hq₀eq]
      exact hc_max q₀ (mem_erase.2 ⟨hq₀v, hq₀T⟩)
    · exact hgmaxT c hcT hcv
  have hge1 : gmaxT ≤ gmaxV := by
    rw [hcgmax]
    exact hgmaxV c hcV hcv
  have hge2 : gmaxV ≤ gmaxT := by
    obtain ⟨q₁, hq₁V, hq₁v, hq₁eq⟩ := hgmaxV_mem
    rw [← hq₁eq]
    exact hgmaxT q₁ (hVT hq₁V) hq₁v
  have hmaxeq : gmaxT = gmaxV := le_antisymm hge1 hge2
  obtain ⟨d, hd_mem, hd_min, hd_exp⟩ := exists_exposed_window_min hvT hu0 hu hdist hneT
  have hdT : d ∈ T := (mem_erase.1 hd_mem).2
  have hdv : d ≠ v := (mem_erase.1 hd_mem).1
  have hdV : d ∈ V := hVdef d hdT hd_exp
  have hdgmin : gminT = toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2)
      (Complex.arg (d - v)) := by
    apply le_antisymm
    · exact hgminT d hdT hdv
    · obtain ⟨q₂, hq₂T, hq₂v, hq₂eq⟩ := hgminT_mem
      rw [← hq₂eq]
      exact hd_min q₂ (mem_erase.2 ⟨hq₂v, hq₂T⟩)
  have hle1 : gminV ≤ gminT := by
    rw [hdgmin]
    exact hgminV d hdV hdv
  have hle2 : gminT ≤ gminV := by
    obtain ⟨q₃, hq₃V, hq₃v, hq₃eq⟩ := hgminV_mem
    rw [← hq₃eq]
    exact hgminT q₃ (hVT hq₃V) hq₃v
  have hmineq : gminT = gminV := le_antisymm hle2 hle1
  rw [hspreadT, hspreadV, hmaxeq, hmineq]

/-- The spread at the distinguished vertex equals the angle between the extreme rays. -/
lemma spreadIn_eq_uangle_of_max_min {S : Finset ℂ} {v a b : ℂ} {u : ℂ} (hv : v ∈ S)
    (hu0 : u ≠ 0) (hu : ∀ q ∈ S, q ≠ v → 0 < (conj u * (q - v)).re)
    (ha : a ∈ S) (hb : b ∈ S) (hav : a ≠ v) (hbv : b ≠ v)
    (hmax : ∀ q ∈ S, q ≠ v →
      toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (q - v)) ≤
        toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (a - v)))
    (hmin : ∀ q ∈ S, q ≠ v →
      toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (b - v)) ≤
        toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (q - v)))
    (hba : toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (b - v)) <
      toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (a - v))) :
    spreadIn S v = uangle (a - v) (b - v) := by
  set α : ℂ → ℝ := fun q => toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2)
    (Complex.arg (q - v)) with hα
  have hne : (S.erase v).Nonempty := ⟨a, mem_erase.2 ⟨hav, ha⟩⟩
  have hf : ∀ x ∈ S, ∀ y ∈ S, x ≠ v → y ≠ v →
      uangle (x - v) (y - v) = |α x - α y| :=
    fun x hx y hy hxv hyv =>
      uangle_in_window_eq hu0 (hu x hx hxv) (hu y hy hyv)
        (sub_ne_zero.mpr hxv) (sub_ne_zero.mpr hyv)
  have h1 : spreadIn S v = ((S.erase v).image α).max' (Finset.Nonempty.image hne α) -
      ((S.erase v).image α).min' (Finset.Nonempty.image hne α) :=
    spreadIn_eq_image_max_sub_min hv hne hf
  have ha_mem : α a ∈ (S.erase v).image α :=
    Finset.mem_image.2 ⟨a, mem_erase.2 ⟨hav, ha⟩, rfl⟩
  have hb_mem : α b ∈ (S.erase v).image α :=
    Finset.mem_image.2 ⟨b, mem_erase.2 ⟨hbv, hb⟩, rfl⟩
  have hmax' : ((S.erase v).image α).max' (Finset.Nonempty.image hne α) = α a := by
    apply le_antisymm
    · apply Finset.max'_le
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
      exact hmax x (mem_erase.1 hx).2 (mem_erase.1 hx).1
    · exact Finset.le_max' _ (α a) ha_mem
  have hmin' : ((S.erase v).image α).min' (Finset.Nonempty.image hne α) = α b := by
    apply le_antisymm
    · exact Finset.min'_le _ (α b) hb_mem
    · apply (Finset.le_min'_iff _ _).2
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
      exact hmin x (mem_erase.1 hx).2 (mem_erase.1 hx).1
  have huang : uangle (a - v) (b - v) = α a - α b := by
    have h : uangle (a - v) (b - v) = |α a - α b| := hf a ha b hb hav hbv
    have hpos : 0 < α a - α b := sub_pos.mpr hba
    rw [abs_of_pos hpos] at h
    exact h
  rw [h1, hmax', hmin', huang]

/-- Removing the left neighbor of `a` shrinks the spread at `a` by the angle at `a`
between the two neighbors. -/
lemma spreadIn_update_at_left {S : Finset ℂ} {v a b : ℂ}
    (hv : v ∈ S) (ha : a ∈ S) (hb : b ∈ S)
    (hva : v ≠ a) (hab : a ≠ b) (hbv : b ≠ v)
    (hne : ((S.erase v).erase a).Nonempty)
    (hcross1 : ∀ x ∈ S, x ≠ a → x ≠ v → 0 < cross (v - a) (x - a))
    (hcross2 : ∀ x ∈ S, x ≠ a → x ≠ b → x ≠ v → 0 < cross (b - a) (x - a)) :
    spreadIn S a = spreadIn (S.erase v) a + uangle (v - a) (b - a) := by
  obtain ⟨hmem, hfv, hf⟩ := coord_left hva hcross1
  set f : ℂ → ℝ := fun x => toIocMod Real.two_pi_pos (Complex.arg (v - a) - Real.pi / 2)
    (Complex.arg (x - a)) with hfdef
  have hfv' : f v = Complex.arg (v - a) := hfv
  have hmem' : ∀ x ∈ S, x ≠ a → x ≠ v →
      f x ∈ Set.Ioo (Complex.arg (v - a)) (Complex.arg (v - a) + Real.pi) := hmem
  have hf' : ∀ x ∈ S, ∀ y ∈ S, x ≠ a → y ≠ a →
      uangle (x - a) (y - a) = |f x - f y| := hf
  have hne1 : (S.erase a).Nonempty := ⟨v, mem_erase.2 ⟨hva, hv⟩⟩
  have h1 : spreadIn S a = ((S.erase a).image f).max' (Finset.Nonempty.image hne1 f) -
      ((S.erase a).image f).min' (Finset.Nonempty.image hne1 f) :=
    spreadIn_eq_image_max_sub_min ha hne1 hf'
  have hv_mem2 : a ∈ S.erase v := mem_erase.2 ⟨hva.symm, ha⟩
  have h2 : spreadIn (S.erase v) a =
      (((S.erase v).erase a).image f).max' (Finset.Nonempty.image hne f) -
      (((S.erase v).erase a).image f).min' (Finset.Nonempty.image hne f) :=
    spreadIn_eq_image_max_sub_min hv_mem2 hne
      (fun x hx y hy hxa hya => hf' x (mem_erase.1 hx).2 y (mem_erase.1 hy).2 hxa hya)
  have hfv_mem1 : f v ∈ (S.erase a).image f :=
    Finset.mem_image.2 ⟨v, mem_erase.2 ⟨hva, hv⟩, rfl⟩
  have hmin1 : ((S.erase a).image f).min' (Finset.Nonempty.image hne1 f) = f v := by
    apply le_antisymm
    · exact Finset.min'_le _ (f v) hfv_mem1
    · apply (Finset.le_min'_iff _ _).2
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
      have hxa : x ≠ a := (mem_erase.1 hx).1
      have hxS : x ∈ S := (mem_erase.1 hx).2
      by_cases hxv : x = v
      · subst hxv
        exact le_rfl
      · have h : Complex.arg (v - a) < f x := (hmem' x hxS hxa hxv).1
        rw [← hfv'] at h
        exact h.le
  have hb_mem2 : b ∈ (S.erase v).erase a := mem_erase.2 ⟨hab.symm, mem_erase.2 ⟨hbv, hb⟩⟩
  have hfb_mem : f b ∈ ((S.erase v).erase a).image f :=
    Finset.mem_image.2 ⟨b, hb_mem2, rfl⟩
  have hfb_lt : f v < f b := by
    have h : Complex.arg (v - a) < f b := (hmem' b hb hab.symm hbv).1
    rw [← hfv'] at h
    exact h
  have hsub : ((S.erase v).erase a).image f ⊆ (S.erase a).image f := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    exact Finset.mem_image.2 ⟨x, mem_erase.2 ⟨(mem_erase.1 hx).1,
      (mem_erase.1 (mem_erase.1 hx).2).2⟩, rfl⟩
  have hmax1 : ((S.erase a).image f).max' (Finset.Nonempty.image hne1 f) =
      (((S.erase v).erase a).image f).max' (Finset.Nonempty.image hne f) := by
    apply le_antisymm
    · apply Finset.max'_le
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
      have hxa : x ≠ a := (mem_erase.1 hx).1
      have hxS : x ∈ S := (mem_erase.1 hx).2
      by_cases hxv : x = v
      · subst hxv
        exact hfb_lt.le.trans (Finset.le_max' _ (f b) hfb_mem)
      · exact Finset.le_max' _ (f x)
          (Finset.mem_image.2 ⟨x, mem_erase.2 ⟨hxa, mem_erase.2 ⟨hxv, hxS⟩⟩, rfl⟩)
    · exact Finset.max'_subset (Finset.Nonempty.image hne f) hsub
  have hmin2 : (((S.erase v).erase a).image f).min' (Finset.Nonempty.image hne f) = f b := by
    apply le_antisymm
    · exact Finset.min'_le _ (f b) hfb_mem
    · apply (Finset.le_min'_iff _ _).2
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
      have hxa : x ≠ a := (mem_erase.1 hx).1
      have hxSv : x ∈ S.erase v := (mem_erase.1 hx).2
      have hxv : x ≠ v := (mem_erase.1 hxSv).1
      have hxS : x ∈ S := (mem_erase.1 hxSv).2
      by_cases hxb : x = b
      · subst hxb
        exact le_rfl
      · have hlt : f b < f x := coord_left_lt hva hab.symm hxa
          (hcross1 b hb hab.symm hbv) (hcross1 x hxS hxa hxv) (hcross2 x hxS hxa hxb hxv)
        exact hlt.le
  have huang : uangle (v - a) (b - a) = f b - f v := by
    have h : uangle (v - a) (b - a) = |f v - f b| := hf' v hv b hb hva hab.symm
    have hneg : f v - f b < 0 := sub_neg.mpr hfb_lt
    rw [abs_of_neg hneg] at h
    rw [h]
    ring
  rw [h1, h2, hmax1, hmin1, hmin2, huang]
  ring

/-- Removing the right neighbor of `b` shrinks the spread at `b` by the angle at `b`
between the two neighbors. -/
lemma spreadIn_update_at_right {S : Finset ℂ} {v a b : ℂ}
    (hv : v ∈ S) (ha : a ∈ S) (hb : b ∈ S)
    (hvb : v ≠ b) (hab : a ≠ b) (hav : a ≠ v)
    (hne : ((S.erase v).erase b).Nonempty)
    (hcross1 : ∀ x ∈ S, x ≠ b → x ≠ v → cross (v - b) (x - b) < 0)
    (hcross2 : ∀ x ∈ S, x ≠ b → x ≠ a → x ≠ v → cross (a - b) (x - b) < 0) :
    spreadIn S b = spreadIn (S.erase v) b + uangle (v - b) (a - b) := by
  obtain ⟨hmem, hfv, hf⟩ := coord_right hvb hcross1
  set g : ℂ → ℝ := fun x => toIocMod Real.two_pi_pos (Complex.arg (v - b) - 3 * Real.pi / 2)
    (Complex.arg (x - b)) with hgdef
  have hfv' : g v = Complex.arg (v - b) := hfv
  have hmem' : ∀ x ∈ S, x ≠ b → x ≠ v →
      g x ∈ Set.Ioo (Complex.arg (v - b) - Real.pi) (Complex.arg (v - b)) := hmem
  have hf' : ∀ x ∈ S, ∀ y ∈ S, x ≠ b → y ≠ b →
      uangle (x - b) (y - b) = |g x - g y| := hf
  have hne1 : (S.erase b).Nonempty := ⟨v, mem_erase.2 ⟨hvb, hv⟩⟩
  have h1 : spreadIn S b = ((S.erase b).image g).max' (Finset.Nonempty.image hne1 g) -
      ((S.erase b).image g).min' (Finset.Nonempty.image hne1 g) :=
    spreadIn_eq_image_max_sub_min hb hne1 hf'
  have hv_mem2 : b ∈ S.erase v := mem_erase.2 ⟨hvb.symm, hb⟩
  have h2 : spreadIn (S.erase v) b =
      (((S.erase v).erase b).image g).max' (Finset.Nonempty.image hne g) -
      (((S.erase v).erase b).image g).min' (Finset.Nonempty.image hne g) :=
    spreadIn_eq_image_max_sub_min hv_mem2 hne
      (fun x hx y hy hxb hyb => hf' x (mem_erase.1 hx).2 y (mem_erase.1 hy).2 hxb hyb)
  have hgv_mem1 : g v ∈ (S.erase b).image g :=
    Finset.mem_image.2 ⟨v, mem_erase.2 ⟨hvb, hv⟩, rfl⟩
  have hmax1 : ((S.erase b).image g).max' (Finset.Nonempty.image hne1 g) = g v := by
    apply le_antisymm
    · apply Finset.max'_le
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
      have hxb : x ≠ b := (mem_erase.1 hx).1
      have hxS : x ∈ S := (mem_erase.1 hx).2
      by_cases hxv : x = v
      · subst hxv
        exact le_rfl
      · have h : g x < Complex.arg (v - b) := (hmem' x hxS hxb hxv).2
        rw [← hfv'] at h
        exact h.le
    · exact Finset.le_max' _ (g v) hgv_mem1
  have ha_mem2 : a ∈ (S.erase v).erase b := mem_erase.2 ⟨hab, mem_erase.2 ⟨hav, ha⟩⟩
  have hga_mem : g a ∈ ((S.erase v).erase b).image g :=
    Finset.mem_image.2 ⟨a, ha_mem2, rfl⟩
  have hga_lt : g a < g v := by
    have h : g a < Complex.arg (v - b) := (hmem' a ha hab hav).2
    rw [← hfv'] at h
    exact h
  have hsub : ((S.erase v).erase b).image g ⊆ (S.erase b).image g := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    exact Finset.mem_image.2 ⟨x, mem_erase.2 ⟨(mem_erase.1 hx).1,
      (mem_erase.1 (mem_erase.1 hx).2).2⟩, rfl⟩
  have hmin1 : ((S.erase b).image g).min' (Finset.Nonempty.image hne1 g) =
      (((S.erase v).erase b).image g).min' (Finset.Nonempty.image hne g) := by
    apply le_antisymm
    · exact Finset.min'_subset (Finset.Nonempty.image hne g) hsub
    · apply (Finset.le_min'_iff _ _).2
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
      have hxb : x ≠ b := (mem_erase.1 hx).1
      have hxS : x ∈ S := (mem_erase.1 hx).2
      by_cases hxv : x = v
      · subst hxv
        exact (Finset.min'_le _ (g a) hga_mem).trans hga_lt.le
      · exact Finset.min'_le _ (g x)
          (Finset.mem_image.2 ⟨x, mem_erase.2 ⟨hxb, mem_erase.2 ⟨hxv, hxS⟩⟩, rfl⟩)
  have hmax2 : (((S.erase v).erase b).image g).max' (Finset.Nonempty.image hne g) = g a := by
    apply le_antisymm
    · apply Finset.max'_le
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
      have hxb : x ≠ b := (mem_erase.1 hx).1
      have hxSv : x ∈ S.erase v := (mem_erase.1 hx).2
      have hxv : x ≠ v := (mem_erase.1 hxSv).1
      have hxS : x ∈ S := (mem_erase.1 hxSv).2
      by_cases hxa : x = a
      · subst hxa
        exact le_rfl
      · have hlt : g x < g a := coord_right_lt hvb hab hxb
          (hcross1 a ha hab hav) (hcross1 x hxS hxb hxv) (hcross2 x hxS hxb hxa hxv)
        exact hlt.le
    · exact Finset.le_max' _ (g a) hga_mem
  have huang : uangle (v - b) (a - b) = g v - g a := by
    have h : uangle (v - b) (a - b) = |g v - g a| := hf' v hv a ha hvb hab
    have hpos : 0 < g v - g a := sub_pos.mpr hga_lt
    rw [abs_of_pos hpos] at h
    exact h
  rw [h1, h2, hmax1, hmin1, hmax2, huang]
  ring

/-- Erasing a point that is not an extreme ray as seen from `x` does not change the
spread at `x`. -/
lemma spreadIn_erase_of_between {S : Finset ℂ} {v x a b : ℂ}
    (hv : v ∈ S) (hx : x ∈ S) (ha : a ∈ S) (hb : b ∈ S)
    (hxv : x ≠ v) (hxa : x ≠ a) (hxb : x ≠ b) (hav : a ≠ v) (hbv : b ≠ v)
    (hne : ((S.erase v).erase x).Nonempty)
    (hu : ∃ u : ℂ, u ≠ 0 ∧ ∀ q ∈ S, q ≠ x → 0 < (conj u * (q - x)).re)
    (hsign1 : 0 < cross (v - x) (b - x))
    (hsign2 : cross (v - x) (a - x) < 0) :
    spreadIn S x = spreadIn (S.erase v) x := by
  obtain ⟨u, hu0, hu⟩ := hu
  set γ : ℂ → ℝ := fun q => toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2)
    (Complex.arg (q - x)) with hγdef
  have hf : ∀ x' ∈ S, ∀ y' ∈ S, x' ≠ x → y' ≠ x →
      uangle (x' - x) (y' - x) = |γ x' - γ y'| :=
    fun x' hx' y' hy' hx'x hy'x =>
      uangle_in_window_eq hu0 (hu x' hx' hx'x) (hu y' hy' hy'x)
        (sub_ne_zero.mpr hx'x) (sub_ne_zero.mpr hy'x)
  have hwin : ∀ q ∈ S, q ≠ x →
      γ q ∈ Set.Ioo (Complex.arg u - Real.pi / 2) (Complex.arg u + Real.pi / 2) :=
    fun q hq hqx => arg_window_of_exposed hu0 (hu q hq hqx) (sub_ne_zero.mpr hqx)
  have hγb : γ v < γ b := by
    set θ := toIocMod Real.two_pi_pos 0 (Complex.arg (b - x) - Complex.arg (v - x)) with hθdef
    set mv := toIocDiv Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (v - x))
      with hmvdef
    set mb := toIocDiv Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (b - x))
      with hmbdef
    set k := toIocDiv Real.two_pi_pos 0 (Complex.arg (b - x) - Complex.arg (v - x)) with hkdef
    have hv_mem : γ v ∈ Set.Ioo (Complex.arg u - Real.pi / 2) (Complex.arg u + Real.pi / 2) :=
      hwin v hv hxv.symm
    have hb_mem : γ b ∈ Set.Ioo (Complex.arg u - Real.pi / 2) (Complex.arg u + Real.pi / 2) :=
      hwin b hb hxb.symm
    have hθ : θ ∈ Set.Ioo 0 Real.pi :=
      (cross_pos_iff (v - x) (b - x) (sub_ne_zero.mpr hxv.symm)
        (sub_ne_zero.mpr hxb.symm)).1 hsign1
    have e1 : γ b + mb • (2 * Real.pi) = Complex.arg (b - x) :=
      toIocMod_add_toIocDiv_zsmul Real.two_pi_pos (Complex.arg u - Real.pi / 2)
        (Complex.arg (b - x))
    have e2 : γ v + mv • (2 * Real.pi) = Complex.arg (v - x) :=
      toIocMod_add_toIocDiv_zsmul Real.two_pi_pos (Complex.arg u - Real.pi / 2)
        (Complex.arg (v - x))
    have e3 : θ + k • (2 * Real.pi) = Complex.arg (b - x) - Complex.arg (v - x) :=
      toIocMod_add_toIocDiv_zsmul Real.two_pi_pos 0 (Complex.arg (b - x) - Complex.arg (v - x))
    have hdiff : γ b - γ v = θ + (k - mb + mv) • (2 * Real.pi) := by
      have h4 : (γ b + mb • (2 * Real.pi)) - (γ v + mv • (2 * Real.pi))
          = θ + k • (2 * Real.pi) := by
        rw [e1, e2]
        exact e3.symm
      simp only [zsmul_eq_mul] at h4 ⊢
      push_cast at h4 ⊢
      linear_combination h4
    have hdiff_mem : γ b - γ v ∈ Set.Ioo (-Real.pi) Real.pi := by
      constructor
      · linarith [hb_mem.1, hv_mem.2]
      · linarith [hb_mem.2, hv_mem.1]
    have hN : ((k - mb + mv : ℤ) : ℝ) * (2 * Real.pi) = (γ b - γ v) - θ := by
      have h := hdiff
      simp only [zsmul_eq_mul] at h
      linarith [h]
    have hNlt : ((k - mb + mv : ℤ) : ℝ) * (2 * Real.pi) < Real.pi := by
      rw [hN]
      linarith [hdiff_mem.2, hθ.1]
    have hNgt : -2 * Real.pi < ((k - mb + mv : ℤ) : ℝ) * (2 * Real.pi) := by
      rw [hN]
      linarith [hdiff_mem.1, hθ.2]
    have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
    have hN1 : (-1 : ℝ) < ((k - mb + mv : ℤ) : ℝ) := by
      have h5 : (-1 : ℝ) * (2 * Real.pi) < ((k - mb + mv : ℤ) : ℝ) * (2 * Real.pi) := by
        linarith [hNgt]
      exact (mul_lt_mul_iff_left₀ h2pi).mp h5
    have hN2 : ((k - mb + mv : ℤ) : ℝ) < 1 := by
      have h5 : ((k - mb + mv : ℤ) : ℝ) * (2 * Real.pi) < (1 : ℝ) * (2 * Real.pi) := by
        linarith [hNlt, Real.pi_pos]
      exact (mul_lt_mul_iff_left₀ h2pi).mp h5
    have hN1' : (-1 : ℤ) < k - mb + mv := by exact_mod_cast hN1
    have hN2' : k - mb + mv < 1 := by exact_mod_cast hN2
    have hN0 : k - mb + mv = 0 := by omega
    have hfin : γ b - γ v = θ := by
      rw [hN0, zero_zsmul, add_zero] at hdiff
      exact hdiff
    linarith [hfin, hθ.1]
  have hγa : γ a < γ v := by
    set θ := toIocMod Real.two_pi_pos 0 (Complex.arg (a - x) - Complex.arg (v - x)) with hθdef
    set mv := toIocDiv Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (v - x))
      with hmvdef
    set ma := toIocDiv Real.two_pi_pos (Complex.arg u - Real.pi / 2) (Complex.arg (a - x))
      with hmadef
    set k := toIocDiv Real.two_pi_pos 0 (Complex.arg (a - x) - Complex.arg (v - x)) with hkdef
    have hv_mem : γ v ∈ Set.Ioo (Complex.arg u - Real.pi / 2) (Complex.arg u + Real.pi / 2) :=
      hwin v hv hxv.symm
    have ha_mem : γ a ∈ Set.Ioo (Complex.arg u - Real.pi / 2) (Complex.arg u + Real.pi / 2) :=
      hwin a ha hxa.symm
    have hθ : θ ∈ Set.Ioo Real.pi (2 * Real.pi) :=
      (cross_neg_iff (v - x) (a - x) (sub_ne_zero.mpr hxv.symm)
        (sub_ne_zero.mpr hxa.symm)).1 hsign2
    have e1 : γ a + ma • (2 * Real.pi) = Complex.arg (a - x) :=
      toIocMod_add_toIocDiv_zsmul Real.two_pi_pos (Complex.arg u - Real.pi / 2)
        (Complex.arg (a - x))
    have e2 : γ v + mv • (2 * Real.pi) = Complex.arg (v - x) :=
      toIocMod_add_toIocDiv_zsmul Real.two_pi_pos (Complex.arg u - Real.pi / 2)
        (Complex.arg (v - x))
    have e3 : θ + k • (2 * Real.pi) = Complex.arg (a - x) - Complex.arg (v - x) :=
      toIocMod_add_toIocDiv_zsmul Real.two_pi_pos 0 (Complex.arg (a - x) - Complex.arg (v - x))
    have hdiff : γ a - γ v = θ + (k - ma + mv) • (2 * Real.pi) := by
      have h4 : (γ a + ma • (2 * Real.pi)) - (γ v + mv • (2 * Real.pi))
          = θ + k • (2 * Real.pi) := by
        rw [e1, e2]
        exact e3.symm
      simp only [zsmul_eq_mul] at h4 ⊢
      push_cast at h4 ⊢
      linear_combination h4
    have hdiff_mem : γ a - γ v ∈ Set.Ioo (-Real.pi) Real.pi := by
      constructor
      · linarith [ha_mem.1, hv_mem.2]
      · linarith [ha_mem.2, hv_mem.1]
    have hN : ((k - ma + mv : ℤ) : ℝ) * (2 * Real.pi) = (γ a - γ v) - θ := by
      have h := hdiff
      simp only [zsmul_eq_mul] at h
      linarith [h]
    have hNlt : ((k - ma + mv : ℤ) : ℝ) * (2 * Real.pi) < 0 := by
      rw [hN]
      linarith [hdiff_mem.2, hθ.1]
    have hNgt : -3 * Real.pi < ((k - ma + mv : ℤ) : ℝ) * (2 * Real.pi) := by
      rw [hN]
      linarith [hdiff_mem.1, hθ.2]
    have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
    have hN1 : (-2 : ℝ) < ((k - ma + mv : ℤ) : ℝ) := by
      have h5 : (-2 : ℝ) * (2 * Real.pi) < ((k - ma + mv : ℤ) : ℝ) * (2 * Real.pi) := by
        linarith [hNgt, Real.pi_pos]
      exact (mul_lt_mul_iff_left₀ h2pi).mp h5
    have hN2 : ((k - ma + mv : ℤ) : ℝ) < 0 := by
      have h5 : ((k - ma + mv : ℤ) : ℝ) * (2 * Real.pi) < (0 : ℝ) * (2 * Real.pi) := by
        linarith [hNlt]
      exact (mul_lt_mul_iff_left₀ h2pi).mp h5
    have hN1' : (-2 : ℤ) < k - ma + mv := by exact_mod_cast hN1
    have hN2' : k - ma + mv < 0 := by exact_mod_cast hN2
    have hNm1 : k - ma + mv = -1 := by omega
    have hfin : γ a - γ v = θ - 2 * Real.pi := by
      rw [hNm1, neg_one_zsmul] at hdiff
      linarith [hdiff]
    linarith [hfin, hθ.2]
  have hne1 : (S.erase x).Nonempty := ⟨v, mem_erase.2 ⟨hxv.symm, hv⟩⟩
  have h1 : spreadIn S x = ((S.erase x).image γ).max' (Finset.Nonempty.image hne1 γ) -
      ((S.erase x).image γ).min' (Finset.Nonempty.image hne1 γ) :=
    spreadIn_eq_image_max_sub_min hx hne1 hf
  have hx_mem2 : x ∈ S.erase v := mem_erase.2 ⟨hxv, hx⟩
  have h2 : spreadIn (S.erase v) x =
      (((S.erase v).erase x).image γ).max' (Finset.Nonempty.image hne γ) -
      (((S.erase v).erase x).image γ).min' (Finset.Nonempty.image hne γ) :=
    spreadIn_eq_image_max_sub_min hx_mem2 hne
      (fun x' hx' y' hy' hx'x hy'x => hf x' (mem_erase.1 hx').2 y' (mem_erase.1 hy').2 hx'x hy'x)
  have ha_mem2 : a ∈ (S.erase v).erase x := mem_erase.2 ⟨hxa.symm, mem_erase.2 ⟨hav, ha⟩⟩
  have hb_mem2 : b ∈ (S.erase v).erase x := mem_erase.2 ⟨hxb.symm, mem_erase.2 ⟨hbv, hb⟩⟩
  have hga_mem : γ a ∈ ((S.erase v).erase x).image γ :=
    Finset.mem_image.2 ⟨a, ha_mem2, rfl⟩
  have hgb_mem : γ b ∈ ((S.erase v).erase x).image γ :=
    Finset.mem_image.2 ⟨b, hb_mem2, rfl⟩
  have hsub : ((S.erase v).erase x).image γ ⊆ (S.erase x).image γ := by
    intro y hy
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 hy
    exact Finset.mem_image.2 ⟨x', mem_erase.2 ⟨(mem_erase.1 hx').1,
      (mem_erase.1 (mem_erase.1 hx').2).2⟩, rfl⟩
  have hmin1 : ((S.erase x).image γ).min' (Finset.Nonempty.image hne1 γ) =
      (((S.erase v).erase x).image γ).min' (Finset.Nonempty.image hne γ) := by
    apply le_antisymm
    · exact Finset.min'_subset (Finset.Nonempty.image hne γ) hsub
    · apply (Finset.le_min'_iff _ _).2
      intro y hy
      obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 hy
      have hx'x : x' ≠ x := (mem_erase.1 hx').1
      have hx'S : x' ∈ S := (mem_erase.1 hx').2
      by_cases hx'v : x' = v
      · subst hx'v
        exact (Finset.min'_le _ (γ a) hga_mem).trans hγa.le
      · exact Finset.min'_le _ (γ x')
          (Finset.mem_image.2 ⟨x', mem_erase.2 ⟨hx'x, mem_erase.2 ⟨hx'v, hx'S⟩⟩, rfl⟩)
  have hmax1 : ((S.erase x).image γ).max' (Finset.Nonempty.image hne1 γ) =
      (((S.erase v).erase x).image γ).max' (Finset.Nonempty.image hne γ) := by
    apply le_antisymm
    · apply Finset.max'_le
      intro y hy
      obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 hy
      have hx'x : x' ≠ x := (mem_erase.1 hx').1
      have hx'S : x' ∈ S := (mem_erase.1 hx').2
      by_cases hx'v : x' = v
      · subst hx'v
        exact hγb.le.trans (Finset.le_max' _ (γ b) hgb_mem)
      · exact Finset.le_max' _ (γ x')
          (Finset.mem_image.2 ⟨x', mem_erase.2 ⟨hx'x, mem_erase.2 ⟨hx'v, hx'S⟩⟩, rfl⟩)
    · exact Finset.max'_subset (Finset.Nonempty.image hne γ) hsub
  rw [h1, h2, hmin1, hmax1]

/-- The sum of the angular spreads of a finite set in strictly convex position equals
the interior-angle sum `(n - 2) * π` of the convex polygon. -/
lemma polygon_spread_sum : ∀ (m : ℕ) (S : Finset ℂ), S.card = m → 3 ≤ m →
    (∀ p ∈ S, ∃ u : ℂ, u ≠ 0 ∧ ∀ q ∈ S, q ≠ p → 0 < (conj u * (q - p)).re) →
    (∀ p ∈ S, ∀ q₁ ∈ S, ∀ q₂ ∈ S, q₁ ≠ p → q₂ ≠ p → q₁ ≠ q₂ →
      toIocMod Real.pi_pos 0 (Complex.arg (q₁ - p)) ≠
        toIocMod Real.pi_pos 0 (Complex.arg (q₂ - p))) →
    ∑ p ∈ S, spreadIn S p = ((m : ℝ) - 2) * Real.pi := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro S hcard hm hconv hdist
    have hinj : ∀ p ∈ S, ∀ q₁ ∈ S, q₁ ≠ p → ∀ q₂ ∈ S, q₂ ≠ p → ∀ A : ℝ,
        toIocMod Real.two_pi_pos A (Complex.arg (q₁ - p)) =
          toIocMod Real.two_pi_pos A (Complex.arg (q₂ - p)) → q₁ = q₂ := by
      intro p hp q₁ hq₁ hq₁p q₂ hq₂ hq₂p A h
      by_contra hne
      exact hdist p hp q₁ hq₁ q₂ hq₂ hq₁p hq₂p hne (mod_pi_arg_eq_of_window_eq h)
    rcases hm.lt_or_eq with hm4 | hm3
    · -- Induction step: `m > 3`; remove an ear vertex `v` with neighbors `a` (max) and `b` (min).
      have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨v, hv⟩ := hSne
      obtain ⟨u, hu0, hu⟩ := hconv v hv
      set A := Complex.arg u - Real.pi / 2 with hA
      set α : ℂ → ℝ := fun q => toIocMod Real.two_pi_pos A (Complex.arg (q - v)) with hα
      have hA2 : A + Real.pi = Complex.arg u + Real.pi / 2 := by rw [hA]; ring
      have hwin : ∀ q ∈ S, q ≠ v → α q ∈ Set.Ioo A (A + Real.pi) := by
        intro q hq hqv
        rw [hA2]
        exact arg_window_of_exposed hu0 (hu q hq hqv) (sub_ne_zero.mpr hqv)
      have hinjv : ∀ q₁ ∈ S, q₁ ≠ v → ∀ q₂ ∈ S, q₂ ≠ v → α q₁ = α q₂ → q₁ = q₂ :=
        fun q₁ hq₁ hq₁v q₂ hq₂ hq₂v h => hinj v hv q₁ hq₁ hq₁v q₂ hq₂ hq₂v A h
      have hne1 : (S.erase v).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem hv, hcard]
        omega
      set img := (S.erase v).image α with himg
      have himg_ne : img.Nonempty := Finset.Nonempty.image hne1 _
      obtain ⟨a, ha_mem, ha_eq⟩ := Finset.mem_image.1 (Finset.max'_mem img himg_ne)
      obtain ⟨b, hb_mem, hb_eq⟩ := Finset.mem_image.1 (Finset.min'_mem img himg_ne)
      have ha : a ∈ S := (mem_erase.1 ha_mem).2
      have hav : a ≠ v := (mem_erase.1 ha_mem).1
      have hb : b ∈ S := (mem_erase.1 hb_mem).2
      have hbv : b ≠ v := (mem_erase.1 hb_mem).1
      have hmax : ∀ q ∈ S, q ≠ v → α q ≤ α a := by
        intro q hq hqv
        rw [ha_eq]
        exact Finset.le_max' img _ (Finset.mem_image.2 ⟨q, mem_erase.2 ⟨hqv, hq⟩, rfl⟩)
      have hmin : ∀ q ∈ S, q ≠ v → α b ≤ α q := by
        intro q hq hqv
        rw [hb_eq]
        exact Finset.min'_le img _ (Finset.mem_image.2 ⟨q, mem_erase.2 ⟨hqv, hq⟩, rfl⟩)
      have hcard_er : (S.erase v).card = m - 1 := by rw [Finset.card_erase_of_mem hv, hcard]
      have hinjOn : Set.InjOn α (S.erase v) := by
        intro x hx y hy h
        exact hinjv x (mem_erase.1 (Finset.mem_coe.1 hx)).2
          (mem_erase.1 (Finset.mem_coe.1 hx)).1 y (mem_erase.1 (Finset.mem_coe.1 hy)).2
          (mem_erase.1 (Finset.mem_coe.1 hy)).1 h
      have himg_card : img.card = m - 1 := by
        rw [himg, Finset.card_image_of_injOn hinjOn, hcard_er]
      have hba : α b < α a := by
        rw [hb_eq, ha_eq]
        by_contra hle
        push Not at hle
        have hcard1 : img.card ≤ 1 := by
          rw [Finset.card_le_one]
          intro x hx y hy
          have h1 : img.min' himg_ne ≤ x := Finset.min'_le img _ hx
          have h2 : x ≤ img.max' himg_ne := Finset.le_max' img _ hx
          have h3 : img.min' himg_ne ≤ y := Finset.min'_le img _ hy
          have h4 : y ≤ img.max' himg_ne := Finset.le_max' img _ hy
          exact le_antisymm (by linarith) (by linarith)
        omega
      have hab : a ≠ b := fun h => by rw [h] at hba; exact absurd hba (lt_irrefl _)
      have hR1 : ∀ x ∈ S, x ≠ v → x ≠ a → 0 < cross (v - a) (x - a) := by
        intro x hx hxv hxa
        exact cross_pos_at_max (T := S.erase v)
          (fun q hq => hwin q (mem_erase.1 hq).2 (mem_erase.1 hq).1)
          (fun q₁ hq₁ q₂ hq₂ h => hinjv q₁ (mem_erase.1 hq₁).2 (mem_erase.1 hq₁).1
            q₂ (mem_erase.1 hq₂).2 (mem_erase.1 hq₂).1 h)
          (mem_erase.2 ⟨hav, ha⟩)
          (fun q hq => hmax q (mem_erase.1 hq).2 (mem_erase.1 hq).1)
          (Finset.notMem_erase v S) x (mem_erase.2 ⟨hxv, hx⟩) hxa
      have hR2 : ∀ x ∈ S, x ≠ v → x ≠ b → cross (v - b) (x - b) < 0 := by
        intro x hx hxv hxb
        exact cross_neg_at_min (T := S.erase v)
          (fun q hq => hwin q (mem_erase.1 hq).2 (mem_erase.1 hq).1)
          (fun q₁ hq₁ q₂ hq₂ h => hinjv q₁ (mem_erase.1 hq₁).2 (mem_erase.1 hq₁).1
            q₂ (mem_erase.1 hq₂).2 (mem_erase.1 hq₂).1 h)
          (mem_erase.2 ⟨hbv, hb⟩)
          (fun q hq => hmin q (mem_erase.1 hq).2 (mem_erase.1 hq).1)
          (Finset.notMem_erase v S) x (mem_erase.2 ⟨hxv, hx⟩) hxb
      have hear : ∀ x ∈ S, x ≠ v → x ≠ a → x ≠ b →
          0 < cross (b - a) (x - a) ∧ cross (a - b) (x - b) < 0 ∧
            0 < cross (v - x) (b - x) ∧ cross (v - x) (a - x) < 0 :=
        fun x hx hxv hxa hxb =>
          polygon_ear hwin hinjv ha hb hx hv hav hbv hxv hxa hxb hab hmax hmin (hconv x hx)
      have hσv : spreadIn S v = uangle (a - v) (b - v) :=
        spreadIn_eq_uangle_of_max_min hv hu0 hu ha hb hav hbv hmax hmin hba
      have hσa : spreadIn S a = spreadIn (S.erase v) a + uangle (v - a) (b - a) :=
        spreadIn_update_at_left hv ha hb hav.symm hab hbv
          ⟨b, mem_erase.2 ⟨hab.symm, mem_erase.2 ⟨hbv, hb⟩⟩⟩
          (fun x hx hxa hxv => hR1 x hx hxv hxa)
          (fun x hx hxa hxb hxv => (hear x hx hxv hxa hxb).1)
      have hσb : spreadIn S b = spreadIn (S.erase v) b + uangle (v - b) (a - b) :=
        spreadIn_update_at_right hv ha hb hbv.symm hab hav
          ⟨a, mem_erase.2 ⟨hab, mem_erase.2 ⟨hav, ha⟩⟩⟩
          (fun x hx hxb hxv => hR2 x hx hxv hxb)
          (fun x hx hxb hxa hxv => (hear x hx hxv hxa hxb).2.1)
      have hσx : ∀ x ∈ S, x ≠ v → x ≠ a → x ≠ b → spreadIn S x = spreadIn (S.erase v) x :=
        fun x hx hxv hxa hxb =>
          spreadIn_erase_of_between hv hx ha hb hxv hxa hxb hav hbv
            ⟨a, mem_erase.2 ⟨hxa.symm, mem_erase.2 ⟨hav, ha⟩⟩⟩ (hconv x hx)
            (hear x hx hxv hxa hxb).2.2.1 (hear x hx hxv hxa hxb).2.2.2
      have hconv' : ∀ p ∈ S.erase v, ∃ u' : ℂ, u' ≠ 0 ∧
          ∀ q ∈ S.erase v, q ≠ p → 0 < (conj u' * (q - p)).re := by
        intro p hp
        obtain ⟨u', hu'0, hu'⟩ := hconv p (mem_erase.1 hp).2
        exact ⟨u', hu'0, fun q hq hqp => hu' q (mem_erase.1 hq).2 hqp⟩
      have hdist' : ∀ p ∈ S.erase v, ∀ q₁ ∈ S.erase v, ∀ q₂ ∈ S.erase v,
          q₁ ≠ p → q₂ ≠ p → q₁ ≠ q₂ →
          toIocMod Real.pi_pos 0 (Complex.arg (q₁ - p)) ≠
            toIocMod Real.pi_pos 0 (Complex.arg (q₂ - p)) := by
        intro p hp q₁ hq₁ q₂ hq₂ h1 h2 h3
        exact hdist p (mem_erase.1 hp).2 q₁ (mem_erase.1 hq₁).2 q₂ (mem_erase.1 hq₂).2 h1 h2 h3
      have hIH : ∑ p ∈ S.erase v, spreadIn (S.erase v) p = (((m - 1 : ℕ) : ℝ) - 2) * Real.pi :=
        IH (m - 1) (by omega) (S.erase v) hcard_er (by omega) hconv' hdist'
      have hpos : 0 < cross (b - v) (a - v) :=
        cross_pos_of_window_lt (sub_ne_zero.mpr hbv) (sub_ne_zero.mpr hav)
          (hwin b hb hbv) (hwin a ha hav) hba
      have hcross_ne : cross (a - v) (b - v) ≠ 0 := by
        rw [cross_swap]
        exact neg_ne_zero.mpr (ne_of_gt hpos)
      have htri : uangle (a - v) (b - v) + uangle (v - a) (b - a) + uangle (v - b) (a - b)
          = Real.pi :=
        triangle_uangle_sum (p := v) (q := a) (r := b) hcross_ne
      have e1 : insert b (((S.erase v).erase a).erase b) = (S.erase v).erase a :=
        Finset.insert_erase (mem_erase.2 ⟨hab.symm, mem_erase.2 ⟨hbv, hb⟩⟩)
      have e2 : insert a ((S.erase v).erase a) = S.erase v :=
        Finset.insert_erase (mem_erase.2 ⟨hav, ha⟩)
      have e3 : insert v (S.erase v) = S := Finset.insert_erase hv
      have g3 : b ∉ ((S.erase v).erase a).erase b := Finset.notMem_erase b _
      have g2 : a ∉ insert b (((S.erase v).erase a).erase b) := by
        rw [Finset.mem_insert]
        push Not
        exact ⟨hab, fun h => (Finset.mem_erase.1 (Finset.mem_erase.1 h).2).1 rfl⟩
      have g1 : v ∉ insert a (insert b (((S.erase v).erase a).erase b)) := by
        rw [Finset.mem_insert, Finset.mem_insert]
        push Not
        exact ⟨hav.symm, hbv.symm, fun h =>
          Finset.notMem_erase v S (Finset.mem_erase.1 (Finset.mem_erase.1 h).2).2⟩
      have key : insert v (insert a (insert b (((S.erase v).erase a).erase b))) = S := by
        rw [e1, e2, e3]
      have hsplit : ∑ p ∈ S, spreadIn S p = spreadIn S v + (spreadIn S a +
          (spreadIn S b + ∑ x ∈ (((S.erase v).erase a).erase b), spreadIn S x)) := by
        have hstep : ∑ p ∈ insert v (insert a (insert b (((S.erase v).erase a).erase b))),
            spreadIn S p = spreadIn S v + (spreadIn S a +
            (spreadIn S b + ∑ x ∈ (((S.erase v).erase a).erase b), spreadIn S x)) := by
          rw [Finset.sum_insert g1, Finset.sum_insert g2, Finset.sum_insert g3]
        rwa [key] at hstep
      have hsplit' : ∑ p ∈ S.erase v, spreadIn (S.erase v) p = spreadIn (S.erase v) a +
          (spreadIn (S.erase v) b +
            ∑ x ∈ (((S.erase v).erase a).erase b), spreadIn (S.erase v) x) := by
        have key2 : insert a (insert b (((S.erase v).erase a).erase b)) = S.erase v := by
          rw [e1, e2]
        have hstep : ∑ p ∈ insert a (insert b (((S.erase v).erase a).erase b)),
            spreadIn (S.erase v) p = spreadIn (S.erase v) a + (spreadIn (S.erase v) b +
            ∑ x ∈ (((S.erase v).erase a).erase b), spreadIn (S.erase v) x) := by
          rw [Finset.sum_insert g2, Finset.sum_insert g3]
        rwa [key2] at hstep
      have hT : ∑ x ∈ (((S.erase v).erase a).erase b), spreadIn S x =
          ∑ x ∈ (((S.erase v).erase a).erase b), spreadIn (S.erase v) x := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxb : x ≠ b := (mem_erase.1 hx).1
        have hxa : x ≠ a := (mem_erase.1 (mem_erase.1 hx).2).1
        have hxv : x ≠ v := (mem_erase.1 (mem_erase.1 (mem_erase.1 hx).2).2).1
        have hxS : x ∈ S := (mem_erase.1 (mem_erase.1 (mem_erase.1 hx).2).2).2
        exact hσx x hxS hxv hxa hxb
      rw [hsplit, hσv, hσa, hσb, hT]
      have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
      rw [hcast] at hIH
      linarith [hIH, hsplit', htri]
    · -- Base case: `m = 3`, the triangle.
      subst hm3
      obtain ⟨p₁, p₂, p₃, h12, h13, h23, hS⟩ := Finset.card_eq_three.1 hcard
      subst hS
      have e1 : spreadIn {p₁, p₂, p₃} p₁ = uangle (p₂ - p₁) (p₃ - p₁) := by
        obtain ⟨u, hu0, hu⟩ := hconv p₁ (by simp)
        set f : ℂ → ℝ := fun q => toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2)
          (Complex.arg (q - p₁)) with hfdef
        have hne : (({p₁, p₂, p₃} : Finset ℂ).erase p₁).Nonempty :=
          ⟨p₂, mem_erase.2 ⟨h12.symm, by simp⟩⟩
        have hf : ∀ x ∈ ({p₁, p₂, p₃} : Finset ℂ), ∀ y ∈ ({p₁, p₂, p₃} : Finset ℂ),
            x ≠ p₁ → y ≠ p₁ → uangle (x - p₁) (y - p₁) = |f x - f y| :=
          fun x hx y hy hx1 hy1 =>
            uangle_in_window_eq hu0 (hu x hx hx1) (hu y hy hy1)
              (sub_ne_zero.mpr hx1) (sub_ne_zero.mpr hy1)
        have h1 : spreadIn {p₁, p₂, p₃} p₁ =
            ((({p₁, p₂, p₃} : Finset ℂ).erase p₁).image f).max' (Finset.Nonempty.image hne f) -
              ((({p₁, p₂, p₃} : Finset ℂ).erase p₁).image f).min'
                (Finset.Nonempty.image hne f) :=
          spreadIn_eq_image_max_sub_min (by simp) hne hf
        have hp2mem : p₂ ∈ ({p₁, p₂, p₃} : Finset ℂ).erase p₁ :=
          mem_erase.2 ⟨h12.symm, by simp⟩
        have hp3mem : p₃ ∈ ({p₁, p₂, p₃} : Finset ℂ).erase p₁ :=
          mem_erase.2 ⟨h13.symm, by simp⟩
        have hp2img : f p₂ ∈ (({p₁, p₂, p₃} : Finset ℂ).erase p₁).image f :=
          Finset.mem_image.2 ⟨p₂, hp2mem, rfl⟩
        have hp3img : f p₃ ∈ (({p₁, p₂, p₃} : Finset ℂ).erase p₁).image f :=
          Finset.mem_image.2 ⟨p₃, hp3mem, rfl⟩
        have hmem_cases : ∀ y ∈ (({p₁, p₂, p₃} : Finset ℂ).erase p₁).image f,
            y = f p₂ ∨ y = f p₃ := by
          intro y hy
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
          have hx2 : x = p₂ ∨ x = p₃ := by
            have h1x := (Finset.mem_erase.1 hx).2
            simp only [Finset.mem_insert, Finset.mem_singleton] at h1x
            rcases h1x with rfl | rfl | rfl
            · exact absurd rfl (Finset.mem_erase.1 hx).1
            · exact Or.inl rfl
            · exact Or.inr rfl
          rcases hx2 with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
        have hmax' : ((({p₁, p₂, p₃} : Finset ℂ).erase p₁).image f).max'
            (Finset.Nonempty.image hne f) = max (f p₂) (f p₃) := by
          apply le_antisymm
          · apply Finset.max'_le
            intro y hy
            rcases hmem_cases y hy with rfl | rfl
            · exact le_max_left _ _
            · exact le_max_right _ _
          · exact max_le (Finset.le_max' _ _ hp2img) (Finset.le_max' _ _ hp3img)
        have hmin' : ((({p₁, p₂, p₃} : Finset ℂ).erase p₁).image f).min'
            (Finset.Nonempty.image hne f) = min (f p₂) (f p₃) := by
          apply le_antisymm
          · exact le_min (Finset.min'_le _ _ hp2img) (Finset.min'_le _ _ hp3img)
          · apply (Finset.le_min'_iff _ _).2
            intro y hy
            rcases hmem_cases y hy with rfl | rfl
            · exact min_le_left _ _
            · exact min_le_right _ _
        rw [h1, hmax', hmin', max_sub_min_eq_abs, abs_sub_comm]
        exact (hf p₂ (by simp) p₃ (by simp) h12.symm h13.symm).symm
      have e2 : spreadIn {p₁, p₂, p₃} p₂ = uangle (p₁ - p₂) (p₃ - p₂) := by
        obtain ⟨u, hu0, hu⟩ := hconv p₂ (by simp)
        set f : ℂ → ℝ := fun q => toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2)
          (Complex.arg (q - p₂)) with hfdef
        have hne : (({p₁, p₂, p₃} : Finset ℂ).erase p₂).Nonempty :=
          ⟨p₁, mem_erase.2 ⟨h12, by simp⟩⟩
        have hf : ∀ x ∈ ({p₁, p₂, p₃} : Finset ℂ), ∀ y ∈ ({p₁, p₂, p₃} : Finset ℂ),
            x ≠ p₂ → y ≠ p₂ → uangle (x - p₂) (y - p₂) = |f x - f y| :=
          fun x hx y hy hx2 hy2 =>
            uangle_in_window_eq hu0 (hu x hx hx2) (hu y hy hy2)
              (sub_ne_zero.mpr hx2) (sub_ne_zero.mpr hy2)
        have h1 : spreadIn {p₁, p₂, p₃} p₂ =
            ((({p₁, p₂, p₃} : Finset ℂ).erase p₂).image f).max' (Finset.Nonempty.image hne f) -
              ((({p₁, p₂, p₃} : Finset ℂ).erase p₂).image f).min'
                (Finset.Nonempty.image hne f) :=
          spreadIn_eq_image_max_sub_min (by simp) hne hf
        have hp1mem : p₁ ∈ ({p₁, p₂, p₃} : Finset ℂ).erase p₂ :=
          mem_erase.2 ⟨h12, by simp⟩
        have hp3mem : p₃ ∈ ({p₁, p₂, p₃} : Finset ℂ).erase p₂ :=
          mem_erase.2 ⟨h23.symm, by simp⟩
        have hp1img : f p₁ ∈ (({p₁, p₂, p₃} : Finset ℂ).erase p₂).image f :=
          Finset.mem_image.2 ⟨p₁, hp1mem, rfl⟩
        have hp3img : f p₃ ∈ (({p₁, p₂, p₃} : Finset ℂ).erase p₂).image f :=
          Finset.mem_image.2 ⟨p₃, hp3mem, rfl⟩
        have hmem_cases : ∀ y ∈ (({p₁, p₂, p₃} : Finset ℂ).erase p₂).image f,
            y = f p₁ ∨ y = f p₃ := by
          intro y hy
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
          have hx2 : x = p₁ ∨ x = p₃ := by
            have h1x := (Finset.mem_erase.1 hx).2
            simp only [Finset.mem_insert, Finset.mem_singleton] at h1x
            rcases h1x with rfl | rfl | rfl
            · exact Or.inl rfl
            · exact absurd rfl (Finset.mem_erase.1 hx).1
            · exact Or.inr rfl
          rcases hx2 with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
        have hmax' : ((({p₁, p₂, p₃} : Finset ℂ).erase p₂).image f).max'
            (Finset.Nonempty.image hne f) = max (f p₁) (f p₃) := by
          apply le_antisymm
          · apply Finset.max'_le
            intro y hy
            rcases hmem_cases y hy with rfl | rfl
            · exact le_max_left _ _
            · exact le_max_right _ _
          · exact max_le (Finset.le_max' _ _ hp1img) (Finset.le_max' _ _ hp3img)
        have hmin' : ((({p₁, p₂, p₃} : Finset ℂ).erase p₂).image f).min'
            (Finset.Nonempty.image hne f) = min (f p₁) (f p₃) := by
          apply le_antisymm
          · exact le_min (Finset.min'_le _ _ hp1img) (Finset.min'_le _ _ hp3img)
          · apply (Finset.le_min'_iff _ _).2
            intro y hy
            rcases hmem_cases y hy with rfl | rfl
            · exact min_le_left _ _
            · exact min_le_right _ _
        rw [h1, hmax', hmin', max_sub_min_eq_abs, abs_sub_comm]
        exact (hf p₁ (by simp) p₃ (by simp) h12 h23.symm).symm
      have e3 : spreadIn {p₁, p₂, p₃} p₃ = uangle (p₁ - p₃) (p₂ - p₃) := by
        obtain ⟨u, hu0, hu⟩ := hconv p₃ (by simp)
        set f : ℂ → ℝ := fun q => toIocMod Real.two_pi_pos (Complex.arg u - Real.pi / 2)
          (Complex.arg (q - p₃)) with hfdef
        have hne : (({p₁, p₂, p₃} : Finset ℂ).erase p₃).Nonempty :=
          ⟨p₁, mem_erase.2 ⟨h13, by simp⟩⟩
        have hf : ∀ x ∈ ({p₁, p₂, p₃} : Finset ℂ), ∀ y ∈ ({p₁, p₂, p₃} : Finset ℂ),
            x ≠ p₃ → y ≠ p₃ → uangle (x - p₃) (y - p₃) = |f x - f y| :=
          fun x hx y hy hx3 hy3 =>
            uangle_in_window_eq hu0 (hu x hx hx3) (hu y hy hy3)
              (sub_ne_zero.mpr hx3) (sub_ne_zero.mpr hy3)
        have h1 : spreadIn {p₁, p₂, p₃} p₃ =
            ((({p₁, p₂, p₃} : Finset ℂ).erase p₃).image f).max' (Finset.Nonempty.image hne f) -
              ((({p₁, p₂, p₃} : Finset ℂ).erase p₃).image f).min'
                (Finset.Nonempty.image hne f) :=
          spreadIn_eq_image_max_sub_min (by simp) hne hf
        have hp1mem : p₁ ∈ ({p₁, p₂, p₃} : Finset ℂ).erase p₃ :=
          mem_erase.2 ⟨h13, by simp⟩
        have hp2mem : p₂ ∈ ({p₁, p₂, p₃} : Finset ℂ).erase p₃ :=
          mem_erase.2 ⟨h23, by simp⟩
        have hp1img : f p₁ ∈ (({p₁, p₂, p₃} : Finset ℂ).erase p₃).image f :=
          Finset.mem_image.2 ⟨p₁, hp1mem, rfl⟩
        have hp2img : f p₂ ∈ (({p₁, p₂, p₃} : Finset ℂ).erase p₃).image f :=
          Finset.mem_image.2 ⟨p₂, hp2mem, rfl⟩
        have hmem_cases : ∀ y ∈ (({p₁, p₂, p₃} : Finset ℂ).erase p₃).image f,
            y = f p₁ ∨ y = f p₂ := by
          intro y hy
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
          have hx2 : x = p₁ ∨ x = p₂ := by
            have h1x := (Finset.mem_erase.1 hx).2
            simp only [Finset.mem_insert, Finset.mem_singleton] at h1x
            rcases h1x with rfl | rfl | rfl
            · exact Or.inl rfl
            · exact Or.inr rfl
            · exact absurd rfl (Finset.mem_erase.1 hx).1
          rcases hx2 with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
        have hmax' : ((({p₁, p₂, p₃} : Finset ℂ).erase p₃).image f).max'
            (Finset.Nonempty.image hne f) = max (f p₁) (f p₂) := by
          apply le_antisymm
          · apply Finset.max'_le
            intro y hy
            rcases hmem_cases y hy with rfl | rfl
            · exact le_max_left _ _
            · exact le_max_right _ _
          · exact max_le (Finset.le_max' _ _ hp1img) (Finset.le_max' _ _ hp2img)
        have hmin' : ((({p₁, p₂, p₃} : Finset ℂ).erase p₃).image f).min'
            (Finset.Nonempty.image hne f) = min (f p₁) (f p₂) := by
          apply le_antisymm
          · exact le_min (Finset.min'_le _ _ hp1img) (Finset.min'_le _ _ hp2img)
          · apply (Finset.le_min'_iff _ _).2
            intro y hy
            rcases hmem_cases y hy with rfl | rfl
            · exact min_le_left _ _
            · exact min_le_right _ _
        rw [h1, hmax', hmin', max_sub_min_eq_abs, abs_sub_comm]
        exact (hf p₁ (by simp) p₂ (by simp) h13 h23).symm
      have g1 : p₁ ∉ insert p₂ ({p₃} : Finset ℂ) := by
        rw [Finset.mem_insert, Finset.mem_singleton]
        push Not
        exact ⟨h12, h13⟩
      have g2 : p₂ ∉ ({p₃} : Finset ℂ) := by
        rw [Finset.mem_singleton]
        exact h23
      rw [Finset.sum_insert g1, Finset.sum_insert g2, Finset.sum_singleton, e1, e2, e3]
      have hcross : cross (p₂ - p₁) (p₃ - p₁) ≠ 0 :=
        cross_ne_zero_of_arg_ne (sub_ne_zero.mpr h12.symm) (sub_ne_zero.mpr h13.symm)
          (hdist p₁ (by simp) p₂ (by simp) p₃ (by simp) h12.symm h13.symm h23)
      have htri : uangle (p₂ - p₁) (p₃ - p₁) + uangle (p₁ - p₂) (p₃ - p₂) +
          uangle (p₁ - p₃) (p₂ - p₃) = Real.pi :=
        triangle_uangle_sum hcross
      have h3 : (((3 : ℕ) : ℝ) - 2) * Real.pi = Real.pi := by norm_num
      rw [h3]
      linarith [htri]

/-- The spread at `k` equals the point-set spread over the image of all centres. -/
lemma spread_eq_spreadIn_image (hn : 3 ≤ n) (hlines : NoLineMeetsThree O) (k : Fin n) :
    spread O k = spreadIn (univ.image O) (O k) := by
  have hset : Set.range (fun p : Fin n × Fin n => uangle (O p.1 - O k) (O p.2 - O k)) =
      ↑((univ.image O ×ˢ univ.image O).image
        fun ab : ℂ × ℂ => uangle (ab.1 - O k) (ab.2 - O k)) := by
    ext y
    constructor
    · rintro ⟨p, rfl⟩
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨(O p.1, O p.2),
        Finset.mem_product.2 ⟨Finset.mem_image.2 ⟨p.1, mem_univ _, rfl⟩,
          Finset.mem_image.2 ⟨p.2, mem_univ _, rfl⟩⟩, rfl⟩)
    · intro hy
      obtain ⟨⟨x₁, x₂⟩, hx_mem, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
      obtain ⟨hx₁, hx₂⟩ := Finset.mem_product.1 hx_mem
      obtain ⟨i₁, -, rfl⟩ := Finset.mem_image.1 hx₁
      obtain ⟨i₂, -, rfl⟩ := Finset.mem_image.1 hx₂
      exact Set.mem_range_self (i₁, i₂)
  exact congrArg sSup hset

/-- The centres are distinct (they are pairwise at distance greater than `2`). -/
lemma O_injective (hn : 3 ≤ n) (hlines : NoLineMeetsThree O) : Function.Injective O := by
  intro i j h
  by_contra hij
  have h2 := two_lt_dist hn hlines hij
  rw [h, sub_self, norm_zero] at h2
  linarith

/-- An endpoint of a diameter of the centres is a vertex of the convex hull. -/
lemma isVertex_of_diameter (hn : 3 ≤ n) (hlines : NoLineMeetsThree O) {i₀ j₀ : Fin n}
    (hmax : ∀ i j : Fin n, ‖O i - O j‖ ≤ ‖O i₀ - O j₀‖) (hij : i₀ ≠ j₀) : IsVertex O i₀ := by
  have h2 : 2 < ‖O j₀ - O i₀‖ := by
    have h := two_lt_dist hn hlines hij
    rw [norm_sub_rev] at h
    exact h
  have hw0 : O j₀ - O i₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at h2
    linarith
  refine ⟨O j₀ - O i₀, hw0, fun j hj => ?_⟩
  have hre : (conj (O j₀ - O i₀) * (O j - O i₀)).re =
      (conj (O j₀ - O i₀) * (O j - O j₀)).re + Complex.normSq (O j₀ - O i₀) := by
    have hdecomp : O j - O i₀ = (O j - O j₀) + (O j₀ - O i₀) := by ring
    rw [hdecomp, mul_add, Complex.add_re]
    have hcc : conj (O j₀ - O i₀) * (O j₀ - O i₀) = (Complex.normSq (O j₀ - O i₀) : ℂ) := by
      rw [mul_comm (conj (O j₀ - O i₀)), Complex.mul_conj]
    rw [hcc, Complex.ofReal_re]
  have hzw : ‖O j - O j₀‖ ≤ ‖O j₀ - O i₀‖ := by
    have h := hmax j j₀
    rw [norm_sub_rev (O i₀) (O j₀)] at h
    exact h
  have hnorm_prod : ‖conj (O j₀ - O i₀) * (O j - O j₀)‖ =
      ‖O j₀ - O i₀‖ * ‖O j - O j₀‖ := by
    rw [norm_mul, Complex.norm_conj]
  have hre_lb : -‖O j₀ - O i₀‖ * ‖O j - O j₀‖ ≤
      (conj (O j₀ - O i₀) * (O j - O j₀)).re := by
    have h1 := Complex.abs_re_le_norm (conj (O j₀ - O i₀) * (O j - O j₀))
    rw [hnorm_prod] at h1
    have h2' := neg_abs_le ((conj (O j₀ - O i₀) * (O j - O j₀)).re)
    linarith
  have hge : ‖O j₀ - O i₀‖ * ‖O j - O j₀‖ ≤ ‖O j₀ - O i₀‖ * ‖O j₀ - O i₀‖ :=
    mul_le_mul_of_nonneg_left hzw (norm_nonneg _)
  have hnn : 0 ≤ (conj (O j₀ - O i₀) * (O j - O i₀)).re := by
    rw [hre, Complex.normSq_eq_norm_sq, pow_two]
    linarith
  rcases hnn.lt_or_eq with hlt | heq
  · exact hlt
  exfalso
  have hre0 : (conj (O j₀ - O i₀) * (O j - O i₀)).re = 0 := heq.symm
  have hzre : (conj (O j₀ - O i₀) * (O j - O j₀)).re = -‖O j₀ - O i₀‖ ^ 2 := by
    have hwsq : Complex.normSq (O j₀ - O i₀) = ‖O j₀ - O i₀‖ ^ 2 :=
      Complex.normSq_eq_norm_sq _
    linarith
  have hpos : 0 < ‖O j₀ - O i₀‖ := by linarith
  have hznorm : ‖O j - O j₀‖ = ‖O j₀ - O i₀‖ := by
    apply le_antisymm hzw
    by_contra hc
    push Not at hc
    have hlt' : ‖O j₀ - O i₀‖ * ‖O j - O j₀‖ < ‖O j₀ - O i₀‖ ^ 2 := by
      rw [pow_two]
      exact mul_lt_mul_of_pos_left hc hpos
    have h1 : ‖O j₀ - O i₀‖ ^ 2 ≤ ‖O j₀ - O i₀‖ * ‖O j - O j₀‖ := by
      linarith
    linarith
  have hynorm : ‖conj (O j₀ - O i₀) * (O j - O j₀)‖ = ‖O j₀ - O i₀‖ ^ 2 := by
    rw [hnorm_prod, hznorm]
    ring
  have hyim : (conj (O j₀ - O i₀) * (O j - O j₀)).im = 0 := by
    have hre2 : (conj (O j₀ - O i₀) * (O j - O j₀)).re *
        (conj (O j₀ - O i₀) * (O j - O j₀)).re =
        ‖conj (O j₀ - O i₀) * (O j - O j₀)‖ * ‖conj (O j₀ - O i₀) * (O j - O j₀)‖ := by
      rw [hzre, hynorm]
      ring
    have h3 : ‖conj (O j₀ - O i₀) * (O j - O j₀)‖ * ‖conj (O j₀ - O i₀) * (O j - O j₀)‖ =
        (conj (O j₀ - O i₀) * (O j - O j₀)).re * (conj (O j₀ - O i₀) * (O j - O j₀)).re +
        (conj (O j₀ - O i₀) * (O j - O j₀)).im * (conj (O j₀ - O i₀) * (O j - O j₀)).im := by
      have h := Complex.normSq_eq_norm_sq (conj (O j₀ - O i₀) * (O j - O j₀))
      rw [Complex.normSq_apply, pow_two] at h
      rw [← h]
    have him0 : (conj (O j₀ - O i₀) * (O j - O j₀)).im *
        (conj (O j₀ - O i₀) * (O j - O j₀)).im = 0 := by
      linarith
    exact mul_self_eq_zero.1 him0
  have hjj₀ : j ≠ j₀ := by
    intro h
    rw [h, sub_self, mul_zero, Complex.zero_re] at hzre
    have hpos2 : 0 < ‖O j₀ - O i₀‖ ^ 2 := pow_pos hpos 2
    linarith
  have hcross0 : cross (O i₀ - O j₀) (O j - O j₀) = 0 := by
    have hswap : O j₀ - O i₀ = -(O i₀ - O j₀) := by ring
    have hc : cross (O j₀ - O i₀) (O j - O j₀) = 0 := hyim
    rw [hswap, cross_neg_left] at hc
    exact neg_eq_zero.1 hc
  have h2' := two_lt_dist hn hlines hij
  have hi₀0 : O i₀ - O j₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at h2'
    linarith
  have hj0 : O j - O j₀ ≠ 0 := sub_ne_zero.mpr (fun h => hjj₀ (O_injective hn hlines h))
  have hcross_ne : cross (O i₀ - O j₀) (O j - O j₀) ≠ 0 :=
    cross_ne_zero_of_arg_ne hi₀0 hj0
      (arg_toIocMod_ne hn hlines hij.symm hjj₀.symm hj.symm)
  exact hcross_ne hcross0

/-- A pair of centres realising the maximal pairwise distance exists. -/
lemma exists_diameter (hn : 3 ≤ n) (hlines : NoLineMeetsThree O) :
    ∃ i₀ j₀ : Fin n, i₀ ≠ j₀ ∧ ∀ i j : Fin n, ‖O i - O j‖ ≤ ‖O i₀ - O j₀‖ := by
  obtain ⟨p, -, hp_max⟩ := (univ ×ˢ univ : Finset (Fin n × Fin n)).exists_max_image
    (fun p : Fin n × Fin n => ‖O p.1 - O p.2‖)
    ⟨(⟨0, by omega⟩, ⟨0, by omega⟩), Finset.mem_product.2 ⟨mem_univ _, mem_univ _⟩⟩
  refine ⟨p.1, p.2, ?_, fun i j =>
    hp_max (i, j) (Finset.mem_product.2 ⟨mem_univ i, mem_univ j⟩)⟩
  by_contra heq
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := fun h => by
    rw [Fin.mk.injEq] at h
    norm_num at h
  have hlt : 2 < ‖O (⟨0, by omega⟩ : Fin n) - O ⟨1, by omega⟩‖ := two_lt_dist hn hlines h01
  have hle : ‖O (⟨0, by omega⟩ : Fin n) - O ⟨1, by omega⟩‖ ≤ ‖O p.1 - O p.2‖ :=
    hp_max (⟨0, by omega⟩, ⟨1, by omega⟩) (Finset.mem_product.2 ⟨mem_univ _, mem_univ _⟩)
  rw [heq, sub_self, norm_zero] at hle
  linarith

/-- The convex hull of the centres has at least two vertices. -/
lemma two_le_card_vertices (hn : 3 ≤ n) (hlines : NoLineMeetsThree O) {V : Finset (Fin n)}
    (hV : ∀ j, j ∈ V ↔ IsVertex O j) : 2 ≤ V.card := by
  obtain ⟨i₀, j₀, hij, hmax⟩ := exists_diameter hn hlines
  have hmax' : ∀ i j : Fin n, ‖O i - O j‖ ≤ ‖O j₀ - O i₀‖ :=
    fun i j => (norm_sub_rev (O i) (O j)).trans_le ((hmax j i).trans_eq (norm_sub_rev (O i₀) (O j₀)))
  have hi₀V : i₀ ∈ V := (hV i₀).2 (isVertex_of_diameter hn hlines hmax hij)
  have hj₀V : j₀ ∈ V := (hV j₀).2 (isVertex_of_diameter hn hlines hmax' hij.symm)
  have h1 : 1 < V.card := Finset.one_lt_card.2 ⟨i₀, hi₀V, j₀, hj₀V, hij⟩
  omega

/-- At a vertex, the spread only sees the other vertices. -/
lemma spread_eq_spreadIn_vertex_image (hn : 3 ≤ n) (hlines : NoLineMeetsThree O) {k : Fin n}
    (hk : IsVertex O k) {V : Finset (Fin n)} (hV : ∀ j, j ∈ V ↔ IsVertex O j)
    (hkV : k ∈ V) (hV2 : 2 ≤ V.card) :
    spread O k = spreadIn (V.image O) (O k) := by
  rw [spread_eq_spreadIn_image hn hlines k]
  obtain ⟨u, hu0, hu⟩ := hk
  refine spreadIn_eq_spreadIn_of_vertex_subset (T := univ.image O) (V := V.image O)
    (v := O k) (u := u) ?_ ?_ ?_ hu0 ?_ ?_ ?_ ?_
  · exact Finset.image_subset_image (Finset.subset_univ V)
  · exact Finset.mem_image.2 ⟨k, hkV, rfl⟩
  · exact Finset.mem_image.2 ⟨k, mem_univ k, rfl⟩
  · intro q hq hqk
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hq
    exact hu j (fun hjk => hqk (by rw [hjk]))
  · intro q₁ hq₁ hq₁k q₂ hq₂ hq₂k hq₁₂
    obtain ⟨j₁, -, rfl⟩ := Finset.mem_image.1 hq₁
    obtain ⟨j₂, -, rfl⟩ := Finset.mem_image.1 hq₂
    have hj₁k : j₁ ≠ k := fun h => hq₁k (by rw [h])
    have hj₂k : j₂ ≠ k := fun h => hq₂k (by rw [h])
    have hj₁₂ : j₁ ≠ j₂ := fun h => hq₁₂ (by rw [h])
    exact arg_toIocMod_ne hn hlines hj₁k.symm hj₂k.symm hj₁₂
  · rw [Finset.card_image_of_injOn (fun x _ y _ h => O_injective hn hlines h)]
    exact hV2
  · intro p hp hw
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨w, hw0, hw⟩ := hw
    refine Finset.mem_image.2 ⟨j, (hV j).2 ⟨w, hw0, fun j' hj' => ?_⟩, rfl⟩
    exact hw (O j') (Finset.mem_image.2 ⟨j', mem_univ j', rfl⟩)
      (fun h => hj' (O_injective hn hlines h))

/-- The convex hull of the centres has at least three vertices. -/
lemma three_le_card_vertices (hn : 3 ≤ n) (hlines : NoLineMeetsThree O) {V : Finset (Fin n)}
    (hV : ∀ j, j ∈ V ↔ IsVertex O j) : 3 ≤ V.card := by
  have hV2 : 2 ≤ V.card := two_le_card_vertices hn hlines hV
  by_contra hlt
  push Not at hlt
  have hcard2 : V.card = 2 := by omega
  have hpos : 0 < V.card := by omega
  obtain ⟨k, hkV⟩ := Finset.card_pos.1 hpos
  have hk : IsVertex O k := (hV k).1 hkV
  have hspread1 : spread O k = spreadIn (V.image O) (O k) :=
    spread_eq_spreadIn_vertex_image hn hlines hk hV hkV hV2
  obtain ⟨u, hu0, hu⟩ := hk
  have hinj : Function.Injective O := O_injective hn hlines
  have hcard2' : (V.image O).card = 2 := by
    rw [Finset.card_image_of_injOn (fun x _ y _ h => hinj h)]
    exact hcard2
  have hspread0 : spread O k = 0 := by
    rw [hspread1]
    obtain ⟨gmin, gmax, _hgmin, _hgmax, ⟨q₁, hq₁S, hq₁k, hq₁⟩, ⟨q₂, hq₂S, hq₂k, hq₂⟩, hspread⟩ :=
      spreadIn_eq_arg (Finset.mem_image.2 ⟨k, hkV, rfl⟩) hu0
        (fun q hq hqk => by
          obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hq
          exact hu j (fun hjk => hqk (by rw [hjk])))
        (Finset.card_pos.1 (by
          rw [Finset.card_erase_of_mem (Finset.mem_image.2 ⟨k, hkV, rfl⟩), hcard2']
          norm_num))
    have herase1 : ((V.image O).erase (O k)).card = 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_image.2 ⟨k, hkV, rfl⟩), hcard2']
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 herase1
    have hq₁e : q₁ ∈ (V.image O).erase (O k) := mem_erase.2 ⟨hq₁k, hq₁S⟩
    have hq₂e : q₂ ∈ (V.image O).erase (O k) := mem_erase.2 ⟨hq₂k, hq₂S⟩
    rw [ha, Finset.mem_singleton] at hq₁e hq₂e
    have hgg : gmin = gmax := by rw [← hq₁, ← hq₂, hq₁e, hq₂e]
    rw [hspread, hgg, sub_self]
  obtain ⟨j₁, hj₁k, -⟩ := exists_ne_ne hn k k
  obtain ⟨j₂, hj₂k, hj₂j₁⟩ := exists_ne_ne hn k j₁
  have huang : 0 < uangle (O j₁ - O k) (O j₂ - O k) := by
    rw [uangle]
    apply abs_pos.2
    intro harg
    have hi0 : O j₁ - O k ≠ 0 := sub_ne_zero.mpr (fun h => hj₁k (hinj h))
    have hj0 : O j₂ - O k ≠ 0 := sub_ne_zero.mpr (fun h => hj₂k (hinj h))
    have hratio : (Complex.arg ((O j₁ - O k) / (O j₂ - O k)) : Real.Angle) =
        ((Complex.arg (O j₁ - O k) - Complex.arg (O j₂ - O k) : ℝ) : Real.Angle) := by
      rw [Complex.arg_div_coe_angle hi0 hj0, Real.Angle.coe_sub]
    rw [harg] at hratio
    obtain ⟨m, hm⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 hratio
    have h2 : Complex.arg (O j₂ - O k) = Complex.arg (O j₁ - O k) + (2 * m) • Real.pi := by
      rw [zsmul_eq_mul]; push_cast; linarith [hm]
    exact arg_toIocMod_ne hn hlines hj₁k.symm hj₂k.symm hj₂j₁.symm
      (by rw [h2, toIocMod_add_zsmul])
  have hle : uangle (O j₁ - O k) (O j₂ - O k) ≤ spread O k := by
    apply le_csSup
    · refine ⟨Real.pi, ?_⟩
      intro y hy
      obtain ⟨p, hp⟩ := hy
      rw [← hp]
      exact (uangle_mem_Icc _ _).2
    · exact Set.mem_range_self (j₁, j₂)
  have hpos2 : 0 < spread O k := lt_of_lt_of_le huang hle
  linarith

/-- The sum of the spreads at the vertices is the angle sum of the convex hull. -/
lemma vertex_spread_sum (hn : 3 ≤ n) (hlines : NoLineMeetsThree O) {V : Finset (Fin n)}
    (hV : ∀ j, j ∈ V ↔ IsVertex O j) :
    ∑ k ∈ V, spread O k = ((V.card : ℝ) - 2) * Real.pi := by
  have hV3 : 3 ≤ V.card := three_le_card_vertices hn hlines hV
  have hV2 : 2 ≤ V.card := two_le_card_vertices hn hlines hV
  have hinj : Set.InjOn O ↑V := fun x _ y _ h => O_injective hn hlines h
  have hconvT : ∀ p ∈ V.image O, ∃ u : ℂ, u ≠ 0 ∧
      ∀ q ∈ V.image O, q ≠ p → 0 < (conj u * (q - p)).re := by
    intro p hp
    obtain ⟨j, hjV, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨u, hu0, hu⟩ := (hV j).1 hjV
    refine ⟨u, hu0, fun q hq hqj => ?_⟩
    obtain ⟨j', -, rfl⟩ := Finset.mem_image.1 hq
    exact hu j' (fun hj'j => hqj (by rw [hj'j]))
  have hdistT : ∀ p ∈ V.image O, ∀ q₁ ∈ V.image O, ∀ q₂ ∈ V.image O,
      q₁ ≠ p → q₂ ≠ p → q₁ ≠ q₂ →
      toIocMod Real.pi_pos 0 (Complex.arg (q₁ - p)) ≠
        toIocMod Real.pi_pos 0 (Complex.arg (q₂ - p)) := by
    intro p hp q₁ hq₁ q₂ hq₂ hq₁p hq₂p hq₁₂
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨j₁, -, rfl⟩ := Finset.mem_image.1 hq₁
    obtain ⟨j₂, -, rfl⟩ := Finset.mem_image.1 hq₂
    have hj₁j : j₁ ≠ j := fun h => hq₁p (by rw [h])
    have hj₂j : j₂ ≠ j := fun h => hq₂p (by rw [h])
    have hj₁₂ : j₁ ≠ j₂ := fun h => hq₁₂ (by rw [h])
    exact arg_toIocMod_ne hn hlines hj₁j.symm hj₂j.symm hj₁₂
  have hsum := polygon_spread_sum V.card (V.image O)
    (by rw [Finset.card_image_of_injOn hinj]) (by omega) hconvT hdistT
  rw [Finset.sum_image hinj] at hsum
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro k hkV
  exact spread_eq_spreadIn_vertex_image hn hlines ((hV k).1 hkV) hV hkV hV2

problem imo2002_p6 (n : ℕ) (hn : 3 ≤ n) (O : Fin n → ℂ)
    (hlines : NoLineMeetsThree O) :
    ∑ p ∈ (univ ×ˢ univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2),
      1 / ‖O p.1 - O p.2‖ ≤ ((n : ℝ) - 1) * Real.pi / 4 := by
  classical
  set V := univ.filter (fun k => IsVertex O k) with hVdef
  have hV : ∀ j, j ∈ V ↔ IsVertex O j := by
    intro j
    rw [hVdef, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨mem_univ j, h⟩⟩
  have hVsum := vertex_spread_sum hn hlines hV
  have hV2 := two_le_card_vertices hn hlines hV
  have hVn : V.card ≤ n := by
    have h1 := Finset.card_le_univ V
    rwa [Fintype.card_fin] at h1
  -- double counting: `2 * X = ∑ k, ∑ j ≠ k, 1 / OⱼOₖ`
  have hswap : ∑ p ∈ (univ ×ˢ univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2),
      1 / ‖O p.1 - O p.2‖ =
      ∑ p ∈ (univ ×ˢ univ : Finset (Fin n × Fin n)).filter (fun p => p.2 < p.1),
      1 / ‖O p.1 - O p.2‖ := by
    apply Finset.sum_bij (fun p _ => (p.2, p.1))
    · intro p hp
      rw [Finset.mem_filter] at hp ⊢
      exact ⟨Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hp.2⟩
    · intro p hp p' hp' h
      obtain ⟨h1, h2⟩ := Prod.eq_iff_fst_eq_snd_eq.1 h
      exact Prod.eq_iff_fst_eq_snd_eq.2 ⟨h2, h1⟩
    · intro p hp
      rw [Finset.mem_filter] at hp
      exact ⟨(p.2, p.1), by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hp.2⟩, rfl⟩
    · intro p hp
      rw [norm_sub_rev]
  have h2X : 2 * (∑ p ∈ (univ ×ˢ univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2),
      1 / ‖O p.1 - O p.2‖) =
      ∑ k ∈ univ, ∑ j ∈ univ.erase k, 1 / ‖O j - O k‖ := by
    have hunion : (univ ×ˢ univ : Finset (Fin n × Fin n)).filter (fun p => p.1 ≠ p.2) =
        (univ ×ˢ univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2) ∪
          (univ ×ˢ univ : Finset (Fin n × Fin n)).filter (fun p => p.2 < p.1) := by
      rw [← Finset.filter_or]
      apply Finset.filter_congr
      intro p _
      exact ⟨lt_or_gt_of_ne, fun h => h.elim (fun h => ne_of_lt h) (fun h => ne_of_gt h)⟩
    have hdisj : Disjoint ((univ ×ˢ univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2))
        ((univ ×ˢ univ : Finset (Fin n × Fin n)).filter (fun p => p.2 < p.1)) := by
      rw [Finset.disjoint_filter]
      intro x _ h1 h2
      exact absurd h1 (lt_asymm h2)
    have h2 : 2 * (∑ p ∈ (univ ×ˢ univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2),
        1 / ‖O p.1 - O p.2‖) =
        (∑ p ∈ (univ ×ˢ univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2),
          1 / ‖O p.1 - O p.2‖) +
        (∑ p ∈ (univ ×ˢ univ : Finset (Fin n × Fin n)).filter (fun p => p.2 < p.1),
          1 / ‖O p.1 - O p.2‖) := by
      rw [hswap]
      ring
    rw [h2, ← Finset.sum_union hdisj, ← hunion]
    rw [Finset.sum_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Finset.filter_ne', Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    show (if k ≠ j then 1 / ‖O k - O j‖ else 0) = (if j ≠ k then 1 / ‖O j - O k‖ else 0)
    by_cases hjk : j = k
    · subst hjk
      simp
    · rw [if_pos (Ne.symm hjk), if_pos hjk]
      rw [norm_sub_rev]
  -- the row bounds, summed with one strict row
  have hrows : ∀ k : Fin n, 2 * (∑ j ∈ univ.erase k, 1 / ‖O j - O k‖) <
      (if k ∈ V then spread O k * ((n : ℝ) - 1) / ((n : ℝ) - 2) else Real.pi) := by
    intro k
    by_cases hk : k ∈ V
    · rw [if_pos hk]
      exact row_bound_vertex hn hlines ((hV k).1 hk)
    · rw [if_neg hk]
      exact row_bound_nonvertex hn hlines k
  obtain ⟨k₀, -⟩ : ∃ k : Fin n, k ∈ (univ : Finset (Fin n)) := ⟨⟨0, by omega⟩, mem_univ _⟩
  have hsum : 2 * (2 * (∑ p ∈ (univ ×ˢ univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2),
      1 / ‖O p.1 - O p.2‖)) <
      ∑ k ∈ univ, (if k ∈ V then spread O k * ((n : ℝ) - 1) / ((n : ℝ) - 2) else Real.pi) := by
    rw [h2X, Finset.mul_sum]
    exact Finset.sum_lt_sum (fun k _ => (hrows k).le) ⟨k₀, mem_univ k₀, hrows k₀⟩
  -- evaluate the `if`-sum via the vertex spread sum
  have hifsum : ∑ k ∈ univ, (if k ∈ V then spread O k * ((n : ℝ) - 1) / ((n : ℝ) - 2)
      else Real.pi) =
      ((n : ℝ) - 1) / ((n : ℝ) - 2) * ((V.card : ℝ) - 2) * Real.pi +
        ((n : ℝ) - V.card) * Real.pi := by
    have hsplit : ∀ k : Fin n, (if k ∈ V then spread O k * ((n : ℝ) - 1) / ((n : ℝ) - 2)
        else Real.pi) =
        (if k ∈ V then spread O k * (((n : ℝ) - 1) / ((n : ℝ) - 2)) - Real.pi else 0) +
          Real.pi := by
      intro k
      by_cases hk : k ∈ V
      · rw [if_pos hk, if_pos hk, mul_div_assoc]
        ring
      · rw [if_neg hk, if_neg hk]
        ring
    rw [Finset.sum_congr rfl (fun k _ => hsplit k), Finset.sum_add_distrib]
    have h1 : ∑ k ∈ univ, (if k ∈ V then spread O k * (((n : ℝ) - 1) / ((n : ℝ) - 2)) - Real.pi
        else (0 : ℝ)) =
        ∑ k ∈ V, (spread O k * (((n : ℝ) - 1) / ((n : ℝ) - 2)) - Real.pi) := by
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    rw [h1, Finset.sum_sub_distrib, ← Finset.sum_mul, hVsum, Finset.sum_const, nsmul_eq_mul]
    have h2 : ∑ _k ∈ (univ : Finset (Fin n)), Real.pi = (n : ℝ) * Real.pi := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [h2]
    ring
  -- the total is at most `(n - 1) * π`
  have hn2 : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hkey : ((n : ℝ) - 1) / ((n : ℝ) - 2) * ((V.card : ℝ) - 2) * Real.pi +
      ((n : ℝ) - V.card) * Real.pi ≤ ((n : ℝ) - 1) * Real.pi := by
    have h1 : ((n : ℝ) - 1) / ((n : ℝ) - 2) * ((V.card : ℝ) - 2) ≤ (V.card : ℝ) - 1 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hn2]
      have h2 : (2 : ℝ) ≤ (V.card : ℝ) := by exact_mod_cast hV2
      have h3 : ((V.card : ℝ)) ≤ (n : ℝ) := by exact_mod_cast hVn
      nlinarith
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    nlinarith [h1, hpi]
  rw [hifsum] at hsum
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  linarith [hsum, hkey, hpi]

end Imo2002P6
