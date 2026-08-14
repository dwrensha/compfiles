/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karl Mehltretter, Kimi K3
-/

module

public import Mathlib.Algebra.EuclideanDomain.Basic
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.PNat.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 1977, Problem 1

Determine all pairs of positive integers (m, n) such that

  1 + x ^ n + x ^ (2 * n) + ... + x ^ (m * n)

is divisible by

  1 + x + x ^ 2 + ... + x ^ m.
-/

namespace Usa1977P1

open Polynomial

noncomputable def geomSumStep (m n : ℕ+) : ℤ[X] :=
  ∑ k ∈ Finset.range (m + 1), X ^ (k * n : ℕ)

noncomputable def geomSum (m : ℕ+) : ℤ[X] :=
  ∑ k ∈ Finset.range (m + 1), X ^ k

snip begin

lemma coeff_geomSum (m : ℕ+) (j : ℕ) :
    (geomSum m).coeff j = if j ≤ (m : ℕ) then (1 : ℤ) else 0 := by
  simp only [geomSum, finsetSum_coeff, coeff_X_pow, Finset.sum_ite_eq,
    Finset.mem_range, Nat.lt_add_one_iff]

lemma geomSum_natDegree (m : ℕ+) : (geomSum m).natDegree = (m : ℕ) := by
  apply le_antisymm
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro j hj
    rw [coeff_geomSum, ite_eq_right (by omega)]
  · exact le_natDegree_of_ne_zero (by simp [coeff_geomSum])

lemma geomSum_monic (m : ℕ+) : (geomSum m).Monic := by
  show (geomSum m).coeff (geomSum m).natDegree = 1
  rw [geomSum_natDegree]
  simp [coeff_geomSum]

lemma map_geomSum (m : ℕ+) :
    (geomSum m).map (Int.castRingHom ℂ) =
      ∑ k ∈ Finset.range ((m : ℕ) + 1), (X : ℂ[X]) ^ k := by
  unfold geomSum
  rw [Polynomial.map_sum]
  simp only [Polynomial.map_pow, Polynomial.map_X]

lemma map_geomSumStep (m n : ℕ+) :
    (geomSumStep m n).map (Int.castRingHom ℂ) =
      ∑ k ∈ Finset.range ((m : ℕ) + 1), ((X : ℂ[X]) ^ (n : ℕ)) ^ k := by
  unfold geomSumStep
  rw [Polynomial.map_sum]
  simp only [Polynomial.map_pow, Polynomial.map_X]
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_comm k (n : ℕ), pow_mul]

lemma eval_map_geomSum (m : ℕ+) {z : ℂ} (hz : z ≠ 1) :
    ((geomSum m).map (Int.castRingHom ℂ)).eval z = (z ^ ((m : ℕ) + 1) - 1) / (z - 1) := by
  rw [map_geomSum]
  simp only [eval_finsetSum, eval_pow, eval_X]
  exact geom_sum_eq hz _

lemma eval_map_geomSumStep (m n : ℕ+) {z : ℂ} (hz : z ^ (n : ℕ) ≠ 1) :
    ((geomSumStep m n).map (Int.castRingHom ℂ)).eval z =
      ((z ^ (n : ℕ)) ^ ((m : ℕ) + 1) - 1) / (z ^ (n : ℕ) - 1) := by
  rw [map_geomSumStep]
  simp only [eval_finsetSum, eval_pow, eval_X]
  exact geom_sum_eq hz _

lemma eval_map_geomSumStep_of_pow_eq_one (m n : ℕ+) {z : ℂ} (hz : z ^ (n : ℕ) = 1) :
    ((geomSumStep m n).map (Int.castRingHom ℂ)).eval z = (((m : ℕ) + 1 : ℕ) : ℂ) := by
  rw [map_geomSumStep]
  simp only [eval_finsetSum, eval_pow, eval_X]
  rw [show (∑ k ∈ Finset.range ((m : ℕ) + 1), (z ^ (n : ℕ)) ^ k) =
      ∑ _k ∈ Finset.range ((m : ℕ) + 1), (1 : ℂ) from
    Finset.sum_congr rfl (fun k _ => by rw [hz, one_pow])]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

/-- Divisibility over `ℤ` transfers to divisibility over `ℂ`, since the divisor is monic. -/
lemma dvd_iff_map_dvd (m n : ℕ+) :
    geomSum m ∣ geomSumStep m n ↔
      (geomSum m).map (Int.castRingHom ℂ) ∣ (geomSumStep m n).map (Int.castRingHom ℂ) :=
  (Polynomial.map_dvd_map _ Int.cast_injective (geomSum_monic m)).symm

/-- Powers of a primitive `A`-th root of unity are injective below `A`. -/
lemma pow_inj_of_lt {A : ℕ} {ω : ℂ} (hζ : IsPrimitiveRoot ω A) (hω0 : ω ≠ 0) {i j : ℕ}
    (hi : i < A) (hj : j < A) (h : ω ^ i = ω ^ j) : i = j := by
  rcases le_total i j with hle | hle
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [pow_add] at h
    have h1 : ω ^ i * 1 = ω ^ i * ω ^ d := by rw [mul_one]; exact h
    have hd1 : ω ^ d = 1 := (mul_left_cancel₀ (pow_ne_zero i hω0) h1).symm
    have hdvd : A ∣ d := (hζ.pow_eq_one_iff_dvd d).mp hd1
    have hd0 : d = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
    omega
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [pow_add] at h
    have h1 : ω ^ j * ω ^ d = ω ^ j * 1 := by rw [mul_one]; exact h
    have hd1 : ω ^ d = 1 := mul_left_cancel₀ (pow_ne_zero j hω0) h1
    have hdvd : A ∣ d := (hζ.pow_eq_one_iff_dvd d).mp hd1
    have hd0 : d = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
    omega

/-- If `gcd (m+1) n ≠ 1`, divisibility fails: the `(m+1)/gcd`-th power of a primitive
`(m+1)`-th root of unity is a root of the divisor but not of the dividend. -/
lemma not_dvd_of_gcd_ne_one {m n : ℕ+} (hgcd : Nat.gcd ((m : ℕ) + 1) (n : ℕ) ≠ 1) :
    ¬ (geomSum m ∣ geomSumStep m n) := by
  intro hdvd
  rw [dvd_iff_map_dvd m n] at hdvd
  have hA : 2 ≤ (m : ℕ) + 1 := by have := m.pos; omega
  set g := Nat.gcd ((m : ℕ) + 1) (n : ℕ) with hgdef
  have hgA : g ∣ (m : ℕ) + 1 := Nat.gcd_dvd_left _ _
  have hgn : g ∣ (n : ℕ) := Nat.gcd_dvd_right _ _
  have hgpos : 1 ≤ g := Nat.gcd_pos_of_pos_left _ (by omega)
  have hg2 : 2 ≤ g := by omega
  set j := ((m : ℕ) + 1) / g with hjdef
  have hj1 : 1 ≤ j := Nat.div_pos (Nat.le_of_dvd (by omega) hgA) (by omega)
  have hjg : j * g = (m : ℕ) + 1 := Nat.div_mul_cancel hgA
  have hjm : j ≤ (m : ℕ) := by
    have h2 : 2 * j ≤ (m : ℕ) + 1 := by
      calc 2 * j ≤ g * j := Nat.mul_le_mul_right _ hg2
        _ = (m : ℕ) + 1 := by rw [mul_comm]; exact hjg
    omega
  -- the primitive root of unity
  set ω := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((((m : ℕ) + 1 : ℕ)) : ℂ)) with hωdef
  have hζ : IsPrimitiveRoot ω ((m : ℕ) + 1) := Complex.isPrimitiveRoot_exp _ (by omega)
  have hωA : ω ^ ((m : ℕ) + 1) = 1 := hζ.pow_eq_one
  set z := ω ^ j with hzdef
  have hzA : z ^ ((m : ℕ) + 1) = 1 := by
    rw [hzdef, ← pow_mul, mul_comm, pow_mul, hωA, one_pow]
  have hz1 : z ≠ 1 := by
    rw [hzdef]
    intro h1
    have hdvd' : (m : ℕ) + 1 ∣ j := (hζ.pow_eq_one_iff_dvd j).mp h1
    have := Nat.le_of_dvd (by omega : 0 < j) hdvd'
    omega
  have hzn : z ^ (n : ℕ) = 1 := by
    obtain ⟨d, hd⟩ := hgn
    have hjn : j * (n : ℕ) = ((m : ℕ) + 1) * d := by
      rw [hd, ← mul_assoc, hjg]
    rw [hzdef, ← pow_mul, hjn, pow_mul, hωA, one_pow]
  have evP : ((geomSum m).map (Int.castRingHom ℂ)).eval z = 0 := by
    rw [eval_map_geomSum m hz1, hzA]
    simp
  have evQ : ((geomSumStep m n).map (Int.castRingHom ℂ)).eval z = (((m : ℕ) + 1 : ℕ) : ℂ) :=
    eval_map_geomSumStep_of_pow_eq_one m n hzn
  have hne : (((m : ℕ) + 1 : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
  obtain ⟨s, hs⟩ := hdvd
  have e0 : ((geomSumStep m n).map (Int.castRingHom ℂ)).eval z = 0 := by
    rw [hs, eval_mul, evP, zero_mul]
  rw [evQ] at e0
  exact hne e0

/-- If `gcd (m+1) n = 1`, divisibility holds: the remainder of the division vanishes at all
`m` nontrivial `(m+1)`-th roots of unity, and has degree `< m`, hence is zero. -/
lemma dvd_of_gcd_eq_one {m n : ℕ+} (hgcd : Nat.gcd ((m : ℕ) + 1) (n : ℕ) = 1) :
    geomSum m ∣ geomSumStep m n := by
  rw [dvd_iff_map_dvd m n]
  have hA : 2 ≤ (m : ℕ) + 1 := by have := m.pos; omega
  have hcp : Nat.Coprime ((m : ℕ) + 1) (n : ℕ) := hgcd
  set ω := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((((m : ℕ) + 1 : ℕ)) : ℂ)) with hωdef
  have hζ : IsPrimitiveRoot ω ((m : ℕ) + 1) := Complex.isPrimitiveRoot_exp _ (by omega)
  have hωA : ω ^ ((m : ℕ) + 1) = 1 := hζ.pow_eq_one
  have hω0 : ω ≠ 0 := by rw [hωdef]; exact Complex.exp_ne_zero _
  -- every `ω ^ j` with `1 ≤ j ≤ m` is a root of the remainder
  have hroot : ∀ j ∈ Finset.Icc 1 (m : ℕ),
      (((geomSumStep m n).map (Int.castRingHom ℂ)) %
        (geomSum m).map (Int.castRingHom ℂ)).eval (ω ^ j) = 0 := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hzA : (ω ^ j) ^ ((m : ℕ) + 1) = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hωA, one_pow]
    have hz1 : ω ^ j ≠ 1 := by
      intro h1
      have hdvd' : (m : ℕ) + 1 ∣ j := (hζ.pow_eq_one_iff_dvd j).mp h1
      have := Nat.le_of_dvd (by omega : 0 < j) hdvd'
      omega
    have evP : ((geomSum m).map (Int.castRingHom ℂ)).eval (ω ^ j) = 0 := by
      rw [eval_map_geomSum m hz1, hzA]
      simp
    have hzn : (ω ^ j) ^ (n : ℕ) ≠ 1 := by
      intro h1
      rw [← pow_mul] at h1
      have hdvd' : (m : ℕ) + 1 ∣ j * (n : ℕ) := (hζ.pow_eq_one_iff_dvd _).mp h1
      have hA' : (m : ℕ) + 1 ∣ j := hcp.dvd_of_dvd_mul_right hdvd'
      have := Nat.le_of_dvd (by omega : 0 < j) hA'
      omega
    have evQ : ((geomSumStep m n).map (Int.castRingHom ℂ)).eval (ω ^ j) = 0 := by
      rw [eval_map_geomSumStep m n hzn]
      have h1 : ((ω ^ j) ^ (n : ℕ)) ^ ((m : ℕ) + 1) = 1 := by
        rw [← pow_mul, mul_comm (n : ℕ) ((m : ℕ) + 1), pow_mul, hzA, one_pow]
      rw [h1]
      simp
    rw [EuclideanDomain.mod_eq_sub_mul_div, eval_sub, eval_mul, evP, evQ, zero_mul, sub_zero]
  -- the set of evaluation points has cardinality `m`
  have hinj : Set.InjOn (fun j => ω ^ j) (Finset.Icc 1 (m : ℕ)) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_Icc] at ha hb
    exact pow_inj_of_lt hζ hω0 (by omega) (by omega) hab
  have hcard : ((Finset.Icc 1 (m : ℕ)).image (fun j => ω ^ j)).card = (m : ℕ) := by
    rw [Finset.card_image_of_injOn hinj, Nat.card_Icc]
    omega
  -- the remainder has degree `< m`
  have hdeg : (((geomSumStep m n).map (Int.castRingHom ℂ)) %
      (geomSum m).map (Int.castRingHom ℂ)).natDegree < (m : ℕ) := by
    have h1 : ((geomSum m).map (Int.castRingHom ℂ)).natDegree = (m : ℕ) := by
      rw [Monic.natDegree_map (geomSum_monic m), geomSum_natDegree]
    have h2 := natDegree_mod_lt ((geomSumStep m n).map (Int.castRingHom ℂ))
      (q := (geomSum m).map (Int.castRingHom ℂ)) (by rw [h1]; omega)
    omega
  have hzero : ((geomSumStep m n).map (Int.castRingHom ℂ)) %
      (geomSum m).map (Int.castRingHom ℂ) = 0 :=
    eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _
      ((Finset.Icc 1 (m : ℕ)).image (fun j => ω ^ j))
      (fun z hz => by
        rw [Finset.mem_image] at hz
        obtain ⟨j, hj, rfl⟩ := hz
        exact hroot j hj)
      (by rw [hcard]; exact hdeg)
  exact EuclideanDomain.mod_eq_zero.mp hzero

snip end

determine solution_set : Set (ℕ+ × ℕ+) := {p | ((p.1 : ℕ) + 1).Coprime (p.2 : ℕ) }

problem usa1977_p1 (m n : ℕ+) :
    (m, n) ∈ solution_set ↔ geomSum m ∣ geomSumStep m n := by
  show ((m : ℕ) + 1).Coprime (n : ℕ) ↔ geomSum m ∣ geomSumStep m n
  constructor
  · exact dvd_of_gcd_eq_one
  · intro h
    by_contra hc
    exact not_dvd_of_gcd_ne_one hc h

end Usa1977P1
