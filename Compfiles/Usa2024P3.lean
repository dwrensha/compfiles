/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.RingTheory.RootsOfUnity.Minpoly
public import Mathlib.RingTheory.SimpleRing.Principal
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics, .Geometry] }

/-!
# USA Mathematical Olympiad 2024, Problem 3

Let (m, n) be positive integers with n ≥ 3 and draw a regular n-gon. We wish to
triangulate this n-gon into n − 2 triangles, each colored one of m colors, so
that each color has an equal sum of areas. For which (m, n) is such a
triangulation and coloring possible?

# Formalization notes

A triangulation is encoded by the two numerical properties of triangulations
that the problem actually uses — it consists of `n - 2` inscribed triangles
whose signed areas add up to the signed area of the whole polygon. Every
genuine triangulation has these properties (orient every triangle
counterclockwise; the triangle areas are then positive and add up over the
partition), and the construction direction builds the genuine fan
triangulation, so the `↔` statement proved here is exactly the olympiad
problem.
-/

namespace Usa2024P3

open Complex

snip begin

/-! ## The root of unity -/

/-- The standard primitive `n`-th root of unity `exp (2πi/n)`. -/
noncomputable def runity (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

lemma isPrimitiveRoot_runity {n : ℕ} (hn : n ≠ 0) : IsPrimitiveRoot (runity n) n :=
  Complex.isPrimitiveRoot_exp n hn

lemma runity_pow (n : ℕ) : runity n ^ n = 1 := by
  by_cases hn : n = 0
  · simp [hn, runity]
  · exact (isPrimitiveRoot_runity hn).pow_eq_one

lemma runity_ne_zero {n : ℕ} (hn : n ≠ 0) : runity n ≠ 0 :=
  (isPrimitiveRoot_runity hn).ne_zero hn

lemma runity_ne_one {n : ℕ} (hn : 1 < n) : runity n ≠ 1 :=
  (isPrimitiveRoot_runity (by omega : n ≠ 0)).ne_one hn

lemma runity_pow_ne_one {n m : ℕ} (hn : n ≠ 0) (h : ¬ n ∣ m) : runity n ^ m ≠ 1 := by
  intro h1
  rw [(isPrimitiveRoot_runity hn).pow_eq_one_iff_dvd] at h1
  exact h h1

lemma star_runity {n : ℕ} (hn : n ≠ 0) : star (runity n) = (runity n)⁻¹ := by
  have hnorm : ‖runity n‖ = 1 := (isPrimitiveRoot_runity hn).norm'_eq_one hn
  rw [Complex.inv_eq_conj hnorm]
  rfl

lemma runity_im_pos {n : ℕ} (hn : 3 ≤ n) : 0 < (runity n).im := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hpos : 0 < 2 * Real.pi / n := div_pos (by positivity) hnR
  have hlt : 2 * Real.pi / n < Real.pi := by
    rw [div_lt_iff₀ hnR]
    have h2 : (2 : ℝ) < n := by exact_mod_cast (by omega : 2 < n)
    calc 2 * Real.pi < n * Real.pi := mul_lt_mul_of_pos_right h2 Real.pi_pos
      _ = Real.pi * n := by ring
  have heq : (2 : ℂ) * Real.pi * Complex.I / n = ((2 * Real.pi / n : ℝ) : ℂ) * Complex.I := by
    have hnR0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
    rw [div_eq_iff hnC]
    rw [show ((2 * Real.pi / n : ℝ) : ℂ) * Complex.I * ↑n =
        ((2 * Real.pi / n * n : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [div_mul_cancel₀ _ hnR0]
    push_cast
    ring
  rw [runity, heq, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, Complex.I_im,
    Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
  exact Real.sin_pos_of_pos_of_lt_pi hpos hlt

lemma runity_integral {n : ℕ} (hn : 0 < n) : IsIntegral ℤ (runity n) :=
  (isPrimitiveRoot_runity (by omega : n ≠ 0)).isIntegral hn

lemma runity_inv_pow {n : ℕ} (hn : 0 < n) (a : ℕ) :
    (runity n ^ a)⁻¹ = runity n ^ ((n - 1) * a) := by
  symm
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_add]
  have h : (n - 1) * a + a = n * a := by
    have h1 : 1 ≤ n := hn
    calc (n - 1) * a + a = (n - 1 + 1) * a := by rw [add_mul, one_mul]
      _ = n * a := by rw [Nat.sub_add_cancel h1]
  rw [h, pow_mul, runity_pow, one_pow]

/-! ## Signed area -/

/-- The signed area of the triangle with vertices `z₁`, `z₂`, `z₃` (positive when
the vertices are listed counterclockwise). -/
noncomputable def sArea (z₁ z₂ z₃ : ℂ) : ℝ := (star (z₂ - z₁) * (z₃ - z₁)).im / 2

/-- The signed area, viewed as a complex number. -/
noncomputable def sAreaC (z₁ z₂ z₃ : ℂ) : ℂ := (sArea z₁ z₂ z₃ : ℂ)

lemma cast_sArea (z₁ z₂ z₃ : ℂ) : ((sArea z₁ z₂ z₃ : ℝ) : ℂ) = sAreaC z₁ z₂ z₃ := rfl

lemma sAreaC_eq (z₁ z₂ z₃ : ℂ) :
    sAreaC z₁ z₂ z₃ =
      (star (z₂ - z₁) * (z₃ - z₁) - (z₂ - z₁) * star (z₃ - z₁)) / (4 * Complex.I) := by
  have hstar : star (star (z₂ - z₁) * (z₃ - z₁)) = (z₂ - z₁) * star (z₃ - z₁) := by
    rw [star_mul, star_star, mul_comm]
  rw [sAreaC, sArea]
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
  rw [Complex.im_eq_sub_conj]
  rw [show (starRingEnd ℂ) (star (z₂ - z₁) * (z₃ - z₁)) = (z₂ - z₁) * star (z₃ - z₁) from hstar]
  rw [div_div]
  congr 1
  ring

/-- Shoelace for three points on the unit circle (so `star x = x⁻¹` etc.). -/
lemma sAreaC_unit {x y z : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hsx : star x = x⁻¹) (hsy : star y = y⁻¹) (hsz : star z = z⁻¹) :
    sAreaC x y z * (4 * Complex.I) = (y / x - 1) * (z / x - 1) * (x / z - x / y) := by
  have h4I : (4 : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
  rw [sAreaC_eq, star_sub, star_sub, hsx, hsy, hsz]
  field_simp
  ring

/-- Complex shoelace: `4i` times the signed area of a triangle whose vertices are
powers of the root of unity. -/
lemma sAreaC_pow {n : ℕ} (hn : n ≠ 0) (a b c : ℕ) :
    sAreaC (runity n ^ a) (runity n ^ b) (runity n ^ c) * (4 * Complex.I) =
      (runity n ^ b / runity n ^ a - 1) * (runity n ^ c / runity n ^ a - 1) *
        (runity n ^ a / runity n ^ c - runity n ^ a / runity n ^ b) := by
  have hζ := runity_ne_zero hn
  apply sAreaC_unit (pow_ne_zero _ hζ) (pow_ne_zero _ hζ) (pow_ne_zero _ hζ)
  · rw [star_pow, star_runity hn, inv_pow]
  · rw [star_pow, star_runity hn, inv_pow]
  · rw [star_pow, star_runity hn, inv_pow]

/-- The same, with all divisions rewritten as (natural) powers, using `ω^n = 1`. -/
lemma sAreaC_pow_factors {n : ℕ} (hn : 0 < n) (a b c : ℕ) :
    sAreaC (runity n ^ a) (runity n ^ b) (runity n ^ c) * (4 * Complex.I) =
      (runity n ^ (b + (n - 1) * a) - 1) * (runity n ^ (c + (n - 1) * a) - 1) *
        (runity n ^ (a + (n - 1) * c) - runity n ^ (a + (n - 1) * b)) := by
  rw [sAreaC_pow (by omega : n ≠ 0)]
  have hζ := runity_ne_zero (by omega : n ≠ 0)
  have key : ∀ x y : ℕ, runity n ^ y / runity n ^ x = runity n ^ (y + (n - 1) * x) := by
    intro x y
    rw [div_eq_iff (pow_ne_zero _ hζ)]
    calc runity n ^ y = runity n ^ y * 1 := (mul_one _).symm
      _ = runity n ^ y * (runity n ^ n) ^ x := by rw [runity_pow, one_pow]
      _ = runity n ^ (y + n * x) := by rw [← pow_mul, ← pow_add]
      _ = runity n ^ (y + (n - 1) * x) * runity n ^ x := by
          rw [← pow_add]
          congr 1
          have h1 : 1 ≤ n := hn
          have hx : n * x = (n - 1) * x + x := by
            conv_lhs => rw [← Nat.sub_add_cancel h1]
            rw [add_mul, one_mul]
          omega
  rw [key a b, key a c, key c a, key b a]

/-- The area of a "fan" triangle `1, ω^j, ω^(j+1)`. -/
lemma sAreaC_one_pow {n : ℕ} (hn : n ≠ 0) (j : ℕ) :
    sAreaC 1 (runity n ^ j) (runity n ^ (j + 1)) =
      (runity n - 1) * ((1 + (runity n)⁻¹) - runity n ^ j - (runity n ^ (j + 1))⁻¹) /
        (4 * Complex.I) := by
  have hζ := runity_ne_zero hn
  have hj : runity n ^ j ≠ 0 := pow_ne_zero _ hζ
  have hj1 : runity n ^ (j + 1) ≠ 0 := pow_ne_zero _ hζ
  have h4I : (4 : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
  have hsy : star (runity n ^ j) = (runity n ^ j)⁻¹ := by
    rw [star_pow, star_runity hn, inv_pow]
  have hsz : star (runity n ^ j * runity n) = (runity n ^ j * runity n)⁻¹ := by
    rw [← pow_succ, star_pow, star_runity hn, inv_pow]
  rw [sAreaC_eq, pow_succ]
  simp only [star_sub, hsy, hsz, star_one]
  field_simp
  ring

lemma sAreaC_one_one (x : ℂ) : sAreaC 1 1 x = 0 := by
  simp [sAreaC_eq]

lemma sAreaC_one_self_one (x : ℂ) : sAreaC 1 x 1 = 0 := by
  simp [sAreaC_eq]

/-! ## Integrality -/

lemma integral_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (h : ∀ i ∈ s, IsIntegral ℤ (f i)) : IsIntegral ℤ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [isIntegral_zero]
  | insert a s has ih =>
      rw [Finset.sum_insert has]
      exact IsIntegral.add (h a (Finset.mem_insert_self a s))
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

lemma runity_pow_integral {n : ℕ} (hn : 0 < n) (a : ℕ) : IsIntegral ℤ (runity n ^ a) :=
  (runity_integral hn).pow a

/-- For even `e`, `ω^e - 1` is divisible by `ω^2 - 1` inside the algebraic integers. -/
lemma runity_sq_sub_one_dvd {n : ℕ} (hn : 0 < n) {e : ℕ} (he : Even e) :
    ∃ H : ℂ, IsIntegral ℤ H ∧ runity n ^ e - 1 = (runity n ^ 2 - 1) * H := by
  obtain ⟨s, rfl⟩ := he
  refine ⟨∑ u ∈ Finset.range s, (runity n ^ 2) ^ u, ?_, ?_⟩
  · exact integral_finset_sum _ _ (fun u _ => ((runity_integral hn).pow 2).pow u)
  · rw [show s + s = 2 * s by omega, pow_mul]
    have h := geom_sum_mul (runity n ^ 2) s
    rw [mul_comm] at h
    rw [h]

/-- `4i` times the signed area of any inscribed triangle is `ω^2 - 1` times an
algebraic integer. -/
lemma shoelace_dvd {n : ℕ} (hn : 0 < n) (a b c : ℕ) :
    ∃ G : ℂ, IsIntegral ℤ G ∧
      (runity n ^ (b + (n - 1) * a) - 1) * (runity n ^ (c + (n - 1) * a) - 1) *
        (runity n ^ (a + (n - 1) * c) - runity n ^ (a + (n - 1) * b)) =
          (runity n ^ 2 - 1) * G := by
  have hint1 : IsIntegral ℤ (runity n ^ (b + (n - 1) * a) - 1) :=
    (runity_pow_integral hn _).sub isIntegral_one
  have hint2 : IsIntegral ℤ (runity n ^ (c + (n - 1) * a) - 1) :=
    (runity_pow_integral hn _).sub isIntegral_one
  have hint3 : IsIntegral ℤ (runity n ^ (a + (n - 1) * c) - runity n ^ (a + (n - 1) * b)) :=
    (runity_pow_integral hn _).sub (runity_pow_integral hn _)
  rcases Nat.even_or_odd (b + (n - 1) * a) with hAe | hAo
  · obtain ⟨H, hH, hHe⟩ := runity_sq_sub_one_dvd hn hAe
    exact ⟨H * (runity n ^ (c + (n - 1) * a) - 1) *
        (runity n ^ (a + (n - 1) * c) - runity n ^ (a + (n - 1) * b)),
      (hH.mul hint2).mul hint3, by rw [hHe]; ring⟩
  rcases Nat.even_or_odd (c + (n - 1) * a) with hBe | hBo
  · obtain ⟨H, hH, hHe⟩ := runity_sq_sub_one_dvd hn hBe
    exact ⟨(runity n ^ (b + (n - 1) * a) - 1) * H *
        (runity n ^ (a + (n - 1) * c) - runity n ^ (a + (n - 1) * b)),
      (hint1.mul hH).mul hint3, by rw [hHe]; ring⟩
  -- both `b + (n-1)a` and `c + (n-1)a` are odd; then `b` and `c` have the same parity
  have hbc : Even b ↔ Even c := by
    have hAB : Even ((b + (n - 1) * a) + (c + (n - 1) * a)) := hAo.add_odd hBo
    have hsum : (b + (n - 1) * a) + (c + (n - 1) * a) = (b + c) + 2 * ((n - 1) * a) := by ring
    rw [hsum, Nat.even_add] at hAB
    have hbc' : Even (b + c) := hAB.mpr (even_two_mul _)
    rwa [Nat.even_add] at hbc'
  -- the difference of the last two exponents is even
  have hC : ∀ d e : ℕ, (Even e ↔ Even d) → d ≤ e →
      ∃ H : ℂ, IsIntegral ℤ H ∧
        runity n ^ (a + (n - 1) * e) - runity n ^ (a + (n - 1) * d) =
          (runity n ^ 2 - 1) * H := by
    intro d e hpar hde
    have hmul : (n - 1) * d ≤ (n - 1) * e := Nat.mul_le_mul_left _ hde
    have hle : a + (n - 1) * d ≤ a + (n - 1) * e := Nat.add_le_add_left hmul a
    have hsub : (a + (n - 1) * e) - (a + (n - 1) * d) = (n - 1) * (e - d) := by
      have h1 : (a + (n - 1) * e) - (a + (n - 1) * d) = (n - 1) * e - (n - 1) * d := by
        omega
      rw [h1, Nat.mul_sub_left_distrib]
    have heven : Even ((n - 1) * (e - d)) := by
      have h2 : Even (e - d) := by
        rw [Nat.even_sub hde]
        exact hpar
      exact h2.mul_left _
    obtain ⟨H', hH', hH'e⟩ := runity_sq_sub_one_dvd hn heven
    refine ⟨runity n ^ (a + (n - 1) * d) * H', (runity_pow_integral hn _).mul hH', ?_⟩
    have hpow : runity n ^ (a + (n - 1) * e) =
        runity n ^ (a + (n - 1) * d) * runity n ^ ((a + (n - 1) * e) - (a + (n - 1) * d)) := by
      rw [← pow_add, Nat.add_sub_cancel' hle]
    rw [hpow, hsub]
    have hfactor : runity n ^ (a + (n - 1) * d) * runity n ^ ((n - 1) * (e - d)) -
        runity n ^ (a + (n - 1) * d) =
        runity n ^ (a + (n - 1) * d) * (runity n ^ ((n - 1) * (e - d)) - 1) := by ring
    rw [hfactor, hH'e]
    ring
  rcases le_total b c with hbc' | hbc'
  · obtain ⟨H, hH, hHe⟩ := hC b c hbc.symm hbc'
    exact ⟨(runity n ^ (b + (n - 1) * a) - 1) * (runity n ^ (c + (n - 1) * a) - 1) * H,
      (hint1.mul hint2).mul hH, by rw [hHe]; ring⟩
  · obtain ⟨H, hH, hHe⟩ := hC c b hbc hbc'
    have hneg : (runity n ^ (a + (n - 1) * c) - runity n ^ (a + (n - 1) * b)) =
        -(runity n ^ (a + (n - 1) * b) - runity n ^ (a + (n - 1) * c)) := by ring
    have hT3 : (runity n ^ (a + (n - 1) * c) - runity n ^ (a + (n - 1) * b)) =
        (runity n ^ 2 - 1) * (-H) := by
      rw [hneg, hHe]
      ring
    exact ⟨(runity n ^ (b + (n - 1) * a) - 1) * (runity n ^ (c + (n - 1) * a) - 1) * (-H),
      (hint1.mul hint2).mul hH.neg, by rw [hT3]; ring⟩

/-! ## The polygon and its area -/

/-- The `k`-th vertex of the regular `n`-gon on the unit circle. -/
noncomputable def vertex (n : ℕ) (k : Fin n) : ℂ := runity n ^ k.val

/-- The signed area of the triangle formed by three vertices of the `n`-gon. -/
noncomputable def triArea (n : ℕ) (t : Fin n × Fin n × Fin n) : ℝ :=
  sArea (vertex n t.1) (vertex n t.2.1) (vertex n t.2.2)

lemma cast_triArea (n : ℕ) (t : Fin n × Fin n × Fin n) :
    ((triArea n t : ℝ) : ℂ) = sAreaC (vertex n t.1) (vertex n t.2.1) (vertex n t.2.2) :=
  rfl

/-- The signed area of the regular `n`-gon, computed as the sum of the signed
areas of the fan triangles `1, ω^k, ω^(k+1)`. -/
noncomputable def polyArea (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, sArea 1 (runity n ^ k) (runity n ^ (k + 1))

lemma polyArea_cast_sum (n : ℕ) :
    ((polyArea n : ℝ) : ℂ) =
      ∑ k ∈ Finset.range n, sAreaC 1 (runity n ^ k) (runity n ^ (k + 1)) := by
  rw [polyArea]
  push_cast
  exact Finset.sum_congr rfl (fun k _ => cast_sArea _ _ _)

/-- A sum of powers of a nontrivial root of unity over a full period vanishes. -/
lemma sum_range_pow_eq_zero {x : ℂ} {q : ℕ} (hx1 : x ≠ 1) (hxq : x ^ q = 1) :
    ∑ t ∈ Finset.range q, x ^ t = 0 := by
  have h := geom_sum_mul x q
  rw [hxq, sub_self] at h
  rcases mul_eq_zero.mp h with hsum | hx
  · exact hsum
  · exact absurd (eq_of_sub_eq_zero hx) hx1

/-- The area sum over a full residue class of triangle indices. -/
lemma sum_sAreaC_residue {m n : ℕ} (hm : 0 < m) (hdvd : m ∣ n) (hlt : m < n) (r : Fin m) :
    ∑ j ∈ (Finset.range n).filter (fun j => j % m = r.val),
        sAreaC 1 (runity n ^ j) (runity n ^ (j + 1)) =
      ((n / m : ℕ) : ℂ) * (runity n - (runity n)⁻¹) / (4 * Complex.I) := by
  have hn0 : n ≠ 0 := by omega
  have hζ := runity_ne_zero hn0
  have hn_eq : m * (n / m) = n := Nat.mul_div_cancel' hdvd
  have hζm : runity n ^ m ≠ 1 := by
    apply runity_pow_ne_one hn0
    intro hnm
    have hle := Nat.le_of_dvd hm hnm
    omega
  have hfilter : (Finset.range n).filter (fun j => j % m = r.val) =
      (Finset.range (n / m)).image (fun t => r.val + m * t) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hjn, hjm⟩
      refine ⟨j / m, ?_, ?_⟩
      · have h1 : m * (j / m) ≤ j := Nat.mul_div_le j m
        have h2 : m * (j / m) < m * (n / m) := lt_of_le_of_lt h1 (by rw [hn_eq]; exact hjn)
        exact Nat.lt_of_mul_lt_mul_left h2
      · rw [add_comm, ← hjm]
        exact Nat.div_add_mod j m
    · rintro ⟨t, ht, rfl⟩
      constructor
      · calc r.val + m * t < m + m * t := Nat.add_lt_add_right r.isLt _
          _ = m * (t + 1) := by ring
          _ ≤ m * (n / m) := Nat.mul_le_mul_left m (Nat.succ_le_of_lt ht)
          _ = n := hn_eq
      · rw [Nat.add_mul_mod_self_left]
        exact Nat.mod_eq_of_lt r.isLt
  rw [hfilter, Finset.sum_image]
  swap
  · intro t₁ _ t₂ _ h
    simp only at h
    exact Nat.mul_left_cancel hm (Nat.add_left_cancel h)
  have hterms : ∀ t : ℕ,
      sAreaC 1 (runity n ^ (r.val + m * t)) (runity n ^ (r.val + m * t + 1)) =
        ((runity n - 1) / (4 * Complex.I)) *
          ((1 + (runity n)⁻¹) - (runity n ^ r.val) * (runity n ^ m) ^ t -
            (runity n ^ (r.val + 1))⁻¹ * ((runity n ^ m)⁻¹) ^ t) := by
    intro t
    rw [sAreaC_one_pow hn0]
    have e1 : runity n ^ (r.val + m * t) = (runity n ^ r.val) * (runity n ^ m) ^ t := by
      rw [pow_add, pow_mul]
    have e2 : (runity n ^ (r.val + m * t + 1))⁻¹ =
        (runity n ^ (r.val + 1))⁻¹ * ((runity n ^ m)⁻¹) ^ t := by
      have hexp : r.val + m * t + 1 = (r.val + 1) + m * t := by ring
      rw [hexp, pow_add, pow_mul, mul_inv]
      simp only [← inv_pow]
    rw [e1, e2]
    ring
  rw [Finset.sum_congr rfl (fun t _ => hterms t)]
  rw [← Finset.mul_sum]
  have hx : ∑ t ∈ Finset.range (n / m), (runity n ^ m) ^ t = 0 := by
    apply sum_range_pow_eq_zero hζm
    rw [← pow_mul, hn_eq, runity_pow]
  have hy : ∑ t ∈ Finset.range (n / m), ((runity n ^ m)⁻¹) ^ t = 0 := by
    apply sum_range_pow_eq_zero
    · rw [inv_ne_one]
      exact hζm
    · rw [inv_pow, ← pow_mul, hn_eq, runity_pow, inv_one]
  have hsumB : ∑ t ∈ Finset.range (n / m),
      ((1 + (runity n)⁻¹) - (runity n ^ r.val) * (runity n ^ m) ^ t -
        (runity n ^ (r.val + 1))⁻¹ * ((runity n ^ m)⁻¹) ^ t) =
      ((n / m : ℕ) : ℂ) * (1 + (runity n)⁻¹) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, ← Finset.mul_sum, hx, ← Finset.mul_sum, hy]
    ring
  rw [hsumB]
  field_simp
  ring

/-- The total area, as a complex number. -/
lemma polyArea_cast {n : ℕ} (hn : 3 ≤ n) :
    ((polyArea n : ℝ) : ℂ) = n * (runity n - (runity n)⁻¹) / (4 * Complex.I) := by
  rw [polyArea_cast_sum]
  have h1 : (Finset.range n).filter (fun j => j % 1 = 0) = Finset.range n := by
    ext j
    simp [Nat.mod_one]
  rw [← h1]
  rw [sum_sAreaC_residue (m := 1) Nat.one_pos (one_dvd n) (by omega) ⟨0, Nat.one_pos⟩]
  simp

lemma polyArea_pos {n : ℕ} (hn : 3 ≤ n) : 0 < polyArea n := by
  have h1 : polyArea n = n * (runity n).im / 2 := by
    apply Complex.ofReal_injective
    have h2 : runity n - (runity n)⁻¹ = ((2 * (runity n).im : ℝ) : ℂ) * Complex.I := by
      rw [← star_runity (by omega : n ≠ 0)]
      exact Complex.sub_conj _
    rw [polyArea_cast hn, h2]
    push_cast
    field_simp
    ring
  rw [h1]
  have him := runity_im_pos hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  exact div_pos (mul_pos hnR him) (by norm_num)

/-! ## Triangulations and colorings -/

/-- A (formal) triangulation of the regular `n`-gon: a finite collection of
`n - 2` triangles with vertices among those of the `n`-gon whose signed areas
add up to the signed area of the whole polygon. Every genuine triangulation
into `n - 2` triangles has these two properties. -/
structure Triangulation (n : ℕ) where
  tris : Finset (Fin n × Fin n × Fin n)
  card_tris : tris.card = n - 2
  area_sum : ∑ t ∈ tris, triArea n t = polyArea n

/-- The total area of a single color class. -/
noncomputable def colorSum {m n : ℕ} (T : Triangulation n)
    (c : Fin n × Fin n × Fin n → Fin m) (i : Fin m) : ℝ :=
  ∑ t ∈ T.tris.filter (fun t => c t = i), triArea n t

/-- `4i` times any color sum is `ω^2 - 1` times an algebraic integer. -/
lemma colorSum_dvd {m n : ℕ} (hn : 3 ≤ n) (T : Triangulation n)
    (c : Fin n × Fin n × Fin n → Fin m) (i : Fin m) :
    ∃ U : ℂ, IsIntegral ℤ U ∧
      ((colorSum T c i : ℝ) : ℂ) * (4 * Complex.I) = (runity n ^ 2 - 1) * U := by
  classical
  have hn0 : 0 < n := by omega
  have key : ∀ t : Fin n × Fin n × Fin n, ∃ G : ℂ, IsIntegral ℤ G ∧
      sAreaC (vertex n t.1) (vertex n t.2.1) (vertex n t.2.2) * (4 * Complex.I) =
        (runity n ^ 2 - 1) * G := by
    intro t
    obtain ⟨G, hG, hGeq⟩ := shoelace_dvd hn0 t.1.val t.2.1.val t.2.2.val
    refine ⟨G, hG, ?_⟩
    simp only [vertex]
    rw [sAreaC_pow_factors hn0]
    exact hGeq
  choose G hG hGeq using key
  refine ⟨∑ t ∈ T.tris.filter (fun t => c t = i), G t,
    integral_finset_sum _ _ (fun t _ => hG t), ?_⟩
  have hcast : ((∑ t ∈ T.tris.filter (fun t => c t = i), triArea n t : ℝ) : ℂ) =
      ∑ t ∈ T.tris.filter (fun t => c t = i),
        sAreaC (vertex n t.1) (vertex n t.2.1) (vertex n t.2.2) := by
    push_cast
    simp only [cast_triArea]
  rw [colorSum, hcast, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun t _ => hGeq t)

/-- Necessity: if a triangulation and an equal-area `m`-coloring exist, then `m`
is a proper divisor of `n`. -/
lemma m_dvd_and_lt {m n : ℕ} (hm : 0 < m) (hn : 3 ≤ n) (T : Triangulation n)
    (c : Fin n × Fin n × Fin n → Fin m)
    (heq : ∀ i j : Fin m, colorSum T c i = colorSum T c j) :
    m ∣ n ∧ m < n := by
  classical
  have i₀ : Fin m := ⟨0, hm⟩
  set S := colorSum T c i₀ with hS
  have heq' : ∀ i : Fin m, colorSum T c i = S := fun i => by rw [hS]; exact heq i i₀
  have hsum : ∑ i : Fin m, colorSum T c i = polyArea n := by
    rw [← T.area_sum]
    exact Finset.sum_fiberwise_of_maps_to (fun t _ => Finset.mem_univ (c t)) (triArea n)
  have hmS : (m : ℝ) * S = polyArea n := by
    have h1 : ∑ i : Fin m, colorSum T c i = ∑ _i : Fin m, S :=
      Finset.sum_congr rfl (fun i _ => heq' i)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    rw [← h1]
    exact hsum
  have hSp : 0 < S := by
    have hp := polyArea_pos hn
    rw [← hmS] at hp
    exact pos_of_mul_pos_right hp (by positivity)
  -- every color is used, hence `m ≤ n - 2`
  have hmn : m < n := by
    have hne : ∀ i : Fin m, ∃ t : Fin n × Fin n × Fin n, t ∈ T.tris ∧ c t = i := by
      intro i
      by_contra hcon
      push Not at hcon
      have hem : T.tris.filter (fun t => c t = i) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro t ht
        rw [Finset.mem_filter] at ht
        exact hcon t ht.1 ht.2
      have h0 : colorSum T c i = 0 := by rw [colorSum, hem, Finset.sum_empty]
      rw [heq' i] at h0
      exact (ne_of_gt hSp) h0
    choose f hf1 hf2 using hne
    have hinj : Function.Injective (fun i => (⟨f i, hf1 i⟩ : {t // t ∈ T.tris})) := by
      intro i j hij
      have hval : f i = f j := Subtype.ext_iff.mp hij
      have hi := hf2 i
      rw [hval] at hi
      exact hi.symm.trans (hf2 j)
    have hcard := Fintype.card_le_of_injective _ hinj
    rw [Fintype.card_fin, Fintype.card_coe, T.card_tris] at hcard
    omega
  -- the integrality argument giving `m ∣ n`
  obtain ⟨U, hU, hUe⟩ := colorSum_dvd hn T c i₀
  rw [← hS] at hUe
  have hml : (m : ℂ) * ((S : ℂ) * (4 * Complex.I)) = (n : ℂ) * (runity n - (runity n)⁻¹) := by
    have hcast : ((m : ℝ) * S : ℂ) = ↑(polyArea n) := by exact_mod_cast hmS
    rw [polyArea_cast hn] at hcast
    push_cast at hcast
    rw [← mul_assoc, hcast]
    field_simp
  have hζ2 : runity n ^ 2 - 1 ≠ 0 := by
    have h1 : runity n ^ 2 ≠ 1 := by
      intro h
      rw [(isPrimitiveRoot_runity (by omega : n ≠ 0)).pow_eq_one_iff_dvd] at h
      have hle := Nat.le_of_dvd (by omega : 0 < 2) h
      omega
    exact sub_ne_zero.mpr h1
  have hω : (n : ℂ) * (runity n - (runity n)⁻¹) =
      (runity n ^ 2 - 1) * ((n : ℂ) * (runity n)⁻¹) := by
    have hζ0 := runity_ne_zero (by omega : n ≠ 0)
    field_simp
  have hkey : (runity n ^ 2 - 1) * ((m : ℂ) * U) =
      (runity n ^ 2 - 1) * ((n : ℂ) * (runity n)⁻¹) := by
    calc (runity n ^ 2 - 1) * ((m : ℂ) * U)
        = (m : ℂ) * ((runity n ^ 2 - 1) * U) := by ring
      _ = (m : ℂ) * ((S : ℂ) * (4 * Complex.I)) := by rw [← hUe]
      _ = (n : ℂ) * (runity n - (runity n)⁻¹) := hml
      _ = (runity n ^ 2 - 1) * ((n : ℂ) * (runity n)⁻¹) := hω
  have hkey2 : (m : ℂ) * U = (n : ℂ) * (runity n)⁻¹ := mul_left_cancel₀ hζ2 hkey
  have hratio : (n : ℂ) / (m : ℂ) = U * runity n := by
    have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
    have hζ0 := runity_ne_zero (by omega : n ≠ 0)
    rw [div_eq_iff hm0]
    calc (n : ℂ) = (n : ℂ) * ((runity n)⁻¹ * runity n) := by
          rw [inv_mul_cancel₀ hζ0, mul_one]
      _ = ((m : ℂ) * U) * runity n := by rw [hkey2, ← mul_assoc]
      _ = U * runity n * m := by ring
  have hint : IsIntegral ℤ ((n : ℂ) / (m : ℂ)) := by
    rw [hratio]
    exact hU.mul (runity_integral (by omega))
  -- descend from `ℂ` to `ℚ`
  set q : ℚ := n / m with hq
  have hqint : IsIntegral ℤ q := by
    have hcast : ((q : ℂ)) = (n : ℂ) / (m : ℂ) := by
      rw [hq]
      exact map_div₀ (algebraMap ℚ ℂ) _ _
    rw [← hcast] at hint
    exact IsIntegral.tower_bot (algebraMap ℚ ℂ).injective hint
  obtain ⟨y, hy⟩ : ∃ y : ℤ, (y : ℚ) = q := by
    haveI : IsIntegrallyClosed ℤ := GCDMonoid.toIsIntegrallyClosed
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (K := ℚ)).mp hqint
    exact ⟨y, by rwa [algebraMap_int_eq] at hy⟩
  -- conclude `m ∣ n`
  have hq2 : (m : ℚ) * y = n := by
    rw [hy, hq]
    have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
    field_simp
  have hq3 : (m : ℤ) * y = n := by exact_mod_cast hq2
  have hy0 : 0 ≤ y := by
    have hpos : (0 : ℤ) < m := by exact_mod_cast hm
    have hnn : (0 : ℤ) ≤ (m : ℤ) * y := by rw [hq3]; exact_mod_cast (Nat.zero_le n)
    have hnn2 : (0 : ℤ) ≤ y * m := by rw [mul_comm]; exact hnn
    exact nonneg_of_mul_nonneg_left hnn2 hpos
  refine ⟨⟨y.toNat, ?_⟩, hmn⟩
  have hq4 : (n : ℤ) = (m : ℤ) * (y.toNat : ℤ) := by
    rw [Int.toNat_of_nonneg hy0]
    exact hq3.symm
  exact_mod_cast hq4

/-! ## The construction: fan triangulation with cyclic coloring -/

/-- The `j`-th fan triangle `(0, j+1, j+2)`, with indices taken modulo `n`. -/
noncomputable def fanTri {n : ℕ} (hn : 0 < n) (j : ℕ) : Fin n × Fin n × Fin n :=
  (⟨0, hn⟩, ⟨(j + 1) % n, Nat.mod_lt _ hn⟩, ⟨(j + 2) % n, Nat.mod_lt _ hn⟩)

/-- The fan triangulation from the vertex `1`, as a finset of triangles. -/
noncomputable def fanTris (n : ℕ) (hn : 3 ≤ n) : Finset (Fin n × Fin n × Fin n) :=
  (Finset.range (n - 2)).image (fanTri (by omega : 0 < n))

lemma fanTris_eq {n : ℕ} (hn : 3 ≤ n) {hn0 : 0 < n} :
    fanTris n hn = (Finset.range (n - 2)).image (fanTri hn0) :=
  rfl

lemma fanTri_injOn {n : ℕ} (hn : 3 ≤ n) {hn0 : 0 < n} :
    Set.InjOn (fanTri hn0) (Finset.range (n - 2) : Set ℕ) := by
  intro j₁ hj₁ j₂ hj₂ h
  have hj₁' : j₁ < n - 2 := Finset.mem_range.mp (Finset.mem_coe.mp hj₁)
  have hj₂' : j₂ < n - 2 := Finset.mem_range.mp (Finset.mem_coe.mp hj₂)
  have h2 := congrArg (fun t : Fin n × Fin n × Fin n => t.2.1.val) h
  simp only [fanTri] at h2
  rw [Nat.mod_eq_of_lt (by omega : j₁ + 1 < n), Nat.mod_eq_of_lt (by omega : j₂ + 1 < n)] at h2
  omega

lemma fanTris_card {n : ℕ} (hn : 3 ≤ n) : (fanTris n hn).card = n - 2 := by
  have hn0 : 0 < n := by omega
  rw [fanTris_eq hn (hn0 := hn0), Finset.card_image_of_injOn (fanTri_injOn hn (hn0 := hn0)),
    Finset.card_range]

lemma triArea_fanTri {n : ℕ} (hn : 3 ≤ n) {hn0 : 0 < n} {j : ℕ} (hj : j < n - 2) :
    triArea n (fanTri hn0 j) = sArea 1 (runity n ^ (j + 1)) (runity n ^ (j + 2)) := by
  have hj1 : j + 1 < n := by omega
  have hj2 : j + 2 < n := by omega
  simp [triArea, vertex, fanTri, Nat.mod_eq_of_lt hj1, Nat.mod_eq_of_lt hj2]

lemma sAreaC_fanTri {n : ℕ} (hn : 3 ≤ n) {hn0 : 0 < n} {j : ℕ} (hj : j < n - 2) :
    sAreaC (vertex n (fanTri hn0 j).1) (vertex n (fanTri hn0 j).2.1)
        (vertex n (fanTri hn0 j).2.2) =
      sAreaC 1 (runity n ^ (j + 1)) (runity n ^ (j + 2)) := by
  rw [← cast_triArea, ← cast_sArea, triArea_fanTri hn (hn0 := hn0) hj]

/-- The signed area of the polygon, as a sum over `Ico 1 (n-1)`. -/
lemma sum_range_eq_sum_Ico_one {n : ℕ} (hn : 3 ≤ n) (T : ℕ → ℂ)
    (hT0 : T 0 = 0) (hTn : T (n - 1) = 0) :
    ∑ j ∈ Finset.range n, T j = ∑ j ∈ Finset.Ico 1 (n - 1), T j := by
  symm
  refine Finset.sum_subset_zero_on_sdiff (fun j hj => ?_) (fun j hj => ?_) (fun j _ => rfl)
  · rw [Finset.mem_Ico] at hj
    exact Finset.mem_range.mpr (by omega)
  · rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_Ico] at hj
    obtain ⟨hjn, hnot⟩ := hj
    have hcase : j = 0 ∨ j = n - 1 := by
      by_contra hne
      push Not at hne
      exact hnot ⟨by omega, by omega⟩
    rcases hcase with rfl | rfl
    · exact hT0
    · exact hTn

lemma sum_Ico_one_eq {n : ℕ} (T : ℕ → ℂ) (hn : 3 ≤ n) :
    ∑ j ∈ Finset.Ico 1 (n - 1), T j = ∑ j ∈ Finset.range (n - 2), T (j + 1) := by
  rw [show (n : ℕ) - 2 = n - 1 - 1 by omega]
  rw [Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  rw [Nat.add_comm 1 j]

lemma fanTris_area_sum {n : ℕ} (hn : 3 ≤ n) :
    ∑ t ∈ fanTris n hn, triArea n t = polyArea n := by
  have hn0 : 0 < n := by omega
  apply Complex.ofReal_injective
  rw [fanTris_eq hn (hn0 := hn0),
    Finset.sum_image (fun j₁ hj₁ j₂ hj₂ h =>
      fanTri_injOn hn (hn0 := hn0) (Finset.mem_coe.mpr hj₁) (Finset.mem_coe.mpr hj₂) h)]
  push_cast
  simp only [cast_triArea]
  rw [Finset.sum_congr rfl (fun j hj => sAreaC_fanTri hn (hn0 := hn0) (Finset.mem_range.mp hj))]
  have hT0 : sAreaC 1 (runity n ^ 0) (runity n ^ (0 + 1)) = 0 := by
    rw [pow_zero]
    exact sAreaC_one_one _
  have hTn : sAreaC 1 (runity n ^ (n - 1)) (runity n ^ (n - 1 + 1)) = 0 := by
    have h1 : n - 1 + 1 = n := by omega
    rw [h1, runity_pow]
    exact sAreaC_one_self_one _
  have hshift : ∑ j ∈ Finset.range (n - 2), sAreaC 1 (runity n ^ (j + 1)) (runity n ^ (j + 2)) =
      ∑ j ∈ Finset.range n, sAreaC 1 (runity n ^ j) (runity n ^ (j + 1)) := by
    rw [sum_range_eq_sum_Ico_one hn _ hT0 hTn, sum_Ico_one_eq _ hn]
  rw [hshift, ← polyArea_cast_sum]

/-- The fan triangulation is a `Triangulation`. -/
noncomputable def fanTriangulation (n : ℕ) (hn : 3 ≤ n) : Triangulation n where
  tris := fanTris n hn
  card_tris := fanTris_card hn
  area_sum := fanTris_area_sum hn

/-- The color sum of color `r` in the fan triangulation with cyclic coloring. -/
lemma fanTris_colorSum {m n : ℕ} (hm : 0 < m) (hn : 3 ≤ n) (hdvd : m ∣ n) (hlt : m < n)
    (r : Fin m) :
    ((∑ t ∈ (fanTris n hn).filter (fun t => (⟨t.2.1.val % m, Nat.mod_lt _ hm⟩ : Fin m) = r),
        triArea n t : ℝ) : ℂ) =
      ((n / m : ℕ) : ℂ) * (runity n - (runity n)⁻¹) / (4 * Complex.I) := by
  classical
  have hn0 : 0 < n := by omega
  have hcv : ∀ j : ℕ, j < n - 2 →
      ((fanTri hn0 j).2.1.val % m = r.val ↔ (j + 1) % m = r.val) := by
    intro j hj
    have hj1 : j + 1 < n := by omega
    simp [fanTri, Nat.mod_eq_of_lt hj1]
  have himg : (fanTris n hn).filter (fun t => (⟨t.2.1.val % m, Nat.mod_lt _ hm⟩ : Fin m) = r) =
      ((Finset.range (n - 2)).filter (fun j => (j + 1) % m = r.val)).image (fanTri hn0) := by
    rw [fanTris_eq hn (hn0 := hn0)]
    ext t
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨⟨j, hj, rfl⟩, hcond⟩
      rw [Fin.ext_iff] at hcond
      exact ⟨j, ⟨hj, (hcv j hj).mp hcond⟩, rfl⟩
    · rintro ⟨j, ⟨hj, hcond⟩, rfl⟩
      refine ⟨⟨j, hj, rfl⟩, ?_⟩
      rw [Fin.ext_iff]
      exact (hcv j hj).mpr hcond
  rw [himg, Finset.sum_image (fun j₁ hj₁ j₂ hj₂ h =>
    fanTri_injOn hn (hn0 := hn0) (Finset.mem_coe.mpr (Finset.mem_of_mem_filter _ hj₁))
      (Finset.mem_coe.mpr (Finset.mem_of_mem_filter _ hj₂)) h)]
  push_cast
  simp only [cast_triArea]
  rw [Finset.sum_congr rfl (fun j hj =>
    sAreaC_fanTri hn (hn0 := hn0) (Finset.mem_range.mp (Finset.mem_of_mem_filter _ hj)))]
  -- reindex from `range (n-2)` with shifted indices to `Ico 1 (n-1)`
  have hshift : ∑ j ∈ (Finset.range (n - 2)).filter (fun j => (j + 1) % m = r.val),
        sAreaC 1 (runity n ^ (j + 1)) (runity n ^ (j + 2)) =
      ∑ j ∈ (Finset.Ico 1 (n - 1)).filter (fun j => j % m = r.val),
        sAreaC 1 (runity n ^ j) (runity n ^ (j + 1)) := by
    rw [Finset.sum_filter, Finset.sum_filter]
    rw [show n - 2 = n - 1 - 1 by omega]
    rw [Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j _
    rw [Nat.add_comm 1 j]
  rw [hshift]
  -- extend from `Ico 1 (n-1)` to `range n` (the two extra terms vanish)
  have hT0 : sAreaC 1 (runity n ^ 0) (runity n ^ (0 + 1)) = 0 := by
    rw [pow_zero]
    exact sAreaC_one_one _
  have hTn : sAreaC 1 (runity n ^ (n - 1)) (runity n ^ (n - 1 + 1)) = 0 := by
    have h1 : n - 1 + 1 = n := by omega
    rw [h1, runity_pow]
    exact sAreaC_one_self_one _
  have hext : ∑ j ∈ (Finset.Ico 1 (n - 1)).filter (fun j => j % m = r.val),
        sAreaC 1 (runity n ^ j) (runity n ^ (j + 1)) =
      ∑ j ∈ (Finset.range n).filter (fun j => j % m = r.val),
        sAreaC 1 (runity n ^ j) (runity n ^ (j + 1)) := by
    refine Finset.sum_subset_zero_on_sdiff (fun j hj => ?_) (fun j hj => ?_) (fun j _ => rfl)
    · rw [Finset.mem_filter, Finset.mem_Ico] at hj
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hj.2⟩
    · rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range, Finset.mem_filter,
        Finset.mem_Ico] at hj
      obtain ⟨⟨hjn, hjm⟩, hnot⟩ := hj
      have hcase : j = 0 ∨ j = n - 1 := by
        by_contra hne
        push Not at hne
        exact hnot ⟨⟨by omega, by omega⟩, hjm⟩
      rcases hcase with rfl | rfl
      · exact hT0
      · exact hTn
  rw [hext]
  exact sum_sAreaC_residue hm hdvd hlt r

/-- Sufficiency: if `m` is a proper divisor of `n`, the fan triangulation with
the cyclic coloring has equal color sums. -/
lemma construction {m n : ℕ} (hm : 0 < m) (hn : 3 ≤ n) (hdvd : m ∣ n) (hlt : m < n) :
    ∃ (T : Triangulation n) (c : Fin n × Fin n × Fin n → Fin m),
      ∀ i j : Fin m, colorSum T c i = colorSum T c j := by
  refine ⟨fanTriangulation n hn, fun t => ⟨t.2.1.val % m, Nat.mod_lt _ hm⟩, fun i j => ?_⟩
  apply Complex.ofReal_injective
  rw [colorSum, colorSum]
  exact (fanTris_colorSum hm hn hdvd hlt i).trans (fanTris_colorSum hm hn hdvd hlt j).symm

snip end

problem usa2024_p3 (m n : ℕ) (hm : 0 < m) (hn : 3 ≤ n) :
    (∃ (T : Triangulation n) (c : Fin n × Fin n × Fin n → Fin m),
      ∀ i j : Fin m, colorSum T c i = colorSum T c j) ↔ m ∣ n ∧ m < n := by
  constructor
  · rintro ⟨T, c, heq⟩
    exact m_dvd_and_lt hm hn T c heq
  · rintro ⟨hdvd, hlt⟩
    exact construction hm hn hdvd hlt

end Usa2024P3
