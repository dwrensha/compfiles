/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roozbeh Yousefzadeh, David Renshaw
-/

import Mathlib.Analysis.Convex.StrictConvexBetween
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra, .Inequality] }

/-!
# International Mathematical Olympiad 1983, Problem 6

Suppose that a,b,c are the side lengths of a triangle. Prove that

   a²b(a - b) + b²c(b - c) + c²a(c - a) ≥ 0.

Determine when equality occurs.
-/

namespace Imo1983P6

snip begin

/-- Equality in Cauchy-Schwarz implies linear dependence. -/
lemma cauchy_schwarz_equals {ι: Type*} (s : Finset ι)
    (f g : ι → ℝ) (hf : ∃ i ∈ s, f i ≠ 0) :
    (∑ i ∈ s, f i * g i) ^ 2 = (∑ i ∈ s, f i ^ 2) * ∑ i ∈ s, g i ^ 2 →
    ∃ r, ∀ i ∈ s, r * f i = g i := by
  intro h0
  let q t := ∑ i ∈ s, (t * f i - g i) * (t * f i - g i)
  have h1 : ∀ t, q t =
      (∑ i ∈ s, f i^2) * (t * t) + ((- 2) * ∑ i ∈ s, f i * g i) * t + ∑ i ∈ s, g i^2 := by
    intro t
    unfold q
    simp only [Finset.mul_sum, Finset.sum_mul, ←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have h2 : discrim (∑ i ∈ s, f i^2) ((- 2) * ∑ i ∈ s, f i * g i) (∑ i ∈ s, g i^2) = 0 := by
    unfold discrim
    linarith
  have h3 : ∑ i ∈ s, f i^2 ≠ 0 := by
    obtain ⟨ii, hii, hiif⟩ := hf
    have h6 : ∀ i ∈ s, f i ^ 2 = f i * f i := by
      intro h hi
      exact pow_two (f h)
    rw [Finset.sum_congr rfl h6]
    intro H
    rw [Finset.sum_mul_self_eq_zero_iff] at H
    specialize H ii hii
    contradiction
  obtain ⟨t0, ht0, -⟩ := (discrim_eq_zero_iff h3).mp h2
  rw [←h1] at ht0
  unfold q at ht0
  use t0
  rw [Finset.sum_mul_self_eq_zero_iff] at ht0
  intro i hi
  specialize ht0 i hi
  linarith

theorem lemma1 {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x * y * z * (z + x + y) = x * y ^ 3 + y * z ^ 3 + z * x ^ 3) :
    x = y ∧ x = z := by
  let f : Fin 3 → ℝ := ![√x * √(y^3), √y * √(z^3), √z * √(x^3)]
  let g : Fin 3 → ℝ := ![√z, √x, √y]
  suffices H : ∃ r : ℝ, ∀ i ∈ Finset.univ, r * f i = g i by
    obtain ⟨r, hr⟩ := H
    dsimp [f, g] at hr
    simp only [Finset.mem_univ, forall_const, f, g] at hr
    have hr0 := hr 0
    have hr1 := hr 1
    have hr2 := hr 2
    clear hr
    apply_fun (·)^2 at hr0 hr1 hr2
    dsimp at hr0 hr1 hr2
    simp only [mul_pow] at hr0 hr1 hr2
    rw [Real.sq_sqrt hx.le, Real.sq_sqrt hy.le] at hr1
    rw [Real.sq_sqrt hz.le, Real.sq_sqrt hx.le] at hr0
    rw [Real.sq_sqrt hy.le, Real.sq_sqrt hz.le] at hr2
    rw [Real.sq_sqrt (by positivity)] at hr0 hr1 hr2
    have h0 : x * y^3 ≠ 0 := by positivity
    have h1 : y * z^3 ≠ 0 := by positivity
    have h2 : z * x^3 ≠ 0 := by positivity
    replace hr0 : r^2 = z / (x * y^3) := (div_eq_of_eq_mul h0 hr0.symm).symm
    replace hr1 : r^2 = x / (y * z^3) := (div_eq_of_eq_mul h1 hr1.symm).symm
    replace hr2 : r^2 = y / (z * x^3) := (div_eq_of_eq_mul h2 hr2.symm).symm
    clear hxyz f g
    constructor
    · rw [hr0] at hr1 hr2
      have h3 : z^4 = x^2 * y^2 := by
        field_simp at hr1 ⊢
        nlinarith
      have h3' : z^2 = x * y := by
        rw [show z ^ 4 = (z^2)^2 by ring, show x ^ 2 * y ^ 2 = (x * y)^2 by ring] at h3
        exact (pow_left_inj₀ (by positivity) (by positivity) (by positivity)).mp h3
      have h4 : z^2 = y^4 / x^2 := by
        field_simp at hr2 ⊢
        nlinarith
      rw [h3'] at h4
      have h5 : x^3 = y ^ 3 := by
        field_simp at h4
        ring_nf at h4 ⊢
        rw [show y^4 = y ^3 * y from rfl] at h4
        nlinarith
      exact (pow_left_inj₀ (by positivity) (by positivity) (by positivity)).mp h5
    · rw [hr2] at hr0 hr1
      have h3 : y^4 = x^2 * z^2 := by
        field_simp at hr0 ⊢
        nlinarith
      have h3' : y^2 = x * z := by
        rw [show y ^ 4 = (y^2)^2 by ring, show x ^ 2 * z ^ 2 = (x * z)^2 by ring] at h3
        exact (pow_left_inj₀ (by positivity) (by positivity) (by positivity)).mp h3
      have h4 : y^2 = x^4 / z^2 := by
        field_simp at hr1 ⊢
        nlinarith
      rw [h3'] at h4
      have h5 : z^3 = x ^ 3 := by
        field_simp at h4
        ring_nf at h4 ⊢
        rw [show x^4 = x^3 * x from rfl] at h4
        nlinarith
      symm
      exact (pow_left_inj₀ (by positivity) (by positivity) (by positivity)).mp h5
  refine cauchy_schwarz_equals _ f g ?_ ?_
  · use 0
    simp [f]
    change _ ≠ 0 ∧ _ ≠ 0
    constructor
    · positivity
    · positivity
  simp only [Fin.sum_univ_three, f, g]
  dsimp
  rw [show x^3 = x^2 * x from rfl, show y^3 = y^2 * y from rfl,
      show z^3 = z^2 * z from rfl]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
      Real.sqrt_mul (by positivity)]
  rw [Real.sqrt_sq hx.le, Real.sqrt_sq hy.le, Real.sqrt_sq hz.le]
  have h1 : √x * (y * √y) * √z + √y * (z * √z) * √x + √z * (x * √x) * √y =
            (√x * √y * √z) * (z + x + y) := by ring
  rw [h1]; clear h1
  simp only [mul_pow]
  simp only [Real.sq_sqrt hx.le, Real.sq_sqrt hy.le, Real.sq_sqrt hz.le]
  rw [pow_two (z + x + y), ←mul_assoc]
  apply_fun (· * (z + x + y)) at hxyz
  linarith

section triangle_inequality

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
         [StrictConvexSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

/-
This theorem is from Eric Wieser on zulip:
https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/strict.20triangle.20inequality.20in.20Euclidean.20space/near/512427539
-/
theorem AffineIndependent.dist_strict_triangle {ι} (i j k : ι) (h : Function.Injective ![i, j, k]) (T : ι → P) (hT : AffineIndependent ℝ T) :
    dist (T i) (T k) < dist (T i) (T j) + dist (T j) (T k) := by
  refine lt_of_le_of_ne' (dist_triangle _ _ _) ?_
  intro H
  rw [dist_add_dist_eq_iff] at H
  replace hT := hT.comp_embedding ⟨_, h⟩
  rw [affineIndependent_iff_not_collinear, Set.range_comp] at hT
  apply hT; clear hT
  convert H.symm.collinear using 1
  simp [Set.image_insert_eq]

end triangle_inequality

snip end

determine EqualityCondition (a b c : ℝ) : Prop := a = b ∧ a = c

problem imo1983_p6 (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) :
    let a := dist (T.points 1) (T.points 2)
    let b := dist (T.points 0) (T.points 2)
    let c := dist (T.points 0) (T.points 1)
    0 ≤ a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a) ∧
    (0 = a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a) ↔
     EqualityCondition a b c) := by
  intro a b c
  have h₁ : c < a + b := by
    have := AffineIndependent.dist_strict_triangle
             (0 : Fin 3) 2 1 (by decide) T.points T.independent
    rw [dist_comm (T.points 2)] at this
    linarith

  have h₂ : b < a + c := by
    have := AffineIndependent.dist_strict_triangle
             (0 : Fin 3) 1 2 (by decide) T.points T.independent
    linarith

  have h₃ : a < b + c := by
    have := AffineIndependent.dist_strict_triangle
             (1 : Fin 3) 0 2 (by decide) T.points T.independent
    rw [dist_comm (T.points 1) (T.points 0)] at this
    linarith

  -- https://prase.cz/kalva/imo/isoln/isoln836.html
  set x := (-a + b + c) / 2
  set y := (a - b + c) / 2
  set z := (a + b - c) / 2
  have hx : 0 < x := by unfold x; linarith
  have hy : 0 < y := by unfold y; linarith
  have hz : 0 < z := by unfold z; linarith

  constructor
  · suffices H : x * y * z * (z + x + y) ≤ x * y ^3 + y * z^3 + z * x ^3 by
      unfold x y z at H
      nlinarith
    let f : Fin 3 → ℝ := ![√x * √(y^3), √y * √(z^3), √z * √(x^3)]
    let g : Fin 3 → ℝ := ![√z, √x, √y]
    have hsum := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ) f g
    simp only [Fin.sum_univ_three, f, g] at hsum
    dsimp at hsum
    rw [show x^3 = x^2 * x from rfl, show y^3 = y^2 * y from rfl,
        show z^3 = z^2 * z from rfl] at hsum
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
        Real.sqrt_mul (by positivity)] at hsum
    rw [Real.sqrt_sq hx.le, Real.sqrt_sq hy.le, Real.sqrt_sq hz.le] at hsum
    have h1 : √x * (y * √y) * √z + √y * (z * √z) * √x + √z * (x * √x) * √y =
              (√x * √y * √z) * (z + x + y) := by ring
    rw [h1] at hsum; clear h1
    simp only [mul_pow] at hsum
    simp only [Real.sq_sqrt hx.le, Real.sq_sqrt hy.le, Real.sq_sqrt hz.le] at hsum
    rw [pow_two (z + x + y), ←mul_assoc] at hsum
    have h2 : 0 < z + x + y := by positivity
    rw [show x^2 * x = x^3 from rfl, show y^2 * y = y^3 from rfl,
        show z^2 * z = z^3 from rfl] at hsum
    exact le_of_mul_le_mul_right hsum h2
  constructor
  · intro h
    have hxyz : x * y * z * (z + x + y) = x * y ^3 + y * z^3 + z * x ^3 := by
      unfold x y z
      linarith
    clear h h₁ h₂ h₃
    unfold EqualityCondition
    suffices H : x = y ∧ x = z by
      unfold x y z at H
      obtain ⟨H1, H2⟩ := H
      constructor
      · linarith
      · linarith
    exact lemma1 hx hy hz hxyz
  · rintro ⟨h1, h2⟩
    simp [←h1, ←h2]

end Imo1983P6
