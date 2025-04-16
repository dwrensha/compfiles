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

problem imo1983_p6
    (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)))
    (a b c : ℝ)
    (ha : a = dist (T.points 1) (T.points 2))
    (hb : b = dist (T.points 0) (T.points 2))
    (hc : c = dist (T.points 0) (T.points 1)) :
    0 ≤ a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a)
    ∧ (0 = a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a) ↔
       EqualityCondition a b c) := by
  have ha' : 0 < a := by
    have ht1 : T.points 1 ≠ T.points 2 := by
      intro H
      have := AffineIndependent.injective T.independent H
      simp_all only [Fin.isValue, Nat.reduceAdd, Fin.reduceEq]
    have : 0 < dist (T.points 1) (T.points 2) := dist_pos.mpr ht1
    rwa [ha]

  have hb' : 0 < b := by
    have ht1 : T.points 0 ≠ T.points 2 := by
      intro H
      have := AffineIndependent.injective T.independent H
      simp_all only [Fin.isValue, Nat.reduceAdd, Fin.reduceEq]
    have : 0 < dist (T.points 0) (T.points 2) := dist_pos.mpr ht1
    rwa [hb]

  have hc' : 0 < c := by
    have ht1 : T.points 0 ≠ T.points 1 := by
      intro H
      have := AffineIndependent.injective T.independent H
      simp_all only [Fin.isValue, Nat.reduceAdd, Fin.reduceEq]
    have : 0 < dist (T.points 0) (T.points 1) := dist_pos.mpr ht1
    rwa [hc]

  have h₁ : c < a + b := by
    have := AffineIndependent.dist_strict_triangle
             (0 : Fin 3) 2 1 (by decide) T.points T.independent
    subst ha hb hc
    rw [dist_comm (T.points 2)] at this
    linarith

  have h₂ : b < a + c := by
    have := AffineIndependent.dist_strict_triangle
             (0 : Fin 3) 1 2 (by decide) T.points T.independent
    subst ha hb hc
    linarith

  have h₃ : a < b + c := by
    have := AffineIndependent.dist_strict_triangle
             (1 : Fin 3) 0 2 (by decide) T.points T.independent
    subst ha hb hc
    rw [dist_comm (T.points 1) (T.points 0)] at this
    linarith

  clear T ha hb hc

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
    constructor
    · sorry
    · sorry
  · rintro ⟨rfl, rfl⟩
    simp

end Imo1983P6
