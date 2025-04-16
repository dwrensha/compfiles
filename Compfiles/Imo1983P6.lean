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

lemma mylemma_1
  (a b c : ℝ)
  (x y z : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₂: c ≤ b ∧ b ≤ a)
  (h₃: z ≤ y ∧ y ≤ x) :
  a * z + c * y + b * x ≤ c * z + b * y + a * x := by
  suffices h₄: c * (y - z) + b * (x - y) ≤ a * (x - z)
  . linarith
  . have h₅: c * (y - z) + b * (x - y) ≤ b * (y - z) + b * (x - y) := by
      simp
      refine mul_le_mul h₂.1 ?_ ?_ ?_
      . exact le_rfl
      . exact sub_nonneg_of_le h₃.1
      . exact le_of_lt h₀.2.1
    refine le_trans h₅ ?_
    rw [mul_sub, mul_sub, add_comm]
    rw [← add_sub_assoc, sub_add_cancel]
    rw [← mul_sub]
    refine mul_le_mul h₂.2 ?_ ?_ ?_
    . exact le_rfl
    . refine sub_nonneg_of_le ?_
      exact le_trans h₃.1 h₃.2
    . exact le_of_lt h₀.1


lemma mylemma_2
  (a b c : ℝ)
  (x y z : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₂: c ≤ b ∧ b ≤ a)
  (h₃: z ≤ y ∧ y ≤ x) :
  b * z + a * y + c * x ≤ c * z + b * y + a * x := by
  suffices h₄: c * (x - z) + b * (z - y) ≤ a * (x - y)
  . linarith
  . have h₅: c * (x - z) + b * (z - y) ≤ b * (x - z) + b * (z - y) := by
      simp
      refine mul_le_mul h₂.1 ?_ ?_ ?_
      . exact le_rfl
      . refine sub_nonneg_of_le ?_
        exact le_trans h₃.1 h₃.2
      . exact le_of_lt h₀.2.1
    refine le_trans h₅ ?_
    rw [mul_sub, mul_sub]
    rw [← add_sub_assoc, sub_add_cancel]
    rw [← mul_sub]
    refine mul_le_mul h₂.2 ?_ ?_ ?_
    . exact le_rfl
    . exact sub_nonneg_of_le h₃.2
    . exact le_of_lt h₀.1


-- case #1
lemma mylemma_cba
  (a b c : ℝ)
  (hap : 0 < a )
  (hbp : 0 < b )
  (hcp : 0 < c )
  (h₁ : c < a + b)
  -- (h₂ : b < a + c)
  (h₃ : a < b + c)
  (hba: b ≤ a)
  (hcb: c ≤ b) :
  0 ≤ a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a) := by
  have g₀: b * c ≤ a * c := by exact (mul_le_mul_iff_of_pos_right hcp).mpr hba
  have g₁: a * c ≤ a * b := by exact (mul_le_mul_iff_of_pos_left hap).mpr hcb
  have g₂: a * (b + c - a) ≤ b * (a + c - b) := by
    have g₂₁: 0 ≤ (a-b) * (a+b-c) := by
      refine mul_nonneg ?_ ?_
      . exact sub_nonneg_of_le hba
      . refine le_of_lt ?_
        exact sub_pos.mpr h₁
    linarith
  have g₃: b * (a + c - b) ≤ c * (a + b - c) := by
    have g₃₁: 0 ≤ (b - c) * (b + c - a) := by
      refine mul_nonneg ?_ ?_
      . exact sub_nonneg_of_le hcb
      . refine le_of_lt ?_
        exact sub_pos.mpr h₃
    linarith
  have g₄: (a * b) * (a * (b + c - a)) + (b * c) * (b * (a + c - b)) + (a * c) * (c * (a + b - c))
      ≤ (b * c) * (a * (b + c - a)) + (a * c) * (b * (a + c - b)) + (a * b) * (c * (a + b - c)) := by
    refine mylemma_1 (a * b) (a * c) (b * c) (c * (a + b - c)) (b * (a + c - b)) (a * (b + c - a)) ?_ ?_ ?_
    . constructor
      . exact mul_pos hap hbp
      . constructor
        . exact mul_pos hap hcp
        . exact mul_pos hbp hcp
    . exact { left := g₀, right := g₁ }
    . exact { left := g₂, right := g₃ }
  linarith

-- tight version
lemma mylemma_cba_tight
    (a b c : ℝ)
    (hap : 0 < a)
    (hbp : 0 < b)
    (hcp : 0 < c)
    (h₁ : c < a + b)
    (h₃ : a < b + c)
    (hba: b ≤ a)
    (hcb: c ≤ b) :
    0 ≤ a^2 * c * (a - c) + c^2 * b * (c - b) + b^2 * a * (b - a) := by
  have g₀: b * c ≤ a * c := by exact (mul_le_mul_iff_of_pos_right hcp).mpr hba
  have g₁: a * c ≤ a * b := by exact (mul_le_mul_iff_of_pos_left hap).mpr hcb
  have g₂: a * (b + c - a) ≤ b * (a + c - b) := by
    have g₂₁: 0 ≤ (a-b) * (a+b-c) := by
      refine mul_nonneg ?_ ?_
      . exact sub_nonneg_of_le hba
      . refine le_of_lt ?_
        exact sub_pos.mpr h₁
    linarith
  have g₃: b * (a + c - b) ≤ c * (a + b - c) := by
    have g₃₁: 0 ≤ (b - c) * (b + c - a) := by
      refine mul_nonneg ?_ ?_
      . exact sub_nonneg_of_le hcb
      . refine le_of_lt ?_
        exact sub_pos.mpr h₃
    linarith
  have g₄: (a * c) * (a * (b + c - a)) + (a * b) * (b * (a + c - b)) + (b * c) * (c * (a + b - c))
      ≤ (b * c) * (a * (b + c - a)) + (a * c) * (b * (a + c - b)) + (a * b) * (c * (a + b - c)) := by
    refine mylemma_2 (a * b) (a * c) (b * c) (c * (a + b - c)) (b * (a + c - b)) (a * (b + c - a)) ?_ ?_ ?_
    . constructor
      . exact mul_pos hap hbp
      . constructor
        . exact mul_pos hap hcp
        . exact mul_pos hbp hcp
    . exact { left := g₀, right := g₁ }
    . exact { left := g₂, right := g₃ }
  linarith

section triangle_inequality

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
         [StrictConvexSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

/-
These two theorems are from Eric Wieser on zulip:
https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/strict.20triangle.20inequality.20in.20Euclidean.20space/near/512427539
-/
theorem AffineIndependent.dist_strict_triangle
    {Ti Tj Tk : P} (hT : AffineIndependent ℝ ![Ti, Tj, Tk]) :
    dist (Ti) (Tk) < dist (Ti) (Tj) + dist (Tj) (Tk) := by
  refine lt_of_le_of_ne' (dist_triangle _ _ _) ?_
  intro H
  rw [dist_add_dist_eq_iff] at H
  rw [affineIndependent_iff_not_collinear] at hT
  apply hT; clear hT
  convert H.symm.collinear using 1
  simp [Set.image_insert_eq]

theorem AffineIndependent.dist_strict_triangle' {ι} (i j k : ι)
    (h : Function.Injective ![i, j, k]) (T : ι → P)
    (hT : AffineIndependent ℝ T) :
    dist (T i) (T k) < dist (T i) (T j) + dist (T j) (T k) := by
  refine AffineIndependent.dist_strict_triangle ?_
  convert hT.comp_embedding ⟨_, h⟩ using 1
  exact FinVec.map_eq _ ![i, j, k]

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
    have := AffineIndependent.dist_strict_triangle'
             (0 : Fin 3) 2 1 (by decide) T.points T.independent
    subst ha hb hc
    rw [dist_comm (T.points 2)] at this
    linarith

  have h₂ : b < a + c := by
    have := AffineIndependent.dist_strict_triangle'
             (0 : Fin 3) 1 2 (by decide) T.points T.independent
    subst ha hb hc
    linarith

  have h₃ : a < b + c := by
    have := AffineIndependent.dist_strict_triangle'
             (1 : Fin 3) 0 2 (by decide) T.points T.independent
    subst ha hb hc
    rw [dist_comm (T.points 1) (T.points 0)] at this
    linarith

  clear T ha hb hc
  constructor
  · wlog ho₀: b ≤ a generalizing a b c
    . clear this
      push_neg at ho₀
      wlog ho₁: c ≤ b generalizing a b c
      . clear this
        push_neg at ho₁ -- a < b < c
        rw [add_comm] at h₁ h₂ h₃
        have g₀: 0 ≤ c ^ 2 * a * (c - a) + a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) := by
          exact mylemma_cba_tight c b a hc' hb' ha' h₃ h₁ (le_of_lt ho₁) (le_of_lt ho₀)
        linarith
      . wlog ho₂: c ≤ a generalizing a b c
        . clear this -- a < c ≤ b
          push_neg at ho₂
          rw [add_comm] at h₁ h₂
          have g₀: 0 ≤ b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) + a ^ 2 * b * (a - b) := by
            exact mylemma_cba b c a hb' hc' ha' h₃ h₂ ho₁ (le_of_lt ho₂)
          linarith
        . -- c ≤ a < b
          rw [add_comm] at h₁
          have g₀: 0 ≤ b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) + a ^ 2 * b * (a - b) := by
            exact mylemma_cba_tight b a c hb' ha' hc' h₁ h₂ (le_of_lt ho₀) ho₂
          linarith
    . wlog ho₁: c ≤ b generalizing a b c
      . clear this
        push_neg at ho₁
        wlog ho₂: c ≤ a generalizing a b c
        . clear this
          push_neg at ho₂ -- b < a < c
          rw [add_comm] at h₂ h₃
          have g₀: 0 ≤ c ^ 2 * a * (c - a) + a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) := by
            exact mylemma_cba c a b hc' ha' hb' h₂ h₁ (le_of_lt ho₂) ho₀
          linarith
        . rw [add_comm] at h₃
          exact mylemma_cba_tight a c b ha' hc' hb' h₂ h₃ ho₂ (le_of_lt ho₁)
      . exact mylemma_cba a b c ha' hb' hc' h₁ h₃ ho₀ ho₁
  constructor
  · intro h
    sorry
  · rintro ⟨rfl, rfl⟩
    simp

end Imo1983P6
