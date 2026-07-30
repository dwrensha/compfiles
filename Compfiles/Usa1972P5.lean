/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 1972, Problem 5

A pentagon is such that each triangle formed by three adjacent vertices
has area 1. Find its area, but show that there are infinitely many
incongruent pentagons with this property.
-/

namespace Usa1972P5

/-- The cross product (determinant) of two planar vectors, viewed as
points of `ℝ × ℝ`. -/
def cr (P Q : ℝ × ℝ) : ℝ := P.1 * Q.2 - P.2 * Q.1

/-- Twice the signed area of the triangle `PQR` (positive when `P`, `Q`, `R`
are oriented counterclockwise). We work with doubled areas throughout to
avoid divisions. -/
def ar (P Q R : ℝ × ℝ) : ℝ := cr (Q - P) (R - P)

/-- The predicate on an ordered tuple of five points `A, B, C, D, E` of the
plane saying that each of the five triangles `ABC`, `BCD`, `CDE`, `DEA`, `EAB`
formed by three adjacent vertices has area `1`, with consistent (say,
counterclockwise) orientation. The last condition `0 < ar A C D` selects the
convex configurations: without it self-intersecting "pentagons" satisfying
the five area equations also exist (their shoelace sum being `5 - √5`
instead of `5 + √5`). -/
def IsAreaOnePentagon (P : (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ)) : Prop :=
  ar P.1 P.2.1 P.2.2.1 = 2 ∧ ar P.2.1 P.2.2.1 P.2.2.2.1 = 2 ∧
  ar P.2.2.1 P.2.2.2.1 P.2.2.2.2 = 2 ∧ ar P.2.2.2.1 P.2.2.2.2 P.1 = 2 ∧
  ar P.2.2.2.2 P.1 P.2.1 = 2 ∧ 0 < ar P.1 P.2.2.1 P.2.2.2.1

/-- Two pentagons (given as ordered tuples of five points of the plane) are
congruent if there is a distance-preserving map of the plane taking the
vertices of one to the vertices of the other, in order. -/
def CongruentPentagons (P Q : (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ)) : Prop :=
  ∃ f : ℝ × ℝ → ℝ × ℝ, (∀ x y, dist (f x) (f y) = dist x y) ∧
    f P.1 = Q.1 ∧ f P.2.1 = Q.2.1 ∧ f P.2.2.1 = Q.2.2.1 ∧
    f P.2.2.2.1 = Q.2.2.2.1 ∧ f P.2.2.2.2 = Q.2.2.2.2

/-- The area of a pentagon such that each triangle formed by three adjacent
vertices has area `1`. -/
noncomputable determine pentagonArea : ℝ := (5 + Real.sqrt 5) / 2

snip begin

/-
## Proof sketch (following J. Scholes' solution at
## https://prase.cz/kalva/usa/usoln/usol725.html)

Let the pentagon be `ABCDE`. Triangles `BCD` and `ECD` have the same area, so
`B` and `E` have the same perpendicular distance from `CD`, hence `BE ∥ CD`;
similarly each diagonal is parallel to the side with which it has no endpoint
in common. If `X = BD ∩ CE`, then `ABXE` is a parallelogram, and putting
`x = area(DEX)` one gets `DX/XB = x/1 = (1-x)/x`, hence `x² + x - 1 = 0` and
`area(ABCDE) = 3 + x = (5 + √5)/2`.

In the formal proof we avoid constructing the intersection point `X` and
instead work with the multiplier `μ` given by `E - C = μ • (B - A)`
(which exists since `AB ∥ CE`). Writing `y` for the doubled signed area
`ar A C D` of triangle `ACD`, the parallelisms `AC ∥ DE` and `AB ∥ CE` give

* `y = -2μ`            (triangles `ACD` and `ACE` have the same area),
* `2 = μ * (2 - y)`    (expanding `ar C D E = 2`),

so `y² - 2y - 4 = 0`, i.e. `y = 1 ± √5`. The convexity hypothesis
`0 < ar A C D` forces `y = 1 + √5`, and the shoelace formula gives
`area(ABCDE) = (2 + y + 2)/2 = (5 + √5)/2`.

For the "infinitely many incongruent pentagons" part, we take one explicit
such pentagon (with `t = (√5 - 1)/2` as the ratio in which the diagonals cut
each other) and apply the area-preserving shear `(x, y) ↦ (x + k y, y)` for
`k = 2, 3, 4, ...`: the determinant of a shear is `1`, so all signed areas
are preserved, while the distance `|C D| = 2k - (√5 - 3)/2` is strictly
increasing in `k`, so the resulting pentagons are pairwise incongruent.
-/

/-- The shear map `(x, y) ↦ (x + k * y, y)`. It has determinant `1`. -/
def shear (k : ℝ) (P : ℝ × ℝ) : ℝ × ℝ := (P.1 + k * P.2, P.2)

/-- Shears preserve (doubled) signed areas. -/
lemma ar_shear (k : ℝ) (P Q R : ℝ × ℝ) :
    ar (shear k P) (shear k Q) (shear k R) = ar P Q R := by
  simp only [ar, cr, shear, Prod.fst_sub, Prod.snd_sub]
  ring

/-- First vertex of the explicit base pentagon. -/
noncomputable def baseA : ℝ × ℝ := (0, 1 + Real.sqrt 5)

/-- Second vertex of the explicit base pentagon. -/
def baseB : ℝ × ℝ := (0, 0)

/-- Third vertex of the explicit base pentagon. -/
noncomputable def baseC : ℝ × ℝ := ((Real.sqrt 5 - 1) / 2, -2)

/-- Fourth vertex of the explicit base pentagon. -/
def baseD : ℝ × ℝ := (1, 0)

/-- Fifth vertex of the explicit base pentagon. -/
noncomputable def baseE : ℝ × ℝ := ((Real.sqrt 5 - 1) / 2, 1 + Real.sqrt 5)

/-- The base pentagon satisfies the five area equations (and the convexity
selector). These are the equations of the problem, specialized to points
constructed from the ratio `t = (√5 - 1)/2` satisfying `t² + t - 1 = 0`. -/
lemma base_areas :
    ar baseA baseB baseC = 2 ∧ ar baseB baseC baseD = 2 ∧ ar baseC baseD baseE = 2 ∧
    ar baseD baseE baseA = 2 ∧ ar baseE baseA baseB = 2 ∧ 0 < ar baseA baseC baseD := by
  have hs : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hsnn := Real.sqrt_nonneg 5
  simp only [ar, cr, baseA, baseB, baseC, baseD, baseE, Prod.fst_sub, Prod.snd_sub]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination (1/2) * hs
  · ring
  · linear_combination (-1/2) * hs
  · linear_combination (1/2) * hs
  · linear_combination (1/2) * hs
  · have h6 : ((Real.sqrt 5 - 1) / 2 - 0) * (0 - (1 + Real.sqrt 5))
        - (-2 - (1 + Real.sqrt 5)) * (1 - 0) = 1 + Real.sqrt 5 := by
      linear_combination (-1/2) * hs
    rw [h6]
    linarith

/-- The distance between the sheared third and fourth base vertices is
strictly increasing in the shear parameter `k ≥ 1`, so different parameters
give incongruent pentagons. -/
lemma base_dist (k : ℝ) (hk : 1 ≤ k) :
    dist (shear k baseC) (shear k baseD) = 2 * k - (Real.sqrt 5 - 3) / 2 := by
  have hs : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs3 : Real.sqrt 5 < 3 := by nlinarith [hs, Real.sqrt_nonneg 5]
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  simp only [shear, baseC, baseD]
  have hu : (Real.sqrt 5 - 1) / 2 + k * (-2) - (1 + k * 0) = (Real.sqrt 5 - 3) / 2 - 2 * k := by
    ring
  have hneg : (Real.sqrt 5 - 3) / 2 - 2 * k < 0 := by nlinarith [hs3, hk]
  have hlt : (Real.sqrt 5 - 3) / 2 - 2 * k < -2 := by nlinarith [hs3, hk]
  rw [hu, abs_of_neg hneg]
  have h2 : |(-2 : ℝ) - 0| = 2 := by norm_num
  rw [h2, max_eq_left (by linarith [hlt] : (2 : ℝ) ≤ -((Real.sqrt 5 - 3) / 2 - 2 * k))]
  ring

snip end

/-- **USA 1972 Problem 5, first part.** If each triangle formed by three
adjacent vertices of the pentagon `ABCDE` has area `1`, then the area of the
pentagon equals `(5 + √5)/2`. We state the area hypotheses with doubled
signed areas (consistent orientation) and add `0 < ar A C D`, which holds for
convex `ABCDE` and excludes self-intersecting configurations. -/
problem usa1972_p5a (A B C D E : ℝ × ℝ)
    (hABC : ar A B C = 2) (hBCD : ar B C D = 2) (hCDE : ar C D E = 2)
    (hDEA : ar D E A = 2) (hEAB : ar E A B = 2) (hconv : 0 < ar A C D) :
    (cr A B + cr B C + cr C D + cr D E + cr E A) / 2 = pentagonArea := by
  -- It suffices to compute the doubled signed area (shoelace sum).
  have key : cr A B + cr B C + cr C D + cr D E + cr E A = 5 + Real.sqrt 5 := by
    simp only [cr, ar, Prod.fst_sub, Prod.snd_sub] at hABC hBCD hCDE hDEA hEAB hconv ⊢
    -- Equal-area triangles on the same base give parallel lines: `AB ∥ CE`.
    have p1 : (E.1 - C.1) * (B.2 - A.2) - (E.2 - C.2) * (B.1 - A.1) = 0 := by
      linear_combination hABC - hEAB
    -- and `AC ∥ DE`.
    have p3 : (C.1 - A.1) * (E.2 - D.2) - (C.2 - A.2) * (E.1 - D.1) = 0 := by
      linear_combination hDEA - hCDE
    -- `B ≠ A`, since `ar A B C = 2 ≠ 0`.
    have hBA : B ≠ A := by
      intro h
      subst h
      simp at hABC
    have hne : (B.1 - A.1) ≠ 0 ∨ (B.2 - A.2) ≠ 0 := by
      by_contra h
      push Not at h
      apply hBA
      rw [Prod.ext_iff]
      constructor <;> linarith [h.1, h.2]
    -- Hence `E - C = μ • (B - A)` for some `μ : ℝ`.
    obtain ⟨μ, hμ1, hμ2⟩ :
        ∃ μ : ℝ, E.1 - C.1 = μ * (B.1 - A.1) ∧ E.2 - C.2 = μ * (B.2 - A.2) := by
      cases hne with
      | inl h1 =>
        refine ⟨(E.1 - C.1) / (B.1 - A.1), by field_simp, ?_⟩
        rw [div_mul_eq_mul_div, eq_div_iff_mul_eq h1]
        linear_combination -p1
      | inr h2 =>
        refine ⟨(E.2 - C.2) / (B.2 - A.2), ?_, by field_simp⟩
        rw [div_mul_eq_mul_div, eq_div_iff_mul_eq h2]
        linear_combination p1
    -- The two key relations, with `y := ar A C D`:
    -- `y = -2μ` from `AC ∥ DE` and `AB ∥ CE`,
    have hC : (C.1 - A.1) * (D.2 - A.2) - (C.2 - A.2) * (D.1 - A.1) = -2 * μ := by
      linear_combination -p3 + (C.1 - A.1) * hμ2 - (C.2 - A.2) * hμ1 - μ * hABC
    -- and `μ * (2 - y) = 2` from `ar C D E = 2`.
    have hB : μ * (2 - ((C.1 - A.1) * (D.2 - A.2) - (C.2 - A.2) * (D.1 - A.1))) = 2 := by
      linear_combination -μ * hBCD - (D.1 - C.1) * hμ2 + (D.2 - C.2) * hμ1 + hCDE
    -- Eliminating `μ` gives `y² - 2y - 4 = 0`.
    have hμv : μ = -((C.1 - A.1) * (D.2 - A.2) - (C.2 - A.2) * (D.1 - A.1)) / 2 := by
      linear_combination hC / 2
    rw [hμv] at hB
    have hquad : ((C.1 - A.1) * (D.2 - A.2) - (C.2 - A.2) * (D.1 - A.1)) ^ 2
        - 2 * ((C.1 - A.1) * (D.2 - A.2) - (C.2 - A.2) * (D.1 - A.1)) - 4 = 0 := by
      linear_combination 2 * hB
    have h7 : (((C.1 - A.1) * (D.2 - A.2) - (C.2 - A.2) * (D.1 - A.1)) - 1) ^ 2 = 5 := by
      linear_combination hquad
    have hsq : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have h8 : (((C.1 - A.1) * (D.2 - A.2) - (C.2 - A.2) * (D.1 - A.1)) - 1) ^ 2
        = (Real.sqrt 5) ^ 2 := by
      linear_combination h7 - hsq
    -- The shoelace sum equals `4 + y`.
    have hS : A.1 * B.2 - A.2 * B.1 + (B.1 * C.2 - B.2 * C.1) + (C.1 * D.2 - C.2 * D.1)
        + (D.1 * E.2 - D.2 * E.1) + (E.1 * A.2 - E.2 * A.1)
        = 4 + ((C.1 - A.1) * (D.2 - A.2) - (C.2 - A.2) * (D.1 - A.1)) := by
      linear_combination hABC + hDEA
    have h15 : (1 : ℝ) < Real.sqrt 5 := by nlinarith [hsq, Real.sqrt_nonneg 5]
    -- `y - 1 = ±√5`, and convexity `0 < y` excludes the negative root.
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h8 with h9 | h9
    · linarith [hS, h9]
    · linarith [hconv, h9, h15]
  show (cr A B + cr B C + cr C D + cr D E + cr E A) / 2 = (5 + Real.sqrt 5) / 2
  linarith [key]

/-- **USA 1972 Problem 5, second part.** There are infinitely many pairwise
incongruent pentagons such that each triangle formed by three adjacent
vertices has area `1`. -/
problem usa1972_p5b :
    ∃ F : ℕ → (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ),
      (∀ n, IsAreaOnePentagon (F n)) ∧ (∀ m n, m ≠ n → ¬ CongruentPentagons (F m) (F n)) := by
  -- Shear the explicit base pentagon by `k = n + 1`.
  refine ⟨fun n => (shear ((n : ℝ) + 1) baseA, shear ((n : ℝ) + 1) baseB,
    shear ((n : ℝ) + 1) baseC, shear ((n : ℝ) + 1) baseD, shear ((n : ℝ) + 1) baseE), ?_, ?_⟩
  · intro n
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := base_areas
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [ar_shear]
    · exact g1
    · exact g2
    · exact g3
    · exact g4
    · exact g5
    · exact g6
  · intro m n hmn hcon
    obtain ⟨f, hf, _, _, hfc, hfd, _⟩ := hcon
    -- A congruence preserves the distance between the third and fourth vertices.
    have hdist : dist (shear ((m : ℝ) + 1) baseC) (shear ((m : ℝ) + 1) baseD)
        = dist (shear ((n : ℝ) + 1) baseC) (shear ((n : ℝ) + 1) baseD) := by
      rw [← hf (shear ((m : ℝ) + 1) baseC) (shear ((m : ℝ) + 1) baseD), hfc, hfd]
    rw [base_dist _ (by linarith [Nat.cast_nonneg (α := ℝ) m]),
        base_dist _ (by linarith [Nat.cast_nonneg (α := ℝ) n])] at hdist
    have hmnr : (m : ℝ) = (n : ℝ) := by linarith
    exact hmn (Nat.cast_inj.mp hmnr)

end Usa1972P5
