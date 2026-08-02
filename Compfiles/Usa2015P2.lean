/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Geometry.Euclidean.Sphere.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 2015, Problem 2

Quadrilateral $APBQ$ is inscribed in circle $\omega$ with $\angle P = \angle Q = 90^\circ$
and $AP = AQ < BP$. Let $X$ be a variable point on segment $PQ$. Line $AX$ meets $\omega$
again at $S$ (other than $A$). Point $T$ lies on arc $AQB$ of $\omega$ such that $XT$ is
perpendicular to $AX$. Let $M$ denote the midpoint of chord $ST$.

As $X$ varies on segment $PQ$, show that $M$ moves along a circle.
-/

open scoped RealInnerProductSpace

namespace Usa2015P2

noncomputable scoped instance : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)

snip begin

/--
For vectors `a`, `p`, `q` from the center of a sphere of radius `R` to three points
on the sphere, the equality of chords `AP = AQ` is equivalent to `⟪a, p⟫ = ⟪a, q⟫`.
-/
lemma inner_eq_of_dist_eq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {a p q : V} {R : ℝ} (ha : ‖a‖ = R) (hp : ‖p‖ = R) (hq : ‖q‖ = R)
    (h : ‖a - p‖ = ‖a - q‖) : ⟪a, p⟫ = ⟪a, q⟫ := by
  have h2 : ‖a - p‖ ^ 2 = ‖a - q‖ ^ 2 := by rw [h]
  rw [norm_sub_sq_real, norm_sub_sq_real, ha, hp, hq] at h2
  linarith

/--
The algebraic heart of the problem.  All vectors are taken relative to the center `O`
of `ω`, so `a`, `s`, `t`, `q` have norm `R`.  Write the point `S` on line `AX` as
`s = a + μ • (x - a)` (so `μ = AS / AX`).  The hypothesis that `S` lies on `ω`
determines `μ * ‖x - a‖² = 2 * (R² - ⟪a, x⟫)` (this is the relation `AX · AS = AQ²`
of the official solution, since `⟪a, x⟫ = ⟪a, q⟫` holds for every `X` on the line
`PQ`, the line `PQ` being perpendicular to `OA` as `AP = AQ`).  Together with
`XT ⊥ AX` this gives that `M = (S + T)/2` stays at squared distance
`R²/4 + AQ²/2` from the midpoint of `AO`, independently of `X`.
-/
lemma dist_sq_midpoint_midpoint {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {a s t x q : V} {R μ : ℝ}
    (ha : ‖a‖ = R) (hs : ‖s‖ = R) (ht : ‖t‖ = R) (hq : ‖q‖ = R)
    (hμ : μ ≠ 0) (hseq : s = a + μ • (x - a))
    (hperp : ⟪x - a, t - x⟫ = 0) (haxq : ⟪a, x⟫ = ⟪a, q⟫) :
    ‖(⅟2 : ℝ) • (s + t - a)‖ ^ 2 = R ^ 2 / 4 + ‖a - q‖ ^ 2 / 2 := by
  have ha2 : ⟪a, a⟫ = R ^ 2 := by rw [real_inner_self_eq_norm_sq, ha]
  have ht2 : ⟪t, t⟫ = R ^ 2 := by rw [real_inner_self_eq_norm_sq, ht]
  have hq2 : ⟪q, q⟫ = R ^ 2 := by rw [real_inner_self_eq_norm_sq, hq]
  -- From `S` on the sphere: `μ * ⟪x - a, x - a⟫ = 2 * (R^2 - ⟪a, x⟫)`.
  have hC : μ * ⟪x - a, x - a⟫ = 2 * (R ^ 2 - ⟪a, x⟫) := by
    have h : ‖a + μ • (x - a)‖ ^ 2 = R ^ 2 := by rw [← hseq, hs]
    rw [norm_add_sq_real, ha] at h
    simp only [← real_inner_self_eq_norm_sq, real_inner_smul_left,
      real_inner_smul_right] at h
    rw [inner_sub_right, ha2] at h
    have h' : μ * (2 * (⟪a, x⟫ - R ^ 2) + μ * ⟪x - a, x - a⟫) = 0 := by
      linear_combination h
    rcases mul_eq_zero.mp h' with h0 | h0
    · exact absurd h0 hμ
    · linear_combination h0
  -- From `XT ⊥ AX`: `⟪x - a, t⟫ = ⟪x - a, x⟫`.
  have hperp' : ⟪x - a, t⟫ = ⟪x - a, x⟫ := by
    have h := hperp
    rw [inner_sub_right] at h
    linear_combination h
  -- Expand everything into inner products and finish by linear algebra.
  have e1 : (⅟2 : ℝ) • (s + t - a) = (⅟2 : ℝ) • (μ • (x - a) + t) := by
    rw [hseq]; congr 1; abel
  rw [e1, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, invOf_eq_inv]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, ← real_inner_comm a x,
    ← real_inner_comm a t, ← real_inner_comm a q, ← real_inner_comm x t] at hC hperp' haxq ⊢
  rw [ha2] at hC
  rw [ha2, ht2, hq2]
  linear_combination ((2 : ℝ)⁻¹ * (2 : ℝ)⁻¹ * μ + (2 : ℝ)⁻¹) * hC + (2 : ℝ)⁻¹ * μ * hperp' - haxq

snip end

/--
**USA Mathematical Olympiad 2015, Problem 2.**

The locus of `M` is the circle centered at the midpoint of `AO` (where `O` is the
center of `ω`) of radius `√(R²/4 + AQ²/2)`, where `R` is the radius of `ω`.

The hypotheses `_hB`, `_hAPB`, `_hAQB`, `_hlt` and `_hPQ` record the full original
configuration (in particular `AB` is a diameter of `ω`, by the converse of Thales'
theorem); they are not needed for the conclusion.  Likewise the conclusion holds
for either of the two points `T` of `ω` with `XT ⊥ AX`, so the arc condition on `T`
is dropped.
-/
problem usa2015_p2 {V : Type*} {Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace Pt] [NormedAddTorsor V Pt]
    (Ω : EuclideanGeometry.Sphere Pt)
    (A B P Q X S T M : Pt)
    (hA : A ∈ Ω) (_hB : B ∈ Ω) (hP : P ∈ Ω) (hQ : Q ∈ Ω)
    (hS : S ∈ Ω) (hT : T ∈ Ω)
    (_hPQ : P ≠ Q)
    (_hAPB : ⟪A -ᵥ P, B -ᵥ P⟫ = 0)  -- ∠APB = 90°
    (_hAQB : ⟪A -ᵥ Q, B -ᵥ Q⟫ = 0)  -- ∠AQB = 90°
    (hAPAQ : dist A P = dist A Q)   -- AP = AQ
    (_hlt : dist A P < dist B P)    -- AP < BP
    (hX : Wbtw ℝ P X Q)             -- X lies on segment PQ
    (hSline : S ∈ line[ℝ, A, X])    -- S lies on line AX
    (hSA : S ≠ A)                   -- S ≠ A
    (hperp : ⟪T -ᵥ X, A -ᵥ X⟫ = 0)  -- XT ⊥ AX
    (hM : M = midpoint ℝ S T) :     -- M is the midpoint of chord ST
    dist M (midpoint ℝ A Ω.center) = Real.sqrt (Ω.radius ^ 2 / 4 + dist A Q ^ 2 / 2) := by
  -- Distances of the points on `ω` to its center.
  have ha : ‖A -ᵥ Ω.center‖ = Ω.radius := by
    rw [← dist_eq_norm_vsub']; exact EuclideanGeometry.mem_sphere'.mp hA
  have hs : ‖S -ᵥ Ω.center‖ = Ω.radius := by
    rw [← dist_eq_norm_vsub']; exact EuclideanGeometry.mem_sphere'.mp hS
  have ht : ‖T -ᵥ Ω.center‖ = Ω.radius := by
    rw [← dist_eq_norm_vsub']; exact EuclideanGeometry.mem_sphere'.mp hT
  have hp : ‖P -ᵥ Ω.center‖ = Ω.radius := by
    rw [← dist_eq_norm_vsub']; exact EuclideanGeometry.mem_sphere'.mp hP
  have hq : ‖Q -ᵥ Ω.center‖ = Ω.radius := by
    rw [← dist_eq_norm_vsub']; exact EuclideanGeometry.mem_sphere'.mp hQ
  -- From `AP = AQ`: `⟪a, p⟫ = ⟪a, q⟫` (so the line `PQ` is perpendicular to `OA`).
  have hapq : ⟪A -ᵥ Ω.center, P -ᵥ Ω.center⟫ = ⟪A -ᵥ Ω.center, Q -ᵥ Ω.center⟫ := by
    have h1 : ‖(A -ᵥ Ω.center) - (P -ᵥ Ω.center)‖ = ‖(A -ᵥ Ω.center) - (Q -ᵥ Ω.center)‖ := by
      rw [vsub_sub_vsub_cancel_right, vsub_sub_vsub_cancel_right,
        ← dist_eq_norm_vsub, ← dist_eq_norm_vsub]
      exact hAPAQ
    exact inner_eq_of_dist_eq ha hp hq h1
  -- From `X` on segment `PQ`: `⟪a, x⟫ = ⟪a, q⟫`.
  obtain ⟨τ, -, hXτ⟩ := hX
  have haxq : ⟪A -ᵥ Ω.center, X -ᵥ Ω.center⟫ = ⟪A -ᵥ Ω.center, Q -ᵥ Ω.center⟫ := by
    rw [← hXτ, AffineMap.lineMap_apply, vadd_vsub_assoc]
    rw [show Q -ᵥ P = (Q -ᵥ Ω.center) - (P -ᵥ Ω.center) from
      (vsub_sub_vsub_cancel_right Q P Ω.center).symm]
    simp only [inner_add_right, real_inner_smul_right, inner_sub_right]
    rw [hapq]
    simp
  -- From `S` on line `AX`, `S ≠ A`: `S -ᵥ O = (A -ᵥ O) + μ • ((X -ᵥ O) - (A -ᵥ O))`, `μ ≠ 0`.
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ • (X -ᵥ A) = S -ᵥ A := by
    have hAmem : A ∈ line[ℝ, A, X] := left_mem_affineSpan_pair ℝ A X
    have h1 : S -ᵥ A ∈ (affineSpan ℝ ({A, X} : Set Pt)).direction := by
      rw [AffineSubspace.vsub_right_mem_direction_iff_mem hAmem S]
      exact hSline
    rw [direction_affineSpan, vectorSpan_pair_rev] at h1
    exact Submodule.mem_span_singleton.mp h1
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hμ
    exact hSA (vsub_eq_zero_iff_eq.mp hμ.symm)
  have hseq : S -ᵥ Ω.center = (A -ᵥ Ω.center) + μ • ((X -ᵥ Ω.center) - (A -ᵥ Ω.center)) := by
    have e1 : S -ᵥ Ω.center = μ • (X -ᵥ A) + (A -ᵥ Ω.center) := by
      rw [hμ]
      exact (vsub_add_vsub_cancel S A Ω.center).symm
    rw [e1, show X -ᵥ A = (X -ᵥ Ω.center) - (A -ᵥ Ω.center) from
      (vsub_sub_vsub_cancel_right X A Ω.center).symm]
    exact add_comm _ _
  -- The condition `XT ⊥ AX` in vector form.
  have hperp' : ⟪(X -ᵥ Ω.center) - (A -ᵥ Ω.center), (T -ᵥ Ω.center) - (X -ᵥ Ω.center)⟫ = 0 := by
    have e1 : (X -ᵥ Ω.center) - (A -ᵥ Ω.center) = X -ᵥ A :=
      vsub_sub_vsub_cancel_right X A Ω.center
    have e2 : (T -ᵥ Ω.center) - (X -ᵥ Ω.center) = T -ᵥ X :=
      vsub_sub_vsub_cancel_right T X Ω.center
    rw [e1, e2, ← neg_vsub_eq_vsub_rev A X, inner_neg_left,
      real_inner_comm (T -ᵥ X) (A -ᵥ X), hperp, neg_zero]
  -- The locus computation.
  have hlocus := dist_sq_midpoint_midpoint ha hs ht hq hμ0 hseq hperp' haxq
  have hMvec : M -ᵥ midpoint ℝ A Ω.center
      = (⅟2 : ℝ) • ((S -ᵥ Ω.center) + (T -ᵥ Ω.center) - (A -ᵥ Ω.center)) := by
    have hM1 : M -ᵥ Ω.center
        = (⅟2 : ℝ) • (S -ᵥ Ω.center) + (⅟2 : ℝ) • (T -ᵥ Ω.center) := by
      rw [hM]
      exact midpoint_vsub S T Ω.center
    have hc1 : midpoint ℝ A Ω.center -ᵥ Ω.center = (⅟2 : ℝ) • (A -ᵥ Ω.center) := by
      rw [midpoint_vsub, vsub_self, smul_zero, add_zero]
    have e : M -ᵥ midpoint ℝ A Ω.center
        = (M -ᵥ Ω.center) - (midpoint ℝ A Ω.center -ᵥ Ω.center) :=
      (vsub_sub_vsub_cancel_right M _ Ω.center).symm
    rw [e, hM1, hc1, smul_sub, smul_add]
  rw [dist_eq_norm_vsub, hMvec]
  have hAQ : ‖(A -ᵥ Ω.center) - (Q -ᵥ Ω.center)‖ = dist A Q := by
    rw [vsub_sub_vsub_cancel_right, dist_eq_norm_vsub]
  rw [hAQ] at hlocus
  rw [← hlocus]
  exact (Real.sqrt_sq (norm_nonneg _)).symm

end Usa2015P2
