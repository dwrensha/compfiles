/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.Positivity.Finset
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Geometry]
}

/-!
# International Mathematical Olympiad 1967, Problem 1

The parallelogram $ABCD$ has $AB = a$, $AD = 1$, $\angle BAD = \alpha$, and the
triangle $ABD$ has all angles acute. Prove that the circles of radius $1$ with
centers $A$, $B$, $C$, $D$ cover the parallelogram if and only if
$$a \le \cos\alpha + \sqrt{3}\sin\alpha.$$

## Formalization notes

We place the configuration in the Euclidean plane with $A = (0, 0)$,
$B = (a, 0)$, $D = (\cos\alpha, \sin\alpha)$ (so that $AD = 1$ and
$\angle BAD = \alpha$), and hence $C = B + D - A = (a + \cos\alpha, \sin\alpha)$.
The parallelogram is parametrized as the set of points
$\sigma B + \tau D$ with $0 \le \sigma, \tau \le 1$.
With this parametrization, acuteness of the angle at $A$ is $\alpha < \pi/2$,
while acuteness of the angles at $B$ and $D$ is equivalent to
$\cos\alpha < a$ and $a \cos\alpha < 1$ respectively
(compute the cosines of those angles via dot products).
-/

namespace Imo1967P1

open Real

/-- The covering condition: every point `σ • B + τ • D` of the parallelogram,
written in coordinates as `(σ * a + τ * cos α, τ * sin α)`, is within distance `1`
of one of the four vertices
`A = (0, 0)`, `B = (a, 0)`, `C = (a + cos α, sin α)`, `D = (cos α, sin α)`. -/
def Covers (a α : ℝ) : Prop :=
  ∀ σ τ : ℝ, 0 ≤ σ → σ ≤ 1 → 0 ≤ τ → τ ≤ 1 →
    ∃ V ∈ ({!₂[0, 0], !₂[a, 0], !₂[a + Real.cos α, Real.sin α], !₂[Real.cos α, Real.sin α]} :
        Finset (EuclideanSpace ℝ (Fin 2))),
      dist !₂[σ * a + τ * Real.cos α, τ * Real.sin α] V ≤ 1

snip begin

/-- Squared distance between two points of the plane given in coordinates. -/
lemma dist_sq (x₁ y₁ x₂ y₂ : ℝ) :
    (dist (!₂[x₁, y₁] : EuclideanSpace ℝ (Fin 2)) !₂[x₂, y₂]) ^ 2
      = (x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

/-- Distance at most `1` between two points of the plane, in coordinates. -/
lemma dist_le_one_iff (x₁ y₁ x₂ y₂ : ℝ) :
    dist (!₂[x₁, y₁] : EuclideanSpace ℝ (Fin 2)) !₂[x₂, y₂] ≤ 1
      ↔ (x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2 ≤ 1 := by
  rw [EuclideanSpace.dist_eq, Real.sqrt_le_one]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

/-- A weighted average of three real numbers, with nonnegative weights
summing to `1`, is at least their minimum. -/
lemma min3_le_weighted {u v w x y z : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (h : u + v + w = 1) : min (min x y) z ≤ u * x + v * y + w * z := by
  have g1 : (0 : ℝ) ≤ u * (x - min (min x y) z) :=
    mul_nonneg hu (sub_nonneg.mpr (le_trans (min_le_left _ _) (min_le_left _ _)))
  have g2 : (0 : ℝ) ≤ v * (y - min (min x y) z) :=
    mul_nonneg hv (sub_nonneg.mpr (le_trans (min_le_left _ _) (min_le_right _ _)))
  have g3 : (0 : ℝ) ≤ w * (z - min (min x y) z) :=
    mul_nonneg hw (sub_nonneg.mpr (min_le_right _ _))
  have hm : (u + v + w) * min (min x y) z = min (min x y) z := by rw [h]; ring
  linarith

/-- The algebraic heart of the covering argument.

Let `A = (0, 0)`, `B = (a, 0)`, `D = (c, s)` with `c = cos α`, `s = sin α`, and let
`R` be the circumradius of the triangle `ABD`, so that `R² = BD² / (4 s²)`
with `BD² = (a - c)² + s²`.  If `R ≤ 1` (expressed as `BD² ≤ 4 s²`), then every
point `v • B + w • D` of the triangle `ABD` (where `0 ≤ v, w` and `v + w ≤ 1`)
is within distance `1` of one of the vertices `A`, `B`, `D`.

Writing `u = 1 - v - w`, the weighted sum `u * PA² + v * PB² + w * PD²` equals
`u v a² + v w BD² + w u AD²`, and the latter is at most `R²` because of the
explicit sum-of-squares identity
`a² BD² (BD² (u+v+w)² - 4 s² (u v a² + v w BD² + w u)) = X² + Y²`
for suitable `X`, `Y` (this is the algebraic content of the classical fact that
an acute triangle is covered by the circles of radius `R` around its vertices). -/
lemma cover_triangle (a c s v w : ℝ) (ha : 0 < a) (hsp : 0 < s)
    (hs : s ^ 2 + c ^ 2 = 1) (hR : (a - c) ^ 2 + s ^ 2 ≤ 4 * s ^ 2)
    (hv : 0 ≤ v) (hw : 0 ≤ w) (hvw : v + w ≤ 1) :
    (v * a + w * c) ^ 2 + (w * s) ^ 2 ≤ 1 ∨
    (v * a + w * c - a) ^ 2 + (w * s) ^ 2 ≤ 1 ∨
    (v * a + w * c - c) ^ 2 + (w * s - s) ^ 2 ≤ 1 := by
  have hu : (0 : ℝ) ≤ 1 - v - w := by linarith
  have hs2p : (0 : ℝ) < s ^ 2 := by positivity
  have hb2p : (0 : ℝ) < (a - c) ^ 2 + s ^ 2 := by linarith [sq_nonneg (a - c), hs2p]
  -- weighted sum of squared distances
  have hW : (1 - v - w) * ((v * a + w * c) ^ 2 + (w * s) ^ 2)
        + v * ((v * a + w * c - a) ^ 2 + (w * s) ^ 2)
        + w * ((v * a + w * c - c) ^ 2 + (w * s - s) ^ 2)
      = (1 - v - w) * v * a ^ 2 + v * w * ((a - c) ^ 2 + s ^ 2) + (1 - v - w) * w := by
    linear_combination (w * (1 - v - w)) * hs
  -- the sum-of-squares identity
  have hSOS : a ^ 2 * ((a - c) ^ 2 + s ^ 2)
        * (((a - c) ^ 2 + s ^ 2) * (1 - v - w + v + w) ^ 2
          - 4 * s ^ 2 * ((1 - v - w) * v * a ^ 2 + v * w * ((a - c) ^ 2 + s ^ 2)
            + (1 - v - w) * w))
      = (a * (((a - c) ^ 2 + s ^ 2) * (1 - v - w + v + w)
            - 2 * s ^ 2 * (v * a ^ 2 + w))) ^ 2
        + (s * (v * a ^ 2 * (((a - c) ^ 2 + s ^ 2) + 1 - a ^ 2)
            - w * (a ^ 2 + ((a - c) ^ 2 + s ^ 2) - 1))) ^ 2 := by
    linear_combination (-s ^ 2 * (a ^ 2 * v + w) ^ 2
      * (4 * a ^ 2 - 4 * a * c + c ^ 2 + s ^ 2 - 1)) * hs
  -- the weighted sum of the squared side lengths is at most `R² (u+v+w)²`
  have hE : (0 : ℝ) ≤ ((a - c) ^ 2 + s ^ 2) * (1 - v - w + v + w) ^ 2
      - 4 * s ^ 2 * ((1 - v - w) * v * a ^ 2 + v * w * ((a - c) ^ 2 + s ^ 2)
        + (1 - v - w) * w) := by
    have hab : (0 : ℝ) < a ^ 2 * ((a - c) ^ 2 + s ^ 2) := by positivity
    have h0 : (0 : ℝ) ≤ (a * (((a - c) ^ 2 + s ^ 2) * (1 - v - w + v + w)
          - 2 * s ^ 2 * (v * a ^ 2 + w))) ^ 2
        + (s * (v * a ^ 2 * (((a - c) ^ 2 + s ^ 2) + 1 - a ^ 2)
          - w * (a ^ 2 + ((a - c) ^ 2 + s ^ 2) - 1))) ^ 2 := by positivity
    rw [← hSOS] at h0
    exact nonneg_of_mul_nonneg_right h0 hab
  have hsum : (1 : ℝ) - v - w + v + w = 1 := by ring
  rw [hsum] at hE
  -- hence the weighted sum of squared distances is at most `1`
  have hW1 : (1 - v - w) * v * a ^ 2 + v * w * ((a - c) ^ 2 + s ^ 2)
      + (1 - v - w) * w ≤ 1 := by
    have hs4 : (0 : ℝ) < 4 * s ^ 2 := by positivity
    have h4 : 4 * s ^ 2 * ((1 - v - w) * v * a ^ 2 + v * w * ((a - c) ^ 2 + s ^ 2)
        + (1 - v - w) * w) ≤ 4 * s ^ 2 * 1 := by nlinarith [hE, hR]
    exact le_of_mul_le_mul_left h4 hs4
  -- so is their minimum
  have hmin := min3_le_weighted (x := (v * a + w * c) ^ 2 + (w * s) ^ 2)
    (y := (v * a + w * c - a) ^ 2 + (w * s) ^ 2)
    (z := (v * a + w * c - c) ^ 2 + (w * s - s) ^ 2) hu hv hw (by ring)
  rw [hW] at hmin
  have h1 := hmin.trans hW1
  rcases min_le_iff.mp h1 with h | h
  · rcases min_le_iff.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

snip end

problem imo1967_p1
    (a α : ℝ) (ha : 0 < a) (hα : 0 < α) (hα2 : α < Real.pi / 2)
    (hacuteB : Real.cos α < a) (hacuteD : a * Real.cos α < 1) :
    Covers a α ↔ a ≤ Real.cos α + Real.sqrt 3 * Real.sin α := by
  unfold Covers
  set s := Real.sin α with hs_def
  set c := Real.cos α with hc_def
  have hs : s ^ 2 + c ^ 2 = 1 := by rw [hs_def, hc_def]; exact Real.sin_sq_add_cos_sq α
  have hsp : 0 < s := by
    rw [hs_def]
    exact Real.sin_pos_of_pos_of_lt_pi hα (by linarith [hα2, Real.pi_pos])
  have hcp : 0 < c := by
    rw [hc_def]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [hα, Real.pi_pos], hα2⟩
  have hsn : s ≠ 0 := ne_of_gt hsp
  have han : a ≠ 0 := ne_of_gt ha
  constructor
  · -- covering ⇒ `a ≤ cos α + √3 sin α`: contrapositive, via the circumcenter
    intro hcov
    by_contra hna
    push_neg at hna
    -- here `R² > 1`, where `R` is the circumradius of `ABD`
    have hgt : (Real.sqrt 3 * s) ^ 2 < (a - c) ^ 2 := by
      have h1 : Real.sqrt 3 * s < a - c := by linarith [hna]
      exact pow_lt_pow_left₀ h1 (by positivity) two_ne_zero
    have hsq3 : (Real.sqrt 3 * s) ^ 2 = 3 * s ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    have hb2gt : 4 * s ^ 2 < (a - c) ^ 2 + s ^ 2 := by nlinarith [hgt, hsq3]
    have hsp4 : (0 : ℝ) < 4 * s ^ 2 := by positivity
    have hR1 : (1 : ℝ) < ((a - c) ^ 2 + s ^ 2) / (4 * s ^ 2) := by
      rw [lt_div_iff₀ hsp4]
      nlinarith [hb2gt]
    -- the circumcenter `O = (a/2, (1 - a c)/(2 s))` lies in the parallelogram:
    -- `O = σ₀ • B + τ₀ • D` with `σ₀ = (a - c)/(2 a s²)`, `τ₀ = (1 - a c)/(2 s²)`
    have hσ0 : (0 : ℝ) ≤ (a - c) / (2 * a * s ^ 2) :=
      div_nonneg (by linarith [hacuteB]) (by positivity)
    have hτ0 : (0 : ℝ) ≤ (1 - a * c) / (2 * s ^ 2) :=
      div_nonneg (by linarith [hacuteD]) (by positivity)
    have hστ1 : (a - c) / (2 * a * s ^ 2) + (1 - a * c) / (2 * s ^ 2) ≤ 1 := by
      have key : (a - c) / (2 * a * s ^ 2) + (1 - a * c) / (2 * s ^ 2)
          = 1 - c * ((a - c) ^ 2 + s ^ 2) / (2 * a * s ^ 2) := by
        field_simp [hsn, han]
        linear_combination ((-2) * a + c) * hs
      rw [key]
      have hnn : (0 : ℝ) ≤ c * ((a - c) ^ 2 + s ^ 2) / (2 * a * s ^ 2) := by positivity
      linarith
    have hσ1 : (a - c) / (2 * a * s ^ 2) ≤ 1 := by linarith [hστ1, hτ0]
    have hτ1 : (1 - a * c) / (2 * s ^ 2) ≤ 1 := by linarith [hστ1, hσ0]
    have hO : (!₂[(a - c) / (2 * a * s ^ 2) * a + (1 - a * c) / (2 * s ^ 2) * c,
          (1 - a * c) / (2 * s ^ 2) * s] : EuclideanSpace ℝ (Fin 2))
        = !₂[a / 2, (1 - a * c) / (2 * s)] := by
      have e1 : (a - c) / (2 * a * s ^ 2) * a + (1 - a * c) / (2 * s ^ 2) * c
          = a / 2 := by
        field_simp [hsn, han]
        linear_combination (-a) * hs
      have e2 : (1 - a * c) / (2 * s ^ 2) * s = (1 - a * c) / (2 * s) := by
        field_simp [hsn]
      rw [e1, e2]
    -- `O` has distance `R` from `A`, `B`, `D` and distance `> R` from `C`
    have hOA2 : (a / 2 - 0) ^ 2 + ((1 - a * c) / (2 * s) - 0) ^ 2
        = ((a - c) ^ 2 + s ^ 2) / (4 * s ^ 2) := by
      field_simp [hsn]
      linear_combination (4 * a ^ 2 - 4) * hs
    have hOB2 : (a / 2 - a) ^ 2 + ((1 - a * c) / (2 * s) - 0) ^ 2
        = ((a - c) ^ 2 + s ^ 2) / (4 * s ^ 2) := by
      field_simp [hsn]
      linear_combination (4 * a ^ 2 - 4) * hs
    have hOD2 : (a / 2 - c) ^ 2 + ((1 - a * c) / (2 * s) - s) ^ 2
        = ((a - c) ^ 2 + s ^ 2) / (4 * s ^ 2) := by
      field_simp [hsn]
      linear_combination (4 * a ^ 2 + 16 * s ^ 2 - 4) * hs
    have hOC2 : (a / 2 - (a + c)) ^ 2 + ((1 - a * c) / (2 * s) - s) ^ 2
        = ((a - c) ^ 2 + s ^ 2) / (4 * s ^ 2) + 2 * a * c := by
      field_simp [hsn]
      linear_combination (4 * a ^ 2 + 16 * s ^ 2 - 4) * hs
    -- so `O` is not covered, contradiction
    obtain ⟨V, hVmem, hVdist⟩ := hcov _ _ hσ0 hσ1 hτ0 hτ1
    rw [hO] at hVdist
    simp only [Finset.mem_insert, Finset.mem_singleton] at hVmem
    have hdist2 : (dist (!₂[a / 2, (1 - a * c) / (2 * s)] : EuclideanSpace ℝ (Fin 2)) V) ^ 2
        ≤ 1 := by
      have h2 := pow_le_pow_left₀ dist_nonneg hVdist 2
      rwa [one_pow] at h2
    rcases hVmem with rfl | rfl | rfl | rfl
    · rw [dist_sq, hOA2] at hdist2
      linarith [hR1, hdist2]
    · rw [dist_sq, hOB2] at hdist2
      linarith [hR1, hdist2]
    · rw [dist_sq, hOC2] at hdist2
      nlinarith [hR1, hdist2, mul_pos ha hcp]
    · rw [dist_sq, hOD2] at hdist2
      linarith [hR1, hdist2]
  · -- `a ≤ cos α + √3 sin α` ⇒ covering
    intro hle σ τ hσ0 hσ1 hτ0 hτ1
    -- here `R² ≤ 1`
    have hR : (a - c) ^ 2 + s ^ 2 ≤ 4 * s ^ 2 := by
      have hac : (0 : ℝ) ≤ a - c := by linarith [hacuteB]
      have h1 : (a - c) ^ 2 ≤ (Real.sqrt 3 * s) ^ 2 :=
        pow_le_pow_left₀ hac (by linarith [hle]) 2
      have hsq3 : (Real.sqrt 3 * s) ^ 2 = 3 * s ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      nlinarith [h1, hsq3]
    by_cases hστ : σ + τ ≤ 1
    · -- the point lies in the triangle `ABD`
      have h := cover_triangle a c s σ τ ha hsp hs hR hσ0 hτ0 hστ
      rcases h with h1 | h1 | h1
      · exact ⟨!₂[0, 0], by simp, (dist_le_one_iff _ _ _ _).mpr (by simpa using h1)⟩
      · exact ⟨!₂[a, 0], by simp, (dist_le_one_iff _ _ _ _).mpr (by simpa using h1)⟩
      · exact ⟨!₂[c, s], by simp, (dist_le_one_iff _ _ _ _).mpr h1⟩
    · -- the point lies in the triangle `BCD`; use the point reflection
      -- `σ ↦ 1 - σ, τ ↦ 1 - τ` through the center of the parallelogram
      push_neg at hστ
      have hv : (0 : ℝ) ≤ 1 - σ := by linarith
      have hw : (0 : ℝ) ≤ 1 - τ := by linarith
      have hvw : 1 - σ + (1 - τ) ≤ 1 := by linarith
      have h := cover_triangle a c s (1 - σ) (1 - τ) ha hsp hs hR hv hw hvw
      rcases h with h1 | h1 | h1
      · refine ⟨!₂[a + c, s], by simp, (dist_le_one_iff _ _ _ _).mpr ?_⟩
        have e : (σ * a + τ * c - (a + c)) ^ 2 + (τ * s - s) ^ 2
            = ((1 - σ) * a + (1 - τ) * c) ^ 2 + ((1 - τ) * s) ^ 2 := by ring
        rwa [e]
      · refine ⟨!₂[c, s], by simp, (dist_le_one_iff _ _ _ _).mpr ?_⟩
        have e : (σ * a + τ * c - c) ^ 2 + (τ * s - s) ^ 2
            = ((1 - σ) * a + (1 - τ) * c - a) ^ 2 + ((1 - τ) * s) ^ 2 := by ring
        rwa [e]
      · refine ⟨!₂[a, 0], by simp, (dist_le_one_iff _ _ _ _).mpr ?_⟩
        have e : (σ * a + τ * c - a) ^ 2 + (τ * s - 0) ^ 2
            = ((1 - σ) * a + (1 - τ) * c - c) ^ 2 + ((1 - τ) * s - s) ^ 2 := by ring
        rwa [e]

end Imo1967P1
