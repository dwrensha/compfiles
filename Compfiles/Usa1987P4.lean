/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 1987, Problem 4

M is the midpoint of XY. The points P and Q lie on a line through Y on
opposite sides of Y, such that |XQ| = 2|MP| and |XY|/2 < |MP| < 3|XY|/2.
For what value of |PY|/|QY| is |PQ| a minimum?

# Solution

The minimum is never attained. Whatever admissible positions of P and Q
one chooses, P can be moved along the line (keeping all the constraints)
so as to make |PQ| strictly smaller. Consequently there is no value of
|PY|/|QY| at which |PQ| is a minimum: |PQ| is minimized only in the
limit, as |PY|/|QY| → ∞ (equivalently, as Q → Y and P tends to the
midpoint of YY', where Y' is the point of the line with |XY'| = |XY|).
We formalize this as the statement that no admissible configuration
minimizes |PQ|.

Reference: https://prase.cz/kalva/usa/usoln/usol874.html
-/

open scoped RealInnerProductSpace

namespace Usa1987P4

variable {V Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace Pt] [NormedAddTorsor V Pt]

/-- An admissible configuration of the problem: points `X`, `Y`, `P`, `Q`
such that `P` and `Q` lie on a line through `Y`, strictly on opposite
sides of `Y`, with `|XQ| = 2|MP|` and `|XY|/2 < |MP| < 3|XY|/2`, where
`M` is the midpoint of `XY`. -/
structure Configuration (V Pt : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace Pt] [NormedAddTorsor V Pt] where
  X : Pt
  Y : Pt
  P : Pt
  Q : Pt
  /-- `P` and `Q` lie on a line through `Y`, strictly on opposite sides
  of `Y`: they are obtained from `Y` by scaling a common nonzero
  direction vector by real parameters of opposite signs. -/
  opposite_sides : ∃ v : V, ∃ p q : ℝ,
    v ≠ 0 ∧ p * q < 0 ∧ P = p • v +ᵥ Y ∧ Q = q • v +ᵥ Y
  /-- The constraint `|XQ| = 2|MP|`. -/
  hXQ : dist X Q = 2 * dist (midpoint ℝ X Y) P
  /-- The constraint `|XY|/2 < |MP|`. -/
  hMP_lower : dist X Y / 2 < dist (midpoint ℝ X Y) P
  /-- The constraint `|MP| < 3|XY|/2`. -/
  hMP_upper : dist (midpoint ℝ X Y) P < 3 * dist X Y / 2

snip begin

/-- The squared distance between the points `s • v` and `t • w`,
for a unit vector `v`. -/
lemma norm_sq_vsub_smul {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (v w : V) (hv : ‖v‖ = 1) (s t : ℝ) :
    ‖s • v - t • w‖ ^ 2 = s ^ 2 - 2 * s * t * ⟪v, w⟫ + t ^ 2 * ‖w‖ ^ 2 := by
  have h1 : ‖s • v‖ = |s| := by
    rw [norm_smul, hv, Real.norm_eq_abs, mul_one]
  rw [norm_sub_sq_real, h1, sq_abs, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_left, real_inner_smul_right]
  ring

/-- Given endpoints `X`, `Y` and a unit direction vector `v`, any real
parameter `p'` in the valid range produces an admissible configuration
on the line through `Y` with direction `v`: `P'` is the point with
parameter `p'` and `Q'` the point with parameter `2γ - 2p'`, where
`γ = ⟪v, X -ᵥ Y⟫`; then `|P'Q'| = |3p' - 2γ|`. -/
lemma build_configuration (X Y : Pt) (v : V) (hv : ‖v‖ = 1) (p' : ℝ)
    (hside : p' * (2 * ⟪v, X -ᵥ Y⟫ - 2 * p') < 0)
    (hb1 : 0 < p' * (p' - ⟪v, X -ᵥ Y⟫))
    (hb2 : p' * (p' - ⟪v, X -ᵥ Y⟫) < 2 * ‖X -ᵥ Y‖ ^ 2) :
    ∃ C' : Configuration V Pt, dist C'.P C'.Q = |3 * p' - 2 * ⟪v, X -ᵥ Y⟫| := by
  set γ := ⟪v, X -ᵥ Y⟫ with hγ
  -- Squared distances along the line, as functions of the parameter.
  have key : ∀ s t : ℝ, ‖s • v - t • (X -ᵥ Y)‖ ^ 2
      = s ^ 2 - 2 * s * t * γ + t ^ 2 * ‖X -ᵥ Y‖ ^ 2 := by
    intro s t
    rw [norm_sq_vsub_smul v (X -ᵥ Y) hv s t, ← hγ]
  have sqQ : ∀ s : ℝ, ‖s • v - (X -ᵥ Y)‖ ^ 2 = s ^ 2 - 2 * s * γ + ‖X -ᵥ Y‖ ^ 2 := by
    intro s
    have h := key s 1
    rwa [one_smul, mul_one, one_pow, one_mul] at h
  have hhalf : (⅟2 : ℝ) = 1 / 2 := by rw [invOf_eq_inv, inv_eq_one_div]
  have sqM : ∀ s : ℝ, ‖s • v - (1/2 : ℝ) • (X -ᵥ Y)‖ ^ 2
      = s ^ 2 - s * γ + ‖X -ᵥ Y‖ ^ 2 / 4 := by
    intro s
    rw [key s (1 / 2)]
    ring
  -- Distances expressed with the parametrization.
  have hc : dist X Y = ‖X -ᵥ Y‖ := dist_eq_norm_vsub _ X Y
  have hdistX : ∀ r : ℝ, dist X (r • v +ᵥ Y) = ‖r • v - (X -ᵥ Y)‖ := by
    intro r
    rw [dist_eq_norm_vsub', vadd_vsub_assoc, ← neg_vsub_eq_vsub_rev, ← sub_eq_add_neg]
  have hdistM : ∀ r : ℝ, dist (midpoint ℝ X Y) (r • v +ᵥ Y)
      = ‖r • v - (1/2 : ℝ) • (X -ᵥ Y)‖ := by
    intro r
    rw [dist_eq_norm_vsub', vadd_vsub_assoc, right_vsub_midpoint, ← neg_vsub_eq_vsub_rev,
      smul_neg, hhalf, ← sub_eq_add_neg]
  have hvne : v ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hv
    exact zero_ne_one hv
  refine ⟨⟨X, Y, p' • v +ᵥ Y, (2 * γ - 2 * p') • v +ᵥ Y,
    ⟨v, p', 2 * γ - 2 * p', hvne, hside, rfl, rfl⟩, ?_, ?_, ?_⟩, ?_⟩
  · -- |XQ'| = 2|MP'|
    rw [hdistX (2 * γ - 2 * p'), hdistM p']
    have hs : ‖(2 * γ - 2 * p') • v - (X -ᵥ Y)‖ ^ 2
        = (2 * ‖p' • v - (1/2 : ℝ) • (X -ᵥ Y)‖) ^ 2 := by
      rw [mul_pow, sqQ (2 * γ - 2 * p'), sqM p']
      ring
    exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp hs
  · -- |XY|/2 < |MP'|
    rw [hc, hdistM p']
    have hs : (‖X -ᵥ Y‖ / 2) ^ 2 < ‖p' • v - (1/2 : ℝ) • (X -ᵥ Y)‖ ^ 2 := by
      rw [sqM p']
      nlinarith [hb1]
    exact (sq_lt_sq₀ (by positivity) (norm_nonneg _)).mp hs
  · -- |MP'| < 3|XY|/2
    rw [hc, hdistM p']
    have hs : ‖p' • v - (1/2 : ℝ) • (X -ᵥ Y)‖ ^ 2 < (3 * ‖X -ᵥ Y‖ / 2) ^ 2 := by
      rw [sqM p']
      nlinarith [hb2]
    exact (sq_lt_sq₀ (norm_nonneg _) (by positivity)).mp hs
  · -- |P'Q'| = |3p' - 2γ|
    show dist (p' • v +ᵥ Y) ((2 * γ - 2 * p') • v +ᵥ Y) = |3 * p' - 2 * γ|
    rw [dist_eq_norm_vsub, vadd_vsub_vadd_cancel_right, ← sub_smul, norm_smul, hv,
      Real.norm_eq_abs, mul_one]
    congr 1
    ring

/-- The scalar heart of the solution. Write `γ` for the cosine factor of
the line. The constraint `|XQ| = 2|MP|` forces `Q`'s parameter to be
`2γ - 2p`, and then `|PQ| = |3p - 2γ|`, which is strictly monotonic in `p`
on each side of the admissible range. Hence from any admissible
parameter `p` one can strictly decrease `|PQ|` by moving `p` towards its
boundary (which is exactly where the ratio `|PY|/|QY|` tends to `∞`
resp. `0`). -/
lemma exists_better_param (p γ : ℝ) (hpq : p * (2 * γ - 2 * p) < 0) :
    ∃ p' : ℝ, p' * (2 * γ - 2 * p') < 0 ∧ 0 < p' * (p' - γ) ∧
      p' * (p' - γ) < p * (p - γ) ∧ |3 * p' - 2 * γ| < |3 * p - 2 * γ| := by
  rcases mul_neg_iff.mp hpq with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · have hγp : γ < p := by linarith
    rcases le_or_gt 0 γ with hγ | hγ
    · -- take p' = (p + γ)/2
      exact ⟨(p + γ) / 2,
        mul_neg_of_pos_of_neg (by linarith) (by linarith),
        mul_pos (by linarith) (by linarith),
        by nlinarith [mul_pos (sub_pos.mpr hγp) (show (0:ℝ) < 3 * p - γ by linarith)],
        by rw [abs_of_pos (show (0:ℝ) < 3 * ((p + γ) / 2) - 2 * γ by linarith),
          abs_of_pos (show (0:ℝ) < 3 * p - 2 * γ by linarith)]; linarith⟩
    · -- take p' = p/2
      exact ⟨p / 2,
        mul_neg_of_pos_of_neg (by linarith) (by linarith),
        mul_pos (by linarith) (by linarith),
        by nlinarith [mul_pos hp (show (0:ℝ) < 3 * p - 2 * γ by linarith)],
        by rw [abs_of_pos (show (0:ℝ) < 3 * (p / 2) - 2 * γ by linarith),
          abs_of_pos (show (0:ℝ) < 3 * p - 2 * γ by linarith)]; linarith⟩
  · have hγp : p < γ := by linarith
    rcases le_or_gt 0 γ with hγ | hγ
    · -- take p' = p/2
      exact ⟨p / 2,
        mul_neg_of_neg_of_pos (by linarith) (by linarith),
        mul_pos_of_neg_of_neg (by linarith) (by linarith),
        by nlinarith [mul_pos_of_neg_of_neg hp (show 3 * p - 2 * γ < (0:ℝ) by linarith)],
        by rw [abs_of_neg (show 3 * (p / 2) - 2 * γ < (0:ℝ) by linarith),
          abs_of_neg (show 3 * p - 2 * γ < (0:ℝ) by linarith)]; linarith⟩
    · -- take p' = (p + γ)/2
      exact ⟨(p + γ) / 2,
        mul_neg_of_neg_of_pos (by linarith) (by linarith),
        mul_pos_of_neg_of_neg (by linarith) (by linarith),
        by nlinarith [
          mul_pos_of_neg_of_neg (sub_neg.mpr hγp) (show 3 * p - γ < (0:ℝ) by linarith)],
        by rw [abs_of_neg (show 3 * ((p + γ) / 2) - 2 * γ < (0:ℝ) by linarith),
          abs_of_neg (show 3 * p - 2 * γ < (0:ℝ) by linarith)]; linarith⟩

snip end

/-- **USA Mathematical Olympiad 1987, Problem 4.**
There is no admissible configuration minimizing `|PQ|`: from every
admissible configuration one can produce another admissible
configuration with strictly smaller `|PQ|`. Hence the minimum of `|PQ|`
is attained for no value of `|PY|/|QY|` (it is approached only in the
limit, as `|PY|/|QY| → ∞`). -/
problem usa1987_p4 (C : Configuration V Pt) :
    ∃ C' : Configuration V Pt, dist C'.P C'.Q < dist C.P C.Q := by
  obtain ⟨X, Y, P, Q, hopps, hXQ, hlo, hhi⟩ := C
  show ∃ C' : Configuration V Pt, dist C'.P C'.Q < dist P Q
  obtain ⟨v₀, p₀, q₀, hv₀, hp₀q₀, hP, hQ⟩ := hopps
  -- Normalize the direction vector to unit length.
  have hn : 0 < ‖v₀‖ := norm_pos_iff.mpr hv₀
  set v := ‖v₀‖⁻¹ • v₀ with hv_def
  have hv : ‖v‖ = 1 := by
    rw [hv_def, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn),
      inv_mul_cancel₀ hn.ne']
  set p := p₀ * ‖v₀‖ with hp_def
  set q := q₀ * ‖v₀‖ with hq_def
  have hpq : p * q < 0 := by
    have h : p * q = (p₀ * q₀) * (‖v₀‖ * ‖v₀‖) := by
      rw [hp_def, hq_def]
      ring
    rw [h]
    exact mul_neg_of_neg_of_pos hp₀q₀ (mul_pos hn hn)
  have hPv : P = p • v +ᵥ Y := by
    rw [hP, hp_def, hv_def, ← mul_smul, mul_assoc, mul_inv_cancel₀ hn.ne', mul_one]
  have hQv : Q = q • v +ᵥ Y := by
    rw [hQ, hq_def, hv_def, ← mul_smul, mul_assoc, mul_inv_cancel₀ hn.ne', mul_one]
  set γ := ⟪v, X -ᵥ Y⟫ with hγ
  -- Squared distances along the line, as functions of the parameter.
  have key : ∀ s t : ℝ, ‖s • v - t • (X -ᵥ Y)‖ ^ 2
      = s ^ 2 - 2 * s * t * γ + t ^ 2 * ‖X -ᵥ Y‖ ^ 2 := by
    intro s t
    rw [norm_sq_vsub_smul v (X -ᵥ Y) hv s t, ← hγ]
  have sqQ : ∀ s : ℝ, ‖s • v - (X -ᵥ Y)‖ ^ 2 = s ^ 2 - 2 * s * γ + ‖X -ᵥ Y‖ ^ 2 := by
    intro s
    have h := key s 1
    rwa [one_smul, mul_one, one_pow, one_mul] at h
  have hhalf : (⅟2 : ℝ) = 1 / 2 := by rw [invOf_eq_inv, inv_eq_one_div]
  have sqM : ∀ s : ℝ, ‖s • v - (1/2 : ℝ) • (X -ᵥ Y)‖ ^ 2
      = s ^ 2 - s * γ + ‖X -ᵥ Y‖ ^ 2 / 4 := by
    intro s
    rw [key s (1 / 2)]
    ring
  -- Distances expressed with the parametrization.
  have hc : dist X Y = ‖X -ᵥ Y‖ := dist_eq_norm_vsub _ X Y
  have hdistX : ∀ r : ℝ, dist X (r • v +ᵥ Y) = ‖r • v - (X -ᵥ Y)‖ := by
    intro r
    rw [dist_eq_norm_vsub', vadd_vsub_assoc, ← neg_vsub_eq_vsub_rev, ← sub_eq_add_neg]
  have hdistM : ∀ r : ℝ, dist (midpoint ℝ X Y) (r • v +ᵥ Y)
      = ‖r • v - (1/2 : ℝ) • (X -ᵥ Y)‖ := by
    intro r
    rw [dist_eq_norm_vsub', vadd_vsub_assoc, right_vsub_midpoint, ← neg_vsub_eq_vsub_rev,
      smul_neg, hhalf, ← sub_eq_add_neg]
  have hPQ : dist P Q = |p - q| := by
    rw [dist_eq_norm_vsub, hPv, hQv, vadd_vsub_vadd_cancel_right, ← sub_smul, norm_smul,
      hv, Real.norm_eq_abs, mul_one]
  -- The constraint |XQ| = 2|MP| determines q from p.
  have hq_eq : q = 2 * γ - 2 * p := by
    have hb := hXQ
    rw [hQv, hPv, hdistX q, hdistM p] at hb
    have h1 : ‖q • v - (X -ᵥ Y)‖ ^ 2 = (2 * ‖p • v - (1/2 : ℝ) • (X -ᵥ Y)‖) ^ 2 := by
      rw [hb]
    rw [mul_pow, sqQ q, sqM p] at h1
    have h2 : (q - 2 * p) * (q - (2 * γ - 2 * p)) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h2 with h | h
    · exfalso
      have hqp : q = 2 * p := by linarith
      rw [hqp] at hpq
      nlinarith [sq_nonneg p]
    · linarith
  -- The bounds on |MP|, as bounds on p * (p - γ).
  have hpg1 : 0 < p * (p - γ) := by
    rw [hPv, hdistM p, hc] at hlo
    have h1 : (‖X -ᵥ Y‖ / 2) ^ 2 < ‖p • v - (1/2 : ℝ) • (X -ᵥ Y)‖ ^ 2 :=
      (sq_lt_sq₀ (by positivity) (norm_nonneg _)).mpr hlo
    rw [sqM p] at h1
    nlinarith [h1]
  have hpg2 : p * (p - γ) < 2 * ‖X -ᵥ Y‖ ^ 2 := by
    rw [hPv, hdistM p, hc] at hhi
    have h1 : ‖p • v - (1/2 : ℝ) • (X -ᵥ Y)‖ ^ 2 < (3 * ‖X -ᵥ Y‖ / 2) ^ 2 :=
      (sq_lt_sq₀ (norm_nonneg _) (by positivity)).mpr hhi
    rw [sqM p] at h1
    nlinarith [h1]
  have hPQpq : dist P Q = |3 * p - 2 * γ| := by
    have h : p - q = 3 * p - 2 * γ := by
      rw [hq_eq]
      ring
    rw [hPQ, h]
  -- Apply the scalar case analysis and rebuild a configuration.
  have hpq' : p * (2 * γ - 2 * p) < 0 := by
    rw [← hq_eq]
    exact hpq
  obtain ⟨p', hs1, hs2, hs3, hs4⟩ := exists_better_param p γ hpq'
  obtain ⟨C', hC'⟩ := build_configuration X Y v hv p' hs1 hs2 (by linarith [hpg2])
  exact ⟨C', by rw [hC', hPQpq, ← hγ]; exact hs4⟩

end Usa1987P4
