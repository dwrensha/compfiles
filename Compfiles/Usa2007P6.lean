/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.LinearCombination.Lemmas
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry, .Inequality] }

/-!
# USA Mathematical Olympiad 2007 P6

Let $ABC$ be an acute triangle with $\omega$, $S$, and $R$ being its incircle,
circumcircle, and circumradius, respectively. Circle $\omega_A$ is tangent
internally to $S$ at $A$ and tangent externally to $\omega$. Circle $S_A$ is
tangent internally to $S$ at $A$ and tangent internally to $\omega$. Let $P_A$
and $Q_A$ denote the centers of $\omega_A$ and $S_A$, respectively. Define
points $P_B$, $Q_B$, $P_C$, $Q_C$ analogously. Prove that
$$ 8 P_AQ_A \cdot P_BQ_B \cdot P_CQ_C \le R^3 $$
with equality if and only if triangle $ABC$ is equilateral.

## Formalization notes

We encode the triangle by its side lengths `a b c : ℝ`, assumed positive and
satisfying the strict triangle inequalities; acuteness is encoded by
`c ^ 2 < a ^ 2 + b ^ 2` and its cyclic permutations (these hypotheses are part
of the problem data; the algebraic core of the proof does not use them). With
`s = (a + b + c) / 2` the semiperimeter, `K = √(s (s - a) (s - b) (s - c))` the
area (Heron's formula) and `R = a b c / (4 K)` the circumradius, the two tangent
circles at `A` are explicit: writing `ρ_A`, `σ_A` for the radii of `ω_A`, `S_A`
one has

    ρ_A = R (s - a)² / (bc)   and   σ_A = R s (s - a) / (bc)

(this is the inversion computation in Evan Chen's *USAMO 2007 Solution Notes*),
and both centers lie on the segment `OA`, so

    P_AQ_A = σ_A - ρ_A = R a (s - a) / (bc) = a² (s - a) / (4 K),

and cyclically for `P_BQ_B` and `P_CQ_C`. Hence, after clearing the common
denominator `(4K)³` and cancelling `(abc)²`, the claim becomes the classical
inequality `8 (s - a) (s - b) (s - c) ≤ abc` (itself equivalent to Euler's
`R ≥ 2r`), which under the substitution `x = s - a`, `y = s - b`, `z = s - c`
is AM–GM: `8xyz ≤ (x + y)(y + z)(z + x)`, with equality iff `x = y = z`,
i.e. iff `a = b = c`.
-/

namespace Usa2007P6

snip begin

/-- AM–GM in the form `8xyz ≤ (x + y)(y + z)(z + x)` for positive reals, with
equality iff `x = y = z`. Both claims follow from the sum-of-squares identity
`(x + y)(y + z)(z + x) - 8xyz = x(y - z)² + y(z - x)² + z(x - y)²`. -/
theorem eight_mul_le_prod (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    8 * x * y * z ≤ (x + y) * (y + z) * (z + x) ∧
      ((x + y) * (y + z) * (z + x) = 8 * x * y * z ↔ x = y ∧ y = z) := by
  have hSOS : (x + y) * (y + z) * (z + x) - 8 * x * y * z =
      x * (y - z) ^ 2 + y * (z - x) ^ 2 + z * (x - y) ^ 2 := by ring
  have t1 : 0 ≤ x * (y - z) ^ 2 := by positivity
  have t2 : 0 ≤ y * (z - x) ^ 2 := by positivity
  have t3 : 0 ≤ z * (x - y) ^ 2 := by positivity
  refine ⟨by linarith, fun h => ?_, fun h => ?_⟩
  · have e1 : x * (y - z) ^ 2 = 0 := by linarith
    have e2 : y * (z - x) ^ 2 = 0 := by linarith
    have hyz : y = z := by
      rcases mul_eq_zero.mp e1 with h1 | h1
      · exact absurd h1 (ne_of_gt hx)
      · have h2 := sq_eq_zero_iff.mp h1
        linarith
    have hzx : z = x := by
      rcases mul_eq_zero.mp e2 with h1 | h1
      · exact absurd h1 (ne_of_gt hy)
      · have h2 := sq_eq_zero_iff.mp h1
        linarith
    exact ⟨by linarith, hyz⟩
  · obtain ⟨h1, h2⟩ := h
    subst h1
    subst h2
    ring

snip end

problem usa2007_p6 (a b c s K R : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hbc : a < b + c) (hca : b < c + a) (hab : c < a + b)
    (hac1 : c ^ 2 < a ^ 2 + b ^ 2) (hac2 : a ^ 2 < b ^ 2 + c ^ 2)
    (hac3 : b ^ 2 < c ^ 2 + a ^ 2)
    (hs : s = (a + b + c) / 2)
    (hK : K = Real.sqrt (s * (s - a) * (s - b) * (s - c)))
    (hR : R = a * b * c / (4 * K)) :
    8 * (a ^ 2 * (s - a) / (4 * K)) * (b ^ 2 * (s - b) / (4 * K)) *
        (c ^ 2 * (s - c) / (4 * K)) ≤ R ^ 3 ∧
      (8 * (a ^ 2 * (s - a) / (4 * K)) * (b ^ 2 * (s - b) / (4 * K)) *
          (c ^ 2 * (s - c) / (4 * K)) = R ^ 3 ↔ a = b ∧ b = c) := by
  rw [hR]
  have hs0 : (0 : ℝ) < s := by rw [hs]; positivity
  have hx : (0 : ℝ) < s - a := by rw [hs]; linarith
  have hy : (0 : ℝ) < s - b := by rw [hs]; linarith
  have hz : (0 : ℝ) < s - c := by rw [hs]; linarith
  have hK0 : (0 : ℝ) < K := by
    rw [hK]
    exact Real.sqrt_pos.mpr (by positivity)
  have h4K : (4 : ℝ) * K ≠ 0 := by positivity
  have hD : (0 : ℝ) < (4 * K) ^ 3 := by positivity
  have hsum1 : s - a + (s - b) = c := by rw [hs]; ring
  have hsum2 : s - b + (s - c) = a := by rw [hs]; ring
  have hsum3 : s - c + (s - a) = b := by rw [hs]; ring
  obtain ⟨hcore, hcoreeq⟩ := eight_mul_le_prod (s - a) (s - b) (s - c) hx hy hz
  rw [hsum1, hsum2, hsum3] at hcore hcoreeq
  have hnorm : 8 * (a ^ 2 * (s - a) / (4 * K)) * (b ^ 2 * (s - b) / (4 * K)) *
        (c ^ 2 * (s - c) / (4 * K))
      = 8 * (a * b * c) ^ 2 * ((s - a) * (s - b) * (s - c)) / (4 * K) ^ 3 := by
    field_simp
  have hR3 : (a * b * c / (4 * K)) ^ 3 = (a * b * c) ^ 3 / (4 * K) ^ 3 := by
    rw [div_pow]
  refine ⟨?_, ?_⟩
  · rw [hnorm, hR3, div_le_div_iff_of_pos_right hD]
    have h2 : (a * b * c) ^ 2 * (8 * ((s - a) * (s - b) * (s - c))) ≤
        (a * b * c) ^ 2 * (a * b * c) :=
      mul_le_mul_of_nonneg_left (by linarith [hcore]) (sq_nonneg _)
    linarith [h2]
  · constructor
    · intro heq
      rw [hnorm, hR3] at heq
      have hnum : 8 * (a * b * c) ^ 2 * ((s - a) * (s - b) * (s - c)) =
          (a * b * c) ^ 3 :=
        mul_right_cancel₀ (ne_of_gt hD)
          ((div_eq_div_iff (ne_of_gt hD) (ne_of_gt hD)).mp heq)
      have h3 : 8 * ((s - a) * (s - b) * (s - c)) = a * b * c := by
        apply mul_left_cancel₀ (ne_of_gt (by positivity : (0 : ℝ) < (a * b * c) ^ 2))
        linear_combination hnum
      have h4 : c * a * b = 8 * (s - a) * (s - b) * (s - c) := by
        linear_combination -h3
      obtain ⟨hxy, hyz⟩ := hcoreeq.mp h4
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      have hxy : s - a = s - b := by linarith
      have hyz : s - b = s - c := by linarith
      have h4 : c * a * b = 8 * (s - a) * (s - b) * (s - c) := hcoreeq.mpr ⟨hxy, hyz⟩
      rw [hnorm, hR3]
      congr 1
      linear_combination -(a * b * c) ^ 2 * h4
