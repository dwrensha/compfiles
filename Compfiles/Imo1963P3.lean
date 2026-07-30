/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Geometry]
}

/-!
# International Mathematical Olympiad 1963, Problem 3

An n-gon has all angles equal and the lengths of consecutive sides satisfy
a₁ ≥ a₂ ≥ ... ≥ aₙ. Prove that all the sides are equal.
-/

namespace Imo1963P3

open Finset

/-- The rotation factor between the directions of two consecutive sides of an
equiangular `n`-gon: traversing the (convex) polygon, each side vector is
obtained from the previous one by rotating through the exterior angle
`2 * π / n` (and rescaling to the new length). -/
noncomputable def rot (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

snip begin

lemma rot_pow {n : ℕ} (hn : 0 < n) : rot n ^ n = 1 := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have e1 : (n : ℂ) * (2 * Real.pi * Complex.I / n) = 2 * Real.pi * Complex.I := by
    rw [mul_comm (n : ℂ) (2 * Real.pi * Complex.I / n), div_mul_cancel₀ _ hn']
  unfold rot
  rw [← Complex.exp_nat_mul, e1, Complex.exp_two_pi_mul_I]

lemma re_rot_pow (n j : ℕ) : (rot n ^ j).re = Real.cos (2 * Real.pi * j / n) := by
  have e1 : (j : ℂ) * (2 * Real.pi * Complex.I / n) =
      ((2 * Real.pi * j / n : ℝ) : ℂ) * Complex.I := by
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    · have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
      push_cast
      field_simp [hn']
  unfold rot
  rw [← Complex.exp_nat_mul, e1, Complex.exp_ofReal_mul_I_re]

lemma cos_lt_one {n j : ℕ} (hn : 3 ≤ n) (hj1 : 1 ≤ j) (hjn : j ≤ n - 1) :
    Real.cos (2 * Real.pi * j / n) < 1 := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj1
  have hpos : (0 : ℝ) < 2 * Real.pi * j / n := by positivity
  have hlt : 2 * Real.pi * j / n < 2 * Real.pi := by
    rw [div_lt_iff₀ hnr]
    exact mul_lt_mul_of_pos_left (by exact_mod_cast (show j < n by omega)) (by positivity)
  have hne : Real.cos (2 * Real.pi * j / n) ≠ 1 :=
    fun hc ↦ hpos.ne'
      ((Real.cos_eq_one_iff_of_lt_of_lt (by linarith [Real.pi_pos]) hlt).mp hc)
  exact lt_of_le_of_ne (Real.cos_le_one _) hne

/-- The algebraic heart of the problem: if real numbers `a₀ ≥ a₁ ≥ ... ≥ aₙ₋₁`
satisfy the polygon closure equation `Σ aₖ ζᵏ = 0` for `ζ = e^{2πi/n}`, then they
are all equal.  Write `n = N + 1` and multiply the equation by `ζ - 1`: the sum of
the rotated differences `(aᵢ - aᵢ₊₁) ζⁱ⁺¹` equals the telescoping sum `a₀ - a_N`.
Comparing real parts gives `Σ (aᵢ - aᵢ₊₁) (1 - cos (2π(i+1)/n)) = 0`, a sum of
nonnegative terms, so every difference `aᵢ - aᵢ₊₁` vanishes. -/
lemma sides_eq_of_sum_eq_zero {n : ℕ} (hn : 3 ≤ n) (a : ℕ → ℝ)
    (ha : ∀ i j : ℕ, i ≤ j → j < n → a j ≤ a i)
    (hH : ∑ k ∈ range n, (a k : ℂ) * rot n ^ k = 0) :
    ∀ i : ℕ, i < n → a i = a 0 := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, n = N + 1 := ⟨n - 1, by omega⟩
  subst hN
  have hζn : rot (N + 1) ^ (N + 1) = 1 := rot_pow (by omega)
  -- Split the closure equation at the top and at the bottom of the range.
  have htop : ∑ k ∈ range N, (a k : ℂ) * rot (N + 1) ^ k =
      - ((a N : ℂ) * rot (N + 1) ^ N) := by
    have h := hH
    rw [Finset.sum_range_succ] at h
    exact eq_neg_of_add_eq_zero_left h
  have hbot : ∑ k ∈ range N, (a (k + 1) : ℂ) * rot (N + 1) ^ (k + 1) = - (a 0 : ℂ) := by
    have h := hH
    rw [Finset.sum_range_succ'] at h
    simp only [pow_zero, mul_one] at h
    exact eq_neg_of_add_eq_zero_left h
  -- The sum of the rotated differences `(aᵢ - aᵢ₊₁) ζⁱ⁺¹` is real.
  have hB : ∑ i ∈ range N, ((a i - a (i + 1) : ℝ) : ℂ) * rot (N + 1) ^ (i + 1) =
      ((a 0 - a N : ℝ) : ℂ) := by
    have per : ∀ i : ℕ, ((a i - a (i + 1) : ℝ) : ℂ) * rot (N + 1) ^ (i + 1) =
        (a i : ℂ) * rot (N + 1) ^ (i + 1) - (a (i + 1) : ℂ) * rot (N + 1) ^ (i + 1) :=
      fun i ↦ by push_cast; ring
    rw [Finset.sum_congr rfl (fun i _ ↦ per i), Finset.sum_sub_distrib]
    have first : ∑ i ∈ range N, (a i : ℂ) * rot (N + 1) ^ (i + 1) = - (a N : ℂ) := by
      have per2 : ∀ i : ℕ, (a i : ℂ) * rot (N + 1) ^ (i + 1) =
          rot (N + 1) * ((a i : ℂ) * rot (N + 1) ^ i) := fun i ↦ by rw [pow_succ]; ring
      rw [Finset.sum_congr rfl (fun i _ ↦ per2 i), ← Finset.mul_sum, htop, mul_neg]
      have e : rot (N + 1) * ((a N : ℂ) * rot (N + 1) ^ N) = (a N : ℂ) := by
        have e2 : rot (N + 1) * ((a N : ℂ) * rot (N + 1) ^ N) =
            (a N : ℂ) * rot (N + 1) ^ (N + 1) := by rw [pow_succ]; ring
        rw [e2, hζn, mul_one]
      rw [e]
    rw [first, hbot]
    push_cast
    ring
  -- Taking real parts kills the rotation.
  have hC : ∑ i ∈ range N,
      (a i - a (i + 1)) * Real.cos (2 * Real.pi * ((i + 1 : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ)) =
      a 0 - a N := by
    have per : ∀ i : ℕ, (((a i - a (i + 1) : ℝ) : ℂ) * rot (N + 1) ^ (i + 1)).re =
        (a i - a (i + 1)) *
          Real.cos (2 * Real.pi * ((i + 1 : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ)) := by
      intro i
      rw [show (((a i - a (i + 1) : ℝ) : ℂ) * rot (N + 1) ^ (i + 1)).re =
          (a i - a (i + 1)) * (rot (N + 1) ^ (i + 1)).re from by
        simp [Complex.mul_re]]
      rw [re_rot_pow]
    have h := congrArg Complex.re hB
    simp only [Complex.re_sum, per, Complex.ofReal_re] at h
    exact h
  -- The unrotated differences telescope.
  have hA : ∑ i ∈ range N, (a i - a (i + 1)) = a 0 - a N := Finset.sum_range_sub' a N
  -- Subtracting, a sum of nonnegative terms vanishes, so each term vanishes.
  have hD : ∑ i ∈ range N,
      (a i - a (i + 1)) *
        (1 - Real.cos (2 * Real.pi * ((i + 1 : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ))) = 0 := by
    have per : ∀ i : ℕ,
        (a i - a (i + 1)) *
            (1 - Real.cos (2 * Real.pi * ((i + 1 : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ))) =
        (a i - a (i + 1)) -
          (a i - a (i + 1)) *
            Real.cos (2 * Real.pi * ((i + 1 : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ)) :=
      fun i ↦ by ring
    rw [Finset.sum_congr rfl (fun i _ ↦ per i), Finset.sum_sub_distrib, hA, hC, sub_self]
  have hnonneg : ∀ i ∈ range N,
      (0 : ℝ) ≤ (a i - a (i + 1)) *
        (1 - Real.cos (2 * Real.pi * ((i + 1 : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ))) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have h1 : (0 : ℝ) ≤ a i - a (i + 1) :=
      sub_nonneg.mpr (ha i (i + 1) (Nat.le_succ i) (by omega))
    have h2 : (0 : ℝ) ≤
        1 - Real.cos (2 * Real.pi * ((i + 1 : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ)) :=
      sub_nonneg.mpr (cos_lt_one (n := N + 1) (j := i + 1) (by omega) (by omega) (by omega)).le
    exact mul_nonneg h1 h2
  have hterm : ∀ i ∈ range N,
      (a i - a (i + 1)) *
        (1 - Real.cos (2 * Real.pi * ((i + 1 : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ))) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hD
  have hdz : ∀ i ∈ range N, a i - a (i + 1) = 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hcos : Real.cos (2 * Real.pi * ((i + 1 : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ)) ≠ 1 :=
      (cos_lt_one (n := N + 1) (j := i + 1) (by omega) (by omega) (by omega)).ne
    rcases mul_eq_zero.mp (hterm i (Finset.mem_range.mpr hi)) with h | h
    · exact h
    · exfalso
      exact hcos (by linarith)
  -- Hence `a` is constant.
  intro i
  induction i with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have h1 : a (k + 1) = a k := by
      have hz := hdz k (Finset.mem_range.mpr (by omega : k < N))
      linarith
    rw [h1]
    exact ih (by omega)

snip end

problem imo1963_p3 {n : ℕ} (hn : 3 ≤ n) (a : ℕ → ℝ)
    -- the lengths of the consecutive sides satisfy `a₁ ≥ a₂ ≥ ... ≥ aₙ`
    (ha : ∀ i j : ℕ, i ≤ j → j < n → a j ≤ a i)
    (hpos : ∀ i : ℕ, i < n → 0 < a i)
    -- `w i` is the `i`-th side vector of the polygon (a list of edge vectors
    -- of a polygon closes up, has the side lengths as norms, and, the polygon
    -- being equiangular, each edge is obtained from the previous one by
    -- rotating through the exterior angle `2 * π / n`)
    (w : ℕ → ℂ)
    (hclose : ∑ i ∈ Finset.range n, w i = 0)
    (hlen : ∀ i : ℕ, i < n → ‖w i‖ = a i)
    (hturn : ∀ i : ℕ, i + 1 < n →
      w (i + 1) = ((a (i + 1) / a i : ℝ) : ℂ) * rot n * w i) :
    ∃ c : ℝ, ∀ i : ℕ, i < n → a i = c := by
  have hn0 : 0 < n := by omega
  have ha0r : a 0 ≠ 0 := (hpos 0 hn0).ne'
  have ha0c : (a 0 : ℂ) ≠ 0 := by exact_mod_cast ha0r
  have hw0 : w 0 ≠ 0 := norm_pos_iff.mp (by rw [hlen 0 hn0]; exact hpos 0 hn0)
  -- Each side vector is `w 0`, rotated and rescaled: `w k = (a k / a 0) ζᵏ w 0`.
  have hw : ∀ k : ℕ, k < n → w k = ((a k / a 0 : ℝ) : ℂ) * rot n ^ k * w 0 := by
    intro k
    induction k with
    | zero =>
      intro hk0
      have h0 : a 0 ≠ 0 := (hpos 0 hk0).ne'
      simp [h0]
    | succ k ih =>
      intro hk
      have hk' : k < n := Nat.lt_of_succ_lt hk
      have hak : (a k : ℂ) ≠ 0 := by exact_mod_cast (hpos k hk').ne'
      rw [hturn k hk, ih hk']
      push_cast
      field_simp [hak, ha0c]
      ring
  -- The closure equation then gives `Σ aₖ ζᵏ = 0`.
  have hsum : ∑ k ∈ Finset.range n, (a k : ℂ) * rot n ^ k = 0 := by
    have e1 : (∑ k ∈ Finset.range n, ((a k : ℂ) / (a 0 : ℂ)) * rot n ^ k) * w 0 =
        ∑ k ∈ Finset.range n, w k := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      rw [hw k hk]
      push_cast
      ring
    rw [hclose] at e1
    rcases mul_eq_zero.mp e1 with h | h
    swap
    · exact absurd h hw0
    · have e3 : ∀ k : ℕ, ((a k : ℂ) / (a 0 : ℂ)) * rot n ^ k =
          (a 0 : ℂ)⁻¹ * ((a k : ℂ) * rot n ^ k) := fun k ↦ by ring
      rw [Finset.sum_congr rfl (fun k _ ↦ e3 k), ← Finset.mul_sum] at h
      rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' (inv_ne_zero ha0c)
      · exact h'
  exact ⟨a 0, sides_eq_of_sum_eq_zero hn a ha hsum⟩

end Imo1963P3
