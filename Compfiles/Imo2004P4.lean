/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra, .Inequality] }

/-!
# International Mathematical Olympiad 2004, Problem 4

Let n ≥ 3 be an integer. Let t₁, t₂, ..., tₙ be positive real numbers
such that

  n² + 1 > (t₁ + t₂ + ⋯ + tₙ) (1/t₁ + 1/t₂ + ⋯ + 1/tₙ).

Show that tᵢ, tⱼ, tₖ are the side lengths of a triangle for all i, j, k
with 1 ≤ i < j < k ≤ n.
-/

namespace Imo2004P4

snip begin

lemma dist2 (x1 y1 x2 y2 : ℝ) :
    dist (!₂[x1, y1] : EuclideanSpace ℝ (Fin 2)) !₂[x2, y2]
      = Real.sqrt ((x1 - x2)^2 + (y1 - y2)^2) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.dist_eq, sq_abs]

/-- If `a`, `b`, `c` satisfy the strict triangle inequalities, then there is an
(automatically nondegenerate) triangle in the plane with those side lengths. -/
lemma exists_triangle {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : c < a + b) (hbc : a < b + c) (hca : b < c + a) :
    ∃ T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)),
      dist (T.points 0) (T.points 1) = a ∧
      dist (T.points 1) (T.points 2) = b ∧
      dist (T.points 2) (T.points 0) = c := by
  set px := (a^2 + c^2 - b^2) / (2 * a) with hpx
  have hpx2 : 2 * a * px = a^2 + c^2 - b^2 := by
    rw [hpx]; field_simp
  have hpos : 0 < c^2 - px^2 := by
    have h4a2 : (0:ℝ) < 4 * a^2 := by positivity
    rw [← mul_pos_iff_of_pos_left h4a2,
      show 4 * a^2 * (c^2 - px^2) = 4 * a^2 * c^2 - (2 * a * px)^2 by ring, hpx2,
      show 4 * a^2 * c^2 - (a^2 + c^2 - b^2)^2
        = (b - a + c) * (b + a - c) * (a + c - b) * (a + c + b) by ring]
    have f1 : 0 < b - a + c := by linarith
    have f2 : 0 < b + a - c := by linarith
    have f3 : 0 < a + c - b := by linarith
    have f4 : 0 < a + c + b := by linarith
    positivity
  set py := Real.sqrt (c^2 - px^2)
  have hpy2 : py^2 = c^2 - px^2 := Real.sq_sqrt hpos.le
  set p0 : EuclideanSpace ℝ (Fin 2) := !₂[0, 0] with hp0
  set p1 : EuclideanSpace ℝ (Fin 2) := !₂[a, 0] with hp1
  set p2 : EuclideanSpace ℝ (Fin 2) := !₂[px, py] with hp2
  have hd01 : dist p0 p1 = a := by
    rw [hp0, hp1, dist2, show (0 - a)^2 + ((0:ℝ) - 0)^2 = a^2 by ring, Real.sqrt_sq ha.le]
  have hd12 : dist p1 p2 = b := by
    rw [hp1, hp2, dist2,
      show (a - px)^2 + ((0:ℝ) - py)^2 = a^2 - 2 * a * px + (px^2 + py^2) by ring,
      hpy2, hpx2,
      show a^2 - (a^2 + c^2 - b^2) + (px^2 + (c^2 - px^2)) = b^2 by ring, Real.sqrt_sq hb.le]
  have hd20 : dist p2 p0 = c := by
    rw [hp2, hp0, dist2, show (px - 0)^2 + (py - (0:ℝ))^2 = px^2 + py^2 by ring,
      hpy2, show px^2 + (c^2 - px^2) = c^2 by ring, Real.sqrt_sq hc.le]
  have hindep : AffineIndependent ℝ ![p0, p1, p2] := by
    rw [affineIndependent_iff_not_collinear_set]
    intro hcol
    rcases hcol.wbtw_or_wbtw_or_wbtw with h | h | h
    · have hd := Wbtw.dist_add_dist h
      rw [hd01, hd12, dist_comm p0 p2, hd20] at hd
      linarith
    · have hd := Wbtw.dist_add_dist h
      rw [hd12, hd20, dist_comm p1 p0, hd01] at hd
      linarith
    · have hd := Wbtw.dist_add_dist h
      rw [hd20, hd01, dist_comm p2 p1, hd12] at hd
      linarith
  refine ⟨⟨![p0, p1, p2], hindep⟩, ?_, ?_, ?_⟩
  · simpa using hd01
  · simpa using hd12
  · simpa using hd20

/-- Cauchy–Schwarz / AM–HM: for positive reals indexed by a finset `s`,
`(card s)² ≤ (∑ tᵢ)(∑ 1/tᵢ)`. -/
lemma card_sq_le {n : ℕ} (s : Finset (Fin n)) (t : Fin n → ℝ) (ht : ∀ i ∈ s, 0 < t i) :
    (s.card : ℝ)^2 ≤ (∑ i ∈ s, t i) * (∑ i ∈ s, 1 / t i) := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s (r := fun _ => (1:ℝ))
    (f := t) (g := fun i => 1 / t i)
    (fun i hi => (ht i hi).le) (fun i hi => by have := ht i hi; positivity)
    (fun i hi => by rw [one_pow, mul_one_div, div_self (ht i hi).ne'])
  simpa using h

/-- The heart of the problem: any three of the values satisfy the triangle inequality. -/
lemma key {n : ℕ} (hn : 3 ≤ n) (t : Fin n → ℝ) (ht : ∀ i, 0 < t i)
    (hsum : (∑ i, t i) * (∑ i, 1 / t i) < n ^ 2 + 1)
    (p q r : Fin n) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    t p < t q + t r := by
  by_contra hcon
  rw [not_lt] at hcon
  set s : Finset (Fin n) := {p, q, r} with hs
  have hscard : s.card = 3 := Finset.card_eq_three.mpr ⟨p, q, r, hpq, hpr, hqr, rfl⟩
  -- Split the universal sums over `s` and its complement.
  have hsplitT : (∑ i, t i) = (∑ i ∈ s, t i) + ∑ i ∈ sᶜ, t i :=
    (Finset.sum_add_sum_compl s t).symm
  have hsplitR : (∑ i, 1 / t i) = (∑ i ∈ s, 1 / t i) + ∑ i ∈ sᶜ, 1 / t i :=
    (Finset.sum_add_sum_compl s _).symm
  set X1 := ∑ i ∈ s, t i with hX1def
  set Y1 := ∑ i ∈ s, 1 / t i with hY1def
  set X2 := ∑ i ∈ sᶜ, t i
  set Y2 := ∑ i ∈ sᶜ, 1 / t i
  -- Evaluate the sums over `s = {p, q, r}`.
  have hX1 : X1 = t p + t q + t r := by
    rw [hX1def, hs, Finset.sum_insert (by simp [hpq, hpr]),
      Finset.sum_insert (by simp [hqr]), Finset.sum_singleton]
    ring
  have hY1 : Y1 = 1 / t p + 1 / t q + 1 / t r := by
    rw [hY1def, hs, Finset.sum_insert (by simp [hpq, hpr]),
      Finset.sum_insert (by simp [hqr]), Finset.sum_singleton]
    ring
  -- Nonnegativity facts.
  have hppos := ht p
  have hqpos := ht q
  have hrpos := ht r
  have hX1pos : 0 < X1 := by rw [hX1]; positivity
  have hY1pos : 0 < Y1 := by rw [hY1]; positivity
  have hX2nn : 0 ≤ X2 := Finset.sum_nonneg (fun i _ => (ht i).le)
  have hY2nn : 0 ≤ Y2 := Finset.sum_nonneg (fun i _ => by have := ht i; positivity)
  -- The three special terms contribute at least 10.
  have hX1Y1 : 10 ≤ X1 * Y1 := by
    rw [hX1, hY1]
    have hexp : (t p + t q + t r) * (1 / t p + 1 / t q + 1 / t r)
        = (t p + t q + t r) * (t p * t q + t q * t r + t r * t p) / (t p * t q * t r) := by
      field_simp; ring
    rw [hexp, le_div_iff₀ (by positivity)]
    -- An SOS certificate: the difference is a sum of three manifestly nonnegative terms.
    have hsos : (t p + t q + t r) * (t p * t q + t q * t r + t r * t p)
          - 10 * (t p * t q * t r)
        = 2 * (t q + t r) * (t q - t r) ^ 2 + (t q + t r) * (t p - t q - t r) ^ 2
          + 3 * (t p - t q - t r) * ((t q - t r) ^ 2 + t q * t r) := by ring
    have h1 : 0 ≤ 2 * (t q + t r) * (t q - t r) ^ 2 := by positivity
    have h2 : 0 ≤ (t q + t r) * (t p - t q - t r) ^ 2 := by positivity
    have h3 : 0 ≤ 3 * (t p - t q - t r) * ((t q - t r) ^ 2 + t q * t r) :=
      mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by positivity)
    linarith
  -- The remaining `n - 3` terms contribute at least `(n - 3)²`.
  set M : ℝ := (sᶜ.card : ℝ) with hMdef
  have hMval : M = (n : ℝ) - 3 := by
    rw [hMdef, Finset.card_compl, Fintype.card_fin, hscard, Nat.cast_sub hn]
    norm_num
  have hMnn : 0 ≤ M := by
    rw [hMval]
    have h3 : (3:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hX2Y2 : M ^ 2 ≤ X2 * Y2 := card_sq_le sᶜ t (fun i _ => ht i)
  -- Combine: the cross terms are at least `6M`.
  have hPnn : 0 ≤ X1 * Y2 + X2 * Y1 :=
    add_nonneg (mul_nonneg hX1pos.le hY2nn) (mul_nonneg hX2nn hY1pos.le)
  have h40 : 40 * M ^ 2 ≤ (X1 * Y2 + X2 * Y1) ^ 2 := by
    have hm : 10 * M ^ 2 ≤ X1 * Y1 * (X2 * Y2) :=
      mul_le_mul hX1Y1 hX2Y2 (sq_nonneg M) (by linarith)
    have hid : (X1 * Y2 + X2 * Y1) ^ 2
        = (X1 * Y2 - X2 * Y1) ^ 2 + 4 * (X1 * Y1 * (X2 * Y2)) := by ring
    rw [hid]
    linarith [sq_nonneg (X1 * Y2 - X2 * Y1)]
  have hP : 6 * M ≤ X1 * Y2 + X2 * Y1 := by
    have h36 : (6 * M) ^ 2 ≤ (X1 * Y2 + X2 * Y1) ^ 2 := by
      have e : (6 * M) ^ 2 = 36 * M ^ 2 := by ring
      rw [e]; linarith [sq_nonneg M]
    exact le_of_sq_le_sq h36 hPnn
  -- Assemble the final contradiction.
  have hfinal : (n : ℝ) ^ 2 + 1 ≤ (∑ i, t i) * (∑ i, 1 / t i) := by
    rw [hsplitT, hsplitR]
    have hexpand : (X1 + X2) * (Y1 + Y2) = X1 * Y1 + X2 * Y2 + (X1 * Y2 + X2 * Y1) := by ring
    rw [hexpand]
    have hn2 : (n : ℝ) ^ 2 + 1 = M ^ 2 + 6 * M + 10 := by rw [hMval]; ring
    rw [hn2]
    linarith
  linarith

snip end

problem imo2004_p4 (n : ℕ) (hn : 3 ≤ n) (t : Fin n → ℝ)
    (ht : ∀ i, 0 < t i)
    (hsum : (∑ i, t i) * (∑ i, 1 / t i) < n ^ 2 + 1)
    (i j k : Fin n) (hij : i < j) (hjk : j < k) :
    ∃ T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)),
      dist (T.points 0) (T.points 1) = t i ∧
      dist (T.points 1) (T.points 2) = t j ∧
      dist (T.points 2) (T.points 0) = t k := by
  have hik : i < k := lt_trans hij hjk
  have h1 : t k < t i + t j := key hn t ht hsum k i j hik.ne' hjk.ne' hij.ne
  have h2 : t i < t j + t k := key hn t ht hsum i j k hij.ne hik.ne hjk.ne
  have h3 : t j < t k + t i := key hn t ht hsum j k i hjk.ne hij.ne' hik.ne'
  exact exists_triangle (ht i) (ht j) (ht k) h1 h2 h3


end Imo2004P4
