/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Int.Star
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1984, Problem 5

Let $d$ be the sum of the lengths of all the diagonals of a plane convex
polygon with $n > 3$ vertices. Let $p$ be its perimeter. Prove that

$$n - 3 < \frac{2d}{p} < \left\lfloor \frac{n}{2} \right\rfloor
  \left\lfloor \frac{n+1}{2} \right\rfloor - 2.$$

**Formalization.**  The polygon is given by its vertices
`v : ZMod n → EuclideanSpace ℝ (Fin 2)`, listed in counterclockwise order.
Strict convexity is expressed by `ConvexCCW v`: every counterclockwise-ordered
triple of distinct vertices makes a strict left turn (positive cross product).
The diagonal sum `d` is written as one half of the sum of `dist (v i) (v j)`
over all *ordered* pairs `(i, j)` of nonadjacent vertices (each diagonal is
counted twice), and `p` is the sum of the side lengths.
-/

namespace Imo1984P5

/-- The Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- The 2-dimensional cross product (scalar valued). -/
def cross (u w : Pt) : ℝ := u 0 * w 1 - u 1 * w 0

/-- Strict convexity, counterclockwise: every triple of vertices in
counterclockwise order makes a strict left turn. -/
abbrev ConvexCCW {n : ℕ} (v : ZMod n → Pt) : Prop :=
  ∀ i : ZMod n, ∀ a b : ℕ, 1 ≤ a → a < b → b ≤ n - 1 →
    0 < cross (v (i + (a : ZMod n)) - v i) (v (i + (b : ZMod n)) - v i)

/-- Length of the side from vertex `i` to vertex `i + 1`. -/
noncomputable abbrev side {n : ℕ} (v : ZMod n → Pt) (i : ZMod n) : ℝ := dist (v i) (v (i + 1))

/-- Distance between vertex `i` and vertex `i + r`. -/
noncomputable abbrev F {n : ℕ} (v : ZMod n → Pt) (i : ZMod n) (r : ℕ) : ℝ :=
  dist (v i) (v (i + (r : ZMod n)))

/-- Length of the polygonal path from vertex `i` to vertex `i + r`
along the sides of the polygon. -/
noncomputable abbrev arc {n : ℕ} (v : ZMod n → Pt) (i : ZMod n) (r : ℕ) : ℝ :=
  ∑ s ∈ Finset.range r, side v (i + (s : ZMod n))

/-- The perimeter of the polygon. -/
noncomputable abbrev perimeter {n : ℕ} [NeZero n] (v : ZMod n → Pt) : ℝ :=
  ∑ i : ZMod n, side v i

/-- Twice the sum of the lengths of the diagonals: the sum over all ordered
pairs `(i, i + r)` with `2 ≤ r ≤ n - 2` counts every diagonal twice. -/
noncomputable abbrev diagTwoSum {n : ℕ} [NeZero n] (v : ZMod n → Pt) : ℝ :=
  ∑ i : ZMod n, ∑ r ∈ Finset.Ico 2 (n - 1), F v i r

/-- The sum of the lengths of the diagonals of the polygon. -/
noncomputable abbrev diagonalsSum {n : ℕ} [NeZero n] (v : ZMod n → Pt) : ℝ :=
  diagTwoSum v / 2

snip begin

/-!
## Basic properties of the cross product
-/

lemma cross_self (u : Pt) : cross u u = 0 := by simp only [cross]; ring

lemma cross_comm (u w : Pt) : cross u w = - cross w u := by simp only [cross]; ring

lemma cross_zero_left (w : Pt) : cross 0 w = 0 := by simp [cross]

lemma cross_add_left (u v w : Pt) : cross (u + v) w = cross u w + cross v w := by
  simp only [cross, PiLp.add_apply]; ring

lemma cross_add_right (u v w : Pt) : cross u (v + w) = cross u v + cross u w := by
  simp only [cross, PiLp.add_apply]; ring

lemma cross_sub_left (u v w : Pt) : cross (u - v) w = cross u w - cross v w := by
  simp only [cross, PiLp.sub_apply]; ring

lemma cross_sub_right (u v w : Pt) : cross u (v - w) = cross u v - cross u w := by
  simp only [cross, PiLp.sub_apply]; ring

lemma cross_smul_left (c : ℝ) (u w : Pt) : cross (c • u) w = c * cross u w := by
  simp only [cross, PiLp.smul_apply, smul_eq_mul]; ring

lemma cross_smul_right (c : ℝ) (u w : Pt) : cross u (c • w) = c * cross u w := by
  simp only [cross, PiLp.smul_apply, smul_eq_mul]; ring

/-!
## Strict triangle inequality from a nonzero cross product
-/

lemma norm_sq (u : Pt) : ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
  simp [sq_abs]

/-- If the cross product of `a` and `b` is nonzero, then `a`, `b` satisfy the
strict triangle inequality. -/
lemma strict_norm_add {a b : Pt} (h : cross a b ≠ 0) : ‖a + b‖ < ‖a‖ + ‖b‖ := by
  have hcross2 : 0 < cross a b ^ 2 := sq_pos_of_ne_zero h
  have lagrange : (a 0 * b 0 + a 1 * b 1) ^ 2 + cross a b ^ 2
      = (a 0 ^ 2 + a 1 ^ 2) * (b 0 ^ 2 + b 1 ^ 2) := by simp only [cross]; ring
  have h1 : (a 0 * b 0 + a 1 * b 1) ^ 2 < (a 0 ^ 2 + a 1 ^ 2) * (b 0 ^ 2 + b 1 ^ 2) := by
    linarith [lagrange, hcross2]
  have hna : ‖a‖ = Real.sqrt (a 0 ^ 2 + a 1 ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg a), norm_sq]
  have hnb : ‖b‖ = Real.sqrt (b 0 ^ 2 + b 1 ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg b), norm_sq]
  have h2 : a 0 * b 0 + a 1 * b 1 < ‖a‖ * ‖b‖ := by
    have h3 := Real.lt_sqrt_of_sq_lt h1
    rwa [Real.sqrt_mul (by positivity), ← hna, ← hnb] at h3
  have h4 : (a 0 + b 0) ^ 2 + (a 1 + b 1) ^ 2 < (‖a‖ + ‖b‖) ^ 2 := by
    have e1 : (a 0 + b 0) ^ 2 + (a 1 + b 1) ^ 2
        = (a 0 ^ 2 + a 1 ^ 2) + (b 0 ^ 2 + b 1 ^ 2) + 2 * (a 0 * b 0 + a 1 * b 1) := by ring
    have e2 : (‖a‖ + ‖b‖) ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 + 2 * (‖a‖ * ‖b‖) := by ring
    rw [norm_sq a, norm_sq b] at e2
    linarith [e1, e2, h2]
  have hnab : ‖a + b‖ = Real.sqrt ((a 0 + b 0) ^ 2 + (a 1 + b 1) ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg _), norm_sq (a + b), PiLp.add_apply, PiLp.add_apply]
  rw [hnab, ← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ ‖a‖ + ‖b‖)]
  exact Real.sqrt_lt_sqrt (by positivity) h4

/-- In the plane, if `cross u w = 0` and `u ≠ 0`, then `w` is a scalar
multiple of `u`. -/
lemma exists_smul_of_cross_eq_zero {u w : Pt} (hu : u ≠ 0) (h : cross u w = 0) :
    ∃ t : ℝ, w = t • u := by
  have h1 : u 0 * w 1 = u 1 * w 0 := by
    simp only [cross] at h; linarith [h]
  by_cases hx : u 0 = 0
  · have hu1 : u 1 ≠ 0 := by
      intro hc
      apply hu
      ext i
      fin_cases i
      · exact hx
      · exact hc
    refine ⟨w 1 / u 1, ?_⟩
    ext i
    fin_cases i
    · show w 0 = ((w 1 / u 1 : ℝ) • u) 0
      simp only [PiLp.smul_apply, smul_eq_mul]
      have h2 : w 0 * u 1 = w 1 * u 0 := by linarith [h1]
      field_simp
      linarith [h2]
    · show w 1 = ((w 1 / u 1 : ℝ) • u) 1
      simp only [PiLp.smul_apply, smul_eq_mul]
      rw [div_mul_cancel₀ _ hu1]
  · refine ⟨w 0 / u 0, ?_⟩
    ext i
    fin_cases i
    · show w 0 = ((w 0 / u 0 : ℝ) • u) 0
      simp only [PiLp.smul_apply, smul_eq_mul]
      rw [div_mul_cancel₀ _ hx]
    · show w 1 = ((w 0 / u 0 : ℝ) • u) 1
      simp only [PiLp.smul_apply, smul_eq_mul]
      have h2 : w 1 * u 0 = w 0 * u 1 := by linarith [h1]
      field_simp
      linarith [h2]

/-!
## The quadrilateral inequality

For four points `P Q R S` in strictly convex position (counterclockwise),
the sum of the diagonals exceeds the sum of two opposite sides:
`dist P Q + dist R S < dist P R + dist Q S`.
-/

lemma diag_sum_gt {P Q R S : Pt}
    (hfQ : cross (R - P) (Q - P) < 0) (hfS : 0 < cross (R - P) (S - P))
    (hgP : 0 < cross (S - Q) (P - Q)) (hgR : cross (S - Q) (R - Q) < 0) :
    dist P Q + dist R S < dist P R + dist Q S := by
  have hD : cross (R - P) (S - Q) = cross (R - P) (S - P) - cross (R - P) (Q - P) := by
    have e : S - Q = S - P - (Q - P) := by abel
    rw [e, cross_sub_right]
  have hDpos : 0 < cross (R - P) (S - Q) := by rw [hD]; linarith [hfQ, hfS]
  set D := cross (R - P) (S - Q) with hDdef
  set u := - cross (R - P) (Q - P) / D with hu
  have hu0 : 0 < u := by rw [hu]; exact div_pos (by linarith [hfQ]) hDpos
  have hu1 : u < 1 := by
    rw [hu, div_lt_one hDpos]
    linarith [hfS, hD]
  set K := Q + u • (S - Q) with hK
  have hfK : cross (R - P) (K - P) = 0 := by
    have hKP : K - P = Q - P + u • (S - Q) := by rw [hK]; abel
    rw [hKP, cross_add_right, cross_smul_right, hu, div_mul_cancel₀ _ hDpos.ne']
    ring
  have hRP : R - P ≠ 0 := by
    intro h0
    rw [h0, cross_zero_left] at hfS
    exact lt_irrefl 0 hfS
  obtain ⟨t, ht⟩ := exists_smul_of_cross_eq_zero hRP hfK
  have hKQ : K - Q = u • (S - Q) := by rw [hK]; abel
  have htD : t * D = cross (S - Q) (P - Q) := by
    have h1 : cross (S - Q) (K - Q) = 0 := by
      rw [hKQ, cross_smul_right, cross_self, mul_zero]
    have h2 : K - Q = P - Q + t • (R - P) := by
      have h3 : K - Q = K - P + (P - Q) := by abel
      rw [h3, ht]; abel
    rw [h2, cross_add_right, cross_smul_right] at h1
    have hSD : cross (S - Q) (R - P) = -D := by rw [cross_comm, ← hDdef]
    rw [hSD] at h1
    linarith [h1]
  have ht_eq : t = cross (S - Q) (P - Q) / D := (eq_div_iff_mul_eq hDpos.ne').mpr htD
  have ht0 : 0 < t := by rw [ht_eq]; exact div_pos hgP hDpos
  have ht1 : t < 1 := by
    rw [ht_eq, div_lt_one hDpos]
    have hid : D - cross (S - Q) (P - Q) = - cross (S - Q) (R - Q) := by
      rw [hDdef]; simp only [cross, PiLp.sub_apply]; ring
    linarith [hgR, hid]
  have hK' : K = P + t • (R - P) := by
    have h3 := sub_eq_iff_eq_add.mp ht
    rw [h3]; abel
  have hdist_PK : dist P K = t * dist P R := by
    rw [dist_comm P K, dist_comm P R, dist_eq_norm, dist_eq_norm, ht, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg ht0.le]
  have hdist_KR : dist K R = (1 - t) * dist P R := by
    rw [dist_comm K R, dist_comm P R]
    simp only [dist_eq_norm]
    have e : R - K = (1 - t) • (R - P) := by
      rw [hK']
      calc R - (P + t • (R - P)) = R - P - t • (R - P) := by abel
        _ = (1 - t) • (R - P) := by rw [sub_smul, one_smul]
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht1])]
  have hdist_QK : dist Q K = u * dist Q S := by
    rw [dist_comm Q K, dist_comm Q S]
    simp only [dist_eq_norm]
    rw [hKQ, norm_smul, Real.norm_eq_abs, abs_of_nonneg hu0.le]
  have hdist_KS : dist K S = (1 - u) * dist Q S := by
    rw [dist_comm K S, dist_comm Q S]
    simp only [dist_eq_norm]
    have e : S - K = (1 - u) • (S - Q) := by
      rw [hK]
      calc S - (Q + u • (S - Q)) = S - Q - u • (S - Q) := by abel
        _ = (1 - u) • (S - Q) := by rw [sub_smul, one_smul]
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hu1])]
  have hst1 : dist P Q < dist P K + dist K Q := by
    rw [dist_comm P Q, dist_comm P K, dist_comm K Q]
    simp only [dist_eq_norm]
    have hab : K - P + (Q - K) = Q - P := by abel
    rw [← hab]
    apply strict_norm_add
    have hc : cross (K - P) (Q - K) = t * cross (R - P) (Q - P) := by
      have hQK : Q - K = Q - P - t • (R - P) := by rw [hK']; abel
      rw [ht, hQK, cross_sub_right, cross_smul_right, cross_smul_left, cross_smul_left,
        cross_self, mul_zero, mul_zero, sub_zero]
    rw [hc]
    exact mul_ne_zero ht0.ne' (ne_of_lt hfQ)
  have hst2 : dist R S < dist R K + dist K S := by
    rw [dist_comm R S, dist_comm R K, dist_comm K S]
    simp only [dist_eq_norm]
    have hab : K - R + (S - K) = S - R := by abel
    rw [← hab]
    apply strict_norm_add
    have hc : cross (K - R) (S - K) = (t - 1) * cross (R - P) (S - P) := by
      have hKR : K - R = (t - 1) • (R - P) := by
        rw [hK']
        calc P + t • (R - P) - R = t • (R - P) - (R - P) := by abel
          _ = (t - 1) • (R - P) := by rw [sub_smul, one_smul]
      have hSK : S - K = S - P - t • (R - P) := by rw [hK']; abel
      rw [hKR, hSK, cross_sub_right, cross_smul_right, cross_smul_left, cross_smul_left,
        cross_self, mul_zero, mul_zero, sub_zero]
    rw [hc]
    exact mul_ne_zero (by linarith [ht1]) (ne_of_gt hfS)
  have e1 : dist P R = dist P K + dist K R := by rw [hdist_PK, hdist_KR]; ring
  have e2 : dist Q S = dist Q K + dist K S := by rw [hdist_QK, hdist_KS]; ring
  have c1 : dist K Q = dist Q K := dist_comm K Q
  have c2 : dist R K = dist K R := dist_comm R K
  linarith [hst1, hst2, e1, e2, c1, c2]

/-!
## Polygon lemmas
-/

/-- The quadrilateral inequality applied to vertices `i, i+1, i+r, i+r+1`. -/
lemma quad_ineq {n : ℕ} [NeZero n] (v : ZMod n → Pt) (hconv : ConvexCCW v)
    (i : ZMod n) (r : ℕ) (h2 : 2 ≤ r) (hr : r ≤ n - 2) :
    side v i + side v (i + (r : ZMod n)) < F v i r + F v (i + 1) r := by
  have e2 : (i : ZMod n) + 1 + (r : ZMod n) = i + (r : ZMod n) + 1 := by ring
  show dist (v i) (v (i + 1)) + dist (v (i + ↑r)) (v (i + ↑r + 1))
    < dist (v i) (v (i + ↑r)) + dist (v (i + 1)) (v (i + 1 + ↑r))
  rw [e2]
  apply diag_sum_gt
  · have h := hconv i 1 r (by norm_num) h2 (by omega)
    rw [Nat.cast_one] at h
    have e : cross (v (i + ↑r) - v i) (v (i + 1) - v i)
        = - cross (v (i + 1) - v i) (v (i + ↑r) - v i) := cross_comm _ _
    rw [e]
    linarith [h]
  · have h := hconv i r (r + 1) (by omega) (by omega) (by omega)
    have e : (i : ZMod n) + ((r + 1 : ℕ) : ZMod n) = i + ↑r + 1 := by push_cast; ring
    rw [e] at h
    exact h
  · have h := hconv (i + 1) r (n - 1) (by omega) (by omega) (by omega)
    have e1 : (i : ZMod n) + 1 + ((n - 1 : ℕ) : ZMod n) = i := by
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one, ZMod.natCast_self]; ring
    have e3 : (i : ZMod n) + 1 + ↑r = i + ↑r + 1 := by ring
    rw [e1, e3] at h
    exact h
  · have h := hconv (i + 1) (r - 1) r (by omega) (by omega) (by omega)
    have e4 : (i : ZMod n) + 1 + ((r - 1 : ℕ) : ZMod n) = i + ↑r := by
      rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]; ring
    rw [e4] at h
    have e : cross (v (i + ↑r + 1) - v (i + 1)) (v (i + ↑r) - v (i + 1))
        = - cross (v (i + ↑r) - v (i + 1)) (v (i + ↑r + 1) - v (i + 1)) := cross_comm _ _
    rw [e]
    have e3 : (i : ZMod n) + ↑r + 1 = i + 1 + ↑r := by ring
    rw [e3]
    linarith [h]

/-- The straight segment is shorter than the polygonal path. -/
lemma F_le_arc {n : ℕ} [NeZero n] (v : ZMod n → Pt) (i : ZMod n) (r : ℕ) :
    F v i r ≤ arc v i r := by
  induction r with
  | zero =>
    show dist (v i) (v (i + ((0 : ℕ) : ZMod n)))
      ≤ ∑ s ∈ Finset.range 0, side v (i + (s : ZMod n))
    rw [Nat.cast_zero, add_zero, dist_self, Finset.sum_range_zero]
  | succ k ih =>
    show dist (v i) (v (i + ((k + 1 : ℕ) : ZMod n))) ≤ arc v i (k + 1)
    have e : (i : ZMod n) + ((k + 1 : ℕ) : ZMod n) = i + ↑k + 1 := by push_cast; ring
    rw [e]
    have h1 : dist (v i) (v (i + ↑k + 1))
        ≤ dist (v i) (v (i + ↑k)) + dist (v (i + ↑k)) (v (i + ↑k + 1)) :=
      dist_triangle _ _ _
    have h2 : arc v i (k + 1) = arc v i k + side v (i + ↑k) := by
      show ∑ s ∈ Finset.range (k + 1), side v (i + ↑s) = _
      rw [Finset.sum_range_succ]
    have h3 : dist (v i) (v (i + ↑k)) ≤ arc v i k := ih
    rw [h2]
    linarith [h1, h3]

/-- Strict version: for `2 ≤ r`, the segment is strictly shorter than the
polygonal path (the first step is not collinear, by convexity). -/
lemma F_lt_arc {n : ℕ} [NeZero n] (v : ZMod n → Pt) (hconv : ConvexCCW v)
    (i : ZMod n) (r : ℕ) (h2 : 2 ≤ r) (hr : r ≤ n - 1) :
    F v i r < arc v i r := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  have hk : 1 ≤ k := by omega
  have hst : dist (v i) (v (i + ((k + 1 : ℕ) : ZMod n)))
      < dist (v i) (v (i + 1)) + dist (v (i + 1)) (v (i + ((k + 1 : ℕ) : ZMod n))) := by
    simp only [dist_eq_norm']
    have hab : (v (i + 1) - v i) + (v (i + ((k + 1 : ℕ) : ZMod n)) - v (i + 1))
        = v (i + ((k + 1 : ℕ) : ZMod n)) - v i := by abel
    rw [← hab]
    apply strict_norm_add
    have h := hconv i 1 (k + 1) (by norm_num) (by omega) (by omega)
    rw [Nat.cast_one] at h
    have e : cross (v (i + 1) - v i) (v (i + ((k + 1 : ℕ) : ZMod n)) - v (i + 1))
        = cross (v (i + 1) - v i) (v (i + ((k + 1 : ℕ) : ZMod n)) - v i) := by
      have e2 : v (i + ((k + 1 : ℕ) : ZMod n)) - v (i + 1)
          = (v (i + ((k + 1 : ℕ) : ZMod n)) - v i) - (v (i + 1) - v i) := by abel
      rw [e2, cross_sub_right, cross_self, sub_zero]
    rw [e]
    exact ne_of_gt h
  have hle : dist (v (i + 1)) (v (i + ((k + 1 : ℕ) : ZMod n))) ≤ arc v (i + 1) k := by
    have e : (i : ZMod n) + 1 + ((k : ℕ) : ZMod n) = i + ((k + 1 : ℕ) : ZMod n) := by
      push_cast; ring
    have h3 : dist (v (i + 1)) (v (i + 1 + ((k : ℕ) : ZMod n))) ≤ arc v (i + 1) k :=
      F_le_arc v (i + 1) k
    rw [e] at h3
    exact h3
  have harc : arc v i (k + 1) = side v i + arc v (i + 1) k := by
    show ∑ s ∈ Finset.range (k + 1), side v (i + ↑s)
      = side v i + ∑ s ∈ Finset.range k, side v (i + 1 + ↑s)
    rw [Finset.sum_range_succ']
    rw [Nat.cast_zero, add_zero, add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro s _
    have e : (i : ZMod n) + ((s + 1 : ℕ) : ZMod n) = i + 1 + (s : ZMod n) := by
      push_cast; ring
    rw [e]
  rw [harc]
  show dist (v i) (v (i + ((k + 1 : ℕ) : ZMod n))) < side v i + arc v (i + 1) k
  linarith [hst, hle]

/-!
## Counting lemmas for sums over `ZMod n`
-/

lemma sum_side_shift {n : ℕ} [NeZero n] (v : ZMod n → Pt) (c : ZMod n) :
    ∑ i : ZMod n, side v (i + c) = perimeter v := by
  have h := Equiv.sum_comp (Equiv.addRight c) (fun i => side v i)
  simpa only [Equiv.coe_addRight] using h

lemma sum_F_shift {n : ℕ} [NeZero n] (v : ZMod n → Pt) (c : ZMod n) (s : ℕ) :
    ∑ i : ZMod n, F v (i + c) s = ∑ i : ZMod n, F v i s := by
  have h := Equiv.sum_comp (Equiv.addRight c) (fun i => F v i s)
  simpa only [Equiv.coe_addRight] using h

lemma sum_arc {n : ℕ} [NeZero n] (v : ZMod n → Pt) (r : ℕ) :
    ∑ i : ZMod n, arc v i r = (r : ℝ) * perimeter v := by
  calc ∑ i : ZMod n, arc v i r
      = ∑ s ∈ Finset.range r, ∑ i : ZMod n, side v (i + (s : ZMod n)) := Finset.sum_comm
    _ = ∑ s ∈ Finset.range r, perimeter v := by
        apply Finset.sum_congr rfl
        intro s _
        exact sum_side_shift v s
    _ = (r : ℝ) * perimeter v := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

lemma zmod_sum_range {n : ℕ} [NeZero n] (f : ZMod n → ℝ) :
    (∑ s ∈ Finset.range n, f (s : ZMod n)) = ∑ x : ZMod n, f x := by
  refine (Finset.sum_bij' (fun x _ => ZMod.val x) (fun s _ => (s : ZMod n)) ?_ ?_ ?_ ?_ ?_).symm
  · intro x _
    exact Finset.mem_range.mpr (ZMod.val_lt x)
  · intro s _
    exact Finset.mem_univ _
  · intro x _
    exact ZMod.natCast_zmod_val x
  · intro s hs
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hs)]
  · intro x _
    congr 1
    exact (ZMod.natCast_zmod_val x).symm

/-- Two complementary arcs make the full perimeter. -/
lemma arc_add {n : ℕ} [NeZero n] (v : ZMod n → Pt) (i : ZMod n) (r : ℕ) (hr : r ≤ n) :
    arc v i r + arc v (i + (r : ZMod n)) (n - r) = perimeter v := by
  have e : ∀ s : ℕ, (i : ZMod n) + (r : ZMod n) + (s : ZMod n) = i + ((r + s : ℕ) : ZMod n) := by
    intro s
    push_cast
    ring
  have h1 : ∑ s ∈ Finset.range (n - r), side v (i + (r : ZMod n) + (s : ZMod n))
      = ∑ s ∈ Finset.range (n - r), side v (i + ((r + s : ℕ) : ZMod n)) := by
    apply Finset.sum_congr rfl
    intro s _
    rw [e s]
  have h2 : ∑ t ∈ Finset.range n, side v (i + (t : ZMod n)) = perimeter v := by
    rw [zmod_sum_range (fun x => side v (i + x))]
    have h3 : ∑ x : ZMod n, side v (i + x) = ∑ x : ZMod n, side v (x + i) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [add_comm]
    rw [h3]
    exact sum_side_shift v i
  have h4 : ∑ s ∈ Finset.range r, side v (i + (s : ZMod n))
      = ∑ t ∈ Finset.Ico 0 r, side v (i + (t : ZMod n)) := by rw [Finset.range_eq_Ico]
  have h5 : ∑ s ∈ Finset.range (n - r), side v (i + ((r + s : ℕ) : ZMod n))
      = ∑ t ∈ Finset.Ico r n, side v (i + (t : ZMod n)) := by
    rw [Finset.sum_Ico_eq_sum_range]
  calc arc v i r + arc v (i + ↑r) (n - r)
      = ∑ t ∈ Finset.Ico 0 r, side v (i + (t : ZMod n))
        + ∑ t ∈ Finset.Ico r n, side v (i + (t : ZMod n)) := by
        show (∑ s ∈ Finset.range r, side v (i + (s : ZMod n)))
          + (∑ s ∈ Finset.range (n - r), side v (i + ↑r + (s : ZMod n))) = _
        rw [h4, h1, h5]
    _ = ∑ t ∈ Finset.Ico 0 n, side v (i + (t : ZMod n)) :=
        Finset.sum_Ico_consecutive _ (Nat.zero_le r) hr
    _ = ∑ t ∈ Finset.range n, side v (i + (t : ZMod n)) := by rw [Finset.range_eq_Ico]
    _ = perimeter v := h2

/-- Symmetry of the diagonal lengths: the diagonal from `i` to `i + r` is the
same as the diagonal from `i + r` to `i + (n - r)`. -/
lemma Fsym {n : ℕ} [NeZero n] (v : ZMod n → Pt) (i : ZMod n) (r : ℕ) (hr : r ≤ n) :
    F v i r = F v (i + (r : ZMod n)) (n - r) := by
  show dist (v i) (v (i + ↑r)) = dist (v (i + ↑r)) (v (i + ↑r + ↑(n - r)))
  have e : (i : ZMod n) + (r : ZMod n) + ((n - r : ℕ) : ZMod n) = i := by
    rw [Nat.cast_sub hr, ZMod.natCast_self]
    ring
  rw [e, dist_comm]

/-- Reflection of an interval sum: `r ↦ n - r` sends `[m+1, n-1)` to
`[2, n - m)`. -/
lemma reflect {n : ℕ} [NeZero n] (m : ℕ) (_hm : m + 1 ≤ n - 1) (g : ℕ → ℝ) :
    ∑ r ∈ Finset.Ico (m + 1) (n - 1), g (n - r) = ∑ r ∈ Finset.Ico 2 (n - m), g r := by
  rw [Finset.sum_Ico_eq_sum_range]
  show ∑ i ∈ Finset.range (n - 1 - (m + 1)), g (n - (m + 1 + i)) = _
  have e : ∀ i ∈ Finset.range (n - 1 - (m + 1)),
      g (n - (m + 1 + i)) = g ((n - 1 - (m + 1)) - 1 - i + 2) := by
    intro i hi
    have hi2 := Finset.mem_range.mp hi
    congr 1
    omega
  calc ∑ i ∈ Finset.range (n - 1 - (m + 1)), g (n - (m + 1 + i))
      = ∑ i ∈ Finset.range (n - 1 - (m + 1)), g ((n - 1 - (m + 1)) - 1 - i + 2) :=
        Finset.sum_congr rfl e
    _ = ∑ j ∈ Finset.range (n - 1 - (m + 1)), g (j + 2) :=
        Finset.sum_range_reflect (fun j => g (j + 2)) (n - 1 - (m + 1))
    _ = ∑ r ∈ Finset.Ico 2 (n - m), g r := by
        have hk2 : n - 1 - (m + 1) = n - m - 2 := by omega
        rw [hk2]
        have h3 : ∑ r ∈ Finset.Ico 2 (n - m), g r
            = ∑ j ∈ Finset.range (n - m - 2), g (2 + j) := Finset.sum_Ico_eq_sum_range g 2 (n - m)
        rw [h3]
        apply Finset.sum_congr rfl
        intro j _
        rw [add_comm]

/-- The "second half" of the diagonal sum equals a sum over short arcs. -/
lemma secondHalf {n : ℕ} [NeZero n] (v : ZMod n → Pt) (m : ℕ) (hm : m + 1 ≤ n - 1) :
    ∑ i : ZMod n, ∑ r ∈ Finset.Ico (m + 1) (n - 1), F v i r
      = ∑ j : ZMod n, ∑ r ∈ Finset.Ico 2 (n - m), F v j r := by
  calc ∑ i : ZMod n, ∑ r ∈ Finset.Ico (m + 1) (n - 1), F v i r
      = ∑ r ∈ Finset.Ico (m + 1) (n - 1), ∑ i : ZMod n, F v i r := Finset.sum_comm
    _ = ∑ r ∈ Finset.Ico (m + 1) (n - 1), ∑ i : ZMod n, F v (i + (r : ZMod n)) (n - r) := by
        apply Finset.sum_congr rfl
        intro r hr
        apply Finset.sum_congr rfl
        intro i _
        have hrn : r ≤ n := by
          have h := (Finset.mem_Ico.mp hr).2
          omega
        exact Fsym v i r hrn
    _ = ∑ r ∈ Finset.Ico (m + 1) (n - 1), ∑ j : ZMod n, F v j (n - r) := by
        apply Finset.sum_congr rfl
        intro r _
        exact sum_F_shift v (↑r) (n - r)
    _ = ∑ j : ZMod n, ∑ r ∈ Finset.Ico (m + 1) (n - 1), F v j (n - r) := Finset.sum_comm
    _ = ∑ j : ZMod n, ∑ r ∈ Finset.Ico 2 (n - m), F v j r := by
        apply Finset.sum_congr rfl
        intro j _
        exact reflect m hm (fun r => F v j r)

/-- Twice the sum of `r` over `r ∈ [2, a)`, as a real number. -/
lemma two_mul_sum_Ico_ge2 (a : ℕ) (ha : 2 ≤ a) :
    (2 : ℝ) * ∑ r ∈ Finset.Ico 2 a, (r : ℝ) = (a : ℝ) * (a - 1) - 2 := by
  rcases (by omega : a = 2 ∨ 3 ≤ a) with rfl | ha3
  · rw [Finset.Ico_self, Finset.sum_empty]
    norm_num
  · have hS : (∑ i ∈ Finset.range (a - 2), (i : ℝ)) * 2 = ((a : ℝ) - 2) * ((a : ℝ) - 3) := by
      have h2 : ((∑ i ∈ Finset.range (a - 2), i : ℕ) : ℝ) * 2
          = (((a - 2) * (a - 3) : ℕ) : ℝ) := by
        have h1' : (∑ i ∈ Finset.range (a - 2), i) * 2 = (a - 2) * (a - 3) := by
          have h1 := Finset.sum_range_id_mul_two (a - 2)
          rwa [Nat.sub_sub] at h1
        exact_mod_cast h1'
      rw [Nat.cast_sum, Nat.cast_mul, Nat.cast_sub (by omega : 2 ≤ a), Nat.cast_ofNat,
        Nat.cast_sub (by omega : 3 ≤ a), Nat.cast_ofNat] at h2
      exact h2
    rw [Finset.sum_Ico_eq_sum_range]
    show (2 : ℝ) * ∑ i ∈ Finset.range (a - 2), ((2 + i : ℕ) : ℝ) = (a : ℝ) * (a - 1) - 2
    have e : ∑ i ∈ Finset.range (a - 2), ((2 + i : ℕ) : ℝ)
        = ∑ i ∈ Finset.range (a - 2), (2 + (i : ℝ)) := by
      apply Finset.sum_congr rfl
      intro i _
      push_cast
      ring
    rw [e, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      Nat.cast_sub (by omega : 2 ≤ a), Nat.cast_ofNat]
    have e2 : (2 : ℝ) * (((a : ℝ) - 2) * 2 + ∑ i ∈ Finset.range (a - 2), (i : ℝ))
        = 4 * ((a : ℝ) - 2) + (∑ i ∈ Finset.range (a - 2), (i : ℝ)) * 2 := by ring
    rw [e2, hS]
    ring

/-- The perimeter is positive. -/
lemma perim_pos {n : ℕ} [NeZero n] (v : ZMod n → Pt) (hconv : ConvexCCW v) (hn : 3 < n) :
    0 < perimeter v := by
  apply Finset.sum_pos'
  · intro i _
    exact dist_nonneg
  · refine ⟨0, Finset.mem_univ _, ?_⟩
    have h := hconv 0 1 2 (by norm_num) (by norm_num) (by omega)
    simp only [zero_add, Nat.cast_one, Nat.cast_ofNat] at h
    show (0 : ℝ) < dist (v 0) (v (0 + 1))
    rw [zero_add, dist_pos]
    intro heq
    have h0 : v (1 : ZMod n) - v 0 = 0 := by rw [← heq, sub_self]
    rw [h0, cross_zero_left] at h
    exact lt_irrefl 0 h

/-!
## The lower bound
-/

lemma lower_bound {n : ℕ} [NeZero n] (v : ZMod n → Pt) (hconv : ConvexCCW v) (hn : 3 < n) :
    ((n : ℝ) - 3) * perimeter v < diagTwoSum v := by
  have h1 : ∀ i : ZMod n, ∀ r ∈ Finset.Ico 2 (n - 1),
      side v i + side v (i + (r : ZMod n)) < F v i r + F v (i + 1) r := by
    intro i r hr
    have hr2 : 2 ≤ r := (Finset.mem_Ico.mp hr).1
    have hrn : r ≤ n - 2 := by
      have h := (Finset.mem_Ico.mp hr).2
      omega
    exact quad_ineq v hconv i r hr2 hrn
  have hsum : ∑ i : ZMod n, ∑ r ∈ Finset.Ico 2 (n - 1), (side v i + side v (i + (r : ZMod n)))
      < ∑ i : ZMod n, ∑ r ∈ Finset.Ico 2 (n - 1), (F v i r + F v (i + 1) r) := by
    apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    intro i _
    apply Finset.sum_lt_sum_of_nonempty
    · exact ⟨2, Finset.mem_Ico.mpr ⟨le_refl 2, by omega⟩⟩
    · intro r hr
      exact h1 i r hr
  have hcard : (Finset.Ico 2 (n - 1)).card = n - 3 := by rw [Nat.card_Ico]; omega
  have hcast : ((n - 3 : ℕ) : ℝ) = (n : ℝ) - 3 := by
    rw [Nat.cast_sub (by omega : 3 ≤ n), Nat.cast_ofNat]
  have hL : ∑ i : ZMod n, ∑ r ∈ Finset.Ico 2 (n - 1), (side v i + side v (i + (r : ZMod n)))
      = 2 * (((n : ℝ) - 3) * perimeter v) := by
    calc ∑ i : ZMod n, ∑ r ∈ Finset.Ico 2 (n - 1), (side v i + side v (i + (r : ZMod n)))
        = ∑ i : ZMod n, ((n - 3 : ℕ) • side v i
            + ∑ r ∈ Finset.Ico 2 (n - 1), side v (i + (r : ZMod n))) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_add_distrib, Finset.sum_const, hcard]
      _ = ∑ i : ZMod n, (((n : ℝ) - 3) * side v i
            + ∑ r ∈ Finset.Ico 2 (n - 1), side v (i + (r : ZMod n))) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [nsmul_eq_mul, hcast]
      _ = ((n : ℝ) - 3) * ∑ i : ZMod n, side v i
            + ∑ i : ZMod n, ∑ r ∈ Finset.Ico 2 (n - 1), side v (i + (r : ZMod n)) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = ((n : ℝ) - 3) * perimeter v + (n - 3 : ℕ) • perimeter v := by
          congr 1
          calc ∑ i : ZMod n, ∑ r ∈ Finset.Ico 2 (n - 1), side v (i + (r : ZMod n))
              = ∑ r ∈ Finset.Ico 2 (n - 1), ∑ i : ZMod n, side v (i + (r : ZMod n)) :=
                Finset.sum_comm
            _ = ∑ r ∈ Finset.Ico 2 (n - 1), perimeter v := by
                apply Finset.sum_congr rfl
                intro r _
                exact sum_side_shift v r
            _ = (n - 3 : ℕ) • perimeter v := by rw [Finset.sum_const, hcard]
      _ = 2 * (((n : ℝ) - 3) * perimeter v) := by rw [nsmul_eq_mul, hcast]; ring
  have hR : ∑ i : ZMod n, ∑ r ∈ Finset.Ico 2 (n - 1), (F v i r + F v (i + 1) r)
      = 2 * diagTwoSum v := by
    have step1 : ∑ i : ZMod n, ∑ r ∈ Finset.Ico 2 (n - 1), (F v i r + F v (i + 1) r)
        = diagTwoSum v + ∑ i : ZMod n, ∑ r ∈ Finset.Ico 2 (n - 1), F v (i + 1) r := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_add_distrib
    have step2 : ∑ i : ZMod n, ∑ r ∈ Finset.Ico 2 (n - 1), F v (i + 1) r = diagTwoSum v := by
      calc ∑ i : ZMod n, ∑ r ∈ Finset.Ico 2 (n - 1), F v (i + 1) r
          = ∑ r ∈ Finset.Ico 2 (n - 1), ∑ i : ZMod n, F v (i + 1) r := Finset.sum_comm
        _ = ∑ r ∈ Finset.Ico 2 (n - 1), ∑ i : ZMod n, F v i r := by
            apply Finset.sum_congr rfl
            intro r _
            exact sum_F_shift v 1 r
        _ = diagTwoSum v := Finset.sum_comm
    rw [step1, step2]
    ring
  rw [hL, hR] at hsum
  linarith [hsum]

/-!
## The upper bound
-/

lemma upper_odd {n : ℕ} [NeZero n] (v : ZMod n → Pt) (hconv : ConvexCCW v) (m : ℕ)
    (hm : n = 2 * m + 1) (hm2 : 2 ≤ m) :
    diagTwoSum v < ((m : ℝ) * (m + 1) - 2) * perimeter v := by
  have hn1 : n - 1 = 2 * m := by omega
  have hm1 : m + 1 ≤ n - 1 := by omega
  have hnm : n - m = m + 1 := by omega
  have hsplit : diagTwoSum v
      = (∑ i : ZMod n, ∑ r ∈ Finset.Ico 2 (m + 1), F v i r)
        + ∑ i : ZMod n, ∑ r ∈ Finset.Ico (m + 1) (n - 1), F v i r := by
    show ∑ i : ZMod n, ∑ r ∈ Finset.Ico 2 (n - 1), F v i r = _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hn1]
    exact (Finset.sum_Ico_consecutive _ (by omega : 2 ≤ m + 1) (by omega : m + 1 ≤ 2 * m)).symm
  have hB : ∑ i : ZMod n, ∑ r ∈ Finset.Ico (m + 1) (n - 1), F v i r
      = ∑ i : ZMod n, ∑ r ∈ Finset.Ico 2 (m + 1), F v i r := by
    have h := secondHalf v m hm1
    rw [hnm] at h
    exact h
  have hA : ∑ i : ZMod n, ∑ r ∈ Finset.Ico 2 (m + 1), F v i r
      < (∑ r ∈ Finset.Ico 2 (m + 1), (r : ℝ)) * perimeter v := by
    calc ∑ i : ZMod n, ∑ r ∈ Finset.Ico 2 (m + 1), F v i r
        < ∑ i : ZMod n, ∑ r ∈ Finset.Ico 2 (m + 1), arc v i r := by
          apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
          intro i _
          apply Finset.sum_lt_sum_of_nonempty
          · exact ⟨2, Finset.mem_Ico.mpr ⟨le_refl 2, by omega⟩⟩
          · intro r hr
            have hr2 : 2 ≤ r := (Finset.mem_Ico.mp hr).1
            have hrm : r ≤ m := by
              have h := (Finset.mem_Ico.mp hr).2
              omega
            exact F_lt_arc v hconv i r hr2 (by omega)
      _ = ∑ r ∈ Finset.Ico 2 (m + 1), ∑ i : ZMod n, arc v i r := Finset.sum_comm
      _ = ∑ r ∈ Finset.Ico 2 (m + 1), ((r : ℝ) * perimeter v) := by
          apply Finset.sum_congr rfl
          intro r _
          exact sum_arc v r
      _ = (∑ r ∈ Finset.Ico 2 (m + 1), (r : ℝ)) * perimeter v := by rw [Finset.sum_mul]
  have hcount : (2 : ℝ) * ∑ r ∈ Finset.Ico 2 (m + 1), (r : ℝ) = (m : ℝ) * (m + 1) - 2 := by
    have h := two_mul_sum_Ico_ge2 (m + 1) (by omega)
    rw [Nat.cast_add, Nat.cast_one] at h
    rw [h]
    ring
  have hT : diagTwoSum v = 2 * (∑ i : ZMod n, ∑ r ∈ Finset.Ico 2 (m + 1), F v i r) := by
    rw [hsplit, hB]
    ring
  rw [hT]
  calc 2 * (∑ i : ZMod n, ∑ r ∈ Finset.Ico 2 (m + 1), F v i r)
      < 2 * ((∑ r ∈ Finset.Ico 2 (m + 1), (r : ℝ)) * perimeter v) :=
        mul_lt_mul_of_pos_left hA (by norm_num : (0 : ℝ) < 2)
    _ = ((2 : ℝ) * ∑ r ∈ Finset.Ico 2 (m + 1), (r : ℝ)) * perimeter v := by ring
    _ = ((m : ℝ) * (m + 1) - 2) * perimeter v := by rw [hcount]

lemma upper_even {n : ℕ} [NeZero n] (v : ZMod n → Pt) (hconv : ConvexCCW v) (m : ℕ)
    (hm : n = 2 * m) (hm2 : 2 ≤ m) :
    diagTwoSum v < ((m : ℝ) * m - 2) * perimeter v := by
  have hn1 : n - 1 = 2 * m - 1 := by omega
  have hm1 : m + 1 ≤ n - 1 := by omega
  have hnm : n - m = m := by omega
  have hsplit : diagTwoSum v
      = (∑ i : ZMod n, ∑ r ∈ Finset.Ico 2 m, F v i r) + (∑ i : ZMod n, F v i m)
        + ∑ i : ZMod n, ∑ r ∈ Finset.Ico (m + 1) (n - 1), F v i r := by
    show ∑ i : ZMod n, ∑ r ∈ Finset.Ico 2 (n - 1), F v i r = _
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hn1]
    have h1 := Finset.sum_Ico_consecutive (fun r => F v i r) (by omega : 2 ≤ m)
      (by omega : m ≤ 2 * m - 1)
    have h2 := Finset.sum_Ico_consecutive (fun r => F v i r) (by omega : m ≤ m + 1)
      (by omega : m + 1 ≤ 2 * m - 1)
    rw [Nat.Ico_succ_singleton, Finset.sum_singleton] at h2
    rw [← h1, ← h2, add_assoc]
  have hB : ∑ i : ZMod n, ∑ r ∈ Finset.Ico (m + 1) (n - 1), F v i r
      = ∑ i : ZMod n, ∑ r ∈ Finset.Ico 2 m, F v i r := by
    have h := secondHalf v m hm1
    rw [hnm] at h
    exact h
  have hA : ∑ i : ZMod n, ∑ r ∈ Finset.Ico 2 m, F v i r
      ≤ (∑ r ∈ Finset.Ico 2 m, (r : ℝ)) * perimeter v := by
    calc ∑ i : ZMod n, ∑ r ∈ Finset.Ico 2 m, F v i r
        ≤ ∑ i : ZMod n, ∑ r ∈ Finset.Ico 2 m, arc v i r := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro r _
          exact F_le_arc v i r
      _ = ∑ r ∈ Finset.Ico 2 m, ∑ i : ZMod n, arc v i r := Finset.sum_comm
      _ = ∑ r ∈ Finset.Ico 2 m, ((r : ℝ) * perimeter v) := by
          apply Finset.sum_congr rfl
          intro r _
          exact sum_arc v r
      _ = (∑ r ∈ Finset.Ico 2 m, (r : ℝ)) * perimeter v := by rw [Finset.sum_mul]
  have hcount : (2 : ℝ) * ∑ r ∈ Finset.Ico 2 m, (r : ℝ) = (m : ℝ) * (m - 1) - 2 :=
    two_mul_sum_Ico_ge2 m hm2
  have hM : ∑ i : ZMod n, F v i m < (m : ℝ) * perimeter v := by
    have hFi : ∀ i : ZMod n, 2 * F v i m < perimeter v := by
      intro i
      have h1 : F v i m < arc v i m := F_lt_arc v hconv i m hm2 (by omega)
      have h2 : F v (i + (m : ZMod n)) m ≤ arc v (i + (m : ZMod n)) m := F_le_arc v _ m
      have h3 : F v i m = F v (i + (m : ZMod n)) (n - m) := Fsym v i m (by omega)
      rw [hnm] at h3
      have h4 : arc v i m + arc v (i + (m : ZMod n)) (n - m) = perimeter v :=
        arc_add v i m (by omega)
      rw [hnm] at h4
      linarith [h1, h2, h3, h4]
    calc ∑ i : ZMod n, F v i m
        < ∑ i : ZMod n, (perimeter v / 2) := by
          apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
          intro i _
          have h := hFi i
          linarith [h]
      _ = (m : ℝ) * perimeter v := by
          rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
          have hnR : (n : ℝ) = 2 * m := by rw [hm]; push_cast; ring
          rw [hnR]
          ring
  calc diagTwoSum v
      = 2 * (∑ i : ZMod n, ∑ r ∈ Finset.Ico 2 m, F v i r) + ∑ i : ZMod n, F v i m := by
        rw [hsplit, hB]
        ring
    _ < 2 * ((∑ r ∈ Finset.Ico 2 m, (r : ℝ)) * perimeter v) + (m : ℝ) * perimeter v := by
        have h2 := mul_le_mul_of_nonneg_left hA (by norm_num : (0 : ℝ) ≤ 2)
        linarith [h2, hM]
    _ = ((m : ℝ) * m - 2) * perimeter v := by
        have e : (2 : ℝ) * ((∑ r ∈ Finset.Ico 2 m, (r : ℝ)) * perimeter v)
            = ((2 : ℝ) * ∑ r ∈ Finset.Ico 2 m, (r : ℝ)) * perimeter v := by ring
        rw [e, hcount]
        ring

snip end

problem imo1984_p5 (n : ℕ) [NeZero n] (hn : 3 < n) (v : ZMod n → Pt)
    (hconv : ConvexCCW v) :
    (n : ℝ) - 3 < 2 * diagonalsSum v / perimeter v ∧
      2 * diagonalsSum v / perimeter v < (((n / 2) * ((n + 1) / 2) - 2 : ℕ) : ℝ) := by
  have hp := perim_pos v hconv hn
  have h2d : 2 * diagonalsSum v = diagTwoSum v := by
    show 2 * (diagTwoSum v / 2) = diagTwoSum v
    ring
  have hlow := lower_bound v hconv hn
  obtain ⟨m, hm⟩ : ∃ m, n = 2 * m ∨ n = 2 * m + 1 := ⟨n / 2, by omega⟩
  have hm2 : 2 ≤ m := by omega
  have hup : diagTwoSum v < (((n / 2) * ((n + 1) / 2) - 2 : ℕ) : ℝ) * perimeter v := by
    rcases hm with rfl | rfl
    · have h := upper_even v hconv m rfl hm2
      have e1 : (2 * m) / 2 = m := by omega
      have e2 : (2 * m + 1) / 2 = m := by omega
      rw [e1, e2]
      have hc : ((m * m - 2 : ℕ) : ℝ) = (m : ℝ) * m - 2 := by
        have h4 : 4 ≤ m * m := Nat.mul_le_mul hm2 hm2
        rw [Nat.cast_sub (by omega : 2 ≤ m * m), Nat.cast_mul, Nat.cast_ofNat]
      rw [hc]
      exact h
    · have h := upper_odd v hconv m rfl hm2
      have e1 : (2 * m + 1) / 2 = m := by omega
      have e2 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
      rw [e1, e2]
      have hc : ((m * (m + 1) - 2 : ℕ) : ℝ) = (m : ℝ) * (m + 1) - 2 := by
        have h4 : 4 ≤ m * (m + 1) := by nlinarith [hm2]
        rw [Nat.cast_sub (by omega : 2 ≤ m * (m + 1)), Nat.cast_mul, Nat.cast_add,
          Nat.cast_one, Nat.cast_ofNat]
      rw [hc]
      exact h
  rw [h2d]
  constructor
  · rw [lt_div_iff₀ hp]
    exact hlow
  · rw [div_lt_iff₀ hp]
    exact hup

end Imo1984P5
