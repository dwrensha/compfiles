/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry, .Combinatorics] }

/-!
# USA Mathematical Olympiad 1998, Problem 6

Let n ≥ 5 be an integer. Find the largest integer k (as a function of n)
such that there exists a convex n-gon A₁A₂...Aₙ for which exactly k of the
quadrilaterals AᵢAᵢ₊₁Aᵢ₊₂Aᵢ₊₃ have an inscribed circle, where indices are
taken modulo n.
-/

namespace Usa1998P6

open Real Finset

open scoped InnerProductSpace

/-- The Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The 2-dimensional cross product (determinant of the two vectors). -/
def cross (u v : Plane) : ℝ := u 0 * v 1 - u 1 * v 0

/-- A convex quadrilateral has an inscribed circle if and only if the sums of
lengths of its two pairs of opposite sides are equal (Pitot's theorem and its
converse).  Every quadrilateral formed by four consecutive vertices of a
strictly convex polygon is convex, so for the purposes of this problem we may
(and do) take the equality of the two sums as the definition of "having an
inscribed circle". -/
def TangentialQuad (a b c d : Plane) : Prop :=
  dist a b + dist c d = dist b c + dist d a

/-- A strictly convex polygon with vertices in counterclockwise order:
every vertex lies strictly to the left of every edge line.  This is one of the
standard characterizations of a strictly convex polygon (given in either
orientation in the original problem; mirroring does not change the side
lengths, so the answer is the same). -/
def ConvexPolygon {N : ℕ} (A : ZMod N → Plane) : Prop :=
  ∀ i j : ZMod N, j ≠ i → j ≠ i + 1 → cross (A (i + 1) - A i) (A j - A i) > 0

/-- The number of quadrilaterals formed by four consecutive vertices that
have an inscribed circle. -/
noncomputable def numTangential {N : ℕ} [NeZero N] (A : ZMod N → Plane) : ℕ :=
  letI : DecidablePred (fun i : ZMod N ↦
    TangentialQuad (A i) (A (i + 1)) (A (i + 2)) (A (i + 3))) := Classical.decPred _
  (Finset.univ.filter fun i : ZMod N ↦
    TangentialQuad (A i) (A (i + 1)) (A (i + 2)) (A (i + 3))).card

snip begin

/-! ### Algebra of the cross product -/

@[simp] lemma cross_apply (u v : Plane) : cross u v = u 0 * v 1 - u 1 * v 0 := rfl

lemma cross_add_left (u v w : Plane) : cross (u + v) w = cross u w + cross v w := by
  simp only [cross, PiLp.add_apply]
  ring

lemma cross_neg_left (u v : Plane) : cross (-u) v = -cross u v := by
  simp only [cross, PiLp.neg_apply]
  ring

lemma cross_sub_left (u v w : Plane) : cross (u - v) w = cross u w - cross v w := by
  simp only [cross, PiLp.sub_apply]
  ring

lemma cross_smul_left (r : ℝ) (u v : Plane) : cross (r • u) v = r * cross u v := by
  simp only [cross, PiLp.smul_apply, smul_eq_mul]
  ring

lemma cross_add_right (u v w : Plane) : cross u (v + w) = cross u v + cross u w := by
  simp only [cross, PiLp.add_apply]
  ring

lemma cross_neg_right (u v : Plane) : cross u (-v) = -cross u v := by
  simp only [cross, PiLp.neg_apply]
  ring

lemma cross_sub_right (u v w : Plane) : cross u (v - w) = cross u v - cross u w := by
  simp only [cross, PiLp.sub_apply]
  ring

lemma cross_smul_right (r : ℝ) (u v : Plane) : cross u (r • v) = r * cross u v := by
  simp only [cross, PiLp.smul_apply, smul_eq_mul]
  ring

@[simp] lemma cross_self (u : Plane) : cross u u = 0 := by
  simp only [cross]
  ring

lemma cross_comm (u v : Plane) : cross u v = -cross v u := by
  simp only [cross]
  ring

/-- The "cocycle" (Plücker) identity for signed areas. -/
lemma cross_plucker (a b d e : Plane) :
    cross (b - a) (e - a) =
      cross (b - a) (d - a) + cross (d - a) (e - a) - cross (d - b) (e - b) := by
  simp only [cross, PiLp.sub_apply]
  ring

/-- The cyclic symmetry of the signed area. -/
lemma cross_cyc (a b c : Plane) :
    cross (b - a) (c - a) = cross (c - b) (a - b) := by
  simp only [cross, PiLp.sub_apply]
  ring

lemma cross_cyc' (a b c : Plane) :
    cross (b - a) (c - a) = cross (a - c) (b - c) := by
  simp only [cross, PiLp.sub_apply]
  ring

/-- If a vector is parallel to two non-parallel vectors, it is zero. -/
lemma eq_zero_of_cross_left_eq_zero {w v₁ v₂ : Plane}
    (h1 : cross w v₁ = 0) (h2 : cross w v₂ = 0) (h : cross v₁ v₂ ≠ 0) : w = 0 := by
  have h1' : w 0 * v₁ 1 = w 1 * v₁ 0 := by
    have hh := h1
    simp only [cross] at hh
    linarith
  have h2' : w 0 * v₂ 1 = w 1 * v₂ 0 := by
    have hh := h2
    simp only [cross] at hh
    linarith
  have hw0 : w 0 = 0 := by
    have e : w 0 * cross v₁ v₂ = 0 := by
      simp only [cross]
      linear_combination v₁ 0 * h2' - v₂ 0 * h1'
    exact (mul_eq_zero.mp e).resolve_right h
  have hw1 : w 1 = 0 := by
    have e : w 1 * cross v₁ v₂ = 0 := by
      simp only [cross]
      linear_combination v₁ 1 * h2' - v₂ 1 * h1'
    exact (mul_eq_zero.mp e).resolve_right h
  ext i
  fin_cases i <;> simp only [PiLp.zero_apply] <;> assumption

/-! ### Points on the unit circle -/

/-- The point on the unit circle at angle `θ`. -/
noncomputable def pt (θ : ℝ) : Plane := WithLp.toLp 2 ![Real.cos θ, Real.sin θ]

@[simp] lemma pt_zero (θ : ℝ) : pt θ 0 = Real.cos θ := rfl

@[simp] lemma pt_one (θ : ℝ) : pt θ 1 = Real.sin θ := rfl

/-- The master identity for the signed area of a triangle of circle points. -/
lemma cross_pt_sub (a b c : ℝ) :
    cross (pt b - pt a) (pt c - pt a) =
      Real.sin (c - b) + Real.sin (b - a) - Real.sin (c - a) := by
  simp only [cross, PiLp.sub_apply, pt_zero, pt_one]
  rw [Real.sin_sub, Real.sin_sub, Real.sin_sub]
  ring

/-- The identity `sin X + sin Y - sin (X + Y) = 4 sin(X/2) sin(Y/2) sin((X+Y)/2)`. -/
lemma sin_add_sub_eq (X Y : ℝ) :
    Real.sin X + Real.sin Y - Real.sin (X + Y) =
      4 * Real.sin (X / 2) * Real.sin (Y / 2) * Real.sin ((X + Y) / 2) := by
  have e1 : Real.sin X = 2 * Real.sin (X / 2) * Real.cos (X / 2) := by
    conv_lhs => rw [show X = 2 * (X / 2) from by ring]
    rw [Real.sin_two_mul]
  have e2 : Real.sin Y = 2 * Real.sin (Y / 2) * Real.cos (Y / 2) := by
    conv_lhs => rw [show Y = 2 * (Y / 2) from by ring]
    rw [Real.sin_two_mul]
  have e3 : Real.sin (X + Y) = 2 * Real.sin ((X + Y) / 2) * Real.cos ((X + Y) / 2) := by
    conv_lhs => rw [show X + Y = 2 * ((X + Y) / 2) from by ring]
    rw [Real.sin_two_mul]
  have e4 : (X + Y) / 2 = X / 2 + Y / 2 := by ring
  rw [e1, e2, e3, e4, Real.sin_add, Real.cos_add]
  have h1 := Real.sin_sq (X / 2)
  have h2 := Real.sin_sq (Y / 2)
  linear_combination
    -(2 * Real.sin (X / 2) * Real.cos (X / 2) * h2 +
      2 * Real.sin (Y / 2) * Real.cos (Y / 2) * h1)

/-- The signed area of a triangle of circle points, in factored form. -/
lemma cross_pt_sub_factor (a b c : ℝ) :
    cross (pt b - pt a) (pt c - pt a) =
      4 * Real.sin ((c - b) / 2) * Real.sin ((b - a) / 2) * Real.sin ((c - a) / 2) := by
  rw [cross_pt_sub]
  have h := sin_add_sub_eq (c - b) (b - a)
  rw [show c - b + (b - a) = c - a from by ring] at h
  rw [h]

/-- The chord length between two circle points. -/
lemma dist_pt (a b : ℝ) : dist (pt a) (pt b) = 2 * |Real.sin ((b - a) / 2)| := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp only [pt_zero, pt_one]
  rw [Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]
  have h : (Real.cos a - Real.cos b) ^ 2 + (Real.sin a - Real.sin b) ^ 2 =
      (2 * Real.sin ((b - a) / 2)) ^ 2 := by
    rw [Real.cos_sub_cos, Real.sin_sub_sin]
    have hs : Real.sin ((a - b) / 2) = -Real.sin ((b - a) / 2) := by
      rw [show (a - b) / 2 = -((b - a) / 2) from by ring, Real.sin_neg]
    rw [hs]
    have h2 := Real.sin_sq ((a + b) / 2)
    linear_combination 4 * Real.sin ((b - a) / 2) ^ 2 * h2
  rw [h, Real.sqrt_sq_eq_abs, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]

/-- The chord length between two circle points, without absolute values. -/
lemma dist_pt_of_le {a b : ℝ} (h0 : 0 ≤ b - a) (h1 : b - a ≤ 2 * π) :
    dist (pt a) (pt b) = 2 * Real.sin ((b - a) / 2) := by
  rw [dist_pt]
  have hs : 0 ≤ Real.sin ((b - a) / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  rw [abs_of_nonneg hs]

/-! ### The strict triangle inequality in the plane -/

/-- The Lagrange identity in dimension two. -/
lemma norm_mul_norm_sub_inner_sq (u v : Plane) :
    ‖u‖ ^ 2 * ‖v‖ ^ 2 - (⟪u, v⟫_ℝ) ^ 2 = (cross u v) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
      Fin.sum_univ_two, Fin.sum_univ_two, PiLp.inner_apply, Fin.sum_univ_two]
  simp only [cross, RCLike.inner_apply, RCLike.conj_to_real]
  ring

/-- The triangle inequality is strict for non-parallel vectors. -/
lemma norm_add_lt_of_cross_ne_zero {u v : Plane} (h : cross u v ≠ 0) :
    ‖u + v‖ < ‖u‖ + ‖v‖ := by
  have hLag : ‖u‖ ^ 2 * ‖v‖ ^ 2 - (⟪u, v⟫_ℝ) ^ 2 = (cross u v) ^ 2 :=
    norm_mul_norm_sub_inner_sq u v
  have hpos : 0 < ‖u‖ ^ 2 * ‖v‖ ^ 2 - (⟪u, v⟫_ℝ) ^ 2 := by
    rw [hLag]
    exact sq_pos_of_ne_zero h
  have hlt : (⟪u, v⟫_ℝ) ^ 2 < ‖u‖ ^ 2 * ‖v‖ ^ 2 := by linarith
  have habs : |⟪u, v⟫_ℝ| < ‖u‖ * ‖v‖ := by
    apply abs_lt_of_sq_lt_sq _ (by positivity)
    rw [mul_pow]
    exact hlt
  have hs : ‖u + v‖ ^ 2 < (‖u‖ + ‖v‖) ^ 2 := by
    rw [norm_add_sq_real, add_sq]
    nlinarith [habs, le_abs_self (⟪u, v⟫_ℝ), norm_nonneg u, norm_nonneg v]
  have := abs_lt_of_sq_lt_sq hs (by positivity)
  rwa [abs_of_nonneg (norm_nonneg _)] at this

/-- The triangle inequality is strict for a point not on the segment. -/
lemma dist_lt_add_of_cross_ne_zero {a x b : Plane} (h : cross (x - a) (b - a) ≠ 0) :
    dist a b < dist a x + dist x b := by
  have hc : cross (x - a) (b - x) ≠ 0 := by
    have e : b - x = b - a - (x - a) := by abel
    rw [e, cross_sub_right, cross_self, sub_zero]
    exact h
  have e2 : b - a = (x - a) + (b - x) := by abel
  rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, norm_sub_rev a b, norm_sub_rev a x,
      norm_sub_rev x b, e2]
  exact norm_add_lt_of_cross_ne_zero hc

/-! ### Adjacent quadrilaterals cannot both have an inscribed circle -/

/-- If A, B, C, D, E are five consecutive vertices of a strictly convex polygon,
then the quadrilaterals ABCD and BCDE cannot both have an inscribed circle.
Indeed, otherwise the two Pitot equalities would give AD + BE = AB + DE, but
the diagonals AD and BE meet at an interior point X, and the strict triangle
inequalities AX + XB > AB and DX + XE > DE give AD + BE > AB + DE. -/
lemma not_adjacent_tangential {a b c d e : Plane}
    (hABE : 0 < cross (b - a) (e - a)) (hABD : 0 < cross (b - a) (d - a))
    (hADE : 0 < cross (d - a) (e - a)) (hBDE : 0 < cross (d - b) (e - b))
    (h1 : TangentialQuad a b c d) (h2 : TangentialQuad b c d e) : False := by
  have hP : dist a d + dist b e = dist a b + dist d e := by
    unfold TangentialQuad at h1 h2
    rw [dist_comm d a, dist_comm e b] at *
    linarith
  have hdenom : 0 < cross (d - a) (e - b) := by
    have e0 : e - b = e - a - (b - a) := by abel
    rw [e0, cross_sub_right]
    have e1 : cross (d - a) (b - a) = -cross (b - a) (d - a) := cross_comm _ _
    linarith [hADE, hABD]
  have hdenom_ne : cross (d - a) (e - b) ≠ 0 := ne_of_gt hdenom
  set t := cross (b - a) (e - b) / cross (d - a) (e - b) with ht
  have ht_num : cross (b - a) (e - b) = cross (b - a) (e - a) := by
    have e1 : e - b = e - a - (b - a) := by abel
    rw [e1, cross_sub_right, cross_self, sub_zero]
  have ht_pos : 0 < t := div_pos (ht_num ▸ hABE) hdenom
  have hd1 : cross (d - a) (e - b) = cross (d - a) (e - a) + cross (b - a) (d - a) := by
    have e0 : e - b = e - a - (b - a) := by abel
    rw [e0, cross_sub_right]
    have e1 : cross (d - a) (b - a) = -cross (b - a) (d - a) := cross_comm _ _
    linarith
  have ht_lt_one : t < 1 := by
    rw [div_lt_one hdenom, ht_num, hd1, cross_plucker a b d e]
    linarith [hBDE]
  set X := a + t • (d - a) with hX
  set s := cross (b - a) (d - a) / cross (d - a) (e - b) with hs
  have hs_pos : 0 < s := div_pos hABD hdenom
  have hs_lt_one : s < 1 := by
    rw [div_lt_one hdenom, hd1]
    linarith [hADE]
  have hX_eq : X = b + s • (e - b) := by
    have w1 : cross (X - b - s • (e - b)) (e - b) = 0 := by
      have e1 : a + t • (d - a) - b = (a - b) + t • (d - a) := by abel
      have e3 : t * cross (d - a) (e - b) = cross (b - a) (e - b) :=
        div_mul_cancel₀ _ hdenom_ne
      rw [cross_sub_left, cross_smul_left, hX, e1, cross_add_left, cross_smul_left,
          cross_self, mul_zero, sub_zero]
      have e2 : cross (a - b) (e - b) = -cross (b - a) (e - b) := by
        have : a - b = -(b - a) := by abel
        rw [this, cross_neg_left]
      rw [e2, e3]
      ring
    have w2 : cross (X - b - s • (e - b)) (d - a) = 0 := by
      have e1 : a + t • (d - a) - b = (a - b) + t • (d - a) := by abel
      have e2 : cross (e - b) (d - a) = -cross (d - a) (e - b) := cross_comm _ _
      have e3 : s * cross (e - b) (d - a) = cross (a - b) (d - a) := by
        rw [hs, e2]
        have e4 : cross (a - b) (d - a) = -cross (b - a) (d - a) := by
          have : a - b = -(b - a) := by abel
          rw [this, cross_neg_left]
        rw [e4]
        field_simp [hdenom_ne]
      rw [cross_sub_left, cross_smul_left, hX, e1, cross_add_left, cross_smul_left,
          cross_self, mul_zero, add_zero, e3]
      ring
    have hXZ : X - b - s • (e - b) = 0 := by
      apply eq_zero_of_cross_left_eq_zero w1 w2
      have e2 : cross (e - b) (d - a) = -cross (d - a) (e - b) := cross_comm _ _
      rw [e2]
      exact neg_ne_zero.mpr hdenom_ne
    have h5 : X - b = s • (e - b) := sub_eq_zero.mp hXZ
    rw [← h5]
    abel
  have hdAD : dist a d = dist a X + dist X d := by
    have e1 : X - a = t • (d - a) := by rw [hX]; abel
    have e2 : d - X = (1 - t) • (d - a) := by rw [hX]; module
    rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, norm_sub_rev a X, norm_sub_rev X d,
        e1, e2, norm_smul, norm_smul, Real.norm_of_nonneg ht_pos.le,
        Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ 1 - t), norm_sub_rev a d]
    ring
  have hdBE : dist b e = dist b X + dist X e := by
    have e1 : X - b = s • (e - b) := by rw [hX_eq]; abel
    have e2 : e - X = (1 - s) • (e - b) := by rw [hX_eq]; module
    rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, norm_sub_rev b X, norm_sub_rev X e,
        e1, e2, norm_smul, norm_smul, Real.norm_of_nonneg hs_pos.le,
        Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ 1 - s), norm_sub_rev b e]
    ring
  have hAB : dist a b < dist a X + dist X b := by
    apply dist_lt_add_of_cross_ne_zero
    have e1 : X - a = t • (d - a) := by rw [hX]; abel
    rw [e1, cross_smul_left]
    have e2 : cross (d - a) (b - a) = -cross (b - a) (d - a) := cross_comm _ _
    rw [e2]
    exact mul_ne_zero (ne_of_gt ht_pos) (by linarith [hABD])
  have hDE : dist d e < dist d X + dist X e := by
    apply dist_lt_add_of_cross_ne_zero
    have e1 : X - d = (1 - t) • (a - d) := by rw [hX]; module
    rw [e1, cross_smul_left]
    have e2 : cross (a - d) (e - d) = -cross (d - a) (e - a) := by
      have e3 : e - d = (e - a) - (d - a) := by abel
      rw [e3, cross_sub_right]
      have e4 : a - d = -(d - a) := by abel
      rw [e4, cross_neg_left, cross_neg_left, cross_self]
      ring
    rw [e2]
    exact mul_ne_zero (by linarith : (1:ℝ) - t ≠ 0) (by linarith [hADE])
  have hsum : dist a d + dist b e = (dist a X + dist X b) + (dist d X + dist X e) := by
    rw [hdAD, hdBE, dist_comm X d, dist_comm b X]
    ring
  linarith [hP, hsum, hAB, hDE]

/-- The natural numbers cast to distinct elements of `ZMod N` when they are
smaller than `N`. -/
lemma zmod_ne_of_lt {N a b : ℕ} [NeZero N] (ha : a < N) (hb : b < N) (hne : a ≠ b) :
    (a : ZMod N) ≠ (b : ZMod N) := by
  intro e
  apply hne
  have h2 : a % N = b % N := ZMod.natCast_eq_natCast_iff a b N |>.mp e
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h2

/-- Adding a nonzero element changes the value. -/
lemma add_ne_self {N : ℕ} {j : ZMod N} {k : ZMod N} (h : k ≠ 0) : j + k ≠ j := by
  intro e
  apply h
  have e2 : j + k = j + 0 := by rw [add_zero]; exact e
  exact add_left_cancel_iff.mp e2

/-- Adding the same element preserves inequality. -/
lemma add_ne_add {N : ℕ} {j : ZMod N} {k l : ZMod N} (h : k ≠ l) : j + k ≠ j + l := by
  intro e
  exact h (add_left_cancel_iff.mp e)

/-- In a convex polygon with at least 5 vertices, two adjacent quadrilaterals
cannot both have an inscribed circle. -/
lemma not_adjacent_of_convex {N : ℕ} [NeZero N] (A : ZMod N → Plane)
    (hconv : ConvexPolygon A) (hN : 5 ≤ N) (i : ZMod N) :
    ¬ (TangentialQuad (A i) (A (i + 1)) (A (i + 2)) (A (i + 3)) ∧
       TangentialQuad (A (i + 1)) (A (i + 2)) (A (i + 3)) (A (i + 4))) := by
  have hN0 : 0 < N := NeZero.pos N
  have h30 : (3 : ZMod N) ≠ 0 := by
    exact_mod_cast zmod_ne_of_lt (show (3 : ℕ) < N by omega) hN0 (by norm_num)
  have h40 : (4 : ZMod N) ≠ 0 := by
    exact_mod_cast zmod_ne_of_lt (show (4 : ℕ) < N by omega) hN0 (by norm_num)
  have h41 : (4 : ZMod N) ≠ 1 := by
    exact_mod_cast zmod_ne_of_lt (show (4 : ℕ) < N by omega)
      (show (1 : ℕ) < N by omega) (by norm_num)
  have h31 : (3 : ZMod N) ≠ 1 := by
    exact_mod_cast zmod_ne_of_lt (show (3 : ℕ) < N by omega)
      (show (1 : ℕ) < N by omega) (by norm_num)
  rintro ⟨h1, h2⟩
  have h5 : (i + 3) + 1 = i + 4 := by ring
  have hABE : 0 < cross (A (i + 1) - A i) (A (i + 4) - A i) :=
    hconv i (i + 4) (add_ne_self h40) (add_ne_add h41)
  have hABD : 0 < cross (A (i + 1) - A i) (A (i + 3) - A i) :=
    hconv i (i + 3) (add_ne_self h30) (add_ne_add h31)
  have hADE : 0 < cross (A (i + 3) - A i) (A (i + 4) - A i) := by
    have h6 := hconv (i + 3) i (add_ne_self h30).symm (by
      rw [h5]
      exact (add_ne_self h40).symm)
    rw [h5] at h6
    rwa [← cross_cyc (A i) (A (i + 3)) (A (i + 4))] at h6
  have hBDE : 0 < cross (A (i + 3) - A (i + 1)) (A (i + 4) - A (i + 1)) := by
    have h6 := hconv (i + 3) (i + 1) (add_ne_add h31.symm) (by
      rw [h5]
      exact add_ne_add h41.symm)
    rw [h5] at h6
    rwa [← cross_cyc (A (i + 1)) (A (i + 3)) (A (i + 4))] at h6
  exact not_adjacent_tangential hABE hABD hADE hBDE h1 h2

/-- A subset of the cycle `ZMod N` containing no two cyclically adjacent
elements has at most `N / 2` elements. -/
lemma card_le_of_no_adjacent {N : ℕ} [NeZero N] (S : Finset (ZMod N))
    (h : ∀ i : ZMod N, ¬ (i ∈ S ∧ (i + 1) ∈ S)) : S.card ≤ N / 2 := by
  have hdisj : Disjoint S (S.image (· + 1)) := by
    rw [Finset.disjoint_left]
    rintro x hx
    rw [Finset.mem_image]
    rintro ⟨y, hy, rfl⟩
    exact h y ⟨hy, hx⟩
  have hcard : (S ∪ S.image (· + 1)).card = 2 * S.card := by
    rw [Finset.card_union_of_disjoint hdisj,
        Finset.card_image_of_injective S (add_left_injective 1)]
    ring
  have hle := Finset.card_le_univ (S ∪ S.image (· + 1))
  rw [hcard, ZMod.card] at hle
  omega

/-- The upper bound: a convex `n`-gon has at most `n / 2` quadrilaterals with
an inscribed circle. -/
lemma numTangential_le {N : ℕ} [NeZero N] (A : ZMod N → Plane)
    (hconv : ConvexPolygon A) (hN : 5 ≤ N) : numTangential A ≤ N / 2 := by
  classical
  apply card_le_of_no_adjacent
  intro i
  rw [Finset.mem_filter, Finset.mem_filter]
  rintro ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
  have h2' : TangentialQuad (A (i + 1)) (A (i + 2)) (A (i + 3)) (A (i + 4)) := by
    have e1 : i + 1 + 1 = i + 2 := by ring
    have e2 : i + 1 + 2 = i + 3 := by ring
    have e3 : i + 1 + 3 = i + 4 := by ring
    rw [e1, e2, e3] at h2
    exact h2
  exact not_adjacent_of_convex A hconv hN i ⟨h1, h2'⟩

/-! ### The construction: shared setup

For the lower bound we construct, for each `n ≥ 5`, a convex `n`-gon with
`n / 2` tangential quadrilaterals.  The construction uses points on the unit
circle alternating between two angular offsets: `V k = (cos kβ, sin kβ)` and
`X k = (cos (kβ + γ), sin (kβ + γ))` where `γ = 2 arctan (sin (β/2))` is
chosen so that every quadrilateral `V k, X k, V (k+1), X (k+1)` is tangential
(this is the relation `sin (γ/2) = sin (β/2) cos (γ/2)`). -/

/-- The angle `γ = 2 arctan (sin (β/2))`. -/
noncomputable def gammaOf (β : ℝ) : ℝ := 2 * Real.arctan (Real.sin (β / 2))

lemma gammaOf_pos {β : ℝ} (hβ0 : 0 < β) (hβπ : β / 2 < π / 2) : 0 < gammaOf β := by
  have hs : 0 < Real.sin (β / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have := Real.arctan_pos.mpr hs
  unfold gammaOf
  linarith

lemma gammaOf_lt {β : ℝ} (hβ0 : 0 < β) (hβπ : β / 2 < π / 2) : gammaOf β < β := by
  have hs : 0 < Real.sin (β / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hcos : 0 < Real.cos (β / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hc : Real.cos (β / 2) < 1 := by
    have h2 := Real.sin_sq (β / 2)
    nlinarith [hs]
  have htan : Real.sin (β / 2) < Real.tan (β / 2) := by
    rw [Real.tan_eq_sin_div_cos, lt_div_iff₀ hcos]
    nlinarith [hs, hc]
  have hmono := Real.arctan_strictMono.lt_iff_lt.mpr htan
  rw [Real.arctan_tan (by linarith) (by linarith)] at hmono
  unfold gammaOf
  linarith [hmono]

/-- The defining relation of `γ`: `sin (γ/2) = sin (β/2) cos (γ/2)`. -/
lemma gammaOf_key (β : ℝ) :
    Real.sin (gammaOf β / 2) = Real.sin (β / 2) * Real.cos (gammaOf β / 2) := by
  have e : gammaOf β / 2 = Real.arctan (Real.sin (β / 2)) := by
    unfold gammaOf
    ring
  rw [e, Real.sin_arctan, Real.cos_arctan, mul_one_div]

/-- "V" vertices on the unit circle. -/
noncomputable def vtxV (β : ℝ) (k : ℕ) : Plane := pt (k * β)

/-- "X" vertices on the unit circle. -/
noncomputable def vtxX (β γ : ℝ) (k : ℕ) : Plane := pt (k * β + γ)

/-- Every quadrilateral formed by four consecutive vertices of the cyclic
chain is tangential. -/
lemma chainQuad_tangential {β γ : ℝ}
    (hγ0 : 0 < γ) (hγβ : γ < β) (hβγ : β + γ ≤ 2 * π)
    (hkey : Real.sin (γ / 2) = Real.sin (β / 2) * Real.cos (γ / 2)) (k : ℕ) :
    TangentialQuad (vtxV β k) (vtxX β γ k) (vtxV β (k + 1)) (vtxX β γ (k + 1)) := by
  have hγ2π : γ ≤ 2 * π := by linarith
  have hβγ0 : 0 < β - γ := by linarith
  have hβγ2π : β - γ ≤ 2 * π := by linarith
  have ed1 : (↑k * β + γ) - ↑k * β = γ := by ring
  have ed2 : (↑(k + 1) * β + γ) - ↑(k + 1) * β = γ := by push_cast; ring
  have ed3 : ↑(k + 1) * β - (↑k * β + γ) = β - γ := by push_cast; ring
  have ed4 : (↑(k + 1) * β + γ) - ↑k * β = β + γ := by push_cast; ring
  have d1 : dist (vtxV β k) (vtxX β γ k) = 2 * Real.sin (γ / 2) := by
    unfold vtxV vtxX
    rw [dist_pt_of_le (by rw [ed1]; linarith) (by rw [ed1]; linarith), ed1]
  have d2 : dist (vtxV β (k + 1)) (vtxX β γ (k + 1)) = 2 * Real.sin (γ / 2) := by
    unfold vtxV vtxX
    rw [dist_pt_of_le (by rw [ed2]; linarith) (by rw [ed2]; linarith), ed2]
  have d3 : dist (vtxX β γ k) (vtxV β (k + 1)) = 2 * Real.sin ((β - γ) / 2) := by
    unfold vtxV vtxX
    rw [dist_pt_of_le (by rw [ed3]; linarith) (by rw [ed3]; linarith), ed3]
  have d4 : dist (vtxX β γ (k + 1)) (vtxV β k) = 2 * Real.sin ((β + γ) / 2) := by
    rw [dist_comm]
    unfold vtxV vtxX
    rw [dist_pt_of_le (by rw [ed4]; linarith) (by rw [ed4]; linarith), ed4]
  unfold TangentialQuad
  rw [d1, d2, d3, d4]
  have hsum : Real.sin ((β - γ) / 2) + Real.sin ((β + γ) / 2) =
      2 * Real.sin (β / 2) * Real.cos (γ / 2) := by
    rw [Real.sin_add_sin]
    have e1 : ((β - γ) / 2 + (β + γ) / 2) / 2 = β / 2 := by ring
    have e2 : ((β - γ) / 2 - (β + γ) / 2) / 2 = -(γ / 2) := by ring
    rw [e1, e2, Real.cos_neg]
  linarith [hkey]

/-- The angle of the `n`-th vertex in the alternating cyclic construction:
`⌊n/2⌋·β` plus `γ` when `n` is odd. -/
noncomputable def angSeq (β γ : ℝ) (n : ℕ) : ℝ :=
  ((n / 2 : ℕ) : ℝ) * β + if n % 2 = 0 then 0 else γ

lemma angSeq_succ {β γ : ℝ} (hγ0 : 0 < γ) (hγβ : γ < β) (n : ℕ) :
    angSeq β γ n < angSeq β γ (n + 1) := by
  unfold angSeq
  by_cases h : n % 2 = 0
  · rw [if_pos h, if_neg (by omega : ¬ (n + 1) % 2 = 0)]
    have h3 : (n + 1) / 2 = n / 2 := by omega
    rw [h3]
    linarith
  · rw [if_neg h, if_pos (by omega : (n + 1) % 2 = 0)]
    have h3 : (n + 1) / 2 = n / 2 + 1 := by omega
    rw [h3, Nat.cast_add, Nat.cast_one]
    linarith

lemma angSeq_strictMono {β γ : ℝ} (hγ0 : 0 < γ) (hγβ : γ < β) :
    StrictMono (angSeq β γ) :=
  strictMono_nat_of_lt_succ (angSeq_succ hγ0 hγβ)

lemma angSeq_even (β γ : ℝ) (k : ℕ) : angSeq β γ (2 * k) = k * β := by
  unfold angSeq
  rw [if_pos (by omega : (2 * k) % 2 = 0)]
  have h2 : (2 * k) / 2 = k := by omega
  rw [h2]
  ring

lemma angSeq_odd (β γ : ℝ) (k : ℕ) : angSeq β γ (2 * k + 1) = k * β + γ := by
  unfold angSeq
  rw [if_neg (by omega : ¬ (2 * k + 1) % 2 = 0)]
  have h2 : (2 * k + 1) / 2 = k := by omega
  rw [h2]

lemma angSeq_add_two_mul {m : ℕ} (hm : 0 < m) (β : ℝ) (hβ : β = 2 * π / m)
    (γ : ℝ) (n : ℕ) :
    angSeq β γ (n + 2 * m) = angSeq β γ n + 2 * π := by
  unfold angSeq
  have h1 : (n + 2 * m) / 2 = n / 2 + m := by omega
  rw [h1, if_congr (by omega : ((n + 2 * m) % 2 = 0) ↔ (n % 2 = 0)) rfl rfl]
  have h3 : (m : ℝ) * β = 2 * π := by
    rw [hβ]
    have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp [hm']
  rw [Nat.cast_add, add_mul, h3]
  ring

/-! ### The even case construction

For `n = 2m` with `m ≥ 3`, take `β = 2π / m` and `γ = gammaOf β`, and let
the polygon alternate between the `V` and `X` vertices: its `i`-th vertex is
`pt (angSeq β γ i)`.  We show that it is strictly convex, that the
quadrilaterals starting at the even positions `2k` (`k < m`) are tangential,
and conclude that the number of tangential quadrilaterals is exactly `m`. -/

/-- `pt` is `2π`-periodic. -/
lemma pt_add_two_pi (θ : ℝ) : pt (θ + 2 * π) = pt θ := by
  unfold pt
  rw [Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- The angle sequence starts at `0`. -/
lemma angSeq_zero (β γ : ℝ) : angSeq β γ 0 = 0 := by
  have h : (0 : ℕ) % 2 = 0 := by norm_num
  unfold angSeq
  rw [if_pos h]
  norm_num

/-- The second angle of the sequence is `γ`. -/
lemma angSeq_one (β γ : ℝ) : angSeq β γ 1 = γ := by
  rw [show (1 : ℕ) = 2 * 0 + 1 from rfl, angSeq_odd β γ 0, Nat.cast_zero, zero_mul,
    zero_add]

/-- Along the angle sequence, an index `b ≤ a + 2m - 1` has angle strictly
less than `angSeq β γ a + 2π` (recall that `β = 2π / m`). -/
lemma angSeq_lt_add_two_pi {m : ℕ} (hm : 0 < m) {β γ : ℝ}
    (hβ : β = 2 * π / m) (hγ0 : 0 < γ) (hγβ : γ < β)
    {a : ℕ} (b : ℕ) (hb : b ≤ a + 2 * m - 1) :
    angSeq β γ b < angSeq β γ a + 2 * π := by
  have hmono : StrictMono (angSeq β γ) := angSeq_strictMono hγ0 hγβ
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hmβ : (m : ℝ) * β = 2 * π := by
    rw [hβ]
    field_simp [hm']
  calc angSeq β γ b ≤ angSeq β γ (a + 2 * m - 1) := hmono.monotone hb
    _ < angSeq β γ a + 2 * π := by
        by_cases ha : a = 0
        · subst ha
          rw [show 0 + 2 * m - 1 = 2 * (m - 1) + 1 from by omega, angSeq_odd,
            angSeq_zero, zero_add]
          have hm1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
          rw [hm1]
          linarith [hmβ, hγβ]
        · rw [show a + 2 * m - 1 = (a - 1) + 2 * m from by omega,
            angSeq_add_two_mul hm β hβ γ (a - 1)]
          have hlt : angSeq β γ (a - 1) < angSeq β γ a := hmono (by omega)
          linarith

/-- The polygon for the even case: its `i`-th vertex is the point at angle
`angSeq β γ i` on the unit circle. -/
noncomputable def evenPoly (m : ℕ) (β γ : ℝ) (i : ZMod (2 * m)) : Plane :=
  pt (angSeq β γ i.val)

lemma evenPoly_apply (m : ℕ) (β γ : ℝ) (i : ZMod (2 * m)) :
    evenPoly m β γ i = pt (angSeq β γ i.val) := rfl

/-- The even-case polygon is strictly convex: the three relevant sine
factors are all positive since the three angular differences lie in
`(0, 2π)`. -/
lemma evenPoly_convex {m : ℕ} (hm : 0 < m) {β γ : ℝ}
    (hβ : β = 2 * π / m) (hγ0 : 0 < γ) (hγβ : γ < β) :
    ConvexPolygon (evenPoly m β γ) := by
  haveI : NeZero (2 * m) := ⟨by omega⟩
  have hmono : StrictMono (angSeq β γ) := angSeq_strictMono hγ0 hγβ
  intro i j hji hji1
  simp only [evenPoly_apply]
  have hi0lt : i.val < 2 * m := ZMod.val_lt i
  have hjlt : j.val < 2 * m := ZMod.val_lt j
  have hvj : j.val ≠ i.val := fun h ↦ hji ((ZMod.val_injective (2 * m)) h)
  have hvj1 : j.val ≠ (i + 1).val := fun h ↦ hji1 ((ZMod.val_injective (2 * m)) h)
  have hi1 : i + 1 = ((i.val + 1 : ℕ) : ZMod (2 * m)) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val i]
    simp only [Nat.cast_add, Nat.cast_one]
  have hi1val : (i + 1).val = (i.val + 1) % (2 * m) := by rw [hi1, ZMod.val_natCast]
  set j' : ℕ := if i.val < j.val then j.val else j.val + 2 * m with hj'def
  have hAi1 : pt (angSeq β γ (i + 1).val) = pt (angSeq β γ (i.val + 1)) := by
    by_cases hc : i.val + 1 < 2 * m
    · rw [hi1val, Nat.mod_eq_of_lt hc]
    · rw [hi1val, show i.val + 1 = 2 * m from by omega, Nat.mod_self,
        show (2 * m : ℕ) = 0 + 2 * m from by omega, angSeq_add_two_mul hm β hβ γ 0]
      exact (pt_add_two_pi _).symm
  have hAj : pt (angSeq β γ j.val) = pt (angSeq β γ j') := by
    rw [hj'def]
    by_cases hc : i.val < j.val
    · rw [if_pos hc]
    · rw [if_neg hc, angSeq_add_two_mul hm β hβ γ j.val]
      exact (pt_add_two_pi _).symm
  have hj'mem : i.val + 2 ≤ j' ∧ j' ≤ i.val + 2 * m - 1 := by
    rw [hj'def]
    by_cases hc : i.val < j.val
    · rw [if_pos hc]
      have hi1v : (i + 1).val = i.val + 1 := by
        rw [hi1val, Nat.mod_eq_of_lt (by omega)]
      have hne : j.val ≠ i.val + 1 := by rw [← hi1v]; exact hvj1
      constructor <;> omega
    · rw [if_neg hc]
      have h2 : j.val < i.val := by omega
      by_cases hi0c : i.val = 2 * m - 1
      · have hi1v : (i + 1).val = 0 := by
          rw [hi1val, show i.val + 1 = 2 * m from by omega, Nat.mod_self]
        have hne : j.val ≠ 0 := by rw [hi1v] at hvj1; exact hvj1
        constructor <;> omega
      · constructor <;> omega
  rw [hAi1, hAj, cross_pt_sub_factor]
  have hb1 : 0 < angSeq β γ (i.val + 1) - angSeq β γ i.val :=
    sub_pos.mpr (hmono (by omega : i.val < i.val + 1))
  have hb2 : 0 < angSeq β γ j' - angSeq β γ (i.val + 1) :=
    sub_pos.mpr (hmono (show i.val + 1 < j' by omega))
  have hb3 : 0 < angSeq β γ j' - angSeq β γ i.val :=
    sub_pos.mpr (hmono (show i.val < j' by omega))
  have hub : angSeq β γ j' - angSeq β γ i.val < 2 * π := by
    have h := angSeq_lt_add_two_pi hm hβ hγ0 hγβ j' hj'mem.2
    linarith
  have s1 : 0 < Real.sin ((angSeq β γ j' - angSeq β γ (i.val + 1)) / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have s2 : 0 < Real.sin ((angSeq β γ (i.val + 1) - angSeq β γ i.val) / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have s3 : 0 < Real.sin ((angSeq β γ j' - angSeq β γ i.val) / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  exact mul_pos (mul_pos (mul_pos (by norm_num) s1) s2) s3

/-- The quadrilateral at an interior even position `2k` (where
`2k + 3 < 2m`) is tangential: it is the chain quadrilateral
`V k, X k, V (k+1), X (k+1)`. -/
lemma evenQuad_tangential_interior {m : ℕ} {β γ : ℝ}
    (hγ0 : 0 < γ) (hγβ : γ < β) (hβγ : β + γ ≤ 2 * π)
    (hkey : Real.sin (γ / 2) = Real.sin (β / 2) * Real.cos (γ / 2))
    {k : ℕ} (hk : 2 * k + 3 < 2 * m) :
    TangentialQuad (evenPoly m β γ ((2 * k : ℕ) : ZMod (2 * m)))
      (evenPoly m β γ (((2 * k : ℕ) : ZMod (2 * m)) + 1))
      (evenPoly m β γ (((2 * k : ℕ) : ZMod (2 * m)) + 2))
      (evenPoly m β γ (((2 * k : ℕ) : ZMod (2 * m)) + 3)) := by
  haveI : NeZero (2 * m) := ⟨by omega⟩
  simp only [evenPoly_apply]
  have v0 : (((2 * k : ℕ) : ZMod (2 * m))).val = 2 * k :=
    ZMod.val_natCast_of_lt (by omega)
  have v1 : (((2 * k : ℕ) : ZMod (2 * m)) + 1).val = 2 * k + 1 := by
    rw [show ((2 * k : ℕ) : ZMod (2 * m)) + 1 = ((2 * k + 1 : ℕ) : ZMod (2 * m)) from by
      rw [Nat.cast_add, Nat.cast_one]]
    exact ZMod.val_natCast_of_lt (by omega)
  have v2 : (((2 * k : ℕ) : ZMod (2 * m)) + 2).val = 2 * k + 2 := by
    rw [show ((2 * k : ℕ) : ZMod (2 * m)) + 2 = ((2 * k + 2 : ℕ) : ZMod (2 * m)) from by
      rw [Nat.cast_add, Nat.cast_ofNat]]
    exact ZMod.val_natCast_of_lt (by omega)
  have v3 : (((2 * k : ℕ) : ZMod (2 * m)) + 3).val = 2 * k + 3 := by
    rw [show ((2 * k : ℕ) : ZMod (2 * m)) + 3 = ((2 * k + 3 : ℕ) : ZMod (2 * m)) from by
      rw [Nat.cast_add, Nat.cast_ofNat]]
    exact ZMod.val_natCast_of_lt (by omega)
  rw [v0, v1, v2, v3, angSeq_even β γ k, angSeq_odd β γ k,
    show 2 * k + 2 = 2 * (k + 1) from by omega, angSeq_even β γ (k + 1),
    show 2 * k + 3 = 2 * (k + 1) + 1 from by omega, angSeq_odd β γ (k + 1)]
  exact chainQuad_tangential hγ0 hγβ hβγ hkey k

/-- The quadrilateral at the wrap-around even position `2(m - 1)`: its
vertices are `V (m-1), X (m-1), V 0, X 0` (indices taken modulo `2m`), and
the Pitot equality reduces to the same identity as for the chain
quadrilaterals. -/
lemma evenQuad_tangential_wrap {m : ℕ} (hm : 0 < m) {β γ : ℝ}
    (hβ : β = 2 * π / m) (hγ0 : 0 < γ) (hγβ : γ < β) (hβγ : β + γ ≤ 2 * π)
    (hkey : Real.sin (γ / 2) = Real.sin (β / 2) * Real.cos (γ / 2)) :
    TangentialQuad (evenPoly m β γ ((2 * (m - 1) : ℕ) : ZMod (2 * m)))
      (evenPoly m β γ (((2 * (m - 1) : ℕ) : ZMod (2 * m)) + 1))
      (evenPoly m β γ (((2 * (m - 1) : ℕ) : ZMod (2 * m)) + 2))
      (evenPoly m β γ (((2 * (m - 1) : ℕ) : ZMod (2 * m)) + 3)) := by
  haveI : NeZero (2 * m) := ⟨by omega⟩
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hmβ : (m : ℝ) * β = 2 * π := by
    rw [hβ]
    field_simp [hm']
  have hβpos : 0 < β := by
    rw [hβ]
    exact div_pos (mul_pos (by norm_num) Real.pi_pos) hmpos
  have hβ2π : β ≤ 2 * π := by
    rw [hβ, div_le_iff₀ hmpos]
    nlinarith [Real.pi_pos, hm1]
  have hM : ((m - 1 : ℕ) : ℝ) * β = 2 * π - β := by
    have hmc : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
    rw [hmc]
    linear_combination hmβ
  have v0 : (((2 * (m - 1) : ℕ) : ZMod (2 * m))).val = 2 * (m - 1) :=
    ZMod.val_natCast_of_lt (by omega)
  have v1 : (((2 * (m - 1) : ℕ) : ZMod (2 * m)) + 1).val = 2 * (m - 1) + 1 := by
    rw [show ((2 * (m - 1) : ℕ) : ZMod (2 * m)) + 1 =
        ((2 * (m - 1) + 1 : ℕ) : ZMod (2 * m)) from by
      rw [Nat.cast_add, Nat.cast_one]]
    exact ZMod.val_natCast_of_lt (by omega)
  have v2 : (((2 * (m - 1) : ℕ) : ZMod (2 * m)) + 2).val = 0 := by
    have e2 : ((2 * (m - 1) : ℕ) : ZMod (2 * m)) + 2 = 0 := by
      rw [show ((2 * (m - 1) : ℕ) : ZMod (2 * m)) + 2 =
          ((2 * (m - 1) + 2 : ℕ) : ZMod (2 * m)) from by
        rw [Nat.cast_add, Nat.cast_ofNat]]
      rw [show 2 * (m - 1) + 2 = 2 * m from by omega]
      exact ZMod.natCast_self _
    rw [e2, ZMod.val_zero]
  have v3 : (((2 * (m - 1) : ℕ) : ZMod (2 * m)) + 3).val = 1 := by
    have e3 : ((2 * (m - 1) : ℕ) : ZMod (2 * m)) + 3 = 1 := by
      rw [show ((2 * (m - 1) : ℕ) : ZMod (2 * m)) + 3 =
          ((2 * (m - 1) + 3 : ℕ) : ZMod (2 * m)) from by
        rw [Nat.cast_add, Nat.cast_ofNat]]
      rw [show 2 * (m - 1) + 3 = 2 * m + 1 from by omega]
      rw [show ((2 * m + 1 : ℕ) : ZMod (2 * m)) = ((2 * m : ℕ) : ZMod (2 * m)) + 1 from by
        rw [Nat.cast_add, Nat.cast_one]]
      rw [ZMod.natCast_self, zero_add]
    rw [e3]
    exact ZMod.val_one'' (by omega : 2 * m ≠ 1)
  simp only [evenPoly_apply]
  rw [v0, v1, v2, v3, angSeq_even β γ (m - 1), angSeq_odd β γ (m - 1), angSeq_zero,
    angSeq_one]
  have e1 : ((m - 1 : ℕ) : ℝ) * β + γ - ((m - 1 : ℕ) : ℝ) * β = γ := by ring
  have d1 : dist (pt (((m - 1 : ℕ) : ℝ) * β)) (pt (((m - 1 : ℕ) : ℝ) * β + γ)) =
      2 * Real.sin (γ / 2) := by
    rw [dist_pt_of_le (by rw [e1]; linarith [hγ0]) (by rw [e1]; linarith [hβγ, hβpos]),
      e1]
  have e2 : γ - 0 = γ := by ring
  have d2 : dist (pt 0) (pt γ) = 2 * Real.sin (γ / 2) := by
    rw [dist_pt_of_le (by rw [e2]; linarith [hγ0]) (by rw [e2]; linarith [hβγ, hβpos]),
      e2]
  have e3 : ((m - 1 : ℕ) : ℝ) * β + γ - 0 = 2 * π - (β - γ) := by rw [hM]; ring
  have d3 : dist (pt (((m - 1 : ℕ) : ℝ) * β + γ)) (pt 0) = 2 * Real.sin ((β - γ) / 2) := by
    rw [dist_comm, dist_pt_of_le (by rw [e3]; linarith [hβ2π, hγ0])
        (by rw [e3]; linarith [hγβ]), e3,
      show (2 * π - (β - γ)) / 2 = π - (β - γ) / 2 from by ring, Real.sin_pi_sub]
  have e4 : ((m - 1 : ℕ) : ℝ) * β - γ = 2 * π - (β + γ) := by rw [hM]; ring
  have d4 : dist (pt γ) (pt (((m - 1 : ℕ) : ℝ) * β)) = 2 * Real.sin ((β + γ) / 2) := by
    rw [dist_pt_of_le (by rw [e4]; linarith [hβγ]) (by rw [e4]; linarith [hβpos, hγ0]),
      e4, show (2 * π - (β + γ)) / 2 = π - (β + γ) / 2 from by ring, Real.sin_pi_sub]
  unfold TangentialQuad
  rw [d1, d2, d3, d4]
  have hsum : Real.sin ((β - γ) / 2) + Real.sin ((β + γ) / 2) =
      2 * Real.sin (β / 2) * Real.cos (γ / 2) := by
    rw [Real.sin_add_sin]
    have f1 : ((β - γ) / 2 + (β + γ) / 2) / 2 = β / 2 := by ring
    have f2 : ((β - γ) / 2 - (β + γ) / 2) / 2 = -(γ / 2) := by ring
    rw [f1, f2, Real.cos_neg]
  linarith [hkey]

/-- The construction for the even case: for `m ≥ 3` there is a strictly
convex `2m`-gon with exactly `m` tangential quadrilaterals. -/
lemma evenConstruction {m : ℕ} (hm : 3 ≤ m) :
    letI : NeZero (2 * m) := ⟨by omega⟩;
    ∃ A : ZMod (2 * m) → Plane, ConvexPolygon A ∧ numTangential A = m := by
  classical
  haveI : NeZero (2 * m) := ⟨by omega⟩
  have hmpos : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hm3 : (3:ℝ) ≤ m := by exact_mod_cast hm
  set β : ℝ := 2 * π / m with hβdef
  have hβpos : 0 < β := by
    rw [hβdef]
    exact div_pos (mul_pos (by norm_num) Real.pi_pos) hmpos
  have hβ2 : β / 2 < π / 2 := by
    rw [hβdef, show 2 * π / m / 2 = π / m from by ring,
      div_lt_div_iff₀ hmpos (by norm_num : (0:ℝ) < 2)]
    nlinarith [Real.pi_pos, hm3]
  have hβle : β ≤ 2 * π / 3 := by
    rw [hβdef, div_le_div_iff₀ hmpos (by norm_num : (0:ℝ) < 3)]
    nlinarith [Real.pi_pos, hm3]
  set γ : ℝ := gammaOf β with hγdef
  have hγ0 : 0 < γ := by rw [hγdef]; exact gammaOf_pos hβpos hβ2
  have hγβ : γ < β := by rw [hγdef]; exact gammaOf_lt hβpos hβ2
  have hβγ : β + γ ≤ 2 * π := by linarith [hβle, hγβ, Real.pi_pos]
  have hkey : Real.sin (γ / 2) = Real.sin (β / 2) * Real.cos (γ / 2) := by
    rw [hγdef]; exact gammaOf_key β
  have hconv : ConvexPolygon (evenPoly m β γ) :=
    evenPoly_convex (by omega) hβdef hγ0 hγβ
  refine ⟨evenPoly m β γ, hconv, ?_⟩
  set P : ZMod (2 * m) → Prop := fun i ↦
    TangentialQuad (evenPoly m β γ i) (evenPoly m β γ (i + 1))
      (evenPoly m β γ (i + 2)) (evenPoly m β γ (i + 3)) with hPdef
  have hnum : numTangential (evenPoly m β γ) = (Finset.univ.filter P).card := rfl
  have htang : ∀ k : ℕ, k < m → P (((2 * k : ℕ) : ZMod (2 * m))) := by
    intro k hk
    by_cases hc : k + 1 < m
    · exact evenQuad_tangential_interior hγ0 hγβ hβγ hkey (by omega)
    · have hkm : k = m - 1 := by omega
      rw [hkm]
      exact evenQuad_tangential_wrap (by omega) hβdef hγ0 hγβ hβγ hkey
  set T : Finset (ZMod (2 * m)) :=
    (Finset.range m).image (fun k : ℕ ↦ ((2 * k : ℕ) : ZMod (2 * m))) with hTdef
  have hinj : Set.InjOn (fun k : ℕ ↦ ((2 * k : ℕ) : ZMod (2 * m))) ↑(Finset.range m) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_range] at ha hb
    have h2 : (2 * a) % (2 * m) = (2 * b) % (2 * m) :=
      (ZMod.natCast_eq_natCast_iff' (2 * a) (2 * b) (2 * m)).mp hab
    rw [Nat.mod_eq_of_lt (by omega : 2 * a < 2 * m),
      Nat.mod_eq_of_lt (by omega : 2 * b < 2 * m)] at h2
    omega
  have hTcard : T.card = m := by
    rw [hTdef, Finset.card_image_of_injOn hinj, Finset.card_range]
  have hsub : T ⊆ Finset.univ.filter P := by
    intro x hx
    rw [hTdef] at hx
    simp only [Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, htang k hk⟩
  have hge : m ≤ numTangential (evenPoly m β γ) := by
    rw [hnum]
    have hcc := Finset.card_le_card hsub
    omega
  have hle : numTangential (evenPoly m β γ) ≤ m := by
    have h := numTangential_le (evenPoly m β γ) hconv (by omega : 5 ≤ 2 * m)
    omega
  exact le_antisymm hle hge

snip end

end Usa1998P6
