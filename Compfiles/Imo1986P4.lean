/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Real.Sqrt
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Geometry]
  }

/-!
# International Mathematical Olympiad 1986, Problem 4

Let A, B be adjacent vertices of a regular n-gon (n ≥ 5) with center O.
A triangle XYZ, which is congruent to and initially coincides with OAB,
moves in the plane in such a way that Y and Z each trace out the whole
boundary of the polygon, with X remaining inside the polygon. Find the
locus of X.

## Formalization notes

We normalize the circumradius to `1`: the polygon has vertices
`V n k = (cos (2πk/n), sin (2πk/n))`, `k = 0, …, n-1`, on the unit circle,
with center `O = 0`.

During the motion `|YZ| = |AB|` always equals the side length of the polygon,
so `Y` and `Z` lie on two edges adjacent to a common vertex `V` (this holds
for the configuration reached from the initial position `XYZ = OAB`;
conversely every such configuration occurs during the motion, since `Y` and
`Z` each trace out the whole boundary). The locus of `X` is therefore defined
(`LocusConfig`) as the set of points `X` for which there is a vertex `V n k`
and points `Y ∈ [V n k, V n (k+1)]`, `Z ∈ [V n k, V n (k-1)]` with `XYZ`
congruent to `OAB` (i.e. `XY = XZ = OA = 1` and `YZ = AB`) and with `X`
strictly inside the polygon (`InsidePolygon`, expressed via the edge
half-planes: the line through the edge `V n j, V n (j+1)` has equation
`⟪P, V n j + V n (j+1)⟫ = 1 + cos (2π/n)`).

The answer (`locus`) is the "star" of `n` segments emanating from `O`: the
segments from `O` to `(1 - 1/cos (π/n)) • V n k` for `k = 0, …, n-1`, each of
length `(1 - cos (π/n))/cos (π/n)`. The key geometric fact is that while `Y`
and `Z` slide on the two edges adjacent to a vertex `V`, the point `X` stays
on the line `OV` (the angle bisector at `V`, since `XYVZ` is cyclic with
`XY = XZ`): writing `Y = (1-t)V + tV₊` and `Z = (1-u)V + uV₋`, the constraint
`|YZ| = |AB|` is `t² + u² + 2tu·cos(2π/n) = 1`, one checks that
`X = (1 - (t+u)) • V`, and `t + u` ranges over `[1, 1/cos(π/n)]`.
-/

open scoped RealInnerProductSpace

open Real

namespace Imo1986P4

/-- The Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- The `k`-th vertex of the regular `n`-gon inscribed in the unit circle. -/
noncomputable def V (n : ℕ) (k : ℕ) : Pt :=
  !₂[Real.cos (2 * π * k / n), Real.sin (2 * π * k / n)]

/-- Strictly inside the regular `n`-gon: on the interior side of every edge
line. The edge `V n j, V n (j+1)` lies on the line
`⟪P, V n j + V n (j+1)⟫ = 1 + cos (2π/n)`, and the center `0` satisfies the
strict inequality. -/
def InsidePolygon (n : ℕ) (X : Pt) : Prop :=
  ∀ j : ℕ, ⟪X, V n j + V n (j + 1)⟫ < 1 + Real.cos (2 * π / n)

/-- The configuration predicate: `X` is a position of the moving triangle's
apex while `Y`, `Z` slide on the two edges adjacent to the vertex `V n k`,
the triangle `XYZ` being congruent to `OAB` (with `O = 0`, `A = V n 0`,
`B = V n 1`) and `X` strictly inside the polygon. -/
def LocusConfig (n : ℕ) (X : Pt) : Prop :=
  ∃ k : Fin n, ∃ Y Z : Pt,
    Y ∈ segment ℝ (V n k) (V n ((k : ℕ) + 1)) ∧
    Z ∈ segment ℝ (V n k) (V n ((k : ℕ) + n - 1)) ∧
    dist X Y = dist (0 : Pt) (V n 0) ∧
    dist X Z = dist (0 : Pt) (V n 1) ∧
    dist Y Z = dist (V n 0) (V n 1) ∧
    InsidePolygon n X

/-- The locus of `X`: the "star" of `n` segments emanating from the center
`O = 0`, from `O` to `(1 - 1/cos (π/n)) • V n k` for each vertex `V n k`. -/
determine locus (n : ℕ) : Set Pt :=
  ⋃ k : Fin n, segment ℝ 0 ((1 - (Real.cos (π / n))⁻¹) • V n k)

snip begin

-- Solution formalized from https://prase.cz/kalva/imo/isoln/isoln864.html

/-- Points of the plane are determined by their two coordinates. -/
theorem Pt_ext {x y : Pt} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  apply WithLp.ofLp_injective (p := 2)
  funext i
  fin_cases i <;> assumption

/-- Inner product in coordinates. -/
theorem inner_eq (x y : Pt) : ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, RCLike.inner_apply]
  simp only [conj_trivial]
  ring

/-- Rotation by 90 degrees. -/
def rot90 (v : Pt) : Pt := !₂[-(v 1), v 0]

theorem rot90_apply0 (v : Pt) : rot90 v 0 = -(v 1) := rfl

theorem rot90_apply1 (v : Pt) : rot90 v 1 = v 0 := rfl

/-- Equality of nonnegative reals from equality of squares. -/
theorem eq_of_sq_eq_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 = b ^ 2) :
    a = b := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h1 | h1
  · exact h1
  · linarith

/-! ### Basic facts about the angles `2π/n` and `π/n` -/

theorem hnR {n : ℕ} (hn : 5 ≤ n) : (5 : ℝ) ≤ n := Nat.cast_le.mpr hn

theorem nR_pos {n : ℕ} (hn : 5 ≤ n) : (0 : ℝ) < n := by
  have h := hnR hn; linarith

theorem nR_ne {n : ℕ} (hn : 5 ≤ n) : (n : ℝ) ≠ 0 := ne_of_gt (nR_pos hn)

theorem beta_pos {n : ℕ} (hn : 5 ≤ n) : 0 < 2 * π / n :=
  div_pos (by positivity) (nR_pos hn)

theorem beta_le {n : ℕ} (hn : 5 ≤ n) : 2 * π / n ≤ 2 * π / 5 :=
  div_le_div_of_nonneg_left (by positivity) (by norm_num) (hnR hn)

theorem cos_beta_pos {n : ℕ} (hn : 5 ≤ n) : 0 < Real.cos (2 * π / n) := by
  apply Real.cos_pos_of_mem_Ioo
  refine ⟨by linarith [beta_pos hn, Real.pi_pos], ?_⟩
  have h1 := beta_le hn
  have h2 : (2 : ℝ) * π / 5 < π / 2 := by linarith [Real.pi_pos]
  linarith

theorem sin_beta_pos {n : ℕ} (hn : 5 ≤ n) : 0 < Real.sin (2 * π / n) := by
  apply Real.sin_pos_of_pos_of_lt_pi (beta_pos hn)
  have h1 := beta_le hn
  have h2 : (2 : ℝ) * π / 5 < π := by linarith [Real.pi_pos]
  linarith

theorem cos_lt_one_of_sin_pos {x : ℝ} (hs : 0 < Real.sin x) : Real.cos x < 1 := by
  by_contra h
  push_neg at h
  have h1 : (1 : ℝ) * 1 ≤ Real.cos x * Real.cos x :=
    mul_le_mul h h zero_le_one (by linarith)
  have h2 := Real.sin_sq_add_cos_sq x
  have h3 := sq_pos_of_pos hs
  nlinarith

theorem cos_beta_lt_one {n : ℕ} (hn : 5 ≤ n) : Real.cos (2 * π / n) < 1 :=
  cos_lt_one_of_sin_pos (sin_beta_pos hn)

theorem hbeta_pos {n : ℕ} (hn : 5 ≤ n) : 0 < π / n :=
  div_pos Real.pi_pos (nR_pos hn)

theorem hbeta_le {n : ℕ} (hn : 5 ≤ n) : π / n ≤ π / 5 :=
  div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) (hnR hn)

theorem sin_hbeta_pos {n : ℕ} (hn : 5 ≤ n) : 0 < Real.sin (π / n) := by
  apply Real.sin_pos_of_pos_of_lt_pi (hbeta_pos hn)
  have h1 := hbeta_le hn
  linarith [Real.pi_pos]

theorem cos_hbeta_pos {n : ℕ} (hn : 5 ≤ n) : 0 < Real.cos (π / n) := by
  apply Real.cos_pos_of_mem_Ioo
  refine ⟨by linarith [hbeta_pos hn, Real.pi_pos], ?_⟩
  have h1 := hbeta_le hn
  have h2 : π / 5 < π / 2 := by linarith [Real.pi_pos]
  linarith

theorem cos_hbeta_lt_one {n : ℕ} (hn : 5 ≤ n) : Real.cos (π / n) < 1 :=
  cos_lt_one_of_sin_pos (sin_hbeta_pos hn)

theorem cos_pi_div_five_ge : (4 : ℝ) / 5 ≤ Real.cos (π / 5) := by
  rw [Real.cos_pi_div_five]
  have h : (11 : ℝ) / 5 ≤ Real.sqrt 5 := by
    have h1 : ((11 : ℝ) / 5) ^ 2 ≤ 5 := by norm_num
    have h2 := Real.sqrt_le_sqrt h1
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact h2
  nlinarith [h]

theorem cos_hbeta_ge {n : ℕ} (hn : 5 ≤ n) : (4 : ℝ) / 5 ≤ Real.cos (π / n) := by
  have h1 : Real.cos (π / 5) ≤ Real.cos (π / n) := by
    apply Real.cos_le_cos_of_nonneg_of_le_pi (le_of_lt (hbeta_pos hn)) _
      (hbeta_le hn)
    linarith [Real.pi_pos]
  linarith [cos_pi_div_five_ge, h1]

/-! ### Trigonometric identities -/

theorem sin_beta_eq (n : ℕ) :
    Real.sin (2 * π / n) = 2 * Real.sin (π / n) * Real.cos (π / n) := by
  have h := Real.sin_two_mul (π / n)
  rw [show 2 * (π / n) = 2 * π / n by ring] at h
  exact h

theorem cos_beta_sq (n : ℕ) :
    Real.cos (2 * π / n) = 2 * Real.cos (π / n) ^ 2 - 1 := by
  have h := Real.cos_two_mul (π / n)
  rw [show 2 * (π / n) = 2 * π / n by ring] at h
  exact h

theorem cos_beta_sq' (n : ℕ) :
    Real.cos (2 * π / n) = 1 - 2 * Real.sin (π / n) ^ 2 := by
  have h1 := cos_beta_sq n
  have h2 := Real.sin_sq_add_cos_sq (π / n)
  nlinarith [h1, h2]

theorem one_add_cos_beta (n : ℕ) :
    1 + Real.cos (2 * π / n) = 2 * Real.cos (π / n) ^ 2 := by
  have h := cos_beta_sq n
  linarith

theorem two_sin_sq (n : ℕ) :
    2 * Real.sin (π / n) ^ 2 = 1 - Real.cos (2 * π / n) := by
  have h := cos_beta_sq' n
  linarith

/-! ### Facts about the vertices `V n k` -/

theorem V_apply_zero (n k : ℕ) : (V n k) 0 = Real.cos (2 * π * k / n) := rfl

theorem V_apply_one (n k : ℕ) : (V n k) 1 = Real.sin (2 * π * k / n) := rfl

theorem cs_sq_V (n k : ℕ) : (V n k) 0 ^ 2 + (V n k) 1 ^ 2 = 1 :=
  Real.cos_sq_add_sin_sq _

theorem inner_V_self (n k : ℕ) : ⟪V n k, V n k⟫ = 1 := by
  rw [inner_eq, ← sq, ← sq, cs_sq_V]

theorem norm_V (n k : ℕ) : ‖V n k‖ = 1 := by
  apply eq_of_sq_eq_sq (norm_nonneg _) zero_le_one
  rw [← real_inner_self_eq_norm_sq, inner_V_self]
  norm_num

theorem inner_V_V (n a b : ℕ) :
    ⟪V n a, V n b⟫ = Real.cos (2 * π * a / n - 2 * π * b / n) := by
  rw [inner_eq, V_apply_zero, V_apply_one, V_apply_zero, V_apply_one, ← Real.cos_sub]

theorem inner_rot90_V_V (n a b : ℕ) :
    ⟪rot90 (V n a), V n b⟫ = Real.sin (2 * π * b / n - 2 * π * a / n) := by
  rw [inner_eq, rot90_apply0, rot90_apply1, V_apply_zero, V_apply_one, V_apply_zero,
    V_apply_one, Real.sin_sub]
  ring

theorem inner_V_V_succ {n : ℕ} (hn : 5 ≤ n) (k : ℕ) :
    ⟪V n k, V n (k + 1)⟫ = Real.cos (2 * π / n) := by
  rw [inner_V_V]
  push_cast
  rw [show 2 * π * (k : ℝ) / n - 2 * π * ((k : ℝ) + 1) / n = -(2 * π / n) by
    field_simp [nR_ne hn]; ring, Real.cos_neg]

theorem inner_rot90_V_succ {n : ℕ} (hn : 5 ≤ n) (k : ℕ) :
    ⟪rot90 (V n k), V n (k + 1)⟫ = Real.sin (2 * π / n) := by
  rw [inner_rot90_V_V]
  push_cast
  rw [show 2 * π * ((k : ℝ) + 1) / n - 2 * π * (k : ℝ) / n = 2 * π / n by
    field_simp [nR_ne hn]; ring]

theorem cast_kn_sub_one {n : ℕ} (hn : 5 ≤ n) (k : ℕ) :
    ((k + n - 1 : ℕ) : ℝ) = (k : ℝ) + n - 1 := by
  rw [Nat.cast_sub (show 1 ≤ k + n by omega), Nat.cast_add, Nat.cast_one]

theorem inner_V_V_pred {n : ℕ} (hn : 5 ≤ n) (k : ℕ) :
    ⟪V n k, V n (k + n - 1)⟫ = Real.cos (2 * π / n) := by
  rw [inner_V_V, cast_kn_sub_one hn]
  rw [show 2 * π * (k : ℝ) / n - 2 * π * ((k : ℝ) + n - 1) / n = -(2 * π - 2 * π / n) by
    field_simp [nR_ne hn]; ring]
  rw [Real.cos_neg, Real.cos_two_pi_sub]

theorem inner_rot90_V_pred {n : ℕ} (hn : 5 ≤ n) (k : ℕ) :
    ⟪rot90 (V n k), V n (k + n - 1)⟫ = -Real.sin (2 * π / n) := by
  rw [inner_rot90_V_V, cast_kn_sub_one hn]
  rw [show 2 * π * ((k : ℝ) + n - 1) / n - 2 * π * (k : ℝ) / n = 2 * π - 2 * π / n by
    field_simp [nR_ne hn]; ring]
  rw [Real.sin_two_pi_sub]

theorem V_period {n : ℕ} (hn : 5 ≤ n) (k : ℕ) : V n (k + n) = V n k := by
  have h : 2 * π * ((k : ℝ) + n) / n = 2 * π * k / n + 2 * π := by
    field_simp [nR_ne hn]
  apply Pt_ext
  · show Real.cos (2 * π * ↑(k + n) / ↑n) = Real.cos (2 * π * ↑k / ↑n)
    rw [Nat.cast_add, h]
    exact Real.cos_add_two_pi _
  · show Real.sin (2 * π * ↑(k + n) / ↑n) = Real.sin (2 * π * ↑k / ↑n)
    rw [Nat.cast_add, h]
    exact Real.sin_add_two_pi _

theorem V_zero (n : ℕ) : V n 0 = !₂[1, 0] := by
  apply Pt_ext
  · show Real.cos (2 * π * (0 : ℕ) / n) = 1
    simp
  · show Real.sin (2 * π * (0 : ℕ) / n) = 0
    simp

theorem dist_zero_V (n k : ℕ) : dist (0 : Pt) (V n k) = 1 := by
  rw [dist_eq_norm, zero_sub, norm_neg, norm_V]

theorem inner_rot90_self (v : Pt) : ⟪rot90 v, v⟫ = 0 := by
  rw [inner_eq, rot90_apply0, rot90_apply1]
  ring

theorem inner_rot90_right (v w : Pt) : ⟪v, rot90 w⟫ = -⟪rot90 v, w⟫ := by
  rw [inner_eq, inner_eq, rot90_apply0, rot90_apply1, rot90_apply0, rot90_apply1]
  ring

theorem inner_W_rot90_self (v : Pt) : ⟪v, rot90 v⟫ = 0 := by
  rw [inner_rot90_right, inner_rot90_self, neg_zero]

theorem inner_rot90_rot90 (v w : Pt) : ⟪rot90 v, rot90 w⟫ = ⟪v, w⟫ := by
  rw [inner_eq, inner_eq, rot90_apply0, rot90_apply1, rot90_apply0, rot90_apply1]
  ring

theorem rot90_rot90 (v : Pt) : rot90 (rot90 v) = -v := Pt_ext rfl rfl

theorem norm_sq_rot90 (v : Pt) : ‖rot90 v‖ ^ 2 = ‖v‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, inner_rot90_rot90]

theorem norm_rot90 (v : Pt) : ‖rot90 v‖ = ‖v‖ :=
  eq_of_sq_eq_sq (norm_nonneg _) (norm_nonneg _) (norm_sq_rot90 v)

/-! ### The orthonormal basis `(V n k, rot90 (V n k))` -/

theorem norm_sq_basis (n k : ℕ) (P : Pt) :
    ‖P‖ ^ 2 = ⟪V n k, P⟫ ^ 2 + ⟪rot90 (V n k), P⟫ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_eq, inner_eq, inner_eq, rot90_apply0,
    rot90_apply1]
  linear_combination -(P 0 ^ 2 + P 1 ^ 2) * cs_sq_V n k

theorem dist_sq_basis (n k : ℕ) (P Q : Pt) :
    (dist P Q) ^ 2 = (⟪V n k, P⟫ - ⟪V n k, Q⟫) ^ 2 +
      (⟪rot90 (V n k), P⟫ - ⟪rot90 (V n k), Q⟫) ^ 2 := by
  rw [dist_eq_norm, norm_sq_basis n k (P - Q), inner_sub_right, inner_sub_right]

theorem eq_basis (n k : ℕ) (P : Pt) :
    P = ⟪V n k, P⟫ • V n k + ⟪rot90 (V n k), P⟫ • rot90 (V n k) := by
  apply Pt_ext
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, inner_eq, rot90_apply0,
      rot90_apply1]
    linear_combination -(P 0) * cs_sq_V n k
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, inner_eq, rot90_apply0,
      rot90_apply1]
    linear_combination -(P 1) * cs_sq_V n k

theorem eq_of_inner_eq (n k : ℕ) {P Q : Pt} (h1 : ⟪V n k, P⟫ = ⟪V n k, Q⟫)
    (h2 : ⟪rot90 (V n k), P⟫ = ⟪rot90 (V n k), Q⟫) : P = Q := by
  rw [eq_basis n k P, eq_basis n k Q, h1, h2]

theorem eq_smul_rot90_of_inner_eq_zero {v w : Pt} (hw : w ≠ 0) (h : ⟪v, w⟫ = 0) :
    ∃ μ : ℝ, v = μ • rot90 w := by
  have hw2 : w 0 ^ 2 + w 1 ^ 2 ≠ 0 := by
    intro hz
    have h0 : w 0 ^ 2 = 0 := by nlinarith [sq_nonneg (w 0), sq_nonneg (w 1)]
    have h1 : w 1 ^ 2 = 0 := by nlinarith [sq_nonneg (w 0), sq_nonneg (w 1)]
    exact hw (Pt_ext ((pow_eq_zero_iff two_ne_zero).mp h0)
      ((pow_eq_zero_iff two_ne_zero).mp h1))
  use (v 1 * w 0 - v 0 * w 1) / (w 0 ^ 2 + w 1 ^ 2)
  rw [inner_eq] at h
  apply Pt_ext
  · simp only [PiLp.smul_apply, smul_eq_mul, rot90_apply0]
    field_simp
    linear_combination (w 0) * h
  · simp only [PiLp.smul_apply, smul_eq_mul, rot90_apply1]
    field_simp
    linear_combination (w 1) * h

/-! ### The two edges adjacent to `V n k` -/

theorem V_succ {n : ℕ} (hn : 5 ≤ n) (k : ℕ) :
    V n (k + 1) = Real.cos (2 * π / n) • V n k +
      Real.sin (2 * π / n) • rot90 (V n k) := by
  apply eq_of_inner_eq n k
  · rw [inner_add_right, inner_smul_right, inner_smul_right, inner_V_self,
      inner_W_rot90_self, inner_V_V_succ hn]
    ring
  · rw [inner_add_right, inner_smul_right, inner_smul_right, inner_rot90_self,
      inner_rot90_rot90, inner_V_self, inner_rot90_V_succ hn]
    ring

theorem V_pred {n : ℕ} (hn : 5 ≤ n) (k : ℕ) :
    V n (k + n - 1) = Real.cos (2 * π / n) • V n k -
      Real.sin (2 * π / n) • rot90 (V n k) := by
  apply eq_of_inner_eq n k
  · rw [inner_V_V_pred hn, inner_sub_right, inner_smul_right, inner_smul_right,
      inner_V_self, inner_W_rot90_self]
    ring
  · rw [inner_rot90_V_pred hn, inner_sub_right, inner_smul_right, inner_smul_right,
      inner_rot90_self, inner_rot90_rot90, inner_V_self]
    ring

/-! ### Coordinates of `Y` and `Z` on the two edges -/

theorem inner_Y {n : ℕ} (hn : 5 ≤ n) (k : ℕ) (t : ℝ) :
    ⟪V n k, (1 - t) • V n k + t • V n (k + 1)⟫ = 1 + t * (Real.cos (2 * π / n) - 1) := by
  rw [inner_add_right, inner_smul_right, inner_smul_right, inner_V_self,
    inner_V_V_succ hn]
  ring

theorem inner_rot90_Y {n : ℕ} (hn : 5 ≤ n) (k : ℕ) (t : ℝ) :
    ⟪rot90 (V n k), (1 - t) • V n k + t • V n (k + 1)⟫ = t * Real.sin (2 * π / n) := by
  rw [inner_add_right, inner_smul_right, inner_smul_right, inner_rot90_self,
    inner_rot90_V_succ hn]
  ring

theorem inner_Z {n : ℕ} (hn : 5 ≤ n) (k : ℕ) (u : ℝ) :
    ⟪V n k, (1 - u) • V n k + u • V n (k + n - 1)⟫ =
      1 + u * (Real.cos (2 * π / n) - 1) := by
  rw [inner_add_right, inner_smul_right, inner_smul_right, inner_V_self,
    inner_V_V_pred hn]
  ring

theorem inner_rot90_Z {n : ℕ} (hn : 5 ≤ n) (k : ℕ) (u : ℝ) :
    ⟪rot90 (V n k), (1 - u) • V n k + u • V n (k + n - 1)⟫ =
      -u * Real.sin (2 * π / n) := by
  rw [inner_add_right, inner_smul_right, inner_smul_right, inner_rot90_self,
    inner_rot90_V_pred hn]
  ring

theorem distYZ_sq {n : ℕ} (hn : 5 ≤ n) (k : ℕ) (t u : ℝ) :
    (dist ((1 - t) • V n k + t • V n (k + 1))
      ((1 - u) • V n k + u • V n (k + n - 1))) ^ 2
      = (t - u) ^ 2 * (1 - Real.cos (2 * π / n)) ^ 2 +
        (t + u) ^ 2 * (Real.sin (2 * π / n)) ^ 2 := by
  rw [dist_sq_basis, inner_Y hn k t, inner_rot90_Y hn k t, inner_Z hn k u,
    inner_rot90_Z hn k u]
  ring

theorem dist_V01_sq (n : ℕ) :
    (dist (V n 0) (V n 1)) ^ 2 = 2 * (1 - Real.cos (2 * π / n)) := by
  rw [dist_eq_norm, ← real_inner_self_eq_norm_sq, inner_eq, PiLp.sub_apply,
    PiLp.sub_apply, V_apply_zero, V_apply_one, V_apply_zero, V_apply_one]
  simp only [Nat.cast_zero, Nat.cast_one, mul_zero, zero_div, Real.cos_zero, Real.sin_zero,
    mul_one]
  have h := Real.cos_sq_add_sin_sq (2 * π / n)
  linear_combination h

theorem dist_V01 {n : ℕ} (hn : 5 ≤ n) : dist (V n 0) (V n 1) = 2 * Real.sin (π / n) := by
  have hsin : 0 < Real.sin (π / n) := sin_hbeta_pos hn
  apply eq_of_sq_eq_sq dist_nonneg (by positivity)
  rw [dist_V01_sq]
  have h := cos_beta_sq' n
  nlinarith [h, hsin]

theorem norm_V_add_V_succ {n : ℕ} (hn : 5 ≤ n) (j : ℕ) :
    ‖V n j + V n (j + 1)‖ = 2 * Real.cos (π / n) := by
  have hcos := cos_hbeta_pos hn
  have hc : ⟪V n (j + 1), V n j⟫ = Real.cos (2 * π / n) := by
    rw [real_inner_comm, inner_V_V_succ hn]
  apply eq_of_sq_eq_sq (norm_nonneg _) (by positivity)
  rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_add_right,
    inner_V_self, inner_V_self, inner_V_V_succ hn, hc]
  have h := cos_beta_sq n
  nlinarith [h, hcos]

/-- The quadratic constraint `t² + u² + 2tu·cos(2π/n) = 1`, from `|YZ| = |AB|`. -/
theorem QC_of_dist {n : ℕ} (hn : 5 ≤ n) (k : ℕ) {t u : ℝ}
    (hYZ : dist ((1 - t) • V n k + t • V n (k + 1))
      ((1 - u) • V n k + u • V n (k + n - 1)) = dist (V n 0) (V n 1)) :
    t ^ 2 + u ^ 2 + 2 * t * u * Real.cos (2 * π / n) = 1 := by
  have h1c : (1 : ℝ) - Real.cos (2 * π / n) ≠ 0 := by
    have h := cos_beta_lt_one hn
    linarith
  have hE : (dist ((1 - t) • V n k + t • V n (k + 1))
      ((1 - u) • V n k + u • V n (k + n - 1))) ^ 2 = (dist (V n 0) (V n 1)) ^ 2 := by
    rw [hYZ]
  rw [distYZ_sq hn k t u, dist_V01_sq] at hE
  have hss : Real.sin (2 * π / n) ^ 2 = 1 - Real.cos (2 * π / n) ^ 2 := by
    have h := Real.sin_sq_add_cos_sq (2 * π / n)
    linarith
  have hK : (1 - Real.cos (2 * π / n)) *
      (2 * (t ^ 2 + u ^ 2 + 2 * t * u * Real.cos (2 * π / n) - 1)) = 0 := by
    linear_combination hE - (t + u) ^ 2 * hss
  rcases mul_eq_zero.mp hK with h | h
  · exact absurd h h1c
  · linarith

theorem QC_to_dist {n : ℕ} (hn : 5 ≤ n) (k : ℕ) {t u : ℝ}
    (hQC : t ^ 2 + u ^ 2 + 2 * t * u * Real.cos (2 * π / n) = 1) :
    dist ((1 - t) • V n k + t • V n (k + 1))
      ((1 - u) • V n k + u • V n (k + n - 1)) = dist (V n 0) (V n 1) := by
  apply eq_of_sq_eq_sq dist_nonneg dist_nonneg
  rw [distYZ_sq hn k t u, dist_V01_sq]
  have hss : Real.sin (2 * π / n) ^ 2 = 1 - Real.cos (2 * π / n) ^ 2 := by
    have h := Real.sin_sq_add_cos_sq (2 * π / n)
    linarith
  linear_combination (1 - Real.cos (2 * π / n)) * (2 * hQC) + (t + u) ^ 2 * hss

/-- The lower bound `1 ≤ t + u`. -/
theorem sigma_ge_one {n : ℕ} (hn : 5 ≤ n) {t u : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u)
    (hQC : t ^ 2 + u ^ 2 + 2 * t * u * Real.cos (2 * π / n) = 1) : 1 ≤ t + u := by
  have hc : Real.cos (2 * π / n) ≤ 1 := Real.cos_le_one _
  have h1 : 1 ≤ (t + u) ^ 2 := by
    nlinarith [hQC, mul_nonneg (mul_nonneg ht hu) (sub_nonneg.mpr hc)]
  by_contra hlt
  push_neg at hlt
  have h2 := pow_lt_one₀ (add_nonneg ht hu) hlt (show (2 : ℕ) ≠ 0 by norm_num)
  linarith

/-- The upper bound `t + u ≤ 1 / cos(π/n)`. -/
theorem sigma_le_sec {n : ℕ} (hn : 5 ≤ n) {t u : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u)
    (hQC : t ^ 2 + u ^ 2 + 2 * t * u * Real.cos (2 * π / n) = 1) :
    t + u ≤ (Real.cos (π / n))⁻¹ := by
  have hcos := cos_hbeta_pos hn
  have key : (1 - Real.cos (2 * π / n)) * (t - u) ^ 2 =
      2 - (t + u) ^ 2 * (1 + Real.cos (2 * π / n)) := by
    linear_combination 2 * hQC
  have h1 : (t + u) ^ 2 * (1 + Real.cos (2 * π / n)) ≤ 2 := by
    have hnn : 0 ≤ (1 - Real.cos (2 * π / n)) * (t - u) ^ 2 :=
      mul_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) (sq_nonneg _)
    linarith [key]
  have hcs2 : Real.cos (π / n) ^ 2 = (1 + Real.cos (2 * π / n)) / 2 := by
    have h := cos_beta_sq n
    linarith
  have hsc : (t + u) * Real.cos (π / n) ≤ 1 := by
    by_contra hlt
    push_neg at hlt
    have hpos : (0 : ℝ) ≤ (t + u) * Real.cos (π / n) := by positivity
    have h2 : (1 : ℝ) < ((t + u) * Real.cos (π / n)) ^ 2 := by
      have h3 : (1 : ℝ) * 1 < ((t + u) * Real.cos (π / n)) * ((t + u) * Real.cos (π / n)) :=
        mul_lt_mul hlt hlt.le (by linarith [hlt]) hpos
      simpa only [pow_two, mul_one] using h3
    nlinarith [h1, hcs2, h2, hpos]
  calc t + u = ((t + u) * Real.cos (π / n)) * (Real.cos (π / n))⁻¹ :=
      (mul_inv_cancel_right₀ hcos.ne' _).symm
    _ ≤ 1 * (Real.cos (π / n))⁻¹ :=
      mul_le_mul_of_nonneg_right hsc (by positivity)
    _ = (Real.cos (π / n))⁻¹ := one_mul _

/-! ### The two candidate positions of `X` -/

theorem dist_X1_Y {n : ℕ} (hn : 5 ≤ n) (k : ℕ) {t u : ℝ}
    (hQC : t ^ 2 + u ^ 2 + 2 * t * u * Real.cos (2 * π / n) = 1) :
    dist ((1 - (t + u)) • V n k) ((1 - t) • V n k + t • V n (k + 1)) = 1 := by
  apply eq_of_sq_eq_sq dist_nonneg zero_le_one
  have inner_X1 : ⟪V n k, (1 - (t + u)) • V n k⟫ = 1 - (t + u) := by
    rw [inner_smul_right, inner_V_self]
    ring
  have inner_rot90_X1 : ⟪rot90 (V n k), (1 - (t + u)) • V n k⟫ = 0 := by
    rw [inner_smul_right, inner_rot90_self]
    ring
  rw [dist_sq_basis, inner_X1, inner_rot90_X1, inner_Y hn k t, inner_rot90_Y hn k t]
  have hss : Real.sin (2 * π / n) ^ 2 = 1 - Real.cos (2 * π / n) ^ 2 := by
    have h := Real.sin_sq_add_cos_sq (2 * π / n)
    linarith
  linear_combination hQC + t ^ 2 * hss

theorem dist_X1_Z {n : ℕ} (hn : 5 ≤ n) (k : ℕ) {t u : ℝ}
    (hQC : t ^ 2 + u ^ 2 + 2 * t * u * Real.cos (2 * π / n) = 1) :
    dist ((1 - (t + u)) • V n k) ((1 - u) • V n k + u • V n (k + n - 1)) = 1 := by
  apply eq_of_sq_eq_sq dist_nonneg zero_le_one
  have inner_X1 : ⟪V n k, (1 - (t + u)) • V n k⟫ = 1 - (t + u) := by
    rw [inner_smul_right, inner_V_self]
    ring
  have inner_rot90_X1 : ⟪rot90 (V n k), (1 - (t + u)) • V n k⟫ = 0 := by
    rw [inner_smul_right, inner_rot90_self]
    ring
  rw [dist_sq_basis, inner_X1, inner_rot90_X1, inner_Z hn k u, inner_rot90_Z hn k u]
  have hss : Real.sin (2 * π / n) ^ 2 = 1 - Real.cos (2 * π / n) ^ 2 := by
    have h := Real.sin_sq_add_cos_sq (2 * π / n)
    linarith
  linear_combination hQC + u ^ 2 * hss

/-- The good candidate `X₁ = (1 - σ) • V n k` is strictly inside the polygon. -/
theorem X1_inside {n : ℕ} (hn : 5 ≤ n) (k : ℕ) {σ : ℝ} (hσ1 : 1 ≤ σ)
    (hσ2 : σ ≤ (Real.cos (π / n))⁻¹) : InsidePolygon n ((1 - σ) • V n k) := by
  intro j
  have hcos := cos_hbeta_pos hn
  have h45 := cos_hbeta_ge hn
  have hnrm : ‖(1 - σ) • V n k‖ = σ - 1 := by
    rw [norm_smul, norm_V, Real.norm_eq_abs, abs_of_nonpos (by linarith : 1 - σ ≤ 0)]
    ring
  have h2 : (1 : ℝ) + Real.cos (2 * π / n) = 2 * Real.cos (π / n) ^ 2 :=
    one_add_cos_beta n
  have hch2 : (16 : ℝ) / 25 ≤ Real.cos (π / n) ^ 2 := by
    have h := mul_le_mul h45 h45 (by norm_num) hcos.le
    nlinarith [h]
  calc ⟪(1 - σ) • V n k, V n j + V n (j + 1)⟫
      ≤ ‖(1 - σ) • V n k‖ * ‖V n j + V n (j + 1)‖ := real_inner_le_norm _ _
    _ = (σ - 1) * (2 * Real.cos (π / n)) := by
        rw [hnrm, norm_V_add_V_succ hn]
    _ ≤ ((Real.cos (π / n))⁻¹ - 1) * (2 * Real.cos (π / n)) :=
        mul_le_mul_of_nonneg_right (by linarith [hσ2]) (by positivity)
    _ = 2 * (1 - Real.cos (π / n)) := by field_simp
    _ < 1 + Real.cos (2 * π / n) := by
        rw [h2]
        nlinarith [hch2, h45, hcos]

/-- The bad candidate `X₂` is outside the polygon (it violates an edge
half-plane at `V n k`). -/
theorem X2_not_inside {n : ℕ} (hn : 5 ≤ n) (k : ℕ) {t u : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u)
    (hQC : t ^ 2 + u ^ 2 + 2 * t * u * Real.cos (2 * π / n) = 1) :
    ¬ InsidePolygon n
      ((1 + (t + u) * Real.cos (2 * π / n)) • V n k +
        ((t - u) * Real.sin (2 * π / n)) • rot90 (V n k)) := by
  intro hIn
  have hc : 0 < Real.cos (2 * π / n) := cos_beta_pos hn
  have hN_plus : V n k + V n (k + 1) =
      (1 + Real.cos (2 * π / n)) • V n k + Real.sin (2 * π / n) • rot90 (V n k) := by
    rw [V_succ hn k]
    module
  have hN_minus : V n (k + n - 1) + V n ((k + n - 1) + 1) =
      (1 + Real.cos (2 * π / n)) • V n k - Real.sin (2 * π / n) • rot90 (V n k) := by
    have e : k + n - 1 + 1 = k + n := by omega
    rw [e, V_period hn k, V_pred hn k]
    module
  have e1 : ⟪(1 + (t + u) * Real.cos (2 * π / n)) • V n k +
        ((t - u) * Real.sin (2 * π / n)) • rot90 (V n k),
      (1 + Real.cos (2 * π / n)) • V n k + Real.sin (2 * π / n) • rot90 (V n k)⟫
      = (1 + (t + u) * Real.cos (2 * π / n)) * (1 + Real.cos (2 * π / n)) +
        (t - u) * Real.sin (2 * π / n) * Real.sin (2 * π / n) := by
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      conj_trivial]
    rw [inner_V_self, inner_rot90_self, inner_W_rot90_self, inner_rot90_rot90,
      inner_V_self]
    ring
  have e2 : ⟪(1 + (t + u) * Real.cos (2 * π / n)) • V n k +
        ((t - u) * Real.sin (2 * π / n)) • rot90 (V n k),
      (1 + Real.cos (2 * π / n)) • V n k - Real.sin (2 * π / n) • rot90 (V n k)⟫
      = (1 + (t + u) * Real.cos (2 * π / n)) * (1 + Real.cos (2 * π / n)) -
        (t - u) * Real.sin (2 * π / n) * Real.sin (2 * π / n) := by
    simp only [inner_add_left, inner_sub_right, inner_smul_left, inner_smul_right,
      conj_trivial]
    rw [inner_V_self, inner_rot90_self, inner_W_rot90_self, inner_rot90_rot90,
      inner_V_self]
    ring
  have hss : Real.sin (2 * π / n) * Real.sin (2 * π / n) =
      1 - Real.cos (2 * π / n) ^ 2 := by
    have h := Real.sin_sq_add_cos_sq (2 * π / n)
    nlinarith [h]
  by_cases htu : u ≤ t
  · -- `X₂` violates the edge `(V n k, V n (k+1))` half-plane.
    have key : 0 < t + u * (2 * Real.cos (2 * π / n) - 1) := by
      by_cases hu0 : u = 0
      · subst hu0
        have ht1 : t = 1 := by
          have h : t ^ 2 = (1 : ℝ) ^ 2 := by nlinarith [hQC]
          exact eq_of_sq_eq_sq ht zero_le_one h
        nlinarith [hc, ht1]
      · have hu' : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
        have e : t + u * (2 * Real.cos (2 * π / n) - 1) =
            (t - u) + 2 * (u * Real.cos (2 * π / n)) := by ring
        rw [e]
        linarith [mul_pos hu' hc, htu]
    have h := hIn k
    rw [hN_plus, e1] at h
    have hpos : (0 : ℝ) < (1 + Real.cos (2 * π / n)) *
        (t + u * (2 * Real.cos (2 * π / n) - 1)) :=
      mul_pos (by linarith [hc]) key
    nlinarith [h, hss, hpos, hc]
  · -- `X₂` violates the edge `(V n (k+n-1), V n k)` half-plane.
    push_neg at htu
    have key : 0 < u + t * (2 * Real.cos (2 * π / n) - 1) := by
      by_cases ht0 : t = 0
      · subst ht0
        have hu1 : u = 1 := by
          have h : u ^ 2 = (1 : ℝ) ^ 2 := by nlinarith [hQC]
          exact eq_of_sq_eq_sq hu zero_le_one h
        nlinarith [hc, hu1]
      · have ht' : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
        have e : u + t * (2 * Real.cos (2 * π / n) - 1) =
            (u - t) + 2 * (t * Real.cos (2 * π / n)) := by ring
        rw [e]
        linarith [mul_pos ht' hc, htu.le]
    have h := hIn (k + n - 1)
    rw [hN_minus, e2] at h
    have hpos : (0 : ℝ) < (1 + Real.cos (2 * π / n)) *
        (u + t * (2 * Real.cos (2 * π / n) - 1)) :=
      mul_pos (by linarith [hc]) key
    nlinarith [h, hss, hpos, hc]

/-! ### Uniqueness of the inside candidate -/

/-- `X` lies on the perpendicular bisector of `YZ`. -/
theorem mid_perp {n : ℕ} (hn : 5 ≤ n) (k : ℕ) {t u : ℝ} {X : Pt}
    (hXY : dist X ((1 - t) • V n k + t • V n (k + 1)) = 1)
    (hXZ : dist X ((1 - u) • V n k + u • V n (k + n - 1)) = 1) :
    ⟪X - (1 / 2 : ℝ) • (((1 - t) • V n k + t • V n (k + 1)) +
        ((1 - u) • V n k + u • V n (k + n - 1))),
      ((1 - u) • V n k + u • V n (k + n - 1)) - ((1 - t) • V n k + t • V n (k + 1))⟫ = 0 := by
  have h : (dist X ((1 - t) • V n k + t • V n (k + 1))) ^ 2 =
      (dist X ((1 - u) • V n k + u • V n (k + n - 1))) ^ 2 := by
    rw [hXY, hXZ]
  simp only [dist_eq_norm, ← real_inner_self_eq_norm_sq] at h
  have e1 : ⟪X - ((1 - t) • V n k + t • V n (k + 1)),
        X - ((1 - t) • V n k + t • V n (k + 1))⟫ =
      ⟪X, X⟫ - 2 * ⟪X, ((1 - t) • V n k + t • V n (k + 1))⟫ +
        ⟪(1 - t) • V n k + t • V n (k + 1), (1 - t) • V n k + t • V n (k + 1)⟫ := by
    simp only [inner_sub_left, inner_sub_right,
      real_inner_comm ((1 - t) • V n k + t • V n (k + 1)) X]
    ring
  have e2 : ⟪X - ((1 - u) • V n k + u • V n (k + n - 1)),
        X - ((1 - u) • V n k + u • V n (k + n - 1))⟫ =
      ⟪X, X⟫ - 2 * ⟪X, ((1 - u) • V n k + u • V n (k + n - 1))⟫ +
        ⟪(1 - u) • V n k + u • V n (k + n - 1),
          (1 - u) • V n k + u • V n (k + n - 1)⟫ := by
    simp only [inner_sub_left, inner_sub_right,
      real_inner_comm ((1 - u) • V n k + u • V n (k + n - 1)) X]
    ring
  rw [e1, e2] at h
  have e3 : ⟪X - (1 / 2 : ℝ) • (((1 - t) • V n k + t • V n (k + 1)) +
        ((1 - u) • V n k + u • V n (k + n - 1))),
      ((1 - u) • V n k + u • V n (k + n - 1)) - ((1 - t) • V n k + t • V n (k + 1))⟫ =
      ⟪X, ((1 - u) • V n k + u • V n (k + n - 1))⟫ -
        ⟪X, ((1 - t) • V n k + t • V n (k + 1))⟫ -
        (1 / 2) * (⟪(1 - u) • V n k + u • V n (k + n - 1),
            (1 - u) • V n k + u • V n (k + n - 1)⟫ -
          ⟪(1 - t) • V n k + t • V n (k + 1), (1 - t) • V n k + t • V n (k + 1)⟫) := by
    have hc : ⟪(1 - u) • V n k + u • V n (k + n - 1),
        (1 - t) • V n k + t • V n (k + 1)⟫ =
        ⟪(1 - t) • V n k + t • V n (k + 1), (1 - u) • V n k + u • V n (k + n - 1)⟫ :=
      real_inner_comm _ _
    simp only [inner_add_left, inner_smul_left, conj_trivial] at hc
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_add_left,
      conj_trivial]
    linarith [hc]
  rw [e3]
  linarith [h]

/-- Vector identity for the good candidate: `(2 sin(π/n)) • (m - X₁) =
cos(π/n) • rot90 (Z - Y)` where `m` is the midpoint of `YZ`. -/
theorem X1_vec_id {n : ℕ} (hn : 5 ≤ n) (k : ℕ) (t u : ℝ) :
    (2 * Real.sin (π / n)) •
        ((1 / 2 : ℝ) • (((1 - t) • V n k + t • V n (k + 1)) +
          ((1 - u) • V n k + u • V n (k + n - 1))) - (1 - (t + u)) • V n k)
      = Real.cos (π / n) • rot90 (((1 - u) • V n k + u • V n (k + n - 1)) -
        ((1 - t) • V n k + t • V n (k + 1))) := by
  have trig1 : Real.cos (π / n) * Real.sin (2 * π / n) =
      (1 + Real.cos (2 * π / n)) * Real.sin (π / n) := by
    rw [sin_beta_eq]
    have h := cos_beta_sq n
    linear_combination -Real.sin (π / n) * h
  apply eq_of_inner_eq n k
  · simp only [inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right,
      inner_add_left, inner_add_right, inner_rot90_right, inner_neg_left, rot90_rot90,
      conj_trivial, inner_V_self, inner_V_V_succ hn, inner_V_V_pred hn,
      inner_rot90_self, inner_rot90_V_succ hn, inner_rot90_V_pred hn,
      inner_W_rot90_self]
    linear_combination -(t + u) * trig1
  · simp only [inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right,
      inner_add_left, inner_add_right, inner_rot90_right, inner_neg_left, rot90_rot90,
      conj_trivial, inner_V_self, inner_V_V_succ hn, inner_V_V_pred hn,
      inner_rot90_self, inner_rot90_V_succ hn, inner_rot90_V_pred hn,
      inner_W_rot90_self, inner_rot90_rot90]
    linear_combination (t - u) * Real.sin (π / n) * sin_beta_eq n +
      (t - u) * Real.cos (π / n) * two_sin_sq n

/-- Vector identity for the bad candidate: `(2 sin(π/n)) • (X₂ - m) =
cos(π/n) • rot90 (Z - Y)`. -/
theorem X2_vec_id {n : ℕ} (hn : 5 ≤ n) (k : ℕ) (t u : ℝ) :
    (2 * Real.sin (π / n)) •
        (((1 + (t + u) * Real.cos (2 * π / n)) • V n k +
          ((t - u) * Real.sin (2 * π / n)) • rot90 (V n k)) -
        (1 / 2 : ℝ) • (((1 - t) • V n k + t • V n (k + 1)) +
          ((1 - u) • V n k + u • V n (k + n - 1))))
      = Real.cos (π / n) • rot90 (((1 - u) • V n k + u • V n (k + n - 1)) -
        ((1 - t) • V n k + t • V n (k + 1))) := by
  have trig1 : Real.cos (π / n) * Real.sin (2 * π / n) =
      (1 + Real.cos (2 * π / n)) * Real.sin (π / n) := by
    rw [sin_beta_eq]
    have h := cos_beta_sq n
    linear_combination -Real.sin (π / n) * h
  apply eq_of_inner_eq n k
  · simp only [inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right,
      inner_add_left, inner_add_right, inner_rot90_right, inner_neg_left, rot90_rot90,
      conj_trivial, inner_V_self, inner_V_V_succ hn, inner_V_V_pred hn,
      inner_rot90_self, inner_rot90_V_succ hn, inner_rot90_V_pred hn,
      inner_W_rot90_self]
    linear_combination -(t + u) * trig1
  · simp only [inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right,
      inner_add_left, inner_add_right, inner_rot90_right, inner_neg_left, rot90_rot90,
      conj_trivial, inner_V_self, inner_V_V_succ hn, inner_V_V_pred hn,
      inner_rot90_self, inner_rot90_V_succ hn, inner_rot90_V_pred hn,
      inner_W_rot90_self, inner_rot90_rot90]
    linear_combination (t - u) * Real.sin (π / n) * sin_beta_eq n +
      (t - u) * Real.cos (π / n) * two_sin_sq n

/-- Any `X` with `XY = XZ = 1` is one of the two candidates. -/
theorem candidates {n : ℕ} (hn : 5 ≤ n) (k : ℕ) {t u : ℝ} {X : Pt}
    (hYZ : dist ((1 - t) • V n k + t • V n (k + 1))
      ((1 - u) • V n k + u • V n (k + n - 1)) = dist (V n 0) (V n 1))
    (hXY : dist X ((1 - t) • V n k + t • V n (k + 1)) = 1)
    (hXZ : dist X ((1 - u) • V n k + u • V n (k + n - 1)) = 1) :
    X = (1 - (t + u)) • V n k ∨
      X = (1 + (t + u) * Real.cos (2 * π / n)) • V n k +
        ((t - u) * Real.sin (2 * π / n)) • rot90 (V n k) := by
  have hsin : 0 < Real.sin (π / n) := sin_hbeta_pos hn
  have h2s : (2 : ℝ) * Real.sin (π / n) ≠ 0 := by positivity
  have hYZ' : dist ((1 - t) • V n k + t • V n (k + 1))
      ((1 - u) • V n k + u • V n (k + n - 1)) = 2 * Real.sin (π / n) := by
    rw [hYZ, dist_V01 hn]
  have hZY_ne : ((1 - u) • V n k + u • V n (k + n - 1)) -
      ((1 - t) • V n k + t • V n (k + 1)) ≠ 0 := by
    intro h
    have h' : (1 - u) • V n k + u • V n (k + n - 1) =
        (1 - t) • V n k + t • V n (k + 1) := sub_eq_zero.mp h
    rw [h', dist_self] at hYZ'
    linarith [hsin]
  obtain ⟨μ, hμ⟩ := eq_smul_rot90_of_inner_eq_zero hZY_ne (mid_perp hn k hXY hXZ)
  have hperp : ⟪X - (1 / 2 : ℝ) • (((1 - t) • V n k + t • V n (k + 1)) +
        ((1 - u) • V n k + u • V n (k + n - 1))),
      (1 / 2 : ℝ) • (((1 - t) • V n k + t • V n (k + 1)) +
        ((1 - u) • V n k + u • V n (k + n - 1))) -
        ((1 - t) • V n k + t • V n (k + 1))⟫ = 0 := by
    have hmm : (1 / 2 : ℝ) • (((1 - t) • V n k + t • V n (k + 1)) +
          ((1 - u) • V n k + u • V n (k + n - 1))) -
        ((1 - t) • V n k + t • V n (k + 1)) =
        (1 / 2 : ℝ) • (((1 - u) • V n k + u • V n (k + n - 1)) -
          ((1 - t) • V n k + t • V n (k + 1))) := by
      module
    rw [hmm, inner_smul_right, mid_perp hn k hXY hXZ, mul_zero]
  have hP : ‖X - ((1 - t) • V n k + t • V n (k + 1))‖ ^ 2 =
      ‖X - (1 / 2 : ℝ) • (((1 - t) • V n k + t • V n (k + 1)) +
          ((1 - u) • V n k + u • V n (k + n - 1)))‖ ^ 2 +
        ‖(1 / 2 : ℝ) • (((1 - t) • V n k + t • V n (k + 1)) +
          ((1 - u) • V n k + u • V n (k + n - 1))) -
          ((1 - t) • V n k + t • V n (k + 1))‖ ^ 2 := by
    have e1 : X - ((1 - t) • V n k + t • V n (k + 1)) =
        (X - (1 / 2 : ℝ) • (((1 - t) • V n k + t • V n (k + 1)) +
          ((1 - u) • V n k + u • V n (k + n - 1)))) +
        ((1 / 2 : ℝ) • (((1 - t) • V n k + t • V n (k + 1)) +
          ((1 - u) • V n k + u • V n (k + n - 1))) -
          ((1 - t) • V n k + t • V n (k + 1))) := by
      abel
    have e2 : ⟪X - ((1 - t) • V n k + t • V n (k + 1)),
          X - ((1 - t) • V n k + t • V n (k + 1))⟫ =
        ⟪X - (1 / 2 : ℝ) • (((1 - t) • V n k + t • V n (k + 1)) +
          ((1 - u) • V n k + u • V n (k + n - 1))),
          X - (1 / 2 : ℝ) • (((1 - t) • V n k + t • V n (k + 1)) +
            ((1 - u) • V n k + u • V n (k + n - 1)))⟫ +
        ⟪(1 / 2 : ℝ) • (((1 - t) • V n k + t • V n (k + 1)) +
          ((1 - u) • V n k + u • V n (k + n - 1))) -
          ((1 - t) • V n k + t • V n (k + 1)),
          (1 / 2 : ℝ) • (((1 - t) • V n k + t • V n (k + 1)) +
            ((1 - u) • V n k + u • V n (k + n - 1))) -
            ((1 - t) • V n k + t • V n (k + 1))⟫ := by
      rw [e1]
      have hc : ⟪(1 / 2 : ℝ) • (((1 - t) • V n k + t • V n (k + 1)) +
            ((1 - u) • V n k + u • V n (k + n - 1))) -
            ((1 - t) • V n k + t • V n (k + 1)),
          X - (1 / 2 : ℝ) • (((1 - t) • V n k + t • V n (k + 1)) +
            ((1 - u) • V n k + u • V n (k + n - 1)))⟫ = 0 := by
        have h1 : ⟪(1 / 2 : ℝ) • (((1 - t) • V n k + t • V n (k + 1)) +
              ((1 - u) • V n k + u • V n (k + n - 1))) -
              ((1 - t) • V n k + t • V n (k + 1)),
            X - (1 / 2 : ℝ) • (((1 - t) • V n k + t • V n (k + 1)) +
              ((1 - u) • V n k + u • V n (k + n - 1)))⟫ =
            ⟪X - (1 / 2 : ℝ) • (((1 - t) • V n k + t • V n (k + 1)) +
              ((1 - u) • V n k + u • V n (k + n - 1))),
            (1 / 2 : ℝ) • (((1 - t) • V n k + t • V n (k + 1)) +
              ((1 - u) • V n k + u • V n (k + n - 1))) -
              ((1 - t) • V n k + t • V n (k + 1))⟫ :=
          real_inner_comm _ _
        rw [h1, hperp]
      simp only [inner_add_left, inner_add_right]
      linarith [hperp, hc]
    simp only [real_inner_self_eq_norm_sq] at e2
    exact e2
  have hmY : ‖(1 / 2 : ℝ) • (((1 - t) • V n k + t • V n (k + 1)) +
        ((1 - u) • V n k + u • V n (k + n - 1))) -
        ((1 - t) • V n k + t • V n (k + 1))‖ ^ 2 = Real.sin (π / n) ^ 2 := by
    have hmm : (1 / 2 : ℝ) • (((1 - t) • V n k + t • V n (k + 1)) +
          ((1 - u) • V n k + u • V n (k + n - 1))) -
        ((1 - t) • V n k + t • V n (k + 1)) =
        (1 / 2 : ℝ) • (((1 - u) • V n k + u • V n (k + n - 1)) -
          ((1 - t) • V n k + t • V n (k + 1))) := by
      module
    rw [hmm, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← dist_eq_norm, dist_comm, hYZ']
    ring
  have hXY2 : ‖X - ((1 - t) • V n k + t • V n (k + 1))‖ ^ 2 = 1 := by
    rw [← dist_eq_norm, hXY]
    norm_num
  have hn1 : ‖X - (1 / 2 : ℝ) • (((1 - t) • V n k + t • V n (k + 1)) +
        ((1 - u) • V n k + u • V n (k + n - 1)))‖ ^ 2 = Real.cos (π / n) ^ 2 := by
    have h := Real.sin_sq_add_cos_sq (π / n)
    linarith [hP, hmY, hXY2]
  have hμsq : (μ * (2 * Real.sin (π / n))) ^ 2 = Real.cos (π / n) ^ 2 := by
    have e1 : ‖X - (1 / 2 : ℝ) • (((1 - t) • V n k + t • V n (k + 1)) +
          ((1 - u) • V n k + u • V n (k + n - 1)))‖ =
        |μ| * ‖((1 - u) • V n k + u • V n (k + n - 1)) -
          ((1 - t) • V n k + t • V n (k + 1))‖ := by
      rw [hμ, norm_smul, norm_rot90, Real.norm_eq_abs]
    have e2 : ‖((1 - u) • V n k + u • V n (k + n - 1)) -
          ((1 - t) • V n k + t • V n (k + 1))‖ = 2 * Real.sin (π / n) := by
      rw [show ‖((1 - u) • V n k + u • V n (k + n - 1)) -
          ((1 - t) • V n k + t • V n (k + 1))‖ =
          dist ((1 - u) • V n k + u • V n (k + n - 1))
            ((1 - t) • V n k + t • V n (k + 1)) from (dist_eq_norm _ _).symm,
        dist_comm, hYZ']
    have e3 : ‖X - (1 / 2 : ℝ) • (((1 - t) • V n k + t • V n (k + 1)) +
          ((1 - u) • V n k + u • V n (k + n - 1)))‖ ^ 2 =
        (|μ| * (2 * Real.sin (π / n))) ^ 2 := by
      rw [e1, e2]
    rw [mul_pow, sq_abs, ← mul_pow] at e3
    rw [hn1] at e3
    exact e3.symm
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hμsq with h | h
  · right
    have key := X2_vec_id hn k t u
    have e1 : (2 * Real.sin (π / n)) •
        (X - (1 / 2 : ℝ) • (((1 - t) • V n k + t • V n (k + 1)) +
          ((1 - u) • V n k + u • V n (k + n - 1)))) =
        (2 * Real.sin (π / n)) •
        ((1 + (t + u) * Real.cos (2 * π / n)) • V n k +
          ((t - u) * Real.sin (2 * π / n)) • rot90 (V n k) -
          (1 / 2 : ℝ) • (((1 - t) • V n k + t • V n (k + 1)) +
            ((1 - u) • V n k + u • V n (k + n - 1)))) := by
      rw [hμ, smul_smul, mul_comm (2 * Real.sin (π / n)) μ, h, key]
    have e2 : X - (1 / 2 : ℝ) • (((1 - t) • V n k + t • V n (k + 1)) +
          ((1 - u) • V n k + u • V n (k + n - 1))) =
        (1 + (t + u) * Real.cos (2 * π / n)) • V n k +
          ((t - u) * Real.sin (2 * π / n)) • rot90 (V n k) -
          (1 / 2 : ℝ) • (((1 - t) • V n k + t • V n (k + 1)) +
            ((1 - u) • V n k + u • V n (k + n - 1))) := by
      have hh := congrArg (fun v : Pt => ((2 * Real.sin (π / n))⁻¹ : ℝ) • v) e1
      rwa [smul_smul, smul_smul, inv_mul_cancel₀ h2s, one_smul, one_smul] at hh
    have h4 : X = X - (1 / 2 : ℝ) • (((1 - t) • V n k + t • V n (k + 1)) +
          ((1 - u) • V n k + u • V n (k + n - 1))) +
        (1 / 2 : ℝ) • (((1 - t) • V n k + t • V n (k + 1)) +
          ((1 - u) • V n k + u • V n (k + n - 1))) := by
      abel
    rw [h4, e2]
    abel
  · left
    have key := X1_vec_id hn k t u
    have e1 : (2 * Real.sin (π / n)) •
        (X - (1 / 2 : ℝ) • (((1 - t) • V n k + t • V n (k + 1)) +
          ((1 - u) • V n k + u • V n (k + n - 1)))) =
        (2 * Real.sin (π / n)) •
        ((1 - (t + u)) • V n k -
          (1 / 2 : ℝ) • (((1 - t) • V n k + t • V n (k + 1)) +
            ((1 - u) • V n k + u • V n (k + n - 1)))) := by
      rw [hμ, smul_smul, mul_comm (2 * Real.sin (π / n)) μ, h, neg_smul, ← key,
        ← smul_neg, neg_sub]
    have e2 : X - (1 / 2 : ℝ) • (((1 - t) • V n k + t • V n (k + 1)) +
          ((1 - u) • V n k + u • V n (k + n - 1))) =
        (1 - (t + u)) • V n k -
          (1 / 2 : ℝ) • (((1 - t) • V n k + t • V n (k + 1)) +
            ((1 - u) • V n k + u • V n (k + n - 1))) := by
      have hh := congrArg (fun v : Pt => ((2 * Real.sin (π / n))⁻¹ : ℝ) • v) e1
      rwa [smul_smul, smul_smul, inv_mul_cancel₀ h2s, one_smul, one_smul] at hh
    have h4 : X = X - (1 / 2 : ℝ) • (((1 - t) • V n k + t • V n (k + 1)) +
          ((1 - u) • V n k + u • V n (k + n - 1))) +
        (1 / 2 : ℝ) • (((1 - t) • V n k + t • V n (k + 1)) +
          ((1 - u) • V n k + u • V n (k + n - 1))) := by
      abel
    rw [h4, e2]
    abel

/-- The inside candidate is `X₁ = (1 - (t+u)) • V n k`. -/
theorem eq_X1 {n : ℕ} (hn : 5 ≤ n) (k : ℕ) {t u : ℝ} {X : Pt} (ht : 0 ≤ t) (hu : 0 ≤ u)
    (hQC : t ^ 2 + u ^ 2 + 2 * t * u * Real.cos (2 * π / n) = 1)
    (hYZ : dist ((1 - t) • V n k + t • V n (k + 1))
      ((1 - u) • V n k + u • V n (k + n - 1)) = dist (V n 0) (V n 1))
    (hXY : dist X ((1 - t) • V n k + t • V n (k + 1)) = 1)
    (hXZ : dist X ((1 - u) • V n k + u • V n (k + n - 1)) = 1)
    (hIn : InsidePolygon n X) :
    X = (1 - (t + u)) • V n k := by
  rcases candidates hn k hYZ hXY hXZ with h | h
  · exact h
  · exfalso
    rw [h] at hIn
    exact X2_not_inside hn k ht hu hQC hIn

snip end

/-- The locus of `X` is the star of `n` segments from `O`. -/
problem imo1986_p4 (n : ℕ) (hn : 5 ≤ n) :
    {X : Pt | LocusConfig n X} = locus n := by
  ext X
  constructor
  · intro hX
    obtain ⟨k, Y, Z, hY, hZ, hXY, hXZ, hYZ, hIn⟩ := hX
    rw [segment_eq_image] at hY hZ
    obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hY
    obtain ⟨u, ⟨hu0, hu1⟩, rfl⟩ := hZ
    rw [dist_zero_V] at hXY hXZ
    have hQC := QC_of_dist hn k hYZ
    have hσ1 := sigma_ge_one hn ht0 hu0 hQC
    have hσ2 := sigma_le_sec hn ht0 hu0 hQC
    have hXe := eq_X1 hn k ht0 hu0 hQC hYZ hXY hXZ hIn
    show X ∈ ⋃ k : Fin n, segment ℝ 0 ((1 - (Real.cos (π / n))⁻¹) • V n k)
    rw [Set.mem_iUnion]
    refine ⟨k, ?_⟩
    rw [segment_eq_image]
    have hsec : (0 : ℝ) < (Real.cos (π / n))⁻¹ - 1 := by
      have h1 := cos_hbeta_lt_one hn
      have h2 := (one_lt_inv₀ (cos_hbeta_pos hn)).mpr h1
      linarith
    refine ⟨(t + u - 1) / ((Real.cos (π / n))⁻¹ - 1), ⟨?_, ?_⟩, ?_⟩
    · exact div_nonneg (by linarith) hsec.le
    · rw [div_le_one hsec]
      linarith [hσ2]
    · show (1 - (t + u - 1) / ((Real.cos (π / n))⁻¹ - 1)) • (0 : Pt) +
          ((t + u - 1) / ((Real.cos (π / n))⁻¹ - 1)) •
            ((1 - (Real.cos (π / n))⁻¹) • V n k) = X
      rw [smul_zero, zero_add, smul_smul]
      have e : (t + u - 1) / ((Real.cos (π / n))⁻¹ - 1) * (1 - (Real.cos (π / n))⁻¹) =
          1 - (t + u) := by
        field_simp [hsec.ne']
        ring
      rw [e]
      exact hXe.symm
  · intro hX
    show LocusConfig n X
    change X ∈ ⋃ k : Fin n, segment ℝ 0 ((1 - (Real.cos (π / n))⁻¹) • V n k) at hX
    rw [Set.mem_iUnion] at hX
    obtain ⟨k, hseg⟩ := hX
    rw [segment_eq_image] at hseg
    obtain ⟨θ, ⟨hθ0, hθ1⟩, hX⟩ := hseg
    simp only [smul_zero, zero_add, smul_smul] at hX
    have hsin : 0 < Real.sin (π / n) := sin_hbeta_pos hn
    have hsin2 : (0 : ℝ) < Real.sin (π / n) ^ 2 := by positivity
    have hch : 0 < Real.cos (π / n) := cos_hbeta_pos hn
    have hsec : (0 : ℝ) < (Real.cos (π / n))⁻¹ - 1 := by
      have h1 := cos_hbeta_lt_one hn
      have h2 := (one_lt_inv₀ hch).mpr h1
      linarith
    set σ := 1 + θ * ((Real.cos (π / n))⁻¹ - 1) with hσdef
    have hσ1 : 1 ≤ σ := by
      have h := mul_nonneg hθ0 hsec.le
      rw [hσdef]
      linarith
    have hσ2 : σ ≤ (Real.cos (π / n))⁻¹ := by
      have h := mul_le_mul_of_nonneg_right hθ1 hsec.le
      rw [hσdef]
      linarith
    have hXe : X = (1 - σ) • V n k := by
      rw [← hX, hσdef]
      congr 1
      ring
    have hσc : σ * Real.cos (π / n) ≤ 1 := by
      calc σ * Real.cos (π / n) ≤ (Real.cos (π / n))⁻¹ * Real.cos (π / n) :=
          mul_le_mul_of_nonneg_right hσ2 hch.le
        _ = 1 := inv_mul_cancel₀ hch.ne'
    set D := σ ^ 2 - (σ ^ 2 - 1) / Real.sin (π / n) ^ 2 with hDdef
    have hDe : D * Real.sin (π / n) ^ 2 = 1 - (σ * Real.cos (π / n)) ^ 2 := by
      have h1 : (σ ^ 2 - 1) / Real.sin (π / n) ^ 2 * Real.sin (π / n) ^ 2 = σ ^ 2 - 1 :=
        div_mul_cancel₀ _ hsin2.ne'
      have h2 := Real.sin_sq_add_cos_sq (π / n)
      rw [hDdef]
      linear_combination -h1 + σ ^ 2 * h2
    have hD : 0 ≤ D := by
      by_contra hlt
      push_neg at hlt
      have h1 : D * Real.sin (π / n) ^ 2 < 0 := mul_neg_of_neg_of_pos hlt hsin2
      rw [hDe] at h1
      have hσc2 : (σ * Real.cos (π / n)) ^ 2 ≤ 1 := by
        have h0 : (0 : ℝ) ≤ σ * Real.cos (π / n) := mul_nonneg (by linarith [hσ1]) hch.le
        have h2 := mul_le_mul hσc hσc h0 zero_le_one
        nlinarith [h2]
      nlinarith [hσc2]
    set t := (σ + Real.sqrt D) / 2 with htdef
    set u := (σ - Real.sqrt D) / 2 with hudef
    have ht0 : 0 ≤ t := by
      rw [htdef]
      have h := Real.sqrt_nonneg D
      linarith [hσ1]
    have hu0 : 0 ≤ u := by
      rw [hudef]
      have h1 : Real.sqrt D ≤ σ := by
        have h2 : D ≤ σ ^ 2 := by
          rw [hDdef]
          have e : (0 : ℝ) ≤ (σ ^ 2 - 1) / Real.sin (π / n) ^ 2 :=
            div_nonneg (by nlinarith [hσ1]) hsin2.le
          linarith
        calc Real.sqrt D ≤ Real.sqrt (σ ^ 2) := Real.sqrt_le_sqrt h2
          _ = σ := Real.sqrt_sq (by linarith [hσ1])
      linarith [Real.sqrt_nonneg D]
    have h2σ : (0 : ℝ) ≤ 2 - σ := by
      have h45 := cos_hbeta_ge hn
      have h54 : (Real.cos (π / n))⁻¹ ≤ (5 : ℝ) / 4 := by
        have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4 / 5) h45
        rw [one_div, one_div, inv_div] at h
        norm_num at h
        exact h
      linarith [hσ2, h54]
    have ht1 : t ≤ 1 := by
      rw [htdef]
      have h1 : Real.sqrt D ≤ 2 - σ := by
        have h2 : D ≤ (2 - σ) ^ 2 := by
          have hcb := cos_beta_pos hn
          have h2ss : Real.sin (π / n) ^ 2 ≤ 1 / 2 := by
            have h := two_sin_sq n
            linarith [hcb]
          have e2 : 4 * (σ - 1) ≤ (σ ^ 2 - 1) / Real.sin (π / n) ^ 2 := by
            rw [le_div_iff₀ hsin2]
            have hprod : (0 : ℝ) ≤ (σ - 1) * (σ + 1 - 4 * Real.sin (π / n) ^ 2) :=
              mul_nonneg (by linarith [hσ1]) (by nlinarith [hσ1, h2ss])
            nlinarith [hprod]
          rw [hDdef]
          nlinarith [e2, hσ1]
        calc Real.sqrt D ≤ Real.sqrt ((2 - σ) ^ 2) := Real.sqrt_le_sqrt h2
          _ = 2 - σ := Real.sqrt_sq h2σ
      linarith [Real.sqrt_nonneg D, h1]
    have hu1 : u ≤ 1 := by
      have hut : u ≤ t := by
        rw [htdef, hudef]
        linarith [Real.sqrt_nonneg D]
      linarith [ht1]
    have htus : t + u = σ := by
      rw [htdef, hudef]
      ring
    have htu2 : t * u = (σ ^ 2 - D) / 4 := by
      rw [htdef, hudef]
      have hD2 : Real.sqrt D ^ 2 = D := Real.sq_sqrt hD
      linear_combination -hD2 / 4
    have hQC : t ^ 2 + u ^ 2 + 2 * t * u * Real.cos (2 * π / n) = 1 := by
      have e1 : t ^ 2 + u ^ 2 + 2 * t * u * Real.cos (2 * π / n) =
          (t + u) ^ 2 - 2 * (t * u) * (1 - Real.cos (2 * π / n)) := by
        ring
      rw [e1, htus, htu2, ← two_sin_sq n]
      have e2 : σ ^ 2 - 2 * ((σ ^ 2 - D) / 4) * (2 * Real.sin (π / n) ^ 2) =
          σ ^ 2 - (σ ^ 2 - D) * Real.sin (π / n) ^ 2 := by
        ring
      rw [e2]
      have h2 := Real.sin_sq_add_cos_sq (π / n)
      linear_combination hDe - σ ^ 2 * h2
    show ∃ k : Fin n, ∃ Y Z : Pt,
      Y ∈ segment ℝ (V n k) (V n ((k : ℕ) + 1)) ∧
      Z ∈ segment ℝ (V n k) (V n ((k : ℕ) + n - 1)) ∧
      dist X Y = dist (0 : Pt) (V n 0) ∧
      dist X Z = dist (0 : Pt) (V n 1) ∧
      dist Y Z = dist (V n 0) (V n 1) ∧
      InsidePolygon n X
    refine ⟨k, (1 - t) • V n (k : ℕ) + t • V n ((k : ℕ) + 1),
      (1 - u) • V n (k : ℕ) + u • V n ((k : ℕ) + n - 1), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [segment_eq_image]
      exact ⟨t, ⟨ht0, ht1⟩, rfl⟩
    · rw [segment_eq_image]
      exact ⟨u, ⟨hu0, hu1⟩, rfl⟩
    · rw [dist_zero_V, hXe, ← htus]
      exact dist_X1_Y hn k hQC
    · rw [dist_zero_V, hXe, ← htus]
      exact dist_X1_Z hn k hQC
    · exact QC_to_dist hn k hQC
    · rw [hXe]
      exact X1_inside hn k hσ1 hσ2

end Imo1986P4
