/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.Real.Sqrt
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1977, Problem 1

In the interior of the square `ABCD`, equilateral triangles `ABK`, `BCL`,
`CDM`, `DAN` are constructed. Prove that the midpoints of the four segments
`KL`, `LM`, `MN`, `NK` and the midpoints of the eight segments `AK`, `BK`,
`BL`, `CL`, `CM`, `DM`, `DN`, `AN` are the twelve vertices of a regular
dodecagon.

# Formal statement

The configuration is given by a center `O` and two plane vectors `u`, `v` with
`v = rot90 u` and `u ≠ 0`: the square has vertices `A = O + u + v`,
`B = O - u + v`, `C = O - u - v`, `D = O + u - v` (so `u` and `v` are the
half-side vectors), and the apices of the four equilateral triangles are
`K = O + (1 - √3) • v`, `L = O - (1 - √3) • u`, `M = O - (1 - √3) • v`,
`N = O + (1 - √3) • u`. This is exactly the data of the problem: `ABCD` is a
square, and each apex is at distance `(√3 / 2) * |AB|` from the midpoint of the
corresponding side, on the same side as the center `O` (i.e. inside the
square). The counterclockwise labeling of the square is without loss of
generality; the clockwise case is symmetric.

# Solution

Follows the coordinate computation of
https://prase.cz/kalva/imo/isoln/isoln771.html : with `e = 2 - √3` and
`d = (√3 - 1) / 2`, the twelve midpoints are
`O + (1/2, e/2)`, `O + (d, d)`, `O + (e/2, 1/2)`, `O + (-e/2, 1/2)`,
`O + (-d, d)`, `O + (-1/2, e/2)`, `O + (-1/2, -e/2)`, `O + (-d, -d)`,
`O + (-e/2, -1/2)`, `O + (e/2, -1/2)`, `O + (d, -d)`, `O + (1/2, -e/2)`
(in the `(u, v)` basis, in angular order). Each has squared distance
`(2 - √3) * |u|²` from `O`, and each is the rotation of the previous one by
`π/6` about `O`, since `cos (π/6) = √3 / 2` and `sin (π/6) = 1/2`. Hence they
are the vertices of a regular dodecagon.
-/

namespace Imo1977P1

/-- The Euclidean plane, coordinatized as `ℝ²`. -/
abbrev Point := Fin 2 → ℝ

/-- The squared Euclidean norm of a plane vector. -/
def sqNorm (u : Point) : ℝ := u 0 ^ 2 + u 1 ^ 2

/-- The Euclidean distance between two points of the plane. -/
noncomputable def Dist (A B : Point) : ℝ := Real.sqrt (sqNorm (B - A))

/-- Counterclockwise rotation by `π / 2` about the origin. -/
def rot90 (w : Point) : Point := ![-w 1, w 0]

/-- Counterclockwise rotation by `π / 6` about the origin, as a matrix:
`cos (π / 6) = √3 / 2` and `sin (π / 6) = 1 / 2`. -/
noncomputable def rot30 (w : Point) : Point :=
  ![(Real.sqrt 3 * w 0 - w 1) / 2, (w 0 + Real.sqrt 3 * w 1) / 2]

/-- The midpoint of a segment. -/
noncomputable def mid (X Y : Point) : Point := (1 / 2 : ℝ) • (X + Y)

/-- Twelve points `p₀, …, p₁₁`, listed in the given cyclic order, are the
vertices of a regular dodecagon: they all lie on a common circle of positive
radius, and each point is the rotation of the previous one by `π / 6` about
the center. -/
def RegularDodecagon (p₀ p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ : Point) : Prop :=
  ∃ O : Point, ∃ r : ℝ, 0 < r ∧
    Dist O p₀ = r ∧ Dist O p₁ = r ∧ Dist O p₂ = r ∧ Dist O p₃ = r ∧
    Dist O p₄ = r ∧ Dist O p₅ = r ∧ Dist O p₆ = r ∧ Dist O p₇ = r ∧
    Dist O p₈ = r ∧ Dist O p₉ = r ∧ Dist O p₁₀ = r ∧ Dist O p₁₁ = r ∧
    p₁ = O + rot30 (p₀ - O) ∧ p₂ = O + rot30 (p₁ - O) ∧
    p₃ = O + rot30 (p₂ - O) ∧ p₄ = O + rot30 (p₃ - O) ∧
    p₅ = O + rot30 (p₄ - O) ∧ p₆ = O + rot30 (p₅ - O) ∧
    p₇ = O + rot30 (p₆ - O) ∧ p₈ = O + rot30 (p₇ - O) ∧
    p₉ = O + rot30 (p₈ - O) ∧ p₁₀ = O + rot30 (p₉ - O) ∧
    p₁₁ = O + rot30 (p₁₀ - O) ∧ p₀ = O + rot30 (p₁₁ - O)

snip begin

/-- A nonzero plane vector has positive squared norm. -/
lemma sqNorm_pos {u : Point} (hu : u ≠ 0) : 0 < sqNorm u := by
  have hne : u 0 ≠ 0 ∨ u 1 ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨h0, h1⟩ := h
    exact hu (funext fun i => by fin_cases i <;> simp [h0, h1])
  rcases hne with h0 | h1
  · have hp : 0 < u 0 ^ 2 := sq_pos_of_ne_zero h0
    have hq : 0 ≤ u 1 ^ 2 := sq_nonneg _
    simp only [sqNorm]
    linarith
  · have hp : 0 < u 1 ^ 2 := sq_pos_of_ne_zero h1
    have hq : 0 ≤ u 0 ^ 2 := sq_nonneg _
    simp only [sqNorm]
    linarith

/-- The distance from `O` to `O + a • u + b • v` when `v = rot90 u`. -/
lemma dist_combo {O u v : Point} (hv : v = rot90 u) (a b : ℝ) :
    Dist O (O + a • u + b • v) = Real.sqrt ((a ^ 2 + b ^ 2) * sqNorm u) := by
  rw [Dist, add_assoc, add_sub_cancel_left]
  congr 1
  rw [hv]
  simp [sqNorm, rot90, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero]
  ring

/-- If `a² + b² = 2 - √3`, the point `O + a • u + b • v` lies on the circle of
radius `√((2 - √3) * |u|²)` about `O`. -/
lemma dist_eq {O u v : Point} (hv : v = rot90 u) {a b : ℝ}
    (h : a ^ 2 + b ^ 2 = 2 - Real.sqrt 3) :
    Dist O (O + a • u + b • v) = Real.sqrt ((2 - Real.sqrt 3) * sqNorm u) := by
  rw [dist_combo hv, h]

/-- Rotation by `π / 6` in the `(u, rot90 u)` basis. -/
lemma rot30_combo {u v : Point} (hv : v = rot90 u) (a b : ℝ) :
    rot30 (a • u + b • v) =
      ((Real.sqrt 3 * a - b) / 2) • u + ((a + Real.sqrt 3 * b) / 2) • v := by
  rw [hv]
  funext i
  fin_cases i <;> simp [rot30, rot90, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring

/-- One edge of the dodecagon: if `(a', b')` is the rotation of `(a, b)` by
`π / 6` in the `(u, v)` basis, then `O + a' • u + b' • v` is the rotation of
`O + a • u + b • v` by `π / 6` about `O`. -/
lemma step {O u v : Point} (hv : v = rot90 u) {a b a' b' : ℝ}
    (ha : (Real.sqrt 3 * a - b) / 2 = a') (hb : (a + Real.sqrt 3 * b) / 2 = b') :
    O + a' • u + b' • v = O + rot30 ((O + a • u + b • v) - O) := by
  have hsub : (O + a • u + b • v) - O = a • u + b • v := by
    rw [add_assoc, add_sub_cancel_left]
  rw [hsub, add_assoc, rot30_combo hv, ha, hb]

snip end

problem imo1977_p1 (A B C D K L M N O u v : Point)
    (hu : u ≠ 0) (hv : v = rot90 u)
    (hA : A = O + u + v) (hB : B = O - u + v)
    (hC : C = O - u - v) (hD : D = O + u - v)
    (hK : K = O + (1 - Real.sqrt 3) • v) (hL : L = O - (1 - Real.sqrt 3) • u)
    (hM : M = O - (1 - Real.sqrt 3) • v) (hN : N = O + (1 - Real.sqrt 3) • u) :
    RegularDodecagon (mid A K) (mid L M) (mid A N) (mid B L) (mid M N) (mid B K)
      (mid C M) (mid N K) (mid C L) (mid D N) (mid K L) (mid D M) := by
  have h3 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h2m3 : (0 : ℝ) < 2 - Real.sqrt 3 := by
    have h : Real.sqrt 3 < 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
    linarith only [h]
  have hsqu : 0 < sqNorm u := sqNorm_pos hu
  -- The twelve midpoints, expressed in the `(u, v)` basis.
  have eAK : mid A K = O + (1 / 2 : ℝ) • u + ((2 - Real.sqrt 3) / 2 : ℝ) • v := by
    rw [hA, hK]
    funext i
    simp [mid, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have eLM : mid L M = O + ((Real.sqrt 3 - 1) / 2 : ℝ) • u +
      ((Real.sqrt 3 - 1) / 2 : ℝ) • v := by
    rw [hL, hM]
    funext i
    simp [mid, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have eAN : mid A N = O + ((2 - Real.sqrt 3) / 2 : ℝ) • u + (1 / 2 : ℝ) • v := by
    rw [hA, hN]
    funext i
    simp [mid, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have eBL : mid B L = O + (-((2 - Real.sqrt 3) / 2) : ℝ) • u + (1 / 2 : ℝ) • v := by
    rw [hB, hL]
    funext i
    simp [mid, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have eMN : mid M N = O + (-((Real.sqrt 3 - 1) / 2) : ℝ) • u +
      ((Real.sqrt 3 - 1) / 2 : ℝ) • v := by
    rw [hM, hN]
    funext i
    simp [mid, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have eBK : mid B K = O + (-(1 / 2) : ℝ) • u + ((2 - Real.sqrt 3) / 2 : ℝ) • v := by
    rw [hB, hK]
    funext i
    simp [mid, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have eCM : mid C M = O + (-(1 / 2) : ℝ) • u + (-((2 - Real.sqrt 3) / 2) : ℝ) • v := by
    rw [hC, hM]
    funext i
    simp [mid, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have eNK : mid N K = O + (-((Real.sqrt 3 - 1) / 2) : ℝ) • u +
      (-((Real.sqrt 3 - 1) / 2) : ℝ) • v := by
    rw [hN, hK]
    funext i
    simp [mid, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have eCL : mid C L = O + (-((2 - Real.sqrt 3) / 2) : ℝ) • u + (-(1 / 2) : ℝ) • v := by
    rw [hC, hL]
    funext i
    simp [mid, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have eDN : mid D N = O + ((2 - Real.sqrt 3) / 2 : ℝ) • u + (-(1 / 2) : ℝ) • v := by
    rw [hD, hN]
    funext i
    simp [mid, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have eKL : mid K L = O + ((Real.sqrt 3 - 1) / 2 : ℝ) • u +
      (-((Real.sqrt 3 - 1) / 2) : ℝ) • v := by
    rw [hK, hL]
    funext i
    simp [mid, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have eDM : mid D M = O + (1 / 2 : ℝ) • u + (-((2 - Real.sqrt 3) / 2) : ℝ) • v := by
    rw [hD, hM]
    funext i
    simp [mid, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  -- Assemble the dodecagon: common center `O`, radius `√((2 - √3) * |u|²)`.
  refine ⟨O, Real.sqrt ((2 - Real.sqrt 3) * sqNorm u),
    Real.sqrt_pos.mpr (mul_pos h2m3 hsqu), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eAK]
    refine dist_eq hv ?_
    linarith only [h3]
  · rw [eLM]
    refine dist_eq hv ?_
    linarith only [h3]
  · rw [eAN]
    refine dist_eq hv ?_
    linarith only [h3]
  · rw [eBL]
    refine dist_eq hv ?_
    linarith only [h3]
  · rw [eMN]
    refine dist_eq hv ?_
    linarith only [h3]
  · rw [eBK]
    refine dist_eq hv ?_
    linarith only [h3]
  · rw [eCM]
    refine dist_eq hv ?_
    linarith only [h3]
  · rw [eNK]
    refine dist_eq hv ?_
    linarith only [h3]
  · rw [eCL]
    refine dist_eq hv ?_
    linarith only [h3]
  · rw [eDN]
    refine dist_eq hv ?_
    linarith only [h3]
  · rw [eKL]
    refine dist_eq hv ?_
    linarith only [h3]
  · rw [eDM]
    refine dist_eq hv ?_
    linarith only [h3]
  · rw [eLM, eAK]
    refine step hv ?_ ?_ <;> linarith only [h3]
  · rw [eAN, eLM]
    refine step hv ?_ ?_ <;> linarith only [h3]
  · rw [eBL, eAN]
    refine step hv ?_ ?_ <;> linarith only [h3]
  · rw [eMN, eBL]
    refine step hv ?_ ?_ <;> linarith only [h3]
  · rw [eBK, eMN]
    refine step hv ?_ ?_ <;> linarith only [h3]
  · rw [eCM, eBK]
    refine step hv ?_ ?_ <;> linarith only [h3]
  · rw [eNK, eCM]
    refine step hv ?_ ?_ <;> linarith only [h3]
  · rw [eCL, eNK]
    refine step hv ?_ ?_ <;> linarith only [h3]
  · rw [eDN, eCL]
    refine step hv ?_ ?_ <;> linarith only [h3]
  · rw [eKL, eDN]
    refine step hv ?_ ?_ <;> linarith only [h3]
  · rw [eDM, eKL]
    refine step hv ?_ ?_ <;> linarith only [h3]
  · rw [eAK, eDM]
    refine step hv ?_ ?_ <;> linarith only [h3]

end Imo1977P1
