/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 2014, Problem 3

Convex quadrilateral `ABCD` has `∠ABC = ∠CDA = 90°`. Point `H` is the foot of the
perpendicular from `A` to `BD`. Points `S` and `T` lie on sides `AB` and `AD`,
respectively, such that `H` lies inside triangle `SCT` and

  `∠CHS − ∠CSB = 90°`,
  `∠THC − ∠DTC = 90°`.

Prove that line `BD` is tangent to the circumcircle of triangle `TSH`.
-/

namespace Imo2014P3

open scoped EuclideanGeometry

open EuclideanGeometry Affine

snip begin

/-!
## Part I: standard coordinates and the algebraic core

The computational heart of the problem (verified symbolically with SymPy and
numerically before formalizing). Place

  `H = (0,0)`, `A = (0,a)`, `B = (b,0)`, `D = (d,0)`, `C = (b+d, bd/a)`

(the last is *forced*: `∠ABC = ∠CDA = 90°` says that `B` and `D` lie on the circle
with diameter `AC`, whose intersections with line `BD` satisfy `x² − c₁x + ac₂ = 0`,
so `c₁ = b + d` and `c₂ = bd/a`). Write `T = (td, a(1−t))` and `S = (sb, a(1−s))`.

* The condition `∠THC − ∠DTC = 90°` (via the equivalent statement "the circumcenter
  of `△CTH` lies on line `AD`", Evan Chen's claim) is the polynomial
  `Qt a b d t = 0` below, and similarly `∠CHS − ∠CSB = 90°` is `Qt a d b s = 0`.
* If `P = (0,p)` is the intersection of line `AH` with the perpendicular bisector of
  `TH`, then `W = ap` satisfies `W(1−t) = |T|²/2`; eliminating `t` gives the quadratic
  `σf a b d W = 0`, whose coefficients are **symmetric in `b` and `d`**
  (`σf = 4a²b²d²W² + 2MN·W − a²MN` with `M = a²(b−d)² + b²d²`, `N = a²(b+d)² + b²d²`).
  The same computation on the `S`-side gives the *same* quadratic, and since `σf`
  has one positive and one negative root while both candidates for `W` are positive,
  they agree: `p = q`. Then the circle centered at `P = (0,p)` through `H` also
  passes through `T` and `S`, and its radius `PH` is vertical, hence perpendicular
  to `BD` (the x-axis): tangency at `H`.
-/

/-- Coordinate helper: the point of `EuclideanSpace ℝ (Fin 2)` with given coordinates. -/
def pt (x y : ℝ) : EuclideanSpace ℝ (Fin 2) := (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![x, y]

@[simp] theorem pt_zero (x y : ℝ) : (pt x y) 0 = x := by
  simp [pt, WithLp.equiv_symm_apply]

@[simp] theorem pt_one (x y : ℝ) : (pt x y) 1 = y := by
  simp [pt, WithLp.equiv_symm_apply]

theorem inner_pt (x₁ y₁ x₂ y₂ : ℝ) :
    inner ℝ (pt x₁ y₁) (pt x₂ y₂) = x₁ * x₂ + y₁ * y₂ := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp [RCLike.inner_apply]
  ring

/-- The polynomial form of the angle condition at `T` (and, with `b` and `d`
swapped, at `S`): `a²d²t² − (a²b² + a²d² + b²d²)t + a²b²`. -/
def Qt (a b d t : ℝ) : ℝ :=
  a^2 * d^2 * t^2 - (a^2*b^2 + a^2*d^2 + b^2*d^2) * t + a^2*b^2

/-- Half the squared norm of `T = (td, a(1−t))`. -/
noncomputable def K1 (a d t : ℝ) : ℝ := (t^2 * d^2 + a^2 * (1 - t)^2) / 2

/-- First symmetric factor `a²(b−d)² + b²d²` of the eliminant's coefficients. -/
def Mf (a b d : ℝ) : ℝ := a^2 * (b - d)^2 + b^2 * d^2

/-- Second symmetric factor `a²(b+d)² + b²d²` of the eliminant's coefficients. -/
def Nf (a b d : ℝ) : ℝ := a^2 * (b + d)^2 + b^2 * d^2

/-- The eliminant: `4a²b²d²W² + 2MN·W − a²MN`, symmetric in `b` and `d`. -/
def σf (a b d W : ℝ) : ℝ :=
  4 * a^2*b^2*d^2 * W^2 + 2 * Mf a b d * Nf a b d * W - a^2 * Mf a b d * Nf a b d

/-- Elimination of `t` from `Qt a b d t = 0` and `W(1−t) = |T|²/2` (`T`-side):
the result `(1−t)²·σf = 0` is a polynomial combination of the two inputs
(cofactors produced by a Gröbner basis computation). -/
theorem elim_T {a b d t W : ℝ} (hQ : Qt a b d t = 0) (hW : W * (1 - t) = K1 a d t) :
    (1 - t)^2 * σf a b d W = 0 := by
  simp only [Qt, K1, Mf, Nf, σf] at hQ hW ⊢
  linear_combination
    (a^4*b^2*t^2 - a^4*b^2*t - a^4*d^2*t + a^4*d^2 + 2*a^2*b^2*d^2*t^2 - 2*a^2*b^2*d^2*t
     - a^2*d^4*t + b^2*d^4*t^2 - b^2*d^4*t) * hQ +
    (-4*W*a^2*b^2*d^2*t + 4*W*a^2*b^2*d^2 - 2*a^4*b^4*t + 2*a^4*b^4 + 2*a^4*b^2*d^2*t^2
     - 2*a^4*b^2*d^2 - 2*a^4*d^4*t + 2*a^4*d^4 - 4*a^2*b^4*d^2*t + 4*a^2*b^4*d^2
     + 2*a^2*b^2*d^4*t^2 - 4*a^2*b^2*d^4*t + 4*a^2*b^2*d^4 - 2*b^4*d^4*t + 2*b^4*d^4) * hW

/-- The eliminant relation, with the nonzero factor `(1−t)²` removed. -/
theorem sigma_zero_of {a b d t W : ℝ} (ht : t ≠ 1) (hQ : Qt a b d t = 0)
    (hW : W * (1 - t) = K1 a d t) : σf a b d W = 0 := by
  have h := elim_T hQ hW
  have hne : (1 - t)^2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr ht.symm)
  exact (mul_eq_zero.mp h).resolve_left hne

/-- The eliminant is symmetric in `b` and `d`. -/
theorem sigma_symm (a b d W : ℝ) : σf a d b W = σf a b d W := by
  simp only [σf, Mf, Nf]; ring

/-- Elimination on the `S`-side gives the same symmetric quadratic. -/
theorem elim_S {a b d s W : ℝ} (hQ : Qt a d b s = 0) (hW : W * (1 - s) = K1 a b s) :
    (1 - s)^2 * σf a b d W = 0 := by
  have h := elim_T (a := a) (b := d) (d := b) (t := s) (W := W) hQ hW
  rwa [sigma_symm] at h

/-- The `S`-side eliminant relation, with `(1−s)²` removed. -/
theorem sigma_zero_of_S {a b d s W : ℝ} (hs : s ≠ 1) (hQ : Qt a d b s = 0)
    (hW : W * (1 - s) = K1 a b s) : σf a b d W = 0 := by
  have h := elim_S hQ hW
  have hne : (1 - s)^2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hs.symm)
  exact (mul_eq_zero.mp h).resolve_left hne

theorem Mf_pos {a b d : ℝ} (hb : b ≠ 0) (hd : d ≠ 0) : 0 < Mf a b d := by
  have hbd : 0 < b^2 * d^2 := by nlinarith [mul_self_pos.mpr hb, mul_self_pos.mpr hd]
  simp only [Mf]
  nlinarith [mul_self_nonneg (a * (b - d))]

theorem Nf_pos {a b d : ℝ} (hb : b ≠ 0) (hd : d ≠ 0) : 0 < Nf a b d := by
  have hbd : 0 < b^2 * d^2 := by nlinarith [mul_self_pos.mpr hb, mul_self_pos.mpr hd]
  simp only [Nf]
  nlinarith [mul_self_nonneg (a * (b + d))]

/-- Two positive roots of `σf` agree: `σf W₁ − σf W₂` factors as
`(W₁ − W₂)(4a²b²d²(W₁+W₂) + 2MN)`, and the second factor is strictly positive. -/
theorem sigma_eq_of_pos {a b d : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0)
    {W₁ W₂ : ℝ} (h₁ : σf a b d W₁ = 0) (h₂ : σf a b d W₂ = 0)
    (hp₁ : 0 < W₁) (hp₂ : 0 < W₂) : W₁ = W₂ := by
  have hM : 0 < Mf a b d := Mf_pos hb hd
  have hN : 0 < Nf a b d := Nf_pos hb hd
  have habd : 0 < a^2 * b^2 * d^2 := by
    have h1 := mul_self_pos.mpr ha
    have h2 := mul_self_pos.mpr hb
    have h3 := mul_self_pos.mpr hd
    nlinarith [mul_pos (mul_pos h1 h2) h3]
  by_contra hne
  have hsub : σf a b d W₁ - σf a b d W₂ = 0 := by rw [h₁, h₂, sub_zero]
  have hfactored : σf a b d W₁ - σf a b d W₂
      = (W₁ - W₂) * (4 * a^2*b^2*d^2 * (W₁ + W₂) + 2 * Mf a b d * Nf a b d) := by
    simp only [σf]; ring
  rw [hfactored] at hsub
  have hfac : 4 * a^2*b^2*d^2 * (W₁ + W₂) + 2 * Mf a b d * Nf a b d = 0 :=
    (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hne)
  have hpos : 0 < 4 * a^2*b^2*d^2 * (W₁ + W₂) + 2 * Mf a b d * Nf a b d := by
    have h12 : 0 < W₁ + W₂ := add_pos hp₁ hp₂
    nlinarith [mul_pos habd h12, mul_pos hM hN]
  linarith

/-!
## Part II: the model theorem in standard coordinates

Everything below in this section is proved: it is the "downstream" half of the
argument, starting from the polynomial conditions `Qt a b d t = 0`, `Qt a d b s = 0`.
-/

/-- The model theorem: in standard coordinates, the polynomial angle conditions
imply that line `BD` (the x-axis) is tangent at `H` to a circle through `T`, `S`, `H`. -/
theorem model_tangency {a b d s t : ℝ} (ha : 0 < a) (hb : b ≠ 0) (hd : d ≠ 0)
    (ht₁ : t < 1) (hs₁ : s < 1)
    (hQt : Qt a b d t = 0) (hQs : Qt a d b s = 0) :
    ∃ (O : EuclideanSpace ℝ (Fin 2)) (r : ℝ), 0 < r ∧
      dist O (pt (t * d) (a * (1 - t))) = r ∧
      dist O (pt (s * b) (a * (1 - s))) = r ∧
      dist O (pt 0 0) = r ∧
      inner ℝ (O - pt 0 0) (pt d 0 - pt b 0) = 0 := by
  have h1t : (0:ℝ) < 1 - t := by linarith
  have h1s : (0:ℝ) < 1 - s := by linarith
  have hane : a ≠ 0 := ha.ne'
  have hK1t : 0 < K1 a d t := by
    simp only [K1]
    nlinarith [mul_self_pos.mpr (mul_ne_zero hane (sub_ne_zero.mpr (ne_of_lt ht₁).symm)),
      mul_self_nonneg (t * d)]
  have hK1s : 0 < K1 a b s := by
    simp only [K1]
    nlinarith [mul_self_pos.mpr (mul_ne_zero hane (sub_ne_zero.mpr (ne_of_lt hs₁).symm)),
      mul_self_nonneg (s * b)]
  -- `P = (0, p)` on line `AH` with `PT = PH`; `Q = (0, q)` on line `AH` with `QS = QH`.
  set p := K1 a d t / (a * (1 - t)) with hp_def
  set q := K1 a b s / (a * (1 - s)) with hq_def
  have hp_pos : 0 < p := div_pos hK1t (mul_pos ha h1t)
  have hq_pos : 0 < q := div_pos hK1s (mul_pos ha h1s)
  have hWp : a * p * (1 - t) = K1 a d t := by
    rw [hp_def]; field_simp
  have hWq : a * q * (1 - s) = K1 a b s := by
    rw [hq_def]; field_simp
  -- Both `ap` and `aq` are positive roots of the same symmetric quadratic `σf`.
  have hσp : σf a b d (a * p) = 0 :=
    sigma_zero_of (ne_of_lt ht₁) hQt hWp
  have hσq : σf a b d (a * q) = 0 :=
    sigma_zero_of_S (ne_of_lt hs₁) hQs hWq
  have hpq : a * p = a * q :=
    sigma_eq_of_pos hane hb hd hσp hσq (mul_pos ha hp_pos) (mul_pos ha hq_pos)
  have hpq' : p = q := mul_left_cancel₀ hane hpq
  -- The circle centered at `O = (0, p)` with radius `p`.
  refine ⟨pt 0 p, p, hp_pos, ?_, ?_, ?_, ?_⟩
  · -- `dist O T = p`, using `a·p·(1−t) = |T|²/2`.
    have hinside : dist (pt 0 p) (pt (t * d) (a * (1 - t))) = Real.sqrt (p^2) := by
      rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
      simp only [pt_zero, pt_one, Real.dist_eq, sq_abs]
      congr 1
      simp only [K1] at hWp
      nlinarith [hWp]
    rw [hinside, Real.sqrt_sq hp_pos.le]
  · -- `dist O S = p`, using `a·q·(1−s) = |S|²/2` and `p = q`.
    have hinside : dist (pt 0 p) (pt (s * b) (a * (1 - s))) = Real.sqrt (p^2) := by
      rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
      simp only [pt_zero, pt_one, Real.dist_eq, sq_abs]
      congr 1
      simp only [K1] at hWq
      nlinarith [hWq, hpq']
    rw [hinside, Real.sqrt_sq hp_pos.le]
  · -- `dist O H = p`.
    have hinside : dist (pt 0 p) (pt 0 0) = Real.sqrt (p^2) := by
      rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
      simp only [pt_zero, pt_one, Real.dist_eq, sq_abs]
      congr 1
      simp
    rw [hinside, Real.sqrt_sq hp_pos.le]
  · -- `OH ⟂ BD`: both are coordinate-aligned.
    rw [inner_sub_left, inner_sub_right, inner_sub_right]
    simp only [inner_pt]
    simp

/-!
## Part III: the geometric bridge

The angle conditions, together with `H` lying strictly inside `△SCT`, force the
polynomial conditions `Qt a b d t = 0` and `Qt a d b s = 0`. The mechanism
(found by computer algebra and verified numerically before formalizing):
taking `cos` of `∠THC = ∠DTC + π/2` and squaring gives `k·Qt·Q̂t = 0` where the
second factor `Q̂t` is a spurious branch. The two branches are separated by the
sign of `crs2 (T−H, C−H) · crs2 (D−T, C−T)` (same sign = good branch), and the
identities `crs2(D−T, C−T) = b(1−t)(a²+d²)/a` resp. `crs2(B−S, C−S) = d(1−s)(a²+b²)/a`
together with the inside-triangle hypothesis (which forces `sign b = −σ`,
`sign d = σ` for the common cross-product sign `σ`, see `claimA`) put us on the
good branch on both sides.
-/

/-- 2D cross product (signed area) of two vectors. -/
def crs2 (u v : EuclideanSpace ℝ (Fin 2)) : ℝ := u 0 * v 1 - u 1 * v 0

/-- A point strictly inside a triangle sees its three vertices with cyclically
consistent orientation: the three cross products are all of the same strict sign. -/
theorem cross_signs_of_mem_interior {S C T H : EuclideanSpace ℝ (Fin 2)}
    (h : H ∈ interior (convexHull ℝ {S, C, T})) :
    (0 < crs2 (S - H) (C - H) ∧ 0 < crs2 (C - H) (T - H) ∧ 0 < crs2 (T - H) (S - H)) ∨
    (crs2 (S - H) (C - H) < 0 ∧ crs2 (C - H) (T - H) < 0 ∧ crs2 (T - H) (S - H) < 0) := by
  -- Step 1: since the interior is nonempty, `{S, C, T}` affinely spans the plane,
  -- hence `S, C, T` are affinely independent.
  have hne : (interior (convexHull ℝ {S, C, T})).Nonempty := ⟨H, h⟩
  have hspan : affineSpan ℝ {S, C, T} = ⊤ := affineSpan_eq_top_of_nonempty_interior hne
  have hrange : Set.range ![S, C, T] = {S, C, T} := by
    ext x
    simp
    tauto
  have hspan' : affineSpan ℝ (Set.range ![S, C, T]) = ⊤ := by rwa [← hrange] at hspan
  have hvspan : vectorSpan ℝ (Set.range ![S, C, T]) = ⊤ := by
    rw [← direction_affineSpan, hspan']
    exact AffineSubspace.direction_top _ _ _
  have hfr : Module.finrank ℝ ↥(vectorSpan ℝ (Set.range ![S, C, T])) = 2 := by
    rw [hvspan, finrank_top, finrank_euclideanSpace_fin]
  have hind : AffineIndependent ℝ ![S, C, T] :=
    (affineIndependent_iff_finrank_vectorSpan_eq ℝ ![S, C, T] (n := 2) (by simp)).mpr hfr
  -- Step 2: `S, C, T` form an affine basis, and `H` has strictly positive barycentric
  -- coordinates in it.
  let b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)) := ⟨![S, C, T], hind, hspan'⟩
  have hbF : (b : Fin 3 → EuclideanSpace ℝ (Fin 2)) = ![S, C, T] := rfl
  have hb0 : b 0 = S := rfl
  have hb1 : b 1 = C := rfl
  have hb2 : b 2 = T := rfl
  have hpos : ∀ i, 0 < b.coord i H := by
    have hH' : H ∈ interior (convexHull ℝ (Set.range (b : Fin 3 → EuclideanSpace ℝ (Fin 2)))) := by
      rwa [hbF, hrange]
    rw [b.interior_convexHull] at hH'
    exact hH'
  have hsum : b.coord 0 H + b.coord 1 H + b.coord 2 H = 1 := by
    have hs := b.sum_coord_apply_eq_one H
    rwa [Fin.sum_univ_three] at hs
  have hlin : b.coord 0 H • S + b.coord 1 H • C + b.coord 2 H • T = H := by
    have hl := b.linear_combination_coord_eq_self H
    rw [Fin.sum_univ_three, hb0, hb1, hb2] at hl
    exact hl
  set α := b.coord 0 H with hα
  set β := b.coord 1 H with hβ
  set γ := b.coord 2 H with hγ
  have hαpos : 0 < α := by rw [hα]; exact hpos 0
  have hβpos : 0 < β := by rw [hβ]; exact hpos 1
  have hγpos : 0 < γ := by rw [hγ]; exact hpos 2
  -- Step 3: coordinatewise expansion of `H`.
  have hH : ∀ j : Fin 2, H j = α * S j + β * C j + γ * T j := by
    intro j
    rw [← hlin]
    simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  -- Step 4: the doubled signed area `K` of the triangle is nonzero.
  set K : ℝ := (C 0 - S 0) * (T 1 - S 1) - (C 1 - S 1) * (T 0 - S 0) with hKdef
  have hli : LinearIndependent ℝ ![C - S, T - S] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h2 : (-s - t) • S + s • C + t • T = 0 := by
      have h3 : s • (C - S) + t • (T - S) = (-s - t) • S + s • C + t • T := by
        simp only [smul_sub, sub_smul, neg_smul]
        abel
      rw [← h3]; exact hst
    have hsum0 : ∑ i : Fin 3, (![-s - t, s, t] : Fin 3 → ℝ) i = 0 := by
      simp [Fin.sum_univ_three]
      ring
    have hw : ∑ i : Fin 3, (![-s - t, s, t] : Fin 3 → ℝ) i •
        (![S, C, T] : Fin 3 → EuclideanSpace ℝ (Fin 2)) i = 0 := by
      rw [Fin.sum_univ_three]
      simpa using h2
    have hall := affineIndependent_iff.mp hind Finset.univ _ hsum0 hw
    have hs0 : s = 0 := by
      have h1 := hall 1 (Finset.mem_univ 1)
      simpa using h1
    have ht0 : t = 0 := by
      have h2' := hall 2 (Finset.mem_univ 2)
      simpa using h2'
    exact ⟨hs0, ht0⟩
  have hK : K ≠ 0 := by
    rw [hKdef]
    intro hK0
    have hu : C - S ≠ 0 := hli.ne_zero 0
    have hpair := (LinearIndependent.pair_iff' hu).mp hli
    have hc0 : (C - S) 0 ≠ 0 ∨ (C - S) 1 ≠ 0 := by
      by_contra hc
      obtain ⟨h0, h1⟩ := not_or.mp hc
      apply hu
      apply PiLp.ext
      rw [Fin.forall_fin_two]
      exact ⟨by simp [of_not_not h0], by simp [of_not_not h1]⟩
    have hK0' : (C 0 - S 0) * (T 1 - S 1) = (C 1 - S 1) * (T 0 - S 0) := by linarith
    rcases hc0 with hu0 | hu1
    · have hu0' : C 0 - S 0 ≠ 0 := by rwa [PiLp.sub_apply] at hu0
      have key : ((T - S) 0 / (C - S) 0) • (C - S) = T - S := by
        apply PiLp.ext
        rw [Fin.forall_fin_two]
        constructor
        · simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
          field_simp [hu0']
        · simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
          field_simp [hu0']
          linear_combination hK0'.symm
      exact hpair _ key
    · have hu1' : C 1 - S 1 ≠ 0 := by rwa [PiLp.sub_apply] at hu1
      have key : ((T - S) 1 / (C - S) 1) • (C - S) = T - S := by
        apply PiLp.ext
        rw [Fin.forall_fin_two]
        constructor
        · simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
          field_simp [hu1']
          linear_combination hK0'
        · simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
          field_simp [hu1']
      exact hpair _ key
  -- Step 5: the three cross products are `γ * K`, `α * K`, `β * K`.
  have e1 : crs2 (S - H) (C - H) = γ * K := by
    have hγ' : γ = 1 - α - β := by linarith
    simp only [crs2, PiLp.sub_apply]
    rw [hKdef, hH 0, hH 1, hγ']
    ring
  have e2 : crs2 (C - H) (T - H) = α * K := by
    have hα' : α = 1 - β - γ := by linarith
    simp only [crs2, PiLp.sub_apply]
    rw [hKdef, hH 0, hH 1, hα']
    ring
  have e3 : crs2 (T - H) (S - H) = β * K := by
    have hβ' : β = 1 - α - γ := by linarith
    simp only [crs2, PiLp.sub_apply]
    rw [hKdef, hH 0, hH 1, hβ']
    ring
  -- Step 6: all three share the sign of `K`.
  rcases hK.lt_or_gt with hKn | hKp
  · right
    exact ⟨by rw [e1]; exact mul_neg_of_pos_of_neg hγpos hKn,
           by rw [e2]; exact mul_neg_of_pos_of_neg hαpos hKn,
           by rw [e3]; exact mul_neg_of_pos_of_neg hβpos hKn⟩
  · left
    exact ⟨by rw [e1]; exact mul_pos hγpos hKp,
           by rw [e2]; exact mul_pos hαpos hKp,
           by rw [e3]; exact mul_pos hβpos hKp⟩

theorem pt_sub (x₁ y₁ x₂ y₂ : ℝ) : pt x₁ y₁ - pt x₂ y₂ = pt (x₁ - x₂) (y₁ - y₂) := by
  ext i; fin_cases i <;> simp [pt]

theorem crs2_pt (x₁ y₁ x₂ y₂ : ℝ) : crs2 (pt x₁ y₁) (pt x₂ y₂) = x₁ * y₂ - y₁ * x₂ := by
  simp [crs2]

theorem crs2_sub_pt (x₁ y₁ x₂ y₂ x₃ y₃ x₄ y₄ : ℝ) :
    crs2 (pt x₁ y₁ - pt x₂ y₂) (pt x₃ y₃ - pt x₄ y₄)
      = (x₁ - x₂) * (y₃ - y₄) - (y₁ - y₂) * (x₃ - x₄) := by
  rw [pt_sub, pt_sub, crs2_pt]

theorem inner_sub_pt (x₁ y₁ x₂ y₂ x₃ y₃ x₄ y₄ : ℝ) :
    inner ℝ (pt x₁ y₁ - pt x₂ y₂) (pt x₃ y₃ - pt x₄ y₄)
      = (x₁ - x₂) * (x₃ - x₄) + (y₁ - y₂) * (y₃ - y₄) := by
  rw [pt_sub, pt_sub, inner_pt]

theorem sin_angle_crs2 {u v : EuclideanSpace ℝ (Fin 2)} (hu : u ≠ 0) (hv : v ≠ 0) :
    Real.sin (InnerProductGeometry.angle u v) = |crs2 u v| / (‖u‖ * ‖v‖) := by
  rw [InnerProductGeometry.sin_angle hu hv]
  congr 1
  have h : (inner ℝ u u) * (inner ℝ v v) - (inner ℝ u v) * (inner ℝ u v) = (crs2 u v)^2 := by
    rw [PiLp.inner_apply, PiLp.inner_apply, PiLp.inner_apply,
      Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    simp [crs2, RCLike.inner_apply]
    ring
  rw [h, Real.sqrt_sq_eq_abs]

theorem crs2_zero_left (v : EuclideanSpace ℝ (Fin 2)) : crs2 0 v = 0 := by simp [crs2]
theorem crs2_zero_right (u : EuclideanSpace ℝ (Fin 2)) : crs2 u 0 = 0 := by simp [crs2]

/-- Inside-sign analysis (I): if the three crosses at `H` are positive
(and `0 < a`, `0 ≤ s, t < 1`), then `b < 0 < d`. -/
theorem claimA {a b d s t : ℝ} (ha : 0 < a) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (ht0 : 0 ≤ t) (ht1 : t < 1)
    (h1 : 0 < s*b^2*d - a^2*(1-s)*(b+d))
    (h2 : 0 < a^2*(b+d)*(1-t) - b*d^2*t)
    (h3 : 0 < a*d*t*(1-s) - a*b*s*(1-t)) : b < 0 ∧ d > 0 := by
  have h1t : (0:ℝ) < 1 - t := by linarith
  have h1s : (0:ℝ) < 1 - s := by linarith
  rcases eq_or_lt_of_le hs0 with rfl | hs0'
  · -- boundary `s = 0`: `h3` gives `d > 0`, `h1`, `h2` give `b < 0`.
    simp only [zero_mul, mul_zero, sub_zero] at h1 h3
    rcases eq_or_lt_of_le ht0 with rfl | ht0'
    · simp only [mul_zero, zero_mul] at h3
      exact absurd h3 (lt_irrefl 0)
    · have hdpos : 0 < d := by
        have : (0:ℝ) < a * t := mul_pos ha ht0'
        nlinarith [h3, this]
      have hbneg : b < 0 := by
        nlinarith [h1, h2, h3, hdpos, mul_pos ha h1t, mul_pos (mul_pos ha hdpos) (mul_pos hdpos ht0')]
      exact ⟨hbneg, hdpos⟩
  · rcases eq_or_lt_of_le ht0 with rfl | ht0'
    · -- boundary `t = 0` (with `s > 0`): `h3` gives `b < 0`, `h2` gives `d > 0`.
      simp only [mul_zero, zero_mul, sub_zero] at h2 h3
      have hbneg : b < 0 := by
        have : (0:ℝ) < a * s := mul_pos ha hs0'
        nlinarith [h3, this]
      have hdpos : 0 < d := by nlinarith [h2, hbneg, mul_pos ha hs0']
      exact ⟨hbneg, hdpos⟩
    · -- main case `0 < s, t < 1`
      have hbne : b ≠ 0 := by
        rintro rfl
        simp only [zero_mul] at h1 h2
        nlinarith [mul_pos ha hs0', mul_pos ha h1s, mul_pos ha h1t]
      have hdne : d ≠ 0 := by
        rintro rfl
        simp only [mul_zero] at h1 h2
        nlinarith [mul_pos ha hs0', mul_pos ha h1s, mul_pos ha h1t]
      have hdpos : 0 < d := by
        by_contra hcon
        push Not at hcon
        have hdneg : d < 0 := lt_of_le_of_ne hcon hdne
        have hX := mul_neg_of_pos_of_neg (mul_pos (mul_pos ha ht0') h1s) hdneg
        have hY := mul_pos (mul_pos ha hs0') h1t
        have hbneg : b < 0 := by nlinarith [h3, hX, hY]
        nlinarith [h1, h2, h3, mul_pos ha hs0', mul_pos ha h1s, mul_pos ha h1t,
          mul_pos (show 0 < -b by linarith) (show 0 < -d by linarith),
          mul_neg_of_pos_of_neg (mul_pos (mul_pos ha ht0') h1t) hbneg,
          mul_neg_of_pos_of_neg (mul_pos (mul_pos ha ht0') h1t) hdneg]
      have hbneg : b < 0 := by
        by_contra hcon
        push Not at hcon
        have hbpos : 0 < b := lt_of_le_of_ne hcon (Ne.symm hbne)
        nlinarith [h1, h2, h3, mul_pos ha hs0', mul_pos ha h1s, mul_pos ha h1t,
          mul_pos hbpos hdpos, mul_pos (mul_pos ha hbpos) hdpos]
      exact ⟨hbneg, hdpos⟩

/-- Inside-sign analysis (II): the mirrored (all-negative) case. -/
theorem claimA' {a b d s t : ℝ} (ha : 0 < a) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (ht0 : 0 ≤ t) (ht1 : t < 1)
    (h1 : s*b^2*d - a^2*(1-s)*(b+d) < 0)
    (h2 : a^2*(b+d)*(1-t) - b*d^2*t < 0)
    (h3 : a*d*t*(1-s) - a*b*s*(1-t) < 0) : 0 < b ∧ d < 0 := by
  have h := claimA (a := a) (b := -b) (d := -d) (s := s) (t := t) ha hs0 hs1 ht0 ht1
    (by nlinarith [h1]) (by nlinarith [h2]) (by nlinarith [h3])
  exact ⟨neg_lt_zero.mp h.1, neg_pos.mp h.2⟩

/-- The key algebraic identity linking the polynomial `Qt` to the geometry. -/
theorem T_identity {a b d t : ℝ} (ha : a ≠ 0) :
    (a^2 + d^2) * (t - 1) / a^2 * Qt a b d t
      = inner ℝ (pt d 0 - pt (t*d) (a*(1-t))) (pt (b+d) (b*d/a) - pt (t*d) (a*(1-t)))
        * inner ℝ (pt (t*d) (a*(1-t)) - pt 0 0) (pt (b+d) (b*d/a) - pt 0 0)
        + crs2 (pt (t*d) (a*(1-t)) - pt 0 0) (pt (b+d) (b*d/a) - pt 0 0)
          * crs2 (pt d 0 - pt (t*d) (a*(1-t))) (pt (b+d) (b*d/a) - pt (t*d) (a*(1-t))) := by
  rw [inner_sub_pt, inner_sub_pt, crs2_sub_pt, crs2_sub_pt]
  simp only [Qt]
  field_simp [ha]
  ring

/-- The generic bridge: the angle condition `∠P HC = ∠DPC + 90°` plus the sign
condition (from the inside-triangle hypothesis) force the polynomial condition
`Qt = 0`. Used twice: with `D, T` and with `B, S` (swapped). -/
theorem Qt_generic {a b d t : ℝ} (ha : 0 < a) (hd : d ≠ 0) (ht1 : t ≠ 1)
    (hangle : ∠ (pt (t * d) (a * (1 - t))) (pt 0 0) (pt (b + d) (b * d / a))
      = ∠ (pt d 0) (pt (t * d) (a * (1 - t))) (pt (b + d) (b * d / a)) + Real.pi / 2)
    (hsgn : 0 < crs2 (pt (t * d) (a * (1 - t)) - pt 0 0) (pt (b + d) (b * d / a) - pt 0 0)
      * crs2 (pt d 0 - pt (t * d) (a * (1 - t))) (pt (b + d) (b * d / a) - pt (t * d) (a * (1 - t)))) :
    Qt a b d t = 0 := by
  set HT : EuclideanSpace ℝ (Fin 2) := pt (t * d) (a * (1 - t)) - pt 0 0 with hHT
  set HC : EuclideanSpace ℝ (Fin 2) := pt (b + d) (b * d / a) - pt 0 0 with hHC
  set TD : EuclideanSpace ℝ (Fin 2) := pt d 0 - pt (t * d) (a * (1 - t)) with hTD
  set TC : EuclideanSpace ℝ (Fin 2) := pt (b + d) (b * d / a) - pt (t * d) (a * (1 - t)) with hTC
  have hcr := mul_ne_zero_iff.mp (ne_of_gt hsgn)
  have hne1 : HT ≠ 0 := by
    intro h
    rw [h, crs2_zero_left] at hcr
    exact hcr.1 rfl
  have hne2 : HC ≠ 0 := by
    intro h
    rw [h, crs2_zero_right] at hcr
    exact hcr.1 rfl
  have hne3 : TD ≠ 0 := by
    intro h
    rw [h, crs2_zero_left] at hcr
    exact hcr.2 rfl
  have hne4 : TC ≠ 0 := by
    intro h
    rw [h, crs2_zero_right] at hcr
    exact hcr.2 rfl
  have hN1 : ‖HT‖ * ‖HC‖ ≠ 0 := mul_ne_zero (norm_ne_zero_iff.mpr hne1) (norm_ne_zero_iff.mpr hne2)
  have hN2 : ‖TD‖ * ‖TC‖ ≠ 0 := mul_ne_zero (norm_ne_zero_iff.mpr hne3) (norm_ne_zero_iff.mpr hne4)
  have hθ : InnerProductGeometry.angle HT HC = InnerProductGeometry.angle TD TC + Real.pi / 2 := by
    simp only [EuclideanGeometry.angle, vsub_eq_sub] at hangle
    rw [← hHT, ← hHC, ← hTD, ← hTC] at hangle
    exact hangle
  have hcos : Real.cos (InnerProductGeometry.angle HT HC)
      = - Real.sin (InnerProductGeometry.angle TD TC) := by
    rw [hθ, Real.cos_add_pi_div_two]
  have hsin : Real.sin (InnerProductGeometry.angle HT HC)
      = Real.cos (InnerProductGeometry.angle TD TC) := by
    rw [hθ, Real.sin_add_pi_div_two]
  have hc1 : inner ℝ HT HC = (‖HT‖ * ‖HC‖) * Real.cos (InnerProductGeometry.angle HT HC) := by
    rw [InnerProductGeometry.cos_angle]
    field_simp [hN1]
  have hc2 : inner ℝ TD TC = (‖TD‖ * ‖TC‖) * Real.cos (InnerProductGeometry.angle TD TC) := by
    rw [InnerProductGeometry.cos_angle]
    field_simp [hN2]
  have hs1 : |crs2 HT HC| = (‖HT‖ * ‖HC‖) * Real.sin (InnerProductGeometry.angle HT HC) := by
    rw [sin_angle_crs2 hne1 hne2]
    field_simp [hN1]
  have hs2 : |crs2 TD TC| = (‖TD‖ * ‖TC‖) * Real.sin (InnerProductGeometry.angle TD TC) := by
    rw [sin_angle_crs2 hne3 hne4]
    field_simp [hN2]
  have habs : crs2 HT HC * crs2 TD TC = |crs2 HT HC| * |crs2 TD TC| := by
    calc crs2 HT HC * crs2 TD TC = |crs2 HT HC * crs2 TD TC| := (abs_of_pos hsgn).symm
      _ = |crs2 HT HC| * |crs2 TD TC| := abs_mul _ _
  have hcomb : crs2 HT HC * crs2 TD TC
      = (‖HT‖ * ‖HC‖) * (‖TD‖ * ‖TC‖) * Real.cos (InnerProductGeometry.angle TD TC)
        * Real.sin (InnerProductGeometry.angle TD TC) := by
    rw [habs, hs1, hs2, hsin]
    ring
  have hinner : inner ℝ HT HC
      = - ((‖HT‖ * ‖HC‖) * Real.sin (InnerProductGeometry.angle TD TC)) := by
    rw [hc1, hcos]
    ring
  have hid := T_identity (a := a) (b := b) (d := d) (t := t) ha.ne'
  rw [← hHT, ← hHC, ← hTD, ← hTC] at hid
  rw [hc2, hinner, hcomb] at hid
  have hfactor : (a^2 + d^2) * (t - 1) / a^2 ≠ 0 := by
    have h1 : a^2 + d^2 ≠ 0 := by nlinarith [mul_self_pos.mpr hd, mul_self_nonneg a]
    have h2 : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
    have h3 : (a:ℝ)^2 ≠ 0 := pow_ne_zero 2 ha.ne'
    exact div_ne_zero (mul_ne_zero h1 h2) h3
  have hzero : (a^2 + d^2) * (t - 1) / a^2 * Qt a b d t = 0 := by
    linarith [hid]
  exact (mul_eq_zero.mp hzero).resolve_left hfactor

/-- The bridge, given the cross-sign trichotomy from the inside-triangle hypothesis. -/
theorem bridge_core {a b d s t : ℝ} (ha : 0 < a) (hb : b ≠ 0) (hd : d ≠ 0)
    (ht₀ : 0 ≤ t) (ht₁ : t < 1) (hs₀ : 0 ≤ s) (hs₁ : s < 1)
    (hSangle : ∠ (pt (b + d) (b * d / a)) (pt 0 0) (pt (s * b) (a * (1 - s)))
      = ∠ (pt (b + d) (b * d / a)) (pt (s * b) (a * (1 - s))) (pt b 0) + Real.pi / 2)
    (hTangle : ∠ (pt (t * d) (a * (1 - t))) (pt 0 0) (pt (b + d) (b * d / a))
      = ∠ (pt d 0) (pt (t * d) (a * (1 - t))) (pt (b + d) (b * d / a)) + Real.pi / 2)
    (hcross : (0 < crs2 (pt (s * b) (a * (1 - s)) - pt 0 0) (pt (b + d) (b * d / a) - pt 0 0)
        ∧ 0 < crs2 (pt (b + d) (b * d / a) - pt 0 0) (pt (t * d) (a * (1 - t)) - pt 0 0)
        ∧ 0 < crs2 (pt (t * d) (a * (1 - t)) - pt 0 0) (pt (s * b) (a * (1 - s)) - pt 0 0))
      ∨ (crs2 (pt (s * b) (a * (1 - s)) - pt 0 0) (pt (b + d) (b * d / a) - pt 0 0) < 0
        ∧ crs2 (pt (b + d) (b * d / a) - pt 0 0) (pt (t * d) (a * (1 - t)) - pt 0 0) < 0
        ∧ crs2 (pt (t * d) (a * (1 - t)) - pt 0 0) (pt (s * b) (a * (1 - s)) - pt 0 0) < 0)) :
    Qt a b d t = 0 ∧ Qt a d b s = 0 := by
  have h1t : (0:ℝ) < 1 - t := by linarith
  have h1s : (0:ℝ) < 1 - s := by linarith
  have hane : a ≠ 0 := ha.ne'
  have fd1 : a * crs2 (pt (s * b) (a * (1 - s)) - pt 0 0) (pt (b + d) (b * d / a) - pt 0 0)
      = s * b^2 * d - a^2 * (1 - s) * (b + d) := by
    rw [crs2_sub_pt]
    field_simp [hane]
    ring
  have fd2 : a * crs2 (pt (b + d) (b * d / a) - pt 0 0) (pt (t * d) (a * (1 - t)) - pt 0 0)
      = a^2 * (b + d) * (1 - t) - b * d^2 * t := by
    rw [crs2_sub_pt]
    field_simp [hane]
    ring
  have fd3 : crs2 (pt (t * d) (a * (1 - t)) - pt 0 0) (pt (s * b) (a * (1 - s)) - pt 0 0)
      = a * d * t * (1 - s) - a * b * s * (1 - t) := by
    rw [crs2_sub_pt]
    ring
  have hcr_HT : crs2 (pt (t * d) (a * (1 - t)) - pt 0 0) (pt (b + d) (b * d / a) - pt 0 0)
      = - crs2 (pt (b + d) (b * d / a) - pt 0 0) (pt (t * d) (a * (1 - t)) - pt 0 0) := by
    rw [crs2_sub_pt, crs2_sub_pt]
    ring
  have hcr_TD : crs2 (pt d 0 - pt (t * d) (a * (1 - t))) (pt (b + d) (b * d / a) - pt (t * d) (a * (1 - t)))
      = b * (1 - t) * (a^2 + d^2) / a := by
    rw [crs2_sub_pt]
    field_simp [hane]
    ring
  have hcr_SB : crs2 (pt b 0 - pt (s * b) (a * (1 - s))) (pt (b + d) (b * d / a) - pt (s * b) (a * (1 - s)))
      = d * (1 - s) * (a^2 + b^2) / a := by
    rw [crs2_sub_pt]
    field_simp [hane]
    ring
  have had : (0:ℝ) < a^2 + d^2 := by nlinarith [mul_self_pos.mpr hd, mul_self_nonneg a]
  have hab : (0:ℝ) < a^2 + b^2 := by nlinarith [mul_self_pos.mpr hb, mul_self_nonneg a]
  rcases hcross with ⟨h1p, h2p, h3p⟩ | ⟨h1n, h2n, h3n⟩
  · -- σ = +1 case: b < 0, d > 0
    have hbd : b < 0 ∧ 0 < d :=
      claimA ha hs₀ hs₁ ht₀ ht₁ (by rw [← fd1]; exact mul_pos ha h1p)
        (by rw [← fd2]; exact mul_pos ha h2p) (by rw [← fd3]; exact h3p)
    have hsgnT : 0 < crs2 (pt (t * d) (a * (1 - t)) - pt 0 0) (pt (b + d) (b * d / a) - pt 0 0)
        * crs2 (pt d 0 - pt (t * d) (a * (1 - t))) (pt (b + d) (b * d / a) - pt (t * d) (a * (1 - t))) := by
      rw [hcr_HT, hcr_TD]
      have hnum : b * (1 - t) * (a^2 + d^2) < 0 := by
        nlinarith [hbd.1, h1t, had, mul_neg_of_pos_of_neg (mul_pos h1t had) hbd.1]
      have hTDneg : b * (1 - t) * (a^2 + d^2) / a < 0 := div_neg_of_neg_of_pos hnum ha
      have h2neg : - crs2 (pt (b + d) (b * d / a) - pt 0 0) (pt (t * d) (a * (1 - t)) - pt 0 0) < 0 :=
        neg_lt_zero.mpr h2p
      exact mul_pos_of_neg_of_neg h2neg hTDneg
    have hsgnS : 0 < crs2 (pt (s * b) (a * (1 - s)) - pt 0 0) (pt (b + d) (b * d / a) - pt 0 0)
        * crs2 (pt b 0 - pt (s * b) (a * (1 - s))) (pt (b + d) (b * d / a) - pt (s * b) (a * (1 - s))) := by
      rw [hcr_SB]
      have hSBpos : 0 < d * (1 - s) * (a^2 + b^2) / a :=
        div_pos (mul_pos (mul_pos hbd.2 h1s) hab) ha
      exact mul_pos h1p hSBpos
    refine ⟨Qt_generic ha hd (ne_of_lt ht₁) hTangle hsgnT, ?_⟩
    have hSangle' : ∠ (pt (s * b) (a * (1 - s))) (pt 0 0) (pt (d + b) (d * b / a))
        = ∠ (pt b 0) (pt (s * b) (a * (1 - s))) (pt (d + b) (d * b / a)) + Real.pi / 2 := by
      rw [add_comm d b, mul_comm d b, ← EuclideanGeometry.angle_comm, hSangle,
        EuclideanGeometry.angle_comm]
    exact Qt_generic ha hb (ne_of_lt hs₁) hSangle' (by
      rw [add_comm d b, mul_comm d b]
      exact hsgnS)
  · -- σ = −1 case: b > 0, d < 0
    have hbd : 0 < b ∧ d < 0 :=
      claimA' ha hs₀ hs₁ ht₀ ht₁ (by rw [← fd1]; exact mul_neg_of_pos_of_neg ha h1n)
        (by rw [← fd2]; exact mul_neg_of_pos_of_neg ha h2n) (by rw [← fd3]; exact h3n)
    have hsgnT : 0 < crs2 (pt (t * d) (a * (1 - t)) - pt 0 0) (pt (b + d) (b * d / a) - pt 0 0)
        * crs2 (pt d 0 - pt (t * d) (a * (1 - t))) (pt (b + d) (b * d / a) - pt (t * d) (a * (1 - t))) := by
      rw [hcr_HT, hcr_TD]
      have hTDpos : 0 < b * (1 - t) * (a^2 + d^2) / a :=
        div_pos (mul_pos (mul_pos hbd.1 h1t) had) ha
      have h2pos : 0 < - crs2 (pt (b + d) (b * d / a) - pt 0 0) (pt (t * d) (a * (1 - t)) - pt 0 0) :=
        neg_pos.mpr h2n
      exact mul_pos h2pos hTDpos
    have hsgnS : 0 < crs2 (pt (s * b) (a * (1 - s)) - pt 0 0) (pt (b + d) (b * d / a) - pt 0 0)
        * crs2 (pt b 0 - pt (s * b) (a * (1 - s))) (pt (b + d) (b * d / a) - pt (s * b) (a * (1 - s))) := by
      rw [hcr_SB]
      have hnum : d * (1 - s) * (a^2 + b^2) < 0 := by
        nlinarith [mul_neg_of_pos_of_neg (mul_pos h1s hab) hbd.2]
      have hSBneg : d * (1 - s) * (a^2 + b^2) / a < 0 := div_neg_of_neg_of_pos hnum ha
      exact mul_pos_of_neg_of_neg h1n hSBneg
    refine ⟨Qt_generic ha hd (ne_of_lt ht₁) hTangle hsgnT, ?_⟩
    have hSangle' : ∠ (pt (s * b) (a * (1 - s))) (pt 0 0) (pt (d + b) (d * b / a))
        = ∠ (pt b 0) (pt (s * b) (a * (1 - s))) (pt (d + b) (d * b / a)) + Real.pi / 2 := by
      rw [add_comm d b, mul_comm d b, ← EuclideanGeometry.angle_comm, hSangle,
        EuclideanGeometry.angle_comm]
    exact Qt_generic ha hb (ne_of_lt hs₁) hSangle' (by
      rw [add_comm d b, mul_comm d b]
      exact hsgnS)

/-- The geometric bridge: the angle conditions, together with `H` lying strictly
inside `△SCT`, force the polynomial conditions `Qt a b d t = 0` and `Qt a d b s = 0`. -/
theorem Qt_of_configuration {a b d s t : ℝ} (ha : 0 < a) (hb : b ≠ 0) (hd : d ≠ 0)
    (ht₀ : 0 ≤ t) (ht₁ : t < 1) (hs₀ : 0 ≤ s) (hs₁ : s < 1)
    (hSangle : ∠ (pt (b + d) (b * d / a)) (pt 0 0) (pt (s * b) (a * (1 - s)))
      = ∠ (pt (b + d) (b * d / a)) (pt (s * b) (a * (1 - s))) (pt b 0) + Real.pi / 2)
    (hTangle : ∠ (pt (t * d) (a * (1 - t))) (pt 0 0) (pt (b + d) (b * d / a))
      = ∠ (pt d 0) (pt (t * d) (a * (1 - t))) (pt (b + d) (b * d / a)) + Real.pi / 2)
    (hHin : pt 0 0 ∈ interior
      (convexHull ℝ {pt (s * b) (a * (1 - s)), pt (b + d) (b * d / a), pt (t * d) (a * (1 - t))})) :
    Qt a b d t = 0 ∧ Qt a d b s = 0 :=
  bridge_core ha hb hd ht₀ ht₁ hs₀ hs₁ hSangle hTangle (cross_signs_of_mem_interior hHin)

theorem pt_add (x₁ y₁ x₂ y₂ : ℝ) : pt x₁ y₁ + pt x₂ y₂ = pt (x₁ + x₂) (y₁ + y₂) := by
  ext i; fin_cases i <;> simp [pt]

theorem pt_smul (c : ℝ) (x y : ℝ) : c • pt x y = pt (c * x) (c * y) := by
  ext i; fin_cases i <;> simp [pt]

theorem pt_zero_zero : pt 0 0 = 0 := by
  ext i; fin_cases i <;> simp [pt]


/-- If `∠ X Y Z = π/2` then the two sides are perpendicular (inner product zero). -/
theorem inner_eq_zero_of_angle_eq_pi_div_two {X Y Z : EuclideanSpace ℝ (Fin 2)}
    (hXY : X ≠ Y) (hZY : Z ≠ Y) (h : ∠ X Y Z = Real.pi / 2) : inner ℝ (X - Y) (Z - Y) = 0 := by
  have hcos : Real.cos (∠ X Y Z) = 0 := by rw [h, Real.cos_pi_div_two]
  rw [EuclideanGeometry.angle, vsub_eq_sub, vsub_eq_sub, InnerProductGeometry.cos_angle] at hcos
  rcases div_eq_zero_iff.mp hcos with hnum | hden
  · exact hnum
  · exfalso
    rw [mul_eq_zero] at hden
    rcases hden with hd | hd
    · exact hXY (sub_eq_zero.mp (norm_eq_zero.mp hd))
    · exact hZY (sub_eq_zero.mp (norm_eq_zero.mp hd))


/-- Standardization: the abstract configuration is isometric to the coordinate model. -/
theorem standardize
    (A B C D H S T : EuclideanSpace ℝ (Fin 2))
    (hAIBC : AffineIndependent ℝ ![A, B, C])
    (hAIBD : AffineIndependent ℝ ![A, B, D])
    (hIACD : AffineIndependent ℝ ![A, C, D])
    (hIBCD : AffineIndependent ℝ ![B, C, D])
    (hconv : ∃ X : EuclideanSpace ℝ (Fin 2), Sbtw ℝ A X C ∧ Sbtw ℝ B X D)
    (hABC : ∠ A B C = Real.pi / 2)
    (hCDA : ∠ C D A = Real.pi / 2)
    (hBD : B ≠ D)
    (hHline : H ∈ line[ℝ, B, D])
    (hHperp : inner ℝ (A - H) (D - B) = 0)
    (hS : Wbtw ℝ A S B)
    (hT : Wbtw ℝ A T D)
    (_hCH : C ≠ H) (hSH : S ≠ H) (hTH : T ≠ H)
    (hCS : C ≠ S) (hBS : B ≠ S) (hCT : C ≠ T) (hDT : D ≠ T)
    (hHin : H ∈ interior (convexHull ℝ {S, C, T}))
    (hSangle : ∠ C H S - ∠ C S B = Real.pi / 2)
    (hTangle : ∠ T H C - ∠ D T C = Real.pi / 2) :
    ∃ (f : EuclideanSpace ℝ (Fin 2) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin 2)) (a b d s t : ℝ),
      0 < a ∧ b ≠ 0 ∧ d ≠ 0 ∧ 0 ≤ s ∧ s < 1 ∧ 0 ≤ t ∧ t < 1 ∧
      f H = pt 0 0 ∧ f A = pt 0 a ∧ f B = pt b 0 ∧ f D = pt d 0 ∧
      f C = pt (b + d) (b * d / a) ∧ f S = pt (s * b) (a * (1 - s)) ∧
      f T = pt (t * d) (a * (1 - t)) ∧
      ∠ (f C) (f H) (f S) = ∠ (f C) (f S) (f B) + Real.pi / 2 ∧
      ∠ (f T) (f H) (f C) = ∠ (f D) (f T) (f C) + Real.pi / 2 ∧
      f H ∈ interior (convexHull ℝ {f S, f C, f T}) := by
  -- Nondegeneracy: `A ≠ H`.
  have hAH : A ≠ H := by
    intro h
    rw [← h] at hHline
    have hcol : Collinear ℝ {A, B, D} := collinear_insert_of_mem_affineSpan_pair hHline
    rw [affineIndependent_iff_not_collinear_set] at hAIBD
    exact hAIBD hcol
  -- Nondegeneracy: `B ≠ H`, via the `S`-angle condition.
  have hBH : B ≠ H := by
    intro h
    rw [← h] at hSangle
    obtain ⟨σ, hσI, rfl⟩ := hS
    have hσ1 : σ < 1 := by
      rcases eq_or_lt_of_le hσI.2 with h1 | h2
      · exfalso
        exact hBS (by rw [h1, AffineMap.lineMap_apply_one])
      · exact h2
    have hray : ∠ C B (AffineMap.lineMap A B σ) = ∠ C B A := by
      have hvec : AffineMap.lineMap A B σ - B = (1 - σ) • (A - B) := by
        rw [AffineMap.lineMap_apply_module]
        module
      simp only [EuclideanGeometry.angle, vsub_eq_sub]
      rw [hvec, InnerProductGeometry.angle_smul_right_of_pos _ _ (sub_pos.mpr hσ1)]
    have hpi : ∠ C B (AffineMap.lineMap A B σ) = Real.pi / 2 := by
      rw [hray, EuclideanGeometry.angle_comm, hABC]
    rw [hpi] at hSangle
    have hzero : ∠ C (AffineMap.lineMap A B σ) B = 0 := by linarith
    simp only [EuclideanGeometry.angle, vsub_eq_sub] at hzero
    rw [InnerProductGeometry.angle_eq_zero_iff] at hzero
    obtain ⟨hzne, r, hr, hrC⟩ := hzero
    have hCmem : C ∈ line[ℝ, AffineMap.lineMap A B σ, B] := by
      have hCeq : C = AffineMap.lineMap (AffineMap.lineMap A B σ) B r⁻¹ := by
        have hkey : C - AffineMap.lineMap A B σ = r⁻¹ • (B - AffineMap.lineMap A B σ) :=
          (eq_inv_smul_iff₀ hr.ne').mpr hrC.symm
        have h2 : C = AffineMap.lineMap A B σ + r⁻¹ • (B - AffineMap.lineMap A B σ) := by
          rw [← hkey]
          module
        rw [h2]
        simp only [AffineMap.lineMap_apply_module]
        module
      rw [hCeq]
      exact AffineMap.lineMap_mem_affineSpan_pair _ _ _
    have hSmem : AffineMap.lineMap A B σ ∈ line[ℝ, A, B] :=
      AffineMap.lineMap_mem_affineSpan_pair _ _ _
    have hsub : line[ℝ, AffineMap.lineMap A B σ, B] ≤ line[ℝ, A, B] := by
      apply affineSpan_le.mpr
      rintro x (rfl | rfl)
      · exact hSmem
      · exact right_mem_affineSpan_pair _ _ _
    have hCmem2 : C ∈ line[ℝ, A, B] := hsub hCmem
    have hcol : Collinear ℝ {C, A, B} := collinear_insert_of_mem_affineSpan_pair hCmem2
    rw [affineIndependent_iff_not_collinear_set] at hAIBC
    apply hAIBC
    rw [show ({A, B, C} : Set _) = {C, A, B} by ext x; simp; tauto]
    exact hcol
  -- Nondegeneracy: `D ≠ H`, mirrored, via the `T`-angle condition.
  have hDH : D ≠ H := by
    intro h
    rw [← h] at hTangle
    obtain ⟨τ, hτI, rfl⟩ := hT
    have hτ1 : τ < 1 := by
      rcases eq_or_lt_of_le hτI.2 with h1 | h2
      · exfalso
        exact hDT (by rw [h1, AffineMap.lineMap_apply_one])
      · exact h2
    have hray : ∠ (AffineMap.lineMap A D τ) D C = ∠ A D C := by
      have hvec : AffineMap.lineMap A D τ - D = (1 - τ) • (A - D) := by
        rw [AffineMap.lineMap_apply_module]
        module
      simp only [EuclideanGeometry.angle, vsub_eq_sub]
      rw [hvec, InnerProductGeometry.angle_smul_left_of_pos _ _ (sub_pos.mpr hτ1)]
    have hpi : ∠ (AffineMap.lineMap A D τ) D C = Real.pi / 2 := by
      rw [hray, EuclideanGeometry.angle_comm, hCDA]
    rw [hpi] at hTangle
    have hzero : ∠ D (AffineMap.lineMap A D τ) C = 0 := by linarith
    simp only [EuclideanGeometry.angle, vsub_eq_sub] at hzero
    rw [InnerProductGeometry.angle_eq_zero_iff] at hzero
    obtain ⟨hzne, r, hr, hrC⟩ := hzero
    have hCmem : C ∈ line[ℝ, AffineMap.lineMap A D τ, D] := by
      have hCeq : C = AffineMap.lineMap (AffineMap.lineMap A D τ) D r := by
        have hkey : C - AffineMap.lineMap A D τ = r • (D - AffineMap.lineMap A D τ) := hrC
        have h2 : C = AffineMap.lineMap A D τ + r • (D - AffineMap.lineMap A D τ) := by
          rw [← hkey]
          module
        rw [h2]
        simp only [AffineMap.lineMap_apply_module]
        module
      rw [hCeq]
      exact AffineMap.lineMap_mem_affineSpan_pair _ _ _
    have hTmem : AffineMap.lineMap A D τ ∈ line[ℝ, A, D] :=
      AffineMap.lineMap_mem_affineSpan_pair _ _ _
    have hsub : line[ℝ, AffineMap.lineMap A D τ, D] ≤ line[ℝ, A, D] := by
      apply affineSpan_le.mpr
      rintro x (rfl | rfl)
      · exact hTmem
      · exact right_mem_affineSpan_pair _ _ _
    have hCmem2 : C ∈ line[ℝ, A, D] := hsub hCmem
    have hcol : Collinear ℝ {C, A, D} := collinear_insert_of_mem_affineSpan_pair hCmem2
    rw [affineIndependent_iff_not_collinear_set] at hIACD
    apply hIACD
    rw [show ({A, C, D} : Set _) = {C, A, D} by ext x; simp; tauto]
    exact hcol
    -- The frame: `e₁` along `DB`, `e₂` along `HA`.
  have hAHne : A - H ≠ 0 := sub_ne_zero.mpr hAH
  have hDBne : D - B ≠ 0 := sub_ne_zero.mpr (Ne.symm hBD)
  set a := ‖A - H‖ with ha_def
  have hapos : 0 < a := norm_pos_iff.mpr hAHne
  have hane : a ≠ 0 := ne_of_gt hapos
  set c₀ := ‖D - B‖ with hc₀
  have hc₀pos : 0 < c₀ := norm_pos_iff.mpr hDBne
  set e₁ := c₀⁻¹ • (D - B) with he₁
  set e₂ := a⁻¹ • (A - H) with he₂
  have he₁norm : ‖e₁‖ = 1 := by
    rw [he₁, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hc₀pos.le), hc₀,
      inv_mul_cancel₀ (ne_of_gt hc₀pos)]
  have he₂norm : ‖e₂‖ = 1 := by
    rw [he₂, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hapos.le), ha_def,
      inv_mul_cancel₀ hane]
  have hperp : inner ℝ (D - B) (A - H) = 0 := by rw [real_inner_comm]; exact hHperp
  have heorth : inner ℝ e₁ e₂ = 0 := by
    rw [he₁, he₂, inner_smul_left, inner_smul_right, hperp, mul_zero, mul_zero]
  have hor : Orthonormal ℝ ![e₁, e₂] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [he₁norm, he₂norm, heorth, (real_inner_comm e₁ e₂)]
  have hli : LinearIndependent ℝ ![e₁, e₂] := hor.linearIndependent
  have hspan : ⊤ ≤ Submodule.span ℝ (Set.range ![e₁, e₂]) := by
    rw [LinearIndependent.span_eq_top_of_card_eq_finrank' hli
      (by rw [finrank_euclideanSpace_fin]; simp)]
  set onb := OrthonormalBasis.mk hor hspan with honb
  have honb0 : onb 0 = e₁ := by rw [honb, OrthonormalBasis.coe_mk]; rfl
  have honb1 : onb 1 = e₂ := by rw [honb, OrthonormalBasis.coe_mk]; rfl
  have repr_eq (v : EuclideanSpace ℝ (Fin 2)) :
      onb.repr v = pt (inner ℝ e₁ v) (inner ℝ e₂ v) := by
    ext i; fin_cases i <;>
      simp [OrthonormalBasis.repr_apply_apply, honb0, honb1]
  -- The coordinate isometry.
  set f : EuclideanSpace ℝ (Fin 2) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    (AffineIsometryEquiv.vaddConst ℝ (-H)).trans (onb.repr.toAffineIsometryEquiv) with hf
  have fapply (P : EuclideanSpace ℝ (Fin 2)) : f P = onb.repr (P - H) := by
    simp only [hf, AffineIsometryEquiv.coe_trans, Function.comp_apply,
      AffineIsometryEquiv.coe_vaddConst, LinearIsometryEquiv.coe_toAffineIsometryEquiv,
      vadd_eq_add]
    rw [sub_eq_add_neg]
  clear_value f onb e₁ e₂
  -- `f H`, `f A`.
  have fH : f H = pt 0 0 := by
    rw [fapply, sub_self, map_zero, pt_zero_zero]
  have fA : f A = pt 0 a := by
    have hAe : A - H = a • e₂ := by
      rw [he₂, smul_inv_smul₀ hane]
    rw [fapply, hAe, map_smul, repr_eq e₂, heorth, real_inner_self_eq_norm_mul_norm,
      he₂norm, mul_one, pt_smul]
    simp
  -- `H` on line `BD` in scalar form.
  have hHv : H -ᵥ B ∈ vectorSpan ℝ {B, D} := by
    have h := (AffineSubspace.vsub_right_mem_direction_iff_mem
      (mem_affineSpan ℝ (Set.mem_insert B {D})) H).mpr hHline
    rwa [direction_affineSpan] at h
  rw [mem_vectorSpan_pair] at hHv
  obtain ⟨μ, hμ⟩ := hHv
  have hμeq : H = B + μ • (B - D) := by
    have h1 : μ • (B - D) = H - B := by rwa [vsub_eq_sub, vsub_eq_sub] at hμ
    have h2 : H - B = μ • (B - D) := h1.symm
    rw [← h2]
    module
  have hBHvec : B - H = μ • (D - B) := by
    rw [hμeq]
    module
  have hDHvec : D - H = (1 + μ) • (D - B) := by
    rw [hμeq]
    module
  -- Perpendicularity of `B−H`, `D−H` to `e₂`.
  have hperpDB : inner ℝ e₂ (D - B) = 0 := by
    rw [he₂, inner_smul_left, hHperp, mul_zero]
  have hperpBH : inner ℝ e₂ (B - H) = 0 := by
    rw [hBHvec, inner_smul_right, hperpDB, mul_zero]
  have hperpDH : inner ℝ e₂ (D - H) = 0 := by
    rw [hDHvec, inner_smul_right, hperpDB, mul_zero]
  -- The scalars `b`, `d`.
  set b := inner ℝ e₁ (B - H) with hb_def
  have he₁DB : inner ℝ e₁ (D - B) = c₀ := by
    rw [he₁, inner_smul_left, real_inner_self_eq_norm_mul_norm, ← hc₀]
    simp [hc₀pos.ne']
  have hbval : b = μ * c₀ := by
    rw [hb_def, hBHvec, inner_smul_right, he₁DB]
  have hb : b ≠ 0 := by
    rw [hbval]
    apply mul_ne_zero _ (ne_of_gt hc₀pos)
    intro hμ0
    rw [hμeq, hμ0, zero_smul, add_zero] at hBH
    exact hBH rfl
  set d := inner ℝ e₁ (D - H) with hd_def
  have hdval : d = (1 + μ) * c₀ := by
    rw [hd_def, hDHvec, inner_smul_right, he₁DB]
  have hd : d ≠ 0 := by
    rw [hdval]
    apply mul_ne_zero _ (ne_of_gt hc₀pos)
    intro hμ1
    apply hDH
    have hμ' : μ = -1 := by linarith
    rw [hμeq, hμ']
    module
  have hbd : b - d ≠ 0 := by
    rw [hbval, hdval]
    have : μ * c₀ - (1 + μ) * c₀ = -c₀ := by ring
    rw [this, neg_ne_zero]
    exact ne_of_gt hc₀pos
  -- `f B`, `f D`.
  have fB : f B = pt b 0 := by
    rw [fapply, repr_eq, hb_def.symm, hperpBH]
  have fD : f D = pt d 0 := by
    rw [fapply, repr_eq, hd_def.symm, hperpDH]
  -- `f C`: the two right angles force `C = (b+d, bd/a)`.
  have fangle (P₁ P₂ P₃ : EuclideanSpace ℝ (Fin 2)) :
      ∠ (f P₁) (f P₂) (f P₃) = ∠ P₁ P₂ P₃ :=
    f.toAffineIsometry.angle_map P₁ P₂ P₃
  have hABC' : ∠ (f A) (f B) (f C) = Real.pi / 2 := by
    rw [fangle, hABC]
  have hCDA' : ∠ (f C) (f D) (f A) = Real.pi / 2 := by
    rw [fangle, hCDA]
  have hABne : A ≠ B := hAIBC.injective.ne (by decide : (0 : Fin 3) ≠ 1)
  have hCBne : C ≠ B := hAIBC.injective.ne (by decide : (2 : Fin 3) ≠ 1)
  have hCDne : C ≠ D := hIACD.injective.ne (by decide : (1 : Fin 3) ≠ 2)
  have hADne : A ≠ D := hAIBD.injective.ne (by decide : (0 : Fin 3) ≠ 2)
  have hinner1 : inner ℝ (f A - f B) (f C - f B) = 0 :=
    inner_eq_zero_of_angle_eq_pi_div_two (f.injective.ne hABne) (f.injective.ne hCBne) hABC'
  have hinner2 : inner ℝ (f C - f D) (f A - f D) = 0 :=
    inner_eq_zero_of_angle_eq_pi_div_two (f.injective.ne hCDne) (f.injective.ne hADne) hCDA'
  set x := inner ℝ e₁ (C - H) with hx_def
  set y := inner ℝ e₂ (C - H) with hy_def
  have fC' : f C = pt x y := by
    rw [fapply, repr_eq, hx_def.symm, hy_def.symm]
  have heq1 : b * x = b^2 + a * y := by
    simp only [fA, fB, fC'] at hinner1
    simp only [pt_sub] at hinner1
    simp only [inner_pt] at hinner1
    linarith only [hinner1]
  have heq2 : d * x = d^2 + a * y := by
    simp only [fA, fD, fC', pt_sub, inner_pt] at hinner2
    linarith only [hinner2]
  have hxval : x = b + d := by
    have hsub : (b - d) * x = (b - d) * (b + d) := by
      have h : b * x - d * x = b^2 - d^2 := by linarith only [heq1, heq2]
      linear_combination h
    exact (mul_left_cancel₀ hbd hsub)
  have hyval : y = b * d / a := by
    rw [hxval] at heq1
    have h : a * y = b * d := by linarith only [heq1]
    field_simp [hane]
    linarith only [h]
  have fC : f C = pt (b + d) (b * d / a) := by
    rw [fC', hxval, hyval]
  -- `f S`, `f T` from the segment hypotheses.
  obtain ⟨s, hsI, hfs⟩ := hS.map (f.toAffineEquiv.toAffineMap)
  have hfs' : AffineMap.lineMap (f A) (f B) s = f S := hfs
  have hs1 : s < 1 := by
    rcases eq_or_lt_of_le hsI.2 with h1 | h2
    · exfalso
      apply hBS
      have h : f S = f B := by rw [← hfs', h1, AffineMap.lineMap_apply_one]
      exact (f.injective h).symm
    · exact h2
  have fS : f S = pt (s * b) (a * (1 - s)) := by
    rw [← hfs', fA, fB]
    simp only [AffineMap.lineMap_apply_module, pt_smul, pt_add]
    congr 1 <;> simp; ring
  obtain ⟨t, htI, hft⟩ := hT.map (f.toAffineEquiv.toAffineMap)
  have hft' : AffineMap.lineMap (f A) (f D) t = f T := hft
  have ht1 : t < 1 := by
    rcases eq_or_lt_of_le htI.2 with h1 | h2
    · exfalso
      apply hDT
      have h : f T = f D := by rw [← hft', h1, AffineMap.lineMap_apply_one]
      exact (f.injective h).symm
    · exact h2
  have fT : f T = pt (t * d) (a * (1 - t)) := by
    rw [← hft', fA, fD]
    simp only [AffineMap.lineMap_apply_module, pt_smul, pt_add]
    congr 1 <;> simp; ring
  -- The angle conditions at the images.
  have hSa : ∠ (f C) (f H) (f S) = ∠ (f C) (f S) (f B) + Real.pi / 2 := by
    rw [fangle, fangle]
    linarith [hSangle]
  have hTa : ∠ (f T) (f H) (f C) = ∠ (f D) (f T) (f C) + Real.pi / 2 := by
    rw [fangle, fangle]
    linarith [hTangle]
  -- `H` inside the triangle, transported.
  have hHi : f H ∈ interior (convexHull ℝ {f S, f C, f T}) := by
    have hcoe : (f.toHomeomorph : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) = ⇑f :=
      f.coe_toHomeomorph
    have h1 : f H ∈ f '' interior (convexHull ℝ {S, C, T}) := ⟨H, hHin, rfl⟩
    rw [← hcoe, f.toHomeomorph.image_interior, hcoe] at h1
    have hch : ⇑f '' convexHull ℝ {S, C, T} = convexHull ℝ (⇑f '' {S, C, T}) :=
      (f.toAffineEquiv.toAffineMap).image_convexHull {S, C, T}
    have h2 : ⇑f '' {S, C, T} = {f S, f C, f T} := by
      rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
    rw [hch, h2] at h1
    exact h1
  -- Package.
  exact ⟨f, a, b, d, s, t, hapos, hb, hd, hsI.1, hs1, htI.1, ht1,
    fH, fA, fB, fD, fC, fS, fT, hSa, hTa, hHi⟩

/-- Inner products of differences are preserved by an affine isometry. -/
theorem inner_map_vsub_vsub_of_affineIsometry (g : EuclideanSpace ℝ (Fin 2) →ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin 2))
    (x y z w : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (g x - g y) (g z - g w) = inner ℝ (x - y) (z - w) := by
  simp only [← vsub_eq_sub]
  rw [← AffineIsometry.map_vsub, ← AffineIsometry.map_vsub, LinearIsometry.inner_map_map]

snip end

problem imo2014_p3
    (A B C D H S T : EuclideanSpace ℝ (Fin 2))
    (hAIBC : AffineIndependent ℝ ![A, B, C])
    (hAIBD : AffineIndependent ℝ ![A, B, D])
    (hIACD : AffineIndependent ℝ ![A, C, D])
    (hIBCD : AffineIndependent ℝ ![B, C, D])
    (hconv : ∃ X : EuclideanSpace ℝ (Fin 2), Sbtw ℝ A X C ∧ Sbtw ℝ B X D)
    (hABC : ∠ A B C = Real.pi / 2)
    (hCDA : ∠ C D A = Real.pi / 2)
    (hBD : B ≠ D)
    (hHline : H ∈ line[ℝ, B, D])
    (hHperp : inner ℝ (A - H) (D - B) = 0)
    (hS : Wbtw ℝ A S B)
    (hT : Wbtw ℝ A T D)
    (hCH : C ≠ H) (hSH : S ≠ H) (hTH : T ≠ H)
    (hCS : C ≠ S) (hBS : B ≠ S) (hCT : C ≠ T) (hDT : D ≠ T)
    (hHin : H ∈ interior (convexHull ℝ {S, C, T}))
    (hSangle : ∠ C H S - ∠ C S B = Real.pi / 2)
    (hTangle : ∠ T H C - ∠ D T C = Real.pi / 2) :
    ∃ (O : EuclideanSpace ℝ (Fin 2)) (r : ℝ), 0 < r ∧
      dist O T = r ∧ dist O S = r ∧ dist O H = r ∧
      inner ℝ (O - H) (D - B) = 0 := by
  -- Step 1: move to standard coordinates by an isometry.
  obtain ⟨f, a, b, d, s, t, ha, hb, hd, hs0, hs1, ht0, ht1, fH, fA, fB, fD, fC, fS, fT,
    hSa, hTa, hHi⟩ :=
    standardize A B C D H S T hAIBC hAIBD hIACD hIBCD hconv hABC hCDA hBD hHline hHperp
      hS hT hCH hSH hTH hCS hBS hCT hDT hHin hSangle hTangle
  -- Step 2: the polynomial angle conditions, via the geometric bridge.
  rw [fC, fH, fS, fB] at hSa
  rw [fT, fH, fC, fD] at hTa
  rw [fH, fS, fC, fT] at hHi
  have hQt := Qt_of_configuration ha hb hd ht0 ht1 hs0 hs1 hSa hTa hHi
  -- Step 3: the circle in the coordinate model.
  obtain ⟨O', r', hr', hdT', hdS', hdH', hperp'⟩ :=
    model_tangency ha hb hd ht1 hs1 hQt.1 hQt.2
  -- Step 4: transport the circle back along the isometry.
  refine ⟨f.symm O', r', hr', ?_, ?_, ?_, ?_⟩
  · have h := (f.dist_map (f.symm O') T).symm
    rw [h, f.apply_symm_apply, fT, hdT']
  · have h := (f.dist_map (f.symm O') S).symm
    rw [h, f.apply_symm_apply, fS, hdS']
  · have h := (f.dist_map (f.symm O') H).symm
    rw [h, f.apply_symm_apply, fH, hdH']
  · have key := inner_map_vsub_vsub_of_affineIsometry f.toAffineIsometry (f.symm O') H D B
    rw [← key]
    show inner ℝ (f (f.symm O') - f H) (f D - f B) = 0
    rw [f.apply_symm_apply, fH, fD, fB]
    exact hperp'

end Imo2014P3

/-!
## Notes on the proof

Status: SOLVED (no `sorry`). The proof formalizes the following argument (found by
computer-algebra experiments with SymPy and verified numerically before formalizing;
compare Evan Chen's first solution in "IMO 2014 Solution Notes", §1.3).

**Part I (algebraic core).** In standard coordinates `H = (0,0)`, `A = (0,a)`,
`B = (b,0)`, `D = (d,0)`, the right angles `∠ABC = ∠CDA = 90°` force
`C = (b+d, bd/a)` (`B, D` are the intersections of line `BD` with the circle of
diameter `AC`). The angle condition `∠THC − ∠DTC = 90°` at `T = (td, a(1−t))` is
equivalent (Evan Chen's claim: the circumcenter of `△CTH` lies on line `AD`) to the
polynomial `Qt a b d t = 0`, and similarly `Qt a d b s = 0` at `S = (sb, a(1−s))`.
If `P = (0,p)` is the intersection of line `AH` with the perpendicular bisector of
`TH`, then `W = ap` satisfies `W(1−t) = |T|²/2`; eliminating `t` (`elim_T`/`elim_S`,
cofactors from a Gröbner basis computation, discharged by `linear_combination`) gives
the quadratic `σf a b d W = 4a²b²d²W² + 2MN·W − a²MN`, whose coefficients are
*symmetric in `b` and `d`* (`sigma_symm`). Since `σf` has at most one positive root
(`sigma_eq_of_pos`) and the candidates from both sides are positive, they agree:
`p = q`, so the circle centered at `P` with radius `p` passes through `H`, `T`, `S`,
and `PH ⟂ BD` (`model_tangency`).

**Part III (the geometric bridge).** The remaining issue is that squaring the exact
relation `cos ∠THC = −sin ∠DTC` produces a second, spurious algebraic branch `Q̂t`
besides `Qt`. The two branches are separated by the sign of
`crs2 (T−H, C−H) · crs2 (D−T, C−T)` (same sign ⟹ `Qt` branch, via the identity
`T_identity` and `Qt_generic`, used once per side). The identities
`crs2 (D−T, C−T) = b(1−t)(a²+d²)/a` and `crs2 (B−S, C−S) = d(1−s)(a²+b²)/a` reduce
this to the signs of `b` and `d`, and the inside-triangle hypothesis forces
`sign b = −σ`, `sign d = σ` where `σ` is the common sign of the three cross products
at `H` (`cross_signs_of_mem_interior`, via barycentric coordinates; the sign forcing
itself is `claimA`/`claimA'`, a two-step algebraic case analysis). Numerically
(7000 randomized configurations), `H` strictly inside `△SCT` always lands on the
`Qt` branch on both sides.

**Part IV (standardization).** `standardize` transports the abstract configuration to
the coordinate model by an explicit `AffineIsometryEquiv` (translate `H` to the
origin, then the `OrthonormalBasis.repr` of the frame `e₁ ∥ DB`, `e₂ ∥ HA`, which are
orthogonal by the foot-of-perpendicular hypothesis). Nondegeneracies `A ≠ H`,
`B ≠ H`, `D ≠ H` are derived from the angle conditions; the coordinates of `C` come
from the two right angles; `Wbtw` gives `S`, `T` in parametric form with `s, t ∈ [0,1)`
(the bridge and model are stated for `0 ≤ s, t` so no further strictness is needed);
angles and the inside-triangle hypothesis transport via `AffineIsometry.angle_map`
and the homeomorphism. The main theorem then reads off the circle from
`model_tangency` and transports it back.

References: Evan Chen, "IMO 2014 Solution Notes" (web.evanchen.cc/exams/IMO-2014-notes.pdf),
§1.3, first solution (the circumcenter-on-`AD` claim plus the `AP/PH` symmetry
computation); the formalization above replaces his law-of-cosines computation by the
resultant/Gröbner eliminant `σf`, which is symmetric in `b` and `d` by construction.
-/
