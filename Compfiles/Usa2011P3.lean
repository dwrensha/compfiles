/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 2011, Problem 3

In hexagon ABCDEF, which is nonconvex but not self-intersecting, no pair of
opposite sides are parallel. The internal angles satisfy ∠A = 3∠D, ∠C = 3∠F,
and ∠E = 3∠B. Furthermore AB = DE, BC = EF, and CD = FA. Prove that
diagonals AD, BE, and CF are concurrent.

## Formalization notes

We model the plane as `ℂ` and follow the official solution
(see e.g. Evan Chen's USAMO 2011 solution notes).

Write β = ∠B, δ = ∠D, φ = ∠F, so the internal angles at A, C, E are
3δ, 3φ, 3β.  The angle sum of a hexagon then gives β + δ + φ = π.  We encode
the angles as unit complex numbers b = e^{iβ}, d = e^{iδ}, f = e^{iφ}; the
condition β + δ + φ = π becomes `b * d * f = -1`, and 0 < β, δ, φ < π becomes
`0 < b.im` etc.

Assume the hexagon is labelled counterclockwise (as does the official
solution).  The signed turning angle at a vertex with internal angle α is
π - α, so starting from the direction `w` of side A→B, the side directions are

  dir(A→B) = w,        dir(B→C) = -w/b,      dir(C→D) = w/(b*f^3),
  dir(D→E) = w/f^2,    dir(E→F) = -w*d^2/b,  dir(F→A) = -w*d^3.

Given the angle relations, the hypothesis that no two opposite sides are
parallel is equivalent to β, δ, φ ≠ π/2, i.e. `b ≠ I`, `d ≠ I`, `f ≠ I`
(note b = -I etc. is already excluded by `0 < b.im`).  The side length
conditions AB = DE, BC = EF, CD = FA are built in by using the same lengths
p, q, r for opposite sides.

The conclusion "AD, BE, CF are concurrent" is expressed as the existence of a
point lying on all three lines.

The proof follows the official one: the closure equation for the sides shows
that the angles determine the side-length ratios p : q : r uniquely (the
vectors Y = σ₁ + σ₄ and Z = σ₂ + σ₅ are not parallel), the "excellent"
hexagon (where B, D, F are the reflections of E, A, C in the sides of
△ACE) realizes the ratio (sin φ, sin δ, sin β), and in an excellent hexagon
the three diagonals are the altitudes of △ACE, hence concurrent.
-/

namespace Usa2011P3

open Complex ComplexConjugate

/-- The 2-dimensional cross product (signed area) of two vectors of the plane,
seen as complex numbers. -/
def cross (u v : ℂ) : ℝ := u.re * v.im - u.im * v.re

/-- `OnLine H P Q` means that the point `H` lies on the line through `P` and
`Q` (regarded as the whole plane when `P = Q`). -/
def OnLine (H P Q : ℂ) : Prop := cross (H - P) (Q - P) = 0

snip begin

lemma cross_mul (c u v : ℂ) :
    cross (c * u) (c * v) = (c.re ^ 2 + c.im ^ 2) * cross u v := by
  simp only [cross, Complex.mul_re, Complex.mul_im]
  ring

lemma cross_self (u : ℂ) : cross u u = 0 := by simp only [cross]; ring

lemma cross_zero_left (v : ℂ) : cross 0 v = 0 := by simp [cross]

lemma cross_zero_right (u : ℂ) : cross u 0 = 0 := by simp [cross]

lemma two_I_mul_cross (u v : ℂ) :
    2 * I * (cross u v : ℂ) = conj u * v - u * conj v := by
  apply Complex.ext <;> (simp [cross, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im]; try ring)

/-- Two vectors perpendicular to a common nonzero vector are parallel. -/
lemma perp_perp_cross {x y u : ℂ} (hx : (x * conj u).re = 0)
    (hy : (y * conj u).re = 0) (hu : u ≠ 0) : cross x y = 0 := by
  have h1 : x.re * u.re + x.im * u.im = 0 := by
    have h := hx
    simp [Complex.mul_re, Complex.conj_re, Complex.conj_im] at h
    linarith
  have h2 : y.re * u.re + y.im * u.im = 0 := by
    have h := hy
    simp [Complex.mul_re, Complex.conj_re, Complex.conj_im] at h
    linarith
  have hu' : u.re ≠ 0 ∨ u.im ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (Complex.ext h.1 h.2)
  have hu2 : (0:ℝ) < u.re ^ 2 + u.im ^ 2 := by
    rcases hu' with h | h
    · have := sq_pos_of_ne_zero h
      nlinarith [sq_nonneg u.im]
    · have := sq_pos_of_ne_zero h
      nlinarith [sq_nonneg u.re]
  have key : cross x y * (u.re ^ 2 + u.im ^ 2) = 0 := by
    simp only [cross]
    linear_combination h1 * (y.im * u.re - y.re * u.im) -
      h2 * (x.im * u.re - x.re * u.im)
  rcases mul_eq_zero.mp key with h | h
  · exact h
  · exact absurd h (ne_of_gt hu2)

/-- The orthocenter of the triangle `0 c e`, given by the formula
`H = c + e - 2O` where `O` is the circumcenter of the triangle. -/
noncomputable def orthoH (c e : ℂ) : ℂ :=
  let det := c.re * e.im - c.im * e.re
  let hC := (c.re ^ 2 + c.im ^ 2) / 2
  let hE := (e.re ^ 2 + e.im ^ 2) / 2
  ⟨c.re + e.re - 2 * ((hC * e.im - hE * c.im) / det),
   c.im + e.im - 2 * ((c.re * hE - e.re * hC) / det)⟩

/-- The three altitude conditions for `orthoH c e`: it lies on the line
through `0` perpendicular to `e - c`, on the line through `e` perpendicular
to `c`, and on the line through `c` perpendicular to `e`. -/
lemma orthoH_perp (c e : ℂ) (hdet : cross c e ≠ 0) :
    (orthoH c e * conj (e - c)).re = 0 ∧
    ((orthoH c e - e) * conj c).re = 0 ∧
    ((orthoH c e - c) * conj e).re = 0 := by
  have hd : c.re * e.im - c.im * e.re ≠ 0 := by
    simpa [cross] using hdet
  have hd2 : c.re * e.im - e.re * c.im ≠ 0 := by
    rw [mul_comm e.re c.im]
    exact hd
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [orthoH, Complex.mul_re, Complex.sub_re,
      Complex.sub_im, Complex.conj_re, Complex.conj_im] <;>
    field_simp [hd, hd2] <;>
    ring

/-- The vertices of the "excellent" representative hexagon with A = 0 and
side lengths (f.im, d.im, b.im), i.e. (sin φ, sin δ, sin β). -/
noncomputable def vtxC (b d f : ℂ) : ℂ := (f.im : ℂ) + (d.im : ℂ) * (-1 / b)

noncomputable def vtxD (b d f : ℂ) : ℂ := vtxC b d f + (b.im : ℂ) * (1 / (b * f ^ 3))

noncomputable def vtxE (b d f : ℂ) : ℂ := vtxD b d f + (f.im : ℂ) * (1 / f ^ 2)

noncomputable def vtxF (b d f : ℂ) : ℂ := vtxE b d f + (d.im : ℂ) * (-d ^ 2 / b)

/-- The closure equation for the excellent representative:
the six side vectors sum to zero.  Equivalently, the side-length triple
(f.im, d.im, b.im) satisfies the closure constraint. -/
lemma closure_exc {b d f : ℂ} (hb0 : b ≠ 0) (hd0 : d ≠ 0) (hf0 : f ≠ 0)
    (hbdf : b * d * f = -1)
    (hbs : 2 * I * (b.im : ℂ) * b = b ^ 2 - 1)
    (hds : 2 * I * (d.im : ℂ) * d = d ^ 2 - 1)
    (hfs : 2 * I * (f.im : ℂ) * f = f ^ 2 - 1) :
    (f.im : ℂ) * 1 + (d.im : ℂ) * (-1 / b) + (b.im : ℂ) * (1 / (b * f ^ 3)) +
      (f.im : ℂ) * (1 / f ^ 2) + (d.im : ℂ) * (-d ^ 2 / b) +
      (b.im : ℂ) * (-d ^ 3) = 0 := by
  have hM : ((2 : ℂ) * b ^ 2 * d * f ^ 3 * I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (pow_ne_zero 2 hb0)) hd0) (pow_ne_zero 3 hf0)) Complex.I_ne_zero
  have e : (2 : ℂ) * b ^ 2 * d * f ^ 3 * I *
      ((f.im : ℂ) * 1 + (d.im : ℂ) * (-1 / b) + (b.im : ℂ) * (1 / (b * f ^ 3)) +
        (f.im : ℂ) * (1 / f ^ 2) + (d.im : ℂ) * (-d ^ 2 / b) +
        (b.im : ℂ) * (-d ^ 3)) =
      (2 : ℂ) * b * d * I * (b.im : ℂ) + (-2 : ℂ) * b * d * f ^ 3 * I * (d.im : ℂ) +
        (-2 : ℂ) * b * d ^ 3 * f ^ 3 * I * (d.im : ℂ) +
        (-2 : ℂ) * b ^ 2 * d ^ 4 * f ^ 3 * I * (b.im : ℂ) +
        (2 : ℂ) * b ^ 2 * d * f * I * (f.im : ℂ) +
        (2 : ℂ) * b ^ 2 * d * f ^ 3 * I * (f.im : ℂ) := by
    field_simp [hb0, hd0, hf0]
    ring
  have hn : (2 : ℂ) * b * d * I * (b.im : ℂ) + (-2 : ℂ) * b * d * f ^ 3 * I * (d.im : ℂ) +
      (-2 : ℂ) * b * d ^ 3 * f ^ 3 * I * (d.im : ℂ) +
      (-2 : ℂ) * b ^ 2 * d ^ 4 * f ^ 3 * I * (b.im : ℂ) +
      (2 : ℂ) * b ^ 2 * d * f * I * (f.im : ℂ) +
      (2 : ℂ) * b ^ 2 * d * f ^ 3 * I * (f.im : ℂ) = 0 := by
    linear_combination
      (-d + b * f ^ 3 + b * d ^ 2 * f - b ^ 2 * d ^ 3 * f ^ 2) * hbdf +
      (d - b * d ^ 4 * f ^ 3) * hbs +
      (-b * f ^ 3 - b * d ^ 2 * f ^ 3) * hds +
      (b ^ 2 * d + b ^ 2 * d * f ^ 2) * hfs
  rw [hn] at e
  exact (mul_eq_zero.mp e).resolve_left hM

/-- In the excellent representative, the diagonal AD is perpendicular to CE. -/
lemma perp1_exc {b d f : ℂ} (hb0 : b ≠ 0) (hd0 : d ≠ 0) (hf0 : f ≠ 0)
    (hbdf : b * d * f = -1)
    (hcb : conj b = 1 / b) (hcf : conj f = 1 / f)
    (hbs : 2 * I * (b.im : ℂ) * b = b ^ 2 - 1)
    (hds : 2 * I * (d.im : ℂ) * d = d ^ 2 - 1)
    (hfs : 2 * I * (f.im : ℂ) * f = f ^ 2 - 1) :
    vtxD b d f * conj (vtxE b d f - vtxC b d f) +
      conj (vtxD b d f) * (vtxE b d f - vtxC b d f) = 0 := by
  have hM : ((4 : ℂ) * b ^ 2 * d * f ^ 4 * I ^ 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (pow_ne_zero 2 hb0)) hd0) (pow_ne_zero 4 hf0)) (pow_ne_zero 2 Complex.I_ne_zero)
  have e : (4 : ℂ) * b ^ 2 * d * f ^ 4 * I ^ 2 *
      (vtxD b d f * conj (vtxE b d f - vtxC b d f) +
        conj (vtxD b d f) * (vtxE b d f - vtxC b d f)) =
      (4 : ℂ) * b ^ 2 * d * f ^ 2 * I ^ 2 * (f.im : ℂ) ^ 2 +
        (4 : ℂ) * b ^ 2 * d * f ^ 6 * I ^ 2 * (f.im : ℂ) ^ 2 +
        (8 : ℂ) * b ^ 2 * d * f ^ 4 * I ^ 2 * (b.im : ℂ) ^ 2 +
        (-4 : ℂ) * b * d * f ^ 6 * I ^ 2 * (d.im : ℂ) * (f.im : ℂ) +
        (-4 : ℂ) * b ^ 2 * d * f * I ^ 2 * (b.im : ℂ) * (d.im : ℂ) +
        (-4 : ℂ) * b ^ 2 * d * f ^ 7 * I ^ 2 * (b.im : ℂ) * (d.im : ℂ) +
        (-4 : ℂ) * b ^ 3 * d * f ^ 2 * I ^ 2 * (d.im : ℂ) * (f.im : ℂ) +
        (4 : ℂ) * b * d * f * I ^ 2 * (b.im : ℂ) * (f.im : ℂ) +
        (4 : ℂ) * b * d * f ^ 3 * I ^ 2 * (b.im : ℂ) * (f.im : ℂ) +
        (4 : ℂ) * b ^ 3 * d * f ^ 5 * I ^ 2 * (b.im : ℂ) * (f.im : ℂ) +
        (4 : ℂ) * b ^ 3 * d * f ^ 7 * I ^ 2 * (b.im : ℂ) * (f.im : ℂ) := by
    simp only [vtxD, vtxC, vtxE, map_add, map_sub, map_mul, map_neg, map_div₀,
      map_one, map_pow, Complex.conj_ofReal, hcb, hcf]
    field_simp [hb0, hd0, hf0]
    ring
  have hn : (4 : ℂ) * b ^ 2 * d * f ^ 2 * I ^ 2 * (f.im : ℂ) ^ 2 +
      (4 : ℂ) * b ^ 2 * d * f ^ 6 * I ^ 2 * (f.im : ℂ) ^ 2 +
      (8 : ℂ) * b ^ 2 * d * f ^ 4 * I ^ 2 * (b.im : ℂ) ^ 2 +
      (-4 : ℂ) * b * d * f ^ 6 * I ^ 2 * (d.im : ℂ) * (f.im : ℂ) +
      (-4 : ℂ) * b ^ 2 * d * f * I ^ 2 * (b.im : ℂ) * (d.im : ℂ) +
      (-4 : ℂ) * b ^ 2 * d * f ^ 7 * I ^ 2 * (b.im : ℂ) * (d.im : ℂ) +
      (-4 : ℂ) * b ^ 3 * d * f ^ 2 * I ^ 2 * (d.im : ℂ) * (f.im : ℂ) +
      (4 : ℂ) * b * d * f * I ^ 2 * (b.im : ℂ) * (f.im : ℂ) +
      (4 : ℂ) * b * d * f ^ 3 * I ^ 2 * (b.im : ℂ) * (f.im : ℂ) +
      (4 : ℂ) * b ^ 3 * d * f ^ 5 * I ^ 2 * (b.im : ℂ) * (f.im : ℂ) +
      (4 : ℂ) * b ^ 3 * d * f ^ 7 * I ^ 2 * (b.im : ℂ) * (f.im : ℂ) = 0 := by
    linear_combination
      (d + d * f ^ 4 + b ^ 3 * f ^ 3 + b ^ 3 * f ^ 7 - b * f - b * f ^ 5 -
        b ^ 2 * d * f ^ 2 - b ^ 2 * d * f ^ 6) * hbdf +
      (-d + b * f + b * f ^ 7 - d * f ^ 4 + b ^ 2 * d * f ^ 4 + b ^ 2 * d * f ^ 8 -
        b * d ^ 2 * f - b * d ^ 2 * f ^ 7 +
        (4 : ℂ) * b * d * f ^ 4 * I * (b.im : ℂ)) * hbs +
      (b * f ^ 5 + b ^ 3 * f - b * f ^ 7 - b ^ 3 * f ^ 3 +
        (-2 : ℂ) * b ^ 2 * f * I * (b.im : ℂ) +
        (-2 : ℂ) * b ^ 2 * f ^ 7 * I * (b.im : ℂ)) * hds +
      (-b ^ 2 * d + b ^ 2 * d * f ^ 2 + b ^ 2 * d * f ^ 6 - b ^ 2 * d * f ^ 4 +
        (2 : ℂ) * b * d * I * (b.im : ℂ) +
        (-2 : ℂ) * b * d * f ^ 5 * I * (d.im : ℂ) +
        (-2 : ℂ) * b ^ 3 * d * f * I * (d.im : ℂ) +
        (2 : ℂ) * b * d * f ^ 2 * I * (b.im : ℂ) +
        (2 : ℂ) * b ^ 3 * d * f ^ 4 * I * (b.im : ℂ) +
        (2 : ℂ) * b ^ 3 * d * f ^ 6 * I * (b.im : ℂ) +
        (2 : ℂ) * b ^ 2 * d * f * I * (f.im : ℂ) +
        (2 : ℂ) * b ^ 2 * d * f ^ 5 * I * (f.im : ℂ)) * hfs
  rw [hn] at e
  exact (mul_eq_zero.mp e).resolve_left hM

/-- In the excellent representative, the diagonal BE is perpendicular to CA. -/
lemma perp2_exc {b d f : ℂ} (hb0 : b ≠ 0) (hd0 : d ≠ 0) (hf0 : f ≠ 0)
    (hbdf : b * d * f = -1)
    (hcb : conj b = 1 / b) (hcf : conj f = 1 / f)
    (hbs : 2 * I * (b.im : ℂ) * b = b ^ 2 - 1)
    (hds : 2 * I * (d.im : ℂ) * d = d ^ 2 - 1)
    (hfs : 2 * I * (f.im : ℂ) * f = f ^ 2 - 1) :
    (vtxE b d f - (f.im : ℂ)) * conj (vtxC b d f) +
      conj (vtxE b d f - (f.im : ℂ)) * vtxC b d f = 0 := by
  have hM : ((4 : ℂ) * b ^ 2 * d ^ 2 * f ^ 4 * I ^ 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (pow_ne_zero 2 hb0)) (pow_ne_zero 2 hd0)) (pow_ne_zero 4 hf0))
      (pow_ne_zero 2 Complex.I_ne_zero)
  have e : (4 : ℂ) * b ^ 2 * d ^ 2 * f ^ 4 * I ^ 2 *
      ((vtxE b d f - (f.im : ℂ)) * conj (vtxC b d f) +
        conj (vtxE b d f - (f.im : ℂ)) * vtxC b d f) =
      (4 : ℂ) * b ^ 2 * d ^ 2 * f ^ 2 * I ^ 2 * (f.im : ℂ) ^ 2 +
        (4 : ℂ) * b ^ 2 * d ^ 2 * f ^ 6 * I ^ 2 * (f.im : ℂ) ^ 2 +
        (8 : ℂ) * b ^ 2 * d ^ 2 * f ^ 4 * I ^ 2 * (d.im : ℂ) ^ 2 +
        (-4 : ℂ) * b * d ^ 2 * f ^ 4 * I ^ 2 * (d.im : ℂ) * (f.im : ℂ) +
        (-4 : ℂ) * b * d ^ 2 * f ^ 6 * I ^ 2 * (d.im : ℂ) * (f.im : ℂ) +
        (-4 : ℂ) * b ^ 2 * d ^ 2 * f * I ^ 2 * (b.im : ℂ) * (d.im : ℂ) +
        (-4 : ℂ) * b ^ 2 * d ^ 2 * f ^ 7 * I ^ 2 * (b.im : ℂ) * (d.im : ℂ) +
        (-4 : ℂ) * b ^ 3 * d ^ 2 * f ^ 2 * I ^ 2 * (d.im : ℂ) * (f.im : ℂ) +
        (-4 : ℂ) * b ^ 3 * d ^ 2 * f ^ 4 * I ^ 2 * (d.im : ℂ) * (f.im : ℂ) +
        (4 : ℂ) * b * d ^ 2 * f * I ^ 2 * (b.im : ℂ) * (f.im : ℂ) +
        (4 : ℂ) * b ^ 3 * d ^ 2 * f ^ 7 * I ^ 2 * (b.im : ℂ) * (f.im : ℂ) := by
    simp only [vtxD, vtxC, vtxE, map_add, map_sub, map_mul, map_neg, map_div₀,
      map_one, map_pow, Complex.conj_ofReal, hcb, hcf]
    field_simp [hb0, hd0, hf0]
    ring
  have hn : (4 : ℂ) * b ^ 2 * d ^ 2 * f ^ 2 * I ^ 2 * (f.im : ℂ) ^ 2 +
      (4 : ℂ) * b ^ 2 * d ^ 2 * f ^ 6 * I ^ 2 * (f.im : ℂ) ^ 2 +
      (8 : ℂ) * b ^ 2 * d ^ 2 * f ^ 4 * I ^ 2 * (d.im : ℂ) ^ 2 +
      (-4 : ℂ) * b * d ^ 2 * f ^ 4 * I ^ 2 * (d.im : ℂ) * (f.im : ℂ) +
      (-4 : ℂ) * b * d ^ 2 * f ^ 6 * I ^ 2 * (d.im : ℂ) * (f.im : ℂ) +
      (-4 : ℂ) * b ^ 2 * d ^ 2 * f * I ^ 2 * (b.im : ℂ) * (d.im : ℂ) +
      (-4 : ℂ) * b ^ 2 * d ^ 2 * f ^ 7 * I ^ 2 * (b.im : ℂ) * (d.im : ℂ) +
      (-4 : ℂ) * b ^ 3 * d ^ 2 * f ^ 2 * I ^ 2 * (d.im : ℂ) * (f.im : ℂ) +
      (-4 : ℂ) * b ^ 3 * d ^ 2 * f ^ 4 * I ^ 2 * (d.im : ℂ) * (f.im : ℂ) +
      (4 : ℂ) * b * d ^ 2 * f * I ^ 2 * (b.im : ℂ) * (f.im : ℂ) +
      (4 : ℂ) * b ^ 3 * d ^ 2 * f ^ 7 * I ^ 2 * (b.im : ℂ) * (f.im : ℂ) = 0 := by
    linear_combination
      (d ^ 2 - d ^ 2 * f ^ 2 + (2 : ℂ) * b ^ 2 * f ^ 4 + b ^ 3 * d * f ^ 7 -
        b * d * f - b * d * f ^ 3 - b ^ 3 * d * f ^ 5 - b ^ 2 * d ^ 2 * f ^ 4 -
        b ^ 2 * d ^ 2 * f ^ 6 + (2 : ℂ) * b * d ^ 3 * f ^ 3) * hbdf +
      (-d ^ 2 + d ^ 2 * f ^ 2 + b * d * f + b * d * f ^ 7 + b ^ 2 * d ^ 2 * f ^ 8 -
        b * d ^ 3 * f - b * d ^ 3 * f ^ 7 - b ^ 2 * d ^ 2 * f ^ 6) * hbs +
      ((-2 : ℂ) * b ^ 2 * f ^ 4 + b * d * f ^ 3 + b ^ 3 * d * f - b * d * f ^ 7 -
        b ^ 3 * d * f ^ 5 + (2 : ℂ) * b ^ 2 * d ^ 2 * f ^ 4 +
        (-2 : ℂ) * b ^ 2 * d * f * I * (b.im : ℂ) +
        (-2 : ℂ) * b ^ 2 * d * f ^ 7 * I * (b.im : ℂ) +
        (4 : ℂ) * b ^ 2 * d * f ^ 4 * I * (d.im : ℂ)) * hds +
      (-b ^ 2 * d ^ 2 + b ^ 2 * d ^ 2 * f ^ 2 + b ^ 2 * d ^ 2 * f ^ 6 -
        b ^ 2 * d ^ 2 * f ^ 4 + (2 : ℂ) * b * d ^ 2 * I * (b.im : ℂ) +
        (-2 : ℂ) * b * d ^ 2 * f ^ 3 * I * (d.im : ℂ) +
        (-2 : ℂ) * b * d ^ 2 * f ^ 5 * I * (d.im : ℂ) +
        (-2 : ℂ) * b ^ 3 * d ^ 2 * f * I * (d.im : ℂ) +
        (-2 : ℂ) * b ^ 3 * d ^ 2 * f ^ 3 * I * (d.im : ℂ) +
        (2 : ℂ) * b ^ 2 * d ^ 2 * f * I * (f.im : ℂ) +
        (2 : ℂ) * b ^ 3 * d ^ 2 * f ^ 6 * I * (b.im : ℂ) +
        (2 : ℂ) * b ^ 2 * d ^ 2 * f ^ 5 * I * (f.im : ℂ)) * hfs
  rw [hn] at e
  exact (mul_eq_zero.mp e).resolve_left hM

/-- In the excellent representative, the diagonal CF is perpendicular to AE. -/
lemma perp3_exc {b d f : ℂ} (hb0 : b ≠ 0) (hd0 : d ≠ 0) (hf0 : f ≠ 0)
    (hbdf : b * d * f = -1)
    (hcb : conj b = 1 / b) (hcd : conj d = 1 / d) (hcf : conj f = 1 / f)
    (hbs : 2 * I * (b.im : ℂ) * b = b ^ 2 - 1)
    (hds : 2 * I * (d.im : ℂ) * d = d ^ 2 - 1)
    (hfs : 2 * I * (f.im : ℂ) * f = f ^ 2 - 1) :
    (vtxF b d f - vtxC b d f) * conj (vtxE b d f) +
      conj (vtxF b d f - vtxC b d f) * vtxE b d f = 0 := by
  have hM : ((4 : ℂ) * b ^ 2 * d ^ 4 * f ^ 4 * I ^ 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (pow_ne_zero 2 hb0)) (pow_ne_zero 4 hd0)) (pow_ne_zero 4 hf0))
      (pow_ne_zero 2 Complex.I_ne_zero)
  have e : (4 : ℂ) * b ^ 2 * d ^ 4 * f ^ 4 * I ^ 2 *
      ((vtxF b d f - vtxC b d f) * conj (vtxE b d f) +
        conj (vtxF b d f - vtxC b d f) * vtxE b d f) =
      (4 : ℂ) * b ^ 2 * d ^ 2 * f ^ 4 * I ^ 2 * (d.im : ℂ) ^ 2 +
        (4 : ℂ) * b ^ 2 * d ^ 4 * f ^ 2 * I ^ 2 * (f.im : ℂ) ^ 2 +
        (4 : ℂ) * b ^ 2 * d ^ 4 * f ^ 6 * I ^ 2 * (f.im : ℂ) ^ 2 +
        (4 : ℂ) * b ^ 2 * d ^ 6 * f ^ 4 * I ^ 2 * (d.im : ℂ) ^ 2 +
        (8 : ℂ) * b ^ 2 * d ^ 4 * f ^ 4 * I ^ 2 * (b.im : ℂ) ^ 2 +
        (8 : ℂ) * b ^ 2 * d ^ 4 * f ^ 4 * I ^ 2 * (f.im : ℂ) ^ 2 +
        (-4 : ℂ) * b * d ^ 4 * f ^ 6 * I ^ 2 * (d.im : ℂ) * (f.im : ℂ) +
        (-4 : ℂ) * b * d ^ 6 * f ^ 4 * I ^ 2 * (d.im : ℂ) * (f.im : ℂ) +
        (-4 : ℂ) * b * d ^ 6 * f ^ 6 * I ^ 2 * (d.im : ℂ) * (f.im : ℂ) +
        (-4 : ℂ) * b ^ 2 * d ^ 2 * f * I ^ 2 * (b.im : ℂ) * (d.im : ℂ) +
        (-4 : ℂ) * b ^ 2 * d ^ 4 * f * I ^ 2 * (b.im : ℂ) * (d.im : ℂ) +
        (-4 : ℂ) * b ^ 2 * d ^ 4 * f ^ 7 * I ^ 2 * (b.im : ℂ) * (d.im : ℂ) +
        (-4 : ℂ) * b ^ 2 * d ^ 6 * f ^ 7 * I ^ 2 * (b.im : ℂ) * (d.im : ℂ) +
        (-4 : ℂ) * b ^ 3 * d ^ 2 * f ^ 2 * I ^ 2 * (d.im : ℂ) * (f.im : ℂ) +
        (-4 : ℂ) * b ^ 3 * d ^ 2 * f ^ 4 * I ^ 2 * (d.im : ℂ) * (f.im : ℂ) +
        (-4 : ℂ) * b ^ 3 * d ^ 4 * f ^ 2 * I ^ 2 * (d.im : ℂ) * (f.im : ℂ) +
        (4 : ℂ) * b * d ^ 4 * f * I ^ 2 * (b.im : ℂ) * (f.im : ℂ) +
        (4 : ℂ) * b ^ 3 * d ^ 4 * f ^ 7 * I ^ 2 * (b.im : ℂ) * (f.im : ℂ) +
        (8 : ℂ) * b * d ^ 4 * f ^ 3 * I ^ 2 * (b.im : ℂ) * (f.im : ℂ) +
        (8 : ℂ) * b ^ 3 * d ^ 4 * f ^ 5 * I ^ 2 * (b.im : ℂ) * (f.im : ℂ) := by
    simp only [vtxF, vtxD, vtxC, vtxE, map_add, map_sub, map_mul, map_neg,
      map_div₀, map_one, map_pow, Complex.conj_ofReal, hcb, hcd, hcf]
    field_simp [hb0, hd0, hf0]
    ring
  have hn : (4 : ℂ) * b ^ 2 * d ^ 2 * f ^ 4 * I ^ 2 * (d.im : ℂ) ^ 2 +
      (4 : ℂ) * b ^ 2 * d ^ 4 * f ^ 2 * I ^ 2 * (f.im : ℂ) ^ 2 +
      (4 : ℂ) * b ^ 2 * d ^ 4 * f ^ 6 * I ^ 2 * (f.im : ℂ) ^ 2 +
      (4 : ℂ) * b ^ 2 * d ^ 6 * f ^ 4 * I ^ 2 * (d.im : ℂ) ^ 2 +
      (8 : ℂ) * b ^ 2 * d ^ 4 * f ^ 4 * I ^ 2 * (b.im : ℂ) ^ 2 +
      (8 : ℂ) * b ^ 2 * d ^ 4 * f ^ 4 * I ^ 2 * (f.im : ℂ) ^ 2 +
      (-4 : ℂ) * b * d ^ 4 * f ^ 6 * I ^ 2 * (d.im : ℂ) * (f.im : ℂ) +
      (-4 : ℂ) * b * d ^ 6 * f ^ 4 * I ^ 2 * (d.im : ℂ) * (f.im : ℂ) +
      (-4 : ℂ) * b * d ^ 6 * f ^ 6 * I ^ 2 * (d.im : ℂ) * (f.im : ℂ) +
      (-4 : ℂ) * b ^ 2 * d ^ 2 * f * I ^ 2 * (b.im : ℂ) * (d.im : ℂ) +
      (-4 : ℂ) * b ^ 2 * d ^ 4 * f * I ^ 2 * (b.im : ℂ) * (d.im : ℂ) +
      (-4 : ℂ) * b ^ 2 * d ^ 4 * f ^ 7 * I ^ 2 * (b.im : ℂ) * (d.im : ℂ) +
      (-4 : ℂ) * b ^ 2 * d ^ 6 * f ^ 7 * I ^ 2 * (b.im : ℂ) * (d.im : ℂ) +
      (-4 : ℂ) * b ^ 3 * d ^ 2 * f ^ 2 * I ^ 2 * (d.im : ℂ) * (f.im : ℂ) +
      (-4 : ℂ) * b ^ 3 * d ^ 2 * f ^ 4 * I ^ 2 * (d.im : ℂ) * (f.im : ℂ) +
      (-4 : ℂ) * b ^ 3 * d ^ 4 * f ^ 2 * I ^ 2 * (d.im : ℂ) * (f.im : ℂ) +
      (4 : ℂ) * b * d ^ 4 * f * I ^ 2 * (b.im : ℂ) * (f.im : ℂ) +
      (4 : ℂ) * b ^ 3 * d ^ 4 * f ^ 7 * I ^ 2 * (b.im : ℂ) * (f.im : ℂ) +
      (8 : ℂ) * b * d ^ 4 * f ^ 3 * I ^ 2 * (b.im : ℂ) * (f.im : ℂ) +
      (8 : ℂ) * b ^ 3 * d ^ 4 * f ^ 5 * I ^ 2 * (b.im : ℂ) * (f.im : ℂ) = 0 := by
    linear_combination
      (d ^ 4 + b ^ 2 * f ^ 4 + d ^ 4 * f ^ 2 + b * d ^ 5 * f ^ 5 +
        b * d ^ 7 * f ^ 3 + b ^ 2 * d ^ 2 * f ^ 2 + b ^ 3 * d ^ 3 * f ^ 5 +
        b ^ 3 * d ^ 3 * f ^ 7 - b * d * f - b * d ^ 3 * f ^ 5 -
        b ^ 2 * d ^ 4 * f ^ 2 - b ^ 2 * d ^ 6 * f ^ 6 +
        (-2 : ℂ) * b * d ^ 5 * f ^ 3 + (-2 : ℂ) * b ^ 2 * d ^ 2 * f ^ 4) * hbdf +
      (-d ^ 4 - d ^ 4 * f ^ 2 + b * d * f + b * d ^ 3 * f ^ 7 +
        b ^ 2 * d ^ 4 * f ^ 6 + b ^ 2 * d ^ 4 * f ^ 8 - b * d ^ 5 * f -
        b * d ^ 7 * f ^ 7 + (4 : ℂ) * b * d ^ 4 * f ^ 4 * I * (b.im : ℂ)) * hbs +
      (-b ^ 2 * f ^ 4 + b * d ^ 3 * f ^ 5 + b * d ^ 5 * f ^ 3 + b ^ 3 * d * f +
        b ^ 3 * d ^ 3 * f + b ^ 2 * d ^ 2 * f ^ 4 + b ^ 2 * d ^ 6 * f ^ 4 -
        b * d ^ 3 * f ^ 7 - b * d ^ 5 * f ^ 7 - b ^ 3 * d * f ^ 5 -
        b ^ 2 * d ^ 4 * f ^ 4 - b ^ 3 * d ^ 3 * f ^ 3 +
        (-2 : ℂ) * b ^ 2 * d * f * I * (b.im : ℂ) +
        (-2 : ℂ) * b ^ 2 * d ^ 3 * f * I * (b.im : ℂ) +
        (-2 : ℂ) * b ^ 2 * d ^ 3 * f ^ 7 * I * (b.im : ℂ) +
        (-2 : ℂ) * b ^ 2 * d ^ 5 * f ^ 7 * I * (b.im : ℂ) +
        (2 : ℂ) * b ^ 2 * d * f ^ 4 * I * (d.im : ℂ) +
        (2 : ℂ) * b ^ 2 * d ^ 5 * f ^ 4 * I * (d.im : ℂ)) * hds +
      (-b ^ 2 * d ^ 4 + b ^ 2 * d ^ 4 * f ^ 4 + b ^ 2 * d ^ 4 * f ^ 6 -
        b ^ 2 * d ^ 4 * f ^ 2 + (2 : ℂ) * b * d ^ 4 * I * (b.im : ℂ) +
        (-2 : ℂ) * b * d ^ 4 * f ^ 5 * I * (d.im : ℂ) +
        (-2 : ℂ) * b * d ^ 6 * f ^ 3 * I * (d.im : ℂ) +
        (-2 : ℂ) * b * d ^ 6 * f ^ 5 * I * (d.im : ℂ) +
        (-2 : ℂ) * b ^ 3 * d ^ 2 * f * I * (d.im : ℂ) +
        (-2 : ℂ) * b ^ 3 * d ^ 4 * f * I * (d.im : ℂ) +
        (-2 : ℂ) * b ^ 3 * d ^ 2 * f ^ 3 * I * (d.im : ℂ) +
        (2 : ℂ) * b ^ 2 * d ^ 4 * f * I * (f.im : ℂ) +
        (2 : ℂ) * b ^ 3 * d ^ 4 * f ^ 6 * I * (b.im : ℂ) +
        (2 : ℂ) * b ^ 2 * d ^ 4 * f ^ 5 * I * (f.im : ℂ) +
        (4 : ℂ) * b * d ^ 4 * f ^ 2 * I * (b.im : ℂ) +
        (4 : ℂ) * b ^ 3 * d ^ 4 * f ^ 4 * I * (b.im : ℂ) +
        (4 : ℂ) * b ^ 2 * d ^ 4 * f ^ 3 * I * (f.im : ℂ)) * hfs
  rw [hn] at e
  exact (mul_eq_zero.mp e).resolve_left hM

/-- The auxiliary polynomial identity `b * P = f * (b^2 - 1)`, used to show
that the last factor in `crossCE_key` is nonzero. -/
lemma Pkey {b d f : ℂ} (hbdf : b * d * f = -1) :
    b * (b ^ 2 * d * f ^ 4 - b * d ^ 2 * f ^ 3 - b * d ^ 2 * f + b * f ^ 3 +
      b * f - d) = f * (b ^ 2 - 1) := by
  linear_combination (f + b ^ 2 * f ^ 3 - b * d - b * d * f ^ 2) * hbdf

/-- The key computation for the uniqueness of the side-length ratios:
`2 * I * cross Y Z * (b * d^3 * f^3)` in factored form, where
Y = σ₁ + σ₄ and Z = σ₂ + σ₅ are the sums of the directions of opposite
sides. -/
lemma crossYZ_key {b d f : ℂ} (hb0 : b ≠ 0) (hd0 : d ≠ 0) (hf0 : f ≠ 0)
    (hcb : conj b = 1 / b) (hcd : conj d = 1 / d) (hcf : conj f = 1 / f) :
    2 * I * (cross (-1 / b + -d ^ 2 / b) (1 / (b * f ^ 3) + -d ^ 3) : ℂ) *
        (b * d ^ 3 * f ^ 3) =
      (d ^ 2 + 1) * (b * d + f ^ 3) * (b * d ^ 3 * f ^ 3 - 1) := by
  have e1 : conj (-1 / b + -d ^ 2 / b) = -b + -(b / d ^ 2) := by
    simp only [map_add, map_neg, map_div₀, map_one, map_pow, hcb, hcd]
    field_simp [hb0, hd0]
  have e2 : conj (1 / (b * f ^ 3) + -d ^ 3) = b * f ^ 3 + -(1 / d ^ 3) := by
    simp only [map_add, map_neg, map_mul, map_div₀, map_one, map_pow, hcb, hcd, hcf]
    field_simp [hd0, hf0]
  rw [two_I_mul_cross, e1, e2]
  field_simp [hb0, hd0, hf0]
  ring

/-- The key computation for the nondegeneracy of △ACE in the excellent
representative: `2 * I * cross C E * (4 * b^2 * d * f^4)` in factored form. -/
lemma crossCE_key {b d f : ℂ} (hb0 : b ≠ 0) (hf0 : f ≠ 0)
    (hcb : conj b = 1 / b) (hcf : conj f = 1 / f)
    (hbs : 2 * I * (b.im : ℂ) * b = b ^ 2 - 1)
    (hds : 2 * I * (d.im : ℂ) * d = d ^ 2 - 1)
    (hfs : 2 * I * (f.im : ℂ) * f = f ^ 2 - 1) :
    2 * I * (cross (vtxC b d f) (vtxE b d f) : ℂ) * (4 * b ^ 2 * d * f ^ 4) =
      (f ^ 2 - 1) * (b ^ 2 * f ^ 2 - 1) *
        (b ^ 2 * d * f ^ 4 - b * d ^ 2 * f ^ 3 - b * d ^ 2 * f + b * f ^ 3 +
          b * f - d) := by
  rw [two_I_mul_cross]
  have hcC : conj (vtxC b d f) = (f.im : ℂ) + (d.im : ℂ) * (-b) := by
    simp only [vtxC, map_add, map_mul, map_neg, Complex.conj_ofReal, map_div₀,
      map_one, hcb]
    field_simp [hb0]
  have hcE : conj (vtxE b d f) = (f.im : ℂ) + (d.im : ℂ) * (-b) +
      (b.im : ℂ) * (b * f ^ 3) + (f.im : ℂ) * f ^ 2 := by
    simp only [vtxE, vtxD, vtxC, map_add, map_mul, map_neg, Complex.conj_ofReal,
      map_div₀, map_one, map_pow, hcb, hcf]
    field_simp [hb0, hf0]
  have key : I ^ 2 *
      ((conj (vtxC b d f) * vtxE b d f - vtxC b d f * conj (vtxE b d f)) *
          (4 * b ^ 2 * d * f ^ 4) -
        (f ^ 2 - 1) * (b ^ 2 * f ^ 2 - 1) *
          (b ^ 2 * d * f ^ 4 - b * d ^ 2 * f ^ 3 - b * d ^ 2 * f + b * f ^ 3 +
            b * f - d)) = 0 := by
    have e : I ^ 2 *
        ((conj (vtxC b d f) * vtxE b d f - vtxC b d f * conj (vtxE b d f)) *
            (4 * b ^ 2 * d * f ^ 4) -
          (f ^ 2 - 1) * (b ^ 2 * f ^ 2 - 1) *
            (b ^ 2 * d * f ^ 4 - b * d ^ 2 * f ^ 3 - b * d ^ 2 * f + b * f ^ 3 +
              b * f - d)) =
        d * I ^ 2 + b * f ^ 5 * I ^ 2 + b ^ 3 * f ^ 3 * I ^ 2 - b * f * I ^ 2 -
          d * f ^ 2 * I ^ 2 - b ^ 3 * f ^ 7 * I ^ 2 + b * d ^ 2 * f * I ^ 2 +
          b ^ 2 * d * f ^ 6 * I ^ 2 + b ^ 4 * d * f ^ 6 * I ^ 2 +
          b ^ 3 * d ^ 2 * f ^ 7 * I ^ 2 - b * d ^ 2 * f ^ 5 * I ^ 2 -
          b ^ 2 * d * f ^ 2 * I ^ 2 - b ^ 4 * d * f ^ 8 * I ^ 2 -
          b ^ 3 * d ^ 2 * f ^ 3 * I ^ 2 +
          (-4 : ℂ) * b ^ 2 * d * f ^ 6 * I ^ 2 * (f.im : ℂ) ^ 2 +
          (4 : ℂ) * b ^ 2 * d * f ^ 2 * I ^ 2 * (f.im : ℂ) ^ 2 +
          (-4 : ℂ) * b ^ 2 * d * f * I ^ 2 * (b.im : ℂ) * (d.im : ℂ) +
          (-4 : ℂ) * b ^ 3 * d * f ^ 7 * I ^ 2 * (b.im : ℂ) * (f.im : ℂ) +
          (-4 : ℂ) * b ^ 3 * d * f ^ 2 * I ^ 2 * (d.im : ℂ) * (f.im : ℂ) +
          (4 : ℂ) * b * d * f * I ^ 2 * (b.im : ℂ) * (f.im : ℂ) +
          (4 : ℂ) * b * d * f ^ 6 * I ^ 2 * (d.im : ℂ) * (f.im : ℂ) +
          (4 : ℂ) * b ^ 2 * d * f ^ 7 * I ^ 2 * (b.im : ℂ) * (d.im : ℂ) := by
      rw [hcC, hcE]
      simp only [vtxC, vtxD, vtxE]
      field_simp [hb0, hf0]
      ring
    rw [e]
    linear_combination
      (d + b * f ^ 5 + b ^ 3 * f ^ 3 - b * f - d * f ^ 2 - b ^ 3 * f ^ 7 +
        b * d ^ 2 * f + b ^ 2 * d * f ^ 6 + b ^ 4 * d * f ^ 6 +
        b ^ 3 * d ^ 2 * f ^ 7 - b * d ^ 2 * f ^ 5 - b ^ 2 * d * f ^ 2 -
        b ^ 4 * d * f ^ 8 - b ^ 3 * d ^ 2 * f ^ 3) * Complex.I_mul_I +
      (-d + b * f + d * f ^ 2 - b * f ^ 7 + b * d ^ 2 * f ^ 7 +
        b ^ 2 * d * f ^ 6 - b * d ^ 2 * f - b ^ 2 * d * f ^ 8) * hbs +
      (b * f ^ 7 + b ^ 3 * f - b * f ^ 5 - b ^ 3 * f ^ 3 +
        (-2 : ℂ) * b ^ 2 * f * I * (b.im : ℂ) +
        (2 : ℂ) * b ^ 2 * f ^ 7 * I * (b.im : ℂ)) * hds +
      (-b ^ 2 * d + b ^ 2 * d * f ^ 2 + b ^ 2 * d * f ^ 4 - b ^ 2 * d * f ^ 6 +
        (2 : ℂ) * b * d * I * (b.im : ℂ) +
        (-2 : ℂ) * b ^ 3 * d * f * I * (d.im : ℂ) +
        (-2 : ℂ) * b ^ 3 * d * f ^ 6 * I * (b.im : ℂ) +
        (-2 : ℂ) * b ^ 2 * d * f ^ 5 * I * (f.im : ℂ) +
        (2 : ℂ) * b * d * f ^ 5 * I * (d.im : ℂ) +
        (2 : ℂ) * b ^ 2 * d * f * I * (f.im : ℂ)) * hfs
  have hI2 : (I : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 Complex.I_ne_zero
  rcases mul_eq_zero.mp key with h1 | h1
  · exact absurd h1 hI2
  · exact sub_eq_zero.mp h1

lemma ne_zero_of_mul_conj_eq_one {z : ℂ} (h : z * conj z = 1) : z ≠ 0 := by
  rintro rfl
  simp at h

lemma conj_eq_inv_of {z : ℂ} (h : z * conj z = 1) : conj z = 1 / z := by
  have hz := ne_zero_of_mul_conj_eq_one h
  rw [eq_div_iff_mul_eq hz, mul_comm]
  exact h

lemma two_I_im_mul {z : ℂ} (h : z * conj z = 1) :
    2 * I * (z.im : ℂ) * z = z ^ 2 - 1 := by
  have hz := ne_zero_of_mul_conj_eq_one h
  have h2 := Complex.sub_conj z
  rw [conj_eq_inv_of h] at h2
  have h3 : (z - 1 / z) * z = z ^ 2 - 1 := by
    rw [sub_mul, one_div_mul_cancel hz]
    ring
  rw [h2] at h3
  push_cast at h3
  linear_combination h3

lemma ne_one_of_im_pos {z : ℂ} (h : 0 < z.im) : z ≠ 1 := by
  rintro rfl
  simp at h

lemma ne_neg_one_of_im_pos {z : ℂ} (h : 0 < z.im) : z ≠ -1 := by
  rintro rfl
  simp at h

lemma ne_neg_I_of_im_pos {z : ℂ} (h : 0 < z.im) : z ≠ -I := by
  rintro rfl
  rw [Complex.neg_im, Complex.I_im] at h
  linarith

lemma sq_add_one_ne_zero {z : ℂ} (hI : z ≠ I) (him : 0 < z.im) :
    z ^ 2 + 1 ≠ 0 := by
  have hfac : z ^ 2 + 1 = (z - I) * (z + I) := by
    linear_combination Complex.I_mul_I
  rw [hfac]
  intro h
  rcases mul_eq_zero.mp h with h1 | h2
  · exact hI (sub_eq_zero.mp h1)
  · exact ne_neg_I_of_im_pos him (eq_neg_of_add_eq_zero_left h2)

lemma sq_sub_one_ne_zero {z : ℂ} (h1 : z ≠ 1) (h1' : z ≠ -1) :
    z ^ 2 - 1 ≠ 0 := by
  intro h
  have hz : z ^ 2 = 1 := sub_eq_zero.mp h
  rcases sq_eq_one_iff.mp hz with rfl | rfl
  · exact h1 rfl
  · exact h1' rfl

lemma bf_ne_one {b d f : ℂ} (hbdf : b * d * f = -1) (him : 0 < d.im) :
    b * f ≠ 1 := by
  intro h
  have h1 : (b * f) * d = -1 := by
    rw [← hbdf]
    ring
  rw [h, one_mul] at h1
  exact ne_neg_one_of_im_pos him h1

lemma bf_ne_neg_one {b d f : ℂ} (hbdf : b * d * f = -1) (him : 0 < d.im) :
    b * f ≠ -1 := by
  intro h
  have h1 : (b * f) * d = -1 := by
    rw [← hbdf]
    ring
  rw [h, neg_one_mul] at h1
  exact ne_one_of_im_pos him (neg_inj.mp h1)

lemma bd_add_f3_ne_zero {b d f : ℂ} (hbdf : b * d * f = -1)
    (hf1 : f ≠ 1) (hf1' : f ≠ -1) (hfI : f ≠ I) (hfI' : f ≠ -I) :
    b * d + f ^ 3 ≠ 0 := by
  intro h
  have h2 : (b * d + f ^ 3) * f = f ^ 4 - 1 := by
    linear_combination hbdf
  rw [h, zero_mul] at h2
  have h4 : (f ^ 2 - 1) * (f ^ 2 + 1) = 0 := by
    linear_combination -h2
  rcases mul_eq_zero.mp h4 with h5 | h6
  · have hz : f ^ 2 = 1 := sub_eq_zero.mp h5
    rcases sq_eq_one_iff.mp hz with rfl | rfl
    · exact hf1 rfl
    · exact hf1' rfl
  · have hfac : f ^ 2 + 1 = (f - I) * (f + I) := by
      linear_combination Complex.I_mul_I
    rw [hfac] at h6
    rcases mul_eq_zero.mp h6 with h7 | h8
    · exact hfI (sub_eq_zero.mp h7)
    · exact hfI' (eq_neg_of_add_eq_zero_left h8)

lemma bd3f3_sub_one_ne_zero {b d f : ℂ} (hbdf : b * d * f = -1) (hb0 : b ≠ 0)
    (hbI : b ≠ I) (hbI' : b ≠ -I) : b * d ^ 3 * f ^ 3 - 1 ≠ 0 := by
  intro h
  have h1 : b * d ^ 3 * f ^ 3 = -(d ^ 2 * f ^ 2) := by
    have e : b * d ^ 3 * f ^ 3 = (b * d * f) * (d ^ 2 * f ^ 2) := by ring
    rw [e, hbdf]
    ring
  rw [h1] at h
  have h2 : d ^ 2 * f ^ 2 = -1 := neg_eq_iff_eq_neg.mp (sub_eq_zero.mp h)
  have h3 : (d * f) ^ 2 + 1 = 0 := by
    rw [mul_pow]
    linear_combination h2
  have hfac : (d * f) ^ 2 + 1 = (d * f - I) * (d * f + I) := by
    linear_combination Complex.I_mul_I
  rw [hfac] at h3
  have hdf : d * f = -1 / b := by
    have e : b * (d * f) = -1 := by
      rw [← hbdf]
      ring
    rw [eq_div_iff_mul_eq hb0, mul_comm]
    exact e
  rcases mul_eq_zero.mp h3 with h4 | h5
  · have h6 : d * f = I := sub_eq_zero.mp h4
    rw [hdf] at h6
    have h7 : b * I = -1 := by
      have h8 : (-1 / b) * b = I * b := by rw [h6]
      rw [div_mul_cancel₀ _ hb0, mul_comm] at h8
      exact h8.symm
    have h9 : b * I * I = -1 * I := by rw [h7]
    rw [neg_one_mul, mul_assoc, Complex.I_mul_I, mul_neg, mul_one] at h9
    exact hbI (neg_injective h9)
  · have h6 : d * f = -I := eq_neg_of_add_eq_zero_left h5
    rw [hdf] at h6
    have h7 : b * I = 1 := by
      have h8 : (-1 / b) * b = -I * b := by rw [h6]
      rw [div_mul_cancel₀ _ hb0, neg_mul, mul_comm I b] at h8
      exact neg_injective h8.symm
    have h9 : b * I * I = 1 * I := by rw [h7]
    rw [one_mul, mul_assoc, Complex.I_mul_I, mul_neg, mul_one] at h9
    exact hbI' (neg_eq_iff_eq_neg.mp h9)

lemma crossYZ_ne {b d f : ℂ} (hb0 : b ≠ 0) (hd0 : d ≠ 0) (hf0 : f ≠ 0)
    (hcb : conj b = 1 / b) (hcd : conj d = 1 / d) (hcf : conj f = 1 / f)
    (hd2 : d ^ 2 + 1 ≠ 0) (hbdf3 : b * d + f ^ 3 ≠ 0)
    (hbd3f3 : b * d ^ 3 * f ^ 3 - 1 ≠ 0) :
    cross (-1 / b + -d ^ 2 / b) (1 / (b * f ^ 3) + -d ^ 3) ≠ 0 := by
  have key := crossYZ_key hb0 hd0 hf0 hcb hcd hcf
  intro hc
  rw [hc] at key
  simp only [Complex.ofReal_zero, mul_zero, zero_mul] at key
  exact (mul_ne_zero (mul_ne_zero hd2 hbdf3) hbd3f3) key.symm

lemma crossCE_ne {b d f : ℂ} (hb0 : b ≠ 0) (hf0 : f ≠ 0)
    (hbdf : b * d * f = -1)
    (hcb : conj b = 1 / b) (hcf : conj f = 1 / f)
    (hbs : 2 * I * (b.im : ℂ) * b = b ^ 2 - 1)
    (hds : 2 * I * (d.im : ℂ) * d = d ^ 2 - 1)
    (hfs : 2 * I * (f.im : ℂ) * f = f ^ 2 - 1)
    (hf2 : f ^ 2 - 1 ≠ 0) (hbf2 : b ^ 2 * f ^ 2 - 1 ≠ 0)
    (hb2 : b ^ 2 - 1 ≠ 0) :
    cross (vtxC b d f) (vtxE b d f) ≠ 0 := by
  have hP : (b ^ 2 * d * f ^ 4 - b * d ^ 2 * f ^ 3 - b * d ^ 2 * f + b * f ^ 3 +
      b * f - d) ≠ 0 := by
    have hpk := Pkey hbdf
    intro h
    rw [h, mul_zero] at hpk
    exact (mul_ne_zero hf0 hb2) hpk.symm
  have key := crossCE_key hb0 hf0 hcb hcf hbs hds hfs
  intro hc
  rw [hc] at key
  simp only [Complex.ofReal_zero, mul_zero, zero_mul] at key
  exact (mul_ne_zero (mul_ne_zero hf2 hbf2) hP) key.symm

/-- If two real linear combinations of `Y` and `Z` vanish and `Y`, `Z` are
not parallel, then the coefficients vanish. -/
lemma cross_ne_zero_elim {Y Z : ℂ} {s t : ℝ} (hYZ : cross Y Z ≠ 0) (hZ : Z ≠ 0)
    (h : (s : ℂ) * Y + (t : ℂ) * Z = 0) : s = 0 ∧ t = 0 := by
  have hre : s * Y.re + t * Z.re = 0 := by
    have h1 := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.zero_re] at h1
    linarith
  have him : s * Y.im + t * Z.im = 0 := by
    have h1 := congrArg Complex.im h
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.zero_im] at h1
    linarith
  have hs : s * cross Y Z = 0 := by
    simp only [cross]
    linear_combination hre * Z.im - him * Z.re
  have hs0 : s = 0 := by
    rcases mul_eq_zero.mp hs with h1 | h1
    · exact h1
    · exact absurd h1 hYZ
  refine ⟨hs0, ?_⟩
  rw [hs0, Complex.ofReal_zero, zero_mul, zero_add] at h
  rcases mul_eq_zero.mp h with h1 | h1
  · exact Complex.ofReal_eq_zero.mp h1
  · exact absurd h1 hZ

snip end

problem usa2011_p3
    (A B C D E F : ℂ) (b d f w : ℂ) (p q r : ℝ)
    (hw : w * conj w = 1) (hb : b * conj b = 1) (hd : d * conj d = 1)
    (hf : f * conj f = 1) (hbdf : b * d * f = -1)
    (hbpos : 0 < b.im) (hdpos : 0 < d.im) (hfpos : 0 < f.im)
    (hbI : b ≠ I) (hdI : d ≠ I) (hfI : f ≠ I)
    (_hp : 0 < p) (_hq : 0 < q) (_hr : 0 < r)
    (hAB : B - A = (p : ℂ) * w)
    (hBC : C - B = (q : ℂ) * (-1 / b) * w)
    (hCD : D - C = (r : ℂ) * (1 / (b * f ^ 3)) * w)
    (hDE : E - D = (p : ℂ) * (1 / f ^ 2) * w)
    (hEF : F - E = (q : ℂ) * (-d ^ 2 / b) * w)
    (hFA : A - F = (r : ℂ) * (-d ^ 3) * w) :
    ∃ H : ℂ, OnLine H A D ∧ OnLine H B E ∧ OnLine H C F := by
  have hb0 := ne_zero_of_mul_conj_eq_one hb
  have hd0 := ne_zero_of_mul_conj_eq_one hd
  have hf0 := ne_zero_of_mul_conj_eq_one hf
  have hw0 := ne_zero_of_mul_conj_eq_one hw
  have hcb := conj_eq_inv_of hb
  have hcd := conj_eq_inv_of hd
  have hcf := conj_eq_inv_of hf
  have hbs := two_I_im_mul hb
  have hds := two_I_im_mul hd
  have hfs := two_I_im_mul hf
  have hb1 := ne_one_of_im_pos hbpos
  have hb1' := ne_neg_one_of_im_pos hbpos
  have hbI' := ne_neg_I_of_im_pos hbpos
  have hd1 := ne_one_of_im_pos hdpos
  have hd1' := ne_neg_one_of_im_pos hdpos
  have hdI' := ne_neg_I_of_im_pos hdpos
  have hf1 := ne_one_of_im_pos hfpos
  have hf1' := ne_neg_one_of_im_pos hfpos
  have hfI' := ne_neg_I_of_im_pos hfpos
  have hd2 := sq_add_one_ne_zero hdI hdpos
  have hbf1 := bf_ne_one hbdf hdpos
  have hbf1' := bf_ne_neg_one hbdf hdpos
  have hbdf3 := bd_add_f3_ne_zero hbdf hf1 hf1' hfI hfI'
  have hbd3f3 := bd3f3_sub_one_ne_zero hbdf hb0 hbI hbI'
  have hb2 := sq_sub_one_ne_zero hb1 hb1'
  have hf2 := sq_sub_one_ne_zero hf1 hf1'
  have hbf2 : b ^ 2 * f ^ 2 - 1 ≠ 0 := by
    have e : b ^ 2 * f ^ 2 - 1 = (b * f - 1) * (b * f + 1) := by ring
    rw [e]
    exact mul_ne_zero (sub_ne_zero.mpr hbf1) (by
      intro hh
      exact hbf1' (eq_neg_of_add_eq_zero_left hh))
  have hclosure : (p : ℂ) * 1 + (q : ℂ) * (-1 / b) + (r : ℂ) * (1 / (b * f ^ 3)) +
      (p : ℂ) * (1 / f ^ 2) + (q : ℂ) * (-d ^ 2 / b) + (r : ℂ) * (-d ^ 3) = 0 := by
    have hsum : (B - A) + (C - B) + (D - C) + (E - D) + (F - E) + (A - F) =
        w * ((p : ℂ) * 1 + (q : ℂ) * (-1 / b) + (r : ℂ) * (1 / (b * f ^ 3)) +
          (p : ℂ) * (1 / f ^ 2) + (q : ℂ) * (-d ^ 2 / b) + (r : ℂ) * (-d ^ 3)) := by
      rw [hAB, hBC, hCD, hDE, hEF, hFA]
      ring
    have hzero : (B - A) + (C - B) + (D - C) + (E - D) + (F - E) + (A - F) = 0 := by
      ring
    rw [hzero] at hsum
    exact (mul_eq_zero.mp hsum.symm).resolve_left hw0
  have hexc := closure_exc hb0 hd0 hf0 hbdf hbs hds hfs
  set lam := p / f.im with hlam_def
  have hsf0 : (f.im : ℝ) ≠ 0 := ne_of_gt hfpos
  have hp_lam : p = lam * f.im := by
    rw [hlam_def]
    exact (div_mul_cancel₀ p hsf0).symm
  have hcomb : ((p : ℂ) - (lam : ℂ) * (f.im : ℂ)) * (1 + 1 / f ^ 2) +
      ((q : ℂ) - (lam : ℂ) * (d.im : ℂ)) * (-1 / b + -d ^ 2 / b) +
      ((r : ℂ) - (lam : ℂ) * (b.im : ℂ)) * (1 / (b * f ^ 3) + -d ^ 3) = 0 := by
    have e : ((p : ℂ) - (lam : ℂ) * (f.im : ℂ)) * (1 + 1 / f ^ 2) +
        ((q : ℂ) - (lam : ℂ) * (d.im : ℂ)) * (-1 / b + -d ^ 2 / b) +
        ((r : ℂ) - (lam : ℂ) * (b.im : ℂ)) * (1 / (b * f ^ 3) + -d ^ 3) =
        ((p : ℂ) * 1 + (q : ℂ) * (-1 / b) + (r : ℂ) * (1 / (b * f ^ 3)) +
          (p : ℂ) * (1 / f ^ 2) + (q : ℂ) * (-d ^ 2 / b) + (r : ℂ) * (-d ^ 3)) -
        (lam : ℂ) * ((f.im : ℂ) * 1 + (d.im : ℂ) * (-1 / b) +
          (b.im : ℂ) * (1 / (b * f ^ 3)) + (f.im : ℂ) * (1 / f ^ 2) +
          (d.im : ℂ) * (-d ^ 2 / b) + (b.im : ℂ) * (-d ^ 3)) := by ring
    rw [e, hclosure, hexc]
    simp
  have hfst : (p : ℂ) - (lam : ℂ) * (f.im : ℂ) = 0 := by
    rw [hp_lam]
    push_cast
    simp
  rw [hfst, zero_mul, zero_add] at hcomb
  have hcomb2 : ((q - lam * d.im : ℝ) : ℂ) * (-1 / b + -d ^ 2 / b) +
      ((r - lam * b.im : ℝ) : ℂ) * (1 / (b * f ^ 3) + -d ^ 3) = 0 := by
    have e : ((q - lam * d.im : ℝ) : ℂ) = (q : ℂ) - (lam : ℂ) * (d.im : ℂ) := by
      push_cast
      ring
    have e2 : ((r - lam * b.im : ℝ) : ℂ) = (r : ℂ) - (lam : ℂ) * (b.im : ℂ) := by
      push_cast
      ring
    rw [e, e2]
    exact hcomb
  have hcrossYZ := crossYZ_ne hb0 hd0 hf0 hcb hcd hcf hd2 hbdf3 hbd3f3
  have hZne : (1 / (b * f ^ 3) + -d ^ 3) ≠ 0 := by
    have hd2f2 : d ^ 2 * f ^ 2 + 1 ≠ 0 := by
      intro h
      have e : b * d ^ 3 * f ^ 3 - 1 = -(d ^ 2 * f ^ 2 + 1) := by
        have e2 : b * d ^ 3 * f ^ 3 = (b * d * f) * (d ^ 2 * f ^ 2) := by ring
        rw [e2, hbdf]
        ring
      rw [h] at e
      simp at e
      exact hbd3f3 e
    have e : (1 / (b * f ^ 3) + -d ^ 3) * (b * f ^ 3) = 1 + d ^ 2 * f ^ 2 := by
      have h1 : (1 / (b * f ^ 3)) * (b * f ^ 3) = 1 :=
        one_div_mul_cancel (mul_ne_zero hb0 (pow_ne_zero 3 hf0))
      calc (1 / (b * f ^ 3) + -d ^ 3) * (b * f ^ 3)
          = 1 + -(b * d ^ 3 * f ^ 3) := by rw [add_mul, h1]; ring
        _ = 1 + d ^ 2 * f ^ 2 := by
          have h2 : b * d ^ 3 * f ^ 3 = (b * d * f) * (d ^ 2 * f ^ 2) := by ring
          rw [h2, hbdf]; ring
    have h1df2 : 1 + d ^ 2 * f ^ 2 ≠ 0 := by
      rw [add_comm]
      exact hd2f2
    intro hZ
    rw [hZ, zero_mul] at e
    exact h1df2 e.symm
  obtain ⟨hs0, ht0⟩ := cross_ne_zero_elim hcrossYZ hZne hcomb2
  have hq_lam : q = lam * d.im := by linarith
  have hr_lam : r = lam * b.im := by linarith
  have hpc : (p : ℂ) = (lam : ℂ) * (f.im : ℂ) := by
    rw [hp_lam]
    push_cast
    ring
  have hqc : (q : ℂ) = (lam : ℂ) * (d.im : ℂ) := by
    rw [hq_lam]
    push_cast
    ring
  have hrc : (r : ℂ) = (lam : ℂ) * (b.im : ℂ) := by
    rw [hr_lam]
    push_cast
    ring
  have hB : B = A + w * (lam : ℂ) * (f.im : ℂ) := by
    have e := hAB
    rw [hpc] at e
    have h2 : B = A + (B - A) := by ring
    rw [h2, e]
    ring
  have hC : C = A + w * (lam : ℂ) * vtxC b d f := by
    have e : C = A + ((C - B) + (B - A)) := by ring
    rw [hBC, hAB, hqc, hpc] at e
    rw [e]
    simp only [vtxC]
    ring
  have hD : D = A + w * (lam : ℂ) * vtxD b d f := by
    have e : D = A + ((D - C) + (C - B) + (B - A)) := by ring
    rw [hCD, hBC, hAB, hrc, hqc, hpc] at e
    rw [e]
    simp only [vtxD, vtxC]
    ring
  have hE : E = A + w * (lam : ℂ) * vtxE b d f := by
    have e : E = A + ((E - D) + (D - C) + (C - B) + (B - A)) := by ring
    rw [hDE, hCD, hBC, hAB, hpc, hrc, hqc] at e
    rw [e]
    simp only [vtxE, vtxD, vtxC]
    ring
  have hF : F = A + w * (lam : ℂ) * vtxF b d f := by
    have e : F = A + ((F - E) + (E - D) + (D - C) + (C - B) + (B - A)) := by ring
    rw [hEF, hDE, hCD, hBC, hAB, hqc, hpc, hrc] at e
    rw [e]
    simp only [vtxF, vtxE, vtxD, vtxC]
    ring
  have hce : cross (vtxC b d f) (vtxE b d f) ≠ 0 :=
    crossCE_ne hb0 hf0 hbdf hcb hcf hbs hds hfs hf2 hbf2 hb2
  have hC0ne : vtxC b d f ≠ 0 := by
    intro h
    rw [h, cross_zero_left] at hce
    exact hce rfl
  have hE0ne : vtxE b d f ≠ 0 := by
    intro h
    rw [h, cross_zero_right] at hce
    exact hce rfl
  have hEC : vtxE b d f - vtxC b d f ≠ 0 := by
    intro h
    have h2 : vtxE b d f = vtxC b d f := sub_eq_zero.mp h
    rw [h2, cross_self] at hce
    exact hce rfl
  obtain ⟨horth1, horth2, horth3⟩ := orthoH_perp (vtxC b d f) (vtxE b d f) hce
  have hperp1 : (vtxD b d f * conj (vtxE b d f - vtxC b d f)).re = 0 := by
    have h := perp1_exc hb0 hd0 hf0 hbdf hcb hcf hbs hds hfs
    have e : conj (vtxD b d f) * (vtxE b d f - vtxC b d f) =
        conj (vtxD b d f * conj (vtxE b d f - vtxC b d f)) := by
      simp [map_mul, map_sub]
    rw [e, Complex.add_conj] at h
    have h2 := Complex.ofReal_eq_zero.mp h
    linarith
  have hperp2 : ((vtxE b d f - (f.im : ℂ)) * conj (vtxC b d f)).re = 0 := by
    have h := perp2_exc hb0 hd0 hf0 hbdf hcb hcf hbs hds hfs
    have e : conj (vtxE b d f - (f.im : ℂ)) * vtxC b d f =
        conj ((vtxE b d f - (f.im : ℂ)) * conj (vtxC b d f)) := by
      simp [map_mul, map_sub]
    rw [e, Complex.add_conj] at h
    have h2 := Complex.ofReal_eq_zero.mp h
    linarith
  have hperp3 : ((vtxF b d f - vtxC b d f) * conj (vtxE b d f)).re = 0 := by
    have h := perp3_exc hb0 hd0 hf0 hbdf hcb hcd hcf hbs hds hfs
    have e : conj (vtxF b d f - vtxC b d f) * vtxE b d f =
        conj ((vtxF b d f - vtxC b d f) * conj (vtxE b d f)) := by
      simp [map_mul, map_sub]
    rw [e, Complex.add_conj] at h
    have h2 := Complex.ofReal_eq_zero.mp h
    linarith
  have hcross_HD : cross (orthoH (vtxC b d f) (vtxE b d f)) (vtxD b d f) = 0 :=
    perp_perp_cross horth1 hperp1 hEC
  have hcross_HB : cross (orthoH (vtxC b d f) (vtxE b d f) - (f.im : ℂ))
      (vtxE b d f - (f.im : ℂ)) = 0 := by
    apply perp_perp_cross (u := -vtxC b d f)
    · have e1 : orthoH (vtxC b d f) (vtxE b d f) - (f.im : ℂ) =
          (orthoH (vtxC b d f) (vtxE b d f) - vtxE b d f) +
            (vtxE b d f - (f.im : ℂ)) := by ring
      rw [e1, add_mul]
      have g1 : ((orthoH (vtxC b d f) (vtxE b d f) - vtxE b d f) *
          conj (-vtxC b d f)).re = 0 := by
        have g : conj (-vtxC b d f) = -conj (vtxC b d f) := by simp
        rw [g, mul_neg]
        simp only [Complex.neg_re, horth2, neg_zero]
      have g2 : ((vtxE b d f - (f.im : ℂ)) * conj (-vtxC b d f)).re = 0 := by
        have g : conj (-vtxC b d f) = -conj (vtxC b d f) := by simp
        rw [g, mul_neg]
        simp only [Complex.neg_re, hperp2, neg_zero]
      simp only [Complex.add_re, g1, g2, add_zero]
    · have g : conj (-vtxC b d f) = -conj (vtxC b d f) := by simp
      rw [g, mul_neg]
      simp only [Complex.neg_re, hperp2, neg_zero]
    · exact neg_ne_zero.mpr hC0ne
  have hcross_HC : cross (orthoH (vtxC b d f) (vtxE b d f) - vtxC b d f)
      (vtxF b d f - vtxC b d f) = 0 := by
    apply perp_perp_cross (u := -vtxE b d f)
    · have g : conj (-vtxE b d f) = -conj (vtxE b d f) := by simp
      rw [g, mul_neg]
      simp only [Complex.neg_re, horth3, neg_zero]
    · have g : conj (-vtxE b d f) = -conj (vtxE b d f) := by simp
      rw [g, mul_neg]
      simp only [Complex.neg_re, hperp3, neg_zero]
    · exact neg_ne_zero.mpr hE0ne
  refine ⟨A + w * (lam : ℂ) * orthoH (vtxC b d f) (vtxE b d f), ?_, ?_, ?_⟩
  · have e1 : A + w * (lam : ℂ) * orthoH (vtxC b d f) (vtxE b d f) - A =
        (w * (lam : ℂ)) * orthoH (vtxC b d f) (vtxE b d f) := by ring
    have e2 : D - A = (w * (lam : ℂ)) * vtxD b d f := by
      rw [hD]
      ring
    show cross (A + w * (lam : ℂ) * orthoH (vtxC b d f) (vtxE b d f) - A)
      (D - A) = 0
    rw [e1, e2, cross_mul, hcross_HD]
    ring
  · have e1 : A + w * (lam : ℂ) * orthoH (vtxC b d f) (vtxE b d f) - B =
        (w * (lam : ℂ)) * (orthoH (vtxC b d f) (vtxE b d f) - (f.im : ℂ)) := by
      rw [hB]
      ring
    have e2 : E - B = (w * (lam : ℂ)) * (vtxE b d f - (f.im : ℂ)) := by
      rw [hE, hB]
      ring
    show cross (A + w * (lam : ℂ) * orthoH (vtxC b d f) (vtxE b d f) - B)
      (E - B) = 0
    rw [e1, e2, cross_mul, hcross_HB]
    ring
  · have e1 : A + w * (lam : ℂ) * orthoH (vtxC b d f) (vtxE b d f) - C =
        (w * (lam : ℂ)) * (orthoH (vtxC b d f) (vtxE b d f) - vtxC b d f) := by
      rw [hC]
      ring
    have e2 : F - C = (w * (lam : ℂ)) * (vtxF b d f - vtxC b d f) := by
      rw [hF, hC]
      ring
    show cross (A + w * (lam : ℂ) * orthoH (vtxC b d f) (vtxE b d f) - C)
      (F - C) = 0
    rw [e1, e2, cross_mul, hcross_HC]
    ring

end Usa2011P3
