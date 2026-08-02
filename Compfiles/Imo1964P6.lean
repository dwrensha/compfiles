/- Copyright (c) 2026 The Compfiles Contributors. All rights reserved. Released under Apache 2.0 license as described in the file LICENSE. Authors: -/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1964, Problem 6

ABCD is a tetrahedron and D₀ is the centroid of ABC. Lines parallel to DD₀
are drawn through A, B and C and meet the planes BCD, CAD and ABD in A₀, B₀,
and C₀ respectively. Prove that the volume of ABCD is one-third of the volume
of A₀B₀C₀D₀. Is the result true if D₀ is an arbitrary point inside ABC?
-/

namespace Imo1964P6

/-- The volume of a tetrahedron with vertices `P₁`, `P₂`, `P₃`, `P₄` in
3-dimensional real space, given as one sixth of the absolute value of the
determinant whose rows are the three edge vectors emanating from `P₁`. -/
noncomputable def tetrahedronVolume (P₁ P₂ P₃ P₄ : Fin 3 → ℝ) : ℝ :=
  |Matrix.det (Matrix.of ![P₂ - P₁, P₃ - P₁, P₄ - P₁])| / 6

snip begin

/-- Cyclic rotation of a linearly independent triple of vectors preserves
linear independence. -/
lemma linearIndependent_rotate {a b c : Fin 3 → ℝ}
    (h : LinearIndependent ℝ ![a, b, c]) :
    LinearIndependent ℝ ![b, c, a] := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro g hg
  rw [Fin.sum_univ_three] at hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at hg
  have h2 : g 2 • a + g 0 • b + g 1 • c = 0 := by
    calc g 2 • a + g 0 • b + g 1 • c = g 0 • b + g 1 • c + g 2 • a := by abel
    _ = 0 := hg
  have key := h ![g 2, g 0, g 1] (by
    rw [Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    exact h2)
  intro i
  fin_cases i
  · simpa using key 1
  · simpa using key 2
  · simpa using key 0

/-- Let `a`, `b`, `c` be linearly independent vectors in `ℝ³` and let
`v = q • a + r • b + s • c` with `q ≠ 0`. If a point `p` lies both in the
plane spanned by `b` and `c` and on the line through `a` parallel to `v`, then
`p` is uniquely determined, namely `p = (-r / q) • b + (-s / q) • c`.

This is the computation behind the construction of the points `A₀`, `B₀`, `C₀`
in the problem, in coordinates relative to `D`: for `A₀` one takes
`a = A - D`, `b = B - D`, `c = C - D` and `v = D₀ - D`. -/
lemma eq_of_mem_span_of_parallel {a b c p v : Fin 3 → ℝ} {t x y q r s : ℝ}
    (hind : LinearIndependent ℝ ![a, b, c])
    (hv : v = q • a + r • b + s • c)
    (hq : q ≠ 0)
    (hmem : x • b + y • c = p)
    (hpar : p - a = t • v) :
    p = (-r / q) • b + (-s / q) • c := by
  have key : (-1 - t * q) • a + (x - t * r) • b + (y - t * s) • c = 0 := by
    have expand : (-1 - t * q) • a + (x - t * r) • b + (y - t * s) • c =
        (p - a) - t • v := by
      rw [← hmem, hv]
      module
    rw [expand, hpar, sub_self]
  have hli := Fintype.linearIndependent_iff.mp hind
  have hsum : ∑ i : Fin 3, ![-1 - t * q, x - t * r, y - t * s] i • ![a, b, c] i = 0 := by
    rw [Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    exact key
  have hc := hli _ hsum
  have hc0 : -1 - t * q = 0 := by simpa using hc 0
  have hc1 : x - t * r = 0 := by simpa using hc 1
  have hc2 : y - t * s = 0 := by simpa using hc 2
  have htq : t * q = -1 := by linarith
  have hxq : x * q = -r := by
    have hx' : x = t * r := by linarith
    calc x * q = r * (t * q) := by rw [hx']; ring
    _ = -r := by rw [htq]; ring
  have hyq : y * q = -s := by
    have hy' : y = t * s := by linarith
    calc y * q = s * (t * q) := by rw [hy']; ring
    _ = -s := by rw [htq]; ring
  have hx : x = -r / q := (eq_div_iff hq).mpr hxq
  have hy : y = -s / q := (eq_div_iff hq).mpr hyq
  rw [← hmem, hx, hy]

/-- The determinant identity behind the volume computation. In coordinates
relative to `D`, write `a = A - D`, `b = B - D`, `c = C - D` and
`D₀ - D = p • a + q • b + r • c` with `p + q + r = 1`. Then the rows of the
determinant computing the volume of `A₀B₀C₀D₀` are `B₀ - A₀`, `C₀ - A₀`,
`D₀ - A₀`, and the claim is that this determinant is `-3` times the
determinant computing the volume of `ABCD` (whose rows can be taken to be
`b - a`, `c - a`, `-a`). -/
lemma det_eq_neg_three_mul_det (a b c : Fin 3 → ℝ) {p q r : ℝ}
    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) (hpqr : p + q + r = 1) :
    Matrix.det (Matrix.of ![((-r / q) • c + (-p / q) • a) - ((-q / p) • b + (-r / p) • c),
      ((-p / r) • a + (-q / r) • b) - ((-q / p) • b + (-r / p) • c),
      (p • a + q • b + r • c) - ((-q / p) • b + (-r / p) • c)]) =
    -3 * Matrix.det (Matrix.of ![b - a, c - a, -a]) := by
  have hrw : r = 1 - p - q := by linarith
  subst hrw
  simp only [Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply,
    smul_eq_mul]
  field_simp
  ring

snip end

/-- Second part of the problem: the answer is "yes" — the result remains true
if `D₀` is an arbitrary point of the triangle `ABC`, or indeed any point of
its plane not on the lines `BC`, `CA`, `AB`. We write `D₀` in barycentric
coordinates relative to `D`: `D₀ - D = p • (A - D) + q • (B - D) + r • (C - D)`
with `p + q + r = 1`; the conditions `p ≠ 0`, `q ≠ 0`, `r ≠ 0` say that `D₀`
does not lie on the lines `BC`, `CA`, `AB` respectively, which is needed for
the points `A₀`, `B₀`, `C₀` to be well-defined. -/
problem imo1964_p6_general
    (A B C D A₀ B₀ C₀ D₀ : Fin 3 → ℝ)
    (p q r : ℝ)
    (hpqr : p + q + r = 1)
    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (hD : LinearIndependent ℝ ![A - D, B - D, C - D])
    (hD₀ : D₀ - D = p • (A - D) + q • (B - D) + r • (C - D))
    (hA₀ : A₀ - D ∈ Submodule.span ℝ ({B - D, C - D} : Set (Fin 3 → ℝ)))
    (hB₀ : B₀ - D ∈ Submodule.span ℝ ({C - D, A - D} : Set (Fin 3 → ℝ)))
    (hC₀ : C₀ - D ∈ Submodule.span ℝ ({A - D, B - D} : Set (Fin 3 → ℝ)))
    (hparA : ∃ t : ℝ, A₀ - A = t • (D₀ - D))
    (hparB : ∃ t : ℝ, B₀ - B = t • (D₀ - D))
    (hparC : ∃ t : ℝ, C₀ - C = t • (D₀ - D)) :
    tetrahedronVolume A B C D = tetrahedronVolume A₀ B₀ C₀ D₀ / 3 := by
  rw [Submodule.mem_span_pair] at hA₀ hB₀ hC₀
  obtain ⟨xA, yA, hA₀⟩ := hA₀
  obtain ⟨xB, yB, hB₀⟩ := hB₀
  obtain ⟨xC, yC, hC₀⟩ := hC₀
  obtain ⟨tA, htA⟩ := hparA
  obtain ⟨tB, htB⟩ := hparB
  obtain ⟨tC, htC⟩ := hparC
  have hvB : D₀ - D = q • (B - D) + r • (C - D) + p • (A - D) := by
    rw [hD₀]; module
  have hvC : D₀ - D = r • (C - D) + p • (A - D) + q • (B - D) := by
    rw [hD₀]; module
  have hparA' : (A₀ - D) - (A - D) = tA • (D₀ - D) := by
    have h : (A₀ - D) - (A - D) = A₀ - A := by module
    rw [h]; exact htA
  have hparB' : (B₀ - D) - (B - D) = tB • (D₀ - D) := by
    have h : (B₀ - D) - (B - D) = B₀ - B := by module
    rw [h]; exact htB
  have hparC' : (C₀ - D) - (C - D) = tC • (D₀ - D) := by
    have h : (C₀ - D) - (C - D) = C₀ - C := by module
    rw [h]; exact htC
  have hA₀' : A₀ - D = (-q / p) • (B - D) + (-r / p) • (C - D) :=
    eq_of_mem_span_of_parallel hD hD₀ hp hA₀ hparA'
  have hB₀' : B₀ - D = (-r / q) • (C - D) + (-p / q) • (A - D) :=
    eq_of_mem_span_of_parallel (linearIndependent_rotate hD) hvB hq hB₀ hparB'
  have hC₀' : C₀ - D = (-p / r) • (A - D) + (-q / r) • (B - D) :=
    eq_of_mem_span_of_parallel (linearIndependent_rotate (linearIndependent_rotate hD))
      hvC hr hC₀ hparC'
  have e1 : B₀ - A₀ = ((-r / q) • (C - D) + (-p / q) • (A - D)) -
      ((-q / p) • (B - D) + (-r / p) • (C - D)) := by
    have h : B₀ - A₀ = (B₀ - D) - (A₀ - D) := by module
    rw [h, hB₀', hA₀']
  have e2 : C₀ - A₀ = ((-p / r) • (A - D) + (-q / r) • (B - D)) -
      ((-q / p) • (B - D) + (-r / p) • (C - D)) := by
    have h : C₀ - A₀ = (C₀ - D) - (A₀ - D) := by module
    rw [h, hC₀', hA₀']
  have e3 : D₀ - A₀ = (p • (A - D) + q • (B - D) + r • (C - D)) -
      ((-q / p) • (B - D) + (-r / p) • (C - D)) := by
    have h : D₀ - A₀ = (D₀ - D) - (A₀ - D) := by module
    rw [h, hD₀, hA₀']
  have e4 : B - A = (B - D) - (A - D) := by module
  have e5 : C - A = (C - D) - (A - D) := by module
  have e6 : D - A = -(A - D) := by module
  unfold tetrahedronVolume
  rw [e1, e2, e3, e4, e5, e6]
  rw [det_eq_neg_three_mul_det (A - D) (B - D) (C - D) hp hq hr hpqr]
  have h3 : |(-3 : ℝ)| = 3 := by norm_num
  rw [abs_mul, h3]
  ring

/-- The main statement of the problem: `D₀` is the centroid of `ABC`, and the
volume of `ABCD` is one third of the volume of `A₀B₀C₀D₀`. This is the special
case `p = q = r = 1 / 3` of `imo1964_p6_general`. -/
problem imo1964_p6
    (A B C D A₀ B₀ C₀ D₀ : Fin 3 → ℝ)
    (hD : LinearIndependent ℝ ![A - D, B - D, C - D])
    (hD₀ : D₀ = (1 / 3 : ℝ) • (A + B + C))
    (hA₀ : A₀ - D ∈ Submodule.span ℝ ({B - D, C - D} : Set (Fin 3 → ℝ)))
    (hB₀ : B₀ - D ∈ Submodule.span ℝ ({C - D, A - D} : Set (Fin 3 → ℝ)))
    (hC₀ : C₀ - D ∈ Submodule.span ℝ ({A - D, B - D} : Set (Fin 3 → ℝ)))
    (hparA : ∃ t : ℝ, A₀ - A = t • (D₀ - D))
    (hparB : ∃ t : ℝ, B₀ - B = t • (D₀ - D))
    (hparC : ∃ t : ℝ, C₀ - C = t • (D₀ - D)) :
    tetrahedronVolume A B C D = tetrahedronVolume A₀ B₀ C₀ D₀ / 3 := by
  have hD₀' : D₀ - D = (1 / 3 : ℝ) • (A - D) + (1 / 3 : ℝ) • (B - D) +
      (1 / 3 : ℝ) • (C - D) := by
    rw [hD₀]; module
  exact imo1964_p6_general A B C D A₀ B₀ C₀ D₀ (1 / 3) (1 / 3) (1 / 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hD hD₀' hA₀ hB₀ hC₀
    hparA hparB hparC

end Imo1964P6
