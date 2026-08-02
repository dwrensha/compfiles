/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Geometry.Euclidean.Triangle
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 2024, Problem 5

Point D is selected inside acute triangle ABC so that ∠DAC = ∠ACB and
∠BDC = 90° + ∠BAC. Point E is chosen on ray BD so that AE = EC. Let M be
the midpoint of BC. Show that line AB is tangent to the circumcircle of
triangle BEM.

# Remarks on the formalization

* Since the problem is invariant under reflection, we may (and do) assume that
  the triangle is positively oriented; `horient` says that the signed area
  `cr (B - A) (C - A)` is positive, where `cr` is the 2-dimensional cross
  product (signed area form).
* "D lies strictly inside triangle ABC" is encoded by the three side tests
  `hD1`, `hD2`, `hD3`: D is on the same side of each edge as the opposite
  vertex.
* "Line AB is tangent to the circumcircle of △BEM" is encoded as: there is a
  circle through B, E and M whose center O satisfies `⟪A - B, O - B⟫ = 0`,
  i.e. the tangent to the circle at B is perpendicular to the radius OB.
* Proof outline. Write vectors from B as `a = A - B`, `c = C - B`, `d = D - B`.
  After clearing denominators, the angle condition `∠BDC = π/2 + ∠BAC` becomes
  the polynomial constraint `C1f a c d = 0` (D lies on a certain circle through
  B and C), and `∠DAC = ∠ACB` becomes `C2f a c d = 0` (D - A is parallel to an
  explicitly known direction `d1dir a c`). The tangency conclusion becomes a
  polynomial identity. The heart of the proof is the identity

    |a-c|²·G' + cr a c·(|a|²-|c|²)·C1 = (|c|²⟨a,d⟩ - |a|²⟨c,d⟩)·C2

  (`master_id`), found by computer algebra and checked by `ring`. The only
  degenerate case left over, `⟪A - C, D - B⟫ = 0`, forces `BA = BC`, hence
  `∠BAC = ∠BCA = ∠DAC`, which would put D on line AB, contradicting the
  hypothesis that D lies strictly inside the triangle.
-/

namespace Usa2024P5

open EuclideanGeometry RealInnerProductSpace

open scoped Real

snip begin

/-- The plane, as a concrete inner product space for computation. -/
abbrev E2 := EuclideanSpace ℝ (Fin 2)

/-- The 2-dimensional cross product (signed area form), in coordinates. -/
noncomputable def cr (u v : E2) : ℝ := u 0 * v 1 - u 1 * v 0

/-- Rotation by 90 degrees counterclockwise. -/
noncomputable def J (u : E2) : E2 := !₂[-u 1, u 0]

lemma inner_eq (u v : E2) : ⟪u, v⟫ = u 0 * v 0 + u 1 * v 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

lemma norm_sq_eq (u : E2) : ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_eq]; ring

@[simp] lemma cr_self (u : E2) : cr u u = 0 := by simp only [cr]; ring
lemma cr_zero_left (v : E2) : cr 0 v = 0 := by simp only [cr, PiLp.zero_apply]; ring
lemma cr_zero_right (u : E2) : cr u 0 = 0 := by simp only [cr, PiLp.zero_apply]; ring
lemma cr_J (u v : E2) : cr u (J v) = ⟪u, v⟫ := by
  simp only [cr, J, Matrix.cons_val_zero, Matrix.cons_val_one, inner_eq]; ring
lemma inner_Jl (u v : E2) : ⟪J u, v⟫ = cr u v := by
  simp only [cr, J, Matrix.cons_val_zero, Matrix.cons_val_one, inner_eq]; ring
lemma inner_Jr (u v : E2) : ⟪u, J v⟫ = cr v u := by
  simp only [cr, J, Matrix.cons_val_zero, Matrix.cons_val_one, inner_eq]; ring

/-- The sine of the angle between two vectors, via the cross product. -/
lemma sin_angle_eq (x y : E2) (hx : x ≠ 0) (hy : y ≠ 0) :
    Real.sin (InnerProductGeometry.angle x y) = |cr x y| / (‖x‖ * ‖y‖) := by
  rw [InnerProductGeometry.sin_angle hx hy]
  congr 1
  have h : ⟪x, x⟫ * ⟪y, y⟫ - ⟪x, y⟫ * ⟪x, y⟫ = (cr x y) ^ 2 := by
    simp only [inner_eq, cr]; ring
  rw [h, Real.sqrt_sq_eq_abs]

/-- The angle between three points is the angle between the difference vectors. -/
lemma angleE (x y z : E2) : ∠ x y z = InnerProductGeometry.angle (x - y) (z - y) := by
  simp only [EuclideanGeometry.angle, vsub_eq_sub]

/-- A vector orthogonal to a nonzero vector `w`, with vanishing cross product
with `w`, is zero. -/
lemma uniq {z w : E2} (hw : w ≠ 0) (h1 : ⟪z, w⟫ = 0) (h2 : cr z w = 0) : z = 0 := by
  rw [inner_eq] at h1
  simp only [cr] at h2
  have hw2 : w 0 ^ 2 + w 1 ^ 2 ≠ 0 := by
    intro h
    have h0 : w 0 = 0 := by nlinarith [sq_nonneg (w 0), sq_nonneg (w 1)]
    have h1' : w 1 = 0 := by nlinarith [sq_nonneg (w 0), sq_nonneg (w 1)]
    exact hw (by ext i; fin_cases i <;> simp [h0, h1'])
  have hz0 : z 0 = 0 := by
    have h : z 0 * (w 0 ^ 2 + w 1 ^ 2) = 0 := by linear_combination h1 * w 0 + h2 * w 1
    exact mul_eq_zero.mp h |>.resolve_right hw2
  have hz1 : z 1 = 0 := by
    have h : z 1 * (w 0 ^ 2 + w 1 ^ 2) = 0 := by linear_combination h1 * w 1 - h2 * w 0
    exact mul_eq_zero.mp h |>.resolve_right hw2
  ext i; fin_cases i <;> simp [hz0, hz1]

/-- The direction of the ray `AD` (up to a positive scalar factor): this is the
rotation of `C - A` by the angle `-∠ACB`, with the positive factor
`|AC| * |BC|` dropped. Here `a = A - B` and `c = C - B`. -/
noncomputable def d1dir (a c : E2) : E2 := ⟪a - c, -c⟫ • (c - a) - cr (a - c) (-c) • J (c - a)

/-- The condition `∠BDC = π/2 + ∠BAC` in cleared polynomial form
(with `a = A - B`, `c = C - B`, `d = D - B`). -/
noncomputable def C1f (a c d : E2) : ℝ := (⟪d, d⟫ - ⟪d, c⟫) * ⟪a, a - c⟫ + cr c a * cr c d

/-- The condition `∠DAC = ∠ACB` in cleared polynomial form: `D - A` is parallel
to `d1dir a c`. -/
noncomputable def C2f (a c d : E2) : ℝ := cr (d - a) (d1dir a c)

/-- The tangency conclusion in cleared polynomial form, multiplied by the
factor `⟪a - c, d⟫` which is eliminated later. -/
noncomputable def Gpf (a c d : E2) : ℝ :=
  (⟪a, c⟫ * cr c d - cr c a * ⟪c, d⟫) * ⟪a - c, d⟫ + cr c a * ⟪d, d⟫ * (⟪a, a⟫ - ⟪c, c⟫)

/-- The master polynomial identity: the tangency polynomial is a linear
combination of the two constraint polynomials. Found by computer algebra. -/
lemma master_id (a c d : E2) :
    ⟪a - c, a - c⟫ * Gpf a c d + cr a c * (⟪a, a⟫ - ⟪c, c⟫) * C1f a c d =
      (⟪c, c⟫ * ⟪a, d⟫ - ⟪a, a⟫ * ⟪c, d⟫) * C2f a c d := by
  simp only [Gpf, C1f, C2f, d1dir, cr, J, inner_eq, PiLp.sub_apply, PiLp.smul_apply,
    PiLp.neg_apply, Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]
  ring

/-- Squared distance in coordinates. -/
lemma distsq (x y : E2) : dist x y ^ 2 = (x - y) 0 ^ 2 + (x - y) 1 ^ 2 := by
  rw [dist_eq_norm, norm_sq_eq]

/-- Expand inner products, cross products and vector operations to coordinates. -/
macro "coords" : tactic => `(tactic| simp only [inner_eq, cr, J, PiLp.sub_apply,
  PiLp.add_apply, PiLp.smul_apply, PiLp.neg_apply, PiLp.zero_apply, Matrix.cons_val_zero,
  Matrix.cons_val_one, smul_eq_mul])

snip end

problem usa2024_p5
    (A B C D E M : E2)
    (horient : 0 < cr (B - A) (C - A))
    (hA : ∠ B A C < π / 2) (hB : ∠ A B C < π / 2) (hC : ∠ B C A < π / 2)
    (hD1 : 0 < cr (D - A) (C - A))
    (hD2 : cr (D - B) (C - B) < 0)
    (hD3 : cr (D - A) (B - A) < 0)
    (h1 : ∠ D A C = ∠ A C B)
    (h2 : ∠ B D C = π / 2 + ∠ B A C)
    (hE : ∃ t : ℝ, 0 < t ∧ E = B + t • (D - B))
    (hEd : dist A E = dist C E)
    (hM : M = midpoint ℝ B C) :
    ∃ O : E2, dist O B = dist O E ∧ dist O E = dist O M ∧ ⟪A - B, O - B⟫ = 0 := by
  obtain ⟨t, ht, hEt⟩ := hE
  -- Nondegeneracy of all the points involved.
  have hnBA : B - A ≠ 0 := by
    intro h; rw [h, cr_zero_left] at horient; exact (lt_irrefl 0 horient).elim
  have hnCA : C - A ≠ 0 := by
    intro h; rw [h, cr_zero_right] at horient; exact (lt_irrefl 0 horient).elim
  have hnDA : D - A ≠ 0 := by
    intro h; rw [h, cr_zero_left] at hD1; exact (lt_irrefl 0 hD1).elim
  have hnDB : D - B ≠ 0 := by
    intro h; rw [h, cr_zero_left] at hD2; exact (lt_irrefl 0 hD2).elim
  have hnCD : C - D ≠ 0 := by
    intro h
    have h' : D = C := (sub_eq_zero.mp h).symm
    subst h'; rw [cr_self] at hD2; exact (lt_irrefl 0 hD2).elim
  have hnCB : C - B ≠ 0 := by
    intro h
    have h' : B = C := (sub_eq_zero.mp h).symm
    subst h'; rw [cr_self] at horient; exact (lt_irrefl 0 horient).elim
  have hnBD : B - D ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp hnDB).symm
  have hnACv : A - C ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp hnCA).symm
  have hnBCv : B - C ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp hnCB).symm
  have nBA : ‖B - A‖ ≠ 0 := norm_ne_zero_iff.mpr hnBA
  have nCA : ‖C - A‖ ≠ 0 := norm_ne_zero_iff.mpr hnCA
  have nDA : ‖D - A‖ ≠ 0 := norm_ne_zero_iff.mpr hnDA
  have nDB : ‖B - D‖ ≠ 0 := norm_ne_zero_iff.mpr hnBD
  have nDC : ‖C - D‖ ≠ 0 := norm_ne_zero_iff.mpr hnCD
  have nAC : ‖A - C‖ ≠ 0 := norm_ne_zero_iff.mpr hnACv
  have nBC : ‖B - C‖ ≠ 0 := norm_ne_zero_iff.mpr hnBCv
  -- Cosines and sines of the angles at hand.
  have cosBDC : Real.cos (∠ B D C) = ⟪B - D, C - D⟫ / (‖B - D‖ * ‖C - D‖) := by
    rw [angleE]; exact InnerProductGeometry.cos_angle _ _
  have sinBDC : Real.sin (∠ B D C) = |cr (B - D) (C - D)| / (‖B - D‖ * ‖C - D‖) := by
    rw [angleE]; exact sin_angle_eq _ _ hnBD hnCD
  have cosBAC : Real.cos (∠ B A C) = ⟪B - A, C - A⟫ / (‖B - A‖ * ‖C - A‖) := by
    rw [angleE]; exact InnerProductGeometry.cos_angle _ _
  have sinBAC : Real.sin (∠ B A C) = |cr (B - A) (C - A)| / (‖B - A‖ * ‖C - A‖) := by
    rw [angleE]; exact sin_angle_eq _ _ hnBA hnCA
  have cosDAC : Real.cos (∠ D A C) = ⟪D - A, C - A⟫ / (‖D - A‖ * ‖C - A‖) := by
    rw [angleE]; exact InnerProductGeometry.cos_angle _ _
  have sinDAC : Real.sin (∠ D A C) = |cr (D - A) (C - A)| / (‖D - A‖ * ‖C - A‖) := by
    rw [angleE]; exact sin_angle_eq _ _ hnDA hnCA
  have cosACB : Real.cos (∠ A C B) = ⟪A - C, B - C⟫ / (‖A - C‖ * ‖B - C‖) := by
    rw [angleE]; exact InnerProductGeometry.cos_angle _ _
  have sinACB : Real.sin (∠ A C B) = |cr (A - C) (B - C)| / (‖A - C‖ * ‖B - C‖) := by
    rw [angleE]; exact sin_angle_eq _ _ hnACv hnBCv
  -- Sign resolutions.
  have sgn1 : 0 < cr (B - D) (C - D) := by
    have h : cr (B - D) (C - D) = - cr (D - B) (C - B) := by coords; ring
    linarith [hD2]
  have abs1 : |cr (B - D) (C - D)| = cr (B - D) (C - D) := abs_of_pos sgn1
  have abs2 : |cr (B - A) (C - A)| = cr (B - A) (C - A) := abs_of_pos horient
  have abs3 : |cr (D - A) (C - A)| = cr (D - A) (C - A) := abs_of_pos hD1
  have hΔ : cr (A - C) (B - C) = cr (B - A) (C - A) := by coords; ring
  have abs4 : |cr (A - C) (B - C)| = cr (A - C) (B - C) := abs_of_pos (hΔ ▸ horient)
  -- From `∠BDC = π/2 + ∠BAC`: derive the constraint `C1f`.
  have h2cos : Real.cos (∠ B D C) = - Real.sin (∠ B A C) := by
    rw [h2, Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  have h2sin : Real.sin (∠ B D C) = Real.cos (∠ B A C) := by
    rw [h2, Real.sin_add, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  have e1 : ⟪B - D, C - D⟫ * (‖B - A‖ * ‖C - A‖)
      = - cr (B - A) (C - A) * (‖B - D‖ * ‖C - D‖) := by
    rw [cosBDC, sinBAC, abs2, ← neg_div] at h2cos
    exact (div_eq_div_iff (mul_ne_zero nDB nDC) (mul_ne_zero nBA nCA)).mp h2cos
  have e2 : cr (B - D) (C - D) * (‖B - A‖ * ‖C - A‖)
      = ⟪B - A, C - A⟫ * (‖B - D‖ * ‖C - D‖) := by
    rw [sinBDC, abs1, cosBAC] at h2sin
    exact (div_eq_div_iff (mul_ne_zero nDB nDC) (mul_ne_zero nBA nCA)).mp h2sin
  have C1 : ⟪B - D, C - D⟫ * ⟪B - A, C - A⟫ + cr (B - D) (C - D) * cr (B - A) (C - A)
      = 0 := by
    have hn : (‖B - A‖ * ‖C - A‖) ≠ 0 := mul_ne_zero nBA nCA
    have key : (‖B - A‖ * ‖C - A‖) *
        (⟪B - D, C - D⟫ * ⟪B - A, C - A⟫ + cr (B - D) (C - D) * cr (B - A) (C - A)) = 0 := by
      linear_combination ⟪B - A, C - A⟫ * e1 + cr (B - A) (C - A) * e2
    exact mul_eq_zero.mp key |>.resolve_left hn
  have C1m : C1f (A - B) (C - B) (D - B) = 0 := by
    have h : C1f (A - B) (C - B) (D - B) =
        ⟪B - D, C - D⟫ * ⟪B - A, C - A⟫ + cr (B - D) (C - D) * cr (B - A) (C - A) := by
      simp only [C1f]; coords; ring
    rw [h, C1]
  -- From `∠DAC = ∠ACB`: derive the constraint `C2f`.
  have e3 : ⟪D - A, C - A⟫ * (‖A - C‖ * ‖B - C‖)
      = ⟪A - C, B - C⟫ * (‖D - A‖ * ‖C - A‖) := by
    have h : Real.cos (∠ D A C) = Real.cos (∠ A C B) := by rw [h1]
    rw [cosDAC, cosACB] at h
    exact (div_eq_div_iff (mul_ne_zero nDA nCA) (mul_ne_zero nAC nBC)).mp h
  have e4 : cr (D - A) (C - A) * (‖A - C‖ * ‖B - C‖)
      = cr (A - C) (B - C) * (‖D - A‖ * ‖C - A‖) := by
    have h : Real.sin (∠ D A C) = Real.sin (∠ A C B) := by rw [h1]
    rw [sinDAC, sinACB, abs3, abs4] at h
    exact (div_eq_div_iff (mul_ne_zero nDA nCA) (mul_ne_zero nAC nBC)).mp h
  have key2 : ⟪A - C, B - C⟫ * cr (D - A) (C - A) = cr (A - C) (B - C) * ⟪D - A, C - A⟫ := by
    have hn : (‖A - C‖ * ‖B - C‖) ≠ 0 := mul_ne_zero nAC nBC
    have key' : (‖A - C‖ * ‖B - C‖) *
        (⟪A - C, B - C⟫ * cr (D - A) (C - A) - cr (A - C) (B - C) * ⟪D - A, C - A⟫) = 0 := by
      linear_combination ⟪A - C, B - C⟫ * e4 - cr (A - C) (B - C) * e3
    have h := mul_eq_zero.mp key' |>.resolve_left hn
    linarith [h]
  have C2m : C2f (A - B) (C - B) (D - B) = 0 := by
    have h : C2f (A - B) (C - B) (D - B) =
        ⟪A - C, B - C⟫ * cr (D - A) (C - A) - cr (A - C) (B - C) * ⟪D - A, C - A⟫ := by
      simp only [C2f, d1dir]; coords; ring
    rw [h]
    exact sub_eq_zero.mpr key2
  -- The point E on the ray and the condition AE = EC.
  have hEe : E - B = t • (D - B) := by rw [hEt]; module
  have hEdi : ⟪A - E, A - E⟫ = ⟪C - E, C - E⟫ := by
    have h := hEd
    rw [dist_eq_norm, dist_eq_norm] at h
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, h]
  have hEr2 : ⟪A - B, A - B⟫ - ⟪C - B, C - B⟫
      = 2 * t * (⟪A - B, D - B⟫ - ⟪C - B, D - B⟫) := by
    have hA' : A - E = (A - B) - t • (D - B) := by
      rw [← hEe, sub_sub_sub_comm, sub_self, sub_zero]
    have hC' : C - E = (C - B) - t • (D - B) := by
      rw [← hEe, sub_sub_sub_comm, sub_self, sub_zero]
    rw [hA', hC'] at hEdi
    simp only [inner_eq, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at hEdi ⊢
    linear_combination hEdi
  -- Apply the master identity.
  have hnACi : ⟪(A - B) - (C - B), (A - B) - (C - B)⟫ ≠ 0 := by
    rw [show (A - B) - (C - B) = A - C by rw [sub_sub_sub_comm, sub_self, sub_zero],
      real_inner_self_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hnACv)
  have hG0 : Gpf (A - B) (C - B) (D - B) = 0 := by
    have hm := master_id (A - B) (C - B) (D - B)
    rw [C1m, C2m] at hm
    simp only [mul_zero, add_zero] at hm
    rcases mul_eq_zero.mp hm with hz | hgp
    · exact absurd hz hnACi
    · exact hgp
  -- Factor the goal polynomial.
  have hfact : Gpf (A - B) (C - B) (D - B) =
      ⟪(A - B) - (C - B), D - B⟫ * (⟪A - B, C - B⟫ * cr (C - B) (D - B) -
        cr (C - B) (A - B) * ⟪C - B, D - B⟫ + 2 * cr (C - B) (A - B) * t * ⟪D - B, D - B⟫) := by
    simp only [Gpf]
    rw [hEr2, inner_sub_left (A - B) (C - B) (D - B)]
    ring
  rw [hfact] at hG0
  rcases mul_eq_zero.mp hG0 with hpar | hbr
  · -- The degenerate case `⟪A - C, D - B⟫ = 0` is impossible.
    exfalso
    rw [inner_sub_left] at hpar
    rw [hpar, mul_zero] at hEr2
    have h2 : ⟪A - B, A - B⟫ = ⟪C - B, C - B⟫ := sub_eq_zero.mp hEr2
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h2
    have hnorm : ‖A - B‖ = ‖C - B‖ := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2
    have hdist : dist B A = dist B C := by
      rw [dist_eq_norm, dist_eq_norm, norm_sub_rev B A, norm_sub_rev B C]
      exact hnorm
    have haa : ∠ B A C = ∠ B C A := EuclideanGeometry.angle_eq_angle_of_dist_eq hdist
    have hDAB : ∠ D A C = ∠ B A C :=
      (h1.trans (angle_comm A C B)).trans haa.symm
    have e5 : ⟪D - A, C - A⟫ * (‖B - A‖ * ‖C - A‖)
        = ⟪B - A, C - A⟫ * (‖D - A‖ * ‖C - A‖) := by
      have h : Real.cos (∠ D A C) = Real.cos (∠ B A C) := by rw [hDAB]
      rw [cosDAC, cosBAC] at h
      exact (div_eq_div_iff (mul_ne_zero nDA nCA) (mul_ne_zero nBA nCA)).mp h
    have e6 : cr (D - A) (C - A) * (‖B - A‖ * ‖C - A‖)
        = cr (B - A) (C - A) * (‖D - A‖ * ‖C - A‖) := by
      have h : Real.sin (∠ D A C) = Real.sin (∠ B A C) := by rw [hDAB]
      rw [sinDAC, sinBAC, abs3, abs2] at h
      exact (div_eq_div_iff (mul_ne_zero nDA nCA) (mul_ne_zero nBA nCA)).mp h
    have hz1 : ⟪‖B - A‖ • (D - A) - ‖D - A‖ • (B - A), C - A⟫ = 0 := by
      have key : (‖B - A‖ * ⟪D - A, C - A⟫ - ‖D - A‖ * ⟪B - A, C - A⟫) * ‖C - A‖ = 0 := by
        linear_combination e5
      have hX := mul_eq_zero.mp key |>.resolve_right nCA
      simp only [inner_eq, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at hX ⊢
      linear_combination hX
    have hz2 : cr (‖B - A‖ • (D - A) - ‖D - A‖ • (B - A)) (C - A) = 0 := by
      have key : (‖B - A‖ * cr (D - A) (C - A) - ‖D - A‖ * cr (B - A) (C - A)) * ‖C - A‖
          = 0 := by
        linear_combination e6
      have hX := mul_eq_zero.mp key |>.resolve_right nCA
      simp only [cr, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at hX ⊢
      linear_combination hX
    have hz := uniq hnCA hz1 hz2
    have hfin : cr (D - A) (B - A) = 0 := by
      have hz' : ‖B - A‖ • (D - A) = ‖D - A‖ • (B - A) := sub_eq_zero.mp hz
      have h := congrArg (fun x => cr x (B - A)) hz'
      have key : ‖B - A‖ * cr (D - A) (B - A) = 0 := by
        simp only [cr, PiLp.smul_apply, smul_eq_mul] at h ⊢
        linear_combination h
      exact mul_eq_zero.mp key |>.resolve_left nBA
    exact absurd hfin (ne_of_lt hD3)
  · -- The main case: the bracket vanishes, which gives the tangency condition.
    have hG2 : ⟪A - B, C - B⟫ * cr (C - B) (E - B) + 2 * cr (C - B) (A - B) * ⟪E - B, E - B⟫
        - cr (C - B) (A - B) * ⟪C - B, E - B⟫ = 0 := by
      rw [hEe]
      simp only [inner_eq, cr, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at hbr ⊢
      linear_combination t * hbr
    have hcrpos : 0 < cr (C - B) (E - B) := by
      have hcrd : 0 < cr (C - B) (D - B) := by
        have h : cr (C - B) (D - B) = - cr (D - B) (C - B) := by coords; ring
        linarith [hD2]
      have h : cr (C - B) (t • (D - B)) = t * cr (C - B) (D - B) := by
        simp only [cr, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
      rw [hEe, h]
      exact mul_pos ht hcrd
    have hcrne : cr (C - B) (E - B) ≠ 0 := ne_of_gt hcrpos
    -- The center of the required circle.
    set μ := (⟪E - B, E - B⟫ - ⟪C - B, E - B⟫ / 2) / (2 * cr (C - B) (E - B)) with hμ
    set o := (1/4 : ℝ) • (C - B) + μ • J (C - B) with ho
    have key : 2 * ⟪o, E - B⟫ = ⟪E - B, E - B⟫ := by
      have h1 : 2 * ⟪o, E - B⟫
          = (1/2) * ⟪C - B, E - B⟫ + 2 * μ * cr (C - B) (E - B) := by
        rw [ho]; coords; ring
      rw [h1, hμ]
      field_simp [hcrne]
      ring
    have keyB : ⟪o, C - B⟫ = (1/4) * ⟪C - B, C - B⟫ := by
      rw [ho]; coords; ring
    refine ⟨B + o, ?_, ?_, ?_⟩
    · have h1sq : dist (B + o) B ^ 2 = dist (B + o) E ^ 2 := by
        rw [distsq, distsq]
        have hsub1 : (B + o) - B = o := by module
        have hsub2 : (B + o) - E = o - (E - B) := by module
        rw [hsub1, hsub2]
        simp only [PiLp.sub_apply]
        have keyc : 2 * (o 0 * (E 0 - B 0) + o 1 * (E 1 - B 1))
            = (E 0 - B 0) ^ 2 + (E 1 - B 1) ^ 2 := by
          rw [inner_eq, inner_eq] at key
          simp only [PiLp.sub_apply] at key
          linear_combination key
        linear_combination keyc
      exact (sq_eq_sq₀ dist_nonneg dist_nonneg).mp h1sq
    · have hMsub : M - B = (⅟2 : ℝ) • (C - B) := by
        have h := midpoint_vsub_left (R := ℝ) B C
        rw [← hM, vsub_eq_sub, vsub_eq_sub] at h
        exact h
      have h2sq : dist (B + o) E ^ 2 = dist (B + o) M ^ 2 := by
        rw [distsq, distsq]
        have hsub2 : (B + o) - E = o - (E - B) := by module
        have hsub3 : (B + o) - M = o - (⅟2 : ℝ) • (C - B) := by rw [← hMsub]; module
        rw [hsub2, hsub3]
        simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
        rw [show (⅟2 : ℝ) = 1 / 2 by norm_num]
        have keyc : 2 * (o 0 * (E 0 - B 0) + o 1 * (E 1 - B 1))
            = (E 0 - B 0) ^ 2 + (E 1 - B 1) ^ 2 := by
          rw [inner_eq, inner_eq] at key
          simp only [PiLp.sub_apply] at key
          linear_combination key
        have keyBc : 2 * (o 0 * (C 0 - B 0) + o 1 * (C 1 - B 1))
            = (1/2) * ((C 0 - B 0) ^ 2 + (C 1 - B 1) ^ 2) := by
          rw [inner_eq, inner_eq] at keyB
          simp only [PiLp.sub_apply] at keyB
          linear_combination 2 * keyB
        linear_combination keyBc / 2 - keyc
      exact (sq_eq_sq₀ dist_nonneg dist_nonneg).mp h2sq
    · have hsub1 : (B + o) - B = o := by module
      rw [hsub1, ho]
      have hG3 : ⟪A - B, (1/4 : ℝ) • (C - B) + μ • J (C - B)⟫
          = (1/4) * ⟪A - B, C - B⟫ + μ * cr (C - B) (A - B) := by
        coords; ring
      rw [hG3]
      have h4 : (2 : ℝ) * cr (C - B) (E - B) ≠ 0 := mul_ne_zero two_ne_zero hcrne
      have hX : μ * (2 * cr (C - B) (E - B)) = ⟪E - B, E - B⟫ - ⟪C - B, E - B⟫ / 2 := by
        rw [hμ]; exact div_mul_cancel₀ _ h4
      have hmul : ((1/4 : ℝ) * ⟪A - B, C - B⟫ + μ * cr (C - B) (A - B))
          * (2 * cr (C - B) (E - B))
          = (1/4) * ⟪A - B, C - B⟫ * (2 * cr (C - B) (E - B)) +
            (⟪E - B, E - B⟫ - ⟪C - B, E - B⟫ / 2) * cr (C - B) (A - B) := by
        rw [add_mul]
        linear_combination cr (C - B) (A - B) * hX
      have hcleared : (1/4 : ℝ) * ⟪A - B, C - B⟫ * (2 * cr (C - B) (E - B)) +
          (⟪E - B, E - B⟫ - ⟪C - B, E - B⟫ / 2) * cr (C - B) (A - B) = 0 := by
        linear_combination hG2 / 2
      have hz : ((1/4 : ℝ) * ⟪A - B, C - B⟫ + μ * cr (C - B) (A - B))
          * (2 * cr (C - B) (E - B)) = 0 := by
        rw [hmul, hcleared]
      exact mul_eq_zero.mp hz |>.resolve_right h4

end Usa2024P5
