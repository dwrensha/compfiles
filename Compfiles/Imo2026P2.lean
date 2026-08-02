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
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Geometry]
  problemImportedFrom :=
    "https://github.com/humanfia/imo2026"
}

/-!
# International Mathematical Olympiad 2026, Problem 2

Let ABC be a triangle and let points M and N be the midpoints of sides AB and
AC, respectively. Let points K and L be chosen strictly inside triangles BMC
and BNC, respectively, such that K lies strictly inside triangle ABL and L
lies strictly inside triangle AKC. Suppose that

    ∠KBA = ∠ACL, ∠LBK = ∠LNC, and ∠LCK = ∠BMK.

Let O be the circumcentre of triangle AKL. Prove that OM = ON.

Statement formalization adapted from AxiomMath/IMO2026; proof adapted from
Humanfia's Kimi-K3 solutions (https://github.com/humanfia/imo2026).
-/

open EuclideanGeometry

namespace Imo2026P2

set_option backward.isDefEq.respectTransparency false

-- We work in the Euclidean plane `ℝ²` with the standard `L²` (Euclidean) norm.
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- A point `P` lies in the open interior of the triangle `X Y Z`: it is a
strictly convex combination `P = α • X + β • Y + γ • Z` with `α, β, γ > 0` and
`α + β + γ = 1`. -/
def InsideTriangle (X Y Z P : Plane) : Prop :=
  ∃ α β γ : ℝ, 0 < α ∧ 0 < β ∧ 0 < γ ∧ α + β + γ = 1 ∧
    P = α • X + β • Y + γ • Z

/-- A point `P` lies inside the (proper) angle at vertex `Y` spanned by the rays
`Y X` and `Y Z`: writing `P - Y = s • (X - Y) + t • (Z - Y)`, one has `s > 0`
and `t > 0`. (If `P` lies strictly inside the triangle `X Y Z`, then it also
lies inside the angle at `Y`, so this hypothesis is weaker than the
"strictly inside triangle" condition of the original problem.) -/
def InsideAngle (X Y Z P : Plane) : Prop :=
  ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ P - Y = s • (X - Y) + t • (Z - Y)

/-- `O` is the circumcentre of triangle `A K L`: it is equidistant from the three
vertices. (For a nondegenerate triangle such a point exists and is unique.) -/
def IsCircumcentre (A K L O : Plane) : Prop :=
  dist O A = dist O K ∧ dist O A = dist O L

snip begin

-- Helper coordinate layer: cross and dot products on Plane, used to turn
-- angle equalities into polynomial identities.
def cr (u v : Plane) : ℝ := u 0 * v 1 - u 1 * v 0
def dt (u v : Plane) : ℝ := u 0 * v 0 + u 1 * v 1

lemma inner_eq_dt (u v : Plane) : @inner ℝ Plane _ u v = dt u v := by
  simp [dt, PiLp.inner_apply, Fin.sum_univ_two]
  ring

lemma norm_sq_eq_dt (u : Plane) : ‖u‖ ^ 2 = dt u u := by
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
  simp [dt, Real.norm_eq_abs, pow_two]

lemma lagrange (x y : Plane) : dt x x * dt y y = (dt x y)^2 + (cr x y)^2 := by
  simp [dt, cr]; ring

lemma angle_eq_to_poly {u v u' v' : Plane}
    (hu : u ≠ 0) (hv : v ≠ 0) (hu' : u' ≠ 0) (hv' : v' ≠ 0)
    (hsign : cr u v * cr u' v' > 0)
    (h : InnerProductGeometry.angle u v = InnerProductGeometry.angle u' v') :
    cr u v * dt u' v' = cr u' v' * dt u v := by
  have hcos : dt u v / (‖u‖ * ‖v‖) = dt u' v' / (‖u'‖ * ‖v'‖) := by
    have := congrArg Real.cos h
    rwa [InnerProductGeometry.cos_angle, InnerProductGeometry.cos_angle, inner_eq_dt, inner_eq_dt] at this
  have nu : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have nv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have nu' : ‖u'‖ ≠ 0 := norm_ne_zero_iff.mpr hu'
  have nv' : ‖v'‖ ≠ 0 := norm_ne_zero_iff.mpr hv'
  have hn1 : 0 < ‖u‖ * ‖v‖ := mul_pos (norm_pos_iff.mpr hu) (norm_pos_iff.mpr hv)
  have hn2 : 0 < ‖u'‖ * ‖v'‖ := mul_pos (norm_pos_iff.mpr hu') (norm_pos_iff.mpr hv')
  have h1 : dt u v * (‖u'‖ * ‖v'‖) = dt u' v' * (‖u‖ * ‖v‖) := by
    rw [div_eq_div_iff (mul_ne_zero nu nv) (mul_ne_zero nu' nv')] at hcos
    linear_combination hcos
  have h2 : (dt u v)^2 * (dt u' u' * dt v' v') = (dt u' v')^2 * (dt u u * dt v v) := by
    have e : ((dt u v) * (‖u'‖ * ‖v'‖))^2 = ((dt u' v') * (‖u‖ * ‖v‖))^2 := by rw [h1]
    rw [← norm_sq_eq_dt u', ← norm_sq_eq_dt v', ← norm_sq_eq_dt u, ← norm_sq_eq_dt v]
    linear_combination e
  have h3 : (dt u v)^2 * (cr u' v')^2 = (dt u' v')^2 * (cr u v)^2 := by
    have e1 := lagrange u v
    have e2 := lagrange u' v'
    nlinarith [h2, e1, e2]
  have hsame : dt u v * dt u' v' ≥ 0 := by
    by_contra hh
    push Not at hh
    have e : (dt u v * dt u' v') * (‖u‖ * ‖v‖) = (dt u v)^2 * (‖u'‖ * ‖v'‖) := by
      calc (dt u v * dt u' v') * (‖u‖ * ‖v‖) = dt u v * (dt u' v' * (‖u‖ * ‖v‖)) := by ring
        _ = dt u v * (dt u v * (‖u'‖ * ‖v'‖)) := by rw [← h1]
        _ = (dt u v)^2 * (‖u'‖ * ‖v'‖) := by ring
    have hlt : (dt u v * dt u' v') * (‖u‖ * ‖v‖) < 0 := mul_neg_of_neg_of_pos hh hn1
    have hge : (dt u v)^2 * (‖u'‖ * ‖v'‖) ≥ 0 := mul_nonneg (sq_nonneg _) (le_of_lt hn2)
    linarith
  have h4 : (dt u v * cr u' v')^2 = (dt u' v' * cr u v)^2 := by nlinarith [h3]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h4 with hh | hh
  · linarith
  · have hprod : (dt u v * dt u' v') * (cr u v * cr u' v') = 0 := by
      have hle : (dt u v * dt u' v') * (cr u v * cr u' v') ≤ 0 := by
        have e : (dt u v * dt u' v') * (cr u v * cr u' v')
            = (dt u v * cr u' v') * (dt u' v' * cr u v) := by ring
        rw [e, hh]
        have e2 : -(dt u' v' * cr u v) * (dt u' v' * cr u v) = -((dt u' v' * cr u v)^2) := by ring
        rw [e2]
        exact neg_nonpos.mpr (sq_nonneg _)
      exact le_antisymm hle (mul_nonneg hsame (le_of_lt hsign))
    rcases mul_eq_zero.mp hprod with hz | hz
    · rcases mul_eq_zero.mp hz with hd | hd
      · have hX : dt u v * cr u' v' = 0 := by rw [hd, zero_mul]
        rw [hX] at hh
        have hy : dt u' v' * cr u v = 0 := by linarith [hh]
        rw [hd, mul_zero]
        linarith [hy]
      · have hY : dt u' v' * cr u v = 0 := by rw [hd, zero_mul]
        rw [hY] at hh
        have hX : dt u v * cr u' v' = 0 := by linarith [hh]
        rw [hd, mul_zero]
        linarith [hX]
    · exact absurd hz (ne_of_gt hsign)

lemma inside_BMC_coordinates {A B C K M : Plane}
    (hM : M = midpoint ℝ A B) (hK : InsideTriangle B M C K) :
    ∃ x y : ℝ, 0 < x ∧ 0 < y ∧ x + y < 1 ∧
      K - A = x • (B - A) + y • (C - A) := by
  rcases hK with ⟨α, β, γ, hα, hβ, hγ, hsum, hK⟩
  refine ⟨α + β / 2, γ, by positivity, hγ, by nlinarith, ?_⟩
  rw [hK, hM, midpoint_eq_smul_add]
  ext i
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
    invOf_eq_inv]
  linear_combination (A i) * hsum

lemma inside_BNC_coordinates {A B C L N : Plane}
    (hN : N = midpoint ℝ A C) (hL : InsideTriangle B N C L) :
    ∃ u v : ℝ, 0 < u ∧ 0 < v ∧ u + v < 1 ∧
      L - A = u • (B - A) + v • (C - A) := by
  rcases hL with ⟨α, β, γ, hα, hβ, hγ, hsum, hL⟩
  refine ⟨α, β / 2 + γ, hα, by positivity, by nlinarith, ?_⟩
  rw [hL, hN, midpoint_eq_smul_add]
  ext i
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
    invOf_eq_inv]
  linear_combination (A i) * hsum

lemma cr_ne_zero_of_not_collinear {A B C : Plane}
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane)) :
    cr (B - A) (C - A) ≠ 0 := by
  have hAB : A ≠ B := ne₁₂_of_not_collinear hABC
  have hu : B - A ≠ 0 := sub_ne_zero.mpr hAB.symm
  intro hcr
  apply hABC
  have hCline : C ∈ line[ℝ, A, B] := by
    rw [← sub_add_cancel C A]
    apply vadd_left_mem_affineSpan_pair.mpr
    by_cases h0 : (B - A) 0 = 0
    · have h1 : (B - A) 1 ≠ 0 := by
        intro hz
        apply hu
        ext i
        fin_cases i <;> assumption
      refine ⟨(C - A) 1 / (B - A) 1, ?_⟩
      ext i
      fin_cases i
      · change ((C - A) 1 / (B - A) 1) * (B - A) 0 = (C - A) 0
        have hv0 : (C - A) 0 = 0 := by
          have huv : (B - A) 1 * (C - A) 0 = 0 := by
            simp only [cr, h0, zero_mul, zero_sub] at hcr
            linarith
          exact (mul_eq_zero.mp huv).resolve_left h1
        simp [h0, hv0]
      · change ((C - A) 1 / (B - A) 1) * (B - A) 1 = (C - A) 1
        exact div_mul_cancel₀ _ h1
    · refine ⟨(C - A) 0 / (B - A) 0, ?_⟩
      ext i
      fin_cases i
      · change ((C - A) 0 / (B - A) 0) * (B - A) 0 = (C - A) 0
        exact div_mul_cancel₀ _ h0
      · change ((C - A) 0 / (B - A) 0) * (B - A) 1 = (C - A) 1
        simp only [cr] at hcr
        field_simp
        nlinarith [hcr]
  have hcol := collinear_insert_of_mem_affineSpan_pair hCline
  have hset : ({C, A, B} : Set Plane) = {A, B, C} := by
    ext p
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [hset] at hcol
  exact hcol

lemma three_angle_cross_signs {A B C K L M N : Plane} {x y u v : ℝ}
    (hM : M = midpoint ℝ A B) (hN : N = midpoint ℝ A C)
    (hx : 0 < x) (hy : 0 < y) (hu : 0 < u) (hv : 0 < v)
    (hK : K - A = x • (B - A) + y • (C - A))
    (hL : L - A = u • (B - A) + v • (C - A))
    (hKangle : InsideAngle L B A K) (hLangle : InsideAngle A C K L)
    (hD : cr (B - A) (C - A) ≠ 0) :
    0 < cr (K - B) (A - B) * cr (A - C) (L - C) ∧
    0 < cr (L - B) (K - B) * cr (L - N) (C - N) ∧
    0 < cr (L - C) (K - C) * cr (B - M) (K - M) := by
  rcases hKangle with ⟨s, t, hs, ht, hKA⟩
  rcases hLangle with ⟨r, w, hr, hw, hLA⟩
  have hk0 := congrArg (fun z : Plane => z 0) hK
  have hk1 := congrArg (fun z : Plane => z 1) hK
  have hl0 := congrArg (fun z : Plane => z 0) hL
  have hl1 := congrArg (fun z : Plane => z 1) hL
  have hka0 := congrArg (fun z : Plane => z 0) hKA
  have hka1 := congrArg (fun z : Plane => z 1) hKA
  have hla0 := congrArg (fun z : Plane => z 0) hLA
  have hla1 := congrArg (fun z : Plane => z 1) hLA
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hk0 hk1 hl0 hl1
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hka0 hka1 hla0 hla1
  have hk0' : K 0 = A 0 + x * (B 0 - A 0) + y * (C 0 - A 0) := by linarith
  have hk1' : K 1 = A 1 + x * (B 1 - A 1) + y * (C 1 - A 1) := by linarith
  have hl0' : L 0 = A 0 + u * (B 0 - A 0) + v * (C 0 - A 0) := by linarith
  have hl1' : L 1 = A 1 + u * (B 1 - A 1) + v * (C 1 - A 1) := by linarith
  have hka0' : K 0 = B 0 + s * (L 0 - B 0) + t * (A 0 - B 0) := by linarith
  have hka1' : K 1 = B 1 + s * (L 1 - B 1) + t * (A 1 - B 1) := by linarith
  have hla0' : L 0 = C 0 + r * (A 0 - C 0) + w * (K 0 - C 0) := by linarith
  have hla1' : L 1 = C 1 + r * (A 1 - C 1) + w * (K 1 - C 1) := by linarith
  let D := cr (B - A) (C - A)
  have hD' : D ≠ 0 := hD
  have hDsq : 0 < D ^ 2 := sq_pos_of_ne_zero hD'
  have hc1l : cr (K - B) (A - B) = y * D := by
    simp only [cr, PiLp.sub_apply, D]
    rw [hk0', hk1']
    ring
  have hc1r : cr (A - C) (L - C) = u * D := by
    simp only [cr, PiLp.sub_apply, D]
    rw [hl0', hl1']
    ring
  have hc2l : cr (L - B) (K - B) = t * v * D := by
    simp only [cr, PiLp.sub_apply, D]
    rw [hka0', hka1', hl0', hl1']
    ring
  have hc2r : cr (L - N) (C - N) = (u / 2) * D := by
    rw [hN, midpoint_eq_smul_add]
    simp only [cr, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      invOf_eq_inv, D]
    rw [hl0', hl1']
    ring
  have hc3l : cr (L - C) (K - C) = r * x * D := by
    simp only [cr, PiLp.sub_apply, D]
    rw [hla0', hla1', hk0', hk1']
    ring
  have hc3r : cr (B - M) (K - M) = (y / 2) * D := by
    rw [hM, midpoint_eq_smul_add]
    simp only [cr, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      invOf_eq_inv, D]
    rw [hk0', hk1']
    ring
  constructor
  · rw [hc1l, hc1r]
    have hpos : 0 < (y * u) * D ^ 2 := mul_pos (mul_pos hy hu) hDsq
    calc
      0 < (y * u) * D ^ 2 := hpos
      _ = y * D * (u * D) := by ring
  constructor
  · rw [hc2l, hc2r]
    have hcoef : 0 < t * v * (u / 2) := by positivity
    have hpos : 0 < (t * v * (u / 2)) * D ^ 2 := mul_pos hcoef hDsq
    calc
      0 < (t * v * (u / 2)) * D ^ 2 := hpos
      _ = t * v * D * (u / 2 * D) := by ring
  · rw [hc3l, hc3r]
    have hcoef : 0 < r * x * (y / 2) := by positivity
    have hpos : 0 < (r * x * (y / 2)) * D ^ 2 := mul_pos hcoef hDsq
    calc
      0 < (r * x * (y / 2)) * D ^ 2 := hpos
      _ = r * x * D * (y / 2 * D) := by ring

lemma eq_smul_of_cr_eq_zero {k l : Plane} (hk : k ≠ 0)
    (hcr : cr k l = 0) : ∃ r : ℝ, r • k = l := by
  by_cases h0 : k 0 = 0
  · have h1 : k 1 ≠ 0 := by
      intro hz
      apply hk
      ext i
      fin_cases i <;> assumption
    refine ⟨l 1 / k 1, ?_⟩
    ext i
    fin_cases i
    · change (l 1 / k 1) * k 0 = l 0
      have hl0 : l 0 = 0 := by
        have huv : k 1 * l 0 = 0 := by
          simp only [cr, h0, zero_mul, zero_sub] at hcr
          linarith
        exact (mul_eq_zero.mp huv).resolve_left h1
      simp [h0, hl0]
    · change (l 1 / k 1) * k 1 = l 1
      exact div_mul_cancel₀ _ h1
  · refine ⟨l 0 / k 0, ?_⟩
    ext i
    fin_cases i
    · change (l 0 / k 0) * k 0 = l 0
      exact div_mul_cancel₀ _ h0
    · change (l 0 / k 0) * k 1 = l 1
      simp only [cr] at hcr
      field_simp
      nlinarith [hcr]

lemma circle_det_ne_zero {o k l : Plane}
    (hk : k ≠ 0) (hl : l ≠ 0) (hkl : k ≠ l)
    (hok : ‖o‖ = ‖o - k‖) (hol : ‖o‖ = ‖o - l‖) :
    cr k l ≠ 0 := by
  intro hdet
  obtain ⟨r, hrl⟩ := eq_smul_of_cr_eq_zero hk hdet
  have hr : r ≠ 0 := by
    intro hr0
    apply hl
    rw [← hrl, hr0, zero_smul]
  have eK := congrArg (fun z : ℝ => z ^ 2) hok
  have eL := congrArg (fun z : ℝ => z ^ 2) hol
  rw [norm_sq_eq_dt, norm_sq_eq_dt] at eK
  rw [norm_sq_eq_dt, norm_sq_eq_dt] at eL
  have hrl0 := congrArg (fun z : Plane => z 0) hrl
  have hrl1 := congrArg (fun z : Plane => z 1) hrl
  simp only [PiLp.smul_apply, smul_eq_mul] at hrl0 hrl1
  have hkk : 0 < dt k k := by
    rw [← norm_sq_eq_dt]
    positivity
  have eK' : 2 * (o 0 * k 0 + o 1 * k 1) = k 0 ^ 2 + k 1 ^ 2 := by
    simp only [dt, PiLp.sub_apply] at eK
    nlinarith [eK]
  have eL' : 2 * r * (o 0 * k 0 + o 1 * k 1) =
      r ^ 2 * (k 0 ^ 2 + k 1 ^ 2) := by
    simp only [dt, PiLp.sub_apply] at eL
    rw [← hrl0, ← hrl1] at eL
    nlinarith [eL]
  have er : r * (r - 1) * dt k k = 0 := by
    simp only [dt]
    linear_combination r * eK' - eL'
  rcases mul_eq_zero.mp er with hrbad | hkkbad
  · rcases mul_eq_zero.mp hrbad with hr0 | hr1
    · exact hr hr0
    · have : r = 1 := by linarith
      apply hkl
      rw [← hrl, this, one_smul]
  · nlinarith

def goalPoly (b c k l : Plane) : ℝ :=
  let nk := dt k k
  let nl := dt l l
  let det := cr k l
  let xnum := nk * l 1 - nl * k 1
  let ynum := k 0 * nl - l 0 * nk
  2 * (xnum * (c 0 - b 0) + ynum * (c 1 - b 1)) -
    (dt c c - dt b b) * det

lemma circle_equation {o k : Plane} (h : ‖o‖ = ‖o - k‖) :
    2 * dt o k = dt k k := by
  have e := congrArg (fun z : ℝ => z ^ 2) h
  rw [norm_sq_eq_dt, norm_sq_eq_dt] at e
  simp only [dt, PiLp.sub_apply] at e ⊢
  nlinarith [e]

lemma midpoint_norm_eq_of_goal {b c k l o : Plane}
    (hok : ‖o‖ = ‖o - k‖) (hol : ‖o‖ = ‖o - l‖)
    (hdet : cr k l ≠ 0) (hgoal : goalPoly b c k l = 0) :
    ‖o - (1 / 2 : ℝ) • b‖ = ‖o - (1 / 2 : ℝ) • c‖ := by
  have ek := circle_equation hok
  have el := circle_equation hol
  let det := cr k l
  let nk := dt k k
  let nl := dt l l
  let xnum := nk * l 1 - nl * k 1
  let ynum := k 0 * nl - l 0 * nk
  have hx : 2 * o 0 * det = xnum := by
    simp only [det, xnum, nk, nl, cr, dt] at ek el ⊢
    linear_combination (l 1) * ek - (k 1) * el
  have hy : 2 * o 1 * det = ynum := by
    simp only [det, xnum, ynum, nk, nl, cr, dt] at ek el hx ⊢
    linear_combination (k 0) * el - (l 0) * ek
  have hmul : det *
      (4 * dt o (c - b) - (dt c c - dt b b)) = 0 := by
    change 2 * (xnum * (c 0 - b 0) + ynum * (c 1 - b 1)) -
      (dt c c - dt b b) * det = 0 at hgoal
    rw [← hx, ← hy] at hgoal
    simp only [dt, PiLp.sub_apply] at hgoal ⊢
    linear_combination hgoal
  have hdet' : det ≠ 0 := hdet
  have htarget : 4 * dt o (c - b) = dt c c - dt b b := by
    have := (mul_eq_zero.mp hmul).resolve_left hdet'
    linarith
  have hsquare : ‖o - (1 / 2 : ℝ) • b‖ ^ 2 =
      ‖o - (1 / 2 : ℝ) • c‖ ^ 2 := by
    rw [norm_sq_eq_dt, norm_sq_eq_dt]
    simp only [dt, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at htarget ⊢
    nlinarith [htarget]
  nlinarith [norm_nonneg (o - (1 / 2 : ℝ) • b),
    norm_nonneg (o - (1 / 2 : ℝ) • c)]

def anglePoly (u v u' v' : Plane) : ℝ :=
  cr u v * dt u' v' - cr u' v' * dt u v

def h1Poly (b c k l : Plane) : ℝ :=
  anglePoly (k - b) (-b) (-c) (l - c)

noncomputable def h2Poly (b c k l : Plane) : ℝ :=
  anglePoly (l - b) (k - b) (l - (1 / 2 : ℝ) • c) (c - (1 / 2 : ℝ) • c)

noncomputable def h3Poly (b c k l : Plane) : ℝ :=
  anglePoly (l - c) (k - c) (b - (1 / 2 : ℝ) • b) (k - (1 / 2 : ℝ) • b)

def G4 (b c k l : Plane) : ℝ :=
      b 1 * c 1 * k 0 * l 0
      + -(b 1 * c 0 * k 1 * l 0)
      + -(b 1 * c 0 * c 1 * k 0)
      + b 1 * (c 0) ^ 2 * k 1
      + (b 1) ^ 2 * c 0 * l 0
      + -((b 1) ^ 2 * (c 0) ^ 2)
      + -(b 0 * c 1 * k 0 * l 1)
      + b 0 * (c 1) ^ 2 * k 0
      + b 0 * c 0 * k 1 * l 1
      + -(b 0 * c 0 * c 1 * k 1)
      + -(b 0 * b 1 * c 1 * l 0)
      + -(b 0 * b 1 * c 0 * l 1)
      + (2 : ℝ) * (b 0 * b 1 * c 0 * c 1)
      + (b 0) ^ 2 * c 1 * l 1
      + -((b 0) ^ 2 * (c 1) ^ 2)

lemma exact_elimination_certificate (b c k l : Plane) :
    G4 b c k l * goalPoly b c k l =
      (let Q1 : ℝ :=
            (-2 : ℝ) * ((c 1) ^ 2 * k 0 * l 0)
            + (2 : ℝ) * (c 0 * c 1 * k 1 * l 0)
            + (2 : ℝ) * (c 0 * c 1 * k 0 * l 1)
            + (-2 : ℝ) * ((c 0) ^ 2 * k 1 * l 1)
            + (4 : ℝ) * (b 1 * c 1 * k 0 * l 0)
            + (-3 : ℝ) * (b 1 * c 0 * k 1 * l 0)
            + -(b 1 * c 0 * k 0 * l 1)
            + -(b 1 * c 0 * c 1 * l 0)
            + -(b 1 * c 0 * c 1 * k 0)
            + b 1 * (c 0) ^ 2 * l 1
            + b 1 * (c 0) ^ 2 * k 1
            + (-2 : ℝ) * ((b 1) ^ 2 * k 0 * l 0)
            + (b 1) ^ 2 * c 0 * l 0
            + (b 1) ^ 2 * c 0 * k 0
            + -(b 0 * c 1 * k 1 * l 0)
            + (-3 : ℝ) * (b 0 * c 1 * k 0 * l 1)
            + b 0 * (c 1) ^ 2 * l 0
            + b 0 * (c 1) ^ 2 * k 0
            + (4 : ℝ) * (b 0 * c 0 * k 1 * l 1)
            + -(b 0 * c 0 * c 1 * l 1)
            + -(b 0 * c 0 * c 1 * k 1)
            + (2 : ℝ) * (b 0 * b 1 * k 1 * l 0)
            + (2 : ℝ) * (b 0 * b 1 * k 0 * l 1)
            + -(b 0 * b 1 * c 1 * l 0)
            + -(b 0 * b 1 * c 1 * k 0)
            + -(b 0 * b 1 * c 0 * l 1)
            + -(b 0 * b 1 * c 0 * k 1)
            + (-2 : ℝ) * ((b 0) ^ 2 * k 1 * l 1)
            + (b 0) ^ 2 * c 1 * l 1
            + (b 0) ^ 2 * c 1 * k 1
       let Q2 : ℝ :=
            (-4 : ℝ) * (b 1 * c 1 * k 0 * l 0)
            + (4 : ℝ) * (b 1 * c 0 * k 1 * l 0)
            + (4 : ℝ) * (b 1 * c 0 * c 1 * k 0)
            + (-4 : ℝ) * (b 1 * (c 0) ^ 2 * k 1)
            + (4 : ℝ) * ((b 1) ^ 2 * k 0 * l 0)
            + (-4 : ℝ) * ((b 1) ^ 2 * c 0 * k 0)
            + (4 : ℝ) * (b 0 * c 1 * k 0 * l 1)
            + (-4 : ℝ) * (b 0 * (c 1) ^ 2 * k 0)
            + (-4 : ℝ) * (b 0 * c 0 * k 1 * l 1)
            + (4 : ℝ) * (b 0 * c 0 * c 1 * k 1)
            + (-4 : ℝ) * (b 0 * b 1 * k 1 * l 0)
            + (-4 : ℝ) * (b 0 * b 1 * k 0 * l 1)
            + (4 : ℝ) * (b 0 * b 1 * c 1 * k 0)
            + (4 : ℝ) * (b 0 * b 1 * c 0 * k 1)
            + (4 : ℝ) * ((b 0) ^ 2 * k 1 * l 1)
            + (-4 : ℝ) * ((b 0) ^ 2 * c 1 * k 1)
       let Q3 : ℝ :=
            (-4 : ℝ) * ((c 1) ^ 2 * k 0 * l 0)
            + (4 : ℝ) * (c 0 * c 1 * k 1 * l 0)
            + (4 : ℝ) * (c 0 * c 1 * k 0 * l 1)
            + (-4 : ℝ) * ((c 0) ^ 2 * k 1 * l 1)
            + (4 : ℝ) * (b 1 * c 1 * k 0 * l 0)
            + (-4 : ℝ) * (b 1 * c 0 * k 1 * l 0)
            + (-4 : ℝ) * (b 1 * c 0 * c 1 * l 0)
            + (4 : ℝ) * (b 1 * (c 0) ^ 2 * l 1)
            + (4 : ℝ) * ((b 1) ^ 2 * c 0 * l 0)
            + (-4 : ℝ) * (b 0 * c 1 * k 0 * l 1)
            + (4 : ℝ) * (b 0 * (c 1) ^ 2 * l 0)
            + (4 : ℝ) * (b 0 * c 0 * k 1 * l 1)
            + (-4 : ℝ) * (b 0 * c 0 * c 1 * l 1)
            + (-4 : ℝ) * (b 0 * b 1 * c 1 * l 0)
            + (-4 : ℝ) * (b 0 * b 1 * c 0 * l 1)
            + (4 : ℝ) * ((b 0) ^ 2 * c 1 * l 1)
       Q1 * h1Poly b c k l + Q2 * h2Poly b c k l + Q3 * h3Poly b c k l) := by
  simp only [G4, goalPoly, h1Poly, h2Poly, h3Poly, anglePoly, cr, dt,
    PiLp.sub_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul]
  ring

lemma left_ne_of_cr_ne {u v : Plane} (h : cr u v ≠ 0) : u ≠ 0 := by
  intro hu
  apply h
  rw [hu]
  simp [cr]

lemma right_ne_of_cr_ne {u v : Plane} (h : cr u v ≠ 0) : v ≠ 0 := by
  intro hv
  apply h
  rw [hv]
  simp [cr]

snip end

/-- With the configuration described above, the circumcentre
`O` of triangle `AKL` satisfies `OM = ON`, where `M`, `N` are the midpoints of
`AB`, `AC`. -/
problem imo2026_p2
    (A B C K L O : Plane)
    -- `ABC` is a nondegenerate triangle.
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane))
    -- `M`, `N` are the midpoints of `AB`, `AC`.
    (M N : Plane) (hM : M = midpoint ℝ A B) (hN : N = midpoint ℝ A C)
    -- `K` is inside triangle `BMC`; `L` is inside triangle `BNC`.
    (hK : InsideTriangle B M C K)
    (hL : InsideTriangle B N C L)
    -- `K` inside angle `∠ L B A`; `L` inside angle `∠ A C K`.
    (hKangle : InsideAngle L B A K)
    (hLangle : InsideAngle A C K L)
    -- The three angle equalities.
    (h1 : ∠ K B A = ∠ A C L)
    (h2 : ∠ L B K = ∠ L N C)
    (h3 : ∠ L C K = ∠ B M K)
    -- `O` is the circumcentre of triangle `AKL`.
    (hO : IsCircumcentre A K L O) :
    dist O M = dist O N := by
  obtain ⟨x, y, hx, hy, hxy, hKcoord⟩ := inside_BMC_coordinates hM hK
  obtain ⟨u, v, hu, hv, huv, hLcoord⟩ := inside_BNC_coordinates hN hL
  have hD := cr_ne_zero_of_not_collinear hABC
  obtain ⟨hs1, hs2, hs3⟩ :=
    three_angle_cross_signs hM hN hx hy hu hv hKcoord hLcoord
      hKangle hLangle hD

  have hc1a : cr (K - B) (A - B) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hs1
    linarith
  have hc1b : cr (A - C) (L - C) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hs1
    linarith
  have hc2a : cr (L - B) (K - B) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hs2
    linarith
  have hc2b : cr (L - N) (C - N) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hs2
    linarith
  have hc3a : cr (L - C) (K - C) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hs3
    linarith
  have hc3b : cr (B - M) (K - M) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hs3
    linarith

  have hp1 := angle_eq_to_poly
    (left_ne_of_cr_ne hc1a) (right_ne_of_cr_ne hc1a)
    (left_ne_of_cr_ne hc1b) (right_ne_of_cr_ne hc1b) hs1 (by
      change InnerProductGeometry.angle (K - B) (A - B) =
        InnerProductGeometry.angle (A - C) (L - C) at h1
      exact h1)
  have hp2 := angle_eq_to_poly
    (left_ne_of_cr_ne hc2a) (right_ne_of_cr_ne hc2a)
    (left_ne_of_cr_ne hc2b) (right_ne_of_cr_ne hc2b) hs2 (by
      change InnerProductGeometry.angle (L - B) (K - B) =
        InnerProductGeometry.angle (L - N) (C - N) at h2
      exact h2)
  have hp3 := angle_eq_to_poly
    (left_ne_of_cr_ne hc3a) (right_ne_of_cr_ne hc3a)
    (left_ne_of_cr_ne hc3b) (right_ne_of_cr_ne hc3b) hs3 (by
      change InnerProductGeometry.angle (L - C) (K - C) =
        InnerProductGeometry.angle (B - M) (K - M) at h3
      exact h3)

  let b := B - A
  let c := C - A
  let k := K - A
  let l := L - A
  let o := O - A
  have hkB : k - b = K - B := by simp [k, b]
  have hAB : -b = A - B := by simp [b]
  have hAC : -c = A - C := by simp [c]
  have hlC : l - c = L - C := by simp [l, c]
  have hlB : l - b = L - B := by simp [l, b]
  have hkC : k - c = K - C := by simp [k, c]
  have hlN : l - (1 / 2 : ℝ) • c = L - N := by
    rw [hN, midpoint_eq_smul_add]
    ext i
    simp only [l, c, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul, invOf_eq_inv]
    ring
  have hcN : c - (1 / 2 : ℝ) • c = C - N := by
    rw [hN, midpoint_eq_smul_add]
    ext i
    simp only [c, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul, invOf_eq_inv]
    ring
  have hbM : b - (1 / 2 : ℝ) • b = B - M := by
    rw [hM, midpoint_eq_smul_add]
    ext i
    simp only [b, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul, invOf_eq_inv]
    ring
  have hkM : k - (1 / 2 : ℝ) • b = K - M := by
    rw [hM, midpoint_eq_smul_add]
    ext i
    simp only [k, b, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul, invOf_eq_inv]
    ring
  have hH1 : h1Poly b c k l = 0 := by
    simp only [h1Poly, anglePoly, hkB, hAB, hAC, hlC]
    linarith [hp1]
  have hH2 : h2Poly b c k l = 0 := by
    simp only [h2Poly, anglePoly, hlB, hkB, hlN, hcN]
    linarith [hp2]
  have hH3 : h3Poly b c k l = 0 := by
    simp only [h3Poly, anglePoly, hlC, hkC, hbM, hkM]
    linarith [hp3]

  let D := cr b c
  have hDbc : D ≠ 0 := by simpa [D, b, c] using hD
  have hkcoord' : k = x • b + y • c := by simpa [k, b, c] using hKcoord
  have hlcoord' : l = u • b + v • c := by simpa [l, b, c] using hLcoord
  have hk0 := congrArg (fun z : Plane => z 0) hkcoord'
  have hk1 := congrArg (fun z : Plane => z 1) hkcoord'
  have hl0 := congrArg (fun z : Plane => z 0) hlcoord'
  have hl1 := congrArg (fun z : Plane => z 1) hlcoord'
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hk0 hk1 hl0 hl1
  have hGfac : G4 b c k l = -(1 - v) * (1 - x) * D ^ 2 := by
    simp only [G4, D, cr]
    rw [hk0, hk1, hl0, hl1]
    ring
  have hvlt : v < 1 := by nlinarith
  have hxlt : x < 1 := by nlinarith
  have hGne : G4 b c k l ≠ 0 := by
    rw [hGfac]
    exact mul_ne_zero
      (mul_ne_zero (neg_ne_zero.mpr (ne_of_gt (sub_pos.mpr hvlt)))
        (ne_of_gt (sub_pos.mpr hxlt)))
      (pow_ne_zero 2 hDbc)
  have hcert : G4 b c k l * goalPoly b c k l = 0 := by
    rw [exact_elimination_certificate]
    simp [hH1, hH2, hH3]
  have hgoal : goalPoly b c k l = 0 :=
    (mul_eq_zero.mp hcert).resolve_left hGne

  have hk0v : k ≠ 0 := by
    intro hkz
    apply hc1a
    have hKA : K = A := by
      ext i
      have hi := congrArg (fun z : Plane => z i) hkz
      simp only [k, PiLp.sub_apply, PiLp.zero_apply] at hi
      linarith
    rw [hKA]
    simp only [cr, PiLp.sub_apply]
    ring
  have hl0v : l ≠ 0 := by
    intro hlz
    apply hc1b
    have hLA : L = A := by
      ext i
      have hi := congrArg (fun z : Plane => z i) hlz
      simp only [l, PiLp.sub_apply, PiLp.zero_apply] at hi
      linarith
    rw [hLA]
    simp only [cr, PiLp.sub_apply]
    ring
  have hkl : k ≠ l := by
    intro hkl'
    apply hc2a
    have hKL : K = L := by
      ext i
      have hi := congrArg (fun z : Plane => z i) hkl'
      simp only [k, l, PiLp.sub_apply] at hi
      linarith
    rw [hKL]
    simp only [cr, PiLp.sub_apply]
    ring
  have hok : ‖o‖ = ‖o - k‖ := by
    simpa [o, k, dist_eq_norm] using hO.1
  have hol : ‖o‖ = ‖o - l‖ := by
    simpa [o, l, dist_eq_norm] using hO.2
  have hdet : cr k l ≠ 0 := circle_det_ne_zero hk0v hl0v hkl hok hol
  have hmid := midpoint_norm_eq_of_goal hok hol hdet hgoal
  have hOM : o - (1 / 2 : ℝ) • b = O - M := by
    rw [hM, midpoint_eq_smul_add]
    ext i
    simp only [o, b, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul, invOf_eq_inv]
    ring
  have hON : o - (1 / 2 : ℝ) • c = O - N := by
    rw [hN, midpoint_eq_smul_add]
    ext i
    simp only [o, c, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul, invOf_eq_inv]
    ring
  rw [hOM, hON] at hmid
  simpa [dist_eq_norm] using hmid

end Imo2026P2
