/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 1982, Problem 3

D is a point inside the equilateral triangle ABC. E is a point inside DBC.
Show that area DBC/(perimeter DBC)² > area EBC/(perimeter EBC)².
-/

namespace Usa1982P3

/-- Distance between two points of the Cartesian plane `ℝ × ℝ`. -/
noncomputable def dist (P Q : ℝ × ℝ) : ℝ := √((P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2)

/-- The area of a triangle with vertices `P`, `Q`, `R` (shoelace formula). -/
noncomputable def area (P Q R : ℝ × ℝ) : ℝ :=
  |P.1 * (Q.2 - R.2) + Q.1 * (R.2 - P.2) + R.1 * (P.2 - Q.2)| / 2

/-- The perimeter of a triangle with vertices `P`, `Q`, `R`. -/
noncomputable def perimeter (P Q R : ℝ × ℝ) : ℝ := dist P Q + dist Q R + dist R P

/-- A point `P` lies strictly inside the triangle `ABC` if it is a convex combination
of the vertices with strictly positive weights. -/
def Inside (P A B C : ℝ × ℝ) : Prop :=
  ∃ α β γ : ℝ, 0 < α ∧ 0 < β ∧ 0 < γ ∧ α + β + γ = 1 ∧ P = α • A + β • B + γ • C

snip begin

/-- The function governing the problem: for a triangle `PBC` with base `BC`,
if `u = cot(B/2)` and `v = cot(C/2)` are the cotangents of the half-angles at the base,
then `perimeter PBC ^ 2 / area PBC = 4 * f u v`. -/
noncomputable def f (u v : ℝ) : ℝ := u * v * (u + v) / (u * v - 1)

/-- `f` is symmetric in its two arguments. -/
lemma f_symm (u v : ℝ) : f u v = f v u := by
  unfold f
  ring

/-- `f` is strictly positive on `(√3, ∞) × (√3, ∞)`. -/
lemma f_pos {u v : ℝ} (hu : √3 < u) (hv : √3 < v) : 0 < f u v := by
  have h3 : (0 : ℝ) < √3 := Real.sqrt_pos.mpr (by norm_num)
  have h13 : (1 : ℝ) < √3 := (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).mpr (by norm_num)
  have hu1 : 1 < u := by linarith
  have hv1 : 1 < v := by linarith
  have huv1 : 1 < u * v := by nlinarith [mul_pos (sub_pos.mpr hu1) (sub_pos.mpr hv1)]
  unfold f
  exact div_pos
    (mul_pos (mul_pos (by linarith : (0 : ℝ) < u) (by linarith : (0 : ℝ) < v))
      (by linarith : (0 : ℝ) < u + v))
    (by linarith)

/-- `f` is strictly increasing in its first variable on `(√3, ∞) × (√3, ∞)`. -/
lemma f_strictMono_fst {u u' v : ℝ} (hu : √3 < u) (huu : u < u') (hv : √3 < v) :
    f u v < f u' v := by
  have h3 : (0 : ℝ) < √3 := Real.sqrt_pos.mpr (by norm_num)
  have h13 : (1 : ℝ) < √3 := (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).mpr (by norm_num)
  have h3sq : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hu1 : 1 < u := by linarith
  have hu'1 : 1 < u' := by linarith
  have hv1 : 1 < v := by linarith
  have huv1 : 1 < u * v := by nlinarith [mul_pos (sub_pos.mpr hu1) (sub_pos.mpr hv1)]
  have huv : 0 < u * v - 1 := by linarith
  have hu'v1 : 1 < u' * v := by nlinarith [mul_pos (sub_pos.mpr hu'1) (sub_pos.mpr hv1)]
  have hu'v : 0 < u' * v - 1 := by linarith
  -- The heart of the matter: this polynomial in `u`, `u'`, `v` is positive.
  have key : 0 < u * u' * v - u - u' - v := by
    have e : u * u' * v - u - u' - v =
        (v - √3) * (u * u' - 1) + (u' - u) * (√3 * u - 1) + (u - √3) * (√3 * u + 1) := by
      linear_combination u * h3sq
    have p1 : 0 < u * u' - 1 := by
      have : 1 < u * u' := by nlinarith [mul_pos (sub_pos.mpr hu1) (sub_pos.mpr hu'1)]
      linarith
    have p2 : 0 < √3 * u - 1 := by nlinarith [mul_pos h3 (sub_pos.mpr hu), h3sq]
    have t1 : 0 < (v - √3) * (u * u' - 1) := mul_pos (sub_pos.mpr hv) p1
    have t2 : 0 < (u' - u) * (√3 * u - 1) := mul_pos (sub_pos.mpr huu) p2
    have t3 : 0 < (u - √3) * (√3 * u + 1) :=
      mul_pos (sub_pos.mpr hu) (add_pos (mul_pos h3 (by linarith : (0 : ℝ) < u)) zero_lt_one)
    rw [e]
    linarith [t1, t2, t3]
  have hdiff : f u' v - f u v =
      v * (u' - u) * (u * u' * v - u - u' - v) / ((u' * v - 1) * (u * v - 1)) := by
    have e1 : f u' v = u' * v * (u' + v) / (u' * v - 1) := rfl
    have e2 : f u v = u * v * (u + v) / (u * v - 1) := rfl
    rw [e1, e2, div_sub_div _ _ hu'v.ne' huv.ne']
    congr 1
    ring
  have hpos : 0 < f u' v - f u v := by
    rw [hdiff]
    exact div_pos (mul_pos (mul_pos (by linarith : (0 : ℝ) < v) (sub_pos.mpr huu)) key)
      (mul_pos hu'v huv)
  linarith [hpos]

/-- `f` is strictly increasing in both variables on `(√3, ∞) × (√3, ∞)`. -/
lemma f_strictMono {u u' v v' : ℝ} (hu : √3 < u) (huu : u < u') (hv : √3 < v)
    (hvv : v < v') : f u v < f u' v' := by
  have hu' : √3 < u' := by linarith
  have h1 := f_strictMono_fst hu huu hv
  have h2 : f u' v < f u' v' := by
    rw [f_symm u' v, f_symm u' v']
    exact f_strictMono_fst hv hvv hu'
  exact lt_trans h1 h2

/-- The cotangent of a half-angle in terms of a slope: if a right triangle has legs
`t` (adjacent, measured in units of the opposite leg) and `1` (opposite), then
`cot(θ/2) = √(1 + t^2) + t`. -/
noncomputable def g (t : ℝ) : ℝ := √(1 + t ^ 2) + t

/-- `g` is strictly increasing on the positive reals. -/
lemma g_strictMono {s t : ℝ} (hs : 0 < s) (hst : s < t) : g s < g t := by
  have ht : 0 < t := lt_trans hs hst
  have hsq : s ^ 2 < t ^ 2 := by
    nlinarith [mul_pos hs (sub_pos.mpr hst), mul_pos ht (sub_pos.mpr hst)]
  have h1 : (1 : ℝ) + s ^ 2 < 1 + t ^ 2 := by linarith
  have h2 := Real.sqrt_lt_sqrt (by positivity : (0 : ℝ) ≤ 1 + s ^ 2) h1
  show √(1 + s ^ 2) + s < √(1 + t ^ 2) + t
  linarith [h2, hst]

/-- Conversion between the half-angle cotangent written with side lengths and `g`. -/
lemma g_apply {a h : ℝ} (ha : 0 < a) (hh : 0 < h) : (√(a ^ 2 + h ^ 2) + a) / h = g (a / h) := by
  have e2 : a ^ 2 + h ^ 2 = h ^ 2 * (1 + (a / h) ^ 2) := by
    field_simp [hh.ne']
    ring
  have e1 : √(a ^ 2 + h ^ 2) = h * √(1 + (a / h) ^ 2) := by
    rw [e2, Real.sqrt_mul (sq_nonneg h), Real.sqrt_sq hh.le]
  show (√(a ^ 2 + h ^ 2) + a) / h = √(1 + (a / h) ^ 2) + a / h
  rw [e1]
  field_simp [hh.ne']

/-- `g (1/√3) = √3`, the half-angle cotangent of a `60°` angle. -/
lemma g_eval : g (1 / √3) = √3 := by
  have h3 : (0 : ℝ) < √3 := Real.sqrt_pos.mpr (by norm_num)
  have h3sq : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  show √(1 + (1 / √3) ^ 2) + 1 / √3 = √3
  have e1 : (1 / √3 : ℝ) ^ 2 = 1 / 3 := by
    rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have e2 : √((1 : ℝ) + 1 / 3) = 2 / √3 := by
    have e : (2 / √3 : ℝ) * (2 / √3) = 1 + 1 / 3 := by
      rw [div_mul_div_comm, h3sq]
      norm_num
    rw [← e, Real.sqrt_mul_self (by positivity)]
  rw [e1, e2, ← add_div, show (2 : ℝ) + 1 = 3 by norm_num, div_eq_iff h3.ne']
  exact h3sq.symm

/-- The half-angle cotangent `u = (√(a^2+h^2)+a)/h` exceeds `√3` when the slope
`h/a` is less than `√3`, i.e. when the angle is less than `60°`. -/
lemma u_gt_sqrt3 {a h : ℝ} (ha : 0 < a) (hh : 0 < h) (h3a : h < √3 * a) :
    √3 < (√(a ^ 2 + h ^ 2) + a) / h := by
  have h3 : (0 : ℝ) < √3 := Real.sqrt_pos.mpr (by norm_num)
  rw [g_apply ha hh]
  have key : 1 / √3 < a / h := by
    have e1 : a / (√3 * a) = 1 / √3 := by
      rw [div_eq_div_iff (mul_ne_zero h3.ne' ha.ne') h3.ne']
      ring
    rw [← e1]
    gcongr
  have hg := g_strictMono (by positivity : (0 : ℝ) < 1 / √3) key
  rw [g_eval] at hg
  exact hg

/-- The half-angle cotangent is strictly increasing in the slope ratio `a / h`. -/
lemma u_lt {a h b k : ℝ} (ha : 0 < a) (hh : 0 < h) (hb : 0 < b) (hk : 0 < k)
    (hab : a / h < b / k) : (√(a ^ 2 + h ^ 2) + a) / h < (√(b ^ 2 + k ^ 2) + b) / k := by
  rw [g_apply ha hh, g_apply hb hk]
  exact g_strictMono (div_pos ha hh) hab

/-- The key identity: for the triangle with vertices `(0,0)`, `(1,0)` and `(a,h)`
with `0 < a < 1` and `0 < h`, the quantity `area / perimeter^2` equals
`1 / (4 * f u v)` where `u` and `v` are the half-angle cotangents at the base. -/
lemma area_div_perimeter_sq {a h : ℝ} (ha : 0 < a) (ha1 : a < 1) (hh : 0 < h) :
    (h / 2) / (1 + √(a ^ 2 + h ^ 2) + √((1 - a) ^ 2 + h ^ 2)) ^ 2 =
    1 / (4 * f ((√(a ^ 2 + h ^ 2) + a) / h) ((√((1 - a) ^ 2 + h ^ 2) + (1 - a)) / h)) := by
  set c1 := √(a ^ 2 + h ^ 2) with hc1
  set d1 := √((1 - a) ^ 2 + h ^ 2) with hd1
  set u := (c1 + a) / h with hu_def
  set v := (d1 + (1 - a)) / h with hv_def
  have hc1sq : c1 ^ 2 = a ^ 2 + h ^ 2 := by
    rw [hc1]
    exact Real.sq_sqrt (by positivity)
  have hd1sq : d1 ^ 2 = (1 - a) ^ 2 + h ^ 2 := by
    rw [hd1]
    exact Real.sq_sqrt (by positivity)
  have hc1pos : 0 < c1 := by
    rw [hc1]
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (sq_nonneg a) (pow_pos hh 2))
  have hd1pos : 0 < d1 := by
    rw [hd1]
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (sq_nonneg (1 - a)) (pow_pos hh 2))
  have hu_pos : 0 < u := by
    rw [hu_def]
    exact div_pos (add_pos hc1pos ha) hh
  have hv_pos : 0 < v := by
    rw [hv_def]
    exact div_pos (add_pos hd1pos (sub_pos.mpr ha1)) hh
  have hu : u * h = c1 + a := by
    rw [hu_def]
    field_simp [hh.ne']
  have hv : v * h = d1 + (1 - a) := by
    rw [hv_def]
    field_simp [hh.ne']
  have hu1 : 1 < u := by
    rw [hu_def, one_lt_div hh]
    have hsq1 : h ^ 2 < a ^ 2 + h ^ 2 := by linarith [pow_pos ha 2]
    have hc1gt : h < c1 := by
      rw [hc1]
      calc h = √(h ^ 2) := (Real.sqrt_sq hh.le).symm
        _ < √(a ^ 2 + h ^ 2) := Real.sqrt_lt_sqrt (sq_nonneg h) hsq1
    linarith [hc1gt, ha]
  have hv1 : 1 < v := by
    rw [hv_def, one_lt_div hh]
    have hsq2 : h ^ 2 < (1 - a) ^ 2 + h ^ 2 := by linarith [pow_pos (sub_pos.mpr ha1) 2]
    have hd1gt : h < d1 := by
      rw [hd1]
      calc h = √(h ^ 2) := (Real.sqrt_sq hh.le).symm
        _ < √((1 - a) ^ 2 + h ^ 2) := Real.sqrt_lt_sqrt (sq_nonneg h) hsq2
    linarith [hd1gt, sub_pos.mpr ha1]
  have huv1 : 1 < u * v := by nlinarith [mul_pos (sub_pos.mpr hu1) (sub_pos.mpr hv1)]
  have huv : u * v - 1 ≠ 0 := (sub_pos.mpr huv1).ne'
  -- Eliminate `a` and `1 - a` in favour of `u`, `v`, `h`.
  have e2u : 2 * u * a = (u ^ 2 - 1) * h := by
    have e1 : (u * h - a) ^ 2 = a ^ 2 + h ^ 2 := by
      have ec1 : u * h - a = c1 := by linarith [hu]
      rw [ec1, hc1sq]
    have hau : 2 * (u * h) * a = (u ^ 2 - 1) * h ^ 2 := by linear_combination -e1
    apply mul_left_cancel₀ hh.ne'
    linear_combination hau
  have e2v : 2 * v * (1 - a) = (v ^ 2 - 1) * h := by
    have e1 : (v * h - (1 - a)) ^ 2 = (1 - a) ^ 2 + h ^ 2 := by
      have ed1 : v * h - (1 - a) = d1 := by linarith [hv]
      rw [ed1, hd1sq]
    have hbv : 2 * (v * h) * (1 - a) = (v ^ 2 - 1) * h ^ 2 := by linear_combination -e1
    apply mul_left_cancel₀ hh.ne'
    linear_combination hbv
  -- The relation `1 = a + (1 - a)` becomes the key identity between `u`, `v` and `h`.
  have hkey : h * (u + v) * (u * v - 1) = 2 * u * v := by
    linear_combination -(v * e2u + u * e2v)
  have hperim : 1 + c1 + d1 = h * (u + v) := by linarith [hu, hv]
  have huv2 : u + v ≠ 0 := (add_pos hu_pos hv_pos).ne'
  have hmul : h * (u + v) ≠ 0 := mul_ne_zero hh.ne' huv2
  have step1 : (h / 2) / (h * (u + v)) ^ 2 = 1 / (2 * h * (u + v) ^ 2) := by
    field_simp [hh.ne', hmul]
  have h4f : 4 * f u v = 4 * u * v * (u + v) / (u * v - 1) := by
    unfold f
    ring
  have step2 : 4 * f u v = 2 * h * (u + v) ^ 2 := by
    rw [h4f, div_eq_iff huv]
    linear_combination -2 * (u + v) * hkey
  rw [hperim, step1, step2]

/-- The area of a triangle with base from `(0,0)` to `(1,0)`. -/
lemma area_eq (P : ℝ × ℝ) (hP2 : 0 < P.2) : area P (0, 0) (1, 0) = P.2 / 2 := by
  show |(P.1 * ((0 : ℝ) - 0) + 0 * (0 - P.2) + 1 * (P.2 - 0))| / 2 = P.2 / 2
  rw [show P.1 * ((0 : ℝ) - 0) + 0 * (0 - P.2) + 1 * (P.2 - 0) = P.2 by ring,
    abs_of_pos hP2]

/-- The perimeter of a triangle with base from `(0,0)` to `(1,0)`. -/
lemma perimeter_eq (P : ℝ × ℝ) :
    perimeter P (0, 0) (1, 0) = 1 + √(P.1 ^ 2 + P.2 ^ 2) + √((1 - P.1) ^ 2 + P.2 ^ 2) := by
  show √((P.1 - (0 : ℝ)) ^ 2 + (P.2 - 0) ^ 2) + √(((0 : ℝ) - 1) ^ 2 + (0 - 0) ^ 2) +
      √((1 - P.1) ^ 2 + (0 - P.2) ^ 2) = _
  rw [show (P.1 - (0 : ℝ)) ^ 2 + (P.2 - 0) ^ 2 = P.1 ^ 2 + P.2 ^ 2 by ring,
    show ((0 : ℝ) - 1) ^ 2 + (0 - 0) ^ 2 = (1 : ℝ) by norm_num,
    show (1 - P.1) ^ 2 + (0 - P.2) ^ 2 = (1 - P.1) ^ 2 + P.2 ^ 2 by ring,
    Real.sqrt_one]
  ring

snip end

/-- Since the ratio `area / perimeter ^ 2` of a triangle is invariant under translations,
rotations and scaling, we may place the equilateral triangle at
`A = (1/2, √3/2)`, `B = (0, 0)`, `C = (1, 0)`. -/
problem usa1982_p3 (D E : ℝ × ℝ)
    (hD : Inside D (1 / 2, √3 / 2) (0, 0) (1, 0))
    (hE : Inside E D (0, 0) (1, 0)) :
    area D (0, 0) (1, 0) / (perimeter D (0, 0) (1, 0)) ^ 2 >
      area E (0, 0) (1, 0) / (perimeter E (0, 0) (1, 0)) ^ 2 := by
  obtain ⟨α, β, γ, hα, hβ, hγ, hsum, hDeq⟩ := hD
  obtain ⟨α', β', γ', hα', hβ', hγ', hsum', hEeq⟩ := hE
  have h3 : (0 : ℝ) < √3 := Real.sqrt_pos.mpr (by norm_num)
  -- Coordinates of `D = α • A + β • B + γ • C`.
  have hD12 : D = (α / 2 + γ, α * (√3 / 2)) := by
    rw [hDeq]
    apply Prod.ext
    · show (α * (1 / 2 : ℝ) + β * 0) + γ * 1 = α / 2 + γ
      ring
    · show (α * (√3 / 2 : ℝ) + β * 0) + γ * 0 = α * (√3 / 2)
      ring
  have hD1 : D.1 = α / 2 + γ := by rw [hD12]
  have hD2 : D.2 = α * (√3 / 2) := by rw [hD12]
  have hd2 : 0 < D.2 := by
    rw [hD2]
    exact mul_pos hα (by positivity)
  have hd1 : 0 < D.1 := by
    rw [hD1]
    linarith [hα, hγ]
  have h1D : 0 < 1 - D.1 := by
    rw [hD1]
    linarith [hα, hβ, hsum]
  have hd1' : D.1 < 1 := by linarith [h1D]
  -- The angles of `DBC` at `B` and `C` are less than `60°`: `D.2 < √3 * D.1` and
  -- `D.2 < √3 * (1 - D.1)`.
  have h3a : D.2 < √3 * D.1 := by
    rw [hD1, hD2]
    nlinarith [mul_pos h3 hγ]
  have h3b : D.2 < √3 * (1 - D.1) := by
    rw [hD2]
    have e1 : 1 - D.1 = α / 2 + β := by
      rw [hD1]
      linarith [hsum]
    rw [e1]
    nlinarith [mul_pos h3 hβ]
  -- Coordinates of `E = α' • D + β' • B + γ' • C`.
  have hE12 : E = (α' * D.1 + γ', α' * D.2) := by
    rw [hEeq]
    apply Prod.ext
    · show (α' * D.1 + β' * 0) + γ' * 1 = α' * D.1 + γ'
      ring
    · show (α' * D.2 + β' * 0) + γ' * 0 = α' * D.2
      ring
  have hE1 : E.1 = α' * D.1 + γ' := by rw [hE12]
  have hE2 : E.2 = α' * D.2 := by rw [hE12]
  have he2 : 0 < E.2 := by
    rw [hE2]
    exact mul_pos hα' hd2
  have he1 : 0 < E.1 := by
    rw [hE1]
    exact add_pos (mul_pos hα' hd1) hγ'
  have h1E : 0 < 1 - E.1 := by
    have e1 : 1 - E.1 = α' * (1 - D.1) + β' := by
      rw [hE1]
      linarith [hsum']
    rw [e1]
    exact add_pos (mul_pos hα' h1D) hβ'
  have he1' : E.1 < 1 := by linarith [h1E]
  -- The angles of `EBC` at `B` and `C` are strictly smaller than those of `DBC`,
  -- so the half-angle cotangents strictly increase.
  have hslt1 : D.1 / D.2 < E.1 / E.2 := by
    rw [hE1, hE2]
    have e1 : (α' * D.1 + γ') / (α' * D.2) = D.1 / D.2 + γ' / (α' * D.2) := by
      rw [add_div, mul_div_mul_left _ _ hα'.ne']
    rw [e1]
    have hpos : 0 < γ' / (α' * D.2) := div_pos hγ' (mul_pos hα' hd2)
    linarith
  have hslt2 : (1 - D.1) / D.2 < (1 - E.1) / E.2 := by
    have e1 : 1 - E.1 = α' * (1 - D.1) + β' := by
      rw [hE1]
      linarith [hsum']
    rw [hE2, e1]
    have e2 : (α' * (1 - D.1) + β') / (α' * D.2) = (1 - D.1) / D.2 + β' / (α' * D.2) := by
      rw [add_div, mul_div_mul_left _ _ hα'.ne']
    rw [e2]
    have hpos : 0 < β' / (α' * D.2) := div_pos hβ' (mul_pos hα' hd2)
    linarith
  -- Apply the analytic machinery.
  set uD := (√(D.1 ^ 2 + D.2 ^ 2) + D.1) / D.2 with huD_def
  set vD := (√((1 - D.1) ^ 2 + D.2 ^ 2) + (1 - D.1)) / D.2 with hvD_def
  set uE := (√(E.1 ^ 2 + E.2 ^ 2) + E.1) / E.2 with huE_def
  set vE := (√((1 - E.1) ^ 2 + E.2 ^ 2) + (1 - E.1)) / E.2 with hvE_def
  have huD : √3 < uD := u_gt_sqrt3 hd1 hd2 h3a
  have hvD : √3 < vD := u_gt_sqrt3 h1D hd2 h3b
  have huE : uD < uE := u_lt hd1 hd2 he1 he2 hslt1
  have hvE : vD < vE := u_lt h1D hd2 h1E he2 hslt2
  have hfD : 0 < f uD vD := f_pos huD hvD
  have hflt : f uD vD < f uE vE := f_strictMono huD huE hvD hvE
  have eD : area D (0, 0) (1, 0) / (perimeter D (0, 0) (1, 0)) ^ 2 = 1 / (4 * f uD vD) := by
    rw [area_eq D hd2, perimeter_eq D]
    exact area_div_perimeter_sq hd1 hd1' hd2
  have eE : area E (0, 0) (1, 0) / (perimeter E (0, 0) (1, 0)) ^ 2 = 1 / (4 * f uE vE) := by
    rw [area_eq E he2, perimeter_eq E]
    exact area_div_perimeter_sq he1 he1' he2
  rw [eD, eE]
  exact one_div_lt_one_div_of_lt (by linarith [hfD]) (by linarith [hflt])

end Usa1982P3
