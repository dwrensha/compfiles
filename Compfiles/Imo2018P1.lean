/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 2018, Problem 1

Let Γ be the circumcircle of acute triangle ABC. Points D and E lie on segments
AB and AC, respectively, such that AD = AE. The perpendicular bisectors of BD
and CE intersect the minor arcs AB and AC of Γ at points F and G, respectively.
Prove that the lines DE and FG are parallel.

## Formalization notes

We work in Cartesian coordinates, placing `A` at the origin and the internal
angle bisector of `∠BAC` along the positive x-axis; this is without loss of
generality since all hypotheses and the conclusion are invariant under rigid
motions of the plane. Writing `2α` for the angle at `A`, `c = AB`, `b = AC` and
`d = AD = AE`, the points are `A = (0, 0)`, `B = (c cos α, c sin α)`,
`C = (b cos α, -b sin α)`, `D = (d cos α, d sin α)` and `E = (d cos α, -d sin α)`.
The hypotheses `0 < d`, `d < b` and `d < c` say that `D` and `E` lie strictly
inside the segments `AB` and `AC` (the endpoint cases are degenerate: if
`D = B` or `E = C` there is no perpendicular bisector to speak of, and if
`D = E = A` there is no line `DE`). The circumcircle `Γ` is given through its
center `O`, equidistant from `A`, `B` and `C`. That `F` lies on the minor arc
`AB` is expressed as: `F` is on the circle and on the opposite side of the line
`AB` from `C` (a strict sign condition on a 2D cross product), and similarly
for `G`. The conclusion says that the cross product of the direction vectors
`G - F` and `E - D` vanishes, i.e. that the lines are parallel. Note that the
acuteness of `ABC` is not needed for the proof (it is only used in the problem
to guarantee that the points `F` and `G` on the minor arcs exist).

The proof is a coordinate computation. With `S = sin α` and `C = cos α`, both
`F.1` and `G.1` turn out to be roots of one and the same quadratic
`4C·X² - 2K·X + C(b+d)(c+d)`, where `K = S²(b+c) + C²(b+c+2d)`. The side
(arc) conditions give `2·F.1 < C(c+d)` and `2·G.1 < C(b+d)`, while the
quadratic is strictly negative both at `C(c+d)/2` and at `C(b+d)/2`; together
these force `F.1 = G.1`, which says exactly that `FG` is parallel to the
vertical line `DE`.
-/

namespace Imo2018P1

snip begin

/-- Key algebraic step: if `(x, y)` lies on the circle with center `(o₁, o₂)`
passing through the origin, where `4 * o₁ * C = e + f` and `4 * o₂ * S = e - f`,
and on the line `2 * (x * C + y * S) = e + d`, then `x` is a root of the
quadratic `4C·X² - 2K·X + C(e+d)(f+d)` with `K = S²(e+f) + C²(e+f+2d)`. -/
lemma quad_eq (x y o₁ o₂ e f S C d : ℝ)
    (hcirc : x ^ 2 + y ^ 2 = 2 * o₁ * x + 2 * o₂ * y)
    (hperp : 2 * (x * C + y * S) = e + d)
    (h1 : 4 * o₁ * C = e + f) (h2 : 4 * o₂ * S = e - f)
    (hsincos : S ^ 2 + C ^ 2 = 1) :
    4 * C * x ^ 2 - 2 * (S ^ 2 * (e + f) + C ^ 2 * (e + f + 2 * d)) * x +
      C * (e + d) * (f + d) = 0 := by
  linear_combination
    (4 * C * S ^ 2) * hcirc + (C * (e - f - 2 * S * y - (e + d - 2 * x * C))) * hperp +
      (2 * S ^ 2 * x) * h1 + (2 * C * S * y) * h2 - (4 * C * x ^ 2) * hsincos

snip end

problem imo2018_p1
    (b c d α : ℝ) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hdb : d < b) (hdc : d < c)
    (hα0 : 0 < α) (hα : α < Real.pi / 2) (O F G : ℝ × ℝ)
    -- `O` is equidistant from `A = (0, 0)`, `B` and `C` (the circumcenter).
    (hOB : (O.1 - c * Real.cos α) ^ 2 + (O.2 - c * Real.sin α) ^ 2 = O.1 ^ 2 + O.2 ^ 2)
    (hOC : (O.1 - b * Real.cos α) ^ 2 + (O.2 + b * Real.sin α) ^ 2 = O.1 ^ 2 + O.2 ^ 2)
    -- `F` and `G` lie on the circumcircle (the circle with center `O` through `A`).
    (hFO : (F.1 - O.1) ^ 2 + (F.2 - O.2) ^ 2 = O.1 ^ 2 + O.2 ^ 2)
    (hGO : (G.1 - O.1) ^ 2 + (G.2 - O.2) ^ 2 = O.1 ^ 2 + O.2 ^ 2)
    -- `F` is on the perpendicular bisector of `BD`; `G` on that of `CE`.
    (hFB : (F.1 - c * Real.cos α) ^ 2 + (F.2 - c * Real.sin α) ^ 2 =
       (F.1 - d * Real.cos α) ^ 2 + (F.2 - d * Real.sin α) ^ 2)
    (hGC : (G.1 - b * Real.cos α) ^ 2 + (G.2 + b * Real.sin α) ^ 2 =
       (G.1 - d * Real.cos α) ^ 2 + (G.2 + d * Real.sin α) ^ 2)
    -- `F` is on the opposite side of the line `AB` from `C` (i.e. on the minor
    -- arc `AB`), and `G` on the opposite side of the line `AC` from `B`.
    (hsideF : (c * Real.cos α * F.2 - c * Real.sin α * F.1) *
        (c * Real.cos α * (-(b * Real.sin α)) - c * Real.sin α * (b * Real.cos α)) < 0)
    (hsideG : (b * Real.cos α * G.2 + b * Real.sin α * G.1) *
        (b * Real.cos α * (c * Real.sin α) + b * Real.sin α * (c * Real.cos α)) < 0) :
    -- The direction vectors `G - F` and `E - D` have vanishing cross product.
    (G.1 - F.1) * (-(d * Real.sin α) - d * Real.sin α) =
      (G.2 - F.2) * (d * Real.cos α - d * Real.cos α) := by
  set S := Real.sin α with hSdef
  set C := Real.cos α with hCdef
  have hαpi : α < Real.pi := by linarith [hα, Real.pi_pos]
  have hS : 0 < S := Real.sin_pos_of_pos_of_lt_pi hα0 hαpi
  have hC : 0 < C := Real.cos_pos_of_mem_Ioo ⟨by linarith [hα0, Real.pi_pos], hα⟩
  have hsincos : S ^ 2 + C ^ 2 = 1 := Real.sin_sq_add_cos_sq α
  -- Circumcenter relations: `4 * O.1 * C = b + c` and `4 * O.2 * S = c - b`.
  have hOB' : c ^ 2 * (C ^ 2 + S ^ 2) = 2 * c * (O.1 * C + O.2 * S) := by
    linear_combination hOB
  have e1 : 2 * c * (O.1 * C + O.2 * S) = c ^ 2 := by
    linear_combination -hOB' + c ^ 2 * hsincos
  have e1' : 2 * (O.1 * C + O.2 * S) = c :=
    mul_left_cancel₀ (ne_of_gt hc) (by linear_combination e1)
  have hOC' : b ^ 2 * (C ^ 2 + S ^ 2) = 2 * b * (O.1 * C - O.2 * S) := by
    linear_combination hOC
  have e2 : 2 * b * (O.1 * C - O.2 * S) = b ^ 2 := by
    linear_combination -hOC' + b ^ 2 * hsincos
  have e2' : 2 * (O.1 * C - O.2 * S) = b :=
    mul_left_cancel₀ (ne_of_gt hb) (by linear_combination e2)
  have hO1 : 4 * O.1 * C = b + c := by linear_combination e1' + e2'
  have hO2 : 4 * O.2 * S = c - b := by linear_combination e1' - e2'
  -- The perpendicular bisector conditions as line equations.
  have stepF : (d - c) * (2 * (F.1 * C + F.2 * S) - (c + d)) = 0 := by
    linear_combination hFB + ((d + c) * (d - c)) * hsincos
  have hFperp : 2 * (F.1 * C + F.2 * S) = c + d :=
    eq_of_sub_eq_zero ((mul_eq_zero.mp stepF).resolve_left (sub_ne_zero.mpr hdc.ne))
  have stepG : (d - b) * (2 * (G.1 * C - G.2 * S) - (b + d)) = 0 := by
    linear_combination hGC + ((d - b) * (b + d)) * hsincos
  have hGperp : 2 * (G.1 * C - G.2 * S) = b + d :=
    eq_of_sub_eq_zero ((mul_eq_zero.mp stepG).resolve_left (sub_ne_zero.mpr hdb.ne))
  -- The circle equations.
  have hFQ : F.1 ^ 2 + F.2 ^ 2 = 2 * O.1 * F.1 + 2 * O.2 * F.2 := by
    linear_combination hFO
  have hGQ : G.1 ^ 2 + G.2 ^ 2 = 2 * O.1 * G.1 + 2 * O.2 * G.2 := by
    linear_combination hGO
  -- The side conditions, simplified.
  have hbcsc : 0 < 2 * b * c * S * C := by positivity
  have hsideF' : 0 < c * C * F.2 - c * S * F.1 := by
    have hf2 : c * C * (-(b * S)) - c * S * (b * C) = -(2 * b * c * S * C) := by ring
    rw [hf2] at hsideF
    rcases mul_neg_iff.mp hsideF with h | h
    · exact h.1
    · exfalso; linarith [h.2, hbcsc]
  have hsideF'' : 0 < C * F.2 - S * F.1 := by
    have e : c * C * F.2 - c * S * F.1 = c * (C * F.2 - S * F.1) := by ring
    rw [e] at hsideF'
    exact (mul_pos_iff_of_pos_left hc).mp hsideF'
  have side1 : 2 * F.1 < C * (c + d) := by
    have hmul : 0 < S * (C * F.2 - S * F.1) := mul_pos hS hsideF''
    have hperpC : C * (2 * (F.1 * C + F.2 * S)) = C * (c + d) := by rw [hFperp]
    have hx : 2 * F.1 * (S ^ 2 + C ^ 2) = 2 * F.1 := by rw [hsincos]; ring
    linarith [hmul, hperpC, hx]
  have hsideG' : b * C * G.2 + b * S * G.1 < 0 := by
    have hg2 : b * C * (c * S) + b * S * (c * C) = 2 * b * c * S * C := by ring
    rw [hg2] at hsideG
    rcases mul_neg_iff.mp hsideG with h | h
    · exfalso; linarith [h.2, hbcsc]
    · exact h.1
  have hsideG'' : C * G.2 + S * G.1 < 0 := by
    have e : b * C * G.2 + b * S * G.1 = b * (C * G.2 + S * G.1) := by ring
    rw [e] at hsideG'
    rcases mul_neg_iff.mp hsideG' with h | h
    · exact h.2
    · exfalso; linarith [h.1, hb]
  have side2 : 2 * G.1 < C * (b + d) := by
    have hmul : S * (C * G.2 + S * G.1) < 0 := mul_neg_of_pos_of_neg hS hsideG''
    have hperpC : C * (2 * (G.1 * C - G.2 * S)) = C * (b + d) := by rw [hGperp]
    have hx : 2 * G.1 * (S ^ 2 + C ^ 2) = 2 * G.1 := by rw [hsincos]; ring
    linarith [hmul, hperpC, hx]
  -- Both `F.1` and `G.1` are roots of `4C·X² - 2K·X + C(b+d)(c+d)`.
  set KK := S ^ 2 * (b + c) + C ^ 2 * (b + c + 2 * d) with hKK
  set MM := C * (b + d) * (c + d) with hMM
  have hqF0 := quad_eq F.1 F.2 O.1 O.2 c b S C d hFQ hFperp
    (by linear_combination hO1) hO2 hsincos
  have hqF : 4 * C * F.1 ^ 2 - 2 * KK * F.1 + MM = 0 := by
    rw [hKK, hMM]; linear_combination hqF0
  have hqG0 := quad_eq G.1 (-G.2) O.1 (-O.2) b c S C d
    (by linear_combination hGQ) (by linear_combination hGperp) hO1
    (by linear_combination -hO2) hsincos
  have hqG : 4 * C * G.1 ^ 2 - 2 * KK * G.1 + MM = 0 := by
    rw [hKK, hMM]; linear_combination hqG0
  -- The quadratic is strictly negative at `C(c+d)/2` and at `C(b+d)/2`.
  have ht1 : 4 * C * (C * (c + d) / 2) ^ 2 - 2 * KK * (C * (c + d) / 2) + MM =
      C * (c + d) * S ^ 2 * (d - c) := by
    rw [hKK, hMM]; linear_combination (-(C * (c + d) * (b + d))) * hsincos
  have ht1neg : 4 * C * (C * (c + d) / 2) ^ 2 - 2 * KK * (C * (c + d) / 2) + MM < 0 := by
    rw [ht1]
    have hpos : 0 < C * (c + d) * S ^ 2 := by positivity
    have hneg : d - c < 0 := by linarith [hdc]
    exact mul_neg_of_pos_of_neg hpos hneg
  have ht2 : 4 * C * (C * (b + d) / 2) ^ 2 - 2 * KK * (C * (b + d) / 2) + MM =
      C * (b + d) * S ^ 2 * (d - b) := by
    rw [hKK, hMM]; linear_combination (-(C * (b + d) * (c + d))) * hsincos
  have ht2neg : 4 * C * (C * (b + d) / 2) ^ 2 - 2 * KK * (C * (b + d) / 2) + MM < 0 := by
    rw [ht2]
    have hpos : 0 < C * (b + d) * S ^ 2 := by positivity
    have hneg : d - b < 0 := by linarith [hdb]
    exact mul_neg_of_pos_of_neg hpos hneg
  -- Factor the quadratic around each of its two roots.
  have hfactF : ∀ X : ℝ, 4 * C * X ^ 2 - 2 * KK * X + MM =
      (X - F.1) * (4 * C * (X + F.1) - 2 * KK) + (4 * C * F.1 ^ 2 - 2 * KK * F.1 + MM) :=
    fun X ↦ by ring
  have hfact1 : (C * (c + d) / 2 - F.1) * (4 * C * (C * (c + d) / 2 + F.1) - 2 * KK) < 0 := by
    have h := hfactF (C * (c + d) / 2)
    rw [hqF] at h
    rw [h] at ht1neg
    linarith [ht1neg]
  have hF1 : F.1 < C * (c + d) / 2 := by linarith [side1]
  have hsign1 : 4 * C * (C * (c + d) / 2 + F.1) - 2 * KK < 0 := by
    rcases mul_neg_iff.mp hfact1 with h | h
    · exact h.2
    · exfalso; linarith [h.1, hF1]
  have hfactG : ∀ X : ℝ, 4 * C * X ^ 2 - 2 * KK * X + MM =
      (X - G.1) * (4 * C * (X + G.1) - 2 * KK) + (4 * C * G.1 ^ 2 - 2 * KK * G.1 + MM) :=
    fun X ↦ by ring
  have hfact2 : (C * (b + d) / 2 - G.1) * (4 * C * (C * (b + d) / 2 + G.1) - 2 * KK) < 0 := by
    have h := hfactG (C * (b + d) / 2)
    rw [hqG] at h
    rw [h] at ht2neg
    linarith [ht2neg]
  have hG1 : G.1 < C * (b + d) / 2 := by linarith [side2]
  have hsign2 : 4 * C * (C * (b + d) / 2 + G.1) - 2 * KK < 0 := by
    rcases mul_neg_iff.mp hfact2 with h | h
    · exact h.2
    · exfalso; linarith [h.1, hG1]
  -- If `F.1 ≠ G.1`, the factorization forces `C(c+d)/2 < G.1` and
  -- `C(b+d)/2 < F.1`, contradicting the side conditions.
  have hFGx : F.1 = G.1 := by
    by_contra hne
    have hz : (G.1 - F.1) * (4 * C * (F.1 + G.1) - 2 * KK) = 0 := by
      have h := hfactF G.1
      rw [hqF] at h
      rw [hqG] at h
      linarith [h]
    rcases mul_eq_zero.mp hz with hz1 | hz2
    · exact hne (eq_of_sub_eq_zero hz1).symm
    · have hK2 : 4 * C * (F.1 + G.1) = 2 * KK := by linarith [hz2]
      have h4C : 0 < 4 * C := by linarith [hC]
      have ht1G : C * (c + d) / 2 < G.1 := by
        have hlt : 4 * C * (C * (c + d) / 2 + F.1) < 4 * C * (F.1 + G.1) := by
          linarith [hsign1, hK2]
        have h2 := lt_of_mul_lt_mul_left hlt h4C.le
        linarith [h2]
      have ht2F : C * (b + d) / 2 < F.1 := by
        have hlt : 4 * C * (C * (b + d) / 2 + G.1) < 4 * C * (F.1 + G.1) := by
          linarith [hsign2, hK2]
        have h2 := lt_of_mul_lt_mul_left hlt h4C.le
        linarith [h2]
      linarith [hF1, ht1G, hG1, ht2F]
  rw [hFGx]
  ring

end Imo2018P1
