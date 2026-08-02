/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1962, Problem 6

The radius of the circumcircle of an isosceles triangle is R and the radius of its
inscribed circle is r. Prove that the distance between the two centers is
√(R(R - 2r)).

# Formalization notes

Every isosceles triangle is congruent to a unique triangle with vertices
`A = (0, h)`, `B = (-x, 0)`, `C = (x, 0)` with `0 < x` (half the base) and `0 < h`
(the height).  We therefore prove the formula for triangles in this normal form,
with the circumcenter, circumradius, incenter and inradius given by their explicit
values.  The lemma `dist_circumcenter` checks that the point we call the
circumcenter is indeed equidistant from the three vertices, at distance
`circumradius`; similarly the defining relation of the incenter
(`inradius x h * (x + leg x h) = x * h`, i.e. `r = area / semiperimeter`) is the
key hypothesis `hr` used in the proof.
-/

namespace Imo1962P6

snip begin

/-- Apex `A = (0, h)` of the normalized isosceles triangle. -/
def apex (h : ℝ) : EuclideanSpace ℝ (Fin 2) := !₂[0, h]

/-- Base vertex `B = (-x, 0)` of the normalized isosceles triangle. -/
def baseL (x : ℝ) : EuclideanSpace ℝ (Fin 2) := !₂[-x, 0]

/-- Base vertex `C = (x, 0)` of the normalized isosceles triangle. -/
def baseR (x : ℝ) : EuclideanSpace ℝ (Fin 2) := !₂[x, 0]

/-- The common length `√(x² + h²)` of the two equal sides `AB` and `AC`. -/
noncomputable def leg (x h : ℝ) : ℝ := Real.sqrt (x ^ 2 + h ^ 2)

/-- The circumradius `R = (x² + h²) / (2h)`. -/
noncomputable def circumradius (x h : ℝ) : ℝ := (x ^ 2 + h ^ 2) / (2 * h)

/-- The inradius `r = xh / (x + √(x² + h²))`, i.e. area over semiperimeter. -/
noncomputable def inradius (x h : ℝ) : ℝ := x * h / (x + leg x h)

/-- The circumcenter `(0, h - R)`: it lies on the axis of symmetry. -/
noncomputable def circumcenter (x h : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[0, h - circumradius x h]

/-- The incenter `(0, r)`: it lies on the axis of symmetry at height `r`. -/
noncomputable def incenter (x h : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[0, inradius x h]

/-- The Euclidean distance between two explicitly given points of the plane. -/
lemma dist_eq_sqrt (a b c d : ℝ) :
    dist (!₂[a, b] : EuclideanSpace ℝ (Fin 2)) !₂[c, d] =
      Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp [Real.dist_eq, sq_abs]

/-- The circumcenter is equidistant from the three vertices, at distance `R`. -/
lemma dist_circumcenter (x h : ℝ) (hx : 0 < x) (hh : 0 < h) :
    dist (circumcenter x h) (apex h) = circumradius x h ∧
    dist (circumcenter x h) (baseL x) = circumradius x h ∧
    dist (circumcenter x h) (baseR x) = circumradius x h := by
  have hsq : 0 < x ^ 2 + h ^ 2 := by positivity
  have hRpos : 0 < circumradius x h := by unfold circumradius; positivity
  have hR : 2 * h * circumradius x h = x ^ 2 + h ^ 2 := by
    unfold circumradius
    field_simp
  refine ⟨?_, ?_, ?_⟩
  · show dist (!₂[0, h - circumradius x h] : EuclideanSpace ℝ (Fin 2)) !₂[0, h] = _
    rw [dist_eq_sqrt,
      show (0 - 0 : ℝ) ^ 2 + (h - circumradius x h - h) ^ 2 =
        (circumradius x h) ^ 2 by ring]
    exact Real.sqrt_sq hRpos.le
  · show dist (!₂[0, h - circumradius x h] : EuclideanSpace ℝ (Fin 2)) !₂[-x, 0] = _
    rw [dist_eq_sqrt,
      show (0 - -x : ℝ) ^ 2 + (h - circumradius x h - 0) ^ 2 =
        (circumradius x h) ^ 2 by linear_combination -hR]
    exact Real.sqrt_sq hRpos.le
  · show dist (!₂[0, h - circumradius x h] : EuclideanSpace ℝ (Fin 2)) !₂[x, 0] = _
    rw [dist_eq_sqrt,
      show (0 - x : ℝ) ^ 2 + (h - circumradius x h - 0) ^ 2 =
        (circumradius x h) ^ 2 by linear_combination -hR]
    exact Real.sqrt_sq hRpos.le

snip end

problem imo1962_p6 (x h : ℝ) (hx : 0 < x) (hh : 0 < h) :
    dist (circumcenter x h) (incenter x h) =
      Real.sqrt (circumradius x h * (circumradius x h - 2 * inradius x h)) := by
  have hsq : 0 < x ^ 2 + h ^ 2 := by positivity
  have hc : (leg x h) ^ 2 = x ^ 2 + h ^ 2 := Real.sq_sqrt hsq.le
  have hcpos : 0 < leg x h := Real.sqrt_pos.mpr hsq
  have hxc : (0 : ℝ) < x + leg x h := add_pos hx hcpos
  have hR : 2 * h * circumradius x h = x ^ 2 + h ^ 2 := by
    unfold circumradius
    field_simp
  have hr : inradius x h * (x + leg x h) = x * h := by
    unfold inradius
    field_simp
  set c := leg x h with hce
  set R := circumradius x h with hRe
  set r := inradius x h with hre
  -- Squaring `r(x + c) = xh` and using `c² = x² + h²` gives `r²h = x²(h - 2r)`.
  have h1' : (x + c) ^ 2 = 2 * x * (x + c) + h ^ 2 := by linear_combination hc
  have h4 : x ^ 2 * h ^ 2 = r ^ 2 * (x + c) ^ 2 := by
    linear_combination -(r * (x + c) + x * h) * hr
  have h5' : x ^ 2 * h ^ 2 - 2 * x ^ 2 * r * h - r ^ 2 * h ^ 2 = 0 := by
    linear_combination h4 + r ^ 2 * h1' + 2 * x * r * hr
  -- The squared distance formula: `(h - R - r)² = R(R - 2r)`.
  have hG : h ^ 2 * ((h - R - r) ^ 2 - (R ^ 2 - 2 * R * r)) = 0 := by
    linear_combination -h5' + (2 * h * r - h ^ 2) * hR
  have hG2 : R * (R - 2 * r) = (h - R - r) ^ 2 := by
    have hh2 : h ^ 2 ≠ 0 := by positivity
    rcases mul_eq_zero.mp hG with h0 | h0
    · exact absurd h0 hh2
    · linear_combination -h0
  -- Both centers lie on the axis of symmetry, so the distance is `|h - R - r|`.
  show dist (!₂[0, h - R] : EuclideanSpace ℝ (Fin 2)) !₂[0, r] = _
  rw [dist_eq_sqrt]
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_add]
  rw [hG2]

end Imo1962P6
