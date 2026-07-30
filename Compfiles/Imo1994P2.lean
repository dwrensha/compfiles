/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.AffineSpace.Midpoint
public import Mathlib.Analysis.Convex.Segment
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1994, Problem 2

ABC is an isosceles triangle with AB = AC. M is the midpoint of BC and O is
the point on the line AM such that OB is perpendicular to AB. Q is an
arbitrary point on BC different from B and C. E lies on the line AB and F
lies on the line AC such that E, Q, F are distinct and collinear. Prove that
OQ is perpendicular to EF if and only if QE = QF.
-/

namespace Imo1994P2

open scoped Affine RealInnerProductSpace

/-- The Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/- The statement of the problem is invariant under rigid motions and
dilations of the plane, so we may place the triangle in standard position:
`B = (-1, 0)`, `C = (1, 0)` (hence `M = (0, 0)`) and `A = (0, a)` with
`0 < a` — the isosceles condition `AB = AC` says exactly that `A` lies on the
perpendicular bisector of `BC`, i.e. on the `y`-axis.  The point `O` is then
forced to be `(0, -1/a)`, and writing `Q = (q, 0)`, `E = (e, a*(e+1))`,
`F = (f, a*(1-f))`, both sides of the conclusion reduce to polynomial
identities in `a, q, e, f`: with `s = e + f` and `d = e - f`, collinearity of
`E, Q, F` is `s² - 2qs = d² + 2d`, perpendicularity of `OQ` and `EF` is
`s = -qd`, and `QE = QF` is `d(s - 2q) + a²s(d + 2) = 0`; the claim follows
from `q ≠ ±1` (see `key_algebra` below). -/

snip begin

theorem Pt.ext {x y : Pt} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  apply WithLp.ofLp_injective (p := 2)
  funext i
  fin_cases i <;> assumption

lemma inner_pt (n x : Pt) : ⟪n, x⟫ = n 0 * x 0 + n 1 * x 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, RCLike.inner_apply]
  simp only [conj_trivial]
  ring

lemma dist_sq (x y : Pt) : dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _),
    Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]

/-- The algebraic heart of the problem.  Here `a > 0` (we only need `a ≠ 0`)
is the height of the triangle, `q` is the `x`-coordinate of `Q` (so `Q ≠ B, C`
means `q ≠ -1, 1`), and `e`, `f` are the `x`-coordinates of `E` and `F`.
The hypothesis `hcoll` says that `E, Q, F` are collinear, `hEF` says that
`E ≠ F`, and the conclusion is `OQ ⊥ EF ↔ QE = QF`. -/
lemma key_algebra {a q e f : ℝ} (ha : a ≠ 0) (hq1 : q ≠ 1) (hq2 : q ≠ -1)
    (hcoll : e * (1 + q) - f * (1 - q) = 2 * e * f)
    (hEF : e = f → e ≠ 0) :
    q * (e - f) + (e + f) = 0 ↔
      (q - e) ^ 2 + a ^ 2 * (e + 1) ^ 2 = (q - f) ^ 2 + a ^ 2 * (1 - f) ^ 2 := by
  constructor
  · -- Assume `OQ ⊥ EF`, i.e. `s = -q*d` where `s = e + f`, `d = e - f`.
    intro hperp
    have hsq : q ^ 2 - 1 ≠ 0 := by
      intro h
      have h1 : q ^ 2 = 1 := by linarith
      rcases sq_eq_one_iff.mp h1 with h2 | h2
      · exact hq1 h2
      · exact hq2 h2
    -- Collinearity and perpendicularity give `(q² - 1) * d * (d + 2) = 0`.
    have hfac : (q ^ 2 - 1) * ((e - f) * ((e - f) + 2)) = 0 := by
      linear_combination -2 * hcoll + (-(e + f) + q * (e - f) + 2 * q) * hperp
    have hfac2 : (e - f) * ((e - f) + 2) = 0 :=
      (mul_eq_zero.mp hfac).resolve_left hsq
    rcases mul_eq_zero.mp hfac2 with hd | hd2
    · -- `d = 0`: then `s = 0` and the distances are equal.
      linear_combination 2 * a ^ 2 * hperp +
        ((e + f) - 2 * q + a ^ 2 * (e + f) - 2 * a ^ 2 * q) * hd
    · -- `d = -2`: then `s = 2q` and the distances are equal.
      linear_combination -2 * hperp + (e + f) * (1 + a ^ 2) * hd2
  · -- Assume `QE = QF`.
    intro hdist
    -- Collinearity and equal distances factor as `w * (w - 2) * (4q²a² + K²) = 0`
    -- with `w = d + 2` and `K = (1 + a²) * w - 2`.
    have hfact : (e - f + 2) * ((e - f) *
        (4 * q ^ 2 * a ^ 2 + ((1 + a ^ 2) * (e - f + 2) - 2) ^ 2)) = 0 := by
      linear_combination 2 * ((1 + a ^ 2) * (e - f + 2) - 2) ^ 2 * hcoll +
        ((e + f) * ((1 + a ^ 2) * (e - f + 2) - 2) + 2 * q * (e - f) -
          2 * q * ((1 + a ^ 2) * (e - f + 2) - 2)) * hdist
    rcases mul_eq_zero.mp hfact with hw | h23
    · -- `d = -2`: equal distances force `s = 2q`, hence `s = -q*d`.
      linear_combination -hdist / 2 + ((e + f) * (1 + a ^ 2) / 2) * hw
    · rcases mul_eq_zero.mp h23 with hd | h3
      · -- `d = 0`: equal distances force `e = f = 0`, i.e. `E = F`; contradiction.
        exfalso
        have hfe : e = f := sub_eq_zero.mp hd
        have h4 : 4 * a ^ 2 * e = 0 := by
          rw [← hfe] at hdist
          linear_combination hdist
        rcases mul_eq_zero.mp h4 with h4a | he0
        · exact ha (sq_eq_zero_iff.mp (by linarith : a ^ 2 = 0))
        · exact hEF hfe he0
      · -- `4q²a² + K² = 0`: then `q = 0` and `K = 0`, contradicting collinearity.
        have h3nn : 0 ≤ 4 * q ^ 2 * a ^ 2 := by positivity
        have hKnn : 0 ≤ ((1 + a ^ 2) * (e - f + 2) - 2) ^ 2 := sq_nonneg _
        rcases (add_eq_zero_iff_of_nonneg h3nn hKnn).mp h3 with ⟨h31, h32⟩
        have hq0 : q = 0 := by
          have hqa : q ^ 2 * a ^ 2 = 0 := by linarith
          rcases mul_eq_zero.mp hqa with hqz | haz
          · exact sq_eq_zero_iff.mp hqz
          · exact absurd (sq_eq_zero_iff.mp haz) ha
        have hK0 : (1 + a ^ 2) * (e - f + 2) - 2 = 0 := sq_eq_zero_iff.mp h32
        -- Collinearity would give `(1 + a²)² * s² + 4a² = 0`, impossible.
        have hcon : (1 + a ^ 2) ^ 2 * (e + f) ^ 2 + 4 * a ^ 2 = 0 := by
          linear_combination -2 * (1 + a ^ 2) ^ 2 * hcoll +
            2 * (1 + a ^ 2) ^ 2 * (e + f) * hq0 +
            ((1 + a ^ 2) * (e - f + 2) - 2 + 4 - 2 * (1 + a ^ 2)) * hK0
        have hpos : 0 < (1 + a ^ 2) ^ 2 * (e + f) ^ 2 + 4 * a ^ 2 := by
          have hsp : 0 ≤ (1 + a ^ 2) ^ 2 * (e + f) ^ 2 := by positivity
          have hap : 0 < 4 * a ^ 2 := by positivity
          linarith
        exact absurd hcon (ne_of_gt hpos)

snip end

problem imo1994_p2
    (a : ℝ) (ha : 0 < a)
    (A B C M O Q E F : Pt)
    (hA : A = !₂[0, a]) (hB : B = !₂[-1, 0]) (hC : C = !₂[1, 0])
    (hM : M = midpoint ℝ B C)
    (hO_line : O ∈ line[ℝ, A, M])
    (hO_perp : ⟪O -ᵥ B, A -ᵥ B⟫ = 0)
    (hQ_seg : Q ∈ segment ℝ B C)
    (hQB : Q ≠ B) (hQC : Q ≠ C)
    (hE_line : E ∈ line[ℝ, A, B])
    (hF_line : F ∈ line[ℝ, A, C])
    (hcol : Collinear ℝ ({E, Q, F} : Set Pt))
    (hEQ : E ≠ Q) (hQF : Q ≠ F) (hEF : E ≠ F) :
    ⟪O -ᵥ Q, F -ᵥ E⟫ = 0 ↔ dist Q E = dist Q F := by
  have hane : a ≠ 0 := ne_of_gt ha
  -- Coordinate values of the base points.
  have hA0 : A 0 = 0 := by rw [hA]; simp
  have hA1 : A 1 = a := by rw [hA]; simp
  have hB0 : B 0 = -1 := by rw [hB]; simp
  have hB1 : B 1 = 0 := by rw [hB]; simp
  have hC0 : C 0 = 1 := by rw [hC]; simp
  have hC1 : C 1 = 0 := by rw [hC]; simp
  -- The midpoint of `BC` is the origin.
  have hMeq : M = !₂[0, 0] := by
    rw [hM, hB, hC, midpoint_eq_smul_add]
    apply Pt.ext <;> simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  -- `O` lies on the `y`-axis, i.e. its first coordinate vanishes.
  rcases mem_affineSpan_pair_iff_exists_lineMap_eq.mp hO_line with ⟨t, ht⟩
  have hO0 : O 0 = 0 := by
    rw [← ht, AffineMap.lineMap_apply, hA, hMeq]
    simp [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  -- Perpendicularity of `OB` and `AB` determines the second coordinate of `O`.
  have hperp0 : 1 + a * (O 1) = 0 := by
    have h := hO_perp
    rw [inner_pt] at h
    simp only [vsub_eq_sub, PiLp.sub_apply] at h
    rw [hO0, hA0, hA1, hB0, hB1] at h
    linarith
  have hO1 : O 1 = -1 / a := by
    field_simp
    linarith [hperp0]
  -- `Q` lies on the `x`-axis.
  rw [hB, hC, segment_eq_image_lineMap] at hQ_seg
  rcases hQ_seg with ⟨tQ, _, htQ⟩
  have hQ1 : Q 1 = 0 := by
    rw [← htQ, AffineMap.lineMap_apply]
    simp [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  -- `Q ≠ C` and `Q ≠ B` in coordinates.
  have hq1 : Q 0 ≠ 1 := by
    intro h
    exact hQC (Pt.ext (by rw [h, hC0]) (by rw [hQ1, hC1]))
  have hq2 : Q 0 ≠ -1 := by
    intro h
    exact hQB (Pt.ext (by rw [h, hB0]) (by rw [hQ1, hB1]))
  set q := Q 0 with hq
  -- `E` lies on the line `A(0,a)`, `B(-1,0)`: its coordinates satisfy `y = a*(x+1)`.
  have hE1 : E 1 = a * (E 0 + 1) := by
    rcases mem_affineSpan_pair_iff_exists_lineMap_eq.mp hE_line with ⟨rE, hrE⟩
    have h0 : E 0 = -rE := by
      rw [← hrE, AffineMap.lineMap_apply, hA, hB]
      simp [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    have h1 : E 1 = a - rE * a := by
      rw [← hrE, AffineMap.lineMap_apply, hA, hB]
      simp [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      ring
    rw [h1, h0]
    ring
  -- `F` lies on the line `A(0,a)`, `C(1,0)`: its coordinates satisfy `y = a*(1-x)`.
  have hF1 : F 1 = a * (1 - F 0) := by
    rcases mem_affineSpan_pair_iff_exists_lineMap_eq.mp hF_line with ⟨rF, hrF⟩
    have h0 : F 0 = rF := by
      rw [← hrF, AffineMap.lineMap_apply, hA, hC]
      simp [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    have h1 : F 1 = a - rF * a := by
      rw [← hrF, AffineMap.lineMap_apply, hA, hC]
      simp [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      ring
    rw [h1, h0]
    ring
  -- `E ≠ F` in coordinates.
  have hEF' : E 0 = F 0 → E 0 ≠ 0 := by
    intro he h0
    have hf0 : F 0 = 0 := by rw [← he]; exact h0
    apply hEF
    apply Pt.ext
    · exact he
    · rw [hE1, hF1, h0, hf0]
      norm_num
  -- Collinearity of `E, Q, F` in coordinates.
  have hQ_mem : Q ∈ line[ℝ, E, F] :=
    Collinear.mem_affineSpan_of_mem_of_ne hcol (by simp) (by simp) (by simp) hEF
  rcases mem_affineSpan_pair_iff_exists_lineMap_eq.mp hQ_mem with ⟨r, hr⟩
  have hQr0 : q = r * (F 0 - E 0) + E 0 := by
    rw [hq, ← hr, AffineMap.lineMap_apply]
    simp [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  have hQr1 : Q 1 = r * (F 1 - E 1) + E 1 := by
    rw [← hr, AffineMap.lineMap_apply]
    simp [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  have h1' : q - E 0 = r * (F 0 - E 0) := by linarith
  have h2 : a * (E 0 + 1) = r * a * (E 0 + F 0) := by
    rw [hQ1, hE1, hF1] at hQr1
    linarith
  have h2' : E 0 + 1 = r * (E 0 + F 0) :=
    mul_left_cancel₀ hane (by linear_combination h2)
  have hcoll : E 0 * (1 + q) - F 0 * (1 - q) = 2 * E 0 * F 0 := by
    linear_combination (E 0 + F 0) * h1' - (F 0 - E 0) * h2'
  -- Perpendicularity of `OQ` and `EF` in coordinates.
  have hperp_iff : (⟪O -ᵥ Q, F -ᵥ E⟫ = 0) ↔ q * (E 0 - F 0) + (E 0 + F 0) = 0 := by
    have hval : ⟪O -ᵥ Q, F -ᵥ E⟫ = q * (E 0 - F 0) + (E 0 + F 0) := by
      rw [inner_pt]
      simp only [vsub_eq_sub, PiLp.sub_apply]
      rw [hO0, hO1, hQ1, hE1, hF1, ← hq]
      field_simp
      ring
    rw [hval]
  -- Equality of distances in coordinates.
  have h2iff : (dist Q E = dist Q F) ↔ (dist Q E) ^ 2 = (dist Q F) ^ 2 :=
    (pow_left_inj₀ dist_nonneg dist_nonneg two_ne_zero).symm
  have hdist_iff : (dist Q E = dist Q F) ↔
      (q - E 0) ^ 2 + a ^ 2 * (E 0 + 1) ^ 2 = (q - F 0) ^ 2 + a ^ 2 * (1 - F 0) ^ 2 := by
    rw [h2iff, dist_sq, dist_sq, hQ1, hE1, hF1, ← hq]
    constructor <;> intro h <;> linear_combination h
  rw [hperp_iff, hdist_iff]
  exact key_algebra hane hq1 hq2 hcoll hEF'

end Imo1994P2
