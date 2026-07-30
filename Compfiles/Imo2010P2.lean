/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Convex.Side
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Geometry.Euclidean.Sphere.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 2010, Problem 2

Let `I` be the incenter of a triangle `ABC` and let `Γ` be its circumcircle.
Let line `AI` intersect `Γ` again at `D`. Let `E` be a point on arc `BDC` and
`F` a point on side `BC` such that `∠BAF = ∠CAE < ½∠BAC`. Finally, let `G`
be the midpoint of `IF`. Prove that `DG` and `EI` intersect on `Γ`.
-/

open Affine Complex ComplexConjugate EuclideanGeometry

open scoped EuclideanGeometry

namespace Imo2010P2

snip begin

/-- The 2D cross product (signed area) of two complex numbers viewed as real vectors. -/
noncomputable def cross (u v : ℂ) : ℝ := (conj u * v).im

lemma cross_self (u : ℂ) : cross u u = 0 := by
  rw [cross, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_im]

lemma cross_neg_left (u v : ℂ) : cross (-u) v = -cross u v := by
  simp only [cross, map_neg, neg_mul, Complex.neg_im]

lemma cross_neg_right (u v : ℂ) : cross u (-v) = -cross u v := by
  simp only [cross, mul_neg, Complex.neg_im]

lemma cross_comm (u v : ℂ) : cross u v = -cross v u := by
  have h : conj (conj u * v) = conj v * u := by simp [mul_comm]
  simp only [cross, ← h, Complex.conj_im, neg_neg]

lemma cross_add_left (u₁ u₂ v : ℂ) : cross (u₁ + u₂) v = cross u₁ v + cross u₂ v := by
  simp only [cross, map_add, add_mul, Complex.add_im]

lemma cross_add_right (u v₁ v₂ : ℂ) : cross u (v₁ + v₂) = cross u v₁ + cross u v₂ := by
  simp only [cross, mul_add, Complex.add_im]

lemma cross_sub_left (u₁ u₂ v : ℂ) : cross (u₁ - u₂) v = cross u₁ v - cross u₂ v := by
  simp only [cross, map_sub, sub_mul, Complex.sub_im]

lemma cross_sub_right (u v₁ v₂ : ℂ) : cross u (v₁ - v₂) = cross u v₁ - cross u v₂ := by
  simp only [cross, mul_sub, Complex.sub_im]

lemma cross_smul_left (r : ℝ) (u v : ℂ) : cross (r • u) v = r * cross u v := by
  simp only [cross, Complex.real_smul, map_mul, Complex.conj_ofReal, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma cross_smul_right (r : ℝ) (u v : ℂ) : cross u (r • v) = r * cross u v := by
  have e : (r • v : ℂ) = (r : ℂ) * v := Complex.real_smul
  simp only [cross, e, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma cross_ofReal_left (r : ℝ) (v : ℂ) : cross (r : ℂ) v = r * v.im := by
  simp only [cross, Complex.conj_ofReal, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero]

/-- Collinearity in the complex plane detected by vanishing of the cross product. -/
lemma collinear_iff_cross_eq_zero {x y z : ℂ} :
    Collinear ℝ ({x, y, z} : Set ℂ) ↔ cross (y - x) (z - x) = 0 := by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  constructor
  · rintro ⟨p₀, v, hv⟩
    obtain ⟨r₁, hr₁⟩ := hv y (by simp)
    obtain ⟨r₂, hr₂⟩ := hv z (by simp)
    obtain ⟨r₀, hr₀⟩ := hv x (by simp)
    simp only [vadd_eq_add] at hr₁ hr₂ hr₀
    have e1 : y - x = (r₁ - r₀) • v := by
      rw [hr₁, hr₀]; simp [sub_smul]
    have e2 : z - x = (r₂ - r₀) • v := by
      rw [hr₂, hr₀]; simp [sub_smul]
    rw [e1, e2, cross_smul_left, cross_smul_right, cross_self]
    simp
  · intro h
    have h3cases : ∀ p : ℂ, p ∈ ({x, y, z} : Set ℂ) → (p = x ∨ p = y ∨ p = z) := by
      intro p hp
      simpa using hp
    by_cases hyx : y = x
    · refine ⟨x, z - x, fun p hp => ?_⟩
      rcases h3cases p hp with hp1 | hp2 | hp3
      · exact ⟨0, by rw [hp1]; simp⟩
      · exact ⟨0, by rw [hp2, hyx]; simp⟩
      · exact ⟨1, by rw [hp3]; simp⟩
    · refine ⟨x, y - x, fun p hp => ?_⟩
      rcases h3cases p hp with hp1 | hp2 | hp3
      · exact ⟨0, by rw [hp1]; simp⟩
      · exact ⟨1, by rw [hp2]; simp⟩
      · rw [hp3]
        have hyx' : normSq (y - x) ≠ 0 := by
          rw [ne_eq, Complex.normSq_eq_zero]
          exact sub_ne_zero.mpr hyx
        have hNC : ((normSq (y - x) : ℝ) : ℂ) ≠ 0 := by
          norm_cast
        set rwit := (conj (y - x) * (z - x)).re / normSq (y - x) with hrwit
        refine ⟨rwit, ?_⟩
        have key : conj (y - x) * (z - x) = (rwit : ℂ) * (normSq (y - x) : ℂ) := by
          rw [hrwit]
          apply Complex.ext_iff.mpr
          refine ⟨?_, ?_⟩
          · have hre : ((↑((conj (y - x) * (z - x)).re / normSq (y - x)) : ℂ) *
                (normSq (y - x) : ℂ)).re = (conj (y - x) * (z - x)).re := by
              push_cast
              rw [div_mul_cancel₀ _ hNC, Complex.ofReal_re]
            exact hre.symm
          · rw [show (conj (y - x) * (z - x)).im = cross (y - x) (z - x) from rfl, h]
            push_cast
            rw [div_mul_cancel₀ _ hNC, Complex.ofReal_im]
        have h3 : z - x = rwit • (y - x) := by
          have h5 : (y - x) * (conj (y - x) * (z - x)) =
              (y - x) * ((rwit : ℂ) * (normSq (y - x) : ℂ)) := by
            rw [key]
          rw [← mul_assoc, Complex.mul_conj] at h5
          have h4 : ((normSq (y - x) : ℝ) : ℂ) * (z - x) =
              ((normSq (y - x) : ℝ) : ℂ) * ((rwit : ℂ) * (y - x)) := by
            rw [h5]
            ring
          have h6 : z - x = (rwit : ℂ) * (y - x) := mul_left_cancel₀ hNC h4
          rw [Complex.real_smul]
          exact h6
        conv_lhs => rw [show z = (z - x) + x from by simp [sub_add_cancel]]
        rw [vadd_eq_add]
        conv_lhs => rw [h3]

/-- On the unit circle, the conjugate is the inverse. -/
lemma conj_of_norm_one {w : ℂ} (hw : ‖w‖ = 1) : conj w = w⁻¹ := by
  have h1 : conj w * w = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self]
    norm_cast
    rw [Complex.normSq_eq_norm_sq, hw]
    norm_num
  exact eq_inv_of_mul_eq_one_left h1

/-- The main algebraic identity: with `a = X²`, `b = Y²`, `c = Z²`, incenter
`i = -(XY + YZ + ZX)`, arc midpoint `d = -YZ`, and `f`, `k` as in the solution,
the points `d`, `g = (i+f)/2` and `k` are collinear (cross product vanishes). -/
lemma main_identity (X Y Z e i f k d : ℂ)
    (hX0 : X ≠ 0) (hY0 : Y ≠ 0) (hZ0 : Z ≠ 0) (he0 : e ≠ 0)
    (hXc : star X = X⁻¹) (hYc : star Y = Y⁻¹) (hZc : star Z = Z⁻¹) (hec : star e = e⁻¹)
    (hi : i = -(X*Y+Y*Z+Z*X))
    (hf : f = (X^2*(Y^2+Z^2-e) - Y^2*Z^2)/(X^2-e))
    (hk : k = star e * (e - i)/(star i - star e))
    (hd : d = -(Y*Z))
    (hae : X^2 ≠ e)
    (hie : i ≠ e) :
    (k - (i+f)/2) * star (k - d) - star (k - (i+f)/2) * (k - d) = 0 := by
  have hic : star i = -(X+Y+Z)/(X*Y*Z) := by
    rw [hi]
    simp only [starRingEnd_apply, star_neg, star_add, star_mul, hXc, hYc, hZc]
    field_simp; ring
  have haee : X⁻¹^2 ≠ e⁻¹ := by rwa [ne_eq, inv_pow, inv_inj]
  have hiee : (-(X+Y+Z)/(X*Y*Z)) ≠ e⁻¹ := by
    rw [← hic, ← hec]; exact fun h => hie (star_injective h)
  have hXYZ0 : X*Y*Z ≠ 0 := mul_ne_zero (mul_ne_zero hX0 hY0) hZ0
  have h1 : (-(X*Y) - X*Z - Y*Z - e) ≠ 0 := by
    have h := sub_ne_zero.mpr hie
    rw [hi] at h
    convert h using 1
    ring
  have h1' : (X*(-Y-Z) - Y*Z - e) ≠ 0 := by
    convert h1 using 1
    ring
  have h2eq : (-(X+Y+Z)/(X*Y*Z) - e⁻¹) * (X*Y*Z*e) = -(X*Y*Z) - X*e - Y*e - Z*e := by
    field_simp
    ring
  have h2 : (-(X*Y*Z) - X*e - Y*e - Z*e) ≠ 0 :=
    h2eq ▸ mul_ne_zero (sub_ne_zero.mpr hiee) (mul_ne_zero hXYZ0 he0)
  have h1c : (-(Z*(Y+X) + X*Y) - e) ≠ 0 := by
    convert h1 using 1
    ring
  have h2c : (-(e*(X+Y+Z)) - X*Y*Z) ≠ 0 := by
    convert h2 using 1
    ring
  rw [hd, hk, hf]
  simp only [starRingEnd_apply, star_sub, star_add, star_neg, star_mul, star_pow, star_div₀,
    star_ofNat, star_inv₀, star_star, hic, hec, hXc, hYc, hZc, inv_pow]
  subst hi
  field_simp [sub_ne_zero, hX0, hY0, hZ0, he0, hae, haee, hie, hiee, hXYZ0, h1c, h2c]
  ring

/-- The polynomial certificate underlying the incenter parametrization:
with `p = α+β+γ` and `num = aα+bβ+cγ` (side lengths and their weighted sum),
`((a(b+c)-bc)p² - num²)² = 4bc·p²·(num-ap)²`, proved by reduction modulo
`α²bc = -(b-c)²`, `β²ca = -(c-a)²`, `γ²ab = -(a-b)²` (certificates computed
by polynomial division). -/
lemma pi_sq_cert (a b c α β γ : ℂ)
    (hα : α ^ 2 * (b * c) = -(b - c) ^ 2)
    (hβ : β ^ 2 * (c * a) = -(c - a) ^ 2)
    (hγ : γ ^ 2 * (a * b) = -(a - b) ^ 2) :
    (a ^ 4 * b ^ 5 * c ^ 5) *
      (((a * (b + c) - b * c) * (α + β + γ) ^ 2 - (a * α + b * β + c * γ) ^ 2) ^ 2 -
        4 * b * c * (α + β + γ) ^ 2 * (a * α + b * β + c * γ - a * (α + β + γ)) ^ 2) = 0 := by
  linear_combination (a^8*α^2*b^4*c^4 - a^8*b^5*c^3 + 2*a^8*b^4*c^4 - a^8*b^3*c^5 - 2*a^7*α^2*b^5*c^4 - 2*a^7*α^2*b^4*c^5 - 4*a^7*α*b^5*c^4*γ - 4*a^7*α*b^4*β*c^5 + 2*a^7*b^6*c^3 - 2*a^7*b^5*β^2*c^4 - 4*a^7*b^5*β*c^4*γ - 2*a^7*b^5*c^4*γ^2 - 2*a^7*b^5*c^4 - 2*a^7*b^4*β^2*c^5 - 4*a^7*b^4*β*c^5*γ - 2*a^7*b^4*c^5*γ^2 - 2*a^7*b^4*c^5 + 2*a^7*b^3*c^6 + a^6*α^2*b^6*c^4 + 4*a^6*α^2*b^5*c^5 + a^6*α^2*b^4*c^6 + 4*a^6*α*b^6*c^4*γ + 8*a^6*α*b^5*β*c^5 + 8*a^6*α*b^5*c^5*γ + 4*a^6*α*b^4*β*c^6 - a^6*b^7*c^3 + 4*a^6*b^6*β^2*c^4 + 4*a^6*b^6*β*c^4*γ + 6*a^6*b^6*c^4*γ^2 - 2*a^6*b^6*c^4 + 2*a^6*b^5*β^2*c^5 + 16*a^6*b^5*β*c^5*γ + 2*a^6*b^5*c^5*γ^2 + 6*a^6*b^5*c^5 + 6*a^6*b^4*β^2*c^6 + 4*a^6*b^4*β*c^6*γ + 4*a^6*b^4*c^6*γ^2 - 2*a^6*b^4*c^6 - a^6*b^3*c^7 - 2*a^5*α^2*b^6*c^5 - 2*a^5*α^2*b^5*c^6 - 4*a^5*α*b^6*β*c^5 - 8*a^5*α*b^6*c^5*γ - 8*a^5*α*b^5*β*c^6 - 4*a^5*α*b^5*c^6*γ - 2*a^5*b^7*β^2*c^4 + 2*a^5*b^7*c^4 + 2*a^5*b^6*β^2*c^5 - 12*a^5*b^6*β*c^5*γ - 12*a^5*b^6*c^5*γ^2 - 2*a^5*b^6*c^5 - 12*a^5*b^5*β^2*c^6 - 12*a^5*b^5*β*c^6*γ + 2*a^5*b^5*c^6*γ^2 - 2*a^5*b^5*c^6 - 2*a^5*b^4*c^7*γ^2 + 2*a^5*b^4*c^7 + a^4*α^2*b^6*c^6 + 4*a^4*α*b^6*β*c^6 + 4*a^4*α*b^6*c^6*γ - 2*a^4*b^7*β^2*c^5 - a^4*b^7*c^5 + 6*a^4*b^6*β^2*c^6 + 8*a^4*b^6*β*c^6*γ + 6*a^4*b^6*c^6*γ^2 + 2*a^4*b^6*c^6 - 2*a^4*b^5*c^7*γ^2 - a^4*b^5*c^7) * hα + (a^6*b^7*c^3 - 3*a^6*b^5*c^5 + 2*a^6*b^4*c^6 + 4*a^5*α*b^7*c^4*γ - 4*a^5*α*b^6*β*c^5 - 12*a^5*α*b^6*c^5*γ + 4*a^5*α*b^5*β*c^6 + 8*a^5*α*b^5*c^6*γ - 2*a^5*b^8*c^3 + a^5*b^7*β^2*c^4 + 4*a^5*b^7*β*c^4*γ + 6*a^5*b^7*c^4*γ^2 + 4*a^5*b^7*c^4 - 2*a^5*b^6*β^2*c^5 - 8*a^5*b^6*β*c^5*γ - 12*a^5*b^6*c^5*γ^2 - 8*a^5*b^6*c^5 + a^5*b^5*β^2*c^6 + 4*a^5*b^5*β*c^6*γ + 6*a^5*b^5*c^6*γ^2 + 12*a^5*b^5*c^6 - 6*a^5*b^4*c^7 - 4*a^4*α*b^8*c^4*γ + 8*a^4*α*b^7*β*c^5 + 16*a^4*α*b^7*c^5*γ - 8*a^4*α*b^6*β*c^6 - 12*a^4*α*b^6*c^6*γ + a^4*b^9*c^3 - 2*a^4*b^8*β^2*c^4 - 4*a^4*b^8*β*c^4*γ - 2*a^4*b^8*c^4*γ^2 - 8*a^4*b^8*c^4 + 4*a^4*b^7*β^2*c^5 + 8*a^4*b^7*β*c^5*γ + 2*a^4*b^7*c^5*γ^2 + 24*a^4*b^7*c^5 - 2*a^4*b^6*β^2*c^6 - 4*a^4*b^6*β*c^6*γ + 2*a^4*b^6*c^6*γ^2 - 28*a^4*b^6*c^6 - 2*a^4*b^5*c^7*γ^2 + 11*a^4*b^5*c^7 - 4*a^3*α*b^8*β*c^5 - 4*a^3*α*b^8*c^5*γ + 4*a^3*α*b^7*β*c^6 + 4*a^3*α*b^7*c^6*γ + a^3*b^9*β^2*c^4 + 4*a^3*b^9*c^4 - 2*a^3*b^8*β^2*c^5 - 2*a^3*b^8*c^5*γ^2 - 12*a^3*b^8*c^5 + a^3*b^7*β^2*c^6 + 4*a^3*b^7*c^6*γ^2 + 12*a^3*b^7*c^6 - 2*a^3*b^6*c^7*γ^2 - 4*a^3*b^6*c^7 - a^2*b^9*c^5 + 2*a^2*b^8*c^6 - a^2*b^7*c^7) * hβ + (-4*a^6*b^6*c^4 + 9*a^6*b^5*c^5 - 6*a^6*b^4*c^6 + a^6*b^3*c^7 + 8*a^5*α*b^6*β*c^5 + 4*a^5*α*b^6*c^5*γ - 12*a^5*α*b^5*β*c^6 - 4*a^5*α*b^5*c^6*γ + 4*a^5*α*b^4*β*c^7 - 4*a^5*b^7*c^4 + 4*a^5*b^6*β*c^5*γ + a^5*b^6*c^5*γ^2 + 22*a^5*b^6*c^5 - 8*a^5*b^5*β*c^6*γ - 2*a^5*b^5*c^6*γ^2 - 34*a^5*b^5*c^6 + 4*a^5*b^4*β*c^7*γ + a^5*b^4*c^7*γ^2 + 18*a^5*b^4*c^7 - 2*a^5*b^3*c^8 - 12*a^4*α*b^6*β*c^6 - 8*a^4*α*b^6*c^6*γ + 16*a^4*α*b^5*β*c^7 + 8*a^4*α*b^5*c^7*γ - 4*a^4*α*b^4*β*c^8 + 9*a^4*b^7*c^5 - 4*a^4*b^6*β*c^6*γ - 2*a^4*b^6*c^6*γ^2 - 34*a^4*b^6*c^6 + 8*a^4*b^5*β*c^7*γ + 4*a^4*b^5*c^7*γ^2 + 42*a^4*b^5*c^7 - 4*a^4*b^4*β*c^8*γ - 2*a^4*b^4*c^8*γ^2 - 18*a^4*b^4*c^8 + a^4*b^3*c^9 + 4*a^3*α*b^6*β*c^7 + 4*a^3*α*b^6*c^7*γ - 4*a^3*α*b^5*β*c^8 - 4*a^3*α*b^5*c^8*γ - 6*a^3*b^7*c^6 + a^3*b^6*c^7*γ^2 + 18*a^3*b^6*c^7 - 2*a^3*b^5*c^8*γ^2 - 18*a^3*b^5*c^8 + a^3*b^4*c^9*γ^2 + 6*a^3*b^4*c^9 + a^2*b^7*c^7 - 2*a^2*b^6*c^8 + a^2*b^5*c^9) * hγ

/-- For points `b`, `c` on the unit circle, the squared side length as a complex number
satisfies `‖b-c‖²·(bc) = -(b-c)²`. -/
lemma side_len_sq {b c : ℂ} (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) :
    (‖b - c‖ : ℂ) ^ 2 * (b * c) = -(b - c) ^ 2 := by
  have hb0 : b ≠ 0 := by
    rw [← norm_ne_zero_iff, hb]; norm_num
  have hc0 : c ≠ 0 := by
    rw [← norm_ne_zero_iff, hc]; norm_num
  have e : (‖b - c‖ : ℂ) ^ 2 = conj (b - c) * (b - c) := by
    rw [show (‖b - c‖ : ℂ) ^ 2 = ((‖b - c‖ ^ 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  rw [e, map_sub, conj_of_norm_one hb, conj_of_norm_one hc]
  field_simp [hb0, hc0]
  ring

/-- The perimeter `p = α+β+γ` is a positive real, hence nonzero as a complex number. -/
lemma perimeter_ne_zero {a b c : ℂ} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    (‖b - c‖ : ℂ) + (‖c - a‖ : ℂ) + (‖a - b‖ : ℂ) ≠ 0 := by
  have hα : (0 : ℝ) < ‖b - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hbc)
  have hβ : (0 : ℝ) < ‖c - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hca)
  have hγ : (0 : ℝ) < ‖a - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
  have hre : ((‖b - c‖ : ℂ) + (‖c - a‖ : ℂ) + (‖a - b‖ : ℂ)).re =
      ‖b - c‖ + ‖c - a‖ + ‖a - b‖ := by
    simp [Complex.add_re, Complex.ofReal_re]
  intro h
  rw [h] at hre
  simp at hre
  linarith

/-- The incenter (given by the side-length formula) is not the vertex `A`:
otherwise `A`, `B`, `C` would be collinear. -/
lemma incenter_ne_vertex {a b c : ℂ}
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (hABC : cross (b - a) (c - a) ≠ 0)
    (i : ℂ) (hi : i = (a * (‖b - c‖ : ℂ) + b * (‖c - a‖ : ℂ) + c * (‖a - b‖ : ℂ)) /
      ((‖b - c‖ : ℂ) + (‖c - a‖ : ℂ) + (‖a - b‖ : ℂ))) :
    i ≠ a := by
  intro hia
  have hp0 := perimeter_ne_zero hab hbc hca
  have h1 : (‖c - a‖ : ℂ) * (b - a) + (‖a - b‖ : ℂ) * (c - a) = 0 := by
    have h2 : a * (‖b - c‖ : ℂ) + b * (‖c - a‖ : ℂ) + c * (‖a - b‖ : ℂ) -
        a * ((‖b - c‖ : ℂ) + (‖c - a‖ : ℂ) + (‖a - b‖ : ℂ)) = 0 := by
      have h3 : i - a = 0 := sub_eq_zero.mpr hia
      rw [hi] at h3
      field_simp at h3
      convert h3 using 1
      ring
    convert h2 using 1
    ring
  -- direction of `b - a` is opposite to direction of `c - a`, forcing collinearity
  have hβ : (‖c - a‖ : ℂ) ≠ 0 := by
    norm_cast
    exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr hca)
  have hγ : (‖a - b‖ : ℂ) ≠ 0 := by
    norm_cast
    exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr hab)
  have h4 : b - a = (-(‖a - b‖ / ‖c - a‖ : ℝ) : ℂ) * (c - a) := by
    have h5 : (b - a) * (‖c - a‖ : ℂ) = -(‖a - b‖ : ℂ) * (c - a) := by
      linear_combination h1
    have h7 : (b - a) * (‖c - a‖ : ℂ) =
        ((-(‖a - b‖ / ‖c - a‖ : ℝ) : ℂ) * (c - a)) * (‖c - a‖ : ℂ) := by
      have e : ((-(‖a - b‖ / ‖c - a‖ : ℝ) : ℂ)) * (‖c - a‖ : ℂ) = -(‖a - b‖ : ℂ) := by
        rw [show ((-(‖a - b‖ / ‖c - a‖ : ℝ) : ℂ)) = (-(‖a - b‖ : ℝ) : ℂ) / (‖c - a‖ : ℂ) by
          push_cast; ring]
        field_simp [hβ]
      have h8 : ((-(‖a - b‖ / ‖c - a‖ : ℝ) : ℂ) * (c - a)) * (‖c - a‖ : ℂ) =
          ((-(‖a - b‖ / ‖c - a‖ : ℝ) : ℂ)) * (‖c - a‖ : ℂ) * (c - a) := by ring
      rw [h8, e, h5]
    exact mul_right_cancel₀ hβ h7
  have h5 : cross (b - a) (c - a) = 0 := by
    rw [h4, neg_mul, cross_neg_left, ← Complex.real_smul, cross_smul_left, cross_self,
      mul_zero, neg_zero]
  exact hABC h5

/-- The conjugate of a unit-modulus complex number times itself is one (forward form). -/
lemma mul_conj_of_norm_one {w : ℂ} (hw : ‖w‖ = 1) : w * conj w = 1 := by
  rw [Complex.mul_conj]
  norm_cast
  rw [Complex.normSq_eq_norm_sq, hw]
  norm_num

/-- Key identity for the incenter: `p² - num·conj(num) = αβγ·p` where `α,β,γ` are the
side lengths, `p = α+β+γ` and `num = aα+bβ+cγ`. -/
lemma incenter_norm_sq {a b c : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) :
    ((‖b - c‖ : ℂ) + (‖c - a‖ : ℂ) + (‖a - b‖ : ℂ)) ^ 2 -
      (a * (‖b - c‖ : ℂ) + b * (‖c - a‖ : ℂ) + c * (‖a - b‖ : ℂ)) *
        conj (a * (‖b - c‖ : ℂ) + b * (‖c - a‖ : ℂ) + c * (‖a - b‖ : ℂ)) =
      (‖b - c‖ : ℂ) * (‖c - a‖ : ℂ) * (‖a - b‖ : ℂ) *
        ((‖b - c‖ : ℂ) + (‖c - a‖ : ℂ) + (‖a - b‖ : ℂ)) := by
  have h1 : a * conj a = 1 := mul_conj_of_norm_one ha
  have h2 : b * conj b = 1 := mul_conj_of_norm_one hb
  have h3 : c * conj c = 1 := mul_conj_of_norm_one hc
  have e2 : (2 - (a * conj b + b * conj a) : ℂ) = (‖a - b‖ : ℂ) ^ 2 := by
    have e : (‖a - b‖ : ℂ) ^ 2 = conj (a - b) * (a - b) := by
      rw [show (‖a - b‖ : ℂ) ^ 2 = ((‖a - b‖ ^ 2 : ℝ) : ℂ) by push_cast; ring,
        ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    rw [e, map_sub]
    linear_combination -h1 - h2
  have e3 : (2 - (b * conj c + c * conj b) : ℂ) = (‖b - c‖ : ℂ) ^ 2 := by
    have e : (‖b - c‖ : ℂ) ^ 2 = conj (b - c) * (b - c) := by
      rw [show (‖b - c‖ : ℂ) ^ 2 = ((‖b - c‖ ^ 2 : ℝ) : ℂ) by push_cast; ring,
        ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    rw [e, map_sub]
    linear_combination -h2 - h3
  have e4 : (2 - (a * conj c + c * conj a) : ℂ) = (‖c - a‖ : ℂ) ^ 2 := by
    have e : (‖c - a‖ : ℂ) ^ 2 = conj (c - a) * (c - a) := by
      rw [show (‖c - a‖ : ℂ) ^ 2 = ((‖c - a‖ ^ 2 : ℝ) : ℂ) by push_cast; ring,
        ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    rw [e, map_sub]
    linear_combination -h1 - h3
  have hconj : conj (a * (‖b - c‖ : ℂ) + b * (‖c - a‖ : ℂ) + c * (‖a - b‖ : ℂ)) =
      conj a * (‖b - c‖ : ℂ) + conj b * (‖c - a‖ : ℂ) + conj c * (‖a - b‖ : ℂ) := by
    simp [map_add, map_mul, Complex.conj_ofReal]
  rw [hconj]
  linear_combination (‖b - c‖ : ℂ) * (‖c - a‖ : ℂ) * e2 +
    (‖c - a‖ : ℂ) * (‖a - b‖ : ℂ) * e3 + (‖b - c‖ : ℂ) * (‖a - b‖ : ℂ) * e4 -
    (‖b - c‖ : ℂ) ^ 2 * h1 - (‖c - a‖ : ℂ) ^ 2 * h2 - (‖a - b‖ : ℂ) ^ 2 * h3

/-- The weighted vertex sum of the incenter has norm strictly less than the perimeter:
the incenter lies strictly inside the circumcircle. -/
lemma incenter_norm_lt {a b c : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    ‖a * (‖b - c‖ : ℂ) + b * (‖c - a‖ : ℂ) + c * (‖a - b‖ : ℂ)‖ <
      ‖b - c‖ + ‖c - a‖ + ‖a - b‖ := by
  have hα : (0 : ℝ) < ‖b - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hbc)
  have hβ : (0 : ℝ) < ‖c - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hca)
  have hγ : (0 : ℝ) < ‖a - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
  set num : ℂ := a * (‖b - c‖ : ℂ) + b * (‖c - a‖ : ℂ) + c * (‖a - b‖ : ℂ) with hnum
  set p : ℝ := ‖b - c‖ + ‖c - a‖ + ‖a - b‖ with hp
  have key := incenter_norm_sq ha hb hc
  rw [← hnum] at key
  have hpC : (p : ℂ) = ((‖b - c‖ : ℂ) + (‖c - a‖ : ℂ) + (‖a - b‖ : ℂ)) := by
    rw [hp]
    push_cast
    ring
  rw [← hpC] at key
  have hnn : num * conj num = ((‖num‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hnn] at key
  have hreal : p ^ 2 - ‖num‖ ^ 2 = ‖b - c‖ * ‖c - a‖ * ‖a - b‖ * p := by
    have h4 : (p : ℂ) ^ 2 - ((‖num‖ ^ 2 : ℝ) : ℂ) = ((p ^ 2 - ‖num‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    have h5 : (‖b - c‖ : ℂ) * (‖c - a‖ : ℂ) * (‖a - b‖ : ℂ) * (p : ℂ) =
        ((‖b - c‖ * ‖c - a‖ * ‖a - b‖ * p : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h4, h5] at key
    exact Complex.ofReal_inj.mp key
  have hppos : (0 : ℝ) < p := by
    rw [hp]
    linarith
  have hnn2 : (0 : ℝ) ≤ ‖num‖ := norm_nonneg num
  nlinarith [hreal, mul_pos (mul_pos (mul_pos hα hβ) hγ) hppos, hnn2, hppos]

/-- The quantity `π = (a(b+c) - bc - i²)/(2(i-a))` satisfies `π² = bc`
(the algebraic heart of the incenter parametrization). -/
lemma pi_sq_eq {a b c : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (i : ℂ) (hi : i = (a * (‖b - c‖ : ℂ) + b * (‖c - a‖ : ℂ) + c * (‖a - b‖ : ℂ)) /
      ((‖b - c‖ : ℂ) + (‖c - a‖ : ℂ) + (‖a - b‖ : ℂ)))
    (hia : i ≠ a) :
    ((a * (b + c) - b * c - i ^ 2) / (2 * (i - a))) ^ 2 = b * c := by
  have hα := side_len_sq hb hc
  have hβ := side_len_sq hc ha
  have hγ := side_len_sq ha hb
  have cert := pi_sq_cert a b c (‖b - c‖ : ℂ) (‖c - a‖ : ℂ) (‖a - b‖ : ℂ) hα hβ hγ
  have ha0 : a ≠ 0 := by
    rw [← norm_ne_zero_iff, ha]; norm_num
  have hb0 : b ≠ 0 := by
    rw [← norm_ne_zero_iff, hb]; norm_num
  have hc0 : c ≠ 0 := by
    rw [← norm_ne_zero_iff, hc]; norm_num
  have hD : a ^ 4 * b ^ 5 * c ^ 5 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero 4 ha0) (pow_ne_zero 5 hb0)) (pow_ne_zero 5 hc0)
  have hE := (mul_eq_zero_iff_left hD).mp cert
  have hp0 := perimeter_ne_zero hab hbc hca
  have e2 : i - a = (a * (‖b - c‖ : ℂ) + b * (‖c - a‖ : ℂ) + c * (‖a - b‖ : ℂ) -
      a * ((‖b - c‖ : ℂ) + (‖c - a‖ : ℂ) + (‖a - b‖ : ℂ))) /
      ((‖b - c‖ : ℂ) + (‖c - a‖ : ℂ) + (‖a - b‖ : ℂ)) := by
    rw [hi]; field_simp [hp0]
  have hY : a * (‖b - c‖ : ℂ) + b * (‖c - a‖ : ℂ) + c * (‖a - b‖ : ℂ) -
      a * ((‖b - c‖ : ℂ) + (‖c - a‖ : ℂ) + (‖a - b‖ : ℂ)) ≠ 0 := by
    intro h
    rw [h] at e2
    simp at e2
    exact hia (sub_eq_zero.mp e2)
  have e1 : a * (b + c) - b * c - i ^ 2 =
      ((a * (b + c) - b * c) * ((‖b - c‖ : ℂ) + (‖c - a‖ : ℂ) + (‖a - b‖ : ℂ)) ^ 2 -
        (a * (‖b - c‖ : ℂ) + b * (‖c - a‖ : ℂ) + c * (‖a - b‖ : ℂ)) ^ 2) /
        ((‖b - c‖ : ℂ) + (‖c - a‖ : ℂ) + (‖a - b‖ : ℂ)) ^ 2 := by
    rw [hi]; field_simp [hp0]
  rw [e1, e2]
  field_simp [hp0, hY]
  linear_combination hE

/-- The quantity `π` is not `-a` (equivalently the parametrizing square roots
can be chosen so that the arc midpoint is `-π ≠ a`). -/
lemma pi_ne_neg_a {a b c : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (hABC : cross (b - a) (c - a) ≠ 0)
    (i : ℂ) (hi : i = (a * (‖b - c‖ : ℂ) + b * (‖c - a‖ : ℂ) + c * (‖a - b‖ : ℂ)) /
      ((‖b - c‖ : ℂ) + (‖c - a‖ : ℂ) + (‖a - b‖ : ℂ)))
    (hia : i ≠ a) :
    (a * (b + c) - b * c - i ^ 2) / (2 * (i - a)) ≠ -a := by
  have hp0 := perimeter_ne_zero hab hbc hca
  have hβ0 : (‖c - a‖ : ℂ) ≠ 0 := by
    norm_cast
    exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr hca)
  have hγ0 : (‖a - b‖ : ℂ) ≠ 0 := by
    norm_cast
    exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr hab)
  intro hπ
  have h1 : (i - a) ^ 2 = -(a - b) * (a - c) := by
    field_simp [sub_ne_zero.mpr hia] at hπ
    linear_combination -hπ
  have hia2 : i - a = ((‖c - a‖ : ℂ) * (b - a) + (‖a - b‖ : ℂ) * (c - a)) /
      ((‖b - c‖ : ℂ) + (‖c - a‖ : ℂ) + (‖a - b‖ : ℂ)) := by
    rw [hi]; field_simp [hp0]; ring
  rw [hia2] at h1
  have hUV : (b - a) * (c - a) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hab.symm) (sub_ne_zero.mpr hca)
  have h2 : ((‖c - a‖ : ℂ) * (b - a) + (‖a - b‖ : ℂ) * (c - a)) ^ 2 / ((b - a) * (c - a)) =
      -(((‖b - c‖ : ℂ) + (‖c - a‖ : ℂ) + (‖a - b‖ : ℂ)) ^ 2) := by
    have h2' : ((‖c - a‖ : ℂ) * (b - a) + (‖a - b‖ : ℂ) * (c - a)) ^ 2 =
        -(((‖b - c‖ : ℂ) + (‖c - a‖ : ℂ) + (‖a - b‖ : ℂ)) ^ 2) * ((b - a) * (c - a)) := by
      field_simp [hp0] at h1
      linear_combination h1
    rw [h2']
    field_simp [hUV]
  have h3 : (‖c - a‖ : ℂ) ^ 2 * ((b - a) / (c - a)) + 2 * (‖c - a‖ : ℂ) * (‖a - b‖ : ℂ) +
      (‖a - b‖ : ℂ) ^ 2 * ((c - a) / (b - a)) =
      -(((‖b - c‖ : ℂ) + (‖c - a‖ : ℂ) + (‖a - b‖ : ℂ)) ^ 2) := by
    rw [← h2]
    field_simp [hUV]
    ring
  set u' := (b - a) / (‖a - b‖ : ℂ) with hu'
  set v' := (c - a) / (‖c - a‖ : ℂ) with hv'
  have hu1 : ‖u'‖ = 1 := by
    rw [hu', norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
      show b - a = -(a - b) by ring, norm_neg]
    exact div_self (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hab))
  have hv1 : ‖v'‖ = 1 := by
    rw [hv', norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    exact div_self (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hca))
  have hu0 : u' ≠ 0 := by
    rw [hu']
    exact div_ne_zero (sub_ne_zero.mpr hab.symm) hγ0
  have hv0 : v' ≠ 0 := by
    rw [hv']
    exact div_ne_zero (sub_ne_zero.mpr hca) hβ0
  have hU : (b - a) = (‖a - b‖ : ℂ) * u' := by
    rw [hu']; field_simp [hγ0]
  have hV : (c - a) = (‖c - a‖ : ℂ) * v' := by
    rw [hv']; field_simp [hβ0]
  have hsub1 : ((b - a) / (c - a)) = ((‖a - b‖ : ℂ) * u') / ((‖c - a‖ : ℂ) * v') := by
    conv_lhs => rw [hU, hV]
  have hsub2 : ((c - a) / (b - a)) = ((‖c - a‖ : ℂ) * v') / ((‖a - b‖ : ℂ) * u') := by
    conv_lhs => rw [hU, hV]
  rw [hsub1, hsub2] at h3
  have h4 : (‖c - a‖ : ℂ) ^ 2 * (((‖a - b‖ : ℂ) * u') / ((‖c - a‖ : ℂ) * v')) +
      2 * (‖c - a‖ : ℂ) * (‖a - b‖ : ℂ) +
      (‖a - b‖ : ℂ) ^ 2 * (((‖c - a‖ : ℂ) * v') / ((‖a - b‖ : ℂ) * u')) =
      (‖c - a‖ : ℂ) * (‖a - b‖ : ℂ) * (u' / v' + v' / u') + 2 * (‖c - a‖ : ℂ) * (‖a - b‖ : ℂ) := by
    field_simp [hβ0, hγ0, hu0, hv0]
    ring
  rw [h4] at h3
  have hcj : conj (u' / v') = v' / u' := by
    rw [map_div₀, conj_of_norm_one hu1, conj_of_norm_one hv1]
    field_simp [hu0, hv0]
  have hre : (u' / v' + v' / u' : ℂ) = 2 * (((u' / v').re : ℝ) : ℂ) := by
    rw [← hcj, Complex.add_conj]
    push_cast
    ring
  rw [hre] at h3
  have h5 : (2 * ‖c - a‖ * ‖a - b‖ * (u' / v').re + 2 * ‖c - a‖ * ‖a - b‖ : ℝ) =
      -((‖b - c‖ + ‖c - a‖ + ‖a - b‖) ^ 2) := by
    have h4 : ((2 * ‖c - a‖ * ‖a - b‖ * (u' / v').re + 2 * ‖c - a‖ * ‖a - b‖ : ℝ) : ℂ) =
        -(((‖b - c‖ : ℂ) + (‖c - a‖ : ℂ) + (‖a - b‖ : ℂ)) ^ 2) := by
      push_cast
      linear_combination h3
    have h5' : ((-((‖b - c‖ + ‖c - a‖ + ‖a - b‖) ^ 2) : ℝ) : ℂ) =
        -(((‖b - c‖ : ℂ) + (‖c - a‖ : ℂ) + (‖a - b‖ : ℂ)) ^ 2) := by
      push_cast
      ring
    have h6 : ((2 * ‖c - a‖ * ‖a - b‖ * (u' / v').re + 2 * ‖c - a‖ * ‖a - b‖ : ℝ) : ℂ) =
        ((-((‖b - c‖ + ‖c - a‖ + ‖a - b‖) ^ 2) : ℝ) : ℂ) := by
      rw [h4, h5']
    exact Complex.ofReal_inj.mp h6
  have h7 : (-1 : ℝ) ≤ (u' / v').re := by
    have h8 : |(u' / v').re| ≤ ‖u' / v'‖ := Complex.abs_re_le_norm (u' / v')
    rw [show ‖u' / v'‖ = 1 by
      rw [norm_div, hu1, hv1]
      norm_num] at h8
    exact (abs_le.mp h8).1
  have hβγ : (0 : ℝ) < ‖c - a‖ * ‖a - b‖ :=
    mul_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hca)) (norm_pos_iff.mpr (sub_ne_zero.mpr hab))
  have hαpos : (0 : ℝ) < ‖b - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hbc)
  have hβpos : (0 : ℝ) < ‖c - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hca)
  have hγpos : (0 : ℝ) < ‖a - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
  nlinarith [h5, h7, hβγ, hαpos, hβpos, hγpos, sq_nonneg (‖b - c‖ + ‖c - a‖ + ‖a - b‖)]

/-- The incenter parametrization: there exist square roots `X, Y, Z` of `a, b, c`
such that the incenter is `-(XY+YZ+ZX)` and `YZ ≠ -a` (so `-YZ` is the midpoint
of the arc `BC` not containing `A`). -/
lemma incenter_param {a b c : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (i : ℂ) (hi : i = (a * (‖b - c‖ : ℂ) + b * (‖c - a‖ : ℂ) + c * (‖a - b‖ : ℂ)) /
      ((‖b - c‖ : ℂ) + (‖c - a‖ : ℂ) + (‖a - b‖ : ℂ)))
    (hia : i ≠ a)
    (hpi2 : ((a * (b + c) - b * c - i ^ 2) / (2 * (i - a))) ^ 2 = b * c)
    (hpine : (a * (b + c) - b * c - i ^ 2) / (2 * (i - a)) ≠ -a) :
    ∃ X Y Z : ℂ, X ^ 2 = a ∧ Y ^ 2 = b ∧ Z ^ 2 = c ∧
      i = -(X * Y + Y * Z + Z * X) ∧ Y * Z ≠ -a := by
  have ha0 : a ≠ 0 := by
    rw [← norm_ne_zero_iff, ha]; norm_num
  generalize hπd : (a * (b + c) - b * c - i ^ 2) / (2 * (i - a)) = π
  have hpi2' : π ^ 2 = b * c := by
    rw [← hπd]; exact hpi2
  have hpine' : π ≠ -a := by
    rw [← hπd]; exact hpine
  have h2pi : 2 * π * (i - a) = a * (b + c) - b * c - i ^ 2 := by
    rw [← hπd]
    have hf : (-(a * 2) + i * 2) ≠ 0 := by
      convert mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) (sub_ne_zero.mpr hia) using 1
      ring
    field_simp [sub_ne_zero.mpr hia, hf]
  obtain ⟨σ, hσ2m⟩ := Complex.isSquare (b + c + 2 * π)
  have hσ2 : σ ^ 2 = b + c + 2 * π := by
    rw [pow_two]; exact hσ2m.symm
  have hσ : σ ≠ 0 := by
    intro h
    rw [h] at hσ2
    simp at hσ2
    have h1 : 2 * π = -(b + c) := by
      linear_combination -hσ2
    have h3' : (2 * π) ^ 2 = 4 * (b * c) := by
      linear_combination 4 * hpi2'
    rw [h1] at h3'
    have h2 : (b - c) ^ 2 = 0 := by
      linear_combination h3'
    have h4 : b = c := sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h2)
    exact hbc h4
  obtain ⟨δ, hδ2m⟩ := Complex.isSquare (σ ^ 2 - 4 * π)
  have hδ2 : δ ^ 2 = σ ^ 2 - 4 * π := by
    rw [pow_two]; exact hδ2m.symm
  set Y := (σ + δ) / 2 with hYd
  set Z := (σ - δ) / 2 with hZd
  have hYsZ : Y + Z = σ := by
    rw [hYd, hZd]; ring
  have h4YZ : 4 * (Y * Z) = 4 * π := by
    rw [hYd, hZd]
    linear_combination -hδ2
  have hYZ : Y * Z = π := mul_left_cancel₀ (by norm_num) h4YZ
  have hY2Z2 : Y ^ 2 + Z ^ 2 = b + c := by
    have e : Y ^ 2 + Z ^ 2 = (Y + Z) ^ 2 - 2 * (Y * Z) := by ring
    rw [e, hYsZ, hYZ, hσ2]
    ring
  have hY2Z2prod : Y ^ 2 * Z ^ 2 = b * c := by
    rw [show Y ^ 2 * Z ^ 2 = (Y * Z) ^ 2 from by ring, hYZ, hpi2']
  have hroots : (Y ^ 2 - b) * (Y ^ 2 - c) = 0 := by
    linear_combination Y ^ 2 * hY2Z2 - hY2Z2prod
  have hX2 : (-(i + π) / σ) ^ 2 = a := by
    rw [div_pow]
    rw [div_eq_iff (pow_ne_zero 2 hσ)]
    linear_combination h2pi + hpi2' - a * hσ2
  rcases mul_eq_zero.mp hroots with hcase | hcase
  · have hZ2 : Z ^ 2 = c := by
      linear_combination hY2Z2 - hcase
    refine ⟨-(i + π) / σ, Y, Z, hX2, sub_eq_zero.mp hcase, hZ2, ?_, ?_⟩
    · have e1 : (-(i + π) / σ) * (Y + Z) = -(i + π) := by
        rw [hYsZ]; field_simp [hσ]
      have e2 : (-(i + π) / σ) * Y + Y * Z + Z * (-(i + π) / σ) =
          (-(i + π) / σ) * (Y + Z) + Y * Z := by ring
      rw [e2, e1, hYZ]
      ring
    · rw [hYZ]
      exact hpine'
  · have hZ2 : Z ^ 2 = b := by
      linear_combination hY2Z2 - hcase
    refine ⟨-(i + π) / σ, Z, Y, hX2, hZ2, sub_eq_zero.mp hcase, ?_, ?_⟩
    · have e1 : (-(i + π) / σ) * (Z + Y) = -(i + π) := by
        rw [show Z + Y = Y + Z from by ring, hYsZ]; field_simp [hσ]
      have e2 : (-(i + π) / σ) * Z + Z * Y + Y * (-(i + π) / σ) =
          (-(i + π) / σ) * (Z + Y) + Z * Y := by ring
      rw [e2, e1, show Z * Y = Y * Z from by ring, hYZ]
      ring
    · rw [show Z * Y = Y * Z from by ring, hYZ]
      exact hpine'

/-- Real part of `x · conj y` equals that of `conj y · x`. -/
lemma re_mul_conj_eq (x y : ℂ) : (x * conj y).re = (conj y * x).re := by
  have e1 : conj (x * conj y) = conj (conj y * x) := by
    simp [mul_comm]
  rw [← Complex.conj_re (x * conj y), e1, Complex.conj_re]

/-- The final computation of the bridge: from the line equation for `ρ` (the isogonal
case), derive the formula for `F`. -/
lemma f_formula_tail {a b c e ρ f : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (he : ‖e‖ = 1)
    (hab : a ≠ b) (hac : a ≠ c) (hae : a ≠ e)
    (hρre : conj ρ = ρ)
    (hfa2 : f = a + ρ * ((b - a) * (c - a) * conj (e - a)))
    (hw : (b - a) * (c - a) * conj (e - a) +
        b * c * conj ((b - a) * (c - a) * conj (e - a)) =
        (a - b) * (a - c) * (a - e) ^ 2 / (a ^ 2 * e))
    (hbc_a : b + c - a - b * c * conj a = -(a - b) * (a - c) / a)
    (hline2 : ρ * ((b - a) * (c - a) * conj (e - a) +
        b * c * conj ((b - a) * (c - a) * conj (e - a))) = b + c - a - b * c * conj a) :
    f = (a * (b + c - e) - b * c) / (a - e) := by
  have ha0 : a ≠ 0 := by
    rw [← norm_ne_zero_iff, ha]; norm_num
  have he0 : e ≠ 0 := by
    rw [← norm_ne_zero_iff, he]; norm_num
  rw [hw, hbc_a] at hline2
  have hne1 : (a - b) * (a - c) * (a - e) ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hab) (sub_ne_zero.mpr hac))
      (pow_ne_zero 2 (sub_ne_zero.mpr hae))
  have hne2 : (a ^ 2 * e) ≠ 0 := mul_ne_zero (pow_ne_zero 2 ha0) he0
  have hne3 : (a - e) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hae)
  have e1 : (-(a - b) * (a - c) / a) / ((a - b) * (a - c) * (a - e) ^ 2 / (a ^ 2 * e)) =
      -(a * e) / (a - e) ^ 2 := by
    rw [div_div, ← mul_div_assoc, div_div_eq_mul_div,
      div_eq_div_iff (mul_ne_zero ha0 hne1) hne3]
    field_simp [ha0]
  have hρ2a : ρ = (-(a - b) * (a - c) / a) / ((a - b) * (a - c) * (a - e) ^ 2 / (a ^ 2 * e)) :=
    eq_div_of_mul_eq (div_ne_zero hne1 hne2) hline2
  have hρ2 : ρ = -(a * e) / (a - e) ^ 2 := by
    rw [hρ2a, e1]
  rw [hfa2, hρ2, map_sub, conj_of_norm_one he, conj_of_norm_one ha]
  rw [show a + (-(a * e) / (a - e) ^ 2) * ((b - a) * (c - a) * (e⁻¹ - a⁻¹)) =
      (a * (a - e) ^ 2 - a * e * ((b - a) * (c - a) * (e⁻¹ - a⁻¹))) / (a - e) ^ 2 from by
    rw [div_mul_eq_mul_div, add_div_eq_mul_add_div _ _ hne3]
    ring]
  rw [div_eq_div_iff hne3 (sub_ne_zero.mpr hae)]
  field_simp [ha0, he0]
  ring
/-- The bridge from the angle condition to the explicit formula for `F`.
Here `E` is given via the crossing point `P` of the chord `AE` with the line `BC`
(which lies strictly inside the segment `BC`), and `F` lies on the segment `BC`
with `∠BAF = ∠CAE`. Then `F = (a(b+c-e) - bc)/(a-e)`. -/
lemma f_formula {a b c e f : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (he : ‖e‖ = 1)
    (hab : a ≠ b) (hac : a ≠ c) (hae : a ≠ e)
    (hσ : cross (b - a) (c - a) ≠ 0)
    (hf_seg : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ f = ((1 - t : ℝ) : ℂ) * b + (t : ℂ) * c)
    (hfa : f ≠ a)
    (hcross : ∃ p : ℂ, (∃ s : ℝ, 0 < s ∧ s < 1 ∧ p = ((1 - s : ℝ) : ℂ) * a + (s : ℂ) * e) ∧
      (∃ u : ℝ, p = ((1 - u : ℝ) : ℂ) * b + (u : ℂ) * c))
    (hangle : ∠ b a f = ∠ c a e) :
    f = (a * (b + c - e) - b * c) / (a - e) := by
  -- unpack the crossing point
  obtain ⟨p, ⟨s, hs0, hs1, hps⟩, u, hpu⟩ := hcross
  have hps' : p = ((1 : ℂ) - (s : ℂ)) * a + (s : ℂ) * e := by
    rw [hps]; push_cast; ring
  have hpu' : p = ((1 : ℂ) - (u : ℂ)) * b + (u : ℂ) * c := by
    rw [hpu]; push_cast; ring
  have h1 : a * conj a = 1 := mul_conj_of_norm_one ha
  have h2 : b * conj b = 1 := mul_conj_of_norm_one hb
  have h3 : c * conj c = 1 := mul_conj_of_norm_one hc
  have h4 : e * conj e = 1 := mul_conj_of_norm_one he
  -- `|p|² = 1 - s(1-s)|a-e|²`, hence `|p| < 1`
  have hp2 : ‖p‖ ^ 2 = 1 - s * (1 - s) * ‖a - e‖ ^ 2 := by
    have key : conj p * p = 1 - (s : ℂ) * (1 - (s : ℂ)) * (‖a - e‖ : ℂ) ^ 2 := by
      rw [hps']
      have e2 : (‖a - e‖ : ℂ) ^ 2 = (2 - (a * conj e + e * conj a) : ℂ) := by
        have e : (‖a - e‖ : ℂ) ^ 2 = conj (a - e) * (a - e) := by
          rw [show (‖a - e‖ : ℂ) ^ 2 = ((‖a - e‖ ^ 2 : ℝ) : ℂ) by push_cast; ring,
            ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
        rw [e, map_sub]
        linear_combination h1 + h4
      simp only [map_add, map_mul, map_sub, map_one, Complex.conj_ofReal]
      linear_combination (1 - s : ℂ) ^ 2 * h1 + (s : ℂ) ^ 2 * h4 +
        (s : ℂ) * (1 - s : ℂ) * e2
    have h5 : ((‖p‖ ^ 2 : ℝ) : ℂ) = ((1 - s * (1 - s) * ‖a - e‖ ^ 2 : ℝ) : ℂ) := by
      have e : ((‖p‖ ^ 2 : ℝ) : ℂ) = conj p * p := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
      rw [e, key]
      push_cast
      ring
    exact_mod_cast h5
  have hplt : ‖p‖ < 1 := by
    have hae' : (0 : ℝ) < ‖a - e‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hae)
    have h7 : (0 : ℝ) < 1 - s := by linarith
    have h6 : (0 : ℝ) < s * (1 - s) * ‖a - e‖ ^ 2 :=
      mul_pos (mul_pos hs0 h7) (sq_pos_of_pos hae')
    have h8 : ‖p‖ ^ 2 < 1 := by linarith [hp2, h6]
    nlinarith [h8, norm_nonneg p]
  -- `p` on line `bc` with `|p|<1` forces `0 < u < 1`
  have hu01 : (0 : ℝ) < u ∧ u < 1 := by
    have hp2b : ‖p‖ ^ 2 = 1 - u * (1 - u) * ‖b - c‖ ^ 2 := by
      have key : conj p * p = 1 - (u : ℂ) * (1 - (u : ℂ)) * (‖b - c‖ : ℂ) ^ 2 := by
        rw [hpu']
        have e2 : (‖b - c‖ : ℂ) ^ 2 = (2 - (b * conj c + c * conj b) : ℂ) := by
          have e : (‖b - c‖ : ℂ) ^ 2 = conj (b - c) * (b - c) := by
            rw [show (‖b - c‖ : ℂ) ^ 2 = ((‖b - c‖ ^ 2 : ℝ) : ℂ) by push_cast; ring,
              ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
          rw [e, map_sub]
          linear_combination h2 + h3
        simp only [map_add, map_mul, map_sub, map_one, Complex.conj_ofReal]
        linear_combination (1 - u : ℂ) ^ 2 * h2 + (u : ℂ) ^ 2 * h3 +
          (u : ℂ) * (1 - u : ℂ) * e2
      have h5 : ((‖p‖ ^ 2 : ℝ) : ℂ) = ((1 - u * (1 - u) * ‖b - c‖ ^ 2 : ℝ) : ℂ) := by
        have e : ((‖p‖ ^ 2 : ℝ) : ℂ) = conj p * p := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
        rw [e, key]
        push_cast
        ring
      exact_mod_cast h5
    have hbc' : (0 : ℝ) < ‖b - c‖ := by
      have hbc : b ≠ c := by
        intro h
        rw [h] at hσ
        exact hσ (cross_self _)
      exact norm_pos_iff.mpr (sub_ne_zero.mpr hbc)
    have := hplt
    have h6 : (0 : ℝ) < u * (1 - u) * ‖b - c‖ ^ 2 := by
      nlinarith [this, hp2b, hbc', norm_nonneg p]
    have h7 : (0 : ℝ) < u * (1 - u) := by
      nlinarith [h6, hbc', sq_pos_of_pos hbc']
    constructor <;> nlinarith [h7]
  -- cosine equality
  obtain ⟨t, ht0, ht1, hf⟩ := hf_seg
  have hu1ne : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hv1ne : f - a ≠ 0 := sub_ne_zero.mpr hfa
  have hu2ne : c - a ≠ 0 := sub_ne_zero.mpr hac.symm
  have hv2ne : e - a ≠ 0 := sub_ne_zero.mpr hae.symm
  have hN1 : ‖b - a‖ * ‖f - a‖ ≠ 0 := mul_ne_zero (norm_ne_zero_iff.mpr hu1ne) (norm_ne_zero_iff.mpr hv1ne)
  have hN2 : ‖c - a‖ * ‖e - a‖ ≠ 0 := mul_ne_zero (norm_ne_zero_iff.mpr hu2ne) (norm_ne_zero_iff.mpr hv2ne)
  have hcos : Real.cos (∠ b a f) = Real.cos (∠ c a e) := congrArg Real.cos hangle
  simp only [EuclideanGeometry.angle, vsub_eq_sub, InnerProductGeometry.cos_angle] at hcos
  have hcos2 : ((f - a) * conj (b - a)).re * (‖c - a‖ * ‖e - a‖) =
      ((e - a) * conj (c - a)).re * (‖b - a‖ * ‖f - a‖) := by
    have h8 : inner ℝ (b - a) (f - a) * (‖c - a‖ * ‖e - a‖) =
        inner ℝ (c - a) (e - a) * (‖b - a‖ * ‖f - a‖) := by
      field_simp [hN1, hN2] at hcos
      convert hcos using 1 <;> ring
    rw [Complex.inner, Complex.inner] at h8
    exact h8
  -- set up the two ratios
  set z₁ := conj (b - a) * (f - a) with hz₁
  set z₂ := conj (c - a) * (e - a) with hz₂
  have hN1' : ‖z₁‖ = ‖b - a‖ * ‖f - a‖ := by
    rw [hz₁, norm_mul, Complex.norm_conj]
  have hN2' : ‖z₂‖ = ‖c - a‖ * ‖e - a‖ := by
    rw [hz₂, norm_mul, Complex.norm_conj]
  have hre : z₁.re * (‖c - a‖ * ‖e - a‖) = z₂.re * (‖b - a‖ * ‖f - a‖) := by
    have h9 := hcos2
    rw [re_mul_conj_eq (f - a) (b - a), re_mul_conj_eq (e - a) (c - a)] at h9
    rw [← hz₁, ← hz₂] at h9
    exact h9
  have him2 : (z₁.im * (‖c - a‖ * ‖e - a‖)) ^ 2 = (z₂.im * (‖b - a‖ * ‖f - a‖)) ^ 2 := by
    have e1 : z₁.im ^ 2 = (‖b - a‖ * ‖f - a‖) ^ 2 - z₁.re ^ 2 := by
      have e : normSq z₁ = (‖b - a‖ * ‖f - a‖) ^ 2 := by
        rw [Complex.normSq_eq_norm_sq, hN1']
      rw [Complex.normSq_apply] at e
      linarith
    have e2 : z₂.im ^ 2 = (‖c - a‖ * ‖e - a‖) ^ 2 - z₂.re ^ 2 := by
      have e : normSq z₂ = (‖c - a‖ * ‖e - a‖) ^ 2 := by
        rw [Complex.normSq_eq_norm_sq, hN2']
      rw [Complex.normSq_apply] at e
      linarith
    have hre2 : (z₁.re * (‖c - a‖ * ‖e - a‖)) ^ 2 = (z₂.re * (‖b - a‖ * ‖f - a‖)) ^ 2 := by
      rw [hre]
    nlinarith [e1, e2, hre2]
  have ha0 : a ≠ 0 := by
    rw [← norm_ne_zero_iff, ha]; norm_num
  have hb0 : b ≠ 0 := by
    rw [← norm_ne_zero_iff, hb]; norm_num
  have hc0 : c ≠ 0 := by
    rw [← norm_ne_zero_iff, hc]; norm_num
  have he0 : e ≠ 0 := by
    rw [← norm_ne_zero_iff, he]; norm_num
  have hN1c : ((‖b - a‖ * ‖f - a‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hN1
  have hN2c : ((‖c - a‖ * ‖e - a‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hN2
  have hu1sq0 : ((‖b - a‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    norm_cast
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hu1ne)
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp him2 with him | him
  · -- case A: the two angles have the same orientation — impossible by the arc position of `E`
    exfalso
    have hz : z₁ * ((‖c - a‖ * ‖e - a‖ : ℝ) : ℂ) = z₂ * ((‖b - a‖ * ‖f - a‖ : ℝ) : ℂ) := by
      apply Complex.ext_iff.mpr
      refine ⟨?_, ?_⟩
      · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        exact hre
      · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
        exact him
    have e1 : (b - a) * (z₁ * ((‖c - a‖ * ‖e - a‖ : ℝ) : ℂ)) =
        (b - a) * (z₂ * ((‖b - a‖ * ‖f - a‖ : ℝ) : ℂ)) := by rw [hz]
    rw [hz₁, hz₂] at e1
    have e2 : ((‖b - a‖ ^ 2 : ℝ) : ℂ) * (f - a) * ((‖c - a‖ * ‖e - a‖ : ℝ) : ℂ) =
        (b - a) * conj (c - a) * (e - a) * ((‖b - a‖ * ‖f - a‖ : ℝ) : ℂ) := by
      have e3 : (b - a) * conj (b - a) = ((‖b - a‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      linear_combination e1 - e3 * ((f - a) * ((‖c - a‖ * ‖e - a‖ : ℝ) : ℂ))
    have hv1 : f - a = (b - a) * conj (c - a) * (e - a) *
        (((‖b - a‖ * ‖f - a‖ : ℝ) : ℂ) / (((‖c - a‖ * ‖e - a‖ : ℝ) : ℂ) * ((‖b - a‖ ^ 2 : ℝ) : ℂ))) := by
      field_simp [hN2c, hu1sq0]
      linear_combination e2
    set ρ : ℝ := (‖b - a‖ * ‖f - a‖) / ((‖c - a‖ * ‖e - a‖) * ‖b - a‖ ^ 2) with hρd
    have hρpos : (0 : ℝ) < ρ := by
      rw [hρd]
      apply div_pos (mul_pos (norm_pos_iff.mpr hu1ne) (norm_pos_iff.mpr hv1ne))
      exact mul_pos (mul_pos (norm_pos_iff.mpr hu2ne) (norm_pos_iff.mpr hv2ne))
        (pow_pos (norm_pos_iff.mpr hu1ne) 2)
    have hcr1 : cross (b - a) (f - a) = t * cross (b - a) (c - a) := by
      rw [hf]
      have e1 : ((1 - t : ℝ) : ℂ) * b + (t : ℂ) * c - a =
          ((1 - t : ℝ) : ℂ) * (b - a) + (t : ℂ) * (c - a) := by
        push_cast
        ring
      rw [e1]
      simp only [cross_add_right, ← Complex.real_smul, cross_smul_right, cross_self,
        mul_zero, zero_add]
    have hcr2 : cross (b - a) (f - a) = ρ * ‖b - a‖ ^ 2 * cross (c - a) (e - a) := by
      have hv1' : f - a = (b - a) * conj (c - a) * (e - a) * ((ρ : ℝ) : ℂ) := by
        have hD' : (((‖c - a‖ * ‖e - a‖ : ℝ) : ℂ) * ((‖b - a‖ ^ 2 : ℝ) : ℂ)) =
            ((‖c - a‖ * ‖e - a‖ * ‖b - a‖ ^ 2 : ℝ) : ℂ) := by
          push_cast
          ring
        have hgoal : ((b - a) * conj (c - a) * (e - a)) *
            (((‖b - a‖ * ‖f - a‖ : ℝ) : ℂ) /
              (((‖c - a‖ * ‖e - a‖ : ℝ) : ℂ) * ((‖b - a‖ ^ 2 : ℝ) : ℂ))) =
            ((b - a) * conj (c - a) * (e - a)) * ((ρ : ℝ) : ℂ) := by
          rw [hρd, Complex.ofReal_div, hD']
        have hw0 : (b - a) * conj (c - a) * (e - a) ≠ 0 := by
          have h0 : star (c - a) ≠ 0 := by
            rw [star_ne_zero]
            exact sub_ne_zero.mpr hac.symm
          have hconj0 : conj (c - a) ≠ 0 := h0
          exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hab.symm) hconj0)
            (sub_ne_zero.mpr hae.symm)
        rw [hv1]
        exact hgoal
      have e1 : conj (b - a) * ((b - a) * conj (c - a) * (e - a) * ((ρ : ℝ) : ℂ)) =
          ((‖b - a‖ ^ 2 : ℝ) : ℂ) * ((ρ : ℝ) : ℂ) * (conj (c - a) * (e - a)) := by
        have e3 : conj (b - a) * (b - a) = ((‖b - a‖ ^ 2 : ℝ) : ℂ) := by
          rw [← Complex.normSq_eq_conj_mul_self]
          norm_cast
          rw [Complex.normSq_eq_norm_sq]
        have e4 : conj (b - a) * ((b - a) * conj (c - a) * (e - a) * ((ρ : ℝ) : ℂ)) =
            (conj (b - a) * (b - a)) * ((conj (c - a) * (e - a)) * ((ρ : ℝ) : ℂ)) := by ring
        rw [e4, e3]
        ring
      rw [hv1', cross, e1]
      simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, zero_add, sub_zero]
      rw [show ρ * ‖b - a‖ ^ 2 * cross (c - a) (e - a) =
          ρ * ‖b - a‖ ^ 2 * (conj (c - a) * (e - a)).im from by rw [cross]]
      simp only [Complex.mul_im]
      ring
    have hcr3 : cross (c - a) (e - a) = -(((1 - u) / s : ℝ)) * cross (b - a) (c - a) := by
      have e1 : conj (c - a) * (p - a) = (s : ℂ) * z₂ := by
        rw [hps']
        have e2 : ((1 : ℂ) - (s : ℂ)) * a + (s : ℂ) * e - a = (s : ℂ) * (e - a) := by ring
        rw [e2, hz₂]
        ring
      have e2 : conj (c - a) * (p - a) = ((1 - u : ℝ) : ℂ) * (conj (c - a) * (b - a)) +
          (u : ℂ) * ((‖c - a‖ ^ 2 : ℝ) : ℂ) := by
        rw [hpu']
        have e3 : ((1 : ℂ) - (u : ℂ)) * b + (u : ℂ) * c - a =
            ((1 - u : ℝ) : ℂ) * (b - a) + (u : ℂ) * (c - a) := by
          push_cast
          ring
        rw [e3]
        have e4 : conj (c - a) * ((u : ℂ) * (c - a)) = (u : ℂ) * ((‖c - a‖ ^ 2 : ℝ) : ℂ) := by
          rw [show conj (c - a) * ((u : ℂ) * (c - a)) = (u : ℂ) * (conj (c - a) * (c - a)) from by
            ring, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
        linear_combination e4
      have e5 : (s : ℂ) * z₂ = ((1 - u : ℝ) : ℂ) * (conj (c - a) * (b - a)) +
          (u : ℂ) * ((‖c - a‖ ^ 2 : ℝ) : ℂ) := by
        rw [← e1, ← e2]
      have e6 : s * z₂.im = (1 - u) * (conj (c - a) * (b - a)).im := by
        have e7 := congrArg Complex.im e5
        rw [show ((s : ℂ) * z₂).im = s * z₂.im from by
          simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]] at e7
        rw [show (((1 - u : ℝ) : ℂ) * (conj (c - a) * (b - a)) + (u : ℂ) * ((‖c - a‖ ^ 2 : ℝ) : ℂ)).im =
            (1 - u) * (conj (c - a) * (b - a)).im from by
          simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
            mul_zero, zero_mul, add_zero, zero_add]] at e7
        exact e7
      have e8 : (conj (c - a) * (b - a)).im = -cross (b - a) (c - a) := by
        rw [cross]
        have e9 : conj (c - a) * (b - a) = conj (conj (b - a) * (c - a)) := by
          simp [mul_comm]
        rw [e9, Complex.conj_im]
      have e9 : z₂.im = cross (c - a) (e - a) := by
        rw [hz₂, cross]
      rw [e9, e8] at e6
      field_simp [hs0.ne'] at e6 ⊢
      linear_combination e6
    have hcr4 : t = -(ρ * ‖b - a‖ ^ 2 * ((1 - u) / s : ℝ)) := by
      have e1 : t * cross (b - a) (c - a) = ρ * ‖b - a‖ ^ 2 * cross (c - a) (e - a) := by
        rw [← hcr1, hcr2]
      rw [hcr3] at e1
      have e2 : t * cross (b - a) (c - a) =
          -(ρ * ‖b - a‖ ^ 2 * ((1 - u) / s : ℝ)) * cross (b - a) (c - a) := by
        linear_combination e1
      exact mul_right_cancel₀ hσ e2
    have hpos : (0 : ℝ) < ρ * ‖b - a‖ ^ 2 * ((1 - u) / s : ℝ) := by
      apply mul_pos (mul_pos hρpos (pow_pos (norm_pos_iff.mpr hu1ne) 2))
      exact div_pos (by linarith [hu01.2]) hs0
    linarith [hcr4, hpos, ht0]
  · -- case B: the isogonal case — the claimed formula holds
    have hz : z₁ * ((‖c - a‖ * ‖e - a‖ : ℝ) : ℂ) = conj z₂ * ((‖b - a‖ * ‖f - a‖ : ℝ) : ℂ) := by
      set_option maxHeartbeats 2000000 in
      apply Complex.ext_iff.mpr
      refine ⟨?_, ?_⟩
      · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
          Complex.conj_re]
        exact hre
      · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add,
          Complex.conj_im]
        linarith [him]
    have hcz2 : conj z₂ = (c - a) * conj (e - a) := by
      rw [hz₂]
      simp [mul_comm]
    have e1 : (b - a) * (z₁ * ((‖c - a‖ * ‖e - a‖ : ℝ) : ℂ)) =
        (b - a) * (conj z₂ * ((‖b - a‖ * ‖f - a‖ : ℝ) : ℂ)) := by rw [hz]
    rw [hz₁, hcz2] at e1
    have e2 : ((‖b - a‖ ^ 2 : ℝ) : ℂ) * (f - a) * ((‖c - a‖ * ‖e - a‖ : ℝ) : ℂ) =
        (b - a) * (c - a) * conj (e - a) * ((‖b - a‖ * ‖f - a‖ : ℝ) : ℂ) := by
      have e3 : (b - a) * conj (b - a) = ((‖b - a‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      linear_combination e1 - e3 * ((f - a) * ((‖c - a‖ * ‖e - a‖ : ℝ) : ℂ))
    have hv1 : f - a = (b - a) * (c - a) * conj (e - a) *
        (((‖b - a‖ * ‖f - a‖ : ℝ) : ℂ) / (((‖c - a‖ * ‖e - a‖ : ℝ) : ℂ) * ((‖b - a‖ ^ 2 : ℝ) : ℂ))) := by
      field_simp [hN2c, hu1sq0]
      linear_combination e2
    generalize hρd : (((‖b - a‖ * ‖f - a‖ : ℝ) : ℂ) /
      (((‖c - a‖ * ‖e - a‖ : ℝ) : ℂ) * ((‖b - a‖ ^ 2 : ℝ) : ℂ))) = ρ
    have hρre : conj ρ = ρ := by
      rw [← hρd]
      simp [map_div₀, map_mul, Complex.conj_ofReal]
    have hfa2 : f = a + ρ * ((b - a) * (c - a) * conj (e - a)) := by
      have e1 : f - a = (b - a) * (c - a) * conj (e - a) * ρ := by
        rw [hv1, hρd]
      rw [show f = a + (f - a) from by ring, e1]
      ring
    have hfc : f = ((1 : ℂ) - (t : ℂ)) * b + (t : ℂ) * c := by
      rw [hf]; push_cast; ring
    have hline : f + b * c * conj f = b + c := by
      have hcb : conj b * b = 1 := by
        rw [← Complex.normSq_eq_conj_mul_self]; norm_cast
        rw [Complex.normSq_eq_norm_sq, hb]; norm_num
      have hcc : conj c * c = 1 := by
        rw [← Complex.normSq_eq_conj_mul_self]; norm_cast
        rw [Complex.normSq_eq_norm_sq, hc]; norm_num
      have e1 : conj f = ((1 : ℂ) - (t : ℂ)) * conj b + (t : ℂ) * conj c := by
        rw [hfc]
        simp only [map_add, map_mul, map_sub, map_one, Complex.conj_ofReal]
      rw [e1, hfc]
      linear_combination (1 - t : ℂ) * c * hcb + (t : ℂ) * b * hcc
    have hw : (b - a) * (c - a) * conj (e - a) +
        b * c * conj ((b - a) * (c - a) * conj (e - a)) =
        (a - b) * (a - c) * (a - e) ^ 2 / (a ^ 2 * e) := by
      have ha1 : star a = a⁻¹ := conj_of_norm_one ha
      have hb1 : star b = b⁻¹ := conj_of_norm_one hb
      have hc1 : star c = c⁻¹ := conj_of_norm_one hc
      have he1 : star e = e⁻¹ := conj_of_norm_one he
      have hcw : conj ((b - a) * (c - a) * conj (e - a)) =
          (b⁻¹ - a⁻¹) * (c⁻¹ - a⁻¹) * (e - a) := by
        have e1 : star (b - a) = b⁻¹ - a⁻¹ := by
          rw [star_sub, hb1, ha1]
        have e2 : star (c - a) = c⁻¹ - a⁻¹ := by
          rw [star_sub, hc1, ha1]
        have e3 : star ((starRingEnd ℂ) (e - a)) = e - a := by
          rw [starRingEnd_apply, star_star]
        rw [starRingEnd_apply, star_mul, star_mul, e1, e2, e3]
        ring
      have he2 : (b - a) * (c - a) * conj (e - a) = (a - b) * (a - c) * (a - e) / (a * e) := by
        rw [starRingEnd_apply, star_sub, he1, ha1]
        field_simp [ha0, he0]
        ring
      rw [hcw, he2]
      field_simp [ha0, hb0, hc0, he0]
      ring
    have hbc_a : b + c - a - b * c * conj a = -(a - b) * (a - c) / a := by
      rw [conj_of_norm_one ha]
      field_simp [ha0]
      ring
    have hline2 : ρ * ((b - a) * (c - a) * conj (e - a) +
        b * c * conj ((b - a) * (c - a) * conj (e - a))) = b + c - a - b * c * conj a := by
      have hc1 : conj (a + ρ * ((b - a) * (c - a) * conj (e - a))) =
          conj a + ρ * conj ((b - a) * (c - a) * conj (e - a)) := by
        rw [map_add, map_mul, hρre]
      rw [hfa2, hc1] at hline
      linear_combination hline
    exact f_formula_tail ha hb hc he hab hac hae hρre hfa2 hw hbc_a hline2

/-- A line through the point `a` of the unit circle in direction `v ≠ 0` meets the unit
circle in exactly one point different from `a`. -/
lemma line_circle_unique {a v w₁ w₂ : ℂ} (ha : ‖a‖ = 1) (hv : v ≠ 0)
    (h1 : ‖a + w₁‖ = 1) (h2 : ‖a + w₂‖ = 1)
    (hw1 : ∃ t₁ : ℝ, w₁ = (t₁ : ℝ) • v) (hw2 : ∃ t₂ : ℝ, w₂ = (t₂ : ℝ) • v)
    (hw1' : w₁ ≠ 0) (hw2' : w₂ ≠ 0) :
    w₁ = w₂ := by
  obtain ⟨t₁, ht₁⟩ := hw1
  obtain ⟨t₂, ht₂⟩ := hw2
  have key : ∀ t : ℝ, ‖a + (t : ℝ) • v‖ = 1 →
      (t : ℝ) • v = 0 ∨ (t : ℝ) • v = (-2 * (a * conj v).re / ‖v‖ ^ 2 : ℝ) • v := by
    intro t ht
    have e1 : conj (a + (t : ℝ) • v) * (a + (t : ℝ) • v) = 1 := by
      rw [← Complex.normSq_eq_conj_mul_self]
      norm_cast
      rw [Complex.normSq_eq_norm_sq, ht]
      norm_num
    have e2 : conj (a + (t : ℝ) • v) * (a + (t : ℝ) • v) =
        conj a * a + ((t : ℝ) : ℂ) * (conj a * v + a * conj v) +
          ((t : ℝ) : ℂ) ^ 2 * (conj v * v) := by
      rw [show (t : ℝ) • v = ((t : ℝ) : ℂ) * v from Complex.real_smul]
      simp only [map_add, map_mul, Complex.conj_ofReal]
      ring
    have e3 : conj a * a = 1 := by
      rw [← Complex.normSq_eq_conj_mul_self]; norm_cast
      rw [Complex.normSq_eq_norm_sq, ha]; norm_num
    have e4 : ((t : ℝ) : ℂ) * (conj a * v + a * conj v) = ((2 * (a * conj v).re * t : ℝ) : ℂ) := by
      have e5 : conj a * v + a * conj v = ((2 * (a * conj v).re : ℝ) : ℂ) := by
        rw [show conj a * v = conj (a * conj v) from by
          simp [map_mul, starRingEnd_self_apply], ← Complex.add_conj (a * conj v)]
        push_cast
        ring
      rw [e5]
      push_cast
      ring
    have e6 : ((t : ℝ) : ℂ) ^ 2 * (conj v * v) = ((t ^ 2 * ‖v‖ ^ 2 : ℝ) : ℂ) := by
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    rw [e2, e3, e4, e6] at e1
    have e7 : ((2 * (a * conj v).re * t : ℝ) : ℂ) + ((t ^ 2 * ‖v‖ ^ 2 : ℝ) : ℂ) = 0 := by
      linear_combination e1
    have e8 : (2 * (a * conj v).re * t + t ^ 2 * ‖v‖ ^ 2 : ℝ) = 0 := by
      have e9 : ((2 * (a * conj v).re * t + t ^ 2 * ‖v‖ ^ 2 : ℝ) : ℂ) = 0 := by
        rw [show ((2 * (a * conj v).re * t + t ^ 2 * ‖v‖ ^ 2 : ℝ) : ℂ) =
            ((2 * (a * conj v).re * t : ℝ) : ℂ) + ((t ^ 2 * ‖v‖ ^ 2 : ℝ) : ℂ) by
          push_cast; ring]
        exact e7
      exact Complex.ofReal_inj.mp e9
    have e10 : t * (2 * (a * conj v).re + t * ‖v‖ ^ 2) = 0 := by
      have e11 : (2 * (a * conj v).re * t + t ^ 2 * ‖v‖ ^ 2 : ℝ) =
          t * (2 * (a * conj v).re + t * ‖v‖ ^ 2) := by ring
      rw [e11] at e8
      exact e8
    rcases mul_eq_zero.mp e10 with ht0 | ht0
    · left
      rw [ht0]
      simp
    · right
      have hv0 : (‖v‖ ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)
      have e12 : t = -2 * (a * conj v).re / ‖v‖ ^ 2 := by
        field_simp [hv0]
        linear_combination ht0
      rw [e12]
  rcases key t₁ (by rwa [ht₁] at h1) with h | h
  · rw [h] at ht₁
    exact (hw1' ht₁).elim
  · rcases key t₂ (by rwa [ht₂] at h2) with h' | h'
    · rw [h'] at ht₂
      exact (hw2' ht₂).elim
    · rw [ht₁, ht₂, h, h']


/-- From collinearity of `{A, I, D}` with `I ≠ A`, the point `D` is an affine
combination: `D - A = t • (I - A)` for a real `t`. -/
lemma sbtv_of_collinear {A I D : ℂ} (h : Collinear ℝ ({A, I, D} : Set ℂ)) (hia : I ≠ A) :
    ∃ t : ℝ, D - A = (t : ℝ) • (I - A) := by
  rw [collinear_iff_exists_forall_eq_smul_vadd] at h
  obtain ⟨p₀, v, hv⟩ := h
  obtain ⟨rA, hrA⟩ := hv A (by simp)
  obtain ⟨rI, hrI⟩ := hv I (by simp)
  obtain ⟨rD, hrD⟩ := hv D (by simp)
  simp only [vadd_eq_add] at hrA hrI hrD
  have h1 : D - A = ((rD - rA) : ℝ) • v := by
    rw [hrD, hrA]; simp [sub_smul]
  have h2 : I - A = ((rI - rA) : ℝ) • v := by
    rw [hrI, hrA]; simp [sub_smul]
  have h3 : rI - rA ≠ 0 := by
    intro h
    apply hia
    have h4 : I - A = 0 := by
      rw [h2, h]; simp
    exact sub_eq_zero.mp h4
  have h5 : (↑rI - ↑rA : ℂ) * (D - A) = (↑rD - ↑rA : ℂ) * (I - A) := by
    rw [h1, h2]
    simp [smul_smul, Complex.real_smul]
    push_cast
    ring
  have hgoal : (D - A) * (↑rI - ↑rA : ℂ) = (↑rD - ↑rA : ℂ) * (I - A) := by
    linear_combination h5
  have hfrac' : (((rD - rA) / (rI - rA) : ℝ) : ℂ) = (↑rD - ↑rA : ℂ) / (↑rI - ↑rA : ℂ) := by
    rw [Complex.ofReal_div]
    push_cast
    ring
  have hfrac'' : (((rD - rA) / (rI - rA) : ℝ) : ℂ) * (I - A) = ((↑rD - ↑rA : ℂ) * (I - A)) / (↑rI - ↑rA : ℂ) := by
    rw [hfrac']
    ring
  have h3'' : (↑rI - ↑rA : ℂ) ≠ 0 := by
    rw [show (↑rI - ↑rA : ℂ) = ((rI - rA : ℝ) : ℂ) by push_cast; ring]
    exact_mod_cast h3
  refine ⟨(rD - rA) / (rI - rA), ?_⟩
  rw [Complex.real_smul, hfrac'']
  rw [eq_div_iff h3'']
  linear_combination hgoal

/-- The algebraic identification of `D`: `d₀ = -YZ` lies on the line `AI`. -/
lemma d₀_collinear {X Y Z A I d₀ : ℂ}
    (hX1 : ‖X‖ = 1) (hY1 : ‖Y‖ = 1) (hZ1 : ‖Z‖ = 1)
    (hX0 : X ≠ 0) (hY0 : Y ≠ 0) (hZ0 : Z ≠ 0)
    (hX2 : X ^ 2 = A) (hiXYZ : I = -(X * Y + Y * Z + Z * X)) (hd₀ : d₀ = -(Y * Z)) :
    Collinear ℝ ({A, I, d₀} : Set ℂ) := by
  rw [collinear_iff_cross_eq_zero]
  have hXc : conj X = X⁻¹ := conj_of_norm_one hX1
  have hYc : conj Y = Y⁻¹ := conj_of_norm_one hY1
  have hZc : conj Z = Z⁻¹ := conj_of_norm_one hZ1
  have e1 : I - A = -(X + Y) * (X + Z) := by
    rw [hiXYZ, ← hX2]
    ring
  have e2 : d₀ - A = -(X ^ 2 + Y * Z) := by
    rw [hd₀, ← hX2]
    ring
  have e3 : conj (conj (I - A) * (d₀ - A)) = conj (I - A) * (d₀ - A) := by
    rw [map_mul, starRingEnd_self_apply, e1, e2]
    simp only [map_neg, map_mul, map_add, map_pow, hXc, hYc, hZc]
    field_simp [hX0, hY0, hZ0]
    ring
  have e4 : (conj (I - A) * (d₀ - A)).im = 0 := by
    have h : (conj (I - A) * (d₀ - A)).im = (conj (conj (I - A) * (d₀ - A))).im := by
      rw [e3]
    rw [Complex.conj_im] at h
    linarith
  exact e4

/-- The main theorem of IMO 2010 Problem 2 in unit-circle form. -/
theorem imo2010_p2_unit {A B C I D E F G : ℂ}
    (hA : ‖A‖ = 1) (hB : ‖B‖ = 1) (hC : ‖C‖ = 1) (hE : ‖E‖ = 1)
    (hABC : cross (B - A) (C - A) ≠ 0)
    (hI : I = (A * (‖B - C‖ : ℂ) + B * (‖C - A‖ : ℂ) + C * (‖A - B‖ : ℂ)) /
      ((‖B - C‖ : ℂ) + (‖C - A‖ : ℂ) + (‖A - B‖ : ℂ)))
    (hD : ‖D‖ = 1) (hDline : Collinear ℝ ({A, I, D} : Set ℂ)) (hDA : D ≠ A)
    (hEarc : ∃ p : ℂ, (∃ s : ℝ, 0 < s ∧ s < 1 ∧ p = ((1 - s : ℝ) : ℂ) * A + (s : ℂ) * E) ∧
      (∃ u : ℝ, p = ((1 - u : ℝ) : ℂ) * B + (u : ℂ) * C))
    (hFseg : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ F = ((1 - t : ℝ) : ℂ) * B + (t : ℂ) * C)
    (hFA : F ≠ A)
    (hangle : ∠ B A F = ∠ C A E)
    (hG : G = (I + F) / 2) :
    ∃ X : ℂ, ‖X‖ = 1 ∧ Collinear ℝ ({D, G, X} : Set ℂ) ∧ Collinear ℝ ({E, I, X} : Set ℂ) := by
  -- distinctness of the vertices
  have hab : A ≠ B := by
    intro h
    rw [h] at hABC
    simp [cross] at hABC
  have hbc : B ≠ C := by
    intro h
    rw [h] at hABC
    exact hABC (cross_self _)
  have hca : C ≠ A := by
    intro h
    rw [h] at hABC
    simp [cross] at hABC
  -- the incenter is not a vertex
  have hia : I ≠ A := incenter_ne_vertex hab hbc hca hABC I hI
  -- the π-identity and the parametrization
  have hpi2 := pi_sq_eq hA hB hC hab hbc hca I hI hia
  have hpine := pi_ne_neg_a hA hB hC hab hbc hca hABC I hI hia
  obtain ⟨X, Y, Z, hX2, hY2, hZ2, hiXYZ, hYZne⟩ := incenter_param hA hB hC hab hbc hca I hI hia hpi2 hpine
  -- unit moduli of the square roots
  have hX0 : X ≠ 0 := by
    intro h
    rw [h] at hX2
    simp at hX2
    rw [← hX2] at hA
    norm_num at hA
  have hY0 : Y ≠ 0 := by
    intro h
    rw [h] at hY2
    simp at hY2
    rw [← hY2] at hB
    norm_num at hB
  have hZ0 : Z ≠ 0 := by
    intro h
    rw [h] at hZ2
    simp at hZ2
    rw [← hZ2] at hC
    norm_num at hC
  have hX1 : ‖X‖ = 1 := by
    have h1 : ‖X ^ 2‖ = 1 := by rw [hX2, hA]
    rw [norm_pow, sq_eq_one_iff] at h1
    rcases h1 with h1 | h1
    · exact h1
    · linarith [norm_nonneg X]
  have hY1 : ‖Y‖ = 1 := by
    have h1 : ‖Y ^ 2‖ = 1 := by rw [hY2, hB]
    rw [norm_pow, sq_eq_one_iff] at h1
    rcases h1 with h1 | h1
    · exact h1
    · linarith [norm_nonneg Y]
  have hZ1 : ‖Z‖ = 1 := by
    have h1 : ‖Z ^ 2‖ = 1 := by rw [hZ2, hC]
    rw [norm_pow, sq_eq_one_iff] at h1
    rcases h1 with h1 | h1
    · exact h1
    · linarith [norm_nonneg Z]
  have hXc : conj X = X⁻¹ := conj_of_norm_one hX1
  have hYc : conj Y = Y⁻¹ := conj_of_norm_one hY1
  have hZc : conj Z = Z⁻¹ := conj_of_norm_one hZ1
  -- `A ≠ E` from the arc position of `E`
  have hae : A ≠ E := by
    intro h
    obtain ⟨p, ⟨s, hs0, hs1, hps⟩, u, hpu⟩ := hEarc
    rw [← h] at hps
    have hpA : p = A := by
      rw [hps]
      push_cast
      ring
    have hcolABC : Collinear ℝ ({A, B, C} : Set ℂ) := by
      rw [collinear_iff_exists_forall_eq_smul_vadd]
      refine ⟨B, C - B, fun q hq => ?_⟩
      have h3cases : q = A ∨ q = B ∨ q = C := by
        simpa using hq
      rcases h3cases with rfl | rfl | rfl
      · refine ⟨u, ?_⟩
        rw [vadd_eq_add, ← hpA, hpu, Complex.real_smul]
        push_cast
        ring
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
    exact hABC (collinear_iff_cross_eq_zero.mp hcolABC)
  -- the point `d₀ = -YZ` and `D = d₀`
  set d₀ := -(Y * Z) with hd₀
  have hd₀1 : ‖d₀‖ = 1 := by
    rw [hd₀]
    simp [hY1, hZ1]
  have hd₀A : d₀ ≠ A := by
    rw [hd₀]
    intro h
    exact hYZne (neg_eq_iff_eq_neg.mp h)
  have hd₀col : Collinear ℝ ({A, I, d₀} : Set ℂ) :=
    d₀_collinear hX1 hY1 hZ1 hX0 hY0 hZ0 hX2 hiXYZ hd₀
  have hdD : D = d₀ := by
    obtain ⟨tD, htD⟩ := sbtv_of_collinear hDline hia
    obtain ⟨t₀, ht₀⟩ := sbtv_of_collinear hd₀col hia
    have hDeq : D - A = d₀ - A := by
      apply line_circle_unique hA (sub_ne_zero.mpr hia) ?_ ?_ ⟨tD, htD⟩ ⟨t₀, ht₀⟩ ?_ ?_
      · rw [show A + (D - A) = D from by simp, hD]
      · rw [show A + (d₀ - A) = d₀ from by simp, hd₀1]
      · intro h
        apply hDA
        rw [show D = A + (D - A) from by simp, h]
        simp
      · intro h
        apply hd₀A
        rw [show d₀ = A + (d₀ - A) from by simp, h]
        simp
    rw [show D = A + (D - A) from by simp, hDeq]
    simp
  -- the formula for `F`
  have hf : F = (A * (B + C - E) - B * C) / (A - E) :=
    f_formula hA hB hC hE hab hca.symm hae hABC hFseg hFA hEarc hangle
  -- the incenter is strictly inside the circle, hence different from `E`
  have hi_lt : ‖I‖ < 1 := by
    have h := incenter_norm_lt hA hB hC hab hbc hca
    have hp : (0 : ℝ) < ‖B - C‖ + ‖C - A‖ + ‖A - B‖ := by
      have hα : (0 : ℝ) < ‖B - C‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hbc)
      linarith [norm_nonneg (C - A), norm_nonneg (A - B)]
    have hpn : ‖(‖B - C‖ : ℂ) + (‖C - A‖ : ℂ) + (‖A - B‖ : ℂ)‖ =
        ‖B - C‖ + ‖C - A‖ + ‖A - B‖ := by
      rw [show ((‖B - C‖ : ℂ) + (‖C - A‖ : ℂ) + (‖A - B‖ : ℂ)) =
          ((‖B - C‖ + ‖C - A‖ + ‖A - B‖ : ℝ) : ℂ) by push_cast; ring]
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [hI, norm_div, hpn]
    exact (div_lt_one hp).mpr h
  have hie : I ≠ E := by
    intro h
    rw [h, hE] at hi_lt
    norm_num at hi_lt
  have hie' : conj I - conj E ≠ 0 := by
    intro hc
    apply hie
    have h2 : I - E = 0 := by
      have hc' : star I - star E = 0 := hc
      have h3 : star (I - E) = star 0 := by
        rw [star_sub, hc', star_zero]
      exact star_injective h3
    exact sub_eq_zero.mp h2
  -- the second intersection `k` of `EI` with the circle
  set k := conj E * (E - I) / (conj I - conj E) with hk
  have hk1 : ‖k‖ = 1 := by
    have e1 : conj k * k = 1 := by
      have e2 : conj E * E = 1 := by
        rw [mul_comm]
        exact mul_conj_of_norm_one hE
      have e3 : conj k = E * (conj E - conj I) / (I - E) := by
        rw [hk]
        simp [map_mul, map_div₀, map_sub]
      have e4 : (E - I) * (conj E - conj I) = ((‖E - I‖ ^ 2 : ℝ) : ℂ) := by
        have e5 : (E - I) * (conj E - conj I) = (I - E) * conj (I - E) := by
          rw [map_sub]
          ring
        rw [e5, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        rw [show I - E = -(E - I) from by ring, norm_neg]
      have e5 : conj (I - E) = conj I - conj E := by rw [map_sub]
      have e6 : conj (I - E) * (I - E) = ((‖I - E‖ ^ 2 : ℝ) : ℂ) := by
        rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
      have e7 : (conj I - conj E) * (I - E) = ((‖I - E‖ ^ 2 : ℝ) : ℂ) := by
        rw [← e5, e6]
      have e8 : conj E * E * ((E - I) * (conj E - conj I)) =
          (conj I - conj E) * (I - E) := by
        rw [show conj E * E * ((E - I) * (conj E - conj I)) =
            (conj E * E) * ((E - I) * (conj E - conj I)) from by ring, e2, one_mul, e4, e7]
        rw [show I - E = -(E - I) from by ring, norm_neg]
      rw [e3, hk]
      field_simp [hie', sub_ne_zero.mpr hie]
      linear_combination e8
    have h1 : normSq k = 1 := by
      rw [← Complex.normSq_eq_conj_mul_self] at e1
      exact_mod_cast e1
    rw [Complex.normSq_eq_norm_sq] at h1
    rcases sq_eq_one_iff.mp h1 with h1 | h1
    · exact h1
    · linarith [norm_nonneg k]
  have hkc : Collinear ℝ ({E, I, k} : Set ℂ) := by
    rw [collinear_iff_cross_eq_zero]
    have e1 : k - E = ((2 - 2 * (E * conj I).re : ℝ) : ℂ) / (conj I - conj E) := by
      rw [hk]
      have e2 : conj E * (E - I) - E * (conj I - conj E) =
          ((2 - 2 * (E * conj I).re : ℝ) : ℂ) := by
        rw [show ((2 - 2 * (E * conj I).re : ℝ) : ℂ) =
            2 - ((2 * (E * conj I).re : ℝ) : ℂ) by push_cast; ring]
        have e3 : conj E * E = 1 := by
          rw [mul_comm]
          exact mul_conj_of_norm_one hE
        have e5 : E * conj E = 1 := mul_conj_of_norm_one hE
        have e4 : conj E * I + E * conj I = ((2 * (E * conj I).re : ℝ) : ℂ) := by
          rw [show conj E * I = conj (E * conj I) from by simp [mul_comm],
            ← Complex.add_conj (E * conj I)]
          push_cast
          ring
        linear_combination e3 + e5 - e4
      rw [show conj E * (E - I) / (conj I - conj E) - E =
          (conj E * (E - I) - E * (conj I - conj E)) / (conj I - conj E) from by
        field_simp [hie']]
      rw [e2]
    have e5 : conj (conj (I - E) * (k - E)) = conj (I - E) * (k - E) := by
      rw [map_mul, starRingEnd_self_apply, e1]
      have e6 : conj (((2 - 2 * (E * conj I).re : ℝ) : ℂ) / (conj I - conj E)) =
          ((2 - 2 * (E * conj I).re : ℝ) : ℂ) / (I - E) := by
        rw [map_div₀, Complex.conj_ofReal, map_sub, starRingEnd_self_apply,
          starRingEnd_self_apply]
      rw [e6]
      have e7 : conj (I - E) = conj I - conj E := by rw [map_sub]
      rw [e7]
      field_simp [hie', sub_ne_zero.mpr hie]
    have e8 : (conj (I - E) * (k - E)).im = 0 := by
      have h : (conj (I - E) * (k - E)).im = (conj (conj (I - E) * (k - E))).im := by
        rw [e5]
      rw [Complex.conj_im] at h
      linarith
    exact e8
  -- the main collinearity
  have hmain : Collinear ℝ ({d₀, G, k} : Set ℂ) := by
    have he0 : E ≠ 0 := by
      rw [← norm_ne_zero_iff, hE]; norm_num
    have hXe : X ^ 2 ≠ E := by
      rw [hX2]
      exact fun h => hae h
    have hec : star E = E⁻¹ := conj_of_norm_one hE
    have hXc' : star X = X⁻¹ := hXc
    have hYc' : star Y = Y⁻¹ := hYc
    have hZc' : star Z = Z⁻¹ := hZc
    have hf' : F = (X ^ 2 * (Y ^ 2 + Z ^ 2 - E) - Y ^ 2 * Z ^ 2) / (X ^ 2 - E) := by
      rw [hf, hX2, hY2, hZ2]
    have hmid := main_identity X Y Z E I F k d₀ hX0 hY0 hZ0 he0 hXc' hYc' hZc' hec hiXYZ hf' hk hd₀ hXe hie
    rw [← hG] at hmid
    rw [collinear_iff_cross_eq_zero]
    have e3 : (conj (k - G) * (k - d₀)).im = 0 := by
      have h1 : conj (k - G) * (k - d₀) = conj ((k - G) * star (k - d₀)) := by
        simp only [map_mul, starRingEnd_apply, star_star]
      have hw : conj ((k - G) * star (k - d₀)) = star (k - G) * (k - d₀) := by
        simp only [map_mul, starRingEnd_apply, star_star]
      have h2 : (k - G) * star (k - d₀) = conj ((k - G) * star (k - d₀)) := by
        rw [hw]
        exact sub_eq_zero.mp hmid
      have h7 : (conj ((k - G) * star (k - d₀))).im =
          -(((k - G) * star (k - d₀)).im) := Complex.conj_im _
      rw [← h2] at h7
      rw [h1, Complex.conj_im]
      linarith
    have e4 : cross (G - d₀) (k - d₀) = -cross (k - G) (k - d₀) := by
      have e6 : (conj (k - d₀) * (k - d₀)).im = 0 := by
        rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_im]
      have e5 : conj (G - d₀) = conj (k - d₀) - conj (k - G) := by
        rw [map_sub, map_sub, map_sub]
        ring
      rw [cross, cross, e5, sub_mul, Complex.sub_im, e6, zero_sub]
    rw [e4, cross, e3, neg_zero]
  exact ⟨k, hk1, by rw [hdD]; exact hmain, hkc⟩

snip end

problem imo2010_p2 (Γ : Sphere ℂ) (A B C I D E F G : ℂ)
    (hABC : ¬Collinear ℝ ({A, B, C} : Set ℂ))
    (hAΓ : A ∈ Γ) (hBΓ : B ∈ Γ) (hCΓ : C ∈ Γ)
    (hI : I = (A * (‖B - C‖ : ℂ) + B * (‖C - A‖ : ℂ) + C * (‖A - B‖ : ℂ)) /
      ((‖B - C‖ : ℂ) + (‖C - A‖ : ℂ) + (‖A - B‖ : ℂ)))
    (hDΓ : D ∈ Γ) (hDline : Collinear ℝ ({A, I, D} : Set ℂ)) (hDA : D ≠ A)
    (hEΓ : E ∈ Γ) (hEarc : (line[ℝ, B, C]).SOppSide A E)
    (hFseg : Wbtw ℝ B F C) (hFA : F ≠ A)
    (hangle : ∠ B A F = ∠ C A E)
    (hlt : ∠ C A E < (1/2) * ∠ B A C)
    (hG : G = midpoint ℝ I F) :
    ∃ X : ℂ, X ∈ Γ ∧ Collinear ℝ ({D, G, X} : Set ℂ) ∧ Collinear ℝ ({E, I, X} : Set ℂ) := by
  -- the radius is positive, for otherwise `A = B`
  have hr : 0 < Γ.radius := by
    by_contra hle
    push Not at hle
    have hdA : dist A Γ.center = Γ.radius := mem_sphere.mp hAΓ
    have h0 : Γ.radius = 0 := le_antisymm hle (hdA ▸ dist_nonneg)
    have hA0 : A = Γ.center := by
      rw [h0] at hdA
      exact dist_eq_zero.mp hdA
    have hB0 : B = Γ.center := by
      have hdB : dist B Γ.center = Γ.radius := mem_sphere.mp hBΓ
      rw [h0] at hdB
      exact dist_eq_zero.mp hdB
    apply hABC
    rw [hA0, hB0, collinear_iff_cross_eq_zero]
    simp [cross]
  have hrC : (Γ.radius : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  -- distinctness of the vertices
  have hab : A ≠ B := by
    intro h
    apply hABC
    rw [h, collinear_iff_cross_eq_zero]
    simp [cross]
  have hbc : B ≠ C := by
    intro h
    apply hABC
    rw [h, collinear_iff_cross_eq_zero]
    exact cross_self _
  have hca : C ≠ A := by
    intro h
    apply hABC
    rw [h, collinear_iff_cross_eq_zero]
    simp [cross]
  have hABCc : cross (B - A) (C - A) ≠ 0 :=
    fun h => hABC ((collinear_iff_cross_eq_zero).mpr h)
  -- norms of points on the sphere
  have hnorm : ∀ z : ℂ, z ∈ Γ → ‖z - Γ.center‖ = Γ.radius := by
    intro z hz
    rw [← dist_eq_norm]
    exact mem_sphere.mp hz
  -- algebraic facts about the scaling map `z ↦ (z - center)/radius`
  have hφ : ∀ x y : ℂ, (x - Γ.center) / Γ.radius - (y - Γ.center) / Γ.radius =
      (x - y) / Γ.radius := fun x y => by ring
  have hside : ∀ x y : ℂ,
      ‖(x - Γ.center) / Γ.radius - (y - Γ.center) / Γ.radius‖ = ‖x - y‖ / Γ.radius := by
    intro x y
    rw [hφ, norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le]
  have hcross : ∀ u v : ℂ, cross (u / Γ.radius) (v / Γ.radius) =
      Γ.radius⁻¹ ^ 2 * cross u v := by
    intro u v
    rw [show u / Γ.radius = (Γ.radius⁻¹ : ℝ) • u by
          rw [Complex.real_smul]; push_cast; ring,
        show v / Γ.radius = (Γ.radius⁻¹ : ℝ) • v by
          rw [Complex.real_smul]; push_cast; ring,
        cross_smul_left, cross_smul_right]
    ring
  have hφaff : ∀ (c : ℝ) (x y : ℂ),
      (↑(1 - c) * x + ↑c * y - Γ.center) / Γ.radius =
      ↑(1 - c) * ((x - Γ.center) / Γ.radius) + ↑c * ((y - Γ.center) / Γ.radius) := by
    intro c x y
    field_simp [hrC]
    push_cast
    ring
  -- unit-modulus hypotheses
  have eA : ‖(A - Γ.center) / Γ.radius‖ = 1 := by
    rw [norm_div, hnorm A hAΓ, Complex.norm_real, Real.norm_of_nonneg hr.le,
      div_self hr.ne']
  have eB : ‖(B - Γ.center) / Γ.radius‖ = 1 := by
    rw [norm_div, hnorm B hBΓ, Complex.norm_real, Real.norm_of_nonneg hr.le,
      div_self hr.ne']
  have eC : ‖(C - Γ.center) / Γ.radius‖ = 1 := by
    rw [norm_div, hnorm C hCΓ, Complex.norm_real, Real.norm_of_nonneg hr.le,
      div_self hr.ne']
  have eE : ‖(E - Γ.center) / Γ.radius‖ = 1 := by
    rw [norm_div, hnorm E hEΓ, Complex.norm_real, Real.norm_of_nonneg hr.le,
      div_self hr.ne']
  have eD : ‖(D - Γ.center) / Γ.radius‖ = 1 := by
    rw [norm_div, hnorm D hDΓ, Complex.norm_real, Real.norm_of_nonneg hr.le,
      div_self hr.ne']
  -- non-collinearity
  have hABCc' : cross ((B - Γ.center) / Γ.radius - (A - Γ.center) / Γ.radius)
      ((C - Γ.center) / Γ.radius - (A - Γ.center) / Γ.radius) ≠ 0 := by
    rw [hφ, hφ, hcross]
    exact mul_ne_zero (pow_ne_zero 2 (inv_ne_zero hr.ne')) hABCc
  -- the incenter formula
  have hperi : ((‖B - C‖ : ℂ) + (‖C - A‖ : ℂ) + (‖A - B‖ : ℂ)) ≠ 0 :=
    perimeter_ne_zero hab hbc hca
  have hperi' : (↑(‖B - C‖ / Γ.radius) + ↑(‖C - A‖ / Γ.radius) +
      ↑(‖A - B‖ / Γ.radius) : ℂ) ≠ 0 := by
    rw [show (↑(‖B - C‖ / Γ.radius) + ↑(‖C - A‖ / Γ.radius) +
        ↑(‖A - B‖ / Γ.radius) : ℂ) =
        ((‖B - C‖ : ℂ) + (‖C - A‖ : ℂ) + (‖A - B‖ : ℂ)) / Γ.radius by push_cast; ring]
    exact div_ne_zero hperi hrC
  have hI' : (I - Γ.center) / Γ.radius =
      ((A - Γ.center) / Γ.radius *
          (↑‖(B - Γ.center) / Γ.radius - (C - Γ.center) / Γ.radius‖) +
        (B - Γ.center) / Γ.radius *
          (↑‖(C - Γ.center) / Γ.radius - (A - Γ.center) / Γ.radius‖) +
        (C - Γ.center) / Γ.radius *
          (↑‖(A - Γ.center) / Γ.radius - (B - Γ.center) / Γ.radius‖)) /
        (↑‖(B - Γ.center) / Γ.radius - (C - Γ.center) / Γ.radius‖ +
          ↑‖(C - Γ.center) / Γ.radius - (A - Γ.center) / Γ.radius‖ +
          ↑‖(A - Γ.center) / Γ.radius - (B - Γ.center) / Γ.radius‖) := by
    rw [hside, hside, hside, hI]
    simp only [Complex.ofReal_div]
    field_simp [hrC, hperi]
    ring
  -- collinearity of `A, I, D`
  have hDline' : Collinear ℝ ({(A - Γ.center) / Γ.radius, (I - Γ.center) / Γ.radius,
      (D - Γ.center) / Γ.radius} : Set ℂ) := by
    rw [collinear_iff_cross_eq_zero, hφ, hφ, hcross,
      (collinear_iff_cross_eq_zero).mp hDline, mul_zero]
  have hDA' : (D - Γ.center) / Γ.radius ≠ (A - Γ.center) / Γ.radius := by
    intro h
    apply hDA
    rw [div_eq_div_iff hrC hrC] at h
    have h1 : D - Γ.center = A - Γ.center := mul_right_cancel₀ hrC h
    have h2 : D - Γ.center + Γ.center = A - Γ.center + Γ.center :=
      congrArg (· + Γ.center) h1
    rwa [sub_add_cancel, sub_add_cancel] at h2
  -- the arc position of `E`
  obtain ⟨p, hpmem, hpsbtw⟩ := hEarc.exists_sbtw
  obtain ⟨hpw, hpA, hpE⟩ := hpsbtw
  rw [← mem_segment_iff_wbtw, segment_eq_image_lineMap] at hpw
  obtain ⟨s, hs, hps⟩ := hpw
  rw [Set.mem_Icc] at hs
  obtain ⟨hs0, hs1⟩ := hs
  rw [AffineMap.lineMap_apply_module] at hps
  have hs0' : 0 < s := by
    rcases hs0.eq_or_lt with h | h
    · exfalso
      apply hpA
      rw [← hps, ← h]
      simp
    · exact h
  have hs1' : s < 1 := by
    rcases hs1.eq_or_lt with h | h
    · exfalso
      apply hpE
      rw [← hps, h]
      simp
    · exact h
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hpmem
  obtain ⟨u, hpu⟩ := hpmem
  rw [AffineMap.lineMap_apply_module] at hpu
  have hEarc' : ∃ q : ℂ, (∃ s₀ : ℝ, 0 < s₀ ∧ s₀ < 1 ∧ q =
      ↑(1 - s₀) * ((A - Γ.center) / Γ.radius) + ↑s₀ * ((E - Γ.center) / Γ.radius)) ∧
      (∃ u₀ : ℝ, q = ↑(1 - u₀) * ((B - Γ.center) / Γ.radius) +
        ↑u₀ * ((C - Γ.center) / Γ.radius)) := by
    refine ⟨(p - Γ.center) / Γ.radius, ⟨s, hs0', hs1', ?_⟩, ⟨u, ?_⟩⟩
    · have hps' : p = ↑(1 - s) * A + ↑s * E := by
        rw [← hps, Complex.real_smul, Complex.real_smul]
      rw [← hφaff s A E, ← hps']
    · have hpu' : p = ↑(1 - u) * B + ↑u * C := by
        rw [← hpu, Complex.real_smul, Complex.real_smul]
      rw [← hφaff u B C, ← hpu']
  -- `F` on the segment `BC`
  rw [← mem_segment_iff_wbtw, segment_eq_image_lineMap] at hFseg
  obtain ⟨t, ht, htF⟩ := hFseg
  rw [Set.mem_Icc] at ht
  obtain ⟨ht0, ht1⟩ := ht
  rw [AffineMap.lineMap_apply_module] at htF
  have hFseg' : ∃ t₀ : ℝ, 0 ≤ t₀ ∧ t₀ ≤ 1 ∧ (F - Γ.center) / Γ.radius =
      ↑(1 - t₀) * ((B - Γ.center) / Γ.radius) + ↑t₀ * ((C - Γ.center) / Γ.radius) := by
    refine ⟨t, ht0, ht1, ?_⟩
    have htF' : F = ↑(1 - t) * B + ↑t * C := by
      rw [← htF, Complex.real_smul, Complex.real_smul]
    rw [← hφaff t B C, ← htF']
  have hFA' : (F - Γ.center) / Γ.radius ≠ (A - Γ.center) / Γ.radius := by
    intro h
    apply hFA
    rw [div_eq_div_iff hrC hrC] at h
    have h1 : F - Γ.center = A - Γ.center := mul_right_cancel₀ hrC h
    have h2 : F - Γ.center + Γ.center = A - Γ.center + Γ.center :=
      congrArg (· + Γ.center) h1
    rwa [sub_add_cancel, sub_add_cancel] at h2
  -- the angle condition
  have hri : 0 < Γ.radius⁻¹ := inv_pos.mpr hr
  have hφv : ∀ x y : ℂ, (x - Γ.center) / Γ.radius -ᵥ ((y - Γ.center) / Γ.radius) =
      (Γ.radius⁻¹ : ℝ) • (x -ᵥ y) := by
    intro x y
    rw [vsub_eq_sub, vsub_eq_sub, hφ, Complex.real_smul]
    push_cast
    ring
  have hangle' : ∠ ((B - Γ.center) / Γ.radius) ((A - Γ.center) / Γ.radius)
      ((F - Γ.center) / Γ.radius) =
      ∠ ((C - Γ.center) / Γ.radius) ((A - Γ.center) / Γ.radius)
        ((E - Γ.center) / Γ.radius) := by
    show InnerProductGeometry.angle
        ((B - Γ.center) / Γ.radius -ᵥ (A - Γ.center) / Γ.radius)
        ((F - Γ.center) / Γ.radius -ᵥ (A - Γ.center) / Γ.radius) =
      InnerProductGeometry.angle
        ((C - Γ.center) / Γ.radius -ᵥ (A - Γ.center) / Γ.radius)
        ((E - Γ.center) / Γ.radius -ᵥ (A - Γ.center) / Γ.radius)
    rw [hφv B A, hφv F A, hφv C A, hφv E A,
      InnerProductGeometry.angle_smul_left_of_pos _ _ hri,
      InnerProductGeometry.angle_smul_right_of_pos _ _ hri,
      InnerProductGeometry.angle_smul_left_of_pos _ _ hri,
      InnerProductGeometry.angle_smul_right_of_pos _ _ hri]
    exact hangle
  -- the midpoint
  have h2 : (⅟2 : ℝ) = 1 / 2 := by
    rw [eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)]
    exact Invertible.invOf_mul_self
  have hG' : (G - Γ.center) / Γ.radius =
      ((I - Γ.center) / Γ.radius + (F - Γ.center) / Γ.radius) / 2 := by
    have e1 : midpoint ℝ I F = (I + F) / 2 := by
      rw [midpoint_eq_smul_add, Complex.real_smul, h2]
      push_cast
      ring
    rw [hG, e1]
    field_simp [hrC]
    ring
  -- apply the unit-circle theorem
  obtain ⟨X', hX'1, hX'c1, hX'c2⟩ := imo2010_p2_unit eA eB eC eE hABCc' hI' eD
    hDline' hDA' hEarc' hFseg' hFA' hangle' hG'
  -- map the intersection point back to `Γ`
  have hsc : ∀ z : ℂ, (Γ.radius : ℂ) * ((z - Γ.center) / Γ.radius) = z - Γ.center := by
    intro z
    rw [mul_comm, div_mul_cancel₀ _ hrC]
  refine ⟨(Γ.radius : ℂ) * X' + Γ.center, ?_, ?_, ?_⟩
  · rw [mem_sphere, dist_eq_norm]
    have e1 : (Γ.radius : ℂ) * X' + Γ.center - Γ.center = (Γ.radius : ℂ) * X' := by ring
    rw [e1, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le, hX'1, mul_one]
  · have e1 : G - D = (Γ.radius : ℂ) *
        (((G - Γ.center) / Γ.radius) - ((D - Γ.center) / Γ.radius)) := by
      rw [mul_sub, hsc, hsc]
      ring
    have e2 : (Γ.radius : ℂ) * X' + Γ.center - D =
        (Γ.radius : ℂ) * (X' - (D - Γ.center) / Γ.radius) := by
      rw [mul_sub, hsc]
      ring
    rw [collinear_iff_cross_eq_zero, e1, e2, ← Complex.real_smul, ← Complex.real_smul,
      cross_smul_left, cross_smul_right, (collinear_iff_cross_eq_zero).mp hX'c1,
      mul_zero, mul_zero]
  · have e1 : I - E = (Γ.radius : ℂ) *
        (((I - Γ.center) / Γ.radius) - ((E - Γ.center) / Γ.radius)) := by
      rw [mul_sub, hsc, hsc]
      ring
    have e2 : (Γ.radius : ℂ) * X' + Γ.center - E =
        (Γ.radius : ℂ) * (X' - (E - Γ.center) / Γ.radius) := by
      rw [mul_sub, hsc]
      ring
    rw [collinear_iff_cross_eq_zero, e1, e2, ← Complex.real_smul, ← Complex.real_smul,
      cross_smul_left, cross_smul_right, (collinear_iff_cross_eq_zero).mp hX'c2,
      mul_zero, mul_zero]

end Imo2010P2
