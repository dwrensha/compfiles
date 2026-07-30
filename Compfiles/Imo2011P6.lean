/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 2011, Problem 6

Let ABC be an acute triangle with circumcircle Γ. Let ℓ be a tangent line to Γ,
and let ℓₐ, ℓ_b, ℓ_c be the lines obtained by reflecting ℓ in the lines BC, CA,
and AB, respectively. Show that the circumcircle of the triangle determined by
the lines ℓₐ, ℓ_b, ℓ_c is tangent to the circle Γ.

## Formalization notes

We work in the complex plane and normalize so that Γ is the unit circle, so the
vertices are complex numbers `a`, `b`, `c` of norm 1 and the tangent point is a
complex number `p` of norm 1.  Acuteness is expressed by positivity of the dot
products `Re ((b - a) * conj (c - a))` etc.

The proof follows the complex-number solution from Evan Chen's IMO 2011 notes:
with `A₁ = ℓ_b ∩ ℓ_c` etc. and `A₂` the reflection of `p` in the diameter
through `a`, the lines `A₁A₂`, `B₁B₂`, `C₁C₂` concur at a point `T` of Γ, and
`A₁B₁ ∥ A₂B₂` (and cyclically), so the circumcircle of `A₁B₁C₁` is the image of
Γ under a homothety centered at `T`, hence tangent to Γ at `T`.

The proof requires generic-position hypotheses on the tangent line ℓ, which we
include as explicit hypotheses: `p ≠ a` (the tangent point is not the vertex
`a`; note that the cases `p = b` and `p = c` are still covered, since they
satisfy this), `a + b + c ≠ p` (otherwise the concurrence point escapes to
infinity), `A₁ ≠ T` (the three reflected lines are not concurrent) and
`A₁ ≠ A₂` (the two circles do not coincide).
-/

namespace Imo2011P6

open scoped ComplexConjugate

/-- The tangent line at `p` to the unit circle, as a set of complex numbers:
the equation `z + p² * conj z = 2p` says `Re (z * conj p) = 1`. -/
noncomputable def tanLine (p : ℂ) : Set ℂ := {z | z + p ^ 2 * conj z = 2 * p}

/-- Reflection of a point `w` in the line through two points `x`, `y`
of the unit circle. -/
noncomputable def reflPt (x y w : ℂ) : ℂ := x + y - x * y * conj w

/-- The reflection of a set of points in the line through `x` and `y`
(of the unit circle), written as a preimage since reflection is an involution. -/
noncomputable def reflLine (x y : ℂ) (ℓ : Set ℂ) : Set ℂ := reflPt x y ⁻¹' ℓ

/-- The intersection of the reflections of the tangent line at `p` in the lines
`xy` and `xz` (with `x`, `y`, `z`, `p` on the unit circle).  This is the vertex
of the reflected triangle "opposite to `x`". -/
noncomputable def vtx (x y z p : ℂ) : ℂ := x + y * z * (x - p) ^ 2 / (p ^ 2 * (y + z))

/-- The reflection of `p` in the diameter of the unit circle through `x`. -/
noncomputable def antip (x p : ℂ) : ℂ := x ^ 2 / p

/-- The point of the unit circle where the lines joining the reflected-triangle
vertices to the diameter-reflections of `p` concur. -/
noncomputable def miquelT (a b c p : ℂ) : ℂ := (a * b + b * c + c * a - a * b * c / p) / (a + b + c - p)

/-- The ratio of the homothety centered at `miquelT a b c p` sending
`antip a p` to `vtx a b c p`. -/
noncomputable def hratio (a b c p : ℂ) : ℂ :=
  (vtx a b c p - miquelT a b c p) / (antip a p - miquelT a b c p)

snip begin

lemma conj_of_norm_one {x : ℂ} (hx : ‖x‖ = 1) : conj x = x⁻¹ := by
  have h : conj x * x = 1 := by
    rw [mul_comm, Complex.mul_conj', hx]
    norm_num
  exact eq_inv_of_mul_eq_one_left h

lemma ne_zero_of_norm_one {x : ℂ} (hx : ‖x‖ = 1) : x ≠ 0 := by
  rintro rfl
  simp at hx

lemma conj_ne_zero {z : ℂ} (hz : z ≠ 0) : conj z ≠ 0 := by
  intro hz0
  apply hz
  have := congrArg conj hz0
  rwa [starRingEnd_self_apply, map_zero] at this

/-- In an acute triangle, no side is a diameter. -/
lemma add_ne_zero_of_dot_pos {u v w : ℂ} (hv : ‖v‖ = 1) (hu : ‖u‖ = 1)
    (h : 0 < ((v - u) * conj (w - u)).re) : v + w ≠ 0 := by
  intro hvw
  have hw : w = -v := by linear_combination hvw
  subst hw
  have hv0 := ne_zero_of_norm_one hv
  have hu0 := ne_zero_of_norm_one hu
  simp only [map_neg, map_sub, conj_of_norm_one hv, conj_of_norm_one hu] at h
  have e : (v - u) * (-v⁻¹ - u⁻¹) = u / v - v / u := by
    field_simp [hv0, hu0]
    ring
  rw [e] at h
  have e2 : conj (u / v) = v / u := by
    simp only [map_div₀, conj_of_norm_one hv, conj_of_norm_one hu]
    field_simp [hv0, hu0]
  have h0 : (u / v - v / u).re = 0 := by
    rw [Complex.sub_re, ← e2, Complex.conj_re]
    ring
  linarith

lemma vtx_comm (x y z p : ℂ) : vtx x y z p = vtx x z y p := by
  rw [vtx, vtx, mul_comm y z, add_comm y z]

lemma reflPt_comm (x y w : ℂ) : reflPt x y w = reflPt y x w := by
  rw [reflPt, reflPt, add_comm x y, mul_comm x y]

lemma reflLine_comm (x y : ℂ) (ℓ : Set ℂ) : reflLine x y ℓ = reflLine y x ℓ := by
  ext w
  simp only [reflLine, Set.mem_preimage, reflPt_comm]

/-- The vertex `vtx x y z p` lies on the reflection of the tangent line in the
line `xy` (a rational identity, checked here by `field_simp` and `ring`). -/
lemma vtx_mem {x y z p : ℂ} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1) (hp : ‖p‖ = 1)
    (hyz : y + z ≠ 0) : reflPt x y (vtx x y z p) ∈ tanLine p := by
  have hx0 := ne_zero_of_norm_one hx
  have hy0 := ne_zero_of_norm_one hy
  have hz0 := ne_zero_of_norm_one hz
  have hp0 := ne_zero_of_norm_one hp
  have hcomb : y⁻¹ + z⁻¹ = (y + z) / (y * z) := by
    field_simp [hy0, hz0]
    ring
  simp only [tanLine, Set.mem_setOf_eq, reflPt, vtx, map_add, map_sub, map_mul, map_div₀,
    map_pow, map_inv₀, conj_of_norm_one hx, conj_of_norm_one hy,
    conj_of_norm_one hz, conj_of_norm_one hp]
  rw [hcomb]
  field_simp [hx0, hy0, hz0, hp0, hyz]
  ring

/-- The concurrence point lies on the unit circle. -/
lemma miquelT_mul_conj {a b c p : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hp : ‖p‖ = 1)
    (hσ : a + b + c ≠ p) (hσ2 : p * (a * b + b * c + c * a) - a * b * c ≠ 0) :
    miquelT a b c p * conj (miquelT a b c p) = 1 := by
  have ha0 := ne_zero_of_norm_one ha
  have hb0 := ne_zero_of_norm_one hb
  have hc0 := ne_zero_of_norm_one hc
  have hp0 := ne_zero_of_norm_one hp
  have hcomb : a⁻¹ + b⁻¹ + c⁻¹ - p⁻¹ =
      (p * (a * b + b * c + c * a) - a * b * c) / (a * b * c * p) := by
    field_simp [ha0, hb0, hc0, hp0]
    ring
  simp only [miquelT, map_add, map_sub, map_mul, map_div₀, conj_of_norm_one ha,
    conj_of_norm_one hb, conj_of_norm_one hc, conj_of_norm_one hp]
  rw [hcomb, div_div_eq_mul_div, mul_div_assoc', div_eq_iff hσ2, one_mul]
  field_simp [ha0, hb0, hc0, hp0, hσ]
  ring

lemma miquelT_norm {a b c p : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hp : ‖p‖ = 1)
    (hσ : a + b + c ≠ p) (hσ2 : p * (a * b + b * c + c * a) - a * b * c ≠ 0) :
    ‖miquelT a b c p‖ = 1 := by
  have h := miquelT_mul_conj ha hb hc hp hσ hσ2
  rw [Complex.mul_conj'] at h
  have h2 : ‖miquelT a b c p‖ ^ 2 = 1 := by exact_mod_cast h
  rcases sq_eq_one_iff.mp h2 with h3 | h3
  · exact h3
  · have := norm_nonneg (miquelT a b c p)
    linarith

/-- A factorization of `T - A₂`, showing that `T ≠ A₂` in the nondegenerate case. -/
lemma miquelT_sub_antip {a b c p : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hp : ‖p‖ = 1)
    (hσ : a + b + c ≠ p) :
    miquelT a b c p - antip a p =
      (p - a) * (a + b) * (a + c) / (p * (a + b + c - p)) := by
  have ha0 := ne_zero_of_norm_one ha
  have hb0 := ne_zero_of_norm_one hb
  have hc0 := ne_zero_of_norm_one hc
  have hp0 := ne_zero_of_norm_one hp
  simp only [miquelT, antip]
  field_simp [ha0, hb0, hc0, hp0, hσ]
  ring

lemma antip_ne_miquelT {a b c p : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hp : ‖p‖ = 1)
    (hpa : p ≠ a) (hab0 : a + b ≠ 0) (hca0 : a + c ≠ 0) (hσ : a + b + c ≠ p) :
    antip a p ≠ miquelT a b c p := by
  have hp0 := ne_zero_of_norm_one hp
  intro hEq
  have h0 : miquelT a b c p - antip a p = 0 := sub_eq_zero.mpr hEq.symm
  rw [miquelT_sub_antip ha hb hc hp hσ, div_eq_zero_iff] at h0
  rcases h0 with h0 | h0
  · rcases mul_eq_zero.mp h0 with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact hpa (sub_eq_zero.mp h2)
      · exact hab0 h2
    · exact hca0 h1
  · exact mul_ne_zero hp0 (sub_ne_zero.mpr hσ) h0

/-- A factorization of `A₁ - A₂`, showing that `A₁ ≠ A₂` is equivalent to
`p * (a*b + b*c + c*a) - a*b*c ≠ 0`. -/
lemma vtx_sub_antip {a b c p : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hp : ‖p‖ = 1)
    (hbc0 : b + c ≠ 0) :
    vtx a b c p - antip a p =
      (p - a) * (p * (a * b + b * c + c * a) - a * b * c) / (p ^ 2 * (b + c)) := by
  have ha0 := ne_zero_of_norm_one ha
  have hb0 := ne_zero_of_norm_one hb
  have hc0 := ne_zero_of_norm_one hc
  have hp0 := ne_zero_of_norm_one hp
  simp only [vtx, antip]
  field_simp [ha0, hb0, hc0, hp0, hbc0]
  ring

lemma pσ2_sub_ne {a b c p : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hp : ‖p‖ = 1)
    (hbc0 : b + c ≠ 0) (hA1A2 : vtx a b c p ≠ antip a p) :
    p * (a * b + b * c + c * a) - a * b * c ≠ 0 := by
  intro h
  apply hA1A2
  have h1 : vtx a b c p - antip a p = 0 := by
    rw [vtx_sub_antip ha hb hc hp hbc0, h]
    ring
  exact eq_of_sub_eq_zero h1

/-- The "parallel chords" identity, in cross-multiplied form. -/
lemma homothety_ab {a b c p : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hp : ‖p‖ = 1)
    (hbc0 : b + c ≠ 0) (hca0 : c + a ≠ 0) (hσ : a + b + c ≠ p) :
    (vtx b c a p - miquelT a b c p) * (antip a p - miquelT a b c p) =
      (vtx a b c p - miquelT a b c p) * (antip b p - miquelT a b c p) := by
  have ha0 := ne_zero_of_norm_one ha
  have hb0 := ne_zero_of_norm_one hb
  have hc0 := ne_zero_of_norm_one hc
  have hp0 := ne_zero_of_norm_one hp
  simp only [vtx, antip, miquelT]
  field_simp [ha0, hb0, hc0, hp0, hbc0, hca0, hσ]
  ring

lemma homothety_ac {a b c p : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hp : ‖p‖ = 1)
    (hbc0 : b + c ≠ 0) (hab0 : a + b ≠ 0) (hσ : a + b + c ≠ p) :
    (vtx c a b p - miquelT a b c p) * (antip a p - miquelT a b c p) =
      (vtx a b c p - miquelT a b c p) * (antip c p - miquelT a b c p) := by
  have ha0 := ne_zero_of_norm_one ha
  have hb0 := ne_zero_of_norm_one hb
  have hc0 := ne_zero_of_norm_one hc
  have hp0 := ne_zero_of_norm_one hp
  simp only [vtx, antip, miquelT]
  field_simp [ha0, hb0, hc0, hp0, hbc0, hab0, hσ]
  ring

/-- The homothety ratio is real (this is the collinearity of `A₁`, `A₂` and `T`,
in cross-multiplied form). -/
lemma hratio_conj {a b c p : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hp : ‖p‖ = 1)
    (hbc0 : b + c ≠ 0) (hσ : a + b + c ≠ p)
    (hσ2 : p * (a * b + b * c + c * a) - a * b * c ≠ 0)
    (hD : antip a p ≠ miquelT a b c p) :
    conj (hratio a b c p) = hratio a b c p := by
  have ha0 := ne_zero_of_norm_one ha
  have hb0 := ne_zero_of_norm_one hb
  have hc0 := ne_zero_of_norm_one hc
  have hp0 := ne_zero_of_norm_one hp
  have hcomb : a⁻¹ + b⁻¹ + c⁻¹ - p⁻¹ =
      (p * (a * b + b * c + c * a) - a * b * c) / (a * b * c * p) := by
    field_simp [ha0, hb0, hc0, hp0]
    ring
  have hσ2h : p * (b * (a + c) + a * c) - a * b * c ≠ 0 := by convert hσ2 using 1; ring
  have hcb0 : c + b ≠ 0 := by rwa [add_comm]
  have key :
      conj (vtx a b c p - miquelT a b c p) * (antip a p - miquelT a b c p) =
        (vtx a b c p - miquelT a b c p) * conj (antip a p - miquelT a b c p) := by
    simp only [map_sub, vtx, antip, miquelT, map_add, map_mul, map_div₀, map_pow,
      conj_of_norm_one ha, conj_of_norm_one hb, conj_of_norm_one hc, conj_of_norm_one hp]
    rw [hcomb]
    field_simp [ha0, hb0, hc0, hp0, hbc0, hcb0, hσ, hσ2h]
    ring
  have hD0 : antip a p - miquelT a b c p ≠ 0 := sub_ne_zero.mpr hD
  have hcj : conj (antip a p - miquelT a b c p) ≠ 0 := conj_ne_zero hD0
  rw [hratio, map_div₀, div_eq_div_iff hcj hD0]
  exact key

/-- Two circles `|z| = 1` and `|z - (1 - Λ) * T| = |Λ|` with `|T| = 1` and a real
ratio `Λ ≠ 1` meet only at `T`; this is the tangency conclusion. -/
lemma tangent_unique {Λ T : ℂ} (hΛ : conj Λ = Λ) (hΛ1 : Λ ≠ 1) (hT : ‖T‖ = 1)
    {z : ℂ} (hz : ‖z‖ = 1) (hzO : ‖z - (1 - Λ) * T‖ = ‖Λ‖) : z = T := by
  have hTsq : Complex.normSq T = 1 := by rw [Complex.normSq_eq_norm_sq, hT]; norm_num
  have hzsq : Complex.normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, hz]; norm_num
  have hΛre : (Λ.re : ℂ) = Λ := Complex.conj_eq_iff_re.mp hΛ
  have e2 : Complex.normSq (z - (1 - Λ) * T) = Complex.normSq Λ := by
    rw [Complex.normSq_eq_norm_sq, hzO, ← Complex.normSq_eq_norm_sq]
  have e3 : z - (1 - Λ) * T = (z - T) + Λ * T := by ring
  rw [e3, Complex.normSq_add, Complex.normSq_mul, hTsq, mul_one, map_mul, hΛ] at e2
  have e4 : (z - T) * (Λ * conj T) = (Λ.re : ℂ) * ((z - T) * conj T) := by
    conv_lhs => rw [← hΛre]
    ring
  rw [e4, Complex.re_ofReal_mul] at e2
  have e1 : Complex.normSq ((z - T) + T) = 1 := by rw [sub_add_cancel]; exact hzsq
  rw [Complex.normSq_add, hTsq] at e1
  set R := ((z - T) * conj T).re with hR
  set W := Complex.normSq (z - T) with hW
  have hR0 : R = 0 := by
    have h1 : (1 - Λ.re) * R = 0 := by linarith
    have hne : (1 : ℝ) - Λ.re ≠ 0 := by
      intro h0
      have hΛre1 : Λ.re = 1 := by linarith
      apply hΛ1
      rw [← hΛre, hΛre1]
      simp
    exact (mul_eq_zero.mp h1).resolve_left hne
  have hW0 : W = 0 := by linarith
  have hWT : Complex.normSq (z - T) = 0 := hW ▸ hW0
  have : z - T = 0 := Complex.normSq_eq_zero.mp hWT
  exact eq_of_sub_eq_zero this

/-- The assembled proof: the circumcircle of the reflected triangle is the image
of the unit circle under the homothety of ratio `hratio a b c p` centered at
`miquelT a b c p`, hence it is tangent to the unit circle. -/
lemma master (a b c p : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hp : ‖p‖ = 1)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (hab0 : a + b ≠ 0) (hbc0 : b + c ≠ 0) (hca0 : c + a ≠ 0)
    (hpa : p ≠ a)
    (hσ : a + b + c ≠ p)
    (hA1T : vtx a b c p ≠ miquelT a b c p)
    (hA1A2 : vtx a b c p ≠ antip a p) :
    ∃ A1 B1 C1 O : ℂ, ∃ r : ℝ,
      A1 ∈ reflLine c a (tanLine p) ∩ reflLine a b (tanLine p) ∧
      B1 ∈ reflLine a b (tanLine p) ∩ reflLine b c (tanLine p) ∧
      C1 ∈ reflLine b c (tanLine p) ∩ reflLine c a (tanLine p) ∧
      A1 ≠ B1 ∧ B1 ≠ C1 ∧ C1 ≠ A1 ∧ 0 < r ∧
      ‖A1 - O‖ = r ∧ ‖B1 - O‖ = r ∧ ‖C1 - O‖ = r ∧
      ∃ T : ℂ, ‖T‖ = 1 ∧ ‖T - O‖ = r ∧
        ∀ z : ℂ, ‖z‖ = 1 → ‖z - O‖ = r → z = T := by
  have ha0 := ne_zero_of_norm_one ha
  have hb0 := ne_zero_of_norm_one hb
  have hc0 := ne_zero_of_norm_one hc
  have hp0 := ne_zero_of_norm_one hp
  have hcb0 : c + b ≠ 0 := by rwa [add_comm]
  have hac0 : a + c ≠ 0 := by rwa [add_comm]
  have hba0 : b + a ≠ 0 := by rwa [add_comm]
  -- The homothety ratio and its basic properties.
  have hσ2 : p * (a * b + b * c + c * a) - a * b * c ≠ 0 :=
    pσ2_sub_ne ha hb hc hp hbc0 hA1A2
  have hD : antip a p ≠ miquelT a b c p := antip_ne_miquelT ha hb hc hp hpa hab0 hac0 hσ
  have hD0 : antip a p - miquelT a b c p ≠ 0 := sub_ne_zero.mpr hD
  have hΛcj : conj (hratio a b c p) = hratio a b c p :=
    hratio_conj ha hb hc hp hbc0 hσ hσ2 hD
  have hΛ0 : hratio a b c p ≠ 0 := div_ne_zero (sub_ne_zero.mpr hA1T) hD0
  have hΛ1 : hratio a b c p ≠ 1 := by
    rw [hratio, ne_eq, div_eq_iff hD0, one_mul, sub_left_inj]
    exact hA1A2
  -- The homothety sends `antip x p` to the corresponding vertex.
  have eA : vtx a b c p - miquelT a b c p =
      hratio a b c p * (antip a p - miquelT a b c p) := by
    rw [hratio]
    exact (div_mul_cancel₀ _ hD0).symm
  have eB : vtx b c a p - miquelT a b c p =
      hratio a b c p * (antip b p - miquelT a b c p) := by
    have h := homothety_ab ha hb hc hp hbc0 hca0 hσ
    rw [eA, mul_right_comm] at h
    exact mul_right_cancel₀ hD0 h
  have eC : vtx c a b p - miquelT a b c p =
      hratio a b c p * (antip c p - miquelT a b c p) := by
    have h := homothety_ac ha hb hc hp hbc0 hab0 hσ
    rw [eA, mul_right_comm] at h
    exact mul_right_cancel₀ hD0 h
  -- The image circle has center `(1 - Λ) * T` and radius `‖Λ‖`.
  have eOA : vtx a b c p - (1 - hratio a b c p) * miquelT a b c p =
      hratio a b c p * antip a p := by linear_combination eA
  have eOB : vtx b c a p - (1 - hratio a b c p) * miquelT a b c p =
      hratio a b c p * antip b p := by linear_combination eB
  have eOC : vtx c a b p - (1 - hratio a b c p) * miquelT a b c p =
      hratio a b c p * antip c p := by linear_combination eC
  have eOT : miquelT a b c p - (1 - hratio a b c p) * miquelT a b c p =
      hratio a b c p * miquelT a b c p := by ring
  have hnorma : ‖antip a p‖ = 1 := by rw [antip, norm_div, norm_pow, ha, hp]; norm_num
  have hnormb : ‖antip b p‖ = 1 := by rw [antip, norm_div, norm_pow, hb, hp]; norm_num
  have hnormc : ‖antip c p‖ = 1 := by rw [antip, norm_div, norm_pow, hc, hp]; norm_num
  have hnormT : ‖miquelT a b c p‖ = 1 := miquelT_norm ha hb hc hp hσ hσ2
  -- The three vertices are distinct.
  have hA2B2 : antip a p ≠ antip b p := by
    intro hEq
    rw [antip, antip, div_eq_div_iff hp0 hp0] at hEq
    have h2 : a ^ 2 = b ^ 2 := mul_right_cancel₀ hp0 hEq
    have h3 : (a + b) * (a - b) = 0 := by
      rw [← sq_sub_sq]
      exact sub_eq_zero.mpr h2
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact hab0 h4
    · exact hab (eq_of_sub_eq_zero h4)
  have hB2C2 : antip b p ≠ antip c p := by
    intro hEq
    rw [antip, antip, div_eq_div_iff hp0 hp0] at hEq
    have h2 : b ^ 2 = c ^ 2 := mul_right_cancel₀ hp0 hEq
    have h3 : (b + c) * (b - c) = 0 := by
      rw [← sq_sub_sq]
      exact sub_eq_zero.mpr h2
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact hbc0 h4
    · exact hbc (eq_of_sub_eq_zero h4)
  have hC2A2 : antip c p ≠ antip a p := by
    intro hEq
    rw [antip, antip, div_eq_div_iff hp0 hp0] at hEq
    have h2 : c ^ 2 = a ^ 2 := mul_right_cancel₀ hp0 hEq
    have h3 : (c + a) * (c - a) = 0 := by
      rw [← sq_sub_sq]
      exact sub_eq_zero.mpr h2
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact hca0 h4
    · exact hca (eq_of_sub_eq_zero h4)
  have hA1B1sub : vtx a b c p - vtx b c a p =
      hratio a b c p * (antip a p - antip b p) := by linear_combination eA - eB
  have hB1C1sub : vtx b c a p - vtx c a b p =
      hratio a b c p * (antip b p - antip c p) := by linear_combination eB - eC
  have hC1A1sub : vtx c a b p - vtx a b c p =
      hratio a b c p * (antip c p - antip a p) := by linear_combination eC - eA
  have hvAB : vtx a b c p ≠ vtx b c a p := by
    intro hEq
    have h0 : vtx a b c p - vtx b c a p = 0 := sub_eq_zero.mpr hEq
    rw [hA1B1sub] at h0
    exact mul_ne_zero hΛ0 (sub_ne_zero.mpr hA2B2) h0
  have hvBC : vtx b c a p ≠ vtx c a b p := by
    intro hEq
    have h0 : vtx b c a p - vtx c a b p = 0 := sub_eq_zero.mpr hEq
    rw [hB1C1sub] at h0
    exact mul_ne_zero hΛ0 (sub_ne_zero.mpr hB2C2) h0
  have hvCA : vtx c a b p ≠ vtx a b c p := by
    intro hEq
    have h0 : vtx c a b p - vtx a b c p = 0 := sub_eq_zero.mpr hEq
    rw [hC1A1sub] at h0
    exact mul_ne_zero hΛ0 (sub_ne_zero.mpr hC2A2) h0
  -- Each vertex lies on the two reflected lines it should.
  have hmA : vtx a b c p ∈ reflLine c a (tanLine p) ∩ reflLine a b (tanLine p) := by
    constructor
    · rw [reflLine_comm c a]
      have h := vtx_mem ha hc hb hp hcb0
      rwa [vtx_comm a c b p] at h
    · exact vtx_mem ha hb hc hp hbc0
  have hmB : vtx b c a p ∈ reflLine a b (tanLine p) ∩ reflLine b c (tanLine p) := by
    constructor
    · rw [reflLine_comm a b]
      have h := vtx_mem hb ha hc hp hac0
      rwa [vtx_comm b a c p] at h
    · exact vtx_mem hb hc ha hp hca0
  have hmC : vtx c a b p ∈ reflLine b c (tanLine p) ∩ reflLine c a (tanLine p) := by
    constructor
    · rw [reflLine_comm b c]
      have h := vtx_mem hc hb ha hp hba0
      rwa [vtx_comm c b a p] at h
    · exact vtx_mem hc ha hb hp hab0
  -- Assemble everything.
  exact ⟨vtx a b c p, vtx b c a p, vtx c a b p, (1 - hratio a b c p) * miquelT a b c p,
    ‖hratio a b c p‖, hmA, hmB, hmC, hvAB, hvBC, hvCA, norm_pos_iff.mpr hΛ0,
    by rw [eOA, norm_mul, hnorma, mul_one],
    by rw [eOB, norm_mul, hnormb, mul_one],
    by rw [eOC, norm_mul, hnormc, mul_one],
    miquelT a b c p, hnormT, by rw [eOT, norm_mul, hnormT, mul_one],
    fun z hz hzO => tangent_unique hΛcj hΛ1 hnormT hz hzO⟩

snip end

problem imo2011_p6
    (a b c p : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hp : ‖p‖ = 1)
    -- The triangle is acute (each angle has positive cosine).
    (hA : 0 < ((b - a) * conj (c - a)).re)
    (hB : 0 < ((c - b) * conj (a - b)).re)
    (hC : 0 < ((a - c) * conj (b - c)).re)
    -- Generic-position hypotheses on the tangent line.
    (hpa : p ≠ a)
    (hσ : a + b + c ≠ p)
    (hA1T : vtx a b c p ≠ miquelT a b c p)
    (hA1A2 : vtx a b c p ≠ antip a p) :
    ∃ A1 B1 C1 O : ℂ, ∃ r : ℝ,
      -- `A1` is the intersection point `ℓ_b ∩ ℓ_c`, etc.
      A1 ∈ reflLine c a (tanLine p) ∩ reflLine a b (tanLine p) ∧
      B1 ∈ reflLine a b (tanLine p) ∩ reflLine b c (tanLine p) ∧
      C1 ∈ reflLine b c (tanLine p) ∩ reflLine c a (tanLine p) ∧
      -- the three points determine a genuine triangle, and
      A1 ≠ B1 ∧ B1 ≠ C1 ∧ C1 ≠ A1 ∧ 0 < r ∧
      -- the circle with center `O` and radius `r` passes through `A1`, `B1`, `C1`,
      ‖A1 - O‖ = r ∧ ‖B1 - O‖ = r ∧ ‖C1 - O‖ = r ∧
      -- and it meets the circumcircle `Γ` (the unit circle) in a single point,
      -- i.e. the two circles are tangent.
      ∃ T : ℂ, ‖T‖ = 1 ∧ ‖T - O‖ = r ∧
        ∀ z : ℂ, ‖z‖ = 1 → ‖z - O‖ = r → z = T := by
  have hab : a ≠ b := by rintro rfl; simp at hA
  have hac : a ≠ c := by rintro rfl; simp at hA
  have hbc : b ≠ c := by rintro rfl; simp at hB
  have hab0 : a + b ≠ 0 := add_ne_zero_of_dot_pos ha hc hC
  have hbc0 : b + c ≠ 0 := add_ne_zero_of_dot_pos hb ha hA
  have hca0 : c + a ≠ 0 := add_ne_zero_of_dot_pos hc hb hB
  exact master a b c p ha hb hc hp hab hbc hac.symm hab0 hbc0 hca0 hpa hσ hA1T hA1A2

end Imo2011P6
