/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.RingTheory.SimpleRing.Principal
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 2023, Problem 6

Let ABC be a triangle with incenter I and excenters Ia, Ib, Ic opposite A, B, and C,
respectively. Given an arbitrary point D on the circumcircle of △ABC that does not lie on
any of the lines IIa, IbIc, or BC, suppose the circumcircles of △DIIa and △DIbIc intersect
at two distinct points D and F. If E is the intersection of lines DF and BC, prove that
∠BAD = ∠EAC.

## Formalization notes

We work in the complex plane; `ℂ` is a real inner product space, and `∠` is mathlib's
unoriented angle. By a similarity transformation (which preserves all the hypotheses and
the conclusion) we may assume that the circumcircle of `ABC` is the unit circle, and we
write `A = a²`, `B = b²`, `C = c²` and `D = d` with `|a| = |b| = |c| = |d| = 1`. It is a
standard fact (see e.g. EGMO, Lemma 6.19) that the square roots can be chosen so that the
incenter is `I = -(ab + bc + ca)` and the excenters are `Ia = ab - bc + ca`,
`Ib = ab + bc - ca`, `Ic = -ab + bc + ca`. Other choices of the square roots merely
permute these four points, in a way that leaves the unordered pair of circles
{circle(D, I, Ia), circle(D, Ib, Ic)} invariant, so no generality is lost by quantifying
over all choices of `a, b, c`.

The line `IIa` is the internal bisector of angle `A`, which meets the circumcircle at `A`
and at the midpoint `-bc` of arc `BC` not containing `A`; hence `D ∉ line IIa` iff
`d ∉ {a², -bc}`. Similarly line `IbIc` meets the circumcircle at `A` and `bc`, and line
`BC` meets the circumcircle at `B` and `C`. The hypotheses below record these conditions.

The circle through three points is encoded by the cross-ratio reality predicate `crc`.
The hypothesis `hne` says that the two circumcircles are distinct (otherwise they would
share all their points, not exactly two).

The computational heart of the proof is the following explicit formula for `E`:
`E = a² + (b² - a²)(c² - a²)/(d - a²)`, for which `(E - A)(D - A) = (B - A)(C - A)`
(hence `∠BAD = ∠EAC`), and which is shown to lie on the radical axis `DF` of the two
circles as well as on line `BC`.
-/

namespace Usa2023P6

open Complex ComplexConjugate

open scoped EuclideanGeometry

/-- `crc z₁ z₂ z₃ w = 0` holds iff `w` lies on the circle or line through `z₁, z₂, z₃`.
It is the multiplied-out polynomial form of
"(w - z₁)(z₃ - z₂) / ((w - z₂)(z₃ - z₁)) is real". -/
def crc (z₁ z₂ z₃ w : ℂ) : ℂ :=
    (w - z₁) * (z₃ - z₂) * conj ((w - z₂) * (z₃ - z₁))
      - conj ((w - z₁) * (z₃ - z₂)) * (w - z₂) * (z₃ - z₁)

snip begin

/-- The incenter, in the unit-circle parametrization. -/
def ptI (a b c : ℂ) : ℂ := -(a * b + b * c + c * a)

/-- The `A`-excenter, in the unit-circle parametrization. -/
def ptIa (a b c : ℂ) : ℂ := a * b - b * c + c * a

/-- The `B`-excenter, in the unit-circle parametrization. -/
def ptIb (a b c : ℂ) : ℂ := a * b + b * c - c * a

/-- The `C`-excenter, in the unit-circle parametrization. -/
def ptIc (a b c : ℂ) : ℂ := -a * b + b * c + c * a

/-- The explicit point `E` (the intersection of lines `DF` and `BC`). -/
noncomputable def ptE (a b c d : ℂ) : ℂ := a ^ 2 + (b ^ 2 - a ^ 2) * (c ^ 2 - a ^ 2) / (d - a ^ 2)

/-- The `z * conj z` coefficient of the circle equation `crc d (ptI a b c) (ptIa a b c)`. -/
def kk1 (a b c d : ℂ) : ℂ :=
    (ptIa a b c - ptI a b c) * conj (ptIa a b c - d)
      - conj (ptIa a b c - ptI a b c) * (ptIa a b c - d)

/-- The `z * conj z` coefficient of the circle equation `crc d (ptIb a b c) (ptIc a b c)`. -/
def kk2 (a b c d : ℂ) : ℂ :=
    (ptIc a b c - ptIb a b c) * conj (ptIc a b c - d)
      - conj (ptIc a b c - ptIb a b c) * (ptIc a b c - d)

/-- The `z` coefficient of the radical-axis equation of the two circles. -/
noncomputable def palpha (a b c d : ℂ) : ℂ :=
    -8 * (a ^ 2 - d) * (b - c) * (b + c)
      * (a ^ 2 * b ^ 2 * c ^ 2 - a ^ 2 * d ^ 2 - 2 * b ^ 2 * c ^ 2 * d + b ^ 2 * d ^ 2
          + c ^ 2 * d ^ 2) / (a ^ 2 * b ^ 3 * c ^ 3 * d ^ 2)

/-- The constant term of the radical-axis equation of the two circles. -/
noncomputable def pgamma (a b c d : ℂ) : ℂ :=
    8 * (a ^ 2 - d) * (b - c) * (b + c)
      * (a ^ 2 * b ^ 4 * c ^ 2 + a ^ 2 * b ^ 2 * c ^ 4 - a ^ 2 * b ^ 2 * c ^ 2 * d
          - a ^ 2 * d ^ 3 - b ^ 4 * c ^ 4 - b ^ 2 * c ^ 2 * d ^ 2 + b ^ 2 * d ^ 3
          + c ^ 2 * d ^ 3) / (a ^ 2 * b ^ 3 * c ^ 3 * d ^ 2)

variable (a b c d : ℂ)
variable (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hd : ‖d‖ = 1)

lemma conj_eq_inv (z : ℂ) (hz : ‖z‖ = 1) : conj z = z⁻¹ := (Complex.inv_eq_conj hz).symm

lemma ne_zero_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) : z ≠ 0 := by
  rintro rfl
  simp at hz

/-- If `x / y` is real (in cross-ratio form), then `x` is a real multiple of `y`. -/
lemma real_smul_of_cross_real {x y : ℂ} (hy : y ≠ 0)
    (h : x * conj y = conj x * y) : ∃ r : ℝ, x = r • y := by
  have hs : conj (x * conj y) = x * conj y := by
    rw [map_mul, conj_conj, ← h]
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.mp hs
  have hns : (Complex.normSq y : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Complex.normSq_pos.mpr hy))
  refine ⟨r / Complex.normSq y, ?_⟩
  have hcy : conj y * y = (Complex.normSq y : ℂ) := by
    rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.normSq_eq_norm_sq]
  calc x = (x * conj y) * y / (Complex.normSq y : ℂ) := by
          rw [mul_assoc, hcy, mul_div_cancel_right₀ _ hns]
    _ = (r / Complex.normSq y : ℝ) • y := by
          rw [Complex.real_smul, Complex.ofReal_div, ← hr]
          ring

/-- Three points with a real cross ratio are collinear. -/
lemma collinear_of_cross_real {p₁ p₂ p₃ : ℂ} (h12 : p₁ ≠ p₂)
    (h : (p₃ - p₁) * conj (p₂ - p₁) = conj (p₃ - p₁) * (p₂ - p₁)) :
    Collinear ℝ ({p₁, p₂, p₃} : Set ℂ) := by
  obtain ⟨r, hr⟩ := real_smul_of_cross_real (sub_ne_zero.mpr (Ne.symm h12)) h
  rw [collinear_iff_of_mem (show p₁ ∈ ({p₁, p₂, p₃} : Set ℂ) from Set.mem_insert p₁ _)]
  refine ⟨p₂ - p₁, fun p hp => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp [vadd_eq_add]⟩
  · exact ⟨r, by simp [vadd_eq_add, ← hr]⟩

/-- Collinear triples have a real cross ratio. -/
lemma cross_real_of_collinear {p₁ p₂ p₃ : ℂ}
    (h : Collinear ℝ ({p₁, p₂, p₃} : Set ℂ)) :
    (p₃ - p₁) * conj (p₂ - p₁) = conj (p₃ - p₁) * (p₂ - p₁) := by
  rw [collinear_iff_of_mem (show p₁ ∈ ({p₁, p₂, p₃} : Set ℂ) from Set.mem_insert p₁ _)] at h
  obtain ⟨v, hv⟩ := h
  obtain ⟨r₃, hr₃⟩ := hv p₃ (by simp)
  obtain ⟨r₂, hr₂⟩ := hv p₂ (by simp)
  have e₃ : p₃ - p₁ = r₃ • v := by rw [hr₃]; simp [vadd_eq_add]
  have e₂ : p₂ - p₁ = r₂ • v := by rw [hr₂]; simp [vadd_eq_add]
  rw [e₃, e₂]
  simp only [Complex.real_smul, map_mul, Complex.conj_ofReal]
  ring

/-- A point of the unit circle lying on a chord of the circle is an endpoint of the chord. -/
lemma eq_of_cross_real_chord {u v w : ℂ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hvw : v ≠ w) (h : (u - v) * conj (w - v) = conj (u - v) * (w - v)) :
    u = v ∨ u = w := by
  have hcu : conj u = u⁻¹ := conj_eq_inv u hu
  have hcv : conj v = v⁻¹ := conj_eq_inv v hv
  have hcw : conj w = w⁻¹ := conj_eq_inv w hw
  have hu0 : u ≠ 0 := ne_zero_of_norm_eq_one hu
  have hv0 : v ≠ 0 := ne_zero_of_norm_eq_one hv
  have hw0 : w ≠ 0 := ne_zero_of_norm_eq_one hw
  rw [map_sub, hcw, hcv, map_sub, hcu, hcv] at h
  have hid : -(u - v) * (w - v) * (u - w) / (u * v * w)
      = (u - v) * (w⁻¹ - v⁻¹) - (u⁻¹ - v⁻¹) * (w - v) := by
    field_simp [hu0, hv0, hw0]
    ring
  have h0 : (u - v) * (w - v) * (u - w) = 0 := by
    have hh : (u - v) * (w⁻¹ - v⁻¹) - (u⁻¹ - v⁻¹) * (w - v) = 0 := sub_eq_zero.mpr h
    rw [← hid] at hh
    have hden : u * v * w ≠ 0 := mul_ne_zero (mul_ne_zero hu0 hv0) hw0
    rcases div_eq_zero_iff.mp hh with h1 | h1
    · linear_combination -h1
    · exact absurd h1 hden
  rcases mul_eq_zero.mp h0 with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact Or.inl (sub_eq_zero.mp h2)
    · exact absurd (sub_eq_zero.mp h2) (Ne.symm hvw)
  · exact Or.inr (sub_eq_zero.mp h1)

/-- Elimination lemma: two vectors satisfying the same real-linear equation are
proportional over the reals (in cross-ratio form). -/
lemma coll_elim_linear {α u v : ℂ} (hα : α ≠ 0)
    (h1 : α * u + conj α * conj u = 0) (h2 : α * v + conj α * conj v = 0) :
    v * conj u = conj v * u := by
  have hαc : conj α ≠ 0 := by
    intro h0
    apply hα
    apply (starRingEnd ℂ).injective
    rw [h0, map_zero]
  have key : conj α * (v * conj u - conj v * u) = 0 := by
    linear_combination h1 * v - h2 * u
  rcases mul_eq_zero.mp key with h0 | h0
  · exact absurd h0 hαc
  · exact sub_eq_zero.mp h0

/-- The cosine bridge: if `u * v' = u' * v` (all nonzero) then the unoriented angles
between `u, v` and between `u', v'` agree. -/
lemma angle_bridge {u v u' v' : ℂ} (hu : u ≠ 0) (hv : v ≠ 0) (hu' : u' ≠ 0) (hv' : v' ≠ 0)
    (h : u * v' = u' * v) :
    InnerProductGeometry.angle u v = InnerProductGeometry.angle u' v' := by
  have hv_eq : v = u * v' / u' := by
    rw [h]
    field_simp [hu']
  have e1 : (v * conj u) * ((‖u'‖ : ℂ) ^ 2) = (v' * conj u') * ((‖u‖ : ℂ) ^ 2) := by
    rw [← Complex.mul_conj' u, ← Complex.mul_conj' u', hv_eq]
    field_simp [hu']
  have hrw : v * conj u = (‖u‖ ^ 2 / ‖u'‖ ^ 2 : ℝ) • (v' * conj u') := by
    have hu'0 : (‖u'‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hu')
    rw [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_pow]
    field_simp [hu'0]
    linear_combination e1
  have e1r : (v * conj u).re = ‖u‖ ^ 2 / ‖u'‖ ^ 2 * (v' * conj u').re := by
    rw [hrw, Complex.smul_re]
    simp
  have e2 : ‖u‖ * ‖v‖ = ‖u‖ * ‖u‖ * ‖v'‖ / ‖u'‖ := by
    rw [hv_eq, norm_div, norm_mul]
    ring
  have hU : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hU' : ‖u'‖ ≠ 0 := norm_ne_zero_iff.mpr hu'
  have hV' : ‖v'‖ ≠ 0 := norm_ne_zero_iff.mpr hv'
  unfold InnerProductGeometry.angle
  rw [Complex.inner, Complex.inner, e1r, e2]
  congr 1
  field_simp [hU, hU', hV']

lemma crc_self₁ (z₁ z₂ z₃ : ℂ) : crc z₁ z₂ z₃ z₁ = 0 := by
  simp [crc]

lemma crc_self₂ (z₁ z₂ z₃ : ℂ) : crc z₁ z₂ z₃ z₂ = 0 := by
  simp [crc]

lemma crc_self₃ (z₁ z₂ z₃ : ℂ) : crc z₁ z₂ z₃ z₃ = 0 := by
  unfold crc
  simp only [map_mul]
  ring

include ha hb hc hd in
/-- The explicit value of `kk1` (factored form). -/
lemma k1val : kk1 a b c d = -2 * (a ^ 2 - d) * (b + c) * (b * c + d) / (a * b * c * d) := by
  have hca : conj a = a⁻¹ := conj_eq_inv a ha
  have hcb : conj b = b⁻¹ := conj_eq_inv b hb
  have hcc : conj c = c⁻¹ := conj_eq_inv c hc
  have hcd : conj d = d⁻¹ := conj_eq_inv d hd
  have ha0 : a ≠ 0 := ne_zero_of_norm_eq_one ha
  have hb0 : b ≠ 0 := ne_zero_of_norm_eq_one hb
  have hc0 : c ≠ 0 := ne_zero_of_norm_eq_one hc
  have hd0 : d ≠ 0 := ne_zero_of_norm_eq_one hd
  simp only [kk1, ptI, ptIa, map_sub, map_add, map_mul, map_neg, hca, hcb, hcc, hcd]
  field_simp [ha0, hb0, hc0, hd0]
  ring

include ha hb hc hd in
/-- The explicit value of `kk2` (factored form). -/
lemma k2val : kk2 a b c d = 2 * (a ^ 2 - d) * (b - c) * (b * c - d) / (a * b * c * d) := by
  have hca : conj a = a⁻¹ := conj_eq_inv a ha
  have hcb : conj b = b⁻¹ := conj_eq_inv b hb
  have hcc : conj c = c⁻¹ := conj_eq_inv c hc
  have hcd : conj d = d⁻¹ := conj_eq_inv d hd
  have ha0 : a ≠ 0 := ne_zero_of_norm_eq_one ha
  have hb0 : b ≠ 0 := ne_zero_of_norm_eq_one hb
  have hc0 : c ≠ 0 := ne_zero_of_norm_eq_one hc
  have hd0 : d ≠ 0 := ne_zero_of_norm_eq_one hd
  simp only [kk2, ptIb, ptIc, map_sub, map_add, map_mul, map_neg, hca, hcb, hcc, hcd]
  field_simp [ha0, hb0, hc0, hd0]
  ring

include ha hb hc hd in
/-- `E` lies on line `BC` (in cross-ratio form). -/
lemma ebc (hdA : d ≠ a ^ 2) :
    (ptE a b c d - b ^ 2) * conj (c ^ 2 - b ^ 2)
      = conj (ptE a b c d - b ^ 2) * (c ^ 2 - b ^ 2) := by
  have hca : conj a = a⁻¹ := conj_eq_inv a ha
  have hcb : conj b = b⁻¹ := conj_eq_inv b hb
  have hcc : conj c = c⁻¹ := conj_eq_inv c hc
  have hcd : conj d = d⁻¹ := conj_eq_inv d hd
  have ha0 : a ≠ 0 := ne_zero_of_norm_eq_one ha
  have hb0 : b ≠ 0 := ne_zero_of_norm_eq_one hb
  have hc0 : c ≠ 0 := ne_zero_of_norm_eq_one hc
  have hd0 : d ≠ 0 := ne_zero_of_norm_eq_one hd
  have had2 : d - a ^ 2 ≠ 0 := sub_ne_zero.mpr hdA
  simp only [ptE, map_sub, map_add, map_mul, map_pow, map_div₀, hca, hcb, hcc, hcd]
  field_simp [ha0, hb0, hc0, hd0, had2]
  ring

include ha hb hc hd in
/-- The explicit value of `crc d I Ia E` (factored form). -/
lemma cr1E (hdA : d ≠ a ^ 2) :
    crc d (ptI a b c) (ptIa a b c) (ptE a b c d)
      = 4 * (a - b) * (a + b) * (a - c) * (a + c) * (b + c) * (b ^ 2 - d) * (c ^ 2 - d)
          * (b * c + d) / (a * b ^ 3 * c ^ 3 * d * (a ^ 2 - d)) := by
  have hca : conj a = a⁻¹ := conj_eq_inv a ha
  have hcb : conj b = b⁻¹ := conj_eq_inv b hb
  have hcc : conj c = c⁻¹ := conj_eq_inv c hc
  have hcd : conj d = d⁻¹ := conj_eq_inv d hd
  have ha0 : a ≠ 0 := ne_zero_of_norm_eq_one ha
  have hb0 : b ≠ 0 := ne_zero_of_norm_eq_one hb
  have hc0 : c ≠ 0 := ne_zero_of_norm_eq_one hc
  have hd0 : d ≠ 0 := ne_zero_of_norm_eq_one hd
  have had2 : d - a ^ 2 ≠ 0 := sub_ne_zero.mpr hdA
  simp only [crc, ptI, ptIa, ptE, map_sub, map_add, map_mul, map_neg, map_pow, map_div₀,
    hca, hcb, hcc, hcd]
  field_simp [ha0, hb0, hc0, hd0, had2]
  ring

include ha hb hc hd in
/-- The explicit value of `crc d Ib Ic E` (factored form). -/
lemma cr2E (hdA : d ≠ a ^ 2) :
    crc d (ptIb a b c) (ptIc a b c) (ptE a b c d)
      = -4 * (a - b) * (a + b) * (a - c) * (a + c) * (b - c) * (b ^ 2 - d) * (c ^ 2 - d)
          * (b * c - d) / (a * b ^ 3 * c ^ 3 * d * (a ^ 2 - d)) := by
  have hca : conj a = a⁻¹ := conj_eq_inv a ha
  have hcb : conj b = b⁻¹ := conj_eq_inv b hb
  have hcc : conj c = c⁻¹ := conj_eq_inv c hc
  have hcd : conj d = d⁻¹ := conj_eq_inv d hd
  have ha0 : a ≠ 0 := ne_zero_of_norm_eq_one ha
  have hb0 : b ≠ 0 := ne_zero_of_norm_eq_one hb
  have hc0 : c ≠ 0 := ne_zero_of_norm_eq_one hc
  have hd0 : d ≠ 0 := ne_zero_of_norm_eq_one hd
  have had2 : d - a ^ 2 ≠ 0 := sub_ne_zero.mpr hdA
  simp only [crc, ptIb, ptIc, ptE, map_sub, map_add, map_mul, map_neg, map_pow, map_div₀,
    hca, hcb, hcc, hcd]
  field_simp [ha0, hb0, hc0, hd0, had2]
  ring

include ha hb hc hd in
/-- The radical axis of the two circles: the difference of the two circle equations
(killed of the `z * conj z` term) is the affine-linear equation
`palpha * z + conj palpha * conj z + pgamma = 0`. -/
lemma Lexpand (w : ℂ) :
    crc d (ptI a b c) (ptIa a b c) w * kk2 a b c d
      - crc d (ptIb a b c) (ptIc a b c) w * kk1 a b c d
    = palpha a b c d * w + conj (palpha a b c d) * conj w + pgamma a b c d := by
  have hca : conj a = a⁻¹ := conj_eq_inv a ha
  have hcb : conj b = b⁻¹ := conj_eq_inv b hb
  have hcc : conj c = c⁻¹ := conj_eq_inv c hc
  have hcd : conj d = d⁻¹ := conj_eq_inv d hd
  have ha0 : a ≠ 0 := ne_zero_of_norm_eq_one ha
  have hb0 : b ≠ 0 := ne_zero_of_norm_eq_one hb
  have hc0 : c ≠ 0 := ne_zero_of_norm_eq_one hc
  have hd0 : d ≠ 0 := ne_zero_of_norm_eq_one hd
  simp only [crc, kk1, kk2, ptI, ptIa, ptIb, ptIc, palpha, pgamma,
    map_sub, map_add, map_mul, map_neg, map_pow, map_div₀, Complex.conj_ofNat, hca, hcb, hcc, hcd]
  field_simp [ha0, hb0, hc0, hd0]
  ring

include ha hb hc hd in
lemma k1_ne (hdA : d ≠ a ^ 2) (hbc : b ^ 2 ≠ c ^ 2) (hdM : d ≠ -(b * c)) :
    kk1 a b c d ≠ 0 := by
  rw [k1val a b c d ha hb hc hd]
  have hbc0 : b + c ≠ 0 := by
    intro h0
    have h1 : b = -c := by linear_combination h0
    have h2 : b ^ 2 = c ^ 2 := by rw [h1]; ring
    exact hbc h2
  have hbcd : b * c + d ≠ 0 := by
    intro h0
    have h1 : d = -(b * c) := by linear_combination h0
    exact hdM h1
  have had : a ^ 2 - d ≠ 0 := sub_ne_zero.mpr (Ne.symm hdA)
  have ha0 : a ≠ 0 := ne_zero_of_norm_eq_one ha
  have hb0 : b ≠ 0 := ne_zero_of_norm_eq_one hb
  have hc0 : c ≠ 0 := ne_zero_of_norm_eq_one hc
  have hd0 : d ≠ 0 := ne_zero_of_norm_eq_one hd
  apply div_ne_zero
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) had) hbc0) hbcd
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero ha0 hb0) hc0) hd0

include ha hb hc hd in
lemma k2_ne (hdA : d ≠ a ^ 2) (hbc : b ^ 2 ≠ c ^ 2) (hdP : d ≠ b * c) :
    kk2 a b c d ≠ 0 := by
  rw [k2val a b c d ha hb hc hd]
  have hbc0 : b - c ≠ 0 := by
    intro h0
    have h1 : b = c := by linear_combination h0
    exact hbc (by rw [h1])
  have hbcd : b * c - d ≠ 0 := sub_ne_zero.mpr (Ne.symm hdP)
  have had : a ^ 2 - d ≠ 0 := sub_ne_zero.mpr (Ne.symm hdA)
  have ha0 : a ≠ 0 := ne_zero_of_norm_eq_one ha
  have hb0 : b ≠ 0 := ne_zero_of_norm_eq_one hb
  have hc0 : c ≠ 0 := ne_zero_of_norm_eq_one hc
  have hd0 : d ≠ 0 := ne_zero_of_norm_eq_one hd
  apply div_ne_zero
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) had) hbc0) hbcd
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero ha0 hb0) hc0) hd0

include ha hb hc hd in
/-- The radical-axis equation is nontrivial: its `z`-coefficient is nonzero.
This is where the hypothesis that the two circles are distinct is used. -/
lemma alpha_ne (hdA : d ≠ a ^ 2) (hbc : b ^ 2 ≠ c ^ 2) (hdP : d ≠ b * c)
    (hne : ¬ (crc d (ptI a b c) (ptIa a b c) (ptIb a b c) = 0 ∧
              crc d (ptI a b c) (ptIa a b c) (ptIc a b c) = 0)) :
    palpha a b c d ≠ 0 := by
  by_contra hα
  have hγ : pgamma a b c d = 0 := by
    have h0 := Lexpand a b c d ha hb hc hd d
    simp only [hα, crc_self₁, map_zero, zero_mul, add_zero, sub_zero, zero_add]
      at h0
    exact h0.symm
  have hkk2 : kk2 a b c d ≠ 0 := k2_ne a b c d ha hb hc hd hdA hbc hdP
  have hIb : crc d (ptI a b c) (ptIa a b c) (ptIb a b c) = 0 := by
    have h0 := Lexpand a b c d ha hb hc hd (ptIb a b c)
    simp only [hα, hγ, crc_self₂, map_zero, zero_mul, add_zero, sub_zero]
      at h0
    exact (mul_eq_zero.mp h0).resolve_right hkk2
  have hIc : crc d (ptI a b c) (ptIa a b c) (ptIc a b c) = 0 := by
    have h0 := Lexpand a b c d ha hb hc hd (ptIc a b c)
    simp only [hα, hγ, crc_self₃, map_zero, zero_mul, add_zero, sub_zero]
      at h0
    exact (mul_eq_zero.mp h0).resolve_right hkk2
  exact hne ⟨hIb, hIc⟩

/-- `D` lies on the radical axis (trivially: it lies on both circles). -/
lemma Llin_d :
    crc d (ptI a b c) (ptIa a b c) d * kk2 a b c d
      - crc d (ptIb a b c) (ptIc a b c) d * kk1 a b c d = 0 := by
  rw [crc_self₁, crc_self₁]
  ring

/-- `F` lies on the radical axis (it lies on both circles). -/
lemma Llin_F {F : ℂ}
    (hF1 : crc d (ptI a b c) (ptIa a b c) F = 0)
    (hF2 : crc d (ptIb a b c) (ptIc a b c) F = 0) :
    crc d (ptI a b c) (ptIa a b c) F * kk2 a b c d
      - crc d (ptIb a b c) (ptIc a b c) F * kk1 a b c d = 0 := by
  rw [hF1, hF2]
  ring

include ha hb hc hd in
/-- `E` lies on the radical axis: the main algebraic identity. -/
lemma Llin_E (hdA : d ≠ a ^ 2) :
    crc d (ptI a b c) (ptIa a b c) (ptE a b c d) * kk2 a b c d
      - crc d (ptIb a b c) (ptIc a b c) (ptE a b c d) * kk1 a b c d = 0 := by
  rw [cr1E a b c d ha hb hc hd hdA, cr2E a b c d ha hb hc hd hdA,
    k1val a b c d ha hb hc hd, k2val a b c d ha hb hc hd]
  have ha0 : a ≠ 0 := ne_zero_of_norm_eq_one ha
  have hb0 : b ≠ 0 := ne_zero_of_norm_eq_one hb
  have hc0 : c ≠ 0 := ne_zero_of_norm_eq_one hc
  have hd0 : d ≠ 0 := ne_zero_of_norm_eq_one hd
  have had2 : a ^ 2 - d ≠ 0 := sub_ne_zero.mpr (Ne.symm hdA)
  field_simp [ha0, hb0, hc0, hd0, had2]
  ring

lemma eA : ptE a b c d - a ^ 2 = (b ^ 2 - a ^ 2) * (c ^ 2 - a ^ 2) / (d - a ^ 2) := by
  simp [ptE]

lemma eA_ne (hab : a ^ 2 ≠ b ^ 2) (hca2 : c ^ 2 ≠ a ^ 2) (hdA : d ≠ a ^ 2) :
    ptE a b c d - a ^ 2 ≠ 0 := by
  rw [eA a b c d]
  exact div_ne_zero
    (mul_ne_zero (sub_ne_zero.mpr (Ne.symm hab)) (sub_ne_zero.mpr hca2))
    (sub_ne_zero.mpr hdA)

/-- The conclusion `∠BAD = ∠EAC` for the explicit point `E`. -/
lemma angle_E0 (hab : a ^ 2 ≠ b ^ 2) (hca2 : c ^ 2 ≠ a ^ 2) (hdA : d ≠ a ^ 2) :
    ∠ (b ^ 2) (a ^ 2) d = ∠ (ptE a b c d) (a ^ 2) (c ^ 2) := by
  have hub : (b : ℂ) ^ 2 - a ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hvd : d - a ^ 2 ≠ 0 := sub_ne_zero.mpr hdA
  have hvc : c ^ 2 - a ^ 2 ≠ 0 := sub_ne_zero.mpr hca2
  have hue : ptE a b c d - a ^ 2 ≠ 0 := eA_ne a b c d hab hca2 hdA
  have hmul : (b ^ 2 - a ^ 2) * (c ^ 2 - a ^ 2) = (ptE a b c d - a ^ 2) * (d - a ^ 2) := by
    rw [eA a b c d]
    field_simp [hvd]
  have h := angle_bridge hub hvd hue hvc hmul
  unfold EuclideanGeometry.angle
  simp only [vsub_eq_sub]
  exact h

include ha hb hc hd in
/-- The explicit point `E` lies on line `BC`. -/
lemma coll_BC_E0 (hbc : b ^ 2 ≠ c ^ 2) (hdA : d ≠ a ^ 2) :
    Collinear ℝ ({b ^ 2, c ^ 2, ptE a b c d} : Set ℂ) :=
  collinear_of_cross_real hbc (ebc a b c d ha hb hc hd hdA)

include ha hb hc hd in
/-- The explicit point `E` lies on line `DF` (the radical axis). -/
lemma coll_dF_E0 {F : ℂ} (hFD : F ≠ d)
    (hF1 : crc d (ptI a b c) (ptIa a b c) F = 0)
    (hF2 : crc d (ptIb a b c) (ptIc a b c) F = 0)
    (hdA : d ≠ a ^ 2) (hbc : b ^ 2 ≠ c ^ 2) (hdP : d ≠ b * c)
    (hne : ¬ (crc d (ptI a b c) (ptIa a b c) (ptIb a b c) = 0 ∧
              crc d (ptI a b c) (ptIa a b c) (ptIc a b c) = 0)) :
    Collinear ℝ ({d, F, ptE a b c d} : Set ℂ) := by
  have hd0 : crc d (ptI a b c) (ptIa a b c) d * kk2 a b c d
      - crc d (ptIb a b c) (ptIc a b c) d * kk1 a b c d
      = palpha a b c d * d + conj (palpha a b c d) * conj d + pgamma a b c d :=
    Lexpand a b c d ha hb hc hd d
  rw [Llin_d a b c d] at hd0
  have hF0 : crc d (ptI a b c) (ptIa a b c) F * kk2 a b c d
      - crc d (ptIb a b c) (ptIc a b c) F * kk1 a b c d
      = palpha a b c d * F + conj (palpha a b c d) * conj F + pgamma a b c d :=
    Lexpand a b c d ha hb hc hd F
  rw [Llin_F a b c d hF1 hF2] at hF0
  have hE0 : crc d (ptI a b c) (ptIa a b c) (ptE a b c d) * kk2 a b c d
      - crc d (ptIb a b c) (ptIc a b c) (ptE a b c d) * kk1 a b c d
      = palpha a b c d * (ptE a b c d) + conj (palpha a b c d) * conj (ptE a b c d)
        + pgamma a b c d :=
    Lexpand a b c d ha hb hc hd (ptE a b c d)
  rw [Llin_E a b c d ha hb hc hd hdA] at hE0
  have hα : palpha a b c d ≠ 0 := alpha_ne a b c d ha hb hc hd hdA hbc hdP hne
  have hu : palpha a b c d * (F - d) + conj (palpha a b c d) * conj (F - d) = 0 := by
    rw [map_sub]
    linear_combination hd0 - hF0
  have hv : palpha a b c d * (ptE a b c d - d) + conj (palpha a b c d) * conj (ptE a b c d - d)
      = 0 := by
    rw [map_sub]
    linear_combination hd0 - hE0
  have hcross := coll_elim_linear hα hu hv
  exact collinear_of_cross_real (Ne.symm hFD) hcross

include ha hb hc hd in
/-- Uniqueness: any point lying on both lines `DF` and `BC` equals the explicit `E`. -/
lemma eq_E0 {F E : ℂ} (hFD : F ≠ d)
    (hF1 : crc d (ptI a b c) (ptIa a b c) F = 0)
    (hF2 : crc d (ptIb a b c) (ptIc a b c) F = 0)
    (hdA : d ≠ a ^ 2) (hdB : d ≠ b ^ 2) (hdC : d ≠ c ^ 2)
    (hbc : b ^ 2 ≠ c ^ 2) (hdP : d ≠ b * c)
    (hne : ¬ (crc d (ptI a b c) (ptIa a b c) (ptIb a b c) = 0 ∧
              crc d (ptI a b c) (ptIa a b c) (ptIc a b c) = 0))
    (hE1 : Collinear ℝ ({d, F, E} : Set ℂ))
    (hE2 : Collinear ℝ ({b ^ 2, c ^ 2, E} : Set ℂ)) :
    E = ptE a b c d := by
  have e1 := cross_real_of_collinear hE1
  have e2 := cross_real_of_collinear hE2
  have e01 : (ptE a b c d - d) * conj (F - d) = conj (ptE a b c d - d) * (F - d) :=
    cross_real_of_collinear (coll_dF_E0 a b c d ha hb hc hd hFD hF1 hF2 hdA hbc hdP hne)
  have e02 : (ptE a b c d - b ^ 2) * conj (c ^ 2 - b ^ 2)
      = conj (ptE a b c d - b ^ 2) * (c ^ 2 - b ^ 2) := ebc a b c d ha hb hc hd hdA
  have d1 : (E - ptE a b c d) * conj (F - d) = conj (E - ptE a b c d) * (F - d) := by
    simp only [map_sub] at e1 e01 ⊢
    linear_combination e1 - e01
  have d2 : (E - ptE a b c d) * conj (c ^ 2 - b ^ 2)
      = conj (E - ptE a b c d) * (c ^ 2 - b ^ 2) := by
    simp only [map_sub] at e2 e02 ⊢
    linear_combination e2 - e02
  by_cases hpar : (F - d) * conj (c ^ 2 - b ^ 2) = conj (F - d) * (c ^ 2 - b ^ 2)
  · exfalso
    -- lines `DF` and `BC` are parallel and share `ptE`, so `d` lies on line `BC`
    obtain ⟨r, hr⟩ := real_smul_of_cross_real (sub_ne_zero.mpr (Ne.symm hbc)) hpar
    have hr0 : r ≠ 0 := by
      intro hr0
      rw [hr0, zero_smul] at hr
      exact hFD (sub_eq_zero.mp hr)
    have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr0
    rw [hr, Complex.real_smul, map_mul, Complex.conj_ofReal] at e01
    have key : (r : ℂ) * ((ptE a b c d - d) * conj (c ^ 2 - b ^ 2))
        = (r : ℂ) * (conj (ptE a b c d - d) * (c ^ 2 - b ^ 2)) := by
      linear_combination e01
    have e01' : (ptE a b c d - d) * conj (c ^ 2 - b ^ 2)
        = conj (ptE a b c d - d) * (c ^ 2 - b ^ 2) := mul_left_cancel₀ hrc key
    have h1 : (d - ptE a b c d) * conj (c ^ 2 - b ^ 2)
        = conj (d - ptE a b c d) * (c ^ 2 - b ^ 2) := by
      have hneg : d - ptE a b c d = -(ptE a b c d - d) := by ring
      rw [hneg, map_neg]
      linear_combination -e01'
    have h3 : (d - b ^ 2) * conj (c ^ 2 - b ^ 2) = conj (d - b ^ 2) * (c ^ 2 - b ^ 2) := by
      have hsplit : d - b ^ 2 = (d - ptE a b c d) + (ptE a b c d - b ^ 2) := by ring
      rw [hsplit, map_add]
      linear_combination h1 + e02
    have hb2 : ‖(b : ℂ) ^ 2‖ = 1 := by rw [norm_pow, hb]; norm_num
    have hc2 : ‖(c : ℂ) ^ 2‖ = 1 := by rw [norm_pow, hc]; norm_num
    rcases eq_of_cross_real_chord hd hb2 hc2 hbc h3 with h0 | h0
    · exact hdB h0
    · exact hdC h0
  · have hbr : conj (F - d) * (c ^ 2 - b ^ 2) - conj (c ^ 2 - b ^ 2) * (F - d) ≠ 0 := by
      intro hbr0
      apply hpar
      have h0 := sub_eq_zero.mp hbr0
      rw [h0]
      ring
    have hδ : (E - ptE a b c d)
        * (conj (F - d) * (c ^ 2 - b ^ 2) - conj (c ^ 2 - b ^ 2) * (F - d)) = 0 := by
      linear_combination d1 * (c ^ 2 - b ^ 2) - d2 * (F - d)
    have h0 : E - ptE a b c d = 0 := (mul_eq_zero.mp hδ).resolve_right hbr
    linear_combination h0

snip end

problem usa2023_p6
    (a b c d F : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hd : ‖d‖ = 1)
    (hab : a ^ 2 ≠ b ^ 2) (hbc : b ^ 2 ≠ c ^ 2) (hca : c ^ 2 ≠ a ^ 2)
    (hdA : d ≠ a ^ 2) (hdB : d ≠ b ^ 2) (hdC : d ≠ c ^ 2)
    (hdP : d ≠ b * c) (hdM : d ≠ -(b * c))
    (hFD : F ≠ d)
    (hF1 : crc d (-(a * b + b * c + c * a)) (a * b - b * c + c * a) F = 0)
    (hF2 : crc d (a * b + b * c - c * a) (-a * b + b * c + c * a) F = 0)
    (hne : ¬ (crc d (-(a * b + b * c + c * a)) (a * b - b * c + c * a)
                (a * b + b * c - c * a) = 0 ∧
              crc d (-(a * b + b * c + c * a)) (a * b - b * c + c * a)
                (-a * b + b * c + c * a) = 0))
    (E : ℂ)
    (hE1 : Collinear ℝ ({d, F, E} : Set ℂ))
    (hE2 : Collinear ℝ ({b ^ 2, c ^ 2, E} : Set ℂ)) :
    ∠ (b ^ 2) (a ^ 2) d = ∠ E (a ^ 2) (c ^ 2) := by
  have _hkk1 := k1_ne a b c d ha hb hc hd hdA hbc hdM
  have hE : E = ptE a b c d :=
    eq_E0 a b c d ha hb hc hd hFD hF1 hF2 hdA hdB hdC hbc hdP hne hE1 hE2
  rw [hE]
  exact angle_E0 a b c d hab hca hdA

end Usa2023P6
