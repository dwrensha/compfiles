/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.Geometry.Euclidean.Projection
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 2010, Problem 1

Let AXYZB be a convex pentagon inscribed in a semicircle of diameter AB.
Denote by P, Q, R, S the feet of the perpendiculars from Y onto lines
AX, BX, AZ, BZ, respectively. Prove that the acute angle formed by lines
PQ and RS is half the size of ∠XOZ, where O is the midpoint of segment AB.
-/

namespace Usa2010P1

open scoped Real InnerProductSpace ComplexConjugate

/-- The foot of the perpendicular from a point `p` of the complex plane to the
line through the points `a` and `b`. -/
noncomputable def foot (a b p : ℂ) : ℂ :=
  EuclideanGeometry.orthogonalProjection (line[ℝ, a, b]) p

/-- The acute angle formed by two lines with direction vectors `u` and `v`. -/
noncomputable def acuteAngle (u v : ℂ) : ℝ :=
  min (InnerProductGeometry.angle u v) (Real.pi - InnerProductGeometry.angle u v)

snip begin

/-- On the unit circle, complex conjugation agrees with inversion. -/
lemma conj_eq_inv_of_norm_eq_one (w : ℂ) (h : ‖w‖ = 1) : conj w = w⁻¹ := by
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, h]
  simp

/-- Explicit formula for the foot of the perpendicular from a point `y` of the unit
circle to the chord through two points `a ≠ b` of the unit circle. -/
lemma foot_eq_of_norm_one {a b y : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hy : ‖y‖ = 1)
    (hab : a ≠ b) :
    foot a b y = (a + b + y - a * b * conj y) / 2 := by
  have ha0 : a ≠ 0 := norm_ne_zero_iff.mp (by rw [ha]; norm_num)
  have hb0 : b ≠ 0 := norm_ne_zero_iff.mp (by rw [hb]; norm_num)
  have hy0 : y ≠ 0 := norm_ne_zero_iff.mp (by rw [hy]; norm_num)
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have haconj : conj a = a⁻¹ := conj_eq_inv_of_norm_eq_one a ha
  have hbconj : conj b = b⁻¹ := conj_eq_inv_of_norm_eq_one b hb
  have hyconj : conj y = y⁻¹ := conj_eq_inv_of_norm_eq_one y hy
  set p₀ : ℂ := (a + b + y - a * b * conj y) / 2 with hp₀
  set t : ℂ := (y - a) * (y + b) / (2 * y * (b - a)) with hteq
  -- the parameter `t` writing `p₀` as `a + t (b - a)` is real
  have ht : conj t = t := by
    rw [hteq]
    simp only [map_div₀, map_mul, map_sub, map_add, map_ofNat, haconj, hbconj, hyconj]
    field_simp
    ring
  have htre : (t.re : ℂ) = t := Complex.conj_eq_iff_re.mp ht
  have hp₀eq : p₀ = (t.re : ℂ) * (b - a) + a := by
    rw [htre, hteq, hp₀, hyconj]
    field_simp
    ring
  -- `p₀` lies on the line through `a` and `b`
  have hp₀mem : p₀ ∈ line[ℝ, a, b] := by
    have hdir : (b -ᵥ a : ℂ) ∈ (line[ℝ, a, b]).direction := by
      rw [direction_affineSpan, vectorSpan_pair_rev]
      exact Submodule.mem_span_singleton_self _
    have hmem : t.re • (b -ᵥ a) +ᵥ a ∈ line[ℝ, a, b] :=
      AffineSubspace.vadd_mem_of_mem_direction (Submodule.smul_mem _ t.re hdir)
        (left_mem_affineSpan_pair ℝ a b)
    rwa [vadd_eq_add, vsub_eq_sub, Complex.real_smul, ← hp₀eq] at hmem
  -- `y - p₀` is orthogonal to the direction of the line
  have hp₀orth : (y -ᵥ p₀ : ℂ) ∈ (line[ℝ, a, b]).directionᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    rw [direction_affineSpan, vectorSpan_pair] at hu
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hu
    rw [← hr, real_inner_smul_left]
    suffices h : ⟪(a -ᵥ b : ℂ), (y -ᵥ p₀ : ℂ)⟫_ℝ = 0 by rw [h, mul_zero]
    rw [vsub_eq_sub, vsub_eq_sub, Complex.inner]
    have key : (y - p₀) * conj (a - b) + conj ((y - p₀) * conj (a - b)) = 0 := by
      simp only [hp₀, map_mul, map_sub, map_add, map_div₀, map_ofNat, haconj, hbconj, hyconj,
        map_inv₀, inv_inv]
      field_simp
      ring
    have hre := Complex.add_conj ((y - p₀) * conj (a - b))
    rw [key] at hre
    have h0 : ((y - p₀) * conj (a - b)).re = 0 := by
      have h1 : 2 * ((y - p₀) * conj (a - b)).re = 0 := Complex.ofReal_eq_zero.mp hre.symm
      exact (mul_eq_zero.mp h1).resolve_left two_ne_zero
    exact h0
  unfold foot
  rw [EuclideanGeometry.coe_orthogonalProjection_eq_iff_mem]
  exact ⟨hp₀mem, hp₀orth⟩

/-- The feet of the perpendiculars from `y` to the lines through `-1, x` and through
`1, x` differ by `1 - x * conj y`. -/
lemma foot_one_sub_foot_neg_one {x y : ℂ} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxim : 0 < x.im) :
    foot 1 x y - foot (-1) x y = 1 - x * conj y := by
  have h1 : (1 : ℂ) ≠ x := by
    intro h
    rw [← h] at hxim
    simp at hxim
  have h2 : (-1 : ℂ) ≠ x := by
    intro h
    rw [← h] at hxim
    simp at hxim
  rw [foot_eq_of_norm_one (by simp) hx hy h1, foot_eq_of_norm_one (by simp) hx hy h2]
  ring

/-- The key trigonometric identity in complex form:
`1 - exp (t I) = 2 sin(t/2) · (-I) · exp (t/2 I)`. -/
lemma one_sub_exp_mul_I (t : ℝ) :
    1 - Complex.exp ((t : ℂ) * Complex.I)
      = ((2 * Real.sin (t / 2) : ℝ) : ℂ) * (-Complex.I)
        * Complex.exp (((t / 2 : ℝ) : ℂ) * Complex.I) := by
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im,
      Complex.I_re, Complex.I_im]
    have h := Real.cos_two_mul_eq_one_sub (t / 2)
    rw [show 2 * (t / 2) = t from by ring] at h
    ring_nf at h ⊢
    linarith
  · simp only [Complex.sub_im, Complex.one_im, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im,
      Complex.I_re, Complex.I_im]
    have h := Real.sin_two_mul (t / 2)
    rw [show 2 * (t / 2) = t from by ring] at h
    ring_nf at h ⊢
    linarith

/-- A point of the unit circle with positive imaginary part has argument in `(0, π)`. -/
lemma arg_mem_Ioo_of_norm_eq_one {w : ℂ} (hw : ‖w‖ = 1) (hwim : 0 < w.im) :
    0 < Complex.arg w ∧ Complex.arg w < Real.pi := by
  have hsin : Real.sin (Complex.arg w) = w.im := by rw [Complex.sin_arg, hw, div_one]
  have hmem := Complex.arg_mem_Ioc w
  constructor
  · by_contra hcon
    push Not at hcon
    have hle : Real.sin (Complex.arg w) ≤ 0 :=
      Real.sin_nonpos_of_nonpos_of_neg_pi_le hcon hmem.1.le
    rw [hsin] at hle
    linarith
  · by_contra hcon
    push Not at hcon
    have heq : Complex.arg w = Real.pi := le_antisymm hmem.2 hcon
    rw [heq, Real.sin_pi] at hsin
    linarith

/-- The angle computation at the heart of the problem. With `x = exp (α I)`,
`y = exp (β I)`, `z = exp (γ I)` and `0 < γ < β < α < π`, the acute angle formed by
the lines `PQ` and `RS` equals `(α - γ) / 2`, which is half of `∠XOZ = α - γ`. -/
lemma acuteAngle_eq_of_exp (α β γ : ℝ) (hγ : 0 < γ) (hγβ : γ < β) (hβα : β < α)
    (hα : α < Real.pi) :
    acuteAngle
      (foot 1 (Complex.exp (α * Complex.I)) (Complex.exp (β * Complex.I))
        - foot (-1) (Complex.exp (α * Complex.I)) (Complex.exp (β * Complex.I)))
      (foot 1 (Complex.exp (γ * Complex.I)) (Complex.exp (β * Complex.I))
        - foot (-1) (Complex.exp (γ * Complex.I)) (Complex.exp (β * Complex.I)))
    = InnerProductGeometry.angle (Complex.exp (α * Complex.I)) (Complex.exp (γ * Complex.I)) / 2 := by
  have hαγ : 0 < α - γ := by linarith
  have hαγπ : α - γ < Real.pi := by linarith
  set x : ℂ := Complex.exp (α * Complex.I) with hx
  set y : ℂ := Complex.exp (β * Complex.I) with hy
  set z : ℂ := Complex.exp (γ * Complex.I) with hz
  have hnx : ‖x‖ = 1 := by rw [hx, Complex.norm_exp_ofReal_mul_I]
  have hny : ‖y‖ = 1 := by rw [hy, Complex.norm_exp_ofReal_mul_I]
  have hnz : ‖z‖ = 1 := by rw [hz, Complex.norm_exp_ofReal_mul_I]
  have himx : 0 < x.im := by
    rw [hx, Complex.exp_ofReal_mul_I_im]
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) hα
  have himy : 0 < y.im := by
    rw [hy, Complex.exp_ofReal_mul_I_im]
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have himz : 0 < z.im := by
    rw [hz, Complex.exp_ofReal_mul_I_im]
    exact Real.sin_pos_of_pos_of_lt_pi hγ (by linarith)
  -- conjugates of the points on the unit circle
  have hconjy : conj y = Complex.exp (-(β * Complex.I)) := by
    rw [hy, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
  have hconjx : conj x = Complex.exp (-(α * Complex.I)) := by
    rw [hx, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
  -- the direction vectors of the lines `PQ` and `RS`
  have hsub1 : foot 1 x y - foot (-1) x y = 1 - x * conj y :=
    foot_one_sub_foot_neg_one hnx hny himx
  have hsub2 : foot 1 z y - foot (-1) z y = 1 - z * conj y :=
    foot_one_sub_foot_neg_one hnz hny himz
  -- each direction vector is a positive real multiple of an explicit unit vector
  set U : ℂ := -Complex.I * Complex.exp ((((α - β) / 2 : ℝ) : ℂ) * Complex.I) with hU
  set V : ℂ := Complex.I * Complex.exp ((((γ - β) / 2 : ℝ) : ℂ) * Complex.I) with hV
  have hsin1 : 0 < 2 * Real.sin ((α - β) / 2) := by
    have h : 0 < Real.sin ((α - β) / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    linarith
  have hsin2 : 0 < -2 * Real.sin ((γ - β) / 2) := by
    have h : Real.sin ((γ - β) / 2) < 0 :=
      Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
    linarith
  have hqp : foot 1 x y - foot (-1) x y = (2 * Real.sin ((α - β) / 2)) • U := by
    rw [hsub1, hx, hconjy, ← Complex.exp_add,
      show α * Complex.I + -(β * Complex.I) = ((α - β : ℝ) : ℂ) * Complex.I by
        push_cast; ring]
    rw [one_sub_exp_mul_I (α - β), Complex.real_smul, hU]
    push_cast
    ring
  have hsr : foot 1 z y - foot (-1) z y = (-2 * Real.sin ((γ - β) / 2)) • V := by
    rw [hsub2, hz, hconjy, ← Complex.exp_add,
      show γ * Complex.I + -(β * Complex.I) = ((γ - β : ℝ) : ℂ) * Complex.I by
        push_cast; ring]
    rw [one_sub_exp_mul_I (γ - β), Complex.real_smul, hV]
    push_cast
    ring
  have hUn : ‖U‖ = 1 := by
    rw [hU, norm_mul, norm_neg, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hVn : ‖V‖ = 1 := by
    rw [hV, norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul]
  -- the inner product of the two unit direction vectors
  have hUVinner : ⟪U, V⟫_ℝ = -Real.cos ((α - γ) / 2) := by
    rw [Complex.inner]
    have hconjU : conj U
        = Complex.I * Complex.exp (-((((α - β) / 2 : ℝ) : ℂ) * Complex.I)) := by
      rw [hU, map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, map_neg,
        Complex.conj_I, mul_neg, neg_neg]
    have hprod : V * conj U = -Complex.exp ((((γ - α) / 2 : ℝ) : ℂ) * Complex.I) := by
      have hexp : Complex.exp ((((γ - β) / 2 : ℝ) : ℂ) * Complex.I)
            * Complex.exp (-((((α - β) / 2 : ℝ) : ℂ) * Complex.I))
          = Complex.exp ((((γ - α) / 2 : ℝ) : ℂ) * Complex.I) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      rw [hV, hconjU]
      calc Complex.I * Complex.exp ((((γ - β) / 2 : ℝ) : ℂ) * Complex.I)
            * (Complex.I * Complex.exp (-((((α - β) / 2 : ℝ) : ℂ) * Complex.I)))
          = (Complex.I * Complex.I) * (Complex.exp ((((γ - β) / 2 : ℝ) : ℂ) * Complex.I)
              * Complex.exp (-((((α - β) / 2 : ℝ) : ℂ) * Complex.I))) := by ring
        _ = -1 * Complex.exp ((((γ - α) / 2 : ℝ) : ℂ) * Complex.I) := by
            rw [Complex.I_mul_I, hexp]
        _ = -Complex.exp ((((γ - α) / 2 : ℝ) : ℂ) * Complex.I) := by ring
    rw [hprod, Complex.neg_re, Complex.exp_ofReal_mul_I_re,
      show (γ - α) / 2 = -((α - γ) / 2) by ring, Real.cos_neg]
  -- hence the angle between the two direction vectors
  have hangle : InnerProductGeometry.angle U V = Real.pi - (α - γ) / 2 := by
    have hcos : Real.cos (InnerProductGeometry.angle U V)
        = Real.cos (Real.pi - (α - γ) / 2) := by
      rw [InnerProductGeometry.cos_angle, hUVinner, hUn, hVn, Real.cos_pi_sub]
      ring
    have h0 : 0 ≤ InnerProductGeometry.angle U V := InnerProductGeometry.angle_nonneg _ _
    have h1 : InnerProductGeometry.angle U V ≤ Real.pi := InnerProductGeometry.angle_le_pi _ _
    have h2 : 0 ≤ Real.pi - (α - γ) / 2 := by linarith [Real.pi_pos]
    have h3 : Real.pi - (α - γ) / 2 ≤ Real.pi := by linarith [Real.pi_pos]
    have h := Real.arccos_cos h0 h1
    rw [hcos, Real.arccos_cos h2 h3] at h
    exact h.symm
  -- and the angle `∠XOZ`
  have hxz : InnerProductGeometry.angle x z = α - γ := by
    have hxzinner : ⟪x, z⟫_ℝ = Real.cos (α - γ) := by
      rw [Complex.inner, hz, hconjx, ← Complex.exp_add,
        show γ * Complex.I + -(α * Complex.I) = ((γ - α : ℝ) : ℂ) * Complex.I by
          push_cast; ring,
        Complex.exp_ofReal_mul_I_re, show γ - α = -(α - γ) by ring, Real.cos_neg]
    have hcos : Real.cos (InnerProductGeometry.angle x z) = Real.cos (α - γ) := by
      rw [InnerProductGeometry.cos_angle, hxzinner, hnx, hnz]
      ring
    have h0 : 0 ≤ InnerProductGeometry.angle x z := InnerProductGeometry.angle_nonneg _ _
    have h1 : InnerProductGeometry.angle x z ≤ Real.pi := InnerProductGeometry.angle_le_pi _ _
    have h := Real.arccos_cos h0 h1
    rw [hcos, Real.arccos_cos hαγ.le hαγπ.le] at h
    exact h.symm
  -- conclude
  rw [hqp, hsr]
  unfold acuteAngle
  rw [InnerProductGeometry.angle_smul_left_of_pos _ _ hsin1,
    InnerProductGeometry.angle_smul_right_of_pos _ _ hsin2, hangle, hxz,
    show Real.pi - (Real.pi - (α - γ) / 2) = (α - γ) / 2 by ring,
    min_eq_right (by linarith : (α - γ) / 2 ≤ Real.pi - (α - γ) / 2)]

snip end

problem usa2010_p1
    (x y z : ℂ)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1)
    (hxim : 0 < x.im) (hyim : 0 < y.im) (hzim : 0 < z.im)
    (hxy : x.re < y.re) (hyz : y.re < z.re) :
    acuteAngle (foot 1 x y - foot (-1) x y) (foot 1 z y - foot (-1) z y)
      = InnerProductGeometry.angle x z / 2 := by
  -- The configuration is determined up to similarity; we have normalized it so that
  -- the semicircle is the upper half of the unit circle, with `A = -1`, `B = 1`,
  -- and `O = 0`. The hypotheses say that `X, Y, Z` lie on the open upper unit
  -- semicircle in the order given by the convex pentagon `AXYZB`.
  have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (by rw [hx]; norm_num)
  have hy0 : y ≠ 0 := norm_ne_zero_iff.mp (by rw [hy]; norm_num)
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hz]; norm_num)
  have hxexp : Complex.exp (Complex.arg x * Complex.I) = x := by
    have h := Complex.norm_mul_exp_arg_mul_I x
    rw [hx, Complex.ofReal_one, one_mul] at h
    exact h
  have hyexp : Complex.exp (Complex.arg y * Complex.I) = y := by
    have h := Complex.norm_mul_exp_arg_mul_I y
    rw [hy, Complex.ofReal_one, one_mul] at h
    exact h
  have hzexp : Complex.exp (Complex.arg z * Complex.I) = z := by
    have h := Complex.norm_mul_exp_arg_mul_I z
    rw [hz, Complex.ofReal_one, one_mul] at h
    exact h
  obtain ⟨hα0, hαpi⟩ := arg_mem_Ioo_of_norm_eq_one hx hxim
  obtain ⟨hβ0, hβpi⟩ := arg_mem_Ioo_of_norm_eq_one hy hyim
  obtain ⟨hγ0, hγpi⟩ := arg_mem_Ioo_of_norm_eq_one hz hzim
  -- the ordering of the real parts gives the ordering of the arguments,
  -- since cosine is strictly antitone on `[0, π]`
  have hαβ : Complex.arg y < Complex.arg x := by
    have hcosα : Real.cos (Complex.arg x) = x.re := by
      rw [Complex.cos_arg hx0, hx, div_one]
    have hcosβ : Real.cos (Complex.arg y) = y.re := by
      rw [Complex.cos_arg hy0, hy, div_one]
    by_contra hcon
    push Not at hcon
    have hle : Real.cos (Complex.arg y) ≤ Real.cos (Complex.arg x) :=
      Real.cos_le_cos_of_nonneg_of_le_pi hα0.le hβpi.le hcon
    rw [hcosα, hcosβ] at hle
    linarith
  have hβγ : Complex.arg z < Complex.arg y := by
    have hcosβ : Real.cos (Complex.arg y) = y.re := by
      rw [Complex.cos_arg hy0, hy, div_one]
    have hcosγ : Real.cos (Complex.arg z) = z.re := by
      rw [Complex.cos_arg hz0, hz, div_one]
    by_contra hcon
    push Not at hcon
    have hle : Real.cos (Complex.arg z) ≤ Real.cos (Complex.arg y) :=
      Real.cos_le_cos_of_nonneg_of_le_pi hβ0.le hγpi.le hcon
    rw [hcosβ, hcosγ] at hle
    linarith
  rw [← hxexp, ← hyexp, ← hzexp]
  exact acuteAngle_eq_of_exp (Complex.arg x) (Complex.arg y) (Complex.arg z) hγ0 hβγ hαβ hαpi

end Usa2010P1
