/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 1984, Problem 3

A, B, C, D, X are five points in space, such that AB, BC, CD, DA all subtend
the acute angle θ at X. Find the maximum and minimum possible values of
∠AXC + ∠BXD (for all such configurations) in terms of θ.
-/

namespace Usa1984P3

open InnerProductGeometry
open scoped InnerProductSpace

/-- The set of all possible values of `∠AXC + ∠BXD`, over all configurations of
five points `A`, `B`, `C`, `D`, `X` in space such that `AB`, `BC`, `CD`, `DA`
all subtend the angle `θ` at `X`. -/
def achievableSums (θ : ℝ) : Set ℝ :=
  {s : ℝ | ∃ A B C D X : EuclideanSpace ℝ (Fin 3),
    A ≠ X ∧ B ≠ X ∧ C ≠ X ∧ D ≠ X ∧
    angle (A - X) (B - X) = θ ∧
    angle (B - X) (C - X) = θ ∧
    angle (C - X) (D - X) = θ ∧
    angle (D - X) (A - X) = θ ∧
    s = angle (A - X) (C - X) + angle (B - X) (D - X)}

/-- The minimum possible value of `∠AXC + ∠BXD`. -/
determine minValue (θ : ℝ) : ℝ := 0

/-- The maximum possible value of `∠AXC + ∠BXD`. -/
noncomputable determine maxValue (θ : ℝ) : ℝ :=
  2 * Real.arccos (2 * Real.cos θ - 1)

snip begin

/-!
## Solution

Only the directions of the four rays `XA`, `XB`, `XC`, `XD` matter, so we may
work with the unit vectors `a`, `b`, `c`, `d` along those rays; the hypothesis
becomes `⟪a, b⟫ = ⟪b, c⟫ = ⟪c, d⟫ = ⟪d, a⟫ = cos θ`.

For the upper bound, set `u = a + c` and `v = b + d`. Then
`⟪u, v⟫ = 4 cos θ`, while `‖u‖ = 2 cos (∠AXC / 2)` and `‖v‖ = 2 cos (∠BXD / 2)`.
Cauchy–Schwarz gives `cos θ ≤ cos (α/2) cos (β/2)` with `α = ∠AXC`, `β = ∠BXD`,
and the product-to-sum formula together with `cos ≤ 1` yields
`cos ((α + β)/2) ≥ 2 cos θ - 1`. Since both sides lie in `[0, π]` where cosine
is strictly antitone, `α + β ≤ 2 arccos (2 cos θ - 1)`.

The minimum `0` is attained by putting `A`, `C` on one ray from `X` and `B`,
`D` on another ray making angle `θ` with the first one (then `∠AXC = ∠BXD = 0`).
The maximum is attained by a square pyramid with apex `X`, where
`∠AXC = ∠BXD = arccos (2 cos θ - 1)`.
-/

section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The inner product of two normalized vectors is the cosine of their angle. -/
lemma inner_normalize (x y : V) :
    ⟪(‖x‖⁻¹ : ℝ) • x, (‖y‖⁻¹ : ℝ) • y⟫_ℝ = Real.cos (angle x y) := by
  rw [inner_smul_left, inner_smul_right, cos_angle]
  simp only [starRingEnd_apply, star_trivial]
  rw [div_eq_inv_mul, mul_inv]
  ring

/-- Normalizing a nonzero vector gives a unit vector. -/
lemma norm_normalize {x : V} (hx : x ≠ 0) : ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := by
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

/-- Normalizing both vectors does not change the angle between them. -/
lemma angle_normalize {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    angle ((‖x‖⁻¹ : ℝ) • x) ((‖y‖⁻¹ : ℝ) • y) = angle x y := by
  rw [angle_smul_left_of_pos _ _ (inv_pos.mpr (norm_pos_iff.mpr hx)),
    angle_smul_right_of_pos _ _ (inv_pos.mpr (norm_pos_iff.mpr hy))]

/-- The norm of the sum of two unit vectors, in terms of the angle between
them. -/
lemma norm_add_unit {a c : V} (ha : ‖a‖ = 1) (hc : ‖c‖ = 1) :
    ‖a + c‖ = 2 * Real.cos (angle a c / 2) := by
  have hcos : 0 ≤ Real.cos (angle a c / 2) := by
    apply Real.cos_nonneg_of_mem_Icc
    have h1 := angle_nonneg a c
    have h2 := angle_le_pi a c
    constructor <;> linarith [Real.pi_pos]
  have hnn : (0 : ℝ) ≤ 2 * Real.cos (angle a c / 2) := by positivity
  have hsq : ‖a + c‖ ^ 2 = (2 * Real.cos (angle a c / 2)) ^ 2 := by
    have hrw : (2 * Real.cos (angle a c / 2)) ^ 2 = 4 * (Real.cos (angle a c / 2)) ^ 2 := by
      ring
    rw [norm_add_sq_real, ha, hc, inner_eq_cos_angle_of_norm_eq_one ha hc, hrw,
      Real.cos_sq, show (2 : ℝ) * (angle a c / 2) = angle a c by ring]
    ring
  calc ‖a + c‖ = Real.sqrt (‖a + c‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt ((2 * Real.cos (angle a c / 2)) ^ 2) := by rw [hsq]
    _ = 2 * Real.cos (angle a c / 2) := Real.sqrt_sq hnn

/-- The key inequality: for unit vectors with consecutive inner products
`cos θ`, the sum of the two "diagonal" angles is at most
`2 * arccos (2 * cos θ - 1)`. -/
lemma angle_add_angle_le {a b c d : V} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hc : ‖c‖ = 1) (hd : ‖d‖ = 1) {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < Real.pi / 2)
    (hab : ⟪a, b⟫_ℝ = Real.cos θ) (hbc : ⟪b, c⟫_ℝ = Real.cos θ)
    (hcd : ⟪c, d⟫_ℝ = Real.cos θ) (hda : ⟪d, a⟫_ℝ = Real.cos θ) :
    angle a c + angle b d ≤ 2 * Real.arccos (2 * Real.cos θ - 1) := by
  have hcosθ : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hθ.le⟩
  -- The sum of the four consecutive inner products
  have huv : ⟪a + c, b + d⟫_ℝ = 4 * Real.cos θ := by
    rw [inner_add_left, inner_add_right, inner_add_right,
      show ⟪a, d⟫_ℝ = ⟪d, a⟫_ℝ from real_inner_comm d a,
      show ⟪c, b⟫_ℝ = ⟪b, c⟫_ℝ from real_inner_comm b c, hab, hbc, hcd, hda]
    ring
  -- Cauchy–Schwarz applied to `a + c` and `b + d`
  have hCS : 4 * Real.cos θ ≤
      (2 * Real.cos (angle a c / 2)) * (2 * Real.cos (angle b d / 2)) := by
    have h := real_inner_le_norm (a + c) (b + d)
    rw [huv, norm_add_unit ha hc, norm_add_unit hb hd] at h
    exact h
  -- Product-to-sum: `2 cos x cos y = cos (x + y) + cos (x - y)`
  have hps : (2 * Real.cos (angle a c / 2)) * (2 * Real.cos (angle b d / 2)) =
      2 * Real.cos ((angle a c + angle b d) / 2) +
        2 * Real.cos ((angle a c - angle b d) / 2) := by
    rw [show (angle a c + angle b d) / 2 = angle a c / 2 + angle b d / 2 by ring,
      show (angle a c - angle b d) / 2 = angle a c / 2 - angle b d / 2 by ring,
      Real.cos_add, Real.cos_sub]
    ring
  -- Hence `cos ((α + β)/2) ≥ 2 cos θ - 1`
  have hge : 2 * Real.cos θ - 1 ≤ Real.cos ((angle a c + angle b d) / 2) := by
    have h1 := Real.cos_le_one ((angle a c - angle b d) / 2)
    linarith
  -- Both sides lie in `[0, π]`, where cosine is strictly antitone
  have hmem1 : (angle a c + angle b d) / 2 ∈ Set.Icc (0 : ℝ) Real.pi := by
    have h1 := angle_nonneg a c
    have h2 := angle_nonneg b d
    have h3 := angle_le_pi a c
    have h4 := angle_le_pi b d
    constructor <;> linarith
  have hmem2 : Real.arccos (2 * Real.cos θ - 1) ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
  have hbnd1 : -1 ≤ 2 * Real.cos θ - 1 := by linarith
  have hbnd2 : 2 * Real.cos θ - 1 ≤ 1 := by linarith [Real.cos_le_one θ]
  have hmono := (Real.strictAntiOn_cos.le_iff_ge hmem2 hmem1).mp
    (show Real.cos (Real.arccos (2 * Real.cos θ - 1)) ≤
        Real.cos ((angle a c + angle b d) / 2) by
      rw [Real.cos_arccos hbnd1 hbnd2]; exact hge)
  linarith

/-- The upper bound for any configuration of five points. -/
lemma upper_bound {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < Real.pi / 2)
    {A B C D X : V} (hAX : A ≠ X) (hBX : B ≠ X) (hCX : C ≠ X) (hDX : D ≠ X)
    (hAB : angle (A - X) (B - X) = θ) (hBC : angle (B - X) (C - X) = θ)
    (hCD : angle (C - X) (D - X) = θ) (hDA : angle (D - X) (A - X) = θ) :
    angle (A - X) (C - X) + angle (B - X) (D - X) ≤
      2 * Real.arccos (2 * Real.cos θ - 1) := by
  have h1 : A - X ≠ 0 := sub_ne_zero.mpr hAX
  have h2 : B - X ≠ 0 := sub_ne_zero.mpr hBX
  have h3 : C - X ≠ 0 := sub_ne_zero.mpr hCX
  have h4 : D - X ≠ 0 := sub_ne_zero.mpr hDX
  have key := angle_add_angle_le (norm_normalize h1) (norm_normalize h2)
    (norm_normalize h3) (norm_normalize h4) hθ0 hθ
    (by rw [inner_normalize, hAB]) (by rw [inner_normalize, hBC])
    (by rw [inner_normalize, hCD]) (by rw [inner_normalize, hDA])
  rwa [angle_normalize h1 h3, angle_normalize h2 h4] at key

end

/-- Every achievable sum is nonnegative. -/
lemma lower_bound {θ : ℝ} {s : ℝ} (hs : s ∈ achievableSums θ) : 0 ≤ s := by
  obtain ⟨A, B, C, D, X, -, -, -, -, -, -, -, -, rfl⟩ := hs
  exact add_nonneg (angle_nonneg _ _) (angle_nonneg _ _)

/-- Every achievable sum is at most `2 * arccos (2 * cos θ - 1)`. -/
lemma upper_bound' {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < Real.pi / 2) {s : ℝ}
    (hs : s ∈ achievableSums θ) : s ≤ 2 * Real.arccos (2 * Real.cos θ - 1) := by
  obtain ⟨A, B, C, D, X, hAX, hBX, hCX, hDX, h1, h2, h3, h4, rfl⟩ := hs
  exact upper_bound hθ0 hθ hAX hBX hCX hDX h1 h2 h3 h4

/-- The value `0` is achieved: put `A`, `C` on one ray from `X` and `B`, `D` on
another ray making angle `θ` with the first one. -/
lemma min_attained {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < Real.pi / 2) :
    (0 : ℝ) ∈ achievableSums θ := by
  classical
  set e0 : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 0 1 with he0
  set e1 : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 1 1 with he1
  set f : EuclideanSpace ℝ (Fin 3) := Real.cos θ • e0 + Real.sin θ • e1 with hf
  have he00 : ⟪e0, e0⟫_ℝ = 1 := by rw [he0]; simp
  have he01 : ⟪e0, e1⟫_ℝ = 0 := by
    rw [he0, he1]; simp [EuclideanSpace.inner_single_left]
  have he10 : ⟪e1, e0⟫_ℝ = 0 := by
    rw [he1, he0]; simp [EuclideanSpace.inner_single_left]
  have he11 : ⟪e1, e1⟫_ℝ = 1 := by rw [he1]; simp
  have hne0 : ‖e0‖ = 1 := by rw [he0]; simp [PiLp.norm_single]
  have hff : ⟪f, f⟫_ℝ = 1 := by
    rw [hf]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      he00, he01, he10, he11, starRingEnd_apply, star_trivial, mul_one, mul_zero,
      add_zero, zero_add]
    linear_combination Real.cos_sq_add_sin_sq θ
  have hnf : ‖f‖ = 1 := by rw [norm_eq_sqrt_real_inner, hff, Real.sqrt_one]
  have he0f : ⟪e0, f⟫_ℝ = Real.cos θ := by
    rw [hf]
    simp only [inner_add_right, inner_smul_right, he00, he01, mul_one, mul_zero,
      add_zero]
  have he0_ne : e0 ≠ 0 := by rw [← norm_ne_zero_iff, hne0]; norm_num
  have hf_ne : f ≠ 0 := by rw [← norm_ne_zero_iff, hnf]; norm_num
  have hangle : angle e0 f = θ := by
    unfold InnerProductGeometry.angle
    rw [he0f, hne0, hnf, mul_one, div_one]
    exact Real.arccos_cos hθ0.le (by linarith [Real.pi_pos])
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have h3pos : (0 : ℝ) < 3 := by norm_num
  refine ⟨e0, f, (2 : ℝ) • e0, (3 : ℝ) • f, 0, he0_ne, hf_ne,
    smul_ne_zero (by norm_num) he0_ne, smul_ne_zero (by norm_num) hf_ne,
    ?_, ?_, ?_, ?_, ?_⟩
  · -- angle (e0 - 0) (f - 0) = θ
    rw [sub_zero, sub_zero]
    exact hangle
  · -- angle (f - 0) ((2:ℝ) • e0 - 0) = θ
    rw [sub_zero, sub_zero, angle_smul_right_of_pos _ _ h2pos, angle_comm f e0]
    exact hangle
  · -- angle ((2:ℝ) • e0 - 0) ((3:ℝ) • f - 0) = θ
    rw [sub_zero, sub_zero, angle_smul_left_of_pos _ _ h2pos,
      angle_smul_right_of_pos _ _ h3pos]
    exact hangle
  · -- angle ((3:ℝ) • f - 0) (e0 - 0) = θ
    rw [sub_zero, sub_zero, angle_smul_left_of_pos _ _ h3pos, angle_comm f e0]
    exact hangle
  · -- 0 = angle (e0 - 0) ((2:ℝ) • e0 - 0) + angle (f - 0) ((3:ℝ) • f - 0)
    rw [sub_zero, sub_zero, sub_zero, sub_zero,
      angle_smul_right_of_pos _ _ h2pos, angle_self he0_ne,
      angle_smul_right_of_pos _ _ h3pos, angle_self hf_ne, add_zero]

/-- The value `2 * arccos (2 * cos θ - 1)` is achieved by a square pyramid:
`X` is the apex and `A`, `B`, `C`, `D` are the vertices of a square whose
center is the foot of the pyramid. -/
lemma max_attained {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < Real.pi / 2) :
    (2 * Real.arccos (2 * Real.cos θ - 1)) ∈ achievableSums θ := by
  classical
  have hcosθ : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ⟩
  have h1mc : 0 ≤ 1 - Real.cos θ := by linarith [Real.cos_le_one θ]
  set e0 : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 0 1 with he0
  set e1 : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 1 1 with he1
  set e2 : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 2 1 with he2
  set t : ℝ := Real.sqrt (1 - Real.cos θ) with ht
  set u : ℝ := Real.sqrt (Real.cos θ) with hu
  set a : EuclideanSpace ℝ (Fin 3) := t • e0 + u • e2 with ha'
  set b : EuclideanSpace ℝ (Fin 3) := t • e1 + u • e2 with hb'
  set c : EuclideanSpace ℝ (Fin 3) := (-t) • e0 + u • e2 with hc'
  set d : EuclideanSpace ℝ (Fin 3) := (-t) • e1 + u • e2 with hd'
  have he00 : ⟪e0, e0⟫_ℝ = 1 := by rw [he0]; simp
  have he01 : ⟪e0, e1⟫_ℝ = 0 := by
    rw [he0, he1]; simp [EuclideanSpace.inner_single_left]
  have he02 : ⟪e0, e2⟫_ℝ = 0 := by
    rw [he0, he2]; simp [EuclideanSpace.inner_single_left]
  have he10 : ⟪e1, e0⟫_ℝ = 0 := by
    rw [he1, he0]; simp [EuclideanSpace.inner_single_left]
  have he11 : ⟪e1, e1⟫_ℝ = 1 := by rw [he1]; simp
  have he12 : ⟪e1, e2⟫_ℝ = 0 := by
    rw [he1, he2]; simp [EuclideanSpace.inner_single_left]
  have he20 : ⟪e2, e0⟫_ℝ = 0 := by
    rw [he2, he0]; simp [EuclideanSpace.inner_single_left]
  have he21 : ⟪e2, e1⟫_ℝ = 0 := by
    rw [he2, he1]; simp [EuclideanSpace.inner_single_left]
  have he22 : ⟪e2, e2⟫_ℝ = 1 := by rw [he2]; simp
  have ht2 : t ^ 2 = 1 - Real.cos θ := by rw [ht]; exact Real.sq_sqrt h1mc
  have hu2 : u ^ 2 = Real.cos θ := by rw [hu]; exact Real.sq_sqrt hcosθ.le
  -- inner products between the four rays
  have haa : ⟪a, a⟫_ℝ = 1 := by
    rw [ha']
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      he00, he02, he20, he22, starRingEnd_apply, star_trivial, mul_one, mul_zero,
      add_zero, zero_add]
    linear_combination ht2 + hu2
  have hbb : ⟪b, b⟫_ℝ = 1 := by
    rw [hb']
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      he11, he12, he21, he22, starRingEnd_apply, star_trivial, mul_one, mul_zero,
      add_zero, zero_add]
    linear_combination ht2 + hu2
  have hcc : ⟪c, c⟫_ℝ = 1 := by
    rw [hc']
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      he00, he02, he20, he22, starRingEnd_apply, star_trivial, mul_one, mul_zero,
      add_zero, zero_add]
    linear_combination ht2 + hu2
  have hdd : ⟪d, d⟫_ℝ = 1 := by
    rw [hd']
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      he11, he12, he21, he22, starRingEnd_apply, star_trivial, mul_one, mul_zero,
      add_zero, zero_add]
    linear_combination ht2 + hu2
  have hab : ⟪a, b⟫_ℝ = Real.cos θ := by
    rw [ha', hb']
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      he01, he02, he21, he22, starRingEnd_apply, star_trivial, mul_one, mul_zero,
      add_zero, zero_add]
    linear_combination hu2
  have hbc : ⟪b, c⟫_ℝ = Real.cos θ := by
    rw [hb', hc']
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      he10, he12, he20, he22, starRingEnd_apply, star_trivial, mul_one, mul_zero,
      add_zero, zero_add]
    linear_combination hu2
  have hcd : ⟪c, d⟫_ℝ = Real.cos θ := by
    rw [hc', hd']
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      he01, he02, he21, he22, starRingEnd_apply, star_trivial, mul_one, mul_zero,
      add_zero, zero_add]
    linear_combination hu2
  have hda : ⟪d, a⟫_ℝ = Real.cos θ := by
    rw [hd', ha']
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      he10, he12, he20, he22, starRingEnd_apply, star_trivial, mul_one, mul_zero,
      add_zero, zero_add]
    linear_combination hu2
  have hac : ⟪a, c⟫_ℝ = 2 * Real.cos θ - 1 := by
    rw [ha', hc']
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      he00, he02, he20, he22, starRingEnd_apply, star_trivial, mul_one, mul_zero,
      add_zero, zero_add]
    linear_combination hu2 - ht2
  have hbd : ⟪b, d⟫_ℝ = 2 * Real.cos θ - 1 := by
    rw [hb', hd']
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      he11, he12, he21, he22, starRingEnd_apply, star_trivial, mul_one, mul_zero,
      add_zero, zero_add]
    linear_combination hu2 - ht2
  -- the four rays are unit vectors
  have hna : ‖a‖ = 1 := by rw [norm_eq_sqrt_real_inner, haa, Real.sqrt_one]
  have hnb : ‖b‖ = 1 := by rw [norm_eq_sqrt_real_inner, hbb, Real.sqrt_one]
  have hnc : ‖c‖ = 1 := by rw [norm_eq_sqrt_real_inner, hcc, Real.sqrt_one]
  have hnd : ‖d‖ = 1 := by rw [norm_eq_sqrt_real_inner, hdd, Real.sqrt_one]
  have ha_ne : a ≠ 0 := by rw [← norm_ne_zero_iff, hna]; norm_num
  have hb_ne : b ≠ 0 := by rw [← norm_ne_zero_iff, hnb]; norm_num
  have hc_ne : c ≠ 0 := by rw [← norm_ne_zero_iff, hnc]; norm_num
  have hd_ne : d ≠ 0 := by rw [← norm_ne_zero_iff, hnd]; norm_num
  -- the angles
  have hpi : θ ≤ Real.pi := by linarith [Real.pi_pos]
  have hang_ab : angle a b = θ := by
    unfold InnerProductGeometry.angle
    rw [hab, hna, hnb, mul_one, div_one]
    exact Real.arccos_cos hθ0.le hpi
  have hang_bc : angle b c = θ := by
    unfold InnerProductGeometry.angle
    rw [hbc, hnb, hnc, mul_one, div_one]
    exact Real.arccos_cos hθ0.le hpi
  have hang_cd : angle c d = θ := by
    unfold InnerProductGeometry.angle
    rw [hcd, hnc, hnd, mul_one, div_one]
    exact Real.arccos_cos hθ0.le hpi
  have hang_da : angle d a = θ := by
    unfold InnerProductGeometry.angle
    rw [hda, hnd, hna, mul_one, div_one]
    exact Real.arccos_cos hθ0.le hpi
  have hang_ac : angle a c = Real.arccos (2 * Real.cos θ - 1) := by
    unfold InnerProductGeometry.angle
    rw [hac, hna, hnc, mul_one, div_one]
  have hang_bd : angle b d = Real.arccos (2 * Real.cos θ - 1) := by
    unfold InnerProductGeometry.angle
    rw [hbd, hnb, hnd, mul_one, div_one]
  refine ⟨a, b, c, d, 0, ha_ne, hb_ne, hc_ne, hd_ne, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sub_zero, sub_zero]; exact hang_ab
  · rw [sub_zero, sub_zero]; exact hang_bc
  · rw [sub_zero, sub_zero]; exact hang_cd
  · rw [sub_zero, sub_zero]; exact hang_da
  · rw [sub_zero, sub_zero, sub_zero, sub_zero, hang_ac, hang_bd, two_mul]

snip end

problem usa1984_p3 (θ : ℝ) (hθ0 : 0 < θ) (hθ : θ < Real.pi / 2) :
    IsLeast (achievableSums θ) (minValue θ) ∧
    IsGreatest (achievableSums θ) (maxValue θ) := by
  refine ⟨⟨min_attained hθ0 hθ, fun s hs => lower_bound hs⟩,
    ⟨max_attained hθ0 hθ, fun s hs => upper_bound' hθ0 hθ hs⟩⟩

end Usa1984P3
