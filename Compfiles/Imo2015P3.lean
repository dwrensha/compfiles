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
public import Mathlib.Analysis.InnerProductSpace.TwoDim
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Geometry.Euclidean.Circumcenter
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 2015, Problem 3

Let ABC be an acute triangle with AB > AC. Let Γ be its circumcircle, H its
orthocenter, and F the foot of the altitude from A. Let M be the midpoint of
BC. Let Q be the point on Γ such that ∠HQA = 90° and let K be the point on Γ
such that ∠HKQ = 90°. Assume that the points A, B, C, K and Q are all different
and lie on Γ in this order. Prove that the circumcircles of triangles KQH and
FKM are tangent to each other.

## Formalization notes

* The hypothesis that A, B, C, K, Q lie on Γ *in this order* is not needed:
  the angle conditions determine Q and K uniquely once the points are known to
  be distinct, so only the pairwise distinctness is assumed.
* "H is the orthocenter" is expressed by AH ⊥ BC and BH ⊥ CA; "F is the foot
  of the altitude from A" by F ∈ line BC and AF ⊥ BC; Γ is given by its center
  O and radius r.
* Tangency of the two circumcircles is expressed as their intersection being
  the single point K.
-/

namespace Imo2015P3

open scoped EuclideanGeometry RealInnerProductSpace

snip begin

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

-- We need some instances in order to talk about oriented angles / rotations.

local instance planeFiniteDim :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
  ⟨finrank_euclideanSpace_fin⟩

noncomputable local instance someOrientation :
    Module.Oriented ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2) :=
  ⟨Module.Basis.orientation (Module.finBasisOfFinrankEq _ _ planeFiniteDim.out)⟩

/-- Two circles through a common point `K` whose centers are collinear with `K`
(with a nontrivial ratio) meet in no other point, i.e. are tangent at `K`. -/
lemma eq_of_mem_both_circles {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] {O₁ O₂ K X : P}
    (hLam : ∃ lam : ℝ, lam ≠ 0 ∧ O₂ -ᵥ O₁ = lam • (K -ᵥ O₁))
    (h1 : dist X O₁ = dist K O₁) (h2 : dist X O₂ = dist K O₂) : X = K := by
  obtain ⟨lam, hlam, hO⟩ := hLam
  have n1 : ‖X -ᵥ O₁‖ ^ 2 = ‖K -ᵥ O₁‖ ^ 2 := by
    rw [← dist_eq_norm_vsub, ← dist_eq_norm_vsub]
    exact congrArg (· ^ 2) h1
  have n2 : ‖X -ᵥ O₂‖ ^ 2 = ‖K -ᵥ O₂‖ ^ 2 := by
    rw [← dist_eq_norm_vsub, ← dist_eq_norm_vsub]
    exact congrArg (· ^ 2) h2
  have e1 : ‖X -ᵥ K‖ ^ 2 + 2 * ⟪X -ᵥ K, K -ᵥ O₁⟫ = 0 := by
    have hu : X -ᵥ O₁ = (X -ᵥ K) + (K -ᵥ O₁) := (vsub_add_vsub_cancel X K O₁).symm
    rw [hu, norm_add_sq_real] at n1
    linarith
  have hK : K -ᵥ O₂ = (1 - lam) • (K -ᵥ O₁) := by
    rw [← vsub_sub_vsub_cancel_right K O₂ O₁, hO]
    module
  have e2 : ‖X -ᵥ K‖ ^ 2 + 2 * (1 - lam) * ⟪X -ᵥ K, K -ᵥ O₁⟫ = 0 := by
    have hu : X -ᵥ O₂ = (X -ᵥ K) + (K -ᵥ O₂) := (vsub_add_vsub_cancel X K O₂).symm
    rw [hu, hK, norm_add_sq_real, norm_smul, inner_smul_right] at n2
    linarith
  have e3 : ⟪X -ᵥ K, K -ᵥ O₁⟫ = 0 := by
    have h3 : 2 * lam * ⟪X -ᵥ K, K -ᵥ O₁⟫ = 0 := by linarith
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd (by linarith : lam = 0) hlam
    · exact h4
  have e4 : ‖X -ᵥ K‖ ^ 2 = 0 := by linarith [e1]
  rw [sq_eq_zero_iff, norm_eq_zero, vsub_eq_zero_iff_eq] at e4
  exact e4

/-- If the angle between two vectors is acute, their inner product is positive. -/
lemma inner_pos_of_angle_lt {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {u v : V} (h : InnerProductGeometry.angle u v < Real.pi / 2) : 0 < ⟪u, v⟫ := by
  have hnn : 0 ≤ InnerProductGeometry.angle u v := InnerProductGeometry.angle_nonneg u v
  have hcos : 0 < Real.cos (InnerProductGeometry.angle u v) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h⟩
  rw [InnerProductGeometry.cos_angle] at hcos
  by_contra hcon
  push Not at hcon
  have hle : ⟪u, v⟫ / (‖u‖ * ‖v‖) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hcon (by positivity)
  linarith

section CoordLemmas

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)]

omit [Fact (Module.finrank ℝ V = 2)] in
lemma coord_li {eX eY : V} (hXX : ⟪eX, eX⟫ = 1) (hXY : ⟪eX, eY⟫ = 0)
    (hYY : ⟪eY, eY⟫ = 1) : LinearIndependent ℝ ![eX, eY] := by
  rw [linearIndependent_fin2]
  constructor
  · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    intro h
    rw [h] at hYY
    simp at hYY
  · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    intro a ha
    have h2 : ⟪a • eY, eX⟫ = ⟪eX, eX⟫ := by rw [ha]
    have hXY' : ⟪eY, eX⟫ = 0 := by rw [real_inner_comm eX eY]; exact hXY
    rw [real_inner_smul_left, hXY', hXX] at h2
    simp at h2

lemma coord_span_top {eX eY : V} (hXX : ⟪eX, eX⟫ = 1) (hXY : ⟪eX, eY⟫ = 0)
    (hYY : ⟪eY, eY⟫ = 1) : Submodule.span ℝ (Set.range ![eX, eY]) = ⊤ := by
  have hcard : Fintype.card (Fin 2) = Module.finrank ℝ V :=
    (Fintype.card_fin 2).trans (Fact.out : Module.finrank ℝ V = 2).symm
  exact coord_li hXX hXY hYY |>.span_eq_top_of_card_eq_finrank' hcard

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (Module.finrank ℝ V = 2)] in
lemma coord_range {eX eY : V} : Set.range ![eX, eY] = {eX, eY} := by
  ext z
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

lemma coord_decomp {eX eY : V} (hXX : ⟪eX, eX⟫ = 1) (hXY : ⟪eX, eY⟫ = 0)
    (hYY : ⟪eY, eY⟫ = 1) (u : V) : u = ⟪u, eX⟫ • eX + ⟪u, eY⟫ • eY := by
  have hu : u ∈ Submodule.span ℝ (Set.range ![eX, eY]) :=
    coord_span_top hXX hXY hYY ▸ Submodule.mem_top
  rw [coord_range, Submodule.mem_span_pair] at hu
  obtain ⟨a, b, hab⟩ := hu
  have hXX' : ‖eX‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq, hXX]
  have hYY' : ‖eY‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq, hYY]
  have hXY' : ⟪eY, eX⟫ = 0 := by rw [real_inner_comm eX eY]; exact hXY
  have ha : a = ⟪u, eX⟫ := by
    rw [← hab]
    simp [inner_add_left, real_inner_smul_left, hXX', hXY']
  have hb : b = ⟪u, eY⟫ := by
    rw [← hab]
    simp [inner_add_left, real_inner_smul_left, hYY', hXY]
  rw [ha, hb] at hab
  exact hab.symm

lemma inner_coord {eX eY : V} (hXX : ⟪eX, eX⟫ = 1) (hXY : ⟪eX, eY⟫ = 0)
    (hYY : ⟪eY, eY⟫ = 1) (u v : V) :
    ⟪u, v⟫ = ⟪u, eX⟫ * ⟪v, eX⟫ + ⟪u, eY⟫ * ⟪v, eY⟫ := by
  have hXX' : ‖eX‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq, hXX]
  have hYY' : ‖eY‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq, hYY]
  have hXY' : ⟪eY, eX⟫ = 0 := by rw [real_inner_comm eX eY]; exact hXY
  rw [coord_decomp hXX hXY hYY u, coord_decomp hXX hXY hYY v]
  simp [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    hXX', hYY', hXY, hXY']
  ring

lemma eq_of_coords {eX eY : V} (hXX : ⟪eX, eX⟫ = 1) (hXY : ⟪eX, eY⟫ = 0)
    (hYY : ⟪eY, eY⟫ = 1) {H p₁ p₂ : P} (h1 : ⟪p₁ -ᵥ H, eX⟫ = ⟪p₂ -ᵥ H, eX⟫)
    (h2 : ⟪p₁ -ᵥ H, eY⟫ = ⟪p₂ -ᵥ H, eY⟫) : p₁ = p₂ := by
  have hx : ⟪p₁ -ᵥ p₂, eX⟫ = 0 := by
    rw [← vsub_sub_vsub_cancel_right p₁ p₂ H, inner_sub_left, h1, sub_self]
  have hy : ⟪p₁ -ᵥ p₂, eY⟫ = 0 := by
    rw [← vsub_sub_vsub_cancel_right p₁ p₂ H, inner_sub_left, h2, sub_self]
  have hd := coord_decomp hXX hXY hYY (p₁ -ᵥ p₂)
  rw [hx, hy, zero_smul, zero_smul, add_zero] at hd
  exact vsub_eq_zero_iff_eq.mp hd

lemma dist_sq {eX eY : V} (hXX : ⟪eX, eX⟫ = 1) (hXY : ⟪eX, eY⟫ = 0)
    (hYY : ⟪eY, eY⟫ = 1) (H p₁ p₂ : P) :
    dist p₁ p₂ ^ 2 = (⟪p₁ -ᵥ H, eX⟫ - ⟪p₂ -ᵥ H, eX⟫) ^ 2 +
      (⟪p₁ -ᵥ H, eY⟫ - ⟪p₂ -ᵥ H, eY⟫) ^ 2 := by
  rw [dist_eq_norm_vsub, ← real_inner_self_eq_norm_sq,
    inner_coord hXX hXY hYY (p₁ -ᵥ p₂) (p₁ -ᵥ p₂)]
  have hx : ⟪p₁ -ᵥ p₂, eX⟫ = ⟪p₁ -ᵥ H, eX⟫ - ⟪p₂ -ᵥ H, eX⟫ := by
    rw [← vsub_sub_vsub_cancel_right p₁ p₂ H, inner_sub_left]
  have hy : ⟪p₁ -ᵥ p₂, eY⟫ = ⟪p₁ -ᵥ H, eY⟫ - ⟪p₂ -ᵥ H, eY⟫ := by
    rw [← vsub_sub_vsub_cancel_right p₁ p₂ H, inner_sub_left]
  rw [hx, hy]
  ring

end CoordLemmas

/- ### Algebraic core: coordinate characterization of Q and K, and the
final collinearity identity. (Verified symbolically; proved by linear
arithmetic over field_simp-cleared rational identities.) -/


/-- `S = m^2 + f^2` is positive (since `f ≠ 0`). -/
lemma S_pos {f : ℝ} (hf : 0 < f) (m : ℝ) : 0 < m^2 + f^2 := by positivity

/-- `T = a^2*m^2 + 4*(m^2+f^2)^2` is positive (the second summand is). -/
lemma T_pos {f : ℝ} (hf : 0 < f) (m a : ℝ) : 0 < a^2*m^2 + 4*(m^2+f^2)^2 := by
  have hS : 0 < m^2 + f^2 := S_pos hf m
  have h1 : 0 < 4 * (m^2+f^2)^2 := mul_pos (by norm_num) (pow_pos hS 2)
  have h2 : 0 ≤ a^2 * m^2 := by
    have h := sq_nonneg (a * m)
    rw [mul_pow] at h
    exact h
  exact add_pos_of_nonneg_of_pos h2 h1

/-- `a * f ≠ 0`. -/
lemma af_ne {a f : ℝ} (ha : 0 < a) (hf : 0 < f) : a * f ≠ 0 :=
  mul_ne_zero (ne_of_gt ha) (ne_of_gt hf)

/-- Characterization of Q. From the two circle equations and Q ≠ A. -/
theorem Q_char {a f m : ℝ} (_ha : 0 < a) (hf : 0 < f) {x y : ℝ}
    (h1 : x^2 + y^2 = a * y)
    (h2 : x^2 + y^2 - 2*m*x - (a - 2*f)*y - 2*a*f = 0)
    (hne : ¬ (x = 0 ∧ y = a)) :
    x = -m*a*f/(m^2+f^2) ∧ y = a*f^2/(m^2+f^2) := by
  have hS : 0 < m^2 + f^2 := S_pos hf m
  have hSne : m^2 + f^2 ≠ 0 := ne_of_gt hS
  have hfne : f ≠ 0 := ne_of_gt hf
  -- Subtracting the two circle equations gives the radical line.
  have hL : f * y = m * x + a * f := by linarith [h1, h2]
  -- Substituting the line into `f^2 * h1` gives `(m^2+f^2)*x^2 + m*a*f*x = 0`.
  have hE : (m^2+f^2)*x^2 + m*a*f*x = 0 := by
    have e1 : (f * y)^2 = (m * x + a * f)^2 := by rw [hL]
    have e2 : f^2 * (x^2 + y^2) = f^2 * (a * y) := by rw [h1]
    linear_combination e2 - e1 + a * f * hL
  have hFac : x * ((m^2+f^2) * x + m*a*f) = 0 := by linear_combination hE
  rcases eq_zero_or_eq_zero_of_mul_eq_zero hFac with hx0 | hx0
  · -- `x = 0` forces `y = a`, i.e. the point A, contradiction.
    rw [hx0] at hL
    have h3 : f * y = f * a := by linarith [hL]
    have hya : y = a := mul_left_cancel₀ hfne h3
    exact absurd ⟨hx0, hya⟩ hne
  · have hx : x = -m*a*f/(m^2+f^2) := by
      field_simp [hSne]
      nlinarith [hx0]
    have hy : y = a*f^2/(m^2+f^2) := by
      have hy' : y = (m * x + a * f) / f := by
        field_simp [hfne]
        nlinarith [hL]
      rw [hy', hx]
      field_simp [hSne, hfne]
      ring
    exact ⟨hx, hy⟩

/-- The computed Q satisfies the second circle equation (Q on Γ). -/
theorem Q_on_gamma {a f m : ℝ} (_ha : 0 < a) (hf : 0 < f) :
    let qx := -m*a*f/(m^2+f^2); let qy := a*f^2/(m^2+f^2)
    qx^2 + qy^2 - 2*m*qx - (a-2*f)*qy - 2*a*f = 0 := by
  have hSne : m^2 + f^2 ≠ 0 := ne_of_gt (S_pos hf m)
  show (-m*a*f/(m^2+f^2))^2 + (a*f^2/(m^2+f^2))^2 - 2*m*(-m*a*f/(m^2+f^2))
      - (a-2*f)*(a*f^2/(m^2+f^2)) - 2*a*f = 0
  field_simp [hSne]
  ring

/-- Characterization of K. qx qy are Q's coordinates (from Q_char). -/
theorem K_char {a f m : ℝ} (ha : 0 < a) (hf : 0 < f) (hm : m ≠ 0)
    {qx qy : ℝ} (hqx : qx = -m*a*f/(m^2+f^2)) (hqy : qy = a*f^2/(m^2+f^2))
    {x y : ℝ}
    (h1 : x^2 + y^2 = x*qx + y*qy)
    (h2 : x^2 + y^2 - 2*m*x - (a-2*f)*y - 2*a*f = 0)
    (hne : ¬ (x = qx ∧ y = qy)) :
    x = -2*a*f*m*(a*f + 2*(m^2+f^2))/(a^2*m^2 + 4*(m^2+f^2)^2) ∧
    y = -2*a*f*(a*m^2 - 2*f*(m^2+f^2))/(a^2*m^2 + 4*(m^2+f^2)^2) := by
  have hS : 0 < m^2 + f^2 := S_pos hf m
  have hSne : m^2 + f^2 ≠ 0 := ne_of_gt hS
  have hT : 0 < a^2*m^2 + 4*(m^2+f^2)^2 := T_pos hf m a
  have hTne : a^2*m^2 + 4*(m^2+f^2)^2 ≠ 0 := ne_of_gt hT
  -- Q lies on Γ (needed to make the parametrization work).
  have hQ2 : qx^2 + qy^2 - 2*m*qx - (a-2*f)*qy - 2*a*f = 0 := by
    rw [hqx, hqy]
    exact Q_on_gamma ha hf
  -- The radical line of the two circles.
  have hLine : (qx - 2*m)*x + (qy - a + 2*f)*y = 2*a*f := by
    linear_combination h2 - h1
  have hQQ : qx^2 + qy^2 = qx*qx + qy*qy := by ring
  -- Q also lies on that line.
  have hLineQ : (qx - 2*m)*qx + (qy - a + 2*f)*qy = 2*a*f := by
    linear_combination hQ2 - hQQ
  set α := qx - 2*m with hαd
  set β := qy - a + 2*f with hβd
  have hL0 : α*(x - qx) + β*(y - qy) = 0 := by linear_combination hLine - hLineQ
  have hα : α = -m*(a*f + 2*(m^2+f^2))/(m^2+f^2) := by
    rw [hαd, hqx]
    field_simp [hSne]
    ring
  have hβ : β = (2*f*(m^2+f^2) - a*m^2)/(m^2+f^2) := by
    rw [hβd, hqy]
    field_simp [hSne]
    ring
  have haf2S : 0 < a*f + 2*(m^2+f^2) :=
    add_pos (mul_pos ha hf) (mul_pos (by norm_num) hS)
  have hαne : α ≠ 0 := by
    rw [hα]
    exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr hm) (ne_of_gt haf2S)) hSne
  have hA2 : α^2 + β^2 = (a^2*m^2 + 4*(m^2+f^2)^2)/(m^2+f^2) := by
    rw [hα, hβ]
    field_simp [hSne]
    ring
  have hA2ne : α^2 + β^2 ≠ 0 := by
    rw [hA2]
    exact div_ne_zero hTne hSne
  -- Parametrize the line as `(qx - t*β, qy + t*α)`.
  set t := ((y - qy)*α - (x - qx)*β)/(α^2 + β^2) with htd
  have htA : t * (α^2+β^2) = (y - qy)*α - (x - qx)*β := by
    rw [htd]
    field_simp [hA2ne]
  have hL0α : α * (α*(x - qx) + β*(y - qy)) = 0 := by rw [hL0, mul_zero]
  have hL0β : β * (α*(x - qx) + β*(y - qy)) = 0 := by rw [hL0, mul_zero]
  have hkey1 : (α^2+β^2)*(x - (qx - t*β)) = 0 := by
    linear_combination β * htA + hL0α
  have hkey2 : (α^2+β^2)*(y - (qy + t*α)) = 0 := by
    linear_combination hL0β - α * htA
  have htx : x = qx - t*β := by
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hkey1 with h | h
    · exact absurd h hA2ne
    · linarith [h]
  have hty : y = qy + t*α := by
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hkey2 with h | h
    · exact absurd h hA2ne
    · linarith [h]
  -- `t = 0` would give `(x, y) = Q`, contradiction.
  have htne : t ≠ 0 := by
    intro ht
    apply hne
    rw [ht] at htx hty
    constructor
    · rw [htx]; ring
    · rw [hty]; ring
  rw [htx, hty] at h2
  -- Substituting into the Γ equation gives `t * (A2*t + A1) = 0`.
  have ht_eq : t * ((α^2+β^2)*t + (-2*β*qx + 2*α*qy + 2*m*β - (a-2*f)*α)) = 0 := by
    linear_combination h2 - hQ2
  have ht2 : (α^2+β^2)*t + (-2*β*qx + 2*α*qy + 2*m*β - (a-2*f)*α) = 0 := by
    rcases eq_zero_or_eq_zero_of_mul_eq_zero ht_eq with h | h
    · exact absurd h htne
    · exact h
  have hA1 : -2*β*qx + 2*α*qy + 2*m*β - (a-2*f)*α = -a^2*f*m/(m^2+f^2) := by
    rw [hα, hβ, hqx, hqy]
    field_simp [hSne]
    ring
  have htval0 : t = -(-2*β*qx + 2*α*qy + 2*m*β - (a-2*f)*α)/(α^2+β^2) := by
    have hA2t : (α^2+β^2)*t = -(-2*β*qx + 2*α*qy + 2*m*β - (a-2*f)*α) := by
      linarith [ht2]
    rw [← hA2t]
    field_simp [hA2ne]
  have htval : t = a^2*f*m/(a^2*m^2 + 4*(m^2+f^2)^2) := by
    rw [htval0, hA1, hA2]
    field_simp [hSne, hTne]
  have hxv : x = -2*a*f*m*(a*f + 2*(m^2+f^2))/(a^2*m^2 + 4*(m^2+f^2)^2) := by
    rw [htx, htval, hqx, hβ]
    field_simp [hSne, hTne]
    ring
  have hyv : y = -2*a*f*(a*m^2 - 2*f*(m^2+f^2))/(a^2*m^2 + 4*(m^2+f^2)^2) := by
    rw [hty, htval, hqy, hα]
    field_simp [hSne, hTne]
    ring
  exact ⟨hxv, hyv⟩

/-- The y-coordinate of K plus `f` is nonzero (denominator guard). -/
theorem Ky_add_f_ne {a f m : ℝ} (ha : 0 < a) (hf : 0 < f)
    (hU : a^2*m^2 - 4*a*f*(m^2+f^2) - 4*(m^2+f^2)^2 ≠ 0)
    {y : ℝ} (hy : y = -2*a*f*(a*m^2 - 2*f*(m^2+f^2))/(a^2*m^2 + 4*(m^2+f^2)^2)) :
    y + f ≠ 0 := by
  have hTne : a^2*m^2 + 4*(m^2+f^2)^2 ≠ 0 := ne_of_gt (T_pos hf m a)
  have e1 : y + f =
      -f*(a^2*m^2 - 4*a*f*(m^2+f^2) - 4*(m^2+f^2)^2)/(a^2*m^2 + 4*(m^2+f^2)^2) := by
    rw [hy]
    field_simp [hTne]
    ring
  rw [e1]
  exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr (ne_of_gt hf)) hU) hTne

/-- The cross product `qx*y - qy*x` (K vs Q) is nonzero. -/
theorem KQH_cross_ne {a f m : ℝ} (ha : 0 < a) (hf : 0 < f) (hm : m ≠ 0)
    {qx qy x y : ℝ} (hqx : qx = -m*a*f/(m^2+f^2)) (hqy : qy = a*f^2/(m^2+f^2))
    (hx : x = -2*a*f*m*(a*f + 2*(m^2+f^2))/(a^2*m^2 + 4*(m^2+f^2)^2))
    (hy : y = -2*a*f*(a*m^2 - 2*f*(m^2+f^2))/(a^2*m^2 + 4*(m^2+f^2)^2)) :
    qx*y - qy*x ≠ 0 := by
  have hSne : m^2 + f^2 ≠ 0 := ne_of_gt (S_pos hf m)
  have hTne : a^2*m^2 + 4*(m^2+f^2)^2 ≠ 0 := ne_of_gt (T_pos hf m a)
  have hcross : qx*y - qy*x = 2*a^3*f^2*m/(a^2*m^2 + 4*(m^2+f^2)^2) := by
    rw [hqx, hqy, hx, hy]
    field_simp [hSne, hTne]
    ring
  rw [hcross]
  refine div_ne_zero ?_ hTne
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (pow_ne_zero 3 (ne_of_gt ha))) (pow_ne_zero 2 (ne_of_gt hf))) hm

/-- The finale: centers collinear with K via explicit λ. -/
theorem finale {a f m : ℝ} (ha : 0 < a) (hf : 0 < f) (hm : m ≠ 0)
    (hU : a^2*m^2 - 4*a*f*(m^2+f^2) - 4*(m^2+f^2)^2 ≠ 0)
    {qx qy x y : ℝ}
    (hqx : qx = -m*a*f/(m^2+f^2)) (hqy : qy = a*f^2/(m^2+f^2))
    (hx : x = -2*a*f*m*(a*f + 2*(m^2+f^2))/(a^2*m^2 + 4*(m^2+f^2)^2))
    (hy : y = -2*a*f*(a*m^2 - 2*f*(m^2+f^2))/(a^2*m^2 + 4*(m^2+f^2)^2)) :
    ∃ lam : ℝ, lam ≠ 0 ∧
      (m/2 - qx/2) = lam * (x - qx/2) ∧
      (-((f^2 + m*x - (x*qx + y*qy))/(y + f))/2 - qy/2) = lam * (y - qy/2) := by
  have hS : 0 < m^2 + f^2 := S_pos hf m
  have hSne : m^2 + f^2 ≠ 0 := ne_of_gt hS
  have hT : 0 < a^2*m^2 + 4*(m^2+f^2)^2 := T_pos hf m a
  have hTne : a^2*m^2 + 4*(m^2+f^2)^2 ≠ 0 := ne_of_gt hT
  have haf : a * f ≠ 0 := af_ne ha hf
  have hfne : f ≠ 0 := ne_of_gt hf
  have hafS : 0 < a*f + (m^2+f^2) := add_pos (mul_pos ha hf) hS
  have hafU : a*f*(a^2*m^2 - 4*a*f*(m^2+f^2) - 4*(m^2+f^2)^2) ≠ 0 :=
    mul_ne_zero haf hU
  have hfU : (-f)*(a^2*m^2 - 4*a*f*(m^2+f^2) - 4*(m^2+f^2)^2) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr hfne) hU
  have e1 : y + f =
      -f*(a^2*m^2 - 4*a*f*(m^2+f^2) - 4*(m^2+f^2)^2)/(a^2*m^2 + 4*(m^2+f^2)^2) := by
    rw [hy]
    field_simp [hTne]
    ring
  -- Closed form of the big numerator-over-`(y + f)` subterm: it equals `W / U`.
  have eN : (f^2 + m*x - (x*qx + y*qy))/(y + f) =
      (4*a^2*f^3 + 5*a^2*f*m^2 + 4*a*f^2*m^2 + 4*a*m^4 - 4*f^5 - 8*f^3*m^2 - 4*f*m^4) /
      (a^2*m^2 - 4*a*f*(m^2+f^2) - 4*(m^2+f^2)^2) := by
    rw [e1, hqx, hqy, hx, hy]
    rw [div_div_eq_mul_div, div_eq_div_iff hfU hU]
    field_simp [hSne, hTne]
    ring
  refine ⟨(a*f+(m^2+f^2))*(a^2*m^2+4*(m^2+f^2)^2) /
      (a*f*(a^2*m^2 - 4*a*f*(m^2+f^2) - 4*(m^2+f^2)^2)),
    div_ne_zero (mul_ne_zero (ne_of_gt hafS) hTne) hafU, ?_, ?_⟩
  · -- x-coordinate: clear `lam`'s denominator manually, then only `S, T` remain.
    rw [hqx, hx, div_mul_eq_mul_div, eq_div_iff hafU]
    field_simp [hSne, hTne]
    ring
  · -- y-coordinate: same, plus cancel the remaining `W / U` via `div_mul_cancel₀`.
    rw [eN, hqy, hy, div_mul_eq_mul_div, eq_div_iff hafU]
    set w := (4*a^2*f^3 + 5*a^2*f*m^2 + 4*a*f^2*m^2 + 4*a*m^4 - 4*f^5 - 8*f^3*m^2 - 4*f*m^4) /
      (a^2*m^2 - 4*a*f*(m^2+f^2) - 4*(m^2+f^2)^2) with hw
    have hwU : w * (a^2*m^2 - 4*a*f*(m^2+f^2) - 4*(m^2+f^2)^2) =
        (4*a^2*f^3 + 5*a^2*f*m^2 + 4*a*f^2*m^2 + 4*a*m^4 - 4*f^5 - 8*f^3*m^2 - 4*f*m^4) := by
      rw [hw]
      exact div_mul_cancel₀ _ hU
    have h1 : w * (a*f*(a^2*m^2 - 4*a*f*(m^2+f^2) - 4*(m^2+f^2)^2)) =
        a*f*(4*a^2*f^3 + 5*a^2*f*m^2 + 4*a*f^2*m^2 + 4*a*m^4 - 4*f^5 - 8*f^3*m^2 - 4*f*m^4) := by
      linear_combination (a*f) * hwU
    have hexp : (-(w)/2 - (a*f^2/(m^2+f^2))/2) *
          (a*f*(a^2*m^2 - 4*a*f*(m^2+f^2) - 4*(m^2+f^2)^2)) =
        -(a*f*(4*a^2*f^3 + 5*a^2*f*m^2 + 4*a*f^2*m^2 + 4*a*m^4 - 4*f^5 - 8*f^3*m^2
            - 4*f*m^4))/2
        - ((a*f^2/(m^2+f^2))/2) * (a*f*(a^2*m^2 - 4*a*f*(m^2+f^2) - 4*(m^2+f^2)^2)) := by
      linear_combination -h1 / 2
    rw [hexp]
    field_simp [hSne, hTne]
    ring

/- ### The geometric configuration, in coordinates adapted to the altitude from A.

We put H at the origin of an orthonormal coordinate system with A on the
positive y-axis. The coordinates of the points are then
H = (0,0), A = (0,a), F = (0,-f), B = (m-w,-f), C = (m+w,-f), M = (m,-f)
with a, f > 0, m ≠ 0 and w² = m² + f(f+a), and everything reduces to the
algebraic core above. -/

/-- The configuration of the problem. -/
structure Cfg where
  (A B C H F M Q K O : EuclideanSpace ℝ (Fin 2))
  (r : ℝ)
  (hABC : AffineIndependent ℝ ![A, B, C])
  (hAcuteA : ∠ B A C < Real.pi / 2)
  (hAcuteB : ∠ C B A < Real.pi / 2)
  (hAcuteC : ∠ A C B < Real.pi / 2)
  (hABAC : dist A C < dist A B)
  (hH1 : ⟪A -ᵥ H, B -ᵥ C⟫ = 0)
  (hH2 : ⟪B -ᵥ H, C -ᵥ A⟫ = 0)
  (hF1 : Collinear ℝ {F, B, C})
  (hF2 : ⟪A -ᵥ F, B -ᵥ C⟫ = 0)
  (hM : M = midpoint ℝ B C)
  (hOA : dist O A = r) (hOB : dist O B = r) (hOC : dist O C = r)
  (hOQ : dist O Q = r)
  (hQangle : ∠ H Q A = Real.pi / 2)
  (hOK : dist O K = r)
  (hKangle : ∠ H K Q = Real.pi / 2)
  (hKQH : AffineIndependent ℝ ![K, Q, H])
  (hFKM : AffineIndependent ℝ ![F, K, M])
  (hQA : Q ≠ A) (hQB : Q ≠ B) (hQC : Q ≠ C)
  (hKA : K ≠ A) (hKB : K ≠ B) (hKC : K ≠ C) (hKQ : K ≠ Q)

namespace Cfg

variable (cfg : Cfg)

lemma A_ne_B : cfg.A ≠ cfg.B := cfg.hABC.injective.ne (by decide : (0 : Fin 3) ≠ 1)
lemma A_ne_C : cfg.A ≠ cfg.C := cfg.hABC.injective.ne (by decide : (0 : Fin 3) ≠ 2)
lemma B_ne_C : cfg.B ≠ cfg.C := cfg.hABC.injective.ne (by decide : (1 : Fin 3) ≠ 2)

lemma angleA_lt : InnerProductGeometry.angle (cfg.B -ᵥ cfg.A) (cfg.C -ᵥ cfg.A) < Real.pi / 2 := by
  have h := cfg.hAcuteA
  unfold EuclideanGeometry.angle at h
  exact h

lemma angleB_lt : InnerProductGeometry.angle (cfg.C -ᵥ cfg.B) (cfg.A -ᵥ cfg.B) < Real.pi / 2 := by
  have h := cfg.hAcuteB
  unfold EuclideanGeometry.angle at h
  exact h

lemma angleC_lt : InnerProductGeometry.angle (cfg.A -ᵥ cfg.C) (cfg.B -ᵥ cfg.C) < Real.pi / 2 := by
  have h := cfg.hAcuteC
  unfold EuclideanGeometry.angle at h
  exact h

lemma A_ne_H : cfg.A ≠ cfg.H := by
  intro h
  have hi : ⟪cfg.B -ᵥ cfg.A, cfg.C -ᵥ cfg.A⟫ = 0 := by
    have hh := cfg.hH2
    rw [← h] at hh
    exact hh
  have h2 := (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two _ _).mp hi
  exact (lt_self_iff_false _).mp (h2 ▸ angleA_lt cfg)

/-- The unit vector along H→A. -/
noncomputable def eY : EuclideanSpace ℝ (Fin 2) := (dist cfg.A cfg.H)⁻¹ • (cfg.A -ᵥ cfg.H)

/-- Its rotation by 90 degrees. -/
noncomputable def eX : EuclideanSpace ℝ (Fin 2) := positiveOrientation.rightAngleRotation (eY cfg)

lemma eY_norm : ‖eY cfg‖ = 1 := by
  have hne : dist cfg.A cfg.H ≠ 0 := dist_ne_zero.mpr (A_ne_H cfg)
  rw [eY, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg dist_nonneg,
    ← dist_eq_norm_vsub, inv_mul_cancel₀ hne]

lemma eY_inner : ⟪eY cfg, eY cfg⟫ = 1 := by
  rw [real_inner_self_eq_norm_sq, eY_norm, one_pow]

lemma eX_inner : ⟪eX cfg, eX cfg⟫ = 1 := by
  rw [eX, LinearIsometryEquiv.inner_map_map, eY_inner]

lemma eX_eY_inner : ⟪eX cfg, eY cfg⟫ = 0 := by
  rw [eX]
  exact Orientation.inner_rightAngleRotation_self positiveOrientation _

lemma inner_c (u v : EuclideanSpace ℝ (Fin 2)) :
    ⟪u, v⟫ = ⟪u, eX cfg⟫ * ⟪v, eX cfg⟫ + ⟪u, eY cfg⟫ * ⟪v, eY cfg⟫ :=
  inner_coord (eX_inner cfg) (eX_eY_inner cfg) (eY_inner cfg) u v

lemma coords_inj {p₁ p₂ : EuclideanSpace ℝ (Fin 2)}
    (h1 : ⟪p₁ -ᵥ cfg.H, eX cfg⟫ = ⟪p₂ -ᵥ cfg.H, eX cfg⟫)
    (h2 : ⟪p₁ -ᵥ cfg.H, eY cfg⟫ = ⟪p₂ -ᵥ cfg.H, eY cfg⟫) : p₁ = p₂ :=
  eq_of_coords (eX_inner cfg) (eX_eY_inner cfg) (eY_inner cfg) h1 h2

lemma dist_c (p₁ p₂ : EuclideanSpace ℝ (Fin 2)) :
    dist p₁ p₂ ^ 2 = (⟪p₁ -ᵥ cfg.H, eX cfg⟫ - ⟪p₂ -ᵥ cfg.H, eX cfg⟫) ^ 2 +
      (⟪p₁ -ᵥ cfg.H, eY cfg⟫ - ⟪p₂ -ᵥ cfg.H, eY cfg⟫) ^ 2 :=
  dist_sq (eX_inner cfg) (eX_eY_inner cfg) (eY_inner cfg) cfg.H p₁ p₂

/-- `a = dist A H > 0`: the y-coordinate of A. -/
noncomputable def aa : ℝ := dist cfg.A cfg.H

/-- `f`: F has y-coordinate `-f`. -/
noncomputable def ff : ℝ := -⟪cfg.F -ᵥ cfg.H, eY cfg⟫

/-- `m`: the x-coordinate of M. -/
noncomputable def mm : ℝ :=
  (⟪cfg.B -ᵥ cfg.H, eX cfg⟫ + ⟪cfg.C -ᵥ cfg.H, eX cfg⟫) / 2

/-- `w`: half the difference of the x-coordinates of C and B. -/
noncomputable def ww : ℝ :=
  (⟪cfg.C -ᵥ cfg.H, eX cfg⟫ - ⟪cfg.B -ᵥ cfg.H, eX cfg⟫) / 2

lemma aa_pos : 0 < aa cfg := dist_pos.mpr (A_ne_H cfg)

lemma aa_ne : aa cfg ≠ 0 := ne_of_gt (aa_pos cfg)

lemma A_x : ⟪cfg.A -ᵥ cfg.H, eX cfg⟫ = 0 := by
  rw [eX, eY, map_smul, real_inner_smul_right, Orientation.inner_rightAngleRotation_swap,
    Orientation.inner_rightAngleRotation_self, neg_zero, mul_zero]

lemma A_y : ⟪cfg.A -ᵥ cfg.H, eY cfg⟫ = aa cfg := by
  have hne : dist cfg.A cfg.H ≠ 0 := dist_ne_zero.mpr (A_ne_H cfg)
  rw [eY, real_inner_smul_right, real_inner_self_eq_norm_sq, ← dist_eq_norm_vsub, aa]
  field_simp

lemma H_x : ⟪cfg.H -ᵥ cfg.H, eX cfg⟫ = 0 := by rw [vsub_self, inner_zero_left]

lemma H_y : ⟪cfg.H -ᵥ cfg.H, eY cfg⟫ = 0 := by rw [vsub_self, inner_zero_left]

/-- Inner product of a difference, x-component. -/
lemma vsub_x (p₁ p₂ : EuclideanSpace ℝ (Fin 2)) :
    ⟪p₁ -ᵥ p₂, eX cfg⟫ = ⟪p₁ -ᵥ cfg.H, eX cfg⟫ - ⟪p₂ -ᵥ cfg.H, eX cfg⟫ := by
  rw [← inner_sub_left, vsub_sub_vsub_cancel_right]

/-- Inner product of a difference, y-component. -/
lemma vsub_y (p₁ p₂ : EuclideanSpace ℝ (Fin 2)) :
    ⟪p₁ -ᵥ p₂, eY cfg⟫ = ⟪p₁ -ᵥ cfg.H, eY cfg⟫ - ⟪p₂ -ᵥ cfg.H, eY cfg⟫ := by
  rw [← inner_sub_left, vsub_sub_vsub_cancel_right]

lemma BC_y : ⟪cfg.B -ᵥ cfg.H, eY cfg⟫ = ⟪cfg.C -ᵥ cfg.H, eY cfg⟫ := by
  have e0 := cfg.hH1
  rw [inner_c cfg, vsub_x cfg cfg.B cfg.C, vsub_y cfg cfg.B cfg.C, A_x, A_y] at e0
  rw [zero_mul, zero_add] at e0
  have h := mul_eq_zero.mp e0
  rcases h with h | h
  · exact absurd h (aa_ne cfg)
  · exact sub_eq_zero.mp h

lemma BxCx_ne : ⟪cfg.B -ᵥ cfg.H, eX cfg⟫ ≠ ⟪cfg.C -ᵥ cfg.H, eX cfg⟫ := by
  intro h
  exact B_ne_C cfg (coords_inj cfg h (BC_y cfg))

lemma F_x : ⟪cfg.F -ᵥ cfg.H, eX cfg⟫ = 0 := by
  have e0 := cfg.hF2
  rw [inner_c cfg, vsub_x cfg cfg.A cfg.F, vsub_y cfg cfg.A cfg.F,
    vsub_x cfg cfg.B cfg.C, vsub_y cfg cfg.B cfg.C, A_x, A_y, BC_y] at e0
  rw [sub_self, mul_zero, add_zero, zero_sub, neg_mul, neg_eq_zero] at e0
  have hne : ⟪cfg.B -ᵥ cfg.H, eX cfg⟫ - ⟪cfg.C -ᵥ cfg.H, eX cfg⟫ ≠ 0 :=
    sub_ne_zero.mpr (BxCx_ne cfg)
  rcases mul_eq_zero.mp e0 with h | h
  · exact h
  · exact absurd h hne

lemma F_mem : cfg.F ∈ line[ℝ, cfg.B, cfg.C] :=
  Collinear.mem_affineSpan_of_mem_of_ne cfg.hF1 (by simp) (by simp) (by simp) (B_ne_C cfg)

lemma F_y : ⟪cfg.F -ᵥ cfg.H, eY cfg⟫ = ⟪cfg.B -ᵥ cfg.H, eY cfg⟫ := by
  have hv : cfg.F -ᵥ cfg.B ∈ ℝ ∙ (cfg.B -ᵥ cfg.C) := by
    have h1 : cfg.F -ᵥ cfg.B ∈ vectorSpan ℝ ({cfg.B, cfg.C} : Set _) :=
      vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan (F_mem cfg)
        (left_mem_affineSpan_pair ℝ cfg.B cfg.C)
    rwa [vectorSpan_pair] at h1
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hv
  have e := congrArg (⟪·, eY cfg⟫) ht
  rw [real_inner_smul_left, vsub_y cfg cfg.B cfg.C, vsub_y cfg cfg.F cfg.B, ← BC_y cfg,
    sub_self, mul_zero] at e
  exact sub_eq_zero.mp e.symm

lemma F_y' : ⟪cfg.F -ᵥ cfg.H, eY cfg⟫ = -ff cfg := by rw [ff, neg_neg]

lemma B_y : ⟪cfg.B -ᵥ cfg.H, eY cfg⟫ = -ff cfg := by rw [← F_y cfg, F_y']

lemma C_y : ⟪cfg.C -ᵥ cfg.H, eY cfg⟫ = -ff cfg := by rw [← BC_y cfg, B_y]

lemma M_x : ⟪cfg.M -ᵥ cfg.H, eX cfg⟫ = mm cfg := by
  have hmid : cfg.M -ᵥ cfg.H = midpoint ℝ (cfg.B -ᵥ cfg.H) (cfg.C -ᵥ cfg.H) := by
    rw [cfg.hM]
    nth_rw 1 [← midpoint_self ℝ cfg.H]
    rw [midpoint_vsub_midpoint]
  rw [midpoint_eq_smul_add] at hmid
  rw [hmid, show (⅟2 : ℝ) = 1 / 2 from by norm_num, real_inner_smul_left, inner_add_left, mm]
  ring

lemma M_y : ⟪cfg.M -ᵥ cfg.H, eY cfg⟫ = -ff cfg := by
  have hmid : cfg.M -ᵥ cfg.H = midpoint ℝ (cfg.B -ᵥ cfg.H) (cfg.C -ᵥ cfg.H) := by
    rw [cfg.hM]
    nth_rw 1 [← midpoint_self ℝ cfg.H]
    rw [midpoint_vsub_midpoint]
  rw [midpoint_eq_smul_add] at hmid
  rw [hmid, show (⅟2 : ℝ) = 1 / 2 from by norm_num, real_inner_smul_left, inner_add_left,
    B_y, C_y]
  ring

lemma B_x : ⟪cfg.B -ᵥ cfg.H, eX cfg⟫ = mm cfg - ww cfg := by rw [mm, ww]; ring

lemma C_x : ⟪cfg.C -ᵥ cfg.H, eX cfg⟫ = mm cfg + ww cfg := by rw [mm, ww]; ring

lemma ww_sq : (ww cfg)^2 = (mm cfg)^2 + ff cfg * (ff cfg + aa cfg) := by
  have e0 := cfg.hH2
  rw [inner_c cfg, vsub_x cfg cfg.C cfg.A, vsub_y cfg cfg.C cfg.A, A_x, A_y,
    B_y, C_y, B_x, C_x] at e0
  linear_combination -e0

lemma fa_pos : 0 < ff cfg + aa cfg := by
  have hpos := inner_pos_of_angle_lt (angleA_lt cfg)
  rw [inner_c cfg, vsub_x cfg cfg.B cfg.A, vsub_y cfg cfg.B cfg.A,
    vsub_x cfg cfg.C cfg.A, vsub_y cfg cfg.C cfg.A, A_x, A_y, B_y, C_y, B_x, C_x] at hpos
  have hww := ww_sq cfg
  nlinarith [hpos, aa_pos cfg]

lemma BxCx_neg : ⟪cfg.B -ᵥ cfg.H, eX cfg⟫ * ⟪cfg.C -ᵥ cfg.H, eX cfg⟫ < 0 := by
  have hB := inner_pos_of_angle_lt (angleB_lt cfg)
  rw [inner_c cfg, vsub_x cfg cfg.C cfg.B, vsub_y cfg cfg.C cfg.B,
    vsub_x cfg cfg.A cfg.B, vsub_y cfg cfg.A cfg.B, A_x, A_y, B_y, C_y] at hB
  have hC := inner_pos_of_angle_lt (angleC_lt cfg)
  rw [inner_c cfg, vsub_x cfg cfg.A cfg.C, vsub_y cfg cfg.A cfg.C,
    vsub_x cfg cfg.B cfg.C, vsub_y cfg cfg.B cfg.C, A_x, A_y, B_y, C_y] at hC
  rw [sub_self, zero_mul, add_zero] at hB
  rw [sub_self, mul_zero, add_zero] at hC
  have hd : ⟪cfg.B -ᵥ cfg.H, eX cfg⟫ - ⟪cfg.C -ᵥ cfg.H, eX cfg⟫ ≠ 0 :=
    sub_ne_zero.mpr (BxCx_ne cfg)
  nlinarith [mul_pos hB hC, sq_pos_of_ne_zero hd]

lemma ff_pos : 0 < ff cfg := by
  have h := BxCx_neg cfg
  rw [B_x, C_x] at h
  have hww := ww_sq cfg
  have hfa := fa_pos cfg
  nlinarith [h, hww, hfa]

lemma mw_neg : mm cfg * ww cfg < 0 := by
  have hsq : dist cfg.A cfg.C ^ 2 < dist cfg.A cfg.B ^ 2 := by
    rw [sq_lt_sq₀ dist_nonneg dist_nonneg]
    exact cfg.hABAC
  rw [dist_c, dist_c, A_x, A_y, B_y, C_y, B_x, C_x] at hsq
  nlinarith [hsq]

lemma mm_ne : mm cfg ≠ 0 := by
  have h := mw_neg cfg
  exact left_ne_zero_of_mul (ne_of_lt h)

lemma ww_ne : ww cfg ≠ 0 := by
  have h := mw_neg cfg
  exact right_ne_zero_of_mul (ne_of_lt h)

lemma O_x : ⟪cfg.O -ᵥ cfg.H, eX cfg⟫ = mm cfg := by
  have hsq : dist cfg.O cfg.B = dist cfg.O cfg.C := cfg.hOB.trans cfg.hOC.symm
  have hsq2 : dist cfg.O cfg.B ^ 2 = dist cfg.O cfg.C ^ 2 := congrArg (· ^ 2) hsq
  rw [dist_c, dist_c, B_y, C_y] at hsq2
  have h1 : (⟪cfg.C -ᵥ cfg.H, eX cfg⟫ - ⟪cfg.B -ᵥ cfg.H, eX cfg⟫) *
        (2 * ⟪cfg.O -ᵥ cfg.H, eX cfg⟫)
      = (⟪cfg.C -ᵥ cfg.H, eX cfg⟫ - ⟪cfg.B -ᵥ cfg.H, eX cfg⟫) *
        (⟪cfg.C -ᵥ cfg.H, eX cfg⟫ + ⟪cfg.B -ᵥ cfg.H, eX cfg⟫) := by
    linear_combination hsq2
  have hne : ⟪cfg.C -ᵥ cfg.H, eX cfg⟫ - ⟪cfg.B -ᵥ cfg.H, eX cfg⟫ ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (BxCx_ne cfg))
  have h2 := mul_left_cancel₀ hne h1
  rw [mm]
  linarith

lemma O_y : ⟪cfg.O -ᵥ cfg.H, eY cfg⟫ = (aa cfg - 2 * ff cfg) / 2 := by
  have hsq : dist cfg.O cfg.A = dist cfg.O cfg.B := cfg.hOA.trans cfg.hOB.symm
  have hsq2 : dist cfg.O cfg.A ^ 2 = dist cfg.O cfg.B ^ 2 := congrArg (· ^ 2) hsq
  rw [dist_c, dist_c, A_x, A_y, B_y, B_x, O_x] at hsq2
  have hww := ww_sq cfg
  have h1 : (aa cfg + ff cfg) * (2 * ⟪cfg.O -ᵥ cfg.H, eY cfg⟫) =
      (aa cfg + ff cfg) * (aa cfg - 2 * ff cfg) := by
    linear_combination -hsq2 - hww
  have hne : aa cfg + ff cfg ≠ 0 := by
    rw [add_comm]
    exact ne_of_gt (fa_pos cfg)
  have h2 := mul_left_cancel₀ hne h1
  linarith

/-- The inner-product equation for Q from ∠HQA = 90°. -/
lemma Q_inner : ⟪cfg.Q -ᵥ cfg.H, eX cfg⟫ ^ 2 + ⟪cfg.Q -ᵥ cfg.H, eY cfg⟫ ^ 2 =
    aa cfg * ⟪cfg.Q -ᵥ cfg.H, eY cfg⟫ := by
  have h := cfg.hQangle
  unfold EuclideanGeometry.angle at h
  have hi := (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two _ _).mpr h
  rw [inner_c cfg, vsub_x cfg cfg.H cfg.Q, vsub_y cfg cfg.H cfg.Q,
    vsub_x cfg cfg.A cfg.Q, vsub_y cfg cfg.A cfg.Q, A_x, A_y, H_x, H_y] at hi
  linear_combination hi

/-- The circle equation for Q from Q ∈ Γ. -/
lemma Q_gamma : ⟪cfg.Q -ᵥ cfg.H, eX cfg⟫ ^ 2 + ⟪cfg.Q -ᵥ cfg.H, eY cfg⟫ ^ 2 -
    2 * mm cfg * ⟪cfg.Q -ᵥ cfg.H, eX cfg⟫ - (aa cfg - 2 * ff cfg) * ⟪cfg.Q -ᵥ cfg.H, eY cfg⟫ -
    2 * aa cfg * ff cfg = 0 := by
  have hsq : dist cfg.O cfg.Q = dist cfg.O cfg.A := cfg.hOQ.trans cfg.hOA.symm
  have hsq2 : dist cfg.O cfg.Q ^ 2 = dist cfg.O cfg.A ^ 2 := congrArg (· ^ 2) hsq
  rw [dist_c, dist_c, O_x, O_y, A_x, A_y] at hsq2
  linear_combination hsq2

lemma Q_ne_A : ¬ (⟪cfg.Q -ᵥ cfg.H, eX cfg⟫ = 0 ∧ ⟪cfg.Q -ᵥ cfg.H, eY cfg⟫ = aa cfg) := by
  rintro ⟨h1, h2⟩
  exact cfg.hQA (coords_inj cfg (by rw [h1, A_x]) (by rw [h2, A_y]))

/-- The coordinates of Q. -/
lemma Q_coords : ⟪cfg.Q -ᵥ cfg.H, eX cfg⟫ =
      -mm cfg * aa cfg * ff cfg / (mm cfg ^ 2 + ff cfg ^ 2) ∧
    ⟪cfg.Q -ᵥ cfg.H, eY cfg⟫ = aa cfg * ff cfg ^ 2 / (mm cfg ^ 2 + ff cfg ^ 2) :=
  Q_char (aa_pos cfg) (ff_pos cfg) (Q_inner cfg) (Q_gamma cfg) (Q_ne_A cfg)

/-- The inner-product equation for K from ∠HKQ = 90°. -/
lemma K_inner : ⟪cfg.K -ᵥ cfg.H, eX cfg⟫ ^ 2 + ⟪cfg.K -ᵥ cfg.H, eY cfg⟫ ^ 2 =
    ⟪cfg.K -ᵥ cfg.H, eX cfg⟫ * ⟪cfg.Q -ᵥ cfg.H, eX cfg⟫ +
    ⟪cfg.K -ᵥ cfg.H, eY cfg⟫ * ⟪cfg.Q -ᵥ cfg.H, eY cfg⟫ := by
  have h := cfg.hKangle
  unfold EuclideanGeometry.angle at h
  have hi := (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two _ _).mpr h
  rw [inner_c cfg, vsub_x cfg cfg.H cfg.K, vsub_y cfg cfg.H cfg.K,
    vsub_x cfg cfg.Q cfg.K, vsub_y cfg cfg.Q cfg.K, H_x, H_y] at hi
  linear_combination hi

/-- The circle equation for K from K ∈ Γ. -/
lemma K_gamma : ⟪cfg.K -ᵥ cfg.H, eX cfg⟫ ^ 2 + ⟪cfg.K -ᵥ cfg.H, eY cfg⟫ ^ 2 -
    2 * mm cfg * ⟪cfg.K -ᵥ cfg.H, eX cfg⟫ - (aa cfg - 2 * ff cfg) * ⟪cfg.K -ᵥ cfg.H, eY cfg⟫ -
    2 * aa cfg * ff cfg = 0 := by
  have hsq : dist cfg.O cfg.K = dist cfg.O cfg.A := cfg.hOK.trans cfg.hOA.symm
  have hsq2 : dist cfg.O cfg.K ^ 2 = dist cfg.O cfg.A ^ 2 := congrArg (· ^ 2) hsq
  rw [dist_c, dist_c, O_x, O_y, A_x, A_y] at hsq2
  linear_combination hsq2

lemma K_ne_Q : ¬ (⟪cfg.K -ᵥ cfg.H, eX cfg⟫ = ⟪cfg.Q -ᵥ cfg.H, eX cfg⟫ ∧
    ⟪cfg.K -ᵥ cfg.H, eY cfg⟫ = ⟪cfg.Q -ᵥ cfg.H, eY cfg⟫) := by
  rintro ⟨h1, h2⟩
  exact cfg.hKQ (coords_inj cfg h1 h2)

/-- The coordinates of K. -/
lemma K_coords : ⟪cfg.K -ᵥ cfg.H, eX cfg⟫ =
      -2 * aa cfg * ff cfg * mm cfg * (aa cfg * ff cfg + 2 * (mm cfg ^ 2 + ff cfg ^ 2)) /
      (aa cfg ^ 2 * mm cfg ^ 2 + 4 * (mm cfg ^ 2 + ff cfg ^ 2) ^ 2) ∧
    ⟪cfg.K -ᵥ cfg.H, eY cfg⟫ =
      -2 * aa cfg * ff cfg * (aa cfg * mm cfg ^ 2 - 2 * ff cfg * (mm cfg ^ 2 + ff cfg ^ 2)) /
      (aa cfg ^ 2 * mm cfg ^ 2 + 4 * (mm cfg ^ 2 + ff cfg ^ 2) ^ 2) :=
  K_char (aa_pos cfg) (ff_pos cfg) (mm_ne cfg) (Q_coords cfg).1 (Q_coords cfg).2
    (K_inner cfg) (K_gamma cfg) (K_ne_Q cfg)

/-- The remaining nondegeneracy: K does not lie on line BC. -/
lemma U_ne : aa cfg ^ 2 * mm cfg ^ 2 - 4 * aa cfg * ff cfg * (mm cfg ^ 2 + ff cfg ^ 2) -
    4 * (mm cfg ^ 2 + ff cfg ^ 2) ^ 2 ≠ 0 := by
  intro hU0
  have hT : (0:ℝ) < aa cfg ^ 2 * mm cfg ^ 2 + 4 * (mm cfg ^ 2 + ff cfg ^ 2) ^ 2 := by
    have h1 : 0 < aa cfg ^ 2 * mm cfg ^ 2 :=
      mul_pos (pow_pos (aa_pos cfg) 2) (sq_pos_of_ne_zero (mm_ne cfg))
    have h2 : 0 ≤ 4 * (mm cfg ^ 2 + ff cfg ^ 2) ^ 2 := by positivity
    linarith
  have hS : (0:ℝ) < mm cfg ^ 2 + ff cfg ^ 2 := by
    have h1 : 0 < ff cfg ^ 2 := pow_pos (ff_pos cfg) 2
    have h2 : 0 ≤ mm cfg ^ 2 := by positivity
    linarith
  have hKyf : ⟪cfg.K -ᵥ cfg.H, eY cfg⟫ + ff cfg =
      -ff cfg * (aa cfg ^ 2 * mm cfg ^ 2 - 4 * aa cfg * ff cfg * (mm cfg ^ 2 + ff cfg ^ 2) -
        4 * (mm cfg ^ 2 + ff cfg ^ 2) ^ 2) /
        (aa cfg ^ 2 * mm cfg ^ 2 + 4 * (mm cfg ^ 2 + ff cfg ^ 2) ^ 2) := by
    rw [(K_coords cfg).2]
    field_simp [ne_of_gt hS, ne_of_gt hT]
    ring
  rw [hU0, mul_zero, zero_div] at hKyf
  have hKy : ⟪cfg.K -ᵥ cfg.H, eY cfg⟫ = -ff cfg := by linarith [hKyf]
  have hKg := K_gamma cfg
  rw [hKy] at hKg
  have hfact : (⟪cfg.K -ᵥ cfg.H, eX cfg⟫ - (mm cfg - ww cfg)) *
      (⟪cfg.K -ᵥ cfg.H, eX cfg⟫ - (mm cfg + ww cfg)) = 0 := by
    linear_combination hKg - ww_sq cfg
  rcases mul_eq_zero.mp hfact with h1 | h1
  · have hx : ⟪cfg.K -ᵥ cfg.H, eX cfg⟫ = ⟪cfg.B -ᵥ cfg.H, eX cfg⟫ := by
      rw [B_x]
      linarith [h1]
    exact cfg.hKB (coords_inj cfg hx (by rw [hKy, B_y]))
  · have hx : ⟪cfg.K -ᵥ cfg.H, eX cfg⟫ = ⟪cfg.C -ᵥ cfg.H, eX cfg⟫ := by
      rw [C_x]
      linarith [h1]
    exact cfg.hKC (coords_inj cfg hx (by rw [hKy, C_y]))

/-- The center of the first circle: since ∠HKQ = 90°, the circumcircle of KQH
is the circle with diameter HQ. -/
noncomputable def O1 : EuclideanSpace ℝ (Fin 2) := midpoint ℝ cfg.H cfg.Q

/-- The radius of the first circle. -/
noncomputable def r1 : ℝ := dist cfg.H cfg.Q / 2

lemma O1_x : ⟪O1 cfg -ᵥ cfg.H, eX cfg⟫ = ⟪cfg.Q -ᵥ cfg.H, eX cfg⟫ / 2 := by
  have hmid : O1 cfg -ᵥ cfg.H = midpoint ℝ (cfg.H -ᵥ cfg.H) (cfg.Q -ᵥ cfg.H) := by
    rw [O1]
    nth_rw 2 [← midpoint_self ℝ cfg.H]
    rw [midpoint_vsub_midpoint]
  rw [midpoint_eq_smul_add] at hmid
  rw [hmid, show (⅟2 : ℝ) = 1 / 2 from by norm_num, real_inner_smul_left, inner_add_left,
    H_x]
  ring

lemma O1_y : ⟪O1 cfg -ᵥ cfg.H, eY cfg⟫ = ⟪cfg.Q -ᵥ cfg.H, eY cfg⟫ / 2 := by
  have hmid : O1 cfg -ᵥ cfg.H = midpoint ℝ (cfg.H -ᵥ cfg.H) (cfg.Q -ᵥ cfg.H) := by
    rw [O1]
    nth_rw 2 [← midpoint_self ℝ cfg.H]
    rw [midpoint_vsub_midpoint]
  rw [midpoint_eq_smul_add] at hmid
  rw [hmid, show (⅟2 : ℝ) = 1 / 2 from by norm_num, real_inner_smul_left, inner_add_left,
    H_y]
  ring

lemma dist_HQ_sq : dist cfg.H cfg.Q ^ 2 =
    ⟪cfg.Q -ᵥ cfg.H, eX cfg⟫ ^ 2 + ⟪cfg.Q -ᵥ cfg.H, eY cfg⟫ ^ 2 := by
  rw [dist_c, H_x, H_y]
  ring

lemma dist_Q_O1 : dist cfg.Q (O1 cfg) = r1 cfg := by
  have hsq : dist cfg.Q (O1 cfg) ^ 2 = (r1 cfg) ^ 2 := by
    rw [r1, dist_c, O1_x, O1_y]
    linear_combination -dist_HQ_sq cfg / 4
  exact (sq_eq_sq₀ dist_nonneg (by rw [r1]; positivity)).mp hsq

lemma dist_H_O1 : dist cfg.H (O1 cfg) = r1 cfg := by
  have hsq : dist cfg.H (O1 cfg) ^ 2 = (r1 cfg) ^ 2 := by
    rw [r1, dist_c, O1_x, O1_y, H_x, H_y]
    linear_combination -dist_HQ_sq cfg / 4
  exact (sq_eq_sq₀ dist_nonneg (by rw [r1]; positivity)).mp hsq

lemma dist_K_O1 : dist cfg.K (O1 cfg) = r1 cfg := by
  have hsq : dist cfg.K (O1 cfg) ^ 2 = (r1 cfg) ^ 2 := by
    rw [r1, dist_c, O1_x, O1_y]
    linear_combination K_inner cfg - dist_HQ_sq cfg / 4
  exact (sq_eq_sq₀ dist_nonneg (by rw [r1]; positivity)).mp hsq

/-- The second circle coefficient: its center is (m/2, -E2/2). -/
noncomputable def E2 : ℝ :=
  (ff cfg ^ 2 + mm cfg * ⟪cfg.K -ᵥ cfg.H, eX cfg⟫ -
    (⟪cfg.K -ᵥ cfg.H, eX cfg⟫ * ⟪cfg.Q -ᵥ cfg.H, eX cfg⟫ +
     ⟪cfg.K -ᵥ cfg.H, eY cfg⟫ * ⟪cfg.Q -ᵥ cfg.H, eY cfg⟫)) /
    (⟪cfg.K -ᵥ cfg.H, eY cfg⟫ + ff cfg)

lemma Ky_f_ne : ⟪cfg.K -ᵥ cfg.H, eY cfg⟫ + ff cfg ≠ 0 :=
  Ky_add_f_ne (aa_pos cfg) (ff_pos cfg) (U_ne cfg) (K_coords cfg).2

/-- The center of the second circle. -/
noncomputable def O2 : EuclideanSpace ℝ (Fin 2) :=
  ((mm cfg / 2) • eX cfg + (-(E2 cfg) / 2) • eY cfg) +ᵥ cfg.H

/-- The radius of the second circle. -/
noncomputable def r2 : ℝ := dist cfg.F (O2 cfg)

lemma eY_eX_inner : ⟪eY cfg, eX cfg⟫ = 0 := by
  rw [real_inner_comm (eX cfg) (eY cfg)]
  exact eX_eY_inner cfg

lemma O2_x : ⟪O2 cfg -ᵥ cfg.H, eX cfg⟫ = mm cfg / 2 := by
  have hv : O2 cfg -ᵥ cfg.H = (mm cfg / 2) • eX cfg + (-(E2 cfg) / 2) • eY cfg := by
    rw [O2, vadd_vsub]
  rw [hv, inner_add_left, real_inner_smul_left, real_inner_smul_left, eX_inner,
    eY_eX_inner]
  ring

lemma O2_y : ⟪O2 cfg -ᵥ cfg.H, eY cfg⟫ = -(E2 cfg) / 2 := by
  have hv : O2 cfg -ᵥ cfg.H = (mm cfg / 2) • eX cfg + (-(E2 cfg) / 2) • eY cfg := by
    rw [O2, vadd_vsub]
  rw [hv, inner_add_left, real_inner_smul_left, real_inner_smul_left, eY_inner,
    eX_eY_inner]
  ring

lemma dist_F_O2 : dist cfg.F (O2 cfg) = r2 cfg := rfl

lemma dist_M_O2 : dist cfg.M (O2 cfg) = r2 cfg := by
  have hsq : dist cfg.M (O2 cfg) ^ 2 = dist cfg.F (O2 cfg) ^ 2 := by
    rw [dist_c, dist_c, O2_x, O2_y, F_x, F_y', M_x, M_y]
    ring
  rw [r2]
  exact (sq_eq_sq₀ dist_nonneg dist_nonneg).mp hsq

lemma E2_key : E2 cfg * (⟪cfg.K -ᵥ cfg.H, eY cfg⟫ + ff cfg) =
    ff cfg ^ 2 + mm cfg * ⟪cfg.K -ᵥ cfg.H, eX cfg⟫ -
    (⟪cfg.K -ᵥ cfg.H, eX cfg⟫ ^ 2 + ⟪cfg.K -ᵥ cfg.H, eY cfg⟫ ^ 2) := by
  rw [E2, div_mul_cancel₀ _ (Ky_f_ne cfg), K_inner cfg]

lemma dist_K_O2 : dist cfg.K (O2 cfg) = r2 cfg := by
  have hsq : dist cfg.K (O2 cfg) ^ 2 = dist cfg.F (O2 cfg) ^ 2 := by
    rw [dist_c, dist_c, O2_x, O2_y, F_x, F_y']
    linear_combination E2_key cfg
  rw [r2]
  exact (sq_eq_sq₀ dist_nonneg dist_nonneg).mp hsq

/-- Vectors are equal iff their coordinates agree. -/
lemma vec_eq_of_inner (u v : EuclideanSpace ℝ (Fin 2))
    (h1 : ⟪u, eX cfg⟫ = ⟪v, eX cfg⟫) (h2 : ⟪u, eY cfg⟫ = ⟪v, eY cfg⟫) : u = v := by
  have du := coord_decomp (eX_inner cfg) (eX_eY_inner cfg) (eY_inner cfg) u
  have dv := coord_decomp (eX_inner cfg) (eX_eY_inner cfg) (eY_inner cfg) v
  rw [du, h1, h2, ← dv]

/-- The two centers and K are collinear, with nontrivial ratio. -/
lemma lam_rel : ∃ lam : ℝ, lam ≠ 0 ∧ O2 cfg -ᵥ O1 cfg = lam • (cfg.K -ᵥ O1 cfg) := by
  obtain ⟨lam, hlam, g1, g2⟩ := finale (aa_pos cfg) (ff_pos cfg) (mm_ne cfg) (U_ne cfg)
    (Q_coords cfg).1 (Q_coords cfg).2 (K_coords cfg).1 (K_coords cfg).2
  refine ⟨lam, hlam, ?_⟩
  apply vec_eq_of_inner cfg
  · rw [vsub_x cfg (O2 cfg) (O1 cfg), O2_x, O1_x, real_inner_smul_left,
      vsub_x cfg cfg.K (O1 cfg), O1_x]
    exact g1
  · rw [vsub_y cfg (O2 cfg) (O1 cfg), O2_y, O1_y, real_inner_smul_left,
      vsub_y cfg cfg.K (O1 cfg), O1_y]
    exact g2

/-- The triangle KQH. -/
noncomputable def t1 : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)) :=
  ⟨![cfg.K, cfg.Q, cfg.H], cfg.hKQH⟩

/-- The triangle FKM. -/
noncomputable def t2 : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)) :=
  ⟨![cfg.F, cfg.K, cfg.M], cfg.hFKM⟩

lemma span_top1 : affineSpan ℝ (Set.range (t1 cfg).points) = ⊤ := by
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) + 1 := by
    rw [Fintype.card_fin, (Fact.out : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2)]
  exact (t1 cfg).independent.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr hcard

lemma span_top2 : affineSpan ℝ (Set.range (t2 cfg).points) = ⊤ := by
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) + 1 := by
    rw [Fintype.card_fin, (Fact.out : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2)]
  exact (t2 cfg).independent.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr hcard

lemma dist_t1 : ∀ i, dist ((t1 cfg).points i) (O1 cfg) = r1 cfg := by
  intro i
  fin_cases i
  · exact dist_K_O1 cfg
  · exact dist_Q_O1 cfg
  · exact dist_H_O1 cfg

lemma dist_t2 : ∀ i, dist ((t2 cfg).points i) (O2 cfg) = r2 cfg := by
  intro i
  fin_cases i
  · exact dist_F_O2 cfg
  · exact dist_K_O2 cfg
  · exact dist_M_O2 cfg

lemma O1_circumcenter : O1 cfg = (t1 cfg).circumcenter :=
  Affine.Simplex.eq_circumcenter_of_dist_eq (t1 cfg) (span_top1 cfg ▸ AffineSubspace.mem_top ℝ _ _)
    (dist_t1 cfg)

lemma r1_circumradius : r1 cfg = (t1 cfg).circumradius :=
  Affine.Simplex.eq_circumradius_of_dist_eq (t1 cfg) (span_top1 cfg ▸ AffineSubspace.mem_top ℝ _ _)
    (dist_t1 cfg)

lemma O2_circumcenter : O2 cfg = (t2 cfg).circumcenter :=
  Affine.Simplex.eq_circumcenter_of_dist_eq (t2 cfg) (span_top2 cfg ▸ AffineSubspace.mem_top ℝ _ _)
    (dist_t2 cfg)

lemma r2_circumradius : r2 cfg = (t2 cfg).circumradius :=
  Affine.Simplex.eq_circumradius_of_dist_eq (t2 cfg) (span_top2 cfg ▸ AffineSubspace.mem_top ℝ _ _)
    (dist_t2 cfg)

/-- The conclusion: the two circumcircles meet only at K, i.e. are tangent. -/
theorem result : ((t1 cfg).circumsphere : Set (EuclideanSpace ℝ (Fin 2))) ∩
    ((t2 cfg).circumsphere : Set (EuclideanSpace ℝ (Fin 2))) = {cfg.K} := by
  ext X
  simp only [Set.mem_inter_iff, EuclideanGeometry.Sphere.mem_coe, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    rw [EuclideanGeometry.mem_sphere, Affine.Simplex.circumsphere_center, ← O1_circumcenter,
      Affine.Simplex.circumsphere_radius, ← r1_circumradius, ← dist_K_O1] at h1
    rw [EuclideanGeometry.mem_sphere, Affine.Simplex.circumsphere_center, ← O2_circumcenter,
      Affine.Simplex.circumsphere_radius, ← r2_circumradius, ← dist_K_O2] at h2
    obtain ⟨lam, hlam, hvec⟩ := lam_rel cfg
    exact eq_of_mem_both_circles ⟨lam, hlam, hvec⟩ h1 h2
  · intro hX
    rw [hX]
    constructor
    · rw [EuclideanGeometry.mem_sphere, Affine.Simplex.circumsphere_center, ← O1_circumcenter,
        Affine.Simplex.circumsphere_radius, ← r1_circumradius]
      exact dist_K_O1 cfg
    · rw [EuclideanGeometry.mem_sphere, Affine.Simplex.circumsphere_center, ← O2_circumcenter,
        Affine.Simplex.circumsphere_radius, ← r2_circumradius]
      exact dist_K_O2 cfg

end Cfg

snip end

problem imo2015_p3
    (A B C H F M Q K O : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hAcuteA : ∠ B A C < Real.pi / 2)
    (hAcuteB : ∠ C B A < Real.pi / 2)
    (hAcuteC : ∠ A C B < Real.pi / 2)
    (hABAC : dist A C < dist A B)
    (hH1 : ⟪A -ᵥ H, B -ᵥ C⟫ = 0)
    (hH2 : ⟪B -ᵥ H, C -ᵥ A⟫ = 0)
    (hF1 : Collinear ℝ {F, B, C})
    (hF2 : ⟪A -ᵥ F, B -ᵥ C⟫ = 0)
    (hM : M = midpoint ℝ B C)
    (hOA : dist O A = r) (hOB : dist O B = r) (hOC : dist O C = r)
    (hOQ : dist O Q = r)
    (hQangle : ∠ H Q A = Real.pi / 2)
    (hOK : dist O K = r)
    (hKangle : ∠ H K Q = Real.pi / 2)
    (hKQH : AffineIndependent ℝ ![K, Q, H])
    (hFKM : AffineIndependent ℝ ![F, K, M])
    (hQA : Q ≠ A) (hQB : Q ≠ B) (hQC : Q ≠ C)
    (hKA : K ≠ A) (hKB : K ≠ B) (hKC : K ≠ C) (hKQ : K ≠ Q) :
    let t₁ : Affine.Triangle ℝ _ := ⟨![K, Q, H], hKQH⟩
    let t₂ : Affine.Triangle ℝ _ := ⟨![F, K, M], hFKM⟩
    ((t₁.circumsphere : Set _) ∩ (t₂.circumsphere : Set _)) = {K} :=
  (⟨A, B, C, H, F, M, Q, K, O, r, hABC, hAcuteA, hAcuteB, hAcuteC, hABAC, hH1, hH2, hF1,
    hF2, hM, hOA, hOB, hOC, hOQ, hQangle, hOK, hKangle, hKQH, hFKM, hQA, hQB, hQC, hKA,
    hKB, hKC, hKQ⟩ : Cfg).result


end Imo2015P3
