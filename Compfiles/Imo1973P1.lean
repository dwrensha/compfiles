/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1973, Problem 1

Let $OP_1, OP_2, \ldots, OP_{2n+1}$ be unit vectors in the plane such that
$P_1, P_2, \ldots, P_{2n+1}$ all lie on the same side of a line through $O$.
Prove that $|OP_1 + OP_2 + \cdots + OP_{2n+1}| \geq 1$.

We formalize "all the points lie on the same side of a line through $O$" as:
there exists a unit vector $u$ (a normal vector of the line) such that
$\langle u, OP_i \rangle \geq 0$ for all $i$. This closed half-plane
formulation is a priori stronger than the hypothesis of the problem.
-/

namespace Imo1973P1

open scoped RealInnerProductSpace

/-- The Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Rotation by 90 degrees counterclockwise: the map $(a, b) \mapsto (-b, a)$. -/
def rot90 (v : Plane) : Plane := !₂[-v 1, v 0]

/-- The angle of a vector in the oriented orthonormal basis $(u, u')$, where
`u'` is `u` rotated by 90 degrees. -/
noncomputable def angleOf (u v : Plane) : ℝ := Real.arcsin ⟪rot90 u, v⟫

snip begin

/-- The squared norm in coordinates. -/
theorem norm_sq (v : Plane) : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
  simp [Real.norm_eq_abs, sq_abs]

/-- The inner product in coordinates. -/
theorem inner_coord (v w : Plane) : ⟪v, w⟫ = v 0 * w 0 + v 1 * w 1 := by
  have h : ⟪v, w⟫ = ⟪v 0, w 0⟫ + ⟪v 1, w 1⟫ := by
    rw [PiLp.inner_apply, Fin.sum_univ_two]
  rw [h]
  simp [inner]
  ring

/-- The 90° rotation is an isometry. -/
theorem norm_rot90 (v : Plane) : ‖rot90 v‖ = ‖v‖ := by
  have h : ‖rot90 v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [norm_sq, norm_sq]
    simp [rot90]
    ring
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- Orthonormal basis expansion along a unit vector `u` and its 90° rotation. -/
theorem eq_inner_smul_add_inner_smul_rot90 (u : Plane) (hu : ‖u‖ = 1) (v : Plane) :
    v = ⟪u, v⟫ • u + ⟪rot90 u, v⟫ • rot90 u := by
  have hu2 : (1:ℝ) = u 0 ^ 2 + u 1 ^ 2 := by
    have h := norm_sq u
    rw [hu] at h
    linarith
  ext i
  fin_cases i <;>
    simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, inner_coord, rot90] <;>
    [linear_combination (v 0) * hu2; linear_combination (v 1) * hu2]

/-- The inner product computed in the orthonormal basis $(u, u')$. -/
theorem inner_eq_inner_mul_inner_add (u : Plane) (hu : ‖u‖ = 1) (v w : Plane) :
    ⟪v, w⟫ = ⟪u, v⟫ * ⟪u, w⟫ + ⟪rot90 u, v⟫ * ⟪rot90 u, w⟫ := by
  have hu2 : (1:ℝ) = u 0 ^ 2 + u 1 ^ 2 := by
    have h := norm_sq u
    rw [hu] at h
    linarith
  simp [inner_coord, rot90]
  linear_combination (v 0 * w 0 + v 1 * w 1) * hu2

/-- Cauchy–Schwarz bound for the `u'`-coordinate of a unit vector. -/
theorem inner_rot90_bounds (u : Plane) (hu : ‖u‖ = 1) (v : Plane) (hv : ‖v‖ = 1) :
    -1 ≤ ⟪rot90 u, v⟫ ∧ ⟪rot90 u, v⟫ ≤ 1 := by
  have hcs := abs_real_inner_le_norm (rot90 u) v
  rw [norm_rot90, hu, hv, mul_one] at hcs
  exact ⟨neg_le_of_abs_le hcs, le_of_abs_le hcs⟩

/-- The cosine of the angle of a unit vector in the half-plane is its
`u`-coordinate. -/
theorem cos_angleOf (u : Plane) (hu : ‖u‖ = 1) (v : Plane)
    (hv : ‖v‖ = 1) (h : 0 ≤ ⟪u, v⟫) :
    Real.cos (angleOf u v) = ⟪u, v⟫ := by
  unfold angleOf
  rw [Real.cos_arcsin]
  have h2 : ⟪u, v⟫ ^ 2 + ⟪rot90 u, v⟫ ^ 2 = 1 := by
    have h1 := inner_eq_inner_mul_inner_add u hu v v
    rw [real_inner_self_eq_norm_sq, hv] at h1
    linarith [h1]
  have h3 : (1:ℝ) - ⟪rot90 u, v⟫ ^ 2 = ⟪u, v⟫ ^ 2 := by linarith [h2]
  rw [h3, Real.sqrt_sq h]

/-- The sine of the angle of a unit vector is its `u'`-coordinate. -/
theorem sin_angleOf (u : Plane) (hu : ‖u‖ = 1) (v : Plane) (hv : ‖v‖ = 1) :
    Real.sin (angleOf u v) = ⟪rot90 u, v⟫ :=
  Real.sin_arcsin (inner_rot90_bounds u hu v hv).1 (inner_rot90_bounds u hu v hv).2

/-- The inner product of two unit vectors in the half-plane is the cosine of
the difference of their angles. -/
theorem inner_eq_cos_angleOf_sub (u : Plane) (hu : ‖u‖ = 1) {v w : Plane}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (h1 : 0 ≤ ⟪u, v⟫) (h2 : 0 ≤ ⟪u, w⟫) :
    ⟪v, w⟫ = Real.cos (angleOf u v - angleOf u w) := by
  rw [Real.cos_sub, cos_angleOf u hu v hv h1, cos_angleOf u hu w hw h2,
    sin_angleOf u hu v hv, sin_angleOf u hu w hw]
  exact inner_eq_inner_mul_inner_add u hu v w

/-- A unit vector in the half-plane is determined by its angle. -/
theorem eq_cos_angleOf_smul_add_sin_angleOf_smul (u : Plane) (hu : ‖u‖ = 1) {v : Plane}
    (hv : ‖v‖ = 1) (h : 0 ≤ ⟪u, v⟫) :
    v = Real.cos (angleOf u v) • u + Real.sin (angleOf u v) • rot90 u := by
  rw [cos_angleOf u hu v hv h, sin_angleOf u hu v hv]
  exact eq_inner_smul_add_inner_smul_rot90 u hu v

/-- Sum-to-product bound: if `α ≤ γ ≤ β` and `β - α ≤ π`, then
`0 ≤ cos (γ - α) + cos (β - γ)`. -/
theorem cos_add_cos_nonneg {α β γ : ℝ} (hαγ : α ≤ γ) (hγβ : γ ≤ β)
    (hβα : β ≤ α + Real.pi) :
    0 ≤ Real.cos (γ - α) + Real.cos (β - γ) := by
  rw [Real.cos_add_cos]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hA : 0 ≤ Real.cos ((γ - α + (β - γ)) / 2) := by
    apply Real.cos_nonneg_of_mem_Icc
    refine ⟨by linarith, by linarith⟩
  have hB : 0 ≤ Real.cos ((γ - α - (β - γ)) / 2) := by
    apply Real.cos_nonneg_of_mem_Icc
    refine ⟨by linarith, by linarith⟩
  exact mul_nonneg (mul_nonneg (by norm_num) hA) hB

/-- If `⟪v, w⟫ ≥ 0` then `‖v‖ ≤ ‖v + w‖`. -/
theorem norm_le_norm_add_of_inner_nonneg {v w : Plane} (h : 0 ≤ ⟪v, w⟫) :
    ‖v‖ ≤ ‖v + w‖ := by
  have hsq : ‖v‖ ^ 2 ≤ ‖v + w‖ ^ 2 := by
    rw [norm_add_sq_real]
    have hw : 0 ≤ ‖w‖ ^ 2 := sq_nonneg _
    linarith [h]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- The induction: any `2n+1` unit vectors in a common closed half-plane have
a sum of norm at least `1`. -/
theorem sum_norm_ge_one (n : ℕ) :
    ∀ {ι : Type*} (s : Finset ι) (p : ι → Plane),
      s.card = 2 * n + 1 → ∀ (u : Plane), ‖u‖ = 1 →
        (∀ i ∈ s, 0 ≤ ⟪u, p i⟫) → (∀ i ∈ s, ‖p i‖ = 1) →
          1 ≤ ‖∑ i ∈ s, p i‖ := by
  induction n with
  | zero =>
    classical
    intro ι s p hs u hu hhalf hunit
    obtain ⟨i₀, rfl⟩ := Finset.card_eq_one.mp hs
    rw [Finset.sum_singleton, hunit i₀ (Finset.mem_singleton_self i₀)]
  | succ n ih =>
    classical
    intro ι s p hs u hu hhalf hunit
    have hne : s.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨imin, himin, hmin⟩ :=
      Finset.exists_min_image s (fun i => angleOf u (p i)) hne
    obtain ⟨imax, himax, hmax⟩ :=
      Finset.exists_max_image s (fun i => angleOf u (p i)) hne
    by_cases heq : angleOf u (p imin) = angleOf u (p imax)
    · -- All angles coincide: all vectors are equal and the sum has norm `2n+3`.
      have hall : ∀ i ∈ s, p i = p imin := by
        intro i hi
        have h1 : angleOf u (p i) = angleOf u (p imin) :=
          le_antisymm ((hmax i hi).trans (le_of_eq heq.symm)) (hmin i hi)
        rw [eq_cos_angleOf_smul_add_sin_angleOf_smul u hu (hunit i hi) (hhalf i hi),
          eq_cos_angleOf_smul_add_sin_angleOf_smul u hu (hunit imin himin) (hhalf imin himin),
          h1]
      rw [Finset.sum_eq_card_nsmul hall, hs, ← Nat.cast_smul_eq_nsmul ℝ, norm_smul,
        hunit imin himin, mul_one, Real.norm_of_nonneg (by positivity)]
      exact_mod_cast (by omega : 1 ≤ 2 * (n + 1) + 1)
    · -- The two extreme vectors are distinct: remove them and use the IH.
      have hne2 : imin ≠ imax := by
        intro h
        exact heq (by rw [h])
      have hsub : ({imin, imax} : Finset ι) ⊆ s := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact himin
        · exact himax
      have hcard : (s \ {imin, imax}).card = 2 * n + 1 := by
        rw [Finset.card_sdiff_of_subset hsub, Finset.card_pair hne2, hs]
        omega
      have ih' : 1 ≤ ‖∑ i ∈ s \ {imin, imax}, p i‖ :=
        ih (s \ {imin, imax}) p hcard u hu
          (fun i hi => hhalf i (Finset.sdiff_subset hi))
          (fun i hi => hunit i (Finset.sdiff_subset hi))
      have hsum : ∑ i ∈ s, p i = (∑ i ∈ s \ {imin, imax}, p i) + (p imin + p imax) := by
        rw [← Finset.sum_sdiff hsub, Finset.sum_pair hne2]
      have hinner : 0 ≤ ⟪∑ i ∈ s \ {imin, imax}, p i, p imin + p imax⟫ := by
        rw [sum_inner]
        apply Finset.sum_nonneg
        intro i hi
        have his : i ∈ s := Finset.sdiff_subset hi
        rw [inner_add_right,
          inner_eq_cos_angleOf_sub u hu (hunit i his) (hunit imin himin)
            (hhalf i his) (hhalf imin himin),
          inner_eq_cos_angleOf_sub u hu (hunit i his) (hunit imax himax)
            (hhalf i his) (hhalf imax himax)]
        have hswap : angleOf u (p i) - angleOf u (p imax) =
            -(angleOf u (p imax) - angleOf u (p i)) := by ring
        rw [hswap, Real.cos_neg]
        apply cos_add_cos_nonneg (hmin i his) (hmax i his)
        have h1 := Real.arcsin_le_pi_div_two ⟪rot90 u, p imax⟫
        have h2 := Real.neg_pi_div_two_le_arcsin ⟪rot90 u, p imin⟫
        unfold angleOf
        linarith
      rw [hsum]
      have hle := norm_le_norm_add_of_inner_nonneg hinner
      linarith [ih']

snip end

problem imo1973_p1
    (n : ℕ)
    (p : Fin (2 * n + 1) → Plane)
    (hunit : ∀ i, ‖p i‖ = 1)
    (hside : ∃ u : Plane, ‖u‖ = 1 ∧ ∀ i, 0 ≤ ⟪u, p i⟫) :
    1 ≤ ‖∑ i, p i‖ := by
  obtain ⟨u, hu, hside⟩ := hside
  exact sum_norm_ge_one n Finset.univ p (by simp) u hu
    (fun i _ => hside i) (fun i _ => hunit i)

end Imo1973P1
