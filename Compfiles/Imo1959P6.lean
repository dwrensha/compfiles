/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1959, Problem 6

The planes $P$ and $Q$ are not parallel. The point $A$ lies in $P$ but not $Q$, and the
point $C$ lies in $Q$ but not $P$. Construct points $B$ in $P$ and $D$ in $Q$ such that
the quadrilateral $ABCD$ satisfies the following conditions:
  (1) it lies in a plane,
  (2) the vertices are in the order $A, B, C, D$,
  (3) it is an isosceles trapezoid with $AB \parallel CD$ (meaning that $AD = BC$, but
      $AD$ is not parallel to $BC$ unless it is a square), and
  (4) a circle can be inscribed in $ABCD$ touching the sides.
-/

namespace Imo1959P6

open RealInnerProductSpace

/-- The type of points of Euclidean three-space. -/
abbrev Pt := EuclideanSpace ℝ (Fin 3)

/-- The feasibility hypothesis: writing $H$ for the foot of the perpendicular from $C$ to
the line through $A$ parallel to $P \cap Q$, the construction is possible exactly when
$CH \le AH$. Since $P \cap Q$ is a line, the quantity
$\langle C - A, u \rangle^2 / \|u\|^2$ equals $AH^2$ for every nonzero vector $u$ along
$P \cap Q$, while $\|C - A\|^2 = AH^2 + CH^2$. -/
def Feasible (P Q : AffineSubspace ℝ Pt) (A C : Pt) : Prop :=
  ∀ u : Pt, u ∈ P.direction ⊓ Q.direction → u ≠ 0 →
    ‖C -ᵥ A‖ ^ 2 ≤ 2 * (⟪C -ᵥ A, u⟫ / ‖u‖) ^ 2

/-- `IsTrapezoidAnswer P Q A C B D` asserts that the points `B` and `D` solve the
construction problem: `B ∈ P`, `D ∈ Q`, the four points are coplanar, `ABCD` is an
isosceles trapezoid with `AB ∥ CD` (the vertices being in this order is encoded by the
two parallel sides pointing in the same direction, with nonzero lengths), the legs
`AD` and `BC` have equal length and are parallel only when the trapezoid is a square,
and Pitot's equality `AB + CD = BC + AD` encodes the existence of an inscribed circle. -/
structure IsTrapezoidAnswer (P Q : AffineSubspace ℝ Pt) (A C B D : Pt) : Prop where
  hB : B ∈ P
  hD : D ∈ Q
  hcoplanar : Coplanar ℝ ({A, B, C, D} : Set Pt)
  hAB : A ≠ B
  hCD : C ≠ D
  hparallel : ∃ k : ℝ, 0 < k ∧ C -ᵥ D = k • (B -ᵥ A)
  hisosceles : dist A D = dist B C
  htangential : dist A B + dist C D = dist B C + dist A D
  hsquare : (∃ j : ℝ, D -ᵥ A = j • (C -ᵥ B)) →
    dist A B = dist B C ∧ dist B C = dist C D ∧ ⟪D -ᵥ A, B -ᵥ A⟫ = 0

snip begin

/-- Two non-parallel planes in three-space meet in a line: their directions intersect in a
one-dimensional subspace. -/
theorem finrank_direction_inf {P Q : AffineSubspace ℝ Pt}
    (hP : Module.finrank ℝ P.direction = 2) (hQ : Module.finrank ℝ Q.direction = 2)
    (hne : P.direction ≠ Q.direction) :
    Module.finrank ℝ ↥(P.direction ⊓ Q.direction) = 1 := by
  have hnot : ¬ Q.direction ≤ P.direction := fun hle =>
    hne ((Submodule.eq_of_le_of_finrank_eq hle (by rw [hP, hQ])).symm)
  have hlt : P.direction < P.direction ⊔ Q.direction :=
    lt_of_le_of_ne le_sup_left (fun h => hnot (h.symm ▸ le_sup_right))
  have hfin : Module.finrank ℝ ↥(P.direction ⊔ Q.direction) = 3 := by
    have h1 : 2 < Module.finrank ℝ ↥(P.direction ⊔ Q.direction) := by
      have h1' : Module.finrank ℝ ↥P.direction < Module.finrank ℝ ↥(P.direction ⊔ Q.direction) :=
        Submodule.finrank_lt_finrank_of_lt hlt
      omega
    have h2 : Module.finrank ℝ ↥(P.direction ⊔ Q.direction) ≤ 3 := by
      have h3 := Submodule.finrank_le (P.direction ⊔ Q.direction)
      rw [finrank_euclideanSpace, Fintype.card_fin] at h3
      exact h3
    omega
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq P.direction Q.direction
  omega

/-- There is a unit vector along the line of intersection of the two planes; we may choose
its orientation so that the component of `C -ᵥ A` along it is nonnegative. -/
theorem exists_unit_vector {P Q : AffineSubspace ℝ Pt} (A C : Pt)
    (hP : Module.finrank ℝ P.direction = 2) (hQ : Module.finrank ℝ Q.direction = 2)
    (hne : P.direction ≠ Q.direction) :
    ∃ u : Pt, u ∈ P.direction ⊓ Q.direction ∧ ⟪u, u⟫ = 1 ∧ 0 ≤ ⟪C -ᵥ A, u⟫ := by
  have h1 : Module.finrank ℝ ↥(P.direction ⊓ Q.direction) = 1 := finrank_direction_inf hP hQ hne
  obtain ⟨x, hx⟩ : ∃ x : ↥(P.direction ⊓ Q.direction), x ≠ 0 :=
    Module.finrank_pos_iff_exists_ne_zero.mp (by rw [h1]; norm_num)
  have hxmem : (x : Pt) ∈ P.direction ⊓ Q.direction := x.2
  have hxne : (x : Pt) ≠ 0 := fun h => hx (Submodule.coe_eq_zero.mp h)
  have hnorm : ‖(x : Pt)‖ ≠ 0 := norm_ne_zero_iff.mpr hxne
  by_cases hs : 0 ≤ ⟪C -ᵥ A, (x : Pt)⟫
  · refine ⟨‖(x : Pt)‖⁻¹ • (x : Pt), Submodule.smul_mem _ _ hxmem, ?_, ?_⟩
    · rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
    · rw [real_inner_smul_right]
      exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) hs
  · push Not at hs
    refine ⟨-(‖(x : Pt)‖⁻¹ • (x : Pt)),
      Submodule.neg_mem _ (Submodule.smul_mem _ _ hxmem), ?_, ?_⟩
    · rw [inner_neg_left, inner_neg_right, real_inner_smul_left, real_inner_smul_right,
        real_inner_self_eq_norm_sq]
      field_simp
    · rw [inner_neg_right, real_inner_smul_right, ← mul_neg]
      exact mul_nonneg (inv_nonneg.mpr (norm_nonneg (x : Pt))) (neg_nonneg.mpr hs.le)

snip end

problem imo1959_p6 (P Q : AffineSubspace ℝ Pt)
    (hP : Module.finrank ℝ P.direction = 2) (hQ : Module.finrank ℝ Q.direction = 2)
    (hne : P.direction ≠ Q.direction)
    (A C : Pt) (hA : A ∈ P) (_hA' : A ∉ Q) (hC : C ∈ Q) (hC' : C ∉ P)
    (hfeas : Feasible P Q A C) :
    ∃ B D : Pt, IsTrapezoidAnswer P Q A C B D := by
  obtain ⟨u, huPQ, hu1, hh0⟩ := exists_unit_vector A C hP hQ hne
  have huP : u ∈ P.direction := huPQ.1
  have huQ : u ∈ Q.direction := huPQ.2
  have hune : u ≠ 0 := by
    intro hu
    rw [hu] at hu1
    simp at hu1
  have hunorm : ‖u‖ = 1 := by
    have h2 : ‖u‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq, hu1]
    exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).mp (by rw [h2, one_pow])
  have hfeasu := hfeas u huPQ hune
  rw [hunorm, div_one] at hfeasu
  set h := ⟪C -ᵥ A, u⟫ with hhdef
  set w := C -ᵥ A - h • u with hwdef
  have hwu : ⟪w, u⟫ = 0 := by
    rw [hwdef, inner_sub_left, real_inner_smul_left, hu1, mul_one, hhdef, sub_self]
  have huw : ⟪u, w⟫ = 0 := by rw [real_inner_comm, hwu]
  have hCA : C -ᵥ A = h • u + w := by
    rw [hwdef]
    abel
  have hCAnorm : ‖C -ᵥ A‖ ^ 2 = h ^ 2 + ‖w‖ ^ 2 := by
    rw [hCA, norm_add_sq_real, norm_smul, hunorm, real_inner_smul_left, huw, mul_zero,
      mul_zero, add_zero, mul_one, Real.norm_eq_abs, sq_abs]
  have hdw : ‖w‖ ^ 2 ≤ h ^ 2 := by linarith [hCAnorm, hfeasu]
  have hwne : w ≠ 0 := by
    intro hw0
    have hCe : C = (h • u) +ᵥ A := by
      have hCA0 : C -ᵥ A = h • u := by rw [hCA, hw0, add_zero]
      rw [← hCA0]
      simp
    have hCmem : C ∈ P := by
      rw [hCe]
      exact AffineSubspace.vadd_mem_of_mem_direction (Submodule.smul_mem _ _ huP) hA
    exact hC' hCmem
  have hhpos : 0 < h := by
    rcases eq_or_lt_of_le hh0 with heq | hlt
    · exfalso
      apply hwne
      have hw2 : ‖w‖ ^ 2 ≤ 0 := by
        have h3 := hdw
        rw [← heq, zero_pow two_ne_zero] at h3
        exact h3
      exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp (le_antisymm hw2 (sq_nonneg _)))
    · exact hlt
  set s := Real.sqrt (h ^ 2 - ‖w‖ ^ 2) with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = h ^ 2 - ‖w‖ ^ 2 := Real.sq_sqrt (by linarith [hdw])
  have hwnormpos : 0 < ‖w‖ := norm_pos_iff.mpr hwne
  have hsh : s < h := by
    have hlt2 : s ^ 2 < h ^ 2 := by
      have hw2pos : 0 < ‖w‖ ^ 2 := pow_pos hwnormpos 2
      linarith [hs2]
    by_contra hle
    push Not at hle
    have h3 := pow_le_pow_left₀ hhpos.le hle 2
    linarith
  have hsumpos : 0 < h + s := by linarith [hhpos, hs0]
  set B := (h + s) • u +ᵥ A with hBdef
  set D := (s • u + w) +ᵥ A with hDdef
  -- Vector identities for the four sides.
  have hBv : B -ᵥ A = (h + s) • u := vadd_vsub _ _
  have hDv : D -ᵥ A = s • u + w := vadd_vsub _ _
  have hCB : C -ᵥ B = -s • u + w := by
    rw [← vsub_sub_vsub_cancel_right C B A, hBv, hCA, add_smul, neg_smul]
    abel
  have hCDv : C -ᵥ D = (h - s) • u := by
    rw [← vsub_sub_vsub_cancel_right C D A, hDv, hCA, sub_smul]
    abel
  have hCe : C = (h • u + w) +ᵥ A := by
    rw [← hCA]
    simp
  have hDeq : D = (s - h) • u +ᵥ C := by
    rw [hDdef, hCe, vadd_vadd]
    congr 1
    rw [sub_smul]
    abel
  -- The four side lengths.
  have hdistAB : dist A B = h + s := by
    rw [dist_comm, dist_eq_norm_vsub, hBv, norm_smul, hunorm, mul_one, Real.norm_eq_abs,
      abs_of_nonneg hsumpos.le]
  have hdistCD : dist C D = h - s := by
    rw [dist_eq_norm_vsub, hCDv, norm_smul, hunorm, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (sub_pos.mpr hsh).le]
  have hnormD : ‖s • u + w‖ = h := by
    apply (pow_left_inj₀ (norm_nonneg _) hhpos.le two_ne_zero).mp
    rw [norm_add_sq_real, real_inner_smul_left, huw, mul_zero, mul_zero, add_zero,
      norm_smul, hunorm, mul_one, Real.norm_eq_abs, sq_abs, hs2]
    ring
  have hnormC : ‖-s • u + w‖ = h := by
    apply (pow_left_inj₀ (norm_nonneg _) hhpos.le two_ne_zero).mp
    rw [norm_add_sq_real, real_inner_smul_left, huw, mul_zero, mul_zero, add_zero,
      norm_smul, hunorm, mul_one, Real.norm_eq_abs, sq_abs, neg_sq, hs2]
    ring
  have hdistAD : dist A D = h := by
    rw [dist_comm, dist_eq_norm_vsub, hDv, hnormD]
  have hdistBC : dist B C = h := by
    rw [dist_comm, dist_eq_norm_vsub, hCB, hnormC]
  -- The nine conditions.
  have hBmem : B ∈ P := by
    rw [hBdef]
    exact AffineSubspace.vadd_mem_of_mem_direction (Submodule.smul_mem _ _ huP) hA
  have hDmem : D ∈ Q := by
    rw [hDeq]
    exact AffineSubspace.vadd_mem_of_mem_direction (Submodule.smul_mem _ _ huQ) hC
  have hcop : Coplanar ℝ ({A, B, C, D} : Set Pt) := by
    have hBA : B -ᵥ A ∈ vectorSpan ℝ ({A, B, C} : Set Pt) :=
      vsub_mem_vectorSpan ℝ (by simp) (by simp)
    have huV : u ∈ vectorSpan ℝ ({A, B, C} : Set Pt) := by
      have hsmul := Submodule.smul_mem _ (h + s)⁻¹ hBA
      rw [hBv, inv_smul_smul₀ hsumpos.ne'] at hsmul
      exact hsmul
    have hCAV : C -ᵥ A ∈ vectorSpan ℝ ({A, B, C} : Set Pt) :=
      vsub_mem_vectorSpan ℝ (by simp) (by simp)
    have hwV : w ∈ vectorSpan ℝ ({A, B, C} : Set Pt) := by
      rw [hwdef]
      exact Submodule.sub_mem _ hCAV (Submodule.smul_mem _ _ huV)
    have hDmem3 : D ∈ affineSpan ℝ ({A, B, C} : Set Pt) := by
      rw [hDdef]
      refine AffineSubspace.vadd_mem_of_mem_direction ?_ (mem_affineSpan ℝ (by simp))
      rw [direction_affineSpan]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ huV) hwV
    have hcop3 : Coplanar ℝ ({A, B, C} : Set Pt) := by
      have h2 := (collinear_pair ℝ A B).coplanar_insert C
      have hset : insert C ({A, B} : Set Pt) = {A, B, C} := by
        ext x
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      rwa [hset] at h2
    have h4 := (coplanar_insert_iff_of_mem_affineSpan hDmem3).mpr hcop3
    have hset : insert D ({A, B, C} : Set Pt) = {A, B, C, D} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rwa [hset] at h4
  have hAB : A ≠ B := by
    intro hab
    rw [hab, dist_self] at hdistAB
    linarith [hsumpos]
  have hCD : C ≠ D := by
    intro hcd
    rw [hcd, dist_self] at hdistCD
    linarith [hsh]
  have hparallel : ∃ k : ℝ, 0 < k ∧ C -ᵥ D = k • (B -ᵥ A) := by
    refine ⟨(h - s) / (h + s), div_pos (sub_pos.mpr hsh) hsumpos, ?_⟩
    rw [hCDv, hBv, smul_smul, div_mul_cancel₀ _ hsumpos.ne']
  have hisosceles : dist A D = dist B C := by rw [hdistAD, hdistBC]
  have htangential : dist A B + dist C D = dist B C + dist A D := by
    rw [hdistAB, hdistCD, hdistAD, hdistBC]
    ring
  have hsquare : (∃ j : ℝ, D -ᵥ A = j • (C -ᵥ B)) →
      dist A B = dist B C ∧ dist B C = dist C D ∧ ⟪D -ᵥ A, B -ᵥ A⟫ = 0 := by
    rintro ⟨j, hj⟩
    rw [hDv, hCB] at hj
    have h1 : ⟪s • u + w, u⟫ = s := by
      rw [inner_add_left, real_inner_smul_left, hu1, hwu, mul_one, add_zero]
    have h2 : ⟪j • (-s • u + w), u⟫ = j * -s := by
      rw [real_inner_smul_left, inner_add_left, real_inner_smul_left, hu1, hwu, mul_one,
        add_zero]
    have hju : s = j * -s := by
      have h5 := congrArg (fun x => ⟪x, u⟫) hj
      rw [h1, h2] at h5
      exact h5
    have h3 : ⟪s • u + w, w⟫ = ‖w‖ ^ 2 := by
      rw [inner_add_left, real_inner_smul_left, huw, mul_zero, zero_add,
        real_inner_self_eq_norm_sq]
    have h4 : ⟪j • (-s • u + w), w⟫ = j * ‖w‖ ^ 2 := by
      rw [real_inner_smul_left, inner_add_left, real_inner_smul_left, huw, mul_zero,
        zero_add, real_inner_self_eq_norm_sq]
    have hjw : ‖w‖ ^ 2 = j * ‖w‖ ^ 2 := by
      have h5 := congrArg (fun x => ⟪x, w⟫) hj
      rw [h3, h4] at h5
      exact h5
    have hw2 : ‖w‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hwne)
    have hj1 : j = 1 := by
      have h5 : 1 * ‖w‖ ^ 2 = j * ‖w‖ ^ 2 := by rw [one_mul]; exact hjw
      exact (mul_right_cancel₀ hw2 h5).symm
    have hs0' : s = 0 := by
      rw [hj1, one_mul] at hju
      linarith [hju]
    refine ⟨?_, ?_, ?_⟩
    · rw [hdistAB, hdistBC, hs0', add_zero]
    · rw [hdistBC, hdistCD, hs0', sub_zero]
    · rw [hDv, hBv, hs0', zero_smul, zero_add, add_zero, real_inner_smul_right, hwu,
        mul_zero]
  exact ⟨B, D, hBmem, hDmem, hcop, hAB, hCD, hparallel, hisosceles, htangential, hsquare⟩

end Imo1959P6
