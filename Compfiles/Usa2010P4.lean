/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Geometry.Euclidean.Triangle
public import Mathlib.NumberTheory.Real.Irrational
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Geometry]
}

/-!
# USA Mathematical Olympiad 2010, Problem 4

Let ABC be a triangle with ∠A = 90°. Points D and E lie on sides AC and AB,
respectively, such that ∠ABD = ∠DBC and ∠ACE = ∠ECB. Segments BD and CE meet
at I. Determine whether or not it is possible for segments AB, AC, BI, ID, CI,
IE to all have integer lengths.
-/

open EuclideanGeometry

open scoped EuclideanGeometry Real

variable (V : Type*) (Pt : Type*)

variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
  [NormedAddTorsor V Pt]

namespace Usa2010P4

/-- The predicate that the six segments named in the problem all have integer
lengths. -/
abbrev all_integer_lengths {Pt : Type*} [MetricSpace Pt] (A B C D E I : Pt) : Prop :=
  ∃ (ab ac bi id' ci ie : ℕ),
    dist A B = ab ∧ dist A C = ac ∧ dist B I = bi ∧
      dist I D = id' ∧ dist C I = ci ∧ dist I E = ie

snip begin

/-
We follow the official solution (also in Evan Chen's *USAMO 2010 Solution
Notes*). The answer is **no**; in fact already `AB`, `AC`, `BI` and `CI`
cannot all be integers. Since `BD` and `CE` are angle bisectors meeting at
the incenter `I`, one has `∠IBC = ∠B/2` and `∠ICB = ∠C/2`, hence

  `∠BIC = π - (∠B + ∠C)/2 = π - π/4 = 3π/4`.

The law of cosines in triangle `BIC` then gives
`BC² = BI² + CI² + √2·BI·CI`, which is irrational as `BI·CI > 0`, while the
Pythagorean theorem gives `BC² = AB² + AC²`, an integer: contradiction.

We apply the following conventions for formalizing the geometry problem,
following `Compfiles/Imo2019P2.lean`. The problem takes place in an arbitrary
inner product space (no planarity assumption is needed). Angles are unoriented.
A reference to an angle `∠XYZ` is taken to imply that `X` and `Z` are not
equal to `Y`, and those implications are included as hypotheses. The triangle
`ABC` is taken to be nondegenerate, expressed as affine independence. Points on
sides or segments are expressed with `Wbtw`, including endpoints (the endpoint
cases turn out to be contradictory anyway).
-/

/-- A configuration satisfying the conditions of the problem. We define this
structure to avoid passing many hypotheses around as we build up information
about the configuration; the final result for a statement of the problem not
using this structure is then deduced from one in terms of this structure. -/
structure Usa2010P4Cfg where
  (A B C D E I : Pt)
  affineIndependent_ABC : AffineIndependent ℝ ![A, B, C]
  angle_BAC : ∠ B A C = π / 2
  wbtw_A_D_C : Wbtw ℝ A D C
  wbtw_A_E_B : Wbtw ℝ A E B
  angle_ABD_eq_DBC : ∠ A B D = ∠ D B C
  angle_ACE_eq_ECB : ∠ A C E = ∠ E C B
  wbtw_B_I_D : Wbtw ℝ B I D
  wbtw_C_I_E : Wbtw ℝ C I E
  -- Hypotheses implicit in the named angles.
  D_ne_B : D ≠ B
  E_ne_C : E ≠ C

variable {V Pt}

namespace Usa2010P4Cfg

variable (cfg : Usa2010P4Cfg V Pt)

lemma A_ne_B : cfg.A ≠ cfg.B := by
  simpa using cfg.affineIndependent_ABC.injective.ne (show (0 : Fin 3) ≠ 1 by decide)

lemma B_ne_C : cfg.B ≠ cfg.C := by
  simpa using cfg.affineIndependent_ABC.injective.ne (show (1 : Fin 3) ≠ 2 by decide)

lemma A_ne_C : cfg.A ≠ cfg.C := by
  simpa using cfg.affineIndependent_ABC.injective.ne (show (0 : Fin 3) ≠ 2 by decide)

lemma not_collinear : ¬Collinear ℝ ({cfg.A, cfg.B, cfg.C} : Set Pt) :=
  affineIndependent_iff_not_collinear_set.1 cfg.affineIndependent_ABC

/-- The endpoint case `D = C` is contradictory: then `∠DBC = 0`, so `∠ABD = 0`,
which forces `A`, `B`, `C` to be collinear. -/
lemma D_ne_C : cfg.D ≠ cfg.C := by
  by_contra! hDC
  have h0 : ∠ cfg.A cfg.B cfg.D = 0 := by
    rw [cfg.angle_ABD_eq_DBC, hDC]
    exact angle_self_of_ne cfg.B_ne_C.symm
  rcases angle_eq_zero_iff_ne_and_wbtw.1 h0 with ⟨_, h⟩ | ⟨_, h⟩
  · rw [hDC] at h
    apply cfg.not_collinear
    have hset : ({cfg.B, cfg.A, cfg.C} : Set Pt) = {cfg.A, cfg.B, cfg.C} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    exact hset ▸ h.collinear
  · rw [hDC] at h
    apply cfg.not_collinear
    have hset : ({cfg.B, cfg.C, cfg.A} : Set Pt) = {cfg.A, cfg.B, cfg.C} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    exact hset ▸ h.collinear

/-- The endpoint case `E = B` is contradictory, similarly. -/
lemma E_ne_B : cfg.E ≠ cfg.B := by
  by_contra! hEB
  have h0 : ∠ cfg.A cfg.C cfg.E = 0 := by
    rw [cfg.angle_ACE_eq_ECB, hEB]
    exact angle_self_of_ne cfg.B_ne_C
  rcases angle_eq_zero_iff_ne_and_wbtw.1 h0 with ⟨_, h⟩ | ⟨_, h⟩
  · rw [hEB] at h
    apply cfg.not_collinear
    have hset : ({cfg.C, cfg.A, cfg.B} : Set Pt) = {cfg.A, cfg.B, cfg.C} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    exact hset ▸ h.collinear
  · rw [hEB] at h
    apply cfg.not_collinear
    have hset : ({cfg.C, cfg.B, cfg.A} : Set Pt) = {cfg.A, cfg.B, cfg.C} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    exact hset ▸ h.collinear

/-- `I` cannot coincide with `B`: otherwise `B` would lie strictly between `C`
and `E`, forcing `∠CBA = π`, contradicting nondegeneracy. -/
lemma I_ne_B : cfg.I ≠ cfg.B := by
  by_contra! hIB
  have hW : Wbtw ℝ cfg.C cfg.B cfg.E := by
    rw [← hIB]
    exact cfg.wbtw_C_I_E
  have hsbtw : Sbtw ℝ cfg.C cfg.B cfg.E := ⟨hW, cfg.B_ne_C, cfg.E_ne_B.symm⟩
  have hpi : ∠ cfg.C cfg.B cfg.E = π := hsbtw.angle₁₂₃_eq_pi
  obtain ⟨r, ⟨hr0, hr1⟩, hEdef⟩ := cfg.wbtw_A_E_B
  have hr10 : (0 : ℝ) < 1 - r := by
    by_contra! hcon
    have hr1' : r = 1 := by linarith
    rw [hr1', AffineMap.lineMap_apply_one] at hEdef
    exact cfg.E_ne_B hEdef.symm
  have hCBE : ∠ cfg.C cfg.B cfg.E = ∠ cfg.C cfg.B cfg.A :=
    angle_smul_right_of_pos cfg.C hr10 (by rw [← hEdef, AffineMap.lineMap_vsub_right])
  rw [hCBE] at hpi
  have hs := angle_eq_pi_iff_sbtw.1 hpi
  apply cfg.not_collinear
  have hset : ({cfg.C, cfg.B, cfg.A} : Set Pt) = {cfg.A, cfg.B, cfg.C} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  exact hset ▸ hs.wbtw.collinear

/-- `I` cannot coincide with `C`, similarly. -/
lemma I_ne_C : cfg.I ≠ cfg.C := by
  by_contra! hIC
  have hW : Wbtw ℝ cfg.B cfg.C cfg.D := by
    rw [← hIC]
    exact cfg.wbtw_B_I_D
  have hsbtw : Sbtw ℝ cfg.B cfg.C cfg.D := ⟨hW, cfg.B_ne_C.symm, cfg.D_ne_C.symm⟩
  have hpi : ∠ cfg.B cfg.C cfg.D = π := hsbtw.angle₁₂₃_eq_pi
  obtain ⟨r, ⟨hr0, hr1⟩, hDdef⟩ := cfg.wbtw_A_D_C
  have hr10 : (0 : ℝ) < 1 - r := by
    by_contra! hcon
    have hr1' : r = 1 := by linarith
    rw [hr1', AffineMap.lineMap_apply_one] at hDdef
    exact cfg.D_ne_C hDdef.symm
  have hBCD : ∠ cfg.B cfg.C cfg.D = ∠ cfg.B cfg.C cfg.A :=
    angle_smul_right_of_pos cfg.B hr10 (by rw [← hDdef, AffineMap.lineMap_vsub_right])
  rw [hBCD] at hpi
  have hs := angle_eq_pi_iff_sbtw.1 hpi
  apply cfg.not_collinear
  have hset : ({cfg.B, cfg.C, cfg.A} : Set Pt) = {cfg.A, cfg.B, cfg.C} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  exact hset ▸ hs.wbtw.collinear

/-- Since `I` lies on the segment `BD`, the ray `BI` equals the ray `BD`. -/
lemma angle_IBC : ∠ cfg.I cfg.B cfg.C = ∠ cfg.D cfg.B cfg.C := by
  obtain ⟨r, ⟨hr0, -⟩, hIdef⟩ := cfg.wbtw_B_I_D
  have hr_pos : (0 : ℝ) < r := by
    by_contra! hcon
    have hr0' : r = 0 := by linarith
    rw [hr0', AffineMap.lineMap_apply_zero] at hIdef
    exact cfg.I_ne_B hIdef.symm
  have h1 : ∠ cfg.C cfg.B cfg.I = ∠ cfg.C cfg.B cfg.D :=
    angle_smul_right_of_pos cfg.C hr_pos (by rw [← hIdef, AffineMap.lineMap_vsub_left])
  rwa [angle_comm cfg.C cfg.B cfg.I, angle_comm cfg.C cfg.B cfg.D] at h1

/-- Since `I` lies on the segment `CE`, the ray `CI` equals the ray `CE`. -/
lemma angle_ICB : ∠ cfg.I cfg.C cfg.B = ∠ cfg.E cfg.C cfg.B := by
  obtain ⟨r, ⟨hr0, -⟩, hIdef⟩ := cfg.wbtw_C_I_E
  have hr_pos : (0 : ℝ) < r := by
    by_contra! hcon
    have hr0' : r = 0 := by linarith
    rw [hr0', AffineMap.lineMap_apply_zero] at hIdef
    exact cfg.I_ne_C hIdef.symm
  have h1 : ∠ cfg.B cfg.C cfg.I = ∠ cfg.B cfg.C cfg.E :=
    angle_smul_right_of_pos cfg.B hr_pos (by rw [← hIdef, AffineMap.lineMap_vsub_left])
  rwa [angle_comm cfg.B cfg.C cfg.I, angle_comm cfg.B cfg.C cfg.E] at h1

/-- The key angle chase: `∠BIC = 3π/4` (i.e. `135°`). -/
lemma angle_BIC : ∠ cfg.B cfg.I cfg.C = 3 * π / 4 := by
  have hsum1 : ∠ cfg.B cfg.A cfg.C + ∠ cfg.A cfg.C cfg.B + ∠ cfg.C cfg.B cfg.A = π :=
    angle_add_angle_add_angle_eq_pi cfg.C cfg.A_ne_B
  have hsum2 : ∠ cfg.B cfg.I cfg.C + ∠ cfg.I cfg.C cfg.B + ∠ cfg.C cfg.B cfg.I = π :=
    angle_add_angle_add_angle_eq_pi cfg.C cfg.I_ne_B
  have h1 : ∠ cfg.C cfg.B cfg.A = 2 * ∠ cfg.C cfg.B cfg.I := by
    have hadd : ∠ cfg.A cfg.B cfg.D + ∠ cfg.D cfg.B cfg.C = ∠ cfg.A cfg.B cfg.C :=
      angle_add_of_ne_of_ne cfg.A_ne_B.symm cfg.B_ne_C cfg.wbtw_A_D_C
    rw [angle_comm cfg.C cfg.B cfg.A, ← hadd, cfg.angle_ABD_eq_DBC, ← cfg.angle_IBC,
      angle_comm cfg.I cfg.B cfg.C]
    ring
  have h2 : ∠ cfg.A cfg.C cfg.B = 2 * ∠ cfg.B cfg.C cfg.I := by
    have hadd : ∠ cfg.A cfg.C cfg.E + ∠ cfg.E cfg.C cfg.B = ∠ cfg.A cfg.C cfg.B :=
      angle_add_of_ne_of_ne cfg.A_ne_C.symm cfg.B_ne_C.symm cfg.wbtw_A_E_B
    rw [← hadd, cfg.angle_ACE_eq_ECB, ← cfg.angle_ICB, angle_comm cfg.I cfg.C cfg.B]
    ring
  rw [cfg.angle_BAC, h1, h2] at hsum1
  rw [angle_comm cfg.I cfg.C cfg.B] at hsum2
  linarith

/-- The conclusion of the problem for a configuration: the six segments cannot
all have integer lengths. -/
theorem not_all_integer :
    ¬all_integer_lengths cfg.A cfg.B cfg.C cfg.D cfg.E cfg.I := by
  rintro ⟨ab, ac, bi, id', ci, ie, hAB, hAC, hBI, -, hCI, -⟩
  have hBI_pos : (0 : ℝ) < (bi : ℝ) := by
    rw [← hBI]
    exact dist_pos.mpr cfg.I_ne_B.symm
  have hCI_pos : (0 : ℝ) < (ci : ℝ) := by
    rw [← hCI]
    exact dist_pos.mpr cfg.I_ne_C.symm
  -- The Pythagorean theorem at `A` (via the law of cosines): `BC² = AB² + AC²`.
  have hpyt : dist cfg.B cfg.C * dist cfg.B cfg.C = (ab : ℝ) ^ 2 + (ac : ℝ) ^ 2 := by
    have h := law_cos cfg.B cfg.A cfg.C
    rw [cfg.angle_BAC, Real.cos_pi_div_two, dist_comm cfg.B cfg.A, dist_comm cfg.C cfg.A,
      hAB, hAC] at h
    linarith [h]
  -- The law of cosines at `I` with `∠BIC = 3π/4`, so `cos = -√2/2`:
  -- `BC² = BI² + CI² + √2·BI·CI`.
  have hkey : (ab : ℝ) ^ 2 + (ac : ℝ) ^ 2 =
      (bi : ℝ) ^ 2 + (ci : ℝ) ^ 2 + Real.sqrt 2 * bi * ci := by
    have h := law_cos cfg.B cfg.I cfg.C
    rw [cfg.angle_BIC, show (3 * π / 4 : ℝ) = π - π / 4 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_four, hBI, hCI] at h
    linarith [h, hpyt]
  -- Hence `√2` would be rational, a contradiction.
  have hbic : (0 : ℝ) < (bi : ℝ) * (ci : ℝ) := mul_pos hBI_pos hCI_pos
  have hsqrteq : Real.sqrt 2 =
      ((((ab : ℚ) ^ 2 + (ac : ℚ) ^ 2 - (bi : ℚ) ^ 2 - (ci : ℚ) ^ 2) /
        ((bi : ℚ) * (ci : ℚ)) : ℚ) : ℝ) := by
    push_cast
    rw [eq_div_iff hbic.ne.symm]
    linarith [hkey]
  exact irrational_sqrt_two ⟨_, hsqrteq.symm⟩

end Usa2010P4Cfg

snip end

determine is_possible : Bool := false

problem usa2010_p4 (A B C D E I : Pt)
    (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C])
    (angle_BAC : ∠ B A C = π / 2)
    (wbtw_A_D_C : Wbtw ℝ A D C) (wbtw_A_E_B : Wbtw ℝ A E B)
    (angle_ABD_eq_DBC : ∠ A B D = ∠ D B C) (angle_ACE_eq_ECB : ∠ A C E = ∠ E C B)
    (wbtw_B_I_D : Wbtw ℝ B I D) (wbtw_C_I_E : Wbtw ℝ C I E)
    (D_ne_B : D ≠ B) (E_ne_C : E ≠ C) :
    if is_possible then all_integer_lengths A B C D E I
    else ¬all_integer_lengths A B C D E I := by
  simp only [is_possible]
  exact (⟨A, B, C, D, E, I, affineIndependent_ABC, angle_BAC, wbtw_A_D_C, wbtw_A_E_B,
      angle_ABD_eq_DBC, angle_ACE_eq_ECB, wbtw_B_I_D, wbtw_C_I_E, D_ne_B, E_ne_C⟩ :
    Usa2010P4Cfg V Pt).not_all_integer

end Usa2010P4
