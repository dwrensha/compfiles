/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Geometry.Euclidean.Inversion.Basic
public import Mathlib.Geometry.Euclidean.Projection
public import Mathlib.Geometry.Euclidean.Triangle
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1995, Problem 5

Let ABCDEF be a convex hexagon with AB = BC = CD and DE = EF = FA, such that
∠BCD = ∠EFA = 60°. Suppose that G and H are points in the interior of the
hexagon such that ∠AGB = ∠DHE = 120°. Prove that
AG + GB + GH + DH + HE ≥ CF.

(Formalization note: the convexity and interior hypotheses are not needed for
the inequality — it holds for arbitrary points of the Euclidean plane
satisfying the stated metric and angle conditions — so they are omitted from
the formal statement.)
-/

open EuclideanGeometry
open scoped EuclideanGeometry Real RealInnerProductSpace

namespace Imo1995P5

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {P : Type*} [MetricSpace P] [NormedAddTorsor V P]

snip begin

/-
## Solution

Since `BC = CD` and `∠BCD = 60°`, the triangle `BCD` is equilateral, so
`BD = BC = AB`; similarly `AEF` is equilateral, so `AE = EF = DE`. Hence both
`B` and `E` are equidistant from `A` and `D`, so the line `BE` is the
perpendicular bisector of `AD` and the reflection `ρ` in the line `BE` swaps
`A` and `D`. Let `C' = ρ C` and `F' = ρ F`. Then `C'F' = CF`, and the
triangles `ABC'` and `DEF'` are equilateral, so Ptolemy's inequality applied
to the quadrangles `C'AGB` and `F'DHE` gives `C'G ≤ AG + GB` and
`F'H ≤ DH + HE`. Finally
`CF = C'F' ≤ C'G + GH + HF' ≤ AG + GB + GH + DH + HE`.

(The degenerate cases `A = D` and `B = E` follow directly from the triangle
inequality.)
-/

/-- In a one-dimensional real inner product space, two vectors of equal norm
are equal or opposite. -/
lemma eq_or_neg_of_norm_eq_of_finrank_eq_one {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] (hW : Module.finrank ℝ W = 1) {u v : W} (h : ‖u‖ = ‖v‖) :
    u = v ∨ u = -v := by
  obtain ⟨w, hw, hspan⟩ := finrank_eq_one_iff'.mp hW
  obtain ⟨a, rfl⟩ := hspan u
  obtain ⟨b, rfl⟩ := hspan v
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs] at h
  have hw2 : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hab : |a| = |b| := mul_right_cancel₀ hw2 h
  rcases abs_eq_abs.mp hab with h' | h'
  · exact Or.inl (by rw [h'])
  · exact Or.inr (by rw [h', neg_smul])

/-- Two points of the Euclidean plane equidistant from two distinct points
`B`, `E` are equal or reflections of each other in the line `BE`. -/
lemma eq_or_eq_reflection_of_dist_eq_of_dist_eq (hdim : Module.finrank ℝ V = 2)
    {B E X Y : P} (hBE : B ≠ E) (hXB : dist X B = dist Y B) (hXE : dist X E = dist Y E) :
    X = Y ∨ X = reflection (affineSpan ℝ {B, E}) Y := by
  set S := affineSpan ℝ ({B, E} : Set P) with hS
  have hBS : B ∈ S := mem_affineSpan ℝ (Set.mem_insert B {E})
  have hES : E ∈ S := mem_affineSpan ℝ (Set.mem_insert_of_mem B (Set.mem_singleton E))
  haveI : Nonempty S := ⟨⟨B, hBS⟩⟩
  haveI : CompleteSpace S.direction := FiniteDimensional.complete ℝ S.direction
  set mX : P := ↑(orthogonalProjection S X) with hmX_def
  set mY : P := ↑(orthogonalProjection S Y) with hmY_def
  have hmX : mX ∈ S := orthogonalProjection_mem X
  have hmY : mY ∈ S := orthogonalProjection_mem Y
  have pythXB : dist B X ^ 2 = dist B mX ^ 2 + dist X mX ^ 2 := by
    have h := dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq X hBS
    simp only [← pow_two] at h
    exact h
  have pythXE : dist E X ^ 2 = dist E mX ^ 2 + dist X mX ^ 2 := by
    have h := dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq X hES
    simp only [← pow_two] at h
    exact h
  have pythYB : dist B Y ^ 2 = dist B mY ^ 2 + dist Y mY ^ 2 := by
    have h := dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq Y hBS
    simp only [← pow_two] at h
    exact h
  have pythYE : dist E Y ^ 2 = dist E mY ^ 2 + dist Y mY ^ 2 := by
    have h := dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq Y hES
    simp only [← pow_two] at h
    exact h
  have eXB : dist B X = dist B Y := by rw [dist_comm B X, dist_comm B Y, hXB]
  have eXE : dist E X = dist E Y := by rw [dist_comm E X, dist_comm E Y, hXE]
  have eXB2 : dist B X ^ 2 = dist B Y ^ 2 := by rw [eXB]
  have eXE2 : dist E X ^ 2 = dist E Y ^ 2 := by rw [eXE]
  have hsub : dist B mX ^ 2 - dist E mX ^ 2 = dist B mY ^ 2 - dist E mY ^ 2 := by
    linarith [pythXB, pythXE, pythYB, pythYE, eXB2, eXE2]
  have hf : ∀ M : P, dist B M ^ 2 - dist E M ^ 2 =
      -2 * ⟪M -ᵥ B, B -ᵥ E⟫ - ‖B -ᵥ E‖ ^ 2 := by
    intro M
    rw [dist_comm B M, dist_comm E M, dist_eq_norm_vsub V M B, dist_eq_norm_vsub V M E,
      ← vsub_add_vsub_cancel M B E, norm_add_sq_real]
    ring
  have hinner : ⟪mX -ᵥ B, B -ᵥ E⟫ = ⟪mY -ᵥ B, B -ᵥ E⟫ := by
    have e1 := hf mX
    have e2 := hf mY
    linarith [e1, e2, hsub]
  have hdir : S.direction = ℝ ∙ (B -ᵥ E) := by rw [hS, direction_affineSpan, vectorSpan_pair]
  have hmem : mX -ᵥ mY ∈ S.direction := S.vsub_mem_direction hmX hmY
  rw [hdir] at hmem
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hmem
  have hdecomp : mX -ᵥ B = (mX -ᵥ mY) + (mY -ᵥ B) := by rw [vsub_add_vsub_cancel]
  rw [hdecomp, ← ht, inner_add_left, real_inner_smul_left] at hinner
  have hw : ⟪(B -ᵥ E), (B -ᵥ E)⟫ ≠ 0 := by
    simp only [Ne, inner_self_eq_zero]
    exact vsub_ne_zero.mpr hBE
  have ht0 : t = 0 := by
    have h'' : t * ⟪(B -ᵥ E), (B -ᵥ E)⟫ = 0 := by linarith [hinner]
    exact (mul_eq_zero.mp h'').resolve_right hw
  rw [ht0, zero_smul] at ht
  have hm : mX = mY := vsub_eq_zero_iff_eq.mp ht.symm
  have hd : dist X mX = dist Y mX := by
    rw [← hm] at pythYB
    have e : dist X mX ^ 2 = dist Y mX ^ 2 := by linarith [pythXB, pythYB, eXB2]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp e with h | h
    · exact h
    · have h1 : (0 : ℝ) ≤ dist X mX := dist_nonneg
      have h2 : (0 : ℝ) ≤ dist Y mX := dist_nonneg
      linarith [h, h1, h2]
  have hoX : X -ᵥ mX ∈ S.directionᗮ := vsub_orthogonalProjection_mem_direction_orthogonal S X
  have hoYmY : Y -ᵥ mY ∈ S.directionᗮ := vsub_orthogonalProjection_mem_direction_orthogonal S Y
  have hoY : Y -ᵥ mX ∈ S.directionᗮ := by rwa [← hm] at hoYmY
  have hfr : Module.finrank ℝ S.directionᗮ = 1 := by
    have h1 : Module.finrank ℝ S.direction = 1 := by
      rw [hdir]
      exact finrank_span_singleton (vsub_ne_zero.mpr hBE)
    have h2 : Module.finrank ℝ S.direction + Module.finrank ℝ S.directionᗮ = Module.finrank ℝ V :=
      S.direction.finrank_add_finrank_orthogonal
    omega
  have hnorm : ‖(⟨X -ᵥ mX, hoX⟩ : S.directionᗮ)‖ = ‖(⟨Y -ᵥ mX, hoY⟩ : S.directionᗮ)‖ := by
    have e1 : ‖(⟨X -ᵥ mX, hoX⟩ : S.directionᗮ)‖ = ‖X -ᵥ mX‖ := rfl
    have e2 : ‖(⟨Y -ᵥ mX, hoY⟩ : S.directionᗮ)‖ = ‖Y -ᵥ mX‖ := rfl
    rw [e1, e2, ← dist_eq_norm_vsub V X mX, ← dist_eq_norm_vsub V Y mX, hd]
  rcases eq_or_neg_of_norm_eq_of_finrank_eq_one hfr hnorm with h | h
  · left
    exact vsub_left_cancel (Subtype.ext_iff.mp h)
  · right
    have h' : X -ᵥ mX = -(Y -ᵥ mX) := congrArg Subtype.val h
    have hr : reflection S Y = -(Y -ᵥ mY) +ᵥ mY := by
      conv_lhs => rw [← vsub_vadd Y mY]
      exact reflection_orthogonal_vadd hmY hoYmY
    rw [hr, ← hm]
    exact (eq_vadd_iff_vsub_eq X (-(Y -ᵥ mX)) mX).mpr h'

snip end

problem imo1995_p5 (hdim : Module.finrank ℝ V = 2) (A B C D E F G H : P)
    (hABC : dist A B = dist B C) (hBCD : dist B C = dist C D)
    (hDEF : dist D E = dist E F) (hEFA : dist E F = dist F A)
    (hBCD_angle : ∠ B C D = π / 3) (hEFA_angle : ∠ E F A = π / 3)
    (hAGB : ∠ A G B = 2 * π / 3) (hDHE : ∠ D H E = 2 * π / 3) :
    dist C F ≤ dist A G + dist G B + dist G H + dist D H + dist H E := by
  -- The triangle `BCD` is equilateral: `BD = BC`.
  have hBD : dist B D = dist B C := by
    have lc := dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle B C D
    rw [hBCD_angle, Real.cos_pi_div_three, dist_comm D C, ← hBCD] at lc
    have hsq : dist B D ^ 2 = dist B C ^ 2 := by
      have e : 2 * dist B C * dist B C * (1 / 2 : ℝ) = dist B C ^ 2 := by ring
      simp only [← pow_two] at lc
      linarith [lc, e]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact h
    · have h1 : (0 : ℝ) ≤ dist B D := dist_nonneg
      have h2 : (0 : ℝ) ≤ dist B C := dist_nonneg
      linarith [h, h1, h2]
  -- The triangle `AEF` is equilateral: `AE = EF`.
  have hAE : dist A E = dist E F := by
    have lc := dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle E F A
    rw [hEFA_angle, Real.cos_pi_div_three, dist_comm A F, ← hEFA] at lc
    have hsq : dist E A ^ 2 = dist E F ^ 2 := by
      have e : 2 * dist E F * dist E F * (1 / 2 : ℝ) = dist E F ^ 2 := by ring
      simp only [← pow_two] at lc
      linarith [lc, e]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · rw [dist_comm A E]; exact h
    · have h1 : (0 : ℝ) ≤ dist E A := dist_nonneg
      have h2 : (0 : ℝ) ≤ dist E F := dist_nonneg
      have h' : dist E A = dist E F := by linarith [h, h1, h2]
      rw [dist_comm A E]; exact h'
  -- Nondegeneracy from the `120°` angle conditions.
  have hAB_ne : A ≠ B := by
    intro h
    by_cases hBG : B = G
    · rw [h, hBG, angle_self_left] at hAGB
      linarith [Real.pi_pos]
    · rw [h, angle_self_of_ne hBG] at hAGB
      linarith [Real.pi_pos]
  have hDE_ne : D ≠ E := by
    intro h
    by_cases hDH : D = H
    · rw [h, h.symm.trans hDH, angle_self_left] at hDHE
      linarith [Real.pi_pos]
    · rw [h, angle_self_of_ne (fun hEH => hDH (h.trans hEH))] at hDHE
      linarith [Real.pi_pos]
  by_cases hAD : A = D
  · -- Degenerate case `A = D`: the triangle inequality suffices.
    have t1 : dist C F ≤ dist C A + dist A F := dist_triangle C A F
    have t2 : dist C A = dist A B := calc
      dist C A = dist C D := by rw [hAD]
      _ = dist B C := hBCD.symm
      _ = dist A B := hABC.symm
    have t3 : dist A F = dist D E := calc
      dist A F = dist F A := dist_comm A F
      _ = dist E F := hEFA.symm
      _ = dist D E := hDEF.symm
    have t4 : dist A B ≤ dist A G + dist G B := dist_triangle A G B
    have t5 : dist D E ≤ dist D H + dist H E := dist_triangle D H E
    have t6 : (0 : ℝ) ≤ dist G H := dist_nonneg
    linarith [t1, t2, t3, t4, t5, t6]
  by_cases hBE : B = E
  · -- Degenerate case `B = E`: the triangle inequality suffices.
    have t1 : dist C F ≤ dist C B + dist B F := dist_triangle C B F
    have t2 : dist C B = dist B C := dist_comm C B
    have t3 : dist B F = dist B C := calc
      dist B F = dist E F := by rw [hBE]
      _ = dist D E := hDEF.symm
      _ = dist D B := by rw [hBE]
      _ = dist B D := dist_comm D B
      _ = dist B C := hBD
    have t4 : dist B C ≤ dist A G + dist G B := by
      rw [← hABC]
      exact dist_triangle A G B
    have t5 : dist B C ≤ dist D H + dist H E := by
      rw [← hBD, dist_comm B D, hBE]
      exact dist_triangle D H E
    have t6 : (0 : ℝ) ≤ dist G H := dist_nonneg
    linarith [t1, t2, t3, t4, t5, t6]
  · -- Main case: reflect in the line `BE`.
    have hBS : B ∈ affineSpan ℝ ({B, E} : Set P) :=
      mem_affineSpan ℝ (Set.mem_insert B {E})
    have hES : E ∈ affineSpan ℝ ({B, E} : Set P) :=
      mem_affineSpan ℝ (Set.mem_insert_of_mem B (Set.mem_singleton E))
    haveI : Nonempty (affineSpan ℝ ({B, E} : Set P)) := ⟨⟨B, hBS⟩⟩
    haveI : CompleteSpace (affineSpan ℝ ({B, E} : Set P)).direction :=
      FiniteDimensional.complete ℝ _
    -- The reflection in the line `BE` fixes `B` and `E` and swaps `A` and `D`.
    have hρB : reflection (affineSpan ℝ {B, E}) B = B := (reflection_eq_self_iff B).mpr hBS
    have hρE : reflection (affineSpan ℝ {B, E}) E = E := (reflection_eq_self_iff E).mpr hES
    have hρA : reflection (affineSpan ℝ {B, E}) A = D := by
      have k1 : dist (reflection (affineSpan ℝ {B, E}) A) B = dist A B := calc
        dist (reflection (affineSpan ℝ {B, E}) A) B
            = dist A (reflection (affineSpan ℝ {B, E}) B) := (dist_reflection _ A B).symm
        _ = dist A B := by rw [hρB]
      have k2 : dist D B = dist A B := calc
        dist D B = dist B D := dist_comm D B
        _ = dist B C := hBD
        _ = dist A B := hABC.symm
      have e1 : dist D B = dist (reflection (affineSpan ℝ {B, E}) A) B := k2.trans k1.symm
      have k3 : dist (reflection (affineSpan ℝ {B, E}) A) E = dist A E := calc
        dist (reflection (affineSpan ℝ {B, E}) A) E
            = dist A (reflection (affineSpan ℝ {B, E}) E) := (dist_reflection _ A E).symm
        _ = dist A E := by rw [hρE]
      have k4 : dist D E = dist A E := calc
        dist D E = dist E F := hDEF
        _ = dist A E := hAE.symm
      have e2 : dist D E = dist (reflection (affineSpan ℝ {B, E}) A) E := k4.trans k3.symm
      rcases eq_or_eq_reflection_of_dist_eq_of_dist_eq hdim hBE e1 e2 with h | h
      · exact h.symm
      · exfalso
        rw [reflection_reflection] at h
        exact hAD h.symm
    -- Ptolemy's inequality in `C'AGB`, where `C'` is the reflection of `C`.
    have keyG : dist (reflection (affineSpan ℝ {B, E}) C) G ≤ dist A G + dist G B := by
      have pt := mul_dist_le_mul_dist_add_mul_dist (reflection (affineSpan ℝ {B, E}) C) A G B
      have e1 : dist (reflection (affineSpan ℝ {B, E}) C) A = dist C D := calc
        dist (reflection (affineSpan ℝ {B, E}) C) A
            = dist C (reflection (affineSpan ℝ {B, E}) A) := (dist_reflection _ C A).symm
        _ = dist C D := by rw [hρA]
      have e2 : dist (reflection (affineSpan ℝ {B, E}) C) B = dist C B := calc
        dist (reflection (affineSpan ℝ {B, E}) C) B
            = dist C (reflection (affineSpan ℝ {B, E}) B) := (dist_reflection _ C B).symm
        _ = dist C B := by rw [hρB]
      have e3 : dist C D = dist A B := by rw [← hBCD, ← hABC]
      have e4 : dist C B = dist A B := by rw [dist_comm C B, ← hABC]
      rw [e1, e2, e3, e4] at pt
      have hABpos : 0 < dist A B := dist_pos.mpr hAB_ne
      have h5 : dist (reflection (affineSpan ℝ {B, E}) C) G ≤ dist G B + dist A G := by
        have h6 : dist A B * dist G B + dist A G * dist A B
            = (dist G B + dist A G) * dist A B := by ring
        have h7 : dist (reflection (affineSpan ℝ {B, E}) C) G * dist A B
            ≤ (dist G B + dist A G) * dist A B := by linarith [pt, h6]
        exact le_of_mul_le_mul_right h7 hABpos
      linarith [h5]
    -- Ptolemy's inequality in `F'DHE`, where `F'` is the reflection of `F`.
    have keyH : dist (reflection (affineSpan ℝ {B, E}) F) H ≤ dist D H + dist H E := by
      have hρD : reflection (affineSpan ℝ {B, E}) D = A := by
        rw [← hρA]
        exact reflection_reflection _ A
      have pt := mul_dist_le_mul_dist_add_mul_dist (reflection (affineSpan ℝ {B, E}) F) D H E
      have f1 : dist (reflection (affineSpan ℝ {B, E}) F) D = dist F A := calc
        dist (reflection (affineSpan ℝ {B, E}) F) D
            = dist F (reflection (affineSpan ℝ {B, E}) D) := (dist_reflection _ F D).symm
        _ = dist F A := by rw [hρD]
      have f2 : dist (reflection (affineSpan ℝ {B, E}) F) E = dist F E := calc
        dist (reflection (affineSpan ℝ {B, E}) F) E
            = dist F (reflection (affineSpan ℝ {B, E}) E) := (dist_reflection _ F E).symm
        _ = dist F E := by rw [hρE]
      have f3 : dist F A = dist D E := by rw [← hEFA, ← hDEF]
      have f4 : dist F E = dist D E := by rw [dist_comm F E, ← hDEF]
      rw [f1, f2, f3, f4] at pt
      have hDEpos : 0 < dist D E := dist_pos.mpr hDE_ne
      have h5 : dist (reflection (affineSpan ℝ {B, E}) F) H ≤ dist H E + dist D H := by
        have h6 : dist D E * dist H E + dist D H * dist D E
            = (dist H E + dist D H) * dist D E := by ring
        have h7 : dist (reflection (affineSpan ℝ {B, E}) F) H * dist D E
            ≤ (dist H E + dist D H) * dist D E := by linarith [pt, h6]
        exact le_of_mul_le_mul_right h7 hDEpos
      linarith [h5]
    -- The triangle inequality along the path `C' → G → H → F'`.
    have hCF : dist C F
        = dist (reflection (affineSpan ℝ {B, E}) C) (reflection (affineSpan ℝ {B, E}) F) :=
      ((reflection (affineSpan ℝ {B, E})).dist_map C F).symm
    have tri1 : dist (reflection (affineSpan ℝ {B, E}) C) (reflection (affineSpan ℝ {B, E}) F)
        ≤ dist (reflection (affineSpan ℝ {B, E}) C) G
          + dist G (reflection (affineSpan ℝ {B, E}) F) := dist_triangle _ _ _
    have tri2 : dist G (reflection (affineSpan ℝ {B, E}) F)
        ≤ dist G H + dist H (reflection (affineSpan ℝ {B, E}) F) := dist_triangle _ _ _
    have hcomm : dist H (reflection (affineSpan ℝ {B, E}) F)
        = dist (reflection (affineSpan ℝ {B, E}) F) H := dist_comm _ _
    rw [hCF]
    linarith [keyG, keyH, tri1, tri2, hcomm]

end Imo1995P5
