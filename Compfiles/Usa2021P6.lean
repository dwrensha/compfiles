/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Circumcenter
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 2021, Problem 6

Let ABCDEF be a convex hexagon satisfying AB ∥ DE, BC ∥ EF, CD ∥ FA, and
AB · DE = BC · EF = CD · FA.
Let X, Y, and Z be the midpoints of AD, BE, and CF. Prove that the circumcenter
of △ACE, the circumcenter of △BDF, and the orthocenter of △XYZ are collinear.

## Formalization notes

* The hexagon is taken to be a convex hexagon. Convexity together with the
  parallel-side hypotheses implies that the opposite sides are anti-parallel,
  i.e. there exist *positive* reals `p`, `q`, `r` with `E - D = p • (A - B)`,
  `F - E = q • (B - C)` and `A - F = r • (C - D)`; we take these as hypotheses.
* We also assume the non-degeneracy conditions `¬ Collinear {A, B, C}`,
  `¬ Collinear {C, D, E}`, `¬ Collinear {A, C, E}`, `¬ Collinear {B, D, F}`
  (all consequences of convexity) and `¬ Collinear {X, Y, Z}`, which is
  needed for the orthocenter of `△XYZ` to exist at all (e.g. in a regular
  hexagon `X = Y = Z`).
* Circumcenters and orthocenters are given by their defining properties
  (`IsCircumcenter`, `IsOrthocenter`); in the plane these determine the
  points uniquely (see `eq_of_isCircumcenter`, `eq_of_isOrthocenter`).
-/

namespace Usa2021P6

open RealInnerProductSpace Affine

/-- The Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- `O` is a circumcenter of the triangle `P₁P₂P₃`: it is equidistant from the
three vertices. For non-collinear `P₁P₂P₃` in the plane this point is unique. -/
def IsCircumcenter (O P₁ P₂ P₃ : Plane) : Prop :=
  dist O P₁ = dist O P₂ ∧ dist O P₂ = dist O P₃

/-- `H` is an orthocenter of the triangle `XYZ`: it lies on the altitudes
through `X` and through `Y` (the third altitude condition follows). For
non-collinear `XYZ` in the plane this point is unique. -/
def IsOrthocenter (H X Y Z : Plane) : Prop :=
  ⟪H - X, Z - Y⟫ = 0 ∧ ⟪H - Y, X - Z⟫ = 0

snip begin

/-- Squared distance in the plane, coordinate form. -/
lemma dist_sq_eq (a b : Plane) :
    dist a b ^ 2 = (a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2 := by
  rw [dist_eq_norm, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp [sq_abs]

/-- Inner product in the plane, coordinate form. -/
lemma inner_eq (a b : Plane) : ⟪a, b⟫ = a 0 * b 0 + a 1 * b 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp [RCLike.inner_apply]
  ring

/-- If the segments `WN` and `XY` have the same midpoint and are parallel
(with ratio `l`), then for any point `O` the equality `OW = ON` is equivalent
to `OX = OY`; we record the precise squared-distance identity. -/
lemma dist_sq_sub_eq_smul_dist_sq_sub {O W N X Y : Plane} {l : ℝ}
    (hsum : W + N = X + Y) (hpar : N - W = l • (Y - X)) :
    dist O W ^ 2 - dist O N ^ 2 = -l * (dist O Y ^ 2 - dist O X ^ 2) := by
  have hN : N = W + l • (Y - X) := by rw [← hpar]; abel
  rw [hN] at hsum
  have hW2 : (2 : ℝ) • W = X + Y - l • (Y - X) := by
    calc (2 : ℝ) • W = (W + (W + l • (Y - X))) - l • (Y - X) := by module
    _ = X + Y - l • (Y - X) := by rw [hsum]
  have hWc : ∀ i : Fin 2, W i = (X i + Y i - l * (Y i - X i)) / 2 := by
    intro i
    have h := congrArg (fun x : Plane => x i) hW2
    simp only [PiLp.smul_apply, PiLp.sub_apply, PiLp.add_apply, smul_eq_mul] at h
    linarith
  have hNc : ∀ i : Fin 2, N i = W i + l * (Y i - X i) := by
    intro i
    have h := congrArg (fun x : Plane => x i) hN
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at h
    linarith
  rw [dist_sq_eq O W, dist_sq_eq O N, dist_sq_eq O Y, dist_sq_eq O X,
    hNc 0, hNc 1, hWc 0, hWc 1]
  ring

/-- Power of the point `Y` with respect to a circle centered at `O` through
`W` and `N`, computed along the secant line `YWN` with `N - Y = t • (W - Y)`:
the power equals `t * dist Y W ^ 2`. -/
lemma power_eq_smul_dist_sq {O W N Y : Plane} {t : ℝ}
    (hρ : dist O W = dist O N) (hsec : N - Y = t • (W - Y)) (ht : t ≠ 1) :
    dist Y O ^ 2 - dist O W ^ 2 = t * dist Y W ^ 2 := by
  have hN : N = Y + t • (W - Y) := by rw [← hsec]; abel
  rw [hN] at hρ
  have hρ2 := congrArg (· ^ 2) hρ
  rw [dist_sq_eq O W, dist_sq_eq O (Y + t • (W - Y))] at hρ2
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at hρ2
  rw [dist_sq_eq Y O, dist_sq_eq O W, dist_sq_eq Y W]
  apply mul_left_cancel₀ (sub_ne_zero.mpr (Ne.symm ht) : (1 : ℝ) - t ≠ 0)
  linear_combination -hρ2

/-- If `W, N, V` lie on a circle centered at `O`, and the lines `WN` and `VM`
meet at `Y` with equal (signed) power products, then `M` also lies on the
circle. -/
lemma dist_eq_of_power_eq {O W N V M Y : Plane} {t s : ℝ}
    (hWN : dist O W = dist O N) (hWV : dist O W = dist O V)
    (hsec₁ : N - Y = t • (W - Y)) (ht : t ≠ 1)
    (hsec₂ : M - Y = s • (V - Y))
    (hpow : ⟪W - Y, N - Y⟫ = ⟪V - Y, M - Y⟫) :
    dist O M = dist O W := by
  have hB := power_eq_smul_dist_sq hWN hsec₁ ht
  rw [hsec₁, hsec₂] at hpow
  have hts : t * dist Y W ^ 2 = s * dist Y V ^ 2 := by
    have e1 : ⟪W - Y, t • (W - Y)⟫ = t * ((W 0 - Y 0) ^ 2 + (W 1 - Y 1) ^ 2) := by
      rw [inner_eq]
      simp [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    have e2 : ⟪V - Y, s • (V - Y)⟫ = s * ((V 0 - Y 0) ^ 2 + (V 1 - Y 1) ^ 2) := by
      rw [inner_eq]
      simp [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [e1, e2] at hpow
    rw [dist_sq_eq, dist_sq_eq]
    linear_combination hpow
  have hWV2 := congrArg (· ^ 2) hWV
  rw [dist_sq_eq Y O, dist_sq_eq O W, dist_sq_eq Y W] at hB
  rw [dist_sq_eq Y W, dist_sq_eq Y V] at hts
  rw [dist_sq_eq O W, dist_sq_eq O V] at hWV2
  have hM : M = Y + s • (V - Y) := by rw [← hsec₂]; abel
  have h2 : dist O M ^ 2 = dist O W ^ 2 := by
    rw [hM, dist_sq_eq O (Y + s • (V - Y)), dist_sq_eq O W]
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    linear_combination (1 - s) * hB + (1 - s) * hts - s * hWV2
  exact (mul_self_inj_of_nonneg dist_nonneg dist_nonneg).mp (by rwa [pow_two, pow_two] at h2)

/-- In the plane, a vector orthogonal to two linearly independent vectors is
zero. -/
lemma eq_zero_of_inner_indep {v u₁ u₂ : Plane}
    (hli : LinearIndependent ℝ ![u₁, u₂]) (h1 : ⟪u₁, v⟫ = 0) (h2 : ⟪u₂, v⟫ = 0) :
    v = 0 := by
  let hb : Module.Basis (Fin 2) ℝ Plane :=
    basisOfLinearIndependentOfCardEqFinrank hli
      (by rw [Fintype.card_fin, finrank_euclideanSpace_fin])
  have hbb : ⇑hb = ![u₁, u₂] := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have hvv : ⟪v, v⟫ = 0 := by
    nth_rewrite 1 [← hb.sum_repr v]
    rw [sum_inner, Fin.sum_univ_two, hbb]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, real_inner_smul_left, h1,
      h2, mul_zero, add_zero]
  exact inner_self_eq_zero.mp hvv

/-- If `P₃ - P₂` is a scalar multiple of `P₂ - P₁`, the three points are
collinear. -/
lemma collinear_of_smul_sub {P₁ P₂ P₃ : Plane} {c : ℝ} (h : P₃ - P₂ = c • (P₂ - P₁)) :
    Collinear ℝ ({P₁, P₂, P₃} : Set Plane) := by
  have hP₃ : P₃ = AffineMap.lineMap P₁ P₂ (1 + c) := by
    rw [AffineMap.lineMap_apply_module']
    have hs : P₃ = c • (P₂ - P₁) + P₂ := by rw [← h]; abel
    rw [hs, add_smul, one_smul]
    abel
  have hmem := AffineMap.lineMap_mem_affineSpan_pair (k := ℝ) (1 + c) P₁ P₂
  have hcol := collinear_insert_of_mem_affineSpan_pair (k := ℝ) hmem
  rw [hP₃]
  have hset : ({P₁, P₂, AffineMap.lineMap P₁ P₂ (1 + c)} : Set Plane) =
      {AffineMap.lineMap P₁ P₂ (1 + c), P₁, P₂} := by
    ext p
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [hset]
  exact hcol

lemma collinear_of_eq₁ {P₁ P₂ P₃ : Plane} (h : P₁ = P₂) :
    Collinear ℝ ({P₁, P₂, P₃} : Set Plane) := by
  rw [h]
  have hs : ({P₂, P₂, P₃} : Set Plane) = {P₂, P₃} := by
    ext p
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [hs]
  exact collinear_pair ℝ _ _

lemma collinear_of_eq₂ {P₁ P₂ P₃ : Plane} (h : P₁ = P₃) :
    Collinear ℝ ({P₁, P₂, P₃} : Set Plane) := by
  rw [h]
  have hs : ({P₃, P₂, P₃} : Set Plane) = {P₂, P₃} := by
    ext p
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [hs]
  exact collinear_pair ℝ _ _

lemma collinear_of_eq₃ {P₁ P₂ P₃ : Plane} (h : P₂ = P₃) :
    Collinear ℝ ({P₁, P₂, P₃} : Set Plane) := by
  rw [h]
  have hs : ({P₁, P₃, P₃} : Set Plane) = {P₁, P₃} := by
    ext p
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [hs]
  exact collinear_pair ℝ _ _

/-- If `N - W = c₁ • u` is a nonzero multiple of the nonzero vector `u`,
`V - W = c₂ • u + c₃ • w` with `c₃ ≠ 0`, and `W, N, V` are collinear,
then `w` is a scalar multiple of `u`. -/
lemma smul_of_collinear {W N V u w : Plane} {c₁ c₂ c₃ : ℝ}
    (hc₁ : c₁ ≠ 0) (hu : u ≠ 0) (hc₃ : c₃ ≠ 0)
    (hNW : N - W = c₁ • u) (hVW : V - W = c₂ • u + c₃ • w)
    (hcol : Collinear ℝ ({W, N, V} : Set Plane)) :
    ∃ d : ℝ, w = d • u := by
  rw [collinear_iff_of_mem (show W ∈ ({W, N, V} : Set Plane) by simp)] at hcol
  obtain ⟨v, hv⟩ := hcol
  obtain ⟨a, ha⟩ := hv N (by simp)
  obtain ⟨b, hb⟩ := hv V (by simp)
  rw [vadd_eq_add] at ha hb
  have haN : N - W = a • v := by rw [ha]; abel
  have hbV : V - W = b • v := by rw [hb]; abel
  rw [hNW] at haN
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at haN
    rw [smul_eq_zero] at haN
    rcases haN with h | h
    · exact hc₁ h
    · exact hu h
  have hv2 : v = (a⁻¹ * c₁) • u := by
    have hh : (a⁻¹ * c₁) • u = a⁻¹ • (a • v) := by rw [← haN, smul_smul]
    rw [hh]
    exact (inv_smul_smul₀ ha0 v).symm
  rw [hv2, smul_smul] at hbV
  rw [hVW] at hbV
  refine ⟨(b * (a⁻¹ * c₁) - c₂) / c₃, ?_⟩
  have key : c₃ • w = (b * (a⁻¹ * c₁) - c₂) • u := by
    calc c₃ • w = (c₂ • u + c₃ • w) - c₂ • u := by module
    _ = (b * (a⁻¹ * c₁)) • u - c₂ • u := by rw [hbV]
    _ = (b * (a⁻¹ * c₁) - c₂) • u := by module
  rw [show ((b * (a⁻¹ * c₁) - c₂) / c₃) • u = c₃⁻¹ • ((b * (a⁻¹ * c₁) - c₂) • u) by
    rw [smul_smul]; congr 1; rw [div_eq_mul_inv, mul_comm]]
  rw [eq_inv_smul_iff₀ hc₃]
  exact key

/-- Uniqueness of the circumcenter of a non-degenerate triangle in the
plane. -/
lemma eq_of_isCircumcenter {O O' P₁ P₂ P₃ : Plane}
    (hnc : ¬ Collinear ℝ ({P₁, P₂, P₃} : Set Plane))
    (hO : IsCircumcenter O P₁ P₂ P₃) (hO' : IsCircumcenter O' P₁ P₂ P₃) :
    O = O' := by
  obtain ⟨hO1, hO2⟩ := hO
  obtain ⟨hO'1, hO'2⟩ := hO'
  have e1 : ⟪P₂ - P₁, O - O'⟫ = 0 := by
    have s1 := congrArg (· ^ 2) hO1
    have s2 := congrArg (· ^ 2) hO'1
    rw [dist_sq_eq, dist_sq_eq] at s1 s2
    rw [inner_eq]
    simp only [PiLp.sub_apply]
    linear_combination (s1 - s2) / 2
  have e2 : ⟪P₃ - P₂, O - O'⟫ = 0 := by
    have s1 := congrArg (· ^ 2) hO2
    have s2 := congrArg (· ^ 2) hO'2
    rw [dist_sq_eq, dist_sq_eq] at s1 s2
    rw [inner_eq]
    simp only [PiLp.sub_apply]
    linear_combination (s1 - s2) / 2
  have hli : LinearIndependent ℝ ![P₂ - P₁, P₃ - P₂] := by
    rw [linearIndependent_fin2]
    refine ⟨?_, ?_⟩
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      intro h
      rw [sub_eq_zero] at h
      exact hnc (collinear_of_eq₃ h.symm)
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      intro a ha
      apply hnc
      have hP : P₁ = AffineMap.lineMap P₂ P₃ (-a) := by
        rw [AffineMap.lineMap_apply_module', neg_smul, ha]
        abel
      rw [hP]
      exact collinear_insert_of_mem_affineSpan_pair (AffineMap.lineMap_mem_affineSpan_pair _ _ _)
  exact sub_eq_zero.mp (eq_zero_of_inner_indep hli e1 e2)

/-- Uniqueness of the orthocenter of a non-degenerate triangle in the
plane. -/
lemma eq_of_isOrthocenter {H H' X Y Z : Plane}
    (hnc : ¬ Collinear ℝ ({X, Y, Z} : Set Plane))
    (hH : IsOrthocenter H X Y Z) (hH' : IsOrthocenter H' X Y Z) :
    H = H' := by
  obtain ⟨hH1, hH2⟩ := hH
  obtain ⟨hH'1, hH'2⟩ := hH'
  have e1 : ⟪Z - Y, H - H'⟫ = 0 := by
    rw [inner_eq] at hH1 hH'1 ⊢
    simp only [PiLp.sub_apply] at hH1 hH'1 ⊢
    linear_combination hH1 - hH'1
  have e2 : ⟪X - Z, H - H'⟫ = 0 := by
    rw [inner_eq] at hH2 hH'2 ⊢
    simp only [PiLp.sub_apply] at hH2 hH'2 ⊢
    linear_combination hH2 - hH'2
  have hli : LinearIndependent ℝ ![Z - Y, X - Z] := by
    rw [linearIndependent_fin2]
    refine ⟨?_, ?_⟩
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      intro h
      rw [sub_eq_zero] at h
      exact hnc (collinear_of_eq₂ h)
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      intro a ha
      apply hnc
      have hY : Y = AffineMap.lineMap Z X (-a) := by
        rw [AffineMap.lineMap_apply_module', neg_smul, ha]
        abel
      rw [hY]
      have hcol := collinear_insert_of_mem_affineSpan_pair
        (AffineMap.lineMap_mem_affineSpan_pair (-a) Z X)
      rw [show ({X, AffineMap.lineMap Z X (-a), Z} : Set Plane) =
          {AffineMap.lineMap Z X (-a), Z, X} by
        ext p
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto]
      exact hcol
  exact sub_eq_zero.mp (eq_zero_of_inner_indep hli e1 e2)

snip end

set_option maxHeartbeats 400000

/-- USA Mathematical Olympiad 2021, Problem 6. -/
problem usa2021_p6 (A B C D E F X Y Z : Plane)
    (hX : X = midpoint ℝ A D) (hY : Y = midpoint ℝ B E) (hZ : Z = midpoint ℝ C F)
    (hpar₁ : ∃ p : ℝ, 0 < p ∧ E - D = p • (A - B))
    (hpar₂ : ∃ q : ℝ, 0 < q ∧ F - E = q • (B - C))
    (hpar₃ : ∃ r : ℝ, 0 < r ∧ A - F = r • (C - D))
    (hprod₁ : dist A B * dist D E = dist B C * dist E F)
    (hprod₂ : dist B C * dist E F = dist C D * dist F A)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane))
    (hCDE : ¬ Collinear ℝ ({C, D, E} : Set Plane))
    (hACE : ¬ Collinear ℝ ({A, C, E} : Set Plane))
    (hBDF : ¬ Collinear ℝ ({B, D, F} : Set Plane))
    (hXYZ : ¬ Collinear ℝ ({X, Y, Z} : Set Plane))
    (O₁ O₂ H : Plane)
    (hO₁ : IsCircumcenter O₁ A C E) (hO₂ : IsCircumcenter O₂ B D F)
    (hH : IsOrthocenter H X Y Z) :
    Collinear ℝ ({O₁, O₂, H} : Set Plane) := by
  obtain ⟨p, hp, hpE⟩ := hpar₁
  obtain ⟨q, hq, hqF⟩ := hpar₂
  obtain ⟨r, hr, hrA⟩ := hpar₃
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hq0 : q ≠ 0 := ne_of_gt hq
  have hr0 : r ≠ 0 := ne_of_gt hr
  -- midpoint equations in vector form
  have hhalf : (⅟2 : ℝ) = 1 / 2 := by norm_num
  have xE : X = (1 / 2 : ℝ) • (A + D) := by rw [hX, midpoint_eq_smul_add, hhalf]
  have yE : Y = (1 / 2 : ℝ) • (B + E) := by rw [hY, midpoint_eq_smul_add, hhalf]
  have zE : Z = (1 / 2 : ℝ) • (C + F) := by rw [hZ, midpoint_eq_smul_add, hhalf]
  -- eliminate `E`, `F`, `A` via the parallel-side conditions
  have eE : E = D + p • (A - B) := by rw [← hpE]; abel
  have fE : F = E + q • (B - C) := by rw [← hqF]; abel
  have aE : A = F + r • (C - D) := by rw [← hrA]; abel
  have fE2 : F = A - r • (C - D) := by rw [aE]; module
  -- midpoints of the sides of the two triangles
  set M : Plane := (1 / 2 : ℝ) • (C + E) with hM
  set N : Plane := (1 / 2 : ℝ) • (E + A) with hN
  set P : Plane := (1 / 2 : ℝ) • (A + C) with hP
  set U : Plane := (1 / 2 : ℝ) • (D + F) with hU
  set V : Plane := (1 / 2 : ℝ) • (F + B) with hV
  set W : Plane := (1 / 2 : ℝ) • (B + D) with hW
  -- key vector identities for the sides and diagonals of the three trapezoids
  have vYmx : Y - X = ((1 - p) / 2) • (B - A) := by rw [yE, xE, eE]; module
  have vZmY : Z - Y = ((1 - q) / 2) • (C - B) := by rw [zE, yE, fE]; module
  have vXmZ : X - Z = ((1 - r) / 2) • (D - C) := by rw [xE, zE, aE]; module
  have vNmx : N - W = (-(1 + p) / 2) • (B - A) := by rw [hN, hW, eE]; module
  have vMmV : M - V = ((1 + q) / 2) • (C - B) := by rw [hM, hV, fE]; module
  have vPmU : P - U = (-(1 + r) / 2 : ℝ) • (D - C) := by rw [hP, hU, aE]; module
  have vWmY : W - Y = (p / 2) • (B - A) := by rw [hW, yE, eE]; module
  have vNmY : N - Y = (-1 / 2 : ℝ) • (B - A) := by rw [hN, yE]; module
  have vVmY : V - Y = (q / 2) • (B - C) := by rw [hV, yE, fE]; module
  have vMmY : M - Y = (-1 / 2 : ℝ) • (B - C) := by rw [hM, yE]; module
  have vWmX : W - X = (1 / 2 : ℝ) • (B - A) := by rw [hW, xE]; module
  have vNmX : N - X = (-p / 2) • (B - A) := by rw [hN, xE, eE]; module
  have vUmX : U - X = (-r / 2) • (C - D) := by rw [hU, xE, aE]; module
  have vPmX : P - X = (1 / 2 : ℝ) • (C - D) := by rw [hP, xE]; module
  have sum1 : W + N = X + Y := by rw [hW, hN, xE, yE]; module
  have sum2 : V + M = Y + Z := by rw [hV, hM, yE, zE]; module
  have sum3 : U + P = Z + X := by rw [hU, hP, zE, xE]; module
  -- non-degeneracy: the side ratios are not `1`
  have hp1ne : p ≠ 1 := by
    intro h
    apply hXYZ
    have h1 : Y = X := by
      have h2 := vYmx
      rw [h] at h2
      simp at h2
      exact sub_eq_zero.mp h2
    exact collinear_of_eq₁ h1.symm
  have hq1ne : q ≠ 1 := by
    intro h
    apply hXYZ
    have h1 : Z = Y := by
      have h2 := vZmY
      rw [h] at h2
      simp at h2
      exact sub_eq_zero.mp h2
    exact collinear_of_eq₃ h1.symm
  have hr1ne : r ≠ 1 := by
    intro h
    apply hXYZ
    have h1 : X = Z := by
      have h2 := vXmZ
      rw [h] at h2
      simp at h2
      exact sub_eq_zero.mp h2
    exact collinear_of_eq₂ h1
  -- the product conditions in squared form
  have hdE : dist D E = p * dist A B := by
    have h1 : D - E = -(p • (A - B)) := by rw [← hpE]; abel
    rw [dist_eq_norm, dist_eq_norm, h1, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (le_of_lt hp)]
  have hdF : dist E F = q * dist B C := by
    have h1 : E - F = -(q • (B - C)) := by rw [← hqF]; abel
    rw [dist_eq_norm, dist_eq_norm, h1, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (le_of_lt hq)]
  have hdA : dist F A = r * dist C D := by
    have h1 : F - A = -(r • (C - D)) := by rw [← hrA]; abel
    rw [dist_eq_norm, dist_eq_norm, h1, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (le_of_lt hr)]
  have hpq : p * dist A B ^ 2 = q * dist B C ^ 2 := by
    rw [hdE, hdF] at hprod₁
    linear_combination hprod₁
  have hqr : q * dist B C ^ 2 = r * dist C D ^ 2 := by
    rw [hdF, hdA] at hprod₂
    linear_combination hprod₂
  rw [dist_sq_eq, dist_sq_eq] at hpq
  rw [dist_sq_eq, dist_sq_eq] at hqr
  -- non-collinearity of the two triples spanning the six-point circles
  have hBA : B - A ≠ 0 := by
    intro h
    apply hABC
    rw [sub_eq_zero] at h
    exact collinear_of_eq₁ h.symm
  have vVW : V - W = (-p / 2) • (B - A) + (q / 2) • (B - C) := by
    rw [hV, hW, fE, eE]; module
  have hWNV : ¬ Collinear ℝ ({W, N, V} : Set Plane) := by
    intro hcol
    obtain ⟨d, hd⟩ := smul_of_collinear (u := B - A) (w := B - C)
      (c₁ := -(1 + p) / 2) (c₂ := -p / 2) (c₃ := q / 2)
      (div_ne_zero (neg_ne_zero.mpr (ne_of_gt (by linarith : (0 : ℝ) < 1 + p))) two_ne_zero)
      hBA (div_ne_zero hq0 two_ne_zero) vNmx vVW hcol
    apply hABC
    apply collinear_of_smul_sub (c := -d)
    rw [← neg_sub, hd, ← neg_smul]
  have vUW : U - W = (-1 / 2 : ℝ) • (B - A) + (r / 2) • (D - C) := by
    rw [hU, hW, fE2]; module
  have hWNU : ¬ Collinear ℝ ({W, N, U} : Set Plane) := by
    intro hcol
    obtain ⟨d, hd⟩ := smul_of_collinear (u := B - A) (w := D - C)
      (c₁ := -(1 + p) / 2) (c₂ := -1 / 2) (c₃ := r / 2)
      (div_ne_zero (neg_ne_zero.mpr (ne_of_gt (by linarith : (0 : ℝ) < 1 + p))) two_ne_zero)
      hBA (div_ne_zero hr0 two_ne_zero) vNmx vUW hcol
    by_cases hd0 : d = 0
    · rw [hd0, zero_smul] at hd
      apply hCDE
      rw [sub_eq_zero] at hd
      exact collinear_of_eq₁ hd.symm
    · apply hCDE
      apply collinear_of_smul_sub (c := -p / d)
      have sc : (-p / d) * d = -p := by field_simp
      have hED : E - D = (-p) • (B - A) := by rw [hpE]; module
      rw [hd, smul_smul, sc, hED]
  -- the first six-point circle, through `W, N, V, M`
  let s₁ : Affine.Simplex ℝ Plane 2 :=
    ⟨![W, N, V], affineIndependent_iff_not_collinear_set.mpr hWNV⟩
  set O' : Plane := s₁.circumcenter with hO'def
  have hρW : dist O' W = s₁.circumradius := by
    rw [dist_comm]; exact s₁.dist_circumcenter_eq_circumradius 0
  have hρN : dist O' N = s₁.circumradius := by
    rw [dist_comm]; exact s₁.dist_circumcenter_eq_circumradius 1
  have hρV : dist O' V = s₁.circumradius := by
    rw [dist_comm]; exact s₁.dist_circumcenter_eq_circumradius 2
  have hsec1 : N - Y = (-1 / p) • (W - Y) := by
    have sc : (-1 / p) * (p / 2) = -1 / 2 := by field_simp
    rw [vNmY, vWmY, smul_smul, sc]
  have ht1 : (-1 / p : ℝ) ≠ 1 := by
    intro h
    field_simp at h
    linarith
  have hsec2 : M - Y = (-1 / q) • (V - Y) := by
    have sc : (-1 / q) * (q / 2) = -1 / 2 := by field_simp
    rw [vMmY, vVmY, smul_smul, sc]
  have hpow1 : ⟪W - Y, N - Y⟫ = ⟪V - Y, M - Y⟫ := by
    rw [vWmY, vNmY, vVmY, vMmY, inner_eq, inner_eq]
    simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    linear_combination (-1 / 4) * hpq
  have hM1 : dist O' M = s₁.circumradius :=
    (dist_eq_of_power_eq (hρW.trans hρN.symm) (hρW.trans hρV.symm) hsec1 ht1 hsec2
      hpow1).trans hρW
  -- the second six-point circle, through `W, N, U, P`
  let s₂ : Affine.Simplex ℝ Plane 2 :=
    ⟨![W, N, U], affineIndependent_iff_not_collinear_set.mpr hWNU⟩
  set O'' : Plane := s₂.circumcenter with hO''def
  have hρ2W : dist O'' W = s₂.circumradius := by
    rw [dist_comm]; exact s₂.dist_circumcenter_eq_circumradius 0
  have hρ2N : dist O'' N = s₂.circumradius := by
    rw [dist_comm]; exact s₂.dist_circumcenter_eq_circumradius 1
  have hρ2U : dist O'' U = s₂.circumradius := by
    rw [dist_comm]; exact s₂.dist_circumcenter_eq_circumradius 2
  have hsec3 : N - X = (-p) • (W - X) := by
    have sc : (-p) * (1 / 2 : ℝ) = -p / 2 := by ring
    rw [vNmX, vWmX, smul_smul, sc]
  have ht3 : (-p : ℝ) ≠ 1 := by
    intro h
    linarith
  have hsec4 : P - X = (-1 / r) • (U - X) := by
    have sc : (-1 / r) * (-r / 2) = 1 / 2 := by field_simp
    rw [vPmX, vUmX, smul_smul, sc]
  have hpow2 : ⟪W - X, N - X⟫ = ⟪U - X, P - X⟫ := by
    rw [vWmX, vNmX, vUmX, vPmX, inner_eq, inner_eq]
    simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    linear_combination (-1 / 4) * hpq + (-1 / 4) * hqr
  have hρ2P : dist O'' P = s₂.circumradius :=
    (dist_eq_of_power_eq (hρ2W.trans hρ2N.symm) (hρ2W.trans hρ2U.symm) hsec3 ht3 hsec4
      hpow2).trans hρ2W
  -- both circle centers are equidistant from `X, Y, Z`
  have hparA : N - W = (-(1 + p) / (1 - p)) • (Y - X) := by
    have hp10 : (1 : ℝ) - p ≠ 0 := sub_ne_zero.mpr hp1ne.symm
    have sc : (-(1 + p) / (1 - p)) * ((1 - p) / 2) = -(1 + p) / 2 := by field_simp
    rw [vNmx, vYmx, smul_smul, sc]
  have hlA : ((1 + p) / (1 - p) : ℝ) ≠ 0 :=
    div_ne_zero (ne_of_gt (by linarith : (0 : ℝ) < 1 + p)) (sub_ne_zero.mpr hp1ne.symm)
  have hXY1 : dist O' X = dist O' Y := by
    have hA := dist_sq_sub_eq_smul_dist_sq_sub (O := O') (W := W) (N := N) (X := X) (Y := Y)
      (l := -(1 + p) / (1 - p)) sum1 hparA
    rw [hρW, hρN] at hA
    have h2 : dist O' Y ^ 2 = dist O' X ^ 2 := by
      have h3 : ((1 + p) / (1 - p)) * (dist O' Y ^ 2 - dist O' X ^ 2) = 0 := by
        linear_combination -hA
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact absurd h4 hlA
      · linarith [h4]
    exact ((mul_self_inj_of_nonneg dist_nonneg dist_nonneg).mp
      (by rwa [pow_two, pow_two] at h2)).symm
  have hparB : M - V = ((1 + q) / (1 - q)) • (Z - Y) := by
    have hq10 : (1 : ℝ) - q ≠ 0 := sub_ne_zero.mpr hq1ne.symm
    have sc : ((1 + q) / (1 - q)) * ((1 - q) / 2) = (1 + q) / 2 := by field_simp
    rw [vMmV, vZmY, smul_smul, sc]
  have hlB : (-(1 + q) / (1 - q) : ℝ) ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr (ne_of_gt (by linarith : (0 : ℝ) < 1 + q)))
      (sub_ne_zero.mpr hq1ne.symm)
  have hYZ1 : dist O' Y = dist O' Z := by
    have hA := dist_sq_sub_eq_smul_dist_sq_sub (O := O') (W := V) (N := M) (X := Y) (Y := Z)
      (l := (1 + q) / (1 - q)) sum2 hparB
    rw [hρV, hM1] at hA
    have h2 : dist O' Z ^ 2 = dist O' Y ^ 2 := by
      have h3 : (-(1 + q) / (1 - q)) * (dist O' Z ^ 2 - dist O' Y ^ 2) = 0 := by
        linear_combination -hA
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact absurd h4 hlB
      · linarith [h4]
    exact ((mul_self_inj_of_nonneg dist_nonneg dist_nonneg).mp
      (by rwa [pow_two, pow_two] at h2)).symm
  have hXY2 : dist O'' X = dist O'' Y := by
    have hA := dist_sq_sub_eq_smul_dist_sq_sub (O := O'') (W := W) (N := N) (X := X) (Y := Y)
      (l := -(1 + p) / (1 - p)) sum1 hparA
    rw [hρ2W, hρ2N] at hA
    have h2 : dist O'' Y ^ 2 = dist O'' X ^ 2 := by
      have h3 : ((1 + p) / (1 - p)) * (dist O'' Y ^ 2 - dist O'' X ^ 2) = 0 := by
        linear_combination -hA
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact absurd h4 hlA
      · linarith [h4]
    exact ((mul_self_inj_of_nonneg dist_nonneg dist_nonneg).mp
      (by rwa [pow_two, pow_two] at h2)).symm
  have hparC : P - U = ((1 + r) / (r - 1)) • (X - Z) := by
    have hr10 : r - 1 ≠ 0 := sub_ne_zero.mpr hr1ne
    have sc : ((1 + r) / (r - 1)) * ((1 - r) / 2) = -(1 + r) / 2 := by field_simp; ring
    rw [vPmU, vXmZ, smul_smul, sc]
  have hlC : (-(1 + r) / (r - 1) : ℝ) ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr (ne_of_gt (by linarith : (0 : ℝ) < 1 + r)))
      (sub_ne_zero.mpr hr1ne)
  have hZX2 : dist O'' Z = dist O'' X := by
    have hA := dist_sq_sub_eq_smul_dist_sq_sub (O := O'') (W := U) (N := P) (X := Z) (Y := X)
      (l := (1 + r) / (r - 1)) sum3 hparC
    rw [hρ2U, hρ2P] at hA
    have h2 : dist O'' X ^ 2 = dist O'' Z ^ 2 := by
      have h3 : (-(1 + r) / (r - 1)) * (dist O'' X ^ 2 - dist O'' Z ^ 2) = 0 := by
        linear_combination -hA
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact absurd h4 hlC
      · linarith [h4]
    exact ((mul_self_inj_of_nonneg dist_nonneg dist_nonneg).mp
      (by rwa [pow_two, pow_two] at h2)).symm
  -- the two circle centers coincide: `O'` is the center of the six-point circle
  have hOO : O' = O'' :=
    eq_of_isCircumcenter hXYZ ⟨hXY1, hYZ1⟩ ⟨hXY2, hXY2.symm.trans hZX2.symm⟩
  rw [← hOO] at hρ2W hρ2U hρ2P
  have hOU : dist O' U = s₁.circumradius := hρ2U.trans (hρ2W.symm.trans hρW)
  have hOP : dist O' P = s₁.circumradius := hρ2P.trans (hρ2W.symm.trans hρW)
  -- the circumcenter of `ACE` is `A + C + E - 2 • O'`
  set O₁c : Plane := A + C + E - (2 : ℝ) • O' with hO₁c
  have hO₁cA : dist O₁c A = 2 * s₁.circumradius := by
    have h1 : O₁c - A = (2 : ℝ) • (M - O') := by rw [hO₁c, hM]; module
    rw [dist_eq_norm, h1, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), ← dist_eq_norm, dist_comm M O', hM1]
  have hO₁cC : dist O₁c C = 2 * s₁.circumradius := by
    have h1 : O₁c - C = (2 : ℝ) • (N - O') := by rw [hO₁c, hN]; module
    rw [dist_eq_norm, h1, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), ← dist_eq_norm, dist_comm N O', hρN]
  have hO₁cE : dist O₁c E = 2 * s₁.circumradius := by
    have h1 : O₁c - E = (2 : ℝ) • (P - O') := by rw [hO₁c, hP]; module
    rw [dist_eq_norm, h1, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), ← dist_eq_norm, dist_comm P O', hOP]
  have hO₁cc : IsCircumcenter O₁c A C E := ⟨hO₁cA.trans hO₁cC.symm, hO₁cC.trans hO₁cE.symm⟩
  -- the circumcenter of `BDF` is `B + D + F - 2 • O'`
  set O₂c : Plane := B + D + F - (2 : ℝ) • O' with hO₂c
  have hO₂cB : dist O₂c B = 2 * s₁.circumradius := by
    have h1 : O₂c - B = (2 : ℝ) • (U - O') := by rw [hO₂c, hU]; module
    rw [dist_eq_norm, h1, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), ← dist_eq_norm, dist_comm U O', hOU]
  have hO₂cD : dist O₂c D = 2 * s₁.circumradius := by
    have h1 : O₂c - D = (2 : ℝ) • (V - O') := by rw [hO₂c, hV]; module
    rw [dist_eq_norm, h1, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), ← dist_eq_norm, dist_comm V O', hρV]
  have hO₂cF : dist O₂c F = 2 * s₁.circumradius := by
    have h1 : O₂c - F = (2 : ℝ) • (W - O') := by rw [hO₂c, hW]; module
    rw [dist_eq_norm, h1, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), ← dist_eq_norm, dist_comm W O', hρW]
  have hO₂cc : IsCircumcenter O₂c B D F := ⟨hO₂cB.trans hO₂cD.symm, hO₂cD.trans hO₂cF.symm⟩
  -- the orthocenter of `XYZ` is `X + Y + Z - 2 • O'`
  set Hc : Plane := X + Y + Z - (2 : ℝ) • O' with hHc
  have hperp1 : ⟪Hc - X, Z - Y⟫ = 0 := by
    have h1 : Hc - X = Y + Z - (2 : ℝ) • O' := by rw [hHc]; module
    have h2 := congrArg (· ^ 2) hYZ1
    rw [dist_sq_eq, dist_sq_eq] at h2
    rw [h1, inner_eq]
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    linear_combination -h2
  have hperp2 : ⟪Hc - Y, X - Z⟫ = 0 := by
    have h1 : Hc - Y = X + Z - (2 : ℝ) • O' := by rw [hHc]; module
    have h2 := congrArg (· ^ 2) (hXY1.trans hYZ1)
    rw [dist_sq_eq, dist_sq_eq] at h2
    rw [h1, inner_eq]
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    linear_combination h2
  have hHcc : IsOrthocenter Hc X Y Z := ⟨hperp1, hperp2⟩
  -- the orthocenter of `XYZ` is the midpoint of the two circumcenters
  have hmid : Hc = midpoint ℝ O₁c O₂c := by
    rw [midpoint_eq_smul_add, hhalf, hHc, hO₁c, hO₂c, xE, yE, zE]
    module
  -- transfer to the given centers by uniqueness, and conclude
  have hO₁eq : O₁ = O₁c := eq_of_isCircumcenter hACE hO₁ hO₁cc
  have hO₂eq : O₂ = O₂c := eq_of_isCircumcenter hBDF hO₂ hO₂cc
  have hHeq : H = Hc := eq_of_isOrthocenter hXYZ hH hHcc
  rw [hO₁eq, hO₂eq, hHeq, hmid]
  have hmem : midpoint ℝ O₁c O₂c ∈ affineSpan ℝ {O₁c, O₂c} :=
    AffineMap.lineMap_mem_affineSpan_pair _ _ _
  rw [show ({O₁c, O₂c, midpoint ℝ O₁c O₂c} : Set Plane) =
      insert (midpoint ℝ O₁c O₂c) {O₁c, O₂c} by
        ext p
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto]
  exact (collinear_insert_iff_of_mem_affineSpan hmem).mpr (collinear_pair ℝ _ _)

end Usa2021P6
