/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.Convex.Side
public import Mathlib.Analysis.Convex.StrictConvexBetween
public import Mathlib.Analysis.InnerProductSpace.OfNorm
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Projection
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1964, Problem 3

A circle is inscribed in triangle ABC with sides a, b, c. Tangents to the
circle parallel to the sides of the triangle are constructed. Each of these
tangents cuts off a triangle from ∆ABC. In each of these triangles a circle
is inscribed. Find the sum of the areas of all four inscribed circles.
-/

namespace Imo1964P3

open EuclideanGeometry
open scoped EuclideanGeometry Real

abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- `(O, r)` is a circle inscribed in the triangle `X Y Z`: the radius is
positive, the center `O` lies strictly inside the triangle (strictly on the
same side of each side line as the opposite vertex), and each side line is
tangent to the circle (its distance from `O` equals `r`). -/
structure Inscribed (X Y Z O : Pt) (r : ℝ) : Prop where
  pos : 0 < r
  sameSideYZ : (line[ℝ, Y, Z]).SSameSide X O
  sameSideZX : (line[ℝ, Z, X]).SSameSide Y O
  sameSideXY : (line[ℝ, X, Y]).SSameSide Z O
  tangentYZ : dist O (orthogonalProjection line[ℝ, Y, Z] O) = r
  tangentZX : dist O (orthogonalProjection line[ℝ, Z, X] O) = r
  tangentXY : dist O (orthogonalProjection line[ℝ, X, Y] O) = r

/-- `Y' Z'` is the chord cut on the side lines `X Y` and `X Z` of the triangle
`X Y Z` by the tangent line to the circle `(O, r)` which is parallel to the
side `Y Z` (and different from the line `Y Z` itself): `Y'` lies on the line
`X Y`, `Z'` lies on the line `X Z`, the line `Y' Z'` is parallel to `Y Z`,
tangent to the circle, and different from the line `Y Z`. -/
structure TangentCut (X Y Z Y' Z' O : Pt) (r : ℝ) : Prop where
  memXY : Y' ∈ line[ℝ, X, Y]
  memXZ : Z' ∈ line[ℝ, X, Z]
  parallel : vectorSpan ℝ {Y', Z'} = vectorSpan ℝ {Y, Z}
  tangent : dist O (orthogonalProjection line[ℝ, Y', Z'] O) = r
  ne : line[ℝ, Y', Z'] ≠ line[ℝ, Y, Z]

noncomputable determine answer (a b c : ℝ) : ℝ :=
  Real.pi * (a ^ 2 + b ^ 2 + c ^ 2) * (b + c - a) * (c + a - b) * (a + b - c) / (a + b + c) ^ 3

snip begin

/-- Twice the signed area of the triangle `X Y Z`
(positive iff `X Y Z` is oriented counterclockwise). -/
noncomputable def S (X Y Z : Pt) : ℝ := (Y 0 - X 0) * (Z 1 - X 1) - (Z 0 - X 0) * (Y 1 - X 1)

/-! ### Coordinate infrastructure -/

theorem smul_pt (t : ℝ) (x : Pt) (i : Fin 2) : (t • x) i = t * x i := by
  rw [PiLp.smul_apply, smul_eq_mul]
theorem add_pt (x y : Pt) (i : Fin 2) : (x + y) i = x i + y i := by
  rw [PiLp.add_apply]
theorem sub_pt (x y : Pt) (i : Fin 2) : (x - y) i = x i - y i := by
  rw [PiLp.sub_apply]

theorem Pt_ext {X Y : Pt} (h0 : X 0 = Y 0) (h1 : X 1 = Y 1) : X = Y := by
  apply WithLp.ofLp_injective (p := 2)
  funext i
  fin_cases i <;> assumption

theorem S_self (X Y : Pt) : S X Y Y = 0 := by
  unfold S
  ring

theorem S_self₂ (X Y : Pt) : S X X Y = 0 := by
  unfold S
  ring

theorem S_cyc (X Y Z : Pt) : S X Y Z = S Y Z X := by
  unfold S
  ring

theorem S_swap (X Y Z : Pt) : S X Z Y = -S X Y Z := by
  unfold S
  ring

theorem S_dissect (O X Y Z : Pt) : S O Y Z + S O Z X + S O X Y = S X Y Z := by
  unfold S
  ring

theorem S_smul_vadd (X Y Z : Pt) (s t : ℝ) :
    S X (s • (Y - X) + X) (t • (Z - X) + X) = s * t * S X Y Z := by
  unfold S
  simp only [PiLp.smul_apply, PiLp.add_apply, PiLp.sub_apply, smul_eq_mul]
  ring

theorem det_smul {u v : Pt} (hv : v ≠ 0) (h : u 0 * v 1 = u 1 * v 0) :
    ∃ t : ℝ, u = t • v := by
  have hv' : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hv (Pt_ext (by simpa using hc.1) (by simpa using hc.2))
  rcases hv' with h0 | h1
  · refine ⟨u 0 / v 0, Pt_ext ?_ ?_⟩
    · rw [PiLp.smul_apply, smul_eq_mul]
      field_simp
    · rw [PiLp.smul_apply, smul_eq_mul]
      field_simp
      linarith
  · refine ⟨u 1 / v 1, Pt_ext ?_ ?_⟩
    · rw [PiLp.smul_apply, smul_eq_mul]
      field_simp
      linarith
    · rw [PiLp.smul_apply, smul_eq_mul]
      field_simp

theorem eq_smul_vadd_of_S_eq_zero {P X Y : Pt} (hXY : X ≠ Y) (h : S P X Y = 0) :
    ∃ s : ℝ, P = s • (Y - X) + X := by
  have hd : (P - X) 0 * (Y - X) 1 = (P - X) 1 * (Y - X) 0 := by
    simp only [PiLp.sub_apply]
    unfold S at h
    linear_combination -h
  obtain ⟨s, hs⟩ := det_smul (sub_ne_zero.mpr (Ne.symm hXY)) hd
  exact ⟨s, by rw [← hs, sub_add_cancel]⟩

theorem S_eq_zero_of_mem {X Y Z : Pt} (h : X ∈ line[ℝ, Y, Z]) : S X Y Z = 0 := by
  have hY : Y ∈ line[ℝ, Y, Z] := left_mem_affineSpan_pair ℝ Y Z
  have hvs : X -ᵥ Y ∈ vectorSpan ℝ ({Y, Z} : Set Pt) :=
    vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan h hY
  rw [vectorSpan_pair, Submodule.mem_span_singleton] at hvs
  obtain ⟨t, ht⟩ := hvs
  have hX : X = t • (Y - Z) + Y := by
    rw [← vsub_vadd X Y, ← ht, vadd_eq_add, vsub_eq_sub]
  unfold S
  rw [hX]
  simp only [PiLp.smul_apply, PiLp.add_apply, PiLp.sub_apply, smul_eq_mul]
  ring

theorem mem_of_S_eq_zero {X Y Z : Pt} (hYZ : Y ≠ Z) (h : S X Y Z = 0) :
    X ∈ line[ℝ, Y, Z] := by
  have hd : (X - Y) 0 * (Z - Y) 1 = (X - Y) 1 * (Z - Y) 0 := by
    simp only [PiLp.sub_apply]
    unfold S at h
    linear_combination -h
  obtain ⟨s, hs⟩ := det_smul (sub_ne_zero.mpr (Ne.symm hYZ)) hd
  have hX : X = AffineMap.lineMap Y Z s := by
    rw [AffineMap.lineMap_apply, vsub_eq_sub, ← hs, vadd_eq_add, sub_add_cancel]
  rw [hX]
  exact AffineMap.lineMap_mem_affineSpan_pair s Y Z

theorem collinear_iff_S_eq_zero {X Y Z : Pt} :
    Collinear ℝ ({X, Y, Z} : Set Pt) ↔ S X Y Z = 0 := by
  constructor
  · intro hc
    rw [collinear_iff_of_mem (Set.mem_insert X _)] at hc
    obtain ⟨v, hv⟩ := hc
    obtain ⟨r₁, hr₁⟩ := hv Y (by simp)
    obtain ⟨r₂, hr₂⟩ := hv Z (by simp)
    unfold S
    rw [hr₁, hr₂]
    simp only [vadd_eq_add, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
    ring
  · intro hS
    by_cases hXY : X = Y
    · rw [hXY]
      rw [Set.insert_eq_of_mem (Set.mem_insert Y {Z})]
      exact collinear_pair ℝ Y Z
    · have hYX : Y - X ≠ 0 := sub_ne_zero.mpr (Ne.symm hXY)
      have hd : (Z - X) 0 * (Y - X) 1 = (Z - X) 1 * (Y - X) 0 := by
        simp only [PiLp.sub_apply]
        unfold S at hS
        linear_combination -hS
      obtain ⟨t, ht⟩ := det_smul hYX hd
      rw [collinear_iff_of_mem (Set.mem_insert X _)]
      refine ⟨Y - X, fun p hp => ?_⟩
      rcases hp with rfl | rfl | rfl
      · exact ⟨0, by rw [zero_smul, zero_vadd]⟩
      · exact ⟨1, by rw [one_smul, vadd_eq_add, sub_add_cancel]⟩
      · exact ⟨t, by rw [← ht, vadd_eq_add, sub_add_cancel]⟩

theorem inner_pt (x y : Pt) : inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply, Real.inner_apply]

theorem dist_sq_pt (X Y : Pt) : dist X Y ^ 2 = (X 0 - Y 0) ^ 2 + (X 1 - Y 1) ^ 2 := by
  rw [dist_eq_norm, norm_eq_sqrt_real_inner, Real.sq_sqrt real_inner_self_nonneg, inner_pt]
  simp only [PiLp.sub_apply]
  ring

theorem dist_mul_eq_abs_S_of_orth {P Q Y Z : Pt} (hSQ : S Q Y Z = 0)
    (horth : inner ℝ (Z - Y) (P - Q) = 0) :
    dist P Q * dist Y Z = |S P Y Z| := by
  have horth' : (Z 0 - Y 0) * (P 0 - Q 0) + (Z 1 - Y 1) * (P 1 - Q 1) = 0 := by
    simp only [inner_pt, PiLp.sub_apply] at horth
    exact horth
  have hS : S P Y Z = (P 0 - Q 0) * (Y 1 - Z 1) - (P 1 - Q 1) * (Y 0 - Z 0) := by
    unfold S at hSQ ⊢
    linear_combination hSQ
  have hLag : ((P 0 - Q 0) * (Y 1 - Z 1) - (P 1 - Q 1) * (Y 0 - Z 0)) ^ 2 =
      ((P 0 - Q 0) ^ 2 + (P 1 - Q 1) ^ 2) * ((Y 0 - Z 0) ^ 2 + (Y 1 - Z 1) ^ 2) -
        ((P 0 - Q 0) * (Y 0 - Z 0) + (P 1 - Q 1) * (Y 1 - Z 1)) ^ 2 := by
    ring
  have hinner0 : (P 0 - Q 0) * (Y 0 - Z 0) + (P 1 - Q 1) * (Y 1 - Z 1) = 0 := by
    linear_combination -horth'
  apply (sq_eq_sq₀ (mul_nonneg dist_nonneg dist_nonneg) (abs_nonneg _)).mp
  rw [sq_abs, mul_pow, dist_sq_pt, dist_sq_pt, hS, hLag, hinner0]
  ring

theorem dist_orthProj_mul {P Y Z : Pt} (hYZ : Y ≠ Z) :
    dist P (orthogonalProjection line[ℝ, Y, Z] P) * dist Y Z = |S P Y Z| := by
  have _ := hYZ -- the statement holds (and is proved) also for `Y = Z`
  have hQmem : (orthogonalProjection line[ℝ, Y, Z] P : Pt) ∈ line[ℝ, Y, Z] :=
    orthogonalProjection_mem P
  have hdir : (Z -ᵥ Y : Pt) ∈ (line[ℝ, Y, Z]).direction :=
    AffineSubspace.vsub_mem_direction (right_mem_affineSpan_pair ℝ Y Z)
      (left_mem_affineSpan_pair ℝ Y Z)
  have horth := vsub_orthogonalProjection_mem_direction_orthogonal line[ℝ, Y, Z] P
  have hinner : inner ℝ (Z - Y) (P - (orthogonalProjection line[ℝ, Y, Z] P : Pt)) = 0 := by
    have h := Submodule.inner_right_of_mem_orthogonal hdir horth
    rwa [vsub_eq_sub, vsub_eq_sub] at h
  exact dist_mul_eq_abs_S_of_orth (S_eq_zero_of_mem hQmem) hinner

theorem sSameSide_S {X Y Z O : Pt} (hYZ : Y ≠ Z) (h : (line[ℝ, Y, Z]).SSameSide X O) :
    0 < S X Y Z * S O Y Z := by
  obtain ⟨p₁, hp₁, p₂, hp₂, hray⟩ := h.1
  have hXn : X ∉ line[ℝ, Y, Z] := h.2.1
  have hOn : O ∉ line[ℝ, Y, Z] := h.2.2
  have hform : ∀ (T p : Pt), p ∈ line[ℝ, Y, Z] →
      S T Y Z = (T 0 - p 0) * (Y 1 - Z 1) - (T 1 - p 1) * (Y 0 - Z 0) := by
    intro T p hp
    have hp0 : S p Y Z = 0 := S_eq_zero_of_mem hp
    unfold S at hp0 ⊢
    linear_combination hp0
  have hX0 : S X Y Z ≠ 0 := fun hc => hXn (mem_of_S_eq_zero hYZ hc)
  have hO0 : S O Y Z ≠ 0 := fun hc => hOn (mem_of_S_eq_zero hYZ hc)
  rcases hray with h1 | h2 | ⟨r₁, r₂, hr₁, hr₂, hray⟩
  · exfalso
    apply hXn
    rw [vsub_eq_zero_iff_eq] at h1
    rw [h1]
    exact hp₁
  · exfalso
    apply hOn
    rw [vsub_eq_zero_iff_eq] at h2
    rw [h2]
    exact hp₂
  · have e : r₁ * S X Y Z = r₂ * S O Y Z := by
      have hcongr := congrArg (fun w : Pt => w 0 * (Y 1 - Z 1) - w 1 * (Y 0 - Z 0)) hray
      simp only [PiLp.smul_apply, smul_eq_mul, vsub_eq_sub, PiLp.sub_apply] at hcongr
      rw [hform X p₁ hp₁, hform O p₂ hp₂]
      linear_combination hcongr
    have hr : 0 < r₂ / r₁ := div_pos hr₂ hr₁
    have hSx : S X Y Z = (r₂ / r₁) * S O Y Z := by
      rw [div_mul_eq_mul_div, eq_div_iff (ne_of_gt hr₁)]
      linear_combination e
    rw [hSx, mul_assoc]
    exact mul_pos hr (mul_self_pos.mpr hO0)

/-! ### Symmetries of the definitions -/

theorem Inscribed.cyc {X Y Z O : Pt} {r : ℝ} (h : Inscribed X Y Z O r) :
    Inscribed Y Z X O r :=
  ⟨h.pos, h.sameSideZX, h.sameSideXY, h.sameSideYZ, h.tangentZX, h.tangentXY, h.tangentYZ⟩

theorem Inscribed.swapYZ {X Y Z O : Pt} {r : ℝ} (h : Inscribed X Y Z O r) :
    Inscribed X Z Y O r := by
  have pc : ∀ u v : Pt, line[ℝ, u, v] = line[ℝ, v, u] := fun u v =>
    AffineSubspace.affineSpan_pair_comm
  refine ⟨h.pos, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pc Z Y]; exact h.sameSideYZ
  · rw [pc Y X]; exact h.sameSideXY
  · rw [pc X Z]; exact h.sameSideZX
  · simp only [pc Z Y]; exact h.tangentYZ
  · simp only [pc Y X]; exact h.tangentXY
  · simp only [pc X Z]; exact h.tangentZX

theorem TangentCut.swapYZ {X Y Z Y' Z' O : Pt} {r : ℝ} (h : TangentCut X Y Z Y' Z' O r) :
    TangentCut X Z Y Z' Y' O r := by
  have pc : ∀ u v : Pt, line[ℝ, u, v] = line[ℝ, v, u] := fun u v =>
    AffineSubspace.affineSpan_pair_comm
  refine ⟨h.memXZ, h.memXY, ?_, ?_, ?_⟩
  · rw [Set.pair_comm Z' Y', Set.pair_comm Z Y]; exact h.parallel
  · simp only [pc Z' Y']; exact h.tangent
  · rw [pc Z' Y', pc Z Y]; exact h.ne

/-! ### The inscribed circle and twice the signed area -/

/-- The three signed areas determined by an inscribed circle, in terms of the
radius and the side lengths. -/
theorem Inscribed.S_rel {X Y Z O : Pt} {r : ℝ} (hS : 0 < S X Y Z) (h : Inscribed X Y Z O r) :
    S O Y Z = r * dist Y Z ∧ S O Z X = r * dist Z X ∧ S O X Y = r * dist X Y := by
  have hne : S X Y Z ≠ 0 := hS.ne'
  have hYZ : Y ≠ Z := fun e => hne (by rw [e]; exact S_self X Z)
  have hZX : Z ≠ X := fun e => hne (by
    rw [e]
    have h1 := S_swap X Y X
    rw [S_self₂] at h1
    linarith [h1])
  have hXY : X ≠ Y := fun e => hne (by rw [e]; exact S_self₂ Y Z)
  have hp_of : ∀ {U V W : Pt}, S U V W = S X Y Z → 0 < S U V W * S O V W → 0 < S O V W := by
    intro U V W hUVW hpos
    rw [hUVW] at hpos
    exact pos_of_mul_pos_right hpos hS.le
  have hp1 : 0 < S O Y Z := hp_of rfl (sSameSide_S hYZ h.sameSideYZ)
  have hp2 : 0 < S O Z X := hp_of (S_cyc X Y Z).symm (sSameSide_S hZX h.sameSideZX)
  have hp3 : 0 < S O X Y :=
    hp_of ((S_cyc Y Z X).symm.trans (S_cyc X Y Z).symm) (sSameSide_S hXY h.sameSideXY)
  have hd1 := dist_orthProj_mul (P := O) (Y := Y) (Z := Z) hYZ
  rw [h.tangentYZ, abs_of_pos hp1] at hd1
  have hd2 := dist_orthProj_mul (P := O) (Y := Z) (Z := X) hZX
  rw [h.tangentZX, abs_of_pos hp2] at hd2
  have hd3 := dist_orthProj_mul (P := O) (Y := X) (Z := Y) hXY
  rw [h.tangentXY, abs_of_pos hp3] at hd3
  exact ⟨hd1.symm, hd2.symm, hd3.symm⟩

/-- Twice the area of a triangle equals the inradius times the perimeter. -/
theorem Inscribed.area_eq {X Y Z O : Pt} {r : ℝ} (hS : 0 < S X Y Z) (h : Inscribed X Y Z O r) :
    S X Y Z = r * (dist Y Z + dist Z X + dist X Y) := by
  obtain ⟨h1, h2, h3⟩ := h.S_rel hS
  have hd := S_dissect O X Y Z
  linarith

/-- The strict triangle inequality, from nondegeneracy. -/
theorem dist_lt_add_of_S_ne_zero {X Y Z : Pt} (hS : S X Y Z ≠ 0) :
    dist Y Z < dist Y X + dist X Z := by
  rw [dist_lt_dist_add_dist_iff]
  intro hw
  have hc := hw.collinear
  rw [Set.insert_comm Y X {Z}] at hc
  exact hS (collinear_iff_S_eq_zero.mp hc)

/-! ### The tangent cut at one vertex -/

/-- The inradius of the small triangle cut off at the vertex `X` by the
tangent line parallel to `Y Z`: it is `r * (b + c - a) / (a + b + c)`. -/
theorem radius_tangentCut {X Y Z Y' Z' O O' : Pt} {r r' : ℝ}
    (hS : 0 < S X Y Z) (hO : Inscribed X Y Z O r)
    (hc : TangentCut X Y Z Y' Z' O r) (hi : Inscribed X Y' Z' O' r') :
    r' * (dist Y Z + dist Z X + dist X Y) = r * (dist Z X + dist X Y - dist Y Z) := by
  have hne : S X Y Z ≠ 0 := hS.ne'
  have hYZ : Y ≠ Z := fun e => hne (by rw [e]; exact S_self X Z)
  have hZX : Z ≠ X := fun e => hne (by
    rw [e]
    have h1 := S_swap X Y X
    rw [S_self₂] at h1
    linarith [h1])
  have hXY : X ≠ Y := fun e => hne (by rw [e]; exact S_self₂ Y Z)
  have hXZ : X ≠ Z := Ne.symm hZX
  have ha_pos : 0 < dist Y Z := dist_pos.mpr hYZ
  have hP : 0 < dist Y Z + dist Z X + dist X Y := by
    have h2 := @dist_nonneg _ _ Z X
    have h3 := @dist_nonneg _ _ X Y
    linarith [ha_pos]
  have hP0 : dist Y Z + dist Z X + dist X Y ≠ 0 := hP.ne'
  -- incircle relations for the big triangle
  obtain ⟨hOYZ, hOZX, hOXY⟩ := hO.S_rel hS
  have harea := hO.area_eq hS
  -- commuted distances
  have hXZc : dist X Z = dist Z X := dist_comm _ _
  have hYXc : dist Y X = dist X Y := dist_comm _ _
  -- parametrization of the cut points
  obtain ⟨s₁, hs₁⟩ := eq_smul_vadd_of_S_eq_zero (P := Y') hXY (S_eq_zero_of_mem hc.memXY)
  obtain ⟨s₂, hs₂⟩ := eq_smul_vadd_of_S_eq_zero (P := Z') hXZ (S_eq_zero_of_mem hc.memXZ)
  -- the parallel condition
  have hmem : Z' -ᵥ Y' ∈ vectorSpan ℝ ({Y', Z'} : Set Pt) :=
    vsub_mem_vectorSpan ℝ (Set.mem_insert_of_mem Y' (Set.mem_singleton Z'))
      (Set.mem_insert Y' ({Z'} : Set Pt))
  rw [hc.parallel, vectorSpan_pair] at hmem
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hmem
  -- flip the sign so the direction is written as `u • (Z - Y)`
  have ht0vec : Z' - Y' = t • (Y - Z) := by
    rw [← vsub_eq_sub]; exact ht.symm
  obtain ⟨u, hu⟩ : ∃ u : ℝ, Z' - Y' = u • (Z - Y) :=
    ⟨-t, by rw [ht0vec, show (Y - Z : Pt) = -(Z - Y) from by abel, smul_neg, neg_smul]⟩
  have hZ'Y' : Z' - Y' = s₂ • (Z - X) - s₁ • (Y - X) := by
    rw [hs₁, hs₂]; abel
  have he : s₂ • (Z - X) - s₁ • (Y - X) = u • (Z - X) - u • (Y - X) := by
    have hZY : (Z - Y : Pt) = (Z - X) - (Y - X) := by abel
    rw [hZY, smul_sub] at hu
    exact hZ'Y'.symm.trans hu
  have hdet1 : (s₂ - u) * ((Z 0 - X 0) * (Y 1 - X 1) - (Z 1 - X 1) * (Y 0 - X 0)) = 0 := by
    have e := congrArg (fun w : Pt => w 0 * (Y 1 - X 1) - w 1 * (Y 0 - X 0)) he
    simp only [smul_pt, sub_pt] at e
    linear_combination e
  have hdet2 : (s₁ - u) * ((Y 0 - X 0) * (Z 1 - X 1) - (Y 1 - X 1) * (Z 0 - X 0)) = 0 := by
    have e := congrArg (fun w : Pt => w 0 * (Z 1 - X 1) - w 1 * (Z 0 - X 0)) he
    simp only [smul_pt, sub_pt] at e
    linear_combination -e
  have hD1 : (Z 0 - X 0) * (Y 1 - X 1) - (Z 1 - X 1) * (Y 0 - X 0) ≠ 0 := by
    have e : (Z 0 - X 0) * (Y 1 - X 1) - (Z 1 - X 1) * (Y 0 - X 0) = -S X Y Z := by
      unfold S; ring
    rw [e, ne_eq, neg_eq_zero]; exact hne
  have hD2 : (Y 0 - X 0) * (Z 1 - X 1) - (Y 1 - X 1) * (Z 0 - X 0) ≠ 0 := by
    have e : (Y 0 - X 0) * (Z 1 - X 1) - (Y 1 - X 1) * (Z 0 - X 0) = S X Y Z := by
      unfold S; ring
    rwa [e]
  have hs₂t : s₂ = u := by
    rcases mul_eq_zero.mp hdet1 with h | h
    · linarith
    · exact absurd h hD1
  have hs₁t : s₁ = u := by
    rcases mul_eq_zero.mp hdet2 with h | h
    · linarith
    · exact absurd h hD2
  rw [hs₁t] at hs₁
  rw [hs₂t] at hs₂
  -- the scaling factor is nonzero
  have hu0 : u ≠ 0 := by
    intro e0
    rw [e0, zero_smul] at hu
    have hZZ' : Z' = Y' := by
      rw [← sub_eq_zero]; exact hu
    rw [hZZ'] at hc
    have hp := hc.parallel
    rw [Set.insert_eq_of_mem (Set.mem_singleton _), vectorSpan_singleton, vectorSpan_pair] at hp
    have hZY0 : Y -ᵥ Z ≠ 0 := fun he2 => hYZ (vsub_eq_zero_iff_eq.mp he2)
    have hsp : (ℝ ∙ (Y -ᵥ Z) : Submodule ℝ Pt) ≠ ⊥ := by
      rwa [ne_eq, Submodule.span_singleton_eq_bot]
    exact hsp hp.symm
  -- twice the area of the small triangle
  have hSsmall : S X Y' Z' = u * u * S X Y Z := by
    rw [hs₁, hs₂, S_smul_vadd]
  have hSsmall_pos : 0 < S X Y' Z' := by
    rw [hSsmall]
    exact mul_pos (mul_self_pos.mpr hu0) hS
  -- the side lengths of the small triangle
  have hdYZ' : dist Y' Z' = |u| * dist Y Z := by
    have e : u • (Y - X) + X - (u • (Z - X) + X) = u • (Y - Z) := by
      rw [smul_sub u Y X, smul_sub u Z X, smul_sub u Y Z]; abel
    rw [hs₁, hs₂, dist_eq_norm, e, norm_smul, Real.norm_eq_abs, ← dist_eq_norm Y Z]
  have hdXY' : dist X Y' = |u| * dist X Y := by
    have e : X - (u • (Y - X) + X) = u • (X - Y) := by
      rw [smul_sub u Y X, smul_sub u X Y]; abel
    rw [hs₁, dist_eq_norm, e, norm_smul, Real.norm_eq_abs, ← dist_eq_norm X Y]
  have hdXZ' : dist X Z' = |u| * dist X Z := by
    have e : X - (u • (Z - X) + X) = u • (X - Z) := by
      rw [smul_sub u Z X, smul_sub u X Z]; abel
    rw [hs₂, dist_eq_norm, e, norm_smul, Real.norm_eq_abs, ← dist_eq_norm X Z]
  have hY'Z' : Y' ≠ Z' := by
    intro e
    rw [e, dist_self] at hdYZ'
    have hu0' : |u| = 0 := by
      rcases mul_eq_zero.mp hdYZ'.symm with h | h
      · exact h
      · exact absurd h ha_pos.ne'
    exact hu0 (abs_eq_zero.mp hu0')
  -- relations for the small inscribed circle
  have harea_small := hi.area_eq hSsmall_pos
  -- the tangency condition on the cut line
  have hcut : r * (|u| * dist Y Z) = |S O Y' Z'| := by
    have hd := dist_orthProj_mul (P := O) (Y := Y') (Z := Z') hY'Z'
    rw [hc.tangent, hdYZ'] at hd
    exact hd
  have hexp : S O Y' Z' = u * (u * S O Y Z + (1 - u) * (S O Y X + S O X Z)) := by
    rw [hs₁, hs₂]
    simp only [S, smul_pt, add_pt, sub_pt]
    ring
  have hfactor : S O Y' Z' = u * r * (u * dist Y Z - (1 - u) * (dist Z X + dist X Y)) := by
    rw [hexp, hOYZ, S_swap O X Y, hOXY, S_swap O Z X, hOZX]
    ring
  have hE : |u * dist Y Z - (1 - u) * (dist Z X + dist X Y)| = dist Y Z := by
    have h3 : |u * r * (u * dist Y Z - (1 - u) * (dist Z X + dist X Y))| =
        |u| * r * |u * dist Y Z - (1 - u) * (dist Z X + dist X Y)| := by
      rw [abs_mul, abs_mul, abs_of_pos hO.pos]
    rw [← hfactor, ← hcut] at h3
    have h2 : r * |u| * dist Y Z =
        r * |u| * |u * dist Y Z - (1 - u) * (dist Z X + dist X Y)| := by
      linear_combination h3
    have h0 : (0:ℝ) < r * |u| := mul_pos hO.pos (abs_pos.mpr hu0)
    exact mul_left_cancel₀ h0.ne' h2.symm
  rcases eq_or_eq_neg_of_abs_eq hE with hcase | hcase
  · -- `u = 1`, i.e. the cut is the side `Y Z` itself; excluded.
    have hu1 : u = 1 := by
      have e : (u - 1) * (dist Y Z + dist Z X + dist X Y) = 0 := by linear_combination hcase
      rcases mul_eq_zero.mp e with h | h
      · linarith
      · exact absurd h hP0
    rw [hu1, one_smul] at hs₁ hs₂
    have hYY : Y' = Y := by rw [hs₁]; abel
    have hZZ : Z' = Z := by rw [hs₂]; abel
    rw [hYY, hZZ] at hc
    exact (hc.ne rfl).elim
  · -- the genuine tangent: `u = (b + c - a) / (a + b + c)`
    have huP : u * (dist Y Z + dist Z X + dist X Y) = dist Z X + dist X Y - dist Y Z := by
      linear_combination hcase
    have hbc : 0 < dist Z X + dist X Y - dist Y Z := by
      have htr := dist_lt_add_of_S_ne_zero (X := X) (Y := Y) (Z := Z) hne
      rw [hYXc, hXZc] at htr
      linarith [htr]
    have hupos : 0 < u := by
      have e : u = (dist Z X + dist X Y - dist Y Z) / (dist Y Z + dist Z X + dist X Y) :=
        (eq_div_iff hP0).mpr huP
      rw [e]
      exact div_pos hbc hP
    rw [hSsmall, harea, hdYZ', dist_comm Z' X, hdXZ', hXZc, hdXY', abs_of_pos hupos] at harea_small
    have hr' : r' = u * r := by
      have hu0r : (0:ℝ) < u * (dist Y Z + dist Z X + dist X Y) := mul_pos hupos hP
      have e : r' * (u * (dist Y Z + dist Z X + dist X Y)) =
          u * r * (u * (dist Y Z + dist Z X + dist X Y)) := by
        linear_combination -harea_small
      exact mul_right_cancel₀ hu0r.ne' e
    rw [hr']
    linear_combination r * huP

/-! ### Heron's formula -/

theorem heron_S (X Y Z : Pt) :
    4 * S X Y Z ^ 2 =
      2 * (dist Y Z ^ 2 * dist Z X ^ 2 + dist Z X ^ 2 * dist X Y ^ 2 + dist X Y ^ 2 * dist Y Z ^ 2) -
        (dist Y Z ^ 4 + dist Z X ^ 4 + dist X Y ^ 4) := by
  have d1 : dist Y Z ^ 4 = (dist Y Z ^ 2) ^ 2 := by ring
  have d2 : dist Z X ^ 4 = (dist Z X ^ 2) ^ 2 := by ring
  have d3 : dist X Y ^ 4 = (dist X Y ^ 2) ^ 2 := by ring
  rw [d1, d2, d3, dist_sq_pt, dist_sq_pt, dist_sq_pt]
  simp only [S]
  ring

/-! ### The main computation -/

theorem main_aux {A B C O O₁ O₂ O₃ B₁ C₁ C₂ A₂ A₃ B₃ : Pt} {r r₁ r₂ r₃ : ℝ}
    (hS : 0 < S A B C) (hO : Inscribed A B C O r)
    (h₁ : TangentCut A B C B₁ C₁ O r) (hi₁ : Inscribed A B₁ C₁ O₁ r₁)
    (h₂ : TangentCut B C A C₂ A₂ O r) (hi₂ : Inscribed B C₂ A₂ O₂ r₂)
    (h₃ : TangentCut C A B A₃ B₃ O r) (hi₃ : Inscribed C A₃ B₃ O₃ r₃) :
    Real.pi * (r ^ 2 + r₁ ^ 2 + r₂ ^ 2 + r₃ ^ 2) =
      answer (dist B C) (dist A C) (dist A B) := by
  have hSBC : 0 < S B C A := by
    rw [← S_cyc A B C]; exact hS
  have hSCA : 0 < S C A B := by
    rw [← S_cyc B C A, ← S_cyc A B C]; exact hS
  have hCA : dist C A = dist A C := dist_comm _ _
  have e₁ := radius_tangentCut hS hO h₁ hi₁
  rw [hCA] at e₁
  have e₂ := radius_tangentCut hSBC hO.cyc h₂ hi₂
  rw [hCA] at e₂
  have e₃ := radius_tangentCut hSCA hO.cyc.cyc h₃ hi₃
  rw [hCA] at e₃
  have harea := hO.area_eq hS
  rw [hCA] at harea
  set a := dist B C with had
  set b := dist A C with hbd
  set c := dist A B with hcd
  have hBneC : B ≠ C := fun e => (ne_of_gt hS) (by rw [e]; exact S_self A C)
  have hP : (0:ℝ) < a + b + c := by
    have h1 : (0:ℝ) < a := by rw [had]; exact dist_pos.mpr hBneC
    have h2 : (0:ℝ) ≤ b := by rw [hbd]; exact dist_nonneg
    have h3 : (0:ℝ) ≤ c := by rw [hcd]; exact dist_nonneg
    linarith
  have hP0 : a + b + c ≠ 0 := hP.ne'
  have hr₁ : r₁ = r * (b + c - a) / (a + b + c) := (eq_div_iff hP0).mpr e₁
  have hr₂ : r₂ = r * (c + a - b) / (a + b + c) := (eq_div_iff hP0).mpr (by linear_combination e₂)
  have hr₃ : r₃ = r * (a + b - c) / (a + b + c) := (eq_div_iff hP0).mpr (by linear_combination e₃)
  have hheron : 4 * S A B C ^ 2 = (a + b + c) * (b + c - a) * (c + a - b) * (a + b - c) := by
    have h2 : (a + b + c) * (b + c - a) * (c + a - b) * (a + b - c) =
        2 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) - (a ^ 4 + b ^ 4 + c ^ 4) := by ring
    rw [h2]
    have h3 := heron_S A B C
    rw [dist_comm C A, ← had, ← hbd, ← hcd] at h3
    exact h3
  have h4 : 4 * r ^ 2 = (b + c - a) * (c + a - b) * (a + b - c) / (a + b + c) := by
    rw [eq_div_iff hP0]
    have e : 4 * (r * (a + b + c)) ^ 2 =
        (a + b + c) * ((b + c - a) * (c + a - b) * (a + b - c)) := by
      rw [← harea]
      linear_combination hheron
    have e3 : (a + b + c) * (4 * r ^ 2 * (a + b + c)) =
        (a + b + c) * ((b + c - a) * (c + a - b) * (a + b - c)) := by
      linear_combination e
    exact mul_left_cancel₀ hP0 e3
  calc Real.pi * (r ^ 2 + r₁ ^ 2 + r₂ ^ 2 + r₃ ^ 2)
      = Real.pi * r ^ 2 * ((a + b + c) ^ 2 + (b + c - a) ^ 2 + (c + a - b) ^ 2 + (a + b - c) ^ 2)
          / (a + b + c) ^ 2 := by
        rw [hr₁, hr₂, hr₃]
        field_simp [hP0]
    _ = Real.pi * r ^ 2 * (4 * (a ^ 2 + b ^ 2 + c ^ 2)) / (a + b + c) ^ 2 := by
        rw [show (a + b + c) ^ 2 + (b + c - a) ^ 2 + (c + a - b) ^ 2 + (a + b - c) ^ 2 =
          4 * (a ^ 2 + b ^ 2 + c ^ 2) by ring]
    _ = Real.pi * (a ^ 2 + b ^ 2 + c ^ 2) * (4 * r ^ 2) / (a + b + c) ^ 2 := by ring
    _ = Real.pi * (a ^ 2 + b ^ 2 + c ^ 2) *
          ((b + c - a) * (c + a - b) * (a + b - c) / (a + b + c)) / (a + b + c) ^ 2 := by
        rw [h4]
    _ = answer a b c := by
        unfold answer
        field_simp [hP0]

snip end

problem imo_1964_p3
    (A B C : Pt) (hABC : ¬ Collinear ℝ ({A, B, C} : Set Pt))
    (O : Pt) (r : ℝ) (hO : Inscribed A B C O r)
    (B₁ C₁ O₁ : Pt) (r₁ : ℝ) (h₁ : TangentCut A B C B₁ C₁ O r) (hi₁ : Inscribed A B₁ C₁ O₁ r₁)
    (C₂ A₂ O₂ : Pt) (r₂ : ℝ) (h₂ : TangentCut B C A C₂ A₂ O r) (hi₂ : Inscribed B C₂ A₂ O₂ r₂)
    (A₃ B₃ O₃ : Pt) (r₃ : ℝ) (h₃ : TangentCut C A B A₃ B₃ O r) (hi₃ : Inscribed C A₃ B₃ O₃ r₃) :
    Real.pi * (r ^ 2 + r₁ ^ 2 + r₂ ^ 2 + r₃ ^ 2) =
      answer (dist B C) (dist A C) (dist A B) := by
  have hne : S A B C ≠ 0 := fun e => hABC (collinear_iff_S_eq_zero.mpr e)
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hS' : (0:ℝ) < S A C B := by
      have e : S A C B = -S A B C := S_swap A B C
      rw [e]; linarith [hneg]
    have hr2 := main_aux hS' hO.swapYZ h₁.swapYZ hi₁.swapYZ h₃.swapYZ hi₃.swapYZ h₂.swapYZ hi₂.swapYZ
    rw [dist_comm C B] at hr2
    have hans : answer (dist B C) (dist A B) (dist A C) =
        answer (dist B C) (dist A C) (dist A B) := by
      unfold answer; ring
    rw [hans] at hr2
    linear_combination hr2
  · exact main_aux hpos hO h₁ hi₁ h₂ hi₂ h₃ hi₃

end Imo1964P3
