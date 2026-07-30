/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics, .Geometry] }

/-!
# International Mathematical Olympiad 1983, Problem 4

Let ABC be an equilateral triangle and E the set of all points contained in the
three segments AB, BC and CA (including A, B and C). Determine whether, for every
partition of E into two disjoint subsets, at least one of the two subsets contains
the vertices of a right-angled triangle.

# Answer

Yes: at least one of the two subsets always contains the vertices of a
right-angled triangle.

# Formalization note

All equilateral triangles in the plane are similar, and the property in question
is invariant under similarities, so we may and do assume that the triangle is the
specific equilateral triangle with vertices
A = (1/2, √3/2), B = (0, 0), C = (1, 0).
-/

namespace Imo1983P4

open scoped RealInnerProductSpace

/-- Points of the Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- Vertex of the standard equilateral triangle. -/
noncomputable def A : Pt := !₂[1/2, √3/2]

/-- Vertex of the standard equilateral triangle. -/
noncomputable def B : Pt := !₂[0, 0]

/-- Vertex of the standard equilateral triangle. -/
noncomputable def C : Pt := !₂[1, 0]

/-- The set `E`: the boundary of the triangle `ABC`. -/
def E : Set Pt := segment ℝ A B ∪ segment ℝ B C ∪ segment ℝ C A

/-- `RightAngle p q r` says that the triangle with vertices `p`, `q`, `r`
has a right angle at `q`. -/
def RightAngle (p q r : Pt) : Prop := p ≠ q ∧ r ≠ q ∧ ⟪p - q, r - q⟫ = 0

determine answer : Prop :=
  ∀ S T : Set Pt, S ∪ T = E ∧ S ∩ T = ∅ →
    (∃ p ∈ S, ∃ q ∈ S, ∃ r ∈ S, RightAngle p q r) ∨
    (∃ p ∈ T, ∃ q ∈ T, ∃ r ∈ T, RightAngle p q r)

snip begin

/-- Extensionality for points of the plane. -/
theorem Pt.ext {x y : Pt} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  apply WithLp.ofLp_injective (p := 2)
  funext i
  fin_cases i <;> assumption

/-- The inner product in coordinates. -/
theorem inner_pt (u v : Pt) : ⟪u, v⟫ = u 0 * v 0 + u 1 * v 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, RCLike.inner_apply]
  simp only [conj_trivial]
  ring

/-- `X`, `Y`, `Z` lie two-thirds of the way along `BC`, `CA`, `AB` respectively. -/
noncomputable def X : Pt := !₂[2/3, 0]

/-- See `X`. -/
noncomputable def Y : Pt := !₂[2/3, √3/3]

/-- See `X`. -/
noncomputable def Z : Pt := !₂[1/6, √3/6]

/-- `W` is the foot of the perpendicular from `Z` to `BC`. -/
noncomputable def W : Pt := !₂[1/6, 0]

/-- `M` is the midpoint of `BC`. -/
noncomputable def M : Pt := !₂[1/2, 0]

/-- `W'` is the foot of the perpendicular from `X` to `CA`. -/
noncomputable def W' : Pt := !₂[11/12, √3/12]

/-- `M'` is the midpoint of `CA`. -/
noncomputable def M' : Pt := !₂[3/4, √3/4]

/-- `W''` is the foot of the perpendicular from `Y` to `AB`. -/
noncomputable def W'' : Pt := !₂[5/12, 5 * √3/12]

/-- `M''` is the midpoint of `AB`. -/
noncomputable def M'' : Pt := !₂[1/4, √3/4]

/-! ### Coordinates of the distinguished points -/

theorem A0 : A 0 = 1/2 := rfl
theorem A1 : A 1 = √3/2 := rfl
theorem B0 : B 0 = 0 := rfl
theorem B1 : B 1 = 0 := rfl
theorem C0 : C 0 = 1 := rfl
theorem C1 : C 1 = 0 := rfl
theorem X0 : X 0 = 2/3 := rfl
theorem X1 : X 1 = 0 := rfl
theorem Y0 : Y 0 = 2/3 := rfl
theorem Y1 : Y 1 = √3/3 := rfl
theorem Z0 : Z 0 = 1/6 := rfl
theorem Z1 : Z 1 = √3/6 := rfl
theorem W0 : W 0 = 1/6 := rfl
theorem W1 : W 1 = 0 := rfl
theorem M0 : M 0 = 1/2 := rfl
theorem M1 : M 1 = 0 := rfl
theorem W'0 : W' 0 = 11/12 := rfl
theorem W'1 : W' 1 = √3/12 := rfl
theorem M'0 : M' 0 = 3/4 := rfl
theorem M'1 : M' 1 = √3/4 := rfl
theorem W''0 : W'' 0 = 5/12 := rfl
theorem W''1 : W'' 1 = 5 * √3/12 := rfl
theorem M''0 : M'' 0 = 1/4 := rfl
theorem M''1 : M'' 1 = √3/4 := rfl

/-! ### Distinctness of the distinguished points -/

theorem Y_ne_X : Y ≠ X :=
  ne_of_apply_ne (· 1) (by simp only [Y1, X1]; positivity)
theorem Z_ne_W : Z ≠ W :=
  ne_of_apply_ne (· 1) (by simp only [Z1, W1]; positivity)
theorem A_ne_M : A ≠ M :=
  ne_of_apply_ne (· 1) (by simp only [A1, M1]; positivity)
theorem B_ne_X : B ≠ X := ne_of_apply_ne (· 0) (by norm_num [B0, X0])
theorem W_ne_X : W ≠ X := ne_of_apply_ne (· 0) (by norm_num [W0, X0])
theorem M_ne_X : M ≠ X := ne_of_apply_ne (· 0) (by norm_num [M0, X0])
theorem C_ne_X : C ≠ X := ne_of_apply_ne (· 0) (by norm_num [C0, X0])
theorem B_ne_W : B ≠ W := ne_of_apply_ne (· 0) (by norm_num [B0, W0])
theorem Z_ne_Y : Z ≠ Y := ne_of_apply_ne (· 0) (by norm_num [Z0, Y0])
theorem A_ne_Y : A ≠ Y := ne_of_apply_ne (· 0) (by norm_num [A0, Y0])
theorem C_ne_Y : C ≠ Y := ne_of_apply_ne (· 0) (by norm_num [C0, Y0])
theorem W'_ne_Y : W' ≠ Y := ne_of_apply_ne (· 0) (by norm_num [W'0, Y0])
theorem M'_ne_Y : M' ≠ Y := ne_of_apply_ne (· 0) (by norm_num [M'0, Y0])
theorem X_ne_Z : X ≠ Z := ne_of_apply_ne (· 0) (by norm_num [X0, Z0])
theorem A_ne_Z : A ≠ Z := ne_of_apply_ne (· 0) (by norm_num [A0, Z0])
theorem B_ne_Z : B ≠ Z := ne_of_apply_ne (· 0) (by norm_num [B0, Z0])
theorem W''_ne_Z : W'' ≠ Z := ne_of_apply_ne (· 0) (by norm_num [W''0, Z0])
theorem M''_ne_Z : M'' ≠ Z := ne_of_apply_ne (· 0) (by norm_num [M''0, Z0])
theorem C_ne_M : C ≠ M := ne_of_apply_ne (· 0) (by norm_num [C0, M0])
theorem X_ne_W' : X ≠ W' := ne_of_apply_ne (· 0) (by norm_num [X0, W'0])
theorem C_ne_W' : C ≠ W' := ne_of_apply_ne (· 0) (by norm_num [C0, W'0])
theorem B_ne_M' : B ≠ M' := ne_of_apply_ne (· 0) (by norm_num [B0, M'0])
theorem A_ne_M' : A ≠ M' := ne_of_apply_ne (· 0) (by norm_num [A0, M'0])
theorem Y_ne_W'' : Y ≠ W'' := ne_of_apply_ne (· 0) (by norm_num [Y0, W''0])
theorem A_ne_W'' : A ≠ W'' := ne_of_apply_ne (· 0) (by norm_num [A0, W''0])
theorem C_ne_M'' : C ≠ M'' := ne_of_apply_ne (· 0) (by norm_num [C0, M''0])
theorem A_ne_M'' : A ≠ M'' := ne_of_apply_ne (· 0) (by norm_num [A0, M''0])

/-! ### Membership in segments -/

/-- A convex combination of the endpoints lies in the segment. -/
theorem mem_segment_of_eq {u v p : Pt} (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (h : (1 - t) • u + t • v = p) : p ∈ segment ℝ u v := by
  rw [segment_eq_image]
  exact ⟨t, ⟨ht0, ht1⟩, h⟩

theorem X_mem_BC : X ∈ segment ℝ B C :=
  mem_segment_of_eq (2/3) (by norm_num) (by norm_num) <| by
    apply Pt.ext <;>
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, B0, B1, C0, C1, X0, X1]
      <;> ring

theorem Y_mem_CA : Y ∈ segment ℝ C A :=
  mem_segment_of_eq (2/3) (by norm_num) (by norm_num) <| by
    apply Pt.ext <;>
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, C0, C1, A0, A1, Y0, Y1]
      <;> ring

theorem Z_mem_AB : Z ∈ segment ℝ A B :=
  mem_segment_of_eq (2/3) (by norm_num) (by norm_num) <| by
    apply Pt.ext <;>
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, A0, A1, B0, B1, Z0, Z1]
      <;> ring

theorem W_mem_BC : W ∈ segment ℝ B C :=
  mem_segment_of_eq (1/6) (by norm_num) (by norm_num) <| by
    apply Pt.ext <;>
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, B0, B1, C0, C1, W0, W1]
      <;> ring

theorem M_mem_BC : M ∈ segment ℝ B C :=
  mem_segment_of_eq (1/2) (by norm_num) (by norm_num) <| by
    apply Pt.ext <;>
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, B0, B1, C0, C1, M0, M1]
      <;> ring

theorem W'_mem_CA : W' ∈ segment ℝ C A :=
  mem_segment_of_eq (1/6) (by norm_num) (by norm_num) <| by
    apply Pt.ext <;>
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, C0, C1, A0, A1, W'0, W'1]
      <;> ring

theorem M'_mem_CA : M' ∈ segment ℝ C A :=
  mem_segment_of_eq (1/2) (by norm_num) (by norm_num) <| by
    apply Pt.ext <;>
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, C0, C1, A0, A1, M'0, M'1]
      <;> ring

theorem W''_mem_AB : W'' ∈ segment ℝ A B :=
  mem_segment_of_eq (1/6) (by norm_num) (by norm_num) <| by
    apply Pt.ext <;>
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, A0, A1, B0, B1, W''0, W''1]
      <;> ring

theorem M''_mem_AB : M'' ∈ segment ℝ A B :=
  mem_segment_of_eq (1/2) (by norm_num) (by norm_num) <| by
    apply Pt.ext <;>
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, A0, A1, B0, B1, M''0, M''1]
      <;> ring

/-! ### Equations of the sides of the triangle -/

theorem lineBC {p : Pt} (hp : p ∈ segment ℝ B C) : p 1 = 0 := by
  rw [segment_eq_image] at hp
  obtain ⟨t, -, rfl⟩ := hp
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, B1, C1]
  ring

theorem lineCA {p : Pt} (hp : p ∈ segment ℝ C A) : p 0 + (√3/3) * p 1 = 1 := by
  rw [segment_eq_image] at hp
  obtain ⟨t, -, rfl⟩ := hp
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, C0, C1, A0, A1]
  linear_combination (t / 6) * h3

theorem lineAB {p : Pt} (hp : p ∈ segment ℝ A B) : p 1 = √3 * p 0 := by
  rw [segment_eq_image] at hp
  obtain ⟨t, -, rfl⟩ := hp
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, A0, A1, B0, B1]
  ring

/-! ### Right angles -/

/-- `YX` is perpendicular to `BC`. -/
theorem RA_YX_of_mem_BC {p : Pt} (hp : p ∈ segment ℝ B C) (hpX : p ≠ X) :
    RightAngle Y X p := by
  refine ⟨Y_ne_X, hpX, ?_⟩
  rw [inner_pt]
  simp only [PiLp.sub_apply, Y0, Y1, X0, X1]
  rw [lineBC hp]
  ring

/-- `ZW` is perpendicular to `WB`. -/
theorem RA_ZWB : RightAngle Z W B := by
  refine ⟨Z_ne_W, B_ne_W, ?_⟩
  rw [inner_pt]
  simp only [PiLp.sub_apply, Z0, Z1, W0, W1, B0, B1]
  ring

/-- `ZY` is perpendicular to `CA`. -/
theorem RA_ZY_of_mem_CA {p : Pt} (hp : p ∈ segment ℝ C A) (hpY : p ≠ Y) :
    RightAngle Z Y p := by
  refine ⟨Z_ne_Y, hpY, ?_⟩
  have hl := lineCA hp
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [inner_pt]
  simp only [PiLp.sub_apply, Z0, Z1, Y0, Y1]
  linarith only [hl, h3]

/-- `AM` is perpendicular to `MC`. -/
theorem RA_AMC : RightAngle A M C := by
  refine ⟨A_ne_M, C_ne_M, ?_⟩
  rw [inner_pt]
  simp only [PiLp.sub_apply, A0, A1, M0, M1, C0, C1]
  ring

/-- `XW'` is perpendicular to `W'C`. -/
theorem RA_XW'C : RightAngle X W' C := by
  refine ⟨X_ne_W', C_ne_W', ?_⟩
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [inner_pt]
  simp only [PiLp.sub_apply, X0, X1, W'0, W'1, C0, C1]
  linarith only [h3]

/-- `XZ` is perpendicular to `AB`. -/
theorem RA_XZ_of_mem_AB {p : Pt} (hp : p ∈ segment ℝ A B) (hpZ : p ≠ Z) :
    RightAngle X Z p := by
  refine ⟨X_ne_Z, hpZ, ?_⟩
  have hl := lineAB hp
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3l : √3 * p 1 = 3 * p 0 := by
    rw [hl, ← mul_assoc, Real.mul_self_sqrt (by norm_num)]
  rw [inner_pt]
  simp only [PiLp.sub_apply, X0, X1, Z0, Z1]
  linarith only [h3l, h3]

/-- `BM'` is perpendicular to `M'A`. -/
theorem RA_BM'A : RightAngle B M' A := by
  refine ⟨B_ne_M', A_ne_M', ?_⟩
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [inner_pt]
  simp only [PiLp.sub_apply, B0, B1, M'0, M'1, A0, A1]
  linarith only [h3]

/-- `YW''` is perpendicular to `W''A`. -/
theorem RA_YW''A : RightAngle Y W'' A := by
  refine ⟨Y_ne_W'', A_ne_W'', ?_⟩
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [inner_pt]
  simp only [PiLp.sub_apply, Y0, Y1, W''0, W''1, A0, A1]
  linarith only [h3]

/-- `CM''` is perpendicular to `M''A`. -/
theorem RA_CM''A : RightAngle C M'' A := by
  refine ⟨C_ne_M'', A_ne_M'', ?_⟩
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [inner_pt]
  simp only [PiLp.sub_apply, C0, C1, M''0, M''1, A0, A1]
  linarith only [h3]

/-! ### The sides are contained in `E` -/

theorem segAB_subset_E : segment ℝ A B ⊆ E :=
  Set.Subset.trans Set.subset_union_left Set.subset_union_left

theorem segBC_subset_E : segment ℝ B C ⊆ E :=
  Set.Subset.trans Set.subset_union_right Set.subset_union_left

theorem segCA_subset_E : segment ℝ C A ⊆ E := Set.subset_union_right

theorem A_mem_E : A ∈ E := segCA_subset_E (right_mem_segment ℝ C A)
theorem B_mem_E : B ∈ E := segBC_subset_E (left_mem_segment ℝ B C)
theorem C_mem_E : C ∈ E := segBC_subset_E (right_mem_segment ℝ B C)
theorem X_mem_E : X ∈ E := segBC_subset_E X_mem_BC
theorem Y_mem_E : Y ∈ E := segCA_subset_E Y_mem_CA
theorem Z_mem_E : Z ∈ E := segAB_subset_E Z_mem_AB
theorem W_mem_E : W ∈ E := segBC_subset_E W_mem_BC
theorem M_mem_E : M ∈ E := segBC_subset_E M_mem_BC
theorem W'_mem_E : W' ∈ E := segCA_subset_E W'_mem_CA
theorem M'_mem_E : M' ∈ E := segCA_subset_E M'_mem_CA
theorem W''_mem_E : W'' ∈ E := segAB_subset_E W''_mem_AB
theorem M''_mem_E : M'' ∈ E := segAB_subset_E M''_mem_AB

/-! ### The three cases of the pigeonhole principle -/

/-- Case `X, Y ∈ S`. Following kalva's solution: every point of `BC` other than
`X` must lie in `T`; hence so do `B`, `W`, `C`, and `Z` would close a right
triangle in `T`, so `Z ∈ S`; then every point of `CA` other than `Y` lies in
`T`; but then `A`, `M`, `C` are all in `T` and form a right triangle. -/
theorem case_XY {S T : Set Pt} (hSU : S ∪ T = E) (hX : X ∈ S) (hY : Y ∈ S) :
    (∃ p ∈ S, ∃ q ∈ S, ∃ r ∈ S, RightAngle p q r) ∨
    (∃ p ∈ T, ∃ q ∈ T, ∃ r ∈ T, RightAngle p q r) := by
  have hE : ∀ p ∈ E, p ∈ S ∨ p ∈ T := by
    intro p hp
    rw [← hSU] at hp
    exact (Set.mem_union _ _ _).mp hp
  by_cases hB : B ∈ S
  · exact Or.inl ⟨Y, hY, X, hX, B, hB, RA_YX_of_mem_BC (left_mem_segment ℝ B C) B_ne_X⟩
  · have hB := (hE B B_mem_E).resolve_left hB
    by_cases hW : W ∈ S
    · exact Or.inl ⟨Y, hY, X, hX, W, hW, RA_YX_of_mem_BC W_mem_BC W_ne_X⟩
    · have hW := (hE W W_mem_E).resolve_left hW
      by_cases hM : M ∈ S
      · exact Or.inl ⟨Y, hY, X, hX, M, hM, RA_YX_of_mem_BC M_mem_BC M_ne_X⟩
      · have hM := (hE M M_mem_E).resolve_left hM
        by_cases hC : C ∈ S
        · exact Or.inl ⟨Y, hY, X, hX, C, hC,
            RA_YX_of_mem_BC (right_mem_segment ℝ B C) C_ne_X⟩
        · have hC := (hE C C_mem_E).resolve_left hC
          by_cases hZ : Z ∈ T
          · exact Or.inr ⟨Z, hZ, W, hW, B, hB, RA_ZWB⟩
          · have hZ := (hE Z Z_mem_E).resolve_right hZ
            by_cases hA : A ∈ S
            · exact Or.inl ⟨Z, hZ, Y, hY, A, hA,
                RA_ZY_of_mem_CA (right_mem_segment ℝ C A) A_ne_Y⟩
            · have hA := (hE A A_mem_E).resolve_left hA
              exact Or.inr ⟨A, hA, M, hM, C, hC, RA_AMC⟩

/-- Case `Y, Z ∈ S` (the rotation of `case_XY`). -/
theorem case_YZ {S T : Set Pt} (hSU : S ∪ T = E) (hY : Y ∈ S) (hZ : Z ∈ S) :
    (∃ p ∈ S, ∃ q ∈ S, ∃ r ∈ S, RightAngle p q r) ∨
    (∃ p ∈ T, ∃ q ∈ T, ∃ r ∈ T, RightAngle p q r) := by
  have hE : ∀ p ∈ E, p ∈ S ∨ p ∈ T := by
    intro p hp
    rw [← hSU] at hp
    exact (Set.mem_union _ _ _).mp hp
  by_cases hC : C ∈ S
  · exact Or.inl ⟨Z, hZ, Y, hY, C, hC, RA_ZY_of_mem_CA (left_mem_segment ℝ C A) C_ne_Y⟩
  · have hC := (hE C C_mem_E).resolve_left hC
    by_cases hA : A ∈ S
    · exact Or.inl ⟨Z, hZ, Y, hY, A, hA, RA_ZY_of_mem_CA (right_mem_segment ℝ C A) A_ne_Y⟩
    · have hA := (hE A A_mem_E).resolve_left hA
      by_cases hW' : W' ∈ S
      · exact Or.inl ⟨Z, hZ, Y, hY, W', hW', RA_ZY_of_mem_CA W'_mem_CA W'_ne_Y⟩
      · have hW' := (hE W' W'_mem_E).resolve_left hW'
        by_cases hM' : M' ∈ S
        · exact Or.inl ⟨Z, hZ, Y, hY, M', hM', RA_ZY_of_mem_CA M'_mem_CA M'_ne_Y⟩
        · have hM' := (hE M' M'_mem_E).resolve_left hM'
          by_cases hX : X ∈ T
          · exact Or.inr ⟨X, hX, W', hW', C, hC, RA_XW'C⟩
          · have hX := (hE X X_mem_E).resolve_right hX
            by_cases hB : B ∈ S
            · exact Or.inl ⟨X, hX, Z, hZ, B, hB,
                RA_XZ_of_mem_AB (right_mem_segment ℝ A B) B_ne_Z⟩
            · have hB := (hE B B_mem_E).resolve_left hB
              exact Or.inr ⟨B, hB, M', hM', A, hA, RA_BM'A⟩

/-- Case `X, Z ∈ S` (the other rotation of `case_XY`). -/
theorem case_XZ {S T : Set Pt} (hSU : S ∪ T = E) (hX : X ∈ S) (hZ : Z ∈ S) :
    (∃ p ∈ S, ∃ q ∈ S, ∃ r ∈ S, RightAngle p q r) ∨
    (∃ p ∈ T, ∃ q ∈ T, ∃ r ∈ T, RightAngle p q r) := by
  have hE : ∀ p ∈ E, p ∈ S ∨ p ∈ T := by
    intro p hp
    rw [← hSU] at hp
    exact (Set.mem_union _ _ _).mp hp
  by_cases hA : A ∈ S
  · exact Or.inl ⟨X, hX, Z, hZ, A, hA, RA_XZ_of_mem_AB (left_mem_segment ℝ A B) A_ne_Z⟩
  · have hA := (hE A A_mem_E).resolve_left hA
    by_cases hB : B ∈ S
    · exact Or.inl ⟨X, hX, Z, hZ, B, hB, RA_XZ_of_mem_AB (right_mem_segment ℝ A B) B_ne_Z⟩
    · have hB := (hE B B_mem_E).resolve_left hB
      by_cases hW'' : W'' ∈ S
      · exact Or.inl ⟨X, hX, Z, hZ, W'', hW'', RA_XZ_of_mem_AB W''_mem_AB W''_ne_Z⟩
      · have hW'' := (hE W'' W''_mem_E).resolve_left hW''
        by_cases hM'' : M'' ∈ S
        · exact Or.inl ⟨X, hX, Z, hZ, M'', hM'', RA_XZ_of_mem_AB M''_mem_AB M''_ne_Z⟩
        · have hM'' := (hE M'' M''_mem_E).resolve_left hM''
          by_cases hY : Y ∈ T
          · exact Or.inr ⟨Y, hY, W'', hW'', A, hA, RA_YW''A⟩
          · have hY := (hE Y Y_mem_E).resolve_right hY
            by_cases hC : C ∈ S
            · exact Or.inl ⟨Y, hY, X, hX, C, hC,
                RA_YX_of_mem_BC (right_mem_segment ℝ B C) C_ne_X⟩
            · have hC := (hE C C_mem_E).resolve_left hC
              exact Or.inr ⟨C, hC, M'', hM'', A, hA, RA_CM''A⟩

snip end

problem imo1983_p4 : answer := by
  intro S T h
  obtain ⟨hSU, -⟩ := h
  have hE : ∀ p ∈ E, p ∈ S ∨ p ∈ T := by
    intro p hp
    rw [← hSU] at hp
    exact (Set.mem_union _ _ _).mp hp
  have hXE : X ∈ E := segBC_subset_E X_mem_BC
  have hYE : Y ∈ E := segCA_subset_E Y_mem_CA
  have hZE : Z ∈ E := segAB_subset_E Z_mem_AB
  rcases hE X hXE with hXS | hXT
  · rcases hE Y hYE with hYS | hYT
    · exact case_XY hSU hXS hYS
    · rcases hE Z hZE with hZS | hZT
      · exact case_XZ hSU hXS hZS
      · exact Or.symm (case_YZ (Set.union_comm _ _ ▸ hSU) hYT hZT)
  · rcases hE Y hYE with hYS | hYT
    · rcases hE Z hZE with hZS | hZT
      · exact case_YZ hSU hYS hZS
      · exact Or.symm (case_XZ (Set.union_comm _ _ ▸ hSU) hXT hZT)
    · rcases hE Z hZE with hZS | hZT
      · exact Or.symm (case_XY (Set.union_comm _ _ ▸ hSU) hXT hYT)
      · exact Or.symm (case_XY (Set.union_comm _ _ ▸ hSU) hXT hYT)

end Imo1983P4
