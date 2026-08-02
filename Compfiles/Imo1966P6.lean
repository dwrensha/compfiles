/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1966, Problem 6

In the interior of sides BC, CA, AB of triangle ABC, any points K, L, M,
respectively, are selected. Prove that the area of at least one of the
triangles AML, BKM, CLK is less than or equal to one quarter of the area of
the triangle ABC.
-/

namespace Imo1966P6

/-- The Euclidean plane, in which the problem takes place. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Twice the signed area of the triangle `PQR`, i.e. the determinant of the
vectors `Q - P` and `R - P`. -/
def twiceSignedArea (P Q R : Plane) : ℝ :=
  (Q 0 - P 0) * (R 1 - P 1) - (Q 1 - P 1) * (R 0 - P 0)

/-- The area of the triangle `PQR`. -/
noncomputable def triArea (P Q R : Plane) : ℝ := |twiceSignedArea P Q R| / 2

snip begin

/-!
## Proof sketch

Write `K = a₁ • B + a₂ • C`, `L = b₁ • C + b₂ • A`, `M = c₁ • A + c₂ • B` with
`a₁ + a₂ = b₁ + b₂ = c₁ + c₂ = 1` and all coefficients in `(0, 1)`.  The
ratios of the areas of the corner triangles `AML`, `BKM`, `CLK` to the area
of `ABC` are `c₂ * b₁`, `a₂ * c₁` and `b₂ * a₁` respectively.  Their product
equals `(a₁ * a₂) * (b₁ * b₂) * (c₁ * c₂) ≤ (1/4)³`, since
`x * (1 - x) ≤ 1 / 4`.  Hence at least one of the three ratios is at most
`1 / 4`.
-/

/-- Twice the signed area is invariant under cyclic permutations of the
vertices. -/
lemma twiceSignedArea_cycle (P Q R : Plane) :
    twiceSignedArea P Q R = twiceSignedArea Q R P := by
  unfold twiceSignedArea
  ring

/-- If twice the signed area of a triangle vanishes, then its vertices are
collinear. -/
lemma collinear_of_twiceSignedArea_eq_zero {P Q R : Plane}
    (h : twiceSignedArea P Q R = 0) : Collinear ℝ ({P, Q, R} : Set Plane) := by
  have hd : (Q 0 - P 0) * (R 1 - P 1) = (Q 1 - P 1) * (R 0 - P 0) := by
    unfold twiceSignedArea at h
    linarith
  rw [collinear_iff_of_mem (Set.mem_insert P _)]
  by_cases hQP : Q = P
  · -- Two vertices coincide: the points lie on the line through `P = Q` and `R`.
    refine ⟨R -ᵥ P, fun p hp => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with h | h | h
    · rw [h]
      exact ⟨0, by rw [zero_smul, zero_vadd]⟩
    · rw [h]
      exact ⟨0, by rw [zero_smul, zero_vadd]; exact hQP⟩
    · rw [h]
      exact ⟨1, by rw [one_smul, vsub_vadd]⟩
  · -- Some component of `Q - P` is nonzero, and `R - P` is a multiple of `Q - P`.
    have hex : ∃ i : Fin 2, Q i - P i ≠ 0 := by
      by_contra hn
      push Not at hn
      apply hQP
      ext i
      have hi := hn i
      rw [sub_eq_zero] at hi
      exact hi
    obtain ⟨i₀, hi₀⟩ := hex
    refine ⟨Q -ᵥ P, fun p hp => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with h | h | h
    · rw [h]
      exact ⟨0, by rw [zero_smul, zero_vadd]⟩
    · rw [h]
      exact ⟨1, by rw [one_smul, vsub_vadd]⟩
    · rw [h]
      -- The case of `R`: the determinant condition gives the ratio componentwise.
      have hRcomp : ∀ j : Fin 2,
          R j - P j = ((R i₀ - P i₀) / (Q i₀ - P i₀)) * (Q j - P j) := by
        intro j
        by_cases hji : j = i₀
        · subst hji
          rw [div_mul_cancel₀ _ hi₀]
        · rw [div_mul_eq_mul_div₀, eq_div_iff_mul_eq hi₀]
          have h2 : ∀ i : Fin 2, i = 0 ∨ i = 1 := fun i => by fin_cases i <;> simp
          rcases h2 i₀ with hi0 | hi0 <;> rcases h2 j with hj | hj
          · exact absurd (hj.trans hi0.symm) hji
          · rw [hj, hi0]; linarith [hd]
          · rw [hj, hi0]; linarith [hd]
          · exact absurd (hj.trans hi0.symm) hji
      exact ⟨(R i₀ - P i₀) / (Q i₀ - P i₀), by
        ext j
        simp only [vadd_eq_add, vsub_eq_sub, PiLp.add_apply, PiLp.sub_apply,
          PiLp.smul_apply, smul_eq_mul]
        have hj := hRcomp j
        linarith [hj]⟩

/-- The signed area is multiplied by `u * v` when the two sides emanating from
`P` are scaled by `u` and `v` respectively. -/
lemma twiceSignedArea_smul_smul {P Q R X Y : Plane} {u v : ℝ}
    (hQ : ∀ i : Fin 2, Q i - P i = u * (X i - P i))
    (hR : ∀ i : Fin 2, R i - P i = v * (Y i - P i)) :
    twiceSignedArea P Q R = u * v * twiceSignedArea P X Y := by
  unfold twiceSignedArea
  rw [hQ 0, hQ 1, hR 0, hR 1]
  ring

/-- AM-GM: if `a₁ + a₂ = 1` then `a₁ * a₂ ≤ 1 / 4`. -/
lemma mul_le_one_quarter {a₁ a₂ : ℝ} (h : a₁ + a₂ = 1) : a₁ * a₂ ≤ 1 / 4 := by
  have ha : a₂ = 1 - a₁ := by linarith
  rw [ha]
  nlinarith [sq_nonneg (a₁ - 1 / 2)]

snip end

problem imo1966_p6 (A B C K L M : Plane)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane))
    (hK : K ∈ openSegment ℝ B C)
    (hL : L ∈ openSegment ℝ C A)
    (hM : M ∈ openSegment ℝ A B) :
    triArea A M L ≤ triArea A B C / 4 ∨
    triArea B K M ≤ triArea A B C / 4 ∨
    triArea C L K ≤ triArea A B C / 4 := by
  -- Extract the barycentric coordinates of `K`, `L`, `M` on their sides.
  obtain ⟨a₁, a₂, ha₁, ha₂, hsumK, hKcomb⟩ := hK
  obtain ⟨b₁, b₂, hb₁, hb₂, hsumL, hLcomb⟩ := hL
  obtain ⟨c₁, c₂, hc₁, hc₂, hsumM, hMcomb⟩ := hM
  -- Componentwise versions of the affine combinations.
  have hKi : ∀ i : Fin 2, K i = a₁ * B i + a₂ * C i := by
    intro i
    have hi : (a₁ • B + a₂ • C) i = K i := by rw [hKcomb]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hi
    exact hi.symm
  have hLi : ∀ i : Fin 2, L i = b₁ * C i + b₂ * A i := by
    intro i
    have hi : (b₁ • C + b₂ • A) i = L i := by rw [hLcomb]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hi
    exact hi.symm
  have hMi : ∀ i : Fin 2, M i = c₁ * A i + c₂ * B i := by
    intro i
    have hi : (c₁ • A + c₂ • B) i = M i := by rw [hMcomb]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hi
    exact hi.symm
  -- The relevant side vectors are multiples of the sides of `ABC`.
  have hKB : ∀ i : Fin 2, K i - B i = a₂ * (C i - B i) := by
    intro i
    have ha : a₁ = 1 - a₂ := by linarith
    rw [hKi i, ha]
    ring
  have hKC : ∀ i : Fin 2, K i - C i = a₁ * (B i - C i) := by
    intro i
    have ha : a₂ = 1 - a₁ := by linarith
    rw [hKi i, ha]
    ring
  have hLA : ∀ i : Fin 2, L i - A i = b₁ * (C i - A i) := by
    intro i
    have hb : b₂ = 1 - b₁ := by linarith
    rw [hLi i, hb]
    ring
  have hLC : ∀ i : Fin 2, L i - C i = b₂ * (A i - C i) := by
    intro i
    have hb : b₁ = 1 - b₂ := by linarith
    rw [hLi i, hb]
    ring
  have hMA : ∀ i : Fin 2, M i - A i = c₂ * (B i - A i) := by
    intro i
    have hc : c₁ = 1 - c₂ := by linarith
    rw [hMi i, hc]
    ring
  have hMB : ∀ i : Fin 2, M i - B i = c₁ * (A i - B i) := by
    intro i
    have hc : c₂ = 1 - c₁ := by linarith
    rw [hMi i, hc]
    ring
  -- The signed areas of the corner triangles as multiples of that of `ABC`.
  have hsAML : twiceSignedArea A M L = (c₂ * b₁) * twiceSignedArea A B C :=
    twiceSignedArea_smul_smul hMA hLA
  have hsBKM : twiceSignedArea B K M = (a₂ * c₁) * twiceSignedArea A B C := by
    rw [twiceSignedArea_smul_smul hKB hMB, twiceSignedArea_cycle B C A,
      twiceSignedArea_cycle C A B]
  have hsCLK : twiceSignedArea C L K = (b₂ * a₁) * twiceSignedArea A B C := by
    rw [twiceSignedArea_smul_smul hLC hKC, twiceSignedArea_cycle C A B]
  -- Non-degeneracy of `ABC`.
  have hs : twiceSignedArea A B C ≠ 0 := mt collinear_of_twiceSignedArea_eq_zero hABC
  have hspos : (0 : ℝ) < |twiceSignedArea A B C| := abs_pos.mpr hs
  have hspos2 : (0 : ℝ) < |twiceSignedArea A B C| / 2 := by linarith
  -- The unsigned areas of the corner triangles.
  have eABC : triArea A B C = |twiceSignedArea A B C| / 2 := rfl
  have eAML : triArea A M L = (c₂ * b₁) * |twiceSignedArea A B C| / 2 := by
    unfold triArea
    rw [hsAML, abs_mul, abs_of_pos (mul_pos hc₂ hb₁)]
  have eBKM : triArea B K M = (a₂ * c₁) * |twiceSignedArea A B C| / 2 := by
    unfold triArea
    rw [hsBKM, abs_mul, abs_of_pos (mul_pos ha₂ hc₁)]
  have eCLK : triArea C L K = (b₂ * a₁) * |twiceSignedArea A B C| / 2 := by
    unfold triArea
    rw [hsCLK, abs_mul, abs_of_pos (mul_pos hb₂ ha₁)]
  -- Suppose all three corner triangles have area greater than a quarter of `ABC`.
  by_contra hneg
  push Not at hneg
  obtain ⟨h1, h2, h3⟩ := hneg
  rw [eABC, eAML] at h1
  rw [eABC, eBKM] at h2
  rw [eABC, eCLK] at h3
  -- Cancel the common factor `|twiceSignedArea A B C| / 2 > 0`.
  have g1 : (1 / 4 : ℝ) < c₂ * b₁ := by
    have h : (1 / 4) * (|twiceSignedArea A B C| / 2) <
        (c₂ * b₁) * (|twiceSignedArea A B C| / 2) := by linarith [h1]
    exact (mul_lt_mul_iff_of_pos_right hspos2).mp h
  have g2 : (1 / 4 : ℝ) < a₂ * c₁ := by
    have h : (1 / 4) * (|twiceSignedArea A B C| / 2) <
        (a₂ * c₁) * (|twiceSignedArea A B C| / 2) := by linarith [h2]
    exact (mul_lt_mul_iff_of_pos_right hspos2).mp h
  have g3 : (1 / 4 : ℝ) < b₂ * a₁ := by
    have h : (1 / 4) * (|twiceSignedArea A B C| / 2) <
        (b₂ * a₁) * (|twiceSignedArea A B C| / 2) := by linarith [h3]
    exact (mul_lt_mul_iff_of_pos_right hspos2).mp h
  -- Multiplying the three strict inequalities gives a product larger than `(1/4)³`.
  have hpos₁ : (0 : ℝ) < c₂ * b₁ := mul_pos hc₂ hb₁
  have hpos₂ : (0 : ℝ) < a₂ * c₁ := mul_pos ha₂ hc₁
  have hprod : (1 / 4 : ℝ) * ((1 / 4) * (1 / 4)) < (c₂ * b₁) * ((a₂ * c₁) * (b₂ * a₁)) := by
    have hA : (0 : ℝ) < (1 / 4) * (1 / 4) := by norm_num
    calc (1 / 4 : ℝ) * ((1 / 4) * (1 / 4))
        < (c₂ * b₁) * ((1 / 4) * (1 / 4)) := mul_lt_mul_of_pos_right g1 hA
      _ < (c₂ * b₁) * ((a₂ * c₁) * (1 / 4)) :=
          mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right g2 (by norm_num)) hpos₁
      _ < (c₂ * b₁) * ((a₂ * c₁) * (b₂ * a₁)) :=
          mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left g3 hpos₂) hpos₁
  -- But the product equals `(a₁a₂)(b₁b₂)(c₁c₂)`, which is at most `(1/4)³`.
  have hub : (c₂ * b₁) * ((a₂ * c₁) * (b₂ * a₁)) ≤ (1 / 4 : ℝ) * ((1 / 4) * (1 / 4)) := by
    have he : (c₂ * b₁) * ((a₂ * c₁) * (b₂ * a₁)) =
        (a₁ * a₂) * ((b₁ * b₂) * (c₁ * c₂)) := by ring
    rw [he]
    have hbc : (b₁ * b₂) * (c₁ * c₂) ≤ (1 / 4 : ℝ) * (1 / 4) :=
      mul_le_mul (mul_le_one_quarter hsumL) (mul_le_one_quarter hsumM)
        (mul_nonneg (le_of_lt hc₁) (le_of_lt hc₂)) (by norm_num)
    exact mul_le_mul (mul_le_one_quarter hsumK) hbc
      (mul_nonneg (mul_nonneg (le_of_lt hb₁) (le_of_lt hb₂))
        (mul_nonneg (le_of_lt hc₁) (le_of_lt hc₂))) (by norm_num)
  linarith

end Imo1966P6
