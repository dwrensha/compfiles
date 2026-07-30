/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Geometry]
}

/-!
# International Mathematical Olympiad 1961, Problem 4

Consider triangle $P_1P_2P_3$ and a point $P$ within the triangle.
Lines $P_1P$, $P_2P$, $P_3P$ intersect the opposite sides in points
$Q_1$, $Q_2$, $Q_3$ respectively. Prove that, of the numbers
$$ \frac{P_1P}{PQ_1}, \quad \frac{P_2P}{PQ_2}, \quad \frac{P_3P}{PQ_3} $$
at least one is $\le 2$ and at least one is $\ge 2$.
-/

namespace Imo1961P4

snip begin

/-!
## Proof strategy

Let $w_i$ be the barycentric coordinate of $P$ at the vertex $P_i$.
Since $P$ is strictly inside the triangle, $0 < w_i$ and
$w_1 + w_2 + w_3 = 1$. The point $Q_i$ lies on the line $P_iP$ and on the
opposite side, and a short computation shows that
$$ \frac{P_iP}{PQ_i} = \frac{1 - w_i}{w_i}. $$
Hence the claim reduces to a pigeonhole principle: since the $w_i$ are
positive and sum to $1$, at least one of them is $\ge 1/3$ and at least one
is $\le 1/3$, and $(1 - w)/w \le 2 \iff w \ge 1/3$.
-/

/--
Key lemma: the ratio in which a cevian through an interior point is divided,
expressed through the barycentric coordinate `f P` of `P` at the vertex `V`.
Here `f` is an affine function with `f V = 1` that vanishes on the two
vertices `V₁, V₂` of the opposite side, and `Q` lies both on the segment
`V₁V₂` and on the line `VP`. Then `dist V P / dist P Q = (1 - f P) / f P`.
-/
lemma cevian_ratio
    {V V₁ V₂ P Q : EuclideanSpace ℝ (Fin 2)} {f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ}
    (hfV : f V = 1) (hfV₁ : f V₁ = 0) (hfV₂ : f V₂ = 0)
    (hfP0 : 0 < f P) (hfP1 : f P < 1)
    (hQ : Q ∈ segment ℝ V₁ V₂)
    (hcol : Collinear ℝ {V, P, Q}) :
    dist V P / dist P Q = (1 - f P) / f P := by
  have hVP : V ≠ P := by
    rintro rfl
    rw [hfV] at hfP1
    exact lt_irrefl 1 hfP1
  -- Since `Q` lies on the segment `V₁V₂`, on which `f` vanishes, `f Q = 0`.
  rw [segment_eq_image_lineMap] at hQ
  obtain ⟨t, -, htQ⟩ := hQ
  have hfQ : f Q = 0 := by
    rw [← htQ, AffineMap.apply_lineMap, hfV₁, hfV₂]
    simp
  -- Since `Q` is collinear with `V` and `P`, write `Q = lineMap V P c`.
  obtain ⟨c, hc⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp
    (hcol.mem_affineSpan_of_mem_of_ne (p₁ := V) (p₂ := P) (p₃ := Q)
      (by simp) (by simp) (by simp) hVP)
  -- Applying `f` to this equation determines `c`.
  have hfc : AffineMap.lineMap (f V) (f P) c = 0 := by
    rw [← AffineMap.apply_lineMap, hc, hfQ]
  rw [hfV] at hfc
  have hw1 : (1 : ℝ) - f P ≠ 0 := ne_of_gt (sub_pos.mpr hfP1)
  have key : c * (1 - f P) = 1 := by
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul] at hfc
    linear_combination -hfc
  have hc_eq : c = 1 / (1 - f P) := (eq_div_iff hw1).mpr key
  have hcgt : 1 < c := by
    rw [hc_eq, one_lt_div (sub_pos.mpr hfP1)]
    linarith [hfP1]
  -- Compute the distance `dist P Q` along the line `VP`.
  have hdist : dist P Q = (c - 1) * dist V P := by
    have e1 : Q = AffineMap.lineMap V P c := hc.symm
    have e2 : P = AffineMap.lineMap V P (1 : ℝ) := (AffineMap.lineMap_apply_one V P).symm
    rw [e1]
    conv_lhs => arg 1; rw [e2]
    rw [dist_lineMap_lineMap, Real.dist_eq, abs_of_neg (sub_neg.mpr hcgt)]
    ring
  -- Assemble the ratio.
  rw [hdist, hc_eq]
  have hd : dist V P ≠ 0 := dist_ne_zero.mpr hVP
  have h4 : (1 : ℝ) / (1 - f P) - 1 = f P / (1 - f P) := by
    field_simp
    ring
  rw [h4, mul_comm (f P / (1 - f P)) (dist V P), div_mul_eq_div_div, div_self hd,
    one_div_div]

snip end

problem imo1961_p4
    (A B C P Q₁ Q₂ Q₃ : EuclideanSpace ℝ (Fin 2))
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C}))
    (hQ₁ : Q₁ ∈ segment ℝ B C) (hcol₁ : Collinear ℝ {A, P, Q₁})
    (hQ₂ : Q₂ ∈ segment ℝ A C) (hcol₂ : Collinear ℝ {B, P, Q₂})
    (hQ₃ : Q₃ ∈ segment ℝ A B) (hcol₃ : Collinear ℝ {C, P, Q₃}) :
    (dist A P / dist P Q₁ ≤ 2 ∨ dist B P / dist P Q₂ ≤ 2 ∨ dist C P / dist P Q₃ ≤ 2) ∧
    (2 ≤ dist A P / dist P Q₁ ∨ 2 ≤ dist B P / dist P Q₂ ∨ 2 ≤ dist C P / dist P Q₃) := by
  -- Set up the affine basis given by the vertices of the triangle.
  have htot' : affineSpan ℝ (Set.range ![A, B, C]) = ⊤ := by
    rw [AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nontrivial]
    apply AffineIndependent.vectorSpan_eq_top_of_card_eq_finrank_add_one hABC
    rw [finrank_euclideanSpace]
    simp only [Nat.succ_eq_add_one, zero_add, Nat.reduceAdd, Fintype.card_fin]
  set basis := AffineBasis.mk _ hABC htot' with h_basis
  have h_range : {A, B, C} = Set.range basis := by
    rw [h_basis, DFunLike.coe, AffineBasis.instFunLike]
    simp
    rw [Set.pair_comm, Set.insert_comm, Set.pair_comm]
  rw [h_range, AffineBasis.interior_convexHull] at hP
  dsimp at hP
  have hA : A = basis 0 := by
    rw [h_basis, DFunLike.coe, AffineBasis.instFunLike]
    simp
  have hB : B = basis 1 := by
    rw [h_basis, DFunLike.coe, AffineBasis.instFunLike]
    simp
  have hC : C = basis 2 := by
    rw [h_basis, DFunLike.coe, AffineBasis.instFunLike]
    simp
  -- The barycentric coordinates of `P` are positive and sum to `1`.
  have hsum : basis.coord 0 P + basis.coord 1 P + basis.coord 2 P = 1 := by
    have h := AffineBasis.sum_coord_apply_eq_one basis P
    rwa [Fin.sum_univ_three] at h
  have hw0lt : basis.coord 0 P < 1 := by
    have h1 := hP 1; have h2 := hP 2; linarith
  have hw1lt : basis.coord 1 P < 1 := by
    have h0 := hP 0; have h2 := hP 2; linarith
  have hw2lt : basis.coord 2 P < 1 := by
    have h0 := hP 0; have h1 := hP 1; linarith
  -- Express each ratio through the corresponding barycentric coordinate.
  have r₁ : dist A P / dist P Q₁ = (1 - basis.coord 0 P) / basis.coord 0 P :=
    cevian_ratio (V := A) (V₁ := B) (V₂ := C) (P := P) (Q := Q₁) (f := basis.coord 0)
      (by rw [hA]; exact AffineBasis.coord_apply_eq basis 0)
      (by rw [hB]; exact AffineBasis.coord_apply_ne basis (show (0 : Fin 3) ≠ 1 by decide))
      (by rw [hC]; exact AffineBasis.coord_apply_ne basis (show (0 : Fin 3) ≠ 2 by decide))
      (hP 0) hw0lt hQ₁ hcol₁
  have r₂ : dist B P / dist P Q₂ = (1 - basis.coord 1 P) / basis.coord 1 P :=
    cevian_ratio (V := B) (V₁ := A) (V₂ := C) (P := P) (Q := Q₂) (f := basis.coord 1)
      (by rw [hB]; exact AffineBasis.coord_apply_eq basis 1)
      (by rw [hA]; exact AffineBasis.coord_apply_ne basis (show (1 : Fin 3) ≠ 0 by decide))
      (by rw [hC]; exact AffineBasis.coord_apply_ne basis (show (1 : Fin 3) ≠ 2 by decide))
      (hP 1) hw1lt hQ₂ hcol₂
  have r₃ : dist C P / dist P Q₃ = (1 - basis.coord 2 P) / basis.coord 2 P :=
    cevian_ratio (V := C) (V₁ := A) (V₂ := B) (P := P) (Q := Q₃) (f := basis.coord 2)
      (by rw [hC]; exact AffineBasis.coord_apply_eq basis 2)
      (by rw [hA]; exact AffineBasis.coord_apply_ne basis (show (2 : Fin 3) ≠ 0 by decide))
      (by rw [hB]; exact AffineBasis.coord_apply_ne basis (show (2 : Fin 3) ≠ 1 by decide))
      (hP 2) hw2lt hQ₃ hcol₃
  -- Pigeonhole: of three positive numbers summing to `1`, at least one is
  -- `≥ 1/3` (giving a ratio `≤ 2`) and at least one is `≤ 1/3` (giving `≥ 2`).
  constructor
  · by_contra! hcon
    obtain ⟨g1, g2, g3⟩ := hcon
    rw [r₁, lt_div_iff₀ (hP 0)] at g1
    rw [r₂, lt_div_iff₀ (hP 1)] at g2
    rw [r₃, lt_div_iff₀ (hP 2)] at g3
    linarith
  · by_contra! hcon
    obtain ⟨g1, g2, g3⟩ := hcon
    rw [r₁, div_lt_iff₀ (hP 0)] at g1
    rw [r₂, div_lt_iff₀ (hP 1)] at g2
    rw [r₃, div_lt_iff₀ (hP 2)] at g3
    linarith

end Imo1961P4
