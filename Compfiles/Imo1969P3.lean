/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Analysis.Convex.StrictConvexBetween
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.AffineSpace.Midpoint
public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1969, Problem 3

For each of k = 1, 2, 3, 4, 5 find necessary and sufficient conditions on
a > 0 such that there exists a tetrahedron with k edges length a and the
remainder length 1.
-/

namespace Imo1969P3

/-- Three-dimensional Euclidean space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The six edges of a tetrahedron whose vertices are indexed by `Fin 4`:
the pairs `(i, j)` with `i < j`. -/
def tetraEdges : Finset (Fin 4 × Fin 4) :=
  (Finset.univ ×ˢ Finset.univ).filter (fun e => e.1 < e.2)

/-- `HasTetra k a` says that there exists a non-degenerate tetrahedron
(four affinely independent points in space) with `k` edges of length `a`
and the remaining `6 - k` edges of length `1`. -/
def HasTetra (k : ℕ) (a : ℝ) : Prop :=
  ∃ p : Fin 4 → E3, AffineIndependent ℝ p ∧ ∃ s : Finset (Fin 4 × Fin 4),
    s ⊆ tetraEdges ∧ s.card = k ∧
    (∀ e ∈ s, dist (p e.1) (p e.2) = a) ∧
    (∀ e ∈ tetraEdges \ s, dist (p e.1) (p e.2) = 1)

/-- The answer to the problem: for each `k = 1, …, 5`, the set of `a > 0`
for which a tetrahedron with `k` edges of length `a` and the remaining
edges of length `1` exists. -/
determine answer (k : ℕ) : Set ℝ :=
  match k with
  | 1 => Set.Ioo 0 (Real.sqrt 3)
  | 2 => Set.Ioo 0 (Real.sqrt (2 + Real.sqrt 3))
  | 3 => Set.Ioi 0
  | 4 => Set.Ioi (Real.sqrt (2 - Real.sqrt 3))
  | 5 => Set.Ioi (1 / Real.sqrt 3)
  | _ => ∅

snip begin

/-- The edge set of a tetrahedron has six elements. -/
theorem card_tetraEdges : tetraEdges.card = 6 := by
  decide

/-- Distance between two literal points of `E3`. -/
theorem dist3 (x1 y1 z1 x2 y2 z2 : ℝ) :
    dist (!₂[x1, y1, z1] : E3) !₂[x2, y2, z2]
      = Real.sqrt ((x1 - x2) ^ 2 + (y1 - y2) ^ 2 + (z1 - z2) ^ 2) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Real.dist_eq, sq_abs]

/-- Four points in "triangular" coordinate form are affinely independent. -/
theorem ai_triangular {x1 x2 y2 x3 y3 z3 : ℝ}
    (hx1 : x1 ≠ 0) (hy2 : y2 ≠ 0) (hz3 : z3 ≠ 0) :
    AffineIndependent ℝ
      ![(!₂[0, 0, 0] : E3), !₂[x1, 0, 0], !₂[x2, y2, 0], !₂[x3, y3, z3]] := by
  rw [affineIndependent_iff_of_fintype]
  intro w hw0 hwv i
  rw [Finset.weightedVSub_eq_linear_combination _ hw0, Fin.sum_univ_four] at hwv
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hwv
  rw [WithLp.ext_iff] at hwv
  simp only [WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_zero] at hwv
  have e0 := congr_fun hwv 0
  have e1 := congr_fun hwv 1
  have e2 := congr_fun hwv 2
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons,
    mul_zero, add_zero, zero_add] at e0 e1 e2
  have h3 : w 3 = 0 := (mul_eq_zero.mp e2).resolve_right hz3
  rw [h3, zero_mul, add_zero] at e1
  have h2 : w 2 = 0 := (mul_eq_zero.mp e1).resolve_right hy2
  rw [h3, h2, zero_mul, zero_mul, add_zero, add_zero] at e0
  have h1 : w 1 = 0 := (mul_eq_zero.mp e0).resolve_right hx1
  rw [Fin.sum_univ_four] at hw0
  have h0 : w 0 = 0 := by linarith
  fin_cases i <;> assumption

/-- Restriction of an affinely independent family to four distinct vertices. -/
theorem ai_comp {p : Fin 4 → E3} (h : AffineIndependent ℝ p) {i j k l : Fin 4}
    (hinj : Function.Injective ![i, j, k, l]) :
    AffineIndependent ℝ ![p i, p j, p k, p l] := by
  have heq : ![p i, p j, p k, p l] = p ∘ ![i, j, k, l] := by
    funext x; fin_cases x <;> rfl
  rw [heq]
  exact AffineIndependent.comp_embedding ⟨![i, j, k, l], hinj⟩ h

/-- Apollonius's theorem: the squared distance from a point to the midpoint of
a segment in terms of the distances to the endpoints. -/
theorem apollonius (P C D : E3) :
    dist P (midpoint ℝ C D) ^ 2
      = (2 * dist P C ^ 2 + 2 * dist P D ^ 2 - dist C D ^ 2) / 4 := by
  have hpara := parallelogram_law_with_norm ℝ (P -ᵥ C) (P -ᵥ D)
  have hsub : (P -ᵥ C) - (P -ᵥ D) = D -ᵥ C := by
    rw [vsub_eq_sub, vsub_eq_sub, vsub_eq_sub]; abel
  have hadd : (P -ᵥ C) + (P -ᵥ D) = (2 : ℝ) • (P -ᵥ midpoint ℝ C D) := by
    rw [midpoint_eq_smul_add, vsub_eq_sub, vsub_eq_sub, vsub_eq_sub, invOf_eq_inv]
    module
  rw [hsub, hadd, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hpara
  have hnorm : ‖D -ᵥ C‖ = ‖C -ᵥ D‖ := by rw [← neg_vsub_eq_vsub_rev, norm_neg]
  rw [dist_eq_norm_vsub, dist_eq_norm_vsub, dist_eq_norm_vsub, dist_eq_norm_vsub,
    ← hnorm]
  linarith [hpara]

/-- Strict triangle inequality with a midpoint: if `A B C D` are affinely
independent, then the midpoint of `CD` cannot lie on the segment `AB`,
so the triangle inequality is strict. -/
theorem hinge_between {A B C D : E3} (h : AffineIndependent ℝ ![A, B, C, D]) :
    dist A B < dist A (midpoint ℝ C D) + dist (midpoint ℝ C D) B := by
  rcases (dist_triangle A (midpoint ℝ C D) B).lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    have hw : Wbtw ℝ A (midpoint ℝ C D) B := dist_add_dist_eq_iff.mp heq.symm
    rw [← mem_segment_iff_wbtw, segment_eq_image_lineMap] at hw
    obtain ⟨t, -, hM⟩ := hw
    have hM2 : (1 - t) • A + t • B = (1 / 2 : ℝ) • C + (1 / 2 : ℝ) • D := by
      have e2 := AffineMap.lineMap_apply_module A B t
      rw [hM, midpoint_eq_smul_add, invOf_eq_inv, smul_add] at e2
      have hhalf : ((2 : ℝ)⁻¹) = 1 / 2 := by norm_num
      rw [hhalf] at e2
      exact e2.symm
    rw [affineIndependent_iff_of_fintype] at h
    have hw0 : ∑ i : Fin 4, ![1 - t, t, -(1 / 2 : ℝ), -(1 / 2 : ℝ)] i = 0 := by
      rw [Fin.sum_univ_four]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      ring
    have hwv : Finset.univ.weightedVSub ![A, B, C, D]
        ![1 - t, t, -(1 / 2 : ℝ), -(1 / 2 : ℝ)] = 0 := by
      rw [Finset.weightedVSub_eq_linear_combination _ hw0, Fin.sum_univ_four]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      linear_combination (norm := module) hM2
    have h2 := h ![1 - t, t, -(1 / 2 : ℝ), -(1 / 2 : ℝ)] hw0 hwv 2
    simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h2
    norm_num at h2

/-- Strict triangle inequality with a midpoint: `B` cannot lie on the segment
from `A` to the midpoint of `CD`. -/
theorem hinge_left {A B C D : E3} (h : AffineIndependent ℝ ![A, B, C, D]) :
    dist A (midpoint ℝ C D) < dist A B + dist B (midpoint ℝ C D) := by
  rcases (dist_triangle A B (midpoint ℝ C D)).lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    have hw : Wbtw ℝ A B (midpoint ℝ C D) := dist_add_dist_eq_iff.mp heq.symm
    rw [← mem_segment_iff_wbtw, segment_eq_image_lineMap] at hw
    obtain ⟨t, -, hM⟩ := hw
    have hM2 : (1 - t) • A + (t / 2 : ℝ) • C + (t / 2 : ℝ) • D = B := by
      have e2 := AffineMap.lineMap_apply_module A (midpoint ℝ C D) t
      rw [hM, midpoint_eq_smul_add, invOf_eq_inv] at e2
      rw [e2]
      module
    rw [affineIndependent_iff_of_fintype] at h
    have hw0 : ∑ i : Fin 4, ![1 - t, -1, t / 2, t / 2] i = 0 := by
      rw [Fin.sum_univ_four]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      ring
    have hwv : Finset.univ.weightedVSub ![A, B, C, D] ![1 - t, -1, t / 2, t / 2] = 0 := by
      rw [Finset.weightedVSub_eq_linear_combination _ hw0, Fin.sum_univ_four]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      linear_combination (norm := module) hM2
    have h2 := h ![1 - t, -1, t / 2, t / 2] hw0 hwv 1
    simp only [Matrix.cons_val_one] at h2
    norm_num at h2

/-- Scaling points by a positive scalar scales distances. -/
theorem dist_smul_point (c : ℝ) (hc : 0 < c) (x y : E3) :
    dist (c • x) (c • y) = c * dist x y := by
  rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_pos hc]

/-- Scaling a tetrahedron by `1/a` swaps the roles of `k` and `6 - k`. -/
theorem hasTetra_dual_aux {k : ℕ} (_hk : k ≤ 6) {a : ℝ} (ha : 0 < a) :
    HasTetra k a → HasTetra (6 - k) (1 / a) := by
  rintro ⟨p, hAI, s, hs, hcard, hsa, hs1⟩
  have ha' : (1 / a : ℝ) ≠ 0 := by positivity
  refine ⟨fun i => (1 / a) • p i, ?_, tetraEdges \ s, Finset.sdiff_subset, ?_, ?_, ?_⟩
  · rw [affineIndependent_iff_of_fintype] at hAI ⊢
    intro w hw0 hwv i
    apply hAI w hw0
    rw [Finset.weightedVSub_eq_linear_combination _ hw0] at hwv ⊢
    have hsum : (∑ i ∈ Finset.univ, w i • (1 / a) • p i)
        = (1 / a) • (∑ i ∈ Finset.univ, w i • p i) := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl (fun i _ => (smul_comm _ _ _).symm)
    rw [hsum, smul_eq_zero] at hwv
    exact hwv.resolve_left ha'
  · rw [Finset.card_sdiff, card_tetraEdges, Finset.inter_eq_left.mpr hs, hcard]
  · intro e he
    have h1 := hs1 e he
    rw [dist_smul_point _ (by positivity : (0 : ℝ) < 1 / a), h1, mul_one]
  · intro e he
    rw [Finset.sdiff_sdiff_eq_self hs] at he
    have h1 := hsa e he
    rw [dist_smul_point _ (by positivity : (0 : ℝ) < 1 / a), h1,
      div_mul_cancel₀ _ ha.ne']

theorem hasTetra_dual {k : ℕ} (hk : k ≤ 6) {a : ℝ} (ha : 0 < a) :
    HasTetra (6 - k) (1 / a) ↔ HasTetra k a := by
  constructor
  · intro h
    have h6 : 6 - k ≤ 6 := by omega
    have hpos : (0 : ℝ) < 1 / a := by positivity
    have h' := hasTetra_dual_aux h6 hpos h
    rwa [show 6 - (6 - k) = k by omega, one_div_one_div] at h'
  · exact hasTetra_dual_aux hk ha

/-- Any edge length occurring in a tetrahedron is positive. -/
theorem hasTetra_pos {k : ℕ} (hk : 0 < k) {a : ℝ} : HasTetra k a → 0 < a := by
  rintro ⟨p, hAI, s, hs, hcard, hsa, -⟩
  obtain ⟨e, he⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
  have h1 := hsa e he
  have he2 : e.1 < e.2 := by
    have h2 := hs he
    simp only [tetraEdges, Finset.mem_filter, Finset.mem_univ, Finset.mem_product,
      true_and] at h2
    exact h2
  rw [← h1]
  exact dist_pos.mpr (hAI.injective.ne he2.ne)

/-- In a tetrahedron where the edge `(i, j)` has length `a` and the other five
edges have length `1`, `a < √3`: hinge the two unit triangles sharing the edge
`(k, l)` about their common edge; the extreme position is degenerate. -/
theorem k1_nec {p : Fin 4 → E3} (hAI : AffineIndependent ℝ p) {a : ℝ} {i j k l : Fin 4}
    (hinj : Function.Injective ![i, j, k, l])
    (hij : dist (p i) (p j) = a) (hik : dist (p i) (p k) = 1)
    (hil : dist (p i) (p l) = 1) (hjk : dist (p j) (p k) = 1)
    (hjl : dist (p j) (p l) = 1) (hkl : dist (p k) (p l) = 1) :
    a < Real.sqrt 3 := by
  have hlt : dist (p i) (p j)
      < dist (p i) (midpoint ℝ (p k) (p l)) + dist (midpoint ℝ (p k) (p l)) (p j) :=
    hinge_between (ai_comp hAI hinj)
  have h34 : Real.sqrt (3 / 4 : ℝ) = Real.sqrt 3 / 2 := by
    rw [Real.sqrt_div (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  have hAi : dist (p i) (midpoint ℝ (p k) (p l)) ^ 2 = 3 / 4 := by
    have h := apollonius (p i) (p k) (p l)
    rw [hik, hil, hkl] at h
    rw [h]; norm_num
  have hAi2 : dist (p i) (midpoint ℝ (p k) (p l)) = Real.sqrt 3 / 2 := by
    rw [← Real.sqrt_sq dist_nonneg, hAi, h34]
  have hBj : dist (p j) (midpoint ℝ (p k) (p l)) ^ 2 = 3 / 4 := by
    have h := apollonius (p j) (p k) (p l)
    rw [hjk, hjl, hkl] at h
    rw [h]; norm_num
  have hBj2 : dist (midpoint ℝ (p k) (p l)) (p j) = Real.sqrt 3 / 2 := by
    rw [dist_comm, ← Real.sqrt_sq dist_nonneg, hBj, h34]
  rw [hij, hAi2, hBj2] at hlt
  have hsum : Real.sqrt 3 / 2 + Real.sqrt 3 / 2 = Real.sqrt 3 := by ring
  linarith

theorem hasTetra_one (a : ℝ) : HasTetra 1 a ↔ 0 < a ∧ a < Real.sqrt 3 := by
  constructor
  · rintro ⟨p, hAI, s, hsub, hcard, ha, h1⟩
    obtain ⟨e, rfl⟩ := Finset.card_eq_one.mp hcard
    have he_mem : e ∈ tetraEdges := hsub (Finset.mem_singleton_self e)
    have hlt_e : e.1 < e.2 := by
      have h := he_mem
      rw [tetraEdges, Finset.mem_filter] at h
      exact h.2
    have ha_e : dist (p e.1) (p e.2) = a := ha e (Finset.mem_singleton_self e)
    have hpos : 0 < a := by
      rw [← ha_e]
      exact dist_pos.mpr (hAI.injective.ne (ne_of_lt hlt_e))
    have h1' : ∀ e' ∈ tetraEdges, e' ≠ e → dist (p e'.1) (p e'.2) = 1 := by
      intro e' he' hne
      exact h1 e' (Finset.mem_sdiff.mpr ⟨he', fun h => hne (Finset.mem_singleton.mp h)⟩)
    refine ⟨hpos, ?_⟩
    fin_cases he_mem
    · -- the edge `(0, 1)` has length `a`
      have h02 := h1' (0, 2) (by decide) (by decide)
      have h03 := h1' (0, 3) (by decide) (by decide)
      have h12 := h1' (1, 2) (by decide) (by decide)
      have h13 := h1' (1, 3) (by decide) (by decide)
      have h23 := h1' (2, 3) (by decide) (by decide)
      exact k1_nec hAI (by decide) ha_e h02 h03 h12 h13 h23
    · -- the edge `(0, 2)` has length `a`
      have h01 := h1' (0, 1) (by decide) (by decide)
      have h03 := h1' (0, 3) (by decide) (by decide)
      have h12 := h1' (1, 2) (by decide) (by decide)
      have h13 := h1' (1, 3) (by decide) (by decide)
      have h23 := h1' (2, 3) (by decide) (by decide)
      exact k1_nec hAI (by decide) ha_e h01 h03 ((dist_comm _ _).trans h12) h23 h13
    · -- the edge `(0, 3)` has length `a`
      have h01 := h1' (0, 1) (by decide) (by decide)
      have h02 := h1' (0, 2) (by decide) (by decide)
      have h12 := h1' (1, 2) (by decide) (by decide)
      have h13 := h1' (1, 3) (by decide) (by decide)
      have h23 := h1' (2, 3) (by decide) (by decide)
      exact k1_nec hAI (by decide) ha_e h01 h02 ((dist_comm _ _).trans h13)
        ((dist_comm _ _).trans h23) h12
    · -- the edge `(1, 2)` has length `a`
      have h01 := h1' (0, 1) (by decide) (by decide)
      have h02 := h1' (0, 2) (by decide) (by decide)
      have h03 := h1' (0, 3) (by decide) (by decide)
      have h13 := h1' (1, 3) (by decide) (by decide)
      have h23 := h1' (2, 3) (by decide) (by decide)
      exact k1_nec hAI (by decide) ha_e ((dist_comm _ _).trans h01) h13
        ((dist_comm _ _).trans h02) h23 h03
    · -- the edge `(1, 3)` has length `a`
      have h01 := h1' (0, 1) (by decide) (by decide)
      have h02 := h1' (0, 2) (by decide) (by decide)
      have h03 := h1' (0, 3) (by decide) (by decide)
      have h12 := h1' (1, 2) (by decide) (by decide)
      have h23 := h1' (2, 3) (by decide) (by decide)
      exact k1_nec hAI (by decide) ha_e ((dist_comm _ _).trans h01) h12
        ((dist_comm _ _).trans h03) ((dist_comm _ _).trans h23) h02
    · -- the edge `(2, 3)` has length `a`
      have h01 := h1' (0, 1) (by decide) (by decide)
      have h02 := h1' (0, 2) (by decide) (by decide)
      have h03 := h1' (0, 3) (by decide) (by decide)
      have h12 := h1' (1, 2) (by decide) (by decide)
      have h13 := h1' (1, 3) (by decide) (by decide)
      exact k1_nec hAI (by decide) ha_e ((dist_comm _ _).trans h02)
        ((dist_comm _ _).trans h12) ((dist_comm _ _).trans h03)
        ((dist_comm _ _).trans h13) h01
  · rintro ⟨ha, hlt⟩
    have ha3 : a ^ 2 < 3 := (Real.lt_sqrt ha.le).mp hlt
    have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
    set c : ℝ := 1 - 2 * a ^ 2 / 3 with hc
    have hc1 : c < 1 := by
      rw [hc]; nlinarith
    have hc2 : -1 < c := by
      rw [hc]; nlinarith
    have h1c : (0:ℝ) < 1 - c ^ 2 := by
      nlinarith [hc1, hc2]
    set sq : ℝ := Real.sqrt (1 - c ^ 2) with hsq
    have hsq_pos : 0 < sq := hsq ▸ Real.sqrt_pos.mpr h1c
    have hsq2 : sq ^ 2 = 1 - c ^ 2 := hsq ▸ Real.sq_sqrt h1c.le
    have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have h32 : (0:ℝ) < Real.sqrt 3 / 2 := by positivity
    refine ⟨![(!₂[0, 0, 0] : E3), !₂[1, 0, 0], !₂[1/2, Real.sqrt 3 / 2, 0],
        !₂[1/2, (Real.sqrt 3 / 2) * c, (Real.sqrt 3 / 2) * sq]], ?_, {(2, 3)},
      ?_, ?_, ?_, ?_⟩
    · exact ai_triangular one_ne_zero (ne_of_gt h32)
        (mul_ne_zero (ne_of_gt h32) (ne_of_gt hsq_pos))
    · intro e he
      rw [Finset.mem_singleton] at he
      rw [he]
      decide
    · simp
    · intro e he
      rw [Finset.mem_singleton] at he
      subst he
      show dist (!₂[1/2, Real.sqrt 3 / 2, 0] : E3)
        !₂[1/2, (Real.sqrt 3 / 2) * c, (Real.sqrt 3 / 2) * sq] = a
      rw [dist3]
      have hin : (1/2 - 1/2 : ℝ) ^ 2 + (Real.sqrt 3 / 2 - (Real.sqrt 3 / 2) * c) ^ 2
          + (0 - (Real.sqrt 3 / 2) * sq) ^ 2 = a ^ 2 := by
        nlinarith [h3, hsq2, hc]
      rw [hin]
      exact Real.sqrt_sq ha.le
    · have hsd : tetraEdges \ ({(2, 3)} : Finset (Fin 4 × Fin 4))
          = {(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)} := by
        decide
      rw [hsd]
      intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl | rfl
      · show dist (!₂[0, 0, 0] : E3) !₂[1, 0, 0] = 1
        rw [dist3]
        have hin : (0 - 1 : ℝ) ^ 2 + (0 - 0) ^ 2 + (0 - 0) ^ 2 = 1 := by ring
        rw [hin]
        exact Real.sqrt_one
      · show dist (!₂[0, 0, 0] : E3) !₂[1/2, Real.sqrt 3 / 2, 0] = 1
        rw [dist3]
        have hin : (0 - 1/2 : ℝ) ^ 2 + (0 - Real.sqrt 3 / 2) ^ 2 + (0 - 0) ^ 2 = 1 := by
          nlinarith [h3]
        rw [hin]
        exact Real.sqrt_one
      · show dist (!₂[0, 0, 0] : E3)
            !₂[1/2, (Real.sqrt 3 / 2) * c, (Real.sqrt 3 / 2) * sq] = 1
        rw [dist3]
        have hin : (0 - 1/2 : ℝ) ^ 2 + (0 - (Real.sqrt 3 / 2) * c) ^ 2
            + (0 - (Real.sqrt 3 / 2) * sq) ^ 2 = 1 := by
          nlinarith [h3, hsq2]
        rw [hin]
        exact Real.sqrt_one
      · show dist (!₂[1, 0, 0] : E3) !₂[1/2, Real.sqrt 3 / 2, 0] = 1
        rw [dist3]
        have hin : (1 - 1/2 : ℝ) ^ 2 + (0 - Real.sqrt 3 / 2) ^ 2 + (0 - 0) ^ 2 = 1 := by
          nlinarith [h3]
        rw [hin]
        exact Real.sqrt_one
      · show dist (!₂[1, 0, 0] : E3)
            !₂[1/2, (Real.sqrt 3 / 2) * c, (Real.sqrt 3 / 2) * sq] = 1
        rw [dist3]
        have hin : (1 - 1/2 : ℝ) ^ 2 + (0 - (Real.sqrt 3 / 2) * c) ^ 2
            + (0 - (Real.sqrt 3 / 2) * sq) ^ 2 = 1 := by
          nlinarith [h3, hsq2]
        rw [hin]
        exact Real.sqrt_one

/-- Swapping the two pairs of an injective quadruple of indices. -/
theorem k2_inj_swap {i j k l : Fin 4} (h : Function.Injective ![i, j, k, l]) :
    Function.Injective ![k, l, i, j] := by
  have heq : ![k, l, i, j] = ![i, j, k, l] ∘ ![2, 3, 0, 1] := by
    funext x; fin_cases x <;> rfl
  rw [heq]
  exact h.comp (by decide : Function.Injective (![2, 3, 0, 1] : Fin 4 → Fin 4))

/-- Necessity bound in the opposite-edges configuration: if the two edges of
length `a` are opposite, then `a < √2`. -/
theorem k2_opp_nec {p : Fin 4 → E3} (hAI : AffineIndependent ℝ p) {a : ℝ}
    {i j k l : Fin 4} (hinj : Function.Injective ![i, j, k, l])
    (hij : dist (p i) (p j) = a) (hkl : dist (p k) (p l) = a)
    (hik : dist (p i) (p k) = 1) (hil : dist (p i) (p l) = 1)
    (hjk : dist (p j) (p k) = 1) (hjl : dist (p j) (p l) = 1) :
    a < Real.sqrt 2 := by
  have ha0 : 0 ≤ a := by rw [← hij]; exact dist_nonneg
  have h1 : dist (p k) (midpoint ℝ (p i) (p j)) ^ 2 = 1 - a ^ 2 / 4 := by
    rw [apollonius, dist_comm (p k) (p i), dist_comm (p k) (p j), hik, hjk, hij]
    ring
  have h2 : dist (p l) (midpoint ℝ (p i) (p j)) ^ 2 = 1 - a ^ 2 / 4 := by
    rw [apollonius, dist_comm (p l) (p i), dist_comm (p l) (p j), hil, hjl, hij]
    ring
  have hu_nonneg : 0 ≤ 1 - a ^ 2 / 4 := by rw [← h1]; positivity
  have hkM : dist (p k) (midpoint ℝ (p i) (p j)) = Real.sqrt (1 - a^2/4) := by
    rw [← Real.sqrt_sq dist_nonneg, h1]
  have hlM : dist (p l) (midpoint ℝ (p i) (p j)) = Real.sqrt (1 - a^2/4) := by
    rw [← Real.sqrt_sq dist_nonneg, h2]
  have hb := hinge_between (A := p k) (B := p l) (C := p i) (D := p j)
    (ai_comp hAI (k2_inj_swap hinj))
  rw [dist_comm (midpoint ℝ (p i) (p j)) (p l), hkl, hkM, hlM] at hb
  have hu2 : (Real.sqrt (1 - a^2/4))^2 = 1 - a^2/4 := Real.sq_sqrt hu_nonneg
  have ha2 : a^2 < 2 := by
    nlinarith [hb, hu2, Real.sqrt_nonneg (1 - a^2/4), ha0]
  exact (Real.lt_sqrt ha0).mpr ha2

/-- Necessity bound in the adjacent-edges configuration: if the two edges of
length `a` share a vertex, then `a < √(2 + √3)`. -/
theorem k2_adj_nec {p : Fin 4 → E3} (hAI : AffineIndependent ℝ p) {a : ℝ}
    {i j k l : Fin 4} (hinj : Function.Injective ![i, j, k, l])
    (hik : dist (p i) (p k) = a) (hil : dist (p i) (p l) = a)
    (hij : dist (p i) (p j) = 1) (hjk : dist (p j) (p k) = 1)
    (hjl : dist (p j) (p l) = 1) (hkl : dist (p k) (p l) = 1) :
    a < Real.sqrt (2 + Real.sqrt 3) := by
  have ha0 : 0 ≤ a := by rw [← hik]; exact dist_nonneg
  have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hjM : dist (p j) (midpoint ℝ (p k) (p l)) = Real.sqrt 3 / 2 := by
    have h : dist (p j) (midpoint ℝ (p k) (p l)) ^ 2 = 3 / 4 := by
      rw [apollonius, hjk, hjl, hkl]
      ring
    rw [← Real.sqrt_sq dist_nonneg, h, Real.sqrt_div (by norm_num : (0:ℝ) ≤ 3),
      show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  have hiM2 : dist (p i) (midpoint ℝ (p k) (p l)) ^ 2 = a ^ 2 - 1 / 4 := by
    rw [apollonius, hik, hil, hkl]
    ring
  have hiM : dist (p i) (midpoint ℝ (p k) (p l)) = Real.sqrt (a ^ 2 - 1 / 4) := by
    rw [← Real.sqrt_sq dist_nonneg, hiM2]
  have hb := hinge_left (A := p i) (B := p j) (C := p k) (D := p l) (ai_comp hAI hinj)
  rw [hiM, hij, hjM] at hb
  have ha2 : a ^ 2 < 2 + Real.sqrt 3 := by
    have hu2 : (Real.sqrt (a^2 - 1/4)) ^ 2 = a^2 - 1/4 :=
      Real.sq_sqrt (by rw [← hiM2]; positivity)
    have hnn : 0 ≤ 1 + Real.sqrt 3 / 2 := by positivity
    have hsq : (Real.sqrt (a^2-1/4))^2 < (1 + Real.sqrt 3 / 2)^2 := by
      nlinarith [hb, Real.sqrt_nonneg (a^2-1/4), hnn]
    nlinarith [hsq, hu2, h3]
  exact (Real.lt_sqrt ha0).mpr ha2


/-- Sufficiency for `k = 2` in the opposite configuration: if `0 < a < √2`,
there is a tetrahedron whose edges `(0,1)` and `(2,3)` have length `a`. -/
theorem k2_suff_opp {a : ℝ} (ha0 : 0 < a) (h2 : a < Real.sqrt 2) : HasTetra 2 a := by
  have ha2 : a ^ 2 < 2 := (Real.lt_sqrt ha0.le).mp h2
  set ρ := Real.sqrt (1 - a^2/4) with hρ
  set c := 1 - a^2 / (2 - a^2/2) with hc
  set s := Real.sqrt (1 - c^2) with hs
  have hρ2 : ρ^2 = 1 - a^2/4 := by rw [hρ]; exact Real.sq_sqrt (by nlinarith [ha2])
  have hρpos : 0 < ρ := by rw [hρ]; exact Real.sqrt_pos_of_pos (by nlinarith [ha2])
  have hdpos : (0:ℝ) < 2 - a^2/2 := by nlinarith [ha2]
  have hd0 : (2:ℝ) - a^2/2 ≠ 0 := hdpos.ne'
  have hc1 : c < 1 := by
    rw [hc]
    have hdiv : (0:ℝ) < a^2 / (2 - a^2/2) := div_pos (by positivity) hdpos
    linarith
  have hc2 : (-1:ℝ) < c := by
    rw [hc]
    have hdiv : a^2 / (2 - a^2/2) < 2 := by
      rw [div_lt_iff₀ hdpos]
      nlinarith [ha2]
    linarith
  have h1cs : (0:ℝ) < 1 - c^2 := by
    nlinarith [mul_pos (sub_pos.mpr hc1) (show (0:ℝ) < c + 1 by linarith)]
  have hs2 : s^2 = 1 - c^2 := by rw [hs]; exact Real.sq_sqrt h1cs.le
  have hspos : 0 < s := by rw [hs]; exact Real.sqrt_pos_of_pos h1cs
  have hkey : ρ^2 * ((1-c)^2 + s^2) = a^2 := by
    have h1c : 1 - c = a^2 / (2 - a^2/2) := by rw [hc]; ring
    have hA : (1-c)^2 + s^2 = 2 * (1 - c) := by rw [hs2]; ring
    rw [hA, h1c, hρ2, ← mul_div_assoc, ← mul_div_assoc,
      show (1 - a^2/4) * (2 * a^2) = (2 - a^2/2) * a^2 by ring,
      mul_div_cancel_left₀ _ hd0]
  have e01 : dist (!₂[(0:ℝ), 0, 0] : E3) (!₂[a, 0, 0] : E3) = a := by
    rw [dist3, show ((0:ℝ) - a)^2 + ((0:ℝ) - 0)^2 + ((0:ℝ) - 0)^2 = a^2 by ring,
      Real.sqrt_sq ha0.le]
  have e23 : dist (!₂[a/2, ρ, (0:ℝ)] : E3) (!₂[a/2, ρ*c, ρ*s] : E3) = a := by
    have e : (a/2 - a/2)^2 + (ρ - ρ*c)^2 + ((0:ℝ) - ρ*s)^2
        = ρ^2 * ((1-c)^2 + s^2) := by ring
    rw [dist3, e, hkey, Real.sqrt_sq ha0.le]
  have e02 : dist (!₂[(0:ℝ), 0, 0] : E3) (!₂[a/2, ρ, (0:ℝ)] : E3) = 1 := by
    rw [dist3, show ((0:ℝ) - a/2)^2 + ((0:ℝ) - ρ)^2 + ((0:ℝ) - 0)^2 = 1 by
      nlinarith only [hρ2], Real.sqrt_one]
  have e03 : dist (!₂[(0:ℝ), 0, 0] : E3) (!₂[a/2, ρ*c, ρ*s] : E3) = 1 := by
    have e1 : ((0:ℝ) - a/2)^2 + ((0:ℝ) - ρ*c)^2 + ((0:ℝ) - ρ*s)^2
        = a^2/4 + ρ^2*(c^2 + s^2) := by ring
    have e2 : ((0:ℝ) - a/2)^2 + ((0:ℝ) - ρ*c)^2 + ((0:ℝ) - ρ*s)^2 = 1 := by
      rw [e1, hs2, hρ2]; ring
    rw [dist3, e2, Real.sqrt_one]
  have e12 : dist (!₂[a, 0, 0] : E3) (!₂[a/2, ρ, (0:ℝ)] : E3) = 1 := by
    rw [dist3, show (a - a/2)^2 + ((0:ℝ) - ρ)^2 + ((0:ℝ) - 0)^2 = 1 by
      nlinarith only [hρ2], Real.sqrt_one]
  have e13 : dist (!₂[a, 0, 0] : E3) (!₂[a/2, ρ*c, ρ*s] : E3) = 1 := by
    have e1 : (a - a/2)^2 + ((0:ℝ) - ρ*c)^2 + ((0:ℝ) - ρ*s)^2
        = a^2/4 + ρ^2*(c^2 + s^2) := by ring
    have e2 : (a - a/2)^2 + ((0:ℝ) - ρ*c)^2 + ((0:ℝ) - ρ*s)^2 = 1 := by
      rw [e1, hs2, hρ2]; ring
    rw [dist3, e2, Real.sqrt_one]
  refine ⟨![!₂[(0:ℝ), 0, 0], !₂[a, 0, 0], !₂[a/2, ρ, (0:ℝ)], !₂[a/2, ρ*c, ρ*s]],
    ai_triangular ha0.ne' hρpos.ne' (mul_ne_zero hρpos.ne' hspos.ne'),
    {(0, 1), (2, 3)}, ?_, by decide, ?_, ?_⟩
  · intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl <;> decide
  · intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact e01
    · exact e23
  · intro e he
    have hcompl : tetraEdges \ {(0, 1), (2, 3)}
        = {(0, 2), (0, 3), (1, 2), (1, 3)} := by decide
    rw [hcompl] at he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact e02
    · exact e03
    · exact e12
    · exact e13

/-- Sufficiency for `k = 2` in the adjacent configuration: if
`√2 ≤ a < √(2 + √3)`, there is a tetrahedron whose edges `(0,3)` and `(1,3)`
have length `a`. -/
theorem k2_suff_adj {a : ℝ} (ha0 : 0 < a) (hub : a < Real.sqrt (2 + Real.sqrt 3))
    (h2 : Real.sqrt 2 ≤ a) : HasTetra 2 a := by
  have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs3 : 0 < Real.sqrt 3 := Real.sqrt_pos_of_pos (by norm_num)
  have hub2 : a ^ 2 < 2 + Real.sqrt 3 := (Real.lt_sqrt ha0.le).mp hub
  have ha2ge : (2:ℝ) ≤ a^2 := (Real.sqrt_le_left ha0.le).mp h2
  set r := Real.sqrt (a^2 - 1/4) with hr
  set c := (a^2 - 1/2) / (Real.sqrt 3 * r) with hc
  set s := Real.sqrt (1 - c^2) with hs
  have hr2 : r^2 = a^2 - 1/4 := by rw [hr]; exact Real.sq_sqrt (by nlinarith [ha2ge])
  have hrpos : 0 < r := by rw [hr]; exact Real.sqrt_pos_of_pos (by nlinarith [ha2ge])
  have hcr : Real.sqrt 3 * r ≠ 0 := mul_ne_zero hs3.ne' hrpos.ne'
  have hrc : Real.sqrt 3 * r * c = a^2 - 1/2 := by
    rw [hc, ← mul_div_assoc, mul_div_cancel_left₀ _ hcr]
  have hquad : (a^2)^2 - 4*a^2 + 1 < 0 := by
    have g1 : (0:ℝ) < a^2 - (2 - Real.sqrt 3) := by nlinarith [ha2ge, hs3]
    have g2 : a^2 - (2 + Real.sqrt 3) < 0 := by linarith [hub2]
    have hprod : (a^2 - (2 - Real.sqrt 3)) * (a^2 - (2 + Real.sqrt 3)) < 0 :=
      mul_neg_of_pos_of_neg g1 g2
    nlinarith [hprod, h3]
  have hc2lt : c^2 < 1 := by
    have hc2' : c^2 = (a^2 - 1/2)^2 / (3 * (a^2 - 1/4)) := by
      rw [hc, div_pow, mul_pow, h3, hr2]
    rw [hc2', div_lt_one (by nlinarith [ha2ge] : (0:ℝ) < 3 * (a^2 - 1/4))]
    nlinarith [hquad]
  have h1cs : (0:ℝ) < 1 - c^2 := by linarith [hc2lt]
  have hs2 : s^2 = 1 - c^2 := by rw [hs]; exact Real.sq_sqrt h1cs.le
  have hspos : 0 < s := by rw [hs]; exact Real.sqrt_pos_of_pos h1cs
  have e03i : ((0:ℝ) - 1/2)^2 + ((0:ℝ) - r*c)^2 + ((0:ℝ) - r*s)^2 = a^2 := by
    have e1 : ((0:ℝ) - 1/2)^2 + ((0:ℝ) - r*c)^2 + ((0:ℝ) - r*s)^2
        = 1/4 + r^2*(c^2 + s^2) := by ring
    rw [e1, hs2, hr2]; ring
  have e03 : dist (!₂[(0:ℝ), 0, 0] : E3) (!₂[1/2, r*c, r*s] : E3) = a := by
    rw [dist3, e03i, Real.sqrt_sq ha0.le]
  have e13i : ((1:ℝ) - 1/2)^2 + ((0:ℝ) - r*c)^2 + ((0:ℝ) - r*s)^2 = a^2 := by
    have e1 : ((1:ℝ) - 1/2)^2 + ((0:ℝ) - r*c)^2 + ((0:ℝ) - r*s)^2
        = 1/4 + r^2*(c^2 + s^2) := by ring
    rw [e1, hs2, hr2]; ring
  have e13 : dist (!₂[(1:ℝ), 0, 0] : E3) (!₂[1/2, r*c, r*s] : E3) = a := by
    rw [dist3, e13i, Real.sqrt_sq ha0.le]
  have e01 : dist (!₂[(0:ℝ), 0, 0] : E3) (!₂[(1:ℝ), 0, 0] : E3) = 1 := by
    rw [dist3, show ((0:ℝ) - 1)^2 + ((0:ℝ) - 0)^2 + ((0:ℝ) - 0)^2 = 1 by norm_num,
      Real.sqrt_one]
  have e02 : dist (!₂[(0:ℝ), 0, 0] : E3) (!₂[1/2, Real.sqrt 3/2, 0] : E3) = 1 := by
    rw [dist3, show ((0:ℝ) - 1/2)^2 + ((0:ℝ) - Real.sqrt 3/2)^2 + ((0:ℝ) - 0)^2 = 1 by
      nlinarith only [h3], Real.sqrt_one]
  have e12 : dist (!₂[(1:ℝ), 0, 0] : E3) (!₂[1/2, Real.sqrt 3/2, 0] : E3) = 1 := by
    rw [dist3, show ((1:ℝ) - 1/2)^2 + ((0:ℝ) - Real.sqrt 3/2)^2 + ((0:ℝ) - 0)^2 = 1 by
      nlinarith only [h3], Real.sqrt_one]
  have e23i : ((1:ℝ)/2 - 1/2)^2 + (Real.sqrt 3/2 - r*c)^2 + ((0:ℝ) - r*s)^2 = 1 := by
    have e1 : ((1:ℝ)/2 - 1/2)^2 + (Real.sqrt 3/2 - r*c)^2 + ((0:ℝ) - r*s)^2
        = 3/4 - Real.sqrt 3 * r * c + r^2*(c^2 + s^2) := by nlinarith only [h3]
    rw [e1, hrc, hs2, hr2]; ring
  have e23 : dist (!₂[1/2, Real.sqrt 3/2, 0] : E3) (!₂[1/2, r*c, r*s] : E3) = 1 := by
    rw [dist3, e23i, Real.sqrt_one]
  refine ⟨![!₂[(0:ℝ), 0, 0], !₂[(1:ℝ), 0, 0], !₂[1/2, Real.sqrt 3/2, 0],
      !₂[1/2, r*c, r*s]],
    ai_triangular one_ne_zero (div_ne_zero hs3.ne' (by norm_num))
      (mul_ne_zero hrpos.ne' hspos.ne'),
    {(0, 3), (1, 3)}, ?_, by decide, ?_, ?_⟩
  · intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl <;> decide
  · intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact e03
    · exact e13
  · intro e he
    have hcompl : tetraEdges \ {(0, 3), (1, 3)}
        = {(0, 1), (0, 2), (1, 2), (2, 3)} := by decide
    rw [hcompl] at he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact e01
    · exact e02
    · exact e12
    · exact e23

/-- The `k = 2` case of IMO 1969 problem 3. -/
theorem hasTetra_two (a : ℝ) :
    HasTetra 2 a ↔ 0 < a ∧ a < Real.sqrt (2 + Real.sqrt 3) := by
  constructor
  · rintro ⟨p, hAI, s, hsub, hcard, hdist_a, hdist_1⟩
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
    have hx_mem : x ∈ tetraEdges := hsub (Finset.mem_insert_self x {y})
    have hy_mem : y ∈ tetraEdges := hsub
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self y))
    obtain ⟨x1, x2⟩ := x
    obtain ⟨y1, y2⟩ := y
    have hx12 : x1 < x2 := by
      have h := hx_mem
      simp only [tetraEdges, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
        and_true, true_and] at h
      exact h
    have hy12 : y1 < y2 := by
      have h := hy_mem
      simp only [tetraEdges, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
        and_true, true_and] at h
      exact h
    have hax : dist (p x1) (p x2) = a := hdist_a (x1, x2) (Finset.mem_insert_self _ _)
    have hay : dist (p y1) (p y2) = a :=
      hdist_a (y1, y2) (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have ha0 : 0 < a := by
      have hne : p x1 ≠ p x2 := fun hh => (ne_of_lt hx12) (hAI.injective hh)
      rw [← hax]
      exact dist_pos.mpr hne
    have hsqrt2_le : Real.sqrt 2 ≤ Real.sqrt (2 + Real.sqrt 3) :=
      Real.sqrt_le_sqrt (le_add_of_nonneg_right (Real.sqrt_nonneg 3))
    refine ⟨ha0, ?_⟩
    have hx_cases : (x1 = 0 ∧ x2 = 1) ∨ (x1 = 0 ∧ x2 = 2) ∨ (x1 = 0 ∧ x2 = 3) ∨
        (x1 = 1 ∧ x2 = 2) ∨ (x1 = 1 ∧ x2 = 3) ∨ (x1 = 2 ∧ x2 = 3) := by
      fin_cases x1 <;> fin_cases x2 <;> first
        | exact absurd hx12 (by decide)
        | decide
    have hy_cases : (y1 = 0 ∧ y2 = 1) ∨ (y1 = 0 ∧ y2 = 2) ∨ (y1 = 0 ∧ y2 = 3) ∨
        (y1 = 1 ∧ y2 = 2) ∨ (y1 = 1 ∧ y2 = 3) ∨ (y1 = 2 ∧ y2 = 3) := by
      fin_cases y1 <;> fin_cases y2 <;> first
        | exact absurd hy12 (by decide)
        | decide
    rcases hx_cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        | ⟨rfl, rfl⟩ <;>
      rcases hy_cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        | ⟨rfl, rfl⟩
    · exact absurd rfl hxy
    · exact k2_adj_nec hAI (by decide : Function.Injective (![0, 3, 1, 2] : Fin 4 → Fin 4))
        hax hay (hdist_1 (0, 3) (by decide))
        ((dist_comm _ _).trans (hdist_1 (1, 3) (by decide)))
        ((dist_comm _ _).trans (hdist_1 (2, 3) (by decide))) (hdist_1 (1, 2) (by decide))
    · exact k2_adj_nec hAI (by decide : Function.Injective (![0, 2, 1, 3] : Fin 4 → Fin 4))
        hax hay (hdist_1 (0, 2) (by decide))
        ((dist_comm _ _).trans (hdist_1 (1, 2) (by decide))) (hdist_1 (2, 3) (by decide))
        (hdist_1 (1, 3) (by decide))
    · exact k2_adj_nec hAI (by decide : Function.Injective (![1, 3, 0, 2] : Fin 4 → Fin 4))
        ((dist_comm _ _).trans hax) hay (hdist_1 (1, 3) (by decide))
        ((dist_comm _ _).trans (hdist_1 (0, 3) (by decide)))
        ((dist_comm _ _).trans (hdist_1 (2, 3) (by decide))) (hdist_1 (0, 2) (by decide))
    · exact k2_adj_nec hAI (by decide : Function.Injective (![1, 2, 0, 3] : Fin 4 → Fin 4))
        ((dist_comm _ _).trans hax) hay (hdist_1 (1, 2) (by decide))
        ((dist_comm _ _).trans (hdist_1 (0, 2) (by decide))) (hdist_1 (2, 3) (by decide))
        (hdist_1 (0, 3) (by decide))
    · exact lt_of_lt_of_le
        (k2_opp_nec hAI (by decide : Function.Injective (![0, 1, 2, 3] : Fin 4 → Fin 4))
          hax hay (hdist_1 (0, 2) (by decide)) (hdist_1 (0, 3) (by decide))
          (hdist_1 (1, 2) (by decide)) (hdist_1 (1, 3) (by decide)))
        hsqrt2_le
    · exact k2_adj_nec hAI (by decide : Function.Injective (![0, 3, 2, 1] : Fin 4 → Fin 4))
        hax hay (hdist_1 (0, 3) (by decide))
        ((dist_comm _ _).trans (hdist_1 (2, 3) (by decide)))
        ((dist_comm _ _).trans (hdist_1 (1, 3) (by decide)))
        ((dist_comm _ _).trans (hdist_1 (1, 2) (by decide)))
    · exact absurd rfl hxy
    · exact k2_adj_nec hAI (by decide : Function.Injective (![0, 1, 2, 3] : Fin 4 → Fin 4))
        hax hay (hdist_1 (0, 1) (by decide)) (hdist_1 (1, 2) (by decide))
        (hdist_1 (1, 3) (by decide)) (hdist_1 (2, 3) (by decide))
    · exact k2_adj_nec hAI (by decide : Function.Injective (![2, 3, 0, 1] : Fin 4 → Fin 4))
        ((dist_comm _ _).trans hax) ((dist_comm _ _).trans hay)
        (hdist_1 (2, 3) (by decide))
        ((dist_comm _ _).trans (hdist_1 (0, 3) (by decide)))
        ((dist_comm _ _).trans (hdist_1 (1, 3) (by decide))) (hdist_1 (0, 1) (by decide))
    · exact lt_of_lt_of_le
        (k2_opp_nec hAI (by decide : Function.Injective (![0, 2, 1, 3] : Fin 4 → Fin 4))
          hax hay (hdist_1 (0, 1) (by decide)) (hdist_1 (0, 3) (by decide))
          ((dist_comm _ _).trans (hdist_1 (1, 2) (by decide))) (hdist_1 (2, 3) (by decide)))
        hsqrt2_le
    · exact k2_adj_nec hAI (by decide : Function.Injective (![2, 1, 0, 3] : Fin 4 → Fin 4))
        ((dist_comm _ _).trans hax) hay
        ((dist_comm _ _).trans (hdist_1 (1, 2) (by decide)))
        ((dist_comm _ _).trans (hdist_1 (0, 1) (by decide))) (hdist_1 (1, 3) (by decide))
        (hdist_1 (0, 3) (by decide))
    · exact k2_adj_nec hAI (by decide : Function.Injective (![0, 2, 3, 1] : Fin 4 → Fin 4))
        hax hay (hdist_1 (0, 2) (by decide)) (hdist_1 (2, 3) (by decide))
        ((dist_comm _ _).trans (hdist_1 (1, 2) (by decide)))
        ((dist_comm _ _).trans (hdist_1 (1, 3) (by decide)))
    · exact k2_adj_nec hAI (by decide : Function.Injective (![0, 1, 3, 2] : Fin 4 → Fin 4))
        hax hay (hdist_1 (0, 1) (by decide)) (hdist_1 (1, 3) (by decide))
        (hdist_1 (1, 2) (by decide))
        ((dist_comm _ _).trans (hdist_1 (2, 3) (by decide)))
    · exact absurd rfl hxy
    · exact lt_of_lt_of_le
        (k2_opp_nec hAI (by decide : Function.Injective (![0, 3, 1, 2] : Fin 4 → Fin 4))
          hax hay (hdist_1 (0, 1) (by decide)) (hdist_1 (0, 2) (by decide))
          ((dist_comm _ _).trans (hdist_1 (1, 3) (by decide)))
          ((dist_comm _ _).trans (hdist_1 (2, 3) (by decide))))
        hsqrt2_le
    · exact k2_adj_nec hAI (by decide : Function.Injective (![3, 2, 0, 1] : Fin 4 → Fin 4))
        ((dist_comm _ _).trans hax) ((dist_comm _ _).trans hay)
        ((dist_comm _ _).trans (hdist_1 (2, 3) (by decide)))
        ((dist_comm _ _).trans (hdist_1 (0, 2) (by decide)))
        ((dist_comm _ _).trans (hdist_1 (1, 2) (by decide))) (hdist_1 (0, 1) (by decide))
    · exact k2_adj_nec hAI (by decide : Function.Injective (![3, 1, 0, 2] : Fin 4 → Fin 4))
        ((dist_comm _ _).trans hax) ((dist_comm _ _).trans hay)
        ((dist_comm _ _).trans (hdist_1 (1, 3) (by decide)))
        ((dist_comm _ _).trans (hdist_1 (0, 1) (by decide))) (hdist_1 (1, 2) (by decide))
        (hdist_1 (0, 2) (by decide))
    · exact k2_adj_nec hAI (by decide : Function.Injective (![1, 3, 2, 0] : Fin 4 → Fin 4))
        hax ((dist_comm _ _).trans hay) (hdist_1 (1, 3) (by decide))
        ((dist_comm _ _).trans (hdist_1 (2, 3) (by decide)))
        ((dist_comm _ _).trans (hdist_1 (0, 3) (by decide)))
        ((dist_comm _ _).trans (hdist_1 (0, 2) (by decide)))
    · exact k2_adj_nec hAI (by decide : Function.Injective (![2, 3, 1, 0] : Fin 4 → Fin 4))
        ((dist_comm _ _).trans hax) ((dist_comm _ _).trans hay)
        (hdist_1 (2, 3) (by decide))
        ((dist_comm _ _).trans (hdist_1 (1, 3) (by decide)))
        ((dist_comm _ _).trans (hdist_1 (0, 3) (by decide)))
        ((dist_comm _ _).trans (hdist_1 (0, 1) (by decide)))
    · exact lt_of_lt_of_le
        (k2_opp_nec hAI (by decide : Function.Injective (![1, 2, 0, 3] : Fin 4 → Fin 4))
          hax hay ((dist_comm _ _).trans (hdist_1 (0, 1) (by decide)))
          (hdist_1 (1, 3) (by decide))
          ((dist_comm _ _).trans (hdist_1 (0, 2) (by decide))) (hdist_1 (2, 3) (by decide)))
        hsqrt2_le
    · exact absurd rfl hxy
    · exact k2_adj_nec hAI (by decide : Function.Injective (![1, 0, 2, 3] : Fin 4 → Fin 4))
        hax hay ((dist_comm _ _).trans (hdist_1 (0, 1) (by decide)))
        (hdist_1 (0, 2) (by decide)) (hdist_1 (0, 3) (by decide))
        (hdist_1 (2, 3) (by decide))
    · exact k2_adj_nec hAI (by decide : Function.Injective (![2, 0, 1, 3] : Fin 4 → Fin 4))
        ((dist_comm _ _).trans hax) hay
        ((dist_comm _ _).trans (hdist_1 (0, 2) (by decide))) (hdist_1 (0, 1) (by decide))
        (hdist_1 (0, 3) (by decide)) (hdist_1 (1, 3) (by decide))
    · exact k2_adj_nec hAI (by decide : Function.Injective (![1, 2, 3, 0] : Fin 4 → Fin 4))
        hax ((dist_comm _ _).trans hay) (hdist_1 (1, 2) (by decide))
        (hdist_1 (2, 3) (by decide))
        ((dist_comm _ _).trans (hdist_1 (0, 2) (by decide)))
        ((dist_comm _ _).trans (hdist_1 (0, 3) (by decide)))
    · exact lt_of_lt_of_le
        (k2_opp_nec hAI (by decide : Function.Injective (![1, 3, 0, 2] : Fin 4 → Fin 4))
          hax hay ((dist_comm _ _).trans (hdist_1 (0, 1) (by decide)))
          (hdist_1 (1, 2) (by decide))
          ((dist_comm _ _).trans (hdist_1 (0, 3) (by decide)))
          ((dist_comm _ _).trans (hdist_1 (2, 3) (by decide))))
        hsqrt2_le
    · exact k2_adj_nec hAI (by decide : Function.Injective (![3, 2, 1, 0] : Fin 4 → Fin 4))
        ((dist_comm _ _).trans hax) ((dist_comm _ _).trans hay)
        ((dist_comm _ _).trans (hdist_1 (2, 3) (by decide)))
        ((dist_comm _ _).trans (hdist_1 (1, 2) (by decide)))
        ((dist_comm _ _).trans (hdist_1 (0, 2) (by decide)))
        ((dist_comm _ _).trans (hdist_1 (0, 1) (by decide)))
    · exact k2_adj_nec hAI (by decide : Function.Injective (![1, 0, 3, 2] : Fin 4 → Fin 4))
        hax hay ((dist_comm _ _).trans (hdist_1 (0, 1) (by decide)))
        (hdist_1 (0, 3) (by decide)) (hdist_1 (0, 2) (by decide))
        ((dist_comm _ _).trans (hdist_1 (2, 3) (by decide)))
    · exact absurd rfl hxy
    · exact k2_adj_nec hAI (by decide : Function.Injective (![3, 0, 1, 2] : Fin 4 → Fin 4))
        ((dist_comm _ _).trans hax) ((dist_comm _ _).trans hay)
        ((dist_comm _ _).trans (hdist_1 (0, 3) (by decide))) (hdist_1 (0, 1) (by decide))
        (hdist_1 (0, 2) (by decide)) (hdist_1 (1, 2) (by decide))
    · exact lt_of_lt_of_le
        (k2_opp_nec hAI (by decide : Function.Injective (![2, 3, 0, 1] : Fin 4 → Fin 4))
          hax hay ((dist_comm _ _).trans (hdist_1 (0, 2) (by decide)))
          ((dist_comm _ _).trans (hdist_1 (1, 2) (by decide)))
          ((dist_comm _ _).trans (hdist_1 (0, 3) (by decide)))
          ((dist_comm _ _).trans (hdist_1 (1, 3) (by decide))))
        hsqrt2_le
    · exact k2_adj_nec hAI (by decide : Function.Injective (![2, 1, 3, 0] : Fin 4 → Fin 4))
        hax ((dist_comm _ _).trans hay)
        ((dist_comm _ _).trans (hdist_1 (1, 2) (by decide))) (hdist_1 (1, 3) (by decide))
        ((dist_comm _ _).trans (hdist_1 (0, 1) (by decide)))
        ((dist_comm _ _).trans (hdist_1 (0, 3) (by decide)))
    · exact k2_adj_nec hAI (by decide : Function.Injective (![3, 1, 2, 0] : Fin 4 → Fin 4))
        ((dist_comm _ _).trans hax) ((dist_comm _ _).trans hay)
        ((dist_comm _ _).trans (hdist_1 (1, 3) (by decide))) (hdist_1 (1, 2) (by decide))
        ((dist_comm _ _).trans (hdist_1 (0, 1) (by decide)))
        ((dist_comm _ _).trans (hdist_1 (0, 2) (by decide)))
    · exact k2_adj_nec hAI (by decide : Function.Injective (![2, 0, 3, 1] : Fin 4 → Fin 4))
        hax ((dist_comm _ _).trans hay)
        ((dist_comm _ _).trans (hdist_1 (0, 2) (by decide))) (hdist_1 (0, 3) (by decide))
        (hdist_1 (0, 1) (by decide))
        ((dist_comm _ _).trans (hdist_1 (1, 3) (by decide)))
    · exact k2_adj_nec hAI (by decide : Function.Injective (![3, 0, 2, 1] : Fin 4 → Fin 4))
        ((dist_comm _ _).trans hax) ((dist_comm _ _).trans hay)
        ((dist_comm _ _).trans (hdist_1 (0, 3) (by decide))) (hdist_1 (0, 2) (by decide))
        (hdist_1 (0, 1) (by decide))
        ((dist_comm _ _).trans (hdist_1 (1, 2) (by decide)))
    · exact absurd rfl hxy
  · rintro ⟨ha0, hub⟩
    rcases lt_or_ge a (Real.sqrt 2) with h2 | h2
    · exact k2_suff_opp ha0 h2
    · exact k2_suff_adj ha0 hub h2

theorem hasTetra_three (a : ℝ) : HasTetra 3 a ↔ 0 < a := by
  constructor
  · rintro ⟨p, hAI, s, hsub, hcard, ha, -⟩
    have hne : s.Nonempty := Finset.card_pos.mp (hcard ▸ by norm_num)
    obtain ⟨e, he⟩ := hne
    have he_a : dist (p e.1) (p e.2) = a := ha e he
    have hlt_e : e.1 < e.2 := by
      have h := hsub he
      rw [tetraEdges, Finset.mem_filter] at h
      exact h.2
    rw [← he_a]
    exact dist_pos.mpr (hAI.injective.ne (ne_of_lt hlt_e))
  · intro ha
    have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have h32 : (0:ℝ) < Real.sqrt 3 / 2 := by positivity
    rcases le_total a 1 with h | h
    · -- case `a ≤ 1`: the three edges of length `a` form a triangle
      have ha21 : a ^ 2 ≤ 1 := by nlinarith [ha, h]
      have hpos : (0:ℝ) < 1 - a ^ 2 / 3 := by nlinarith
      set hgt : ℝ := Real.sqrt (1 - a ^ 2 / 3) with hh
      have hh_pos : 0 < hgt := hh ▸ Real.sqrt_pos.mpr hpos
      have hh2 : hgt ^ 2 = 1 - a ^ 2 / 3 := hh ▸ Real.sq_sqrt hpos.le
      refine ⟨![(!₂[0, 0, 0] : E3), !₂[a, 0, 0], !₂[a/2, a * Real.sqrt 3 / 2, 0],
          !₂[a/2, a * Real.sqrt 3 / 6, hgt]], ?_, {(0, 1), (0, 2), (1, 2)},
        ?_, ?_, ?_, ?_⟩
      · exact ai_triangular ha.ne'
          (div_ne_zero (mul_ne_zero ha.ne' (ne_of_gt (by positivity))) (by norm_num))
          (ne_of_gt hh_pos)
      · intro e he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl | rfl <;> decide
      · decide
      · intro e he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl | rfl
        · show dist (!₂[0, 0, 0] : E3) !₂[a, 0, 0] = a
          rw [dist3]
          have hin : (0 - a : ℝ) ^ 2 + (0 - 0) ^ 2 + (0 - 0) ^ 2 = a ^ 2 := by ring
          rw [hin]
          exact Real.sqrt_sq ha.le
        · show dist (!₂[0, 0, 0] : E3) !₂[a/2, a * Real.sqrt 3 / 2, 0] = a
          rw [dist3]
          have hin : (0 - a/2 : ℝ) ^ 2 + (0 - a * Real.sqrt 3 / 2) ^ 2 + (0 - 0) ^ 2
              = a ^ 2 := by
            nlinarith [h3]
          rw [hin]
          exact Real.sqrt_sq ha.le
        · show dist (!₂[a, 0, 0] : E3) !₂[a/2, a * Real.sqrt 3 / 2, 0] = a
          rw [dist3]
          have hin : (a - a/2 : ℝ) ^ 2 + (0 - a * Real.sqrt 3 / 2) ^ 2 + (0 - 0) ^ 2
              = a ^ 2 := by
            nlinarith [h3]
          rw [hin]
          exact Real.sqrt_sq ha.le
      · have hsd : tetraEdges \ ({(0, 1), (0, 2), (1, 2)} : Finset (Fin 4 × Fin 4))
            = {(0, 3), (1, 3), (2, 3)} := by
          decide
        rw [hsd]
        intro e he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl | rfl
        · show dist (!₂[0, 0, 0] : E3) !₂[a/2, a * Real.sqrt 3 / 6, hgt] = 1
          rw [dist3]
          have hin : (0 - a/2 : ℝ) ^ 2 + (0 - a * Real.sqrt 3 / 6) ^ 2 + (0 - hgt) ^ 2
              = 1 := by
            nlinarith [h3, hh2]
          rw [hin]
          exact Real.sqrt_one
        · show dist (!₂[a, 0, 0] : E3) !₂[a/2, a * Real.sqrt 3 / 6, hgt] = 1
          rw [dist3]
          have hin : (a - a/2 : ℝ) ^ 2 + (0 - a * Real.sqrt 3 / 6) ^ 2 + (0 - hgt) ^ 2
              = 1 := by
            nlinarith [h3, hh2]
          rw [hin]
          exact Real.sqrt_one
        · show dist (!₂[a/2, a * Real.sqrt 3 / 2, 0] : E3)
              !₂[a/2, a * Real.sqrt 3 / 6, hgt] = 1
          rw [dist3]
          have hin : (a/2 - a/2 : ℝ) ^ 2 + (a * Real.sqrt 3 / 2 - a * Real.sqrt 3 / 6) ^ 2
              + (0 - hgt) ^ 2 = 1 := by
            nlinarith [h3, hh2]
          rw [hin]
          exact Real.sqrt_one
    · -- case `a ≥ 1`: the three edges of length `a` join a unit triangle to the apex
      have h1a : (1:ℝ) ≤ a ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr h) ha.le]
      have hpos : (0:ℝ) < a ^ 2 - 1 / 3 := by nlinarith
      set hgt : ℝ := Real.sqrt (a ^ 2 - 1 / 3) with hh
      have hh_pos : 0 < hgt := hh ▸ Real.sqrt_pos.mpr hpos
      have hh2 : hgt ^ 2 = a ^ 2 - 1 / 3 := hh ▸ Real.sq_sqrt hpos.le
      refine ⟨![(!₂[0, 0, 0] : E3), !₂[1, 0, 0], !₂[1/2, Real.sqrt 3 / 2, 0],
          !₂[1/2, Real.sqrt 3 / 6, hgt]], ?_, {(0, 3), (1, 3), (2, 3)},
        ?_, ?_, ?_, ?_⟩
      · exact ai_triangular one_ne_zero (ne_of_gt h32) (ne_of_gt hh_pos)
      · intro e he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl | rfl <;> decide
      · decide
      · intro e he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl | rfl
        · show dist (!₂[0, 0, 0] : E3) !₂[1/2, Real.sqrt 3 / 6, hgt] = a
          rw [dist3]
          have hin : (0 - 1/2 : ℝ) ^ 2 + (0 - Real.sqrt 3 / 6) ^ 2 + (0 - hgt) ^ 2
              = a ^ 2 := by
            nlinarith [h3, hh2]
          rw [hin]
          exact Real.sqrt_sq ha.le
        · show dist (!₂[1, 0, 0] : E3) !₂[1/2, Real.sqrt 3 / 6, hgt] = a
          rw [dist3]
          have hin : (1 - 1/2 : ℝ) ^ 2 + (0 - Real.sqrt 3 / 6) ^ 2 + (0 - hgt) ^ 2
              = a ^ 2 := by
            nlinarith [h3, hh2]
          rw [hin]
          exact Real.sqrt_sq ha.le
        · show dist (!₂[1/2, Real.sqrt 3 / 2, 0] : E3) !₂[1/2, Real.sqrt 3 / 6, hgt] = a
          rw [dist3]
          have hin : (1/2 - 1/2 : ℝ) ^ 2 + (Real.sqrt 3 / 2 - Real.sqrt 3 / 6) ^ 2
              + (0 - hgt) ^ 2 = a ^ 2 := by
            nlinarith [h3, hh2]
          rw [hin]
          exact Real.sqrt_sq ha.le
      · have hsd : tetraEdges \ ({(0, 3), (1, 3), (2, 3)} : Finset (Fin 4 × Fin 4))
            = {(0, 1), (0, 2), (1, 2)} := by
          decide
        rw [hsd]
        intro e he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl | rfl
        · show dist (!₂[0, 0, 0] : E3) !₂[1, 0, 0] = 1
          rw [dist3]
          have hin : (0 - 1 : ℝ) ^ 2 + (0 - 0) ^ 2 + (0 - 0) ^ 2 = 1 := by ring
          rw [hin]
          exact Real.sqrt_one
        · show dist (!₂[0, 0, 0] : E3) !₂[1/2, Real.sqrt 3 / 2, 0] = 1
          rw [dist3]
          have hin : (0 - 1/2 : ℝ) ^ 2 + (0 - Real.sqrt 3 / 2) ^ 2 + (0 - 0) ^ 2 = 1 := by
            nlinarith [h3]
          rw [hin]
          exact Real.sqrt_one
        · show dist (!₂[1, 0, 0] : E3) !₂[1/2, Real.sqrt 3 / 2, 0] = 1
          rw [dist3]
          have hin : (1 - 1/2 : ℝ) ^ 2 + (0 - Real.sqrt 3 / 2) ^ 2 + (0 - 0) ^ 2 = 1 := by
            nlinarith [h3]
          rw [hin]
          exact Real.sqrt_one

theorem hasTetra_four (a : ℝ) : HasTetra 4 a ↔ Real.sqrt (2 - Real.sqrt 3) < a := by
  have h2m3 : (0 : ℝ) < 2 - Real.sqrt 3 := by
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have hle : Real.sqrt 3 < 2 := by
      rw [← h4]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  have hkey : Real.sqrt (2 - Real.sqrt 3) * Real.sqrt (2 + Real.sqrt 3) = 1 := by
    rw [← Real.sqrt_mul h2m3.le,
      show (2 - Real.sqrt 3) * (2 + Real.sqrt 3) = 1 by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)],
      Real.sqrt_one]
  by_cases ha : 0 < a
  · have h1 : HasTetra 4 a ↔ HasTetra 2 (1 / a) := by
      have hpos : (0 : ℝ) < 1 / a := by positivity
      have h := hasTetra_dual (k := 2) (by norm_num) hpos
      rwa [show (6 : ℕ) - 2 = 4 by norm_num, one_div_one_div] at h
    rw [h1, hasTetra_two]
    have hsp : (0 : ℝ) < Real.sqrt (2 + Real.sqrt 3) := by positivity
    constructor
    · rintro ⟨-, h2⟩
      rw [div_lt_iff₀ ha] at h2
      have h4 : Real.sqrt (2 + Real.sqrt 3) * Real.sqrt (2 - Real.sqrt 3)
          < Real.sqrt (2 + Real.sqrt 3) * a := by
        rw [mul_comm (Real.sqrt (2 + Real.sqrt 3)) _, hkey]
        exact h2
      exact (mul_lt_mul_iff_right₀ hsp).mp h4
    · intro h
      refine ⟨by positivity, ?_⟩
      rw [div_lt_iff₀ ha]
      have h4 := (mul_lt_mul_iff_right₀ hsp).mpr h
      rw [mul_comm (Real.sqrt (2 + Real.sqrt 3)) _, hkey] at h4
      exact h4
  · exact ⟨fun h => absurd (hasTetra_pos (by norm_num : (0 : ℕ) < 4) h) ha,
      fun h => by linarith [le_of_not_gt ha, Real.sqrt_pos.mpr h2m3]⟩

theorem hasTetra_five (a : ℝ) : HasTetra 5 a ↔ 1 / Real.sqrt 3 < a := by
  have hs3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  by_cases ha : 0 < a
  · have h1 : HasTetra 5 a ↔ HasTetra 1 (1 / a) := by
      have hpos : (0 : ℝ) < 1 / a := by positivity
      have h := hasTetra_dual (k := 1) (by norm_num) hpos
      rwa [show (6 : ℕ) - 1 = 5 by norm_num, one_div_one_div] at h
    rw [h1, hasTetra_one]
    constructor
    · rintro ⟨-, h2⟩
      rw [div_lt_iff₀ ha] at h2
      rw [div_lt_iff₀ hs3]
      rwa [mul_comm]
    · intro h
      refine ⟨by positivity, ?_⟩
      rw [div_lt_iff₀ ha]
      rw [div_lt_iff₀ hs3] at h
      rwa [mul_comm] at h
  · exact ⟨fun h => absurd (hasTetra_pos (by norm_num : (0 : ℕ) < 5) h) ha,
      fun h => by
        have hpos : (0 : ℝ) < 1 / Real.sqrt 3 := by positivity
        linarith [le_of_not_gt ha]⟩

snip end

problem imo1969_p3 (k : ℕ) (hk : k ∈ Finset.Icc 1 5) (a : ℝ) :
    HasTetra k a ↔ a ∈ answer k := by
  fin_cases hk
  · exact hasTetra_one a
  · exact hasTetra_two a
  · exact hasTetra_three a
  · exact hasTetra_four a
  · exact hasTetra_five a

end Imo1969P3
