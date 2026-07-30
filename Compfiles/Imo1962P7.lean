/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Analysis.Convex.StrictConvexBetween
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Real.Basic
public import Mathlib.Geometry.Euclidean.Sphere.Basic
public import Mathlib.Geometry.Euclidean.Sphere.OrthRadius
public import Mathlib.Geometry.Euclidean.Sphere.Tangent
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1962, Problem 7

The tetrahedron SABC has the following property: there exist five spheres,
each of which is tangent to the edges SA, SB, SC, CA, CB, AB or their
extensions.

(a) Prove that the tetrahedron SABC is regular.
(b) Prove conversely that for every regular tetrahedron five such spheres
    exist.
-/

namespace Imo1962P7

open EuclideanGeometry RealInnerProductSpace

/-- The ambient space: three-dimensional Euclidean space. -/
abbrev Pt := EuclideanSpace ℝ (Fin 3)

/-- A sphere that is tangent to the six extended edges of the tetrahedron with
vertices `A`: it is tangent to each of the six lines through two vertices. -/
def TangentToEdges (A : Fin 4 → Pt) (s : Sphere Pt) : Prop :=
  0 < s.radius ∧ ∀ i j : Fin 4, i ≠ j → ∃ T : Pt, s.IsTangentAt T (line[ℝ, A i, A j])

snip begin

/-- The length of a tangent from the vertex `A i` to the sphere `s`.
This is well-defined (independent of the chosen edge through `A i`) and equals
the distance from `A i` to any tangency point on a line through `A i`. -/
noncomputable def tanLen (A : Fin 4 → Pt) (s : Sphere Pt) (i : Fin 4) : ℝ :=
  Real.sqrt (dist (A i) s.center ^ 2 - s.radius ^ 2)

/-- A tangent sphere of "insphere type": every tangency point lies on the edge
segment itself, so every edge length is the sum of the two tangent lengths. -/
def InsphereType (A : Fin 4 → Pt) (s : Sphere Pt) : Prop :=
  ∀ i j : Fin 4, i ≠ j → dist (A i) (A j) = tanLen A s i + tanLen A s j

/-- A tangent sphere of "escribed type at vertex `k`": the tangency points on the
three edges through `k` lie beyond the other endpoints, while the tangency
points on the three edges of the opposite face lie on the segments. -/
def EscribedType (A : Fin 4 → Pt) (s : Sphere Pt) (k : Fin 4) : Prop :=
  (∀ j : Fin 4, j ≠ k → dist (A k) (A j) = tanLen A s k - tanLen A s j) ∧
  (∀ i j : Fin 4, i ≠ k → j ≠ k → i ≠ j → dist (A i) (A j) = tanLen A s i + tanLen A s j)

/-! ### Geometric interface lemmas -/

/-- The tangent length from `A i` equals the distance from `A i` to the
tangency point on any edge-line through `A i` (Pythagoras). -/
lemma tanLen_eq_dist {A : Fin 4 → Pt} {s : Sphere Pt} {i j : Fin 4} (_hij : i ≠ j)
    {T : Pt} (hT : s.IsTangentAt T (line[ℝ, A i, A j])) :
    tanLen A s i = dist (A i) T := by
  have h := hT.dist_sq_eq_of_mem (left_mem_affineSpan_pair ℝ (A i) (A j))
  unfold tanLen
  rw [h, add_sub_cancel_left, Real.sqrt_sq dist_nonneg]

/-- For each edge, its length is either the sum or a difference of the two
tangent lengths (the tangency point is between the vertices or outside). -/
lemma edge_trichotomy {A : Fin 4 → Pt} {s : Sphere Pt} (hs : TangentToEdges A s)
    {i j : Fin 4} (hij : i ≠ j) (_hAij : A i ≠ A j) :
    dist (A i) (A j) = tanLen A s i + tanLen A s j ∨
    dist (A i) (A j) = tanLen A s i - tanLen A s j ∨
    dist (A i) (A j) = tanLen A s j - tanLen A s i := by
  obtain ⟨T, hT⟩ := hs.2 i j hij
  have hT' : s.IsTangentAt T (line[ℝ, A j, A i]) := by
    rwa [AffineSubspace.affineSpan_pair_comm] at hT
  have hti : tanLen A s i = dist (A i) T := tanLen_eq_dist hij hT
  have htj : tanLen A s j = dist (A j) T := tanLen_eq_dist (Ne.symm hij) hT'
  have hcol : Collinear ℝ ({T, A i, A j} : Set Pt) :=
    collinear_insert_of_mem_affineSpan_pair hT.mem_space
  rcases hcol.wbtw_or_wbtw_or_wbtw with hw | hw | hw
  · -- `T` weakly between `A i` and `A j`: `dist (A i) (A j) = t j - t i`.
    refine Or.inr (Or.inr ?_)
    rw [hti, htj]
    have h := hw.dist_add_dist
    rw [dist_comm T (A i), dist_comm T (A j)] at h
    linarith
  · -- `A j` weakly between `A i` and `T`: `dist (A i) (A j) = t i - t j`.
    refine Or.inr (Or.inl ?_)
    rw [hti, htj]
    have h := hw.dist_add_dist
    linarith
  · -- `A i` weakly between `A j` and `T`: `dist (A i) (A j) = t i + t j`.
    refine Or.inl ?_
    rw [hti, htj]
    have h := hw.dist_add_dist
    rw [dist_comm (A j) (A i), dist_comm T (A i)] at h
    linarith

/-- The inner product of the vector from `A i` to the center with an edge
direction is determined by the tangent lengths: it is `± t_i * L`, with the
negative sign exactly when the tangency point lies on the ray opposite to
`A j` (the `L = t_j - t_i` case). -/
lemma center_inner_eq {A : Fin 4 → Pt} {s : Sphere Pt} (hs : TangentToEdges A s)
    {i j : Fin 4} (hij : i ≠ j) (hAij : A i ≠ A j) :
    ⟪s.center - A i, A j - A i⟫ =
      (if dist (A i) (A j) = tanLen A s j - tanLen A s i
       then -tanLen A s i else tanLen A s i) * dist (A i) (A j) := by
  obtain ⟨T, hT⟩ := hs.2 i j hij
  have hT' : s.IsTangentAt T (line[ℝ, A j, A i]) := by
    rwa [AffineSubspace.affineSpan_pair_comm] at hT
  -- Parameterize the tangency point on the edge line: `T = A i + c • (A j - A i)`.
  obtain ⟨c, hc⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.1 hT.mem_space
  have hTeq : T = A i + c • (A j - A i) := by
    rw [← hc, AffineMap.lineMap_apply_module']; abel
  have hL : 0 < dist (A i) (A j) := dist_pos.2 hAij
  -- The radius to the tangency point is orthogonal to the edge direction.
  have h1 := hT.inner_left_eq_zero_of_mem (left_mem_affineSpan_pair ℝ (A i) (A j))
  have h2 := hT.inner_left_eq_zero_of_mem (right_mem_affineSpan_pair ℝ (A i) (A j))
  simp only [vsub_eq_sub] at h1 h2
  have horth : ⟪A j - A i, T - s.center⟫ = 0 := by
    have h3 := inner_sub_left (𝕜 := ℝ) (A j - T) (A i - T) (T - s.center)
    rw [sub_sub_sub_cancel_right, h2, h1, sub_zero] at h3
    exact h3
  have hv : T - s.center = c • (A j - A i) - (s.center - A i) := by
    rw [hTeq]; abel
  rw [hv, inner_sub_right, real_inner_smul_right,
    real_inner_comm (s.center - A i) (A j - A i)] at horth
  have hnorm : ⟪A j - A i, A j - A i⟫ = dist (A i) (A j) ^ 2 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm (A j) (A i), dist_comm (A j) (A i)]
  have hkey : ⟪s.center - A i, A j - A i⟫ = c * dist (A i) (A j) ^ 2 := by
    rw [← hnorm]
    linarith [horth]
  -- Distances from the vertices to the tangency point, in terms of `c`.
  have hAiT : A i - T = -(c • (A j - A i)) := by rw [hTeq]; abel
  have hdTi : dist (A i) T = |c| * dist (A i) (A j) := by
    rw [dist_eq_norm (A i) T, hAiT, norm_neg, norm_smul, Real.norm_eq_abs,
      ← dist_eq_norm (A j) (A i), dist_comm (A j) (A i)]
  have hAjT : A j - T = (1 - c) • (A j - A i) := by
    rw [hTeq, sub_smul, one_smul]; abel
  have hdTj : dist (A j) T = |1 - c| * dist (A i) (A j) := by
    rw [dist_eq_norm (A j) T, hAjT, norm_smul, Real.norm_eq_abs,
      ← dist_eq_norm (A j) (A i), dist_comm (A j) (A i)]
  have hti' : tanLen A s i = |c| * dist (A i) (A j) := (tanLen_eq_dist hij hT).trans hdTi
  have htj' : tanLen A s j = |1 - c| * dist (A i) (A j) :=
    (tanLen_eq_dist (Ne.symm hij) hT').trans hdTj
  -- Cancel one factor of `dist (A i) (A j)` and resolve the sign of `c`.
  rw [hkey, pow_two, ← mul_assoc]
  refine congrArg (· * dist (A i) (A j)) ?_
  split_ifs with hcond
  · -- Here `|1 - c| = 1 + |c|`, forcing `c ≤ 0`.
    have hc0 : c ≤ 0 := by
      rcases abs_cases c with ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩ <;>
        rcases abs_cases (1 - c) with ⟨hc3, hc4⟩ | ⟨hc3, hc4⟩ <;>
        rw [hc1] at hti' <;> rw [hc3] at htj' <;> nlinarith only [hti', htj', hcond, hL, hc2, hc4]
    rw [abs_of_nonpos hc0] at hti'
    linarith [hti']
  · -- Otherwise `edge_trichotomy` gives `|c| + |1 - c| = 1` or `|c| - |1 - c| = 1`,
    -- both forcing `0 ≤ c`.
    have htc := edge_trichotomy hs hij hAij
    have hc0 : 0 ≤ c := by
      rcases htc with h1 | h2 | h3
      · rcases abs_cases c with ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩ <;>
          rcases abs_cases (1 - c) with ⟨hc3, hc4⟩ | ⟨hc3, hc4⟩ <;>
          rw [hc1] at hti' <;> rw [hc3] at htj' <;> nlinarith only [hti', htj', h1, hL, hc2, hc4]
      · rcases abs_cases c with ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩ <;>
          rcases abs_cases (1 - c) with ⟨hc3, hc4⟩ | ⟨hc3, hc4⟩ <;>
          rw [hc1] at hti' <;> rw [hc3] at htj' <;> nlinarith only [hti', htj', h2, hL, hc2, hc4]
      · exact absurd h3 hcond
    rw [abs_of_nonneg hc0] at hti'
    linarith [hti']

/-- In a non-degenerate tetrahedron, a vector orthogonal to the three edge
directions from a vertex is zero. -/
lemma eq_of_inner_vsub_eq_zero {A : Fin 4 → Pt} (hA : AffineIndependent ℝ A) {x : Pt}
    (h : ∀ j : Fin 4, j ≠ 0 → ⟪x, A j - A 0⟫ = 0) : x = 0 := by
  have hli : LinearIndependent ℝ (fun i : {j : Fin 4 // j ≠ 0} => (A i -ᵥ A 0 : Pt)) :=
    (affineIndependent_iff_linearIndependent_vsub ℝ A 0).1 hA
  have hcard : Fintype.card {j : Fin 4 // j ≠ 0} = Module.finrank ℝ Pt := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin,
      finrank_euclideanSpace_fin]
  have hspan : Submodule.span ℝ
      (Set.range (fun i : {j : Fin 4 // j ≠ 0} => (A i -ᵥ A 0 : Pt))) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' hcard
  have hxorth : x ∈ (⊤ : Submodule ℝ Pt)ᗮ := by
    rw [← hspan, Submodule.mem_orthogonal']
    intro v hv
    induction hv using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        exact h j j.2
    | zero => exact inner_zero_right x
    | add y z _ _ ihy ihz => rw [inner_add_right, ihy, ihz, add_zero]
    | smul a y _ ihy => rw [real_inner_smul_right, ihy, mul_zero]
  rw [Submodule.top_orthogonal_eq_bot] at hxorth
  exact (Submodule.mem_bot ℝ).1 hxorth

/-- Vertices of a non-degenerate tetrahedron are distinct. -/
lemma ne_of_affineIndependent {A : Fin 4 → Pt} (hA : AffineIndependent ℝ A) {i j : Fin 4}
    (hij : i ≠ j) : A i ≠ A j :=
  fun h => hij (hA.injective h)

/-- Strict triangle inequality on each face of a non-degenerate tetrahedron. -/
lemma face_dist_lt {A : Fin 4 → Pt} (hA : AffineIndependent ℝ A) {i j k : Fin 4}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    dist (A i) (A k) < dist (A i) (A j) + dist (A j) (A k) := by
  rw [dist_lt_dist_add_dist_iff]
  intro hw
  have hcol : Collinear ℝ ({A i, A j, A k} : Set Pt) := hw.collinear
  have hinj : Function.Injective ![i, j, k] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  have hA' : AffineIndependent ℝ (A ∘ ![i, j, k]) := hA.comp_embedding ⟨![i, j, k], hinj⟩
  have hA'' : AffineIndependent ℝ ![A i, A j, A k] := by
    have hfun : (A ∘ ![i, j, k]) = ![A i, A j, A k] := by
      funext m
      fin_cases m <;> rfl
    rwa [hfun] at hA'
  have hncol : ¬ Collinear ℝ ({A i, A j, A k} : Set Pt) :=
    affineIndependent_iff_not_collinear_set.1 hA''
  exact hncol hcol

/-- A tangent sphere is determined by its tangent lengths: two tangent spheres
with the same tangent lengths at all four vertices coincide. -/
lemma sphere_eq_of_tanLen_eq {A : Fin 4 → Pt} (hA : AffineIndependent ℝ A)
    {s₁ s₂ : Sphere Pt} (hs₁ : TangentToEdges A s₁) (hs₂ : TangentToEdges A s₂)
    (ht : ∀ i : Fin 4, tanLen A s₁ i = tanLen A s₂ i) : s₁ = s₂ := by
  -- The centers agree: their difference is orthogonal to every edge direction from `A 0`.
  have hcenter : s₁.center = s₂.center := by
    have hz : ∀ j : Fin 4, j ≠ 0 → ⟪s₁.center - s₂.center, A j - A 0⟫ = 0 := by
      intro j hj
      have hj0 : (0 : Fin 4) ≠ j := Ne.symm hj
      have hA0j : A 0 ≠ A j := ne_of_affineIndependent hA hj0
      have e1 := center_inner_eq hs₁ hj0 hA0j
      have e2 := center_inner_eq hs₂ hj0 hA0j
      simp only [ht] at e1
      rw [show s₁.center - s₂.center = s₁.center - A 0 - (s₂.center - A 0) by abel,
        inner_sub_left, e1, e2, sub_self]
    exact sub_eq_zero.1 (eq_of_inner_vsub_eq_zero hA hz)
  -- The radii agree: `radius ^ 2 = dist (A 0) center ^ 2 - tanLen 0 ^ 2` for both.
  have hradius : s₁.radius = s₂.radius := by
    have h01 : (0 : Fin 4) ≠ 1 := by decide
    obtain ⟨T₁, hT₁⟩ := hs₁.2 0 1 h01
    obtain ⟨T₂, hT₂⟩ := hs₂.2 0 1 h01
    have e₁ : s₁.radius ^ 2 = dist (A 0) s₁.center ^ 2 - tanLen A s₁ 0 ^ 2 := by
      have hd := hT₁.dist_sq_eq_of_mem (left_mem_affineSpan_pair ℝ (A 0) (A 1))
      have hnn : 0 ≤ dist (A 0) s₁.center ^ 2 - s₁.radius ^ 2 := by
        rw [hd, add_sub_cancel_left]; exact sq_nonneg _
      unfold tanLen
      rw [Real.sq_sqrt hnn, hd]; ring
    have e₂ : s₂.radius ^ 2 = dist (A 0) s₂.center ^ 2 - tanLen A s₂ 0 ^ 2 := by
      have hd := hT₂.dist_sq_eq_of_mem (left_mem_affineSpan_pair ℝ (A 0) (A 1))
      have hnn : 0 ≤ dist (A 0) s₂.center ^ 2 - s₂.radius ^ 2 := by
        rw [hd, add_sub_cancel_left]; exact sq_nonneg _
      unfold tanLen
      rw [Real.sq_sqrt hnn, hd]; ring
    rw [hcenter, ht 0] at e₁
    have hsq : s₁.radius ^ 2 = s₂.radius ^ 2 := e₁.trans e₂.symm
    exact (sq_eq_sq₀ hs₁.1.le hs₂.1.le).1 hsq
  exact Sphere.ext_iff.2 ⟨hcenter, hradius⟩

/-! ### Combinatorial core: classification of tangent-length patterns -/

/-- Pick a third index different from two given ones. -/
lemma fin4_exists_ne_ne {i j : Fin 4} : ∃ k : Fin 4, k ≠ i ∧ k ≠ j := by
  fin_cases i <;> fin_cases j <;> first
    | exact ⟨0, by decide, by decide⟩ | exact ⟨1, by decide, by decide⟩
    | exact ⟨2, by decide, by decide⟩

/-- Pick a fourth index different from three given ones. -/
lemma fin4_exists_ne_ne_ne {i j k : Fin 4} : ∃ l : Fin 4, l ≠ i ∧ l ≠ j ∧ l ≠ k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> first
    | exact ⟨0, by decide, by decide, by decide⟩
    | exact ⟨1, by decide, by decide, by decide⟩
    | exact ⟨2, by decide, by decide, by decide⟩
    | exact ⟨3, by decide, by decide, by decide⟩

/-- Four pairwise distinct indices exhaust `Fin 4`. -/
lemma fin4_cover {i j k l : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) (x : Fin 4) :
    x = i ∨ x = j ∨ x = k ∨ x = l := by
  have hcard : ({i, j, k, l} : Finset (Fin 4)).card = 4 := by
    rw [Finset.card_insert_of_notMem ?_, Finset.card_insert_of_notMem ?_,
      Finset.card_insert_of_notMem ?_, Finset.card_singleton]
    · simp only [Finset.mem_singleton]
      exact hkl
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hjk, hjl⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hij, hik, hil⟩
  have huniv : ({i, j, k, l} : Finset (Fin 4)) = Finset.univ :=
    Finset.eq_univ_of_card _ (by simpa using hcard)
  have hx : x ∈ ({i, j, k, l} : Finset (Fin 4)) := by
    rw [huniv]
    exact Finset.mem_univ x
  simpa [Finset.mem_insert, Finset.mem_singleton] using hx

/-- Classification of one face: either all three edges are sums of tangent
lengths, or there is a distinguished vertex whose two edges are differences. -/
lemma face_classify {t : Fin 4 → ℝ} (ht : ∀ i, 0 ≤ t i) {L : Fin 4 → Fin 4 → ℝ}
    (hL : ∀ i j, i ≠ j → 0 < L i j)
    (hsym : ∀ i j, L i j = L j i)
    (htri : ∀ i j k, i ≠ j → j ≠ k → i ≠ k → L i k < L i j + L j k)
    (h : ∀ i j, i ≠ j → L i j = t i + t j ∨ L i j = t i - t j ∨ L i j = t j - t i)
    {i j k : Fin 4} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (L i j = t i + t j ∧ L i k = t i + t k ∧ L j k = t j + t k) ∨
    (L i j = t i - t j ∧ L i k = t i - t k ∧ L j k = t j + t k) ∨
    (L j i = t j - t i ∧ L j k = t j - t k ∧ L i k = t i + t k) ∨
    (L k i = t k - t i ∧ L k j = t k - t j ∧ L i j = t i + t j) := by
  obtain e1|e1|e1 := h i j hij <;>
  obtain e2|e2|e2 := h i k hik <;>
  obtain e3|e3|e3 := h j k hjk <;>
  first
  | (exact Or.inl ⟨e1, e2, e3⟩)
  | (exact Or.inr (Or.inl ⟨e1, e2, e3⟩))
  | (exact Or.inr (Or.inr (Or.inl ⟨(hsym j i).trans e1, e3, e2⟩)))
  | (exact Or.inr (Or.inr (Or.inr ⟨(hsym k i).trans e2, (hsym k j).trans e3, e1⟩)))
  | (exfalso; linarith [ht i, ht j, ht k, hL i j hij, hL i k hik, hL j k hjk,
      htri i j k hij hjk hik, htri i k j hik hjk.symm hij, htri j i k hij.symm hik hjk,
      hsym i j, hsym i k, hsym j k, hsym j i, hsym k i, hsym k j])

/-- Global classification: a valid tangent-length pattern on the tetrahedron is
either the insphere pattern or the escribed pattern at a unique vertex. -/
lemma classify {t : Fin 4 → ℝ} (ht : ∀ i, 0 ≤ t i) {L : Fin 4 → Fin 4 → ℝ}
    (hL : ∀ i j, i ≠ j → 0 < L i j)
    (hsym : ∀ i j, L i j = L j i)
    (htri : ∀ i j k, i ≠ j → j ≠ k → i ≠ k → L i k < L i j + L j k)
    (h : ∀ i j, i ≠ j → L i j = t i + t j ∨ L i j = t i - t j ∨ L i j = t j - t i) :
    (∀ i j, i ≠ j → L i j = t i + t j) ∨
    ∃ k, (∀ j, j ≠ k → L k j = t k - t j) ∧
         (∀ i j, i ≠ k → j ≠ k → i ≠ j → L i j = t i + t j) := by
  by_cases hall : ∀ i j, i ≠ j → L i j = t i + t j
  · exact Or.inl hall
  push Not at hall
  obtain ⟨i, j, hij, hdij⟩ := hall
  obtain ⟨k, hki, hkj⟩ := fin4_exists_ne_ne
  obtain ⟨l, hli, hlj, hlk⟩ := fin4_exists_ne_ne_ne
  obtain f1 := face_classify ht hL hsym htri h hij hkj.symm hki.symm
  obtain f2 := face_classify ht hL hsym htri h hij hlj.symm hli.symm
  rcases f1 with f1|f1|f1|f1
  · exact absurd f1.1 hdij
  · -- face (i,j,k) special at `i`
    rcases f2 with f2|f2|f2|f2
    · exact absurd f2.1 hdij
    · -- face (i,j,l) special at `i`: star at `i`
      refine Or.inr ⟨i, fun j' hj' ↦ ?_, fun a b ha hb hab ↦ ?_⟩
      · rcases fin4_cover hij hki.symm hli.symm hkj.symm hlj.symm hlk.symm j' with rfl|rfl|rfl|rfl
        · exact (hj' rfl).elim
        · exact f1.1
        · exact f1.2.1
        · exact f2.2.1
      · have hkl' : L k l = t k + t l := by
          obtain g|g|g|g := face_classify ht hL hsym htri h hki.symm hlk.symm hli.symm
          · exact g.2.2
          · exact g.2.2
          · exfalso; linarith [g.1, f1.2.1, hsym k i, hL i k hki.symm]
          · exfalso; linarith [g.1, f2.2.1, hsym l i, hL i l hli.symm]
        rcases fin4_cover hij hki.symm hli.symm hkj.symm hlj.symm hlk.symm a with rfl|rfl|rfl|rfl
        · exact (ha rfl).elim
        · rcases fin4_cover hij hki.symm hli.symm hkj.symm hlj.symm hlk.symm b with rfl|rfl|rfl|rfl
          · exact (hb rfl).elim
          · exact (hab rfl).elim
          · exact f1.2.2
          · exact f2.2.2
        · rcases fin4_cover hij hki.symm hli.symm hkj.symm hlj.symm hlk.symm b with rfl|rfl|rfl|rfl
          · exact (hb rfl).elim
          · linarith [f1.2.2, hsym a b]
          · exact (hab rfl).elim
          · exact hkl'
        · rcases fin4_cover hij hki.symm hli.symm hkj.symm hlj.symm hlk.symm b with rfl|rfl|rfl|rfl
          · exact (hb rfl).elim
          · linarith [f2.2.2, hsym a b]
          · linarith [hkl', hsym a b]
          · exact (hab rfl).elim
    · -- face (i,j,l) special at `j`: contradiction
      exfalso
      linarith [f1.1, f2.1, hsym j i, hL i j hij]
    · exact absurd f2.2.2 hdij
  · -- face (i,j,k) special at `j`
    rcases f2 with f2|f2|f2|f2
    · exact absurd f2.1 hdij
    · -- face (i,j,l) special at `i`: contradiction
      exfalso
      linarith [f1.1, f2.1, hsym j i, hL i j hij]
    · -- face (i,j,l) special at `j`: star at `j`
      refine Or.inr ⟨j, fun j' hj' ↦ ?_, fun a b ha hb hab ↦ ?_⟩
      · rcases fin4_cover hij.symm hkj.symm hlj.symm hki.symm hli.symm hlk.symm j' with rfl|rfl|rfl|rfl
        · exact (hj' rfl).elim
        · exact f1.1
        · exact f1.2.1
        · exact f2.2.1
      · have hkl' : L k l = t k + t l := by
          obtain g|g|g|g := face_classify ht hL hsym htri h hkj.symm hlk.symm hlj.symm
          · exact g.2.2
          · exact g.2.2
          · exfalso; linarith [g.1, f1.2.1, hsym k j, hL j k hkj.symm]
          · exfalso; linarith [g.1, f2.2.1, hsym l j, hL j l hlj.symm]
        rcases fin4_cover hij.symm hkj.symm hlj.symm hki.symm hli.symm hlk.symm a with rfl|rfl|rfl|rfl
        · exact (ha rfl).elim
        · rcases fin4_cover hij.symm hkj.symm hlj.symm hki.symm hli.symm hlk.symm b with rfl|rfl|rfl|rfl
          · exact (hb rfl).elim
          · exact (hab rfl).elim
          · exact f1.2.2
          · exact f2.2.2
        · rcases fin4_cover hij.symm hkj.symm hlj.symm hki.symm hli.symm hlk.symm b with rfl|rfl|rfl|rfl
          · exact (hb rfl).elim
          · linarith [f1.2.2, hsym a b]
          · exact (hab rfl).elim
          · exact hkl'
        · rcases fin4_cover hij.symm hkj.symm hlj.symm hki.symm hli.symm hlk.symm b with rfl|rfl|rfl|rfl
          · exact (hb rfl).elim
          · linarith [f2.2.2, hsym a b]
          · linarith [hkl', hsym a b]
          · exact (hab rfl).elim
    · exact absurd f2.2.2 hdij
  · exact absurd f1.2.2 hdij

/-- Every tangent sphere is of insphere type or of escribed type at some vertex. -/
lemma type_of_sphere {A : Fin 4 → Pt} (hA : AffineIndependent ℝ A)
    {s : Sphere Pt} (hs : TangentToEdges A s) :
    InsphereType A s ∨ ∃ k : Fin 4, EscribedType A s k := by
  have hne : ∀ i j : Fin 4, i ≠ j → A i ≠ A j := fun i j hij ↦ ne_of_affineIndependent hA hij
  have hcl := classify (t := tanLen A s) (L := fun i j ↦ dist (A i) (A j))
    (fun i ↦ Real.sqrt_nonneg _)
    (fun i j hij ↦ dist_pos.mpr (hne i j hij))
    (fun i j ↦ dist_comm (A i) (A j))
    (fun i j k hij hjk hik ↦ face_dist_lt hA hij hjk hik)
    (fun i j hij ↦ edge_trichotomy hs hij (hne i j hij))
  rcases hcl with hcl | ⟨k, hk1, hk2⟩
  · exact Or.inl hcl
  · exact Or.inr ⟨k, hk1, hk2⟩

/-- Tangent lengths of an insphere-type sphere are determined by the edge
lengths. -/
lemma tanLen_eq_of_insphere {A : Fin 4 → Pt} {s₁ s₂ : Sphere Pt}
    (h₁ : InsphereType A s₁) (h₂ : InsphereType A s₂) (i : Fin 4) :
    tanLen A s₁ i = tanLen A s₂ i := by
  obtain ⟨j, hji⟩ := exists_ne i
  obtain ⟨k, hki, hkj⟩ := fin4_exists_ne_ne
  have e1 := h₁ i j hji.symm
  have e2 := h₁ i k hki.symm
  have e3 := h₁ j k hkj.symm
  have f1 := h₂ i j hji.symm
  have f2 := h₂ i k hki.symm
  have f3 := h₂ j k hkj.symm
  linarith

/-- Tangent lengths of an escribed-type sphere at `k` are determined by the
edge lengths. -/
lemma tanLen_eq_of_escribed {A : Fin 4 → Pt} {s₁ s₂ : Sphere Pt} {k : Fin 4}
    (h₁ : EscribedType A s₁ k) (h₂ : EscribedType A s₂ k) (i : Fin 4) :
    tanLen A s₁ i = tanLen A s₂ i := by
  have side : ∀ j : Fin 4, j ≠ k → tanLen A s₁ j = tanLen A s₂ j := by
    intro j hjk
    obtain ⟨l, hlj, hlk⟩ : ∃ l : Fin 4, l ≠ j ∧ l ≠ k := fin4_exists_ne_ne
    obtain ⟨m, hmj, hml, hmk⟩ : ∃ m : Fin 4, m ≠ j ∧ m ≠ l ∧ m ≠ k := fin4_exists_ne_ne_ne
    have e1 := h₁.2 j l hjk hlk hlj.symm
    have e2 := h₁.2 j m hjk hmk hmj.symm
    have e3 := h₁.2 l m hlk hmk hml.symm
    have f1 := h₂.2 j l hjk hlk hlj.symm
    have f2 := h₂.2 j m hjk hmk hmj.symm
    have f3 := h₂.2 l m hlk hmk hml.symm
    linarith
  by_cases hi : i = k
  · rw [hi]
    obtain ⟨j, hjk⟩ := exists_ne k
    have e1 := h₁.1 j hjk
    have e2 := h₂.1 j hjk
    have e3 := side j hjk
    linarith
  · exact side i hi

/-- The type map of five distinct tangent spheres covers all five possible
types: the insphere type and the four escribed types. -/
lemma type_cover {A : Fin 4 → Pt} (hA : AffineIndependent ℝ A)
    (S : Fin 5 → Sphere Pt) (hinj : Function.Injective S)
    (hT : ∀ k, TangentToEdges A (S k)) :
    (∃ k, InsphereType A (S k)) ∧ ∀ m : Fin 4, ∃ k, EscribedType A (S k) m := by
  classical
  have key : ∀ k : Fin 5, ∃ o : Option (Fin 4),
      (o = none ∧ InsphereType A (S k)) ∨ ∃ m, o = some m ∧ EscribedType A (S k) m := by
    intro k
    rcases type_of_sphere hA (hT k) with h | ⟨m, h⟩
    · exact ⟨none, Or.inl ⟨rfl, h⟩⟩
    · exact ⟨some m, Or.inr ⟨m, rfl, h⟩⟩
  choose τ hτ using key
  have hτinj : Function.Injective τ := by
    intro a b hab
    rcases hτ a with ⟨ha, hAa⟩ | ⟨ma, ha, hAa⟩ <;>
    rcases hτ b with ⟨hb, hBb⟩ | ⟨mb, hb, hBb⟩
    · exact hinj (sphere_eq_of_tanLen_eq hA (hT a) (hT b)
        (fun i ↦ tanLen_eq_of_insphere hAa hBb i))
    · exfalso; rw [ha, hb] at hab; simp at hab
    · exfalso; rw [ha, hb] at hab; simp at hab
    · rw [ha, hb] at hab
      obtain rfl : ma = mb := Option.some.inj hab
      exact hinj (sphere_eq_of_tanLen_eq hA (hT a) (hT b)
        (fun i ↦ tanLen_eq_of_escribed hAa hBb i))
  have hτsurj : Function.Surjective τ :=
    (Finite.injective_iff_surjective_of_equiv (finSuccEquiv' 0)).mp hτinj
  constructor
  · obtain ⟨k, hk⟩ := hτsurj none
    rcases hτ k with ⟨hkn, hkin⟩ | ⟨m', hkm, hke⟩
    · exact ⟨k, hkin⟩
    · rw [hkm] at hk; simp at hk
  · intro m
    obtain ⟨k, hk⟩ := hτsurj (some m)
    rcases hτ k with ⟨hkn, hkin⟩ | ⟨m', hkm, hke⟩
    · rw [hkn] at hk; simp at hk
    · rw [hkm] at hk
      obtain rfl : m' = m := Option.some.inj hk
      exact ⟨k, hke⟩

/-- Among five distinct tangent spheres, one is of insphere type. -/
lemma exists_insphere {A : Fin 4 → Pt} (hA : AffineIndependent ℝ A)
    (S : Fin 5 → Sphere Pt) (hinj : Function.Injective S)
    (hT : ∀ k, TangentToEdges A (S k)) :
    ∃ k, InsphereType A (S k) :=
  (type_cover hA S hinj hT).1

/-- Among five distinct tangent spheres, for each vertex `m` one is escribed
at `m`. -/
lemma exists_escribed {A : Fin 4 → Pt} (hA : AffineIndependent ℝ A)
    (S : Fin 5 → Sphere Pt) (hinj : Function.Injective S)
    (hT : ∀ k, TangentToEdges A (S k)) (m : Fin 4) :
    ∃ k, EscribedType A (S k) m :=
  (type_cover hA S hinj hT).2 m

/-- Final algebra: the edge lengths of a tetrahedron admitting an insphere-type
sphere and escribed-type spheres at two distinct vertices are all equal. -/
lemma regular_of_types {A : Fin 4 → Pt} {s₀ s₁ s₂ : Sphere Pt}
    (h₀ : InsphereType A s₀)
    (h₁ : EscribedType A s₁ 0) (h₂ : EscribedType A s₂ 1) :
    ∃ s : ℝ, ∀ i j : Fin 4, i ≠ j → dist (A i) (A j) = s := by
  refine ⟨2 * tanLen A s₀ 0, fun i j hij ↦ ?_⟩
  have a01 := h₀ 0 1 (by decide); have a02 := h₀ 0 2 (by decide); have a03 := h₀ 0 3 (by decide)
  have a12 := h₀ 1 2 (by decide); have a13 := h₀ 1 3 (by decide); have a23 := h₀ 2 3 (by decide)
  have b1 := h₁.1 1 (by decide); have b2 := h₁.1 2 (by decide); have b3 := h₁.1 3 (by decide)
  have c12 := h₁.2 1 2 (by decide) (by decide) (by decide)
  have c13 := h₁.2 1 3 (by decide) (by decide) (by decide)
  have c23 := h₁.2 2 3 (by decide) (by decide) (by decide)
  have d0 := h₂.1 0 (by decide); have d2 := h₂.1 2 (by decide); have d3 := h₂.1 3 (by decide)
  have e02 := h₂.2 0 2 (by decide) (by decide) (by decide)
  have e03 := h₂.2 0 3 (by decide) (by decide) (by decide)
  have e23 := h₂.2 2 3 (by decide) (by decide) (by decide)
  have s10 : dist (A 1) (A 0) = dist (A 0) (A 1) := dist_comm _ _
  have s20 : dist (A 2) (A 0) = dist (A 0) (A 2) := dist_comm _ _
  have s30 : dist (A 3) (A 0) = dist (A 0) (A 3) := dist_comm _ _
  have s21 : dist (A 2) (A 1) = dist (A 1) (A 2) := dist_comm _ _
  have s31 : dist (A 3) (A 1) = dist (A 1) (A 3) := dist_comm _ _
  have s32 : dist (A 3) (A 2) = dist (A 2) (A 3) := dist_comm _ _
  -- the escribed sphere at `0` has the tangent lengths of the insphere on {1,2,3}
  have h11 : tanLen A s₁ 1 = tanLen A s₀ 1 := by linarith
  have h12 : tanLen A s₁ 2 = tanLen A s₀ 2 := by linarith
  have h13 : tanLen A s₁ 3 = tanLen A s₀ 3 := by linarith
  -- hence `tanLen A s₀` is constant on {1,2,3}
  have hb12 : tanLen A s₀ 1 = tanLen A s₀ 2 := by linarith
  have hb23 : tanLen A s₀ 2 = tanLen A s₀ 3 := by linarith
  -- the escribed sphere at `1` has the tangent lengths of the insphere on {0,2,3}
  have g0 : tanLen A s₂ 0 = tanLen A s₀ 0 := by linarith
  have g2 : tanLen A s₂ 2 = tanLen A s₀ 2 := by linarith
  have g3 : tanLen A s₂ 3 = tanLen A s₀ 3 := by linarith
  -- hence `tanLen A s₀ 0 = tanLen A s₀ 2`, so all tangent lengths coincide
  have hd : tanLen A s₀ 0 = tanLen A s₀ 2 := by linarith
  have key : tanLen A s₀ 0 = tanLen A s₀ 1 := by linarith
  have e01 : dist (A 0) (A 1) = 2 * tanLen A s₀ 0 := by linarith
  have e02 : dist (A 0) (A 2) = 2 * tanLen A s₀ 0 := by linarith
  have e03 : dist (A 0) (A 3) = 2 * tanLen A s₀ 0 := by linarith
  have e10 : dist (A 1) (A 0) = 2 * tanLen A s₀ 0 := by linarith
  have e12 : dist (A 1) (A 2) = 2 * tanLen A s₀ 0 := by linarith
  have e13 : dist (A 1) (A 3) = 2 * tanLen A s₀ 0 := by linarith
  have e20 : dist (A 2) (A 0) = 2 * tanLen A s₀ 0 := by linarith
  have e21 : dist (A 2) (A 1) = 2 * tanLen A s₀ 0 := by linarith
  have e23 : dist (A 2) (A 3) = 2 * tanLen A s₀ 0 := by linarith
  have e30 : dist (A 3) (A 0) = 2 * tanLen A s₀ 0 := by linarith
  have e31 : dist (A 3) (A 1) = 2 * tanLen A s₀ 0 := by linarith
  have e32 : dist (A 3) (A 2) = 2 * tanLen A s₀ 0 := by linarith
  fin_cases i <;> fin_cases j <;> (try contradiction) <;> assumption

/-- If the foot `T` on the line through `A i`, `A j` is perpendicular to the
radius from `E` and at distance `R` from `E`, then the sphere `⟨E, R⟩` is
tangent at `T` to the line through `A i`, `A j`. -/
lemma isTangentAt_of_perp {A : Fin 4 → Pt} {i j : Fin 4} {E : Pt} {R : ℝ} (hR : 0 ≤ R)
    (T : Pt) (c₀ : ℝ) (hT : T = c₀ • (A j - A i) + A i)
    (Q : ℝ) (hQ : R ^ 2 = Q)
    (hperp : ⟪T - E, A j - A i⟫ = 0)
    (hdist : ⟪T - E, T - E⟫ = Q) :
    (⟨E, R⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A i, A j]) := by
  have hperp2 : ⟪A j - A i, T - E⟫ = 0 := by
    rw [real_inner_comm]
    exact hperp
  have e1 : A i - T = -c₀ • (A j - A i) := by
    rw [hT]; module
  have e2 : A j - T = (1 - c₀) • (A j - A i) := by
    rw [hT]; module
  refine ⟨?_, ?_, ?_⟩
  · apply (sq_eq_sq₀ dist_nonneg hR).mp
    rw [dist_eq_norm, ← real_inner_self_eq_norm_sq, hdist]
    exact hQ.symm
  · rw [hT]
    exact smul_vsub_vadd_mem_affineSpan_pair c₀ (A i) (A j)
  · apply affineSpan_pair_le_of_mem_of_mem
    · rw [EuclideanGeometry.Sphere.mem_orthRadius_iff_inner_left]
      show ⟪A i - T, T - E⟫ = 0
      rw [e1, real_inner_smul_left, hperp2, mul_zero]
    · rw [EuclideanGeometry.Sphere.mem_orthRadius_iff_inner_left]
      show ⟪A j - T, T - E⟫ = 0
      rw [e2, real_inner_smul_left, hperp2, mul_zero]

/-- The insphere of a regular tetrahedron (centered at the centroid, with
radius `√(s²/8)` where `s` is the edge length) is tangent to the six extended
edges. -/
lemma insphere_tangent (A : Fin 4 → Pt) (s : ℝ)
    (hs : ∀ i j : Fin 4, i ≠ j → dist (A i) (A j) = s) (hs_pos : 0 < s) :
    TangentToEdges A ⟨A 0 + (1/4 : ℝ) • ((A 1 - A 0) + (A 2 - A 0) + (A 3 - A 0)), Real.sqrt (s ^ 2 / 8)⟩ := by
  set W1 : Pt := A 1 - A 0 with hW1
  set W2 : Pt := A 2 - A 0 with hW2
  set W3 : Pt := A 3 - A 0 with hW3
  set c : Pt := A 0 + (1/4 : ℝ) • ((A 1 - A 0) + (A 2 - A 0) + (A 3 - A 0)) with hc
  set r₀ : ℝ := Real.sqrt (s ^ 2 / 8) with hr₀
  have hvsq : ∀ j : Fin 4, j ≠ 0 → ⟪A j - A 0, A j - A 0⟫ = s ^ 2 := by
    intro j hj
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, dist_comm, hs 0 j (Ne.symm hj)]
  have hv : ∀ j k : Fin 4, j ≠ 0 → k ≠ 0 → j ≠ k → ⟪A j - A 0, A k - A 0⟫ = s ^ 2 / 2 := by
    intro j k hj hk hjk
    have h1 : ‖(A j - A 0) - (A k - A 0)‖ ^ 2 = s ^ 2 := by
      rw [sub_sub_sub_cancel_right, ← dist_eq_norm, hs j k hjk]
    rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq (A j - A 0),
      ← real_inner_self_eq_norm_sq (A k - A 0), hvsq j hj, hvsq k hk] at h1
    linarith
  have I11 : ⟪W1, W1⟫ = s ^ 2 := by rw [hW1]; exact hvsq 1 (by decide)
  have I22 : ⟪W2, W2⟫ = s ^ 2 := by rw [hW2]; exact hvsq 2 (by decide)
  have I33 : ⟪W3, W3⟫ = s ^ 2 := by rw [hW3]; exact hvsq 3 (by decide)
  have I12 : ⟪W1, W2⟫ = s ^ 2 / 2 := by
    rw [hW1, hW2]; exact hv 1 2 (by decide) (by decide) (by decide)
  have I13 : ⟪W1, W3⟫ = s ^ 2 / 2 := by
    rw [hW1, hW3]; exact hv 1 3 (by decide) (by decide) (by decide)
  have I23 : ⟪W2, W3⟫ = s ^ 2 / 2 := by
    rw [hW2, hW3]; exact hv 2 3 (by decide) (by decide) (by decide)
  have I21 : ⟪W2, W1⟫ = s ^ 2 / 2 := by rw [real_inner_comm]; exact I12
  have I31 : ⟪W3, W1⟫ = s ^ 2 / 2 := by rw [real_inner_comm]; exact I13
  have I32 : ⟪W3, W2⟫ = s ^ 2 / 2 := by rw [real_inner_comm]; exact I23
  have key : ∀ a₁ a₂ a₃ b₁ b₂ b₃ : ℝ,
      ⟪a₁ • W1 + a₂ • W2 + a₃ • W3, b₁ • W1 + b₂ • W2 + b₃ • W3⟫ =
        (a₁ * b₁ + a₂ * b₂ + a₃ * b₃) * s ^ 2 +
        (a₁ * b₂ + a₂ * b₁ + a₁ * b₃ + a₃ * b₁ + a₂ * b₃ + a₃ * b₂) * (s ^ 2 / 2) := by
    intro a₁ a₂ a₃ b₁ b₂ b₃
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
    simp only [I11, I22, I33, I12, I13, I23, I21, I31, I32]
    ring
  have hQ_in : r₀ ^ 2 = s ^ 2 / 8 := by
    rw [hr₀]
    exact Real.sq_sqrt (by positivity)
  have hr₀_pos : 0 < r₀ := by
    rw [hr₀]
    exact Real.sqrt_pos.mpr (by positivity)
  refine ⟨hr₀_pos, fun i j hij => ?_⟩
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · show ∃ T, (⟨c, r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 0, A 1])
    have hTE : ((1/2 : ℝ) • (A 1 - A 0) + A 0) - (c) = (1/4 : ℝ) • W1 + (-1/4 : ℝ) • W2 + (-1/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(1/2 : ℝ) • (A 1 - A 0) + A 0, isTangentAt_of_perp hr₀_pos.le _ (1/2 : ℝ) rfl _ hQ_in
      (by rw [hTE, show A 1 - A 0 = (1 : ℝ) • W1 + (0 : ℝ) • W2 + (0 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨c, r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 0, A 2])
    have hTE : ((1/2 : ℝ) • (A 2 - A 0) + A 0) - (c) = (-1/4 : ℝ) • W1 + (1/4 : ℝ) • W2 + (-1/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(1/2 : ℝ) • (A 2 - A 0) + A 0, isTangentAt_of_perp hr₀_pos.le _ (1/2 : ℝ) rfl _ hQ_in
      (by rw [hTE, show A 2 - A 0 = (0 : ℝ) • W1 + (1 : ℝ) • W2 + (0 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨c, r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 0, A 3])
    have hTE : ((1/2 : ℝ) • (A 3 - A 0) + A 0) - (c) = (-1/4 : ℝ) • W1 + (-1/4 : ℝ) • W2 + (1/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(1/2 : ℝ) • (A 3 - A 0) + A 0, isTangentAt_of_perp hr₀_pos.le _ (1/2 : ℝ) rfl _ hQ_in
      (by rw [hTE, show A 3 - A 0 = (0 : ℝ) • W1 + (0 : ℝ) • W2 + (1 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨c, r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 1, A 0])
    have hTE : ((1/2 : ℝ) • (A 0 - A 1) + A 1) - (c) = (1/4 : ℝ) • W1 + (-1/4 : ℝ) • W2 + (-1/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(1/2 : ℝ) • (A 0 - A 1) + A 1, isTangentAt_of_perp hr₀_pos.le _ (1/2 : ℝ) rfl _ hQ_in
      (by rw [hTE, show A 0 - A 1 = (-1 : ℝ) • W1 + (0 : ℝ) • W2 + (0 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · exact (hij rfl).elim
  · show ∃ T, (⟨c, r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 1, A 2])
    have hTE : ((1/2 : ℝ) • (A 2 - A 1) + A 1) - (c) = (1/4 : ℝ) • W1 + (1/4 : ℝ) • W2 + (-1/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(1/2 : ℝ) • (A 2 - A 1) + A 1, isTangentAt_of_perp hr₀_pos.le _ (1/2 : ℝ) rfl _ hQ_in
      (by rw [hTE, show A 2 - A 1 = (-1 : ℝ) • W1 + (1 : ℝ) • W2 + (0 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨c, r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 1, A 3])
    have hTE : ((1/2 : ℝ) • (A 3 - A 1) + A 1) - (c) = (1/4 : ℝ) • W1 + (-1/4 : ℝ) • W2 + (1/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(1/2 : ℝ) • (A 3 - A 1) + A 1, isTangentAt_of_perp hr₀_pos.le _ (1/2 : ℝ) rfl _ hQ_in
      (by rw [hTE, show A 3 - A 1 = (-1 : ℝ) • W1 + (0 : ℝ) • W2 + (1 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨c, r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 2, A 0])
    have hTE : ((1/2 : ℝ) • (A 0 - A 2) + A 2) - (c) = (-1/4 : ℝ) • W1 + (1/4 : ℝ) • W2 + (-1/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(1/2 : ℝ) • (A 0 - A 2) + A 2, isTangentAt_of_perp hr₀_pos.le _ (1/2 : ℝ) rfl _ hQ_in
      (by rw [hTE, show A 0 - A 2 = (0 : ℝ) • W1 + (-1 : ℝ) • W2 + (0 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨c, r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 2, A 1])
    have hTE : ((1/2 : ℝ) • (A 1 - A 2) + A 2) - (c) = (1/4 : ℝ) • W1 + (1/4 : ℝ) • W2 + (-1/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(1/2 : ℝ) • (A 1 - A 2) + A 2, isTangentAt_of_perp hr₀_pos.le _ (1/2 : ℝ) rfl _ hQ_in
      (by rw [hTE, show A 1 - A 2 = (1 : ℝ) • W1 + (-1 : ℝ) • W2 + (0 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · exact (hij rfl).elim
  · show ∃ T, (⟨c, r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 2, A 3])
    have hTE : ((1/2 : ℝ) • (A 3 - A 2) + A 2) - (c) = (-1/4 : ℝ) • W1 + (1/4 : ℝ) • W2 + (1/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(1/2 : ℝ) • (A 3 - A 2) + A 2, isTangentAt_of_perp hr₀_pos.le _ (1/2 : ℝ) rfl _ hQ_in
      (by rw [hTE, show A 3 - A 2 = (0 : ℝ) • W1 + (-1 : ℝ) • W2 + (1 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨c, r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 3, A 0])
    have hTE : ((1/2 : ℝ) • (A 0 - A 3) + A 3) - (c) = (-1/4 : ℝ) • W1 + (-1/4 : ℝ) • W2 + (1/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(1/2 : ℝ) • (A 0 - A 3) + A 3, isTangentAt_of_perp hr₀_pos.le _ (1/2 : ℝ) rfl _ hQ_in
      (by rw [hTE, show A 0 - A 3 = (0 : ℝ) • W1 + (0 : ℝ) • W2 + (-1 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨c, r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 3, A 1])
    have hTE : ((1/2 : ℝ) • (A 1 - A 3) + A 3) - (c) = (1/4 : ℝ) • W1 + (-1/4 : ℝ) • W2 + (1/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(1/2 : ℝ) • (A 1 - A 3) + A 3, isTangentAt_of_perp hr₀_pos.le _ (1/2 : ℝ) rfl _ hQ_in
      (by rw [hTE, show A 1 - A 3 = (1 : ℝ) • W1 + (0 : ℝ) • W2 + (-1 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨c, r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 3, A 2])
    have hTE : ((1/2 : ℝ) • (A 2 - A 3) + A 3) - (c) = (-1/4 : ℝ) • W1 + (1/4 : ℝ) • W2 + (1/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(1/2 : ℝ) • (A 2 - A 3) + A 3, isTangentAt_of_perp hr₀_pos.le _ (1/2 : ℝ) rfl _ hQ_in
      (by rw [hTE, show A 2 - A 3 = (0 : ℝ) • W1 + (1 : ℝ) • W2 + (-1 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · exact (hij rfl).elim

/-- The escribed sphere at vertex 0 of a regular tetrahedron (centered
at the reflection of the centroid in the opposite face, with radius `3√(s²/8)`)
is tangent to the six extended edges. -/
lemma escribed_tangent0 (A : Fin 4 → Pt) (s : ℝ)
    (hs : ∀ i j : Fin 4, i ≠ j → dist (A i) (A j) = s) (hs_pos : 0 < s) :
    TangentToEdges A ⟨3 • (A 0 + (1/4 : ℝ) • ((A 1 - A 0) + (A 2 - A 0) + (A 3 - A 0))) - 2 • A 0, 3 * Real.sqrt (s ^ 2 / 8)⟩ := by
  set W1 : Pt := A 1 - A 0 with hW1
  set W2 : Pt := A 2 - A 0 with hW2
  set W3 : Pt := A 3 - A 0 with hW3
  set c : Pt := A 0 + (1/4 : ℝ) • ((A 1 - A 0) + (A 2 - A 0) + (A 3 - A 0)) with hc
  set r₀ : ℝ := Real.sqrt (s ^ 2 / 8) with hr₀
  have hvsq : ∀ j : Fin 4, j ≠ 0 → ⟪A j - A 0, A j - A 0⟫ = s ^ 2 := by
    intro j hj
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, dist_comm, hs 0 j (Ne.symm hj)]
  have hv : ∀ j k : Fin 4, j ≠ 0 → k ≠ 0 → j ≠ k → ⟪A j - A 0, A k - A 0⟫ = s ^ 2 / 2 := by
    intro j k hj hk hjk
    have h1 : ‖(A j - A 0) - (A k - A 0)‖ ^ 2 = s ^ 2 := by
      rw [sub_sub_sub_cancel_right, ← dist_eq_norm, hs j k hjk]
    rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq (A j - A 0),
      ← real_inner_self_eq_norm_sq (A k - A 0), hvsq j hj, hvsq k hk] at h1
    linarith
  have I11 : ⟪W1, W1⟫ = s ^ 2 := by rw [hW1]; exact hvsq 1 (by decide)
  have I22 : ⟪W2, W2⟫ = s ^ 2 := by rw [hW2]; exact hvsq 2 (by decide)
  have I33 : ⟪W3, W3⟫ = s ^ 2 := by rw [hW3]; exact hvsq 3 (by decide)
  have I12 : ⟪W1, W2⟫ = s ^ 2 / 2 := by
    rw [hW1, hW2]; exact hv 1 2 (by decide) (by decide) (by decide)
  have I13 : ⟪W1, W3⟫ = s ^ 2 / 2 := by
    rw [hW1, hW3]; exact hv 1 3 (by decide) (by decide) (by decide)
  have I23 : ⟪W2, W3⟫ = s ^ 2 / 2 := by
    rw [hW2, hW3]; exact hv 2 3 (by decide) (by decide) (by decide)
  have I21 : ⟪W2, W1⟫ = s ^ 2 / 2 := by rw [real_inner_comm]; exact I12
  have I31 : ⟪W3, W1⟫ = s ^ 2 / 2 := by rw [real_inner_comm]; exact I13
  have I32 : ⟪W3, W2⟫ = s ^ 2 / 2 := by rw [real_inner_comm]; exact I23
  have key : ∀ a₁ a₂ a₃ b₁ b₂ b₃ : ℝ,
      ⟪a₁ • W1 + a₂ • W2 + a₃ • W3, b₁ • W1 + b₂ • W2 + b₃ • W3⟫ =
        (a₁ * b₁ + a₂ * b₂ + a₃ * b₃) * s ^ 2 +
        (a₁ * b₂ + a₂ * b₁ + a₁ * b₃ + a₃ * b₁ + a₂ * b₃ + a₃ * b₂) * (s ^ 2 / 2) := by
    intro a₁ a₂ a₃ b₁ b₂ b₃
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
    simp only [I11, I22, I33, I12, I13, I23, I21, I31, I32]
    ring
  have hQ_es : (3 * r₀) ^ 2 = 9 * (s ^ 2 / 8) := by
    rw [hr₀, mul_pow, Real.sq_sqrt (by positivity)]
    ring
  have hr₀_pos : 0 < r₀ := by
    rw [hr₀]
    exact Real.sqrt_pos.mpr (by positivity)
  have h3r : 0 < 3 * r₀ := by linarith [hr₀_pos]
  refine ⟨h3r, fun i j hij => ?_⟩
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · show ∃ T, (⟨3 • c - 2 • A 0, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 0, A 1])
    have hTE : ((3/2 : ℝ) • (A 1 - A 0) + A 0) - (3 • c - 2 • A 0) = (3/4 : ℝ) • W1 + (-3/4 : ℝ) • W2 + (-3/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(3/2 : ℝ) • (A 1 - A 0) + A 0, isTangentAt_of_perp h3r.le _ (3/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 1 - A 0 = (1 : ℝ) • W1 + (0 : ℝ) • W2 + (0 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨3 • c - 2 • A 0, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 0, A 2])
    have hTE : ((3/2 : ℝ) • (A 2 - A 0) + A 0) - (3 • c - 2 • A 0) = (-3/4 : ℝ) • W1 + (3/4 : ℝ) • W2 + (-3/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(3/2 : ℝ) • (A 2 - A 0) + A 0, isTangentAt_of_perp h3r.le _ (3/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 2 - A 0 = (0 : ℝ) • W1 + (1 : ℝ) • W2 + (0 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨3 • c - 2 • A 0, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 0, A 3])
    have hTE : ((3/2 : ℝ) • (A 3 - A 0) + A 0) - (3 • c - 2 • A 0) = (-3/4 : ℝ) • W1 + (-3/4 : ℝ) • W2 + (3/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(3/2 : ℝ) • (A 3 - A 0) + A 0, isTangentAt_of_perp h3r.le _ (3/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 3 - A 0 = (0 : ℝ) • W1 + (0 : ℝ) • W2 + (1 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨3 • c - 2 • A 0, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 1, A 0])
    have hTE : ((-1/2 : ℝ) • (A 0 - A 1) + A 1) - (3 • c - 2 • A 0) = (3/4 : ℝ) • W1 + (-3/4 : ℝ) • W2 + (-3/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(-1/2 : ℝ) • (A 0 - A 1) + A 1, isTangentAt_of_perp h3r.le _ (-1/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 0 - A 1 = (-1 : ℝ) • W1 + (0 : ℝ) • W2 + (0 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · exact (hij rfl).elim
  · show ∃ T, (⟨3 • c - 2 • A 0, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 1, A 2])
    have hTE : ((1/2 : ℝ) • (A 2 - A 1) + A 1) - (3 • c - 2 • A 0) = (-1/4 : ℝ) • W1 + (-1/4 : ℝ) • W2 + (-3/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(1/2 : ℝ) • (A 2 - A 1) + A 1, isTangentAt_of_perp h3r.le _ (1/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 2 - A 1 = (-1 : ℝ) • W1 + (1 : ℝ) • W2 + (0 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨3 • c - 2 • A 0, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 1, A 3])
    have hTE : ((1/2 : ℝ) • (A 3 - A 1) + A 1) - (3 • c - 2 • A 0) = (-1/4 : ℝ) • W1 + (-3/4 : ℝ) • W2 + (-1/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(1/2 : ℝ) • (A 3 - A 1) + A 1, isTangentAt_of_perp h3r.le _ (1/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 3 - A 1 = (-1 : ℝ) • W1 + (0 : ℝ) • W2 + (1 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨3 • c - 2 • A 0, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 2, A 0])
    have hTE : ((-1/2 : ℝ) • (A 0 - A 2) + A 2) - (3 • c - 2 • A 0) = (-3/4 : ℝ) • W1 + (3/4 : ℝ) • W2 + (-3/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(-1/2 : ℝ) • (A 0 - A 2) + A 2, isTangentAt_of_perp h3r.le _ (-1/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 0 - A 2 = (0 : ℝ) • W1 + (-1 : ℝ) • W2 + (0 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨3 • c - 2 • A 0, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 2, A 1])
    have hTE : ((1/2 : ℝ) • (A 1 - A 2) + A 2) - (3 • c - 2 • A 0) = (-1/4 : ℝ) • W1 + (-1/4 : ℝ) • W2 + (-3/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(1/2 : ℝ) • (A 1 - A 2) + A 2, isTangentAt_of_perp h3r.le _ (1/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 1 - A 2 = (1 : ℝ) • W1 + (-1 : ℝ) • W2 + (0 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · exact (hij rfl).elim
  · show ∃ T, (⟨3 • c - 2 • A 0, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 2, A 3])
    have hTE : ((1/2 : ℝ) • (A 3 - A 2) + A 2) - (3 • c - 2 • A 0) = (-3/4 : ℝ) • W1 + (-1/4 : ℝ) • W2 + (-1/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(1/2 : ℝ) • (A 3 - A 2) + A 2, isTangentAt_of_perp h3r.le _ (1/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 3 - A 2 = (0 : ℝ) • W1 + (-1 : ℝ) • W2 + (1 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨3 • c - 2 • A 0, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 3, A 0])
    have hTE : ((-1/2 : ℝ) • (A 0 - A 3) + A 3) - (3 • c - 2 • A 0) = (-3/4 : ℝ) • W1 + (-3/4 : ℝ) • W2 + (3/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(-1/2 : ℝ) • (A 0 - A 3) + A 3, isTangentAt_of_perp h3r.le _ (-1/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 0 - A 3 = (0 : ℝ) • W1 + (0 : ℝ) • W2 + (-1 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨3 • c - 2 • A 0, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 3, A 1])
    have hTE : ((1/2 : ℝ) • (A 1 - A 3) + A 3) - (3 • c - 2 • A 0) = (-1/4 : ℝ) • W1 + (-3/4 : ℝ) • W2 + (-1/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(1/2 : ℝ) • (A 1 - A 3) + A 3, isTangentAt_of_perp h3r.le _ (1/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 1 - A 3 = (1 : ℝ) • W1 + (0 : ℝ) • W2 + (-1 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨3 • c - 2 • A 0, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 3, A 2])
    have hTE : ((1/2 : ℝ) • (A 2 - A 3) + A 3) - (3 • c - 2 • A 0) = (-3/4 : ℝ) • W1 + (-1/4 : ℝ) • W2 + (-1/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(1/2 : ℝ) • (A 2 - A 3) + A 3, isTangentAt_of_perp h3r.le _ (1/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 2 - A 3 = (0 : ℝ) • W1 + (1 : ℝ) • W2 + (-1 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · exact (hij rfl).elim

/-- The escribed sphere at vertex 1 of a regular tetrahedron (centered
at the reflection of the centroid in the opposite face, with radius `3√(s²/8)`)
is tangent to the six extended edges. -/
lemma escribed_tangent1 (A : Fin 4 → Pt) (s : ℝ)
    (hs : ∀ i j : Fin 4, i ≠ j → dist (A i) (A j) = s) (hs_pos : 0 < s) :
    TangentToEdges A ⟨3 • (A 0 + (1/4 : ℝ) • ((A 1 - A 0) + (A 2 - A 0) + (A 3 - A 0))) - 2 • A 1, 3 * Real.sqrt (s ^ 2 / 8)⟩ := by
  set W1 : Pt := A 1 - A 0 with hW1
  set W2 : Pt := A 2 - A 0 with hW2
  set W3 : Pt := A 3 - A 0 with hW3
  set c : Pt := A 0 + (1/4 : ℝ) • ((A 1 - A 0) + (A 2 - A 0) + (A 3 - A 0)) with hc
  set r₀ : ℝ := Real.sqrt (s ^ 2 / 8) with hr₀
  have hvsq : ∀ j : Fin 4, j ≠ 0 → ⟪A j - A 0, A j - A 0⟫ = s ^ 2 := by
    intro j hj
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, dist_comm, hs 0 j (Ne.symm hj)]
  have hv : ∀ j k : Fin 4, j ≠ 0 → k ≠ 0 → j ≠ k → ⟪A j - A 0, A k - A 0⟫ = s ^ 2 / 2 := by
    intro j k hj hk hjk
    have h1 : ‖(A j - A 0) - (A k - A 0)‖ ^ 2 = s ^ 2 := by
      rw [sub_sub_sub_cancel_right, ← dist_eq_norm, hs j k hjk]
    rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq (A j - A 0),
      ← real_inner_self_eq_norm_sq (A k - A 0), hvsq j hj, hvsq k hk] at h1
    linarith
  have I11 : ⟪W1, W1⟫ = s ^ 2 := by rw [hW1]; exact hvsq 1 (by decide)
  have I22 : ⟪W2, W2⟫ = s ^ 2 := by rw [hW2]; exact hvsq 2 (by decide)
  have I33 : ⟪W3, W3⟫ = s ^ 2 := by rw [hW3]; exact hvsq 3 (by decide)
  have I12 : ⟪W1, W2⟫ = s ^ 2 / 2 := by
    rw [hW1, hW2]; exact hv 1 2 (by decide) (by decide) (by decide)
  have I13 : ⟪W1, W3⟫ = s ^ 2 / 2 := by
    rw [hW1, hW3]; exact hv 1 3 (by decide) (by decide) (by decide)
  have I23 : ⟪W2, W3⟫ = s ^ 2 / 2 := by
    rw [hW2, hW3]; exact hv 2 3 (by decide) (by decide) (by decide)
  have I21 : ⟪W2, W1⟫ = s ^ 2 / 2 := by rw [real_inner_comm]; exact I12
  have I31 : ⟪W3, W1⟫ = s ^ 2 / 2 := by rw [real_inner_comm]; exact I13
  have I32 : ⟪W3, W2⟫ = s ^ 2 / 2 := by rw [real_inner_comm]; exact I23
  have key : ∀ a₁ a₂ a₃ b₁ b₂ b₃ : ℝ,
      ⟪a₁ • W1 + a₂ • W2 + a₃ • W3, b₁ • W1 + b₂ • W2 + b₃ • W3⟫ =
        (a₁ * b₁ + a₂ * b₂ + a₃ * b₃) * s ^ 2 +
        (a₁ * b₂ + a₂ * b₁ + a₁ * b₃ + a₃ * b₁ + a₂ * b₃ + a₃ * b₂) * (s ^ 2 / 2) := by
    intro a₁ a₂ a₃ b₁ b₂ b₃
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
    simp only [I11, I22, I33, I12, I13, I23, I21, I31, I32]
    ring
  have hQ_es : (3 * r₀) ^ 2 = 9 * (s ^ 2 / 8) := by
    rw [hr₀, mul_pow, Real.sq_sqrt (by positivity)]
    ring
  have hr₀_pos : 0 < r₀ := by
    rw [hr₀]
    exact Real.sqrt_pos.mpr (by positivity)
  have h3r : 0 < 3 * r₀ := by linarith [hr₀_pos]
  refine ⟨h3r, fun i j hij => ?_⟩
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · show ∃ T, (⟨3 • c - 2 • A 1, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 0, A 1])
    have hTE : ((-1/2 : ℝ) • (A 1 - A 0) + A 0) - (3 • c - 2 • A 1) = (3/4 : ℝ) • W1 + (-3/4 : ℝ) • W2 + (-3/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(-1/2 : ℝ) • (A 1 - A 0) + A 0, isTangentAt_of_perp h3r.le _ (-1/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 1 - A 0 = (1 : ℝ) • W1 + (0 : ℝ) • W2 + (0 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨3 • c - 2 • A 1, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 0, A 2])
    have hTE : ((1/2 : ℝ) • (A 2 - A 0) + A 0) - (3 • c - 2 • A 1) = (5/4 : ℝ) • W1 + (-1/4 : ℝ) • W2 + (-3/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(1/2 : ℝ) • (A 2 - A 0) + A 0, isTangentAt_of_perp h3r.le _ (1/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 2 - A 0 = (0 : ℝ) • W1 + (1 : ℝ) • W2 + (0 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨3 • c - 2 • A 1, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 0, A 3])
    have hTE : ((1/2 : ℝ) • (A 3 - A 0) + A 0) - (3 • c - 2 • A 1) = (5/4 : ℝ) • W1 + (-3/4 : ℝ) • W2 + (-1/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(1/2 : ℝ) • (A 3 - A 0) + A 0, isTangentAt_of_perp h3r.le _ (1/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 3 - A 0 = (0 : ℝ) • W1 + (0 : ℝ) • W2 + (1 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨3 • c - 2 • A 1, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 1, A 0])
    have hTE : ((3/2 : ℝ) • (A 0 - A 1) + A 1) - (3 • c - 2 • A 1) = (3/4 : ℝ) • W1 + (-3/4 : ℝ) • W2 + (-3/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(3/2 : ℝ) • (A 0 - A 1) + A 1, isTangentAt_of_perp h3r.le _ (3/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 0 - A 1 = (-1 : ℝ) • W1 + (0 : ℝ) • W2 + (0 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · exact (hij rfl).elim
  · show ∃ T, (⟨3 • c - 2 • A 1, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 1, A 2])
    have hTE : ((3/2 : ℝ) • (A 2 - A 1) + A 1) - (3 • c - 2 • A 1) = (3/4 : ℝ) • W1 + (3/4 : ℝ) • W2 + (-3/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(3/2 : ℝ) • (A 2 - A 1) + A 1, isTangentAt_of_perp h3r.le _ (3/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 2 - A 1 = (-1 : ℝ) • W1 + (1 : ℝ) • W2 + (0 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨3 • c - 2 • A 1, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 1, A 3])
    have hTE : ((3/2 : ℝ) • (A 3 - A 1) + A 1) - (3 • c - 2 • A 1) = (3/4 : ℝ) • W1 + (-3/4 : ℝ) • W2 + (3/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(3/2 : ℝ) • (A 3 - A 1) + A 1, isTangentAt_of_perp h3r.le _ (3/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 3 - A 1 = (-1 : ℝ) • W1 + (0 : ℝ) • W2 + (1 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨3 • c - 2 • A 1, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 2, A 0])
    have hTE : ((1/2 : ℝ) • (A 0 - A 2) + A 2) - (3 • c - 2 • A 1) = (5/4 : ℝ) • W1 + (-1/4 : ℝ) • W2 + (-3/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(1/2 : ℝ) • (A 0 - A 2) + A 2, isTangentAt_of_perp h3r.le _ (1/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 0 - A 2 = (0 : ℝ) • W1 + (-1 : ℝ) • W2 + (0 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨3 • c - 2 • A 1, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 2, A 1])
    have hTE : ((-1/2 : ℝ) • (A 1 - A 2) + A 2) - (3 • c - 2 • A 1) = (3/4 : ℝ) • W1 + (3/4 : ℝ) • W2 + (-3/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(-1/2 : ℝ) • (A 1 - A 2) + A 2, isTangentAt_of_perp h3r.le _ (-1/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 1 - A 2 = (1 : ℝ) • W1 + (-1 : ℝ) • W2 + (0 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · exact (hij rfl).elim
  · show ∃ T, (⟨3 • c - 2 • A 1, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 2, A 3])
    have hTE : ((1/2 : ℝ) • (A 3 - A 2) + A 2) - (3 • c - 2 • A 1) = (5/4 : ℝ) • W1 + (-1/4 : ℝ) • W2 + (-1/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(1/2 : ℝ) • (A 3 - A 2) + A 2, isTangentAt_of_perp h3r.le _ (1/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 3 - A 2 = (0 : ℝ) • W1 + (-1 : ℝ) • W2 + (1 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨3 • c - 2 • A 1, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 3, A 0])
    have hTE : ((1/2 : ℝ) • (A 0 - A 3) + A 3) - (3 • c - 2 • A 1) = (5/4 : ℝ) • W1 + (-3/4 : ℝ) • W2 + (-1/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(1/2 : ℝ) • (A 0 - A 3) + A 3, isTangentAt_of_perp h3r.le _ (1/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 0 - A 3 = (0 : ℝ) • W1 + (0 : ℝ) • W2 + (-1 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨3 • c - 2 • A 1, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 3, A 1])
    have hTE : ((-1/2 : ℝ) • (A 1 - A 3) + A 3) - (3 • c - 2 • A 1) = (3/4 : ℝ) • W1 + (-3/4 : ℝ) • W2 + (3/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(-1/2 : ℝ) • (A 1 - A 3) + A 3, isTangentAt_of_perp h3r.le _ (-1/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 1 - A 3 = (1 : ℝ) • W1 + (0 : ℝ) • W2 + (-1 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨3 • c - 2 • A 1, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 3, A 2])
    have hTE : ((1/2 : ℝ) • (A 2 - A 3) + A 3) - (3 • c - 2 • A 1) = (5/4 : ℝ) • W1 + (-1/4 : ℝ) • W2 + (-1/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(1/2 : ℝ) • (A 2 - A 3) + A 3, isTangentAt_of_perp h3r.le _ (1/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 2 - A 3 = (0 : ℝ) • W1 + (1 : ℝ) • W2 + (-1 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · exact (hij rfl).elim

/-- The escribed sphere at vertex 2 of a regular tetrahedron (centered
at the reflection of the centroid in the opposite face, with radius `3√(s²/8)`)
is tangent to the six extended edges. -/
lemma escribed_tangent2 (A : Fin 4 → Pt) (s : ℝ)
    (hs : ∀ i j : Fin 4, i ≠ j → dist (A i) (A j) = s) (hs_pos : 0 < s) :
    TangentToEdges A ⟨3 • (A 0 + (1/4 : ℝ) • ((A 1 - A 0) + (A 2 - A 0) + (A 3 - A 0))) - 2 • A 2, 3 * Real.sqrt (s ^ 2 / 8)⟩ := by
  set W1 : Pt := A 1 - A 0 with hW1
  set W2 : Pt := A 2 - A 0 with hW2
  set W3 : Pt := A 3 - A 0 with hW3
  set c : Pt := A 0 + (1/4 : ℝ) • ((A 1 - A 0) + (A 2 - A 0) + (A 3 - A 0)) with hc
  set r₀ : ℝ := Real.sqrt (s ^ 2 / 8) with hr₀
  have hvsq : ∀ j : Fin 4, j ≠ 0 → ⟪A j - A 0, A j - A 0⟫ = s ^ 2 := by
    intro j hj
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, dist_comm, hs 0 j (Ne.symm hj)]
  have hv : ∀ j k : Fin 4, j ≠ 0 → k ≠ 0 → j ≠ k → ⟪A j - A 0, A k - A 0⟫ = s ^ 2 / 2 := by
    intro j k hj hk hjk
    have h1 : ‖(A j - A 0) - (A k - A 0)‖ ^ 2 = s ^ 2 := by
      rw [sub_sub_sub_cancel_right, ← dist_eq_norm, hs j k hjk]
    rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq (A j - A 0),
      ← real_inner_self_eq_norm_sq (A k - A 0), hvsq j hj, hvsq k hk] at h1
    linarith
  have I11 : ⟪W1, W1⟫ = s ^ 2 := by rw [hW1]; exact hvsq 1 (by decide)
  have I22 : ⟪W2, W2⟫ = s ^ 2 := by rw [hW2]; exact hvsq 2 (by decide)
  have I33 : ⟪W3, W3⟫ = s ^ 2 := by rw [hW3]; exact hvsq 3 (by decide)
  have I12 : ⟪W1, W2⟫ = s ^ 2 / 2 := by
    rw [hW1, hW2]; exact hv 1 2 (by decide) (by decide) (by decide)
  have I13 : ⟪W1, W3⟫ = s ^ 2 / 2 := by
    rw [hW1, hW3]; exact hv 1 3 (by decide) (by decide) (by decide)
  have I23 : ⟪W2, W3⟫ = s ^ 2 / 2 := by
    rw [hW2, hW3]; exact hv 2 3 (by decide) (by decide) (by decide)
  have I21 : ⟪W2, W1⟫ = s ^ 2 / 2 := by rw [real_inner_comm]; exact I12
  have I31 : ⟪W3, W1⟫ = s ^ 2 / 2 := by rw [real_inner_comm]; exact I13
  have I32 : ⟪W3, W2⟫ = s ^ 2 / 2 := by rw [real_inner_comm]; exact I23
  have key : ∀ a₁ a₂ a₃ b₁ b₂ b₃ : ℝ,
      ⟪a₁ • W1 + a₂ • W2 + a₃ • W3, b₁ • W1 + b₂ • W2 + b₃ • W3⟫ =
        (a₁ * b₁ + a₂ * b₂ + a₃ * b₃) * s ^ 2 +
        (a₁ * b₂ + a₂ * b₁ + a₁ * b₃ + a₃ * b₁ + a₂ * b₃ + a₃ * b₂) * (s ^ 2 / 2) := by
    intro a₁ a₂ a₃ b₁ b₂ b₃
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
    simp only [I11, I22, I33, I12, I13, I23, I21, I31, I32]
    ring
  have hQ_es : (3 * r₀) ^ 2 = 9 * (s ^ 2 / 8) := by
    rw [hr₀, mul_pow, Real.sq_sqrt (by positivity)]
    ring
  have hr₀_pos : 0 < r₀ := by
    rw [hr₀]
    exact Real.sqrt_pos.mpr (by positivity)
  have h3r : 0 < 3 * r₀ := by linarith [hr₀_pos]
  refine ⟨h3r, fun i j hij => ?_⟩
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · show ∃ T, (⟨3 • c - 2 • A 2, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 0, A 1])
    have hTE : ((1/2 : ℝ) • (A 1 - A 0) + A 0) - (3 • c - 2 • A 2) = (-1/4 : ℝ) • W1 + (5/4 : ℝ) • W2 + (-3/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(1/2 : ℝ) • (A 1 - A 0) + A 0, isTangentAt_of_perp h3r.le _ (1/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 1 - A 0 = (1 : ℝ) • W1 + (0 : ℝ) • W2 + (0 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨3 • c - 2 • A 2, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 0, A 2])
    have hTE : ((-1/2 : ℝ) • (A 2 - A 0) + A 0) - (3 • c - 2 • A 2) = (-3/4 : ℝ) • W1 + (3/4 : ℝ) • W2 + (-3/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(-1/2 : ℝ) • (A 2 - A 0) + A 0, isTangentAt_of_perp h3r.le _ (-1/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 2 - A 0 = (0 : ℝ) • W1 + (1 : ℝ) • W2 + (0 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨3 • c - 2 • A 2, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 0, A 3])
    have hTE : ((1/2 : ℝ) • (A 3 - A 0) + A 0) - (3 • c - 2 • A 2) = (-3/4 : ℝ) • W1 + (5/4 : ℝ) • W2 + (-1/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(1/2 : ℝ) • (A 3 - A 0) + A 0, isTangentAt_of_perp h3r.le _ (1/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 3 - A 0 = (0 : ℝ) • W1 + (0 : ℝ) • W2 + (1 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨3 • c - 2 • A 2, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 1, A 0])
    have hTE : ((1/2 : ℝ) • (A 0 - A 1) + A 1) - (3 • c - 2 • A 2) = (-1/4 : ℝ) • W1 + (5/4 : ℝ) • W2 + (-3/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(1/2 : ℝ) • (A 0 - A 1) + A 1, isTangentAt_of_perp h3r.le _ (1/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 0 - A 1 = (-1 : ℝ) • W1 + (0 : ℝ) • W2 + (0 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · exact (hij rfl).elim
  · show ∃ T, (⟨3 • c - 2 • A 2, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 1, A 2])
    have hTE : ((-1/2 : ℝ) • (A 2 - A 1) + A 1) - (3 • c - 2 • A 2) = (3/4 : ℝ) • W1 + (3/4 : ℝ) • W2 + (-3/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(-1/2 : ℝ) • (A 2 - A 1) + A 1, isTangentAt_of_perp h3r.le _ (-1/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 2 - A 1 = (-1 : ℝ) • W1 + (1 : ℝ) • W2 + (0 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨3 • c - 2 • A 2, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 1, A 3])
    have hTE : ((1/2 : ℝ) • (A 3 - A 1) + A 1) - (3 • c - 2 • A 2) = (-1/4 : ℝ) • W1 + (5/4 : ℝ) • W2 + (-1/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(1/2 : ℝ) • (A 3 - A 1) + A 1, isTangentAt_of_perp h3r.le _ (1/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 3 - A 1 = (-1 : ℝ) • W1 + (0 : ℝ) • W2 + (1 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨3 • c - 2 • A 2, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 2, A 0])
    have hTE : ((3/2 : ℝ) • (A 0 - A 2) + A 2) - (3 • c - 2 • A 2) = (-3/4 : ℝ) • W1 + (3/4 : ℝ) • W2 + (-3/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(3/2 : ℝ) • (A 0 - A 2) + A 2, isTangentAt_of_perp h3r.le _ (3/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 0 - A 2 = (0 : ℝ) • W1 + (-1 : ℝ) • W2 + (0 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨3 • c - 2 • A 2, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 2, A 1])
    have hTE : ((3/2 : ℝ) • (A 1 - A 2) + A 2) - (3 • c - 2 • A 2) = (3/4 : ℝ) • W1 + (3/4 : ℝ) • W2 + (-3/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(3/2 : ℝ) • (A 1 - A 2) + A 2, isTangentAt_of_perp h3r.le _ (3/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 1 - A 2 = (1 : ℝ) • W1 + (-1 : ℝ) • W2 + (0 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · exact (hij rfl).elim
  · show ∃ T, (⟨3 • c - 2 • A 2, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 2, A 3])
    have hTE : ((3/2 : ℝ) • (A 3 - A 2) + A 2) - (3 • c - 2 • A 2) = (-3/4 : ℝ) • W1 + (3/4 : ℝ) • W2 + (3/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(3/2 : ℝ) • (A 3 - A 2) + A 2, isTangentAt_of_perp h3r.le _ (3/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 3 - A 2 = (0 : ℝ) • W1 + (-1 : ℝ) • W2 + (1 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨3 • c - 2 • A 2, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 3, A 0])
    have hTE : ((1/2 : ℝ) • (A 0 - A 3) + A 3) - (3 • c - 2 • A 2) = (-3/4 : ℝ) • W1 + (5/4 : ℝ) • W2 + (-1/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(1/2 : ℝ) • (A 0 - A 3) + A 3, isTangentAt_of_perp h3r.le _ (1/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 0 - A 3 = (0 : ℝ) • W1 + (0 : ℝ) • W2 + (-1 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨3 • c - 2 • A 2, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 3, A 1])
    have hTE : ((1/2 : ℝ) • (A 1 - A 3) + A 3) - (3 • c - 2 • A 2) = (-1/4 : ℝ) • W1 + (5/4 : ℝ) • W2 + (-1/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(1/2 : ℝ) • (A 1 - A 3) + A 3, isTangentAt_of_perp h3r.le _ (1/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 1 - A 3 = (1 : ℝ) • W1 + (0 : ℝ) • W2 + (-1 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨3 • c - 2 • A 2, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 3, A 2])
    have hTE : ((-1/2 : ℝ) • (A 2 - A 3) + A 3) - (3 • c - 2 • A 2) = (-3/4 : ℝ) • W1 + (3/4 : ℝ) • W2 + (3/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(-1/2 : ℝ) • (A 2 - A 3) + A 3, isTangentAt_of_perp h3r.le _ (-1/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 2 - A 3 = (0 : ℝ) • W1 + (1 : ℝ) • W2 + (-1 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · exact (hij rfl).elim

/-- The escribed sphere at vertex 3 of a regular tetrahedron (centered
at the reflection of the centroid in the opposite face, with radius `3√(s²/8)`)
is tangent to the six extended edges. -/
lemma escribed_tangent3 (A : Fin 4 → Pt) (s : ℝ)
    (hs : ∀ i j : Fin 4, i ≠ j → dist (A i) (A j) = s) (hs_pos : 0 < s) :
    TangentToEdges A ⟨3 • (A 0 + (1/4 : ℝ) • ((A 1 - A 0) + (A 2 - A 0) + (A 3 - A 0))) - 2 • A 3, 3 * Real.sqrt (s ^ 2 / 8)⟩ := by
  set W1 : Pt := A 1 - A 0 with hW1
  set W2 : Pt := A 2 - A 0 with hW2
  set W3 : Pt := A 3 - A 0 with hW3
  set c : Pt := A 0 + (1/4 : ℝ) • ((A 1 - A 0) + (A 2 - A 0) + (A 3 - A 0)) with hc
  set r₀ : ℝ := Real.sqrt (s ^ 2 / 8) with hr₀
  have hvsq : ∀ j : Fin 4, j ≠ 0 → ⟪A j - A 0, A j - A 0⟫ = s ^ 2 := by
    intro j hj
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, dist_comm, hs 0 j (Ne.symm hj)]
  have hv : ∀ j k : Fin 4, j ≠ 0 → k ≠ 0 → j ≠ k → ⟪A j - A 0, A k - A 0⟫ = s ^ 2 / 2 := by
    intro j k hj hk hjk
    have h1 : ‖(A j - A 0) - (A k - A 0)‖ ^ 2 = s ^ 2 := by
      rw [sub_sub_sub_cancel_right, ← dist_eq_norm, hs j k hjk]
    rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq (A j - A 0),
      ← real_inner_self_eq_norm_sq (A k - A 0), hvsq j hj, hvsq k hk] at h1
    linarith
  have I11 : ⟪W1, W1⟫ = s ^ 2 := by rw [hW1]; exact hvsq 1 (by decide)
  have I22 : ⟪W2, W2⟫ = s ^ 2 := by rw [hW2]; exact hvsq 2 (by decide)
  have I33 : ⟪W3, W3⟫ = s ^ 2 := by rw [hW3]; exact hvsq 3 (by decide)
  have I12 : ⟪W1, W2⟫ = s ^ 2 / 2 := by
    rw [hW1, hW2]; exact hv 1 2 (by decide) (by decide) (by decide)
  have I13 : ⟪W1, W3⟫ = s ^ 2 / 2 := by
    rw [hW1, hW3]; exact hv 1 3 (by decide) (by decide) (by decide)
  have I23 : ⟪W2, W3⟫ = s ^ 2 / 2 := by
    rw [hW2, hW3]; exact hv 2 3 (by decide) (by decide) (by decide)
  have I21 : ⟪W2, W1⟫ = s ^ 2 / 2 := by rw [real_inner_comm]; exact I12
  have I31 : ⟪W3, W1⟫ = s ^ 2 / 2 := by rw [real_inner_comm]; exact I13
  have I32 : ⟪W3, W2⟫ = s ^ 2 / 2 := by rw [real_inner_comm]; exact I23
  have key : ∀ a₁ a₂ a₃ b₁ b₂ b₃ : ℝ,
      ⟪a₁ • W1 + a₂ • W2 + a₃ • W3, b₁ • W1 + b₂ • W2 + b₃ • W3⟫ =
        (a₁ * b₁ + a₂ * b₂ + a₃ * b₃) * s ^ 2 +
        (a₁ * b₂ + a₂ * b₁ + a₁ * b₃ + a₃ * b₁ + a₂ * b₃ + a₃ * b₂) * (s ^ 2 / 2) := by
    intro a₁ a₂ a₃ b₁ b₂ b₃
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
    simp only [I11, I22, I33, I12, I13, I23, I21, I31, I32]
    ring
  have hQ_es : (3 * r₀) ^ 2 = 9 * (s ^ 2 / 8) := by
    rw [hr₀, mul_pow, Real.sq_sqrt (by positivity)]
    ring
  have hr₀_pos : 0 < r₀ := by
    rw [hr₀]
    exact Real.sqrt_pos.mpr (by positivity)
  have h3r : 0 < 3 * r₀ := by linarith [hr₀_pos]
  refine ⟨h3r, fun i j hij => ?_⟩
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · show ∃ T, (⟨3 • c - 2 • A 3, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 0, A 1])
    have hTE : ((1/2 : ℝ) • (A 1 - A 0) + A 0) - (3 • c - 2 • A 3) = (-1/4 : ℝ) • W1 + (-3/4 : ℝ) • W2 + (5/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(1/2 : ℝ) • (A 1 - A 0) + A 0, isTangentAt_of_perp h3r.le _ (1/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 1 - A 0 = (1 : ℝ) • W1 + (0 : ℝ) • W2 + (0 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨3 • c - 2 • A 3, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 0, A 2])
    have hTE : ((1/2 : ℝ) • (A 2 - A 0) + A 0) - (3 • c - 2 • A 3) = (-3/4 : ℝ) • W1 + (-1/4 : ℝ) • W2 + (5/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(1/2 : ℝ) • (A 2 - A 0) + A 0, isTangentAt_of_perp h3r.le _ (1/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 2 - A 0 = (0 : ℝ) • W1 + (1 : ℝ) • W2 + (0 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨3 • c - 2 • A 3, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 0, A 3])
    have hTE : ((-1/2 : ℝ) • (A 3 - A 0) + A 0) - (3 • c - 2 • A 3) = (-3/4 : ℝ) • W1 + (-3/4 : ℝ) • W2 + (3/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(-1/2 : ℝ) • (A 3 - A 0) + A 0, isTangentAt_of_perp h3r.le _ (-1/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 3 - A 0 = (0 : ℝ) • W1 + (0 : ℝ) • W2 + (1 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨3 • c - 2 • A 3, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 1, A 0])
    have hTE : ((1/2 : ℝ) • (A 0 - A 1) + A 1) - (3 • c - 2 • A 3) = (-1/4 : ℝ) • W1 + (-3/4 : ℝ) • W2 + (5/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(1/2 : ℝ) • (A 0 - A 1) + A 1, isTangentAt_of_perp h3r.le _ (1/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 0 - A 1 = (-1 : ℝ) • W1 + (0 : ℝ) • W2 + (0 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · exact (hij rfl).elim
  · show ∃ T, (⟨3 • c - 2 • A 3, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 1, A 2])
    have hTE : ((1/2 : ℝ) • (A 2 - A 1) + A 1) - (3 • c - 2 • A 3) = (-1/4 : ℝ) • W1 + (-1/4 : ℝ) • W2 + (5/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(1/2 : ℝ) • (A 2 - A 1) + A 1, isTangentAt_of_perp h3r.le _ (1/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 2 - A 1 = (-1 : ℝ) • W1 + (1 : ℝ) • W2 + (0 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨3 • c - 2 • A 3, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 1, A 3])
    have hTE : ((-1/2 : ℝ) • (A 3 - A 1) + A 1) - (3 • c - 2 • A 3) = (3/4 : ℝ) • W1 + (-3/4 : ℝ) • W2 + (3/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(-1/2 : ℝ) • (A 3 - A 1) + A 1, isTangentAt_of_perp h3r.le _ (-1/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 3 - A 1 = (-1 : ℝ) • W1 + (0 : ℝ) • W2 + (1 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨3 • c - 2 • A 3, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 2, A 0])
    have hTE : ((1/2 : ℝ) • (A 0 - A 2) + A 2) - (3 • c - 2 • A 3) = (-3/4 : ℝ) • W1 + (-1/4 : ℝ) • W2 + (5/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(1/2 : ℝ) • (A 0 - A 2) + A 2, isTangentAt_of_perp h3r.le _ (1/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 0 - A 2 = (0 : ℝ) • W1 + (-1 : ℝ) • W2 + (0 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨3 • c - 2 • A 3, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 2, A 1])
    have hTE : ((1/2 : ℝ) • (A 1 - A 2) + A 2) - (3 • c - 2 • A 3) = (-1/4 : ℝ) • W1 + (-1/4 : ℝ) • W2 + (5/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(1/2 : ℝ) • (A 1 - A 2) + A 2, isTangentAt_of_perp h3r.le _ (1/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 1 - A 2 = (1 : ℝ) • W1 + (-1 : ℝ) • W2 + (0 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · exact (hij rfl).elim
  · show ∃ T, (⟨3 • c - 2 • A 3, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 2, A 3])
    have hTE : ((-1/2 : ℝ) • (A 3 - A 2) + A 2) - (3 • c - 2 • A 3) = (-3/4 : ℝ) • W1 + (3/4 : ℝ) • W2 + (3/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(-1/2 : ℝ) • (A 3 - A 2) + A 2, isTangentAt_of_perp h3r.le _ (-1/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 3 - A 2 = (0 : ℝ) • W1 + (-1 : ℝ) • W2 + (1 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨3 • c - 2 • A 3, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 3, A 0])
    have hTE : ((3/2 : ℝ) • (A 0 - A 3) + A 3) - (3 • c - 2 • A 3) = (-3/4 : ℝ) • W1 + (-3/4 : ℝ) • W2 + (3/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(3/2 : ℝ) • (A 0 - A 3) + A 3, isTangentAt_of_perp h3r.le _ (3/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 0 - A 3 = (0 : ℝ) • W1 + (0 : ℝ) • W2 + (-1 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨3 • c - 2 • A 3, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 3, A 1])
    have hTE : ((3/2 : ℝ) • (A 1 - A 3) + A 3) - (3 • c - 2 • A 3) = (3/4 : ℝ) • W1 + (-3/4 : ℝ) • W2 + (3/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(3/2 : ℝ) • (A 1 - A 3) + A 3, isTangentAt_of_perp h3r.le _ (3/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 1 - A 3 = (1 : ℝ) • W1 + (0 : ℝ) • W2 + (-1 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · show ∃ T, (⟨3 • c - 2 • A 3, 3 * r₀⟩ : Sphere Pt).IsTangentAt T (line[ℝ, A 3, A 2])
    have hTE : ((3/2 : ℝ) • (A 2 - A 3) + A 3) - (3 • c - 2 • A 3) = (-3/4 : ℝ) • W1 + (3/4 : ℝ) • W2 + (3/4 : ℝ) • W3 := by
      rw [hc, hW1, hW2, hW3]; module
    exact ⟨(3/2 : ℝ) • (A 2 - A 3) + A 3, isTangentAt_of_perp h3r.le _ (3/2 : ℝ) rfl _ hQ_es
      (by rw [hTE, show A 2 - A 3 = (0 : ℝ) • W1 + (1 : ℝ) • W2 + (-1 : ℝ) • W3 from by rw [hW1, hW2, hW3]; module, key]; ring)
      (by rw [hTE, key]; ring)⟩
  · exact (hij rfl).elim

snip end

/-- **IMO 1962 Problem 7, part (a)**: if a (non-degenerate) tetrahedron admits
five distinct spheres each tangent to its six extended edges, then it is
regular. -/
problem imo1962_p7a (A : Fin 4 → Pt) (hA : AffineIndependent ℝ A)
    (S : Fin 5 → Sphere Pt) (hinj : Function.Injective S)
    (hT : ∀ k, TangentToEdges A (S k)) :
    ∃ s : ℝ, ∀ i j : Fin 4, i ≠ j → dist (A i) (A j) = s := by
  obtain ⟨k₀, hk₀⟩ := exists_insphere hA S hinj hT
  obtain ⟨k₁, hk₁⟩ := exists_escribed hA S hinj hT 0
  obtain ⟨k₂, hk₂⟩ := exists_escribed hA S hinj hT 1
  exact regular_of_types hk₀ hk₁ hk₂

/-- **IMO 1962 Problem 7, part (b)**: every regular tetrahedron admits five
distinct spheres each tangent to its six extended edges. -/
problem imo1962_p7b (A : Fin 4 → Pt) (hA : AffineIndependent ℝ A)
    (hreg : ∃ s : ℝ, ∀ i j : Fin 4, i ≠ j → dist (A i) (A j) = s) :
    ∃ S : Fin 5 → Sphere Pt, Function.Injective S ∧ ∀ k, TangentToEdges A (S k) := by
  obtain ⟨s, hs⟩ := hreg
  have hAi : Function.Injective A := hA.injective
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have hs_pos : 0 < s := by
    have h := hs 0 1 h01
    rw [← h]
    exact dist_pos.mpr (hAi.ne h01)
  set c : Pt := A 0 + (1/4 : ℝ) • ((A 1 - A 0) + (A 2 - A 0) + (A 3 - A 0)) with hc
  set r₀ : ℝ := Real.sqrt (s ^ 2 / 8) with hr₀
  have hr₀_pos : 0 < r₀ := by
    rw [hr₀]
    exact Real.sqrt_pos.mpr (by positivity)
  refine ⟨Fin.cons ⟨c, r₀⟩ (fun m : Fin 4 => ⟨3 • c - 2 • A m, 3 * r₀⟩), ?_, ?_⟩
  · intro k l h
    obtain rfl | ⟨m, rfl⟩ := Fin.eq_zero_or_eq_succ k
    · obtain rfl | ⟨m', rfl⟩ := Fin.eq_zero_or_eq_succ l
      · rfl
      · rw [Fin.cons_zero, Fin.cons_succ] at h
        have hr : r₀ = 3 * r₀ := congrArg Sphere.radius h
        linarith
    · obtain rfl | ⟨m', rfl⟩ := Fin.eq_zero_or_eq_succ l
      · rw [Fin.cons_succ, Fin.cons_zero] at h
        have hr : 3 * r₀ = r₀ := congrArg Sphere.radius h
        linarith
      · rw [Fin.cons_succ, Fin.cons_succ] at h
        have hcc : 3 • c - 2 • A m = 3 • c - 2 • A m' := congrArg Sphere.center h
        have h2 : (2:ℝ) • A m = (2:ℝ) • A m' := by
          calc (2:ℝ) • A m = 3 • c - (3 • c - 2 • A m) := by module
            _ = 3 • c - (3 • c - 2 • A m') := by rw [hcc]
            _ = (2:ℝ) • A m' := by module
        have hmm : A m = A m' := by
          calc A m = (2:ℝ)⁻¹ • ((2:ℝ) • A m) := (inv_smul_smul₀ (by norm_num) _).symm
            _ = (2:ℝ)⁻¹ • ((2:ℝ) • A m') := by rw [h2]
            _ = A m' := inv_smul_smul₀ (by norm_num) _
        exact congrArg Fin.succ (hAi hmm)
  · intro k
    obtain rfl | ⟨m, rfl⟩ := Fin.eq_zero_or_eq_succ k
    · rw [Fin.cons_zero, hc, hr₀]
      exact insphere_tangent A s hs hs_pos
    · rw [Fin.cons_succ]
      fin_cases m <;> rw [hc, hr₀]
      · exact escribed_tangent0 A s hs hs_pos
      · exact escribed_tangent1 A s hs hs_pos
      · exact escribed_tangent2 A s hs hs_pos
      · exact escribed_tangent3 A s hs hs_pos

end Imo1962P7
