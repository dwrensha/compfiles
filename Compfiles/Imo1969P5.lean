/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.Convex.Independent
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Choose.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics, .Geometry] }

/-!
# International Mathematical Olympiad 1969, Problem 5

Given $n > 4$ points in the plane, no three collinear. Prove that there are at
least $(n-3)(n-4)/2$ convex quadrilaterals with vertices amongst the $n$ points.
-/

namespace Imo1969P5

/-- The type of points in the Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- A finite set of points is in *convex position* if no point of the set lies in
the convex hull of the remaining points. A convex quadrilateral determined by a set
of points is a 4-element subset of the set that is in convex position. -/
def ConvexPosition (Q : Finset Pt) : Prop :=
  ConvexIndependent ℝ (fun p : (Q : Set Pt) => (p : Pt))

/-- The convex quadrilaterals determined by a finset of points `S`: the 4-element
subsets of `S` that are in convex position. -/
noncomputable def convexQuads (S : Finset Pt) : Finset (Finset Pt) := by
  classical
  exact (S.powersetCard 4).filter fun Q => ConvexPosition Q

snip begin

/-- Membership in `convexQuads`: the 4-element subsets in convex position. -/
theorem mem_convexQuads {S Q : Finset Pt} :
    Q ∈ convexQuads S ↔ Q ⊆ S ∧ Q.card = 4 ∧ ConvexPosition Q := by
  classical
  simp only [convexQuads, Finset.mem_filter, Finset.mem_powersetCard, and_assoc]

/-- The cardinality of a biUnion is at most the sum of the cardinalities. -/
theorem card_biUnion_le {ι α : Type*} [DecidableEq ι] [DecidableEq α] (s : Finset ι)
    (f : ι → Finset α) : (s.biUnion f).card ≤ ∑ i ∈ s, (f i).card := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.biUnion_insert]
    exact (Finset.card_union_le _ _).trans (add_le_add le_rfl ih)

attribute [local instance] Classical.decEq

/-- The linear functional `p ↦ (X 1 - Y 1) * p 0 - (X 0 - Y 0) * p 1`, i.e. twice the
signed area of the triangle `X Y p` up to an additive constant; its level sets are the
lines parallel to `X Y`. -/
def lineMap (X Y : Pt) : Pt →ₗ[ℝ] ℝ where
  toFun p := (X 1 - Y 1) * p 0 - (X 0 - Y 0) * p 1
  map_add' x y := by
    simp only [PiLp.add_apply]
    ring
  map_smul' c x := by
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp]
theorem lineMap_apply (X Y p : Pt) :
    lineMap X Y p = (X 1 - Y 1) * p 0 - (X 0 - Y 0) * p 1 := rfl

/-- `gfun X Y p` measures the signed distance of `p` from the line through `X` and `Y`;
it vanishes exactly on that line. -/
abbrev gfun (X Y p : Pt) : ℝ := lineMap X Y p - lineMap X Y X

theorem gfun_self (X Y : Pt) : gfun X Y X = 0 := sub_self _

theorem lineMap_right (X Y : Pt) : lineMap X Y Y = lineMap X Y X := by
  rw [lineMap_apply, lineMap_apply]; ring

theorem gfun_right (X Y : Pt) : gfun X Y Y = 0 := sub_eq_zero.2 (lineMap_right X Y)

theorem lineMap_swap (X Y : Pt) : lineMap Y X = -lineMap X Y := by
  ext p
  simp only [lineMap_apply, LinearMap.neg_apply]
  ring

theorem gfun_swap (X Y p : Pt) : gfun Y X p = -gfun X Y p := by
  show lineMap Y X p - lineMap Y X Y = -(lineMap X Y p - lineMap X Y X)
  simp only [lineMap_apply]
  ring

/-- Applying the affine functional `gfun X Y` to a convex combination yields the
corresponding combination of values. -/
theorem gfun_sum (X Y : Pt) {s : Finset Pt} {w : Pt → ℝ} (hsum : ∑ i ∈ s, w i = 1)
    {x : Pt} (hcombo : ∑ i ∈ s, w i • i = x) :
    gfun X Y x = ∑ i ∈ s, w i * gfun X Y i := by
  have e := congrArg (⇑(lineMap X Y)) hcombo
  rw [map_sum] at e
  simp_rw [map_smul, smul_eq_mul] at e
  have h2 : ∑ i ∈ s, w i * gfun X Y i
      = ∑ i ∈ s, w i * lineMap X Y i - (∑ i ∈ s, w i) * lineMap X Y X := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_sub]
  rw [h2, e, hsum, one_mul]

/-- Sum over a three-element finset. -/
theorem sum3gen {M : Type*} [AddCommMonoid M] {a b c : Pt} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (f : Pt → M) :
    ∑ i ∈ ({a, b, c} : Finset Pt), f i = f a + f b + f c := by
  rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
    Finset.sum_singleton, add_assoc]

/-- If `p` lies on the zero level set of `gfun X Y`, then `X, Y, p` are collinear. -/
theorem collinear_of_gfun_eq_zero {X Y p : Pt} (hXY : X ≠ Y) (h : gfun X Y p = 0) :
    Collinear ℝ ({X, Y, p} : Set Pt) := by
  rw [collinear_iff_of_mem (show X ∈ ({X, Y, p} : Set Pt) by simp)]
  refine ⟨Y - X, fun q hq => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with h1 | h1 | h1
  · exact ⟨0, by simp [h1]⟩
  · exact ⟨1, by simp [h1, vadd_eq_add]⟩
  · -- the case `q = p` is the interesting one
    obtain ⟨r, hr⟩ : ∃ r : ℝ, p = r • (Y - X) +ᵥ X := by
      have h2 : (X 1 - Y 1) * (p 0 - X 0) = (X 0 - Y 0) * (p 1 - X 1) := by
        have h' : (X 1 - Y 1) * p 0 - (X 0 - Y 0) * p 1
            = (X 1 - Y 1) * X 0 - (X 0 - Y 0) * X 1 := by
          have h'' := sub_eq_zero.1 h
          rwa [lineMap_apply, lineMap_apply] at h''
        linear_combination h'
      have hcd : Y 0 - X 0 ≠ 0 ∨ Y 1 - X 1 ≠ 0 := by
        by_contra hc
        push Not at hc
        apply hXY
        apply PiLp.ext
        rw [Fin.forall_fin_two]
        exact ⟨(sub_eq_zero.1 hc.1).symm, (sub_eq_zero.1 hc.2).symm⟩
      rcases hcd with hc | hd
      · refine ⟨(p 0 - X 0) / (Y 0 - X 0), ?_⟩
        have e0 : (p 0 - X 0) / (Y 0 - X 0) * (Y 0 - X 0) = p 0 - X 0 := div_mul_cancel₀ _ hc
        have hdet : (Y 1 - X 1) * (p 0 - X 0) = (Y 0 - X 0) * (p 1 - X 1) := by
          linear_combination -h2
        have e1 : (p 0 - X 0) / (Y 0 - X 0) * (Y 1 - X 1) = p 1 - X 1 := by
          field_simp [hc]
          linear_combination hdet
        apply PiLp.ext
        rw [Fin.forall_fin_two]
        constructor
        · simp only [vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
            smul_eq_mul]
          linarith [e0]
        · simp only [vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
            smul_eq_mul]
          linarith [e1]
      · refine ⟨(p 1 - X 1) / (Y 1 - X 1), ?_⟩
        have e1 : (p 1 - X 1) / (Y 1 - X 1) * (Y 1 - X 1) = p 1 - X 1 := div_mul_cancel₀ _ hd
        have hdet : (Y 0 - X 0) * (p 1 - X 1) = (Y 1 - X 1) * (p 0 - X 0) := by
          linear_combination h2
        have e0 : (p 1 - X 1) / (Y 1 - X 1) * (Y 0 - X 0) = p 0 - X 0 := by
          field_simp [hd]
          linear_combination hdet
        apply PiLp.ext
        rw [Fin.forall_fin_two]
        constructor
        · simp only [vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
            smul_eq_mul]
          linarith [e0]
        · simp only [vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
            smul_eq_mul]
          linarith [e1]
    exact ⟨r, h1.trans hr⟩

/-- If `B` and `C` are strictly on the same side of the line `X Y`, then `X` lies outside
the convex hull of `{B, C, Y}`. -/
theorem notMem_hull_pair {X Y B C : Pt} (hXY : X ≠ Y) (hBC : B ≠ C) (hBY : B ≠ Y)
    (hCY : C ≠ Y) (hgB : gfun X Y B ≠ 0) (hgC : gfun X Y C ≠ 0)
    (hg : 0 < gfun X Y B * gfun X Y C) :
    X ∉ convexHull ℝ (({B, C, Y} : Finset Pt) : Set Pt) := by
  intro hmem
  rw [Finset.mem_convexHull'] at hmem
  obtain ⟨w, hw, hsum, hcombo⟩ := hmem
  have hsum' : w B + w C + w Y = 1 := by rw [← hsum]; exact (sum3gen hBC hBY hCY w).symm
  have happ : gfun X Y X = w B * gfun X Y B + w C * gfun X Y C + w Y * gfun X Y Y := by
    rw [gfun_sum X Y hsum hcombo]; exact sum3gen hBC hBY hCY (fun i => w i * gfun X Y i)
  rw [gfun_self, gfun_right, mul_zero, add_zero] at happ
  have hbc0 : w B = 0 ∧ w C = 0 := by
    rcases mul_pos_iff.1 hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨e1, e2⟩ := (add_eq_zero_iff_of_nonneg (mul_nonneg (hw B (by simp)) h1.le)
        (mul_nonneg (hw C (by simp)) h2.le)).1 happ.symm
      refine ⟨?_, ?_⟩
      · rcases mul_eq_zero.1 e1 with h | h
        · exact h
        · exact absurd h hgB
      · rcases mul_eq_zero.1 e2 with h | h
        · exact h
        · exact absurd h hgC
    · have happ' : w B * (-gfun X Y B) + w C * (-gfun X Y C) = 0 := by linarith [happ]
      obtain ⟨e1, e2⟩ := (add_eq_zero_iff_of_nonneg
        (mul_nonneg (hw B (by simp)) (by linarith [h1.le]))
        (mul_nonneg (hw C (by simp)) (by linarith [h2.le]))).1 happ'
      refine ⟨?_, ?_⟩
      · rcases mul_eq_zero.1 e1 with h | h
        · exact h
        · exact absurd (neg_eq_zero.1 h) hgB
      · rcases mul_eq_zero.1 e2 with h | h
        · exact h
        · exact absurd (neg_eq_zero.1 h) hgC
  have hwY : w Y = 1 := by linarith [hsum']
  apply hXY
  have hc' : w B • B + w C • C + w Y • Y = X := by
    rw [← hcombo]; exact (sum3gen hBC hBY hCY (fun i => w i • i)).symm
  rw [hbc0.1, hbc0.2, hwY] at hc'
  simp only [zero_smul, one_smul, zero_add, add_zero] at hc'
  exact hc'.symm

/-- Auxiliary for `notMem_hull_vertex`: apex `R` with `0 < gfun P Q R`, a line-point `Z`
with `gfun P Q Z = 0`, and `X, Y` inside the triangle `P Q R` (both different from `R`).
Then `R` lies outside the convex hull of `{Z, X, Y}`. -/
theorem notMem_hull_vertex_aux {P Q R Z X Y : Pt} (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R)
    (hZX : Z ≠ X) (hZY : Z ≠ Y) (hXY : X ≠ Y)
    (hgR : 0 < gfun P Q R) (hgZ : gfun P Q Z = 0)
    (hXR : X ≠ R) (hYR : Y ≠ R)
    (hX : X ∈ convexHull ℝ (({P, Q, R} : Finset Pt) : Set Pt))
    (hY : Y ∈ convexHull ℝ (({P, Q, R} : Finset Pt) : Set Pt)) :
    R ∉ convexHull ℝ (({Z, X, Y} : Finset Pt) : Set Pt) := by
  have key : ∀ W : Pt, W ∈ convexHull ℝ (({P, Q, R} : Finset Pt) : Set Pt) → W ≠ R →
      gfun P Q W < gfun P Q R := by
    intro W hW hWR
    rw [Finset.mem_convexHull'] at hW
    obtain ⟨w, hw, hsum, hcombo⟩ := hW
    have hsum' : w P + w Q + w R = 1 := by rw [← hsum]; exact (sum3gen hPQ hPR hQR w).symm
    have hcombo' : w P • P + w Q • Q + w R • R = W := by
      rw [← hcombo]; exact (sum3gen hPQ hPR hQR (fun i => w i • i)).symm
    rw [gfun_sum P Q hsum hcombo, sum3gen hPQ hPR hQR (fun i => w i * gfun P Q i),
      gfun_self, gfun_right]
    simp only [mul_zero, add_zero, zero_add]
    by_cases hwR1 : w R = 1
    · exfalso
      have hwP0 : w P = 0 := by
        have h1 := hw P (by simp); have h2 := hw Q (by simp); linarith
      have hwQ0 : w Q = 0 := by
        have h1 := hw P (by simp); have h2 := hw Q (by simp); linarith
      rw [hwP0, hwQ0, hwR1] at hcombo'
      simp only [zero_smul, one_smul, zero_add, add_zero] at hcombo'
      exact hWR hcombo'.symm
    · have hwRle : w R ≤ 1 := by
        have h1 := hw P (by simp); have h2 := hw Q (by simp); linarith
      have hwRlt : w R < 1 := lt_of_le_of_ne hwRle hwR1
      calc w R * gfun P Q R < 1 * gfun P Q R := mul_lt_mul_of_pos_right hwRlt hgR
        _ = gfun P Q R := one_mul _
  have hgX := key X hX hXR
  have hgY := key Y hY hYR
  intro hmem
  rw [Finset.mem_convexHull'] at hmem
  obtain ⟨u, hu, husum, hucombo⟩ := hmem
  have hlt : ∀ i ∈ ({Z, X, Y} : Finset Pt), gfun P Q i < gfun P Q R := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · rw [hgZ]; exact hgR
    · exact hgX
    · exact hgY
  have happ : gfun P Q R = ∑ i ∈ ({Z, X, Y} : Finset Pt), u i * gfun P Q i :=
    gfun_sum P Q husum hucombo
  obtain ⟨i, hi, hui⟩ : ∃ i ∈ ({Z, X, Y} : Finset Pt), 0 < u i := by
    by_contra h
    push Not at h
    have h0 : ∑ i ∈ ({Z, X, Y} : Finset Pt), u i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i hi => hu i hi).2
        fun i hi => le_antisymm (h i hi) (hu i hi)
    rw [h0] at husum
    exact one_ne_zero husum.symm
  have hstrict : ∑ i ∈ ({Z, X, Y} : Finset Pt), u i * gfun P Q i
      < ∑ i ∈ ({Z, X, Y} : Finset Pt), u i * gfun P Q R :=
    Finset.sum_lt_sum (fun i hi => mul_le_mul_of_nonneg_left (hlt i hi).le (hu i hi))
      ⟨i, hi, mul_lt_mul_of_pos_left (hlt i hi) hui⟩
  rw [← Finset.sum_mul, husum, one_mul, ← happ] at hstrict
  exact lt_irrefl _ hstrict

/-- A vertex `R` of a genuine triangle `P Q R` lies outside the convex hull of
`{Q, X, Y}` when `X, Y` are points of the triangle different from `R`. -/
theorem notMem_hull_vertex {P Q R X Y : Pt} (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R)
    (hQX : Q ≠ X) (hQY : Q ≠ Y) (hXY : X ≠ Y)
    (hXR : X ≠ R) (hYR : Y ≠ R)
    (hncol : ¬Collinear ℝ ({P, Q, R} : Set Pt))
    (hX : X ∈ convexHull ℝ (({P, Q, R} : Finset Pt) : Set Pt))
    (hY : Y ∈ convexHull ℝ (({P, Q, R} : Finset Pt) : Set Pt)) :
    R ∉ convexHull ℝ (({Q, X, Y} : Finset Pt) : Set Pt) := by
  have hgR : gfun P Q R ≠ 0 := fun h => hncol (collinear_of_gfun_eq_zero hPQ h)
  rcases lt_or_gt_of_ne hgR with hneg | hpos
  · have hgR' : 0 < gfun Q P R := by rw [gfun_swap P Q R]; exact neg_pos_of_neg hneg
    have hX' : X ∈ convexHull ℝ (({Q, P, R} : Finset Pt) : Set Pt) := by
      rw [show ({Q, P, R} : Finset Pt) = {P, Q, R} from Finset.insert_comm Q P {R}]
      exact hX
    have hY' : Y ∈ convexHull ℝ (({Q, P, R} : Finset Pt) : Set Pt) := by
      rw [show ({Q, P, R} : Finset Pt) = {P, Q, R} from Finset.insert_comm Q P {R}]
      exact hY
    exact notMem_hull_vertex_aux hPQ.symm hQR hPR hQX hQY hXY hgR' (gfun_self Q P) hXR hYR
      hX' hY'
  · exact notMem_hull_vertex_aux hPQ hPR hQR hQX hQY hXY hpos (gfun_right P Q) hXR hYR hX hY

/-- Core geometric fact: if `X, Y` lie in the convex hull of the nondegenerate triangle
`A B C`, all five points are distinct, `{X, Y, B}` and `{X, Y, C}` are noncollinear, and
`B, C` lie strictly on the same side of the line `X Y`, then `{B, C, X, Y}` is in convex
position. -/
theorem core_convex {A B C X Y : Pt}
    (_hXA : X ≠ A) (hXB : X ≠ B) (hXC : X ≠ C)
    (_hYA : Y ≠ A) (hYB : Y ≠ B) (hYC : Y ≠ C)
    (hXY : X ≠ Y) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hncolABC : ¬Collinear ℝ ({A, B, C} : Set Pt))
    (hncolXB : ¬Collinear ℝ ({X, Y, B} : Set Pt))
    (hncolXC : ¬Collinear ℝ ({X, Y, C} : Set Pt))
    (hX : X ∈ convexHull ℝ (({A, B, C} : Finset Pt) : Set Pt))
    (hY : Y ∈ convexHull ℝ (({A, B, C} : Finset Pt) : Set Pt))
    (hg : 0 < gfun X Y B * gfun X Y C) :
    ConvexPosition ({B, C, X, Y} : Finset Pt) := by
  have hgB : gfun X Y B ≠ 0 := fun h => hncolXB (collinear_of_gfun_eq_zero hXY h)
  have hgC : gfun X Y C ≠ 0 := fun h => hncolXC (collinear_of_gfun_eq_zero hXY h)
  have h1 : X ∉ convexHull ℝ (({B, C, Y} : Finset Pt) : Set Pt) :=
    notMem_hull_pair hXY hBC hYB.symm hYC.symm hgB hgC hg
  have h2 : Y ∉ convexHull ℝ (({B, C, X} : Finset Pt) : Set Pt) := by
    have hgB' : gfun Y X B ≠ 0 := by
      rw [gfun_swap X Y B]; exact fun h => hgB (neg_eq_zero.1 h)
    have hgC' : gfun Y X C ≠ 0 := by
      rw [gfun_swap X Y C]; exact fun h => hgC (neg_eq_zero.1 h)
    have hg' : 0 < gfun Y X B * gfun Y X C := by
      rw [gfun_swap X Y B, gfun_swap X Y C, neg_mul_neg]; exact hg
    exact notMem_hull_pair hXY.symm hBC hXB.symm hXC.symm hgB' hgC' hg'
  have h3 : B ∉ convexHull ℝ (({C, X, Y} : Finset Pt) : Set Pt) := by
    have hnACB : ¬Collinear ℝ ({A, C, B} : Set Pt) := by
      rw [Set.pair_comm C B]; exact hncolABC
    have hX' : X ∈ convexHull ℝ (({A, C, B} : Finset Pt) : Set Pt) := by
      rw [Finset.pair_comm C B]; exact hX
    have hY' : Y ∈ convexHull ℝ (({A, C, B} : Finset Pt) : Set Pt) := by
      rw [Finset.pair_comm C B]; exact hY
    exact notMem_hull_vertex hAC hAB hBC.symm hXC.symm hYC.symm hXY hXB hYB hnACB hX' hY'
  have h4 : C ∉ convexHull ℝ (({B, X, Y} : Finset Pt) : Set Pt) :=
    notMem_hull_vertex hAB hAC hBC hXB.symm hYB.symm hXY hXC hYC hncolABC hX hY
  rw [ConvexPosition, convexIndependent_set_iff_notMem_convexHull_sdiff]
  intro z hz
  simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with hzB | hzC | hzX | hzY
  · rw [hzB]
    have e : (({B, C, X, Y} : Finset Pt) : Set Pt) \ {B}
        = (({C, X, Y} : Finset Pt) : Set Pt) := by
      rw [← Finset.coe_erase, Finset.erase_insert (by simp [hBC, hXB.symm, hYB.symm])]
    rw [e]; exact h3
  · rw [hzC]
    have e : (({B, C, X, Y} : Finset Pt) : Set Pt) \ {C}
        = (({B, X, Y} : Finset Pt) : Set Pt) := by
      rw [← Finset.coe_erase, Finset.erase_insert_of_ne hBC,
        Finset.erase_insert (by simp [hXC.symm, hYC.symm])]
    rw [e]; exact h4
  · rw [hzX]
    have e : (({B, C, X, Y} : Finset Pt) : Set Pt) \ {X}
        = (({B, C, Y} : Finset Pt) : Set Pt) := by
      rw [← Finset.coe_erase, Finset.erase_insert_of_ne hXB.symm,
        Finset.erase_insert_of_ne hXC.symm, Finset.erase_insert (by simp [hXY])]
    rw [e]; exact h1
  · rw [hzY]
    have e : (({B, C, X, Y} : Finset Pt) : Set Pt) \ {Y}
        = (({B, C, X} : Finset Pt) : Set Pt) := by
      rw [← Finset.coe_erase, Finset.erase_insert_of_ne hYB.symm,
        Finset.erase_insert_of_ne hYC.symm, Finset.erase_insert_of_ne hXY]
      simp
    rw [e]; exact h2

/-- Among three nonzero reals, two have the same sign. -/
theorem pigeonhole_sign {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    0 < a * b ∨ 0 < a * c ∨ 0 < b * c := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2, h3⟩ := h
  have hpos : 0 < (a * b) * (a * c) * (b * c) := by
    have hsq : (a * b) * (a * c) * (b * c) = (a * b * c) ^ 2 := by ring
    rw [hsq]
    exact sq_pos_of_ne_zero (mul_ne_zero (mul_ne_zero ha hb) hc)
  have h4 : 0 ≤ (a * b) * (a * c) := mul_nonneg_of_nonpos_of_nonpos h1 h2
  have h5 : (a * b) * (a * c) * (b * c) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h4 h3
  linarith

/-- The geometric heart of the problem: among any five points of the given
configuration, some four are the vertices of a convex quadrilateral.

Proof outline (following the standard solution): either the five points are already
in convex position (and any four of them work), or some point lies in the convex
hull of the other four. In the latter case, either those four are in convex
position, or some two of the five points lie inside the triangle formed by the
remaining three; then two vertices of that triangle lie on the same side of the
line through the two interior points, and those two vertices together with the two
interior points form a convex quadrilateral. -/
theorem exists_convexPosition_of_five {T : Finset Pt} (hT : T.card = 5)
    (hcol : ∀ p₁ ∈ T, ∀ p₂ ∈ T, ∀ p₃ ∈ T, p₁ ≠ p₂ → p₁ ≠ p₃ → p₂ ≠ p₃ →
      ¬ Collinear ℝ {p₁, p₂, p₃}) :
    ∃ Q ⊆ T, Q.card = 4 ∧ ConvexPosition Q := by
  by_cases hconv : ConvexIndependent ℝ ((↑) : ↥(T : Set Pt) → Pt)
  · have hne : T.Nonempty := by rw [← Finset.card_pos, hT]; norm_num
    obtain ⟨p, hp⟩ := hne
    exact ⟨T.erase p, Finset.erase_subset _ _, by rw [Finset.card_erase_of_mem hp, hT],
      hconv.mono (Finset.coe_subset.2 (Finset.erase_subset _ _))⟩
  · rw [convexIndependent_set_iff_notMem_convexHull_sdiff] at hconv
    push Not at hconv
    obtain ⟨X, hXT', hXhull⟩ := hconv
    rw [Finset.mem_coe] at hXT'
    have hXR : X ∉ T.erase X := Finset.notMem_erase _ _
    have hcardR : (T.erase X).card = 4 := by rw [Finset.card_erase_of_mem hXT', hT]
    rw [← Finset.coe_erase] at hXhull
    by_cases hconvR : ConvexPosition (T.erase X)
    · exact ⟨T.erase X, Finset.erase_subset _ _, hcardR, hconvR⟩
    · rw [ConvexPosition, convexIndependent_set_iff_notMem_convexHull_sdiff] at hconvR
      push Not at hconvR
      obtain ⟨Y, hYR', hYhull⟩ := hconvR
      rw [Finset.mem_coe] at hYR'
      have hYU : Y ∉ (T.erase X).erase Y := Finset.notMem_erase _ _
      have hcardU : ((T.erase X).erase Y).card = 3 := by
        rw [Finset.card_erase_of_mem hYR', hcardR]
      rw [← Finset.coe_erase] at hYhull
      have hYeq : insert Y ((T.erase X).erase Y) = T.erase X := Finset.insert_erase hYR'
      have hXhullU : X ∈ convexHull ℝ (((T.erase X).erase Y : Finset Pt) : Set Pt) := by
        have hsub : ((T.erase X : Finset Pt) : Set Pt) ⊆
            convexHull ℝ (((T.erase X).erase Y : Finset Pt) : Set Pt) := by
          intro p hp
          rw [← hYeq, Finset.coe_insert, Set.mem_insert_iff] at hp
          rcases hp with rfl | hpU
          · exact hYhull
          · exact subset_convexHull ℝ _ hpU
        exact convexHull_min hsub (convex_convexHull ℝ _) hXhull
      obtain ⟨A, B, C, hAB, hAC, hBC, hUeq⟩ := Finset.card_eq_three.1 hcardU
      have hYmem : Y ∈ T := Finset.erase_subset _ _ hYR'
      have hAU : A ∈ (T.erase X).erase Y := by rw [hUeq]; exact Finset.mem_insert_self _ _
      have hBU : B ∈ (T.erase X).erase Y := by rw [hUeq]; simp
      have hCU : C ∈ (T.erase X).erase Y := by rw [hUeq]; simp
      have hAR : A ∈ T.erase X := Finset.erase_subset _ _ hAU
      have hBR : B ∈ T.erase X := Finset.erase_subset _ _ hBU
      have hCR : C ∈ T.erase X := Finset.erase_subset _ _ hCU
      have hAT : A ∈ T := Finset.erase_subset _ _ hAR
      have hBT : B ∈ T := Finset.erase_subset _ _ hBR
      have hCT : C ∈ T := Finset.erase_subset _ _ hCR
      have hXY : X ≠ Y := by rintro rfl; exact hXR hYR'
      have hXA : X ≠ A := by rintro rfl; exact hXR hAR
      have hXB : X ≠ B := by rintro rfl; exact hXR hBR
      have hXC : X ≠ C := by rintro rfl; exact hXR hCR
      have hYA : Y ≠ A := by rintro rfl; exact hYU hAU
      have hYB : Y ≠ B := by rintro rfl; exact hYU hBU
      have hYC : Y ≠ C := by rintro rfl; exact hYU hCU
      have hXh : X ∈ convexHull ℝ (({A, B, C} : Finset Pt) : Set Pt) := hUeq ▸ hXhullU
      have hYh : Y ∈ convexHull ℝ (({A, B, C} : Finset Pt) : Set Pt) := hUeq ▸ hYhull
      have hnABC : ¬Collinear ℝ ({A, B, C} : Set Pt) := hcol A hAT B hBT C hCT hAB hAC hBC
      have hnXYA : ¬Collinear ℝ ({X, Y, A} : Set Pt) :=
        hcol X hXT' Y hYmem A hAT hXY hXA hYA
      have hnXYB : ¬Collinear ℝ ({X, Y, B} : Set Pt) :=
        hcol X hXT' Y hYmem B hBT hXY hXB hYB
      have hnXYC : ¬Collinear ℝ ({X, Y, C} : Set Pt) :=
        hcol X hXT' Y hYmem C hCT hXY hXC hYC
      have hgA : gfun X Y A ≠ 0 := fun h => hnXYA (collinear_of_gfun_eq_zero hXY h)
      have hgB : gfun X Y B ≠ 0 := fun h => hnXYB (collinear_of_gfun_eq_zero hXY h)
      have hgC : gfun X Y C ≠ 0 := fun h => hnXYC (collinear_of_gfun_eq_zero hXY h)
      rcases pigeonhole_sign hgA hgB hgC with hg | hg | hg
      · -- `A, B` on the same side of line `X Y`: take `Q = {A, B, X, Y}`
        have hcv : ConvexPosition ({A, B, X, Y} : Finset Pt) := by
          have hnCAB : ¬Collinear ℝ ({C, A, B} : Set Pt) := by
            rw [Set.insert_comm C A {B}, Set.pair_comm C B]; exact hnABC
          have hX' : X ∈ convexHull ℝ (({C, A, B} : Finset Pt) : Set Pt) := by
            rw [Finset.insert_comm C A {B}, Finset.pair_comm C B]; exact hXh
          have hY' : Y ∈ convexHull ℝ (({C, A, B} : Finset Pt) : Set Pt) := by
            rw [Finset.insert_comm C A {B}, Finset.pair_comm C B]; exact hYh
          exact core_convex hXC hXA hXB hYC hYA hYB hXY hAC.symm hBC.symm hAB hnCAB
            hnXYA hnXYB hX' hY' hg
        exact ⟨{A, B, X, Y},
          Finset.insert_subset_iff.2 ⟨hAT, Finset.insert_subset_iff.2 ⟨hBT,
            Finset.insert_subset_iff.2 ⟨hXT', Finset.singleton_subset_iff.2 hYmem⟩⟩⟩,
          Finset.card_eq_four.2 ⟨A, B, X, Y, hAB, hXA.symm, hYA.symm, hXB.symm, hYB.symm,
            hXY, rfl⟩,
          hcv⟩
      · -- `A, C` on the same side of line `X Y`: take `Q = {A, C, X, Y}`
        have hcv : ConvexPosition ({A, C, X, Y} : Finset Pt) := by
          have hnBAC : ¬Collinear ℝ ({B, A, C} : Set Pt) := by
            rw [Set.insert_comm B A {C}]; exact hnABC
          have hX' : X ∈ convexHull ℝ (({B, A, C} : Finset Pt) : Set Pt) := by
            rw [Finset.insert_comm B A {C}]; exact hXh
          have hY' : Y ∈ convexHull ℝ (({B, A, C} : Finset Pt) : Set Pt) := by
            rw [Finset.insert_comm B A {C}]; exact hYh
          exact core_convex hXB hXA hXC hYB hYA hYC hXY hAB.symm hBC hAC hnBAC
            hnXYA hnXYC hX' hY' hg
        exact ⟨{A, C, X, Y},
          Finset.insert_subset_iff.2 ⟨hAT, Finset.insert_subset_iff.2 ⟨hCT,
            Finset.insert_subset_iff.2 ⟨hXT', Finset.singleton_subset_iff.2 hYmem⟩⟩⟩,
          Finset.card_eq_four.2 ⟨A, C, X, Y, hAC, hXA.symm, hYA.symm, hXC.symm, hYC.symm,
            hXY, rfl⟩,
          hcv⟩
      · -- `B, C` on the same side of line `X Y`: take `Q = {B, C, X, Y}`
        have hcv : ConvexPosition ({B, C, X, Y} : Finset Pt) :=
          core_convex hXA hXB hXC hYA hYB hYC hXY hAB hAC hBC hnABC hnXYB hnXYC hXh hYh hg
        exact ⟨{B, C, X, Y},
          Finset.insert_subset_iff.2 ⟨hBT, Finset.insert_subset_iff.2 ⟨hCT,
            Finset.insert_subset_iff.2 ⟨hXT', Finset.singleton_subset_iff.2 hYmem⟩⟩⟩,
          Finset.card_eq_four.2 ⟨B, C, X, Y, hBC, hXB.symm, hYB.symm, hXC.symm, hYC.symm,
            hXY, rfl⟩,
          hcv⟩

/-- Double counting: every 5-element subset contains a convex quadrilateral, and
every convex quadrilateral lies in exactly `n - 4` five-element subsets. -/
theorem card_fives_le {n : ℕ} {S : Finset Pt} (hcard : S.card = n)
    (h : ∀ T ∈ S.powersetCard 5, ∃ Q ∈ convexQuads S, Q ⊆ T) :
    n.choose 5 ≤ (convexQuads S).card * (n - 4) := by
  classical
  -- The number of 5-subsets containing a given convex quadrilateral `Q` is `n - 4`.
  have hfib : ∀ Q ∈ convexQuads S,
      ((S.powersetCard 5).filter fun T => Q ⊆ T).card ≤ n - 4 := by
    intro Q hQ
    obtain ⟨hQS, hQ4, -⟩ := mem_convexQuads.mp hQ
    have hmaps : Set.MapsTo (fun T => T \ Q)
        ((S.powersetCard 5).filter fun T => Q ⊆ T) ((S \ Q).powersetCard 1) := by
      intro T hT
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard] at hT
      obtain ⟨⟨hTS, hT5⟩, hQT⟩ := hT
      show T \ Q ∈ (S \ Q).powersetCard 1
      rw [Finset.mem_powersetCard]
      refine ⟨Finset.sdiff_subset_sdiff hTS (Finset.Subset.refl Q), ?_⟩
      rw [Finset.card_sdiff_of_subset hQT, hT5, hQ4]
    have hinj : Set.InjOn (fun T => T \ Q)
        (((S.powersetCard 5).filter fun T => Q ⊆ T) : Set (Finset Pt)) := by
      intro T₁ hT₁ T₂ hT₂ hsd
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard] at hT₁ hT₂
      obtain ⟨⟨-, -⟩, hQT₁⟩ := hT₁
      obtain ⟨⟨-, -⟩, hQT₂⟩ := hT₂
      have e1 := Finset.union_sdiff_of_subset hQT₁
      have e2 := Finset.union_sdiff_of_subset hQT₂
      dsimp only at hsd
      rw [hsd] at e1
      exact e1.symm.trans e2
    calc ((S.powersetCard 5).filter fun T => Q ⊆ T).card
        ≤ ((S \ Q).powersetCard 1).card := Finset.card_le_card_of_injOn _ hmaps hinj
      _ = ((S \ Q).card).choose 1 := Finset.card_powersetCard _ _
      _ = (S \ Q).card := Nat.choose_one_right _
      _ = n - 4 := by rw [Finset.card_sdiff_of_subset hQS, hcard, hQ4]
  -- Every 5-subset contains some convex quadrilateral, so the 5-subsets are covered
  -- by the fibers.
  have hsub : S.powersetCard 5 ⊆ (convexQuads S).biUnion
      (fun Q => (S.powersetCard 5).filter fun T => Q ⊆ T) := by
    intro T hT
    rw [Finset.mem_biUnion]
    obtain ⟨Q, hQ, hQT⟩ := h T hT
    exact ⟨Q, hQ, Finset.mem_filter.mpr ⟨hT, hQT⟩⟩
  calc n.choose 5
      = (S.powersetCard 5).card := by rw [Finset.card_powersetCard, hcard]
    _ ≤ ((convexQuads S).biUnion fun Q => (S.powersetCard 5).filter fun T => Q ⊆ T).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ Q ∈ convexQuads S, ((S.powersetCard 5).filter fun T => Q ⊆ T).card :=
        card_biUnion_le _ _
    _ ≤ ∑ _Q ∈ convexQuads S, (n - 4) := Finset.sum_le_sum hfib
    _ = (convexQuads S).card * (n - 4) := by
        simp [Finset.sum_const]

/-- For `n > 4`, `n * (n - 1) * (n - 2) ≥ 60 * (n - 4)` (as real numbers); indeed
`n * (n - 1) * (n - 2) - 60 * (n - 4) = (n - 5) * (n - 6) * (n + 8)`. -/
theorem sixty_mul_le {n : ℕ} (hn : 4 < n) :
    60 * ((n : ℝ) - 4) ≤ (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) := by
  rcases (by omega : n = 5 ∨ n = 6 ∨ 7 ≤ n) with rfl | rfl | h7
  · norm_num
  · norm_num
  · have h7' : (7 : ℝ) ≤ n := by exact_mod_cast h7
    nlinarith [mul_nonneg
      (mul_nonneg (show (0 : ℝ) ≤ (n : ℝ) - 5 by linarith)
        (show (0 : ℝ) ≤ (n : ℝ) - 6 by linarith))
      (show (0 : ℝ) ≤ (n : ℝ) + 8 by linarith)]

/-- The arithmetic step: `C(n,5) / (n - 4) ≥ (n - 3) * (n - 4) / 2` for `n > 4`. -/
theorem choose_bound {n : ℕ} (hn : 4 < n) {q : ℕ}
    (h : n.choose 5 ≤ q * (n - 4)) :
    ((n : ℝ) - 3) * ((n : ℝ) - 4) / 2 ≤ q := by
  have h5le : (5 : ℝ) ≤ n := by exact_mod_cast hn
  have h4 : 4 ≤ n := by omega
  -- The binomial coefficient `C(n,5)` as a real number.
  have hdesc : (n.descFactorial 5 : ℝ) =
      (n : ℝ) * (n - 1) * (n - 2) * (n - 3) * (n - 4) := by
    have hn1 : (1 : ℕ) ≤ n := by omega
    have hn2 : (2 : ℕ) ≤ n := by omega
    have hn3 : (3 : ℕ) ≤ n := by omega
    have hn4 : (4 : ℕ) ≤ n := by omega
    simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero, Nat.mul_one,
      Nat.cast_mul, Nat.cast_sub hn4, Nat.cast_sub hn3, Nat.cast_sub hn2, Nat.cast_sub hn1,
      Nat.cast_one]
    ring
  have hchoose : (n.choose 5 : ℝ) =
      (n : ℝ) * (n - 1) * (n - 2) * (n - 3) * (n - 4) / 120 := by
    have h120 : Nat.factorial 5 = 120 := by decide
    have e : n.descFactorial 5 = 120 * n.choose 5 := by
      rw [← h120]; exact Nat.descFactorial_eq_factorial_mul_choose n 5
    have e' : (n.descFactorial 5 : ℝ) = 120 * (n.choose 5 : ℝ) := by exact_mod_cast e
    rw [hdesc] at e'
    rw [eq_div_iff (by norm_num : (120 : ℝ) ≠ 0)]
    linarith [e']
  -- The assumed bound, cast to the reals.
  have hq1 : (n.choose 5 : ℝ) ≤ (q : ℝ) * ((n : ℝ) - 4) := by
    have h' := Nat.cast_le (α := ℝ).mpr h
    rw [Nat.cast_mul, Nat.cast_sub h4] at h'
    exact h'
  have hpos : (0 : ℝ) < (n : ℝ) - 4 := by linarith
  -- Cancel the factor `n - 4`.
  have hqX : (n : ℝ) * (n - 1) * (n - 2) * (n - 3) / 120 ≤ q := by
    rw [hchoose] at hq1
    have e : (n : ℝ) * (n - 1) * (n - 2) * (n - 3) * (n - 4) / 120 =
        ((n : ℝ) * (n - 1) * (n - 2) * (n - 3) / 120) * ((n : ℝ) - 4) := by ring
    rw [e] at hq1
    exact le_of_mul_le_mul_right hq1 hpos
  -- Compare with `(n - 3) * (n - 4) / 2`.
  have hcore := sixty_mul_le hn
  have h30 : (0 : ℝ) ≤ (n : ℝ) - 3 := by linarith
  have h3 : ((n : ℝ) - 3) * ((n : ℝ) - 4) / 2 ≤
      ((n : ℝ) - 3) * ((n : ℝ) * (n - 1) * (n - 2) / 120) := by
    have h' : ((n : ℝ) - 4) / 2 ≤ (n : ℝ) * (n - 1) * (n - 2) / 120 := by linarith
    calc ((n : ℝ) - 3) * ((n : ℝ) - 4) / 2
        = ((n : ℝ) - 3) * (((n : ℝ) - 4) / 2) := by ring
      _ ≤ ((n : ℝ) - 3) * ((n : ℝ) * (n - 1) * (n - 2) / 120) :=
          mul_le_mul_of_nonneg_left h' h30
  have hqX' : ((n : ℝ) - 3) * ((n : ℝ) * (n - 1) * (n - 2) / 120) ≤ q := by
    have e : (n : ℝ) * (n - 1) * (n - 2) * (n - 3) / 120 =
        ((n : ℝ) - 3) * ((n : ℝ) * (n - 1) * (n - 2) / 120) := by ring
    rwa [e] at hqX
  exact h3.trans hqX'

snip end

problem imo1969_p5 (n : ℕ) (hn : 4 < n) (S : Finset Pt) (hcard : S.card = n)
    (hcol : ∀ p₁ ∈ S, ∀ p₂ ∈ S, ∀ p₃ ∈ S, p₁ ≠ p₂ → p₁ ≠ p₃ → p₂ ≠ p₃ →
      ¬ Collinear ℝ {p₁, p₂, p₃}) :
    ((n : ℝ) - 3) * ((n : ℝ) - 4) / 2 ≤ (convexQuads S).card := by
  classical
  apply choose_bound hn
  apply card_fives_le hcard
  intro T hT
  rw [Finset.mem_powersetCard] at hT
  obtain ⟨hTS, hT5⟩ := hT
  obtain ⟨Q, hQT, hQ4, hQconv⟩ := exists_convexPosition_of_five hT5
    (fun p₁ h₁ p₂ h₂ p₃ h₃ h₁₂ h₁₃ h₂₃ =>
      hcol p₁ (hTS h₁) p₂ (hTS h₂) p₃ (hTS h₃) h₁₂ h₁₃ h₂₃)
  exact ⟨Q, mem_convexQuads.mpr ⟨hQT.trans hTS, hQ4, hQconv⟩, hQT⟩

end Imo1969P5
