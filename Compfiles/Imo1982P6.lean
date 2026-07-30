/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.Monotone
public import Mathlib.Topology.Sequences
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1982, Problem 6

Let S be a square with sides length 100. Let L be a path within S which does
not meet itself and which is composed of line segments A₀A₁, A₁A₂, A₂A₃, ...,
Aₙ₋₁Aₙ with A₀ = Aₙ. Suppose that for every point P on the boundary of S there
is a point of L at a distance from P no greater than 1/2. Prove that there are
two points X and Y of L such that the distance between X and Y is not greater
than 1 and the length of the part of L which lies between X and Y is not
smaller than 198.

## Formalization notes

We parametrize the polygonal path `L` by arc length: `γ : ℝ → Pt` is the
parametrization, with parameter range `Icc 0 T` where `T` is the total length
of `L`. The hypotheses of the problem then become:
* `hcont` : `γ` is continuous on `Icc 0 T`;
* `hlip` : `γ` is `1`-Lipschitz (the chord is at most the arc length);
* `h0T` : `γ 0 = γ T` (the path is closed, `A₀ = Aₙ`);
* `hsimple` : `γ` is injective on `Ico 0 T` (the path does not meet itself);
* `hin` : the path stays within the square;
* `hbdy` : every point of the boundary of the square is within distance `1/2`
  of some point of the path.
The square is described by its four vertices `a b c d` (in order) via the four
side lengths and the four right angles. With the arc length parametrization,
the length of the part of `L` between `X = γ s` and `Y = γ t` (with `s ≤ t`)
is `t - s`, so the conclusion asserts the existence of `s t ∈ Icc 0 T` with
`dist (γ s) (γ t) ≤ 1` and `198 ≤ t - s`.
-/

namespace Imo1982P6

open Set Filter
open scoped RealInnerProductSpace InnerProductSpace Convex Topology

/-- The Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

snip begin

/-- The set of parameters `t ∈ Icc 0 T` at which the curve `γ` passes within
distance `1/2` of the point `p`. -/
def approachSet (γ : ℝ → Pt) (T : ℝ) (p : Pt) : Set ℝ :=
  {t ∈ Icc 0 T | dist (γ t) p ≤ 1 / 2}

lemma approachSet_bddBelow (γ : ℝ → Pt) (T : ℝ) (p : Pt) :
    BddBelow (approachSet γ T p) :=
  ⟨0, fun _t ht => ht.1.1⟩

/-- The set of parameters in `Icc u v` at which `γ` passes within distance
`1/2` of `p` is closed. -/
lemma isClosed_approachOn {γ : ℝ → Pt} {u v : ℝ} (hcont : ContinuousOn γ (Icc u v))
    (p : Pt) : IsClosed {t ∈ Icc u v | dist (γ t) p ≤ 1 / 2} := by
  apply IsSeqClosed.isClosed
  intro tn t htn ht
  have htI : t ∈ Icc u v :=
    isClosed_Icc.mem_of_tendsto ht (Filter.Eventually.of_forall fun n => (htn n).1)
  refine ⟨htI, ?_⟩
  have hu : Tendsto tn atTop (𝓝[Icc u v] t) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht, Filter.Eventually.of_forall fun n => (htn n).1⟩
  have hdist : Tendsto (fun n => dist (γ (tn n)) p) atTop (𝓝 (dist (γ t) p)) :=
    (Filter.Tendsto.comp (hcont t htI) hu).dist tendsto_const_nhds
  exact le_of_tendsto hdist (Filter.Eventually.of_forall fun n => (htn n).2)

lemma approachSet_isClosed {γ : ℝ → Pt} {T : ℝ} (hcont : ContinuousOn γ (Icc 0 T))
    (p : Pt) : IsClosed (approachSet γ T p) :=
  isClosed_approachOn hcont p

/-- The first time at which the curve approaches `p` is attained. -/
lemma firstApproach_mem {γ : ℝ → Pt} {T : ℝ} (hcont : ContinuousOn γ (Icc 0 T))
    {p : Pt} (hp : (approachSet γ T p).Nonempty) :
    sInf (approachSet γ T p) ∈ approachSet γ T p :=
  (approachSet_isClosed hcont p).csInf_mem hp (approachSet_bddBelow γ T p)

/-- Two points that are more than `1` apart cannot be approached at the same
parameter. -/
lemma firstApproach_ne {γ : ℝ → Pt} {T : ℝ} (hcont : ContinuousOn γ (Icc 0 T))
    {p q : Pt} (hp : (approachSet γ T p).Nonempty) (hq : (approachSet γ T q).Nonempty)
    (hpq : 1 < dist p q) :
    sInf (approachSet γ T p) ≠ sInf (approachSet γ T q) := by
  intro h
  have hp' := firstApproach_mem hcont hp
  rw [h] at hp'
  have hq' := firstApproach_mem hcont hq
  have hd := dist_triangle p (γ (sInf (approachSet γ T q))) q
  rw [dist_comm p (γ _)] at hd
  linarith [hp'.2, hq'.2, hpq, hd]

/-- In a right angle with legs of length `100`, any point of one leg is at
distance at least `100` from the far endpoint of the other leg. -/
lemma dist_ge_100_of_mem_segment {a b d : Pt}
    (hab : dist a b = 100) (had : dist a d = 100) (horth : ⟪b - a, d - a⟫_ℝ = 0)
    {x : Pt} (hx : x ∈ [a -[ℝ] d]) : 100 ≤ dist x b := by
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨u, -, rfl⟩ := hx
  rw [AffineMap.lineMap_apply_module, dist_comm ((1 - u) • a + u • d) b, dist_eq_norm]
  have key : b - ((1 - u) • a + u • d) = (b - a) - u • (d - a) := by module
  have hnorm : ‖b - ((1 - u) • a + u • d)‖ ^ 2 = ‖b - a‖ ^ 2 + u ^ 2 * ‖d - a‖ ^ 2 := by
    rw [key, norm_sub_sq_real, real_inner_smul_right, horth, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs]
    ring
  have hba : ‖b - a‖ = 100 := by rw [← dist_eq_norm, dist_comm b]; exact hab
  have hda : ‖d - a‖ = 100 := by rw [← dist_eq_norm, dist_comm d]; exact had
  have hsq : (100 : ℝ) ^ 2 ≤ ‖b - ((1 - u) • a + u • d)‖ ^ 2 := by
    rw [hnorm, hba, hda]
    exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg u) (by norm_num))
  by_contra hc
  replace hc := not_le.mp hc
  have hlt : ‖b - ((1 - u) • a + u • d)‖ ^ 2 < (100 : ℝ) ^ 2 := by
    nlinarith [norm_nonneg (b - ((1 - u) • a + u • d)), hc]
  linarith

/-- The diagonal of a square of side `100` has length `100 * √2`, which is
greater than `1`. -/
lemma one_lt_dist_of_right_angle {a b d : Pt}
    (hab : dist a b = 100) (had : dist a d = 100) (horth : ⟪b - a, d - a⟫_ℝ = 0) :
    1 < dist b d := by
  have key : b - d = (b - a) - (d - a) := by abel
  rw [dist_eq_norm, key]
  have hnorm : ‖(b - a) - (d - a)‖ ^ 2 = ‖b - a‖ ^ 2 + ‖d - a‖ ^ 2 := by
    rw [norm_sub_sq_real, horth, mul_zero, sub_zero]
  have hba : ‖b - a‖ = 100 := by rw [← dist_eq_norm, dist_comm b]; exact hab
  have hda : ‖d - a‖ = 100 := by rw [← dist_eq_norm, dist_comm d]; exact had
  rw [hba, hda] at hnorm
  by_contra hc
  replace hc := not_lt.mp hc
  have hle : ‖(b - a) - (d - a)‖ ^ 2 ≤ (1 : ℝ) ^ 2 := by
    nlinarith [norm_nonneg ((b - a) - (d - a)), hc]
  nlinarith [hnorm, hle]

/-- The set of points of the plane that are within distance `1/2` of some
point of the curve with parameter in `Icc u v` is closed. -/
lemma isClosed_approachedOn {γ : ℝ → Pt} {u v : ℝ} (hcont : ContinuousOn γ (Icc u v)) :
    IsClosed {x : Pt | ∃ t ∈ Icc u v, dist (γ t) x ≤ 1 / 2} := by
  apply IsSeqClosed.isClosed
  intro xn x hxn hx
  simp only [Set.mem_setOf_eq] at hxn
  choose t ht htd using hxn
  obtain ⟨t', ht', φ, hφ, hφlim⟩ := isCompact_Icc.tendsto_subseq ht
  refine ⟨t', ht', ?_⟩
  have hu : Tendsto (fun n => t (φ n)) atTop (𝓝[Icc u v] t') :=
    tendsto_nhdsWithin_iff.mpr ⟨hφlim, Filter.Eventually.of_forall fun n => ht (φ n)⟩
  have hdist : Tendsto (fun n => dist (γ (t (φ n))) (xn (φ n))) atTop
      (𝓝 (dist (γ t') x)) :=
    (Filter.Tendsto.comp (hcont t' ht') hu).dist (hx.comp hφ.tendsto_atTop)
  exact le_of_tendsto hdist (Filter.Eventually.of_forall fun n => htd (φ n))

/-- The heart of the proof. Suppose that `a b d` are three vertices of the
square, with the right angle at `a` (so that `a d` and `a b` are sides), that
`a` is approached by the curve no later than `b`, and that `b` is approached
strictly before `d`. Then the two required points of the curve exist. -/
theorem exists_pair_of_first_vertex
    {γ : ℝ → Pt} {T : ℝ}
    (hcont : ContinuousOn γ (Icc 0 T))
    (hlip : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, dist (γ s) (γ t) ≤ |s - t|)
    {a b d : Pt}
    (hab : dist a b = 100) (had : dist a d = 100) (horth : ⟪b - a, d - a⟫_ℝ = 0)
    (hside : ∀ p ∈ [a -[ℝ] d], (approachSet γ T p).Nonempty)
    (hb : (approachSet γ T b).Nonempty)
    (hτab : sInf (approachSet γ T a) ≤ sInf (approachSet γ T b))
    (hτbd : sInf (approachSet γ T b) < sInf (approachSet γ T d)) :
    ∃ s t : ℝ, s ∈ Icc 0 T ∧ t ∈ Icc 0 T ∧ dist (γ s) (γ t) ≤ 1 ∧ 198 ≤ t - s := by
  have ha : (approachSet γ T a).Nonempty := hside a (left_mem_segment ℝ a d)
  set tA := sInf (approachSet γ T a) with htA_def
  set tB := sInf (approachSet γ T b) with htB_def
  have htB : tB ∈ approachSet γ T b := by rw [htB_def]; exact firstApproach_mem hcont hb
  have htA : tA ∈ approachSet γ T a := by rw [htA_def]; exact firstApproach_mem hcont ha
  obtain ⟨htBIcc, hBb⟩ := htB
  obtain ⟨htAIcc, hAa⟩ := htA
  -- The set of points of the side `a d` approached with parameter in
  -- `Icc 0 tB` is compact and nonempty.
  have hsegc : IsCompact [a -[ℝ] d] := by
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have hclosed : IsClosed {x : Pt | ∃ t ∈ Icc 0 tB, dist (γ t) x ≤ 1 / 2} :=
    isClosed_approachedOn (hcont.mono (Icc_subset_Icc_right htBIcc.2))
  have hcomp : IsCompact ([a -[ℝ] d] ∩ {x : Pt | ∃ t ∈ Icc 0 tB, dist (γ t) x ≤ 1 / 2}) :=
    hsegc.inter_right hclosed
  have hne : ([a -[ℝ] d] ∩ {x : Pt | ∃ t ∈ Icc 0 tB, dist (γ t) x ≤ 1 / 2}).Nonempty :=
    ⟨a, left_mem_segment ℝ a d, tA, ⟨htAIcc.1, hτab⟩, hAa⟩
  -- Take `X'`, the point of the side `a d` approached with parameter `≤ tB`
  -- that is closest to `d`, and `X = γ tX` a corresponding point of the curve.
  obtain ⟨X', hX'mem, hX'min⟩ :=
    hcomp.exists_isMinOn hne (f := fun x => dist x d)
      ((continuous_id.dist continuous_const).continuousOn)
  replace hX'min : ∀ y ∈ [a -[ℝ] d] ∩ {x : Pt | ∃ t ∈ Icc 0 tB, dist (γ t) x ≤ 1 / 2},
      dist X' d ≤ dist y d := hX'min
  obtain ⟨hX'seg, tX, htXIcc, hXX'⟩ := hX'mem
  have hX'ne : X' ≠ d := by
    intro h
    have hmem : tX ∈ approachSet γ T d :=
      ⟨⟨htXIcc.1, htXIcc.2.trans htBIcc.2⟩, h ▸ hXX'⟩
    have hle : sInf (approachSet γ T d) ≤ tX := csInf_le (approachSet_bddBelow γ T d) hmem
    linarith [htXIcc.2, hτbd, hle]
  have hdX' : 0 < dist X' d := dist_pos.mpr hX'ne
  -- Every point of the side `a d` that is closer to `d` than `X'` must be
  -- approached with a parameter in `Icc tB T`.
  have hstep : ∀ y ∈ [a -[ℝ] d], dist y d < dist X' d →
      ∃ t ∈ Icc tB T, dist (γ t) y ≤ 1 / 2 := by
    intro y hyseg hyd
    obtain ⟨t, htIcc, hty⟩ := hside y hyseg
    by_cases ht : t ≤ tB
    · exact absurd (hX'min y ⟨hyseg, t, ⟨htIcc.1, ht⟩, hty⟩) (by linarith [hyd])
    · exact ⟨t, ⟨(not_le.mp ht).le, htIcc.2⟩, hty⟩
  -- By closedness, `X'` itself is approached with a parameter in `Icc tB T`;
  -- call `Y = γ tY` a corresponding point of the curve.
  have hX'2 : X' ∈ {x : Pt | ∃ t ∈ Icc tB T, dist (γ t) x ≤ 1 / 2} := by
    have hclosed2 : IsClosed {x : Pt | ∃ t ∈ Icc tB T, dist (γ t) x ≤ 1 / 2} :=
      isClosed_approachedOn (hcont.mono (Icc_subset_Icc_left htBIcc.1))
    rw [← hclosed2.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    have hnormdX' : ‖d - X'‖ = dist X' d := by rw [← dist_eq_norm, dist_comm d]
    set s := min (1 / 2 : ℝ) (ε / (2 * dist X' d)) with hs_def
    have hs_pos : 0 < s := by
      rw [hs_def]
      exact lt_min (by norm_num) (div_pos hε (mul_pos (by norm_num) hdX'))
    have hs_le : s ≤ 1 / 2 := by rw [hs_def]; exact min_le_left _ _
    have hs_le2 : s ≤ ε / (2 * dist X' d) := by rw [hs_def]; exact min_le_right _ _
    refine ⟨AffineMap.lineMap X' d s, ?_, ?_⟩
    · show ∃ t ∈ Icc tB T, dist (γ t) (AffineMap.lineMap X' d s) ≤ 1 / 2
      apply hstep
      · have hy1 : AffineMap.lineMap X' d s ∈ [X' -[ℝ] d] := by
          rw [segment_eq_image_lineMap]
          exact ⟨s, ⟨hs_pos.le, hs_le.trans (by norm_num)⟩, rfl⟩
        exact (convex_segment a d).segment_subset hX'seg (right_mem_segment ℝ a d) hy1
      · have hy : d - AffineMap.lineMap X' d s = (1 - s) • (d - X') := by
          rw [AffineMap.lineMap_apply_module]; module
        have h1 : (0 : ℝ) ≤ 1 - s := by linarith [hs_le]
        rw [dist_eq_norm, norm_sub_rev, hy, norm_smul, Real.norm_eq_abs, abs_of_nonneg h1,
          hnormdX']
        have h4 : (1 - s) * dist X' d = dist X' d - s * dist X' d := by ring
        rw [h4]
        have h6 := mul_pos hs_pos hdX'
        linarith
    · have hy : X' - AffineMap.lineMap X' d s = s • (X' - d) := by
        rw [AffineMap.lineMap_apply_module]; module
      rw [dist_eq_norm, hy, norm_smul, Real.norm_eq_abs, abs_of_pos hs_pos, ← dist_eq_norm]
      have h3 : s * dist X' d ≤ ε / 2 := by
        rw [← div_div] at hs_le2
        exact (le_div_iff₀ hdX').mp hs_le2
      linarith [hε]
  obtain ⟨tY, htYIcc, hX'Y⟩ := hX'2
  -- The distance estimates.
  have hX'b : 100 ≤ dist X' b := dist_ge_100_of_mem_segment hab had horth hX'seg
  have hXB : 99 ≤ dist (γ tX) (γ tB) := by
    have h1 := dist_triangle X' (γ tX) b
    have h2 := dist_triangle (γ tX) (γ tB) b
    rw [dist_comm X' (γ tX)] at h1
    linarith [hX'b, hXX', hBb, h1, h2]
  have hYB : 99 ≤ dist (γ tY) (γ tB) := by
    have h1 := dist_triangle X' (γ tY) b
    have h2 := dist_triangle (γ tY) (γ tB) b
    rw [dist_comm X' (γ tY)] at h1
    linarith [hX'b, hX'Y, hBb, h1, h2]
  -- The arc length estimates coming from the 1-Lipschitz property.
  have htXT : tX ∈ Icc 0 T := ⟨htXIcc.1, htXIcc.2.trans htBIcc.2⟩
  have htYT : tY ∈ Icc 0 T := ⟨htBIcc.1.trans htYIcc.1, htYIcc.2⟩
  have hs1 := hlip tX htXT tB htBIcc
  rw [abs_of_nonpos (sub_nonpos.mpr htXIcc.2)] at hs1
  have hs2 := hlip tB htBIcc tY htYT
  rw [abs_of_nonpos (sub_nonpos.mpr htYIcc.1), dist_comm (γ tB) (γ tY)] at hs2
  refine ⟨tX, tY, htXT, htYT, ?_, ?_⟩
  · have h1 := dist_triangle (γ tX) X' (γ tY)
    rw [dist_comm X' (γ tY)] at h1
    linarith [hXX', hX'Y, h1]
  · linarith [hXB, hs1, hYB, hs2]

snip end

problem imo1982_p6
    {a b c d : Pt}
    (hab : dist a b = 100) (hbc : dist b c = 100)
    (hcd : dist c d = 100) (hda : dist d a = 100)
    (ha : ⟪b - a, d - a⟫_ℝ = 0) (hb : ⟪a - b, c - b⟫_ℝ = 0)
    (hc : ⟪b - c, d - c⟫_ℝ = 0) (hd : ⟪c - d, a - d⟫_ℝ = 0)
    (γ : ℝ → Pt) (T : ℝ) (hT : 0 < T)
    (hcont : ContinuousOn γ (Icc 0 T))
    (hlip : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, dist (γ s) (γ t) ≤ |s - t|)
    (h0T : γ 0 = γ T)
    (hsimple : ∀ s ∈ Ico 0 T, ∀ t ∈ Ico 0 T, γ s = γ t → s = t)
    (hin : ∀ t ∈ Icc 0 T, γ t ∈ convexHull ℝ {a, b, c, d})
    (hbdy : ∀ p ∈ [a -[ℝ] b] ∪ [b -[ℝ] c] ∪ [c -[ℝ] d] ∪ [d -[ℝ] a],
        (approachSet γ T p).Nonempty) :
    ∃ s t : ℝ, s ∈ Icc 0 T ∧ t ∈ Icc 0 T ∧ dist (γ s) (γ t) ≤ 1 ∧ 198 ≤ t - s := by
  -- Each side of the square is approached by the curve.
  have side_ab : ∀ p ∈ [a -[ℝ] b], (approachSet γ T p).Nonempty :=
    fun p hp => hbdy p (Or.inl (Or.inl (Or.inl hp)))
  have side_bc : ∀ p ∈ [b -[ℝ] c], (approachSet γ T p).Nonempty :=
    fun p hp => hbdy p (Or.inl (Or.inl (Or.inr hp)))
  have side_cd : ∀ p ∈ [c -[ℝ] d], (approachSet γ T p).Nonempty :=
    fun p hp => hbdy p (Or.inl (Or.inr hp))
  have side_da : ∀ p ∈ [d -[ℝ] a], (approachSet γ T p).Nonempty :=
    fun p hp => hbdy p (Or.inr hp)
  have side_ad : ∀ p ∈ [a -[ℝ] d], (approachSet γ T p).Nonempty := by
    rw [segment_symm ℝ a d]; exact side_da
  have side_ba : ∀ p ∈ [b -[ℝ] a], (approachSet γ T p).Nonempty := by
    rw [segment_symm ℝ b a]; exact side_ab
  have side_cb : ∀ p ∈ [c -[ℝ] b], (approachSet γ T p).Nonempty := by
    rw [segment_symm ℝ c b]; exact side_bc
  have side_dc : ∀ p ∈ [d -[ℝ] c], (approachSet γ T p).Nonempty := by
    rw [segment_symm ℝ d c]; exact side_cd
  -- In particular each vertex is approached.
  have haN : (approachSet γ T a).Nonempty := side_ab a (left_mem_segment ℝ a b)
  have hbN : (approachSet γ T b).Nonempty := side_bc b (left_mem_segment ℝ b c)
  have hcN : (approachSet γ T c).Nonempty := side_cd c (left_mem_segment ℝ c d)
  have hdN : (approachSet γ T d).Nonempty := side_da d (left_mem_segment ℝ d a)
  -- The diagonals have length `100 * √2 > 1`.
  have hdiag_bd : 1 < dist b d :=
    one_lt_dist_of_right_angle hab (by rw [dist_comm]; exact hda) ha
  have hdiag_ac : 1 < dist a c :=
    one_lt_dist_of_right_angle (by rw [dist_comm]; exact hab) hbc hb
  have hdiag_ca : 1 < dist c a := by rw [dist_comm]; exact hdiag_ac
  -- The first approach times of the four vertices.
  set τa := sInf (approachSet γ T a)
  set τb := sInf (approachSet γ T b)
  set τc := sInf (approachSet γ T c)
  set τd := sInf (approachSet γ T d)
  -- Case split on which vertex is approached first, and on the order in which
  -- its two neighbours are approached.
  rcases le_total τa τb with h1 | h1 <;> rcases le_total τc τd with h2 | h2
  · rcases le_total τa τc with h3 | h3
    · -- `a` is approached first; neighbours `b` and `d`.
      have hne : τb ≠ τd := firstApproach_ne hcont hbN hdN hdiag_bd
      have had' : dist a d = 100 := by rw [dist_comm]; exact hda
      rcases lt_or_gt_of_ne hne with h | h
      · exact exists_pair_of_first_vertex hcont hlip hab had' ha side_ad hbN h1 h
      · exact exists_pair_of_first_vertex hcont hlip had' hab
          (by rw [real_inner_comm]; exact ha) side_ab hdN (h3.trans h2) h
    · -- `c` is approached first; neighbours `b` and `d`.
      have hne : τb ≠ τd := firstApproach_ne hcont hbN hdN hdiag_bd
      have hcb : dist c b = 100 := by rw [dist_comm]; exact hbc
      rcases lt_or_gt_of_ne hne with h | h
      · exact exists_pair_of_first_vertex hcont hlip hcb hcd hc side_cd hbN (h3.trans h1) h
      · exact exists_pair_of_first_vertex hcont hlip hcd hcb
          (by rw [real_inner_comm]; exact hc) side_cb hdN h2 h
  · rcases le_total τa τd with h3 | h3
    · -- `a` is approached first; neighbours `b` and `d`.
      have hne : τb ≠ τd := firstApproach_ne hcont hbN hdN hdiag_bd
      have had' : dist a d = 100 := by rw [dist_comm]; exact hda
      rcases lt_or_gt_of_ne hne with h | h
      · exact exists_pair_of_first_vertex hcont hlip hab had' ha side_ad hbN h1 h
      · exact exists_pair_of_first_vertex hcont hlip had' hab
          (by rw [real_inner_comm]; exact ha) side_ab hdN h3 h
    · -- `d` is approached first; neighbours `c` and `a`.
      have hne : τc ≠ τa := firstApproach_ne hcont hcN haN hdiag_ca
      have hdc : dist d c = 100 := by rw [dist_comm]; exact hcd
      rcases lt_or_gt_of_ne hne with h | h
      · exact exists_pair_of_first_vertex hcont hlip hdc hda hd side_da hcN h2 h
      · exact exists_pair_of_first_vertex hcont hlip hda hdc
          (by rw [real_inner_comm]; exact hd) side_dc haN h3 h
  · rcases le_total τb τc with h3 | h3
    · -- `b` is approached first; neighbours `a` and `c`.
      have hne : τa ≠ τc := firstApproach_ne hcont haN hcN hdiag_ac
      have hba : dist b a = 100 := by rw [dist_comm]; exact hab
      rcases lt_or_gt_of_ne hne with h | h
      · exact exists_pair_of_first_vertex hcont hlip hba hbc hb side_bc haN h1 h
      · exact exists_pair_of_first_vertex hcont hlip hbc hba
          (by rw [real_inner_comm]; exact hb) side_ba hcN h3 h
    · -- `c` is approached first; neighbours `b` and `d`.
      have hne : τb ≠ τd := firstApproach_ne hcont hbN hdN hdiag_bd
      have hcb : dist c b = 100 := by rw [dist_comm]; exact hbc
      rcases lt_or_gt_of_ne hne with h | h
      · exact exists_pair_of_first_vertex hcont hlip hcb hcd hc side_cd hbN h3 h
      · exact exists_pair_of_first_vertex hcont hlip hcd hcb
          (by rw [real_inner_comm]; exact hc) side_cb hdN h2 h
  · rcases le_total τb τd with h3 | h3
    · -- `b` is approached first; neighbours `a` and `c`.
      have hne : τa ≠ τc := firstApproach_ne hcont haN hcN hdiag_ac
      have hba : dist b a = 100 := by rw [dist_comm]; exact hab
      rcases lt_or_gt_of_ne hne with h | h
      · exact exists_pair_of_first_vertex hcont hlip hba hbc hb side_bc haN h1 h
      · exact exists_pair_of_first_vertex hcont hlip hbc hba
          (by rw [real_inner_comm]; exact hb) side_ba hcN (h3.trans h2) h
    · -- `d` is approached first; neighbours `c` and `a`.
      have hne : τc ≠ τa := firstApproach_ne hcont hcN haN hdiag_ca
      have hdc : dist d c = 100 := by rw [dist_comm]; exact hcd
      rcases lt_or_gt_of_ne hne with h | h
      · exact exists_pair_of_first_vertex hcont hlip hdc hda hd side_da hcN h2 h
      · exact exists_pair_of_first_vertex hcont hlip hda hdc
          (by rw [real_inner_comm]; exact hd) side_dc haN (h3.trans h1) h

end Imo1982P6
