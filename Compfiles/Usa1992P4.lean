/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.InnerProductSpace.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 1992, Problem 4

Three chords of a sphere meet at a point X inside the sphere but are not
coplanar. A sphere through an endpoint of each chord and X touches the sphere
through the other endpoints and X. Show that the chords have equal length.
-/

namespace Usa1992P4

open scoped InnerProductSpace

snip begin

/-!
### Proof outline

We give an algebraic proof using vectors (inner product spaces).

Translate so that `X` is the origin.  Write the three chords as pairs
`a, -α • a`, `b, -β • b`, `c, -γ • c` with `α, β, γ > 0`
(the point `X = 0` lies strictly between the two endpoints of each chord).

* Tangency of the two small spheres (both passing through `X = 0`) forces
  their centers `p, p'` to be collinear with `X`:  `parallel_of_tangent`.
  In fact `ρ • p' + ρ' • p = 0` (external tangency); the internal case is
  impossible since it would force `α < 0`.
* From `a, b, c` on the sphere centered at `p` and `-α • a, -β • b, -γ • c` on
  the sphere centered at `p'` we get `α = β = γ = ρ' / ρ`.
* The power of the point `X` with respect to the big sphere gives
  `α * ‖a‖² = β * ‖b‖² = γ * ‖c‖² = r² - ‖q‖²`, hence
  `‖a‖ = ‖b‖ = ‖c‖`.
* Each chord length is `(1 + α) * ‖a‖`, etc., so the three chords are equal.
-/

/-- If two spheres of radii `ρ, ρ'` centered at `p, p'` both pass through the
origin and are tangent to each other (`dist p p' = ρ + ρ'` externally or
`|ρ - ρ'|` internally), then the origin lies on the line through the centers:
`ρ • p' + ρ' • p = 0` (external) or `ρ • p' - ρ' • p = 0` (internal). -/
lemma parallel_of_tangent {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (p p' : V) {ρ ρ' : ℝ} (hρ : 0 < ρ) (hρ' : 0 < ρ')
    (hp : ‖p‖ = ρ) (hp' : ‖p'‖ = ρ')
    (h : ‖p - p'‖ = ρ + ρ' ∨ ‖p - p'‖ = |ρ - ρ'|) :
    ρ • p' + ρ' • p = 0 ∨ ρ • p' - ρ' • p = 0 := by
  have hp2 : ‖p‖ ^ 2 = ρ ^ 2 := by rw [hp]
  have hp'2 : ‖p'‖ ^ 2 = ρ' ^ 2 := by rw [hp']
  have hr1 : ‖(ρ : ℝ)‖ = ρ := Real.norm_of_nonneg hρ.le
  have hr2 : ‖(ρ' : ℝ)‖ = ρ' := Real.norm_of_nonneg hρ'.le
  rcases h with h | h
  · left
    have h2 : ‖p - p'‖ ^ 2 = (ρ + ρ') ^ 2 := by rw [h]
    rw [norm_sub_sq_real] at h2
    have hexp : (ρ + ρ') ^ 2 = ρ ^ 2 + 2 * (ρ * ρ') + ρ' ^ 2 := by ring
    have h_inner : ⟪p, p'⟫_ℝ = -(ρ * ρ') := by linarith
    have hz : ‖ρ • p' + ρ' • p‖ ^ 2 = 0 := by
      rw [norm_add_sq_real, norm_smul, norm_smul, hr1, hr2, real_inner_smul_left,
        real_inner_smul_right, real_inner_comm p p']
      linear_combination ρ ^ 2 * hp'2 + 2 * ρ * ρ' * h_inner + ρ' ^ 2 * hp2
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
  · right
    have h2 : ‖p - p'‖ ^ 2 = (ρ - ρ') ^ 2 := by rw [h, sq_abs]
    rw [norm_sub_sq_real] at h2
    have hexp : (ρ - ρ') ^ 2 = ρ ^ 2 - 2 * (ρ * ρ') + ρ' ^ 2 := by ring
    have h_inner : ⟪p, p'⟫_ℝ = ρ * ρ' := by linarith
    have hz : ‖ρ • p' - ρ' • p‖ ^ 2 = 0 := by
      rw [norm_sub_sq_real, norm_smul, norm_smul, hr1, hr2, real_inner_smul_left,
        real_inner_smul_right, real_inner_comm p p']
      linear_combination ρ ^ 2 * hp'2 - 2 * ρ * ρ' * h_inner + ρ' ^ 2 * hp2
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)

/-- Equations satisfied by one chord `v, -δ • v` (with `δ > 0`) through the
origin: the small-sphere equations give `‖v‖² = 2⟪v,p⟫` and
`δ‖v‖² = -2⟪v,p'⟫`, and the big-sphere equations give the power-of-a-point
relation `δ‖v‖² = r² - ‖q‖²`. -/
lemma sphere_eqs_of_chord {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {q p p' : V} {r ρ ρ' : ℝ}
    (hq : ‖q‖ < r) (hp0 : ‖p‖ = ρ) (hp0' : ‖p'‖ = ρ')
    (v : V) {δ : ℝ} (hδ : 0 < δ)
    (hv : ‖v - p‖ = ρ) (hv' : ‖-δ • v - p'‖ = ρ')
    (hw : ‖v - q‖ = r) (hw' : ‖-δ • v - q‖ = r) :
    δ * ‖v‖ ^ 2 = -2 * ⟪v, p'⟫_ℝ ∧ ‖v‖ ^ 2 = 2 * ⟪v, p⟫_ℝ ∧
      δ * ‖v‖ ^ 2 = r ^ 2 - ‖q‖ ^ 2 ∧ ‖v‖ ^ 2 ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `v, X` on the sphere centered at `p'`
    have nδ : ‖-δ • v‖ = δ * ‖v‖ := by
      rw [neg_smul, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
    have iδ : ⟪-δ • v, p'⟫_ℝ = -δ * ⟪v, p'⟫_ℝ := by rw [real_inner_smul_left]
    have h1 : ‖-δ • v - p'‖ ^ 2 = ‖p'‖ ^ 2 := by rw [hv', hp0']
    rw [norm_sub_sq_real, nδ, iδ] at h1
    have h2 : δ * (δ * ‖v‖ ^ 2 + 2 * ⟪v, p'⟫_ℝ) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h hδ.ne'
    · linarith
  · -- `v, X` on the sphere centered at `p`
    have h3 : ‖v - p‖ ^ 2 = ‖p‖ ^ 2 := by rw [hv, hp0]
    rw [norm_sub_sq_real] at h3
    linarith
  · -- power of the point `X = 0` with respect to the big sphere
    have nδ : ‖-δ • v‖ = δ * ‖v‖ := by
      rw [neg_smul, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
    have iδ : ⟪-δ • v, q⟫_ℝ = -δ * ⟪v, q⟫_ℝ := by rw [real_inner_smul_left]
    have d1 : ‖v‖ ^ 2 - 2 * ⟪v, q⟫_ℝ + ‖q‖ ^ 2 = r ^ 2 := by
      have h : ‖v - q‖ ^ 2 = r ^ 2 := by rw [hw]
      rwa [norm_sub_sq_real] at h
    have d2 : δ ^ 2 * ‖v‖ ^ 2 + 2 * δ * ⟪v, q⟫_ℝ + ‖q‖ ^ 2 = r ^ 2 := by
      have h : ‖-δ • v - q‖ ^ 2 = r ^ 2 := by rw [hw']
      rw [norm_sub_sq_real, nδ, iδ] at h
      linear_combination h
    have h_pow : δ * (δ + 1) * ‖v‖ ^ 2 = (δ + 1) * (r ^ 2 - ‖q‖ ^ 2) := by
      linear_combination d2 + δ * d1
    have hδ1 : (0 : ℝ) < δ + 1 := by linarith
    have hcancel : (δ + 1) * (δ * ‖v‖ ^ 2) = (δ + 1) * (r ^ 2 - ‖q‖ ^ 2) := by
      linear_combination h_pow
    exact mul_left_cancel₀ (ne_of_gt hδ1) hcancel
  · -- `v ≠ 0`, since `X` is strictly inside the big sphere
    intro h0
    have hv0 : v = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp h0)
    rw [hv0, zero_sub, norm_neg] at hw
    linarith

/-- Main algebraic step: with `X` at the origin, the three chords have equal
length. -/
lemma chord_length_eq_of_tangent {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {q : V} {r : ℝ} (hq : ‖q‖ < r)
    (a b c : V) {α β γ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (ha : ‖a - q‖ = r) (ha' : ‖-α • a - q‖ = r)
    (hb : ‖b - q‖ = r) (hb' : ‖-β • b - q‖ = r)
    (hc : ‖c - q‖ = r) (hc' : ‖-γ • c - q‖ = r)
    {p p' : V} {ρ ρ' : ℝ} (hρ : 0 < ρ) (hρ' : 0 < ρ')
    (hpa : ‖a - p‖ = ρ) (hpb : ‖b - p‖ = ρ) (hpc : ‖c - p‖ = ρ) (hp0 : ‖p‖ = ρ)
    (hpa' : ‖-α • a - p'‖ = ρ') (hpb' : ‖-β • b - p'‖ = ρ')
    (hpc' : ‖-γ • c - p'‖ = ρ') (hp0' : ‖p'‖ = ρ')
    (htouch : ‖p - p'‖ = ρ + ρ' ∨ ‖p - p'‖ = |ρ - ρ'|) :
    ‖a + α • a‖ = ‖b + β • b‖ ∧ ‖b + β • b‖ = ‖c + γ • c‖ := by
  rcases parallel_of_tangent p p' hρ hρ' hp0 hp0' htouch with hz | hz
  · -- external tangency: `ρ • p' = (-ρ') • p`
    have hrel : ∀ v : V, ρ * ⟪v, p'⟫_ℝ = -ρ' * ⟪v, p⟫_ℝ := by
      intro v
      have hz' : ρ • p' = (-ρ') • p := by
        have h2 : ρ • p' = -(ρ' • p) := add_eq_zero_iff_eq_neg.mp hz
        rwa [← neg_smul] at h2
      have h3 := congrArg (fun w => ⟪v, w⟫_ℝ) hz'
      rwa [real_inner_smul_right, real_inner_smul_right] at h3
    obtain ⟨P1a, P2a, P3a, P4a⟩ := sphere_eqs_of_chord hq hp0 hp0' a hα hpa hpa' ha ha'
    obtain ⟨P1b, P2b, P3b, P4b⟩ := sphere_eqs_of_chord hq hp0 hp0' b hβ hpb hpb' hb hb'
    obtain ⟨P1c, P2c, P3c, P4c⟩ := sphere_eqs_of_chord hq hp0 hp0' c hγ hpc hpc' hc hc'
    -- tangency gives `α = β = γ = ρ' / ρ`
    have hαρα : α * ρ = ρ' := by
      have h : (α * ρ) * ‖a‖ ^ 2 = ρ' * ‖a‖ ^ 2 := by
        linear_combination ρ * P1a - 2 * hrel a - ρ' * P2a
      exact mul_right_cancel₀ P4a h
    have hβρ : β * ρ = ρ' := by
      have h : (β * ρ) * ‖b‖ ^ 2 = ρ' * ‖b‖ ^ 2 := by
        linear_combination ρ * P1b - 2 * hrel b - ρ' * P2b
      exact mul_right_cancel₀ P4b h
    have hγρ : γ * ρ = ρ' := by
      have h : (γ * ρ) * ‖c‖ ^ 2 = ρ' * ‖c‖ ^ 2 := by
        linear_combination ρ * P1c - 2 * hrel c - ρ' * P2c
      exact mul_right_cancel₀ P4c h
    have hαβ : α = β := mul_right_cancel₀ (ne_of_gt hρ) (hαρα.trans hβρ.symm)
    have hβγ : β = γ := mul_right_cancel₀ (ne_of_gt hρ) (hβρ.trans hγρ.symm)
    -- power of the point then gives `‖a‖ = ‖b‖ = ‖c‖`
    have hnorm_ab : ‖a‖ ^ 2 = ‖b‖ ^ 2 := by
      rw [← hαβ] at P3b
      exact mul_left_cancel₀ (ne_of_gt hα) (P3a.trans P3b.symm)
    have hnorm_bc : ‖b‖ ^ 2 = ‖c‖ ^ 2 := by
      rw [← hβγ] at P3c
      exact mul_left_cancel₀ (ne_of_gt hβ) (P3b.trans P3c.symm)
    have hnorm_ab' : ‖a‖ = ‖b‖ := (sq_eq_sq₀ (norm_nonneg a) (norm_nonneg b)).mp hnorm_ab
    have hnorm_bc' : ‖b‖ = ‖c‖ := (sq_eq_sq₀ (norm_nonneg b) (norm_nonneg c)).mp hnorm_bc
    have fin : ∀ (v : V) (δ : ℝ), 0 < δ → ‖v + δ • v‖ = (1 + δ) * ‖v‖ := by
      intro v δ hδ
      have h1 : v + δ • v = (1 + δ) • v := by rw [add_smul, one_smul]
      rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos (show (0 : ℝ) < 1 + δ by linarith)]
    exact ⟨by rw [fin a α hα, fin b β hβ, hαβ, hnorm_ab'],
           by rw [fin b β hβ, fin c γ hγ, hβγ, hnorm_bc']⟩
  · -- internal tangency is impossible: it would force `α < 0`
    have hrel : ∀ v : V, ρ * ⟪v, p'⟫_ℝ = ρ' * ⟪v, p⟫_ℝ := by
      intro v
      have h3 := congrArg (fun w => ⟪v, w⟫_ℝ) (sub_eq_zero.mp hz)
      rwa [real_inner_smul_right, real_inner_smul_right] at h3
    obtain ⟨P1a, P2a, -, P4a⟩ := sphere_eqs_of_chord hq hp0 hp0' a hα hpa hpa' ha ha'
    exfalso
    have hαρα : α * ρ = -ρ' := by
      have h : (α * ρ) * ‖a‖ ^ 2 = (-ρ') * ‖a‖ ^ 2 := by
        linear_combination ρ * P1a - 2 * hrel a + ρ' * P2a
      exact mul_right_cancel₀ P4a h
    have hpos : (0 : ℝ) < α * ρ := mul_pos hα hρ
    linarith

snip end

problem usa1992_p4
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (o : V) {r : ℝ} (_hr : 0 < r)
    (x : V) (hx : dist x o < r)
    (A B C A' B' C' : V)
    (hA : dist A o = r) (hA' : dist A' o = r)
    (hB : dist B o = r) (hB' : dist B' o = r)
    (hC : dist C o = r) (hC' : dist C' o = r)
    (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hA'x : A' - x = -α • (A - x))
    (hB'x : B' - x = -β • (B - x))
    (hC'x : C' - x = -γ • (C - x))
    (_hlin : LinearIndependent ℝ ![A - x, B - x, C - x])
    (m m' : V) {ρ ρ' : ℝ} (hρ : 0 < ρ) (hρ' : 0 < ρ')
    (hmA : dist A m = ρ) (hmB : dist B m = ρ) (hmC : dist C m = ρ)
    (hmx : dist x m = ρ)
    (hmA' : dist A' m' = ρ') (hmB' : dist B' m' = ρ') (hmC' : dist C' m' = ρ')
    (hmx' : dist x m' = ρ')
    (htouch : dist m m' = ρ + ρ' ∨ dist m m' = |ρ - ρ'|) :
    dist A A' = dist B B' ∧ dist B B' = dist C C' := by
  -- translate so that `x` becomes the origin
  have hq : ‖o - x‖ < r := by rw [← dist_eq_norm, dist_comm]; exact hx
  have ha : ‖A - x - (o - x)‖ = r := by
    rw [sub_sub_sub_cancel_right, ← dist_eq_norm]; exact hA
  have ha' : ‖-α • (A - x) - (o - x)‖ = r := by
    rw [← hA'x, sub_sub_sub_cancel_right, ← dist_eq_norm]; exact hA'
  have hb : ‖B - x - (o - x)‖ = r := by
    rw [sub_sub_sub_cancel_right, ← dist_eq_norm]; exact hB
  have hb' : ‖-β • (B - x) - (o - x)‖ = r := by
    rw [← hB'x, sub_sub_sub_cancel_right, ← dist_eq_norm]; exact hB'
  have hc : ‖C - x - (o - x)‖ = r := by
    rw [sub_sub_sub_cancel_right, ← dist_eq_norm]; exact hC
  have hc' : ‖-γ • (C - x) - (o - x)‖ = r := by
    rw [← hC'x, sub_sub_sub_cancel_right, ← dist_eq_norm]; exact hC'
  have hpa : ‖A - x - (m - x)‖ = ρ := by
    rw [sub_sub_sub_cancel_right, ← dist_eq_norm]; exact hmA
  have hpb : ‖B - x - (m - x)‖ = ρ := by
    rw [sub_sub_sub_cancel_right, ← dist_eq_norm]; exact hmB
  have hpc : ‖C - x - (m - x)‖ = ρ := by
    rw [sub_sub_sub_cancel_right, ← dist_eq_norm]; exact hmC
  have hp0 : ‖m - x‖ = ρ := by rw [← dist_eq_norm, dist_comm]; exact hmx
  have hpa' : ‖-α • (A - x) - (m' - x)‖ = ρ' := by
    rw [← hA'x, sub_sub_sub_cancel_right, ← dist_eq_norm]; exact hmA'
  have hpb' : ‖-β • (B - x) - (m' - x)‖ = ρ' := by
    rw [← hB'x, sub_sub_sub_cancel_right, ← dist_eq_norm]; exact hmB'
  have hpc' : ‖-γ • (C - x) - (m' - x)‖ = ρ' := by
    rw [← hC'x, sub_sub_sub_cancel_right, ← dist_eq_norm]; exact hmC'
  have hp0' : ‖m' - x‖ = ρ' := by rw [← dist_eq_norm, dist_comm]; exact hmx'
  have htouch' : ‖m - x - (m' - x)‖ = ρ + ρ' ∨ ‖m - x - (m' - x)‖ = |ρ - ρ'| := by
    rw [sub_sub_sub_cancel_right, ← dist_eq_norm]; exact htouch
  have eA : A - A' = (A - x) + α • (A - x) := by
    rw [← sub_sub_sub_cancel_right A A' x, hA'x, neg_smul, sub_neg_eq_add]
  have eB : B - B' = (B - x) + β • (B - x) := by
    rw [← sub_sub_sub_cancel_right B B' x, hB'x, neg_smul, sub_neg_eq_add]
  have eC : C - C' = (C - x) + γ • (C - x) := by
    rw [← sub_sub_sub_cancel_right C C' x, hC'x, neg_smul, sub_neg_eq_add]
  obtain ⟨h1, h2⟩ := chord_length_eq_of_tangent hq (A - x) (B - x) (C - x) hα hβ hγ
    ha ha' hb hb' hc hc' hρ hρ' hpa hpb hpc hp0 hpa' hpb' hpc' hp0' htouch'
  exact ⟨by rw [dist_eq_norm, eA, dist_eq_norm, eB]; exact h1,
         by rw [dist_eq_norm, eB, dist_eq_norm, eC]; exact h2⟩

end Usa1992P4
