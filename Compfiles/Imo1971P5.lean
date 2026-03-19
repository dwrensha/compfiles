/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Benpigchu
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 1971, Problem 5

Prove that for every natural number m there exists a nonempty finite
set S of points in the plane with the following property:
For every point s in S, there are exactly m points which are at a unit
distance from s.
-/

namespace Imo1971P5

open scoped EuclideanGeometry

abbrev Pt := EuclideanSpace ℝ (Fin 2)

snip begin

lemma norm_one_infinity : {p : Pt | ‖p‖ = 1}.Infinite := by
  suffices h : (Metric.sphere (0 : Pt) 1).Infinite by
    convert h using 1; ext p; simp
  apply IsPreconnected.infinite_of_nontrivial
  · refine isPreconnected_sphere ?_ 0 1
    rw [← Module.finrank_eq_rank (R := ℝ) (M := Pt), finrank_euclideanSpace_fin]
    norm_num
  · refine ⟨EuclideanSpace.single 0 1, by simp [PiLp.norm_single],
            EuclideanSpace.single 1 1, by simp [PiLp.norm_single], ?_⟩
    intro h
    have : (EuclideanSpace.single 0 (1 : ℝ) : Pt) 1 = (EuclideanSpace.single 1 (1 : ℝ) : Pt) 1 :=
      congr_arg (· 1) h
    simp at this

universe u

lemma exists_three_of_infinite
  {α : Type u} {s : Set α} (hs : s.Infinite)
  : ∃ p q r : α, p ∈ s ∧ q ∈ s ∧ r ∈ s
    ∧ p ≠ q ∧ q ≠ r ∧ r ≠ p := by
  obtain ⟨p, hp, q, hq, hpq⟩ := hs.nontrivial
  obtain ⟨r, hr, hrpq⟩ := (hs.diff (Set.toFinite {p, q})).nonempty
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hrpq
  exact ⟨p, q, r, hp, hq, hr, hpq, fun h => hrpq.2 h.symm, fun h => hrpq.1 h⟩

lemma sphere_inter_finite
  {s₁ s₂ : EuclideanGeometry.Sphere Pt} (hs : s₁ ≠ s₂) :
  ((s₁ : Set Pt) ∩ s₂).Finite := by
  by_contra! h'
  rcases exists_three_of_infinite h' with ⟨p, q, r, hp, hq, hr, hpq, hqr, hrp⟩
  have hd : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := finrank_euclideanSpace_fin
  rw [Set.mem_inter_iff, EuclideanGeometry.Sphere.mem_coe, EuclideanGeometry.Sphere.mem_coe] at hp hq hr
  have h'' := EuclideanGeometry.eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two
    hd hs hpq hp.left hq.left hr.left hp.right hq.right hr.right
  grind only

lemma sphere_eq_sub_norm (o : Pt) (r : ℝ)
  : {p : Pt | ‖p - o‖ = r} = (EuclideanGeometry.Sphere.mk o r : Set Pt) := by
  ext p
  rw [Set.mem_setOf_eq, mem_sphere_iff_norm]

lemma norm_one_inter_finite {s : Pt} (hs : s ≠ 0)
  : ({p : Pt | ‖p - 0‖ = 1} ∩ {p : Pt | ‖p - s‖ = 1}).Finite := by
  rw [sphere_eq_sub_norm 0 1, sphere_eq_sub_norm s 1]
  apply sphere_inter_finite
  rw [ne_eq, EuclideanGeometry.Sphere.ext_iff]
  dsimp
  rw [and_iff_left rfl, ← ne_eq]
  symm
  exact hs

lemma finite₁ {S : Set Pt} (hS : S.Finite)
  : {p | ∃ s t, s ∈ S ∧ t ∈ S ∧ s - t = p}.Finite := by
  have h' : {p | ∃ s t, s ∈ S ∧ t ∈ S ∧ s - t = p}
    = ⋃ s ∈ S, ⋃ t ∈ S, {s - t} := by
    ext p
    simp
    constructor <;> rintro ⟨s, hs, t, ht, hstp⟩ <;> use s <;> rw [and_iff_right hs]
      <;> use t <;> rw [and_iff_right ht, hstp]
  rw [h']
  apply Set.Finite.biUnion hS
  intro s hs
  apply Set.Finite.biUnion hS
  intro t ht
  apply Set.finite_singleton

lemma finite₂ {S : Set Pt} (hS : S.Finite)
  : {p : Pt | ∃ (s t : Pt), s ∈ S ∧ t ∈ S ∧ s ≠ t ∧ ‖p‖ = 1 ∧ dist s (t + p) = 1}.Finite := by
  have h' : {p : Pt | ∃ (s t : Pt), s ∈ S ∧ t ∈ S ∧ s ≠ t ∧ ‖p‖ = 1 ∧ dist s (t + p) = 1}
    = ⋃ s ∈ S, ⋃ t ∈ S, {p : Pt | s ≠ t ∧ ‖p‖ = 1 ∧ dist s (t + p) = 1} := by
    ext p
    simp
    constructor <;> rintro ⟨s, hs, t, ht, hstp⟩ <;> use s <;> rw [and_iff_right hs]
      <;> use t <;> rw [and_iff_right ht] <;> grind only
  rw [h']
  apply Set.Finite.biUnion hS
  intro s hs
  apply Set.Finite.biUnion hS
  intro t ht
  by_cases! hst : s = t
  · have h'' :  {p | s ≠ t ∧ ‖p‖ = 1 ∧ dist s (t + p) = 1} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro p
      contrapose! hst
      dsimp at hst
      exact hst.left
    rw [h'']
    exact Set.finite_empty
  · have h'' :  {p | s ≠ t ∧ ‖p‖ = 1 ∧ dist s (t + p) = 1}
      = {p : Pt | ‖p - 0‖ = 1} ∩ {p : Pt | ‖p - (s - t)‖ = 1} := by
      ext p
      simp [- ne_eq]
      rw [and_iff_right hst]
      constructor <;> rintro ⟨hp₁, hp₂⟩ <;> rw [and_iff_right hp₁, ← hp₂]
        <;> rw [← sub_add, dist_comm, dist_eq_norm] <;> abel_nf
    rw [h'']
    rw [← sub_eq_zero.ne] at hst
    exact norm_one_inter_finite hst

snip end

problem imo1971_p5 (m : ℕ) :
    ∃ S : Set Pt, S.Nonempty ∧ S.Finite ∧
      ∀ s ∈ S, {t ∈ S | dist s t = 1}.encard = m := by
  induction' m with m h
  · exact ⟨{0}, Set.singleton_nonempty _, Set.finite_singleton _, fun s hs => by
      rw [Nat.cast_zero, Set.encard_eq_zero, Set.eq_empty_iff_forall_notMem]
      rintro t ⟨ht, hst⟩
      rw [Set.mem_singleton_iff] at hs ht
      rw [hs, ht, dist_self] at hst; norm_num at hst⟩
  · rcases h with ⟨S', hS'₁, hS'₂, hS'₃⟩
    -- Pick d on the unit circle avoiding finitely many bad values
    have hd_set := (norm_one_infinity.diff ((finite₁ hS'₂).union (finite₂ hS'₂))).nonempty
    rw [← Set.diff_diff] at hd_set
    obtain ⟨d, ⟨hd₁, hd₂⟩, hd₃⟩ := hd_set
    dsimp at hd₁ hd₂ hd₃; push_neg at hd₂ hd₃
    -- Define translated set S'' = S' + d
    set f := fun p ↦ p + d with hf
    set S'' := {p : Pt | ∃ p' ∈ S', p = p' + d} with hS''
    have h'S'' : S'' = f '' S' := by
      ext p; rw [Set.mem_image, hS'']; simp only [Set.mem_setOf_eq, hf]
      constructor <;> rintro ⟨p', hp'₁, hp'₂⟩ <;> exact ⟨p', hp'₁, hp'₂.symm⟩
    have hS''₁ : S''.Nonempty := by rw [h'S'', Set.image_nonempty]; exact hS'₁
    have hS''₂ : S''.Finite := by rw [h'S'']; exact hS'₂.image _
    have hf' : Function.Injective f := add_left_injective d
    have hf'' : ∀ s ∈ S', {t | t ∈ f '' S' ∧ dist (f s) t = 1} =
        f '' {t | t ∈ S' ∧ dist s t = 1} := by
      intro s hs; ext t; simp only [Set.mem_setOf_eq, Set.mem_image, hf]
      constructor
      · rintro ⟨⟨t', ht', rfl⟩, hst⟩
        exact ⟨t', ⟨ht', by rwa [dist_add_right] at hst⟩, rfl⟩
      · rintro ⟨t', ⟨ht', hst⟩, rfl⟩
        exact ⟨⟨t', ht', rfl⟩, by rw [dist_add_right]; exact hst⟩
    have hS''₃ : ∀ s ∈ S'', {t | t ∈ S'' ∧ dist s t = 1}.encard = ↑m := by
      intro s hs; rw [h'S''] at hs ⊢
      obtain ⟨s', hs'S', rfl⟩ := hs
      rw [← hS'₃ s' hs'S', hf'' s' hs'S', hf'.encard_image]
    clear hf' hf'' h'S''
    use S' ∪ S''
    refine ⟨Set.union_nonempty.mpr (Or.inl hS'₁), hS'₂.union hS''₂, ?_⟩
    intro s hs
    wlog hsS' : s ∈ S' generalizing S' d
    · have hsS'' : s ∈ S'' := (Set.mem_union _ _ _).mp hs |>.resolve_left hsS'
      have hd'₁ : ‖-d‖ = 1 := by rw [norm_neg]; exact hd₁
      have hd'₂ : ∀ (s t : Pt), s ∈ S'' → t ∈ S'' → s - t ≠ -d := by
        intro s t hs ht
        rcases hs with ⟨s', hs', hss'd⟩
        rcases ht with ⟨t', ht', htt'd⟩
        rw [hss'd, htt'd, ← neg_eq_iff_eq_neg.ne, (by abel : -(s' + d - (t' + d)) = t' - s')]
        exact hd₂ t' s' ht' hs'
      have hd'₃ : ∀ (s t : Pt), s ∈ S'' → t ∈ S'' → s ≠ t → ‖-d‖ = 1 →
          dist s (t + -d) ≠ 1 := by
        intro s t hs ht hst hd
        rw [hS''] at hs ht
        rcases hs with ⟨s', hs', hss'd⟩
        rcases ht with ⟨t', ht', htt'd⟩
        rw [hss'd, htt'd, ← sub_eq_add_neg, add_sub_cancel_right, dist_comm]
        rw [hss'd, htt'd, add_right_cancel_iff.ne] at hst
        exact hd₃ t' s' ht' hs' hst.symm hd₁
      have hS'''_eq_S' : {p | ∃ p' ∈ S'', p = p' + -d} = S' := by
        rw [hS'']; ext p; constructor
        · rintro ⟨p', ⟨p'', hp''S', hp''⟩, hp'⟩
          rw [hp', hp'', ← sub_eq_add_neg, add_sub_cancel_right]; exact hp''S'
        · intro hp
          exact ⟨p + d, ⟨p, hp, rfl⟩, by rw [← sub_eq_add_neg, add_sub_cancel_right]⟩
      rw [← hS'''_eq_S'] at hS'₁ hS'₂ hS'₃ hs
      rw [Set.union_comm] at hs
      have h := this S'' hS''₁ hS''₂ hS''₃ (-d)
        hd'₁ hd'₂ hd'₃ rfl rfl hS'₁ hS'₂ hS'₃ hs hsS''
      rw [hS'''_eq_S', Set.union_comm] at h
      exact h
    -- Main case: s ∈ S'
    have heq : {t | t ∈ S' ∪ S'' ∧ dist s t = 1} = {t | t ∈ S' ∧ dist s t = 1} ∪ {s + d} := by
      ext t; rw [Set.mem_union, Set.mem_singleton_iff]
      constructor
      · rintro ⟨ht, hts⟩
        rcases Set.mem_union _ _ _ |>.mp ht with htS' | htS''
        · exact Or.inl ⟨htS', hts⟩
        · right; rcases htS'' with ⟨s', hs'S', hts'd⟩
          by_cases hss' : s = s'
          · rw [hts'd, hss']
          · exact absurd hts (by rw [hts'd]; exact hd₃ s s' hsS' hs'S' hss' hd₁)
      · rintro (⟨htS', hts⟩ | rfl)
        · exact ⟨Set.mem_union_left _ htS', hts⟩
        · exact ⟨Set.mem_union_right _ ⟨s, hsS', rfl⟩,
            by rw [dist_eq_norm', add_sub_cancel_left, hd₁]⟩
    rw [heq]
    have h_disj : Disjoint {t | t ∈ S' ∧ dist s t = 1} {s + d} := by
      rw [Set.disjoint_singleton_right]
      rintro ⟨hsd⟩
      exact hd₂ (s + d) s hsd hsS' (by rw [add_sub_cancel_left])
    rw [Set.encard_union_eq h_disj, Set.encard_singleton, hS'₃ s hsS', Nat.cast_add, Nat.cast_one]


end Imo1971P5
