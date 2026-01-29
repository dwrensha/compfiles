/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Benpigchu
-/

import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.Tactic

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
  set f := fun n : ℕ+ ↦ (!₂[1 / n, √(n ^ 2 - 1) / n] : Pt) with hf
  have h' : ∀ n : ℕ+, (0 : ℝ) ≤ ↑↑n ^ 2 - 1 := by
    intro n
    rw [sub_nonneg]
    norm_cast
    rw [one_le_pow_iff (by norm_num)]
    apply PNat.one_le
  have hf' : (Set.range f) ⊆ {p : Pt | ‖p‖ = 1} := by
    intro p hp
    rcases hp with ⟨n, hn⟩
    dsimp
    rw [← hn, hf]
    dsimp
    rw [EuclideanSpace.norm_eq]
    simp
    field_simp
    rw [pow_two, Real.mul_self_sqrt (h' n)]
    ring
  apply Set.Infinite.mono hf'
  apply Set.infinite_range_of_injective
  intro n m hfnm
  rw [hf] at hfnm
  simp at hfnm
  exact hfnm.left

universe u

lemma exists_three_of_infinite
  {α : Type u} {s : Set α} (hs : s.Infinite)
  : ∃ p q r : α, p ∈ s ∧ q ∈ s ∧ r ∈ s
    ∧ p ≠ q ∧ q ≠ r ∧ r ≠ p := by
  have h₁ : s.Nonempty := hs.nonempty
  rw [Set.nonempty_def] at h₁
  rcases h₁ with ⟨p, hp⟩
  have h₂ : (s \ {p}).Nonempty := by
    apply Set.Infinite.nonempty
    apply Set.Infinite.diff hs
    apply Set.finite_singleton
  rcases h₂ with ⟨q, hq⟩
  have h₃ : (s \ {p, q}).Nonempty := by
    apply Set.Infinite.nonempty
    apply Set.Infinite.diff hs
    rw [Set.finite_insert]
    apply Set.finite_singleton
  rcases h₃ with ⟨r, hr⟩
  rw [Set.mem_diff] at hq hr
  rw [Set.mem_insert_iff] at hr
  rw [Set.mem_singleton_iff] at hq hr
  use p, q, r
  grind only

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
  rw [EuclideanGeometry.Sphere.mem_coe, EuclideanGeometry.mem_sphere]
  dsimp
  rw [dist_eq_norm]

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
  · have h_pt : Nonempty Pt := by
      apply Infinite.nonempty
    rw [← exists_true_iff_nonempty] at h_pt
    rcases h_pt with ⟨p⟩
    use {p}
    constructorm* _ ∧ _
    · apply Set.singleton_nonempty
    · apply Set.finite_singleton
    · intro s hs
      rw [Nat.cast_zero, Set.encard_eq_zero, Set.eq_empty_iff_forall_notMem]
      rintro t ⟨ht, hst⟩
      rw [Set.mem_singleton_iff] at hs ht
      contrapose! hst
      rw [hs, ht, dist_self]
      norm_num
  · rcases h with ⟨S', ⟨hS'₁, hS'₂, hS'₃⟩⟩
    have hd_set : ({p : Pt | ‖p‖ = 1}
      \ ({p : Pt | ∃ (s t : Pt), s ∈ S' ∧ t ∈ S' ∧ s - t = p}
      ∪ {p : Pt | ∃ (s t : Pt), s ∈ S' ∧ t ∈ S' ∧ s ≠ t ∧ ‖p‖ = 1 ∧ dist s (t + p) = 1})).Nonempty := by
      apply Set.Infinite.nonempty
      apply Set.Infinite.diff
      · exact norm_one_infinity
      · apply Set.Finite.union
        · exact finite₁ hS'₂
        · exact finite₂ hS'₂
    rw [← Set.diff_diff] at hd_set
    rcases hd_set with ⟨d, ⟨⟨hd₁, hd₂⟩, hd₃⟩⟩
    dsimp at hd₁ hd₂ hd₃
    push_neg at hd₂ hd₃
    set f := fun p ↦ p + d with hf
    set S'' := {p : Pt | ∃ p' ∈ S', p = p' + d} with hS''
    have h'S'' : S'' = f '' S' := by
      ext p
      rw [Set.mem_image, hS'']
      dsimp
      constructor <;> rintro ⟨p', ⟨hp'₁, hp'₂⟩⟩ <;> use p' <;> rw [and_iff_right hp'₁]
        <;> symm <;> exact hp'₂
    have hS''₁ : S''.Nonempty := by
      rw [h'S'', Set.image_nonempty]
      exact hS'₁
    have hS''₂ : S''.Finite := by
      rw [h'S'']
      apply Set.Finite.image
      exact hS'₂
    have hf' : Function.Injective f := by
      intro s t hst
      rw [hf] at hst
      dsimp at hst
      exact add_right_cancel hst
    have hf'' : ∀ s ∈ S', {t | t ∈ f '' S' ∧ dist (f s) t = 1} = f '' {t | t ∈ S' ∧ dist s t = 1} := by
      intro s hs
      ext t
      rw [Set.mem_image]
      dsimp
      rw [Set.mem_image, hf]
      dsimp
      constructor
      · rintro ⟨⟨t', ⟨ht', ht't⟩⟩, hst⟩
        use t'
        constructorm* _ ∧ _
        · exact ht'
        · rw [← ht't, dist_add_right] at hst
          exact hst
        · exact ht't
      · rintro ⟨t', ⟨⟨ht', hst'⟩, ht't⟩⟩
        constructor
        · use t'
        · rw [← ht't, dist_add_right, hst']
    have hS''₃ : ∀ s ∈ S'', {t | t ∈ S'' ∧ dist s t = 1}.encard = ↑m := by
      intro s hs
      rw [h'S''] at hs ⊢
      rcases hs with ⟨s', ⟨hs'S', hfs's⟩⟩
      rw [← hS'₃ s' hs'S', ← hfs's, hf'' s' hs'S']
      apply Function.Injective.encard_image hf'
    clear hf' hf'' h'S''
    use S' ∪ S''
    constructorm* _ ∧ _
    · rw [Set.union_nonempty]
      left
      exact hS'₁
    · apply Set.Finite.union hS'₂ hS''₂
    · intro s hs
      wlog hsS' : s ∈ S' generalizing S' d
      · have hsS'' : s ∈ S'' := by
          rw [Set.mem_union, or_iff_right hsS'] at hs
          exact hs
        have hd'₁ : ‖-d‖ = 1 := by
          rw [norm_neg, hd₁]
        have hd'₂ : ∀ (s t : Pt), s ∈ S'' → t ∈ S'' → s - t ≠ -d := by
          intro s t hs ht
          rcases hs with ⟨s', ⟨hs', hss'd⟩⟩
          rcases ht with ⟨t', ⟨ht', htt'd⟩⟩
          rw [hss'd, htt'd, ← neg_eq_iff_eq_neg.ne, (by abel : -(s' + d - (t' + d)) = t' - s')]
          apply hd₂ t' s' ht' hs'
        have hd'₃ : ∀ (s t : Pt), s ∈ S'' → t ∈ S'' → s ≠ t → ‖-d‖ = 1 → dist s (t + -d) ≠ 1 := by
          intro s t hs ht hst hd
          rw [hS''] at hs ht
          rcases hs with ⟨s', ⟨hs', hss'd⟩⟩
          rcases ht with ⟨t', ⟨ht', htt'd⟩⟩
          rw [hss'd, htt'd, ← sub_eq_add_neg, add_sub_cancel_right, dist_comm]
          rw [hss'd, htt'd, add_right_cancel_iff.ne,] at hst
          apply hd₃ t' s' ht' hs' hst.symm hd₁
        have hS'''_eq_S' : {p | ∃ p' ∈ S'', p = p' + -d} = S' := by
          rw [hS'']
          ext p
          constructor
          · rintro ⟨p', ⟨⟨p'', ⟨hp''S', hp''⟩⟩, hp'⟩⟩
            rw [hp', hp'', ← sub_eq_add_neg, add_sub_cancel_right]
            exact hp''S'
          · intro hp
            use p + d
            constructor
            · use p
            · rw [← sub_eq_add_neg, add_sub_cancel_right]
        rw [← hS'''_eq_S'] at hS'₁ hS'₂ hS'₃ hs
        rw [Set.union_comm] at hs
        have h := this S'' hS''₁ hS''₂ hS''₃ (-d)
          hd'₁ hd'₂ hd'₃ rfl rfl hS'₁ hS'₂ hS'₃ hs hsS''
        rw [hS'''_eq_S', Set.union_comm] at h
        exact h
      have heq : {t | t ∈ S' ∪ S'' ∧ dist s t = 1} = {t | t ∈ S' ∧ dist s t = 1} ∪ {s + d} := by
        ext t
        rw [Set.mem_union, Set.mem_singleton_iff]
        constructor
        · rintro ⟨ht, hts⟩
          rw [Set.mem_union] at ht
          rcases ht with htS'|htS''
          · left
            exact ⟨htS', hts⟩
          · right
            rw [hS''] at htS''
            rcases htS'' with ⟨s', ⟨hs'S', hts'd⟩⟩
            by_cases! hss' : s = s'
            · rw [hts'd, hss']
            · rw [hts'd] at hts
              contrapose! hts
              apply hd₃ s s' hsS' hs'S' hss' hd₁
        · rintro (⟨htS', hts⟩|htsd)
          · dsimp
            rw [and_iff_left hts]
            apply Set.mem_union_left
            exact htS'
          · constructor
            · apply Set.mem_union_right
              rw [hS'']
              use s
            · rw [← sub_eq_iff_eq_add'] at htsd
              rw [dist_eq_norm', htsd, hd₁]
      rw [heq]
      have h_disj : Disjoint {t | t ∈ S' ∧ dist s t = 1} {s + d} := by
        rw [Set.disjoint_singleton_right]
        rintro ⟨h'⟩
        set t := s + d with ht
        rw [← sub_eq_iff_eq_add'] at ht
        contrapose! ht
        apply hd₂ t s h' hsS'
      rw [Set.encard_union_eq h_disj, Set.encard_singleton, hS'₃ s hsS', Nat.cast_add, Nat.cast_one]


end Imo1971P5
