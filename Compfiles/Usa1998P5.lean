/-
Copyright (c) 2023 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 1998, Problem 5

Prove that for each n ≥ 2, there is a set S of n integers such that
(a-b)² divides ab for every distinct a,b ∈ S.
-/

namespace Usa1998P5

problem usa1998_p5 (n : ℕ) (_hn : 2 ≤ n) :
    ∃ S : Finset ℤ,
       S.card = n ∧
       ∀ a ∈ S, ∀ b ∈ S, a ≠ b → (a - b)^2 ∣ a * b := by
  -- (Adaptation of informal proof from Andreescu & Feng.)
  suffices H : ∃ S : Finset ℤ,(∀ x ∈ S, 0 ≤ x) ∧
       S.card = n ∧
       ∀ a ∈ S, ∀ b ∈ S, a ≠ b → (a - b)^2 ∣ a * b by
    obtain ⟨S, _, hS2⟩ := H
    exact ⟨S, hS2⟩
  clear _hn
  induction n with
  | zero => use ∅; simp
  | succ n ih =>
    obtain ⟨Sp, sp_nonnegative, sp_card, hsp⟩ := ih
    let L : ℤ := ∏ s ∈ Sp, ∏ t ∈ Sp.erase s, (s-t)^2

    have L_pos : 0 < L := by
      refine Finset.prod_pos fun s _ ↦ Finset.prod_pos ?_
      intro t ht
      obtain ⟨t_ne_s, _⟩ := Finset.mem_erase.mp ht
      have : s - t ≠ 0 := sub_ne_zero_of_ne t_ne_s.symm
      positivity

    -- Define Sₙ₊₁ = { L + a : a ∈ Sₙ } ∪ { 0 }.
    let S : Finset ℤ := Sp.map (addLeftEmbedding L) ∪ {0}
    use S

    constructor
    · -- all elements are nonnegative
      intro x hx
      rw [Finset.mem_union] at hx
      cases hx with
      | inl hx =>
        rw [Finset.mem_map] at hx
        obtain ⟨w, hw1, hw2⟩ := hx
        have := sp_nonnegative w hw1
        replace hw2 : L + w = x := hw2
        omega
      | inr hx => simp_all
    · constructor
      · --cardinality is n + 1
        have hdisj : Disjoint (Finset.map (addLeftEmbedding L) Sp) {0} := by
          intro X hX h0 y hy
          have hyy := h0 hy
          rw [Finset.mem_singleton] at hyy
          rw [hyy] at hy
          have hxx := hX hy
          rw [Finset.mem_map] at hxx
          obtain ⟨z, hz, hz2⟩ := hxx
          replace hz2 : L + z = 0 := hz2
          have := sp_nonnegative z hz
          omega
        rw [Finset.card_union_of_disjoint hdisj, Finset.card_singleton,
            Finset.card_map, sp_card]
      · intro α hα β hβ α_ne_β
        rw [Finset.mem_union, Finset.mem_map] at hα hβ
        -- If α,β ∈ Sₙ₊₁ and either α or β is zero, then (α - β)² divides αβ.
        cases hα with
        | inr hα => simp_all
        | inl hα =>
          cases hβ with
          | inr hβ => simp_all
          | inl hβ =>
            obtain ⟨a, ha, ha2⟩ := hα
            replace ha2 : L + a = α := ha2
            obtain ⟨b, hb, hb2⟩ := hβ
            replace hb2 : L + b = β := hb2
            have a_ne_b : a ≠ b := by omega
            have ih := hsp a ha b hb a_ne_b
            have h5 : L = (∏ t ∈ Sp.erase a, (a-t)^2) *
                         ∏ s ∈ Sp.erase a, ∏ t ∈ Sp.erase s, (s-t)^2 :=
              (Finset.mul_prod_erase Sp _ ha).symm
            have hbb := Finset.mem_erase.mpr ⟨a_ne_b.symm, hb⟩
            have h6 : (a-b)^2 * ∏ t ∈ (Sp.erase a).erase b, (a-t)^2 =
                      ∏ t ∈ Sp.erase a, (a-t)^2 :=
               Finset.mul_prod_erase (Sp.erase a) (fun x ↦ (a-x)^2) hbb
            have Lmod : L % (a - b)^2 = 0 := by
                 rw [h5, ←h6, mul_assoc, Int.mul_emod, Int.emod_self]
                 norm_num
            have Lmod' : (L + a) * (L + b) % (a-b)^2 = 0 := by
               have h7 : (L + a) * (L + b) = L * (L + a + b) + a * b := by ring
               rw [h7, Int.add_emod]
               have h8 : L * (L + a + b) % (a - b) ^ 2 = 0 := by
                 rw [Int.mul_emod, Lmod]
                 norm_num
               have h9 :  a * b % (a - b) ^ 2 = 0 := Int.emod_eq_zero_of_dvd ih
               rw [h8, h9]
               norm_num
            have hab : a - b = α - β := by omega
            rw [ha2, hb2, hab] at Lmod'
            exact Int.dvd_of_emod_eq_zero Lmod'


end Usa1998P5
