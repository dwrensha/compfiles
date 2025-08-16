/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ansar Azhdarov
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 2003, Problem 1

Let A be a 101-element subset of S = {1,2,...10⁶}. Prove that
there exist numbers t₁, t₂, ..., t₁₀₀ in S such that the sets

     Aⱼ = {x + tⱼ | x ∈ A},     j = 1,2, ..., 100

are pairwise disjoint.
-/

namespace Imo2003P1

abbrev S := Finset.Icc 1 1000000

snip begin

/- Proof by induction on the number of tᵢ's -/
theorem induction_lemma (A : Finset ℕ) (_AS : A ⊆ S) (Acard : A.card = 101)
    {k : ℕ} (hk : k ≤ 100) :
    ∃ t ⊆ S, t.card = k ∧ ∀ x ∈ t, ∀ y ∈ t, x ≠ y → Disjoint {x + a | a ∈ A} {y + a | a ∈ A} := by
  classical
  induction' k with k h
  · exact ⟨∅, by simp⟩
  · obtain ⟨t, tS, tcard, ht⟩ := h (by omega)

    /- For a shift of A by x, consider the shifts by y ∈ S intersecting it -/
    let f (x : ℕ) := {y ∈ S | ¬ Disjoint {x + a | a ∈ A} {y + a | a ∈ A}}

    obtain ⟨a, aA⟩ : A.Nonempty := Finset.card_pos.mp (by linarith)

    let B := insert (a, a) A.offDiag

    have Bcard : B.card = 10101 := by
      have : (a, a) ∉ A.offDiag := by simp
      rw [Finset.card_insert_of_notMem this]
      norm_num [Acard]

    /- These correspond to some pairs of points from A overlaying after the shifts -/
    have hchoose (x : ℕ) : ∀ y : f x, ∃ p : B, x + p.1.1 = y + p.1.2 := by
      intro ⟨y, yf⟩
      unfold f at yf
      simp at yf
      have := yf.2
      simp [Set.not_disjoint_iff] at this
      obtain ⟨b, bA, c, cA, hbc⟩ := this
      by_cases b = c
      · use ⟨(a, a), by grind⟩; grind
      · use ⟨(b, c), by grind⟩; grind

    have fcard (x : ℕ) (xt : x ∈ t) : (f x).card ≤ 10101 := by
      choose u hu using hchoose x
      have : u.Injective := by
        intro y z hyz
        have hy := (hu y)
        have hz := (hu z)
        rw [Subtype.eq_iff]
        simp [hyz ▸ hy] at hz
        exact hz
      exact Bcard ▸ Finset.card_le_card_of_injective this

    have Ufcard : (t.biUnion f).card ≤ 999999 := by
      refine le_trans Finset.card_biUnion_le ?_
      refine le_trans (Finset.sum_le_sum fcard) ?_
      simp [tcard]
      linarith

    /- By counting, there must be a shift by x ∈ S intersecting neither of the shifts by tᵢ -/
    have : ∃ x ∈ S, x ∉ t.biUnion f := by
      refine Finset.exists_mem_notMem_of_card_lt_card ?_
      exact lt_of_le_of_lt Ufcard (by norm_num)

    obtain ⟨w, wS, wUf⟩ := this

    have xf (x : ℕ) (xS : x ∈ S) : x ∈ f x := by
      unfold f
      simp [Finset.mem_filter, xS]
      push_neg
      use x + a
      simp [aA]

    have wt : w ∉ t := by
      have := xf w wS
      contrapose! wUf with wt
      rw [Finset.mem_biUnion]
      use w

    have tw (x : ℕ) (xt : x ∈ t) : Disjoint {x + a | a ∈ A} {w + a | a ∈ A} := by
      contrapose! wUf
      unfold f
      simp [wS]
      use x

    let r := insert w t

    have rS : r ⊆ S := by
      intro x xr
      rw [Finset.mem_insert] at xr
      rcases xr with xz | xt
      · rw [xz]
        exact wS
      · exact tS xt

    have rcard : r.card = k + 1 := by
      rw [Finset.card_insert_of_notMem wt]
      congr

    have hr : ∀ x ∈ r, ∀ y ∈ r, x ≠ y → Disjoint {x + a | a ∈ A} {y + a | a ∈ A} := by
      intro x xr y yr xy
      rw [Finset.mem_insert] at xr yr
      rcases xr with xz | xt
      · rcases yr with yz | yt
        · rw [xz, yz] at xy
          contradiction
        · rw [xz]
          exact Disjoint.symm (tw y yt)
      · rcases yr with yz | yt
        · rw [yz]
          exact tw x xt
        · exact ht x xt y yt xy

    use r

snip end

problem imo2003_p1 (A : Finset ℕ) (AS : A ⊆ S) (Acard : A.card = 101) :
    ∃ t ⊆ S, t.card = 100 ∧ ∀ x ∈ t, ∀ y ∈ t, x ≠ y → Disjoint {x + a | a ∈ A} {y + a | a ∈ A} :=
  induction_lemma A AS Acard (Nat.le_refl _)

end Imo2003P1
