/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shalev Wengrowsky
-/

import Mathlib.Data.Set.Card
import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 1966, Problem 1.

In a mathematical contest, three problems, A, B, C were posed. Among the
participants there were 25 students who solved at least one problem each.
Of all the contestants who did not solve problem A, the number who solved
B was twice the number who solved C. The number of students who solved
only problem A was one more than the number of students who solved A
and at least one other problem. Of all students who solved just one problem,
half did not solve problem A. How many students solved only problem B?

-/

namespace Imo1966P1

variable {U : Type*} [DecidableEq U]

snip begin

-- outline of the proof, modified from https://prase.cz/kalva/imo/isoln/isoln661.html
example (a b c d e : ℕ)
  (h1 : a + b + c + d + e = 25)
  (h2 : b + d = 2 * (c + d))
  (h3 : a = 1 + 25 - a - b - c - d)
  (h4 : a = b + c) : b = 6 := by omega

lemma lemma1 (A B C : Finset U) : (A \ B) \ C = (A \ C) \ B := by
  ext x; simp; tauto

lemma lemma2 (A B : Finset U) : A = (A ∩ B) ∪ (A \ B) := by
  ext x; simp; tauto

lemma lemma3 (A B C : Finset U) :
  (A ∪ B) \ C = (A \ C) ∪ (B \ C) := by
  ext x; simp; tauto

lemma lemma4 (A B C : Finset U) :
  (A ∩ B) \ C = (A \ C) ∩ (B \ C) := by
  ext x; simp; tauto

lemma lemma5 (A B C : Finset U) :
  (A \ B) ∩ C = (A \ B) ∩ (C \ B) := by
  ext x; simp; tauto

snip end

determine solution : ℕ := 6

problem Imo1966_p1 (A B C : Finset U)
  (h1 : (A ∪ B ∪ C).card = 25)
  (h2 : (B \ A).card = 2 * (C \ A).card)
  (h3 : ((A \ B) \ C).card = 1 + (A ∩ (B ∪ C)).card)
  (h4 : ((A \ B) \ C).card = ((B \ A) \ C).card + ((C \ A) \ B).card) :
  ((B \ A) \ C).card = solution := by {
  let a := ((A \ B) \ C).card
  let b := ((B \ A) \ C).card
  let c := ((C \ A) \ B).card
  let d := ((B ∩ C) \ A).card
  let e := (A ∩ (B ∪ C)).card

  have h_eq1_lemma : A ∪ B ∪ C =
    (A \ B) \ C ∪ (B \ A) \ C ∪ (C \ A) \ B ∪ (B ∩ C) \ A ∪ A ∩ (B ∪ C) := by
    ext x; simp; tauto
  have h_eq1 : a + b + c + d + e = 25 := by {
    simp [a, b, c, d, e]
    repeat rw [← Finset.card_union_of_disjoint]
    · rw [← h_eq1_lemma]
      exact h1
    repeat {
      intro S h1' h2'
      simp at h1' h2' ⊢
      ext x
      constructor
      · intro h3'
        have h1' := h1' h3'
        have h2' := h2' h3'
        simp at h1' h2'
        tauto
      · intro; tauto
    }
  }

  have h_eq2: b + d = 2 * (c + d) := by {
    simp [b, c, d]
    rw [lemma2 B C] at h2
    rw [lemma3] at h2
    rw [Finset.card_union_of_disjoint] at h2
    · rw [lemma1, add_comm, h2]
      rw [← Finset.card_union_of_disjoint]
      · rw [Finset.inter_comm, lemma4]
        rw [← lemma5, Finset.union_comm, ← lemma2]
      · unfold Disjoint
        simp
        intro S h1' h2'
        rw [lemma1] at h1'
        rw [Finset.inter_comm] at h2'
        ext x
        constructor
        · intro h3'
          have h1' := h1' h3'
          have h2' := h2' h3'
          simp at h1' h2'
          tauto
        · intro h3'
          tauto

    · refine Finset.disjoint_left.mpr ?_
      intro x
      simp
      tauto
  }
  have h_eq3_lemma: A ∩ (B ∪ C) =
    ((((A ∪ B ∪ C) \ ((A \ B) \ C)) \ ((B \ A) \ C)) \ ((C \ A) \ B)) \ ((B ∩ C) \ A) := by {
    ext x; simp; tauto
  }
  have h_eq3 : a = 1 + 25 - a - b - c - d := by {
    repeat rw [Nat.add_sub_assoc]
    · simp only [a, b, c, d, ← h1]
      repeat rw [← Finset.card_sdiff_of_subset]
      · rw [← h_eq3_lemma]
        exact h3
      repeat intro; simp; tauto
    repeat omega
  }
  -- no need for eq4
  unfold solution; omega
}

end Imo1966P1
