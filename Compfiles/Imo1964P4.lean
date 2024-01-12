/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Aesop
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic.Linarith

import ProblemExtraction

problem_file

/-!
# International Mathematical Olympiad 1964, Problem 4

Seventeen people correspond by mail with one another -- each one with
all the rest. In their letters only three different topics are
discussed. Each pair of correspondents deals with only one of the topics.
Prove that there are at least three people who write to each other
about the same topic.

-/

namespace Imo1964P4

snip begin

/--
 Smaller version of the problem, with 6 (or more) people and 2 topics.
-/
theorem lemma1
    (Person Topic : Type)
    [Fintype Person] [DecidableEq Person]
    [Fintype Topic] [DecidableEq Topic]
    (card_person : 5 < Fintype.card Person)
    (card_topic : Fintype.card Topic = 2)
    (discusses : Person → Person → Topic)
    (discussion_sym : ∀ p1 p2 : Person, discusses p1 p2 = discusses p2 p1) :
    ∃ t : Topic, ∃ s : Finset Person,
      2 < s.card ∧
        ∀ p1 ∈ s, ∀ p2 ∈ s, p1 ≠ p2 → discusses p1 p2 = t := by
  -- Choose a person p2.
  have p2 : Person := Nonempty.some (Fintype.card_pos_iff.mp (by omega))
  let Person' := {p3 // p3 ≠ p2}
  have hfcα : 4 < Fintype.card Person' := by
    rw [Fintype.card_subtype_compl, Fintype.card_ofSubsingleton]
    exact lt_tsub_of_add_lt_left card_person
  have h1 : Fintype.card Topic * 2 < Fintype.card Person' := by omega

  -- By the pigeonhole principle, there must be some topic t2 such that the
  -- size of the set {p3 // p3 ≠ p2 ∧ discusses p2 p3 = t2} is at least 3.
  have h2 := Fintype.exists_lt_card_fiber_of_mul_lt_card
              (fun (p3: Person') ↦ discusses p2 p3.val) h1
  obtain ⟨t2, ht2⟩ := h2
  -- Call that set α.
  let α := (Finset.filter (fun (x : Person') ↦ discusses p2 ↑x = t2) Finset.univ)

  -- If any pair of people p4 p5 in α discusses topic t2, then we are done.
  -- So the people in α must all discuss only the remaining one topic t3.
  let Topic' := {t3 // t3 ≠ t2}
  have h4 : Fintype.card Topic' = 1 := by
    simp[Fintype.card_subtype_compl, card_topic]

  -- let t3 be the other element of Topic
  obtain ⟨t3, ht3⟩ := Fintype.card_eq_one_iff.mp h4

  obtain h6 | h7 := Classical.em (∃ p3 p4 : α, p3 ≠ p4 ∧
                                    discusses p3.val p4.val = t2)
  · obtain ⟨p3, p4, hp1, hp2⟩ := h6
    use t2
    -- the set we want is {p2,p3,p4}
    let s1 : Finset Person := {p3.val.val}
    let s2 : Finset Person := Finset.cons p4.val s1
                               (by rw [Finset.mem_singleton]; intro hp
                                   exact (hp1 (Subtype.val_injective
                                          (Subtype.val_injective hp)).symm).elim)
    let s3 : Finset Person := Finset.cons p2 s2
                               (by rw [Finset.mem_cons, Finset.mem_singleton]
                                   intro hp
                                   cases hp with
                                   | inl hp =>
                                     exact (p4.val.property.symm hp).elim
                                   | inr hp =>
                                     exact (p3.val.property.symm hp).elim)
    use s3
    constructor
    · simp (config := {decide := true}) only [Finset.card_cons, Finset.card_singleton]
    · intro p1' hp1' p2' hp2' hp1p2
      rw [Finset.mem_cons, Finset.mem_cons, Finset.mem_singleton] at hp1' hp2'
      have hp4d : discusses p2 ↑↑p4 = t2 := by
         have := p4.property; simp at this; exact this
      have hp3d : discusses p2 ↑↑p3 = t2 := by
         have := p3.property; simp at this; exact this
      aesop

  · push_neg at h7
    use t3
    let α' := Finset.map ⟨λ (x :Person') => x.val, Subtype.coe_injective⟩ α
    use α'
    constructor
    · rw [Finset.card_map]; exact ht2
    · intro p3' hp3' p4' hp4' hp3p4'
      rw [Finset.mem_map] at hp3' hp4'
      obtain ⟨⟨p3, p3_ne⟩, p3_mem_α, p3_eq⟩ := hp3'
      obtain ⟨⟨p4, p4_ne⟩, p4_mem_α, p4_eq⟩ := hp4'
      dsimp at p3_eq p4_eq
      rw [←p3_eq, ←p4_eq]
      have hne : p3 ≠ p4 := by rwa [p3_eq, p4_eq]
      have h8 := h7 ⟨⟨p3, p3_ne⟩, p3_mem_α⟩ ⟨⟨p4, p4_ne⟩, p4_mem_α⟩ (by simp[hne])
      let t3': Topic' := ⟨discusses p3 p4, h8⟩
      have h9 := ht3 t3'
      rw [←h9]

snip end

problem imo1964_p4
    (Person Topic : Type)
    [Fintype Person] [DecidableEq Person]
    [Fintype Topic] [DecidableEq Topic]
    (card_person : Fintype.card Person = 17)
    (card_topic : Fintype.card Topic = 3)
    (discusses : Person → Person → Topic)
    (discussion_sym : ∀ p1 p2 : Person, discusses p1 p2 = discusses p2 p1) :
    ∃ t : Topic, ∃ s : Finset Person,
      2 < s.card ∧
        ∀ p1 ∈ s, ∀ p2 ∈ s, p1 ≠ p2 → discusses p1 p2 = t := by
  -- Choose a person p1.
  have p1 : Person := Nonempty.some (Fintype.card_pos_iff.mp (by omega))
  let Person' := {p2 // p2 ≠ p1}

  -- By the pigeonhole principle, there must be some topic t1 such
  -- that the size of the set {p2 // p2 ≠ p1 ∧ discusses p1 p2 = t1}
  -- is at least 6.

  have hfcα : Fintype.card Person' = 16 := by
      simp[Fintype.card_subtype_compl, card_person]
  have h1 : Fintype.card Topic * 5 < Fintype.card Person' := by
      rw [hfcα, card_topic]; norm_num

  have h2 := Fintype.exists_lt_card_fiber_of_mul_lt_card
              (fun (p2: Person') ↦ discusses p1 p2.val) h1
  clear h1
  obtain ⟨t1, ht1⟩ := h2
  -- Call that set α.
  let α := (Finset.filter (fun (x : Person') ↦ discusses p1 ↑x = t1) Finset.univ)
  have cardα : 5 < Fintype.card α := by rw [Fintype.card_coe]; exact ht1;

  -- If any pair of people p2 p3 in α discusses topic t1, then we are done.
  obtain h6 | h7 := Classical.em (∃ p2 p3 : α, p2 ≠ p3 ∧
                                    discusses p2.val p3.val = t1)
  · obtain ⟨p3, p4, hp1, hp2⟩ := h6
    use t1
    -- the set we want is {p1,p3,p4}
    let s1 : Finset Person := {p3.val.val}

    have hs1 : ¬ p4.val.val ∈ s1 := by
      rw [Finset.mem_singleton]; intro hp
      exact (hp1 (Subtype.val_injective (Subtype.val_injective hp)).symm).elim

    let s2 : Finset Person := Finset.cons p4.val s1 hs1

    have hs2 : ¬ p1 ∈ s2 := by
      rw [Finset.mem_cons, Finset.mem_singleton]; intro hp
      cases hp with
      | inl hp => exact (p4.val.property.symm hp).elim
      | inr hp => exact (p3.val.property.symm hp).elim

    let s3 : Finset Person := Finset.cons p1 s2 hs2
    use s3
    constructor
    · simp (config := {decide := true}) only [Finset.card_cons, Finset.card_singleton]
    · intro p1' hp1' p2' hp2' hp1p2
      rw [Finset.mem_cons, Finset.mem_cons, Finset.mem_singleton] at hp1' hp2'
      have hp4d : discusses p1 ↑↑p4 = t1 := by
         have := p4.property; simp at this; exact this
      have hp3d : discusses p1 ↑↑p3 = t1 := by
         have := p3.property; simp at this; exact this
      aesop

  · -- So the people in α must all discuss only the remaining two topics.
    push_neg at h7
    let Topic' := {t2 // t2 ≠ t1}
    have h3 : Fintype Topic' := Fintype.ofFinite Topic'
    have h4 : Fintype.card Topic' = 2 := by
      simp[Fintype.card_subtype_compl, card_topic]
    have t0 : Topic' := Nonempty.some (Fintype.card_pos_iff.mp (by rw [h4]; norm_num))

    let discusses' : α → α → Topic' :=
      fun (p2 p3 : α) ↦
        if heq : p2 = p3 then t0
        else
        ⟨discusses p2.val p3.val, h7 ⟨p2, p2.property⟩ ⟨p3, p3.property⟩ heq⟩
    have discusses_sym' :
        ∀ (p1 p2 : { x // x ∈ α }), discusses' p1 p2 = discusses' p2 p1 := by
      intro p3 p4
      simp
      split_ifs with hf1 hf2 hf3
      · rfl
      · exact (hf2 hf1.symm).elim
      · exact (hf1 hf3.symm).elim
      · simp[discussion_sym]
    have h5 := lemma1 α Topic' cardα h4 discusses' discusses_sym'
    obtain ⟨t2, s, hs1, hs2⟩ := h5
    use t2
    let s' := Finset.map ⟨λ (x : α) => x.val.val,
                          fun x y hxy ↦ Subtype.coe_injective (Subtype.coe_injective hxy)⟩ s
    use s'
    constructor
    · rwa [Finset.card_map]
    · intro p3 hp3 p4 hp4 hp34
      rw [Finset.mem_map] at hp3 hp4
      obtain ⟨⟨⟨p3', p3_mem_person'⟩, p3_mem_α⟩, p3_mem_s, hp3eq⟩ := hp3
      obtain ⟨⟨⟨p4', p4_mem_person'⟩, p4_mem_α⟩, p4_mem_s, hp4eq⟩ := hp4
      dsimp at hp3eq hp4eq
      rw [←hp3eq, ←hp4eq]
      have hne : p3' ≠ p4' := by rwa[hp3eq, hp4eq]
      have h6 := hs2 ⟨⟨p3', p3_mem_person'⟩, p3_mem_α⟩ p3_mem_s
                     ⟨⟨p4', p4_mem_person'⟩, p4_mem_α⟩ p4_mem_s (by simp[hne])
      simp[hne] at h6
      exact (congrArg Subtype.val h6)
