import Mathlib.Data.Fin.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic.CasesM
import Mathlib.Tactic.LibrarySearch

/-!
# International Mathematical Olympiad 1964, Problem 4

Seventeen people correspond by mail with one another -- each one with
all the rest. In their letters only three different topics are
discussed. Each pair of correspondents deals with only one of the topics.
Prove that there are at least three people who write to each other
about the same topic.

-/

theorem lemma1
    (Person Topic : Type)
    [Fintype Person]
    [Fintype Topic]
    (card_person : Fintype.card Person = 6)
    (card_topic : Fintype.card Topic = 2)
    (discusses : Person → Person → Topic)
    (discussion_sym : ∀ p1 p2 : Person, discusses p1 p2 = discusses p2 p1) :
    ∃ t : Topic, ∃ s : Finset Person,
      2 < s.card ∧
        ∀ p1 ∈ s, ∀ p2 ∈ s, p1 ≠ p2 → discusses p1 p2 = t := by
  -- By the pigeonhole principle, there must be some topic t2 such that the
  -- size of the set {p3 // p3 ≠ p2 ∧ discusses p2 p3 = t2} is at least 3.
  have nonzero_people : Fintype.card Person > 0 := by rw[card_person]; norm_num
  have nonzero_topic : Fintype.card Topic > 0 := by rw[card_topic]; norm_num
  have p2 := (truncOfCardPos nonzero_people).out
  let Person' := {p3 // p3 ≠ p2}
  -- want to prove that (Fintype α) and (Fintype.card α = 5).
  have hfα : Fintype Person' := sorry
  have hfcα : Fintype.card Person' = 5 := sorry
  have h1 : Fintype.card Topic * 2 < Fintype.card Person' := sorry
  have hd : DecidableEq Topic := sorry
  have h2 := Fintype.exists_lt_card_fiber_of_mul_lt_card
              (fun (p3: Person') ↦ discusses p2 p3.val) h1
  obtain ⟨t2, ht2⟩ := h2
  -- 2 < Finset.card
  --  (Finset.filter (fun x => discusses p2 ↑x = t2) Finset.univ)
  -- Call that set α.
  let α := (Finset.filter (fun (x : Person') ↦ discusses p2 ↑x = t2) Finset.univ)
--  let Person' := (Finset.filter (fun (p3: α) ↦ discusses p2 p3.val = t2) Finset.univ)

  -- If any pair of people p4 p5 in P2 discusses topic t2, then we are done.
  -- So the people in P2 must all discuss only the remaining one topic t3.
  let Topic' := {t3 // t3 ≠ t2}
  have h3 : Fintype Topic' := sorry
  have h4 : Fintype.card Topic' = 1 := sorry

  -- let t3 be the other element of Topic
  have nonzero_topic' : Fintype.card Topic' > 0 := by rw[h4]; norm_num
  have t3 := (truncOfCardPos nonzero_topic').out
  have h5 : t3.val ≠ t2 := by sorry

  obtain h6 | h7 := Classical.em (∃ p3 p4 : α, p3 ≠ p4 ∧
                                    discusses p3.val p4.val = t2)
  · obtain ⟨p3, p4, hp1, hp2⟩ := h6
    use t2
    -- the set we want is {p2,p3,p4}
    let s1 : Finset Person := {p3.val.val}
    let s2 : Finset Person := Finset.cons p4.val s1 sorry
    let s3 : Finset Person := Finset.cons p2 s2 sorry
    use s3
    constructor
    · norm_num
    · intros p1' hp1' p2' hp2' hp1p2
      rw[Finset.mem_cons, Finset.mem_cons, Finset.mem_singleton] at hp1' hp2'
      -- TODO?
      -- casesm* (_ ∨ _) + congruence closure?
      cases hp1' with
      | inl hp1' => cases hp2' with
        | inl hp2' => rw[hp1', hp2'] at hp1p2; exact (hp1p2 rfl).elim
        | inr hp2' => cases hp2' with
          | inl hp2' => rw[hp1', hp2']; have := p4.property; simp at this
                        exact this
          | inr hp2' => rw[hp1', hp2']; have := p3.property; simp at this
                        exact this
      | inr hp1' => cases hp1' with
        | inl hp1' => cases hp2' with
          | inl hp2' => rw[hp1', hp2']; have := p4.property; simp at this
                        rwa[discussion_sym (p4.val) p2]
          | inr hp2' => cases hp2' with
            | inl hp2' => rw[hp1', hp2'] at hp1p2; exact (hp1p2 rfl).elim
            | inr hp2' => rw[hp1', hp2']; rwa[discussion_sym p4.val p3.val]
        | inr hp1' => cases hp2' with
            | inl hp2' => rw[hp1', hp2']; have := p3.property; simp at this
                          rwa[discussion_sym (p3.val) p2]
            | inr hp2' => cases hp2' with
              | inl hp2' => rw[hp1', hp2']; exact hp2
              | inr hp2' => rw[hp1', hp2'] at hp1p2; exact (hp1p2 rfl).elim
  · push_neg at h7
    use t3
    let α' := Finset.map ⟨λ (x :Person') => x.val, Subtype.coe_injective⟩ α
    use α'
    constructor
    · rw[Finset.card_map]; exact ht2
    · intros p1 hp1 p2 hp2 hp1p2
      sorry

theorem imo1964_q4
    (Person Topic : Type)
    [Fintype Person]
    [Fintype Topic]
    (card_person : Fintype.card Person = 17)
    (card_topic : Fintype.card Topic = 3)
    (discusses : Person → Person → Topic)
    (discussion_sym : ∀ p1 p2 : Person, discusses p1 p2 = discusses p2 p1) :
    ∃ t : Topic, ∃ s : Finset Person,
      2 < s.card ∧
        ∀ p1 ∈ s, ∀ p2 ∈ s, p1 ≠ p2 → discusses p1 p2 = t := by
  -- Choose a person p1.
  -- By the pigeonhole principle, there must be some topic t1 such
  -- that the size of the set {p2 // p2 ≠ p1 ∧ discusses p1 p2 = t1}
  -- is at least 6. Call that set P1.
  -- If any pair of people p2 p3 in P1 discusses topic t1, then we are done.
  -- So the people in P1 must all discuss only the remaining two topics.
  -- Choose a persion p2 in P1.
  -- By the pigeonhole principle, there must be some topic t2 such that the
  -- size of the set {p3 // p3 ≠ p2 ∧ discusses p2 p3 = t2} is at least 3.
  -- Call that set P2.
  -- If any pair of people p4 p5 in P2 discusses topic t2, then we are done.
  -- So the people in P2 must all discuss only the remaining one topic t3.
  -- Since P2 has at least 3 members, we are done.
  sorry
