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

#check Subtype.val_injective
#check Fintype.card_eq_one_iff

theorem lemma1
    (Person Topic : Type)
    [Fintype Person]
    [Fintype Topic]
    [DecidableEq Topic]
    (card_person : 5 < Fintype.card Person)
    (card_topic : Fintype.card Topic = 2)
    (discusses : Person → Person → Topic)
    (discussion_sym : ∀ p1 p2 : Person, discusses p1 p2 = discusses p2 p1) :
    ∃ t : Topic, ∃ s : Finset Person,
      2 < s.card ∧
        ∀ p1 ∈ s, ∀ p2 ∈ s, p1 ≠ p2 → discusses p1 p2 = t := by
  -- By the pigeonhole principle, there must be some topic t2 such that the
  -- size of the set {p3 // p3 ≠ p2 ∧ discusses p2 p3 = t2} is at least 3.
  have nonzero_people : Fintype.card Person > 0 := sorry --by rw[card_person]; norm_num
  have nonzero_topic : Fintype.card Topic > 0 := by rw[card_topic]; norm_num
  have p2 := (truncOfCardPos nonzero_people).out
  let Person' := {p3 // p3 ≠ p2}
  -- want to prove that (Fintype α) and (Fintype.card α = 5).
  have hfα : Fintype Person' := Fintype.ofFinite Person'
  have hfcα : 4 < Fintype.card Person' := sorry
  have h1 : Fintype.card Topic * 2 < Fintype.card Person' := by
      sorry --rw[hfcα, card_topic]; norm_num
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
  have h3 : Fintype Topic' := Fintype.ofFinite Topic'
  have h4 : Fintype.card Topic' = 1 := sorry

  -- let t3 be the other element of Topic
  obtain ⟨t3, ht3⟩ := Fintype.card_eq_one_iff.mp h4

  have h5 : t3.val ≠ t2 := by sorry

  obtain h6 | h7 := Classical.em (∃ p3 p4 : α, p3 ≠ p4 ∧
                                    discusses p3.val p4.val = t2)
  · obtain ⟨p3, p4, hp1, hp2⟩ := h6
    use t2
    -- the set we want is {p2,p3,p4}
    let s1 : Finset Person := {p3.val.val}
    let s2 : Finset Person := Finset.cons p4.val s1
                               (by simp; intro hp
                                   exact (hp1 (Subtype.val_injective
                                          (Subtype.val_injective hp)).symm).elim)
    let s3 : Finset Person := Finset.cons p2 s2
                               (by simp; intro hp;
                                   cases hp with
                                   | inl hp =>
                                     exact (p4.val.property.symm hp).elim
                                   | inr hp =>
                                     exact (p3.val.property.symm hp).elim)
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
    · intros p3' hp3' p4' hp4' hp3p4'
      have h11 : p3' ≠ p2 := by
        intro hh; rw[hh] at hp3'; simp at hp3'
      have h12 : p4' ≠ p2 := by
        intro hh; rw[hh] at hp4'; simp at hp4'

      have h13 : discusses p2 p3' = t2 := by
        simp at hp3'
        obtain ⟨x, hx1, hx2, hx3⟩ := hp3'
        rwa[ hx3] at hx1

      have h14 : discusses p2 p4' = t2 := by
        simp at hp4'
        obtain ⟨x, hx1, hx2, hx3⟩ := hp4'
        rwa[hx3] at hx1

      let p3 : { x // x ∈ α} := ⟨⟨p3', h11⟩, by simp[h13]⟩
      let p4 : { x // x ∈ α} := ⟨⟨p4', h12⟩, by simp[h14]⟩
      have h5 : p3 ≠ p4 := by
        intro hp3p4
        have hp3p4A : p3.val = p4.val := (congrArg Subtype.val hp3p4)
        have hp3p4B : p3.val.val = p4.val.val := (congrArg Subtype.val hp3p4A)
        simp at hp3p4B
        exact hp3p4' hp3p4B
      have h8 := h7 p3 p4 h5
      let t3': Topic' := ⟨discusses p3.val.val p4.val.val, h8⟩
      have h9 := ht3 t3'
      rw[←h9]

#check Finset.card_cons

theorem imo1964_q4
    (Person Topic : Type)
    [Fintype Person]
    [DecidableEq Person]
    [Fintype Topic]
    [DecidableEq Topic]
    (card_person : Fintype.card Person = 17)
    (card_topic : Fintype.card Topic = 3)
    (discusses : Person → Person → Topic)
    (discussion_sym : ∀ p1 p2 : Person, discusses p1 p2 = discusses p2 p1) :
    ∃ t : Topic, ∃ s : Finset Person,
      2 < s.card ∧
        ∀ p1 ∈ s, ∀ p2 ∈ s, p1 ≠ p2 → discusses p1 p2 = t := by
  -- Choose a person p1.
  have nonzero_people : Fintype.card Person > 0 := by rw[card_person]; norm_num
  have nonzero_topic : Fintype.card Topic > 0 := by rw[card_topic]; norm_num
  have p1 := (truncOfCardPos nonzero_people).out
  let Person' := {p2 // p2 ≠ p1}

  -- By the pigeonhole principle, there must be some topic t1 such
  -- that the size of the set {p2 // p2 ≠ p1 ∧ discusses p1 p2 = t1}
  -- is at least 6.

  have hfα : Fintype Person' := Fintype.ofFinite Person'
  have hfcα : Fintype.card Person' = 16 := sorry
  have h1 : Fintype.card Topic * 5 < Fintype.card Person' := by
      rw[hfcα, card_topic]; norm_num

  have h2 := Fintype.exists_lt_card_fiber_of_mul_lt_card
              (fun (p2: Person') ↦ discusses p1 p2.val) h1
  obtain ⟨t1, ht1⟩ := h2

  -- Call that set α.
  let α := (Finset.filter (fun (x : Person') ↦ discusses p1 ↑x = t1) Finset.univ)

  have cardα : 5 < Fintype.card α := by sorry

  -- If any pair of people p2 p3 in α discusses topic t1, then we are done.
  obtain h6 | h7 := Classical.em (∃ p2 p3 : α, p2 ≠ p3 ∧
                                    discusses p2.val p3.val = t1)
  · obtain ⟨p3, p4, hp1, hp2⟩ := h6
    use t1
    -- the set we want is {p1,p3,p4}
    let s1 : Finset Person := {p3.val.val}

    have hs1 : ¬ p4.val.val ∈ s1 := by
      simp; intro hp
      exact (hp1 (Subtype.val_injective (Subtype.val_injective hp)).symm).elim

    let s2 : Finset Person := Finset.cons p4.val s1 hs1

    have hs2 : ¬ p1 ∈ s2 := by
      simp; intro hp
      cases hp with
      | inl hp => exact (p4.val.property.symm hp).elim
      | inr hp => exact (p3.val.property.symm hp).elim

    let s3 : Finset Person := Finset.cons p1 s2 hs2
    use s3
    constructor
    · rw[Finset.card_cons hs2, Finset.card_cons hs1]; simp
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
                        rwa[discussion_sym (p4.val) p1]
          | inr hp2' => cases hp2' with
            | inl hp2' => rw[hp1', hp2'] at hp1p2; exact (hp1p2 rfl).elim
            | inr hp2' => rw[hp1', hp2']; rwa[discussion_sym p4.val p3.val]
        | inr hp1' => cases hp2' with
            | inl hp2' => rw[hp1', hp2']; have := p3.property; simp at this
                          rwa[discussion_sym (p3.val) p1]
            | inr hp2' => cases hp2' with
              | inl hp2' => rw[hp1', hp2']; exact hp2
              | inr hp2' => rw[hp1', hp2'] at hp1p2; exact (hp1p2 rfl).elim

  · sorry
/-
    -- So the people in α must all discuss only the remaining two topics.
    push_neg at h7
    let Topic' := {t2 // t2 ≠ t1}
    have h3 : Fintype Topic' := Fintype.ofFinite Topic'
    have h4 : Fintype.card Topic' = 2 := sorry
    have nonzero_topic' : Fintype.card Topic' > 0 := by rw[h4]; norm_num
    have t0 := (truncOfCardPos nonzero_topic').out

    let discusses' : α → α → Topic' :=
      fun (p2 p3 : α) ↦
        if heq : p2 = p3 then t0
        else
        ⟨discusses p2.val p3.val,
         by have := h7 ⟨p2, Finset.coe_mem p2⟩ ⟨p3, Finset.coe_mem p3⟩
            simp at this
            push_neg at this
            apply this
            exact heq⟩
    have discusses_sym' :
        ∀ (p1 p2 : { x // x ∈ α }), discusses' p1 p2 = discusses' p2 p1 := by
      intros p3 p4
      simp
      split_ifs with hf1 hf2 hf3
      · rfl
      · exact (hf2 hf1.symm).elim
      · exact (hf1 hf3.symm).elim
      · simp[discussion_sym]
    have h5 := lemma1 α Topic' cardα h4 discusses' discusses_sym'
    obtain ⟨t2, s, hs1, hs2⟩ := h5
    use t2
    let s' := Finset.map ⟨λ (x : α) => x.val, Subtype.coe_injective⟩ s
    let s'' := Finset.map ⟨λ (x : Person') => x.val, Subtype.coe_injective⟩ s'
    use s''
    constructor
    · rwa[Finset.card_map, Finset.card_map]
    · intros p3 hp3 p4 hp4 hp34
      have h11 : p3 ≠ p1 := by
        intro hh; rw[hh] at hp3; simp at hp3

      have h13 : discusses p1 p3 = t1 := by
        simp at hp3
        obtain ⟨x, hx1, hx2⟩ := hp3
        exact hx1

      let p3' : {x // x ∈ α} := ⟨⟨p3, h11⟩, (by simp[h13])⟩
      have hp3' : p3' ∈ s := by
        simp at hp3
        obtain ⟨x,hx1,hx2⟩ := hp3
        simp[hx2]

      have h12 : p4 ≠ p1 := by
        intro hh; rw[hh] at hp4; simp at hp4

      have h14 : discusses p1 p4 = t1 := by
        simp at hp4
        obtain ⟨x, hx1, hx2⟩ := hp4
        exact hx1

      let p4' : {x // x ∈ α} := ⟨⟨p4, h12⟩, by simp[h14]⟩
      have hp4' : p4' ∈ s := by
        simp at hp4
        obtain ⟨x,hx1,hx2⟩ := hp4
        simp[hx2]

      have h7 : p3' ≠ p4' := by
        intro hp3p4
        have hp3p4A : p3'.val = p4'.val := (congrArg Subtype.val hp3p4)
        have hp3p4B : p3'.val.val = p4'.val.val := (congrArg Subtype.val hp3p4A)
        simp at hp3p4B
        exact hp34 hp3p4B
      have h6 := hs2 p3' hp3' p4' hp4' h7
      simp[hp34] at h6
      exact (congrArg Subtype.val h6)
-/
