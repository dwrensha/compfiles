import Mathlib.Data.Fin.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic.LibrarySearch

/-!
# International Mathematical Olympiad 1964, Problem 4

Seventeen people correspond by mail with one another -- each one with
all the rest. In their letters only three different topics are
discussed. Each pair of correspondents deals with only one of the topics.
Prove that there are at least three people who write to each other
about the same topic.

-/

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
