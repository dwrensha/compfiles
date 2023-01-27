import Mathlib.Data.Fin.Basic

/-!
# International Mathematical Olympiad 1964, Problem 4

Seventeen people correspond by mail with one another -- each one with
all the rest. In their letters only three different topics are
discussed. Each pair of correspondents deals with only one of the topics.
Prove that there are at least three people who write to each other
about the same topic.

-/

def Person := Fin 17

theorem imo1964_q4
    (topic : Person → Person → Fin 3)
    (topic_sym : ∀ p1 p2 : Person, topic p1 p2 = topic p2 p1) :
    ∃ p1 p2 p3 : Person,
      topic p1 p2 = topic p2 p3 ∧ topic p2 p3 = topic p3 p1 := by
  sorry

