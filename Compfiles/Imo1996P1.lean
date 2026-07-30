/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 1996, Problem 1

We are given a positive integer r and a rectangular board ABCD with
dimensions |AB| = 20, |BC| = 12. The rectangle is divided into a grid of
20 × 12 unit squares. The following moves are permitted on the board:
one can move from one square to another only if the distance between the
centers of the two squares is √r. The task is to find a sequence of moves
leading from the square with A as a vertex to the square with B as
a vertex.

(a) Show that the task cannot be done if r is divisible by 2 or 3.
(b) Prove that the task is possible when r = 73.
(c) Can the task be done when r = 97?
-/

namespace Imo1996P1

/- We identify each unit square with the integer coordinates `(i, j)` of its
center: `i` is the column in the direction from `A` to `B` and `j` is the row,
so `1 ≤ i ≤ 20` and `1 ≤ j ≤ 12`. The square with vertex `A` is `(1, 1)` and
the square with vertex `B` is `(20, 1)`. The centers of two squares differ by
an integer vector `(a, b)`, and the distance between the centers is
`√(a² + b²)`, so a move between them is permitted exactly when `a² + b² = r`. -/

/-- The predicate that `p` is a square of the 20 × 12 board. -/
abbrev OnBoard (p : ℤ × ℤ) : Prop := 1 ≤ p.1 ∧ p.1 ≤ 20 ∧ 1 ≤ p.2 ∧ p.2 ≤ 12

/-- A permitted move between two squares: both lie on the board and the
squared distance between their centers equals `r`. -/
abbrev Move (r : ℤ) (p q : ℤ × ℤ) : Prop :=
  OnBoard p ∧ OnBoard q ∧ (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 = r

/-- The square with vertex `A`. -/
abbrev SqA : ℤ × ℤ := (1, 1)

/-- The square with vertex `B`. -/
abbrev SqB : ℤ × ℤ := (20, 1)

snip begin

/-! ### Small arithmetic facts -/

lemma sq_mod_two (n : ℤ) : n ^ 2 % 2 = n % 2 := by
  rcases Int.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have h : (k + k) ^ 2 = 2 * (2 * k ^ 2) := by ring
    omega
  · have h : (2 * k + 1) ^ 2 = 2 * (2 * k ^ 2 + 2 * k) + 1 := by ring
    omega

lemma sq_mod_three (n : ℤ) : n ^ 2 % 3 = 0 ∨ n ^ 2 % 3 = 1 := by
  have hr : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  obtain ⟨k, hk⟩ : ∃ k : ℤ, n = 3 * k + n % 3 := ⟨n / 3, by omega⟩
  rcases hr with h | h | h
  · left
    have e : n ^ 2 = 3 * (3 * k ^ 2) := by rw [hk, h]; ring
    omega
  · right
    have e : n ^ 2 = 3 * (3 * k ^ 2 + 2 * k) + 1 := by rw [hk, h]; ring
    omega
  · right
    have e : n ^ 2 = 3 * (3 * k ^ 2 + 4 * k + 1) + 1 := by rw [hk, h]; ring
    omega

lemma sq_mod_three_eq_zero {n : ℤ} (h : n ^ 2 % 3 = 0) : n % 3 = 0 := by
  have hr : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  obtain ⟨k, hk⟩ : ∃ k : ℤ, n = 3 * k + n % 3 := ⟨n / 3, by omega⟩
  rcases hr with h0 | h0 | h0
  · exact h0
  · have e : n ^ 2 = 3 * (3 * k ^ 2 + 2 * k) + 1 := by rw [hk, h0]; ring
    omega
  · have e : n ^ 2 = 3 * (3 * k ^ 2 + 4 * k + 1) + 1 := by rw [hk, h0]; ring
    omega

/-! ### Invariants for part (a) -/

/-- If `r` is even and `a² + b² = r`, then `a ≡ b (mod 2)`, so a move
preserves the parity of `p.1 + p.2`. -/
lemma step_two {r : ℤ} (hr : 2 ∣ r) {p q : ℤ × ℤ} (h : Move r p q) :
    (p.1 + p.2) % 2 = 0 → (q.1 + q.2) % 2 = 0 := by
  obtain ⟨-, -, hdist⟩ := h
  obtain ⟨c, hc⟩ := hr
  have e1 := sq_mod_two (p.1 - q.1)
  have e2 := sq_mod_two (p.2 - q.2)
  omega

/-- If `3 ∣ r` and `a² + b² = r`, then `3 ∣ a` and `3 ∣ b`, so a move
preserves `p.1 mod 3`. -/
lemma step_three {r : ℤ} (hr : 3 ∣ r) {p q : ℤ × ℤ} (h : Move r p q) :
    p.1 % 3 = 1 → q.1 % 3 = 1 := by
  obtain ⟨-, -, hdist⟩ := h
  obtain ⟨c, hc⟩ := hr
  have h0 : ((p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2) % 3 = 0 := by omega
  have h1 := sq_mod_three (p.1 - q.1)
  have h2 := sq_mod_three (p.2 - q.2)
  have ha : (p.1 - q.1) ^ 2 % 3 = 0 := by omega
  have ha' := sq_mod_three_eq_zero ha
  omega

lemma reach_two {r : ℤ} (hr : 2 ∣ r) {p q : ℤ × ℤ}
    (h : Relation.ReflTransGen (Move r) p q) :
    (p.1 + p.2) % 2 = 0 → (q.1 + q.2) % 2 = 0 := by
  induction h with
  | refl => exact id
  | tail _ hbc ih => exact fun hp => step_two hr hbc (ih hp)

lemma reach_three {r : ℤ} (hr : 3 ∣ r) {p q : ℤ × ℤ}
    (h : Relation.ReflTransGen (Move r) p q) :
    p.1 % 3 = 1 → q.1 % 3 = 1 := by
  induction h with
  | refl => exact id
  | tail _ hbc ih => exact fun hp => step_three hr hbc (ih hp)

/-! ### The move classification for `r = 97` -/

lemma abs_le_nine {a b : ℤ} (h : a ^ 2 + b ^ 2 = 97) : |a| ≤ 9 := by
  by_contra hcon
  push Not at hcon
  have h1 : a ^ 2 ≤ 97 := by linarith [sq_nonneg b]
  by_cases hs : 0 ≤ a
  · rw [abs_of_nonneg hs] at hcon
    nlinarith [sq_nonneg (a - 10)]
  · push Not at hs
    rw [abs_of_neg hs] at hcon
    nlinarith [sq_nonneg (a + 10)]

lemma sq97_aux (A B : ℤ) (hA0 : 0 ≤ A) (hA9 : A ≤ 9) (hB0 : 0 ≤ B) (hB9 : B ≤ 9)
    (h : A ^ 2 + B ^ 2 = 97) : (A = 9 ∧ B = 4) ∨ (A = 4 ∧ B = 9) := by
  interval_cases A <;> interval_cases B <;> omega

/-- The only ways to write `97` as a sum of two squares are `81 + 16` and
`16 + 81`, so each permitted move for `r = 97` is of the form `(±9, ±4)` or
`(±4, ±9)`. -/
lemma move97 {a b : ℤ} (h : a ^ 2 + b ^ 2 = 97) :
    (|a| = 9 ∧ |b| = 4) ∨ (|a| = 4 ∧ |b| = 9) := by
  have ha := abs_le_nine h
  have hb := abs_le_nine (show b ^ 2 + a ^ 2 = 97 by linarith [h])
  exact sq97_aux |a| |b| (abs_nonneg a) ha (abs_nonneg b) hb
    (by rw [sq_abs, sq_abs]; exact h)

/-- The invariant for part (c): row membership in the central strip
`{5, 6, 7, 8}` agrees with evenness of the column. A "toggle" move `(±9, ±4)`
flips both sides of the equivalence; a move `(±4, ±9)` flips neither (such a
move cannot start or end inside the strip, and it preserves the parity of the
column). -/
lemma step97 {p q : ℤ × ℤ} (h : Move 97 p q) :
    (p.1 % 2 = 0 ↔ 5 ≤ p.2 ∧ p.2 ≤ 8) → (q.1 % 2 = 0 ↔ 5 ≤ q.2 ∧ q.2 ≤ 8) := by
  obtain ⟨hp, hq, hdist⟩ := h
  obtain ⟨hp1, hp20, hp3, hp12⟩ := hp
  obtain ⟨hq1, hq20, hq3, hq12⟩ := hq
  have hclass := move97 hdist
  rcases hclass with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
    rcases eq_or_eq_neg_of_abs_eq ha with hdx | hdx <;>
    rcases eq_or_eq_neg_of_abs_eq hb with hdy | hdy <;>
    omega

lemma reach97 {p q : ℤ × ℤ} (h : Relation.ReflTransGen (Move 97) p q) :
    (p.1 % 2 = 0 ↔ 5 ≤ p.2 ∧ p.2 ≤ 8) → (q.1 % 2 = 0 ↔ 5 ≤ q.2 ∧ q.2 ≤ 8) := by
  induction h with
  | refl => exact id
  | tail _ hbc ih => exact fun hp => step97 hbc (ih hp)

snip end

problem imo1996_p1_a (r : ℤ) (hr : 2 ∣ r ∨ 3 ∣ r) :
    ¬ Relation.ReflTransGen (Move r) SqA SqB := by
  intro h
  rcases hr with h2 | h3
  · exact absurd (reach_two h2 h (by decide)) (by decide)
  · exact absurd (reach_three h3 h (by decide)) (by decide)

problem imo1996_p1_b : Relation.ReflTransGen (Move 73) SqA SqB := by
  -- An explicit sequence of 11 moves, using `73 = 8² + 3²`.
  have s1 : Move 73 SqA (9, 4) := ⟨by decide, by decide, by decide⟩
  have s2 : Move 73 (9, 4) (17, 7) := ⟨by decide, by decide, by decide⟩
  have s3 : Move 73 (17, 7) (9, 10) := ⟨by decide, by decide, by decide⟩
  have s4 : Move 73 (9, 10) (12, 2) := ⟨by decide, by decide, by decide⟩
  have s5 : Move 73 (12, 2) (20, 5) := ⟨by decide, by decide, by decide⟩
  have s6 : Move 73 (20, 5) (12, 8) := ⟨by decide, by decide, by decide⟩
  have s7 : Move 73 (12, 8) (20, 11) := ⟨by decide, by decide, by decide⟩
  have s8 : Move 73 (20, 11) (17, 3) := ⟨by decide, by decide, by decide⟩
  have s9 : Move 73 (17, 3) (9, 6) := ⟨by decide, by decide, by decide⟩
  have s10 : Move 73 (9, 6) (17, 9) := ⟨by decide, by decide, by decide⟩
  have s11 : Move 73 (17, 9) SqB := ⟨by decide, by decide, by decide⟩
  exact Relation.ReflTransGen.head s1 (Relation.ReflTransGen.head s2
    (Relation.ReflTransGen.head s3 (Relation.ReflTransGen.head s4
    (Relation.ReflTransGen.head s5 (Relation.ReflTransGen.head s6
    (Relation.ReflTransGen.head s7 (Relation.ReflTransGen.head s8
    (Relation.ReflTransGen.head s9 (Relation.ReflTransGen.head s10
    (Relation.ReflTransGen.head s11 Relation.ReflTransGen.refl))))))))))

/- The answer to part (c): the task cannot be done when `r = 97`. -/
determine answer : Prop := ¬ Relation.ReflTransGen (Move 97) SqA SqB

problem imo1996_p1_c : answer := by
  intro h
  exact absurd (reach97 h (by decide)) (by decide)

end Imo1996P1
