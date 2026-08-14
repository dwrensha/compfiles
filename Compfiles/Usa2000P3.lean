/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Int.Star
public import Mathlib.Data.List.Permutation
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2000, Problem 3

A player starts with A blue cards, B red cards and C white cards. He scores
points as he plays each card. If he plays a blue card, his score is the number
of white cards remaining in his hand. If he plays a red card it is three times
the number of blue cards remaining in his hand. If he plays a white card, it is
twice the number of red cards remaining in his hand. What is the lowest
possible score as a function of A, B and C and how many different ways can it
be achieved?
-/

namespace Usa2000P3

/-- The three colors of cards. -/
inductive Card where
  | blue
  | red
  | white
  deriving BEq, DecidableEq

instance : LawfulBEq Card where
  eq_of_beq := fun {a b} => by
    cases a <;> cases b <;> intro h <;> first | rfl | (exact absurd h (by decide))
  rfl := fun {a} => by cases a <;> rfl

/-- The score accumulated when playing the sequence of cards `l`, listed in the
order they are played. When a blue card is played, the score gained is the
number of white cards remaining; for a red card it is three times the number of
blue cards remaining; for a white card it is twice the number of red cards
remaining. -/
def score : List Card → ℕ
  | [] => 0
  | .blue :: t => t.count .white + score t
  | .red :: t => 3 * t.count .blue + score t
  | .white :: t => 2 * t.count .red + score t

/-- The canonical play: all blue cards, then all red cards, then all white
cards. Every play with the same card counts is a permutation of this one. -/
def canonicalPlay (A B C : ℕ) : List Card :=
  List.replicate A .blue ++ (List.replicate B .red ++ List.replicate C .white)

/-- The finite set of all plays with `A` blue, `B` red and `C` white cards. -/
def plays (A B C : ℕ) : Finset (List Card) :=
  (canonicalPlay A B C).permutations.toFinset

determine lowestScore (A B C : ℕ) : ℕ := min (min (A * C) (3 * A * B)) (2 * B * C)

/-- The number of different ways the lowest score can be achieved. -/
determine fewestWays (A B C : ℕ) : ℕ :=
  if A = 0 ∧ B = 0 ∧ C = 0 then 1
  else if C = 3 * B ∧ A = 2 * B then A + B + C
  else if C = 3 * B ∧ A < 2 * B then A + 1
  else if 3 * A = 2 * C ∧ 2 * B < A then B + 1
  else if A = 2 * B ∧ C < 3 * B then C + 1
  else 1

snip begin

@[simp] lemma score_nil : score [] = 0 := rfl
@[simp] lemma score_cons_blue (t : List Card) :
    score (.blue :: t) = t.count .white + score t := rfl
@[simp] lemma score_cons_red (t : List Card) :
    score (.red :: t) = 3 * t.count .blue + score t := rfl
@[simp] lemma score_cons_white (t : List Card) :
    score (.white :: t) = 2 * t.count .red + score t := rfl

lemma mem_plays {A B C : ℕ} {l : List Card} :
    l ∈ plays A B C ↔ l.count .blue = A ∧ l.count .red = B ∧ l.count .white = C := by
  rw [plays, List.mem_toFinset, List.mem_permutations, List.perm_iff_count]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · have hb := h .blue
      simpa [canonicalPlay, List.count_replicate] using hb
    · have hr := h .red
      simpa [canonicalPlay, List.count_replicate] using hr
    · have hw := h .white
      simpa [canonicalPlay, List.count_replicate] using hw
  · rintro ⟨hb, hr, hw⟩
    intro a
    rcases a with _ | _ | _ <;>
      simp [canonicalPlay, List.count_replicate, hb, hr, hw]

-- Purely arithmetic facts about `lowestScore` and `fewestWays`.

lemma lowestScore_cases (A B C : ℕ) :
    lowestScore A B C = A * C ∨ lowestScore A B C = 3 * A * B ∨
      lowestScore A B C = 2 * B * C := by
  unfold lowestScore
  rcases le_total (A * C) (3 * A * B) with h | h
  · rw [min_eq_left h]
    rcases le_total (A * C) (2 * B * C) with h2 | h2
    · exact Or.inl (min_eq_left h2)
    · exact Or.inr (Or.inr (min_eq_right h2))
  · rw [min_eq_right h]
    rcases le_total (3 * A * B) (2 * B * C) with h2 | h2
    · exact Or.inr (Or.inl (min_eq_left h2))
    · exact Or.inr (Or.inr (min_eq_right h2))

-- Score computations.

variable (A B C : ℕ)

lemma lowestScore_le_ac : lowestScore A B C ≤ A * C :=
  le_trans (min_le_left _ _) (min_le_left _ _)

lemma lowestScore_le_ab : lowestScore A B C ≤ 3 * A * B :=
  le_trans (min_le_left _ _) (min_le_right _ _)

lemma lowestScore_le_bc : lowestScore A B C ≤ 2 * B * C :=
  min_le_right _ _

lemma lowestScore_eq_ac (hA : 0 < A) (hC : 0 < C) (h : ¬(C ≤ 3 * B ∧ A ≤ 2 * B)) : lowestScore A B C ≠ A * C := by
  simp [lowestScore, -not_and]
  rw [mul_le_mul_iff_left₀ hC]
  move_mul [A]
  rwa [mul_le_mul_iff_left₀ hA]

lemma lowestScore_zero_b_c : lowestScore 0 B C = 0 := by simp [lowestScore]

lemma lowestScore_a_zero_c : lowestScore A 0 C = 0 := by simp [lowestScore]

lemma lowestScore_a_b_zero : lowestScore A B 0 = 0 := by simp [lowestScore]

lemma lowestScore_le_add_blue :
    lowestScore (A + 1) B C ≤ C + lowestScore A B C := by
  rcases lowestScore_cases A B C with h | h | h
  · calc lowestScore (A + 1) B C ≤ (A + 1) * C :=
          le_trans (min_le_left _ _) (min_le_left _ _)
      _ = C + A * C := by ring
      _ = C + lowestScore A B C := by rw [h]
  · have b1 : 3 * A * B ≤ A * C := by rw [← h]; exact lowestScore_le_ac A B C
    by_cases hA : A = 0
    · subst hA
      have hL0 : lowestScore 0 B C = 0 := by
        apply le_antisymm
        · calc lowestScore 0 B C ≤ 3 * 0 * B := lowestScore_le_ab 0 B C
            _ = 0 := by ring
        · exact Nat.zero_le _
      rw [hL0]
      calc lowestScore (0 + 1) B C ≤ (0 + 1) * C :=
            le_trans (min_le_left _ _) (min_le_left _ _)
        _ = C := by ring
        _ ≤ C + 0 := by omega
    · have hA' : 0 < A := Nat.pos_of_ne_zero hA
      have h3 : 3 * B ≤ C := by nlinarith [b1, hA']
      calc lowestScore (A + 1) B C ≤ 3 * (A + 1) * B :=
            le_trans (min_le_left _ _) (min_le_right _ _)
        _ = 3 * A * B + 3 * B := by ring
        _ ≤ 3 * A * B + C := by omega
        _ = C + 3 * A * B := by ring
        _ = C + lowestScore A B C := by rw [h]
  · calc lowestScore (A + 1) B C ≤ 2 * B * C := min_le_right _ _
      _ ≤ C + 2 * B * C := by omega
      _ = C + lowestScore A B C := by rw [h]

lemma lowestScore_le_add_red (A B C : ℕ) :
    lowestScore A (B + 1) C ≤ 3 * A + lowestScore A B C := by
  rcases lowestScore_cases A B C with h | h | h
  · calc lowestScore A (B + 1) C ≤ A * C :=
          le_trans (min_le_left _ _) (min_le_left _ _)
      _ ≤ 3 * A + A * C := by omega
      _ = 3 * A + lowestScore A B C := by rw [h]
  · calc lowestScore A (B + 1) C ≤ 3 * A * (B + 1) :=
          le_trans (min_le_left _ _) (min_le_right _ _)
      _ = 3 * A + 3 * A * B := by ring
      _ = 3 * A + lowestScore A B C := by rw [h]
  · have b1 : 2 * B * C ≤ A * C := by rw [← h]; exact lowestScore_le_ac A B C
    have b2 : 2 * B * C ≤ 3 * A * B := by rw [← h]; exact lowestScore_le_ab A B C
    by_cases h32 : 2 * C ≤ 3 * A
    · calc lowestScore A (B + 1) C ≤ 2 * (B + 1) * C := min_le_right _ _
        _ = 2 * B * C + 2 * C := by ring
        _ ≤ 2 * B * C + 3 * A := by omega
        _ = 3 * A + 2 * B * C := by ring
        _ = 3 * A + lowestScore A B C := by rw [h]
    · push Not at h32
      have hB : B = 0 := by
        by_contra hB
        have hB' : 0 < B := Nat.pos_of_ne_zero hB
        nlinarith [b2, hB', h32]
      subst hB
      have hL0 : lowestScore A 0 C = 0 := by
        apply le_antisymm
        · calc lowestScore A 0 C ≤ 3 * A * 0 := lowestScore_le_ab A 0 C
            _ = 0 := by ring
        · exact Nat.zero_le _
      rw [hL0]
      calc lowestScore A (0 + 1) C ≤ 3 * A * (0 + 1) :=
            le_trans (min_le_left _ _) (min_le_right _ _)
        _ = 3 * A := by ring
        _ ≤ 3 * A + 0 := by omega

lemma lowestScore_le_add_white (A B C : ℕ) :
    lowestScore A B (C + 1) ≤ 2 * B + lowestScore A B C := by
  rcases lowestScore_cases A B C with h | h | h
  · have b3 : A * C ≤ 2 * B * C := by rw [← h]; exact lowestScore_le_bc A B C
    by_cases hA2 : A ≤ 2 * B
    · calc lowestScore A B (C + 1) ≤ A * (C + 1) :=
            le_trans (min_le_left _ _) (min_le_left _ _)
        _ = A * C + A := by ring
        _ ≤ A * C + 2 * B := by omega
        _ = 2 * B + A * C := by ring
        _ = 2 * B + lowestScore A B C := by rw [h]
    · push Not at hA2
      have hC : C = 0 := by
        by_contra hC
        have hC' : 0 < C := Nat.pos_of_ne_zero hC
        nlinarith [b3, hC', hA2]
      subst hC
      have hL0 : lowestScore A B 0 = 0 := by
        apply le_antisymm
        · calc lowestScore A B 0 ≤ A * 0 := lowestScore_le_ac A B 0
            _ = 0 := by ring
        · exact Nat.zero_le _
      rw [hL0]
      calc lowestScore A B (0 + 1) ≤ 2 * B * (0 + 1) := min_le_right _ _
        _ = 2 * B := by ring
        _ ≤ 2 * B + 0 := by omega
  · calc lowestScore A B (C + 1) ≤ 3 * A * B :=
          le_trans (min_le_left _ _) (min_le_right _ _)
      _ ≤ 2 * B + 3 * A * B := by omega
      _ = 2 * B + lowestScore A B C := by rw [h]
  · calc lowestScore A B (C + 1) ≤ 2 * B * (C + 1) := min_le_right _ _
      _ = 2 * B + 2 * B * C := by ring
      _ = 2 * B + lowestScore A B C := by rw [h]

lemma tight_blue (A B C : ℕ) :
    C + lowestScore A B C = lowestScore (A + 1) B C ↔
      lowestScore (A + 1) B C = (A + 1) * C := by
  constructor
  · intro he
    by_cases hC : C = 0
    · subst hC
      have hz : lowestScore (A + 1) B 0 = 0 := by
        apply le_antisymm
        · calc lowestScore (A + 1) B 0 ≤ 2 * B * 0 := min_le_right _ _
            _ = 0 := by ring
        · exact Nat.zero_le _
      rw [hz]; ring
    · by_cases hA : A = 0
      · subst hA
        have hL0 : lowestScore 0 B C = 0 := lowestScore_zero_b_c B C
        rw [hL0] at he
        rw [← he]; ring
      · have hA' : 0 < A := Nat.pos_of_ne_zero hA
        have hC' : 0 < C := Nat.pos_of_ne_zero hC
        have b3 : C + lowestScore A B C ≤ 2 * B * C := by
          rw [he]; exact min_le_right _ _
        have hne : lowestScore A B C ≠ 2 * B * C := by
          intro hh
          rw [hh] at b3
          nlinarith [b3, hC']
        rcases lowestScore_cases A B C with h | h | h
        · rw [← he, h]; ring
        · have b2 : C + 3 * A * B ≤ 3 * (A + 1) * B := by
            have e := lowestScore_le_ab (A + 1) B C
            rw [← he, h] at e
            exact e
          have hC3 : C ≤ 3 * B := by nlinarith [b2]
          have b1 : 3 * A * B ≤ A * C := by rw [← h]; exact lowestScore_le_ac A B C
          have h3B : 3 * B ≤ C := by nlinarith [b1, hA']
          have hCe : C = 3 * B := le_antisymm hC3 h3B
          rw [← he, h, hCe]; ring
        · exact absurd h hne
  · intro hmin
    have le1 : (A + 1) * C ≤ 3 * (A + 1) * B := by
      rw [← hmin]; exact le_trans (min_le_left _ _) (min_le_right _ _)
    have le2 : (A + 1) * C ≤ 2 * B * C := by
      rw [← hmin]; exact min_le_right _ _
    have g1 : A * C ≤ 3 * A * B := by
      have h3 : C ≤ 3 * B := by nlinarith [le1, Nat.succ_pos A]
      nlinarith [h3, Nat.zero_le A]
    have g2 : A * C ≤ 2 * B * C := by nlinarith [le2]
    have hL : lowestScore A B C = A * C := by
      apply le_antisymm
      · exact lowestScore_le_ac A B C
      · exact le_min (le_min (le_refl _) g1) g2
    rw [hL, hmin]; ring

lemma tight_red (A B C : ℕ) :
    3 * A + lowestScore A B C = lowestScore A (B + 1) C ↔
      lowestScore A (B + 1) C = 3 * A * (B + 1) := by
  constructor
  · intro he
    by_cases hA : A = 0
    · subst hA
      have hz : lowestScore 0 (B + 1) C = 0 := lowestScore_zero_b_c (B + 1) C
      rw [hz]; ring
    · by_cases hC : C = 0
      · subst hC
        have hL0 : lowestScore A B 0 = 0 := by
          apply le_antisymm
          · calc lowestScore A B 0 ≤ A * 0 := lowestScore_le_ac A B 0
              _ = 0 := by ring
          · exact Nat.zero_le _
        have hL0' : lowestScore A (B + 1) 0 = 0 := lowestScore_a_b_zero A (B + 1)
        rw [hL0, hL0'] at he
        have hAz : A = 0 := by omega
        exact absurd hAz hA
      · have hA' : 0 < A := Nat.pos_of_ne_zero hA
        have b1 : 3 * A + lowestScore A B C ≤ A * C := by
          rw [he]; exact le_trans (min_le_left _ _) (min_le_left _ _)
        have hne : lowestScore A B C ≠ A * C := by
          intro hh
          rw [hh] at b1
          nlinarith [b1, hA']
        rcases lowestScore_cases A B C with h | h | h
        · exact absurd h hne
        · rw [← he, h]; ring
        · by_cases hB : B = 0
          · subst hB
            have hL0 : lowestScore A 0 C = 0 := lowestScore_a_zero_c A C
            rw [← he, hL0]; ring
          · have hB' : 0 < B := Nat.pos_of_ne_zero hB
            have b3 : 3 * A + 2 * B * C ≤ 2 * (B + 1) * C := by
              have e := lowestScore_le_bc A (B + 1) C
              rw [← he, h] at e
              exact e
            have h32 : 3 * A ≤ 2 * C := by nlinarith [b3]
            have b2L : 2 * B * C ≤ 3 * A * B := by rw [← h]; exact lowestScore_le_ab A B C
            by_cases heq : 2 * B * C = 3 * A * B
            · rw [← he, h, heq]; ring
            · have hlt : 2 * B * C < 3 * A * B := lt_of_le_of_ne b2L heq
              have h23 : 2 * C < 3 * A := by nlinarith [hlt, hB']
              omega
  · intro hmin
    have le1 : 3 * A * (B + 1) ≤ A * C := by
      rw [← hmin]; exact le_trans (min_le_left _ _) (min_le_left _ _)
    have le2 : 3 * A * (B + 1) ≤ 2 * (B + 1) * C := by
      rw [← hmin]; exact min_le_right _ _
    have g1 : 3 * A * B ≤ A * C := by nlinarith [le1]
    have g2 : 3 * A * B ≤ 2 * B * C := by
      have h32 : 3 * A ≤ 2 * C := by nlinarith [le2, Nat.succ_pos B]
      nlinarith [h32, Nat.zero_le B]
    have hL : lowestScore A B C = 3 * A * B := by
      apply le_antisymm
      · exact lowestScore_le_ab A B C
      · exact le_min (le_min g1 (le_refl _)) g2
    rw [hL, hmin]; ring

lemma tight_white (A B C : ℕ) :
    2 * B + lowestScore A B C = lowestScore A B (C + 1) ↔
      lowestScore A B (C + 1) = 2 * B * (C + 1) := by
  constructor
  · intro he
    by_cases hB : B = 0
    · subst hB
      have hz : lowestScore A 0 (C + 1) = 0 := lowestScore_a_zero_c A (C + 1)
      rw [hz]; ring
    · by_cases hA : A = 0
      · subst hA
        have hL0 : lowestScore 0 B C = 0 := lowestScore_zero_b_c B C
        have hL0' : lowestScore 0 B (C + 1) = 0 := lowestScore_zero_b_c B (C + 1)
        rw [hL0, hL0'] at he
        have hBz : B = 0 := by omega
        exact absurd hBz hB
      · have hA' : 0 < A := Nat.pos_of_ne_zero hA
        have hB' : 0 < B := Nat.pos_of_ne_zero hB
        have b2 : 2 * B + lowestScore A B C ≤ 3 * A * B := by
          rw [he]; exact le_trans (min_le_left _ _) (min_le_right _ _)
        have hne : lowestScore A B C ≠ 3 * A * B := by
          intro hh
          rw [hh] at b2
          nlinarith [b2, hB']
        rcases lowestScore_cases A B C with h | h | h
        · by_cases hC : C = 0
          · subst hC
            have hL0 : lowestScore A B 0 = 0 := lowestScore_a_b_zero A B
            rw [← he, hL0]; ring
          · have hC' : 0 < C := Nat.pos_of_ne_zero hC
            have b1 : 2 * B + A * C ≤ A * (C + 1) := by
              have e := lowestScore_le_ac A B (C + 1)
              rw [← he, h] at e
              exact e
            have h2A : 2 * B ≤ A := by nlinarith [b1]
            have b3 : 2 * B + A * C ≤ 2 * B * (C + 1) := by
              have e := lowestScore_le_bc A B (C + 1)
              rw [← he, h] at e
              exact e
            have hA2 : A ≤ 2 * B := by nlinarith [b3, hC']
            have hAe : A = 2 * B := le_antisymm hA2 h2A
            rw [← he, h, hAe]; ring
        · exact absurd h hne
        · rw [← he, h]; ring
  · intro hmin
    have le1 : 2 * B * (C + 1) ≤ A * (C + 1) := by
      rw [← hmin]; exact le_trans (min_le_left _ _) (min_le_left _ _)
    have le2 : 2 * B * (C + 1) ≤ 3 * A * B := by
      rw [← hmin]; exact le_trans (min_le_left _ _) (min_le_right _ _)
    have g1 : 2 * B * C ≤ A * C := by
      have h2A : 2 * B ≤ A := by nlinarith [le1, Nat.succ_pos C]
      nlinarith [h2A, Nat.zero_le C]
    have g2 : 2 * B * C ≤ 3 * A * B := by nlinarith [le2]
    have hL : lowestScore A B C = 2 * B * C := by
      apply le_antisymm
      · exact lowestScore_le_bc A B C
      · exact le_min (le_min g1 g2) (le_refl _)
    rw [hL, hmin]; ring

lemma fewestWays_zero_b_c : fewestWays 0 B C = 1 := by lia

lemma fewestWays_a_zero_c : fewestWays A 0 C = 1 := by lia

lemma fewestWays_a_b_zero : fewestWays A B 0 = 1 := by lia

set_option maxHeartbeats 0 in
lemma fewestWays_rec (A B C : ℕ) (h : 0 < A + B + C) :
    fewestWays A B C =
      (if 0 < A ∧ lowestScore A B C = A * C then fewestWays (A - 1) B C else 0) +
      (if 0 < B ∧ lowestScore A B C = 3 * A * B then fewestWays A (B - 1) C else 0) +
      (if 0 < C ∧ lowestScore A B C = 2 * B * C then fewestWays A B (C - 1) else 0) := by
  by_cases h2 : C = 3 * B ∧ A = 2 * B
  · -- C = 3B, A = 2B: value A + B + C
    obtain ⟨rfl, rfl⟩ := h2
    have eLHS : fewestWays (2 * B) B (3 * B) = (2 * B) + B + (3 * B) := by lia
    lia
  · by_cases h3 : C = 3 * B ∧ A < 2 * B
    · -- C = 3B, A < 2B: value A + 1
      obtain ⟨rfl, hA2⟩ := h3
      have eLHS : fewestWays A B (3 * B) = A + 1 := by lia
      have hL : lowestScore A B (3 * B) = 3 * A * B := by
        apply le_antisymm
        · exact lowestScore_le_ab A B (3 * B)
        · have e1 : 3 * A * B ≤ A * (3 * B) := by lia
          have e2 : 3 * A * B ≤ 2 * B * (3 * B) := by nlinarith only [hA2, Nat.zero_le B]
          refine le_min (le_min e1 (le_refl _)) e2
      have c1t : lowestScore A B (3 * B) = A * (3 * B) := by rw [hL]; ring
      have c3f : ¬ (0 < (3 * B) ∧ lowestScore A B (3 * B) = 2 * B * (3 * B)) := by
        intro hh
        have e : 3 * A * B = 2 * B * (3 * B) := by rw [← hL]; exact hh.2
        have hB : 0 < B := by lia
        nlinarith only [e, hA2, hB]
      rw [eLHS, ite_eq_right c3f]
      lia
    · replace h3 : ¬ (C = 3 * B ∧ A ≤ 2 * B) := by lia
      clear h2
      by_cases h4 : 3 * A = 2 * C ∧ 2 * B < A
      · -- 3A = 2C, 2B < A: value B + 1
        clear h3
        obtain ⟨hAC, hBA⟩ := h4
        have hA' : 0 < A := by lia
        have hC' : 0 < C := by lia
        have hC3 : 3 * B < C := by lia
        have eLHS : fewestWays A B C = B + 1 := by lia
        have hL : lowestScore A B C = 3 * A * B := by
          apply le_antisymm
          · exact lowestScore_le_ab A B C
          · have e1 : 3 * A * B ≤ A * C := by nlinarith only [hC3, Nat.zero_le A]
            have e2 : 3 * A * B ≤ 2 * B * C := by rw [hAC]; lia
            exact le_min (le_min e1 (le_refl _)) e2
        simp_rw [eLHS, hL]
        have c1f : ¬ (0 < A ∧ 3 * A * B = A * C) := by
          intro hh
          have e : 3 * A * B = A * C := hh.2
          nlinarith only [e, hC3, hA']
        have c3t : 3 * A * B = 2 * B * C := by rw [hAC]; ring
        rw [ite_eq_right c1f]
        rcases Nat.eq_zero_or_pos B with rfl | hB'
        · rw [ite_eq_right (fun hh => absurd hh.1 (lt_irrefl 0)), ite_eq_left ⟨hC', c3t⟩, fewestWays_a_zero_c]
        · rw [ite_eq_left ⟨hB', True.intro⟩, ite_eq_left ⟨hC', c3t⟩]
          lia
      · by_cases h5 : A = 2 * B ∧ C < 3 * B
        · -- A = 2B, C < 3B: value C + 1
          obtain ⟨hA, hC3⟩ := h5
          have hB : 0 < B := by lia
          have hA' : 0 < A := by lia
          have eLHS : fewestWays A B C = C + 1 := by lia
          have hL : lowestScore A B C = 2 * B * C := by
            apply le_antisymm
            · exact lowestScore_le_bc A B C
            · have e1 : 2 * B * C ≤ A * C := by nlinarith only [hA, Nat.zero_le C]
              have e2 : 2 * B * C ≤ 3 * A * B := by nlinarith only [hA, hC3, hB]
              exact le_min (le_min e1 e2) (le_refl _)
          have c1t : lowestScore A B C = A * C := by rw [hL, hA]
          have c2f : ¬ (0 < B ∧ lowestScore A B C = 3 * A * B) := by
            intro hh
            have e : 2 * B * C = 3 * A * B := by rw [← hL]; exact hh.2
            nlinarith only [e, hA, hC3, hB]
          rw [eLHS, ite_eq_left ⟨hA', c1t⟩, ite_eq_right c2f]
          rcases Nat.eq_zero_or_pos C with rfl | hC'
          · rw [ite_eq_right (fun hh => absurd hh.1 (lt_irrefl 0)), fewestWays_a_b_zero]
          · rw [ite_eq_left ⟨hC', hL⟩]
            lia
        · -- else branch: value 1
          have eLHS : fewestWays A B C = 1 := by lia
          rcases lowestScore_cases A B C with hL | hL | hL
          · -- L = A * C
            have f2 : A * C ≤ 3 * A * B := by rw [← hL]; exact lowestScore_le_ab A B C
            have f3 : A * C ≤ 2 * B * C := by rw [← hL]; exact lowestScore_le_bc A B C
            rcases Nat.eq_zero_or_pos A with rfl | hA'
            · have hL0 : lowestScore 0 B C = 0 := lowestScore_zero_b_c _ _
              rcases Nat.eq_zero_or_pos B with rfl | hB'
              · have hC' : 0 < C := by lia
                rw [eLHS, ite_eq_right (fun hh => absurd hh.1 (lt_irrefl 0)),
                  ite_eq_right (fun hh => absurd hh.1 (lt_irrefl 0)),
                  ite_eq_left ⟨hC', by rw [hL0]; ring⟩,
                  fewestWays_a_zero_c]
              · have c3f : ¬ (0 < C ∧ lowestScore 0 B C = 2 * B * C) := by
                  intro hh
                  rw [hL0] at hh
                  nlinarith only [hh.2, hB', hh.1]
                rw [eLHS, ite_eq_right (fun hh => absurd hh.1 (lt_irrefl 0)),
                  ite_eq_left ⟨hB', by rw [hL0]; ring⟩, ite_eq_right c3f, fewestWays_zero_b_c]
            · have c2f : ¬ (0 < B ∧ lowestScore A B C = 3 * A * B) := by
                intro hh
                have e : A * C = 3 * A * B := by rw [← hL]; exact hh.2
                have hC3 : C = 3 * B := by nlinarith only [e, hA']
                push Not at h3
                have hAnl : 2 * B < A := h3 hC3
                have hA2 : 2 * B + 1 ≤ A := by lia
                have hB' : 0 < B := hh.1
                nlinarith only [f3, hC3, hA2, hB']
              have c3f : ¬ (0 < C ∧ lowestScore A B C = 2 * B * C) := by
                intro hh
                have e : A * C = 2 * B * C := by rw [← hL]; exact hh.2
                have hA2 : A = 2 * B := by rwa [Nat.mul_right_cancel_iff hh.1] at e
                have hC' : 0 < C := hh.1
                have hCnl : ¬ C < 3 * B := fun hh' => h5 ⟨hA2, hh'⟩
                have h1' : C ≤ 3 * B := by nlinarith only [f2, hA2, hh.1, hA']
                have hC3 : C = 3 * B := by lia
                push Not at h3
                exact h3 hC3 |>.ne hA2.symm
              have wA : fewestWays (A - 1) B C = 1 := by
                unfold fewestWays
                split_ifs with g1 g2 g3 g4 g5 <;> try rfl
                all_goals rcases Nat.eq_zero_or_pos C with rfl | hC0'; lia
                · have hA21 : A = 2 * B + 1 := by lia
                  nlinarith only [f3, hA21, hC0']
                · have hC3 : C = 3 * B := g3.1
                  push Not at h3
                  have hAnl : 2 * B < A := h3 hC3
                  have hA2 : 2 * B + 1 ≤ A := by lia
                  nlinarith only [f3, hC3, hA2, hC0']
                · have hA22 : 2 * B + 2 ≤ A := by lia
                  nlinarith only [f3, hA22, hC0']
                · have hA21 : A = 2 * B + 1 := by lia
                  nlinarith only [f3, hA21, hC0']
              rw [eLHS, ite_eq_left ⟨hA', hL⟩, ite_eq_right c2f, ite_eq_right c3f, wA]
          · -- L = 3 * A * B
            have f1 : 3 * A * B ≤ A * C := by rw [← hL]; exact lowestScore_le_ac A B C
            have f3 : 3 * A * B ≤ 2 * B * C := by rw [← hL]; exact lowestScore_le_bc A B C
            rcases Nat.eq_zero_or_pos B with rfl | hB'
            · have hL0 : lowestScore A 0 C = 0 := lowestScore_a_zero_c _ _
              rcases Nat.eq_zero_or_pos C with rfl | hC'
              · have hA' : 0 < A := by lia
                have wA : fewestWays (A - 1) 0 0 = 1 := fewestWays_a_zero_c _ _
                rw [eLHS, ite_eq_left ⟨hA', by rw [hL0]; ring⟩,
                  ite_eq_right (fun hh => absurd hh.1 (lt_irrefl 0)),
                  ite_eq_right (fun hh => absurd hh.1 (lt_irrefl 0)), wA]
              · have c1f : ¬ (0 < A ∧ lowestScore A 0 C = A * C) := by
                  intro hh
                  rw [hL0] at hh
                  nlinarith only [hh.2, hh.1, hC']
                have wC : fewestWays A 0 (C - 1) = 1 := fewestWays_a_zero_c _ _
                rw [eLHS, ite_eq_right c1f, ite_eq_right (fun hh => absurd hh.1 (lt_irrefl 0)),
                  ite_eq_left ⟨hC', by rw [hL0]; ring⟩, wC]
            · have c1f : ¬ (0 < A ∧ lowestScore A B C = A * C) := by
                intro hh
                have e : 3 * A * B = A * C := by rw [← hL]; exact hh.2
                have hC3 : C = 3 * B := by
                  apply_fun (· * A) using mul_left_injective₀ (by lia)
                  ring_nf at e ⊢
                  exact e.symm
                push Not at h3
                have hA2 : 2 * B < A := h3 hC3
                clear h3 h4 h5 eLHS hL f1
                nlinarith only [f3, hC3, hA2, hB']
              have c3f : ¬ (0 < C ∧ lowestScore A B C = 2 * B * C) := by
                intro hh
                have e : 3 * A * B = 2 * B * C := by rw [← hL]; exact hh.2
                have hAC2 : 3 * A = 2 * C := by
                  apply_fun (· * B) using mul_left_injective₀ (by lia)
                  ring_nf at e ⊢
                  exact e
                have hAnl : ¬ 2 * B < A := fun hh' => h4 ⟨hAC2, hh'⟩
                have hC' : 0 < C := hh.1
                rcases Nat.eq_zero_or_pos A with rfl | hA0'
                · lia
                · have h31 : 3 * B ≤ C := by nlinarith only [f1, hA0']
                  have hC3 : C = 3 * B := by lia
                  have hA2 : A = 2 * B := by lia
                  exact h3 ⟨hC3, hA2.le⟩
              have wB : fewestWays A (B - 1) C = 1 := by
                unfold fewestWays
                split_ifs with g1 g2 g3 g4 g5 <;> try rfl
                all_goals rcases Nat.eq_zero_or_pos A with rfl | hA0'; lia
                · have hAe : A + 2 = 2 * B := by lia
                  have hCe : C + 3 = 3 * B := by lia
                  nlinarith only [f1, hAe, hCe, hA0']
                · have hCe : C + 3 = 3 * B := by lia
                  nlinarith only [f1, hCe, hA0']
                · have h31 : 3 * B ≤ C := by nlinarith only [f1, hA0']
                  lia
                · have h31 : 3 * B ≤ C := by nlinarith only [f1, hA0']
                  lia
              rw [eLHS, ite_eq_right c1f, ite_eq_left ⟨hB', hL⟩, ite_eq_right c3f, wB]
          · -- L = 2 * B * C
            have f1 : 2 * B * C ≤ A * C := by rw [← hL]; exact lowestScore_le_ac A B C
            have f2 : 2 * B * C ≤ 3 * A * B := by rw [← hL]; exact lowestScore_le_ab A B C
            rcases Nat.eq_zero_or_pos C with rfl | hC'
            · have hL0 : lowestScore A B 0 = 0 := lowestScore_a_b_zero _ _
              rcases Nat.eq_zero_or_pos A with rfl | hA'
              · have hB' : 0 < B := by lia
                rw [eLHS, ite_eq_right (fun hh => absurd hh.1 (lt_irrefl 0)),
                  ite_eq_left ⟨hB', by rw [hL0]; ring⟩,
                  ite_eq_right (fun hh => absurd hh.1 (lt_irrefl 0)),
                  fewestWays_zero_b_c]
              · have c2f : ¬ (0 < B ∧ lowestScore A B 0 = 3 * A * B) := by
                  intro hh
                  rw [hL0] at hh
                  nlinarith only [hh.2, hh.1, hA']
                have wA : fewestWays (A - 1) B 0 = 1 := by lia
                rw [eLHS, ite_eq_left ⟨hA', by rw [hL0]; ring⟩, ite_eq_right c2f,
                  ite_eq_right (fun hh => absurd hh.1 (lt_irrefl 0)), wA]
            · have c1f : ¬ (0 < A ∧ lowestScore A B C = A * C) := by
                intro hh
                have e : 2 * B * C = A * C := by rw [← hL]; exact hh.2
                have hA' : 0 < A := hh.1
                have hA2 : A = 2 * B := by
                  apply_fun (· * C) using mul_left_injective₀ (by lia)
                  exact e.symm
                have hCnl : ¬ C < 3 * B := fun hh' => h5 ⟨hA2, hh'⟩
                have hB' : 0 < B := by lia
                have h1' : C ≤ 3 * B := by nlinarith [f2, hA2, hB']
                have hC3 : C = 3 * B := by lia
                exact h3 ⟨hC3, hA2.le⟩
              have c2f : ¬ (0 < B ∧ lowestScore A B C = 3 * A * B) := by
                intro hh
                have e : 2 * B * C = 3 * A * B := by rw [← hL]; exact hh.2
                have hB' : 0 < B := hh.1
                have hAC2 : 2 * C = 3 * A := by
                  apply_fun (· * B) using mul_left_injective₀ (by lia)
                  ring_nf at e ⊢
                  exact e
                push Not at h4
                have hAnl : A ≤ 2 * B := h4 (by lia)
                have h2B : 2 * B ≤ A := by nlinarith only [f1, hC']
                have hA2 : A = 2 * B := by lia
                have hC3 : C = 3 * B := by lia
                exact h3 ⟨hC3, hAnl⟩
              have wC : fewestWays A B (C - 1) = 1 := by
                unfold fewestWays
                split_ifs with g1 g2 g3 g4 g5 <;> try rfl
                · have hCe : C = 3 * B + 1 := by lia
                  have hAe : A = 2 * B := g2.2
                  rcases Nat.eq_zero_or_pos B with rfl | hB0'
                  · lia
                  · nlinarith only [f2, hCe, hAe, hB0']
                · have hCe : C = 3 * B + 1 := by lia
                  have h2B : 2 * B ≤ A := by nlinarith only [f1, hC']
                  lia
                · have hAC2 : 2 * C = 3 * A + 2 := by lia
                  have hB0 : B = 0 := by
                    by_contra hB0
                    have hB0' : 0 < B := Nat.pos_of_ne_zero hB0
                    nlinarith only [f2, hAC2, hB0']
                  lia
                · lia
              rw [eLHS, ite_eq_right c1f, ite_eq_right c2f, ite_eq_left ⟨hC', hL⟩, wC]


-- Score computations.

lemma score_ge (l : List Card) :
    lowestScore (l.count .blue) (l.count .red) (l.count .white) ≤ score l := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons c t IH =>
    cases c with
    | blue =>
      simp only [score_cons_blue, List.count_cons_self,
        List.count_cons_of_ne (by decide : Card.blue ≠ Card.red),
        List.count_cons_of_ne (by decide : Card.blue ≠ Card.white)]
      exact (lowestScore_le_add_blue _ _ _).trans (Nat.add_le_add_left IH _)
    | red =>
      simp only [score_cons_red, List.count_cons_self,
        List.count_cons_of_ne (by decide : Card.red ≠ Card.blue),
        List.count_cons_of_ne (by decide : Card.red ≠ Card.white)]
      exact (lowestScore_le_add_red _ _ _).trans (Nat.add_le_add_left IH _)
    | white =>
      simp only [score_cons_white, List.count_cons_self,
        List.count_cons_of_ne (by decide : Card.white ≠ Card.blue),
        List.count_cons_of_ne (by decide : Card.white ≠ Card.red)]
      exact (lowestScore_le_add_white _ _ _).trans (Nat.add_le_add_left IH _)

lemma score_replicate_blue_append (n : ℕ) (l : List Card) :
    score (List.replicate n .blue ++ l) = n * l.count .white + score l := by
  induction n with
  | zero => simp
  | succ k IH =>
    rw [List.replicate_succ, List.cons_append, score_cons_blue, List.count_append, IH]
    simp [List.count_replicate]
    ring

lemma score_replicate_red_append (n : ℕ) (l : List Card) :
    score (List.replicate n .red ++ l) = 3 * n * l.count .blue + score l := by
  induction n with
  | zero => simp
  | succ k IH =>
    rw [List.replicate_succ, List.cons_append, score_cons_red, List.count_append, IH]
    simp [List.count_replicate]
    ring

lemma score_replicate_white_append (n : ℕ) (l : List Card) :
    score (List.replicate n .white ++ l) = 2 * n * l.count .red + score l := by
  induction n with
  | zero => simp
  | succ k IH =>
    rw [List.replicate_succ, List.cons_append, score_cons_white, List.count_append, IH]
    simp [List.count_replicate]
    ring

lemma score_replicate_blue (n : ℕ) : score (List.replicate n .blue) = 0 := by
  have h := score_replicate_blue_append n []
  simp [score_nil] at h
  exact h

lemma score_replicate_red (n : ℕ) : score (List.replicate n .red) = 0 := by
  have h := score_replicate_red_append n []
  simp [score_nil] at h
  exact h

lemma score_replicate_white (n : ℕ) : score (List.replicate n .white) = 0 := by
  have h := score_replicate_white_append n []
  simp [score_nil] at h
  exact h

lemma score_canonicalPlay (A B C : ℕ) : score (canonicalPlay A B C) = A * C := by
  rw [canonicalPlay, score_replicate_blue_append, List.count_append,
    score_replicate_red_append, score_replicate_white]
  simp [List.count_replicate]

lemma score_rwb (A B C : ℕ) :
    score (List.replicate B .red ++ (List.replicate C .white ++ List.replicate A .blue)) =
      3 * A * B := by
  rw [score_replicate_red_append, List.count_append, score_replicate_white_append,
    score_replicate_blue]
  simp [List.count_replicate]
  ring

lemma score_wbr (A B C : ℕ) :
    score (List.replicate C .white ++ (List.replicate A .blue ++ List.replicate B .red)) =
      2 * B * C := by
  rw [score_replicate_white_append, List.count_append, score_replicate_blue_append,
    score_replicate_red]
  simp [List.count_replicate]
  ring

-- Counting.

/-- The set of plays that achieve the lowest score. -/
def optPlays (A B C : ℕ) : Finset (List Card) :=
  (plays A B C).filter (fun l ↦ score l = lowestScore A B C)

lemma eq_cons_of_head?_eq_some {l : List Card} {c : Card} (h : l.head? = some c) :
    ∃ t, l = c :: t := by
  cases l with
  | nil => simp at h
  | cons a t =>
    rw [List.head?_cons] at h
    exact ⟨t, by rw [Option.some.inj h]⟩

lemma card_optPlays_head_blue (A B C : ℕ) :
    ((optPlays A B C).filter (fun l ↦ l.head? = some .blue)).card =
      if 0 < A ∧ lowestScore A B C = A * C then (optPlays (A - 1) B C).card else 0 := by
  by_cases hA : A = 0
  · subst hA
    have hempty : (optPlays 0 B C).filter (fun l ↦ l.head? = some .blue) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro l hl
      rw [Finset.mem_filter, optPlays, Finset.mem_filter] at hl
      obtain ⟨t, rfl⟩ := eq_cons_of_head?_eq_some hl.2
      have hc := (mem_plays.mp hl.1.1).1
      simp at hc
    rw [hempty, Finset.card_empty, ite_eq_right]
    rintro ⟨h, -⟩
    exact (Nat.lt_irrefl 0) h
  · obtain ⟨A', rfl⟩ : ∃ k, A = k + 1 := ⟨A - 1, by omega⟩
    by_cases htight : C + lowestScore A' B C = lowestScore (A' + 1) B C
    · have himg : (optPlays (A' + 1) B C).filter (fun l ↦ l.head? = some .blue) =
          (optPlays A' B C).image (fun t ↦ .blue :: t) := by
        ext l
        constructor
        · intro hl
          rw [Finset.mem_filter, optPlays, Finset.mem_filter] at hl
          obtain ⟨t, rfl⟩ := eq_cons_of_head?_eq_some hl.2
          obtain ⟨hb, hr, hw⟩ := mem_plays.mp hl.1.1
          rw [List.count_cons_self] at hb
          rw [List.count_cons_of_ne (by decide : Card.blue ≠ Card.red)] at hr
          rw [List.count_cons_of_ne (by decide : Card.blue ≠ Card.white)] at hw
          have hsc := hl.1.2
          rw [score_cons_blue, hw] at hsc
          have hst : score t = lowestScore A' B C := by omega
          rw [Finset.mem_image]
          refine ⟨t, ?_, rfl⟩
          rw [optPlays, Finset.mem_filter]
          exact ⟨mem_plays.mpr ⟨by omega, hr, hw⟩, hst⟩
        · intro hl
          rw [Finset.mem_image] at hl
          obtain ⟨t, ht, rfl⟩ := hl
          rw [optPlays, Finset.mem_filter] at ht
          obtain ⟨hb, hr, hw⟩ := mem_plays.mp ht.1
          rw [Finset.mem_filter, optPlays, Finset.mem_filter]
          refine ⟨⟨mem_plays.mpr ⟨?_, ?_, ?_⟩, ?_⟩, rfl⟩
          · rw [List.count_cons_self, hb]
          · rw [List.count_cons_of_ne (by decide : Card.blue ≠ Card.red), hr]
          · rw [List.count_cons_of_ne (by decide : Card.blue ≠ Card.white), hw]
          · rw [score_cons_blue, hw, ht.2, htight]
      rw [himg, Finset.card_image_of_injective _ (fun x y hxy ↦ (List.cons.inj hxy).2),
        ite_eq_left ⟨Nat.succ_pos A', (tight_blue A' B C).mp htight⟩, Nat.add_sub_cancel]
    · have hempty : (optPlays (A' + 1) B C).filter (fun l ↦ l.head? = some .blue) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro l hl
        rw [Finset.mem_filter, optPlays, Finset.mem_filter] at hl
        obtain ⟨t, rfl⟩ := eq_cons_of_head?_eq_some hl.2
        obtain ⟨hb, hr, hw⟩ := mem_plays.mp hl.1.1
        rw [List.count_cons_self] at hb
        rw [List.count_cons_of_ne (by decide : Card.blue ≠ Card.red)] at hr
        rw [List.count_cons_of_ne (by decide : Card.blue ≠ Card.white)] at hw
        have hbc : t.count .blue = A' := by omega
        have hge := score_ge t
        rw [hbc, hr, hw] at hge
        have hlt : lowestScore (A' + 1) B C < C + lowestScore A' B C :=
          lt_of_le_of_ne (lowestScore_le_add_blue A' B C) (fun h ↦ htight h.symm)
        have e := hl.1.2
        rw [score_cons_blue, hw] at e
        omega
      rw [hempty, Finset.card_empty, ite_eq_right]
      rintro ⟨-, h2⟩
      exact htight ((tight_blue A' B C).mpr h2)

lemma card_optPlays_head_red (A B C : ℕ) :
    ((optPlays A B C).filter (fun l ↦ l.head? = some .red)).card =
      if 0 < B ∧ lowestScore A B C = 3 * A * B then (optPlays A (B - 1) C).card else 0 := by
  by_cases hB : B = 0
  · subst hB
    have hempty : (optPlays A 0 C).filter (fun l ↦ l.head? = some .red) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro l hl
      rw [Finset.mem_filter, optPlays, Finset.mem_filter] at hl
      obtain ⟨t, rfl⟩ := eq_cons_of_head?_eq_some hl.2
      have hc := (mem_plays.mp hl.1.1).2.1
      simp at hc
    rw [hempty, Finset.card_empty, ite_eq_right]
    rintro ⟨h, -⟩
    exact (Nat.lt_irrefl 0) h
  · obtain ⟨B', rfl⟩ : ∃ k, B = k + 1 := ⟨B - 1, by omega⟩
    by_cases htight : 3 * A + lowestScore A B' C = lowestScore A (B' + 1) C
    · have himg : (optPlays A (B' + 1) C).filter (fun l ↦ l.head? = some .red) =
          (optPlays A B' C).image (fun t ↦ .red :: t) := by
        ext l
        constructor
        · intro hl
          rw [Finset.mem_filter, optPlays, Finset.mem_filter] at hl
          obtain ⟨t, rfl⟩ := eq_cons_of_head?_eq_some hl.2
          obtain ⟨hb, hr, hw⟩ := mem_plays.mp hl.1.1
          rw [List.count_cons_of_ne (by decide : Card.red ≠ Card.blue)] at hb
          rw [List.count_cons_self] at hr
          rw [List.count_cons_of_ne (by decide : Card.red ≠ Card.white)] at hw
          have hsc := hl.1.2
          rw [score_cons_red, hb] at hsc
          have hst : score t = lowestScore A B' C := by omega
          rw [Finset.mem_image]
          refine ⟨t, ?_, rfl⟩
          rw [optPlays, Finset.mem_filter]
          exact ⟨mem_plays.mpr ⟨hb, by omega, hw⟩, hst⟩
        · intro hl
          rw [Finset.mem_image] at hl
          obtain ⟨t, ht, rfl⟩ := hl
          rw [optPlays, Finset.mem_filter] at ht
          obtain ⟨hb, hr, hw⟩ := mem_plays.mp ht.1
          rw [Finset.mem_filter, optPlays, Finset.mem_filter]
          refine ⟨⟨mem_plays.mpr ⟨?_, ?_, ?_⟩, ?_⟩, rfl⟩
          · rw [List.count_cons_of_ne (by decide : Card.red ≠ Card.blue), hb]
          · rw [List.count_cons_self, hr]
          · rw [List.count_cons_of_ne (by decide : Card.red ≠ Card.white), hw]
          · rw [score_cons_red, hb, ht.2, htight]
      rw [himg, Finset.card_image_of_injective _ (fun x y hxy ↦ (List.cons.inj hxy).2),
        ite_eq_left ⟨Nat.succ_pos B', (tight_red A B' C).mp htight⟩, Nat.add_sub_cancel]
    · have hempty : (optPlays A (B' + 1) C).filter (fun l ↦ l.head? = some .red) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro l hl
        rw [Finset.mem_filter, optPlays, Finset.mem_filter] at hl
        obtain ⟨t, rfl⟩ := eq_cons_of_head?_eq_some hl.2
        obtain ⟨hb, hr, hw⟩ := mem_plays.mp hl.1.1
        rw [List.count_cons_of_ne (by decide : Card.red ≠ Card.blue)] at hb
        rw [List.count_cons_self] at hr
        rw [List.count_cons_of_ne (by decide : Card.red ≠ Card.white)] at hw
        have hrc : t.count .red = B' := by omega
        have hge := score_ge t
        rw [hb, hrc, hw] at hge
        have hlt : lowestScore A (B' + 1) C < 3 * A + lowestScore A B' C :=
          lt_of_le_of_ne (lowestScore_le_add_red A B' C) (fun h ↦ htight h.symm)
        have e := hl.1.2
        rw [score_cons_red, hb] at e
        omega
      rw [hempty, Finset.card_empty, ite_eq_right]
      rintro ⟨-, h2⟩
      exact htight ((tight_red A B' C).mpr h2)

lemma card_optPlays_head_white (A B C : ℕ) :
    ((optPlays A B C).filter (fun l ↦ l.head? = some .white)).card =
      if 0 < C ∧ lowestScore A B C = 2 * B * C then (optPlays A B (C - 1)).card else 0 := by
  by_cases hC : C = 0
  · subst hC
    have hempty : (optPlays A B 0).filter (fun l ↦ l.head? = some .white) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro l hl
      rw [Finset.mem_filter, optPlays, Finset.mem_filter] at hl
      obtain ⟨t, rfl⟩ := eq_cons_of_head?_eq_some hl.2
      have hc := (mem_plays.mp hl.1.1).2.2
      simp at hc
    rw [hempty, Finset.card_empty, ite_eq_right]
    rintro ⟨h, -⟩
    exact (Nat.lt_irrefl 0) h
  · obtain ⟨C', rfl⟩ : ∃ k, C = k + 1 := ⟨C - 1, by omega⟩
    by_cases htight : 2 * B + lowestScore A B C' = lowestScore A B (C' + 1)
    · have himg : (optPlays A B (C' + 1)).filter (fun l ↦ l.head? = some .white) =
          (optPlays A B C').image (fun t ↦ .white :: t) := by
        ext l
        constructor
        · intro hl
          rw [Finset.mem_filter, optPlays, Finset.mem_filter] at hl
          obtain ⟨t, rfl⟩ := eq_cons_of_head?_eq_some hl.2
          obtain ⟨hb, hr, hw⟩ := mem_plays.mp hl.1.1
          rw [List.count_cons_of_ne (by decide : Card.white ≠ Card.blue)] at hb
          rw [List.count_cons_of_ne (by decide : Card.white ≠ Card.red)] at hr
          rw [List.count_cons_self] at hw
          have hsc := hl.1.2
          rw [score_cons_white, hr] at hsc
          have hst : score t = lowestScore A B C' := by omega
          rw [Finset.mem_image]
          refine ⟨t, ?_, rfl⟩
          rw [optPlays, Finset.mem_filter]
          exact ⟨mem_plays.mpr ⟨hb, hr, by omega⟩, hst⟩
        · intro hl
          rw [Finset.mem_image] at hl
          obtain ⟨t, ht, rfl⟩ := hl
          rw [optPlays, Finset.mem_filter] at ht
          obtain ⟨hb, hr, hw⟩ := mem_plays.mp ht.1
          rw [Finset.mem_filter, optPlays, Finset.mem_filter]
          refine ⟨⟨mem_plays.mpr ⟨?_, ?_, ?_⟩, ?_⟩, rfl⟩
          · rw [List.count_cons_of_ne (by decide : Card.white ≠ Card.blue), hb]
          · rw [List.count_cons_of_ne (by decide : Card.white ≠ Card.red), hr]
          · rw [List.count_cons_self, hw]
          · rw [score_cons_white, hr, ht.2, htight]
      rw [himg, Finset.card_image_of_injective _ (fun x y hxy ↦ (List.cons.inj hxy).2),
        ite_eq_left ⟨Nat.succ_pos C', (tight_white A B C').mp htight⟩, Nat.add_sub_cancel]
    · have hempty : (optPlays A B (C' + 1)).filter (fun l ↦ l.head? = some .white) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro l hl
        rw [Finset.mem_filter, optPlays, Finset.mem_filter] at hl
        obtain ⟨t, rfl⟩ := eq_cons_of_head?_eq_some hl.2
        obtain ⟨hb, hr, hw⟩ := mem_plays.mp hl.1.1
        rw [List.count_cons_of_ne (by decide : Card.white ≠ Card.blue)] at hb
        rw [List.count_cons_of_ne (by decide : Card.white ≠ Card.red)] at hr
        rw [List.count_cons_self] at hw
        have hwc : t.count .white = C' := by omega
        have hge := score_ge t
        rw [hb, hr, hwc] at hge
        have hlt : lowestScore A B (C' + 1) < 2 * B + lowestScore A B C' :=
          lt_of_le_of_ne (lowestScore_le_add_white A B C') (fun h ↦ htight h.symm)
        have e := hl.1.2
        rw [score_cons_white, hr] at e
        omega
      rw [hempty, Finset.card_empty, ite_eq_right]
      rintro ⟨-, h2⟩
      exact htight ((tight_white A B C').mpr h2)

lemma optPlays_card_rec (A B C : ℕ) (h : 0 < A + B + C) :
    (optPlays A B C).card =
      (if 0 < A ∧ lowestScore A B C = A * C then (optPlays (A - 1) B C).card else 0) +
      (if 0 < B ∧ lowestScore A B C = 3 * A * B then (optPlays A (B - 1) C).card else 0) +
      (if 0 < C ∧ lowestScore A B C = 2 * B * C then (optPlays A B (C - 1)).card else 0) := by
  have hne : ∀ l ∈ optPlays A B C, l ≠ [] := by
    intro l hl hl0
    rw [optPlays, Finset.mem_filter] at hl
    obtain ⟨hb, hr, hw⟩ := mem_plays.mp hl.1
    rw [hl0] at hb hr hw
    simp at hb hr hw
    omega
  have hpart : optPlays A B C =
      (optPlays A B C).filter (fun l ↦ l.head? = some .blue) ∪
      ((optPlays A B C).filter (fun l ↦ l.head? = some .red) ∪
       (optPlays A B C).filter (fun l ↦ l.head? = some .white)) := by
    ext l
    constructor
    · intro hl
      have hnel := hne l hl
      cases l with
      | nil => exact absurd rfl hnel
      | cons c t =>
        rcases c with _ | _ | _
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hl, rfl⟩))
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl
            (Finset.mem_filter.mpr ⟨hl, rfl⟩))))
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr
            (Finset.mem_filter.mpr ⟨hl, rfl⟩))))
    · intro hl
      rcases Finset.mem_union.mp hl with h1 | h1
      · exact (Finset.mem_filter.mp h1).1
      · rcases Finset.mem_union.mp h1 with h2 | h2
        · exact (Finset.mem_filter.mp h2).1
        · exact (Finset.mem_filter.mp h2).1
  have hdRW : Disjoint ((optPlays A B C).filter (fun l ↦ l.head? = some .red))
      ((optPlays A B C).filter (fun l ↦ l.head? = some .white)) := by
    rw [Finset.disjoint_left]
    intro l hl hl2
    rw [Finset.mem_filter] at hl hl2
    obtain ⟨-, hl2'⟩ := hl2
    rw [hl.2] at hl2'
    exact absurd (Option.some.inj hl2') (by decide)
  have hdB : Disjoint ((optPlays A B C).filter (fun l ↦ l.head? = some .blue))
      ((optPlays A B C).filter (fun l ↦ l.head? = some .red) ∪
       (optPlays A B C).filter (fun l ↦ l.head? = some .white)) := by
    rw [Finset.disjoint_left]
    intro l hl hl2
    rw [Finset.mem_filter] at hl
    obtain ⟨-, hl'⟩ := hl
    rcases Finset.mem_union.mp hl2 with h1 | h1 <;>
      rw [Finset.mem_filter] at h1 <;>
      obtain ⟨-, h1'⟩ := h1 <;>
      rw [hl'] at h1' <;>
      exact absurd (Option.some.inj h1') (by decide)
  rw [hpart, Finset.card_union_of_disjoint hdB, Finset.card_union_of_disjoint hdRW,
    card_optPlays_head_blue, card_optPlays_head_red, card_optPlays_head_white,
    Nat.add_assoc]

lemma optPlays_zero : (optPlays 0 0 0).card = 1 := by
  have h0 : optPlays 0 0 0 = {[]} := by
    ext l
    rw [optPlays, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro hl
      obtain ⟨hb, hr, hw⟩ := mem_plays.mp hl.1
      cases l with
      | nil => rfl
      | cons c t =>
        rcases c with _ | _ | _
        · rw [List.count_cons_self] at hb
          exact absurd hb (Nat.succ_ne_zero _)
        · rw [List.count_cons_self] at hr
          exact absurd hr (Nat.succ_ne_zero _)
        · rw [List.count_cons_self] at hw
          exact absurd hw (Nat.succ_ne_zero _)
    · intro hl
      rw [hl]
      refine ⟨mem_plays.mpr ⟨rfl, rfl, rfl⟩, ?_⟩
      rfl
  rw [h0, Finset.card_singleton]

lemma optPlays_card (A B C : ℕ) : (optPlays A B C).card = fewestWays A B C := by
  suffices H : ∀ n : ℕ, ∀ a b c : ℕ, a + b + c < n →
      (optPlays a b c).card = fewestWays a b c by
    exact H (A + B + C + 1) A B C (Nat.lt_succ_self _)
  intro n
  induction' n with n IH
  · intro a b c h
    omega
  · intro a b c hlt
    by_cases h0 : a + b + c = 0
    · obtain ⟨rfl, rfl, rfl⟩ : a = 0 ∧ b = 0 ∧ c = 0 := by omega
      rw [optPlays_zero]
      simp [fewestWays]
    · have hpos : 0 < a + b + c := Nat.pos_of_ne_zero h0
      rw [optPlays_card_rec a b c hpos, fewestWays_rec a b c hpos]
      have e1 : (if 0 < a ∧ lowestScore a b c = a * c then (optPlays (a - 1) b c).card
          else 0) =
          (if 0 < a ∧ lowestScore a b c = a * c then fewestWays (a - 1) b c else 0) := by
        by_cases h : 0 < a ∧ lowestScore a b c = a * c
        · rw [ite_eq_left h, ite_eq_left h]
          exact IH (a - 1) b c (by omega)
        · rw [ite_eq_right h, ite_eq_right h]
      have e2 : (if 0 < b ∧ lowestScore a b c = 3 * a * b then (optPlays a (b - 1) c).card
          else 0) =
          (if 0 < b ∧ lowestScore a b c = 3 * a * b then fewestWays a (b - 1) c
          else 0) := by
        by_cases h : 0 < b ∧ lowestScore a b c = 3 * a * b
        · rw [ite_eq_left h, ite_eq_left h]
          exact IH a (b - 1) c (by omega)
        · rw [ite_eq_right h, ite_eq_right h]
      have e3 : (if 0 < c ∧ lowestScore a b c = 2 * b * c then (optPlays a b (c - 1)).card
          else 0) =
          (if 0 < c ∧ lowestScore a b c = 2 * b * c then fewestWays a b (c - 1)
          else 0) := by
        by_cases h : 0 < c ∧ lowestScore a b c = 2 * b * c
        · rw [ite_eq_left h, ite_eq_left h]
          exact IH a b (c - 1) (by omega)
        · rw [ite_eq_right h, ite_eq_right h]
      rw [e1, e2, e3]

lemma canonicalPlay_mem_plays (A B C : ℕ) : canonicalPlay A B C ∈ plays A B C :=
  mem_plays.mpr ⟨by simp [canonicalPlay, List.count_replicate],
    by simp [canonicalPlay, List.count_replicate],
    by simp [canonicalPlay, List.count_replicate]⟩

lemma mem_plays_rwb (A B C : ℕ) :
    List.replicate B .red ++ (List.replicate C .white ++ List.replicate A .blue) ∈
      plays A B C :=
  mem_plays.mpr ⟨by simp [List.count_replicate], by simp [List.count_replicate],
    by simp [List.count_replicate]⟩

lemma mem_plays_wbr (A B C : ℕ) :
    List.replicate C .white ++ (List.replicate A .blue ++ List.replicate B .red) ∈
      plays A B C :=
  mem_plays.mpr ⟨by simp [List.count_replicate], by simp [List.count_replicate],
    by simp [List.count_replicate]⟩

lemma isLeast_lowestScore (A B C : ℕ) :
    IsLeast {s : ℕ | ∃ l ∈ plays A B C, score l = s} (lowestScore A B C) := by
  constructor
  · rcases lowestScore_cases A B C with h | h | h
    · exact ⟨canonicalPlay A B C, canonicalPlay_mem_plays A B C,
        by rw [score_canonicalPlay]; exact h.symm⟩
    · exact ⟨List.replicate B .red ++ (List.replicate C .white ++ List.replicate A .blue),
        mem_plays_rwb A B C, by rw [score_rwb]; exact h.symm⟩
    · exact ⟨List.replicate C .white ++ (List.replicate A .blue ++ List.replicate B .red),
        mem_plays_wbr A B C, by rw [score_wbr]; exact h.symm⟩
  · intro s hs
    obtain ⟨l, hl, rfl⟩ := hs
    obtain ⟨hb, hr, hw⟩ := mem_plays.mp hl
    rw [← hb, ← hr, ← hw]
    exact score_ge l

snip end

problem usa2000_p3 (A B C : ℕ) :
    IsLeast {s : ℕ | ∃ l ∈ plays A B C, score l = s} (lowestScore A B C) ∧
    ((plays A B C).filter (fun l ↦ score l = lowestScore A B C)).card =
      fewestWays A B C := by
  refine ⟨isLeast_lowestScore A B C, ?_⟩
  exact optPlays_card A B C

end Usa2000P3
