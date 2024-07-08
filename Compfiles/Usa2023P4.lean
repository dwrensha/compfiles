/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 2023, Problem 4

Positive integers a and N are fixed, and N positive integers are written on
a blackboard. Alice and Bob play the following game. On Alice's turn, she must
replace some integer n on the board with n + a, and on Bob's turn he must
replace some even integer n on the board with n/2. Alice goes first and they
alternate turns. If Bob has no valid moves on his turn the game ends.

After analyzing the N integers on the board, Bob realizes that, regardless of
what moves Alices makes, he will be able to force the game to end eventually.
Show that, in fact, no matter what either player does, for these values of a and N
and these particular N integers, the game is guaranteed to end, regardless of
either player's moves.
-/

namespace Usa2023P4

inductive Player where
| Alice : Player
| Bob : Player

abbrev Blackboard (n : ℕ) := Fin n → ℕ+

structure State (n : ℕ) where
  board : Blackboard n
  turn : Player

theorem halve_even (x : ℕ+) (he : Even x.val) : 0 < x.val / 2 := by
   obtain ⟨x, hx⟩ := x
   obtain ⟨t, ht⟩ := he
   dsimp at *; omega

def valid_moves (a : ℕ+) (n : ℕ) : State n → Set (State n)
| ⟨b, .Alice⟩ =>
      {s | ∃ i : Fin n, s = ⟨Function.update b i (b i + a), .Bob⟩}
| ⟨b, .Bob⟩ =>
      {s | ∃ i : Fin n,
           ∃ he : Even (b i).val,
           s = ⟨Function.update b i ⟨b i / 2, halve_even _ he⟩,
                .Alice⟩}

inductive BobCanForceEnd (a : ℕ+) (n : ℕ) : State n → Prop where
| BaseCase (b : Blackboard n) :
    valid_moves a n ⟨b, .Bob⟩ = ∅ → BobCanForceEnd a n ⟨b, .Bob⟩
| BobTurn (b : Blackboard n) (m : State n) :
          (m ∈ valid_moves a n ⟨b, .Bob⟩) → BobCanForceEnd a n m →
          BobCanForceEnd a n ⟨b, .Bob⟩
| AliceTurn (b : Blackboard n) :
            (∀ m ∈ valid_moves a n ⟨b, .Alice⟩, BobCanForceEnd a n m) →
            BobCanForceEnd a n ⟨b, .Alice⟩

inductive EndIsInevitable (a : ℕ+) (n : ℕ) : State n → Prop where
| BaseCase (s : State n) : valid_moves a n s = ∅ → EndIsInevitable a n s
| Step (s : State n)
       (h : ∀ m ∈ valid_moves a n s, EndIsInevitable a n m) :
       EndIsInevitable a n s

snip begin

/-- The N=1 case is degenerate. -/
lemma lemma1 (a : ℕ+) (s : State 1) (he : BobCanForceEnd a 1 s) :
    EndIsInevitable a 1 s := by
  induction he with
  | BaseCase bb no_moves => exact .BaseCase _ no_moves
  | BobTurn bb m moves _ ih =>
    apply EndIsInevitable.Step
    intro m' hm'
    have hmm : m = m' := by
      simp only [valid_moves, Set.mem_setOf_eq] at moves hm'
      obtain ⟨i, hie, hi⟩ := moves
      obtain ⟨j, hje, hj⟩ := hm'
      simp_rw [Fin.fin_one_eq_zero] at hi hj
      rw [hi, hj]
    rw [hmm] at ih
    exact ih
  | AliceTurn bb _ ih =>
    apply EndIsInevitable.Step
    intro m' hm'
    exact ih m' hm'

/-- end is inevitable in M moves -/
inductive EndInevitableIn (a : ℕ+) (n : ℕ) : ℕ → State n → Prop where
| BaseCase (s : State n) : valid_moves a n s = ∅ → EndInevitableIn a n 0 s
| BobTurn (b : Blackboard n) (s : State n) (m : ℕ) :
          (∀ s ∈ valid_moves a n ⟨b, .Bob⟩, EndInevitableIn a n m s) →
          EndInevitableIn a n (m + 1) ⟨b, .Bob⟩
| AliceTurn (b : Blackboard n) (s : State n) (m : ℕ) :
          (∀ s ∈ valid_moves a n ⟨b, .Alice⟩, EndInevitableIn a n m s) →
          EndInevitableIn a n m ⟨b, .Alice⟩

lemma lemma3 (N : ℕ) (b : Blackboard N)
    (hd : ∑ i : Fin N, Nat.maxPowDiv 2 (b i) = 0) :
    ∀ i : Fin N, ¬ Even (b i).val := by
  intro i hei
  have h1 : 0 < Nat.maxPowDiv 2 (b i).val := by
     have h2 : 2 ∣ (b i : ℕ) := even_iff_two_dvd.mp hei
     replace h2 : 2^1 ∣ (b i : ℕ) := h2
     exact Nat.maxPowDiv.le_of_dvd one_lt_two (b i).prop h2
  rw [Finset.sum_eq_zero_iff] at hd
  have h2 := hd i (Finset.mem_univ i)
  omega

lemma lemma5 {a x : ℕ} (hx : 0 < x)
    (hax : Nat.maxPowDiv 2 x < Nat.maxPowDiv 2 a) :
    Nat.maxPowDiv 2 (x + a) < Nat.maxPowDiv 2 a := by
  by_contra! H
  have h1 : 2 ^ (Nat.maxPowDiv 2 (x + a)) ∣ x + a := Nat.maxPowDiv.pow_dvd 2 (x + a)
  have h2 : 2 ^ (Nat.maxPowDiv 2 a) ∣ a := Nat.maxPowDiv.pow_dvd 2 a
  have h4 : 2 ^ (Nat.maxPowDiv 2 a) ∣ x + a :=
    Nat.pow_dvd_of_le_of_pow_dvd H h1
  have h5 : 2 ^ (Nat.maxPowDiv 2 a) ∣ x := (Nat.dvd_add_iff_left h2).mpr h4
  have h6 := Nat.maxPowDiv.le_of_dvd one_lt_two hx h5
  omega

lemma alice_move_preserves_nu
     (a : ℕ+) (N : ℕ) (b0 : Blackboard N)
     (hd : ∀ i : Fin N, Nat.maxPowDiv 2 (b0 i) < Nat.maxPowDiv 2 a)
     (s1 : State N) (hs1 : s1 ∈ valid_moves a N ⟨b0, .Alice⟩) :
     ∀ i : Fin N, Nat.maxPowDiv 2 (s1.board i) < Nat.maxPowDiv 2 a := by
  intro i
  dsimp [valid_moves] at hs1
  obtain ⟨j, rfl⟩ := hs1
  dsimp
  by_cases hji : j = i
  · rw [hji]
    have h2 : Function.update b0 i (b0 i + a) i = b0 i + a :=
      Function.update_same i (b0 i + a) b0
    rw [h2]
    have h3 := hd i
    push_cast
    exact lemma5 (b0 i).pos h3
  · have h2 : Function.update b0 j (b0 j + a) i = b0 i := by
      apply Function.update_noteq
      symm
      exact hji
    rw [h2]
    exact hd i

-- When N ≥ 2, if ν2(x) < ν2(a) for all x ∈ S, the game must terminate
-- in ∑_{x∈S} ν2(x) moves, no matter what either player does.
lemma lemma2' (a : ℕ+) (N : ℕ) (hN : 1 < N) (s0 : State N)
    (hd : ∀ i : Fin N, Nat.maxPowDiv 2 (s0.board i) < Nat.maxPowDiv 2 a) :
    EndInevitableIn a N (∑ i : Fin N, Nat.maxPowDiv 2 (s0.board i)) s0 := by
  generalize hms : ∑ i : Fin N, Nat.maxPowDiv 2 (s0.board i) = ms
  induction' ms
  · have h1 := lemma3 N s0.board hms
    obtain ⟨b0, t0⟩ := s0
    match t0 with
    | .Bob =>
      apply EndInevitableIn.BaseCase
      dsimp [valid_moves]
      rw [Set.eq_empty_iff_forall_not_mem]
      intro x hx
      rw [Set.mem_setOf_eq] at hx
      obtain ⟨i, hie, _⟩ := hx
      exact h1 i hie
    | .Alice =>
      apply EndInevitableIn.AliceTurn _ ⟨b0, .Alice⟩
      intro s hs
      have : Even a := by sorry
      sorry
  sorry

-- When N ≥ 2, if ν2(x) < ν2(a) for all x ∈ S, the game must terminate no
-- matter what either player does.
lemma lemma2 (a : ℕ+) (N : ℕ) (hN : 1 < N) (s0 : State N)
    (hd : ∀ i : Fin N, Nat.maxPowDiv 2 (s0.board i) < Nat.maxPowDiv 2 a) :
    EndIsInevitable a N s0 := by
  /-
   The ν2 of a number is unchanged by Alice’s move and decreases by one on Bob’s
   move. The game ends when every ν2 is zero.
   Hence, in fact the game will always terminate in exactly ∑_{x∈S} ν2(x)
   moves in this case, regardless of what either player does.
  -/
  sorry

-- Claim — When N ≥ 2, if there exists a number x on the board such that ν2(x) ≥
-- ν2(a), then Alice can cause the game to go on forever.

snip end

problem usa2023_p4 (a : ℕ+) (N : ℕ) (hN : 0 < N) (b0 : Blackboard N)
    (he : BobCanForceEnd a N ⟨b0, .Alice⟩) :
    EndIsInevitable a N ⟨b0, .Alice⟩ := by
  -- we follow the proof from
  -- https://web.evanchen.cc/exams/USAMO-2023-notes.pdf
  obtain rfl | hN : N = 1 ∨ 1 < N := LE.le.eq_or_gt hN
  · exact lemma1 a ⟨b0, .Alice⟩ he
  sorry
