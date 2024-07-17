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

inductive EndInevitable (a : ℕ+) (n : ℕ) : State n → Prop where
| BaseCase (s : State n) : valid_moves a n s = ∅ → EndInevitable a n s
| Step (s : State n)
       (h : ∀ m ∈ valid_moves a n s, EndInevitable a n m) :
       EndInevitable a n s

snip begin

/-- The N=1 case is degenerate. -/
lemma lemma1 (a : ℕ+) (s : State 1) (he : BobCanForceEnd a 1 s) :
    EndInevitable a 1 s := by
  induction he with
  | BaseCase bb no_moves => exact .BaseCase _ no_moves
  | BobTurn bb m moves _ ih =>
    apply EndInevitable.Step
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
    apply EndInevitable.Step
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

lemma end_inevitable_n {a : ℕ+} {n : ℕ} {m : ℕ} {s : State n}
    (h : EndInevitableIn a n m s) : EndInevitable a n s := by
  induction h with
  | BaseCase s he => exact .BaseCase s he
  | BobTurn b _ _ _ ih => exact .Step _ ih
  | AliceTurn _ _ _ _ ih => exact .Step _ ih

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

lemma lemma5' {a x : ℕ} (hx : 0 < x)
    (hax : Nat.maxPowDiv 2 x < Nat.maxPowDiv 2 a) :
    Nat.maxPowDiv 2 (x + a) = Nat.maxPowDiv 2 x := by
  have h1 : 2 ^ (Nat.maxPowDiv 2 (x + a)) ∣ x + a := Nat.maxPowDiv.pow_dvd 2 (x + a)
  have h2 : 2 ^ (Nat.maxPowDiv 2 a) ∣ a := Nat.maxPowDiv.pow_dvd 2 a
  have h4 : 2 ^ (Nat.maxPowDiv 2 x) ∣ x := Nat.maxPowDiv.pow_dvd 2 x

  obtain ⟨c, hc⟩ : ∃ c, (Nat.maxPowDiv 2 a) = (Nat.maxPowDiv 2 x) + 1 + c :=
    Nat.exists_eq_add_of_le hax

  obtain ⟨aa, haa⟩ := h2
  obtain ⟨xx, hxx⟩ := h4
  obtain ⟨xa, hxa⟩ := h1
  rw [hc, add_assoc, pow_add] at haa

  have h10 : x + a = 2 ^ Nat.maxPowDiv 2 x * (xx + 2 ^ (1 + c) * aa) := by
    nth_rw 1 [hxx]
    nth_rw 1 [haa]
    rw [mul_assoc, ←mul_add]

  have h12 : 2 ^ Nat.maxPowDiv 2 x ∣ x + a := Dvd.intro _ h10.symm
  replace h12 := Nat.maxPowDiv.le_of_dvd one_lt_two (Nat.add_pos_left hx a) h12
  suffices H : Nat.maxPowDiv 2 (x + a) ≤ Nat.maxPowDiv 2 x from Nat.le_antisymm H h12
  by_contra! H

  rw [h10] at H

  have h16 : ¬ 2 ∣ xx := by
    rintro ⟨z, rfl⟩
    rw [←mul_assoc, ←pow_succ] at hxx
    have h17 : 2 ^ (Nat.maxPowDiv 2 x + 1) ∣ x := Dvd.intro z hxx.symm
    replace h17 := Nat.maxPowDiv.le_of_dvd one_lt_two hx h17
    omega

  have h15' : ¬ 2 ∣ xx + 2 ^ (1 + c) * aa := by
    intro HH
    have h19 : 2 ∣ 2 ^ (1 + c) * aa := by
      rw [pow_add, pow_one, mul_assoc]
      exact Nat.dvd_mul_right 2 _
    have : 2 ∣ xx := (Nat.dvd_add_iff_left h19).mpr HH
    contradiction

  have h15 : Nat.maxPowDiv 2 (xx + 2 ^ (1 + c) * aa) = 0 := by
    by_contra! HH
    replace HH : 0 < Nat.maxPowDiv 2 (xx + 2 ^ (1 + c) * aa) := Nat.zero_lt_of_ne_zero HH
    generalize hee : xx + 2 ^ (1 + c) * aa = ee
    rw [hee] at HH h15'
    have h18 := Nat.maxPowDiv.pow_dvd 2 ee
    generalize hee' : Nat.maxPowDiv 2 ee = ee'
    rw [hee'] at h18 HH
    cases' ee' with ee'
    · omega
    rw [pow_succ] at h18
    have : 2 ∣ ee := Nat.dvd_of_pow_dvd HH h18
    contradiction

  have h13 : 0 < xx + 2 ^ (1 + c) * aa := by
    have h21 : (xx + 2 ^ (1 + c) * aa) % 2 = 1 := Nat.two_dvd_ne_zero.mp h15'
    obtain ⟨k, hk⟩ : Odd (xx + 2 ^ (1 + c) * aa) := Nat.odd_iff.mpr h21
    rw [hk]
    exact Nat.zero_lt_succ (2 * k)

  rw [Nat.maxPowDiv.base_pow_mul one_lt_two h13] at H
  rw [h15, zero_add] at H
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

lemma alice_move_preserves_nu'
     (a : ℕ+) (N : ℕ) (b0 : Blackboard N)
     (hd : ∀ i : Fin N, Nat.maxPowDiv 2 (b0 i) < Nat.maxPowDiv 2 a)
     (s1 : State N) (hs1 : s1 ∈ valid_moves a N ⟨b0, .Alice⟩) :
     ∀ i, Nat.maxPowDiv 2 (s1.board i) =  Nat.maxPowDiv 2 (b0 i) := by
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
    exact lemma5' (b0 i).pos h3
  · have h2 : Function.update b0 j (b0 j + a) i = b0 i := by
      apply Function.update_noteq
      symm
      exact hji
    rw [h2]

lemma bob_moves_after_alice {a : ℕ+} {N : Nat} (b0 : Blackboard N)
    (s1 : State N)
    (hs : s1 ∈ valid_moves a N ⟨b0, .Alice⟩) :
    ∃ b1, s1 = ⟨b1, .Bob⟩ := by
  dsimp [valid_moves] at hs
  obtain ⟨i, rfl⟩ := hs
  simp

lemma lemma6 {x : ℕ} (hp : 0 < x) (hx : Even x)
    : Nat.maxPowDiv x / 2 + 1 = Nat.maxPowDiv x := by
  sorry

-- When N ≥ 2, if ν2(x) < ν2(a) for all x ∈ S, the game must terminate
-- in ∑_{x∈S} ν2(x) moves, no matter what either player does.
lemma lemma2' (a : ℕ+) (N : ℕ) (hN : 1 < N) (s0 : State N)
    (hd : ∀ i : Fin N, Nat.maxPowDiv 2 (s0.board i) < Nat.maxPowDiv 2 a) :
    EndInevitableIn a N (∑ i : Fin N, Nat.maxPowDiv 2 (s0.board i)) s0 := by
  generalize hms : ∑ i : Fin N, Nat.maxPowDiv 2 (s0.board i) = ms
  revert s0
  induction' ms with ms' ih
  · intro s0 hd hms
    have h1 := lemma3 N s0.board hms
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
      have h2 : Even (a:ℕ) := by
        have ha : 0 < Nat.maxPowDiv 2 ↑a := by
          have := hd ⟨0, by omega⟩
          omega
        have ha1 := Nat.maxPowDiv.pow_dvd 2 a
        rw [even_iff_two_dvd]
        exact Nat.dvd_of_pow_dvd ha ha1
      apply EndInevitableIn.BaseCase
      obtain ⟨b1, rfl⟩ := bob_moves_after_alice b0 s hs
      dsimp [valid_moves] at hs ⊢
      rw [Set.eq_empty_iff_forall_not_mem]
      intro s1' hs1'
      rw [Set.mem_setOf_eq] at hs1'
      obtain ⟨i, hie, _⟩ := hs1'
      obtain ⟨j, hje⟩ := hs
      simp only [State.mk.injEq, and_true] at hje
      subst hje
      by_cases hij : i = j
      · subst hij
        rw [Function.update_same] at hie
        have h3 := h1 i
        dsimp at h3
        push_cast at hie
        rw [← Nat.odd_iff_not_even] at h3
        have h4 := Even.odd_add h2 h3
        rw [Nat.odd_iff_not_even] at h4
        exact h4 hie
      · rw [Function.update_noteq hij] at hie
        have h3 := h1 i
        exact h3 hie

  intro s0 hd hms
  obtain ⟨b0, t0⟩ := s0
  match t0 with
  | .Bob =>
      apply EndInevitableIn.BobTurn _ ⟨b0, .Bob⟩
      intro s hs
      dsimp [valid_moves] at hs
      obtain ⟨i, hie, his⟩ := hs
      sorry
  | .Alice =>
    apply EndInevitableIn.AliceTurn _ ⟨b0, .Alice⟩
    intro s hs
    have h1 := alice_move_preserves_nu' a N b0 hd s hs
    dsimp at hms
    have h2 : ∑ i : Fin N, Nat.maxPowDiv 2 ↑(b0 i) = ∑ i : Fin N, Nat.maxPowDiv 2 ↑(s.board i) := by
      congr
      ext i
      exact (h1 i).symm
    rw [h2] at hms; clear h1 h2
    obtain ⟨b1, rfl⟩ := bob_moves_after_alice b0 s hs
    dsimp at hms
    dsimp [valid_moves] at hs
    obtain ⟨i, hi⟩ := hs
    simp only [State.mk.injEq, and_true] at hi
    apply EndInevitableIn.BobTurn _ ⟨b1, .Bob⟩
    intro s2 hs2
    dsimp [valid_moves] at hs2
    obtain ⟨j, hje, hj⟩ := hs2
    specialize ih s2
    sorry


-- When N ≥ 2, if ν2(x) < ν2(a) for all x ∈ S, the game must terminate no
-- matter what either player does.
lemma lemma2 (a : ℕ+) (N : ℕ) (hN : 1 < N) (s0 : State N)
    (hd : ∀ i : Fin N, Nat.maxPowDiv 2 (s0.board i) < Nat.maxPowDiv 2 a) :
    EndInevitable a N s0 := by
  exact end_inevitable_n (lemma2' a N hN s0 hd)

-- Claim — When N ≥ 2, if there exists a number x on the board such that ν2(x) ≥
-- ν2(a), then Alice can cause the game to go on forever.

snip end

problem usa2023_p4 (a : ℕ+) (N : ℕ) (hN : 0 < N) (b0 : Blackboard N)
    (he : BobCanForceEnd a N ⟨b0, .Alice⟩) :
    EndInevitable a N ⟨b0, .Alice⟩ := by
  -- we follow the proof from
  -- https://web.evanchen.cc/exams/USAMO-2023-notes.pdf
  obtain rfl | hN : N = 1 ∨ 1 < N := LE.le.eq_or_gt hN
  · exact lemma1 a ⟨b0, .Alice⟩ he
  sorry


end Usa2023P4
