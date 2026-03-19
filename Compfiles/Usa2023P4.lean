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
   dsimp at *; lia

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
    (hd : ∑ i : Fin N, padicValNat 2 (b i) = 0) :
    ∀ i : Fin N, ¬ Even (b i).val := by
  intro i hei
  have h1 : 0 < padicValNat 2 (b i).val := by
     have h2 : 2 ∣ (b i : ℕ) := even_iff_two_dvd.mp hei
     replace h2 : 2^1 ∣ (b i : ℕ) := h2
     exact (Nat.pow_dvd_iff_le_padicValNat (by omega) (PNat.ne_zero (b i))).mp h2
  rw [Finset.sum_eq_zero_iff] at hd
  have h2 := hd i (Finset.mem_univ i)
  lia

lemma lemma5 {a x : ℕ} (hx : 0 < x)
    (hax : padicValNat 2 x < padicValNat 2 a) :
    padicValNat 2 (x + a) < padicValNat 2 a := by
  by_contra! H
  have h1 : 2 ^ (padicValNat 2 (x + a)) ∣ x + a := pow_padicValNat_dvd
  have h2 : 2 ^ (padicValNat 2 a) ∣ a := pow_padicValNat_dvd
  have h4 : 2 ^ (padicValNat 2 a) ∣ x + a :=
    Nat.pow_dvd_of_le_of_pow_dvd H h1
  have h5 : 2 ^ (padicValNat 2 a) ∣ x := (Nat.dvd_add_iff_left h2).mpr h4
  have h6 := (Nat.pow_dvd_iff_le_padicValNat (by omega) (Nat.ne_zero_of_lt hx)).mp h5
  lia

lemma lemma5' {a x : ℕ} (hx : 0 < x)
    (hax : padicValNat 2 x < padicValNat 2 a) :
    padicValNat 2 (x + a) = padicValNat 2 x := by
  have h1 : 2 ^ (padicValNat 2 (x + a)) ∣ x + a := pow_padicValNat_dvd
  have h2 : 2 ^ (padicValNat 2 a) ∣ a := pow_padicValNat_dvd
  have h4 : 2 ^ (padicValNat 2 x) ∣ x := pow_padicValNat_dvd

  obtain ⟨c, hc⟩ : ∃ c, (padicValNat 2 a) = (padicValNat 2 x) + 1 + c :=
    Nat.exists_eq_add_of_le hax

  obtain ⟨aa, haa⟩ := h2
  obtain ⟨xx, hxx⟩ := h4
  obtain ⟨xa, hxa⟩ := h1
  rw [hc, add_assoc, pow_add] at haa

  have h10 : x + a = 2 ^ padicValNat 2 x * (xx + 2 ^ (1 + c) * aa) := by
    nth_rw 1 [hxx]
    nth_rw 1 [haa]
    rw [mul_assoc, ←mul_add]

  have h12 : 2 ^ padicValNat 2 x ∣ x + a := Dvd.intro _ h10.symm
  replace h12 := (Nat.pow_dvd_iff_le_padicValNat (by omega) (by lia)).mp h12
  suffices H : padicValNat 2 (x + a) ≤ padicValNat 2 x from Nat.le_antisymm H h12
  by_contra! H

  rw [h10] at H

  have h16 : ¬ 2 ∣ xx := by
    rintro ⟨z, rfl⟩
    rw [←mul_assoc, ←pow_succ] at hxx
    have h17 : 2 ^ (padicValNat 2 x + 1) ∣ x := Dvd.intro z hxx.symm
    replace h17 := (Nat.pow_dvd_iff_le_padicValNat (by omega) (Nat.ne_zero_of_lt hx)).mp h17
    lia

  have h15 : ¬ 2 ∣ xx + 2 ^ (1 + c) * aa := by
    intro HH
    have h19 : 2 ∣ 2 ^ (1 + c) * aa := by
      rw [pow_add, pow_one, mul_assoc]
      exact Nat.dvd_mul_right 2 _
    have : 2 ∣ xx := (Nat.dvd_add_iff_left h19).mpr HH
    contradiction

  have h13 : 0 < xx + 2 ^ (1 + c) * aa := by
    have h21 : (xx + 2 ^ (1 + c) * aa) % 2 = 1 := Nat.two_dvd_ne_zero.mp h15
    obtain ⟨k, hk⟩ : Odd (xx + 2 ^ (1 + c) * aa) := Nat.odd_iff.mpr h21
    rw [hk]
    exact Nat.zero_lt_succ (2 * k)

  replace h15 : padicValNat 2 (xx + 2 ^ (1 + c) * aa) = 0 :=
    padicValNat.eq_zero_of_not_dvd h15

  rw [padicValNat_base_pow_mul one_lt_two h13.ne'] at H
  rw [h15, zero_add] at H
  lia

lemma alice_move_preserves_nu
     (a : ℕ+) (N : ℕ) (b0 : Blackboard N)
     (hd : ∀ i : Fin N, padicValNat 2 (b0 i) < padicValNat 2 a)
     (s1 : State N) (hs1 : s1 ∈ valid_moves a N ⟨b0, .Alice⟩) :
     ∀ i : Fin N, padicValNat 2 (s1.board i) < padicValNat 2 a := by
  intro i
  dsimp [valid_moves] at hs1
  obtain ⟨j, rfl⟩ := hs1
  dsimp
  by_cases hji : j = i
  · rw [hji]
    have h2 : Function.update b0 i (b0 i + a) i = b0 i + a :=
      Function.update_self i (b0 i + a) b0
    rw [h2]
    have h3 := hd i
    push_cast
    exact lemma5 (b0 i).pos h3
  · have h2 : Function.update b0 j (b0 j + a) i = b0 i := by
      apply Function.update_of_ne
      symm
      exact hji
    rw [h2]
    exact hd i

lemma alice_move_preserves_nu'
     (a : ℕ+) (N : ℕ) (b0 : Blackboard N)
     (hd : ∀ i : Fin N, padicValNat 2 (b0 i) < padicValNat 2 a)
     (s1 : State N) (hs1 : s1 ∈ valid_moves a N ⟨b0, .Alice⟩) :
     ∀ i, padicValNat 2 (s1.board i) =  padicValNat 2 (b0 i) := by
  intro i
  dsimp [valid_moves] at hs1
  obtain ⟨j, rfl⟩ := hs1
  dsimp
  by_cases hji : j = i
  · rw [hji]
    have h2 : Function.update b0 i (b0 i + a) i = b0 i + a :=
      Function.update_self i (b0 i + a) b0
    rw [h2]
    have h3 := hd i
    push_cast
    exact lemma5' (b0 i).pos h3
  · have h2 : Function.update b0 j (b0 j + a) i = b0 i := by
      apply Function.update_of_ne
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
    : padicValNat 2 (x / 2) + 1 = padicValNat 2 x := by
  have h2 : (2 : ℕ) ∣ x := even_iff_two_dvd.mp hx
  have hv : 1 ≤ padicValNat 2 x := by
    rwa [← Nat.pow_dvd_iff_le_padicValNat (by omega) (by omega), pow_one]
  rw [padicValNat.div h2]
  omega

-- When N ≥ 2, if ν2(x) < ν2(a) for all x ∈ S, the game must terminate
-- in ∑_{x∈S} ν2(x) moves, no matter what either player does.
lemma lemma2' (a : ℕ+) (N : ℕ) (hN : 1 < N) (s0 : State N)
    (hd : ∀ i : Fin N, padicValNat 2 (s0.board i) < padicValNat 2 a) :
    EndInevitableIn a N (∑ i : Fin N, padicValNat 2 (s0.board i)) s0 := by
  generalize hms : ∑ i : Fin N, padicValNat 2 (s0.board i) = ms
  revert s0
  induction' ms with ms' ih
  · intro s0 hd hms
    have h1 := lemma3 N s0.board hms
    obtain ⟨b0, t0⟩ := s0
    match t0 with
    | .Bob =>
      apply EndInevitableIn.BaseCase
      dsimp [valid_moves]
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      rw [Set.mem_setOf_eq] at hx
      obtain ⟨i, hie, _⟩ := hx
      exact h1 i hie
    | .Alice =>
      apply EndInevitableIn.AliceTurn _ ⟨b0, .Alice⟩
      intro s hs
      have h2 : Even (a:ℕ) := by
        have ha : 0 < padicValNat 2 ↑a := by
          have := hd ⟨0, by lia⟩
          lia
        have ha1 : 2 ^ padicValNat 2 (a : ℕ) ∣ (a : ℕ) := pow_padicValNat_dvd
        rw [even_iff_two_dvd]
        exact Nat.dvd_of_pow_dvd ha ha1
      apply EndInevitableIn.BaseCase
      obtain ⟨b1, rfl⟩ := bob_moves_after_alice b0 s hs
      dsimp [valid_moves] at hs ⊢
      rw [Set.eq_empty_iff_forall_notMem]
      intro s1' hs1'
      rw [Set.mem_setOf_eq] at hs1'
      obtain ⟨i, hie, _⟩ := hs1'
      obtain ⟨j, hje⟩ := hs
      simp only [State.mk.injEq, and_true] at hje
      subst hje
      by_cases hij : i = j
      · subst hij
        rw [Function.update_self] at hie
        have h3 := h1 i
        dsimp at h3
        push_cast at hie
        rw [Nat.not_even_iff_odd] at h3
        have h4 := Even.odd_add h2 h3
        rw [←Nat.not_even_iff_odd] at h4
        exact h4 hie
      · rw [Function.update_of_ne hij] at hie
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
      subst his
      apply ih
      · intro k
        simp only at hd
        by_cases hki : k = i
        · subst hki; simp [Function.update_self]
          have hv1 := lemma6 (b0 k).pos hie; have := hd k; omega
        · simp [Function.update_of_ne hki]; exact hd k
      · simp only at hd hms ⊢
        have hv := lemma6 (b0 i).pos hie
        have hae := Finset.add_sum_erase Finset.univ (fun k => padicValNat 2 ↑(b0 k)) (Finset.mem_univ i)
        dsimp at hae
        trans (padicValNat 2 (↑(b0 i) / 2) + ∑ k ∈ Finset.univ.erase i, padicValNat 2 ↑(b0 k))
        · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
          congr 1
          · simp [Function.update_self]
          · apply Finset.sum_congr rfl
            intro k hk; rw [Finset.mem_erase] at hk
            simp [Function.update_of_ne hk.1]
        · omega
  | .Alice =>
    apply EndInevitableIn.AliceTurn _ ⟨b0, .Alice⟩
    intro s hs
    have h1 := alice_move_preserves_nu' a N b0 hd s hs
    dsimp at hms
    have h2 : ∑ i : Fin N, padicValNat 2 ↑(b0 i) = ∑ i : Fin N, padicValNat 2 ↑(s.board i) := by
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
    subst hj
    apply ih
    · intro k
      have hd1 : ∀ k, padicValNat 2 ↑(b1 k) < padicValNat 2 ↑a := by
        intro k; subst hi
        by_cases hki : k = i
        · subst hki; simp only [Function.update_self]; push_cast
          exact lemma5 (b0 k).pos (hd k)
        · simp only [Function.update_of_ne hki]; exact hd k
      by_cases hkj : k = j
      · subst hkj; simp only [Function.update_self]
        show padicValNat 2 (↑(b1 k) / 2) < padicValNat 2 ↑a
        have hv1 := lemma6 (b1 k).pos hje
        have := hd1 k; omega
      · simp only [Function.update_of_ne hkj]; exact hd1 k
    · simp only at hms ⊢
      have hv := lemma6 (b1 j).pos hje
      have hae := Finset.add_sum_erase Finset.univ (fun k => padicValNat 2 ↑(b1 k)) (Finset.mem_univ j)
      dsimp at hae
      trans (padicValNat 2 (↑(b1 j) / 2) + ∑ k ∈ Finset.univ.erase j, padicValNat 2 ↑(b1 k))
      · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
        congr 1
        · simp [Function.update_self]
        · apply Finset.sum_congr rfl
          intro k hk; rw [Finset.mem_erase] at hk
          simp [Function.update_of_ne hk.1]
      · omega


-- When N ≥ 2, if ν2(x) < ν2(a) for all x ∈ S, the game must terminate no
-- matter what either player does.
lemma lemma2 (a : ℕ+) (N : ℕ) (hN : 1 < N) (s0 : State N)
    (hd : ∀ i : Fin N, padicValNat 2 (s0.board i) < padicValNat 2 a) :
    EndInevitable a N s0 := by
  exact end_inevitable_n (lemma2' a N hN s0 hd)

-- Key fact: when ν₂(x) = ν₂(a), ν₂(x+a) ≥ ν₂(a) + 1
lemma lemma7 {x a : ℕ} (hx : 0 < x) (ha : 0 < a)
    (heq : padicValNat 2 x = padicValNat 2 a) :
    padicValNat 2 a + 1 ≤ padicValNat 2 (x + a) := by
  set k := padicValNat 2 a with hk_def
  suffices h : 2 ^ (k + 1) ∣ (x + a) from
    (Nat.pow_dvd_iff_le_padicValNat (by omega) (by omega)).mp h
  have hkx : 2 ^ k ∣ x := by rw [← heq]; exact pow_padicValNat_dvd
  have hka : 2 ^ k ∣ a := pow_padicValNat_dvd
  obtain ⟨x', hx'⟩ := hkx
  obtain ⟨a', ha'⟩ := hka
  have hx'_odd : ¬ 2 ∣ x' := by
    intro ⟨z, hz⟩
    have h1 : 2 ^ (k + 1) ∣ x := by
      rw [hx', hz, pow_succ]; exact mul_dvd_mul_left _ (dvd_mul_right (2 : ℕ) z)
    have h2 := (Nat.pow_dvd_iff_le_padicValNat (by omega) (by omega)).mp h1
    omega
  have ha'_odd : ¬ 2 ∣ a' := by
    intro ⟨z, hz⟩
    have h1 : 2 ^ (k + 1) ∣ a := by
      rw [ha', hz, pow_succ]; exact mul_dvd_mul_left _ (dvd_mul_right (2 : ℕ) z)
    have h2 := (Nat.pow_dvd_iff_le_padicValNat (by omega) (by omega)).mp h1
    omega
  have hse : 2 ∣ (x' + a') := by
    rw [Nat.dvd_iff_mod_eq_zero]
    have h1 := mt (Nat.dvd_iff_mod_eq_zero (m := 2) (n := x')).mpr hx'_odd
    have h2 := mt (Nat.dvd_iff_mod_eq_zero (m := 2) (n := a')).mpr ha'_odd
    omega
  rw [hx', ha', ← mul_add, pow_succ]
  exact mul_dvd_mul_left _ hse

-- When N ≥ 2, if ∃ i with ν₂(b i) ≥ ν₂(a) (+ offset by turn), then ¬BobCanForceEnd.
lemma alice_prevents_end (a : ℕ+) (N : ℕ) (hN : 1 < N)
    (s : State N) (he : BobCanForceEnd a N s)
    (hinv : ∃ i : Fin N,
      padicValNat 2 ↑a + (match s.turn with | .Alice => 0 | .Bob => 1) ≤
      padicValNat 2 ↑(s.board i)) :
    False := by
  induction he with
  | BaseCase b hnm =>
    obtain ⟨i, hi⟩ := hinv
    simp only at hi
    have heven : Even (↑(b i) : ℕ) := by
      rw [even_iff_two_dvd]
      exact Nat.dvd_of_pow_dvd (by omega : 1 ≤ padicValNat 2 ↑(b i)) pow_padicValNat_dvd
    rw [Set.eq_empty_iff_forall_notMem] at hnm
    exact hnm ⟨Function.update b i ⟨↑(b i) / 2, halve_even _ heven⟩, .Alice⟩ ⟨i, heven, rfl⟩
  | BobTurn b m hm he' ih =>
    obtain ⟨i₀, hi₀⟩ := hinv
    simp only at hi₀
    dsimp [valid_moves] at hm
    obtain ⟨j, hje, rfl⟩ := hm
    apply ih; dsimp
    by_cases hji : j = i₀
    · subst hji
      refine ⟨j, ?_⟩
      rw [Function.update_self]
      show padicValNat 2 ↑a ≤ padicValNat 2 (↑(b j) / 2)
      have := lemma6 (b j).pos hje; omega
    · refine ⟨i₀, ?_⟩
      have hboard : (Function.update b j ⟨↑(b j) / 2, halve_even _ hje⟩ : Blackboard N) i₀ = b i₀ := by
        apply Function.update_of_ne; exact Ne.symm hji
      rw [hboard]; omega
  | AliceTurn b hall ih =>
    obtain ⟨i, hi⟩ := hinv
    dsimp at hi
    by_cases heq : padicValNat 2 ↑(b i) = padicValNat 2 ↑a
    · apply ih ⟨Function.update b i (b i + a), .Bob⟩ ⟨i, rfl⟩
      dsimp
      refine ⟨i, ?_⟩; simp only [Function.update_self]
      push_cast; exact lemma7 (b i).pos a.pos heq
    · have hi_gt : padicValNat 2 ↑a + 1 ≤ padicValNat 2 ↑(b i) := by omega
      obtain ⟨j, hji⟩ : ∃ j : Fin N, j ≠ i := by
        exact ⟨if i = ⟨0, by omega⟩ then ⟨1, by omega⟩ else ⟨0, by omega⟩,
               by split_ifs with h <;> (simp_all [Fin.ext_iff]; try omega)⟩
      apply ih ⟨Function.update b j (b j + a), .Bob⟩ ⟨j, rfl⟩
      dsimp
      refine ⟨i, ?_⟩
      have hboard : (Function.update b j (b j + a) : Blackboard N) i = b i := by
        apply Function.update_of_ne; exact hji.symm
      simp_rw [hboard]; exact hi_gt

snip end

problem usa2023_p4 (a : ℕ+) (N : ℕ) (hN : 0 < N) (b0 : Blackboard N)
    (he : BobCanForceEnd a N ⟨b0, .Alice⟩) :
    EndInevitable a N ⟨b0, .Alice⟩ := by
  -- we follow the proof from
  -- https://web.evanchen.cc/exams/USAMO-2023-notes.pdf
  obtain rfl | hN : 1 = N ∨ 1 < N := LE.le.eq_or_lt hN
  · exact lemma1 a ⟨b0, .Alice⟩ he
  suffices h : ∀ i : Fin N, padicValNat 2 ↑(b0 i) < padicValNat 2 ↑a from
    lemma2 a N hN ⟨b0, .Alice⟩ h
  by_contra h_not
  push_neg at h_not
  obtain ⟨i₀, hi₀⟩ := h_not
  exact alice_prevents_end a N hN ⟨b0, .Alice⟩ he ⟨i₀, by dsimp; exact hi₀⟩


end Usa2023P4
