/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Algebra.IsPrimePow
public import Mathlib.NumberTheory.Divisors
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 1990, Problem 5

Given an initial integer n₀ > 1, two players A and B choose integers n₁, n₂, n₃, ...
alternately according to the following rules:

Knowing n₂ₖ, A chooses any integer n₂ₖ₊₁ such that n₂ₖ ≤ n₂ₖ₊₁ ≤ n₂ₖ².

Knowing n₂ₖ₊₁, B chooses any integer n₂ₖ₊₂ such that n₂ₖ₊₁/n₂ₖ₊₂ = p^r for some prime p
and integer r ≥ 1.

Player A wins the game by choosing the number 1990; player B wins by choosing the number 1.

For which n₀ does
(a) A have a winning strategy?
(b) B have a winning strategy?
(c) neither player have a winning strategy?

## Solution sketch (after kalva)

Answer: A wins iff n₀ ≥ 8; B wins iff n₀ ∈ {2, 3, 4, 5}; for n₀ ∈ {6, 7} neither player
has a winning strategy (optimal play cycles 6 → 30 → 6 → …, a draw).

* A's winning strategy, given `n`: pick 60 for `n ∈ [8, 11]`, 140 for `n ∈ [12, 16]`,
  280 for `n ∈ [17, 22]`, 504 for `n ∈ [23, 44]`, 1990 for `n ∈ [45, 1990]`,
  1991 for `n = 1991 = 11·181`, and `11^(r+1)·181` for
  `n ∈ (11^r·181, 11^(r+1)·181]`, `r ≥ 1`. One checks that after each pair of moves
  either A has won or A receives a number in `[8, n)` in the last case (finite tree
  in the first cases), so A eventually wins.
* If B is given a number `m ≤ 29`, B can move to `{1, 2, 3, 4}`: this wins because
  from `n ∈ {2, 3, 4, 5}` every move of A lands in `[n, n²] ⊆ [2, 29]` (chaining
  through `[2, 11]` and `[2, 19]`). So B wins for `n₀ ∈ {2, 3, 4, 5}`.
* Given 6, A can only avoid losing by picking 30 (everything else in `[6, 36]` either
  is a prime power, or lets B move into `{1, …, 5}`); B's answers to 30 are 6, 10, 15,
  and 10, 15 are winning for A, so B must answer 6: a draw. Given 7, A's only
  non-losing picks are 30 and 42 = 2·3·7, and B must answer 6 again.

## Formalization notes

The game is a reachability game with finite branching, so each player's winning region
is exactly its attractor, which we write as an inductive predicate: `AWins n` (A to move
from `n` wins) and `BWins m` (B to move from `m` wins); `BWinsStart n` says that B wins
from the initial position (A to move from `n`). The three parts are then the
equivalences proved in `imo1990_p5`.
-/

namespace Imo1990P5

/-- A legal move of player B: from the number `m` just chosen by A, B may choose any
`m'` such that `m / m'` is a prime power `p ^ r` with `r ≥ 1` (B wins by choosing 1). -/
@[reducible] def BMove (m m' : ℕ) : Prop := ∃ p r : ℕ, p.Prime ∧ 0 < r ∧ m = m' * p ^ r

/-- `AWins n`: it is A's turn and the current number is `n` (the initial position has
`n = n₀`), and A has a winning strategy. A either wins immediately by choosing 1990
(possible iff `n ≤ 1990 ≤ n²`), or chooses some `m ∈ [n, n²]` which is not a prime power
(so B cannot win immediately) and such that every legal answer of B is again a winning
position for A. -/
inductive AWins : ℕ → Prop
  | win (n : ℕ) (h₁ : n ≤ 1990) (h₂ : 1990 ≤ n ^ 2) : AWins n
  | move (n m : ℕ) (h₁ : n ≤ m) (h₂ : m ≤ n ^ 2) (h₃ : ¬ IsPrimePow m)
      (h₄ : ∀ m', BMove m m' → AWins m') : AWins n

/-- `BWins m`: it is B's turn and the current number is `m`, and B has a winning
strategy. B either wins immediately by choosing 1 (possible iff `m` is a prime power),
or chooses a legal move to some `m' ≠ 1` such that A cannot win immediately
(`1990 ∉ [m', m'²]`) and every answer of A is again a winning position for B. -/
inductive BWins : ℕ → Prop
  | one (m : ℕ) (h : BMove m 1) : BWins m
  | move (m m' : ℕ) (h : BMove m m') (h₁ : m' ≠ 1)
      (h₂ : ∀ m'', m' ≤ m'' → m'' ≤ m' ^ 2 → m'' ≠ 1990)
      (h₃ : ∀ m'', m' ≤ m'' → m'' ≤ m' ^ 2 → BWins m'') : BWins m

/-- `BWinsStart n`: B has a winning strategy from the initial position with `n₀ = n`
(it is A's turn): whatever A chooses as a first move `m ∈ [n, n²]`, it is not 1990
and B wins from `m`. -/
def BWinsStart (n : ℕ) : Prop := ∀ m, n ≤ m → m ≤ n ^ 2 → m ≠ 1990 ∧ BWins m

snip begin

theorem prime_pow_ne_one {p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r) : p ^ r ≠ 1 := by
  have h2 : 2 ≤ p ^ r := by
    calc 2 ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ r := Nat.pow_le_pow_right hp.pos hr
  omega

/-- A number divisible by two distinct primes is not a prime power. -/
theorem not_isPrimePow_of_dvd_of_dvd {m a b : ℕ} (ha : a.Prime) (hb : b.Prime)
    (hab : a ≠ b) (ham : a ∣ m) (hbm : b ∣ m) : ¬ IsPrimePow m := by
  rw [isPrimePow_nat_iff]
  rintro ⟨p, k, hp, hk, hpk⟩
  rw [← hpk] at ham hbm
  have hap : a ∣ p := ha.dvd_of_dvd_pow ham
  have hbp : b ∣ p := hb.dvd_of_dvd_pow hbm
  have h₁ : a = p := (Nat.prime_dvd_prime_iff_eq ha hp).mp hap
  have h₂ : b = p := (Nat.prime_dvd_prime_iff_eq hb hp).mp hbp
  exact hab (h₁.trans h₂.symm)

theorem not_pp6 : ¬ IsPrimePow 6 :=
  not_isPrimePow_of_dvd_of_dvd (a := 2) (b := 3) (by norm_num) (by norm_num) (by decide)
    (by decide) (by decide)
theorem not_pp10 : ¬ IsPrimePow 10 :=
  not_isPrimePow_of_dvd_of_dvd (a := 2) (b := 5) (by norm_num) (by norm_num) (by decide)
    (by decide) (by decide)
theorem not_pp12 : ¬ IsPrimePow 12 :=
  not_isPrimePow_of_dvd_of_dvd (a := 2) (b := 3) (by norm_num) (by norm_num) (by decide)
    (by decide) (by decide)
theorem not_pp14 : ¬ IsPrimePow 14 :=
  not_isPrimePow_of_dvd_of_dvd (a := 2) (b := 7) (by norm_num) (by norm_num) (by decide)
    (by decide) (by decide)
theorem not_pp15 : ¬ IsPrimePow 15 :=
  not_isPrimePow_of_dvd_of_dvd (a := 3) (b := 5) (by norm_num) (by norm_num) (by decide)
    (by decide) (by decide)
theorem not_pp18 : ¬ IsPrimePow 18 :=
  not_isPrimePow_of_dvd_of_dvd (a := 2) (b := 3) (by norm_num) (by norm_num) (by decide)
    (by decide) (by decide)
theorem not_pp20 : ¬ IsPrimePow 20 :=
  not_isPrimePow_of_dvd_of_dvd (a := 2) (b := 5) (by norm_num) (by norm_num) (by decide)
    (by decide) (by decide)
theorem not_pp21 : ¬ IsPrimePow 21 :=
  not_isPrimePow_of_dvd_of_dvd (a := 3) (b := 7) (by norm_num) (by norm_num) (by decide)
    (by decide) (by decide)
theorem not_pp24 : ¬ IsPrimePow 24 :=
  not_isPrimePow_of_dvd_of_dvd (a := 2) (b := 3) (by norm_num) (by norm_num) (by decide)
    (by decide) (by decide)
theorem not_pp28 : ¬ IsPrimePow 28 :=
  not_isPrimePow_of_dvd_of_dvd (a := 2) (b := 7) (by norm_num) (by norm_num) (by decide)
    (by decide) (by decide)
theorem not_pp30 : ¬ IsPrimePow 30 :=
  not_isPrimePow_of_dvd_of_dvd (a := 2) (b := 3) (by norm_num) (by norm_num) (by decide)
    (by decide) (by decide)
theorem not_pp35 : ¬ IsPrimePow 35 :=
  not_isPrimePow_of_dvd_of_dvd (a := 5) (b := 7) (by norm_num) (by norm_num) (by decide)
    (by decide) (by decide)
theorem not_pp36 : ¬ IsPrimePow 36 :=
  not_isPrimePow_of_dvd_of_dvd (a := 2) (b := 3) (by norm_num) (by norm_num) (by decide)
    (by decide) (by decide)
theorem not_pp40 : ¬ IsPrimePow 40 :=
  not_isPrimePow_of_dvd_of_dvd (a := 2) (b := 5) (by norm_num) (by norm_num) (by decide)
    (by decide) (by decide)
theorem not_pp42 : ¬ IsPrimePow 42 :=
  not_isPrimePow_of_dvd_of_dvd (a := 2) (b := 3) (by norm_num) (by norm_num) (by decide)
    (by decide) (by decide)
theorem not_pp56 : ¬ IsPrimePow 56 :=
  not_isPrimePow_of_dvd_of_dvd (a := 2) (b := 7) (by norm_num) (by norm_num) (by decide)
    (by decide) (by decide)
theorem not_pp60 : ¬ IsPrimePow 60 :=
  not_isPrimePow_of_dvd_of_dvd (a := 2) (b := 3) (by norm_num) (by norm_num) (by decide)
    (by decide) (by decide)
theorem not_pp63 : ¬ IsPrimePow 63 :=
  not_isPrimePow_of_dvd_of_dvd (a := 3) (b := 7) (by norm_num) (by norm_num) (by decide)
    (by decide) (by decide)
theorem not_pp70 : ¬ IsPrimePow 70 :=
  not_isPrimePow_of_dvd_of_dvd (a := 2) (b := 5) (by norm_num) (by norm_num) (by decide)
    (by decide) (by decide)
theorem not_pp72 : ¬ IsPrimePow 72 :=
  not_isPrimePow_of_dvd_of_dvd (a := 2) (b := 3) (by norm_num) (by norm_num) (by decide)
    (by decide) (by decide)
theorem not_pp84 : ¬ IsPrimePow 84 :=
  not_isPrimePow_of_dvd_of_dvd (a := 2) (b := 3) (by norm_num) (by norm_num) (by decide)
    (by decide) (by decide)
theorem not_pp126 : ¬ IsPrimePow 126 :=
  not_isPrimePow_of_dvd_of_dvd (a := 2) (b := 3) (by norm_num) (by norm_num) (by decide)
    (by decide) (by decide)
theorem not_pp140 : ¬ IsPrimePow 140 :=
  not_isPrimePow_of_dvd_of_dvd (a := 2) (b := 5) (by norm_num) (by norm_num) (by decide)
    (by decide) (by decide)
theorem not_pp168 : ¬ IsPrimePow 168 :=
  not_isPrimePow_of_dvd_of_dvd (a := 2) (b := 3) (by norm_num) (by norm_num) (by decide)
    (by decide) (by decide)
theorem not_pp252 : ¬ IsPrimePow 252 :=
  not_isPrimePow_of_dvd_of_dvd (a := 2) (b := 3) (by norm_num) (by norm_num) (by decide)
    (by decide) (by decide)
theorem not_pp280 : ¬ IsPrimePow 280 :=
  not_isPrimePow_of_dvd_of_dvd (a := 2) (b := 5) (by norm_num) (by norm_num) (by decide)
    (by decide) (by decide)
theorem not_pp504 : ¬ IsPrimePow 504 :=
  not_isPrimePow_of_dvd_of_dvd (a := 2) (b := 3) (by norm_num) (by norm_num) (by decide)
    (by decide) (by decide)
theorem not_pp1991 : ¬ IsPrimePow 1991 :=
  not_isPrimePow_of_dvd_of_dvd (a := 11) (b := 181) (by norm_num) (by norm_num) (by decide)
    (by decide) (by decide)

theorem divisors30 : Nat.divisors 30 = {1, 2, 3, 5, 6, 10, 15, 30} := by decide
theorem divisors60 : Nat.divisors 60 = {1, 2, 3, 4, 5, 6, 10, 12, 15, 20, 30, 60} := by
  decide
theorem divisors140 : Nat.divisors 140 = {1, 2, 4, 5, 7, 10, 14, 20, 28, 35, 70, 140} := by
  decide
theorem divisors280 :
    Nat.divisors 280 = {1, 2, 4, 5, 7, 8, 10, 14, 20, 28, 35, 40, 56, 70, 140, 280} := by
  decide
theorem divisors504 : Nat.divisors 504 =
    {1, 2, 3, 4, 6, 7, 8, 9, 12, 14, 18, 21, 24, 28, 36, 42, 56, 63, 72, 84, 126, 168,
      252, 504} := by
  decide
set_option maxRecDepth 10000 in
theorem divisors1991 : Nat.divisors 1991 = {1, 11, 181, 1991} := by decide

/-! ### A wins from `n₀ ≥ 8`

A's winning strategy, following kalva: the moves 60, 140, 280, 504, 1990 cover
`[8, 1990]`, 1991 covers `n = 1991`, and `11 ^ (r + 1) * 181` covers `n ≥ 1992` by
strong induction. -/

theorem aw_45_1990 {n : ℕ} (h₁ : 45 ≤ n) (h₂ : n ≤ 1990) : AWins n := by
  apply AWins.win
  · exact h₂
  · nlinarith [h₁]

theorem aw_23_44 {n : ℕ} (h₁ : 23 ≤ n) (h₂ : n ≤ 44) : AWins n := by
  apply AWins.move (m := 504)
  · omega
  · nlinarith [h₁]
  · exact not_pp504
  · intro m' hm'
    obtain ⟨p, r, hp, hr, h⟩ := hm'
    have hd : m' ∈ Nat.divisors 504 := Nat.mem_divisors.mpr ⟨⟨p ^ r, h⟩, by decide⟩
    rw [divisors504] at hd
    fin_cases hd
    · have hpr : p ^ r = 504 := by omega
      exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp504
    · have hpr : p ^ r = 252 := by omega
      exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp252
    · have hpr : p ^ r = 168 := by omega
      exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp168
    · have hpr : p ^ r = 126 := by omega
      exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp126
    · have hpr : p ^ r = 84 := by omega
      exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp84
    · have hpr : p ^ r = 72 := by omega
      exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp72
    · have hpr : p ^ r = 63 := by omega
      exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp63
    · have hpr : p ^ r = 56 := by omega
      exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp56
    · have hpr : p ^ r = 42 := by omega
      exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp42
    · have hpr : p ^ r = 36 := by omega
      exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp36
    · have hpr : p ^ r = 28 := by omega
      exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp28
    · have hpr : p ^ r = 24 := by omega
      exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp24
    · have hpr : p ^ r = 21 := by omega
      exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp21
    · have hpr : p ^ r = 18 := by omega
      exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp18
    · have hpr : p ^ r = 14 := by omega
      exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp14
    · have hpr : p ^ r = 12 := by omega
      exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp12
    · exact aw_45_1990 (by decide) (by decide)
    · exact aw_45_1990 (by decide) (by decide)
    · exact aw_45_1990 (by decide) (by decide)
    · have hpr : p ^ r = 6 := by omega
      exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp6
    · exact aw_45_1990 (by decide) (by decide)
    · exact aw_45_1990 (by decide) (by decide)
    · exact aw_45_1990 (by decide) (by decide)
    · have hpr : p ^ r = 1 := by omega
      exact absurd hpr (prime_pow_ne_one hp hr)

theorem aw_17_22 {n : ℕ} (h₁ : 17 ≤ n) (h₂ : n ≤ 22) : AWins n := by
  apply AWins.move (m := 280)
  · omega
  · nlinarith [h₁]
  · exact not_pp280
  · intro m' hm'
    obtain ⟨p, r, hp, hr, h⟩ := hm'
    have hd : m' ∈ Nat.divisors 280 := Nat.mem_divisors.mpr ⟨⟨p ^ r, h⟩, by decide⟩
    rw [divisors280] at hd
    fin_cases hd
    · have hpr : p ^ r = 280 := by omega
      exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp280
    · have hpr : p ^ r = 140 := by omega
      exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp140
    · have hpr : p ^ r = 70 := by omega
      exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp70
    · have hpr : p ^ r = 56 := by omega
      exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp56
    · have hpr : p ^ r = 40 := by omega
      exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp40
    · have hpr : p ^ r = 35 := by omega
      exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp35
    · have hpr : p ^ r = 28 := by omega
      exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp28
    · have hpr : p ^ r = 20 := by omega
      exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp20
    · have hpr : p ^ r = 14 := by omega
      exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp14
    · have hpr : p ^ r = 10 := by omega
      exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp10
    · exact aw_23_44 (by decide) (by decide)
    · exact aw_23_44 (by decide) (by decide)
    · exact aw_45_1990 (by decide) (by decide)
    · exact aw_45_1990 (by decide) (by decide)
    · exact aw_45_1990 (by decide) (by decide)
    · have hpr : p ^ r = 1 := by omega
      exact absurd hpr (prime_pow_ne_one hp hr)

theorem aw_12_16 {n : ℕ} (h₁ : 12 ≤ n) (h₂ : n ≤ 16) : AWins n := by
  apply AWins.move (m := 140)
  · omega
  · nlinarith [h₁]
  · exact not_pp140
  · intro m' hm'
    obtain ⟨p, r, hp, hr, h⟩ := hm'
    have hd : m' ∈ Nat.divisors 140 := Nat.mem_divisors.mpr ⟨⟨p ^ r, h⟩, by decide⟩
    rw [divisors140] at hd
    fin_cases hd
    · have hpr : p ^ r = 140 := by omega
      exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp140
    · have hpr : p ^ r = 70 := by omega
      exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp70
    · have hpr : p ^ r = 35 := by omega
      exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp35
    · have hpr : p ^ r = 28 := by omega
      exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp28
    · have hpr : p ^ r = 20 := by omega
      exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp20
    · have hpr : p ^ r = 14 := by omega
      exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp14
    · have hpr : p ^ r = 10 := by omega
      exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp10
    · exact aw_17_22 (by decide) (by decide)
    · exact aw_23_44 (by decide) (by decide)
    · exact aw_23_44 (by decide) (by decide)
    · exact aw_45_1990 (by decide) (by decide)
    · have hpr : p ^ r = 1 := by omega
      exact absurd hpr (prime_pow_ne_one hp hr)

theorem aw_8_11 {n : ℕ} (h₁ : 8 ≤ n) (h₂ : n ≤ 11) : AWins n := by
  apply AWins.move (m := 60)
  · omega
  · nlinarith [h₁]
  · exact not_pp60
  · intro m' hm'
    obtain ⟨p, r, hp, hr, h⟩ := hm'
    have hd : m' ∈ Nat.divisors 60 := Nat.mem_divisors.mpr ⟨⟨p ^ r, h⟩, by decide⟩
    rw [divisors60] at hd
    fin_cases hd
    · have hpr : p ^ r = 60 := by omega
      exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp60
    · have hpr : p ^ r = 30 := by omega
      exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp30
    · have hpr : p ^ r = 20 := by omega
      exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp20
    · have hpr : p ^ r = 15 := by omega
      exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp15
    · have hpr : p ^ r = 12 := by omega
      exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp12
    · have hpr : p ^ r = 10 := by omega
      exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp10
    · have hpr : p ^ r = 6 := by omega
      exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp6
    · exact aw_12_16 (by decide) (by decide)
    · exact aw_12_16 (by decide) (by decide)
    · exact aw_17_22 (by decide) (by decide)
    · exact aw_23_44 (by decide) (by decide)
    · have hpr : p ^ r = 1 := by omega
      exact absurd hpr (prime_pow_ne_one hp hr)

theorem aw_1991 : AWins 1991 := by
  apply AWins.move (m := 1991)
  · decide
  · decide
  · exact not_pp1991
  · intro m' hm'
    obtain ⟨p, r, hp, hr, h⟩ := hm'
    have hd : m' ∈ Nat.divisors 1991 := Nat.mem_divisors.mpr ⟨⟨p ^ r, h⟩, by decide⟩
    rw [divisors1991] at hd
    fin_cases hd
    · have hpr : p ^ r = 1991 := by omega
      exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp1991
    · exact aw_8_11 (by decide) (by decide)
    · exact aw_45_1990 (by decide) (by decide)
    · have hpr : p ^ r = 1 := by omega
      exact absurd hpr (prime_pow_ne_one hp hr)

/-- For `n ≥ 1992` there is an exponent `r ≥ 1` with `11 ^ r * 181 < n ≤
11 ^ (r + 1) * 181`, i.e. the intervals `(11^r·181, 11^(r+1)·181]` cover `[1992, ∞)`. -/
theorem exists_interval {n : ℕ} (h : 1992 ≤ n) :
    ∃ r, 1 ≤ r ∧ 11 ^ r * 181 < n ∧ n ≤ 11 ^ (r + 1) * 181 := by
  have hne : ∃ r, n ≤ 11 ^ (r + 1) * 181 := by
    refine ⟨n, le_trans (Nat.lt_pow_self (by decide : (1 : ℕ) < 11)).le ?_⟩
    exact le_trans (Nat.pow_le_pow_right (by decide) (by omega))
      (Nat.le_mul_of_pos_right _ (by decide))
  have hr1 : 1 ≤ Nat.find hne := by
    by_contra hc
    have h0 : Nat.find hne = 0 := by omega
    have hr3 := Nat.find_spec hne
    rw [h0] at hr3
    norm_num at hr3
    omega
  have hr2 : 11 ^ Nat.find hne * 181 < n := by
    by_contra hc
    have hrlt : Nat.find hne - 1 < Nat.find hne := by omega
    have hmin := Nat.find_min hne hrlt
    rw [Nat.sub_add_cancel hr1] at hmin
    exact hmin (by omega)
  exact ⟨Nat.find hne, hr1, hr2, Nat.find_spec hne⟩

theorem aw_big {n : ℕ} (h : 1992 ≤ n) (IH : ∀ m', m' < n → 8 ≤ m' → AWins m') :
    AWins n := by
  obtain ⟨r, hr1, hlt, hle⟩ := exists_interval h
  apply AWins.move (m := 11 ^ (r + 1) * 181)
  · exact hle
  · -- `11 ^ (r + 1) * 181 ≤ n ^ 2`
    have key : 11 ≤ 11 ^ r * 181 := by
      calc (11 : ℕ) = 11 ^ 1 := (pow_one _).symm
        _ ≤ 11 ^ r := Nat.pow_le_pow_right (by decide) hr1
        _ ≤ 11 ^ r * 181 := Nat.le_mul_of_pos_right _ (by decide)
    have h1 : 11 ^ (r + 1) * 181 ≤ (11 ^ r * 181) ^ 2 := by
      calc 11 ^ (r + 1) * 181 = 11 * 11 ^ r * 181 := by rw [pow_succ']
        _ = 11 ^ r * (11 * 181) := by ring
        _ ≤ 11 ^ r * ((11 ^ r * 181) * 181) :=
            Nat.mul_le_mul (le_refl _) (Nat.mul_le_mul key (le_refl 181))
        _ = (11 ^ r * 181) ^ 2 := by rw [pow_two]; ring
    exact le_trans h1 (Nat.pow_le_pow_left (le_of_lt hlt) 2)
  · -- `11 ^ (r + 1) * 181` is not a prime power
    apply not_isPrimePow_of_dvd_of_dvd (a := 11) (b := 181) (by norm_num) (by norm_num)
      (by decide)
    · exact ⟨11 ^ r * 181, by rw [pow_succ']; ring⟩
    · exact ⟨11 ^ (r + 1), by rw [mul_comm (11 ^ (r + 1)) 181]⟩
  · -- every legal answer of B is smaller than `n` and at least `8`
    intro m' hm'
    obtain ⟨p, k, hp, hk, h⟩ := hm'
    have hpm : p ∣ 11 ^ (r + 1) * 181 := by
      have h1 : p ∣ p ^ k := dvd_pow_self p (by omega)
      have h2 : p ^ k ∣ 11 ^ (r + 1) * 181 := ⟨m', h.trans (mul_comm m' (p ^ k))⟩
      exact dvd_trans h1 h2
    rcases (hp.dvd_mul.mp hpm) with hp11 | hp181
    · have hp11' : p = 11 :=
        (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (hp.dvd_of_dvd_pow hp11)
      subst hp11'
      have h181 : 181 ∣ m' := by
        have h181m : (181 : ℕ) ∣ m' * 11 ^ k := by
          rw [← h]
          exact ⟨11 ^ (r + 1), by rw [mul_comm (11 ^ (r + 1)) 181]⟩
        rcases ((by norm_num : Nat.Prime 181).dvd_mul.mp h181m) with h' | h'
        · exact h'
        · have h2 : (181 : ℕ) ∣ 11 := (by norm_num : Nat.Prime 181).dvd_of_dvd_pow h'
          have h3 :=
            (Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 181)
              (by norm_num : Nat.Prime 11)).mp h2
          omega
      obtain ⟨c, rfl⟩ := h181
      have hc : 0 < c := by
        by_contra hc0
        have h0 : c = 0 := by omega
        rw [h0] at h
        simp only [mul_zero, zero_mul] at h
        exact absurd h (ne_of_gt (by positivity : 0 < 11 ^ (r + 1) * 181))
      have hub : 181 * c ≤ 11 ^ r * 181 := by
        have e1 : (11 : ℕ) ≤ 11 ^ k := by
          calc (11 : ℕ) = 11 ^ 1 := (pow_one _).symm
            _ ≤ 11 ^ k := Nat.pow_le_pow_right (by decide) hk
        have h1 : (181 * c) * 11 ≤ (181 * c) * 11 ^ k := Nat.mul_le_mul (le_refl _) e1
        have h2 : (181 * c) * 11 ^ k = 11 ^ (r + 1) * 181 := h.symm
        rw [h2, pow_succ'] at h1
        have h3 : (181 * c) * 11 ≤ (11 ^ r * 181) * 11 := by
          calc (181 * c) * 11 ≤ 11 * 11 ^ r * 181 := h1
            _ = (11 ^ r * 181) * 11 := by ring
        exact Nat.le_of_mul_le_mul_right h3 (by decide)
      apply IH (181 * c) (lt_of_le_of_lt hub hlt)
      calc 8 ≤ 181 := by decide
        _ ≤ 181 * c := Nat.le_mul_of_pos_right _ hc
    · have hp181' : p = 181 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hp181
      subst hp181'
      have h11 : 11 ∣ m' := by
        have h11m : (11 : ℕ) ∣ m' * 181 ^ k := by
          rw [← h]
          exact ⟨11 ^ r * 181, by rw [pow_succ']; ring⟩
        rcases ((by norm_num : Nat.Prime 11).dvd_mul.mp h11m) with h' | h'
        · exact h'
        · have h2 : (11 : ℕ) ∣ 181 := (by norm_num : Nat.Prime 11).dvd_of_dvd_pow h'
          have h3 :=
            (Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 11)
              (by norm_num : Nat.Prime 181)).mp h2
          omega
      obtain ⟨c, rfl⟩ := h11
      have hc : 0 < c := by
        by_contra hc0
        have h0 : c = 0 := by omega
        rw [h0] at h
        simp only [mul_zero, zero_mul] at h
        exact absurd h (ne_of_gt (by positivity : 0 < 11 ^ (r + 1) * 181))
      have hub : 11 * c ≤ 11 ^ (r + 1) := by
        have e1 : (181 : ℕ) ≤ 181 ^ k := by
          calc (181 : ℕ) = 181 ^ 1 := (pow_one _).symm
            _ ≤ 181 ^ k := Nat.pow_le_pow_right (by decide) hk
        have h1 : (11 * c) * 181 ≤ (11 * c) * 181 ^ k := Nat.mul_le_mul (le_refl _) e1
        have h2 : (11 * c) * 181 ^ k = 11 ^ (r + 1) * 181 := h.symm
        rw [h2] at h1
        exact Nat.le_of_mul_le_mul_right h1 (by decide)
      apply IH (11 * c)
      · calc 11 * c ≤ 11 ^ (r + 1) := hub
          _ = 11 * 11 ^ r := pow_succ' _ _
          _ ≤ 181 * 11 ^ r := Nat.mul_le_mul (by decide) (le_refl _)
          _ = 11 ^ r * 181 := by rw [mul_comm]
          _ < n := hlt
      · calc 8 ≤ 11 := by decide
          _ ≤ 11 * c := Nat.le_mul_of_pos_right _ hc

/-- A wins from every `n ≥ 8`. -/
theorem awins_of_ge_8 (n : ℕ) : 8 ≤ n → AWins n := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro h
    by_cases hbig : 1992 ≤ n
    · exact aw_big hbig IH
    · have h' : n ≤ 11 ∨ (12 ≤ n ∧ n ≤ 16) ∨ (17 ≤ n ∧ n ≤ 22) ∨
        (23 ≤ n ∧ n ≤ 44) ∨ (45 ≤ n ∧ n ≤ 1990) ∨ n = 1991 := by omega
      rcases h' with h' | h' | h' | h' | h' | h'
      · exact aw_8_11 h h'
      · exact aw_12_16 h'.1 h'.2
      · exact aw_17_22 h'.1 h'.2
      · exact aw_23_44 h'.1 h'.2
      · exact aw_45_1990 h'.1 h'.2
      · subst h'; exact aw_1991

/-! ### A does not win below 8 -/

/-- From any non-prime-power `m ∈ [2, 49]`, B has a legal move into `[2, 7]`. -/
theorem escape_le49 {m : ℕ} (h₁ : 2 ≤ m) (h₂ : m ≤ 49) (h₃ : ¬ IsPrimePow m) :
    ∃ m', BMove m m' ∧ 2 ≤ m' ∧ m' ≤ 7 := by
  interval_cases m
  · exact absurd ((isPrimePow_nat_iff _).mpr ⟨2, 1, by norm_num, by decide, by decide⟩) h₃
  · exact absurd ((isPrimePow_nat_iff _).mpr ⟨3, 1, by norm_num, by decide, by decide⟩) h₃
  · exact absurd ((isPrimePow_nat_iff _).mpr ⟨2, 2, by norm_num, by decide, by decide⟩) h₃
  · exact absurd ((isPrimePow_nat_iff _).mpr ⟨5, 1, by norm_num, by decide, by decide⟩) h₃
  · exact ⟨2, ⟨3, 1, by norm_num, by decide, by decide⟩, by decide, by decide⟩
  · exact absurd ((isPrimePow_nat_iff _).mpr ⟨7, 1, by norm_num, by decide, by decide⟩) h₃
  · exact absurd ((isPrimePow_nat_iff _).mpr ⟨2, 3, by norm_num, by decide, by decide⟩) h₃
  · exact absurd ((isPrimePow_nat_iff _).mpr ⟨3, 2, by norm_num, by decide, by decide⟩) h₃
  · exact ⟨2, ⟨5, 1, by norm_num, by decide, by decide⟩, by decide, by decide⟩
  · exact absurd ((isPrimePow_nat_iff _).mpr ⟨11, 1, by norm_num, by decide, by decide⟩) h₃
  · exact ⟨3, ⟨2, 2, by norm_num, by decide, by decide⟩, by decide, by decide⟩
  · exact absurd ((isPrimePow_nat_iff _).mpr ⟨13, 1, by norm_num, by decide, by decide⟩) h₃
  · exact ⟨2, ⟨7, 1, by norm_num, by decide, by decide⟩, by decide, by decide⟩
  · exact ⟨3, ⟨5, 1, by norm_num, by decide, by decide⟩, by decide, by decide⟩
  · exact absurd ((isPrimePow_nat_iff _).mpr ⟨2, 4, by norm_num, by decide, by decide⟩) h₃
  · exact absurd ((isPrimePow_nat_iff _).mpr ⟨17, 1, by norm_num, by decide, by decide⟩) h₃
  · exact ⟨2, ⟨3, 2, by norm_num, by decide, by decide⟩, by decide, by decide⟩
  · exact absurd ((isPrimePow_nat_iff _).mpr ⟨19, 1, by norm_num, by decide, by decide⟩) h₃
  · exact ⟨4, ⟨5, 1, by norm_num, by decide, by decide⟩, by decide, by decide⟩
  · exact ⟨3, ⟨7, 1, by norm_num, by decide, by decide⟩, by decide, by decide⟩
  · exact ⟨2, ⟨11, 1, by norm_num, by decide, by decide⟩, by decide, by decide⟩
  · exact absurd ((isPrimePow_nat_iff _).mpr ⟨23, 1, by norm_num, by decide, by decide⟩) h₃
  · exact ⟨3, ⟨2, 3, by norm_num, by decide, by decide⟩, by decide, by decide⟩
  · exact absurd ((isPrimePow_nat_iff _).mpr ⟨5, 2, by norm_num, by decide, by decide⟩) h₃
  · exact ⟨2, ⟨13, 1, by norm_num, by decide, by decide⟩, by decide, by decide⟩
  · exact absurd ((isPrimePow_nat_iff _).mpr ⟨3, 3, by norm_num, by decide, by decide⟩) h₃
  · exact ⟨4, ⟨7, 1, by norm_num, by decide, by decide⟩, by decide, by decide⟩
  · exact absurd ((isPrimePow_nat_iff _).mpr ⟨29, 1, by norm_num, by decide, by decide⟩) h₃
  · exact ⟨6, ⟨5, 1, by norm_num, by decide, by decide⟩, by decide, by decide⟩
  · exact absurd ((isPrimePow_nat_iff _).mpr ⟨31, 1, by norm_num, by decide, by decide⟩) h₃
  · exact absurd ((isPrimePow_nat_iff _).mpr ⟨2, 5, by norm_num, by decide, by decide⟩) h₃
  · exact ⟨3, ⟨11, 1, by norm_num, by decide, by decide⟩, by decide, by decide⟩
  · exact ⟨2, ⟨17, 1, by norm_num, by decide, by decide⟩, by decide, by decide⟩
  · exact ⟨5, ⟨7, 1, by norm_num, by decide, by decide⟩, by decide, by decide⟩
  · exact ⟨4, ⟨3, 2, by norm_num, by decide, by decide⟩, by decide, by decide⟩
  · exact absurd ((isPrimePow_nat_iff _).mpr ⟨37, 1, by norm_num, by decide, by decide⟩) h₃
  · exact ⟨2, ⟨19, 1, by norm_num, by decide, by decide⟩, by decide, by decide⟩
  · exact ⟨3, ⟨13, 1, by norm_num, by decide, by decide⟩, by decide, by decide⟩
  · exact ⟨5, ⟨2, 3, by norm_num, by decide, by decide⟩, by decide, by decide⟩
  · exact absurd ((isPrimePow_nat_iff _).mpr ⟨41, 1, by norm_num, by decide, by decide⟩) h₃
  · exact ⟨6, ⟨7, 1, by norm_num, by decide, by decide⟩, by decide, by decide⟩
  · exact absurd ((isPrimePow_nat_iff _).mpr ⟨43, 1, by norm_num, by decide, by decide⟩) h₃
  · exact ⟨4, ⟨11, 1, by norm_num, by decide, by decide⟩, by decide, by decide⟩
  · exact ⟨5, ⟨3, 2, by norm_num, by decide, by decide⟩, by decide, by decide⟩
  · exact ⟨2, ⟨23, 1, by norm_num, by decide, by decide⟩, by decide, by decide⟩
  · exact absurd ((isPrimePow_nat_iff _).mpr ⟨47, 1, by norm_num, by decide, by decide⟩) h₃
  · exact ⟨6, ⟨2, 3, by norm_num, by decide, by decide⟩, by decide, by decide⟩
  · exact absurd ((isPrimePow_nat_iff _).mpr ⟨7, 2, by norm_num, by decide, by decide⟩) h₃

theorem awins_ge {n : ℕ} (h : AWins n) : n = 1 ∨ 8 ≤ n := by
  induction h with
  | win n h₁ h₂ =>
      right
      by_contra hc
      have h44 : n ≤ 44 := by omega
      have h3 : n ^ 2 ≤ 1936 := by
        calc n ^ 2 ≤ 44 ^ 2 := Nat.pow_le_pow_left h44 2
          _ = 1936 := by decide
      omega
  | move n m h₁ h₂ h₃ h₄ IH =>
      by_cases hn : 8 ≤ n
      · exact Or.inr hn
      · by_cases hn1 : n = 1
        · exact Or.inl hn1
        · by_cases hn0 : n = 0
          · subst hn0
            have h₂' : m ≤ 0 := by simpa using h₂
            have hm0 : m = 0 := by omega
            subst hm0
            exact IH 0 ⟨2, 1, by norm_num, by decide, by decide⟩
          · have h2n : 2 ≤ n := by omega
            have h7n : n ≤ 7 := by omega
            obtain ⟨m', hbm, h2', h7'⟩ := escape_le49 (le_trans h2n h₁)
              (le_trans h₂ (le_trans (Nat.pow_le_pow_left h7n 2) (by decide))) h₃
            have hIH := IH m' hbm
            omega

/-! ### Determinism: A and B cannot both have a winning strategy -/

theorem awins_not_bwinsstart {n : ℕ} (hA : AWins n) : BWinsStart n → False := by
  induction hA with
  | win n h₁ h₂ =>
      intro hB
      exact (hB 1990 h₁ h₂).1 rfl
  | move n m h₁ h₂ h₃ h₄ IH =>
      intro hB
      have hBm := (hB m h₁ h₂).2
      cases hBm with
      | one m₁ h =>
          obtain ⟨p, r, hp, hr, hmr⟩ := h
          exact h₃ ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, by omega⟩)
      | move m₁ m' hl hm1 hm2 hm3 =>
          exact IH m' hl (fun m'' a b => ⟨hm2 m'' a b, hm3 m'' a b⟩)

/-! ### B wins from `n₀ ∈ {2, 3, 4, 5}` -/

theorem bw_pp {m : ℕ} (h : IsPrimePow m) : BWins m := by
  rw [isPrimePow_nat_iff] at h
  obtain ⟨p, r, hp, hr, hpr⟩ := h
  apply BWins.one
  exact ⟨p, r, hp, hr, by rw [one_mul, hpr]⟩

theorem bw_le_11 {m : ℕ} (h₁ : 2 ≤ m) (h₂ : m ≤ 11) : BWins m := by
  interval_cases m
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨2, 1, by norm_num, by decide, by decide⟩)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨3, 1, by norm_num, by decide, by decide⟩)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨2, 2, by norm_num, by decide, by decide⟩)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨5, 1, by norm_num, by decide, by decide⟩)
  · apply BWins.move (m := 6) (m' := 2) (⟨3, 1, by norm_num, by decide, by decide⟩ : BMove 6 2) (by decide)
    · intro m'' h₁ h₂
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      omega
    · intro m'' h₁ h₂
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      interval_cases m''
      · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨2, 1, by norm_num, by decide, by decide⟩)
      · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨3, 1, by norm_num, by decide, by decide⟩)
      · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨2, 2, by norm_num, by decide, by decide⟩)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨7, 1, by norm_num, by decide, by decide⟩)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨2, 3, by norm_num, by decide, by decide⟩)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨3, 2, by norm_num, by decide, by decide⟩)
  · apply BWins.move (m := 10) (m' := 2) (⟨5, 1, by norm_num, by decide, by decide⟩ : BMove 10 2) (by decide)
    · intro m'' h₁ h₂
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      omega
    · intro m'' h₁ h₂
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      interval_cases m''
      · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨2, 1, by norm_num, by decide, by decide⟩)
      · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨3, 1, by norm_num, by decide, by decide⟩)
      · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨2, 2, by norm_num, by decide, by decide⟩)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨11, 1, by norm_num, by decide, by decide⟩)

theorem bw_le_19 {m : ℕ} (h₁ : 2 ≤ m) (h₂ : m ≤ 19) : BWins m := by
  interval_cases m
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨2, 1, by norm_num, by decide, by decide⟩)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨3, 1, by norm_num, by decide, by decide⟩)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨2, 2, by norm_num, by decide, by decide⟩)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨5, 1, by norm_num, by decide, by decide⟩)
  · apply BWins.move (m := 6) (m' := 2) (⟨3, 1, by norm_num, by decide, by decide⟩ : BMove 6 2) (by decide)
    · intro m'' h₁ h₂
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      omega
    · intro m'' h₁ h₂
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      interval_cases m'' <;> exact bw_le_11 (by decide) (by decide)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨7, 1, by norm_num, by decide, by decide⟩)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨2, 3, by norm_num, by decide, by decide⟩)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨3, 2, by norm_num, by decide, by decide⟩)
  · apply BWins.move (m := 10) (m' := 2) (⟨5, 1, by norm_num, by decide, by decide⟩ : BMove 10 2) (by decide)
    · intro m'' h₁ h₂
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      omega
    · intro m'' h₁ h₂
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      interval_cases m'' <;> exact bw_le_11 (by decide) (by decide)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨11, 1, by norm_num, by decide, by decide⟩)
  · apply BWins.move (m := 12) (m' := 3) (⟨2, 2, by norm_num, by decide, by decide⟩ : BMove 12 3) (by decide)
    · intro m'' h₁ h₂
      have hb : m'' ≤ 9 := le_trans h₂ (by decide)
      omega
    · intro m'' h₁ h₂
      have hb : m'' ≤ 9 := le_trans h₂ (by decide)
      interval_cases m'' <;> exact bw_le_11 (by decide) (by decide)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨13, 1, by norm_num, by decide, by decide⟩)
  · apply BWins.move (m := 14) (m' := 2) (⟨7, 1, by norm_num, by decide, by decide⟩ : BMove 14 2) (by decide)
    · intro m'' h₁ h₂
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      omega
    · intro m'' h₁ h₂
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      interval_cases m'' <;> exact bw_le_11 (by decide) (by decide)
  · apply BWins.move (m := 15) (m' := 3) (⟨5, 1, by norm_num, by decide, by decide⟩ : BMove 15 3) (by decide)
    · intro m'' h₁ h₂
      have hb : m'' ≤ 9 := le_trans h₂ (by decide)
      omega
    · intro m'' h₁ h₂
      have hb : m'' ≤ 9 := le_trans h₂ (by decide)
      interval_cases m'' <;> exact bw_le_11 (by decide) (by decide)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨2, 4, by norm_num, by decide, by decide⟩)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨17, 1, by norm_num, by decide, by decide⟩)
  · apply BWins.move (m := 18) (m' := 2) (⟨3, 2, by norm_num, by decide, by decide⟩ : BMove 18 2) (by decide)
    · intro m'' h₁ h₂
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      omega
    · intro m'' h₁ h₂
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      interval_cases m'' <;> exact bw_le_11 (by decide) (by decide)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨19, 1, by norm_num, by decide, by decide⟩)

theorem bw_le_29 {m : ℕ} (h₁ : 2 ≤ m) (h₂ : m ≤ 29) : BWins m := by
  interval_cases m
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨2, 1, by norm_num, by decide, by decide⟩)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨3, 1, by norm_num, by decide, by decide⟩)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨2, 2, by norm_num, by decide, by decide⟩)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨5, 1, by norm_num, by decide, by decide⟩)
  · apply BWins.move (m := 6) (m' := 2) (⟨3, 1, by norm_num, by decide, by decide⟩ : BMove 6 2) (by decide)
    · intro m'' h₁ h₂
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      omega
    · intro m'' h₁ h₂
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      interval_cases m'' <;> exact bw_le_11 (by decide) (by decide)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨7, 1, by norm_num, by decide, by decide⟩)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨2, 3, by norm_num, by decide, by decide⟩)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨3, 2, by norm_num, by decide, by decide⟩)
  · apply BWins.move (m := 10) (m' := 2) (⟨5, 1, by norm_num, by decide, by decide⟩ : BMove 10 2) (by decide)
    · intro m'' h₁ h₂
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      omega
    · intro m'' h₁ h₂
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      interval_cases m'' <;> exact bw_le_11 (by decide) (by decide)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨11, 1, by norm_num, by decide, by decide⟩)
  · apply BWins.move (m := 12) (m' := 3) (⟨2, 2, by norm_num, by decide, by decide⟩ : BMove 12 3) (by decide)
    · intro m'' h₁ h₂
      have hb : m'' ≤ 9 := le_trans h₂ (by decide)
      omega
    · intro m'' h₁ h₂
      have hb : m'' ≤ 9 := le_trans h₂ (by decide)
      interval_cases m'' <;> exact bw_le_11 (by decide) (by decide)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨13, 1, by norm_num, by decide, by decide⟩)
  · apply BWins.move (m := 14) (m' := 2) (⟨7, 1, by norm_num, by decide, by decide⟩ : BMove 14 2) (by decide)
    · intro m'' h₁ h₂
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      omega
    · intro m'' h₁ h₂
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      interval_cases m'' <;> exact bw_le_11 (by decide) (by decide)
  · apply BWins.move (m := 15) (m' := 3) (⟨5, 1, by norm_num, by decide, by decide⟩ : BMove 15 3) (by decide)
    · intro m'' h₁ h₂
      have hb : m'' ≤ 9 := le_trans h₂ (by decide)
      omega
    · intro m'' h₁ h₂
      have hb : m'' ≤ 9 := le_trans h₂ (by decide)
      interval_cases m'' <;> exact bw_le_11 (by decide) (by decide)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨2, 4, by norm_num, by decide, by decide⟩)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨17, 1, by norm_num, by decide, by decide⟩)
  · apply BWins.move (m := 18) (m' := 2) (⟨3, 2, by norm_num, by decide, by decide⟩ : BMove 18 2) (by decide)
    · intro m'' h₁ h₂
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      omega
    · intro m'' h₁ h₂
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      interval_cases m'' <;> exact bw_le_11 (by decide) (by decide)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨19, 1, by norm_num, by decide, by decide⟩)
  · apply BWins.move (m := 20) (m' := 4) (⟨5, 1, by norm_num, by decide, by decide⟩ : BMove 20 4) (by decide)
    · intro m'' h₁ h₂
      have hb : m'' ≤ 16 := le_trans h₂ (by decide)
      omega
    · intro m'' h₁ h₂
      have hb : m'' ≤ 16 := le_trans h₂ (by decide)
      interval_cases m'' <;> exact bw_le_19 (by decide) (by decide)
  · apply BWins.move (m := 21) (m' := 3) (⟨7, 1, by norm_num, by decide, by decide⟩ : BMove 21 3) (by decide)
    · intro m'' h₁ h₂
      have hb : m'' ≤ 9 := le_trans h₂ (by decide)
      omega
    · intro m'' h₁ h₂
      have hb : m'' ≤ 9 := le_trans h₂ (by decide)
      interval_cases m'' <;> exact bw_le_11 (by decide) (by decide)
  · apply BWins.move (m := 22) (m' := 2) (⟨11, 1, by norm_num, by decide, by decide⟩ : BMove 22 2) (by decide)
    · intro m'' h₁ h₂
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      omega
    · intro m'' h₁ h₂
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      interval_cases m'' <;> exact bw_le_11 (by decide) (by decide)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨23, 1, by norm_num, by decide, by decide⟩)
  · apply BWins.move (m := 24) (m' := 3) (⟨2, 3, by norm_num, by decide, by decide⟩ : BMove 24 3) (by decide)
    · intro m'' h₁ h₂
      have hb : m'' ≤ 9 := le_trans h₂ (by decide)
      omega
    · intro m'' h₁ h₂
      have hb : m'' ≤ 9 := le_trans h₂ (by decide)
      interval_cases m'' <;> exact bw_le_11 (by decide) (by decide)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨5, 2, by norm_num, by decide, by decide⟩)
  · apply BWins.move (m := 26) (m' := 2) (⟨13, 1, by norm_num, by decide, by decide⟩ : BMove 26 2) (by decide)
    · intro m'' h₁ h₂
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      omega
    · intro m'' h₁ h₂
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      interval_cases m'' <;> exact bw_le_11 (by decide) (by decide)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨3, 3, by norm_num, by decide, by decide⟩)
  · apply BWins.move (m := 28) (m' := 4) (⟨7, 1, by norm_num, by decide, by decide⟩ : BMove 28 4) (by decide)
    · intro m'' h₁ h₂
      have hb : m'' ≤ 16 := le_trans h₂ (by decide)
      omega
    · intro m'' h₁ h₂
      have hb : m'' ≤ 16 := le_trans h₂ (by decide)
      interval_cases m'' <;> exact bw_le_19 (by decide) (by decide)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨29, 1, by norm_num, by decide, by decide⟩)

theorem bwinsstart_2 : BWinsStart 2 := by
  intro m h₁ h₂
  have h4 : m ≤ 4 := le_trans h₂ (by decide)
  exact ⟨by omega, bw_le_11 (by omega) (by omega)⟩

theorem bwinsstart_3 : BWinsStart 3 := by
  intro m h₁ h₂
  have h9 : m ≤ 9 := le_trans h₂ (by decide)
  exact ⟨by omega, bw_le_11 (by omega) (by omega)⟩

theorem bwinsstart_4 : BWinsStart 4 := by
  intro m h₁ h₂
  have h16 : m ≤ 16 := le_trans h₂ (by decide)
  exact ⟨by omega, bw_le_19 (by omega) (by omega)⟩

theorem bwinsstart_5 : BWinsStart 5 := by
  intro m h₁ h₂
  have h25 : m ≤ 25 := le_trans h₂ (by decide)
  exact ⟨by omega, bw_le_29 (by omega) (by omega)⟩

/-! ### B does not win from 30, hence not from `n₀ ∈ {6, 7}` -/

/-- B has no winning strategy from any of 30, 60, 140, 280, 504: from each of these,
every legal move of B either is impossible, loses to A grabbing 1990, or lands back in
the same set (the induction hypothesis applies). -/
theorem not_bwins_trap {m : ℕ} (h : BWins m) :
    m ≠ 30 ∧ m ≠ 60 ∧ m ≠ 140 ∧ m ≠ 280 ∧ m ≠ 504 := by
  induction h with
  | one m h =>
      obtain ⟨p, r, hp, hr, hmr⟩ := h
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro heq <;> subst heq
      · exact not_pp30 ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, by omega⟩)
      · exact not_pp60 ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, by omega⟩)
      · exact not_pp140 ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, by omega⟩)
      · exact not_pp280 ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, by omega⟩)
      · exact not_pp504 ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, by omega⟩)
  | move m m' hl hm1 hm2 hm3 IH =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro heq <;> subst heq
      · -- B to move at 30
        obtain ⟨p, r, hp, hr, h⟩ := hl
        have hd : m' ∈ Nat.divisors 30 := Nat.mem_divisors.mpr ⟨⟨p ^ r, h⟩, by decide⟩
        rw [divisors30] at hd
        fin_cases hd
        · exact absurd rfl hm1
        · have hpr : p ^ r = 15 := by omega
          exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp15
        · have hpr : p ^ r = 10 := by omega
          exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp10
        · have hpr : p ^ r = 6 := by omega
          exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp6
        · exact (IH 30 (by decide) (by decide)).1 rfl
        · exact (IH 60 (by decide) (by decide)).2.1 rfl
        · exact (IH 140 (by decide) (by decide)).2.2.1 rfl
        · have hpr : p ^ r = 1 := by omega
          exact absurd hpr (prime_pow_ne_one hp hr)
      · -- B to move at 60
        obtain ⟨p, r, hp, hr, h⟩ := hl
        have hd : m' ∈ Nat.divisors 60 := Nat.mem_divisors.mpr ⟨⟨p ^ r, h⟩, by decide⟩
        rw [divisors60] at hd
        fin_cases hd
        · exact absurd rfl hm1
        · have hpr : p ^ r = 30 := by omega
          exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp30
        · have hpr : p ^ r = 20 := by omega
          exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp20
        · have hpr : p ^ r = 15 := by omega
          exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp15
        · have hpr : p ^ r = 12 := by omega
          exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp12
        · have hpr : p ^ r = 10 := by omega
          exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp10
        · have hpr : p ^ r = 6 := by omega
          exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp6
        · exact (IH 140 (by decide) (by decide)).2.2.1 rfl
        · exact (IH 140 (by decide) (by decide)).2.2.1 rfl
        · exact (IH 280 (by decide) (by decide)).2.2.2.1 rfl
        · exact (IH 504 (by decide) (by decide)).2.2.2.2 rfl
        · have hpr : p ^ r = 1 := by omega
          exact absurd hpr (prime_pow_ne_one hp hr)
      · -- B to move at 140
        obtain ⟨p, r, hp, hr, h⟩ := hl
        have hd : m' ∈ Nat.divisors 140 := Nat.mem_divisors.mpr ⟨⟨p ^ r, h⟩, by decide⟩
        rw [divisors140] at hd
        fin_cases hd
        · exact absurd rfl hm1
        · have hpr : p ^ r = 70 := by omega
          exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp70
        · have hpr : p ^ r = 35 := by omega
          exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp35
        · have hpr : p ^ r = 28 := by omega
          exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp28
        · have hpr : p ^ r = 20 := by omega
          exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp20
        · have hpr : p ^ r = 14 := by omega
          exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp14
        · have hpr : p ^ r = 10 := by omega
          exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp10
        · exact (IH 280 (by decide) (by decide)).2.2.2.1 rfl
        · exact (IH 504 (by decide) (by decide)).2.2.2.2 rfl
        · exact (IH 504 (by decide) (by decide)).2.2.2.2 rfl
        · exact hm2 1990 (by decide) (by decide) rfl
        · have hpr : p ^ r = 1 := by omega
          exact absurd hpr (prime_pow_ne_one hp hr)
      · -- B to move at 280
        obtain ⟨p, r, hp, hr, h⟩ := hl
        have hd : m' ∈ Nat.divisors 280 := Nat.mem_divisors.mpr ⟨⟨p ^ r, h⟩, by decide⟩
        rw [divisors280] at hd
        fin_cases hd
        · exact absurd rfl hm1
        · have hpr : p ^ r = 140 := by omega
          exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp140
        · have hpr : p ^ r = 70 := by omega
          exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp70
        · have hpr : p ^ r = 56 := by omega
          exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp56
        · have hpr : p ^ r = 40 := by omega
          exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp40
        · have hpr : p ^ r = 35 := by omega
          exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp35
        · have hpr : p ^ r = 28 := by omega
          exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp28
        · have hpr : p ^ r = 20 := by omega
          exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp20
        · have hpr : p ^ r = 14 := by omega
          exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp14
        · have hpr : p ^ r = 10 := by omega
          exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp10
        · exact (IH 504 (by decide) (by decide)).2.2.2.2 rfl
        · exact (IH 504 (by decide) (by decide)).2.2.2.2 rfl
        · exact hm2 1990 (by decide) (by decide) rfl
        · exact hm2 1990 (by decide) (by decide) rfl
        · exact hm2 1990 (by decide) (by decide) rfl
        · have hpr : p ^ r = 1 := by omega
          exact absurd hpr (prime_pow_ne_one hp hr)
      · -- B to move at 504
        obtain ⟨p, r, hp, hr, h⟩ := hl
        have hd : m' ∈ Nat.divisors 504 := Nat.mem_divisors.mpr ⟨⟨p ^ r, h⟩, by decide⟩
        rw [divisors504] at hd
        fin_cases hd
        · exact absurd rfl hm1
        · have hpr : p ^ r = 252 := by omega
          exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp252
        · have hpr : p ^ r = 168 := by omega
          exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp168
        · have hpr : p ^ r = 126 := by omega
          exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp126
        · have hpr : p ^ r = 84 := by omega
          exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp84
        · have hpr : p ^ r = 72 := by omega
          exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp72
        · have hpr : p ^ r = 63 := by omega
          exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp63
        · have hpr : p ^ r = 56 := by omega
          exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp56
        · have hpr : p ^ r = 42 := by omega
          exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp42
        · have hpr : p ^ r = 36 := by omega
          exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp36
        · have hpr : p ^ r = 28 := by omega
          exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp28
        · have hpr : p ^ r = 24 := by omega
          exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp24
        · have hpr : p ^ r = 21 := by omega
          exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp21
        · have hpr : p ^ r = 18 := by omega
          exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp18
        · have hpr : p ^ r = 14 := by omega
          exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp14
        · have hpr : p ^ r = 12 := by omega
          exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp12
        · exact hm2 1990 (by decide) (by decide) rfl
        · exact hm2 1990 (by decide) (by decide) rfl
        · exact hm2 1990 (by decide) (by decide) rfl
        · have hpr : p ^ r = 6 := by omega
          exact absurd ((isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, hpr⟩) not_pp6
        · exact hm2 1990 (by decide) (by decide) rfl
        · exact hm2 1990 (by decide) (by decide) rfl
        · exact hm2 1990 (by decide) (by decide) rfl
        · have hpr : p ^ r = 1 := by omega
          exact absurd hpr (prime_pow_ne_one hp hr)

theorem not_bwinsstart_6 : ¬ BWinsStart 6 := by
  intro h
  obtain ⟨h1, h2⟩ := h 30 (by decide) (by decide)
  exact (not_bwins_trap h2).1 rfl

theorem not_bwinsstart_7 : ¬ BWinsStart 7 := by
  intro h
  obtain ⟨h1, h2⟩ := h 30 (by decide) (by decide)
  exact (not_bwins_trap h2).1 rfl

snip end

/-- The answer to part (a): the initial values from which A has a winning strategy. -/
determine aWinsSet : Set ℕ := {n | 8 ≤ n}

/-- The answer to part (b): the initial values from which B has a winning strategy. -/
determine bWinsSet : Finset ℕ := {2, 3, 4, 5}

/-- The answer to part (c): the initial values for which neither player has a winning
strategy (a draw). -/
determine drawSet : Finset ℕ := {6, 7}

problem imo1990_p5 (n : ℕ) (hn : 2 ≤ n) :
    (AWins n ↔ n ∈ aWinsSet) ∧ (BWinsStart n ↔ n ∈ bWinsSet) ∧
      ((¬ AWins n ∧ ¬ BWinsStart n) ↔ n ∈ drawSet) := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro h
      rcases awins_ge h with h1 | h1
      · exfalso; omega
      · exact h1
    · intro h
      exact awins_of_ge_8 n h
  · constructor
    · intro h
      by_cases h8 : 8 ≤ n
      · exact (awins_not_bwinsstart (awins_of_ge_8 n h8) h).elim
      · interval_cases n
        · decide
        · decide
        · decide
        · decide
        · exact absurd h not_bwinsstart_6
        · exact absurd h not_bwinsstart_7
    · intro h
      fin_cases h
      · exact bwinsstart_2
      · exact bwinsstart_3
      · exact bwinsstart_4
      · exact bwinsstart_5
  · constructor
    · intro ⟨hA, hB⟩
      by_cases h8 : 8 ≤ n
      · exact absurd (awins_of_ge_8 n h8) hA
      · interval_cases n
        · exact absurd bwinsstart_2 hB
        · exact absurd bwinsstart_3 hB
        · exact absurd bwinsstart_4 hB
        · exact absurd bwinsstart_5 hB
        · decide
        · decide
    · intro h
      fin_cases h
      · exact ⟨fun hA => by rcases awins_ge hA with h1 | h1 <;> omega, not_bwinsstart_6⟩
      · exact ⟨fun hA => by rcases awins_ge hA with h1 | h1 <;> omega, not_bwinsstart_7⟩

end Imo1990P5
