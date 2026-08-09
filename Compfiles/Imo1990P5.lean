/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Algebra.IsPrimePow
public import Mathlib.Data.Finset.NatDivisors
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

## Formalization notes

The proof follows a solution sketch after kalva.
-/

namespace Imo1990P5

/-- A legal move of player A: from the number `n` just chosen by B (or the initial
number `n₀`), A may choose any `m` with `n ≤ m ≤ n ^ 2` (A wins by choosing 1990). -/
@[reducible] def AMove (n m : ℕ) : Prop := n ≤ m ∧ m ≤ n ^ 2

/-- A legal move of player B: from the number `m` just chosen by A, B may choose any
`m'` such that `m / m'` is a prime power `p ^ r` with `r ≥ 1` (B wins by choosing 1). -/
@[reducible] def BMove (m m' : ℕ) : Prop := ∃ p r : ℕ, p.Prime ∧ 0 < r ∧ m = m' * p ^ r

/-- `AWins n`: it is A's turn and the current number is `n` (the initial position has
`n = n₀`), and A has a winning strategy. A either wins immediately by choosing 1990
(a legal move from `n`), or chooses a legal move `m` from which B cannot win
(B wins by choosing 1) and such that every legal answer of B is again a winning
position for A. -/
inductive AWins : ℕ → Prop
  | win (n : ℕ) (h : AMove n 1990) : AWins n
  | move (n m : ℕ) (h₁ : AMove n m) (h₂ : ¬ BMove m 1)
      (h₃ : ∀ m', BMove m m' → AWins m') : AWins n

/-- `BWins m`: it is B's turn and the current number is `m`, and B has a winning
strategy. B either wins immediately by choosing 1, or chooses a legal move `m' ≠ 1`
from which A cannot win (A wins by choosing 1990) and such that every legal answer
of A is again a winning position for B. -/
inductive BWins : ℕ → Prop
  | one (m : ℕ) (h : BMove m 1) : BWins m
  | move (m m' : ℕ) (h : BMove m m') (h₁ : m' ≠ 1)
      (h₂ : ∀ m'', AMove m' m'' → m'' ≠ 1990)
      (h₃ : ∀ m'', AMove m' m'' → BWins m'') : BWins m

/-- `BWinsStart n`: B has a winning strategy from the initial position with `n₀ = n`
(it is A's turn): whatever legal first move `m` A makes, it is not 1990 and B wins
from `m`. -/
def BWinsStart (n : ℕ) : Prop := ∀ m, AMove n m → m ≠ 1990 ∧ BWins m

snip begin

/-- B can win from the move `m` (by choosing 1) iff `m` is a prime power. -/
theorem bmove_one_iff_isPrimePow {m : ℕ} : BMove m 1 ↔ IsPrimePow m := by
  constructor
  · rintro ⟨p, r, hp, hr, h⟩
    exact (isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, by rw [h, one_mul]⟩
  · intro h
    rw [isPrimePow_nat_iff] at h
    obtain ⟨p, r, hp, hr, hpr⟩ := h
    exact ⟨p, r, hp, hr, by rw [one_mul, hpr]⟩

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

/-- The legal responses available to B after A chooses `m`.  Keeping only divisors
whose complementary factor is a prime power avoids reasoning about impossible moves. -/
def bResponses (m : ℕ) : Finset ℕ :=
  m.divisors.filter fun m' => IsPrimePow (m / m')

theorem bmove_iff_mem_bResponses {m m' : ℕ} (hm : m ≠ 0) :
    BMove m m' ↔ m' ∈ bResponses m := by
  rw [bResponses, Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨p, r, hp, hr, h⟩
    have hm' : 0 < m' := by
      by_contra hm'
      simp only [not_lt, nonpos_iff_eq_zero] at hm'
      rw [hm', zero_mul] at h
      exact hm h
    refine ⟨⟨⟨p ^ r, h⟩, hm⟩, (isPrimePow_nat_iff _).mpr ⟨p, r, hp, hr, ?_⟩⟩
    exact (Nat.div_eq_of_eq_mul_right hm' h).symm
  · rintro ⟨⟨hd, -⟩, hpp⟩
    obtain ⟨p, r, hp, hr, hpr⟩ := (isPrimePow_nat_iff _).mp hpp
    exact ⟨p, r, hp, hr, (Nat.mul_div_cancel' hd).symm.trans (by rw [← hpr])⟩

theorem not_bmove_one_of_not_mem {m : ℕ} (hm : m ≠ 0) (h1 : 1 ∉ bResponses m) :
    ¬ BMove m 1 := fun h => h1 ((bmove_iff_mem_bResponses hm).mp h)

theorem bResponses_30 : bResponses 30 = {6, 10, 15} := by decide +kernel
theorem bResponses_60 : bResponses 60 = {12, 15, 20, 30} := by decide +kernel
theorem bResponses_140 : bResponses 140 = {20, 28, 35, 70} := by decide +kernel
theorem bResponses_280 : bResponses 280 = {35, 40, 56, 70, 140} := by decide +kernel
theorem bResponses_504 : bResponses 504 = {56, 63, 72, 126, 168, 252} := by
  decide +kernel
theorem bResponses_1991 : bResponses 1991 = {11, 181} := by decide +kernel

/-- The finite trap used for the drawn starting positions. -/
def trap : Finset ℕ := {30, 60, 140, 280, 504}

lemma ne_zero_of_mem_trap {m : ℕ} (hm : m ∈ trap) : m ≠ 0 := by
  rw [trap] at hm
  fin_cases hm <;> decide

lemma one_not_mem_bResponses_of_mem_trap {m : ℕ} (hm : m ∈ trap) :
    1 ∉ bResponses m := by
  rw [trap] at hm
  fin_cases hm <;>
    simp [bResponses_30, bResponses_60, bResponses_140, bResponses_280, bResponses_504]

/-- Whatever B plays from a trap number, A can legally return to that same number. -/
lemma return_to_trap {m m' : ℕ} (hm : m ∈ trap) (hm' : m' ∈ bResponses m) :
    AMove m' m := by
  rw [trap] at hm
  fin_cases hm
  all_goals first
    | rw [bResponses_30] at hm'
    | rw [bResponses_60] at hm'
    | rw [bResponses_140] at hm'
    | rw [bResponses_280] at hm'
    | rw [bResponses_504] at hm'
  all_goals fin_cases hm' <;> decide

/-! ### A wins from `n₀ ≥ 8`

A's winning strategy, following kalva: the moves 60, 140, 280, 504, 1990 cover
`[8, 1990]`, 1991 covers `n = 1991`, and `11 ^ (r + 1) * 181` covers `n ≥ 1992` by
strong induction. -/

theorem aw_45_1990 {n : ℕ} (h₁ : 45 ≤ n) (h₂ : n ≤ 1990) : AWins n := by
  apply AWins.win
  exact ⟨h₂, by nlinarith [h₁]⟩

theorem aw_23_44 {n : ℕ} (h₁ : 23 ≤ n) (h₂ : n ≤ 44) : AWins n := by
  apply AWins.move (m := 504)
  · exact ⟨by omega, by nlinarith [h₁]⟩
  · exact not_bmove_one_of_not_mem (by decide) (by simp [bResponses_504])
  · intro m' hm'
    have hm' := (bmove_iff_mem_bResponses (m := 504) (by decide)).mp hm'
    rw [bResponses_504] at hm'
    fin_cases hm' <;> exact aw_45_1990 (by decide) (by decide)

theorem aw_17_22 {n : ℕ} (h₁ : 17 ≤ n) (h₂ : n ≤ 22) : AWins n := by
  apply AWins.move (m := 280)
  · exact ⟨by omega, by nlinarith [h₁]⟩
  · exact not_bmove_one_of_not_mem (by decide) (by simp [bResponses_280])
  · intro m' hm'
    have hm' := (bmove_iff_mem_bResponses (m := 280) (by decide)).mp hm'
    rw [bResponses_280] at hm'
    fin_cases hm' <;> first
      | exact aw_23_44 (by decide) (by decide)
      | exact aw_45_1990 (by decide) (by decide)

theorem aw_12_16 {n : ℕ} (h₁ : 12 ≤ n) (h₂ : n ≤ 16) : AWins n := by
  apply AWins.move (m := 140)
  · exact ⟨by omega, by nlinarith [h₁]⟩
  · exact not_bmove_one_of_not_mem (by decide) (by simp [bResponses_140])
  · intro m' hm'
    have hm' := (bmove_iff_mem_bResponses (m := 140) (by decide)).mp hm'
    rw [bResponses_140] at hm'
    fin_cases hm' <;> first
      | exact aw_17_22 (by decide) (by decide)
      | exact aw_23_44 (by decide) (by decide)
      | exact aw_45_1990 (by decide) (by decide)

theorem aw_8_11 {n : ℕ} (h₁ : 8 ≤ n) (h₂ : n ≤ 11) : AWins n := by
  apply AWins.move (m := 60)
  · exact ⟨by omega, by nlinarith [h₁]⟩
  · exact not_bmove_one_of_not_mem (by decide) (by simp [bResponses_60])
  · intro m' hm'
    have hm' := (bmove_iff_mem_bResponses (m := 60) (by decide)).mp hm'
    rw [bResponses_60] at hm'
    fin_cases hm' <;> first
      | exact aw_12_16 (by decide) (by decide)
      | exact aw_17_22 (by decide) (by decide)
      | exact aw_23_44 (by decide) (by decide)

theorem aw_1991 : AWins 1991 := by
  apply AWins.move (m := 1991)
  · exact ⟨by decide, by decide⟩
  · exact not_bmove_one_of_not_mem (by decide) (by simp [bResponses_1991])
  · intro m' hm'
    have hm' := (bmove_iff_mem_bResponses (m := 1991) (by decide)).mp hm'
    rw [bResponses_1991] at hm'
    fin_cases hm' <;> first
      | exact aw_8_11 (by decide) (by decide)
      | exact aw_45_1990 (by decide) (by decide)

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
  · refine ⟨hle, ?_⟩
    -- `11 ^ (r + 1) * 181 ≤ n ^ 2`
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
  · -- B cannot win from `11 ^ (r + 1) * 181`, which is not a prime power
    apply mt bmove_one_iff_isPrimePow.mp
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
  | win n h =>
      obtain ⟨-, h₂⟩ := h
      right
      by_contra hc
      have h44 : n ≤ 44 := by omega
      have h3 : n ^ 2 ≤ 1936 := by
        calc n ^ 2 ≤ 44 ^ 2 := Nat.pow_le_pow_left h44 2
          _ = 1936 := by decide
      omega
  | move n m h₁ h₂ h₃ IH =>
      by_cases hn : 8 ≤ n
      · exact Or.inr hn
      · by_cases hn1 : n = 1
        · exact Or.inl hn1
        · by_cases hn0 : n = 0
          · subst hn0
            have h₂' : m ≤ 0 := by simpa using h₁.2
            have hm0 : m = 0 := by omega
            subst hm0
            exact IH 0 ⟨2, 1, by norm_num, by decide, by decide⟩
          · have h2n : 2 ≤ n := by omega
            have h7n : n ≤ 7 := by omega
            obtain ⟨m', hbm, h2', h7'⟩ := escape_le49 (le_trans h2n h₁.1)
              (le_trans h₁.2 (le_trans (Nat.pow_le_pow_left h7n 2) (by decide)))
              (mt bmove_one_iff_isPrimePow.mpr h₂)
            have hIH := IH m' hbm
            omega

/-! ### Determinism: A and B cannot both have a winning strategy -/

theorem awins_not_bwinsstart {n : ℕ} (hA : AWins n) : BWinsStart n → False := by
  induction hA with
  | win n h =>
      intro hB
      exact (hB 1990 h).1 rfl
  | move n m h₁ h₂ h₃ IH =>
      intro hB
      have hBm := (hB m h₁).2
      cases hBm with
      | one m₁ h => exact h₂ h
      | move m₁ m' hl hm1 hm2 hm3 =>
          exact IH m' hl (fun m'' h'' => ⟨hm2 m'' h'', hm3 m'' h''⟩)

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
    · intro m'' ⟨h₁, h₂⟩
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      omega
    · intro m'' ⟨h₁, h₂⟩
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      interval_cases m''
      · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨2, 1, by norm_num, by decide, by decide⟩)
      · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨3, 1, by norm_num, by decide, by decide⟩)
      · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨2, 2, by norm_num, by decide, by decide⟩)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨7, 1, by norm_num, by decide, by decide⟩)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨2, 3, by norm_num, by decide, by decide⟩)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨3, 2, by norm_num, by decide, by decide⟩)
  · apply BWins.move (m := 10) (m' := 2) (⟨5, 1, by norm_num, by decide, by decide⟩ : BMove 10 2) (by decide)
    · intro m'' ⟨h₁, h₂⟩
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      omega
    · intro m'' ⟨h₁, h₂⟩
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
    · intro m'' ⟨h₁, h₂⟩
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      omega
    · intro m'' ⟨h₁, h₂⟩
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      interval_cases m'' <;> exact bw_le_11 (by decide) (by decide)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨7, 1, by norm_num, by decide, by decide⟩)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨2, 3, by norm_num, by decide, by decide⟩)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨3, 2, by norm_num, by decide, by decide⟩)
  · apply BWins.move (m := 10) (m' := 2) (⟨5, 1, by norm_num, by decide, by decide⟩ : BMove 10 2) (by decide)
    · intro m'' ⟨h₁, h₂⟩
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      omega
    · intro m'' ⟨h₁, h₂⟩
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      interval_cases m'' <;> exact bw_le_11 (by decide) (by decide)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨11, 1, by norm_num, by decide, by decide⟩)
  · apply BWins.move (m := 12) (m' := 3) (⟨2, 2, by norm_num, by decide, by decide⟩ : BMove 12 3) (by decide)
    · intro m'' ⟨h₁, h₂⟩
      have hb : m'' ≤ 9 := le_trans h₂ (by decide)
      omega
    · intro m'' ⟨h₁, h₂⟩
      have hb : m'' ≤ 9 := le_trans h₂ (by decide)
      interval_cases m'' <;> exact bw_le_11 (by decide) (by decide)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨13, 1, by norm_num, by decide, by decide⟩)
  · apply BWins.move (m := 14) (m' := 2) (⟨7, 1, by norm_num, by decide, by decide⟩ : BMove 14 2) (by decide)
    · intro m'' ⟨h₁, h₂⟩
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      omega
    · intro m'' ⟨h₁, h₂⟩
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      interval_cases m'' <;> exact bw_le_11 (by decide) (by decide)
  · apply BWins.move (m := 15) (m' := 3) (⟨5, 1, by norm_num, by decide, by decide⟩ : BMove 15 3) (by decide)
    · intro m'' ⟨h₁, h₂⟩
      have hb : m'' ≤ 9 := le_trans h₂ (by decide)
      omega
    · intro m'' ⟨h₁, h₂⟩
      have hb : m'' ≤ 9 := le_trans h₂ (by decide)
      interval_cases m'' <;> exact bw_le_11 (by decide) (by decide)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨2, 4, by norm_num, by decide, by decide⟩)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨17, 1, by norm_num, by decide, by decide⟩)
  · apply BWins.move (m := 18) (m' := 2) (⟨3, 2, by norm_num, by decide, by decide⟩ : BMove 18 2) (by decide)
    · intro m'' ⟨h₁, h₂⟩
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      omega
    · intro m'' ⟨h₁, h₂⟩
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
    · intro m'' ⟨h₁, h₂⟩
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      omega
    · intro m'' ⟨h₁, h₂⟩
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      interval_cases m'' <;> exact bw_le_11 (by decide) (by decide)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨7, 1, by norm_num, by decide, by decide⟩)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨2, 3, by norm_num, by decide, by decide⟩)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨3, 2, by norm_num, by decide, by decide⟩)
  · apply BWins.move (m := 10) (m' := 2) (⟨5, 1, by norm_num, by decide, by decide⟩ : BMove 10 2) (by decide)
    · intro m'' ⟨h₁, h₂⟩
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      omega
    · intro m'' ⟨h₁, h₂⟩
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      interval_cases m'' <;> exact bw_le_11 (by decide) (by decide)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨11, 1, by norm_num, by decide, by decide⟩)
  · apply BWins.move (m := 12) (m' := 3) (⟨2, 2, by norm_num, by decide, by decide⟩ : BMove 12 3) (by decide)
    · intro m'' ⟨h₁, h₂⟩
      have hb : m'' ≤ 9 := le_trans h₂ (by decide)
      omega
    · intro m'' ⟨h₁, h₂⟩
      have hb : m'' ≤ 9 := le_trans h₂ (by decide)
      interval_cases m'' <;> exact bw_le_11 (by decide) (by decide)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨13, 1, by norm_num, by decide, by decide⟩)
  · apply BWins.move (m := 14) (m' := 2) (⟨7, 1, by norm_num, by decide, by decide⟩ : BMove 14 2) (by decide)
    · intro m'' ⟨h₁, h₂⟩
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      omega
    · intro m'' ⟨h₁, h₂⟩
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      interval_cases m'' <;> exact bw_le_11 (by decide) (by decide)
  · apply BWins.move (m := 15) (m' := 3) (⟨5, 1, by norm_num, by decide, by decide⟩ : BMove 15 3) (by decide)
    · intro m'' ⟨h₁, h₂⟩
      have hb : m'' ≤ 9 := le_trans h₂ (by decide)
      omega
    · intro m'' ⟨h₁, h₂⟩
      have hb : m'' ≤ 9 := le_trans h₂ (by decide)
      interval_cases m'' <;> exact bw_le_11 (by decide) (by decide)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨2, 4, by norm_num, by decide, by decide⟩)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨17, 1, by norm_num, by decide, by decide⟩)
  · apply BWins.move (m := 18) (m' := 2) (⟨3, 2, by norm_num, by decide, by decide⟩ : BMove 18 2) (by decide)
    · intro m'' ⟨h₁, h₂⟩
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      omega
    · intro m'' ⟨h₁, h₂⟩
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      interval_cases m'' <;> exact bw_le_11 (by decide) (by decide)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨19, 1, by norm_num, by decide, by decide⟩)
  · apply BWins.move (m := 20) (m' := 4) (⟨5, 1, by norm_num, by decide, by decide⟩ : BMove 20 4) (by decide)
    · intro m'' ⟨h₁, h₂⟩
      have hb : m'' ≤ 16 := le_trans h₂ (by decide)
      omega
    · intro m'' ⟨h₁, h₂⟩
      have hb : m'' ≤ 16 := le_trans h₂ (by decide)
      interval_cases m'' <;> exact bw_le_19 (by decide) (by decide)
  · apply BWins.move (m := 21) (m' := 3) (⟨7, 1, by norm_num, by decide, by decide⟩ : BMove 21 3) (by decide)
    · intro m'' ⟨h₁, h₂⟩
      have hb : m'' ≤ 9 := le_trans h₂ (by decide)
      omega
    · intro m'' ⟨h₁, h₂⟩
      have hb : m'' ≤ 9 := le_trans h₂ (by decide)
      interval_cases m'' <;> exact bw_le_11 (by decide) (by decide)
  · apply BWins.move (m := 22) (m' := 2) (⟨11, 1, by norm_num, by decide, by decide⟩ : BMove 22 2) (by decide)
    · intro m'' ⟨h₁, h₂⟩
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      omega
    · intro m'' ⟨h₁, h₂⟩
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      interval_cases m'' <;> exact bw_le_11 (by decide) (by decide)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨23, 1, by norm_num, by decide, by decide⟩)
  · apply BWins.move (m := 24) (m' := 3) (⟨2, 3, by norm_num, by decide, by decide⟩ : BMove 24 3) (by decide)
    · intro m'' ⟨h₁, h₂⟩
      have hb : m'' ≤ 9 := le_trans h₂ (by decide)
      omega
    · intro m'' ⟨h₁, h₂⟩
      have hb : m'' ≤ 9 := le_trans h₂ (by decide)
      interval_cases m'' <;> exact bw_le_11 (by decide) (by decide)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨5, 2, by norm_num, by decide, by decide⟩)
  · apply BWins.move (m := 26) (m' := 2) (⟨13, 1, by norm_num, by decide, by decide⟩ : BMove 26 2) (by decide)
    · intro m'' ⟨h₁, h₂⟩
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      omega
    · intro m'' ⟨h₁, h₂⟩
      have hb : m'' ≤ 4 := le_trans h₂ (by decide)
      interval_cases m'' <;> exact bw_le_11 (by decide) (by decide)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨3, 3, by norm_num, by decide, by decide⟩)
  · apply BWins.move (m := 28) (m' := 4) (⟨7, 1, by norm_num, by decide, by decide⟩ : BMove 28 4) (by decide)
    · intro m'' ⟨h₁, h₂⟩
      have hb : m'' ≤ 16 := le_trans h₂ (by decide)
      omega
    · intro m'' ⟨h₁, h₂⟩
      have hb : m'' ≤ 16 := le_trans h₂ (by decide)
      interval_cases m'' <;> exact bw_le_19 (by decide) (by decide)
  · exact bw_pp ((isPrimePow_nat_iff _).mpr ⟨29, 1, by norm_num, by decide, by decide⟩)

theorem bwinsstart_2 : BWinsStart 2 := by
  intro m ⟨h₁, h₂⟩
  have h4 : m ≤ 4 := le_trans h₂ (by decide)
  exact ⟨by omega, bw_le_11 (by omega) (by omega)⟩

theorem bwinsstart_3 : BWinsStart 3 := by
  intro m ⟨h₁, h₂⟩
  have h9 : m ≤ 9 := le_trans h₂ (by decide)
  exact ⟨by omega, bw_le_11 (by omega) (by omega)⟩

theorem bwinsstart_4 : BWinsStart 4 := by
  intro m ⟨h₁, h₂⟩
  have h16 : m ≤ 16 := le_trans h₂ (by decide)
  exact ⟨by omega, bw_le_19 (by omega) (by omega)⟩

theorem bwinsstart_5 : BWinsStart 5 := by
  intro m ⟨h₁, h₂⟩
  have h25 : m ≤ 25 := le_trans h₂ (by decide)
  exact ⟨by omega, bw_le_29 (by omega) (by omega)⟩

/-! ### B does not win from 30, hence not from `n₀ ∈ {6, 7}` -/

/-- B has no winning strategy from a trap number: A can always restore it. -/
theorem not_bwins_trap {m : ℕ} (h : BWins m) : m ∉ trap := by
  induction h with
  | one m h =>
      intro hm
      exact one_not_mem_bResponses_of_mem_trap hm
        ((bmove_iff_mem_bResponses (ne_zero_of_mem_trap hm)).mp h)
  | move m m' hl hm1 hm2 hm3 IH =>
      intro hm
      have hm' := (bmove_iff_mem_bResponses (ne_zero_of_mem_trap hm)).mp hl
      exact IH m (return_to_trap hm hm') hm

theorem not_bwinsstart_6 : ¬ BWinsStart 6 := by
  intro h
  obtain ⟨h1, h2⟩ := h 30 ⟨by decide, by decide⟩
  exact not_bwins_trap h2 (by decide)

theorem not_bwinsstart_7 : ¬ BWinsStart 7 := by
  intro h
  obtain ⟨h1, h2⟩ := h 30 ⟨by decide, by decide⟩
  exact not_bwins_trap h2 (by decide)

snip end

determine aWinsSet : Set ℕ := {n | 8 ≤ n}

determine bWinsSet : Finset ℕ := {2, 3, 4, 5}

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
