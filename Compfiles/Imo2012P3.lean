/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Combinatorics]
}

/-!
# International Mathematical Olympiad 2012, Problem 3

The liar's guessing game is a game played between two players A and B. The rules
of the game depend on two fixed positive integers k and n which are known to both
players.

At the start of the game A chooses integers x and N with 1 ≤ x ≤ N. Player A
keeps x secret, and truthfully tells N to player B. Player B now tries to obtain
information about x by asking player A questions as follows: each question consists
of B specifying an arbitrary set S of positive integers (possibly one specified in
some previous question), and asking A whether x belongs to S. Player B may ask as
many questions as he wishes. After each question, player A must immediately answer
it with yes or no, but is allowed to lie as many times as she wants; the only
restriction is that, among any k + 1 consecutive answers, at least one answer must
be truthful.

After B has asked as many questions as he wants, he must specify a set X of at
most n positive integers. If x belongs to X, then B wins; otherwise, he loses.
Prove that:

(a) If n ≥ 2^k, then B can guarantee a win.

(b) For all sufficiently large k, there exists an integer n ≥ (1.99)^k such that
B cannot guarantee a win.
-/

namespace Imo2012P3

/-!
## Game infrastructure

Since `1 ≤ x ≤ N` throughout the game, only the intersection of each question
(and of the final set `X`) with `{1, ..., N}` matters, so we model the candidates
as `Fin N`, questions as `Finset (Fin N)`, and answers as `Bool`
(`true` = "yes", `false` = "no"). Answers are indexed by `ℕ`: the `i`-th answer
is given after player B chooses his `i`-th move based on the previous answers.
-/

/-- A move of player B: either stop and guess a set `X`, or ask whether `x ∈ S`. -/
inductive Move (N : ℕ) where
  | guess : Finset (Fin N) → Move N
  | ask : Finset (Fin N) → Move N

/-- A strategy for player B: from the list of answers so far (in chronological
order), decide the next move. -/
structure Strategy (N : ℕ) where
  move : List Bool → Move N

/-- The answer history after `t` questions, when player A answers according
to `ans`. -/
def hist (ans : ℕ → Bool) : ℕ → List Bool
  | 0 => []
  | t + 1 => hist ans t ++ [ans t]

/-- The `i`-th answer is truthful for the secret `x`: it matches the truth value
of `x ∈ S`, where `S` is the question B asked at that point. (If B guessed instead
of asking, the answer is vacuously truthful.) -/
def TruthfulAt {N : ℕ} (σ : Strategy N) (x : Fin N) (ans : ℕ → Bool) (i : ℕ) : Prop :=
  ∀ S : Finset (Fin N), σ.move (hist ans i) = Move.ask S → (x ∈ S ↔ ans i = true)

/-- The play is consistent with the secret `x` up to time `T`: among any `k + 1`
consecutive answers within the first `T`, at least one is truthful. -/
def ConsistentUpTo (k : ℕ) {N : ℕ} (σ : Strategy N) (x : Fin N) (ans : ℕ → Bool)
    (T : ℕ) : Prop :=
  ∀ t : ℕ, t + k + 1 ≤ T → ∃ i : ℕ, t ≤ i ∧ i ≤ t + k ∧ TruthfulAt σ x ans i

/-- Player B's strategy `σ` guarantees a win if
1. against any answer sequence that stays consistent with `x` forever, B eventually
   stops and guesses, and
2. whenever B guesses `X` at time `T` and the answers given so far are consistent
   with `x`, then `x ∈ X` and `X` has at most `n` elements. -/
def GuaranteesWin (k n : ℕ) {N : ℕ} (σ : Strategy N) : Prop :=
  (∀ (x : Fin N) (ans : ℕ → Bool), (∀ T, ConsistentUpTo k σ x ans T) →
    ∃ T X, σ.move (hist ans T) = Move.guess X) ∧
  (∀ (x : Fin N) (ans : ℕ → Bool) (T : ℕ) (X : Finset (Fin N)),
    σ.move (hist ans T) = Move.guess X → ConsistentUpTo k σ x ans T →
    x ∈ X ∧ X.card ≤ n)

/-- Player B can guarantee a win with parameters `k, n` when player A's bound
is `N`. -/
def BobWins (k n N : ℕ) : Prop :=
  ∃ σ : Strategy N, GuaranteesWin k n σ

snip begin

/-!
## Part (b): A's counter-strategy

We follow the standard weight argument. Against any strategy of B, player A
answers so that after the `t`-th answer she can claim "x ∉ B_t", where `B_t` is
whichever of `S_t` and its complement has smaller total weight; the weight of a
candidate is `(1.998) ^ e`, where `e` is the length of its current run of
consecutive lies. The total weight never exceeds `1000 * N`, so once
`1000 * N < (1.998) ^ (k + 1)` no candidate can ever accumulate `k + 1`
consecutive lies. Hence every window of `k + 1` consecutive answers contains,
for every candidate `x`, an answer that is truthful for `x`: the whole answer
sequence is consistent with every `x`, so B's final set of at most `n` elements
cannot contain all `N = n + 1` candidates.
-/

noncomputable section PartB

variable {N : ℕ}

/-- The base of the weights used by A's counter-strategy. -/
def weightBase : ℝ := 1.998

lemma one_lt_weightBase : (1 : ℝ) < weightBase := by norm_num [weightBase]

/-- A's counterplay against `σ`: after each answer she records, for every
candidate, the length of its current run of consecutive lies. Given a question,
she chooses the side with smaller total weight as the "bad set" and answers that
`x` lies on the other side. The third component is the answer given at that step.
(Once B guesses, the streaks are frozen and the answers are junk.) -/
def alicePlay (σ : Strategy N) : ℕ → (Fin N → ℕ) × List Bool × Bool
  | 0 => (fun _ => 0, [], true)
  | t + 1 =>
    match σ.move (alicePlay σ t).2.1 with
    | Move.guess _ => ((alicePlay σ t).1, (alicePlay σ t).2.1 ++ [true], true)
    | Move.ask S =>
      if ∑ x ∈ S, weightBase ^ ((alicePlay σ t).1 x) ≤
          ∑ x ∈ Sᶜ, weightBase ^ ((alicePlay σ t).1 x) then
        (fun x => if x ∈ S then (alicePlay σ t).1 x + 1 else 0,
          (alicePlay σ t).2.1 ++ [false], false)
      else
        (fun x => if x ∉ S then (alicePlay σ t).1 x + 1 else 0,
          (alicePlay σ t).2.1 ++ [true], true)

/-- The streak (length of the current run of consecutive lies) of each candidate
after `t` answers of A's counterplay. -/
def aliceStreak (σ : Strategy N) (t : ℕ) : Fin N → ℕ := (alicePlay σ t).1

/-- The answer history of A's counterplay after `t` steps. -/
def aliceHist (σ : Strategy N) (t : ℕ) : List Bool := (alicePlay σ t).2.1

/-- The `t`-th answer of A's counterplay. -/
def aliceAns (σ : Strategy N) (t : ℕ) : Bool := (alicePlay σ (t + 1)).2.2

/-- The total weight after `t` answers. -/
def aliceWeight (σ : Strategy N) (t : ℕ) : ℝ := ∑ x, weightBase ^ (aliceStreak σ t x)

lemma alicePlay_guess {σ : Strategy N} {t : ℕ} {X : Finset (Fin N)}
    (h : σ.move (aliceHist σ t) = Move.guess X) :
    alicePlay σ (t + 1) = (aliceStreak σ t, aliceHist σ t ++ [true], true) := by
  have h' : σ.move (alicePlay σ t).2.1 = Move.guess X := h
  conv_lhs => rw [alicePlay]
  rw [h']
  rfl

lemma aliceStreak_guess {σ : Strategy N} {t : ℕ} {X : Finset (Fin N)}
    (h : σ.move (aliceHist σ t) = Move.guess X) :
    aliceStreak σ (t + 1) = aliceStreak σ t := by
  rw [show aliceStreak σ (t + 1) = (alicePlay σ (t + 1)).1 from rfl, alicePlay_guess h]

lemma alicePlay_ask {σ : Strategy N} {t : ℕ} {S : Finset (Fin N)}
    (h : σ.move (aliceHist σ t) = Move.ask S) :
    alicePlay σ (t + 1) =
      if ∑ x ∈ S, weightBase ^ (aliceStreak σ t x) ≤
          ∑ x ∈ Sᶜ, weightBase ^ (aliceStreak σ t x)
      then (fun x => if x ∈ S then aliceStreak σ t x + 1 else 0,
            aliceHist σ t ++ [false], false)
      else (fun x => if x ∉ S then aliceStreak σ t x + 1 else 0,
            aliceHist σ t ++ [true], true) := by
  have h' : σ.move (alicePlay σ t).2.1 = Move.ask S := h
  conv_lhs => rw [alicePlay]
  rw [h']
  rfl

lemma aliceHist_succ {σ : Strategy N} (t : ℕ) :
    aliceHist σ (t + 1) = aliceHist σ t ++ [aliceAns σ t] := by
  cases h : σ.move (aliceHist σ t) with
  | guess X =>
      rw [show aliceHist σ (t + 1) = (alicePlay σ (t + 1)).2.1 from rfl,
        show aliceAns σ t = (alicePlay σ (t + 1)).2.2 from rfl, alicePlay_guess h]
  | ask S =>
      rw [show aliceHist σ (t + 1) = (alicePlay σ (t + 1)).2.1 from rfl,
        show aliceAns σ t = (alicePlay σ (t + 1)).2.2 from rfl, alicePlay_ask h]
      split <;> rfl

lemma aliceHist_eq_hist {σ : Strategy N} (t : ℕ) :
    aliceHist σ t = hist (aliceAns σ) t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [hist, ← ih]; exact aliceHist_succ t

/-- At an ask-step, the new total weight is at most `weightBase / 2` times the
old weight plus `N`. -/
lemma aliceWeight_step_ask {σ : Strategy N} {t : ℕ} {S : Finset (Fin N)}
    (h : σ.move (aliceHist σ t) = Move.ask S) :
    aliceWeight σ (t + 1) ≤ weightBase / 2 * aliceWeight σ t + N := by
  have hq : (0 : ℝ) ≤ weightBase := le_of_lt (by norm_num [weightBase])
  set e := aliceStreak σ t
  set W := aliceWeight σ t
  have hsplit : ∑ x ∈ S, weightBase ^ (e x) + ∑ x ∈ Sᶜ, weightBase ^ (e x) = W :=
    Finset.sum_add_sum_compl S _
  have hcard : ∀ T : Finset (Fin N), (T.card : ℝ) ≤ N := by
    intro T
    have h1 : T.card ≤ N := by
      have := Finset.card_le_card (Finset.subset_univ T)
      rwa [Finset.card_univ, Fintype.card_fin] at this
    exact_mod_cast h1
  by_cases hC : ∑ x ∈ S, weightBase ^ (e x) ≤ ∑ x ∈ Sᶜ, weightBase ^ (e x)
  · -- Alice chooses `S` as the bad set: candidates in `S` get their streak increased.
    have hW : ∑ x ∈ S, weightBase ^ (e x) ≤ W / 2 := by linarith
    have hstreak : aliceStreak σ (t + 1) = fun x => if x ∈ S then e x + 1 else 0 := by
      have hp := alicePlay_ask h
      rw [if_pos hC] at hp
      exact congrArg Prod.fst hp
    have hsum : aliceWeight σ (t + 1) =
        ∑ x ∈ S, weightBase ^ (if x ∈ S then e x + 1 else 0) +
        ∑ x ∈ Sᶜ, weightBase ^ (if x ∈ S then e x + 1 else 0) := by
      rw [aliceWeight, hstreak, ← Finset.sum_add_sum_compl S]
    have h1 : ∑ x ∈ S, weightBase ^ (if x ∈ S then e x + 1 else 0)
        = (∑ x ∈ S, weightBase ^ (e x)) * weightBase := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun x hx => by rw [if_pos hx, pow_succ]
    have h2 : ∑ x ∈ Sᶜ, weightBase ^ (if x ∈ S then e x + 1 else 0) = (Sᶜ.card : ℝ) := by
      have hc : ∀ x ∈ Sᶜ, weightBase ^ (if x ∈ S then e x + 1 else 0) = (1 : ℝ) :=
        fun x hx => by rw [if_neg (Finset.mem_compl.mp hx), pow_zero]
      rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hsum, h1, h2]
    have h3 := mul_le_mul_of_nonneg_right hW hq
    have h4 := hcard Sᶜ
    linarith
  · -- Alice chooses `Sᶜ` as the bad set.
    have hW : ∑ x ∈ Sᶜ, weightBase ^ (e x) ≤ W / 2 := by linarith
    have hstreak : aliceStreak σ (t + 1) = fun x => if x ∉ S then e x + 1 else 0 := by
      have hp := alicePlay_ask h
      rw [if_neg hC] at hp
      exact congrArg Prod.fst hp
    have hsum : aliceWeight σ (t + 1) =
        ∑ x ∈ Sᶜ, weightBase ^ (if x ∉ S then e x + 1 else 0) +
        ∑ x ∈ S, weightBase ^ (if x ∉ S then e x + 1 else 0) := by
      rw [aliceWeight, hstreak, ← Finset.sum_add_sum_compl Sᶜ, compl_compl]
    have h1 : ∑ x ∈ Sᶜ, weightBase ^ (if x ∉ S then e x + 1 else 0)
        = (∑ x ∈ Sᶜ, weightBase ^ (e x)) * weightBase := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun x hx => by
        rw [if_pos (Finset.mem_compl.mp hx), pow_succ]
    have h2 : ∑ x ∈ S, weightBase ^ (if x ∉ S then e x + 1 else 0) = (S.card : ℝ) := by
      have hc : ∀ x ∈ S, weightBase ^ (if x ∉ S then e x + 1 else 0) = (1 : ℝ) :=
        fun x hx => by rw [if_neg (not_not_intro hx), pow_zero]
      rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hsum, h1, h2]
    have h3 := mul_le_mul_of_nonneg_right hW hq
    have h4 := hcard S
    linarith

/-- The total weight never exceeds `1000 * N`. -/
lemma aliceWeight_le (σ : Strategy N) (t : ℕ) : aliceWeight σ t ≤ 1000 * N := by
  induction t with
  | zero =>
      have h0 : aliceWeight σ 0 = (N : ℝ) := by
        simp [aliceWeight, aliceStreak, alicePlay]
      rw [h0]
      have hN : (0 : ℝ) ≤ N := by positivity
      linarith
  | succ t ih =>
      cases h : σ.move (aliceHist σ t) with
      | guess X =>
          rw [aliceWeight, aliceStreak_guess h]
          exact_mod_cast ih
      | ask S =>
          have hstep := aliceWeight_step_ask h
          have hq2 : weightBase / 2 * (1000 * (N : ℝ)) + N = 1000 * N := by
            rw [weightBase]; ring
          have hmul := mul_le_mul_of_nonneg_left ih (le_of_lt (by norm_num [weightBase] :
            (0 : ℝ) < weightBase / 2))
          linarith

/-- No candidate's streak ever reaches `k + 1`, once `1000 * N < (1.998) ^ (k+1)`. -/
lemma aliceStreak_le (σ : Strategy N) {k : ℕ} (hWt : 1000 * (N : ℝ) < weightBase ^ (k + 1))
    (x : Fin N) (t : ℕ) :
    aliceStreak σ t x ≤ k := by
  by_contra hcon
  push Not at hcon
  have h1 : weightBase ^ (aliceStreak σ t x) ≤ aliceWeight σ t :=
    Finset.single_le_sum (f := fun x => weightBase ^ (aliceStreak σ t x))
      (fun x _ => pow_nonneg (by norm_num [weightBase]) _) (Finset.mem_univ x)
  have h2 : weightBase ^ (k + 1) ≤ weightBase ^ (aliceStreak σ t x) :=
    pow_le_pow_right₀ (le_of_lt one_lt_weightBase) hcon
  have h3 := aliceWeight_le σ t
  linarith

/-- If A's `i`-th answer is a lie for `x`, then `x`'s streak increases by one. -/
lemma alice_lie_streak {σ : Strategy N} {x : Fin N} {i : ℕ}
    (h : ¬ TruthfulAt σ x (aliceAns σ) i) :
    aliceStreak σ (i + 1) x = aliceStreak σ i x + 1 := by
  rw [TruthfulAt, ← aliceHist_eq_hist] at h
  push Not at h
  obtain ⟨S, hS, htruth⟩ := h
  have hp := alicePlay_ask hS
  have hans : aliceAns σ i = (if ∑ x ∈ S, weightBase ^ (aliceStreak σ i x) ≤
      ∑ x ∈ Sᶜ, weightBase ^ (aliceStreak σ i x) then false else true) := by
    rw [show aliceAns σ i = (alicePlay σ (i + 1)).2.2 from rfl, hp]
    by_cases hC : (∑ x ∈ S, weightBase ^ (aliceStreak σ i x)) ≤
        (∑ x ∈ Sᶜ, weightBase ^ (aliceStreak σ i x)) <;> simp [hC]
  have hstr : aliceStreak σ (i + 1) = (if ∑ x ∈ S, weightBase ^ (aliceStreak σ i x) ≤
      ∑ x ∈ Sᶜ, weightBase ^ (aliceStreak σ i x)
      then (fun x => if x ∈ S then aliceStreak σ i x + 1 else 0)
      else (fun x => if x ∉ S then aliceStreak σ i x + 1 else 0)) := by
    rw [show aliceStreak σ (i + 1) = (alicePlay σ (i + 1)).1 from rfl, hp]
    by_cases hC : (∑ x ∈ S, weightBase ^ (aliceStreak σ i x)) ≤
        (∑ x ∈ Sᶜ, weightBase ^ (aliceStreak σ i x)) <;> simp [hC]
  by_cases hC : (∑ x ∈ S, weightBase ^ (aliceStreak σ i x)) ≤
      (∑ x ∈ Sᶜ, weightBase ^ (aliceStreak σ i x))
  · rw [if_pos hC] at hans hstr
    rw [hstr]
    rcases htruth with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩
    · simp [hx1]
    · rw [hans] at hx2
      exact Bool.noConfusion hx2
  · rw [if_neg hC] at hans hstr
    rw [hstr]
    rcases htruth with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩
    · rw [hans] at hx2
      exact (hx2 rfl).elim
    · simp [hx1]

/-- A's answer sequence is consistent with every candidate at all times: among
any `k + 1` consecutive answers, at least one is truthful for `x`. -/
lemma alice_consistent (σ : Strategy N) {k : ℕ}
    (hWt : 1000 * (N : ℝ) < weightBase ^ (k + 1))
    (x : Fin N) (T : ℕ) :
    ConsistentUpTo k σ x (aliceAns σ) T := by
  intro t _
  by_contra hcon
  push Not at hcon
  have hgrow : ∀ m : ℕ, m ≤ k + 1 →
      aliceStreak σ t x + m ≤ aliceStreak σ (t + m) x := by
    intro m
    induction m with
    | zero => simp
    | succ m ihm =>
      intro hm
      have h1 := hcon (t + m) (by omega) (by omega)
      have h2 := alice_lie_streak h1
      have h3 := ihm (by omega)
      rw [show t + (m + 1) = t + m + 1 by omega, h2]
      omega
  have hbig := hgrow (k + 1) le_rfl
  have hbound := aliceStreak_le σ hWt x (t + (k + 1))
  omega

/-- The weight bound needed at `N = n + 1` where `n = ⌈(1.99) ^ k⌉`. -/
lemma aliceWeightBase_bound {k n : ℕ} (hn : n = ⌈(1.99 : ℝ) ^ k⌉₊)
    (h1000 : 1000 * ((1.99 : ℝ) ^ k + 2) < weightBase ^ (k + 1)) :
    1000 * ((n + 1 : ℕ) : ℝ) < weightBase ^ (k + 1) := by
  have hpos : (0 : ℝ) ≤ 1.99 ^ k := by positivity
  have hceil : (n : ℝ) ≤ 1.99 ^ k + 1 := by
    rw [hn]
    exact (Nat.ceil_lt_add_one hpos).le
  have hN : ((n + 1 : ℕ) : ℝ) ≤ 1.99 ^ k + 2 := by
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by simp
    linarith
  linarith

/-- Under the weight bound, B has no winning strategy: A's counterplay is
consistent with every candidate at all times, so B can never stop with a
correct guess of size at most `n`. -/
lemma not_bobWins {k n : ℕ} (hWt : 1000 * ((n + 1 : ℕ) : ℝ) < weightBase ^ (k + 1))
    (hN : 1 ≤ n + 1) :
    ¬ BobWins k n (n + 1) := by
  rintro ⟨σ, hterm, hwin⟩
  have hcons : ∀ (x : Fin (n + 1)) (T : ℕ), ConsistentUpTo k σ x (aliceAns σ) T :=
    fun x T => alice_consistent σ hWt x T
  obtain ⟨T, X, hT⟩ := hterm ⟨0, hN⟩ (aliceAns σ) (hcons _)
  have hsub : Finset.univ ⊆ X := by
    intro x _
    exact (hwin x (aliceAns σ) T X hT (hcons x T)).1
  have hcardX : X.card ≤ n := (hwin ⟨0, hN⟩ (aliceAns σ) T X hT (hcons _ T)).2
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  omega

/-- Helper: `1 ≤ (1.99) ^ k`. -/
lemma one_le_pow_199 (k : ℕ) : (1 : ℝ) ≤ 1.99 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [pow_succ]
      exact one_le_mul_of_one_le_of_one_le ih (by norm_num)

/-- For all sufficiently large `k`, `1000 * ((1.99) ^ k + 2) < (1.998) ^ (k + 1)`. -/
lemma exists_eventually_large :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, 1000 * ((1.99 : ℝ) ^ k + 2) < weightBase ^ (k + 1) := by
  have h1 : (1 : ℝ) < 1.998 / 1.99 := by norm_num
  have ht := tendsto_pow_atTop_atTop_of_one_lt h1
  have hev : ∀ᶠ k : ℕ in Filter.atTop, (2000 : ℝ) < (1.998 / 1.99) ^ k :=
    ht.eventually_gt_atTop 2000
  rw [Filter.eventually_atTop] at hev
  obtain ⟨k₀, hk₀⟩ := hev
  refine ⟨k₀, fun k hk => ?_⟩
  have hr := hk₀ k hk
  have hpos : (0 : ℝ) < 1.99 ^ k := by positivity
  have hge : (1 : ℝ) ≤ 1.99 ^ k := one_le_pow_199 k
  have key : weightBase ^ (k + 1) = 1.998 * ((1.998 / 1.99) ^ k) * (1.99 ^ k) := by
    rw [weightBase, div_pow, pow_succ]
    field_simp
  rw [key]
  nlinarith [hr, hge, hpos, mul_pos (sub_pos.mpr hr) hpos]

end PartB

/-!
## Part (a): B's elimination strategy

B maintains a pool of candidates (initially all `N` of them). As long as the
pool has more than `2 ^ k` elements, he runs *elimination rounds*:

* probe phase: he asks the singleton question `{s}` (where `s` is a fixed
  candidate outside the image of the bit patterns) until he hears "yes", at
  most `k + 1` times. If all `k + 1` answers are "no", one of them is truthful,
  so `s` is eliminated.
* bit phase: after hearing "yes", he asks `k` questions about the bits of the
  remaining candidates, using an embedding of the `2 ^ k` bit patterns into the
  pool. Among the last `k + 1` answers (the "yes" and the `k` bit answers) one
  is truthful, so the unique embedded candidate whose bit pattern is opposite
  to the bit answers is eliminated.

Each round eliminates exactly one candidate in at most `2 k + 1` questions, so
after finitely many questions the pool has at most `2 ^ k ≤ n` elements, and B
guesses it. The true `x` is never eliminated, since every eliminated candidate
has `k + 1` consecutive answers that are all lies for it.
-/

noncomputable section PartA

variable {k N : ℕ}

/-- Bob's phase within the current elimination round: either probing with the
singleton question (`j` consecutive "no" answers so far), or asking the bit
questions after a "yes" (the probe phase took `j` answers, and `bs` are the
bit answers so far). -/
inductive BobPhase where
  | probe (j : ℕ) : BobPhase
  | bits (j : ℕ) (bs : List Bool) : BobPhase

/-- Bob's state: his current candidate pool together with the progress in the
current elimination round. -/
structure BobState (N : ℕ) where
  pool : Finset (Fin N)
  phase : BobPhase

lemma bobState_ext_iff {s : BobState N} {P : Finset (Fin N)} {ph : BobPhase} :
    s = ⟨P, ph⟩ ↔ s.pool = P ∧ s.phase = ph := by
  constructor
  · intro h
    rw [h]
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    cases s
    simp_all

/-- The number of answers given so far in the current round. -/
def BobPhase.answers : BobPhase → ℕ
  | probe j => j
  | bits j bs => j + bs.length

/-- An embedding of the `2 ^ k` bit patterns into the pool. -/
noncomputable def bobEmbedding (P : Finset (Fin N)) (h : 2 ^ k ≤ P.card) :
    (Fin k → Bool) ↪ P :=
  let hcard : Fintype.card (Fin k → Bool) = 2 ^ k := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  ((Fintype.equivFin (Fin k → Bool)).trans (finCongr hcard)).toEmbedding.trans
    ((Fin.castLEEmb h).trans (P.orderIsoOfFin rfl).toOrderEmbedding.toEmbedding)

lemma bobEmbedding_mem (P : Finset (Fin N)) (h : 2 ^ k ≤ P.card) (p : Fin k → Bool) :
    (bobEmbedding P h p : Fin N) ∈ P :=
  (bobEmbedding P h p).2

/-- There is an element of the pool outside the image of the bit patterns. -/
lemma exists_special (P : Finset (Fin N)) (h : 2 ^ k + 1 ≤ P.card) :
    ∃ s ∈ P, ∀ p : Fin k → Bool, (bobEmbedding P (by omega) p : Fin N) ≠ s := by
  have h1 : 2 ^ k ≤ P.card := by omega
  have hcard : (Finset.univ.image (fun p : Fin k → Bool =>
      (bobEmbedding P h1 p : Fin N))).card < P.card := by
    rw [Finset.card_image_of_injective _
      (fun a b hab => (bobEmbedding P h1).injective (Subtype.coe_injective hab)),
      Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    omega
  by_contra hcon
  push Not at hcon
  have hsub : P ⊆ Finset.univ.image (fun p : Fin k → Bool =>
      (bobEmbedding P h1 p : Fin N)) := by
    intro s hs
    obtain ⟨p, hp⟩ := hcon s hs
    exact Finset.mem_image.mpr ⟨p, Finset.mem_univ p, hp⟩
  have hle := Finset.card_le_card hsub
  omega

/-- The distinguished candidate asked about in the probe phase: an element of
the pool outside the image of the bit patterns. -/
noncomputable def bobSpecial (P : Finset (Fin N)) (h : 2 ^ k + 1 ≤ P.card) : Fin N :=
  (exists_special P h).choose

lemma bobSpecial_mem (P : Finset (Fin N)) (h : 2 ^ k + 1 ≤ P.card) : bobSpecial P h ∈ P :=
  (exists_special P h).choose_spec.1

lemma bobSpecial_ne_embedding (P : Finset (Fin N)) (h : 2 ^ k + 1 ≤ P.card)
    (p : Fin k → Bool) :
    (bobEmbedding P (by omega) p : Fin N) ≠ bobSpecial P h :=
  (exists_special P h).choose_spec.2 p

lemma bobSpecial_congr {P Q : Finset (Fin N)} (hPQ : P = Q) (hP : 2 ^ k + 1 ≤ P.card) :
    bobSpecial P hP = bobSpecial Q (hPQ ▸ hP) := by
  subst hPQ
  rfl

lemma bobEmbedding_congr {P Q : Finset (Fin N)} (hPQ : P = Q) (hP : 2 ^ k ≤ P.card)
    (p : Fin k → Bool) :
    (bobEmbedding P hP p : Fin N) = (bobEmbedding Q (hPQ ▸ hP) p : Fin N) := by
  subst hPQ
  rfl

/-- The set of candidates whose `i`-th bit is `1`. -/
noncomputable def bitQuestion (P : Finset (Fin N)) (h : 2 ^ k ≤ P.card) (i : Fin k) :
    Finset (Fin N) :=
  (Finset.univ.filter (fun p : Fin k → Bool => p i = true)).image
    (fun p => (bobEmbedding P h p : Fin N))

lemma mem_bitQuestion (P : Finset (Fin N)) (h : 2 ^ k ≤ P.card) (i : Fin k)
    (p : Fin k → Bool) :
    ((bobEmbedding P h p : Fin N) ∈ bitQuestion P h i) ↔ p i = true := by
  constructor
  · intro hm
    rw [bitQuestion, Finset.mem_image] at hm
    obtain ⟨q, hq, hqp⟩ := hm
    rw [Finset.mem_filter] at hq
    have hqp' : q = p := (bobEmbedding P h).injective (Subtype.coe_injective hqp)
    rw [hqp'] at hq
    exact hq.2
  · intro hp
    rw [bitQuestion, Finset.mem_image]
    exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp⟩, rfl⟩

/-- Bob's question in a given phase: the singleton `{special}` when probing,
the `|bs|`-th bit question in the bit phase. -/
noncomputable def bobQuestion (P : Finset (Fin N)) (h : 2 ^ k + 1 ≤ P.card) :
    BobPhase → Finset (Fin N)
  | BobPhase.probe _ => {bobSpecial P h}
  | BobPhase.bits _ bs =>
    if hb : bs.length < k then bitQuestion P (by omega) ⟨bs.length, hb⟩ else ∅

lemma bobQuestion_probe (P : Finset (Fin N)) (h : 2 ^ k + 1 ≤ P.card) (j : ℕ) :
    bobQuestion P h (BobPhase.probe j) = {bobSpecial P h} := rfl

lemma bobQuestion_bits (P : Finset (Fin N)) (h : 2 ^ k + 1 ≤ P.card) (j : ℕ)
    (bs : List Bool) (hb : bs.length < k) :
    bobQuestion P h (BobPhase.bits j bs) = bitQuestion P (by omega) ⟨bs.length, hb⟩ := by
  unfold bobQuestion
  exact dif_pos hb

/-- One round-step of Bob's state machine, in the case `2 ^ k < P.card`. -/
noncomputable def bobStepPhase (P : Finset (Fin N)) (h : 2 ^ k + 1 ≤ P.card)
    (ph : BobPhase) (a : Bool) : BobState N :=
  match ph with
  | BobPhase.probe j =>
    match a with
    | true => ⟨P, BobPhase.bits (j + 1) []⟩
    | false =>
      if j = k then ⟨P.erase (bobSpecial P h), BobPhase.probe 0⟩
      else ⟨P, BobPhase.probe (j + 1)⟩
  | BobPhase.bits j bs =>
    let bs' := bs ++ [a]
    if hb : bs'.length = k then
      ⟨P.erase (bobEmbedding P (by omega)
        (fun i : Fin k => !(bs'.get ⟨i, hb ▸ i.2⟩)) : Fin N), BobPhase.probe 0⟩
    else ⟨P, BobPhase.bits j bs'⟩

/-- One step of Bob's state machine. If the pool is already small enough, the
state is frozen. -/
noncomputable def bobStep (k : ℕ) (s : BobState N) (a : Bool) : BobState N :=
  if h : s.pool.card ≤ 2 ^ k then s
  else bobStepPhase (k := k) s.pool (by omega) s.phase a

/-- Bob's winning strategy for part (a). -/
noncomputable def bobStrategy (k : ℕ) : Strategy N where
  move hist :=
    let s := hist.foldl (bobStep k) ⟨Finset.univ, BobPhase.probe 0⟩
    if h : s.pool.card ≤ 2 ^ k then Move.guess s.pool
    else Move.ask (bobQuestion (k := k) s.pool (by omega) s.phase)

/-- Bob's state after processing the first `t` answers. -/
def bobStateOf (N k : ℕ) (ans : ℕ → Bool) (t : ℕ) : BobState N :=
  (hist ans t).foldl (bobStep k) ⟨Finset.univ, BobPhase.probe 0⟩

lemma bobStateOf_zero (ans : ℕ → Bool) :
    bobStateOf N k ans 0 = ⟨Finset.univ, BobPhase.probe 0⟩ := rfl

lemma bobStateOf_succ (ans : ℕ → Bool) (t : ℕ) :
    bobStateOf N k ans (t + 1) = bobStep k (bobStateOf N k ans t) (ans t) := by
  show (hist ans t ++ [ans t]).foldl (bobStep k) ⟨Finset.univ, BobPhase.probe 0⟩ = _
  rw [List.foldl_append]
  rfl

lemma bobStep_frozen (s : BobState N) (h : s.pool.card ≤ 2 ^ k) (a : Bool) :
    bobStep k s a = s := by
  unfold bobStep
  exact dif_pos h

lemma bobStep_active (s : BobState N) (h : ¬ s.pool.card ≤ 2 ^ k) (a : Bool) :
    bobStep k s a = bobStepPhase (k := k) s.pool (by omega) s.phase a := by
  unfold bobStep
  exact dif_neg h

lemma bobStepPhase_probe_true (P : Finset (Fin N)) (h : 2 ^ k + 1 ≤ P.card) (j : ℕ) :
    bobStepPhase P h (BobPhase.probe j) true = ⟨P, BobPhase.bits (j + 1) []⟩ := rfl

lemma bobStepPhase_probe_false_eq (P : Finset (Fin N)) (h : 2 ^ k + 1 ≤ P.card) (j : ℕ)
    (hj : j = k) :
    bobStepPhase P h (BobPhase.probe j) false =
      ⟨P.erase (bobSpecial P h), BobPhase.probe 0⟩ := by
  show ((if j = k then ⟨P.erase (bobSpecial P h), BobPhase.probe 0⟩
    else ⟨P, BobPhase.probe (j + 1)⟩) : BobState N) = _
  rw [if_pos hj]

lemma bobStepPhase_probe_false_lt (P : Finset (Fin N)) (h : 2 ^ k + 1 ≤ P.card) (j : ℕ)
    (hj : j ≠ k) :
    bobStepPhase P h (BobPhase.probe j) false = ⟨P, BobPhase.probe (j + 1)⟩ := by
  show ((if j = k then ⟨P.erase (bobSpecial P h), BobPhase.probe 0⟩
    else ⟨P, BobPhase.probe (j + 1)⟩) : BobState N) = _
  rw [if_neg hj]

lemma bobStepPhase_bits_complete (P : Finset (Fin N)) (h : 2 ^ k + 1 ≤ P.card) (j : ℕ)
    (bs : List Bool) (a : Bool) (hb : (bs ++ [a]).length = k) :
    bobStepPhase P h (BobPhase.bits j bs) a =
      ⟨P.erase (bobEmbedding P (by omega)
        (fun i : Fin k => !((bs ++ [a]).get ⟨i, hb ▸ i.2⟩)) : Fin N), BobPhase.probe 0⟩ := by
  unfold bobStepPhase
  dsimp only
  rw [dif_pos hb]

lemma bobStepPhase_bits_cont (P : Finset (Fin N)) (h : 2 ^ k + 1 ≤ P.card) (j : ℕ)
    (bs : List Bool) (a : Bool) (hb : (bs ++ [a]).length ≠ k) :
    bobStepPhase P h (BobPhase.bits j bs) a = ⟨P, BobPhase.bits j (bs ++ [a])⟩ := by
  unfold bobStepPhase
  dsimp only
  rw [dif_neg hb]

lemma bobStrategy_move_guess {ans : ℕ → Bool} {t : ℕ}
    (h : (bobStateOf N k ans t).pool.card ≤ 2 ^ k) :
    (bobStrategy k).move (hist ans t) = Move.guess (bobStateOf N k ans t).pool := by
  have h' : ((hist ans t).foldl (bobStep k) ⟨Finset.univ, BobPhase.probe 0⟩).pool.card
      ≤ 2 ^ k := h
  show (let s := (hist ans t).foldl (bobStep k) ⟨Finset.univ, BobPhase.probe 0⟩
    if h' : s.pool.card ≤ 2 ^ k then Move.guess s.pool
    else Move.ask (bobQuestion s.pool _ s.phase)) = _
  dsimp only
  exact dif_pos h'

lemma bobStrategy_move_ask {ans : ℕ → Bool} {t : ℕ}
    (h : ¬ (bobStateOf N k ans t).pool.card ≤ 2 ^ k) :
    (bobStrategy k).move (hist ans t) =
      Move.ask (bobQuestion (k := k) (bobStateOf N k ans t).pool (by omega)
        (bobStateOf N k ans t).phase) := by
  have h' : ¬ ((hist ans t).foldl (bobStep k) ⟨Finset.univ, BobPhase.probe 0⟩).pool.card
      ≤ 2 ^ k := h
  show (let s := (hist ans t).foldl (bobStep k) ⟨Finset.univ, BobPhase.probe 0⟩
    if h' : s.pool.card ≤ 2 ^ k then Move.guess s.pool
    else Move.ask (bobQuestion s.pool _ s.phase)) = _
  dsimp only
  exact dif_neg h'

lemma bobStrategy_move_ask_probe {ans : ℕ → Bool} {t : ℕ} {j : ℕ}
    (hstate : (bobStateOf N k ans t).phase = BobPhase.probe j)
    (hcard : ¬ (bobStateOf N k ans t).pool.card ≤ 2 ^ k)
    (h : 2 ^ k + 1 ≤ (bobStateOf N k ans t).pool.card) :
    (bobStrategy k).move (hist ans t) =
      Move.ask {bobSpecial (k := k) (bobStateOf N k ans t).pool h} := by
  rw [bobStrategy_move_ask hcard, hstate, bobQuestion_probe]

lemma bobStrategy_move_ask_bits {ans : ℕ → Bool} {t : ℕ} {j : ℕ} {bs : List Bool}
    (hstate : (bobStateOf N k ans t).phase = BobPhase.bits j bs)
    (hcard : ¬ (bobStateOf N k ans t).pool.card ≤ 2 ^ k)
    (h : 2 ^ k ≤ (bobStateOf N k ans t).pool.card)
    (m : ℕ) (hm : bs.length = m) (hbs : m < k) :
    (bobStrategy k).move (hist ans t) =
      Move.ask (bitQuestion (k := k) (bobStateOf N k ans t).pool h ⟨m, hbs⟩) := by
  have hbs' : bs.length < k := by rw [hm]; exact hbs
  rw [bobStrategy_move_ask hcard, hstate, bobQuestion_bits _ _ _ _ hbs']
  rw [show (⟨bs.length, hbs'⟩ : Fin k) = ⟨m, hbs⟩ from Fin.ext hm]


lemma bob_answers_le (ans : ℕ → Bool) (t : ℕ) :
    (bobStateOf N k ans t).phase.answers ≤ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [bobStateOf_succ]
    by_cases hfr : (bobStateOf N k ans t).pool.card ≤ 2 ^ k
    · rw [bobStep_frozen _ hfr _]
      exact le_trans ih (Nat.le_succ t)
    · rw [bobStep_active _ hfr _]
      cases hph : (bobStateOf N k ans t).phase with
      | probe j =>
        rw [hph] at ih
        change j ≤ t at ih
        cases hat : ans t with
        | true =>
          rw [bobStepPhase_probe_true]
          show j + 1 ≤ t + 1
          omega
        | false =>
          by_cases hjk : j = k
          · rw [bobStepPhase_probe_false_eq _ _ _ hjk]
            exact Nat.zero_le _
          · rw [bobStepPhase_probe_false_lt _ _ _ hjk]
            show j + 1 ≤ t + 1
            omega
      | bits j bs =>
        rw [hph] at ih
        change j + bs.length ≤ t at ih
        by_cases hlen : (bs ++ [ans t]).length = k
        · rw [bobStepPhase_bits_complete _ _ _ _ _ hlen]
          exact Nat.zero_le _
        · rw [bobStepPhase_bits_cont _ _ _ _ _ hlen]
          show j + (bs ++ [ans t]).length ≤ t + 1
          rw [List.length_append]
          simp
          omega

lemma bob_phase_inv (hk : 1 ≤ k) (ans : ℕ → Bool) (t : ℕ) :
    (match (bobStateOf N k ans t).phase with
    | BobPhase.probe j => j ≤ k
    | BobPhase.bits j bs => 1 ≤ j ∧ j ≤ k + 1 ∧ bs.length < k) := by
  induction t with
  | zero => exact Nat.zero_le k
  | succ t ih =>
    rw [bobStateOf_succ]
    by_cases hfr : (bobStateOf N k ans t).pool.card ≤ 2 ^ k
    · rw [bobStep_frozen _ hfr _]; exact ih
    · rw [bobStep_active _ hfr _]
      cases hph : (bobStateOf N k ans t).phase with
      | probe j =>
        rw [hph] at ih
        have hj : j ≤ k := ih
        cases hat : ans t with
        | true =>
          rw [bobStepPhase_probe_true]
          show 1 ≤ j + 1 ∧ j + 1 ≤ k + 1 ∧ ([] : List Bool).length < k
          exact ⟨by omega, by omega, by simp; omega⟩
        | false =>
          by_cases hjk : j = k
          · rw [bobStepPhase_probe_false_eq _ _ _ hjk]
            show (0 : ℕ) ≤ k
            exact Nat.zero_le k
          · rw [bobStepPhase_probe_false_lt _ _ _ hjk]
            show j + 1 ≤ k
            omega
      | bits j bs =>
        rw [hph] at ih
        obtain ⟨hj1, hj2, hbl⟩ := ih
        by_cases hlen : (bs ++ [ans t]).length = k
        · rw [bobStepPhase_bits_complete _ _ _ _ _ hlen]
          show (0 : ℕ) ≤ k
          exact Nat.zero_le k
        · rw [bobStepPhase_bits_cont _ _ _ _ _ hlen]
          show 1 ≤ j ∧ j ≤ k + 1 ∧ (bs ++ [ans t]).length < k
          refine ⟨hj1, hj2, ?_⟩
          rw [List.length_append] at hlen ⊢
          simp at hlen ⊢
          omega

/-- Backward step, probe phase with `j ≥ 1`. -/
lemma bob_backward_probe {ans : ℕ → Bool} {t : ℕ} {P : Finset (Fin N)} {j : ℕ}
    (h : bobStateOf N k ans (t + 1) = ⟨P, BobPhase.probe j⟩)
    (hcard : ¬ P.card ≤ 2 ^ k) (hj : 1 ≤ j) :
    bobStateOf N k ans t = ⟨P, BobPhase.probe (j - 1)⟩ ∧ ans t = false := by
  have hstep : bobStep k (bobStateOf N k ans t) (ans t) = ⟨P, BobPhase.probe j⟩ := by
    rw [← bobStateOf_succ (N := N) (k := k) ans t]; exact h
  by_cases hfr : (bobStateOf N k ans t).pool.card ≤ 2 ^ k
  · rw [bobStep_frozen _ hfr _] at hstep
    rw [hstep] at hfr
    exact absurd hfr hcard
  · rw [bobStep_active _ hfr _] at hstep
    cases hph : (bobStateOf N k ans t).phase with
    | probe j' =>
      rw [hph] at hstep
      cases hat : ans t with
      | true =>
        rw [hat] at hstep
        rw [bobStepPhase_probe_true] at hstep
        cases hstep
      | false =>
        rw [hat] at hstep
        by_cases hjk : j' = k
        · rw [bobStepPhase_probe_false_eq _ _ _ hjk] at hstep
          cases hstep
          omega
        · rw [bobStepPhase_probe_false_lt _ _ _ hjk] at hstep
          cases hstep
          refine ⟨?_, rfl⟩
          rw [show BobPhase.probe (j' + 1 - 1) = BobPhase.probe j' from rfl,
            bobState_ext_iff]
          exact ⟨rfl, hph⟩
    | bits j' bs' =>
      rw [hph] at hstep
      by_cases hlen : (bs' ++ [ans t]).length = k
      · rw [bobStepPhase_bits_complete _ _ _ _ _ hlen] at hstep
        cases hstep
        omega
      · rw [bobStepPhase_bits_cont _ _ _ _ _ hlen] at hstep
        cases hstep

/-- Backward step, bit phase with no bit answers yet. -/
lemma bob_backward_bits_nil {ans : ℕ → Bool} {t : ℕ} {P : Finset (Fin N)} {j : ℕ}
    (h : bobStateOf N k ans (t + 1) = ⟨P, BobPhase.bits j []⟩)
    (hcard : ¬ P.card ≤ 2 ^ k) :
    bobStateOf N k ans t = ⟨P, BobPhase.probe (j - 1)⟩ ∧ ans t = true := by
  have hstep : bobStep k (bobStateOf N k ans t) (ans t) = ⟨P, BobPhase.bits j []⟩ := by
    rw [← bobStateOf_succ (N := N) (k := k) ans t]; exact h
  by_cases hfr : (bobStateOf N k ans t).pool.card ≤ 2 ^ k
  · rw [bobStep_frozen _ hfr _] at hstep
    rw [hstep] at hfr
    exact absurd hfr hcard
  · rw [bobStep_active _ hfr _] at hstep
    cases hph : (bobStateOf N k ans t).phase with
    | probe j' =>
      rw [hph] at hstep
      cases hat : ans t with
      | true =>
        rw [hat] at hstep
        rw [bobStepPhase_probe_true] at hstep
        cases hstep
        refine ⟨?_, rfl⟩
        rw [show BobPhase.probe (j' + 1 - 1) = BobPhase.probe j' from rfl,
          bobState_ext_iff]
        exact ⟨rfl, hph⟩
      | false =>
        rw [hat] at hstep
        by_cases hjk : j' = k
        · rw [bobStepPhase_probe_false_eq _ _ _ hjk] at hstep
          cases hstep
        · rw [bobStepPhase_probe_false_lt _ _ _ hjk] at hstep
          cases hstep
    | bits j' bs' =>
      rw [hph] at hstep
      by_cases hlen : (bs' ++ [ans t]).length = k
      · rw [bobStepPhase_bits_complete _ _ _ _ _ hlen] at hstep
        cases hstep
      · rw [bobStepPhase_bits_cont _ _ _ _ _ hlen] at hstep
        simp only [BobState.mk.injEq, BobPhase.bits.injEq] at hstep
        obtain ⟨_, _, hbs⟩ := hstep
        have hl := congrArg List.length hbs
        simp [List.length_append] at hl

/-- Backward step, bit phase with at least one bit answer. -/
lemma bob_backward_bits_snoc {ans : ℕ → Bool} {t : ℕ} {P : Finset (Fin N)} {j : ℕ}
    {bs : List Bool} {b : Bool}
    (h : bobStateOf N k ans (t + 1) = ⟨P, BobPhase.bits j (bs ++ [b])⟩)
    (hcard : ¬ P.card ≤ 2 ^ k) :
    bobStateOf N k ans t = ⟨P, BobPhase.bits j bs⟩ ∧ ans t = b := by
  have hstep : bobStep k (bobStateOf N k ans t) (ans t) = ⟨P, BobPhase.bits j (bs ++ [b])⟩ := by
    rw [← bobStateOf_succ (N := N) (k := k) ans t]; exact h
  by_cases hfr : (bobStateOf N k ans t).pool.card ≤ 2 ^ k
  · rw [bobStep_frozen _ hfr _] at hstep
    rw [hstep] at hfr
    exact absurd hfr hcard
  · rw [bobStep_active _ hfr _] at hstep
    cases hph : (bobStateOf N k ans t).phase with
    | probe j' =>
      rw [hph] at hstep
      cases hat : ans t with
      | true =>
        rw [hat] at hstep
        rw [bobStepPhase_probe_true] at hstep
        simp only [BobState.mk.injEq, BobPhase.bits.injEq] at hstep
        obtain ⟨_, _, hbs⟩ := hstep
        have hl := congrArg List.length hbs
        simp [List.length_append] at hl
      | false =>
        rw [hat] at hstep
        by_cases hjk : j' = k
        · rw [bobStepPhase_probe_false_eq _ _ _ hjk] at hstep
          cases hstep
        · rw [bobStepPhase_probe_false_lt _ _ _ hjk] at hstep
          cases hstep
    | bits j' bs' =>
      rw [hph] at hstep
      by_cases hlen : (bs' ++ [ans t]).length = k
      · rw [bobStepPhase_bits_complete _ _ _ _ _ hlen] at hstep
        cases hstep
      · rw [bobStepPhase_bits_cont _ _ _ _ _ hlen] at hstep
        simp only [BobState.mk.injEq, BobPhase.bits.injEq] at hstep
        obtain ⟨hP, hj, hbs⟩ := hstep
        subst hP hj
        have hlen2 : bs'.length = bs.length := by
          have hl := congrArg List.length hbs
          simp [List.length_append] at hl
          omega
        obtain ⟨hbs', hans⟩ := List.append_inj hbs hlen2
        subst hbs'
        refine ⟨?_, by simpa using hans⟩
        rw [bobState_ext_iff]
        exact ⟨rfl, hph⟩

/-- Iterated backward step through a probe phase. -/
lemma bob_backward_probe_chain {ans : ℕ → Bool} {t : ℕ} {P : Finset (Fin N)} {j i : ℕ}
    (h : bobStateOf N k ans t = ⟨P, BobPhase.probe j⟩)
    (hcard : ¬ P.card ≤ 2 ^ k) (hi : i ≤ j) (ht : j ≤ t) :
    bobStateOf N k ans (t - i) = ⟨P, BobPhase.probe (j - i)⟩ ∧
      (1 ≤ i → ans (t - i) = false) := by
  induction i with
  | zero => exact ⟨by simpa using h, fun hi0 => absurd hi0 (by omega)⟩
  | succ i ih =>
    have h1 := ih (by omega)
    have ht1 : t - i = t - (i + 1) + 1 := by omega
    have h2 := bob_backward_probe (t := t - (i + 1)) (by rw [← ht1]; exact h1.1) hcard (by omega)
    have e : j - (i + 1) = j - i - 1 := by omega
    rw [e]
    exact ⟨h2.1, fun _ => h2.2⟩

/-- Iterated backward step through a bit phase. -/
lemma bob_backward_bits_chain {ans : ℕ → Bool} {t : ℕ} {P : Finset (Fin N)} {j : ℕ}
    {bs : List Bool} {i : ℕ}
    (h : bobStateOf N k ans t = ⟨P, BobPhase.bits j bs⟩)
    (hcard : ¬ P.card ≤ 2 ^ k) (hi : i ≤ bs.length) (ht : bs.length + 1 ≤ t + 1) :
    bobStateOf N k ans (t - i) = ⟨P, BobPhase.bits j (bs.take (bs.length - i))⟩ ∧
      ((hi1 : 1 ≤ i) → ans (t - i) = bs[bs.length - i]'(by omega)) := by
  induction i with
  | zero =>
    refine ⟨?_, fun hi0 => absurd hi0 (by omega)⟩
    simpa using h
  | succ i ih =>
    have h1 := ih (by omega)
    set m := bs.length - (i + 1) with hm
    have hm1 : bs.length - i = m + 1 := by omega
    have htake : bs.take (bs.length - i) = bs.take m ++ [bs[m]'(by omega)] := by
      rw [hm1, List.take_add_one]
      rw [List.getElem?_eq_getElem (show m < bs.length by omega)]
      rfl
    have ht1 : t - i = t - (i + 1) + 1 := by omega
    have h2 := bob_backward_bits_snoc (t := t - (i + 1)) (bs := bs.take m)
      (b := bs[m]'(by omega)) (by rw [← ht1, h1.1, htake]) hcard
    exact ⟨h2.1, fun _ => h2.2⟩


/-- The termination measure: while the pool has more than `2 ^ k` elements,
`t` is bounded by `(2k+1) * (eliminated so far) + (answers in current round)`. -/
lemma bob_measure (hk : 1 ≤ k) (ans : ℕ → Bool) (t : ℕ)
    (hcard : ¬ (bobStateOf N k ans t).pool.card ≤ 2 ^ k) :
    t ≤ (2 * k + 1) * (N - (bobStateOf N k ans t).pool.card) +
      (bobStateOf N k ans t).phase.answers := by
  induction t with
  | zero =>
    simp [bobStateOf_zero] at hcard ⊢
  | succ t ih =>
    rw [bobStateOf_succ] at hcard ⊢
    by_cases hfr : (bobStateOf N k ans t).pool.card ≤ 2 ^ k
    · rw [bobStep_frozen _ hfr _] at hcard
      exact absurd hfr hcard
    · have hih := ih hfr
      rw [bobStep_active _ hfr _]
      cases hph : (bobStateOf N k ans t).phase with
      | probe j =>
        rw [hph] at hih
        change t ≤ (2 * k + 1) * (N - (bobStateOf N k ans t).pool.card) + j at hih
        cases hat : ans t with
        | true =>
          rw [bobStepPhase_probe_true]
          show t + 1 ≤ (2 * k + 1) * (N - (bobStateOf N k ans t).pool.card) + (j + 1)
          omega
        | false =>
          by_cases hjk : j = k
          · rw [bobStepPhase_probe_false_eq _ _ _ hjk]
            have hmem := bobSpecial_mem (k := k) (bobStateOf N k ans t).pool (by omega)
            have hce : ((bobStateOf N k ans t).pool.erase (bobSpecial _ _)).card =
                (bobStateOf N k ans t).pool.card - 1 := Finset.card_erase_of_mem hmem
            rw [hce]
            have hc : (bobStateOf N k ans t).pool.card ≤ N := by
              have h2 := Finset.card_le_card (Finset.subset_univ (bobStateOf N k ans t).pool)
              rwa [Finset.card_univ, Fintype.card_fin] at h2
            have hc1 : 1 ≤ (bobStateOf N k ans t).pool.card :=
              Finset.card_pos.mpr ⟨_, hmem⟩
            have e1 : N - ((bobStateOf N k ans t).pool.card - 1) =
                N - (bobStateOf N k ans t).pool.card + 1 := by omega
            have e2 : (2 * k + 1) * (N - (bobStateOf N k ans t).pool.card + 1) =
                (2 * k + 1) * (N - (bobStateOf N k ans t).pool.card) + (2 * k + 1) := by
              rw [Nat.mul_add, Nat.mul_one]
            rw [e1, e2]
            show t + 1 ≤ (2 * k + 1) * (N - (bobStateOf N k ans t).pool.card) + (2 * k + 1) + 0
            omega
          · rw [bobStepPhase_probe_false_lt _ _ _ hjk]
            show t + 1 ≤ (2 * k + 1) * (N - (bobStateOf N k ans t).pool.card) + (j + 1)
            omega
      | bits j bs =>
        rw [hph] at hih
        change t ≤ (2 * k + 1) * (N - (bobStateOf N k ans t).pool.card) + (j + bs.length) at hih
        have hinv := bob_phase_inv (N := N) (k := k) hk ans t
        rw [hph] at hinv
        obtain ⟨hj1, hj2, hbl⟩ := hinv
        by_cases hlen : (bs ++ [ans t]).length = k
        · rw [bobStepPhase_bits_complete _ _ _ _ _ hlen]
          have hmem : ((bobEmbedding (k := k) (bobStateOf N k ans t).pool (by omega)
              (fun i : Fin k => !((bs ++ [ans t]).get ⟨i, hlen ▸ i.2⟩)) : Fin N)) ∈
              (bobStateOf N k ans t).pool := bobEmbedding_mem _ _ _
          have hce : ((bobStateOf N k ans t).pool.erase _).card =
              (bobStateOf N k ans t).pool.card - 1 := Finset.card_erase_of_mem hmem
          rw [hce]
          have hc : (bobStateOf N k ans t).pool.card ≤ N := by
            have h2 := Finset.card_le_card (Finset.subset_univ (bobStateOf N k ans t).pool)
            rwa [Finset.card_univ, Fintype.card_fin] at h2
          have hc1 : 1 ≤ (bobStateOf N k ans t).pool.card := Finset.card_pos.mpr ⟨_, hmem⟩
          have e1 : N - ((bobStateOf N k ans t).pool.card - 1) =
              N - (bobStateOf N k ans t).pool.card + 1 := by omega
          have e2 : (2 * k + 1) * (N - (bobStateOf N k ans t).pool.card + 1) =
              (2 * k + 1) * (N - (bobStateOf N k ans t).pool.card) + (2 * k + 1) := by
            rw [Nat.mul_add, Nat.mul_one]
          rw [e1, e2]
          have hblen : bs.length = k - 1 := by
            rw [List.length_append] at hlen
            simp at hlen
            omega
          show t + 1 ≤ (2 * k + 1) * (N - (bobStateOf N k ans t).pool.card) + (2 * k + 1) + 0
          omega
        · rw [bobStepPhase_bits_cont _ _ _ _ _ hlen]
          show t + 1 ≤ (2 * k + 1) * (N - (bobStateOf N k ans t).pool.card) +
            (j + (bs ++ [ans t]).length)
          rw [List.length_append]
          simp
          omega

/-- B's strategy always stops: the pool shrinks by one every `2k + 1` answers. -/
lemma bob_terminates (hk : 1 ≤ k) (ans : ℕ → Bool) :
    ∃ T X, (bobStrategy (N := N) k).move (hist ans T) = Move.guess X := by
  by_contra hnever
  push Not at hnever
  have hcard : ∀ t, ¬ (bobStateOf N k ans t).pool.card ≤ 2 ^ k := by
    intro t ht
    exact hnever t _ (bobStrategy_move_guess ht)
  have hbound : ∀ t, t ≤ (2 * k + 1) * (N - 2 ^ k - 1) + 2 * k := by
    intro t
    have hm := bob_measure (N := N) (k := k) hk ans t (hcard t)
    have hc : (bobStateOf N k ans t).pool.card ≤ N := by
      have h2 := Finset.card_le_card (Finset.subset_univ (bobStateOf N k ans t).pool)
      rwa [Finset.card_univ, Fintype.card_fin] at h2
    have hpa : (bobStateOf N k ans t).phase.answers ≤ 2 * k := by
      have hinv := bob_phase_inv (N := N) (k := k) hk ans t
      cases hph : (bobStateOf N k ans t).phase with
      | probe j =>
        have hj : j ≤ k := by rw [hph] at hinv; exact hinv
        show j ≤ 2 * k
        omega
      | bits j bs =>
        rw [hph] at hinv
        obtain ⟨hj1, hj2, hbl⟩ := hinv
        show j + bs.length ≤ 2 * k
        omega
    have h1 : (2 * k + 1) * (N - (bobStateOf N k ans t).pool.card) ≤
        (2 * k + 1) * (N - 2 ^ k - 1) := by
      have h2 : N - (bobStateOf N k ans t).pool.card ≤ N - 2 ^ k - 1 := by
        have h3 := hcard t
        omega
      gcongr
    omega
  have hcontra := hbound ((2 * k + 1) * (N - 2 ^ k - 1) + 2 * k + 1)
  omega


/-- The pool invariant: if the answers are consistent with `x` up to time `t`,
then `x` is still in Bob's pool. -/
lemma bob_mem_pool (hk : 1 ≤ k) {x : Fin N} {ans : ℕ → Bool} {t : ℕ}
    (hcons : ConsistentUpTo k (bobStrategy k) x ans t) :
    x ∈ (bobStateOf N k ans t).pool := by
  induction t with
  | zero => exact Finset.mem_univ x
  | succ t ih =>
    have hcons' : ConsistentUpTo k (bobStrategy k) x ans t :=
      fun s hs => hcons s (by omega)
    have hx := ih hcons'
    rw [bobStateOf_succ]
    by_cases hfr : (bobStateOf N k ans t).pool.card ≤ 2 ^ k
    · rw [bobStep_frozen _ hfr _]
      exact hx
    · rw [bobStep_active _ hfr _]
      cases hph : (bobStateOf N k ans t).phase with
      | probe j =>
        cases hat : ans t with
        | true =>
          rw [bobStepPhase_probe_true]
          exact hx
        | false =>
          by_cases hjk : j = k
          · -- probe round completes: eliminate `special`; show `x ≠ special`.
            rw [bobStepPhase_probe_false_eq _ _ _ hjk]
            rw [Finset.mem_erase]
            refine ⟨?_, hx⟩
            intro hxs
            have htk : j ≤ t := by
              have h1 := bob_answers_le (N := N) (k := k) ans t
              rw [hph] at h1
              change j ≤ t at h1
              exact h1
            obtain ⟨i, hi1, hi2, hti⟩ := hcons (t - k) (by omega)
            obtain ⟨j', hj'⟩ : ∃ j', j' = t - i := ⟨t - i, rfl⟩
            have hij : i = t - j' := by omega
            have hj'b : j' ≤ k := by omega
            have hchain := bob_backward_probe_chain (bobState_ext_iff.mpr ⟨rfl, hph⟩)
              hfr (i := j') (by omega) htk
            obtain ⟨hstate, hans⟩ := hchain
            have hpool : (bobStateOf N k ans (t - j')).pool = (bobStateOf N k ans t).pool :=
              (bobState_ext_iff.mp hstate).1
            have hphase : (bobStateOf N k ans (t - j')).phase =
                BobPhase.probe (j - j') := (bobState_ext_iff.mp hstate).2
            have hfr' : ¬ (bobStateOf N k ans (t - j')).pool.card ≤ 2 ^ k := by
              rw [hpool]
              exact hfr
            have hcardP : 2 ^ k + 1 ≤ (bobStateOf N k ans (t - j')).pool.card := by omega
            have hmi : (bobStrategy k).move (hist ans i) =
                Move.ask {bobSpecial (k := k) (bobStateOf N k ans (t - j')).pool hcardP} := by
              rw [hij]
              exact bobStrategy_move_ask_probe hphase hfr' hcardP
            have hspeq := bobSpecial_congr hpool hcardP
            rw [hspeq] at hmi
            have htf := hti _ hmi
            have hansi : ans i = false := by
              by_cases hj0 : j' = 0
              · rw [hij, hj0]
                simp only [Nat.sub_zero]
                exact hat
              · rw [hij]
                exact hans (by omega)
            have hxs' : x = bobSpecial (k := k) (bobStateOf N k ans t).pool (hpool ▸ hcardP) :=
              hxs
            rw [hxs', hansi] at htf
            simp at htf
          · rw [bobStepPhase_probe_false_lt _ _ _ hjk]
            exact hx
      | bits j bs =>
        by_cases hlen : (bs ++ [ans t]).length = k
        · -- bit round completes: eliminate the embedded opposite pattern.
          rw [bobStepPhase_bits_complete _ _ _ _ _ hlen]
          rw [Finset.mem_erase]
          refine ⟨?_, hx⟩
          intro hxe
          have hbl : k = bs.length + 1 := by
            rw [List.length_append] at hlen
            simpa using hlen.symm
          have htk : k ≤ t := by
            have h1 := bob_answers_le (N := N) (k := k) ans t
            rw [hph] at h1
            change j + bs.length ≤ t at h1
            have h2 := bob_phase_inv (N := N) (k := k) hk ans t
            rw [hph] at h2
            obtain ⟨hj1, -, -⟩ := h2
            omega
          have hchain : ∀ i (hii : i ≤ bs.length),
              bobStateOf N k ans (t - i) = ⟨(bobStateOf N k ans t).pool,
                BobPhase.bits j (bs.take (bs.length - i))⟩ ∧
              ((hi1 : 1 ≤ i) → ans (t - i) = bs[bs.length - i]'(by omega)) :=
            fun i hii => bob_backward_bits_chain (bobState_ext_iff.mpr ⟨rfl, hph⟩)
              hfr hii (by omega)
          obtain ⟨i, hi1, hi2, hti⟩ := hcons (t - k) (by omega)
          obtain ⟨j', hj'⟩ : ∃ j', j' = t - i := ⟨t - i, rfl⟩
          have hij : i = t - j' := by omega
          have hj'b : j' ≤ k := by omega
          rcases (by omega : j' ≤ k - 1 ∨ j' = k) with hjb | hjk
          · -- a bit position (this also covers `j' = 0`, i.e. the last question)
            obtain ⟨hstate, hans⟩ := hchain j' (by omega)
            have hpool : (bobStateOf N k ans (t - j')).pool = (bobStateOf N k ans t).pool :=
              (bobState_ext_iff.mp hstate).1
            have hphase : (bobStateOf N k ans (t - j')).phase =
                BobPhase.bits j (bs.take (bs.length - j')) := (bobState_ext_iff.mp hstate).2
            have hfr' : ¬ (bobStateOf N k ans (t - j')).pool.card ≤ 2 ^ k := by
              rw [hpool]
              exact hfr
            have hcardP : 2 ^ k ≤ (bobStateOf N k ans (t - j')).pool.card := by omega
            have hbsl' : bs.length - j' < k := by omega
            have hlen' : (bs.take (bs.length - j')).length = bs.length - j' := by
              rw [List.length_take, min_eq_left (by omega)]
            have hmi : (bobStrategy k).move (hist ans i) =
                Move.ask (bitQuestion (k := k) (bobStateOf N k ans (t - j')).pool hcardP
                  ⟨bs.length - j', hbsl'⟩) := by
              rw [hij]
              exact bobStrategy_move_ask_bits hphase hfr' hcardP _ hlen' hbsl'
            have htf := hti _ hmi
            have hxe' : x = (bobEmbedding (k := k) (bobStateOf N k ans (t - j')).pool hcardP
                (fun i : Fin k => !((bs ++ [ans t]).get ⟨i, hlen ▸ i.2⟩)) : Fin N) := by
              subst hxe
              exact bobEmbedding_congr hpool.symm _ _
            rw [hxe', mem_bitQuestion] at htf
            have hget : (bs ++ [ans t]).get ⟨bs.length - j', hlen ▸ hbsl'⟩ = ans i := by
              rw [List.get_eq_getElem]
              by_cases hj0 : j' = 0
              · subst hj0
                have e : (bs ++ [ans t])[bs.length]'(by omega) = ans t := by
                  rw [List.getElem_append_right (le_refl _)]
                  exact List.getElem_singleton (by omega)
                have ei : ans t = ans i := by rw [hij]; rfl
                exact e.trans ei
              · rw [List.getElem_append_left (show bs.length - j' < bs.length by omega)]
                have hans' := hans (by omega)
                have ei : ans (t - j') = ans i := by rw [hij]
                exact hans'.symm.trans ei
            change (Bool.not ((bs ++ [ans t]).get ⟨bs.length - j', hlen ▸ hbsl'⟩) = true ↔
              ans i = true) at htf
            rw [hget] at htf
            cases ha : ans i <;> simp [ha] at htf
          · -- the probe "yes" position
            rw [hjk] at hij
            have hchn := hchain (k - 1) (by omega)
            have hnil : bobStateOf N k ans (t - k + 1) =
                ⟨(bobStateOf N k ans t).pool, BobPhase.bits j []⟩ := by
              have h1 : t - (k - 1) = t - k + 1 := by omega
              have h2 : bs.take (bs.length - (k - 1)) = ([] : List Bool) := by
                have hz : bs.length - (k - 1) = 0 := by omega
                rw [hz]
                simp
              rw [← h1, hchn.1, h2]
            obtain ⟨hprobe, hansyes⟩ := bob_backward_bits_nil (t := t - k) hnil hfr
            have hpool : (bobStateOf N k ans (t - k)).pool = (bobStateOf N k ans t).pool :=
              (bobState_ext_iff.mp hprobe).1
            have hphase : (bobStateOf N k ans (t - k)).phase = BobPhase.probe (j - 1) :=
              (bobState_ext_iff.mp hprobe).2
            have hfr' : ¬ (bobStateOf N k ans (t - k)).pool.card ≤ 2 ^ k := by
              rw [hpool]
              exact hfr
            have hcardP : 2 ^ k + 1 ≤ (bobStateOf N k ans (t - k)).pool.card := by omega
            have hcardP₂ : 2 ^ k ≤ (bobStateOf N k ans (t - k)).pool.card := by omega
            have hmi : (bobStrategy k).move (hist ans i) =
                Move.ask {bobSpecial (k := k) (bobStateOf N k ans (t - k)).pool hcardP} := by
              rw [hij]
              exact bobStrategy_move_ask_probe hphase hfr' hcardP
            have hspeq := bobSpecial_congr hpool hcardP
            rw [hspeq] at hmi
            have htf := hti _ hmi
            have hansi : ans i = true := by rw [hij]; exact hansyes
            rw [hansi] at htf
            have hmem := htf.mpr rfl
            have hxe' : x = (bobEmbedding (k := k) (bobStateOf N k ans (t - k)).pool hcardP₂
                (fun i : Fin k => !((bs ++ [ans t]).get ⟨i, hlen ▸ i.2⟩)) : Fin N) := by
              subst hxe
              exact bobEmbedding_congr hpool.symm _ _
            have hne : (bobEmbedding (k := k) (bobStateOf N k ans (t - k)).pool hcardP₂
                (fun i : Fin k => !((bs ++ [ans t]).get ⟨i, hlen ▸ i.2⟩)) : Fin N) ≠
                bobSpecial (k := k) (bobStateOf N k ans (t - k)).pool hcardP :=
              bobSpecial_ne_embedding _ hcardP _
            have hne' := hspeq ▸ hne
            rw [hxe'] at hmem
            exact hne' (Finset.mem_singleton.mp hmem)
        · rw [bobStepPhase_bits_cont _ _ _ _ _ hlen]
          exact hx

/-- B's strategy guarantees a win when `n ≥ 2 ^ k`. -/
lemma bob_guaranteesWin (n : ℕ) (hk : 1 ≤ k) (hn : 2 ^ k ≤ n) :
    GuaranteesWin k n (bobStrategy (N := N) k) := by
  constructor
  · intro x ans _
    exact bob_terminates (N := N) (k := k) hk ans
  · intro x ans T X hguess hcons
    by_cases hT : (bobStateOf N k ans T).pool.card ≤ 2 ^ k
    · rw [bobStrategy_move_guess hT] at hguess
      have hXX := Move.guess.inj hguess
      rw [← hXX]
      exact ⟨bob_mem_pool (N := N) (k := k) hk hcons, le_trans hT hn⟩
    · rw [bobStrategy_move_ask hT] at hguess
      cases hguess

end PartA

snip end

problem imo2012_p3_part_a {k n : ℕ} (hk : 1 ≤ k) (hn : 2 ^ k ≤ n) (N : ℕ) :
    BobWins k n N :=
  ⟨bobStrategy (N := N) k, bob_guaranteesWin (N := N) (k := k) (n := n) hk hn⟩

problem imo2012_p3_part_b :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, ∃ n : ℕ, (1.99 : ℝ) ^ k ≤ (n : ℝ) ∧
      ¬ BobWins k n (n + 1) := by
  obtain ⟨k₀, hk₀⟩ := exists_eventually_large
  refine ⟨k₀, fun k hk => ⟨⌈(1.99 : ℝ) ^ k⌉₊, Nat.le_ceil _, not_bobWins ?_ ?_⟩⟩
  · exact aliceWeightBase_bound rfl (hk₀ k hk)
  · omega

end Imo2012P3
