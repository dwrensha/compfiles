/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib

import ProblemExtraction

problem_file {
  problemImportedFrom :=
    "https://github.com/jsm28/IMOLean/blob/main/IMO/IMO2025P5.lean"
}

/-!
# International Mathematical Olympiad 2025, Problem 5

Alice and Bazza are playing the *inekoalaty game*, a two-player game
whose rules depend on a positive number λ known to both players. On
the nth turn of the game (starting with n = 1) the following happens:

 * If n is odd, Alice chooses a nonnegative real number xₙ such that

                    x₁ + x₂ + ... + xₙ ≤ λn

 * If n is even, Bazza chooses a nonnegative real number xₙ such that

                   x₁² + x₂² + .. + xₙ² ≤ n.

If a player cannot choose a suitable n, the game ends and the other
player wins. If the game goes forever, neither player wins. All
chosen numbers are known to both players.

Determine all values of λ for which Alice has a winning strategy
and all those for which Bazza has a winning strategy.
-/

namespace Imo2025P5

/-- Whether all the numbers chosen are valid. -/
def ValidSeq (c : ℝ) {n : ℕ} (x : Fin n → ℝ) : Prop := (∀ i : Fin n, 0 ≤ x i) ∧
  (∀ i : Fin n, Even (i : ℕ) → (∑ j ≤ i, x j) ≤ c * ((i : ℕ) + 1)) ∧
  (∀ i : Fin n, Odd (i : ℕ) → (∑ j ≤ i, (x j) ^ 2) ≤ ((i : ℕ) + 1))

/-- Whether a sequence of numbers chosen is a win for the given player (expressed as the 0-based
numbers of that player's moves, mod 2): the other player makes the first invalid move. -/
def Wins (c : ℝ) (p : ℕ) {n : ℕ} (x : Fin n → ℝ) : Prop := ∃ i : Fin n, (i : ℕ) % 2 ≠ p ∧
  IsLeast {j : Fin n | ¬ ValidSeq c (Fin.take ((j : ℕ) + 1) (by omega) x)} i

/-- A strategy for a given player gives a choice of number in every position, with the convention
that invalid moves lose and the strategy's choices are ignored in cases where it is not that
player's turn, a previous move was invalid or the sequence of previous moves is not possible
under the strategy. -/
abbrev Strategy : Type := ⦃k : ℕ⦄ → (Fin k → ℝ) → ℝ

/-- Playing a strategy, k turns, against a given sequence of opponent moves (possibly not
valid). -/
def Strategy.play (s : Strategy) (p : ℕ) (opponentMoves : ℕ → ℝ) : (k : ℕ) → Fin k → ℝ
| 0 => Fin.elim0
| k + 1 => Fin.snoc (s.play p opponentMoves k)
    (if k % 2 = p then s (s.play p opponentMoves k) else opponentMoves k)

/-- Whether a strategy wins for the given player, against all possible opponent moves. -/
def Strategy.Winning (s : Strategy) (c : ℝ) (p : ℕ) : Prop :=
  ∀ opponentMoves : ℕ → ℝ, ∃ k : ℕ, Wins c p (s.play p opponentMoves k)

/-- The answer to be determined. -/
determine answer : Set ℝ × Set ℝ :=
  ({c : ℝ | Real.sqrt 2 / 2 < c}, {c : ℝ | c < Real.sqrt 2 / 2})

snip begin

/-
The solution formalized here follows the writeup in Evan Chen's notes
https://web.evanchen.cc/exams/IMO-2025-notes.pdf .

Alice has a winning strategy exactly when λ > √2/2, and Bazza has one
exactly when λ < √2/2 (when λ = √2/2 the game can go on forever).

* If λ < √2/2 (or λ ≤ 0), Bazza plays "greedily": he always chooses
  the largest number allowed, making the sum of squares after his move
  at index 2k+1 exactly 2k+2.  Each pair of moves (a, b) then satisfies
  a² + b² = 2 and hence a + b ≥ √2, so the sum after 2k moves is at
  least k√2.  Since k√2 > λ(2k+1) for large k, Alice eventually cannot
  move; moreover her slack λ(2k+1) - k√2 ≤ √2/2 stays too small to ever
  break Bazza's quadratic budget.

* If λ > √2/2, Alice plays 0 until a suitable large even index N, at
  which point her unspent linear budget λ(N+1) - (sum of Bazza's moves)
  ≥ λ(N+1) - √2·(N/2) has grown linearly, in particular larger than
  √(N+2), and she spends all of it, making the sum of squares exceed
  N+2 so that Bazza cannot move.  (The bound on Bazza's contribution is
  Cauchy-Schwarz: his N/2 moves have squares summing to at most N.)

* If λ = √2/2 the two arguments above degenerate: playing all zeros
  keeps Alice alive forever against any Bazza strategy, and greedy play
  keeps Bazza alive forever against any Alice strategy, so neither
  player has a winning strategy.
-/

open Finset

/-- Validity of the move at (0-based) index `j` of the infinite sequence `x`,
as a statement about natural-number-indexed sequences. -/
def ValidAt (c : ℝ) (x : ℕ → ℝ) (j : ℕ) : Prop :=
  0 ≤ x j ∧
    (Even j → ∑ m ∈ range (j + 1), x m ≤ c * ((j : ℝ) + 1)) ∧
    (Odd j → ∑ m ∈ range (j + 1), x m ^ 2 ≤ (j : ℝ) + 1)

lemma sum_Iic_coe (f : ℕ → ℝ) {n : ℕ} (i : Fin n) :
    ∑ j ∈ Finset.Iic i, f (j : ℕ) = ∑ m ∈ range ((i : ℕ) + 1), f m := by
  rw [Nat.range_succ_eq_Iic, ← Fin.map_valEmbedding_Iic, Finset.sum_map]
  rfl

/-- `ValidSeq` for a length-`n` window of an infinite sequence, in terms of `ValidAt`. -/
lemma validSeq_iff (c : ℝ) (x : ℕ → ℝ) (n : ℕ) :
    ValidSeq c (fun i : Fin n => x i) ↔ ∀ j < n, ValidAt c x j := by
  constructor
  · rintro ⟨h0, h1, h2⟩ j hj
    refine ⟨h0 ⟨j, hj⟩, fun he => ?_, fun ho => ?_⟩
    · have := h1 ⟨j, hj⟩ he
      rwa [sum_Iic_coe x ⟨j, hj⟩] at this
    · have := h2 ⟨j, hj⟩ ho
      rwa [sum_Iic_coe (fun m => x m ^ 2) ⟨j, hj⟩] at this
  · intro h
    refine ⟨fun i => (h i i.isLt).1, fun i he => ?_, fun i ho => ?_⟩
    · rw [sum_Iic_coe x i]
      exact (h i i.isLt).2.1 he
    · rw [sum_Iic_coe (fun m => x m ^ 2) i]
      exact (h i i.isLt).2.2 ho

lemma take_coe {n m : ℕ} (h : m ≤ n) (x : ℕ → ℝ) :
    Fin.take m h (fun i : Fin n => x i) = fun i : Fin m => x i := by
  funext i
  simp [Fin.take_apply]

/-- `Wins` for a length-`n` window of an infinite sequence, in terms of `ValidAt`. -/
lemma wins_iff (c : ℝ) (p : ℕ) (x : ℕ → ℝ) (n : ℕ) :
    Wins c p (fun i : Fin n => x i) ↔
      ∃ j < n, j % 2 ≠ p ∧ (∀ m < j, ValidAt c x m) ∧ ¬ ValidAt c x j := by
  unfold Wins
  simp only [take_coe, validSeq_iff]
  constructor
  · rintro ⟨i, hp, hmem, hlb⟩
    have hgood : ∀ m < (i : ℕ), ValidAt c x m := by
      intro m hm
      by_contra hbad
      have hmem' : (⟨m, lt_trans hm i.isLt⟩ : Fin n) ∈
          {j : Fin n | ¬ ∀ m' < (j : ℕ) + 1, ValidAt c x m'} := by
        intro hall
        exact hbad (hall m m.lt_succ_self)
      have h1 := hlb hmem'
      rw [Fin.le_def] at h1
      lia
    refine ⟨(i : ℕ), i.isLt, hp, hgood, fun hv => ?_⟩
    apply hmem
    intro m hm
    rcases Nat.lt_succ_iff_lt_or_eq.mp hm with h' | h'
    · exact hgood m h'
    · exact h' ▸ hv
  · rintro ⟨j, hj, hp, hgood, hbad⟩
    refine ⟨⟨j, hj⟩, hp, fun hall => hbad (hall j j.lt_succ_self), ?_⟩
    rintro b hb
    rw [Fin.le_def]
    by_contra hlt
    apply hb
    intro m hm
    exact hgood m (by lia)

/-- The infinite sequence of moves of a play. -/
def Strategy.playSeq (s : Strategy) (p : ℕ) (om : ℕ → ℝ) (j : ℕ) : ℝ :=
  s.play p om (j + 1) ⟨j, Nat.lt_succ_self j⟩

lemma play_castLE (s : Strategy) (p : ℕ) (om : ℕ → ℝ) :
    ∀ (k j : ℕ) (h : j ≤ k) (i : Fin j), s.play p om k (Fin.castLE h i) = s.play p om j i := by
  intro k
  induction k with
  | zero =>
    intro j h i
    have : j = 0 := by lia
    subst this
    exact i.elim0
  | succ k ih =>
    intro j h i
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h) with h' | h'
    · have h'' : j ≤ k := by lia
      have hcast : Fin.castLE h i = Fin.castSucc (Fin.castLE h'' i) := by
        ext; simp
      rw [hcast]
      simp only [Strategy.play, Fin.snoc_castSucc]
      exact ih j h'' i
    · subst h'
      have : Fin.castLE h i = i := by ext; simp
      rw [this]

lemma play_eq_playSeq (s : Strategy) (p : ℕ) (om : ℕ → ℝ) (k : ℕ) :
    s.play p om k = fun i : Fin k => s.playSeq p om (i : ℕ) := by
  funext i
  have h : (i : ℕ) + 1 ≤ k := i.isLt
  have h2 := play_castLE s p om k ((i : ℕ) + 1) h ⟨(i : ℕ), Nat.lt_succ_self _⟩
  rwa [show Fin.castLE h ⟨(i : ℕ), Nat.lt_succ_self _⟩ = i from Fin.ext rfl] at h2

lemma playSeq_apply (s : Strategy) (p : ℕ) (om : ℕ → ℝ) (j : ℕ) :
    s.playSeq p om j =
      if j % 2 = p then s (fun i : Fin j => s.playSeq p om (i : ℕ)) else om j := by
  have h : s.playSeq p om j = Fin.snoc (α := fun _ => ℝ) (s.play p om j)
      (if j % 2 = p then s (s.play p om j) else om j) (Fin.last j) := rfl
  rw [h, Fin.snoc_last, play_eq_playSeq]

/-- The sequence of moves arising when the player with parity `p` plays the strategy `s` and
the opponent always responds according to `r`. -/
def respSeq (s : Strategy) (p : ℕ) (r : Strategy) : ℕ → ℝ
  | j => if j % 2 = p then s (fun i : Fin j => respSeq s p r (i : ℕ))
         else r (fun i : Fin j => respSeq s p r (i : ℕ))
  termination_by j => j
  decreasing_by all_goals exact i.isLt

lemma play_respSeq (s : Strategy) (p : ℕ) (r : Strategy) (k : ℕ) :
    s.play p (respSeq s p r) k = fun i : Fin k => respSeq s p r (i : ℕ) := by
  induction k with
  | zero =>
    funext i
    exact i.elim0
  | succ k ih =>
    funext i
    simp only [Strategy.play, ih]
    refine Fin.lastCases ?_ ?_ i
    · rw [Fin.snoc_last]
      by_cases hk : k % 2 = p
      · rw [if_pos hk]
        conv_rhs => rw [Fin.val_last, respSeq]
        rw [if_pos hk]
      · rw [if_neg hk]
        rw [Fin.val_last]
    · intro i
      rw [Fin.snoc_castSucc, Fin.val_castSucc]

/-- A first invalid index exists as soon as any invalid index does. -/
lemma exists_first_invalid {c : ℝ} {x : ℕ → ℝ} (hex : ∃ j, ¬ ValidAt c x j) :
    ∃ j, (∀ m < j, ValidAt c x m) ∧ ¬ ValidAt c x j := by
  classical
  exact ⟨Nat.find hex, fun m hm => not_not.mp (Nat.find_min hex hm), Nat.find_spec hex⟩

/-- If `0 ≤ b` and `a ^ 2 ≤ b ^ 2` then `a ≤ b`. -/
lemma le_of_sq_le_sq' {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]

lemma sum_range_two_mul (f : ℕ → ℝ) (k : ℕ) :
    ∑ i ∈ range (2 * k), f i = ∑ i ∈ range k, (f (2 * i) + f (2 * i + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih, show 2 * (k + 1) = 2 * k + 1 + 1 from by ring,
      Finset.sum_range_succ, Finset.sum_range_succ]
    ring

/-- Cauchy-Schwarz bound: if a sequence vanishes at even indices below `2 * k`, is
nonnegative there, and its squares sum to at most `2 * k`, then its sum is at most `√2 * k`. -/
lemma sum_le_sqrt_two_mul (x : ℕ → ℝ) (k : ℕ)
    (h0 : ∀ i < 2 * k, Even i → x i = 0)
    (hQ : ∑ i ∈ range (2 * k), x i ^ 2 ≤ 2 * (k : ℝ)) :
    ∑ i ∈ range (2 * k), x i ≤ Real.sqrt 2 * k := by
  have hsplit : ∑ i ∈ range (2 * k), x i = ∑ i ∈ range k, x (2 * i + 1) := by
    rw [sum_range_two_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [h0 (2 * i) (by lia) (even_two_mul i), zero_add]
  have hsplitQ : ∑ i ∈ range (2 * k), x i ^ 2 = ∑ i ∈ range k, x (2 * i + 1) ^ 2 := by
    rw [sum_range_two_mul (fun i => x i ^ 2)]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [h0 (2 * i) (by lia) (even_two_mul i)]
    ring
  rw [hsplit]
  have hQ' : ∑ i ∈ range k, x (2 * i + 1) ^ 2 ≤ 2 * (k : ℝ) := by
    rwa [← hsplitQ]
  have hcs := sq_sum_le_card_mul_sum_sq (s := range k) (f := fun i => x (2 * i + 1))
  rw [Finset.card_range] at hcs
  apply le_of_sq_le_sq' (by positivity)
  have hsq : (Real.sqrt 2 * k) ^ 2 = 2 * (k : ℝ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [hsq]
  calc (∑ i ∈ range k, x (2 * i + 1)) ^ 2
      ≤ (k : ℝ) * ∑ i ∈ range k, x (2 * i + 1) ^ 2 := hcs
    _ ≤ (k : ℝ) * (2 * (k : ℝ)) := by
        apply mul_le_mul_of_nonneg_left hQ' (by positivity)
    _ = 2 * (k : ℝ) ^ 2 := by ring

/-- If `a, b ≥ 0` and `a² + b² = 2` then `a + b ≥ √2`. -/
lemma sqrt_two_le_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 + b ^ 2 = 2) :
    Real.sqrt 2 ≤ a + b := by
  apply le_of_sq_le_sq' (by positivity)
  rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  nlinarith [mul_nonneg ha hb]

/-! ### Bazza's side: the greedy strategy

Throughout this section, `x` is a sequence of moves in which every odd-indexed move
is the greedy move `√(j + 1 - (sum of squares so far))`. -/

/-- One round of greedy play when `c ≤ √2/2`, assuming the invariant after `2k` moves
and the validity of Alice's move at index `2k`: Alice's move is at most `√2/2`, so Bazza's
greedy reply at index `2k + 1` exists, and the squares of the pair sum to `2`. -/
lemma bazza_step {c : ℝ} {x : ℕ → ℝ} (hc : c ≤ Real.sqrt 2 / 2) {k : ℕ}
    (hb : x (2 * k + 1) =
      Real.sqrt (((2 * k + 1 : ℕ) : ℝ) + 1 - ∑ i ∈ range (2 * k + 1), x i ^ 2))
    (hQ : ∑ i ∈ range (2 * k), x i ^ 2 = 2 * (k : ℝ))
    (hS : Real.sqrt 2 * k ≤ ∑ i ∈ range (2 * k), x i)
    (hv : ValidAt c x (2 * k)) :
    ∑ i ∈ range (2 * k + 1), x i ^ 2 = 2 * (k : ℝ) + x (2 * k) ^ 2 ∧
      0 ≤ x (2 * k + 1) ∧ x (2 * k + 1) ^ 2 = 2 - x (2 * k) ^ 2 := by
  obtain ⟨ha0, haS, -⟩ := hv
  have haS' := haS (even_two_mul k)
  rw [Finset.sum_range_succ] at haS'
  push_cast at haS'
  -- Alice's move `x (2 * k)` is at most `√2 / 2`.
  have hc' : c * (2 * (k : ℝ) + 1) ≤ Real.sqrt 2 / 2 * (2 * (k : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right hc (by positivity)
  have hab : x (2 * k) ≤ Real.sqrt 2 / 2 := by nlinarith
  have ha2 : x (2 * k) ^ 2 ≤ 1 / 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hQ1 : ∑ i ∈ range (2 * k + 1), x i ^ 2 = 2 * (k : ℝ) + x (2 * k) ^ 2 := by
    rw [Finset.sum_range_succ, hQ]
  have harg : ((2 * k + 1 : ℕ) : ℝ) + 1 - ∑ i ∈ range (2 * k + 1), x i ^ 2 =
      2 - x (2 * k) ^ 2 := by
    rw [hQ1]; push_cast; ring
  rw [harg] at hb
  exact ⟨hQ1, hb ▸ Real.sqrt_nonneg _, by rw [hb, Real.sq_sqrt (by linarith)]⟩

/-- Invariant of greedy play when `c ≤ √2/2`: while all moves so far are valid, the sum of
squares after Bazza's move at index `2k - 1` is exactly `2k`, and the plain sum is
at least `√2 * k`. -/
lemma bazza_invariant {c : ℝ} {x : ℕ → ℝ} (hc : c ≤ Real.sqrt 2 / 2)
    (hgreedy : ∀ j, Odd j → x j = Real.sqrt ((j : ℝ) + 1 - ∑ i ∈ range j, x i ^ 2)) :
    ∀ k : ℕ, (∀ m < 2 * k, ValidAt c x m) →
      ∑ i ∈ range (2 * k), x i ^ 2 = 2 * (k : ℝ) ∧
        Real.sqrt 2 * k ≤ ∑ i ∈ range (2 * k), x i := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    intro hvalid
    obtain ⟨hQ, hS⟩ := ih (fun m hm => hvalid m (by lia))
    have hv := hvalid (2 * k) (by lia)
    obtain ⟨hQ1, hbnn, hb2⟩ :=
      bazza_step hc (hgreedy (2 * k + 1) (Nat.odd_iff.mpr (by lia))) hQ hS hv
    have hidx : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
    constructor
    · rw [hidx, Finset.sum_range_succ, hQ1, hb2]
      push_cast
      ring
    · have hpair : Real.sqrt 2 ≤ x (2 * k) + x (2 * k + 1) :=
        sqrt_two_le_add hv.1 hbnn (by rw [hb2]; ring)
      rw [hidx, Finset.sum_range_succ, Finset.sum_range_succ]
      push_cast
      linarith

/-- When `c ≤ √2/2` and Bazza plays greedily, no odd index is ever the first invalid one. -/
lemma bazza_validAt_odd {c : ℝ} {x : ℕ → ℝ} (hc : c ≤ Real.sqrt 2 / 2)
    (hgreedy : ∀ j, Odd j → x j = Real.sqrt ((j : ℝ) + 1 - ∑ i ∈ range j, x i ^ 2)) :
    ∀ j, Odd j → (∀ m < j, ValidAt c x m) → ValidAt c x j := by
  intro j hj hvalid
  obtain ⟨k, rfl⟩ : ∃ k, j = 2 * k + 1 := by
    rw [Nat.odd_iff] at hj
    exact ⟨j / 2, by lia⟩
  obtain ⟨hQ, hS⟩ := bazza_invariant hc hgreedy k (fun m hm => hvalid m (by lia))
  obtain ⟨hQ1, hbnn, hb2⟩ :=
    bazza_step hc (hgreedy (2 * k + 1) (Nat.odd_iff.mpr (by lia))) hQ hS
      (hvalid (2 * k) (by lia))
  refine ⟨hbnn, fun he => ?_, fun _ => ?_⟩
  · exfalso
    rw [Nat.even_iff] at he
    lia
  · rw [Finset.sum_range_succ, hQ1, hb2]
    push_cast
    linarith

/-- Bazza's greedy strategy: spend the entire quadratic budget. -/
noncomputable def bazzaStrategy : Strategy := fun k h => Real.sqrt ((k : ℝ) + 1 - ∑ i, h i ^ 2)

/-- The all-zeros strategy. -/
def zeroStrategy : Strategy := fun _ _ => 0

/-- If `c ≤ √2/2` then Alice has no winning strategy: Bazza survives greedy play forever. -/
lemma alice_not_wins {c : ℝ} (hc : c ≤ Real.sqrt 2 / 2) :
    ¬ ∃ s : Strategy, s.Winning c 0 := by
  rintro ⟨s, hs⟩
  obtain ⟨k, hk⟩ := hs (respSeq s 0 bazzaStrategy)
  rw [play_respSeq, wins_iff] at hk
  obtain ⟨j, _, hjp, hjmin, hjbad⟩ := hk
  have hgreedy : ∀ j', Odd j' → respSeq s 0 bazzaStrategy j' =
      Real.sqrt ((j' : ℝ) + 1 - ∑ i ∈ range j', respSeq s 0 bazzaStrategy i ^ 2) := by
    intro j' hj'
    rw [respSeq, if_neg (by rw [Nat.odd_iff] at hj'; lia)]
    show Real.sqrt _ = _
    rw [Fin.sum_univ_eq_sum_range (fun i => respSeq s 0 bazzaStrategy i ^ 2) j']
  exact hjbad (bazza_validAt_odd hc hgreedy j (Nat.odd_iff.mpr (by lia)) hjmin)

/-- If `c < √2/2` then Bazza's greedy strategy wins. -/
lemma bazza_wins {c : ℝ} (hc : c < Real.sqrt 2 / 2) : ∃ s : Strategy, s.Winning c 1 := by
  refine ⟨bazzaStrategy, fun om => ?_⟩
  set x : ℕ → ℝ := bazzaStrategy.playSeq 1 om with hx
  have hgreedy : ∀ j, Odd j → x j =
      Real.sqrt ((j : ℝ) + 1 - ∑ i ∈ range j, x i ^ 2) := by
    intro j hj
    rw [hx, playSeq_apply, if_pos (Nat.odd_iff.mp hj)]
    show Real.sqrt _ = _
    rw [Fin.sum_univ_eq_sum_range (fun i => bazzaStrategy.playSeq 1 om i ^ 2) j]
  -- Choose k₀ with √2 * k₀ > c * (2 * k₀ + 1).
  have hσ : 0 < Real.sqrt 2 - 2 * c := by linarith
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt (c / (Real.sqrt 2 - 2 * c))
  rw [div_lt_iff₀ hσ] at hk₀
  have hkey : c * (2 * (k₀ : ℝ) + 1) < Real.sqrt 2 * k₀ := by nlinarith
  -- Some index at most 2 * k₀ is invalid.
  have hex : ∃ j, ¬ ValidAt c x j := by
    by_cases hall : ∀ m < 2 * k₀, ValidAt c x m
    · refine ⟨2 * k₀, ?_⟩
      obtain ⟨hQ, hS⟩ := bazza_invariant (le_of_lt hc) hgreedy k₀ hall
      rintro ⟨h0, hsum, -⟩
      have h1 := hsum (even_two_mul k₀)
      rw [Finset.sum_range_succ] at h1
      push_cast at h1
      linarith
    · push Not at hall
      obtain ⟨m, _, hbad⟩ := hall
      exact ⟨m, hbad⟩
  -- The least invalid index is even, so Bazza wins.
  obtain ⟨j₀, hj₀min, hj₀bad⟩ := exists_first_invalid hex
  have hj₀p : j₀ % 2 ≠ 1 := by
    intro hp
    exact hj₀bad (bazza_validAt_odd (le_of_lt hc) hgreedy j₀ (Nat.odd_iff.mpr hp) hj₀min)
  refine ⟨j₀ + 1, ?_⟩
  rw [play_eq_playSeq, ← hx, wins_iff]
  exact ⟨j₀, by lia, hj₀p, hj₀min, hj₀bad⟩

/-! ### Alice's side -/

/-- The partial-sum bound coming from Cauchy-Schwarz, for play in which Alice has played
all zeros so far. -/
lemma zeros_sum_le {c : ℝ} {x : ℕ → ℝ} (t : ℕ)
    (h0 : ∀ i < 2 * t, Even i → x i = 0)
    (hvalid : ∀ m < 2 * t, ValidAt c x m) :
    ∑ i ∈ range (2 * t), x i ≤ Real.sqrt 2 * t := by
  apply sum_le_sqrt_two_mul x t h0
  cases t with
  | zero => simp
  | succ t' =>
    have h := (hvalid (2 * t' + 1) (by lia)).2.2 (Nat.odd_iff.mpr (by lia))
    rw [show 2 * t' + 1 + 1 = 2 * (t' + 1) from by ring] at h
    push_cast at h ⊢
    linarith

/-- If `c ≥ √2/2` and all of Alice's moves up to an even index `2 * t` are `0`, then
her move at `2 * t` is valid. -/
lemma zeros_validAt_even {c : ℝ} {x : ℕ → ℝ} (hc : Real.sqrt 2 / 2 ≤ c) (t : ℕ)
    (h0 : ∀ i ≤ 2 * t, Even i → x i = 0)
    (hvalid : ∀ m < 2 * t, ValidAt c x m) :
    ValidAt c x (2 * t) := by
  have hxt : x (2 * t) = 0 := h0 (2 * t) le_rfl (even_two_mul t)
  have hS := zeros_sum_le t (fun i hi => h0 i (by lia)) hvalid
  refine ⟨le_of_eq hxt.symm, fun _ => ?_, fun ho => ?_⟩
  · rw [Finset.sum_range_succ, hxt, add_zero]
    have h1 : Real.sqrt 2 * t ≤ Real.sqrt 2 / 2 * (2 * (t : ℝ) + 1) := by
      nlinarith [Real.sqrt_nonneg 2]
    have h2 : Real.sqrt 2 / 2 * (2 * (t : ℝ) + 1) ≤ c * (2 * (t : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    push_cast
    linarith
  · exfalso
    rw [Nat.odd_iff] at ho
    lia

/-- If `c ≥ √2/2` then Bazza has no winning strategy: Alice survives forever by
playing all zeros. -/
lemma bazza_not_wins {c : ℝ} (hc : Real.sqrt 2 / 2 ≤ c) :
    ¬ ∃ s : Strategy, s.Winning c 1 := by
  rintro ⟨s, hs⟩
  obtain ⟨k, hk⟩ := hs (respSeq s 1 zeroStrategy)
  rw [play_respSeq, wins_iff] at hk
  obtain ⟨j, _, hjp, hjmin, hjbad⟩ := hk
  have h0 : ∀ i, Even i → respSeq s 1 zeroStrategy i = 0 := by
    intro i hi
    rw [respSeq, if_neg (by rw [Nat.even_iff] at hi; lia)]
    rfl
  obtain ⟨t, rfl⟩ : ∃ t, j = 2 * t := ⟨j / 2, by lia⟩
  exact hjbad (zeros_validAt_even hc t (fun i _ hi => h0 i hi) hjmin)

/-- If `c > √2/2` then Alice wins: she plays zeros until index `N`, then spends her whole
linear budget, which by then exceeds `√(N + 2)`, so Bazza cannot answer. -/
lemma alice_wins {c : ℝ} (hc : Real.sqrt 2 / 2 < c) : ∃ s : Strategy, s.Winning c 0 := by
  have hc0 : 0 < c := lt_trans (by positivity) hc
  have hε : 0 < c - Real.sqrt 2 / 2 := by linarith
  -- Choose M large enough.
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / (c - Real.sqrt 2 / 2) ^ 2 + 2)
  set N : ℕ := 2 * M with hN
  have hM2 : (2 : ℝ) ≤ M := by
    linarith [show (0:ℝ) ≤ 1 / (c - Real.sqrt 2 / 2) ^ 2 by positivity]
  have hMpos : (0 : ℝ) < M := by linarith
  have hε2 : 1 < (c - Real.sqrt 2 / 2) ^ 2 * M := by
    have h' : 1 / (c - Real.sqrt 2 / 2) ^ 2 < M := by linarith
    rw [div_lt_iff₀ (by positivity)] at h'
    linarith
  -- The key inequality: Alice's budget at time N exceeds √(N + 2).
  have hkey : Real.sqrt ((N : ℝ) + 2) < c * ((N : ℝ) + 1) - Real.sqrt 2 * M := by
    have hNc : (N : ℝ) = 2 * (M : ℝ) := by rw [hN]; push_cast; ring
    have hpos : 0 < c + 2 * (c - Real.sqrt 2 / 2) * M := by nlinarith [mul_pos hε hMpos]
    rw [show c * ((N : ℝ) + 1) - Real.sqrt 2 * M = c + 2 * (c - Real.sqrt 2 / 2) * M from
      by rw [hNc]; ring, hNc, Real.sqrt_lt' hpos]
    nlinarith [mul_lt_mul_of_pos_right hε2 hMpos, sq_nonneg c,
      mul_nonneg (mul_nonneg hc0.le hε.le) hMpos.le]
  -- Alice's strategy.
  set s : Strategy := fun k h => if k = N then c * ((N : ℝ) + 1) - ∑ i, h i else 0 with hs
  refine ⟨s, fun om => ?_⟩
  set x : ℕ → ℝ := s.playSeq 0 om with hx
  have hplay : ∀ j, j % 2 = 0 →
      x j = if j = N then c * ((N : ℝ) + 1) - ∑ i ∈ range j, x i else 0 := by
    intro j hj
    rw [hx, playSeq_apply, if_pos hj]
    show (if j = N then c * ((N : ℝ) + 1) - ∑ i : Fin j, s.playSeq 0 om (i : ℕ) else 0) = _
    rw [Fin.sum_univ_eq_sum_range (fun i => s.playSeq 0 om i) j]
  have hxeven : ∀ j, Even j → j ≠ N → x j = 0 := by
    intro j hj hjN
    rw [hplay j (Nat.even_iff.mp hj), if_neg hjN]
  have hNeven : Even N := ⟨M, by lia⟩
  have hxN : x N = c * ((N : ℝ) + 1) - ∑ i ∈ range N, x i := by
    rw [hplay N (Nat.even_iff.mp hNeven), if_pos rfl]
  -- Validity of Alice's moves below N.
  have hvalid_lt : ∀ t, 2 * t < N → (∀ m < 2 * t, ValidAt c x m) → ValidAt c x (2 * t) := by
    intro t ht hvalid
    exact zeros_validAt_even (le_of_lt hc) t
      (fun i hi he => hxeven i he (by lia)) hvalid
  -- Validity of Alice's move at N.
  have hSN : (∀ m < N, ValidAt c x m) → ∑ i ∈ range N, x i ≤ Real.sqrt 2 * M := by
    intro hvalid
    rw [hN]
    exact zeros_sum_le M (fun i hi he => hxeven i he (by lia))
      (fun m hm => hvalid m (by rw [hN]; exact hm))
  have hvalidN : (∀ m < N, ValidAt c x m) → ValidAt c x N := by
    intro hvalid
    have hS := hSN hvalid
    have hxNnn : 0 ≤ x N := by
      rw [hxN]
      nlinarith [Real.sqrt_nonneg ((N : ℝ) + 2)]
    refine ⟨hxNnn, fun _ => ?_, fun ho => ?_⟩
    · rw [Finset.sum_range_succ, hxN]
      linarith
    · exfalso
      have := Nat.even_iff.mp hNeven
      rw [Nat.odd_iff] at ho
      lia
  -- Invalidity at N + 1, if everything before was valid.
  have hinvalidN1 : (∀ m < N + 1, ValidAt c x m) → ¬ ValidAt c x (N + 1) := by
    intro hvalid
    rintro ⟨-, -, hsum⟩
    have hoddN1 : Odd (N + 1) := by
      rw [Nat.odd_iff]
      lia
    have h1 := hsum hoddN1
    have hS := hSN (fun m hm => hvalid m (by lia))
    have hxNbig : Real.sqrt ((N : ℝ) + 2) < x N := by
      rw [hxN]
      linarith
    have hxNsq : (N : ℝ) + 2 < x N ^ 2 := by
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ (N : ℝ) + 2 by positivity),
        Real.sqrt_nonneg ((N : ℝ) + 2)]
    have hterm : x N ^ 2 ≤ ∑ i ∈ range (N + 1 + 1), x i ^ 2 :=
      Finset.single_le_sum (f := fun i => x i ^ 2) (fun i _ => sq_nonneg (x i))
        (Finset.mem_range.mpr (by lia))
    push_cast at h1
    linarith
  -- Locate the first invalid index; it is odd, so Alice wins.
  have hex : ∃ j, ¬ ValidAt c x j := by
    by_cases hall : ∀ m < N + 1, ValidAt c x m
    · exact ⟨N + 1, hinvalidN1 hall⟩
    · push Not at hall
      obtain ⟨m, _, hbad⟩ := hall
      exact ⟨m, hbad⟩
  obtain ⟨j₀, hj₀min, hj₀bad⟩ := exists_first_invalid hex
  have hj₀le : j₀ ≤ N + 1 := by
    by_contra hgt
    exact hinvalidN1 (fun m hm => hj₀min m (by lia)) (hj₀min (N + 1) (by lia))
  have hj₀p : j₀ % 2 ≠ 0 := by
    intro hp
    have hNmod := Nat.even_iff.mp hNeven
    have hj₀N : j₀ ≤ N := by lia
    rcases Nat.lt_or_ge j₀ N with h | h
    · apply hj₀bad
      have ht : j₀ = 2 * (j₀ / 2) := by lia
      rw [ht]
      exact hvalid_lt (j₀ / 2) (by lia) (fun m hm => hj₀min m (by lia))
    · have hjN : j₀ = N := by lia
      apply hj₀bad
      rw [hjN]
      exact hvalidN (fun m hm => hj₀min m (by lia))
  refine ⟨j₀ + 1, ?_⟩
  rw [play_eq_playSeq, ← hx, wins_iff]
  exact ⟨j₀, by lia, hj₀p, hj₀min, hj₀bad⟩

snip end

problem imo2025_p5 :
    ({c : ℝ | ∃ s : Strategy, s.Winning c 0}, {c : ℝ | ∃ s : Strategy, s.Winning c 1}) =
      answer := by
  have h1 : {c : ℝ | ∃ s : Strategy, s.Winning c 0} = {c : ℝ | Real.sqrt 2 / 2 < c} := by
    ext c
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      by_contra hle
      exact alice_not_wins (not_lt.mp hle) h
    · exact alice_wins
  have h2 : {c : ℝ | ∃ s : Strategy, s.Winning c 1} = {c : ℝ | c < Real.sqrt 2 / 2} := by
    ext c
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      by_contra hle
      exact bazza_not_wins (not_lt.mp hle) h
    · exact bazza_wins
  rw [h1, h2]

end Imo2025P5
