/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.DeriveFintype
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 1999, Problem 5

The Y2K Game is played on a 1 × 2000 grid as follows. Two players in turn write either
an S or an O in an empty square. The first player who produces three consecutive boxes
that spell SOS wins. If all boxes are filled without producing SOS then the game is a draw.
Show that the second player has a winning strategy.
-/

namespace Usa1999P5

snip begin

/-! ### Basic definitions -/

/-- The two letters that can be written in a square. -/
inductive Piece | S | O
  deriving DecidableEq, Fintype, Inhabited

/-- The board: square `i` contains `b i` for `i < 2000`; anything outside is irrelevant. -/
abbrev Board := ℕ → Option Piece

/-- Well-formed board: nothing written outside the 2000 squares. -/
def BOK (b : Board) : Prop := ∀ i, 2000 ≤ i → b i = none

/-- The board contains three consecutive squares spelling S O S. -/
def HasSOS (b : Board) : Prop :=
  ∃ i ∈ Finset.range 1998, b i = some Piece.S ∧ b (i + 1) = some Piece.O ∧
    b (i + 2) = some Piece.S

instance (b : Board) : Decidable (HasSOS b) := by
  unfold HasSOS; infer_instance

/-- The player to move can win immediately: some legal move produces SOS. -/
def HasThreat (b : Board) : Prop :=
  ∃ x ∈ Finset.range 2000, ∃ l : Piece, b x = none ∧
    HasSOS (Function.update b x (some l))

instance (b : Board) : Decidable (HasThreat b) := by
  unfold HasThreat; infer_instance

/-- No immediate winning move is available. -/
def ThreatFree (b : Board) : Prop := ¬ HasThreat b

/-- A losing square: an empty square such that playing either letter there
    allows the opponent to win on the following move. -/
def IsLosing (b : Board) (x : ℕ) : Prop :=
  b x = none ∧ ∀ l : Piece, HasThreat (Function.update b x (some l))

instance (b : Board) (x : ℕ) : Decidable (IsLosing b x) := by
  unfold IsLosing; infer_instance

/-- A "trap": the pattern S _ _ S with both middle squares empty.
    Its two middle squares will turn out to be exactly the losing squares. -/
def TrapAt (b : Board) (a : ℕ) : Prop :=
  b a = some Piece.S ∧ b (a + 1) = none ∧ b (a + 2) = none ∧ b (a + 3) = some Piece.S

instance (b : Board) (a : ℕ) : Decidable (TrapAt b a) := by
  unfold TrapAt; infer_instance

/-- The board contains a trap. -/
def HasTrap (b : Board) : Prop := ∃ a ∈ Finset.range 1997, TrapAt b a

instance (b : Board) : Decidable (HasTrap b) := by
  unfold HasTrap; infer_instance

/-- The empty squares of the board. -/
def empties (b : Board) : Finset ℕ := (Finset.range 2000).filter fun i => b i = none

/-- The occupied squares of the board. -/
def letters (b : Board) : Finset ℕ := (Finset.range 2000).filter fun i => b i ≠ none

/-- The losing squares of the board. -/
def losing (b : Board) : Finset ℕ := (Finset.range 2000).filter fun i => IsLosing b i

/-- The left ends of traps on the board. -/
def trapEnds (b : Board) : Finset ℕ := (Finset.range 1997).filter fun a => TrapAt b a

/-- The outcome of a game: first player wins, second player wins, or draw. -/
inductive Outcome | p1 | p2 | draw
  deriving DecidableEq

/-- A strategy chooses a square and a letter given a board. -/
abbrev Strategy := Board → ℕ × Piece

/-- Playing out the game with two strategies; `fuel` bounds the number of moves
    (2001 always suffices). `true` means it is the first player's turn.
    An illegal move (off the board or onto an occupied square) loses immediately. -/
def play : ℕ → Strategy → Strategy → Board → Bool → Outcome
  | 0, _, _, _, _ => .draw
  | fuel + 1, σ₁, σ₂, b, true =>
      if HasSOS b then .p2
      else if empties b = ∅ then .draw
      else if (σ₁ b).1 < 2000 ∧ b (σ₁ b).1 = none
      then play fuel σ₁ σ₂ (Function.update b (σ₁ b).1 (some (σ₁ b).2)) false
      else .p2
  | fuel + 1, σ₁, σ₂, b, false =>
      if HasSOS b then .p1
      else if empties b = ∅ then .draw
      else if (σ₂ b).1 < 2000 ∧ b (σ₂ b).1 = none
      then play fuel σ₁ σ₂ (Function.update b (σ₂ b).1 (some (σ₂ b).2)) true
      else .p1

/-! ### Simple lemmas about `empties`, `letters` and updates -/

lemma mem_empties {b : Board} {x : ℕ} : x ∈ empties b ↔ x < 2000 ∧ b x = none := by
  simp [empties]

lemma mem_letters {b : Board} {x : ℕ} : x ∈ letters b ↔ x < 2000 ∧ b x ≠ none := by
  simp [letters]

lemma letters_update_card {b : Board} {x : ℕ} (hx : x < 2000) (hxe : b x = none) (l : Piece) :
    (letters (Function.update b x (some l))).card = (letters b).card + 1 := by
  have h1 : letters (Function.update b x (some l)) = insert x (letters b) := by
    ext y
    simp only [letters, Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
    by_cases hyx : y = x
    · subst hyx; simp [Function.update_self, hx]
    · simp [hyx]
  have hxn : x ∉ letters b := by
    simp [letters, hxe]
  rw [h1, Finset.card_insert_of_notMem hxn]

lemma empties_update_card {b : Board} {x : ℕ} (hx : x < 2000) (hxe : b x = none) (l : Piece) :
    (empties (Function.update b x (some l))).card = (empties b).card - 1 := by
  have h1 : empties (Function.update b x (some l)) = (empties b).erase x := by
    ext y
    simp only [empties, Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
    by_cases hyx : y = x
    · subst hyx; simp [Function.update_self]
    · simp [hyx]
  have hxm : x ∈ empties b := mem_empties.mpr ⟨hx, hxe⟩
  rw [h1, Finset.card_erase_of_mem hxm]

lemma empties_ne_empty {b : Board} (h : (empties b).card ≠ 0) : empties b ≠ ∅ := by
  intro he; rw [he] at h; simp at h

lemma empties_card_pos {b : Board} (h : empties b ≠ ∅) : 0 < (empties b).card :=
  Finset.card_pos.mpr (Finset.nonempty_of_ne_empty h)

/-- A board with SOS has at least three occupied squares. -/
lemma three_le_card_letters_of_hasSOS {b : Board} (h : HasSOS b) : 3 ≤ (letters b).card := by
  rcases h with ⟨i, hi, h0, h1, h2⟩
  rw [Finset.mem_range] at hi
  have s0 : i ∈ letters b := mem_letters.mpr ⟨by omega, by simp [h0]⟩
  have s1 : i + 1 ∈ letters b := mem_letters.mpr ⟨by omega, by simp [h1]⟩
  have s2 : i + 2 ∈ letters b := mem_letters.mpr ⟨by omega, by simp [h2]⟩
  have sub : {i, i + 1, i + 2} ⊆ letters b := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card sub
  rw [Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp),
    Finset.card_singleton] at this
  exact this

/-- A board with a trap has at least two occupied squares. -/
lemma two_le_card_letters_of_hasTrap {b : Board} (h : HasTrap b) : 2 ≤ (letters b).card := by
  rcases h with ⟨a, ha, h0, -, -, h3⟩
  rw [Finset.mem_range] at ha
  have s0 : a ∈ letters b := mem_letters.mpr ⟨by omega, by simp [h0]⟩
  have s3 : a + 3 ∈ letters b := mem_letters.mpr ⟨by omega, by simp [h3]⟩
  have sub : {a, a + 3} ⊆ letters b := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl <;> assumption
  have := Finset.card_le_card sub
  rw [Finset.card_insert_of_notMem (by simp), Finset.card_singleton] at this
  exact this

/-- On a threat-free board, no move can produce SOS (else that move would have won). -/
lemma not_hasSOS_update_of_threatFree {b : Board} (hTF : ThreatFree b) {x : ℕ}
    (hx : x < 2000) (hxe : b x = none) (l : Piece) :
    ¬ HasSOS (Function.update b x (some l)) :=
  fun hS => hTF ⟨x, Finset.mem_range.mpr hx, l, hxe, hS⟩

lemma bOK_update {b : Board} (hBOK : BOK b) {x : ℕ} (hx : x < 2000) (l : Piece) :
    BOK (Function.update b x (some l)) := by
  intro i hi
  have hix : i ≠ x := by omega
  rw [Function.update_of_ne hix]
  exact hBOK i hi

/-- The shape of any immediate win created by playing letter `l₀` at square `x` of a
    threat-free board. The six alternatives correspond to the opponent's possible
    winning replies; the first two are the replies to an O, the other four to an S. -/
lemma threat_shapes {b : Board} (hTF : ThreatFree b) {x : ℕ}
    (hx : x < 2000) (hxe : b x = none) {l₀ : Piece}
    (h : HasThreat (Function.update b x (some l₀))) :
    (l₀ = Piece.O ∧ 1 ≤ x ∧ b (x - 1) = none ∧ b (x + 1) = some Piece.S) ∨
    (l₀ = Piece.O ∧ 1 ≤ x ∧ b (x + 1) = none ∧ b (x - 1) = some Piece.S) ∨
    (l₀ = Piece.S ∧ b (x + 2) = some Piece.S ∧ b (x + 1) = none) ∨
    (l₀ = Piece.S ∧ 2 ≤ x ∧ b (x - 2) = some Piece.S ∧ b (x - 1) = none) ∨
    (l₀ = Piece.S ∧ 2 ≤ x ∧ b (x - 1) = some Piece.O ∧ b (x - 2) = none) ∨
    (l₀ = Piece.S ∧ b (x + 1) = some Piece.O ∧ b (x + 2) = none) := by
  rcases h with ⟨y, hyr, l, hye, hsos⟩
  rcases hsos with ⟨i, hir, h0, h1, h2⟩
  rw [Finset.mem_range] at hyr hir
  -- The SOS triple must contain the square `y` just played: otherwise the same
  -- triple would already be an SOS after playing `l₀` at `x`, contradicting
  -- threat-freeness.
  have hyT : i = y ∨ i + 1 = y ∨ i + 2 = y := by
    by_contra hcon
    have c0 : i ≠ y := fun hh => hcon (Or.inl hh)
    have c1 : i + 1 ≠ y := fun hh => hcon (Or.inr (Or.inl hh))
    have c2 : i + 2 ≠ y := fun hh => hcon (Or.inr (Or.inr hh))
    rw [Function.update_of_ne c0] at h0
    rw [Function.update_of_ne c1] at h1
    rw [Function.update_of_ne c2] at h2
    exact not_hasSOS_update_of_threatFree hTF hx hxe l₀
      ⟨i, Finset.mem_range.mpr hir, h0, h1, h2⟩
  rcases hyT with rfl | rfl | rfl
  · -- y = i: the letter played at `y` is S.
    rw [Function.update_self] at h0
    have hl : l = Piece.S := Option.some.inj h0
    subst l
    rw [Function.update_of_ne (show i + 1 ≠ i by omega)] at h1
    rw [Function.update_of_ne (show i + 2 ≠ i by omega)] at h2
    by_cases hx1 : x = i + 1
    · -- x = i + 1 forces l₀ = O: first shape.
      have hl₀ : l₀ = Piece.O := by
        rw [← hx1] at h1
        rw [Function.update_self] at h1
        exact Option.some.inj h1
      have e1 : x - 1 = i := by omega
      have e2 : x + 1 = i + 2 := by omega
      have hb1 : b (x - 1) = none := by
        rw [e1]
        rw [Function.update_of_ne (show i ≠ x by omega)] at hye
        exact hye
      have hb2 : b (x + 1) = some Piece.S := by
        rw [e2]
        rw [Function.update_of_ne (show i + 2 ≠ x by omega)] at h2
        exact h2
      exact Or.inl ⟨hl₀, by omega, hb1, hb2⟩
    · by_cases hx2 : x = i + 2
      · -- x = i + 2 forces l₀ = S: fifth shape.
        have hl₀ : l₀ = Piece.S := by
          rw [← hx2] at h2
          rw [Function.update_self] at h2
          exact Option.some.inj h2
        have e1 : x - 1 = i + 1 := by omega
        have e2 : x - 2 = i := by omega
        have hb1 : b (x - 1) = some Piece.O := by
          rw [e1]
          rw [Function.update_of_ne (show i + 1 ≠ x by omega)] at h1
          exact h1
        have hb2 : b (x - 2) = none := by
          rw [e2]
          rw [Function.update_of_ne (show i ≠ x by omega)] at hye
          exact hye
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hl₀, by omega, hb1, hb2⟩))))
      · -- x outside the triple: `y = i` was already a winning move on `b`.
        have hxi : x ≠ i := by
          rintro rfl
          rw [Function.update_self] at hye
          cases hye
        have hbi : b i = none := by
          rw [Function.update_of_ne (show i ≠ x by omega)] at hye
          exact hye
        have hb1 : b (i + 1) = some Piece.O := by
          rw [Function.update_of_ne (show i + 1 ≠ x by omega)] at h1
          exact h1
        have hb2 : b (i + 2) = some Piece.S := by
          rw [Function.update_of_ne (show i + 2 ≠ x by omega)] at h2
          exact h2
        refine absurd ?_ hTF
        refine ⟨i, Finset.mem_range.mpr hyr, Piece.S, hbi, i,
          Finset.mem_range.mpr hir, ?_, ?_, ?_⟩
        · rw [Function.update_self]
        · rw [Function.update_of_ne (show i + 1 ≠ i by omega)]
          exact hb1
        · rw [Function.update_of_ne (show i + 2 ≠ i by omega)]
          exact hb2
  · -- y = i + 1: the letter played at `y` is O.
    rw [Function.update_self] at h1
    have hl : l = Piece.O := Option.some.inj h1
    subst l
    rw [Function.update_of_ne (show i ≠ i + 1 by omega)] at h0
    rw [Function.update_of_ne (show i + 2 ≠ i + 1 by omega)] at h2
    by_cases hx0 : x = i
    · -- x = i forces l₀ = S: third shape.
      have hl₀ : l₀ = Piece.S := by
        rw [← hx0] at h0
        rw [Function.update_self] at h0
        exact Option.some.inj h0
      have e1 : x + 2 = i + 2 := by omega
      have e2 : x + 1 = i + 1 := by omega
      have hb1 : b (x + 2) = some Piece.S := by
        rw [e1]
        rw [Function.update_of_ne (show i + 2 ≠ x by omega)] at h2
        exact h2
      have hb2 : b (x + 1) = none := by
        rw [e2]
        rw [Function.update_of_ne (show i + 1 ≠ x by omega)] at hye
        exact hye
      exact Or.inr (Or.inr (Or.inl ⟨hl₀, hb1, hb2⟩))
    · by_cases hx2 : x = i + 2
      · -- x = i + 2 forces l₀ = S: fourth shape.
        have hl₀ : l₀ = Piece.S := by
          rw [← hx2] at h2
          rw [Function.update_self] at h2
          exact Option.some.inj h2
        have e1 : x - 2 = i := by omega
        have e2 : x - 1 = i + 1 := by omega
        have hb1 : b (x - 2) = some Piece.S := by
          rw [e1]
          rw [Function.update_of_ne (show i ≠ x by omega)] at h0
          exact h0
        have hb2 : b (x - 1) = none := by
          rw [e2]
          rw [Function.update_of_ne (show i + 1 ≠ x by omega)] at hye
          exact hye
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hl₀, by omega, hb1, hb2⟩)))
      · -- x outside the triple: `y = i + 1` was already a winning move on `b`.
        have hxi : x ≠ i + 1 := by
          rintro rfl
          rw [Function.update_self] at hye
          cases hye
        have hbi : b (i + 1) = none := by
          rw [Function.update_of_ne (show i + 1 ≠ x by omega)] at hye
          exact hye
        have hb0 : b i = some Piece.S := by
          rw [Function.update_of_ne (show i ≠ x by omega)] at h0
          exact h0
        have hb2 : b (i + 2) = some Piece.S := by
          rw [Function.update_of_ne (show i + 2 ≠ x by omega)] at h2
          exact h2
        refine absurd ?_ hTF
        refine ⟨i + 1, Finset.mem_range.mpr hyr, Piece.O, hbi, i,
          Finset.mem_range.mpr hir, ?_, ?_, ?_⟩
        · rw [Function.update_of_ne (show i ≠ i + 1 by omega)]
          exact hb0
        · rw [Function.update_self]
        · rw [Function.update_of_ne (show i + 2 ≠ i + 1 by omega)]
          exact hb2
  · -- y = i + 2: the letter played at `y` is S.
    rw [Function.update_self] at h2
    have hl : l = Piece.S := Option.some.inj h2
    subst l
    rw [Function.update_of_ne (show i ≠ i + 2 by omega)] at h0
    rw [Function.update_of_ne (show i + 1 ≠ i + 2 by omega)] at h1
    by_cases hx0 : x = i
    · -- x = i forces l₀ = S: sixth shape.
      have hl₀ : l₀ = Piece.S := by
        rw [← hx0] at h0
        rw [Function.update_self] at h0
        exact Option.some.inj h0
      have e1 : x + 1 = i + 1 := by omega
      have e2 : x + 2 = i + 2 := by omega
      have hb1 : b (x + 1) = some Piece.O := by
        rw [e1]
        rw [Function.update_of_ne (show i + 1 ≠ x by omega)] at h1
        exact h1
      have hb2 : b (x + 2) = none := by
        rw [e2]
        rw [Function.update_of_ne (show i + 2 ≠ x by omega)] at hye
        exact hye
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hl₀, hb1, hb2⟩))))
    · by_cases hx1 : x = i + 1
      · -- x = i + 1 forces l₀ = O: second shape.
        have hl₀ : l₀ = Piece.O := by
          rw [← hx1] at h1
          rw [Function.update_self] at h1
          exact Option.some.inj h1
        have e1 : x + 1 = i + 2 := by omega
        have e2 : x - 1 = i := by omega
        have hb1 : b (x + 1) = none := by
          rw [e1]
          rw [Function.update_of_ne (show i + 2 ≠ x by omega)] at hye
          exact hye
        have hb2 : b (x - 1) = some Piece.S := by
          rw [e2]
          rw [Function.update_of_ne (show i ≠ x by omega)] at h0
          exact h0
        exact Or.inr (Or.inl ⟨hl₀, by omega, hb1, hb2⟩)
      · -- x outside the triple: `y = i + 2` was already a winning move on `b`.
        have hxi : x ≠ i + 2 := by
          rintro rfl
          rw [Function.update_self] at hye
          cases hye
        have hbi : b (i + 2) = none := by
          rw [Function.update_of_ne (show i + 2 ≠ x by omega)] at hye
          exact hye
        have hb0 : b i = some Piece.S := by
          rw [Function.update_of_ne (show i ≠ x by omega)] at h0
          exact h0
        have hb1 : b (i + 1) = some Piece.O := by
          rw [Function.update_of_ne (show i + 1 ≠ x by omega)] at h1
          exact h1
        refine absurd ?_ hTF
        refine ⟨i + 2, Finset.mem_range.mpr hyr, Piece.S, hbi, i,
          Finset.mem_range.mpr hir, ?_, ?_, ?_⟩
        · rw [Function.update_of_ne (show i ≠ i + 2 by omega)]
          exact hb0
        · rw [Function.update_of_ne (show i + 1 ≠ i + 2 by omega)]
          exact hb1
        · rw [Function.update_self]

/-- The middle squares of a trap are losing squares. -/
lemma trap_middle {b : Board} {a : ℕ} (ha : a < 1997) (h : TrapAt b a) :
    IsLosing b (a + 1) ∧ IsLosing b (a + 2) := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  constructor
  · -- IsLosing b (a + 1): play O at a + 1, opponent plays S at a + 2 (triple a..a+2);
    -- play S at a + 1, opponent plays O at a + 2 (triple a+1..a+3).
    refine ⟨h1, fun l => ?_⟩
    cases l with
    | S =>
      refine ⟨a + 2, Finset.mem_range.mpr (by omega), Piece.O, ?_, ?_⟩
      · rw [Function.update_of_ne (by omega : a + 2 ≠ a + 1)]; exact h2
      · refine ⟨a + 1, Finset.mem_range.mpr (by omega), ?_, ?_, ?_⟩
        · rw [Function.update_of_ne (by omega : a + 1 ≠ a + 2), Function.update_self]
        · rw [Function.update_self]
        · rw [Function.update_of_ne (by omega : a + 3 ≠ a + 2),
            Function.update_of_ne (by omega : a + 3 ≠ a + 1)]
          exact h3
    | O =>
      refine ⟨a + 2, Finset.mem_range.mpr (by omega), Piece.S, ?_, ?_⟩
      · rw [Function.update_of_ne (by omega : a + 2 ≠ a + 1)]; exact h2
      · refine ⟨a, Finset.mem_range.mpr (by omega), ?_, ?_, ?_⟩
        · rw [Function.update_of_ne (by omega : a ≠ a + 2),
            Function.update_of_ne (by omega : a ≠ a + 1)]
          exact h0
        · rw [Function.update_of_ne (by omega : a + 1 ≠ a + 2), Function.update_self]
        · rw [Function.update_self]
  · -- IsLosing b (a + 2): play S, opponent plays O at a + 1 (triple a..a+2);
    -- play O, opponent plays S at a + 1 (triple a+1..a+3).
    refine ⟨h2, fun l => ?_⟩
    cases l with
    | S =>
      refine ⟨a + 1, Finset.mem_range.mpr (by omega), Piece.O, ?_, ?_⟩
      · rw [Function.update_of_ne (by omega : a + 1 ≠ a + 2)]; exact h1
      · refine ⟨a, Finset.mem_range.mpr (by omega), ?_, ?_, ?_⟩
        · rw [Function.update_of_ne (by omega : a ≠ a + 1),
            Function.update_of_ne (by omega : a ≠ a + 2)]
          exact h0
        · rw [Function.update_self]
        · rw [Function.update_of_ne (by omega : a + 2 ≠ a + 1), Function.update_self]
    | O =>
      refine ⟨a + 1, Finset.mem_range.mpr (by omega), Piece.S, ?_, ?_⟩
      · rw [Function.update_of_ne (by omega : a + 1 ≠ a + 2)]; exact h1
      · refine ⟨a + 1, Finset.mem_range.mpr (by omega), ?_, ?_, ?_⟩
        · rw [Function.update_self]
        · rw [Function.update_of_ne (by omega : a + 2 ≠ a + 1), Function.update_self]
        · rw [Function.update_of_ne (by omega : a + 3 ≠ a + 1),
            Function.update_of_ne (by omega : a + 3 ≠ a + 2)]
          exact h3

/-- A losing square of a threat-free board is the middle of a trap. -/
lemma losing_char {b : Board} (hBOK : BOK b) (hTF : ThreatFree b) {x : ℕ}
    (hx : x < 2000) (hL : IsLosing b x) :
    (2 ≤ x ∧ x ≤ 1998 ∧ TrapAt b (x - 2)) ∨ (1 ≤ x ∧ x ≤ 1997 ∧ TrapAt b (x - 1)) := by
  obtain ⟨hxe, hL'⟩ := hL
  have hO := threat_shapes hTF hx hxe (hL' Piece.O)
  have hS := threat_shapes hTF hx hxe (hL' Piece.S)
  have hA : (1 ≤ x ∧ b (x - 1) = none ∧ b (x + 1) = some Piece.S) ∨
      (1 ≤ x ∧ b (x + 1) = none ∧ b (x - 1) = some Piece.S) := by
    rcases hO with h | h | h | h | h | h
    · exact Or.inl h.2
    · exact Or.inr h.2
    · exact absurd h.1 (by simp)
    · exact absurd h.1 (by simp)
    · exact absurd h.1 (by simp)
    · exact absurd h.1 (by simp)
  have hB : (b (x + 2) = some Piece.S ∧ b (x + 1) = none) ∨
      (2 ≤ x ∧ b (x - 2) = some Piece.S ∧ b (x - 1) = none) ∨
      (2 ≤ x ∧ b (x - 1) = some Piece.O ∧ b (x - 2) = none) ∨
      (b (x + 1) = some Piece.O ∧ b (x + 2) = none) := by
    rcases hS with h | h | h | h | h | h
    · exact absurd h.1 (by simp)
    · exact absurd h.1 (by simp)
    · exact Or.inl h.2
    · exact Or.inr (Or.inl h.2)
    · exact Or.inr (Or.inr (Or.inl h.2))
    · exact Or.inr (Or.inr (Or.inr h.2))
  rcases hA with ⟨hx1, hA1, hA2⟩ | ⟨hx1, hA1, hA2⟩
  · rcases hB with ⟨hB1, hB2⟩ | ⟨hx2, hB1, hB2⟩ | ⟨hx2, hB1, hB2⟩ | ⟨hB1, hB2⟩
    · rw [hA2] at hB2; simp at hB2
    · have hx1998 : x ≤ 1998 := by
        by_contra hc
        have h2000 : 2000 ≤ x + 1 := by omega
        rw [hBOK (x + 1) h2000] at hA2; simp at hA2
      have e1 : x - 2 + 1 = x - 1 := by omega
      have e2 : x - 2 + 2 = x := by omega
      have e3 : x - 2 + 3 = x + 1 := by omega
      refine Or.inl ⟨hx2, hx1998, ?_⟩
      show b (x - 2) = some Piece.S ∧ b (x - 2 + 1) = none ∧ b (x - 2 + 2) = none ∧
        b (x - 2 + 3) = some Piece.S
      rw [e1, e2, e3]
      exact ⟨hB1, hA1, hxe, hA2⟩
    · rw [hA1] at hB1; simp at hB1
    · rw [hA2] at hB1; simp at hB1
  · rcases hB with ⟨hB1, hB2⟩ | ⟨hx2, hB1, hB2⟩ | ⟨hx2, hB1, hB2⟩ | ⟨hB1, hB2⟩
    · have hx1997 : x ≤ 1997 := by
        by_contra hc
        have h2000 : 2000 ≤ x + 2 := by omega
        rw [hBOK (x + 2) h2000] at hB1; simp at hB1
      have e1 : x - 1 + 1 = x := by omega
      have e2 : x - 1 + 2 = x + 1 := by omega
      have e3 : x - 1 + 3 = x + 2 := by omega
      refine Or.inr ⟨hx1, hx1997, ?_⟩
      show b (x - 1) = some Piece.S ∧ b (x - 1 + 1) = none ∧ b (x - 1 + 2) = none ∧
        b (x - 1 + 3) = some Piece.S
      rw [e1, e2, e3]
      exact ⟨hA2, hxe, hA1, hB1⟩
    · rw [hA2] at hB2; simp at hB2
    · rw [hA2] at hB1; simp at hB1
    · rw [hA1] at hB1; simp at hB1

/-- Middle pairs of distinct traps are disjoint. -/
lemma trap_disjoint {b : Board} {a c : ℕ}
    (haT : TrapAt b a) (hcT : TrapAt b c) (hne : a ≠ c) :
    Disjoint ({a + 1, a + 2} : Finset ℕ) {c + 1, c + 2} := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hx'
  obtain ⟨h0, h1, h2, -⟩ := haT
  obtain ⟨g0, -, -, g3⟩ := hcT
  rcases hx with rfl | rfl <;> rcases hx' with hx' | hx'
  · exact hne (by omega)
  · have e : c + 3 = a + 2 := by omega
    rw [e] at g3; rw [h2] at g3; simp at g3
  · have e : c = a + 1 := by omega
    rw [e] at g0; rw [h1] at g0; simp at g0
  · exact hne (by omega)

lemma mem_losing {b : Board} {x : ℕ} : x ∈ losing b ↔ x < 2000 ∧ IsLosing b x := by
  simp [losing]

lemma mem_trapEnds {b : Board} {a : ℕ} : a ∈ trapEnds b ↔ a < 1997 ∧ TrapAt b a := by
  simp [trapEnds]

/-- The losing squares are exactly the middle squares of the traps. -/
lemma losing_eq_biUnion {b : Board} (hBOK : BOK b) (hTF : ThreatFree b) :
    losing b = (trapEnds b).biUnion fun a => {a + 1, a + 2} := by
  ext x
  simp only [mem_losing, Finset.mem_biUnion, mem_trapEnds, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro ⟨hx, hL⟩
    rcases losing_char hBOK hTF hx hL with ⟨hx2, hx1998, hT⟩ | ⟨hx1, hx1997, hT⟩
    · exact ⟨x - 2, ⟨by omega, hT⟩, by omega⟩
    · exact ⟨x - 1, ⟨by omega, hT⟩, by omega⟩
  · intro ⟨a, ⟨ha, hT⟩, hxm⟩
    have hmid := trap_middle ha hT
    rcases hxm with rfl | rfl
    · exact ⟨by omega, hmid.1⟩
    · exact ⟨by omega, hmid.2⟩

/-- Losing squares come in pairs, hence there is an even number of them. -/
lemma even_card_losing {b : Board} (hBOK : BOK b) (hTF : ThreatFree b) :
    Even (losing b).card := by
  rw [losing_eq_biUnion hBOK hTF, Finset.card_biUnion]
  · have hc2 : ∀ a ∈ trapEnds b, ({a + 1, a + 2} : Finset ℕ).card = 2 :=
      fun a _ => by simp
    have h2 : ∑ a ∈ trapEnds b, ({a + 1, a + 2} : Finset ℕ).card = 2 * (trapEnds b).card := by
      rw [Finset.sum_congr rfl hc2, Finset.sum_const, smul_eq_mul, mul_comm]
    rw [h2]; exact even_two_mul _
  · intro a ha c hc hne
    rw [Finset.mem_coe, mem_trapEnds] at ha hc
    show Disjoint ({a + 1, a + 2} : Finset ℕ) {c + 1, c + 2}
    exact trap_disjoint ha.2 hc.2 hne

/-- A safe move: a legal move that is not on a losing square and that creates
    neither SOS nor an immediate winning opportunity for the opponent. -/
def SafeMove (b : Board) (x : ℕ) (l : Piece) : Prop :=
  x < 2000 ∧ b x = none ∧ ¬ IsLosing b x ∧
    ¬ HasThreat (Function.update b x (some l)) ∧ ¬ HasSOS (Function.update b x (some l))

instance (b : Board) (x : ℕ) (l : Piece) : Decidable (SafeMove b x l) := by
  unfold SafeMove; infer_instance

/-- On a threat-free board with an odd number of empty squares, a safe move
    always exists: there are evenly many losing squares, so some empty square
    is not losing (this is the heart of the pairing argument). -/
lemma exists_safe_move {b : Board} (hBOK : BOK b) (hTF : ThreatFree b)
    (hodd : Odd (empties b).card) :
    ∃ x ∈ Finset.range 2000, ∃ l : Piece, SafeMove b x l := by
  have hsub : losing b ⊆ empties b := by
    intro x hx
    rw [mem_losing] at hx
    exact mem_empties.mpr ⟨hx.1, hx.2.1⟩
  have hlt : (losing b).card < (empties b).card := by
    have hle := Finset.card_le_card hsub
    rcases even_card_losing hBOK hTF with ⟨r, hr⟩
    rcases hodd with ⟨k, hk⟩
    omega
  obtain ⟨x, hxe, hxnl⟩ : ∃ x ∈ empties b, x ∉ losing b := by
    by_contra hcon
    push Not at hcon
    have hsub2 : empties b ⊆ losing b := hcon
    have := Finset.card_le_card hsub2
    omega
  rw [mem_empties] at hxe
  obtain ⟨hx, hxe'⟩ := hxe
  have hnl : ¬ IsLosing b x := fun hL => hxnl (mem_losing.mpr ⟨hx, hL⟩)
  have hnl2 : ¬ ∀ l : Piece, HasThreat (Function.update b x (some l)) :=
    fun hall => hnl ⟨hxe', hall⟩
  obtain ⟨l, hl⟩ := not_forall.mp hnl2
  exact ⟨x, Finset.mem_range.mpr hx, l, hx, hxe', hnl, hl,
    not_hasSOS_update_of_threatFree hTF hx hxe' l⟩

/-- A good second setup move: playing an S at `t` creates a trap without
    giving the opponent an immediate win. -/
def SecondSetupOk (b : Board) (t : ℕ) : Prop :=
  b t = none ∧ ¬ HasThreat (Function.update b t (some Piece.S)) ∧
    ¬ HasSOS (Function.update b t (some Piece.S)) ∧
    HasTrap (Function.update b t (some Piece.S))

instance (b : Board) (t : ℕ) : Decidable (SecondSetupOk b t) := by
  unfold SecondSetupOk; infer_instance

/-- The second player's strategy. -/
noncomputable def p2strat : Strategy := fun b =>
  if h₁ : HasThreat b then
    -- take the immediate win
    (Classical.choose h₁, Classical.choose (Classical.choose_spec h₁).2)
  else if _h₂ : HasTrap b then
    -- play a safe move
    if h₃ : ∃ x ∈ Finset.range 2000, ∃ l : Piece, SafeMove b x l then
      (Classical.choose h₃, Classical.choose (Classical.choose_spec h₃).2)
    else (0, Piece.S)
  else if h₄ : (letters b).card = 1 then
    -- first move: play an S far away from the first player's move
    (if Classical.choose (Finset.card_eq_one.mp h₄) < 1000 then 1500 else 500, Piece.S)
  else if h₆ : ∃ t ∈ Finset.range 2000, SecondSetupOk b t then
    -- second move: complete a trap
    (Classical.choose h₆, Piece.S)
  else (0, Piece.S)

lemma p2strat_threat {b : Board} (h : HasThreat b) :
    ∃ x l, (p2strat b).1 = x ∧ (p2strat b).2 = l ∧ x < 2000 ∧ b x = none ∧
      HasSOS (Function.update b x (some l)) := by
  simp only [p2strat]
  rw [dif_pos h]
  refine ⟨_, _, rfl, rfl, ?_⟩
  have hs := Classical.choose_spec h
  have hs2 := Classical.choose_spec hs.2
  rw [Finset.mem_range] at hs
  exact ⟨hs.1, hs2.1, hs2.2⟩

lemma p2strat_safe {b : Board} (hTF : ThreatFree b) (hT : HasTrap b)
    (h : ∃ x ∈ Finset.range 2000, ∃ l : Piece, SafeMove b x l) :
    ∃ x l, (p2strat b).1 = x ∧ (p2strat b).2 = l ∧ SafeMove b x l := by
  simp only [p2strat]
  rw [dif_neg hTF, dif_pos hT, dif_pos h]
  refine ⟨_, _, rfl, rfl, ?_⟩
  have hs := Classical.choose_spec h
  exact Classical.choose_spec hs.2

lemma p2strat_setup1 {b : Board} (hTF : ThreatFree b) (hNT : ¬ HasTrap b)
    (h1 : (letters b).card = 1) :
    ∃ a, letters b = {a} ∧ (p2strat b).1 = (if a < 1000 then 1500 else 500) ∧
      (p2strat b).2 = Piece.S := by
  simp only [p2strat]
  rw [dif_neg hTF, dif_neg hNT, dif_pos h1]
  exact ⟨_, Classical.choose_spec (Finset.card_eq_one.mp h1), rfl, rfl⟩

lemma p2strat_setup2 {b : Board} (hTF : ThreatFree b) (hNT : ¬ HasTrap b)
    (h1 : (letters b).card ≠ 1) (h : ∃ t ∈ Finset.range 2000, SecondSetupOk b t) :
    ∃ t, (p2strat b).1 = t ∧ (p2strat b).2 = Piece.S ∧ t < 2000 ∧ SecondSetupOk b t := by
  simp only [p2strat]
  rw [dif_neg hTF, dif_neg hNT, dif_neg h1, dif_pos h]
  refine ⟨_, rfl, rfl, ?_⟩
  have hs := Classical.choose_spec h
  rw [Finset.mem_range] at hs
  exact ⟨hs.1, hs.2⟩

/-- The invariant maintained after each move of the second player:
    a threat-free board with a trap and no SOS, with the right parity of
    empty squares (`t = true`: first player to move). -/
def Inv (b : Board) (t : Bool) : Prop :=
  BOK b ∧ ThreatFree b ∧ ¬ HasSOS b ∧ HasTrap b ∧
    (if t then Even (empties b).card ∧ 2 ≤ (empties b).card else Odd (empties b).card)

/-- A trap survives any move that avoids its middle squares
    (which are losing squares). -/
lemma hasTrap_update {b : Board} (hT : HasTrap b) {x : ℕ} (_hx : x < 2000) (hxe : b x = none)
    (hnl : ¬ IsLosing b x) (l : Piece) : HasTrap (Function.update b x (some l)) := by
  rcases hT with ⟨a, ha, hTa⟩
  rw [Finset.mem_range] at ha
  have hmid := trap_middle ha hTa
  have hxa1 : x ≠ a + 1 := by
    intro e; rw [← e] at hmid; exact hnl hmid.1
  have hxa2 : x ≠ a + 2 := by
    intro e; rw [← e] at hmid; exact hnl hmid.2
  have hxa0 : x ≠ a := by
    intro e; rw [e] at hxe; rw [hTa.1] at hxe; simp at hxe
  have hxa3 : x ≠ a + 3 := by
    intro e; rw [e] at hxe; rw [hTa.2.2.2] at hxe; simp at hxe
  refine ⟨a, Finset.mem_range.mpr ha, ?_⟩
  show Function.update b x (some l) a = some Piece.S ∧
    Function.update b x (some l) (a + 1) = none ∧
    Function.update b x (some l) (a + 2) = none ∧
    Function.update b x (some l) (a + 3) = some Piece.S
  rw [Function.update_of_ne hxa0.symm, Function.update_of_ne hxa1.symm,
    Function.update_of_ne hxa2.symm, Function.update_of_ne hxa3.symm]
  exact hTa

/-- The heart of the argument: from an invariant position the second player wins. -/
lemma main_induction (τ : Strategy) :
    ∀ fuel : ℕ, ∀ b : Board, ∀ t : Bool,
      (empties b).card + 1 ≤ fuel → Inv b t → play fuel τ p2strat b t = Outcome.p2 := by
  intro fuel
  induction fuel with
  | zero => intro b t hfuel hInv; omega
  | succ fuel ih =>
    intro b t hfuel hInv
    cases t with
    | false =>
      -- second player to move: odd number of empty squares
      obtain ⟨hBOK, hTF, hSOS, hT, hpar⟩ := hInv
      have hodd : Odd (empties b).card := hpar
      have hne : empties b ≠ ∅ := by
        rcases hodd with ⟨k, hk⟩
        exact empties_ne_empty (by omega)
      rw [play, if_neg hSOS, if_neg hne]
      obtain ⟨x, l, hf, hs, hx, hxe, hnl, hlT, hlSOS⟩ :=
        p2strat_safe hTF hT (exists_safe_move hBOK hTF hodd)
      rw [hf, hs, if_pos ⟨hx, hxe⟩]
      have hcard := empties_update_card hx hxe l
      rcases hodd with ⟨k, hk⟩
      have hn3 : 3 ≤ (empties b).card := by
        rcases hT with ⟨a, ha, hTa⟩
        rw [Finset.mem_range] at ha
        have hmid := trap_middle ha hTa
        have sub : {a + 1, a + 2} ⊆ losing b := by
          intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl
          · exact mem_losing.mpr ⟨by omega, hmid.1⟩
          · exact mem_losing.mpr ⟨by omega, hmid.2⟩
        have h2 := Finset.card_le_card sub
        rw [Finset.card_insert_of_notMem (by simp), Finset.card_singleton] at h2
        have hle : losing b ⊆ empties b := by
          intro y hy
          rw [mem_losing] at hy
          exact mem_empties.mpr ⟨hy.1, hy.2.1⟩
        have := Finset.card_le_card hle
        omega
      refine ih _ true (by omega) ⟨bOK_update hBOK hx l, hlT, hlSOS,
        hasTrap_update hT hx hxe hnl l, ?_⟩
      rw [hcard, hk]
      exact ⟨⟨k, by omega⟩, by omega⟩
    | true =>
      -- first player to move: even number of empty squares, at least 2
      obtain ⟨hBOK, hTF, hSOS, hT, hpar⟩ := hInv
      have hev2 : Even (empties b).card ∧ 2 ≤ (empties b).card := hpar
      obtain ⟨hev, h2⟩ := hev2
      have hne : empties b ≠ ∅ := empties_ne_empty (by omega)
      rw [play, if_neg hSOS, if_neg hne]
      by_cases hlegal : (τ b).1 < 2000 ∧ b (τ b).1 = none
      · rw [if_pos hlegal]
        set m := τ b with hm
        have hcard := empties_update_card hlegal.1 hlegal.2 m.2
        have hSOS' : ¬ HasSOS (Function.update b m.1 (some m.2)) :=
          not_hasSOS_update_of_threatFree hTF hlegal.1 hlegal.2 m.2
        have hBOK' : BOK (Function.update b m.1 (some m.2)) := bOK_update hBOK hlegal.1 m.2
        by_cases hThr : HasThreat (Function.update b m.1 (some m.2))
        · -- the first player blundered: second player wins immediately
          obtain ⟨x, l, hf, hs, hx, hxe, hSOSx⟩ := p2strat_threat hThr
          cases fuel with
          | zero => omega
          | succ fuel =>
            rw [play, if_neg hSOS']
            have hne' : empties (Function.update b m.1 (some m.2)) ≠ ∅ :=
              empties_ne_empty (by rw [hcard]; omega)
            rw [if_neg hne', hf, hs, if_pos ⟨hx, hxe⟩]
            cases fuel with
            | zero => omega
            | succ fuel => rw [play, if_pos hSOSx]
        · -- a safe move: the invariant is preserved
          have hnl : ¬ IsLosing b m.1 := fun hL => hThr (hL.2 m.2)
          refine ih _ false (by omega) ⟨hBOK', hThr, hSOS',
            hasTrap_update hT hlegal.1 hlegal.2 hnl m.2, ?_⟩
          rw [hcard]
          rcases hev with ⟨k, hk⟩
          exact ⟨k - 1, by omega⟩
      · rw [if_neg hlegal]

/-- A good second setup move exists after the second player's first move,
    whatever the first player does (that is not immediately losing). -/
lemma exists_second_setup {q p r : ℕ} {lq lr : Piece}
    (_hq : q < 2000) (hp : p < 2000) (hr : r < 2000)
    (hpq : q + 500 ≤ p ∨ p + 500 ≤ q) (hp5 : p = 500 ∨ p = 1500)
    (hqr : q ≠ r) (hpr : p ≠ r)
    (hTF : ThreatFree (Function.update (Function.update
      (Function.update (fun _ => none) q (some lq)) p (some Piece.S)) r (some lr))) :
    ∃ t ∈ Finset.range 2000,
      SecondSetupOk (Function.update (Function.update
        (Function.update (fun _ => none) q (some lq)) p (some Piece.S)) r (some lr)) t := by
  set b₃ := Function.update (Function.update
    (Function.update (fun _ => none) q (some lq)) p (some Piece.S)) r (some lr) with hb₃def
  have hbq : b₃ q = some lq := by
    rw [hb₃def, Function.update_of_ne hqr, Function.update_of_ne (by omega),
      Function.update_self]
  have hbp : b₃ p = some Piece.S := by
    rw [hb₃def, Function.update_of_ne hpr, Function.update_self]
  have hb₃ : ∀ x : ℕ, x ≠ q → x ≠ p → x ≠ r → b₃ x = none := by
    intro x hxq hxp hxr
    rw [hb₃def, Function.update_of_ne hxr, Function.update_of_ne hxp, Function.update_of_ne hxq]
  have core : ∀ t : ℕ, (t = p + 3 ∨ t + 3 = p) → (r + 2 < t ∨ t + 2 < r) →
      SecondSetupOk b₃ t := by
    intro t ht htr
    -- The square `t` is empty.
    have hte : b₃ t = none := hb₃ t (by omega) (by omega) (by omega)
    -- Playing S at `t` does not produce SOS: among `t, q, p, r`, the only pairs at
    -- distance ≤ 2 involve `r`, and no three of them are consecutive.
    have hnoSOS : ¬ HasSOS (Function.update b₃ t (some Piece.S)) := by
      intro hS
      rcases hS with ⟨i, hir, h0, h1, h2⟩
      rw [Finset.mem_range] at hir
      have mem4 : ∀ j : ℕ, Function.update b₃ t (some Piece.S) j ≠ none →
          j = t ∨ j = q ∨ j = p ∨ j = r := by
        intro j hnn
        by_cases hjt : j = t
        · exact Or.inl hjt
        · rw [Function.update_of_ne hjt] at hnn
          by_cases hq2 : j = q
          · exact Or.inr (Or.inl hq2)
          · by_cases hp2 : j = p
            · exact Or.inr (Or.inr (Or.inl hp2))
            · by_cases hr2 : j = r
              · exact Or.inr (Or.inr (Or.inr hr2))
              · rw [hb₃ _ hq2 hp2 hr2] at hnn; simp at hnn
      have hi0 := mem4 i (by rw [h0]; simp)
      have hi1 := mem4 (i + 1) (by rw [h1]; simp)
      have hi2 := mem4 (i + 2) (by rw [h2]; simp)
      rcases hi0 with hi0 | hi0 | hi0 | hi0 <;>
        rcases hi1 with hi1 | hi1 | hi1 | hi1 <;>
        rcases hi2 with hi2 | hi2 | hi2 | hi2 <;> omega
    -- Playing S at `t` does not give the opponent an immediate win: such a win would
    -- involve `t` and another letter at distance ≤ 2, but `q, p` are far and `r` is
    -- kept away by the choice of `t`.
    have hnoThr : ¬ HasThreat (Function.update b₃ t (some Piece.S)) := by
      intro hT
      rcases hT with ⟨z, hzr, m, hze, hS⟩
      rcases hS with ⟨i, hir, h0, h1, h2⟩
      rw [Finset.mem_range] at hzr hir
      have hzt : z ≠ t := by
        intro e; rw [e, Function.update_self] at hze; simp at hze
      have hzT : z = i ∨ z = i + 1 ∨ z = i + 2 := by
        by_contra hc
        push Not at hc
        rw [Function.update_of_ne hc.1.symm] at h0
        rw [Function.update_of_ne hc.2.1.symm] at h1
        rw [Function.update_of_ne hc.2.2.symm] at h2
        exact hnoSOS ⟨i, Finset.mem_range.mpr hir, h0, h1, h2⟩
      have htT : t = i ∨ t = i + 1 ∨ t = i + 2 := by
        by_contra hc
        push Not at hc
        have et : ∀ j, j ≠ t →
            Function.update (Function.update b₃ t (some Piece.S)) z (some m) j =
              Function.update b₃ z (some m) j := by
          intro j hj
          by_cases hjz : j = z
          · rw [hjz, Function.update_self, Function.update_self]
          · rw [Function.update_of_ne hjz, Function.update_of_ne hjz, Function.update_of_ne hj]
        rw [et i hc.1.symm] at h0
        rw [et (i + 1) hc.2.1.symm] at h1
        rw [et (i + 2) hc.2.2.symm] at h2
        have hbz : b₃ z = none := by
          rw [Function.update_of_ne hzt] at hze; exact hze
        exact hTF ⟨z, Finset.mem_range.mpr hzr, m, hbz, i, Finset.mem_range.mpr hir, h0, h1, h2⟩
      have mem3 : ∀ j : ℕ, j ≠ z → j ≠ t →
          Function.update (Function.update b₃ t (some Piece.S)) z (some m) j ≠ none →
          j = q ∨ j = p ∨ j = r := by
        intro j hjz hjt hnn
        rw [Function.update_of_ne hjz, Function.update_of_ne hjt] at hnn
        by_cases hq2 : j = q
        · exact Or.inl hq2
        · by_cases hp2 : j = p
          · exact Or.inr (Or.inl hp2)
          · by_cases hr2 : j = r
            · exact Or.inr (Or.inr hr2)
            · rw [hb₃ _ hq2 hp2 hr2] at hnn; simp at hnn
      rcases htT with ht1 | ht1 | ht1 <;> rcases hzT with hz1 | hz1 | hz1
      · omega
      · rcases mem3 (i + 2) (by omega) (by omega) (by rw [h2]; simp) with h | h | h <;> omega
      · rcases mem3 (i + 1) (by omega) (by omega) (by rw [h1]; simp) with h | h | h <;> omega
      · rcases mem3 (i + 2) (by omega) (by omega) (by rw [h2]; simp) with h | h | h <;> omega
      · omega
      · rcases mem3 i (by omega) (by omega) (by rw [h0]; simp) with h | h | h <;> omega
      · rcases mem3 (i + 1) (by omega) (by omega) (by rw [h1]; simp) with h | h | h <;> omega
      · rcases mem3 i (by omega) (by omega) (by rw [h0]; simp) with h | h | h <;> omega
      · omega
    -- The trap is created between `p` and `t`.
    have htrap : HasTrap (Function.update b₃ t (some Piece.S)) := by
      rcases ht with ht1 | ht1
      · refine ⟨p, Finset.mem_range.mpr (by omega), ?_⟩
        show Function.update b₃ t (some Piece.S) p = some Piece.S ∧
          Function.update b₃ t (some Piece.S) (p + 1) = none ∧
          Function.update b₃ t (some Piece.S) (p + 2) = none ∧
          Function.update b₃ t (some Piece.S) (p + 3) = some Piece.S
        rw [Function.update_of_ne (by omega : p ≠ t),
          Function.update_of_ne (by omega : p + 1 ≠ t),
          Function.update_of_ne (by omega : p + 2 ≠ t), show p + 3 = t from by omega]
        exact ⟨hbp, hb₃ _ (by omega) (by omega) (by omega),
          hb₃ _ (by omega) (by omega) (by omega), Function.update_self _ _ _⟩
      · refine ⟨t, Finset.mem_range.mpr (by omega), ?_⟩
        show Function.update b₃ t (some Piece.S) t = some Piece.S ∧
          Function.update b₃ t (some Piece.S) (t + 1) = none ∧
          Function.update b₃ t (some Piece.S) (t + 2) = none ∧
          Function.update b₃ t (some Piece.S) (t + 3) = some Piece.S
        rw [Function.update_self, Function.update_of_ne (by omega : t + 1 ≠ t),
          Function.update_of_ne (by omega : t + 2 ≠ t),
          Function.update_of_ne (by omega : t + 3 ≠ t), show t + 3 = p from by omega]
        exact ⟨rfl, hb₃ _ (by omega) (by omega) (by omega),
          hb₃ _ (by omega) (by omega) (by omega), hbp⟩
    exact ⟨hte, hnoThr, hnoSOS, htrap⟩
  by_cases hbr : p + 1 ≤ r ∧ r ≤ p + 5
  · exact ⟨p - 3, Finset.mem_range.mpr (by omega), core (p - 3) (by omega) (by omega)⟩
  · exact ⟨p + 3, Finset.mem_range.mpr (by omega), core (p + 3) (by omega) (by omega)⟩

snip end

problem usa1999_p5 :
    ∃ σ : Strategy, ∀ τ : Strategy, play 2001 τ σ (fun _ => none) true = Outcome.p2 := by
  refine ⟨p2strat, fun τ => ?_⟩
  have hBOK0 : BOK (fun _ => none) := fun i _ => rfl
  have hSOS0 : ¬ HasSOS (fun _ => none : Board) := by
    rintro ⟨i, -, h0, -, -⟩
    simp at h0
  have hcard0 : (empties (fun _ => none : Board)).card = 2000 := by simp [empties]
  have hne0 : empties (fun _ => none : Board) ≠ ∅ := empties_ne_empty (by omega)
  rw [play, if_neg hSOS0, if_neg hne0]
  -- first player's first move
  set m₀ := τ (fun _ => none) with hm₀
  by_cases hlegal0 : m₀.1 < 2000 ∧ ((fun _ => none : Board) m₀.1) = none
  swap
  · rw [if_neg hlegal0]
  rw [if_pos hlegal0]
  set b₁ := Function.update (fun _ => none) m₀.1 (some m₀.2) with hb₁def
  have hBOK1 : BOK b₁ := bOK_update hBOK0 hlegal0.1 m₀.2
  have hlet1 : letters b₁ = {m₀.1} := by
    ext y
    simp only [letters, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, hb₁def]
    by_cases hy : y = m₀.1
    · subst hy; simp [Function.update_self, hlegal0.1]
    · rw [Function.update_of_ne hy]; simp [hy]
  have hcardl1 : (letters b₁).card = 1 := by rw [hlet1, Finset.card_singleton]
  have hSOS1 : ¬ HasSOS b₁ := by
    intro hS
    have h3 := three_le_card_letters_of_hasSOS hS
    omega
  have hTF1 : ThreatFree b₁ := by
    intro hT
    rcases hT with ⟨x, hx, l, hxe, hS⟩
    rw [Finset.mem_range] at hx
    have h3 := three_le_card_letters_of_hasSOS hS
    have hc := letters_update_card hx hxe l
    rw [hlet1, Finset.card_singleton] at hc
    omega
  have hNT1 : ¬ HasTrap b₁ := by
    intro hT
    have h2 := two_le_card_letters_of_hasTrap hT
    omega
  have hcard1 : (empties b₁).card = 1999 := by
    rw [hb₁def, empties_update_card hlegal0.1 hlegal0.2 m₀.2, hcard0]
  have hne1 : empties b₁ ≠ ∅ := empties_ne_empty (by omega)
  -- second player's first move: an S far away from the first player's move
  obtain ⟨a, hleta, hf1, hs1⟩ := p2strat_setup1 hTF1 hNT1 hcardl1
  have haq : a = m₀.1 := Finset.singleton_inj.mp (hleta.symm.trans hlet1)
  rw [haq] at hf1
  set p := if m₀.1 < 1000 then 1500 else 500 with hpdef
  have hp2000 : p < 2000 := by rw [hpdef]; split <;> omega
  have hpq : m₀.1 + 500 ≤ p ∨ p + 500 ≤ m₀.1 := by rw [hpdef]; split <;> omega
  have hp5 : p = 500 ∨ p = 1500 := by rw [hpdef]; split <;> simp
  have hpne : p ≠ m₀.1 := by rw [hpdef]; split <;> omega
  have hbp1 : b₁ p = none := by
    rw [hb₁def, Function.update_of_ne hpne]
  rw [play, if_neg hSOS1, if_neg hne1]
  rw [hf1, hs1, if_pos ⟨hp2000, hbp1⟩]
  -- first player's second move
  set b₂ := Function.update b₁ p (some Piece.S) with hb₂def
  have hBOK2 : BOK b₂ := bOK_update hBOK1 hp2000 Piece.S
  have hlet2 : (letters b₂).card = 2 := by
    rw [hb₂def, letters_update_card hp2000 hbp1 Piece.S, hcardl1]
  have hSOS2 : ¬ HasSOS b₂ := by
    intro hS
    have h3 := three_le_card_letters_of_hasSOS hS
    omega
  have hcard2 : (empties b₂).card = 1998 := by
    rw [hb₂def, empties_update_card hp2000 hbp1 Piece.S, hcard1]
  have hne2 : empties b₂ ≠ ∅ := empties_ne_empty (by omega)
  rw [play, if_neg hSOS2, if_neg hne2]
  set m₂ := τ b₂ with hm₂
  by_cases hlegal2 : m₂.1 < 2000 ∧ b₂ m₂.1 = none
  swap
  · rw [if_neg hlegal2]
  rw [if_pos hlegal2]
  set b₃ := Function.update b₂ m₂.1 (some m₂.2) with hb₃def
  have hBOK3 : BOK b₃ := bOK_update hBOK2 hlegal2.1 m₂.2
  have hb₂q : b₂ m₀.1 = some m₀.2 := by
    rw [hb₂def, Function.update_of_ne hpne.symm, hb₁def, Function.update_self]
  have hb₂p : b₂ p = some Piece.S := by
    rw [hb₂def, Function.update_self]
  have hm₂q : m₂.1 ≠ m₀.1 := by
    intro e; rw [e, hb₂q] at hlegal2; simp at hlegal2
  have hm₂p : m₂.1 ≠ p := by
    intro e; rw [e, hb₂p] at hlegal2; simp at hlegal2
  have hlet3 : (letters b₃).card = 3 := by
    rw [hb₃def, letters_update_card hlegal2.1 hlegal2.2 m₂.2, hlet2]
  have hcard3 : (empties b₃).card = 1997 := by
    rw [hb₃def, empties_update_card hlegal2.1 hlegal2.2 m₂.2, hcard2]
  have hne3 : empties b₃ ≠ ∅ := empties_ne_empty (by omega)
  have hSOS3 : ¬ HasSOS b₃ := by
    rintro ⟨i, hir, h0, h1, h2⟩
    rw [Finset.mem_range] at hir
    have mem3 : ∀ j : ℕ, b₃ j ≠ none → j = m₀.1 ∨ j = p ∨ j = m₂.1 := by
      intro j hj
      rw [hb₃def] at hj
      by_cases hj2 : j = m₂.1
      · exact Or.inr (Or.inr hj2)
      · rw [Function.update_of_ne hj2, hb₂def] at hj
        by_cases hjp : j = p
        · exact Or.inr (Or.inl hjp)
        · rw [Function.update_of_ne hjp, hb₁def] at hj
          by_cases hjq : j = m₀.1
          · exact Or.inl hjq
          · rw [Function.update_of_ne hjq] at hj
            simp at hj
    have hi0 := mem3 i (by rw [h0]; simp)
    have hi1 := mem3 (i + 1) (by rw [h1]; simp)
    have hi2 := mem3 (i + 2) (by rw [h2]; simp)
    rcases hi0 with hi0 | hi0 | hi0 <;> rcases hi1 with hi1 | hi1 | hi1 <;>
      rcases hi2 with hi2 | hi2 | hi2 <;> omega
  have hexp : b₃ = Function.update (Function.update
      (Function.update (fun _ => none) m₀.1 (some m₀.2)) p (some Piece.S)) m₂.1 (some m₂.2) := by
    rw [hb₃def, hb₂def, hb₁def]
  by_cases hThr3 : HasThreat b₃
  · -- the first player allows an immediate win
    obtain ⟨x, l, hf, hs, hx, hxe, hSOSx⟩ := p2strat_threat hThr3
    rw [play, if_neg hSOS3, if_neg hne3, hf, hs, if_pos ⟨hx, hxe⟩]
    rw [play, if_pos hSOSx]
  by_cases hT3 : HasTrap b₃
  · -- the first player has already built a trap: play a safe move
    have hodd3 : Odd (empties b₃).card := ⟨998, by omega⟩
    obtain ⟨x, l, hf, hs, hx, hxe, hnl, hlT, hlSOS⟩ :=
      p2strat_safe hThr3 hT3 (exists_safe_move hBOK3 hThr3 hodd3)
    rw [play, if_neg hSOS3, if_neg hne3, hf, hs, if_pos ⟨hx, hxe⟩]
    have hcard4 := empties_update_card hx hxe l
    have hInv4 : Inv (Function.update b₃ x (some l)) true :=
      ⟨bOK_update hBOK3 hx l, hlT, hlSOS, hasTrap_update hT3 hx hxe hnl l,
        ⟨⟨998, by omega⟩, by omega⟩⟩
    exact main_induction τ 1997 _ true (by omega) hInv4
  · -- the second player builds the trap
    have hcardl3ne : (letters b₃).card ≠ 1 := by rw [hlet3]; simp
    have hTF3exp : ThreatFree (Function.update (Function.update
        (Function.update (fun _ => none) m₀.1 (some m₀.2)) p (some Piece.S)) m₂.1 (some m₂.2)) :=
      hexp ▸ hThr3
    obtain ⟨t, htr, hOk⟩ := exists_second_setup hlegal0.1 hp2000 hlegal2.1 hpq hp5 hm₂q.symm
      hm₂p.symm hTF3exp
    rw [Finset.mem_range] at htr
    rw [← hexp] at hOk
    obtain ⟨t, hf, hs, ht2000, hOk2⟩ :=
      p2strat_setup2 hThr3 hT3 hcardl3ne ⟨t, Finset.mem_range.mpr htr, hOk⟩
    rw [play, if_neg hSOS3, if_neg hne3, hf, hs, if_pos ⟨ht2000, hOk2.1⟩]
    obtain ⟨hte, hnoThr, hnoSOS, htrap⟩ := hOk2
    have hcard4 := empties_update_card ht2000 hte Piece.S
    exact main_induction τ 1997 _ true (by omega)
      ⟨bOK_update hBOK3 ht2000 Piece.S, hnoThr, hnoSOS, htrap, ⟨⟨998, by omega⟩, by omega⟩⟩

end Usa1999P5
