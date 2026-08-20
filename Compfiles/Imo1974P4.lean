/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Order.Interval.Finset.Nat
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 1974, Problem 4

Consider decompositions of an 8 × 8 chessboard into p non-overlapping
rectangles, subject to the following conditions:

(i) Each rectangle has as many white squares as black squares.
(ii) If aᵢ is the number of white squares in the i-th rectangle, then
     a₁ < a₂ < ... < aₚ.

Find the maximum value of p for which such a decomposition is possible.
For this value of p, determine all possible sequences a₁, a₂, ..., aₚ.
-/

namespace Imo1974P4

/-- A rectangle on the chessboard, given by the coordinates `(r, c)` of its
top-left unit square, its height `h` (number of rows) and its width `w`
(number of columns). -/
structure Rect where
  r : ℕ
  c : ℕ
  h : ℕ
  w : ℕ
deriving DecidableEq

/-- The unit squares making up a rectangle. -/
def Rect.cells (R : Rect) : Finset (ℕ × ℕ) :=
  Finset.Icc (R.r, R.c) (R.r + (R.h - 1), R.c + (R.w - 1))

/-- The white squares of the chessboard are those whose coordinates have
even sum. -/
def isWhite (x : ℕ × ℕ) : Prop :=
  (x.1 + x.2) % 2 = 0

instance : DecidablePred isWhite :=
  fun x ↦ inferInstanceAs (Decidable ((x.1 + x.2) % 2 = 0))

/-- The number of white squares of a rectangle. -/
def Rect.whiteCount (R : Rect) : ℕ :=
  (R.cells.filter isWhite).card

/-- The number of black squares of a rectangle. -/
def Rect.blackCount (R : Rect) : ℕ :=
  (R.cells.filter fun x ↦ ¬ isWhite x).card

/-- The 8 × 8 chessboard. -/
def board : Finset (ℕ × ℕ) :=
  Finset.Icc (0, 0) (7, 7)

/-- A valid decomposition of the chessboard: a finite set of nonempty
rectangles contained in the board, pairwise disjoint, covering the whole
board, each having as many white squares as black squares (condition (i)),
and such that no two rectangles have the same number of white squares
(condition (ii)). -/
def ValidDecomp (T : Finset Rect) : Prop :=
  (∀ R ∈ T, 1 ≤ R.h ∧ 1 ≤ R.w ∧ R.r + R.h ≤ 8 ∧ R.c + R.w ≤ 8) ∧
  (∀ R₁ ∈ T, ∀ R₂ ∈ T, R₁ ≠ R₂ → R₁.cells ∩ R₂.cells = ∅) ∧
  T.biUnion Rect.cells = board ∧
  (∀ R ∈ T, R.whiteCount = R.blackCount) ∧
  (T.image Rect.whiteCount).card = T.card

instance (T : Finset Rect) : Decidable (ValidDecomp T) := by
  unfold ValidDecomp
  infer_instance

determine solutions : Finset (Finset ℕ) :=
  {{1, 2, 3, 4, 5, 7, 10}, {1, 2, 3, 4, 5, 8, 9},
   {1, 2, 3, 4, 6, 7, 9}, {1, 2, 3, 5, 6, 7, 8}}

/-- The maximum possible number of white squares. -/
determine maxCount : ℕ := 7

snip begin

/-- The number of unit squares of a rectangle is the product of its two
side lengths. -/
lemma Rect.card_cells (R : Rect) (hh : 1 ≤ R.h) (hw : 1 ≤ R.w) :
    R.cells.card = R.h * R.w := by
  have hcells : R.cells =
      Finset.Icc R.r (R.r + (R.h - 1)) ×ˢ Finset.Icc R.c (R.c + (R.w - 1)) :=
    rfl
  rw [hcells, Finset.card_product, Nat.card_Icc, Nat.card_Icc]
  have e1 : R.r + (R.h - 1) + 1 - R.r = R.h := by lia
  have e2 : R.c + (R.w - 1) + 1 - R.c = R.w := by lia
  rw [e1, e2]

/-- White and black squares together make up all squares of a rectangle. -/
lemma Rect.whiteCount_add_blackCount (R : Rect) :
    R.whiteCount + R.blackCount = R.cells.card := by
  show (R.cells.filter isWhite).card +
    (R.cells.filter fun x ↦ ¬ isWhite x).card = R.cells.card
  exact Finset.card_filter_add_card_filter_not isWhite

/-- A rectangle satisfying condition (i) has at least one white square. -/
lemma Rect.one_le_whiteCount (R : Rect) (hh : 1 ≤ R.h) (hw : 1 ≤ R.w)
    (hbal : R.whiteCount = R.blackCount) : 1 ≤ R.whiteCount := by
  have hcard := R.card_cells hh hw
  have hsum := R.whiteCount_add_blackCount
  have hm : 1 ≤ R.h * R.w := Nat.mul_le_mul hh hw
  lia

/-- A finite set of `k` distinct positive integers has sum at least
`1 + 2 + ... + k`, here phrased as `k * (k + 1) ≤ 2 * ∑ x ∈ S, x`. -/
lemma card_mul_succ_le_two_mul_sum (S : Finset ℕ) :
    (∀ x ∈ S, 1 ≤ x) → S.card * (S.card + 1) ≤ 2 * ∑ x ∈ S, x := by
  refine Finset.strongInduction (p := fun S ↦ (∀ x ∈ S, 1 ≤ x) →
    S.card * (S.card + 1) ≤ 2 * ∑ x ∈ S, x) (fun S ih h ↦ ?_) S
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨m, hm, hmax⟩ := S.exists_max_image id hne
  simp only [id_eq] at hmax
  have ih' := ih (S.erase m) (Finset.erase_ssubset hm)
    (fun x hx ↦ h x (Finset.mem_of_mem_erase hx))
  have hcardpos : 0 < S.card := Finset.card_pos.mpr hne
  have hcard : (S.erase m).card = S.card - 1 := Finset.card_erase_of_mem hm
  have hsub : S ⊆ Finset.Icc 1 m :=
    fun x hx ↦ Finset.mem_Icc.mpr ⟨h x hx, hmax x hx⟩
  have hcardle : S.card ≤ m :=
    calc S.card ≤ (Finset.Icc 1 m).card := Finset.card_le_card hsub
      _ = m := by rw [Nat.card_Icc]; lia
  have hsum := Finset.add_sum_erase S (fun x ↦ x) hm
  set k := (S.erase m).card with hk
  set s := ∑ x ∈ S.erase m, x with hs
  have e1 : S.card = k + 1 := by lia
  have e2 : ∑ x ∈ S, x = m + s := by lia
  rw [e1, e2]
  calc (k + 1) * (k + 2) = k * (k + 1) + 2 * (k + 1) := by ring
    _ ≤ 2 * s + 2 * m := Nat.add_le_add ih' (by lia)
    _ = 2 * (m + s) := by ring

/-- The total number of white squares in a valid decomposition is 32. -/
lemma sum_whiteCount (T : Finset Rect) (hT : ValidDecomp T) :
    ∑ R ∈ T, R.whiteCount = 32 := by
  obtain ⟨hfit, hdisj, hcover, hbal, hdist⟩ := hT
  have hpd : (T : Set Rect).PairwiseDisjoint
      (fun R ↦ R.cells.filter isWhite) := by
    intro R₁ h₁ R₂ h₂ hne
    simp only [Function.onFun]
    have hD : Disjoint R₁.cells R₂.cells :=
      Finset.disjoint_iff_inter_eq_empty.mpr
        (hdisj R₁ (Finset.mem_coe.mp h₁) R₂ (Finset.mem_coe.mp h₂) hne)
    exact Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) hD
  have hunion : T.biUnion (fun R ↦ R.cells.filter isWhite) =
      board.filter isWhite := by
    rw [← hcover]
    exact Eq.symm (Finset.filter_biUnion T Rect.cells isWhite)
  have hcard : (board.filter isWhite).card = 32 := by decide
  have key := Finset.card_biUnion hpd
  rw [hunion, hcard] at key
  rw [key]
  exact rfl

/-- The five sets of seven distinct positive integers summing to 32.
(Enumerated by `decide` over the 7-subsets of `[1, 11]`.) -/
lemma seven_distinct_sum_32 (S : Finset ℕ) (hcard : S.card = 7)
    (hpos : ∀ x ∈ S, 1 ≤ x) (hmax : ∀ x ∈ S, x ≤ 11) (hsum : ∑ x ∈ S, x = 32) :
    S ∈ ({{1, 2, 3, 4, 5, 6, 11}, {1, 2, 3, 4, 5, 7, 10},
          {1, 2, 3, 4, 5, 8, 9}, {1, 2, 3, 4, 6, 7, 9},
          {1, 2, 3, 5, 6, 7, 8}} : Finset (Finset ℕ)) := by
  have hmem : S ∈ (Finset.Icc 1 11).powersetCard 7 :=
    Finset.mem_powersetCard.mpr
      ⟨fun x hx ↦ Finset.mem_Icc.mpr ⟨hpos x hx, hmax x hx⟩, hcard⟩
  have key : ((Finset.Icc 1 11).powersetCard 7).filter
      (fun s ↦ ∑ x ∈ s, x = 32) =
      {{1, 2, 3, 4, 5, 6, 11}, {1, 2, 3, 4, 5, 7, 10}, {1, 2, 3, 4, 5, 8, 9},
       {1, 2, 3, 4, 6, 7, 9}, {1, 2, 3, 5, 6, 7, 8}} := by
    decide
  have h : S ∈ ((Finset.Icc 1 11).powersetCard 7).filter
      (fun s ↦ ∑ x ∈ s, x = 32) :=
    Finset.mem_filter.mpr ⟨hmem, hsum⟩
  rw [key] at h
  exact h

/-- A decomposition realising the white-square counts {1, 2, 3, 4, 5, 7, 10}
(rectangle sizes 2, 4, 6, 8, 10, 14, 20). -/
def decomp₁ : Finset Rect :=
  {⟨0, 0, 2, 7⟩, ⟨0, 7, 8, 1⟩, ⟨2, 0, 4, 5⟩, ⟨2, 5, 3, 2⟩,
   ⟨5, 5, 2, 2⟩, ⟨6, 0, 2, 5⟩, ⟨7, 5, 1, 2⟩}

/-- A decomposition realising the white-square counts {1, 2, 3, 4, 5, 8, 9}
(rectangle sizes 2, 4, 6, 8, 10, 16, 18). -/
def decomp₂ : Finset Rect :=
  {⟨0, 0, 2, 8⟩, ⟨2, 0, 3, 6⟩, ⟨2, 6, 3, 2⟩, ⟨5, 0, 2, 5⟩,
   ⟨5, 5, 2, 1⟩, ⟨5, 6, 2, 2⟩, ⟨7, 0, 1, 8⟩}

/-- A decomposition realising the white-square counts {1, 2, 3, 4, 6, 7, 9}
(rectangle sizes 2, 4, 6, 8, 12, 14, 18). -/
def decomp₃ : Finset Rect :=
  {⟨0, 0, 2, 7⟩, ⟨0, 7, 2, 1⟩, ⟨2, 0, 3, 6⟩, ⟨2, 6, 4, 2⟩,
   ⟨5, 0, 2, 6⟩, ⟨6, 6, 2, 2⟩, ⟨7, 0, 1, 6⟩}

/-- A decomposition realising the white-square counts {1, 2, 3, 5, 6, 7, 8}
(rectangle sizes 2, 4, 6, 10, 12, 14, 16). -/
def decomp₄ : Finset Rect :=
  {⟨0, 0, 2, 8⟩, ⟨2, 0, 2, 7⟩, ⟨2, 7, 2, 1⟩, ⟨4, 0, 2, 6⟩,
   ⟨4, 6, 2, 2⟩, ⟨6, 0, 2, 5⟩, ⟨6, 5, 2, 3⟩}

snip end

problem imo1974_p4 :
    (∀ T : Finset Rect, ValidDecomp T → T.card ≤ maxCount ∧
      (T.card = maxCount → T.image Rect.whiteCount ∈ solutions)) ∧
    ∀ s ∈ solutions, ∃ T : Finset Rect, ValidDecomp T ∧ T.card = maxCount ∧
      T.image Rect.whiteCount = s := by
  refine ⟨fun T hT ↦ ?_, fun s hs ↦ ?_⟩
  · -- Upper bound and classification.
    obtain ⟨hfit, hdisj, hcover, hbal, hdist⟩ := hT
    have hinj : ∀ x ∈ T, ∀ y ∈ T, Rect.whiteCount x = Rect.whiteCount y →
        x = y :=
      fun a ha b hb hab ↦ Finset.injOn_of_card_image_eq hdist ha hb hab
    have hSsum : ∑ x ∈ T.image Rect.whiteCount, x = 32 := by
      rw [Finset.sum_image hinj]
      simpa using sum_whiteCount T ⟨hfit, hdisj, hcover, hbal, hdist⟩
    have hSpos : ∀ x ∈ T.image Rect.whiteCount, 1 ≤ x := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨R, hR, rfl⟩ := hx
      exact Rect.one_le_whiteCount R (hfit R hR).1 (hfit R hR).2.1 (hbal R hR)
    have hub : T.card ≤ 7 := by
      by_contra hcon
      push Not at hcon
      have h1 := card_mul_succ_le_two_mul_sum _ hSpos
      rw [hdist, hSsum] at h1
      have h2 : 8 * 9 ≤ T.card * (T.card + 1) := Nat.mul_le_mul hcon (by lia)
      lia
    refine ⟨hub, fun hcard7 ↦ ?_⟩
    have hScard : (T.image Rect.whiteCount).card = 7 := by
      rw [hdist]; exact hcard7
    have hSmax : ∀ x ∈ T.image Rect.whiteCount, x ≤ 11 := by
      intro x hx
      have h1 := card_mul_succ_le_two_mul_sum ((T.image Rect.whiteCount).erase x)
        (fun y hy ↦ hSpos y (Finset.mem_of_mem_erase hy))
      have hcard_erase : ((T.image Rect.whiteCount).erase x).card = 6 := by
        rw [Finset.card_erase_of_mem hx, hScard]
      rw [hcard_erase] at h1
      have h2 := Finset.add_sum_erase _ (fun y ↦ y) hx
      rw [hSsum] at h2
      lia
    have henum := seven_distinct_sum_32 _ hScard hSpos hSmax hSsum
    simp only [Finset.mem_insert, Finset.mem_singleton] at henum
    rcases henum with h | h | h | h | h
    · -- The set {1,2,3,4,5,6,11} is impossible: a rectangle with 11 white
      -- squares would have 22 squares in total, hence a side of length at
      -- least 11, which does not fit on the board.
      exfalso
      have h11 : (11 : ℕ) ∈ T.image Rect.whiteCount := by rw [h]; decide
      rw [Finset.mem_image] at h11
      obtain ⟨R, hR, hw11⟩ := h11
      have hcardR := Rect.card_cells R (hfit R hR).1 (hfit R hR).2.1
      have hsumR := Rect.whiteCount_add_blackCount R
      have hbalR := hbal R hR
      have h1h : 1 ≤ R.h := (hfit R hR).1
      have h1w : 1 ≤ R.w := (hfit R hR).2.1
      have hh8 : R.h ≤ 8 := by have := (hfit R hR).2.2.1; lia
      have hw8 : R.w ≤ 8 := by have := (hfit R hR).2.2.2; lia
      have h22 : R.h * R.w = 22 := by lia
      set a := R.h with ha
      set b := R.w with hb
      interval_cases a <;> lia
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide
  · -- Each of the four sets is realised by an explicit decomposition.
    simp only [solutions, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact ⟨decomp₁, by decide, by decide, by decide⟩
    · exact ⟨decomp₂, by decide, by decide, by decide⟩
    · exact ⟨decomp₃, by decide, by decide, by decide⟩
    · exact ⟨decomp₄, by decide, by decide, by decide⟩

end Imo1974P4
