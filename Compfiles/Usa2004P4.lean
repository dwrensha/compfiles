/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Data.Nat.Dist
public import Mathlib.Data.Rat.Star
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Combinatorics]
  }

/-!
# USA Mathematical Olympiad 2004, Problem 4

Alice and Bob play a game on a 6 by 6 grid. On his turn, a player chooses
a rational number not yet appearing in the grid and writes it in an empty square
of the grid. Alice goes first and then the players alternate. When all squares
have numbers written in them, in each row, the square with the greatest number in
that row is colored black. Alice wins if he can then draw a line from the top of
the grid to the bottom of the grid that stays in black squares, and Bob wins if
he can't. (If two squares share a vertex, Alice can draw a line from one to the
other that stays in those two squares.) Find, with proof, a winning strategy for
one of the players.
-/

namespace Usa2004P4

/-! ### The board, the pairing of cells, and the endgame -/

/-- A cell of the 6×6 grid: `(row, column)`, both in `Fin 6`.
Row `0` is the top row of the grid and row `5` the bottom row. -/
abbrev Cell : Type := Fin 6 × Fin 6

snip begin

-- Solution formalized from https://web.evanchen.cc/exams/USAMO-2004-notes.pdf

/-- The pairing of columns: each column is paired with the column three places away. -/
def colMate (j : Fin 6) : Fin 6 :=
  ⟨if j.1 < 3 then j.1 + 3 else j.1 - 3, by split <;> omega⟩

/-- The pairing of the cells of the first two rows: the cell `(0, j)` is paired with
`(1, colMate j)` and vice versa; all other cells are paired with themselves.
Paired cells are in different rows and three columns apart, so they do not even
share a vertex. -/
def mate (c : Cell) : Cell :=
  if c.1 = 0 then (1, colMate c.2)
  else if c.1 = 1 then (0, colMate c.2)
  else c

lemma colMate_colMate : ∀ j : Fin 6, colMate (colMate j) = j := by decide

lemma colMate_dist : ∀ j : Fin 6, Nat.dist (colMate j).1 j.1 = 3 := by decide

lemma mate_mate : ∀ c : Cell, mate (mate c) = c := by decide

lemma mate_ne : ∀ c : Cell, c.1.1 ≤ 1 → mate c ≠ c := by decide

lemma mate_val_le : ∀ c : Cell, c.1.1 ≤ 1 → (mate c).1.1 ≤ 1 := by decide

lemma mate_val_eq_of0 : ∀ c : Cell, c.1.1 = 0 → (mate c).1.1 = 1 := by decide

lemma mate_val_eq_of1 : ∀ c : Cell, c.1.1 = 1 → (mate c).1.1 = 0 := by decide

lemma mate_of_ge2 : ∀ c : Cell, 2 ≤ c.1.1 → mate c = c := by decide

lemma mate_snd_dist : ∀ c : Cell, c.1.1 ≤ 1 → Nat.dist c.2.1 (mate c).2.1 = 3 := by decide

lemma mate_fst_ne_iff : ∀ c x : Cell, c.1.1 ≤ 1 → x.1.1 ≤ 1 →
    (c.1 ≠ x.1 ↔ c.1 = (mate x).1) := by decide

lemma mate_fst_eq_iff : ∀ c x : Cell, c.1.1 ≤ 1 → x.1.1 ≤ 1 →
    ((mate c).1 = x.1 ↔ c.1 = (mate x).1) := by decide

lemma mate_fst_ne_self : ∀ c : Cell, c.1.1 ≤ 1 → (mate c).1 ≠ c.1 := by decide

lemma mate_inj : Function.Injective mate := fun c d h => by
  have h1 := congrArg mate h
  rw [mate_mate, mate_mate] at h1
  exact h1

snip end

/-- Two cells are adjacent if their squares share a vertex (Chebyshev distance at most 1). -/
def Adj (x y : Cell) : Prop := Nat.dist x.1.1 y.1.1 ≤ 1 ∧ Nat.dist x.2.1 y.2.1 ≤ 1

/-- A cell is black if it contains the greatest number in its row. -/
def IsBlack (f : Cell → ℚ) (c : Cell) : Prop := ∀ d : Cell, d.1 = c.1 → f d ≤ f c

/-- Alice wins a finished board: there is a chain of black cells, consecutive cells
sharing a vertex, from the top row to the bottom row. -/
def AliceWins (f : Cell → ℚ) : Prop :=
  ∃ c d : Cell, c.1.1 = 0 ∧ d.1.1 = 5 ∧ IsBlack f c ∧ IsBlack f d ∧
    Relation.ReflTransGen (fun x y => Adj x y ∧ IsBlack f x ∧ IsBlack f y) c d

snip begin

/-- The black cell of a row is unique (for an injective filling). -/
lemma IsBlack.unique {f : Cell → ℚ} (hinj : Function.Injective f) {x y : Cell}
    (hx : IsBlack f x) (hy : IsBlack f y) (h : x.1 = y.1) : x = y := by
  have h1 : f y ≤ f x := hx y h.symm
  have h2 : f x ≤ f y := hy x h
  exact hinj (le_antisymm h2 h1)

/-- Every row has a black cell. -/
lemma exists_isBlack (f : Cell → ℚ) (r : Fin 6) : ∃ c : Cell, c.1 = r ∧ IsBlack f c := by
  have hne : (Finset.univ.filter fun c : Cell => c.1 = r).Nonempty :=
    ⟨(r, 0), by simp⟩
  obtain ⟨c, hc, hmax⟩ := Finset.exists_max_image _ f hne
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
  exact ⟨c, hc, fun d hd => hmax d (by simp [hd, hc])⟩

/-- The key endgame lemma: if the black cell of row 1 is the mate of the black cell
of row 0, then the two black cells are three columns apart, so no black chain can
leave row 0, and Alice cannot win. -/
lemma not_aliceWins (f : Cell → ℚ) (hinj : Function.Injective f)
    (c : Cell) (hc0 : c.1.1 = 0) (hc : IsBlack f c) (hm : IsBlack f (mate c)) :
    ¬ AliceWins f := by
  rintro ⟨a, b, ha0, hb5, haB, hbB, hpath⟩
  suffices key : b.1.1 = 0 by omega
  have hgen : ∀ z : Cell,
      Relation.ReflTransGen (fun x y => Adj x y ∧ IsBlack f x ∧ IsBlack f y) a z →
      z.1.1 = 0 := by
    intro z hz
    induction hz with
    | refl => exact ha0
    | tail _ hstep ih =>
      obtain ⟨hadj, hmB, hnB⟩ := hstep
      rename_i prev nxt _
      -- `prev.1.1 = 0` by `ih`, show `nxt.1.1 = 0`
      have hdist : nxt.1.1 ≤ 1 := by
        have h1 := hadj.1
        rw [ih, Nat.dist_zero_left] at h1
        exact h1
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hdist with h | h
      · exact h
      · exfalso
        -- `nxt` is the black cell of row 1, `prev` the black cell of row 0
        have hmc1 : (mate c).1.1 = 1 := mate_val_eq_of0 c hc0
        have hrow : nxt.1 = (mate c).1 := Fin.ext (by rw [h, hmc1])
        have hn : nxt = mate c := IsBlack.unique hinj hnB hm hrow
        have hm0 : prev.1 = c.1 := Fin.ext (by rw [ih, hc0])
        have hprev : prev = c := IsBlack.unique hinj hmB hc hm0
        have h2 := hadj.2
        rw [hn, hprev, mate_snd_dist c (by omega)] at h2
        omega
  exact hgen b hpath

/-! ### Rational numbers: fresh choices avoiding a finite set -/

/-- There is always a rational number outside any finite set. -/
lemma exists_fresh_rat_avoiding (F : Finset ℚ) : ∃ w : ℚ, w ∉ F :=
  Finset.exists_notMem F

/-- Given finite sets `L`, `U` of rationals with everything in `L` smaller than
everything in `U`, there is a rational number strictly between the two sets that
moreover avoids a third finite set `F`. -/
lemma exists_rat_between_avoiding (L U F : Finset ℚ)
    (h : ∀ a ∈ L, ∀ b ∈ U, a < b) :
    ∃ w : ℚ, (∀ a ∈ L, a < w) ∧ (∀ b ∈ U, w < b) ∧ w ∉ F := by
  -- Any nonempty open interval of ℚ is infinite, so it contains a point outside the
  -- finite set `F`.
  have key : ∀ {p q : ℚ}, p < q → ∃ w : ℚ, p < w ∧ w < q ∧ w ∉ F := by
    intro p q hpq
    obtain ⟨w, ⟨hpw, hwq⟩, hwF⟩ := (Set.Ioo_infinite hpq).exists_notMem_finset F
    exact ⟨w, hpw, hwq, hwF⟩
  rcases L.eq_empty_or_nonempty with hL | hL
  · rcases U.eq_empty_or_nonempty with hU | hU
    · -- L = ∅, U = ∅: any rational avoiding F works.
      obtain ⟨w, hwF⟩ := exists_fresh_rat_avoiding F
      exact ⟨w, fun a ha ↦ absurd (hL ▸ ha) (Finset.notMem_empty a),
        fun b hb ↦ absurd (hU ▸ hb) (Finset.notMem_empty b), hwF⟩
    · -- L = ∅, U ≠ ∅: pick w in (min' U - 1, min' U).
      obtain ⟨w, -, hwq, hwF⟩ := key (p := U.min' hU - 1) (q := U.min' hU) (by linarith)
      exact ⟨w, fun a ha ↦ absurd (hL ▸ ha) (Finset.notMem_empty a),
        fun b hb ↦ lt_of_lt_of_le hwq (Finset.min'_le U b hb), hwF⟩
  · rcases U.eq_empty_or_nonempty with hU | hU
    · -- L ≠ ∅, U = ∅: pick w in (max' L, max' L + 1).
      obtain ⟨w, hwp, -, hwF⟩ := key (p := L.max' hL) (q := L.max' hL + 1) (by linarith)
      exact ⟨w, fun a ha ↦ lt_of_le_of_lt (Finset.le_max' L a ha) hwp,
        fun b hb ↦ absurd (hU ▸ hb) (Finset.notMem_empty b), hwF⟩
    · -- L ≠ ∅, U ≠ ∅: max' L < min' U, pick w in (max' L, min' U).
      have hpq : L.max' hL < U.min' hU := h _ (L.max'_mem hL) _ (U.min'_mem hU)
      obtain ⟨w, hwp, hwq, hwF⟩ := key hpq
      exact ⟨w, fun a ha ↦ lt_of_le_of_lt (Finset.le_max' L a ha) hwp,
        fun b hb ↦ lt_of_lt_of_le hwq (Finset.min'_le U b hb), hwF⟩

/-! ### Plays and partial boards -/

snip end

/-- A play of the game: the sequence of 36 moves, each a cell together with the
rational number written in it.  Alice makes the moves `0, 2, ..., 34` and Bob the
moves `1, 3, ..., 35`.  The legality conditions are that all cells played are
distinct (a player must write in an empty square) and that all numbers played are
distinct (a player must choose a rational not yet appearing in the grid). -/
structure Play where
  moves : Fin 36 → Cell × ℚ
  cell_inj : Function.Injective fun i => (moves i).1
  val_inj : Function.Injective fun i => (moves i).2

/-- The board after the first `n` moves of a play. -/
noncomputable def prefBoard (p : Play) (n : ℕ) : Cell → Option ℚ :=
  fun c => if h : ∃ i : Fin 36, (i : ℕ) < n ∧ (p.moves i).1 = c
    then some (p.moves h.choose).2
    else none

/-- The final board of a play: after 36 moves every cell is filled (see
`prefBoard_finalBoard`), and this is the number written in each cell. -/
noncomputable def finalBoard (p : Play) : Cell → ℚ :=
  fun c => (prefBoard p 36 c).getD 0

/-- A play follows Bob's strategy `σ` if each of Bob's moves (the odd-numbered
moves) is the move prescribed by `σ` on the current board. -/
def FollowsStrategy (σ : (Cell → Option ℚ) → Cell × ℚ) (p : Play) : Prop :=
  ∀ k : Fin 36, Odd (k : ℕ) → p.moves k = σ (prefBoard p k)

snip begin

lemma prefBoard_zero (p : Play) (c : Cell) : prefBoard p 0 c = none := by
  simp [prefBoard]

lemma prefBoard_eq_some {p : Play} {n : ℕ} {c : Cell} {v : ℚ} :
    prefBoard p n c = some v ↔ ∃ i : Fin 36, (i : ℕ) < n ∧ p.moves i = (c, v) := by
  unfold prefBoard
  by_cases h : ∃ i : Fin 36, (i : ℕ) < n ∧ (p.moves i).1 = c
  · rw [dif_pos h]
    constructor
    · intro hv
      exact ⟨h.choose, h.choose_spec.1, Prod.ext h.choose_spec.2 (Option.some.inj hv)⟩
    · rintro ⟨i, hin, hi⟩
      have hce : h.choose = i := p.cell_inj (by simp [h.choose_spec.2, hi])
      rw [hce, hi]
  · rw [dif_neg h]
    constructor
    · intro hv
      nomatch hv
    · rintro ⟨i, hin, hi⟩
      exact absurd ⟨i, hin, congrArg Prod.fst hi⟩ h

lemma prefBoard_eq_none {p : Play} {n : ℕ} {c : Cell} :
    prefBoard p n c = none ↔ ∀ i : Fin 36, (i : ℕ) < n → (p.moves i).1 ≠ c := by
  constructor
  · intro h i hin hic
    have hs : prefBoard p n c = some (p.moves i).2 :=
      prefBoard_eq_some.mpr ⟨i, hin, Prod.ext hic rfl⟩
    rw [h] at hs
    nomatch hs
  · intro h
    cases hbo : prefBoard p n c with
    | none => rfl
    | some v =>
      obtain ⟨i, hin, hi⟩ := prefBoard_eq_some.mp hbo
      exact absurd (congrArg Prod.fst hi) (h i hin)

lemma prefBoard_succ (p : Play) {n : ℕ} (hn : n < 36) :
    prefBoard p (n + 1) = Function.update (prefBoard p n) (p.moves ⟨n, hn⟩).1
      (some (p.moves ⟨n, hn⟩).2) := by
  funext c
  by_cases hc : c = (p.moves ⟨n, hn⟩).1
  · subst hc
    rw [Function.update_self]
    exact prefBoard_eq_some.mpr ⟨⟨n, hn⟩, Nat.lt_succ_self n, rfl⟩
  · rw [Function.update_of_ne hc]
    cases h1 : prefBoard p n c with
    | none =>
      cases h2 : prefBoard p (n + 1) c with
      | none => rfl
      | some v =>
        obtain ⟨i, hi, hiv⟩ := prefBoard_eq_some.mp h2
        have hic : (p.moves i).1 = c := congrArg Prod.fst hiv
        have hlt : (i : ℕ) < n := by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
          · exact h
          · exfalso
            apply hc
            have hie : i = ⟨n, hn⟩ := Fin.ext h
            rw [← hic, hie]
        rw [prefBoard_eq_some.mpr ⟨i, hlt, hiv⟩] at h1
        nomatch h1
    | some v =>
      have hs : prefBoard p (n + 1) c = some v := by
        obtain ⟨i, hi, hiv⟩ := prefBoard_eq_some.mp h1
        exact prefBoard_eq_some.mpr ⟨i, Nat.lt_succ_of_lt hi, hiv⟩
      rw [hs]

lemma prefBoard_apply_self (p : Play) {n : ℕ} (hn : n < 36) :
    prefBoard p n (p.moves ⟨n, hn⟩).1 = none := by
  rw [prefBoard_eq_none]
  intro i hi hic
  have hie : i = ⟨n, hn⟩ := p.cell_inj hic
  have hiv : (i : ℕ) = n := Fin.ext_iff.mp hie
  omega

lemma prefBoard_inj {p : Play} {n m : ℕ} {c d : Cell} {v : ℚ} :
    prefBoard p n c = some v → prefBoard p m d = some v → c = d := by
  intro h1 h2
  obtain ⟨i, _, hi⟩ := prefBoard_eq_some.mp h1
  obtain ⟨j, _, hj⟩ := prefBoard_eq_some.mp h2
  have hvv : (p.moves i).2 = (p.moves j).2 := by rw [hi, hj]
  have hij : i = j := p.val_inj hvv
  have hc1 : (p.moves i).1 = c := congrArg Prod.fst hi
  have hd1 : (p.moves j).1 = d := congrArg Prod.fst hj
  rw [← hc1, ← hd1, hij]

/-- The set of cells filled after the first `n` moves of a play. -/
def filled (p : Play) (n : ℕ) (hn : n ≤ 36) : Finset Cell :=
  Finset.univ.image fun i : Fin n => (p.moves (Fin.castLE hn i)).1

lemma filled_cell_inj (p : Play) {n : ℕ} {hn : n ≤ 36} :
    Function.Injective fun i : Fin n => (p.moves (Fin.castLE hn i)).1 := by
  intro i j h
  have h1 := p.cell_inj h
  rwa [Fin.castLE_inj] at h1

lemma card_filled (p : Play) (n : ℕ) (hn : n ≤ 36) : (filled p n hn).card = n := by
  rw [filled, Finset.card_image_of_injOn (filled_cell_inj p).injOn, Finset.card_univ,
    Fintype.card_fin]

lemma mem_filled {p : Play} {n : ℕ} {hn : n ≤ 36} {c : Cell} :
    c ∈ filled p n hn ↔ prefBoard p n c ≠ none := by
  constructor
  · intro h
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    intro hcon
    rw [prefBoard_eq_none] at hcon
    exact hcon _ i.2 hi
  · intro h
    cases hbo : prefBoard p n c with
    | none => exact absurd hbo h
    | some v =>
      obtain ⟨i, hin, hi⟩ := prefBoard_eq_some.mp hbo
      apply Finset.mem_image.mpr
      refine ⟨⟨i.1, hin⟩, Finset.mem_univ _, ?_⟩
      have hie : Fin.castLE hn ⟨i.1, hin⟩ = i := Fin.ext rfl
      rw [hie]
      exact congrArg Prod.fst hi

lemma prefBoard_36_isSome (p : Play) (c : Cell) : (prefBoard p 36 c).isSome := by
  have hbij : Function.Bijective fun i => (p.moves i).1 := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨p.cell_inj, by decide⟩
  obtain ⟨i, hi⟩ := hbij.2 c
  rw [Option.isSome_iff_exists]
  exact ⟨(p.moves i).2, prefBoard_eq_some.mpr ⟨i, i.2, Prod.ext hi rfl⟩⟩

lemma prefBoard_finalBoard (p : Play) (c : Cell) :
    prefBoard p 36 c = some (finalBoard p c) := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (prefBoard_36_isSome p c)
  simp [finalBoard, hv]

lemma finalBoard_inj (p : Play) : Function.Injective (finalBoard p) := by
  intro c d hcd
  have h2 : prefBoard p 36 d = some (finalBoard p c) := hcd ▸ prefBoard_finalBoard p d
  exact prefBoard_inj (prefBoard_finalBoard p c) h2

/-! ### Two general-purpose lemmas -/

/-- A set of cells of the first two rows closed under the pairing has even cardinality:
it is a union of pairs `{c, mate c}`. -/
lemma even_card_of_mate_closed (S : Finset Cell)
    (hsub : ∀ c ∈ S, c.1.1 ≤ 1)
    (hclosed : ∀ c ∈ S, mate c ∈ S) : Even S.card := by
  set T := S.filter (fun c => c.1.1 = 0) with hT
  have hunion : S = T ∪ T.image mate := by
    ext c
    simp only [Finset.mem_union, Finset.mem_image, hT, Finset.mem_filter]
    constructor
    · intro hc
      have hc1 := hsub c hc
      rcases (by omega : c.1.1 = 0 ∨ c.1.1 = 1) with h | h
      · exact Or.inl ⟨hc, h⟩
      · exact Or.inr ⟨mate c, ⟨hclosed c hc, mate_val_eq_of1 c h⟩, mate_mate c⟩
    · rintro (⟨hc, -⟩ | ⟨d, ⟨hd, -⟩, rfl⟩)
      · exact hc
      · exact hclosed d hd
  have hdisj : Disjoint T (T.image mate) := by
    rw [Finset.disjoint_left]
    intro c hcT hcI
    rw [hT] at hcT
    obtain ⟨hcS, hc0⟩ := Finset.mem_filter.mp hcT
    obtain ⟨d, hdT, hdc⟩ := Finset.mem_image.mp hcI
    rw [hT] at hdT
    obtain ⟨hdS, hd0⟩ := Finset.mem_filter.mp hdT
    rw [← hdc] at hc0
    have := mate_val_eq_of0 d hd0
    omega
  rw [hunion, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injOn mate_inj.injOn]
  exact ⟨T.card, rfl⟩

/-- Updating two order-isomorphic functions at a fresh point with values occupying
the same relative position preserves the order-isomorphism. -/
lemma orderIso_update {ι : Type*} [DecidableEq ι] (A B : ι → ℚ) (S : Set ι) (x : ι)
    (vx w : ℚ) (hx : x ∉ S)
    (hiso : ∀ c ∈ S, ∀ d ∈ S, (A c < A d ↔ B c < B d))
    (hnew : ∀ z ∈ S, (A z < vx → B z < w) ∧ (vx < A z → w < B z))
    (hA : ∀ z ∈ S, A z ≠ vx) :
    ∀ c ∈ S ∪ {x}, ∀ d ∈ S ∪ {x},
      (Function.update A x vx c < Function.update A x vx d ↔
       Function.update B x w c < Function.update B x w d) := by
  intro c hc d hd
  rcases hc with hc | rfl
  · rcases hd with hd | rfl
    · rw [Function.update_of_ne (ne_of_mem_of_not_mem hc hx),
        Function.update_of_ne (ne_of_mem_of_not_mem hd hx),
        Function.update_of_ne (ne_of_mem_of_not_mem hc hx),
        Function.update_of_ne (ne_of_mem_of_not_mem hd hx)]
      exact hiso c hc d hd
    · rw [Function.update_self, Function.update_self,
        Function.update_of_ne (ne_of_mem_of_not_mem hc hx),
        Function.update_of_ne (ne_of_mem_of_not_mem hc hx)]
      refine ⟨(hnew c hc).1, fun hlt => ?_⟩
      by_contra hcon
      rw [not_lt] at hcon
      have hgt : vx < A c := lt_of_le_of_ne hcon (Ne.symm (hA c hc))
      exact absurd hlt (not_lt_of_gt ((hnew c hc).2 hgt))
  · rcases hd with hd | rfl
    · rw [Function.update_self, Function.update_self,
        Function.update_of_ne (ne_of_mem_of_not_mem hd hx),
        Function.update_of_ne (ne_of_mem_of_not_mem hd hx)]
      refine ⟨(hnew d hd).2, fun hlt => ?_⟩
      by_contra hcon
      rw [not_lt] at hcon
      have hgt : A d < vx := lt_of_le_of_ne hcon (hA d hd)
      exact absurd ((hnew d hd).1 hgt) (not_lt_of_gt hlt)
    · rw [Function.update_self, Function.update_self]
      exact ⟨fun hlt => absurd hlt (lt_irrefl _), fun hlt => absurd hlt (lt_irrefl _)⟩

/-! ### Bob's strategy -/

/-- The board is closed under the pairing on the first two rows: a cell of the
first two rows is filled iff its mate is filled. -/
def Rows01Closed (b : Cell → Option ℚ) : Prop :=
  ∀ c : Cell, c.1.1 ≤ 1 → (b c = none ↔ b (mate c) = none)

/-- The entries of each of the first two rows are ordered in the same way as the
entries of the paired cells. -/
def SameRowIso (b : Cell → Option ℚ) : Prop :=
  ∀ c d : Cell, ∀ vc vd vmc vmd : ℚ, c.1 = d.1 → c.1.1 ≤ 1 →
    b c = some vc → b d = some vd → b (mate c) = some vmc → b (mate d) = some vmd →
    (vc < vd ↔ vmc < vmd)

/-- The invariant Bob maintains after each of his moves. -/
def Inv (b : Cell → Option ℚ) : Prop := Rows01Closed b ∧ SameRowIso b

/-- `GoodMateValue b x vx w` says that the number `w` is a legal and good answer
for Bob in the mate of the cell `x` (which contains `vx`): it does not yet appear
on the board, and it occupies the same position relative to the entries of the row
of `x` as `vx` does relative to the entries of the paired cells. -/
def GoodMateValue (b : Cell → Option ℚ) (x : Cell) (vx w : ℚ) : Prop :=
  (∀ c : Cell, b c ≠ some w) ∧
  ∀ z : Cell, ∀ vz vmz : ℚ, z.1 = x.1 → z ≠ x → b z = some vz → b (mate z) = some vmz →
    (vz < vx → vmz < w) ∧ (vx < vz → w < vmz)

/-- A good value for Bob's answer exists: the constraints coming from entries below
`vx` and those coming from entries above `vx` are consistent (by the
order-isomorphism of the board before Alice's move), and `ℚ` is dense. -/
lemma exists_GoodMateValue {b₀ b₁ : Cell → Option ℚ} (hinv : Inv b₀)
    {x : Cell} (hx01 : x.1.1 ≤ 1) (hx : b₀ x = none) {vx : ℚ}
    (hb₁ : b₁ = Function.update b₀ x (some vx)) :
    ∃ w, GoodMateValue b₁ x vx w := by
  classical
  subst hb₁
  set b₁ := Function.update b₀ x (some vx) with hb₁
  -- the lower and upper constraints on `w`, as finite sets of rationals
  set L : Finset ℚ := (Finset.univ.filter fun z : Cell =>
      z.1 = x.1 ∧ z ≠ x ∧ ∃ vz vmz, b₁ z = some vz ∧ b₁ (mate z) = some vmz ∧
        vz < vx).image fun z => (b₁ (mate z)).getD 0 with hL
  set U : Finset ℚ := (Finset.univ.filter fun z : Cell =>
      z.1 = x.1 ∧ z ≠ x ∧ ∃ vz vmz, b₁ z = some vz ∧ b₁ (mate z) = some vmz ∧
        vx < vz).image fun z => (b₁ (mate z)).getD 0 with hU
  set F : Finset ℚ := Finset.univ.image fun c => (b₁ c).getD 0 with hF
  -- every element of `L` is smaller than every element of `U`
  have hLU : ∀ a ∈ L, ∀ bb ∈ U, a < bb := by
    intro a ha bb hb
    rw [hL] at ha
    obtain ⟨z₁, hz₁, ha'⟩ := Finset.mem_image.mp ha
    rw [hU] at hb
    obtain ⟨z₂, hz₂, hb'⟩ := Finset.mem_image.mp hb
    obtain ⟨-, hz₁row, hz₁ne, vz₁, vmz₁, hz₁v, hz₁m, hz₁lt⟩ := Finset.mem_filter.mp hz₁
    obtain ⟨-, hz₂row, hz₂ne, vz₂, vmz₂, hz₂v, hz₂m, hz₂lt⟩ := Finset.mem_filter.mp hz₂
    -- move everything to the board `b₀` before Alice's move
    have hb₀z₁ : b₀ z₁ = some vz₁ := by
      rw [hb₁, Function.update_of_ne hz₁ne] at hz₁v
      exact hz₁v
    have hb₀z₂ : b₀ z₂ = some vz₂ := by
      rw [hb₁, Function.update_of_ne hz₂ne] at hz₂v
      exact hz₂v
    have hmz₁ : mate z₁ ≠ x := by
      intro hcon
      have h0 : b₀ z₁ = none := by
        have hcl := hinv.1 z₁ (by rw [hz₁row]; exact hx01)
        rw [hcon] at hcl
        exact hcl.mpr hx
      rw [h0] at hb₀z₁
      nomatch hb₀z₁
    have hmz₂ : mate z₂ ≠ x := by
      intro hcon
      have h0 : b₀ z₂ = none := by
        have hcl := hinv.1 z₂ (by rw [hz₂row]; exact hx01)
        rw [hcon] at hcl
        exact hcl.mpr hx
      rw [h0] at hb₀z₂
      nomatch hb₀z₂
    have hb₀mz₁ : b₀ (mate z₁) = some vmz₁ := by
      rw [hb₁, Function.update_of_ne hmz₁] at hz₁m
      exact hz₁m
    have hb₀mz₂ : b₀ (mate z₂) = some vmz₂ := by
      rw [hb₁, Function.update_of_ne hmz₂] at hz₂m
      exact hz₂m
    have ha'' : a = vmz₁ := by
      rw [← ha']
      show (b₁ (mate z₁)).getD 0 = vmz₁
      rw [hb₁, Function.update_of_ne hmz₁, hb₀mz₁]
      rfl
    have hb'' : bb = vmz₂ := by
      rw [← hb']
      show (b₁ (mate z₂)).getD 0 = vmz₂
      rw [hb₁, Function.update_of_ne hmz₂, hb₀mz₂]
      rfl
    rw [ha'', hb'']
    have hrow : z₁.1 = z₂.1 := hz₁row.trans hz₂row.symm
    have h01 : z₁.1.1 ≤ 1 := by rw [hz₁row]; exact hx01
    have hlt : vz₁ < vz₂ := lt_trans hz₁lt hz₂lt
    exact (hinv.2 z₁ z₂ vz₁ vz₂ vmz₁ vmz₂ hrow h01 hb₀z₁ hb₀z₂ hb₀mz₁ hb₀mz₂).mp hlt
  obtain ⟨w, hLw, hUw, hFw⟩ := exists_rat_between_avoiding L U F hLU
  refine ⟨w, ?_, ?_⟩
  · intro c hc
    apply hFw
    rw [hF]
    exact Finset.mem_image.mpr ⟨c, Finset.mem_univ c,
      by show (b₁ c).getD 0 = w; rw [hc]; rfl⟩
  · intro z vz vmz hzrow hzne hzvm hzm
    constructor
    · intro hlt
      apply hLw
      rw [hL]
      refine Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ z, hzrow,
        hzne, vz, vmz, hzvm, hzm, hlt⟩, ?_⟩
      show (b₁ (mate z)).getD 0 = vmz
      rw [hzm]
      rfl
    · intro hlt
      apply hUw
      rw [hU]
      refine Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ z, hzrow,
        hzne, vz, vmz, hzvm, hzm, hlt⟩, ?_⟩
      show (b₁ (mate z)).getD 0 = vmz
      rw [hzm]
      rfl

open Classical in
/-- The number Bob writes in the mate of Alice's cell when he answers in the first
two rows. -/
noncomputable def bobMateValue (b : Cell → Option ℚ) (x : Cell) : ℚ :=
  if h : ∃ w, GoodMateValue b x ((b x).getD 0) w then h.choose else 0

/-- The cell Bob plays in when Alice plays in rows 3 to 6: some empty cell of rows
3 to 6 (one always exists at that point by a parity argument, see `inv_prefBoard`). -/
noncomputable def bobCell2 (b : Cell → Option ℚ) : Cell :=
  if h : ∃ c : Cell, 2 ≤ c.1.1 ∧ b c = none then h.choose else (2, 0)

/-- A rational number not appearing on the board. -/
noncomputable def bobFreshValue (b : Cell → Option ℚ) : ℚ :=
  (exists_fresh_rat_avoiding (Finset.univ.image fun c => (b c).getD 0)).choose

lemma bobFreshValue_fresh (b : Cell → Option ℚ) (c : Cell) :
    b c ≠ some (bobFreshValue b) := by
  intro hc
  have hspec := (exists_fresh_rat_avoiding
    (Finset.univ.image fun c => (b c).getD 0)).choose_spec
  apply hspec
  exact Finset.mem_image.mpr ⟨c, Finset.mem_univ c,
    by show (b c).getD 0 = _; rw [hc]; rfl⟩

/-- Bob's strategy: if Alice just played in the first two rows, answer in the mate
of her cell with a number preserving the order-isomorphism; otherwise play in any
empty cell of rows 3 to 6 with a fresh number. -/
noncomputable def bobMove (b : Cell → Option ℚ) : Cell × ℚ :=
  if h : ∃ y : Cell, y.1.1 ≤ 1 ∧ b y ≠ none ∧ b (mate y) = none
  then (mate h.choose, bobMateValue b h.choose)
  else (bobCell2 b, bobFreshValue b)

lemma bobMove_eq_mate {b : Cell → Option ℚ} {x : Cell} (hx01 : x.1.1 ≤ 1)
    (hxs : b x ≠ none) (hxm : b (mate x) = none)
    (huniq : ∀ y : Cell, y.1.1 ≤ 1 → b y ≠ none → b (mate y) = none → y = x) :
    bobMove b = (mate x, bobMateValue b x) := by
  have hP : ∃ y : Cell, y.1.1 ≤ 1 ∧ b y ≠ none ∧ b (mate y) = none :=
    ⟨x, hx01, hxs, hxm⟩
  unfold bobMove
  rw [dif_pos hP]
  have hce : hP.choose = x :=
    huniq _ hP.choose_spec.1 hP.choose_spec.2.1 hP.choose_spec.2.2
  rw [hce]

lemma bobMove_eq_rows2 {b : Cell → Option ℚ}
    (h : ¬ ∃ y : Cell, y.1.1 ≤ 1 ∧ b y ≠ none ∧ b (mate y) = none) :
    bobMove b = (bobCell2 b, bobFreshValue b) := by
  unfold bobMove
  rw [dif_neg h]

lemma bobCell2_spec {b : Cell → Option ℚ}
    (h : ∃ c : Cell, 2 ≤ c.1.1 ∧ b c = none) :
    2 ≤ (bobCell2 b).1.1 ∧ b (bobCell2 b) = none := by
  unfold bobCell2
  rw [dif_pos h]
  exact h.choose_spec

lemma goodMateValue_bobMateValue {b : Cell → Option ℚ} {x : Cell} {vx : ℚ}
    (hx : b x = some vx) (h : ∃ w, GoodMateValue b x vx w) :
    GoodMateValue b x vx (bobMateValue b x) := by
  have hdx : (b x).getD 0 = vx := by rw [hx]; rfl
  unfold bobMateValue
  rw [hdx, dif_pos h]
  exact h.choose_spec

/-- The invariant is preserved when Alice plays in rows 3 to 6 and Bob answers in
rows 3 to 6 (the first two rows are untouched). -/
lemma inv_update_rows2 {b₀ b₁ b₂ : Cell → Option ℚ} (hinv : Inv b₀)
    {x c₂ : Cell} (hx2 : 2 ≤ x.1.1) (hc₂2 : 2 ≤ c₂.1.1) {vx w₂ : ℚ}
    (hb₁ : b₁ = Function.update b₀ x (some vx))
    (hb₂ : b₂ = Function.update b₁ c₂ (some w₂)) :
    Inv b₂ := by
  subst hb₁
  subst hb₂
  have hn : ∀ e : Cell, e.1.1 ≤ 1 → e ≠ x ∧ e ≠ c₂ ∧ mate e ≠ x ∧ mate e ≠ c₂ := by
    intro e he
    have hme := mate_val_le e he
    exact ⟨by rintro rfl; omega, by rintro rfl; omega,
      by intro h; rw [h] at hme; omega, by intro h; rw [h] at hme; omega⟩
  constructor
  · intro c hc
    obtain ⟨h1, h2, h3, h4⟩ := hn c hc
    rw [Function.update_of_ne h2, Function.update_of_ne h1,
      Function.update_of_ne h4, Function.update_of_ne h3]
    exact hinv.1 c hc
  · intro c d vc vd vmc vmd hcd hc01 hvC hvD hvMC hvMD
    obtain ⟨h1, h2, h3, h4⟩ := hn c hc01
    have hd01 : d.1.1 ≤ 1 := by rw [← hcd]; exact hc01
    obtain ⟨h5, h6, h7, h8⟩ := hn d hd01
    rw [Function.update_of_ne h2, Function.update_of_ne h1] at hvC
    rw [Function.update_of_ne h6, Function.update_of_ne h5] at hvD
    rw [Function.update_of_ne h4, Function.update_of_ne h3] at hvMC
    rw [Function.update_of_ne h8, Function.update_of_ne h7] at hvMD
    exact hinv.2 c d vc vd vmc vmd hcd hc01 hvC hvD hvMC hvMD

/-- The invariant is preserved when Alice plays in the first two rows and Bob
answers in the mate of her cell with a good value. -/
lemma inv_update_mate {b₀ b₁ b₂ : Cell → Option ℚ} (hinv : Inv b₀)
    {x : Cell} (hx01 : x.1.1 ≤ 1) (hx : b₀ x = none) {vx w : ℚ}
    (hb₁ : b₁ = Function.update b₀ x (some vx))
    (hb₂ : b₂ = Function.update b₁ (mate x) (some w))
    (hinj : ∀ c d : Cell, ∀ v : ℚ, b₁ c = some v → b₁ d = some v → c = d)
    (hw : GoodMateValue b₁ x vx w) :
    Inv b₂ := by
  subst hb₁
  subst hb₂
  have hmx : x ≠ mate x := (mate_ne x hx01).symm
  have hxm : b₀ (mate x) = none := (hinv.1 x hx01).mp hx
  constructor
  · -- the rows 0-1 part of the new board is still closed under the pairing
    intro c hc
    by_cases hcx : c = x
    · subst hcx
      rw [Function.update_of_ne hmx, Function.update_self, Function.update_self]
      exact iff_of_false (Option.some_ne_none _) (Option.some_ne_none _)
    · by_cases hcmx : c = mate x
      · subst hcmx
        rw [Function.update_self, mate_mate, Function.update_of_ne hmx,
          Function.update_self]
        exact iff_of_false (Option.some_ne_none _) (Option.some_ne_none _)
      · have hmcc : mate c ≠ mate x := fun h => hcx (mate_inj h)
        have hmcx : mate c ≠ x := by
          intro h
          apply hcmx
          have h2 := congrArg mate h
          rw [mate_mate] at h2
          exact h2
        rw [Function.update_of_ne hcmx, Function.update_of_ne hcx,
          Function.update_of_ne hmcc, Function.update_of_ne hmcx]
        exact hinv.1 c hc
  · -- the order-isomorphism is preserved
    intro c d vc vd vmc vmd hcd hc01 hvC hvD hvMC hvMD
    -- transfer the order-isomorphism via the functions "value of `e`" and
    -- "value of `mate e`" on the row of `x`
    set x' : {e : Cell // e.1 = x.1} := ⟨x, rfl⟩ with hx'
    set A₀ : {e : Cell // e.1 = x.1} → ℚ := fun e => (b₀ e.1).getD 0 with hA₀
    set B₀ : {e : Cell // e.1 = x.1} → ℚ := fun e => (b₀ (mate e.1)).getD 0 with hB₀
    set S : Set {e : Cell // e.1 = x.1} := {e | b₀ e.1 ≠ none} with hS
    have hxv : x'.1 = x := rfl
    have hAupd : (fun e : {e : Cell // e.1 = x.1} =>
          (Function.update (Function.update b₀ x (some vx)) (mate x) (some w) e.1).getD 0) =
        Function.update A₀ x' vx := by
      funext e
      by_cases he : e = x'
      · subst he
        show (Function.update (Function.update b₀ x (some vx)) (mate x) (some w) x'.1).getD 0 =
          Function.update A₀ x' vx x'
        rw [hxv, Function.update_self, Function.update_of_ne hmx, Function.update_self]
        rfl
      · rw [Function.update_of_ne he]
        show (Function.update (Function.update b₀ x (some vx)) (mate x) (some w) e.1).getD 0 =
          A₀ e
        have hex : e.1 ≠ x := fun hcon => he (Subtype.ext hcon)
        have hem : e.1 ≠ mate x := by
          intro hcon
          exact mate_fst_ne_self x hx01 (hcon ▸ e.2)
        rw [Function.update_of_ne hem, Function.update_of_ne hex]
    have hBupd : (fun e : {e : Cell // e.1 = x.1} =>
          (Function.update (Function.update b₀ x (some vx)) (mate x) (some w)
            (mate e.1)).getD 0) = Function.update B₀ x' w := by
      funext e
      by_cases he : e = x'
      · subst he
        show (Function.update (Function.update b₀ x (some vx)) (mate x) (some w)
          (mate x'.1)).getD 0 = Function.update B₀ x' w x'
        rw [hxv, Function.update_self, Function.update_self]
        rfl
      · rw [Function.update_of_ne he]
        show (Function.update (Function.update b₀ x (some vx)) (mate x) (some w)
          (mate e.1)).getD 0 = B₀ e
        have hemx : mate e.1 ≠ mate x := fun hcon => he (Subtype.ext (mate_inj hcon))
        have hex2 : mate e.1 ≠ x := by
          intro hcon
          have h1 : (mate e.1).1 ≠ (e.1).1 :=
            mate_fst_ne_self _ (by rw [e.2]; exact hx01)
          rw [hcon] at h1
          exact h1 e.2.symm
        rw [Function.update_of_ne hemx, Function.update_of_ne hex2]
    have hx'S : x' ∉ S := by
      intro hcon
      rw [hS, Set.mem_setOf_eq, hxv] at hcon
      exact hcon hx
    have hiso : ∀ c ∈ S, ∀ d ∈ S, (A₀ c < A₀ d ↔ B₀ c < B₀ d) := by
      intro c hc d hd
      rw [hS, Set.mem_setOf_eq] at hc hd
      obtain ⟨ac, hac⟩ : ∃ v, b₀ c.1 = some v := by
        cases hbo : b₀ c.1 with
        | none => exact absurd hbo hc
        | some v => exact ⟨v, rfl⟩
      obtain ⟨ad, had⟩ : ∃ v, b₀ d.1 = some v := by
        cases hbo : b₀ d.1 with
        | none => exact absurd hbo hd
        | some v => exact ⟨v, rfl⟩
      have hc01 : c.1.1.1 ≤ 1 := by rw [c.2]; exact hx01
      have hd01 : d.1.1.1 ≤ 1 := by rw [d.2]; exact hx01
      obtain ⟨amc, hamc⟩ : ∃ v, b₀ (mate c.1) = some v := by
        cases hbo : b₀ (mate c.1) with
        | none => exact absurd ((hinv.1 c.1 hc01).mpr hbo) hc
        | some v => exact ⟨v, rfl⟩
      obtain ⟨amd, hamd⟩ : ∃ v, b₀ (mate d.1) = some v := by
        cases hbo : b₀ (mate d.1) with
        | none => exact absurd ((hinv.1 d.1 hd01).mpr hbo) hd
        | some v => exact ⟨v, rfl⟩
      have hAc : A₀ c = ac := by
        show (b₀ c.1).getD 0 = ac
        rw [hac]
        rfl
      have hAd : A₀ d = ad := by
        show (b₀ d.1).getD 0 = ad
        rw [had]
        rfl
      have hBc : B₀ c = amc := by
        show (b₀ (mate c.1)).getD 0 = amc
        rw [hamc]
        rfl
      have hBd : B₀ d = amd := by
        show (b₀ (mate d.1)).getD 0 = amd
        rw [hamd]
        rfl
      rw [hAc, hAd, hBc, hBd]
      have hrow : c.1.1 = d.1.1 := c.2.trans d.2.symm
      exact hinv.2 c.1 d.1 ac ad amc amd hrow hc01 hac had hamc hamd
    have hnew : ∀ z ∈ S, (A₀ z < vx → B₀ z < w) ∧ (vx < A₀ z → w < B₀ z) := by
      intro z hz
      rw [hS, Set.mem_setOf_eq] at hz
      obtain ⟨az, haz⟩ : ∃ v, b₀ z.1 = some v := by
        cases hbo : b₀ z.1 with
        | none => exact absurd hbo hz
        | some v => exact ⟨v, rfl⟩
      have hz01 : z.1.1.1 ≤ 1 := by rw [z.2]; exact hx01
      obtain ⟨amz, hamz⟩ : ∃ v, b₀ (mate z.1) = some v := by
        cases hbo : b₀ (mate z.1) with
        | none => exact absurd ((hinv.1 z.1 hz01).mpr hbo) hz
        | some v => exact ⟨v, rfl⟩
      have hzx : z.1 ≠ x := fun h => hz (h.symm ▸ hx)
      have hmzx : mate z.1 ≠ x := by
        intro hcon
        apply hz
        have h2 : z.1 = mate x := by
          have h3 := congrArg mate hcon
          rw [mate_mate] at h3
          exact h3
        rw [h2]
        exact hxm
      have hb₁z : Function.update b₀ x (some vx) z.1 = some az := by
        rw [Function.update_of_ne hzx]
        exact haz
      have hb₁mz : Function.update b₀ x (some vx) (mate z.1) = some amz := by
        rw [Function.update_of_ne hmzx]
        exact hamz
      obtain ⟨h1, h2⟩ := hw.2 z.1 az amz z.2 hzx hb₁z hb₁mz
      have hAz : A₀ z = az := by
        show (b₀ z.1).getD 0 = az
        rw [haz]
        rfl
      have hBz : B₀ z = amz := by
        show (b₀ (mate z.1)).getD 0 = amz
        rw [hamz]
        rfl
      rw [hAz, hBz]
      exact ⟨h1, h2⟩
    have hA : ∀ z ∈ S, A₀ z ≠ vx := by
      intro z hz hcon
      rw [hS, Set.mem_setOf_eq] at hz
      obtain ⟨az, haz⟩ : ∃ v, b₀ z.1 = some v := by
        cases hbo : b₀ z.1 with
        | none => exact absurd hbo hz
        | some v => exact ⟨v, rfl⟩
      have hzx : z.1 ≠ x := fun h => hz (h.symm ▸ hx)
      have hAz : A₀ z = az := by
        show (b₀ z.1).getD 0 = az
        rw [haz]
        rfl
      rw [hAz] at hcon
      have hb₁z : Function.update b₀ x (some vx) z.1 = some vx := by
        rw [Function.update_of_ne hzx, haz, hcon]
      exact hzx (hinj z.1 x vx hb₁z (Function.update_self _ _ _))
    have hmain := orderIso_update A₀ B₀ S x' vx w hx'S hiso hnew hA
    by_cases hcx : c.1 = x.1
    · have hdx : d.1 = x.1 := hcd ▸ hcx
      set c' : {e : Cell // e.1 = x.1} := ⟨c, hcx⟩ with hcc'
      set d' : {e : Cell // e.1 = x.1} := ⟨d, hdx⟩ with hdd'
      have hc'mem : c' ∈ S ∪ {x'} := by
        by_cases hccx : c = x
        · exact Or.inr (Subtype.ext hccx)
        · apply Or.inl
          rw [hS, Set.mem_setOf_eq]
          have hcmx : c ≠ mate x := by
            intro hcon
            rw [hcon] at hcx
            exact mate_fst_ne_self x hx01 hcx
          have hc2 : Function.update (Function.update b₀ x (some vx)) (mate x) (some w) c ≠
              none := by
            rw [hvC]
            exact Option.some_ne_none _
          rw [Function.update_of_ne hcmx, Function.update_of_ne hccx] at hc2
          exact hc2
      have hd'mem : d' ∈ S ∪ {x'} := by
        by_cases hddx : d = x
        · exact Or.inr (Subtype.ext hddx)
        · apply Or.inl
          rw [hS, Set.mem_setOf_eq]
          have hdmx : d ≠ mate x := by
            intro hcon
            rw [hcon] at hdx
            exact mate_fst_ne_self x hx01 hdx
          have hd2 : Function.update (Function.update b₀ x (some vx)) (mate x) (some w) d ≠
              none := by
            rw [hvD]
            exact Option.some_ne_none _
          rw [Function.update_of_ne hdmx, Function.update_of_ne hddx] at hd2
          exact hd2
      have hstep := hmain c' hc'mem d' hd'mem
      have hAv : Function.update A₀ x' vx c' = vc := by
        rw [← hAupd]
        show (Function.update (Function.update b₀ x (some vx)) (mate x) (some w) c).getD 0 = vc
        rw [hvC]
        rfl
      have hAvd : Function.update A₀ x' vx d' = vd := by
        rw [← hAupd]
        show (Function.update (Function.update b₀ x (some vx)) (mate x) (some w) d).getD 0 = vd
        rw [hvD]
        rfl
      have hBv : Function.update B₀ x' w c' = vmc := by
        rw [← hBupd]
        show (Function.update (Function.update b₀ x (some vx)) (mate x) (some w)
          (mate c)).getD 0 = vmc
        rw [hvMC]
        rfl
      have hBvd : Function.update B₀ x' w d' = vmd := by
        rw [← hBupd]
        show (Function.update (Function.update b₀ x (some vx)) (mate x) (some w)
          (mate d)).getD 0 = vmd
        rw [hvMD]
        rfl
      rw [hAv, hAvd, hBv, hBvd] at hstep
      exact hstep
    · have hcx2 : c.1 = (mate x).1 := (mate_fst_ne_iff c x hc01 hx01).mp hcx
      have hdx2 : d.1 = (mate x).1 := hcd ▸ hcx2
      have hd01 : d.1.1 ≤ 1 := by rw [← hcd]; exact hc01
      have hmcx : (mate c).1 = x.1 := (mate_fst_eq_iff c x hc01 hx01).mpr hcx2
      have hmdx : (mate d).1 = x.1 := (mate_fst_eq_iff d x hd01 hx01).mpr hdx2
      set c' : {e : Cell // e.1 = x.1} := ⟨mate c, hmcx⟩ with hcc'
      set d' : {e : Cell // e.1 = x.1} := ⟨mate d, hmdx⟩ with hdd'
      have hc'mem : c' ∈ S ∪ {x'} := by
        by_cases hccx : mate c = x
        · exact Or.inr (Subtype.ext hccx)
        · apply Or.inl
          rw [hS, Set.mem_setOf_eq]
          have hcmx : mate c ≠ mate x := by
            intro hcon
            exact hcx (congrArg Prod.fst (mate_inj hcon))
          have hc2 : Function.update (Function.update b₀ x (some vx)) (mate x) (some w)
              (mate c) ≠ none := by
            rw [hvMC]
            exact Option.some_ne_none _
          rw [Function.update_of_ne hcmx, Function.update_of_ne hccx] at hc2
          exact hc2
      have hd'mem : d' ∈ S ∪ {x'} := by
        by_cases hddx : mate d = x
        · exact Or.inr (Subtype.ext hddx)
        · apply Or.inl
          rw [hS, Set.mem_setOf_eq]
          have hdmx : mate d ≠ mate x := by
            intro hcon
            exact absurd (congrArg Prod.fst (mate_inj hcon)) (hcd ▸ hcx)
          have hd2 : Function.update (Function.update b₀ x (some vx)) (mate x) (some w)
              (mate d) ≠ none := by
            rw [hvMD]
            exact Option.some_ne_none _
          rw [Function.update_of_ne hdmx, Function.update_of_ne hddx] at hd2
          exact hd2
      have hstep := hmain c' hc'mem d' hd'mem
      have hAv : Function.update A₀ x' vx c' = vmc := by
        rw [← hAupd]
        show (Function.update (Function.update b₀ x (some vx)) (mate x) (some w)
          (mate c)).getD 0 = vmc
        rw [hvMC]
        rfl
      have hAvd : Function.update A₀ x' vx d' = vmd := by
        rw [← hAupd]
        show (Function.update (Function.update b₀ x (some vx)) (mate x) (some w)
          (mate d)).getD 0 = vmd
        rw [hvMD]
        rfl
      have hBv : Function.update B₀ x' w c' = vc := by
        rw [← hBupd]
        show (Function.update (Function.update b₀ x (some vx)) (mate x) (some w)
          (mate (mate c))).getD 0 = vc
        rw [mate_mate, hvC]
        rfl
      have hBvd : Function.update B₀ x' w d' = vd := by
        rw [← hBupd]
        show (Function.update (Function.update b₀ x (some vx)) (mate x) (some w)
          (mate (mate d))).getD 0 = vd
        rw [mate_mate, hvD]
        rfl
      rw [hAv, hAvd, hBv, hBvd] at hstep
      exact hstep.symm

/-- Bob's invariant holds after each of his moves in every play that follows his
strategy. -/
lemma inv_prefBoard (p : Play) (hp : FollowsStrategy bobMove p) :
    ∀ m : ℕ, m ≤ 18 → Inv (prefBoard p (2 * m)) := by
  intro m
  induction m with
  | zero =>
    intro _
    constructor
    · intro c hc
      rw [prefBoard_zero, prefBoard_zero]
    · intro c d vc vd vmc vmd _ _ hC _ _ _
      rw [prefBoard_zero] at hC
      nomatch hC
  | succ m ih =>
    intro hm
    have hih := ih (by omega)
    have h0 : 2 * m < 36 := by omega
    have h1 : 2 * m + 1 < 36 := by omega
    set b₀ := prefBoard p (2 * m) with hb₀
    set b₁ := prefBoard p (2 * m + 1) with hb₁
    set x := (p.moves ⟨2 * m, h0⟩).1 with hx
    set vx := (p.moves ⟨2 * m, h0⟩).2 with hvx
    have hb₀x : b₀ x = none := prefBoard_apply_self p h0
    have hb₁eq : b₁ = Function.update b₀ x (some vx) := prefBoard_succ p h0
    have hb₁x : b₁ x = some vx := by
      rw [hb₁eq]
      exact Function.update_self _ _ _
    have hb₁inj : ∀ c d : Cell, ∀ v : ℚ, b₁ c = some v → b₁ d = some v → c = d :=
      fun c d v h1 h2 => prefBoard_inj h1 h2
    have hcons : p.moves ⟨2 * m + 1, h1⟩ = bobMove b₁ :=
      hp ⟨2 * m + 1, h1⟩ (⟨m, rfl⟩ : Odd (2 * m + 1))
    have hb₂eq : prefBoard p (2 * (m + 1)) =
        Function.update b₁ (p.moves ⟨2 * m + 1, h1⟩).1
          (some (p.moves ⟨2 * m + 1, h1⟩).2) := by
      have h2 : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
      rw [h2]
      exact prefBoard_succ p h1
    rw [hcons] at hb₂eq
    rw [hb₂eq]
    by_cases hx01 : x.1.1 ≤ 1
    · -- Alice played in the first two rows: Bob answers in the mate of her cell.
      have hxm : b₁ (mate x) = none := by
        rw [hb₁eq, Function.update_of_ne (mate_ne x hx01)]
        exact (hih.1 x hx01).mp hb₀x
      have huniq : ∀ y : Cell, y.1.1 ≤ 1 → b₁ y ≠ none → b₁ (mate y) = none → y = x := by
        intro y hy01 hys hym
        by_contra hyx
        have hb₀y : b₀ y ≠ none := by
          rw [hb₁eq, Function.update_of_ne hyx] at hys
          exact hys
        have hmyx : mate y ≠ x := by
          intro hcon
          apply hb₀y
          have h2 := congrArg mate hcon
          rw [mate_mate] at h2
          rw [h2]
          exact (hih.1 x hx01).mp hb₀x
        rw [hb₁eq, Function.update_of_ne hmyx] at hym
        exact hb₀y ((hih.1 y hy01).mpr hym)
      have hbm := bobMove_eq_mate hx01 (by rw [hb₁x]; exact Option.some_ne_none _) hxm huniq
      rw [hbm]
      have hex : ∃ w, GoodMateValue b₁ x vx w := exists_GoodMateValue hih hx01 hb₀x hb₁eq
      have hgood : GoodMateValue b₁ x vx (bobMateValue b₁ x) :=
        goodMateValue_bobMateValue hb₁x hex
      show Inv (Function.update b₁ (mate x) (some (bobMateValue b₁ x)))
      exact inv_update_mate hih hx01 hb₀x hb₁eq rfl hb₁inj hgood
    · -- Alice played in rows 3 to 6: Bob answers in rows 3 to 6.
      have hx2 : 2 ≤ x.1.1 := by omega
      have hnowit : ¬ ∃ y : Cell, y.1.1 ≤ 1 ∧ b₁ y ≠ none ∧ b₁ (mate y) = none := by
        rintro ⟨y, hy01, hys, hym⟩
        have hyx : y ≠ x := by
          intro h
          rw [h] at hy01
          omega
        rw [hb₁eq, Function.update_of_ne hyx] at hys
        have hmyx : mate y ≠ x := by
          intro h
          have h2 := mate_val_le y hy01
          rw [h] at h2
          omega
        rw [hb₁eq, Function.update_of_ne hmyx] at hym
        exact hys ((hih.1 y hy01).mpr hym)
      have hbm := bobMove_eq_rows2 hnowit
      rw [hbm]
      have hex2 : ∃ c : Cell, 2 ≤ c.1.1 ∧ b₁ c = none := by
        have hn36 : 2 * m + 1 ≤ 36 := by omega
        set F := filled p (2 * m + 1) hn36 with hF
        have hcardF : F.card = 2 * m + 1 := card_filled p _ hn36
        have hmemF : ∀ c : Cell, c ∈ F ↔ b₁ c ≠ none := fun c => mem_filled
        -- the invariant still holds after Alice's move (rows 0-1 were untouched)
        have hinvb₁ : Inv b₁ := by
          constructor
          · intro c hc
            have hcx : c ≠ x := by
              intro h
              rw [h] at hc
              omega
            have hmcx : mate c ≠ x := by
              intro h
              have h2 := mate_val_le c hc
              rw [h] at h2
              omega
            rw [hb₁eq, Function.update_of_ne hcx, Function.update_of_ne hmcx]
            exact hih.1 c hc
          · intro c d vc vd vmc vmd hcd hc01 hvC hvD hvMC hvMD
            have hcx : c ≠ x := by
              intro h
              rw [h] at hc01
              omega
            have hd01 : d.1.1 ≤ 1 := by rw [← hcd]; exact hc01
            have hdx : d ≠ x := by
              intro h
              rw [h] at hd01
              omega
            have hmcx : mate c ≠ x := by
              intro h
              have h2 := mate_val_le c hc01
              rw [h] at h2
              omega
            have hmdx : mate d ≠ x := by
              intro h
              have h2 := mate_val_le d hd01
              rw [h] at h2
              omega
            rw [hb₁eq, Function.update_of_ne hcx] at hvC
            rw [hb₁eq, Function.update_of_ne hdx] at hvD
            rw [hb₁eq, Function.update_of_ne hmcx] at hvMC
            rw [hb₁eq, Function.update_of_ne hmdx] at hvMD
            exact hih.2 c d vc vd vmc vmd hcd hc01 hvC hvD hvMC hvMD
        -- the part of the filled cells lying in rows 0-1 is mate-closed, hence even
        set S := F.filter (fun c => c.1.1 ≤ 1) with hS
        have hEvenS : Even S.card := by
          apply even_card_of_mate_closed
          · intro c hc
            exact (Finset.mem_filter.mp hc).2
          · intro c hc
            obtain ⟨hcF, hc01⟩ := Finset.mem_filter.mp hc
            apply Finset.mem_filter.mpr
            refine ⟨?_, mate_val_le c hc01⟩
            rw [hmemF] at hcF ⊢
            have hcl := hinvb₁.1 c hc01
            intro hcon
            exact hcF (hcl.mpr hcon)
        set T := F.filter (fun c => ¬ c.1.1 ≤ 1) with hT
        have hcardST : S.card + T.card = F.card := by
          rw [hS, hT]
          exact Finset.card_filter_add_card_filter_not _
        have hOddT : Odd T.card := by
          obtain ⟨k, hk⟩ := hEvenS
          rw [hcardF] at hcardST
          exact ⟨m - k, by omega⟩
        have hcardR : (Finset.univ.filter fun c : Cell => ¬ c.1.1 ≤ 1).card = 24 := by
          decide
        have hTR : T ⊆ Finset.univ.filter (fun c : Cell => ¬ c.1.1 ≤ 1) := by
          intro c hc
          obtain ⟨-, hc2⟩ := Finset.mem_filter.mp hc
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc2⟩
        have hTneR : T ≠ Finset.univ.filter (fun c : Cell => ¬ c.1.1 ≤ 1) := by
          intro hcon
          have h24 : T.card = 24 := by
            rw [hcon]
            exact hcardR
          obtain ⟨k, hk⟩ := hOddT
          omega
        have hss : T ⊂ Finset.univ.filter (fun c : Cell => ¬ c.1.1 ≤ 1) :=
          Finset.ssubset_iff_subset_ne.mpr ⟨hTR, hTneR⟩
        obtain ⟨c, hcR, hcT⟩ := Finset.exists_of_ssubset hss
        obtain ⟨-, hc2⟩ := Finset.mem_filter.mp hcR
        refine ⟨c, by omega, ?_⟩
        by_contra hcon
        apply hcT
        exact Finset.mem_filter.mpr ⟨(hmemF c).mpr hcon, hc2⟩
      obtain ⟨hc₂2, hc₂none⟩ := bobCell2_spec hex2
      show Inv (Function.update b₁ (bobCell2 b₁) (some (bobFreshValue b₁)))
      exact inv_update_rows2 hih hx2 hc₂2 hb₁eq rfl

snip end

/-- **USAMO 2004, Problem 4.** Bob (the second player) has a winning strategy:
whenever the play follows Bob's strategy `σ` of answering a move in the first two
rows by a suitable number in the paired cell (and playing anywhere in rows 3 to 6
otherwise), the final board has no black path from the top row to the bottom row,
so Alice cannot win. -/
problem usa2004_p4 :
    ∃ σ : (Cell → Option ℚ) → Cell × ℚ,
      ∀ p : Play, FollowsStrategy σ p → ¬ AliceWins (finalBoard p) := by
  refine ⟨bobMove, fun p hp => ?_⟩
  have hinv := inv_prefBoard p hp 18 le_rfl
  have hinj := finalBoard_inj p
  obtain ⟨c₀, hc₀r, hc₀B⟩ := exists_isBlack (finalBoard p) 0
  have hc₀v : c₀.1.1 = 0 := congrArg Fin.val hc₀r
  have hmB : IsBlack (finalBoard p) (mate c₀) := by
    intro d hd
    have hmcv : (mate c₀).1.1 = 1 := mate_val_eq_of0 c₀ hc₀v
    have hdv : d.1.1 = 1 := by rw [hd]; exact hmcv
    have hmdv : (mate d).1.1 = 0 := mate_val_eq_of1 d hdv
    have hmdr : (mate d).1 = c₀.1 := Fin.ext (by rw [hmdv, hc₀v])
    have hle : finalBoard p (mate d) ≤ finalBoard p c₀ := hc₀B (mate d) hmdr
    by_cases heq : mate d = c₀
    · have hd' : d = mate c₀ := by
        have h2 := congrArg mate heq
        rw [mate_mate] at h2
        exact h2
      rw [hd']
    · have hlt : finalBoard p (mate d) < finalBoard p c₀ :=
        lt_of_le_of_ne hle (fun h => heq (hinj h))
      have h01 : (mate d).1.1 ≤ 1 := by rw [hmdv]; omega
      have hiso := hinv.2 (mate d) c₀ (finalBoard p (mate d)) (finalBoard p c₀)
        (finalBoard p d) (finalBoard p (mate c₀)) hmdr h01
        (prefBoard_finalBoard p (mate d)) (prefBoard_finalBoard p c₀) ?_ ?_
      · exact (hiso.mp hlt).le
      · rw [mate_mate]
        exact prefBoard_finalBoard p d
      · exact prefBoard_finalBoard p (mate c₀)
  exact not_aliceWins (finalBoard p) hinj c₀ hc₀v hc₀B hmB

end Usa2004P4
