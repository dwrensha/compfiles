/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Bounds.Defs
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 2018, Problem 4

A site is any point (x, y) in the plane for which x, y ∈ {1, . . . , 20}.
Initially, each of the 400 sites is unoccupied. Amy and Ben take turns
placing stones on unoccupied sites, with Amy going first; Amy has the
additional restriction that no two of her stones may be at a distance
equal to √5. They stop once either player cannot move. Find the greatest
K such that Amy can ensure that she places at least K stones.

## Formalization notes

* We use 0-indexed coordinates, so a site is an element of
  `Fin 20 × Fin 20`.
* Two sites are at distance `√5` exactly when they are a knight's move
  apart: their coordinate differences are 1 and 2 in some order
  (`KnightAdj`).
* `CanEnsure K fuel red blue` says that from the position with red
  stones on `red`, blue stones on `blue`, and Amy to move, Amy can
  ensure that she places at least `K` stones in total. The `fuel`
  parameter bounds the number of rounds left to play; every round
  occupies two new sites, so `CanEnsure K 400 ∅ ∅` (with fuel exceeding
  any possible length of play) is the exact game-theoretic meaning of
  "Amy can ensure at least `K` stones", abbreviated `AmyEnsures K`.

The answer is `K = 100`.
-/

namespace Imo2018P4

/-- A site on the board: the 0-indexed version of `{1, ..., 20}²`. -/
abbrev Site : Type := Fin 20 × Fin 20

/-- Two sites are at distance `√5` iff they are a knight's move apart,
i.e. their coordinate differences are `(±1, ±2)` or `(±2, ±1)`. -/
def KnightAdj (a b : Site) : Prop :=
  (a.1.val + 1 = b.1.val ∧ a.2.val + 2 = b.2.val) ∨
  (a.1.val + 2 = b.1.val ∧ a.2.val + 1 = b.2.val) ∨
  (a.1.val + 1 = b.1.val ∧ b.2.val + 2 = a.2.val) ∨
  (a.1.val + 2 = b.1.val ∧ b.2.val + 1 = a.2.val) ∨
  (b.1.val + 1 = a.1.val ∧ a.2.val + 2 = b.2.val) ∨
  (b.1.val + 2 = a.1.val ∧ a.2.val + 1 = b.2.val) ∨
  (b.1.val + 1 = a.1.val ∧ b.2.val + 2 = a.2.val) ∨
  (b.1.val + 2 = a.1.val ∧ b.2.val + 1 = a.2.val)

instance (a b : Site) : Decidable (KnightAdj a b) := by
  unfold KnightAdj; infer_instance

/-- The sites on which Amy may place a stone: the unoccupied sites at
distance different from `√5` from every red stone. -/
def amyMoves (red blue : Finset Site) : Finset Site :=
  (Finset.univ \ (red ∪ blue)).filter fun a => ∀ r ∈ red, ¬ KnightAdj a r

/-- The sites on which Ben may place a stone: all unoccupied sites. -/
def benMoves (red blue : Finset Site) : Finset Site :=
  Finset.univ \ (red ∪ blue)

/-- With `fuel` rounds left to play, Amy can ensure from the position
`(red, blue)` (with Amy to move) that she places at least `K` stones in
total. (An inductive predicate so that definitions and proofs do not
have to unfold a recursion on the `fuel` parameter.) -/
inductive CanEnsure (K : ℕ) : ℕ → Finset Site → Finset Site → Prop
  /-- If Amy already has `K` stones, she is done. -/
  | zero {red blue : Finset Site} (h : K ≤ red.card) : CanEnsure K 0 red blue
  /-- If Amy has no legal move, the game stops; she needs to already
  have `K` stones. -/
  | of_no_move {fuel : ℕ} {red blue : Finset Site} (hm : amyMoves red blue = ∅)
      (h : K ≤ red.card) : CanEnsure K (fuel + 1) red blue
  /-- Amy plays `a`; if Ben cannot reply the game stops and she needs
  `K` stones; otherwise she must still ensure `K` stones after every
  reply of Ben. -/
  | of_move {fuel : ℕ} {red blue : Finset Site} {a : Site} (ha : a ∈ amyMoves red blue)
      (hend : benMoves (insert a red) blue = ∅ → K ≤ (insert a red).card)
      (hcont : ∀ b ∈ benMoves (insert a red) blue,
        CanEnsure K fuel (insert a red) (insert b blue)) :
      CanEnsure K (fuel + 1) red blue

/-- Amy can ensure that she places at least `K` stones. (400 rounds of
fuel exceeds any possible length of play, since every round occupies two
new sites of the 400.) -/
def AmyEnsures (K : ℕ) : Prop := CanEnsure K 400 ∅ ∅

snip begin

/-
We follow the official solution (as presented in Evan Chen's IMO 2018
solution notes, https://web.evanchen.cc/exams/IMO-2018-notes.pdf).
The answer is K = 100.

* Amy can always place at least 100 stones: she only ever plays on the
  black squares of the checkerboard coloring. No two black squares are
  at knight's move distance, and there are 200 of them, so she gets at
  least half of them.

* Ben can prevent Amy from placing more than 100 stones: partition the
  board into 4×4 blocks and label each block as
  ```
  1 2 3 4
  3 4 1 2
  2 1 4 3
  4 3 2 1
  ```
  The four squares with each label form a 4-cycle of knight's moves.
  Whenever Amy plays in a cycle, Ben plays the opposite site of the
  cycle, which prevents Amy from ever playing another stone in that
  cycle. Hence Amy plays at most one stone in each of the 100 cycles.
-/

/-! ### The checkerboard coloring (Amy's strategy) -/

/-- The black squares of the checkerboard coloring. -/
def blacks : Finset Site := Finset.univ.filter fun c => (c.1.val + c.2.val) % 2 = 0

lemma blacks_card : blacks.card = 200 := by
  have h400 : (Finset.univ : Finset Site).card = 400 := by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset Site)) (p := fun c : Site => (c.1.val + c.2.val) % 2 = 0)
  rw [h400] at hsum
  have hbij : (Finset.univ.filter fun c : Site => (c.1.val + c.2.val) % 2 = 0).card =
      (Finset.univ.filter fun c : Site => ¬ (c.1.val + c.2.val) % 2 = 0).card := by
    apply Finset.card_bij (fun c _ => (c.1, ⟨19 - c.2.val, by have := c.2.isLt; omega⟩))
    · intro c hc
      have hc' : (c.1.val + c.2.val) % 2 = 0 := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
        exact hc
      have := c.2.isLt
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      show ¬ (c.1.val + (19 - c.2.val)) % 2 = 0
      omega
    · intro a _ b _ h
      obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h
      have h2' : 19 - a.2.val = 19 - b.2.val := Fin.mk.inj_iff.mp h2
      have := a.2.isLt
      have := b.2.isLt
      exact Prod.ext h1 (Fin.ext (by omega))
    · intro d hd
      have hd' : ¬ (d.1.val + d.2.val) % 2 = 0 := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
        exact hd
      have := d.2.isLt
      refine ⟨(d.1, ⟨19 - d.2.val, by omega⟩), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        show (d.1.val + (19 - d.2.val)) % 2 = 0
        omega
      · show (d.1, ⟨19 - (19 - d.2.val), by omega⟩) = d
        apply Prod.ext
        · rfl
        · apply Fin.ext
          show 19 - (19 - d.2.val) = d.2.val
          omega
  unfold blacks
  omega

/-- No two black squares are at knight's move distance. -/
lemma not_knightAdj_of_black {a b : Site} (ha : a ∈ blacks) (hb : b ∈ blacks) :
    ¬ KnightAdj a b := by
  simp only [blacks, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  intro h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/-- Every unoccupied black square is a legal move for Amy. -/
lemma black_sdiff_subset_amyMoves {red blue : Finset Site} (hsub : red ⊆ blacks) :
    blacks \ (red ∪ blue) ⊆ amyMoves red blue := by
  intro a ha
  rw [Finset.mem_sdiff] at ha
  simp only [amyMoves, Finset.mem_filter, Finset.mem_sdiff]
  exact ⟨⟨Finset.mem_univ a, ha.2⟩, fun r hr => not_knightAdj_of_black ha.1 (hsub hr)⟩

/-! ### The 4-cycles (Ben's strategy) -/

/-- The label (`0`–`3`) of a cell within its `4×4` block, from the pattern
```
1 2 3 4
3 4 1 2
2 1 4 3
4 3 2 1
```
(read with 1-indexed labels in the official solution). -/
def lab : ℕ → ℕ → ℕ
  | 0, 0 => 0 | 0, 1 => 1 | 0, 2 => 2 | 0, 3 => 3
  | 1, 0 => 2 | 1, 1 => 3 | 1, 2 => 0 | 1, 3 => 1
  | 2, 0 => 1 | 2, 1 => 0 | 2, 2 => 3 | 2, 3 => 2
  | 3, 0 => 3 | 3, 1 => 2 | 3, 2 => 1 | 3, 3 => 0
  | _, _ => 0

/-- Each label is at most `3`. -/
lemma lab_le : ∀ i j : Fin 4, lab i.val j.val ≤ 3 := by decide

/-- Opposite cells of a `4×4` block carry the same label. -/
lemma lab_opp : ∀ i j : Fin 4, lab (3 - i.val) (3 - j.val) = lab i.val j.val := by
  decide

/-- Two cells of a `4×4` block with the same label are either equal,
opposite, or a knight's move apart within the block. -/
lemma lab_eq_cases : ∀ i j i' j' : Fin 4,
    lab i.val j.val = lab i'.val j'.val →
    (i = i' ∧ j = j') ∨ (i.val = 3 - i'.val ∧ j.val = 3 - j'.val) ∨
    ((i.val + 1 = i'.val ∧ j.val + 2 = j'.val) ∨
     (i.val + 2 = i'.val ∧ j.val + 1 = j'.val) ∨
     (i.val + 1 = i'.val ∧ j'.val + 2 = j.val) ∨
     (i.val + 2 = i'.val ∧ j'.val + 1 = j.val) ∨
     (i'.val + 1 = i.val ∧ j.val + 2 = j'.val) ∨
     (i'.val + 2 = i.val ∧ j.val + 1 = j'.val) ∨
     (i'.val + 1 = i.val ∧ j'.val + 2 = j.val) ∨
     (i'.val + 2 = i.val ∧ j'.val + 1 = j.val)) := by
  decide

/-- The 4-cycle (one of 100) that a site belongs to: its `4×4` block
together with its label within the block. -/
def cyc (c : Site) : ℕ :=
  (c.1.val / 4 * 5 + c.2.val / 4) * 4 + lab (c.1.val % 4) (c.2.val % 4)

lemma cyc_lt_100 : ∀ c : Site, cyc c < 100 := by
  intro c
  have := c.1.isLt
  have := c.2.isLt
  have hlab : lab (c.1.val % 4) (c.2.val % 4) ≤ 3 :=
    lab_le ⟨c.1.val % 4, Nat.mod_lt _ (by omega)⟩
      ⟨c.2.val % 4, Nat.mod_lt _ (by omega)⟩
  unfold cyc
  omega

/-- The opposite coordinate within a `4×4` block: `i ↦ 3 − i` within
the block. -/
def oppCoord (x : ℕ) : ℕ := 4 * (x / 4) + (3 - x % 4)

lemma oppCoord_lt {x : ℕ} (hx : x < 20) : oppCoord x < 20 := by
  unfold oppCoord; omega

/-- The opposite site of a site in its 4-cycle: the two sites of the
cycle that are *not* a knight's move apart. -/
def opp (c : Site) : Site :=
  (⟨oppCoord c.1.val, oppCoord_lt c.1.isLt⟩, ⟨oppCoord c.2.val, oppCoord_lt c.2.isLt⟩)

lemma opp_ne : ∀ c : Site, opp c ≠ c := by
  intro c h
  have h1 : c.1.val = (opp c).1.val := by rw [h]
  have h2 : c.1.val = 4 * (c.1.val / 4) + (3 - c.1.val % 4) := h1
  omega

lemma opp_opp : ∀ c : Site, opp (opp c) = c := by
  intro c
  have key : ∀ x : ℕ, x < 20 → oppCoord (oppCoord x) = x := by
    intro x hx
    unfold oppCoord
    omega
  exact Prod.ext (Fin.ext (key c.1.val c.1.isLt)) (Fin.ext (key c.2.val c.2.isLt))

lemma cyc_opp : ∀ c : Site, cyc (opp c) = cyc c := by
  intro c
  have := c.1.isLt
  have := c.2.isLt
  have hd1 : (opp c).1.val / 4 = c.1.val / 4 ∧ (opp c).1.val % 4 = 3 - c.1.val % 4 := by
    show (4 * (c.1.val / 4) + (3 - c.1.val % 4)) / 4 = c.1.val / 4 ∧
      (4 * (c.1.val / 4) + (3 - c.1.val % 4)) % 4 = 3 - c.1.val % 4
    omega
  have hd2 : (opp c).2.val / 4 = c.2.val / 4 ∧ (opp c).2.val % 4 = 3 - c.2.val % 4 := by
    show (4 * (c.2.val / 4) + (3 - c.2.val % 4)) / 4 = c.2.val / 4 ∧
      (4 * (c.2.val / 4) + (3 - c.2.val % 4)) % 4 = 3 - c.2.val % 4
    omega
  have hlab : lab ((opp c).1.val % 4) ((opp c).2.val % 4) =
      lab (c.1.val % 4) (c.2.val % 4) := by
    rw [hd1.2, hd2.2]
    exact lab_opp ⟨c.1.val % 4, Nat.mod_lt _ (by omega)⟩
      ⟨c.2.val % 4, Nat.mod_lt _ (by omega)⟩
  unfold cyc
  rw [hd1.1, hd2.1, hlab]

/-- Two sites in the same 4-cycle are either equal, opposite, or a
knight's move apart. -/
lemma eq_or_opp_or_adj_of_cyc_eq :
    ∀ a b : Site, cyc a = cyc b → a = b ∨ a = opp b ∨ KnightAdj a b := by
  intro a b h
  have := a.1.isLt
  have := a.2.isLt
  have := b.1.isLt
  have := b.2.isLt
  have hla : lab (a.1.val % 4) (a.2.val % 4) ≤ 3 :=
    lab_le ⟨a.1.val % 4, Nat.mod_lt _ (by omega)⟩
      ⟨a.2.val % 4, Nat.mod_lt _ (by omega)⟩
  have hlb : lab (b.1.val % 4) (b.2.val % 4) ≤ 3 :=
    lab_le ⟨b.1.val % 4, Nat.mod_lt _ (by omega)⟩
      ⟨b.2.val % 4, Nat.mod_lt _ (by omega)⟩
  unfold cyc at h
  have hblk : a.1.val / 4 = b.1.val / 4 ∧ a.2.val / 4 = b.2.val / 4 := by omega
  have hlab : lab (a.1.val % 4) (a.2.val % 4) = lab (b.1.val % 4) (b.2.val % 4) := by
    omega
  rcases lab_eq_cases ⟨a.1.val % 4, Nat.mod_lt _ (by omega)⟩
      ⟨a.2.val % 4, Nat.mod_lt _ (by omega)⟩ ⟨b.1.val % 4, Nat.mod_lt _ (by omega)⟩
      ⟨b.2.val % 4, Nat.mod_lt _ (by omega)⟩ hlab with hc | hc | hc
  · -- The in-block offsets agree, so the sites are equal.
    obtain ⟨hi, hj⟩ := hc
    have hi' : a.1.val % 4 = b.1.val % 4 := congrArg Fin.val hi
    have hj' : a.2.val % 4 = b.2.val % 4 := congrArg Fin.val hj
    exact Or.inl (Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega)))
  · -- The in-block offsets are opposite, so the sites are opposite.
    obtain ⟨hi, hj⟩ := hc
    have hi' : a.1.val % 4 = 3 - b.1.val % 4 := hi
    have hj' : a.2.val % 4 = 3 - b.2.val % 4 := hj
    have e1 : a.1.val = oppCoord b.1.val := by unfold oppCoord; omega
    have e2 : a.2.val = oppCoord b.2.val := by unfold oppCoord; omega
    exact Or.inr (Or.inl (Prod.ext (Fin.ext e1) (Fin.ext e2)))
  · -- The in-block offsets are a knight's move apart, and so are the sites.
    refine Or.inr (Or.inr ?_)
    unfold KnightAdj
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have h1' : a.1.val % 4 + 1 = b.1.val % 4 := h1
      have h2' : a.2.val % 4 + 2 = b.2.val % 4 := h2
      exact Or.inl ⟨by omega, by omega⟩
    · have h1' : a.1.val % 4 + 2 = b.1.val % 4 := h1
      have h2' : a.2.val % 4 + 1 = b.2.val % 4 := h2
      exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    · have h1' : a.1.val % 4 + 1 = b.1.val % 4 := h1
      have h2' : b.2.val % 4 + 2 = a.2.val % 4 := h2
      exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))
    · have h1' : a.1.val % 4 + 2 = b.1.val % 4 := h1
      have h2' : b.2.val % 4 + 1 = a.2.val % 4 := h2
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))
    · have h1' : b.1.val % 4 + 1 = a.1.val % 4 := h1
      have h2' : a.2.val % 4 + 2 = b.2.val % 4 := h2
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))
    · have h1' : b.1.val % 4 + 2 = a.1.val % 4 := h1
      have h2' : a.2.val % 4 + 1 = b.2.val % 4 := h2
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))
    · have h1' : b.1.val % 4 + 1 = a.1.val % 4 := h1
      have h2' : b.2.val % 4 + 2 = a.2.val % 4 := h2
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))))
    · have h1' : b.1.val % 4 + 2 = a.1.val % 4 := h1
      have h2' : b.2.val % 4 + 1 = a.2.val % 4 := h2
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))))

/-- Ben's invariant: every 4-cycle contains at most one red stone, and
the blue stones are exactly the opposite sites of the red stones. -/
def BenInv (red blue : Finset Site) : Prop :=
  (∀ a ∈ red, opp a ∈ blue) ∧ (∀ b ∈ blue, opp b ∈ red) ∧
    ∀ a ∈ red, ∀ b ∈ red, cyc a = cyc b → a = b

lemma benInv_empty : BenInv ∅ ∅ :=
  ⟨fun a ha => absurd ha (Finset.notMem_empty a),
   fun b hb => absurd hb (Finset.notMem_empty b),
   fun a ha _ _ _ => absurd ha (Finset.notMem_empty a)⟩

/-- Under Ben's invariant there is at most one red stone per 4-cycle,
hence at most 100 red stones. -/
lemma card_le_100_of_benInv {red blue : Finset Site} (h : BenInv red blue) :
    red.card ≤ 100 := by
  have hinj : Set.InjOn cyc red := fun a ha b hb hab => h.2.2 a ha b hb hab
  rw [← Finset.card_image_of_injOn hinj, ← Finset.card_range 100]
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_image] at hx
  obtain ⟨c, _, rfl⟩ := hx
  exact Finset.mem_range.mpr (cyc_lt_100 c)

/-! ### Game lemmas -/

lemma insert_union_insert (a b : Site) (s t : Finset Site) :
    insert a s ∪ insert b t = insert a (insert b (s ∪ t)) := by
  rw [Finset.insert_union, Finset.union_insert]

/-- Once Amy has `K` stones she keeps them: the game can only add red
stones. -/
lemma canEnsure_of_card_le {K : ℕ} :
    ∀ {fuel : ℕ} {red blue : Finset Site}, K ≤ red.card → CanEnsure K fuel red blue := by
  intro fuel; induction fuel with
  | zero => intro red blue h; exact .zero h
  | succ fuel ih =>
      intro red blue h
      by_cases hm : amyMoves red blue = ∅
      · exact .of_no_move hm h
      · obtain ⟨a, ha⟩ := Finset.nonempty_of_ne_empty hm
        have hle : red.card ≤ (insert a red).card :=
          Finset.card_le_card (Finset.subset_insert _ _)
        exact .of_move ha (fun _ => h.trans hle) (fun _ _ => ih (h.trans hle))

/-- Ensuring more stones is harder. -/
lemma canEnsure_mono {fuel : ℕ} {red blue : Finset Site} {K K' : ℕ}
    (h : CanEnsure K fuel red blue) (hle : K' ≤ K) : CanEnsure K' fuel red blue := by
  induction h with
  | zero h => exact .zero (hle.trans h)
  | of_no_move hm h => exact .of_no_move hm (hle.trans h)
  | of_move ha hend hcont ih =>
      exact .of_move ha (fun hb => hle.trans (hend hb)) ih

/-- Amy's strategy: always play on a black square. With the potential
`2 * red.card + (blacks \ (red ∪ blue)).card` Amy ensures half of what
remains of the 200 black squares. -/
lemma canEnsure_of_black {K : ℕ} :
    ∀ {fuel : ℕ} {red blue : Finset Site},
      red ⊆ blacks → (benMoves red blue).card ≤ fuel →
      2 * K ≤ 2 * red.card + (blacks \ (red ∪ blue)).card →
      CanEnsure K fuel red blue := by
  intro fuel; induction fuel with
  | zero =>
      intro red blue hsub hfuel hpot
      have hB : benMoves red blue = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hfuel)
      have hS0 : blacks \ (red ∪ blue) = ∅ := by
        have hss : blacks \ (red ∪ blue) ⊆ benMoves red blue :=
          Finset.sdiff_subset_sdiff (Finset.subset_univ _) le_rfl
        rw [hB] at hss
        exact Finset.subset_empty.mp hss
      rw [hS0, Finset.card_empty] at hpot
      exact .zero (by omega)
  | succ fuel ih =>
      intro red blue hsub hfuel hpot
      by_cases hKle : K ≤ red.card
      · exact canEnsure_of_card_le hKle
      · -- Here `K > red.card`, so at least two black sites are still free.
        have hm2 : 2 ≤ (blacks \ (red ∪ blue)).card := by omega
        obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < (blacks \ (red ∪ blue)).card)
        have hab : a ∈ blacks := (Finset.mem_sdiff.mp ha).1
        have haX : a ∉ red ∪ blue := (Finset.mem_sdiff.mp ha).2
        have har : a ∉ red := fun hr => haX (Finset.mem_union.mpr (Or.inl hr))
        have ha_amy : a ∈ amyMoves red blue := black_sdiff_subset_amyMoves hsub ha
        have hcard : (insert a red).card = red.card + 1 :=
          Finset.card_insert_of_notMem har
        refine .of_move ha_amy ?_ ?_
        · -- If Ben cannot reply, the game ends; Amy still has `K` stones.
          intro hB2
          have hsub2 : blacks \ (insert a red ∪ blue) ⊆ benMoves (insert a red) blue :=
            Finset.sdiff_subset_sdiff (Finset.subset_univ _) le_rfl
          rw [hB2, Finset.subset_empty, Finset.insert_union, Finset.sdiff_insert] at hsub2
          have h0 : ((blacks \ (red ∪ blue)).erase a).card = 0 :=
            Finset.card_eq_zero.mpr hsub2
          rw [Finset.card_erase_of_mem ha] at h0
          omega
        · -- Ben replies `b`; the potential is preserved.
          intro b hb
          have hb' : b ∉ insert a red ∪ blue := by
            have hb1 : b ∈ benMoves (insert a red) blue := hb
            simp only [benMoves, Finset.mem_sdiff, Finset.mem_univ, true_and] at hb1
            exact hb1
          have hbX : b ∉ red ∪ blue := by
            intro h
            apply hb'
            rcases Finset.mem_union.mp h with hr | hb2
            · exact Finset.mem_union.mpr (Or.inl (Finset.mem_insert_of_mem hr))
            · exact Finset.mem_union.mpr (Or.inr hb2)
          have hba : b ≠ a := by
            intro h
            apply hb'
            rw [h]
            exact Finset.mem_union.mpr (Or.inl (Finset.mem_insert_self a red))
          have hsub' : insert a red ⊆ blacks := Finset.insert_subset hab hsub
          have hB' : (benMoves (insert a red) (insert b blue)).card =
              (benMoves red blue).card - 1 - 1 := by
            have hbmem : b ∈ Finset.univ \ (red ∪ blue) :=
              Finset.mem_sdiff.mpr ⟨Finset.mem_univ b, hbX⟩
            have hamem : a ∈ (Finset.univ \ (red ∪ blue)).erase b :=
              Finset.mem_erase.mpr ⟨hba.symm,
                Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, haX⟩⟩
            simp only [benMoves]
            rw [insert_union_insert, Finset.sdiff_insert, Finset.sdiff_insert,
              Finset.card_erase_of_mem hamem, Finset.card_erase_of_mem hbmem]
          have hfuel' : (benMoves (insert a red) (insert b blue)).card ≤ fuel := by
            rw [hB']; omega
          have hS' : (blacks \ (red ∪ blue)).card ≤
              (blacks \ (insert a red ∪ insert b blue)).card + 2 := by
            rw [insert_union_insert, Finset.sdiff_insert, Finset.sdiff_insert]
            by_cases hbb : b ∈ blacks \ (red ∪ blue)
            · rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hba.symm, ha⟩),
                Finset.card_erase_of_mem hbb]
              omega
            · rw [Finset.erase_eq_of_notMem hbb, Finset.card_erase_of_mem ha]
              omega
          have hpot' : 2 * K ≤ 2 * (insert a red).card +
              (blacks \ (insert a red ∪ insert b blue)).card := by
            rw [hcard]; omega
          exact ih hsub' hfuel' hpot'

/-- Ben's strategy: always reply with the opposite site of the 4-cycle in
which Amy just played. Then every 4-cycle contains at most one red
stone, so Amy places at most 100 stones. -/
lemma not_canEnsure_101_of_benInv :
    ∀ {fuel : ℕ} {red blue : Finset Site},
      BenInv red blue → ¬ CanEnsure 101 fuel red blue := by
  intro fuel; induction fuel with
  | zero =>
      intro red blue h hc
      have hle100 := card_le_100_of_benInv h
      cases hc with
      | zero hcard => omega
  | succ fuel ih =>
      intro red blue h hc
      cases hc
      case of_no_move hm hcard =>
          have hle100 := card_le_100_of_benInv h
          omega
      case of_move a ha hend hcont =>
        simp only [amyMoves, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
          true_and] at ha
        obtain ⟨haX, ha_adj⟩ := ha
        have har : a ∉ red := fun hr => haX (Finset.mem_union.mpr (Or.inl hr))
        have habl : a ∉ blue := fun hb => haX (Finset.mem_union.mpr (Or.inr hb))
        have hopp_red : opp a ∉ red := by
          intro hr
          have hb2 : opp (opp a) ∈ blue := h.1 (opp a) hr
          rw [opp_opp] at hb2
          exact habl hb2
        have hopp_blue : opp a ∉ blue := by
          intro hb
          have hr2 : opp (opp a) ∈ red := h.2.1 (opp a) hb
          rw [opp_opp] at hr2
          exact har hr2
        have hopp_mem : opp a ∈ benMoves (insert a red) blue := by
          simp only [benMoves, Finset.mem_sdiff, Finset.mem_univ, true_and,
            Finset.mem_union, Finset.mem_insert, not_or]
          exact ⟨⟨opp_ne a, hopp_red⟩, hopp_blue⟩
        have hInv' : BenInv (insert a red) (insert (opp a) blue) := by
          refine ⟨?_, ?_, ?_⟩
          · intro x hx
            rcases Finset.mem_insert.mp hx with hxa | hxr
            · subst x
              exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem (h.1 x hxr)
          · intro y hy
            rcases Finset.mem_insert.mp hy with hya | hyb
            · subst y
              rw [opp_opp]
              exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem (h.2.1 y hyb)
          · intro x hx y hy hcyc
            rcases Finset.mem_insert.mp hx with hxa | hxr
            · subst x
              rcases Finset.mem_insert.mp hy with hya | hyr
              · subst y
                rfl
              · rcases eq_or_opp_or_adj_of_cyc_eq a y hcyc with h' | h' | h'
                · exact h'
                · exfalso
                  have hya2 : y = opp a := by conv_lhs => rw [← opp_opp y, ← h']
                  exact hopp_red (hya2 ▸ hyr)
                · exact absurd h' (ha_adj y hyr)
            · rcases Finset.mem_insert.mp hy with hya | hyr
              · subst y
                rcases eq_or_opp_or_adj_of_cyc_eq a x hcyc.symm with h' | h' | h'
                · exact h'.symm
                · exfalso
                  have hxa2 : x = opp a := by conv_lhs => rw [← opp_opp x, ← h']
                  exact hopp_red (hxa2 ▸ hxr)
                · exact absurd h' (ha_adj x hxr)
              · exact h.2.2 x hxr y hyr hcyc
        exact ih hInv' (hcont (opp a) hopp_mem)

snip end

determine answer : ℕ := 100

problem imo2018_p4 : IsGreatest {K | AmyEnsures K} answer := by
  have h100 : CanEnsure 100 400 ∅ ∅ := by
    refine canEnsure_of_black (Finset.empty_subset blacks) ?_ ?_
    · have h : (benMoves ∅ ∅).card = 400 := by
        simp [benMoves, Fintype.card_prod, Fintype.card_fin]
      exact h.le
    · simp [blacks_card]
  have hnot : ¬ CanEnsure 101 400 ∅ ∅ := not_canEnsure_101_of_benInv benInv_empty
  refine ⟨?_, fun K hK => ?_⟩
  · exact h100
  · show K ≤ 100
    by_contra hlt
    rw [not_le] at hlt
    have hK' : CanEnsure K 400 ∅ ∅ := hK
    have h101 : CanEnsure 101 400 ∅ ∅ := canEnsure_mono hK' hlt
    exact hnot h101

end Imo2018P4
