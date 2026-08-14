/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2000, Problem 4

Find the smallest positive integer $n$ such that if $n$ squares of a
$1000 \times 1000$ chessboard are colored, then there will exist three
colored squares whose centers form a right triangle with sides parallel
to the edges of the board.
-/

namespace Usa2000P4

/-- A set `S` of squares on an `m × n` board contains no forbidden triangle:
one cannot find three (distinct) chosen squares whose centers form a right
triangle with sides parallel to the edges of the board, that is, with two of
them in the same row and two of them in the same column. -/
def Good {m n : ℕ} (S : Finset (Fin m × Fin n)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x ≠ y → y ≠ z → x ≠ z →
    ¬((x.1 = y.1 ∨ x.1 = z.1 ∨ y.1 = z.1) ∧ (x.2 = y.2 ∨ x.2 = z.2 ∨ y.2 = z.2))

snip begin

/-- The squares of `S` lying in row `r`. -/
def rowFiber {m n : ℕ} (S : Finset (Fin m × Fin n)) (r : Fin m) : Finset (Fin m × Fin n) :=
  S.filter fun s ↦ s.1 = r

/-- The squares of `S` lying in column `c`. -/
def colFiber {m n : ℕ} (S : Finset (Fin m × Fin n)) (c : Fin n) : Finset (Fin m × Fin n) :=
  S.filter fun s ↦ s.2 = c

lemma mem_rowFiber {m n : ℕ} {S : Finset (Fin m × Fin n)} {r : Fin m} {s : Fin m × Fin n} :
    s ∈ rowFiber S r ↔ s ∈ S ∧ s.1 = r := Finset.mem_filter

lemma mem_colFiber {m n : ℕ} {S : Finset (Fin m × Fin n)} {c : Fin n} {s : Fin m × Fin n} :
    s ∈ colFiber S c ↔ s ∈ S ∧ s.2 = c := Finset.mem_filter

/-- Any subset of a good set is good. -/
lemma Good.mono {m n : ℕ} {S T : Finset (Fin m × Fin n)} (hTS : T ⊆ S) (hS : Good S) :
    Good T :=
  fun x hx y hy z hz ↦ hS x (hTS hx) y (hTS hy) z (hTS hz)

/-- In a good set, every chosen square is the unique chosen square of its row
or the unique chosen square of its column: otherwise the square together with
a different chosen square in its row and a different chosen square in its
column would form a forbidden configuration. -/
lemma alone_of_good {m n : ℕ} {S : Finset (Fin m × Fin n)} (hS : Good S)
    {s : Fin m × Fin n} (hs : s ∈ S) :
    (∀ t ∈ S, t.1 = s.1 → t = s) ∨ (∀ t ∈ S, t.2 = s.2 → t = s) := by
  by_contra h
  push Not at h
  obtain ⟨⟨y, hyS, hy1, hyne⟩, ⟨z, hzS, hz2, hzne⟩⟩ := h
  have hyz : y ≠ z := by
    rintro rfl
    exact hyne (Prod.ext hy1 hz2)
  exact hS s hs y hyS z hzS (Ne.symm hyne) hyz (Ne.symm hzne)
    ⟨Or.inl hy1.symm, Or.inr (Or.inl hz2.symm)⟩

/-- Conversely, if every square of `S` is alone in its row or alone in its
column, then `S` is good: in any would-be forbidden triple, the row-pair and
the column-pair share a square, which then has both a row-partner and a
column-partner. -/
lemma good_of_alone {m n : ℕ} {S : Finset (Fin m × Fin n)}
    (h : ∀ s ∈ S, (∀ t ∈ S, t.1 = s.1 → t = s) ∨ (∀ t ∈ S, t.2 = s.2 → t = s)) :
    Good S := by
  intro x hx y hy z hz hxy hyz hxz ⟨hrow, hcol⟩
  have key : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b.1 = a.1 → c.2 = a.2 →
      False := by
    intro a ha b hb c hc hab hac h1 h2
    rcases h a ha with hrow | hcol
    · exact hab (hrow b hb h1).symm
    · exact hac (hcol c hc h2).symm
  rcases hrow with h1 | h1 | h1 <;> rcases hcol with h2 | h2 | h2
  · exact absurd (Prod.ext h1 h2) hxy
  · exact key x hx y hy z hz hxy hxz h1.symm h2.symm
  · exact key y hy x hx z hz hxy.symm hyz h1 h2.symm
  · exact key x hx z hz y hy hxz hxy h1.symm h2.symm
  · exact absurd (Prod.ext h1 h2) hxz
  · exact key z hz x hx y hy hxz.symm hyz.symm h1 h2
  · exact key y hy z hz x hx hyz hxy.symm h1.symm h2
  · exact key z hz y hy x hx hyz.symm hxz.symm h1 h2
  · exact absurd (Prod.ext h1 h2) hyz

/-- Upper bound: a good set on an `m × n` board with `m, n ≥ 2` has at most
`m + n - 2` squares.

Proof: call a row (resp. column) *light* if it contains exactly one chosen
square and *heavy* if it contains at least two. The squares lying in light
rows are in bijection with the light rows, and every square in a heavy row is
the unique chosen square of its column (by `alone_of_good`), so the squares in
heavy rows inject into the light columns. Hence
`|S| ≤ (#light rows) + (#light columns)`. If there is at least one heavy row
and one heavy column, this is at most `m + n - 2`; if there is no heavy row
then `|S| ≤ m`, and if there is no heavy column then `|S| ≤ n`. -/
lemma card_le_of_good {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {S : Finset (Fin m × Fin n)} (hS : Good S) :
    S.card ≤ m + n - 2 := by
  set rows : Finset (Fin m) := S.image Prod.fst with hrows
  set cols : Finset (Fin n) := S.image Prod.snd with hcols
  set lightR : Finset (Fin m) := rows.filter fun r ↦ (rowFiber S r).card = 1 with hlightR
  set heavyR : Finset (Fin m) := rows.filter fun r ↦ 2 ≤ (rowFiber S r).card with hheavyR
  set lightC : Finset (Fin n) := cols.filter fun c ↦ (colFiber S c).card = 1 with hlightC
  set heavyC : Finset (Fin n) := cols.filter fun c ↦ 2 ≤ (colFiber S c).card with hheavyC
  have row_card_pos : ∀ r ∈ rows, 1 ≤ (rowFiber S r).card := by
    intro r hr
    rw [hrows, Finset.mem_image] at hr
    obtain ⟨s, hsS, hs⟩ := hr
    rw [← hs]
    exact Finset.card_pos.mpr ⟨s, mem_rowFiber.mpr ⟨hsS, rfl⟩⟩
  have col_card_pos : ∀ c ∈ cols, 1 ≤ (colFiber S c).card := by
    intro c hc
    rw [hcols, Finset.mem_image] at hc
    obtain ⟨s, hsS, hs⟩ := hc
    rw [← hs]
    exact Finset.card_pos.mpr ⟨s, mem_colFiber.mpr ⟨hsS, rfl⟩⟩
  have hR : rows.card = lightR.card + heavyR.card := by
    have h := Finset.card_filter_add_card_filter_not (s := rows)
      (p := fun r ↦ (rowFiber S r).card = 1)
    have h2 : rows.filter (fun r ↦ ¬ (rowFiber S r).card = 1) = heavyR := by
      rw [hheavyR]
      apply Finset.filter_congr
      intro r hr
      have := row_card_pos r hr
      lia
    rw [h2, ← hlightR] at h
    lia
  have hC : cols.card = lightC.card + heavyC.card := by
    have h := Finset.card_filter_add_card_filter_not (s := cols)
      (p := fun c ↦ (colFiber S c).card = 1)
    have h2 : cols.filter (fun c ↦ ¬ (colFiber S c).card = 1) = heavyC := by
      rw [hheavyC]
      apply Finset.filter_congr
      intro c hc
      have := col_card_pos c hc
      lia
    rw [h2, ← hlightC] at h
    lia
  have rows_le : rows.card ≤ m := by
    rw [hrows]
    calc (S.image Prod.fst).card ≤ Fintype.card (Fin m) := Finset.card_le_univ _
      _ = m := Fintype.card_fin m
  have cols_le : cols.card ≤ n := by
    rw [hcols]
    calc (S.image Prod.snd).card ≤ Fintype.card (Fin n) := Finset.card_le_univ _
      _ = n := Fintype.card_fin n
  -- Every square in a heavy row is the unique chosen square of its column.
  have key : ∀ s ∈ S, 2 ≤ (rowFiber S s.1).card → (colFiber S s.2).card = 1 := by
    intro s hsS hcard
    have hs_in : s ∈ rowFiber S s.1 := mem_rowFiber.mpr ⟨hsS, rfl⟩
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
    have hs_ne : ∃ t ∈ rowFiber S s.1, t ≠ s := by
      by_cases has : a = s
      · exact ⟨b, hb, fun e ↦ hab (has.trans e.symm)⟩
      · exact ⟨a, ha, has⟩
    obtain ⟨t, ht, hts⟩ := hs_ne
    rw [mem_rowFiber] at ht
    rcases alone_of_good hS hsS with hrow | hcol
    · exact absurd (hrow t ht.1 ht.2) hts
    · have hpos : 1 ≤ (colFiber S s.2).card :=
        Finset.card_pos.mpr ⟨s, mem_colFiber.mpr ⟨hsS, rfl⟩⟩
      have hle : (colFiber S s.2).card ≤ 1 := Finset.card_le_one.mpr fun a ha b hb ↦ by
        rw [mem_colFiber] at ha hb
        rw [hcol a ha.1 ha.2, hcol b hb.1 hb.2]
      lia
  -- Split `S` into squares in light rows and squares in heavy rows.
  set S₁ : Finset (Fin m × Fin n) := S.filter fun s ↦ (rowFiber S s.1).card = 1 with hS₁
  set S₂ : Finset (Fin m × Fin n) := S.filter fun s ↦ 2 ≤ (rowFiber S s.1).card with hS₂
  have hS_card : S.card = S₁.card + S₂.card := by
    have h := Finset.card_filter_add_card_filter_not (s := S)
      (p := fun s ↦ (rowFiber S s.1).card = 1)
    have h2 : S.filter (fun s ↦ ¬ (rowFiber S s.1).card = 1) = S₂ := by
      rw [hS₂]
      apply Finset.filter_congr
      intro x hx
      have hx1 : 1 ≤ (rowFiber S x.1).card :=
        Finset.card_pos.mpr ⟨x, mem_rowFiber.mpr ⟨hx, rfl⟩⟩
      lia
    rw [h2, ← hS₁] at h
    lia
  have hS₁card : S₁.card = lightR.card := by
    have hinj : Set.InjOn Prod.fst (S₁ : Set (Fin m × Fin n)) := by
      intro a ha b hb hab
      rw [hS₁, Finset.mem_coe, Finset.mem_filter] at ha hb
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp ha.2
      have ha_mem : a ∈ rowFiber S a.1 := mem_rowFiber.mpr ⟨ha.1, rfl⟩
      have hb_mem : b ∈ rowFiber S a.1 := mem_rowFiber.mpr ⟨hb.1, hab.symm⟩
      rw [hx, Finset.mem_singleton] at ha_mem hb_mem
      rw [ha_mem, hb_mem]
    have him : S₁.image Prod.fst = lightR := by
      exact Eq.symm Finset.filter_image
    rw [← him]
    exact (Finset.card_image_of_injOn hinj).symm
  have hS₂card : S₂.card ≤ lightC.card := by
    have hinj : Set.InjOn Prod.snd (S₂ : Set (Fin m × Fin n)) := by
      intro a ha b hb hab
      rw [hS₂, Finset.mem_coe, Finset.mem_filter] at ha hb
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp (key a ha.1 ha.2)
      have ha_mem : a ∈ colFiber S a.2 := mem_colFiber.mpr ⟨ha.1, rfl⟩
      have hb_mem : b ∈ colFiber S a.2 := mem_colFiber.mpr ⟨hb.1, hab.symm⟩
      rw [hx, Finset.mem_singleton] at ha_mem hb_mem
      rw [ha_mem, hb_mem]
    have him : S₂.image Prod.snd ⊆ lightC := by
      intro c hc
      rw [Finset.mem_image] at hc
      obtain ⟨s, hs, rfl⟩ := hc
      rw [hS₂, Finset.mem_filter] at hs
      rw [hlightC, Finset.mem_filter]
      exact ⟨by rw [hcols, Finset.mem_image]; exact ⟨s, hs.1, rfl⟩, key s hs.1 hs.2⟩
    calc S₂.card = (S₂.image Prod.snd).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ lightC.card := Finset.card_le_card him
  have hmain : S.card + (heavyR.card + heavyC.card) ≤ m + n := by
    calc S.card + (heavyR.card + heavyC.card)
        = S₁.card + S₂.card + (heavyR.card + heavyC.card) := by rw [hS_card]
      _ ≤ lightR.card + lightC.card + (heavyR.card + heavyC.card) :=
          Nat.add_le_add_right (by rw [hS₁card]; exact Nat.add_le_add_left hS₂card _) _
      _ = rows.card + cols.card := by rw [hR, hC]; ring
      _ ≤ m + n := Nat.add_le_add rows_le cols_le
  by_cases hR0 : heavyR.card = 0
  · -- No heavy row: distinct squares lie in distinct rows, so `|S| ≤ m`.
    have hinj : Set.InjOn Prod.fst (S : Set (Fin m × Fin n)) := by
      intro a ha b hb hab
      rw [Finset.mem_coe] at ha hb
      have h1 : (rowFiber S a.1).card = 1 := by
        have ha1 : a.1 ∈ rows := by
          rw [hrows, Finset.mem_image]; exact ⟨a, ha, rfl⟩
        have hnot : ¬ 2 ≤ (rowFiber S a.1).card := by
          intro hh
          have hmem : a.1 ∈ heavyR := by
            rw [hheavyR, Finset.mem_filter]; exact ⟨ha1, hh⟩
          rw [Finset.card_eq_zero.mp hR0] at hmem
          exact Finset.notMem_empty _ hmem
        have hpos := row_card_pos a.1 ha1
        lia
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h1
      have ha_mem : a ∈ rowFiber S a.1 := mem_rowFiber.mpr ⟨ha, rfl⟩
      have hb_mem : b ∈ rowFiber S a.1 := mem_rowFiber.mpr ⟨hb, hab.symm⟩
      rw [hx, Finset.mem_singleton] at ha_mem hb_mem
      rw [ha_mem, hb_mem]
    have hScard : S.card = rows.card := by
      rw [hrows]; exact (Finset.card_image_of_injOn hinj).symm
    lia
  · by_cases hC0 : heavyC.card = 0
    · -- No heavy column: distinct squares lie in distinct columns, so `|S| ≤ n`.
      have hinj : Set.InjOn Prod.snd (S : Set (Fin m × Fin n)) := by
        intro a ha b hb hab
        rw [Finset.mem_coe] at ha hb
        have h1 : (colFiber S a.2).card = 1 := by
          have ha1 : a.2 ∈ cols := by
            rw [hcols, Finset.mem_image]; exact ⟨a, ha, rfl⟩
          have hnot : ¬ 2 ≤ (colFiber S a.2).card := by
            intro hh
            have hmem : a.2 ∈ heavyC := by
              rw [hheavyC, Finset.mem_filter]; exact ⟨ha1, hh⟩
            rw [Finset.card_eq_zero.mp hC0] at hmem
            exact Finset.notMem_empty _ hmem
          have hpos := col_card_pos a.2 ha1
          lia
        obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h1
        have ha_mem : a ∈ colFiber S a.2 := mem_colFiber.mpr ⟨ha, rfl⟩
        have hb_mem : b ∈ colFiber S a.2 := mem_colFiber.mpr ⟨hb, hab.symm⟩
        rw [hx, Finset.mem_singleton] at ha_mem hb_mem
        rw [ha_mem, hb_mem]
      have hScard : S.card = cols.card := by
        rw [hcols]; exact (Finset.card_image_of_injOn hinj).symm
      lia
    · -- One heavy row and one heavy column: the main estimate applies.
      lia

/-- The extremal configuration: every square of row `0` or of column `0`,
except the corner square `(0, 0)`. -/
def construction : Finset (Fin 1000 × Fin 1000) :=
  ({0} : Finset (Fin 1000)) ×ˢ (Finset.univ.erase 0) ∪
    (Finset.univ.erase 0) ×ˢ ({0} : Finset (Fin 1000))

-- The `constructorNameAsVariable` linter normalizes the types of all binders;
-- here those are memberships in concrete finsets on the `1000 × 1000` board,
-- whose `whnf` unfolds a 1000-element list and exceeds the recursion limit.
set_option linter.constructorNameAsVariable false in
lemma card_construction : construction.card = 1998 := by
  have h1 : (({0} : Finset (Fin 1000)) ×ˢ ((Finset.univ : Finset (Fin 1000)).erase 0)).card
      = 999 := by
    rw [Finset.card_product, Finset.card_singleton,
      Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, Fintype.card_fin]
  have h2 : (((Finset.univ : Finset (Fin 1000)).erase 0) ×ˢ ({0} : Finset (Fin 1000))).card
      = 999 := by
    rw [Finset.card_product, Finset.card_singleton,
      Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, Fintype.card_fin]
  have hdisj : Disjoint (({0} : Finset (Fin 1000)) ×ˢ ((Finset.univ : Finset (Fin 1000)).erase 0))
      (((Finset.univ : Finset (Fin 1000)).erase 0) ×ˢ ({0} : Finset (Fin 1000))) := by
    rw [Finset.disjoint_left]
    intro s hs1 hs2
    rw [Finset.mem_product, Finset.mem_singleton] at hs1
    rw [Finset.mem_product, Finset.mem_erase] at hs2
    exact hs2.1.1 hs1.1
  have hrfl : construction =
      ({0} : Finset (Fin 1000)) ×ˢ ((Finset.univ : Finset (Fin 1000)).erase 0) ∪
        ((Finset.univ : Finset (Fin 1000)).erase 0) ×ˢ ({0} : Finset (Fin 1000)) := rfl
  rw [hrfl, Finset.card_union_of_disjoint hdisj, h1, h2]

-- See the comment at `card_construction` for the disabled linter.
set_option linter.constructorNameAsVariable false in
lemma good_construction : Good construction := by
  have hrfl : construction =
      ({0} : Finset (Fin 1000)) ×ˢ ((Finset.univ : Finset (Fin 1000)).erase 0) ∪
        ((Finset.univ : Finset (Fin 1000)).erase 0) ×ˢ ({0} : Finset (Fin 1000)) := rfl
  apply good_of_alone
  intro s hs
  rw [hrfl, Finset.mem_union, Finset.mem_product, Finset.mem_product] at hs
  rcases hs with ⟨hs1, hs2⟩ | ⟨hs1, hs2⟩
  · -- `s = (0, j)` with `j ≠ 0` is the unique chosen square of its column.
    right
    rw [Finset.mem_singleton] at hs1
    rw [Finset.mem_erase] at hs2
    intro t ht hte
    rw [hrfl, Finset.mem_union, Finset.mem_product, Finset.mem_product] at ht
    rcases ht with ⟨ht1, -⟩ | ⟨-, ht2⟩
    · rw [Finset.mem_singleton] at ht1
      exact Prod.ext (ht1.trans hs1.symm) hte
    · rw [Finset.mem_singleton] at ht2
      exact absurd (hte.symm.trans ht2) hs2.1
  · -- `s = (i, 0)` with `i ≠ 0` is the unique chosen square of its row.
    left
    rw [Finset.mem_singleton] at hs2
    rw [Finset.mem_erase] at hs1
    intro t ht hte
    rw [hrfl, Finset.mem_union, Finset.mem_product, Finset.mem_product] at ht
    rcases ht with ⟨ht1, -⟩ | ⟨-, ht2⟩
    · rw [Finset.mem_singleton] at ht1
      exact absurd (hte.symm.trans ht1) hs1.1
    · rw [Finset.mem_singleton] at ht2
      exact Prod.ext hte (ht2.trans hs2.symm)

snip end

determine smallestN : ℕ := 1999

problem usa2000_p4 :
    IsLeast {n : ℕ | ∀ S : Finset (Fin 1000 × Fin 1000), S.card = n → ¬Good S}
      smallestN := by
  constructor
  · -- 1999 colored squares always contain a forbidden triangle, since a set
    -- with no forbidden triangle has at most 1998 squares.
    intro S hcard hS
    have h := card_le_of_good (by norm_num) (by norm_num) hS
    have hcard' : S.card = 1999 := hcard
    lia
  · -- Any smaller `n` admits a counterexample: a subset of size `n` of the
    -- extremal configuration (which has 1998 squares).
    intro k hk
    by_contra hlt
    have hk' : k ≤ 1998 := by
      have hlt' : k < 1999 := Nat.lt_of_not_le hlt
      lia
    obtain ⟨T, hTsub, hTcard⟩ :=
      Finset.exists_subset_card_eq (s := construction) (n := k)
        (by rw [card_construction]; exact hk')
    exact hk T hTcard (good_construction.mono hTsub)

end Usa2000P4
