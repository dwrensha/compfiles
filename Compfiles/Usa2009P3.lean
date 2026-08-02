/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Int.SuccPred
public import Mathlib.Tactic.Cases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2009, Problem 3

We define a *chessboard polygon* to be a simple polygon whose sides are
situated along lines of the form x = a or y = b, where a and b are integers.
These lines divide the interior into unit squares, which are shaded
alternately gray and white so that adjacent squares have different colors.
To tile a chessboard polygon by dominoes is to exactly cover the polygon by
non-overlapping 1 × 2 rectangles. Finally, a *tasteful* tiling is one which
avoids the following two configurations of dominoes and colors: two vertical
dominoes whose 2 × 2 bounding box has a gray lower-left square, and two
horizontal dominoes whose 2 × 2 bounding box has a white lower-left square.

Prove that
(a) if a chessboard polygon can be tiled by dominoes, then it can be done
    so tastefully, and
(b) such a tasteful tiling is unique.

## Formalization notes

We work with the discrete model: a cell is a point of `ℤ × ℤ` (the
lower-left corner of a unit square), a region is a `Finset` of cells, and a
tiling of a region `S` is a fixed-point-free involution `f` on `S` mapping
each cell to an adjacent one (its domino partner).  The square `(i, j)` is
shaded gray when `i + j` is odd and white when `i + j` is even; with this
convention the two forbidden configurations are
  * a vertical pair `{(i,j),(i,j+1)}`, `{(i+1,j),(i+1,j+1)}` with `i+j` odd,
  * a horizontal pair `{(i,j),(i+1,j)}`, `{(i,j+1),(i+1,j+1)}` with `i+j` even.
(The other choice of shading gives an equivalent statement, via translation
of the region by `(1,0)`.)

A chessboard polygon (a simple lattice polygon) is represented by a region
that is connected and whose complement is connected; these are precisely the
finite unions of cells homeomorphic to a closed disk, i.e. the polyominoes
without holes, and every simple lattice polygon has this form.
-/

namespace Usa2009P3

/-- A cell: a unit square with integer coordinates, identified with its
lower-left corner. -/
abbrev Cell := ℤ × ℤ

/-- Two cells are adjacent if they share an edge. -/
def Adjacent (c c' : Cell) : Prop := (c.1 - c'.1).natAbs + (c.2 - c'.2).natAbs = 1

/-- `IsTiling S f` says that `f` matches every cell of `S` with an adjacent
cell of `S`, i.e. the dominoes `{c, f c}` tile `S`.  The function `f` is
only required to behave well on `S`; its values off `S` are irrelevant. -/
def IsTiling (S : Finset Cell) (f : Cell → Cell) : Prop :=
  ∀ c ∈ S, f c ∈ S ∧ f (f c) = c ∧ f c ≠ c ∧ Adjacent c (f c)

/-- `Tasteful S f` says the tiling has no forbidden configuration:
no vertical pair of dominoes whose shared 2 × 2 block has lower-left cell
`(i, j)` with `i + j` odd, and no horizontal pair with `i + j` even. -/
def Tasteful (S : Finset Cell) (f : Cell → Cell) : Prop :=
  (∀ i j : ℤ, (i, j) ∈ S → (i + 1, j) ∈ S → Odd (i + j) →
    ¬(f (i, j) = (i, j + 1) ∧ f (i + 1, j) = (i + 1, j + 1))) ∧
  (∀ i j : ℤ, (i, j) ∈ S → (i, j + 1) ∈ S → Even (i + j) →
    ¬(f (i, j) = (i + 1, j) ∧ f (i, j + 1) = (i + 1, j + 1)))

/-- Paths through cells satisfying a predicate. -/
def CellPath (P : Cell → Prop) : Cell → Cell → Prop :=
  Relation.ReflTransGen fun c c' ↦ P c ∧ P c' ∧ Adjacent c c'

/-- A region is connected if any two of its cells are linked by a path of
edge-adjacent cells inside it. -/
def Connected (S : Finset Cell) : Prop := ∀ c ∈ S, ∀ c' ∈ S, CellPath (· ∈ S) c c'

/-- A region has no holes if any two cells outside it are linked by a path
of edge-adjacent cells staying outside. -/
def ComplConnected (S : Finset Cell) : Prop := ∀ c ∉ S, ∀ c' ∉ S, CellPath (· ∉ S) c c'

snip begin

lemma adjacent_comm {c c' : Cell} (h : Adjacent c c') : Adjacent c' c := by
  have e1 : c'.1 - c.1 = -(c.1 - c'.1) := by ring
  have e2 : c'.2 - c.2 = -(c.2 - c'.2) := by ring
  rw [Adjacent, e1, e2, Int.natAbs_neg, Int.natAbs_neg]
  exact h

/-- The four neighbors of a cell. -/
lemma adjacent_cases {c c' : Cell} (h : Adjacent c c') :
    c' = (c.1 + 1, c.2) ∨ c' = (c.1 - 1, c.2) ∨ c' = (c.1, c.2 + 1) ∨ c' = (c.1, c.2 - 1) := by
  obtain ⟨a, b⟩ := c
  obtain ⟨a', b'⟩ := c'
  rw [Adjacent] at h
  simp only at h
  obtain ⟨hx, hy⟩ | ⟨hx, hy⟩ : ((a - a').natAbs = 0 ∧ (b - b').natAbs = 1) ∨
    ((a - a').natAbs = 1 ∧ (b - b').natAbs = 0) := by omega
  · rw [Int.natAbs_eq_zero] at hx
    obtain hy | hy := Int.natAbs_eq_iff.mp hy <;> simp_all <;> omega
  · rw [Int.natAbs_eq_zero] at hy
    obtain hx | hx := Int.natAbs_eq_iff.mp hx <;> simp_all <;> omega

/-- The cell to the right is adjacent. -/
lemma adjacent_mk_right (x y : ℤ) : Adjacent (x, y) (x + 1, y) := by
  show (x - (x + 1)).natAbs + (y - y).natAbs = 1
  rw [sub_self, show x - (x + 1) = -1 by ring]
  decide

/-- The cell above is adjacent. -/
lemma adjacent_mk_up (x y : ℤ) : Adjacent (x, y) (x, y + 1) := by
  show (x - x).natAbs + (y - (y + 1)).natAbs = 1
  rw [sub_self, show y - (y + 1) = -1 by ring]
  decide

lemma pair_ne_of_ne_fst {x₁ x₂ : ℤ} (h : x₁ ≠ x₂) (y₁ y₂ : ℤ) : (x₁, y₁) ≠ (x₂, y₂) :=
  fun hh => h (Prod.mk_inj.mp hh).1

lemma pair_ne_of_ne_snd {y₁ y₂ : ℤ} (h : y₁ ≠ y₂) (x₁ x₂ : ℤ) : (x₁, y₁) ≠ (x₂, y₂) :=
  fun hh => h (Prod.mk_inj.mp hh).2

lemma cell_ne_of_ne_fst (c : Cell) {x : ℤ} (h : x ≠ c.1) (y : ℤ) : (x, y) ≠ c :=
  fun hh => h (congrArg Prod.fst hh)

lemma cell_ne_of_ne_snd (c : Cell) {y : ℤ} (h : y ≠ c.2) (x : ℤ) : (x, y) ≠ c :=
  fun hh => h (congrArg Prod.snd hh)

lemma cell_ne_of_ne_fst' (c : Cell) {x : ℤ} (h : x ≠ c.1) (y : ℤ) : c ≠ (x, y) :=
  fun hh => h (congrArg Prod.fst hh).symm

lemma cell_ne_of_ne_snd' (c : Cell) {y : ℤ} (h : y ≠ c.2) (x : ℤ) : c ≠ (x, y) :=
  fun hh => h (congrArg Prod.snd hh).symm

/-- Every nonempty region has a *lower-left* cell: one with minimal
`y`-coordinate, and minimal `x`-coordinate among those. -/
lemma lower_left_exists {S : Finset Cell} (hne : S.Nonempty) :
    ∃ s ∈ S, (∀ c ∈ S, s.2 ≤ c.2) ∧ (∀ c ∈ S, c.2 = s.2 → s.1 ≤ c.1) := by
  have hne1 : (S.image Prod.snd).Nonempty := hne.image _
  have hmem : (S.image Prod.snd).min' hne1 ∈ S.image Prod.snd := Finset.min'_mem _ _
  rw [Finset.mem_image] at hmem
  obtain ⟨c₀, hc₀S, hc₀y⟩ := hmem
  have hne2 : (S.filter (fun c ↦ c.2 = (S.image Prod.snd).min' hne1)).Nonempty :=
    ⟨c₀, Finset.mem_filter.mpr ⟨hc₀S, hc₀y⟩⟩
  have hmem2 : ((S.filter (fun c ↦ c.2 = (S.image Prod.snd).min' hne1)).image Prod.fst).min'
        (hne2.image _)
      ∈ (S.filter (fun c ↦ c.2 = (S.image Prod.snd).min' hne1)).image Prod.fst :=
    Finset.min'_mem _ _
  rw [Finset.mem_image] at hmem2
  obtain ⟨c₁, hc₁T, hc₁x⟩ := hmem2
  rw [Finset.mem_filter] at hc₁T
  obtain ⟨hc₁S, hc₁y⟩ := hc₁T
  refine ⟨c₁, hc₁S, fun c hc => ?_, fun c hc hc2 => ?_⟩
  · rw [hc₁y]
    exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨c, hc, rfl⟩)
  · rw [hc₁x]
    exact Finset.min'_le _ _
      (Finset.mem_image.mpr ⟨c, Finset.mem_filter.mpr ⟨hc, hc2.trans hc₁y⟩, rfl⟩)

/-- Removing a domino — two cells matched to each other — from a tiling
leaves a tiling of the remaining region. -/
lemma isTiling_restrict_erase2 {S : Finset Cell} {f : Cell → Cell} (hf : IsTiling S f)
    {a b : Cell} (ha : f a = b) (hb : f b = a) :
    IsTiling ((S.erase a).erase b) f := by
  intro c hc
  rw [Finset.mem_erase, Finset.mem_erase] at hc
  obtain ⟨hcb, hca, hcS⟩ := hc
  obtain ⟨h1, h2, h3, h4⟩ := hf c hcS
  refine ⟨?_, h2, h3, h4⟩
  rw [Finset.mem_erase, Finset.mem_erase]
  refine ⟨?_, ?_, h1⟩
  · intro hfcb
    rw [hfcb, hb] at h2
    exact hca h2.symm
  · intro hfca
    rw [hfca, ha] at h2
    exact hcb h2.symm

/-- Adding a domino on two fresh adjacent cells `a`, `b` to a tiling of `T`
gives a tiling of `insert a (insert b T)`. -/
lemma isTiling_update_domino {T : Finset Cell} {f : Cell → Cell} (hf : IsTiling T f)
    {a b : Cell} (hab : a ≠ b) (ha : a ∉ T) (hb : b ∉ T) (hadj : Adjacent a b) :
    IsTiling (insert a (insert b T)) (Function.update (Function.update f a b) b a) := by
  have ga : Function.update (Function.update f a b) b a a = b := by
    rw [Function.update_of_ne hab, Function.update_self]
  have gb : Function.update (Function.update f a b) b a b = a := Function.update_self _ _ _
  have gne : ∀ c : Cell, c ≠ a → c ≠ b →
      Function.update (Function.update f a b) b a c = f c :=
    fun c h1 h2 => by rw [Function.update_of_ne h2, Function.update_of_ne h1]
  intro c hc
  rw [Finset.mem_insert, Finset.mem_insert] at hc
  rcases hc with rfl | rfl | hcT
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [ga]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · rw [ga, gb]
    · rw [ga]
      exact hab.symm
    · rw [ga]
      exact hadj
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [gb]
      exact Finset.mem_insert_self _ _
    · rw [gb, ga]
    · rw [gb]
      exact hab
    · rw [gb]
      exact adjacent_comm hadj
  · have hca : c ≠ a := fun hh => ha (hh ▸ hcT)
    have hcb : c ≠ b := fun hh => hb (hh ▸ hcT)
    obtain ⟨h1, h2, h3, h4⟩ := hf c hcT
    have hfa : f c ≠ a := fun hh => ha (hh ▸ h1)
    have hfb : f c ≠ b := fun hh => hb (hh ▸ h1)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [gne c hca hcb]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h1)
    · rw [gne c hca hcb, gne (f c) hfa hfb]
      exact h2
    · rw [gne c hca hcb]
      exact h3
    · rw [gne c hca hcb]
      exact h4

/-- Extending a tasteful tiling by a vertical domino on the fresh cells
`(ax, ay)`, `(ax, ay + 1)` stays tasteful, provided the cell `(ax - 1, ay)`
to the left is absent (so the new domino cannot be the right half of a
forbidden vertical pair) and the cell to the right is not matched vertically
when `ax + ay` is odd (so it cannot be the left half of one).  The new
vertical domino can never belong to a horizontal pair. -/
lemma tasteful_extend_vertical {T : Finset Cell} {f : Cell → Cell} (ht : Tasteful T f)
    (ax ay : ℤ) (_ha : (ax, ay) ∉ T) (_hb : (ax, ay + 1) ∉ T) (hleft : (ax - 1, ay) ∉ T)
    (hright : Odd (ax + ay) → (ax + 1, ay) ∈ insert (ax, ay) (insert (ax, ay + 1) T) →
      f (ax + 1, ay) ≠ (ax + 1, ay + 1)) :
    Tasteful (insert (ax, ay) (insert (ax, ay + 1) T))
      (Function.update (Function.update f (ax, ay) (ax, ay + 1)) (ax, ay + 1) (ax, ay)) := by
  obtain ⟨ht1, ht2⟩ := ht
  have hab : (ax, ay) ≠ (ax, ay + 1) := pair_ne_of_ne_snd (by omega) _ _
  have ga : Function.update (Function.update f (ax, ay) (ax, ay + 1)) (ax, ay + 1) (ax, ay)
      (ax, ay) = (ax, ay + 1) := by
    rw [Function.update_of_ne hab, Function.update_self]
  have gb : Function.update (Function.update f (ax, ay) (ax, ay + 1)) (ax, ay + 1) (ax, ay)
      (ax, ay + 1) = (ax, ay) := Function.update_self _ _ _
  have gne : ∀ c : Cell, c ≠ (ax, ay) → c ≠ (ax, ay + 1) →
      Function.update (Function.update f (ax, ay) (ax, ay + 1)) (ax, ay + 1) (ax, ay) c = f c :=
    fun c h1 h2 => by rw [Function.update_of_ne h2, Function.update_of_ne h1]
  have memT : ∀ c : Cell, c ≠ (ax, ay) → c ≠ (ax, ay + 1) →
      c ∈ insert (ax, ay) (insert (ax, ay + 1) T) → c ∈ T := by
    intro c h1 h2 hc
    rw [Finset.mem_insert, Finset.mem_insert] at hc
    rcases hc with h | h | h
    · exact absurd h h1
    · exact absurd h h2
    · exact h
  refine ⟨?_, ?_⟩
  · -- vertical pairs, `i + j` odd
    intro i j hi hij hpar hconf
    obtain ⟨h1, h2⟩ := hconf
    by_cases hA : (i, j) = (ax, ay)
    · obtain ⟨e1, e2⟩ := Prod.mk_inj.mp hA
      rw [e1, e2] at h2 hij hpar
      have hne1 : (ax + 1, ay) ≠ (ax, ay) := pair_ne_of_ne_fst (by omega) _ _
      have hne2 : (ax + 1, ay) ≠ (ax, ay + 1) := pair_ne_of_ne_fst (by omega) _ _
      rw [gne _ hne1 hne2] at h2
      exact hright hpar hij h2
    · by_cases hB : (i, j) = (ax, ay + 1)
      · obtain ⟨e1, e2⟩ := Prod.mk_inj.mp hB
        rw [e1, e2] at h1
        rw [gb] at h1
        exact absurd (Prod.mk_inj.mp h1).2 (by omega)
      · by_cases hC : (i + 1, j) = (ax, ay)
        · obtain ⟨e1, e2⟩ := Prod.mk_inj.mp hC
          rw [e2] at hi
          have hiT : (i, ay) ∈ T := memT _
            (cell_ne_of_ne_fst (ax, ay) (show i ≠ ax by omega) _)
            (cell_ne_of_ne_snd (ax, ay + 1) (show ay ≠ ay + 1 by omega) _) hi
          have ei : i = ax - 1 := by omega
          rw [ei] at hiT
          exact hleft hiT
        · by_cases hD : (i + 1, j) = (ax, ay + 1)
          · obtain ⟨e1, e2⟩ := Prod.mk_inj.mp hD
            rw [hD] at h2
            rw [gb] at h2
            obtain ⟨e3, e4⟩ := Prod.mk_inj.mp h2
            omega
          · exact ht1 i j (memT _ hA hB hi) (memT _ hC hD hij) hpar
              ⟨by rwa [gne _ hA hB] at h1, by rwa [gne _ hC hD] at h2⟩
  · -- horizontal pairs, `i + j` even; a vertical domino plays no role
    intro i j hi hij hpar hconf
    obtain ⟨h1, h2⟩ := hconf
    by_cases hA : (i, j) = (ax, ay)
    · obtain ⟨e1, e2⟩ := Prod.mk_inj.mp hA
      rw [e1, e2] at h1
      rw [ga] at h1
      exact absurd (Prod.mk_inj.mp h1).1 (by omega)
    · by_cases hB : (i, j) = (ax, ay + 1)
      · obtain ⟨e1, e2⟩ := Prod.mk_inj.mp hB
        rw [e1, e2] at h1
        rw [gb] at h1
        exact absurd (Prod.mk_inj.mp h1).1 (by omega)
      · by_cases hC : (i, j + 1) = (ax, ay)
        · obtain ⟨e1, e2⟩ := Prod.mk_inj.mp hC
          rw [hC] at h2
          rw [ga] at h2
          obtain ⟨e3, e4⟩ := Prod.mk_inj.mp h2
          omega
        · by_cases hD : (i, j + 1) = (ax, ay + 1)
          · obtain ⟨e1, e2⟩ := Prod.mk_inj.mp hD
            rw [hD] at h2
            rw [gb] at h2
            obtain ⟨e3, e4⟩ := Prod.mk_inj.mp h2
            omega
          · exact ht2 i j (memT _ hA hB hi) (memT _ hC hD hij) hpar
              ⟨by rwa [gne _ hA hB] at h1, by rwa [gne _ hC hD] at h2⟩

/-- Extending a tasteful tiling by a horizontal domino on the fresh cells
`(ax, ay)`, `(ax + 1, ay)` stays tasteful, provided the cell `(ax, ay - 1)`
below is absent (so the new domino cannot be the top half of a forbidden
horizontal pair) and the cell above is not matched horizontally when
`ax + ay` is even (so it cannot be the bottom half of one).  The new
horizontal domino can never belong to a vertical pair. -/
lemma tasteful_extend_horizontal {T : Finset Cell} {f : Cell → Cell} (ht : Tasteful T f)
    (ax ay : ℤ) (_ha : (ax, ay) ∉ T) (_hb : (ax + 1, ay) ∉ T) (hdown : (ax, ay - 1) ∉ T)
    (hup : Even (ax + ay) → (ax, ay + 1) ∈ insert (ax, ay) (insert (ax + 1, ay) T) →
      f (ax, ay + 1) ≠ (ax + 1, ay + 1)) :
    Tasteful (insert (ax, ay) (insert (ax + 1, ay) T))
      (Function.update (Function.update f (ax, ay) (ax + 1, ay)) (ax + 1, ay) (ax, ay)) := by
  obtain ⟨ht1, ht2⟩ := ht
  have hab : (ax, ay) ≠ (ax + 1, ay) := pair_ne_of_ne_fst (by omega) _ _
  have ga : Function.update (Function.update f (ax, ay) (ax + 1, ay)) (ax + 1, ay) (ax, ay)
      (ax, ay) = (ax + 1, ay) := by
    rw [Function.update_of_ne hab, Function.update_self]
  have gb : Function.update (Function.update f (ax, ay) (ax + 1, ay)) (ax + 1, ay) (ax, ay)
      (ax + 1, ay) = (ax, ay) := Function.update_self _ _ _
  have gne : ∀ c : Cell, c ≠ (ax, ay) → c ≠ (ax + 1, ay) →
      Function.update (Function.update f (ax, ay) (ax + 1, ay)) (ax + 1, ay) (ax, ay) c = f c :=
    fun c h1 h2 => by rw [Function.update_of_ne h2, Function.update_of_ne h1]
  have memT : ∀ c : Cell, c ≠ (ax, ay) → c ≠ (ax + 1, ay) →
      c ∈ insert (ax, ay) (insert (ax + 1, ay) T) → c ∈ T := by
    intro c h1 h2 hc
    rw [Finset.mem_insert, Finset.mem_insert] at hc
    rcases hc with h | h | h
    · exact absurd h h1
    · exact absurd h h2
    · exact h
  refine ⟨?_, ?_⟩
  · -- vertical pairs, `i + j` odd; a horizontal domino plays no role
    intro i j hi hij hpar hconf
    obtain ⟨h1, h2⟩ := hconf
    by_cases hA : (i, j) = (ax, ay)
    · obtain ⟨e1, e2⟩ := Prod.mk_inj.mp hA
      rw [e1, e2] at h1
      rw [ga] at h1
      exact absurd (Prod.mk_inj.mp h1).1 (by omega)
    · by_cases hB : (i, j) = (ax + 1, ay)
      · obtain ⟨e1, e2⟩ := Prod.mk_inj.mp hB
        rw [e1, e2] at h1
        rw [gb] at h1
        exact absurd (Prod.mk_inj.mp h1).1 (by omega)
      · by_cases hC : (i + 1, j) = (ax, ay)
        · obtain ⟨e1, e2⟩ := Prod.mk_inj.mp hC
          rw [hC] at h2
          rw [ga] at h2
          obtain ⟨e3, e4⟩ := Prod.mk_inj.mp h2
          omega
        · by_cases hD : (i + 1, j) = (ax + 1, ay)
          · obtain ⟨e1, e2⟩ := Prod.mk_inj.mp hD
            rw [hD] at h2
            rw [gb] at h2
            obtain ⟨e3, e4⟩ := Prod.mk_inj.mp h2
            omega
          · exact ht1 i j (memT _ hA hB hi) (memT _ hC hD hij) hpar
              ⟨by rwa [gne _ hA hB] at h1, by rwa [gne _ hC hD] at h2⟩
  · -- horizontal pairs, `i + j` even
    intro i j hi hij hpar hconf
    obtain ⟨h1, h2⟩ := hconf
    by_cases hA : (i, j) = (ax, ay)
    · obtain ⟨e1, e2⟩ := Prod.mk_inj.mp hA
      rw [e1, e2] at h2 hij hpar
      have hne1 : (ax, ay + 1) ≠ (ax, ay) := pair_ne_of_ne_snd (by omega) _ _
      have hne2 : (ax, ay + 1) ≠ (ax + 1, ay) := pair_ne_of_ne_snd (by omega) _ _
      rw [gne _ hne1 hne2] at h2
      exact hup hpar hij h2
    · by_cases hB : (i, j) = (ax + 1, ay)
      · obtain ⟨e1, e2⟩ := Prod.mk_inj.mp hB
        rw [e1, e2] at h1
        rw [gb] at h1
        exact absurd (Prod.mk_inj.mp h1).1 (by omega)
      · by_cases hC : (i, j + 1) = (ax, ay)
        · obtain ⟨e1, e2⟩ := Prod.mk_inj.mp hC
          have hiT : (i, j) ∈ T := memT _
            (cell_ne_of_ne_snd (ax, ay) (show j ≠ ay by omega) _)
            (cell_ne_of_ne_snd (ax + 1, ay) (show j ≠ ay by omega) _) hi
          rw [e1] at hiT
          have e4 : j = ay - 1 := by omega
          rw [e4] at hiT
          exact hdown hiT
        · by_cases hD : (i, j + 1) = (ax + 1, ay)
          · obtain ⟨e1, e2⟩ := Prod.mk_inj.mp hD
            rw [hD] at h2
            rw [gb] at h2
            obtain ⟨e3, e4⟩ := Prod.mk_inj.mp h2
            omega
          · exact ht2 i j (memT _ hA hB hi) (memT _ hC hD hij) hpar
              ⟨by rwa [gne _ hA hB] at h1, by rwa [gne _ hC hD] at h2⟩

/-- USAMO 2009 Problem 3, part (a): every region that can be tiled by
dominoes can be tiled tastefully. -/
theorem exists_tasteful_tiling (S : Finset Cell) (h : ∃ f, IsTiling S f) :
    ∃ f, IsTiling S f ∧ Tasteful S f := by
  have aux : ∀ n : ℕ, ∀ S : Finset Cell, S.card = n → (∃ f, IsTiling S f) →
      ∃ f, IsTiling S f ∧ Tasteful S f := by
    intro n
    induction' n using Nat.strong_induction_on with n ih
    intro S hn h
    by_cases hne : S.Nonempty
    · obtain ⟨s, hsS, hsy, hsx⟩ := lower_left_exists hne
      -- the cells to the left of and below `s` are not in `S`
      have hL : (s.1 - 1, s.2) ∉ S := by
        intro hm
        have h1 := hsx _ hm rfl
        omega
      have hD : (s.1, s.2 - 1) ∉ S := by
        intro hm
        have h1 := hsy _ hm
        omega
      have hadj_sr : Adjacent s (s.1 + 1, s.2) := by
        show Adjacent (s.1, s.2) (s.1 + 1, s.2)
        exact adjacent_mk_right _ _
      have hadj_su : Adjacent s (s.1, s.2 + 1) := by
        show Adjacent (s.1, s.2) (s.1, s.2 + 1)
        exact adjacent_mk_up _ _
      -- Shared final step: given any tiling of `S` minus the horizontal domino
      -- `{s, (s.1 + 1, s.2)}`, extend the tasteful tiling from the induction
      -- hypothesis by that domino.  The extra hypothesis rules out a forbidden
      -- horizontal pair with lower-left cell `s`.
      have finale : ∀ (_ : (s.1 + 1, s.2) ∈ S)
          (_ : ∃ f, IsTiling ((S.erase s).erase (s.1 + 1, s.2)) f)
          (_ : ∀ fT : Cell → Cell, IsTiling ((S.erase s).erase (s.1 + 1, s.2)) fT →
            Tasteful ((S.erase s).erase (s.1 + 1, s.2)) fT →
            Even (s.1 + s.2) → (s.1, s.2 + 1) ∈ S →
            fT (s.1, s.2 + 1) ≠ (s.1 + 1, s.2 + 1)),
          ∃ f, IsTiling S f ∧ Tasteful S f := by
        intro hrS hS₄tile hup
        set S₄ := (S.erase s).erase (s.1 + 1, s.2) with hS₄def
        have hr_mem : (s.1 + 1, s.2) ∈ S.erase s :=
          Finset.mem_erase.mpr ⟨cell_ne_of_ne_fst s (by omega) _, hrS⟩
        have hcardS₄ : S₄.card < n := by
          have h1 : S₄.card = S.card - 1 - 1 := by
            rw [hS₄def, Finset.card_erase_of_mem hr_mem, Finset.card_erase_of_mem hsS]
          have h2 : 0 < S.card := Finset.card_pos.mpr ⟨s, hsS⟩
          omega
        obtain ⟨f'', hf'', ht''⟩ := ih _ hcardS₄ S₄ rfl hS₄tile
        have hsS₄ : s ∉ S₄ := fun hm => Finset.notMem_erase _ _ (Finset.erase_subset _ _ hm)
        have hrS₄ : (s.1 + 1, s.2) ∉ S₄ := fun hm => Finset.notMem_erase _ _ hm
        have hdownS₄ : (s.1, s.2 - 1) ∉ S₄ := fun hm =>
          hD (Finset.erase_subset _ _ (Finset.erase_subset _ _ hm))
        have heS₄ : insert s (insert (s.1 + 1, s.2) S₄) = S := by
          rw [hS₄def, Finset.insert_erase hr_mem, Finset.insert_erase hsS]
        have hne_sr : s ≠ (s.1 + 1, s.2) := cell_ne_of_ne_fst' s (by omega) _
        refine ⟨Function.update (Function.update f'' s (s.1 + 1, s.2)) (s.1 + 1, s.2) s, ?_, ?_⟩
        · have hg : IsTiling (insert s (insert (s.1 + 1, s.2) S₄)) _ :=
            isTiling_update_domino hf'' hne_sr hsS₄ hrS₄ hadj_sr
          rwa [heS₄] at hg
        · have hup' : Even (s.1 + s.2) →
              (s.1, s.2 + 1) ∈ insert (s.1, s.2) (insert (s.1 + 1, s.2) S₄) →
              f'' (s.1, s.2 + 1) ≠ (s.1 + 1, s.2 + 1) := by
            intro he hum
            apply hup f'' hf'' ht'' he
            rw [Finset.mem_insert, Finset.mem_insert] at hum
            rcases hum with h | h | h
            · exact absurd h (pair_ne_of_ne_snd (by omega) _ _)
            · exact absurd h (pair_ne_of_ne_fst (by omega) _ _)
            · exact Finset.erase_subset _ _ (Finset.erase_subset _ _ h)
          have hg : Tasteful (insert (s.1, s.2) (insert (s.1 + 1, s.2) S₄)) _ :=
            tasteful_extend_horizontal ht'' s.1 s.2 hsS₄ hrS₄ hdownS₄ hup'
          rw [← heS₄]
          exact hg
      by_cases hA : ∃ f, IsTiling S f ∧ f s = (s.1, s.2 + 1)
      · -- Case A: some tiling matches `s` with the cell above it.
        obtain ⟨f₀, hf₀, hf₀s⟩ := hA
        have huS : (s.1, s.2 + 1) ∈ S := hf₀s ▸ (hf₀ s hsS).1
        have hf₀u : f₀ (s.1, s.2 + 1) = s := by
          have h1 := (hf₀ s hsS).2.1
          rw [hf₀s] at h1
          exact h1
        have hne_su : s ≠ (s.1, s.2 + 1) := cell_ne_of_ne_snd' s (by omega) _
        have hne_us : (s.1, s.2 + 1) ≠ s := cell_ne_of_ne_snd s (by omega) _
        set S' := (S.erase s).erase (s.1, s.2 + 1) with hS'def
        have hf₀S' : IsTiling S' f₀ := isTiling_restrict_erase2 hf₀ hf₀s hf₀u
        have hu_mem : (s.1, s.2 + 1) ∈ S.erase s := Finset.mem_erase.mpr ⟨hne_us, huS⟩
        have hcardS' : S'.card < n := by
          have h1 : S'.card = S.card - 1 - 1 := by
            rw [hS'def, Finset.card_erase_of_mem hu_mem, Finset.card_erase_of_mem hsS]
          have h2 : 0 < S.card := Finset.card_pos.mpr ⟨s, hsS⟩
          omega
        have hsS' : s ∉ S' := fun hm => Finset.notMem_erase _ _ (Finset.erase_subset _ _ hm)
        have huS' : (s.1, s.2 + 1) ∉ S' := fun hm => Finset.notMem_erase _ _ hm
        have hleftS' : (s.1 - 1, s.2) ∉ S' := fun hm =>
          hL (Finset.erase_subset _ _ (Finset.erase_subset _ _ hm))
        have heS : insert s (insert (s.1, s.2 + 1) S') = S := by
          rw [hS'def, Finset.insert_erase hu_mem, Finset.insert_erase hsS]
        obtain ⟨f', hf', ht'⟩ := ih _ hcardS' S' rfl ⟨f₀, hf₀S'⟩
        have hgT : IsTiling S
            (Function.update (Function.update f' s (s.1, s.2 + 1)) (s.1, s.2 + 1) s) := by
          have hg : IsTiling (insert s (insert (s.1, s.2 + 1) S')) _ :=
            isTiling_update_domino hf' hne_su hsS' huS' hadj_su
          rwa [heS] at hg
        -- the vertical extension of the IH tiling works unless its only
        -- possible flaw, a forbidden vertical pair with lower-left cell `s`,
        -- actually occurs
        have vertical_route : (Odd (s.1 + s.2) →
              (s.1 + 1, s.2) ∈ insert (s.1, s.2) (insert (s.1, s.2 + 1) S') →
              f' (s.1 + 1, s.2) ≠ (s.1 + 1, s.2 + 1)) →
            ∃ f, IsTiling S f ∧ Tasteful S f := by
          intro hright
          refine ⟨_, hgT, ?_⟩
          rw [← heS]
          exact tasteful_extend_vertical ht' s.1 s.2 hsS' huS' hleftS' hright
        by_cases hrS : (s.1 + 1, s.2) ∈ S
        · by_cases htest : f' (s.1 + 1, s.2) = (s.1 + 1, s.2 + 1)
          · by_cases hpar : Odd (s.1 + s.2)
            · -- the vertical extension has a forbidden vertical pair at `s`;
              -- flip the 2 × 2 block to make `s` horizontal instead, then
              -- apply the induction hypothesis once more.
              have hrS' : (s.1 + 1, s.2) ∈ S' :=
                Finset.mem_erase.mpr ⟨pair_ne_of_ne_fst (by omega) _ _,
                  Finset.mem_erase.mpr ⟨cell_ne_of_ne_fst s (by omega) _, hrS⟩⟩
              have hruS' : (s.1 + 1, s.2 + 1) ∈ S' := htest ▸ (hf' _ hrS').1
              have hf'ru : f' (s.1 + 1, s.2 + 1) = (s.1 + 1, s.2) := by
                have h1 := (hf' _ hrS').2.1
                rw [htest] at h1
                exact h1
              have hne_rru : (s.1 + 1, s.2) ≠ (s.1 + 1, s.2 + 1) :=
                pair_ne_of_ne_snd (by omega) _ _
              have hne_rur : (s.1 + 1, s.2 + 1) ≠ (s.1 + 1, s.2) :=
                pair_ne_of_ne_snd (by omega) _ _
              have hne_uru : (s.1, s.2 + 1) ≠ (s.1 + 1, s.2 + 1) :=
                pair_ne_of_ne_fst (by omega) _ _
              have hne_sr : s ≠ (s.1 + 1, s.2) := cell_ne_of_ne_fst' s (by omega) _
              have hne_sru : s ≠ (s.1 + 1, s.2 + 1) := cell_ne_of_ne_snd' s (by omega) _
              set S₂ := (S'.erase (s.1 + 1, s.2)).erase (s.1 + 1, s.2 + 1) with hS₂def
              have hfS₂ : IsTiling S₂ f' := isTiling_restrict_erase2 hf' htest hf'ru
              have huS₂ : (s.1, s.2 + 1) ∉ S₂ := fun hm =>
                huS' (Finset.erase_subset _ _ (Finset.erase_subset _ _ hm))
              have hruS₂ : (s.1 + 1, s.2 + 1) ∉ S₂ := fun hm => Finset.notMem_erase _ _ hm
              set g₂ := Function.update (Function.update f' (s.1, s.2 + 1) (s.1 + 1, s.2 + 1))
                (s.1 + 1, s.2 + 1) (s.1, s.2 + 1)
              have hg₂ : IsTiling (insert (s.1, s.2 + 1) (insert (s.1 + 1, s.2 + 1) S₂)) g₂ :=
                isTiling_update_domino hfS₂ hne_uru huS₂ hruS₂ (adjacent_mk_right _ _)
              have hs₂ : s ∉ insert (s.1, s.2 + 1) (insert (s.1 + 1, s.2 + 1) S₂) := by
                intro hm
                rw [Finset.mem_insert, Finset.mem_insert] at hm
                rcases hm with h | h | h
                · exact hne_su h
                · exact hne_sru h
                · exact hsS' (Finset.erase_subset _ _ (Finset.erase_subset _ _ h))
              have hr₂ : (s.1 + 1, s.2) ∉
                  insert (s.1, s.2 + 1) (insert (s.1 + 1, s.2 + 1) S₂) := by
                intro hm
                rw [Finset.mem_insert, Finset.mem_insert] at hm
                rcases hm with h | h | h
                · exact absurd h (pair_ne_of_ne_fst (by omega) _ _)
                · exact hne_rru h
                · exact Finset.notMem_erase _ _ (Finset.erase_subset _ _ h)
              set g₃ := Function.update (Function.update g₂ s (s.1 + 1, s.2))
                (s.1 + 1, s.2) s with hg₃def
              have hg₃ : IsTiling (insert s (insert (s.1 + 1, s.2)
                  (insert (s.1, s.2 + 1) (insert (s.1 + 1, s.2 + 1) S₂)))) g₃ :=
                isTiling_update_domino hg₂ hne_sr hs₂ hr₂ hadj_sr
              have heS₃ : insert s (insert (s.1 + 1, s.2)
                  (insert (s.1, s.2 + 1) (insert (s.1 + 1, s.2 + 1) S₂))) = S := by
                have e1 : insert (s.1 + 1, s.2 + 1) S₂ = S'.erase (s.1 + 1, s.2) := by
                  rw [hS₂def]
                  exact Finset.insert_erase (Finset.mem_erase.mpr ⟨hne_rur, hruS'⟩)
                have e2 : insert (s.1 + 1, s.2) (S'.erase (s.1 + 1, s.2)) = S' :=
                  Finset.insert_erase hrS'
                rw [e1, Finset.insert_comm (a := (s.1 + 1, s.2)) (b := (s.1, s.2 + 1)), e2, heS]
              have hg₃S : IsTiling S g₃ := heS₃ ▸ hg₃
              have hg₃s : g₃ s = (s.1 + 1, s.2) := by
                rw [hg₃def, Function.update_of_ne hne_sr, Function.update_self]
              have hg₃r : g₃ (s.1 + 1, s.2) = s := by
                rw [hg₃def]
                exact Function.update_self _ _ _
              have hg₃S₄ : IsTiling ((S.erase s).erase (s.1 + 1, s.2)) g₃ :=
                isTiling_restrict_erase2 hg₃S hg₃s hg₃r
              exact finale hrS ⟨g₃, hg₃S₄⟩
                (fun fT _ _ heven _ => absurd heven (Int.not_even_iff_odd.mpr hpar))
            · -- even parity: the vertical pair clause does not apply at `s`
              exact vertical_route (fun hodd _ => absurd hodd hpar)
          · -- the cell to the right is not matched vertically: no forbidden pair
            exact vertical_route (fun _ _ => htest)
        · -- the cell to the right is absent: no forbidden pair at `s`
          apply vertical_route
          intro _ hrmem
          rw [Finset.mem_insert, Finset.mem_insert] at hrmem
          rcases hrmem with h | h | h
          · exact absurd h (pair_ne_of_ne_fst (by omega) _ _)
          · exact absurd h (pair_ne_of_ne_fst (by omega) _ _)
          · exact absurd (Finset.erase_subset _ _ (Finset.erase_subset _ _ h)) hrS
      · -- Case B: every tiling matches `s` with the cell to its right.
        obtain ⟨f₀, hf₀⟩ := h
        have hf₀s := hf₀ s hsS
        have hf₀seq : f₀ s = (s.1 + 1, s.2) := by
          have hcases := adjacent_cases hf₀s.2.2.2
          rcases hcases with h1 | h2 | h3 | h4
          · exact h1
          · exact absurd (h2 ▸ hf₀s.1) hL
          · exact absurd ⟨f₀, hf₀, h3⟩ hA
          · exact absurd (h4 ▸ hf₀s.1) hD
        have hrS : (s.1 + 1, s.2) ∈ S := hf₀seq ▸ hf₀s.1
        have hf₀r : f₀ (s.1 + 1, s.2) = s := by
          have h1 := hf₀s.2.1
          rw [hf₀seq] at h1
          exact h1
        have hf₀S₄ : IsTiling ((S.erase s).erase (s.1 + 1, s.2)) f₀ :=
          isTiling_restrict_erase2 hf₀ hf₀seq hf₀r
        refine finale hrS ⟨f₀, hf₀S₄⟩ ?_
        intro fT hfT htT _ huS hbad
        -- a forbidden horizontal pair at `s` would let us flip the 2 × 2 block,
        -- producing a tiling that matches `s` with the cell above: contradiction.
        have hne_us : (s.1, s.2 + 1) ≠ s := cell_ne_of_ne_snd s (by omega) _
        have hne_ur : (s.1, s.2 + 1) ≠ (s.1 + 1, s.2) := pair_ne_of_ne_fst (by omega) _ _
        have huS₄ : (s.1, s.2 + 1) ∈ (S.erase s).erase (s.1 + 1, s.2) :=
          Finset.mem_erase.mpr ⟨hne_ur, Finset.mem_erase.mpr ⟨hne_us, huS⟩⟩
        have hruS₄ : (s.1 + 1, s.2 + 1) ∈ (S.erase s).erase (s.1 + 1, s.2) :=
          hbad ▸ (hfT _ huS₄).1
        have hfTru : fT (s.1 + 1, s.2 + 1) = (s.1, s.2 + 1) := by
          have h1 := (hfT _ huS₄).2.1
          rw [hbad] at h1
          exact h1
        have hne_rru : (s.1 + 1, s.2) ≠ (s.1 + 1, s.2 + 1) := pair_ne_of_ne_snd (by omega) _ _
        have hne_ruu : (s.1 + 1, s.2 + 1) ≠ (s.1, s.2 + 1) := pair_ne_of_ne_fst (by omega) _ _
        have hne_uru : (s.1, s.2 + 1) ≠ (s.1 + 1, s.2 + 1) := pair_ne_of_ne_fst (by omega) _ _
        have hne_su : s ≠ (s.1, s.2 + 1) := cell_ne_of_ne_snd' s (by omega) _
        have hne_sr : s ≠ (s.1 + 1, s.2) := cell_ne_of_ne_fst' s (by omega) _
        have hne_rs : (s.1 + 1, s.2) ≠ s := cell_ne_of_ne_fst s (by omega) _
        have hne_sru : s ≠ (s.1 + 1, s.2 + 1) := cell_ne_of_ne_snd' s (by omega) _
        set S₆ := (((S.erase s).erase (s.1 + 1, s.2)).erase (s.1, s.2 + 1)).erase
          (s.1 + 1, s.2 + 1) with hS₆def
        have hfS₆ : IsTiling S₆ fT := isTiling_restrict_erase2 hfT hbad hfTru
        have hrS₆ : (s.1 + 1, s.2) ∉ S₆ := fun hm =>
          Finset.notMem_erase _ _ (Finset.erase_subset _ _ (Finset.erase_subset _ _ hm))
        have hruS₆ : (s.1 + 1, s.2 + 1) ∉ S₆ := fun hm => Finset.notMem_erase _ _ hm
        set g₁ := Function.update (Function.update fT (s.1 + 1, s.2) (s.1 + 1, s.2 + 1))
          (s.1 + 1, s.2 + 1) (s.1 + 1, s.2)
        have hg₁ : IsTiling (insert (s.1 + 1, s.2) (insert (s.1 + 1, s.2 + 1) S₆)) g₁ :=
          isTiling_update_domino hfS₆ hne_rru hrS₆ hruS₆ (adjacent_mk_up _ _)
        have hs₁ : s ∉ insert (s.1 + 1, s.2) (insert (s.1 + 1, s.2 + 1) S₆) := by
          intro hm
          rw [Finset.mem_insert, Finset.mem_insert] at hm
          rcases hm with h | h | h
          · exact hne_sr h
          · exact hne_sru h
          · exact Finset.notMem_erase _ _
              (Finset.erase_subset _ _ (Finset.erase_subset _ _ (Finset.erase_subset _ _ h)))
        have hu₁ : (s.1, s.2 + 1) ∉ insert (s.1 + 1, s.2) (insert (s.1 + 1, s.2 + 1) S₆) := by
          intro hm
          rw [Finset.mem_insert, Finset.mem_insert] at hm
          rcases hm with h | h | h
          · exact hne_ur h
          · exact hne_uru h
          · exact Finset.notMem_erase _ _ (Finset.erase_subset _ _ h)
        set g₂ := Function.update (Function.update g₁ s (s.1, s.2 + 1))
          (s.1, s.2 + 1) s with hg₂def
        have hg₂ : IsTiling (insert s (insert (s.1, s.2 + 1)
            (insert (s.1 + 1, s.2) (insert (s.1 + 1, s.2 + 1) S₆)))) g₂ :=
          isTiling_update_domino hg₁ hne_su hs₁ hu₁ hadj_su
        have heS₆ : insert s (insert (s.1, s.2 + 1)
            (insert (s.1 + 1, s.2) (insert (s.1 + 1, s.2 + 1) S₆))) = S := by
          have e1 : insert (s.1 + 1, s.2 + 1) S₆ =
              ((S.erase s).erase (s.1 + 1, s.2)).erase (s.1, s.2 + 1) := by
            rw [hS₆def]
            exact Finset.insert_erase (Finset.mem_erase.mpr ⟨hne_ruu, hruS₄⟩)
          have e2 : insert (s.1, s.2 + 1)
              (((S.erase s).erase (s.1 + 1, s.2)).erase (s.1, s.2 + 1)) =
              (S.erase s).erase (s.1 + 1, s.2) :=
            Finset.insert_erase huS₄
          have e3 : insert (s.1 + 1, s.2) ((S.erase s).erase (s.1 + 1, s.2)) = S.erase s :=
            Finset.insert_erase (Finset.mem_erase.mpr ⟨hne_rs, hrS⟩)
          rw [e1, Finset.insert_comm (a := (s.1, s.2 + 1)) (b := (s.1 + 1, s.2)), e2, e3,
            Finset.insert_erase hsS]
        have hg₂S : IsTiling S g₂ := heS₆ ▸ hg₂
        have hg₂s : g₂ s = (s.1, s.2 + 1) := by
          rw [hg₂def, Function.update_of_ne hne_su, Function.update_self]
        exact hA ⟨g₂, hg₂S, hg₂s⟩
    · -- the empty region is trivially tastefully tiled
      have hSe : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst hSe
      refine ⟨id, ?_, ?_⟩
      · intro c hc
        exact absurd hc (Finset.notMem_empty c)
      · refine ⟨?_, ?_⟩ <;> intro i j hi <;> exact absurd hi (Finset.notMem_empty _)
  exact aux _ S rfl h

/-- Auxiliary conjunction for the staircase forcing lemmas, proved by
induction on `k`: the vertical domino on the diagonal cell `(x + k, y + k)`
and the horizontal domino on `(x + k + 1, y + k)` are both forced. -/
lemma tasteful_staircase_aux {S : Finset Cell} {f : Cell → Cell} (hf : IsTiling S f)
    (ht : Tasteful S f) {x y : ℤ} (hodd : Odd (x + y)) (hs : (x, y) ∈ S)
    (hsv : f (x, y) = (x, y + 1)) (hmin : ∀ c ∈ S, y ≤ c.2) :
    ∀ k : ℕ, ((∀ j ≤ k, (x + j, y + j) ∈ S) → (∀ j < k, (x + j + 1, y + j) ∈ S) →
        f (x + k, y + k) = (x + k, y + k + 1)) ∧
      ((∀ j ≤ k, (x + j, y + j) ∈ S) → (∀ j ≤ k, (x + j + 1, y + j) ∈ S) →
        f (x + k + 1, y + k) = (x + k + 2, y + k)) := by
  obtain ⟨m, hm⟩ := hodd
  intro k
  induction k with
  | zero =>
    simp only [Nat.cast_zero, add_zero]
    constructor
    · intro _ _
      exact hsv
    · intro _ hO
      have h1S : (x + 1, y) ∈ S := by
        simpa only [Nat.cast_zero, add_zero] using hO 0 (le_refl 0)
      obtain ⟨hmem, hinv, _, hadj⟩ := hf _ h1S
      rcases adjacent_cases hadj with hR | hL | hU | hD
      · -- right: the forced horizontal domino
        have hRc : f (x + 1, y) = (x + 1 + 1, y) := hR
        rw [hRc, Prod.mk.injEq]
        exact ⟨by omega, rfl⟩
      · -- left: `(x, y)` is already matched upward
        have hLc : f (x + 1, y) = (x + 1 - 1, y) := hL
        rw [hLc] at hinv
        have e : (x + 1 - 1, y) = (x, y) := by
          rw [Prod.mk.injEq]
          exact ⟨by omega, rfl⟩
        rw [e, hsv] at hinv
        have g1 := (Prod.mk_inj.mp hinv).1
        omega
      · -- up: a forbidden vertical pair with lower-left `(x, y)`
        have hUc : f (x + 1, y) = (x + 1, y + 1) := hU
        exact absurd ⟨hsv, hUc⟩ (ht.1 x y hs h1S ⟨m, hm⟩)
      · -- down: the cell `(x + 1, y - 1)` is not in `S`
        have hDc : f (x + 1, y) = (x + 1, y - 1) := hD
        rw [hDc] at hmem
        have h2 : y ≤ y - 1 := hmin _ hmem
        omega
  | succ k ih =>
    have hVk1_of : (∀ j ≤ k + 1, (x + j, y + j) ∈ S) →
        (∀ j < k + 1, (x + j + 1, y + j) ∈ S) →
        f (x + (k + 1 : ℕ), y + (k + 1 : ℕ)) = (x + (k + 1 : ℕ), y + (k + 1 : ℕ) + 1) := by
      intro hE hO
      have hEk : ∀ j ≤ k, (x + j, y + j) ∈ S := fun j hj => hE j (by omega)
      have hOltk : ∀ j < k, (x + j + 1, y + j) ∈ S := fun j hj => hO j (by omega)
      have hOlek : ∀ j ≤ k, (x + j + 1, y + j) ∈ S := fun j hj => hO j (by omega)
      have hVk : f (x + (k : ℕ), y + (k : ℕ)) = (x + (k : ℕ), y + (k : ℕ) + 1) :=
        ih.1 hEk hOltk
      have hHk : f (x + (k : ℕ) + 1, y + (k : ℕ)) = (x + (k : ℕ) + 2, y + (k : ℕ)) :=
        ih.2 hEk hOlek
      have hnS : (x + (k + 1 : ℕ), y + (k + 1 : ℕ)) ∈ S := hE (k + 1) le_rfl
      obtain ⟨-, hinv, _, hadj⟩ := hf _ hnS
      rcases adjacent_cases hadj with hR | hL | hU | hD
      · -- right: a forbidden horizontal pair with the horizontal domino below
        have hRc : f (x + (k + 1 : ℕ), y + (k + 1 : ℕ)) =
            (x + (k + 1 : ℕ) + 1, y + (k + 1 : ℕ)) := hR
        have e1 : (x + (k + 1 : ℕ), y + (k : ℕ)) = (x + (k : ℕ) + 1, y + (k : ℕ)) := by
          rw [Prod.mk.injEq]
          exact ⟨by omega, rfl⟩
        have hi1 : (x + (k + 1 : ℕ), y + (k : ℕ)) ∈ S := by
          rw [e1]
          exact hOlek k le_rfl
        have e2 : (x + (k + 1 : ℕ), y + (k : ℕ) + 1) =
            (x + (k + 1 : ℕ), y + (k + 1 : ℕ)) := by
          rw [Prod.mk.injEq]
          exact ⟨rfl, by omega⟩
        have hi2 : (x + (k + 1 : ℕ), y + (k : ℕ) + 1) ∈ S := by
          rw [e2]
          exact hnS
        have hpar : Even (x + (k + 1 : ℕ) + (y + (k : ℕ))) := ⟨m + (k : ℕ) + 1, by omega⟩
        have e3 : (x + (k + 1 : ℕ) + 1, y + (k : ℕ)) = (x + (k : ℕ) + 2, y + (k : ℕ)) := by
          rw [Prod.mk.injEq]
          exact ⟨by omega, rfl⟩
        have g1 : f (x + (k + 1 : ℕ), y + (k : ℕ)) =
            (x + (k + 1 : ℕ) + 1, y + (k : ℕ)) := by
          rw [e1, e3]
          exact hHk
        have e4 : (x + (k + 1 : ℕ) + 1, y + (k : ℕ) + 1) =
            (x + (k + 1 : ℕ) + 1, y + (k + 1 : ℕ)) := by
          rw [Prod.mk.injEq]
          exact ⟨rfl, by omega⟩
        have g2 : f (x + (k + 1 : ℕ), y + (k : ℕ) + 1) =
            (x + (k + 1 : ℕ) + 1, y + (k : ℕ) + 1) := by
          rw [e2, e4]
          exact hRc
        exact absurd ⟨g1, g2⟩ (ht.2 _ _ hi1 hi2 hpar)
      · -- left: the cell above `(x + k, y + k)` is already matched downward
        have hLc : f (x + (k + 1 : ℕ), y + (k + 1 : ℕ)) =
            (x + (k + 1 : ℕ) - 1, y + (k + 1 : ℕ)) := hL
        rw [hLc] at hinv
        have hinvk := (hf _ (hEk k le_rfl)).2.1
        rw [hVk] at hinvk
        have e : (x + (k + 1 : ℕ) - 1, y + (k + 1 : ℕ)) =
            (x + (k : ℕ), y + (k : ℕ) + 1) := by
          rw [Prod.mk.injEq]
          exact ⟨by omega, by omega⟩
        rw [e] at hinv
        have g1 := (Prod.mk_inj.mp (hinvk.symm.trans hinv)).1
        omega
      · -- up: the forced vertical domino
        exact hU
      · -- down: the cell below is already matched to the right
        have hDc : f (x + (k + 1 : ℕ), y + (k + 1 : ℕ)) =
            (x + (k + 1 : ℕ), y + (k + 1 : ℕ) - 1) := hD
        rw [hDc] at hinv
        have e : (x + (k + 1 : ℕ), y + (k + 1 : ℕ) - 1) =
            (x + (k : ℕ) + 1, y + (k : ℕ)) := by
          rw [Prod.mk.injEq]
          exact ⟨by omega, by omega⟩
        rw [e] at hinv
        have g1 := (Prod.mk_inj.mp (hHk.symm.trans hinv)).1
        omega
    refine ⟨hVk1_of, fun hE hO => ?_⟩
    have hEk : ∀ j ≤ k, (x + j, y + j) ∈ S := fun j hj => hE j (by omega)
    have hOlek : ∀ j ≤ k, (x + j + 1, y + j) ∈ S := fun j hj => hO j (by omega)
    have hHk : f (x + (k : ℕ) + 1, y + (k : ℕ)) = (x + (k : ℕ) + 2, y + (k : ℕ)) :=
      ih.2 hEk hOlek
    have hVk1 : f (x + (k + 1 : ℕ), y + (k + 1 : ℕ)) =
        (x + (k + 1 : ℕ), y + (k + 1 : ℕ) + 1) :=
      hVk1_of hE (fun j hj => hO j (by omega))
    have hqS : (x + (k + 1 : ℕ) + 1, y + (k + 1 : ℕ)) ∈ S := hO (k + 1) le_rfl
    obtain ⟨-, hinv, _, hadj⟩ := hf _ hqS
    rcases adjacent_cases hadj with hR | hL | hU | hD
    · -- right: the forced horizontal domino
      have hRc : f (x + (k + 1 : ℕ) + 1, y + (k + 1 : ℕ)) =
          (x + (k + 1 : ℕ) + 1 + 1, y + (k + 1 : ℕ)) := hR
      rw [hRc, Prod.mk.injEq]
      exact ⟨by omega, rfl⟩
    · -- left: the diagonal cell is already matched upward
      have hLc : f (x + (k + 1 : ℕ) + 1, y + (k + 1 : ℕ)) =
          (x + (k + 1 : ℕ) + 1 - 1, y + (k + 1 : ℕ)) := hL
      rw [hLc] at hinv
      have e : (x + (k + 1 : ℕ) + 1 - 1, y + (k + 1 : ℕ)) =
          (x + (k + 1 : ℕ), y + (k + 1 : ℕ)) := by
        rw [Prod.mk.injEq]
        exact ⟨by omega, rfl⟩
      rw [e] at hinv
      have g1 := (Prod.mk_inj.mp (hVk1.symm.trans hinv)).1
      omega
    · -- up: a forbidden vertical pair with the diagonal domino
      have hUc : f (x + (k + 1 : ℕ) + 1, y + (k + 1 : ℕ)) =
          (x + (k + 1 : ℕ) + 1, y + (k + 1 : ℕ) + 1) := hU
      have hnS : (x + (k + 1 : ℕ), y + (k + 1 : ℕ)) ∈ S := hE (k + 1) le_rfl
      have hpar : Odd (x + (k + 1 : ℕ) + (y + (k + 1 : ℕ))) := ⟨m + (k + 1 : ℕ), by omega⟩
      exact absurd ⟨hVk1, hUc⟩ (ht.1 _ _ hnS hqS hpar)
    · -- down: the cell below is already matched to the right
      have hDc : f (x + (k + 1 : ℕ) + 1, y + (k + 1 : ℕ)) =
          (x + (k + 1 : ℕ) + 1, y + (k + 1 : ℕ) - 1) := hD
      rw [hDc] at hinv
      have hinvk := (hf _ (hOlek k le_rfl)).2.1
      rw [hHk] at hinvk
      have e : (x + (k + 1 : ℕ) + 1, y + (k + 1 : ℕ) - 1) =
          (x + (k : ℕ) + 2, y + (k : ℕ)) := by
        rw [Prod.mk.injEq]
        exact ⟨by omega, by omega⟩
      rw [e] at hinv
      have g1 := (Prod.mk_inj.mp (hinvk.symm.trans hinv)).1
      omega

/-- Forced vertical dominoes on the staircase diagonal: in a tasteful tiling,
if `(x, y)` (with `x + y` odd) is matched upward and the whole diagonal
staircase up to `(x + k, y + k)` lies in `S`, then `(x + k, y + k)` is also
matched upward. -/
lemma tasteful_staircase_V {S : Finset Cell} {f : Cell → Cell} (hf : IsTiling S f)
    (ht : Tasteful S f) {x y : ℤ} (hodd : Odd (x + y)) (hs : (x, y) ∈ S)
    (hsv : f (x, y) = (x, y + 1)) (hmin : ∀ c ∈ S, y ≤ c.2) (k : ℕ)
    (hE : ∀ j ≤ k, (x + j, y + j) ∈ S) (hO : ∀ j < k, (x + j + 1, y + j) ∈ S) :
    f (x + k, y + k) = (x + k, y + k + 1) :=
  (tasteful_staircase_aux hf ht hodd hs hsv hmin k).1 hE hO

/-- Forced horizontal dominoes on the staircase: under the same hypotheses,
`(x + k + 1, y + k)` (if in `S`) is matched to the right. -/
lemma tasteful_staircase_H {S : Finset Cell} {f : Cell → Cell} (hf : IsTiling S f)
    (ht : Tasteful S f) {x y : ℤ} (hodd : Odd (x + y)) (hs : (x, y) ∈ S)
    (hsv : f (x, y) = (x, y + 1)) (hmin : ∀ c ∈ S, y ≤ c.2) (k : ℕ)
    (hE : ∀ j ≤ k, (x + j, y + j) ∈ S) (hO : ∀ j ≤ k, (x + j + 1, y + j) ∈ S) :
    f (x + k + 1, y + k) = (x + k + 2, y + k) :=
  (tasteful_staircase_aux hf ht hodd hs hsv hmin k).2 hE hO

variable {S : Finset Cell} {f g : Cell → Cell}

lemma IsTiling.mapsTo (hf : IsTiling S f) : ∀ c ∈ S, f c ∈ S := fun c hc ↦ (hf c hc).1
lemma IsTiling.involute (hf : IsTiling S f) : ∀ c ∈ S, f (f c) = c := fun c hc ↦ (hf c hc).2.1
lemma IsTiling.ne (hf : IsTiling S f) : ∀ c ∈ S, f c ≠ c := fun c hc ↦ (hf c hc).2.2.1
lemma IsTiling.adj (hf : IsTiling S f) : ∀ c ∈ S, Adjacent c (f c) := fun c hc ↦ (hf c hc).2.2.2

lemma IsTiling.injOn (hf : IsTiling S f) : Set.InjOn f S := by
  intro a ha b hb h
  have h2 : f (f a) = f (f b) := by rw [h]
  rwa [hf.involute a ha, hf.involute b hb] at h2

/-- Cells where two tilings disagree. -/
def sd (S : Finset Cell) (f g : Cell → Cell) : Finset Cell := S.filter fun c ↦ ¬ f c = g c

lemma mem_sd {c : Cell} : c ∈ sd S f g ↔ c ∈ S ∧ f c ≠ g c := Finset.mem_filter

lemma f_mem_sd (hf : IsTiling S f) (hg : IsTiling S g) {c : Cell} (hc : c ∈ sd S f g) :
    f c ∈ sd S f g := by
  rw [mem_sd] at hc ⊢
  obtain ⟨hcS, hne⟩ := hc
  refine ⟨(hf c hcS).1, ?_⟩
  rw [hf.involute c hcS]
  intro h
  apply hne
  have hfc : f c ∈ S := (hf c hcS).1
  have key : f c = g c := by
    calc f c = g (g (f c)) := by rw [hg.involute _ hfc]
      _ = g c := by rw [← h]
  exact key

lemma g_mem_sd (hf : IsTiling S f) (hg : IsTiling S g) {c : Cell} (hc : c ∈ sd S f g) :
    g c ∈ sd S f g := by
  rw [mem_sd] at hc ⊢
  obtain ⟨hcS, hne⟩ := hc
  refine ⟨(hg c hcS).1, ?_⟩
  rw [hg.involute c hcS]
  intro h
  apply hne
  have hgc : g c ∈ S := (hg c hcS).1
  have key : g c = f c := by
    calc g c = f (f (g c)) := by rw [hf.involute _ hgc]
      _ = f c := by rw [h]
  exact key.symm

/-- The alternating walk: `v 0 = s`, then alternate `g, f, g, f, ...`. -/
noncomputable def walk (s : Cell) (f g : Cell → Cell) : ℕ → Cell
  | 0 => s
  | n + 1 => (if Even n then g else f) (walk s f g n)

@[simp] lemma walk_zero (s : Cell) : walk s f g 0 = s := rfl
lemma walk_succ (s : Cell) (n : ℕ) : walk s f g (n + 1) = (if Even n then g else f) (walk s f g n) := rfl

lemma walk_mem (hf : IsTiling S f) (hg : IsTiling S g) {s : Cell} (hs : s ∈ sd S f g) (n : ℕ) :
    walk s f g n ∈ sd S f g := by
  induction n with
  | zero => simpa using hs
  | succ n ih =>
    rw [walk_succ]
    split_ifs with h
    · exact g_mem_sd hf hg ih
    · have : Odd n := Nat.not_even_iff_odd.mp h
      exact f_mem_sd hf hg ih

lemma walk_eq_g_of_even {s : Cell} {n : ℕ} (h : Even n) : walk s f g (n + 1) = g (walk s f g n) := by
  rw [walk_succ, if_pos h]

lemma walk_eq_f_of_odd {s : Cell} {n : ℕ} (h : Odd n) : walk s f g (n + 1) = f (walk s f g n) := by
  rw [walk_succ, if_neg (Nat.not_even_iff_odd.mpr h)]

lemma walk_even (s : Cell) (k : ℕ) : walk s f g (2 * k + 1) = g (walk s f g (2 * k)) :=
  walk_eq_g_of_even ⟨k, by ring⟩

lemma walk_odd (s : Cell) (k : ℕ) : walk s f g (2 * k + 2) = f (walk s f g (2 * k + 1)) :=
  walk_eq_f_of_odd ⟨k, rfl⟩

lemma walk_two_mul (s : Cell) (k : ℕ) : walk s f g (2 * (k + 1)) = f (g (walk s f g (2 * k))) := by
  have e1 : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
  rw [e1, walk_eq_f_of_odd (⟨k, by omega⟩ : Odd (2 * k + 1)),
    walk_eq_g_of_even (⟨k, by omega⟩ : Even (2 * k))]

lemma exists_ne_walk_eq (hf : IsTiling S f) (hg : IsTiling S g) {s : Cell} (hs : s ∈ sd S f g) :
    ∃ i j : ℕ, i ≠ j ∧ walk s f g i = walk s f g j := by
  have h : ∃ i j : ℕ, i ≠ j ∧ (⟨walk s f g i, walk_mem hf hg hs i⟩ : sd S f g) =
      ⟨walk s f g j, walk_mem hf hg hs j⟩ :=
    Finite.exists_ne_map_eq_of_infinite _
  obtain ⟨i, j, hij1, hij2⟩ := h
  exact ⟨i, j, hij1, by simpa using hij2⟩

lemma exists_cycle_data (hf : IsTiling S f) (hg : IsTiling S g) {s : Cell} (hs : s ∈ sd S f g) :
    ∃ m : ℕ, 2 ≤ m ∧ walk s f g (2 * m) = s ∧
      (∀ i < 2 * m, ∀ j < 2 * m, walk s f g i = walk s f g j → i = j) := by
  classical
  obtain ⟨i, j, hij_ne, hij_eq⟩ := exists_ne_walk_eq hf hg hs
  have hex : ∃ j : ℕ, ∃ i : ℕ, i < j ∧ walk s f g i = walk s f g j := by
    rcases lt_or_gt_of_ne hij_ne with h | h
    · exact ⟨j, i, h, hij_eq⟩
    · exact ⟨i, j, h, hij_eq.symm⟩
  let j₀ := Nat.find hex
  have hj₀ : ∃ i : ℕ, i < j₀ ∧ walk s f g i = walk s f g j₀ := Nat.find_spec hex
  obtain ⟨i₀, hi₀_lt, hi₀_eq⟩ := hj₀
  have hmin : ∀ j < j₀, ∀ i < j, walk s f g i ≠ walk s f g j := by
    intro j hj i hij h
    have hn : ¬ ∃ i : ℕ, i < j ∧ walk s f g i = walk s f g j := Nat.find_min hex hj
    exact hn ⟨i, hij, h⟩
  have hf2 : ∀ n, f (f (walk s f g n)) = walk s f g n :=
    fun n ↦ hf.involute _ (mem_sd.mp (walk_mem hf hg hs n)).1
  have hg2 : ∀ n, g (g (walk s f g n)) = walk s f g n :=
    fun n ↦ hg.involute _ (mem_sd.mp (walk_mem hf hg hs n)).1
  have hfinj : ∀ {a b : Cell}, a ∈ sd S f g → b ∈ sd S f g → f a = f b → a = b :=
    fun ha hb h ↦ hf.injOn (mem_sd.mp ha).1 (mem_sd.mp hb).1 h
  have hginj : ∀ {a b : Cell}, a ∈ sd S f g → b ∈ sd S f g → g a = g b → a = b :=
    fun ha hb h ↦ hg.injOn (mem_sd.mp ha).1 (mem_sd.mp hb).1 h
  have hw : ∀ n, walk s f g n ∈ sd S f g := walk_mem hf hg hs
  have hgne : ∀ n, g (walk s f g n) ≠ walk s f g n :=
    fun n ↦ hg.ne _ (mem_sd.mp (hw n)).1
  have hfg_ne : ∀ i, f (g (walk s f g i)) ≠ walk s f g i := by
    intro i h
    have hwS : walk s f g i ∈ S := (mem_sd.mp (hw i)).1
    have hgwS : g (walk s f g i) ∈ S := (hg _ hwS).1
    have h5 : g (walk s f g i) = f (walk s f g i) := by
      calc g (walk s f g i) = f (f (g (walk s f g i))) := by rw [hf.involute _ hgwS]
        _ = f (walk s f g i) := by rw [h]
    exact (mem_sd.mp (hw i)).2 h5.symm
  -- show i₀ = 0 by parity case analysis
  have hi₀ : i₀ = 0 := by
    by_contra hcon
    have hge1 : 1 ≤ i₀ := Nat.pos_of_ne_zero hcon
    have hj1 : 1 ≤ j₀ := by omega
    rcases Nat.even_or_odd i₀ with hei | hoi
    · rcases Nat.even_or_odd j₀ with hej | hoj
      · obtain ⟨a, ha⟩ := hei
        obtain ⟨b, hb⟩ := hej
        have hb1 : 1 ≤ b := by omega
        have ei₀ : walk s f g ((i₀ - 1) + 1) = f (walk s f g (i₀ - 1)) :=
          walk_eq_f_of_odd (⟨a - 1, by omega⟩ : Odd (i₀ - 1))
        rw [show i₀ - 1 + 1 = i₀ from by omega] at ei₀
        have ej₀ : walk s f g ((j₀ - 1) + 1) = f (walk s f g (j₀ - 1)) :=
          walk_eq_f_of_odd (⟨b - 1, by omega⟩ : Odd (j₀ - 1))
        rw [show j₀ - 1 + 1 = j₀ from by omega] at ej₀
        have : walk s f g (i₀ - 1) = walk s f g (j₀ - 1) :=
          hfinj (hw _) (hw _) (by rw [← ei₀, ← ej₀, hi₀_eq])
        exact hmin (j₀ - 1) (by omega) (i₀ - 1) (by omega) this
      · obtain ⟨a, ha⟩ := hei
        obtain ⟨b, hb⟩ := hoj
        have hlt1 : i₀ + 1 < j₀ := by
          rcases lt_or_eq_of_le (show i₀ + 1 ≤ j₀ from by omega) with h | h
          · exact h
          · exfalso
            have e1 : walk s f g (i₀ + 1) = g (walk s f g i₀) := walk_eq_g_of_even ⟨a, ha⟩
            rw [h, hi₀_eq] at e1
            exact hgne j₀ e1.symm
        have ej₀ : walk s f g ((j₀ - 1) + 1) = g (walk s f g (j₀ - 1)) :=
          walk_eq_g_of_even (⟨b, by omega⟩ : Even (j₀ - 1))
        rw [show j₀ - 1 + 1 = j₀ from by omega] at ej₀
        have ei₁ : walk s f g (i₀ + 1) = g (walk s f g i₀) := walk_eq_g_of_even ⟨a, ha⟩
        have h1 : walk s f g (j₀ - 1) = walk s f g (i₀ + 1) := by
          have e3 : g (walk s f g (j₀ - 1)) = walk s f g i₀ := by rw [← ej₀, hi₀_eq]
          calc walk s f g (j₀ - 1) = g (g (walk s f g (j₀ - 1))) := by rw [hg2]
            _ = g (walk s f g i₀) := by rw [e3]
            _ = walk s f g (i₀ + 1) := ei₁.symm
        rcases Nat.lt_or_eq_of_le (show i₀ + 1 ≤ j₀ - 1 from by omega) with hlt2 | heq2
        · exact hmin (j₀ - 1) (by omega) (i₀ + 1) (by omega) h1.symm
        · have h2 : j₀ = i₀ + 2 := by omega
          have h3 : walk s f g (i₀ + 2) = f (g (walk s f g i₀)) := by
            rw [show i₀ + 2 = (i₀ + 1) + 1 from by omega,
              walk_eq_f_of_odd (⟨a, by omega⟩ : Odd (i₀ + 1)), ei₁]
          have h4 : walk s f g (i₀ + 2) = walk s f g i₀ := by rw [← h2, hi₀_eq]
          rw [h3] at h4
          exact hfg_ne i₀ h4
    · rcases Nat.even_or_odd j₀ with hej | hoj
      · obtain ⟨a, ha⟩ := hoi
        obtain ⟨b, hb⟩ := hej
        have hb1 : 1 ≤ b := by omega
        have hlt1 : i₀ + 1 < j₀ := by
          rcases lt_or_eq_of_le (show i₀ + 1 ≤ j₀ from by omega) with h | h
          · exact h
          · exfalso
            have e1 : walk s f g (i₀ + 1) = f (walk s f g i₀) := walk_eq_f_of_odd ⟨a, ha⟩
            rw [h, hi₀_eq] at e1
            exact (hf.ne _ (mem_sd.mp (hw j₀)).1) e1.symm
        have ei₀ : walk s f g ((i₀ - 1) + 1) = g (walk s f g (i₀ - 1)) :=
          walk_eq_g_of_even (⟨a, by omega⟩ : Even (i₀ - 1))
        rw [show i₀ - 1 + 1 = i₀ from by omega] at ei₀
        have ej₀ : walk s f g ((j₀ - 1) + 1) = f (walk s f g (j₀ - 1)) :=
          walk_eq_f_of_odd (⟨b - 1, by omega⟩ : Odd (j₀ - 1))
        rw [show j₀ - 1 + 1 = j₀ from by omega] at ej₀
        have h1 : walk s f g (i₀ + 1) = walk s f g (j₀ - 1) := by
          have h2 : walk s f g (i₀ + 1) = f (walk s f g i₀) := walk_eq_f_of_odd ⟨a, ha⟩
          have e3 : f (walk s f g (j₀ - 1)) = walk s f g i₀ := by rw [← ej₀, hi₀_eq]
          calc walk s f g (i₀ + 1) = f (walk s f g i₀) := h2
            _ = f (f (walk s f g (j₀ - 1))) := by rw [e3]
            _ = walk s f g (j₀ - 1) := by rw [hf2]
        rcases Nat.lt_or_eq_of_le (show i₀ + 1 ≤ j₀ - 1 from by omega) with hlt2 | heq2
        · exact hmin (j₀ - 1) (by omega) (i₀ + 1) (by omega) h1
        · have h2 : j₀ = i₀ + 2 := by omega
          have h3 : walk s f g (i₀ + 2) = f (g (walk s f g i₀)) := by
            rw [show i₀ + 2 = 2 * (a + 1) from by omega, walk_two_mul,
              show 2 * a = i₀ from by omega]
          have h4 : walk s f g (i₀ + 2) = walk s f g i₀ := by rw [← h2, hi₀_eq]
          rw [h3] at h4
          exact hfg_ne i₀ h4
      · obtain ⟨a, ha⟩ := hoi
        obtain ⟨b, hb⟩ := hoj
        have ei₀ : walk s f g ((i₀ - 1) + 1) = g (walk s f g (i₀ - 1)) :=
          walk_eq_g_of_even (⟨a, by omega⟩ : Even (i₀ - 1))
        rw [show i₀ - 1 + 1 = i₀ from by omega] at ei₀
        have ej₀ : walk s f g ((j₀ - 1) + 1) = g (walk s f g (j₀ - 1)) :=
          walk_eq_g_of_even (⟨b, by omega⟩ : Even (j₀ - 1))
        rw [show j₀ - 1 + 1 = j₀ from by omega] at ej₀
        have : walk s f g (i₀ - 1) = walk s f g (j₀ - 1) :=
          hginj (hw _) (hw _) (by rw [← ei₀, ← ej₀, hi₀_eq])
        exact hmin (j₀ - 1) (by omega) (i₀ - 1) (by omega) this
  -- now j₀ is even, = 2m, m ≥ 2
  have hj₀_even : Even j₀ := by
    by_contra hcon
    have hoj : Odd j₀ := Nat.not_even_iff_odd.mp hcon
    obtain ⟨b, hb⟩ := hoj
    rw [hi₀] at hi₀_eq
    have ei₀0 : walk s f g j₀ = s := hi₀_eq.symm
    have hj1 : 1 ≤ j₀ := by omega
    have hjne1 : j₀ ≠ 1 := by
      intro h1
      have e1 : walk s f g 1 = s := by rw [← h1, ei₀0]
      rw [show (1 : ℕ) = 0 + 1 from by ring, walk_eq_g_of_even ⟨0, by omega⟩] at e1
      exact hgne 0 (by rw [walk_zero] at e1; exact e1)
    have hb1 : 1 ≤ b := by omega
    have ej₀ : walk s f g ((j₀ - 1) + 1) = g (walk s f g (j₀ - 1)) :=
      walk_eq_g_of_even (⟨b, by omega⟩ : Even (j₀ - 1))
    rw [show j₀ - 1 + 1 = j₀ from by omega] at ej₀
    have h1 : walk s f g (j₀ - 1) = walk s f g 1 := by
      have e3 : g (walk s f g (j₀ - 1)) = s := by rw [← ej₀, ei₀0]
      have e4 : walk s f g 1 = g s := walk_eq_g_of_even ⟨0, by omega⟩
      calc walk s f g (j₀ - 1) = g (g (walk s f g (j₀ - 1))) := by rw [hg2]
        _ = g s := by rw [e3]
        _ = walk s f g 1 := e4.symm
    rcases lt_or_eq_of_le hj1 with h1gt | h1eq
    · exact hmin (j₀ - 1) (by omega) 1 (by omega) h1.symm
    · exact hjne1 h1eq.symm
  obtain ⟨m, hm⟩ := hj₀_even
  have hjm : j₀ = 2 * m := by omega
  have hm2 : 2 ≤ m := by
    by_contra hcon
    have hmle : m ≤ 1 := by omega
    interval_cases m
    · omega
    · have hj2 : j₀ = 2 := by omega
      have h2 : f (g s) = s := by
        rw [hi₀, hj2] at hi₀_eq
        have e2 := walk_two_mul (f := f) (g := g) s 0
        rw [show 2 * (0 + 1) = (2 : ℕ) from by ring, show 2 * 0 = (0 : ℕ) from by ring,
          walk_zero] at e2
        rw [← hi₀_eq, walk_zero] at e2
        exact e2.symm
      exact hfg_ne 0 (by rw [walk_zero]; exact h2)
  have hinj : ∀ i < 2 * m, ∀ j < 2 * m, walk s f g i = walk s f g j → i = j := by
    intro i hi j hj h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hmin j (hjm.symm ▸ hj) i hlt h
    · exact hmin i (hjm.symm ▸ hi) j hgt h.symm
  have hret : walk s f g (2 * m) = s := by
    rw [hi₀, hjm] at hi₀_eq
    rw [walk_zero] at hi₀_eq
    exact hi₀_eq.symm
  exact ⟨m, hm2, hret, hinj⟩


-- ============================================================
-- Cycle edges, handshake parity, inside/outside
-- ============================================================

/-- Edges of the cycle through `s`, as 2-element finsets of cells. -/
noncomputable def cycEdges (s : Cell) (f g : Cell → Cell) (m : ℕ) : Finset (Finset Cell) :=
  (Finset.range (2 * m)).image fun i ↦ {walk s f g i, walk s f g (i + 1)}

lemma mem_cycEdges {s : Cell} {m : ℕ} {e : Finset Cell} :
    e ∈ cycEdges s f g m ↔ ∃ i ∈ Finset.range (2 * m), {walk s f g i, walk s f g (i + 1)} = e :=
  Finset.mem_image

lemma abs_one_cases {x : ℤ} (h : |x| = 1) : x = 1 ∨ x = -1 := by
  rcases lt_trichotomy x 0 with h1 | h1 | h1
  · rw [abs_of_neg h1] at h
    right; omega
  · rw [h1] at h
    simp at h
  · rw [abs_of_pos h1] at h
    left; omega

lemma min_max_of_abs_one {x y : ℤ} (h : |x - y| = 1) :
    (min x y = y ∧ max x y = x) ∨ (min x y = x ∧ max x y = y) := by
  rcases abs_one_cases h with h1 | h1
  · left
    rw [min_eq_right (show y ≤ x by omega), max_eq_left (show y ≤ x by omega)]
    exact ⟨rfl, rfl⟩
  · right
    rw [min_eq_left (show x ≤ y by omega), max_eq_right (show x ≤ y by omega)]
    exact ⟨rfl, rfl⟩

lemma pair_eq_pair {a b c d : Cell} (ha : a ≠ b) (h : ({a, b} : Finset Cell) = {c, d}) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have h1 : a ∈ ({c, d} : Finset Cell) := h ▸ Finset.mem_insert_self _ _
  have h2 : b ∈ ({c, d} : Finset Cell) := h ▸ Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
  rw [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  rcases h1 with h1 | h1
  · subst h1
    rcases h2 with h2 | h2
    · exact absurd h2.symm ha
    · exact Or.inl ⟨rfl, h2⟩
  · subst h1
    rcases h2 with h2 | h2
    · exact Or.inr ⟨rfl, h2⟩
    · exact absurd h2.symm ha

lemma walk_succ_adj (hf : IsTiling S f) (hg : IsTiling S g) {s : Cell} (hs : s ∈ sd S f g) (i : ℕ) :
    Adjacent (walk s f g i) (walk s f g (i + 1)) := by
  rw [walk_succ]
  split_ifs with h
  · exact hg.adj _ (mem_sd.mp (walk_mem hf hg hs i)).1
  · exact hf.adj _ (mem_sd.mp (walk_mem hf hg hs i)).1

lemma cycEdges_inj {m : ℕ} (hf : IsTiling S f) (hg : IsTiling S g) {s : Cell} (hs : s ∈ sd S f g)
    (hinj : ∀ i < 2 * m, ∀ j < 2 * m, walk s f g i = walk s f g j → i = j)
    (hm : 2 ≤ m) (hret : walk s f g (2 * m) = s) {i j : ℕ}
    (hi : i < 2 * m) (hj : j < 2 * m)
    (h : ({walk s f g i, walk s f g (i + 1)} : Finset Cell) = {walk s f g j, walk s f g (j + 1)}) :
    i = j := by
  have hne : walk s f g i ≠ walk s f g (i + 1) := by
    intro hne
    have hmem := walk_mem hf hg hs i
    rw [walk_succ] at hne
    split_ifs at hne
    · exact hg.ne _ (mem_sd.mp hmem).1 hne.symm
    · exact hf.ne _ (mem_sd.mp hmem).1 hne.symm
  have hp := pair_eq_pair hne h
  rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hinj i hi j hj h1
  · by_cases hji : j + 1 < 2 * m
    · have e1 : i = j + 1 := hinj i hi (j + 1) hji h1
      have e2 : i + 1 = j := by
        by_cases hi1 : i + 1 < 2 * m
        · exact hinj (i + 1) hi1 j hj h2
        · have hi1' : i + 1 = 2 * m := by omega
          rw [hi1'] at h2
          rw [hret] at h2
          have h20 : walk s f g 0 = walk s f g j := by rw [walk_zero]; exact h2
          have h0j := hinj 0 (by omega) j hj h20
          omega
      omega
    · have hj' : j = 2 * m - 1 := by omega
      rw [hj'] at h1 h2
      rw [show 2 * m - 1 + 1 = 2 * m from by omega, hret] at h1
      have e1 : i = 0 := hinj i hi 0 (by omega) (by rw [walk_zero]; exact h1)
      have hi1 : i + 1 < 2 * m := by omega
      have hj1 : 2 * m - 1 < 2 * m := by omega
      have e2 : i + 1 = 2 * m - 1 := hinj (i + 1) hi1 (2 * m - 1) hj1 h2
      omega

lemma edge_of_vertical (hf : IsTiling S f) (hg : IsTiling S g) {s : Cell} (hs : s ∈ sd S f g)
    (i : ℕ) (hx : (walk s f g i).1 = (walk s f g (i + 1)).1)
    {y : ℤ} (hy : ((walk s f g i).2 = y ∧ (walk s f g (i + 1)).2 = y + 1) ∨
      ((walk s f g i).2 = y + 1 ∧ (walk s f g (i + 1)).2 = y)) :
    ({walk s f g i, walk s f g (i + 1)} : Finset Cell) =
      {((walk s f g i).1, y), ((walk s f g i).1, y + 1)} := by
  rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have e1 : walk s f g i = ((walk s f g i).1, y) := by ext <;> simp [h1]
    have e2 : walk s f g (i + 1) = ((walk s f g i).1, y + 1) := by ext <;> simp [hx, h2]
    rw [e1, e2]
  · have e1 : walk s f g i = ((walk s f g i).1, y + 1) := by ext <;> simp [h1]
    have e2 : walk s f g (i + 1) = ((walk s f g i).1, y) := by ext <;> simp [hx, h2]
    rw [e1, e2]
    ext x
    simp [Finset.mem_insert, Finset.mem_singleton]
    tauto

/-- At most one cycle edge is vertical with given column `a` and min-height `y`. -/
lemma cycEdges_le_one {m : ℕ} (hf : IsTiling S f) (hg : IsTiling S g) {s : Cell} (hs : s ∈ sd S f g)
    (hinj : ∀ i < 2 * m, ∀ j < 2 * m, walk s f g i = walk s f g j → i = j)
    (hm : 2 ≤ m) (hret : walk s f g (2 * m) = s) (a y : ℤ) :
    ((Finset.range (2 * m)).filter fun i ↦ (walk s f g i).1 = a ∧ (walk s f g (i + 1)).1 = a ∧
      ((walk s f g i).2 = y ∧ (walk s f g (i + 1)).2 = y + 1 ∨
       (walk s f g i).2 = y + 1 ∧ (walk s f g (i + 1)).2 = y)).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro i j hi hj
  rw [Finset.mem_filter] at hi hj
  obtain ⟨hi1, hia, hia', hiy⟩ := hi
  obtain ⟨hj1, hja, hja', hjy⟩ := hj
  apply cycEdges_inj hf hg hs hinj hm hret (Finset.mem_range.mp hi1) (Finset.mem_range.mp hj1)
  have hxi : (walk s f g i).1 = (walk s f g (i + 1)).1 := by rw [hia, hia']
  have hxj : (walk s f g j).1 = (walk s f g (j + 1)).1 := by rw [hja, hja']
  have ei := edge_of_vertical hf hg hs i hxi hiy
  have ej := edge_of_vertical hf hg hs j hxj hjy
  rw [hia] at ei
  rw [hja] at ej
  rw [ei, ej]

/-- Vertical-edge ray count: cycle edges that are vertical, in column `> c.1`,
and spanning rows `c.2` to `c.2+1`. -/
noncomputable def Ncount (s : Cell) (f g : Cell → Cell) (m : ℕ) (c : Cell) : ℕ :=
  ((Finset.range (2 * m)).filter fun i ↦ (walk s f g i).1 = (walk s f g (i + 1)).1 ∧
    c.1 < (walk s f g i).1 ∧
    ((walk s f g i).2 = c.2 ∧ (walk s f g (i + 1)).2 = c.2 + 1 ∨
     (walk s f g i).2 = c.2 + 1 ∧ (walk s f g (i + 1)).2 = c.2)).card

/-- `inside c`: the even-odd rule with an eastward ray. -/
noncomputable def inside (s : Cell) (f g : Cell → Cell) (m : ℕ) (c : Cell) : Prop := Odd (Ncount s f g m c)

/-- Horizontal-edge ray count. -/
noncomputable def Nscount (s : Cell) (f g : Cell → Cell) (m : ℕ) (c : Cell) : ℕ :=
  ((Finset.range (2 * m)).filter fun i ↦ (walk s f g i).2 = (walk s f g (i + 1)).2 ∧
    (walk s f g i).2 < c.2 ∧
    ((walk s f g i).1 = c.1 ∧ (walk s f g (i + 1)).1 = c.1 + 1 ∨
     (walk s f g i).1 = c.1 + 1 ∧ (walk s f g (i + 1)).1 = c.1)).card

/-- Decomposition of `Ncount` along an eastward step. -/
lemma Ncount_east {m : ℕ} (hf : IsTiling S f) (hg : IsTiling S g) {s : Cell} (hs : s ∈ sd S f g)
    (hinj : ∀ i < 2 * m, ∀ j < 2 * m, walk s f g i = walk s f g j → i = j)
    (hm : 2 ≤ m) (hret : walk s f g (2 * m) = s) (c : Cell) :
    Ncount s f g m c = Ncount s f g m (c.1 + 1, c.2) +
      (if ({(c.1 + 1, c.2), (c.1 + 1, c.2 + 1)} : Finset Cell) ∈ cycEdges s f g m then 1 else 0) := by
  classical
  unfold Ncount
  have hdecomp : (Finset.range (2 * m)).filter
      (fun i ↦ (walk s f g i).1 = (walk s f g (i + 1)).1 ∧ c.1 < (walk s f g i).1 ∧
        ((walk s f g i).2 = c.2 ∧ (walk s f g (i + 1)).2 = c.2 + 1 ∨
         (walk s f g i).2 = c.2 + 1 ∧ (walk s f g (i + 1)).2 = c.2)) =
    (Finset.range (2 * m)).filter
      (fun i ↦ (walk s f g i).1 = (walk s f g (i + 1)).1 ∧ c.1 + 1 < (walk s f g i).1 ∧
        ((walk s f g i).2 = c.2 ∧ (walk s f g (i + 1)).2 = c.2 + 1 ∨
         (walk s f g i).2 = c.2 + 1 ∧ (walk s f g (i + 1)).2 = c.2)) ∪
    (Finset.range (2 * m)).filter
      (fun i ↦ (walk s f g i).1 = (walk s f g (i + 1)).1 ∧ (walk s f g i).1 = c.1 + 1 ∧
        ((walk s f g i).2 = c.2 ∧ (walk s f g (i + 1)).2 = c.2 + 1 ∨
         (walk s f g i).2 = c.2 + 1 ∧ (walk s f g (i + 1)).2 = c.2)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · intro h
      obtain ⟨h1, h2, h3, h4⟩ := h
      by_cases hx : (walk s f g i).1 = c.1 + 1
      · exact Or.inr ⟨h1, h2, hx, h4⟩
      · exact Or.inl ⟨h1, h2, by omega, h4⟩
    · intro h
      rcases h with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
      · exact ⟨h1, h2, by omega, h4⟩
      · exact ⟨h1, h2, by omega, h4⟩
  rw [hdecomp, Finset.card_union_of_disjoint (by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    rw [Finset.mem_filter] at hi1 hi2
    omega)]
  congr 1
  have hextra : ((Finset.range (2 * m)).filter fun i ↦ (walk s f g i).1 = (walk s f g (i + 1)).1 ∧
      (walk s f g i).1 = c.1 + 1 ∧
      ((walk s f g i).2 = c.2 ∧ (walk s f g (i + 1)).2 = c.2 + 1 ∨
       (walk s f g i).2 = c.2 + 1 ∧ (walk s f g (i + 1)).2 = c.2)).card =
      if ({(c.1 + 1, c.2), (c.1 + 1, c.2 + 1)} : Finset Cell) ∈ cycEdges s f g m then 1 else 0 := by
    by_cases h : ({(c.1 + 1, c.2), (c.1 + 1, c.2 + 1)} : Finset Cell) ∈ cycEdges s f g m
    · rw [if_pos h]
      rw [mem_cycEdges] at h
      obtain ⟨i, hi, hi2⟩ := h
      have hset : (Finset.range (2 * m)).filter (fun i' ↦ (walk s f g i').1 = (walk s f g (i' + 1)).1 ∧
          (walk s f g i').1 = c.1 + 1 ∧
          ((walk s f g i').2 = c.2 ∧ (walk s f g (i' + 1)).2 = c.2 + 1 ∨
           (walk s f g i').2 = c.2 + 1 ∧ (walk s f g (i' + 1)).2 = c.2)) = {i} := by
        ext i'
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · intro hi'
          obtain ⟨h1, h2, h3, h4⟩ := hi'
          have hxi' : (walk s f g i').1 = (walk s f g (i' + 1)).1 := h2
          have ei' := edge_of_vertical hf hg hs i' hxi' h4
          have hia' : (walk s f g (i' + 1)).1 = c.1 + 1 := by rw [← h2, h3]
          rw [h3] at ei'
          have : ({walk s f g i', walk s f g (i' + 1)} : Finset Cell) =
              {walk s f g i, walk s f g (i + 1)} := by rw [ei', hi2]
          exact cycEdges_inj hf hg hs hinj hm hret (Finset.mem_range.mp h1) (Finset.mem_range.mp hi) this
        · intro hi'
          rw [hi']
          have hne : walk s f g i ≠ walk s f g (i + 1) := by
            intro hne
            have hmem := walk_mem hf hg hs i
            rw [walk_succ] at hne
            split_ifs at hne
            · exact hg.ne _ (mem_sd.mp hmem).1 hne.symm
            · exact hf.ne _ (mem_sd.mp hmem).1 hne.symm
          rcases pair_eq_pair hne hi2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
          · rw [e1, e2]
            exact ⟨hi, by simp, by simp, Or.inl ⟨by simp, by simp⟩⟩
          · rw [e1, e2]
            exact ⟨hi, by simp, by simp, Or.inr ⟨by simp, by simp⟩⟩
      rw [hset, Finset.card_singleton]
    · rw [if_neg h]
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro i hi
      rw [Finset.mem_filter] at hi
      obtain ⟨h1, h2, h3, h4⟩ := hi
      apply h
      rw [mem_cycEdges]
      have hxi : (walk s f g i).1 = (walk s f g (i + 1)).1 := h2
      have ei := edge_of_vertical hf hg hs i hxi h4
      have hia' : (walk s f g (i + 1)).1 = c.1 + 1 := by rw [← h2, h3]
      rw [h3] at ei
      exact ⟨i, h1, ei⟩
  rw [hextra]


lemma edge_of_horizontal (hf : IsTiling S f) (hg : IsTiling S g) {s : Cell} (hs : s ∈ sd S f g)
    (i : ℕ) (hx : (walk s f g i).2 = (walk s f g (i + 1)).2)
    {x : ℤ} (hy : ((walk s f g i).1 = x ∧ (walk s f g (i + 1)).1 = x + 1) ∨
      ((walk s f g i).1 = x + 1 ∧ (walk s f g (i + 1)).1 = x)) :
    ({walk s f g i, walk s f g (i + 1)} : Finset Cell) =
      {(x, (walk s f g i).2), (x + 1, (walk s f g i).2)} := by
  rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have e1 : walk s f g i = (x, (walk s f g i).2) := by
      ext
      · simp [h1]
      · rfl
    have e2 : walk s f g (i + 1) = (x + 1, (walk s f g i).2) := by
      ext
      · simp [h2]
      · simp [hx]
    rw [e1, e2]
  · have e1 : walk s f g i = (x + 1, (walk s f g i).2) := by
      ext
      · simp [h1]
      · rfl
    have e2 : walk s f g (i + 1) = (x, (walk s f g i).2) := by
      ext
      · simp [h2]
      · simp [hx]
    rw [e1, e2]
    ext y
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto

lemma cycEdges_le_one_h {m : ℕ} (hf : IsTiling S f) (hg : IsTiling S g) {s : Cell} (hs : s ∈ sd S f g)
    (hinj : ∀ i < 2 * m, ∀ j < 2 * m, walk s f g i = walk s f g j → i = j)
    (hm : 2 ≤ m) (hret : walk s f g (2 * m) = s) (x y : ℤ) :
    ((Finset.range (2 * m)).filter fun i ↦ (walk s f g i).2 = y ∧ (walk s f g (i + 1)).2 = y ∧
      ((walk s f g i).1 = x ∧ (walk s f g (i + 1)).1 = x + 1 ∨
       (walk s f g i).1 = x + 1 ∧ (walk s f g (i + 1)).1 = x)).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro i j hi hj
  rw [Finset.mem_filter] at hi hj
  obtain ⟨hi1, hia, hia', hiy⟩ := hi
  obtain ⟨hj1, hja, hja', hjy⟩ := hj
  apply cycEdges_inj hf hg hs hinj hm hret (Finset.mem_range.mp hi1) (Finset.mem_range.mp hj1)
  have hxi : (walk s f g i).2 = (walk s f g (i + 1)).2 := by rw [hia, hia']
  have hxj : (walk s f g j).2 = (walk s f g (j + 1)).2 := by rw [hja, hja']
  have ei := edge_of_horizontal hf hg hs i hxi hiy
  have ej := edge_of_horizontal hf hg hs j hxj hjy
  rw [hia] at ei
  rw [hja] at ej
  rw [ei, ej]

lemma Nscount_south {m : ℕ} (hf : IsTiling S f) (hg : IsTiling S g) {s : Cell} (hs : s ∈ sd S f g)
    (hinj : ∀ i < 2 * m, ∀ j < 2 * m, walk s f g i = walk s f g j → i = j)
    (hm : 2 ≤ m) (hret : walk s f g (2 * m) = s) (c : Cell) :
    Nscount s f g m (c.1, c.2 + 1) = Nscount s f g m c +
      (if ({(c.1, c.2), (c.1 + 1, c.2)} : Finset Cell) ∈ cycEdges s f g m then 1 else 0) := by
  classical
  unfold Nscount
  have hdecomp : (Finset.range (2 * m)).filter
      (fun i ↦ (walk s f g i).2 = (walk s f g (i + 1)).2 ∧ (walk s f g i).2 < c.2 + 1 ∧
        ((walk s f g i).1 = c.1 ∧ (walk s f g (i + 1)).1 = c.1 + 1 ∨
         (walk s f g i).1 = c.1 + 1 ∧ (walk s f g (i + 1)).1 = c.1)) =
    (Finset.range (2 * m)).filter
      (fun i ↦ (walk s f g i).2 = (walk s f g (i + 1)).2 ∧ (walk s f g i).2 < c.2 ∧
        ((walk s f g i).1 = c.1 ∧ (walk s f g (i + 1)).1 = c.1 + 1 ∨
         (walk s f g i).1 = c.1 + 1 ∧ (walk s f g (i + 1)).1 = c.1)) ∪
    (Finset.range (2 * m)).filter
      (fun i ↦ (walk s f g i).2 = (walk s f g (i + 1)).2 ∧ (walk s f g i).2 = c.2 ∧
        ((walk s f g i).1 = c.1 ∧ (walk s f g (i + 1)).1 = c.1 + 1 ∨
         (walk s f g i).1 = c.1 + 1 ∧ (walk s f g (i + 1)).1 = c.1)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · intro h
      obtain ⟨h1, h2, h3, h4⟩ := h
      by_cases hx : (walk s f g i).2 = c.2
      · exact Or.inr ⟨h1, h2, hx, h4⟩
      · exact Or.inl ⟨h1, h2, by omega, h4⟩
    · intro h
      rcases h with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
      · exact ⟨h1, h2, by omega, h4⟩
      · exact ⟨h1, h2, by omega, h4⟩
  rw [hdecomp, Finset.card_union_of_disjoint (by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    rw [Finset.mem_filter] at hi1 hi2
    omega)]
  congr 1
  have hextra : ((Finset.range (2 * m)).filter fun i ↦ (walk s f g i).2 = (walk s f g (i + 1)).2 ∧
      (walk s f g i).2 = c.2 ∧
      ((walk s f g i).1 = c.1 ∧ (walk s f g (i + 1)).1 = c.1 + 1 ∨
       (walk s f g i).1 = c.1 + 1 ∧ (walk s f g (i + 1)).1 = c.1)).card =
      if ({(c.1, c.2), (c.1 + 1, c.2)} : Finset Cell) ∈ cycEdges s f g m then 1 else 0 := by
    by_cases h : ({(c.1, c.2), (c.1 + 1, c.2)} : Finset Cell) ∈ cycEdges s f g m
    · rw [if_pos h]
      rw [mem_cycEdges] at h
      obtain ⟨i, hi, hi2⟩ := h
      have hset : (Finset.range (2 * m)).filter (fun i' ↦ (walk s f g i').2 = (walk s f g (i' + 1)).2 ∧
          (walk s f g i').2 = c.2 ∧
          ((walk s f g i').1 = c.1 ∧ (walk s f g (i' + 1)).1 = c.1 + 1 ∨
           (walk s f g i').1 = c.1 + 1 ∧ (walk s f g (i' + 1)).1 = c.1)) = {i} := by
        ext i'
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · intro hi'
          obtain ⟨h1, h2, h3, h4⟩ := hi'
          have hxi' : (walk s f g i').2 = (walk s f g (i' + 1)).2 := h2
          have ei' := edge_of_horizontal hf hg hs i' hxi' h4
          have hia' : (walk s f g (i' + 1)).2 = c.2 := by rw [← h2, h3]
          rw [h3] at ei'
          have : ({walk s f g i', walk s f g (i' + 1)} : Finset Cell) =
              {walk s f g i, walk s f g (i + 1)} := by rw [ei', hi2]
          exact cycEdges_inj hf hg hs hinj hm hret (Finset.mem_range.mp h1) (Finset.mem_range.mp hi) this
        · intro hi'
          rw [hi']
          have hne : walk s f g i ≠ walk s f g (i + 1) := by
            intro hne
            have hmem := walk_mem hf hg hs i
            rw [walk_succ] at hne
            split_ifs at hne
            · exact hg.ne _ (mem_sd.mp hmem).1 hne.symm
            · exact hf.ne _ (mem_sd.mp hmem).1 hne.symm
          rcases pair_eq_pair hne hi2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
          · rw [e1, e2]
            exact ⟨hi, by simp, by simp, Or.inl ⟨by simp, by simp⟩⟩
          · rw [e1, e2]
            exact ⟨hi, by simp, by simp, Or.inr ⟨by simp, by simp⟩⟩
      rw [hset, Finset.card_singleton]
    · rw [if_neg h]
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro i hi
      rw [Finset.mem_filter] at hi
      obtain ⟨h1, h2, h3, h4⟩ := hi
      apply h
      rw [mem_cycEdges]
      have hxi : (walk s f g i).2 = (walk s f g (i + 1)).2 := h2
      have ei := edge_of_horizontal hf hg hs i hxi h4
      have hia' : (walk s f g (i + 1)).2 = c.2 := by rw [← h2, h3]
      rw [h3] at ei
      exact ⟨i, h1, ei⟩
  rw [hextra]

/-- Handshake: the number of cycle edges crossing a finset `U` is even. -/
lemma even_crossings {m : ℕ} {s : Cell} (hret : walk s f g (2 * m) = s) (U : Finset Cell) :
    Even ((Finset.range (2 * m)).filter
      (fun i ↦ (walk s f g i ∈ U) ≠ (walk s f g (i + 1) ∈ U))).card := by
  classical
  set a : ℕ → ℕ := fun i ↦ if walk s f g i ∈ U then 1 else 0
  have ha0 : a 0 = a (2 * m) := by
    simp only [a]
    rw [hret, walk_zero]
  have hshift : ∑ i ∈ Finset.range (2 * m), a (i + 1) = ∑ i ∈ Finset.range (2 * m), a i := by
    have h1 := Finset.sum_range_succ' a (2 * m)
    have h2 := Finset.sum_range_succ a (2 * m)
    rw [← ha0] at h2
    omega
  have hsum : ∑ i ∈ Finset.range (2 * m), (a i + a (i + 1)) = 2 * ∑ i ∈ Finset.range (2 * m), a i := by
    rw [Finset.sum_add_distrib, hshift]
    ring
  have hboth : ((Finset.range (2 * m)).filter (fun i ↦ walk s f g i ∈ U ∧ walk s f g (i + 1) ∈ U)).card =
      ∑ i ∈ Finset.range (2 * m), a i * a (i + 1) := by
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [a]
    split_ifs with h1 h2 h2 <;> simp_all
  have hcross : ((Finset.range (2 * m)).filter (fun i ↦ (walk s f g i ∈ U) ≠ (walk s f g (i + 1) ∈ U))).card =
      ∑ i ∈ Finset.range (2 * m), (a i + a (i + 1) - 2 * (a i * a (i + 1))) := by
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [a]
    split_ifs with h1 h2 h2 <;> simp_all
  have key : ((Finset.range (2 * m)).filter (fun i ↦ (walk s f g i ∈ U) ≠ (walk s f g (i + 1) ∈ U))).card +
      2 * ((Finset.range (2 * m)).filter (fun i ↦ walk s f g i ∈ U ∧ walk s f g (i + 1) ∈ U)).card =
      2 * ∑ i ∈ Finset.range (2 * m), a i := by
    rw [hcross, hboth]
    have hterm : ∑ i ∈ Finset.range (2 * m), (a i + a (i + 1) - 2 * (a i * a (i + 1))) +
        2 * ∑ i ∈ Finset.range (2 * m), a i * a (i + 1) =
        ∑ i ∈ Finset.range (2 * m), (a i + a (i + 1) - 2 * (a i * a (i + 1)) + 2 * (a i * a (i + 1))) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    rw [hterm]
    have hterm2 : ∑ i ∈ Finset.range (2 * m), (a i + a (i + 1) - 2 * (a i * a (i + 1)) + 2 * (a i * a (i + 1))) =
        ∑ i ∈ Finset.range (2 * m), (a i + a (i + 1)) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [a]
      split_ifs with h1 h2 h2 <;> simp_all
    rw [hterm2, hsum]
  have hfin : ((Finset.range (2 * m)).filter (fun i ↦ (walk s f g i ∈ U) ≠ (walk s f g (i + 1) ∈ U))).card =
      2 * (∑ i ∈ Finset.range (2 * m), a i -
        ((Finset.range (2 * m)).filter (fun i ↦ walk s f g i ∈ U ∧ walk s f g (i + 1) ∈ U)).card) := by
    omega
  rw [hfin]
  exact even_two_mul _


/-- The set of cycle cells. -/
noncomputable def cycSet (s : Cell) (f g : Cell → Cell) (m : ℕ) : Finset Cell :=
  (Finset.range (2 * m)).image (walk s f g)

lemma mem_cycSet {s : Cell} {m : ℕ} {c : Cell} :
    c ∈ cycSet s f g m ↔ ∃ i ∈ Finset.range (2 * m), walk s f g i = c :=
  Finset.mem_image

lemma cycSet_subset_sd (hf : IsTiling S f) (hg : IsTiling S g) {s : Cell} (hs : s ∈ sd S f g) {m : ℕ} :
    cycSet s f g m ⊆ sd S f g := by
  intro c hc
  rw [mem_cycSet] at hc
  obtain ⟨i, hi, rfl⟩ := hc
  exact walk_mem hf hg hs i

lemma edge_cells_mem_cycSet {m : ℕ} {s : Cell} {e : Finset Cell} {a b : Cell}
    (hret : walk s f g (2 * m) = s)
    (he : e ∈ cycEdges s f g m) (hab : e = {a, b}) : a ∈ cycSet s f g m ∧ b ∈ cycSet s f g m := by
  rw [mem_cycEdges] at he
  obtain ⟨i, hi, hei⟩ := he
  rw [hab] at hei
  have h1 : a ∈ ({walk s f g i, walk s f g (i + 1)} : Finset Cell) := by
    rw [hei]
    exact Finset.mem_insert_self _ _
  have h2 : b ∈ ({walk s f g i, walk s f g (i + 1)} : Finset Cell) := by
    rw [hei]
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
  rw [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  have second : walk s f g (i + 1) ∈ cycSet s f g m := by
    rw [mem_cycSet]
    by_cases hi1 : i + 1 < 2 * m
    · exact ⟨i + 1, Finset.mem_range.mpr hi1, rfl⟩
    · have hlt := Finset.mem_range.mp hi
      have hi1' : i + 1 = 2 * m := by omega
      have hpos : 0 < 2 * m := by omega
      refine ⟨0, Finset.mem_range.mpr hpos, ?_⟩
      rw [show walk s f g (i + 1) = s from by rw [hi1']; exact hret, walk_zero]
  constructor
  · rcases h1 with h1 | h1
    · rw [mem_cycSet]
      exact ⟨i, hi, h1.symm⟩
    · rw [h1]
      exact second
  · rcases h2 with h2 | h2
    · rw [mem_cycSet]
      exact ⟨i, hi, h2.symm⟩
    · rw [h2]
      exact second

/-- Box rule: `Ncount c + Nscount (c+(0,1))` is even. -/
lemma box_rule {m : ℕ} (hf : IsTiling S f) (hg : IsTiling S g) {s : Cell} (hs : s ∈ sd S f g)
    (hinj : ∀ i < 2 * m, ∀ j < 2 * m, walk s f g i = walk s f g j → i = j)
    (hm : 2 ≤ m) (hret : walk s f g (2 * m) = s) (c : Cell) :
    Even (Ncount s f g m c + Nscount s f g m (c.1, c.2 + 1)) := by
  classical
  have hsS : s ∈ S := (mem_sd.mp hs).1
  have hne : S.Nonempty := ⟨s, hsS⟩
  set M := (S.image (·.1)).max' (hne.image _)
  set m₀ := (S.image (·.2)).min' (hne.image _)
  have hM : ∀ x ∈ S, x.1 ≤ M := fun x hx ↦ Finset.le_max' _ _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  have hm₀ : ∀ x ∈ S, m₀ ≤ x.2 := fun x hx ↦ Finset.min'_le _ _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  have hbds : ∀ i, (walk s f g i).1 ≤ M ∧ m₀ ≤ (walk s f g i).2 := by
    intro i
    have h := walk_mem hf hg hs i
    have hS := (mem_sd.mp h).1
    exact ⟨hM _ hS, hm₀ _ hS⟩
  set U : Finset Cell := Finset.Icc (c.1 + 1) M ×ˢ Finset.Icc m₀ c.2
  have hcross := even_crossings hret U
  -- characterize crossings
  have hUx : ∀ x : Cell, (x ∈ U ↔ (c.1 + 1 ≤ x.1 ∧ x.1 ≤ M) ∧ (m₀ ≤ x.2 ∧ x.2 ≤ c.2)) := by
    intro x
    simp [U]
  have hne_iff : ∀ p q : Prop, (p ≠ q) ↔ (p ∧ ¬ q) ∨ (¬ p ∧ q) := by
    intro p q
    by_cases hp : p <;> by_cases hq : q <;> simp_all
  have hc : ∀ i ∈ Finset.range (2 * m), ((walk s f g i ∈ U) ≠ (walk s f g (i + 1) ∈ U)) ↔
      ((walk s f g i).1 = (walk s f g (i + 1)).1 ∧ c.1 < (walk s f g i).1 ∧
        ((walk s f g i).2 = c.2 ∧ (walk s f g (i + 1)).2 = c.2 + 1 ∨
         (walk s f g i).2 = c.2 + 1 ∧ (walk s f g (i + 1)).2 = c.2)) ∨
      ((walk s f g i).2 = (walk s f g (i + 1)).2 ∧ (walk s f g i).2 < c.2 + 1 ∧
        ((walk s f g i).1 = c.1 ∧ (walk s f g (i + 1)).1 = c.1 + 1 ∨
         (walk s f g i).1 = c.1 + 1 ∧ (walk s f g (i + 1)).1 = c.1)) := by
    intro i hi
    have hb1 := hbds i
    have hadj := walk_succ_adj hf hg hs i
    rw [hne_iff]
    rcases adjacent_cases hadj with ha | ha | ha | ha
    · -- walk (i+1) = (x+1, y): horizontal right
      have hb2 := hbds (i + 1)
      rw [ha] at hb2
      simp at hb2
      have hA : walk s f g i ∈ U → walk s f g (i + 1) ∈ U := by
        intro h
        rw [hUx] at h ⊢
        rw [ha] at ⊢
        obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
        exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
      have hA' : (walk s f g i ∉ U ∧ walk s f g (i + 1) ∈ U) ↔
          ((walk s f g i).2 ≤ c.2 ∧ (walk s f g i).1 = c.1) := by
        constructor
        · intro h
          obtain ⟨h1, h2⟩ := h
          rw [hUx] at h1 h2
          rw [ha] at h2
          obtain ⟨⟨h21, h22⟩, h23, h24⟩ := h2
          have : (walk s f g i).1 < c.1 + 1 ∨ (walk s f g i).2 > c.2 := by
            by_contra hcon
            push_neg at hcon
            exact h1 ⟨⟨hcon.1, hb1.1⟩, hb1.2, hcon.2⟩
          rcases this with hthis | hthis
          · exact ⟨by omega, by omega⟩
          · exfalso; omega
        · intro h
          obtain ⟨h1, h2⟩ := h
          constructor
          · rw [hUx]
            omega
          · rw [ha]
            rw [hUx]
            exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
      constructor
      · intro h
        rcases h with h | h
        · exact absurd (hA h.1) h.2
        · rw [hA'] at h
          obtain ⟨h1, h2⟩ := h
          refine Or.inr ⟨?_, ?_, Or.inl ⟨?_, ?_⟩⟩
          · rw [ha]
          · omega
          · omega
          · rw [ha]
            simp [h2]
      · intro h
        rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · rw [ha] at h1
          simp at h1
        · rcases h3 with ⟨h3, h4⟩ | ⟨h3, h4⟩
          · right
            rw [hA']
            exact ⟨by omega, by omega⟩
          · rw [ha] at h4
            simp at h4
            omega
    · -- walk (i+1) = (x-1, y): horizontal left
      have hb2 := hbds (i + 1)
      rw [ha] at hb2
      simp at hb2
      have hC : walk s f g (i + 1) ∈ U → walk s f g i ∈ U := by
        intro h
        rw [ha] at h
        rw [hUx] at h ⊢
        obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
        exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
      have hC' : (walk s f g i ∈ U ∧ walk s f g (i + 1) ∉ U) ↔
          ((walk s f g i).2 ≤ c.2 ∧ (walk s f g i).1 = c.1 + 1) := by
        constructor
        · intro h
          obtain ⟨h1, h2⟩ := h
          rw [hUx] at h1 h2
          rw [ha] at h2
          obtain ⟨⟨h11, h12⟩, h13, h14⟩ := h1
          have : (walk s f g i).1 < c.1 + 2 := by
            by_contra hcon
            push_neg at hcon
            exact h2 ⟨⟨by omega, by omega⟩, by omega, by omega⟩
          exact ⟨by omega, by omega⟩
        · intro h
          obtain ⟨h1, h2⟩ := h
          constructor
          · rw [hUx]
            exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
          · rw [ha]
            rw [hUx]
            omega
      constructor
      · intro h
        rcases h with h | h
        · rw [hC'] at h
          obtain ⟨h1, h2⟩ := h
          refine Or.inr ⟨?_, ?_, Or.inr ⟨?_, ?_⟩⟩
          · rw [ha]
          · omega
          · omega
          · rw [ha]
            simp [h2]
        · exact absurd (hC h.2) h.1
      · intro h
        rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · rw [ha] at h1
          simp at h1
          omega
        · rcases h3 with ⟨h3, h4⟩ | ⟨h3, h4⟩
          · rw [ha] at h4
            simp at h4
            omega
          · left
            rw [hC']
            exact ⟨by omega, by omega⟩
    · -- walk (i+1) = (x, y+1): vertical up
      have hb2 := hbds (i + 1)
      rw [ha] at hb2
      simp at hb2
      have hB : walk s f g (i + 1) ∈ U → walk s f g i ∈ U := by
        intro h
        rw [ha] at h
        rw [hUx] at h ⊢
        obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
        exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
      have hB' : (walk s f g i ∈ U ∧ walk s f g (i + 1) ∉ U) ↔
          (c.1 < (walk s f g i).1 ∧ (walk s f g i).2 = c.2) := by
        constructor
        · intro h
          obtain ⟨h1, h2⟩ := h
          rw [hUx] at h1 h2
          rw [ha] at h2
          obtain ⟨⟨h11, h12⟩, h13, h14⟩ := h1
          have hy : (walk s f g i).2 = c.2 := by
            by_contra hcon
            push_neg at hcon
            apply h2
            rcases (by omega : (walk s f g i).2 < c.2 ∨ c.2 < (walk s f g i).2) with hle | hle
            · exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
            · exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
          exact ⟨by omega, by omega⟩
        · intro h
          obtain ⟨h1, h2⟩ := h
          constructor
          · rw [hUx]
            exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
          · rw [ha]
            rw [hUx]
            omega
      constructor
      · intro h
        rcases h with h | h
        · rw [hB'] at h
          obtain ⟨h1, h2⟩ := h
          refine Or.inl ⟨?_, ?_, Or.inl ⟨?_, ?_⟩⟩
          · simp [ha]
          · omega
          · omega
          · rw [ha]
            simp [h2]
        · exact absurd (hB h.2) h.1
      · intro h
        rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · rcases h3 with ⟨h3, h4⟩ | ⟨h3, h4⟩
          · left
            rw [hB']
            exact ⟨by omega, by omega⟩
          · rw [ha] at h4
            simp at h4
            omega
        · rw [ha] at h1
          simp at h1
    · -- walk (i+1) = (x, y-1): vertical down
      have hb2 := hbds (i + 1)
      rw [ha] at hb2
      simp at hb2
      have hD : walk s f g i ∈ U → walk s f g (i + 1) ∈ U := by
        intro h
        rw [hUx] at h ⊢
        rw [ha] at ⊢
        obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
        exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
      have hD' : (walk s f g i ∉ U ∧ walk s f g (i + 1) ∈ U) ↔
          (c.1 < (walk s f g i).1 ∧ (walk s f g i).2 = c.2 + 1) := by
        constructor
        · intro h
          obtain ⟨h1, h2⟩ := h
          rw [hUx] at h1 h2
          rw [ha] at h2
          obtain ⟨⟨h21, h22⟩, h23, h24⟩ := h2
          have : (walk s f g i).2 > c.2 := by
            by_contra hcon
            push_neg at hcon
            apply h1
            rcases (by omega : (walk s f g i).1 < c.1 + 1 ∨ c.1 + 1 ≤ (walk s f g i).1) with hle | hle
            · exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
            · exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
          exact ⟨by omega, by omega⟩
        · intro h
          obtain ⟨h1, h2⟩ := h
          constructor
          · rw [hUx]
            omega
          · rw [ha]
            rw [hUx]
            exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
      constructor
      · intro h
        rcases h with h | h
        · exact absurd (hD h.1) h.2
        · rw [hD'] at h
          obtain ⟨h1, h2⟩ := h
          refine Or.inl ⟨?_, ?_, Or.inr ⟨?_, ?_⟩⟩
          · simp [ha]
          · omega
          · omega
          · rw [ha]
            simp [h2]
      · intro h
        rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · rcases h3 with ⟨h3, h4⟩ | ⟨h3, h4⟩
          · rw [ha] at h4
            simp at h4
            omega
          · right
            rw [hD']
            exact ⟨by omega, by omega⟩
        · rw [ha] at h1
          simp at h1
          omega
  have hcrossset : (Finset.range (2 * m)).filter (fun i ↦ (walk s f g i ∈ U) ≠ (walk s f g (i + 1) ∈ U)) =
      (Finset.range (2 * m)).filter (fun i ↦ (walk s f g i).1 = (walk s f g (i + 1)).1 ∧
        c.1 < (walk s f g i).1 ∧
        ((walk s f g i).2 = c.2 ∧ (walk s f g (i + 1)).2 = c.2 + 1 ∨
         (walk s f g i).2 = c.2 + 1 ∧ (walk s f g (i + 1)).2 = c.2)) ∪
      (Finset.range (2 * m)).filter (fun i ↦ (walk s f g i).2 = (walk s f g (i + 1)).2 ∧
        (walk s f g i).2 < c.2 + 1 ∧
        ((walk s f g i).1 = c.1 ∧ (walk s f g (i + 1)).1 = c.1 + 1 ∨
         (walk s f g i).1 = c.1 + 1 ∧ (walk s f g (i + 1)).1 = c.1)) := by
    ext i
    by_cases hi : i ∈ Finset.range (2 * m)
    · simp only [Finset.mem_filter, Finset.mem_union]
      rw [hc i hi]
      constructor
      · intro h
        obtain ⟨h1, h2⟩ := h
        rcases h2 with h2 | h2
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr ⟨h1, h2⟩
      · intro h
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨h1, Or.inl h2⟩
        · exact ⟨h1, Or.inr h2⟩
    · simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_range]
      simp only [Finset.mem_range] at hi
      constructor
      · intro h
        obtain ⟨h1, h2⟩ := h
        exact absurd h1 hi
      · intro h
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact absurd h1 hi
        · exact absurd h1 hi
  rw [hcrossset, Finset.card_union_of_disjoint (by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    rw [Finset.mem_filter] at hi1 hi2
    have hadj := walk_succ_adj hf hg hs i
    rcases adjacent_cases hadj with ha | ha | ha | ha
    · rw [ha] at hi1; simp at hi1
    · rw [ha] at hi1; simp at hi1; omega
    · rw [ha] at hi2; simp at hi2
    · rw [ha] at hi2; simp at hi2; omega)] at hcross
  unfold Ncount Nscount
  exact hcross

-- ============================================================
-- Inside/outside: direction rules, path invariance, Jordan property
-- ============================================================

/-- The box relation at a cell: `Ncount c + Nscount c + ind({c, c+(1,0)})` is even.
This is the consistency relation between the east ray and the south ray. -/
lemma box_south_rel {m : ℕ} (hf : IsTiling S f) (hg : IsTiling S g) {s : Cell}
    (hs : s ∈ sd S f g) (hinj : ∀ i < 2 * m, ∀ j < 2 * m, walk s f g i = walk s f g j → i = j)
    (hm : 2 ≤ m) (hret : walk s f g (2 * m) = s) (c : Cell) :
    Even (Ncount s f g m c + Nscount s f g m c +
      (if ({(c.1, c.2), (c.1 + 1, c.2)} : Finset Cell) ∈ cycEdges s f g m then 1 else 0)) := by
  have h1 := box_rule hf hg hs hinj hm hret c
  have h2 := Nscount_south hf hg hs hinj hm hret c
  rw [h2] at h1
  obtain ⟨a, ha⟩ := h1
  refine ⟨a, by omega⟩

/-- Parity rule for a north step: `Ncount (c+(0,1)) + Ncount c + ind` is even,
where `ind` counts the horizontal cycle edge to the east of the target cell. -/
lemma north_rel {m : ℕ} (hf : IsTiling S f) (hg : IsTiling S g) {s : Cell}
    (hs : s ∈ sd S f g) (hinj : ∀ i < 2 * m, ∀ j < 2 * m, walk s f g i = walk s f g j → i = j)
    (hm : 2 ≤ m) (hret : walk s f g (2 * m) = s) (c : Cell) :
    Even (Ncount s f g m (c.1, c.2 + 1) + Ncount s f g m c +
      (if ({(c.1, c.2 + 1), (c.1 + 1, c.2 + 1)} : Finset Cell) ∈ cycEdges s f g m
        then 1 else 0)) := by
  have hR1 : Even (Ncount s f g m (c.1, c.2 + 1) + Nscount s f g m (c.1, c.2 + 1) +
      (if ({(c.1, c.2 + 1), (c.1 + 1, c.2 + 1)} : Finset Cell) ∈ cycEdges s f g m
        then 1 else 0)) := box_south_rel hf hg hs hinj hm hret (c.1, c.2 + 1)
  have hR2 := box_south_rel hf hg hs hinj hm hret c
  have hS := Nscount_south hf hg hs hinj hm hret c
  rw [hS] at hR1
  obtain ⟨a, ha⟩ := hR1
  obtain ⟨b, hb⟩ := hR2
  refine ⟨a + b - (Nscount s f g m c +
    (if ({(c.1, c.2), (c.1 + 1, c.2)} : Finset Cell) ∈ cycEdges s f g m then 1 else 0)), by omega⟩

/-- Adjacent cells that both lie off the cycle have the same inside status. -/
lemma inside_adj_of_not_mem {m : ℕ} (hf : IsTiling S f) (hg : IsTiling S g) {s : Cell}
    (hs : s ∈ sd S f g) (hinj : ∀ i < 2 * m, ∀ j < 2 * m, walk s f g i = walk s f g j → i = j)
    (hm : 2 ≤ m) (hret : walk s f g (2 * m) = s) {c c' : Cell}
    (hadj : Adjacent c c') (hc : c ∉ cycSet s f g m) (hc' : c' ∉ cycSet s f g m) :
    inside s f g m c ↔ inside s f g m c' := by
  rcases adjacent_cases hadj with h | h | h | h
  · -- east step: c' = (c.1 + 1, c.2)
    have h0 : ({(c.1 + 1, c.2), (c.1 + 1, c.2 + 1)} : Finset Cell) ∉ cycEdges s f g m := by
      intro he
      have hh := edge_cells_mem_cycSet (a := (c.1 + 1, c.2)) (b := (c.1 + 1, c.2 + 1)) hret he rfl
      rw [h] at hc'
      exact hc' hh.1
    have h1 := Ncount_east hf hg hs hinj hm hret c
    rw [if_neg h0, add_zero] at h1
    unfold inside
    rw [h, h1]
  · -- west step: c' = (c.1 - 1, c.2)
    have h0 : ({(c.1, c.2), (c.1, c.2 + 1)} : Finset Cell) ∉ cycEdges s f g m := by
      intro he
      have hh := edge_cells_mem_cycSet (a := (c.1, c.2)) (b := (c.1, c.2 + 1)) hret he rfl
      exact hc hh.1
    have h1 : Ncount s f g m (c.1 - 1, c.2) = Ncount s f g m (c.1 - 1 + 1, c.2) +
        (if ({(c.1 - 1 + 1, c.2), (c.1 - 1 + 1, c.2 + 1)} : Finset Cell) ∈ cycEdges s f g m
          then 1 else 0) := Ncount_east hf hg hs hinj hm hret (c.1 - 1, c.2)
    rw [show c.1 - 1 + 1 = c.1 by ring, if_neg h0, add_zero] at h1
    unfold inside
    rw [h, h1]
  · -- north step: c' = (c.1, c.2 + 1)
    have h0 : ({(c.1, c.2 + 1), (c.1 + 1, c.2 + 1)} : Finset Cell) ∉ cycEdges s f g m := by
      intro he
      have hh := edge_cells_mem_cycSet (a := (c.1, c.2 + 1)) (b := (c.1 + 1, c.2 + 1)) hret he rfl
      rw [h] at hc'
      exact hc' hh.1
    have h1 := north_rel hf hg hs hinj hm hret c
    rw [if_neg h0, add_zero] at h1
    obtain ⟨k, hk⟩ := h1
    unfold inside
    rw [h]
    constructor
    · intro ⟨a, ha⟩
      refine ⟨k - (a + 1), by omega⟩
    · intro ⟨a, ha⟩
      refine ⟨k - (a + 1), by omega⟩
  · -- south step: c' = (c.1, c.2 - 1)
    have h0 : ({(c.1, c.2), (c.1 + 1, c.2)} : Finset Cell) ∉ cycEdges s f g m := by
      intro he
      have hh := edge_cells_mem_cycSet (a := (c.1, c.2)) (b := (c.1 + 1, c.2)) hret he rfl
      exact hc hh.1
    have h1 : Even (Ncount s f g m (c.1, c.2 - 1 + 1) + Ncount s f g m (c.1, c.2 - 1) +
        (if ({(c.1, c.2 - 1 + 1), (c.1 + 1, c.2 - 1 + 1)} : Finset Cell) ∈ cycEdges s f g m
          then 1 else 0)) := north_rel hf hg hs hinj hm hret (c.1, c.2 - 1)
    rw [show c.2 - 1 + 1 = c.2 by ring, if_neg h0, add_zero] at h1
    obtain ⟨k, hk⟩ := h1
    rw [Prod.eta] at hk
    unfold inside
    rw [h]
    constructor
    · intro ⟨a, ha⟩
      refine ⟨k - (a + 1), by omega⟩
    · intro ⟨a, ha⟩
      refine ⟨k - (a + 1), by omega⟩

/-- Inside status is constant along paths avoiding the cycle. -/
lemma inside_of_cellPath {m : ℕ} (hf : IsTiling S f) (hg : IsTiling S g) {s : Cell}
    (hs : s ∈ sd S f g) (hinj : ∀ i < 2 * m, ∀ j < 2 * m, walk s f g i = walk s f g j → i = j)
    (hm : 2 ≤ m) (hret : walk s f g (2 * m) = s) {c c' : Cell}
    (hpath : CellPath (· ∉ cycSet s f g m) c c') :
    inside s f g m c ↔ inside s f g m c' := by
  induction hpath with
  | refl => exact Iff.rfl
  | tail hab hstep ih =>
    obtain ⟨hb, hc', hadj⟩ := hstep
    exact ih.trans (inside_adj_of_not_mem hf hg hs hinj hm hret hadj hb hc')

/-- The Jordan property for the alternating cycle: every inside cell lies in `S`.
Indeed, a cell outside `S` is connected to a far eastern cell (which is not
inside) by a path staying outside `S`, hence avoiding the cycle. -/
lemma inside_mem_S {m : ℕ} (hf : IsTiling S f) (hg : IsTiling S g) (hcc : ComplConnected S)
    {s : Cell} (hs : s ∈ sd S f g)
    (hinj : ∀ i < 2 * m, ∀ j < 2 * m, walk s f g i = walk s f g j → i = j)
    (hm : 2 ≤ m) (hret : walk s f g (2 * m) = s) {c : Cell}
    (hc : inside s f g m c) : c ∈ S := by
  by_contra hcS
  have hsS : s ∈ S := (mem_sd.mp hs).1
  have hne : S.Nonempty := ⟨s, hsS⟩
  set M := (S.image Prod.fst).max' (hne.image _) with hMdef
  have hM : ∀ x ∈ S, x.1 ≤ M := fun x hx ↦ Finset.le_max' _ _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  set z : Cell := (M + 1, c.2) with hzdef
  have hzS : z ∉ S := by
    intro hmz
    have h1 := hM z hmz
    rw [hzdef] at h1
    change M + 1 ≤ M at h1
    omega
  -- a path from `c` to `z` outside `S`; it avoids the cycle since `cycSet ⊆ S`
  have hpathS : CellPath (· ∉ S) c z := hcc c hcS z hzS
  have hmono : ∀ a b : Cell, ((· ∉ S) a ∧ (· ∉ S) b ∧ Adjacent a b) →
      ((· ∉ cycSet s f g m) a ∧ (· ∉ cycSet s f g m) b ∧ Adjacent a b) := by
    intro a b ⟨ha, hb, hab⟩
    have hsub : cycSet s f g m ⊆ S := by
      intro x hx
      have hx' := cycSet_subset_sd hf hg hs hx
      exact (mem_sd.mp hx').1
    exact ⟨fun ha' ↦ ha (hsub ha'), fun hb' ↦ hb (hsub hb'), hab⟩
  have hpath : CellPath (· ∉ cycSet s f g m) c z :=
    Relation.ReflTransGen.mono hmono c z hpathS
  have hcz := inside_of_cellPath hf hg hs hinj hm hret hpath
  -- but `z` is not inside: no cycle cell lies to its right
  have hN0 : Ncount s f g m z = 0 := by
    unfold Ncount
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro i hi
    rw [Finset.mem_filter] at hi
    obtain ⟨h1, h2, h3, -⟩ := hi
    have hwi : walk s f g i ∈ S := (mem_sd.mp (walk_mem hf hg hs i)).1
    have h4 := hM _ hwi
    rw [hzdef] at h3
    simp at h3
    omega
  rw [hcz] at hc
  unfold inside at hc
  rw [hN0] at hc
  obtain ⟨a, ha⟩ := hc
  omega

-- ============================================================
-- Level function and staircase cells (for Lemma A)
-- ============================================================

/-- The level of a cell relative to base point `(x, y)`:
`(c.2 - y) - (c.1 - x) + 1`.  Adjacent cells differ by exactly one in level;
moving east or south decreases the level, moving west or north increases it. -/
def lvl (x y : ℤ) (c : Cell) : ℤ := (c.2 - y) - (c.1 - x) + 1

lemma lvl_adj_cases {x y : ℤ} {c c' : Cell} (h : Adjacent c c') :
    lvl x y c' = lvl x y c + 1 ∨ lvl x y c' = lvl x y c - 1 := by
  rcases adjacent_cases h with h1 | h1 | h1 | h1 <;> rw [h1] <;> unfold lvl <;> omega

/-- The even staircase point `pe k = (x + k, y + k)`. -/
def pe (x y : ℤ) (k : ℕ) : Cell := (x + k, y + k)

/-- The odd staircase point `po k = (x + k + 1, y + k)`. -/
def po (x y : ℤ) (k : ℕ) : Cell := (x + k + 1, y + k)

/-- The cell above `pe k`: `u k = (x + k, y + k + 1)`. -/
def uu (x y : ℤ) (k : ℕ) : Cell := (x + k, y + k + 1)

/-- The cell right of `po k`: `r k = (x + k + 2, y + k)`. -/
def rr (x y : ℤ) (k : ℕ) : Cell := (x + k + 2, y + k)

lemma lvl_pe (x y : ℤ) (k : ℕ) : lvl x y (pe x y k) = 1 := by unfold lvl pe; ring
lemma lvl_po (x y : ℤ) (k : ℕ) : lvl x y (po x y k) = 0 := by unfold lvl po; ring
lemma lvl_uu (x y : ℤ) (k : ℕ) : lvl x y (uu x y k) = 2 := by unfold lvl uu; ring
lemma lvl_rr (x y : ℤ) (k : ℕ) : lvl x y (rr x y k) = -1 := by unfold lvl rr; ring

/-- A cell of level 1 whose second coordinate is `≥ y` is an even staircase point. -/
lemma eq_pe_of_lvl_one {x y : ℤ} {c : Cell} (hy : y ≤ c.2) (h1 : lvl x y c = 1) :
    ∃ k : ℕ, c = pe x y k := by
  have h2 : c.1 - x = c.2 - y := by unfold lvl at h1; omega
  have h3 : 0 ≤ c.1 - x := by omega
  refine ⟨(c.1 - x).toNat, ?_⟩
  unfold pe
  ext <;> simp [Int.toNat_of_nonneg h3] <;> omega

/-- A cell of level 0 whose second coordinate is `≥ y` is an odd staircase point. -/
lemma eq_po_of_lvl_zero {x y : ℤ} {c : Cell} (hy : y ≤ c.2) (h0 : lvl x y c = 0) :
    ∃ k : ℕ, c = po x y k := by
  have h2 : c.1 - x - 1 = c.2 - y := by unfold lvl at h0; omega
  have h3 : 0 ≤ c.1 - x - 1 := by omega
  refine ⟨(c.1 - x - 1).toNat, ?_⟩
  unfold po
  ext <;> simp [Int.toNat_of_nonneg h3] <;> omega

-- ============================================================
-- Corner arguments: the first staircase cells are in `S`
-- ============================================================

lemma po_zero_eq (x y : ℤ) : po x y 0 = (x + 1, y) := by
  unfold po; ext <;> simp <;> ring
lemma rr_zero_eq (x y : ℤ) : rr x y 0 = (x + 2, y) := by
  unfold rr; ext <;> simp <;> ring
lemma pe_one_eq (x y : ℤ) : pe x y 1 = (x + 1, y + 1) := by
  unfold pe; ext <;> simp <;> ring
lemma po_one_eq (x y : ℤ) : po x y 1 = (x + 2, y + 1) := by
  unfold po; ext <;> simp <;> ring

/-- At the lower-left corner, the only horizontal cycle edge in a low row is
`{po 0, rr 0}`, so the south-ray count at `pe 1` is exactly one. -/
lemma nscount_pe_one {S : Finset Cell} {f g : Cell → Cell} {m : ℕ}
    (hf : IsTiling S f) (hg : IsTiling S g) {x y : ℤ}
    (hmin : ∀ c ∈ S, y ≤ c.2)
    (hsd : (x, y) ∈ sd S f g)
    (hinj : ∀ i < 2 * m, ∀ j < 2 * m, walk (x, y) f g i = walk (x, y) f g j → i = j)
    (hm : 2 ≤ m) (hret : walk (x, y) f g (2 * m) = (x, y))
    (hw1 : walk (x, y) f g 1 = po x y 0) (hw2 : walk (x, y) f g 2 = rr x y 0) :
    Nscount (x, y) f g m (pe x y 1) = 1 := by
  have hw2' : walk (x, y) f g (1 + 1) = rr x y 0 := hw2
  have hp1 : pe x y 1 = (x + 1, y + 1) := pe_one_eq x y
  have h1mem : (1 : ℕ) ∈ (Finset.range (2 * m)).filter
      (fun i ↦ (walk (x, y) f g i).2 = (walk (x, y) f g (i + 1)).2 ∧
        (walk (x, y) f g i).2 < (pe x y 1).2 ∧
        ((walk (x, y) f g i).1 = (pe x y 1).1 ∧ (walk (x, y) f g (i + 1)).1 = (pe x y 1).1 + 1 ∨
         (walk (x, y) f g i).1 = (pe x y 1).1 + 1 ∧ (walk (x, y) f g (i + 1)).1 = (pe x y 1).1)) := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_range.mpr (by omega), ?_, ?_, ?_⟩
    · rw [hw1, hw2', po_zero_eq, rr_zero_eq]
    · rw [hw1, po_zero_eq, hp1]
      show y < y + 1
      omega
    · rw [hw1, hw2', po_zero_eq, rr_zero_eq, hp1]
      exact Or.inl ⟨rfl, by ring⟩
  have huniq : (Finset.range (2 * m)).filter
      (fun i ↦ (walk (x, y) f g i).2 = (walk (x, y) f g (i + 1)).2 ∧
        (walk (x, y) f g i).2 < (pe x y 1).2 ∧
        ((walk (x, y) f g i).1 = (pe x y 1).1 ∧ (walk (x, y) f g (i + 1)).1 = (pe x y 1).1 + 1 ∨
         (walk (x, y) f g i).1 = (pe x y 1).1 + 1 ∧ (walk (x, y) f g (i + 1)).1 = (pe x y 1).1)) = {1} := by
    ext i
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro hi
      obtain ⟨hi1, hi2, hi3, hi4⟩ := hi
      have hwiS : walk (x, y) f g i ∈ S := (mem_sd.mp (walk_mem hf hg hsd i)).1
      have hy_i : y ≤ (walk (x, y) f g i).2 := hmin _ hwiS
      have hrow : (walk (x, y) f g i).2 = y := by
        rw [hp1] at hi3
        simp at hi3
        omega
      have hcols : ((walk (x, y) f g i).1 = x + 1 ∧ (walk (x, y) f g (i + 1)).1 = x + 2) ∨
          ((walk (x, y) f g i).1 = x + 2 ∧ (walk (x, y) f g (i + 1)).1 = x + 1) := by
        rw [hp1] at hi4
        simp at hi4
        rcases hi4 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1, by omega⟩
        · exact Or.inr ⟨by omega, h2⟩
      have hedge := edge_of_horizontal hf hg hsd i hi2 (x := x + 1) (by
        rcases hcols with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1, by omega⟩
        · exact Or.inr ⟨by omega, h2⟩)
      rw [hrow, show x + 1 + 1 = x + 2 by ring] at hedge
      have hedge12 : ({walk (x, y) f g 1, walk (x, y) f g (1 + 1)} : Finset Cell) =
          {(x + 1, y), (x + 2, y)} := by
        rw [hw1, hw2', po_zero_eq, rr_zero_eq]
      exact cycEdges_inj hf hg hsd hinj hm hret (Finset.mem_range.mp hi1)
        (show 1 < 2 * m by omega) (by rw [hedge, hedge12])
    · intro hi
      rw [hi]
      exact Finset.mem_filter.mp h1mem
  unfold Nscount
  rw [huniq, Finset.card_singleton]

/-- Corner fact: `pe 1` is inside the cycle or on it (hence in `S`). -/
lemma pe_one_mem_inside_or_cyc {S : Finset Cell} {f g : Cell → Cell} {m : ℕ}
    (hf : IsTiling S f) (hg : IsTiling S g) {x y : ℤ}
    (hmin : ∀ c ∈ S, y ≤ c.2)
    (hsd : (x, y) ∈ sd S f g)
    (hinj : ∀ i < 2 * m, ∀ j < 2 * m, walk (x, y) f g i = walk (x, y) f g j → i = j)
    (hm : 2 ≤ m) (hret : walk (x, y) f g (2 * m) = (x, y))
    (hw1 : walk (x, y) f g 1 = po x y 0) (hw2 : walk (x, y) f g 2 = rr x y 0) :
    inside (x, y) f g m (pe x y 1) ∨ pe x y 1 ∈ cycSet (x, y) f g m := by
  have hN := nscount_pe_one hf hg hmin hsd hinj hm hret hw1 hw2
  have hR := box_south_rel hf hg hsd hinj hm hret (pe x y 1)
  rw [hN] at hR
  by_cases hed : ({((pe x y 1).1, (pe x y 1).2), ((pe x y 1).1 + 1, (pe x y 1).2)} : Finset Cell) ∈
      cycEdges (x, y) f g m
  · right
    exact (edge_cells_mem_cycSet (a := ((pe x y 1).1, (pe x y 1).2))
      (b := ((pe x y 1).1 + 1, (pe x y 1).2)) hret hed rfl).1
  · left
    rw [if_neg hed, add_zero] at hR
    obtain ⟨a, ha⟩ := hR
    unfold inside
    refine ⟨a - 1, by omega⟩

-- ============================================================
-- Propagation: staircase cells stay in `S`
-- ============================================================

/-- The partner of an inside, off-cycle cell is inside and off-cycle. -/
lemma inside_off_cycle_f_partner {S : Finset Cell} {f g : Cell → Cell} {m : ℕ}
    (hf : IsTiling S f) (hg : IsTiling S g) {s : Cell}
    (hsd : s ∈ sd S f g)
    (hinj : ∀ i < 2 * m, ∀ j < 2 * m, walk s f g i = walk s f g j → i = j)
    (hm : 2 ≤ m) (hret : walk s f g (2 * m) = s) {c : Cell}
    (hcS : c ∈ S) (hci : inside s f g m c) (hcγ : c ∉ cycSet s f g m) :
    inside s f g m (f c) ∧ f c ∉ cycSet s f g m := by
  have hfcγ : f c ∉ cycSet s f g m := by
    intro hfc
    rw [mem_cycSet] at hfc
    obtain ⟨t, htr, hte⟩ := hfc
    have hff : f (walk s f g t) = c := by
      have h1 : f (f c) = c := (hf c hcS).2.1
      rw [← hte] at h1
      exact h1
    have ht2m : t < 2 * m := Finset.mem_range.mp htr
    rcases Nat.even_or_odd t with hev | hodd
    · by_cases ht0 : t = 0
      · subst ht0
        have h1 : f (walk s f g (2 * m - 1)) = s := by
          have hs1 : walk s f g (2 * m - 1 + 1) =
              (if Even (2 * m - 1) then g else f) (walk s f g (2 * m - 1)) :=
            walk_succ s (2 * m - 1)
          rw [if_neg (Nat.not_even_iff_odd.mpr ⟨m - 1, by omega⟩)] at hs1
          rw [show 2 * m - 1 + 1 = 2 * m by omega, hret] at hs1
          exact hs1.symm
        have h2 := (hf _ (mem_sd.mp (walk_mem hf hg hsd (2 * m - 1))).1).2.1
        rw [h1] at h2
        have hc_eq : c = walk s f g (2 * m - 1) := by
          rw [walk_zero] at hff
          rw [← hff, h2]
        have hmem : walk s f g (2 * m - 1) ∈ cycSet s f g m :=
          mem_cycSet.mpr ⟨2 * m - 1, Finset.mem_range.mpr (by omega), rfl⟩
        rw [← hc_eq] at hmem
        exact hcγ hmem
      · have h1 : walk s f g t = f (walk s f g (t - 1)) := by
          have hs1 : walk s f g (t - 1 + 1) =
              (if Even (t - 1) then g else f) (walk s f g (t - 1)) :=
            walk_succ s (t - 1)
          rw [if_neg (Nat.not_even_iff_odd.mpr (by
            rcases hev with ⟨a, ha⟩
            exact ⟨a - 1, by omega⟩))] at hs1
          rw [show t - 1 + 1 = t by omega] at hs1
          exact hs1
        have h2 : f (walk s f g t) = walk s f g (t - 1) := by
          have h4 := (hf _ (mem_sd.mp (walk_mem hf hg hsd (t - 1))).1).2.1
          rw [← h4, h1]
        have hc_eq : c = walk s f g (t - 1) := by
          rw [← hff, h2]
        have hmem : walk s f g (t - 1) ∈ cycSet s f g m :=
          mem_cycSet.mpr ⟨t - 1, Finset.mem_range.mpr (by omega), rfl⟩
        rw [← hc_eq] at hmem
        exact hcγ hmem
    · have h1 : walk s f g (t + 1) = f (walk s f g t) := by
        have hs1 : walk s f g (t + 1) = (if Even t then g else f) (walk s f g t) := walk_succ s t
        rwa [if_neg (Nat.not_even_iff_odd.mpr hodd)] at hs1
      by_cases hlt : t + 1 < 2 * m
      · have hc_eq : c = walk s f g (t + 1) := by
          rw [← hff, ← h1]
        have hmem : walk s f g (t + 1) ∈ cycSet s f g m :=
          mem_cycSet.mpr ⟨t + 1, Finset.mem_range.mpr hlt, rfl⟩
        rw [← hc_eq] at hmem
        exact hcγ hmem
      · have hlt2 : t + 1 = 2 * m := by omega
        have hc_eq : c = walk s f g 0 := by
          rw [← hff, ← h1, hlt2, hret, walk_zero]
        have hmem : walk s f g 0 ∈ cycSet s f g m :=
          mem_cycSet.mpr ⟨0, Finset.mem_range.mpr (by omega), rfl⟩
        rw [← hc_eq] at hmem
        exact hcγ hmem
  have hadj : Adjacent c (f c) := (hf c hcS).2.2.2
  have hiff := inside_adj_of_not_mem hf hg hsd hinj hm hret hadj hcγ hfcγ
  exact ⟨hiff.mp hci, hfcγ⟩

/-- East propagation along the staircase: from `pe j` (inside, off-cycle) the
cell `po j` is inside or on the cycle. -/
lemma propagate_po {S : Finset Cell} {f g : Cell → Cell} {m : ℕ}
    (hf : IsTiling S f) (hg : IsTiling S g) {x y : ℤ}
    (hsd : (x, y) ∈ sd S f g)
    (hinj : ∀ i < 2 * m, ∀ j < 2 * m, walk (x, y) f g i = walk (x, y) f g j → i = j)
    (hm : 2 ≤ m) (hret : walk (x, y) f g (2 * m) = (x, y)) (j : ℕ)
    (hpe : inside (x, y) f g m (pe x y j)) (hpeγ : pe x y j ∉ cycSet (x, y) f g m) :
    inside (x, y) f g m (po x y j) ∨ po x y j ∈ cycSet (x, y) f g m := by
  have hpo : po x y j = ((pe x y j).1 + 1, (pe x y j).2) := by
    unfold po pe; ext <;> simp <;> ring
  have h1 := Ncount_east hf hg hsd hinj hm hret (pe x y j)
  -- the indicator edge is `{po j, po j + (0,1)}`
  by_cases hed : ({((pe x y j).1 + 1, (pe x y j).2), ((pe x y j).1 + 1, (pe x y j).2 + 1)} : Finset Cell) ∈
      cycEdges (x, y) f g m
  · right
    rw [hpo]
    exact (edge_cells_mem_cycSet (a := ((pe x y j).1 + 1, (pe x y j).2))
      (b := ((pe x y j).1 + 1, (pe x y j).2 + 1)) hret hed rfl).1
  · left
    rw [if_neg hed, add_zero] at h1
    rw [hpo]
    unfold inside
    rw [← h1]
    exact hpe

-- ============================================================
-- Forcing wrappers and the remaining propagation steps
-- ============================================================

/-- `V`-forcing: `f (pe k) = uu k`, repackaging `tasteful_staircase_V`. -/
lemma f_pe_eq_uu {S : Finset Cell} {f : Cell → Cell} (hf : IsTiling S f)
    (ht : Tasteful S f) {x y : ℤ} (hodd : Odd (x + y)) (hs : (x, y) ∈ S)
    (hsv : f (x, y) = (x, y + 1)) (hmin : ∀ c ∈ S, y ≤ c.2) (k : ℕ)
    (hE : ∀ j ≤ k, pe x y j ∈ S) (hO : ∀ j < k, po x y j ∈ S) :
    f (pe x y k) = uu x y k :=
  tasteful_staircase_V hf ht hodd hs hsv hmin k hE hO

/-- `H`-forcing: `f (po k) = rr k`, repackaging `tasteful_staircase_H`. -/
lemma f_po_eq_rr {S : Finset Cell} {f : Cell → Cell} (hf : IsTiling S f)
    (ht : Tasteful S f) {x y : ℤ} (hodd : Odd (x + y)) (hs : (x, y) ∈ S)
    (hsv : f (x, y) = (x, y + 1)) (hmin : ∀ c ∈ S, y ≤ c.2) (k : ℕ)
    (hE : ∀ j ≤ k, pe x y j ∈ S) (hO : ∀ j ≤ k, po x y j ∈ S) :
    f (po x y k) = rr x y k :=
  tasteful_staircase_H hf ht hodd hs hsv hmin k hE hO

/-- East propagation from `uu j`: `pe (j+1)` is inside or on the cycle. -/
lemma propagate_pe_succ {S : Finset Cell} {f g : Cell → Cell} {m : ℕ}
    (hf : IsTiling S f) (hg : IsTiling S g) {x y : ℤ}
    (hsd : (x, y) ∈ sd S f g)
    (hinj : ∀ i < 2 * m, ∀ j < 2 * m, walk (x, y) f g i = walk (x, y) f g j → i = j)
    (hm : 2 ≤ m) (hret : walk (x, y) f g (2 * m) = (x, y)) (j : ℕ)
    (huu : inside (x, y) f g m (uu x y j)) (huuγ : uu x y j ∉ cycSet (x, y) f g m) :
    inside (x, y) f g m (pe x y (j + 1)) ∨ pe x y (j + 1) ∈ cycSet (x, y) f g m := by
  have hpe : pe x y (j + 1) = ((uu x y j).1 + 1, (uu x y j).2) := by
    unfold pe uu; ext <;> simp <;> ring
  have h1 := Ncount_east hf hg hsd hinj hm hret (uu x y j)
  by_cases hed : ({((uu x y j).1 + 1, (uu x y j).2), ((uu x y j).1 + 1, (uu x y j).2 + 1)} : Finset Cell) ∈
      cycEdges (x, y) f g m
  · right
    rw [hpe]
    exact (edge_cells_mem_cycSet (a := ((uu x y j).1 + 1, (uu x y j).2))
      (b := ((uu x y j).1 + 1, (uu x y j).2 + 1)) hret hed rfl).1
  · left
    rw [if_neg hed, add_zero] at h1
    rw [hpe]
    unfold inside
    rw [← h1]
    exact huu

-- ============================================================
-- Closed walks on the cell lattice have even length
-- ============================================================

/-- Every step between adjacent cells changes `c.1 + c.2` by exactly one. -/
lemma pm_one_of_adjacent {c c' : Cell} (h : Adjacent c c') :
    c'.1 + c'.2 = c.1 + c.2 + 1 ∨ c'.1 + c'.2 = c.1 + c.2 - 1 := by
  rcases adjacent_cases h with h1 | h1 | h1 | h1 <;> rw [h1] <;> simp <;> omega

/-- A closed walk on the (bipartite) cell lattice has even length. -/
lemma even_length_of_closed_walk {v : ℕ → Cell} {L : ℕ}
    (h : ∀ i < L, Adjacent (v i) (v (i + 1))) (hL : v L = v 0) : Even L := by
  have hpar : ∀ i ≤ L, Even ((v i).1 + (v i).2 + i - ((v 0).1 + (v 0).2)) := by
    intro i hi
    induction i with
    | zero => exact ⟨0, by ring⟩
    | succ i ih =>
      have hii : i ≤ i + 1 := Nat.le_succ i
      have hii2 : i ≤ L := by omega
      obtain ⟨a, ha⟩ := ih hii2
      have hstep : (v (i + 1)).1 + (v (i + 1)).2 = (v i).1 + (v i).2 + 1 ∨
          (v (i + 1)).1 + (v (i + 1)).2 = (v i).1 + (v i).2 - 1 :=
        pm_one_of_adjacent (h i (by omega))
      rcases hstep with h1 | h1
      · exact ⟨a + 1, by omega⟩
      · exact ⟨a, by omega⟩
  obtain ⟨a, ha⟩ := hpar L (le_refl L)
  rw [hL] at ha
  exact ⟨a.toNat, by omega⟩

-- ============================================================
-- Lemma A, odd case: infrastructure
-- ============================================================

/-- The cell `pe 0` is the base point itself. -/
lemma pe_zero_eq (x y : ℤ) : pe x y 0 = (x, y) := by
  unfold pe; ext <;> simp <;> ring

/-- First-hit return: the first time after index `a` that the walk reaches a
nonnegative level.  Such a time exists because `w (2m-1) = uu 0` has level 2. -/
lemma first_return_exists {f g : Cell → Cell} {m : ℕ} {x y : ℤ}
    (hwlast : walk (x, y) f g (2 * m - 1) = uu x y 0) (a : ℕ) (ha : a ≤ 2 * m - 1) :
    ∃ t, a ≤ t ∧ t ≤ 2 * m - 1 ∧ lvl x y (walk (x, y) f g t) ≥ 0 :=
  ⟨2 * m - 1, ha, le_refl _, by rw [hwlast, lvl_uu]; omega⟩

-- ============================================================
-- The staircase arc and the return-time parity lemma
-- ============================================================

lemma adjacent_pe_po (x y : ℤ) (j : ℕ) : Adjacent (pe x y j) (po x y j) :=
  adjacent_mk_right (x + (j : ℤ)) (y + (j : ℤ))

lemma adjacent_po_pe (x y : ℤ) (j : ℕ) : Adjacent (po x y j) (pe x y j) :=
  adjacent_comm (adjacent_pe_po x y j)

lemma adjacent_pe_po_pred (x y : ℤ) {j : ℕ} (hj : 1 ≤ j) :
    Adjacent (pe x y j) (po x y (j - 1)) := by
  have h2 : po x y (j - 1) = ((pe x y j).1, (pe x y j).2 - 1) := by
    unfold po pe
    ext <;> simp <;> (rw [Int.ofNat_sub hj]; ring)
  rw [h2]
  unfold Adjacent
  simp

/-- The staircase arc function descending from `po k`:
`st 0 = po k`, `st 1 = pe k`, `st 2 = po (k-1)`, `st 3 = pe (k-1)`, ... -/
noncomputable def st (x y : ℤ) (k : ℕ) : ℕ → Cell :=
  fun n ↦ if Even n then po x y (k - n / 2) else pe x y (k - n / 2)

lemma st_zero (x y : ℤ) (k : ℕ) : st x y k 0 = po x y k := by
  unfold st
  rw [if_pos ⟨0, by ring⟩]
  simp

lemma st_adj_even {x y : ℤ} {k a : ℕ} : Adjacent (st x y k (2 * a)) (st x y k (2 * a + 1)) := by
  unfold st
  rw [if_pos (even_two_mul a), if_neg (Nat.not_even_iff_odd.mpr ⟨a, by ring⟩)]
  have h1 : (2 * a) / 2 = a := by omega
  have h2 : (2 * a + 1) / 2 = a := by omega
  rw [h1, h2]
  exact adjacent_po_pe x y (k - a)

lemma st_adj_odd {x y : ℤ} {k a : ℕ} (ha : 1 ≤ k - a) :
    Adjacent (st x y k (2 * a + 1)) (st x y k (2 * a + 2)) := by
  unfold st
  rw [if_neg (Nat.not_even_iff_odd.mpr ⟨a, by ring⟩),
    if_pos (show Even (2 * a + 2) from ⟨a + 1, by ring⟩)]
  have h1 : (2 * a + 1) / 2 = a := by omega
  have h2 : (2 * a + 2) / 2 = a + 1 := by omega
  rw [h1, h2, show k - (a + 1) = k - a - 1 by omega]
  exact adjacent_pe_po_pred x y ha

lemma st_adj {x y : ℤ} {k : ℕ} (n : ℕ) (hn : 1 ≤ n) (hn2 : n / 2 ≤ k) :
    Adjacent (st x y k (n - 1)) (st x y k n) := by
  rcases Nat.even_or_odd n with hev | hodd
  · obtain ⟨a, ha⟩ := hev
    have ha1 : 1 ≤ a := by omega
    have h1 : n - 1 = 2 * (a - 1) + 1 := by omega
    have h2 : n = 2 * (a - 1) + 2 := by omega
    rw [h1, h2]
    apply st_adj_odd
    omega
  · obtain ⟨a, ha⟩ := hodd
    have h1 : n - 1 = 2 * a := by omega
    have h2 : n = 2 * a + 1 := by omega
    rw [h1, h2]
    exact st_adj_even

/-- The closed curve (walk arc from index `a`, then the staircase arc from
`po k` back down to `po i`). -/
noncomputable def arc (w : ℕ → Cell) (a t : ℕ) (x y : ℤ) (k : ℕ) (j : ℕ) : Cell :=
  if j ≤ t - a then w (a + j) else st x y k (j - (t - a))

/-- The closed curve formed by a walk arc and the staircase arc has even length,
so the return time has the same parity as the previous visit time. -/
lemma return_parity {S : Finset Cell} {f g : Cell → Cell} {m : ℕ}
    (hf : IsTiling S f) (hg : IsTiling S g) {x y : ℤ}
    (hsd : (x, y) ∈ sd S f g)
    (hinj : ∀ i < 2 * m, ∀ j < 2 * m, walk (x, y) f g i = walk (x, y) f g j → i = j)
    {a t : ℕ} {i k : ℕ} (ha : walk (x, y) f g a = po x y i)
    (ht : walk (x, y) f g t = po x y k)
    (hlt : a < t) (hik : i < k) :
    t % 2 = a % 2 := by
  classical
  have hadj : ∀ j < (t - a) + 2 * (k - i),
      Adjacent (arc (walk (x, y) f g) a t x y k j) (arc (walk (x, y) f g) a t x y k (j + 1)) := by
    intro j hj
    by_cases hj1 : j + 1 ≤ t - a
    · have hj2 : j ≤ t - a := by omega
      rw [arc, if_pos hj2, arc, if_pos hj1]
      have h1 : a + (j + 1) = a + j + 1 := by ring
      rw [h1]
      exact walk_succ_adj hf hg hsd (a + j)
    · by_cases hj2 : j ≤ t - a
      · -- the junction: `arc j = walk t = po k`, `arc (j+1) = st 1 = pe k`
        have hj3 : j = t - a := by omega
        rw [arc, if_pos hj2]
        have hwalk : walk (x, y) f g (a + j) = po x y k := by
          rw [hj3, show a + (t - a) = t by omega, ht]
        rw [hwalk]
        have hjs : arc (walk (x, y) f g) a t x y k (j + 1) = st x y k 1 := by
          rw [arc, if_neg (by omega : ¬ j + 1 ≤ t - a)]
          rw [hj3, show t - a + 1 - (t - a) = 1 by omega]
        rw [hjs]
        have hst1 : st x y k 1 = pe x y k := by
          unfold st
          rw [if_neg (Nat.not_even_iff_odd.mpr ⟨0, by ring⟩)]
          simp
        rw [hst1]
        exact adjacent_po_pe x y k
      · -- inside the staircase arc
        rw [arc, if_neg hj2, arc, if_neg (by omega : ¬ j + 1 ≤ t - a)]
        have h1 : j + 1 - (t - a) = j - (t - a) + 1 := by omega
        rw [h1]
        have hn : 1 ≤ j - (t - a) := by omega
        have hn2 : (j - (t - a) + 1) / 2 ≤ k := by
          have h2 : j - (t - a) ≤ 2 * (k - i) - 1 := by omega
          have h3 : (j - (t - a) + 1) / 2 ≤ (2 * (k - i)) / 2 :=
            Nat.div_le_div_right (by omega)
          have h4 : (2 * (k - i)) / 2 = k - i := by omega
          rw [h4] at h3
          omega
        have h5 : j - (t - a) + 1 - 1 = j - (t - a) := by omega
        rw [← h5]
        exact st_adj (j - (t - a) + 1) (by omega) hn2
  have hL : arc (walk (x, y) f g) a t x y k ((t - a) + 2 * (k - i)) =
      arc (walk (x, y) f g) a t x y k 0 := by
    rw [arc, if_neg (by omega : ¬ (t - a) + 2 * (k - i) ≤ t - a)]
    have h2 : (t - a) + 2 * (k - i) - (t - a) = 2 * (k - i) := by omega
    rw [h2]
    have h3 : st x y k (2 * (k - i)) = po x y (k - (k - i)) := by
      unfold st
      rw [if_pos (even_two_mul _), show 2 * (k - i) / 2 = k - i by omega]
    rw [h3, show k - (k - i) = i by omega, ← ha]
    rw [arc, if_pos (by omega : 0 ≤ t - a)]
    simp
  have hEven := even_length_of_closed_walk hadj hL
  obtain ⟨r, hr⟩ := hEven
  omega

-- ============================================================
-- The membership chain: all staircase cells `pe j` are strictly inside
-- ============================================================

/-- If no level-1 cell up to index `N` is on the cycle, then every `pe j'` with
`1 ≤ j' ≤ j ≤ N` is inside the cycle and every `po j'` is inside or on it. -/
lemma pe_chain {S : Finset Cell} (hcc : ComplConnected S)
    {f g : Cell → Cell} (hf : IsTiling S f) (htf : Tasteful S f)
    (hg : IsTiling S g) (htg : Tasteful S g)
    {x y : ℤ} (hsS : (x, y) ∈ S) (hodd : Odd (x + y))
    (hmin : ∀ c ∈ S, y ≤ c.2) (hfu : f (x, y) = (x, y + 1)) (hgr : g (x, y) = (x + 1, y))
    {m : ℕ} (hm : 2 ≤ m) (hsd : (x, y) ∈ sd S f g)
    (hinj : ∀ i < 2 * m, ∀ j < 2 * m, walk (x, y) f g i = walk (x, y) f g j → i = j)
    (hret : walk (x, y) f g (2 * m) = (x, y))
    (hw1 : walk (x, y) f g 1 = po x y 0) (hw2 : walk (x, y) f g 2 = rr x y 0)
    {N : ℕ} (hnolv : ∀ j' ≤ N, 1 ≤ j' → pe x y j' ∉ cycSet (x, y) f g m)
    {j : ℕ} (hj : 1 ≤ j) (hjN : j ≤ N) :
    (∀ j' ≤ j, 1 ≤ j' → inside (x, y) f g m (pe x y j')) ∧
    (∀ j' ≤ j, 1 ≤ j' →
      inside (x, y) f g m (po x y j') ∨ po x y j' ∈ cycSet (x, y) f g m) := by
  induction j with
  | zero => omega
  | succ j ihj =>
    by_cases hj0 : j = 0
    · subst hj0
      have h1 := pe_one_mem_inside_or_cyc hf hg hmin hsd hinj hm hret hw1 hw2
      have hpe1in : inside (x, y) f g m (pe x y 1) := by
        rcases h1 with h1 | h1
        · exact h1
        · exact absurd h1 (hnolv 1 hjN (by omega))
      have hpo1 := propagate_po hf hg hsd hinj hm hret 1 hpe1in (hnolv 1 hjN (by omega))
      refine ⟨fun j' hj' h => by
          have h2 : j' = 1 := by omega
          subst h2
          exact hpe1in,
        fun j' hj' h => by
          have h2 : j' = 1 := by omega
          subst h2
          exact hpo1⟩
    · have h1 : 1 ≤ j := by omega
      obtain ⟨hpe, hpo⟩ := ihj h1 (by omega)
      have hV : f (pe x y j) = uu x y j := by
        apply f_pe_eq_uu hf htf hodd hsS hfu hmin j
        · intro j' hj'
          by_cases hj'' : j' = 0
          · subst hj''
            rw [pe_zero_eq]
            exact hsS
          · have h2 : 1 ≤ j' := by omega
            exact inside_mem_S hf hg hcc hsd hinj hm hret (hpe j' (by omega) h2)
        · intro j' hj'
          by_cases hj0 : j' = 0
          · subst hj0
            have h2 := (hg (x, y) hsS).1
            rw [hgr, ← po_zero_eq] at h2
            exact h2
          · have h3 : 1 ≤ j' := by omega
            have h2 := hpo j' (by omega) h3
            rcases h2 with h2 | h2
            · exact inside_mem_S hf hg hcc hsd hinj hm hret h2
            · exact (mem_sd.mp (cycSet_subset_sd hf hg hsd h2)).1
      have hpein : inside (x, y) f g m (pe x y j) := hpe j (by omega) h1
      have hpeγ : pe x y j ∉ cycSet (x, y) f g m := hnolv j (by omega) h1
      have hpeS : pe x y j ∈ S := inside_mem_S hf hg hcc hsd hinj hm hret hpein
      have huu := inside_off_cycle_f_partner hf hg hsd hinj hm hret hpeS hpein hpeγ
      rw [hV] at huu
      have hpe1in : inside (x, y) f g m (pe x y (j + 1)) := by
        have h3 := propagate_pe_succ hf hg hsd hinj hm hret j huu.1 huu.2
        rcases h3 with h3 | h3
        · exact h3
        · exact absurd h3 (hnolv (j + 1) (by omega) (by omega))
      have hpo1 := propagate_po hf hg hsd hinj hm hret (j + 1) hpe1in
        (hnolv (j + 1) (by omega) (by omega))
      refine ⟨fun j' hj' h => ?_, fun j' hj' h => ?_⟩
      · by_cases hj'' : j' ≤ j
        · exact hpe j' hj'' h
        · have h2 : j' = j + 1 := by omega
          subst h2
          exact hpe1in
      · by_cases hj'' : j' ≤ j
        · exact hpo j' hj'' h
        · have h2 : j' = j + 1 := by omega
          subst h2
          exact hpo1

/-- Consequently `pe j'` is in `S` (inside cells are). -/
lemma pe_chain_mem_S {S : Finset Cell} (hcc : ComplConnected S)
    {f g : Cell → Cell} (hf : IsTiling S f) (htf : Tasteful S f)
    (hg : IsTiling S g) (htg : Tasteful S g)
    {x y : ℤ} (hsS : (x, y) ∈ S) (hodd : Odd (x + y))
    (hmin : ∀ c ∈ S, y ≤ c.2) (hfu : f (x, y) = (x, y + 1)) (hgr : g (x, y) = (x + 1, y))
    {m : ℕ} (hm : 2 ≤ m) (hsd : (x, y) ∈ sd S f g)
    (hinj : ∀ i < 2 * m, ∀ j < 2 * m, walk (x, y) f g i = walk (x, y) f g j → i = j)
    (hret : walk (x, y) f g (2 * m) = (x, y))
    (hw1 : walk (x, y) f g 1 = po x y 0) (hw2 : walk (x, y) f g 2 = rr x y 0)
    {N : ℕ} (hnolv : ∀ j' ≤ N, 1 ≤ j' → pe x y j' ∉ cycSet (x, y) f g m)
    {j : ℕ} (hj : 1 ≤ j) (hjN : j ≤ N) :
    (∀ j' ≤ j, 1 ≤ j' → pe x y j' ∈ S) ∧ (∀ j' ≤ j, 1 ≤ j' → po x y j' ∈ S) := by
  obtain ⟨h1, h2⟩ := pe_chain hcc hf htf hg htg hsS hodd hmin hfu hgr hm hsd hinj hret hw1 hw2 hnolv hj hjN
  refine ⟨fun j' hj' h => inside_mem_S hf hg hcc hsd hinj hm hret (h1 j' hj' h),
    fun j' hj' h => ?_⟩
  obtain h3 | h3 := h2 j' hj' h
  · exact inside_mem_S hf hg hcc hsd hinj hm hret h3
  · exact (mem_sd.mp (cycSet_subset_sd hf hg hsd h3)).1

-- ============================================================
-- The down-bounce at a first-hit return
-- ============================================================

/-- The two level-(-1) neighbors of `po k` are `rr k` (east) and `rr (k-1)` (south). -/
lemma po_lvl_neg_one_neighbors {x y : ℤ} {c : Cell} {k : ℕ} (hk : 1 ≤ k)
    (h : c = po x y k) {c' : Cell} (hadj : Adjacent c c') (hl : lvl x y c' = -1) :
    c' = rr x y k ∨ c' = rr x y (k - 1) := by
  subst h
  rcases adjacent_cases hadj with h1 | h1 | h1 | h1
  · left
    have h2 : c' = rr x y k := by
      rw [h1]
      unfold po rr
      ext <;> simp <;> omega
    exact h2
  · exfalso
    have h2 : c' = pe x y k := by
      rw [h1]
      unfold po pe
      ext <;> simp <;> omega
    rw [h2, lvl_pe] at hl
    omega
  · exfalso
    have h2 : c' = pe x y (k + 1) := by
      rw [h1]
      unfold po pe
      ext <;> simp <;> omega
    rw [h2, lvl_pe] at hl
    omega
  · right
    have h2 : c' = rr x y (k - 1) := by
      rw [h1]
      unfold po rr
      ext <;> simp <;> omega
    exact h2

/-- At a first-hit return `w_t = po k` with `t` odd and membership up to `k`,
the walk is forced: `w_{t+1} = rr k` (the `f`-edge after), `w_{t-1} = rr (k-1)`
(the `g`-edge before), and `w_{t-2} = po (k-1)`. -/
lemma bounce_at_return {S : Finset Cell} {f g : Cell → Cell} {m : ℕ} {x y : ℤ}
    (hf : IsTiling S f) (hg : IsTiling S g) (htf : Tasteful S f)
    (hsd : (x, y) ∈ sd S f g)
    (hinj : ∀ i < 2 * m, ∀ j < 2 * m, walk (x, y) f g i = walk (x, y) f g j → i = j)
    (hm : 2 ≤ m) (hret : walk (x, y) f g (2 * m) = (x, y))
    (hsS : (x, y) ∈ S) (hodd : Odd (x + y)) (hfu : f (x, y) = (x, y + 1))
    (hmin : ∀ c ∈ S, y ≤ c.2)
    {k : ℕ} {t : ℕ} (ht : walk (x, y) f g t = po x y k) (htodd : Odd t) (ht2 : 2 ≤ t)
    (hk : 1 ≤ k)
    (hprev : lvl x y (walk (x, y) f g (t - 1)) = -1)
    (hmem : (∀ j' ≤ k, po x y j' ∈ S)) (hmemV : (∀ j' ≤ k, pe x y j' ∈ S))
    (hmemV1 : (∀ j' < k, po x y j' ∈ S)) (hmemV2 : (∀ j' ≤ k - 1, pe x y j' ∈ S)) :
    walk (x, y) f g (t + 1) = rr x y k ∧
    walk (x, y) f g (t - 1) = rr x y (k - 1) ∧
    walk (x, y) f g (t - 2) = po x y (k - 1) := by
  -- `f (po k) = rr k` by H-forcing
  have hH : f (po x y k) = rr x y k := by
    apply f_po_eq_rr hf htf hodd hsS hfu hmin k
    · intro j' hj'
      exact hmemV j' hj'
    · intro j' hj'
      exact hmem j' (by omega)
  -- `f (po (k-1)) = rr (k-1)` by H-forcing
  have hH1 : f (po x y (k - 1)) = rr x y (k - 1) := by
    apply f_po_eq_rr hf htf hodd hsS hfu hmin (k - 1)
    · intro j' hj'
      exact hmemV2 j' hj'
    · intro j' hj'
      exact hmemV1 j' (by omega)
  -- `t` odd: step `t → t+1` uses `f`, so `w_{t+1} = rr k`
  have hstep : walk (x, y) f g (t + 1) = rr x y k := by
    have h1 : walk (x, y) f g (t + 1) = f (walk (x, y) f g t) :=
      walk_eq_f_of_odd htodd
    rw [ht, hH] at h1
    exact h1
  -- `t-1` even: step `t-1 → t` uses `g`, so `g (po k) = w_{t-1}`
  have hg1 : g (po x y k) = walk (x, y) f g (t - 1) := by
    have h2 : walk (x, y) f g (t - 1 + 1) = g (walk (x, y) f g (t - 1)) := by
      have h2' : walk (x, y) f g (t - 1 + 1) =
          (if Even (t - 1) then g else f) (walk (x, y) f g (t - 1)) :=
        walk_succ (x, y) (t - 1)
      have ht1even : Even (t - 1) := by
        rcases htodd with ⟨a, ha⟩
        use a
        omega
      rwa [if_pos ht1even] at h2'
    rw [show t - 1 + 1 = t by omega, ht] at h2
    have h3 : walk (x, y) f g (t - 1) ∈ S := (mem_sd.mp (walk_mem hf hg hsd (t - 1))).1
    have h4 := (hg _ h3).2.1
    rw [h2.symm] at h4
    exact h4
  -- `w_{t-1}` is a level-(-1) neighbor of `po k`: `rr k` or `rr (k-1)`
  have hnb := po_lvl_neg_one_neighbors hk (c := po x y k) rfl (by
    have h5 := walk_succ_adj hf hg hsd (t - 1)
    rw [show t - 1 + 1 = t by omega, ht] at h5
    exact adjacent_comm h5) hprev
  -- but `w_{t-1} ≠ rr k`, since `f (po k) = rr k ≠ g (po k)`
  have hgsd : walk (x, y) f g (t - 1) ≠ rr x y k := by
    intro hcon
    have h1 : po x y k ∈ sd S f g := by
      rw [← ht]
      exact walk_mem hf hg hsd t
    have h2 := (mem_sd.mp h1).2
    rw [hH] at h2
    rw [hcon] at hg1
    exact h2 hg1.symm
  have hw1 : walk (x, y) f g (t - 1) = rr x y (k - 1) := by
    rcases hnb with h3 | h3
    · exact absurd h3 hgsd
    · exact h3
  -- `w_{t-2} = f (rr (k-1)) = po (k-1)`
  have hw2 : walk (x, y) f g (t - 2) = po x y (k - 1) := by
    have h1 : walk (x, y) f g (t - 2 + 1) = f (walk (x, y) f g (t - 2)) := by
      have h1' : walk (x, y) f g (t - 2 + 1) =
          (if Even (t - 2) then g else f) (walk (x, y) f g (t - 2)) :=
        walk_succ (x, y) (t - 2)
      have ht2odd : Odd (t - 2) := by
        rcases htodd with ⟨a, ha⟩
        exact ⟨a - 1, by omega⟩
      rwa [if_neg (Nat.not_even_iff_odd.mpr ht2odd)] at h1'
    rw [show t - 2 + 1 = t - 1 by omega, hw1] at h1
    have h2 : walk (x, y) f g (t - 2) ∈ S := (mem_sd.mp (walk_mem hf hg hsd (t - 2))).1
    have h3 := (hf _ h2).2.1
    rw [h1.symm] at h3
    have h4 : f (rr x y (k - 1)) = po x y (k - 1) := by
      have h5 : po x y (k - 1) ∈ S := hmemV1 (k - 1) (by omega)
      have h6 := (hf _ h5).2.1
      rw [hH1] at h6
      exact h6
    have h7 : walk (x, y) f g (t - 2) = f (rr x y (k - 1)) := h3.symm
    rw [h4] at h7
    exact h7
  exact ⟨hstep, hw1, hw2⟩
-- ============================================================
-- The first-hit return lands on a staircase point
-- ============================================================

/-- The first time after index `a` that the walk reaches a nonnegative level
lands on an odd staircase point `po k`, with the previous cell at level -1. -/
lemma return_landing2 {S : Finset Cell} {f g : Cell → Cell} {m : ℕ} {x y : ℤ}
    (hf : IsTiling S f) (hg : IsTiling S g)
    (hmin : ∀ c ∈ S, y ≤ c.2)
    (hsd : (x, y) ∈ sd S f g)
    {a : ℕ} (ha : a ≤ 2 * m - 1)
    (hwlast : walk (x, y) f g (2 * m - 1) = uu x y 0)
    (hrr : lvl x y (walk (x, y) f g a) = -1)
    (ha2 : 2 ≤ a) :
    ∃ t k : ℕ, a ≤ t ∧ t ≤ 2 * m - 1 ∧
      lvl x y (walk (x, y) f g t) = 0 ∧ walk (x, y) f g t = po x y k ∧
      lvl x y (walk (x, y) f g (t - 1)) = -1 ∧
      (∀ t' < t, a ≤ t' → lvl x y (walk (x, y) f g t') < 0) := by
  classical
  have hex := first_return_exists hwlast a ha
  obtain ⟨ht1, ht2, ht3⟩ := Nat.find_spec hex
  have htmin : ∀ t' < Nat.find hex, a ≤ t' → lvl x y (walk (x, y) f g t') < 0 := by
    intro t' ht' ht'2
    by_contra hcon
    push_neg at hcon
    have hmin' : ¬ (a ≤ t' ∧ t' ≤ 2 * m - 1 ∧ lvl x y (walk (x, y) f g t') ≥ 0) :=
      Nat.find_min hex ht'
    by_cases h1 : t' ≤ 2 * m - 1
    · exact hmin' ⟨ht'2, h1, hcon⟩
    · omega
  have ht3' : lvl x y (walk (x, y) f g (Nat.find hex)) ≥ 0 := ht3
  have hprev : lvl x y (walk (x, y) f g (Nat.find hex - 1)) = -1 := by
    have hta : Nat.find hex ≠ a := by
      intro hta
      rw [← hta] at hrr
      omega
    have h1 : Nat.find hex - 1 = a ∨ a < Nat.find hex - 1 := by omega
    rcases h1 with h1 | h1
    · rw [h1, hrr]
    · have h2 := htmin (Nat.find hex - 1) (by omega) (by omega)
      have h3 : lvl x y (walk (x, y) f g (Nat.find hex - 1 + 1)) =
          lvl x y (walk (x, y) f g (Nat.find hex - 1)) + 1 ∨
        lvl x y (walk (x, y) f g (Nat.find hex - 1 + 1)) =
          lvl x y (walk (x, y) f g (Nat.find hex - 1)) - 1 :=
        lvl_adj_cases (walk_succ_adj hf hg hsd (Nat.find hex - 1))
      rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega] at h3
      omega
  have hwt : lvl x y (walk (x, y) f g (Nat.find hex)) = 0 := by
    have h3 : lvl x y (walk (x, y) f g (Nat.find hex - 1 + 1)) =
        lvl x y (walk (x, y) f g (Nat.find hex - 1)) + 1 ∨
      lvl x y (walk (x, y) f g (Nat.find hex - 1 + 1)) =
        lvl x y (walk (x, y) f g (Nat.find hex - 1)) - 1 :=
      lvl_adj_cases (walk_succ_adj hf hg hsd (Nat.find hex - 1))
    rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega] at h3
    omega
  have hwtS : walk (x, y) f g (Nat.find hex) ∈ S := (mem_sd.mp (walk_mem hf hg hsd _)).1
  obtain ⟨k, hk⟩ := eq_po_of_lvl_zero (hmin _ hwtS) hwt
  exact ⟨Nat.find hex, k, ht1, ht2, hwt, hk, hprev, htmin⟩

-- ============================================================
-- The staircase induction step (injectivity-based)
-- ============================================================

/-- The induction step: from `w_{2i+1} = po i` and `w_{2i+2} = rr i` (with
`f (po i) = rr i`), the walk either continues up the staircase
(`w_{2i+3} = po (i+1)`, `w_{2i+4} = rr (i+1)` with `f (po (i+1)) = rr (i+1)`),
or it leaves the staircase levels (`lvl (w_{2i+3}) ≤ -2`, the "break" case).

The continuation needs no membership propagation: `f (po (i+1)) = pe (i+1)`
contradicts `hnolv`, `f (po (i+1)) = pe (i+2)` is a forbidden vertical pair
(with `V`-forcing at `i+1` from `pe_chain`), and `f (po (i+1)) = rr i`
contradicts injectivity of `f`. -/
lemma staircase_step {S : Finset Cell} (hcc : ComplConnected S)
    {f g : Cell → Cell} (hf : IsTiling S f) (htf : Tasteful S f)
    (hg : IsTiling S g) (htg : Tasteful S g)
    {x y : ℤ} (hsS : (x, y) ∈ S) (hodd : Odd (x + y))
    (hmin : ∀ c ∈ S, y ≤ c.2) (hfu : f (x, y) = (x, y + 1)) (hgr : g (x, y) = (x + 1, y))
    {m : ℕ} (hm : 2 ≤ m) (hsd : (x, y) ∈ sd S f g)
    (hinj : ∀ i < 2 * m, ∀ j < 2 * m, walk (x, y) f g i = walk (x, y) f g j → i = j)
    (hret : walk (x, y) f g (2 * m) = (x, y))
    (hw1 : walk (x, y) f g 1 = po x y 0) (hw2 : walk (x, y) f g 2 = rr x y 0)
    {N : ℕ} (hnolv : ∀ j' ≤ N, 1 ≤ j' → pe x y j' ∉ cycSet (x, y) f g m)
    {i : ℕ} (hiN : i + 1 ≤ N) (hi : 2 * i + 4 ≤ 2 * m - 1)
    (hprev : walk (x, y) f g (2 * i + 1) = po x y i)
    (hprev2 : walk (x, y) f g (2 * i + 2) = rr x y i)
    (hforce : f (po x y i) = rr x y i) :
    (walk (x, y) f g (2 * i + 3) = po x y (i + 1) ∧
      walk (x, y) f g (2 * i + 4) = rr x y (i + 1) ∧
      f (po x y (i + 1)) = rr x y (i + 1)) ∨
    lvl x y (walk (x, y) f g (2 * i + 3)) ≤ -2 := by
  classical
  -- `w_{2i+3} = g (rr i)`
  have hw3 : walk (x, y) f g (2 * i + 3) = g (rr x y i) := by
    have h1 : walk (x, y) f g (2 * i + 2 + 1) = g (walk (x, y) f g (2 * i + 2)) :=
      walk_eq_g_of_even ⟨i + 1, by omega⟩
    rwa [show 2 * i + 2 + 1 = 2 * i + 3 by omega, hprev2] at h1
  -- the four neighbors of `rr i`
  have hadj := walk_succ_adj hf hg hsd (2 * i + 2)
  rw [show 2 * i + 2 + 1 = 2 * i + 3 by omega, hprev2] at hadj
  have hcase : walk (x, y) f g (2 * i + 3) = po x y (i + 1) ∨
      lvl x y (walk (x, y) f g (2 * i + 3)) ≤ -2 := by
    rcases adjacent_cases hadj with h3 | h3 | h3 | h3
    · -- `g (rr i) = (x+i+3, y+i)`: level `-2`
      right
      rw [h3]
      unfold lvl rr
      simp
      omega
    · -- `g (rr i) = (x+i+1, y+i) = po i`: visited, contradiction
      exfalso
      have h4 : walk (x, y) f g (2 * i + 3) = po x y i := by
        rw [h3]
        unfold po rr
        ext <;> simp <;> ring
      have h5 := hinj (2 * i + 3) (by omega) (2 * i + 1) (by omega) (by rw [h4, hprev])
      omega
    · -- `g (rr i) = (x+i+2, y+i+1) = po (i+1)`: continue
      left
      rw [h3]
      unfold po rr
      ext <;> simp <;> ring
    · -- `g (rr i) = (x+i+2, y+i-1)`: level `-2`
      right
      rw [h3]
      unfold lvl rr
      simp
      omega
  rcases hcase with hcont | hbrk
  · -- the continuation case
    have hpo1S : po x y (i + 1) ∈ S := by
      rw [← hcont]
      exact (mem_sd.mp (walk_mem hf hg hsd (2 * i + 3))).1
    have hw4 : walk (x, y) f g (2 * i + 4) = f (po x y (i + 1)) := by
      have h1 : walk (x, y) f g (2 * i + 3 + 1) = f (walk (x, y) f g (2 * i + 3)) :=
        walk_eq_f_of_odd ⟨i + 1, by omega⟩
      rwa [show 2 * i + 3 + 1 = 2 * i + 4 by omega, hcont] at h1
    -- membership for `V`-forcing at `i+1` (from `pe_chain` at `j := i+1`)
    have hck := pe_chain_mem_S hcc hf htf hg htg hsS hodd hmin hfu hgr hm hsd hinj hret hw1 hw2
      (N := N) hnolv (j := i + 1) (by omega) hiN
    have hV : f (pe x y (i + 1)) = uu x y (i + 1) := by
      apply f_pe_eq_uu hf htf hodd hsS hfu hmin (i + 1)
      · intro j' hj'
        by_cases hj0 : j' = 0
        · subst hj0
          rw [pe_zero_eq]
          exact hsS
        · exact hck.1 j' hj' (by omega)
      · intro j' hj'
        by_cases hj0 : j' = 0
        · subst hj0
          have h2 := (hg (x, y) hsS).1
          rw [hgr, ← po_zero_eq] at h2
          exact h2
        · exact hck.2 j' (by omega) (by omega)
    have hforce1 : f (po x y (i + 1)) = rr x y (i + 1) := by
      have hadj2 : Adjacent (po x y (i + 1)) (f (po x y (i + 1))) := (hf _ hpo1S).2.2.2
      rcases adjacent_cases hadj2 with h3 | h3 | h3 | h3
      · -- `f = (x+i+3, y+i+1) = rr (i+1)` ✓
        rw [h3]
        unfold po rr
        ext <;> simp <;> ring
      · -- `f = (x+i+1, y+i+1) = pe (i+1)`: on the cycle, contradicting `hnolv`
        exfalso
        have h4 : f (po x y (i + 1)) = pe x y (i + 1) := by
          rw [h3]
          unfold pe po
          ext <;> simp <;> ring
        have h5 : pe x y (i + 1) ∈ cycSet (x, y) f g m := by
          rw [mem_cycSet]
          exact ⟨2 * i + 4, Finset.mem_range.mpr (by omega), by rw [hw4, h4]⟩
        exact hnolv (i + 1) hiN (by omega) h5
      · -- `f = (x+i+2, y+i+2) = pe (i+2)`: a forbidden vertical pair
        exfalso
        have h4 : f (po x y (i + 1)) = pe x y (i + 2) := by
          rw [h3]
          unfold pe po
          ext <;> simp <;> ring
        have h4' : f (x + ↑(i + 1) + 1, y + ↑(i + 1)) = (x + ↑(i + 1) + 1, y + ↑(i + 1) + 1) := by
          have h5 : f (po x y (i + 1)) = pe x y (i + 2) := h4
          unfold pe po at h5
          rw [show (x + ↑(i + 2) : ℤ) = x + ↑(i + 1) + 1 by push_cast; ring,
            show (y + ↑(i + 2) : ℤ) = y + ↑(i + 1) + 1 by push_cast; ring] at h5
          exact h5
        have hV' : f (x + ↑(i + 1), y + ↑(i + 1)) = (x + ↑(i + 1), y + ↑(i + 1) + 1) := hV
        have hpe1S : pe x y (i + 1) ∈ S := hck.1 (i + 1) (by omega) (by omega)
        obtain ⟨a, ha⟩ := hodd
        exact htf.1 (x + (i + 1 : ℕ)) (y + (i + 1 : ℕ)) hpe1S hpo1S
          ⟨a + (i + 1 : ℕ), by push_cast; omega⟩ ⟨hV', h4'⟩
      · -- `f = (x+i+2, y+i) = rr i`: already matched to `po i`
        exfalso
        have h4 : f (po x y (i + 1)) = rr x y i := by
          rw [h3]
          unfold po rr
          ext <;> simp <;> ring
        have h6 := (hf _ hpo1S).2.1
        rw [h4] at h6
        have h7 : f (rr x y i) = po x y i := by
          have h8 := (hf _ (show po x y i ∈ S from by
            rw [← hprev]
            exact (mem_sd.mp (walk_mem hf hg hsd (2 * i + 1))).1)).2.1
          rw [hforce] at h8
          exact h8
        have h9 : po x y (i + 1) = po x y i := h6.symm.trans h7
        have h10 : (x + ↑(i + 1) + 1 : ℤ) = x + ↑i + 1 := congrArg Prod.fst h9
        omega
    exact Or.inl ⟨hcont, by rw [hw4, hforce1], hforce1⟩
  · exact Or.inr hbrk

-- ============================================================
-- The staircase chain
-- ============================================================

/-- The staircase chain: `w_{2j'+1} = po j'`, `w_{2j'+2} = rr j'` with
`f (po j') = rr j'` for all `j' ≤ n`, unless the walk leaves the staircase
levels at some earlier step (the "break" case). -/
lemma staircase_chain {S : Finset Cell} (hcc : ComplConnected S)
    {f g : Cell → Cell} (hf : IsTiling S f) (htf : Tasteful S f)
    (hg : IsTiling S g) (htg : Tasteful S g)
    {x y : ℤ} (hsS : (x, y) ∈ S) (hodd : Odd (x + y))
    (hmin : ∀ c ∈ S, y ≤ c.2) (hfu : f (x, y) = (x, y + 1)) (hgr : g (x, y) = (x + 1, y))
    {m : ℕ} (hm : 2 ≤ m) (hsd : (x, y) ∈ sd S f g)
    (hinj : ∀ i < 2 * m, ∀ j < 2 * m, walk (x, y) f g i = walk (x, y) f g j → i = j)
    (hret : walk (x, y) f g (2 * m) = (x, y))
    (hw1 : walk (x, y) f g 1 = po x y 0) (hw2 : walk (x, y) f g 2 = rr x y 0)
    {N : ℕ} (hnolv : ∀ j' ≤ N, 1 ≤ j' → pe x y j' ∉ cycSet (x, y) f g m)
    {n : ℕ} (hnN : n + 1 ≤ N) (hn : 2 * n + 2 ≤ 2 * m - 1) :
    (∀ j' ≤ n, walk (x, y) f g (2 * j' + 1) = po x y j' ∧
      walk (x, y) f g (2 * j' + 2) = rr x y j' ∧ f (po x y j') = rr x y j') ∨
    (∃ i ≤ n, (∀ j' ≤ i, walk (x, y) f g (2 * j' + 1) = po x y j' ∧
      walk (x, y) f g (2 * j' + 2) = rr x y j' ∧ f (po x y j') = rr x y j') ∧
      lvl x y (walk (x, y) f g (2 * i + 3)) ≤ -2) := by
  classical
  induction n with
  | zero =>
    refine Or.inl (fun j' hj' => by
      have h0 : j' = 0 := by omega
      subst h0
      exact ⟨hw1, hw2, by
        apply f_po_eq_rr hf htf hodd hsS hfu hmin 0
        · intro j hj
          have h0 : j = 0 := by omega
          subst h0
          rw [pe_zero_eq]
          exact hsS
        · intro j hj
          have h0 : j = 0 := by omega
          subst h0
          have h2 := (hg (x, y) hsS).1
          rw [hgr, ← po_zero_eq] at h2
          exact h2⟩)
  | succ n ih =>
    rcases ih (by omega) (by omega) with h | h
    · -- chain holds to `n`: try the step at `i = n`
      have hstep := staircase_step hcc hf htf hg htg hsS hodd hmin hfu hgr hm hsd hinj hret hw1 hw2
        hnolv (i := n) (by omega) (by omega) (h n (by omega)).1 (h n (by omega)).2.1 (h n (by omega)).2.2
      rcases hstep with hcont | hbrk
      · refine Or.inl (fun j' hj' => ?_)
        by_cases hj'n : j' ≤ n
        · exact h j' hj'n
        · have h1 : j' = n + 1 := by omega
          subst h1
          have h2 : 2 * (n + 1) + 1 = 2 * n + 3 := by ring
          have h3 : 2 * (n + 1) + 2 = 2 * n + 4 := by ring
          rw [h2, h3]
          exact hcont
      · exact Or.inr ⟨n, by omega, h, hbrk⟩
    · -- already broken at some `i ≤ n`
      obtain ⟨i, hi, hchain, hbrk⟩ := h
      exact Or.inr ⟨i, by omega, hchain, hbrk⟩


-- ============================================================
-- Sum parity along the walk
-- ============================================================

/-- The cell-sum parity flips at each step of the walk: `(w n).1 + (w n).2`
differs from `s.1 + s.2 + n` by an even integer. -/
lemma walk_sum_parity {S : Finset Cell} {f g : Cell → Cell}
    (hf : IsTiling S f) (hg : IsTiling S g) {s : Cell} (hs : s ∈ sd S f g) (n : ℕ) :
    Even ((walk s f g n).1 + (walk s f g n).2 - ((s.1 + s.2) + n)) := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    have hadj := walk_succ_adj hf hg hs n
    obtain ⟨a, ha⟩ := ih
    rcases pm_one_of_adjacent hadj with h | h
    · exact ⟨a, by omega⟩
    · exact ⟨a - 1, by omega⟩

/-- `po k` (cell-sum `x + y + 2k + 1`, even since `x + y` is odd) is visited
only at odd times. -/
lemma po_visit_odd {S : Finset Cell} {f g : Cell → Cell} {x y : ℤ}
    (hf : IsTiling S f) (hg : IsTiling S g) (hodd : Odd (x + y))
    (hsd : (x, y) ∈ sd S f g) {k t : ℕ} (ht : walk (x, y) f g t = po x y k) :
    t % 2 = 1 := by
  have hp := walk_sum_parity hf hg hsd t
  rw [ht] at hp
  obtain ⟨a, ha⟩ := hp
  unfold po at ha
  simp at ha
  omega

/-- `pe k` (cell-sum `x + y + 2k`, odd) is visited only at even times. -/
lemma pe_visit_even {S : Finset Cell} {f g : Cell → Cell} {x y : ℤ}
    (hf : IsTiling S f) (hg : IsTiling S g) (hodd : Odd (x + y))
    (hsd : (x, y) ∈ sd S f g) {k t : ℕ} (ht : walk (x, y) f g t = pe x y k) :
    t % 2 = 0 := by
  have hp := walk_sum_parity hf hg hsd t
  rw [ht] at hp
  obtain ⟨a, ha⟩ := hp
  unfold pe at ha
  simp at ha
  omega

/-- `rr k` (cell-sum `x + y + 2k + 2`, odd) is visited only at even times. -/
lemma rr_visit_even {S : Finset Cell} {f g : Cell → Cell} {x y : ℤ}
    (hf : IsTiling S f) (hg : IsTiling S g) (hodd : Odd (x + y))
    (hsd : (x, y) ∈ sd S f g) {k t : ℕ} (ht : walk (x, y) f g t = rr x y k) :
    t % 2 = 0 := by
  have hp := walk_sum_parity hf hg hsd t
  rw [ht] at hp
  obtain ⟨a, ha⟩ := hp
  unfold rr at ha
  simp at ha
  omega

/-- `uu k` (cell-sum `x + y + 2k + 1`, even) is visited only at odd times. -/
lemma uu_visit_odd {S : Finset Cell} {f g : Cell → Cell} {x y : ℤ}
    (hf : IsTiling S f) (hg : IsTiling S g) (hodd : Odd (x + y))
    (hsd : (x, y) ∈ sd S f g) {k t : ℕ} (ht : walk (x, y) f g t = uu x y k) :
    t % 2 = 1 := by
  have hp := walk_sum_parity hf hg hsd t
  rw [ht] at hp
  obtain ⟨a, ha⟩ := hp
  unfold uu at ha
  simp at ha
  omega

-- ============================================================
-- The tangent-below structure before the first level-(≥1) visit
-- ============================================================

/-- At a level-0 visit `po a` (`1 ≤ a`) strictly before time `T` such that no
level-(≥1) cell is visited before `T`, both tilings map `po a` into
`{rr a, rr (a-1)}` (the visit is "tangent-below"). -/
lemma tangent_below {S : Finset Cell} {f g : Cell → Cell} {m : ℕ} {x y : ℤ}
    (hf : IsTiling S f) (hg : IsTiling S g) (hodd : Odd (x + y))
    (hmin : ∀ c ∈ S, y ≤ c.2)
    (hsd : (x, y) ∈ sd S f g) {T : ℕ}
    (hT : ∀ t' < T, 1 ≤ t' → lvl x y (walk (x, y) f g t') < 1)
    {a u : ℕ} (ha : walk (x, y) f g u = po x y a) (ha1 : 1 ≤ a)
    (hu : u + 1 < T) (hu1 : 2 ≤ u) :
    (f (po x y a) = rr x y a ∨ f (po x y a) = rr x y (a - 1)) ∧
    (g (po x y a) = rr x y a ∨ g (po x y a) = rr x y (a - 1)) := by
  classical
  have huodd : u % 2 = 1 := po_visit_odd hf hg hodd hsd ha
  have hupa : u % 2 = 1 := huodd
  -- `f (po a) = w_{u+1}` (odd index gives an `f`-step)
  have hfstep : walk (x, y) f g (u + 1) = f (po x y a) := by
    have h1 : walk (x, y) f g (u + 1) = f (walk (x, y) f g u) :=
      walk_eq_f_of_odd (Nat.odd_iff.mpr hupa)
    rwa [ha] at h1
  -- `g (po a) = w_{u-1}` (`u-1` even gives a `g`-step, then involution)
  have hgstep : walk (x, y) f g (u - 1 + 1) = g (walk (x, y) f g (u - 1)) := by
    have h1 : Even (u - 1) := by
      have h2 : u % 2 = 1 := hupa
      refine ⟨(u - 1) / 2, by omega⟩
    exact walk_eq_g_of_even h1
  have hgstep2 : g (po x y a) = walk (x, y) f g (u - 1) := by
    have h2 : u - 1 + 1 = u := by omega
    rw [h2, ha] at hgstep
    have h3 := (hg _ (mem_sd.mp (walk_mem hf hg hsd (u - 1))).1).2.1
    rw [← hgstep] at h3
    exact h3
  -- level of `w_{u+1}` is `-1`
  have hflvl : lvl x y (f (po x y a)) = -1 := by
    have h1 : u + 1 < T := hu
    have h2 := hT (u + 1) h1 (by omega)
    rw [hfstep] at h2
    have h3 : lvl x y (f (po x y a)) = lvl x y (po x y a) + 1 ∨
        lvl x y (f (po x y a)) = lvl x y (po x y a) - 1 :=
      lvl_adj_cases (show Adjacent (po x y a) (f (po x y a)) from
        (hf _ (by rw [← ha]; exact (mem_sd.mp (walk_mem hf hg hsd u)).1)).2.2.2)
    rw [show lvl x y (po x y a) = 0 from lvl_po x y a] at h3
    omega
  -- level of `w_{u-1}` is `-1` (not `0` since level-0 visits are at odd times)
  have hglvl : lvl x y (g (po x y a)) = -1 := by
    have h2 : u - 1 < T := by omega
    have h3 : 2 ≤ u := hu1
    have h4 := hT (u - 1) h2 (by omega)
    rw [← hgstep2] at h4
    have h5 : lvl x y (g (po x y a)) = lvl x y (po x y a) + 1 ∨
        lvl x y (g (po x y a)) = lvl x y (po x y a) - 1 :=
      lvl_adj_cases (show Adjacent (po x y a) (g (po x y a)) from by
        have hS : po x y a ∈ S := by rw [← ha]; exact (mem_sd.mp (walk_mem hf hg hsd u)).1
        exact (hg _ hS).2.2.2)
    rw [show lvl x y (po x y a) = 0 from lvl_po x y a] at h5
    have h7 : lvl x y (g (po x y a)) ≠ 0 := by
      intro h8
      obtain ⟨b, hb⟩ := eq_po_of_lvl_zero (hmin _ (by
        rw [hgstep2]
        exact (mem_sd.mp (walk_mem hf hg hsd (u - 1))).1)) h8
      have h9 : (u - 1) % 2 = 1 := po_visit_odd hf hg hodd hsd (by rw [← hgstep2, hb])
      omega
    omega
  -- conclude by the level-(-1) neighbor analysis
  have haf : Adjacent (po x y a) (f (po x y a)) :=
    (hf _ (by rw [← ha]; exact (mem_sd.mp (walk_mem hf hg hsd u)).1)).2.2.2
  have hag : Adjacent (po x y a) (g (po x y a)) := by
    have hS : po x y a ∈ S := by rw [← ha]; exact (mem_sd.mp (walk_mem hf hg hsd u)).1
    exact (hg _ hS).2.2.2
  exact ⟨po_lvl_neg_one_neighbors ha1 rfl haf hflvl, po_lvl_neg_one_neighbors ha1 rfl hag hglvl⟩


-- ============================================================
-- The first level-(≥1) visit: the crossing
-- ============================================================

/-- The first time (in `[1, 2m-1]`) that the walk reaches a level-(≥1) cell:
it lands on a level-1 cell `pe k'`, preceded by a level-0 cell `po j₀` with
`f (po j₀) = pe k'` (the "crossing"). -/
lemma first_lvl_ge_one_visit {S : Finset Cell} {f g : Cell → Cell} {m : ℕ} {x y : ℤ}
    (hf : IsTiling S f) (hg : IsTiling S g)
    (hodd : Odd (x + y)) (hmin : ∀ c ∈ S, y ≤ c.2)
    (hsd : (x, y) ∈ sd S f g)
    (hw1 : walk (x, y) f g 1 = po x y 0)
    (hex : ∃ t, 1 ≤ t ∧ t ≤ 2 * m - 1 ∧ lvl x y (walk (x, y) f g t) ≥ 1) :
    ∃ τ₀ k' j₀ : ℕ, 2 ≤ τ₀ ∧ τ₀ ≤ 2 * m - 1 ∧ Even τ₀ ∧
      walk (x, y) f g τ₀ = pe x y k' ∧ walk (x, y) f g (τ₀ - 1) = po x y j₀ ∧
      f (po x y j₀) = pe x y k' ∧
      (∀ t' < τ₀, 1 ≤ t' → lvl x y (walk (x, y) f g t') < 1) := by
  classical
  obtain ⟨ht1, ht2, ht3⟩ := Nat.find_spec hex
  have ht3' : lvl x y (walk (x, y) f g (Nat.find hex)) ≥ 1 := ht3
  have htmin : ∀ t' < Nat.find hex, 1 ≤ t' → lvl x y (walk (x, y) f g t') < 1 := by
    intro t' ht' ht'2
    by_contra hcon
    push_neg at hcon
    by_cases h1 : t' ≤ 2 * m - 1
    · exact Nat.find_min hex ht' ⟨ht'2, h1, hcon⟩
    · omega
  have ht0ge2 : 2 ≤ Nat.find hex := by
    by_contra hcon
    have h1 : Nat.find hex = 1 := by omega
    rw [h1, hw1, lvl_po] at ht3'
    omega
  have hlvl1 : lvl x y (walk (x, y) f g (Nat.find hex)) = 1 := by
    have h1 := htmin (Nat.find hex - 1) (by omega) (by omega)
    have h2 : lvl x y (walk (x, y) f g (Nat.find hex - 1 + 1)) =
        lvl x y (walk (x, y) f g (Nat.find hex - 1)) + 1 ∨
      lvl x y (walk (x, y) f g (Nat.find hex - 1 + 1)) =
        lvl x y (walk (x, y) f g (Nat.find hex - 1)) - 1 :=
      lvl_adj_cases (walk_succ_adj hf hg hsd (Nat.find hex - 1))
    rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega] at h2
    omega
  have hwtS : walk (x, y) f g (Nat.find hex) ∈ S := (mem_sd.mp (walk_mem hf hg hsd _)).1
  obtain ⟨k', hk'⟩ := eq_pe_of_lvl_one (hmin _ hwtS) hlvl1
  have hwtS2 : walk (x, y) f g (Nat.find hex - 1) ∈ S :=
    (mem_sd.mp (walk_mem hf hg hsd _)).1
  have hlvl0 : lvl x y (walk (x, y) f g (Nat.find hex - 1)) = 0 := by
    have h1 := htmin (Nat.find hex - 1) (by omega) (by omega)
    have h2 : lvl x y (walk (x, y) f g (Nat.find hex - 1 + 1)) =
        lvl x y (walk (x, y) f g (Nat.find hex - 1)) + 1 ∨
      lvl x y (walk (x, y) f g (Nat.find hex - 1 + 1)) =
        lvl x y (walk (x, y) f g (Nat.find hex - 1)) - 1 :=
      lvl_adj_cases (walk_succ_adj hf hg hsd (Nat.find hex - 1))
    rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega, hlvl1] at h2
    omega
  obtain ⟨j₀, hj₀⟩ := eq_po_of_lvl_zero (hmin _ hwtS2) hlvl0
  have hte : Even (Nat.find hex) := by
    have h1 := pe_visit_even hf hg hodd hsd hk'
    exact Nat.even_iff.mpr h1
  have hfo : f (po x y j₀) = pe x y k' := by
    have h2 : Odd (Nat.find hex - 1) := by
      obtain ⟨a, ha⟩ := hte
      exact ⟨a - 1, by omega⟩
    have h1 : walk (x, y) f g (Nat.find hex - 1 + 1) =
        f (walk (x, y) f g (Nat.find hex - 1)) := walk_eq_f_of_odd h2
    rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega, hj₀, hk'] at h1
    exact h1.symm
  exact ⟨Nat.find hex, k', j₀, ht0ge2, ht2, hte, hk', hj₀, hfo, htmin⟩


-- ============================================================
-- The defect at the crossing forces a staircase gap
-- ============================================================

/-- If `f (po j₀) ≠ rr j₀` (a "defect" at `po j₀`, e.g. from the crossing),
then some staircase cell below `j₀` is missing from `S` (a "gap").
This is just the contrapositive of `f_po_eq_rr` (the H-cascade). -/
lemma exists_gap_of_defect {S : Finset Cell} {f : Cell → Cell} (hf : IsTiling S f)
    (htf : Tasteful S f) {x y : ℤ} (hodd : Odd (x + y)) (hsS : (x, y) ∈ S)
    (hfu : f (x, y) = (x, y + 1)) (hmin : ∀ c ∈ S, y ≤ c.2)
    (j₀ : ℕ) (hdef : f (po x y j₀) ≠ rr x y j₀) :
    (∃ j'' ≤ j₀, pe x y j'' ∉ S) ∨ (∃ j'' ≤ j₀, po x y j'' ∉ S) := by
  by_contra h
  push_neg at h
  obtain ⟨hE, hO⟩ := h
  exact hdef (f_po_eq_rr hf htf hodd hsS hfu hmin j₀
    (fun j hj => hE j hj) (fun j hj => hO j hj))


/-- The two level-1 neighbors of `po k` are `pe k` (west) and `pe (k+1)` (north). -/
lemma po_lvl_one_neighbors {x y : ℤ} {c : Cell} {k : ℕ} (hk : 1 ≤ k)
    (h : c = po x y k) {c' : Cell} (hadj : Adjacent c c') (hl : lvl x y c' = 1) :
    c' = pe x y k ∨ c' = pe x y (k + 1) := by
  subst h
  rcases adjacent_cases hadj with h1 | h1 | h1 | h1
  · exfalso
    have h2 : c' = rr x y k := by
      rw [h1]
      unfold po rr
      ext <;> simp <;> omega
    rw [h2, lvl_rr] at hl
    omega
  · left
    have h2 : c' = pe x y k := by
      rw [h1]
      unfold po pe
      ext <;> simp <;> omega
    exact h2
  · right
    have h2 : c' = pe x y (k + 1) := by
      rw [h1]
      unfold po pe
      ext <;> simp <;> omega
    exact h2
  · exfalso
    have h2 : c' = rr x y (k - 1) := by
      rw [h1]
      unfold po rr
      ext <;> simp <;> omega
    rw [h2, lvl_rr] at hl
    omega

-- ============================================================
-- The crossing conflict: the free cases (membership complete)
-- ============================================================

/-- **Free case V**: if the crossing cell `pe k'` satisfies `k' ≤ N + 1`
(where `pe 1, …, pe N` are all off the cycle), then staircase `V`-forcing
gives `f (pe k') = uu k'`, while the crossing gives `f (pe k') = po j₀` —
a coordinate contradiction. -/
lemma crossing_conflict_V {S : Finset Cell} {f g : Cell → Cell} {m : ℕ} {x y : ℤ}
    (hf : IsTiling S f) (htf : Tasteful S f) (hg : IsTiling S g) (htg : Tasteful S g)
    (hcc : ComplConnected S)
    (hsS : (x, y) ∈ S) (hodd : Odd (x + y)) (hmin : ∀ c ∈ S, y ≤ c.2)
    (hfu : f (x, y) = (x, y + 1)) (hgr : g (x, y) = (x + 1, y))
    (hm : 2 ≤ m) (hsd : (x, y) ∈ sd S f g)
    (hinj : ∀ i < 2 * m, ∀ j < 2 * m, walk (x, y) f g i = walk (x, y) f g j → i = j)
    (hret : walk (x, y) f g (2 * m) = (x, y))
    (hw1 : walk (x, y) f g 1 = po x y 0) (hw2 : walk (x, y) f g 2 = rr x y 0)
    {N : ℕ} (hnolv : ∀ j' ≤ N, 1 ≤ j' → pe x y j' ∉ cycSet (x, y) f g m)
    {k' j₀ : ℕ} (hkγ : pe x y k' ∈ cycSet (x, y) f g m)
    (hkj : f (po x y j₀) = pe x y k') (hjS : po x y j₀ ∈ S)
    (hk'N : k' ≤ N + 1) : False := by
  have hpe0 : pe x y 0 = (x, y) := by unfold pe; simp
  have hpo0 : po x y 0 = (x + 1, y) := by unfold po; simp
  -- `1 ≤ k'`: the crossing value `pe k'` cannot be `pe 0 = (x, y)`
  have hk0 : 1 ≤ k' := by
    by_contra hcon
    push_neg at hcon
    have h0 : k' = 0 := by omega
    subst h0
    rw [hpe0] at hkj
    have hinv := (hf _ hjS).2.1
    rw [hkj, hfu] at hinv
    unfold po at hinv
    simp [Prod.ext_iff] at hinv
    omega
  -- hence `k' = N + 1`
  have hk'eq : k' = N + 1 := by
    by_contra hcon
    have h1 : k' ≤ N := by omega
    exact hnolv k' h1 hk0 hkγ
  -- staircase membership below `k'`
  have hE : ∀ j ≤ k', pe x y j ∈ S := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · subst hj0
      rw [hpe0]
      exact hsS
    · by_cases hjN : j ≤ N
      · have hN1 : 1 ≤ N := by omega
        exact (pe_chain_mem_S hcc hf htf hg htg hsS hodd hmin hfu hgr hm hsd hinj
          hret hw1 hw2 hnolv hN1 le_rfl).1 j hjN hj0
      · have hjk : j = k' := by omega
        rw [hjk]
        exact (mem_sd.mp (cycSet_subset_sd hf hg hsd hkγ)).1
  have hO : ∀ j < k', po x y j ∈ S := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · subst hj0
      rw [hpo0, ← hgr]
      exact (hg _ hsS).1
    · have hjN : j ≤ N := by omega
      have hN1 : 1 ≤ N := by omega
      exact (pe_chain_mem_S hcc hf htf hg htg hsS hodd hmin hfu hgr hm hsd hinj
        hret hw1 hw2 hnolv hN1 le_rfl).2 j hjN hj0
  -- the single-cell conflict
  have hV := f_pe_eq_uu hf htf hodd hsS hfu hmin k' hE hO
  have hinv := (hf _ hjS).2.1
  rw [hkj, hV] at hinv
  unfold uu po at hinv
  simp [Prod.ext_iff] at hinv
  omega

/-- **Free case H**: if the crossing source `po j₀` satisfies `j₀ ≤ N + 1`
(and `pe (N+1) ∈ S`), then staircase `H`-forcing gives `f (po j₀) = rr j₀`,
while the crossing gives `f (po j₀) = pe k'` — a coordinate contradiction. -/
lemma crossing_conflict_H {S : Finset Cell} {f g : Cell → Cell} {m : ℕ} {x y : ℤ}
    (hf : IsTiling S f) (htf : Tasteful S f) (hg : IsTiling S g) (htg : Tasteful S g)
    (hcc : ComplConnected S)
    (hsS : (x, y) ∈ S) (hodd : Odd (x + y)) (hmin : ∀ c ∈ S, y ≤ c.2)
    (hfu : f (x, y) = (x, y + 1)) (hgr : g (x, y) = (x + 1, y))
    (hm : 2 ≤ m) (hsd : (x, y) ∈ sd S f g)
    (hinj : ∀ i < 2 * m, ∀ j < 2 * m, walk (x, y) f g i = walk (x, y) f g j → i = j)
    (hret : walk (x, y) f g (2 * m) = (x, y))
    (hw1 : walk (x, y) f g 1 = po x y 0) (hw2 : walk (x, y) f g 2 = rr x y 0)
    {N : ℕ} (hnolv : ∀ j' ≤ N, 1 ≤ j' → pe x y j' ∉ cycSet (x, y) f g m)
    (hpeN : pe x y (N + 1) ∈ S)
    {k' j₀ : ℕ} (hkj : f (po x y j₀) = pe x y k') (hjS : po x y j₀ ∈ S)
    (hj₀N : j₀ ≤ N + 1) : False := by
  have hpe0 : pe x y 0 = (x, y) := by unfold pe; simp
  have hpo0 : po x y 0 = (x + 1, y) := by unfold po; simp
  have hE : ∀ j ≤ j₀, pe x y j ∈ S := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · subst hj0
      rw [hpe0]
      exact hsS
    · by_cases hjN : j ≤ N
      · have hN1 : 1 ≤ N := by omega
        exact (pe_chain_mem_S hcc hf htf hg htg hsS hodd hmin hfu hgr hm hsd hinj
          hret hw1 hw2 hnolv hN1 le_rfl).1 j hjN hj0
      · have hjk : j = N + 1 := by omega
        rw [hjk]
        exact hpeN
  have hO : ∀ j ≤ j₀, po x y j ∈ S := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · subst hj0
      rw [hpo0, ← hgr]
      exact (hg _ hsS).1
    · by_cases hjN : j ≤ N
      · have hN1 : 1 ≤ N := by omega
        exact (pe_chain_mem_S hcc hf htf hg htg hsS hodd hmin hfu hgr hm hsd hinj
          hret hw1 hw2 hnolv hN1 le_rfl).2 j hjN hj0
      · have hjk : j = j₀ := by omega
        rw [hjk]
        exact hjS
  have hH := f_po_eq_rr hf htf hodd hsS hfu hmin j₀ hE hO
  rw [hkj] at hH
  unfold pe rr at hH
  simp [Prod.ext_iff] at hH
  omega

-- ============================================================
-- The Lemma A staircase induction: propagation and the break case
-- ============================================================

/-- Eastward membership propagation (step 5 of the Lemma A induction): from
`pe (i+1)` inside and off the cycle (and the chain below), the next staircase
cell `pe (i+2)` is inside or on the cycle. -/
lemma pe_succ_inside_or_cyc {S : Finset Cell} (hcc : ComplConnected S)
    {f g : Cell → Cell} (hf : IsTiling S f) (htf : Tasteful S f)
    (hg : IsTiling S g) (htg : Tasteful S g)
    {x y : ℤ} (hsS : (x, y) ∈ S) (hodd : Odd (x + y))
    (hmin : ∀ c ∈ S, y ≤ c.2) (hfu : f (x, y) = (x, y + 1)) (hgr : g (x, y) = (x + 1, y))
    {m : ℕ} (hm : 2 ≤ m) (hsd : (x, y) ∈ sd S f g)
    (hinj : ∀ i < 2 * m, ∀ j < 2 * m, walk (x, y) f g i = walk (x, y) f g j → i = j)
    (hret : walk (x, y) f g (2 * m) = (x, y))
    (hw1 : walk (x, y) f g 1 = po x y 0) (hw2 : walk (x, y) f g 2 = rr x y 0)
    {N : ℕ} (hnolv : ∀ j' ≤ N, 1 ≤ j' → pe x y j' ∉ cycSet (x, y) f g m)
    {i : ℕ} (hiN : i + 1 ≤ N)
    (hpe1 : inside (x, y) f g m (pe x y (i + 1)))
    (hpe1γ : pe x y (i + 1) ∉ cycSet (x, y) f g m) :
    inside (x, y) f g m (pe x y (i + 2)) ∨ pe x y (i + 2) ∈ cycSet (x, y) f g m := by
  have hchain := pe_chain_mem_S hcc hf htf hg htg hsS hodd hmin hfu hgr hm hsd hinj
    hret hw1 hw2 hnolv (j := i + 1) (by omega) hiN
  have hE : ∀ j ≤ i + 1, pe x y j ∈ S := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · subst hj0
      rw [show pe x y 0 = (x, y) from by unfold pe; simp]
      exact hsS
    · exact hchain.1 j hj hj0
  have hO : ∀ j < i + 1, po x y j ∈ S := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · subst hj0
      rw [show po x y 0 = (x + 1, y) from by unfold po; simp, ← hgr]
      exact (hg _ hsS).1
    · exact hchain.2 j (by omega) hj0
  have hV : f (pe x y (i + 1)) = uu x y (i + 1) :=
    f_pe_eq_uu hf htf hodd hsS hfu hmin (i + 1) hE hO
  have hpe1S : pe x y (i + 1) ∈ S := inside_mem_S hf hg hcc hsd hinj hm hret hpe1
  obtain ⟨huu, huuγ⟩ := inside_off_cycle_f_partner hf hg hsd hinj hm hret hpe1S hpe1 hpe1γ
  rw [hV] at huu huuγ
  exact propagate_pe_succ hf hg hsd hinj hm hret (i + 1) huu huuγ

/-- The break case of the staircase step lands at a `po k` with `k ≥ i+2`:
the first return to level `0` after the break at `2i+3` cannot be at `k ≤ i`
(already visited, by injectivity) nor at `k = i+1` (the down-bounce would put
`po i` at `t - 2`, contradicting the first-hit minimality). -/
lemma break_landing_ge {S : Finset Cell} (hcc : ComplConnected S)
    {f g : Cell → Cell} (hf : IsTiling S f) (htf : Tasteful S f)
    (hg : IsTiling S g) (htg : Tasteful S g)
    {x y : ℤ} (hsS : (x, y) ∈ S) (hodd : Odd (x + y))
    (hmin : ∀ c ∈ S, y ≤ c.2) (hfu : f (x, y) = (x, y + 1)) (hgr : g (x, y) = (x + 1, y))
    {m : ℕ} (hm : 2 ≤ m) (hsd : (x, y) ∈ sd S f g)
    (hinj : ∀ i < 2 * m, ∀ j < 2 * m, walk (x, y) f g i = walk (x, y) f g j → i = j)
    (hret : walk (x, y) f g (2 * m) = (x, y))
    (hw1 : walk (x, y) f g 1 = po x y 0) (hw2 : walk (x, y) f g 2 = rr x y 0)
    (hwlast : walk (x, y) f g (2 * m - 1) = uu x y 0)
    {N : ℕ} (hnolv : ∀ j' ≤ N, 1 ≤ j' → pe x y j' ∉ cycSet (x, y) f g m)
    {i : ℕ} (hiN : i + 1 ≤ N) (hi : 2 * i + 4 ≤ 2 * m - 1)
    (hprefix : ∀ j' ≤ i, walk (x, y) f g (2 * j' + 1) = po x y j' ∧
      walk (x, y) f g (2 * j' + 2) = rr x y j')
    (hbrk : lvl x y (walk (x, y) f g (2 * i + 3)) ≤ -2) :
    ∃ t k : ℕ, 2 * i + 5 ≤ t ∧ t ≤ 2 * m - 1 ∧ Odd t ∧
      walk (x, y) f g t = po x y k ∧ i + 2 ≤ k ∧
      lvl x y (walk (x, y) f g (t - 1)) = -1 ∧
      (∀ t' < t, 2 * i + 2 ≤ t' → lvl x y (walk (x, y) f g t') < 0) := by
  have hrr2 : lvl x y (walk (x, y) f g (2 * i + 2)) = -1 := by
    rw [(hprefix i le_rfl).2, lvl_rr]
  obtain ⟨t, k, ht0, ht1, htlvl, htk, htprev, htmin⟩ :=
    return_landing2 hf hg hmin hsd (a := 2 * i + 2) (by omega) hwlast hrr2 (by omega)
  have htodd : Odd t := Nat.odd_iff.mpr (po_visit_odd hf hg hodd hsd htk)
  -- `t ≠ 2i+2` (level `0` vs `-1`) and `t ≠ 2i+3` (level `0` vs `≤ -2`)
  have ht5 : 2 * i + 5 ≤ t := by
    by_contra hcon
    push_neg at hcon
    have h2 : t = 2 * i + 2 ∨ t = 2 * i + 3 ∨ t = 2 * i + 4 := by omega
    rcases h2 with h2 | h2 | h2
    · rw [h2] at htlvl
      omega
    · rw [h2] at htlvl
      omega
    · rw [h2] at htodd
      exact Nat.not_odd_iff_even.mpr ⟨i + 2, by omega⟩ htodd
  -- `k ≠ 0`: `po 0 = w₁` is already visited
  have hk0 : 1 ≤ k := by
    by_contra hcon
    push_neg at hcon
    have h0 : k = 0 := by omega
    subst h0
    rw [← hw1] at htk
    have h2 := hinj t (by omega) 1 (by omega) htk
    omega
  -- `k ≤ i` is impossible: `po k = w_{2k+1}` already visited
  have hkge : i + 1 ≤ k := by
    by_contra hcon
    push_neg at hcon
    have h2 := hinj t (by omega) (2 * k + 1) (by omega) (by
      rw [htk, (hprefix k (by omega)).1])
    omega
  -- `k = i+1` is impossible: the down-bounce lands `po i` at `t-2`
  have hkge2 : i + 2 ≤ k := by
    by_contra hcon
    push_neg at hcon
    have hk : k = i + 1 := by omega
    subst hk
    have hchain := pe_chain_mem_S hcc hf htf hg htg hsS hodd hmin hfu hgr hm hsd
      hinj hret hw1 hw2 hnolv (j := i + 1) (by omega) hiN
    have hpoS : po x y (i + 1) ∈ S := by
      rw [← htk]
      exact (mem_sd.mp (walk_mem hf hg hsd t)).1
    have hmem : ∀ j' ≤ i + 1, po x y j' ∈ S := by
      intro j' hj'
      by_cases h3 : j' ≤ i
      · rcases Nat.eq_zero_or_pos j' with hj0 | hj0
        · subst hj0
          rw [show po x y 0 = (x + 1, y) from by unfold po; simp, ← hgr]
          exact (hg _ hsS).1
        · exact hchain.2 j' (by omega) hj0
      · have h3 : j' = i + 1 := by omega
        rw [h3]
        exact hpoS
    have hmemV : ∀ j' ≤ i + 1, pe x y j' ∈ S := by
      intro j' hj'
      rcases Nat.eq_zero_or_pos j' with hj0 | hj0
      · subst hj0
        rw [show pe x y 0 = (x, y) from by unfold pe; simp]
        exact hsS
      · exact hchain.1 j' hj' hj0
    have hmemV1 : ∀ j' < i + 1, po x y j' ∈ S := fun j' hj' => hmem j' (by omega)
    have hmemV2 : ∀ j' ≤ i, pe x y j' ∈ S := fun j' hj' => hmemV j' (by omega)
    obtain ⟨-, -, hb2⟩ := bounce_at_return hf hg htf hsd hinj hm hret hsS hodd
      hfu hmin htk htodd (by omega) (by omega) htprev hmem hmemV hmemV1 hmemV2
    have h3 := htmin (t - 2) (by omega) (by omega)
    rw [hb2, lvl_po] at h3
    omega
  exact ⟨t, k, ht5, ht1, htodd, htk, hkge2, htprev, htmin⟩

-- ============================================================
-- The cascade/landing interfaces and the conditional Lemma A (odd case)
-- ============================================================

/-- The induction step of Lemma A, conditional on the cascade hypothesis
`hcascade` (any staircase gap at index `≥ N+1` is impossible) and the landing
hypothesis `hlanding` (no landing at `po k` with `k ≥ N+1`).  From the walk
prefix to stage `i`, the inside-ness of `pe (i+1)`, and `pe 1, …, pe (i+1)`
off the cycle, the walk continues to stage `i+1` and `pe (i+2)` is inside and
off the cycle. -/
lemma lemma_a_step_of_cascade {S : Finset Cell} (hcc : ComplConnected S)
    {f g : Cell → Cell} (hf : IsTiling S f) (htf : Tasteful S f)
    (hg : IsTiling S g) (htg : Tasteful S g)
    {x y : ℤ} (hsS : (x, y) ∈ S) (hodd : Odd (x + y))
    (hmin : ∀ c ∈ S, y ≤ c.2) (hfu : f (x, y) = (x, y + 1)) (hgr : g (x, y) = (x + 1, y))
    {m : ℕ} (hm : 2 ≤ m) (hsd : (x, y) ∈ sd S f g)
    (hinj : ∀ i < 2 * m, ∀ j < 2 * m, walk (x, y) f g i = walk (x, y) f g j → i = j)
    (hret : walk (x, y) f g (2 * m) = (x, y))
    (hw1 : walk (x, y) f g 1 = po x y 0) (hw2 : walk (x, y) f g 2 = rr x y 0)
    (hwlast : walk (x, y) f g (2 * m - 1) = uu x y 0)
    (hcascade : ∀ (N' i' : ℕ), 2 * i' + 4 ≤ 2 * m - 1 →
      (∀ j' ≤ i', walk (x, y) f g (2 * j' + 1) = po x y j' ∧
        walk (x, y) f g (2 * j' + 2) = rr x y j') →
      (∀ j' ≤ N', 1 ≤ j' → pe x y j' ∉ cycSet (x, y) f g m) →
      N' ≤ i' + 1 →
      (∃ J, N' + 1 ≤ J ∧ (pe x y J ∉ S ∨ po x y J ∉ S)) → False)
    (hlanding : ∀ (N' i' : ℕ), 2 * i' + 4 ≤ 2 * m - 1 →
      (∀ j' ≤ i', walk (x, y) f g (2 * j' + 1) = po x y j' ∧
        walk (x, y) f g (2 * j' + 2) = rr x y j') →
      (∀ j' ≤ N', 1 ≤ j' → pe x y j' ∉ cycSet (x, y) f g m) →
      N' ≤ i' + 1 →
      ∀ {t k : ℕ}, 2 * i' + 5 ≤ t → t ≤ 2 * m - 1 → Odd t →
      walk (x, y) f g t = po x y k → N' + 1 ≤ k →
      lvl x y (walk (x, y) f g (t - 1)) = -1 →
      (∀ t' < t, 2 * i' + 2 ≤ t' → lvl x y (walk (x, y) f g t') < 0) → False)
    {i : ℕ} (hi : 2 * i + 4 ≤ 2 * m - 1)
    (hprefix : ∀ j' ≤ i, walk (x, y) f g (2 * j' + 1) = po x y j' ∧
      walk (x, y) f g (2 * j' + 2) = rr x y j' ∧ f (po x y j') = rr x y j')
    (hnolv : ∀ j' ≤ i + 1, 1 ≤ j' → pe x y j' ∉ cycSet (x, y) f g m)
    (hpe1 : inside (x, y) f g m (pe x y (i + 1))) :
    (∀ j' ≤ i + 1, walk (x, y) f g (2 * j' + 1) = po x y j' ∧
      walk (x, y) f g (2 * j' + 2) = rr x y j' ∧ f (po x y j') = rr x y j') ∧
    inside (x, y) f g m (pe x y (i + 2)) ∧ pe x y (i + 2) ∉ cycSet (x, y) f g m := by
  have hprefix' : ∀ j' ≤ i, walk (x, y) f g (2 * j' + 1) = po x y j' ∧
      walk (x, y) f g (2 * j' + 2) = rr x y j' :=
    fun j' hj' => ⟨(hprefix j' hj').1, (hprefix j' hj').2.1⟩
  -- the walk step at stage `i`: continue, or break (killed by `hlanding`)
  have hstep : (walk (x, y) f g (2 * i + 3) = po x y (i + 1) ∧
      walk (x, y) f g (2 * i + 4) = rr x y (i + 1) ∧
      f (po x y (i + 1)) = rr x y (i + 1)) := by
    rcases staircase_step hcc hf htf hg htg hsS hodd hmin hfu hgr hm hsd hinj hret
      hw1 hw2 hnolv (i := i) (by omega) hi (hprefix i le_rfl).1 (hprefix i le_rfl).2.1
      (hprefix i le_rfl).2.2 with hcont | hbrk
    · exact hcont
    · exfalso
      obtain ⟨t, k, ht5, ht1, htodd, htk, hk2, htprev, htmin⟩ :=
        break_landing_ge hcc hf htf hg htg hsS hodd hmin hfu hgr hm hsd hinj hret
          hw1 hw2 hwlast hnolv (i := i) (by omega) hi hprefix' hbrk
      exact hlanding (i + 1) i hi hprefix' hnolv (by omega) ht5 ht1 htodd htk hk2
        htprev htmin
  -- `pe (i+2)` is off the cycle: the crossing analysis
  have hpe2γ : pe x y (i + 2) ∉ cycSet (x, y) f g m := by
    intro hpe2c
    have hex : ∃ t, 1 ≤ t ∧ t ≤ 2 * m - 1 ∧ lvl x y (walk (x, y) f g t) ≥ 1 := by
      rw [mem_cycSet] at hpe2c
      obtain ⟨t, htr, hte⟩ := hpe2c
      have ht2 : t < 2 * m := Finset.mem_range.mp htr
      have ht0 : t ≠ 0 := by
        intro h0
        rw [h0, walk_zero] at hte
        unfold pe at hte
        simp [Prod.ext_iff] at hte
        omega
      refine ⟨t, by omega, by omega, ?_⟩
      rw [hte, lvl_pe]
    obtain ⟨τ₀, k', jō, hτ0, hτ02, hτe, hwτ, hwτ1, hfcross, hfirst⟩ :=
      first_lvl_ge_one_visit hf hg hodd hmin hsd hw1 hex
    have hkγ : pe x y k' ∈ cycSet (x, y) f g m :=
      mem_cycSet.mpr ⟨τ₀, Finset.mem_range.mpr (by omega), hwτ⟩
    have hjS : po x y jō ∈ S := by
      rw [← hwτ1]
      exact (mem_sd.mp (walk_mem hf hg hsd (τ₀ - 1))).1
    by_cases hk'2 : k' ≤ i + 2
    · exact crossing_conflict_V hf htf hg htg hcc hsS hodd hmin hfu hgr hm hsd
        hinj hret hw1 hw2 hnolv hkγ hfcross hjS (by omega)
    · by_cases hj2 : jō ≤ i + 2
      · exact crossing_conflict_H hf htf hg htg hcc hsS hodd hmin hfu hgr hm hsd
          hinj hret hw1 hw2 hnolv
          ((mem_sd.mp (cycSet_subset_sd hf hg hsd hpe2c)).1) hfcross hjS (by omega)
      · -- the stall case: a defect at `jō`, hence a gap, hence the cascade
        have hdef : f (po x y jō) ≠ rr x y jō := by
          rw [hfcross]
          intro hcon
          unfold pe rr at hcon
          simp [Prod.ext_iff] at hcon
          omega
        have hgap := exists_gap_of_defect hf htf hodd hsS hfu hmin jō hdef
        have hmem_pe : ∀ J ≤ i + 1, 1 ≤ J → pe x y J ∈ S :=
          (pe_chain_mem_S hcc hf htf hg htg hsS hodd hmin hfu hgr hm hsd hinj hret
            hw1 hw2 hnolv (j := i + 1) (by omega) le_rfl).1
        have hmem_po : ∀ J ≤ i + 1, 1 ≤ J → po x y J ∈ S :=
          (pe_chain_mem_S hcc hf htf hg htg hsS hodd hmin hfu hgr hm hsd hinj hret
            hw1 hw2 hnolv (j := i + 1) (by omega) le_rfl).2
        rcases hgap with ⟨J, hJ1, hJ2⟩ | ⟨J, hJ1, hJ2⟩
        · by_cases hJN : J ≤ i + 1
          · rcases Nat.eq_zero_or_pos J with hJ0 | hJ0
            · subst hJ0
              exact hJ2 (by rw [pe_zero_eq]; exact hsS)
            · exact hJ2 (hmem_pe J hJN hJ0)
          · exact hcascade (i + 1) i hi hprefix' hnolv (by omega) ⟨J, by omega,
              Or.inl hJ2⟩
        · by_cases hJN : J ≤ i + 1
          · rcases Nat.eq_zero_or_pos J with hJ0 | hJ0
            · subst hJ0
              exact hJ2 (by rw [po_zero_eq, ← hgr]; exact (hg _ hsS).1)
            · exact hJ2 (hmem_po J hJN hJ0)
          · exact hcascade (i + 1) i hi hprefix' hnolv (by omega) ⟨J, by omega,
              Or.inr hJ2⟩
  -- `pe (i+2)` is inside
  have hpe2in : inside (x, y) f g m (pe x y (i + 2)) := by
    rcases pe_succ_inside_or_cyc hcc hf htf hg htg hsS hodd hmin hfu hgr hm hsd
      hinj hret hw1 hw2 hnolv (i := i) (by omega) hpe1 (hnolv (i + 1) le_rfl (by omega))
      with h | h
    · exact h
    · exact absurd h hpe2γ
  refine ⟨?_, hpe2in, hpe2γ⟩
  intro j' hj'
  by_cases hj'i : j' ≤ i
  · exact hprefix j' hj'i
  · have h1 : j' = i + 1 := by omega
    subst h1
    have e1 : 2 * (i + 1) + 1 = 2 * i + 3 := by ring
    have e2 : 2 * (i + 1) + 2 = 2 * i + 4 := by ring
    rw [e1, e2]
    exact hstep

/-- **Lemma A** (the odd corner case), conditional on the cascade and landing
hypotheses: the walk must climb the staircase all the way, and the last cell
`w_{2m-1} = uu 0` cannot be a neighbor of `rr (m-2)`. -/
lemma lemma_a_odd_of_cascade {S : Finset Cell} (hcc : ComplConnected S)
    {f g : Cell → Cell} (hf : IsTiling S f) (htf : Tasteful S f)
    (hg : IsTiling S g) (htg : Tasteful S g)
    {x y : ℤ} (hsS : (x, y) ∈ S) (hodd : Odd (x + y))
    (hmin : ∀ c ∈ S, y ≤ c.2) (hfu : f (x, y) = (x, y + 1)) (hgr : g (x, y) = (x + 1, y))
    {m : ℕ} (hm : 2 ≤ m) (hsd : (x, y) ∈ sd S f g)
    (hinj : ∀ i < 2 * m, ∀ j < 2 * m, walk (x, y) f g i = walk (x, y) f g j → i = j)
    (hret : walk (x, y) f g (2 * m) = (x, y))
    (hw1 : walk (x, y) f g 1 = po x y 0) (hw2 : walk (x, y) f g 2 = rr x y 0)
    (hwlast : walk (x, y) f g (2 * m - 1) = uu x y 0)
    (hcascade : ∀ (N' i' : ℕ), 2 * i' + 4 ≤ 2 * m - 1 →
      (∀ j' ≤ i', walk (x, y) f g (2 * j' + 1) = po x y j' ∧
        walk (x, y) f g (2 * j' + 2) = rr x y j') →
      (∀ j' ≤ N', 1 ≤ j' → pe x y j' ∉ cycSet (x, y) f g m) →
      N' ≤ i' + 1 →
      (∃ J, N' + 1 ≤ J ∧ (pe x y J ∉ S ∨ po x y J ∉ S)) → False)
    (hlanding : ∀ (N' i' : ℕ), 2 * i' + 4 ≤ 2 * m - 1 →
      (∀ j' ≤ i', walk (x, y) f g (2 * j' + 1) = po x y j' ∧
        walk (x, y) f g (2 * j' + 2) = rr x y j') →
      (∀ j' ≤ N', 1 ≤ j' → pe x y j' ∉ cycSet (x, y) f g m) →
      N' ≤ i' + 1 →
      ∀ {t k : ℕ}, 2 * i' + 5 ≤ t → t ≤ 2 * m - 1 → Odd t →
      walk (x, y) f g t = po x y k → N' + 1 ≤ k →
      lvl x y (walk (x, y) f g (t - 1)) = -1 →
      (∀ t' < t, 2 * i' + 2 ≤ t' → lvl x y (walk (x, y) f g t') < 0) → False) :
    False := by
  have hf0 : f (po x y 0) = rr x y 0 := by
    apply f_po_eq_rr hf htf hodd hsS hfu hmin 0
    · intro j hj
      have h0 : j = 0 := by omega
      subst h0
      rw [pe_zero_eq]
      exact hsS
    · intro j hj
      have h0 : j = 0 := by omega
      subst h0
      rw [po_zero_eq, ← hgr]
      exact (hg _ hsS).1
  have hprefix0 : ∀ j' ≤ 0, walk (x, y) f g (2 * j' + 1) = po x y j' ∧
      walk (x, y) f g (2 * j' + 2) = rr x y j' := by
    intro j' hj'
    have h0 : j' = 0 := by omega
    subst h0
    exact ⟨hw1, hw2⟩
  have hnolv0 : ∀ j' ≤ 0, 1 ≤ j' → pe x y j' ∉ cycSet (x, y) f g m :=
    fun j' hj' h => by omega
  -- `pe 1` is off the cycle (the `j = 1` corner case)
  have hpe1γ : pe x y 1 ∉ cycSet (x, y) f g m := by
    intro hpe1c
    have hex : ∃ t, 1 ≤ t ∧ t ≤ 2 * m - 1 ∧ lvl x y (walk (x, y) f g t) ≥ 1 := by
      rw [mem_cycSet] at hpe1c
      obtain ⟨t, htr, hte⟩ := hpe1c
      have ht2 : t < 2 * m := Finset.mem_range.mp htr
      have ht0 : t ≠ 0 := by
        intro h0
        rw [h0, walk_zero] at hte
        unfold pe at hte
        simp [Prod.ext_iff] at hte
      refine ⟨t, by omega, by omega, ?_⟩
      rw [hte, lvl_pe]
    obtain ⟨τ₀, k', jō, hτ0, hτ02, hτe, hwτ, hwτ1, hfcross, hfirst⟩ :=
      first_lvl_ge_one_visit hf hg hodd hmin hsd hw1 hex
    by_cases hm2 : m = 2
    · subst hm2
      have hτ : τ₀ = 2 := by
        rcases hτe with ⟨a, ha⟩
        omega
      rw [hτ, hw2] at hwτ
      unfold pe rr at hwτ
      simp [Prod.ext_iff] at hwτ
      omega
    · have hkγ : pe x y k' ∈ cycSet (x, y) f g m :=
        mem_cycSet.mpr ⟨τ₀, Finset.mem_range.mpr (by omega), hwτ⟩
      have hjS : po x y jō ∈ S := by
        rw [← hwτ1]
        exact (mem_sd.mp (walk_mem hf hg hsd (τ₀ - 1))).1
      have hpeN : pe x y 1 ∈ S := (mem_sd.mp (cycSet_subset_sd hf hg hsd hpe1c)).1
      by_cases hk'1 : k' ≤ 1
      · exact crossing_conflict_V hf htf hg htg hcc hsS hodd hmin hfu hgr hm hsd
          hinj hret hw1 hw2 hnolv0 hkγ hfcross hjS (by omega)
      · by_cases hj1 : jō ≤ 1
        · exact crossing_conflict_H hf htf hg htg hcc hsS hodd hmin hfu hgr hm hsd
            hinj hret hw1 hw2 hnolv0 hpeN hfcross hjS (by omega)
        · have hdef : f (po x y jō) ≠ rr x y jō := by
            rw [hfcross]
            intro hcon
            unfold pe rr at hcon
            simp [Prod.ext_iff] at hcon
            omega
          have hgap := exists_gap_of_defect hf htf hodd hsS hfu hmin jō hdef
          rcases hgap with ⟨J, hJ1, hJ2⟩ | ⟨J, hJ1, hJ2⟩
          · by_cases hJ0 : J = 0
            · subst hJ0
              exact hJ2 (by rw [pe_zero_eq]; exact hsS)
            · exact hcascade 0 0 (by omega) hprefix0 hnolv0 (by omega)
                ⟨J, by omega, Or.inl hJ2⟩
          · by_cases hJ0 : J = 0
            · subst hJ0
              exact hJ2 (by rw [po_zero_eq, ← hgr]; exact (hg _ hsS).1)
            · exact hcascade 0 0 (by omega) hprefix0 hnolv0 (by omega)
                ⟨J, by omega, Or.inr hJ2⟩
  have hpe1in : inside (x, y) f g m (pe x y 1) := by
    rcases pe_one_mem_inside_or_cyc hf hg hmin hsd hinj hm hret hw1 hw2 with h | h
    · exact h
    · exact absurd h hpe1γ
  -- the staircase induction
  have hP : ∀ n : ℕ, 2 * n + 2 ≤ 2 * m - 1 →
      (∀ j' ≤ n, walk (x, y) f g (2 * j' + 1) = po x y j' ∧
        walk (x, y) f g (2 * j' + 2) = rr x y j' ∧ f (po x y j') = rr x y j') ∧
      (∀ j' ≤ n + 1, 1 ≤ j' → inside (x, y) f g m (pe x y j') ∧
        pe x y j' ∉ cycSet (x, y) f g m) := by
    intro n
    induction n with
    | zero =>
      intro hn
      refine ⟨fun j' hj' => ?_, fun j' hj' h => ?_⟩
      · have h0 : j' = 0 := by omega
        subst h0
        exact ⟨hw1, hw2, hf0⟩
      · have h1 : j' = 1 := by omega
        subst h1
        exact ⟨hpe1in, hpe1γ⟩
    | succ n ih =>
      intro hn
      have ihr := ih (by omega)
      have hstep := lemma_a_step_of_cascade hcc hf htf hg htg hsS hodd hmin hfu hgr
        hm hsd hinj hret hw1 hw2 hwlast hcascade hlanding (i := n) (by omega) ihr.1
        (fun j' hj' h => (ihr.2 j' hj' h).2) (ihr.2 (n + 1) le_rfl (by omega)).1
      refine ⟨hstep.1, fun j' hj' h => ?_⟩
      by_cases hj'n : j' ≤ n + 1
      · exact ihr.2 j' hj'n h
      · have h1 : j' = n + 2 := by omega
        subst h1
        exact ⟨hstep.2.1, hstep.2.2⟩
  -- conclude: `w_{2m-1} = uu 0` is a neighbor of `rr (m-2)`, impossible
  have hP' := hP (m - 2) (by omega)
  have hww1 : walk (x, y) f g (2 * m - 3) = po x y (m - 2) := by
    have h1 := (hP'.1 (m - 2) le_rfl).1
    rwa [show 2 * (m - 2) + 1 = 2 * m - 3 from by omega] at h1
  have hww2 : walk (x, y) f g (2 * m - 2) = rr x y (m - 2) := by
    have h1 := (hP'.1 (m - 2) le_rfl).2.1
    rwa [show 2 * (m - 2) + 2 = 2 * m - 2 from by omega] at h1
  have hw3 : walk (x, y) f g (2 * m - 1) = g (rr x y (m - 2)) := by
    have h1 : walk (x, y) f g (2 * m - 2 + 1) = g (walk (x, y) f g (2 * m - 2)) :=
      walk_eq_g_of_even ⟨m - 1, by omega⟩
    rwa [show 2 * m - 2 + 1 = 2 * m - 1 from by omega, hww2] at h1
  have hgrr : g (rr x y (m - 2)) = uu x y 0 := by
    rw [← hw3]
    exact hwlast
  have hrrS : rr x y (m - 2) ∈ S := by
    rw [← hww2]
    exact (mem_sd.mp (walk_mem hf hg hsd (2 * m - 2))).1
  have hadj : Adjacent (rr x y (m - 2)) (uu x y 0) := by
    have h1 : Adjacent (rr x y (m - 2)) (g (rr x y (m - 2))) := (hg _ hrrS).2.2.2
    rwa [hgrr] at h1
  unfold Adjacent at hadj
  rw [show (rr x y (m - 2)).1 = x + ↑(m - 2) + 2 from rfl,
    show (rr x y (m - 2)).2 = y + ↑(m - 2) from rfl,
    show (uu x y 0).1 = x from by simp [uu],
    show (uu x y 0).2 = y + 1 from by simp [uu]] at hadj
  have e1 : x + ↑(m - 2) + 2 - x = (m : ℤ) := by
    have h1 : ((m - 2 : ℕ) : ℤ) = (m : ℤ) - 2 := by omega
    rw [h1]
    ring
  have e2 : y + ↑(m - 2) - (y + 1) = (m : ℤ) - 3 := by
    have h1 : ((m - 2 : ℕ) : ℤ) = (m : ℤ) - 2 := by omega
    rw [h1]
    ring
  rw [e1, e2] at hadj
  have hnm : ((m : ℤ)).natAbs = m := by simp
  rw [hnm] at hadj
  by_cases hm3 : m = 2
  · subst hm3
    norm_num at hadj
  · have hm4 : 3 ≤ m := by omega
    have e3 : ((m : ℤ) - 3).natAbs = m - 3 := by
      have h1 : (0 : ℤ) ≤ (m : ℤ) - 3 := by omega
      have h2 : ((m : ℤ) - 3).natAbs = ((m : ℤ) - 3).toNat := by
        cases' ((m : ℤ) - 3 : ℤ) with n n
        · rfl
        · omega
      rw [h2]
      omega
    rw [e3] at hadj
    omega

-- ============================================================
-- The landing hypothesis: climb analysis and well-founded recursion
-- ============================================================

/-- Climbing along the level-0 staircase after a down-bounce (`w_t = po k`,
`w_{t+1} = rr k`): either a defect appears at some `po (k+b')` (forcing a
gap), or the walk dives below level `-2` and lands again at some `po k'`
with `k' ≥ N+1`, past the climb.  Well-founded induction on
`2 * m - t - 2 * b - 1`, which decreases by 2 at each climb step; the west
neighbour is already visited (injectivity), the north neighbour either
continues the climb, hits the boundary (`uu 0` resp. `s`), or gives a defect,
and the east/south neighbours are dives. -/
lemma climb_or_landing {S : Finset Cell} (hcc : ComplConnected S)
    {f g : Cell → Cell} (hf : IsTiling S f) (htf : Tasteful S f)
    (hg : IsTiling S g) (htg : Tasteful S g)
    {x y : ℤ} (hsS : (x, y) ∈ S) (hodd : Odd (x + y))
    (hmin : ∀ c ∈ S, y ≤ c.2) (hfu : f (x, y) = (x, y + 1)) (hgr : g (x, y) = (x + 1, y))
    {m : ℕ} (hm : 2 ≤ m) (hsd : (x, y) ∈ sd S f g)
    (hinj : ∀ i < 2 * m, ∀ j < 2 * m, walk (x, y) f g i = walk (x, y) f g j → i = j)
    (hret : walk (x, y) f g (2 * m) = (x, y))
    (hw1 : walk (x, y) f g 1 = po x y 0) (hw2 : walk (x, y) f g 2 = rr x y 0)
    (hwlast : walk (x, y) f g (2 * m - 1) = uu x y 0)
    {N i : ℕ} (hnolv : ∀ j' ≤ N, 1 ≤ j' → pe x y j' ∉ cycSet (x, y) f g m)
    (hNi : N ≤ i + 1) (hi : 2 * i + 4 ≤ 2 * m - 1)
    (hprefix : ∀ j' ≤ i, walk (x, y) f g (2 * j' + 1) = po x y j' ∧
      walk (x, y) f g (2 * j' + 2) = rr x y j')
    {t k : ℕ} (htodd : Odd t) (htk : walk (x, y) f g t = po x y k)
    (hwt1 : walk (x, y) f g (t + 1) = rr x y k)
    (ht1 : t + 1 ≤ 2 * m - 1) (ht2 : 2 * i + 1 ≤ t) (hk : N + 1 ≤ k) :
    (∃ b', f (po x y (k + b')) ≠ rr x y (k + b')) ∨
    ∃ (b' : ℕ) (t' k' : ℕ), t + 2 * b' + 3 ≤ t' ∧ t' ≤ 2 * m - 1 ∧ Odd t' ∧
      walk (x, y) f g t' = po x y k' ∧ lvl x y (walk (x, y) f g (t' - 1)) = -1 ∧
      (∀ t'' < t', t + 2 * b' + 1 ≤ t'' → lvl x y (walk (x, y) f g t'') < 0) ∧
      N + 1 ≤ k' := by
  rcases htodd with ⟨a₀, ha₀⟩
  have hclimb : ∀ d : ℕ, ∀ b : ℕ, d = 2 * m - t - 2 * b - 1 →
      walk (x, y) f g (t + 2 * b) = po x y (k + b) →
      walk (x, y) f g (t + 2 * b + 1) = rr x y (k + b) →
      t + 2 * b + 1 ≤ 2 * m - 1 →
      (∃ b', f (po x y (k + b')) ≠ rr x y (k + b')) ∨
      ∃ (b' : ℕ) (t' k' : ℕ), t + 2 * b' + 3 ≤ t' ∧ t' ≤ 2 * m - 1 ∧ Odd t' ∧
        walk (x, y) f g t' = po x y k' ∧ lvl x y (walk (x, y) f g (t' - 1)) = -1 ∧
        (∀ t'' < t', t + 2 * b' + 1 ≤ t'' → lvl x y (walk (x, y) f g t'') < 0) ∧
        N + 1 ≤ k' := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ihd =>
      intro b hd hwb hwb1 hb
      have hwg : walk (x, y) f g (t + 2 * b + 2) = g (rr x y (k + b)) := by
        have h1 := walk_eq_g_of_even (s := (x, y)) (f := f) (g := g) (n := t + 2 * b + 1)
          ⟨a₀ + b + 1, by omega⟩
        rwa [show t + 2 * b + 1 + 1 = t + 2 * b + 2 from by omega, hwb1] at h1
      have hrrS : rr x y (k + b) ∈ S := by
        rw [← hwb1]
        exact (mem_sd.mp (walk_mem hf hg hsd _)).1
      have hadj : Adjacent (rr x y (k + b)) (g (rr x y (k + b))) := (hg _ hrrS).2.2.2
      have hdive : lvl x y (walk (x, y) f g (t + 2 * b + 2)) ≤ -2 →
          (∃ b', f (po x y (k + b')) ≠ rr x y (k + b')) ∨
          ∃ (b' : ℕ) (t' k' : ℕ), t + 2 * b' + 3 ≤ t' ∧ t' ≤ 2 * m - 1 ∧ Odd t' ∧
            walk (x, y) f g t' = po x y k' ∧ lvl x y (walk (x, y) f g (t' - 1)) = -1 ∧
            (∀ t'' < t', t + 2 * b' + 1 ≤ t'' → lvl x y (walk (x, y) f g t'') < 0) ∧
            N + 1 ≤ k' := by
        intro hlv
        have hrr1 : lvl x y (walk (x, y) f g (t + 2 * b + 1)) = -1 := by
          rw [hwb1, lvl_rr]
        obtain ⟨t', k', ht'0, ht'1, ht'lvl, htk', ht'prev, ht'min⟩ :=
          return_landing2 hf hg hmin hsd (a := t + 2 * b + 1) hb hwlast hrr1 (by omega)
        have ht'odd : Odd t' := Nat.odd_iff.mpr (po_visit_odd hf hg hodd hsd htk')
        have ht'3 : t + 2 * b + 3 ≤ t' := by
          have h1 : t' ≠ t + 2 * b + 1 := by
            intro h1
            rw [h1, hrr1] at ht'lvl
            omega
          have h2 : t' ≠ t + 2 * b + 2 := by
            intro h2
            rw [h2] at ht'lvl
            omega
          omega
        have hk' : N + 1 ≤ k' := by
          by_contra hcon
          push_neg at hcon
          by_cases hk'i : k' ≤ i
          · have h2 := hinj t' (by omega) (2 * k' + 1) (by omega) (by
              rw [htk', (hprefix k' hk'i).1])
            omega
          · have hN' : N = i + 1 := by omega
            have hk'' : k' = i + 1 := by omega
            subst hk''
            have hchain := pe_chain_mem_S hcc hf htf hg htg hsS hodd hmin hfu hgr
              hm hsd hinj hret hw1 hw2 hnolv (j := N) (by omega) le_rfl
            have hpoS' : po x y (i + 1) ∈ S := by
              rw [← htk']
              exact (mem_sd.mp (walk_mem hf hg hsd t')).1
            have hmem2 : ∀ j' ≤ i + 1, po x y j' ∈ S := by
              intro j' hj'
              by_cases h3 : j' ≤ i
              · rcases Nat.eq_zero_or_pos j' with hj0 | hj0
                · subst hj0
                  rw [show po x y 0 = (x + 1, y) from by unfold po; simp, ← hgr]
                  exact (hg _ hsS).1
                · exact hchain.2 j' (by omega) hj0
              · have h3 : j' = i + 1 := by omega
                rw [h3]
                exact hpoS'
            have hmemV2 : ∀ j' ≤ i + 1, pe x y j' ∈ S := by
              intro j' hj'
              rcases Nat.eq_zero_or_pos j' with hj0 | hj0
              · subst hj0
                rw [show pe x y 0 = (x, y) from by unfold pe; simp]
                exact hsS
              · exact hchain.1 j' (by omega) hj0
            have hmemV1 : ∀ j' < i + 1, po x y j' ∈ S := fun j' hj' => hmem2 j' (by omega)
            have hmemV3 : ∀ j' ≤ i, pe x y j' ∈ S := fun j' hj' => hmemV2 j' (by omega)
            obtain ⟨-, -, hb2⟩ := bounce_at_return hf hg htf hsd hinj hm hret hsS
              hodd hfu hmin htk' ht'odd (by omega) (by omega) ht'prev hmem2 hmemV2
              hmemV1 hmemV3
            have h3 := ht'min (t' - 2) (by omega) (by omega)
            rw [hb2, lvl_po] at h3
            omega
        exact Or.inr ⟨b, t', k', ht'3, ht'1, ht'odd, htk', ht'prev, ht'min, hk'⟩
      rcases adjacent_cases hadj with h3 | h3 | h3 | h3
      · -- east: dive
        apply hdive
        have hlv : lvl x y ((rr x y (k + b)).1 + 1, (rr x y (k + b)).2) = -2 := by
          unfold lvl rr
          simp
          ring
        rw [hwg, h3, hlv]
      · -- west `po (k+b)`: already visited
        exfalso
        have hpo : g (rr x y (k + b)) = po x y (k + b) := by
          rw [h3]
          unfold po rr
          ext <;> simp <;> ring
        rw [hpo] at hwg
        by_cases htop : t + 2 * b + 2 = 2 * m
        · rw [htop, hret] at hwg
          unfold po at hwg
          simp [Prod.ext_iff] at hwg
          omega
        · have h1 := hinj (t + 2 * b + 2) (by omega) (t + 2 * b) (by omega) (by
            rw [hwg, hwb])
          omega
      · -- north `po (k+b+1)`: continue, defect, or boundary
        have hpo : g (rr x y (k + b)) = po x y (k + b + 1) := by
          rw [h3]
          unfold po rr
          ext <;> simp <;> ring
        rw [hpo] at hwg
        by_cases htop1 : t + 2 * b + 2 = 2 * m - 1
        · exfalso
          rw [htop1, hwlast] at hwg
          unfold po uu at hwg
          simp [Prod.ext_iff] at hwg
          omega
        · by_cases htop2 : t + 2 * b + 2 = 2 * m
          · exfalso
            rw [htop2, hret] at hwg
            unfold po at hwg
            simp [Prod.ext_iff] at hwg
            omega
          · have hw3 : walk (x, y) f g (t + 2 * b + 3) = f (po x y (k + b + 1)) := by
              have h1 := walk_eq_f_of_odd (s := (x, y)) (f := f) (g := g)
                (n := t + 2 * b + 2) ⟨a₀ + b + 1, by omega⟩
              rwa [show t + 2 * b + 2 + 1 = t + 2 * b + 3 from by omega, hwg] at h1
            by_cases hfb : f (po x y (k + b + 1)) = rr x y (k + b + 1)
            · have hwb' : walk (x, y) f g (t + 2 * (b + 1)) = po x y (k + (b + 1)) := by
                have h4 : t + 2 * (b + 1) = t + 2 * b + 2 := by ring
                rw [h4]
                exact hwg
              have hwb1' : walk (x, y) f g (t + 2 * (b + 1) + 1) = rr x y (k + (b + 1)) := by
                have h4 : t + 2 * (b + 1) + 1 = t + 2 * b + 3 := by ring
                rw [h4]
                exact hw3.trans hfb
              exact ihd (2 * m - t - 2 * (b + 1) - 1) (by omega) (b + 1) rfl hwb' hwb1'
                (by omega)
            · exact Or.inl ⟨b + 1, hfb⟩
      · -- south: dive
        apply hdive
        have hlv : lvl x y ((rr x y (k + b)).1, (rr x y (k + b)).2 - 1) = -2 := by
          unfold lvl rr
          simp
          ring
        rw [hwg, h3, hlv]
  have h00 : walk (x, y) f g (t + 2 * 0) = po x y (k + 0) := by
    simpa using htk
  have h01 : walk (x, y) f g (t + 2 * 0 + 1) = rr x y (k + 0) := by
    simpa using hwt1
  exact hclimb (2 * m - t - 1) 0 rfl h00 h01 (by omega)

/-- A landing at `po k` with `k ≥ N + 1` is impossible (given the cascade
hypothesis).  Well-founded recursion on `2 * m - t`: the `rr k` case and the
`f`-entry subcases give a defect, hence a gap, hence the cascade; the
down-bounce case climbs the staircase (`climb_or_landing`) and either gives a
defect or lands again strictly later. -/
lemma landing_absurd {S : Finset Cell} (hcc : ComplConnected S)
    {f g : Cell → Cell} (hf : IsTiling S f) (htf : Tasteful S f)
    (hg : IsTiling S g) (htg : Tasteful S g)
    {x y : ℤ} (hsS : (x, y) ∈ S) (hodd : Odd (x + y))
    (hmin : ∀ c ∈ S, y ≤ c.2) (hfu : f (x, y) = (x, y + 1)) (hgr : g (x, y) = (x + 1, y))
    {m : ℕ} (hm : 2 ≤ m) (hsd : (x, y) ∈ sd S f g)
    (hinj : ∀ i < 2 * m, ∀ j < 2 * m, walk (x, y) f g i = walk (x, y) f g j → i = j)
    (hret : walk (x, y) f g (2 * m) = (x, y))
    (hw1 : walk (x, y) f g 1 = po x y 0) (hw2 : walk (x, y) f g 2 = rr x y 0)
    (hwlast : walk (x, y) f g (2 * m - 1) = uu x y 0)
    (hcascade : ∀ (N' i' : ℕ), 2 * i' + 4 ≤ 2 * m - 1 →
      (∀ j' ≤ i', walk (x, y) f g (2 * j' + 1) = po x y j' ∧
        walk (x, y) f g (2 * j' + 2) = rr x y j') →
      (∀ j' ≤ N', 1 ≤ j' → pe x y j' ∉ cycSet (x, y) f g m) →
      N' ≤ i' + 1 →
      (∃ J, N' + 1 ≤ J ∧ (pe x y J ∉ S ∨ po x y J ∉ S)) → False)
    {N i : ℕ} (hi : 2 * i + 4 ≤ 2 * m - 1)
    (hprefix : ∀ j' ≤ i, walk (x, y) f g (2 * j' + 1) = po x y j' ∧
      walk (x, y) f g (2 * j' + 2) = rr x y j')
    (hnolv : ∀ j' ≤ N, 1 ≤ j' → pe x y j' ∉ cycSet (x, y) f g m)
    (hNi : N ≤ i + 1) :
    ∀ d : ℕ, ∀ {a t k : ℕ}, 2 * i + 2 ≤ a → a ≤ t - 2 → t = 2 * m - d →
      t ≤ 2 * m - 1 → Odd t → walk (x, y) f g t = po x y k →
      lvl x y (walk (x, y) f g (t - 1)) = -1 →
      (∀ t' < t, a ≤ t' → lvl x y (walk (x, y) f g t') < 0) → N + 1 ≤ k → False := by
  have hmem_pe : ∀ J ≤ N, 1 ≤ J → pe x y J ∈ S := by
    by_cases hN : 1 ≤ N
    · exact (pe_chain_mem_S hcc hf htf hg htg hsS hodd hmin hfu hgr hm hsd hinj
        hret hw1 hw2 hnolv (j := N) hN le_rfl).1
    · intro J hJ1 hJ2
      omega
  have hmem_po : ∀ J ≤ N, 1 ≤ J → po x y J ∈ S := by
    by_cases hN : 1 ≤ N
    · exact (pe_chain_mem_S hcc hf htf hg htg hsS hodd hmin hfu hgr hm hsd hinj
        hret hw1 hw2 hnolv (j := N) hN le_rfl).2
    · intro J hJ1 hJ2
      omega
  have gap_absurd : ∀ {ℓ : ℕ}, (∃ j'' ≤ ℓ, pe x y j'' ∉ S) ∨
      (∃ j'' ≤ ℓ, po x y j'' ∉ S) → False := by
    intro ℓ hgap
    rcases hgap with ⟨J, hJ1, hJ2⟩ | ⟨J, hJ1, hJ2⟩
    · by_cases hJN : J ≤ N
      · rcases Nat.eq_zero_or_pos J with hJ0 | hJ0
        · subst hJ0
          exact hJ2 (by rw [pe_zero_eq]; exact hsS)
        · exact hJ2 (hmem_pe J hJN hJ0)
      · exact hcascade N i hi hprefix hnolv hNi ⟨J, by omega, Or.inl hJ2⟩
    · by_cases hJN : J ≤ N
      · rcases Nat.eq_zero_or_pos J with hJ0 | hJ0
        · subst hJ0
          exact hJ2 (by rw [po_zero_eq, ← hgr]; exact (hg _ hsS).1)
        · exact hJ2 (hmem_po J hJN hJ0)
      · exact hcascade N i hi hprefix hnolv hNi ⟨J, by omega, Or.inr hJ2⟩
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro a t k ha2 hat htd ht1 htodd htk htprev htmin hk
    have hg1 : g (po x y k) = walk (x, y) f g (t - 1) := by
      have h2 : walk (x, y) f g (t - 1 + 1) = g (walk (x, y) f g (t - 1)) := by
        have h2' : walk (x, y) f g (t - 1 + 1) =
            (if Even (t - 1) then g else f) (walk (x, y) f g (t - 1)) :=
          walk_succ (x, y) (t - 1)
        have ht1even : Even (t - 1) := by
          rcases htodd with ⟨a', ha'⟩
          exact ⟨a', by omega⟩
        rwa [if_pos ht1even] at h2'
      rw [show t - 1 + 1 = t by omega, htk] at h2
      have h3 : walk (x, y) f g (t - 1) ∈ S := (mem_sd.mp (walk_mem hf hg hsd (t - 1))).1
      have h4 := (hg _ h3).2.1
      rw [h2.symm] at h4
      exact h4
    have hk1 : 1 ≤ k := by omega
    have hnb := po_lvl_neg_one_neighbors hk1 (c := po x y k) rfl (by
      have h5 := walk_succ_adj hf hg hsd (t - 1)
      rw [show t - 1 + 1 = t by omega, htk] at h5
      exact adjacent_comm h5) htprev
    have hpsd : po x y k ∈ sd S f g := by
      rw [← htk]
      exact walk_mem hf hg hsd t
    have hpoS : po x y k ∈ S := (mem_sd.mp hpsd).1
    have hfne := (mem_sd.mp hpsd).2
    rcases hnb with hw1' | hw1'
    · -- `g (po k) = rr k`: defect at `k`
      rw [hw1'] at hg1
      rw [hg1] at hfne
      exact gap_absurd (exists_gap_of_defect hf htf hodd hsS hfu hmin k hfne)
    · -- `g (po k) = rr (k-1)`: analyse `f (po k)`
      rw [hw1'] at hg1
      rw [hg1] at hfne
      have hfadj : Adjacent (po x y k) (f (po x y k)) := (hf _ hpoS).2.2.2
      rcases adjacent_cases hfadj with h3 | h3 | h3 | h3
      · -- `f (po k) = rr k`: down-bounce, climb
        have hfk : f (po x y k) = rr x y k := by
          rw [h3]
          unfold po rr
          ext <;> simp <;> ring
        have hwt1 : walk (x, y) f g (t + 1) = rr x y k := by
          have h1 : walk (x, y) f g (t + 1) = f (walk (x, y) f g t) :=
            walk_eq_f_of_odd htodd
          rwa [htk, hfk] at h1
        have httop : t + 1 ≤ 2 * m - 1 := by
          by_contra hcon
          push_neg at hcon
          have h2 : t = 2 * m - 1 := by omega
          rw [h2, hwlast] at htk
          unfold po uu at htk
          simp [Prod.ext_iff] at htk
          omega
        have ht2 : 2 * i + 1 ≤ t := by omega
        obtain hB | ⟨b', t', k', ht'3, ht'1, ht'odd, htk', ht'prev, ht'min, hk'⟩ :=
          climb_or_landing hcc hf htf hg htg hsS hodd hmin hfu hgr hm hsd hinj hret
            hw1 hw2 hwlast hnolv hNi hi hprefix htodd htk hwt1 httop ht2 hk
        · obtain ⟨b'', hdef⟩ := hB
          exact gap_absurd (exists_gap_of_defect hf htf hodd hsS hfu hmin (k + b'') hdef)
        · exact ih (2 * m - t') (by omega) (a := t + 2 * b' + 1) (by omega) (by omega)
            (by omega) ht'1 ht'odd htk' ht'prev ht'min hk'
      · -- `f (po k) = pe k`: defect
        have hfk : f (po x y k) = pe x y k := by
          rw [h3]
          unfold po pe
          ext <;> simp <;> ring
        have hdef : f (po x y k) ≠ rr x y k := by
          rw [hfk]
          intro hcon
          unfold pe rr at hcon
          simp [Prod.ext_iff] at hcon
        exact gap_absurd (exists_gap_of_defect hf htf hodd hsS hfu hmin k hdef)
      · -- `f (po k) = pe (k+1)`: defect
        have hfk : f (po x y k) = pe x y (k + 1) := by
          rw [h3]
          unfold po pe
          ext <;> simp <;> ring
        have hdef : f (po x y k) ≠ rr x y k := by
          rw [hfk]
          intro hcon
          unfold pe rr at hcon
          simp [Prod.ext_iff] at hcon
        exact gap_absurd (exists_gap_of_defect hf htf hodd hsS hfu hmin k hdef)
      · -- `f (po k) = rr (k-1)`: excluded by `sd`
        have hfk : f (po x y k) = rr x y (k - 1) := by
          rw [h3]
          unfold po rr
          ext <;> simp <;> omega
        exact hfne hfk

-- ============================================================
-- The walk endpoints (setup for the induction frame)
-- ============================================================

/-- The first step of the walk is `po 0 = (x+1, y)` (the `g`-image of `s`). -/
lemma walk_one_eq {f g : Cell → Cell} {x y : ℤ}
    (hgr : g (x, y) = (x + 1, y)) :
    walk (x, y) f g 1 = po x y 0 := by
  have h1 : walk (x, y) f g (0 + 1) = g (walk (x, y) f g 0) :=
    walk_eq_g_of_even ⟨0, rfl⟩
  rw [walk_zero, hgr] at h1
  rw [show (1 : ℕ) = 0 + 1 from rfl, h1, po_zero_eq]

/-- The second step of the walk is `rr 0 = (x+2, y)` (the forced horizontal
domino at the corner). -/
lemma walk_two_eq {S : Finset Cell} {f : Cell → Cell} (hf : IsTiling S f)
    (htf : Tasteful S f) {g : Cell → Cell} (hg : IsTiling S g) {x y : ℤ}
    (hsS : (x, y) ∈ S) (hodd : Odd (x + y)) (hmin : ∀ c ∈ S, y ≤ c.2)
    (hfu : f (x, y) = (x, y + 1)) (hgr : g (x, y) = (x + 1, y)) :
    walk (x, y) f g 2 = rr x y 0 := by
  have hf0 : f (po x y 0) = rr x y 0 := by
    apply f_po_eq_rr hf htf hodd hsS hfu hmin 0
    · intro j hj
      have h0 : j = 0 := by omega
      subst h0
      rw [pe_zero_eq]
      exact hsS
    · intro j hj
      have h0 : j = 0 := by omega
      subst h0
      rw [po_zero_eq, ← hgr]
      exact (hg _ hsS).1
  have h1 : walk (x, y) f g (1 + 1) = f (walk (x, y) f g 1) :=
    walk_eq_f_of_odd ⟨0, rfl⟩
  rw [walk_one_eq hgr, hf0] at h1
  have h2 : (1 : ℕ) + 1 = 2 := rfl
  rw [← h2]
  exact h1

/-- The last cell of the walk is `uu 0 = (x, y+1)` (the `f`-preimage of `s`). -/
lemma walk_last_eq {S : Finset Cell} {f g : Cell → Cell} {m : ℕ} {x y : ℤ}
    (hf : IsTiling S f) (hg : IsTiling S g)
    (hsd : (x, y) ∈ sd S f g) (hm : 2 ≤ m)
    (hret : walk (x, y) f g (2 * m) = (x, y)) (hfu : f (x, y) = (x, y + 1)) :
    walk (x, y) f g (2 * m - 1) = uu x y 0 := by
  have h1 : walk (x, y) f g (2 * m - 1 + 1) = f (walk (x, y) f g (2 * m - 1)) :=
    walk_eq_f_of_odd ⟨m - 1, by omega⟩
  rw [show 2 * m - 1 + 1 = 2 * m from by omega, hret] at h1
  have h2 : walk (x, y) f g (2 * m - 1) ∈ S :=
    (mem_sd.mp (walk_mem hf hg hsd (2 * m - 1))).1
  have h3 := (hf _ h2).2.1
  rw [← h1] at h3
  rw [← h3, hfu]
  unfold uu
  simp

-- ============================================================
-- The induction frame: the disagreement set and erasing the corner domino
-- ============================================================

/-- `CellPath` is monotone in the predicate. -/
lemma cellpath_of_imp {P Q : Cell → Prop} {c c' : Cell} (h : CellPath P c c')
    (hpq : ∀ d, P d → Q d) : CellPath Q c c' := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih =>
    apply Relation.ReflTransGen.tail ih
    obtain ⟨ha', hb', hab'⟩ := hbc
    exact ⟨hpq _ ha', hpq _ hb', hab'⟩

/-- `CellPath` is symmetric (adjacency is symmetric). -/
lemma cellpath_symm {P : Cell → Prop} {c c' : Cell} (h : CellPath P c c') :
    CellPath P c' c := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih =>
    obtain ⟨ha', hb', hab'⟩ := hbc
    exact Relation.ReflTransGen.head ⟨hb', ha', adjacent_comm hab'⟩ ih

/-- The disagreement set is symmetric in the two tilings. -/
lemma sd_symm (S : Finset Cell) (f g : Cell → Cell) : sd S f g = sd S g f := by
  unfold sd
  refine Finset.filter_congr fun c _ => ?_
  simp only [ne_eq, eq_comm]

/-- The restriction of a tiling to the region with the domino `{s, f s}`
removed is still a tiling. -/
lemma IsTiling.erase_pair {S : Finset Cell} {f : Cell → Cell} (hf : IsTiling S f)
    {s : Cell} (hs : s ∈ S) :
    IsTiling ((S.erase (f s)).erase s) f := by
  intro c hc
  have hcS : c ∈ S := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hc)
  obtain ⟨h1, h2, h3, h4⟩ := hf c hcS
  refine ⟨?_, h2, h3, h4⟩
  simp only [Finset.mem_erase, ne_eq]
  refine ⟨?_, ?_, h1⟩
  · -- `f c ≠ s`, else `c = f s` is erased
    intro hcon
    have h5 : f s = c := by
      have h6 := (hf c hcS).2.1
      rw [hcon] at h6
      exact h6
    have hc2 : c = f s := h5.symm
    have h7 : c ∉ S.erase (f s) := by
      rw [hc2]
      simp [Finset.mem_erase]
    exact h7 (Finset.mem_of_mem_erase hc)
  · -- `f c ≠ f s`, else `c = s` is erased
    intro hcon
    have h5 : c = s := by
      have h6 := congrArg f hcon
      rwa [(hf c hcS).2.1, (hf s hs).2.1] at h6
    rw [h5] at hc
    simp [Finset.mem_erase] at hc

/-- `Tasteful` restricts to subsets. -/
lemma Tasteful.subset {S T : Finset Cell} {f : Cell → Cell} (ht : Tasteful S f)
    (hsub : T ⊆ S) : Tasteful T f := by
  obtain ⟨h1, h2⟩ := ht
  exact ⟨fun i j hi1 hi2 hpar hcon => h1 i j (hsub hi1) (hsub hi2) hpar hcon,
    fun i j hi1 hi2 hpar hcon => h2 i j (hsub hi1) (hsub hi2) hpar hcon⟩

/-- Removing the corner domino `{s, f s}` preserves hole-freeness, provided
the cell `z` just outside the corner is not in `S`: every outside cell links
to `z` (through the old complement, or directly via `s — z` and `t — s — z`),
and the complement of a subset of `S` stays inside the old complement. -/
lemma compl_connected_erase_corner {S : Finset Cell} (hcc : ComplConnected S)
    {s t z : Cell} (hst : Adjacent s t) (hsz : Adjacent s z)
    (hzS : z ∉ S) (_hsS : s ∈ S) (_htS : t ∈ S) :
    ComplConnected ((S.erase t).erase s) := by
  classical
  have hsz' : z ∉ (S.erase t).erase s := by
    simp only [Finset.mem_erase, ne_eq, not_and, not_not]
    exact fun _ _ => hzS
  have hsS' : s ∉ (S.erase t).erase s := by
    simp [Finset.mem_erase]
  have htS' : t ∉ (S.erase t).erase s := by
    simp [Finset.mem_erase]
  have key : ∀ c ∉ (S.erase t).erase s, CellPath (· ∉ (S.erase t).erase s) c z := by
    intro c hc
    by_cases hcs : c = s
    · subst hcs
      exact Relation.ReflTransGen.single ⟨hc, hsz', hsz⟩
    · by_cases hct : c = t
      · subst hct
        exact Relation.ReflTransGen.tail
          (Relation.ReflTransGen.single ⟨hc, hsS', adjacent_comm hst⟩)
          ⟨hsS', hsz', hsz⟩
      · have hcS : c ∉ S := by
          intro hcon
          have h1 : c ∈ (S.erase t).erase s := by
            simp only [Finset.mem_erase, ne_eq]
            exact ⟨hcs, hct, hcon⟩
          exact hc h1
        have hpath := hcc c hcS z hzS
        exact cellpath_of_imp hpath (fun d hd => by
          simp only [Finset.mem_erase, ne_eq, not_and, not_not]
          exact fun _ _ => hd)
  intro c hc c' hc'
  exact Relation.ReflTransGen.trans (key c hc) (cellpath_symm (key c' hc'))

/-- Any nonempty region has a lower-left corner: a cell of minimal `y`,
leftmost among such cells. -/
lemma exists_corner {S : Finset Cell} (hne : S.Nonempty) :
    ∃ s ∈ S, (∀ c ∈ S, s.2 ≤ c.2) ∧ (∀ c ∈ S, c.2 = s.2 → s.1 ≤ c.1) := by
  obtain ⟨s, hs, hmin⟩ := S.exists_min_image Prod.snd hne
  have hne2 : (S.filter fun c => c.2 = s.2).Nonempty :=
    ⟨s, Finset.mem_filter.mpr ⟨hs, rfl⟩⟩
  obtain ⟨s', hs', hmin2⟩ := (S.filter fun c => c.2 = s.2).exists_min_image Prod.fst hne2
  have hs2 : s'.2 = s.2 := (Finset.mem_filter.mp hs').2
  refine ⟨s', (Finset.mem_filter.mp hs').1, fun c hc => by rw [hs2]; exact hmin c hc,
    fun c hc hcy => hmin2 c (Finset.mem_filter.mpr ⟨hc, by rw [hcy, hs2]⟩)⟩

-- ============================================================
-- The induction frame: uniqueness by strong induction on the region
-- ============================================================

/-- Uniqueness of tasteful tilings by strong induction on the size of the
region, conditional on the cascade lemma (`hcascade`, the content of
`cascade_absurd`) and the even-corner lemma (`heven`).  The corner cell's
partner is right or up; if `f` and `g` disagree there, Lemma A (odd corner,
via `lemma_a_odd_of_cascade`, or its swapped instance) resp. `heven` (even
corner) gives a contradiction.  Otherwise the corner domino is erased and
the induction hypothesis applies to the smaller region. -/
lemma usa2009_p3_aux
    (hcascade : ∀ {S : Finset Cell} {f g : Cell → Cell} (hcc : ComplConnected S)
      (hf : IsTiling S f) (htf : Tasteful S f) (hg : IsTiling S g) (htg : Tasteful S g)
      {x y : ℤ} (hsS : (x, y) ∈ S) (hodd : Odd (x + y)) (hmin : ∀ c ∈ S, y ≤ c.2)
      (hfu : f (x, y) = (x, y + 1)) (hgr : g (x, y) = (x + 1, y))
      {m : ℕ} (hm : 2 ≤ m) (hsd : (x, y) ∈ sd S f g)
      (hinj : ∀ i < 2 * m, ∀ j < 2 * m, walk (x, y) f g i = walk (x, y) f g j → i = j)
      (hret : walk (x, y) f g (2 * m) = (x, y))
      (hw1 : walk (x, y) f g 1 = po x y 0) (hw2 : walk (x, y) f g 2 = rr x y 0)
      (hwlast : walk (x, y) f g (2 * m - 1) = uu x y 0)
      {N i : ℕ} (hi : 2 * i + 4 ≤ 2 * m - 1)
      (hprefix : ∀ j' ≤ i, walk (x, y) f g (2 * j' + 1) = po x y j' ∧
        walk (x, y) f g (2 * j' + 2) = rr x y j')
      (hnolv : ∀ j' ≤ N, 1 ≤ j' → pe x y j' ∉ cycSet (x, y) f g m)
      (hNi : N ≤ i + 1)
      (hgap : ∃ J, N + 1 ≤ J ∧ (pe x y J ∉ S ∨ po x y J ∉ S)), False)
    (heven : ∀ (S : Finset Cell) (f g : Cell → Cell), IsTiling S f → IsTiling S g →
      Tasteful S f → Tasteful S g → ComplConnected S →
      ∀ (x y : ℤ), Even (x + y) → (x, y) ∈ S → (∀ c ∈ S, y ≤ c.2) →
      (∀ c ∈ S, c.2 = y → x ≤ c.1) → f (x, y) = g (x, y)) :
    ∀ n : ℕ, ∀ S : Finset Cell, S.card = n → ComplConnected S →
    ∀ f g : Cell → Cell, IsTiling S f → IsTiling S g → Tasteful S f → Tasteful S g →
    ∀ c ∈ S, f c = g c := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hcard hcc f g hf hg htf htg c hc
    by_cases hne : S.Nonempty
    swap
    · simp [Finset.not_nonempty_iff_eq_empty.mp hne] at hc
    obtain ⟨s, hs, hmin, hx⟩ := exists_corner hne
    obtain ⟨x, y⟩ := s
    -- the corner partner is right or up
    have hdir : ∀ (h : Cell → Cell) (hh : IsTiling S h),
        h (x, y) = (x + 1, y) ∨ h (x, y) = (x, y + 1) := by
      intro h hh
      have hadj : Adjacent (x, y) (h (x, y)) := (hh _ hs).2.2.2
      have hmem : h (x, y) ∈ S := (hh _ hs).1
      rcases adjacent_cases hadj with h1 | h1 | h1 | h1
      · left
        exact h1
      · exfalso
        have h2 : (x - 1, y) ∈ S := by rw [← h1]; exact hmem
        have h3 := hx _ h2 rfl
        simp at h3
      · right
        exact h1
      · exfalso
        have h2 : (x, y - 1) ∈ S := by rw [← h1]; exact hmem
        have h3 := hmin _ h2
        simp at h3
    by_cases hfg : f (x, y) = g (x, y)
    · -- erase the corner domino and apply the induction hypothesis
      have hf' : IsTiling ((S.erase (f (x, y))).erase (x, y)) f := hf.erase_pair hs
      have hg0 : IsTiling ((S.erase (g (x, y))).erase (x, y)) g := hg.erase_pair hs
      rw [← hfg] at hg0
      have hsub : (S.erase (f (x, y))).erase (x, y) ⊆ S := fun c' hc' =>
        Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hc')
      have htf' := htf.subset hsub
      have htg' := htg.subset hsub
      have hzS : (x - 1, y) ∉ S := by
        intro hcon
        have h3 := hx _ hcon rfl
        simp at h3
      have hst : Adjacent (x, y) (f (x, y)) := (hf _ hs).2.2.2
      have hsz : Adjacent (x, y) (x - 1, y) := by
        unfold Adjacent
        simp
      have hcc' : ComplConnected ((S.erase (f (x, y))).erase (x, y)) :=
        compl_connected_erase_corner hcc hst hsz hzS hs (hf _ hs).1
      have h2card : 2 ≤ S.card := by
        have h4 : ({(x, y), f (x, y)} : Finset Cell) ⊆ S := by
          intro c' hc'
          simp only [Finset.mem_insert, Finset.mem_singleton] at hc'
          rcases hc' with rfl | rfl
          · exact hs
          · exact (hf _ hs).1
        have h5 : ({(x, y), f (x, y)} : Finset Cell).card = 2 := by
          rw [Finset.card_insert_of_notMem (by
            intro hcon
            rw [Finset.mem_singleton] at hcon
            exact (hf _ hs).2.2.1 hcon.symm), Finset.card_singleton]
        have h6 := Finset.card_le_card h4
        rw [h5] at h6
        exact h6
      have hcard' : ((S.erase (f (x, y))).erase (x, y)).card = n - 2 := by
        have h1 : (S.erase (f (x, y))).card = n - 1 := by
          rw [Finset.card_erase_of_mem (hf _ hs).1, hcard]
        have h2 : (x, y) ∈ S.erase (f (x, y)) := by
          simp only [Finset.mem_erase, ne_eq]
          exact ⟨(hf _ hs).2.2.1.symm, hs⟩
        calc ((S.erase (f (x, y))).erase (x, y)).card = (S.erase (f (x, y))).card - 1 :=
              Finset.card_erase_of_mem h2
          _ = n - 1 - 1 := by rw [h1]
          _ = n - 2 := by omega
      have key : ∀ c' ∈ (S.erase (f (x, y))).erase (x, y), f c' = g c' := by
        have hle : n - 2 < n := by omega
        exact ih (n - 2) hle _ hcard' hcc' f g hf' hg0 htf' htg'
      by_cases h1 : c = (x, y)
      · rw [h1]
        exact hfg
      · by_cases h2 : c = f (x, y)
        · rw [h2]
          have e1 := (hf _ hs).2.1
          have e2 : g (f (x, y)) = (x, y) := by
            rw [hfg]
            exact (hg _ hs).2.1
          rw [e1, e2]
        · have h3 : c ∈ (S.erase (f (x, y))).erase (x, y) := by
            simp only [Finset.mem_erase, ne_eq]
            exact ⟨h1, h2, hc⟩
          exact key c h3
    · -- `f s ≠ g s`: the Lemma A family
      rcases hdir f hf with hfr | hfu'
      · rcases hdir g hg with hgr' | hgu
        · exact absurd (hfr.trans hgr'.symm) hfg
        · -- `f` right, `g` up: the swapped Lemma A
          exfalso
          by_cases hodd : Odd (x + y)
          · have hsd : (x, y) ∈ sd S g f := by
              rw [mem_sd]
              exact ⟨hs, by rw [hgu, hfr]; intro hcon; simp [Prod.ext_iff] at hcon⟩
            obtain ⟨m, hm, hret, hinj⟩ := exists_cycle_data hg hf hsd
            have hw1 : walk (x, y) g f 1 = po x y 0 := walk_one_eq hfr
            have hw2 := walk_two_eq hg htg hf hs hodd hmin hgu hfr
            have hwlast := walk_last_eq hg hf hsd hm hret hgu
            have hland : ∀ (N' i' : ℕ), 2 * i' + 4 ≤ 2 * m - 1 →
                (∀ j' ≤ i', walk (x, y) g f (2 * j' + 1) = po x y j' ∧
                  walk (x, y) g f (2 * j' + 2) = rr x y j') →
                (∀ j' ≤ N', 1 ≤ j' → pe x y j' ∉ cycSet (x, y) g f m) →
                N' ≤ i' + 1 →
                ∀ {t k : ℕ}, 2 * i' + 5 ≤ t → t ≤ 2 * m - 1 → Odd t →
                walk (x, y) g f t = po x y k → N' + 1 ≤ k →
                lvl x y (walk (x, y) g f (t - 1)) = -1 →
                (∀ t' < t, 2 * i' + 2 ≤ t' → lvl x y (walk (x, y) g f t') < 0) →
                False := by
              intro N' i' hi' hprefix' hnolv' hNi' t k ht5 ht1 htodd htk hk htprev htmin
              exact landing_absurd hcc hg htg hf htf hs hodd hmin hgu hfr hm hsd hinj
                hret hw1 hw2 hwlast
                (fun N'' i'' hi'' hprefix'' hnolv'' hNi'' hgap =>
                  hcascade hcc hg htg hf htf hs hodd hmin hgu hfr hm hsd hinj hret hw1
                    hw2 hwlast hi'' hprefix'' hnolv'' hNi'' hgap)
                hi' hprefix' hnolv' hNi' (2 * m - t)
                (a := 2 * i' + 2) le_rfl (by omega) (by omega) ht1 htodd htk htprev htmin hk
            exact lemma_a_odd_of_cascade hcc hg htg hf htf hs hodd hmin hgu hfr hm hsd
              hinj hret hw1 hw2 hwlast
              (fun N'' i'' hi'' hprefix'' hnolv'' hNi'' hgap =>
                hcascade hcc hg htg hf htf hs hodd hmin hgu hfr hm hsd hinj hret hw1
                  hw2 hwlast hi'' hprefix'' hnolv'' hNi'' hgap)
              hland
          · have hev : Even (x + y) := by
              rcases Int.even_or_odd (x + y) with h | h
              · exact h
              · exact absurd h hodd
            exact hfg (heven S f g hf hg htf htg hcc x y hev hs hmin hx)
      · rcases hdir g hg with hgr' | hgu
        · -- `f` up, `g` right: Lemma A (odd corner) or `heven` (even corner)
          exfalso
          by_cases hodd : Odd (x + y)
          · have hsd : (x, y) ∈ sd S f g := by
              rw [mem_sd]
              exact ⟨hs, by rw [hfu', hgr']; intro hcon; simp [Prod.ext_iff] at hcon⟩
            obtain ⟨m, hm, hret, hinj⟩ := exists_cycle_data hf hg hsd
            have hw1 : walk (x, y) f g 1 = po x y 0 := walk_one_eq hgr'
            have hw2 := walk_two_eq hf htf hg hs hodd hmin hfu' hgr'
            have hwlast := walk_last_eq hf hg hsd hm hret hfu'
            have hland : ∀ (N' i' : ℕ), 2 * i' + 4 ≤ 2 * m - 1 →
                (∀ j' ≤ i', walk (x, y) f g (2 * j' + 1) = po x y j' ∧
                  walk (x, y) f g (2 * j' + 2) = rr x y j') →
                (∀ j' ≤ N', 1 ≤ j' → pe x y j' ∉ cycSet (x, y) f g m) →
                N' ≤ i' + 1 →
                ∀ {t k : ℕ}, 2 * i' + 5 ≤ t → t ≤ 2 * m - 1 → Odd t →
                walk (x, y) f g t = po x y k → N' + 1 ≤ k →
                lvl x y (walk (x, y) f g (t - 1)) = -1 →
                (∀ t' < t, 2 * i' + 2 ≤ t' → lvl x y (walk (x, y) f g t') < 0) →
                False := by
              intro N' i' hi' hprefix' hnolv' hNi' t k ht5 ht1 htodd htk hk htprev htmin
              exact landing_absurd hcc hf htf hg htg hs hodd hmin hfu' hgr' hm hsd hinj
                hret hw1 hw2 hwlast
                (fun N'' i'' hi'' hprefix'' hnolv'' hNi'' hgap =>
                  hcascade hcc hf htf hg htg hs hodd hmin hfu' hgr' hm hsd hinj hret hw1
                    hw2 hwlast hi'' hprefix'' hnolv'' hNi'' hgap)
                hi' hprefix' hnolv' hNi' (2 * m - t)
                (a := 2 * i' + 2) le_rfl (by omega) (by omega) ht1 htodd htk htprev htmin hk
            exact lemma_a_odd_of_cascade hcc hf htf hg htg hs hodd hmin hfu' hgr' hm hsd
              hinj hret hw1 hw2 hwlast
              (fun N'' i'' hi'' hprefix'' hnolv'' hNi'' hgap =>
                hcascade hcc hf htf hg htg hs hodd hmin hfu' hgr' hm hsd hinj hret hw1
                  hw2 hwlast hi'' hprefix'' hnolv'' hNi'' hgap)
              hland
          · have hev : Even (x + y) := by
              rcases Int.even_or_odd (x + y) with h | h
              · exact h
              · exact absurd h hodd
            exact hfg (heven S f g hf hg htf htg hcc x y hev hs hmin hx)
        · exact absurd (hfu'.trans hgu.symm) hfg
-- ============================================================
-- The mirrored staircase (for the even corner case, `heven`)
-- ============================================================

/-- The mirrored staircase forcing, with `(x, y+1)` as the base row and `g`
as the focused tiling (the even-corner counterpart of
`tasteful_staircase_aux`).  The forbidden-pair parity is identical to the
odd case (the `(x, y+1)`-row cells `(x+k, y+1+k)` are odd and the
`(x+k+1, y+1+k)` are even, since `x + y + 1` is odd); the only difference is
the base case `k = 0`, where the downward option `g (x+1, y+1) = (x+1, y)`
is excluded by the involution `g (x+1, y) = (x, y)` (coming from the corner
horizontal domino `g (x, y) = (x+1, y)`) instead of the minimality of `y`. -/
lemma tasteful_staircase_aux_mirror {S : Finset Cell} {g : Cell → Cell}
    (hg : IsTiling S g) (ht : Tasteful S g) {x y : ℤ} (hodd : Odd (x + y + 1))
    (hs : (x, y + 1) ∈ S) (hsv : g (x, y + 1) = (x, y + 2))
    (hg0 : g (x + 1, y) = (x, y)) :
    ∀ k : ℕ, ((∀ j ≤ k, (x + j, y + 1 + j) ∈ S) →
        (∀ j < k, (x + j + 1, y + 1 + j) ∈ S) →
        g (x + k, y + 1 + k) = (x + k, y + 1 + k + 1)) ∧
      ((∀ j ≤ k, (x + j, y + 1 + j) ∈ S) → (∀ j ≤ k, (x + j + 1, y + 1 + j) ∈ S) →
        g (x + k + 1, y + 1 + k) = (x + k + 2, y + 1 + k)) := by
  obtain ⟨m, hm⟩ := hodd
  intro k
  induction k with
  | zero =>
    simp only [Nat.cast_zero, add_zero]
    have hsv2 : g (x, y + 1) = (x, y + 1 + 1) := by
      rw [show y + 1 + 1 = y + 2 from by ring]
      exact hsv
    constructor
    · intro _ _
      exact hsv2
    · intro _ hO
      have h1S : (x + 1, y + 1) ∈ S := by
        simpa only [Nat.cast_zero, add_zero] using hO 0 (le_refl 0)
      obtain ⟨hmem, hinv, _, hadj⟩ := hg _ h1S
      rcases adjacent_cases hadj with hR | hL | hU | hD
      · -- right: the forced horizontal domino
        have hRc : g (x + 1, y + 1) = (x + 1 + 1, y + 1) := hR
        rw [hRc, Prod.mk.injEq]
        exact ⟨by omega, rfl⟩
      · -- left: `(x, y+1)` is already matched upward
        have hLc : g (x + 1, y + 1) = (x + 1 - 1, y + 1) := hL
        rw [hLc] at hinv
        have e : (x + 1 - 1, y + 1) = (x, y + 1) := by
          rw [Prod.mk.injEq]
          exact ⟨by omega, rfl⟩
        rw [e, hsv] at hinv
        have g1 := (Prod.mk_inj.mp hinv).1
        omega
      · -- up: a forbidden vertical pair with lower-left `(x, y+1)`
        have hUc : g (x + 1, y + 1) = (x + 1, y + 1 + 1) := hU
        exact absurd ⟨hsv2, hUc⟩ (ht.1 x (y + 1) hs h1S ⟨m, by omega⟩)
      · -- down: excluded by the involution `g (x+1, y) = (x, y)`
        have hDc : g (x + 1, y + 1) = (x + 1, y + 1 - 1) := hD
        rw [hDc] at hinv
        have e : (x + 1, y + 1 - 1) = (x + 1, y) := by
          rw [Prod.mk.injEq]
          exact ⟨by omega, by omega⟩
        rw [e, hg0] at hinv
        have g1 := (Prod.mk_inj.mp hinv).1
        omega
  | succ k ih =>
    have hVk1_of : (∀ j ≤ k + 1, (x + j, y + 1 + j) ∈ S) →
        (∀ j < k + 1, (x + j + 1, y + 1 + j) ∈ S) →
        g (x + (k + 1 : ℕ), y + 1 + (k + 1 : ℕ)) =
          (x + (k + 1 : ℕ), y + 1 + (k + 1 : ℕ) + 1) := by
      intro hE hO
      have hEk : ∀ j ≤ k, (x + j, y + 1 + j) ∈ S := fun j hj => hE j (by omega)
      have hOltk : ∀ j < k, (x + j + 1, y + 1 + j) ∈ S := fun j hj => hO j (by omega)
      have hOlek : ∀ j ≤ k, (x + j + 1, y + 1 + j) ∈ S := fun j hj => hO j (by omega)
      have hVk : g (x + (k : ℕ), y + 1 + (k : ℕ)) =
          (x + (k : ℕ), y + 1 + (k : ℕ) + 1) :=
        ih.1 hEk hOltk
      have hHk : g (x + (k : ℕ) + 1, y + 1 + (k : ℕ)) =
          (x + (k : ℕ) + 2, y + 1 + (k : ℕ)) :=
        ih.2 hEk hOlek
      have hnS : (x + (k + 1 : ℕ), y + 1 + (k + 1 : ℕ)) ∈ S := hE (k + 1) le_rfl
      obtain ⟨-, hinv, _, hadj⟩ := hg _ hnS
      rcases adjacent_cases hadj with hR | hL | hU | hD
      · -- right: a forbidden horizontal pair with the horizontal domino below
        have hRc : g (x + (k + 1 : ℕ), y + 1 + (k + 1 : ℕ)) =
            (x + (k + 1 : ℕ) + 1, y + 1 + (k + 1 : ℕ)) := hR
        have e1 : (x + (k + 1 : ℕ), y + 1 + (k : ℕ)) =
            (x + (k : ℕ) + 1, y + 1 + (k : ℕ)) := by
          rw [Prod.mk.injEq]
          exact ⟨by omega, rfl⟩
        have hi1 : (x + (k + 1 : ℕ), y + 1 + (k : ℕ)) ∈ S := by
          rw [e1]
          exact hOlek k le_rfl
        have e2 : (x + (k + 1 : ℕ), y + 1 + (k : ℕ) + 1) =
            (x + (k + 1 : ℕ), y + 1 + (k + 1 : ℕ)) := by
          rw [Prod.mk.injEq]
          exact ⟨rfl, by omega⟩
        have hi2 : (x + (k + 1 : ℕ), y + 1 + (k : ℕ) + 1) ∈ S := by
          rw [e2]
          exact hnS
        have hpar : Even (x + (k + 1 : ℕ) + (y + 1 + (k : ℕ))) :=
          ⟨m + (k : ℕ) + 1, by omega⟩
        have e3 : (x + (k + 1 : ℕ) + 1, y + 1 + (k : ℕ)) =
            (x + (k : ℕ) + 2, y + 1 + (k : ℕ)) := by
          rw [Prod.mk.injEq]
          exact ⟨by omega, rfl⟩
        have g1 : g (x + (k + 1 : ℕ), y + 1 + (k : ℕ)) =
            (x + (k + 1 : ℕ) + 1, y + 1 + (k : ℕ)) := by
          rw [e1, e3]
          exact hHk
        have g2 : g (x + (k + 1 : ℕ), (y + 1 + (k : ℕ)) + 1) =
            (x + (k + 1 : ℕ) + 1, (y + 1 + (k : ℕ)) + 1) := by
          have h1 : y + 1 + (k + 1 : ℕ) = (y + 1 + (k : ℕ)) + 1 := by omega
          rw [← h1]
          exact hRc
        exact absurd ⟨g1, g2⟩ (ht.2 _ _ hi1 hi2 hpar)
      · -- left: the cell above `(x+k, y+1+k)` is already matched downward
        have hLc : g (x + (k + 1 : ℕ), y + 1 + (k + 1 : ℕ)) =
            (x + (k + 1 : ℕ) - 1, y + 1 + (k + 1 : ℕ)) := hL
        rw [hLc] at hinv
        have hinvk := (hg _ (hEk k le_rfl)).2.1
        rw [hVk] at hinvk
        have e : (x + (k + 1 : ℕ) - 1, y + 1 + (k + 1 : ℕ)) =
            (x + (k : ℕ), y + 1 + (k : ℕ) + 1) := by
          rw [Prod.mk.injEq]
          exact ⟨by omega, by omega⟩
        rw [e] at hinv
        have g1 := (Prod.mk_inj.mp (hinvk.symm.trans hinv)).1
        omega
      · -- up: the forced vertical domino
        exact hU
      · -- down: the cell below is already matched to the right
        have hDc : g (x + (k + 1 : ℕ), y + 1 + (k + 1 : ℕ)) =
            (x + (k + 1 : ℕ), y + 1 + (k + 1 : ℕ) - 1) := hD
        rw [hDc] at hinv
        have e : (x + (k + 1 : ℕ), y + 1 + (k + 1 : ℕ) - 1) =
            (x + (k : ℕ) + 1, y + 1 + (k : ℕ)) := by
          rw [Prod.mk.injEq]
          exact ⟨by omega, by omega⟩
        rw [e] at hinv
        have g1 := (Prod.mk_inj.mp (hHk.symm.trans hinv)).1
        omega
    refine ⟨hVk1_of, fun hE hO => ?_⟩
    have hEk : ∀ j ≤ k, (x + j, y + 1 + j) ∈ S := fun j hj => hE j (by omega)
    have hOlek : ∀ j ≤ k, (x + j + 1, y + 1 + j) ∈ S := fun j hj => hO j (by omega)
    have hHk : g (x + (k : ℕ) + 1, y + 1 + (k : ℕ)) =
        (x + (k : ℕ) + 2, y + 1 + (k : ℕ)) :=
      ih.2 hEk hOlek
    have hVk1 : g (x + (k + 1 : ℕ), y + 1 + (k + 1 : ℕ)) =
        (x + (k + 1 : ℕ), y + 1 + (k + 1 : ℕ) + 1) :=
      hVk1_of hE (fun j hj => hO j (by omega))
    have hqS : (x + (k + 1 : ℕ) + 1, y + 1 + (k + 1 : ℕ)) ∈ S := hO (k + 1) le_rfl
    obtain ⟨-, hinv, _, hadj⟩ := hg _ hqS
    rcases adjacent_cases hadj with hR | hL | hU | hD
    · -- right: the forced horizontal domino
      have hRc : g (x + (k + 1 : ℕ) + 1, y + 1 + (k + 1 : ℕ)) =
          (x + (k + 1 : ℕ) + 1 + 1, y + 1 + (k + 1 : ℕ)) := hR
      rw [hRc, Prod.mk.injEq]
      exact ⟨by omega, rfl⟩
    · -- left: the diagonal cell is already matched upward
      have hLc : g (x + (k + 1 : ℕ) + 1, y + 1 + (k + 1 : ℕ)) =
          (x + (k + 1 : ℕ) + 1 - 1, y + 1 + (k + 1 : ℕ)) := hL
      rw [hLc] at hinv
      have e : (x + (k + 1 : ℕ) + 1 - 1, y + 1 + (k + 1 : ℕ)) =
          (x + (k + 1 : ℕ), y + 1 + (k + 1 : ℕ)) := by
        rw [Prod.mk.injEq]
        exact ⟨by omega, rfl⟩
      rw [e] at hinv
      have g1 := (Prod.mk_inj.mp (hVk1.symm.trans hinv)).1
      omega
    · -- up: a forbidden vertical pair with the diagonal domino
      have hUc : g (x + (k + 1 : ℕ) + 1, y + 1 + (k + 1 : ℕ)) =
          (x + (k + 1 : ℕ) + 1, y + 1 + (k + 1 : ℕ) + 1) := hU
      have hnS : (x + (k + 1 : ℕ), y + 1 + (k + 1 : ℕ)) ∈ S := hE (k + 1) le_rfl
      have hpar : Odd (x + (k + 1 : ℕ) + (y + 1 + (k + 1 : ℕ))) :=
        ⟨m + (k + 1 : ℕ), by omega⟩
      exact absurd ⟨hVk1, hUc⟩ (ht.1 _ _ hnS hqS hpar)
    · -- down: the cell below is already matched to the right
      have hDc : g (x + (k + 1 : ℕ) + 1, y + 1 + (k + 1 : ℕ)) =
          (x + (k + 1 : ℕ) + 1, y + 1 + (k + 1 : ℕ) - 1) := hD
      rw [hDc] at hinv
      have hinvk := (hg _ (hOlek k le_rfl)).2.1
      rw [hHk] at hinvk
      have e : (x + (k + 1 : ℕ) + 1, y + 1 + (k + 1 : ℕ) - 1) =
          (x + (k : ℕ) + 2, y + 1 + (k : ℕ)) := by
        rw [Prod.mk.injEq]
        exact ⟨by omega, by omega⟩
      rw [e] at hinv
      have g1 := (Prod.mk_inj.mp (hinvk.symm.trans hinv)).1
      omega

/-- `V`-forcing on the mirrored staircase. -/
lemma g_pe_eq_uu_mirror {S : Finset Cell} {g : Cell → Cell} (hg : IsTiling S g)
    (ht : Tasteful S g) {x y : ℤ} (hodd : Odd (x + y + 1)) (hs : (x, y + 1) ∈ S)
    (hsv : g (x, y + 1) = (x, y + 2)) (hg0 : g (x + 1, y) = (x, y)) (k : ℕ)
    (hE : ∀ j ≤ k, (x + j, y + 1 + j) ∈ S) (hO : ∀ j < k, (x + j + 1, y + 1 + j) ∈ S) :
    g (x + k, y + 1 + k) = (x + k, y + 1 + k + 1) :=
  (tasteful_staircase_aux_mirror hg ht hodd hs hsv hg0 k).1 hE hO

/-- `H`-forcing on the mirrored staircase. -/
lemma g_po_eq_rr_mirror {S : Finset Cell} {g : Cell → Cell} (hg : IsTiling S g)
    (ht : Tasteful S g) {x y : ℤ} (hodd : Odd (x + y + 1)) (hs : (x, y + 1) ∈ S)
    (hsv : g (x, y + 1) = (x, y + 2)) (hg0 : g (x + 1, y) = (x, y)) (k : ℕ)
    (hE : ∀ j ≤ k, (x + j, y + 1 + j) ∈ S) (hO : ∀ j ≤ k, (x + j + 1, y + 1 + j) ∈ S) :
    g (x + k + 1, y + 1 + k) = (x + k + 2, y + 1 + k) :=
  (tasteful_staircase_aux_mirror hg ht hodd hs hsv hg0 k).2 hE hO
-- ============================================================
-- A landing with full staircase membership is impossible (case A)
-- ============================================================

/-- A landing at `po k` (odd time, previous cell at level `-1`) with the whole
staircase below `k` in `S` cannot happen after a dive: the down-bounce
(`bounce_at_return`) puts `po (k-1)` at `t - 2`, but the first-hit
minimality forces level `< 0` there.  This closes every landing that does
not cross the minimal gap (case (A) of the cascade analysis). -/
lemma landing_absurd_of_mem {S : Finset Cell} {f g : Cell → Cell} {m : ℕ} {x y : ℤ}
    (hf : IsTiling S f) (htf : Tasteful S f) (hg : IsTiling S g)
    (hsd : (x, y) ∈ sd S f g)
    (hinj : ∀ i < 2 * m, ∀ j < 2 * m, walk (x, y) f g i = walk (x, y) f g j → i = j)
    (hm : 2 ≤ m) (hret : walk (x, y) f g (2 * m) = (x, y))
    (hsS : (x, y) ∈ S) (hodd : Odd (x + y)) (hfu : f (x, y) = (x, y + 1))
    (hmin : ∀ c ∈ S, y ≤ c.2)
    {t k : ℕ} (ht : walk (x, y) f g t = po x y k) (htodd : Odd t) (ht2 : 2 ≤ t)
    (hk : 1 ≤ k) (hprev : lvl x y (walk (x, y) f g (t - 1)) = -1)
    (hmem : ∀ j' ≤ k, po x y j' ∈ S) (hmemV : ∀ j' ≤ k, pe x y j' ∈ S)
    (hmemV1 : ∀ j' < k, po x y j' ∈ S) (hmemV2 : ∀ j' ≤ k - 1, pe x y j' ∈ S)
    {a : ℕ} (hat : a ≤ t - 2)
    (hmin' : ∀ t' < t, a ≤ t' → lvl x y (walk (x, y) f g t') < 0) : False := by
  obtain ⟨-, -, hb2⟩ := bounce_at_return hf hg htf hsd hinj hm hret hsS hodd hfu
    hmin ht htodd ht2 hk hprev hmem hmemV hmemV1 hmemV2
  have h3 := hmin' (t - 2) (by omega) hat
  rw [hb2, lvl_po] at h3
  omega
-- ============================================================
-- The even corner: starting directions (for `heven`)
-- ============================================================

/-- At the even corner, `g (x, y+1)` (the cell above the corner) is forced
up or goes left: right is a forbidden horizontal pair with the corner
domino `g (x, y) = (x+1, y)`, and down is the corner cell itself. -/
lemma g_uu_zero_cases {S : Finset Cell} {g : Cell → Cell} (hg : IsTiling S g)
    (ht : Tasteful S g) {x y : ℤ} (hev : Even (x + y)) (hs : (x, y) ∈ S)
    (hgr : g (x, y) = (x + 1, y)) (huu : (x, y + 1) ∈ S) :
    g (x, y + 1) = (x, y + 2) ∨ g (x, y + 1) = (x - 1, y + 1) := by
  obtain ⟨hmem, hinv, -, hadj⟩ := hg _ huu
  rcases adjacent_cases hadj with hR | hL | hU | hD
  · exfalso
    have hRc : g (x, y + 1) = (x + 1, y + 1) := hR
    exact absurd ⟨hgr, hRc⟩ (ht.2 x y hs huu hev)
  · right
    exact hL
  · left
    rw [← show y + 1 + 1 = y + 2 from by ring]
    exact hU
  · exfalso
    have hDc : g (x, y + 1) = (x, y + 1 - 1) := hD
    have e : (x, y + 1 - 1) = (x, y) := by
      rw [Prod.mk.injEq]
      exact ⟨rfl, by omega⟩
    rw [hDc, e] at hinv
    rw [hgr] at hinv
    simp [Prod.ext_iff] at hinv

/-- In the even case, `f (po 0)` is `rr 0` (right) or `pe 1` (up): the
vertical pair with the corner domino is allowed when `x + y` is even. -/
lemma f_po_zero_cases {S : Finset Cell} {f : Cell → Cell} (hf : IsTiling S f)
    {x y : ℤ} (hs : (x, y) ∈ S) (hmin : ∀ c ∈ S, y ≤ c.2)
    (hfu : f (x, y) = (x, y + 1)) (hpo : (x + 1, y) ∈ S) :
    f (x + 1, y) = (x + 2, y) ∨ f (x + 1, y) = (x + 1, y + 1) := by
  obtain ⟨hmem, hinv, -, hadj⟩ := hf _ hpo
  rcases adjacent_cases hadj with hR | hL | hU | hD
  · left
    rw [show x + 2 = x + 1 + 1 from by ring]
    exact hR
  · exfalso
    have hLc : f (x + 1, y) = (x + 1 - 1, y) := hL
    rw [hLc] at hinv
    have e : (x + 1 - 1, y) = (x, y) := by
      rw [Prod.mk.injEq]
      exact ⟨by omega, rfl⟩
    rw [e, hfu] at hinv
    simp [Prod.ext_iff] at hinv
  · right
    exact hU
  · exfalso
    have hDc : f (x + 1, y) = (x + 1, y - 1) := hD
    rw [hDc] at hmem
    have h2 : y ≤ y - 1 := hmin _ hmem
    omega
-- ============================================================
-- The shifted level function (for the even corner, `heven`)
-- ============================================================

/-- Shifting the base row up by one shifts all levels down by one. -/
lemma lvl_succ (x y : ℤ) (c : Cell) : lvl x (y + 1) c = lvl x y c - 1 := by
  unfold lvl
  ring

/-- A cell at level `0` for the shifted base row `(x, y+1)` is either the
corner `s = (x, y)` itself (when on the `y`-row) or a `po k` on the shifted
staircase. -/
lemma lvl_succ_zero_cases {x y : ℤ} {c : Cell} (hy : y ≤ c.2)
    (h0 : lvl x (y + 1) c = 0) :
    c = (x, y) ∨ ∃ k : ℕ, c = po x (y + 1) k := by
  obtain ⟨a, b⟩ := c
  by_cases hcy : b = y
  · left
    have ha : a = x := by
      unfold lvl at h0
      simp only at h0
      rw [hcy] at h0
      simp at h0
      omega
    exact Prod.ext ha hcy
  · right
    have hy' : y + 1 ≤ b := by omega
    exact eq_po_of_lvl_zero hy' h0


-- ============================================================
-- Route Y: the global height-difference invariant (merged from the
-- backup route file; namespace `AltP3b` inside `Usa2009P3`).
-- ============================================================

/-!
# USAMO 2009 P3(b) — backup route: global height-difference invariant

Route Y (independent of the main line's cascade).  For two tilings `f g` of a
hole-free region `S` we define a height-difference function `D : ℤ × ℤ → ℤ` on
grid vertices, as a west-ray sum of the difference 1-form `Δ = φ f − φ g`.
`Δ` is closed around *every* cell (both tilings contribute `0` around cells of
`S`, and equal contributions around cells outside `S`), which gives the
gradient property of `D` by a finite telescoping — no topology needed.

The final contradiction (proved later in the file): a tasteful tiling is a
pointwise height maximum, so two tasteful tilings force `D = 0`, hence `f = g`.
-/

namespace AltP3b

abbrev Cell := ℤ × ℤ

def Adjacent (c c' : Cell) : Prop := (c.1 - c'.1).natAbs + (c.2 - c'.2).natAbs = 1

def IsTiling (S : Finset Cell) (f : Cell → Cell) : Prop :=
  ∀ c ∈ S, f c ∈ S ∧ f (f c) = c ∧ f c ≠ c ∧ Adjacent c (f c)

def Tasteful (S : Finset Cell) (f : Cell → Cell) : Prop :=
  (∀ i j : ℤ, (i, j) ∈ S → (i + 1, j) ∈ S → Odd (i + j) →
    ¬(f (i, j) = (i, j + 1) ∧ f (i + 1, j) = (i + 1, j + 1))) ∧
  (∀ i j : ℤ, (i, j) ∈ S → (i, j + 1) ∈ S → Even (i + j) →
    ¬(f (i, j) = (i + 1, j) ∧ f (i, j + 1) = (i + 1, j + 1)))

def CellPath (P : Cell → Prop) : Cell → Cell → Prop :=
  Relation.ReflTransGen fun c c' ↦ P c ∧ P c' ∧ Adjacent c c'

def ComplConnected (S : Finset Cell) : Prop := ∀ c ∉ S, ∀ c' ∉ S, CellPath (· ∉ S) c c'

lemma adjacent_cases {c c' : Cell} (h : Adjacent c c') :
    c' = (c.1 + 1, c.2) ∨ c' = (c.1 - 1, c.2) ∨ c' = (c.1, c.2 + 1) ∨ c' = (c.1, c.2 - 1) := by
  obtain ⟨a, b⟩ := c
  obtain ⟨a', b'⟩ := c'
  rw [Adjacent] at h
  simp only at h
  obtain ⟨hx, hy⟩ | ⟨hx, hy⟩ : ((a - a').natAbs = 0 ∧ (b - b').natAbs = 1) ∨
    ((a - a').natAbs = 1 ∧ (b - b').natAbs = 0) := by omega
  · rw [Int.natAbs_eq_zero] at hx
    obtain hy | hy := Int.natAbs_eq_iff.mp hy <;> simp_all <;> omega
  · rw [Int.natAbs_eq_zero] at hy
    obtain hx | hx := Int.natAbs_eq_iff.mp hx <;> simp_all <;> omega

variable {S : Finset Cell} {f g : Cell → Cell}

open Classical

lemma IsTiling.mapsTo (hf : IsTiling S f) : ∀ c ∈ S, f c ∈ S := fun c hc ↦ (hf c hc).1
lemma IsTiling.involute (hf : IsTiling S f) : ∀ c ∈ S, f (f c) = c := fun c hc ↦ (hf c hc).2.1
lemma IsTiling.ne (hf : IsTiling S f) : ∀ c ∈ S, f c ≠ c := fun c hc ↦ (hf c hc).2.2.1
lemma IsTiling.adj (hf : IsTiling S f) : ∀ c ∈ S, Adjacent c (f c) := fun c hc ↦ (hf c hc).2.2.2

-- ============================================================
-- The height 1-form
-- ============================================================

/-- The east grid edge from vertex `(a,b)` (to `(a+1,b)`) is crossed by the
vertical domino `{(a,b-1),(a,b)}`. -/
def crE (S : Finset Cell) (f : Cell → Cell) (a b : ℤ) : Prop :=
  (a, b - 1) ∈ S ∧ f (a, b - 1) = (a, b)

/-- The north grid edge from vertex `(a,b)` (to `(a,b+1)`) is crossed by the
horizontal domino `{(a-1,b),(a,b)}`. -/
def crN (S : Finset Cell) (f : Cell → Cell) (a b : ℤ) : Prop :=
  (a - 1, b) ∈ S ∧ f (a - 1, b) = (a, b)


/-- The height 1-form on the east edge from `(a,b)`, traversed eastward. -/
noncomputable def φE (S : Finset Cell) (f : Cell → Cell) (a b : ℤ) : ℤ :=
  (if Even (a + b) then (1 : ℤ) else -1) * (if crE S f a b then -3 else 1)

/-- The height 1-form on the north edge from `(a,b)`, traversed northward. -/
noncomputable def φN (S : Finset Cell) (f : Cell → Cell) (a b : ℤ) : ℤ :=
  (if Even (a + b) then (-1 : ℤ) else 1) * (if crN S f a b then -3 else 1)

lemma crE_of_not_mem (hf : IsTiling S f) {a b : ℤ} (h : (a, b) ∉ S) : ¬ crE S f a b := by
  rintro ⟨hmem, hval⟩
  have := hf.mapsTo _ hmem
  rw [hval] at this
  exact h this

lemma crN_of_not_mem (hf : IsTiling S f) {a b : ℤ} (h : (a, b) ∉ S) : ¬ crN S f a b := by
  rintro ⟨hmem, hval⟩
  have := hf.mapsTo _ hmem
  rw [hval] at this
  exact h this

lemma even_add_one_int (n : ℤ) : Even (n + 1) ↔ ¬ Even n :=
  Int.even_add_one

-- Crossing predicates rephrased as values of `f (i,j)`.
lemma crN_succ_iff (hf : IsTiling S f) {i j : ℤ} (hij : (i, j) ∈ S) :
    crN S f (i + 1) j ↔ f (i, j) = (i + 1, j) := by
  simp [crN, add_sub_cancel, hij]

lemma crE_succ_iff (hf : IsTiling S f) {i j : ℤ} (hij : (i, j) ∈ S) :
    crE S f i (j + 1) ↔ f (i, j) = (i, j + 1) := by
  simp [crE, add_sub_cancel, hij]

lemma crN_self_iff (hf : IsTiling S f) {i j : ℤ} (hij : (i, j) ∈ S) :
    crN S f i j ↔ f (i, j) = (i - 1, j) := by
  constructor
  · rintro ⟨hmem, hval⟩
    calc f (i, j) = f (f (i - 1, j)) := by rw [hval]
      _ = (i - 1, j) := hf.involute _ hmem
  · intro h
    refine ⟨?_, ?_⟩
    · rw [← h]; exact hf.mapsTo _ hij
    · rw [← h]; exact hf.involute _ hij

lemma crE_self_iff (hf : IsTiling S f) {i j : ℤ} (hij : (i, j) ∈ S) :
    crE S f i j ↔ f (i, j) = (i, j - 1) := by
  constructor
  · rintro ⟨hmem, hval⟩
    calc f (i, j) = f (f (i, j - 1)) := by rw [hval]
      _ = (i, j - 1) := hf.involute _ hmem
  · intro h
    refine ⟨?_, ?_⟩
    · rw [← h]; exact hf.mapsTo _ hij
    · rw [← h]; exact hf.involute _ hij

/-- Closedness of the height 1-form around a cell of `S`. -/
lemma φ_closed (hf : IsTiling S f) {i j : ℤ} (hij : (i, j) ∈ S) :
    φE S f i j + φN S f (i + 1) j - φE S f i (j + 1) - φN S f i j = 0 := by
  have hpa : Even (i + 1 + j) ↔ ¬ Even (i + j) := by
    rw [show i + 1 + j = (i + j) + 1 from by ring]; exact even_add_one_int _
  have hpb : Even (i + (j + 1)) ↔ ¬ Even (i + j) := by
    rw [show i + (j + 1) = (i + j) + 1 from by ring]; exact even_add_one_int _
  have hfc := hf.adj _ hij
  obtain hE | hW | hN | hS := adjacent_cases hfc
  · have hE' : f (i, j) = (i + 1, j) := hE
    have c1 : crN S f (i + 1) j := (crN_succ_iff hf hij).mpr hE'
    have c2 : ¬ crN S f i j := by
      rw [crN_self_iff hf hij]; intro hh; rw [hE'] at hh; simp only [Prod.mk.injEq] at hh; omega
    have c3 : ¬ crE S f i j := by
      rw [crE_self_iff hf hij]; intro hh; rw [hE'] at hh; simp only [Prod.mk.injEq] at hh; omega
    have c4 : ¬ crE S f i (j + 1) := by
      rw [crE_succ_iff hf hij]; intro hh; rw [hE'] at hh; simp only [Prod.mk.injEq] at hh; omega
    simp only [φE, φN, c1, c2, c3, c4, if_true, if_false]
    by_cases hp : Even (i + j) <;> simp [hp, hpa, hpb]
  · have hW' : f (i, j) = (i - 1, j) := hW
    have c1 : crN S f i j := (crN_self_iff hf hij).mpr hW'
    have c2 : ¬ crN S f (i + 1) j := by
      rw [crN_succ_iff hf hij]; intro hh; rw [hW'] at hh; simp only [Prod.mk.injEq] at hh; omega
    have c3 : ¬ crE S f i j := by
      rw [crE_self_iff hf hij]; intro hh; rw [hW'] at hh; simp only [Prod.mk.injEq] at hh; omega
    have c4 : ¬ crE S f i (j + 1) := by
      rw [crE_succ_iff hf hij]; intro hh; rw [hW'] at hh; simp only [Prod.mk.injEq] at hh; omega
    simp only [φE, φN, c1, c2, c3, c4, if_true, if_false]
    by_cases hp : Even (i + j) <;> simp [hp, hpa, hpb]
  · have hN' : f (i, j) = (i, j + 1) := hN
    have c1 : crE S f i (j + 1) := (crE_succ_iff hf hij).mpr hN'
    have c2 : ¬ crE S f i j := by
      rw [crE_self_iff hf hij]; intro hh; rw [hN'] at hh; simp only [Prod.mk.injEq] at hh; omega
    have c3 : ¬ crN S f i j := by
      rw [crN_self_iff hf hij]; intro hh; rw [hN'] at hh; simp only [Prod.mk.injEq] at hh; omega
    have c4 : ¬ crN S f (i + 1) j := by
      rw [crN_succ_iff hf hij]; intro hh; rw [hN'] at hh; simp only [Prod.mk.injEq] at hh; omega
    simp only [φE, φN, c1, c2, c3, c4, if_true, if_false]
    by_cases hp : Even (i + j) <;> simp [hp, hpa, hpb]
  · have hS' : f (i, j) = (i, j - 1) := hS
    have c1 : crE S f i j := (crE_self_iff hf hij).mpr hS'
    have c2 : ¬ crE S f i (j + 1) := by
      rw [crE_succ_iff hf hij]; intro hh; rw [hS'] at hh; simp only [Prod.mk.injEq] at hh; omega
    have c3 : ¬ crN S f i j := by
      rw [crN_self_iff hf hij]; intro hh; rw [hS'] at hh; simp only [Prod.mk.injEq] at hh; omega
    have c4 : ¬ crN S f (i + 1) j := by
      rw [crN_succ_iff hf hij]; intro hh; rw [hS'] at hh; simp only [Prod.mk.injEq] at hh; omega
    simp only [φE, φN, c1, c2, c3, c4, if_true, if_false]
    by_cases hp : Even (i + j) <;> simp [hp, hpa, hpb]

/-- Closedness of the difference 1-form around ANY cell (in `S` or not). -/
lemma Δ_closed (hf : IsTiling S f) (hg : IsTiling S g) {i j : ℤ} :
    (φE S f i j - φE S g i j) + (φN S f (i + 1) j - φN S g (i + 1) j)
      - (φE S f i (j + 1) - φE S g i (j + 1)) - (φN S f i j - φN S g i j) = 0 := by
  by_cases hij : (i, j) ∈ S
  · have hf' := φ_closed hf hij
    have hg' := φ_closed hg hij
    linear_combination hf' - hg'
  · have hfE := crE_of_not_mem hf hij
    have hgE := crE_of_not_mem hg hij
    have hfN := crN_of_not_mem hf hij
    have hgN := crN_of_not_mem hg hij
    have hfE1 : ¬ crE S f i (j + 1) := by
      rintro ⟨hmem, _⟩
      exact hij (by simpa using hmem)
    have hgE1 : ¬ crE S g i (j + 1) := by
      rintro ⟨hmem, _⟩
      exact hij (by simpa using hmem)
    have hfN1 : ¬ crN S f (i + 1) j := by
      rintro ⟨hmem, _⟩
      exact hij (by simpa using hmem)
    have hgN1 : ¬ crN S g (i + 1) j := by
      rintro ⟨hmem, _⟩
      exact hij (by simpa using hmem)
    simp only [φE, φN, hfE, hgE, hfN, hgN, hfE1, hgE1, hfN1, hgN1, if_false]
    ring

-- ============================================================
-- The height-difference function D (west-ray definition)
-- ============================================================

/-- A bound strictly west of every cell of `S`. -/
noncomputable def westBound (S : Finset Cell) : ℤ :=
  if h : (S.image Prod.fst).Nonempty then (S.image Prod.fst).min' h - 1 else 0

lemma westBound_lt (S : Finset Cell) {c : Cell} (hc : c ∈ S) : westBound S < c.1 := by
  rw [westBound]
  split_ifs with hne
  · have : (S.image Prod.fst).min' hne ≤ c.1 := Finset.min'_le _ _ (Finset.mem_image_of_mem _ hc)
    omega
  · have hSe : S = ∅ := Finset.image_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp hne)
    rw [hSe] at hc
    simp at hc

/-- The difference 1-form on east edges. -/
noncomputable def ΔE (S : Finset Cell) (f g : Cell → Cell) (a b : ℤ) : ℤ := φE S f a b - φE S g a b

/-- The difference 1-form on north edges. -/
noncomputable def ΔN (S : Finset Cell) (f g : Cell → Cell) (a b : ℤ) : ℤ := φN S f a b - φN S g a b

lemma ΔE_eq_zero_of_lt (hf : IsTiling S f) (hg : IsTiling S g) {a b : ℤ} (h : a < westBound S) :
    ΔE S f g a b = 0 := by
  have h1 : (a, b - 1) ∉ S := fun hc ↦ by
    have hh := westBound_lt S hc; simp at hh; omega
  have hf' : ¬ crE S f a b := fun ⟨hmem, _⟩ ↦ h1 hmem
  have hg' : ¬ crE S g a b := fun ⟨hmem, _⟩ ↦ h1 hmem
  simp [ΔE, φE, hf', hg']

lemma ΔN_eq_zero_of_lt (hf : IsTiling S f) (hg : IsTiling S g) {a b : ℤ} (h : a < westBound S) :
    ΔN S f g a b = 0 := by
  have h1 : (a - 1, b) ∉ S := fun hc ↦ by
    have hh := westBound_lt S hc; simp at hh; omega
  have hf' : ¬ crN S f a b := fun ⟨hmem, _⟩ ↦ h1 hmem
  have hg' : ¬ crN S g a b := fun ⟨hmem, _⟩ ↦ h1 hmem
  simp [ΔN, φN, hf', hg']

/-- Integer-interval version of `Finset.sum_Ico_succ_top`. -/
lemma sum_Ico_succ_top_int (F : ℤ → ℤ) {a b : ℤ} (h : a ≤ b) :
    ∑ i ∈ Finset.Ico a (b + 1), F i = ∑ i ∈ Finset.Ico a b, F i + F b :=
  (Finset.sum_Ico_add_eq_sum_Ico_add_one h F).symm

/-- Telescoping sum over an integer interval. -/
lemma sum_Ico_sub_int (F : ℤ → ℤ) (m n : ℤ) (h : m ≤ n) :
    ∑ i ∈ Finset.Ico m n, (F (i + 1) - F i) = F n - F m := by
  have key : ∀ k : ℕ, ∑ i ∈ Finset.Ico m (m + k), (F (i + 1) - F i) = F (m + k) - F m := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show m + (↑(k + 1) : ℤ) = (m + ↑k) + 1 from by push_cast; ring]
      rw [sum_Ico_succ_top_int _ (show m ≤ m + ↑k by omega)]
      rw [ih]
      ring
  have hn : n = m + (n - m).toNat := by omega
  rw [hn]
  exact key (n - m).toNat

/-- The height-difference function: west-ray sum of the difference 1-form. -/
noncomputable def D (S : Finset Cell) (f g : Cell → Cell) (a b : ℤ) : ℤ :=
  ∑ i ∈ Finset.Ico (westBound S) a, ΔE S f g i b

lemma D_eq_zero_of_le (hf : IsTiling S f) (hg : IsTiling S g) {a b : ℤ} (h : a ≤ westBound S) :
    D S f g a b = 0 := by
  rw [D, Finset.Ico_eq_empty (by omega)]
  simp

lemma D_east (hf : IsTiling S f) (hg : IsTiling S g) {a b : ℤ} :
    D S f g (a + 1) b = D S f g a b + ΔE S f g a b := by
  by_cases h : westBound S ≤ a
  · simp only [D]
    rw [sum_Ico_succ_top_int _ h]
  · have ha : a < westBound S := by omega
    rw [D_eq_zero_of_le hf hg (by omega : a ≤ westBound S),
        D_eq_zero_of_le hf hg (by omega : a + 1 ≤ westBound S),
        ΔE_eq_zero_of_lt hf hg ha]
    ring

lemma D_north (hf : IsTiling S f) (hg : IsTiling S g) {a b : ℤ} :
    D S f g a (b + 1) = D S f g a b + ΔN S f g a b := by
  by_cases h : westBound S ≤ a
  · have hclosed : ∀ i : ℤ, ΔE S f g i (b + 1) - ΔE S f g i b = ΔN S f g (i + 1) b - ΔN S f g i b := by
      intro i
      have hcc := Δ_closed hf hg (i := i) (j := b)
      simp only [ΔE, ΔN]
      linear_combination -hcc
    have hwb : ΔN S f g (westBound S) b = 0 := by
      have h1 : (westBound S - 1, b) ∉ S := fun hc ↦ by
        have hh := westBound_lt S hc; simp at hh; omega
      have hf' : ¬ crN S f (westBound S) b := fun ⟨hmem, _⟩ ↦ h1 hmem
      have hg' : ¬ crN S g (westBound S) b := fun ⟨hmem, _⟩ ↦ h1 hmem
      simp [ΔN, φN, hf', hg']
    have hsum : (∑ i ∈ Finset.Ico (westBound S) a, ΔE S f g i (b + 1))
        = (∑ i ∈ Finset.Ico (westBound S) a, ΔE S f g i b) + ΔN S f g a b := by
      have h1 : (∑ i ∈ Finset.Ico (westBound S) a, (ΔE S f g i (b + 1) - ΔE S f g i b)) = ΔN S f g a b := by
        rw [Finset.sum_congr rfl (fun i _ ↦ hclosed i), sum_Ico_sub_int (fun i ↦ ΔN S f g i b) _ _ h, hwb]
        ring
      have h2 : (∑ i ∈ Finset.Ico (westBound S) a, (ΔE S f g i (b + 1) - ΔE S f g i b))
          = (∑ i ∈ Finset.Ico (westBound S) a, ΔE S f g i (b + 1)) - (∑ i ∈ Finset.Ico (westBound S) a, ΔE S f g i b) := by
        rw [Finset.sum_sub_distrib]
      rw [h2] at h1
      omega
    simp only [D]
    exact hsum
  · have ha : a < westBound S := by omega
    rw [D_eq_zero_of_le hf hg (by omega : a ≤ westBound S),
        D_eq_zero_of_le hf hg (by omega : a ≤ westBound S),
        ΔN_eq_zero_of_lt hf hg ha]
    ring

-- ============================================================
-- The poison-pair lemma (local)
-- ============================================================

/-- Two stacked horizontal dominoes at an even base form a distasteful pair. -/
lemma not_tasteful_of_crN_pair (ht : Tasteful S f) {a b : ℤ}
    (h1 : crN S f a b) (h2 : crN S f a (b - 1)) (hpar : Even (a + b)) : False := by
  obtain ⟨hm1, hv1⟩ := h1
  obtain ⟨hm2, hv2⟩ := h2
  obtain ⟨k, hk⟩ := hpar
  have hpar' : Even (a - 1 + (b - 1)) := ⟨k - 1, by omega⟩
  exact ht.2 (a - 1) (b - 1) (by simpa using hm2) (by simpa using hm1) hpar'
    ⟨by simpa using hv2, by simpa using hv1⟩

/-- Two side-by-side vertical dominoes at an odd base form a distasteful pair. -/
lemma not_tasteful_of_crE_pair (ht : Tasteful S f) {a b : ℤ}
    (h1 : crE S f a b) (h2 : crE S f (a - 1) b) (hpar : Odd (a + b)) : False := by
  obtain ⟨hm1, hv1⟩ := h1
  obtain ⟨hm2, hv2⟩ := h2
  obtain ⟨k, hk⟩ := hpar
  have hpar' : Odd (a - 1 + (b - 1)) := ⟨k - 1, by omega⟩
  exact ht.1 (a - 1) (b - 1) (by simpa using hm2) (by simpa using hm1) hpar'
    ⟨by simpa using hv2, by simpa using hv1⟩

-- ============================================================
-- D is compactly supported
-- ============================================================

/-- A bound strictly east of every cell of `S`. -/
noncomputable def eastBound (S : Finset Cell) : ℤ :=
  if h : (S.image Prod.fst).Nonempty then (S.image Prod.fst).max' h + 1 else 0

lemma eastBound_gt (S : Finset Cell) {c : Cell} (hc : c ∈ S) : c.1 < eastBound S := by
  rw [eastBound]
  split_ifs with hne
  · have : c.1 ≤ (S.image Prod.fst).max' hne := Finset.le_max' _ _ (Finset.mem_image_of_mem _ hc)
    omega
  · have hSe : S = ∅ := Finset.image_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp hne)
    rw [hSe] at hc
    simp at hc

/-- A bound strictly south of every cell of `S`. -/
noncomputable def southBound (S : Finset Cell) : ℤ :=
  if h : (S.image Prod.snd).Nonempty then (S.image Prod.snd).min' h - 1 else 0

lemma southBound_lt (S : Finset Cell) {c : Cell} (hc : c ∈ S) : southBound S < c.2 := by
  rw [southBound]
  split_ifs with hne
  · have : (S.image Prod.snd).min' hne ≤ c.2 := Finset.min'_le _ _ (Finset.mem_image_of_mem _ hc)
    omega
  · have hSe : S = ∅ := Finset.image_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp hne)
    rw [hSe] at hc
    simp at hc

/-- A bound strictly north of every cell of `S`. -/
noncomputable def northBound (S : Finset Cell) : ℤ :=
  if h : (S.image Prod.snd).Nonempty then (S.image Prod.snd).max' h + 1 else 0

lemma northBound_gt (S : Finset Cell) {c : Cell} (hc : c ∈ S) : c.2 < northBound S := by
  rw [northBound]
  split_ifs with hne
  · have : c.2 ≤ (S.image Prod.snd).max' hne := Finset.le_max' _ _ (Finset.mem_image_of_mem _ hc)
    omega
  · have hSe : S = ∅ := Finset.image_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp hne)
    rw [hSe] at hc
    simp at hc

lemma ΔE_eq_zero_of_north (hf : IsTiling S f) (hg : IsTiling S g) {a b : ℤ}
    (h : northBound S ≤ b) : ΔE S f g a b = 0 := by
  have h1 : (a, b) ∉ S := fun hc ↦ by
    have hh := northBound_gt S hc; simp at hh; omega
  have hf' := crE_of_not_mem hf h1
  have hg' := crE_of_not_mem hg h1
  simp [ΔE, φE, hf', hg']

lemma ΔE_eq_zero_of_south (hf : IsTiling S f) (hg : IsTiling S g) {a b : ℤ}
    (h : b ≤ southBound S) : ΔE S f g a b = 0 := by
  have h1 : (a, b - 1) ∉ S := fun hc ↦ by
    have hh := southBound_lt S hc; simp at hh; omega
  have hf' : ¬ crE S f a b := fun ⟨hmem, _⟩ ↦ h1 hmem
  have hg' : ¬ crE S g a b := fun ⟨hmem, _⟩ ↦ h1 hmem
  simp [ΔE, φE, hf', hg']

lemma ΔN_eq_zero_of_east (hf : IsTiling S f) (hg : IsTiling S g) {a b : ℤ}
    (h : eastBound S ≤ a) : ΔN S f g a b = 0 := by
  have h1 : (a, b) ∉ S := fun hc ↦ by
    have hh := eastBound_gt S hc; simp at hh; omega
  have hf' := crN_of_not_mem hf h1
  have hg' := crN_of_not_mem hg h1
  simp [ΔN, φN, hf', hg']

/-- `D` vanishes south of `S` (everywhere). -/
lemma D_eq_zero_of_south (hf : IsTiling S f) (hg : IsTiling S g) {a b : ℤ}
    (h : b ≤ southBound S) : D S f g a b = 0 := by
  rw [D]
  apply Finset.sum_eq_zero
  intro i _
  exact ΔE_eq_zero_of_south hf hg h

/-- `D` vanishes east of `S` (everywhere), by southward induction. -/
lemma D_eq_zero_of_east (hf : IsTiling S f) (hg : IsTiling S g) {a b : ℤ}
    (h : eastBound S ≤ a) : D S f g a b = 0 := by
  have key : ∀ b₂ : ℤ, b₂ ≤ southBound S → ∀ b₁ : ℤ, b₂ ≤ b₁ → D S f g a b₁ = D S f g a b₂ := by
    intro b₂ hb₂ b₁ hle
    have h2 : ∀ k : ℕ, D S f g a (b₂ + k) = D S f g a b₂ := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [show b₂ + (↑(k + 1) : ℤ) = (b₂ + ↑k) + 1 from by push_cast; ring]
        rw [D_north hf hg, ΔN_eq_zero_of_east hf hg h, ih]
        ring
    have hb₁ : b₁ = b₂ + (b₁ - b₂).toNat := by
      rw [Int.toNat_of_nonneg (by omega : 0 ≤ b₁ - b₂)]
      ring
    rw [hb₁]
    exact h2 (b₁ - b₂).toNat
  by_cases hb : b ≤ southBound S
  · exact D_eq_zero_of_south hf hg hb
  · push_neg at hb
    rw [key (southBound S) (le_refl _) b (by omega)]
    exact D_eq_zero_of_south hf hg (le_refl _)

/-- `D` vanishes north of `S` (everywhere). -/
lemma D_eq_zero_of_north (hf : IsTiling S f) (hg : IsTiling S g) {a b : ℤ}
    (h : northBound S ≤ b) : D S f g a b = 0 := by
  rw [D]
  apply Finset.sum_eq_zero
  intro i _
  exact ΔE_eq_zero_of_north hf hg h

/-- `D` is nonzero only on a finite box. -/
lemma D_finite_support (hf : IsTiling S f) (hg : IsTiling S g) :
    ∀ a b : ℤ, D S f g a b ≠ 0 →
      westBound S < a ∧ a < eastBound S ∧ southBound S < b ∧ b < northBound S := by
  intro a b hne
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_contra h
    push_neg at h
    exact hne (D_eq_zero_of_le hf hg h)
  · by_contra h
    push_neg at h
    exact hne (D_eq_zero_of_east hf hg h)
  · by_contra h
    push_neg at h
    exact hne (D_eq_zero_of_south hf hg h)
  · by_contra h
    push_neg at h
    exact hne (D_eq_zero_of_north hf hg h)

/-- `D` attains a global minimum. -/
lemma D_exists_min (hf : IsTiling S f) (hg : IsTiling S g) :
    ∃ v₀ : Cell, ∀ v : Cell, D S f g v₀.1 v₀.2 ≤ D S f g v.1 v.2 := by
  classical
  let box := Finset.Ico (westBound S) (eastBound S) ×ˢ Finset.Ico (southBound S) (northBound S)
  let pt : Cell := (westBound S, southBound S)
  let vals := (insert pt box).image (fun v : Cell ↦ D S f g v.1 v.2)
  have hne : vals.Nonempty := Finset.image_nonempty.mpr (Finset.insert_nonempty _ _)
  have hm_mem : vals.min' hne ∈ vals := Finset.min'_mem _ _
  rw [Finset.mem_image] at hm_mem
  obtain ⟨v₀, hv₀, hmval⟩ := hm_mem
  have hmval' : D S f g v₀.1 v₀.2 = vals.min' hne := hmval
  refine ⟨v₀, fun v ↦ ?_⟩
  by_cases hv : v ∈ insert pt box
  · rw [hmval']
    exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ hv)
  · have hDv : D S f g v.1 v.2 = 0 := by
      by_contra h
      have hsup := D_finite_support hf hg (a := v.1) (b := v.2) h
      have : v ∈ box := by
        simp [box] at hv ⊢
        omega
      exact hv (Finset.mem_insert.mpr (Or.inr this))
    rw [hDv]
    have hm0 : vals.min' hne ≤ D S f g pt.1 pt.2 :=
      Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Finset.mem_insert_self _ _))
    have hpt0 : D S f g pt.1 pt.2 = 0 := D_eq_zero_of_le hf hg (le_refl _)
    rw [hpt0] at hm0
    omega

-- ============================================================
-- From D = 0 to f = g
-- ============================================================

lemma ΔE_eq_zero_of_D (hf : IsTiling S f) (hg : IsTiling S g)
    (hD : ∀ a b : ℤ, D S f g a b = 0) {a b : ℤ} : ΔE S f g a b = 0 := by
  have h1 := D_east hf hg (a := a) (b := b)
  rw [hD, hD] at h1
  simpa using h1.symm

lemma ΔN_eq_zero_of_D (hf : IsTiling S f) (hg : IsTiling S g)
    (hD : ∀ a b : ℤ, D S f g a b = 0) {a b : ℤ} : ΔN S f g a b = 0 := by
  have h1 := D_north hf hg (a := a) (b := b)
  rw [hD, hD] at h1
  simpa using h1.symm

lemma crE_iff_of_ΔE (hf : IsTiling S f) (hg : IsTiling S g)
    (hD : ∀ a b : ℤ, D S f g a b = 0) {a b : ℤ} : crE S f a b ↔ crE S g a b := by
  have h := ΔE_eq_zero_of_D hf hg hD (a := a) (b := b)
  by_cases hpar : Even (a + b) <;> by_cases hcf : crE S f a b <;> by_cases hcg : crE S g a b <;>
    simp [ΔE, φE, hpar, hcf, hcg] at h ⊢

lemma crN_iff_of_ΔN (hf : IsTiling S f) (hg : IsTiling S g)
    (hD : ∀ a b : ℤ, D S f g a b = 0) {a b : ℤ} : crN S f a b ↔ crN S g a b := by
  have h := ΔN_eq_zero_of_D hf hg hD (a := a) (b := b)
  by_cases hpar : Even (a + b) <;> by_cases hcf : crN S f a b <;> by_cases hcg : crN S g a b <;>
    simp [ΔN, φN, hpar, hcf, hcg] at h ⊢

/-- `D = 0` everywhere forces `f = g` on `S`. -/
lemma eq_of_D_eq_zero (hf : IsTiling S f) (hg : IsTiling S g)
    (hD : ∀ a b : ℤ, D S f g a b = 0) : ∀ c ∈ S, f c = g c := by
  intro c hc
  obtain ⟨i, j⟩ := c
  have hfc := hf.adj _ hc
  obtain hE | hW | hN | hS := adjacent_cases hfc
  · have hE' : f (i, j) = (i + 1, j) := hE
    have hcr : crN S f (i + 1) j := (crN_succ_iff hf hc).mpr hE'
    have hcrg : crN S g (i + 1) j := (crN_iff_of_ΔN hf hg hD).mp hcr
    exact hE'.trans ((crN_succ_iff hg hc).mp hcrg).symm
  · have hW' : f (i, j) = (i - 1, j) := hW
    have hcr : crN S f i j := (crN_self_iff hf hc).mpr hW'
    have hcrg : crN S g i j := (crN_iff_of_ΔN hf hg hD).mp hcr
    exact hW'.trans ((crN_self_iff hg hc).mp hcrg).symm
  · have hN' : f (i, j) = (i, j + 1) := hN
    have hcr : crE S f i (j + 1) := (crE_succ_iff hf hc).mpr hN'
    have hcrg : crE S g i (j + 1) := (crE_iff_of_ΔE hf hg hD).mp hcr
    exact hN'.trans ((crE_succ_iff hg hc).mp hcrg).symm
  · have hS' : f (i, j) = (i, j - 1) := hS
    have hcr : crE S f i j := (crE_self_iff hf hc).mpr hS'
    have hcrg : crE S g i j := (crE_iff_of_ΔE hf hg hD).mp hcr
    exact hS'.trans ((crE_self_iff hg hc).mp hcrg).symm

/-- Swapping the two tilings negates `D`. -/
lemma D_neg (hf : IsTiling S f) (hg : IsTiling S g) {a b : ℤ} :
    D S g f a b = - D S f g a b := by
  rw [D, D]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ΔE]
  ring

-- ============================================================
-- The crux hypothesis (E) and the uniqueness reduction
-- ============================================================

 /-!
## Proof strategy for the crux (E) (design document, paper-verified)

The crux is proved by a **descent argument** on the height landscape, avoiding
any walk-chasing (this is the global advantage over the main line's cascade):

1. `D` is compactly supported (`D_finite_support`) and attains a global minimum
   `v₀` (`D_exists_min`).  If `D ≥ 0` everywhere there is nothing to prove, so
   suppose the minimum is `< 0`.

2. At `v₀` every neighbour `w` has `D w ≥ D v₀`, i.e. `Δ(v₀ → w) ≥ 0`.
   Write `u_f(e) ∈ {0,1}` for the crossing indicator of an edge at `v₀` and
   `σ_e = ±1` for the black-left sign; then `Δ(v₀ → w) = 4 σ_e (u_g(e) − u_f(e))`.
   The **pattern** `u_f = 0` on the two `σ⁺` edges and `u_f = 1` on the two
   `σ⁻` edges is exactly a flippable pair of `f`, and by parity it is a
   *distasteful* pair (`not_tasteful_of_crN_pair` / `not_tasteful_of_crE_pair`).

3. If `v₀` does NOT have the pattern, there is a **bad edge**: a `σ⁺` edge with
   `u_f = 1` (then `Δ ≥ 0` forces `u_g = 1`, a shared domino) or a `σ⁻` edge
   with `u_f = 0` (then `u_g = 0`, a shared non-edge).  Move across it to `w`.
   On a bad edge `Δ = 0`, so `D w = D v₀` (still a minimum), and — crucially —
   the individual height `h_f` **strictly decreases** (by `3` across a shared
   domino, by `1` across a shared non-edge): `h_f(w) − h_f(v₀) = σ_e(1 − 4u_f(e))
   ∈ {−1, −3}`.

4. **Termination.**  The descent is non-revisiting: a revisit `v_i = v_j`
   (`i < j`) would give a simple cycle `C` on which every step has `φ_f < 0`,
   so `∑_C φ_f < 0`.  But `C` lies at level `D = −4k` inside an `f`-lower
   alternating cycle `γ₀`, hence its inside `R` satisfies `R ⊆ inside(γ₀) ⊆ S`
   (`inside_mem_S`), and the discrete Green theorem
   `∑_C φ_f = ∑_{c ∈ R} defect_f(c) = 0` (each `defect_f(c) = 0` on `S`,
   `φ_closed`) — contradiction.  So the descent reaches a pattern vertex,
   which yields the distasteful pair.

The discrete Green theorem (`∑_C φ_f = ∑_{c ∈ R} defect_f(c)` for a simple
cycle `C` with inside `R`) is the only topological input.  Its two parts:
  * finite telescoping — `∑_{c ∈ R} defect_f(c)` regroups onto the boundary
    edges, interior edges cancelling (PROVED: `sum_defect`), so for `R ⊆ S`
    the boundary sum of `φ f` is `0` (PROVED: `boundary_sum_eq_zero`);
  * the walk–boundary relation — a simple closed walk `C` is the boundary of
    its inside `R` (the discrete Jordan curve theorem), and the enclosure
    `R ⊆ S` (via `inside_mem_S`).  These two Jordan facts are the remaining
    formalization work; everything else in the route is complete.
-/
/-- The crux (E): if `f` is ever strictly lower than `g` (height-difference `D < 0`),
then `f` has a distasteful pair.  This is the remaining content of the theorem;
it is proved below via the descent argument (see `cruxE`). -/
def CruxE : Prop :=
  ∀ (S : Finset Cell) (f g : Cell → Cell), IsTiling S f → IsTiling S g →
    ComplConnected S → (∃ v : Cell, D S f g v.1 v.2 < 0) →
    (∃ a b : ℤ, (crN S f a b ∧ crN S f a (b - 1) ∧ Even (a + b)) ∨
      (crE S f a b ∧ crE S f (a - 1) b ∧ Odd (a + b)))

/-- Uniqueness of the tasteful tiling, reduced to the crux (E). -/
theorem unique_tasteful_of_cruxE (hE : CruxE) (hcc : ComplConnected S)
    (hf : IsTiling S f) (hg : IsTiling S g) (htf : Tasteful S f) (htg : Tasteful S g) :
    ∀ c ∈ S, f c = g c := by
  classical
  -- D ≥ 0 everywhere (else (E) gives a poison pair of f)
  have hge : ∀ a b : ℤ, 0 ≤ D S f g a b := by
    by_contra h
    push_neg at h
    obtain ⟨av, bv, hv⟩ := h
    have hneg : ∃ v : Cell, D S f g v.1 v.2 < 0 := ⟨(av, bv), hv⟩
    obtain ⟨a, b, hpoison⟩ := hE S f g hf hg hcc hneg
    rcases hpoison with ⟨h1, h2, hpar⟩ | ⟨h1, h2, hpar⟩
    · exact not_tasteful_of_crN_pair htf h1 h2 hpar
    · exact not_tasteful_of_crE_pair htf h1 h2 hpar
  -- symmetric: D(g,f) ≥ 0, i.e. D(f,g) ≤ 0
  have hle : ∀ a b : ℤ, D S f g a b ≤ 0 := by
    have hge' : ∀ a b : ℤ, 0 ≤ D S g f a b := by
      by_contra h
      push_neg at h
      obtain ⟨av, bv, hv⟩ := h
      have hneg : ∃ v : Cell, D S g f v.1 v.2 < 0 := ⟨(av, bv), hv⟩
      obtain ⟨a, b, hpoison⟩ := hE S g f hg hf hcc hneg
      rcases hpoison with ⟨h1, h2, hpar⟩ | ⟨h1, h2, hpar⟩
      · exact not_tasteful_of_crN_pair htg h1 h2 hpar
      · exact not_tasteful_of_crE_pair htg h1 h2 hpar
    intro a b
    have h2 := hge' a b
    rw [D_neg hf hg] at h2
    linarith
  have hD : ∀ a b : ℤ, D S f g a b = 0 := fun a b ↦ le_antisymm (hle a b) (hge a b)
  exact eq_of_D_eq_zero hf hg hD

-- ============================================================
-- Discrete Green theorem: the cell-defect telescoping
-- ============================================================

/-- The cell defect: the ccw boundary sum of the height 1-form around a cell.
Vanishes on cells of `S` (`φ_closed`). -/
noncomputable def defect (S : Finset Cell) (f : Cell → Cell) (c : Cell) : ℤ :=
  φE S f c.1 c.2 + φN S f (c.1 + 1) c.2 - φE S f c.1 (c.2 + 1) - φN S f c.1 c.2

lemma defect_eq_zero_of_mem (hf : IsTiling S f) {c : Cell} (hc : c ∈ S) : defect S f c = 0 := by
  obtain ⟨i, j⟩ := c
  exact φ_closed hf hc

/-- The defect of a cell outside `S` is `+4` (black) or `−4` (white). -/
lemma defect_of_not_mem (hf : IsTiling S f) {c : Cell} (hc : c ∉ S) :
    defect S f c = if Even (c.1 + c.2) then 4 else -4 := by
  obtain ⟨i, j⟩ := c
  have hfE := crE_of_not_mem hf hc
  have hfN := crN_of_not_mem hf hc
  have hfE1 : ¬ crE S f i (j + 1) := fun ⟨hmem, _⟩ ↦ hc (by simpa using hmem)
  have hfN1 : ¬ crN S f (i + 1) j := by
    rintro ⟨hmem, -⟩
    exact hc (by simpa using hmem)
  simp only [defect, φE, φN, hfE, hfN, hfE1, hfN1, if_false]
  by_cases hp : Even (i + j) <;>
    simp [hp, show Even (i + 1 + j) ↔ ¬ Even (i + j) from by
      rw [show i + 1 + j = (i + j) + 1 from by ring]; exact even_add_one_int _,
      show Even (i + (j + 1)) ↔ ¬ Even (i + j) from by
      rw [show i + (j + 1) = (i + j) + 1 from by ring]; exact even_add_one_int _] <;>
    ring

/-- The telescoping identity: the sum of defects over a finite region regroups
onto the boundary edges.  This is the discrete Green theorem in raw form. -/
lemma sum_defect (R : Finset Cell) :
    ∑ c ∈ R, defect S f c =
      (∑ c ∈ R, φE S f c.1 c.2 - ∑ c ∈ R.image (fun c ↦ (c.1, c.2 + 1)), φE S f c.1 c.2)
      + (∑ c ∈ R.image (fun c ↦ (c.1 + 1, c.2)), φN S f c.1 c.2 - ∑ c ∈ R, φN S f c.1 c.2) := by
  have himg1 : Function.Injective (fun c : Cell ↦ (c.1, c.2 + 1)) := by
    intro a b h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext_iff.mpr ⟨h.1, by omega⟩
  have himg2 : Function.Injective (fun c : Cell ↦ (c.1 + 1, c.2)) := by
    intro a b h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext_iff.mpr ⟨by omega, h.2⟩
  have e1 : ∑ c ∈ R.image (fun c : Cell ↦ (c.1, c.2 + 1)), φE S f c.1 c.2
      = ∑ c ∈ R, φE S f c.1 (c.2 + 1) := by
    rw [Finset.sum_image (fun x _ y _ h ↦ himg1 h)]
  have e2 : ∑ c ∈ R.image (fun c : Cell ↦ (c.1 + 1, c.2)), φN S f c.1 c.2
      = ∑ c ∈ R, φN S f (c.1 + 1) c.2 := by
    rw [Finset.sum_image (fun x _ y _ h ↦ himg2 h)]
  rw [e1, e2]
  simp only [defect]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

/-- For `R ⊆ S`, the boundary-edge sum of `φ f` vanishes (Green theorem). -/
lemma boundary_sum_eq_zero (hf : IsTiling S f) {R : Finset Cell} (hR : R ⊆ S) :
    (∑ c ∈ R, φE S f c.1 c.2 - ∑ c ∈ R.image (fun c ↦ (c.1, c.2 + 1)), φE S f c.1 c.2)
      + (∑ c ∈ R.image (fun c ↦ (c.1 + 1, c.2)), φN S f c.1 c.2 - ∑ c ∈ R, φN S f c.1 c.2) = 0 := by
  rw [← sum_defect]
  apply Finset.sum_eq_zero
  intro c hc
  exact defect_eq_zero_of_mem hf (hR hc)

-- ============================================================
-- Jordan machinery for a generic simple closed walk on the grid
-- (port of the main line's cell-walk `Ncount`/`inside` machinery;
--  used for the descent cycle, which is a VERTEX walk — the enclosed
--  objects are the CELLS, counted by the same east-ray rule)
-- ============================================================

section JordanWalk

variable {w : ℕ → Cell} {n : ℕ}

/-- Consecutive vertices of a simple closed walk are distinct. -/
lemma walkV_ne_succ (hn : 4 ≤ n) (hinj : ∀ i < n, ∀ j < n, w i = w j → i = j)
    (hret : w n = w 0) (i : ℕ) (hi : i < n) : w i ≠ w (i + 1) := by
  intro h
  by_cases hi1 : i + 1 < n
  · have h1 := hinj i hi (i + 1) hi1 h
    omega
  · have hi1' : i + 1 = n := by omega
    have h2 : w i = w 0 := by rw [hi1', hret] at h; exact h
    have h0 : i = 0 := hinj i hi 0 (by omega) h2
    rw [h0] at h
    have h1 := hinj 0 (by omega) 1 (by omega) h
    omega

/-- The edge set of the walk (unordered consecutive pairs). -/
noncomputable def cycEdgesV (w : ℕ → Cell) (n : ℕ) : Finset (Finset Cell) :=
  (Finset.range n).image fun i ↦ {w i, w (i + 1)}

lemma mem_cycEdgesV {w : ℕ → Cell} {n : ℕ} {e : Finset Cell} :
    e ∈ cycEdgesV w n ↔ ∃ i ∈ Finset.range n, {w i, w (i + 1)} = e :=
  Finset.mem_image

lemma pair_eq_pairV {a b c d : Cell} (ha : a ≠ b) (h : ({a, b} : Finset Cell) = {c, d}) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have h1 : a ∈ ({c, d} : Finset Cell) := h ▸ Finset.mem_insert_self _ _
  have h2 : b ∈ ({c, d} : Finset Cell) := h ▸ Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
  rw [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  rcases h1 with h1 | h1
  · subst h1
    rcases h2 with h2 | h2
    · exact absurd h2.symm ha
    · exact Or.inl ⟨rfl, h2⟩
  · subst h1
    rcases h2 with h2 | h2
    · exact Or.inr ⟨rfl, h2⟩
    · exact absurd h2.symm ha

/-- The edges of a simple closed walk are distinct. -/
lemma cycEdgesV_inj (hn : 4 ≤ n) (hinj : ∀ i < n, ∀ j < n, w i = w j → i = j)
    (hret : w n = w 0) {i j : ℕ} (hi : i < n) (hj : j < n)
    (h : ({w i, w (i + 1)} : Finset Cell) = {w j, w (j + 1)}) : i = j := by
  have hne : w i ≠ w (i + 1) := walkV_ne_succ hn hinj hret i hi
  have hp := pair_eq_pairV hne h
  rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hinj i hi j hj h1
  · by_cases hji : j + 1 < n
    · have e1 : i = j + 1 := hinj i hi (j + 1) hji h1
      have e2 : i + 1 = j := by
        by_cases hi1 : i + 1 < n
        · exact hinj (i + 1) hi1 j hj h2
        · have hi1' : i + 1 = n := by omega
          rw [hi1', hret] at h2
          have h0j := hinj 0 (by omega) j hj h2
          omega
      omega
    · have hj' : j = n - 1 := by omega
      rw [hj'] at h1 h2
      have hjn : n - 1 + 1 = n := by omega
      rw [hjn, hret] at h1
      have e1 : i = 0 := hinj i hi 0 (by omega) h1
      have hi1 : i + 1 < n := by omega
      have hj1 : n - 1 < n := by omega
      have e2 : i + 1 = n - 1 := hinj (i + 1) hi1 (n - 1) hj1 h2
      omega

lemma edge_of_verticalV (i : ℕ) (hx : (w i).1 = (w (i + 1)).1)
    {y : ℤ} (hy : ((w i).2 = y ∧ (w (i + 1)).2 = y + 1) ∨
      ((w i).2 = y + 1 ∧ (w (i + 1)).2 = y)) :
    ({w i, w (i + 1)} : Finset Cell) = {((w i).1, y), ((w i).1, y + 1)} := by
  rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have e1 : w i = ((w i).1, y) := by ext <;> simp [h1]
    have e2 : w (i + 1) = ((w i).1, y + 1) := by ext <;> simp [hx, h2]
    rw [e1, e2]
  · have e1 : w i = ((w i).1, y + 1) := by ext <;> simp [h1]
    have e2 : w (i + 1) = ((w i).1, y) := by ext <;> simp [hx, h2]
    rw [e1, e2]
    ext x
    simp [Finset.mem_insert, Finset.mem_singleton]
    tauto

/-- At most one walk edge is vertical with given column `a` and min-height `y`. -/
lemma cycEdgesV_le_one (hn : 4 ≤ n) (hinj : ∀ i < n, ∀ j < n, w i = w j → i = j)
    (hret : w n = w 0) (a y : ℤ) :
    ((Finset.range n).filter fun i ↦ (w i).1 = a ∧ (w (i + 1)).1 = a ∧
      ((w i).2 = y ∧ (w (i + 1)).2 = y + 1 ∨
       (w i).2 = y + 1 ∧ (w (i + 1)).2 = y)).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro i j hi hj
  rw [Finset.mem_filter] at hi hj
  obtain ⟨hi1, hia, hia', hiy⟩ := hi
  obtain ⟨hj1, hja, hja', hjy⟩ := hj
  apply cycEdgesV_inj hn hinj hret (Finset.mem_range.mp hi1) (Finset.mem_range.mp hj1)
  have hxi : (w i).1 = (w (i + 1)).1 := by rw [hia, hia']
  have hxj : (w j).1 = (w (j + 1)).1 := by rw [hja, hja']
  have ei := edge_of_verticalV i hxi hiy
  have ej := edge_of_verticalV j hxj hjy
  rw [hia] at ei
  rw [hja] at ej
  rw [ei, ej]

/-- Vertical-edge ray count: walk edges that are vertical, in column `> c.1`,
and spanning rows `c.2` to `c.2+1`. -/
noncomputable def NcountV (w : ℕ → Cell) (n : ℕ) (c : Cell) : ℕ :=
  ((Finset.range n).filter fun i ↦ (w i).1 = (w (i + 1)).1 ∧ c.1 < (w i).1 ∧
    ((w i).2 = c.2 ∧ (w (i + 1)).2 = c.2 + 1 ∨
     (w i).2 = c.2 + 1 ∧ (w (i + 1)).2 = c.2)).card

/-- `insideV c`: the even-odd rule with an eastward ray. -/
noncomputable def insideV (w : ℕ → Cell) (n : ℕ) (c : Cell) : Prop := Odd (NcountV w n c)

lemma edge_of_horizontalV (i : ℕ) (hx : (w i).2 = (w (i + 1)).2)
    {x : ℤ} (hy : ((w i).1 = x ∧ (w (i + 1)).1 = x + 1) ∨
      ((w i).1 = x + 1 ∧ (w (i + 1)).1 = x)) :
    ({w i, w (i + 1)} : Finset Cell) = {(x, (w i).2), (x + 1, (w i).2)} := by
  rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have e1 : w i = (x, (w i).2) := by ext <;> simp [h1]
    have e2 : w (i + 1) = (x + 1, (w i).2) := by ext <;> simp [hx, h2]
    rw [e1, e2]
  · have e1 : w i = (x + 1, (w i).2) := by ext <;> simp [h1]
    have e2 : w (i + 1) = (x, (w i).2) := by ext <;> simp [hx, h2]
    rw [e1, e2]
    ext y
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto

/-- At most one walk edge is horizontal with given row `y` and min-column `x`. -/
lemma cycEdgesV_le_one_h (hn : 4 ≤ n) (hinj : ∀ i < n, ∀ j < n, w i = w j → i = j)
    (hret : w n = w 0) (x y : ℤ) :
    ((Finset.range n).filter fun i ↦ (w i).2 = y ∧ (w (i + 1)).2 = y ∧
      ((w i).1 = x ∧ (w (i + 1)).1 = x + 1 ∨
       (w i).1 = x + 1 ∧ (w (i + 1)).1 = x)).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro i j hi hj
  rw [Finset.mem_filter] at hi hj
  obtain ⟨hi1, hia, hia', hiy⟩ := hi
  obtain ⟨hj1, hja, hja', hjy⟩ := hj
  apply cycEdgesV_inj hn hinj hret (Finset.mem_range.mp hi1) (Finset.mem_range.mp hj1)
  have hxi : (w i).2 = (w (i + 1)).2 := by rw [hia, hia']
  have hxj : (w j).2 = (w (j + 1)).2 := by rw [hja, hja']
  have ei := edge_of_horizontalV i hxi hiy
  have ej := edge_of_horizontalV j hxj hjy
  rw [hia] at ei
  rw [hja] at ej
  rw [ei, ej]

/-- Decomposition of `NcountV` along an eastward step. -/
lemma NcountV_east (hn : 4 ≤ n) (hinj : ∀ i < n, ∀ j < n, w i = w j → i = j)
    (hret : w n = w 0) (c : Cell) :
    NcountV w n c = NcountV w n (c.1 + 1, c.2) +
      (if ({(c.1 + 1, c.2), (c.1 + 1, c.2 + 1)} : Finset Cell) ∈ cycEdgesV w n then 1 else 0) := by
  classical
  unfold NcountV
  have hdecomp : (Finset.range n).filter
      (fun i ↦ (w i).1 = (w (i + 1)).1 ∧ c.1 < (w i).1 ∧
        ((w i).2 = c.2 ∧ (w (i + 1)).2 = c.2 + 1 ∨
         (w i).2 = c.2 + 1 ∧ (w (i + 1)).2 = c.2)) =
    (Finset.range n).filter
      (fun i ↦ (w i).1 = (w (i + 1)).1 ∧ c.1 + 1 < (w i).1 ∧
        ((w i).2 = c.2 ∧ (w (i + 1)).2 = c.2 + 1 ∨
         (w i).2 = c.2 + 1 ∧ (w (i + 1)).2 = c.2)) ∪
    (Finset.range n).filter
      (fun i ↦ (w i).1 = (w (i + 1)).1 ∧ (w i).1 = c.1 + 1 ∧
        ((w i).2 = c.2 ∧ (w (i + 1)).2 = c.2 + 1 ∨
         (w i).2 = c.2 + 1 ∧ (w (i + 1)).2 = c.2)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · intro h
      obtain ⟨h1, h2, h3, h4⟩ := h
      by_cases hx : (w i).1 = c.1 + 1
      · exact Or.inr ⟨h1, h2, hx, h4⟩
      · exact Or.inl ⟨h1, h2, by omega, h4⟩
    · intro h
      rcases h with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
      · exact ⟨h1, h2, by omega, h4⟩
      · exact ⟨h1, h2, by omega, h4⟩
  rw [hdecomp, Finset.card_union_of_disjoint (by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    rw [Finset.mem_filter] at hi1 hi2
    omega)]
  congr 1
  have hextra : ((Finset.range n).filter fun i ↦ (w i).1 = (w (i + 1)).1 ∧
      (w i).1 = c.1 + 1 ∧
      ((w i).2 = c.2 ∧ (w (i + 1)).2 = c.2 + 1 ∨
       (w i).2 = c.2 + 1 ∧ (w (i + 1)).2 = c.2)).card =
      if ({(c.1 + 1, c.2), (c.1 + 1, c.2 + 1)} : Finset Cell) ∈ cycEdgesV w n then 1 else 0 := by
    by_cases h : ({(c.1 + 1, c.2), (c.1 + 1, c.2 + 1)} : Finset Cell) ∈ cycEdgesV w n
    · rw [if_pos h]
      rw [mem_cycEdgesV] at h
      obtain ⟨i, hi, hi2⟩ := h
      have hset : (Finset.range n).filter (fun i' ↦ (w i').1 = (w (i' + 1)).1 ∧
          (w i').1 = c.1 + 1 ∧
          ((w i').2 = c.2 ∧ (w (i' + 1)).2 = c.2 + 1 ∨
           (w i').2 = c.2 + 1 ∧ (w (i' + 1)).2 = c.2)) = {i} := by
        ext i'
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · intro hi'
          obtain ⟨h1, h2, h3, h4⟩ := hi'
          have hxi' : (w i').1 = (w (i' + 1)).1 := h2
          have ei' := edge_of_verticalV i' hxi' h4
          have hia' : (w (i' + 1)).1 = c.1 + 1 := by rw [← h2, h3]
          rw [h3] at ei'
          have : ({w i', w (i' + 1)} : Finset Cell) = {w i, w (i + 1)} := by rw [ei', hi2]
          exact cycEdgesV_inj hn hinj hret (Finset.mem_range.mp h1) (Finset.mem_range.mp hi) this
        · intro hi'
          rw [hi']
          have hne : w i ≠ w (i + 1) := walkV_ne_succ hn hinj hret i (Finset.mem_range.mp hi)
          rcases pair_eq_pairV hne hi2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
          · rw [e1, e2]
            exact ⟨hi, by simp, by simp, Or.inl ⟨by simp, by simp⟩⟩
          · rw [e1, e2]
            exact ⟨hi, by simp, by simp, Or.inr ⟨by simp, by simp⟩⟩
      rw [hset, Finset.card_singleton]
    · rw [if_neg h]
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro i hi
      rw [Finset.mem_filter] at hi
      obtain ⟨h1, h2, h3, h4⟩ := hi
      apply h
      rw [mem_cycEdgesV]
      have hxi : (w i).1 = (w (i + 1)).1 := h2
      have ei := edge_of_verticalV i hxi h4
      have hia' : (w (i + 1)).1 = c.1 + 1 := by rw [← h2, h3]
      rw [h3] at ei
      exact ⟨i, h1, ei⟩
  rw [hextra]

/-- Horizontal-edge ray count. -/
noncomputable def NscountV (w : ℕ → Cell) (n : ℕ) (c : Cell) : ℕ :=
  ((Finset.range n).filter fun i ↦ (w i).2 = (w (i + 1)).2 ∧
    (w i).2 < c.2 ∧
    ((w i).1 = c.1 ∧ (w (i + 1)).1 = c.1 + 1 ∨
     (w i).1 = c.1 + 1 ∧ (w (i + 1)).1 = c.1)).card

/-- Decomposition of `NscountV` along a southward step. -/
lemma NscountV_south (hn : 4 ≤ n) (hinj : ∀ i < n, ∀ j < n, w i = w j → i = j)
    (hret : w n = w 0) (c : Cell) :
    NscountV w n (c.1, c.2 + 1) = NscountV w n c +
      (if ({(c.1, c.2), (c.1 + 1, c.2)} : Finset Cell) ∈ cycEdgesV w n then 1 else 0) := by
  classical
  unfold NscountV
  have hdecomp : (Finset.range n).filter
      (fun i ↦ (w i).2 = (w (i + 1)).2 ∧ (w i).2 < c.2 + 1 ∧
        ((w i).1 = c.1 ∧ (w (i + 1)).1 = c.1 + 1 ∨
         (w i).1 = c.1 + 1 ∧ (w (i + 1)).1 = c.1)) =
    (Finset.range n).filter
      (fun i ↦ (w i).2 = (w (i + 1)).2 ∧ (w i).2 < c.2 ∧
        ((w i).1 = c.1 ∧ (w (i + 1)).1 = c.1 + 1 ∨
         (w i).1 = c.1 + 1 ∧ (w (i + 1)).1 = c.1)) ∪
    (Finset.range n).filter
      (fun i ↦ (w i).2 = (w (i + 1)).2 ∧ (w i).2 = c.2 ∧
        ((w i).1 = c.1 ∧ (w (i + 1)).1 = c.1 + 1 ∨
         (w i).1 = c.1 + 1 ∧ (w (i + 1)).1 = c.1)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · intro h
      obtain ⟨h1, h2, h3, h4⟩ := h
      by_cases hx : (w i).2 = c.2
      · exact Or.inr ⟨h1, h2, hx, h4⟩
      · exact Or.inl ⟨h1, h2, by omega, h4⟩
    · intro h
      rcases h with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
      · exact ⟨h1, h2, by omega, h4⟩
      · exact ⟨h1, h2, by omega, h4⟩
  rw [hdecomp, Finset.card_union_of_disjoint (by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    rw [Finset.mem_filter] at hi1 hi2
    omega)]
  congr 1
  have hextra : ((Finset.range n).filter fun i ↦ (w i).2 = (w (i + 1)).2 ∧
      (w i).2 = c.2 ∧
      ((w i).1 = c.1 ∧ (w (i + 1)).1 = c.1 + 1 ∨
       (w i).1 = c.1 + 1 ∧ (w (i + 1)).1 = c.1)).card =
      if ({(c.1, c.2), (c.1 + 1, c.2)} : Finset Cell) ∈ cycEdgesV w n then 1 else 0 := by
    by_cases h : ({(c.1, c.2), (c.1 + 1, c.2)} : Finset Cell) ∈ cycEdgesV w n
    · rw [if_pos h]
      rw [mem_cycEdgesV] at h
      obtain ⟨i, hi, hi2⟩ := h
      have hset : (Finset.range n).filter (fun i' ↦ (w i').2 = (w (i' + 1)).2 ∧
          (w i').2 = c.2 ∧
          ((w i').1 = c.1 ∧ (w (i' + 1)).1 = c.1 + 1 ∨
           (w i').1 = c.1 + 1 ∧ (w (i' + 1)).1 = c.1)) = {i} := by
        ext i'
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · intro hi'
          obtain ⟨h1, h2, h3, h4⟩ := hi'
          have hxi' : (w i').2 = (w (i' + 1)).2 := h2
          have ei' := edge_of_horizontalV i' hxi' h4
          have hia' : (w (i' + 1)).2 = c.2 := by rw [← h2, h3]
          rw [h3] at ei'
          have : ({w i', w (i' + 1)} : Finset Cell) = {w i, w (i + 1)} := by rw [ei', hi2]
          exact cycEdgesV_inj hn hinj hret (Finset.mem_range.mp h1) (Finset.mem_range.mp hi) this
        · intro hi'
          rw [hi']
          have hne : w i ≠ w (i + 1) := walkV_ne_succ hn hinj hret i (Finset.mem_range.mp hi)
          rcases pair_eq_pairV hne hi2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
          · rw [e1, e2]
            exact ⟨hi, by simp, by simp, Or.inl ⟨by simp, by simp⟩⟩
          · rw [e1, e2]
            exact ⟨hi, by simp, by simp, Or.inr ⟨by simp, by simp⟩⟩
      rw [hset, Finset.card_singleton]
    · rw [if_neg h]
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro i hi
      rw [Finset.mem_filter] at hi
      obtain ⟨h1, h2, h3, h4⟩ := hi
      apply h
      rw [mem_cycEdgesV]
      have hxi : (w i).2 = (w (i + 1)).2 := h2
      have ei := edge_of_horizontalV i hxi h4
      have hia' : (w (i + 1)).2 = c.2 := by rw [← h2, h3]
      rw [h3] at ei
      exact ⟨i, h1, ei⟩
  rw [hextra]

/-- Handshake: the number of walk edges crossing a finset `U` is even. -/
lemma even_crossingsV (hret : w n = w 0) (U : Finset Cell) :
    Even ((Finset.range n).filter
      (fun i ↦ (w i ∈ U) ≠ (w (i + 1) ∈ U))).card := by
  classical
  set a : ℕ → ℕ := fun i ↦ if w i ∈ U then 1 else 0
  have ha0 : a 0 = a n := by
    simp only [a]
    rw [hret]
  have hshift : ∑ i ∈ Finset.range n, a (i + 1) = ∑ i ∈ Finset.range n, a i := by
    have h1 := Finset.sum_range_succ' a n
    have h2 := Finset.sum_range_succ a n
    rw [← ha0] at h2
    omega
  have hsum : ∑ i ∈ Finset.range n, (a i + a (i + 1)) = 2 * ∑ i ∈ Finset.range n, a i := by
    rw [Finset.sum_add_distrib, hshift]
    ring
  have hboth : ((Finset.range n).filter (fun i ↦ w i ∈ U ∧ w (i + 1) ∈ U)).card =
      ∑ i ∈ Finset.range n, a i * a (i + 1) := by
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [a]
    split_ifs with h1 h2 h2 <;> simp_all
  have hcross : ((Finset.range n).filter (fun i ↦ (w i ∈ U) ≠ (w (i + 1) ∈ U))).card =
      ∑ i ∈ Finset.range n, (a i + a (i + 1) - 2 * (a i * a (i + 1))) := by
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [a]
    split_ifs with h1 h2 h2 <;> simp_all
  have key : ((Finset.range n).filter (fun i ↦ (w i ∈ U) ≠ (w (i + 1) ∈ U))).card +
      2 * ((Finset.range n).filter (fun i ↦ w i ∈ U ∧ w (i + 1) ∈ U)).card =
      2 * ∑ i ∈ Finset.range n, a i := by
    rw [hcross, hboth]
    have hterm : ∑ i ∈ Finset.range n, (a i + a (i + 1) - 2 * (a i * a (i + 1))) +
        2 * ∑ i ∈ Finset.range n, a i * a (i + 1) =
        ∑ i ∈ Finset.range n, (a i + a (i + 1) - 2 * (a i * a (i + 1)) + 2 * (a i * a (i + 1))) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    rw [hterm]
    have hterm2 : ∑ i ∈ Finset.range n, (a i + a (i + 1) - 2 * (a i * a (i + 1)) + 2 * (a i * a (i + 1))) =
        ∑ i ∈ Finset.range n, (a i + a (i + 1)) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [a]
      split_ifs with h1 h2 h2 <;> simp_all
    rw [hterm2, hsum]
  have hfin : ((Finset.range n).filter (fun i ↦ (w i ∈ U) ≠ (w (i + 1) ∈ U))).card =
      2 * (∑ i ∈ Finset.range n, a i -
        ((Finset.range n).filter (fun i ↦ w i ∈ U ∧ w (i + 1) ∈ U)).card) := by
    omega
  rw [hfin]
  exact even_two_mul _

/-- The set of walk vertices. -/
noncomputable def cycSetV (w : ℕ → Cell) (n : ℕ) : Finset Cell :=
  (Finset.range n).image w

lemma mem_cycSetV {w : ℕ → Cell} {n : ℕ} {c : Cell} :
    c ∈ cycSetV w n ↔ ∃ i ∈ Finset.range n, w i = c :=
  Finset.mem_image

lemma edge_cells_mem_cycSetV (hret : w n = w 0) {e : Finset Cell} {a b : Cell}
    (he : e ∈ cycEdgesV w n) (hab : e = {a, b}) : a ∈ cycSetV w n ∧ b ∈ cycSetV w n := by
  rw [mem_cycEdgesV] at he
  obtain ⟨i, hi, hei⟩ := he
  rw [hab] at hei
  have h1 : a ∈ ({w i, w (i + 1)} : Finset Cell) := by
    rw [hei]
    exact Finset.mem_insert_self _ _
  have h2 : b ∈ ({w i, w (i + 1)} : Finset Cell) := by
    rw [hei]
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
  rw [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  have second : w (i + 1) ∈ cycSetV w n := by
    rw [mem_cycSetV]
    by_cases hi1 : i + 1 < n
    · exact ⟨i + 1, Finset.mem_range.mpr hi1, rfl⟩
    · have hlt := Finset.mem_range.mp hi
      have hi1' : i + 1 = n := by omega
      have hpos : 0 < n := by omega
      refine ⟨0, Finset.mem_range.mpr hpos, ?_⟩
      rw [show w (i + 1) = w 0 from by rw [hi1']; exact hret]
  constructor
  · rcases h1 with h1 | h1
    · rw [mem_cycSetV]
      exact ⟨i, hi, h1.symm⟩
    · rw [h1]
      exact second
  · rcases h2 with h2 | h2
    · rw [mem_cycSetV]
      exact ⟨i, hi, h2.symm⟩
    · rw [h2]
      exact second

/-- Box rule: `NcountV c + NscountV (c+(0,1))` is even. -/
lemma box_ruleV (hn : 4 ≤ n) (hadj : ∀ i < n, Adjacent (w i) (w (i + 1)))
    (hinj : ∀ i < n, ∀ j < n, w i = w j → i = j) (hret : w n = w 0) (c : Cell) :
    Even (NcountV w n c + NscountV w n (c.1, c.2 + 1)) := by
  classical
  have hn0 : 0 < n := by omega
  have hne : (cycSetV w n).Nonempty := by
    refine ⟨w 0, ?_⟩
    rw [mem_cycSetV]
    exact ⟨0, Finset.mem_range.mpr hn0, rfl⟩
  set M := ((cycSetV w n).image (·.1)).max' (hne.image _)
  set m₀ := ((cycSetV w n).image (·.2)).min' (hne.image _)
  have hM : ∀ x ∈ cycSetV w n, x.1 ≤ M := fun x hx ↦ Finset.le_max' _ _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  have hm₀ : ∀ x ∈ cycSetV w n, m₀ ≤ x.2 := fun x hx ↦ Finset.min'_le _ _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  have hbds : ∀ i ≤ n, (w i).1 ≤ M ∧ m₀ ≤ (w i).2 := by
    intro i hi
    by_cases hi' : i < n
    · have hmem : w i ∈ cycSetV w n := by
        rw [mem_cycSetV]
        exact ⟨i, Finset.mem_range.mpr hi', rfl⟩
      exact ⟨hM _ hmem, hm₀ _ hmem⟩
    · have hi'' : i = n := by omega
      rw [hi'', hret]
      have hmem : w 0 ∈ cycSetV w n := by
        rw [mem_cycSetV]
        exact ⟨0, Finset.mem_range.mpr hn0, rfl⟩
      exact ⟨hM _ hmem, hm₀ _ hmem⟩
  set U : Finset Cell := Finset.Icc (c.1 + 1) M ×ˢ Finset.Icc m₀ c.2
  have hcross := even_crossingsV hret U
  have hUx : ∀ x : Cell, (x ∈ U ↔ (c.1 + 1 ≤ x.1 ∧ x.1 ≤ M) ∧ (m₀ ≤ x.2 ∧ x.2 ≤ c.2)) := by
    intro x
    simp [U]
  have hne_iff : ∀ p q : Prop, (p ≠ q) ↔ (p ∧ ¬ q) ∨ (¬ p ∧ q) := by
    intro p q
    by_cases hp : p <;> by_cases hq : q <;> simp_all
  have hc : ∀ i ∈ Finset.range n, ((w i ∈ U) ≠ (w (i + 1) ∈ U)) ↔
      ((w i).1 = (w (i + 1)).1 ∧ c.1 < (w i).1 ∧
        ((w i).2 = c.2 ∧ (w (i + 1)).2 = c.2 + 1 ∨
         (w i).2 = c.2 + 1 ∧ (w (i + 1)).2 = c.2)) ∨
      ((w i).2 = (w (i + 1)).2 ∧ (w i).2 < c.2 + 1 ∧
        ((w i).1 = c.1 ∧ (w (i + 1)).1 = c.1 + 1 ∨
         (w i).1 = c.1 + 1 ∧ (w (i + 1)).1 = c.1)) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hb1 := hbds i (by omega)
    have hadj_i := hadj i hi'
    rw [hne_iff]
    rcases adjacent_cases hadj_i with ha | ha | ha | ha
    · -- walk (i+1) = (x+1, y): horizontal right
      have hb2 := hbds (i + 1) (by omega)
      rw [ha] at hb2
      simp at hb2
      have hA : w i ∈ U → w (i + 1) ∈ U := by
        intro h
        rw [hUx] at h ⊢
        rw [ha] at ⊢
        obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
        exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
      have hA' : (w i ∉ U ∧ w (i + 1) ∈ U) ↔
          ((w i).2 ≤ c.2 ∧ (w i).1 = c.1) := by
        constructor
        · intro h
          obtain ⟨h1, h2⟩ := h
          rw [hUx] at h1 h2
          rw [ha] at h2
          obtain ⟨⟨h21, h22⟩, h23, h24⟩ := h2
          have : (w i).1 < c.1 + 1 ∨ (w i).2 > c.2 := by
            by_contra hcon
            push_neg at hcon
            exact h1 ⟨⟨hcon.1, hb1.1⟩, hb1.2, hcon.2⟩
          rcases this with hthis | hthis
          · exact ⟨by omega, by omega⟩
          · exfalso; omega
        · intro h
          obtain ⟨h1, h2⟩ := h
          constructor
          · rw [hUx]
            omega
          · rw [ha]
            rw [hUx]
            exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
      constructor
      · intro h
        rcases h with h | h
        · exact absurd (hA h.1) h.2
        · rw [hA'] at h
          obtain ⟨h1, h2⟩ := h
          refine Or.inr ⟨?_, ?_, Or.inl ⟨?_, ?_⟩⟩
          · rw [ha]
          · omega
          · omega
          · rw [ha]
            simp [h2]
      · intro h
        rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · rw [ha] at h1
          simp at h1
        · rcases h3 with ⟨h3, h4⟩ | ⟨h3, h4⟩
          · right
            rw [hA']
            exact ⟨by omega, by omega⟩
          · rw [ha] at h4
            simp at h4
            omega
    · -- walk (i+1) = (x-1, y): horizontal left
      have hb2 := hbds (i + 1) (by omega)
      rw [ha] at hb2
      simp at hb2
      have hC : w (i + 1) ∈ U → w i ∈ U := by
        intro h
        rw [ha] at h
        rw [hUx] at h ⊢
        obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
        exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
      have hC' : (w i ∈ U ∧ w (i + 1) ∉ U) ↔
          ((w i).2 ≤ c.2 ∧ (w i).1 = c.1 + 1) := by
        constructor
        · intro h
          obtain ⟨h1, h2⟩ := h
          rw [hUx] at h1 h2
          rw [ha] at h2
          obtain ⟨⟨h11, h12⟩, h13, h14⟩ := h1
          have : (w i).1 < c.1 + 2 := by
            by_contra hcon
            push_neg at hcon
            exact h2 ⟨⟨by omega, by omega⟩, by omega, by omega⟩
          exact ⟨by omega, by omega⟩
        · intro h
          obtain ⟨h1, h2⟩ := h
          constructor
          · rw [hUx]
            exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
          · rw [ha]
            rw [hUx]
            omega
      constructor
      · intro h
        rcases h with h | h
        · rw [hC'] at h
          obtain ⟨h1, h2⟩ := h
          refine Or.inr ⟨?_, ?_, Or.inr ⟨?_, ?_⟩⟩
          · rw [ha]
          · omega
          · omega
          · rw [ha]
            simp [h2]
        · exact absurd (hC h.2) h.1
      · intro h
        rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · rw [ha] at h1
          simp at h1
          omega
        · rcases h3 with ⟨h3, h4⟩ | ⟨h3, h4⟩
          · rw [ha] at h4
            simp at h4
            omega
          · left
            rw [hC']
            exact ⟨by omega, by omega⟩
    · -- walk (i+1) = (x, y+1): vertical up
      have hb2 := hbds (i + 1) (by omega)
      rw [ha] at hb2
      simp at hb2
      have hB : w (i + 1) ∈ U → w i ∈ U := by
        intro h
        rw [ha] at h
        rw [hUx] at h ⊢
        obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
        exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
      have hB' : (w i ∈ U ∧ w (i + 1) ∉ U) ↔
          (c.1 < (w i).1 ∧ (w i).2 = c.2) := by
        constructor
        · intro h
          obtain ⟨h1, h2⟩ := h
          rw [hUx] at h1 h2
          rw [ha] at h2
          obtain ⟨⟨h11, h12⟩, h13, h14⟩ := h1
          have hy : (w i).2 = c.2 := by
            by_contra hcon
            push_neg at hcon
            apply h2
            rcases (by omega : (w i).2 < c.2 ∨ c.2 < (w i).2) with hle | hle
            · exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
            · exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
          exact ⟨by omega, by omega⟩
        · intro h
          obtain ⟨h1, h2⟩ := h
          constructor
          · rw [hUx]
            exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
          · rw [ha]
            rw [hUx]
            omega
      constructor
      · intro h
        rcases h with h | h
        · rw [hB'] at h
          obtain ⟨h1, h2⟩ := h
          refine Or.inl ⟨?_, ?_, Or.inl ⟨?_, ?_⟩⟩
          · simp [ha]
          · omega
          · omega
          · rw [ha]
            simp [h2]
        · exact absurd (hB h.2) h.1
      · intro h
        rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · rcases h3 with ⟨h3, h4⟩ | ⟨h3, h4⟩
          · left
            rw [hB']
            exact ⟨by omega, by omega⟩
          · rw [ha] at h4
            simp at h4
            omega
        · rw [ha] at h1
          simp at h1
    · -- walk (i+1) = (x, y-1): vertical down
      have hb2 := hbds (i + 1) (by omega)
      rw [ha] at hb2
      simp at hb2
      have hD : w i ∈ U → w (i + 1) ∈ U := by
        intro h
        rw [hUx] at h ⊢
        rw [ha] at ⊢
        obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
        exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
      have hD' : (w i ∉ U ∧ w (i + 1) ∈ U) ↔
          (c.1 < (w i).1 ∧ (w i).2 = c.2 + 1) := by
        constructor
        · intro h
          obtain ⟨h1, h2⟩ := h
          rw [hUx] at h1 h2
          rw [ha] at h2
          obtain ⟨⟨h21, h22⟩, h23, h24⟩ := h2
          have : (w i).2 > c.2 := by
            by_contra hcon
            push_neg at hcon
            apply h1
            rcases (by omega : (w i).1 < c.1 + 1 ∨ c.1 + 1 ≤ (w i).1) with hle | hle
            · exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
            · exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
          exact ⟨by omega, by omega⟩
        · intro h
          obtain ⟨h1, h2⟩ := h
          constructor
          · rw [hUx]
            omega
          · rw [ha]
            rw [hUx]
            exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
      constructor
      · intro h
        rcases h with h | h
        · exact absurd (hD h.1) h.2
        · rw [hD'] at h
          obtain ⟨h1, h2⟩ := h
          refine Or.inl ⟨?_, ?_, Or.inr ⟨?_, ?_⟩⟩
          · simp [ha]
          · omega
          · omega
          · rw [ha]
            simp [h2]
      · intro h
        rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · rcases h3 with ⟨h3, h4⟩ | ⟨h3, h4⟩
          · rw [ha] at h4
            simp at h4
            omega
          · right
            rw [hD']
            exact ⟨by omega, by omega⟩
        · rw [ha] at h1
          simp at h1
          omega
  have hcrossset : (Finset.range n).filter (fun i ↦ (w i ∈ U) ≠ (w (i + 1) ∈ U)) =
      (Finset.range n).filter (fun i ↦ (w i).1 = (w (i + 1)).1 ∧
        c.1 < (w i).1 ∧
        ((w i).2 = c.2 ∧ (w (i + 1)).2 = c.2 + 1 ∨
         (w i).2 = c.2 + 1 ∧ (w (i + 1)).2 = c.2)) ∪
      (Finset.range n).filter (fun i ↦ (w i).2 = (w (i + 1)).2 ∧
        (w i).2 < c.2 + 1 ∧
        ((w i).1 = c.1 ∧ (w (i + 1)).1 = c.1 + 1 ∨
         (w i).1 = c.1 + 1 ∧ (w (i + 1)).1 = c.1)) := by
    ext i
    by_cases hi : i ∈ Finset.range n
    · simp only [Finset.mem_filter, Finset.mem_union]
      rw [hc i hi]
      constructor
      · intro h
        obtain ⟨h1, h2⟩ := h
        rcases h2 with h2 | h2
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr ⟨h1, h2⟩
      · intro h
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨h1, Or.inl h2⟩
        · exact ⟨h1, Or.inr h2⟩
    · simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_range]
      simp only [Finset.mem_range] at hi
      constructor
      · intro h
        obtain ⟨h1, h2⟩ := h
        exact absurd h1 hi
      · intro h
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact absurd h1 hi
        · exact absurd h1 hi
  rw [hcrossset, Finset.card_union_of_disjoint (by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    rw [Finset.mem_filter] at hi1 hi2
    have hadj_i := hadj i (Finset.mem_range.mp hi1.1)
    rcases adjacent_cases hadj_i with ha | ha | ha | ha
    · rw [ha] at hi1; simp at hi1
    · rw [ha] at hi1; simp at hi1; omega
    · rw [ha] at hi2; simp at hi2
    · rw [ha] at hi2; simp at hi2; omega)] at hcross
  unfold NcountV NscountV
  exact hcross

/-- The box relation at a cell: `NcountV c + NscountV c + ind({c, c+(1,0)})` is even. -/
lemma box_south_relV (hn : 4 ≤ n) (hadj : ∀ i < n, Adjacent (w i) (w (i + 1)))
    (hinj : ∀ i < n, ∀ j < n, w i = w j → i = j) (hret : w n = w 0) (c : Cell) :
    Even (NcountV w n c + NscountV w n c +
      (if ({(c.1, c.2), (c.1 + 1, c.2)} : Finset Cell) ∈ cycEdgesV w n then 1 else 0)) := by
  have h1 := box_ruleV hn hadj hinj hret c
  have h2 := NscountV_south hn hinj hret c
  rw [h2] at h1
  obtain ⟨a, ha⟩ := h1
  refine ⟨a, by omega⟩

/-- Parity rule for a north step: `NcountV (c+(0,1)) + NcountV c + ind` is even. -/
lemma north_relV (hn : 4 ≤ n) (hadj : ∀ i < n, Adjacent (w i) (w (i + 1)))
    (hinj : ∀ i < n, ∀ j < n, w i = w j → i = j) (hret : w n = w 0) (c : Cell) :
    Even (NcountV w n (c.1, c.2 + 1) + NcountV w n c +
      (if ({(c.1, c.2 + 1), (c.1 + 1, c.2 + 1)} : Finset Cell) ∈ cycEdgesV w n
        then 1 else 0)) := by
  have hR1 : Even (NcountV w n (c.1, c.2 + 1) + NscountV w n (c.1, c.2 + 1) +
      (if ({(c.1, c.2 + 1), (c.1 + 1, c.2 + 1)} : Finset Cell) ∈ cycEdgesV w n
        then 1 else 0)) := box_south_relV hn hadj hinj hret (c.1, c.2 + 1)
  have hR2 := box_south_relV hn hadj hinj hret c
  have hS := NscountV_south hn hinj hret c
  rw [hS] at hR1
  obtain ⟨a, ha⟩ := hR1
  obtain ⟨b, hb⟩ := hR2
  refine ⟨a + b - (NscountV w n c +
    (if ({(c.1, c.2), (c.1 + 1, c.2)} : Finset Cell) ∈ cycEdgesV w n then 1 else 0)), by omega⟩

/-- Adjacent cells that both lie off the walk have the same inside status. -/
lemma insideV_adj_of_not_mem (hn : 4 ≤ n) (hadj : ∀ i < n, Adjacent (w i) (w (i + 1)))
    (hinj : ∀ i < n, ∀ j < n, w i = w j → i = j) (hret : w n = w 0) {c c' : Cell}
    (hadjc : Adjacent c c') (hc : c ∉ cycSetV w n) (hc' : c' ∉ cycSetV w n) :
    insideV w n c ↔ insideV w n c' := by
  rcases adjacent_cases hadjc with h | h | h | h
  · -- east step: c' = (c.1 + 1, c.2)
    have h0 : ({(c.1 + 1, c.2), (c.1 + 1, c.2 + 1)} : Finset Cell) ∉ cycEdgesV w n := by
      intro he
      have hh := edge_cells_mem_cycSetV hret he (a := (c.1 + 1, c.2)) (b := (c.1 + 1, c.2 + 1)) rfl
      rw [h] at hc'
      exact hc' hh.1
    have h1 := NcountV_east hn hinj hret c
    rw [if_neg h0, add_zero] at h1
    unfold insideV
    rw [h, h1]
  · -- west step: c' = (c.1 - 1, c.2)
    have h0 : ({(c.1, c.2), (c.1, c.2 + 1)} : Finset Cell) ∉ cycEdgesV w n := by
      intro he
      have hh := edge_cells_mem_cycSetV hret he (a := (c.1, c.2)) (b := (c.1, c.2 + 1)) rfl
      exact hc hh.1
    have h1 : NcountV w n (c.1 - 1, c.2) = NcountV w n (c.1 - 1 + 1, c.2) +
        (if ({(c.1 - 1 + 1, c.2), (c.1 - 1 + 1, c.2 + 1)} : Finset Cell) ∈ cycEdgesV w n
          then 1 else 0) := NcountV_east hn hinj hret (c.1 - 1, c.2)
    rw [show c.1 - 1 + 1 = c.1 by ring, if_neg h0, add_zero] at h1
    unfold insideV
    rw [h, h1]
  · -- north step: c' = (c.1, c.2 + 1)
    have h0 : ({(c.1, c.2 + 1), (c.1 + 1, c.2 + 1)} : Finset Cell) ∉ cycEdgesV w n := by
      intro he
      have hh := edge_cells_mem_cycSetV hret he (a := (c.1, c.2 + 1)) (b := (c.1 + 1, c.2 + 1)) rfl
      rw [h] at hc'
      exact hc' hh.1
    have h1 := north_relV hn hadj hinj hret c
    rw [if_neg h0, add_zero] at h1
    obtain ⟨k, hk⟩ := h1
    unfold insideV
    rw [h]
    constructor
    · intro ⟨a, ha⟩
      refine ⟨k - (a + 1), by omega⟩
    · intro ⟨a, ha⟩
      refine ⟨k - (a + 1), by omega⟩
  · -- south step: c' = (c.1, c.2 - 1)
    have h0 : ({(c.1, c.2), (c.1 + 1, c.2)} : Finset Cell) ∉ cycEdgesV w n := by
      intro he
      have hh := edge_cells_mem_cycSetV hret he (a := (c.1, c.2)) (b := (c.1 + 1, c.2)) rfl
      exact hc hh.1
    have h1 : Even (NcountV w n (c.1, c.2 - 1 + 1) + NcountV w n (c.1, c.2 - 1) +
        (if ({(c.1, c.2 - 1 + 1), (c.1 + 1, c.2 - 1 + 1)} : Finset Cell) ∈ cycEdgesV w n
          then 1 else 0)) := north_relV hn hadj hinj hret (c.1, c.2 - 1)
    rw [show c.2 - 1 + 1 = c.2 by ring, if_neg h0, add_zero] at h1
    obtain ⟨k, hk⟩ := h1
    rw [Prod.eta] at hk
    unfold insideV
    rw [h]
    constructor
    · intro ⟨a, ha⟩
      refine ⟨k - (a + 1), by omega⟩
    · intro ⟨a, ha⟩
      refine ⟨k - (a + 1), by omega⟩

/-- Inside status is constant along paths avoiding the walk. -/
lemma insideV_of_cellPath (hn : 4 ≤ n) (hadj : ∀ i < n, Adjacent (w i) (w (i + 1)))
    (hinj : ∀ i < n, ∀ j < n, w i = w j → i = j) (hret : w n = w 0) {c c' : Cell}
    (hpath : CellPath (· ∉ cycSetV w n) c c') :
    insideV w n c ↔ insideV w n c' := by
  induction hpath with
  | refl => exact Iff.rfl
  | tail hab hstep ih =>
    obtain ⟨hb, hc', hadj'⟩ := hstep
    exact ih.trans (insideV_adj_of_not_mem hn hadj hinj hret hadj' hb hc')

end JordanWalk

-- ============================================================
-- The enclosure: the inside of the descent cycle lies in `S`
-- (via the NE-corner height constancy on hole paths — NO alternating
--  cycle or Jordan nesting needed: each step of a hole path crosses
--  no `crE`/`crN` (its endpoint cells are off `S`), so the NE-corner
--  height is constant, hence `0` at the far east; a walk edge at an
--  inside/outside flip then has `D = 0` endpoints, contradicting the
--  cycle's negative level)
-- ============================================================

section Enclosure

variable {w : ℕ → Cell} {n : ℕ}

/-- The NE-corner height `D (c.1+1, c.2+1)` is constant along any path
avoiding `S`. -/
lemma D_ne_const_of_path (hf : IsTiling S f) (hg : IsTiling S g) {c c' : Cell}
    (hpath : CellPath (· ∉ S) c c') :
    D S f g (c.1 + 1) (c.2 + 1) = D S f g (c'.1 + 1) (c'.2 + 1) := by
  induction hpath with
  | refl => rfl
  | tail hab hstep ih =>
    rename_i b d
    obtain ⟨hb, hc', hadj⟩ := hstep
    rw [ih]
    rcases adjacent_cases hadj with h | h | h | h
    · -- E step: `c' = (b.1 + 1, b.2)`
      have hΔ : ΔE S f g (b.1 + 1) (b.2 + 1) = 0 := by
        have hf' : ¬ crE S f (b.1 + 1) (b.2 + 1) := by
          rintro ⟨hmem, -⟩
          apply hc'; rw [h]; simpa using hmem
        have hg' : ¬ crE S g (b.1 + 1) (b.2 + 1) := by
          rintro ⟨hmem, -⟩
          apply hc'; rw [h]; simpa using hmem
        simp [ΔE, φE, hf', hg']
      have h2 := D_east hf hg (a := b.1 + 1) (b := b.2 + 1)
      rw [hΔ] at h2
      rw [h]
      show D S f g (b.1 + 1) (b.2 + 1) = D S f g (b.1 + 1 + 1) (b.2 + 1)
      omega
    · -- W step: `c' = (b.1 - 1, b.2)`
      have hΔ : ΔE S f g b.1 (b.2 + 1) = 0 := by
        have hf' : ¬ crE S f b.1 (b.2 + 1) := by
          rintro ⟨hmem, -⟩
          apply hb; simpa using hmem
        have hg' : ¬ crE S g b.1 (b.2 + 1) := by
          rintro ⟨hmem, -⟩
          apply hb; simpa using hmem
        simp [ΔE, φE, hf', hg']
      have h2 := D_east hf hg (a := b.1) (b := b.2 + 1)
      rw [hΔ] at h2
      rw [h]
      show D S f g (b.1 + 1) (b.2 + 1) = D S f g (b.1 - 1 + 1) (b.2 + 1)
      rw [show b.1 - 1 + 1 = b.1 from by ring]
      omega
    · -- N step: `c' = (b.1, b.2 + 1)`
      have hΔ : ΔN S f g (b.1 + 1) (b.2 + 1) = 0 := by
        have hf' : ¬ crN S f (b.1 + 1) (b.2 + 1) := by
          rintro ⟨hmem, -⟩
          apply hc'; rw [h]; simpa using hmem
        have hg' : ¬ crN S g (b.1 + 1) (b.2 + 1) := by
          rintro ⟨hmem, -⟩
          apply hc'; rw [h]; simpa using hmem
        simp [ΔN, φN, hf', hg']
      have h2 := D_north hf hg (a := b.1 + 1) (b := b.2 + 1)
      rw [hΔ] at h2
      rw [h]
      show D S f g (b.1 + 1) (b.2 + 1) = D S f g (b.1 + 1) (b.2 + 1 + 1)
      omega
    · -- S step: `c' = (b.1, b.2 - 1)`
      have hΔ : ΔN S f g (b.1 + 1) b.2 = 0 := by
        have hf' : ¬ crN S f (b.1 + 1) b.2 := by
          rintro ⟨hmem, -⟩
          apply hb; simpa using hmem
        have hg' : ¬ crN S g (b.1 + 1) b.2 := by
          rintro ⟨hmem, -⟩
          apply hb; simpa using hmem
        simp [ΔN, φN, hf', hg']
      have h2 := D_north hf hg (a := b.1 + 1) (b := b.2)
      rw [hΔ] at h2
      rw [h]
      show D S f g (b.1 + 1) (b.2 + 1) = D S f g (b.1 + 1) (b.2 - 1 + 1)
      rw [show b.2 - 1 + 1 = b.2 from by ring]
      omega

/-- The NE-corner height vanishes on every cell outside `S` (ComplConnected). -/
lemma D_ne_eq_zero_of_not_mem (hf : IsTiling S f) (hg : IsTiling S g) (hcc : ComplConnected S)
    {c : Cell} (hc : c ∉ S) : D S f g (c.1 + 1) (c.2 + 1) = 0 := by
  have heast : (eastBound S, c.2) ∉ S := by
    intro hm
    have h1 := eastBound_gt S hm
    simp at h1
  have hpath : CellPath (· ∉ S) c (eastBound S, c.2) := hcc c hc _ heast
  have h1 := D_ne_const_of_path hf hg hpath
  rw [h1]
  show D S f g (eastBound S + 1) (c.2 + 1) = 0
  exact D_eq_zero_of_east hf hg (by omega)

/-- A path from an inside cell to an outside cell crosses the walk: some step
has one cell inside and the next outside. -/
lemma exists_insideV_change_of_path {c c' : Cell}
    (hpath : CellPath (· ∉ S) c c') (h1 : insideV w n c) (h2 : ¬ insideV w n c') :
    ∃ a b : Cell, a ∉ S ∧ b ∉ S ∧ Adjacent a b ∧ insideV w n a ∧ ¬ insideV w n b := by
  revert h1 h2
  induction hpath with
  | refl =>
    intro h1 h2
    exact absurd h1 h2
  | tail hab hstep ih =>
    intro h1 h2
    rename_i b d
    obtain ⟨hb, hc', hadj⟩ := hstep
    by_cases hbV : insideV w n b
    · exact ⟨b, d, hb, hc', hadj, hbV, h2⟩
    · exact ih h1 hbV

/-- A walk edge whose two endpoints both have height `D = 0` contradicts the
cycle's negative level. -/
lemma false_of_mem_cycEdgesV_D_eq_zero (hn : 4 ≤ n)
    (hinj : ∀ i < n, ∀ j < n, w i = w j → i = j) (hret : w n = w 0)
    (hlevel : ∀ i < n, D S f g (w i).1 (w i).2 < 0)
    {p q : Cell} (he : ({p, q} : Finset Cell) ∈ cycEdgesV w n)
    (hp : D S f g p.1 p.2 = 0) (hq : D S f g q.1 q.2 = 0) : False := by
  rw [mem_cycEdgesV] at he
  obtain ⟨i, hi, hei⟩ := he
  have hne : p ≠ q := by
    intro h
    rw [h] at hei
    have h1 : w i = q := by
      have hm : w i ∈ ({q, q} : Finset Cell) := hei ▸ Finset.mem_insert_self _ _
      simpa using hm
    have h2 : w (i + 1) = q := by
      have hm : w (i + 1) ∈ ({q, q} : Finset Cell) :=
        hei ▸ Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
      simpa using hm
    exact walkV_ne_succ hn hinj hret i (Finset.mem_range.mp hi) (by rw [h1, h2])
  have hlv1 : D S f g (w i).1 (w i).2 < 0 := hlevel i (Finset.mem_range.mp hi)
  have hlv2 : D S f g (w (i + 1)).1 (w (i + 1)).2 < 0 := by
    by_cases hi1 : i + 1 < n
    · exact hlevel (i + 1) hi1
    · have hi1' : i + 1 = n := by
        have hi' := Finset.mem_range.mp hi
        omega
      rw [hi1', hret]
      exact hlevel 0 (by omega)
  rcases pair_eq_pairV hne hei.symm with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1] at hp
    omega
  · rw [e2] at hq
    omega

/-- The enclosure: every cell inside the descent cycle lies in `S`. -/
lemma insideV_subset_S (hf : IsTiling S f) (hg : IsTiling S g) (hcc : ComplConnected S)
    (hn : 4 ≤ n) (hadj : ∀ i < n, Adjacent (w i) (w (i + 1)))
    (hinj : ∀ i < n, ∀ j < n, w i = w j → i = j) (hret : w n = w 0)
    (hlevel : ∀ i < n, D S f g (w i).1 (w i).2 < 0)
    {c : Cell} (hc : insideV w n c) : c ∈ S := by
  by_contra hcS
  have heast : (eastBound S, c.2) ∉ S := by
    intro hm
    have h1 := eastBound_gt S hm
    simp at h1
  have hpath : CellPath (· ∉ S) c (eastBound S, c.2) := hcc c hcS _ heast
  have hnotin : ¬ insideV w n (eastBound S, c.2) := by
    have hN0 : NcountV w n (eastBound S, c.2) = 0 := by
      unfold NcountV
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro i hi
      rw [Finset.mem_filter] at hi
      obtain ⟨h1, h2, h3, -⟩ := hi
      have hbound : (w i).1 < eastBound S := by
        have hlv := hlevel i (Finset.mem_range.mp h1)
        have hne : D S f g (w i).1 (w i).2 ≠ 0 := by omega
        exact (D_finite_support hf hg (w i).1 (w i).2 hne).2.1
      simp at h3
      omega
    rw [insideV, hN0]
    intro hod
    obtain ⟨a, ha⟩ := hod
    omega
  obtain ⟨a, b, haS, hbS, hadj', haV, hbV⟩ := exists_insideV_change_of_path hpath hc hnotin
  rcases adjacent_cases hadj' with h | h | h | h
  · -- E step: `b = (a.1 + 1, a.2)`, walk edge `{(a.1+1, a.2), (a.1+1, a.2+1)}`
    have hN := NcountV_east hn hinj hret a
    have hNb : NcountV w n (a.1 + 1, a.2) = NcountV w n b := by rw [h]
    rw [hNb] at hN
    have hedge : ({(a.1 + 1, a.2), (a.1 + 1, a.2 + 1)} : Finset Cell) ∈ cycEdgesV w n := by
      by_contra h0
      rw [if_neg h0, add_zero] at hN
      rw [insideV, hN] at haV
      exact hbV haV
    have hD1 : D S f g (a.1 + 1) (a.2 + 1) = 0 := by
      have hΔ : ΔE S f g (a.1 + 1) (a.2 + 1) = 0 := by
        have hf' : ¬ crE S f (a.1 + 1) (a.2 + 1) := by
          rintro ⟨hmem, -⟩
          apply hbS; rw [h]; simpa using hmem
        have hg' : ¬ crE S g (a.1 + 1) (a.2 + 1) := by
          rintro ⟨hmem, -⟩
          apply hbS; rw [h]; simpa using hmem
        simp [ΔE, φE, hf', hg']
      have h2 := D_ne_eq_zero_of_not_mem hf hg hcc hbS
      rw [h] at h2
      have h3 := D_east hf hg (a := a.1 + 1) (b := a.2 + 1)
      rw [hΔ] at h3
      rw [h3] at h2
      simpa using h2
    have hD2 : D S f g (a.1 + 1) a.2 = 0 := by
      have hΔ : ΔN S f g (a.1 + 1) a.2 = 0 := by
        have hf' : ¬ crN S f (a.1 + 1) a.2 := by
          rintro ⟨hmem, -⟩
          apply haS; simpa using hmem
        have hg' : ¬ crN S g (a.1 + 1) a.2 := by
          rintro ⟨hmem, -⟩
          apply haS; simpa using hmem
        simp [ΔN, φN, hf', hg']
      have h3 := D_north hf hg (a := a.1 + 1) (b := a.2)
      rw [hΔ] at h3
      rw [h3] at hD1
      simpa using hD1
    exact false_of_mem_cycEdgesV_D_eq_zero hn hinj hret hlevel hedge hD2 hD1
  · -- W step: `b = (a.1 - 1, a.2)`, walk edge `{(a.1, a.2), (a.1, a.2+1)}`
    have hN : NcountV w n b = NcountV w n a +
        (if ({a, (a.1, a.2 + 1)} : Finset Cell) ∈ cycEdgesV w n then 1 else 0) := by
      have h1 := NcountV_east hn hinj hret b
      have hba1 : (b.1 + 1, b.2) = (a.1, a.2) := by rw [h]; ext <;> simp <;> ring
      have hba2 : (b.1 + 1, b.2 + 1) = (a.1, a.2 + 1) := by rw [h]; ext <;> simp <;> ring
      rw [hba1, hba2, Prod.eta] at h1
      exact h1
    have hedge : ({a, (a.1, a.2 + 1)} : Finset Cell) ∈ cycEdgesV w n := by
      by_contra h0
      rw [if_neg h0, add_zero] at hN
      rw [insideV, hN] at hbV
      exact hbV haV
    have hD1 : D S f g a.1 (a.2 + 1) = 0 := by
      have h2 := D_ne_eq_zero_of_not_mem hf hg hcc hbS
      rw [h] at h2
      simpa using h2
    have hD2 : D S f g a.1 a.2 = 0 := by
      have hΔ : ΔN S f g a.1 a.2 = 0 := by
        have hf' : ¬ crN S f a.1 a.2 := by
          rintro ⟨hmem, -⟩
          apply hbS; rw [h]; simpa using hmem
        have hg' : ¬ crN S g a.1 a.2 := by
          rintro ⟨hmem, -⟩
          apply hbS; rw [h]; simpa using hmem
        simp [ΔN, φN, hf', hg']
      have h3 := D_north hf hg (a := a.1) (b := a.2)
      rw [hΔ] at h3
      rw [h3] at hD1
      simpa using hD1
    exact false_of_mem_cycEdgesV_D_eq_zero hn hinj hret hlevel hedge hD2 hD1
  · -- N step: `b = (a.1, a.2 + 1)`, walk edge `{(a.1, a.2+1), (a.1+1, a.2+1)}`
    have hN := north_relV hn hadj hinj hret a
    have hNb : NcountV w n (a.1, a.2 + 1) = NcountV w n b := by rw [h]
    rw [hNb] at hN
    have hedge : ({(a.1, a.2 + 1), (a.1 + 1, a.2 + 1)} : Finset Cell) ∈ cycEdgesV w n := by
      by_contra h0
      rw [if_neg h0, add_zero] at hN
      obtain ⟨k, hk⟩ := hN
      obtain ⟨m, hm⟩ := haV
      have hbV' : ¬ Odd (NcountV w n b) := hbV
      exact hbV' ⟨k - m - 1, by omega⟩
    have hD1 : D S f g (a.1 + 1) (a.2 + 1) = 0 := by
      have hΔ : ΔN S f g (a.1 + 1) (a.2 + 1) = 0 := by
        have hf' : ¬ crN S f (a.1 + 1) (a.2 + 1) := by
          rintro ⟨hmem, -⟩
          apply hbS; rw [h]; simpa using hmem
        have hg' : ¬ crN S g (a.1 + 1) (a.2 + 1) := by
          rintro ⟨hmem, -⟩
          apply hbS; rw [h]; simpa using hmem
        simp [ΔN, φN, hf', hg']
      have h2 := D_ne_eq_zero_of_not_mem hf hg hcc hbS
      rw [h] at h2
      have h3 := D_north hf hg (a := a.1 + 1) (b := a.2 + 1)
      rw [hΔ] at h3
      rw [h3] at h2
      simpa using h2
    have hD2 : D S f g a.1 (a.2 + 1) = 0 := by
      have hΔ : ΔE S f g a.1 (a.2 + 1) = 0 := by
        have hf' : ¬ crE S f a.1 (a.2 + 1) := by
          rintro ⟨hmem, -⟩
          apply haS; simpa using hmem
        have hg' : ¬ crE S g a.1 (a.2 + 1) := by
          rintro ⟨hmem, -⟩
          apply haS; simpa using hmem
        simp [ΔE, φE, hf', hg']
      have h3 := D_east hf hg (a := a.1) (b := a.2 + 1)
      rw [hΔ] at h3
      rw [h3] at hD1
      simpa using hD1
    exact false_of_mem_cycEdgesV_D_eq_zero hn hinj hret hlevel hedge hD2 hD1
  · -- S step: `b = (a.1, a.2 - 1)`, walk edge `{(a.1, a.2), (a.1+1, a.2)}`
    have hN : Even (NcountV w n a + NcountV w n b +
        (if ({a, (a.1 + 1, a.2)} : Finset Cell) ∈ cycEdgesV w n then 1 else 0)) := by
      have h1 := north_relV hn hadj hinj hret b
      have hba1 : (b.1, b.2 + 1) = (a.1, a.2) := by rw [h]; ext <;> simp <;> ring
      have hba2 : (b.1 + 1, b.2 + 1) = (a.1 + 1, a.2) := by rw [h]; ext <;> simp <;> ring
      rw [hba1, hba2, Prod.eta] at h1
      exact h1
    have hedge : ({a, (a.1 + 1, a.2)} : Finset Cell) ∈ cycEdgesV w n := by
      by_contra h0
      rw [if_neg h0, add_zero] at hN
      obtain ⟨k, hk⟩ := hN
      obtain ⟨m, hm⟩ := haV
      exact hbV ⟨k - m - 1, by omega⟩
    have hD1 : D S f g (a.1 + 1) a.2 = 0 := by
      have h2 := D_ne_eq_zero_of_not_mem hf hg hcc hbS
      rw [h] at h2
      simpa using h2
    have hD2 : D S f g a.1 a.2 = 0 := by
      have hΔ : ΔE S f g a.1 a.2 = 0 := by
        have hf' : ¬ crE S f a.1 a.2 := by
          rintro ⟨hmem, -⟩
          apply hbS; rw [h]; simpa using hmem
        have hg' : ¬ crE S g a.1 a.2 := by
          rintro ⟨hmem, -⟩
          apply hbS; rw [h]; simpa using hmem
        simp [ΔE, φE, hf', hg']
      have h3 := D_east hf hg (a := a.1) (b := a.2)
      rw [hΔ] at h3
      rw [h3] at hD1
      simpa using hD1
    exact false_of_mem_cycEdgesV_D_eq_zero hn hinj hret hlevel hedge hD2 hD1

end Enclosure

-- ============================================================
-- The walk-boundary relation (discrete Green theorem for the descent
-- cycle): the descent-direction sum of `φ f` around the cycle equals,
-- up to the orientation sign, the enclosed defect sum (which vanishes
-- by the enclosure + `boundary_sum_eq_zero`)
-- ============================================================

section WalkBoundary

variable {w : ℕ → Cell} {n : ℕ}

/-- Far-west cells have even `NcountV` (all vertical edges of the row are
crossed, and those pair up by the handshake `even_crossingsV`). -/
noncomputable def wminx (w : ℕ → Cell) (n : ℕ) : ℤ :=
  if h : (((Finset.range n).image w).image (·.1)).Nonempty then
    (((Finset.range n).image w).image (·.1)).min' h else 0

noncomputable def wmaxx (w : ℕ → Cell) (n : ℕ) : ℤ :=
  if h : (((Finset.range n).image w).image (·.1)).Nonempty then
    (((Finset.range n).image w).image (·.1)).max' h else 0

noncomputable def wminy (w : ℕ → Cell) (n : ℕ) : ℤ :=
  if h : (((Finset.range n).image w).image (·.2)).Nonempty then
    (((Finset.range n).image w).image (·.2)).min' h else 0

noncomputable def wmaxy (w : ℕ → Cell) (n : ℕ) : ℤ :=
  if h : (((Finset.range n).image w).image (·.2)).Nonempty then
    (((Finset.range n).image w).image (·.2)).max' h else 0

lemma wminx_le (w : ℕ → Cell) (n : ℕ) (i : ℕ) (hi : i < n) : wminx w n ≤ (w i).1 := by
  rw [wminx]
  split_ifs with hne
  · exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hi)))
  · have hne2 : ¬ ((Finset.range n).image w).Nonempty := by
      intro h'
      exact hne (Finset.image_nonempty.mpr h')
    have h1 : (Finset.range n).image w = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne2
    have h2 : Finset.range n = ∅ := Finset.image_eq_empty.mp h1
    have h3 : (Finset.range n).card = 0 := by rw [h2]; simp
    rw [Finset.card_range] at h3
    omega

lemma wmaxx_ge (w : ℕ → Cell) (n : ℕ) (i : ℕ) (hi : i < n) : (w i).1 ≤ wmaxx w n := by
  rw [wmaxx]
  split_ifs with hne
  · exact Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hi)))
  · have hne2 : ¬ ((Finset.range n).image w).Nonempty := by
      intro h'
      exact hne (Finset.image_nonempty.mpr h')
    have h1 : (Finset.range n).image w = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne2
    have h2 : Finset.range n = ∅ := Finset.image_eq_empty.mp h1
    have h3 : (Finset.range n).card = 0 := by rw [h2]; simp
    rw [Finset.card_range] at h3
    omega

lemma wminy_le (w : ℕ → Cell) (n : ℕ) (i : ℕ) (hi : i < n) : wminy w n ≤ (w i).2 := by
  rw [wminy]
  split_ifs with hne
  · exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hi)))
  · have hne2 : ¬ ((Finset.range n).image w).Nonempty := by
      intro h'
      exact hne (Finset.image_nonempty.mpr h')
    have h1 : (Finset.range n).image w = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne2
    have h2 : Finset.range n = ∅ := Finset.image_eq_empty.mp h1
    have h3 : (Finset.range n).card = 0 := by rw [h2]; simp
    rw [Finset.card_range] at h3
    omega

lemma wmaxy_ge (w : ℕ → Cell) (n : ℕ) (i : ℕ) (hi : i < n) : (w i).2 ≤ wmaxy w n := by
  rw [wmaxy]
  split_ifs with hne
  · exact Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hi)))
  · have hne2 : ¬ ((Finset.range n).image w).Nonempty := by
      intro h'
      exact hne (Finset.image_nonempty.mpr h')
    have h1 : (Finset.range n).image w = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne2
    have h2 : Finset.range n = ∅ := Finset.image_eq_empty.mp h1
    have h3 : (Finset.range n).card = 0 := by rw [h2]; simp
    rw [Finset.card_range] at h3
    omega

lemma NcountV_even_of_lt (hn : 4 ≤ n) (hadj : ∀ i < n, Adjacent (w i) (w (i + 1)))
    (hret : w n = w 0) {c : Cell} (hmin : ∀ i < n, c.1 < (w i).1) : Even (NcountV w n c) := by
  classical
  set U : Finset Cell := (Finset.Icc (wminx w n) (wmaxx w n) ×ˢ
    Finset.Icc (wminy w n) (wmaxy w n)).filter (·.2 ≤ c.2) with hU
  have memU : ∀ i ≤ n, (w i ∈ U ↔ (w i).2 ≤ c.2) := by
    intro i hi
    rw [hU, Finset.mem_filter]
    constructor
    · intro h
      exact h.2
    · intro h
      refine ⟨?_, h⟩
      by_cases hi' : i < n
      · rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
        exact ⟨⟨wminx_le w n i hi', wmaxx_ge w n i hi'⟩, ⟨wminy_le w n i hi', wmaxy_ge w n i hi'⟩⟩
      · have hi'' : i = n := by omega
        rw [hi'', hret]
        rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
        exact ⟨⟨wminx_le w n 0 (by omega), wmaxx_ge w n 0 (by omega)⟩,
          ⟨wminy_le w n 0 (by omega), wmaxy_ge w n 0 (by omega)⟩⟩
  have hcross := even_crossingsV hret U
  have hset : (Finset.range n).filter (fun i ↦ (w i ∈ U) ≠ (w (i + 1) ∈ U)) =
      (Finset.range n).filter (fun i ↦ (w i).1 = (w (i + 1)).1 ∧
        ((w i).2 = c.2 ∧ (w (i + 1)).2 = c.2 + 1 ∨
         (w i).2 = c.2 + 1 ∧ (w (i + 1)).2 = c.2)) := by
    ext i
    simp only [Finset.mem_filter]
    by_cases hi : i ∈ Finset.range n
    · have hadj_i := hadj i (Finset.mem_range.mp hi)
      constructor
      · intro h
        obtain ⟨h1, h2⟩ := h
        refine ⟨h1, ?_⟩
        have hi' : i < n := Finset.mem_range.mp hi
        rw [memU i (by omega), memU (i + 1) (by omega)] at h2
        rcases adjacent_cases hadj_i with ha | ha | ha | ha
        · rw [ha] at h2
          simp at h2
        · rw [ha] at h2
          simp at h2
        · refine ⟨by rw [ha], Or.inl ⟨?_, ?_⟩⟩
          · rw [ha] at h2
            simp at h2
            omega
          · rw [ha]
            have h3 : (w i).2 = c.2 := by
              rw [ha] at h2
              simp at h2
              omega
            simp [h3]
        · refine ⟨by rw [ha], Or.inr ⟨?_, ?_⟩⟩
          · rw [ha] at h2
            simp at h2
            omega
          · rw [ha]
            have h3 : (w i).2 = c.2 + 1 := by
              rw [ha] at h2
              simp at h2
              omega
            simp [h3]
      · intro h
        obtain ⟨h1, h2⟩ := h
        refine ⟨h1, ?_⟩
        have hi' : i < n := Finset.mem_range.mp hi
        rw [memU i (by omega), memU (i + 1) (by omega)]
        rcases h2 with ⟨h1', ⟨hA1, hA2⟩ | ⟨hB1, hB2⟩⟩
        · rw [hA1, hA2]
          simp
        · rw [hB1, hB2]
          simp
    · constructor
      · intro h
        obtain ⟨h1, h2⟩ := h
        exact absurd h1 hi
      · intro h
        obtain ⟨h1, h2⟩ := h
        exact absurd h1 hi
  rw [hset] at hcross
  have hN : NcountV w n c = ((Finset.range n).filter fun i ↦ (w i).1 = (w (i + 1)).1 ∧
      ((w i).2 = c.2 ∧ (w (i + 1)).2 = c.2 + 1 ∨
       (w i).2 = c.2 + 1 ∧ (w (i + 1)).2 = c.2)).card := by
    unfold NcountV
    congr 1
    ext i
    simp only [Finset.mem_filter]
    constructor
    · intro h
      obtain ⟨h1, h2, -, h4⟩ := h
      exact ⟨h1, h2, h4⟩
    · intro h
      obtain ⟨h1, h2, h4⟩ := h
      exact ⟨h1, h2, hmin i (Finset.mem_range.mp h1), h4⟩
  rw [hN]
  exact hcross

/-- The inside cells of the walk lie in its bounding box. -/
lemma insideV_mem_box (hn : 4 ≤ n) (hadj : ∀ i < n, Adjacent (w i) (w (i + 1)))
    (hret : w n = w 0) {c : Cell} (hc : insideV w n c)
    (hminx hmaxx hminy hmaxy : ℤ)
    (hminx' : ∀ i < n, hminx ≤ (w i).1) (hmaxx' : ∀ i < n, (w i).1 ≤ hmaxx)
    (hminy' : ∀ i < n, hminy ≤ (w i).2) (hmaxy' : ∀ i < n, (w i).2 ≤ hmaxy) :
    hminx ≤ c.1 ∧ c.1 < hmaxx ∧ hminy ≤ c.2 ∧ c.2 ≤ hmaxy := by
  have hsucc1 : ∀ j < n, hminy ≤ (w (j + 1)).2 := by
    intro j hj
    by_cases hj1 : j + 1 < n
    · exact hminy' (j + 1) hj1
    · have hj1' : j + 1 = n := by omega
      rw [hj1', hret]
      exact hminy' 0 (by omega)
  have hsucc2 : ∀ j < n, (w (j + 1)).2 ≤ hmaxy := by
    intro j hj
    by_cases hj1 : j + 1 < n
    · exact hmaxy' (j + 1) hj1
    · have hj1' : j + 1 = n := by omega
      rw [hj1', hret]
      exact hmaxy' 0 (by omega)
  obtain ⟨k, hk⟩ := hc
  have hpos : 1 ≤ NcountV w n c := by omega
  unfold NcountV at hpos
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter] at hi
  obtain ⟨hi1, hi2, hi3, hi4⟩ := hi
  have hir := Finset.mem_range.mp hi1
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_contra hcon
    push_neg at hcon
    have hlt : ∀ j < n, c.1 < (w j).1 := fun j hj ↦ by
      have h1 := hminx' j hj
      omega
    have hev := NcountV_even_of_lt hn hadj hret hlt
    obtain ⟨a, ha⟩ := hev
    omega
  · have h1 := hmaxx' i hir
    omega
  · rcases hi4 with ⟨h4, h5⟩ | ⟨h4, h5⟩
    · have h1 := hminy' i hir
      omega
    · have h1 := hsucc1 i hir
      omega
  · rcases hi4 with ⟨h4, h5⟩ | ⟨h4, h5⟩
    · have h1 := hsucc2 i hir
      omega
    · have h1 := hmaxy' i hir
      omega

/-- The inside of the walk, as a `Finset` (via the bounding box). -/
noncomputable def insideR (w : ℕ → Cell) (n : ℕ) : Finset Cell :=
  (Finset.Icc (wminx w n) (wmaxx w n) ×ˢ Finset.Icc (wminy w n) (wmaxy w n)).filter (insideV w n)

lemma mem_insideR {w : ℕ → Cell} {n : ℕ} (hn : 4 ≤ n) (hadj : ∀ i < n, Adjacent (w i) (w (i + 1)))
    (hret : w n = w 0) {c : Cell} :
    c ∈ insideR w n ↔ insideV w n c := by
  rw [insideR, Finset.mem_filter]
  constructor
  · intro h
    exact h.2
  · intro h
    refine ⟨?_, h⟩
    have hb := insideV_mem_box hn hadj hret h (wminx w n) (wmaxx w n) (wminy w n) (wmaxy w n)
      (fun i hi ↦ wminx_le w n i hi) (fun i hi ↦ wmaxx_ge w n i hi)
      (fun i hi ↦ wminy_le w n i hi) (fun i hi ↦ wmaxy_ge w n i hi)
    simp [Finset.mem_Icc]
    omega

end WalkBoundary

-- ============================================================
-- The discrete Green theorem for a simple closed walk whose inside
-- lies in `S`: the descent-direction sum of `φ f` around the walk is `0`.
-- ============================================================

section GreenCycle

variable {w : ℕ → Cell} {n : ℕ}

/-- The inside indicator of a cell, as an integer (`1` inside, `0` outside). -/
noncomputable def indR (w : ℕ → Cell) (n : ℕ) (c : Cell) : ℤ :=
  if insideV w n c then 1 else 0

lemma indR_eq_one (w : ℕ → Cell) (n : ℕ) {c : Cell} (h : insideV w n c) : indR w n c = 1 := by
  rw [indR, if_pos h]

lemma indR_eq_zero (w : ℕ → Cell) (n : ℕ) {c : Cell} (h : ¬ insideV w n c) : indR w n c = 0 := by
  rw [indR, if_neg h]

lemma odd_iff_not_odd {A B : ℕ} (h : Odd (A + B)) : Odd A ↔ ¬ Odd B := by
  obtain ⟨k, hk⟩ := h
  constructor
  · rintro ⟨m1, hm1⟩ ⟨m2, hm2⟩
    omega
  · intro hB
    by_contra hA
    rw [Nat.not_odd_iff_even] at hA hB
    obtain ⟨m1, hm1⟩ := hA
    obtain ⟨m2, hm2⟩ := hB
    omega

lemma odd_iff_odd {A B : ℕ} (h : Even (A + B)) : Odd A ↔ Odd B := by
  obtain ⟨k, hk⟩ := h
  constructor
  · rintro ⟨m1, hm1⟩
    by_contra hB
    rw [Nat.not_odd_iff_even] at hB
    obtain ⟨m2, hm2⟩ := hB
    omega
  · rintro ⟨m2, hm2⟩
    by_contra hA
    rw [Nat.not_odd_iff_even] at hA
    obtain ⟨m1, hm1⟩ := hA
    omega

/-- The inside indicator differs across an edge iff the inside status flips. -/
lemma indR_ne_iff (w : ℕ → Cell) (n : ℕ) {x y : Cell} :
    indR w n x ≠ indR w n y ↔ (insideV w n x ↔ ¬ insideV w n y) := by
  by_cases hx : insideV w n x <;> by_cases hy : insideV w n y <;> simp [indR, hx, hy]

/-- Walk-boundary relation across a horizontal edge: the inside status of the
cells `(a,b)` (north) and `(a,b-1)` (south) differs iff the edge is on the walk. -/
lemma indR_ne_across_horizontal (hn : 4 ≤ n) (hadj : ∀ i < n, Adjacent (w i) (w (i + 1)))
    (hinj : ∀ i < n, ∀ j < n, w i = w j → i = j) (hret : w n = w 0) (a b : ℤ) :
    (indR w n (a, b) ≠ indR w n (a, b - 1)) ↔
      ({(a, b), (a + 1, b)} : Finset Cell) ∈ cycEdgesV w n := by
  have h1 := north_relV hn hadj hinj hret (a, b - 1)
  rw [show (a, b - 1).1 = a from rfl, show (a, b - 1).2 + 1 = b from by ring,
      show (a, b - 1).1 + 1 = a + 1 from by ring] at h1
  rw [indR_ne_iff]
  by_cases he : ({(a, b), (a + 1, b)} : Finset Cell) ∈ cycEdgesV w n
  · rw [if_pos he] at h1
    simp only [he, iff_true]
    obtain ⟨k, hk⟩ := h1
    exact odd_iff_not_odd ⟨k - 1, by omega⟩
  · rw [if_neg he, add_zero] at h1
    simp only [he, iff_false]
    have hAB := odd_iff_odd h1
    intro hbad
    by_cases hA : insideV w n (a, b)
    · exact (hbad.mp hA) (hAB.mp hA)
    · exact hA (hbad.mpr fun hB ↦ hA (hAB.mpr hB))

lemma odd_iff_not_odd_of_eq_add_one {A B : ℕ} (h : A = B + 1) : Odd A ↔ ¬ Odd B := by
  subst h
  constructor
  · rintro ⟨m1, hm1⟩ ⟨m2, hm2⟩
    omega
  · intro hB
    rw [Nat.not_odd_iff_even] at hB
    obtain ⟨m2, hm2⟩ := hB
    exact ⟨m2, by omega⟩

/-- Walk-boundary relation across a vertical edge: the inside status of the
cells `(a-1,b)` (west) and `(a,b)` (east) differs iff the edge is on the walk. -/
lemma indR_ne_across_vertical (hn : 4 ≤ n)
    (hinj : ∀ i < n, ∀ j < n, w i = w j → i = j) (hret : w n = w 0) (a b : ℤ) :
    (indR w n (a - 1, b) ≠ indR w n (a, b)) ↔
      ({(a, b), (a, b + 1)} : Finset Cell) ∈ cycEdgesV w n := by
  have h1 := NcountV_east hn hinj hret (a - 1, b)
  rw [show (a - 1, b).1 + 1 = a from by ring, show (a - 1, b).2 = b from rfl] at h1
  rw [indR_ne_iff]
  by_cases he : ({(a, b), (a, b + 1)} : Finset Cell) ∈ cycEdgesV w n
  · rw [if_pos he] at h1
    simp only [he, iff_true]
    exact odd_iff_not_odd_of_eq_add_one h1
  · rw [if_neg he, add_zero] at h1
    simp only [he, iff_false]
    have hAB : insideV w n (a - 1, b) ↔ insideV w n (a, b) := by
      unfold insideV
      rw [h1]
    intro hbad
    by_cases hA : insideV w n (a - 1, b)
    · exact (hbad.mp hA) (hAB.mp hA)
    · exact hA (hbad.mpr fun hB ↦ hA (hAB.mpr hB))

/-- Adjacent cells whose shared (vertical) edge is not on the walk have the same
inside status — eastward version. -/
lemma insideV_iff_of_east (hn : 4 ≤ n)
    (hinj : ∀ i < n, ∀ j < n, w i = w j → i = j) (hret : w n = w 0) {p : Cell}
    (he : ({(p.1 + 1, p.2), (p.1 + 1, p.2 + 1)} : Finset Cell) ∉ cycEdgesV w n) :
    insideV w n p ↔ insideV w n (p.1 + 1, p.2) := by
  have h1 := NcountV_east hn hinj hret p
  rw [if_neg he, add_zero] at h1
  unfold insideV
  rw [h1]

/-- Adjacent cells whose shared (horizontal) edge is not on the walk have the same
inside status — northward version. -/
lemma insideV_iff_of_north (hn : 4 ≤ n) (hadj : ∀ i < n, Adjacent (w i) (w (i + 1)))
    (hinj : ∀ i < n, ∀ j < n, w i = w j → i = j) (hret : w n = w 0) {p : Cell}
    (he : ({(p.1, p.2 + 1), (p.1 + 1, p.2 + 1)} : Finset Cell) ∉ cycEdgesV w n) :
    insideV w n p ↔ insideV w n (p.1, p.2 + 1) := by
  have h1 := north_relV hn hadj hinj hret p
  rw [if_neg he, add_zero] at h1
  obtain ⟨k, hk⟩ := h1
  unfold insideV
  constructor <;> intro h <;> obtain ⟨m, hm⟩ := h <;> refine ⟨k - m - 1, by omega⟩

/-- Adjacent cells whose shared (vertical) edge is not on the walk have the same
inside status — westward version. -/
lemma insideV_iff_of_west (hn : 4 ≤ n)
    (hinj : ∀ i < n, ∀ j < n, w i = w j → i = j) (hret : w n = w 0) {p : Cell}
    (he : ({(p.1, p.2), (p.1, p.2 + 1)} : Finset Cell) ∉ cycEdgesV w n) :
    insideV w n p ↔ insideV w n (p.1 - 1, p.2) := by
  have h1 : NcountV w n (p.1 - 1, p.2) = NcountV w n p := by
    have h := NcountV_east hn hinj hret (p.1 - 1, p.2)
    rw [show (p.1 - 1, p.2).1 + 1 = p.1 from by ring, show (p.1 - 1, p.2).2 = p.2 from rfl,
        if_neg he, add_zero, Prod.eta] at h
    exact h
  unfold insideV
  rw [h1]

/-- Adjacent cells whose shared (horizontal) edge is not on the walk have the same
inside status — southward version. -/
lemma insideV_iff_of_south (hn : 4 ≤ n) (hadj : ∀ i < n, Adjacent (w i) (w (i + 1)))
    (hinj : ∀ i < n, ∀ j < n, w i = w j → i = j) (hret : w n = w 0) {p : Cell}
    (he : ({(p.1, p.2), (p.1 + 1, p.2)} : Finset Cell) ∉ cycEdgesV w n) :
    insideV w n p ↔ insideV w n (p.1, p.2 - 1) := by
  have h1 := north_relV hn hadj hinj hret (p.1, p.2 - 1)
  rw [show (p.1, p.2 - 1).1 = p.1 from rfl, show (p.1, p.2 - 1).2 + 1 = p.2 from by ring,
      show (p.1, p.2 - 1).1 + 1 = p.1 + 1 from by ring, if_neg he, add_zero] at h1
  obtain ⟨k, hk⟩ := h1
  unfold insideV
  show Odd (NcountV w n (p.1, p.2)) ↔ Odd (NcountV w n (p.1, p.2 - 1))
  constructor <;> intro h <;> obtain ⟨m, hm⟩ := h <;> refine ⟨k - m - 1, by omega⟩

/-- The cell to the left of a directed step `u → v` (for adjacent `u v`). -/
def leftCell (u v : Cell) : Cell :=
  if v = (u.1 + 1, u.2) then (u.1, u.2)
  else if v = (u.1 - 1, u.2) then (u.1 - 1, u.2 - 1)
  else if v = (u.1, u.2 + 1) then (u.1 - 1, u.2)
  else (u.1, u.2 - 1)

lemma leftCell_east {u : Cell} : leftCell u (u.1 + 1, u.2) = (u.1, u.2) := by
  rw [leftCell, if_pos rfl]

lemma leftCell_west {u : Cell} : leftCell u (u.1 - 1, u.2) = (u.1 - 1, u.2 - 1) := by
  rw [leftCell, if_neg (by intro h; rw [Prod.mk.injEq] at h; omega), if_pos rfl]

lemma leftCell_north {u : Cell} : leftCell u (u.1, u.2 + 1) = (u.1 - 1, u.2) := by
  rw [leftCell, if_neg (by intro h; rw [Prod.mk.injEq] at h; omega),
    if_neg (by intro h; rw [Prod.mk.injEq] at h; omega), if_pos rfl]

lemma leftCell_south {u : Cell} : leftCell u (u.1, u.2 - 1) = (u.1, u.2 - 1) := by
  rw [leftCell, if_neg (by intro h; rw [Prod.mk.injEq] at h; omega),
    if_neg (by intro h; rw [Prod.mk.injEq] at h; omega),
    if_neg (by intro h; rw [Prod.mk.injEq] at h; omega)]

lemma leftCell_of_east {u v : Cell} (h : v = (u.1 + 1, u.2)) : leftCell u v = (u.1, u.2) := by
  rw [leftCell, if_pos h]

lemma leftCell_of_west {u v : Cell} (h : v = (u.1 - 1, u.2)) :
    leftCell u v = (u.1 - 1, u.2 - 1) := by
  rw [leftCell, if_neg (by intro h'; rw [h'] at h; rw [Prod.mk.injEq] at h; omega), if_pos h]

lemma leftCell_of_north {u v : Cell} (h : v = (u.1, u.2 + 1)) :
    leftCell u v = (u.1 - 1, u.2) := by
  rw [leftCell, if_neg (by intro h'; rw [h'] at h; rw [Prod.mk.injEq] at h; omega),
    if_neg (by intro h'; rw [h'] at h; rw [Prod.mk.injEq] at h; omega), if_pos h]

lemma leftCell_of_south {u v : Cell} (h : v = (u.1, u.2 - 1)) :
    leftCell u v = (u.1, u.2 - 1) := by
  rw [leftCell, if_neg (by intro h'; rw [h'] at h; rw [Prod.mk.injEq] at h; omega),
    if_neg (by intro h'; rw [h'] at h; rw [Prod.mk.injEq] at h; omega),
    if_neg (by intro h'; rw [h'] at h; rw [Prod.mk.injEq] at h; omega)]

/-- A vertex of a simple closed walk lies on exactly two walk edges. -/
lemma not_mem_cycEdgesV_of_ne {v a c' x : Cell}
    (huniq : ∀ z : Cell, ({v, z} : Finset Cell) ∈ cycEdgesV w n → z = a ∨ z = c')
    (hxa : x ≠ a) (hxc : x ≠ c') : ({v, x} : Finset Cell) ∉ cycEdgesV w n := by
  intro h
  rcases huniq x h with h' | h'
  · exact hxa h'
  · exact hxc h'

lemma not_mem_cycEdgesV_swap {a b : Cell}
    (h : ({a, b} : Finset Cell) ∉ cycEdgesV w n) : ({b, a} : Finset Cell) ∉ cycEdgesV w n := by
  intro h'
  apply h
  rw [mem_cycEdgesV] at h' ⊢
  obtain ⟨i, hi, hei⟩ := h'
  exact ⟨i, hi, by rw [hei]; ext; simp [Finset.mem_insert, Finset.mem_singleton]; tauto⟩

/-- Inside-status transfer across a non-walk edge, east step with explicit target. -/
lemma insideV_iff_east_to (hn : 4 ≤ n)
    (hinj : ∀ i < n, ∀ j < n, w i = w j → i = j) (hret : w n = w 0) {p q : Cell}
    (hq : q = (p.1 + 1, p.2))
    (he : ({(p.1 + 1, p.2), (p.1 + 1, p.2 + 1)} : Finset Cell) ∉ cycEdgesV w n) :
    insideV w n p ↔ insideV w n q := by
  rw [hq]; exact insideV_iff_of_east hn hinj hret he

/-- Inside-status transfer across a non-walk edge, west step with explicit target. -/
lemma insideV_iff_west_to (hn : 4 ≤ n)
    (hinj : ∀ i < n, ∀ j < n, w i = w j → i = j) (hret : w n = w 0) {p q : Cell}
    (hq : q = (p.1 - 1, p.2))
    (he : ({(p.1, p.2), (p.1, p.2 + 1)} : Finset Cell) ∉ cycEdgesV w n) :
    insideV w n p ↔ insideV w n q := by
  rw [hq]; exact insideV_iff_of_west hn hinj hret he

/-- Inside-status transfer across a non-walk edge, north step with explicit target. -/
lemma insideV_iff_north_to (hn : 4 ≤ n) (hadj : ∀ i < n, Adjacent (w i) (w (i + 1)))
    (hinj : ∀ i < n, ∀ j < n, w i = w j → i = j) (hret : w n = w 0) {p q : Cell}
    (hq : q = (p.1, p.2 + 1))
    (he : ({(p.1, p.2 + 1), (p.1 + 1, p.2 + 1)} : Finset Cell) ∉ cycEdgesV w n) :
    insideV w n p ↔ insideV w n q := by
  rw [hq]; exact insideV_iff_of_north hn hadj hinj hret he

/-- Inside-status transfer across a non-walk edge, south step with explicit target. -/
lemma insideV_iff_south_to (hn : 4 ≤ n) (hadj : ∀ i < n, Adjacent (w i) (w (i + 1)))
    (hinj : ∀ i < n, ∀ j < n, w i = w j → i = j) (hret : w n = w 0) {p q : Cell}
    (hq : q = (p.1, p.2 - 1))
    (he : ({(p.1, p.2), (p.1 + 1, p.2)} : Finset Cell) ∉ cycEdgesV w n) :
    insideV w n p ↔ insideV w n q := by
  rw [hq]; exact insideV_iff_of_south hn hadj hinj hret he

/-- The inside status of the left cell is preserved across a vertex of the walk:
the left cell of the incoming step and of the outgoing step have the same inside
status.  This is the local form of the consistent orientation of a simple closed
walk. -/
lemma insideV_leftCell_trans (hn : 4 ≤ n) (hadj : ∀ i < n, Adjacent (w i) (w (i + 1)))
    (hinj : ∀ i < n, ∀ j < n, w i = w j → i = j) (hret : w n = w 0)
    {a v c' : Cell} (hac : a ≠ c')
    (huniq : ∀ z : Cell, ({v, z} : Finset Cell) ∈ cycEdgesV w n → z = a ∨ z = c')
    (hadj1 : Adjacent a v) (hadj2 : Adjacent v c') :
    insideV w n (leftCell a v) ↔ insideV w n (leftCell v c') := by
  obtain ⟨x, y⟩ := v
  have hne : ∀ z : Cell, z ≠ a → z ≠ c' → ({(x, y), z} : Finset Cell) ∉ cycEdgesV w n :=
    fun z hza hzc ↦ not_mem_cycEdgesV_of_ne huniq hza hzc
  rcases adjacent_cases hadj1 with h1 | h1 | h1 | h1 <;>
    rcases adjacent_cases hadj2 with h2 | h2 | h2 | h2
  · -- a = W, c' = E (straight east)
    have ha : a = (x - 1, y) := by
      rw [Prod.mk.injEq] at h1; rw [← Prod.eta a, Prod.mk.injEq]; constructor <;> omega
    have hc : c' = (x + 1, y) := by rw [h2]
    have hL1 : leftCell a (x, y) = (x - 1, y) := by rw [leftCell_of_east h1, ha]
    have hL2 : leftCell (x, y) c' = (x, y) := by rw [h2]; exact leftCell_east
    rw [hL1, hL2]
    have hN : ({(x, y), (x, y + 1)} : Finset Cell) ∉ cycEdgesV w n :=
      hne _ (by rw [ha]; intro h; rw [Prod.mk.injEq] at h; omega)
            (by rw [hc]; intro h; rw [Prod.mk.injEq] at h; omega)
    exact (insideV_iff_of_west hn hinj hret (p := (x, y)) hN).symm
  · -- a = W, c' = W : excluded (a = c')
    have ha : a = (x - 1, y) := by
      rw [Prod.mk.injEq] at h1; rw [← Prod.eta a, Prod.mk.injEq]; constructor <;> omega
    have hc : c' = (x - 1, y) := by rw [h2]
    exact absurd (ha.trans hc.symm) hac
  · -- a = W, c' = N (left turn, same left cell)
    have ha : a = (x - 1, y) := by
      rw [Prod.mk.injEq] at h1; rw [← Prod.eta a, Prod.mk.injEq]; constructor <;> omega
    have hL1 : leftCell a (x, y) = (x - 1, y) := by rw [leftCell_of_east h1, ha]
    have hL2 : leftCell (x, y) c' = (x - 1, y) := by rw [h2]; exact leftCell_north
    rw [hL1, hL2]
  · -- a = W, c' = S (right turn)
    have ha : a = (x - 1, y) := by
      rw [Prod.mk.injEq] at h1; rw [← Prod.eta a, Prod.mk.injEq]; constructor <;> omega
    have hc : c' = (x, y - 1) := by rw [h2]
    have hL1 : leftCell a (x, y) = (x - 1, y) := by rw [leftCell_of_east h1, ha]
    have hL2 : leftCell (x, y) c' = (x, y - 1) := by rw [h2]; exact leftCell_south
    rw [hL1, hL2]
    have hN : ({(x, y), (x, y + 1)} : Finset Cell) ∉ cycEdgesV w n :=
      hne _ (by rw [ha]; intro h; rw [Prod.mk.injEq] at h; omega)
            (by rw [hc]; intro h; rw [Prod.mk.injEq] at h; omega)
    have hE : ({(x, y), (x + 1, y)} : Finset Cell) ∉ cycEdgesV w n :=
      hne _ (by rw [ha]; intro h; rw [Prod.mk.injEq] at h; omega)
            (by rw [hc]; intro h; rw [Prod.mk.injEq] at h; omega)
    exact (insideV_iff_of_west hn hinj hret (p := (x, y)) hN).symm.trans
      (insideV_iff_of_south hn hadj hinj hret (p := (x, y)) hE)
  · -- a = E, c' = E : excluded
    have ha : a = (x + 1, y) := by
      rw [Prod.mk.injEq] at h1; rw [← Prod.eta a, Prod.mk.injEq]; constructor <;> omega
    have hc : c' = (x + 1, y) := by rw [h2]
    exact absurd (ha.trans hc.symm) hac
  · -- a = E, c' = W (straight west)
    have ha : a = (x + 1, y) := by
      rw [Prod.mk.injEq] at h1; rw [← Prod.eta a, Prod.mk.injEq]; constructor <;> omega
    have hc : c' = (x - 1, y) := by rw [h2]
    have hL1 : leftCell a (x, y) = (x, y - 1) := by rw [leftCell_of_west h1, ha]; simp
    have hL2 : leftCell (x, y) c' = (x - 1, y - 1) := by rw [h2]; exact leftCell_west
    rw [hL1, hL2]
    have hS : ({(x, y), (x, y - 1)} : Finset Cell) ∉ cycEdgesV w n :=
      hne _ (by rw [ha]; intro h; rw [Prod.mk.injEq] at h; omega)
            (by rw [hc]; intro h; rw [Prod.mk.injEq] at h; omega)
    exact insideV_iff_of_west hn hinj hret (p := (x, y - 1)) (by
      show ({(x, y - 1), (x, y - 1 + 1)} : Finset Cell) ∉ cycEdgesV w n
      rw [show y - 1 + 1 = y from by ring]
      exact not_mem_cycEdgesV_swap hS)
  · -- a = E, c' = N (right turn)
    have ha : a = (x + 1, y) := by
      rw [Prod.mk.injEq] at h1; rw [← Prod.eta a, Prod.mk.injEq]; constructor <;> omega
    have hc : c' = (x, y + 1) := by rw [h2]
    have hL1 : leftCell a (x, y) = (x, y - 1) := by rw [leftCell_of_west h1, ha]; simp
    have hL2 : leftCell (x, y) c' = (x - 1, y) := by rw [h2]; exact leftCell_north
    rw [hL1, hL2]
    have hS : ({(x, y), (x, y - 1)} : Finset Cell) ∉ cycEdgesV w n :=
      hne _ (by rw [ha]; intro h; rw [Prod.mk.injEq] at h; omega)
            (by rw [hc]; intro h; rw [Prod.mk.injEq] at h; omega)
    have hW : ({(x, y), (x - 1, y)} : Finset Cell) ∉ cycEdgesV w n :=
      hne _ (by rw [ha]; intro h; rw [Prod.mk.injEq] at h; omega)
            (by rw [hc]; intro h; rw [Prod.mk.injEq] at h; omega)
    exact (insideV_iff_of_west hn hinj hret (p := (x, y - 1)) (by
      show ({(x, y - 1), (x, y - 1 + 1)} : Finset Cell) ∉ cycEdgesV w n
      rw [show y - 1 + 1 = y from by ring]
      exact not_mem_cycEdgesV_swap hS)).trans
      (insideV_iff_north_to hn hadj hinj hret (p := (x - 1, y - 1)) (q := (x - 1, y)) (by simp) (by
        show ({(x - 1, y - 1 + 1), (x - 1 + 1, y - 1 + 1)} : Finset Cell) ∉ cycEdgesV w n
        rw [show x - 1 + 1 = x from by ring, show y - 1 + 1 = y from by ring]
        exact not_mem_cycEdgesV_swap hW))
  · -- a = E, c' = S (left turn, same left cell)
    have ha : a = (x + 1, y) := by
      rw [Prod.mk.injEq] at h1; rw [← Prod.eta a, Prod.mk.injEq]; constructor <;> omega
    have hL1 : leftCell a (x, y) = (x, y - 1) := by rw [leftCell_of_west h1, ha]; simp
    have hL2 : leftCell (x, y) c' = (x, y - 1) := by rw [h2]; exact leftCell_south
    rw [hL1, hL2]
  · -- a = S, c' = E (right turn)
    have ha : a = (x, y - 1) := by
      rw [Prod.mk.injEq] at h1; rw [← Prod.eta a, Prod.mk.injEq]; constructor <;> omega
    have hc : c' = (x + 1, y) := by rw [h2]
    have hL1 : leftCell a (x, y) = (x - 1, y - 1) := by rw [leftCell_of_north h1, ha]
    have hL2 : leftCell (x, y) c' = (x, y) := by rw [h2]; exact leftCell_east
    rw [hL1, hL2]
    have hW : ({(x, y), (x - 1, y)} : Finset Cell) ∉ cycEdgesV w n :=
      hne _ (by rw [ha]; intro h; rw [Prod.mk.injEq] at h; omega)
            (by rw [hc]; intro h; rw [Prod.mk.injEq] at h; omega)
    have hN : ({(x, y), (x, y + 1)} : Finset Cell) ∉ cycEdgesV w n :=
      hne _ (by rw [ha]; intro h; rw [Prod.mk.injEq] at h; omega)
            (by rw [hc]; intro h; rw [Prod.mk.injEq] at h; omega)
    exact (insideV_iff_north_to hn hadj hinj hret (p := (x - 1, y - 1)) (q := (x - 1, y)) (by simp) (by
      show ({(x - 1, y - 1 + 1), (x - 1 + 1, y - 1 + 1)} : Finset Cell) ∉ cycEdgesV w n
      rw [show x - 1 + 1 = x from by ring, show y - 1 + 1 = y from by ring]
      exact not_mem_cycEdgesV_swap hW)).trans
      (insideV_iff_of_west hn hinj hret (p := (x, y)) hN).symm
  · -- a = S, c' = W (left turn, same left cell)
    have ha : a = (x, y - 1) := by
      rw [Prod.mk.injEq] at h1; rw [← Prod.eta a, Prod.mk.injEq]; constructor <;> omega
    have hL1 : leftCell a (x, y) = (x - 1, y - 1) := by rw [leftCell_of_north h1, ha]
    have hL2 : leftCell (x, y) c' = (x - 1, y - 1) := by rw [h2]; exact leftCell_west
    rw [hL1, hL2]
  · -- a = S, c' = N (straight north)
    have ha : a = (x, y - 1) := by
      rw [Prod.mk.injEq] at h1; rw [← Prod.eta a, Prod.mk.injEq]; constructor <;> omega
    have hc : c' = (x, y + 1) := by rw [h2]
    have hL1 : leftCell a (x, y) = (x - 1, y - 1) := by rw [leftCell_of_north h1, ha]
    have hL2 : leftCell (x, y) c' = (x - 1, y) := by rw [h2]; exact leftCell_north
    rw [hL1, hL2]
    have hW : ({(x, y), (x - 1, y)} : Finset Cell) ∉ cycEdgesV w n :=
      hne _ (by rw [ha]; intro h; rw [Prod.mk.injEq] at h; omega)
            (by rw [hc]; intro h; rw [Prod.mk.injEq] at h; omega)
    exact insideV_iff_north_to hn hadj hinj hret (p := (x - 1, y - 1)) (q := (x - 1, y)) (by simp) (by
      show ({(x - 1, y - 1 + 1), (x - 1 + 1, y - 1 + 1)} : Finset Cell) ∉ cycEdgesV w n
      rw [show x - 1 + 1 = x from by ring, show y - 1 + 1 = y from by ring]
      exact not_mem_cycEdgesV_swap hW)
  · -- a = S, c' = S : excluded
    have ha : a = (x, y - 1) := by
      rw [Prod.mk.injEq] at h1; rw [← Prod.eta a, Prod.mk.injEq]; constructor <;> omega
    have hc : c' = (x, y - 1) := by rw [h2]
    exact absurd (ha.trans hc.symm) hac
  · -- a = N, c' = E (left turn, same left cell)
    have ha : a = (x, y + 1) := by
      rw [Prod.mk.injEq] at h1; rw [← Prod.eta a, Prod.mk.injEq]; constructor <;> omega
    have hL1 : leftCell a (x, y) = (x, y) := by rw [leftCell_of_south h1, ha]; simp
    have hL2 : leftCell (x, y) c' = (x, y) := by rw [h2]; exact leftCell_east
    rw [hL1, hL2]
  · -- a = N, c' = W (right turn)
    have ha : a = (x, y + 1) := by
      rw [Prod.mk.injEq] at h1; rw [← Prod.eta a, Prod.mk.injEq]; constructor <;> omega
    have hc : c' = (x - 1, y) := by rw [h2]
    have hL1 : leftCell a (x, y) = (x, y) := by rw [leftCell_of_south h1, ha]; simp
    have hL2 : leftCell (x, y) c' = (x - 1, y - 1) := by rw [h2]; exact leftCell_west
    rw [hL1, hL2]
    have hE : ({(x, y), (x + 1, y)} : Finset Cell) ∉ cycEdgesV w n :=
      hne _ (by rw [ha]; intro h; rw [Prod.mk.injEq] at h; omega)
            (by rw [hc]; intro h; rw [Prod.mk.injEq] at h; omega)
    have hS : ({(x, y), (x, y - 1)} : Finset Cell) ∉ cycEdgesV w n :=
      hne _ (by rw [ha]; intro h; rw [Prod.mk.injEq] at h; omega)
            (by rw [hc]; intro h; rw [Prod.mk.injEq] at h; omega)
    exact (insideV_iff_of_south hn hadj hinj hret (p := (x, y)) hE).trans
      (insideV_iff_of_west hn hinj hret (p := (x, y - 1)) (by
        show ({(x, y - 1), (x, y - 1 + 1)} : Finset Cell) ∉ cycEdgesV w n
        rw [show y - 1 + 1 = y from by ring]
        exact not_mem_cycEdgesV_swap hS))
  · -- a = N, c' = N : excluded
    have ha : a = (x, y + 1) := by
      rw [Prod.mk.injEq] at h1; rw [← Prod.eta a, Prod.mk.injEq]; constructor <;> omega
    have hc : c' = (x, y + 1) := by rw [h2]
    exact absurd (ha.trans hc.symm) hac
  · -- a = N, c' = S (straight south)
    have ha : a = (x, y + 1) := by
      rw [Prod.mk.injEq] at h1; rw [← Prod.eta a, Prod.mk.injEq]; constructor <;> omega
    have hc : c' = (x, y - 1) := by rw [h2]
    have hL1 : leftCell a (x, y) = (x, y) := by rw [leftCell_of_south h1, ha]; simp
    have hL2 : leftCell (x, y) c' = (x, y - 1) := by rw [h2]; exact leftCell_south
    rw [hL1, hL2]
    have hE : ({(x, y), (x + 1, y)} : Finset Cell) ∉ cycEdgesV w n :=
      hne _ (by rw [ha]; intro h; rw [Prod.mk.injEq] at h; omega)
            (by rw [hc]; intro h; rw [Prod.mk.injEq] at h; omega)
    exact insideV_iff_of_south hn hadj hinj hret (p := (x, y)) hE

/-- A vertex of a simple closed walk lies on exactly two walk edges: the edge to
its successor and the edge to its predecessor. -/
lemma eq_pred_or_succ_of_mem_cycEdgesV (hn : 4 ≤ n)
    (hinj : ∀ i < n, ∀ j < n, w i = w j → i = j) (hret : w n = w 0)
    {k : ℕ} (hk : k < n) {x : Cell}
    (he : ({w k, x} : Finset Cell) ∈ cycEdgesV w n) :
    x = w (k + 1) ∨ x = (if k = 0 then w (n - 1) else w (k - 1)) := by
  rw [mem_cycEdgesV] at he
  obtain ⟨j, hj, hej⟩ := he
  have hj' := Finset.mem_range.mp hj
  have hne : w j ≠ w (j + 1) := walkV_ne_succ hn hinj hret j hj'
  rcases pair_eq_pairV hne hej with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · have hjk : j = k := hinj j hj' k hk e1
    left
    rw [← hjk]
    exact e2.symm
  · right
    by_cases hj1 : j + 1 < n
    · have hjk : j + 1 = k := hinj (j + 1) hj1 k hk e2
      have hk1 : k ≠ 0 := by omega
      rw [if_neg hk1, ← hjk, show j + 1 - 1 = j from by omega]
      exact e1.symm
    · have hj1' : j + 1 = n := by omega
      have hk0 : k = 0 := by
        have h0 : w n = w k := hj1' ▸ e2
        have h0' : w 0 = w k := hret.symm.trans h0
        exact (hinj 0 (by omega) k hk h0').symm
      rw [if_pos hk0]
      have hjn : j = n - 1 := by omega
      rw [← hjn]
      exact e1.symm

/-- Consistent orientation: the inside status of the left cell is the same for
every step of the walk. -/
lemma leftIn_const (hn : 4 ≤ n) (hadj : ∀ i < n, Adjacent (w i) (w (i + 1)))
    (hinj : ∀ i < n, ∀ j < n, w i = w j → i = j) (hret : w n = w 0) :
    ∀ i < n, insideV w n (leftCell (w i) (w (i + 1))) ↔
      insideV w n (leftCell (w 0) (w 1)) := by
  intro i
  induction i with
  | zero => intro _; exact Iff.rfl
  | succ k ih =>
    intro hk1
    have hk : k < n := by omega
    have hac : w k ≠ w (k + 2) := by
      intro h
      by_cases hk2 : k + 2 < n
      · have h2 := hinj k hk (k + 2) hk2 h
        omega
      · have hk2' : k + 2 = n := by omega
        have h0 : w (k + 2) = w 0 := by rw [hk2', hret]
        rw [h0] at h
        have h2 := hinj k hk 0 (by omega) h
        omega
    have huniq : ∀ z : Cell, ({w (k + 1), z} : Finset Cell) ∈ cycEdgesV w n →
        z = w k ∨ z = w (k + 2) := by
      intro z hz
      have h := eq_pred_or_succ_of_mem_cycEdgesV hn hinj hret hk1 hz
      rw [if_neg (by omega : k + 1 ≠ 0), show k + 1 + 1 = k + 2 from by omega,
          show k + 1 - 1 = k from by omega] at h
      exact h.symm
    have hlocal := insideV_leftCell_trans hn hadj hinj hret (a := w k) (v := w (k + 1))
      (c' := w (k + 2)) hac huniq (hadj k hk) (hadj (k + 1) hk1)
    exact hlocal.symm.trans (ih hk)

end GreenCycle

-- ============================================================
-- The discrete Green theorem for the descent cycle: assembly
-- ============================================================

section GreenSum

variable {w : ℕ → Cell} {n : ℕ}

/-- Reindexing an `Icc` sum under the shift `b ↦ b + 1`. -/
lemma sum_Icc_shift (G : ℤ → ℤ) (y0 y1 : ℤ) :
    ∑ b ∈ Finset.Icc y0 y1, G (b + 1) = ∑ b ∈ Finset.Icc (y0 + 1) (y1 + 1), G b := by
  rw [show Finset.Icc (y0 + 1) (y1 + 1) = (Finset.Icc y0 y1).image (· + 1) from by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_image]
    constructor
    · intro h
      exact ⟨x - 1, ⟨by omega, by omega⟩, by omega⟩
    · intro h
      obtain ⟨a, ⟨h1, h2⟩, h3⟩ := h
      rw [← h3]
      constructor <;> omega]
  rw [Finset.sum_image (fun x _ y _ h ↦ by omega)]

/-- Summation by parts over a column: the `(ind b − ind (b−1)) · F b` sum equals
the difference of the `ind · F` sums, when `ind` vanishes on the boundary. -/
lemma sum_Icc_telescope (F ind : ℤ → ℤ) {y0 y1 : ℤ} (hy : y0 ≤ y1)
    (h0 : ind y0 = 0) (h0' : ind (y0 - 1) = 0) (h1 : ind y1 = 0) :
    ∑ b ∈ Finset.Icc y0 y1, (ind b - ind (b - 1)) * F b =
      ∑ b ∈ Finset.Icc y0 y1, ind b * F b - ∑ b ∈ Finset.Icc y0 y1, ind b * F (b + 1) := by
  have hshift : ∑ b ∈ Finset.Icc y0 y1, ind b * F (b + 1) =
      ∑ b ∈ Finset.Icc (y0 + 1) (y1 + 1), ind (b - 1) * F b := by
    rw [← sum_Icc_shift (fun b ↦ ind (b - 1) * F b) y0 y1]
    apply Finset.sum_congr rfl
    intro b _
    simp
  have hset : Finset.Icc (y0 + 1) y1 = Finset.Icc y0 y1 \ {y0} := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_sdiff, Finset.mem_singleton]
    omega
  have hsub : ({y0} : Finset ℤ) ⊆ Finset.Icc y0 y1 :=
    Finset.singleton_subset_iff.mpr (by rw [Finset.mem_Icc]; exact ⟨le_refl _, hy⟩)
  have h2 : ∑ b ∈ Finset.Icc y0 y1, ind b * F b =
      ∑ b ∈ Finset.Icc (y0 + 1) y1, ind b * F b := by
    have hsdiff := Finset.sum_sdiff (s₁ := ({y0} : Finset ℤ)) (s₂ := Finset.Icc y0 y1)
      (f := fun b ↦ ind b * F b) hsub
    rw [Finset.sum_singleton, h0, zero_mul, add_zero] at hsdiff
    rw [hset]
    exact hsdiff.symm
  have h3 : ∑ b ∈ Finset.Icc (y0 + 1) (y1 + 1), ind (b - 1) * F b =
      ∑ b ∈ Finset.Icc (y0 + 1) y1, ind (b - 1) * F b := by
    have hset2 : Finset.Icc (y0 + 1) (y1 + 1) = insert (y1 + 1) (Finset.Icc (y0 + 1) y1) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hset2, Finset.sum_insert (by intro h; rw [Finset.mem_Icc] at h; omega)]
    simp [h1]
  have h4 : ∑ b ∈ Finset.Icc y0 y1, (ind b - ind (b - 1)) * F b =
      ∑ b ∈ Finset.Icc (y0 + 1) y1, (ind b - ind (b - 1)) * F b := by
    have hsdiff := Finset.sum_sdiff (s₁ := ({y0} : Finset ℤ)) (s₂ := Finset.Icc y0 y1)
      (f := fun b ↦ (ind b - ind (b - 1)) * F b) hsub
    rw [Finset.sum_singleton, h0, h0', sub_self, zero_mul, add_zero] at hsdiff
    rw [hset]
    exact hsdiff.symm
  rw [h4, h2, hshift, h3]
  rw [Finset.sum_congr rfl (fun b _ ↦ sub_mul (ind b) (ind (b - 1)) (F b))]
  rw [Finset.sum_sub_distrib]

/-- A box around the walk with a one-cell margin. -/
noncomputable def walkBox (w : ℕ → Cell) (n : ℕ) : Finset Cell :=
  Finset.Icc (wminx w n - 1) (wmaxx w n + 1) ×ˢ Finset.Icc (wminy w n - 1) (wmaxy w n + 1)

/-- `indR` vanishes outside the walk's bounding box. -/
lemma indR_eq_zero_of_outside (hn : 4 ≤ n) (hadj : ∀ i < n, Adjacent (w i) (w (i + 1)))
    (hret : w n = w 0) {c : Cell}
    (h : c.1 < wminx w n ∨ wmaxx w n ≤ c.1 ∨ c.2 < wminy w n ∨ wmaxy w n < c.2) :
    indR w n c = 0 := by
  rw [indR, if_neg]
  intro hin
  have hb := insideV_mem_box hn hadj hret hin (wminx w n) (wmaxx w n) (wminy w n) (wmaxy w n)
    (fun i hi ↦ wminx_le w n i hi) (fun i hi ↦ wmaxx_ge w n i hi)
    (fun i hi ↦ wminy_le w n i hi) (fun i hi ↦ wmaxy_ge w n i hi)
  obtain ⟨h1, h2, h3, h4⟩ := hb
  rcases h with h | h | h | h <;> omega

/-- The inside of the walk lies in the box. -/
lemma insideR_subset_box (hn : 4 ≤ n) (hadj : ∀ i < n, Adjacent (w i) (w (i + 1)))
    (hret : w n = w 0) : insideR w n ⊆ walkBox w n := by
  intro c hc
  have hin := (mem_insideR hn hadj hret).mp hc
  have hb := insideV_mem_box hn hadj hret hin (wminx w n) (wmaxx w n) (wminy w n) (wmaxy w n)
    (fun i hi ↦ wminx_le w n i hi) (fun i hi ↦ wmaxx_ge w n i hi)
    (fun i hi ↦ wminy_le w n i hi) (fun i hi ↦ wmaxy_ge w n i hi)
  obtain ⟨h1, h2, h3, h4⟩ := hb
  simp only [walkBox, Finset.mem_product, Finset.mem_Icc]
  omega

/-- A box sum, iterated with the `y`-coordinate on the outside. -/
lemma sum_walkBox_rows (F : Cell → ℤ) (w : ℕ → Cell) (n : ℕ) :
    ∑ c ∈ walkBox w n, F c = ∑ b ∈ Finset.Icc (wminy w n - 1) (wmaxy w n + 1),
      ∑ a ∈ Finset.Icc (wminx w n - 1) (wmaxx w n + 1), F (a, b) := by
  rw [walkBox, Finset.sum_product, Finset.sum_comm]

/-- The horizontal boundary sum of `φ f` over the inside region, regrouped onto
the box as a per-edge sum (Green theorem, horizontal part). -/
lemma HE_telescope (hn : 4 ≤ n) (hadj : ∀ i < n, Adjacent (w i) (w (i + 1)))
    (hinj : ∀ i < n, ∀ j < n, w i = w j → i = j) (hret : w n = w 0) :
    (∑ c ∈ insideR w n, φE S f c.1 c.2 -
      ∑ c ∈ (insideR w n).image (fun c ↦ (c.1, c.2 + 1)), φE S f c.1 c.2) =
      ∑ c ∈ walkBox w n, (indR w n c - indR w n (c.1, c.2 - 1)) * φE S f c.1 c.2 := by
  have himg : Function.Injective (fun c : Cell ↦ (c.1, c.2 + 1)) := by
    intro a b h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext_iff.mpr ⟨h.1, by omega⟩
  have hR1 : ∑ c ∈ walkBox w n, indR w n c * φE S f c.1 c.2 =
      ∑ c ∈ insideR w n, φE S f c.1 c.2 := by
    have h1 : ∑ c ∈ insideR w n, indR w n c * φE S f c.1 c.2 =
        ∑ c ∈ walkBox w n, indR w n c * φE S f c.1 c.2 :=
      Finset.sum_subset (insideR_subset_box hn hadj hret) (fun c hcB hcR ↦ by
        rw [indR_eq_zero w n (fun hin ↦ hcR ((mem_insideR hn hadj hret).mpr hin)), zero_mul])
    rw [← h1]
    apply Finset.sum_congr rfl
    intro c hc
    rw [indR_eq_one w n ((mem_insideR hn hadj hret).mp hc), one_mul]
  have hR2 : ∑ c ∈ (insideR w n).image (fun c ↦ (c.1, c.2 + 1)), φE S f c.1 c.2 =
      ∑ c ∈ walkBox w n, indR w n c * φE S f c.1 (c.2 + 1) := by
    rw [Finset.sum_image (fun x _ y _ h ↦ himg h)]
    have h1 : ∑ c ∈ insideR w n, indR w n c * φE S f c.1 (c.2 + 1) =
        ∑ c ∈ walkBox w n, indR w n c * φE S f c.1 (c.2 + 1) :=
      Finset.sum_subset (insideR_subset_box hn hadj hret) (fun c hcB hcR ↦ by
        rw [indR_eq_zero w n (fun hin ↦ hcR ((mem_insideR hn hadj hret).mpr hin)), zero_mul])
    rw [← h1]
    apply Finset.sum_congr rfl
    intro c hc
    rw [indR_eq_one w n ((mem_insideR hn hadj hret).mp hc), one_mul]
  rw [← hR1, hR2]
  have hwy : wminy w n - 1 ≤ wmaxy w n + 1 := by
    have h1 := wminy_le w n 0 (by omega)
    have h2 := wmaxy_ge w n 0 (by omega)
    omega
  simp only [walkBox, Finset.sum_product]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  exact (sum_Icc_telescope (fun b ↦ φE S f a b) (fun b ↦ indR w n (a, b)) hwy
    (indR_eq_zero_of_outside hn hadj hret (by simp))
    (indR_eq_zero_of_outside hn hadj hret (by simp))
    (indR_eq_zero_of_outside hn hadj hret (by simp))).symm

/-- The vertical boundary sum of `φ f` over the inside region, regrouped onto
the box as a per-edge sum (Green theorem, vertical part). -/
lemma VE_telescope (hn : 4 ≤ n) (hadj : ∀ i < n, Adjacent (w i) (w (i + 1)))
    (hinj : ∀ i < n, ∀ j < n, w i = w j → i = j) (hret : w n = w 0) :
    (∑ c ∈ (insideR w n).image (fun c ↦ (c.1 + 1, c.2)), φN S f c.1 c.2 -
      ∑ c ∈ insideR w n, φN S f c.1 c.2) =
      ∑ c ∈ walkBox w n, (indR w n (c.1 - 1, c.2) - indR w n c) * φN S f c.1 c.2 := by
  have himg : Function.Injective (fun c : Cell ↦ (c.1 + 1, c.2)) := by
    intro a b h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext_iff.mpr ⟨by omega, h.2⟩
  have hR1 : ∑ c ∈ walkBox w n, indR w n c * φN S f c.1 c.2 =
      ∑ c ∈ insideR w n, φN S f c.1 c.2 := by
    have h1 : ∑ c ∈ insideR w n, indR w n c * φN S f c.1 c.2 =
        ∑ c ∈ walkBox w n, indR w n c * φN S f c.1 c.2 :=
      Finset.sum_subset (insideR_subset_box hn hadj hret) (fun c hcB hcR ↦ by
        rw [indR_eq_zero w n (fun hin ↦ hcR ((mem_insideR hn hadj hret).mpr hin)), zero_mul])
    rw [← h1]
    apply Finset.sum_congr rfl
    intro c hc
    rw [indR_eq_one w n ((mem_insideR hn hadj hret).mp hc), one_mul]
  have hR2 : ∑ c ∈ (insideR w n).image (fun c ↦ (c.1 + 1, c.2)), φN S f c.1 c.2 =
      ∑ c ∈ walkBox w n, indR w n c * φN S f (c.1 + 1) c.2 := by
    rw [Finset.sum_image (fun x _ y _ h ↦ himg h)]
    have h1 : ∑ c ∈ insideR w n, indR w n c * φN S f (c.1 + 1) c.2 =
        ∑ c ∈ walkBox w n, indR w n c * φN S f (c.1 + 1) c.2 :=
      Finset.sum_subset (insideR_subset_box hn hadj hret) (fun c hcB hcR ↦ by
        rw [indR_eq_zero w n (fun hin ↦ hcR ((mem_insideR hn hadj hret).mpr hin)), zero_mul])
    rw [← h1]
    apply Finset.sum_congr rfl
    intro c hc
    rw [indR_eq_one w n ((mem_insideR hn hadj hret).mp hc), one_mul]
  rw [← hR1, hR2]
  have hwx : wminx w n - 1 ≤ wmaxx w n + 1 := by
    have h1 := wminx_le w n 0 (by omega)
    have h2 := wmaxx_ge w n 0 (by omega)
    omega
  rw [← Finset.sum_sub_distrib]
  rw [sum_walkBox_rows (fun c ↦ indR w n c * φN S f (c.1 + 1) c.2 - indR w n c * φN S f c.1 c.2) w n]
  rw [sum_walkBox_rows (fun c ↦ (indR w n (c.1 - 1, c.2) - indR w n c) * φN S f c.1 c.2) w n]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_sub_distrib]
  have htel := sum_Icc_telescope (fun a ↦ φN S f a b) (fun a ↦ indR w n (a, b)) hwx
    (indR_eq_zero_of_outside hn hadj hret (by simp))
    (indR_eq_zero_of_outside hn hadj hret (by simp))
    (indR_eq_zero_of_outside hn hadj hret (by simp))
  rw [show (∑ a ∈ Finset.Icc (wminx w n - 1) (wmaxx w n + 1), indR w n (a, b) * φN S f (a + 1) b -
        ∑ a ∈ Finset.Icc (wminx w n - 1) (wmaxx w n + 1), indR w n (a, b) * φN S f a b) =
      - (∑ a ∈ Finset.Icc (wminx w n - 1) (wmaxx w n + 1), indR w n (a, b) * φN S f a b -
        ∑ a ∈ Finset.Icc (wminx w n - 1) (wmaxx w n + 1), indR w n (a, b) * φN S f (a + 1) b) from by ring]
  rw [← htel, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- The 1-form `φ f` evaluated on a directed step `u → v` of adjacent vertices. -/
noncomputable def stepφ (S : Finset Cell) (f : Cell → Cell) (u v : Cell) : ℤ :=
  if v = (u.1 + 1, u.2) then φE S f u.1 u.2
  else if v = (u.1 - 1, u.2) then -φE S f (u.1 - 1) u.2
  else if v = (u.1, u.2 + 1) then φN S f u.1 u.2
  else -φN S f u.1 (u.2 - 1)

lemma stepφ_of_east {u v : Cell} (h : v = (u.1 + 1, u.2)) : stepφ S f u v = φE S f u.1 u.2 := by
  rw [stepφ, if_pos h]

lemma stepφ_of_west {u v : Cell} (h : v = (u.1 - 1, u.2)) :
    stepφ S f u v = -φE S f (u.1 - 1) u.2 := by
  rw [stepφ, if_neg (by intro h'; rw [h'] at h; rw [Prod.mk.injEq] at h; omega), if_pos h]

lemma stepφ_of_north {u v : Cell} (h : v = (u.1, u.2 + 1)) :
    stepφ S f u v = φN S f u.1 u.2 := by
  rw [stepφ, if_neg (by intro h'; rw [h'] at h; rw [Prod.mk.injEq] at h; omega),
    if_neg (by intro h'; rw [h'] at h; rw [Prod.mk.injEq] at h; omega), if_pos h]

lemma stepφ_of_south {u v : Cell} (h : v = (u.1, u.2 - 1)) :
    stepφ S f u v = -φN S f u.1 (u.2 - 1) := by
  rw [stepφ, if_neg (by intro h'; rw [h'] at h; rw [Prod.mk.injEq] at h; omega),
    if_neg (by intro h'; rw [h'] at h; rw [Prod.mk.injEq] at h; omega),
    if_neg (by intro h'; rw [h'] at h; rw [Prod.mk.injEq] at h; omega)]

/-- The boundary contribution of a directed step (depends only on the edge). -/
noncomputable def bndTerm (S : Finset Cell) (f : Cell → Cell) (w : ℕ → Cell) (n : ℕ)
    (u v : Cell) : ℤ :=
  if v = (u.1 + 1, u.2) then (indR w n (u.1, u.2) - indR w n (u.1, u.2 - 1)) * φE S f u.1 u.2
  else if v = (u.1 - 1, u.2) then
    (indR w n (u.1 - 1, u.2) - indR w n (u.1 - 1, u.2 - 1)) * φE S f (u.1 - 1) u.2
  else if v = (u.1, u.2 + 1) then (indR w n (u.1 - 1, u.2) - indR w n (u.1, u.2)) * φN S f u.1 u.2
  else (indR w n (u.1 - 1, u.2 - 1) - indR w n (u.1, u.2 - 1)) * φN S f u.1 (u.2 - 1)

lemma bndTerm_of_east {u v : Cell} (h : v = (u.1 + 1, u.2)) :
    bndTerm S f w n u v = (indR w n (u.1, u.2) - indR w n (u.1, u.2 - 1)) * φE S f u.1 u.2 := by
  rw [bndTerm, if_pos h]

lemma bndTerm_of_west {u v : Cell} (h : v = (u.1 - 1, u.2)) :
    bndTerm S f w n u v =
      (indR w n (u.1 - 1, u.2) - indR w n (u.1 - 1, u.2 - 1)) * φE S f (u.1 - 1) u.2 := by
  rw [bndTerm, if_neg (by intro h'; rw [h'] at h; rw [Prod.mk.injEq] at h; omega), if_pos h]

lemma bndTerm_of_north {u v : Cell} (h : v = (u.1, u.2 + 1)) :
    bndTerm S f w n u v = (indR w n (u.1 - 1, u.2) - indR w n (u.1, u.2)) * φN S f u.1 u.2 := by
  rw [bndTerm, if_neg (by intro h'; rw [h'] at h; rw [Prod.mk.injEq] at h; omega),
    if_neg (by intro h'; rw [h'] at h; rw [Prod.mk.injEq] at h; omega), if_pos h]

lemma bndTerm_of_south {u v : Cell} (h : v = (u.1, u.2 - 1)) :
    bndTerm S f w n u v =
      (indR w n (u.1 - 1, u.2 - 1) - indR w n (u.1, u.2 - 1)) * φN S f u.1 (u.2 - 1) := by
  rw [bndTerm, if_neg (by intro h'; rw [h'] at h; rw [Prod.mk.injEq] at h; omega),
    if_neg (by intro h'; rw [h'] at h; rw [Prod.mk.injEq] at h; omega),
    if_neg (by intro h'; rw [h'] at h; rw [Prod.mk.injEq] at h; omega)]

/-- Each step of the walk contributes `σ · bndTerm`, where `σ = ±1` is the global
orientation sign (inside on the left, or not). -/
lemma stepφ_eq_σ_bndTerm (hn : 4 ≤ n) (hadj : ∀ i < n, Adjacent (w i) (w (i + 1)))
    (hinj : ∀ i < n, ∀ j < n, w i = w j → i = j) (hret : w n = w 0)
    {i : ℕ} (hi : i < n) :
    stepφ S f (w i) (w (i + 1)) =
      (if insideV w n (leftCell (w 0) (w 1)) then (1 : ℤ) else -1) *
        bndTerm S f w n (w i) (w (i + 1)) := by
  rcases adjacent_cases (hadj i hi) with hdir | hdir | hdir | hdir
  · -- east step
    rw [stepφ_of_east hdir, bndTerm_of_east hdir]
    have hedge : ({((w i).1, (w i).2), ((w i).1 + 1, (w i).2)} : Finset Cell) ∈ cycEdgesV w n := by
      rw [mem_cycEdgesV]
      exact ⟨i, Finset.mem_range.mpr hi, by rw [hdir, Prod.eta]⟩
    have hdiff := (indR_ne_across_horizontal hn hadj hinj hret (w i).1 (w i).2).mpr hedge
    have hdiff' := (indR_ne_iff w n).mp hdiff
    have hleft : insideV w n ((w i).1, (w i).2) ↔ insideV w n (leftCell (w 0) (w 1)) := by
      have h1 := leftIn_const hn hadj hinj hret i hi
      rw [leftCell_of_east hdir] at h1
      exact h1
    by_cases h0 : insideV w n (leftCell (w 0) (w 1))
    · rw [if_pos h0]
      have hi1 : insideV w n ((w i).1, (w i).2) := hleft.mpr h0
      have hi2 : ¬ insideV w n ((w i).1, (w i).2 - 1) := hdiff'.mp hi1
      rw [indR_eq_one w n hi1, indR_eq_zero w n hi2]
      ring
    · rw [if_neg h0]
      have hi1 : ¬ insideV w n ((w i).1, (w i).2) := fun h ↦ h0 (hleft.mp h)
      have hi2 : insideV w n ((w i).1, (w i).2 - 1) := by
        by_contra hcon
        exact hi1 (hdiff'.mpr hcon)
      rw [indR_eq_zero w n hi1, indR_eq_one w n hi2]
      ring
  · -- west step
    rw [stepφ_of_west hdir, bndTerm_of_west hdir]
    have hedge : ({((w i).1 - 1, (w i).2), ((w i).1 - 1 + 1, (w i).2)} : Finset Cell) ∈ cycEdgesV w n := by
      rw [mem_cycEdgesV]
      refine ⟨i, Finset.mem_range.mpr hi, ?_⟩
      have key : ((w i).1 - 1 + 1, (w i).2) = w i := by
        rw [← Prod.eta (w i), Prod.mk.injEq]
        constructor <;> simp
      rw [hdir, key]
      ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    have hdiff := (indR_ne_across_horizontal hn hadj hinj hret ((w i).1 - 1) (w i).2).mpr hedge
    have hdiff' := (indR_ne_iff w n).mp hdiff
    have hleft : insideV w n ((w i).1 - 1, (w i).2 - 1) ↔ insideV w n (leftCell (w 0) (w 1)) := by
      have h1 := leftIn_const hn hadj hinj hret i hi
      rw [leftCell_of_west hdir] at h1
      exact h1
    by_cases h0 : insideV w n (leftCell (w 0) (w 1))
    · rw [if_pos h0]
      have hi1 : insideV w n ((w i).1 - 1, (w i).2 - 1) := hleft.mpr h0
      have hi2 : ¬ insideV w n ((w i).1 - 1, (w i).2) := fun hA ↦ (hdiff'.mp hA) hi1
      rw [indR_eq_one w n hi1, indR_eq_zero w n hi2]
      ring
    · rw [if_neg h0]
      have hi1 : ¬ insideV w n ((w i).1 - 1, (w i).2 - 1) := fun h ↦ h0 (hleft.mp h)
      have hi2 : insideV w n ((w i).1 - 1, (w i).2) := hdiff'.mpr hi1
      rw [indR_eq_zero w n hi1, indR_eq_one w n hi2]
      ring
  · -- north step
    rw [stepφ_of_north hdir, bndTerm_of_north hdir]
    have hedge : ({((w i).1, (w i).2), ((w i).1, (w i).2 + 1)} : Finset Cell) ∈ cycEdgesV w n := by
      rw [mem_cycEdgesV]
      exact ⟨i, Finset.mem_range.mpr hi, by rw [hdir, Prod.eta]⟩
    have hdiff := (indR_ne_across_vertical hn hinj hret ((w i).1) (w i).2).mpr hedge
    have hdiff' := (indR_ne_iff w n).mp hdiff
    have hleft : insideV w n ((w i).1 - 1, (w i).2) ↔ insideV w n (leftCell (w 0) (w 1)) := by
      have h1 := leftIn_const hn hadj hinj hret i hi
      rw [leftCell_of_north hdir] at h1
      exact h1
    by_cases h0 : insideV w n (leftCell (w 0) (w 1))
    · rw [if_pos h0]
      have hi1 : insideV w n ((w i).1 - 1, (w i).2) := hleft.mpr h0
      have hi2 : ¬ insideV w n ((w i).1, (w i).2) := hdiff'.mp hi1
      rw [indR_eq_one w n hi1, indR_eq_zero w n hi2]
      ring
    · rw [if_neg h0]
      have hi1 : ¬ insideV w n ((w i).1 - 1, (w i).2) := fun h ↦ h0 (hleft.mp h)
      have hi2 : insideV w n ((w i).1, (w i).2) := by
        by_contra hcon
        exact hi1 (hdiff'.mpr hcon)
      rw [indR_eq_zero w n hi1, indR_eq_one w n hi2]
      ring
  · -- south step
    rw [stepφ_of_south hdir, bndTerm_of_south hdir]
    have hedge : ({((w i).1, (w i).2 - 1), ((w i).1, (w i).2 - 1 + 1)} : Finset Cell) ∈ cycEdgesV w n := by
      rw [mem_cycEdgesV]
      refine ⟨i, Finset.mem_range.mpr hi, ?_⟩
      have key : ((w i).1, (w i).2 - 1 + 1) = w i := by
        rw [← Prod.eta (w i), Prod.mk.injEq]
        constructor <;> simp
      rw [hdir, key]
      ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    have hdiff := (indR_ne_across_vertical hn hinj hret ((w i).1) ((w i).2 - 1)).mpr hedge
    have hdiff' := (indR_ne_iff w n).mp hdiff
    have hleft : insideV w n ((w i).1, (w i).2 - 1) ↔ insideV w n (leftCell (w 0) (w 1)) := by
      have h1 := leftIn_const hn hadj hinj hret i hi
      rw [leftCell_of_south hdir] at h1
      exact h1
    by_cases h0 : insideV w n (leftCell (w 0) (w 1))
    · rw [if_pos h0]
      have hi1 : insideV w n ((w i).1, (w i).2 - 1) := hleft.mpr h0
      have hi2 : ¬ insideV w n ((w i).1 - 1, (w i).2 - 1) := fun hA ↦ (hdiff'.mp hA) hi1
      rw [indR_eq_one w n hi1, indR_eq_zero w n hi2]
      ring
    · rw [if_neg h0]
      have hi1 : ¬ insideV w n ((w i).1, (w i).2 - 1) := fun h ↦ h0 (hleft.mp h)
      have hi2 : insideV w n ((w i).1 - 1, (w i).2 - 1) := hdiff'.mpr hi1
      rw [indR_eq_zero w n hi1, indR_eq_one w n hi2]
      ring

/-- The left vertex of a horizontal step. -/
noncomputable def hLeft (u v : Cell) : Cell := (min u.1 v.1, u.2)

/-- A horizontal step's edge is determined by its left vertex. -/
lemma cycEdge_of_horiz {u v : Cell} (hadj : Adjacent u v) (hy : u.2 = v.2) :
    ({u, v} : Finset Cell) = {hLeft u v, ((hLeft u v).1 + 1, (hLeft u v).2)} := by
  rcases adjacent_cases hadj with h | h | h | h
  · rw [h]
    have hm : min u.1 (u.1 + 1) = u.1 := min_eq_left (by omega)
    simp [hLeft, hm, Prod.eta]
  · rw [h]
    have hm : min u.1 (u.1 - 1) = u.1 - 1 := min_eq_right (by omega)
    simp [hLeft, hm, Prod.eta]
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · exfalso; rw [h] at hy; simp at hy
  · exfalso; rw [h] at hy; simp at hy; omega

/-- The sum of `bndTerm` over the horizontal steps equals the horizontal
boundary sum over the box (edge bijection, horizontal part). -/
lemma sum_bndTerm_horiz (hn : 4 ≤ n) (hadj : ∀ i < n, Adjacent (w i) (w (i + 1)))
    (hinj : ∀ i < n, ∀ j < n, w i = w j → i = j) (hret : w n = w 0) :
    ∑ i ∈ (Finset.range n).filter (fun i ↦ (w i).2 = (w (i + 1)).2),
        bndTerm S f w n (w i) (w (i + 1)) =
      ∑ c ∈ walkBox w n, (indR w n c - indR w n (c.1, c.2 - 1)) * φE S f c.1 c.2 := by
  classical
  have hsub : ((Finset.range n).filter (fun i ↦ (w i).2 = (w (i + 1)).2)).image
      (fun i ↦ hLeft (w i) (w (i + 1))) ⊆ walkBox w n := by
    intro c hc
    rw [Finset.mem_image] at hc
    obtain ⟨i, hi, hci⟩ := hc
    rw [Finset.mem_filter] at hi
    obtain ⟨hir, hiy⟩ := hi
    have hir' := Finset.mem_range.mp hir
    have hadj_i := hadj i hir'
    have hsucc : (w (i + 1)).1 ≤ wmaxx w n ∧ wminx w n ≤ (w (i + 1)).1 ∧
        wminy w n ≤ (w (i + 1)).2 ∧ (w (i + 1)).2 ≤ wmaxy w n := by
      by_cases hi1 : i + 1 < n
      · exact ⟨wmaxx_ge w n (i + 1) hi1, wminx_le w n (i + 1) hi1,
          wminy_le w n (i + 1) hi1, wmaxy_ge w n (i + 1) hi1⟩
      · have hi1' : i + 1 = n := by omega
        rw [hi1', hret]
        exact ⟨wmaxx_ge w n 0 (by omega), wminx_le w n 0 (by omega),
          wminy_le w n 0 (by omega), wmaxy_ge w n 0 (by omega)⟩
    obtain ⟨hx1, hx2, hy1, hy2⟩ := hsucc
    have hxi : wminx w n ≤ (w i).1 ∧ (w i).1 ≤ wmaxx w n :=
      ⟨wminx_le w n i hir', wmaxx_ge w n i hir'⟩
    have hyi : wminy w n ≤ (w i).2 ∧ (w i).2 ≤ wmaxy w n :=
      ⟨wminy_le w n i hir', wmaxy_ge w n i hir'⟩
    rw [← hci]
    simp only [hLeft, walkBox, Finset.mem_product, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rcases adjacent_cases hadj_i with h | h | h | h <;> rw [h] <;> simp [min] <;> omega
    · rcases adjacent_cases hadj_i with h | h | h | h <;> rw [h] <;> simp [min] <;> omega
    · omega
  have hvanish : ∀ c ∈ walkBox w n,
      c ∉ ((Finset.range n).filter (fun i ↦ (w i).2 = (w (i + 1)).2)).image
        (fun i ↦ hLeft (w i) (w (i + 1))) →
      (indR w n c - indR w n (c.1, c.2 - 1)) * φE S f c.1 c.2 = 0 := by
    intro c hcB hcimg
    by_contra hne
    have hdiff : indR w n c ≠ indR w n (c.1, c.2 - 1) := by
      intro heq
      apply hne
      rw [heq, sub_self, zero_mul]
    have hedge := (indR_ne_across_horizontal hn hadj hinj hret c.1 c.2).mp hdiff
    rw [mem_cycEdgesV] at hedge
    obtain ⟨i, hi, hei⟩ := hedge
    have hir' := Finset.mem_range.mp hi
    apply hcimg
    rw [Finset.mem_image]
    have hne2 : w i ≠ w (i + 1) := walkV_ne_succ hn hinj hret i hir'
    have hadj_i := hadj i hir'
    refine ⟨i, Finset.mem_filter.mpr ⟨hi, ?_⟩, ?_⟩
    · rcases pair_eq_pairV hne2 hei with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [e1, e2]
      · rw [e1, e2]
    · rcases pair_eq_pairV hne2 hei with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [e1, e2]
        simp [hLeft, min]
      · rw [e1, e2]
        simp [hLeft, min]
  rw [← Finset.sum_subset hsub hvanish]
  have hinj' : ∀ i ∈ (Finset.range n).filter (fun i ↦ (w i).2 = (w (i + 1)).2),
      ∀ j ∈ (Finset.range n).filter (fun i ↦ (w i).2 = (w (i + 1)).2),
      hLeft (w i) (w (i + 1)) = hLeft (w j) (w (j + 1)) → i = j := by
    intro i hi j hj hij
    rw [Finset.mem_filter] at hi hj
    have hi' := Finset.mem_range.mp hi.1
    have hj' := Finset.mem_range.mp hj.1
    apply cycEdgesV_inj hn hinj hret hi' hj'
    have hadj_i := hadj i hi'
    have hadj_j := hadj j hj'
    rw [cycEdge_of_horiz hadj_i hi.2, cycEdge_of_horiz hadj_j hj.2, hij]
  rw [Finset.sum_image hinj']
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_filter] at hi
  obtain ⟨hir, hiy⟩ := hi
  have hir' := Finset.mem_range.mp hir
  have hadj_i := hadj i hir'
  rcases adjacent_cases hadj_i with hdir | hdir | hdir | hdir
  · rw [bndTerm_of_east hdir, hdir]
    simp [hLeft, min_eq_left (by omega : (w i).1 ≤ (w i).1 + 1)]
  · rw [bndTerm_of_west hdir, hdir]
    simp [hLeft, min_eq_right (by omega : (w i).1 - 1 ≤ (w i).1)]
  · exfalso
    rw [hdir] at hiy
    simp at hiy
  · exfalso
    rw [hdir] at hiy
    simp at hiy; omega

/-- The bottom vertex of a vertical step. -/
noncomputable def botV (u v : Cell) : Cell := (u.1, min u.2 v.2)

/-- A vertical step's edge is determined by its bottom vertex. -/
lemma cycEdge_of_vert {u v : Cell} (hadj : Adjacent u v) (hy : u.2 ≠ v.2) :
    ({u, v} : Finset Cell) = {botV u v, ((botV u v).1, (botV u v).2 + 1)} := by
  rcases adjacent_cases hadj with h | h | h | h
  · exfalso; rw [h] at hy; simp at hy
  · exfalso; rw [h] at hy; simp at hy
  · rw [h]
    have hm : min u.2 (u.2 + 1) = u.2 := min_eq_left (by omega)
    simp [botV, hm, Prod.eta]
  · rw [h]
    have hm : min u.2 (u.2 - 1) = u.2 - 1 := min_eq_right (by omega)
    simp [botV, hm, Prod.eta]
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto

/-- The sum of `bndTerm` over the vertical steps equals the vertical
boundary sum over the box (edge bijection, vertical part). -/
lemma sum_bndTerm_vert (hn : 4 ≤ n) (hadj : ∀ i < n, Adjacent (w i) (w (i + 1)))
    (hinj : ∀ i < n, ∀ j < n, w i = w j → i = j) (hret : w n = w 0) :
    ∑ i ∈ (Finset.range n).filter (fun i ↦ ¬ ((w i).2 = (w (i + 1)).2)),
        bndTerm S f w n (w i) (w (i + 1)) =
      ∑ c ∈ walkBox w n, (indR w n (c.1 - 1, c.2) - indR w n c) * φN S f c.1 c.2 := by
  classical
  have hsub : ((Finset.range n).filter (fun i ↦ ¬ ((w i).2 = (w (i + 1)).2))).image
      (fun i ↦ botV (w i) (w (i + 1))) ⊆ walkBox w n := by
    intro c hc
    rw [Finset.mem_image] at hc
    obtain ⟨i, hi, hci⟩ := hc
    rw [Finset.mem_filter] at hi
    obtain ⟨hir, hiy⟩ := hi
    have hir' := Finset.mem_range.mp hir
    have hadj_i := hadj i hir'
    have hsucc : (w (i + 1)).1 ≤ wmaxx w n ∧ wminx w n ≤ (w (i + 1)).1 ∧
        wminy w n ≤ (w (i + 1)).2 ∧ (w (i + 1)).2 ≤ wmaxy w n := by
      by_cases hi1 : i + 1 < n
      · exact ⟨wmaxx_ge w n (i + 1) hi1, wminx_le w n (i + 1) hi1,
          wminy_le w n (i + 1) hi1, wmaxy_ge w n (i + 1) hi1⟩
      · have hi1' : i + 1 = n := by omega
        rw [hi1', hret]
        exact ⟨wmaxx_ge w n 0 (by omega), wminx_le w n 0 (by omega),
          wminy_le w n 0 (by omega), wmaxy_ge w n 0 (by omega)⟩
    obtain ⟨hx1, hx2, hy1, hy2⟩ := hsucc
    have hxi : wminx w n ≤ (w i).1 ∧ (w i).1 ≤ wmaxx w n :=
      ⟨wminx_le w n i hir', wmaxx_ge w n i hir'⟩
    have hyi : wminy w n ≤ (w i).2 ∧ (w i).2 ≤ wmaxy w n :=
      ⟨wminy_le w n i hir', wmaxy_ge w n i hir'⟩
    rw [← hci]
    simp only [botV, walkBox, Finset.mem_product, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · omega
    · omega
    · rcases adjacent_cases hadj_i with h | h | h | h <;> rw [h] <;> simp [min] <;> omega
  have hvanish : ∀ c ∈ walkBox w n,
      c ∉ ((Finset.range n).filter (fun i ↦ ¬ ((w i).2 = (w (i + 1)).2))).image
        (fun i ↦ botV (w i) (w (i + 1))) →
      (indR w n (c.1 - 1, c.2) - indR w n c) * φN S f c.1 c.2 = 0 := by
    intro c hcB hcimg
    by_contra hne
    have hdiff : indR w n (c.1 - 1, c.2) ≠ indR w n c := by
      intro heq
      apply hne
      rw [heq, sub_self, zero_mul]
    have hedge := (indR_ne_across_vertical hn hinj hret c.1 c.2).mp hdiff
    rw [mem_cycEdgesV] at hedge
    obtain ⟨i, hi, hei⟩ := hedge
    have hir' := Finset.mem_range.mp hi
    apply hcimg
    rw [Finset.mem_image]
    have hne2 : w i ≠ w (i + 1) := walkV_ne_succ hn hinj hret i hir'
    have hadj_i := hadj i hir'
    refine ⟨i, Finset.mem_filter.mpr ⟨hi, ?_⟩, ?_⟩
    · rcases pair_eq_pairV hne2 hei with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [e1, e2]; simp
      · rw [e1, e2]; simp
    · rcases pair_eq_pairV hne2 hei with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [e1, e2]
        simp [botV, min]
      · rw [e1, e2]
        simp [botV, min]
  rw [← Finset.sum_subset hsub hvanish]
  have hinj' : ∀ i ∈ (Finset.range n).filter (fun i ↦ ¬ ((w i).2 = (w (i + 1)).2)),
      ∀ j ∈ (Finset.range n).filter (fun i ↦ ¬ ((w i).2 = (w (i + 1)).2)),
      botV (w i) (w (i + 1)) = botV (w j) (w (j + 1)) → i = j := by
    intro i hi j hj hij
    rw [Finset.mem_filter] at hi hj
    have hi' := Finset.mem_range.mp hi.1
    have hj' := Finset.mem_range.mp hj.1
    apply cycEdgesV_inj hn hinj hret hi' hj'
    have hadj_i := hadj i hi'
    have hadj_j := hadj j hj'
    rw [cycEdge_of_vert hadj_i hi.2, cycEdge_of_vert hadj_j hj.2, hij]
  rw [Finset.sum_image hinj']
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_filter] at hi
  obtain ⟨hir, hiy⟩ := hi
  have hir' := Finset.mem_range.mp hir
  have hadj_i := hadj i hir'
  rcases adjacent_cases hadj_i with hdir | hdir | hdir | hdir
  · exfalso
    rw [hdir] at hiy
    simp at hiy
  · exfalso
    rw [hdir] at hiy
    simp at hiy
  · rw [bndTerm_of_north hdir, hdir]
    simp [botV, min_eq_left (by omega : (w i).2 ≤ (w i).2 + 1)]
  · rw [bndTerm_of_south hdir, hdir]
    simp [botV, min_eq_right (by omega : (w i).2 - 1 ≤ (w i).2)]

/-- The discrete Green theorem for a simple closed walk whose inside lies in
`S`: the descent-direction sum of `φ f` around the walk vanishes. -/
lemma cycSum_eq_zero (hf : IsTiling S f) (hn : 4 ≤ n)
    (hadj : ∀ i < n, Adjacent (w i) (w (i + 1)))
    (hinj : ∀ i < n, ∀ j < n, w i = w j → i = j) (hret : w n = w 0)
    (hinside : ∀ c : Cell, insideV w n c → c ∈ S) :
    ∑ i ∈ Finset.range n, stepφ S f (w i) (w (i + 1)) = 0 := by
  have h1 : ∑ i ∈ Finset.range n, stepφ S f (w i) (w (i + 1)) =
      (if insideV w n (leftCell (w 0) (w 1)) then (1 : ℤ) else -1) *
        ∑ i ∈ Finset.range n, bndTerm S f w n (w i) (w (i + 1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact stepφ_eq_σ_bndTerm hn hadj hinj hret (Finset.mem_range.mp hi)
  rw [h1]
  have h2 : ∑ i ∈ Finset.range n, bndTerm S f w n (w i) (w (i + 1)) = 0 := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range n) (fun i ↦ (w i).2 = (w (i + 1)).2)
      (fun i ↦ bndTerm S f w n (w i) (w (i + 1)))]
    rw [sum_bndTerm_horiz hn hadj hinj hret, sum_bndTerm_vert hn hadj hinj hret]
    rw [← HE_telescope hn hadj hinj hret, ← VE_telescope hn hadj hinj hret]
    rw [← sum_defect]
    apply Finset.sum_eq_zero
    intro c hc
    exact defect_eq_zero_of_mem hf (hinside c ((mem_insideR hn hadj hret).mp hc))
  rw [h2, mul_zero]

end GreenSum

-- ============================================================
-- The descent argument for the crux (E)
-- ============================================================

section Descent

variable {S : Finset Cell} {f g : Cell → Cell}

/-- The difference 1-form on an east edge, in terms of the crossing indicators. -/
lemma ΔE_eq (hf : IsTiling S f) (hg : IsTiling S g) (a b : ℤ) :
    ΔE S f g a b = 4 * (if Even (a + b) then (1 : ℤ) else -1) *
      ((if crE S g a b then (1 : ℤ) else 0) - (if crE S f a b then (1 : ℤ) else 0)) := by
  rw [ΔE, φE, φE]
  by_cases hpar : Even (a + b) <;> by_cases hcf : crE S f a b <;> by_cases hcg : crE S g a b <;>
    simp [hpar, hcf, hcg] <;> ring

/-- The difference 1-form on a north edge, in terms of the crossing indicators. -/
lemma ΔN_eq (hf : IsTiling S f) (hg : IsTiling S g) (a b : ℤ) :
    ΔN S f g a b = 4 * (if Even (a + b) then (-1 : ℤ) else 1) *
      ((if crN S g a b then (1 : ℤ) else 0) - (if crN S f a b then (1 : ℤ) else 0)) := by
  rw [ΔN, φN, φN]
  by_cases hpar : Even (a + b) <;> by_cases hcf : crN S f a b <;> by_cases hcg : crN S g a b <;>
    simp [hpar, hcf, hcg] <;> ring

/-- The value of `φ f` on an east step, in terms of the crossing indicator. -/
lemma φE_eq (hf : IsTiling S f) (a b : ℤ) :
    φE S f a b = (if Even (a + b) then (1 : ℤ) else -1) * (if crE S f a b then -3 else 1) := by
  rw [φE]

/-- The value of `φ f` on a north step, in terms of the crossing indicator. -/
lemma φN_eq (hf : IsTiling S f) (a b : ℤ) :
    φN S f a b = (if Even (a + b) then (-1 : ℤ) else 1) * (if crN S f a b then -3 else 1) := by
  rw [φN]

/-- A descent step to the east neighbour across a bad edge. -/
lemma descent_east (hf : IsTiling S f) (hg : IsTiling S g) {a b : ℤ}
    (hE : 0 ≤ ΔE S f g a b)
    (hbad : (Even (a + b) ∧ crE S f a b) ∨ (¬ Even (a + b) ∧ ¬ crE S f a b)) :
    Adjacent (a, b) (a + 1, b) ∧ D S f g (a + 1) b = D S f g a b ∧
      stepφ S f (a, b) (a + 1, b) < 0 := by
  have hΔ : ΔE S f g a b = 0 := by
    rw [ΔE_eq hf hg] at hE ⊢
    rcases hbad with ⟨hpar, hu⟩ | ⟨hpar, hu⟩ <;>
      by_cases hcg : crE S g a b <;>
      simp only [hpar, hu, hcg, if_true, if_false] at hE ⊢ <;> omega
  refine ⟨by simp [Adjacent], ?_, ?_⟩
  · have h2 := D_east hf hg (a := a) (b := b)
    rw [hΔ] at h2
    simp at h2
    exact h2
  · rw [stepφ_of_east rfl, φE_eq hf]
    rcases hbad with ⟨hpar, hu⟩ | ⟨hpar, hu⟩ <;>
      simp only [hpar, hu, if_true, if_false] <;> omega

/-- A descent step to the west neighbour across a bad edge. -/
lemma descent_west (hf : IsTiling S f) (hg : IsTiling S g) {a b : ℤ}
    (hW : ΔE S f g (a - 1) b ≤ 0)
    (hbad : (¬ Even (a - 1 + b) ∧ crE S f (a - 1) b) ∨ (Even (a - 1 + b) ∧ ¬ crE S f (a - 1) b)) :
    Adjacent (a, b) (a - 1, b) ∧ D S f g (a - 1) b = D S f g a b ∧
      stepφ S f (a, b) (a - 1, b) < 0 := by
  have hΔ : ΔE S f g (a - 1) b = 0 := by
    rw [ΔE_eq hf hg] at hW ⊢
    rcases hbad with ⟨hpar, hu⟩ | ⟨hpar, hu⟩ <;>
      by_cases hcg : crE S g (a - 1) b <;>
      simp only [hpar, hu, hcg, if_true, if_false] at hW ⊢ <;> omega
  refine ⟨by simp [Adjacent], ?_, ?_⟩
  · have h2 := D_east hf hg (a := a - 1) (b := b)
    rw [hΔ] at h2
    rw [show a - 1 + 1 = a from by ring] at h2
    simp at h2
    exact h2.symm
  · rw [stepφ_of_west rfl, φE_eq hf]
    rcases hbad with ⟨hpar, hu⟩ | ⟨hpar, hu⟩ <;>
      simp only [hpar, hu, if_true, if_false] <;> omega

/-- A descent step to the north neighbour across a bad edge. -/
lemma descent_north (hf : IsTiling S f) (hg : IsTiling S g) {a b : ℤ}
    (hN : 0 ≤ ΔN S f g a b)
    (hbad : (¬ Even (a + b) ∧ crN S f a b) ∨ (Even (a + b) ∧ ¬ crN S f a b)) :
    Adjacent (a, b) (a, b + 1) ∧ D S f g a (b + 1) = D S f g a b ∧
      stepφ S f (a, b) (a, b + 1) < 0 := by
  have hΔ : ΔN S f g a b = 0 := by
    rw [ΔN_eq hf hg] at hN ⊢
    rcases hbad with ⟨hpar, hu⟩ | ⟨hpar, hu⟩ <;>
      by_cases hcg : crN S g a b <;>
      simp only [hpar, hu, hcg, if_true, if_false] at hN ⊢ <;> omega
  refine ⟨by simp [Adjacent], ?_, ?_⟩
  · have h2 := D_north hf hg (a := a) (b := b)
    rw [hΔ] at h2
    simp at h2
    exact h2
  · rw [stepφ_of_north rfl, φN_eq hf]
    rcases hbad with ⟨hpar, hu⟩ | ⟨hpar, hu⟩ <;>
      simp only [hpar, hu, if_true, if_false] <;> omega

/-- A descent step to the south neighbour across a bad edge. -/
lemma descent_south (hf : IsTiling S f) (hg : IsTiling S g) {a b : ℤ}
    (hS : ΔN S f g a (b - 1) ≤ 0)
    (hbad : (Even (a + (b - 1)) ∧ crN S f a (b - 1)) ∨ (¬ Even (a + (b - 1)) ∧ ¬ crN S f a (b - 1))) :
    Adjacent (a, b) (a, b - 1) ∧ D S f g a (b - 1) = D S f g a b ∧
      stepφ S f (a, b) (a, b - 1) < 0 := by
  have hΔ : ΔN S f g a (b - 1) = 0 := by
    rw [ΔN_eq hf hg] at hS ⊢
    rcases hbad with ⟨hpar, hu⟩ | ⟨hpar, hu⟩ <;>
      by_cases hcg : crN S g a (b - 1) <;>
      simp only [hpar, hu, hcg, if_true, if_false] at hS ⊢ <;> omega
  refine ⟨by simp [Adjacent], ?_, ?_⟩
  · have h2 := D_north hf hg (a := a) (b := b - 1)
    rw [hΔ] at h2
    rw [show b - 1 + 1 = b from by ring] at h2
    simp at h2
    exact h2.symm
  · rw [stepφ_of_south rfl, φN_eq hf]
    rcases hbad with ⟨hpar, hu⟩ | ⟨hpar, hu⟩ <;>
      simp only [hpar, hu, if_true, if_false] <;> omega

/-- The local step of the descent: at a `D`-minimal vertex, either there is a
distasteful pair (the "pattern"), or a descent step to a `D`-minimal neighbour
across which `φ f` is negative. -/
lemma descent_step (hf : IsTiling S f) (hg : IsTiling S g) {v : Cell}
    (hmin : ∀ w : Cell, D S f g v.1 v.2 ≤ D S f g w.1 w.2) :
    (crN S f v.1 v.2 ∧ crN S f v.1 (v.2 - 1) ∧ Even (v.1 + v.2)) ∨
    (crE S f v.1 v.2 ∧ crE S f (v.1 - 1) v.2 ∧ Odd (v.1 + v.2)) ∨
    ∃ w : Cell, Adjacent v w ∧ D S f g w.1 w.2 = D S f g v.1 v.2 ∧ stepφ S f v w < 0 := by
  obtain ⟨a, b⟩ := v
  have hE : 0 ≤ ΔE S f g a b := by
    have h := hmin (a + 1, b)
    have h2 := D_east hf hg (a := a) (b := b)
    simp at h
    omega
  have hN : 0 ≤ ΔN S f g a b := by
    have h := hmin (a, b + 1)
    have h2 := D_north hf hg (a := a) (b := b)
    simp at h
    omega
  have hW : ΔE S f g (a - 1) b ≤ 0 := by
    have h := hmin (a - 1, b)
    have h2 := D_east hf hg (a := a - 1) (b := b)
    simp at h
    rw [show a - 1 + 1 = a from by ring] at h2
    omega
  have hS : ΔN S f g a (b - 1) ≤ 0 := by
    have h := hmin (a, b - 1)
    have h2 := D_north hf hg (a := a) (b := b - 1)
    simp at h
    rw [show b - 1 + 1 = b from by ring] at h2
    omega
  by_cases hpar : Even (a + b)
  · -- σ_E = σ_W = +1, σ_N = σ_S = -1
    by_cases huN : crN S f a b
    · by_cases huS : crN S f a (b - 1)
      · by_cases huE : crE S f a b
        · -- bad edge E (σ⁺, u_f = 1)
          exact Or.inr (Or.inr ⟨(a + 1, b), descent_east hf hg hE (Or.inl ⟨hpar, huE⟩)⟩)
        · by_cases huW : crE S f (a - 1) b
          · -- bad edge W (σ⁺, u_f = 1)
            have hpar' : ¬ Even (a - 1 + b) := by
              intro h
              obtain ⟨k, hk⟩ := hpar
              obtain ⟨m, hm⟩ := h
              omega
            exact Or.inr (Or.inr ⟨(a - 1, b), descent_west hf hg hW (Or.inl ⟨hpar', huW⟩)⟩)
          · -- pattern N
            exact Or.inl ⟨huN, huS, hpar⟩
      · -- bad edge S (σ⁻, u_f = 0)
        have hpar'' : ¬ Even (a + (b - 1)) := by
          intro h
          obtain ⟨k, hk⟩ := hpar
          obtain ⟨m, hm⟩ := h
          omega
        exact Or.inr (Or.inr ⟨(a, b - 1), descent_south hf hg hS (Or.inr ⟨hpar'', huS⟩)⟩)
    · -- bad edge N (σ⁻, u_f = 0)
      exact Or.inr (Or.inr ⟨(a, b + 1), descent_north hf hg hN (Or.inr ⟨hpar, huN⟩)⟩)
  · -- Odd (a + b): σ_E = σ_W = -1, σ_N = σ_S = +1
    have hpar' : ¬ Even (a + b) := hpar
    by_cases huE : crE S f a b
    · by_cases huW : crE S f (a - 1) b
      · by_cases huN : crN S f a b
        · -- bad edge N (σ⁺, u_f = 1)
          exact Or.inr (Or.inr ⟨(a, b + 1), descent_north hf hg hN (Or.inl ⟨hpar', huN⟩)⟩)
        · by_cases huS : crN S f a (b - 1)
          · -- bad edge S (σ⁺, u_f = 1)
            have hpar'' : Even (a + (b - 1)) := by
              obtain ⟨k, hk⟩ := Int.not_even_iff_odd.mp hpar
              exact ⟨k, by omega⟩
            exact Or.inr (Or.inr ⟨(a, b - 1), descent_south hf hg hS (Or.inl ⟨hpar'', huS⟩)⟩)
          · -- pattern E
            exact Or.inr (Or.inl ⟨huE, huW, Int.not_even_iff_odd.mp hpar⟩)
      · -- bad edge W (σ⁻, u_f = 0)
        have hpar'' : Even (a - 1 + b) := by
          obtain ⟨k, hk⟩ := Int.not_even_iff_odd.mp hpar
          exact ⟨k, by omega⟩
        exact Or.inr (Or.inr ⟨(a - 1, b), descent_west hf hg hW (Or.inr ⟨hpar'', huW⟩)⟩)
    · -- bad edge E (σ⁻, u_f = 0)
      exact Or.inr (Or.inr ⟨(a + 1, b), descent_east hf hg hE (Or.inr ⟨hpar, huE⟩)⟩)

/-- The descent-step choice function: a neighbour across a bad edge, if any. -/
noncomputable def nextV (hf : IsTiling S f) (hg : IsTiling S g) (u : Cell) : Cell :=
  if h : ∃ w : Cell, Adjacent u w ∧ D S f g w.1 w.2 = D S f g u.1 u.2 ∧ stepφ S f u w < 0 then
    h.choose
  else u

/-- For a `D`-minimal vertex with no distasteful pattern, `nextV` is a descent step. -/
lemma nextV_step (hf : IsTiling S f) (hg : IsTiling S g) {u : Cell}
    (hmin : ∀ w : Cell, D S f g u.1 u.2 ≤ D S f g w.1 w.2)
    (hnopat : ¬ ((crN S f u.1 u.2 ∧ crN S f u.1 (u.2 - 1) ∧ Even (u.1 + u.2)) ∨
      (crE S f u.1 u.2 ∧ crE S f (u.1 - 1) u.2 ∧ Odd (u.1 + u.2)))) :
    Adjacent u (nextV hf hg u) ∧ D S f g (nextV hf hg u).1 (nextV hf hg u).2 = D S f g u.1 u.2 ∧
      stepφ S f u (nextV hf hg u) < 0 := by
  have hstep := descent_step hf hg hmin
  rcases hstep with h | h | h
  · exact absurd (Or.inl h) hnopat
  · exact absurd (Or.inr h) hnopat
  · rw [nextV, dif_pos h]
    exact h.choose_spec

/-- The descent sequence from the global minimum. -/
noncomputable def descSeq (hf : IsTiling S f) (hg : IsTiling S g) (v₀ : Cell) : ℕ → Cell :=
  fun k ↦ (nextV hf hg)^[k] v₀

/-- Every vertex of the descent sequence is `D`-minimal at level `D v₀`, and each
step is a descent step (adjacent, `D`-preserving, `φ f < 0`). -/
lemma descSeq_prop (hf : IsTiling S f) (hg : IsTiling S g) {v₀ : Cell}
    (hv₀ : ∀ w : Cell, D S f g v₀.1 v₀.2 ≤ D S f g w.1 w.2)
    (hnopat : ∀ u : Cell, (∀ w : Cell, D S f g u.1 u.2 ≤ D S f g w.1 w.2) →
      ¬ ((crN S f u.1 u.2 ∧ crN S f u.1 (u.2 - 1) ∧ Even (u.1 + u.2)) ∨
        (crE S f u.1 u.2 ∧ crE S f (u.1 - 1) u.2 ∧ Odd (u.1 + u.2)))) :
    ∀ k : ℕ, (∀ w : Cell, D S f g (descSeq hf hg v₀ k).1 (descSeq hf hg v₀ k).2 ≤
        D S f g w.1 w.2) ∧
      D S f g (descSeq hf hg v₀ k).1 (descSeq hf hg v₀ k).2 = D S f g v₀.1 v₀.2 ∧
      Adjacent (descSeq hf hg v₀ k) (descSeq hf hg v₀ (k + 1)) ∧
      stepφ S f (descSeq hf hg v₀ k) (descSeq hf hg v₀ (k + 1)) < 0 := by
  intro k
  induction k with
  | zero =>
    have h1 := nextV_step hf hg hv₀ (hnopat v₀ hv₀)
    exact ⟨hv₀, rfl, h1.1, h1.2.2⟩
  | succ k ih =>
    obtain ⟨hmin, hD, hadj, hsp⟩ := ih
    have h1 := nextV_step hf hg hmin (hnopat _ hmin)
    have hD1 : D S f g (descSeq hf hg v₀ (k + 1)).1 (descSeq hf hg v₀ (k + 1)).2 =
        D S f g v₀.1 v₀.2 := by
      have hds : descSeq hf hg v₀ (k + 1) = nextV hf hg (descSeq hf hg v₀ k) :=
        Function.iterate_succ_apply' _ _ _
      rw [hds, h1.2.1, hD]
    have hmin1 : ∀ w : Cell, D S f g (descSeq hf hg v₀ (k + 1)).1 (descSeq hf hg v₀ (k + 1)).2 ≤
        D S f g w.1 w.2 := by
      rw [hD1]
      exact hv₀
    have h2 := nextV_step hf hg hmin1 (hnopat _ hmin1)
    have hds2 : descSeq hf hg v₀ (k + 2) = nextV hf hg (descSeq hf hg v₀ (k + 1)) :=
      Function.iterate_succ_apply' _ _ _
    refine ⟨hmin1, hD1, ?_, ?_⟩
    · rw [hds2]
      exact h2.1
    · rw [hds2]
      exact h2.2.2

/-- `φ f` is antisymmetric on a step. -/
lemma stepφ_antisymm (hf : IsTiling S f) {u v : Cell} (hadj : Adjacent u v) :
    stepφ S f v u = - stepφ S f u v := by
  rcases adjacent_cases hadj with h | h | h | h
  · rw [h, stepφ_of_east rfl]
    have e : stepφ S f (u.1 + 1, u.2) u = -φE S f u.1 u.2 := by
      have h3 := stepφ_of_west (S := S) (f := f) (u := (u.1 + 1, u.2)) (v := u) (by simp)
      rw [show ((u.1 + 1, u.2).1 - 1) = u.1 from by simp] at h3
      exact h3
    rw [e]
  · rw [h, stepφ_of_west rfl]
    have e : stepφ S f (u.1 - 1, u.2) u = φE S f (u.1 - 1) u.2 := by
      have h3 := stepφ_of_east (S := S) (f := f) (u := (u.1 - 1, u.2)) (v := u) (by simp)
      exact h3
    rw [e, neg_neg]
  · rw [h, stepφ_of_north rfl]
    have e : stepφ S f (u.1, u.2 + 1) u = -φN S f u.1 u.2 := by
      have h3 := stepφ_of_south (S := S) (f := f) (u := (u.1, u.2 + 1)) (v := u) (by simp)
      rw [show ((u.1, u.2 + 1).2 - 1) = u.2 from by simp] at h3
      exact h3
    rw [e]
  · rw [h, stepφ_of_south rfl]
    have e : stepφ S f (u.1, u.2 - 1) u = φN S f u.1 (u.2 - 1) := by
      have h3 := stepφ_of_north (S := S) (f := f) (u := (u.1, u.2 - 1)) (v := u) (by simp)
      exact h3
    rw [e, neg_neg]

/-- The crux (E): the descent terminates in a distasteful pair. -/
theorem cruxE : CruxE := by
  classical
  intro S f g hf hg hcc ⟨v, hv⟩
  obtain ⟨v₀, hv₀⟩ := D_exists_min hf hg
  have hm0 : D S f g v₀.1 v₀.2 < 0 := lt_of_le_of_lt (hv₀ v) hv
  by_cases hpat : ∀ u : Cell, (∀ w : Cell, D S f g u.1 u.2 ≤ D S f g w.1 w.2) →
      ¬ ((crN S f u.1 u.2 ∧ crN S f u.1 (u.2 - 1) ∧ Even (u.1 + u.2)) ∨
        (crE S f u.1 u.2 ∧ crE S f (u.1 - 1) u.2 ∧ Odd (u.1 + u.2)))
  · exfalso
    set B := Finset.Ico (westBound S) (eastBound S) ×ˢ Finset.Ico (southBound S) (northBound S) with hB
    have hbox : ∀ k : ℕ, descSeq hf hg v₀ k ∈ B := by
      intro k
      have hD := (descSeq_prop hf hg hv₀ hpat k).2.1
      have hne : D S f g (descSeq hf hg v₀ k).1 (descSeq hf hg v₀ k).2 ≠ 0 := by
        rw [hD]; omega
      have hsup := D_finite_support hf hg _ _ hne
      rw [hB]
      simp only [Finset.mem_product, Finset.mem_Ico]
      omega
    have hpg := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := Finset.range (B.card + 1)) (t := B) (f := descSeq hf hg v₀)
      (by rw [Finset.card_range]; omega) (fun i _ ↦ hbox i)
    obtain ⟨i, hi, j, hj, hne, heq⟩ := hpg
    have hex : ∃ j, ∃ i, i < j ∧ descSeq hf hg v₀ i = descSeq hf hg v₀ j := by
      rw [Finset.mem_range] at hi hj
      by_cases hij : i < j
      · exact ⟨j, i, hij, heq⟩
      · exact ⟨i, j, by omega, heq.symm⟩
    let j₀ := Nat.find hex
    have hj₀ : ∃ i, i < j₀ ∧ descSeq hf hg v₀ i = descSeq hf hg v₀ j₀ := Nat.find_spec hex
    obtain ⟨i₀, hi₀, hvi₀⟩ := hj₀
    have hmin : ∀ j < j₀, ∀ i < j, descSeq hf hg v₀ i ≠ descSeq hf hg v₀ j := by
      intro j hj i hi
      have h := Nat.find_min hex hj
      push_neg at h
      exact h i hi
    set n' := j₀ - i₀ with hn'
    set w' : ℕ → Cell := fun k ↦ descSeq hf hg v₀ (i₀ + k) with hw'
    have hn'0 : 0 < n' := by omega
    have hret : w' n' = w' 0 := by
      have h1 : i₀ + (j₀ - i₀) = j₀ := by omega
      rw [hw', hn']
      show descSeq hf hg v₀ (i₀ + (j₀ - i₀)) = descSeq hf hg v₀ (i₀ + 0)
      rw [h1, show i₀ + 0 = i₀ from by omega]
      exact hvi₀.symm
    have hinj : ∀ a < n', ∀ b < n', w' a = w' b → a = b := by
      intro a ha b hb hab
      rw [hw'] at hab
      rcases lt_trichotomy a b with h | h | h
      · exact absurd hab (hmin (i₀ + b) (by omega) (i₀ + a) (by omega))
      · exact h
      · exact absurd hab.symm (hmin (i₀ + a) (by omega) (i₀ + b) (by omega))
    have hadj : ∀ k < n', Adjacent (w' k) (w' (k + 1)) := by
      intro k hk
      rw [hw']
      exact (descSeq_prop hf hg hv₀ hpat (i₀ + k)).2.2.1
    have hlevel : ∀ k < n', D S f g (w' k).1 (w' k).2 < 0 := by
      intro k hk
      rw [hw', (descSeq_prop hf hg hv₀ hpat (i₀ + k)).2.1]
      exact hm0
    have hstep : ∀ k < n', stepφ S f (w' k) (w' (k + 1)) < 0 := by
      intro k hk
      rw [hw']
      exact (descSeq_prop hf hg hv₀ hpat (i₀ + k)).2.2.2
    have hn'1 : n' ≠ 1 := by
      intro h
      have hj : j₀ = i₀ + 1 := by omega
      rw [hj] at hvi₀
      have hadj0 := (descSeq_prop hf hg hv₀ hpat i₀).2.2.1
      rw [← hvi₀] at hadj0
      simp [Adjacent] at hadj0
    have hn'2 : n' ≠ 2 := by
      intro h
      have hj : j₀ = i₀ + 2 := by omega
      rw [hj] at hvi₀
      have hsp0 := (descSeq_prop hf hg hv₀ hpat i₀).2.2.2
      have hsp1 := (descSeq_prop hf hg hv₀ hpat (i₀ + 1)).2.2.2
      rw [← hvi₀] at hsp1
      have hadj0 := (descSeq_prop hf hg hv₀ hpat i₀).2.2.1
      have hanti := stepφ_antisymm hf hadj0
      omega
    have hpar : Even n' := by
      have hstep2 : ∀ k < n', ((w' (k + 1)).1 + (w' (k + 1)).2) = ((w' k).1 + (w' k).2) + 1 ∨
          ((w' (k + 1)).1 + (w' (k + 1)).2) = ((w' k).1 + (w' k).2) - 1 := by
        intro k hk
        have hadj_k := hadj k hk
        rcases adjacent_cases hadj_k with h | h | h | h <;> rw [h] <;> simp <;> omega
      have key : ∀ k : ℕ, k ≤ n' → Even (((w' k).1 + (w' k).2) + ((w' 0).1 + (w' 0).2) + k) := by
        intro k hk
        induction k with
        | zero =>
          refine ⟨(w' 0).1 + (w' 0).2, by push_cast; ring⟩
        | succ k ih =>
          have hk' : k ≤ n' := by omega
          obtain ⟨m, hm⟩ := ih hk'
          rcases hstep2 k (by omega) with h | h
          · refine ⟨m + 1, by omega⟩
          · refine ⟨m, by omega⟩
      have h0 := key n' (le_refl _)
      rw [hret] at h0
      obtain ⟨m, hm⟩ := h0
      have hE : Even (n' : ℤ) := ⟨m - ((w' 0).1 + (w' 0).2), by omega⟩
      obtain ⟨m', hm'⟩ := hE
      exact ⟨m'.toNat, by omega⟩
    have hn'4 : 4 ≤ n' := by
      obtain ⟨m, hm⟩ := hpar
      omega
    have hinside : ∀ c : Cell, insideV w' n' c → c ∈ S :=
      fun c hc ↦ insideV_subset_S hf hg hcc hn'4 hadj hinj hret hlevel (c := c) hc
    have hgreen := cycSum_eq_zero hf hn'4 hadj hinj hret hinside
    have hneg : ∑ k ∈ Finset.range n', stepφ S f (w' k) (w' (k + 1)) < 0 := by
      apply Finset.sum_neg'
      · intro k hk
        exact le_of_lt (hstep k (Finset.mem_range.mp hk))
      · exact ⟨0, Finset.mem_range.mpr (by omega), hstep 0 (by omega)⟩
    omega
  · push_neg at hpat
    obtain ⟨u, humin, hpat'⟩ := hpat
    rcases hpat' with h | h
    · exact ⟨u.1, u.2, Or.inl h⟩
    · exact ⟨u.1, u.2, Or.inr h⟩

/-- USAMO 2009 Problem 3(b): the tasteful tiling of a hole-free region
(a `ComplConnected` region of cells) is unique. -/
theorem usa2009_p3_b (hcc : ComplConnected S) (hf : IsTiling S f) (hg : IsTiling S g)
    (htf : Tasteful S f) (htg : Tasteful S g) : ∀ c ∈ S, f c = g c :=
  unique_tasteful_of_cruxE cruxE hcc hf hg htf htg

end Descent

end AltP3b

snip end


/-- USAMO 2009 Problem 3, part (a): every region that can be tiled by
dominoes can be tiled tastefully. -/
problem usa2009_p3a (S : Finset Cell) (h : ∃ f, IsTiling S f) :
    ∃ f, IsTiling S f ∧ Tasteful S f :=
  exists_tasteful_tiling S h

/-- USAMO 2009 Problem 3, part (b): the tasteful tiling of a chessboard
polygon (a region that is connected and hole-free) is unique.  Proved by
the global height-difference invariant (Route Y, `AltP3b.usa2009_p3_b`);
the definitions `IsTiling`/`Tasteful`/`ComplConnected` of the two
namespaces are delta-equal, so the bridge is by defeq. -/
problem usa2009_p3b (S : Finset Cell) (_ : Connected S) (hcc : ComplConnected S)
    (f g : Cell → Cell) (hf : IsTiling S f) (hg : IsTiling S g)
    (htf : Tasteful S f) (htg : Tasteful S g) :
    ∀ c ∈ S, f c = g c :=
  Usa2009P3.AltP3b.usa2009_p3_b hcc hf hg htf htg

end Usa2009P3
