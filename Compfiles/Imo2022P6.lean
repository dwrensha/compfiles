/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Kimi K3
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Data.Nat.Dist
public import Mathlib.Data.PNat.Basic
public import Mathlib.Order.Lattice.Nat
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Combinatorics]
  problemImportedFrom :=
    "https://github.com/jsm28/IMOLean/blob/main/IMO/IMO2022P6.lean"
}

/-!
# International Mathematical Olympiad 2022, Problem 6

Let n be a positive integer. A Nordic square is an n×n board containing
all the integers from 1 to n² so that each cell contains exactly one
number. Two different cells are considered adjacent if they share a
common side. Every cell that is adjacent only to cells containing larger
numbers is called a valley. An uphill path is a sequence of one or more
cells such that:

  (1) the first cell in the sequence is a valley,
  (2) each subsequent cell in the sequence is adjacent to the
      previous cell, and
  (3) the numbers written in the cells in the sequence are in
      increasing order.

Find, as a function of n, the smallest possible total number of uphill
paths in a Nordic square.
-/

open scoped Cardinal

namespace Imo2022P6

/-- A cell of the board. -/
abbrev Cell (n : ℕ) : Type := Fin n × Fin n

/-- A Nordic square. -/
abbrev NordicSquare (n : ℕ) : Type := Cell n ≃ Finset.Icc 1 (n ^ 2)

/-- Whether two cells are adjacent. -/
def Adjacent {n : ℕ} (x y : Cell n) : Prop :=
  Nat.dist x.1 y.1 + Nat.dist x.2 y.2 = 1

/-- The definition of a valley from the problem. -/
def NordicSquare.Valley {n : ℕ} (ns : NordicSquare n) (c : Cell n) : Prop :=
  ∀ c' : Cell n, Adjacent c c' → (ns c : ℕ) < (ns c' : ℕ)

/-- The definition of an uphill path from the problem. -/
structure NordicSquare.UphillPath {n : ℕ} (ns : NordicSquare n) where
  /-- The cells on the path. -/
  cells : List (Cell n)
  nonempty : cells ≠ []
  first_valley : ns.Valley (cells.head nonempty)
  adjacent : cells.IsChain Adjacent
  increasing : cells.IsChain fun x y ↦ (ns x : ℕ) < (ns y : ℕ)

snip begin

/-- Adjacency is symmetric. -/
theorem Adjacent.symm {n : ℕ} {x y : Cell n} (h : Adjacent x y) : Adjacent y x := by
  unfold Adjacent at *
  rw [Nat.dist_comm y.1 x.1, Nat.dist_comm y.2 x.2]
  exact h

/-- Adjacency is decidable. -/
instance {n : ℕ} (x y : Cell n) : Decidable (Adjacent x y) :=
  inferInstanceAs (Decidable (Nat.dist x.1 y.1 + Nat.dist x.2 y.2 = 1))

/-- Adjacent cells are distinct. -/
theorem Adjacent.ne {n : ℕ} {x y : Cell n} (h : Adjacent x y) : x ≠ y := by
  rintro rfl
  simp [Adjacent, Nat.dist_self] at h

/-- Adjacent cells have different values. -/
theorem NordicSquare.value_ne_of_adjacent {n : ℕ} (ns : NordicSquare n) {x y : Cell n}
    (h : Adjacent x y) : (ns x : ℕ) ≠ (ns y : ℕ) := by
  intro heq
  apply h.ne
  apply ns.injective
  apply Subtype.ext
  exact heq

/-- In a Nordic square, any non-valley cell has an adjacent cell with a smaller value. -/
theorem NordicSquare.exists_smaller_neighbor {n : ℕ} (ns : NordicSquare n) {c : Cell n}
    (h : ¬ ns.Valley c) : ∃ c' : Cell n, Adjacent c c' ∧ (ns c' : ℕ) < (ns c : ℕ) := by
  simp only [NordicSquare.Valley, not_forall, not_lt] at h
  obtain ⟨c', hadj, hle⟩ := h
  exact ⟨c', hadj, lt_of_le_of_ne hle (Ne.symm (ns.value_ne_of_adjacent hadj))⟩

/-- A cell with no smaller-valued adjacent cell is a valley. -/
theorem NordicSquare.valley_of_no_smaller_neighbor {n : ℕ} (ns : NordicSquare n) {c : Cell n}
    (h : ¬ ∃ c' : Cell n, Adjacent c c' ∧ (ns c' : ℕ) < (ns c : ℕ)) : ns.Valley c := by
  intro c' hadj
  by_contra hlt
  apply h
  exact ⟨c', hadj, lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm (ns.value_ne_of_adjacent hadj))⟩

/-- The path from a valley to a given cell, following decreasing values.
This is defined by well-founded recursion on the value of the cell. -/
noncomputable def NordicSquare.pathTo {n : ℕ} (ns : NordicSquare n) (c : Cell n) : List (Cell n) :=
  if h : ∃ c' : Cell n, Adjacent c c' ∧ (ns c' : ℕ) < (ns c : ℕ) then
    let c' := Classical.choose h
    pathTo ns c' ++ [c]
  else [c]
termination_by (ns c : ℕ)
decreasing_by
  simp_wf
  exact (Classical.choose_spec h).2

theorem NordicSquare.pathTo_ne_nil {n : ℕ} (ns : NordicSquare n) (c : Cell n) :
    pathTo ns c ≠ [] := by
  rw [pathTo]
  split <;> simp

/-- The defining property of `pathTo`: it is an uphill path ending at `c`. -/
theorem NordicSquare.pathTo_props {n : ℕ} (ns : NordicSquare n) (c : Cell n) :
    (∀ v, (pathTo ns c).head? = some v → ns.Valley v) ∧
    (pathTo ns c).IsChain Adjacent ∧
    (pathTo ns c).IsChain (fun x y ↦ (ns x : ℕ) < (ns y : ℕ)) ∧
    (pathTo ns c).getLast? = some c := by
  induction c using NordicSquare.pathTo.induct (ns := ns) with
  | case1 c h c' ih =>
    have hc'spec := Classical.choose_spec h
    obtain ⟨ih1, ih2, ih3, ih4⟩ := ih
    rw [pathTo.eq_1, dite_eq_left h]
    dsimp only
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro v hv
      have hs : (ns.pathTo c').head? = some ((ns.pathTo c').head (pathTo_ne_nil ns c')) :=
        List.head?_eq_some_head _
      rw [List.head?_append, hs, Option.some_or, Option.some.injEq] at hv
      rw [← hv]
      exact ih1 _ hs
    · apply List.IsChain.append ih2 (List.isChain_singleton _)
      intro x hx y hy
      rw [ih4, Option.mem_some] at hx
      rw [List.head?_singleton, Option.mem_some] at hy
      subst hx
      subst hy
      exact hc'spec.1.symm
    · apply List.IsChain.append ih3 (List.isChain_singleton _)
      intro x hx y hy
      rw [ih4, Option.mem_some] at hx
      rw [List.head?_singleton, Option.mem_some] at hy
      subst hx
      subst hy
      exact hc'spec.2
    · rw [List.getLast?_append]
      simp
  | case2 c h =>
    rw [pathTo.eq_1, dite_eq_right h]
    refine ⟨?_, List.isChain_singleton _, List.isChain_singleton _, ?_⟩
    · intro v hv
      rw [List.head?_singleton, Option.some.injEq] at hv
      rw [← hv]
      exact ns.valley_of_no_smaller_neighbor h
    · rfl

/-- `pathTo` packaged as an uphill path. -/
noncomputable def NordicSquare.uphillPathTo {n : ℕ} (ns : NordicSquare n) (c : Cell n) :
    ns.UphillPath where
  cells := pathTo ns c
  nonempty := pathTo_ne_nil ns c
  first_valley := (pathTo_props ns c).1 _ (List.head?_eq_some_head _)
  adjacent := (pathTo_props ns c).2.1
  increasing := (pathTo_props ns c).2.2.1

theorem NordicSquare.uphillPathTo_getLast? {n : ℕ} (ns : NordicSquare n) (c : Cell n) :
    (uphillPathTo ns c).cells.getLast? = some c :=
  (pathTo_props ns c).2.2.2

/-- The cell with value 1. -/
noncomputable def NordicSquare.minCell {n : ℕ} (ns : NordicSquare (n + 1)) : Cell (n + 1) :=
  ns.symm ⟨1, by simp [Finset.mem_Icc, Nat.one_le_pow]⟩

theorem NordicSquare.minCell_value {n : ℕ} (ns : NordicSquare (n + 1)) :
    (ns (minCell ns) : ℕ) = 1 := by
  rw [minCell, Equiv.apply_symm_apply]

theorem NordicSquare.minCell_valley {n : ℕ} (ns : NordicSquare (n + 1)) :
    ns.Valley (minCell ns) := by
  intro c' hadj
  rw [minCell_value]
  have h1 : (1 : ℕ) ≤ (ns c' : ℕ) := (Finset.mem_Icc.1 (ns c').2).1
  have hne : (ns c' : ℕ) ≠ 1 := by
    intro heq
    apply hadj.ne
    apply ns.injective
    apply Subtype.ext
    rw [heq, minCell_value]
  omega

/-- The trivial uphill path consisting of just the minimum cell. -/
noncomputable def NordicSquare.trivialPath {n : ℕ} (ns : NordicSquare (n + 1)) : ns.UphillPath where
  cells := [minCell ns]
  nonempty := by simp
  first_valley := by simp [minCell_valley]
  adjacent := List.isChain_singleton _
  increasing := List.isChain_singleton _

/-- Given adjacent cells a, b, the uphill path ending with the edge {a,b}
(obtained by extending the path to the smaller-valued cell by the larger one). -/
noncomputable def NordicSquare.gapPath {n : ℕ} (ns : NordicSquare n) (a b : Cell n)
    (hab : Adjacent a b) : ns.UphillPath :=
  if h : (ns a : ℕ) < (ns b : ℕ) then
    { cells := pathTo ns a ++ [b]
      nonempty := by simp [pathTo_ne_nil]
      first_valley := by
        rw [List.head_append_of_ne_nil (pathTo_ne_nil ns a)]
        exact (pathTo_props ns a).1 _ (List.head?_eq_some_head _)
      adjacent := by
        apply List.IsChain.append (pathTo_props ns a).2.1 (List.isChain_singleton _)
        intro x hx y hy
        rw [(pathTo_props ns a).2.2.2, Option.mem_some] at hx
        rw [List.head?_singleton, Option.mem_some] at hy
        rw [← hx, ← hy]
        exact hab
      increasing := by
        apply List.IsChain.append (pathTo_props ns a).2.2.1 (List.isChain_singleton _)
        intro x hx y hy
        rw [(pathTo_props ns a).2.2.2, Option.mem_some] at hx
        rw [List.head?_singleton, Option.mem_some] at hy
        rw [← hx, ← hy]
        exact h }
  else
    { cells := pathTo ns b ++ [a]
      nonempty := by simp [pathTo_ne_nil]
      first_valley := by
        rw [List.head_append_of_ne_nil (pathTo_ne_nil ns b)]
        exact (pathTo_props ns b).1 _ (List.head?_eq_some_head _)
      adjacent := by
        apply List.IsChain.append (pathTo_props ns b).2.1 (List.isChain_singleton _)
        intro x hx y hy
        rw [(pathTo_props ns b).2.2.2, Option.mem_some] at hx
        rw [List.head?_singleton, Option.mem_some] at hy
        rw [← hx, ← hy]
        exact hab.symm
      increasing := by
        apply List.IsChain.append (pathTo_props ns b).2.2.1 (List.isChain_singleton _)
        intro x hx y hy
        rw [(pathTo_props ns b).2.2.2, Option.mem_some] at hx
        rw [List.head?_singleton, Option.mem_some] at hy
        rw [← hx, ← hy]
        exact lt_of_le_of_ne (not_lt.1 h) (Ne.symm (ns.value_ne_of_adjacent hab)) }

theorem NordicSquare.gapPath_cells {n : ℕ} (ns : NordicSquare n) (a b : Cell n)
    (hab : Adjacent a b) :
    (gapPath ns a b hab).cells =
      if (ns a : ℕ) < (ns b : ℕ) then pathTo ns a ++ [b] else pathTo ns b ++ [a] := by
  unfold gapPath
  split <;> rfl

theorem NordicSquare.gapPath_length {n : ℕ} (ns : NordicSquare n) (a b : Cell n)
    (hab : Adjacent a b) : 2 ≤ (gapPath ns a b hab).cells.length := by
  rw [gapPath_cells]
  split
  · rw [List.length_append, List.length_singleton]
    have := List.length_pos_iff_ne_nil.2 (pathTo_ne_nil ns a)
    omega
  · rw [List.length_append, List.length_singleton]
    have := List.length_pos_iff_ne_nil.2 (pathTo_ne_nil ns b)
    omega

/-- The last two cells of an uphill path, as a pair (second-to-last, last),
with junk value for the second-to-last cell if the path has length 1. -/
noncomputable def UphillPath.lastTwo {n : ℕ} {ns : NordicSquare (n + 1)} (p : ns.UphillPath) :
    Cell (n + 1) × Cell (n + 1) :=
  (p.cells.getD (p.cells.length - 2) (⟨⟨0, by omega⟩, ⟨0, by omega⟩⟩ : Cell (n + 1)),
   p.cells.getLast p.nonempty)

/-- The last two cells of `gapPath a b` are the two cells, smaller-valued first. -/
theorem NordicSquare.gapPath_lastTwo {n : ℕ} (ns : NordicSquare (n + 1)) (a b : Cell (n + 1))
    (hab : Adjacent a b) :
    UphillPath.lastTwo (gapPath ns a b hab) =
      if (ns a : ℕ) < (ns b : ℕ) then (a, b) else (b, a) := by
  unfold UphillPath.lastTwo
  simp only [NordicSquare.gapPath_cells]
  split
  · apply Prod.ext
    · simp only
      have hpos : 0 < (pathTo ns a).length := List.length_pos_iff_ne_nil.2 (pathTo_ne_nil ns a)
      rw [List.getD_eq_getElem?_getD]
      rw [List.length_append, List.length_singleton]
      rw [List.getElem?_eq_getElem (by rw [List.length_append, List.length_singleton]; omega)]
      rw [Option.getD_some]
      rw [List.getElem_append_left (by omega : (pathTo ns a).length + 1 - 2 < (pathTo ns a).length)]
      have hgl : (pathTo ns a).getLast (pathTo_ne_nil ns a) = a := by
        have h := (pathTo_props ns a).2.2.2
        rw [List.getLast?_eq_some_getLast (pathTo_ne_nil ns a)] at h
        exact Option.some.inj h
      rw [List.getLast_eq_getElem] at hgl
      have hid : (pathTo ns a).length + 1 - 2 = (pathTo ns a).length - 1 := by omega
      simpa only [hid] using hgl
    · simp only
      exact List.getLast_append_singleton _
  · apply Prod.ext
    · simp only
      have hpos : 0 < (pathTo ns b).length := List.length_pos_iff_ne_nil.2 (pathTo_ne_nil ns b)
      rw [List.getD_eq_getElem?_getD]
      rw [List.length_append, List.length_singleton]
      rw [List.getElem?_eq_getElem (by rw [List.length_append, List.length_singleton]; omega)]
      rw [Option.getD_some]
      rw [List.getElem_append_left (by omega : (pathTo ns b).length + 1 - 2 < (pathTo ns b).length)]
      have hgl : (pathTo ns b).getLast (pathTo_ne_nil ns b) = b := by
        have h := (pathTo_props ns b).2.2.2
        rw [List.getLast?_eq_some_getLast (pathTo_ne_nil ns b)] at h
        exact Option.some.inj h
      rw [List.getLast_eq_getElem] at hgl
      have hid : (pathTo ns b).length + 1 - 2 = (pathTo ns b).length - 1 := by omega
      simpa only [hid] using hgl
    · simp only
      exact List.getLast_append_singleton _

/-- A direction for a gap between two adjacent cells. -/
inductive GapDir : Type
  | horiz : GapDir
  | vert : GapDir

/-- The ordered pair of cells of a gap: for `horiz`, `(i, j), (i, j+1)`;
for `vert`, `(j, i), (j+1, i)`. -/
def gapPair {n : ℕ} (d : GapDir) (g : Fin (n + 1) × Fin n) : Cell (n + 1) × Cell (n + 1) :=
  match d with
  | .horiz => ((g.1, ⟨g.2.1, by omega⟩), (g.1, ⟨g.2.1 + 1, by omega⟩))
  | .vert => ((⟨g.2.1, by omega⟩, g.1), (⟨g.2.1 + 1, by omega⟩, g.1))

theorem gapPair_adjacent {n : ℕ} (d : GapDir) (g : Fin (n + 1) × Fin n) :
    Adjacent (gapPair d g).1 (gapPair d g).2 := by
  cases d <;> simp [gapPair, Adjacent, Nat.dist]

/-- The unordered pair of cells of a gap determines the gap. -/
theorem gapPair_injective {n : ℕ} (d₁ d₂ : GapDir) (g₁ g₂ : Fin (n + 1) × Fin n)
    (h : gapPair d₁ g₁ = gapPair d₂ g₂ ∨ gapPair d₁ g₁ = (gapPair d₂ g₂).swap) :
    d₁ = d₂ ∧ g₁ = g₂ := by
  cases d₁ <;> cases d₂ <;>
    simp only [gapPair, Prod.mk.injEq, Prod.swap_prod_mk, Fin.ext_iff] at h
  · refine ⟨rfl, Prod.ext (Fin.ext ?_) (Fin.ext ?_)⟩ <;> rcases h with h | h <;> omega
  · exfalso; rcases h with h | h <;> omega
  · exfalso; rcases h with h | h <;> omega
  · refine ⟨rfl, Prod.ext (Fin.ext ?_) (Fin.ext ?_)⟩ <;> rcases h with h | h <;> omega

/-- The injection from gaps (plus a point for the trivial path) to uphill paths. -/
noncomputable def gapPathInj {n : ℕ} (ns : NordicSquare (n + 1)) :
    (GapDir × (Fin (n + 1) × Fin n)) ⊕ Unit → ns.UphillPath
  | .inl (d, g) => NordicSquare.gapPath ns (gapPair d g).1 (gapPair d g).2 (gapPair_adjacent _ _)
  | .inr () => NordicSquare.trivialPath ns

theorem gapPathInj_injective {n : ℕ} (ns : NordicSquare (n + 1)) :
    Function.Injective (gapPathInj ns) := by
  intro x y h
  cases x with
  | inl xd =>
    obtain ⟨dx, gx⟩ := xd
    cases y with
    | inl yd =>
      obtain ⟨dy, gy⟩ := yd
      have hlt := congrArg UphillPath.lastTwo h
      simp only [gapPathInj, NordicSquare.gapPath_lastTwo] at hlt
      split at hlt <;> split at hlt
      · obtain ⟨h1, h2⟩ := Prod.ext_iff.1 hlt
        obtain ⟨rfl, rfl⟩ := gapPair_injective dx dy gx gy (Or.inl (Prod.ext h1 h2))
        rfl
      · obtain ⟨h1, h2⟩ := Prod.ext_iff.1 hlt
        obtain ⟨rfl, rfl⟩ := gapPair_injective dx dy gx gy (Or.inr (Prod.ext h1 h2))
        rfl
      · obtain ⟨h1, h2⟩ := Prod.ext_iff.1 hlt
        obtain ⟨rfl, rfl⟩ := gapPair_injective dx dy gx gy (Or.inr (Prod.ext h2 h1))
        rfl
      · obtain ⟨h1, h2⟩ := Prod.ext_iff.1 hlt
        obtain ⟨rfl, rfl⟩ := gapPair_injective dx dy gx gy (Or.inl (Prod.ext h2 h1))
        rfl
    | inr u =>
      exfalso
      have hx := congrArg (fun p ↦ p.cells.length) h
      simp only [gapPathInj, NordicSquare.trivialPath, List.length_singleton] at hx
      have := NordicSquare.gapPath_length ns (gapPair dx gx).1 (gapPair dx gx).2 (gapPair_adjacent dx gx)
      omega
  | inr u =>
    cases y with
    | inl yd =>
      obtain ⟨dy, gy⟩ := yd
      exfalso
      have hx := congrArg (fun p ↦ p.cells.length) h
      simp only [gapPathInj, NordicSquare.trivialPath, List.length_singleton] at hx
      have := NordicSquare.gapPath_length ns (gapPair dy gy).1 (gapPair dy gy).2 (gapPair_adjacent dy gy)
      omega
    | inr v => rfl

/-- `GapDir` is equivalent to `Fin 2`. -/
def gapDirEquivFin2 : GapDir ≃ Fin 2 where
  toFun := fun | .horiz => ⟨0, by omega⟩ | .vert => ⟨1, by omega⟩
  invFun := fun i => if i = 0 then .horiz else .vert
  left_inv := fun d => by cases d <;> simp
  right_inv := fun i => by fin_cases i <;> simp

/-- `GapDir` is a finite type. -/
instance : Fintype GapDir := Fintype.ofEquiv (Fin 2) gapDirEquivFin2.symm

/-- The number of gaps (plus one for the trivial path) as a cardinal. -/
theorem mk_gaps (n : ℕ) :
    (#(GapDir × (Fin (n + 1) × Fin n) ⊕ Unit) : Cardinal) =
      ((2 * ((n + 1) * n) + 1 : ℕ) : Cardinal) := by
  rw [Cardinal.mk_sum, Cardinal.mk_unit, Cardinal.mk_prod, Cardinal.mk_prod,
    Cardinal.mk_fin, Cardinal.mk_fin]
  have hgd : (#GapDir : Cardinal) = ((2 : ℕ) : Cardinal) := by
    rw [Cardinal.mk_eq_nat_iff]
    exact ⟨gapDirEquivFin2⟩
  rw [hgd]
  simp only [Cardinal.lift_id]
  norm_cast

/-- The answer expressed as `2 * ((n+1) * n) + 1`. -/
theorem answer_eq (n : ℕ) : 2 * (n + 1) ^ 2 - 2 * (n + 1) + 1 = 2 * ((n + 1) * n) + 1 := by
  have hsq : (n + 1) ^ 2 = (n + 1) * n + (n + 1) := by ring
  omega

/-- **Lower bound**: every Nordic square on an `(n+1) × (n+1)` board has at least
`2 * ((n+1) * n) + 1` uphill paths. -/
theorem lower_bound {n : ℕ} (ns : NordicSquare (n + 1)) :
    ((2 * ((n + 1) * n) + 1 : ℕ) : Cardinal) ≤ #ns.UphillPath := by
  have h1 : #(GapDir × (Fin (n + 1) × Fin n) ⊕ Unit) ≤ #ns.UphillPath :=
    Cardinal.mk_le_of_injective (gapPathInj_injective ns)
  rwa [mk_gaps n] at h1

/-- **Lower bound** (general form): every Nordic square on an `m × m` board has at least
`2 * (m * (m - 1)) + 1` uphill paths. -/
theorem lower_bound' {m : ℕ} (hm : 1 ≤ m) (ns : NordicSquare m) :
    ((2 * ((m - 1) + 1) * (m - 1) + 1 : ℕ) : Cardinal) ≤ #ns.UphillPath := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, (Nat.sub_add_cancel hm).symm⟩
  simpa [Nat.add_sub_cancel, Nat.mul_assoc] using lower_bound ns

/-- Two uphill paths with the same cells are equal. -/
theorem NordicSquare.UphillPath.ext {n : ℕ} {ns : NordicSquare n} {p q : ns.UphillPath}
    (h : p.cells = q.cells) : p = q := by
  cases p; cases q; congr

/-- An increasing chain of cells has no duplicates. -/
theorem NordicSquare.isChain_nodup {n : ℕ} (ns : NordicSquare n) (l : List (Cell n))
    (h : l.IsChain fun x y ↦ (ns x : ℕ) < (ns y : ℕ)) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a l ih =>
    rw [List.isChain_cons] at h
    obtain ⟨h1, h2⟩ := h
    rw [List.nodup_cons]
    refine ⟨?_, ih h2⟩
    intro ha
    have hr := List.IsChain.rel_cons (List.isChain_cons.2 ⟨h1, h2⟩) ha
    simp at hr

/-- The list of cells of an uphill path has length at most the number of cells. -/
theorem NordicSquare.uphillPath_length_le {n : ℕ} (ns : NordicSquare n) (p : ns.UphillPath) :
    p.cells.length ≤ n ^ 2 := by
  have hnd := ns.isChain_nodup p.cells p.increasing
  have h1 := hnd.length_le_card
  rw [Fintype.card_prod, Fintype.card_fin, ← pow_two] at h1
  exact h1

/-- Bounded-length lists over a finite type form a finite type. -/
instance finiteBoundedList (α : Type*) [Finite α] (k : ℕ) :
    Finite {l : List α // l.length ≤ k} :=
  Finite.of_injective (β := Fin k → Option α)
    (fun l ↦ fun i ↦ l.1[i]?)
    (by
      intro a b h
      apply Subtype.ext
      apply List.ext_getElem?
      intro n
      by_cases hn : n < k
      · exact congrFun h ⟨n, hn⟩
      · rw [List.getElem?_eq_none_iff.2, List.getElem?_eq_none_iff.2]
        · exact le_trans b.2 (by omega)
        · exact le_trans a.2 (by omega))

/-- There are finitely many uphill paths. -/
instance (n : ℕ) (ns : NordicSquare n) : Finite ns.UphillPath :=
  Finite.of_injective (β := {l : List (Cell n) // l.length ≤ n ^ 2})
    (fun p ↦ ⟨p.cells, ns.uphillPath_length_le p⟩)
    (by
      intro a b h
      simp only [Subtype.mk.injEq] at h
      exact NordicSquare.UphillPath.ext h)

noncomputable instance (n : ℕ) (ns : NordicSquare n) : Fintype ns.UphillPath := Fintype.ofFinite _

/-- The cardinal of the type of uphill paths as a natural. -/
theorem mk_uphillPath (n : ℕ) (ns : NordicSquare n) :
    #ns.UphillPath = (Nat.card ns.UphillPath : Cardinal) := by
  rw [← Fintype.card_eq_nat_card]
  exact Cardinal.mk_eq_nat_iff.2 ⟨Fintype.equivFin ns.UphillPath⟩

/-- The dropLast of an uphill path of length at least 2 is an uphill path. -/
def NordicSquare.UphillPath.dropLast {n : ℕ} {ns : NordicSquare n} (p : ns.UphillPath)
    (h : 2 ≤ p.cells.length) : ns.UphillPath where
  cells := p.cells.dropLast
  nonempty := by
    rw [List.ne_nil_iff_length_pos, List.length_dropLast]
    omega
  first_valley := by
    rw [List.head_dropLast]
    exact p.first_valley
  adjacent := p.adjacent.dropLast
  increasing := p.increasing.dropLast

/-- The last cell of the `dropLast` of a path of length ≥ 2 is its second-to-last cell. -/
theorem NordicSquare.UphillPath.dropLast_getLast {n : ℕ} {ns : NordicSquare n}
    (p : ns.UphillPath) (h : 2 ≤ p.cells.length) :
    (p.dropLast h).cells.getLast (p.dropLast h).nonempty =
      p.cells[p.cells.length - 2]'(by omega) := by
  exact List.getLast_dropLast _

/-- The penultimate and last cells of a path of length ≥ 2 are adjacent,
with the value of the penultimate one smaller. -/
theorem NordicSquare.UphillPath.penultimate_props {n : ℕ} {ns : NordicSquare n}
    (p : ns.UphillPath) (h : 2 ≤ p.cells.length) :
    Adjacent ((p.dropLast h).cells.getLast (p.dropLast h).nonempty) (p.cells.getLast p.nonempty) ∧
      (ns ((p.dropLast h).cells.getLast (p.dropLast h).nonempty) : ℕ) <
        (ns (p.cells.getLast p.nonempty) : ℕ) := by
  have hne : p.cells.dropLast ≠ [] := by
    rw [List.ne_nil_iff_length_pos, List.length_dropLast]
    omega
  exact ⟨p.adjacent.rel_getLast_dropLast hne, p.increasing.rel_getLast_dropLast hne⟩

/-- A "hill" in a Nordic square: a cell adjacent only to cells with smaller values. -/
def NordicSquare.Hill {n : ℕ} (ns : NordicSquare n) (c : Cell n) : Prop :=
  ∀ c' : Cell n, Adjacent c c' → (ns c' : ℕ) < (ns c : ℕ)

/-- Valley and Hill are decidable. -/
instance {n : ℕ} (ns : NordicSquare n) (c : Cell n) : Decidable (ns.Valley c) :=
  inferInstanceAs (Decidable (∀ c' : Cell n, Adjacent c c' → (ns c : ℕ) < (ns c' : ℕ)))

/-- Hills are decidable. -/
instance {n : ℕ} (ns : NordicSquare n) (c : Cell n) : Decidable (ns.Hill c) :=
  inferInstanceAs (Decidable (∀ c' : Cell n, Adjacent c c' → (ns c' : ℕ) < (ns c : ℕ)))

/-- A valley has no smaller-valued neighbor. -/
theorem NordicSquare.no_smaller_of_valley {n : ℕ} (ns : NordicSquare n) {c : Cell n}
    (h : ns.Valley c) : ¬ ∃ c', Adjacent c c' ∧ (ns c' : ℕ) < (ns c : ℕ) := by
  rintro ⟨c', hadj, hlt⟩
  have := h c' hadj
  omega

/-- A valley is not a hill when it has a neighbor. -/
theorem NordicSquare.not_hill_of_exists_larger {n : ℕ} (ns : NordicSquare n) {c : Cell n}
    (h : ∃ c', Adjacent c c' ∧ (ns c : ℕ) < (ns c' : ℕ)) : ¬ ns.Hill c := by
  obtain ⟨c', hadj, hlt⟩ := h
  intro hh
  have := hh c' hadj
  omega

/-- A cell with a smaller-valued neighbor is not a valley. -/
theorem NordicSquare.not_valley_of_exists_smaller {n : ℕ} (ns : NordicSquare n) {c : Cell n}
    (h : ∃ c', Adjacent c c' ∧ (ns c' : ℕ) < (ns c : ℕ)) : ¬ ns.Valley c := by
  obtain ⟨c', hadj, hlt⟩ := h
  intro hv
  have := hv c' hadj
  omega

/-- The properties of a Nordic square implying the minimal number of uphill paths. -/
structure NordicSquare.Good {n : ℕ} (ns : NordicSquare n) : Prop where
  /-- there is exactly one valley -/
  valley_unique : ∃! c : Cell n, ns.Valley c
  /-- every non-valley non-hill cell has exactly one smaller-valued neighbor -/
  one_smaller : ∀ c : Cell n, ¬ ns.Valley c → ¬ ns.Hill c →
    ∃! c' : Cell n, Adjacent c c' ∧ (ns c' : ℕ) < (ns c : ℕ)
  /-- hills are pairwise non-adjacent -/
  hills_independent : ∀ h₁ h₂ : Cell n, ns.Hill h₁ → ns.Hill h₂ → h₁ ≠ h₂ → ¬ Adjacent h₁ h₂

/-- In a good square, any uphill path ending at a non-hill cell `c` equals `pathTo ns c`. -/
theorem NordicSquare.cells_eq_pathTo_of_good {n : ℕ} (ns : NordicSquare n) (hg : ns.Good)
    (c : Cell n) (hc : ¬ ns.Hill c) (p : ns.UphillPath)
    (hlast : p.cells.getLast p.nonempty = c) : p.cells = pathTo ns c := by
  have P : ∀ k : ℕ, ∀ c : Cell n, (ns c : ℕ) = k → ¬ ns.Hill c →
      ∀ p : ns.UphillPath, p.cells.getLast p.nonempty = c → p.cells = pathTo ns c := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro c hk hc p hlast
      by_cases hlen : p.cells.length = 1
      · -- path of length 1: cells = [c], and c is a valley
        obtain ⟨a, ha⟩ := List.length_eq_one_iff.1 hlen
        have hac : a = c := by
          simp only [ha, List.getLast_singleton] at hlast
          exact hlast
        rw [hac] at ha
        have hval : ns.Valley c := by
          have hfv := p.first_valley
          simp only [ha, List.head_singleton] at hfv
          exact hfv
        have : pathTo ns c = [c] := by
          rw [NordicSquare.pathTo.eq_1]
          rw [dite_eq_right (ns.no_smaller_of_valley hval)]
        rw [ha, this]
      · -- path of length ≥ 2
        have h2 : 2 ≤ p.cells.length := by
          have := p.nonempty
          rw [List.ne_nil_iff_length_pos] at this
          omega
        obtain ⟨hadj, hlt⟩ := p.penultimate_props h2
        rw [hlast] at hadj hlt
        generalize hcp : (p.dropLast h2).cells.getLast (p.dropLast h2).nonempty = c' at hadj hlt
        -- c' is a smaller neighbor of c; c is not a valley
        have hnv : ¬ ns.Valley c := ns.not_valley_of_exists_smaller ⟨c', hadj.symm, hlt⟩
        -- the unique smaller neighbor
        have huniq := hg.one_smaller c hnv hc
        -- c' is not a hill (c is a larger neighbor)
        have hc' : ¬ ns.Hill c' := ns.not_hill_of_exists_larger ⟨c, hadj, hlt⟩
        have hlt' : (ns c' : ℕ) < k := by
          rw [← hk]
          exact hlt
        -- apply IH to the dropLast path
        have ihp := ih (ns c' : ℕ) hlt' c' rfl hc' (p.dropLast h2) hcp
        -- pathTo c = pathTo c' ++ [c]
        have hpt : pathTo ns c = pathTo ns c' ++ [c] := by
          have hex : ∃ x : Cell n, Adjacent c x ∧ (ns x : ℕ) < (ns c : ℕ) := ⟨c', hadj.symm, hlt⟩
          rw [NordicSquare.pathTo.eq_1, dite_eq_left hex]
          have hch := Classical.choose_spec hex
          have hce : Classical.choose hex = c' :=
            huniq.unique hch ⟨hadj.symm, hlt⟩
          rw [hce]
        -- assemble
        rw [hpt, ← ihp, ← hlast]
        exact (List.dropLast_append_getLast p.nonempty).symm
  exact P (ns c : ℕ) c rfl hc p hlast

/-- The fiber of uphill paths ending at a non-hill cell has cardinality 1. -/
theorem NordicSquare.countTo_eq_one_of_not_hill {n : ℕ} (ns : NordicSquare n) (hg : ns.Good)
    (c : Cell n) (hc : ¬ ns.Hill c) :
    Nat.card {p : ns.UphillPath // p.cells.getLast p.nonempty = c} = 1 := by
  have : Subsingleton {p : ns.UphillPath // p.cells.getLast p.nonempty = c} :=
    ⟨fun p q ↦ by
      apply Subtype.ext
      apply NordicSquare.UphillPath.ext
      rw [ns.cells_eq_pathTo_of_good hg c hc p.1 p.2,
        ns.cells_eq_pathTo_of_good hg c hc q.1 q.2]⟩
  have : Nonempty {p : ns.UphillPath // p.cells.getLast p.nonempty = c} := by
    refine ⟨⟨ns.uphillPathTo c, ?_⟩⟩
    have h := ns.uphillPathTo_getLast? c
    rw [List.getLast?_eq_some_getLast (ns.uphillPathTo c).nonempty] at h
    exact Option.some.inj h
  exact Nat.card_unique

/-- The degree of a cell: the number of cells adjacent to it. -/
def cellDegree {n : ℕ} (c : Cell n) : ℕ := (Finset.univ.filter fun c' ↦ Adjacent c' c).card

/-- A path ending at a hill (which has a neighbor) has length at least 2. -/
theorem NordicSquare.length_ge_two_of_getLast_hill {n : ℕ} (ns : NordicSquare n)
    (h : Cell n) (hh : ns.Hill h) (hnb : ∃ c', Adjacent h c')
    (p : {p : ns.UphillPath // p.cells.getLast p.nonempty = h}) : 2 ≤ p.1.cells.length := by
  have hne := p.1.nonempty
  rw [List.ne_nil_iff_length_pos] at hne
  by_contra hle
  have h1 : p.1.cells.length = 1 := by omega
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.1 h1
  have hac : a = h := by
    have hgl := p.2
    simp only [ha, List.getLast_singleton] at hgl
    exact hgl
  rw [hac] at ha
  have hval : ns.Valley h := by
    have hfv := p.1.first_valley
    simp only [ha, List.head_singleton] at hfv
    exact hfv
  obtain ⟨c', hadj⟩ := hnb
  have h1 := hval c' hadj
  have h2 := hh c' hadj
  omega

/-- The fiber of uphill paths ending at a hill is equivalent to its set of neighbors. -/
noncomputable def NordicSquare.hillFiberEquiv {n : ℕ} (ns : NordicSquare n) (hg : ns.Good)
    (h : Cell n) (hh : ns.Hill h) (hnb : ∃ c', Adjacent h c') :
    {p : ns.UphillPath // p.cells.getLast p.nonempty = h} ≃ {c' : Cell n // Adjacent c' h} where
  toFun := fun p ↦
    ⟨(p.1.dropLast (ns.length_ge_two_of_getLast_hill h hh hnb p)).cells.getLast
        (p.1.dropLast (ns.length_ge_two_of_getLast_hill h hh hnb p)).nonempty,
      by
        have hp := (p.1.penultimate_props (ns.length_ge_two_of_getLast_hill h hh hnb p)).1
        rw [p.2] at hp
        exact hp⟩
  invFun := fun c' ↦
    ⟨NordicSquare.gapPath ns c'.1 h c'.2,
      by
        have hlt : (ns c'.1 : ℕ) < (ns h : ℕ) := hh c'.1 (c'.2).symm
        have hc := NordicSquare.gapPath_cells ns c'.1 h c'.2
        rw [ite_eq_left hlt] at hc
        simp only [hc]
        exact List.getLast_append_singleton _⟩
  left_inv := by
    intro p
    apply Subtype.ext
    apply NordicSquare.UphillPath.ext
    have h2 : 2 ≤ p.1.cells.length := ns.length_ge_two_of_getLast_hill h hh hnb p
    set c' := (p.1.dropLast h2).cells.getLast _ with hcp
    have hadj : Adjacent c' h := by
      have hp := (p.1.penultimate_props h2).1
      rw [p.2] at hp
      exact hp
    have hlt : (ns c' : ℕ) < (ns h : ℕ) := hh c' hadj.symm
    have hc := NordicSquare.gapPath_cells ns c' h hadj
    rw [ite_eq_left hlt] at hc
    show (NordicSquare.gapPath ns c' h hadj).cells = p.1.cells
    rw [hc]
    -- p.cells = pathTo c' ++ [h]
    have hnh : ¬ ns.Hill c' := by
      intro hh'
      exact hg.hills_independent h c' hh hh' (Adjacent.ne hadj.symm) hadj.symm
    have hpath := ns.cells_eq_pathTo_of_good hg c' hnh (p.1.dropLast h2) rfl
    rw [← hpath]
    have e : p.1.cells = p.1.cells.dropLast ++ [p.1.cells.getLast p.1.nonempty] :=
      (List.dropLast_append_getLast _).symm
    rw [e, p.2]
    rfl
  right_inv := by
    intro c'
    apply Subtype.ext
    have hlt : (ns c'.1 : ℕ) < (ns h : ℕ) := hh c'.1 (c'.2).symm
    have hc := NordicSquare.gapPath_cells ns c'.1 h c'.2
    rw [ite_eq_left hlt] at hc
    have hgl : ((NordicSquare.gapPath ns c'.1 h c'.2).cells.dropLast).getLast? = some c'.1 := by
      rw [hc, List.dropLast_concat]
      exact (NordicSquare.pathTo_props ns c'.1).2.2.2
    have hne : (NordicSquare.gapPath ns c'.1 h c'.2).cells.dropLast ≠ [] := by
      rw [hc, List.dropLast_concat]
      exact NordicSquare.pathTo_ne_nil ns c'.1
    have h2 := List.getLast?_eq_some_getLast hne
    rw [hgl] at h2
    exact (Option.some.inj h2).symm

/-- The fiber of uphill paths ending at a hill has cardinality its degree. -/
theorem NordicSquare.countTo_eq_degree_of_hill {n : ℕ} (ns : NordicSquare n) (hg : ns.Good)
    (h : Cell n) (hh : ns.Hill h) (hnb : ∃ c', Adjacent h c') :
    Nat.card {p : ns.UphillPath // p.cells.getLast p.nonempty = h} = cellDegree h := by
  have h1 : Nat.card {p : ns.UphillPath // p.cells.getLast p.nonempty = h} =
      Nat.card {c' : Cell n // Adjacent c' h} :=
    Nat.card_congr (ns.hillFiberEquiv hg h hh hnb)
  rw [h1, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

/-- Cells of a gap on an `n × n` board (ordered by position). -/
def gapCells {n : ℕ} (d : GapDir) (g : Fin n × Fin (n - 1)) : Cell n × Cell n :=
  match d with
  | .horiz => ((g.1, ⟨g.2.1, by omega⟩), (g.1, ⟨g.2.1 + 1, by omega⟩))
  | .vert => ((⟨g.2.1, by omega⟩, g.1), (⟨g.2.1 + 1, by omega⟩, g.1))

theorem gapCells_adjacent {n : ℕ} (d : GapDir) (g : Fin n × Fin (n - 1)) :
    Adjacent (gapCells d g).1 (gapCells d g).2 := by
  cases d <;> simp [gapCells, Adjacent, Nat.dist]

/-- The arithmetic content of adjacency, unpacked. -/
theorem Adjacent.dist {n : ℕ} {x y : Cell n} (h : Adjacent x y) :
    (x.1.1 - y.1.1 + (y.1.1 - x.1.1)) + (x.2.1 - y.2.1 + (y.2.1 - x.2.1)) = 1 := by
  have h' := h
  simp only [Adjacent, Nat.dist] at h'
  exact h'

/-- The gap determined by an ordered pair of adjacent cells. -/
noncomputable def gapOfPair {n : ℕ} (cc : Cell n × Cell n) (h : Adjacent cc.1 cc.2) :
    GapDir × (Fin n × Fin (n - 1)) :=
  if h1 : cc.1.1 = cc.2.1 then
    (.horiz, (cc.1.1, ⟨min cc.1.2.1 cc.2.2.1, by
      have _hdist := h.dist
      rw [h1, Nat.sub_self, Nat.add_zero] at _hdist
      have h2 := cc.1.2.2
      have h3 := cc.2.2.2
      omega⟩))
  else
    (.vert, (cc.1.2, ⟨min cc.1.1.1 cc.2.1.1, by
      have hdist := h.dist
      have hne : ¬ cc.1.1.1 = cc.2.1.1 := fun hv ↦ h1 (Fin.ext hv)
      have h2 := cc.1.1.2
      have h3 := cc.2.1.2
      omega⟩))

/-- `gapOfPair` is invariant under swapping the two cells. -/
theorem gapOfPair_swap {n : ℕ} (cc : Cell n × Cell n) (h : Adjacent cc.1 cc.2) :
    gapOfPair cc.swap h.symm = gapOfPair cc h := by
  unfold gapOfPair
  by_cases h1 : cc.1.1 = cc.2.1
  · rw [dite_eq_left h1, dite_eq_left (by simpa only [Prod.fst_swap, Prod.snd_swap] using h1.symm)]
    simp only [Prod.fst_swap, Prod.snd_swap, Prod.mk.injEq]
    exact ⟨trivial, h1.symm, by simp [min_comm]⟩
  · have hdist := h.dist
    have hne : ¬ cc.1.1.1 = cc.2.1.1 := fun hv ↦ h1 (Fin.ext hv)
    have ha2 : cc.1.2 = cc.2.2 := by
      have h21 := cc.1.1.2
      have h23 := cc.2.1.2
      have h22 := cc.1.2.2
      have h24 := cc.2.2.2
      omega
    rw [dite_eq_right h1, dite_eq_right (by simpa only [Prod.fst_swap, Prod.snd_swap] using fun hh ↦ h1 hh.symm)]
    simp only [Prod.fst_swap, Prod.snd_swap, Prod.mk.injEq]
    exact ⟨trivial, ha2.symm, by simp [min_comm]⟩

/-- In the horizontal case, `gapOfPair` is the horizontal gap of the two cells. -/
theorem gapOfPair_eq_horiz {n : ℕ} (cc : Cell n × Cell n) (h : Adjacent cc.1 cc.2)
    (h1 : cc.1.1 = cc.2.1) :
    gapOfPair cc h = (.horiz, (cc.1.1, ⟨min cc.1.2.1 cc.2.2.1, by
      have _hdist := h.dist
      rw [h1, Nat.sub_self, Nat.add_zero] at _hdist
      have h2 := cc.1.2.2
      have h3 := cc.2.2.2
      omega⟩)) := by
  unfold gapOfPair
  rw [dite_eq_left h1]

/-- In the vertical case, `gapOfPair` is the vertical gap of the two cells. -/
theorem gapOfPair_eq_vert {n : ℕ} (cc : Cell n × Cell n) (h : Adjacent cc.1 cc.2)
    (h1 : ¬ cc.1.1 = cc.2.1) :
    gapOfPair cc h = (.vert, (cc.1.2, ⟨min cc.1.1.1 cc.2.1.1, by
      have _hdist := h.dist
      have hne : ¬ cc.1.1.1 = cc.2.1.1 := fun hv ↦ h1 (Fin.ext hv)
      have h2 := cc.1.1.2
      have h3 := cc.2.1.2
      omega⟩)) := by
  unfold gapOfPair
  rw [dite_eq_right h1]

/-- The two cells of `gapOfPair cc` are exactly the two cells of `cc` (in some order). -/
theorem gapCells_gapOfPair {n : ℕ} (cc : Cell n × Cell n) (h : Adjacent cc.1 cc.2) :
    gapCells (gapOfPair cc h).1 (gapOfPair cc h).2 = cc ∨
      gapCells (gapOfPair cc h).1 (gapOfPair cc h).2 = cc.swap := by
  by_cases h1 : cc.1.1 = cc.2.1
  · -- horizontal case
    rw [gapOfPair_eq_horiz cc h h1]
    have hdist := h.dist
    rw [h1, Nat.sub_self, Nat.add_zero] at hdist
    have h21 := cc.1.1.2
    have h22 := cc.1.2.2
    have h23 := cc.2.1.2
    have h24 := cc.2.2.2
    simp only [gapCells]
    by_cases hle : cc.1.2.1 ≤ cc.2.2.1
    · left
      apply Prod.ext_iff.2
      refine ⟨Prod.ext_iff.2 ⟨rfl, Fin.ext (by simp only []; omega)⟩,
        Prod.ext_iff.2 ⟨h1, Fin.ext (by simp only []; omega)⟩⟩
    · right
      rw [show cc.swap = (cc.2, cc.1) from rfl]
      apply Prod.ext_iff.2
      refine ⟨Prod.ext_iff.2 ⟨h1, Fin.ext (by simp only []; omega)⟩,
        Prod.ext_iff.2 ⟨rfl, Fin.ext (by simp only []; omega)⟩⟩
  · -- vertical case
    rw [gapOfPair_eq_vert cc h h1]
    have hdist := h.dist
    have hne : ¬ cc.1.1.1 = cc.2.1.1 := fun hv ↦ h1 (Fin.ext hv)
    have hdist1 : cc.1.1.1 - cc.2.1.1 + (cc.2.1.1 - cc.1.1.1) = 1 := by
      have h21 := cc.1.1.2
      have h22 := cc.1.2.2
      have h23 := cc.2.1.2
      have h24 := cc.2.2.2
      omega
    have ha2 : cc.1.2 = cc.2.2 := by
      have h21 := cc.1.1.2
      have h22 := cc.1.2.2
      have h23 := cc.2.1.2
      have h24 := cc.2.2.2
      omega
    have h21 := cc.1.1.2
    have h22 := cc.1.2.2
    have h23 := cc.2.1.2
    have h24 := cc.2.2.2
    simp only [gapCells]
    by_cases hle : cc.1.1.1 ≤ cc.2.1.1
    · left
      apply Prod.ext_iff.2
      refine ⟨Prod.ext_iff.2 ⟨Fin.ext (by simp only []; omega), rfl⟩,
        Prod.ext_iff.2 ⟨Fin.ext (by simp only []; omega), ha2⟩⟩
    · right
      rw [show cc.swap = (cc.2, cc.1) from rfl]
      apply Prod.ext_iff.2
      refine ⟨Prod.ext_iff.2 ⟨Fin.ext (by simp only []; omega), ha2⟩,
        Prod.ext_iff.2 ⟨Fin.ext (by simp only []; omega), rfl⟩⟩

/-- The gap of the cells of a gap is the gap itself. -/
theorem gapOfPair_gapCells {n : ℕ} (d : GapDir) (g : Fin n × Fin (n - 1)) :
    gapOfPair (gapCells d g) (gapCells_adjacent d g) = (d, g) := by
  cases d with
  | horiz =>
    obtain ⟨i, j⟩ := g
    simp [gapCells, gapOfPair, Fin.eta]
  | vert =>
    obtain ⟨i, j⟩ := g
    simp [gapCells, gapOfPair, Fin.eta]

/-- The decreasing orientation of the cells of a gap. -/
noncomputable def decPairOfGap {n : ℕ} (ns : NordicSquare n) (d : GapDir)
    (g : Fin n × Fin (n - 1)) :
    {cc : Cell n × Cell n // Adjacent cc.1 cc.2 ∧ (ns cc.2 : ℕ) < (ns cc.1 : ℕ)} :=
  if h : (ns (gapCells d g).1 : ℕ) < (ns (gapCells d g).2 : ℕ) then
    ⟨((gapCells d g).2, (gapCells d g).1), (gapCells_adjacent d g).symm, h⟩
  else
    ⟨gapCells d g, gapCells_adjacent d g, by
      have hne : (ns (gapCells d g).1 : ℕ) ≠ (ns (gapCells d g).2 : ℕ) :=
        ns.value_ne_of_adjacent (gapCells_adjacent d g)
      omega⟩

/-- The decreasing-adjacent-pairs are equivalent to the gaps. -/
noncomputable def decPairEquivGaps {n : ℕ} (ns : NordicSquare n) :
    {cc : Cell n × Cell n // Adjacent cc.1 cc.2 ∧ (ns cc.2 : ℕ) < (ns cc.1 : ℕ)} ≃
      GapDir × (Fin n × Fin (n - 1)) where
  toFun := fun cc ↦ gapOfPair cc.1 cc.2.1
  invFun := fun g ↦ decPairOfGap ns g.1 g.2
  left_inv := by
    intro cc
    obtain ⟨⟨a, b⟩, hadj, hlt⟩ := cc
    have hlt' : (ns b : ℕ) < (ns a : ℕ) := hlt
    have hcells := gapCells_gapOfPair (a, b) hadj
    show decPairOfGap ns (gapOfPair (a, b) hadj).1 (gapOfPair (a, b) hadj).2 = _
    rw [decPairOfGap]
    rcases hcells with hcells | hcells
    · simp only [hcells]
      rw [dite_eq_right (by omega : ¬ (ns a : ℕ) < (ns b : ℕ))]
    · simp only [hcells, Prod.swap_prod_mk]
      rw [dite_eq_left hlt']
  right_inv := by
    intro g
    have hgo := gapOfPair_gapCells g.1 g.2
    show gapOfPair (decPairOfGap ns g.1 g.2).1 (decPairOfGap ns g.1 g.2).2.1 = g
    rw [decPairOfGap]
    by_cases hif : (ns (gapCells g.1 g.2).1 : ℕ) < (ns (gapCells g.1 g.2).2 : ℕ)
    · rw [dite_eq_left hif]
      have hs := gapOfPair_swap (gapCells g.1 g.2) (gapCells_adjacent g.1 g.2)
      show gapOfPair (gapCells g.1 g.2).swap _ = g
      rw [hs]
      exact hgo
    · rw [dite_eq_right hif]
      show gapOfPair (gapCells g.1 g.2) _ = g
      exact hgo

/-- The number of decreasing adjacent pairs is the number of gaps. -/
theorem card_decPair {n : ℕ} (ns : NordicSquare n) :
    Fintype.card {cc : Cell n × Cell n // Adjacent cc.1 cc.2 ∧ (ns cc.2 : ℕ) < (ns cc.1 : ℕ)} =
      2 * (n * (n - 1)) := by
  have h1 := Fintype.card_congr (decPairEquivGaps ns)
  rw [h1, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  have hgd : Fintype.card GapDir = 2 := by
    rw [← Fintype.card_fin 2]
    exact Fintype.card_congr gapDirEquivFin2
  rw [hgd]

/-- Every cell on a board of side at least 2 has an adjacent cell. -/
theorem exists_adjacent {n : ℕ} (hn : 2 ≤ n) (c : Cell n) : ∃ c', Adjacent c c' := by
  obtain ⟨i, j⟩ := c
  by_cases hi : i.1 = 0
  · refine ⟨(⟨1, by omega⟩, j), ?_⟩
    have hi' : i = ⟨0, by omega⟩ := Fin.ext (by simp [hi])
    rw [hi']
    simp [Adjacent, Nat.dist]
  · refine ⟨(⟨i.1 - 1, by omega⟩, j), ?_⟩
    have h2 := i.2
    simp only [Adjacent, Nat.dist, Nat.sub_self, Nat.add_zero]
    omega

/-- The total number of "smaller neighbor" incidences equals the number of gaps. -/
theorem sum_smaller_eq_gaps {n : ℕ} (ns : NordicSquare n) :
    (∑ c : Cell n, (Finset.univ.filter fun c' ↦ Adjacent c c' ∧ (ns c' : ℕ) < (ns c : ℕ)).card) =
      2 * (n * (n - 1)) := by
  have e1 : ∀ c : Cell n, (Finset.univ.filter fun c' ↦ Adjacent c c' ∧ (ns c' : ℕ) < (ns c : ℕ)).card =
      ∑ c' : Cell n, (if Adjacent c c' ∧ (ns c' : ℕ) < (ns c : ℕ) then 1 else 0) := by
    intro c
    rw [Finset.card_filter]
  rw [Finset.sum_congr rfl (fun c _ ↦ e1 c)]
  rw [← Finset.sum_product']
  rw [← Finset.card_filter, Finset.univ_product_univ, ← Fintype.card_subtype]
  exact card_decPair ns

/-- The number of uphill paths as a sum over the last cell. -/
theorem NordicSquare.card_eq_sum_countTo {n : ℕ} (ns : NordicSquare n) :
    Nat.card ns.UphillPath =
      ∑ c : Cell n, Nat.card {p : ns.UphillPath // p.cells.getLast p.nonempty = c} := by
  have h1 : Nat.card ns.UphillPath = Fintype.card ns.UphillPath := Nat.card_eq_fintype_card
  have h2 : Fintype.card ns.UphillPath =
      ∑ c : Cell n, Fintype.card {p : ns.UphillPath // p.cells.getLast p.nonempty = c} := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv
      (fun p : ns.UphillPath ↦ p.cells.getLast p.nonempty)).symm
  rw [h1, h2]
  exact Finset.sum_congr rfl (fun c _ ↦ (Nat.card_eq_fintype_card).symm)

/-- **Counting theorem**: a good Nordic square on an `n × n` board (with `n ≥ 2`)
has exactly `2 * n * (n - 1) + 1` uphill paths. -/
theorem NordicSquare.good_count {n : ℕ} (hn : 2 ≤ n) (ns : NordicSquare n) (hg : ns.Good) :
    Nat.card ns.UphillPath = 2 * n * (n - 1) + 1 := by
  obtain ⟨v, hv, huniq⟩ := hg.valley_unique
  have hvnot : ¬ ns.Hill v := by
    obtain ⟨c', hadj⟩ := exists_adjacent hn v
    intro hh
    have h1 := hh c' hadj
    have h2 := hv c' hadj
    omega
  -- the smaller-neighbor count of each cell
  have hs : ∀ c : Cell n, (Finset.univ.filter fun c' ↦ Adjacent c c' ∧ (ns c' : ℕ) < (ns c : ℕ)).card =
      if ns.Valley c then 0 else if ns.Hill c then cellDegree c else 1 := by
    intro c
    by_cases hvc : ns.Valley c
    · rw [ite_eq_left hvc, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro c' _ ⟨hadj, hlt⟩
      have := hvc c' hadj
      omega
    · by_cases hh : ns.Hill c
      · rw [ite_eq_right hvc, ite_eq_left hh]
        apply congrArg Finset.card
        apply Finset.filter_congr
        intro c' _
        exact ⟨fun h ↦ h.1.symm, fun hadj ↦ ⟨hadj.symm, hh c' hadj.symm⟩⟩
      · rw [ite_eq_right hvc, ite_eq_right hh]
        obtain ⟨c', hc', hu⟩ := hg.one_smaller c hvc hh
        rw [Finset.card_eq_one]
        refine ⟨c', Finset.ext fun x ↦ ?_⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨fun h ↦ hu x h, fun h ↦ h.symm ▸ hc'⟩
  -- the path count of each cell
  have hcnt : ∀ c : Cell n, Nat.card {p : ns.UphillPath // p.cells.getLast p.nonempty = c} =
      if ns.Hill c then cellDegree c else 1 := by
    intro c
    by_cases hh : ns.Hill c
    · rw [ite_eq_left hh]
      exact ns.countTo_eq_degree_of_hill hg c hh (exists_adjacent hn c)
    · rw [ite_eq_right hh]
      exact ns.countTo_eq_one_of_not_hill hg c hh
  -- assemble
  have hsum : (∑ c : Cell n, (if ns.Valley c then (0 : ℕ) else if ns.Hill c then cellDegree c else 1)) =
      2 * (n * (n - 1)) := by
    rw [← sum_smaller_eq_gaps ns]
    exact Finset.sum_congr rfl (fun c _ ↦ (hs c).symm)
  have hge : 1 ≤ ∑ c : Cell n, (if ns.Hill c then cellDegree c else 1) := by
    have hle := Finset.single_le_sum (f := fun c ↦ if ns.Hill c then cellDegree c else 1)
      (fun c _ ↦ by split <;> exact Nat.zero_le _) (Finset.mem_univ v)
    rw [ite_eq_right hvnot] at hle
    exact hle
  have key : (∑ c : Cell n, (if ns.Valley c then (0 : ℕ) else if ns.Hill c then cellDegree c else 1)) =
      (∑ c : Cell n, (if ns.Hill c then cellDegree c else 1)) - 1 := by
    have h1 : (∑ c : Cell n, (if ns.Valley c then (0 : ℕ) else if ns.Hill c then cellDegree c else 1)) =
        (∑ c : Cell n, (if ns.Hill c then cellDegree c else 1)) - (if ns.Valley v then (1 : ℕ) else 0) := by
      rw [← Finset.add_sum_erase Finset.univ
        (fun c ↦ if ns.Valley c then (0 : ℕ) else if ns.Hill c then cellDegree c else 1)
        (Finset.mem_univ v)]
      rw [ite_eq_left hv, zero_add]
      rw [Finset.sum_congr rfl (g := fun c ↦ if ns.Hill c then cellDegree c else 1)
        (fun c hc ↦ ?_)]
      · rw [← Finset.add_sum_erase Finset.univ
          (fun c ↦ if ns.Hill c then cellDegree c else 1) (Finset.mem_univ v)]
        rw [ite_eq_right hvnot, ite_eq_left hv]
        omega
      · rw [Finset.mem_erase] at hc
        rw [ite_eq_right (show ¬ ns.Valley c from fun hvc ↦ hc.1 (huniq c hvc))]
    rw [h1, ite_eq_left hv]
  rw [NordicSquare.card_eq_sum_countTo, Finset.sum_congr rfl (fun c _ ↦ hcnt c)]
  rw [mul_assoc, ← hsum, key, Nat.sub_add_cancel hge]

/-- The number of uphill paths on a 1×1 board is 1. -/
theorem nat_card_uphillPath_one (ns : NordicSquare 1) : Nat.card ns.UphillPath = 1 := by
  have : Subsingleton (Cell 1) := ⟨fun a b ↦ by
    obtain ⟨a1, a2⟩ := a
    obtain ⟨b1, b2⟩ := b
    simp [Fin.ext_iff]⟩
  have : Subsingleton ns.UphillPath := ⟨fun p q ↦ by
    apply NordicSquare.UphillPath.ext
    have hp : p.cells.length = 1 := by
      have hnd := ns.isChain_nodup p.cells p.increasing
      have h1 := hnd.length_le_card
      rw [Fintype.card_prod, Fintype.card_fin] at h1
      have hne := p.nonempty
      rw [List.ne_nil_iff_length_pos] at hne
      omega
    have hq : q.cells.length = 1 := by
      have hnd := ns.isChain_nodup q.cells q.increasing
      have h1 := hnd.length_le_card
      rw [Fintype.card_prod, Fintype.card_fin] at h1
      have hne := q.nonempty
      rw [List.ne_nil_iff_length_pos] at hne
      omega
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.1 hp
    obtain ⟨b, hb⟩ := List.length_eq_one_iff.1 hq
    rw [ha, hb, Subsingleton.elim a b]⟩
  have : Nonempty ns.UphillPath := ⟨NordicSquare.trivialPath ns⟩
  exact Nat.card_eq_one_iff_unique.2 ⟨inferInstance, inferInstance⟩

/-- The column offset of the construction (handles the case `m % 3 = 1`). -/
def pOffset (m : ℕ) : ℕ := if m % 3 = 1 then 1 else 0

/-- Whether a cell with pattern-column residue `jm6 = j % 6` and row `r` is a tree
cell of the construction (its complement are the hills). -/
def isTreeJ (jm6 : ℕ) (r : ℕ) : Bool :=
  if jm6 = 1 then true
  else if jm6 = 4 then r ≥ 1
  else if jm6 = 0 ∨ jm6 = 2 then r % 2 = 0
  else r % 2 = 1 ∨ r = 0

/-- Whether a cell of the board is a tree cell of the construction. -/
def isTree (m : ℕ) (x : Fin m × Fin m) : Bool :=
  isTreeJ ((x.2.1 + pOffset m) % 6) x.1.1

/-- The position of column-in-strip `cs` within its row in the strip order. -/
def cspos (cs : ℕ) : ℕ := if cs = 1 then 0 else if cs = 0 then 1 else 2

/-- `cspos` is at most 2. -/
theorem cspos_le (cs : ℕ) : cspos cs ≤ 2 := by
  by_cases h1 : cs = 1 <;> by_cases h0 : cs = 0 <;> simp [cspos, h1, h0]

/-- `cspos` is injective on `{0, 1, 2}`. -/
theorem cspos_injective {a b : ℕ} (ha : a ≤ 2) (hb : b ≤ 2) (h : cspos a = cspos b) : a = b := by
  unfold cspos at h
  interval_cases a <;> interval_cases b <;> simp_all

/-- The within-strip order key of a cell (pattern column `j`, row `r`). -/
def subKey (_m : ℕ) (j : ℕ) (r : ℕ) : ℕ :=
  if (j / 3) % 2 = 0 then
    if r = 0 then j % 3
    else 3 + 3 * (r - 1) + cspos (j % 3)
  else
    if r = 0 then (if j % 3 = 0 then 0 else 4)
    else if r = 1 then 1 + (j % 3)
    else 5 + 3 * (r - 2) + cspos (j % 3)

/-- The within-strip key is less than `3 * m`. -/
theorem subKey_lt {m j r : ℕ} (hr : r < m) (hm : 2 ≤ m) : subKey m j r < 3 * m := by
  unfold subKey
  by_cases hs : (j / 3) % 2 = 0
  · rw [ite_eq_left hs]
    by_cases hr0 : r = 0
    · rw [ite_eq_left hr0]
      have : j % 3 < 3 := Nat.mod_lt _ (by omega)
      omega
    · rw [ite_eq_right hr0]
      have := cspos_le (j % 3)
      omega
  · rw [ite_eq_right hs]
    by_cases hr0 : r = 0
    · rw [ite_eq_left hr0]
      split <;> omega
    · rw [ite_eq_right hr0]
      by_cases hr1 : r = 1
      · rw [ite_eq_left hr1]
        have : j % 3 < 3 := Nat.mod_lt _ (by omega)
        omega
      · rw [ite_eq_right hr1]
        have := cspos_le (j % 3)
        omega

/-- The key function of the construction: tree cells come first (in strip order),
then the hills (in column-major order). -/
def keyFn (m : ℕ) (x : Fin m × Fin m) : ℕ :=
  if isTree m x = true then (3 * m) * ((x.2.1 + pOffset m) / 3) + subKey m (x.2.1 + pOffset m) x.1.1
  else m * m + 3 * m + (x.2.1 * m + x.1.1)

/-- The tree key is less than `m * m + 3 * m`. -/
theorem keyFn_tree_lt {m : ℕ} (hm : 2 ≤ m) (x : Fin m × Fin m) (hT : isTree m x = true) :
    keyFn m x < m * m + 3 * m := by
  unfold keyFn
  rw [ite_eq_left hT]
  have hsub := subKey_lt (j := x.2.1 + pOffset m) x.1.2 hm
  have hj : (x.2.1 + pOffset m) / 3 ≤ m / 3 := by
    apply Nat.div_le_div_right
    unfold pOffset
    split <;> omega
  have h3m : 3 * (m / 3) ≤ m := by
    have h := Nat.div_add_mod m 3
    omega
  have hle : (3 * m) * ((x.2.1 + pOffset m) / 3) ≤ (3 * m) * (m / 3) :=
    Nat.mul_le_mul_left (3 * m) hj
  have hle2 : m * (3 * (m / 3)) ≤ m * m := Nat.mul_le_mul_left m h3m
  have hring : (3 * m) * (m / 3) = m * (3 * (m / 3)) := by ring
  omega

/-- The subKey determines the row (within a strip, for tree cells). -/
theorem subKey_inj {m j r₁ r₂ : ℕ} (h : subKey m j r₁ = subKey m j r₂) : r₁ = r₂ := by
  unfold subKey at h
  by_cases hs : (j / 3) % 2 = 0
  · simp only [ite_eq_left hs] at h
    by_cases hr1 : r₁ = 0
    · simp only [ite_eq_left hr1] at h
      by_cases hr2 : r₂ = 0
      · simp only [ite_eq_left hr2] at h
        exact hr1.trans hr2.symm
      · simp only [ite_eq_right hr2] at h
        have hc := cspos_le (j % 3)
        have hmod : j % 3 < 3 := Nat.mod_lt _ (by omega)
        omega
    · simp only [ite_eq_right hr1] at h
      by_cases hr2 : r₂ = 0
      · simp only [ite_eq_left hr2] at h
        have hc := cspos_le (j % 3)
        have hmod : j % 3 < 3 := Nat.mod_lt _ (by omega)
        omega
      · simp only [ite_eq_right hr2] at h
        have hc := cspos_le (j % 3)
        have hd : 3 * (r₁ - 1) = 3 * (r₂ - 1) := by omega
        have := Nat.mul_left_cancel (by omega : 0 < 3) hd
        omega
  · simp only [ite_eq_right hs] at h
    by_cases hr1 : r₁ = 0
    · simp only [ite_eq_left hr1] at h
      by_cases hr2 : r₂ = 0
      · simp only [ite_eq_left hr2] at h
        exact hr1.trans hr2.symm
      · simp only [ite_eq_right hr2] at h
        by_cases hr2' : r₂ = 1
        · simp only [ite_eq_left hr2'] at h
          have hmod : j % 3 < 3 := Nat.mod_lt _ (by omega)
          have hc := cspos_le (j % 3)
          split at h <;> omega
        · simp only [ite_eq_right hr2'] at h
          have hmod : j % 3 < 3 := Nat.mod_lt _ (by omega)
          have hc := cspos_le (j % 3)
          split at h <;> omega
    · simp only [ite_eq_right hr1] at h
      by_cases hr1' : r₁ = 1
      · simp only [ite_eq_left hr1'] at h
        by_cases hr2 : r₂ = 0
        · simp only [ite_eq_left hr2] at h
          have hmod : j % 3 < 3 := Nat.mod_lt _ (by omega)
          split at h <;> omega
        · simp only [ite_eq_right hr2] at h
          by_cases hr2' : r₂ = 1
          · simp only [ite_eq_left hr2'] at h
            exact hr1'.trans hr2'.symm
          · simp only [ite_eq_right hr2'] at h
            have hmod : j % 3 < 3 := Nat.mod_lt _ (by omega)
            have hc := cspos_le (j % 3)
            omega
      · simp only [ite_eq_right hr1'] at h
        by_cases hr2 : r₂ = 0
        · simp only [ite_eq_left hr2] at h
          have hmod : j % 3 < 3 := Nat.mod_lt _ (by omega)
          have hc := cspos_le (j % 3)
          split at h <;> omega
        · simp only [ite_eq_right hr2] at h
          by_cases hr2' : r₂ = 1
          · simp only [ite_eq_left hr2'] at h
            have hmod : j % 3 < 3 := Nat.mod_lt _ (by omega)
            have hc := cspos_le (j % 3)
            omega
          · simp only [ite_eq_right hr2'] at h
            have hc := cspos_le (j % 3)
            have hd : 3 * (r₁ - 2) = 3 * (r₂ - 2) := by omega
            have := Nat.mul_left_cancel (by omega : 0 < 3) hd
            omega

/-- The subKey of a tree cell determines its row and column-in-strip jointly. -/
theorem subKey_inj_both {m j₁ j₂ r₁ r₂ : ℕ} (hs : j₁ / 3 = j₂ / 3)
    (hT1 : isTreeJ (j₁ % 6) r₁ = true) (hT2 : isTreeJ (j₂ % 6) r₂ = true)
    (h : subKey m j₁ r₁ = subKey m j₂ r₂) : r₁ = r₂ ∧ j₁ % 3 = j₂ % 3 := by
  have hc1 : j₁ % 3 < 3 := Nat.mod_lt _ (by omega)
  have hc2 : j₂ % 3 < 3 := Nat.mod_lt _ (by omega)
  have hcp1 := cspos_le (j₁ % 3)
  have hcp2 := cspos_le (j₂ % 3)
  unfold subKey at h
  by_cases hp : (j₁ / 3) % 2 = 0
  · -- even strip: subKey < 3 iff r = 0, otherwise cspos determines the column
    have hp2 : (j₂ / 3) % 2 = 0 := by omega
    simp only [ite_eq_left hp, ite_eq_left hp2] at h
    by_cases hr1 : r₁ = 0
    · simp only [ite_eq_left hr1] at h
      by_cases hr2 : r₂ = 0
      · simp only [ite_eq_left hr2] at h
        exact ⟨hr1.trans hr2.symm, h⟩
      · simp only [ite_eq_right hr2] at h
        omega
    · simp only [ite_eq_right hr1] at h
      by_cases hr2 : r₂ = 0
      · simp only [ite_eq_left hr2] at h
        omega
      · simp only [ite_eq_right hr2] at h
        have hr : r₁ = r₂ := by omega
        have hcp : cspos (j₁ % 3) = cspos (j₂ % 3) := by omega
        exact ⟨hr, cspos_injective (by omega) (by omega) hcp⟩
  · -- odd strip: the ranges {0, 4}, {1, 2, 3}, [5, ∞) separate r = 0, r = 1, r ≥ 2
    have hp2 : ¬(j₂ / 3) % 2 = 0 := by omega
    simp only [ite_eq_right hp, ite_eq_right hp2] at h
    by_cases hr1 : r₁ = 0
    · simp only [ite_eq_left hr1] at h
      by_cases hr2 : r₂ = 0
      · simp only [ite_eq_left hr2] at h
        refine ⟨hr1.trans hr2.symm, ?_⟩
        have hj16 : j₁ % 6 = j₁ % 3 + 3 := by omega
        have hj26 : j₂ % 6 = j₂ % 3 + 3 := by omega
        have hc1ne : j₁ % 3 ≠ 1 := by
          intro hc
          rw [hr1, hj16, hc] at hT1
          simp [isTreeJ] at hT1
        have hc2ne : j₂ % 3 ≠ 1 := by
          intro hc
          rw [hr2, hj26, hc] at hT2
          simp [isTreeJ] at hT2
        split at h <;> split at h <;> omega
      · simp only [ite_eq_right hr2] at h
        by_cases hr2' : r₂ = 1
        · simp only [ite_eq_left hr2'] at h
          split at h <;> omega
        · simp only [ite_eq_right hr2'] at h
          split at h <;> omega
    · simp only [ite_eq_right hr1] at h
      by_cases hr1' : r₁ = 1
      · simp only [ite_eq_left hr1'] at h
        by_cases hr2 : r₂ = 0
        · simp only [ite_eq_left hr2] at h
          split at h <;> omega
        · simp only [ite_eq_right hr2] at h
          by_cases hr2' : r₂ = 1
          · simp only [ite_eq_left hr2'] at h
            exact ⟨hr1'.trans hr2'.symm, by omega⟩
          · simp only [ite_eq_right hr2'] at h
            omega
      · simp only [ite_eq_right hr1'] at h
        by_cases hr2 : r₂ = 0
        · simp only [ite_eq_left hr2] at h
          split at h <;> omega
        · simp only [ite_eq_right hr2] at h
          by_cases hr2' : r₂ = 1
          · simp only [ite_eq_left hr2'] at h
            omega
          · simp only [ite_eq_right hr2'] at h
            have hr : r₁ = r₂ := by omega
            have hcp : cspos (j₁ % 3) = cspos (j₂ % 3) := by omega
            exact ⟨hr, cspos_injective (by omega) (by omega) hcp⟩

/-- The key function is injective. -/
theorem keyFn_injective {m : ℕ} (hm : 2 ≤ m) : Function.Injective (keyFn m) := by
  intro x y hxy
  unfold keyFn at hxy
  by_cases ht1 : isTree m x = true <;> by_cases ht2 : isTree m y = true
  · -- both tree
    rw [ite_eq_left ht1, ite_eq_left ht2] at hxy
    have hK : 0 < 3 * m := by omega
    have hsub1 := subKey_lt (j := x.2.1 + pOffset m) x.1.2 hm
    have hsub2 := subKey_lt (j := y.2.1 + pOffset m) y.1.2 hm
    have hs : (x.2.1 + pOffset m) / 3 = (y.2.1 + pOffset m) / 3 := by
      have h1 := congrArg (· / (3 * m)) hxy
      rw [Nat.mul_add_div hK, Nat.mul_add_div hK] at h1
      rw [Nat.div_eq_of_lt hsub1, Nat.div_eq_of_lt hsub2] at h1
      omega
    have hsub : subKey m (x.2.1 + pOffset m) x.1.1 = subKey m (y.2.1 + pOffset m) y.1.1 := by
      rw [hs] at hxy
      exact Nat.add_left_cancel hxy
    obtain ⟨hr, hcs⟩ := subKey_inj_both hs ht1 ht2 hsub
    have hj : x.2.1 + pOffset m = y.2.1 + pOffset m := by
      have h1 := Nat.div_add_mod (x.2.1 + pOffset m) 3
      have h2 := Nat.div_add_mod (y.2.1 + pOffset m) 3
      omega
    have hx2 : x.2.1 = y.2.1 := by omega
    have hx1 : x.1.1 = y.1.1 := hr
    exact Prod.ext (Fin.ext hx1) (Fin.ext hx2)
  · -- tree vs hill: key x < BIG ≤ key y
    rw [ite_eq_left ht1] at hxy
    have hlt := keyFn_tree_lt hm x ht1
    rw [ite_eq_right ht2] at hxy
    rw [keyFn, ite_eq_left ht1] at hlt
    omega
  · rw [ite_eq_left ht2] at hxy
    have hlt := keyFn_tree_lt hm y ht2
    rw [ite_eq_right ht1] at hxy
    rw [keyFn, ite_eq_left ht2] at hlt
    omega
  · -- both hill
    rw [ite_eq_right ht1, ite_eq_right ht2] at hxy
    have h1 : x.2.1 * m + x.1.1 = y.2.1 * m + y.1.1 := by omega
    have hdiv : (x.2.1 * m + x.1.1) / m = (y.2.1 * m + y.1.1) / m := by rw [h1]
    rw [Nat.mul_comm x.2.1 m, Nat.mul_comm y.2.1 m] at hdiv
    rw [Nat.mul_add_div (by omega : 0 < m), Nat.mul_add_div (by omega : 0 < m)] at hdiv
    rw [Nat.div_eq_of_lt x.1.2, Nat.div_eq_of_lt y.1.2, add_zero, add_zero] at hdiv
    have hx2 : x.2.1 = y.2.1 := hdiv
    rw [hx2] at h1
    have hx1 : x.1.1 = y.1.1 := Nat.add_left_cancel h1
    exact Prod.ext (Fin.ext hx1) (Fin.ext hx2)

/-- The linear order on cells induced by the key function. -/
@[reducible] noncomputable def cellOrder (m : ℕ) (hm : 2 ≤ m) : LinearOrder (Fin m × Fin m) :=
  LinearOrder.lift' (keyFn m) (keyFn_injective hm)

/-- The cell type equipped with the key order (a synonym to avoid instance clashes). -/
def OrderedCell (m : ℕ) := Fin m × Fin m

instance {m : ℕ} : Fintype (OrderedCell m) := inferInstanceAs (Fintype (Fin m × Fin m))

instance {m : ℕ} : DecidableEq (OrderedCell m) := inferInstanceAs (DecidableEq (Fin m × Fin m))

/-- The identity map from cells to ordered cells. -/
def OrderedCell.of {m : ℕ} : Cell m ≃ OrderedCell m := Equiv.refl _

/-- The key function is injective for all `m`. -/
theorem keyFn_injective' (m : ℕ) : Function.Injective (keyFn m) := by
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m
    · intro x y _
      obtain ⟨x1, x2⟩ := x
      obtain ⟨y1, y2⟩ := y
      exact Subsingleton.elim _ _
    · exact Function.injective_of_subsingleton (keyFn 1)
  · exact keyFn_injective hm

/-- The linear order on ordered cells given by the key function. -/
noncomputable instance OrderedCell.instLinearOrder {m : ℕ} : LinearOrder (OrderedCell m) :=
  LinearOrder.lift' (keyFn m) (keyFn_injective' m)

/-- The order isomorphism between all cells (with the key order) and `Fin (m ^ 2)`. -/
noncomputable def nsOfIso {m : ℕ} (_hm : 2 ≤ m) :
    ↥(Finset.univ : Finset (OrderedCell m)) ≃o Fin (m ^ 2) := by
  have hcard : (Finset.univ : Finset (OrderedCell m)).card = m ^ 2 := by
    rw [Finset.card_univ]
    show Fintype.card (Fin m × Fin m) = m ^ 2
    rw [Fintype.card_prod, Fintype.card_fin, pow_two]
  exact (Finset.orderIsoOfFin (Finset.univ : Finset (OrderedCell m)) hcard).symm

/-- The constructed Nordic square: values are positions in the key order plus one. -/
noncomputable def nsOf {m : ℕ} (hm : 2 ≤ m) : NordicSquare m := by
  exact {
  toFun := fun c ↦ ⟨((nsOfIso hm) ⟨OrderedCell.of c, Finset.mem_univ _⟩).1 + 1, by
    rw [Finset.mem_Icc]
    have h2 := ((nsOfIso hm) ⟨OrderedCell.of c, Finset.mem_univ _⟩).2
    omega⟩
  invFun := fun y ↦ ((nsOfIso hm).symm ⟨y.1 - 1, by
    have h2 := y.2
    rw [Finset.mem_Icc] at h2
    omega⟩).1
  left_inv := fun c ↦ by
    have hlt : ((nsOfIso hm) ⟨OrderedCell.of c, Finset.mem_univ _⟩).1 + 1 - 1 < m ^ 2 := by
      have h2 := ((nsOfIso hm) ⟨OrderedCell.of c, Finset.mem_univ _⟩).2
      omega
    show ((nsOfIso hm).symm ⟨((nsOfIso hm) ⟨OrderedCell.of c, Finset.mem_univ _⟩).1 + 1 - 1, hlt⟩).1 = c
    have h : (⟨((nsOfIso hm) ⟨OrderedCell.of c, Finset.mem_univ _⟩).1 + 1 - 1, hlt⟩ : Fin (m ^ 2)) =
        (nsOfIso hm) ⟨OrderedCell.of c, Finset.mem_univ _⟩ := by
      apply Fin.ext
      simp only [Nat.add_sub_cancel]
    rw [h, (nsOfIso hm).symm_apply_apply]
    rfl
  right_inv := fun y ↦ by
    show ⟨((nsOfIso hm) ((nsOfIso hm).symm ⟨y.1 - 1, _⟩)).1 + 1, _⟩ = y
    simp only [(nsOfIso hm).apply_symm_apply]
    have h2 := y.2
    rw [Finset.mem_Icc] at h2
    exact Subtype.ext (Nat.sub_add_cancel h2.1)
  }

/-- Comparison of values in the constructed square is comparison of keys. -/
theorem nsOf_lt_iff {m : ℕ} (hm : 2 ≤ m) (c c' : Fin m × Fin m) :
    (nsOf hm c : ℕ) < (nsOf hm c' : ℕ) ↔ keyFn m c < keyFn m c' := by
  have h1 : (nsOf hm c : ℕ) = ((nsOfIso hm) ⟨OrderedCell.of c, Finset.mem_univ _⟩).1 + 1 := rfl
  have h2 : (nsOf hm c' : ℕ) = ((nsOfIso hm) ⟨OrderedCell.of c', Finset.mem_univ _⟩).1 + 1 := rfl
  rw [h1, h2, Nat.add_lt_add_iff_right]
  show (nsOfIso hm) ⟨OrderedCell.of c, Finset.mem_univ _⟩ <
      (nsOfIso hm) ⟨OrderedCell.of c', Finset.mem_univ _⟩ ↔ keyFn m c < keyFn m c'
  rw [(nsOfIso hm).lt_iff_lt]
  exact Iff.rfl

/-- Characterization of tree cells by column residue and row. -/
lemma isTreeJ_true_iff {c r : ℕ} (hc : c < 6) :
    isTreeJ c r = true ↔
      c = 1 ∨ (c = 4 ∧ r ≥ 1) ∨ ((c = 0 ∨ c = 2) ∧ r % 2 = 0) ∨
        ((c = 3 ∨ c = 5) ∧ (r % 2 = 1 ∨ r = 0)) := by
  unfold isTreeJ
  by_cases h1 : c = 1
  · rw [ite_eq_left h1]
    exact iff_of_true rfl (Or.inl h1)
  · rw [ite_eq_right h1]
    by_cases h4 : c = 4
    · rw [ite_eq_left h4, decide_eq_true_eq]
      constructor
      · intro hr
        exact Or.inr (Or.inl ⟨h4, hr⟩)
      · rintro (h | ⟨-, hr⟩ | ⟨⟨h0 | h2⟩, -⟩ | ⟨⟨h3 | h5⟩, -⟩)
        · omega
        · exact hr
        · omega
        · omega
        · omega
        · omega
    · rw [ite_eq_right h4]
      by_cases h02 : c = 0 ∨ c = 2
      · rw [ite_eq_left h02, decide_eq_true_eq]
        constructor
        · intro hr
          exact Or.inr (Or.inr (Or.inl ⟨h02, hr⟩))
        · rintro (h | ⟨h4', -⟩ | ⟨-, hr⟩ | ⟨⟨h3 | h5⟩, -⟩)
          · omega
          · omega
          · exact hr
          · omega
          · omega
      · rw [ite_eq_right h02, decide_eq_true_eq]
        constructor
        · intro hr
          exact Or.inr (Or.inr (Or.inr ⟨by omega, hr⟩))
        · rintro (h | ⟨h4', -⟩ | ⟨h02', -⟩ | ⟨-, hr⟩)
          · omega
          · omega
          · omega
          · exact hr

/-- The root cell of the construction (its global key minimum). -/
def rootCell (m : ℕ) (hm : 2 ≤ m) : Cell m := (⟨0, by omega⟩, ⟨0, by omega⟩)

theorem rootCell_isTree (m : ℕ) (hm : 2 ≤ m) : isTree m (rootCell m hm) = true := by
  unfold isTree isTreeJ pOffset rootCell
  split <;> simp

theorem rootCell_key_min (m : ℕ) (hm : 2 ≤ m) (x : Cell m) (hx : x ≠ rootCell m hm) :
    keyFn m (rootCell m hm) < keyFn m x := by
  have hpoff : pOffset m ≤ 1 := by
    unfold pOffset
    split <;> omega
  have hrootT : isTree m (rootCell m hm) = true := by
    unfold isTree isTreeJ pOffset rootCell
    split <;> simp
  have hrootkey : keyFn m (rootCell m hm) = pOffset m := by
    have e1 : (rootCell m hm).1.1 = 0 := rfl
    have e2 : (rootCell m hm).2.1 = 0 := rfl
    have h3 : (0 + pOffset m) / 3 = 0 := Nat.div_eq_of_lt (by omega)
    have hmod : (0 + pOffset m) % 3 = pOffset m := by
      rw [Nat.zero_add]
      exact Nat.mod_eq_of_lt (by omega)
    unfold keyFn subKey
    rw [ite_eq_left hrootT, e1, e2, h3, ite_eq_left (Nat.zero_mod 2), ite_eq_left rfl, hmod]
    simp
  rw [hrootkey]
  by_cases hT : isTree m x = true
  · unfold keyFn
    rw [ite_eq_left hT]
    by_cases hj : (x.2.1 + pOffset m) / 3 = 0
    · have hj3 : x.2.1 + pOffset m < 3 := by omega
      unfold subKey
      have hs : ((x.2.1 + pOffset m) / 3) % 2 = 0 := by omega
      rw [ite_eq_left hs]
      by_cases hr : x.1.1 = 0
      · rw [ite_eq_left hr]
        by_cases hx2 : x.2.1 = 0
        · exact absurd (by
            rw [Prod.ext_iff]
            exact ⟨Fin.ext hr, Fin.ext hx2⟩) hx
        · rw [hj, Nat.mod_eq_of_lt hj3]
          omega
      · rw [ite_eq_right hr, hj]
        omega
    · have h1 : 1 ≤ (x.2.1 + pOffset m) / 3 := by omega
      have hge : 3 * m ≤ (3 * m) * ((x.2.1 + pOffset m) / 3) := by
        have hmul := Nat.mul_le_mul_left (3 * m) h1
        rwa [mul_one] at hmul
      have h6 : 6 ≤ 3 * m := by
        have := Nat.mul_le_mul_left 3 hm
        omega
      omega
  · unfold keyFn
    rw [ite_eq_right hT]
    have h4 : 4 ≤ m * m := by
      have := Nat.mul_le_mul hm hm
      omega
    have h6 : 6 ≤ 3 * m := by
      have := Nat.mul_le_mul_left 3 hm
      omega
    omega

theorem tree_key_lt_hill {m : ℕ} (hm : 2 ≤ m) (x y : Cell m)
    (hx : isTree m x = true) (hy : isTree m y = false) : keyFn m x < keyFn m y := by
  have hlt := keyFn_tree_lt hm x hx
  have hy' : ¬ isTree m y = true := by
    rw [hy]
    simp
  unfold keyFn at hlt ⊢
  rw [ite_eq_left hx] at hlt
  rw [ite_eq_left hx, ite_eq_right hy']
  omega

/-- A tree cell in an earlier strip has a smaller key. -/
lemma keyFn_lt_of_strip_lt {m : ℕ} (hm : 2 ≤ m) (jy jx : ℕ) {y : Cell m}
    (hyT : isTree m y = true) {x : Cell m} (hxT : isTree m x = true)
    (hjy : y.2.1 + pOffset m = jy) (hjx : x.2.1 + pOffset m = jx)
    (hst : jy / 3 < jx / 3) (hry : y.1.1 < m) :
    keyFn m y < keyFn m x := by
  unfold keyFn
  rw [ite_eq_left hyT, ite_eq_left hxT, hjy, hjx]
  have hsub := subKey_lt (m := m) (j := jy) hry hm
  have e1 : (3 * m) * (jy / 3) + 3 * m = (3 * m) * (jy / 3 + 1) := by ring
  have e2 : (3 * m) * (jy / 3 + 1) ≤ (3 * m) * (jx / 3) :=
    Nat.mul_le_mul_left (3 * m) (by omega)
  omega

lemma cspos_zero : cspos 0 = 1 := by decide

/-- `cspos` at `1`. -/
lemma cspos_one : cspos 1 = 0 := by decide

/-- `cspos` at `2`. -/
lemma cspos_two : cspos 2 = 2 := by decide

lemma isTreeJ_zero_zero : isTreeJ 0 0 = true := by decide

lemma isTreeJ_one (r : ℕ) : isTreeJ 1 r = true := by
  unfold isTreeJ
  rw [ite_eq_left rfl]

lemma isTreeJ_two_zero : isTreeJ 2 0 = true := by decide

lemma isTreeJ_three_zero : isTreeJ 3 0 = true := by decide

lemma isTreeJ_three_one : isTreeJ 3 1 = true := by decide

lemma isTreeJ_four {r : ℕ} (hr : 1 ≤ r) : isTreeJ 4 r = true := by
  unfold isTreeJ
  rw [ite_eq_right (by norm_num : ¬((4 : ℕ) = 1)), ite_eq_left rfl, decide_eq_true_eq]
  exact hr

lemma isTreeJ_five_zero : isTreeJ 5 0 = true := by decide

lemma isTreeJ_five_one : isTreeJ 5 1 = true := by decide

/-- `subKey` at row `0` of an even strip. -/
lemma subKey_even_zero {m j : ℕ} (hj : (j / 3) % 2 = 0) : subKey m j 0 = j % 3 := by
  unfold subKey
  rw [ite_eq_left hj, ite_eq_left rfl]

/-- `subKey` at a positive row of an even strip. -/
lemma subKey_even_of_ne_zero {m j r : ℕ} (hj : (j / 3) % 2 = 0) (hr : r ≠ 0) :
    subKey m j r = 3 + 3 * (r - 1) + cspos (j % 3) := by
  unfold subKey
  rw [ite_eq_left hj, ite_eq_right hr]

/-- `subKey` at row `0` of an odd strip. -/
lemma subKey_odd_zero {m j : ℕ} (hj : (j / 3) % 2 ≠ 0) :
    subKey m j 0 = (if j % 3 = 0 then 0 else 4) := by
  unfold subKey
  rw [ite_eq_right hj, ite_eq_left rfl]

/-- `subKey` at row `1` of an odd strip. -/
lemma subKey_odd_one {m j : ℕ} (hj : (j / 3) % 2 ≠ 0) :
    subKey m j 1 = 1 + j % 3 := by
  unfold subKey
  rw [ite_eq_right hj, ite_eq_right (by norm_num : ¬((1 : ℕ) = 0)), ite_eq_left rfl]

/-- `subKey` at a row `≥ 2` of an odd strip. -/
lemma subKey_odd_of_ge_two {m j r : ℕ} (hj : (j / 3) % 2 ≠ 0) (hr : 2 ≤ r) :
    subKey m j r = 5 + 3 * (r - 2) + cspos (j % 3) := by
  unfold subKey
  rw [ite_eq_right hj, ite_eq_right (by omega : r ≠ 0), ite_eq_right (by omega : r ≠ 1)]

/-- Between two tree cells in the same strip, the key order is the `subKey` order. -/
lemma keyFn_lt_of_same_strip {m : ℕ} (jy jx : ℕ) {y : Cell m}
    (hyT : isTree m y = true) {x : Cell m} (hxT : isTree m x = true)
    (hjy : y.2.1 + pOffset m = jy) (hjx : x.2.1 + pOffset m = jx)
    (hst : jy / 3 = jx / 3) (hsub : subKey m jy y.1.1 < subKey m jx x.1.1) :
    keyFn m y < keyFn m x := by
  unfold keyFn
  rw [ite_eq_left hyT, ite_eq_left hxT, hjy, hjx, hst]
  omega

/-- A tree cell in an earlier strip has a smaller key. -/
theorem parent_exists {m : ℕ} (hm : 2 ≤ m) (x : Cell m)
    (hx : isTree m x = true) (hx0 : x ≠ rootCell m hm) :
    ∃ y : Cell m, Adjacent x y ∧ isTree m y = true ∧ keyFn m y < keyFn m x := by
  obtain ⟨r, c⟩ := x
  have hr : r.1 < m := r.2
  have hc : c.1 < m := c.2
  have hoff : pOffset m ≤ 1 := by unfold pOffset; split <;> omega
  set j : ℕ := c.1 + pOffset m with hj
  have hT : isTreeJ (j % 6) r.1 = true := hx
  have hne_root : ¬ (r.1 = 0 ∧ c.1 = 0) := by
    rintro ⟨h0, h1⟩
    apply hx0
    unfold rootCell
    rw [Prod.ext_iff]
    exact ⟨Fin.ext h0, Fin.ext h1⟩
  have h6cases : j % 6 = 0 ∨ j % 6 = 1 ∨ j % 6 = 2 ∨ j % 6 = 3 ∨ j % 6 = 4 ∨
      j % 6 = 5 := by
    have hlt := Nat.mod_lt j (by norm_num : 0 < 6)
    omega
  rcases h6cases with h6 | h6 | h6 | h6 | h6 | h6
  · -- even strip, column `0` of the strip: tree rows are the even rows
    rw [h6] at hT
    have hcond : r.1 % 2 = 0 := by
      unfold isTreeJ at hT
      rw [ite_eq_right (by norm_num : ¬((0 : ℕ) = 1)), ite_eq_right (by norm_num : ¬((0 : ℕ) = 4)),
        ite_eq_left (by norm_num : (0 : ℕ) = 0 ∨ (0 : ℕ) = 2), decide_eq_true_eq] at hT
      exact hT
    rcases Nat.eq_zero_or_pos r.1 with h0 | h0
    · -- `x = (0, c)`: the parent is the last row-0 cell of the previous strip
      have hj6 : 6 ≤ j := by
        by_contra hlt
        have hj0 : j = 0 := by omega
        have hc0 : c.1 = 0 := by omega
        exact hne_root ⟨h0, hc0⟩
      have hc1 : ↑c - 1 < m := by omega
      have hyT : isTree m (r, ⟨c.1 - 1, hc1⟩) = true := by
        show isTreeJ ((c.1 - 1 + pOffset m) % 6) r.1 = true
        rw [show c.1 - 1 + pOffset m = j - 1 by omega, show (j - 1) % 6 = 5 by omega, h0]
        exact isTreeJ_five_zero
      refine ⟨(r, ⟨c.1 - 1, by omega⟩), ?_, hyT, ?_⟩
      · simp only [Adjacent, Nat.dist, Nat.sub_self, Nat.add_zero, Nat.zero_add]
        omega
      · exact keyFn_lt_of_strip_lt hm (j - 1) j hyT hx
          (by show c.1 - 1 + pOffset m = j - 1; omega) hj.symm (by omega) hr
    · -- `x = (r, c)` with `r ≥ 2` even: the parent is the middle-column cell `(r, c+1)`
      have hr2 : 2 ≤ r.1 := by omega
      have hc1 : c.1 + 1 < m := by
        by_cases hm3 : m % 3 = 1
        · have h1 : pOffset m = 1 := by unfold pOffset; rw [ite_eq_left hm3]
          omega
        · have h0' : pOffset m = 0 := by unfold pOffset; rw [ite_eq_right hm3]
          omega
      have hyT : isTree m (r, ⟨c.1 + 1, hc1⟩) = true := by
        show isTreeJ ((c.1 + 1 + pOffset m) % 6) r.1 = true
        rw [show c.1 + 1 + pOffset m = j + 1 by omega, show (j + 1) % 6 = 1 by omega]
        exact isTreeJ_one _
      refine ⟨(r, ⟨c.1 + 1, by omega⟩), ?_, hyT, ?_⟩
      · simp only [Adjacent, Nat.dist, Nat.sub_self, Nat.add_zero, Nat.zero_add]
        omega
      · have hsub : subKey m (j + 1) r.1 < subKey m j r.1 := by
          rw [subKey_even_of_ne_zero (by omega : ((j + 1) / 3) % 2 = 0) (by omega : r.1 ≠ 0),
            subKey_even_of_ne_zero (by omega : (j / 3) % 2 = 0) (by omega : r.1 ≠ 0),
            show (j + 1) % 3 = 1 by omega, show j % 3 = 0 by omega, cspos_one, cspos_zero]
          omega
        exact keyFn_lt_of_same_strip (j + 1) j hyT hx
          (by show c.1 + 1 + pOffset m = j + 1; omega) hj.symm (by omega) hsub
  · -- even strip, column `1` of the strip: all rows are tree cells
    rcases Nat.eq_zero_or_pos r.1 with h0 | h0
    · -- `x = (0, c)`: the parent is `(0, c-1)`, the strip's first cell (or the root)
      have hc1 : 1 ≤ c.1 := by
        by_contra hlt
        have hc0 : c.1 = 0 := by omega
        exact hne_root ⟨h0, hc0⟩
      have hyT : isTree m (r, ⟨c.1 - 1, by omega⟩) = true := by
        show isTreeJ ((c.1 - 1 + pOffset m) % 6) r.1 = true
        rw [show c.1 - 1 + pOffset m = j - 1 by omega, show (j - 1) % 6 = 0 by omega, h0]
        exact isTreeJ_zero_zero
      refine ⟨(r, ⟨c.1 - 1, by omega⟩), ?_, hyT, ?_⟩
      · simp only [Adjacent, Nat.dist, Nat.sub_self, Nat.add_zero, Nat.zero_add]
        omega
      · have hsub : subKey m (j - 1) r.1 < subKey m j r.1 := by
          rw [h0, subKey_even_zero (by omega : ((j - 1) / 3) % 2 = 0),
            subKey_even_zero (by omega : (j / 3) % 2 = 0)]
          omega
        exact keyFn_lt_of_same_strip (j - 1) j hyT hx
          (by show c.1 - 1 + pOffset m = j - 1; omega) hj.symm (by omega) hsub
    · -- `x = (r, c)` with `r ≥ 1`: the parent is `(r-1, c)` directly above
      have hyT : isTree m (⟨r.1 - 1, by omega⟩, c) = true := by
        show isTreeJ (j % 6) (r.1 - 1) = true
        rw [h6]
        exact isTreeJ_one _
      refine ⟨(⟨r.1 - 1, by omega⟩, c), ?_, hyT, ?_⟩
      · simp only [Adjacent, Nat.dist, Nat.sub_self, Nat.add_zero]
        omega
      · have hsub : subKey m j (r.1 - 1) < subKey m j r.1 := by
          by_cases h1 : r.1 = 1
          · rw [h1]
            show subKey m j 0 < subKey m j 1
            rw [subKey_even_zero (by omega : (j / 3) % 2 = 0),
              subKey_even_of_ne_zero (by omega : (j / 3) % 2 = 0) (by norm_num : (1 : ℕ) ≠ 0),
              show j % 3 = 1 by omega, cspos_one]
            omega
          · have hr2 : 2 ≤ r.1 := by omega
            rw [subKey_even_of_ne_zero (by omega : (j / 3) % 2 = 0) (by omega : r.1 - 1 ≠ 0),
              subKey_even_of_ne_zero (by omega : (j / 3) % 2 = 0) (by omega : r.1 ≠ 0),
              show j % 3 = 1 by omega, cspos_one]
            omega
        exact keyFn_lt_of_same_strip j j hyT hx hj.symm hj.symm rfl hsub
  · -- even strip, column `2` of the strip: tree rows are the even rows
    rw [h6] at hT
    have hcond : r.1 % 2 = 0 := by
      unfold isTreeJ at hT
      rw [ite_eq_right (by norm_num : ¬((2 : ℕ) = 1)), ite_eq_right (by norm_num : ¬((2 : ℕ) = 4)),
        ite_eq_left (by norm_num : (2 : ℕ) = 0 ∨ (2 : ℕ) = 2), decide_eq_true_eq] at hT
      exact hT
    rcases Nat.eq_zero_or_pos r.1 with h0 | h0
    · -- `x = (0, c)`: the parent is `(0, c-1)`, the middle cell of row `0` in this strip
      have hc1 : 1 ≤ c.1 := by omega
      have hyT : isTree m (r, ⟨c.1 - 1, by omega⟩) = true := by
        show isTreeJ ((c.1 - 1 + pOffset m) % 6) r.1 = true
        rw [show c.1 - 1 + pOffset m = j - 1 by omega, show (j - 1) % 6 = 1 by omega]
        exact isTreeJ_one _
      refine ⟨(r, ⟨c.1 - 1, by omega⟩), ?_, hyT, ?_⟩
      · simp only [Adjacent, Nat.dist, Nat.sub_self, Nat.add_zero, Nat.zero_add]
        omega
      · have hsub : subKey m (j - 1) r.1 < subKey m j r.1 := by
          rw [h0, subKey_even_zero (by omega : ((j - 1) / 3) % 2 = 0),
            subKey_even_zero (by omega : (j / 3) % 2 = 0)]
          omega
        exact keyFn_lt_of_same_strip (j - 1) j hyT hx
          (by show c.1 - 1 + pOffset m = j - 1; omega) hj.symm (by omega) hsub
    · -- `x = (r, c)` with `r ≥ 2` even: the parent is `(r, c-1)`
      have hr2 : 2 ≤ r.1 := by omega
      have hc1 : 1 ≤ c.1 := by omega
      have hyT : isTree m (r, ⟨c.1 - 1, by omega⟩) = true := by
        show isTreeJ ((c.1 - 1 + pOffset m) % 6) r.1 = true
        rw [show c.1 - 1 + pOffset m = j - 1 by omega, show (j - 1) % 6 = 1 by omega]
        exact isTreeJ_one _
      refine ⟨(r, ⟨c.1 - 1, by omega⟩), ?_, hyT, ?_⟩
      · simp only [Adjacent, Nat.dist, Nat.sub_self, Nat.add_zero, Nat.zero_add]
        omega
      · have hsub : subKey m (j - 1) r.1 < subKey m j r.1 := by
          rw [subKey_even_of_ne_zero (by omega : ((j - 1) / 3) % 2 = 0) (by omega : r.1 ≠ 0),
            subKey_even_of_ne_zero (by omega : (j / 3) % 2 = 0) (by omega : r.1 ≠ 0),
            show (j - 1) % 3 = 1 by omega, show j % 3 = 2 by omega, cspos_one, cspos_two]
          omega
        exact keyFn_lt_of_same_strip (j - 1) j hyT hx
          (by show c.1 - 1 + pOffset m = j - 1; omega) hj.symm (by omega) hsub
  · -- odd strip, column `0` of the strip: tree rows are row `0` and the odd rows
    rw [h6] at hT
    have hcond : r.1 % 2 = 1 ∨ r.1 = 0 := by
      unfold isTreeJ at hT
      rw [ite_eq_right (by norm_num : ¬((3 : ℕ) = 1)), ite_eq_right (by norm_num : ¬((3 : ℕ) = 4)),
        ite_eq_right (by norm_num : ¬((3 : ℕ) = 0 ∨ (3 : ℕ) = 2)), decide_eq_true_eq] at hT
      exact hT
    rcases Nat.eq_zero_or_pos r.1 with h0 | h0
    · -- `x = (0, c)`: the parent is the last row-0 cell of the previous strip
      have hc1 : 1 ≤ c.1 := by omega
      have hyT : isTree m (r, ⟨c.1 - 1, by omega⟩) = true := by
        show isTreeJ ((c.1 - 1 + pOffset m) % 6) r.1 = true
        rw [show c.1 - 1 + pOffset m = j - 1 by omega, show (j - 1) % 6 = 2 by omega, h0]
        exact isTreeJ_two_zero
      refine ⟨(r, ⟨c.1 - 1, by omega⟩), ?_, hyT, ?_⟩
      · simp only [Adjacent, Nat.dist, Nat.sub_self, Nat.add_zero, Nat.zero_add]
        omega
      · exact keyFn_lt_of_strip_lt hm (j - 1) j hyT hx
          (by show c.1 - 1 + pOffset m = j - 1; omega) hj.symm (by omega) hr
    · have hcond1 : r.1 % 2 = 1 := by
        rcases hcond with h | h
        · exact h
        · omega
      by_cases h1 : r.1 = 1
      · -- `x = (1, c)`: the parent is `(0, c)` directly above
        have hyT : isTree m (⟨0, by omega⟩, c) = true := by
          show isTreeJ (j % 6) 0 = true
          rw [h6]
          exact isTreeJ_three_zero
        refine ⟨(⟨0, by omega⟩, c), ?_, hyT, ?_⟩
        · simp only [Adjacent, Nat.dist, Nat.sub_self, Nat.add_zero]
          omega
        · have hsub : subKey m j 0 < subKey m j r.1 := by
            rw [h1, subKey_odd_zero (by omega : (j / 3) % 2 ≠ 0),
              subKey_odd_one (by omega : (j / 3) % 2 ≠ 0), show j % 3 = 0 by omega, ite_eq_left rfl]
            omega
          exact keyFn_lt_of_same_strip j j hyT hx hj.symm hj.symm rfl hsub
      · -- `x = (r, c)` with `r ≥ 3` odd: the parent is `(r, c+1)`
        have hr3 : 3 ≤ r.1 := by omega
        have hc1 : c.1 + 1 < m := by
          by_cases hm3 : m % 3 = 1
          · have h1' : pOffset m = 1 := by unfold pOffset; rw [ite_eq_left hm3]
            omega
          · have h0' : pOffset m = 0 := by unfold pOffset; rw [ite_eq_right hm3]
            omega
        have hyT : isTree m (r, ⟨c.1 + 1, by omega⟩) = true := by
          show isTreeJ ((c.1 + 1 + pOffset m) % 6) r.1 = true
          rw [show c.1 + 1 + pOffset m = j + 1 by omega, show (j + 1) % 6 = 4 by omega]
          exact isTreeJ_four (by omega : 1 ≤ r.1)
        refine ⟨(r, ⟨c.1 + 1, by omega⟩), ?_, hyT, ?_⟩
        · simp only [Adjacent, Nat.dist, Nat.sub_self, Nat.add_zero, Nat.zero_add]
          omega
        · have hsub : subKey m (j + 1) r.1 < subKey m j r.1 := by
            rw [subKey_odd_of_ge_two (by omega : ((j + 1) / 3) % 2 ≠ 0) (by omega : 2 ≤ r.1),
              subKey_odd_of_ge_two (by omega : (j / 3) % 2 ≠ 0) (by omega : 2 ≤ r.1),
              show (j + 1) % 3 = 1 by omega, show j % 3 = 0 by omega, cspos_one, cspos_zero]
            omega
          exact keyFn_lt_of_same_strip (j + 1) j hyT hx
            (by show c.1 + 1 + pOffset m = j + 1; omega) hj.symm (by omega) hsub
  · -- odd strip, column `1` of the strip: tree rows are the rows `≥ 1`
    rw [h6] at hT
    have hr1 : 1 ≤ r.1 := by
      unfold isTreeJ at hT
      rw [ite_eq_right (by norm_num : ¬((4 : ℕ) = 1)), ite_eq_left rfl, decide_eq_true_eq] at hT
      exact hT
    by_cases h1 : r.1 = 1
    · -- `x = (1, c)`: the parent is `(1, c-1)`
      have hc1 : 1 ≤ c.1 := by omega
      have hyT : isTree m (r, ⟨c.1 - 1, by omega⟩) = true := by
        show isTreeJ ((c.1 - 1 + pOffset m) % 6) r.1 = true
        rw [show c.1 - 1 + pOffset m = j - 1 by omega, show (j - 1) % 6 = 3 by omega, h1]
        exact isTreeJ_three_one
      refine ⟨(r, ⟨c.1 - 1, by omega⟩), ?_, hyT, ?_⟩
      · simp only [Adjacent, Nat.dist, Nat.sub_self, Nat.add_zero, Nat.zero_add]
        omega
      · have hsub : subKey m (j - 1) r.1 < subKey m j r.1 := by
          rw [h1, subKey_odd_one (by omega : ((j - 1) / 3) % 2 ≠ 0),
            subKey_odd_one (by omega : (j / 3) % 2 ≠ 0),
            show (j - 1) % 3 = 0 by omega, show j % 3 = 1 by omega]
          omega
        exact keyFn_lt_of_same_strip (j - 1) j hyT hx
          (by show c.1 - 1 + pOffset m = j - 1; omega) hj.symm (by omega) hsub
    · -- `x = (r, c)` with `r ≥ 2`: the parent is `(r-1, c)` directly above
      have hr2 : 2 ≤ r.1 := by omega
      have hyT : isTree m (⟨r.1 - 1, by omega⟩, c) = true := by
        show isTreeJ (j % 6) (r.1 - 1) = true
        rw [h6]
        exact isTreeJ_four (by omega : 1 ≤ r.1 - 1)
      refine ⟨(⟨r.1 - 1, by omega⟩, c), ?_, hyT, ?_⟩
      · simp only [Adjacent, Nat.dist, Nat.sub_self, Nat.add_zero]
        omega
      · have hsub : subKey m j (r.1 - 1) < subKey m j r.1 := by
          by_cases h2 : r.1 = 2
          · rw [h2]
            show subKey m j 1 < subKey m j 2
            rw [subKey_odd_one (by omega : (j / 3) % 2 ≠ 0),
              subKey_odd_of_ge_two (by omega : (j / 3) % 2 ≠ 0) (by norm_num : (2 : ℕ) ≤ 2),
              show j % 3 = 1 by omega, cspos_one]
            omega
          · have hr3 : 3 ≤ r.1 := by omega
            rw [subKey_odd_of_ge_two (by omega : (j / 3) % 2 ≠ 0) (by omega : 2 ≤ r.1 - 1),
              subKey_odd_of_ge_two (by omega : (j / 3) % 2 ≠ 0) (by omega : 2 ≤ r.1),
              show j % 3 = 1 by omega, cspos_one]
            omega
        exact keyFn_lt_of_same_strip j j hyT hx hj.symm hj.symm rfl hsub
  · -- odd strip, column `2` of the strip: tree rows are row `0` and the odd rows
    rw [h6] at hT
    have hcond : r.1 % 2 = 1 ∨ r.1 = 0 := by
      unfold isTreeJ at hT
      rw [ite_eq_right (by norm_num : ¬((5 : ℕ) = 1)), ite_eq_right (by norm_num : ¬((5 : ℕ) = 4)),
        ite_eq_right (by norm_num : ¬((5 : ℕ) = 0 ∨ (5 : ℕ) = 2)), decide_eq_true_eq] at hT
      exact hT
    rcases Nat.eq_zero_or_pos r.1 with h0 | h0
    · -- `x = (0, c)`: the parent is `(1, c)` directly below
      have hyT : isTree m (⟨1, by omega⟩, c) = true := by
        show isTreeJ (j % 6) 1 = true
        rw [h6]
        exact isTreeJ_five_one
      refine ⟨(⟨1, by omega⟩, c), ?_, hyT, ?_⟩
      · simp only [Adjacent, Nat.dist, Nat.sub_self, Nat.add_zero]
        omega
      · have hsub : subKey m j 1 < subKey m j r.1 := by
          rw [h0, subKey_odd_one (by omega : (j / 3) % 2 ≠ 0),
            subKey_odd_zero (by omega : (j / 3) % 2 ≠ 0), show j % 3 = 2 by omega,
            ite_eq_right (by norm_num : ¬((2 : ℕ) = 0))]
          omega
        exact keyFn_lt_of_same_strip j j hyT hx hj.symm hj.symm rfl hsub
    · have hcond1 : r.1 % 2 = 1 := by
        rcases hcond with h | h
        · exact h
        · omega
      by_cases h1 : r.1 = 1
      · -- `x = (1, c)`: the parent is `(1, c-1)`
        have hc1 : 1 ≤ c.1 := by omega
        have hyT : isTree m (r, ⟨c.1 - 1, by omega⟩) = true := by
          show isTreeJ ((c.1 - 1 + pOffset m) % 6) r.1 = true
          rw [show c.1 - 1 + pOffset m = j - 1 by omega, show (j - 1) % 6 = 4 by omega, h1]
          exact isTreeJ_four (by norm_num : 1 ≤ 1)
        refine ⟨(r, ⟨c.1 - 1, by omega⟩), ?_, hyT, ?_⟩
        · simp only [Adjacent, Nat.dist, Nat.sub_self, Nat.add_zero, Nat.zero_add]
          omega
        · have hsub : subKey m (j - 1) r.1 < subKey m j r.1 := by
            rw [h1, subKey_odd_one (by omega : ((j - 1) / 3) % 2 ≠ 0),
              subKey_odd_one (by omega : (j / 3) % 2 ≠ 0),
              show (j - 1) % 3 = 1 by omega, show j % 3 = 2 by omega]
            omega
          exact keyFn_lt_of_same_strip (j - 1) j hyT hx
            (by show c.1 - 1 + pOffset m = j - 1; omega) hj.symm (by omega) hsub
      · -- `x = (r, c)` with `r ≥ 3` odd: the parent is `(r, c-1)`
        have hr3 : 3 ≤ r.1 := by omega
        have hc1 : 1 ≤ c.1 := by omega
        have hyT : isTree m (r, ⟨c.1 - 1, by omega⟩) = true := by
          show isTreeJ ((c.1 - 1 + pOffset m) % 6) r.1 = true
          rw [show c.1 - 1 + pOffset m = j - 1 by omega, show (j - 1) % 6 = 4 by omega]
          exact isTreeJ_four (by omega : 1 ≤ r.1)
        refine ⟨(r, ⟨c.1 - 1, by omega⟩), ?_, hyT, ?_⟩
        · simp only [Adjacent, Nat.dist, Nat.sub_self, Nat.add_zero, Nat.zero_add]
          omega
        · have hsub : subKey m (j - 1) r.1 < subKey m j r.1 := by
            rw [subKey_odd_of_ge_two (by omega : ((j - 1) / 3) % 2 ≠ 0) (by omega : 2 ≤ r.1),
              subKey_odd_of_ge_two (by omega : (j / 3) % 2 ≠ 0) (by omega : 2 ≤ r.1),
              show (j - 1) % 3 = 1 by omega, show j % 3 = 2 by omega, cspos_one, cspos_two]
            omega
          exact keyFn_lt_of_same_strip (j - 1) j hyT hx
            (by show c.1 - 1 + pOffset m = j - 1; omega) hj.symm (by omega) hsub


theorem keyFn_tree_eq {m : ℕ} (x : Cell m) (hx : isTree m x = true) :
    keyFn m x = 3 * m * ((x.2.1 + pOffset m) / 3) + subKey m (x.2.1 + pOffset m) x.1.1 := by
  unfold keyFn
  rw [ite_eq_left hx]

/-- `subKey` in an even strip, row `0`. -/

theorem subKey_even_pos {m j r : ℕ} (hs : (j / 3) % 2 = 0) (hr : 1 ≤ r) :
    subKey m j r = 3 + 3 * (r - 1) + cspos (j % 3) := by
  unfold subKey
  rw [ite_eq_left hs, ite_eq_right (by omega : ¬ r = 0)]

/-- `subKey` in an odd strip, row `0`. -/

theorem subKey_odd_ge2 {m j r : ℕ} (hs : ¬ (j / 3) % 2 = 0) (hr : 2 ≤ r) :
    subKey m j r = 5 + 3 * (r - 2) + cspos (j % 3) := by
  unfold subKey
  rw [ite_eq_right hs, ite_eq_right (by omega : ¬ r = 0), ite_eq_right (by omega : ¬ r = 1)]

/-- If the tree cell `y` directly below the tree cell `x` has smaller key, then `x`
has pattern column `5` (mod 6) and row `0`. -/

theorem rule_down {m : ℕ} (_hm : 2 ≤ m) (x y : Cell m)
    (hx : isTree m x = true) (hy : isTree m y = true)
    (hcol : y.2.1 = x.2.1) (hrow : y.1.1 = x.1.1 + 1)
    (hyk : keyFn m y < keyFn m x) :
    (x.2.1 + pOffset m) % 6 = 5 ∧ x.1.1 = 0 := by
  rw [keyFn_tree_eq x hx, keyFn_tree_eq y hy] at hyk
  rw [hcol, hrow] at hyk
  unfold isTree at hx
  generalize hjd : x.2.1 + pOffset m = j at *
  generalize hrd : x.1.1 = r at *
  have hsub : subKey m j (r + 1) < subKey m j r := by omega
  have hmod : j % 3 < 3 := Nat.mod_lt _ (by omega)
  have hcp := cspos_le (j % 3)
  by_cases hs : (j / 3) % 2 = 0
  · by_cases hr : r = 0
    · subst hr
      rw [subKey_even_zero hs, subKey_even_pos hs (show 1 ≤ (0 : ℕ) + 1 by omega)] at hsub
      omega
    · have hr1 : 1 ≤ r := by omega
      rw [subKey_even_pos hs (show 1 ≤ r + 1 by omega), subKey_even_pos hs hr1] at hsub
      omega
  · by_cases hr : r = 0
    · subst hr
      rw [show (0 : ℕ) + 1 = 1 from rfl, subKey_odd_one hs, subKey_odd_zero hs] at hsub
      by_cases hc0 : j % 3 = 0
      · rw [ite_eq_left hc0] at hsub
        omega
      · rw [ite_eq_right hc0] at hsub
        have hj6 : j % 6 = j % 3 + 3 := by omega
        by_cases hc1 : j % 3 = 1
        · rw [hj6, hc1] at hx
          simp [isTreeJ] at hx
        · have hc2 : j % 3 = 2 := by omega
          exact ⟨by omega, rfl⟩
    · have hr1 : 1 ≤ r := by omega
      by_cases hr1e : r = 1
      · subst hr1e
        rw [show (1 : ℕ) + 1 = 2 from rfl, subKey_odd_ge2 hs (show 2 ≤ (2 : ℕ) by omega),
          subKey_odd_one hs] at hsub
        omega
      · have hr2 : 2 ≤ r := by omega
        rw [subKey_odd_ge2 hs (show 2 ≤ r + 1 by omega), subKey_odd_ge2 hs hr2] at hsub
        omega

/-- If the tree cell `y` directly above the tree cell `x` has smaller key, then `x`
has pattern column `1` (mod 6) with a positive row, or pattern column `3` and row `1`,
or pattern column `4` and row at least `2`. -/
theorem rule_up {m : ℕ} (_hm : 2 ≤ m) (x y : Cell m)
    (hx : isTree m x = true) (hy : isTree m y = true)
    (hcol : y.2.1 = x.2.1) (hrow : y.1.1 + 1 = x.1.1)
    (hyk : keyFn m y < keyFn m x) :
    (x.2.1 + pOffset m) % 6 = 1 ∧ 1 ≤ x.1.1 ∨
      (x.2.1 + pOffset m) % 6 = 3 ∧ x.1.1 = 1 ∨
        (x.2.1 + pOffset m) % 6 = 4 ∧ 2 ≤ x.1.1 := by
  rw [keyFn_tree_eq x hx, keyFn_tree_eq y hy] at hyk
  have hry : y.1.1 = x.1.1 - 1 := by omega
  rw [hcol, hry] at hyk
  unfold isTree at hx hy
  rw [hcol, hry] at hy
  generalize hjd : x.2.1 + pOffset m = j at *
  generalize hrd : x.1.1 = r at *
  have hr1 : 1 ≤ r := by omega
  have hsub : subKey m j (r - 1) < subKey m j r := by omega
  by_cases hs : (j / 3) % 2 = 0
  · have hj6 : j % 6 = j % 3 := by omega
    by_cases hc0 : j % 3 = 0
    · rw [hj6, hc0] at hx hy
      simp [isTreeJ] at hx hy
      omega
    · by_cases hc1 : j % 3 = 1
      · exact Or.inl ⟨by omega, hr1⟩
      · have hc2 : j % 3 = 2 := by omega
        rw [hj6, hc2] at hx hy
        simp [isTreeJ] at hx hy
        omega
  · have hj6 : j % 6 = j % 3 + 3 := by omega
    by_cases hr1e : r = 1
    · subst hr1e
      rw [show (1 : ℕ) - 1 = 0 from rfl, subKey_odd_zero hs, subKey_odd_one hs] at hsub
      by_cases hc0 : j % 3 = 0
      · exact Or.inr (Or.inl ⟨by omega, rfl⟩)
      · rw [ite_eq_right hc0] at hsub
        have hmod : j % 3 < 3 := Nat.mod_lt _ (by omega)
        omega
    · have hr2 : 2 ≤ r := by omega
      by_cases hc1 : j % 3 = 1
      · exact Or.inr (Or.inr ⟨by omega, hr2⟩)
      · by_cases hc0 : j % 3 = 0
        · rw [hj6, hc0] at hx hy
          simp [isTreeJ] at hx hy
          omega
        · have hc2 : j % 3 = 2 := by omega
          rw [hj6, hc2] at hx hy
          simp [isTreeJ] at hx hy
          omega

/-- If the tree cell `y` directly left of the tree cell `x` has smaller key, then the
pattern column and row of `x` satisfy one of six mutually exclusive signatures. -/
theorem rule_left {m : ℕ} (_hm : 2 ≤ m) (x y : Cell m)
    (hx : isTree m x = true) (hy : isTree m y = true)
    (hrow : y.1.1 = x.1.1) (hcol : y.2.1 + 1 = x.2.1)
    (hyk : keyFn m y < keyFn m x) :
    (x.2.1 + pOffset m) % 6 = 0 ∧ x.1.1 = 0 ∨
      (x.2.1 + pOffset m) % 6 = 3 ∧ x.1.1 = 0 ∨
        (x.2.1 + pOffset m) % 6 = 1 ∧ x.1.1 = 0 ∨
          (x.2.1 + pOffset m) % 6 = 2 ∨
            (x.2.1 + pOffset m) % 6 = 4 ∧ x.1.1 = 1 ∨
              (x.2.1 + pOffset m) % 6 = 5 ∧ 1 ≤ x.1.1 := by
  rw [keyFn_tree_eq x hx, keyFn_tree_eq y hy] at hyk
  rw [hrow] at hyk
  unfold isTree at hx hy
  rw [hrow] at hy
  generalize hjd : x.2.1 + pOffset m = j at *
  generalize hjyd : y.2.1 + pOffset m = jy at *
  generalize hrd : x.1.1 = r at *
  have hjj : jy + 1 = j := by omega
  by_cases hc0 : j % 3 = 0
  · by_cases hs : (j / 3) % 2 = 0
    · have hj6 : j % 6 = 0 := by omega
      have hjy6 : jy % 6 = 5 := by omega
      rw [hj6] at hx
      rw [hjy6] at hy
      simp [isTreeJ] at hx hy
      exact Or.inl ⟨hj6, by omega⟩
    · have hj6 : j % 6 = 3 := by omega
      have hjy6 : jy % 6 = 2 := by omega
      rw [hj6] at hx
      rw [hjy6] at hy
      simp [isTreeJ] at hx hy
      exact Or.inr (Or.inl ⟨hj6, by omega⟩)
  · by_cases hc1 : j % 3 = 1
    · have hsd : jy / 3 = j / 3 := by omega
      rw [hsd] at hyk
      have hsub : subKey m jy r < subKey m j r := by omega
      have hjy3 : jy % 3 = 0 := by omega
      by_cases hs : (j / 3) % 2 = 0
      · have hsye : (jy / 3) % 2 = 0 := by omega
        by_cases hr : r = 0
        · subst hr
          have hj6 : j % 6 = 1 := by omega
          exact Or.inr (Or.inr (Or.inl ⟨hj6, rfl⟩))
        · have hr1 : 1 ≤ r := by omega
          rw [subKey_even_pos hsye hr1, subKey_even_pos hs hr1] at hsub
          rw [hjy3, hc1, cspos_zero, cspos_one] at hsub
          omega
      · have hsye : ¬ (jy / 3) % 2 = 0 := by omega
        by_cases hr : r = 0
        · subst hr
          have hj6 : j % 6 = 4 := by omega
          rw [hj6] at hx
          simp [isTreeJ] at hx
        · by_cases hr1 : r = 1
          · subst hr1
            have hj6 : j % 6 = 4 := by omega
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hj6, rfl⟩))))
          · have hr2 : 2 ≤ r := by omega
            rw [subKey_odd_ge2 hsye hr2, subKey_odd_ge2 hs hr2] at hsub
            rw [hjy3, hc1, cspos_zero, cspos_one] at hsub
            omega
    · have hc2 : j % 3 = 2 := by omega
      have hsd : jy / 3 = j / 3 := by omega
      rw [hsd] at hyk
      have hsub : subKey m jy r < subKey m j r := by omega
      have hjy3 : jy % 3 = 1 := by omega
      by_cases hs : (j / 3) % 2 = 0
      · have hj6 : j % 6 = 2 := by omega
        exact Or.inr (Or.inr (Or.inr (Or.inl hj6)))
      · have hsye : ¬ (jy / 3) % 2 = 0 := by omega
        by_cases hr : r = 0
        · subst hr
          rw [subKey_odd_zero hsye, subKey_odd_zero hs] at hsub
          rw [hjy3, hc2] at hsub
          simp at hsub
        · have hr1 : 1 ≤ r := by omega
          have hj6 : j % 6 = 5 := by omega
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hj6, hr1⟩))))

/-- If the tree cell `y` directly right of the tree cell `x` has smaller key, then `x`
has pattern column `0` (mod 6) and row at least `2`, or pattern column `3` and row at
least `3`. -/
theorem rule_right {m : ℕ} (hm : 2 ≤ m) (x y : Cell m)
    (hx : isTree m x = true) (hy : isTree m y = true)
    (hrow : y.1.1 = x.1.1) (hcol : y.2.1 = x.2.1 + 1)
    (hyk : keyFn m y < keyFn m x) :
    (x.2.1 + pOffset m) % 6 = 0 ∧ 2 ≤ x.1.1 ∨
      (x.2.1 + pOffset m) % 6 = 3 ∧ 3 ≤ x.1.1 := by
  rw [keyFn_tree_eq x hx, keyFn_tree_eq y hy] at hyk
  rw [hrow] at hyk
  have hrm : x.1.1 < m := x.1.2
  unfold isTree at hx hy
  rw [hrow] at hy
  generalize hjd : x.2.1 + pOffset m = j at *
  generalize hjyd : y.2.1 + pOffset m = jy at *
  generalize hrd : x.1.1 = r at *
  have hjj : jy = j + 1 := by omega
  by_cases hc0 : j % 3 = 0
  · have hsd : jy / 3 = j / 3 := by omega
    rw [hsd] at hyk
    have hsub : subKey m jy r < subKey m j r := by omega
    have hjy3 : jy % 3 = 1 := by omega
    by_cases hs : (j / 3) % 2 = 0
    · have hsye : (jy / 3) % 2 = 0 := by omega
      by_cases hr : r = 0
      · subst hr
        rw [subKey_even_zero hsye, subKey_even_zero hs] at hsub
        rw [hjy3, hc0] at hsub
        omega
      · have hr1 : 1 ≤ r := by omega
        have hj6 : j % 6 = 0 := by omega
        rw [hj6] at hx
        simp [isTreeJ] at hx
        exact Or.inl ⟨hj6, by omega⟩
    · have hsye : ¬ (jy / 3) % 2 = 0 := by omega
      by_cases hr : r = 0
      · subst hr
        rw [subKey_odd_zero hsye, subKey_odd_zero hs] at hsub
        rw [hjy3, hc0] at hsub
        simp at hsub
      · by_cases hr1 : r = 1
        · subst hr1
          rw [subKey_odd_one hsye, subKey_odd_one hs] at hsub
          rw [hjy3, hc0] at hsub
          omega
        · have hr2 : 2 ≤ r := by omega
          have hj6 : j % 6 = 3 := by omega
          rw [hj6] at hx
          simp [isTreeJ] at hx
          exact Or.inr ⟨hj6, by omega⟩
  · by_cases hc1 : j % 3 = 1
    · have hsd : jy / 3 = j / 3 := by omega
      rw [hsd] at hyk
      have hsub : subKey m jy r < subKey m j r := by omega
      have hjy3 : jy % 3 = 2 := by omega
      by_cases hs : (j / 3) % 2 = 0
      · have hsye : (jy / 3) % 2 = 0 := by omega
        by_cases hr : r = 0
        · subst hr
          rw [subKey_even_zero hsye, subKey_even_zero hs] at hsub
          rw [hjy3, hc1] at hsub
          omega
        · have hr1 : 1 ≤ r := by omega
          rw [subKey_even_pos hsye hr1, subKey_even_pos hs hr1] at hsub
          rw [hjy3, hc1, cspos_two, cspos_one] at hsub
          omega
      · have hsye : ¬ (jy / 3) % 2 = 0 := by omega
        by_cases hr : r = 0
        · subst hr
          rw [subKey_odd_zero hsye, subKey_odd_zero hs] at hsub
          rw [hjy3, hc1] at hsub
          simp at hsub
        · by_cases hr1 : r = 1
          · subst hr1
            rw [subKey_odd_one hsye, subKey_odd_one hs] at hsub
            rw [hjy3, hc1] at hsub
            omega
          · have hr2 : 2 ≤ r := by omega
            rw [subKey_odd_ge2 hsye hr2, subKey_odd_ge2 hs hr2] at hsub
            rw [hjy3, hc1, cspos_two, cspos_one] at hsub
            omega
    · have hc2 : j % 3 = 2 := by omega
      have hsd : jy / 3 = j / 3 + 1 := by omega
      have hB : 3 * m * (jy / 3) = 3 * m * (j / 3) + 3 * m := by
        rw [hsd]
        ring
      have hsublt : subKey m j r < 3 * m := subKey_lt (j := j) hrm hm
      omega

/-- Two adjacent cells differ by one in exactly one coordinate. -/

theorem adjacent_dir {n : ℕ} {x y : Cell n} (h : Adjacent x y) :
    (x.1.1 = y.1.1 ∧ x.2.1 = y.2.1 + 1) ∨ (x.1.1 = y.1.1 ∧ y.2.1 = x.2.1 + 1) ∨
      (x.2.1 = y.2.1 ∧ x.1.1 = y.1.1 + 1) ∨ (x.2.1 = y.2.1 ∧ y.1.1 = x.1.1 + 1) := by
  have hd := h.dist
  omega


theorem smaller_neighbor_unique {m : ℕ} (hm : 2 ≤ m) (x y z : Cell m)
    (hx : isTree m x = true) (hy : isTree m y = true) (hz : isTree m z = true)
    (hxy : Adjacent x y) (hxz : Adjacent x z)
    (hyk : keyFn m y < keyFn m x) (hzk : keyFn m z < keyFn m x) : y = z := by
  have dirY := adjacent_dir hxy
  have dirZ := adjacent_dir hxz
  rcases dirY with ⟨hyr, hyc⟩ | ⟨hyr, hyc⟩ | ⟨hyc, hyr⟩ | ⟨hyc, hyr⟩ <;>
    rcases dirZ with ⟨hzr, hzc⟩ | ⟨hzr, hzc⟩ | ⟨hzc, hzr⟩ | ⟨hzc, hzr⟩
  · exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
  · exfalso
    have s1 := rule_left hm x y hx hy hyr.symm hyc.symm hyk
    have s2 := rule_right hm x z hx hz hzr.symm hzc hzk
    omega
  · exfalso
    have s1 := rule_left hm x y hx hy hyr.symm hyc.symm hyk
    have s2 := rule_up hm x z hx hz hzc.symm hzr.symm hzk
    omega
  · exfalso
    have s1 := rule_left hm x y hx hy hyr.symm hyc.symm hyk
    have s2 := rule_down hm x z hx hz hzc.symm hzr hzk
    omega
  · exfalso
    have s1 := rule_right hm x y hx hy hyr.symm hyc hyk
    have s2 := rule_left hm x z hx hz hzr.symm hzc.symm hzk
    omega
  · exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
  · exfalso
    have s1 := rule_right hm x y hx hy hyr.symm hyc hyk
    have s2 := rule_up hm x z hx hz hzc.symm hzr.symm hzk
    omega
  · exfalso
    have s1 := rule_right hm x y hx hy hyr.symm hyc hyk
    have s2 := rule_down hm x z hx hz hzc.symm hzr hzk
    omega
  · exfalso
    have s1 := rule_up hm x y hx hy hyc.symm hyr.symm hyk
    have s2 := rule_left hm x z hx hz hzr.symm hzc.symm hzk
    omega
  · exfalso
    have s1 := rule_up hm x y hx hy hyc.symm hyr.symm hyk
    have s2 := rule_right hm x z hx hz hzr.symm hzc hzk
    omega
  · exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
  · exfalso
    have s1 := rule_up hm x y hx hy hyc.symm hyr.symm hyk
    have s2 := rule_down hm x z hx hz hzc.symm hzr hzk
    omega
  · exfalso
    have s1 := rule_down hm x y hx hy hyc.symm hyr hyk
    have s2 := rule_left hm x z hx hz hzr.symm hzc.symm hzk
    omega
  · exfalso
    have s1 := rule_down hm x y hx hy hyc.symm hyr hyk
    have s2 := rule_right hm x z hx hz hzr.symm hzc hzk
    omega
  · exfalso
    have s1 := rule_down hm x y hx hy hyc.symm hyr hyk
    have s2 := rule_up hm x z hx hz hzc.symm hzr.symm hzk
    omega
  · exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

theorem hill_neighbor_tree {m : ℕ} (x y : Cell m)
    (hx : isTree m x = false) (hxy : Adjacent x y) : isTree m y = true := by
  have hd := hxy.dist
  unfold isTree at hx ⊢
  have hcx : (x.2.1 + pOffset m) % 6 < 6 := Nat.mod_lt _ (by norm_num)
  have hcy : (y.2.1 + pOffset m) % 6 < 6 := Nat.mod_lt _ (by norm_num)
  rw [isTreeJ_true_iff hcy]
  have hxt : ¬ isTreeJ ((x.2.1 + pOffset m) % 6) x.1.1 = true := by
    rw [hx]
    exact Bool.false_ne_true
  rw [isTreeJ_true_iff hcx] at hxt
  omega

theorem tree_not_hill {m : ℕ} (hm : 2 ≤ m) (x : Cell m)
    (hx : isTree m x = true) : ∃ y : Cell m, Adjacent x y ∧ keyFn m x < keyFn m y := by
  obtain ⟨a, b⟩ := x
  have ha : a.1 < m := a.2
  have hb : b.1 < m := b.2
  have hoff : pOffset m = 0 ∨ pOffset m = 1 := by
    by_cases h : m % 3 = 1 <;> simp [pOffset, h]
  have hoff1 : pOffset m = 1 ↔ m % 3 = 1 := by
    by_cases h : m % 3 = 1 <;> simp [pOffset, h]
  have hcsp0 : cspos 0 = 1 := by simp [cspos]
  have hcsp1 : cspos 1 = 0 := by simp [cspos]
  have hcsp2 : cspos 2 = 2 := by simp [cspos]
  -- a hill cell has a larger key than the tree cell `x`
  have hill_lt : ∀ y : Cell m, isTree m y = false → keyFn m (a, b) < keyFn m y := by
    exact fun y hy => tree_key_lt_hill hm (a, b) y hx hy
  -- a tree cell in the same strip with a larger subKey has a larger key
  have tree_lt : ∀ y : Cell m, isTree m y = true →
      (y.2.1 + pOffset m) / 3 = (b.1 + pOffset m) / 3 →
      subKey m (b.1 + pOffset m) a.1 < subKey m (y.2.1 + pOffset m) y.1.1 →
      keyFn m (a, b) < keyFn m y := by
    exact fun y hy hs hsk =>
      keyFn_lt_of_same_strip (b.1 + pOffset m) (y.2.1 + pOffset m) hx hy rfl rfl
        hs.symm hsk
  have hx' : isTreeJ ((b.1 + pOffset m) % 6) a.1 = true := hx
  have h6lt : (b.1 + pOffset m) % 6 < 6 := Nat.mod_lt _ (by omega)
  have h6cases : (b.1 + pOffset m) % 6 = 0 ∨ (b.1 + pOffset m) % 6 = 1 ∨
      (b.1 + pOffset m) % 6 = 2 ∨ (b.1 + pOffset m) % 6 = 3 ∨
      (b.1 + pOffset m) % 6 = 4 ∨ (b.1 + pOffset m) % 6 = 5 := by omega
  rcases h6cases with hk | hk | hk | hk | hk | hk
  · -- pattern column 0 (even strip, edge column): tree iff row even
    have hxc : isTreeJ 0 a.1 = true := by rw [hk] at hx'; exact hx'
    simp [isTreeJ] at hxc
    by_cases hr0 : a.1 = 0
    · -- top row: the backbone cell to the right has subKey 1 > 0
      have hb1 : b.1 + 1 < m := by omega
      refine ⟨(⟨0, by omega⟩, ⟨b.1 + 1, hb1⟩), ?_, ?_⟩
      · show Nat.dist a.1 0 + Nat.dist b.1 (b.1 + 1) = 1
        simp only [Nat.dist]
        omega
      · apply tree_lt
        · show isTreeJ ((b.1 + 1 + pOffset m) % 6) 0 = true
          have h6y : (b.1 + 1 + pOffset m) % 6 = 1 := by omega
          rw [h6y]
          simp [isTreeJ]
        · show (b.1 + 1 + pOffset m) / 3 = (b.1 + pOffset m) / 3
          omega
        · show subKey m (b.1 + pOffset m) a.1 < subKey m (b.1 + 1 + pOffset m) 0
          rw [hr0]
          unfold subKey
          have hp : ((b.1 + pOffset m) / 3) % 2 = 0 := by omega
          have hp' : ((b.1 + 1 + pOffset m) / 3) % 2 = 0 := by omega
          simp only [ite_eq_left hp, ite_eq_left hp', ite_true]
          have hJ3 : (b.1 + pOffset m) % 3 = 0 := by omega
          have hJ'3 : (b.1 + 1 + pOffset m) % 3 = 1 := by omega
          rw [hJ3, hJ'3]
          omega
    · -- even row ≥ 2: the cell above is a hill
      refine ⟨(⟨a.1 - 1, by omega⟩, b), ?_, ?_⟩
      · show Nat.dist a.1 (a.1 - 1) + Nat.dist b.1 b.1 = 1
        simp only [Nat.dist]
        omega
      · apply hill_lt
        show isTreeJ ((b.1 + pOffset m) % 6) (a.1 - 1) = false
        rw [hk]
        have hd : ¬ (a.1 - 1) % 2 = 0 := by omega
        simp [isTreeJ, hd]
  · -- pattern column 1 (the backbone): all rows are trees
    by_cases hrm : a.1 + 1 < m
    · -- the cell below has a larger subKey
      refine ⟨(⟨a.1 + 1, hrm⟩, b), ?_, ?_⟩
      · show Nat.dist a.1 (a.1 + 1) + Nat.dist b.1 b.1 = 1
        simp only [Nat.dist]
        omega
      · apply tree_lt
        · show isTreeJ ((b.1 + pOffset m) % 6) (a.1 + 1) = true
          rw [hk]
          simp [isTreeJ]
        · show (b.1 + pOffset m) / 3 = (b.1 + pOffset m) / 3
          rfl
        · show subKey m (b.1 + pOffset m) a.1 < subKey m (b.1 + pOffset m) (a.1 + 1)
          unfold subKey
          have hp : ((b.1 + pOffset m) / 3) % 2 = 0 := by omega
          simp only [ite_eq_left hp]
          have hR' : ¬ a.1 + 1 = 0 := by omega
          have hJ3 : (b.1 + pOffset m) % 3 = 1 := by omega
          by_cases hr0 : a.1 = 0
          · simp only [ite_eq_left hr0, ite_eq_right hR']
            rw [hJ3, hcsp1]
            omega
          · simp only [ite_eq_right hr0, ite_eq_right hR']
            rw [hJ3, hcsp1]
            omega
    · -- bottom row: use a horizontal neighbor
      by_cases hre : a.1 % 2 = 0
      · by_cases hb0 : b.1 = 0
        · -- leftmost column (offset 1): the right neighbor (pattern 2) is a larger tree
          have hoffv : pOffset m = 1 := by omega
          refine ⟨(a, ⟨1, by omega⟩), ?_, ?_⟩
          · show Nat.dist a.1 a.1 + Nat.dist b.1 1 = 1
            simp only [Nat.dist]
            omega
          · apply tree_lt
            · show isTreeJ ((1 + pOffset m) % 6) a.1 = true
              have h6y : (1 + pOffset m) % 6 = 2 := by omega
              rw [h6y]
              simp [isTreeJ, hre]
            · show (1 + pOffset m) / 3 = (b.1 + pOffset m) / 3
              omega
            · show subKey m (b.1 + pOffset m) a.1 < subKey m (1 + pOffset m) a.1
              unfold subKey
              have hp : ((b.1 + pOffset m) / 3) % 2 = 0 := by omega
              have hp' : ((1 + pOffset m) / 3) % 2 = 0 := by omega
              simp only [ite_eq_left hp, ite_eq_left hp']
              have hL0 : ¬ a.1 = 0 := by omega
              simp only [ite_eq_right hL0]
              have hJ3 : (b.1 + pOffset m) % 3 = 1 := by omega
              have hJ'3 : (1 + pOffset m) % 3 = 2 := by omega
              rw [hJ3, hJ'3, hcsp1, hcsp2]
              omega
        · -- the left neighbor (pattern 0) is a tree with a larger subKey
          have hb1 : 1 ≤ b.1 := by omega
          refine ⟨(a, ⟨b.1 - 1, by omega⟩), ?_, ?_⟩
          · show Nat.dist a.1 a.1 + Nat.dist b.1 (b.1 - 1) = 1
            simp only [Nat.dist]
            omega
          · apply tree_lt
            · show isTreeJ ((b.1 - 1 + pOffset m) % 6) a.1 = true
              have h6y : (b.1 - 1 + pOffset m) % 6 = 0 := by omega
              rw [h6y]
              simp [isTreeJ, hre]
            · show (b.1 - 1 + pOffset m) / 3 = (b.1 + pOffset m) / 3
              omega
            · show subKey m (b.1 + pOffset m) a.1 < subKey m (b.1 - 1 + pOffset m) a.1
              unfold subKey
              have hp : ((b.1 + pOffset m) / 3) % 2 = 0 := by omega
              have hp' : ((b.1 - 1 + pOffset m) / 3) % 2 = 0 := by omega
              simp only [ite_eq_left hp, ite_eq_left hp']
              have hL0 : ¬ a.1 = 0 := by omega
              simp only [ite_eq_right hL0]
              have hJ3 : (b.1 + pOffset m) % 3 = 1 := by omega
              have hJ'3 : (b.1 - 1 + pOffset m) % 3 = 0 := by omega
              rw [hJ3, hJ'3, hcsp1, hcsp0]
              omega
      · -- odd bottom row: a horizontal neighbor is a hill
        have hro : a.1 % 2 = 1 := by omega
        by_cases hb0 : b.1 = 0
        · have hoffv : pOffset m = 1 := by omega
          refine ⟨(a, ⟨1, by omega⟩), ?_, ?_⟩
          · show Nat.dist a.1 a.1 + Nat.dist b.1 1 = 1
            simp only [Nat.dist]
            omega
          · apply hill_lt
            show isTreeJ ((1 + pOffset m) % 6) a.1 = false
            have h6y : (1 + pOffset m) % 6 = 2 := by omega
            rw [h6y]
            have hd : ¬ a.1 % 2 = 0 := by omega
            simp [isTreeJ, hd]
        · have hb1 : 1 ≤ b.1 := by omega
          refine ⟨(a, ⟨b.1 - 1, by omega⟩), ?_, ?_⟩
          · show Nat.dist a.1 a.1 + Nat.dist b.1 (b.1 - 1) = 1
            simp only [Nat.dist]
            omega
          · apply hill_lt
            show isTreeJ ((b.1 - 1 + pOffset m) % 6) a.1 = false
            have h6y : (b.1 - 1 + pOffset m) % 6 = 0 := by omega
            rw [h6y]
            have hd : ¬ a.1 % 2 = 0 := by omega
            simp [isTreeJ, hd]
  · -- pattern column 2 (even strip, edge column): tree iff row even
    have hxc : isTreeJ 2 a.1 = true := by rw [hk] at hx'; exact hx'
    simp [isTreeJ] at hxc
    by_cases hr0 : a.1 = 0
    · -- top row: the cell below is a hill
      refine ⟨(⟨1, by omega⟩, b), ?_, ?_⟩
      · show Nat.dist a.1 1 + Nat.dist b.1 b.1 = 1
        simp only [Nat.dist]
        omega
      · apply hill_lt
        show isTreeJ ((b.1 + pOffset m) % 6) 1 = false
        rw [hk]
        have hd : ¬ (1 : ℕ) % 2 = 0 := by omega
        simp [isTreeJ, hd]
    · -- even row ≥ 2: the cell above is a hill
      refine ⟨(⟨a.1 - 1, by omega⟩, b), ?_, ?_⟩
      · show Nat.dist a.1 (a.1 - 1) + Nat.dist b.1 b.1 = 1
        simp only [Nat.dist]
        omega
      · apply hill_lt
        show isTreeJ ((b.1 + pOffset m) % 6) (a.1 - 1) = false
        rw [hk]
        have hd : ¬ (a.1 - 1) % 2 = 0 := by omega
        simp [isTreeJ, hd]
  · -- pattern column 3 (odd strip, edge column): tree iff row 0 or odd
    have hxc : isTreeJ 3 a.1 = true := by rw [hk] at hx'; exact hx'
    simp [isTreeJ] at hxc
    by_cases hr0 : a.1 = 0
    · -- top row: the cell to the right (pattern 4) is a hill
      have hb1 : b.1 + 1 < m := by omega
      refine ⟨(⟨0, by omega⟩, ⟨b.1 + 1, hb1⟩), ?_, ?_⟩
      · show Nat.dist a.1 0 + Nat.dist b.1 (b.1 + 1) = 1
        simp only [Nat.dist]
        omega
      · apply hill_lt
        show isTreeJ ((b.1 + 1 + pOffset m) % 6) 0 = false
        have h6y : (b.1 + 1 + pOffset m) % 6 = 4 := by omega
        rw [h6y]
        have hd : ¬ (0 : ℕ) ≥ 1 := by omega
        simp [isTreeJ, hd]
    · -- odd row: the cell to the left (pattern 2) is a hill
      have hro : a.1 % 2 = 1 := by omega
      have hb1 : 1 ≤ b.1 := by omega
      refine ⟨(a, ⟨b.1 - 1, by omega⟩), ?_, ?_⟩
      · show Nat.dist a.1 a.1 + Nat.dist b.1 (b.1 - 1) = 1
        simp only [Nat.dist]
        omega
      · apply hill_lt
        show isTreeJ ((b.1 - 1 + pOffset m) % 6) a.1 = false
        have h6y : (b.1 - 1 + pOffset m) % 6 = 2 := by omega
        rw [h6y]
        have hd : ¬ a.1 % 2 = 0 := by omega
        simp [isTreeJ, hd]
  · -- pattern column 4 (odd strip, backbone): tree iff row ≥ 1
    have hxc : isTreeJ 4 a.1 = true := by rw [hk] at hx'; exact hx'
    simp [isTreeJ] at hxc
    by_cases hrm : a.1 + 1 < m
    · -- the cell below has a larger subKey
      refine ⟨(⟨a.1 + 1, hrm⟩, b), ?_, ?_⟩
      · show Nat.dist a.1 (a.1 + 1) + Nat.dist b.1 b.1 = 1
        simp only [Nat.dist]
        omega
      · apply tree_lt
        · show isTreeJ ((b.1 + pOffset m) % 6) (a.1 + 1) = true
          rw [hk]
          have hd : a.1 + 1 ≥ 1 := by omega
          simp [isTreeJ, hd]
        · show (b.1 + pOffset m) / 3 = (b.1 + pOffset m) / 3
          rfl
        · show subKey m (b.1 + pOffset m) a.1 < subKey m (b.1 + pOffset m) (a.1 + 1)
          unfold subKey
          have hp : ¬ ((b.1 + pOffset m) / 3) % 2 = 0 := by omega
          simp only [ite_eq_right hp]
          have hR0' : ¬ a.1 + 1 = 0 := by omega
          have hR1' : ¬ a.1 + 1 = 1 := by omega
          have hJ3 : (b.1 + pOffset m) % 3 = 1 := by omega
          by_cases hr1 : a.1 = 1
          · have hL0 : ¬ a.1 = 0 := by omega
            simp only [ite_eq_right hL0, ite_eq_left hr1, ite_eq_right hR0', ite_eq_right hR1']
            rw [hJ3, hcsp1]
            omega
          · have hL0 : ¬ a.1 = 0 := by omega
            simp only [ite_eq_right hL0, ite_eq_right hr1, ite_eq_right hR0', ite_eq_right hR1']
            rw [hJ3, hcsp1]
            omega
    · -- bottom row: use the left neighbor (pattern 3)
      have hb1 : 1 ≤ b.1 := by omega
      by_cases hre : a.1 % 2 = 0
      · -- even bottom row: the left neighbor is a hill
        refine ⟨(a, ⟨b.1 - 1, by omega⟩), ?_, ?_⟩
        · show Nat.dist a.1 a.1 + Nat.dist b.1 (b.1 - 1) = 1
          simp only [Nat.dist]
          omega
        · apply hill_lt
          show isTreeJ ((b.1 - 1 + pOffset m) % 6) a.1 = false
          have h6y : (b.1 - 1 + pOffset m) % 6 = 3 := by omega
          rw [h6y]
          have hd : ¬ (a.1 % 2 = 1 ∨ a.1 = 0) := by omega
          simp [isTreeJ, hd]
      · -- odd bottom row: the left neighbor is a tree with a larger subKey
        have hro : a.1 % 2 = 1 := by omega
        refine ⟨(a, ⟨b.1 - 1, by omega⟩), ?_, ?_⟩
        · show Nat.dist a.1 a.1 + Nat.dist b.1 (b.1 - 1) = 1
          simp only [Nat.dist]
          omega
        · apply tree_lt
          · show isTreeJ ((b.1 - 1 + pOffset m) % 6) a.1 = true
            have h6y : (b.1 - 1 + pOffset m) % 6 = 3 := by omega
            rw [h6y]
            have hd : a.1 % 2 = 1 ∨ a.1 = 0 := Or.inl hro
            simp [isTreeJ, hd]
          · show (b.1 - 1 + pOffset m) / 3 = (b.1 + pOffset m) / 3
            omega
          · show subKey m (b.1 + pOffset m) a.1 < subKey m (b.1 - 1 + pOffset m) a.1
            unfold subKey
            have hp : ¬ ((b.1 + pOffset m) / 3) % 2 = 0 := by omega
            have hp' : ¬ ((b.1 - 1 + pOffset m) / 3) % 2 = 0 := by omega
            simp only [ite_eq_right hp, ite_eq_right hp']
            have hL0 : ¬ a.1 = 0 := by omega
            have hL1 : ¬ a.1 = 1 := by omega
            simp only [ite_eq_right hL0, ite_eq_right hL1]
            have hJ3 : (b.1 + pOffset m) % 3 = 1 := by omega
            have hJ'3 : (b.1 - 1 + pOffset m) % 3 = 0 := by omega
            rw [hJ3, hJ'3, hcsp1, hcsp0]
            omega
  · -- pattern column 5 (odd strip, edge column): tree iff row 0 or odd
    have hxc : isTreeJ 5 a.1 = true := by rw [hk] at hx'; exact hx'
    simp [isTreeJ] at hxc
    by_cases hr0 : a.1 = 0
    · -- top row: the cell to the left (pattern 4) is a hill
      have hb1 : 1 ≤ b.1 := by omega
      refine ⟨(⟨0, by omega⟩, ⟨b.1 - 1, by omega⟩), ?_, ?_⟩
      · show Nat.dist a.1 0 + Nat.dist b.1 (b.1 - 1) = 1
        simp only [Nat.dist]
        omega
      · apply hill_lt
        show isTreeJ ((b.1 - 1 + pOffset m) % 6) 0 = false
        have h6y : (b.1 - 1 + pOffset m) % 6 = 4 := by omega
        rw [h6y]
        have hd : ¬ (0 : ℕ) ≥ 1 := by omega
        simp [isTreeJ, hd]
    · by_cases hr1 : a.1 = 1
      · -- row 1: the cell above (row 0) has subKey 4 > 3
        refine ⟨(⟨0, by omega⟩, b), ?_, ?_⟩
        · show Nat.dist a.1 0 + Nat.dist b.1 b.1 = 1
          simp only [Nat.dist]
          omega
        · apply tree_lt
          · show isTreeJ ((b.1 + pOffset m) % 6) 0 = true
            rw [hk]
            simp [isTreeJ]
          · show (b.1 + pOffset m) / 3 = (b.1 + pOffset m) / 3
            rfl
          · show subKey m (b.1 + pOffset m) a.1 < subKey m (b.1 + pOffset m) 0
            rw [hr1]
            unfold subKey
            have hp : ¬ ((b.1 + pOffset m) / 3) % 2 = 0 := by omega
            simp only [ite_eq_right hp]
            have hL0 : ¬ (1 : ℕ) = 0 := by omega
            have hJ3 : (b.1 + pOffset m) % 3 = 2 := by omega
            have hJ3ne : ¬ (b.1 + pOffset m) % 3 = 0 := by omega
            simp only [ite_eq_right hL0, ite_eq_right hJ3ne, ite_true]
            rw [hJ3]
            omega
      · -- odd row ≥ 3: the cell above is a hill
        have hro : a.1 % 2 = 1 := by omega
        refine ⟨(⟨a.1 - 1, by omega⟩, b), ?_, ?_⟩
        · show Nat.dist a.1 (a.1 - 1) + Nat.dist b.1 b.1 = 1
          simp only [Nat.dist]
          omega
        · apply hill_lt
          show isTreeJ ((b.1 + pOffset m) % 6) (a.1 - 1) = false
          rw [hk]
          have hd : ¬ ((a.1 - 1) % 2 = 1 ∨ (a.1 - 1) = 0) := by omega
          simp [isTreeJ, hd]

/-- **The construction** (the strip pattern from the official IMO 2022 solution, as drawn
in Evan Chen's IMO 2022 Solution Notes): for every `m ≥ 2` there is a "good" Nordic square
on the `m × m` board (exactly one valley, every non-hill cell has exactly one
smaller-valued neighbor, hills are pairwise non-adjacent), which therefore has exactly
`2 * m * (m - 1) + 1` uphill paths. -/
theorem nordicSquare_good (m : ℕ) (hm : 2 ≤ m) : ∃ ns : NordicSquare m, ns.Good := by
  refine ⟨nsOf hm, ?_⟩
  have hrootT := rootCell_isTree m hm
  have hill_iff : ∀ c : Cell m, (nsOf hm).Hill c ↔ isTree m c = false := by
    intro c
    constructor
    · intro hh
      by_contra hT
      simp only [Bool.not_eq_false] at hT
      obtain ⟨y, hadj, hlt⟩ := tree_not_hill hm c hT
      have h1 := hh y hadj
      rw [nsOf_lt_iff] at h1
      omega
    · intro hT c' hadj
      have hT' := hill_neighbor_tree c c' hT hadj
      rw [nsOf_lt_iff]
      exact tree_key_lt_hill hm c' c hT' hT
  have valley_iff : ∀ c : Cell m, (nsOf hm).Valley c ↔ c = rootCell m hm := by
    intro c
    constructor
    · intro hv
      by_contra hne
      by_cases hT : isTree m c = true
      · obtain ⟨y, hadj, hTy, hlt⟩ := parent_exists hm c hT hne
        have h1 := hv y hadj
        rw [nsOf_lt_iff] at h1
        omega
      · simp only [Bool.not_eq_true] at hT
        obtain ⟨y, hadj⟩ := exists_adjacent (by omega) c
        have hTy := hill_neighbor_tree c y hT hadj
        have h1 := hv y hadj
        rw [nsOf_lt_iff] at h1
        have h2 := tree_key_lt_hill hm y c hTy hT
        omega
    · rintro rfl c' hadj
      rw [nsOf_lt_iff]
      exact rootCell_key_min m hm c' (Ne.symm (Adjacent.ne hadj))
  refine ⟨?_, ?_, ?_⟩
  · -- valley_unique
    exact ⟨rootCell m hm, (valley_iff _).2 rfl, fun y hy ↦ (valley_iff y).1 hy⟩
  · -- one_smaller
    intro c hnv hnh
    have hcT : isTree m c = true := by
      by_contra hF
      simp only [Bool.not_eq_true] at hF
      exact hnh (hill_iff c |>.2 hF)
    have hcne : c ≠ rootCell m hm := by
      intro hce
      exact hnv (valley_iff c |>.2 hce)
    obtain ⟨y, hadj, hTy, hlt⟩ := parent_exists hm c hcT hcne
    refine ⟨y, ⟨hadj, (nsOf_lt_iff hm _ _).2 hlt⟩, fun z hz ↦ ?_⟩
    obtain ⟨hzadj, hzlt⟩ := hz
    have hzT : isTree m z = true := by
      by_contra hF
      simp only [Bool.not_eq_true] at hF
      have hgt := tree_key_lt_hill hm c z hcT hF
      rw [nsOf_lt_iff] at hzlt
      omega
    exact (smaller_neighbor_unique hm c y z hcT hTy hzT hadj hzadj hlt
      ((nsOf_lt_iff hm _ _).1 hzlt)).symm
  · -- hills_independent
    intro h₁ h₂ hh₁ hh₂ hne hadj
    have hF1 := (hill_iff h₁).1 hh₁
    have hF2 := (hill_iff h₂).1 hh₂
    have hT2 := hill_neighbor_tree h₁ h₂ hF1 hadj
    rw [hT2] at hF2
    simp at hF2

snip end

determine answer : ℕ+ → ℕ := fun n ↦ 2 * n.val ^ 2 - 2 * n.val + 1

/-- The answer expressed as `2 * n * (n - 1) + 1`. -/
theorem answer_val (n : ℕ+) : answer n = 2 * (n : ℕ) * ((n : ℕ) - 1) + 1 := by
  have hn : (n : ℕ) = ((n : ℕ) - 1) + 1 := (Nat.sub_add_cancel n.pos).symm
  conv_lhs => rw [answer, hn]
  rw [answer_eq, ← hn, Nat.mul_assoc]

problem imo2022_p6 {n : ℕ+} :
    IsLeast {k : ℕ | ∃ ns : NordicSquare n, #ns.UphillPath = k} (answer n) := by
  constructor
  · by_cases h1 : (n : ℕ) = 1
    · -- the 1×1 board
      have hn1 : n = 1 := Subtype.ext h1
      subst hn1
      rw [show (↑(1 : ℕ+)) = 1 from rfl] at *
      refine ⟨⟨fun _ ↦ ⟨1, by simp⟩, fun _ ↦ (⟨⟨0, by omega⟩, ⟨0, by omega⟩⟩ : Cell 1),
        fun c ↦ by obtain ⟨a, b⟩ := c; simp [Fin.ext_iff],
        fun c ↦ by
          obtain ⟨a, ha⟩ := c
          have h2 : a ≤ 1 := by
            have h := (Finset.mem_Icc.1 ha).2
            simpa using h
          have h1 := (Finset.mem_Icc.1 ha).1
          apply Subtype.ext
          change 1 = a
          omega⟩, ?_⟩
      rw [mk_uphillPath, nat_card_uphillPath_one]
      simp [answer]
    · -- board of side ≥ 2: the strip construction
      obtain ⟨ns, hg⟩ := nordicSquare_good (n : ℕ) (by have := n.pos; omega)
      refine ⟨ns, ?_⟩
      rw [mk_uphillPath, NordicSquare.good_count (by have := n.pos; omega) ns hg, answer_val]
  · intro k hk
    obtain ⟨ns, hns⟩ := hk
    have hb := lower_bound' n.pos ns
    rw [Nat.sub_add_cancel n.pos, hns] at hb
    rw [answer_val]
    exact_mod_cast hb

end Imo2022P6
