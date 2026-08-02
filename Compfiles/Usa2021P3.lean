/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.RingTheory.SimpleRing.Principal
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2021, Problem 3

Let n ≥ 2 be an integer. An n × n board is initially empty. Each minute, you may
perform one of three moves:

• If there is an L-shaped tromino region of three cells without stones on the
  board (see figure; rotations not allowed), you may place a stone in each of
  those cells.
• If all cells in a column have a stone, you may remove all stones from that
  column.
• If all cells in a row have a stone, you may remove all stones from that row.

For which n is it possible that, after some non-zero number of moves, the board
has no stones?
-/

namespace Usa2021P3

determine answer : ℕ → Prop := fun n ↦ 3 ∣ n

snip begin

/-!
## The game

We model a board position as the set of cells that currently hold a stone.
Cells are indexed by `(row, column)` in `ℕ × ℕ` (rows counted downwards); the
actual board is `{0, ..., n-1} × {0, ..., n-1}`, although the type does not
enforce this.  The L-shaped tromino of the problem statement has the shape

```
X .
X X
```

so with anchor `(i, j)` (the corner cell) it covers `(i, j)`, `(i + 1, j)` and
`(i + 1, j + 1)`.
-/

/-- A board state: the set of cells that currently hold a stone. -/
abbrev Board := Finset (ℕ × ℕ)

/-- The three cells of the L-tromino with anchor `(i, j)`, as in the figure of
the problem statement: `(i, j)`, `(i + 1, j)` and `(i + 1, j + 1)`. -/
def trominoCells (i j : ℕ) : Finset (ℕ × ℕ) := {(i, j), (i + 1, j), (i + 1, j + 1)}

/-- One legal move of the game: either place a stone on each cell of an empty
L-tromino, or clear a full row, or clear a full column. -/
inductive Step (n : ℕ) : Board → Board → Prop
  | tromino {b : Board} {i j : ℕ} (hi : i + 1 < n) (hj : j + 1 < n)
      (h₁ : (i, j) ∉ b) (h₂ : (i + 1, j) ∉ b) (h₃ : (i + 1, j + 1) ∉ b) :
      Step n b (b ∪ trominoCells i j)
  | clearRow {b : Board} (r : ℕ) (hfull : Finset.range n ×ˢ {r} ⊆ b) :
      Step n b (b \ Finset.range n ×ˢ {r})
  | clearCol {b : Board} (c : ℕ) (hfull : {c} ×ˢ Finset.range n ⊆ b) :
      Step n b (b \ {c} ×ˢ Finset.range n)

/-- A sequence of legal moves. -/
inductive Reach (n : ℕ) : Board → Board → Prop
  | refl (b : Board) : Reach n b b
  | tail {b b' b'' : Board} : Reach n b b' → Step n b' b'' → Reach n b b''

/-- The goal of the game: the board can be emptied after a non-zero number of
moves. -/
def Solvable (n : ℕ) : Prop := ∃ b, Step n ∅ b ∧ Reach n b ∅

lemma Reach.trans {n : ℕ} {b b' b'' : Board} (h₁ : Reach n b b') (h₂ : Reach n b' b'') :
    Reach n b b'' := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hstep ih => exact Reach.tail ih hstep

lemma Reach.single {n : ℕ} {b b' : Board} (h : Step n b b') : Reach n b b' :=
  Reach.tail (Reach.refl b) h

/-!
## Counting stones: the cell equations

Suppose the board is emptied by a sequence of moves.  For each cell `(r, c)`,
the number of times the cell gains a stone equals the number of times it loses
one.  If `a i j` counts the tromino placements with anchor `(i, j)`, `ρ r`
counts the clears of column `r` and `γ c` counts the clears of row `c`, then
the gains of cell `(r, c)` are given by `gains a n r c` below, while its losses
are `ρ r + γ c` (a row or column can only be cleared while it is full, so the
cell holds a stone at each of those moments).
-/

/-- `gains a n r c` counts how many times cell `(r, c)` receives a stone, given
that a tromino was placed with anchor `(i, j)` exactly `a i j` times.  The cell
`(r, c)` is covered by the trominoes anchored at `(r, c)`, `(r - 1, c)` and
`(r - 1, c - 1)`. -/
def gains (a : ℕ → ℕ → ℕ) (n r c : ℕ) : ℕ :=
  (if r + 1 < n ∧ c + 1 < n then a r c else 0) +
  (if 1 ≤ r ∧ c + 1 < n then a (r - 1) c else 0) +
  (if 1 ≤ r ∧ 1 ≤ c then a (r - 1) (c - 1) else 0)

/-- Trominoes may only be placed at anchors `(i, j)` with `i + 1 < n` and
`j + 1 < n`; counts at other anchors vanish. -/
def Support (a : ℕ → ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ i j, n ≤ i + 1 ∨ n ≤ j + 1 → a i j = 0

@[simp]
lemma gains_zero (n r c : ℕ) : gains (fun _ _ ↦ 0) n r c = 0 := by
  simp [gains]

lemma gains_add (a₁ a₂ : ℕ → ℕ → ℕ) (n r c : ℕ) :
    gains (fun i j ↦ a₁ i j + a₂ i j) n r c = gains a₁ n r c + gains a₂ n r c := by
  unfold gains
  split_ifs <;> ring

lemma Support.add {a₁ a₂ : ℕ → ℕ → ℕ} {n : ℕ} (h₁ : Support a₁ n) (h₂ : Support a₂ n) :
    Support (fun i j ↦ a₁ i j + a₂ i j) n := by
  intro i j h
  simp [h₁ i j h, h₂ i j h]

/-- The gains coming from a single tromino placed at the legal anchor `(i, j)`
are exactly the indicator function of its three cells. -/
lemma gains_single {n i j : ℕ} (hi : i + 1 < n) (hj : j + 1 < n) (r c : ℕ) :
    gains (fun x y ↦ if x = i ∧ y = j then 1 else 0) n r c =
      if (r, c) ∈ trominoCells i j then 1 else 0 := by
  have t1 : (if r + 1 < n ∧ c + 1 < n then (if r = i ∧ c = j then (1 : ℕ) else 0) else 0) =
      if r = i ∧ c = j then 1 else 0 := by
    by_cases h : r = i ∧ c = j
    · obtain ⟨rfl, rfl⟩ := h; simp [hi, hj]
    · simp [h]
  have t2 : (if 1 ≤ r ∧ c + 1 < n then (if r - 1 = i ∧ c = j then (1 : ℕ) else 0) else 0) =
      if r = i + 1 ∧ c = j then 1 else 0 := by
    by_cases h : r = i + 1 ∧ c = j
    · obtain ⟨rfl, rfl⟩ := h; simp [hj]
    · rw [if_neg h]
      by_cases h2 : 1 ≤ r ∧ c + 1 < n
      · rw [if_pos h2, if_neg]
        rintro ⟨h3, h4⟩
        exact h ⟨by omega, h4⟩
      · rw [if_neg h2]
  have t3 : (if 1 ≤ r ∧ 1 ≤ c then (if r - 1 = i ∧ c - 1 = j then (1 : ℕ) else 0) else 0) =
      if r = i + 1 ∧ c = j + 1 then 1 else 0 := by
    by_cases h : r = i + 1 ∧ c = j + 1
    · obtain ⟨rfl, rfl⟩ := h; simp
    · rw [if_neg h]
      by_cases h2 : 1 ≤ r ∧ 1 ≤ c
      · rw [if_pos h2, if_neg]
        rintro ⟨h3, h4⟩
        exact h ⟨by omega, by omega⟩
      · rw [if_neg h2]
  simp only [gains]
  rw [t1, t2, t3]
  simp only [trominoCells, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  split_ifs <;> omega

/-- A single move, seen through the counting functions: the gains and losses of
every cell can be expressed with suitable counts. -/
lemma extract_step {n : ℕ} {b b' : Board} (h : Step n b b') :
    ∃ (a : ℕ → ℕ → ℕ) (ρ γ : ℕ → ℕ), Support a n ∧ ∀ r c, r < n → c < n →
      gains a n r c + (if (r, c) ∈ b then 1 else 0) =
        ρ r + γ c + (if (r, c) ∈ b' then 1 else 0) := by
  cases h with
  | tromino hi hj h₁ h₂ h₃ =>
    rename_i i j
    refine ⟨fun x y ↦ if x = i ∧ y = j then 1 else 0, fun _ ↦ 0, fun _ ↦ 0, ?_, ?_⟩
    · intro x y hxy
      show (if x = i ∧ y = j then (1 : ℕ) else 0) = 0
      split_ifs with h2
      · obtain ⟨rfl, rfl⟩ := h2
        rcases hxy with h | h <;> omega
      · rfl
    · intro r c hr hc
      rw [gains_single hi hj r c]
      show (if (r, c) ∈ trominoCells i j then (1 : ℕ) else 0) + (if (r, c) ∈ b then 1 else 0) =
        0 + 0 + (if (r, c) ∈ b ∪ trominoCells i j then 1 else 0)
      have hdisj : Disjoint b (trominoCells i j) := by
        rw [Finset.disjoint_right]
        intro c' hc'
        simp only [trominoCells, Finset.mem_insert, Finset.mem_singleton] at hc'
        rcases hc' with rfl | rfl | rfl
        · exact h₁
        · exact h₂
        · exact h₃
      by_cases hb : (r, c) ∈ b
      · rw [if_pos hb, if_neg (Finset.disjoint_left.1 hdisj hb), zero_add,
          if_pos (Finset.mem_union_left _ hb)]
      · rw [if_neg hb]
        by_cases hT : (r, c) ∈ trominoCells i j
        · rw [if_pos hT, if_pos (Finset.mem_union_right _ hT)]
        · rw [if_neg hT, if_neg]
          intro hmem
          rcases Finset.mem_union.1 hmem with h4 | h4
          · exact hb h4
          · exact hT h4
  | clearRow r hfull =>
    refine ⟨fun _ _ ↦ 0, fun _ ↦ 0, fun c ↦ if c = r then 1 else 0, by simp [Support], ?_⟩
    intro r' c hr hc
    simp only [gains_zero, zero_add]
    by_cases hcr : c = r
    · rw [hcr]
      have hmem : (r', r) ∈ Finset.range n ×ˢ {r} := by
        rw [Finset.mem_product]
        exact ⟨Finset.mem_range.2 hr, Finset.mem_singleton_self r⟩
      rw [if_pos rfl, if_pos (hfull hmem), if_neg]
      exact fun h ↦ (Finset.mem_sdiff.1 h).2 hmem
    · rw [if_neg hcr, zero_add]
      by_cases hb : (r', c) ∈ b
      · rw [if_pos hb, if_pos]
        exact Finset.mem_sdiff.2 ⟨hb, fun hmem ↦
          hcr (Finset.mem_singleton.1 (Finset.mem_product.1 hmem).2)⟩
      · rw [if_neg hb, if_neg]
        exact fun h ↦ hb (Finset.mem_sdiff.1 h).1
  | clearCol c hfull =>
    refine ⟨fun _ _ ↦ 0, fun x ↦ if x = c then 1 else 0, fun _ ↦ 0, by simp [Support], ?_⟩
    intro r c' hr hc
    simp only [gains_zero, add_zero, zero_add]
    by_cases hcr : r = c
    · rw [hcr]
      have hmem : (c, c') ∈ {c} ×ˢ Finset.range n := by
        rw [Finset.mem_product]
        exact ⟨Finset.mem_singleton_self c, Finset.mem_range.2 hc⟩
      rw [if_pos rfl, if_pos (hfull hmem), if_neg]
      exact fun h ↦ (Finset.mem_sdiff.1 h).2 hmem
    · rw [if_neg hcr, zero_add]
      by_cases hb : (r, c') ∈ b
      · rw [if_pos hb, if_pos]
        exact Finset.mem_sdiff.2 ⟨hb, fun hmem ↦
          hcr (Finset.mem_singleton.1 (Finset.mem_product.1 hmem).1)⟩
      · rw [if_neg hb, if_neg]
        exact fun h ↦ hb (Finset.mem_sdiff.1 h).1

/-- A whole sequence of moves, seen through the counting functions. -/
lemma extract {n : ℕ} {b b' : Board} (h : Reach n b b') :
    ∃ (a : ℕ → ℕ → ℕ) (ρ γ : ℕ → ℕ), Support a n ∧ ∀ r c, r < n → c < n →
      gains a n r c + (if (r, c) ∈ b then 1 else 0) =
        ρ r + γ c + (if (r, c) ∈ b' then 1 else 0) := by
  induction h with
  | refl =>
    exact ⟨fun _ _ ↦ 0, fun _ ↦ 0, fun _ ↦ 0, by simp [Support], by simp⟩
  | tail hreach hstep ih =>
    obtain ⟨a₁, ρ₁, γ₁, hs₁, he₁⟩ := ih
    obtain ⟨a₂, ρ₂, γ₂, hs₂, he₂⟩ := extract_step hstep
    refine ⟨fun i j ↦ a₁ i j + a₂ i j, fun r ↦ ρ₁ r + ρ₂ r, fun c ↦ γ₁ c + γ₂ c,
      hs₁.add hs₂, ?_⟩
    intro r c hr hc
    have e₁ := he₁ r c hr hc
    have e₂ := he₂ r c hr hc
    rw [gains_add]
    dsimp only
    omega

/-- In particular, a successful game yields the cell equations together with at
least one tromino that was actually placed. -/
lemma extract_solvable {n : ℕ} (hn : 1 ≤ n) (h : Solvable n) :
    ∃ (a : ℕ → ℕ → ℕ) (ρ γ : ℕ → ℕ), Support a n ∧
      (∀ r c, r < n → c < n → gains a n r c = ρ r + γ c) ∧ ∃ i j : ℕ, 1 ≤ a i j := by
  obtain ⟨b, hstep, hreach⟩ := h
  obtain ⟨a₂, ρ₂, γ₂, hs₂, he₂⟩ := extract hreach
  cases hstep with
  | tromino hi hj h₁ h₂ h₃ =>
    rename_i i j
    refine ⟨fun x y ↦ a₂ x y + (if x = i ∧ y = j then 1 else 0), ρ₂, γ₂, ?_, ?_, i, j, ?_⟩
    · apply hs₂.add
      intro x y hxy
      show (if x = i ∧ y = j then (1 : ℕ) else 0) = 0
      split_ifs with h2
      · obtain ⟨rfl, rfl⟩ := h2
        rcases hxy with h | h <;> omega
      · rfl
    · intro r c hr hc
      have e := he₂ r c hr hc
      simp only [Finset.empty_union, Finset.notMem_empty, if_false, add_zero] at e
      rw [gains_add, gains_single hi hj r c]
      exact e
    · simp
  | clearRow r hfull =>
    exfalso
    have hmem : (0, r) ∈ Finset.range n ×ˢ {r} := by
      rw [Finset.mem_product]
      exact ⟨Finset.mem_range.2 (by omega), Finset.mem_singleton_self r⟩
    exact Finset.notMem_empty _ (hfull hmem)
  | clearCol c hfull =>
    exfalso
    have hmem : (c, 0) ∈ {c} ×ˢ Finset.range n := by
      rw [Finset.mem_product]
      exact ⟨Finset.mem_singleton_self c, Finset.mem_range.2 (by omega)⟩
    exact Finset.notMem_empty _ (hfull hmem)

/-!
## The polynomial obstruction

If the board can be emptied, then `3 ∣ n`.  The proof sums the cell equations
against the weights `ζ ^ r * η ^ c`, where `ζ, η` are `n`-th roots of unity
different from `1`: the tromino side factors as `(1 + ζ + ζ * η)` times the
tromino generating function, while the row/column side vanishes.  When `3 ∤ n`
one has `1 + ζ + ζ * η ≠ 0`, so the generating function vanishes on a large
grid of points, which forces every tromino count to be zero — contradicting
that at least one tromino was placed.
-/

/-- Shifting a sum by one, provided the boundary terms vanish. -/
lemma sum_range_shift (f : ℕ → ℂ) (n : ℕ) (hf0 : f 0 = 0) (hfn : f n = 0) :
    ∑ i ∈ Finset.range n, f (i + 1) = ∑ r ∈ Finset.range n, f r := by
  have h1 := Finset.sum_range_succ' f n
  have h2 := Finset.sum_range_succ f n
  rw [hf0, add_zero] at h1
  rw [hfn, add_zero] at h2
  rw [← h1, h2]

/-- The key identity: evaluated at `n`-th roots of unity `ζ, η ≠ 1`, the cell
equations imply that `(1 + ζ + ζ * η)` times the tromino generating function
vanishes. -/
lemma key_identity {n : ℕ} (hn : 2 ≤ n) {a : ℕ → ℕ → ℕ} {ρ γ : ℕ → ℕ}
    (hsupp : Support a n)
    (hcell : ∀ r c, r < n → c < n → gains a n r c = ρ r + γ c)
    {ζ η : ℂ} (hζ : ζ ^ n = 1) (hζ1 : ζ ≠ 1) (hη : η ^ n = 1) (hη1 : η ≠ 1) :
    (1 + ζ + ζ * η) * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      (a i j : ℂ) * ζ ^ i * η ^ j = 0 := by
  have hηsum : ∑ c ∈ Finset.range n, η ^ c = 0 := by
    rw [geom_sum_eq hη1 n, hη, sub_self, zero_div]
  have hζsum : ∑ r ∈ Finset.range n, ζ ^ r = 0 := by
    rw [geom_sum_eq hζ1 n, hζ, sub_self, zero_div]
  have eζ : ζ * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        (a i j : ℂ) * ζ ^ i * η ^ j =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (a i j : ℂ) * ζ ^ (i + 1) * η ^ j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_succ]
    ring
  have eζη : (ζ * η) * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        (a i j : ℂ) * ζ ^ i * η ^ j =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (a i j : ℂ) * ζ ^ (i + 1) * η ^ (j + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_succ, pow_succ]
    ring
  have egains : ∀ r c, (gains a n r c : ℂ) =
      (if r + 1 < n ∧ c + 1 < n then (a r c : ℂ) else 0) +
      (if 1 ≤ r ∧ c + 1 < n then (a (r - 1) c : ℂ) else 0) +
      (if 1 ≤ r ∧ 1 ≤ c then (a (r - 1) (c - 1) : ℂ) else 0) := by
    intro r c
    simp [gains]
  have s1 : ∑ r ∈ Finset.range n, ∑ c ∈ Finset.range n, (a r c : ℂ) * ζ ^ r * η ^ c =
      ∑ r ∈ Finset.range n, ∑ c ∈ Finset.range n,
        (if r + 1 < n ∧ c + 1 < n then (a r c : ℂ) else 0) * ζ ^ r * η ^ c := by
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro c _
    by_cases hcond : r + 1 < n ∧ c + 1 < n
    · rw [if_pos hcond]
    · rw [if_neg hcond, zero_mul, zero_mul]
      have hz : a r c = 0 := hsupp r c (by omega)
      simp [hz]
  have s2 : ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (a i j : ℂ) * ζ ^ (i + 1) * η ^ j =
      ∑ r ∈ Finset.range n, ∑ c ∈ Finset.range n,
        (if 1 ≤ r ∧ c + 1 < n then (a (r - 1) c : ℂ) else 0) * ζ ^ r * η ^ c := by
    have hfn : (fun r ↦ if r = 0 then (0 : ℂ)
        else ∑ j ∈ Finset.range n, (a (r - 1) j : ℂ) * ζ ^ r * η ^ j) n = 0 := by
      show (if n = 0 then (0 : ℂ)
        else ∑ j ∈ Finset.range n, (a (n - 1) j : ℂ) * ζ ^ n * η ^ j) = 0
      by_cases hn0 : n = 0
      · rw [if_pos hn0]
      · rw [if_neg hn0]
        apply Finset.sum_eq_zero
        intro j _
        have hz : a (n - 1) j = 0 := hsupp _ _ (Or.inl (by omega))
        simp [hz]
    have hshift := sum_range_shift
      (fun r ↦ if r = 0 then (0 : ℂ)
        else ∑ j ∈ Finset.range n, (a (r - 1) j : ℂ) * ζ ^ r * η ^ j) n (by simp) hfn
    have e1 : ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (a i j : ℂ) * ζ ^ (i + 1) * η ^ j =
        ∑ i ∈ Finset.range n, (fun r ↦ if r = 0 then (0 : ℂ)
          else ∑ j ∈ Finset.range n, (a (r - 1) j : ℂ) * ζ ^ r * η ^ j) (i + 1) := by
      apply Finset.sum_congr rfl
      intro i _
      simp
    rw [e1, hshift]
    apply Finset.sum_congr rfl
    intro r _
    by_cases hr0 : r = 0
    · subst hr0
      simp
    · rw [if_neg hr0]
      apply Finset.sum_congr rfl
      intro c _
      by_cases hcond : c + 1 < n
      · rw [if_pos ⟨by omega, hcond⟩]
      · rw [if_neg (by omega : ¬(1 ≤ r ∧ c + 1 < n)), zero_mul, zero_mul]
        have hz : a (r - 1) c = 0 := hsupp _ _ (Or.inr (by omega))
        simp [hz]
  have s3 : ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        (a i j : ℂ) * ζ ^ (i + 1) * η ^ (j + 1) =
      ∑ r ∈ Finset.range n, ∑ c ∈ Finset.range n,
        (if 1 ≤ r ∧ 1 ≤ c then (a (r - 1) (c - 1) : ℂ) else 0) * ζ ^ r * η ^ c := by
    have inner : ∀ i : ℕ, ∑ j ∈ Finset.range n, (a i j : ℂ) * ζ ^ (i + 1) * η ^ (j + 1) =
        ∑ c ∈ Finset.range n, (if 1 ≤ c then (a i (c - 1) : ℂ) * ζ ^ (i + 1) * η ^ c
          else 0) := by
      intro i
      have hfn : (fun c ↦ if c = 0 then (0 : ℂ)
          else (a i (c - 1) : ℂ) * ζ ^ (i + 1) * η ^ c) n = 0 := by
        show (if n = 0 then (0 : ℂ) else (a i (n - 1) : ℂ) * ζ ^ (i + 1) * η ^ n) = 0
        by_cases hn0 : n = 0
        · rw [if_pos hn0]
        · rw [if_neg hn0]
          have hz : a i (n - 1) = 0 := hsupp _ _ (Or.inr (by omega))
          simp [hz]
      have hshift := sum_range_shift
        (fun c ↦ if c = 0 then (0 : ℂ) else (a i (c - 1) : ℂ) * ζ ^ (i + 1) * η ^ c) n
        (by simp) hfn
      have e1 : ∑ j ∈ Finset.range n, (a i j : ℂ) * ζ ^ (i + 1) * η ^ (j + 1) =
          ∑ j ∈ Finset.range n, (fun c ↦ if c = 0 then (0 : ℂ)
            else (a i (c - 1) : ℂ) * ζ ^ (i + 1) * η ^ c) (j + 1) := by
        apply Finset.sum_congr rfl
        intro j _
        simp
      rw [e1, hshift]
      apply Finset.sum_congr rfl
      intro c _
      by_cases hc0 : c = 0
      · subst hc0
        simp
      · rw [if_neg hc0, if_pos (by omega : 1 ≤ c)]
    have outer : ∑ i ∈ Finset.range n, ∑ c ∈ Finset.range n,
          (if 1 ≤ c then (a i (c - 1) : ℂ) * ζ ^ (i + 1) * η ^ c else 0) =
        ∑ r ∈ Finset.range n, ∑ c ∈ Finset.range n,
          (if 1 ≤ r ∧ 1 ≤ c then (a (r - 1) (c - 1) : ℂ) else 0) * ζ ^ r * η ^ c := by
      have hf0 : (fun r ↦ ∑ c ∈ Finset.range n,
            (if 1 ≤ c then (if r = 0 then (0 : ℂ) else (a (r - 1) (c - 1) : ℂ)) * ζ ^ r * η ^ c
              else 0)) 0 = 0 := by
        simp
      have hfn : (fun r ↦ ∑ c ∈ Finset.range n,
            (if 1 ≤ c then (if r = 0 then (0 : ℂ) else (a (r - 1) (c - 1) : ℂ)) * ζ ^ r * η ^ c
              else 0)) n = 0 := by
        show ∑ c ∈ Finset.range n,
          (if 1 ≤ c then (if n = 0 then (0 : ℂ) else (a (n - 1) (c - 1) : ℂ)) * ζ ^ n * η ^ c
            else 0) = 0
        apply Finset.sum_eq_zero
        intro c _
        by_cases hc : 1 ≤ c
        · rw [if_pos hc]
          have hn0 : n ≠ 0 := by omega
          rw [if_neg hn0]
          have hz : a (n - 1) (c - 1) = 0 := hsupp _ _ (Or.inl (by omega))
          simp [hz]
        · rw [if_neg hc]
      have hshift := sum_range_shift
        (fun r ↦ ∑ c ∈ Finset.range n,
          (if 1 ≤ c then (if r = 0 then (0 : ℂ) else (a (r - 1) (c - 1) : ℂ)) * ζ ^ r * η ^ c
            else 0)) n hf0 hfn
      have e1 : ∑ i ∈ Finset.range n, ∑ c ∈ Finset.range n,
            (if 1 ≤ c then (a i (c - 1) : ℂ) * ζ ^ (i + 1) * η ^ c else 0) =
          ∑ i ∈ Finset.range n, (fun r ↦ ∑ c ∈ Finset.range n,
            (if 1 ≤ c then (if r = 0 then (0 : ℂ) else (a (r - 1) (c - 1) : ℂ)) * ζ ^ r * η ^ c
              else 0)) (i + 1) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro c _
        by_cases hc : 1 ≤ c
        · rw [if_pos hc, if_pos hc, if_neg (by omega : i + 1 ≠ 0), Nat.add_sub_cancel]
        · rw [if_neg hc, if_neg hc]
      rw [e1, hshift]
      apply Finset.sum_congr rfl
      intro r _
      by_cases hr0 : r = 0
      · subst hr0
        simp
      · apply Finset.sum_congr rfl
        intro c _
        by_cases hc : 1 ≤ c
        · rw [if_pos hc, if_neg hr0, if_pos ⟨by omega, hc⟩]
        · rw [if_neg hc, if_neg (by omega : ¬(1 ≤ r ∧ 1 ≤ c)), zero_mul, zero_mul]
    calc ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (a i j : ℂ) * ζ ^ (i + 1) * η ^ (j + 1)
        = ∑ i ∈ Finset.range n, ∑ c ∈ Finset.range n,
            (if 1 ≤ c then (a i (c - 1) : ℂ) * ζ ^ (i + 1) * η ^ c else 0) :=
          Finset.sum_congr rfl fun i _ ↦ inner i
      _ = ∑ r ∈ Finset.range n, ∑ c ∈ Finset.range n,
            (if 1 ≤ r ∧ 1 ≤ c then (a (r - 1) (c - 1) : ℂ) else 0) * ζ ^ r * η ^ c := outer
  have hfin : ∑ r ∈ Finset.range n, ∑ c ∈ Finset.range n,
        (gains a n r c : ℂ) * ζ ^ r * η ^ c =
      (∑ r ∈ Finset.range n, ∑ c ∈ Finset.range n,
          (if r + 1 < n ∧ c + 1 < n then (a r c : ℂ) else 0) * ζ ^ r * η ^ c +
        ∑ r ∈ Finset.range n, ∑ c ∈ Finset.range n,
          (if 1 ≤ r ∧ c + 1 < n then (a (r - 1) c : ℂ) else 0) * ζ ^ r * η ^ c) +
      ∑ r ∈ Finset.range n, ∑ c ∈ Finset.range n,
        (if 1 ≤ r ∧ 1 ≤ c then (a (r - 1) (c - 1) : ℂ) else 0) * ζ ^ r * η ^ c := by
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro c _
    rw [egains r c]
    ring
  have hside : ∑ r ∈ Finset.range n, ∑ c ∈ Finset.range n,
        (gains a n r c : ℂ) * ζ ^ r * η ^ c = 0 := by
    have e2 : ∑ r ∈ Finset.range n, ∑ c ∈ Finset.range n,
          (gains a n r c : ℂ) * ζ ^ r * η ^ c =
        ∑ r ∈ Finset.range n, ∑ c ∈ Finset.range n,
          ((ρ r : ℂ) + γ c) * ζ ^ r * η ^ c := by
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro c hc
      rw [hcell r c (Finset.mem_range.1 hr) (Finset.mem_range.1 hc), Nat.cast_add]
    have t1 : ∑ r ∈ Finset.range n, ∑ c ∈ Finset.range n, (ρ r : ℂ) * ζ ^ r * η ^ c =
        (∑ r ∈ Finset.range n, (ρ r : ℂ) * ζ ^ r) * ∑ c ∈ Finset.range n, η ^ c := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.mul_sum]
    have t2 : ∑ r ∈ Finset.range n, ∑ c ∈ Finset.range n, (γ c : ℂ) * ζ ^ r * η ^ c =
        (∑ c ∈ Finset.range n, (γ c : ℂ) * η ^ c) * ∑ r ∈ Finset.range n, ζ ^ r := by
      rw [Finset.sum_comm, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring
    rw [e2]
    simp only [add_mul, Finset.sum_add_distrib]
    rw [t1, t2, hηsum, hζsum, mul_zero, mul_zero, add_zero]
  rw [add_mul, add_mul, one_mul, eζ, eζη, s1, s2, s3, ← hfin]
  exact hside

/-- If `3 ∤ n` and `ζ, η` are `n`-th roots of unity with `ζ ≠ 1`, then
`1 + ζ + ζ * η ≠ 0`. -/
lemma one_add_ne_zero {n : ℕ} (hn : 2 ≤ n) (h3 : ¬ 3 ∣ n) {ζ η : ℂ}
    (hζ : ζ ^ n = 1) (hζ1 : ζ ≠ 1) (hη : η ^ n = 1) :
    1 + ζ + ζ * η ≠ 0 := by
  intro h
  have hn0 : n ≠ 0 := by omega
  have hζ0 : ζ ≠ 0 := by
    intro h0
    rw [h0] at hζ
    simp [hn0] at hζ
  have ns_pow : ∀ (z : ℂ) (k : ℕ), Complex.normSq (z ^ k) = (Complex.normSq z) ^ k := by
    intro z k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, Complex.normSq_mul, ih, pow_succ]
  have ns1 : Complex.normSq ζ = 1 := by
    have h1 : (Complex.normSq ζ) ^ n = 1 := by
      rw [← ns_pow, hζ]
      exact Complex.normSq_one
    exact (pow_eq_one_iff_of_nonneg (Complex.normSq_nonneg _) hn0).1 h1
  have ns2 : Complex.normSq η = 1 := by
    have h1 : (Complex.normSq η) ^ n = 1 := by
      rw [← ns_pow, hη]
      exact Complex.normSq_one
    exact (pow_eq_one_iff_of_nonneg (Complex.normSq_nonneg _) hn0).1 h1
  have hmul : ζ * η = -1 - ζ := by linear_combination h
  have hns : Complex.normSq (1 + ζ) = 1 := by
    have h1 : Complex.normSq (ζ * η) = 1 := by
      rw [Complex.normSq_mul, ns1, ns2, mul_one]
    rw [hmul, show (-1 : ℂ) - ζ = -(1 + ζ) by ring, Complex.normSq_neg] at h1
    exact h1
  have hre : ζ.re = -1 / 2 := by
    have e := Complex.normSq_add 1 ζ
    rw [Complex.normSq_one, ns1, one_mul, Complex.conj_re, hns] at e
    linarith
  have hconj : (starRingEnd ℂ) ζ = -1 - ζ := by
    have e := Complex.add_conj ζ
    have hre2 : (2 : ℝ) * ζ.re = -1 := by rw [hre]; norm_num
    rw [hre2] at e
    have e3 : (starRingEnd ℂ) ζ = (-1 : ℝ) - ζ := by linear_combination e
    rw [e3]
    norm_cast
  have hquad : ζ ^ 2 + ζ + 1 = 0 := by
    have e := Complex.mul_conj ζ
    rw [hconj, ns1, Complex.ofReal_one] at e
    linear_combination -e
  have hcub : ζ ^ 3 = 1 := by
    have e : ζ ^ 3 = (ζ - 1) * (ζ ^ 2 + ζ + 1) + 1 := by ring
    rw [hquad, mul_zero, zero_add] at e
    exact e
  have hu3 : (Units.mk0 ζ hζ0) ^ 3 = 1 := by
    apply Units.ext
    show ζ ^ 3 = 1
    exact hcub
  have hun : (Units.mk0 ζ hζ0) ^ n = 1 := by
    apply Units.ext
    show ζ ^ n = 1
    exact hζ
  have hdg := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hu3) (orderOf_dvd_of_pow_eq_one hun)
  have hgcd : Nat.gcd 3 n = 1 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3).gcd_eq_one
  rw [hgcd, Nat.dvd_one] at hdg
  have hu1 : Units.mk0 ζ hζ0 = 1 := orderOf_eq_one_iff.1 hdg
  have hζeq : ζ = 1 := by
    have hv := congrArg Units.val hu1
    show (Units.mk0 ζ hζ0 : ℂˣ).val = 1
    exact hv
  exact hζ1 hζeq

/-- A polynomial of degree `< m` with coefficients coming from the tromino
counts vanishes on the `m` points of the grid, hence is zero.  Applied twice,
this shows that all tromino counts vanish. -/
lemma count_eq_zero {n : ℕ} (hn : 2 ≤ n) {a : ℕ → ℕ → ℕ}
    (hsupp : Support a n)
    (hP : ∀ ζ η : ℂ, ζ ^ n = 1 → ζ ≠ 1 → η ^ n = 1 → η ≠ 1 →
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (a i j : ℂ) * ζ ^ i * η ^ j = 0) :
    ∀ i j, a i j = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / (↑(m + 1) : ℂ)) with hωdef
  have hω : IsPrimitiveRoot ω (m + 1) := by
    rw [hωdef]
    exact Complex.isPrimitiveRoot_exp (m + 1) (Nat.succ_ne_zero m)
  have hωn : ω ^ (m + 1) = 1 := hω.pow_eq_one
  set S : Finset ℂ := (Finset.range m).image (fun k ↦ ω ^ (k + 1)) with hSdef
  have hinj : Set.InjOn (fun k ↦ ω ^ (k + 1)) ↑(Finset.range m) := by
    intro x hx y hy hxy
    simp only [Finset.coe_range, Set.mem_Iio] at hx hy
    simp only at hxy
    have h1 : x + 1 < m + 1 := by omega
    have h2 : y + 1 < m + 1 := by omega
    have h3 := hω.pow_inj h1 h2 hxy
    omega
  have hScard : S.card = m := by
    rw [hSdef]
    exact (Finset.card_image_iff.2 hinj).trans (Finset.card_range m)
  have hSmem : ∀ z ∈ S, z ^ (m + 1) = 1 ∧ z ≠ 1 := by
    intro z hz
    rw [hSdef, Finset.mem_image] at hz
    obtain ⟨k, hk, rfl⟩ := hz
    rw [Finset.mem_range] at hk
    constructor
    · show (ω ^ (k + 1)) ^ (m + 1) = 1
      rw [← pow_mul, Nat.mul_comm, pow_mul, hωn, one_pow]
    · show ω ^ (k + 1) ≠ 1
      intro h1
      rw [hω.pow_eq_one_iff_dvd] at h1
      have h2 := Nat.le_of_dvd (by omega) h1
      omega
  have hcut : ∀ ζ η : ℂ,
      ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
          (a i j : ℂ) * ζ ^ i * η ^ j =
      ∑ i ∈ Finset.range m, (∑ j ∈ Finset.range m, (a i j : ℂ) * η ^ j) * ζ ^ i := by
    intro ζ η
    rw [Finset.sum_range_succ]
    have hzero : ∑ j ∈ Finset.range (m + 1), (a m j : ℂ) * ζ ^ m * η ^ j = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      have hz : a m j = 0 := hsupp _ _ (Or.inl (by omega))
      simp [hz]
    rw [hzero, add_zero]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_range_succ]
    have hzero2 : (a i m : ℂ) * ζ ^ i * η ^ m = 0 := by
      have hz : a i m = 0 := hsupp _ _ (Or.inr (by omega))
      simp [hz]
    rw [hzero2, add_zero, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  -- stage A: for each `η ∈ S`, the polynomial in `X` with coefficients
  -- `∑ j, a i j * η ^ j` vanishes on `S`, hence is zero.
  have stageA : ∀ η ∈ S, ∀ i, i < m → ∑ j ∈ Finset.range m, (a i j : ℂ) * η ^ j = 0 := by
    intro η hη
    set F : Polynomial ℂ := ∑ i ∈ Finset.range m,
      Polynomial.C (∑ j ∈ Finset.range m, (a i j : ℂ) * η ^ j) * Polynomial.X ^ i with hFdef
    have heval : ∀ z ∈ S, F.eval z = 0 := by
      intro z hz
      obtain ⟨hzn, hz1⟩ := hSmem z hz
      obtain ⟨hηn, hη1⟩ := hSmem η hη
      rw [hFdef, Polynomial.eval_finsetSum]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      rw [← hcut z η]
      exact hP z η hzn hz1 hηn hη1
    have hdeg : F.natDegree ≤ m - 1 := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro i hi
      rw [Finset.mem_range] at hi
      exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)
    have hF0 : F = 0 :=
      Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' F S heval (by rw [hScard]; omega)
    intro i hi
    have hc : F.coeff i = 0 := by rw [hF0]; simp
    rw [hFdef, Polynomial.finsetSum_coeff] at hc
    simp only [Polynomial.coeff_C_mul_X_pow] at hc
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.2 hi)] at hc
    exact hc
  intro i j
  by_cases hij : i < m ∧ j < m
  · -- stage B: for each `i < m`, the polynomial `∑ j, a i j * X ^ j` vanishes
    -- on `S`, hence is zero, so `a i j = 0`.
    obtain ⟨hi, hj⟩ := hij
    set Q : Polynomial ℂ := ∑ j ∈ Finset.range m, Polynomial.C (a i j : ℂ) * Polynomial.X ^ j with hQdef
    have heval : ∀ z ∈ S, Q.eval z = 0 := by
      intro z hz
      rw [hQdef, Polynomial.eval_finsetSum]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      exact stageA z hz i hi
    have hdeg : Q.natDegree ≤ m - 1 := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro j' hj'
      rw [Finset.mem_range] at hj'
      exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)
    have hQ0 : Q = 0 :=
      Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' Q S heval (by rw [hScard]; omega)
    have hc : Q.coeff j = 0 := by rw [hQ0]; simp
    rw [hQdef, Polynomial.finsetSum_coeff] at hc
    simp only [Polynomial.coeff_C_mul_X_pow] at hc
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.2 hj)] at hc
    exact Nat.cast_eq_zero.1 hc
  · exact hsupp i j (by omega)

/-- The obstruction: the board cannot be emptied when `3 ∤ n`. -/
lemma not_solvable_of_not_three_dvd {n : ℕ} (hn : 2 ≤ n) (h3 : ¬ 3 ∣ n) (h : Solvable n) :
    False := by
  obtain ⟨a, ρ, γ, hsupp, hcell, i₀, j₀, hpos⟩ := extract_solvable (by omega) h
  have hP : ∀ ζ η : ℂ, ζ ^ n = 1 → ζ ≠ 1 → η ^ n = 1 → η ≠ 1 →
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (a i j : ℂ) * ζ ^ i * η ^ j = 0 := by
    intro ζ η hζ hζ1 hη hη1
    have hid := key_identity hn hsupp hcell hζ hζ1 hη hη1
    rcases mul_eq_zero.1 hid with hzero | hzero
    · exact absurd hzero (one_add_ne_zero hn h3 hζ hζ1 hη)
    · exact hzero
  have hzero := count_eq_zero hn hsupp hP
  have h00 := hzero i₀ j₀
  omega

/-!
## The construction for `3 ∣ n`

When `3 ∣ n` the task is possible.  Write `n = 3k` and partition the board
into `3 × 3` blocks.  The same strategy is played simultaneously in every
block.  For `k = 1` it is the six-move solution

```
A = {(0,1),(1,1),(1,2)},   B = {(1,0),(2,0),(2,1)},   clear column 1,
C = {(0,0),(1,0),(1,1)},   clear rows 0 and 1.
```

In general: place all `A`-trominoes and all `B`-trominoes (one per block);
then every column whose index is `≡ 1 (mod 3)` is completely filled and can be
cleared; then place all `C`-trominoes; now every row whose index is
`≢ 2 (mod 3)` is completely filled and can be cleared, leaving the board
empty.
-/

/-- Placing trominoes at a finset of anchors, one at a time: if every anchor is
legal, the trominoes are pairwise disjoint, and all their cells are currently
empty, then all of them can be placed in succession. -/
lemma reach_place {n : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ × ℕ) :
    ∀ b : Board,
    (∀ i ∈ s, (f i).1 + 1 < n ∧ (f i).2 + 1 < n) →
    (∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (trominoCells (f i).1 (f i).2) (trominoCells (f j).1 (f j).2)) →
    (∀ i ∈ s, ∀ c ∈ trominoCells (f i).1 (f i).2, c ∉ b) →
    Reach n b (b ∪ s.biUnion (fun i ↦ trominoCells (f i).1 (f i).2)) := by
  induction s using Finset.induction with
  | empty =>
    intro b _ _ _
    rw [Finset.biUnion_empty, Finset.union_empty]
    exact Reach.refl b
  | @insert x s hx ih =>
    intro b hleg hdisj hfresh
    rw [Finset.biUnion_insert]
    have hstep : Step n b (b ∪ trominoCells (f x).1 (f x).2) := by
      obtain ⟨h1, h2⟩ := hleg x (Finset.mem_insert_self x s)
      refine Step.tromino h1 h2 ?_ ?_ ?_
      · exact hfresh x (Finset.mem_insert_self x s) _ (by simp [trominoCells])
      · exact hfresh x (Finset.mem_insert_self x s) _ (by simp [trominoCells])
      · exact hfresh x (Finset.mem_insert_self x s) _ (by simp [trominoCells])
    refine Reach.trans (Reach.single hstep) ?_
    rw [← Finset.union_assoc]
    exact ih (b ∪ trominoCells (f x).1 (f x).2)
      (fun i hi ↦ hleg i (Finset.mem_insert_of_mem hi))
      (fun i hi j hj hij ↦ hdisj i (Finset.mem_insert_of_mem hi) j
        (Finset.mem_insert_of_mem hj) hij)
      (fun i hi c hc ↦ by
        have hix : i ≠ x := fun h ↦ hx (h ▸ hi)
        have hd := hdisj i (Finset.mem_insert_of_mem hi) x (Finset.mem_insert_self x s) hix
        exact fun hmem ↦ (Finset.mem_union.1 hmem).elim
          (hfresh i (Finset.mem_insert_of_mem hi) c hc)
          (Finset.disjoint_left.1 hd hc))

/-- Clearing full rows, one at a time. -/
lemma reach_clearRows {n : ℕ} (s : Finset ℕ) :
    ∀ b : Board, (∀ r ∈ s, Finset.range n ×ˢ {r} ⊆ b) →
      Reach n b (b \ (Finset.range n ×ˢ s)) := by
  induction s using Finset.induction with
  | empty =>
    intro b _
    rw [Finset.product_empty, Finset.sdiff_empty]
    exact Reach.refl b
  | @insert r s hr ih =>
    intro b hfull
    have hstep : Step n b (b \ Finset.range n ×ˢ {r}) :=
      Step.clearRow r (hfull r (Finset.mem_insert_self r s))
    refine Reach.trans (Reach.single hstep) ?_
    have hprod : Finset.range n ×ˢ (insert r s : Finset ℕ) =
        (Finset.range n ×ˢ {r}) ∪ (Finset.range n ×ˢ s) := by
      ext ⟨x, y⟩
      simp only [Finset.mem_product, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]
      tauto
    rw [hprod]
    have hsd : (b \ Finset.range n ×ˢ {r}) \ (Finset.range n ×ˢ s) =
        b \ ((Finset.range n ×ˢ {r}) ∪ (Finset.range n ×ˢ s)) := by
      ext ⟨x, y⟩
      simp only [Finset.mem_sdiff, Finset.mem_union]
      tauto
    rw [← hsd]
    exact ih (b \ Finset.range n ×ˢ {r}) (fun r' hr' x hx ↦ by
      rw [Finset.mem_sdiff]
      refine ⟨hfull r' (Finset.mem_insert_of_mem hr') hx, fun hxA ↦ ?_⟩
      have h1 := Finset.mem_singleton.1 (Finset.mem_product.1 hxA).2
      have h2 := Finset.mem_singleton.1 (Finset.mem_product.1 hx).2
      have hrr : r = r' := h1.symm.trans h2
      exact hr (hrr.symm ▸ hr'))

/-- Clearing full columns, one at a time. -/
lemma reach_clearCols {n : ℕ} (s : Finset ℕ) :
    ∀ b : Board, (∀ c ∈ s, {c} ×ˢ Finset.range n ⊆ b) →
      Reach n b (b \ (s ×ˢ Finset.range n)) := by
  induction s using Finset.induction with
  | empty =>
    intro b _
    rw [Finset.empty_product, Finset.sdiff_empty]
    exact Reach.refl b
  | @insert c s hc ih =>
    intro b hfull
    have hstep : Step n b (b \ {c} ×ˢ Finset.range n) :=
      Step.clearCol c (hfull c (Finset.mem_insert_self c s))
    refine Reach.trans (Reach.single hstep) ?_
    have hprod : (insert c s : Finset ℕ) ×ˢ Finset.range n =
        ({c} ×ˢ Finset.range n) ∪ (s ×ˢ Finset.range n) := by
      ext ⟨x, y⟩
      simp only [Finset.mem_product, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]
      tauto
    rw [hprod]
    have hsd : (b \ {c} ×ˢ Finset.range n) \ (s ×ˢ Finset.range n) =
        b \ (({c} ×ˢ Finset.range n) ∪ (s ×ˢ Finset.range n)) := by
      ext ⟨x, y⟩
      simp only [Finset.mem_sdiff, Finset.mem_union]
      tauto
    rw [← hsd]
    exact ih (b \ {c} ×ˢ Finset.range n) (fun c' hc' x hx ↦ by
      rw [Finset.mem_sdiff]
      refine ⟨hfull c' (Finset.mem_insert_of_mem hc') hx, fun hxA ↦ ?_⟩
      have h1 := Finset.mem_singleton.1 (Finset.mem_product.1 hxA).1
      have h2 := Finset.mem_singleton.1 (Finset.mem_product.1 hx).1
      have hcc : c = c' := h1.symm.trans h2
      exact hc (hcc.symm ▸ hc'))

/-- The construction: the board can be emptied whenever `3 ∣ n`. -/
lemma solvable_of_three_dvd {n : ℕ} (hn : 2 ≤ n) (h3 : 3 ∣ n) : Solvable n := by
  obtain ⟨k, rfl⟩ := h3
  have hk : 1 ≤ k := by omega
  set idx : Finset (ℕ × ℕ) := Finset.range k ×ˢ Finset.range k with hidx
  have mem_idx : ∀ p : ℕ × ℕ, p ∈ idx ↔ p.1 < k ∧ p.2 < k := by
    intro p
    rw [hidx, Finset.mem_product, Finset.mem_range, Finset.mem_range]
  set B1 : Board := idx.biUnion (fun p ↦ trominoCells (3 * p.1) (3 * p.2 + 1)) with hB1
  set B2 : Board := B1 ∪ idx.biUnion (fun p ↦ trominoCells (3 * p.1 + 1) (3 * p.2)) with hB2
  set Cols : Finset ℕ := (Finset.range k).image (fun t ↦ 3 * t + 1) with hCols
  set B3 : Board := B2 \ (Cols ×ˢ Finset.range (3 * k)) with hB3
  set B4 : Board := B3 ∪ idx.biUnion (fun p ↦ trominoCells (3 * p.1) (3 * p.2)) with hB4
  set Rows0 : Finset ℕ := (Finset.range k).image (fun s ↦ 3 * s) with hRows0
  set Rows1 : Finset ℕ := (Finset.range k).image (fun s ↦ 3 * s + 1) with hRows1
  set B5 : Board := B4 \ (Finset.range (3 * k) ×ˢ Rows0) with hB5
  set B6 : Board := B5 \ (Finset.range (3 * k) ×ˢ Rows1) with hB6
  have disjAA : ∀ p ∈ idx, ∀ q ∈ idx, p ≠ q →
      Disjoint (trominoCells (3 * p.1) (3 * p.2 + 1))
        (trominoCells (3 * q.1) (3 * q.2 + 1)) := by
    intro p hp q hq hpq
    rw [mem_idx] at hp hq
    have hpq' : p.1 ≠ q.1 ∨ p.2 ≠ q.2 := not_and_or.1 (fun h ↦ hpq (Prod.ext_iff.2 h))
    rw [Finset.disjoint_left]
    intro c hc
    simp only [trominoCells, Finset.mem_insert, Finset.mem_singleton] at hc ⊢
    rcases hc with rfl | rfl | rfl <;> rintro (h | h | h) <;> simp only [Prod.mk.injEq] at h <;>
      omega
  have disjBB : ∀ p ∈ idx, ∀ q ∈ idx, p ≠ q →
      Disjoint (trominoCells (3 * p.1 + 1) (3 * p.2))
        (trominoCells (3 * q.1 + 1) (3 * q.2)) := by
    intro p hp q hq hpq
    rw [mem_idx] at hp hq
    have hpq' : p.1 ≠ q.1 ∨ p.2 ≠ q.2 := not_and_or.1 (fun h ↦ hpq (Prod.ext_iff.2 h))
    rw [Finset.disjoint_left]
    intro c hc
    simp only [trominoCells, Finset.mem_insert, Finset.mem_singleton] at hc ⊢
    rcases hc with rfl | rfl | rfl <;> rintro (h | h | h) <;> simp only [Prod.mk.injEq] at h <;>
      omega
  have disjCC : ∀ p ∈ idx, ∀ q ∈ idx, p ≠ q →
      Disjoint (trominoCells (3 * p.1) (3 * p.2))
        (trominoCells (3 * q.1) (3 * q.2)) := by
    intro p hp q hq hpq
    rw [mem_idx] at hp hq
    have hpq' : p.1 ≠ q.1 ∨ p.2 ≠ q.2 := not_and_or.1 (fun h ↦ hpq (Prod.ext_iff.2 h))
    rw [Finset.disjoint_left]
    intro c hc
    simp only [trominoCells, Finset.mem_insert, Finset.mem_singleton] at hc ⊢
    rcases hc with rfl | rfl | rfl <;> rintro (h | h | h) <;> simp only [Prod.mk.injEq] at h <;>
      omega
  have freshB : ∀ p ∈ idx, ∀ c ∈ trominoCells (3 * p.1 + 1) (3 * p.2), c ∉ B1 := by
    intro p hp c hc h
    rw [mem_idx] at hp
    rw [hB1, Finset.mem_biUnion] at h
    obtain ⟨q, hq, hq2⟩ := h
    rw [mem_idx] at hq
    simp only [trominoCells, Finset.mem_insert, Finset.mem_singleton] at hc hq2
    rcases hc with rfl | rfl | rfl <;> rcases hq2 with h | h | h <;>
      simp only [Prod.mk.injEq] at h <;> omega
  have freshC : ∀ p ∈ idx, ∀ c ∈ trominoCells (3 * p.1) (3 * p.2), c ∉ B3 := by
    intro p hp c hc h
    rw [mem_idx] at hp
    rw [hB3, Finset.mem_sdiff] at h
    obtain ⟨hcB2, hcD⟩ := h
    simp only [trominoCells, Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl
    · rw [hB2, Finset.mem_union] at hcB2
      rcases hcB2 with hcB2 | hcB2
      · rw [hB1, Finset.mem_biUnion] at hcB2
        obtain ⟨q, hq, hq2⟩ := hcB2
        rw [mem_idx] at hq
        simp only [trominoCells, Finset.mem_insert, Finset.mem_singleton] at hq2
        rcases hq2 with h | h | h <;> simp only [Prod.mk.injEq] at h <;> omega
      · rw [Finset.mem_biUnion] at hcB2
        obtain ⟨q, hq, hq2⟩ := hcB2
        rw [mem_idx] at hq
        simp only [trominoCells, Finset.mem_insert, Finset.mem_singleton] at hq2
        rcases hq2 with h | h | h <;> simp only [Prod.mk.injEq] at h <;> omega
    · exact hcD (Finset.mem_product.2 ⟨by
          rw [hCols, Finset.mem_image]
          exact ⟨p.1, Finset.mem_range.2 hp.1, rfl⟩, Finset.mem_range.2 (by omega)⟩)
    · exact hcD (Finset.mem_product.2 ⟨by
          rw [hCols, Finset.mem_image]
          exact ⟨p.1, Finset.mem_range.2 hp.1, rfl⟩, Finset.mem_range.2 (by omega)⟩)
  have fullCols : ∀ c ∈ Cols, {c} ×ˢ Finset.range (3 * k) ⊆ B2 := by
    intro c hc x hx
    rw [hCols, Finset.mem_image] at hc
    obtain ⟨t, ht, rfl⟩ := hc
    rw [Finset.mem_range] at ht
    rw [Finset.mem_product, Finset.mem_singleton] at hx
    obtain ⟨hxc, hy⟩ := hx
    have hylt : x.2 < 3 * k := Finset.mem_range.1 hy
    have hx1 : x.1 = 3 * t + 1 := hxc
    set s := x.2 / 3 with hs
    set m := x.2 % 3 with hm
    have hsk : s < k := by omega
    have hx2 : x = (3 * t + 1, 3 * s + m) := by
      have h2 : x.2 = 3 * s + m := by omega
      exact Prod.ext_iff.2 ⟨hx1, h2⟩
    rw [hx2]
    rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2) with h | h | h <;> rw [h]
    · rw [hB2]
      apply Finset.mem_union_right
      rw [Finset.mem_biUnion]
      exact ⟨(t, s), (mem_idx _).2 ⟨ht, hsk⟩, by simp [trominoCells]⟩
    · rw [hB2]
      apply Finset.mem_union_left
      rw [hB1, Finset.mem_biUnion]
      exact ⟨(t, s), (mem_idx _).2 ⟨ht, hsk⟩, by simp [trominoCells]⟩
    · rw [hB2]
      apply Finset.mem_union_left
      rw [hB1, Finset.mem_biUnion]
      exact ⟨(t, s), (mem_idx _).2 ⟨ht, hsk⟩, by simp [trominoCells]⟩
  have fullRows0 : ∀ r ∈ Rows0, Finset.range (3 * k) ×ˢ {r} ⊆ B4 := by
    intro r hr x hx
    rw [hRows0, Finset.mem_image] at hr
    obtain ⟨s, hs, rfl⟩ := hr
    rw [Finset.mem_range] at hs
    rw [Finset.mem_product, Finset.mem_singleton] at hx
    obtain ⟨hxr, hr2⟩ := hx
    have h1 : x.2 = 3 * s := hr2
    have hxlt : x.1 < 3 * k := Finset.mem_range.1 hxr
    set t := x.1 / 3 with ht
    set m := x.1 % 3 with hm
    have htk : t < k := by omega
    have hx2 : x = (3 * t + m, 3 * s) := by
      have h2 : x.1 = 3 * t + m := by omega
      exact Prod.ext_iff.2 ⟨h2, h1⟩
    rw [hx2]
    rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2) with h | h | h <;> rw [h]
    · rw [hB4]
      apply Finset.mem_union_right
      rw [Finset.mem_biUnion]
      exact ⟨(t, s), (mem_idx _).2 ⟨htk, hs⟩, by simp [trominoCells]⟩
    · rw [hB4]
      apply Finset.mem_union_right
      rw [Finset.mem_biUnion]
      exact ⟨(t, s), (mem_idx _).2 ⟨htk, hs⟩, by simp [trominoCells]⟩
    · rw [hB4]
      apply Finset.mem_union_left
      rw [hB3, Finset.mem_sdiff]
      refine ⟨?_, ?_⟩
      · rw [hB2]
        apply Finset.mem_union_right
        rw [Finset.mem_biUnion]
        exact ⟨(t, s), (mem_idx _).2 ⟨htk, hs⟩, by simp [trominoCells]⟩
      · rw [Finset.mem_product]
        rintro ⟨h1, -⟩
        have h1' : 3 * t + 2 ∈ Cols := h1
        rw [hCols, Finset.mem_image] at h1'
        obtain ⟨t', ht', hteq⟩ := h1'
        rw [Finset.mem_range] at ht'
        omega
  have fullRows1 : ∀ r ∈ Rows1, Finset.range (3 * k) ×ˢ {r} ⊆ B5 := by
    intro r hr x hx
    rw [hRows1, Finset.mem_image] at hr
    obtain ⟨s, hs, rfl⟩ := hr
    rw [Finset.mem_range] at hs
    rw [Finset.mem_product, Finset.mem_singleton] at hx
    obtain ⟨hxr, hr2⟩ := hx
    have h1 : x.2 = 3 * s + 1 := hr2
    have hxlt : x.1 < 3 * k := Finset.mem_range.1 hxr
    set t := x.1 / 3 with ht
    set m := x.1 % 3 with hm
    have htk : t < k := by omega
    have hx2 : x = (3 * t + m, 3 * s + 1) := by
      have h2 : x.1 = 3 * t + m := by omega
      exact Prod.ext_iff.2 ⟨h2, h1⟩
    rw [hx2]
    rw [hB5, Finset.mem_sdiff]
    refine ⟨?_, ?_⟩
    · rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2) with h | h | h <;> rw [h]
      · rw [hB4]
        apply Finset.mem_union_left
        rw [hB3, Finset.mem_sdiff]
        refine ⟨?_, ?_⟩
        · rw [hB2]
          apply Finset.mem_union_left
          rw [hB1, Finset.mem_biUnion]
          exact ⟨(t, s), (mem_idx _).2 ⟨htk, hs⟩, by simp [trominoCells]⟩
        · rw [Finset.mem_product]
          rintro ⟨h1, -⟩
          have h1' : 3 * t + 0 ∈ Cols := h1
          rw [hCols, Finset.mem_image] at h1'
          obtain ⟨t', ht', hteq⟩ := h1'
          rw [Finset.mem_range] at ht'
          omega
      · rw [hB4]
        apply Finset.mem_union_right
        rw [Finset.mem_biUnion]
        exact ⟨(t, s), (mem_idx _).2 ⟨htk, hs⟩, by simp [trominoCells]⟩
      · rw [hB4]
        apply Finset.mem_union_left
        rw [hB3, Finset.mem_sdiff]
        refine ⟨?_, ?_⟩
        · rw [hB2]
          apply Finset.mem_union_right
          rw [Finset.mem_biUnion]
          exact ⟨(t, s), (mem_idx _).2 ⟨htk, hs⟩, by simp [trominoCells]⟩
        · rw [Finset.mem_product]
          rintro ⟨h1, -⟩
          have h1' : 3 * t + 2 ∈ Cols := h1
          rw [hCols, Finset.mem_image] at h1'
          obtain ⟨t', ht', hteq⟩ := h1'
          rw [Finset.mem_range] at ht'
          omega
    · rw [Finset.mem_product]
      rintro ⟨-, h1'⟩
      have h1'' : 3 * s + 1 ∈ Rows0 := h1'
      rw [hRows0, Finset.mem_image] at h1''
      obtain ⟨s', hs', hseq⟩ := h1''
      omega
  have hB6empty : B6 = ∅ := by
    have cell_check : ∀ c : ℕ × ℕ, c ∈ B4 → c.1 < 3 * k ∧ (c.2 ∈ Rows0 ∨ c.2 ∈ Rows1) := by
      intro c hc
      rw [hB4, Finset.mem_union] at hc
      rcases hc with hc | hc
      · rw [hB3, Finset.mem_sdiff] at hc
        obtain ⟨hcB2, hcD⟩ := hc
        rw [hB2, Finset.mem_union] at hcB2
        rcases hcB2 with hcB2 | hcB2
        · rw [hB1, Finset.mem_biUnion] at hcB2
          obtain ⟨q, hq, hq2⟩ := hcB2
          rw [mem_idx] at hq
          simp only [trominoCells, Finset.mem_insert, Finset.mem_singleton] at hq2
          rcases hq2 with h | h | h
          · subst h
            refine ⟨by omega, Or.inr ?_⟩
            rw [hRows1, Finset.mem_image]
            exact ⟨q.2, Finset.mem_range.2 hq.2, rfl⟩
          · subst h
            exfalso
            apply hcD
            rw [Finset.mem_product]
            refine ⟨?_, Finset.mem_range.2 (by omega)⟩
            rw [hCols, Finset.mem_image]
            exact ⟨q.1, Finset.mem_range.2 hq.1, rfl⟩
          · subst h
            exfalso
            apply hcD
            rw [Finset.mem_product]
            refine ⟨?_, Finset.mem_range.2 (by omega)⟩
            rw [hCols, Finset.mem_image]
            exact ⟨q.1, Finset.mem_range.2 hq.1, rfl⟩
        · rw [Finset.mem_biUnion] at hcB2
          obtain ⟨q, hq, hq2⟩ := hcB2
          rw [mem_idx] at hq
          simp only [trominoCells, Finset.mem_insert, Finset.mem_singleton] at hq2
          rcases hq2 with h | h | h
          · subst h
            exfalso
            apply hcD
            rw [Finset.mem_product]
            refine ⟨?_, Finset.mem_range.2 (by omega)⟩
            rw [hCols, Finset.mem_image]
            exact ⟨q.1, Finset.mem_range.2 hq.1, rfl⟩
          · subst h
            refine ⟨by omega, Or.inl ?_⟩
            rw [hRows0, Finset.mem_image]
            exact ⟨q.2, Finset.mem_range.2 hq.2, rfl⟩
          · subst h
            refine ⟨by omega, Or.inr ?_⟩
            rw [hRows1, Finset.mem_image]
            exact ⟨q.2, Finset.mem_range.2 hq.2, rfl⟩
      · rw [Finset.mem_biUnion] at hc
        obtain ⟨q, hq, hq2⟩ := hc
        rw [mem_idx] at hq
        simp only [trominoCells, Finset.mem_insert, Finset.mem_singleton] at hq2
        rcases hq2 with h | h | h
        · subst h
          refine ⟨by omega, Or.inl ?_⟩
          rw [hRows0, Finset.mem_image]
          exact ⟨q.2, Finset.mem_range.2 hq.2, rfl⟩
        · subst h
          refine ⟨by omega, Or.inl ?_⟩
          rw [hRows0, Finset.mem_image]
          exact ⟨q.2, Finset.mem_range.2 hq.2, rfl⟩
        · subst h
          refine ⟨by omega, Or.inr ?_⟩
          rw [hRows1, Finset.mem_image]
          exact ⟨q.2, Finset.mem_range.2 hq.2, rfl⟩
    rw [hB6, hB5]
    apply Finset.eq_empty_iff_forall_notMem.2
    intro c hc
    rw [Finset.mem_sdiff, Finset.mem_sdiff] at hc
    obtain ⟨⟨hcB4, hc0⟩, hc1⟩ := hc
    obtain ⟨hx, hy⟩ := cell_check c hcB4
    rcases hy with hy | hy
    · exact hc0 (Finset.mem_product.2 ⟨Finset.mem_range.2 hx, hy⟩)
    · exact hc1 (Finset.mem_product.2 ⟨Finset.mem_range.2 hx, hy⟩)
  -- now run the six phases
  have hstep0 : Step (3 * k) ∅ (∅ ∪ trominoCells 0 1) := by
    apply Step.tromino (by omega) (by omega) <;> simp
  refine ⟨∅ ∪ trominoCells 0 1, hstep0, ?_⟩
  have r1 : Reach (3 * k) (∅ ∪ trominoCells 0 1) B1 := by
    have hmem : (0, 0) ∈ idx := by
      rw [hidx, Finset.mem_product]
      exact ⟨Finset.mem_range.2 hk, Finset.mem_range.2 hk⟩
    have hB1' : B1 = trominoCells 0 1 ∪
        (idx.erase (0, 0)).biUnion (fun p ↦ trominoCells (3 * p.1) (3 * p.2 + 1)) := by
      rw [hB1, ← Finset.insert_erase hmem, Finset.biUnion_insert]
      simp
    rw [hB1']
    have hr := reach_place (n := 3 * k) (idx.erase (0, 0)) (fun p ↦ (3 * p.1, 3 * p.2 + 1))
      (∅ ∪ trominoCells 0 1) ?_ ?_ ?_
    · rw [Finset.empty_union] at hr
      exact hr
    · intro p hp
      rw [Finset.mem_erase] at hp
      rw [mem_idx] at hp
      exact ⟨by omega, by omega⟩
    · intro p hp q hq hpq
      rw [Finset.mem_erase] at hp hq
      exact disjAA p hp.2 q hq.2 hpq
    · intro p hp c hc
      rw [Finset.mem_erase] at hp
      obtain ⟨hpne, hpmem⟩ := hp
      intro hmem2
      rcases Finset.mem_union.1 hmem2 with h | h
      · exact Finset.notMem_empty _ h
      · have hd := disjAA p hpmem (0, 0) hmem hpne
        have h' : c ∈ trominoCells (3 * (0, 0).1) (3 * (0, 0).2 + 1) := h
        exact (Finset.disjoint_right.1 hd h') hc
  have r2 : Reach (3 * k) B1 B2 := by
    rw [hB2]
    apply reach_place idx (fun p ↦ (3 * p.1 + 1, 3 * p.2)) B1
    · intro p hp
      rw [mem_idx] at hp
      exact ⟨by omega, by omega⟩
    · intro p hp q hq hpq
      exact disjBB p hp q hq hpq
    · exact freshB
  have r3 : Reach (3 * k) B2 B3 := by
    rw [hB3]
    exact reach_clearCols Cols B2 fullCols
  have r4 : Reach (3 * k) B3 B4 := by
    rw [hB4]
    apply reach_place idx (fun p ↦ (3 * p.1, 3 * p.2)) B3
    · intro p hp
      rw [mem_idx] at hp
      exact ⟨by omega, by omega⟩
    · intro p hp q hq hpq
      exact disjCC p hp q hq hpq
    · exact freshC
  have r5 : Reach (3 * k) B4 B5 := by
    rw [hB5]
    exact reach_clearRows Rows0 B4 fullRows0
  have r6 : Reach (3 * k) B5 B6 := by
    rw [hB6]
    exact reach_clearRows Rows1 B5 fullRows1
  rw [hB6empty] at r6
  exact ((((r1.trans r2).trans r3).trans r4).trans r5).trans r6


snip end

/-- USAMO 2021 Problem 3: the board can be emptied after a non-zero number of
moves if and only if `3 ∣ n`. -/
problem usa2021_p3 (n : ℕ) (hn : 2 ≤ n) : Solvable n ↔ answer n := by
  constructor
  · intro h
    by_contra h3
    exact not_solvable_of_not_three_dvd hn h3 h
  · intro h
    exact solvable_of_three_dvd hn h

end Usa2021P3
