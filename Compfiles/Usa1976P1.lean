/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Data.Fin.VecNotation
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 1976, Problem 1

The squares of a 4 x 7 chess board are colored red or blue. Show that however
the coloring is done, we can find a rectangle with four distinct corner
squares all the same color. Find a counter-example to show that this is not
true for a 4 x 6 board.
-/

namespace Usa1976P1

/-- A coloring (true = red, false = blue) of an `m × n` board has a
monochromatic rectangle if there are two distinct rows and two distinct
columns whose four intersection squares all have the same color. -/
def HasMonoRectangle {m n : ℕ} (c : Fin m → Fin n → Bool) : Prop :=
  ∃ r1 r2 : Fin m, ∃ j1 j2 : Fin n, ∃ b : Bool,
    r1 ≠ r2 ∧ j1 ≠ j2 ∧
    c r1 j1 = b ∧ c r2 j1 = b ∧ c r1 j2 = b ∧ c r2 j2 = b

/-- A 4 x 6 coloring with no monochromatic rectangle. Written row by row,
with `true` = red:
```
R B R B R B
R B B R B R
B R R B B R
B R B R R B
```
Every column has two red and two blue squares, and no two columns have their
red squares in the same two rows or their blue squares in the same two rows,
so there can be no monochromatic rectangle. -/
determine counterexample : Fin 4 → Fin 6 → Bool :=
  ![![true,  false, true,  false, true,  false],
    ![true,  false, false, true,  false, true ],
    ![false, true,  true,  false, false, true ],
    ![false, true,  false, true,  true,  false]]

snip begin

/-- The monochromatic pairs of rows in column `j`, tagged with their color:
`(r1, r2, b)` means `r1 < r2` and both squares `(r1, j)` and `(r2, j)` have
color `b`. -/
def monoTriples (c : Fin 4 → Fin 7 → Bool) (j : Fin 7) :
    Finset (Fin 4 × Fin 4 × Bool) :=
  Finset.univ.filter fun t ↦ t.1 < t.2.1 ∧ c t.1 j = t.2.2 ∧ c t.2.1 j = t.2.2

/-- In any column of 4 squares colored with 2 colors, if `k` squares are red
then `4 - k` are blue, so the number of monochromatic pairs of squares is
`k.choose 2 + (4 - k).choose 2 ≥ 1 + 1 = 2`. There are only 16 possible
columns, so we check them all. -/
lemma two_le_card_monoTriples (c : Fin 4 → Fin 7 → Bool) (j : Fin 7) :
    2 ≤ (monoTriples c j).card := by
  have h : ∀ d : Fin 4 → Bool,
      2 ≤ (Finset.univ.filter fun t : Fin 4 × Fin 4 × Bool ↦
        t.1 < t.2.1 ∧ d t.1 = t.2.2 ∧ d t.2.1 = t.2.2).card := by
    decide
  exact h (fun r ↦ c r j)

/-- There are `6` pairs of distinct rows and `2` colors, hence `12` colored
pairs of rows. -/
lemma card_colored_rowPairs :
    (Finset.univ.filter fun t : Fin 4 × Fin 4 × Bool ↦ t.1 < t.2.1).card = 12 := by
  decide

snip end

problem usa1976_p1_first (c : Fin 4 → Fin 7 → Bool) : HasMonoRectangle c := by
  unfold HasMonoRectangle
  by_contra hcon
  -- If there is no monochromatic rectangle, then the sets of monochromatic
  -- colored row-pairs of distinct columns are disjoint.
  have hdisj : ((Finset.univ : Finset (Fin 7)) : Set (Fin 7)).PairwiseDisjoint
      (monoTriples c) := by
    intro j1 _ j2 _ hne
    simp only [Function.onFun, Finset.disjoint_left]
    rintro ⟨r1, r2, b⟩ ht1 ht2
    simp only [monoTriples, Finset.mem_filter, Finset.mem_univ, true_and] at ht1 ht2
    exact hcon ⟨r1, r2, j1, j2, b, ht1.1.ne, hne, ht1.2.1, ht1.2.2, ht2.2.1, ht2.2.2⟩
  -- Every monochromatic colored row-pair is one of the 12 colored pairs of
  -- rows, so the disjoint union of the 7 sets has at most 12 elements.
  have hsub : Finset.univ.biUnion (monoTriples c) ⊆
      Finset.univ.filter (fun t : Fin 4 × Fin 4 × Bool ↦ t.1 < t.2.1) := by
    intro t ht
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at ht
    obtain ⟨j, hj⟩ := ht
    simp only [monoTriples, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact hj.1
  have hle : (Finset.univ.biUnion (monoTriples c)).card ≤ 12 := by
    rw [← card_colored_rowPairs]
    exact Finset.card_le_card hsub
  -- But each of the 7 columns contributes at least 2 monochromatic colored
  -- row-pairs, so the disjoint union has at least 14 elements.
  have hge : 14 ≤ (Finset.univ.biUnion (monoTriples c)).card := by
    rw [Finset.card_biUnion hdisj]
    calc 14 = ∑ _j : Fin 7, (2 : ℕ) := by decide
    _ ≤ ∑ j : Fin 7, (monoTriples c j).card := by
      apply Finset.sum_le_sum
      intro j _
      exact two_le_card_monoTriples c j
  lia

problem usa1976_p1_second : ¬ HasMonoRectangle counterexample := by
  unfold HasMonoRectangle
  decide

end Usa1976P1
