/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Abel
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Combinatorics]
}

/-!
# USA Mathematical Olympiad 2012, Problem 2

A circle is divided into 432 congruent arcs by 432 points. The points are
colored in four colors such that some 108 points are colored Red, some 108
points are colored Green, some 108 points are colored Blue, and the remaining
108 points are colored Yellow. Prove that one can choose three points of each
color in such a way that the four triangles formed by the chosen points of the
same color are congruent.

## Formalization notes

We identify the 432 points with `ZMod 432`; a rotation of the circle is then
addition of a constant. The coloring is a map `color : ZMod 432 → Fin 4`,
where `0, 1, 2, 3` stand for red, green, blue and yellow. We prove the
stronger statement that the four triangles can be chosen to be rotations of
one another: there is a red triangle `U` and rotations `t₁, t₂, t₃` such that
`U + t₁`, `U + t₂`, `U + t₃` are green, blue and yellow triangles. Since the
pairwise arc distances of the vertices are preserved by rotations, the four
triangles are congruent (equal chord lengths, hence SSS).
-/

namespace Usa2012P2

/-- The arc distance between two of the 432 points: the number of unit arcs
in the shorter of the two arcs joining them. The chord through `x` and `y` has
length `2R sin(π·d/432)` with `d = arcDist x y`, which is strictly increasing
in `d ∈ [0, 216]`; hence two inscribed triangles with equal pairwise arc
distances have equal side lengths and are congruent. -/
def arcDist (x y : ZMod 432) : ℕ := min (x - y).val (y - x).val

snip begin

-- The proof follows the solution in Evan Chen's USAMO 2012 solution notes
-- (https://web.evanchen.cc/exams/USAMO-2012-notes.pdf): double-count
-- red-green, red-blue and red-yellow incidences over all non-identity
-- rotations and apply the pigeonhole principle three times.

/-- Arc distance is invariant under rotations. -/
lemma arcDist_add (x y t : ZMod 432) : arcDist (x + t) (y + t) = arcDist x y := by
  unfold arcDist
  rw [show (x + t) - (y + t) = x - y by abel, show (y + t) - (x + t) = y - x by abel]

lemma mem_filter_color {color : ZMod 432 → Fin 4} {i : Fin 4} {x : ZMod 432} :
    x ∈ Finset.univ.filter (fun y => color y = i) ↔ color x = i := by
  simp

/-- Different color classes are disjoint. -/
lemma disjoint_color {color : ZMod 432 → Fin 4} {i j : Fin 4} (hij : i ≠ j) :
    Disjoint (Finset.univ.filter fun x => color x = i)
      (Finset.univ.filter fun x => color x = j) := by
  rw [Finset.disjoint_left]
  intro x hxi hxj
  rw [mem_filter_color] at hxi hxj
  exact hij (hxi.symm.trans hxj)

/-- Pigeonhole over rotations. Suppose that no rotation in `avoid` moves a
point of `S` onto a point of `C`, and that `(432 - #avoid) * k < #S * #C`.
Each of the `#S * #C` pairs `(x, c) ∈ S × C` determines a unique rotation
sending `x` to `c`, and this rotation lies outside `avoid`; averaging over the
`432 - #avoid` allowed rotations, some rotation moves more than `k` points of
`S` onto `C`. -/
lemma exists_rotation {S C avoid : Finset (ZMod 432)} {k : ℕ}
    (havoid : ∀ x ∈ S, ∀ t ∈ avoid, x + t ∉ C)
    (hcard : (432 - avoid.card) * k < S.card * C.card) :
    ∃ t, t ∉ avoid ∧ ∃ T, T ⊆ S ∧ k < T.card ∧ ∀ x ∈ T, x + t ∈ C := by
  suffices ∃ t, t ∉ avoid ∧ k < (S.filter fun x => x + t ∈ C).card by
    obtain ⟨t, ht, h⟩ := this
    exact ⟨t, ht, S.filter (fun x => x + t ∈ C), Finset.filter_subset _ _, h,
      fun x hx => (Finset.mem_filter.mp hx).2⟩
  -- double counting: the total number of incidences over all allowed rotations
  have key : ∑ t ∈ Finset.univ \ avoid, (S.filter fun x => x + t ∈ C).card
      = S.card * C.card := by
    have h1 : ∀ x ∈ S, ((Finset.univ \ avoid).filter fun t => x + t ∈ C)
        = Finset.univ.filter fun t => x + t ∈ C := by
      intro x hx
      ext t
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact ⟨fun h => h.2, fun h => ⟨fun ha => havoid x hx t ha h, h⟩⟩
    have h2 : ∀ x : ZMod 432, (Finset.univ.filter fun t => x + t ∈ C).card
        = C.card := by
      intro x
      apply Finset.card_bij (fun t _ => x + t)
      · intro t ht; simpa using ht
      · intro t₁ _ t₂ _ h; exact add_left_cancel_iff.mp h
      · intro c hc; exact ⟨c - x, by simpa, by simp⟩
    have h3 : ∀ x ∈ S, ∑ t ∈ Finset.univ \ avoid, (if x + t ∈ C then 1 else 0)
        = C.card := by
      intro x hx
      rw [← Finset.card_filter, h1 x hx, h2 x]
    rw [Finset.sum_congr rfl (fun t _ => Finset.card_filter _ _), Finset.sum_comm,
      Finset.sum_congr rfl h3, Finset.sum_const, Nat.nsmul_eq_mul]
  have hTcard : (Finset.univ \ avoid : Finset (ZMod 432)).card
      = 432 - avoid.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, ZMod.card]
  -- the average number of incidences exceeds `k`, so some rotation exceeds `k`
  obtain ⟨t, ht, h⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ \ avoid)
    (f := fun _ => k) (g := fun t => (S.filter fun x => x + t ∈ C).card) <| by
    rw [Finset.sum_const, Nat.nsmul_eq_mul, hTcard, key]
    exact hcard
  exact ⟨t, by simpa using ht, h⟩

snip end

problem usa2012_p2 (color : ZMod 432 → Fin 4)
    (hcolor : ∀ i, (Finset.univ.filter fun x => color x = i).card = 108) :
    ∃ (U : Finset (ZMod 432)) (t₁ t₂ t₃ : ZMod 432),
      U.card = 3 ∧
      (∀ x ∈ U, color x = 0) ∧
      (∀ x ∈ U, color (x + t₁) = 1) ∧
      (∀ x ∈ U, color (x + t₂) = 2) ∧
      (∀ x ∈ U, color (x + t₃) = 3) ∧
      (∀ x ∈ U, ∀ y ∈ U, arcDist x y = arcDist (x + t₁) (y + t₁)) ∧
      (∀ x ∈ U, ∀ y ∈ U, arcDist x y = arcDist (x + t₂) (y + t₂)) ∧
      (∀ x ∈ U, ∀ y ∈ U, arcDist x y = arcDist (x + t₃) (y + t₃)) := by
  -- Step 1: some nonzero rotation `t₁` moves at least 28 red points onto
  -- green points, since 108 * 108 = 11664 > 11637 = 431 * 27.
  obtain ⟨t₁, ht₁, S₁, hS₁R, hS₁card, hS₁G⟩ :=
    exists_rotation (S := Finset.univ.filter fun x => color x = 0)
      (C := Finset.univ.filter fun x => color x = 1) (avoid := {0}) (k := 27)
      (fun x hx t ht => by
        rw [Finset.mem_singleton] at ht
        subst ht
        rw [add_zero]
        exact Finset.disjoint_left.mp
          (disjoint_color (show (0 : Fin 4) ≠ 1 by decide)) hx)
      (by rw [hcolor 0, hcolor 1, Finset.card_singleton]; decide)
  have ht₁0 : t₁ ≠ 0 := by simpa using ht₁
  -- Step 2: excluding `0` and `t₁` (which move points of `S₁` onto red and
  -- green points), some rotation `t₂` moves at least 8 of those 28 points
  -- onto blue points, since 28 * 108 = 3024 > 3010 = 430 * 7.
  obtain ⟨t₂, ht₂, S₂, hS₂S₁, hS₂card, hS₂B⟩ :=
    exists_rotation (S := S₁)
      (C := Finset.univ.filter fun x => color x = 2) (avoid := {0, t₁}) (k := 7)
      (fun x hx t ht => by
        rw [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl
        · rw [add_zero]
          exact Finset.disjoint_left.mp
            (disjoint_color (show (0 : Fin 4) ≠ 2 by decide)) (hS₁R hx)
        · exact Finset.disjoint_left.mp
            (disjoint_color (show (1 : Fin 4) ≠ 2 by decide)) (hS₁G x hx))
      (by rw [hcolor 2, Finset.card_pair ht₁0.symm]; lia)
  have ht₂0 : t₂ ≠ 0 := by
    intro h
    subst h
    simp at ht₂
  have ht₂1 : t₂ ≠ t₁ := by
    intro h
    subst h
    simp at ht₂
  have hcard012 : ({0, t₁, t₂} : Finset (ZMod 432)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair ht₂1.symm]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨ht₁0.symm, ht₂0.symm⟩
  -- Step 3: excluding `0`, `t₁` and `t₂` (which move points of `S₂` onto red,
  -- green and blue points), some rotation `t₃` moves at least 3 of those 8
  -- points onto yellow points, since 8 * 108 = 864 > 858 = 429 * 2.
  obtain ⟨t₃, -, S₃, hS₃S₂, hS₃card, hS₃Y⟩ :=
    exists_rotation (S := S₂)
      (C := Finset.univ.filter fun x => color x = 3) (avoid := {0, t₁, t₂}) (k := 2)
      (fun x hx t ht => by
        rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl
        · rw [add_zero]
          exact Finset.disjoint_left.mp
            (disjoint_color (show (0 : Fin 4) ≠ 3 by decide)) (hS₁R (hS₂S₁ hx))
        · exact Finset.disjoint_left.mp
            (disjoint_color (show (1 : Fin 4) ≠ 3 by decide)) (hS₁G x (hS₂S₁ hx))
        · exact Finset.disjoint_left.mp
            (disjoint_color (show (2 : Fin 4) ≠ 3 by decide)) (hS₂B x hx))
      (by rw [hcolor 3, hcard012]; lia)
  -- keep exactly 3 of the at-least-3 points
  obtain ⟨U, hUS₃, hUcard⟩ :=
    Finset.exists_subset_card_eq (Nat.succ_le_of_lt hS₃card)
  refine ⟨U, t₁, t₂, t₃, hUcard, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact mem_filter_color.mp (hS₁R (hS₂S₁ (hS₃S₂ (hUS₃ hx))))
  · intro x hx
    exact mem_filter_color.mp (hS₁G x (hS₂S₁ (hS₃S₂ (hUS₃ hx))))
  · intro x hx
    exact mem_filter_color.mp (hS₂B x (hS₃S₂ (hUS₃ hx)))
  · intro x hx
    exact mem_filter_color.mp (hS₃Y x (hUS₃ hx))
  · intro x _ y _
    exact (arcDist_add x y t₁).symm
  · intro x _ y _
    exact (arcDist_add x y t₂).symm
  · intro x _ y _
    exact (arcDist_add x y t₃).symm

end Usa2012P2
