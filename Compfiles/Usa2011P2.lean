/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2011, Problem 2

An integer is assigned to each vertex of a regular pentagon so that the sum of
the five integers is 2011. A turn of a solitaire game consists of subtracting
an integer m (not necessarily positive) from each of the integers at two
neighboring vertices and adding 2m to the opposite vertex, which is not
adjacent to either of the first two vertices. (The amount m and the vertices
chosen can vary from turn to turn.) The game is won at a certain vertex if,
after some number of turns, that vertex has the number 2011 and the other four
vertices have the number 0. Prove that for any choice of the initial integers,
there is exactly one vertex at which the game can be won.
-/

namespace Usa2011P2

/-- A configuration of the game: an integer at each vertex of the pentagon.
The vertices are indexed by `ZMod 5`, so that the neighbors of vertex `i` are
`i - 1` and `i + 1`. -/
abbrev Config := ZMod 5 → ℤ

/-- Reachability of configurations. A turn at the edge `i, i + 1` with amount
`m` subtracts `m` from the values at the vertices `i` and `i + 1` and adds
`2 * m` to the value at the opposite vertex `i + 3` (the unique vertex adjacent
to neither of them). The effects of successive turns add up, so a sequence of
turns is described by integers `x j`, the sum of the amounts of the turns whose
opposite vertex is `j`. Such a turn has edge `j + 2, j + 3`, hence vertex `i`
gains `2 * x i` in total and loses `x (i + 2) + x (i + 3)`. Conversely any
choice of `x` is realized by doing one turn per edge. -/
def Reachable (a b : Config) : Prop :=
  ∃ x : ZMod 5 → ℤ, ∀ i, b i = a i + 2 * x i - x (i + 2) - x (i + 3)

/-- The game is won at vertex `v` from the configuration `a` if the
configuration with value 2011 at `v` and 0 at the other four vertices is
reachable from `a`. -/
def WinAt (a : Config) (v : ZMod 5) : Prop :=
  Reachable a (Pi.single v 2011)

/-- The invariant of the game: the weighted sum of the values, where the value
at vertex `i` has weight `i`. A turn changes it by a multiple of 5. -/
def invariant (a : Config) : ZMod 5 := ∑ i, i * (a i : ZMod 5)

snip begin

-- Follows the solution at https://web.evanchen.cc/exams/USAMO-2011-notes.pdf .
-- The invariant shows that a win at vertex `v` forces `v = invariant a`,
-- which gives uniqueness; for existence one reduces by rotation to winning
-- at vertex 0 and then solves the resulting linear system explicitly.

lemma zmod5_sum {M : Type*} [AddCommMonoid M] (f : ZMod 5 → M) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 := Fin.sum_univ_five f

lemma zmod5_cases (i : ZMod 5) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
  decide +revert

/-- The key identity behind the invariance of `invariant`: the weight of a
turn at edge `i, i + 1` is `i + (i + 1) = 2 * (i + 3) - 5`. -/
lemma key_identity (X : ZMod 5 → ZMod 5) :
    (∑ i, i * (2 * X i - X (i + 2) - X (i + 3))) = 0 := by
  have h2 : (∑ i : ZMod 5, i * X (i + 2)) = ∑ j, (j - 2 : ZMod 5) * X j := by
    apply Fintype.sum_equiv (Equiv.addRight 2)
    intro i
    show i * X (i + 2) = (i + 2 - 2 : ZMod 5) * X (i + 2)
    rw [add_sub_cancel_right]
  have h3 : (∑ i : ZMod 5, i * X (i + 3)) = ∑ j, (j - 3 : ZMod 5) * X j := by
    apply Fintype.sum_equiv (Equiv.addRight 3)
    intro i
    show i * X (i + 3) = (i + 3 - 3 : ZMod 5) * X (i + 3)
    rw [add_sub_cancel_right]
  calc ∑ i : ZMod 5, i * (2 * X i - X (i + 2) - X (i + 3))
      = (∑ i : ZMod 5, i * (2 * X i)) - (∑ i, i * X (i + 2))
          - (∑ i, i * X (i + 3)) := by
        rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl; intro i _; ring
    _ = (∑ i : ZMod 5, i * (2 * X i)) - (∑ i, (i - 2 : ZMod 5) * X i)
          - (∑ i, (i - 3 : ZMod 5) * X i) := by rw [h2, h3]
    _ = ∑ i : ZMod 5, (5 : ZMod 5) * X i := by
        rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl; intro i _; ring
    _ = 0 := by
        rw [← Finset.mul_sum, show (5 : ZMod 5) = 0 by decide, zero_mul]

/-- The invariant is preserved by any sequence of turns. -/
lemma invariant_eq_of_reachable {a b : Config} (h : Reachable a b) :
    invariant b = invariant a := by
  obtain ⟨x, hx⟩ := h
  have e : (∑ i : ZMod 5, i * ((b i : ℤ) : ZMod 5))
      = (∑ i : ZMod 5, i * ((a i : ℤ) : ZMod 5))
        + ∑ i : ZMod 5, i * (2 * ((x i : ℤ) : ZMod 5) - ((x (i + 2) : ℤ) : ZMod 5)
            - ((x (i + 3) : ℤ) : ZMod 5)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hx i]
    push_cast
    ring
  unfold invariant
  rw [e, key_identity, add_zero]

/-- The invariant of the configuration won at vertex `v`; since
`2011 ≡ 1 (mod 5)`, it equals `v`. -/
lemma invariant_single (v : ZMod 5) : invariant (Pi.single v 2011) = v := by
  unfold invariant
  rw [Finset.sum_eq_single v]
  · rw [Pi.single_eq_same, show ((2011 : ℤ) : ZMod 5) = 1 by decide, mul_one]
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, Int.cast_zero, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ v) h

/-- The core existence lemma: a configuration with sum 2011 and vanishing
invariant can be won at vertex 0. With `k` given by
`a 1 + 2 * a 2 + 3 * a 3 + 4 * a 4 = 5 * k`, the explicit solution is
`x 0 = 0`, `x 1 = -k - a 1`, `x 2 = -2 * k + a 3 + a 4`,
`x 3 = -3 * k + a 2 + a 3 + 2 * a 4`, `x 4 = -4 * k + a 2 + 2 * a 3 + 2 * a 4`. -/
lemma win_at_zero (a : Config) (hsum : ∑ i, a i = 2011) (hinv : invariant a = 0) :
    WinAt a 0 := by
  rw [zmod5_sum] at hsum
  have hdvd : (5 : ℤ) ∣ a 1 + 2 * a 2 + 3 * a 3 + 4 * a 4 := by
    have h : ((a 1 + 2 * a 2 + 3 * a 3 + 4 * a 4 : ℤ) : ZMod 5) = 0 := by
      have hi := hinv
      unfold invariant at hi
      rw [zmod5_sum] at hi
      push_cast
      linear_combination hi
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  obtain ⟨k, hk⟩ := hdvd
  refine ⟨fun i => if i = 0 then (0 : ℤ)
      else if i = 1 then (-k - a 1)
      else if i = 2 then (-2 * k + a 3 + a 4)
      else if i = 3 then (-3 * k + a 2 + a 3 + 2 * a 4)
      else (-4 * k + a 2 + 2 * a 3 + 2 * a 4), fun i => ?_⟩
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
  · show (2011 : ℤ) = a 0 + 2 * 0 - (-2 * k + a 3 + a 4)
      - (-3 * k + a 2 + a 3 + 2 * a 4)
    lia
  · show (0 : ℤ) = a 1 + 2 * (-k - a 1) - (-3 * k + a 2 + a 3 + 2 * a 4)
      - (-4 * k + a 2 + 2 * a 3 + 2 * a 4)
    lia
  · show (0 : ℤ) = a 2 + 2 * (-2 * k + a 3 + a 4)
      - (-4 * k + a 2 + 2 * a 3 + 2 * a 4) - 0
    lia
  · show (0 : ℤ) = a 3 + 2 * (-3 * k + a 2 + a 3 + 2 * a 4) - 0 - (-k - a 1)
    lia
  · show (0 : ℤ) = a 4 + 2 * (-4 * k + a 2 + 2 * a 3 + 2 * a 4) - (-k - a 1)
      - (-2 * k + a 3 + a 4)
    lia

snip end

problem usa2011_p2 (a : Config) (hsum : ∑ i, a i = 2011) :
    ∃! v, WinAt a v := by
  refine ⟨invariant a, ?_, fun w hw => ?_⟩
  · -- Existence at `v = invariant a`, via the rotated configuration
    -- `a' i = a (i + v)`, which has vanishing invariant.
    have hsum' : (∑ i : ZMod 5, a (i + invariant a)) = 2011 := by
      have h := Fintype.sum_equiv (Equiv.addRight (invariant a))
        (fun i => a (i + invariant a)) a (fun i => rfl)
      rw [hsum] at h
      exact h
    have h1 : (∑ i : ZMod 5, i * ((a (i + invariant a) : ℤ) : ZMod 5))
        = ∑ j : ZMod 5, (j - invariant a : ZMod 5) * ((a j : ℤ) : ZMod 5) := by
      apply Fintype.sum_equiv (Equiv.addRight (invariant a))
      intro i
      show i * ((a (i + invariant a) : ℤ) : ZMod 5)
          = (i + invariant a - invariant a : ZMod 5)
            * ((a (i + invariant a) : ℤ) : ZMod 5)
      rw [add_sub_cancel_right]
    have hinv' : invariant (fun i => a (i + invariant a)) = 0 := by
      show (∑ i : ZMod 5, i * ((a (i + invariant a) : ℤ) : ZMod 5)) = 0
      rw [h1]
      have h3 : (∑ j : ZMod 5, (j - invariant a : ZMod 5) * ((a j : ℤ) : ZMod 5))
          = (∑ j : ZMod 5, j * (a j : ZMod 5))
            - invariant a * (∑ j : ZMod 5, (a j : ZMod 5)) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [h3, ← Int.cast_sum, hsum, show ((2011 : ℤ) : ZMod 5) = 1 by decide,
        mul_one]
      exact sub_self _
    obtain ⟨x', hx'⟩ := win_at_zero (fun i => a (i + invariant a)) hsum' hinv'
    refine ⟨fun i => x' (i - invariant a), fun i => ?_⟩
    have e1 : (Pi.single (invariant a) 2011 : Config) i
        = (Pi.single (0 : ZMod 5) 2011 : Config) (i - invariant a) := by
      by_cases hiv : i = invariant a
      · subst hiv
        rw [sub_self, Pi.single_eq_same, Pi.single_eq_same]
      · have h0 : i - invariant a ≠ 0 := sub_ne_zero.mpr hiv
        rw [Pi.single_eq_of_ne hiv, Pi.single_eq_of_ne h0]
    rw [e1, hx' (i - invariant a)]
    show a (i - invariant a + invariant a) + 2 * x' (i - invariant a)
        - x' (i - invariant a + 2) - x' (i - invariant a + 3)
        = a i + 2 * x' (i - invariant a) - x' (i + 2 - invariant a)
          - x' (i + 3 - invariant a)
    have r0 : i - invariant a + invariant a = i := sub_add_cancel _ _
    have r2 : i - invariant a + 2 = i + 2 - invariant a := by ring
    have r3 : i - invariant a + 3 = i + 3 - invariant a := by ring
    rw [r0, r2, r3]
  · -- Uniqueness: a win at `w` forces `w = invariant a`.
    have h1 := invariant_eq_of_reachable hw
    rw [invariant_single] at h1
    exact h1

end Usa2011P2
