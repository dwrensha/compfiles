/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.EuclideanDomain.Basic
public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Rat.Star
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 1975, Problem 5

A pack of n cards, including three aces, is well shuffled. Cards are turned
over in turn. Show that the expected number of cards that must be turned over
to reach the second ace is (n+1)/2.

## Formalization notes

We model the well-shuffled pack by the set of positions occupied by the three
aces, which is uniformly distributed over the 3-element subsets of
`{1, ..., n}`. The number of cards that must be turned over to reach the
second ace is then the middle (second-smallest) of the three ace positions,
and the expected number of cards is the average of this quantity over all
3-element subsets.
-/

namespace Usa1975P5

open Finset

/-- The sample space: the 3-element subsets of the positions `{1, ..., n}`;
each such subset records the positions of the three aces in the pack. -/
def aceSets (n : ℕ) : Finset (Finset ℕ) := (Icc 1 n).powersetCard 3

/-- Reflection of the pack about its middle: the card in position `x`
of a pack of `n` cards moves to position `n + 1 - x`. -/
def reflect (n x : ℕ) : ℕ := n + 1 - x

/-- The minimum of a set of naturals, defaulting to `0` for the empty set. -/
def minD (S : Finset ℕ) : ℕ := (S.min).untopD 0

/-- The maximum of a set of naturals, defaulting to `0` for the empty set. -/
def maxD (S : Finset ℕ) : ℕ := (S.max).unbotD 0

/-- The middle element of a 3-element set of natural numbers, computed as
the sum minus the minimum minus the maximum. When `S` is the set of ace
positions, this is the number of cards turned over to reach the second ace. -/
def mid (S : Finset ℕ) : ℤ :=
  (∑ x ∈ S, (x : ℤ)) - (minD S : ℤ) - (maxD S : ℤ)

snip begin

lemma card_aceSets (n : ℕ) : (aceSets n).card = n.choose 3 := by
  simp [aceSets, card_powersetCard]

lemma nonempty_of_mem_aceSets {n : ℕ} {S : Finset ℕ} (hS : S ∈ aceSets n) :
    S.Nonempty := by
  have h3 : S.card = 3 := (mem_powersetCard.mp hS).2
  exact card_pos.mp (by omega)

/-- A card in position `x ∈ {1, ..., n}` reflects to a position in `{1, ..., n}`. -/
lemma reflect_mem {n x : ℕ} (hx : x ∈ Icc 1 n) : reflect n x ∈ Icc 1 n := by
  rw [mem_Icc] at hx ⊢
  simp only [reflect]
  omega

/-- Reflection is injective on positions that are at most `n`. -/
lemma reflect_injOn (n : ℕ) : Set.InjOn (reflect n) {x | x ≤ n} := by
  intro x hx y hy h
  simp only [Set.mem_ofPred_eq] at hx hy
  simp only [reflect] at h
  omega

/-- Reflection is an involution on positions that are at most `n`. -/
lemma reflect_reflect {n x : ℕ} (hx : x ≤ n) : reflect n (reflect n x) = x := by
  simp only [reflect]
  omega

/-- The minimum of the reflected set is the reflection of the maximum. -/
lemma min_image_reflect {n : ℕ} {S : Finset ℕ} (hsub : S ⊆ Icc 1 n) (hne : S.Nonempty) :
    (minD (S.image (reflect n)) : ℤ) = (n : ℤ) + 1 - (maxD S : ℤ) := by
  have him : (S.image (reflect n)).Nonempty := image_nonempty.mpr hne
  have hmax_mem : S.max' hne ∈ S := max'_mem _ _
  have hmax_le : S.max' hne ≤ n := (mem_Icc.mp (hsub hmax_mem)).2
  have key : (S.image (reflect n)).min' him = n + 1 - S.max' hne := by
    apply le_antisymm
    · apply min'_le
      exact mem_image.mpr ⟨S.max' hne, hmax_mem, rfl⟩
    · apply le_min'
      intro y hy
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hy
      have ha' : 1 ≤ a ∧ a ≤ n := mem_Icc.mp (hsub ha)
      have hle : a ≤ S.max' hne := le_max' _ _ ha
      simp only [reflect]
      omega
  unfold minD maxD
  rw [← coe_min' him, WithTop.untopD_coe, key, ← coe_max' hne, WithBot.unbotD_coe,
    Nat.cast_sub (show S.max' hne ≤ n + 1 by omega)]
  push_cast
  ring

/-- The maximum of the reflected set is the reflection of the minimum. -/
lemma max_image_reflect {n : ℕ} {S : Finset ℕ} (hsub : S ⊆ Icc 1 n) (hne : S.Nonempty) :
    (maxD (S.image (reflect n)) : ℤ) = (n : ℤ) + 1 - (minD S : ℤ) := by
  have him : (S.image (reflect n)).Nonempty := image_nonempty.mpr hne
  have hmin_mem : S.min' hne ∈ S := min'_mem _ _
  have hmin_le : S.min' hne ≤ n := (mem_Icc.mp (hsub hmin_mem)).2
  have key : (S.image (reflect n)).max' him = n + 1 - S.min' hne := by
    apply le_antisymm
    · apply max'_le
      intro y hy
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hy
      have ha' : 1 ≤ a ∧ a ≤ n := mem_Icc.mp (hsub ha)
      have hge : S.min' hne ≤ a := min'_le _ _ ha
      simp only [reflect]
      omega
    · apply le_max'
      exact mem_image.mpr ⟨S.min' hne, hmin_mem, rfl⟩
  unfold minD maxD
  rw [← coe_max' him, WithBot.unbotD_coe, key, ← coe_min' hne, WithTop.untopD_coe,
    Nat.cast_sub (show S.min' hne ≤ n + 1 by omega)]
  push_cast
  ring

/-- The sum of the reflected set is `3 * (n + 1)` minus the sum of the set. -/
lemma sum_image_reflect {n : ℕ} {S : Finset ℕ} (hsub : S ⊆ Icc 1 n) (hcard : S.card = 3) :
    (∑ y ∈ S.image (reflect n), (y : ℤ)) = 3 * ((n : ℤ) + 1) - ∑ x ∈ S, (x : ℤ) := by
  have hinj : Set.InjOn (reflect n) S :=
    (reflect_injOn n).mono (fun x hx => (mem_Icc.mp (hsub hx)).2)
  have h1 : ∀ x ∈ S, ((reflect n x : ℕ) : ℤ) = (n : ℤ) + 1 - (x : ℤ) := by
    intro x hx
    have hx' : x ≤ n := (mem_Icc.mp (hsub hx)).2
    show ((n + 1 - x : ℕ) : ℤ) = (n : ℤ) + 1 - (x : ℤ)
    rw [Nat.cast_sub (show x ≤ n + 1 by omega)]
    push_cast
    ring
  rw [sum_image hinj]
  trans ∑ x ∈ S, ((n : ℤ) + 1 - (x : ℤ))
  · exact sum_congr rfl h1
  · rw [sum_sub_distrib, sum_const, hcard, nsmul_eq_mul]
    norm_num

/-- Reflecting every position turns the middle element `m` into `n + 1 - m`:
this is the heart of the reflection argument. -/
lemma mid_image_reflect {n : ℕ} {S : Finset ℕ} (hS : S ∈ aceSets n) :
    mid (S.image (reflect n)) = (n : ℤ) + 1 - mid S := by
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hS
  have hne : S.Nonempty := nonempty_of_mem_aceSets hS
  unfold mid
  rw [sum_image_reflect hsub hcard, min_image_reflect hsub hne, max_image_reflect hsub hne]
  ring

/-- Reflecting the positions of the aces yields another valid set of positions. -/
lemma image_mem_aceSets {n : ℕ} {S : Finset ℕ} (hS : S ∈ aceSets n) :
    S.image (reflect n) ∈ aceSets n := by
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hS
  show S.image (reflect n) ∈ (Icc 1 n).powersetCard 3
  rw [mem_powersetCard]
  refine ⟨?_, ?_⟩
  · intro y hy
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hy
    exact reflect_mem (hsub ha)
  · rw [card_image_of_injOn
      ((reflect_injOn n).mono (fun x hx => (mem_Icc.mp (hsub hx)).2))]
    exact hcard

/-- Reflection of position sets is an involution on the sample space. -/
lemma image_image_reflect {n : ℕ} {S : Finset ℕ} (hS : S ∈ aceSets n) :
    (S.image (reflect n)).image (reflect n) = S := by
  obtain ⟨hsub, -⟩ := mem_powersetCard.mp hS
  rw [image_image]
  trans S.image (fun x => x)
  · exact image_congr (fun x hx => reflect_reflect ((mem_Icc.mp (hsub hx)).2))
  · exact image_id'

/-- Reflection of position sets is injective on the sample space. -/
lemma image_reflect_injOn (n : ℕ) :
    Set.InjOn (fun S : Finset ℕ => S.image (reflect n)) (aceSets n) := by
  intro S₁ h₁ S₂ h₂ h
  change S₁.image (reflect n) = S₂.image (reflect n) at h
  have e1 := image_image_reflect h₁
  have e2 := image_image_reflect h₂
  rw [h] at e1
  rw [e2] at e1
  exact e1.symm

/-- Reflecting the position sets permutes the sample space. -/
lemma image_reflect_aceSets (n : ℕ) :
    (aceSets n).image (fun S => S.image (reflect n)) = aceSets n := by
  ext T
  simp only [mem_image]
  constructor
  · rintro ⟨S, hS, rfl⟩
    exact image_mem_aceSets hS
  · intro hT
    exact ⟨T.image (reflect n), image_mem_aceSets hT, image_image_reflect hT⟩

/-- Reindexing the sum over the sample space by reflection. -/
lemma sum_mid_image_reflect (n : ℕ) :
    ∑ S ∈ aceSets n, mid (S.image (reflect n)) = ∑ S ∈ aceSets n, mid S := by
  have h := (sum_image (f := mid) (image_reflect_injOn n)).symm
  rw [image_reflect_aceSets] at h
  exact h

/-- Twice the total of the middle positions equals `(n + 1)` times the number
of position sets: the average middle position is `(n + 1) / 2`. -/
lemma two_mul_sum_mid (n : ℕ) :
    2 * (∑ S ∈ aceSets n, mid S) = (n.choose 3 : ℤ) * (n + 1) := by
  have h2 : ∑ S ∈ aceSets n, (mid S + mid (S.image (reflect n)))
      = (n.choose 3 : ℤ) * (n + 1) := by
    have hs : ∀ S ∈ aceSets n, mid S + mid (S.image (reflect n)) = (n : ℤ) + 1 := by
      intro S hS
      rw [mid_image_reflect hS]
      ring
    rw [sum_congr rfl hs, sum_const, card_aceSets, nsmul_eq_mul]
  rw [← h2, sum_add_distrib, sum_mid_image_reflect, two_mul]

snip end

/-- The expected number of cards that must be turned over to reach the
second ace. -/
determine expected (n : ℕ) : ℚ := (n + 1) / 2

problem usa1975_p5 (n : ℕ) (hn : 3 ≤ n) :
    (∑ S ∈ aceSets n, (mid S : ℚ)) / n.choose 3 = expected n := by
  have hQ : 2 * (∑ S ∈ aceSets n, (mid S : ℚ)) = (n.choose 3 : ℚ) * ((n : ℚ) + 1) := by
    have h' := congrArg (Int.cast : ℤ → ℚ) (two_mul_sum_mid n)
    push_cast at h'
    exact h'
  have hc : (n.choose 3 : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hn).ne'
  have hS : (∑ S ∈ aceSets n, (mid S : ℚ)) = (n.choose 3 : ℚ) * (((n : ℚ) + 1) / 2) := by
    linarith
  rw [hS, mul_div_cancel_left₀ _ hc]

end Usa1975P5
