/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Data.ZMod.Defs
public import Mathlib.InformationTheory.Hamming
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 1990, Problem 1

A license plate has six digits from 0 to 9 and may have leading zeros.
If two plates must always differ in at least two places, what is the
largest number of plates that is possible?
-/

namespace Usa1990P1

/-- A license plate: six digits, each from 0 to 9 (leading zeros allowed).
We model digits as elements of `ZMod 10` so that digit sums modulo ten
are available for the checksum argument. -/
abbrev Plate := Fin 6 → ZMod 10

/-- A collection of plates is valid if any two distinct plates in it
differ in at least two places. -/
def IsValid (S : Finset Plate) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, p ≠ q → 2 ≤ hammingDist p q

snip begin

/-- The checksum construction: given five digits `f : Fin 5 → ZMod 10`,
build a six-digit plate whose last digit makes the total digit sum
congruent to zero modulo ten. -/
def extend (f : Fin 5 → ZMod 10) : Plate :=
  Fin.lastCases (-∑ i, f i) (fun i ↦ f i)

/-- The digit sum of a plate built by `extend` is zero modulo ten. -/
theorem sum_extend (f : Fin 5 → ZMod 10) : ∑ j, extend f j = 0 := by
  rw [Fin.sum_univ_castSucc]
  unfold extend
  rw [Fin.lastCases_last]
  simp only [Fin.lastCases_castSucc]
  exact add_neg_cancel _

/-- The first five digits determine a plate built by `extend`. -/
theorem extend_injective : Function.Injective extend := by
  intro f g h
  funext i
  have hi := congrFun h (Fin.castSucc i)
  simpa [extend] using hi

/-- Two plates with the same digit sum modulo ten cannot differ in
exactly one place; hence distinct plates of equal sum differ in at
least two places. -/
theorem hammingDist_ge_two_of_sum_eq {n : ℕ} {p q : Fin n → ZMod 10}
    (hsum : ∑ i, p i = ∑ i, q i) (hne : p ≠ q) :
    2 ≤ hammingDist p q := by
  have hne1 : hammingDist p q ≠ 1 := by
    intro h1
    have h1' : (Finset.univ.filter fun i ↦ p i ≠ q i).card = 1 := h1
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp h1'
    have hpj : p j ≠ q j := by
      have hjj : j ∈ Finset.univ.filter (fun i ↦ p i ≠ q i) :=
        hj ▸ Finset.mem_singleton_self j
      exact (Finset.mem_filter.mp hjj).2
    -- the sum of the differences telescopes to the single term `p j - q j`
    have hsub : ∑ i, (p i - q i) = 0 := by
      rw [Finset.sum_sub_distrib, hsum, sub_self]
    have hss : ∑ i ∈ ({j} : Finset (Fin n)), (p i - q i) =
        ∑ i ∈ Finset.univ, (p i - q i) := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hij
      have hi : p i = q i := by
        by_contra hpi
        have hmem : i ∈ Finset.univ.filter (fun i ↦ p i ≠ q i) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ i, hpi⟩
        rw [hj] at hmem
        exact hij hmem
      rw [hi, sub_self]
    rw [Finset.sum_singleton, hsub] at hss
    exact hpj (sub_eq_zero.mp hss)
  have hpos : 0 < hammingDist p q := hammingDist_pos.mpr hne
  lia

/-- Upper bound: a valid collection of plates has at most `10 ^ 5`
members. Indeed, two plates agreeing on the first five digits differ in
at most one place, so the "first five digits" map is injective on any
valid collection, whose codomain has size `10 ^ 5`. -/
theorem card_le_of_valid {S : Finset Plate} (hS : IsValid S) :
    S.card ≤ 10 ^ 5 := by
  have hinj : Set.InjOn (fun p : Plate ↦ fun i : Fin 5 ↦ p (Fin.castSucc i)) S := by
    intro p hp q hq hpq
    by_contra hne
    have h2 := hS p (Finset.mem_coe.mp hp) q (Finset.mem_coe.mp hq) hne
    have hsub : Finset.univ.filter (fun i ↦ p i ≠ q i) ⊆ {Fin.last 5} := by
      intro i hi
      by_contra hmem
      have hlast : i ≠ Fin.last 5 := fun h ↦ hmem (Finset.mem_singleton.mpr h)
      obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hlast
      exact (Finset.mem_filter.mp hi).2 (congrFun hpq j)
    have hle : hammingDist p q ≤ 1 :=
      calc hammingDist p q = (Finset.univ.filter fun i ↦ p i ≠ q i).card := rfl
        _ ≤ ({Fin.last 5} : Finset (Fin 6)).card := Finset.card_le_card hsub
        _ = 1 := Finset.card_singleton _
    lia
  calc S.card ≤ (Finset.univ : Finset (Fin 5 → ZMod 10)).card :=
        Finset.card_le_card_of_injOn _ (fun p _ ↦ Finset.mem_univ _) hinj
    _ = 10 ^ 5 := by
        rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]

snip end

determine answer : ℕ := 10 ^ 5

problem usa1990_p1 :
    IsGreatest {k : ℕ | ∃ S : Finset Plate, S.card = k ∧ IsValid S} answer := by
  refine ⟨⟨Finset.univ.image extend, ?_, ?_⟩, ?_⟩
  · show (Finset.univ.image extend).card = 10 ^ 5
    rw [Finset.card_image_of_injOn extend_injective.injOn, Finset.card_univ,
      Fintype.card_fun, ZMod.card, Fintype.card_fin]
  · intro p hp q hq hpq
    obtain ⟨f, -, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hq
    exact hammingDist_ge_two_of_sum_eq (by simp [sum_extend]) hpq
  · intro k hk
    obtain ⟨S, rfl, hS⟩ := hk
    exact card_le_of_valid hS

end Usa1990P1
