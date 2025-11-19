/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Bradley (Problem statement + scaffolding)
-/

import Mathlib.Tactic
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.NumberTheory.Divisors

import ProblemExtraction

problem_file {
  tags := [.NumberTheory]
}

/-!
# International Mathematical Olympiad 2025, Problem 4
A proper divisor of a positive integer N is a positive divisor of N other than N itself.

The infinite sequence a₁, a₂, ... consists of positive integers, each of which has at least three proper
divisors. For each n ≥ 1, the integer aₙ + 1 is the sum of the three largest proper divisors of aₙ.
Determine all possible values of a₁.
-/

open Finset
open Nat

snip begin

/-- The proper divisors of `n`, sorted in decreasing order. -/
def sortedProperDivisors (n : ℕ) : List ℕ :=
  (Nat.properDivisors n).sort GE.ge

variable {n : ℕ}

lemma sortedProperDivisors_eq : sortedProperDivisors n = (Nat.properDivisors n).toList.insertionSort GE.ge := by
  unfold sortedProperDivisors
  apply List.eq_of_perm_of_sorted (r := GE.ge)
  · trans n.properDivisors.toList
    · apply sort_perm_toList
    · symm
      apply List.perm_insertionSort
  · apply sort_sorted
  · apply List.sorted_insertionSort

@[simp]
lemma length_sortedProperDivisors : (sortedProperDivisors n).length = #n.properDivisors := by
  simp [sortedProperDivisors]

lemma mem_properDivisors_iff_mem_sortedProperDivisors :
    ∀ {d}, d ∈ n.properDivisors ↔ d ∈ sortedProperDivisors n := by
  simp [sortedProperDivisors]

lemma sortedProperDivisors_sorted (n : ℕ) :
    List.Sorted GT.gt (sortedProperDivisors n) :=
  n.properDivisors.sort_sorted_gt

lemma sortedProperDivisors_strictAnti (n : ℕ) :
    StrictAnti (sortedProperDivisors n).get :=
  fun _ _ h => (sortedProperDivisors_sorted n).rel_get_of_lt h

lemma le_div_two_of_mem_properDivisors {x : ℕ} : ∀ y ∈ x.properDivisors, y ≤ x / 2 := by
  intro y hy
  if hx : x = 0 then
    rw [hx, properDivisors_zero] at hy
    contradiction
  else
    have ⟨k, hk₁, hk₂⟩ := (mem_properDivisors_iff_exists hx).mp hy
    rw [hk₂]
    trans y * (k / 2)
    · apply Nat.le_mul_of_pos_right
      omega
    · apply mul_div_le_mul_div_assoc

-- Antitonicity but for a specific element and index
lemma getIdx_eq_of {l : List ℕ} {x : ℕ} {i : Fin l.length}
    (mem : x ∈ l) (left : ∀ j, (hj : j < i) → l.get j > x) (right : ∀ j, (hj : j > i) → l.get j < x)
    : x = l.get i := by
  rw [List.mem_iff_get] at mem
  have ⟨i', hi'⟩ := mem
  suffices i = i' from this ▸ hi'.symm
  by_contra hi
  apply (Fin.lt_or_lt_of_ne hi).elim
  · intro hi
    suffices l.get i' < x by omega
    apply right _ hi
  · intro hi
    suffices l.get i' > x by omega
    apply left _ hi

lemma sortedProperDivisors_getIdx_eq {d : ℕ} (mem : d ∈ n.properDivisors)
    {i : Fin (sortedProperDivisors n).length}
    (left : ∀ j, (hj : j < i) → (sortedProperDivisors n).get j > d)
    (right : ∀ j, (hj : j > i) → (sortedProperDivisors n).get j < d)
    : d = (sortedProperDivisors n).get i := by
  apply getIdx_eq_of
  case' mem => rw [←mem_properDivisors_iff_mem_sortedProperDivisors]
  all_goals assumption

/-- Like `mem_properDivisors.mpr`, but for the multiplicative inverse -/
lemma mem_properDivisors' {n m : ℕ} (h₁ : n > 1) (h₂ : n ∣ m) (h₃ : 0 < m) : (m / n) ∈ m.properDivisors := by
  rw [mem_properDivisors]
  constructor
  · exact div_dvd_of_dvd h₂
  · exact div_lt_self h₃ h₁

lemma sortedProperDivisors_get {i : Fin #n.properDivisors} {x : ℕ}
    (hx₁ : x ∈ n.properDivisors) (hx₂ : #{y ∈ n.properDivisors | y > x} = i)
    : x = (sortedProperDivisors n)[i.cast length_sortedProperDivisors.symm] := by
  rw [mem_properDivisors_iff_mem_sortedProperDivisors,
      List.mem_iff_get] at hx₁
  -- x has to be in the list somewhere, at index `i'`

  have ⟨i', hi'⟩ := hx₁
  -- show `i = i'`
  suffices #({y ∈ n.properDivisors | y > x}) = i' by simp_all
  -- establish a bijection between ↑ the set and `Fin i'`
  apply Finset.card_eq_of_equiv_fin
  symm

  let get (j : Fin i') : {y ∈ n.properDivisors | y > x} := by
    use (sortedProperDivisors n)[j]
    rw [mem_filter]
    split_ands
    · rw [mem_properDivisors_iff_mem_sortedProperDivisors]
      apply List.getElem_mem
    · simp only [←hi']
      dsimp
      apply sortedProperDivisors_strictAnti
      exact j.is_lt

  apply Equiv.ofBijective get
  constructor
  · intro j k h
    simp only [Subtype.mk.injEq, get] at h
    have := (sortedProperDivisors_sorted n).nodup.get_inj_iff (i := j.castLE i'.is_le') (j := k.castLE i'.is_le')
    apply Fin.castLE_inj.mp ∘ this.mp
    exact h
  · intro ⟨y, hy⟩
    rw [mem_filter, mem_properDivisors_iff_mem_sortedProperDivisors] at hy
    have ⟨j, hj⟩ := List.get_of_mem hy.left
    refine ⟨⟨j, ?_⟩, ?_⟩
    · apply (sortedProperDivisors_strictAnti n).antitone.reflect_lt
      rw [hi', hj]
      exact hy.right
    · simp only [Subtype.mk.injEq, get]
      exact hj

lemma sortedProperDivisors_get_zero_eq_div_two (h₁ : 2 ∣ n) (h₂ : n > 0) : n / 2 = (sortedProperDivisors n).get ⟨0, by simp; omega⟩ := by
  apply sortedProperDivisors_get (i := ⟨0, by simp; omega⟩)
  · apply mem_properDivisors' <;> omega
  · simp only [Finset.card_eq_zero, filter_eq_empty_iff]
    intro d hd₁ hd₂
    have := le_div_two_of_mem_properDivisors d hd₁
    exact Nat.not_le_of_gt hd₂ this

lemma three_le_card_properDivisors_of_six_dvd (h₁ : 6 ∣ n) (h₂ : n > 0) : 3 ≤ #n.properDivisors := by
  rw [Finset.le_card_iff_exists_subset_card]
  refine ⟨{ 1, 2, 3 }, ?_, rfl⟩
  simp only [insert_subset_iff, singleton_subset_iff]
  repeat rw [Nat.mem_properDivisors]
  omega

lemma lt_lemma {y k l : ℕ} (h₁ : y * k / l < y) (h₂ : l > 0) : k < l :=
  have := lt_of_le_of_lt (Nat.mul_div_le_mul_div_assoc ..) h₁
  have := lt_one_of_mul_lt_right this
  (Nat.div_lt_one_iff h₂).mp this

lemma sortedProperDivisors_get_one_eq_div_three (h₁ : 2 ∣ n) (h₂ : 3 ∣ n) (h₃ : n > 0) : ∃ pf, n / 3 = (sortedProperDivisors n).get ⟨1, pf⟩ := by
  have one_lt_length : 1 < (sortedProperDivisors n).length := by
    apply lt_of_lt_of_le (show 1 < 3 by decide)
    rw [sortedProperDivisors, length_sort]
    apply three_le_card_properDivisors_of_six_dvd
    <;> omega
  use one_lt_length
  apply sortedProperDivisors_get (i := ⟨1, by rwa [←length_sortedProperDivisors]⟩)
  · apply mem_properDivisors' <;> omega
  · suffices {y ∈ n.properDivisors | n / 3 < y} = {n / 2} by simp [this]
    ext y
    simp only [mem_filter, mem_singleton]
    constructor
    · intro ⟨hy₁, hy₂⟩
      have ⟨k, hk₁, hk₂⟩ := (Nat.mem_properDivisors_iff_exists (by omega)).mp hy₁
      rw [hk₂]
      have : k < 3 := lt_lemma (hk₂ ▸ hy₂) (by decide)
      simp [show k = 2 from Nat.eq_of_le_of_lt_succ hk₁ this]
    · intro hy
      rw [hy]
      exact ⟨mem_properDivisors' (by decide) h₁ h₃, by omega⟩

namespace Imo2025P4

/-- The type of sequences `aₙ` that satisfy the problem constraints -/
structure IsAllowed (a : ℕ → ℕ+) : Prop where
  atLeastThree : ∀ n, #(Nat.properDivisors (a n)) ≥ 3
  isSumOfPrevMaxThree : ∀ n,
    let divisors := sortedProperDivisors (a n)
    have : divisors.length ≥ 3 := by
      simp [divisors, atLeastThree]
    a (n + 1) = divisors[0] + divisors[1] + divisors[2]

/-- The set of all possible values of `a₀` that give allowed sequences -/
def A₀ := { a₀ | ∃ a, a 0 = a₀ ∧ IsAllowed a }

variable {x : ℕ+}

/-- A constant sequence from a number divisible by 2 and 3 but not by 4 and 5 is allowed -/
lemma isAllowed_of_constant (h₂ : 2 ∣ x.val) (h₃ : 3 ∣ x.val) (h₄ : ¬4 ∣ x.val) (h₅ : ¬5 ∣ x.val) : IsAllowed (fun _ => x) :=
  have h₆ : 6 ∣ x.val := by
    rw [show 6 = 2 * 3 from rfl]
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd <;> trivial

  have atLeastThree _ :=
    three_le_card_properDivisors_of_six_dvd h₆ x.pos

  have isSumOfPrevMaxThree _ := by
    dsimp
    apply Eq.trans <|
      show x.val = x / 2 + x / 3 + x / 6 by omega

    have : #x.val.properDivisors ≥ 3 := by
      simp [atLeastThree 0]

    have h₂' : x.val / 2 ∈ x.val.properDivisors := by
      apply mem_properDivisors' <;> omega
    have h₃' : x.val / 3 ∈ x.val.properDivisors := by
      apply mem_properDivisors' <;> omega

    congr
    · exact sortedProperDivisors_get_zero_eq_div_two h₂ x.pos
    · exact (sortedProperDivisors_get_one_eq_div_three h₂ h₃ x.pos).2
    · apply sortedProperDivisors_get (i := ⟨2, by omega⟩)
      · apply mem_properDivisors' <;> omega
      · suffices {y ∈ x.val.properDivisors | x.val / 6 < y} = {x.val / 2, x.val / 3} by
          rw [this, Finset.card_eq_two]
          refine ⟨_, _, ?_, rfl⟩
          omega
        ext y
        simp only [mem_filter, mem_insert, mem_singleton]
        constructor
        · intro ⟨hy₁, hy₂⟩
          have ⟨k, hk₁, hk₂⟩ := (Nat.mem_properDivisors_iff_exists (by omega)).mp hy₁
          rw [hk₂]
          have : k < 6 := lt_lemma (hk₂ ▸ hy₂) (by decide)
          match k with
          | 2 | 3 => simp
          | 4 | 5 => exfalso; omega
        · rintro (hy|hy)
          all_goals
            rw [hy]
            exact ⟨by assumption, by omega⟩

  { atLeastThree, isSumOfPrevMaxThree }

snip end

determine answer : Set ℕ+ :=
  { x | ∃ (k : ℕ) (m : ℕ+), x = 6 * 12^k * m ∧ ¬2 ∣ m ∧ ¬5 ∣ m }

problem imo2025_p4 : A₀ = answer := by
  ext x
  constructor
  case mpr => -- the easy direction
    intro ⟨k, m, hx, not_two_dvd_m, not_five_dvd_m⟩
    rw [hx]
    clear hx
    induction k generalizing m with
    | zero =>
      -- Use the constant sequence 6 * m, 6 * m, ...
      refine ⟨fun _ => 6 * m, rfl, ?_⟩
      apply isAllowed_of_constant
      · rw [show 6 * m = 2 * (3 * m) by ring]
        apply dvd_mul_right
      · rw [show 6 * m = 3 * (2 * m) by ring]
        apply dvd_mul_right
      · dsimp
        intro hn
        apply not_two_dvd_m
        rw [show 4 = 2 * 2 from rfl,
            show 6 * m.val = 2 * (3 * m) by ring] at hn
        rw [Nat.mul_dvd_mul_iff_left (by decide),
            Nat.Coprime.dvd_mul_left (by decide)] at hn
        rwa [PNat.dvd_iff]
      · dsimp
        intro hn
        apply not_five_dvd_m
        rw [Nat.Coprime.dvd_mul_left (by decide)] at hn
        rwa [PNat.dvd_iff]

    | succ k' ih =>
      let a : ℕ → ℕ+
        | 0 => 6 * 12 ^ (k' + 1) * m
        | _ => 6 * 12 ^ k' * (13 * m)

      use a
      have : (a 1 : ℕ) = (a 0 / 2) + (a 0 / 3) + (a 0 / 4) := by
        dsimp [a]
        grind
      have : 6 * 12 ^ k' * (13 * m) ∈ A₀ := by
        apply ih
        all_goals
          rw [PNat.dvd_iff, PNat.mul_coe, Nat.Coprime.dvd_mul_left, ←PNat.dvd_iff]
          <;> trivial
      refine ⟨rfl, ?_, ?_⟩
      · rintro (_|_)
        <;> apply three_le_card_properDivisors_of_six_dvd
        <;> simp [a, mul_assoc]
      · rintro (_|_)
        · simp
          convert_to (a 1 : ℕ) = (a 0 / 2) + (a 0 / 3) + (a 0 / 4)
          · congr
            · sorry
            · sorry
            · sorry
          · grind
        · sorry
  case mp => -- the hard direction
    intro ⟨a, ha, hx⟩
    sorry
