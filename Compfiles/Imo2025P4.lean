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
Problem text:
- A proper divisor of a positive integer N is a positive divisor of N other than N itself.

  The infinite sequence a₁, a₂, ... consists of positive integers, each of which has at least three proper
  divisors. For each n ≥ 1, the integer aₙ + 1 is the sum of the three largest proper divisors of aₙ.
  Determine all possible values of a₁.
Proof follows https://www.youtube.com/watch?v=Kb4h_GVFT1k
-/

open Finset
open Nat

snip begin

namespace Imo2025P4

section BasicLemmas

@[simp]
lemma two_dvd_six_mul (x) : 2 ∣ 6 * x := by
  rw [show 6 = 2 * 3 by rfl, mul_assoc]
  apply Nat.dvd_mul_right

@[simp]
lemma three_dvd_six_mul (x) : 3 ∣ 6 * x := by
  rw [show 6 = 3 * 2 by rfl, mul_assoc]
  apply Nat.dvd_mul_right

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

/-- Like `mem_properDivisors.mpr`, but for the multiplicative inverse -/
lemma mem_properDivisors' {n m : ℕ} (h₁ : n > 1) (h₂ : n ∣ m) (h₃ : 0 < m) : (m / n) ∈ m.properDivisors := by
  rw [mem_properDivisors]
  constructor
  · exact div_dvd_of_dvd h₂
  · exact div_lt_self h₃ h₁

lemma three_le_card_properDivisors_of_six_dvd {n : ℕ} (h₁ : 6 ∣ n) (h₂ : n > 0) : 3 ≤ #n.properDivisors := by
  rw [Finset.le_card_iff_exists_subset_card]
  refine ⟨{ 1, 2, 3 }, ?_, rfl⟩
  simp only [insert_subset_iff, singleton_subset_iff]
  repeat rw [Nat.mem_properDivisors]
  omega

end BasicLemmas

/-- The proper divisors of `n`, sorted in decreasing order. -/
def sortedProperDivisors (n : ℕ) : List ℕ :=
  (Nat.properDivisors n).sort GE.ge

variable {n : ℕ}

section SortedProperDivisors

@[simp]
lemma length_sortedProperDivisors : (sortedProperDivisors n).length = #n.properDivisors := by
  simp [sortedProperDivisors]

lemma mem_properDivisors_iff_mem_sortedProperDivisors :
    ∀ {d}, d ∈ n.properDivisors ↔ d ∈ sortedProperDivisors n := by
  simp [sortedProperDivisors]

@[simp]
lemma mem_properDivisors_of_getElem (i : ℕ)
    (hi : i < #n.properDivisors := by first
      | get_elem_tactic
      | rw [←length_sortedProperDivisors]; get_elem_tactic)
    : (sortedProperDivisors n)[i]'(by simp [hi]) ∈ n.properDivisors := by
  rw [mem_properDivisors_iff_mem_sortedProperDivisors]
  apply List.mem_of_getElem (i := i) <;> trivial


lemma sortedProperDivisors_sorted (n : ℕ) :
    List.Sorted GT.gt (sortedProperDivisors n) :=
  n.properDivisors.sort_sorted_gt

lemma sortedProperDivisors_strictAnti (n : ℕ) :
    StrictAnti (sortedProperDivisors n).get :=
  fun _ _ h => (sortedProperDivisors_sorted n).rel_get_of_lt h

/-- The core theorem that establishes where a divisor appears in `sortedProperDivisors`. -/
theorem sortedProperDivisors_get {i : Fin #n.properDivisors} {x : ℕ}
    (hx₁ : x ∈ n.properDivisors) (hx₂ : #{y ∈ n.properDivisors | y > x} = i)
    : x = (sortedProperDivisors n)[i] := by
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
    · apply mem_properDivisors_of_getElem j
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

theorem sortedProperDivisors_get_zero_eq_div_two (h₁ : 2 ∣ n) (h₂ : n > 0) : n / 2 = (sortedProperDivisors n).get ⟨0, by simp; omega⟩ := by
  apply sortedProperDivisors_get (i := ⟨0, by simp; omega⟩)
  · apply mem_properDivisors' <;> omega
  · simp only [Finset.card_eq_zero, filter_eq_empty_iff]
    intro d hd₁ hd₂
    have := le_div_two_of_mem_properDivisors d hd₁
    exact Nat.not_le_of_gt hd₂ this

lemma lt_of_mul_div_lt {y k l : ℕ} (h₁ : y * k / l < y) (h₂ : l > 0) : k < l :=
  have := lt_of_le_of_lt (Nat.mul_div_le_mul_div_assoc ..) h₁
  have := lt_one_of_mul_lt_right this
  (Nat.div_lt_one_iff h₂).mp this

theorem sortedProperDivisors_get_one_eq_div_three (h₁ : 2 ∣ n) (h₂ : 3 ∣ n) (h₃ : n > 0) : ∃ pf, n / 3 = (sortedProperDivisors n).get ⟨1, pf⟩ := by
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
      have : k < 3 := lt_of_mul_div_lt (hk₂ ▸ hy₂) (by decide)
      simp [show k = 2 from Nat.eq_of_le_of_lt_succ hk₁ this]
    · intro hy
      rw [hy]
      exact ⟨mem_properDivisors' (by decide) h₁ h₃, by omega⟩

theorem sortedProperDivisors_get_two_eq
    (hn₁ : 2 ∣ n) (hn₂ : 3 ∣ n) (hn₃ : n > 0)
    {d : ℕ} (hd₁ : d > 3) (hd₂ : ∀ x, 3 < x → x < d → ¬x ∣ n) (hd₃ : d ∣ n)
    : ∃ pf, n / d = (sortedProperDivisors n).get ⟨2, pf⟩ := by
  have two_lt_length : 2 < (sortedProperDivisors n).length := by
    rw [sortedProperDivisors, length_sort]
    apply three_le_card_properDivisors_of_six_dvd
    <;> omega
  use two_lt_length
  apply sortedProperDivisors_get (i := ⟨2, by rwa [←length_sortedProperDivisors]⟩)
  · apply mem_properDivisors' <;> omega
  · rw [card_eq_two]
    use n / 2, n / 3
    constructor
    · omega
    · ext y
      simp only [mem_filter, mem_insert, mem_singleton]
      constructor
      · intro ⟨hy₁, hy₂⟩
        have ⟨k, hk₁, hk₂⟩ := (Nat.mem_properDivisors_iff_exists (Nat.ne_zero_of_lt hn₃)).mp hy₁
        suffices k < 4 by
          match k with | 2 | 3 => simp [hk₂]

        apply Nat.lt_succ_of_le
        apply Nat.le_of_not_gt
        intro hn
        apply hd₂ k hn
        · apply lt_of_mul_div_lt (y := y)
          · rwa [←hk₂]
          · exact lt_trans (by decide) hd₁
        · exact Dvd.intro_left _ hk₂.symm
      · rintro (hy|hy)
        all_goals
          rw [hy]
          constructor
          · exact mem_properDivisors' (by decide) ‹_› hn₃
          · rw [gt_iff_lt, Nat.div_lt_div_left (Nat.ne_zero_of_lt hn₃) hd₃ ‹_›]
            first | exact hd₁ | exact lt_trans (by decide) hd₁

lemma le_div_succ_of_lt_div_of_dvd {x a b : ℕ} (h₁ : x < a / b) (h₂ : x ∣ a) : x ≤ a / (b + 1) := by
  have ⟨k, hk⟩ := h₂
  rw [hk] at ⊢ h₁
  refine le_trans ?_ (Nat.mul_div_le_mul_div_assoc _ _ _)
  apply Nat.le_mul_of_pos_right x
  apply Nat.div_pos
  · show b < k
    rw [Nat.lt_div_iff_mul_lt (Nat.pos_of_ne_zero fun hb => by simp_all)] at h₁
    replace h₁ := Nat.add_lt_of_lt_sub h₁
    replace h₁ := Nat.lt_of_add_right_lt h₁
    exact Nat.lt_of_mul_lt_mul_left h₁
  · apply zero_lt_succ

/-- The greatest proper divisor is always `≤ n / 2`, the second greatest `≤ n / 3`, etc. -/
theorem sortedProperDivisors_get_le {i : Fin #(properDivisors n)} : (sortedProperDivisors n)[i] ≤ n / (i + 2) := by
  replace ⟨i, hi⟩ := i
  induction i with
  | zero =>
    apply le_div_two_of_mem_properDivisors
    simp only [sortedProperDivisors, ←Finset.mem_sort GE.ge]
    exact List.mem_of_getElem rfl
  | succ i ih =>
    have _ : i + 1 < (sortedProperDivisors n).length := by simp [*]
    have _ : i < (sortedProperDivisors n).length := lt_of_succ_lt ‹_›
    simp [Fin.getElem_fin] at ⊢ ih
    suffices (sortedProperDivisors n)[i + 1] < n / (i + 2) by
      rw [show i + 1 + 2 = (i + 2) + 1 by ring]
      apply le_div_succ_of_lt_div_of_dvd this
      apply And.left ∘ Nat.mem_properDivisors.mp
      apply mem_properDivisors_of_getElem (i + 1)
    apply lt_of_lt_of_le (b := (sortedProperDivisors n)[i])
    · apply sortedProperDivisors_strictAnti
      simp
    · exact ih (lt_of_succ_lt hi)

end SortedProperDivisors

section ProblemTheory -- The more advanced theorems and definitions needed for the problem

/-- The sum of the biggest three proper divisors of `n`. -/
def threeDivisorSum (n : ℕ) (h : #n.properDivisors ≥ 3) : ℕ+ :=
  let divisors := sortedProperDivisors n
  have : divisors.length ≥ 3 := by
    simp [divisors, h]
  Subtype.mk (divisors[0] + divisors[1] + divisors[2]) <| by
    apply Nat.add_pos_right
    apply Nat.pos_of_mem_properDivisors (n := n)
    apply mem_properDivisors_of_getElem 2

lemma threeDivisorSum_eq_thirteen_mul_self_div_twelve_of_twelve_dvd (h₁ : 12 ∣ n) (h₂ : n > 0) : ∃ pf, threeDivisorSum n pf = 13 * n / 12 := by
  have three_le_length : 3 ≤ #n.properDivisors := by
    apply three_le_card_properDivisors_of_six_dvd <;> omega
  use three_le_length

  simp only [threeDivisorSum, PNat.mk_coe,
             show 13 * n / 12 = n / 2 + n / 3 + n / 4 by grind]
  congr <;> symm
  · apply sortedProperDivisors_get_zero_eq_div_two <;> omega
  · refine (sortedProperDivisors_get_one_eq_div_three ?_ ?_ ?_).2 <;> omega
  · refine (sortedProperDivisors_get_two_eq ?_ ?_ ?_ ?_ ?_ ?_).2 <;> omega

lemma threeDivisorSum_lt_self_of_odd (h₁ : ¬2 ∣ n) (h₂ : #n.properDivisors ≥ 3) : threeDivisorSum n h₂ < n := by
  -- In the video n ↦ n/3 + n/5 + n/7, but this bound is easier to show
  -- because the two later terms are handled by `sortedProperDivisors_get_le`
  refine lt_of_le_of_lt (b := n / 3 + n / 3 + n / 4) ?_ (by omega)
  simp [threeDivisorSum]
  apply Nat.add_le_add
  · apply Nat.add_le_add
    · have := sortedProperDivisors_get_le (n := n) (i := ⟨0, by omega⟩)
      simp only [Fin.getElem_fin, zero_add] at this
      have _ : (sortedProperDivisors n).length ≥ 3 := by
        simp [h₂]
      have : (sortedProperDivisors n)[0] ∈ properDivisors n :=
        mem_properDivisors_of_getElem 0
      have ⟨k, hk₁, hk₂⟩ := (mem_properDivisors_iff_exists (by omega)).mp this
      conv => rhs; rw [hk₂]
      rw [Nat.le_div_iff_mul_le (by decide)]
      apply Nat.mul_le_mul_left
      match k with
      | 2 =>
        exfalso
        apply h₁
        use (sortedProperDivisors n)[0]
        rwa [mul_comm]
      | _ + 3 => omega
    · apply sortedProperDivisors_get_le (i := ⟨1, by omega⟩)
  · apply sortedProperDivisors_get_le (i := ⟨2, by omega⟩)

/-- The type of sequences `aₙ` that satisfy the problem constraints -/
structure IsAllowed (a : ℕ → ℕ+) : Prop where
  atLeastThree : ∀ n, #(Nat.properDivisors (a n)) ≥ 3
  isSumOfPrevMaxThree : ∀ n,
    a (n + 1) = threeDivisorSum (a n) (atLeastThree n)

/-- The set of all possible values of `a₀` that give allowed sequences -/
def A₀ := { a₀ | ∃ a, a 0 = a₀ ∧ IsAllowed a }

/-- Some `a₀` is in `A₀` if the next value (under `threeDivisorSum`) is in `A₀`. -/
-- N.B. I think this is also true in the other direction but we don't need it yet
theorem mem_A₀_of_threeDivisorSum_mem_A₀ {a₀ : ℕ+} (h₁ : #a₀.val.properDivisors ≥ 3) (h₂ : threeDivisorSum a₀ h₁ ∈ A₀) : a₀ ∈ A₀ := by
  have ⟨a, ha₁, ha₂, ha₃⟩ := h₂
  let a' : ℕ → ℕ+
    | 0 => a₀
    | i + 1 => a i

  refine ⟨a', rfl, ?_, ?_⟩
  · rintro ⟨_, _⟩
    · exact h₁
    · simp [a', ha₂]
  · rintro ⟨_, _⟩
    · simp [a', ha₁]
    · rename_i k
      simp [a', ha₃]

theorem even_of_mem_A₀ {a₀ : ℕ+} (h : a₀ ∈ A₀) : 2 ∣ a₀ := by
  by_contra hn
  have ⟨a, ha₁, ha₂, ha₃⟩ := h
  have := ha₃ 0
  simp_rw [ha₁, zero_add] at this
  suffices ∀ n, a n > a (n + 1) by
    sorry
  sorry

/-- A constant sequence from a number divisible by 2 and 3 but not by 4 and 5 is allowed -/
lemma isAllowed_of_constant {x : ℕ+} (h₂ : 2 ∣ x.val) (h₃ : 3 ∣ x.val) (h₄ : ¬4 ∣ x.val) (h₅ : ¬5 ∣ x.val) : IsAllowed (fun _ => x) :=
  have h₆ : 6 ∣ x.val := by
    rw [show 6 = 2 * 3 from rfl]
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd <;> trivial

  have atLeastThree _ :=
    three_le_card_properDivisors_of_six_dvd h₆ x.pos

  have isSumOfPrevMaxThree _ := by
    apply PNat.eq
    apply Eq.trans <|
      show x.val = x / 2 + x / 3 + x / 6 by omega
    congr
    · exact sortedProperDivisors_get_zero_eq_div_two h₂ x.pos
    · exact (sortedProperDivisors_get_one_eq_div_three h₂ h₃ x.pos).2
    · refine (sortedProperDivisors_get_two_eq h₂ h₃ x.pos (by decide) ?_ h₆).2
      intro y _ _
      match y with
      | 4 | 5 => assumption

  { atLeastThree, isSumOfPrevMaxThree }

end ProblemTheory

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
      · simp
      · simp
      · dsimp
        intro hn
        apply not_two_dvd_m
        rw [show 4 = 2 * 2 from rfl,
            show 6 * m.val = 2 * (3 * m) by ring,
            Nat.mul_dvd_mul_iff_left (by decide),
            Nat.Coprime.dvd_mul_left (by decide)] at hn
        rwa [PNat.dvd_iff]
      · dsimp
        intro hn
        apply not_five_dvd_m
        rw [Nat.Coprime.dvd_mul_left (by decide)] at hn
        rwa [PNat.dvd_iff]
    | succ k' ih =>
      apply mem_A₀_of_threeDivisorSum_mem_A₀
      · convert_to 6 * 12 ^ k' * (13 * m) ∈ A₀
        · simp only [PNat.mul_coe, PNat.val_ofNat, PNat.pow_coe]
          have := (threeDivisorSum_eq_thirteen_mul_self_div_twelve_of_twelve_dvd
            (n := 6 * 12 ^ (k' + 1) * ↑m) ?_ ?_).2
          · apply PNat.eq
            rw [this]
            simp only [PNat.mul_coe, PNat.val_ofNat, PNat.pow_coe]
            ring_nf
            rw [Nat.mul_div_assoc _ (by decide)]
            congr
          · simp_rw [pow_succ', ←mul_assoc, mul_comm 6, mul_assoc, dvd_mul_right]
          · simp
        · apply ih
          <;> rw [PNat.dvd_iff, PNat.mul_coe, Nat.Coprime.dvd_mul_left, ←PNat.dvd_iff]
          <;> trivial
      · apply three_le_card_properDivisors_of_six_dvd
        · simp [mul_assoc]
        · simp

  case mp => -- the hard direction
    intro ⟨a, ha, hx⟩
    sorry
