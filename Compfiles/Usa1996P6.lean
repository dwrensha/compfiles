/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karl Mehltretter
-/

import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics, .NumberTheory] }

/-!
# USA Mathematical Olympiad 1996, Problem 6

Determine, with proof, whether there is a subset X of the integers with
the following property: for any integer n there is exactly one pair (a, b)
of elements of X satisfying a + 2b = n.
-/

namespace Usa1996P6

def UniqueRepresentationSet (X : Set ℤ) : Prop :=
  ∀ n : ℤ, ∃! p : ℤ × ℤ,
    p.1 ∈ X ∧ p.2 ∈ X ∧ p.1 + 2 * p.2 = n

snip begin

def negFourValue {b : ℕ} (digits : List (Fin b)) : ℤ :=
  Nat.ofDigits (-4 : ℤ) (digits.map fun d ↦ d.val)

@[simp]
lemma negFourValue_nil {b : ℕ} : negFourValue ([] : List (Fin b)) = 0 := rfl

@[simp]
lemma negFourValue_cons {b : ℕ} (d : Fin b) (digits : List (Fin b)) :
    negFourValue (d :: digits) = d.val + (-4) * negFourValue digits := rfl

def lowBit (d : Fin 4) : Fin 2 :=
  match d.val with
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | _ => 1

def highBit (d : Fin 4) : Fin 2 :=
  match d.val with
  | 0 => 0
  | 1 => 0
  | _ => 1

lemma lowBit_add_two_mul_highBit (d : Fin 4) :
    (d.val : ℤ) = (lowBit d).val + 2 * (highBit d).val := by
  obtain ⟨d, hd⟩ := d
  have : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> rfl

lemma negFourQuotient_natAbs_lt (n : ℤ) (hn₀ : n ≠ 0) (hn₁ : n ≠ -1) :
    (n / (-4)).natAbs < n.natAbs := by
  have hrem0 : 0 ≤ n % (-4) := Int.emod_nonneg n (by decide)
  have hrem4 : n % (-4) < 4 := Int.emod_lt_abs n (by decide)
  have hdecomp := Int.emod_add_mul_ediv n (-4)
  by_cases hn : 0 ≤ n
  · have hnpos : 0 < n := by omega
    have hqnonpos : n / (-4) ≤ 0 := by omega
    have hqabs : ((n / (-4)).natAbs : ℤ) = -(n / (-4)) := by
      rw [← Int.natAbs_neg]
      exact Int.natAbs_of_nonneg (by omega)
    have hnabs : (n.natAbs : ℤ) = n := Int.natAbs_of_nonneg hn
    have hcast : ((n / (-4)).natAbs : ℤ) < (n.natAbs : ℤ) := by omega
    exact Int.ofNat_lt.mp hcast
  · have hnneg : n < 0 := lt_of_not_ge hn
    have hqpos : 0 ≤ n / (-4) := by omega
    have hqabs : ((n / (-4)).natAbs : ℤ) = n / (-4) :=
      Int.natAbs_of_nonneg hqpos
    have hnabs : (n.natAbs : ℤ) = -n := by
      rw [← Int.natAbs_neg]
      exact Int.natAbs_of_nonneg (by omega)
    have hcast : ((n / (-4)).natAbs : ℤ) < (n.natAbs : ℤ) := by omega
    exact Int.ofNat_lt.mp hcast

lemma exists_negFourExpansion (n : ℤ) :
    ∃ digits : List (Fin 4), negFourValue digits = n := by
  refine (measure Int.natAbs).wf.induction
    (C := fun n ↦ ∃ digits : List (Fin 4), negFourValue digits = n) n ?_
  intro x ih
  by_cases hx₀ : x = 0
  · subst x
    exact ⟨[], rfl⟩
  · by_cases hx₁ : x = -1
    · subst x
      refine ⟨[3, 1], ?_⟩
      norm_num [negFourValue, Nat.ofDigits]
    · have hmeasure := negFourQuotient_natAbs_lt x hx₀ hx₁
      obtain ⟨digits, hdigits⟩ := ih (x / (-4)) hmeasure
      have hrem0 : 0 ≤ x % (-4) := Int.emod_nonneg x (by decide)
      have hrem4 : x % (-4) < 4 := Int.emod_lt_abs x (by decide)
      have hdigit : (x % (-4)).toNat < 4 := by omega
      refine ⟨⟨(x % (-4)).toNat, hdigit⟩ :: digits, ?_⟩
      simp only [negFourValue, List.map_cons, Nat.ofDigits]
      change ((x % (-4)).toNat : ℤ) + (-4) * negFourValue digits = x
      rw [hdigits, Int.toNat_of_nonneg hrem0, Int.emod_add_mul_ediv]

lemma negFourValue_split (digits : List (Fin 4)) :
    negFourValue digits =
      negFourValue (digits.map lowBit) + 2 * negFourValue (digits.map highBit) := by
  induction digits with
  | nil => simp
  | cons d digits ih =>
    simp only [List.map_cons, negFourValue_cons]
    rw [ih, lowBit_add_two_mul_highBit]
    ring

def headBit : List (Fin 2) → Fin 2
  | [] => 0
  | d :: _ => d

lemma negFourValue_eq_headBit_add_tail (digits : List (Fin 2)) :
    negFourValue digits = headBit digits + (-4) * negFourValue digits.tail := by
  cases digits <;> rfl

lemma binary_pair_unique_aux (n : ℕ) (as bs cs ds : List (Fin 2))
    (hlen : as.length + bs.length + cs.length + ds.length ≤ n)
    (h : negFourValue as + 2 * negFourValue bs =
      negFourValue cs + 2 * negFourValue ds) :
    negFourValue as = negFourValue cs ∧ negFourValue bs = negFourValue ds := by
  induction n generalizing as bs cs ds with
  | zero =>
    have has : as = [] := List.length_eq_zero_iff.mp (by omega)
    have hbs : bs = [] := List.length_eq_zero_iff.mp (by omega)
    have hcs : cs = [] := List.length_eq_zero_iff.mp (by omega)
    have hds : ds = [] := List.length_eq_zero_iff.mp (by omega)
    subst as
    subst bs
    subst cs
    subst ds
    simp
  | succ n ih =>
    have htailLen : as.tail.length + bs.tail.length + cs.tail.length + ds.tail.length ≤ n := by
      simp only [List.length_tail]
      omega
    rw [negFourValue_eq_headBit_add_tail as, negFourValue_eq_headBit_add_tail bs,
      negFourValue_eq_headBit_add_tail cs, negFourValue_eq_headBit_add_tail ds] at h
    have hheads : ((headBit as).val : ℤ) + 2 * (headBit bs).val =
        (headBit cs).val + 2 * (headBit ds).val := by omega
    have hac : headBit as = headBit cs := by
      apply Fin.ext
      omega
    have hbd : headBit bs = headBit ds := by
      apply Fin.ext
      omega
    have htails : negFourValue as.tail + 2 * negFourValue bs.tail =
        negFourValue cs.tail + 2 * negFourValue ds.tail := by omega
    obtain ⟨hacTail, hbdTail⟩ := ih as.tail bs.tail cs.tail ds.tail htailLen htails
    constructor
    · rw [negFourValue_eq_headBit_add_tail as, negFourValue_eq_headBit_add_tail cs,
        hac, hacTail]
    · rw [negFourValue_eq_headBit_add_tail bs, negFourValue_eq_headBit_add_tail ds,
        hbd, hbdTail]

lemma binary_pair_unique (as bs cs ds : List (Fin 2))
    (h : negFourValue as + 2 * negFourValue bs =
      negFourValue cs + 2 * negFourValue ds) :
    negFourValue as = negFourValue cs ∧ negFourValue bs = negFourValue ds := by
  exact binary_pair_unique_aux
    (as.length + bs.length + cs.length + ds.length) as bs cs ds le_rfl h

snip end

determine does_exist : Bool := true

problem usa1996_p6 :
    does_exist ↔ ∃ X : Set ℤ, UniqueRepresentationSet X := by
  simp only [does_exist, true_iff]
  let X : Set ℤ := Set.range (negFourValue (b := 2))
  refine ⟨X, ?_⟩
  intro n
  obtain ⟨digits, hdigits⟩ := exists_negFourExpansion n
  let as := digits.map lowBit
  let bs := digits.map highBit
  have habs : negFourValue as + 2 * negFourValue bs = n := by
    rw [← hdigits, negFourValue_split]
  refine ⟨(negFourValue as, negFourValue bs), ?_, ?_⟩
  · exact ⟨Set.mem_range_self as, Set.mem_range_self bs, habs⟩
  · rintro ⟨a, b⟩ ⟨ha, hb, hab⟩
    change a ∈ X at ha
    change b ∈ X at hb
    obtain ⟨cs, rfl⟩ := ha
    obtain ⟨ds, rfl⟩ := hb
    have hvalues : negFourValue cs + 2 * negFourValue ds =
        negFourValue as + 2 * negFourValue bs := hab.trans habs.symm
    apply Prod.ext
    · exact (binary_pair_unique cs ds as bs hvalues).1
    · exact (binary_pair_unique cs ds as bs hvalues).2

end Usa1996P6
