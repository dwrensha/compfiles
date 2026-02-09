/-
Copyright (c) 2026 The Compfiles Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Rydh
-/

import Mathlib.Tactic
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Nat.Nth

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 1994, Problem 6

Show that there exists a set A of positive integers with the following
property: For any infinite set S of primes there exist two positive integers
m ∈ A and n ∉ A each of which is a product of k distinct elements of S for
some k ≥ 2.

-/

namespace Imo1994P6

def IsProductOfkDistinctMembers (x : ℕ) (k : ℕ) (S : Set ℕ) : Prop :=
  ∃ S' : Finset S, S'.card = k ∧ x = ∏ p ∈ S', p.val

snip begin

def Primes := { p : ℕ | p.Prime }
instance : Infinite Primes := Nat.infinite_setOf_prime.to_subtype
noncomputable def primes_iso : ℕ ≃o ↑Primes := Nat.Subtype.orderIsoOfNat Primes

-- Number of distinct prime factors of x
def ω : ℕ → ℕ := fun x ↦ (Nat.primeFactors x).card

lemma prod_of_primes {S : Set ℕ} {S' : Finset S} (h : ∀p ∈ S, p.Prime) :
  (∏ p ∈ S', p.val).primeFactors = S'.map ⟨Subtype.val, Subtype.val_injective⟩ := by
  have : ∏ p ∈ S', p.val = ∏ p ∈ S'.map ⟨Subtype.val, Subtype.val_injective⟩, p :=
    Eq.symm (Finset.prod_map S' { toFun := Subtype.val, inj' := Subtype.val_injective } fun x ↦ x)
  rw [this, Nat.primeFactors_prod]
  aesop

lemma orderiso_min_image {α : Type} [DecidableEq α] [LinearOrder α] (f : ℕ ≃o α) (k i : ℕ) (h₁ : 0 < k)
  : ((Finset.range k).image (fun j ↦ f (j + i))).min' (Finset.image_nonempty.mpr (Finset.nonempty_range_iff.mpr (Nat.ne_zero_of_lt h₁))) = f i := by
  let S := (Finset.range k).image (fun j ↦ f (j + i))
  have h_non_empty : S.Nonempty := by grind only [Finset.image_nonempty, Finset.nonempty_range_iff]
  have h' : S.min' h_non_empty = f i := by
    have h₄: ∀ j : ℕ, f i ≤ f (j + i) := by intro i ; aesop
    have h₅: f i ∈ S := by aesop
    have h₆: ∀x ∈ S, ∃j, x = f j := by grind
    rw [Finset.min'_eq_iff]
    grind
  grind only [Finset.coe_min']


lemma min_of_embedded {A : Set ℕ} (S : Finset A) (h : S.Nonempty) :
  (S.map ⟨Subtype.val, Subtype.val_injective⟩).min' (Finset.Nonempty.map h) = (S.min' h).val := by
  let T : Finset ℕ := S.map ⟨Subtype.val, Subtype.val_injective⟩
  apply le_antisymm
  · have hmem : (S.min' h).val ∈ T := by simp [T, Finset.min'_mem]
    exact Finset.min'_le T (↑(S.min' h)) hmem
  · apply Finset.le_min'
    intro x hx
    rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact Finset.min'_le S y hy

lemma prod_of_distinct_members (k i : ℕ) (S : Set ℕ) (f : ℕ ≃o S) : IsProductOfkDistinctMembers (∏ p ∈ ((Finset.range k).image (fun j ↦ f (j+i))), p) k S := by
  unfold IsProductOfkDistinctMembers
  let Sₘ := (Finset.range k).image (fun j ↦ f (j+i))
  let m : ℕ := ∏ p ∈ Sₘ, p
  use Sₘ
  have hinj : (fun j ↦ (f (j + i))).Injective := by grind only [Function.not_injective_iff, OrderIso.apply_eq_iff_eq]
  have : Sₘ.card = k := by
    unfold Sₘ
    rw [Finset.card_image_of_injective (Finset.range k) hinj]
    grind
  constructor
  · exact this
  · constructor

lemma primeFactors_card  {S : Set ℕ} (k i : ℕ) (f : ℕ ≃o S) (h : ∀ s ∈ S, s.Prime) : ω (∏ p ∈ ((Finset.range k).image (fun j ↦ f (j+i))), p) = k := by
  let Sₙ := (Finset.range k).image (fun j ↦ f (j+i))
  let n : ℕ := ∏ p ∈ Sₙ, p
  unfold ω
  rw [prod_of_primes h]
  simp
  rw [Finset.card_image_of_injective]
  · exact Finset.card_range k
  · exact fun _ _ h => Nat.add_right_cancel (f.injective h)

snip end



problem imo1994_p6 :
  ∃ A : Set ℕ, ∀ a ∈ A, 0 < a ∧ ∀ S : Set ℕ, Infinite S ∧ (∀ p ∈ S, p.Prime) →
    ∃ k m n : ℕ, 2 ≤ k ∧
      (m ∈ A ∧ 0 < m ∧ IsProductOfkDistinctMembers m k S) ∧
      (n ∉ A ∧ 0 < n ∧ IsProductOfkDistinctMembers n k S) := by
  -- Solution based on https://prase.cz/kalva/imo/isoln/isoln946.html
  -- Note that https://artofproblemsolving.com/wiki/index.php/1994_IMO_Problems/Problem_6
  -- interprets the problem differently, allowing m and n to be products of different
  -- numbers of primes, which is not what the original wording suggests.

  let A : Set ℕ := { x | ∃ h : 1 < x, primes_iso ((ω x) - 1) < (Nat.primeFactors x).min' (Nat.nonempty_primeFactors.mpr h) }
  use A
  intro a ha
  constructor
  · grind
  intro S ⟨hS_inf, hS_mem_prime⟩

  let pₛ := Nat.Subtype.orderIsoOfNat S

  -- Note: John Scholes' proof use the index of the smallest prime in S to construct k,
  -- but that might result in k being 1 (if 2 ∈ S). For that reason, we ignore the smallest
  -- prime in S, both when constructing k and when selecting prime factors for m and n.

  -- k is the number of factors to use when constructing m and n
  -- The order isomorphism is 0-based, so we add one
  let k := (primes_iso.symm ⟨pₛ 1, hS_mem_prime (pₛ 1).val (pₛ 1).val_prop⟩) + 1

  have hk_gt_two : 2 ≤ k := by
    unfold k
    simp
    have h₁ : 3 ≤ (pₛ 1).val := by
      have h : (pₛ 0).val < (pₛ 1).val := by
        simp_all only [Subtype.coe_lt_coe, OrderIso.lt_iff_lt, zero_lt_one, pₛ]
      have : (pₛ 0).val ∈ S := Subtype.coe_prop (pₛ 0)
      replace : (pₛ 0).val.Prime := hS_mem_prime (↑(pₛ 0)) this
      replace : 2 ≤ (pₛ 0).val := Nat.Prime.two_le this
      grind
    have h₂ : ∀ p, 3 ≤ p.val → 1 ≤ primes_iso.symm p := by
      intro p hp
      by_contra
      simp at this
      have : p.val = 2 := by
        unfold primes_iso at this
        have hq : ∀ q : ↑Primes, q ≤ p → (Nat.Subtype.orderIsoOfNat Primes).symm q ≤ (Nat.Subtype.orderIsoOfNat Primes).symm p := by
          exact fun _ hq ↦ (OrderIso.le_iff_le (Nat.Subtype.orderIsoOfNat Primes).symm).mpr hq
        rw [this] at hq
        replace hq : ∀ q ≤ p, (Nat.Subtype.orderIsoOfNat Primes).symm q = 0 := fun q a ↦ Nat.eq_zero_of_le_zero (hq q a)
        replace : p = Nat.Subtype.orderIsoOfNat Primes 0 := (OrderIso.symm_apply_eq (Nat.Subtype.orderIsoOfNat Primes)).mp this
        replace hq : ∀ q ≤ p, q = Nat.Subtype.orderIsoOfNat Primes 0 := fun q a ↦ (OrderIso.symm_apply_eq (Nat.Subtype.orderIsoOfNat Primes)).mp (hq q a)
        rw [←this] at hq
        let q : ↑Primes := ⟨2, Nat.prime_two⟩
        have hq_le : q ≤ p := Std.le_of_lt hp
        grind
      linarith
    exact Nat.one_le_of_lt (h₂ ⟨↑(pₛ 1), hS_mem_prime (↑(pₛ 1)) (Subtype.val_prop (pₛ 1))⟩ h₁)


  let Sⱼ := fun j ↦ (Finset.range k).image (fun i ↦ pₛ (i + j))

  have aux₁ {i : ℕ} : (primes_iso (ω (∏ p ∈ (Sⱼ i), p.val) - 1)).val = pₛ 1 := by
    rw [primeFactors_card k i pₛ hS_mem_prime]
    unfold k
    simp only [add_tsub_cancel_right, OrderIso.apply_symm_apply]

  have aux₃ {i : ℕ} : 1 < (∏ p ∈ (Sⱼ i), p.val) := by
    have hprime : ∀ x ∈ (Sⱼ i), x.val.Prime := by grind
    have h₁ : ∀ x ∈ (Sⱼ i), 1 < x.val := by intro x hx ; exact Nat.Prime.one_lt (hprime x hx)
    have h₂ : pₛ i ∈ (Sⱼ i) := by aesop
    have h₃ : 1 < (pₛ i).val := by grind
    have h₄ : ∃x ∈ (Sⱼ i), 1 < x.val := by use pₛ i
    exact (Finset.one_lt_prod_iff_of_one_le (fun x hx ↦ le_of_lt (h₁ x hx))).mpr h₄

  have aux₂ {i : ℕ} : (∏ p ∈ (Sⱼ i), p.val).primeFactors.min' (Nat.nonempty_primeFactors.mpr aux₃) = pₛ i := by
    have hnon_empty : (Sⱼ i).Nonempty := (Finset.image_nonempty.mpr (Finset.nonempty_range_iff.mpr (Nat.ne_zero_of_lt hk_gt_two)))
    have : (Sⱼ i).min' hnon_empty = pₛ i := by grind only [orderiso_min_image]
    conv => arg 1 ; arg 1 ; rw [prod_of_primes hS_mem_prime]
    rw [min_of_embedded (Sⱼ i) hnon_empty, this]


  -- Define m and prove m ∈ A
  let Sₘ := Sⱼ 2
  let m : ℕ := ∏ p ∈ Sₘ, p
  have hm_in_A : m ∈ A := by
    rw [Set.mem_setOf_eq, aux₁]
    use aux₃
    rw [aux₂]
    simp only [Subtype.coe_lt_coe, OrderIso.lt_iff_lt, Nat.one_lt_two]


  -- Define n and prove n ∉ A
  let Sₙ := Sⱼ 1
  let n : ℕ := ∏ p ∈ Sₙ, p
  have hn_nin_A : n ∉ A := by
    by_contra hn_in_A
    obtain ⟨_, hn₂⟩ := hn_in_A
    rw [aux₁, aux₂] at hn₂
    simp_all only [Subtype.coe_lt_coe, OrderIso.lt_iff_lt]
    exact (lt_self_iff_false 1).mp hn₂

  -- Prove that m and n are positive
  have hm_pos : 0 < m := Nat.zero_lt_of_lt aux₃
  have hn_pos : 0 < n := Nat.zero_lt_of_lt aux₃

  -- Prove that both m and n is the product of k primes from S
  have hm_prod : IsProductOfkDistinctMembers m k S := prod_of_distinct_members k 2 S pₛ
  have hn_prod : IsProductOfkDistinctMembers n k S := prod_of_distinct_members k 1 S pₛ
  use k, m, n

end Imo1994P6
