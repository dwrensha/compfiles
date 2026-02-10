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

lemma minFac_prod_primes {S : Set ℕ} (k i : ℕ) (f : ℕ ≃o S)
    (hS : ∀ s ∈ S, s.Prime) (hk : 0 < k) :
    (∏ p ∈ (Finset.range k).image (fun j ↦ f (j + i)), (p : ℕ)).minFac = (f i).val := by
  set Sf := (Finset.range k).image (fun j ↦ f (j + i))
  have hfi_mem : f i ∈ Sf :=
    Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hk, by simp⟩
  have hfi_prime : ((f i) : ℕ).Prime := hS _ (f i).prop
  have hprod_ne_one : ∏ p ∈ Sf, (p : ℕ) ≠ 1 := by
    intro h
    exact absurd ((Finset.prod_eq_one_iff_of_one_le'
      (fun x hx ↦ (hS x.val x.prop).one_le)).mp h _ hfi_mem) hfi_prime.one_lt.ne'
  apply le_antisymm
  · exact Nat.minFac_le_of_dvd hfi_prime.two_le (Finset.dvd_prod_of_mem _ hfi_mem)
  · -- minFac is prime and divides the product, so it divides some prime factor
    have hmf_prime := Nat.minFac_prime hprod_ne_one
    obtain ⟨a, ha_mem, hmf_dvd_a⟩ :=
      (hmf_prime.prime.dvd_finset_prod_iff _).mp (Nat.minFac_dvd _)
    -- Since both minFac and a.val are prime, minFac = a.val
    have : (∏ p ∈ Sf, (p : ℕ)).minFac = a.val := by
      cases (hS a.val a.prop).eq_one_or_self_of_dvd _ hmf_dvd_a with
      | inl h => exact absurd h hmf_prime.one_lt.ne'
      | inr h => exact h
    -- And a = f(j+i) for some j ≥ 0, so a.val ≥ (f i).val
    rw [this]
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha_mem
    exact (f.monotone (Nat.le_add_left i j))

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
  exact ⟨this, rfl⟩

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
  ∃ A : Set ℕ, (∀ a ∈ A, 0 < a) ∧ ∀ S : Set ℕ, Infinite S ∧ (∀ p ∈ S, p.Prime) →
    ∃ k m n : ℕ, 2 ≤ k ∧
      (m ∈ A ∧ 0 < m ∧ IsProductOfkDistinctMembers m k S) ∧
      (n ∉ A ∧ 0 < n ∧ IsProductOfkDistinctMembers n k S) := by
  -- Solution based on https://prase.cz/kalva/imo/isoln/isoln946.html
  -- A = { x > 1 | the (ω(x)-1)-th prime < x's smallest prime factor }
  let A : Set ℕ := { x | 1 < x ∧ (primes_iso ((ω x) - 1)).val < x.minFac }
  use A
  refine ⟨fun a ⟨h, _⟩ ↦ by lia, ?_⟩
  intro S ⟨hS_inf, hS_mem_prime⟩
  let pₛ := Nat.Subtype.orderIsoOfNat S
  -- k = index of pₛ(1) among all primes + 1
  let k := (primes_iso.symm ⟨pₛ 1, hS_mem_prime (pₛ 1).val (pₛ 1).val_prop⟩) + 1

  have hk_ge_two : 2 ≤ k := by
    -- pₛ(0) < pₛ(1) as primes, so their indices in the global enumeration differ
    show 2 ≤ primes_iso.symm ⟨↑(pₛ 1), hS_mem_prime _ (pₛ 1).val_prop⟩ + 1
    have : (⟨(pₛ 0).val, hS_mem_prime _ (pₛ 0).prop⟩ : Primes) <
           ⟨(pₛ 1).val, hS_mem_prime _ (pₛ 1).prop⟩ :=
      Subtype.mk_lt_mk.mpr (pₛ.strictMono (by lia))
    have := primes_iso.symm.strictMono this
    lia

  let Sⱼ := fun j ↦ (Finset.range k).image (fun i ↦ pₛ (i + j))

  -- Key fact 1: primes_iso(ω(product) - 1) = pₛ(1) for any starting index
  have aux₁ {i : ℕ} : (primes_iso (ω (∏ p ∈ (Sⱼ i), p.val) - 1)).val = (pₛ 1).val := by
    rw [primeFactors_card k i pₛ hS_mem_prime]; simp [k]

  -- Key fact 2: minFac of the product = pₛ(starting index)
  have aux₂ {i : ℕ} : (∏ p ∈ (Sⱼ i), p.val).minFac = (pₛ i).val :=
    minFac_prod_primes k i pₛ hS_mem_prime (by lia)

  -- Key fact 3: the product is > 1
  have aux₃ {i : ℕ} : 1 < (∏ p ∈ (Sⱼ i), p.val) := by
    have hmem : pₛ i ∈ Sⱼ i := Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by lia), by simp⟩
    exact (Finset.one_lt_prod_iff_of_one_le
      (fun x hx ↦ (hS_mem_prime x.val x.prop).one_le)).mpr
      ⟨pₛ i, hmem, (hS_mem_prime _ (pₛ i).prop).one_lt⟩

  -- m = product of k primes starting from pₛ(2); m ∈ A since pₛ(1) < pₛ(2) = minFac(m)
  let m : ℕ := ∏ p ∈ Sⱼ 2, p
  have hm_in_A : m ∈ A := ⟨aux₃, by rw [aux₁, aux₂]; exact pₛ.strictMono (by lia)⟩

  -- n = product of k primes starting from pₛ(1); n ∉ A since pₛ(1) = minFac(n), not <
  let n : ℕ := ∏ p ∈ Sⱼ 1, p
  have hn_nin_A : n ∉ A := by
    intro ⟨_, h⟩; rw [aux₁, aux₂] at h; exact lt_irrefl _ h

  exact ⟨k, m, n, hk_ge_two,
    ⟨hm_in_A, Nat.zero_lt_of_lt aux₃, prod_of_distinct_members k 2 S pₛ⟩,
    ⟨hn_nin_A, Nat.zero_lt_of_lt aux₃, prod_of_distinct_members k 1 S pₛ⟩⟩

end Imo1994P6
