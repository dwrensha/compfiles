/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics, .NumberTheory] }

/-!
# International Mathematical Olympiad 1991, Problem 3

Let S = {1, 2, ..., 280}. Find the smallest natural number n such
that every n-element subset of S contains five numbers which are
pairwise relatively prime.
-/

namespace Imo1991P3

determine solution : ℕ := 217

snip begin

/-- The elements of `{1, ..., 280}` divisible by `2`, `3`, `5` or `7`.
Among any five of them, two share a common prime factor. -/
def badSet : Finset ℕ := (Finset.Icc 1 280).filter fun x => 2 ∣ x ∨ 3 ∣ x ∨ 5 ∣ x ∨ 7 ∣ x

/-- `1` together with all primes in `{1, ..., 280}`; pairwise coprime. -/
def coprimeSet1 : Finset ℕ :=
  {1, 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79,
   83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173,
   179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269,
   271, 277}

/-- `{2·41, 3·37, 5·31, 7·29, 11·23, 13·19}`; pairwise coprime. -/
def coprimeSet2 : Finset ℕ := {82, 111, 155, 203, 253, 247}

/-- `{2·37, 3·31, 5·29, 7·23, 11·19, 13·17}`; pairwise coprime. -/
def coprimeSet3 : Finset ℕ := {74, 93, 145, 161, 209, 221}

/-- `{2·31, 3·29, 5·23, 7·19, 11·17, 13·13}`; pairwise coprime. -/
def coprimeSet4 : Finset ℕ := {62, 87, 115, 133, 187, 169}

/-- `{2·29, 3·23, 5·19, 7·17, 11·13}`; pairwise coprime. -/
def coprimeSet5 : Finset ℕ := {58, 69, 95, 119, 143}

/-- `{2·23, 3·19, 5·17, 7·13, 11·11}`; pairwise coprime. -/
def coprimeSet6 : Finset ℕ := {46, 57, 85, 91, 121}

/-- The union of the six pairwise coprime families, all inside `{1, ..., 280}`. -/
def bigUnion : Finset ℕ :=
  coprimeSet1 ∪ coprimeSet2 ∪ coprimeSet3 ∪ coprimeSet4 ∪ coprimeSet5 ∪ coprimeSet6

set_option maxRecDepth 1000 in
lemma bigUnion_card : bigUnion.card = 88 := by decide

set_option maxRecDepth 1000 in
lemma bigUnion_subset : ∀ x ∈ bigUnion, x ∈ Finset.Icc 1 280 := by decide

set_option maxRecDepth 1000 in
lemma coprimeSet1_pairwise :
    ∀ a ∈ coprimeSet1, ∀ b ∈ coprimeSet1, a ≠ b → Nat.gcd a b = 1 := by decide

lemma coprimeSet2_pairwise :
    ∀ a ∈ coprimeSet2, ∀ b ∈ coprimeSet2, a ≠ b → Nat.gcd a b = 1 := by decide

lemma coprimeSet3_pairwise :
    ∀ a ∈ coprimeSet3, ∀ b ∈ coprimeSet3, a ≠ b → Nat.gcd a b = 1 := by decide

lemma coprimeSet4_pairwise :
    ∀ a ∈ coprimeSet4, ∀ b ∈ coprimeSet4, a ≠ b → Nat.gcd a b = 1 := by decide

lemma coprimeSet5_pairwise :
    ∀ a ∈ coprimeSet5, ∀ b ∈ coprimeSet5, a ≠ b → Nat.gcd a b = 1 := by decide

lemma coprimeSet6_pairwise :
    ∀ a ∈ coprimeSet6, ∀ b ∈ coprimeSet6, a ≠ b → Nat.gcd a b = 1 := by decide

/-- If `P ∩ T` has at least `5` elements and the elements of `P` are pairwise coprime,
then `T` contains five pairwise coprime numbers. -/
lemma five_of_subset {T P : Finset ℕ} (h : 5 ≤ (P ∩ T).card)
    (hp : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → Nat.gcd a b = 1) :
    ∃ U ⊆ T, U.card = 5 ∧ (U : Set ℕ).Pairwise Nat.Coprime := by
  obtain ⟨U, hUsub, hUcard⟩ := Finset.exists_subset_card_eq h
  refine ⟨U, fun x hx => (Finset.mem_inter.mp (hUsub hx)).2, hUcard, ?_⟩
  intro a ha b hb hab
  rw [Finset.mem_coe] at ha hb
  exact hp a (Finset.mem_inter.mp (hUsub ha)).1 b (Finset.mem_inter.mp (hUsub hb)).1 hab

/-- A prime in `{2, 3, 5, 7}` dividing `x`, whenever one exists. -/
def smallPrimeFactor (x : ℕ) : ℕ := if 2 ∣ x then 2 else if 3 ∣ x then 3 else if 5 ∣ x then 5 else 7

lemma smallPrimeFactor_mem (x : ℕ) : smallPrimeFactor x ∈ ({2, 3, 5, 7} : Finset ℕ) := by
  unfold smallPrimeFactor
  split_ifs <;> simp

lemma smallPrimeFactor_dvd {x : ℕ} (hx : x ∈ badSet) : smallPrimeFactor x ∣ x := by
  have hx' := Finset.mem_filter.mp hx
  unfold smallPrimeFactor
  split_ifs with h2 h3 h5
  · exact h2
  · exact h3
  · exact h5
  · rcases hx'.2 with h | h | h | h
    · exact absurd h h2
    · exact absurd h h3
    · exact absurd h h5
    · exact h

snip end

problem imo1991_p3 :
    IsLeast
      {n : ℕ | ∀ T ⊆ Finset.Icc 1 280, T.card = n →
        ∃ U ⊆ T, U.card = 5 ∧ (U : Set ℕ).Pairwise Nat.Coprime}
      solution := by
  rw [show solution = 217 from rfl]
  refine ⟨?_, ?_⟩
  · -- every 217-element subset contains five pairwise coprime numbers
    intro T hTsub hTcard
    have hScard : (Finset.Icc 1 280).card = 280 := by decide +kernel
    have hST : (Finset.Icc 1 280 \ T).card = 63 := by
      rw [Finset.card_sdiff_of_subset hTsub, hScard, hTcard]
    have hBT : 25 ≤ (bigUnion ∩ T).card := by
      have h2 := Finset.card_inter_add_card_sdiff bigUnion T
      rw [bigUnion_card] at h2
      have h3 : (bigUnion \ T).card ≤ 63 := by
        rw [← hST]
        apply Finset.card_le_card
        intro x hx
        rw [Finset.mem_sdiff] at hx ⊢
        exact ⟨bigUnion_subset _ hx.1, hx.2⟩
      omega
    have hsplit : (coprimeSet1 ∩ T) ∪ (coprimeSet2 ∩ T) ∪ (coprimeSet3 ∩ T) ∪
        (coprimeSet4 ∩ T) ∪ (coprimeSet5 ∩ T) ∪ (coprimeSet6 ∩ T) = bigUnion ∩ T := by
      change _ = (coprimeSet1 ∪ coprimeSet2 ∪ coprimeSet3 ∪ coprimeSet4 ∪ coprimeSet5 ∪
          coprimeSet6) ∩ T
      simp only [Finset.union_inter_distrib_right]
    have h1 := Finset.card_union_le
      (coprimeSet1 ∩ T ∪ coprimeSet2 ∩ T ∪ coprimeSet3 ∩ T ∪ coprimeSet4 ∩ T ∪
        coprimeSet5 ∩ T) (coprimeSet6 ∩ T)
    have h2 := Finset.card_union_le
      (coprimeSet1 ∩ T ∪ coprimeSet2 ∩ T ∪ coprimeSet3 ∩ T ∪ coprimeSet4 ∩ T)
      (coprimeSet5 ∩ T)
    have h3 := Finset.card_union_le
      (coprimeSet1 ∩ T ∪ coprimeSet2 ∩ T ∪ coprimeSet3 ∩ T) (coprimeSet4 ∩ T)
    have h4 := Finset.card_union_le (coprimeSet1 ∩ T ∪ coprimeSet2 ∩ T) (coprimeSet3 ∩ T)
    have h5 := Finset.card_union_le (coprimeSet1 ∩ T) (coprimeSet2 ∩ T)
    rw [← hsplit] at hBT
    have hge : 5 ≤ (coprimeSet1 ∩ T).card ∨ 5 ≤ (coprimeSet2 ∩ T).card ∨
        5 ≤ (coprimeSet3 ∩ T).card ∨ 5 ≤ (coprimeSet4 ∩ T).card ∨
        5 ≤ (coprimeSet5 ∩ T).card ∨ 5 ≤ (coprimeSet6 ∩ T).card := by omega
    rcases hge with h | h | h | h | h | h
    · exact five_of_subset h coprimeSet1_pairwise
    · exact five_of_subset h coprimeSet2_pairwise
    · exact five_of_subset h coprimeSet3_pairwise
    · exact five_of_subset h coprimeSet4_pairwise
    · exact five_of_subset h coprimeSet5_pairwise
    · exact five_of_subset h coprimeSet6_pairwise
  · -- no n < 217 works: the multiples of 2, 3, 5 or 7 give a bad set of size 216
    intro n hn
    by_contra hcon
    push Not at hcon
    have hbadcard : badSet.card = 216 := by decide +kernel
    obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq (show n ≤ badSet.card by omega)
    have hTIcc : T ⊆ Finset.Icc 1 280 := fun x hx => (Finset.mem_filter.mp (hTsub hx)).1
    obtain ⟨U, hUT, hUcard, hUpair⟩ := hn T hTIcc hTcard
    have hUbad : U ⊆ badSet := fun x hx => hTsub (hUT hx)
    have hmaps : Set.MapsTo smallPrimeFactor (U : Set ℕ) ({2, 3, 5, 7} : Finset ℕ) :=
      fun x _ => Finset.mem_coe.mpr (smallPrimeFactor_mem x)
    have hcardlt : ({2, 3, 5, 7} : Finset ℕ).card < U.card := by
      rw [hUcard]
      decide
    obtain ⟨a, ha, b, hb, hab, hfab⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcardlt hmaps
    have hcop : Nat.gcd a b = 1 := hUpair (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab
    have hadvd : smallPrimeFactor a ∣ a := smallPrimeFactor_dvd (hUbad ha)
    have hbdvd : smallPrimeFactor b ∣ b := smallPrimeFactor_dvd (hUbad hb)
    rw [← hfab] at hbdvd
    have hdiv : smallPrimeFactor a ∣ Nat.gcd a b := Nat.dvd_gcd hadvd hbdvd
    rw [hcop] at hdiv
    have hle1 : smallPrimeFactor a ≤ 1 := Nat.le_of_dvd one_pos hdiv
    have hge2 : 2 ≤ smallPrimeFactor a := by
      have h := smallPrimeFactor_mem a
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h | h | h <;> omega
    omega

end Imo1991P3
