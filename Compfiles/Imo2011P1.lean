/-
Copyright (c) 2026 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 2011, Problem 1

Given any set A = {a₁, a₂, a₃, a₄} of four distinct positive integers,
we denote the sum a₁ + a₂ + a₃ + a₄ by s_A. Let n_A denote the number
of pairs (i, j) with 1 ≤ i < j ≤ 4 for which a_i + a_j divides s_A.
Find all sets A of four distinct positive integers which achieve the
largest possible value of n_A.
-/

namespace Imo2011P1

/-- The number of two-element subsets of `A` whose sum divides the sum of `A`. -/
def pairCount (A : Finset ℕ) : ℕ :=
  ((A.powersetCard 2).filter fun p ↦ (∑ x ∈ p, x) ∣ ∑ x ∈ A, x).card

determine SolutionSet : Set (Finset ℕ) :=
  { A | ∃ c : ℕ, 0 < c ∧
        (A = {c, 5 * c, 7 * c, 11 * c} ∨ A = {c, 11 * c, 19 * c, 29 * c}) }

snip begin

lemma mem_pair {x u v : ℕ} (h : x ∈ ({u, v} : Finset ℕ)) : x = u ∨ x = v := by
  simpa using h

lemma pair_ne_pair {p q r s : ℕ} (h : (p ≠ r ∧ p ≠ s) ∨ (q ≠ r ∧ q ≠ s)) :
    ({p, q} : Finset ℕ) ≠ {r, s} := by
  intro he
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hp : p ∈ ({r, s} : Finset ℕ) := by rw [← he]; simp
    rcases mem_pair hp with rfl | rfl
    · exact h1 rfl
    · exact h2 rfl
  · have hq : q ∈ ({r, s} : Finset ℕ) := by rw [← he]; simp
    rcases mem_pair hq with rfl | rfl
    · exact h1 rfl
    · exact h2 rfl

/-- A natural number strictly between `m` and `2 * m` is not divisible by `m`. -/
lemma not_dvd_between {m s : ℕ} (h1 : m < s) (h2 : s < 2 * m) : ¬ m ∣ s := fun h ↦
  absurd (Nat.eq_of_dvd_of_lt_two_mul (by lia) h h2) (by lia)

lemma pair_mem_powersetCard_two {A : Finset ℕ} {x y : ℕ}
    (hx : x ∈ A) (hy : y ∈ A) (hxy : x ≠ y) : ({x, y} : Finset ℕ) ∈ A.powersetCard 2 :=
  Finset.mem_powersetCard.mpr
    ⟨Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy), Finset.card_pair hxy⟩

lemma sum_four {a b c d : ℕ} (hab : a < b) (hbc : b < c) (hcd : c < d) :
    ∑ x ∈ ({a, b, c, d} : Finset ℕ), x = a + b + c + d := by
  rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; lia),
      Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; lia),
      Finset.sum_insert (by simp only [Finset.mem_singleton]; lia),
      Finset.sum_singleton]
  ring

/-- The two-element subsets of `{a, b, c, d}` whose sum divides the total,
viewed inside `pairCount`. -/
lemma filter_subset_target {a b c d : ℕ} (hab : a < b) (hbc : b < c) (hcd : c < d) :
    ((({a, b, c, d} : Finset ℕ).powersetCard 2).filter
        fun p ↦ (∑ x ∈ p, x) ∣ ∑ x ∈ ({a, b, c, d} : Finset ℕ), x) ⊆
      ((({a, b, c, d} : Finset ℕ).powersetCard 2) \ {({b, d} : Finset ℕ), {c, d}}) := by
  have hS : ∑ x ∈ ({a, b, c, d} : Finset ℕ), x = a + b + c + d := sum_four hab hbc hcd
  intro p hp
  rw [Finset.mem_filter] at hp
  rw [Finset.mem_sdiff]
  refine ⟨hp.1, fun hbad ↦ ?_⟩
  rw [Finset.mem_insert, Finset.mem_singleton] at hbad
  have hp2 := hp.2
  rw [hS] at hp2
  rcases hbad with rfl | rfl
  · rw [Finset.sum_pair (by lia : b ≠ d)] at hp2
    exact not_dvd_between (by lia) (by lia) hp2
  · rw [Finset.sum_pair (by lia : c ≠ d)] at hp2
    exact not_dvd_between (by lia) (by lia) hp2

lemma card_target {a b c d : ℕ} (hab : a < b) (hbc : b < c) (hcd : c < d) :
    ((({a, b, c, d} : Finset ℕ).powersetCard 2) \
      {({b, d} : Finset ℕ), {c, d}}).card = 4 := by
  have hsub : ({({b, d} : Finset ℕ), {c, d}} : Finset (Finset ℕ)) ⊆
      ({a, b, c, d} : Finset ℕ).powersetCard 2 :=
    Finset.insert_subset (pair_mem_powersetCard_two (by simp) (by simp) (by lia))
      (Finset.singleton_subset_iff.mpr
        (pair_mem_powersetCard_two (by simp) (by simp) (by lia)))
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, Finset.card_powersetCard,
      Finset.card_pair (pair_ne_pair (Or.inl ⟨by lia, by lia⟩))]
  have hA4 : ({a, b, c, d} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem
          (by simp only [Finset.mem_insert, Finset.mem_singleton]; lia),
        Finset.card_insert_of_notMem
          (by simp only [Finset.mem_insert, Finset.mem_singleton]; lia),
        Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; lia),
        Finset.card_singleton]
  rw [hA4]
  decide

lemma pairCount_le_four {a b c d : ℕ} (hab : a < b) (hbc : b < c) (hcd : c < d) :
    pairCount {a, b, c, d} ≤ 4 := by
  rw [pairCount, ← card_target hab hbc hcd]
  exact Finset.card_le_card (filter_subset_target hab hbc hcd)

/-- If the count is (at least) 4, then all four candidate pairs divide the sum. -/
lemma dvds_of_four_le {a b c d : ℕ} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (h : 4 ≤ pairCount {a, b, c, d}) :
    (a + b ∣ a + b + c + d) ∧ (a + c ∣ a + b + c + d) ∧
    (a + d ∣ a + b + c + d) ∧ (b + c ∣ a + b + c + d) := by
  have hS : ∑ x ∈ ({a, b, c, d} : Finset ℕ), x = a + b + c + d := sum_four hab hbc hcd
  rw [pairCount] at h
  have heq : ((({a, b, c, d} : Finset ℕ).powersetCard 2).filter
        fun p ↦ (∑ x ∈ p, x) ∣ ∑ x ∈ ({a, b, c, d} : Finset ℕ), x) =
      ((({a, b, c, d} : Finset ℕ).powersetCard 2) \ {({b, d} : Finset ℕ), {c, d}}) :=
    Finset.eq_of_subset_of_card_le (filter_subset_target hab hbc hcd)
      (le_trans (by rw [card_target hab hbc hcd]) h)
  have hmem : ∀ x y : ℕ, x < y → x ∈ ({a, b, c, d} : Finset ℕ) →
      y ∈ ({a, b, c, d} : Finset ℕ) → ({x, y} : Finset ℕ) ≠ {b, d} →
      ({x, y} : Finset ℕ) ≠ {c, d} → x + y ∣ a + b + c + d := by
    intro x y hxy hxA hyA hne1 hne2
    have hxy' : ({x, y} : Finset ℕ) ∈
        ((({a, b, c, d} : Finset ℕ).powersetCard 2) \ {({b, d} : Finset ℕ), {c, d}}) := by
      rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨pair_mem_powersetCard_two hxA hyA (by lia), by tauto⟩
    rw [← heq, Finset.mem_filter] at hxy'
    have h2 := hxy'.2
    rwa [Finset.sum_pair (by lia : x ≠ y), hS] at h2
  exact ⟨hmem a b hab (by simp) (by simp) (pair_ne_pair (Or.inl ⟨by lia, by lia⟩))
      (pair_ne_pair (Or.inl ⟨by lia, by lia⟩)),
    hmem a c (by lia) (by simp) (by simp) (pair_ne_pair (Or.inl ⟨by lia, by lia⟩))
      (pair_ne_pair (Or.inl ⟨by lia, by lia⟩)),
    hmem a d (by lia) (by simp) (by simp) (pair_ne_pair (Or.inl ⟨by lia, by lia⟩))
      (pair_ne_pair (Or.inl ⟨by lia, by lia⟩)),
    hmem b c hbc (by simp) (by simp) (pair_ne_pair (Or.inr ⟨by lia, by lia⟩))
      (pair_ne_pair (Or.inl ⟨by lia, by lia⟩))⟩

/-- If all four candidate pairs divide the sum, the count is exactly 4. -/
lemma pairCount_eq_four {a b c d : ℕ} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (h1 : a + b ∣ a + b + c + d) (h2 : a + c ∣ a + b + c + d)
    (h3 : a + d ∣ a + b + c + d) (h4 : b + c ∣ a + b + c + d) :
    pairCount {a, b, c, d} = 4 := by
  refine le_antisymm (pairCount_le_four hab hbc hcd) ?_
  have hS : ∑ x ∈ ({a, b, c, d} : Finset ℕ), x = a + b + c + d := sum_four hab hbc hcd
  rw [pairCount]
  have hgood : ({({a, b} : Finset ℕ), {a, c}, {a, d}, {b, c}} : Finset (Finset ℕ)) ⊆
      ((({a, b, c, d} : Finset ℕ).powersetCard 2).filter
        fun p ↦ (∑ x ∈ p, x) ∣ ∑ x ∈ ({a, b, c, d} : Finset ℕ), x) := by
    have hmem : ∀ x y : ℕ, x < y → x ∈ ({a, b, c, d} : Finset ℕ) →
        y ∈ ({a, b, c, d} : Finset ℕ) → x + y ∣ a + b + c + d →
        ({x, y} : Finset ℕ) ∈ ((({a, b, c, d} : Finset ℕ).powersetCard 2).filter
          fun p ↦ (∑ x ∈ p, x) ∣ ∑ x ∈ ({a, b, c, d} : Finset ℕ), x) := by
      intro x y hxy hxA hyA hdvd
      rw [Finset.mem_filter]
      exact ⟨pair_mem_powersetCard_two hxA hyA (by lia),
        by rwa [Finset.sum_pair (by lia : x ≠ y), hS]⟩
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hmem a b hab (by simp) (by simp) h1
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hmem a c (by lia) (by simp) (by simp) h2
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hmem a d (by lia) (by simp) (by simp) h3
    rw [Finset.mem_singleton] at hp
    exact hp ▸ hmem b c hbc (by simp) (by simp) h4
  have hcard : ({({a, b} : Finset ℕ), {a, c}, {a, d}, {b, c}} :
      Finset (Finset ℕ)).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
    · rw [Finset.mem_singleton]
      exact pair_ne_pair (Or.inl ⟨by lia, by lia⟩)
    · rw [Finset.mem_insert, Finset.mem_singleton]
      rintro (h' | h')
      · exact pair_ne_pair (Or.inr ⟨by lia, by lia⟩) h'
      · exact pair_ne_pair (Or.inl ⟨by lia, by lia⟩) h'
    · rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
      rintro (h' | h' | h')
      · exact pair_ne_pair (Or.inr ⟨by lia, by lia⟩) h'
      · exact pair_ne_pair (Or.inr ⟨by lia, by lia⟩) h'
      · exact pair_ne_pair (Or.inl ⟨by lia, by lia⟩) h'
  calc 4 = ({({a, b} : Finset ℕ), {a, c}, {a, d}, {b, c}} :
        Finset (Finset ℕ)).card := hcard.symm
    _ ≤ _ := Finset.card_le_card hgood

/-- The heart of the solution: if all four candidate pairs divide the sum,
then the quadruple is `(a, 5a, 7a, 11a)` or `(a, 11a, 19a, 29a)`. -/
lemma classify {a b c d : ℕ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (h1 : a + b ∣ a + b + c + d) (h2 : a + c ∣ a + b + c + d)
    (h3 : a + d ∣ a + b + c + d) (h4 : b + c ∣ a + b + c + d) :
    (b = 5 * a ∧ c = 7 * a ∧ d = 11 * a) ∨
    (b = 11 * a ∧ c = 19 * a ∧ d = 29 * a) := by
  -- a + d and b + c divide each other, so they are equal.
  have e3 : a + b + c + d = (a + d) + (b + c) := by ring
  rw [e3] at h3 h4
  have h3' : a + d ∣ b + c := (Nat.dvd_add_right (dvd_refl (a + d))).mp h3
  have h4' : b + c ∣ a + d := (Nat.dvd_add_left (dvd_refl (b + c))).mp h4
  have ht : a + d = b + c := Nat.dvd_antisymm h3' h4'
  -- the total sum is 2 * (b + c)
  have hsum : a + b + c + d = 2 * (b + c) := by lia
  rw [hsum] at h1 h2
  obtain ⟨k, hk⟩ := h1
  obtain ⟨l, hl⟩ := h2
  -- k ≥ 3 since a + b < b + c
  have hk3 : 3 ≤ k := by
    by_contra hk2
    have h5 : (a + b) * k ≤ (a + b) * 2 := Nat.mul_le_mul_left (a + b) (by lia)
    lia
  -- l ≥ 3 since a + c < b + c
  have hl3 : 3 ≤ l := by
    by_contra hl2
    have h5 : (a + c) * l ≤ (a + c) * 2 := Nat.mul_le_mul_left (a + c) (by lia)
    lia
  -- k > l since a + b < a + c
  have hlk : l < k := by
    by_contra hkl
    have h5 : (a + c) * k ≤ (a + c) * l := Nat.mul_le_mul_left (a + c) (by lia)
    have h6 : (a + b) * k < (a + c) * k :=
      mul_lt_mul_of_pos_right (by lia) (by lia)
    lia
  -- since (a + b) + (a + c) > b + c, we get k * l < 2 * k + 2 * l
  have hkey : k * l < 2 * k + 2 * l := by
    have hpq : b + c < (a + b) + (a + c) := by lia
    have h5 : k * l * (b + c) < k * l * ((a + b) + (a + c)) :=
      (Nat.mul_lt_mul_left (Nat.mul_pos (by lia) (by lia))).mpr hpq
    have e5 : k * l * ((a + b) + (a + c)) =
        l * ((a + b) * k) + k * ((a + c) * l) := by ring
    rw [e5, ← hk, ← hl] at h5
    have e6 : l * (2 * (b + c)) + k * (2 * (b + c)) =
        (2 * l + 2 * k) * (b + c) := by ring
    rw [e6] at h5
    have h6 := Nat.lt_of_mul_lt_mul_right h5
    lia
  -- hence l = 3
  have hl3' : l = 3 := by
    by_contra hl4
    have h5 : k * 4 ≤ k * l := Nat.mul_le_mul_left k (by lia)
    lia
  subst hl3'
  -- and k = 4 or k = 5
  have hk45 : k = 4 ∨ k = 5 := by lia
  rcases hk45 with rfl | rfl
  · exact Or.inl ⟨by lia, by lia, by lia⟩
  · exact Or.inr ⟨by lia, by lia, by lia⟩

/-- Any 4-element finset of naturals can be listed in increasing order. -/
lemma exists_sorted_four {A : Finset ℕ} (hA : A.card = 4) :
    ∃ a b c d : ℕ, a < b ∧ b < c ∧ c < d ∧ A = {a, b, c, d} := by
  obtain ⟨a, b, c, d, hL⟩ : ∃ a b c d : ℕ, A.sort (· ≤ ·) = [a, b, c, d] := by
    refine List.length_eq_four.mp ?_
    rw [Finset.length_sort, hA]
  have hsorted := (Finset.sortedLT_sort A).pairwise
  rw [hL] at hsorted
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil] at hsorted
  have h5 : (A.sort (· ≤ ·)).toFinset = A := by rw [Finset.sort_toFinset]
  rw [hL] at h5
  refine ⟨a, b, c, d, by tauto, by tauto, by tauto, ?_⟩
  rw [← h5]
  simp

snip end

problem imo2011_p1 (A : Finset ℕ) (hA : A.card = 4) (hApos : ∀ a ∈ A, 0 < a) :
    A ∈ SolutionSet ↔
      ∀ B : Finset ℕ, B.card = 4 → (∀ b ∈ B, 0 < b) →
        pairCount B ≤ pairCount A := by
  constructor
  · rintro ⟨e, he, hAeq⟩ B hB _hBpos
    obtain ⟨a, b, c, d, hab, hbc, hcd, rfl⟩ := exists_sorted_four hB
    have hA4 : pairCount A = 4 := by
      rcases hAeq with rfl | rfl
      · exact pairCount_eq_four (by lia) (by lia) (by lia)
          ⟨4, by ring⟩ ⟨3, by ring⟩ ⟨2, by ring⟩ ⟨2, by ring⟩
      · exact pairCount_eq_four (by lia) (by lia) (by lia)
          ⟨5, by ring⟩ ⟨3, by ring⟩ ⟨2, by ring⟩ ⟨2, by ring⟩
    rw [hA4]
    exact pairCount_le_four hab hbc hcd
  · intro h
    have hwitness := h {1, 5, 7, 11} (by decide) (by decide)
    rw [show pairCount {1, 5, 7, 11} = 4 from by decide] at hwitness
    obtain ⟨a, b, c, d, hab, hbc, hcd, rfl⟩ := exists_sorted_four hA
    have ha : 0 < a := hApos a (by simp)
    obtain ⟨h1, h2, h3, h4⟩ := dvds_of_four_le hab hbc hcd hwitness
    rcases classify ha hab hbc h1 h2 h3 h4 with ⟨hb, hc, hd⟩ | ⟨hb, hc, hd⟩
    · exact ⟨a, ha, Or.inl (by rw [hb, hc, hd])⟩
    · exact ⟨a, ha, Or.inr (by rw [hb, hc, hd])⟩

end Imo2011P1
