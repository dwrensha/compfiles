/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:　Benpigchu
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 1985, Problem 4

Given a set M of 1985 distinct positive integers, none of which has a prime
divisor greater than 23, prove that M contains a subset of 4 elements
whose product is the 4th power of an integer.
-/

namespace Imo1985P4

snip begin

universe u v w

lemma extended_pigeonhole {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]
  {s : Finset α} {f: α → β} {s' : Finset β} (hf : ∀ n ∈ s, f n ∈ s')
  (n : ℕ) (hn : 2 * n + s'.card - 1 ≤ s.card)
  : ∃ t : Finset (Finset α), t.card = n
    ∧ (∀ t' : Finset α, t' ∈ t → t' ⊆ s)
    ∧ (∀ t' : Finset α, t' ∈ t → t'.card = 2)
    ∧ ((t.toSet).PairwiseDisjoint id)
    ∧ (∀ t' : Finset α, t' ∈ t → ∃ p : β, ∀ n : α, n ∈ t' → f n = p)
    := by
  induction' n with n' hn'
  · use ∅
    tauto
  · have h'n' : 2 * n' + s'.card - 1 ≤ s.card := by omega
    rcases hn' h'n' with ⟨tn', ⟨htn'₁, htn'₂, htn'₃, htn'₄, htn'₅⟩⟩
    let s'' := s \ (Finset.disjiUnion tn' id htn'₄)
    have hs'' : s''.card = s.card - 2 * n' := by
      calc s''.card
          = s.card - (Finset.disjiUnion tn' id htn'₄).card := by
            apply Finset.card_sdiff_of_subset
            intro x hx
            simp at hx
            rcases hx with ⟨t', ⟨ht'₁, ht'₂⟩⟩
            exact (htn'₂ t' ht'₁) ht'₂
        _ = s.card - ∑ x ∈ tn', x.card := by
          rw [Finset.card_disjiUnion]
          simp
        _ = s.card - ∑ x ∈ tn', 2 := by rw [Finset.sum_congr rfl htn'₃]
        _ = s.card - 2 * n' := by
          rw [Finset.sum_const]
          simp
          rw [htn'₁]
          omega
    have hf' : Set.MapsTo f s'' s' := by
      intro x hxs''
      rw [Finset.mem_coe] at *
      exact hf x (Finset.mem_sdiff.mp hxs'').left
    have h's'' : s'.card < s''.card := by omega
    rcases Finset.exists_ne_map_eq_of_card_lt_of_maps_to h's'' hf' with ⟨p, hp, q, hq, hpq₁, hpq₂⟩
    use (insert {p, q} tn')
    have hpqs'' : {p, q} ⊆ s'' := Finset.insert_subset hp (Finset.singleton_subset_iff.mpr hq)
    constructorm* _ ∧ _
    · rw [← htn'₁]
      apply Finset.card_insert_of_notMem
      rw [Finset.subset_sdiff] at hpqs''
      have h' := hpqs''.right
      contrapose! h'
      simp
      intro htn'
      use {p, q}
      constructor
      · exact h'
      · simp
    · intro t' ht'
      rw [Finset.mem_insert] at ht'
      rcases ht' with (ht'pq|ht'tn')
      · rw [ht'pq]
        exact subset_trans hpqs'' Finset.sdiff_subset
      · exact htn'₂ t' ht'tn'
    · intro t' ht'
      rw [Finset.mem_insert] at ht'
      rcases ht' with (ht'pq|ht'tn')
      · rw [ht'pq]
        apply Finset.card_insert_of_notMem
        exact Finset.notMem_singleton.mpr hpq₁
      · exact htn'₃ t' ht'tn'
    · rw [Finset.coe_insert, Set.pairwiseDisjoint_insert]
      constructor
      · exact htn'₄
      · intro j hj hpqj
        simp only [id_eq, Finset.disjoint_iff_ne]
        intro a ha b hb
        have has'' := hpqs'' ha
        rw [Finset.mem_sdiff] at has''
        have hatn' := has''.right
        contrapose! hatn'
        rw [hatn']
        simp
        use j
        exact ⟨hj, hb⟩
    · intro t' ht'
      rw [Finset.mem_insert] at ht'
      rcases ht' with (ht'pq|ht'tn')
      · use (f p)
        intro m hm
        rw [ht'pq, Finset.mem_insert, Finset.mem_singleton] at hm
        rcases hm with (hmp|hmq)
        · rw [hmp]
        · rw [hmq,hpq₂]
      · exact htn'₅ t' ht'tn'

lemma double_pigeonhole {α : Type u} {β : Type v} {γ : Type w} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
  {s : Finset α} {f₁: α → β} {f₂: (Finset α) → γ} {s₁ : Finset β} {s₂ : Finset γ}
  (hf₁ : ∀ n ∈ s, f₁ n ∈ s₁) (hf₂ : ∀ s' ⊆ s, f₂ s' ∈ s₂)
  (hs: 2 * s₂.card + s₁.card + 1 ≤ s.card)
  : ∃ t₁ t₂ : (Finset α), t₁.card = 2 ∧ t₂.card = 2
    ∧ t₁ ⊆ s ∧ t₂ ⊆ s ∧ Disjoint t₁ t₂
    ∧ (∃ p : β, ∀ n : α, n ∈ t₁ → f₁ n = p)
    ∧ (∃ p : β, ∀ n : α, n ∈ t₂ → f₁ n = p)
    ∧ (f₂ t₁ = f₂ t₂)
    := by
  have h's : 2 * (s₂.card + 1) + s₁.card - 1 ≤ s.card := by omega
  rcases extended_pigeonhole hf₁ (s₂.card + 1) h's with ⟨t, ⟨ht₁, ht₂, ht₃, ht₄, ht₅⟩⟩
  have h't : s₂.card < t.card := by omega
  have h'f₂ : Set.MapsTo f₂ t s₂ := by
    intro x hxt
    rw [Finset.mem_coe] at *
    exact hf₂ x (ht₂ x hxt)
  rcases Finset.exists_ne_map_eq_of_card_lt_of_maps_to h't h'f₂ with ⟨p, hp, q, hq, hpq₁, hpq₂⟩
  use p, q
  constructorm* _ ∧ _
  · exact ht₃ p hp
  · exact ht₃ q hq
  · exact ht₂ p hp
  · exact ht₂ q hq
  · exact ht₄ hp hq hpq₁
  · exact ht₅ p hp
  · exact ht₅ q hq
  · exact hpq₂

noncomputable def pow_of_kth_prime_mod_two (k : ℕ) (n : ℕ) : ℕ :=
  (padicValNat (Nat.nth Nat.Prime k) n) % 2

def two_pow_k_finset (k : ℕ) := Finset.pi (Finset.range k) (fun _ ↦ Finset.range 2)

noncomputable def pow_of_first_k_prime_mod_two (k : ℕ) (n : ℕ) :=
  fun (k' : ℕ) ↦ fun (_ : k' ∈ Finset.range k) ↦ pow_of_kth_prime_mod_two k' n

lemma pow_of_first_k_prime_mod_two_mem_two_pow_k_finset (k : ℕ) (n : ℕ) :
  pow_of_first_k_prime_mod_two k n ∈ two_pow_k_finset k := by
  rw [two_pow_k_finset, Finset.mem_pi]
  intro a ha
  simp [pow_of_first_k_prime_mod_two, pow_of_kth_prime_mod_two]
  apply Nat.mod_lt
  norm_num

lemma square_of_pow_of_pow_of_kth_prime_mod_two_eq {m n : ℕ}
  (hm₀ : m ≠ 0) (hn₀ : n ≠ 0)
  (hmn : ∀ k , pow_of_kth_prime_mod_two k m = pow_of_kth_prime_mod_two k n):
  ∃ k, m * n = k ^ 2 := by
  let k := ∏ p ∈ Finset.range (m * n + 1) with Nat.Prime p, p ^ ((padicValNat p m + padicValNat p n) / 2)
  use k
  have hmn₀ : m * n ≠ 0 := Nat.mul_ne_zero hm₀ hn₀
  rw [← Nat.prod_pow_prime_padicValNat (m * n) hmn₀ (m * n + 1) (by omega:_)]
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro p hp
  simp at hp
  have hp' := hp.right
  rw [← pow_mul]
  congr
  haveI : Fact (Nat.Prime p) := { out := hp' }
  rw [padicValNat.mul hm₀ hn₀]
  symm
  apply Nat.div_mul_cancel
  apply Nat.dvd_of_mod_eq_zero
  have hmn':= hmn (Nat.primeCounting' p)
  simp [pow_of_kth_prime_mod_two, Nat.primeCounting'] at hmn'
  rw [Nat.nth_count hp'] at hmn'
  omega

lemma padicValNat_eq_zero_of_divisors {k m k': ℕ} (hm₀ : m ≠ 0)
  (hm : ∀ p, p.Prime ∧ p ∣ m → p ≤ Nat.nth Nat.Prime k) (hk' : k < k'):
  padicValNat (Nat.nth Nat.Prime k') m = 0 := by
  by_contra! hdiv
  haveI : Fact (Nat.Prime (Nat.nth Nat.Prime k')) := {
    out := Nat.prime_nth_prime k'
  }
  rw [← dvd_iff_padicValNat_ne_zero hm₀] at hdiv
  have hdiv' := hm (Nat.nth Nat.Prime k') ⟨Nat.prime_nth_prime k', hdiv⟩
  rw [Nat.nth_le_nth Nat.infinite_setOf_prime] at hdiv'
  omega

lemma square_of_pow_of_first_k_prime_mod_two_eq {k m n : ℕ}
  (hm₀ : m ≠ 0) (hn₀ : n ≠ 0)
  (hmn : pow_of_first_k_prime_mod_two (k + 1) m = pow_of_first_k_prime_mod_two (k + 1) n)
  (hm : ∀ p, p.Prime ∧ p ∣ m → p ≤ Nat.nth Nat.Prime k)
  (hn : ∀ p, p.Prime ∧ p ∣ n → p ≤ Nat.nth Nat.Prime k) :
  ∃ k, m * n = k ^ 2 := by
  have hmn' : ∀ k' , pow_of_kth_prime_mod_two k' m = pow_of_kth_prime_mod_two k' n := by
    intro k'
    by_cases hk' : k' ≤ k
    · rw [funext_iff] at hmn
      have hmn'' := hmn k'
      rw [funext_iff] at hmn''
      have h'k' : k' ∈ Finset.range (k + 1) := by exact Finset.mem_range_succ_iff.mpr hk'
      have hmn''' := hmn'' h'k'
      simp only [pow_of_first_k_prime_mod_two] at hmn'''
      exact hmn'''
    · push_neg at hk'
      simp only [pow_of_kth_prime_mod_two]
      rw [padicValNat_eq_zero_of_divisors hm₀ hm hk']
      rw [padicValNat_eq_zero_of_divisors hn₀ hn hk']
  exact square_of_pow_of_pow_of_kth_prime_mod_two_eq hm₀ hn₀ hmn'

lemma prod_square_of_pow_of_first_k_prime_mod_two_eq {M : Finset ℕ} {k : ℕ}
  (Mdivisors : ∀ m ∈ M, ∀ n, n.Prime ∧ n ∣ m → n ≤ Nat.nth Nat.Prime k)
  (Mpos : ∀ m ∈ M, 0 < m) {s : Finset ℕ} (hs₁ : s.card = 2) (hs₂ : s ⊆ M)
  (hs₃ : ∃ f, ∀ n ∈ s, pow_of_first_k_prime_mod_two (k+1) n = f) :
  ∃ k, s.prod id = k ^ 2 := by
  rw [Finset.card_eq_two] at hs₁
  rcases hs₁ with ⟨m, n, hmn₁, hmn₂⟩
  rw [hmn₂, Finset.prod_insert (Finset.notMem_singleton.mpr hmn₁), Finset.prod_singleton, id_eq, id_eq]
  have hm' : m ∈ M := by
    apply hs₂
    simp [hmn₂]
  have hn' : n ∈ M := by
    apply hs₂
    simp [hmn₂]
  have hm₀ : m ≠ 0 := Nat.ne_zero_iff_zero_lt.mpr (Mpos m hm')
  have hn₀ : n ≠ 0 := Nat.ne_zero_iff_zero_lt.mpr (Mpos n hn')
  have hmn : pow_of_first_k_prime_mod_two (k + 1) m = pow_of_first_k_prime_mod_two (k + 1) n := by
    rcases hs₃ with ⟨f, hf⟩
    rw [hf m (by simp [hmn₂]:_), hf n (by simp [hmn₂]:_)]
  have hm : ∀ p, p.Prime ∧ p ∣ m → p ≤ Nat.nth Nat.Prime k := Mdivisors m hm'
  have hn : ∀ p, p.Prime ∧ p ∣ n → p ≤ Nat.nth Nat.Prime k := Mdivisors n hn'
  exact square_of_pow_of_first_k_prime_mod_two_eq hm₀ hn₀ hmn hm hn

lemma sqrt_prod_subset_ne_zero {M s : Finset ℕ} {k : ℕ}
  (Mpos : ∀ m ∈ M, 0 < m) (hs: s ⊆ M) (hk : s.prod id = k ^ 2) :
  k ≠ 0 := by
  contrapose! hk
  rw [hk]
  simp
  rw [Finset.prod_eq_zero_iff]
  push_neg
  intro n hn
  exact Nat.ne_zero_iff_zero_lt.mpr (Mpos n (hs hn))

lemma sqrt_divisors_subset {M s : Finset ℕ} {k k₁: ℕ}
  (Mdivisors : ∀ m ∈ M, ∀ n, n.Prime ∧ n ∣ m → n ≤ Nat.nth Nat.Prime k)
  (hs: s ⊆ M) (hk₁ : s.prod id = k₁ ^ 2) : ∀ p, p.Prime ∧ p ∣ k₁ → p ≤ Nat.nth Nat.Prime k := by
  rintro p' ⟨hp', h'p'⟩
  rw [← Prime.dvd_pow_iff_dvd (Nat.Prime.prime hp') (by norm_num:2 ≠ 0)] at h'p'
  rw [← hk₁] at h'p'
  apply Prime.exists_mem_finset_dvd (Nat.Prime.prime hp') at h'p'
  rcases h'p' with ⟨n, hn, hn'⟩
  exact Mdivisors n (hs hn) p' ⟨hp', hn'⟩

theorem generalized (M : Finset ℕ) (k : ℕ)
  (Mcard : 3 * 2 ^ (k + 1) + 1 ≤ M.card) (Mpos : ∀ m ∈ M, 0 < m)
  (Mdivisors : ∀ m ∈ M, ∀ n, n.Prime ∧ n ∣ m → n ≤ Nat.nth Nat.Prime k)
  : ∃ M' : Finset ℕ, M' ⊆ M ∧ M'.card = 4 ∧ ∃ k, M'.prod id = k^4 := by
  let f₁ := fun (n : ℕ) ↦ pow_of_first_k_prime_mod_two (k+1) n
  have hf₁ : ∀ n ∈ M, f₁ n ∈ two_pow_k_finset (k + 1) := by
    intro m hm
    simp [f₁]
    apply pow_of_first_k_prime_mod_two_mem_two_pow_k_finset
  let f₂ := fun (n : Finset ℕ) ↦ pow_of_first_k_prime_mod_two (k+1) (Nat.sqrt (∏ x ∈ n, x))
  have hf₂ : ∀ n ⊆ M, f₂ n ∈ two_pow_k_finset (k + 1) := by
    intro m hm
    simp [f₂]
    apply pow_of_first_k_prime_mod_two_mem_two_pow_k_finset
  have hs : 2 * (two_pow_k_finset (k + 1)).card + (two_pow_k_finset (k + 1)).card + 1 ≤ M.card := by
    rw [two_pow_k_finset, Finset.card_pi, Finset.card_range, Finset.prod_const, Finset.card_range]
    omega
  rcases double_pigeonhole hf₁ hf₂ hs with ⟨p, q, hp₁, hq₁, hp₂, hq₂, hpq₁, hp₃, hq₃, hpq₂⟩
  use p ∪ q
  constructorm* _ ∧ _
  · exact Finset.union_subset hp₂ hq₂
  · rw [← Finset.card_union_eq_card_add_card] at hpq₁
    rw [hpq₁]
    omega
  · rw [Finset.prod_union hpq₁]
    rcases prod_square_of_pow_of_first_k_prime_mod_two_eq Mdivisors Mpos hp₁ hp₂ hp₃ with ⟨k₁, hk₁⟩
    rcases prod_square_of_pow_of_first_k_prime_mod_two_eq Mdivisors Mpos hq₁ hq₂ hq₃ with ⟨k₂, hk₂⟩
    rw [hk₁, hk₂]
    have h₀k₁ : k₁ ≠ 0 := sqrt_prod_subset_ne_zero Mpos hp₂ hk₁
    have h₀k₂ : k₂ ≠ 0 := sqrt_prod_subset_ne_zero Mpos hq₂ hk₂
    have hk₁k₂ : pow_of_first_k_prime_mod_two (k + 1) k₁ = pow_of_first_k_prime_mod_two (k + 1) k₂ := by
      simp [f₂] at hpq₂
      simp at hk₁ hk₂
      rw [hk₁, hk₂, Nat.sqrt_eq' k₁, Nat.sqrt_eq' k₂] at hpq₂
      exact hpq₂
    have h'k₁ : ∀ p, p.Prime ∧ p ∣ k₁ → p ≤ Nat.nth Nat.Prime k :=
      sqrt_divisors_subset Mdivisors hp₂ hk₁
    have h'k₂ : ∀ p, p.Prime ∧ p ∣ k₂ → p ≤ Nat.nth Nat.Prime k :=
      sqrt_divisors_subset Mdivisors hq₂ hk₂
    rcases square_of_pow_of_first_k_prime_mod_two_eq h₀k₁ h₀k₂ hk₁k₂ h'k₁ h'k₂ with ⟨k, hk⟩
    use k
    rw [← mul_pow, hk, ← pow_mul]

snip end

problem imo1985_p4 (M : Finset ℕ) (Mcard : M.card = 1985) (Mpos : ∀ m ∈ M, 0 < m)
    (Mdivisors : ∀ m ∈ M, ∀ n, n ∈ m.primeFactors → n ≤ 23)
    : ∃ M' : Finset ℕ, M' ⊆ M ∧ M'.card = 4 ∧ ∃ k, M'.prod id = k^4 := by
  replace Mdivisors : ∀ m ∈ M, ∀ n, n.Prime ∧ n ∣ m → n ≤ 23 := fun m hm n ↦ by
    rw [←Nat.mem_primeFactors_of_ne_zero (Mpos m hm).ne.symm]
    grind
  let k := 8
  have h₁ : Nat.nth Nat.Prime k = 23 := by
    have h' : Nat.count Nat.Prime 23 = k := by decide
    rw [← h']
    apply Nat.nth_count
    decide
  rw [← h₁] at Mdivisors
  have h₂ : 3 * 2 ^ (k + 1) + 1 ≤ M.card := by
    rw [Mcard]
    decide
  exact generalized M k h₂ Mpos Mdivisors


end Imo1985P4
