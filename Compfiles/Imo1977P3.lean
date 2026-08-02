/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.NumberTheory]
}

/-!
# International Mathematical Olympiad 1977, Problem 3

Given an integer n > 2, let Vₙ be the set of integers 1 + kn for k a positive integer.
A number m in Vₙ is called indecomposable if it cannot be expressed as the product of
two members of Vₙ. Prove that there is a number in Vₙ which can be expressed as the
product of indecomposable members of Vₙ in more than one way (decompositions which
differ solely in the order of factors are not regarded as different).
-/

namespace Imo1977P3

/-- The set `Vₙ` of natural numbers of the form `1 + k * n` with `k` a positive integer. -/
def Vn (n : ℕ) : Set ℕ := {m | ∃ k : ℕ, 1 ≤ k ∧ m = 1 + k * n}

/-- `m` is indecomposable in `Vₙ` if it belongs to `Vₙ` but cannot be written as a
product of two members of `Vₙ`. -/
def Indecomposable (n : ℕ) (m : ℕ) : Prop :=
  m ∈ Vn n ∧ ¬ ∃ p q : ℕ, p ∈ Vn n ∧ q ∈ Vn n ∧ m = p * q

snip begin

/-- Every member of `Vₙ` is at least `n + 1`. -/
lemma vn_ge {n m : ℕ} (hm : m ∈ Vn n) : n + 1 ≤ m := by
  obtain ⟨k, hk, rfl⟩ := hm
  have h := Nat.mul_le_mul hk (le_refl n)
  omega

/-- `Vₙ` is closed under multiplication. -/
lemma mul_mem_vn {n p q : ℕ} (hp : p ∈ Vn n) (hq : q ∈ Vn n) : p * q ∈ Vn n := by
  obtain ⟨a, ha, rfl⟩ := hp
  obtain ⟨b, hb, rfl⟩ := hq
  exact ⟨a + b + a * b * n, by omega, by ring⟩

/-- `(n - 1)^2` (written with `n = c + 3`) is indecomposable in `Vₙ`: it is smaller
than the square of the smallest member of `Vₙ`. -/
lemma indecomposable_sq (c : ℕ) : Indecomposable (c + 3) ((c + 2) ^ 2) := by
  refine ⟨⟨c + 1, by omega, by ring⟩, ?_⟩
  rintro ⟨p, q, hp, hq, h⟩
  have hp1 : c + 4 ≤ p := by have := vn_ge hp; omega
  have hq1 : c + 4 ≤ q := by have := vn_ge hq; omega
  have hle : (c + 4) * (c + 4) ≤ (c + 2) ^ 2 := by
    have := Nat.mul_le_mul hp1 hq1
    rwa [← h] at this
  have e : (c + 4) * (c + 4) = (c + 2) ^ 2 + (4 * c + 12) := by ring
  omega

/-- `(n - 1)^2` does not divide `(n - 1) * (2 * n - 1)` (written with `n = c + 3`),
since `n - 1` does not divide `2 * n - 1 = 2 * (n - 1) + 1`. -/
lemma not_dvd (c : ℕ) : ¬ (c + 2) ^ 2 ∣ (c + 2) * (2 * c + 5) := by
  intro h
  have h2 : c + 2 ∣ 2 * c + 5 := by
    have h' := h
    rw [sq] at h'
    exact Nat.dvd_of_mul_dvd_mul_left (by omega) h'
  have h3 : c + 2 ∣ 2 * c + 5 - 2 * (c + 2) := Nat.dvd_sub h2 (dvd_mul_left _ _)
  have h4 : 2 * c + 5 - 2 * (c + 2) = 1 := by omega
  rw [h4] at h3
  have := Nat.le_of_dvd one_pos h3
  omega

/-- Every member of `Vₙ` is a product of indecomposable members of `Vₙ`. -/
lemma exists_factorization (n : ℕ) (hn : 2 < n) :
    ∀ m : ℕ, m ∈ Vn n →
      ∃ F : Multiset ℕ, (∀ d ∈ F, Indecomposable n d) ∧ F.prod = m := by
  intro m
  induction' m using Nat.strong_induction_on with m ih
  intro hm
  by_cases h : Indecomposable n m
  · exact ⟨{m}, fun d hd => by
      rw [Multiset.mem_singleton] at hd
      rw [hd]
      exact h, Multiset.prod_singleton m⟩
  · obtain ⟨p, q, hp, hq, rfl⟩ : ∃ p q : ℕ, p ∈ Vn n ∧ q ∈ Vn n ∧ m = p * q := by
      by_contra hcon
      exact h ⟨hm, hcon⟩
    have hpg : n + 1 ≤ p := vn_ge hp
    have hqg : n + 1 ≤ q := vn_ge hq
    have hplt : p < p * q := by
      have h2 : p * 2 ≤ p * q := Nat.mul_le_mul (le_refl p) (by omega)
      omega
    have hqlt : q < p * q := by
      have h2 : 2 * q ≤ p * q := Nat.mul_le_mul (by omega) (le_refl q)
      omega
    obtain ⟨Fp, hFp, hFpprod⟩ := ih p hplt hp
    obtain ⟨Fq, hFq, hFqprod⟩ := ih q hqlt hq
    exact ⟨Fp + Fq, fun d hd => by
      rw [Multiset.mem_add] at hd
      rcases hd with hd | hd
      · exact hFp d hd
      · exact hFq d hd, by rw [Multiset.prod_add, hFpprod, hFqprod]⟩

snip end

problem imo1977_p3 (n : ℕ) (hn : 2 < n) :
    ∃ r ∈ Vn n, ∃ F₁ F₂ : Multiset ℕ,
      (∀ d ∈ F₁, Indecomposable n d) ∧ (∀ d ∈ F₂, Indecomposable n d) ∧
      F₁.prod = r ∧ F₂.prod = r ∧ F₁ ≠ F₂ := by
  obtain ⟨c, rfl⟩ : ∃ c : ℕ, n = c + 3 := ⟨n - 3, by omega⟩
  -- The witness is `r = (n - 1)^2 * (2 * n - 1)^2`, written with `c = n - 3`
  -- (so `c + 2 = n - 1` and `2 * c + 5 = 2 * n - 1`) to avoid truncated subtraction.
  have hs2mem : (c + 2) ^ 2 ∈ Vn (c + 3) := ⟨c + 1, by omega, by ring⟩
  have ht2mem : (2 * c + 5) ^ 2 ∈ Vn (c + 3) := ⟨4 * c + 8, by omega, by ring⟩
  have hstmem : (c + 2) * (2 * c + 5) ∈ Vn (c + 3) := ⟨2 * c + 3, by omega, by ring⟩
  -- First factorization: `(n-1)^2` times any factorization of `(2n-1)^2`.
  obtain ⟨G, hG, hGprod⟩ := exists_factorization (c + 3) (by omega) _ ht2mem
  -- Second factorization: any factorization of `(n-1)*(2n-1)`, taken twice.
  obtain ⟨H, hH, hHprod⟩ := exists_factorization (c + 3) (by omega) _ hstmem
  refine ⟨(c + 2) ^ 2 * (2 * c + 5) ^ 2, mul_mem_vn hs2mem ht2mem, (c + 2) ^ 2 ::ₘ G,
    H + H, ?_, ?_, ?_, ?_, ?_⟩
  · intro d hd
    rw [Multiset.mem_cons] at hd
    rcases hd with rfl | hd
    · exact indecomposable_sq c
    · exact hG d hd
  · intro d hd
    rw [Multiset.mem_add] at hd
    rcases hd with hd | hd <;> exact hH d hd
  · rw [Multiset.prod_cons, hGprod]
  · rw [Multiset.prod_add, hHprod]; ring
  · -- The factorizations differ: `(n-1)^2` occurs in the first one, but every factor
    -- of the second one divides `(n-1)*(2n-1)`, which `(n-1)^2` does not divide.
    intro h
    have hmem : (c + 2) ^ 2 ∈ (c + 2) ^ 2 ::ₘ G := Multiset.mem_cons_self _ _
    rw [h, Multiset.mem_add] at hmem
    rcases hmem with hmem | hmem <;> {
      have hdvd := Multiset.dvd_prod hmem
      rw [hHprod] at hdvd
      exact not_dvd c hdvd
    }

end Imo1977P3
