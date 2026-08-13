/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Data.Fintype.Perm
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Inequality] }

/-!
# USA Mathematical Olympiad 2020 Problem 6

Let n ≥ 2 be an integer. Let x₁ ≥ x₂ ≥ ⋯ ≥ xₙ and y₁ ≥ y₂ ≥ ⋯ ≥ yₙ be 2n real
numbers such that

0 = x₁ + x₂ + ⋯ + xₙ = y₁ + y₂ + ⋯ + yₙ,

and

1 = x₁² + x₂² + ⋯ + xₙ² = y₁² + y₂² + ⋯ + yₙ².

Prove that

∑_{i=1}^{n} (xᵢyᵢ − xᵢyₙ₊₁₋ᵢ) ≥ 2/√(n−1).
-/

namespace Usa2020P6

open Finset Nat

snip begin

/-
We follow the expected-value approach from Evan Chen's solution notes.

For a permutation `σ` on `{1, ..., n}` put `S σ = ∑ i, x i * y (σ i)`.  For a
uniform random permutation one computes `E[S] = 0` and `E[S²] = 1/(n-1)`.
Since any random variable `A` with mean `μ` taking values in `[m, M]` has
variance at most `(M - m)²/4`, we get `max S - min S ≥ 2/√(n-1)`.  Finally,
by the rearrangement inequality, `max S = ∑ i, x i * y i` and
`min S = ∑ i, x i * y (Fin.rev i)`.
-/

/-- The fibers of the evaluation map `σ ↦ σ i` on `Perm (Fin n)` all have the same
cardinality: left multiplication by `Equiv.swap a b` is a bijection between the fiber
over `a` and the fiber over `b`. -/
lemma card_fiber_eq {n : ℕ} (i a b : Fin n) :
    #(univ.filter fun σ : Equiv.Perm (Fin n) => σ i = a) =
    #(univ.filter fun σ : Equiv.Perm (Fin n) => σ i = b) := by
  refine Finset.card_bij (fun σ _ => Equiv.swap a b * σ) ?_ ?_ ?_
  · intro σ hσ
    show (Equiv.swap a b * σ) ∈ univ.filter (fun σ : Equiv.Perm (Fin n) => σ i = b)
    rw [Finset.mem_filter] at hσ ⊢
    exact ⟨Finset.mem_univ _, by rw [Equiv.Perm.mul_apply, hσ.2, Equiv.swap_apply_left]⟩
  · intro σ₁ _ σ₂ _ h
    exact mul_left_cancel h
  · intro τ hτ
    rw [Finset.mem_filter] at hτ
    refine ⟨Equiv.swap a b * τ, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by rw [Equiv.Perm.mul_apply, hτ.2, Equiv.swap_apply_right]⟩
    · show Equiv.swap a b * (Equiv.swap a b * τ) = τ
      rw [← mul_assoc, Equiv.swap_mul_self, one_mul]

/-- Each fiber of the evaluation map `σ ↦ σ i` has cardinality `(n-1)!`. -/
lemma card_fiber {n : ℕ} (hn : 1 ≤ n) (i a : Fin n) :
    #(univ.filter fun σ : Equiv.Perm (Fin n) => σ i = a) = (n - 1)! := by
  have key : ∀ b : Fin n, #(univ.filter fun σ : Equiv.Perm (Fin n) => σ i = b) =
      #(univ.filter fun σ : Equiv.Perm (Fin n) => σ i = a) :=
    fun b => card_fiber_eq i b a
  have htotal : #(univ : Finset (Equiv.Perm (Fin n))) = n ! := by
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  have hsum : ∑ b : Fin n, #(univ.filter fun σ : Equiv.Perm (Fin n) => σ i = b) = n ! := by
    rw [← htotal]
    exact (Finset.card_eq_sum_card_fiberwise (s := univ) (t := univ)
      (f := fun σ : Equiv.Perm (Fin n) => σ i) (fun σ _ => Finset.mem_univ _)).symm
  rw [Finset.sum_congr rfl (fun b _ => key b), Finset.sum_const, smul_eq_mul,
    Finset.card_univ, Fintype.card_fin] at hsum
  have hfact : n ! = n * (n - 1)! := by
    have h1 : n = n - 1 + 1 := by omega
    conv_lhs => rw [h1]
    rw [Nat.factorial_succ, Nat.sub_add_cancel hn]
  rw [hfact] at hsum
  exact Nat.mul_left_cancel (by omega) hsum

/-- Summing `f (σ i)` over all permutations gives `(n-1)!` times the sum of `f`. -/
lemma sum_perm_apply {n : ℕ} (hn : 1 ≤ n) (i : Fin n) (f : Fin n → ℝ) :
    ∑ σ : Equiv.Perm (Fin n), f (σ i) = ((n - 1)! : ℝ) * ∑ a, f a := by
  calc ∑ σ : Equiv.Perm (Fin n), f (σ i)
      = ∑ a : Fin n, ∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin n) => σ i = a), f a := by
        exact (Finset.sum_fiberwise_of_maps_to' (s := univ) (t := univ)
          (g := fun σ : Equiv.Perm (Fin n) => σ i) (f := f)
          (fun σ _ => Finset.mem_univ _)).symm
    _ = ∑ a : Fin n, ((n - 1)! : ℝ) * f a := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_const, nsmul_eq_mul, card_fiber hn i a]
    _ = ((n - 1)! : ℝ) * ∑ a, f a := (Finset.mul_sum _ _ _).symm

/-- The fibers of `σ ↦ (σ i, σ j)` over pairs `(a₁, b)` and `(a₂, b)` have the same
cardinality, via left multiplication by `Equiv.swap a₁ a₂`. -/
lemma card_fiber₂_eq {n : ℕ} (i j : Fin n) (b a₁ a₂ : Fin n) (h₁ : a₁ ≠ b) (h₂ : a₂ ≠ b) :
    #(univ.filter fun σ : Equiv.Perm (Fin n) => σ i = a₁ ∧ σ j = b) =
    #(univ.filter fun σ : Equiv.Perm (Fin n) => σ i = a₂ ∧ σ j = b) := by
  refine Finset.card_bij (fun σ _ => Equiv.swap a₁ a₂ * σ) ?_ ?_ ?_
  · intro σ hσ
    show (Equiv.swap a₁ a₂ * σ) ∈ univ.filter (fun σ : Equiv.Perm (Fin n) => σ i = a₂ ∧ σ j = b)
    rw [Finset.mem_filter] at hσ ⊢
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · rw [Equiv.Perm.mul_apply, hσ.2.1, Equiv.swap_apply_left]
    · rw [Equiv.Perm.mul_apply, hσ.2.2,
        Equiv.swap_apply_of_ne_of_ne (Ne.symm h₁) (Ne.symm h₂)]
  · intro σ₁ _ σ₂ _ h
    exact mul_left_cancel h
  · intro τ hτ
    rw [Finset.mem_filter] at hτ
    refine ⟨Equiv.swap a₁ a₂ * τ, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · rw [Equiv.Perm.mul_apply, hτ.2.1, Equiv.swap_apply_right]
      · rw [Equiv.Perm.mul_apply, hτ.2.2,
          Equiv.swap_apply_of_ne_of_ne (Ne.symm h₁) (Ne.symm h₂)]
    · show Equiv.swap a₁ a₂ * (Equiv.swap a₁ a₂ * τ) = τ
      rw [← mul_assoc, Equiv.swap_mul_self, one_mul]

/-- Each fiber of `σ ↦ (σ i, σ j)` over a pair `(a, b)` with `a ≠ b` has
cardinality `(n-2)!`. -/
lemma card_fiber₂ {n : ℕ} (hn : 2 ≤ n) (i j : Fin n) (hij : i ≠ j) (a b : Fin n)
    (hab : a ≠ b) :
    #(univ.filter fun σ : Equiv.Perm (Fin n) => σ i = a ∧ σ j = b) = (n - 2)! := by
  have hsplit : ∀ a' : Fin n, (univ.filter fun σ : Equiv.Perm (Fin n) => σ i = a' ∧ σ j = b) =
      (univ.filter fun σ : Equiv.Perm (Fin n) => σ j = b).filter fun σ => σ i = a' := by
    intro a'
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro σ _
    exact and_comm
  have htotal : #(univ.filter fun σ : Equiv.Perm (Fin n) => σ j = b) =
      ∑ a' : Fin n, #(univ.filter fun σ : Equiv.Perm (Fin n) => σ i = a' ∧ σ j = b) := by
    rw [Finset.card_eq_sum_card_fiberwise (s := univ.filter fun σ : Equiv.Perm (Fin n) => σ j = b)
      (t := univ) (f := fun σ : Equiv.Perm (Fin n) => σ i) (fun σ _ => Finset.mem_univ _)]
    apply Finset.sum_congr rfl
    intro a' _
    rw [hsplit a']
  have hemp : #(univ.filter fun σ : Equiv.Perm (Fin n) => σ i = b ∧ σ j = b) = 0 := by
    rw [Finset.card_eq_zero]
    apply Finset.filter_false_of_mem
    intro σ _ h
    exact hij ((Equiv.injective σ) (h.1.trans h.2.symm))
  have huniform : ∀ a' : Fin n, a' ≠ b →
      #(univ.filter fun σ : Equiv.Perm (Fin n) => σ i = a' ∧ σ j = b) =
      #(univ.filter fun σ : Equiv.Perm (Fin n) => σ i = a ∧ σ j = b) :=
    fun a' ha' => card_fiber₂_eq i j b a' a ha' hab
  have hFib : #(univ.filter fun σ : Equiv.Perm (Fin n) => σ j = b) = (n - 1)! :=
    card_fiber (by omega) j b
  rw [hFib] at htotal
  have hsum : ∑ a' : Fin n, #(univ.filter fun σ : Equiv.Perm (Fin n) => σ i = a' ∧ σ j = b) =
      (n - 1) * #(univ.filter fun σ : Equiv.Perm (Fin n) => σ i = a ∧ σ j = b) := by
    rw [← Finset.add_sum_erase univ _ (Finset.mem_univ b), hemp, zero_add,
      Finset.sum_congr rfl (fun a' ha' => huniform a' (Finset.mem_erase.1 ha').1),
      Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ b),
      Finset.card_univ, Fintype.card_fin]
  rw [hsum] at htotal
  have hfact : (n - 1)! = (n - 1) * (n - 2)! := by
    have h1 : n - 1 = n - 2 + 1 := by omega
    rw [h1, Nat.factorial_succ]
  rw [hfact] at htotal
  exact (Nat.mul_left_cancel (by omega) htotal).symm

/-- Summing `g (σ i) (σ j)` over all permutations, for `i ≠ j`. -/
lemma sum_perm_apply₂ {n : ℕ} (hn : 2 ≤ n) (i j : Fin n) (hij : i ≠ j) (g : Fin n → Fin n → ℝ) :
    ∑ σ : Equiv.Perm (Fin n), g (σ i) (σ j) =
      ((n - 2)! : ℝ) * ∑ a : Fin n, ∑ b ∈ univ.erase a, g a b := by
  have hpair : ∀ a b : Fin n, (univ.filter fun σ : Equiv.Perm (Fin n) => (σ i, σ j) = (a, b)) =
      univ.filter fun σ : Equiv.Perm (Fin n) => σ i = a ∧ σ j = b := by
    intro a b
    apply Finset.filter_congr
    intro σ _
    exact Prod.ext_iff
  have hdiag : ∀ a : Fin n, #(univ.filter fun σ : Equiv.Perm (Fin n) => (σ i, σ j) = (a, a)) = 0 := by
    intro a
    rw [hpair a a, Finset.card_eq_zero]
    apply Finset.filter_false_of_mem
    intro σ _ h
    exact hij ((Equiv.injective σ) (h.1.trans h.2.symm))
  calc ∑ σ : Equiv.Perm (Fin n), g (σ i) (σ j)
      = ∑ p : Fin n × Fin n, ∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin n) => (σ i, σ j) = p),
          g p.1 p.2 := by
        exact (Finset.sum_fiberwise_of_maps_to' (s := univ) (t := univ)
          (g := fun σ : Equiv.Perm (Fin n) => (σ i, σ j)) (f := fun p : Fin n × Fin n => g p.1 p.2)
          (fun σ _ => Finset.mem_univ _)).symm
    _ = ∑ p : Fin n × Fin n,
          ((univ.filter (fun σ : Equiv.Perm (Fin n) => (σ i, σ j) = p)).card : ℝ) * g p.1 p.2 := by
        apply Finset.sum_congr rfl
        intro p _
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((n - 2)! : ℝ) * ∑ a : Fin n, ∑ b ∈ univ.erase a, g a b := by
        rw [← Finset.univ_product_univ, Finset.sum_product, Finset.mul_sum]
        dsimp only
        apply Finset.sum_congr rfl
        intro a _
        rw [← Finset.add_sum_erase univ _ (Finset.mem_univ a), hdiag a, Nat.cast_zero, zero_mul,
          zero_add]
        have h2 : (∑ b ∈ univ.erase a,
            ((univ.filter (fun σ : Equiv.Perm (Fin n) => (σ i, σ j) = (a, b))).card : ℝ) * g a b) =
            ∑ b ∈ univ.erase a, ((n - 2)! : ℝ) * g a b := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [hpair a b, card_fiber₂ hn i j hij a b (Ne.symm (Finset.mem_erase.1 hb).1)]
        rw [h2, ← Finset.mul_sum]

/-- `∑ σ, S σ = 0` where `S σ = ∑ i, x i * y (σ i)`. -/
lemma sum_S_eq_zero {n : ℕ} (hn : 1 ≤ n) (x y : Fin n → ℝ) (hys : ∑ i, y i = 0) :
    ∑ σ : Equiv.Perm (Fin n), ∑ i, x i * y (σ i) = 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i _
  show (∑ σ : Equiv.Perm (Fin n), x i * y (σ i)) = 0
  rw [← Finset.mul_sum, sum_perm_apply hn i y, hys, mul_zero, mul_zero]

/-- The second moment `∑ σ, (S σ)² = (n-1)! + (n-2)!`. -/
lemma sum_S_sq {n : ℕ} (hn : 2 ≤ n) (x y : Fin n → ℝ)
    (hxs : ∑ i, x i = 0) (hys : ∑ i, y i = 0)
    (hx2 : ∑ i, x i ^ 2 = 1) (hy2 : ∑ i, y i ^ 2 = 1) :
    ∑ σ : Equiv.Perm (Fin n), (∑ i, x i * y (σ i)) ^ 2 = ((n - 1)! : ℝ) + ((n - 2)! : ℝ) := by
  have hyy : ∑ a : Fin n, ∑ b ∈ univ.erase a, y a * y b = -1 := by
    have h1 : ∀ a : Fin n, ∑ b ∈ univ.erase a, y a * y b = -(y a ^ 2) := by
      intro a
      have h2 : (∑ b ∈ univ.erase a, y b) = ∑ b, y b - y a := by
        have h3 := Finset.sum_erase_add univ y (Finset.mem_univ a)
        linarith
      rw [← Finset.mul_sum, h2, hys]
      ring
    rw [Finset.sum_congr rfl (fun a _ => h1 a), Finset.sum_neg_distrib, hy2]
  have hxx : ∀ i : Fin n, ∑ j ∈ univ.erase i, x i * x j = -(x i ^ 2) := by
    intro i
    have h2 : (∑ j ∈ univ.erase i, x j) = ∑ j, x j - x i := by
      have h3 := Finset.sum_erase_add univ x (Finset.mem_univ i)
      linarith
    rw [← Finset.mul_sum, h2, hxs]
    ring
  have hexp : ∀ σ : Equiv.Perm (Fin n), (∑ i, x i * y (σ i)) ^ 2 =
      ∑ i : Fin n, ∑ j : Fin n, (x i * y (σ i)) * (x j * y (σ j)) := by
    intro σ
    rw [pow_two, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl (fun σ _ => hexp σ)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm)]
  have hin : ∀ i j : Fin n, ∑ σ : Equiv.Perm (Fin n), (x i * y (σ i)) * (x j * y (σ j)) =
      (x i * x j) * ∑ σ : Equiv.Perm (Fin n), y (σ i) * y (σ j) := by
    intro i j
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    ring
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hin i j))]
  have hCii : ∀ i : Fin n, ∑ σ : Equiv.Perm (Fin n), y (σ i) * y (σ i) = ((n - 1)! : ℝ) := by
    intro i
    have h := sum_perm_apply (by omega : 1 ≤ n) i (fun a => y a ^ 2)
    change (∑ σ : Equiv.Perm (Fin n), y (σ i) ^ 2) = ((n - 1)! : ℝ) * ∑ a, y a ^ 2 at h
    rw [hy2, mul_one] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro σ _
    rw [pow_two]
  have hCij : ∀ i j : Fin n, i ≠ j → ∑ σ : Equiv.Perm (Fin n), y (σ i) * y (σ j) =
      -((n - 2)! : ℝ) := by
    intro i j hij
    have h := sum_perm_apply₂ hn i j hij (fun a b => y a * y b)
    change (∑ σ : Equiv.Perm (Fin n), y (σ i) * y (σ j)) =
      ((n - 2)! : ℝ) * ∑ a : Fin n, ∑ b ∈ univ.erase a, y a * y b at h
    rw [hyy] at h
    rw [h]
    ring
  have hper : ∀ i : Fin n, (x i * x i) * (∑ σ : Equiv.Perm (Fin n), y (σ i) * y (σ i)) +
      ∑ j ∈ univ.erase i, (x i * x j) * (∑ σ : Equiv.Perm (Fin n), y (σ i) * y (σ j)) =
      (((n - 1)! : ℝ) + ((n - 2)! : ℝ)) * x i ^ 2 := by
    intro i
    rw [hCii i]
    have hoff : (∑ j ∈ univ.erase i, (x i * x j) * (∑ σ : Equiv.Perm (Fin n), y (σ i) * y (σ j))) =
        ∑ j ∈ univ.erase i, (x i * x j) * (-((n - 2)! : ℝ)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hCij i j (Ne.symm (Finset.mem_erase.1 hj).1)]
    rw [hoff, ← Finset.sum_mul, hxx i]
    ring
  rw [Finset.sum_congr rfl (fun i _ => (Finset.add_sum_erase univ _ (Finset.mem_univ i)).symm)]
  rw [Finset.sum_congr rfl (fun i _ => hper i)]
  rw [← Finset.mul_sum, hx2, mul_one]

/-- The variance bound: if `S σ` lies in `[m, M]` for all `σ`, then
`2/√(n-1) ≤ M - m`. -/
lemma variance_bound {n : ℕ} (hn : 2 ≤ n) (x y : Fin n → ℝ)
    (hxs : ∑ i, x i = 0) (hys : ∑ i, y i = 0)
    (hx2 : ∑ i, x i ^ 2 = 1) (hy2 : ∑ i, y i ^ 2 = 1)
    (m M : ℝ) (hm : ∀ σ : Equiv.Perm (Fin n), m ≤ ∑ i, x i * y (σ i))
    (hM : ∀ σ : Equiv.Perm (Fin n), ∑ i, x i * y (σ i) ≤ M) :
    2 / Real.sqrt ((n : ℝ) - 1) ≤ M - m := by
  have hS0 : ∑ σ : Equiv.Perm (Fin n), ∑ i, x i * y (σ i) = 0 :=
    sum_S_eq_zero (by omega) x y hys
  have hS2 : ∑ σ : Equiv.Perm (Fin n), (∑ i, x i * y (σ i)) ^ 2 = ((n - 1)! : ℝ) + ((n - 2)! : ℝ) :=
    sum_S_sq hn x y hxs hys hx2 hy2
  have hpt : ∀ σ : Equiv.Perm (Fin n), (∑ i, x i * y (σ i)) ^ 2 ≤
      (m + M) * (∑ i, x i * y (σ i)) - m * M := by
    intro σ
    have h1 : 0 ≤ (∑ i, x i * y (σ i) - m) * (M - ∑ i, x i * y (σ i)) :=
      mul_nonneg (sub_nonneg.2 (hm σ)) (sub_nonneg.2 (hM σ))
    have h2 : (∑ i, x i * y (σ i) - m) * (M - ∑ i, x i * y (σ i)) =
        -(∑ i, x i * y (σ i)) ^ 2 + (m + M) * (∑ i, x i * y (σ i)) - m * M := by ring
    linarith
  have hsum : ∑ σ : Equiv.Perm (Fin n), (∑ i, x i * y (σ i)) ^ 2 ≤
      ∑ σ : Equiv.Perm (Fin n), ((m + M) * (∑ i, x i * y (σ i)) - m * M) :=
    Finset.sum_le_sum (fun σ _ => hpt σ)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hS0, mul_zero, zero_sub, Finset.sum_const,
    nsmul_eq_mul, Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at hsum
  rw [hS2] at hsum
  have h4 : 4 * (((n - 1)! : ℝ) + ((n - 2)! : ℝ)) ≤ ((n)! : ℝ) * (M - m) ^ 2 := by
    have h1 : 4 * (((n - 1)! : ℝ) + ((n - 2)! : ℝ)) ≤ -(4 * ((n)! : ℝ) * (m * M)) := by
      linarith [hsum]
    have h2 : -(4 * ((n)! : ℝ) * (m * M)) ≤ ((n)! : ℝ) * (M - m) ^ 2 := by
      have h3 : (0:ℝ) ≤ ((n)! : ℝ) * (M + m) ^ 2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
      have h4' : ((n)! : ℝ) * (M - m) ^ 2 + 4 * ((n)! : ℝ) * (m * M) = ((n)! : ℝ) * (M + m) ^ 2 := by
        ring
      linarith
    exact h1.trans h2
  have hfact1 : ((n - 1)! : ℝ) + ((n - 2)! : ℝ) = (n : ℝ) * ((n - 2)! : ℝ) := by
    have h1 : (n - 1)! + (n - 2)! = n * (n - 2)! := by
      have e1 : (n - 1)! = (n - 1) * (n - 2)! := by
        have h1' : n - 1 = n - 2 + 1 := by omega
        rw [h1', Nat.factorial_succ]
      rw [e1]
      have e2 : (n - 1) * (n - 2)! + (n - 2)! = (n - 1 + 1) * (n - 2)! := by ring
      rw [e2, Nat.sub_add_cancel (by omega : 1 ≤ n)]
    exact_mod_cast h1
  have hfact2 : ((n)! : ℝ) = (n : ℝ) * ((n : ℝ) - 1) * ((n - 2)! : ℝ) := by
    have h2 : n ! = n * (n - 1) * (n - 2)! := by
      have e1 : n ! = n * (n - 1)! := by
        have h1' : n = n - 1 + 1 := by omega
        conv_lhs => rw [h1']
        rw [Nat.factorial_succ, Nat.sub_add_cancel (by omega : 1 ≤ n)]
      have e2 : (n - 1)! = (n - 1) * (n - 2)! := by
        have h1' : n - 1 = n - 2 + 1 := by omega
        rw [h1', Nat.factorial_succ]
      rw [e1, e2, mul_assoc]
    have h3 : (↑(n - 1) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    rw [h2, Nat.cast_mul, Nat.cast_mul, h3]
  rw [hfact1, hfact2] at h4
  have hc : (0:ℝ) < (n : ℝ) * ((n - 2)! : ℝ) :=
    mul_pos (Nat.cast_pos.2 (by omega)) (Nat.cast_pos.2 (Nat.factorial_pos _))
  have h5 : 4 ≤ ((n : ℝ) - 1) * (M - m) ^ 2 := by
    have h4'' : (4 : ℝ) * ((n : ℝ) * ((n - 2)! : ℝ)) ≤
        (((n : ℝ) - 1) * (M - m) ^ 2) * ((n : ℝ) * ((n - 2)! : ℝ)) := by
      calc (4:ℝ) * ((n : ℝ) * ((n - 2)! : ℝ))
          ≤ ((n : ℝ) * ((n : ℝ) - 1) * ((n - 2)! : ℝ)) * (M - m) ^ 2 := h4
        _ = (((n : ℝ) - 1) * (M - m) ^ 2) * ((n : ℝ) * ((n - 2)! : ℝ)) := by ring
    exact le_of_mul_le_mul_right h4'' hc
  have hn1 : (0:ℝ) < (n : ℝ) - 1 := by
    have h : (1:ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    linarith
  have h6 : (2 / Real.sqrt ((n : ℝ) - 1)) ^ 2 ≤ (M - m) ^ 2 := by
    rw [div_pow, Real.sq_sqrt (le_of_lt hn1), div_le_iff₀ hn1,
      mul_comm ((M - m) ^ 2) ((n : ℝ) - 1)]
    have h2sq : (2:ℝ) ^ 2 = 4 := by norm_num
    rw [h2sq]
    exact h5
  have h7 : (0:ℝ) ≤ M - m := by
    have h1 := hm (1 : Equiv.Perm (Fin n))
    have h2 := hM (1 : Equiv.Perm (Fin n))
    linarith
  exact le_of_sq_le_sq h6 h7

/-- A strictly monotone function `Fin m → ℕ` dominates the identity. -/
lemma fin_strictMono_ge {m : ℕ} {g : Fin m → ℕ} (hg : StrictMono g) (j : Fin m) :
    j.val ≤ g j := by
  have h : ∀ v : ℕ, ∀ hv : v < m, v ≤ g ⟨v, hv⟩ := by
    intro v
    induction v with
    | zero => intro hv; exact Nat.zero_le _
    | succ v ih =>
      intro hv
      have hvm : v < m := Nat.lt_of_succ_lt hv
      have h1 : v ≤ g ⟨v, hvm⟩ := ih hvm
      have h2 : g ⟨v, hvm⟩ < g ⟨v + 1, hv⟩ := hg (by rw [Fin.mk_lt_mk]; exact Nat.lt_succ_self v)
      omega
  have h3 := h j.val j.isLt
  rwa [Fin.eta j j.isLt] at h3

/-- The sum of an antitone function over any finset is at most the sum over an initial
segment of the same cardinality. -/
lemma topsum {n : ℕ} (y : Fin n → ℝ) (hy : Antitone y) (s : Finset (Fin n)) {m : ℕ}
    (hm : s.card = m) (hmn : m ≤ n) :
    ∑ i ∈ s, y i ≤ ∑ j : Fin m, y ⟨j.val, lt_of_lt_of_le j.isLt hmn⟩ := by
  have h1 : ∑ i ∈ s, y i = ∑ j : Fin m, y (s.orderIsoOfFin hm j : Fin n) := by
    rw [← Finset.sum_coe_sort s y]
    exact (Equiv.sum_comp (s.orderIsoOfFin hm).toEquiv (fun i : ↥s => y (i : Fin n))).symm
  rw [h1]
  apply Finset.sum_le_sum
  intro j _
  apply hy
  rw [Fin.le_def, Finset.coe_orderIsoOfFin_apply]
  exact fin_strictMono_ge (Fin.val_strictMono.comp (s.orderEmbOfFin hm).strictMono) j

/-- The sum of a monotone function over any finset is at most the sum over a terminal
segment of the same cardinality. -/
lemma topsum' {n : ℕ} (g : Fin n → ℝ) (hg : Monotone g) (s : Finset (Fin n)) {m : ℕ}
    (hm : s.card = m) (hmn : m ≤ n) :
    ∑ i ∈ s, g i ≤ ∑ j : Fin m, g (Fin.rev ⟨j.val, lt_of_lt_of_le j.isLt hmn⟩) := by
  have hanti : Antitone (g ∘ Fin.rev) :=
    hg.comp_antitone (fun a b hab => Fin.rev_le_rev.2 hab)
  have him : (s.image Fin.rev).card = m := by
    rw [Finset.card_image_of_injective s Fin.rev_injective]
    exact hm
  have h1 := topsum (g ∘ Fin.rev) hanti (s.image Fin.rev) him hmn
  rw [Finset.sum_image Fin.rev_injective.injOn] at h1
  simp only [Function.comp_apply, Fin.rev_rev] at h1
  exact h1

/-- The sum of an antitone function over any finset is at least the sum over a terminal
segment of the same cardinality. -/
lemma bottomsum {n : ℕ} (y : Fin n → ℝ) (hy : Antitone y) (s : Finset (Fin n)) {m : ℕ}
    (hm : s.card = m) (hmn : m ≤ n) :
    ∑ j : Fin m, y (Fin.rev ⟨j.val, lt_of_lt_of_le j.isLt hmn⟩) ≤ ∑ i ∈ s, y i := by
  have h1 := topsum' (fun i => -y i) (fun a b hab => neg_le_neg (hy hab)) s hm hmn
  rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib] at h1
  have h2 := neg_le_neg h1
  rw [neg_neg, neg_neg] at h2
  exact h2

/-- Summation by parts: if `z` has zero sum and nonnegative partial sums, and `x` is
decreasing on `range n`, then `∑ x i * z i ≥ 0`. -/
lemma abel_nonneg {n : ℕ} (x z : ℕ → ℝ)
    (hz : ∑ i ∈ Finset.range n, z i = 0)
    (hx : ∀ k : ℕ, k + 1 < n → 0 ≤ x k - x (k + 1))
    (hZ : ∀ k : ℕ, k < n → 0 ≤ ∑ i ∈ Finset.range (k + 1), z i) :
    0 ≤ ∑ i ∈ Finset.range n, x i * z i := by
  have htele : ∀ i : ℕ, i < n →
      x i = x (n - 1) + ∑ k ∈ Finset.Ico i (n - 1), (x k - x (k + 1)) := by
    intro i hi
    have h1 : ∑ k ∈ Finset.Ico i (n - 1), (x (k + 1) - x k) = x (n - 1) - x i := by
      rw [Finset.sum_Ico_eq_sub _ (show i ≤ n - 1 by omega), Finset.sum_range_sub,
        Finset.sum_range_sub]
      ring
    have h2 : ∑ k ∈ Finset.Ico i (n - 1), (x k - x (k + 1)) = x i - x (n - 1) := by
      rw [Finset.sum_congr rfl (fun k _ => (neg_sub (x (k + 1)) (x k)).symm),
        Finset.sum_neg_distrib, h1]
      ring
    rw [h2]
    ring
  have hswap : (∑ i ∈ Finset.range n, ∑ k ∈ Finset.Ico i (n - 1), z i * (x k - x (k + 1))) =
      ∑ k ∈ Finset.range (n - 1), ∑ i ∈ Finset.range (k + 1), z i * (x k - x (k + 1)) := by
    have e1 : (∑ i ∈ Finset.range n, ∑ k ∈ Finset.Ico i (n - 1), z i * (x k - x (k + 1))) =
        ∑ p ∈ (Finset.range n).sigma (fun i => Finset.Ico i (n - 1)),
          z p.1 * (x p.2 - x (p.2 + 1)) := by
      rw [Finset.sum_sigma]
    have e2 : (∑ k ∈ Finset.range (n - 1), ∑ i ∈ Finset.range (k + 1),
          z i * (x k - x (k + 1))) =
        ∑ p ∈ (Finset.range (n - 1)).sigma (fun k => Finset.range (k + 1)),
          z p.2 * (x p.1 - x (p.1 + 1)) := by
      rw [Finset.sum_sigma]
    rw [e1, e2]
    apply Finset.sum_bij (fun p _ => ⟨p.2, p.1⟩)
    · intro ⟨i, k⟩ hp
      show (⟨k, i⟩ : Σ _ : ℕ, ℕ) ∈ (Finset.range (n - 1)).sigma (fun k => Finset.range (k + 1))
      simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Ico] at hp
      simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_range]
      omega
    · intro ⟨i, k⟩ _ ⟨i', k'⟩ _ h
      simp only [Sigma.mk.injEq, heq_iff_eq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    · intro ⟨k, i⟩ hq
      simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_range] at hq
      refine ⟨⟨i, k⟩, ?_, rfl⟩
      show (⟨i, k⟩ : Σ _ : ℕ, ℕ) ∈ (Finset.range n).sigma (fun i => Finset.Ico i (n - 1))
      simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Ico]
      omega
    · intro ⟨i, k⟩ _
      rfl
  calc (0:ℝ) ≤ ∑ k ∈ Finset.range (n - 1), (x k - x (k + 1)) * (∑ i ∈ Finset.range (k + 1), z i) := by
        apply Finset.sum_nonneg
        intro k hk
        rw [Finset.mem_range] at hk
        exact mul_nonneg (hx k (by omega)) (hZ k (by omega))
    _ = ∑ i ∈ Finset.range n, x i * z i := by
        have e1 : (∑ i ∈ Finset.range n, x i * z i) =
            ∑ i ∈ Finset.range n,
              (x (n - 1) + ∑ k ∈ Finset.Ico i (n - 1), (x k - x (k + 1))) * z i := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [htele i (Finset.mem_range.1 hi)]
        rw [e1]
        rw [Finset.sum_congr rfl (fun i _ => add_mul _ _ _)]
        rw [Finset.sum_add_distrib]
        rw [← Finset.mul_sum, hz, mul_zero, zero_add]
        rw [Finset.sum_congr rfl (fun i _ => Finset.sum_mul _ _ _)]
        rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => mul_comm _ _))]
        rw [hswap]
        rw [Finset.sum_congr rfl (fun k _ => (Finset.sum_mul _ _ _).symm)]
        rw [Finset.sum_congr rfl (fun k _ => mul_comm _ _)]

/-- Rearrangement inequality (upper bound): for two decreasing sequences, the
"identity" pairing maximizes `∑ x i * y (σ i)` over all permutations `σ`. -/
lemma rearr_upper {n : ℕ} (x y : Fin n → ℝ) (hx : Antitone x) (hy : Antitone y)
    (σ : Equiv.Perm (Fin n)) :
    ∑ i, x i * y (σ i) ≤ ∑ i, x i * y i := by
  have hz : (∑ i ∈ Finset.range n, (if h : i < n then (y ⟨i, h⟩ - y (σ ⟨i, h⟩)) else 0)) = 0 := by
    have e1 : (∑ i ∈ Finset.range n, (if h : i < n then (y ⟨i, h⟩ - y (σ ⟨i, h⟩)) else 0)) =
        ∑ i : Fin n, (y i - y (σ i)) := by
      rw [Finset.sum_range]
      apply Finset.sum_congr rfl
      intro i _
      simp only [dif_pos i.isLt, Fin.eta i i.isLt]
    rw [e1, Finset.sum_sub_distrib, Equiv.sum_comp σ y, sub_self]
  have hxd : ∀ k : ℕ, k + 1 < n → 0 ≤ (if h : k < n then x ⟨k, h⟩ else 0) -
      (if h : k + 1 < n then x ⟨k + 1, h⟩ else 0) := by
    intro k hk
    rw [dif_pos (by omega : k < n), dif_pos hk]
    exact sub_nonneg.2 (hx (by rw [Fin.le_def]; exact Nat.le_succ k))
  have hZ : ∀ k : ℕ, k < n → 0 ≤ ∑ i ∈ Finset.range (k + 1),
      (if h : i < n then (y ⟨i, h⟩ - y (σ ⟨i, h⟩)) else 0) := by
    intro k hk
    have e1 : (∑ i ∈ Finset.range (k + 1), (if h : i < n then (y ⟨i, h⟩ - y (σ ⟨i, h⟩)) else 0)) =
        ∑ i : Fin (k + 1), (y ⟨i.val, lt_of_lt_of_le i.isLt hk⟩ -
          y (σ ⟨i.val, lt_of_lt_of_le i.isLt hk⟩)) := by
      rw [Finset.sum_range]
      apply Finset.sum_congr rfl
      intro i _
      simp only [dif_pos (lt_of_lt_of_le i.isLt hk)]
    rw [e1, Finset.sum_sub_distrib, sub_nonneg]
    let e : Fin (k + 1) ↪ Fin n := ⟨fun i => σ ⟨i.val, lt_of_lt_of_le i.isLt hk⟩, by
      intro a b hab
      have h := (Equiv.injective σ) hab
      rw [Fin.mk.injEq] at h
      exact Fin.ext h⟩
    have h1 : (∑ i : Fin (k + 1), y (σ ⟨i.val, lt_of_lt_of_le i.isLt hk⟩)) =
        ∑ i ∈ Finset.map e Finset.univ, y i :=
      (Finset.sum_map Finset.univ e y).symm
    rw [h1]
    exact topsum y hy (Finset.map e Finset.univ)
      (by rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]) (by omega)
  have hab : 0 ≤ ∑ i ∈ Finset.range n, (fun i => if h : i < n then x ⟨i, h⟩ else 0) i *
      (fun i => if h : i < n then (y ⟨i, h⟩ - y (σ ⟨i, h⟩)) else 0) i :=
    abel_nonneg _ _ hz hxd hZ
  have hconv : (∑ i ∈ Finset.range n, (if h : i < n then x ⟨i, h⟩ else 0) *
      (if h : i < n then (y ⟨i, h⟩ - y (σ ⟨i, h⟩)) else 0)) =
      ∑ i : Fin n, x i * (y i - y (σ i)) := by
    rw [Finset.sum_range]
    apply Finset.sum_congr rfl
    intro i _
    simp only [dif_pos i.isLt, Fin.eta i i.isLt]
  have hab2 : 0 ≤ ∑ i : Fin n, x i * (y i - y (σ i)) := by
    rw [← hconv]
    exact hab
  rw [Finset.sum_congr rfl (fun i _ => mul_sub (x i) (y i) (y (σ i))),
    Finset.sum_sub_distrib] at hab2
  exact sub_nonneg.1 hab2

/-- Rearrangement inequality (lower bound): for two decreasing sequences, the
"reversed" pairing minimizes `∑ x i * y (σ i)` over all permutations `σ`. -/
lemma rearr_lower {n : ℕ} (x y : Fin n → ℝ) (hx : Antitone x) (hy : Antitone y)
    (σ : Equiv.Perm (Fin n)) :
    ∑ i, x i * y (Fin.rev i) ≤ ∑ i, x i * y (σ i) := by
  have hz : (∑ i ∈ Finset.range n, (if h : i < n then (y (σ ⟨i, h⟩) - y (Fin.rev ⟨i, h⟩)) else 0)) = 0 := by
    have e1 : (∑ i ∈ Finset.range n, (if h : i < n then (y (σ ⟨i, h⟩) - y (Fin.rev ⟨i, h⟩)) else 0)) =
        ∑ i : Fin n, (y (σ i) - y (Fin.rev i)) := by
      rw [Finset.sum_range]
      apply Finset.sum_congr rfl
      intro i _
      simp only [dif_pos i.isLt, Fin.eta i i.isLt]
    rw [e1, Finset.sum_sub_distrib, Equiv.sum_comp σ y]
    have hrev : (∑ i : Fin n, y (Fin.rev i)) = ∑ i : Fin n, y i := Equiv.sum_comp Fin.revPerm y
    rw [hrev, sub_self]
  have hxd : ∀ k : ℕ, k + 1 < n → 0 ≤ (if h : k < n then x ⟨k, h⟩ else 0) -
      (if h : k + 1 < n then x ⟨k + 1, h⟩ else 0) := by
    intro k hk
    rw [dif_pos (by omega : k < n), dif_pos hk]
    exact sub_nonneg.2 (hx (by rw [Fin.le_def]; exact Nat.le_succ k))
  have hZ : ∀ k : ℕ, k < n → 0 ≤ ∑ i ∈ Finset.range (k + 1),
      (if h : i < n then (y (σ ⟨i, h⟩) - y (Fin.rev ⟨i, h⟩)) else 0) := by
    intro k hk
    have e1 : (∑ i ∈ Finset.range (k + 1), (if h : i < n then (y (σ ⟨i, h⟩) - y (Fin.rev ⟨i, h⟩)) else 0)) =
        ∑ i : Fin (k + 1), (y (σ ⟨i.val, lt_of_lt_of_le i.isLt hk⟩) -
          y (Fin.rev ⟨i.val, lt_of_lt_of_le i.isLt hk⟩)) := by
      rw [Finset.sum_range]
      apply Finset.sum_congr rfl
      intro i _
      simp only [dif_pos (lt_of_lt_of_le i.isLt hk)]
    rw [e1, Finset.sum_sub_distrib, sub_nonneg]
    let e : Fin (k + 1) ↪ Fin n := ⟨fun i => σ ⟨i.val, lt_of_lt_of_le i.isLt hk⟩, by
      intro a b hab
      have h := (Equiv.injective σ) hab
      rw [Fin.mk.injEq] at h
      exact Fin.ext h⟩
    have h1 : (∑ i : Fin (k + 1), y (σ ⟨i.val, lt_of_lt_of_le i.isLt hk⟩)) =
        ∑ i ∈ Finset.map e Finset.univ, y i :=
      (Finset.sum_map Finset.univ e y).symm
    rw [h1]
    exact bottomsum y hy (Finset.map e Finset.univ)
      (by rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]) (by omega)
  have hab : 0 ≤ ∑ i ∈ Finset.range n, (fun i => if h : i < n then x ⟨i, h⟩ else 0) i *
      (fun i => if h : i < n then (y (σ ⟨i, h⟩) - y (Fin.rev ⟨i, h⟩)) else 0) i :=
    abel_nonneg _ _ hz hxd hZ
  have hconv : (∑ i ∈ Finset.range n, (if h : i < n then x ⟨i, h⟩ else 0) *
      (if h : i < n then (y (σ ⟨i, h⟩) - y (Fin.rev ⟨i, h⟩)) else 0)) =
      ∑ i : Fin n, x i * (y (σ i) - y (Fin.rev i)) := by
    rw [Finset.sum_range]
    apply Finset.sum_congr rfl
    intro i _
    simp only [dif_pos i.isLt, Fin.eta i i.isLt]
  have hab2 : 0 ≤ ∑ i : Fin n, x i * (y (σ i) - y (Fin.rev i)) := by
    rw [← hconv]
    exact hab
  rw [Finset.sum_congr rfl (fun i _ => mul_sub (x i) (y (σ i)) (y (Fin.rev i))),
    Finset.sum_sub_distrib] at hab2
  exact sub_nonneg.1 hab2

snip end

/-- USA Mathematical Olympiad 2020, Problem 6. -/
problem usa2020_p6 {n : ℕ} (hn : 2 ≤ n) (x y : Fin n → ℝ)
    (hx : Antitone x) (hy : Antitone y)
    (hxs : ∑ i, x i = 0) (hys : ∑ i, y i = 0)
    (hx2 : ∑ i, x i ^ 2 = 1) (hy2 : ∑ i, y i ^ 2 = 1) :
    ∑ i, (x i * y i - x i * y (Fin.rev i)) ≥ 2 / Real.sqrt ((n : ℝ) - 1) := by
  obtain ⟨σM, -, hσM⟩ :=
    Finset.exists_max_image univ (fun σ : Equiv.Perm (Fin n) => ∑ i, x i * y (σ i))
      Finset.univ_nonempty
  obtain ⟨σm, -, hσm⟩ :=
    Finset.exists_min_image univ (fun σ : Equiv.Perm (Fin n) => ∑ i, x i * y (σ i))
      Finset.univ_nonempty
  have hvar : 2 / Real.sqrt ((n : ℝ) - 1) ≤ (∑ i, x i * y (σM i)) - (∑ i, x i * y (σm i)) :=
    variance_bound hn x y hxs hys hx2 hy2 _ _
      (fun σ => hσm σ (Finset.mem_univ σ)) (fun σ => hσM σ (Finset.mem_univ σ))
  have h2 := rearr_upper x y hx hy σM
  have h3 := rearr_lower x y hx hy σm
  have h4 : 2 / Real.sqrt ((n : ℝ) - 1) ≤ (∑ i, x i * y i) - (∑ i, x i * y (Fin.rev i)) := by
    linarith
  rw [← Finset.sum_sub_distrib] at h4
  exact h4

end Usa2020P6
