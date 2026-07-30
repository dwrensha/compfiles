/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.EuclideanDomain.Basic
public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Normed.Field.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics, .Inequality] }

/-!
# USA Mathematical Olympiad 2024, Problem 6

Let n > 2 be an integer and let ℓ ∈ {1, 2, ..., n}. A collection A₁, ..., Aₖ
of (not necessarily distinct) subsets of {1, 2, ..., n} is called ℓ-large if
|Aᵢ| ≥ ℓ for all 1 ≤ i ≤ k. Find, in terms of n and ℓ, the largest real
number c such that the inequality

  ∑ᵢ ∑ⱼ xᵢ xⱼ |Aᵢ ∩ Aⱼ|²/(|Aᵢ|·|Aⱼ|) ≥ c (∑ᵢ xᵢ)²

holds for all positive integers k, all nonnegative real numbers x₁, ..., xₖ,
and all ℓ-large collections A₁, ..., Aₖ of subsets of {1, ..., n}.
-/

namespace Usa2024P6

/-- The answer: `c = (n + ℓ² - 2ℓ)/(n(n-1))`. -/
noncomputable determine solution : ℕ → ℕ → ℝ := fun n ℓ =>
  ((n : ℝ) + (ℓ : ℝ) ^ 2 - 2 * (ℓ : ℝ)) / ((n : ℝ) * ((n : ℝ) - 1))

/-- `Works n ℓ c` says that the inequality of the problem holds with constant
`c`: for every positive integer `k`, all nonnegative weights `x₁, ..., xₖ` and
every ℓ-large collection `A₁, ..., Aₖ` of subsets of `{1, ..., n}`. -/
noncomputable def Works (n ℓ : ℕ) (c : ℝ) : Prop :=
  ∀ (k : ℕ), 0 < k → ∀ (x : Fin k → ℝ), (∀ i, 0 ≤ x i) →
    ∀ (A : Fin k → Finset (Fin n)), (∀ i, ℓ ≤ (A i).card) →
      c * (∑ i, x i) ^ 2 ≤
        ∑ i, ∑ j, x i * x j *
          (((A i ∩ A j).card : ℝ) ^ 2 / ((A i).card : ℝ) / ((A j).card : ℝ))

snip begin

/-- The quantity `v_{p,q}` from the official solution: the total normalized
weight of the sets containing both `p` and `q`. -/
noncomputable def vvv {n k : ℕ} (x : Fin k → ℝ) (A : Fin k → Finset (Fin n))
    (p q : Fin n) : ℝ :=
  ∑ i : Fin k, if p ∈ A i ∧ q ∈ A i then x i / (A i).card else 0

lemma vvv_def {n k : ℕ} (x : Fin k → ℝ) (A : Fin k → Finset (Fin n)) (p q : Fin n) :
    vvv x A p q = ∑ i : Fin k, if p ∈ A i ∧ q ∈ A i then x i / (A i).card else 0 :=
  rfl

/-- Intersection cardinality as a sum of indicators. -/
lemma card_inter_cast {n : ℕ} (A B : Finset (Fin n)) :
    ((A ∩ B).card : ℝ) = ∑ p : Fin n, (if p ∈ A ∧ p ∈ B then (1 : ℝ) else 0) := by
  classical
  have h1 : A ∩ B = Finset.univ.filter (fun p => p ∈ A ∧ p ∈ B) := by
    ext p
    simp [Finset.mem_inter]
  rw [h1, Finset.natCast_card_filter]

/-- Swapping the order of a quadruple sum. -/
lemma sum_swap4 {n k : ℕ} (F : Fin k → Fin k → Fin n → Fin n → ℝ) :
    (∑ i : Fin k, ∑ j : Fin k, ∑ p : Fin n, ∑ q : Fin n, F i j p q) =
      ∑ p : Fin n, ∑ q : Fin n, ∑ i : Fin k, ∑ j : Fin k, F i j p q := by
  rw [show (∑ i : Fin k, ∑ j : Fin k, ∑ p : Fin n, ∑ q : Fin n, F i j p q) =
      ∑ i : Fin k, ∑ p : Fin n, ∑ q : Fin n, ∑ j : Fin k, F i j p q from
    Finset.sum_congr rfl fun i _ => by
      rw [show (∑ j : Fin k, ∑ p : Fin n, ∑ q : Fin n, F i j p q) =
          ∑ p : Fin n, ∑ j : Fin k, ∑ q : Fin n, F i j p q from Finset.sum_comm]
      exact Finset.sum_congr rfl fun p _ => Finset.sum_comm]
  rw [show (∑ i : Fin k, ∑ p : Fin n, ∑ q : Fin n, ∑ j : Fin k, F i j p q) =
      ∑ p : Fin n, ∑ q : Fin n, ∑ i : Fin k, ∑ j : Fin k, F i j p q from
    by rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun p _ => Finset.sum_comm]

/-- The key rewriting step: the left-hand side of the inequality equals the
sum of the squares of the `v_{p,q}`. -/
lemma lhs_eq_sum_v_sq {n k : ℕ} (x : Fin k → ℝ) (A : Fin k → Finset (Fin n)) :
    ∑ i : Fin k, ∑ j : Fin k, x i * x j *
        (((A i ∩ A j).card : ℝ) ^ 2 / ((A i).card : ℝ) / ((A j).card : ℝ)) =
      ∑ p : Fin n, ∑ q : Fin n, (vvv x A p q) ^ 2 := by
  classical
  have per : ∀ i j : Fin k,
      x i * x j *
          (((A i ∩ A j).card : ℝ) ^ 2 / ((A i).card : ℝ) / ((A j).card : ℝ)) =
        ∑ p : Fin n, ∑ q : Fin n,
          (if p ∈ A i ∧ q ∈ A i then x i / (A i).card else 0) *
            (if p ∈ A j ∧ q ∈ A j then x j / (A j).card else 0) := by
    intro i j
    set e : Fin k → Fin n → ℝ := fun r s => if s ∈ A r then 1 else 0 with he
    have hcard : ((A i ∩ A j).card : ℝ) = ∑ p : Fin n, e i p * e j p := by
      rw [card_inter_cast]
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hp : p ∈ A i ∧ p ∈ A j
      · rw [if_pos hp]
        have h1 : e i p = 1 := by simp [he, hp.1]
        have h2 : e j p = 1 := by simp [he, hp.2]
        rw [h1, h2, mul_one]
      · rw [if_neg hp]
        rcases not_and_or.mp hp with hpi | hpj
        · have h1 : e i p = 0 := by simp [he, hpi]
          rw [h1, zero_mul]
        · have h2 : e j p = 0 := by simp [he, hpj]
          rw [h2, mul_zero]
    calc x i * x j *
          (((A i ∩ A j).card : ℝ) ^ 2 / ((A i).card : ℝ) / ((A j).card : ℝ))
        = x i * x j * ((∑ p : Fin n, e i p * e j p) ^ 2 /
            ((A i).card : ℝ) / ((A j).card : ℝ)) := by rw [hcard]
      _ = ∑ p : Fin n, ∑ q : Fin n,
            (x i * x j / ((A i).card : ℝ) / ((A j).card : ℝ)) *
              ((e i p * e j p) * (e i q * e j q)) := by
          rw [sq, Finset.sum_mul_sum, ← mul_div_assoc, ← mul_div_assoc, Finset.mul_sum,
            Finset.sum_div, Finset.sum_div]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.mul_sum, Finset.sum_div, Finset.sum_div]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
      _ = ∑ p : Fin n, ∑ q : Fin n,
            (if p ∈ A i ∧ q ∈ A i then x i / (A i).card else 0) *
              (if p ∈ A j ∧ q ∈ A j then x j / (A j).card else 0) := by
          refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
          rw [show (e i p * e j p) * (e i q * e j q) =
              (if p ∈ A i ∧ q ∈ A i then (1 : ℝ) else 0) *
                (if p ∈ A j ∧ q ∈ A j then (1 : ℝ) else 0) from by
            by_cases h1 : p ∈ A i <;> by_cases h2 : q ∈ A i <;>
              by_cases h3 : p ∈ A j <;> by_cases h4 : q ∈ A j <;>
              simp [he, h1, h2, h3, h4]]
          by_cases h1 : p ∈ A i ∧ q ∈ A i <;> by_cases h2 : p ∈ A j ∧ q ∈ A j <;>
            simp [h1, h2, div_mul_div_comm, div_div]
  calc ∑ i : Fin k, ∑ j : Fin k, x i * x j *
        (((A i ∩ A j).card : ℝ) ^ 2 / ((A i).card : ℝ) / ((A j).card : ℝ))
      = ∑ i : Fin k, ∑ j : Fin k, ∑ p : Fin n, ∑ q : Fin n,
          (if p ∈ A i ∧ q ∈ A i then x i / (A i).card else 0) *
            (if p ∈ A j ∧ q ∈ A j then x j / (A j).card else 0) := by
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => per i j
    _ = ∑ p : Fin n, ∑ q : Fin n, ∑ i : Fin k, ∑ j : Fin k,
          (if p ∈ A i ∧ q ∈ A i then x i / (A i).card else 0) *
            (if p ∈ A j ∧ q ∈ A j then x j / (A j).card else 0) :=
        sum_swap4 _
    _ = ∑ p : Fin n, ∑ q : Fin n, (vvv x A p q) ^ 2 := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
        rw [vvv_def, sq]
        exact (Finset.sum_mul_sum _ _ _ _).symm

/-- The "diagonal" sum: `∑ p, v_{p,p} = ∑ i, x i`. -/
lemma sum_diag {n k : ℕ} (x : Fin k → ℝ) (A : Fin k → Finset (Fin n))
    (hA : ∀ i, (A i).card ≠ 0) :
    ∑ p : Fin n, vvv x A p p = ∑ i : Fin k, x i := by
  classical
  simp only [vvv_def, and_self]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_filter]
  rw [show Finset.univ.filter (· ∈ A i) = A i from by ext p; simp]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hAi : ((A i).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hA i)
  rw [← mul_div_assoc]
  exact mul_div_cancel_left₀ _ hAi

/-- Sums over the off-diagonal pairs as double sums. -/
lemma sum_sigma_erase {n : ℕ} (f : Fin n → Fin n → ℝ) :
    ∑ t ∈ Finset.univ.sigma (fun p : Fin n => Finset.univ.erase p), f t.1 t.2 =
      ∑ p : Fin n, ∑ q ∈ Finset.univ.erase p, f p q :=
  (Finset.sum_sigma' _ _ _).symm

/-- The "off-diagonal" sum: `∑ p ≠ q, v_{p,q} = ∑ i, (|Aᵢ| - 1)·xᵢ`. -/
lemma sum_offdiag {n k : ℕ} (x : Fin k → ℝ) (A : Fin k → Finset (Fin n))
    (hA : ∀ i, (A i).card ≠ 0) :
    ∑ t ∈ Finset.univ.sigma (fun p : Fin n => Finset.univ.erase p), vvv x A t.1 t.2 =
      ∑ i : Fin k, (((A i).card : ℝ) - 1) * x i := by
  classical
  simp only [vvv_def]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_filter]
  have hf : (Finset.univ.sigma (fun p : Fin n => Finset.univ.erase p)).filter
        (fun t => t.1 ∈ A i ∧ t.2 ∈ A i) = (A i).sigma (fun p => (A i).erase p) := by
    ext ⟨p, q⟩
    simp only [Finset.mem_filter, Finset.mem_sigma, Finset.mem_univ, Finset.mem_erase,
      true_and]
    tauto
  rw [hf]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (((A i).sigma (fun p => (A i).erase p)).card : ℝ) =
      ((A i).card : ℝ) * (((A i).card : ℝ) - 1) := by
    have h1 : ∀ p ∈ A i, (((A i).erase p).card : ℝ) = ((A i).card : ℝ) - 1 := by
      intro p hp
      rw [Finset.card_erase_of_mem hp, Nat.cast_sub (Finset.card_pos.mpr ⟨p, hp⟩),
        Nat.cast_one]
    rw [Finset.card_sigma, Nat.cast_sum, Finset.sum_congr rfl h1, Finset.sum_const,
      nsmul_eq_mul]
  rw [hcard]
  have hAi : ((A i).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hA i)
  field_simp [hAi]

/-- Splitting `∑ p, ∑ q, (v_{p,q})²` into diagonal and off-diagonal parts. -/
lemma sum_sq_split {n k : ℕ} (x : Fin k → ℝ) (A : Fin k → Finset (Fin n)) :
    ∑ p : Fin n, ∑ q : Fin n, (vvv x A p q) ^ 2 =
      (∑ p : Fin n, (vvv x A p p) ^ 2) +
        ∑ p : Fin n, ∑ q ∈ Finset.univ.erase p, (vvv x A p q) ^ 2 := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => (Finset.add_sum_erase _ _ (Finset.mem_univ p)).symm

/-- The answer in split form: `c·S² = S²/n + (ℓ-1)²·S²/(n(n-1))`. -/
lemma solution_eq {n ℓ : ℕ} (hn : 2 < n) (S : ℝ) :
    solution n ℓ * S ^ 2 =
      S ^ 2 / (n : ℝ) + ((ℓ : ℝ) - 1) ^ 2 * S ^ 2 / ((n : ℝ) * ((n : ℝ) - 1)) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have h1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    exact sub_ne_zero.mpr (ne_of_gt h1)
  unfold solution
  field_simp
  ring

/-- The claimed constant works (first part of `IsGreatest`). -/
lemma solution_works {n ℓ : ℕ} (hn : 2 < n) (hℓ1 : 1 ≤ ℓ) :
    Works n ℓ (solution n ℓ) := by
  intro k _hk x hx A hA
  have hA0 : ∀ i, (A i).card ≠ 0 := fun i => by
    have h1 := hA i
    omega
  rw [lhs_eq_sum_v_sq, sum_sq_split, ← sum_sigma_erase]
  rw [solution_eq hn (∑ i, x i)]
  refine add_le_add ?_ ?_
  · -- Diagonal part: `S²/n ≤ ∑ p, (v_{p,p})²` by QM-AM.
    have hsum := sum_diag x A hA0
    have hQM := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
      (f := fun p => vvv x A p p)
    rw [Finset.card_univ, Fintype.card_fin] at hQM
    rw [hsum] at hQM
    rw [div_le_iff₀ (show (0 : ℝ) < (n : ℝ) by exact_mod_cast (by omega : 0 < n))]
    exact le_trans hQM (le_of_eq (mul_comm _ _))
  · -- Off-diagonal part: `(ℓ-1)²S²/(n(n-1)) ≤ ∑ p≠q, (v_{p,q})²`.
    have hsum := sum_offdiag x A hA0
    have hge : ((ℓ : ℝ) - 1) * (∑ i, x i) ≤
        ∑ t ∈ Finset.univ.sigma (fun p : Fin n => Finset.univ.erase p), vvv x A t.1 t.2 := by
      rw [hsum, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      exact mul_le_mul_of_nonneg_right (sub_le_sub_right (Nat.cast_le.mpr (hA i)) 1) (hx i)
    have hS : (0 : ℝ) ≤ ∑ i, x i := Finset.sum_nonneg fun i _ => hx i
    have hℓ1' : (0 : ℝ) ≤ (ℓ : ℝ) - 1 := sub_nonneg.mpr (by exact_mod_cast hℓ1)
    have hnn : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by
      have h1 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      have h2 : (0 : ℝ) < (n : ℝ) - 1 := by
        have h3 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
        linarith
      exact mul_pos h1 h2
    have hle : (((ℓ : ℝ) - 1) * ∑ i, x i) ^ 2 ≤
        (∑ t ∈ Finset.univ.sigma (fun p : Fin n => Finset.univ.erase p),
          vvv x A t.1 t.2) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hℓ1' hS) hge 2
    have hcardT : ((Finset.univ.sigma (fun p : Fin n => Finset.univ.erase p)).card : ℝ) =
        (n : ℝ) * ((n : ℝ) - 1) := by
      have h1 : ∀ p : Fin n, ((Finset.univ.erase p).card : ℝ) = (n : ℝ) - 1 := fun p => by
        rw [Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, Fintype.card_fin]
        rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
      rw [Finset.card_sigma, Nat.cast_sum, Finset.sum_congr rfl (fun p _ => h1 p)]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hQM := sq_sum_le_card_mul_sum_sq
      (s := Finset.univ.sigma (fun p : Fin n => Finset.univ.erase p))
      (f := fun t => vvv x A t.1 t.2)
    rw [hcardT] at hQM
    rw [div_le_iff₀ hnn]
    calc ((ℓ : ℝ) - 1) ^ 2 * (∑ i, x i) ^ 2 = (((ℓ : ℝ) - 1) * ∑ i, x i) ^ 2 :=
          (mul_pow _ _ _).symm
      _ ≤ (∑ t ∈ Finset.univ.sigma (fun p : Fin n => Finset.univ.erase p),
            vvv x A t.1 t.2) ^ 2 := hle
      _ ≤ ((n : ℝ) * ((n : ℝ) - 1)) *
            ∑ t ∈ Finset.univ.sigma (fun p : Fin n => Finset.univ.erase p),
              (vvv x A t.1 t.2) ^ 2 := hQM
      _ = (∑ t ∈ Finset.univ.sigma (fun p : Fin n => Finset.univ.erase p),
            (vvv x A t.1 t.2) ^ 2) * ((n : ℝ) * ((n : ℝ) - 1)) := mul_comm _ _

/-- Counting the elements of a finset with a weight of `1` each. -/
lemma diag_count {n : ℕ} (B : Finset (Fin n)) :
    ∑ p : Fin n, (if p ∈ B then (1 : ℝ) else 0) = (B.card : ℝ) := by
  classical
  have h' : Finset.univ.filter (· ∈ B) = B := by
    ext p
    simp
  rw [show (B.card : ℝ) = ((Finset.univ.filter (· ∈ B)).card : ℝ) from by rw [h'],
    Finset.natCast_card_filter]

/-- The pairs `(p, q)` with `p ≠ q` inside `B × B`, as a sigma finset. -/
lemma pair_filter_eq {n : ℕ} (B : Finset (Fin n)) :
    (Finset.univ.sigma (fun p : Fin n => Finset.univ.erase p)).filter
        (fun t => t.1 ∈ B ∧ t.2 ∈ B) = B.sigma (fun p => B.erase p) := by
  ext ⟨p, q⟩
  simp only [Finset.mem_filter, Finset.mem_sigma, Finset.mem_univ, Finset.mem_erase,
    true_and]
  tauto

/-- Counting ordered pairs of distinct elements of `B`. -/
lemma card_pairs {n : ℕ} (B : Finset (Fin n)) :
    ∑ p : Fin n, ∑ q ∈ Finset.univ.erase p, (if p ∈ B ∧ q ∈ B then (1 : ℝ) else 0) =
      (B.card : ℝ) * ((B.card : ℝ) - 1) := by
  classical
  rw [Finset.sum_sigma']
  rw [← Finset.sum_filter, pair_filter_eq B]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Finset.card_sigma, Nat.cast_sum]
  by_cases hB : B = ∅
  · subst hB
    simp
  · have hpos : 1 ≤ B.card :=
      Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hB)
    have h1 : ∀ p ∈ B, ((B.erase p).card : ℝ) = (B.card : ℝ) - 1 := by
      intro p hp
      rw [Finset.card_erase_of_mem hp, Nat.cast_sub hpos, Nat.cast_one]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]

/-- A permutation of `[n]` mapping `p ↦ p'` and `q ↦ q'` simultaneously. -/
lemma exists_perm_eq {n : ℕ} (p q p' q' : Fin n) (hpq : p ≠ q) (hpq' : p' ≠ q') :
    ∃ π : Equiv.Perm (Fin n), π p = p' ∧ π q = q' := by
  refine ⟨Equiv.swap ((Equiv.swap p p') q) q' * Equiv.swap p p', ?_, ?_⟩
  · show Equiv.swap ((Equiv.swap p p') q) q' ((Equiv.swap p p') p) = p'
    rw [Equiv.swap_apply_left]
    apply Equiv.swap_apply_of_ne_of_ne
    · by_cases h : q = p'
      · rw [h, Equiv.swap_apply_right]
        exact fun hcon => hpq (hcon.symm.trans h.symm)
      · rw [Equiv.swap_apply_of_ne_of_ne hpq.symm h]
        exact Ne.symm h
    · exact hpq'
  · show Equiv.swap ((Equiv.swap p p') q) q' ((Equiv.swap p p') q) = q'
    exact Equiv.swap_apply_left _ _

/-- The image of an `ℓ`-subset under a permutation is still an `ℓ`-subset. -/
lemma finsetCongr_mem_powersetCard {n ℓ : ℕ} (π : Equiv.Perm (Fin n)) (B : Finset (Fin n))
    (hB : B ∈ Finset.powersetCard ℓ (Finset.univ : Finset (Fin n))) :
    π.finsetCongr B ∈ Finset.powersetCard ℓ (Finset.univ : Finset (Fin n)) := by
  rw [Finset.mem_powersetCard] at hB ⊢
  exact ⟨Finset.subset_univ _, by rw [Equiv.finsetCongr_apply, Finset.card_map, hB.2]⟩

/-- The number of `ℓ`-subsets containing a given point does not depend on the
point. -/
lemma cntS_single {n ℓ : ℕ} (p q : Fin n) :
    ((Finset.powersetCard ℓ (Finset.univ : Finset (Fin n))).filter
        (fun B => p ∈ B)).card =
      ((Finset.powersetCard ℓ (Finset.univ : Finset (Fin n))).filter
        (fun B => q ∈ B)).card := by
  classical
  refine Finset.card_bij' (fun B _ => (Equiv.swap p q).finsetCongr B)
    (fun B _ => (Equiv.swap p q).finsetCongr B) ?_ ?_ ?_ ?_
  · intro B hB
    rw [Finset.mem_filter] at hB ⊢
    exact ⟨finsetCongr_mem_powersetCard _ _ hB.1, by
      rw [Equiv.finsetCongr_apply, Finset.mem_map]
      exact ⟨p, hB.2, Equiv.swap_apply_left p q⟩⟩
  · intro B hB
    rw [Finset.mem_filter] at hB ⊢
    exact ⟨finsetCongr_mem_powersetCard _ _ hB.1, by
      rw [Equiv.finsetCongr_apply, Finset.mem_map]
      exact ⟨q, hB.2, Equiv.swap_apply_right p q⟩⟩
  · intro B _
    show (Equiv.swap p q).finsetCongr ((Equiv.swap p q).finsetCongr B) = B
    rw [show (Equiv.swap p q).finsetCongr ((Equiv.swap p q).finsetCongr B) =
        ((Equiv.swap p q).finsetCongr.trans (Equiv.swap p q).finsetCongr) B from rfl]
    rw [Equiv.finsetCongr_trans, Equiv.swap_swap, Equiv.finsetCongr_refl]
    rfl
  · intro B _
    show (Equiv.swap p q).finsetCongr ((Equiv.swap p q).finsetCongr B) = B
    rw [show (Equiv.swap p q).finsetCongr ((Equiv.swap p q).finsetCongr B) =
        ((Equiv.swap p q).finsetCongr.trans (Equiv.swap p q).finsetCongr) B from rfl]
    rw [Equiv.finsetCongr_trans, Equiv.swap_swap, Equiv.finsetCongr_refl]
    rfl

/-- The number of `ℓ`-subsets containing two given distinct points does not
depend on the pair of points. -/
lemma cntS_pair {n ℓ : ℕ} (p q p' q' : Fin n) (hpq : p ≠ q) (hpq' : p' ≠ q') :
    ((Finset.powersetCard ℓ (Finset.univ : Finset (Fin n))).filter
        (fun B => p ∈ B ∧ q ∈ B)).card =
      ((Finset.powersetCard ℓ (Finset.univ : Finset (Fin n))).filter
        (fun B => p' ∈ B ∧ q' ∈ B)).card := by
  classical
  obtain ⟨π, hπp, hπq⟩ := exists_perm_eq p q p' q' hpq hpq'
  refine Finset.card_bij' (fun B _ => π.finsetCongr B) (fun B _ => π.symm.finsetCongr B)
    ?_ ?_ ?_ ?_
  · intro B hB
    rw [Finset.mem_filter] at hB ⊢
    refine ⟨finsetCongr_mem_powersetCard _ _ hB.1, ?_, ?_⟩
    · rw [← hπp, Equiv.finsetCongr_apply, Finset.mem_map]
      exact ⟨p, hB.2.1, rfl⟩
    · rw [← hπq, Equiv.finsetCongr_apply, Finset.mem_map]
      exact ⟨q, hB.2.2, rfl⟩
  · intro B hB
    rw [Finset.mem_filter] at hB ⊢
    refine ⟨finsetCongr_mem_powersetCard π.symm _ hB.1, ?_, ?_⟩
    · rw [Equiv.finsetCongr_apply, Finset.mem_map]
      exact ⟨p', hB.2.1, by rw [← hπp]; exact Equiv.symm_apply_apply π p⟩
    · rw [Equiv.finsetCongr_apply, Finset.mem_map]
      exact ⟨q', hB.2.2, by rw [← hπq]; exact Equiv.symm_apply_apply π q⟩
  · intro B _
    show π.symm.finsetCongr (π.finsetCongr B) = B
    rw [show π.symm.finsetCongr (π.finsetCongr B) =
        (π.finsetCongr.trans π.symm.finsetCongr) B from rfl]
    rw [Equiv.finsetCongr_trans, Equiv.self_trans_symm, Equiv.finsetCongr_refl]
    rfl
  · intro B _
    show π.finsetCongr (π.symm.finsetCongr B) = B
    rw [show π.finsetCongr (π.symm.finsetCongr B) =
        (π.symm.finsetCongr.trans π.finsetCongr) B from rfl]
    rw [Equiv.finsetCongr_trans, Equiv.symm_trans_self, Equiv.finsetCongr_refl]
    rfl

/-- Reindexing: counting indices `i` with `p, q ∈ A i` equals counting sets of
the family containing `p, q`, when `A` enumerates the family. -/
lemma cnt_bridge {n k : ℕ} (s : Finset (Finset (Fin n))) (A : Fin k → Finset (Fin n))
    (hAmem : ∀ i, A i ∈ s) (hAinj : Function.Injective A)
    (hAsurj : ∀ B ∈ s, ∃ i, A i = B) (p q : Fin n) :
    (Finset.univ.filter (fun i => p ∈ A i ∧ q ∈ A i)).card =
      (s.filter (fun B => p ∈ B ∧ q ∈ B)).card := by
  refine Finset.card_bij (fun i _ => A i) ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨hAmem i, hi.2⟩
  · intro i₁ _ i₂ _ h
    exact hAinj h
  · intro B hB
    rw [Finset.mem_filter] at hB
    obtain ⟨i, rfl⟩ := hAsurj B hB.1
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hB.2⟩, rfl⟩

/-- Reindexing, single-point version. -/
lemma cnt_bridge1 {n k : ℕ} (s : Finset (Finset (Fin n))) (A : Fin k → Finset (Fin n))
    (hAmem : ∀ i, A i ∈ s) (hAinj : Function.Injective A)
    (hAsurj : ∀ B ∈ s, ∃ i, A i = B) (p : Fin n) :
    (Finset.univ.filter (fun i => p ∈ A i)).card =
      (s.filter (fun B => p ∈ B)).card := by
  refine Finset.card_bij (fun i _ => A i) ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨hAmem i, hi.2⟩
  · intro i₁ _ i₂ _ h
    exact hAinj h
  · intro B hB
    rw [Finset.mem_filter] at hB
    obtain ⟨i, rfl⟩ := hAsurj B hB.1
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hB.2⟩, rfl⟩

/-- No constant larger than `solution n ℓ` works: equality is attained (in the
limit sense of the inequality) by taking all `ℓ`-subsets once with weight `1`
(second part of `IsGreatest`). -/
lemma solution_le_of_works {n ℓ : ℕ} (hn : 2 < n) (hℓ1 : 1 ≤ ℓ) (hℓn : ℓ ≤ n) (c : ℝ)
    (hc : Works n ℓ c) : c ≤ solution n ℓ := by
  classical
  -- The extremal family: all `ℓ`-subsets of `[n]`, each used once, weights `1`.
  set s : Finset (Finset (Fin n)) := Finset.powersetCard ℓ Finset.univ with hs
  have hscard : s.card = Nat.choose n ℓ := by
    rw [hs, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  set k : ℕ := s.card with hk
  have hkpos : 0 < k := by rw [hscard]; exact Nat.choose_pos hℓn
  have e : ↥s ≃ Fin k := Fintype.equivFinOfCardEq (by rw [hk]; exact Fintype.card_coe s)
  set A : Fin k → Finset (Fin n) := fun i => (e.symm i).1 with hA
  have hAmem : ∀ i, A i ∈ s := fun i => (e.symm i).2
  have hAcard : ∀ i, (A i).card = ℓ := fun i => (Finset.mem_powersetCard.mp (hAmem i)).2
  have hAinj : Function.Injective A := fun i₁ i₂ h => e.symm.injective (Subtype.ext h)
  have hAsurj : ∀ B ∈ s, ∃ i, A i = B := fun B hB =>
    ⟨e ⟨B, hB⟩, congrArg Subtype.val (Equiv.symm_apply_apply e ⟨B, hB⟩)⟩
  have hℓ0 : (ℓ : ℝ) ≠ 0 := by exact_mod_cast (by omega : ℓ ≠ 0)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have h1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    exact sub_ne_zero.mpr (ne_of_gt h1)
  have hnn : (n : ℝ) * ((n : ℝ) - 1) ≠ 0 := mul_ne_zero hn0 hn1
  -- Each `v_{p,q}` is `1/ℓ` times the number of sets containing `p, q`.
  have hv : ∀ p q : Fin n, vvv (1 : Fin k → ℝ) A p q =
      (1 / (ℓ : ℝ)) *
        ((Finset.univ.filter (fun i => p ∈ A i ∧ q ∈ A i)).card : ℝ) := by
    intro p q
    rw [vvv_def, ← Finset.sum_filter]
    simp only [Pi.one_apply]
    rw [Finset.sum_congr rfl (fun i _ => by rw [hAcard i])]
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  -- The number of sets containing a point `p` is `k·ℓ/n`, independently of `p`.
  have hcnt1 : ∀ p : Fin n,
      ((Finset.univ.filter (fun i => p ∈ A i)).card : ℝ) = (k : ℝ) * (ℓ : ℝ) / (n : ℝ) := by
    intro p
    have hsum : ∑ p' : Fin n, ((Finset.univ.filter (fun i => p' ∈ A i)).card : ℝ) =
        (k : ℝ) * (ℓ : ℝ) := by
      calc ∑ p' : Fin n, ((Finset.univ.filter (fun i => p' ∈ A i)).card : ℝ)
          = ∑ p' : Fin n, ∑ i : Fin k, (if p' ∈ A i then (1 : ℝ) else 0) := by
            refine Finset.sum_congr rfl fun p' _ => ?_
            rw [Finset.natCast_card_filter]
        _ = ∑ i : Fin k, ∑ p' : Fin n, (if p' ∈ A i then (1 : ℝ) else 0) :=
            Finset.sum_comm
        _ = ∑ i : Fin k, ((A i).card : ℝ) :=
            Finset.sum_congr rfl fun i _ => diag_count (A i)
        _ = ∑ i : Fin k, (ℓ : ℝ) := Finset.sum_congr rfl fun i _ => by rw [hAcard i]
        _ = (k : ℝ) * (ℓ : ℝ) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h2 : ((Finset.univ.filter (fun i => p ∈ A i)).card : ℝ) * (n : ℝ) =
        (k : ℝ) * (ℓ : ℝ) := by
      rw [← hsum]
      rw [Finset.sum_congr rfl (fun p' _ => by
        have hb1 := cnt_bridge1 s A hAmem hAinj hAsurj p
        have hb2 := cnt_bridge1 s A hAmem hAinj hAsurj p'
        have hsymm : (s.filter (fun B => p' ∈ B)).card = (s.filter (fun B => p ∈ B)).card :=
          cntS_single p' p (ℓ := ℓ)
        rw [show (Finset.univ.filter (fun i => p' ∈ A i)).card =
            (Finset.univ.filter (fun i => p ∈ A i)).card from
          hb2.trans (hsymm.trans hb1.symm)])]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]
    rw [eq_div_iff hn0]
    exact h2
  -- The number of sets containing distinct `p, q` is `k·ℓ(ℓ-1)/(n(n-1))`.
  have hcnt2 : ∀ p q : Fin n, p ≠ q →
      ((Finset.univ.filter (fun i => p ∈ A i ∧ q ∈ A i)).card : ℝ) =
        (k : ℝ) * ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) / ((n : ℝ) * ((n : ℝ) - 1)) := by
    intro p q hpq
    have hsum : ∑ p' : Fin n, ∑ q' ∈ Finset.univ.erase p',
        ((Finset.univ.filter (fun i => p' ∈ A i ∧ q' ∈ A i)).card : ℝ) =
          (k : ℝ) * ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) := by
      calc ∑ p' : Fin n, ∑ q' ∈ Finset.univ.erase p',
            ((Finset.univ.filter (fun i => p' ∈ A i ∧ q' ∈ A i)).card : ℝ)
          = ∑ p' : Fin n, ∑ q' ∈ Finset.univ.erase p', ∑ i : Fin k,
              (if p' ∈ A i ∧ q' ∈ A i then (1 : ℝ) else 0) := by
            refine Finset.sum_congr rfl fun p' _ => Finset.sum_congr rfl fun q' _ => ?_
            rw [Finset.natCast_card_filter]
        _ = ∑ t ∈ Finset.univ.sigma (fun p' : Fin n => Finset.univ.erase p'),
              ∑ i : Fin k, (if t.1 ∈ A i ∧ t.2 ∈ A i then (1 : ℝ) else 0) :=
            Finset.sum_sigma' _ _ _
        _ = ∑ i : Fin k, ∑ t ∈ Finset.univ.sigma (fun p' : Fin n => Finset.univ.erase p'),
              (if t.1 ∈ A i ∧ t.2 ∈ A i then (1 : ℝ) else 0) := Finset.sum_comm
        _ = ∑ i : Fin k, ((A i).card : ℝ) * (((A i).card : ℝ) - 1) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← card_pairs (A i), Finset.sum_sigma']
        _ = ∑ i : Fin k, (ℓ : ℝ) * ((ℓ : ℝ) - 1) :=
            Finset.sum_congr rfl fun i _ => by rw [hAcard i]
        _ = (k : ℝ) * ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h2 : ((Finset.univ.filter (fun i => p ∈ A i ∧ q ∈ A i)).card : ℝ) *
        ((n : ℝ) * ((n : ℝ) - 1)) = (k : ℝ) * ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) := by
      rw [← hsum]
      rw [Finset.sum_congr rfl (fun p' _ => Finset.sum_congr rfl (fun q' hq' => by
        have hq'ne : q' ≠ p' := (Finset.mem_erase.mp hq').1
        have hb1 := cnt_bridge s A hAmem hAinj hAsurj p q
        have hb2 := cnt_bridge s A hAmem hAinj hAsurj p' q'
        have hsymm : (s.filter (fun B => p ∈ B ∧ q ∈ B)).card =
            (s.filter (fun B => p' ∈ B ∧ q' ∈ B)).card :=
          cntS_pair p q p' q' hpq hq'ne.symm (ℓ := ℓ)
        rw [show (Finset.univ.filter (fun i => p' ∈ A i ∧ q' ∈ A i)).card =
            (Finset.univ.filter (fun i => p ∈ A i ∧ q ∈ A i)).card from
          (hb2.trans (hsymm.symm.trans hb1.symm))]))]
      rw [Finset.sum_congr rfl (fun p' _ => Finset.sum_const _)]
      rw [Finset.sum_congr rfl (fun p' _ => by
        rw [Finset.card_erase_of_mem (Finset.mem_univ p'), Finset.card_univ, Fintype.card_fin])]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      rw [nsmul_eq_mul, nsmul_eq_mul, Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one]
      ring
    rw [eq_div_iff hnn]
    exact h2
  -- The values of `v_{p,p}` and `v_{p,q}`.
  have hvpp : ∀ p : Fin n, vvv (1 : Fin k → ℝ) A p p = (k : ℝ) / (n : ℝ) := by
    intro p
    rw [hv p p]
    have hff : (Finset.univ.filter (fun i => p ∈ A i ∧ p ∈ A i)) =
        Finset.univ.filter (fun i => p ∈ A i) := by
      ext i
      simp
    rw [hff, hcnt1 p]
    field_simp
  have hvpq : ∀ p q : Fin n, p ≠ q → vvv (1 : Fin k → ℝ) A p q =
      (k : ℝ) * ((ℓ : ℝ) - 1) / ((n : ℝ) * ((n : ℝ) - 1)) := by
    intro p q hpq
    rw [hv p q, hcnt2 p q hpq]
    field_simp
  have hdiag_sum : ∑ p : Fin n, (vvv (1 : Fin k → ℝ) A p p) ^ 2 = (k : ℝ) ^ 2 / (n : ℝ) := by
    rw [Finset.sum_congr rfl (fun p _ => by rw [hvpp p])]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hoff_sum : ∑ p : Fin n, ∑ q ∈ Finset.univ.erase p,
      (vvv (1 : Fin k → ℝ) A p q) ^ 2 =
        ((ℓ : ℝ) - 1) ^ 2 * (k : ℝ) ^ 2 / ((n : ℝ) * ((n : ℝ) - 1)) := by
    rw [Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q hq => by
      rw [hvpq p q (Ne.symm (Finset.mem_erase.mp hq).1)]))]
    rw [Finset.sum_congr rfl (fun p _ => Finset.sum_const _)]
    rw [Finset.sum_congr rfl (fun p _ => by
      rw [Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, Fintype.card_fin])]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [nsmul_eq_mul, nsmul_eq_mul, Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one]
    field_simp
  have hLHS : ∑ i : Fin k, ∑ j : Fin k, (1 : Fin k → ℝ) i * (1 : Fin k → ℝ) j *
        (((A i ∩ A j).card : ℝ) ^ 2 / ((A i).card : ℝ) / ((A j).card : ℝ)) =
      solution n ℓ * (k : ℝ) ^ 2 := by
    rw [lhs_eq_sum_v_sq, sum_sq_split, hdiag_sum, hoff_sum]
    exact (solution_eq hn (k : ℝ)).symm
  -- Apply the hypothesis `hc` to this instance and read off `c ≤ solution n ℓ`.
  have hkey := hc k hkpos (1 : Fin k → ℝ) (fun i => by simp) A
    (fun i => le_of_eq (hAcard i).symm)
  have hsum1 : ∑ i : Fin k, (1 : Fin k → ℝ) i = (k : ℝ) := by
    simp only [Pi.one_apply]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [hsum1, hLHS] at hkey
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
  exact le_of_mul_le_mul_right hkey (pow_pos hk0 2)

snip end

problem usa2024_p6 (n ℓ : ℕ) (hn : 2 < n) (hℓ : 1 ≤ ℓ ∧ ℓ ≤ n) :
    IsGreatest {c : ℝ | Works n ℓ c} (solution n ℓ) := by
  refine ⟨?_, ?_⟩
  · exact solution_works hn hℓ.1
  · intro c hc
    exact solution_le_of_works hn hℓ.1 hℓ.2 c hc

end Usa2024P6
