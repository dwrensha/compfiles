/-
Copyright (c) 2023 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 2023, Problem 3

For each integer k ≥ 2, determine all infinite sequences of positive
integers a₁, a₂, ... for which there exists a polynomial P of the form

  P(x) = xᵏ + cₖ₋₁xᵏ⁻¹ + ... + c₁x + c₀,

where c₀, c₁, ..., cₖ₋₁ are non-negative integers, such that

  P(aₙ) = aₙ₊₁aₙ₊₂⋯aₙ₊ₖ

for every integer n ≥ 1.
-/

namespace Imo2023P3

open Polynomial

determine SolutionSet {k : ℕ} (hk : 2 ≤ k) : Set (ℕ+ → ℕ+) :=
  {a | ∃ a₀ d : ℕ, ∀ m : ℕ, (a ⟨m + 1, Nat.succ_pos m⟩).val = a₀ + d * m}

snip begin

/-- The polynomial `P(x) = ∏_{i=1}^{k} (x + i·d)` attached to an arithmetic
progression with common difference `d`. -/
noncomputable def apPoly (k d : ℕ) : Polynomial ℤ :=
  ∏ i ∈ Finset.range k, (X + C ((i + 1) * d : ℤ))

lemma apPoly_monic (k d : ℕ) : (apPoly k d).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_add_C _

lemma apPoly_natDegree (k d : ℕ) : (apPoly k d).natDegree = k := by
  rw [apPoly, natDegree_prod_of_monic _ _ (fun _ _ => monic_X_add_C _)]
  simp only [natDegree_X_add_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

lemma apPoly_degree (k d : ℕ) : (apPoly k d).degree = k := by
  rw [degree_eq_natDegree (apPoly_monic k d).ne_zero, apPoly_natDegree k d]

lemma coeff_X_add_C_nonneg {c : ℤ} (hc : 0 ≤ c) (j : ℕ) :
    0 ≤ (X + C c : ℤ[X]).coeff j := by
  rw [coeff_add, coeff_X, coeff_C]
  split_ifs with h1 h2 h2 <;> simp_all

/-- Coercion of a `ℕ+`-valued product to `ℤ`. -/
lemma pnat_prod_coe {ι : Type*} (s : Finset ι) (f : ι → ℕ+) :
    ((∏ i ∈ s, f i : ℕ+) : ℤ) = ∏ i ∈ s, ((f i : ℕ+) : ℤ) := by
  norm_cast

/-- Telescoping sum of consecutive differences over `ℤ`. -/
lemma sum_range_sub_self {f : ℕ → ℤ} (n : ℕ) :
    ∑ i ∈ Finset.range n, (f (i + 1) - f i) = f n - f 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

/-- For naturals, `x ^ k ≤ y ^ k` implies `x ≤ y`. -/
lemma le_of_pow_le {x y k : ℕ} (hk : 0 < k) (h : x ^ k ≤ y ^ k) : x ≤ y := by
  by_cases h' : x ≤ y
  · exact h'
  · have h'' : y < x := lt_of_not_ge h'
    exact absurd h (not_le_of_gt (pow_lt_pow_left₀ h'' (Nat.zero_le y) (Nat.pos_iff_ne_zero.1 hk)))

/-- First two terms of the binomial expansion bound the power below. -/
lemma pow_ge_add_mul (x y n : ℕ) :
    x ^ (n + 1) + (n + 1) * x ^ n * y ≤ (x + y) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have e : (x + y) ^ (n + 2) = (x + y) ^ (n + 1) * (x + y) := by ring
      rw [e]
      calc x ^ (n + 2) + (n + 2) * x ^ (n + 1) * y
          ≤ (x ^ (n + 1) + (n + 1) * x ^ n * y) * (x + y) := by
            have : (x ^ (n + 1) + (n + 1) * x ^ n * y) * (x + y) =
                x ^ (n + 2) + (n + 2) * x ^ (n + 1) * y + (n + 1) * x ^ n * y * y := by ring
            rw [this]
            exact Nat.le_add_right _ _
        _ ≤ (x + y) ^ (n + 1) * (x + y) := by gcongr

/-- Expansion of `P.eval` for a monic `P` of degree `k`. -/
lemma eval_eq {k : ℕ} (_hk : 2 ≤ k) {P : Polynomial ℤ} (hmon : P.Monic)
    (hdeg : P.degree = k) (x : ℤ) :
    P.eval x = x ^ k + ∑ j ∈ Finset.range k, P.coeff j * x ^ j := by
  have hnd : P.natDegree = k := natDegree_eq_of_degree_eq_some hdeg
  conv_lhs => rw [eval_eq_sum_range, hnd]
  rw [Finset.sum_range_succ]
  have hlead : P.coeff k = 1 := by
    rw [← hnd]
    exact hmon.leadingCoeff
  rw [hlead, one_mul, add_comm]

/-- `P.eval` is positive at positive integers. -/
lemma eval_pos {k : ℕ} (_hk : 2 ≤ k) {P : Polynomial ℤ} (hmon : P.Monic)
    (hdeg : P.degree = k) (hcoef : ∀ n, n ≤ k → 0 ≤ P.coeff n)
    {x : ℤ} (hx : 0 < x) :
    0 < P.eval x := by
  rw [eval_eq _hk hmon hdeg x]
  apply add_pos_of_pos_of_nonneg (pow_pos hx k)
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (hcoef j (Nat.le_of_lt (Finset.mem_range.1 hj))) (pow_nonneg hx.le j)

/-- `P.eval` is strictly increasing on positive integers. -/
lemma eval_strictMono {k : ℕ} (hk : 2 ≤ k) {P : Polynomial ℤ} (hmon : P.Monic)
    (hdeg : P.degree = k) (hcoef : ∀ n, n ≤ k → 0 ≤ P.coeff n)
    {x y : ℤ} (hx : 0 < x) (hxy : x < y) :
    P.eval x < P.eval y := by
  rw [eval_eq hk hmon hdeg x, eval_eq hk hmon hdeg y]
  apply add_lt_add_of_lt_of_le
  · exact pow_lt_pow_left₀ hxy hx.le (by omega)
  · apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.le hxy.le j)
      (hcoef j (Nat.le_of_lt (Finset.mem_range.1 hj)))

/-- The key recurrence obtained by dividing two consecutive instances of the
functional equation: `a_{n+k+1}·P(a_n) = a_{n+1}·P(a_{n+1})`. -/
lemma key_recurrence {k : ℕ} {P : Polynomial ℤ} {A : ℕ → ℕ}
    (hA : ∀ m : ℕ, P.eval (A m : ℤ) = ∏ i ∈ Finset.range k, (A (m + 1 + i) : ℤ))
    (m : ℕ) :
    (A (m + 1 + k) : ℤ) * P.eval (A m : ℤ) = (A (m + 1) : ℤ) * P.eval (A (m + 1) : ℤ) := by
  rw [hA m, hA (m + 1)]
  set f := fun i => (A (m + 1 + i) : ℤ) with hf
  have h1 : (∏ i ∈ Finset.range k, (A (m + 1 + 1 + i) : ℤ)) =
      ∏ i ∈ Finset.range k, f (i + 1) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hf, Nat.add_right_comm, Nat.add_assoc]
  rw [h1]
  have h2 : (A (m + 1) : ℤ) = f 0 := by rw [hf]
  have h3 : (A (m + 1 + k) : ℤ) = f k := by rw [hf]
  rw [h2, h3]
  have e1 : f 0 * ∏ i ∈ Finset.range k, f (i + 1) = ∏ i ∈ Finset.range (k + 1), f i := by
    rw [Finset.prod_range_succ', mul_comm]
  have e2 : f k * ∏ i ∈ Finset.range k, f i = ∏ i ∈ Finset.range (k + 1), f i := by
    rw [Finset.prod_range_succ, mul_comm]
  rw [e1, e2]

/-- The sequence reindexed by `ℕ`: `seqA a m = a_{m+1}`. -/
def seqA (a : ℕ+ → ℕ+) (m : ℕ) : ℕ := (a ⟨m + 1, Nat.succ_pos m⟩).val

lemma seqA_pos (a : ℕ+ → ℕ+) (m : ℕ) : 0 < seqA a m := (a _).pos

/-- The functional equation restated for the `ℕ`-indexed sequence. -/
lemma hA_of {k : ℕ} {P : Polynomial ℤ} {a : ℕ+ → ℕ+}
    (hP : ∀ n : ℕ+, P.eval ((a n) : ℤ) =
      ∏ i ∈ Finset.range k, a ⟨n + i + 1, Nat.succ_pos _⟩) (m : ℕ) :
    P.eval (seqA a m : ℤ) = ∏ i ∈ Finset.range k, (seqA a (m + 1 + i) : ℤ) := by
  have h := hP ⟨m + 1, Nat.succ_pos m⟩
  rw [pnat_prod_coe] at h
  exact h.trans (Finset.prod_congr rfl fun _ _ => rfl)

/-- `Csum P k = Σ_{j<k} P.coeff j`, the total mass of the lower coefficients. -/
def Csum (P : Polynomial ℤ) (k : ℕ) : ℤ := ∑ j ∈ Finset.range k, P.coeff j

lemma Csum_nonneg {k : ℕ} {P : Polynomial ℤ} (hcoef : ∀ n, n ≤ k → 0 ≤ P.coeff n) :
    0 ≤ Csum P k :=
  Finset.sum_nonneg fun j hj => hcoef j (Nat.le_of_lt (Finset.mem_range.1 hj))

/-- Lower bound: `x ^ k ≤ P.eval x` for `x ≥ 1`. -/
lemma eval_lower {k : ℕ} (hk : 2 ≤ k) {P : Polynomial ℤ} (hmon : P.Monic)
    (hdeg : P.degree = k) (hcoef : ∀ n, n ≤ k → 0 ≤ P.coeff n)
    {x : ℤ} (hx : 1 ≤ x) : x ^ k ≤ P.eval x := by
  rw [eval_eq hk hmon hdeg x]
  apply le_add_of_nonneg_right
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (hcoef j (Nat.le_of_lt (Finset.mem_range.1 hj))) (pow_nonneg (by omega) j)

/-- Upper bound: `P.eval x ≤ x ^ k + C·x ^ (k-1)` for `x ≥ 1`. -/
lemma eval_upper {k : ℕ} (hk : 2 ≤ k) {P : Polynomial ℤ} (hmon : P.Monic)
    (hdeg : P.degree = k) (hcoef : ∀ n, n ≤ k → 0 ≤ P.coeff n)
    {x : ℤ} (hx : 1 ≤ x) : P.eval x ≤ x ^ k + Csum P k * x ^ (k - 1) := by
  rw [eval_eq hk hmon hdeg x]
  apply add_le_add_right
  unfold Csum
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  have hj' : j ≤ k - 1 := Nat.le_pred_of_lt (Finset.mem_range.1 hj)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx hj')
    (hcoef j (Nat.le_of_lt (Finset.mem_range.1 hj)))

/-- Chaining one-step inequalities over an interval. -/
lemma chain_le_nat {B : ℕ → ℕ} {a b : ℕ} (h : ∀ j, a ≤ j → j < b → B j ≤ B (j + 1)) :
    ∀ {t}, a + t ≤ b → B a ≤ B (a + t) := by
  intro t ht
  induction t with
  | zero => simp
  | succ t ih =>
      have := h (a + t) (by omega) (by omega)
      exact (ih (by omega)).trans this

/-- The sequence is non-decreasing. Proof: among all descent indices `n`
(with `A (n+1) < A n`), take one with `A (n+1)` minimal; the key recurrence
forces `A (n+k+1) < A (n+1)`, and chaining up to `n+k+1` contradicts minimality. -/
lemma seq_monotone {k : ℕ} (hk : 2 ≤ k) {P : Polynomial ℤ} (hmon : P.Monic)
    (hdeg : P.degree = k) (hcoef : ∀ n, n ≤ k → 0 ≤ P.coeff n)
    {A : ℕ → ℕ} (hA : ∀ m, P.eval (A m : ℤ) = ∏ i ∈ Finset.range k, (A (m + 1 + i) : ℤ))
    (hpos : ∀ m, 0 < A m) : Monotone A := by
  apply monotone_nat_of_le_succ
  by_contra hnot
  push Not at hnot
  set V : Set ℕ := {v | ∃ n, A (n + 1) < A n ∧ A (n + 1) = v} with hV
  have hVne : V.Nonempty := by
    obtain ⟨n, hn⟩ := hnot
    exact ⟨A (n + 1), n, hn, rfl⟩
  obtain ⟨n₀, hn₀, hv₀⟩ := Nat.sInf_mem hVne
  have hmin : ∀ n, A (n + 1) < A n → sInf V ≤ A (n + 1) := fun n hn =>
    Nat.sInf_le ⟨n, hn, rfl⟩
  have hestep : A (n₀ + k + 1) < A (n₀ + 1) := by
    have h1 : P.eval (A (n₀ + 1) : ℤ) < P.eval (A n₀ : ℤ) :=
      eval_strictMono hk hmon hdeg hcoef (by exact_mod_cast hpos (n₀ + 1))
        (by exact_mod_cast hn₀)
    have h2 : (A (n₀ + 1) : ℤ) * P.eval (A (n₀ + 1) : ℤ) <
        (A (n₀ + 1) : ℤ) * P.eval (A n₀ : ℤ) :=
      mul_lt_mul_of_pos_left h1 (by exact_mod_cast hpos (n₀ + 1))
    have h3 := key_recurrence hA n₀
    rw [Nat.add_right_comm] at h3
    rw [← h3] at h2
    have h4 : (A (n₀ + k + 1) : ℤ) < (A (n₀ + 1) : ℤ) :=
      lt_of_mul_lt_mul_right h2 (le_of_lt (eval_pos hk hmon hdeg hcoef
        (by exact_mod_cast hpos n₀)))
    exact_mod_cast h4
  have key : ∀ t, t ≤ k → ∀ j, k - t ≤ j → j ≤ k → A (n₀ + j) ≤ A (n₀ + j + 1) := by
    intro t
    induction t with
    | zero =>
        intro _ j hj1 hj2
        have hj : j = k := by omega
        rw [hj]
        by_contra hlt
        have hlt' : A (n₀ + k + 1) < A (n₀ + k) := Nat.lt_of_not_ge hlt
        have hle := hmin (n₀ + k) hlt'
        rw [← hv₀] at hle
        exact absurd (hestep.trans_le hle) (lt_irrefl _)
    | succ t iht =>
        intro ht j hj1 hj2
        rcases eq_or_lt_of_le hj1 with rfl | hj1'
        · by_contra hlt
          have hlt' : A (n₀ + (k - (t + 1)) + 1) < A (n₀ + (k - (t + 1))) :=
            Nat.lt_of_not_ge hlt
          have hge : A (n₀ + (k - (t + 1)) + 1) ≤ A (n₀ + (k + 1)) := by
            have hstep : ∀ j', (k - (t + 1)) + 1 ≤ j' → j' < k + 1 →
                A (n₀ + j') ≤ A (n₀ + j' + 1) := by
              intro j' hj'1 hj'2
              exact iht (by omega) j' (by omega) (by omega)
            have h : k - (t + 1) + 1 + (t + 1) = k + 1 := by
              rw [Nat.add_right_comm, Nat.sub_add_cancel ht]
            have hc := chain_le_nat hstep (t := t + 1) h.le
            rwa [h] at hc
          have hle := hmin (n₀ + (k - (t + 1))) hlt'
          rw [← hv₀] at hle
          exact absurd ((hge.trans_lt hestep).trans_le hle) (lt_irrefl _)
        · exact iht (by omega) j (by omega) hj2
  have hchain : A (n₀ + 1) ≤ A (n₀ + (k + 1)) := by
    have hstep : ∀ j, 1 ≤ j → j < k + 1 → A (n₀ + j) ≤ A (n₀ + j + 1) := by
      intro j hj1 hj2
      exact key k (le_refl k) j (by omega) (by omega)
    have hc := chain_le_nat hstep (t := k) (by omega)
    rwa [add_comm 1] at hc
  rw [← add_assoc] at hchain
  exact absurd (hchain.trans_lt hestep) (lt_irrefl _)

/-- Bounded consecutive differences: `A (m+1) ≤ A m + C` where `C = (Csum P k).toNat`. -/
lemma diff_le {k : ℕ} (hk : 2 ≤ k) {P : Polynomial ℤ} (hmon : P.Monic)
    (hdeg : P.degree = k) (hcoef : ∀ n, n ≤ k → 0 ≤ P.coeff n)
    {A : ℕ → ℕ} (hA : ∀ m, P.eval (A m : ℤ) = ∏ i ∈ Finset.range k, (A (m + 1 + i) : ℤ))
    (hpos : ∀ m, 0 < A m) (hmono : Monotone A) (m : ℕ) :
    A (m + 1) ≤ A m + (Csum P k).toNat := by
  set CN := (Csum P k).toNat with hCN
  have hC : (CN : ℤ) = Csum P k := Int.toNat_of_nonneg (Csum_nonneg hcoef)
  have h1 : A (m + 1) ^ k ≤ ∏ i ∈ Finset.range k, A (m + 1 + i) := by
    have e : A (m + 1) ^ k = ∏ i ∈ Finset.range k, A (m + 1) := by
      rw [Finset.prod_const, Finset.card_range]
    rw [e]
    apply Finset.prod_le_prod
    · intro i _; exact Nat.zero_le _
    · intro i _
      exact hmono (by omega)
  have h6 : (A m) ^ k + CN * (A m) ^ (k - 1) ≤ (A m + CN) ^ k := by
    have h7 := pow_ge_add_mul (A m) CN (k - 1)
    rw [Nat.sub_add_cancel (by omega)] at h7
    calc (A m) ^ k + CN * (A m) ^ (k - 1)
        ≤ (A m) ^ k + k * (A m) ^ (k - 1) * CN := by
          apply Nat.add_le_add_left
          nlinarith [hk, Nat.zero_le (CN * (A m) ^ (k - 1))]
      _ ≤ (A m + CN) ^ k := h7
  have h8 : (∏ i ∈ Finset.range k, A (m + 1 + i)) ≤ (A m + CN) ^ k := by
    have h9 : ((∏ i ∈ Finset.range k, A (m + 1 + i) : ℕ) : ℤ) ≤
        (((A m + CN) ^ k : ℕ) : ℤ) := by
      have h3 : ((∏ i ∈ Finset.range k, A (m + 1 + i) : ℕ) : ℤ) = P.eval (A m : ℤ) := by
        push_cast
        exact (hA m).symm
      rw [h3]
      calc P.eval (A m : ℤ) ≤ (A m : ℤ) ^ k + Csum P k * (A m : ℤ) ^ (k - 1) :=
            eval_upper hk hmon hdeg hcoef (by exact_mod_cast hpos m)
        _ = (((A m) ^ k + CN * (A m) ^ (k - 1) : ℕ) : ℤ) := by
            rw [← hC]; push_cast; ring
        _ ≤ (((A m + CN) ^ k : ℕ) : ℤ) := by exact_mod_cast h6
    exact_mod_cast h9
  exact le_of_pow_le (by omega : 0 < k) (h1.trans h8)

/-- The shifts `A (m+i) - A m` lie in `[0, i·C]`. -/
lemma shift_bounds {k : ℕ} (hk : 2 ≤ k) {P : Polynomial ℤ} (hmon : P.Monic)
    (hdeg : P.degree = k) (hcoef : ∀ n, n ≤ k → 0 ≤ P.coeff n)
    {A : ℕ → ℕ} (hA : ∀ m, P.eval (A m : ℤ) = ∏ i ∈ Finset.range k, (A (m + 1 + i) : ℤ))
    (hpos : ∀ m, 0 < A m) (hmono : Monotone A) (m i : ℕ) :
    0 ≤ (A (m + i) : ℤ) - A m ∧ (A (m + i) : ℤ) - A m ≤ i * Csum P k := by
  set CN := (Csum P k).toNat with hCN
  have hC : (CN : ℤ) = Csum P k := Int.toNat_of_nonneg (Csum_nonneg hcoef)
  have hub : A (m + i) ≤ A m + i * CN := by
    induction i with
    | zero => simp
    | succ i ih =>
        calc A (m + (i + 1)) = A ((m + i) + 1) := by ring_nf
          _ ≤ A (m + i) + CN := diff_le hk hmon hdeg hcoef hA hpos hmono (m + i)
          _ ≤ (A m + i * CN) + CN := Nat.add_le_add_right ih CN
          _ = A m + (i + 1) * CN := by ring
  constructor
  · have h := hmono (show m ≤ m + i by omega)
    have h' : (A m : ℤ) ≤ (A (m + i) : ℤ) := by exact_mod_cast h
    linarith
  · have h : (A (m + i) : ℤ) ≤ (A m + i * CN : ℕ) := by exact_mod_cast hub
    push_cast at h
    rw [hC] at h
    linarith

/-- A product of linear factors is monic. -/
lemma monic_prod_linear {σ : ℕ → ℤ} (s : Finset ℕ) :
    (∏ i ∈ s, (X + C (σ i))).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_add_C _

lemma natDegree_prod_linear {σ : ℕ → ℤ} (s : Finset ℕ) :
    (∏ i ∈ s, (X + C (σ i))).natDegree = s.card := by
  rw [natDegree_prod_of_monic _ _ (fun _ _ => monic_X_add_C _)]
  simp only [natDegree_X_add_C, Finset.sum_const, smul_eq_mul, mul_one]

lemma degree_prod_linear {σ : ℕ → ℤ} (s : Finset ℕ) :
    (∏ i ∈ s, (X + C (σ i))).degree = (s.card : WithBot ℕ) := by
  rw [degree_eq_natDegree (monic_prod_linear (σ := σ) s).ne_zero, natDegree_prod_linear]

/-- Coefficients of a product of linear factors `X + C σᵢ` are bounded by
`(1 + S) ^ (number of factors)` when every `|σᵢ| ≤ S`. -/
lemma coeff_prod_linear_bound {S : ℤ} (hS : 0 ≤ S) (σ : ℕ → ℤ) :
    ∀ (s : Finset ℕ), (∀ i ∈ s, |σ i| ≤ S) →
      ∀ j : ℕ, |(∏ i ∈ s, (X + C (σ i))).coeff j| ≤ (1 + S) ^ s.card := by
  intro s hσ
  induction s using Finset.induction with
  | empty =>
      intro j
      rw [Finset.prod_empty, Finset.card_empty, pow_zero, coeff_one]
      split_ifs <;> simp
  | insert i s hi ih =>
      intro j
      have hSi : |σ i| ≤ S := hσ i (Finset.mem_insert_self i s)
      have ih' : ∀ j, |(∏ i ∈ s, (X + C (σ i))).coeff j| ≤ (1 + S) ^ s.card :=
        ih (fun i' hi' => hσ i' (Finset.mem_insert_of_mem hi'))
      rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
      ring_nf
      rw [coeff_add, coeff_C_mul]
      rcases eq_or_ne j 0 with rfl | hj0
      · rw [coeff_X_mul_zero]
        simp only [zero_add, abs_mul]
        calc
          _ ≤ S * (1 + S) ^ s.card := mul_le_mul hSi (ih' 0) (abs_nonneg _) hS
          _ ≤ S * (1 + S) ^ s.card + (1 + S) ^ s.card := le_add_of_nonneg_right (pow_nonneg (by linarith) _)
      · obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
        rw [coeff_X_mul]
        calc
          -- make terms implicit to make calc faster
          _ ≤ _ := abs_add_le _ _
          _ ≤ S * (1 + S) ^ s.card + (1 + S) ^ s.card := by
              rw [add_comm, abs_mul]
              apply add_le_add ?_ (ih' j')
              exact mul_le_mul hSi (ih' (j' + 1)) (abs_nonneg _) hS

/-- `Fpoly P A k m := ∏_{i=1}^{k} (X + C (A (m+i) - A m)) - P`; it vanishes at `A m`. -/
noncomputable def Fpoly (P : Polynomial ℤ) (A : ℕ → ℕ) (k m : ℕ) : Polynomial ℤ :=
  ∏ i ∈ Finset.range k, (X + C ((A (m + 1 + i) : ℤ) - A m)) - P

lemma Fpoly_eval {k : ℕ} {P : Polynomial ℤ} {A : ℕ → ℕ}
    (hA : ∀ m, P.eval (A m : ℤ) = ∏ i ∈ Finset.range k, (A (m + 1 + i) : ℤ))
    (m : ℕ) : (Fpoly P A k m).eval (A m : ℤ) = 0 := by
  rw [Fpoly, eval_sub, eval_prod]
  have h : ∏ i ∈ Finset.range k, (X + C ((A (m + 1 + i) : ℤ) - A m)).eval (A m : ℤ) =
      ∏ i ∈ Finset.range k, (A (m + 1 + i) : ℤ) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [eval_add, eval_X, eval_C]
    ring
  rw [h, hA m, sub_self]

lemma Fpoly_degree_lt {k : ℕ} (_hk : 2 ≤ k) {P : Polynomial ℤ} (hmon : P.Monic)
    (hdeg : P.degree = k) (A : ℕ → ℕ) (m : ℕ) :
    (Fpoly P A k m).degree < k := by
  have h1 : (∏ i ∈ Finset.range k, (X + C ((A (m + 1 + i) : ℤ) - A m))).degree =
      P.degree := by
    rw [degree_prod_linear, hdeg, Finset.card_range]
  have h2 : (∏ i ∈ Finset.range k, (X + C ((A (m + 1 + i) : ℤ) - A m))) ≠ 0 :=
    (monic_prod_linear _).ne_zero
  have h3 : (∏ i ∈ Finset.range k, (X + C ((A (m + 1 + i) : ℤ) - A m))).leadingCoeff =
      P.leadingCoeff := by
    rw [(monic_prod_linear _).leadingCoeff, hmon.leadingCoeff]
  have h4 := degree_sub_lt_left h1 h2 h3
  rw [degree_prod_linear, Finset.card_range] at h4
  exact h4

lemma Fpoly_coeff_bound {k : ℕ} (hk : 2 ≤ k) {P : Polynomial ℤ} (hmon : P.Monic)
    (hdeg : P.degree = k) (hcoef : ∀ n, n ≤ k → 0 ≤ P.coeff n)
    {A : ℕ → ℕ} (hA : ∀ m, P.eval (A m : ℤ) = ∏ i ∈ Finset.range k, (A (m + 1 + i) : ℤ))
    (hpos : ∀ m, 0 < A m) (hmono : Monotone A) (m j : ℕ) :
    |(Fpoly P A k m).coeff j| ≤ (1 + k * Csum P k) ^ k + Csum P k := by
  have hC0 := Csum_nonneg hcoef
  by_cases hj : j < k
  · have hcb : |(∏ i ∈ Finset.range k, (X + C ((A (m + 1 + i) : ℤ) - A m))).coeff j| ≤
        (1 + k * Csum P k) ^ (Finset.range k).card := by
      apply coeff_prod_linear_bound (by positivity) _ (Finset.range k) _ j
      intro i hi
      have hb := shift_bounds hk hmon hdeg hcoef hA hpos hmono m (1 + i)
      rw [← add_assoc] at hb
      rw [abs_of_nonneg hb.1]
      calc (A (m + 1 + i) : ℤ) - A m ≤ (1 + i) * Csum P k := hb.2
        _ ≤ k * Csum P k := by
            have hi' : i < k := Finset.mem_range.1 hi
            exact mul_le_mul_of_nonneg_right (by omega) hC0
    rw [Finset.card_range] at hcb
    rw [Fpoly, coeff_sub]
    calc |(∏ i ∈ Finset.range k, (X + C ((A (m + 1 + i) : ℤ) - A m))).coeff j - P.coeff j|
        = |(∏ i ∈ Finset.range k, (X + C ((A (m + 1 + i) : ℤ) - A m))).coeff j + (-(P.coeff j))| := by
          rw [sub_eq_add_neg]
      _ ≤ |(∏ i ∈ Finset.range k, (X + C ((A (m + 1 + i) : ℤ) - A m))).coeff j| +
          |(-(P.coeff j))| := abs_add_le _ _
      _ = |(∏ i ∈ Finset.range k, (X + C ((A (m + 1 + i) : ℤ) - A m))).coeff j| +
          |P.coeff j| := by rw [abs_neg]
      _ ≤ (1 + k * Csum P k) ^ k + Csum P k := by
          apply add_le_add hcb _
          rw [abs_of_nonneg (hcoef j (by omega))]
          exact Finset.single_le_sum
            (fun i hi => hcoef i (Nat.le_of_lt (Finset.mem_range.1 hi)))
            (Finset.mem_range.2 hj)
  · have h0 : (Fpoly P A k m).coeff j = 0 := by
      apply coeff_eq_zero_of_degree_lt
      exact lt_of_lt_of_le (Fpoly_degree_lt hk hmon hdeg A m) (by exact_mod_cast le_of_not_gt hj)
    rw [h0, abs_zero]
    positivity

/-- An integer root `x ≥ 1` of a nonzero integer polynomial is bounded by
`natDegree × (coefficient bound)`. -/
lemma root_bound {F : Polynomial ℤ} {B : ℤ} (hF : F ≠ 0) (hB : ∀ j, |F.coeff j| ≤ B)
    {x : ℤ} (hx : 1 ≤ x) (hFx : F.eval x = 0) : x ≤ F.natDegree * B := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  by_cases hn : F.natDegree = 0
  · have h1 : F.eval x = ∑ i ∈ Finset.range (F.natDegree + 1), F.coeff i * x ^ i :=
      eval_eq_sum_range x
    rw [hFx, hn, Finset.sum_range_one] at h1
    simp at h1
    have hne : F.coeff 0 ≠ 0 := by
      have h2 : F.coeff F.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hF
      rwa [hn] at h2
    exact absurd h1.symm hne
  · have hn' : 0 < F.natDegree := Nat.pos_of_ne_zero hn
    have h1 : F.eval x = ∑ i ∈ Finset.range (F.natDegree + 1), F.coeff i * x ^ i :=
      eval_eq_sum_range x
    rw [hFx, Finset.sum_range_succ] at h1
    have h2 : F.coeff F.natDegree * x ^ F.natDegree =
        - ∑ i ∈ Finset.range F.natDegree, F.coeff i * x ^ i := by linarith
    have habs : |F.coeff F.natDegree * x ^ F.natDegree| ≤
        B * F.natDegree * x ^ (F.natDegree - 1) := by
      rw [h2]
      calc |(- ∑ i ∈ Finset.range F.natDegree, F.coeff i * x ^ i)|
          = |∑ i ∈ Finset.range F.natDegree, F.coeff i * x ^ i| := abs_neg _
        _ ≤ ∑ i ∈ Finset.range F.natDegree, |F.coeff i * x ^ i| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ i ∈ Finset.range F.natDegree, |F.coeff i| * x ^ i := by
            apply Finset.sum_congr rfl
            intro i _
            rw [abs_mul, abs_pow, abs_of_nonneg (by omega : 0 ≤ x)]
        _ ≤ ∑ i ∈ Finset.range F.natDegree, B * x ^ (F.natDegree - 1) := by
            apply Finset.sum_le_sum
            intro i hi
            have hi' : i ≤ F.natDegree - 1 := Nat.le_pred_of_lt (Finset.mem_range.1 hi)
            calc |F.coeff i| * x ^ i ≤ B * x ^ i :=
                  mul_le_mul_of_nonneg_right (hB i) (pow_nonneg (by omega) i)
              _ ≤ B * x ^ (F.natDegree - 1) :=
                  mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx hi') hB0
        _ = B * F.natDegree * x ^ (F.natDegree - 1) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            ring
    have h4 : |F.coeff F.natDegree| * x ^ F.natDegree ≤
        B * F.natDegree * x ^ (F.natDegree - 1) := by
      have e : |F.coeff F.natDegree * x ^ F.natDegree| =
          |F.coeff F.natDegree| * x ^ F.natDegree := by
        rw [abs_mul, abs_pow, abs_of_nonneg (by omega : 0 ≤ x)]
      rw [← e]
      exact habs
    have hbn : 1 ≤ |F.coeff F.natDegree| := by
      have hne : F.coeff F.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hF
      have hpos : 0 < |F.coeff F.natDegree| := abs_pos.2 hne
      omega
    have h5 : x ^ F.natDegree ≤ B * F.natDegree * x ^ (F.natDegree - 1) := by
      calc x ^ F.natDegree = 1 * x ^ F.natDegree := by ring
        _ ≤ |F.coeff F.natDegree| * x ^ F.natDegree :=
            mul_le_mul_of_nonneg_right hbn (pow_nonneg (by omega) _)
        _ ≤ B * F.natDegree * x ^ (F.natDegree - 1) := h4
    have h6 : x ^ F.natDegree = x * x ^ (F.natDegree - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel (by omega)]
    rw [h6] at h5
    have h7 : x ≤ B * F.natDegree :=
      le_of_mul_le_mul_right h5 (pow_pos (by omega : 0 < x) _)
    rw [mul_comm]
    exact h7

/-- Once `A m` exceeds the root bound, `F_m` vanishes, and comparing the
`X ^ (k-1)`-coefficients yields the key relation
`Σ_{i<k} A (m+1+i) = k·A m + c_{k-1}`. -/
lemma eval_sum_eq {k : ℕ} (hk : 2 ≤ k) {P : Polynomial ℤ} (hmon : P.Monic)
    (hdeg : P.degree = k) (hcoef : ∀ n, n ≤ k → 0 ≤ P.coeff n)
    {A : ℕ → ℕ} (hA : ∀ m, P.eval (A m : ℤ) = ∏ i ∈ Finset.range k, (A (m + 1 + i) : ℤ))
    (hpos : ∀ m, 0 < A m) (hmono : Monotone A)
    {N₀ : ℕ} (hN₀ : ∀ m, m ≥ N₀ → (k * ((1 + k * Csum P k) ^ k + Csum P k) : ℤ) < A m)
    (m : ℕ) (hm : m ≥ N₀) :
    ∑ i ∈ Finset.range k, (A (m + 1 + i) : ℤ) = k * (A m : ℤ) + P.coeff (k - 1) := by
  have hF0 : Fpoly P A k m = 0 := by
    by_contra hF
    have hroot := root_bound hF (Fpoly_coeff_bound hk hmon hdeg hcoef hA hpos hmono m)
      (by exact_mod_cast hpos m) (Fpoly_eval hA m)
    have hdt : (Fpoly P A k m).natDegree < k := by
      rw [Polynomial.natDegree_lt_iff_degree_lt hF]
      exact Fpoly_degree_lt hk hmon hdeg A m
    have hB0 : 0 ≤ (1 + k * Csum P k) ^ k + Csum P k := by
      have hC0 := Csum_nonneg hcoef
      positivity
    have hBpos : 0 < (1 + k * Csum P k) ^ k + Csum P k := by
      have hC0 := Csum_nonneg hcoef
      positivity
    have hle1 : ((Fpoly P A k m).natDegree : ℤ) * ((1 + k * Csum P k) ^ k + Csum P k) ≤
        ((k : ℤ) - 1) * ((1 + k * Csum P k) ^ k + Csum P k) := by
      apply mul_le_mul_of_nonneg_right _ hB0
      have hle : ((Fpoly P A k m).natDegree : ℤ) + 1 ≤ (k : ℤ) := by exact_mod_cast hdt
      linarith
    have hlt2 : ((k : ℤ) - 1) * ((1 + k * Csum P k) ^ k + Csum P k) <
        k * ((1 + k * Csum P k) ^ k + Csum P k) :=
      mul_lt_mul_of_pos_right (by omega) hBpos
    have := hN₀ m hm
    linarith [hroot]
  have hprod : (∏ i ∈ Finset.range k, (X + C ((A (m + 1 + i) : ℤ) - A m))) = P :=
    sub_eq_zero.1 hF0
  have hcoeff : P.coeff (k - 1) = ∑ i ∈ Finset.range k, ((A (m + 1 + i) : ℤ) - A m) := by
    conv_lhs => rw [← hprod]
    rw [Finset.prod_X_add_C_coeff (Finset.range k) _ (by rw [Finset.card_range]; exact Nat.sub_le _ _)]
    rw [Finset.card_range, Nat.sub_sub_self (by omega), Finset.powersetCard_one,
      Finset.sum_map]
    exact Finset.sum_congr rfl fun i _ => by simp
  have hsum : ∑ i ∈ Finset.range k, ((A (m + 1 + i) : ℤ) - A m) =
      (∑ i ∈ Finset.range k, (A (m + 1 + i) : ℤ)) - k * (A m : ℤ) := by
    rw [Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  linarith [hcoeff, hsum]

/-- The consecutive difference `Dif A j = A (j+1) - A j` as an integer. -/
def Dif (A : ℕ → ℕ) (j : ℕ) : ℤ := (A (j + 1) : ℤ) - A j

/-- Once `A m` exceeds the root bound, the difference `Dif A j` is eventually
constant: the sum relation `Σ_{l<k} Dif A (j+1+l) = k · Dif A j` forces the
maximal difference to propagate. -/
lemma diff_eventually_const {k : ℕ} (hk : 2 ≤ k) {P : Polynomial ℤ} (hmon : P.Monic)
    (hdeg : P.degree = k) (hcoef : ∀ n, n ≤ k → 0 ≤ P.coeff n)
    {A : ℕ → ℕ} (hA : ∀ m, P.eval (A m : ℤ) = ∏ i ∈ Finset.range k, (A (m + 1 + i) : ℤ))
    (hpos : ∀ m, 0 < A m) (hmono : Monotone A)
    {N₀ : ℕ} (hN₀ : ∀ m, m ≥ N₀ → (k * ((1 + k * Csum P k) ^ k + Csum P k) : ℤ) < A m) :
    ∃ m c, (∀ j ≥ m, Dif A j = c) := by
  have hE : ∀ m ≥ N₀, ∑ i ∈ Finset.range k, (A (m + 1 + i) : ℤ) =
      k * (A m : ℤ) + P.coeff (k - 1) :=
    fun m hm => eval_sum_eq hk hmon hdeg hcoef hA hpos hmono hN₀ m hm
  have hd0 : ∀ j, 0 ≤ Dif A j := by
    intro j
    have h := hmono (show j ≤ j + 1 by omega)
    have h' : (A j : ℤ) ≤ (A (j + 1) : ℤ) := by exact_mod_cast h
    rw [Dif]
    linarith
  have hdC : ∀ j, Dif A j ≤ Csum P k := by
    intro j
    have hdl := diff_le hk hmon hdeg hcoef hA hpos hmono j
    have hC : ((Csum P k).toNat : ℤ) = Csum P k := Int.toNat_of_nonneg (Csum_nonneg hcoef)
    have h : (A (j + 1) : ℤ) ≤ (A j + (Csum P k).toNat : ℕ) := by exact_mod_cast hdl
    push_cast at h
    rw [hC] at h
    rw [Dif]
    linarith
  have hsumD : ∀ j ≥ N₀, ∑ l ∈ Finset.range k, Dif A (j + 1 + l) = k * Dif A j := by
    intro j hj
    have e1 := hE j hj
    have e2 := hE (j + 1) (by omega)
    simp only [Nat.add_right_comm (j+1), Nat.add_assoc (j+1)] at e2
    simp only [Dif, add_assoc (j+1), Finset.sum_sub_distrib]
    linarith only [e1, e2]
  -- the set of difference magnitudes and its maximum
  set S : Set ℕ := {v | ∃ j ≥ N₀, v = (Dif A j).toNat} with hS
  have hSne : S.Nonempty := ⟨_, N₀, le_refl _, rfl⟩
  have hSbd : BddAbove S := by
    refine ⟨(Csum P k).toNat, ?_⟩
    rintro v ⟨j, hj, rfl⟩
    have h3 : ((Dif A j).toNat : ℤ) ≤ ((Csum P k).toNat : ℤ) := by
      rw [Int.toNat_of_nonneg (hd0 j), Int.toNat_of_nonneg (Csum_nonneg hcoef)]
      exact hdC j
    exact_mod_cast h3
  set M : ℕ := sSup S with hM
  obtain ⟨m, hm, hMm⟩ := Nat.sSup_mem hSne hSbd
  rw [← hM] at hMm
  have hdM : ∀ j ≥ N₀, Dif A j ≤ (M : ℤ) := by
    intro j hj
    have h4 : (Dif A j).toNat ≤ M := le_csSup hSbd ⟨j, hj, rfl⟩
    have h5 : ((Dif A j).toNat : ℤ) ≤ (M : ℤ) := by exact_mod_cast h4
    rwa [Int.toNat_of_nonneg (hd0 j)] at h5
  have hdm : Dif A m = (M : ℤ) := by
    rw [hMm, Int.toNat_of_nonneg (hd0 m)]
  have hkey : ∀ j ≥ N₀, Dif A j = (M : ℤ) → ∀ l ∈ Finset.range k, Dif A (j + 1 + l) = (M : ℤ) := by
    intro j hj hdj l hl
    have hsum := hsumD j hj
    rw [hdj] at hsum
    by_contra hlt
    have hlt' : Dif A (j + 1 + l) < (M : ℤ) :=
      lt_of_le_of_ne (hdM (j + 1 + l) (by omega)) hlt
    have hsumlt : ∑ l' ∈ Finset.range k, Dif A (j + 1 + l') < ∑ l' ∈ Finset.range k, (M : ℤ) := by
      apply Finset.sum_lt_sum
      · intro l' hl'
        exact hdM (j + 1 + l') (by omega)
      · exact ⟨l, hl, hlt'⟩
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsumlt
    linarith [hsum]
  have hconst : ∀ t, Dif A (m + t) = (M : ℤ) := by
    intro t
    induction t with
    | zero => exact hdm
    | succ t iht =>
        exact hkey (m + t) (by omega) iht 0 (Finset.mem_range.2 (by omega))
  exact ⟨m, M, fun j hj => by
    rw [← Nat.add_sub_of_le hj]
    exact hconst (j - m)⟩

lemma apPoly_coeff_nonneg_aux (d : ℕ) (s : Finset ℕ) (n : ℕ) :
    0 ≤ (∏ i ∈ s, (X + C ((i + 1) * d : ℤ))).coeff n := by
  induction s using Finset.induction generalizing n with
  | empty => rw [Finset.prod_empty, coeff_one]; split_ifs <;> norm_num
  | insert i s hi ih =>
      rw [Finset.prod_insert hi, coeff_mul]
      apply Finset.sum_nonneg
      rintro ⟨j, l⟩ -
      exact mul_nonneg (coeff_X_add_C_nonneg (Int.natCast_nonneg _) j) (ih l)

lemma apPoly_coeff_nonneg (k d : ℕ) (n : ℕ) : 0 ≤ (apPoly k d).coeff n :=
  apPoly_coeff_nonneg_aux d _ n

lemma apPoly_eval (k d : ℕ) (x : ℤ) :
    (apPoly k d).eval x = ∏ i ∈ Finset.range k, (x + ((i + 1) * d : ℤ)) := by
  rw [apPoly, eval_prod]
  exact Finset.prod_congr rfl fun i _ => by rw [eval_add, eval_X, eval_C]

/-- The bounded case: a bounded monotone sequence of naturals stabilizes, and
the functional equation forces it to be constant. -/
lemma backward_bounded {k : ℕ} (hk : 2 ≤ k) {P : Polynomial ℤ} (hmon : P.Monic)
    (hdeg : P.degree = k) (hcoef : ∀ n, n ≤ k → 0 ≤ P.coeff n)
    {A : ℕ → ℕ} (hA : ∀ m, P.eval (A m : ℤ) = ∏ i ∈ Finset.range k, (A (m + 1 + i) : ℤ))
    (hpos : ∀ m, 0 < A m) (hmono : Monotone A)
    {B : ℕ} (hB : ∀ m, A m ≤ B) :
    ∃ a₀ d : ℕ, ∀ m, A m = a₀ + d * m := by
  obtain ⟨V, N, hN⟩ := converges_of_monotone_of_bounded hmono hB
  have hV1 : 1 ≤ V := by
    have h := hpos N
    rw [hN N (le_refl N)] at h
    exact h
  have hPV : P.eval (V : ℤ) = (V : ℤ) ^ k := by
    have h1 := hA N
    rw [hN N (le_refl N)] at h1
    have h2 : ∏ i ∈ Finset.range k, (A (N + 1 + i) : ℤ) = (V : ℤ) ^ k := by
      rw [show (∏ i ∈ Finset.range k, (A (N + 1 + i) : ℤ)) = ∏ i ∈ Finset.range k, (V : ℤ) from
        Finset.prod_congr rfl fun i _ => by rw [hN (N + 1 + i) (by omega)]]
      rw [Finset.prod_const, Finset.card_range]
    rw [h2] at h1
    exact h1
  have hcoef0 : ∀ j < k, P.coeff j = 0 := by
    have h3 : P.eval (V : ℤ) = (V : ℤ) ^ k + ∑ j ∈ Finset.range k, P.coeff j * (V : ℤ) ^ j :=
      eval_eq hk hmon hdeg V
    rw [hPV] at h3
    have h4 : ∑ j ∈ Finset.range k, P.coeff j * (V : ℤ) ^ j = 0 := by linarith [h3]
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun j hj => by
      exact mul_nonneg (hcoef j (Nat.le_of_lt (Finset.mem_range.1 hj)))
        (pow_nonneg (by exact_mod_cast (by omega : (0 : ℤ) ≤ V)) j))] at h4
    intro j hj
    have h5 := h4 j (Finset.mem_range.2 hj)
    have h6 : (0 : ℤ) < (V : ℤ) := by exact_mod_cast hV1
    have hVpos : (V : ℤ) ^ j ≠ 0 := pow_ne_zero j (by omega)
    exact (mul_eq_zero.1 h5).resolve_right hVpos
  have hP_eq : P = X ^ k := by
    have hnd : P.natDegree = k := natDegree_eq_of_degree_eq_some hdeg
    apply Polynomial.ext
    intro n
    by_cases hn : n < k
    · rw [hcoef0 n hn, coeff_X_pow, ite_eq_right (by omega)]
    · by_cases hn' : k < n
      · rw [show P.coeff n = 0 from coeff_eq_zero_of_natDegree_lt (by omega), coeff_X_pow,
          ite_eq_right (by omega)]
      · have h : n = k := by omega
        rw [h, coeff_X_pow, ite_eq_left rfl, ← hnd]
        exact hmon.leadingCoeff
  -- downward induction: every value is `V`
  have hdown : ∀ j, j ≤ N → A (N - j) = V := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      by_cases hj0 : j = 0
      · subst hj0
        simpa using hN N (le_refl N)
      · set m' := N - j with hm'
        have hm'1 : m' + 1 = N - (j - 1) := by omega
        have hjm1 := ih (j - 1) (by omega) (by omega)
        rw [← hm'1] at hjm1
        have hval : ∀ i ∈ Finset.range k, A (m' + 1 + i) = V := by
          intro i hi
          have hi' : i < k := Finset.mem_range.1 hi
          by_cases hcase : N ≤ m' + 1 + i
          · exact hN (m' + 1 + i) hcase
          · push Not at hcase
            have hji : m' + 1 + i = N - (j - 1 - i) := by omega
            have hih := ih (j - 1 - i) (by omega) (by omega)
            rw [hji, hih]
        have h1 := hA m'
        have h2 : ∏ i ∈ Finset.range k, (A (m' + 1 + i) : ℤ) = (V : ℤ) ^ k := by
          rw [show (∏ i ∈ Finset.range k, (A (m' + 1 + i) : ℤ)) = ∏ i ∈ Finset.range k, (V : ℤ) from
            Finset.prod_congr rfl fun i hi => by rw [hval i hi]]
          rw [Finset.prod_const, Finset.card_range]
        rw [h2, hP_eq, eval_pow, eval_X] at h1
        have h4 : (A m') ^ k = V ^ k := by exact_mod_cast h1
        exact le_antisymm (le_of_pow_le (by omega : 0 < k) (le_of_eq h4))
          (le_of_pow_le (by omega : 0 < k) (le_of_eq h4.symm))
  -- conclusion
  have hfin : ∀ n, A n = V := by
    intro n
    by_cases! hn : n ≤ N
    · have h := hdown (N - n) (by omega)
      rwa [Nat.sub_sub_self hn] at h
    · exact hN n (by omega)
  exact ⟨V, 0, fun n => by rw [hfin n]; simp⟩

/-- The unbounded case: once the sequence exceeds the root bound, it is an
arithmetic progression. -/
lemma backward_unbounded {k : ℕ} (hk : 2 ≤ k) {P : Polynomial ℤ} (hmon : P.Monic)
    (hdeg : P.degree = k) (hcoef : ∀ n, n ≤ k → 0 ≤ P.coeff n)
    {A : ℕ → ℕ} (hA : ∀ m, P.eval (A m : ℤ) = ∏ i ∈ Finset.range k, (A (m + 1 + i) : ℤ))
    (hpos : ∀ m, 0 < A m) (hmono : Monotone A)
    {N₀ : ℕ} (hN₀ : ∀ m, m ≥ N₀ → (k * ((1 + k * Csum P k) ^ k + Csum P k) : ℤ) < A m) :
    ∃ a₀ d : ℕ, ∀ m, A m = a₀ + d * m := by
  obtain ⟨m, c, hconst⟩ := diff_eventually_const hk hmon hdeg hcoef hA hpos hmono hN₀
  set m₂ := max m N₀ with hm₂
  have hconst2 : ∀ j ≥ m₂, Dif A j = c := fun j hj => hconst j (by omega)
  have hc0 : 0 ≤ c := by
    have h := hconst2 m₂ (le_refl m₂)
    have h0 : (0 : ℤ) ≤ Dif A m₂ := by
      have hm := hmono (show m₂ ≤ m₂ + 1 by omega)
      have h' : (A m₂ : ℤ) ≤ (A (m₂ + 1) : ℤ) := by exact_mod_cast hm
      rw [Dif]
      linarith
    rw [← h]
    exact h0
  set dN := c.toNat with hdN
  have hdNc : (dN : ℤ) = c := Int.toNat_of_nonneg hc0
  have htail : ∀ t, (A (m₂ + t) : ℤ) = A m₂ + t * c := by
    intro t
    induction t with
    | zero => simp
    | succ t iht =>
        have h : Dif A (m₂ + t) = c := hconst2 (m₂ + t) (by omega)
        rw [Dif] at h
        have e : (A (m₂ + (t + 1)) : ℤ) = (A (m₂ + t) : ℤ) + c := by
          rw [← add_assoc]
          linarith [h]
        rw [e, iht]
        push_cast
        ring
  -- the polynomial is `apPoly k dN`
  have hP_eq : P = apPoly k dN := by
    have hF0 : Fpoly P A k m₂ = 0 := by
      by_contra hF
      have hroot := root_bound hF (Fpoly_coeff_bound hk hmon hdeg hcoef hA hpos hmono m₂)
        (by exact_mod_cast hpos m₂) (Fpoly_eval hA m₂)
      have hdt : (Fpoly P A k m₂).natDegree < k := by
        rw [Polynomial.natDegree_lt_iff_degree_lt hF]
        exact Fpoly_degree_lt hk hmon hdeg A m₂
      have hB0 : 0 ≤ (1 + k * Csum P k) ^ k + Csum P k := by
        have hC0 := Csum_nonneg hcoef
        positivity
      have hBpos : 0 < (1 + k * Csum P k) ^ k + Csum P k := by
        have hC0 := Csum_nonneg hcoef
        positivity
      have hle1 : ((Fpoly P A k m₂).natDegree : ℤ) * ((1 + k * Csum P k) ^ k + Csum P k) ≤
          ((k : ℤ) - 1) * ((1 + k * Csum P k) ^ k + Csum P k) := by
        apply mul_le_mul_of_nonneg_right _ hB0
        have hle : ((Fpoly P A k m₂).natDegree : ℤ) + 1 ≤ (k : ℤ) := by exact_mod_cast hdt
        linarith
      have hlt2 : ((k : ℤ) - 1) * ((1 + k * Csum P k) ^ k + Csum P k) <
          k * ((1 + k * Csum P k) ^ k + Csum P k) :=
        mul_lt_mul_of_pos_right (by omega) hBpos
      have hm2N : m₂ ≥ N₀ := le_max_right _ _
      have := hN₀ m₂ hm2N
      linarith [hroot]
    have hprod : (∏ i ∈ Finset.range k, (X + C ((A (m₂ + 1 + i) : ℤ) - A m₂))) = P :=
      sub_eq_zero.1 hF0
    have hσ : ∀ i ∈ Finset.range k, ((A (m₂ + 1 + i) : ℤ) - A m₂) = ((i + 1) * dN : ℤ) := by
      intro i hi
      have ht := htail (1 + i)
      rw [← add_assoc, ← hdNc] at ht
      push_cast at ht
      linarith [ht]
    rw [apPoly, ← hprod]
    exact Finset.prod_congr rfl fun i hi => by rw [hσ i hi]
  -- backward induction: `A (m₂ - j) = A m₂ - j·c` for `j ≤ m₂`
  have hback : ∀ j, j ≤ m₂ → (A (m₂ - j) : ℤ) = A m₂ - (j : ℤ) * c := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      by_cases hj0 : j = 0
      · subst hj0; simp
      · set m' := m₂ - j with hm'
        have hm'1 : m' + 1 = m₂ - (j - 1) := by omega
        have hcast1 : ((j - 1 : ℕ) : ℤ) = (j : ℤ) - 1 := Nat.cast_sub (by omega)
        have hjm1 := ih (j - 1) (by omega) (by omega)
        rw [← hm'1] at hjm1
        have hval : ∀ i ∈ Finset.range k, (A (m' + 1 + i) : ℤ) = (A (m' + 1) : ℤ) + (i : ℤ) * c := by
          intro i hi
          have hi' : i < k := Finset.mem_range.1 hi
          by_cases hcase : m₂ ≤ m' + 1 + i
          · have ht := htail (m' + 1 + i - m₂)
            rw [Nat.add_sub_of_le hcase] at ht
            have hcast2 : ((m' + 1 + i - m₂ : ℕ) : ℤ) = (m' : ℤ) + 1 + (i : ℤ) - (m₂ : ℤ) := by
              omega
            have hm'' : (m' : ℤ) = (m₂ : ℤ) - (j : ℤ) := by omega
            rw [hcast2] at ht
            rw [hm''] at ht
            rw [hjm1, hcast1]
            linarith [ht]
          · push Not at hcase
            have hji : m' + 1 + i = m₂ - (j - 1 - i) := by omega
            have hih := ih (j - 1 - i) (by omega) (by omega)
            have hcast : ((j - 1 - i : ℕ) : ℤ) = (j : ℤ) - 1 - (i : ℤ) := by omega
            rw [hji, hih, hjm1, hcast, hcast1]
            linarith
        -- the product comparison forcing `Dif A m' = c`
        have hstep : (A m' : ℤ) = (A (m' + 1) : ℤ) - c := by
          have hprod_eq : ∏ i ∈ Finset.range k, (A (m' + 1 + i) : ℤ) =
              ∏ i ∈ Finset.range k, ((A m' : ℤ) + ((A (m' + 1) : ℤ) - A m') + (i : ℤ) * c) := by
            apply Finset.prod_congr rfl
            intro i hi
            rw [hval i hi]
            ring
          have h1 := hA m'
          rw [hprod_eq] at h1
          have h2 : P.eval (A m' : ℤ) = ∏ i ∈ Finset.range k, ((A m' : ℤ) + (i + 1) * c) := by
            rw [hP_eq, apPoly_eval]
            apply Finset.prod_congr rfl
            intro i _
            rw [hdNc]
          rw [h2] at h1
          set t := (A (m' + 1) : ℤ) - A m' with ht
          have ht0 : 0 ≤ t := by
            have hm'' := hmono (show m' ≤ m' + 1 by omega)
            have h'' : (A m' : ℤ) ≤ (A (m' + 1) : ℤ) := by exact_mod_cast hm''
            rw [ht]
            linarith
          have hpos' : (0 : ℤ) < (A m' : ℤ) := by exact_mod_cast hpos m'
          rcases lt_trichotomy t c with htc | htc | htc
          · have hlt : ∏ i ∈ Finset.range k, ((A m' : ℤ) + t + (i : ℤ) * c) <
                ∏ i ∈ Finset.range k, ((A m' : ℤ) + (i + 1) * c) := by
              apply Finset.prod_lt_prod_of_nonempty
              · intro i _
                have hi0 : (0 : ℤ) ≤ (i : ℤ) * c := mul_nonneg (Int.natCast_nonneg _) hc0
                linarith [ht0, hpos']
              · intro i hi
                linarith [htc]
              · exact Finset.nonempty_range_iff.2 (by omega)
            rw [ht] at hlt
            linarith [h1, hlt]
          · rw [ht] at htc
            linarith [htc]
          · have hgt : ∏ i ∈ Finset.range k, ((A m' : ℤ) + t + (i : ℤ) * c) >
                ∏ i ∈ Finset.range k, ((A m' : ℤ) + (i + 1) * c) := by
              apply Finset.prod_lt_prod_of_nonempty
              · intro i _
                have hi0 : (0 : ℤ) ≤ (i : ℤ) * c := mul_nonneg (Int.natCast_nonneg _) hc0
                linarith [ht0, hpos']
              · intro i hi
                have hi' : i < k := Finset.mem_range.1 hi
                have h1i : (1 : ℤ) ≤ (i : ℤ) + 1 := by
                  have : (0 : ℤ) ≤ (i : ℤ) := Int.natCast_nonneg _
                  linarith
                nlinarith [htc, hc0]
              · exact Finset.nonempty_range_iff.2 (by omega)
            rw [ht] at hgt
            linarith [h1, hgt]
        rw [hstep, hjm1, hcast1]
        ring
  -- final formula
  have hfin : ∀ n, (A n : ℤ) = (A 0 : ℤ) + (n : ℤ) * c := by
    intro n
    have h0 := hback m₂ (le_refl m₂)
    rw [Nat.sub_self] at h0
    by_cases! hn : n ≤ m₂
    · have h := hback (m₂ - n) (by omega)
      rw [Nat.sub_sub_self hn] at h
      have hcast : ((m₂ - n : ℕ) : ℤ) = (m₂ : ℤ) - (n : ℤ) := Nat.cast_sub hn
      rw [hcast] at h
      linarith [h, h0]
    · have ht := htail (n - m₂)
      rw [Nat.add_sub_of_le hn.le] at ht
      have hcast : ((n - m₂ : ℕ) : ℤ) = (n : ℤ) - (m₂ : ℤ) := Nat.cast_sub (by omega)
      rw [hcast] at ht
      linarith [ht, h0]
  exact ⟨A 0, dN, fun n => by
    have h : (A n : ℤ) = ((A 0 + dN * n : ℕ) : ℤ) := by
      rw [hfin n, ← hdNc]
      push_cast
      ring
    exact_mod_cast h⟩


/-- The backward direction: any sequence satisfying the functional equation is
an arithmetic progression. -/
lemma backward_main {k : ℕ} (hk : 2 ≤ k) {P : Polynomial ℤ} (hmon : P.Monic)
    (hdeg : P.degree = k) (hcoef : ∀ n, n ≤ k → 0 ≤ P.coeff n)
    {A : ℕ → ℕ} (hA : ∀ m, P.eval (A m : ℤ) = ∏ i ∈ Finset.range k, (A (m + 1 + i) : ℤ))
    (hpos : ∀ m, 0 < A m) :
    ∃ a₀ d : ℕ, ∀ m, A m = a₀ + d * m := by
  have hmono := seq_monotone hk hmon hdeg hcoef hA hpos
  by_cases hbound : ∃ B, ∀ m, A m ≤ B
  · obtain ⟨B, hB⟩ := hbound
    exact backward_bounded hk hmon hdeg hcoef hA hpos hmono hB
  · push Not at hbound
    have hC0 := Csum_nonneg hcoef
    obtain ⟨n₀, hn₀⟩ := hbound (k * ((1 + k * Csum P k) ^ k + Csum P k)).toNat
    have hN₀ : ∀ m, m ≥ n₀ → (k * ((1 + k * Csum P k) ^ k + Csum P k) : ℤ) < A m := by
      intro m hm
      have h1 : A n₀ ≤ A m := hmono hm
      have h2 : (k * ((1 + k * Csum P k) ^ k + Csum P k) : ℤ) < (A n₀ : ℤ) := by
        have h3 : (k * ((1 + k * Csum P k) ^ k + Csum P k)).toNat < A n₀ := hn₀
        have h4 : ((k * ((1 + k * Csum P k) ^ k + Csum P k)).toNat : ℤ) =
            k * ((1 + k * Csum P k) ^ k + Csum P k) :=
          Int.toNat_of_nonneg (by positivity)
        rw [← h4]
        exact_mod_cast h3
      have h5 : (A n₀ : ℤ) ≤ (A m : ℤ) := by exact_mod_cast h1
      linarith [h2, h5]
    exact backward_unbounded hk hmon hdeg hcoef hA hpos hmono hN₀

snip end

problem imo2023_p3 {k : ℕ} (hk : 2 ≤ k) (a : ℕ+ → ℕ+) :
    a ∈ SolutionSet hk ↔
    (∃ P : Polynomial ℤ, P.Monic ∧ P.degree = k ∧
     (∀ n, n ≤ k → 0 ≤ P.coeff n) ∧
      ∀ n : ℕ+,
        P.eval ((a n) : ℤ) =
        ∏ i ∈ Finset.range k, a ⟨n + i + 1, Nat.succ_pos _⟩) := by
  constructor
  · rintro ⟨a₀, d, hd⟩
    refine ⟨apPoly k d, apPoly_monic k d, apPoly_degree k d,
      fun n _ => apPoly_coeff_nonneg k d n, fun n => ?_⟩
    have h2 : ∀ m : ℕ, ((a ⟨m + 1, Nat.succ_pos m⟩ : ℕ+) : ℤ) = (a₀ + d * m : ℕ) :=
      fun m => by exact_mod_cast hd m
    have h3 : ((a n : ℕ+) : ℤ) = (a₀ + d * (n.val - 1) : ℕ) := by
      have h := h2 (n.val - 1)
      rwa [show (⟨n.val - 1 + 1, Nat.succ_pos _⟩ : ℕ+) = n from
        Subtype.ext (Nat.sub_add_cancel n.pos)] at h
    rw [apPoly_eval, pnat_prod_coe]
    apply Finset.prod_congr rfl
    intro i _
    rw [h2 (n.val + i), h3]
    push_cast
    rw [Nat.cast_sub n.pos]
    push_cast
    ring
  · intro h
    obtain ⟨P, hmon, hdeg, hcoef, hP⟩ := h
    obtain ⟨a₀, d, hd⟩ := backward_main hk hmon hdeg hcoef (hA_of hP) (seqA_pos a)
    exact ⟨a₀, d, hd⟩

end Imo2023P3
