/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Data.Rat.Star
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Tactic.NormNum.Prime
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.NumberTheory],
}

/-!
# USA Mathematical Olympiad 2006, Problem 4

Find all positive integers n for which there exist an integer k ≥ 2 and
positive rational numbers a₁, a₂, ..., aₖ satisfying
a₁ + a₂ + ... + aₖ = a₁ · a₂ · ... · aₖ = n.
-/

namespace Usa2006P4

determine SolutionSet : Set ℕ := { n | n = 4 ∨ 6 ≤ n }

snip begin

/-!
We follow the solution from Evan Chen's notes
(<https://web.evanchen.cc/exams/USAMO-2006-notes.pdf>, problem USAMO 2006/4):

* If `k = 2`, then `(a₁ - a₂)² = n² - 4n` must be the square of a rational
  number; for `n ∈ {1, 2, 3, 5}` this is impossible.
* If `k ≥ 3`, the AM–GM inequality gives `n ^ (k - 1) ≥ k ^ k > 5 ^ (k - 1)`,
  forcing `n ≥ 6`.
* Constructions: `n = 4`: `(2, 2)`; even `n ≥ 6`: `(n/2, 2, 1, …, 1)`;
  `n = 7`: `(4/3, 7/6, 9/2)`; odd `n ≥ 9`: `(n/2, 1/2, 4, 1, …, 1)`.
-/

/-- `5` is not the square of a natural number. -/
lemma not_isSquare_five_nat : ¬ IsSquare (5 : ℕ) := by
  rintro ⟨m, hm⟩
  have hm2 : m ≤ 2 := by
    by_contra h
    have h3 : 3 ≤ m := by lia
    have h9 : 3 * 3 ≤ m * m := Nat.mul_le_mul h3 h3
    lia
  interval_cases m <;> norm_num at hm

/-- `5` is not the square of a rational number. -/
lemma rat_mul_self_ne_five (q : ℚ) : q * q ≠ 5 := by
  intro hq
  have hI : Irrational (Real.sqrt (5 : ℝ)) := by
    have h := Nat.Prime.irrational_sqrt (p := 5) (by norm_num)
    simpa using h
  apply hI
  refine ⟨|q|, ?_⟩
  have hq2 : (q : ℝ) ^ 2 = (5 : ℝ) := by
    have h : (q : ℝ) * q = (5 : ℝ) := by exact_mod_cast hq
    rw [← h]; ring
  rw [Rat.cast_abs, ← hq2, Real.sqrt_sq_eq_abs]

/-- Summing the entries of a list of rationals via `Fin`-indexed access. -/
lemma sum_eq_sum_get (l : List ℚ) : ∑ i : Fin l.length, l.get i = l.sum := by
  rw [← Fin.sum_ofFn, List.ofFn_get]

/-- Multiplying the entries of a list of rationals via `Fin`-indexed access. -/
lemma prod_eq_prod_get (l : List ℚ) : ∏ i : Fin l.length, l.get i = l.prod := by
  rw [← Fin.prod_ofFn, List.ofFn_get]

/-- AM–GM, raised to the `k`-th power, for positive rationals indexed by `Fin k`:
the product is at most the `k`-th power of the arithmetic mean. -/
lemma prod_le_sum_div_pow {k : ℕ} (hk : 0 < k) (z : Fin k → ℚ) (hz : ∀ i, 0 < z i) :
    ((∏ i, z i : ℚ) : ℝ) ≤ (((∑ i, z i : ℚ) : ℝ) / k) ^ k := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hzR : ∀ i : Fin k, (0 : ℝ) ≤ (z i : ℝ) := fun i ↦ Rat.cast_nonneg.mpr (hz i).le
  -- weighted AM–GM with uniform weights `1/k`
  have hW := Real.geom_mean_le_arith_mean_weighted Finset.univ
      (fun (_ : Fin k) ↦ (k : ℝ)⁻¹) (fun (i : Fin k) ↦ (z i : ℝ))
      (fun _ _ ↦ inv_nonneg.mpr (Nat.cast_nonneg _))
      (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          mul_inv_cancel₀ hkR])
      (fun i _ ↦ hzR i)
  -- raise both sides to the power `k`
  have h1 := pow_le_pow_left₀ (Finset.prod_nonneg fun i _ ↦ Real.rpow_nonneg (hzR i) _) hW k
  -- simplify the left-hand side: `(∏ zᵢ ^ (1/k)) ^ k = ∏ zᵢ`
  have hL : (∏ i : Fin k, ((z i : ℚ) : ℝ) ^ (k : ℝ)⁻¹) ^ k = ((∏ i, z i : ℚ) : ℝ) := by
    rw [← Finset.prod_pow]
    simp_rw [← Real.rpow_natCast, ← Real.rpow_mul (hzR _), inv_mul_cancel₀ hkR, Real.rpow_one]
    exact (Rat.cast_prod Finset.univ z).symm
  -- simplify the right-hand side: `∑ (1/k) * zᵢ = (∑ zᵢ) / k`
  have hR : (∑ i : Fin k, (k : ℝ)⁻¹ * ((z i : ℚ) : ℝ)) = ((∑ i, z i : ℚ) : ℝ) / k := by
    rw [← Finset.mul_sum, ← Rat.cast_sum, div_eq_mul_inv, mul_comm]
  rwa [hL, hR] at h1

snip end

problem usa2006_p4 (n : ℕ) (hn : 0 < n) :
    n ∈ SolutionSet ↔
      ∃ l : List ℚ, 2 ≤ l.length ∧ (∀ x ∈ l, 0 < x) ∧ l.sum = (n : ℚ) ∧
        l.prod = (n : ℚ) := by
  show (n = 4 ∨ 6 ≤ n) ↔
    ∃ l : List ℚ, 2 ≤ l.length ∧ (∀ x ∈ l, 0 < x) ∧ l.sum = (n : ℚ) ∧
      l.prod = (n : ℚ)
  constructor
  · -- Constructions.
    rintro (rfl | hn6)
    · -- `n = 4`: take `(2, 2)`.
      refine ⟨[2, 2], by decide, ?_, ?_, ?_⟩
      · intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> norm_num
      · norm_num [List.sum_cons, List.sum_nil]
      · norm_num [List.prod_cons, List.prod_nil]
    · rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · -- even `n = m + m ≥ 6`: take `(m, 2, 1, …, 1)` with `m - 2` ones.
        have hm : 3 ≤ m := by lia
        refine ⟨[(m : ℚ), 2] ++ List.replicate (m - 2) 1, ?_, ?_, ?_, ?_⟩
        · simp only [List.length_append, List.length_cons, List.length_nil,
            List.length_replicate]
          lia
        · intro x hx
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
            List.mem_replicate] at hx
          rcases hx with (rfl | rfl) | ⟨_, rfl⟩
          · exact_mod_cast (by lia : 0 < m)
          · norm_num
          · norm_num
        · have hrs : (List.replicate (m - 2) (1 : ℚ)).sum = ((m - 2 : ℕ) : ℚ) := by
            rw [List.sum_replicate, nsmul_eq_mul, mul_one]
          simp only [List.sum_append, List.sum_cons, List.sum_nil, add_zero, hrs]
          rw [Nat.cast_sub (by lia : 2 ≤ m)]
          push_cast
          ring
        · simp only [List.prod_append, List.prod_cons, List.prod_nil, mul_one,
            List.prod_replicate, one_pow]
          push_cast
          ring
      · -- odd `n = 2m + 1 ≥ 7`.
        have hm : 3 ≤ m := by lia
        rcases (by lia : m = 3 ∨ 4 ≤ m) with rfl | hm4
        · -- `n = 7`: take `(4/3, 7/6, 9/2)`.
          refine ⟨[4/3, 7/6, 9/2], by decide, ?_, ?_, ?_⟩
          · intro x hx
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl | rfl <;> norm_num
          · norm_num [List.sum_cons, List.sum_nil]
          · norm_num [List.prod_cons, List.prod_nil]
        · -- odd `n = 2m + 1 ≥ 9`: take `(n/2, 1/2, 4, 1, …, 1)` with `m - 4` ones.
          refine ⟨[((2 * m + 1 : ℕ) : ℚ) / 2, 1/2, 4] ++ List.replicate (m - 4) 1,
            ?_, ?_, ?_, ?_⟩
          · simp only [List.length_append, List.length_cons, List.length_nil,
              List.length_replicate]
            lia
          · intro x hx
            simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
              List.mem_replicate] at hx
            rcases hx with (rfl | rfl | rfl) | ⟨_, rfl⟩
            · positivity
            · norm_num
            · norm_num
            · norm_num
          · have hrs : (List.replicate (m - 4) (1 : ℚ)).sum = ((m - 4 : ℕ) : ℚ) := by
              rw [List.sum_replicate, nsmul_eq_mul, mul_one]
            simp only [List.sum_append, List.sum_cons, List.sum_nil, add_zero, hrs]
            rw [Nat.cast_sub (by lia : 4 ≤ m)]
            push_cast
            ring
          · simp only [List.prod_append, List.prod_cons, List.prod_nil, mul_one,
              List.prod_replicate, one_pow]
            push_cast
            ring
  · -- No `n ∈ {1, 2, 3, 5}` works.
    rintro ⟨l, hl2, hpos, hsum, hprod⟩
    by_cases hk2 : l.length = 2
    · -- `k = 2`: then `(a₁ - a₂)² = n² - 4n` is the square of a rational.
      obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hk2
      have hsum' : a + b = (n : ℚ) := by simpa using hsum
      have hprod' : a * b = (n : ℚ) := by simpa using hprod
      have hsq : (a - b) ^ 2 = (n : ℚ) ^ 2 - 4 * n := by
        have e : (a - b) ^ 2 = (a + b) ^ 2 - 4 * (a * b) := by ring
        rw [e, hsum', hprod']
      have h1 : (0 : ℚ) ≤ (n : ℚ) ^ 2 - 4 * n := hsq ▸ sq_nonneg (a - b)
      have hn4 : 4 ≤ n := by
        by_contra h
        have hlt : n < 4 := by lia
        interval_cases n <;> norm_num at h1
      have hn5 : n ≠ 5 := by
        rintro rfl
        norm_num at hsq
        exact rat_mul_self_ne_five (a - b) (by rw [← hsq]; ring)
      lia
    · -- `k ≥ 3`: AM–GM gives `k ^ k ≤ n ^ (k - 1)`, forcing `n ≥ 6`.
      have hk3 : 3 ≤ l.length := by lia
      have hB := prod_le_sum_div_pow (k := l.length) (by lia) l.get
        (fun i ↦ hpos _ (List.get_mem l i))
      rw [sum_eq_sum_get, prod_eq_prod_get, hsum, hprod] at hB
      push_cast at hB
      rw [div_pow] at hB
      -- from `n ≤ n ^ k / k ^ k` deduce `k ^ k ≤ n ^ (k - 1)`
      have hkR : (0 : ℝ) < l.length := by exact_mod_cast (by lia : 0 < l.length)
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have e1 : (n : ℝ) * (l.length : ℝ) ^ l.length ≤ (n : ℝ) ^ l.length :=
        (le_div_iff₀ (pow_pos hkR _)).mp hB
      have e2 : (n : ℝ) ^ l.length = (n : ℝ) ^ (l.length - 1) * n := by
        rw [← pow_succ, Nat.sub_add_cancel (by lia : 1 ≤ l.length)]
      rw [e2] at e1
      have e3 : (l.length : ℝ) ^ l.length ≤ (n : ℝ) ^ (l.length - 1) := by
        rw [mul_comm ((n : ℝ)) ((l.length : ℝ) ^ l.length)] at e1
        exact (mul_le_mul_iff_left₀ hnR).mp e1
      have e4 : l.length ^ l.length ≤ n ^ (l.length - 1) := by exact_mod_cast e3
      suffices hnn : 6 ≤ n from Or.inr hnn
      by_contra hlt
      have hn5 : n ≤ 5 := by lia
      have e5 : n ^ (l.length - 1) ≤ 5 ^ (l.length - 1) := pow_le_pow_left' hn5 _
      have e6 : l.length ^ l.length ≤ 5 ^ (l.length - 1) := le_trans e4 e5
      have hk5 : l.length ≤ 5 := by
        have e7 : l.length ^ l.length ≤ 5 ^ l.length :=
          le_trans e6 (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le l.length 1))
        exact (Nat.pow_le_pow_iff_left (by lia : l.length ≠ 0)).mp e7
      have hk35 : l.length = 3 ∨ l.length = 4 ∨ l.length = 5 := by lia
      rcases hk35 with h | h | h <;> rw [h] at e6 <;> norm_num at e6

end Usa2006P4
