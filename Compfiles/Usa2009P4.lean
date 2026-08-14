/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra, .Inequality] }

/-!
# USA Mathematical Olympiad 2009, Problem 4

For n ≥ 2, let a₁, a₂, ..., aₙ be positive real numbers such that

  (a₁ + a₂ + ... + aₙ) (1/a₁ + 1/a₂ + ... + 1/aₙ) ≤ (n + 1/2)².

Prove that max(a₁, a₂, ..., aₙ) ≤ 4 min(a₁, a₂, ..., aₙ).
-/

namespace Usa2009P4

snip begin

-- The proof follows the official solution (see e.g. Evan Chen's notes at
-- https://web.evanchen.cc/exams/USAMO-2009-notes.pdf): cross-pair the two
-- distinguished entries inside the Cauchy–Schwarz inequality.

/-- Cross-paired Cauchy–Schwarz: for any two distinct indices `p` and `q`, the product
`(∑ aᵢ)(∑ 1/aᵢ)` is bounded below by `(√(a p / a q) + √(a q / a p) + (n - 2))²`. -/
lemma sum_mul_sum_inv_ge {n : ℕ} {a : Fin n → ℝ} (ha : ∀ i, 0 < a i)
    {p q : Fin n} (hpq : p ≠ q) :
    (√(a p / a q) + √(a q / a p) + ((n : ℝ) - 2)) ^ 2 ≤
      (∑ i, a i) * (∑ i, (a i)⁻¹) := by
  have hqmem : q ∈ Finset.univ.erase p :=
    Finset.mem_erase.mpr ⟨hpq.symm, Finset.mem_univ q⟩
  have hn2 : 2 ≤ n := by
    have hcard : 1 < (Finset.univ : Finset (Fin n)).card :=
      Finset.one_lt_card.mpr ⟨p, Finset.mem_univ p, q, Finset.mem_univ q, hpq⟩
    rwa [Finset.card_univ, Fintype.card_fin] at hcard
  -- The term at `p` in the mixed sum.
  have hfp : √(a p) * √((a (Equiv.swap p q p))⁻¹) = √(a p / a q) := by
    rw [Equiv.swap_apply_left, ← Real.sqrt_mul (ha p).le, div_eq_mul_inv]
  -- The term at `q` in the mixed sum.
  have hfq : √(a q) * √((a (Equiv.swap p q q))⁻¹) = √(a q / a p) := by
    rw [Equiv.swap_apply_right, ← Real.sqrt_mul (ha q).le, div_eq_mul_inv]
  -- Each remaining term of the mixed sum equals `1`, and there are `n - 2` of them.
  have hrest : ∑ i ∈ (Finset.univ.erase p).erase q, √(a i) * √((a (Equiv.swap p q i))⁻¹)
      = (n : ℝ) - 2 := by
    have h1 : ∀ i ∈ (Finset.univ.erase p).erase q,
        √(a i) * √((a (Equiv.swap p q i))⁻¹) = 1 := by
      intro i hi
      rw [Finset.mem_erase, Finset.mem_erase] at hi
      obtain ⟨hiq, hip, -⟩ := hi
      rw [Equiv.swap_apply_of_ne_of_ne hip hiq, Real.sqrt_inv,
        mul_inv_cancel₀ (Real.sqrt_pos.mpr (ha i)).ne']
    have hcard : ((Finset.univ.erase p).erase q).card = n - 2 := by
      rw [Finset.card_erase_of_mem hqmem, Finset.card_erase_of_mem (Finset.mem_univ p),
        Finset.card_univ, Fintype.card_fin]
      omega
    calc ∑ i ∈ (Finset.univ.erase p).erase q, √(a i) * √((a (Equiv.swap p q i))⁻¹)
        = ∑ i ∈ (Finset.univ.erase p).erase q, (1 : ℝ) := Finset.sum_congr rfl h1
      _ = (((Finset.univ.erase p).erase q).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = (n : ℝ) - 2 := by
          rw [hcard, Nat.cast_sub hn2]
          norm_num
  -- The mixed sum splits into the two cross terms and `n - 2` ones.
  have hmixed : ∑ i, √(a i) * √((a (Equiv.swap p q i))⁻¹)
      = √(a p / a q) + √(a q / a p) + ((n : ℝ) - 2) := by
    have s1 : ∑ i, √(a i) * √((a (Equiv.swap p q i))⁻¹)
        = √(a p) * √((a (Equiv.swap p q p))⁻¹)
          + ∑ i ∈ Finset.univ.erase p, √(a i) * √((a (Equiv.swap p q i))⁻¹) :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ p)).symm
    have s2 : ∑ i ∈ Finset.univ.erase p, √(a i) * √((a (Equiv.swap p q i))⁻¹)
        = √(a q) * √((a (Equiv.swap p q q))⁻¹)
          + ∑ i ∈ (Finset.univ.erase p).erase q, √(a i) * √((a (Equiv.swap p q i))⁻¹) :=
      (Finset.add_sum_erase _ _ hqmem).symm
    rw [s1, s2, hfp, hfq, hrest, add_assoc]
  -- The two squared sums are just `∑ aᵢ` and `∑ (aᵢ)⁻¹`.
  have hsq1 : ∑ i, √(a i) ^ 2 = ∑ i, a i :=
    Finset.sum_congr rfl fun i _ ↦ Real.sq_sqrt (ha i).le
  have hsq2 : ∑ i, (√((a (Equiv.swap p q i))⁻¹)) ^ 2 = ∑ i, (a i)⁻¹ := by
    have e : ∑ i, (√((a (Equiv.swap p q i))⁻¹)) ^ 2 = ∑ i, (a (Equiv.swap p q i))⁻¹ :=
      Finset.sum_congr rfl fun i _ ↦ Real.sq_sqrt (inv_nonneg.mpr (ha _).le)
    rw [e]
    exact Equiv.sum_comp (Equiv.swap p q) (fun i ↦ (a i)⁻¹)
  -- Cauchy–Schwarz applied to `√aᵢ` and `√(a (Equiv.swap p q i))⁻¹`.
  calc (√(a p / a q) + √(a q / a p) + ((n : ℝ) - 2)) ^ 2
      = (∑ i, √(a i) * √((a (Equiv.swap p q i))⁻¹)) ^ 2 := by rw [hmixed]
    _ ≤ (∑ i, √(a i) ^ 2) * (∑ i, (√((a (Equiv.swap p q i))⁻¹)) ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = (∑ i, a i) * (∑ i, (a i)⁻¹) := by rw [hsq1, hsq2]

/-- Any entry is at most `4` times any other entry. -/
lemma entry_le_four_mul_entry {n : ℕ} {a : Fin n → ℝ} (ha : ∀ i, 0 < a i)
    (h : (∑ i, a i) * (∑ i, 1 / a i) ≤ ((n : ℝ) + 1 / 2) ^ 2) (p q : Fin n) :
    a p ≤ 4 * a q := by
  rcases le_or_gt (a p) (a q) with hpq | hpq
  · -- Easy case: `a p ≤ a q ≤ 4 * a q`.
    have hq0 := ha q
    linarith
  · -- The interesting case `a q < a p`.
    have hpq_ne : p ≠ q := by rintro rfl; exact (lt_irrefl _ hpq).elim
    have hn2 : (2 : ℝ) ≤ n := by
      have hcard : 1 < (Finset.univ : Finset (Fin n)).card :=
        Finset.one_lt_card.mpr ⟨p, Finset.mem_univ p, q, Finset.mem_univ q, hpq_ne⟩
      rw [Finset.card_univ, Fintype.card_fin] at hcard
      exact_mod_cast hcard
    have hCS := sum_mul_sum_inv_ge ha hpq_ne
    -- Abbreviate `t = √(a p / a q)`, so `√(a q / a p) = t⁻¹`.
    set t := √(a p / a q) with ht
    have hinv : √(a q / a p) = t⁻¹ := by
      rw [ht, ← inv_div, Real.sqrt_inv]
    rw [hinv] at hCS
    have h' : (∑ i, a i) * (∑ i, (a i)⁻¹) ≤ ((n : ℝ) + 1 / 2) ^ 2 := by
      simpa only [one_div] using h
    have h3 : (t + t⁻¹ + ((n : ℝ) - 2)) ^ 2 ≤ ((n : ℝ) + 1 / 2) ^ 2 := hCS.trans h'
    have ht0 : 0 < t := Real.sqrt_pos.mpr (div_pos (ha p) (ha q))
    have ht1 : 1 < t := by
      rw [ht, Real.lt_sqrt zero_le_one, one_pow, one_lt_div (ha q)]
      exact hpq
    have hbase : 0 ≤ t + t⁻¹ + ((n : ℝ) - 2) := by positivity
    have h4 : t + t⁻¹ + ((n : ℝ) - 2) ≤ (n : ℝ) + 1 / 2 :=
      (pow_le_pow_iff_left₀ hbase (by positivity) two_ne_zero).mp h3
    have h5 : t + t⁻¹ ≤ 5 / 2 := by linarith
    -- Multiply by `2t > 0`: from `t + 1/t ≤ 5/2` we get `(2t - 1)(t - 2) ≤ 0`, so `t ≤ 2`.
    have hmul : t * (t + t⁻¹) = t ^ 2 + 1 := by
      rw [mul_add, mul_inv_cancel₀ ht0.ne']
      ring
    have h6 : t ^ 2 + 1 ≤ t * (5 / 2) := by
      rw [← hmul]
      exact mul_le_mul_of_nonneg_left h5 ht0.le
    have ht2 : t ≤ 2 := by
      by_contra hcon
      push Not at hcon
      have h1 : (0 : ℝ) < t - 2 := by linarith
      have h2 : (0 : ℝ) < 2 * t - 1 := by linarith
      have hpos : (0 : ℝ) < (t - 2) * (2 * t - 1) := mul_pos h1 h2
      nlinarith
    have hsqt : t ^ 2 = a p / a q := by
      rw [ht]
      exact Real.sq_sqrt (div_nonneg (ha p).le (ha q).le)
    have hfinal : a p / a q ≤ 4 := by
      rw [← hsqt]
      have hsq4 : t ^ 2 ≤ (2 : ℝ) ^ 2 := pow_le_pow_left₀ ht0.le ht2 2
      norm_num at hsq4
      exact hsq4
    calc a p = (a p / a q) * a q := (div_mul_cancel₀ _ (ha q).ne').symm
      _ ≤ 4 * a q := mul_le_mul_of_nonneg_right hfinal (ha q).le

snip end

problem usa2009_p4 {n : ℕ} (hn : 2 ≤ n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i)
    (h : (∑ i, a i) * (∑ i, 1 / a i) ≤ ((n : ℝ) + 1 / 2) ^ 2) :
    (Finset.univ.image a).max' (Finset.image_nonempty.mpr ⟨⟨0, by omega⟩, Finset.mem_univ _⟩)
      ≤ 4 * (Finset.univ.image a).min'
          (Finset.image_nonempty.mpr ⟨⟨0, by omega⟩, Finset.mem_univ _⟩) := by
  obtain ⟨p, -, hp⟩ := Finset.mem_image.mp (Finset.max'_mem (Finset.univ.image a) _)
  obtain ⟨q, -, hq⟩ := Finset.mem_image.mp (Finset.min'_mem (Finset.univ.image a) _)
  rw [← hp, ← hq]
  exact entry_le_four_mul_entry ha h p q

end Usa2009P4
