/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 1976, Problem 5

n is a positive integer and m = 2n. aᵢⱼ = 0, 1 or -1 for 1 ≤ i ≤ n,
1 ≤ j ≤ m. The m unknowns x₁, x₂, ... , xₘ satisfy the n equations:

  aᵢ₁x₁ + aᵢ₂x₂ + ... + aᵢₘxₘ = 0,

for i = 1, 2, ... , n. Prove that the system has a solution in integers
of absolute value at most m, not all zero.

# Solution

We use a counting argument
(https://prase.cz/kalva/imo/isoln/isoln765.html). If each |xⱼ| ≤ n, then
each left-hand side is an integer between -2n² and 2n², so the tuple of
left-hand sides takes at most (4n² + 1)ⁿ values. But there are
(2n + 1)²ⁿ = (4n² + 4n + 1)ⁿ > (4n² + 1)ⁿ such tuples (x₁, ... , xₘ),
so two distinct tuples x and x' give the same left-hand sides. Then
x - x' is a nonzero integer solution with |xⱼ - x'ⱼ| ≤ 2n = m.
-/

namespace Imo1976P5

snip begin

/-- The candidate values for the tuple of unknowns: integers between `-n`
and `n` in each coordinate. -/
noncomputable def valueFinset (n : ℕ) : Finset (Fin (2 * n) → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(n : ℤ)) (n : ℤ)

/-- The possible values of the tuple of left-hand sides: each coordinate is
an integer between `-2n²` and `2n²`. -/
noncomputable def lhsFinset (n : ℕ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(2 * (n : ℤ) ^ 2)) (2 * (n : ℤ) ^ 2)

/-- The tuple of left-hand sides of the equations, as a function of the
tuple of unknowns. -/
def lhs (n : ℕ) (a : Fin n → Fin (2 * n) → ℤ) (x : Fin (2 * n) → ℤ) :
    Fin n → ℤ :=
  fun i => ∑ j, a i j * x j

theorem card_valueFinset (n : ℕ) :
    (valueFinset n).card = (2 * n + 1) ^ (2 * n) := by
  have h : (Finset.Icc (-(n : ℤ)) (n : ℤ)).card = 2 * n + 1 := by
    rw [Int.card_Icc,
      show (n : ℤ) + 1 - -(n : ℤ) = ((2 * n + 1 : ℕ) : ℤ) by push_cast; ring,
      Int.toNat_natCast]
  simp only [valueFinset, Fintype.piFinset, Finset.card_map, Finset.card_pi,
    h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem card_lhsFinset (n : ℕ) :
    (lhsFinset n).card = (4 * n ^ 2 + 1) ^ n := by
  have h :
      (Finset.Icc (-(2 * (n : ℤ) ^ 2)) (2 * (n : ℤ) ^ 2)).card = 4 * n ^ 2 + 1 := by
    rw [Int.card_Icc,
      show 2 * (n : ℤ) ^ 2 + 1 - -(2 * (n : ℤ) ^ 2) = ((4 * n ^ 2 + 1 : ℕ) : ℤ) by
        push_cast; ring,
      Int.toNat_natCast]
  simp only [lhsFinset, Fintype.piFinset, Finset.card_map, Finset.card_pi,
    h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The pigeonhole step: there are more candidate tuples than possible
values of the left-hand sides. -/
theorem card_lhs_lt_card_value (n : ℕ) (hn : 0 < n) :
    (lhsFinset n).card < (valueFinset n).card := by
  rw [card_lhsFinset, card_valueFinset,
    show (2 * n + 1) ^ (2 * n) = ((2 * n + 1) ^ 2) ^ n by rw [← pow_mul]]
  have h2 : 4 * n ^ 2 + 1 < (2 * n + 1) ^ 2 := by
    have hsq : (2 * n + 1) ^ 2 = 4 * n ^ 2 + 4 * n + 1 := by ring
    omega
  exact Nat.pow_lt_pow_left h2 hn.ne'

/-- Each left-hand side is bounded by `2n²` when every |xⱼ| ≤ n. -/
theorem mapsTo (n : ℕ) (a : Fin n → Fin (2 * n) → ℤ)
    (ha : ∀ i j, a i j = 0 ∨ a i j = 1 ∨ a i j = -1) :
    Set.MapsTo (lhs n a) ↑(valueFinset n) ↑(lhsFinset n) := by
  intro x hx
  simp only [Finset.mem_coe, valueFinset, lhsFinset, Fintype.mem_piFinset] at hx ⊢
  intro i
  simp only [Finset.mem_Icc, ← abs_le]
  unfold lhs
  calc |∑ j, a i j * x j| ≤ ∑ j, |a i j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin (2 * n), (n : ℤ) := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        have ha1 : |a i j| ≤ 1 := by
          rcases ha i j with h | h | h <;> simp [h]
        have hx1 : |x j| ≤ (n : ℤ) := abs_le.mpr (Finset.mem_Icc.mp (hx j))
        have h := mul_le_mul ha1 hx1 (abs_nonneg _) zero_le_one
        rwa [one_mul] at h
    _ = 2 * (n : ℤ) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

snip end

problem imo1976_p5 (n : ℕ) (hn : 0 < n) (a : Fin n → Fin (2 * n) → ℤ)
    (ha : ∀ i j, a i j = 0 ∨ a i j = 1 ∨ a i j = -1) :
    ∃ x : Fin (2 * n) → ℤ,
      (∀ j, |x j| ≤ 2 * (n : ℤ)) ∧ (∃ j, x j ≠ 0) ∧
        ∀ i, ∑ j, a i j * x j = 0 := by
  obtain ⟨x, hxS, x', hx'S, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (card_lhs_lt_card_value n hn)
      (mapsTo n a ha)
  have hxS' : ∀ j, x j ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) :=
    Fintype.mem_piFinset.mp hxS
  have hx'S' : ∀ j, x' j ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) :=
    Fintype.mem_piFinset.mp hx'S
  refine ⟨x - x', fun j => ?_, ?_, fun i => ?_⟩
  · rw [Pi.sub_apply, abs_le]
    have h1 := hxS' j
    have h2 := hx'S' j
    rw [Finset.mem_Icc] at h1 h2
    constructor <;> linarith
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
    exact ⟨j, by rw [Pi.sub_apply]; exact sub_ne_zero.mpr hj⟩
  · have h : (∑ j, a i j * x j) = ∑ j, a i j * x' j := congrFun heq i
    have hsum : ∑ j, a i j * (x - x') j = ∑ j, (a i j * x j - a i j * x' j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Pi.sub_apply, mul_sub]
    rw [hsum, Finset.sum_sub_distrib, sub_eq_zero]
    exact h

end Imo1976P5
