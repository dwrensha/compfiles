/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file

/-!
# USA Mathematical Olympiad 1981, Problem 5

Show that for any positive real number x and any nonnegative
integer n,

    ∑ₖ (⌊kx⌋/k) ≤ ⌊nx⌋

where the sum goes from k = 1 to k = n, inclusive.
-/

namespace Usa1981P5
open BigOperators

problem usa1981_p5 (x : ℝ) (n : ℕ) :
    ∑ k in Finset.Icc 1 n, ((⌊k * x⌋:ℝ)/k) ≤ ⌊n * x⌋ := by
  -- We follow the solution from
  -- https://artofproblemsolving.com/wiki/index.php/1981_USAMO_Problems/Problem_5

  -- We write ⌊kx⌋ = kx - {kx}.

  -- We need to prove
  -- $\sum_{1}^{n}\left(\frac{\{kx\}}{k}\right)\geq \{nx\}.$
  simp_rw [←Int.self_sub_fract, sub_div, mul_div_right_comm]
  rw [Finset.sum_sub_distrib]
  have h1 : ∀ x1 ∈ Finset.Icc 1 n, (x1 : ℝ) / (x1 : ℝ) * x = x := fun x1 hx ↦ by
    have h3 : (x1:ℝ) ≠ 0 := by
      rw [Finset.mem_Icc] at hx; replace hx := hx.1;
      intro hx1
      obtain rfl : x1 = 0 := Nat.cast_eq_zero.mp hx1
      exact Nat.not_succ_le_zero 0 hx
    rw [div_self h3, one_mul]
  rw [Finset.sum_congr rfl h1]
  have h2 : ∑ x_1 in Finset.Icc 1 n, x = n * x := by
    rw [Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul]
  rw [h2]
  suffices H : Int.fract (↑n * x) ≤
               ∑ x_1 in Finset.Icc 1 n, Int.fract (↑x_1 * x) / ↑x_1 from
    sub_le_sub_left H (↑n * x)

  -- Let's denote $a_k=\{kx\}$
  let a : ℕ → ℝ := fun k ↦ Int.fract (k * x)

  -- It is easy to see that $a_k+a_m \geq a_{k+m}$
  have h4 : ∀ k m, a (k + m) ≤ a k + a m := fun k m ↦ by
    unfold_let a
    dsimp
    have h5 : ↑(k + m) * x = ↑ k * x + ↑m * x := by
      push_cast; exact add_mul (↑k) (↑m) x
    rw [h5]
    exact Int.fract_add_le (↑k * x) (↑m * x)

  change a n ≤ ∑ ii in Finset.Icc 1 n, a ii / ii

  induction' n using Nat.strongInductionOn with n ih
  wlog H : 0 < n with hn
  · obtain rfl : n = 0 := Nat.eq_zero_of_not_pos H
    simp

  -- Let's take $m$ such that $\frac{a_m}{m}$ is minimal.
  have : Nonempty (Finset.Icc 1 n) := by
    use 1; rw [Finset.mem_Icc]; simp only [le_refl, true_and]; exact H
  obtain ⟨⟨m, hm1⟩, hm2⟩ :=
    Finite.exists_min (fun (m : Finset.Icc 1 n) ↦ a m / m)

  rw [Finset.mem_Icc] at hm1
  obtain ⟨hm3, hm4⟩ := hm1
  obtain rfl | hlt := (Nat.lt_or_eq_of_le hm4).symm
  · have h6 : ∀ ii ∈ Finset.Icc 1 m, a m / m ≤ a ii / ii :=
      fun ii hii ↦ hm2 ⟨ii, hii⟩
    have h7 : ∑ ii in Finset.Icc 1 m, a m / ↑m ≤
              ∑ ii in Finset.Icc 1 m, a ii / ↑ii := Finset.sum_le_sum h6
    have h8 : a m = ∑ ii in Finset.Icc 1 m, a m / ↑m := by
      have h9 : (m:ℝ) ≠ 0 := by
        intro hm5
        obtain rfl : m = 0 := Nat.cast_eq_zero.mp hm5
        exact Nat.not_succ_le_zero 0 hm3
      rw [Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul]
      exact (mul_div_cancel' _ h9).symm
    rw [h8]
    exact h7

  have h9 := ih (n - m) (Nat.sub_lt H hm3)
  sorry
