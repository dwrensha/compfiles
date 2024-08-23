/-
Copyright (c) 2023 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 1986, Problem 1

Let d be any positive integer not equal to 2, 5 or 13.
Show that one can find distinct a, b in the set {2, 5, 13, d} such that ab - 1
is not a perfect square.
-/

namespace Imo1986P1

snip begin

/-
We prove a slightly stronger statement, namely:
Let d be any integer, then 2 * d - 1, 5 * d - 1 and 13 * d - 1 can't all be perfect squares.
We follow "Solution 2" on https://artofproblemsolving.com/wiki/index.php/1986_IMO_Problems/Problem_1
by showing a contradiction: we show d is odd and d is even.
First we assume that there are p, q and r such that:
2 * d - 1 = p^2
5 * d - 1 = q^2 and
13 * d - 1 = r^2

The fact that d is odd follows from the fact that p is odd.
The fact that d is even follows from examining the difference 13 * d - 5 * d.
-/

theorem imo1986_p1' (d : ℤ):
    ¬ ((IsSquare (2 * d - 1)) ∧ (IsSquare (5 * d - 1)) ∧ (IsSquare (d * 13 - 1))) := by
  rintro ⟨⟨p, hp⟩, ⟨q, hq⟩, ⟨r, hr⟩⟩
  rw [← pow_two] at hp hq hr
  have hpodd : Odd p := (Int.odd_pow' two_ne_zero).mp (by use d - 1; rw [← hp]; ring)
  cases' hpodd with k hk
  have hp := hp.symm
  have hdp : d  = 2*(k + k^2) + 1 := by
    rw [hk, ←(add_left_inj 1), sub_add_cancel _] at hp
    ring_nf at hp
    have h422 : (4 : ℤ) = 2 * 2 := by norm_num
    simp only [h422,  ← mul_assoc] at hp
    nth_rw 1 [← one_mul 2] at hp
    rw [← add_mul, ← add_mul, mul_left_inj' two_ne_zero] at hp
    rw [← hp]
    ring
  have hdodd : Odd d := by use k + k ^ 2
  have hd_sub_one : Even (d - 1) := by use (k + k ^ 2); rw [hdp]; ring
  have hqeven : Even q := by
    refine (Int.even_pow' two_ne_zero).mp ?_
    have heq : 5 * d - 1 = 5 * (d - 1) + 4 := by ring_nf
    rw [← hq, heq]
    exact Even.add (Even.mul_left hd_sub_one 5) (by use 2; rfl)
  have hreven : Even (r : ℤ) := by
    refine (Int.even_pow' two_ne_zero).mp ?_
    have heq : d * 13 - 1 = 13*(d - 1) + 12 := by
      rw [mul_comm]
      ring_nf
    rw [← hr, heq]
    exact Even.add (Even.mul_left hd_sub_one 13) (by use 6; rfl)
  cases' hqeven with n hqeven'
  cases' hreven with m hreven'
  have h8d : d * 8 = 4*m^2 - 4*n^2 := by
    calc d * 8 = (d * 13 - 1) - (5 * d - 1) := by ring
          _ = r^2 - q^2 := by rw [hr, hq]
          _ = (m + m)^2 - (n + n)^2 := by rw [hqeven', hreven']
          _ = 4*m^2 - 4*n^2 := by ring
  have h4d : 4 * (2 * d) = 4 * (m^2 - n^2) := by ring_nf; rw [h8d]; ring_nf
  have hnm' : 2*d = (m + n)*(m - n):= by
    rw [← pow_two_sub_pow_two]
    refine (mul_right_inj' ?_).mp h4d
    decide
  have h2d : Even ((m + n) * (m - n)) := by use d; rw [← two_mul, hnm']
  have hnm_parity : (Even m ↔ Even n) := by
    cases' Int.even_mul.mp h2d with hmneven hmneven
    · exact Int.even_add.mp hmneven
    · exact Int.even_sub.mp hmneven
  have hnm_sub : Even (m - n) := Int.even_sub.mpr hnm_parity
  have hnm_add : Even (m + n) := Int.even_add.mpr hnm_parity

  have hdeven : Even d := by
    cases' hnm_sub with v hnm_sub
    cases' hnm_add with w hnm_add
    simp only [hnm_sub, hnm_add, ← two_mul] at hnm'
    rw [mul_assoc,  mul_right_inj' two_ne_zero, ← mul_assoc, mul_comm w, mul_assoc, two_mul] at hnm'
    exact ⟨w * v, hnm'⟩
  exact Int.not_odd_iff_even.mpr hdeven hdodd

snip end

problem imo1986_p1 (d : ℤ) (_hdpos : 1 ≤ d) (h2 : d ≠ 2) (h5 : d ≠ 5) (h13 : d ≠ 13) :
    ∃ a b :({2, 5, 13, d} : Finset ℤ), (a ≠ b) ∧ ¬ ∃ z, z^2 = (a * (b : ℤ) - 1) := by
  by_contra h
  simp only [ne_eq, Subtype.exists, Finset.mem_singleton, Finset.mem_insert, false_or,
  exists_and_right, Subtype.mk.injEq, exists_prop, exists_eq_or_imp, exists_eq_left, not_or,
  not_exists, not_and, not_forall, not_not, and_imp, forall_eq_or_imp, IsEmpty.forall_iff,
  forall_true_left, forall_eq, true_and, not_true, and_true] at h
  have := h.1.2.2 h2.symm
  cases' this with p hp
  have := h.2.1.2.2 h5.symm
  cases' this with q hq
  have := h.2.2.2.2.2 h13
  cases' this with r hr
  have : (IsSquare (2 * d - 1)) ∧ (IsSquare (5 * d - 1)) ∧ (IsSquare (d * 13 - 1)) := by
    refine ⟨?_, ?_, ?_⟩
    · use p; rw [← pow_two]; exact hp.symm
    · use q; rw [← pow_two]; exact hq.symm
    · use r; rw [← pow_two]; exact hr.symm
  exact imo1986_p1' d this


end Imo1986P1
