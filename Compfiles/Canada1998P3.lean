/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra, .Inequality] }

/-!
Canadian Mathematical Olympiad 1998, Problem 3

Let n be a natural number such that n ≥ 2. Show that

  (1/(n + 1))(1 + 1/3 + ... + 1/(2n - 1)) > (1/n)(1/2 + 1/4 + ... + 1/2n).
-/

namespace Canada1998P3

open BigOperators

problem canada1998_p3 (n : ℕ) (hn : 2 ≤ n) :
    (1/(n:ℝ)) * ∑ i in Finset.range n, (1/(2 * (i:ℝ) + 2)) <
    (1/((n:ℝ) + 1)) * ∑ i in Finset.range n, (1/(2 * (i:ℝ) + 1)) := by
  -- Follows the proof in _Mathematical Olympiads 1998-1999_
  -- by Titu Andreescu and Zuming Feng

  cases' n with n; · norm_num at hn
  cases' n with n; · norm_num at hn

  revert hn
  intro h2; clear h2

  -- We prove
  -- (n + 1)(1/2 + 1/4 + ... + 1/2n) < n(1 + 1/3 + ... + 1/(2n - 1))
  -- by induction.
  suffices
   ((n.succ.succ:ℝ) + 1) * ∑ i in Finset.range n.succ.succ, (1/(2 * (i:ℝ) + 2)) <
   (n.succ.succ:ℝ) * ∑ i in Finset.range n.succ.succ, (1/(2 * (i:ℝ) + 1))
      by rw [div_mul_eq_mul_div₀, one_mul, div_mul_eq_mul_div₀, one_mul]
         apply (div_lt_div_iff (by positivity) (by positivity)).mpr
         linarith

  induction n with
  | zero =>
     -- Base case: when n = 2, we have 8/3 > 9/4.
     field_simp[Finset.sum_range_succ]
     norm_num
  | succ m ih =>
    let k := m.succ.succ

    -- Inductive case: suppose claim is true for k ≥ 2. Then we have
    -- k (1 + 1/3 + ... 1/(2k - 1)) > (k + 1)(1/2 + 1/4 + ... + 1/2k).
    -- Note that
    --  (1 + 1/3 + ... + 1/(2k-1)) + (k+1)/(2k+1)
    --    = (1/2 + 1/3 + ... + 1/(2k-1)) + 1/2 + (k+1)/(2k+1)
    --    > (1/2 + 1/4 + ... + 1/2k) + 1/2 + (k+1)/(2k+1)
    --    > (1/2 + 1/4 + ... + 1/2k) + (k + 1)/(2k + 2) + 1/(2k+1)
    --    > (1/2 + 1/4 + ... + 1/2k) + (k + 2)/(2k + 2).

    have h1 : (1:ℝ) / (2 * ↑(0:ℕ) + 1) = 1 := by norm_num

    have h2 : ∀ k' ∈ Finset.range (m + 1), (1:ℝ) / (2 * ↑(k' + 1) + 1 + 1) <
                                           (1:ℝ) / (2 * ↑(k' + 1) + 1) := by
      intro k' _
      apply div_lt_div_of_lt_left zero_lt_one
      · positivity
      · exact lt_add_one _

    have h3 : (∑i in Finset.range k, 1 / (2 * (i:ℝ) + 1)) + (k+1)/(2 * k + 1)
            = _ := rfl

    nth_rewrite 1 [Finset.sum_range_succ'] at h3
    rw [h1, add_assoc] at h3

    have h4 : Finset.Nonempty (Finset.range (m + 1)) :=
      Finset.nonempty_range_succ
    have h5 := Finset.sum_lt_sum_of_nonempty h4 h2
    norm_cast at h5

    have h6 : (∑i in Finset.range k, 1 / (2 * (i:ℝ) + 1 + 1)) = _ := rfl
    nth_rewrite 1 [Finset.sum_range_succ'] at h6

    have h7' : (2:ℝ) * (k:ℝ) ≥ 4 := by
      have hh2' : k ≥ 2 := Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le m))
      have hh2 : (k:ℝ) ≥ 2 := by exact_mod_cast hh2'
      calc
        (2:ℝ) * (k:ℝ) ≥ (2:ℝ) * 2 := mul_le_mul_of_nonneg_left hh2 (by linarith)
        _ = 4 := by norm_num

    have h7 : 1 / (2 * (k:ℝ) + 2) < 1 / 2 := by apply div_lt_div' <;> linarith
    have h8 : ((k:ℝ)+1)/(2 * (k:ℝ) + 2) < ((k:ℝ)+1)/(2 * (k:ℝ) + 1) :=
      by apply div_lt_div' <;> linarith

    have h9 :=
           --  (1 + 1/3 + ... + 1/(2k-1)) + (k+1)/(2k+1)
      calc (∑i in Finset.range k, 1 / (2 * (i:ℝ) + 1)) + (k+1)/(2 * k + 1)

      --    = (1/3 + ... + 1/(2k-1)) + (1 + (k+1)/(2k+1))
         = (∑i in Finset.range (m+1), 1 / (2 * ((i + 1):ℝ) + 1))
               + (1 + (k+1)/(2 * k + 1)) := by rw [←h3]; norm_cast
                                        -- TODO shouldn't need casting?

       --    > (1/4 + ... + 1/2k) + (1 + (k+1)/(2k+1))
       _ > (∑i in Finset.range (m+1), 1 / (2 * ((i + 1):ℝ) + 1 + 1))
              + (1 + (k+1)/(2 * k + 1)) := by norm_cast; linarith

       _ = (∑i in Finset.range (m+1), 1 / (2 * ((i + 1):ℝ) + 1 + 1))
              + (1/2 + 1/2 + (k+1)/(2 * k + 1)) := by field_simp
       _ = (∑i in Finset.range (m+1), 1 / (2 * ((i + 1):ℝ) + 1 + 1))
              + 1/2 + (1/2 + (k+1)/(2 * k + 1)) := by ring
       _ = (∑i in Finset.range (m+1), 1 / (2 * ((i + 1):ℝ) + 1 + 1))
              + 1/(2 *(((0:ℕ)):ℝ) + 1 + 1) + (1/2 + (k+1)/(2 * k + 1)) :=
                      by norm_num
       _ = (∑i in Finset.range k, 1 / (2 * (i:ℝ) + 1 + 1)) +
              (1/2 + (k+1)/(2 * k + 1)) := by rw [←h6]; norm_cast

       --    > (1/2 + 1/4 + ... + 1/2k) + (k + 1)/(2k + 2) + 1/(2k+1)
       _ > (∑i in Finset.range k, 1 / (2 * (i:ℝ) + 1 + 1)) +
              ((k+1)/(2 * k + 2) + 1/(2 * k + 2)) := by linarith

       --    = (1/2 + 1/4 + ... + 1/2k) + (k + 2)/(2k + 2).
       _ = (∑i in Finset.range k, 1 / (2 * (i:ℝ) + 1 + 1)) +
              (k+2)/(2 * k + 2) := by field_simp; ring

   --
   -- Then we are done because
   -- (k + 1)(1 + 1/3 + ... + 1/(2k - 1) + 1/(2k + 1))
   --  = k (1 + 1/3 + ... + 1/(2k - 1))
   --     + (1 + 1/3 + ... + 1/(2k - 1)) + (k + 1)/(2k + 1)
   --  > k (1 + 1/3 + ... + 1/(2k - 1))
   --     + (1/2 + 1/4 + ... + 1/2k)) + (k + 2)/(2k + 2)
   --    (by h9, proved above)

   --  > (k + 2)(1/2 + 1/4 + ... + 1/(2k + 2)).

    have :=
      calc (k + 1) * (∑i in Finset.range k.succ, 1 / (2 * (i:ℝ) + 1))
         = k * (∑i in Finset.range k, 1 / (2 * (i:ℝ) + 1)) +
             ((∑i in Finset.range k, 1 / (2 * (i:ℝ) + 1)) +
                (k + 1) / (2 * k + 1)) := by
                   rw [Finset.sum_range_succ]; ring
       _ > k * (∑i in Finset.range k, 1 / (2 * (i:ℝ) + 1)) +
             ((∑i in Finset.range k, 1 / (2 * (i:ℝ) + 1 + 1)) +
                (k + 2) / (2 * k + 2)) := add_lt_add_left h9 _
       _ > (k + 1) * (∑i in Finset.range k, 1 / (2 * (i:ℝ) + 2)) +
             ((∑i in Finset.range k, 1 / (2 * (i:ℝ) + 1 + 1)) +
                (k + 2) / (2 * k + 2)) := add_lt_add_right ih _
       _ = (k + 1) * (∑i in Finset.range k, 1 / (2 * (i:ℝ) + 2)) +
             ((∑i in Finset.range k, 1 / (2 * (i:ℝ) + 2)) +
                (k + 2) / (2 * k + 2)) := by
             congr; funext x; rw [add_assoc, show (1:ℝ) + 1 = 2 by norm_num]
       _ = (k + 2) * ((∑i in Finset.range k, 1 / (2 * (i:ℝ) + 2)) +
                1 / (2 * k + 2)) := by ring
       _ = (k + 2) * (∑i in Finset.range k.succ, 1 / (2 * (i:ℝ) + 2))
                 := by rw [←Finset.sum_range_succ]
    norm_cast at this
    norm_cast
