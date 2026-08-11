/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Fable 5, via Claude Code), Kimi K3
-/

module

public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics, .Inequality] }

/-!
# International Mathematical Olympiad 1997, Problem 6

For each positive integer n, let f(n) denote the number of ways of representing n
as a sum of powers of 2 with non-negative integer exponents. Representations
which differ only in the ordering of their summands are considered to be the
same. For example, f(4) = 4, because 4 can be represented as 4, 2 + 2, 2 + 1 + 1
or 1 + 1 + 1 + 1. Prove that for any integer n ≥ 3,
2^(n²/4) < f(2^n) < 2^(n²/2).
-/

namespace Imo1997P6

/-- `f n` is the number of ways of representing `n` as a sum of powers of two
with non-negative integer exponents, where representations that differ only in
the order of their summands are considered the same. Rather than defining `f`
as a cardinality, we define it directly through its classical recurrence:
a representation of an odd number `2m + 1` must use a `1`, hence
`f (2m + 1) = f (2m)`; a representation of `2m + 2` either uses a `1` (and
deleting it gives a representation of `2m + 1`) or does not (and halving every
summand gives a representation of `m + 1`), hence
`f (2m + 2) = f (2m + 1) + f (m + 1)`. -/
def f : ℕ → ℕ
  | 0 => 1
  | n + 1 => f n + if (n + 1) % 2 = 0 then f ((n + 1) / 2) else 0
termination_by n => n
decreasing_by all_goals omega

snip begin

/-- Unfolding equation for the recursive definition. -/
lemma f_succ (n : ℕ) :
    f (n + 1) = f n + if (n + 1) % 2 = 0 then f ((n + 1) / 2) else 0 := by
  simp only [f]

/-- A representation of an odd number must contain a `1`. -/
lemma f_odd (m : ℕ) : f (2 * m + 1) = f (2 * m) := by
  rw [f_succ (2 * m), if_neg (by omega), add_zero]

/-- The recurrence at even arguments. -/
lemma f_even (m : ℕ) : f (2 * m + 2) = f (2 * m + 1) + f (m + 1) := by
  rw [f_succ, add_assoc, Nat.add_mod_right, Nat.mul_mod_right, if_pos rfl]
  congr
  omega

/-- The recurrence at even arguments, shifted form. -/
lemma f_even' (m : ℕ) (hm : 1 ≤ m) : f (2 * m) = f (2 * m - 1) + f m := by
  convert f_even (m - 1) <;> lia

lemma f_zero : f 0 = 1 := by simp only [f]

lemma f_one : f 1 = 1 := by
  show f (2 * 0 + 1) = 1
  rw [f_odd 0]
  exact f_zero

lemma f_two : f 2 = 2 := by
  show f (2 * 0 + 2) = 2
  rw [f_even 0]
  show f 1 + f 1 = 2
  rw [f_one]

lemma f_three : f 3 = 2 := by
  show f (2 * 1 + 1) = 2
  rw [f_odd 1]
  exact f_two

lemma f_four : f 4 = 4 := by
  show f (2 * 1 + 2) = 4
  rw [f_even 1]
  show f 3 + f 2 = 4
  rw [f_three, f_two]

/-- `f` is monotone nondecreasing. -/
lemma f_mono : Monotone f := by
  refine monotone_nat_of_le_succ fun n => ?_
  rw [f_succ n]
  exact Nat.le_add_right _ _

/-- Iterating the recurrence gives `f (2N)` as a sum of values of `f`. -/
lemma f_sum (N : ℕ) : f (2 * N) = ∑ i ∈ Finset.range (N + 1), f i := by
  induction N with
  | zero => simp [f_zero]
  | succ N ih =>
    rw [mul_add, mul_one, f_even N, f_odd N, ih]
    conv_rhs => rw [Finset.sum_range_succ]

/-- The upper-bound engine: `f (2m)` is strictly less than `(m + 1) * f m`
as soon as `m ≥ 2` (the term `f 0 = 1 < f m` makes the inequality strict). -/
lemma f_two_mul_lt (m : ℕ) (hm : 2 ≤ m) : f (2 * m) < (m + 1) * f m := by
  have hconst : (m + 1) * f m = ∑ i ∈ Finset.range (m + 1), f m := by
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  rw [f_sum m, hconst]
  refine Finset.sum_lt_sum (fun i hi => f_mono (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
    ⟨0, by simp, ?_⟩
  have h1 : f 2 ≤ f m := f_mono hm
  have h2 : f 0 = 1 := f_zero
  have h3 : f 2 = 2 := f_two
  omega

/-- The key pairing inequality for the lower bound: the pairs
`f k + f (2r + 1 - k)` are nonincreasing in `k` for `1 ≤ k ≤ r`. -/
lemma f_pair_step (r k : ℕ) (hk : 1 ≤ k) (hkr : k < r) :
    f (k + 1) + f (2 * r - k) ≤ f k + f (2 * r + 1 - k) := by
  rcases Nat.even_or_odd k with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [← two_mul t, f_odd t,
      show 2 * r + 1 - 2 * t = 2 * (r - t) + 1 by lia,
      ← Nat.mul_sub, f_odd (r - t)]
  · rw [f_even t, Nat.add_sub_add_right, Nat.sub_add_eq, ← Nat.mul_sub, f_even' (r - t) (by lia)]
    have hle : f (t + 1) ≤ f (r - t) := f_mono (by lia)
    omega

/-- Every pair in the sum is at least `2 * f r`. -/
lemma f_pair_ge (r k : ℕ) (hk : 1 ≤ k) (hkr : k ≤ r) :
    2 * f r ≤ f k + f (2 * r + 1 - k) := by
  have key : ∀ j, j ≤ r - 1 → 2 * f r ≤ f (r - j) + f (2 * r + 1 - (r - j)) := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [Nat.sub_zero, Nat.sub_add_comm <| Nat.le_mul_of_pos_left _ zero_lt_two, two_mul r, Nat.add_sub_self_right]
      rw [two_mul, Nat.add_le_add_iff_left]
      exact f_mono <| Nat.le_add_right r 1
    | succ j ih =>
      intro hj
      have step := f_pair_step r (r - (j + 1)) (by omega) (by omega)
      have : 1 ≤ r - j := by lia
      calc
        2 * f r
        _ ≤ f (r - j) + f (2 * r + 1 - (r - j)) := ih <| Nat.le_of_succ_le hj
        _ ≤ f (r - (j + 1)) + f (2 * r + 1 - (r - (j + 1))) := by
          rwa [Nat.sub_add_eq, Nat.sub_add_cancel this, Nat.sub_sub_right (2 * r) this] at step
  rw [← Nat.sub_sub_self hkr]
  exact key (r - k) <| Nat.sub_le_sub_left hk r

/-- The lemma `f 1 + f 2 + ... + f (2r) ≥ 2r * f r` of the official solution. -/
lemma f_sum_pair (r : ℕ) (hr : 1 ≤ r) :
    2 * r * f r ≤ ∑ i ∈ Finset.range (2 * r), f (i + 1) := by
  have split : ∑ i ∈ Finset.range (2 * r), f (i + 1)
      = ∑ i ∈ Finset.range r, f (i + 1) + ∑ i ∈ Finset.range r, f (r + i + 1) := by
    rw [two_mul, Finset.sum_range_add]
  have hrefl : ∑ i ∈ Finset.range r, f (r + i + 1) = ∑ i ∈ Finset.range r, f (2 * r - i) := by
    conv_lhs => rw [← Finset.sum_range_reflect (fun j => f (r + j + 1)) r]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < r := Finset.mem_range.mp hi
    congr 1
    omega
  rw [split, hrefl, ← Finset.sum_add_distrib]
  have hconst : 2 * r * f r = ∑ i ∈ Finset.range r, 2 * f r := by
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    ring
  rw [hconst]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i < r := Finset.mem_range.mp hi
  have h := f_pair_ge r (i + 1) (by omega) (by omega)
  rwa [Nat.add_sub_add_right] at h

/-- The two-step lower-bound recurrence: `f (2^(n+1)) > 2^n * f (2^(n-1))`. -/
lemma f_lower_step (n : ℕ) (hn : 1 ≤ n) :
    2 ^ n * f (2 ^ (n - 1)) < f (2 ^ (n + 1)) := by
  have hsum : f (2 ^ (n + 1)) = ∑ i ∈ Finset.range (2 ^ n + 1), f i := by
    have h := f_sum (2 ^ n)
    rwa [mul_comm (2 : ℕ) (2 ^ n), ← pow_succ] at h
  rw [Finset.sum_range_succ'] at hsum
  have hpair := f_sum_pair (2 ^ (n - 1)) Nat.one_le_two_pow
  have e2 : 2 * 2 ^ (n - 1) = 2 ^ n := by
    conv_rhs => rw [← Nat.sub_add_cancel hn]
    rw [pow_succ, mul_comm]
  rw [e2] at hpair
  have hf0 : f 0 = 1 := f_zero
  omega

/-- The lower bound in integer form: `(f (2^n))^4 > 2^(n²)`, proved by
two-step induction; note `4 * (n + 2) + (n + 1)² = (n + 3)²`. -/
lemma f_lower_main (n : ℕ) (hn : 1 ≤ n) : 2 ^ (n ^ 2) < (f (2 ^ n)) ^ 4 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | _ | n
    · omega
    · norm_num [f_two]
    · norm_num [f_four]
    · have ihn := ih (n + 1) (by omega) (by omega)
      have step := f_lower_step (n + 2) (by omega)
      rw [Nat.add_succ_sub_one, add_assoc] at step
      calc
        2 ^ (n + 3) ^ 2
        _ = 2 ^ (4 * (n + 2) + (n + 1) ^ 2) := by ring
        _ = 2 ^ (4 * (n + 2)) * 2 ^ ((n + 1) ^ 2) := pow_add 2 _ _
        _ < 2 ^ (4 * (n + 2)) * (f (2 ^ (n + 1))) ^ 4 := by gcongr
        _ = (2 ^ (n + 2) * f (2 ^ (n + 1))) ^ 4 := by rw [mul_pow, ← pow_mul, mul_comm _ 4]
        _ < (f (2 ^ (n + 3))) ^ 4 := Nat.pow_lt_pow_left step (by norm_num)

/-- One step of the upper-bound induction, in squared form. -/
lemma f_sq_step (n : ℕ) (hn : 2 ≤ n) (ih : (f (2 ^ n)) ^ 2 ≤ 2 ^ (n ^ 2)) :
    (f (2 ^ (n + 1))) ^ 2 < 2 ^ ((n + 1) ^ 2) := by
  have h2n : (2 : ℕ) ≤ 2 ^ n := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hstep : f (2 ^ (n + 1)) < (2 ^ n + 1) * f (2 ^ n) := by
    rw [pow_succ, mul_comm (2 ^ n) 2]
    exact f_two_mul_lt (2 ^ n) h2n
  have hsq : (f (2 ^ (n + 1))) ^ 2 < ((2 ^ n + 1) * f (2 ^ n)) ^ 2 :=
    Nat.pow_lt_pow_left hstep (by norm_num)
  have haux : (2 ^ n + 1) ^ 2 ≤ 2 ^ (2 * n + 1) := by
    have e2n : (2 : ℕ) ^ (2 * n) = (2 ^ n) ^ 2 := by rw [mul_comm (2 : ℕ) n, ← pow_mul]
    have en1 : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by ring
    have h1 : 2 ^ (n + 1) + 1 ≤ 2 ^ (2 * n) := by
      calc 2 ^ (n + 1) + 1
          ≤ 2 ^ (n + 1) + 2 ^ (n + 1) := by
            have hpos : (1 : ℕ) ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
            omega
        _ = 2 ^ (n + 2) := by ring
        _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc (2 ^ n + 1) ^ 2
        = 2 ^ (2 * n) + (2 ^ (n + 1) + 1) := by rw [e2n, en1]; ring
      _ ≤ 2 ^ (2 * n) + 2 ^ (2 * n) := by omega
      _ = 2 ^ (2 * n + 1) := by ring
  have key : ((2 ^ n + 1) * f (2 ^ n)) ^ 2 ≤ 2 ^ ((n + 1) ^ 2) := by
    calc ((2 ^ n + 1) * f (2 ^ n)) ^ 2
        = (2 ^ n + 1) ^ 2 * (f (2 ^ n)) ^ 2 := mul_pow _ _ _
      _ ≤ (2 ^ n + 1) ^ 2 * 2 ^ (n ^ 2) := mul_le_mul_right ih _
      _ ≤ 2 ^ (2 * n + 1) * 2 ^ (n ^ 2) := mul_le_mul_left haux _
      _ = 2 ^ (2 * n + 1 + n ^ 2) := (pow_add 2 _ _).symm
      _ = 2 ^ ((n + 1) ^ 2) := by congr 1; ring
  exact lt_of_lt_of_le hsq key

/-- The upper bound in integer form, nonstrict version (for the induction). -/
lemma f_sq_le (n : ℕ) (hn : 2 ≤ n) : (f (2 ^ n)) ^ 2 ≤ 2 ^ (n ^ 2) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [f_four]
  | succ n hn ih => exact le_of_lt (f_sq_step n hn ih)

/-- The upper bound in integer form, strict for `n ≥ 3`. -/
lemma f_sq_lt (n : ℕ) (hn : 3 ≤ n) : (f (2 ^ n)) ^ 2 < 2 ^ (n ^ 2) := by
  have h := f_sq_step (n - 1) (Nat.le_sub_one_of_lt hn) (f_sq_le (n - 1) (Nat.le_sub_one_of_lt hn))
  rwa [Nat.sub_add_cancel (by omega)] at h

/-- The lower bound with real powers: `2^(n²/4) < f (2^n)`. -/
lemma f_gt_lower (n : ℕ) (hn : 3 ≤ n) :
    (2 : ℝ) ^ ((n : ℝ) ^ 2 / 4) < (f (2 ^ n) : ℝ) := by
  have h := f_lower_main n (by omega)
  have hr : (2 : ℝ) ^ (n ^ 2 : ℕ) < (f (2 ^ n) : ℝ) ^ 4 := by exact_mod_cast h
  have hp : ((2 : ℝ) ^ ((n : ℝ) ^ 2 / 4)) ^ 4 = (2 : ℝ) ^ (n ^ 2 : ℕ) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ ((n : ℝ) ^ 2 / 4)) 4,
      ← Real.rpow_natCast (2 : ℝ) (n ^ 2),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    push_cast
    ring
  by_contra hlt
  rw [not_lt] at hlt
  have hle : (f (2 ^ n) : ℝ) ^ 4 ≤ (2 : ℝ) ^ (n ^ 2 : ℕ) := by
    rw [← hp]
    gcongr
  exact (not_lt_of_ge hle) hr

/-- The upper bound with real powers: `f (2^n) < 2^(n²/2)`. -/
lemma f_lt_upper (n : ℕ) (hn : 3 ≤ n) :
    (f (2 ^ n) : ℝ) < (2 : ℝ) ^ ((n : ℝ) ^ 2 / 2) := by
  have h := f_sq_lt n hn
  have hr : (f (2 ^ n) : ℝ) ^ 2 < (2 : ℝ) ^ (n ^ 2 : ℕ) := by exact_mod_cast h
  have hp : ((2 : ℝ) ^ ((n : ℝ) ^ 2 / 2)) ^ 2 = (2 : ℝ) ^ (n ^ 2 : ℕ) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ ((n : ℝ) ^ 2 / 2)) 2,
      ← Real.rpow_natCast (2 : ℝ) (n ^ 2),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    push_cast
    ring
  by_contra hlt
  rw [not_lt] at hlt
  have hle : (2 : ℝ) ^ (n ^ 2 : ℕ) ≤ (f (2 ^ n) : ℝ) ^ 2 := by
    rw [← hp]
    gcongr
  exact (not_lt_of_ge hle) hr

snip end

problem imo1997_p6 (n : ℕ) (hn : 3 ≤ n) :
    (2 : ℝ) ^ ((n : ℝ) ^ 2 / 4) < (f (2 ^ n) : ℝ) ∧
      (f (2 ^ n) : ℝ) < (2 : ℝ) ^ ((n : ℝ) ^ 2 / 2) :=
  ⟨f_gt_lower n hn, f_lt_upper n hn⟩
