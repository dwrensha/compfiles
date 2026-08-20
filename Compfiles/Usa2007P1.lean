/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 2007, Problem 1

Let n be a positive integer. Define a sequence by setting a₁ = n and,
for each k > 1, letting aₖ be the unique integer in the range 0 ≤ aₖ ≤ k - 1
for which a₁ + a₂ + ··· + aₖ is divisible by k. (For instance, when n = 9
the obtained sequence is 9, 1, 2, 0, 3, 3, 3, ....)
Prove that for any n the sequence a₁, a₂, ... eventually becomes constant.
-/

namespace Usa2007P1

/-- The partial sums `s n k = a n 0 + a n 1 + ... + a n k` of the sequence of the
problem, defined directly: `s n 0 = n`, and `s n (k + 1)` is the smallest multiple
of `k + 2` which is `≥ s n k`. -/
def s (n : ℕ) : ℕ → ℕ
  | 0 => n
  | (k + 1) => s n k + (k + 2 - s n k % (k + 2)) % (k + 2)

/-- The sequence of the problem, with indices shifted by one so that `a n 0 = n`:
for `k ≥ 1`, `a n k` is the unique integer in `[0, k]` for which `k + 1` divides
`s n k = a n 0 + ... + a n k`. -/
def a (n : ℕ) : ℕ → ℕ
  | 0 => n
  | (k + 1) => s n (k + 1) - s n k

snip begin

-- sanity check against the example given in the problem statement
example : a 9 0 = 9 ∧ a 9 1 = 1 ∧ a 9 2 = 2 ∧ a 9 3 = 0 ∧ a 9 4 = 3 ∧
    a 9 5 = 3 ∧ a 9 6 = 3 := by
  decide

lemma s_succ (n k : ℕ) :
    s n (k + 1) = s n k + (k + 2 - s n k % (k + 2)) % (k + 2) := rfl

lemma a_succ (n k : ℕ) :
    a n (k + 1) = (k + 2 - s n k % (k + 2)) % (k + 2) :=
  Nat.add_sub_cancel_left _ _

lemma s_succ_eq_add_a (n k : ℕ) : s n (k + 1) = s n k + a n (k + 1) := by
  rw [a_succ, s_succ]

lemma a_succ_lt (n k : ℕ) : a n (k + 1) < k + 2 := by
  rw [a_succ]
  exact Nat.mod_lt _ (by lia)

lemma dvd_s (n k : ℕ) : (k + 1) ∣ s n k := by
  induction k with
  | zero => exact one_dvd n
  | succ k _ =>
      rw [Nat.dvd_iff_mod_eq_zero, s_succ, Nat.add_mod, Nat.mod_mod]
      generalize hr : s n k % (k + 2) = r
      have hrl : r < k + 2 := by rw [← hr]; exact Nat.mod_lt _ (by lia)
      rcases Nat.eq_zero_or_pos r with h0 | hpos
      · rw [h0]
        simp
      · rw [Nat.mod_eq_of_lt (by lia : k + 2 - r < k + 2),
            show r + (k + 2 - r) = k + 2 by lia]
        exact Nat.mod_self _

/-- The average `b n k = (a n 0 + ... + a n k) / (k + 1)`, a nonnegative integer. -/
def b (n k : ℕ) : ℕ := s n k / (k + 1)

lemma s_eq (n k : ℕ) : s n k = (k + 1) * b n k := by
  show s n k = (k + 1) * (s n k / (k + 1))
  rw [mul_comm, Nat.div_mul_cancel (dvd_s n k)]

lemma b_succ_le (n k : ℕ) : b n (k + 1) ≤ b n k := by
  have h2 : s n (k + 1) = s n k + a n (k + 1) := s_succ_eq_add_a n k
  have h4 : a n (k + 1) < k + 2 := a_succ_lt n k
  have h5 : s n k = (k + 1) * b n k := s_eq n k
  have h6 : s n (k + 1) = (k + 2) * b n (k + 1) := s_eq n (k + 1)
  by_contra hlt
  have hlt' : b n k + 1 ≤ b n (k + 1) := not_le.mp hlt
  have h7 : (k + 2) * (b n k + 1) ≤ (k + 2) * b n (k + 1) :=
    Nat.mul_le_mul_left _ hlt'
  rw [show (k + 2) * (b n k + 1) = (k + 1) * b n k + b n k + (k + 2) by ring] at h7
  lia

lemma b_eventually_const (n : ℕ) : ∃ N, ∀ k ≥ N, b n k = b n N := by
  have hb : Antitone (b n) := antitone_nat_of_succ_le (b_succ_le n)
  obtain ⟨N, hN⟩ := Nat.sInf_mem (Set.range_nonempty (b n))
  refine ⟨N, fun k hk => le_antisymm (hb hk) ?_⟩
  rw [hN]
  exact Nat.sInf_le ⟨k, rfl⟩

/-- The partial sums of `a n` are indeed given by `s n`. -/
lemma sum_a (n k : ℕ) : ∑ i ∈ Finset.range (k + 1), a n i = s n k := by
  induction k with
  | zero => rw [Finset.sum_range_one]; rfl
  | succ k ih =>
      rw [Finset.sum_range_succ, ih, s_succ_eq_add_a]

/-- `a n` satisfies the divisibility requirement of the problem statement. -/
lemma dvd_sum_a (n k : ℕ) : (k + 1) ∣ ∑ i ∈ Finset.range (k + 1), a n i := by
  rw [sum_a]
  exact dvd_s n k

/-- `a n` satisfies the range requirement of the problem statement. -/
lemma a_le (n : ℕ) {k : ℕ} (hk : 1 ≤ k) : a n k ≤ k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by lia)
  exact Nat.lt_succ_iff.mp (a_succ_lt n j)

snip end

problem usa2007_p1 (n : ℕ) (_hn : 0 < n) :
    ∃ c N, ∀ k ≥ N, a n k = c := by
  obtain ⟨N, hN⟩ := b_eventually_const n
  refine ⟨b n N, N + 1, fun k hk => ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by lia)
  have e1 : s n (j + 1) = (j + 2) * b n N := by
    rw [s_eq, hN (j + 1) (by lia)]
  have e2 : s n j = (j + 1) * b n N := by
    rw [s_eq, hN j (by lia)]
  calc a n (j + 1) = s n (j + 1) - s n j := rfl
    _ = (j + 2) * b n N - (j + 1) * b n N := by rw [e1, e2]
    _ = b n N := by
          have h8 : (j + 2) * b n N = (j + 1) * b n N + b n N := by ring
          lia

end Usa2007P1
