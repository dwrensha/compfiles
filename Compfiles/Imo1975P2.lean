/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InternLM-MATH LEAN Formalizer v0.1, Shahar Blumentzvaig
-/


import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic
import ProblemExtraction


problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1975, Problem 2

Let a1 < a2 < a3 < ... be positive integers.
Prove that for every i >= 1,
there are infinitely many a_n that can be written in the form a_n = ra_i + sa_j,
with r, s positive integers and j > i.
-/

namespace Imo1975P2

problem imo1975_p2 (a : ℕ → ℤ)
    (apos : ∀ i : ℕ, 0 < a i)
    (ha : ∀ i : ℕ, a i < a (i + 1))
    : ∀ i n0 : ℕ,
      ∃ n, n0 ≤ n ∧
      ∃ r s : ℕ,
      ∃ j : ℕ,
        a n = r * a i + s * a j ∧
        i < j ∧
        0 < r ∧
        0 < s := by
  let b : ℕ → ℕ := fun n => (a n).natAbs
  intro i
  have hn0 : ∀ j, a j ≠ (0 : ℤ) := fun j ↦ (Int.ne_of_lt (apos j)).symm
  intro n0
  have h1 : ∃t:ℕ , ∀ n1:ℕ , ∃ n:ℕ , n > n1 ∧ a i ∣ (a n-t) := by
    by_contra h2
    push_neg at h2

    choose f hf using h2
    let m := Nat.succ (Finset.sup ((List.range (b i)).toFinset) f)
    have h3 : ∀ n>m , ∀ t:ℕ , t < b i → ¬ (a i ∣ a n - t) := by
      intro n1 g t1 r
      have h4 : m > f t1 := by
        have h4' : (Finset.sup (List.range (b i)).toFinset f) >= f t1 := by
          apply Finset.le_sup
          rw[List.mem_toFinset]
          exact List.mem_range.2 r
        exact Nat.lt_add_one_of_le h4'
      have h6 : n1 > f t1 := Nat.lt_trans h4 g
      apply hf t1 n1 h6
    have h4 := h3 (m+1) (Nat.lt_add_one m)
    let t_int := a (m+1) - (a i)*((a (m+1))/(a i))
    let t := t_int.natAbs
    have g : (a i)∣ a (m+1) - (a (m+1) - (a i)*((a (m+1))/(a i))) := by
      simp
    have h5 := h4 t
    have h6 : (a i ∣ a (m + 1) - ↑t) → (t ≥ b i) := by
      contrapose
      intro r
      apply lt_of_not_ge at r
      exact h5 r
    dsimp [t] at h6
    dsimp [t_int] at h6
    have g : (a (m + 1) - a i * (a (m + 1) / a i))≥0 := by
        have r : (a i)*(a (m + 1) / a i) ≤ a (m+1) := Int.mul_ediv_self_le (hn0 i)
        lia
    have h7 : ↑(a (m + 1) - a i * (a (m + 1) / a i)).natAbs = (a (m + 1) - a i * (a (m + 1) / a i)) := Int.natAbs_of_nonneg g
    rw [h7] at h6
    simp only [sub_sub_cancel, dvd_mul_right, ge_iff_le, forall_const] at h6
    unfold b at h6
    have h8 : a (m + 1) - a i * (a (m + 1) / a i) < (a i):= by
      have h8' : a i * (a (m + 1) / a i) + (a i) > a (m + 1) :=  Int.lt_mul_ediv_self_add (apos i)
      lia
    lia
  obtain ⟨t,ht⟩ := h1
  have g := ht (n0+i)
  obtain ⟨k,hk⟩ := g
  rcases hk.right with ⟨x, hx⟩
  have g' := ht k
  obtain ⟨m,hm⟩ := g'
  rcases hm.right with ⟨y, hy⟩
  have g : a m = (y-x)*(a i) + (a k) := by
    calc
          a m   = (a m - t) - (a k - t)+(a k) := by ring
          _   = a i * y - a i * x +(a k)     := by rw [hy, hx]
          _   = (y - x) * a i +(a k)        := by ring
  have rm : n0 ≤ m ∧ ∃ r s j : ℕ, a m = ↑r * a i + ↑s * a j ∧ i < j ∧ 0 < r ∧ 0 < s := by
    have r1 : m ≥ n0 := by lia
    have r2 : ∃ r s j : ℕ, a m = r * a i + s * a j ∧ i < j ∧ 0 < r ∧ 0 < s := by
      have s3 : 0<y-x := by
        have t1 : a k < a m := strictMono_nat_of_lt_succ ha hm.left
        have t2 : a m - t > a k - t :=  add_lt_add_left t1 (-t)
        rw [hy] at t2
        rw [hx] at t2
        have : PosMulStrictMono ℤ := PosMulMono.toPosMulStrictMono
        have t3 := (mul_lt_mul_iff_right₀ (apos i)).mp t2
        exact sub_pos.mpr t3
      have s : a m = (y-x) * a i + 1 * a k ∧ i < k ∧ 0 < (y - x).natAbs ∧ (0 : ℕ)<(1 : ℕ) := by
        lia
      use (y-x).natAbs, 1, k
      have abs_eq : ↑((y - x).natAbs) = y - x := by
        rw [Int.natAbs_of_nonneg (Int.le_of_lt s3)]
      rw [abs_eq]
      exact s
    exact And.intro r1 r2
  use m

end Imo1975P2
