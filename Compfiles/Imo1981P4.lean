/-
Copyright (c) 2026 Constantin Seebach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Constantin Seebach
-/
import Mathlib

import ProblemExtraction

problem_file {
  tags := [.NumberTheory]
}

namespace Imo1981P4

/-!
# International Mathematical Olympiad 1981, Problem 4

(a) For which values of $n>2$ is there a set of $n$ consecutive positive integers such that
the largest number in the set is a divisor of the least common multiple of the remaining $n-1$ numbers?

(b) For which values of $n>2$ is there exactly one set having the stated property?
-/

open Finset

def last_divides_lcm_remaining (n k : ℕ) : Prop := k+n ∣ lcm (Icc (k+1) (k+n-1)) id

snip begin

theorem not_existsUnique_of_not_exists {α : Type} {p : α → Prop} : (¬∃ x, p x) → ¬∃! x, p x := by
  grind only [ExistsUnique]

theorem not_existsUnique_of_exists_ne {α : Type} {p : α → Prop} (a b : α) : p a → p b → a ≠ b → ¬∃! x, p x := by
  grind only [ExistsUnique]


theorem dvd_factorial {n k : ℕ} (h : last_divides_lcm_remaining n k) : k+n ∣ Nat.factorial (n-1) := by
  have := dvd_trans h (lcm_dvd_prod (Icc (k+1) (k+n-1)) id)
  rw [Nat.dvd_iff_mod_eq_zero, prod_nat_mod] at this
  zify at this
  rw [prod_bij (t:=Finset.range (n-1)) (g:=fun x => -(x+1:ℤ) % (↑k + ↑n)) (fun i _ => k+n-i-1), <-prod_int_mod, prod_neg] at this
  · rw [<-Int.dvd_iff_emod_eq_zero] at this
    conv at this =>
      lhs
      norm_cast
    rw [<-ZMod.intCast_zmod_eq_zero_iff_dvd] at this
    simp only [Int.reduceNeg, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, neg_one_pow_mul_eq_zero_iff] at this
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
    rw [Nat.factorial_eq_prod_range_add_one]
    norm_cast at this
  · grind
  · grind
  · intro j hj
    use (n+k-1-j), ?_ <;> grind
  · intro i hi
    rw [Nat.cast_sub, Nat.cast_sub, Nat.cast_add]
    · simp
    · grind only [= mem_Icc]
    · grind only [= mem_Icc]

theorem not_3 : ¬ ∃ k, last_divides_lcm_remaining 3 k := by
  by_contra! c
  let ⟨k, h⟩ := c
  have := dvd_factorial h
  clear h c
  rw [show Nat.factorial (3 - 1) = 2 by rfl] at this
  have := Nat.le_of_dvd (by simp) this
  lia

theorem unique_4 : ∃! k, last_divides_lcm_remaining 4 k := by
  use 2
  and_intros
  · unfold last_divides_lcm_remaining
    decide
  · by_contra! c
    let ⟨k, h, kne⟩ := c
    have hdvd := dvd_factorial h
    clear h c
    rw [show Nat.factorial (4 - 1) = 6 by rfl] at hdvd
    have := Nat.le_of_dvd (by simp) hdvd
    have bd : k ≤ 1 := by lia
    clear this kne
    revert hdvd
    decide +revert

theorem coprime_sub_succ {n d : ℕ} (h : d < n) : Nat.Coprime (n-d) (n-(d+1)) := by
  rw [Nat.sub_succ', Nat.coprime_self_sub_right]
  · simp
  · lia

theorem lcm_sub_succ {n d : ℕ} (h : d < n) : Nat.lcm (n-d) (n-(d+1)) = (n-d)*(n-(d+1)) := by
  refine Nat.Coprime.lcm_eq_mul ?_
  apply coprime_sub_succ h

theorem ge_5 (n d : ℕ) (hge : 5 ≤ n) (hd : d = 1 ∨ d = 2) : last_divides_lcm_remaining n (Nat.lcm (n-d) (n-(d+1)) - n) := by
  rw [lcm_sub_succ (by lia)]
  unfold last_divides_lcm_remaining
  rw [Nat.sub_add_cancel]
  · apply (coprime_sub_succ (by lia)).mul_dvd_of_dvd_of_dvd
    · trans (n-d)*(n-(d+2))
      · simp
      · apply dvd_lcm
        rw [show n - (d + 2) = n - (d + 1) - 1 by lia, Nat.mul_sub _ _ 1, mul_one, mem_Icc]
        and_intros
        · apply Nat.sub_lt_sub_left
          · refine (Nat.lt_mul_iff_one_lt_right ?_).mpr ?_ <;> lia
          · lia
        · apply Nat.sub_le_sub_left
          lia
    · trans (n-(d+1))*(n-(d+1))
      · simp
      · apply dvd_lcm
        nth_rw 3 [show n - (d+1) = n - d - 1 by lia]
        rw [Nat.sub_mul _ 1, one_mul, mem_Icc]
        and_intros
        · apply Nat.sub_lt_sub_left
          · refine (Nat.lt_mul_iff_one_lt_left ?_).mpr ?_ <;> lia
          · lia
        · apply Nat.sub_le_sub_left
          lia
  · zify
    repeat rw [Nat.cast_sub (by lia)]
    rw [sub_mul, mul_sub, mul_sub, <-sub_nonneg]
    apply hd.elim <;> {
      intro _
      subst d
      simp only [Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, one_mul]
      nlinarith
    }

snip end

determine values_a : Set ℕ := Set.Ici 4

determine values_b : Set ℕ := {4}

problem imo1981_p4 (n : ℕ) :
      (n ∈ values_a ↔ 2 < n ∧ ∃  k, last_divides_lcm_remaining n k)
    ∧ (n ∈ values_b ↔ 2 < n ∧ ∃! k, last_divides_lcm_remaining n k) := by
  and_intros
  · unfold values_a
    apply Iff.intro _ (not_imp_not.mp _)
    · intro h
      have : n = 4 ∨ 5 ≤ n := by grind only [= Set.mem_Ici]
      apply this.elim
      · intro h
        subst n
        use (by lia)
        exact unique_4.exists
      · intro h
        use (by lia), ?_
        exact (ge_5 n 1 h (by simp))
    · simp only [not_and]
      intro _ _
      have : n = 3 := by grind
      subst n
      exact not_3
  · unfold values_b
    apply Iff.intro _ (not_imp_not.mp _)
    · simp only [Set.mem_singleton_iff]
      intro h
      subst n
      simp [unique_4]
    · simp only [Set.mem_singleton_iff, not_and]
      intro h1 h2
      have : n = 3 ∨ 5 ≤ n := by lia
      apply this.elim
      · intro h
        subst n
        apply not_existsUnique_of_not_exists not_3
      · intro h
        apply not_existsUnique_of_exists_ne _ _ (ge_5 n 1 h (by simp)) (ge_5 n 2 h (by simp))
        repeat rw [lcm_sub_succ (by lia)]
        simp
        zify
        rw [Nat.cast_sub, Nat.cast_sub, mul_comm]
        · simp
          omega
        · zify
          repeat rw [Nat.cast_sub (by lia)]
          rw [sub_mul, mul_sub, mul_sub, <-sub_nonneg]
          simp
          nlinarith
        · zify
          repeat rw [Nat.cast_sub (by lia)]
          rw [sub_mul, mul_sub, mul_sub, <-sub_nonneg]
          simp
          nlinarith


end Imo1981P4
