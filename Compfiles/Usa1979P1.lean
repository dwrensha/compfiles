/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongyu Ouyang
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra, .Inequality] }

/-!
# USA Mathematical Olympiad 1979, Problem 1

Determine all non-negative integral solutions $(n_1,n_2,\dots , n_{14})$ if any,
apart from permutations, of the Diophantine Equation $n_1^4+n_2^4+\cdots +n_{14}^4=1599$.
-/

namespace Usa1979P1

determine SolutionSet : Set (Fin 14 → ℕ) := ∅

problem usa1979_p1 : ∀ e, e ∈ SolutionSet ↔
    ∃ p : Equiv.Perm (Fin 14), ∑ x : Fin 14, e (p x) ^ 4 = 1599 := by
  -- solution from
  -- https://artofproblemsolving.com/wiki/index.php/1979_USAMO_Problems/Problem_1
  unfold SolutionSet
  intro e
  constructor
  · simp only [Set.mem_empty_iff_false, false_implies]
  · rintro ⟨p, hp⟩
    rw [Function.Bijective.sum_comp (Equiv.bijective p) (fun x ↦ e x ^ 4)] at hp
    clear p
    apply_fun (· % 16) at hp
    rw [Finset.sum_nat_mod] at hp
    suffices : ∑ i : Fin 14, e i ^ 4 % 16 ≤ 14; omega
    have h1 : ∀ x ∈ Finset.univ, e x ^ 4 % 16 ≤ 1 := fun x _ ↦ by
      rw [Nat.pow_mod]
      mod_cases H : e x % 16 <;> change _ % _ = _ % _ at H <;> rw[H] <;> norm_num
    have h2 := Finset.sum_le_card_nsmul (Finset.univ (α := Fin 14)) (fun i ↦ e i ^4 % 16) 1 h1
    simp only [Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h2
    exact h2

end Usa1979P1
