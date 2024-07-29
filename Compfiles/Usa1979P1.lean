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

/--
A type representing assignments to the variables $n_1$, $n_2$, ..., $n_{14}$,
quotiented by permutations of indices.
-/
structure MultisetNatOfLen14 where
  s : Multiset ℕ
  p : Multiset.card s = 14

determine SolutionSet : Set MultisetNatOfLen14 := ∅

problem usa1979_p1 : ∀ e, e ∈ SolutionSet ↔ (e.s.map (fun x ↦ x ^ 4)).sum = 1599 := by
  -- solution from
  -- https://artofproblemsolving.com/wiki/index.php/1979_USAMO_Problems/Problem_1
  unfold SolutionSet
  intro e
  constructor
  · simp only [Set.mem_empty_iff_false, false_implies]
  · intro contra
    apply_fun (· % 16) at contra
    rw [Multiset.sum_nat_mod, Multiset.map_map] at contra
    simp only [Function.comp_apply, Nat.reduceMod] at contra
    suffices : (Multiset.map (fun x ↦ x ^ 4 % 16) e.s).sum ≤ 14; omega
    rw [show 14 = Multiset.card (e.s.map (fun x ↦ x ^ 4 % 16)) * 1 by rw [Multiset.card_map, e.p]]
    apply Multiset.sum_le_card_nsmul
    intro x
    rw [Multiset.mem_map]
    intro ⟨i, ⟨_, h⟩⟩
    rw [← h, Nat.pow_mod]
    mod_cases i % 16
    all_goals rw [H]; try norm_num

end Usa1979P1
