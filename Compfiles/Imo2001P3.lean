/-
Copyright (c) 2024 the Compfiles Contributers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan, David Renshaw
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.NormNum.Ineq

import ProblemExtraction

problem_file {
  tags := [.Combinatorics]
  importedFrom := "https://github.com/leanprover-community/mathlib4/blob/master/Archive/Imo/Imo2001Q3.lean"
}

/-!
# International Mathematical Olympiad 2001, Problem 3

Twenty-one girls and twenty-one boys took part in a mathematical competition.
It turned out that each contestant solved at most six problems, and for each
pair of a girl and a boy, there was at most one problem solved by both the
girl and the boy. Show that there was a problem solved by at least three
girls and at least three boys.
-/

namespace Imo2001P3

open Finset

/-- A problem is easy for a cohort (boys or girls) if at least three
    of its members solved it. -/
def Easy {α : Type} [Fintype α] (F : α → Finset ℕ) (p : ℕ) : Prop := 3 ≤ #{i | p ∈ F i}

snip begin

/-
# Solution
Note that not all of the problems a girl $g$ solves can be "hard" for boys, in the sense that
at most two boys solved it. If that was true, by condition 1 at most $6 × 2 = 12$ boys solved
some problem $g$ solved, but by condition 2 that property holds for all 21 boys, which is a
contradiction.
Hence there are at most 5 problems $g$ solved that are hard for boys, and the number of girl-boy
pairs who solved some problem in common that was hard for boys is at most $5 × 2 × 21 = 210$.
By the same reasoning this bound holds when "girls" and "boys" are swapped throughout, but there
are $21^2$ girl-boy pairs in all and $21^2 > 210 + 210$, so some girl-boy pairs solved only problems
in common that were not hard for girls or boys. By condition 2 the result follows.
-/

open Classical in
/-- Every contestant solved at most five problems that were not easy for the other cohort. -/
lemma card_not_easy_le_five {α β : Type} [Fintype α]
    {β_solved : β → Finset ℕ} {α_solved : α → Finset ℕ}
    (hcard : 21 = Fintype.card α)
    {i : β} (hG : #(β_solved i) ≤ 6) (hB : ∀ j, ¬Disjoint (β_solved i) (α_solved j)) :
    #{p ∈ β_solved i | ¬Easy α_solved p} ≤ 5 := by
  by_contra! h
  replace h := le_antisymm (card_filter_le ..) (hG.trans h)
  simp_rw [card_filter_eq_iff, Easy, not_le] at h
  suffices 21 ≤ 12 by norm_num at this
  calc
    _ = #{j | ¬Disjoint (β_solved i) (α_solved j)} := by simp [filter_true_of_mem fun j _ ↦ hB j]
                                                         exact hcard
    _ = #((β_solved i).biUnion fun p ↦ {j | p ∈ α_solved j}) := by congr 1; ext j; simp [not_disjoint_iff]
    _ ≤ ∑ p ∈ β_solved i, #{j | p ∈ α_solved j}              := card_biUnion_le
    _ ≤ ∑ p ∈ β_solved i, 2                           := sum_le_sum fun p mp ↦ Nat.le_of_lt_succ (h p mp)
    _ ≤ _                                      := by rw [sum_const, smul_eq_mul]; lia

open Classical in
/-- There are at most 210 girl-boy pairs who solved some problem in common that was not easy for
a fixed cohort. -/
lemma card_not_easy_le_210 {α β : Type} [Fintype α] [Fintype β]
    (hcard_α : 21 = Fintype.card α)
    (hcard_β : 21 = Fintype.card β)
    {α_solved : α → Finset ℕ} {β_solved : β → Finset ℕ}
    (hA : ∀ i, #(β_solved i) ≤ 6) (hB : ∀ i j, ¬Disjoint (β_solved i) (α_solved j)) :
    #{ij : β × α | ∃ p, ¬Easy α_solved p ∧ p ∈ β_solved ij.1 ∩ α_solved ij.2} ≤ 210 :=
  calc
    _ = ∑ i, #{j | ∃ p, ¬Easy α_solved p ∧ p ∈ β_solved i ∩ α_solved j} := by
      simp_rw [card_filter, ← univ_product_univ, sum_product]
    _ = ∑ i, #({p ∈ β_solved i | ¬Easy α_solved p}.biUnion fun p ↦ {j | p ∈ α_solved j}) := by
      congr!; ext
      simp_rw [mem_biUnion, mem_inter, mem_filter, mem_univ, true_and]
      grind
    _ ≤ ∑ i, ∑ p ∈ β_solved i with ¬Easy α_solved p, #{j | p ∈ α_solved j} := sum_le_sum fun _ _ ↦ card_biUnion_le
    _ ≤ ∑ i, ∑ p ∈  β_solved i with ¬Easy α_solved p, 2 := by
      gcongr with i _ p mp
      rw [mem_filter, Easy, not_le] at mp
      exact Nat.le_of_lt_succ mp.2
    _ ≤ ∑ i : β, 5 * 2 := by
      gcongr with i
      rw [sum_const, smul_eq_mul]
      exact mul_le_mul_left (card_not_easy_le_five hcard_α (hA _) (hB _)) _
    _ = _ := by simp [←hcard_β]

snip end

problem imo2001_p3
    {Girl Boy : Type}
    [Fintype Girl] [Fintype Boy] [DecidableEq Girl] [DecidableEq Boy]
    {G : Girl → Finset ℕ} {B : Boy → Finset ℕ} -- solved problems
    (hcard_girl : 21 = Fintype.card Girl)
    (hcard_boy : 21 = Fintype.card Boy)
    (G_le_6 : ∀ i, #(G i) ≤ 6) -- Every girl solved at most six problems.
    (B_le_6 : ∀ j, #(B j) ≤ 6) -- Every boy solved at most six problems.
    (G_inter_B : ∀ i j, ¬Disjoint (G i) (B j)) :
    ∃ p, Easy G p ∧ Easy B p := by
  have B_inter_G : ∀ i j, ¬Disjoint (B i) (G j) := fun i j ↦ by
    rw [disjoint_comm]; exact G_inter_B j i
  have cB := card_not_easy_le_210 hcard_boy hcard_girl G_le_6 G_inter_B
  have cG := card_not_easy_le_210 hcard_girl hcard_boy B_le_6 B_inter_G
  rw [← card_map ⟨_, Prod.swap_injective⟩] at cG
  have key := (card_union_le _ _).trans (add_le_add cB cG) |>.trans_lt
    (show _ < #(@univ (Girl × Boy) _) by simp [←hcard_boy, ←hcard_girl])
  obtain ⟨⟨i, j⟩, -, hij⟩ := exists_mem_notMem_of_card_lt_card key
  simp_rw [mem_union, mem_map, mem_filter, mem_univ, Function.Embedding.coeFn_mk, Prod.exists,
    Prod.swap_prod_mk, Prod.mk.injEq, existsAndEq, true_and, and_true, not_or, not_exists,
    not_and', not_not, mem_inter, and_imp] at hij
  obtain ⟨p, pG, pB⟩ := not_disjoint_iff.mp (G_inter_B i j)
  use p, hij.2 _ pB pG, hij.1 _ pG pB

end Imo2001P3
