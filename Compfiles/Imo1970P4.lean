/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Adam Kurkiewicz
-/

import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 1970, Problem 4

Determine the set of all positive integers n with the property that
the set {n, n + 1, n + 2, n + 3, n + 4, n + 5} can be partitioned
into two sets such that the product of the numbers in one set
equals the product of the numbers in the other set.
-/

namespace Imo1970P4

snip begin

/-
There are no such n. Suppose s1 ∪ s2 = {n, ..., n + 5} were such a
partition, with both products equal to P. Then P * P is the product of
all six numbers. If one of the six were divisible by 7, then 7 would
divide P, and hence both s1 and s2 would contain a multiple of 7; but a
window of six consecutive integers cannot contain two distinct multiples
of 7. Hence none of the six is divisible by 7, so their residues mod 7
are six distinct nonzero values, forcing n ≡ 1 (mod 7). But then
P * P ≡ 6! ≡ -1 (mod 7), and -1 is not a square modulo 7.
-/

lemma no_partition {n : ℕ} {s1 s2 : Finset ℕ}
    (partition : s1 ∪ s2 = Finset.Icc n (n + 5))
    (no_dups : s1 ∩ s2 = ∅)
    (eq_prod : ∏ m ∈ s1, m = ∏ m ∈ s2, m) : False := by
  have hsq : (∏ m ∈ s1, m) * (∏ m ∈ s1, m) = ∏ m ∈ Finset.Icc n (n + 5), m := by
    rw [← partition, Finset.prod_union (Finset.disjoint_iff_inter_eq_empty.mpr no_dups),
        eq_prod]
  have h7 : Prime (7 : ℕ) := (by norm_num : Nat.Prime 7).prime
  by_cases hx : ∃ x ∈ Finset.Icc n (n + 5), 7 ∣ x
  · -- One of the six numbers is a multiple of 7. Then 7 divides both
    -- products, so each of s1, s2 contains a multiple of 7, and those two
    -- multiples are distinct: impossible within six consecutive numbers.
    obtain ⟨x, hx_mem, hx_dvd⟩ := hx
    have hx2 : x ∈ s1 ∪ s2 := by rw [partition]; exact hx_mem
    have hP : 7 ∣ ∏ m ∈ s1, m := by
      rcases Finset.mem_union.mp hx2 with h | h
      · exact hx_dvd.trans (Finset.dvd_prod_of_mem _ h)
      · rw [eq_prod]
        exact hx_dvd.trans (Finset.dvd_prod_of_mem _ h)
    obtain ⟨y1, hy1, hd1⟩ := h7.exists_mem_finset_dvd hP
    obtain ⟨y2, hy2, hd2⟩ := h7.exists_mem_finset_dvd (eq_prod ▸ hP)
    have hm1 := Finset.mem_Icc.mp (partition ▸ Finset.mem_union_left s2 hy1)
    have hm2 := Finset.mem_Icc.mp (partition ▸ Finset.mem_union_right s1 hy2)
    have hne : y1 ≠ y2 := fun h => Finset.notMem_empty y1
      (no_dups ▸ Finset.mem_inter.mpr ⟨hy1, h ▸ hy2⟩)
    lia
  · -- None of the six numbers is a multiple of 7.
    push Not at hx
    have hdvd : ∀ k : ℕ, k ≤ 5 → ¬ (7 ∣ (n + k)) := fun k hk =>
      hx (n + k) (Finset.mem_Icc.mpr ⟨Nat.le_add_right n k, by lia⟩)
    have hz : ∀ k : ℕ, k ≤ 5 → (n : ZMod 7) + (k : ZMod 7) ≠ 0 := by
      intro k hk h
      refine hdvd k hk ((ZMod.natCast_eq_zero_iff _ _).mp ?_)
      push_cast
      exact h
    have z0 := hz 0 (by norm_num)
    have z1 := hz 1 (by norm_num)
    have z2 := hz 2 (by norm_num)
    have z3 := hz 3 (by norm_num)
    have z4 := hz 4 (by norm_num)
    have z5 := hz 5 (by norm_num)
    norm_num at z0 z1 z2 z3 z4 z5
    -- the squared product equation, transported to ZMod 7
    have hcast : ((∏ m ∈ s1, m : ℕ) : ZMod 7) * ((∏ m ∈ s1, m : ℕ) : ZMod 7)
        = ∏ m ∈ Finset.Icc n (n + 5), (m : ZMod 7) := by
      rw [← Nat.cast_prod, ← Nat.cast_mul, hsq]
    have hprod : ∏ m ∈ Finset.Icc n (n + 5), (m : ZMod 7)
        = (n : ZMod 7) * ((n : ZMod 7) + 1) * ((n : ZMod 7) + 2) * ((n : ZMod 7) + 3)
          * ((n : ZMod 7) + 4) * ((n : ZMod 7) + 5) := by
      rw [show n + 5 = n + 4 + 1 from rfl, Finset.prod_Icc_succ_top (by lia),
          show n + 4 = n + 3 + 1 from rfl, Finset.prod_Icc_succ_top (by lia),
          show n + 3 = n + 2 + 1 from rfl, Finset.prod_Icc_succ_top (by lia),
          show n + 2 = n + 1 + 1 from rfl, Finset.prod_Icc_succ_top (by lia),
          show n + 1 = n + 0 + 1 from rfl, Finset.prod_Icc_succ_top (by lia),
          show n + 0 = n from rfl, Finset.Icc_self, Finset.prod_singleton]
      push_cast
      ring
    -- six consecutive nonzero residues mod 7 multiply to -1,
    -- and -1 is not a square mod 7
    have key : ∀ a b : ZMod 7, a ≠ 0 → a + 1 ≠ 0 → a + 2 ≠ 0 → a + 3 ≠ 0 →
        a + 4 ≠ 0 → a + 5 ≠ 0 →
        b * b ≠ a * (a + 1) * (a + 2) * (a + 3) * (a + 4) * (a + 5) := by decide
    exact key _ _ z0 z1 z2 z3 z4 z5 (hcast.trans hprod)

snip end

determine SolutionSet : Finset ℕ+ := {}

problem imo1970_p4 (n : ℕ+):
  n ∈ SolutionSet ↔
    ∃ s1 s2 : Finset ℕ,
      s1 ∪ s2 = Finset.Icc n.val (n.val + 5) ∧
      s1 ∩ s2 = ∅ ∧
      ∏ m ∈ s1, m = ∏ m ∈ s2, m := by
  constructor
  · intro h
    exact absurd h (Finset.notMem_empty n)
  · rintro ⟨s1, s2, partition, no_dups, eq_prod⟩
    exact (no_partition partition no_dups eq_prod).elim

end Imo1970P4
