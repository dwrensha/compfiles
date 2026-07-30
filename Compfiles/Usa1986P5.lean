/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 1986, Problem 5

A partition of n is an increasing sequence of integers with sum n.
For example, the partitions of 5 are: 1, 1, 1, 1, 1; 1, 1, 1, 2; 1, 1, 3;
1, 4; 5; 1, 2, 2; and 2, 3. If p is a partition, f(p) = the number of 1s
in p, and g(p) = the number of distinct integers in the partition.
Show that ∑ f(p) = ∑ g(p), where the sum is taken over all partitions of n.
-/

namespace Usa1986P5

snip begin

/-- The number of partitions of `n`. -/
abbrev numPartitions (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

/-- The partitions of `n` containing `m` as a part are in bijection with the
partitions of `n - m` (erase one occurrence of `m`), so there are
`numPartitions (n - m)` of them. -/
lemma card_partitions_containing (n m : ℕ) (h1 : 1 ≤ m) (h2 : m ≤ n) :
    Fintype.card { p : Nat.Partition n // m ∈ p.parts } = numPartitions (n - m) :=
  Fintype.card_congr (Nat.Partition.partitionWithPartEquiv h1 h2)

/-- `∑ f(p)`, where `f(p)` is the number of `1`s in `p`, satisfies the recurrence
`F(n + 1) = F(n) + π(n)`: erasing a `1` is a bijection between the partitions of
`n + 1` that contain a `1` and the partitions of `n`, and partitions of `n + 1`
with no `1` contribute nothing to the sum. -/
lemma sum_count_one_succ (n : ℕ) :
    ∑ p : Nat.Partition (n + 1), p.parts.count 1 =
      ∑ p : Nat.Partition n, p.parts.count 1 + numPartitions n := by
  classical
  have hsplit :
      (∑ p : Nat.Partition (n + 1), p.parts.count 1) =
        (∑ p : { p : Nat.Partition (n + 1) // 1 ∈ p.parts }, p.1.parts.count 1) +
          ∑ p : { p : Nat.Partition (n + 1) // ¬ 1 ∈ p.parts }, p.1.parts.count 1 :=
    (Fintype.sum_subtype_add_sum_subtype
      (fun p : Nat.Partition (n + 1) => 1 ∈ p.parts)
      (fun p : Nat.Partition (n + 1) => p.parts.count 1)).symm
  have hzero :
      (∑ p : { p : Nat.Partition (n + 1) // ¬ 1 ∈ p.parts }, p.1.parts.count 1) = 0 := by
    refine Finset.sum_eq_zero fun p _ => ?_
    exact Multiset.count_eq_zero.mpr p.2
  rw [hsplit, hzero, add_zero]
  -- transport the sum over partitions containing `1` to a sum over all partitions of `n`
  let e : { p : Nat.Partition (n + 1) // 1 ∈ p.parts } ≃ Nat.Partition n :=
    Nat.Partition.partitionWithPartEquiv (n := n + 1) (a := 1) (le_refl 1)
      (Nat.le_add_left 1 n)
  rw [← Equiv.sum_comp e.symm
    (fun p : { p : Nat.Partition (n + 1) // 1 ∈ p.parts } => p.1.parts.count 1)]
  have hcount : ∀ q : Nat.Partition n,
      ((e.symm q).1.parts.count 1 : ℕ) = q.parts.count 1 + 1 := fun q => by
    show Multiset.count 1 (((Nat.Partition.partitionWithPartEquiv (n := n + 1) (a := 1)
      (le_refl 1) (Nat.le_add_left 1 n)).symm q).1.parts) = _
    rw [Nat.Partition.partitionWithPartEquiv_symm_apply_parts]
    exact Multiset.count_cons_self 1 q.parts
  rw [Finset.sum_congr rfl fun q _ => hcount q, Finset.sum_add_distrib]
  congr 1
  simp [numPartitions]

/-- Summing the number of `1`s over all partitions of `n` gives
`π(0) + π(1) + ⋯ + π(n - 1)`. -/
lemma sum_count_one (n : ℕ) :
    ∑ p : Nat.Partition n, p.parts.count 1 =
      ∑ k ∈ Finset.range n, numPartitions k := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_count_one_succ, ih, Finset.sum_range_succ]

/-- Summing the number of distinct parts over all partitions of `n` also gives
`π(0) + π(1) + ⋯ + π(n - 1)`: count the pairs `(p, m)` with `m ∈ p` in two ways. -/
lemma sum_distinct_parts (n : ℕ) :
    ∑ p : Nat.Partition n, p.parts.toFinset.card =
      ∑ k ∈ Finset.range n, numPartitions k := by
  classical
  -- the number of distinct parts of `p`, as a sum of indicators over all possible parts
  have hcard : ∀ p : Nat.Partition n, p.parts.toFinset.card =
      ∑ m ∈ Finset.Ico 1 (n + 1), if m ∈ p.parts then 1 else 0 := by
    intro p
    have hsub : p.parts.toFinset ⊆ Finset.Ico 1 (n + 1) := by
      intro m hm
      rw [Multiset.mem_toFinset] at hm
      rw [Finset.mem_Ico]
      have hpos := p.parts_pos hm
      have hle := Nat.Partition.le_of_mem_parts (p := p) hm
      omega
    rw [Finset.card_eq_sum_ite hsub]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [Multiset.mem_toFinset]
  rw [Finset.sum_congr rfl fun p _ => hcard p, Finset.sum_comm]
  -- for each fixed part `m`, count the partitions containing it
  have hstep : ∀ m ∈ Finset.Ico 1 (n + 1),
      (∑ p : Nat.Partition n, if m ∈ p.parts then 1 else 0) = numPartitions (n - m) := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    rw [Finset.sum_boole, Nat.cast_id, ← Fintype.card_subtype]
    exact card_partitions_containing n m hm.1 (Nat.lt_succ_iff.mp hm.2)
  rw [Finset.sum_congr rfl hstep, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  -- reindex: `∑ k < n, π (n - (1 + k)) = ∑ k < n, π (n - 1 - k) = ∑ k < n, π k`
  have hshift : (∑ k ∈ Finset.range n, numPartitions (n - (1 + k))) =
      ∑ k ∈ Finset.range n, numPartitions (n - 1 - k) :=
    Finset.sum_congr rfl fun k _ => by rw [← Nat.sub_sub]
  rw [hshift]
  exact Finset.sum_range_reflect numPartitions n

snip end

problem usa1986_p5 (n : ℕ) :
    ∑ p : Nat.Partition n, p.parts.count 1 =
      ∑ p : Nat.Partition n, p.parts.toFinset.card := by
  rw [sum_count_one, sum_distinct_parts]

end Usa1986P5
