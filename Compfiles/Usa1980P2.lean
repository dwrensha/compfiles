/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 1980, Problem 2

Find the maximum possible number of three term arithmetic progressions
in a monotone sequence of n distinct reals.
-/

namespace Usa1980P2

open Finset

/-!
### Formalization notes

A monotone sequence of *distinct* reals is strictly monotone, and reversing a strictly
decreasing sequence gives a strictly increasing one with the same number of three-term
arithmetic progressions, so we only consider sequences `a : ℕ → ℝ` that are strictly
increasing on `Set.Iio n`.  Three indices `i < j < k` form an arithmetic progression
iff `a i + a k = 2 * a j`, and we count the progressions by their middle index `j`.
-/

snip begin

open Classical in
/-- For a sequence `a : ℕ → ℝ` and an index `j`, the finset of pairs `(i, k)` with
`i < j < k < n` such that `a i, a j, a k` forms a three-term arithmetic progression.
Every three-term arithmetic progression with indices below `n` corresponds to exactly
one such pair, with `j` its middle index. -/
noncomputable def apPairs (n : ℕ) (a : ℕ → ℝ) (j : ℕ) : Finset (ℕ × ℕ) :=
  ((range j) ×ˢ (Ioo j n)).filter fun p => a p.1 + a p.2 = 2 * a j

open Classical in
/-- The number of three-term arithmetic progressions among the first `n` terms of `a`,
counted by their middle index. -/
noncomputable def apCount (n : ℕ) (a : ℕ → ℝ) : ℕ :=
  ∑ j ∈ range n, (apPairs n a j).card

theorem mem_apPairs {n : ℕ} {a : ℕ → ℝ} {j : ℕ} {p : ℕ × ℕ} :
    p ∈ apPairs n a j ↔ p.1 < j ∧ j < p.2 ∧ p.2 < n ∧ a p.1 + a p.2 = 2 * a j := by
  classical
  simp only [apPairs, mem_filter, mem_product, mem_range, mem_Ioo]
  tauto

/-- A three-term progression is determined by its middle term together with any one of
its other two terms, so the number of progressions with middle index `j` is at most
`min j (n - 1 - j)`. -/
theorem card_apPairs_le (n : ℕ) (a : ℕ → ℝ) (ha : StrictMonoOn a (Set.Iio n)) (j : ℕ) :
    (apPairs n a j).card ≤ min j (n - 1 - j) := by
  classical
  refine le_min ?_ ?_
  · have h1 : (apPairs n a j).card ≤ (range j).card := by
      apply Finset.card_le_card_of_injOn Prod.fst
      · intro p hp
        rw [Finset.mem_coe, mem_apPairs] at hp
        exact mem_range.mpr hp.1
      · intro p hp q hq h
        rw [Finset.mem_coe, mem_apPairs] at hp hq
        have e1 : a p.1 + a p.2 = 2 * a j := hp.2.2.2
        have e2 : a q.1 + a q.2 = 2 * a j := hq.2.2.2
        rw [h] at e1
        have h2 : p.2 = q.2 :=
          ha.injOn (Set.mem_Iio.mpr hp.2.2.1) (Set.mem_Iio.mpr hq.2.2.1) (by linarith)
        exact Prod.ext h h2
    rwa [card_range] at h1
  · have h2 : (apPairs n a j).card ≤ (Ioo j n).card := by
      apply Finset.card_le_card_of_injOn Prod.snd
      · intro p hp
        rw [Finset.mem_coe, mem_apPairs] at hp
        exact mem_Ioo.mpr ⟨hp.2.1, hp.2.2.1⟩
      · intro p hp q hq h
        rw [Finset.mem_coe, mem_apPairs] at hp hq
        have e1 : a p.1 + a p.2 = 2 * a j := hp.2.2.2
        have e2 : a q.1 + a q.2 = 2 * a j := hq.2.2.2
        rw [h] at e1
        have h1 : p.1 = q.1 :=
          ha.injOn (Set.mem_Iio.mpr (hp.1.trans (hp.2.1.trans hp.2.2.1)))
            (Set.mem_Iio.mpr (hq.1.trans (hq.2.1.trans hq.2.2.1))) (by linarith)
        exact Prod.ext h1 h
    rwa [Nat.card_Ioo, show n - j - 1 = n - 1 - j by omega] at h2

/-- The per-index bounds telescope in steps of two:
`∑ j < n + 2, min j (n + 1 - j) = ∑ j < n, min j (n - 1 - j) + n`. -/
theorem sum_min_step (n : ℕ) :
    (∑ j ∈ range (n + 2), min j (n + 1 - j)) = (∑ j ∈ range n, min j (n - 1 - j)) + n := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ]
  simp only [Nat.sub_zero, Nat.sub_self, Nat.zero_min, Nat.min_zero, add_zero]
  have term : ∀ j ∈ range n, min (j + 1) (n + 1 - (j + 1)) = min j (n - 1 - j) + 1 := by
    intro j hj
    rw [mem_range] at hj
    have e : n + 1 - (j + 1) = n - 1 - j + 1 := by omega
    rw [e, min_add_add_right]
  rw [sum_congr rfl term, sum_add_distrib]
  simp

/-- Closed form of the total bound: `∑ j < n, min j (n - 1 - j) = (n - 1)² / 4`. -/
theorem sum_min_closed (n : ℕ) : (∑ j ∈ range n, min j (n - 1 - j)) = (n - 1)^2 / 4 := by
  suffices key : ∀ m : ℕ, (∑ j ∈ range m, min j (m - 1 - j)) = (m - 1)^2 / 4 ∧
      (∑ j ∈ range (m + 1), min j (m + 1 - 1 - j)) = (m + 1 - 1)^2 / 4 from (key n).1
  intro m
  induction m with
  | zero => exact ⟨by simp, by simp⟩
  | succ m ih =>
    refine ⟨ih.2, ?_⟩
    show (∑ j ∈ range (m + 2), min j (m + 1 - j)) = (m + 1)^2 / 4
    rw [sum_min_step, ih.1]
    rcases m with _ | k
    · decide
    · simp only [Nat.add_sub_cancel]
      have e : (k + 1 + 1)^2 = k^2 + 4 * k + 4 := by ring
      rw [e]
      omega

/-- The sequence `a i = i` is strictly increasing on `Set.Iio n`. -/
theorem strictMonoOn_cast (n : ℕ) : StrictMonoOn (fun i : ℕ => (i : ℝ)) (Set.Iio n) :=
  (strictMono_nat_of_lt_succ fun i => by exact_mod_cast Nat.lt_succ_self i).strictMonoOn _

/-- Equality holds in `card_apPairs_le` for the sequence `a i = i`: the pairs
`(j - 1 - d, j + 1 + d)` for `d < min j (n - 1 - j)` are distinct elements of
`apPairs n (fun i => (i : ℝ)) j`. -/
theorem card_apPairs_cast (n : ℕ) (j : ℕ) :
    (apPairs n (fun i => (i : ℝ)) j).card = min j (n - 1 - j) := by
  classical
  apply le_antisymm
  · exact card_apPairs_le n _ (strictMonoOn_cast n) j
  · have hinj : (range (min j (n - 1 - j))).card ≤
        (apPairs n (fun i => (i : ℝ)) j).card := by
      apply Finset.card_le_card_of_injOn fun d => (j - 1 - d, j + 1 + d)
      · intro d hd
        rw [Finset.mem_coe, mem_range] at hd
        rw [Finset.mem_coe, mem_apPairs]
        have hd1 : d < j := lt_of_lt_of_le hd (min_le_left _ _)
        have hd2 : d < n - 1 - j := lt_of_lt_of_le hd (min_le_right _ _)
        have hnat : j - 1 - d + (j + 1 + d) = 2 * j := by omega
        have e4 : ((j - 1 - d : ℕ) : ℝ) + ((j + 1 + d : ℕ) : ℝ) = 2 * (j : ℝ) := by
          exact_mod_cast hnat
        show j - 1 - d < j ∧ j < j + 1 + d ∧ j + 1 + d < n ∧
          ((j - 1 - d : ℕ) : ℝ) + ((j + 1 + d : ℕ) : ℝ) = 2 * (j : ℝ)
        exact ⟨by omega, by omega, by omega, e4⟩
      · intro d _ e _ h
        have h2 : j + 1 + d = j + 1 + e := congrArg Prod.snd h
        omega
    rwa [card_range] at hinj

/-- The bound is achieved by the sequence `a i = i`. -/
theorem apCount_cast (n : ℕ) : apCount n (fun i : ℕ => (i : ℝ)) = (n - 1)^2 / 4 := by
  classical
  unfold apCount
  rw [← sum_min_closed n]
  exact sum_congr rfl fun j _ => card_apPairs_cast n j

/-- The bound holds for every strictly increasing sequence. -/
theorem apCount_le (n : ℕ) (a : ℕ → ℝ) (ha : StrictMonoOn a (Set.Iio n)) :
    apCount n a ≤ (n - 1)^2 / 4 := by
  classical
  unfold apCount
  rw [← sum_min_closed n]
  exact sum_le_sum fun j _ => card_apPairs_le n a ha j

snip end

determine answer (n : ℕ) : ℕ := (n - 1)^2 / 4

problem usa1980_p2 (n : ℕ) :
    IsGreatest {m : ℕ | ∃ a : ℕ → ℝ, StrictMonoOn a (Set.Iio n) ∧ m = apCount n a}
      (answer n) := by
  refine ⟨⟨fun i => (i : ℝ), strictMonoOn_cast n, (apCount_cast n).symm⟩, ?_⟩
  rintro m ⟨a, ha, rfl⟩
  exact apCount_le n a ha

end Usa1980P2
