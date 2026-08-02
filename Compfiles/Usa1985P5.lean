/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.BigOperators
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 1985, Problem 5

0 < a₁ ≤ a₂ ≤ a₃ ≤ ⋯ is an unbounded sequence of integers. Let bₙ = m if aₘ is the
first member of the sequence to equal or exceed n. Given that a₁₉ = 85, what is the
maximum possible value of a₁ + a₂ + ⋯ + a₁₉ + b₁ + b₂ + ⋯ + b₈₅?
-/

namespace Usa1985P5

/-- The first index `i` (0-based) such that `n ≤ a i`. This exists because `a` is
unbounded. The problem's `bₙ` is `c a hu n + 1` (the 1-based index). -/
noncomputable abbrev c (a : ℕ → ℕ) (hu : ∀ n, ∃ i, n ≤ a i) (n : ℕ) : ℕ :=
  Nat.find (hu n)

snip begin

lemma find_iff {a : ℕ → ℕ} (hm : Monotone a) (hu : ∀ n, ∃ i, n ≤ a i) (i j : ℕ) :
    c a hu j ≤ i ↔ j ≤ a i := by
  constructor
  · intro h
    exact le_trans (Nat.find_spec (hu j)) (hm h)
  · intro h
    exact Nat.find_le h

/-- `∑ j ∈ range 85, (if j < a i then 1 else 0)` counts the elements of `range (a i)`
when `a i ≤ 85`. -/
lemma sum_indicator_left {a : ℕ → ℕ} {i : ℕ} (hi : a i ≤ 85) :
    ∑ j ∈ Finset.range 85, (if j < a i then 1 else 0) = a i := by
  rw [← Finset.card_filter]
  have h : (Finset.range 85).filter (fun j => j < a i) = Finset.range (a i) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨lt_of_lt_of_le h hi, h⟩
  rw [h, Finset.card_range]

/-- `∑ i ∈ range 19, (if i < c a hu (j+1) then 1 else 0)` counts the elements of
`range (c a hu (j+1))` when `c a hu (j+1) ≤ 18`. -/
lemma sum_indicator_right {a : ℕ → ℕ} {hu : ∀ n, ∃ i, n ≤ a i} {j : ℕ}
    (hj : c a hu (j + 1) ≤ 18) :
    ∑ i ∈ Finset.range 19, (if i < c a hu (j + 1) then 1 else 0) = c a hu (j + 1) := by
  rw [← Finset.card_filter]
  have h : (Finset.range 19).filter (fun i => i < c a hu (j + 1)) =
      Finset.range (c a hu (j + 1)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨by have h2 := lt_of_lt_of_le h hj; omega, h⟩
  rw [h, Finset.card_range]

/-- The key identity: the sum is *constant*. Double-count the pairs
`(i, j) ∈ range 19 × range 85`: for each pair, exactly one of
`j < a i` and `i < c a hu (j+1)` holds, so the two indicator sums add up to
`19 * 85`; the extra `+ 1` in each `b` term contributes another `85`. -/
lemma sum_eq (a : ℕ → ℕ) (hm : Monotone a) (hu : ∀ n, ∃ i, n ≤ a i)
    (h19 : a 18 = 85) :
    ∑ i ∈ Finset.range 19, a i + ∑ j ∈ Finset.range 85, (c a hu (j + 1) + 1) = 1700 := by
  have key : ∀ i j : ℕ, i < c a hu (j + 1) ↔ a i ≤ j := by
    intro i j
    rw [← Nat.not_le, find_iff hm hu i (j + 1)]
    exact Iff.trans Nat.not_le Nat.lt_add_one_iff
  have ha85 : ∀ i ∈ Finset.range 19, a i ≤ 85 := by
    intro i hi
    have hi18 : i ≤ 18 := by
      have h := Finset.mem_range.mp hi
      omega
    rw [← h19]
    exact hm hi18
  have hc18 : ∀ j ∈ Finset.range 85, c a hu (j + 1) ≤ 18 := by
    intro j hj
    have hj85 : j + 1 ≤ 85 := by
      have h := Finset.mem_range.mp hj
      omega
    exact Nat.find_le (by rw [h19]; exact hj85)
  have e1 : ∑ i ∈ Finset.range 19, a i
      = ∑ i ∈ Finset.range 19, ∑ j ∈ Finset.range 85, (if j < a i then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact (sum_indicator_left (ha85 i hi)).symm
  have e2 : ∑ j ∈ Finset.range 85, (c a hu (j + 1) + 1)
      = ∑ j ∈ Finset.range 85, ∑ i ∈ Finset.range 19,
          (if i < c a hu (j + 1) then 1 else 0) + 85 := by
    rw [Finset.sum_add_distrib]
    have h1 : ∑ j ∈ Finset.range 85, c a hu (j + 1)
        = ∑ j ∈ Finset.range 85, ∑ i ∈ Finset.range 19,
            (if i < c a hu (j + 1) then 1 else 0) :=
      Finset.sum_congr rfl (fun j hj => (sum_indicator_right (hc18 j hj)).symm)
    have h2 : ∑ j ∈ Finset.range 85, (1 : ℕ) = 85 := by simp
    rw [h1, h2]
  have e3 : ∑ j ∈ Finset.range 85, ∑ i ∈ Finset.range 19,
        (if i < c a hu (j + 1) then 1 else 0)
      = ∑ i ∈ Finset.range 19, ∑ j ∈ Finset.range 85,
          (if i < c a hu (j + 1) then 1 else 0) :=
    Finset.sum_comm
  have e4 : ∀ i ∈ Finset.range 19,
      (∑ j ∈ Finset.range 85, (if j < a i then 1 else 0) : ℕ) +
        ∑ j ∈ Finset.range 85, (if i < c a hu (j + 1) then 1 else 0)
        = ∑ j ∈ Finset.range 85, 1 := by
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : j < a i
    · rw [if_pos h, if_neg (fun hc => Nat.not_le.mpr h ((key i j).mp hc))]
    · rw [if_neg h, if_pos ((key i j).mpr (Nat.le_of_not_lt h))]
  have hsum : (∑ i ∈ Finset.range 19, ∑ j ∈ Finset.range 85, (if j < a i then 1 else 0)) +
        (∑ i ∈ Finset.range 19, ∑ j ∈ Finset.range 85,
          (if i < c a hu (j + 1) then 1 else 0)) = 1615 := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl e4]
    norm_num [Finset.sum_const, Finset.card_range]
  rw [e1, e2, e3, ← add_assoc, hsum]

snip end

determine solution : ℕ := 1700

problem usa1985_p5 :
    IsGreatest { s : ℕ | ∃ (a : ℕ → ℕ) (_ : Monotone a) (_ : 0 < a 0)
        (hu : ∀ n, ∃ i, n ≤ a i), a 18 = 85 ∧
        s = ∑ i ∈ Finset.range 19, a i + ∑ j ∈ Finset.range 85, (c a hu (j + 1) + 1) }
      solution := by
  have hmono : Monotone (fun i => 85 + (i - 18)) := fun i j hij =>
    Nat.add_le_add_left (Nat.sub_le_sub_right hij 18) 85
  have hpos : 0 < (fun i => 85 + (i - 18)) 0 := by decide
  have hunb : ∀ n, ∃ i, n ≤ (fun i => 85 + (i - 18)) i := fun n =>
    ⟨n, by show n ≤ 85 + (n - 18); omega⟩
  have h85 : (fun i => 85 + (i - 18)) 18 = 85 := by decide
  refine ⟨?_, ?_⟩
  · refine ⟨fun i => 85 + (i - 18), hmono, hpos, hunb, h85, ?_⟩
    exact (sum_eq (fun i => 85 + (i - 18)) hmono hunb h85).symm
  · intro s hs
    obtain ⟨a, hm, hp, hu, h19, hs⟩ := hs
    rw [hs]
    exact le_of_eq (sum_eq a hm hu h19)

end Usa1985P5
