/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 1992, Problem 3

A set of 11 distinct positive integers has the property that we can find a
subset with sum n for any n between 1 and 1500 inclusive. What is the smallest
possible value for the second largest element?
-/

namespace Usa1992P3

snip begin

/--
If the values `a 0, …, a 10` are strictly increasing, then `a` is monotone
on the interval `[0, 10]`.
-/
lemma monotone_of_consec_lt (a : ℕ → ℕ) (h : ∀ i, i < 10 → a i < a (i + 1))
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ 10) : a i ≤ a j := by
  have aux : ∀ k : ℕ, i + k ≤ 10 → a i ≤ a (i + k) := by
    intro k
    induction k with
    | zero => intro; exact le_rfl
    | succ k ih =>
      intro hk
      have h1 := ih (by lia)
      have h2 := h (i + k) (by lia)
      rw [show i + (k + 1) = i + k + 1 by ring]
      exact le_trans h1 (le_of_lt h2)
  have e : i + (j - i) = j := by lia
  have h3 := aux (j - i) (by lia)
  rwa [e] at h3

/--
The key gap lemma: writing `s j` for the sum of the `j` smallest elements,
if `s j < 1500` then the next element satisfies `a j ≤ s j + 1`.
Indeed, `s j + 1 ≤ 1500` must occur as a subset sum, and any subset with
that sum must contain some `a i` with `i ≥ j`, so `a j ≤ a i ≤ s j + 1`.
-/
lemma gap (a : ℕ → ℕ)
    (hsub : ∀ n : ℕ, 1 ≤ n → n ≤ 1500 →
      ∃ t : Finset ℕ, t ⊆ Finset.range 11 ∧ ∑ i ∈ t, a i = n)
    (hmono : ∀ {i j : ℕ}, i ≤ j → j ≤ 10 → a i ≤ a j)
    {j : ℕ} (_hj : j ≤ 10)
    (hs : ∑ i ∈ Finset.range j, a i < 1500) :
    a j ≤ ∑ i ∈ Finset.range j, a i + 1 := by
  obtain ⟨t, ht, htsum⟩ :=
    hsub (∑ i ∈ Finset.range j, a i + 1) (by lia) (by lia)
  by_contra hcon
  push Not at hcon
  have hlt : ∀ i ∈ t, i < j := by
    intro i hi
    by_contra hij
    push Not at hij
    have hi10 : i ≤ 10 := by
      have h11 : i < 11 := Finset.mem_range.mp (ht hi)
      lia
    have hge : a j ≤ a i := hmono hij hi10
    have hle : a i ≤ ∑ x ∈ t, a x :=
      Finset.single_le_sum (fun x _ ↦ Nat.zero_le _) hi
    lia
  have htr : t ⊆ Finset.range j := fun i hi ↦ Finset.mem_range.mpr (hlt i hi)
  have hle2 : ∑ i ∈ t, a i ≤ ∑ i ∈ Finset.range j, a i :=
    Finset.sum_le_sum_of_subset htr
  lia

/--
Induction using the gap lemma: the sum of the `k` smallest elements is at
most `2 ^ k - 1`, for every `k ≤ 10`.
-/
lemma pow_bound (a : ℕ → ℕ)
    (hsub : ∀ n : ℕ, 1 ≤ n → n ≤ 1500 →
      ∃ t : Finset ℕ, t ⊆ Finset.range 11 ∧ ∑ i ∈ t, a i = n)
    (hmono : ∀ {i j : ℕ}, i ≤ j → j ≤ 10 → a i ≤ a j) :
    ∀ k : ℕ, k ≤ 10 → ∑ i ∈ Finset.range k, a i ≤ 2 ^ k - 1 := by
  intro k
  induction k with
  | zero => intro; simp
  | succ k ih =>
    intro hk
    have ih' := ih (by lia)
    have hpow : (2 : ℕ) ^ k ≤ 2 ^ 9 := pow_le_pow_right' (by norm_num) (by lia)
    have hlt : ∑ i ∈ Finset.range k, a i < 1500 := by lia
    have hgap := gap a hsub hmono (j := k) (by lia) hlt
    rw [Finset.sum_range_succ]
    have _ : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := pow_succ' 2 k
    have hX : 0 < (2 : ℕ) ^ k := pow_pos (by norm_num) k
    lia

snip end

/--
Formalization of "a set of 11 distinct positive integers such that every
integer between 1 and 1500 is the sum of a subset", with the elements listed
in increasing order as `a 0 < a 1 < … < a 10`.
-/
def Good (a : ℕ → ℕ) : Prop :=
  (∀ i : ℕ, i < 11 → 0 < a i) ∧
  (∀ i : ℕ, i < 10 → a i < a (i + 1)) ∧
  ∀ n : ℕ, 1 ≤ n → n ≤ 1500 → ∃ t : Finset ℕ, t ⊆ Finset.range 11 ∧ ∑ i ∈ t, a i = n

/-- The answer to the problem. -/
determine answer : ℕ := 248

problem usa1992_p3 : IsLeast {x : ℕ | ∃ a : ℕ → ℕ, Good a ∧ x = a 9} answer := by
  constructor
  · -- `248` is attained by the set `{1,2,4,8,16,32,64,128,247,248,750}`.
    refine ⟨fun i ↦ List.getD [1, 2, 4, 8, 16, 32, 64, 128, 247, 248, 750] i 0,
      ⟨?_, ?_, ?_⟩, rfl⟩
    · decide
    · decide
    · intro n hn1 hn2
      -- Subset sums of the first `k` elements `1, 2, 4, …, 2^(k-1)` cover `[0, 2^k - 1]`.
      have helper : ∀ k : ℕ, k ≤ 8 → ∀ m : ℕ, m ≤ 2 ^ k - 1 →
          ∃ t : Finset ℕ, t ⊆ Finset.range k ∧
            ∑ i ∈ t, List.getD [1, 2, 4, 8, 16, 32, 64, 128, 247, 248, 750] i 0 = m := by
        intro k
        induction k with
        | zero =>
          intro _ m hm
          have hm0 : m = 0 := by
            norm_num at hm
            lia
          exact ⟨∅, by simp, by simp [hm0]⟩
        | succ k ih =>
          intro hk m hm
          have hpow : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := pow_succ' 2 k
          have hpos : 0 < (2 : ℕ) ^ k := pow_pos (by norm_num) k
          by_cases hcase : m ≤ 2 ^ k - 1
          · obtain ⟨t, ht, htsum⟩ := ih (by lia) m hcase
            exact ⟨t, ht.trans (Finset.range_subset_range.mpr (by lia)), htsum⟩
          · push Not at hcase
            have hk7 : k ≤ 7 := by lia
            have hfk : List.getD [1, 2, 4, 8, 16, 32, 64, 128, 247, 248, 750] k 0
                = 2 ^ k := by
              interval_cases k <;> rfl
            obtain ⟨t, ht, htsum⟩ := ih (by lia) (m - 2 ^ k) (by lia)
            have hkt : k ∉ t := fun hmem ↦ by
              have hlt := Finset.mem_range.mp (ht hmem)
              lia
            refine ⟨insert k t, ?_, ?_⟩
            · rw [Finset.insert_subset_iff]
              exact ⟨Finset.mem_range.mpr (by lia),
                ht.trans (Finset.range_subset_range.mpr (by lia))⟩
            · rw [Finset.sum_insert hkt, hfk, htsum]
              lia
      -- Adjoining an element `v ≤ B + 1` extends the covered range from `[0, B]` to
      -- `[0, B + v]`.
      have extend : ∀ (B v j : ℕ), v ≤ B + 1 →
          List.getD [1, 2, 4, 8, 16, 32, 64, 128, 247, 248, 750] j 0 = v →
          (∀ m : ℕ, m ≤ B → ∃ t : Finset ℕ, t ⊆ Finset.range j ∧
            ∑ i ∈ t, List.getD [1, 2, 4, 8, 16, 32, 64, 128, 247, 248, 750] i 0 = m) →
          ∀ m : ℕ, m ≤ B + v → ∃ t : Finset ℕ, t ⊆ Finset.range (j + 1) ∧
            ∑ i ∈ t, List.getD [1, 2, 4, 8, 16, 32, 64, 128, 247, 248, 750] i 0 = m := by
        intro B v j hv hfj cover m hm
        by_cases h : m ≤ B
        · obtain ⟨t, ht, htsum⟩ := cover m h
          exact ⟨t, ht.trans (Finset.range_subset_range.mpr (by lia)), htsum⟩
        · push Not at h
          obtain ⟨t, ht, htsum⟩ := cover (m - v) (by lia)
          have hjt : j ∉ t := fun hmem ↦ by
            have hlt := Finset.mem_range.mp (ht hmem)
            lia
          refine ⟨insert j t, ?_, ?_⟩
          · rw [Finset.insert_subset_iff]
            exact ⟨Finset.mem_range.mpr (by lia),
              ht.trans (Finset.range_subset_range.mpr (by lia))⟩
          · rw [Finset.sum_insert hjt, hfj, htsum]
            lia
      have cover8 : ∀ m : ℕ, m ≤ 255 → ∃ t : Finset ℕ, t ⊆ Finset.range 8 ∧
          ∑ i ∈ t, List.getD [1, 2, 4, 8, 16, 32, 64, 128, 247, 248, 750] i 0 = m :=
        fun m hm ↦ helper 8 (le_refl 8) m (by show m ≤ 255; exact hm)
      have cover9 : ∀ m : ℕ, m ≤ 502 → ∃ t : Finset ℕ, t ⊆ Finset.range 9 ∧
          ∑ i ∈ t, List.getD [1, 2, 4, 8, 16, 32, 64, 128, 247, 248, 750] i 0 = m :=
        fun m hm ↦ extend 255 247 8 (by norm_num) rfl cover8 m hm
      have cover10 : ∀ m : ℕ, m ≤ 750 → ∃ t : Finset ℕ, t ⊆ Finset.range 10 ∧
          ∑ i ∈ t, List.getD [1, 2, 4, 8, 16, 32, 64, 128, 247, 248, 750] i 0 = m :=
        fun m hm ↦ extend 502 248 9 (by norm_num) rfl cover9 m hm
      have cover11 : ∀ m : ℕ, m ≤ 1500 → ∃ t : Finset ℕ, t ⊆ Finset.range 11 ∧
          ∑ i ∈ t, List.getD [1, 2, 4, 8, 16, 32, 64, 128, 247, 248, 750] i 0 = m :=
        fun m hm ↦ extend 750 750 10 (by norm_num) rfl cover10 m hm
      exact cover11 n hn2
  · -- No smaller value of the second largest element is possible.
    intro x hx
    obtain ⟨a, ⟨_hpos, hinc, hsub⟩, rfl⟩ := hx
    have hmono : ∀ {i j : ℕ}, i ≤ j → j ≤ 10 → a i ≤ a j :=
      fun hij hj ↦ monotone_of_consec_lt a hinc hij hj
    have hb := pow_bound a hsub hmono
    have hs8 : ∑ i ∈ Finset.range 8, a i ≤ 255 :=
      le_trans (hb 8 (by norm_num)) (by norm_num)
    obtain ⟨t11, ht11, htsum11⟩ := hsub 1500 (by norm_num) (by norm_num)
    have hs11 : 1500 ≤ ∑ i ∈ Finset.range 11, a i := by
      have hle : ∑ i ∈ t11, a i ≤ ∑ i ∈ Finset.range 11, a i :=
        Finset.sum_le_sum_of_subset ht11
      lia
    have hgap10 : a 10 ≤ ∑ i ∈ Finset.range 10, a i + 1 := by
      have hb10 := hb 10 (by norm_num)
      have h2 : (2 : ℕ) ^ 10 - 1 < 1500 := by norm_num
      exact gap a hsub hmono (by norm_num) (by lia)
    have hs10 : 750 ≤ ∑ i ∈ Finset.range 10, a i := by
      have e11 : ∑ i ∈ Finset.range 11, a i = ∑ i ∈ Finset.range 10, a i + a 10 :=
        Finset.sum_range_succ _ _
      lia
    have e10 : ∑ i ∈ Finset.range 10, a i = ∑ i ∈ Finset.range 9, a i + a 9 :=
      Finset.sum_range_succ _ _
    have e9 : ∑ i ∈ Finset.range 9, a i = ∑ i ∈ Finset.range 8, a i + a 8 :=
      Finset.sum_range_succ _ _
    have h89 : a 8 ≤ a 9 := hmono (by norm_num) (by norm_num)
    show (248 : ℕ) ≤ a 9
    lia

end Usa1992P3
