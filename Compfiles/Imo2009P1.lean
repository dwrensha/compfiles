/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 2009, Problem 1

Let $n$ be a positive integer and let $a_1, a_2, \ldots, a_k$ ($k \ge 2$) be
distinct integers in the set $\{1, 2, \ldots, n\}$ such that $n$ divides
$a_i(a_{i+1} - 1)$ for $i = 1, 2, \ldots, k - 1$. Prove that $n$ does not
divide $a_k(a_1 - 1)$.
-/

namespace Imo2009P1

snip begin

/-- Telescoping: if `c j * c (j+1) = c j` for all `j`, then the product of any
window `c i, c (i+1), …, c (i+m)` collapses to its first term `c i`. -/
lemma telescope {R : Type*} [CommMonoid R] (c : ℕ → R)
    (hc : ∀ j, c j * c (j + 1) = c j) :
    ∀ m i, ∏ x ∈ Finset.range (m + 1), c (i + x) = c i := by
  intro m
  induction m with
  | zero => intro i; simp
  | succ m ih =>
    intro i
    rw [Finset.prod_range_succ, Finset.prod_range_succ, mul_assoc,
        show i + (m + 1) = (i + m) + 1 from by ring, hc (i + m),
        ← Finset.prod_range_succ]
    exact ih i

/-- If the relation `c j * c (j+1) = c j` holds and `c` is periodic with period
`k ≥ 1`, then `c` is constant: `c i = c (i+1)` for all `i`. -/
lemma const_of_cyclic {R : Type*} [CommMonoid R] (c : ℕ → R) (k : ℕ) (hk : 1 ≤ k)
    (hc : ∀ j, c j * c (j + 1) = c j) (hper : ∀ i, c (i + k) = c i) :
    ∀ i, c i = c (i + 1) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by lia⟩
  intro i
  have hφi : ∏ x ∈ Finset.range (k' + 1), c (i + x) = c i := telescope c hc k' i
  have hφi1 : ∏ x ∈ Finset.range (k' + 1), c (i + 1 + x) = c (i + 1) :=
    telescope c hc k' (i + 1)
  rw [← hφi, ← hφi1, Finset.prod_range_succ', Finset.prod_range_succ]
  congr 1
  · apply Finset.prod_congr rfl
    intro x _
    congr 1
    ring
  · rw [Nat.add_zero, show i + 1 + k' = i + (k' + 1) from by ring]
    exact (hper i).symm

snip end

problem imo2009_p1 (n k : ℕ) (_hn : 0 < n) (hk : 2 ≤ k)
    (a : Fin k → ℤ)
    (hmem : ∀ i, a i ∈ Finset.Icc 1 (n : ℤ))
    (hdistinct : Function.Injective a)
    (hdvd : ∀ i : Fin k, (hi : (i : ℕ) + 1 < k) →
              (n : ℤ) ∣ a i * (a ⟨(i : ℕ) + 1, hi⟩ - 1)) :
    ¬ (n : ℤ) ∣ a ⟨k - 1, by lia⟩ * (a ⟨0, by lia⟩ - 1) := by
  intro hwrap
  have hk0 : 0 < k := by lia
  -- View the (cyclic) sequence as a periodic function `c : ℕ → ZMod n`.
  set c : ℕ → ZMod n := fun j => ((a ⟨j % k, Nat.mod_lt j hk0⟩ : ℤ) : ZMod n) with hc_def
  have hone : (1 : ℕ) % k = 1 := Nat.mod_eq_of_lt (by lia)
  -- The divisibility hypotheses, packaged cyclically.
  have hc : ∀ j, c j * c (j + 1) = c j := by
    intro j
    have hr : j % k < k := Nat.mod_lt j hk0
    have hDvd : (n : ℤ) ∣ a ⟨j % k, hr⟩ * (a ⟨(j + 1) % k, Nat.mod_lt _ hk0⟩ - 1) := by
      rcases lt_or_eq_of_le (Nat.succ_le_of_lt hr) with hlt | heq
      · have hmod : (j + 1) % k = j % k + 1 := by
          rw [Nat.add_mod, hone, Nat.mod_eq_of_lt hlt]
        have he : (⟨(j + 1) % k, Nat.mod_lt _ hk0⟩ : Fin k) = ⟨j % k + 1, by lia⟩ :=
          Fin.ext hmod
        rw [he]
        exact hdvd ⟨j % k, hr⟩ hlt
      · have hmod0 : (j + 1) % k = 0 := by
          rw [Nat.add_mod, hone, show j % k + 1 = k from heq, Nat.mod_self]
        have e1 : (⟨j % k, hr⟩ : Fin k) = ⟨k - 1, by lia⟩ := Fin.ext (by lia)
        have e2 : (⟨(j + 1) % k, Nat.mod_lt _ hk0⟩ : Fin k) = ⟨0, by lia⟩ := Fin.ext hmod0
        rw [e1, e2]
        exact hwrap
    have hz : ((a ⟨j % k, hr⟩ * (a ⟨(j + 1) % k, Nat.mod_lt _ hk0⟩ - 1) : ℤ) : ZMod n) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mpr hDvd
    push_cast at hz
    simp only [hc_def]
    linear_combination hz
  have hper : ∀ i, c (i + k) = c i := by
    intro i
    simp only [hc_def]
    congr 2
    exact Fin.ext (Nat.add_mod_right i k)
  -- Hence `c` is constant; in particular the first two terms agree mod `n`.
  have key : c 0 = c 1 := const_of_cyclic c k hk0 hc hper 0
  simp only [hc_def] at key
  have e0 : (⟨0 % k, Nat.mod_lt 0 hk0⟩ : Fin k) = ⟨0, by lia⟩ := Fin.ext (Nat.zero_mod k)
  have e1 : (⟨1 % k, Nat.mod_lt 1 hk0⟩ : Fin k) = ⟨1, by lia⟩ := Fin.ext hone
  rw [e0, e1] at key
  -- Translate the congruence back to an integer divisibility.
  have hdvdInt : (n : ℤ) ∣ (a ⟨0, by lia⟩ - a ⟨1, by lia⟩) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [key, sub_self]
  -- But the two entries are distinct elements of `{1, …, n}`, a contradiction:
  -- a nonzero multiple of `n` cannot have absolute value below `n`.
  obtain ⟨hb0l, hb0r⟩ := Finset.mem_Icc.mp (hmem ⟨0, by lia⟩)
  obtain ⟨hb1l, hb1r⟩ := Finset.mem_Icc.mp (hmem ⟨1, by lia⟩)
  have hdvd' : n ∣ (a ⟨0, by lia⟩ - a ⟨1, by lia⟩).natAbs := by
    simpa using Int.natAbs_dvd_natAbs.mpr hdvdInt
  have hlt : (a ⟨0, by lia⟩ - a ⟨1, by lia⟩).natAbs < n := by lia
  have hzero := Nat.eq_zero_of_dvd_of_lt hdvd' hlt
  rw [Int.natAbs_eq_zero, sub_eq_zero] at hzero
  exact absurd (hdistinct hzero) (by simp [Fin.ext_iff])

end Imo2009P1
