/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 1994, Problem 2

The sequence a₁, a₂, ... , a₉₉ has a₁ = a₃ = a₅ = ... = a₉₇ = 1,
a₂ = a₄ = a₆ = ... = a₉₈ = 2, and a₉₉ = 3. We interpret subscripts greater
than 99 by subtracting 99, so that a₁₀₀ means a₁ etc. An allowed move is to
change the value of any one of the aₙ to another member of {1, 2, 3}
different from its two neighbors, aₙ₋₁ and aₙ₊₁. Is there a sequence of
allowed moves which results in aₘ = aₘ₊₂ = ... = aₘ₊₉₆ = 1,
aₘ₊₁ = aₘ₊₃ = ... = aₘ₊₉₅ = 2, aₘ₊₉₇ = 3, aₘ₊₉₈ = 2 for some m?
[So if m = 1, we have just interchanged the values of a₉₈ and a₉₉.]

The answer is "no": the cyclic-weight sum below is an invariant of allowed
moves, it equals 3 for the initial configuration and -3 for every target
configuration.
-/

namespace Usa1994P2

/-- The three values that may appear in the sequence. We identify the values
1, 2, 3 of the problem statement with 0, 1, 2 in `ZMod 3`; the cyclic
successor map `x ↦ x + 1` then sends 1 → 2 → 3 → 1. -/
abbrev Val := ZMod 3

/-- A configuration of the sequence, indexed by `ZMod 99` (indices are
interpreted modulo 99, as in the problem statement). Index `i` corresponds
to the problem's aᵢ₊₁. -/
abbrev Config := ZMod 99 → Val

/-- The initial configuration: 1, 2, 1, 2, ..., 1, 2, 3. -/
def initial : Config := fun i ↦
  if i.val = 98 then 2 else if i.val % 2 = 0 then 0 else 1

/-- The alternating pattern underlying the target configurations:
`targetPat k` is the value at offset `k` (with `0 ≤ k ≤ 98`) from the base
index, namely 1 at even offsets `≤ 96`, 2 at odd offsets `≤ 95`, 3 at
offset 97 and 2 at offset 98. -/
def targetPat (k : ℕ) : Val :=
  if k = 97 then 2 else if k = 98 then 1 else if k % 2 = 0 then 0 else 1

/-- The target configuration with base index `m`: the value at index `i`
depends only on the offset `i - m`, exactly as in the problem statement
where index `m + k` carries the `k`-th value of the pattern. -/
def target (m : ZMod 99) : Config := fun i ↦ targetPat (i - m).val

/-- An allowed move: change the value at some index `n` to another value `v`
that differs from both neighbors. -/
def Move (a b : Config) : Prop :=
  ∃ n v, v ≠ a n ∧ v ≠ a (n - 1) ∧ v ≠ a (n + 1) ∧ b = Function.update a n v

snip begin

/-- The weight of a pair of consecutive values: `0` if they are equal,
`+1` if the second is the cyclic successor of the first (i.e. the pairs
(1,2), (2,3), (3,1) of the problem statement), and `-1` otherwise. -/
def pairWeight (x y : Val) : ℤ :=
  if x = y then 0 else if y = x + 1 then 1 else -1

/-- The invariant: the total weight around the cycle. -/
def totalWeight (a : Config) : ℤ := ∑ i : ZMod 99, pairWeight (a i) (a (i + 1))

/-- A case analysis on `ZMod 3`: the key local identity behind the
invariance of `totalWeight`. If `x` differs from both `L` and `R` and `v`
differs from all of `x`, `L` and `R`, then the two pairs through `x` and
through `v` have the same total weight. (This forces `L = R`, and each side
of the identity vanishes.) -/
theorem pairWeight_local :
    ∀ L R x v : Val, (x ≠ L ∧ x ≠ R ∧ v ≠ x ∧ v ≠ L ∧ v ≠ R) →
      pairWeight L v - pairWeight L x + (pairWeight v R - pairWeight x R) = 0 := by
  decide

/-- In `ZMod 99`, an index and its successor are distinct. -/
theorem succ_ne_self (n : ZMod 99) : n + 1 ≠ n := by
  intro h
  have h10 : (1 : ZMod 99) ≠ 0 := by decide
  have h2 : n + 1 - n = n - n := congrArg (· - n) h
  rw [add_sub_cancel_left, sub_self] at h2
  exact h10 h2

/-- In `ZMod 99`, an index and its predecessor are distinct. -/
theorem pred_ne_self (n : ZMod 99) : n - 1 ≠ n := by
  intro h
  have h10 : (1 : ZMod 99) ≠ 0 := by decide
  have h2 : n - 1 - n = n - n := congrArg (· - n) h
  rw [sub_sub_cancel_left, sub_self] at h2
  exact h10 (neg_eq_zero.mp h2)

/-- A move preserves the property that every two consecutive values are
distinct. -/
theorem move_preserves_distinct {a b : Config} (hm : Move a b)
    (h : ∀ i, a i ≠ a (i + 1)) : ∀ i, b i ≠ b (i + 1) := by
  obtain ⟨n, v, _hvx, hvL, hvR, rfl⟩ := hm
  intro i
  by_cases hi : i = n
  · obtain rfl : i = n := hi
    rw [Function.update_self, Function.update_of_ne (succ_ne_self _)]
    exact hvR
  · by_cases hi1 : i + 1 = n
    · have hi2 : i = n - 1 := eq_sub_of_add_eq hi1
      rw [Function.update_of_ne hi, hi1, Function.update_self, hi2]
      exact Ne.symm hvL
    · rw [Function.update_of_ne hi, Function.update_of_ne hi1]
      exact h i

/-- The total weight is invariant under allowed moves, provided the
configuration has distinct consecutive values. -/
theorem totalWeight_move {a b : Config} (hm : Move a b)
    (h : ∀ i, a i ≠ a (i + 1)) : totalWeight a = totalWeight b := by
  obtain ⟨n, v, hvx, hvL, hvR, rfl⟩ := hm
  have hne : n - 1 ≠ n := pred_ne_self n
  -- The difference of the two sums is supported on the two-element set
  -- `{n - 1, n}`.
  have hsupp : ∀ i : ZMod 99, i ∉ ({n - 1, n} : Finset (ZMod 99)) →
      pairWeight (Function.update a n v i) (Function.update a n v (i + 1)) -
        pairWeight (a i) (a (i + 1)) = 0 := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    have hi1 : i + 1 ≠ n := fun hcon ↦ hi.1 (eq_sub_of_add_eq hcon)
    rw [Function.update_of_ne hi.2, Function.update_of_ne hi1, sub_self]
  have hdiff : ∑ i : ZMod 99,
      (pairWeight (Function.update a n v i) (Function.update a n v (i + 1)) -
        pairWeight (a i) (a (i + 1))) = 0 := by
    rw [← Finset.sum_subset (Finset.subset_univ _) (fun i _ hi ↦ hsupp i hi),
      Finset.sum_pair hne]
    rw [Function.update_of_ne hne v a, sub_add_cancel, Function.update_self,
      Function.update_of_ne (succ_ne_self n) v a]
    have hxL : a n ≠ a (n - 1) := by
      have h' := h (n - 1)
      rw [sub_add_cancel] at h'
      exact Ne.symm h'
    have hxR : a n ≠ a (n + 1) := h n
    exact pairWeight_local _ _ _ _ ⟨hxL, hxR, hvx, hvL, hvR⟩
  rw [Finset.sum_sub_distrib, sub_eq_zero] at hdiff
  exact hdiff.symm

/-- In the initial configuration, consecutive values are distinct. -/
theorem initial_distinct : ∀ i : ZMod 99, initial i ≠ initial (i + 1) := by
  decide

set_option maxRecDepth 8192 in
/-- The total weight of the initial configuration is `3`. -/
theorem totalWeight_initial : totalWeight initial = 3 := by
  decide

set_option maxRecDepth 8192 in
/-- The total weight of the target configuration with base `0` is `-3`. -/
theorem totalWeight_target_zero : totalWeight (target 0) = -3 := by
  decide

/-- Shifting the base index of the target configuration does not change the
total weight: the sum is over a full cycle. -/
theorem totalWeight_target_eq (m : ZMod 99) :
    totalWeight (target m) = totalWeight (target 0) := by
  have hbij : Function.Bijective (· - m : ZMod 99 → ZMod 99) :=
    Function.bijective_iff_has_inverse.mpr
      ⟨(· + m), fun _ ↦ sub_add_cancel _ _, fun _ ↦ add_sub_cancel_right _ _⟩
  calc totalWeight (target m)
      = ∑ i : ZMod 99, pairWeight (targetPat (i - m).val)
          (targetPat (i - m + 1).val) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        show pairWeight (targetPat (i - m).val) (targetPat (i + 1 - m).val) = _
        rw [show i + 1 - m = i - m + 1 by ring]
    _ = ∑ j : ZMod 99, pairWeight (targetPat j.val) (targetPat (j + 1).val) :=
        Fintype.sum_bijective (· - m) hbij _ _ fun i ↦ rfl
    _ = totalWeight (target 0) := by
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        show pairWeight (targetPat j.val) (targetPat (j + 1).val) =
          pairWeight (targetPat (j - 0).val) (targetPat (j + 1 - 0).val)
        rw [sub_zero, sub_zero]

/-- Every reachable configuration has the same total weight as the initial
configuration, and has distinct consecutive values. -/
theorem reachable_invariant {b : Config}
    (hr : Relation.ReflTransGen Move initial b) :
    totalWeight b = totalWeight initial ∧ ∀ i, b i ≠ b (i + 1) := by
  induction hr with
  | refl => exact ⟨rfl, initial_distinct⟩
  | tail _ hbc ih =>
    exact ⟨(totalWeight_move hbc ih.2).symm.trans ih.1, move_preserves_distinct hbc ih.2⟩

snip end

problem usa1994_p2 :
    ¬ ∃ m : ZMod 99, Relation.ReflTransGen Move initial (target m) := by
  rintro ⟨m, hm⟩
  obtain ⟨hw, -⟩ := reachable_invariant hm
  rw [totalWeight_target_eq m, totalWeight_target_zero, totalWeight_initial] at hw
  exact absurd hw (by decide)

end Usa1994P2
