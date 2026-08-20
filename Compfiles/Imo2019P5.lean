/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Rat.Star
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Zify
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Combinatorics],
}

/-!
# International Mathematical Olympiad 2019, Problem 5

Let n be a positive integer. Harry has n coins lined up on his desk, which can
show either heads or tails. He does the following operation: if there are k > 0
coins which show heads, then he flips the kth coin over; otherwise he stops the
process. (For example, the process starting with THT would be THT → HHT → HTT
→ TTT, which takes three steps.)

Prove the process will always terminate, and determine the average number of
steps this takes over all 2ⁿ configurations.
-/

namespace Imo2019P5

open Finset

/-- The number of coins showing heads in a configuration of `n` coins.
A configuration is a function `Fin n → Bool`, where `c i = true` means that
the `i`-th coin from the left (starting the count at `0`) shows heads. -/
def numHeads {n : ℕ} (c : Fin n → Bool) : ℕ :=
  (univ.filter fun i ↦ c i).card

/-- The index of the coin that Harry flips in configuration `c`: the `k`-th
coin from the left, where `k` is the number of heads. -/
def flipIx {n : ℕ} (c : Fin n → Bool) (h : numHeads c ≠ 0) : Fin n :=
  ⟨numHeads c - 1, by
    have h1 : numHeads c ≤ n := (card_le_univ _).trans (by simp)
    lia⟩

/-- One step of Harry's process: if there are `k > 0` heads, flip the `k`-th
coin from the left; otherwise (all coins show tails) do nothing. -/
def step {n : ℕ} (c : Fin n → Bool) : Fin n → Bool :=
  if h : numHeads c = 0 then c else Function.update c (flipIx c h) (!c (flipIx c h))

/-- The sum of the 1-based positions of the coins showing heads. -/
def weightedSum {n : ℕ} (c : Fin n → Bool) : ℕ :=
  ∑ i : Fin n, (i.val + 1) * (if c i then 1 else 0)

/-- The measure of a configuration: twice the sum of the 1-based positions of
the heads minus the square of the number of heads. We will show that this is
a nonnegative integer (see `meas_nonneg`) which drops by exactly one at each
step (see `step_meas`), hence it equals the number of steps the process takes. -/
def meas {n : ℕ} (c : Fin n → Bool) : ℤ :=
  2 * (weightedSum c : ℤ) - (numHeads c : ℤ) ^ 2

/-- The number of steps that Harry's process takes starting from
configuration `c`. -/
def L {n : ℕ} (c : Fin n → Bool) : ℕ := (meas c).toNat

snip begin

/-- The `j`-th smallest element of a finset `S` of `Fin n` is at least `j`. -/
theorem le_orderEmbOfFin {n : ℕ} (S : Finset (Fin n)) (j : Fin S.card) :
    (j : ℕ) ≤ (S.orderEmbOfFin rfl j).val := by
  have hsub : (Iio j).map (S.orderEmbOfFin rfl).toEmbedding ⊆
      Iio (S.orderEmbOfFin rfl j) := by
    intro x hx
    rw [mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [mem_Iio] at hy ⊢
    exact (S.orderEmbOfFin rfl).lt_iff_lt.mpr hy
  calc (j : ℕ) = (Iio j).card := (Fin.card_Iio j).symm
    _ = ((Iio j).map (S.orderEmbOfFin rfl).toEmbedding).card := (card_map _).symm
    _ ≤ (Iio (S.orderEmbOfFin rfl j)).card := card_le_card hsub
    _ = (S.orderEmbOfFin rfl j).val := Fin.card_Iio _

/-- For a finset `S` of `Fin n`, the sum of the values of its elements is at
least `card S * (card S - 1) / 2` (twice that sum, to stay in `ℕ`). -/
theorem sum_range_card_le {n : ℕ} (S : Finset (Fin n)) :
    S.card * (S.card - 1) ≤ 2 * ∑ i ∈ S, (i : ℕ) := by
  have hpoint : ∀ j : Fin S.card, (j : ℕ) ≤ (S.orderEmbOfFin rfl j).val :=
    le_orderEmbOfFin S
  have hsum : ∑ i ∈ S, (i : ℕ) = ∑ j : Fin S.card, (S.orderEmbOfFin rfl j).val := by
    conv_lhs => rw [← map_orderEmbOfFin_univ S rfl]
    rw [sum_map]
    simp only [RelEmbedding.coe_toEmbedding]
  rw [hsum]
  have h2 : (∑ j : Fin S.card, (j : ℕ)) * 2 ≤
      (∑ j : Fin S.card, (S.orderEmbOfFin rfl j).val) * 2 :=
    Nat.mul_le_mul_right _ (sum_le_sum fun j _ => hpoint j)
  have h3 : (∑ j : Fin S.card, (j : ℕ)) * 2 = S.card * (S.card - 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun j ↦ j) S.card, sum_range_id_mul_two]
  linarith [h2, h3]

/-- The key combinatorial estimate: if a configuration has `k` heads, then the
sum of the 1-based positions of the heads is at least `k * (k + 1) / 2`. -/
theorem numHeads_mul_succ_le {n : ℕ} (c : Fin n → Bool) :
    numHeads c * (numHeads c + 1) ≤ 2 * weightedSum c := by
  have h1 := sum_range_card_le (univ.filter fun i ↦ c i)
  have h2 : weightedSum c = ∑ i ∈ univ.filter (fun i ↦ c i), (i.val + 1) := by
    rw [weightedSum, sum_filter]
    apply sum_congr rfl
    intro i _
    by_cases hi : c i = true <;> simp [hi]
  have h3 : ∑ i ∈ univ.filter (fun i ↦ c i), (i.val + 1)
      = ∑ i ∈ univ.filter (fun i ↦ c i), i.val + numHeads c := by
    rw [sum_add_distrib, sum_const, nsmul_eq_mul, mul_one]
    rfl
  have h4 : ∀ k : ℕ, k * (k + 1) = k * (k - 1) + 2 * k := by
    intro k
    rcases k with _ | k
    · simp
    · rw [Nat.add_one_sub_one]; ring
  rw [h2, h3, h4]
  unfold numHeads
  linarith [h1]

theorem meas_def {n : ℕ} (c : Fin n → Bool) :
    meas c = 2 * (weightedSum c : ℤ) - (numHeads c : ℤ) ^ 2 := rfl

theorem meas_nonneg {n : ℕ} (c : Fin n → Bool) : 0 ≤ meas c := by
  have h := numHeads_mul_succ_le c
  have h' : (numHeads c : ℤ) * ((numHeads c : ℤ) + 1) ≤ 2 * (weightedSum c : ℤ) := by
    exact_mod_cast h
  have hnn : (0 : ℤ) ≤ (numHeads c : ℤ) := Int.natCast_nonneg _
  unfold meas
  linarith [h']

theorem meas_ge_numHeads {n : ℕ} (c : Fin n → Bool) : (numHeads c : ℤ) ≤ meas c := by
  have h := numHeads_mul_succ_le c
  have h' : (numHeads c : ℤ) * ((numHeads c : ℤ) + 1) ≤ 2 * (weightedSum c : ℤ) := by
    exact_mod_cast h
  unfold meas
  linarith [h']

theorem meas_eq_zero_iff {n : ℕ} (c : Fin n → Bool) : meas c = 0 ↔ numHeads c = 0 := by
  constructor
  · intro h
    have h1 := meas_ge_numHeads c
    have h2 : (numHeads c : ℤ) = 0 := by
      have hnn : (0 : ℤ) ≤ (numHeads c : ℤ) := Int.natCast_nonneg _
      linarith [h, h1]
    lia
  · intro h
    have hf : ∀ i : Fin n, c i = false := by
      intro i
      have hempty : (univ.filter fun j ↦ c j) = ∅ := card_eq_zero.mp h
      by_contra hne
      have hti : c i = true := by cases hci : c i <;> simp_all
      have hmem : i ∈ univ.filter (fun j ↦ c j) := mem_filter.mpr ⟨mem_univ i, hti⟩
      rw [hempty] at hmem
      exact notMem_empty i hmem
    have hw : weightedSum c = 0 := by
      apply sum_eq_zero
      intro i _
      simp [hf i]
    simp [meas, h, hw]

/-- The number of heads as a sum of indicators, in `ℤ`. -/
theorem numHeads_cast {n : ℕ} (c : Fin n → Bool) :
    (numHeads c : ℤ) = ∑ i : Fin n, (if c i then (1 : ℤ) else 0) := by
  have h2 : numHeads c = ∑ i : Fin n, (if c i = true then (1 : ℕ) else 0) :=
    card_filter _ _
  exact_mod_cast h2

/-- The weighted sum as a sum over all positions, in `ℤ`. -/
theorem weightedSum_cast {n : ℕ} (c : Fin n → Bool) :
    (weightedSum c : ℤ) = ∑ i : Fin n, ((i : ℕ) + 1 : ℤ) * (if c i then (1 : ℤ) else 0) := by
  rw [weightedSum, Nat.cast_sum]
  apply sum_congr rfl
  intro i _
  by_cases hi : c i = true <;> simp [hi]

/-- How the head-count sum changes when coin `p` is flipped. -/
theorem headsZ_update {n : ℕ} (c : Fin n → Bool) (p : Fin n) :
    ∑ i : Fin n, (if Function.update c p (!c p) i then (1 : ℤ) else 0)
      = (∑ i : Fin n, (if c i then (1 : ℤ) else 0)) + (if c p then (-1 : ℤ) else 1) := by
  have h1 : (fun i : Fin n ↦ (if Function.update c p (!c p) i then (1 : ℤ) else 0))
      = Function.update (fun i : Fin n ↦ (if c i then (1 : ℤ) else 0)) p
        (if c p then (0 : ℤ) else 1) := by
    funext i
    by_cases hi : i = p
    · subst hi
      by_cases hc : c i <;> simp_all [Function.update_self]
    · rw [Function.update_of_ne hi, Function.update_of_ne hi]
  rw [h1, sum_update_of_mem (mem_univ p), sdiff_singleton_eq_erase,
    ← add_sum_erase univ _ (mem_univ p)]
  by_cases hc : c p
  · simp only [ite_eq_left hc]; ring
  · simp only [ite_eq_right hc]; ring

/-- How the weighted sum changes when coin `p` is flipped. -/
theorem weightedZ_update {n : ℕ} (c : Fin n → Bool) (p : Fin n) :
    ∑ i : Fin n, ((i : ℕ) + 1 : ℤ) * (if Function.update c p (!c p) i then (1 : ℤ) else 0)
      = (∑ i : Fin n, ((i : ℕ) + 1 : ℤ) * (if c i then (1 : ℤ) else 0))
        + ((p : ℕ) + 1 : ℤ) * (if c p then (-1 : ℤ) else 1) := by
  have h1 : (fun i : Fin n ↦ ((i : ℕ) + 1 : ℤ) *
        (if Function.update c p (!c p) i then (1 : ℤ) else 0))
      = Function.update (fun i : Fin n ↦ ((i : ℕ) + 1 : ℤ) * (if c i then (1 : ℤ) else 0)) p
        (((p : ℕ) + 1 : ℤ) * (if c p then (0 : ℤ) else 1)) := by
    funext i
    by_cases hi : i = p
    · subst hi
      by_cases hc : c i <;> simp_all [Function.update_self]
    · rw [Function.update_of_ne hi, Function.update_of_ne hi]
  rw [h1, sum_update_of_mem (mem_univ p), sdiff_singleton_eq_erase,
    ← add_sum_erase univ _ (mem_univ p)]
  by_cases hc : c p
  · simp only [ite_eq_left hc]; ring
  · simp only [ite_eq_right hc]; ring

/-- The measure drops by exactly one at each step. -/
theorem step_meas {n : ℕ} (c : Fin n → Bool) (h : numHeads c ≠ 0) :
    meas (step c) = meas c - 1 := by
  have hstep : step c = Function.update c (flipIx c h) (!c (flipIx c h)) := by
    unfold step
    rw [dite_eq_right h]
  rw [hstep]
  set p := flipIx c h with hp
  have hp2 : (p : ℕ) + 1 = numHeads c := by
    have h1 : 0 < numHeads c := Nat.pos_of_ne_zero h
    have hpv : (p : ℕ) = numHeads c - 1 := by rw [hp]; rfl
    lia
  have hpv : ((p : ℕ) + 1 : ℤ) = ∑ i : Fin n, (if c i then (1 : ℤ) else 0) := by
    rw [← numHeads_cast c]
    exact_mod_cast hp2
  have e1 := numHeads_cast (Function.update c p (!c p))
  have e2 := numHeads_cast c
  have e3 := weightedSum_cast (Function.update c p (!c p))
  have e4 := weightedSum_cast c
  rw [meas_def, meas_def, e1, e2, e3, e4, headsZ_update, weightedZ_update, hpv]
  by_cases hc : c p <;> simp [hc] <;> ring

/-- After `m` steps with `m ≤ meas c`, the measure has dropped by exactly `m`. -/
theorem iter_meas {n : ℕ} (c : Fin n → Bool) (m : ℕ) (hm : (m : ℤ) ≤ meas c) :
    meas (step^[m] c) = meas c - (m : ℤ) := by
  induction m with
  | zero => simp
  | succ k ih =>
    have hmk : (k : ℤ) + 1 ≤ meas c := by exact_mod_cast hm
    have hk : (k : ℤ) ≤ meas c := by linarith
    have hih := ih hk
    have hne : numHeads (step^[k] c) ≠ 0 := by
      intro hz
      have h0 : meas (step^[k] c) = 0 := (meas_eq_zero_iff _).mpr hz
      rw [hih] at h0
      linarith [hmk]
    rw [Function.iterate_succ_apply', step_meas _ hne, hih]
    push_cast
    ring

/-- The process from `c` stops after exactly `L c` steps in the all-tails
configuration. -/
theorem iterate_L {n : ℕ} (c : Fin n → Bool) : step^[L c] c = fun _ ↦ false := by
  have h1 : (L c : ℤ) = meas c := Int.toNat_of_nonneg (meas_nonneg c)
  have h2 := iter_meas c (L c) (le_of_eq h1)
  rw [h1] at h2
  have h3 : meas (step^[L c] c) = 0 := by rw [h2]; ring
  have h4 : numHeads (step^[L c] c) = 0 := (meas_eq_zero_iff _).mp h3
  have h5 : (univ.filter fun j ↦ (step^[L c] c) j) = ∅ := card_eq_zero.mp h4
  funext i
  by_cases hi : (step^[L c] c) i
  · exfalso
    have hmem : i ∈ univ.filter (fun j ↦ (step^[L c] c) j) :=
      mem_filter.mpr ⟨mem_univ i, hi⟩
    rw [h5] at hmem
    exact notMem_empty i hmem
  · cases hv : (step^[L c] c) i
    · rfl
    · exact absurd hv hi

/-- Before step `L c`, the process has not stopped yet. -/
theorem not_iterate_lt_L {n : ℕ} (c : Fin n → Bool) {m : ℕ} (hm : m < L c) :
    step^[m] c ≠ fun _ ↦ false := by
  have h1 : (L c : ℤ) = meas c := Int.toNat_of_nonneg (meas_nonneg c)
  have h2 : (m : ℤ) ≤ meas c := by
    have : (m : ℤ) < (L c : ℤ) := by exact_mod_cast hm
    linarith [h1]
  have h3 := iter_meas c m h2
  intro hcon
  have h4 : meas (step^[m] c) = 0 := by
    have : numHeads (step^[m] c) = 0 := by
      have hf : ∀ i : Fin n, (step^[m] c) i = false := fun i ↦ congrFun hcon i
      have : (univ.filter fun j ↦ (step^[m] c) j) = ∅ := by
        apply eq_empty_of_forall_notMem
        intro j
        rw [mem_filter]
        rintro ⟨_, hj⟩
        rw [hf j] at hj
        exact absurd hj (by simp)
      exact card_eq_zero.mpr this
    exact (meas_eq_zero_iff _).mpr this
  rw [h3] at h4
  have h5 : (m : ℤ) < meas c := by rw [← h1]; exact_mod_cast hm
  linarith

/-- Configurations with a head at position `i` are in bijection with those
with a tail at position `i`, by flipping coin `i`. -/
theorem card_filter_true_eq_card_filter_false {n : ℕ} (i : Fin n) :
    (univ.filter fun c : Fin n → Bool ↦ c i = true).card
      = (univ.filter fun c : Fin n → Bool ↦ c i = false).card := by
  apply card_bij' (fun c _ ↦ Function.update c i (!c i)) (fun c _ ↦ Function.update c i (!c i))
    (fun c hc ↦ mem_filter.mpr ⟨mem_univ _, by
      have hc2 : c i = true := (mem_filter.mp hc).2
      simp [Function.update_self, hc2]⟩)
    (fun c hc ↦ mem_filter.mpr ⟨mem_univ _, by
      have hc2 : c i = false := (mem_filter.mp hc).2
      simp [Function.update_self, hc2]⟩)
  · intro c _
    calc Function.update (Function.update c i (!c i)) i (!Function.update c i (!c i) i)
        = Function.update (Function.update c i (!c i)) i (c i) := by
          rw [Function.update_self, Bool.not_not]
      _ = Function.update c i (c i) := Function.update_idem _ _ _
      _ = c := Function.update_eq_self i c
  · intro c _
    calc Function.update (Function.update c i (!c i)) i (!Function.update c i (!c i) i)
        = Function.update (Function.update c i (!c i)) i (c i) := by
          rw [Function.update_self, Bool.not_not]
      _ = Function.update c i (c i) := Function.update_idem _ _ _
      _ = c := Function.update_eq_self i c

/-- Exactly half of all `2 ^ n` configurations have a head at position `i`. -/
theorem card_filter_true {n : ℕ} (hn : 0 < n) (i : Fin n) :
    (univ.filter fun c : Fin n → Bool ↦ c i = true).card = 2 ^ (n - 1) := by
  have hbij := card_filter_true_eq_card_filter_false i
  have hsum : (univ.filter fun c : Fin n → Bool ↦ c i = true).card
      + (univ.filter fun c : Fin n → Bool ↦ c i = false).card = 2 ^ n := by
    have h := card_filter_add_card_filter_not (fun c : Fin n → Bool ↦ c i = true)
      (s := (univ : Finset (Fin n → Bool)))
    have hfalse : (univ.filter fun c : Fin n → Bool ↦ ¬c i = true)
        = (univ.filter fun c : Fin n → Bool ↦ c i = false) := by
      ext c
      simp only [mem_filter, mem_univ, true_and]
      cases c i <;> simp
    rw [hfalse] at h
    rw [h, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have h2n : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rcases n with _ | n'
    · lia
    · rw [Nat.add_one_sub_one, pow_succ]
      exact mul_comm _ _
  have hkey : 2 * (univ.filter fun c : Fin n → Bool ↦ c i = true).card = 2 ^ n := by
    have h2 := hsum
    rw [← hbij] at h2
    rw [← h2]
    exact two_mul _
  exact Nat.mul_left_cancel (by norm_num) (hkey.trans h2n)

/-- Twice the number of configurations with heads at both `i` and `j`
equals `2 ^ (n - 1)`. -/
theorem two_mul_card_filter_pair {n : ℕ} (hn : 0 < n) {i j : Fin n} (hij : i ≠ j) :
    2 * (univ.filter fun c : Fin n → Bool ↦ c i = true ∧ c j = true).card = 2 ^ (n - 1) := by
  have hbij : (univ.filter fun c : Fin n → Bool ↦ c i = true ∧ c j = true).card
      = (univ.filter fun c : Fin n → Bool ↦ c i = true ∧ c j = false).card := by
    apply card_bij' (fun c _ ↦ Function.update c j (!c j)) (fun c _ ↦ Function.update c j (!c j))
      (fun c hc ↦ mem_filter.mpr ⟨mem_univ _, by
        have hc2 := (mem_filter.mp hc).2
        constructor
        · rw [Function.update_of_ne hij]; exact hc2.1
        · simp [Function.update_self, hc2.2]⟩)
      (fun c hc ↦ mem_filter.mpr ⟨mem_univ _, by
        have hc2 := (mem_filter.mp hc).2
        constructor
        · rw [Function.update_of_ne hij]; exact hc2.1
        · simp [Function.update_self, hc2.2]⟩)
    · intro c _
      calc Function.update (Function.update c j (!c j)) j (!Function.update c j (!c j) j)
          = Function.update (Function.update c j (!c j)) j (c j) := by
            rw [Function.update_self, Bool.not_not]
        _ = Function.update c j (c j) := Function.update_idem _ _ _
        _ = c := Function.update_eq_self j c
    · intro c _
      calc Function.update (Function.update c j (!c j)) j (!Function.update c j (!c j) j)
          = Function.update (Function.update c j (!c j)) j (c j) := by
            rw [Function.update_self, Bool.not_not]
        _ = Function.update c j (c j) := Function.update_idem _ _ _
        _ = c := Function.update_eq_self j c
  have hsum : (univ.filter fun c : Fin n → Bool ↦ c i = true ∧ c j = true).card
      + (univ.filter fun c : Fin n → Bool ↦ c i = true ∧ c j = false).card
      = (univ.filter fun c : Fin n → Bool ↦ c i = true).card := by
    have h := card_filter_add_card_filter_not (fun c : Fin n → Bool ↦ c j = true)
      (s := univ.filter fun c : Fin n → Bool ↦ c i = true)
    rw [filter_filter, filter_filter] at h
    have hfalse : (univ.filter fun c : Fin n → Bool ↦ c i = true ∧ ¬c j = true)
        = (univ.filter fun c : Fin n → Bool ↦ c i = true ∧ c j = false) := by
      ext c
      simp only [mem_filter, mem_univ, true_and]
      cases c j <;> simp
    rw [hfalse] at h
    exact h
  have h1 := card_filter_true hn i
  rw [← hbij] at hsum
  rw [← h1, ← hsum]
  exact two_mul _

/-- The number of configurations with heads at both `i` and `j` is
`2 ^ (n - 2)`. -/
theorem card_filter_pair {n : ℕ} (hn : 0 < n) {i j : Fin n} (hij : i ≠ j) :
    (univ.filter fun c : Fin n → Bool ↦ c i = true ∧ c j = true).card = 2 ^ (n - 2) := by
  have h2 := two_mul_card_filter_pair hn hij
  have hn2 : 2 ≤ n := by
    have hnont := nontrivial_of_ne i j hij
    rw [← Fintype.one_lt_card_iff_nontrivial] at hnont
    rwa [Fintype.card_fin] at hnont
  have h3 : 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
    have h : n - 1 = n - 2 + 1 := by lia
    rw [h, pow_succ]
    exact mul_comm _ _
  rw [h3] at h2
  exact Nat.mul_left_cancel (by norm_num) h2

/-- The sum of the indicator of heads at position `i` over all configurations. -/
theorem sum_indicator {n : ℕ} (hn : 0 < n) (i : Fin n) :
    ∑ c : Fin n → Bool, (if c i then (1 : ℤ) else 0) = 2 ^ (n - 1) := by
  have h := card_filter_true hn i
  have h2 := card_filter (fun c : Fin n → Bool ↦ c i = true) (univ : Finset (Fin n → Bool))
  rw [h] at h2
  exact_mod_cast h2.symm

/-- The total of `L` over all configurations is `2 ^ n * n * (n + 1) / 4`;
we prove four times that value to stay in `ℤ`. -/
theorem sum_four_L {n : ℕ} (hn : 0 < n) :
    4 * ∑ c : Fin n → Bool, (L c : ℤ) = 2 ^ n * n * (n + 1) := by
  have hcount := sum_indicator hn
  set T : ℤ := ∑ i : Fin n, ((i : ℕ) + 1 : ℤ) with hTdef
  have h2T : 2 * T = n * (n + 1) := by
    rw [hTdef]
    have hs : ∑ i : Fin n, ((i : ℕ) + 1 : ℤ) = ∑ i : Fin n, ((i : ℕ) : ℤ) + (n : ℤ) := by
      rw [sum_add_distrib]
      simp [sum_const]
    have hsum_id : 2 * ∑ i : Fin n, ((i : ℕ) : ℤ) = n * ((n - 1 : ℕ) : ℤ) := by
      have h := sum_range_id_mul_two n
      rw [← Fin.sum_univ_eq_sum_range (fun j ↦ j) n] at h
      have h' : ((∑ i : Fin n, (i : ℕ)) * 2 : ℕ) = ((n * (n - 1) : ℕ) : ℤ) := by
        exact_mod_cast h
      push_cast at h'
      linarith [h']
    have hcast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
      rw [Nat.cast_sub hn]
      simp
    rw [hs]
    rw [hcast] at hsum_id
    linarith [hsum_id]
  have hsumW : ∑ c : Fin n → Bool, (weightedSum c : ℤ) = (2 : ℤ) ^ (n - 1) * T := by
    calc ∑ c : Fin n → Bool, (weightedSum c : ℤ)
        = ∑ c : Fin n → Bool, ∑ i : Fin n, ((i : ℕ) + 1 : ℤ) * (if c i then (1 : ℤ) else 0) :=
          sum_congr rfl fun c _ ↦ weightedSum_cast c
      _ = ∑ i : Fin n, ∑ c : Fin n → Bool, ((i : ℕ) + 1 : ℤ) * (if c i then (1 : ℤ) else 0) :=
          sum_comm
      _ = ∑ i : Fin n, ((i : ℕ) + 1 : ℤ) * (2 : ℤ) ^ (n - 1) := by
          apply sum_congr rfl
          intro i _
          rw [← mul_sum, hcount i]
      _ = (∑ i : Fin n, ((i : ℕ) + 1 : ℤ)) * (2 : ℤ) ^ (n - 1) := (sum_mul univ _ _).symm
      _ = (2 : ℤ) ^ (n - 1) * T := by rw [← hTdef, mul_comm]
  have hsumH : ∑ c : Fin n → Bool, ((numHeads c : ℤ)) ^ 2
      = n * (2 : ℤ) ^ (n - 1) + n * ((n - 1 : ℕ) : ℤ) * (2 : ℤ) ^ (n - 2) := by
    have hdiag : ∀ i : Fin n,
        ∑ c : Fin n → Bool, (if c i then (1 : ℤ) else 0) * (if c i then (1 : ℤ) else 0)
          = (2 : ℤ) ^ (n - 1) := by
      intro i
      have hid : ∀ c : Fin n → Bool,
          (if c i then (1 : ℤ) else 0) * (if c i then (1 : ℤ) else 0)
            = (if c i then (1 : ℤ) else 0) := by
        intro c
        by_cases h : c i <;> simp [h]
      calc ∑ c : Fin n → Bool, (if c i then (1 : ℤ) else 0) * (if c i then (1 : ℤ) else 0)
          = ∑ c : Fin n → Bool, (if c i then (1 : ℤ) else 0) := sum_congr rfl fun c _ ↦ hid c
        _ = (2 : ℤ) ^ (n - 1) := hcount i
    have hsplit : ∀ (i : Fin n) {j : Fin n}, j ≠ i →
        ∑ c : Fin n → Bool, (if c i then (1 : ℤ) else 0) * (if c j then (1 : ℤ) else 0)
          = (2 : ℤ) ^ (n - 2) := by
      intro i j hj
      have h := card_filter_pair hn hj.symm
      have h2 := card_filter (fun c : Fin n → Bool ↦ c i = true ∧ c j = true)
        (univ : Finset (Fin n → Bool))
      rw [h] at h2
      have hcast : ((2 ^ (n - 2) : ℕ) : ℤ)
          = ∑ c : Fin n → Bool, (if (c i = true ∧ c j = true) then (1 : ℤ) else 0) := by
        exact_mod_cast h2
      have h3 : (2 : ℤ) ^ (n - 2) = ((2 ^ (n - 2) : ℕ) : ℤ) := by norm_cast
      rw [h3, hcast]
      apply sum_congr rfl
      intro c _
      by_cases h1 : c i <;> by_cases h2 : c j <;> simp [h1, h2]
    have hper : ∀ i : Fin n,
        ∑ j : Fin n, ∑ c : Fin n → Bool,
            (if c i then (1 : ℤ) else 0) * (if c j then (1 : ℤ) else 0)
          = (2 : ℤ) ^ (n - 1) + ∑ j ∈ univ.erase i, (2 : ℤ) ^ (n - 2) := by
      intro i
      conv_lhs => rw [← insert_erase (mem_univ i)]
      rw [sum_insert (notMem_erase i univ)]
      congr 1
      · exact hdiag i
      · apply sum_congr rfl
        intro j hj
        exact hsplit i (mem_erase.mp hj).1
    calc ∑ c : Fin n → Bool, ((numHeads c : ℤ)) ^ 2
        = ∑ c : Fin n → Bool, (∑ i : Fin n, (if c i then (1 : ℤ) else 0)) ^ 2 :=
          sum_congr rfl fun c _ ↦ by rw [numHeads_cast]
      _ = ∑ c : Fin n → Bool, ∑ i : Fin n, ∑ j : Fin n,
            (if c i then (1 : ℤ) else 0) * (if c j then (1 : ℤ) else 0) := by
          apply sum_congr rfl
          intro c _
          rw [sq, sum_mul_sum]
      _ = ∑ i : Fin n, ∑ c : Fin n → Bool, ∑ j : Fin n,
            (if c i then (1 : ℤ) else 0) * (if c j then (1 : ℤ) else 0) := sum_comm
      _ = ∑ i : Fin n, ∑ j : Fin n, ∑ c : Fin n → Bool,
            (if c i then (1 : ℤ) else 0) * (if c j then (1 : ℤ) else 0) :=
          sum_congr rfl fun i _ ↦ sum_comm
      _ = ∑ i : Fin n, ((2 : ℤ) ^ (n - 1) + ∑ j ∈ univ.erase i, (2 : ℤ) ^ (n - 2)) :=
          sum_congr rfl fun i _ ↦ hper i
      _ = ∑ i : Fin n, ((2 : ℤ) ^ (n - 1) + ((n - 1 : ℕ) : ℤ) * (2 : ℤ) ^ (n - 2)) := by
          apply sum_congr rfl
          intro i _
          rw [sum_const, card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin,
            nsmul_eq_mul]
      _ = n * (2 : ℤ) ^ (n - 1) + n * ((n - 1 : ℕ) : ℤ) * (2 : ℤ) ^ (n - 2) := by
          rw [sum_add_distrib, sum_const, sum_const, card_univ, Fintype.card_fin,
            nsmul_eq_mul, nsmul_eq_mul]
          ring
  have hsumL : ∑ c : Fin n → Bool, (L c : ℤ)
      = 2 * ((2 : ℤ) ^ (n - 1) * T)
        - (n * (2 : ℤ) ^ (n - 1) + n * ((n - 1 : ℕ) : ℤ) * (2 : ℤ) ^ (n - 2)) := by
    have hL : ∀ c : Fin n → Bool, (L c : ℤ) = meas c :=
      fun c ↦ Int.toNat_of_nonneg (meas_nonneg c)
    calc ∑ c : Fin n → Bool, (L c : ℤ)
        = ∑ c : Fin n → Bool, meas c := sum_congr rfl fun c _ ↦ hL c
      _ = ∑ c : Fin n → Bool, (2 * (weightedSum c : ℤ) - (numHeads c : ℤ) ^ 2) :=
          sum_congr rfl fun c _ ↦ meas_def c
      _ = 2 * (∑ c : Fin n → Bool, (weightedSum c : ℤ))
          - ∑ c : Fin n → Bool, (numHeads c : ℤ) ^ 2 := by
          rw [sum_sub_distrib, ← mul_sum]
      _ = 2 * ((2 : ℤ) ^ (n - 1) * T)
          - (n * (2 : ℤ) ^ (n - 1) + n * ((n - 1 : ℕ) : ℤ) * (2 : ℤ) ^ (n - 2)) := by
          rw [hsumW, hsumH]
  rcases lt_or_ge n 2 with hlt | hge
  · have hn1 : n = 1 := by lia
    subst hn1
    have h2T' : 2 * T = 2 := by norm_num [h2T]
    rw [hsumL]
    norm_num
    linarith [h2T']
  · have hq1 : (2 : ℤ) ^ (n - 1) = 2 * (2 : ℤ) ^ (n - 2) := by
      have h : n - 1 = n - 2 + 1 := by lia
      rw [h, pow_succ]
      exact mul_comm _ _
    have hq2 : (2 : ℤ) ^ n = 4 * (2 : ℤ) ^ (n - 2) := by
      have h : n = n - 2 + 2 := by lia
      conv_lhs => rw [h]
      rw [pow_add]
      ring
    have hcast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
      rw [Nat.cast_sub (by lia : 1 ≤ n)]
      simp
    rw [hsumL, hq1, hq2, hcast]
    linear_combination 8 * (2 : ℤ) ^ (n - 2) * h2T

snip end

/-- The average number of steps over all `2 ^ n` initial configurations. -/
determine averageSteps (n : ℕ) : ℚ := n * (n + 1) / 4

/-- Part (a): the process always terminates. -/
problem imo2019_p5_parta (n : ℕ) (c : Fin n → Bool) :
    ∃ m : ℕ, step^[m] c = fun _ ↦ false :=
  ⟨L c, iterate_L c⟩

/-- Part (b): the average number of steps over all `2 ^ n` configurations is
`n * (n + 1) / 4`. -/
problem imo2019_p5_partb (n : ℕ) (hn : 0 < n) :
    (∑ c : Fin n → Bool, (L c : ℚ)) / 2 ^ n = averageSteps n := by
  have h := sum_four_L hn
  have h' : (4 : ℚ) * ∑ c : Fin n → Bool, (L c : ℚ) = 2 ^ n * n * (n + 1) := by
    exact_mod_cast h
  unfold averageSteps
  have h2n : ((2 : ℚ) ^ n) ≠ 0 := by positivity
  field_simp
  linear_combination h'

end Imo2019P5
