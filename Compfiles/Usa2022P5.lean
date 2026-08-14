/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Tactic.IntervalCases
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra, .Combinatorics] }

/-!
# USA Mathematical Olympiad 2022, Problem 5

A function f : ℝ → ℝ is essentially increasing if f(s) ≤ f(t) holds
whenever s ≤ t are real numbers such that f(s) ≠ 0 and f(t) ≠ 0.

Find the smallest integer k such that for any 2022 real numbers
x₁, x₂, ..., x₂₀₂₂, there exist k essentially increasing functions
f₁, f₂, ..., fₖ such that

  f₁(n) + f₂(n) + ⋯ + fₖ(n) = xₙ

for every n = 1, 2, ..., 2022.
-/

namespace Usa2022P5

/-- A function `f : ℝ → ℝ` is *essentially increasing* if `f s ≤ f t`
whenever `s ≤ t` are real numbers such that `f s ≠ 0` and `f t ≠ 0`. -/
def EssentiallyIncreasing (f : ℝ → ℝ) : Prop :=
  ∀ s t : ℝ, s ≤ t → f s ≠ 0 → f t ≠ 0 → f s ≤ f t

/-- The property of the natural number `k` occurring in the problem:
every `2022`-tuple `(x₁, …, x₂₀₂₂)` of real numbers is the pointwise sum
of `k` essentially increasing functions at the points `1, …, 2022`. -/
def Good (k : ℕ) : Prop :=
  ∀ x : Fin 2022 → ℝ, ∃ f : Fin k → ℝ → ℝ,
    (∀ i, EssentiallyIncreasing (f i)) ∧
    ∀ n : Fin 2022, ∑ i, f i (n.val + 1) = x n

determine solution : ℕ := 11

snip begin

/-- The identically zero function is essentially increasing. -/
lemma essentiallyIncreasing_zero : EssentiallyIncreasing (0 : ℝ → ℝ) := by
  intro s t _ hs _
  exact (hs rfl).elim

/-- If `k` functions suffice, then so do any `m ≥ k` functions,
by padding with zero functions. -/
lemma Good.mono {k m : ℕ} (hkm : k ≤ m) (hk : Good k) : Good m := by
  intro x
  obtain ⟨f, hf, hsum⟩ := hk x
  refine ⟨fun j => if h : j.val < k then f ⟨j.val, h⟩ else 0, fun j => ?_, fun n => ?_⟩
  · by_cases h : j.val < k
    · show EssentiallyIncreasing (if h : j.val < k then f ⟨j.val, h⟩ else 0)
      rw [dite_eq_left h]
      exact hf ⟨j.val, h⟩
    · show EssentiallyIncreasing (if h : j.val < k then f ⟨j.val, h⟩ else 0)
      rw [dite_eq_right h]
      exact essentiallyIncreasing_zero
  · rw [← hsum n]
    change ∑ j : Fin m, (if h : j.val < k then f ⟨j.val, h⟩ else 0) (n.val + 1)
        = ∑ j : Fin k, f j (n.val + 1)
    have hzero : ∀ j ∈ (Finset.univ : Finset (Fin m)),
        j ∉ Finset.univ.image (Fin.castLE hkm) →
        (if h : j.val < k then f ⟨j.val, h⟩ else 0) (n.val + 1) = 0 := by
      intro j _ hj
      have hjv : ¬ j.val < k := by
        intro hjv
        apply hj
        rw [Finset.mem_image]
        exact ⟨⟨j.val, hjv⟩, Finset.mem_univ _, Fin.ext rfl⟩
      rw [dite_eq_right hjv]
      rfl
    rw [← Finset.sum_subset (Finset.subset_univ _) hzero,
      Finset.sum_image (fun a _ b _ hab => Fin.castLE_injective hkm hab)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h' : (Fin.castLE hkm i).val < k := i.isLt
    rw [dite_eq_left h']
    rfl

/-- The lower bound: ten functions do not suffice.
Following the official solution, take `xₙ = -(n + 1)`. For each `n` the
support `S(n) = {i | fᵢ(n) ≠ 0}` is nonempty, and there are only
`2¹⁰ - 1 = 1023 < 2022` nonempty subsets of a ten-element set, so two
supports coincide, contradicting the essentially increasing condition
because `x` is strictly decreasing. -/
lemma not_good_ten : ¬ Good 10 := by
  intro h
  obtain ⟨f, hf, hsum⟩ := h fun n => -((n.val : ℝ) + 1)
  set S : Fin 2022 → Finset (Fin 10) := fun n =>
    Finset.univ.filter fun i => f i (n.val + 1) ≠ 0 with hSdef
  have hne : ∀ n : Fin 2022, (S n).Nonempty := by
    intro n
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have h0 : ∑ i : Fin 10, f i (n.val + 1) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_contra hfi
      have hi : i ∈ S n := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hfi⟩
      rw [hne] at hi
      exact absurd hi (Finset.notMem_empty i)
    rw [hsum n] at h0
    simp only [neg_eq_zero] at h0
    have hpos : (0:ℝ) < (n.val : ℝ) + 1 := by positivity
    linarith
  have hcard : ((Finset.univ : Finset (Finset (Fin 10))) \ {∅}).card
      < (Finset.univ : Finset (Fin 2022)).card := by
    have e1 : (Finset.univ : Finset (Finset (Fin 10))).card = 2 ^ 10 := by
      rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
    have e2 : ((Finset.univ : Finset (Finset (Fin 10))) \ {∅}).card = 2 ^ 10 - 1 := by
      rw [Finset.card_sdiff, Finset.singleton_inter_of_mem (Finset.mem_univ ∅),
        Finset.card_singleton, e1]
    rw [e2, Finset.card_univ, Fintype.card_fin]
    norm_num
  obtain ⟨a, _, b, _, hab, hSab⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := (Finset.univ : Finset (Fin 2022)))
      (t := ((Finset.univ : Finset (Finset (Fin 10))) \ {∅}))
      hcard
      (f := S)
      (fun n _ => Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ _, fun hc =>
          (Finset.nonempty_iff_ne_empty.mp (hne n)) (Finset.mem_singleton.mp hc)⟩)
  have key : ∀ a b : Fin 2022, a < b → S a = S b → False := by
    intro a b hablt hSab
    have hle : ∀ i : Fin 10, f i (a.val + 1) ≤ f i (b.val + 1) := by
      intro i
      by_cases hi : i ∈ S a
      · have hi' : i ∈ S b := hSab ▸ hi
        have hineq : (a.val : ℝ) + 1 ≤ (b.val : ℝ) + 1 := by
          have hval : a.val ≤ b.val := Nat.le_of_lt hablt
          exact_mod_cast Nat.add_le_add_right hval 1
        exact hf i _ _ hineq
          (Finset.mem_filter.mp (show i ∈ Finset.univ.filter
            (fun i => f i (a.val + 1) ≠ 0) from hi)).2
          (Finset.mem_filter.mp (show i ∈ Finset.univ.filter
            (fun i => f i (b.val + 1) ≠ 0) from hi')).2
      · have hi' : i ∉ S b := fun h => hi (hSab.symm ▸ h)
        have h0 : f i (a.val + 1) = 0 := by
          by_contra hc
          exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hc⟩)
        have h0' : f i (b.val + 1) = 0 := by
          by_contra hc
          exact hi' (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hc⟩)
        rw [h0, h0']
    have hsumle : ∑ i : Fin 10, f i (a.val + 1) ≤ ∑ i : Fin 10, f i (b.val + 1) :=
      Finset.sum_le_sum fun i _ => hle i
    rw [hsum a, hsum b] at hsumle
    simp only [neg_le_neg_iff] at hsumle
    have hval : b.val ≤ a.val := by
      have h1 : (b.val : ℝ) ≤ a.val := by linarith
      exact_mod_cast h1
    exact (not_le_of_gt hablt) hval
  rcases lt_trichotomy a b with hlt | heq | hgt
  · exact key a b hlt hSab
  · exact absurd heq hab
  · exact key b a hgt hSab.symm

/-! ### The construction: eleven functions suffice

We follow the inductive construction from the official solution (see
also Evan Chen's USAMO 2022 notes). For `N = 2¹¹ - 1 = 2047` and any
choice of target values `x₁, …, x_N`, we build `11` essentially
increasing functions, finitely supported on `{1, …, N}`, whose pointwise
sum equals `x`. Every position `n` has a *level* `lvl n = ⌊log₂ n⌋ + 1`;
writing `cval n = 2^(lvl n) - 1 - n`, the `j`-th function is the
"corrector" `xₙ - cval n * B` on its own level and the constant
`2ʲ * B` on the `j`-th bit of `cval n` on higher levels, where `B` is
chosen larger than all values and all consecutive differences of `x`. -/

/-- The level of `n`: for `n ≥ 1` this is the unique `ℓ ≥ 1` with
`2^(ℓ-1) ≤ n < 2^ℓ`. -/
def lvl (n : ℕ) : ℕ := Nat.log 2 n + 1

lemma lvl_pos (n : ℕ) : 1 ≤ lvl n := Nat.le_add_left 1 _

lemma pow_lvl_sub_one_le {n : ℕ} (hn : 1 ≤ n) : 2 ^ (lvl n - 1) ≤ n := by
  have e : lvl n - 1 = Nat.log 2 n := Nat.add_sub_cancel _ _
  rw [e]
  exact Nat.pow_log_le_self 2 (by omega)

lemma lt_pow_lvl (n : ℕ) : n < 2 ^ lvl n :=
  Nat.lt_pow_succ_log_self (by norm_num) n

lemma lvl_le_of_le {n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ 2047) : lvl n ≤ 11 := by
  by_contra hc
  push Not at hc
  have h3 : 11 ≤ Nat.log 2 n := by
    have h12 : 12 ≤ Nat.log 2 n + 1 := hc
    omega
  have h4 : (2:ℕ) ^ 11 ≤ n :=
    le_trans (Nat.pow_le_pow_right (by norm_num) h3) (Nat.pow_log_le_self 2 (by omega))
  norm_num at h4
  omega

lemma lvl_mono {m n : ℕ} (h : m ≤ n) : lvl m ≤ lvl n := by
  have h' := Nat.log_mono_right (b := 2) h
  show Nat.log 2 m + 1 ≤ Nat.log 2 n + 1
  omega

lemma lvl_eq_of_mem {m ℓ : ℕ} (h1 : 2 ^ (ℓ - 1) ≤ m) (h2 : m < 2 ^ ℓ) : lvl m = ℓ := by
  have hℓ : 1 ≤ ℓ := by
    by_contra hc
    push Not at hc
    interval_cases ℓ
    simp at h1 h2
    omega
  have hm : m ≠ 0 := by
    have hpos : 0 < (2:ℕ) ^ (ℓ - 1) := pow_pos (by norm_num) _
    omega
  have hlo : ℓ - 1 ≤ Nat.log 2 m := Nat.le_log_of_pow_le (by norm_num) h1
  have hhi : Nat.log 2 m < ℓ := Nat.log_lt_of_lt_pow hm h2
  show Nat.log 2 m + 1 = ℓ
  omega

/-- The complement of `n` inside its level. -/
def cval (n : ℕ) : ℕ := 2 ^ lvl n - 1 - n

lemma cval_lt {n : ℕ} (hn : 1 ≤ n) : cval n < 2 ^ (lvl n - 1) := by
  have h1 := pow_lvl_sub_one_le hn
  have h2 := lt_pow_lvl n
  have h3 := lvl_pos n
  have h4 : (2:ℕ) ^ lvl n = 2 * 2 ^ (lvl n - 1) := by
    nth_rewrite 1 [← Nat.sub_add_cancel h3]
    rw [pow_succ, mul_comm]
  show 2 ^ lvl n - 1 - n < _
  omega

/-- Extension of the target tuple to all naturals
(zero outside `[1, 2022]`). -/
def xe (x : Fin 2022 → ℝ) (m : ℕ) : ℝ :=
  if h : 1 ≤ m ∧ m ≤ 2022 then x ⟨m - 1, by omega⟩ else 0

lemma xe_apply (x : Fin 2022 → ℝ) (n : Fin 2022) : xe x (n.val + 1) = x n := by
  have h : 1 ≤ n.val + 1 ∧ n.val + 1 ≤ 2022 :=
    ⟨Nat.le_add_left 1 n.val, Nat.succ_le_of_lt n.isLt⟩
  unfold xe
  rw [dite_eq_left h]
  congr 1

/-- A constant dominating all values and all consecutive differences
of `xe`. -/
noncomputable def Bnd (x : Fin 2022 → ℝ) : ℝ :=
  1 + ∑ m ∈ Finset.range 2050, (|xe x m| + |xe x (m + 1) - xe x m|)

lemma Bnd_pos (x : Fin 2022 → ℝ) : 0 < Bnd x := by
  have h : (0:ℝ) ≤ ∑ m ∈ Finset.range 2050, (|xe x m| + |xe x (m + 1) - xe x m|) :=
    Finset.sum_nonneg fun m _ => add_nonneg (abs_nonneg _) (abs_nonneg _)
  have h2 : Bnd x = 1 + ∑ m ∈ Finset.range 2050, (|xe x m| + |xe x (m + 1) - xe x m|) := rfl
  linarith

lemma abs_xe_le (x : Fin 2022 → ℝ) {m : ℕ} (hm : m ≤ 2047) : |xe x m| ≤ Bnd x - 1 := by
  have h := Finset.single_le_sum
    (f := fun m => |xe x m| + |xe x (m + 1) - xe x m|)
    (fun (i : ℕ) (_ : i ∈ Finset.range 2050) =>
      add_nonneg (abs_nonneg (xe x i)) (abs_nonneg (xe x (i + 1) - xe x i)))
    (Finset.mem_range.mpr (by omega : m < 2050))
  have h1 : |xe x m| ≤ |xe x m| + |xe x (m + 1) - xe x m| :=
    le_add_of_nonneg_right (abs_nonneg _)
  have h2 : Bnd x = 1 + ∑ m ∈ Finset.range 2050, (|xe x m| + |xe x (m + 1) - xe x m|) := rfl
  linarith

lemma abs_gap_le (x : Fin 2022 → ℝ) {m : ℕ} (hm : m ≤ 2047) :
    |xe x (m + 1) - xe x m| ≤ Bnd x - 1 := by
  have h := Finset.single_le_sum
    (f := fun m => |xe x m| + |xe x (m + 1) - xe x m|)
    (fun (i : ℕ) (_ : i ∈ Finset.range 2050) =>
      add_nonneg (abs_nonneg (xe x i)) (abs_nonneg (xe x (i + 1) - xe x i)))
    (Finset.mem_range.mpr (by omega : m < 2050))
  have h1 : |xe x (m + 1) - xe x m| ≤ |xe x m| + |xe x (m + 1) - xe x m| :=
    le_add_of_nonneg_left (abs_nonneg _)
  have h2 : Bnd x = 1 + ∑ m ∈ Finset.range 2050, (|xe x m| + |xe x (m + 1) - xe x m|) := rfl
  linarith

/-- The value of the `j`-th constructed function at the integer point
`n`: zero outside `[1, 2047]`; on its own level (`j = lvl n - 1`) it is
the corrector `xe x n - cval n * Bnd x`, and on higher levels it is the
bit contribution `2^j * Bnd x` when bit `j` of `cval n` is set. -/
noncomputable def gval (x : Fin 2022 → ℝ) (j n : ℕ) : ℝ :=
  if 1 ≤ n ∧ n ≤ 2047 then
    (if (cval n).testBit j = true then (2:ℝ) ^ j * Bnd x else 0) +
    (if j = lvl n - 1 then xe x n - (cval n : ℝ) * Bnd x else 0)
  else 0

lemma gval_of_mem (x : Fin 2022 → ℝ) {j n : ℕ} (h : 1 ≤ n ∧ n ≤ 2047) :
    gval x j n =
      (if (cval n).testBit j = true then (2:ℝ) ^ j * Bnd x else 0) +
      (if j = lvl n - 1 then xe x n - (cval n : ℝ) * Bnd x else 0) :=
  ite_eq_left h

lemma gval_of_not_mem (x : Fin 2022 → ℝ) {j n : ℕ} (h : ¬ (1 ≤ n ∧ n ≤ 2047)) :
    gval x j n = 0 :=
  ite_eq_right h

lemma testBit_cval_eq_false_of_ge {j n : ℕ} (hn : 1 ≤ n) (h : lvl n - 1 ≤ j) :
    (cval n).testBit j = false :=
  Nat.testBit_eq_false_of_lt
    (lt_of_lt_of_le (cval_lt hn) (Nat.pow_le_pow_right (by norm_num) h))

lemma if_testBit_false {tb : Bool} (h : tb = false) {a : ℝ} :
    (if tb = true then a else (0:ℝ)) = 0 :=
  ite_eq_right fun ht => Bool.false_ne_true (h.symm.trans ht)

lemma if_testBit_true {tb : Bool} (h : tb = true) {a : ℝ} :
    (if tb = true then a else (0:ℝ)) = a :=
  ite_eq_left h

/-- Within one level, the corrector values strictly increase from `m`
to `m + 1`, because `Bnd x` dominates the consecutive differences
of `xe`. -/
lemma gval_step_corrector (x : Fin 2022 → ℝ) {j m : ℕ}
    (hm : 1 ≤ m) (hjm : j = lvl m - 1) (hm1 : m + 1 ≤ 2 ^ lvl m - 1)
    (hm2 : m + 1 ≤ 2047) :
    gval x j m ≤ gval x j (m + 1) := by
  have hm1' : 1 ≤ m + 1 := by omega
  have hmlm : lvl (m + 1) = lvl m := by
    apply lvl_eq_of_mem
    · exact le_trans (pow_lvl_sub_one_le hm) (Nat.le_add_right m 1)
    · exact lt_of_le_of_lt hm1
        (Nat.sub_lt (pow_pos (by norm_num : (0:ℕ) < 2) _) (by norm_num))
  rw [gval_of_mem x ⟨hm, by omega⟩, gval_of_mem x ⟨hm1', hm2⟩]
  have hbit1 : (cval m).testBit j = false := testBit_cval_eq_false_of_ge hm (by omega)
  have hbit2 : (cval (m + 1)).testBit j = false := by
    apply testBit_cval_eq_false_of_ge hm1'
    rw [hmlm]
    omega
  rw [if_testBit_false hbit1, if_testBit_false hbit2, hmlm, ite_eq_left hjm, ite_eq_left hjm, zero_add, zero_add]
  have hcv : cval (m + 1) + 1 = cval m := by
    have e : cval (m + 1) = 2 ^ lvl m - 1 - (m + 1) := by
      show 2 ^ lvl (m + 1) - 1 - (m + 1) = 2 ^ lvl m - 1 - (m + 1)
      rw [hmlm]
    show cval (m + 1) + 1 = 2 ^ lvl m - 1 - m
    rw [e]
    omega
  have hcvr : (cval (m + 1) : ℝ) + 1 = (cval m : ℝ) := by exact_mod_cast hcv
  have hgap := abs_gap_le x (by omega : m ≤ 2047)
  have hB := Bnd_pos x
  have h2 : -(xe x (m + 1) - xe x m) ≤ Bnd x - 1 := le_trans (neg_le_abs _) hgap
  have h3 : (cval m : ℝ) * Bnd x = (cval (m + 1) : ℝ) * Bnd x + Bnd x := by
    rw [← hcvr]
    ring
  linarith

/-- The constructed values are monotone at integer points (on their
support); this is the heart of the essentially increasing property. -/
lemma gval_mono (x : Fin 2022 → ℝ) {j ns nt : ℕ}
    (hns : 1 ≤ ns) (hle : ns ≤ nt) (htt : nt ≤ 2047)
    (hs : gval x j ns ≠ 0) (ht : gval x j nt ≠ 0) :
    gval x j ns ≤ gval x j nt := by
  have hnts : ns ≤ 2047 := le_trans hle htt
  have hnt1 : 1 ≤ nt := le_trans hns hle
  have hℓ : lvl ns ≤ lvl nt := lvl_mono hle
  have hℓs1 : 1 ≤ lvl ns := lvl_pos ns
  have hℓt1 : 1 ≤ lvl nt := lvl_pos nt
  have hj_s : j ≤ lvl ns - 1 := by
    by_contra hj
    push Not at hj
    have hbit : (cval ns).testBit j = false := testBit_cval_eq_false_of_ge hns (by omega)
    have hcorr : j ≠ lvl ns - 1 := by omega
    rw [gval_of_mem x ⟨hns, hnts⟩] at hs
    rw [if_testBit_false hbit, ite_eq_right hcorr] at hs
    exact hs (add_zero _)
  have hj_t : j ≤ lvl nt - 1 := by
    by_contra hj
    push Not at hj
    have hbit : (cval nt).testBit j = false := testBit_cval_eq_false_of_ge hnt1 (by omega)
    have hcorr : j ≠ lvl nt - 1 := by omega
    rw [gval_of_mem x ⟨hnt1, htt⟩] at ht
    rw [if_testBit_false hbit, ite_eq_right hcorr] at ht
    exact ht (add_zero _)
  rcases eq_or_lt_of_le hj_s with hjs | hjs
  · rcases eq_or_lt_of_le hj_t with hjt | hjt
    · -- both points lie in the level where `j` is the corrector
      have hℓeq : lvl ns = lvl nt := by omega
      have hlvl : ∀ d : ℕ, ns + d ≤ nt → lvl (ns + d) = lvl ns := by
        intro d hd
        apply lvl_eq_of_mem
        · exact le_trans (pow_lvl_sub_one_le hns) (Nat.le_add_right ns d)
        · have e1 := lt_pow_lvl nt
          rw [← hℓeq] at e1
          exact lt_of_le_of_lt hd e1
      have chain : ∀ d : ℕ, ns + d ≤ nt → gval x j ns ≤ gval x j (ns + d) := by
        intro d
        induction d with
        | zero => intro _; exact le_refl _
        | succ d ih =>
            intro hd
            have hd' : ns + d ≤ nt := by omega
            have hstep : gval x j (ns + d) ≤ gval x j (ns + d + 1) := by
              apply gval_step_corrector x (by omega)
              · rw [hlvl d hd']
                exact hjs
              · rw [hlvl d hd']
                have e1 := lt_pow_lvl nt
                rw [← hℓeq] at e1
                omega
              · omega
            exact le_trans (ih hd') hstep
      have hfinal := chain (nt - ns) (by omega)
      rw [Nat.add_sub_cancel' hle] at hfinal
      exact hfinal
    · -- corrector at `ns`, bit contribution at `nt`
      have hbits : (cval ns).testBit j = false := testBit_cval_eq_false_of_ge hns (by omega)
      have hbitt : (cval nt).testBit j = true := by
        by_contra hc
        rw [Bool.not_eq_true] at hc
        rw [gval_of_mem x ⟨hnt1, htt⟩] at ht
        rw [if_testBit_false hc, ite_eq_right (by omega : j ≠ lvl nt - 1)] at ht
        exact ht (add_zero _)
      have eL : gval x j ns = xe x ns - (cval ns : ℝ) * Bnd x := by
        rw [gval_of_mem x ⟨hns, hnts⟩, if_testBit_false hbits, ite_eq_left hjs, zero_add]
      have eR : gval x j nt = (2:ℝ) ^ j * Bnd x := by
        rw [gval_of_mem x ⟨hnt1, htt⟩, if_testBit_true hbitt,
          ite_eq_right (by omega : j ≠ lvl nt - 1), add_zero]
      rw [eL, eR]
      have hB := Bnd_pos x
      have hxe := abs_xe_le x hnts
      have h2j : (1:ℝ) ≤ (2:ℝ) ^ j := one_le_pow₀ (by norm_num)
      have h1 : xe x ns ≤ |xe x ns| := le_abs_self _
      have h2 : (0:ℝ) ≤ (cval ns : ℝ) * Bnd x := mul_nonneg (Nat.cast_nonneg _) (le_of_lt hB)
      have h3 : Bnd x ≤ (2:ℝ) ^ j * Bnd x := by
        nth_rewrite 1 [← one_mul (Bnd x)]
        exact mul_le_mul_of_nonneg_right h2j (le_of_lt hB)
      linarith
  · rcases eq_or_lt_of_le hj_t with hjt | hjt
    · omega
    · -- bit contributions at both points
      have hbitst : (cval ns).testBit j = true := by
        by_contra hc
        rw [Bool.not_eq_true] at hc
        rw [gval_of_mem x ⟨hns, hnts⟩] at hs
        rw [if_testBit_false hc, ite_eq_right (by omega : j ≠ lvl ns - 1)] at hs
        exact hs (add_zero _)
      have hbittt : (cval nt).testBit j = true := by
        by_contra hc
        rw [Bool.not_eq_true] at hc
        rw [gval_of_mem x ⟨hnt1, htt⟩] at ht
        rw [if_testBit_false hc, ite_eq_right (by omega : j ≠ lvl nt - 1)] at ht
        exact ht (add_zero _)
      have eL : gval x j ns = (2:ℝ) ^ j * Bnd x := by
        rw [gval_of_mem x ⟨hns, hnts⟩, if_testBit_true hbitst,
          ite_eq_right (by omega : j ≠ lvl ns - 1), add_zero]
      have eR : gval x j nt = (2:ℝ) ^ j * Bnd x := by
        rw [gval_of_mem x ⟨hnt1, htt⟩, if_testBit_true hbittt,
          ite_eq_right (by omega : j ≠ lvl nt - 1), add_zero]
      rw [eL, eR]

/-- Binary expansion: a natural number is the sum of its bit values. -/
lemma sum_range_testBit (c : ℕ) {L : ℕ} (h : c < 2 ^ L) :
    ∑ i ∈ Finset.range L, (if c.testBit i = true then 2 ^ i else 0) = c := by
  induction L generalizing c with
  | zero =>
      have hc : c = 0 := by
        have h' : c < 1 := by simpa using h
        omega
      simp [hc]
  | succ L ih =>
      rw [Finset.sum_range_succ']
      have hts : ∀ i : ℕ, c.testBit (i + 1) = (c / 2).testBit i :=
        fun i => Nat.testBit_succ c i
      have hrest : (∑ i ∈ Finset.range L, (if c.testBit (i + 1) = true then 2 ^ (i + 1) else 0))
          = 2 * ∑ i ∈ Finset.range L, (if (c / 2).testBit i = true then 2 ^ i else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hts i]
        by_cases hb : (c / 2).testBit i = true
        · rw [ite_eq_left hb, ite_eq_left hb, pow_succ]
          ring
        · rw [ite_eq_right hb, ite_eq_right hb, mul_zero]
      have hL : c / 2 < 2 ^ L := by
        rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)]
        calc c < 2 ^ (L + 1) := h
        _ = 2 ^ L * 2 := pow_succ 2 L
      rw [hrest, ih (c / 2) hL]
      have h0 : (if c.testBit 0 = true then 2 ^ 0 else 0) = c % 2 := by
        rw [Nat.testBit_zero]
        rcases Nat.mod_two_eq_zero_or_one c with h1 | h1 <;> simp [h1]
      rw [h0, add_comm]
      exact Nat.mod_add_div c 2

/-- Real version of the binary expansion. -/
lemma sum_range_testBit_real (c : ℕ) {L : ℕ} (h : c < 2 ^ L) :
    ∑ i ∈ Finset.range L, (if c.testBit i = true then (2:ℝ) ^ i else 0) = (c : ℝ) := by
  have h2 := sum_range_testBit c h
  have h3 : ((∑ i ∈ Finset.range L, (if c.testBit i = true then 2 ^ i else 0) : ℕ) : ℝ)
      = (c : ℝ) := by exact_mod_cast h2
  rw [Nat.cast_sum] at h3
  push_cast at h3
  exact h3

open Classical in
/-- The `j`-th constructed function on the real line; it is nonzero only
at the integers `1, …, 2047`. -/
noncomputable def ffun (x : Fin 2022 → ℝ) (j : Fin 11) (t : ℝ) : ℝ :=
  if t = (Nat.floor t : ℝ) then gval x j.val (Nat.floor t) else 0

lemma ffun_apply_nat (x : Fin 2022 → ℝ) (j : Fin 11) (n : ℕ) :
    ffun x j (n : ℝ) = gval x j.val n := by
  show (if ((n : ℝ) = ((Nat.floor (n : ℝ)) : ℝ)) then gval x j.val (Nat.floor (n : ℝ)) else 0)
      = gval x j.val n
  rw [Nat.floor_natCast]
  exact ite_eq_left rfl

lemma ess_incr_ffun (x : Fin 2022 → ℝ) (j : Fin 11) :
    EssentiallyIncreasing (ffun x j) := by
  intro s t hst hs ht
  by_cases hfs : s = (Nat.floor s : ℝ)
  swap
  · exact absurd (ite_eq_right hfs) hs
  by_cases hft : t = (Nat.floor t : ℝ)
  swap
  · exact absurd (ite_eq_right hft) ht
  have hgs : gval x j.val (Nat.floor s) ≠ 0 := by
    have e : ffun x j s = gval x j.val (Nat.floor s) := ite_eq_left hfs
    rwa [e] at hs
  have hgt : gval x j.val (Nat.floor t) ≠ 0 := by
    have e : ffun x j t = gval x j.val (Nat.floor t) := ite_eq_left hft
    rwa [e] at ht
  have hbs : 1 ≤ Nat.floor s ∧ Nat.floor s ≤ 2047 := by
    by_contra hb
    exact hgs (gval_of_not_mem x hb)
  have hbt : 1 ≤ Nat.floor t ∧ Nat.floor t ≤ 2047 := by
    by_contra hb
    exact hgt (gval_of_not_mem x hb)
  have e1 : ffun x j s = gval x j.val (Nat.floor s) := ite_eq_left hfs
  have e2 : ffun x j t = gval x j.val (Nat.floor t) := ite_eq_left hft
  rw [e1, e2]
  exact gval_mono x hbs.1 (Nat.floor_le_floor hst) hbt.2 hgs hgt

/-- The sum identity: at every integer point `n ∈ [1, 2047]` the eleven
constructed functions sum to the target value `xe x n`. -/
lemma sum_ffun (x : Fin 2022 → ℝ) {n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ 2047) :
    ∑ j : Fin 11, ffun x j (n : ℝ) = xe x n := by
  rw [Finset.sum_congr rfl (fun (j : Fin 11) _ => ffun_apply_nat x j n)]
  rw [Finset.sum_congr rfl (fun (j : Fin 11) _ => gval_of_mem x (j := (j : ℕ)) (n := n) ⟨h1, h2⟩)]
  rw [Finset.sum_add_distrib]
  have hbit : (∑ j : Fin 11, if (cval n).testBit (j : ℕ) = true then (2:ℝ) ^ (j : ℕ) * Bnd x
      else 0) = (cval n : ℝ) * Bnd x := by
    rw [Fin.sum_univ_eq_sum_range
      (fun v => if (cval n).testBit v = true then (2:ℝ) ^ v * Bnd x else 0) 11]
    have key : (∑ v ∈ Finset.range 11, if (cval n).testBit v = true then (2:ℝ) ^ v else 0)
        = (cval n : ℝ) := by
      apply sum_range_testBit_real
      have h1' := cval_lt h1
      have h2' := lvl_le_of_le h1 h2
      calc cval n < 2 ^ (lvl n - 1) := h1'
      _ ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ < 2 ^ 11 := by norm_num
    have hfact : (∑ v ∈ Finset.range 11,
        if (cval n).testBit v = true then (2:ℝ) ^ v * Bnd x else 0)
        = Bnd x * ∑ v ∈ Finset.range 11,
            if (cval n).testBit v = true then (2:ℝ) ^ v else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      by_cases hb : (cval n).testBit v = true
      · rw [ite_eq_left hb, ite_eq_left hb, mul_comm]
      · rw [ite_eq_right hb, ite_eq_right hb, mul_zero]
    rw [hfact, key, mul_comm]
  have hcorr : (∑ j : Fin 11, if (j : ℕ) = lvl n - 1 then xe x n - (cval n : ℝ) * Bnd x
      else 0) = xe x n - (cval n : ℝ) * Bnd x := by
    rw [Fin.sum_univ_eq_sum_range
      (fun v => if v = lvl n - 1 then xe x n - (cval n : ℝ) * Bnd x else 0) 11]
    have hmem : lvl n - 1 ∈ Finset.range 11 := by
      rw [Finset.mem_range]
      have h2' := lvl_le_of_le h1 h2
      have h1' := lvl_pos n
      omega
    rw [Finset.sum_ite_eq', ite_eq_left hmem]
  rw [hbit, hcorr]
  ring

/-- Eleven functions suffice: the explicit construction works for every
choice of target values. -/
lemma good_eleven : Good 11 := by
  intro x
  refine ⟨ffun x, ess_incr_ffun x, fun n => ?_⟩
  have h1 : 1 ≤ n.val + 1 := Nat.le_add_left 1 n.val
  have h2 : n.val + 1 ≤ 2047 := le_trans (Nat.succ_le_of_lt n.isLt) (by norm_num)
  have e : ((n.val + 1 : ℕ) : ℝ) = (n.val : ℝ) + 1 := by
    rw [Nat.cast_add, Nat.cast_one]
  rw [← e, sum_ffun x h1 h2, xe_apply x n]

snip end

problem usa2022_p5 : IsLeast {k | Good k} solution := by
  constructor
  · exact good_eleven
  · intro k hk
    by_contra hc
    push Not at hc
    have h10 : k ≤ 10 := by
      have h' : k < 11 := hc
      omega
    exact not_good_ten (Good.mono h10 hk)

end Usa2022P5
