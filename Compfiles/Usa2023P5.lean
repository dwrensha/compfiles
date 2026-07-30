/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Ring.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2023, Problem 5

Let n be an integer greater than 2. We will be arranging the numbers
1, 2, ... n² into an n × n grid. Such an arrangement is called *row-valid*
if the numbers in each row can be permuted to make an arithmetic progression.
Similarly, such an arrangement is called *column-valid* if the numbers
in each column can be permuted to make an arithmetic progression.

Determine the values of n for which it possible to transform
any row-valid arrangement into a column-valid arrangement by permuting
the numbers in each row.

-/

namespace Usa2023P5

def PermutedArithSeq {n : ℕ} (hn : 0 < n) (a : Fin n ↪ Fin (n ^ 2)) : Prop :=
    ∃ p : Fin n → Fin n, p.Bijective ∧
      ∃ k : ℕ, ∀ m : Fin n, (a (p m)).val = a (p ⟨0, hn⟩) + m.val * k

def row_valid {n : ℕ} (hn : 0 < n) (a : Fin n → Fin n → Fin (n ^ 2)) (ha : a.Injective2) : Prop :=
    ∀ r : Fin n, PermutedArithSeq hn ⟨(a r ·), Function.Injective2.right ha r⟩

def col_valid {n : ℕ} (hn : 0 < n) (a : Fin n → Fin n → Fin (n ^ 2)) (ha : a.Injective2) : Prop :=
    ∀ c : Fin n, PermutedArithSeq hn ⟨(a · c), Function.Injective2.left ha c⟩

theorem injective_of_permuted_rows {α β γ : Type}
    {f : α → β → γ} (hf : f.Injective2) {p : α → β → β} (hp : ∀ a, (p a).Injective) :
    Function.Injective2 (fun r c ↦ f r (p r c)) := by
  intro a1 a2 b1 b2 hab
  obtain ⟨ha1, hp1⟩ := hf hab
  rw [ha1] at *
  rw [hp a2 hp1]
  simp only [and_self]

determine solution_set : Set ℕ := { n | n.Prime }

snip begin

/-- The Anton Trygub counterexample construction for composite `n` with prime divisor `q`,
at the level of natural number values. Row `0` is `0, …, n-1`; rows `1 ≤ r ≤ q` are
arithmetic progressions with difference `q` filling `n, …, n*q+n-1`; the remaining rows
contain the leftover numbers in reading order. -/
def trygub (n q r c : ℕ) : ℕ :=
  if r = 0 then c else if r ≤ q then n + (r - 1) + q * c else n * q + n + (r - q - 1) * n + c

lemma trygub_row_zero (n q c : ℕ) : trygub n q 0 c = c := rfl

lemma trygub_lt {n q r c : ℕ} (hr : r < n) (hc : c < n) (hq : 2 ≤ q) (hqn : q + 1 ≤ n) :
    trygub n q r c < n ^ 2 := by
  unfold trygub
  split_ifs with h0 hle
  · have hn1 : 1 ≤ n := by omega
    calc c < n := hc
      _ ≤ n ^ 2 := by rw [pow_two]; exact Nat.le_mul_of_pos_left n (by omega)
  · have hqc : q * c + q ≤ n * q := by
      calc q * c + q = q * (c + 1) := by rw [← Nat.mul_succ]
        _ ≤ q * n := Nat.mul_le_mul_left q hc
        _ = n * q := Nat.mul_comm q n
    have hkey : n + (r - 1) + q * c < n * (q + 1) := by
      rw [Nat.mul_succ]
      omega
    calc n + (r - 1) + q * c < n * (q + 1) := hkey
      _ ≤ n * n := Nat.mul_le_mul_left n hqn
      _ = n ^ 2 := (pow_two n).symm
  · have hle : q < r := not_le.mp hle
    have hqn2 : q + 2 ≤ n := by omega
    have h3 : (r - q - 1) * n + (n * q + 2 * n) ≤ n * n := by
      have h31 : (r - q - 1) * n ≤ (n - (q + 2)) * n := Nat.mul_le_mul_right n (by omega)
      have h32 : (n - (q + 2)) * n + (n * q + 2 * n) = n * n := by
        rw [Nat.mul_comm n q, ← add_mul, ← Nat.add_mul, Nat.sub_add_cancel hqn2]
      omega
    have hle2 : n * q + 2 * n ≤ n * n := by
      have := Nat.mul_le_mul_right n hqn2
      rw [add_mul, Nat.mul_comm q n] at this
      exact this
    rw [pow_two]
    omega

lemma trygub_eq_zero {n q r c : ℕ} (hn : 2 ≤ n) :
    trygub n q r c = 0 → r = 0 ∧ c = 0 := by
  unfold trygub
  split_ifs with h0 hle
  · exact fun h ↦ ⟨h0, h⟩
  · omega
  · omega

/-- Rows `1 ≤ r ≤ q` contain values in `[n, n*q+n)`. -/
lemma trygub_mid_bounds {n q r c : ℕ} (h0 : r ≠ 0) (hle : r ≤ q) (hc : c < n) :
    n ≤ trygub n q r c ∧ trygub n q r c < n * q + n := by
  unfold trygub
  rw [if_neg h0, if_pos hle]
  have hqc : q * c + q ≤ n * q := by
    calc q * c + q = q * (c + 1) := by rw [← Nat.mul_succ]
      _ ≤ q * n := Nat.mul_le_mul_left q hc
      _ = n * q := Nat.mul_comm q n
  omega

/-- Rows `r > q` contain values in `[n*q+n, n^2)`. -/
lemma trygub_top_bound (n q : ℕ) {r : ℕ} (c : ℕ) (hle : ¬ r ≤ q) :
    n * q + n ≤ trygub n q r c := by
  unfold trygub
  rw [if_neg (by omega : r ≠ 0), if_neg hle]
  omega

lemma trygub_last_ge {n q c : ℕ} (hq : 2 ≤ q) (hqn : q + 2 ≤ n) :
    n ^ 2 - n ≤ trygub n q (n - 1) c := by
  unfold trygub
  split_ifs with h0 hle
  · omega
  · omega
  · have e2 : (n - 1 - q - 1) * n + (q + 2) * n = n * n := by
      have e1 : n - 1 - q - 1 = n - (q + 2) := by omega
      rw [e1, ← Nat.add_mul, Nat.sub_add_cancel hqn]
    have e3 : (q + 2) * n = n * q + 2 * n := by rw [add_mul, Nat.mul_comm q n]
    rw [e3] at e2
    rw [pow_two]
    omega

lemma trygub_inj {n q r₁ r₂ c₁ c₂ : ℕ} (hn : 4 ≤ n) (hq : 2 ≤ q) (_hqn : q + 1 ≤ n)
    (hr₁ : r₁ < n) (hr₂ : r₂ < n) (hc₁ : c₁ < n) (hc₂ : c₂ < n)
    (h : trygub n q r₁ c₁ = trygub n q r₂ c₂) : r₁ = r₂ ∧ c₁ = c₂ := by
  by_cases h10 : r₁ = 0
  · by_cases h20 : r₂ = 0
    · subst h10; subst h20
      rw [trygub_row_zero, trygub_row_zero] at h
      exact ⟨rfl, h⟩
    · by_cases h2q : r₂ ≤ q
      · rw [h10, trygub_row_zero] at h
        have hb := (trygub_mid_bounds h20 h2q hc₂).1
        omega
      · rw [h10, trygub_row_zero] at h
        have hb := trygub_top_bound n q c₂ h2q
        omega
  · by_cases h20 : r₂ = 0
    · by_cases h1q : r₁ ≤ q
      · rw [h20, trygub_row_zero] at h
        have hb := (trygub_mid_bounds h10 h1q hc₁).1
        omega
      · rw [h20, trygub_row_zero] at h
        have hb := trygub_top_bound n q c₁ h1q
        omega
    · by_cases h1q : r₁ ≤ q
      · by_cases h2q : r₂ ≤ q
        · unfold trygub at h
          rw [if_neg h10, if_pos h1q, if_neg h20, if_pos h2q] at h
          have h' : r₁ - 1 + q * c₁ = r₂ - 1 + q * c₂ := by omega
          have m1 : (r₁ - 1 + q * c₁) % q = r₁ - 1 := by
            rw [Nat.add_mul_mod_self_left]
            exact Nat.mod_eq_of_lt (by omega)
          have m2 : (r₂ - 1 + q * c₂) % q = r₂ - 1 := by
            rw [Nat.add_mul_mod_self_left]
            exact Nat.mod_eq_of_lt (by omega)
          have hr1 : r₁ - 1 = r₂ - 1 := by rw [h'] at m1; exact m1.symm.trans m2
          have hr : r₁ = r₂ := by omega
          subst hr
          have hm : q * c₁ = q * c₂ := by omega
          exact ⟨rfl, mul_left_cancel₀ (by omega : q ≠ 0) hm⟩
        · have h1b := (trygub_mid_bounds h10 h1q hc₁).2
          have h2b := trygub_top_bound n q c₂ h2q
          omega
      · by_cases h2q : r₂ ≤ q
        · have h1b := trygub_top_bound n q c₁ h1q
          have h2b := (trygub_mid_bounds h20 h2q hc₂).2
          omega
        · unfold trygub at h
          rw [if_neg h10, if_neg h1q, if_neg h20, if_neg h2q] at h
          have h' : (r₁ - q - 1) * n + c₁ = (r₂ - q - 1) * n + c₂ := by omega
          have hc : c₁ = c₂ := by
            have m1 : ((r₁ - q - 1) * n + c₁) % n = c₁ := by
              rw [Nat.add_comm, Nat.add_mul_mod_self_right]
              exact Nat.mod_eq_of_lt hc₁
            have m2 : ((r₂ - q - 1) * n + c₂) % n = c₂ := by
              rw [Nat.add_comm, Nat.add_mul_mod_self_right]
              exact Nat.mod_eq_of_lt hc₂
            rw [h'] at m1
            exact m1.symm.trans m2
          subst hc
          have hr : r₁ - q - 1 = r₂ - q - 1 := by
            have m1 : ((r₁ - q - 1) * n + c₁) / n = r₁ - q - 1 := by
              rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega : 0 < n)]
              rw [Nat.div_eq_of_lt hc₁]
              omega
            have m2 : ((r₂ - q - 1) * n + c₁) / n = r₂ - q - 1 := by
              rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega : 0 < n)]
              rw [Nat.div_eq_of_lt hc₁]
              omega
            rw [h'] at m1
            exact m1.symm.trans m2
          have : r₁ = r₂ := by omega
          exact ⟨this, rfl⟩

lemma trygub_eq_add_one {n q r c : ℕ} (_hn : 4 ≤ n) (hq : 2 ≤ q)
    (_hr : r < n) (hc : c < n) (h : trygub n q r c = n + 1) : r = 2 := by
  unfold trygub at h
  split_ifs at h with h0 hle
  · omega
  · by_cases hc0 : c = 0
    · subst hc0
      rw [Nat.mul_zero, Nat.add_zero] at h
      omega
    · have hqc : q ≤ q * c := Nat.le_mul_of_pos_right q (by omega)
      omega
  · have hnq : n * 2 ≤ n * q := Nat.mul_le_mul_left n hq
    omega

lemma trygub_eq_two_mul_add_one {n q r c : ℕ} (hn : 4 ≤ n) (hq : 2 ≤ q) (hdvd : q ∣ n)
    (_hr : r < n) (hc : c < n) (h : trygub n q r c = 2 * n + 1) : r = 2 := by
  unfold trygub at h
  split_ifs at h with h0 hle
  · omega
  · have h1 : r - 1 + q * c = n + 1 := by omega
    have h2 : (r - 1 + q * c) % q = r - 1 := by
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (by omega)
    have h3 : (n + 1) % q = 1 := by
      obtain ⟨t, ht⟩ := hdvd
      rw [ht, Nat.add_comm (q * t) 1, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt hq
    rw [h1] at h2
    have h4 : r - 1 = 1 := h2.symm.trans h3
    omega
  · have hnq : n * 2 ≤ n * q := Nat.mul_le_mul_left n hq
    omega

lemma trygub_mid (n q r c : ℕ) (h0 : r ≠ 0) (hle : r ≤ q) :
    trygub n q r c = n + (r - 1) + q * c := by
  unfold trygub
  rw [if_neg h0, if_pos hle]

lemma trygub_top (n q r c : ℕ) (hle : ¬ r ≤ q) :
    trygub n q r c = n * q + n + (r - q - 1) * n + c := by
  unfold trygub
  rw [if_neg (by omega : r ≠ 0), if_neg hle]

/-- Two naturals with the same quotient and remainder mod `m` are equal. -/
lemma eq_of_div_mod_eq {v₁ v₂ m : ℕ} (hdiv : v₁ / m = v₂ / m) (hmod : v₁ % m = v₂ % m) :
    v₁ = v₂ := by
  rw [← Nat.div_add_mod v₁ m, ← Nat.div_add_mod v₂ m, hdiv, hmod]

/-- The quotient of an element of `Fin (n^2)` by `n` is again in `Fin n`. -/
lemma div_lt_of_mem {n : ℕ} (v : Fin (n ^ 2)) : v.val / n < n :=
  Nat.div_lt_of_lt_mul (by rw [← pow_two]; exact v.isLt)

/-- The common difference of a permuted arithmetic progression of length at least 2
of elements of `Fin (n^2)` is positive. -/
lemma ap_k_pos {n : ℕ} (hn : 0 < n) (h2 : 2 ≤ n) {f : Fin n → Fin (n ^ 2)} (hf : f.Injective)
    {p : Fin n → Fin n} (hp : p.Injective) {k : ℕ}
    (hk : ∀ m : Fin n, (f (p m)).val = (f (p ⟨0, hn⟩)).val + m.val * k) : 1 ≤ k := by
  by_contra h0
  have h0 : k = 0 := by omega
  subst h0
  have heq : f (p ⟨1, by omega⟩) = f (p ⟨0, hn⟩) := by
    apply Fin.ext
    rw [hk ⟨1, by omega⟩, Nat.mul_zero, Nat.add_zero]
  have h10 := hp (hf heq)
  have h13 : (1 : ℕ) = 0 := congrArg Fin.val h10
  omega

/-- For prime `n`, an arithmetic progression of length `n` whose common difference is not
divisible by `n` hits every residue class mod `n` at most once. -/
lemma ap_res_inj {n : ℕ} (hp : n.Prime) {k : ℕ} (hk : ¬ n ∣ k) (b : ℕ) {m₁ m₂ : Fin n}
    (h : (b + m₁.val * k) % n = (b + m₂.val * k) % n) : m₁ = m₂ := by
  haveI : Fact n.Prime := ⟨hp⟩
  have h' : ((b + m₁.val * k : ℕ) : ZMod n) = ((b + m₂.val * k : ℕ) : ZMod n) := by
    rw [ZMod.natCast_eq_natCast_iff']
    exact h
  push_cast at h'
  have hk0 : (k : ZMod n) ≠ 0 := by
    intro hkc
    rw [ZMod.natCast_eq_zero_iff] at hkc
    exact hk hkc
  have hmk : (m₁.val : ZMod n) * (k : ZMod n) = (m₂.val : ZMod n) * (k : ZMod n) :=
    add_left_cancel h'
  have hm : (m₁.val : ZMod n) = (m₂.val : ZMod n) := mul_right_cancel₀ hk0 hmk
  rw [ZMod.natCast_eq_natCast_iff] at hm
  have hval : m₁.val = m₂.val := by
    rw [← Nat.mod_eq_of_lt m₁.isLt, ← Nat.mod_eq_of_lt m₂.isLt]
    exact hm
  exact Fin.ext hval

/-- The Trygub arrangement, packaged as a grid of elements of `Fin (n^2)`. -/
def trygubArr (n q : ℕ) (hbound : ∀ r c : Fin n, trygub n q r.val c.val < n ^ 2) :
    Fin n → Fin n → Fin (n ^ 2) :=
  fun r c ↦ ⟨trygub n q r.val c.val, hbound r c⟩

lemma trygubArr_injective2 {n q : ℕ} (hn : 4 ≤ n) (hq : 2 ≤ q) (hqn : q + 1 ≤ n)
    (hbound : ∀ r c : Fin n, trygub n q r.val c.val < n ^ 2) :
    (trygubArr n q hbound).Injective2 := by
  intro r₁ r₂ c₁ c₂ h
  have hv : trygub n q r₁.val c₁.val = trygub n q r₂.val c₂.val := congrArg Fin.val h
  obtain ⟨hr, hc⟩ := trygub_inj hn hq hqn r₁.isLt r₂.isLt c₁.isLt c₂.isLt hv
  exact ⟨Fin.ext hr, Fin.ext hc⟩

lemma trygubArr_row_valid {n q : ℕ} (hn0 : 0 < n) (_hq : 2 ≤ q)
    (hbound : ∀ r c : Fin n, trygub n q r.val c.val < n ^ 2)
    (ha : (trygubArr n q hbound).Injective2) :
    row_valid hn0 (trygubArr n q hbound) ha := by
  intro r
  by_cases h0 : r.val = 0
  · refine ⟨id, Function.bijective_id, 1, fun m ↦ ?_⟩
    show (trygubArr n q hbound r m).val = (trygubArr n q hbound r ⟨0, hn0⟩).val + m.val * 1
    show trygub n q r.val m.val = trygub n q r.val 0 + m.val * 1
    rw [h0, trygub_row_zero, trygub_row_zero]
    omega
  · by_cases hq_le : r.val ≤ q
    · refine ⟨id, Function.bijective_id, q, fun m ↦ ?_⟩
      show (trygubArr n q hbound r m).val = (trygubArr n q hbound r ⟨0, hn0⟩).val + m.val * q
      show trygub n q r.val m.val = trygub n q r.val 0 + m.val * q
      rw [trygub_mid n q r.val m.val h0 hq_le, trygub_mid n q r.val 0 h0 hq_le,
        Nat.mul_comm q m.val]
      omega
    · refine ⟨id, Function.bijective_id, 1, fun m ↦ ?_⟩
      show (trygubArr n q hbound r m).val = (trygubArr n q hbound r ⟨0, hn0⟩).val + m.val * 1
      show trygub n q r.val m.val = trygub n q r.val 0 + m.val * 1
      rw [trygub_top n q r.val m.val hq_le, trygub_top n q r.val 0 hq_le]
      omega

snip end

problem usa2023_p5 (n : ℕ) (hn : 2 < n) :
    n ∈ solution_set ↔
    (∀ a : (Fin n → Fin n → Fin (n^2)),
      (ha : a.Injective2) → row_valid (Nat.zero_lt_of_lt hn) a ha →
        ∃ p : Fin n → Fin n → Fin n, ∃ hp : (∀ r, (p r).Injective),
            col_valid (Nat.zero_lt_of_lt hn) (fun r c ↦ a r (p r c))
              (injective_of_permuted_rows ha hp)) := by
  have hn0 : 0 < n := Nat.zero_lt_of_lt hn
  constructor
  · -- The prime case: given a row-valid arrangement, we permute each row to make
    -- every column an arithmetic progression.
    intro hnp
    have hnp' : n.Prime := hnp
    intro a ha hrow
    have hn2 : 2 ≤ n := by omega
    -- Extract the arithmetic progression data of every row.
    have ext : ∀ r : Fin n, ∃ p : Fin n → Fin n, p.Bijective ∧ ∃ k : ℕ,
        ∀ m : Fin n, (a r (p m)).val = (a r (p ⟨0, hn0⟩)).val + m.val * k := by
      intro r
      obtain ⟨p, hp, k, hk⟩ := hrow r
      exact ⟨p, hp, k, hk⟩
    choose p hp k hk using ext
    -- In a row whose difference is divisible by `n`, all values share one residue mod `n`.
    have hres : ∀ r : Fin n, n ∣ k r → ∀ j : Fin n,
        (a r j).val % n = (a r (p r ⟨0, hn0⟩)).val % n := by
      intro r hd j
      obtain ⟨m, hm⟩ := (hp r).2 j
      obtain ⟨t, ht⟩ := hd
      have e1 : m.val * k r = n * (m.val * t) := by rw [ht]; ring
      rw [← hm, hk r m, e1, Nat.add_mul_mod_self_left]
    -- Hence in such a row the quotient map `j ↦ (a r j) / n` is bijective.
    have hquot : ∀ r : Fin n, n ∣ k r → Function.Bijective
        (fun j : Fin n ↦ (⟨(a r j).val / n, div_lt_of_mem (a r j)⟩ : Fin n)) := by
      intro r hd
      rw [← Finite.injective_iff_bijective]
      intro j₁ j₂ hje
      have hdiv : (a r j₁).val / n = (a r j₂).val / n := congrArg Fin.val hje
      have hmod : (a r j₁).val % n = (a r j₂).val % n := by
        rw [hres r hd j₁, hres r hd j₂]
      have hv : (a r j₁).val = (a r j₂).val := eq_of_div_mod_eq hdiv hmod
      exact (ha.right r) (Fin.ext hv)
    by_cases hcase : ∃ r₀ : Fin n, n ∣ k r₀
    · -- Case A: some row has difference divisible by `n`; then so does every row,
      -- and each row is exactly one residue class mod `n`.
      obtain ⟨r₀, hr₀⟩ := hcase
      have hall : ∀ r : Fin n, n ∣ k r := by
        intro r
        by_contra hnr
        -- The residue map of row `r` is injective, hence hits the residue class of
        -- row `r₀`; the two rows would then share a value.
        have hinj : Function.Injective (fun m : Fin n ↦
            (⟨((a r (p r ⟨0, hn0⟩)).val + m.val * k r) % n, Nat.mod_lt _ hn0⟩ : Fin n)) := by
          intro m₁ m₂ h
          exact ap_res_inj hnp' hnr _ (congrArg Fin.val h)
        obtain ⟨m₀, hm₀⟩ := ((Finite.injective_iff_bijective).mp hinj).2
          ⟨(a r₀ (p r₀ ⟨0, hn0⟩)).val % n, Nat.mod_lt _ hn0⟩
        have hvres : (a r (p r m₀)).val % n = (a r₀ (p r₀ ⟨0, hn0⟩)).val % n := by
          have h2 : ((a r (p r ⟨0, hn0⟩)).val + m₀.val * k r) % n =
              (a r₀ (p r₀ ⟨0, hn0⟩)).val % n := congrArg Fin.val hm₀
          rw [hk r m₀]
          exact h2
        obtain ⟨j₀, hj₀⟩ := (hquot r₀ hr₀).2
          ⟨(a r (p r m₀)).val / n, div_lt_of_mem (a r (p r m₀))⟩
        have hdiv : (a r₀ j₀).val / n = (a r (p r m₀)).val / n := congrArg Fin.val hj₀
        have hmod : (a r₀ j₀).val % n = (a r (p r m₀)).val % n := by
          rw [hres r₀ hr₀ j₀]
          exact hvres.symm
        have hv : (a r₀ j₀).val = (a r (p r m₀)).val := eq_of_div_mod_eq hdiv hmod
        obtain ⟨hrr, -⟩ := ha (Fin.ext hv)
        exact hnr (hrr ▸ hr₀)
      -- The residues of the rows form a permutation of `Fin n`.
      have hσinj : Function.Injective (fun r : Fin n ↦
          (⟨(a r (p r ⟨0, hn0⟩)).val % n, Nat.mod_lt _ hn0⟩ : Fin n)) := by
        intro r₁ r₂ h
        have hmod12 : (a r₁ (p r₁ ⟨0, hn0⟩)).val % n = (a r₂ (p r₂ ⟨0, hn0⟩)).val % n :=
          congrArg Fin.val h
        obtain ⟨j₁, hj₁⟩ := (hquot r₁ (hall r₁)).2
          ⟨(a r₂ (p r₂ ⟨0, hn0⟩)).val / n, div_lt_of_mem _⟩
        have hdiv : (a r₁ j₁).val / n = (a r₂ (p r₂ ⟨0, hn0⟩)).val / n :=
          congrArg Fin.val hj₁
        have hmod : (a r₁ j₁).val % n = (a r₂ (p r₂ ⟨0, hn0⟩)).val % n := by
          rw [hres r₁ (hall r₁) j₁]
          exact hmod12
        have hv : (a r₁ j₁).val = (a r₂ (p r₂ ⟨0, hn0⟩)).val := eq_of_div_mod_eq hdiv hmod
        obtain ⟨hrr, -⟩ := ha (Fin.ext hv)
        exact hrr
      set σ : Fin n → Fin n := fun r ↦ (⟨(a r (p r ⟨0, hn0⟩)).val % n, Nat.mod_lt _ hn0⟩ : Fin n)
        with hσdef
      have hσbij : σ.Bijective := (Finite.injective_iff_bijective).mp hσinj
      set S := Equiv.ofBijective σ hσbij with hSdef
      -- In row `r`, put the value with quotient `c` in column `c`.
      set π : Fin n → Fin n → Fin n := fun r c ↦
        (Equiv.ofBijective _ (hquot r (hall r))).symm c with hπdef
      have hπinj : ∀ r, (π r).Injective := fun r ↦ by
        rw [hπdef]
        exact (Equiv.symm _).injective
      refine ⟨π, hπinj, fun c ↦ ?_⟩
      -- Every entry of the grid has value `(column) * n + (row residue)`.
      have key : ∀ r : Fin n, (a r (π r c)).val = c.val * n + (σ r).val := by
        intro r
        have h1 : (a r (π r c)).val / n = c.val := by
          have happ := Equiv.apply_symm_apply (Equiv.ofBijective _ (hquot r (hall r))) c
          exact congrArg Fin.val happ
        have h2 : (a r (π r c)).val % n = (σ r).val := hres r (hall r) (π r c)
        rw [← Nat.div_add_mod (a r (π r c)).val n, h1, h2, Nat.mul_comm]
      have keyS : ∀ m : Fin n, (a (S.symm m) (π (S.symm m) c)).val = c.val * n + m.val := by
        intro m
        rw [key (S.symm m)]
        have hsm : (σ (S.symm m)).val = m.val := congrArg Fin.val (Equiv.apply_symm_apply S m)
        rw [hsm]
      refine ⟨⇑S.symm, (S.symm).bijective, 1, fun m ↦ ?_⟩
      show (a (S.symm m) (π (S.symm m) c)).val =
          (a (S.symm ⟨0, hn0⟩) (π (S.symm ⟨0, hn0⟩) c)).val + m.val * 1
      rw [keyS m, keyS ⟨0, hn0⟩]
      show c.val * n + m.val = c.val * n + 0 + m.val * 1
      omega
    · -- Case B: every row has difference not divisible by `n`; hence every row
      -- contains every residue class mod `n` exactly once.
      have hnr : ∀ r : Fin n, ¬ n ∣ k r := fun r hd ↦ hcase ⟨r, hd⟩
      -- The residue map of each row is bijective.
      have hresb : ∀ r : Fin n, Function.Bijective (fun j : Fin n ↦
          (⟨(a r j).val % n, Nat.mod_lt _ hn0⟩ : Fin n)) := by
        intro r
        rw [← Finite.injective_iff_bijective]
        intro j₁ j₂ h
        have hmod : (a r j₁).val % n = (a r j₂).val % n := congrArg Fin.val h
        obtain ⟨m₁, hm₁⟩ := (hp r).2 j₁
        obtain ⟨m₂, hm₂⟩ := (hp r).2 j₂
        rw [← hm₁, ← hm₂] at hmod
        rw [hk r m₁, hk r m₂] at hmod
        have hmm : m₁ = m₂ := ap_res_inj hnp' (hnr r) _ hmod
        rw [← hm₁, ← hm₂, hmm]
      -- In row `r`, put the value congruent to `c` mod `n` in column `c`.
      set ψ : Fin n → Fin n → Fin n := fun r j ↦ (⟨(a r j).val % n, Nat.mod_lt _ hn0⟩ : Fin n)
        with hψdef
      set π : Fin n → Fin n → Fin n := fun r c ↦ (Equiv.ofBijective (ψ r) (hresb r)).symm c
        with hπdef
      have hπinj : ∀ r, (π r).Injective := fun r ↦ by
        rw [hπdef]
        exact (Equiv.symm _).injective
      refine ⟨π, hπinj, fun c ↦ ?_⟩
      -- Every entry of the grid is congruent to its column index mod `n`.
      have key : ∀ r : Fin n, (a r (π r c)).val % n = c.val := by
        intro r
        have happ := Equiv.apply_symm_apply (Equiv.ofBijective (ψ r) (hresb r)) c
        exact congrArg Fin.val happ
      -- The quotient map `r ↦ (a r (π r c)) / n` of each column is bijective.
      have ginj : Function.Injective (fun r : Fin n ↦
          (⟨(a r (π r c)).val / n, div_lt_of_mem (a r (π r c))⟩ : Fin n)) := by
        intro r₁ r₂ h
        have hdiv : (a r₁ (π r₁ c)).val / n = (a r₂ (π r₂ c)).val / n := congrArg Fin.val h
        have hmod : (a r₁ (π r₁ c)).val % n = (a r₂ (π r₂ c)).val % n := by
          rw [key r₁, key r₂]
        have hv : (a r₁ (π r₁ c)).val = (a r₂ (π r₂ c)).val := eq_of_div_mod_eq hdiv hmod
        exact ((injective_of_permuted_rows ha hπinj) (Fin.ext hv)).1
      set G := Equiv.ofBijective _ ((Finite.injective_iff_bijective).mp ginj) with hGdef
      -- Every entry of the grid has value `(column) + (quotient) * n`.
      have keyG : ∀ m : Fin n, (a (G.symm m) (π (G.symm m) c)).val = c.val + m.val * n := by
        intro m
        have hdiv : (a (G.symm m) (π (G.symm m) c)).val / n = m.val :=
          congrArg Fin.val (Equiv.apply_symm_apply G m)
        have hmod : (a (G.symm m) (π (G.symm m) c)).val % n = c.val := key (G.symm m)
        rw [← Nat.div_add_mod (a (G.symm m) (π (G.symm m) c)).val n, hdiv, hmod,
          Nat.mul_comm n m.val]
        omega
      refine ⟨⇑G.symm, (G.symm).bijective, n, fun m ↦ ?_⟩
      show (a (G.symm m) (π (G.symm m) c)).val =
          (a (G.symm ⟨0, hn0⟩) (π (G.symm ⟨0, hn0⟩) c)).val + m.val * n
      rw [keyG m, keyG ⟨0, hn0⟩]
      show c.val + m.val * n = c.val + 0 * n + m.val * n
      omega
  · -- If the transformation property holds then `n` is prime: we prove the
    -- contrapositive using the Trygub counterexample arrangement.
    intro htrans
    by_contra hnot
    have hnp : ¬ n.Prime := hnot
    have hn2 : 2 ≤ n := by omega
    have hn1 : n ≠ 1 := by omega
    set q := n.minFac with hqdef
    have hqprime : q.Prime := Nat.minFac_prime hn1
    have hq2 : 2 ≤ q := hqprime.two_le
    have hqdvd : q ∣ n := Nat.minFac_dvd n
    have hq1n : q + 1 ≤ n := by
      have hle : q ≤ n := Nat.le_of_dvd hn0 hqdvd
      have hne : q ≠ n := by
        intro hqq
        exact hnp (hqq ▸ hqprime)
      omega
    have hn4 : 4 ≤ n := by
      rcases lt_or_ge n 4 with h | h
      · interval_cases n
        exact absurd (by decide : Nat.Prime 3) hnp
      · exact h
    have hq2n : q + 2 ≤ n := by
      obtain ⟨t, ht⟩ := hqdvd
      have ht2 : 2 ≤ t := by
        rcases Nat.eq_zero_or_pos t with h0 | h0
        · subst h0
          rw [Nat.mul_zero] at ht
          omega
        · rcases eq_or_ne t 1 with h1 | h1
          · subst h1
            rw [Nat.mul_one] at ht
            exact absurd ht.symm (by omega : q ≠ n)
          · omega
      calc q + 2 ≤ q * 2 := by omega
        _ ≤ q * t := Nat.mul_le_mul_left q ht2
        _ = n := ht.symm
    -- The Trygub arrangement and its basic properties.
    have hbound : ∀ r c : Fin n, trygub n q r.val c.val < n ^ 2 :=
      fun r c ↦ trygub_lt r.isLt c.isLt hq2 hq1n
    set a := trygubArr n q hbound with ha_def
    have ha_inj : a.Injective2 := trygubArr_injective2 hn4 hq2 hq1n hbound
    have hrow : row_valid hn0 a ha_inj := trygubArr_row_valid hn0 hq2 hbound ha_inj
    obtain ⟨π, hπ, hcol⟩ := htrans a ha_inj hrow
    -- Extract the arithmetic progression data of every column.
    have ext : ∀ c : Fin n, ∃ ρ : Fin n → Fin n, ρ.Bijective ∧ ∃ kk : ℕ,
        ∀ m : Fin n, (a (ρ m) (π (ρ m) c)).val =
          (a (ρ ⟨0, hn0⟩) (π (ρ ⟨0, hn0⟩) c)).val + m.val * kk := by
      intro c
      obtain ⟨ρ, hρ, kk, hkk⟩ := hcol c
      exact ⟨ρ, hρ, kk, hkk⟩
    choose ρ hρ kk hkk using ext
    have h1n : 1 < n := by omega
    have hnm1 : n - 1 < n := by omega
    have kkpos : ∀ c : Fin n, 1 ≤ kk c := by
      intro c
      exact ap_k_pos hn0 hn2 ((injective_of_permuted_rows ha_inj hπ).left c) (hρ c).1 (hkk c)
    -- Every column's base value is at most `n - 1` (the entry coming from row `0`).
    have base_le : ∀ c : Fin n, (a (ρ c ⟨0, hn0⟩) (π (ρ c ⟨0, hn0⟩) c)).val ≤ n - 1 := by
      intro c
      obtain ⟨m, hm⟩ := (hρ c).2 ⟨0, hn0⟩
      have e1 : (a (ρ c m) (π (ρ c m) c)).val =
          (a (ρ c ⟨0, hn0⟩) (π (ρ c ⟨0, hn0⟩) c)).val + m.val * kk c := hkk c m
      rw [hm] at e1
      have e2 : (a ⟨0, hn0⟩ (π ⟨0, hn0⟩ c)).val = (π ⟨0, hn0⟩ c).val :=
        trygub_row_zero n q (π ⟨0, hn0⟩ c).val
      have e3 : (π ⟨0, hn0⟩ c).val < n := (π ⟨0, hn0⟩ c).isLt
      omega
    -- Every column's largest value is at least `n^2 - n` (the entry from row `n - 1`).
    have max_ge : ∀ c : Fin n, n ^ 2 - n ≤
        (a (ρ c ⟨0, hn0⟩) (π (ρ c ⟨0, hn0⟩) c)).val + (n - 1) * kk c := by
      intro c
      obtain ⟨m, hm⟩ := (hρ c).2 ⟨n - 1, hnm1⟩
      have e1 : (a (ρ c m) (π (ρ c m) c)).val =
          (a (ρ c ⟨0, hn0⟩) (π (ρ c ⟨0, hn0⟩) c)).val + m.val * kk c := hkk c m
      rw [hm] at e1
      have e2 : n ^ 2 - n ≤ (a ⟨n - 1, hnm1⟩ (π ⟨n - 1, hnm1⟩ c)).val :=
        trygub_last_ge hq2 hq2n
      have e3 : m.val * kk c ≤ (n - 1) * kk c :=
        Nat.mul_le_mul_right (kk c) (Nat.le_pred_of_lt m.isLt)
      omega
    -- Hence every common difference is `n - 1`, `n` or `n + 1`.
    have kk_bounds : ∀ c : Fin n, n - 1 ≤ kk c ∧ kk c ≤ n + 1 := by
      intro c
      have hb := base_le c
      have hm := max_ge c
      have hmaxle : (a (ρ c ⟨0, hn0⟩) (π (ρ c ⟨0, hn0⟩) c)).val + (n - 1) * kk c ≤
          n ^ 2 - 1 := by
        have e1 : (a (ρ c ⟨n - 1, hnm1⟩) (π (ρ c ⟨n - 1, hnm1⟩) c)).val =
            (a (ρ c ⟨0, hn0⟩) (π (ρ c ⟨0, hn0⟩) c)).val + (n - 1) * kk c := by
          have e1 := hkk c ⟨n - 1, hnm1⟩
          rwa [show ((⟨n - 1, hnm1⟩ : Fin n).val) = n - 1 from rfl] at e1
        have e2 : (a (ρ c ⟨n - 1, hnm1⟩) (π (ρ c ⟨n - 1, hnm1⟩) c)).val < n ^ 2 :=
          (a _ _).isLt
        omega
      have hsq : (n - 1) * (n - 1) = n * n - n - (n - 1) := by
        rw [Nat.mul_sub, Nat.mul_one, Nat.sub_mul, Nat.one_mul]
      have h1 : (n - 1) * (n - 1) ≤ (n - 1) * kk c := by
        have hm' : n * n - n ≤
            (a (ρ c ⟨0, hn0⟩) (π (ρ c ⟨0, hn0⟩) c)).val + (n - 1) * kk c := by
          rw [← pow_two]
          exact hm
        omega
      have hkle1 : n - 1 ≤ kk c := Nat.le_of_mul_le_mul_left h1 (by omega)
      have hsq2 : (n - 1) * (n + 1) = n * n - 1 := by
        rw [Nat.mul_comm, ← Nat.sq_sub_sq, one_pow, pow_two]
      have h2 : (n - 1) * kk c ≤ (n - 1) * (n + 1) := by
        rw [hsq2]
        have hmaxle' : (a (ρ c ⟨0, hn0⟩) (π (ρ c ⟨0, hn0⟩) c)).val + (n - 1) * kk c ≤
            n * n - 1 := by
          rw [← pow_two]
          exact hmaxle
        omega
      have hkle2 : kk c ≤ n + 1 := Nat.le_of_mul_le_mul_left h2 (by omega)
      exact ⟨hkle1, hkle2⟩
    -- The column `c₀` containing the value `1`.
    have hπ0b : Function.Bijective (π ⟨0, hn0⟩) :=
      (Finite.injective_iff_bijective).mp (hπ ⟨0, hn0⟩)
    obtain ⟨c₀, hc₀⟩ := hπ0b.2 ⟨1, h1n⟩
    have one_val : (a ⟨0, hn0⟩ (π ⟨0, hn0⟩ c₀)).val = 1 := by
      rw [hc₀]
      exact trygub_row_zero n q (⟨1, h1n⟩ : Fin n).val
    obtain ⟨m₁, hm₁⟩ := (hρ c₀).2 ⟨0, hn0⟩
    have e1 : (a (ρ c₀ m₁) (π (ρ c₀ m₁) c₀)).val =
        (a (ρ c₀ ⟨0, hn0⟩) (π (ρ c₀ ⟨0, hn0⟩) c₀)).val + m₁.val * kk c₀ := hkk c₀ m₁
    rw [hm₁] at e1
    rw [one_val] at e1
    -- The base value of column `c₀` is not `0`: the value `0` also sits in row `0`.
    have base_ne : (a (ρ c₀ ⟨0, hn0⟩) (π (ρ c₀ ⟨0, hn0⟩) c₀)).val ≠ 0 := by
      intro hzero
      have h2 : trygub n q (ρ c₀ ⟨0, hn0⟩).val (π (ρ c₀ ⟨0, hn0⟩) c₀).val = 0 := hzero
      obtain ⟨hr0, -⟩ := trygub_eq_zero (by omega : 2 ≤ n) h2
      have h3 : ρ c₀ ⟨0, hn0⟩ = ⟨0, hn0⟩ := Fin.ext hr0
      rw [← h3] at one_val
      omega
    have base1 : (a (ρ c₀ ⟨0, hn0⟩) (π (ρ c₀ ⟨0, hn0⟩) c₀)).val = 1 := by omega
    -- The common difference of column `c₀` must be exactly `n`.
    have hkc0 : kk c₀ = n := by
      obtain ⟨h1, h2⟩ := kk_bounds c₀
      have hmax := max_ge c₀
      rw [base1] at hmax
      have hmaxle : 1 + (n - 1) * kk c₀ ≤ n ^ 2 - 1 := by
        have e := hkk c₀ ⟨n - 1, hnm1⟩
        rw [base1, show ((⟨n - 1, hnm1⟩ : Fin n).val) = n - 1 from rfl] at e
        have e2 : (a (ρ c₀ ⟨n - 1, hnm1⟩) (π (ρ c₀ ⟨n - 1, hnm1⟩) c₀)).val < n ^ 2 :=
          (a _ _).isLt
        omega
      have hsq : (n - 1) * (n - 1) = n * n - n - (n - 1) := by
        rw [Nat.mul_sub, Nat.mul_one, Nat.sub_mul, Nat.one_mul]
      have hsq2 : (n - 1) * (n + 1) = n * n - 1 := by
        rw [Nat.mul_comm, ← Nat.sq_sub_sq, one_pow, pow_two]
      have hnn : n * 2 ≤ n * n := Nat.mul_le_mul_left n hn2
      have hmax' : n * n - n ≤ 1 + (n - 1) * kk c₀ := by
        rw [← pow_two]
        exact hmax
      have hmaxle' : 1 + (n - 1) * kk c₀ ≤ n * n - 1 := by
        rw [← pow_two]
        exact hmaxle
      have h3 : kk c₀ = n - 1 ∨ kk c₀ = n ∨ kk c₀ = n + 1 := by omega
      rcases h3 with h | h | h
      · rw [h, hsq] at hmax'
        omega
      · exact h
      · rw [h, hsq2] at hmaxle'
        omega
    -- So column `c₀` is `{1, n+1, 2n+1, …}`, but both `n+1` and `2n+1` lie in row `2`.
    have ev1 := hkk c₀ ⟨1, h1n⟩
    rw [base1, hkc0, show ((⟨1, h1n⟩ : Fin n).val) = 1 from rfl] at ev1
    have loc1 : (ρ c₀ ⟨1, h1n⟩).val = 2 := by
      have h2 : trygub n q (ρ c₀ ⟨1, h1n⟩).val (π (ρ c₀ ⟨1, h1n⟩) c₀).val = n + 1 := by
        have h3 : (a (ρ c₀ ⟨1, h1n⟩) (π (ρ c₀ ⟨1, h1n⟩) c₀)).val = n + 1 := by omega
        exact h3
      exact trygub_eq_add_one hn4 hq2 (ρ c₀ ⟨1, h1n⟩).isLt (π (ρ c₀ ⟨1, h1n⟩) c₀).isLt h2
    have ev2 := hkk c₀ ⟨2, hn⟩
    rw [base1, hkc0, show ((⟨2, hn⟩ : Fin n).val) = 2 from rfl] at ev2
    have loc2 : (ρ c₀ ⟨2, hn⟩).val = 2 := by
      have h2 : trygub n q (ρ c₀ ⟨2, hn⟩).val (π (ρ c₀ ⟨2, hn⟩) c₀).val = 2 * n + 1 := by
        have h3 : (a (ρ c₀ ⟨2, hn⟩) (π (ρ c₀ ⟨2, hn⟩) c₀)).val = 2 * n + 1 := by omega
        exact h3
      exact trygub_eq_two_mul_add_one hn4 hq2 hqdvd (ρ c₀ ⟨2, hn⟩).isLt
        (π (ρ c₀ ⟨2, hn⟩) c₀).isLt h2
    have h12 : (⟨1, h1n⟩ : Fin n) = ⟨2, hn⟩ := by
      apply (hρ c₀).1
      apply Fin.ext
      rw [loc1, loc2]
    have h13 : (1 : ℕ) = 2 := congrArg Fin.val h12
    omega


end Usa2023P5
