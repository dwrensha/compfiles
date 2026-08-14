/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Data.List.TakeWhile
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Tactic.NormNum.Prime
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 2019, Problem 3

Let K be the set of positive integers not containing the decimal digit 7.
Determine all polynomials f(x) with nonnegative coefficients such that
f(x) ∈ K for all x ∈ K.
-/

namespace Usa2019P3

open Polynomial

/-- The set of positive integers whose decimal representation does not
contain the digit 7. -/
def K : Set ℕ := {n | 0 < n ∧ 7 ∉ Nat.digits 10 n}

theorem mem_K {n : ℕ} : n ∈ K ↔ 0 < n ∧ 7 ∉ Nat.digits 10 n := Iff.rfl

/-- The polynomials that map `K` into `K`: the constants with value in `K`,
and the polynomials `10^e * x + k` with `k < 10^e` and `k ∈ K ∪ {0}`. -/
determine solution_set : Set (Polynomial ℕ) :=
  {f | (∃ k : ℕ, k ∈ K ∧ f = C k) ∨
       (∃ e k : ℕ, k < 10 ^ e ∧ (k = 0 ∨ k ∈ K) ∧ f = C (10 ^ e) * X + C k)}

snip begin

/-!
## Proof outline (following Evan Chen's notes)

Call a polynomial *stable* if it maps `K` into `K`.

1. (Reduction to monomials) If `f` is stable then every monomial `aᵢ xⁱ` of
   `f` is stable: plug in `x = 10^E * m` for `E` huge; the decimal digits of
   `f(10^E * m)` are the digits of the blocks `aᵢ mⁱ` padded with zeros.
2. (Linear classification) If `c * x` is stable then `c` is a power of ten.
   Otherwise, writing `c ∈ [d * 10^e, (d+1) * 10^e)`, an explicit multiplier
   `x ∈ K` (depending on the leading digit `d` of `c`) makes `c * x` start
   with the digit `7`.
3. (Higher degrees) If `c * x^d` is stable with `d ≥ 2`, then so is
   `c * (10x + 3)^d`; reducing to monomials shows that
   `c * d * 3^(d-1) * 10 * x` is stable, so `c * d * 3^(d-1) * 10` is a power
   of ten, which forces `3 ∣ 10`, a contradiction.
4. Hence every nonconstant stable polynomial is `10^e * x + k`, and a short
   argument with `x = 7 * 10^s - 1` shows `k < 10^e`.
-/

theorem one_mem_K : (1 : ℕ) ∈ K := by
  refine ⟨by norm_num, ?_⟩
  have h : Nat.digits 10 1 = [1] := Nat.digits_of_lt 10 1 (by norm_num) (by norm_num)
  rw [h]
  simp

/-- The decimal digits of `a` have length at most `k` when `a < 10 ^ k`. -/
theorem digits_len_le_of_lt_pow {a k : ℕ} (h : a < 10 ^ k) :
    (Nat.digits 10 a).length ≤ k :=
  (Nat.digits_length_le_iff (by norm_num : 1 < 10) a).mpr h

/-- Core concatenation lemma: if `a < 10 ^ k` and `0 < m`, then the decimal
digits of `m * 10 ^ k + a` are the digits of `a`, padded with zeros up to
length `k`, followed by the digits of `m`. -/
theorem digits_mul_pow_add {m a k : ℕ} (hm : 0 < m) (ha : a < 10 ^ k) :
    Nat.digits 10 (m * 10 ^ k + a)
      = Nat.digits 10 a ++ List.replicate (k - (Nat.digits 10 a).length) 0
        ++ Nat.digits 10 m := by
  have hlen : (Nat.digits 10 a).length ≤ k := digits_len_le_of_lt_pow ha
  have h1 : m * 10 ^ k + a
      = a + 10 ^ ((Nat.digits 10 a).length + (k - (Nat.digits 10 a).length)) * m := by
    rw [Nat.add_sub_cancel' hlen]
    ring
  rw [h1]
  exact (Nat.digits_append_zeroes_append_digits (by norm_num : 1 < 10) hm).symm

/-- Any natural number in `[7 * 10 ^ E, 8 * 10 ^ E)` contains the digit 7
(in fact, as its leading digit). -/
theorem seven_mem_digits_of_le_lt {y E : ℕ} (h1 : 7 * 10 ^ E ≤ y)
    (h2 : y < 8 * 10 ^ E) : 7 ∈ Nat.digits 10 y := by
  have h3 : y - 7 * 10 ^ E < 10 ^ E := by omega
  have h4 : y = 7 * 10 ^ E + (y - 7 * 10 ^ E) := by omega
  rw [h4, digits_mul_pow_add (by norm_num : (0 : ℕ) < 7) h3]
  have h7 : Nat.digits 10 7 = [7] := Nat.digits_of_lt 10 7 (by norm_num) (by norm_num)
  rw [h7]
  exact List.mem_append_right _ (List.mem_singleton_self 7)

/-- The decimal digits of `10 ^ s - 1` are exactly `s` nines. -/
theorem digits_ten_pow_sub_one (s : ℕ) :
    Nat.digits 10 (10 ^ s - 1) = List.replicate s 9 := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hpos : 0 < 10 ^ s := pow_pos (by norm_num) s
    have h1 : 10 ^ (s + 1) - 1 = 9 * 10 ^ s + (10 ^ s - 1) := by
      have h2 : 10 ^ (s + 1) = 10 ^ s * 10 := pow_succ 10 s
      omega
    have h2 : 10 ^ s - 1 < 10 ^ s := Nat.sub_lt hpos (by norm_num)
    rw [h1, digits_mul_pow_add (by norm_num : (0 : ℕ) < 9) h2, ih, List.length_replicate,
      Nat.sub_self, List.replicate_zero, List.append_nil]
    have h9 : Nat.digits 10 9 = [9] := Nat.digits_of_lt 10 9 (by norm_num) (by norm_num)
    rw [h9]
    simp [List.replicate_add]

/-- The number `7 * 10 ^ s - 1` (i.e. a six followed by `s` nines) lies in `K`. -/
theorem seven_pow_sub_one_mem_K (s : ℕ) : 7 * 10 ^ s - 1 ∈ K := by
  have hpos : 0 < 10 ^ s := pow_pos (by norm_num) s
  constructor
  · omega
  · have h1 : 7 * 10 ^ s - 1 = 6 * 10 ^ s + (10 ^ s - 1) := by omega
    have h2 : 10 ^ s - 1 < 10 ^ s := Nat.sub_lt hpos (by norm_num)
    rw [h1, digits_mul_pow_add (by norm_num : (0 : ℕ) < 6) h2, digits_ten_pow_sub_one,
      List.length_replicate, Nat.sub_self, List.replicate_zero, List.append_nil]
    have h6 : Nat.digits 10 6 = [6] := Nat.digits_of_lt 10 6 (by norm_num) (by norm_num)
    rw [h6]
    simp [List.mem_replicate]

/-- Remove the trailing (i.e. most significant) zeros of a digit list. -/
def dropTrailingZeros (L : List ℕ) : List ℕ := (L.reverse.dropWhile (· = 0)).reverse

theorem ofDigits_eq_zero_of_forall_eq_zero {L : List ℕ} (h : ∀ l ∈ L, l = 0) :
    Nat.ofDigits 10 L = 0 := by
  induction L with
  | nil => rfl
  | cons d L ih =>
    rw [Nat.ofDigits_cons, h d List.mem_cons_self,
      ih (fun l hl => h l (List.mem_cons_of_mem d hl)), mul_zero, add_zero]

theorem ofDigits_dropTrailingZeros (L : List ℕ) :
    Nat.ofDigits 10 (dropTrailingZeros L) = Nat.ofDigits 10 L := by
  have h1 : L = dropTrailingZeros L ++ (L.reverse.takeWhile (· = 0)).reverse := by
    have h2 : dropTrailingZeros L = (L.reverse.dropWhile (· = 0)).reverse := rfl
    rw [h2]
    conv_lhs => rw [← List.reverse_reverse L,
      ← List.takeWhile_append_dropWhile (p := (· = 0)) (l := L.reverse)]
    rw [List.reverse_append]
  conv_rhs => rw [h1]
  rw [Nat.ofDigits_append,
    ofDigits_eq_zero_of_forall_eq_zero
      (L := (L.reverse.takeWhile (· = 0)).reverse) (by
        intro l hl
        rw [List.mem_reverse] at hl
        exact of_decide_eq_true (List.mem_takeWhile_imp (p := fun x ↦ decide (x = 0)) hl)),
    mul_zero, add_zero]

theorem digits_ofDigits_eq_dropTrailingZeros (L : List ℕ) (hL : ∀ l ∈ L, l < 10) :
    Nat.digits 10 (Nat.ofDigits 10 L) = dropTrailingZeros L := by
  induction L using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a ih =>
    by_cases ha : a = 0
    · subst ha
      rw [Nat.ofDigits_append_zero, ih (fun x hx => hL x (List.mem_append_left [0] hx))]
      unfold dropTrailingZeros
      rw [List.reverse_append]
      simp
    · have h1 : dropTrailingZeros (l ++ [a]) = l ++ [a] := by
        unfold dropTrailingZeros
        rw [List.reverse_append]
        simp [List.reverse_cons, ha]
      have h2 : Nat.digits 10 (Nat.ofDigits 10 (l ++ [a])) = l ++ [a] := by
        apply Nat.digits_ofDigits 10 (by norm_num) (l ++ [a])
        · exact hL
        · intro hne
          rw [List.getLast_append_of_right_ne_nil l [a] (by simp)]
          simp only [List.getLast_singleton]
          exact ha
      rw [h1, h2]

theorem mem_dropTrailingZeros_of_mem {x : ℕ} (hx : x ≠ 0) {L : List ℕ} (h : x ∈ L) :
    x ∈ dropTrailingZeros L := by
  unfold dropTrailingZeros
  rw [List.mem_reverse]
  rw [← List.mem_reverse] at h
  have h2 := List.takeWhile_append_dropWhile (p := (· = 0)) (l := L.reverse)
  rw [← h2, List.mem_append] at h
  rcases h with h | h
  · exact absurd (of_decide_eq_true (List.mem_takeWhile_imp (p := fun x ↦ decide (x = 0)) h)) hx
  · exact h

/-- If all entries of `L` are digits and `7` does not occur in the digits of
`Nat.ofDigits 10 L`, then `7` does not occur in `L` either. -/
theorem not_mem_ofDigits_of_not_mem {L : List ℕ} (hL : ∀ l ∈ L, l < 10)
    (h : 7 ∉ Nat.digits 10 (Nat.ofDigits 10 L)) : 7 ∉ L := by
  intro h7
  apply h
  rw [digits_ofDigits_eq_dropTrailingZeros L hL]
  exact mem_dropTrailingZeros_of_mem (by norm_num) h7

/-- The base-10 value of the digit list obtained by concatenating the padded
blocks of `b 0, b 1, …, b (n - 1)` (each block padded to width `E`) equals
`∑ i, b i * 10 ^ (E * i)`. -/
theorem ofDigits_flatMap_digits_pad {E : ℕ} (b : ℕ → ℕ) (hb : ∀ i, b i < 10 ^ E) (n : ℕ) :
    Nat.ofDigits 10 ((List.range n).flatMap fun i =>
        Nat.digits 10 (b i) ++ List.replicate (E - (Nat.digits 10 (b i)).length) 0)
      = ∑ i ∈ Finset.range n, b i * 10 ^ (E * i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hlen : ∀ i, (Nat.digits 10 (b i)).length ≤ E :=
      fun i => (Nat.digits_length_le_iff (by norm_num : 1 < 10) _).mpr (hb i)
    have hpadlen : ∀ i,
        (Nat.digits 10 (b i) ++ List.replicate (E - (Nat.digits 10 (b i)).length) 0).length
          = E := by
      intro i
      rw [List.length_append, List.length_replicate, Nat.add_sub_cancel' (hlen i)]
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, Nat.ofDigits_append, ih,
      List.length_flatMap, Nat.ofDigits_append_replicate_zero, Nat.ofDigits_digits,
      Finset.sum_range_succ]
    have hsum : ((List.range n).map fun i =>
        (Nat.digits 10 (b i) ++ List.replicate (E - (Nat.digits 10 (b i)).length) 0).length).sum
          = n * E := by
      simp [hpadlen, List.map_const', List.sum_replicate]
    rw [hsum, Nat.mul_comm n E, Nat.mul_comm (10 ^ (E * n)) (b n)]

/-- Reduction to monomials: if `f` maps `K` into `K` and its `i`-th
coefficient is nonzero, then `f.coeff i * m ^ i ∈ K` for every `m ∈ K`.
The idea: evaluate at `10 ^ E * m` for a huge `E`; the decimal digits of the
result are the padded blocks of the digits of `f.coeff i * m ^ i`. -/
theorem coeff_stable {f : Polynomial ℕ} (hf : ∀ n ∈ K, f.eval n ∈ K)
    {m : ℕ} (hm : m ∈ K) {i : ℕ} (hi : f.coeff i ≠ 0) : f.coeff i * m ^ i ∈ K := by
  obtain ⟨hmpos, hm7⟩ := hm
  set b : ℕ → ℕ := fun j => f.coeff j * m ^ j with hb
  set S := ∑ j ∈ Finset.range (f.natDegree + 1), b j with hS
  have hbE : ∀ j, b j < 10 ^ (S + 1) := by
    intro j
    by_cases hj : j ≤ f.natDegree
    · have h1 : b j ≤ S :=
        Finset.single_le_sum (fun k _ => Nat.zero_le (b k))
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
      have h2 : S + 1 ≤ 10 ^ (S + 1) := by
        have h3 : S + 1 < 2 ^ (S + 1) := Nat.lt_pow_self (by norm_num : 1 < 2)
        have h4 : 2 ^ (S + 1) ≤ 10 ^ (S + 1) := Nat.pow_le_pow_left (by norm_num) (S + 1)
        omega
      omega
    · push Not at hj
      have h5 : f.coeff j = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hj
      have h6 : b j = 0 := by
        rw [hb]
        simp [h5]
      rw [h6]
      exact pow_pos (by norm_num : (0 : ℕ) < 10) (S + 1)
  have hEm : 10 ^ (S + 1) * m ∈ K := by
    constructor
    · exact Nat.mul_pos (pow_pos (by norm_num) (S + 1)) hmpos
    · rw [Nat.digits_base_pow_mul (by norm_num : 1 < 10) hmpos]
      intro h7
      rw [List.mem_append] at h7
      rcases h7 with h7 | h7
      · rw [List.mem_replicate] at h7
        exact absurd h7.2 (by norm_num)
      · exact hm7 h7
  obtain ⟨_, h7⟩ := hf _ hEm
  have heval : f.eval (10 ^ (S + 1) * m)
      = Nat.ofDigits 10 ((List.range (f.natDegree + 1)).flatMap fun j =>
        Nat.digits 10 (b j) ++ List.replicate (S + 1 - (Nat.digits 10 (b j)).length) 0) := by
    rw [ofDigits_flatMap_digits_pad b hbE, Polynomial.eval_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j _
    show f.coeff j * (10 ^ (S + 1) * m) ^ j = f.coeff j * m ^ j * 10 ^ ((S + 1) * j)
    rw [mul_pow, ← pow_mul]
    ring
  rw [heval] at h7
  have h7L : 7 ∉ (List.range (f.natDegree + 1)).flatMap fun j =>
      Nat.digits 10 (b j) ++ List.replicate (S + 1 - (Nat.digits 10 (b j)).length) 0 := by
    apply not_mem_ofDigits_of_not_mem _ h7
    intro l hl
    rw [List.mem_flatMap] at hl
    obtain ⟨j, _, hl⟩ := hl
    rw [List.mem_append] at hl
    rcases hl with hl | hl
    · exact Nat.digits_lt_base (by norm_num) hl
    · rw [List.mem_replicate] at hl
      rw [hl.2]
      norm_num
  have hi_le : i ≤ f.natDegree := Polynomial.le_natDegree_of_ne_zero hi
  have h7i : 7 ∉ Nat.digits 10 (b i) := by
    intro h
    apply h7L
    rw [List.mem_flatMap]
    exact ⟨i, List.mem_range.mpr (Nat.lt_succ_of_le hi_le), List.mem_append_left _ h⟩
  constructor
  · exact Nat.mul_pos (Nat.pos_of_ne_zero hi) (pow_pos hmpos i)
  · exact h7i

/-- Linear classification: if `x ↦ c * x` maps `K` into `K` and `c ≠ 0`, then
`c` is a power of ten. Otherwise, with `d * 10 ^ e ≤ c < (d + 1) * 10 ^ e` and
`d ∈ {1, …, 9} ∖ {7}`, an explicit multiplier `x ∈ K` (depending on `d`)
makes `c * x` begin with the digit `7`. -/
theorem eq_ten_pow_of_stable {c : ℕ} (hc : c ≠ 0) (hstab : ∀ m ∈ K, c * m ∈ K) :
    ∃ e, c = 10 ^ e := by
  by_contra h
  push Not at h
  have h1K : c ∈ K := by
    have h1 := hstab 1 one_mem_K
    rwa [mul_one] at h1
  obtain ⟨hcpos, hc7⟩ := h1K
  have hlen : 0 < (Nat.digits 10 c).length :=
    List.length_pos_of_ne_nil (Nat.digits_ne_nil_iff_ne_zero.mpr hc)
  set e := (Nat.digits 10 c).length - 1 with he
  have hP0 : 0 < 10 ^ e := pow_pos (by norm_num) e
  have hle : 10 ^ e ≤ c := by
    have h1 : e < (Nat.digits 10 c).length := by rw [he]; omega
    exact (Nat.lt_digits_length_iff (by norm_num : 1 < 10) c).mp h1
  have hge : c < 10 * 10 ^ e := by
    have h1 : (Nat.digits 10 c).length ≤ e + 1 := by rw [he]; omega
    have h2 := (Nat.digits_length_le_iff (by norm_num : 1 < 10) c).mp h1
    rw [pow_succ] at h2
    omega
  set d := c / 10 ^ e with hd
  have hd_pos : 0 < d := Nat.div_pos hle hP0
  have hd_lt : d < 10 := (Nat.div_lt_iff_lt_mul hP0).mpr hge
  have hclow : d * 10 ^ e ≤ c := Nat.div_mul_le_self c (10 ^ e)
  have hchigh : c < (d + 1) * 10 ^ e := by
    have h1 := Nat.div_add_mod c (10 ^ e)
    have h2 := Nat.mod_lt c hP0
    rw [← hd, mul_comm (10 ^ e) d] at h1
    calc c = d * 10 ^ e + c % 10 ^ e := h1.symm
      _ < d * 10 ^ e + 10 ^ e := Nat.add_lt_add_left h2 _
      _ = (d + 1) * 10 ^ e := by ring
  have hd7 : d ≠ 7 := by
    intro h7
    apply hc7
    have h1 : d * 10 ^ e + c % 10 ^ e = c := by
      rw [hd, mul_comm (c / 10 ^ e) (10 ^ e)]
      exact Nat.div_add_mod c (10 ^ e)
    have h2 : Nat.digits 10 (d * 10 ^ e + c % 10 ^ e)
        = Nat.digits 10 (c % 10 ^ e)
          ++ List.replicate (e - (Nat.digits 10 (c % 10 ^ e)).length) 0 ++ Nat.digits 10 d :=
      digits_mul_pow_add hd_pos (Nat.mod_lt c hP0)
    rw [h1] at h2
    rw [h2, h7]
    have h77 : Nat.digits 10 7 = [7] := Nat.digits_of_lt 10 7 (by norm_num) (by norm_num)
    rw [h77]
    exact List.mem_append_right _ (List.mem_singleton_self 7)
  have hE1 : 10 ^ (e + 1) = 10 * 10 ^ e := by rw [pow_add]; ring
  have hE2 : 10 ^ (e + 2) = 100 * 10 ^ e := by rw [pow_add]; ring
  interval_cases d
  · -- leading digit 1; note that `c > 10 ^ e` since `c` is not a power of ten
    rw [one_mul] at hclow
    have hcgt : 10 ^ e < c := lt_of_le_of_ne' hclow (h e)
    by_cases g1 : 10 * c < 11 * 10 ^ e
    · -- the multiplier `x = 7 * 10 ^ (e + 2) - 1 = 699…9`
      have hctop : c < 10 ^ (e + 2) := by
        rw [hE2]
        omega
      have h7c1 : 7 * 10 ^ e ≤ 7 * c - 1 := by omega
      have h7c2 : 7 * c - 1 < 8 * 10 ^ e := by omega
      have h7mem : 7 ∈ Nat.digits 10 (7 * c - 1) := seven_mem_digits_of_le_lt h7c1 h7c2
      have hxK : 7 * 10 ^ (e + 2) - 1 ∈ K := seven_pow_sub_one_mem_K (e + 2)
      have hcx : c * (7 * 10 ^ (e + 2) - 1)
          = (7 * c - 1) * 10 ^ (e + 2) + (10 ^ (e + 2) - c) := by
        have h2 : c ≤ 10 ^ (e + 2) := le_of_lt hctop
        have h3 : (1 : ℕ) ≤ 7 * c := by omega
        rw [Nat.mul_sub, Nat.sub_mul]
        have h4 : c * (7 * 10 ^ (e + 2)) = 7 * c * 10 ^ (e + 2) := by ring
        rw [h4]
        have h5 : 10 ^ (e + 2) ≤ 7 * c * 10 ^ (e + 2) := by
          have h6 : 7 * c = 1 + (7 * c - 1) := by omega
          rw [h6, add_mul, one_mul]
          exact Nat.le_add_right _ _
        omega
      have h7x : 7 ∈ Nat.digits 10 (c * (7 * 10 ^ (e + 2) - 1)) := by
        rw [hcx, digits_mul_pow_add (by omega : 0 < 7 * c - 1)
          (Nat.sub_lt (pow_pos (by norm_num) _) (by omega : 0 < c))]
        exact List.mem_append_right _ h7mem
      exact (hstab _ hxK).2 h7x
    · by_cases g2 : 4 * c < 5 * 10 ^ e
      · have hxK : (64 : ℕ) ∈ K := mem_K.mpr (by decide)
        exact (hstab 64 hxK).2 (seven_mem_digits_of_le_lt (E := e + 1)
          (by rw [hE1]; omega) (by rw [hE1]; omega))
      · by_cases g3 : 5 * c < 7 * 10 ^ e
        · have hxK : (56 : ℕ) ∈ K := mem_K.mpr (by decide)
          exact (hstab 56 hxK).2 (seven_mem_digits_of_le_lt (E := e + 1)
            (by rw [hE1]; omega) (by rw [hE1]; omega))
        · by_cases g4 : 5 * c < 8 * 10 ^ e
          · have hxK : (5 : ℕ) ∈ K := mem_K.mpr (by decide)
            exact (hstab 5 hxK).2 (seven_mem_digits_of_le_lt (E := e) (by omega) (by omega))
          · by_cases g5 : 11 * c < 20 * 10 ^ e
            · have hxK : (44 : ℕ) ∈ K := mem_K.mpr (by decide)
              exact (hstab 44 hxK).2 (seven_mem_digits_of_le_lt (E := e + 1)
                (by rw [hE1]; omega) (by rw [hE1]; omega))
            · have hxK : (39 : ℕ) ∈ K := mem_K.mpr (by decide)
              exact (hstab 39 hxK).2 (seven_mem_digits_of_le_lt (E := e + 1)
                (by rw [hE1]; omega) (by rw [hE1]; omega))
  · -- leading digit 2
    by_cases g1 : 7 * c < 16 * 10 ^ e
    · have hxK : (35 : ℕ) ∈ K := mem_K.mpr (by decide)
      exact (hstab 35 hxK).2 (seven_mem_digits_of_le_lt (E := e + 1)
        (by rw [hE1]; omega) (by rw [hE1]; omega))
    · by_cases g2 : 4 * c < 10 * 10 ^ e
      · have hxK : (31 : ℕ) ∈ K := mem_K.mpr (by decide)
        exact (hstab 31 hxK).2 (seven_mem_digits_of_le_lt (E := e + 1)
          (by rw [hE1]; omega) (by rw [hE1]; omega))
      · by_cases g3 : 13 * c < 35 * 10 ^ e
        · have hxK : (28 : ℕ) ∈ K := mem_K.mpr (by decide)
          exact (hstab 28 hxK).2 (seven_mem_digits_of_le_lt (E := e + 1)
            (by rw [hE1]; omega) (by rw [hE1]; omega))
        · have hxK : (26 : ℕ) ∈ K := mem_K.mpr (by decide)
          exact (hstab 26 hxK).2 (seven_mem_digits_of_le_lt (E := e + 1)
            (by rw [hE1]; omega) (by rw [hE1]; omega))
  · -- leading digit 3
    by_cases g1 : 3 * c < 10 * 10 ^ e
    · have hxK : (24 : ℕ) ∈ K := mem_K.mpr (by decide)
      exact (hstab 24 hxK).2 (seven_mem_digits_of_le_lt (E := e + 1)
        (by rw [hE1]; omega) (by rw [hE1]; omega))
    · by_cases g2 : 11 * c < 40 * 10 ^ e
      · have hxK : (22 : ℕ) ∈ K := mem_K.mpr (by decide)
        exact (hstab 22 hxK).2 (seven_mem_digits_of_le_lt (E := e + 1)
          (by rw [hE1]; omega) (by rw [hE1]; omega))
      · have hxK : (20 : ℕ) ∈ K := mem_K.mpr (by decide)
        exact (hstab 20 hxK).2 (seven_mem_digits_of_le_lt (E := e + 1)
          (by rw [hE1]; omega) (by rw [hE1]; omega))
  · -- leading digit 4
    by_cases g1 : 35 * 10 ^ e ≤ 8 * c
    · have hxK : (16 : ℕ) ∈ K := mem_K.mpr (by decide)
      exact (hstab 16 hxK).2 (seven_mem_digits_of_le_lt (E := e + 1)
        (by rw [hE1]; omega) (by rw [hE1]; omega))
    · have hxK : (18 : ℕ) ∈ K := mem_K.mpr (by decide)
      exact (hstab 18 hxK).2 (seven_mem_digits_of_le_lt (E := e + 1)
        (by rw [hE1]; omega) (by rw [hE1]; omega))
  · -- leading digit 5
    by_cases g1 : 14 * c < 80 * 10 ^ e
    · have hxK : (14 : ℕ) ∈ K := mem_K.mpr (by decide)
      exact (hstab 14 hxK).2 (seven_mem_digits_of_le_lt (E := e + 1)
        (by rw [hE1]; omega) (by rw [hE1]; omega))
    · have hxK : (13 : ℕ) ∈ K := mem_K.mpr (by decide)
      exact (hstab 13 hxK).2 (seven_mem_digits_of_le_lt (E := e + 1)
        (by rw [hE1]; omega) (by rw [hE1]; omega))
  · -- leading digit 6
    by_cases g1 : 3 * c < 20 * 10 ^ e
    · have hxK : (12 : ℕ) ∈ K := mem_K.mpr (by decide)
      exact (hstab 12 hxK).2 (seven_mem_digits_of_le_lt (E := e + 1)
        (by rw [hE1]; omega) (by rw [hE1]; omega))
    · have hxK : (11 : ℕ) ∈ K := mem_K.mpr (by decide)
      exact (hstab 11 hxK).2 (seven_mem_digits_of_le_lt (E := e + 1)
        (by rw [hE1]; omega) (by rw [hE1]; omega))
  · exact absurd rfl hd7
  · -- leading digit 8
    have hxK : (88 : ℕ) ∈ K := mem_K.mpr (by decide)
    exact (hstab 88 hxK).2 (seven_mem_digits_of_le_lt (E := e + 2)
      (by rw [hE2]; omega) (by rw [hE2]; omega))
  · -- leading digit 9
    have hxK : (8 : ℕ) ∈ K := mem_K.mpr (by decide)
    exact (hstab 8 hxK).2 (seven_mem_digits_of_le_lt (E := e + 1)
      (by rw [hE1]; omega) (by rw [hE1]; omega))

/-- The constant coefficient of `(a * x + b) ^ d` is `b ^ d`. -/
theorem coeff_zero_pow_linear (d a b : ℕ) : ((C a * X + C b) ^ d).coeff 0 = b ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ, Polynomial.mul_coeff_zero, ih]
    simp [pow_succ]

/-- The coefficient of `x` in `(a * x + b) ^ d` is `d * a * b ^ (d - 1)`. -/
theorem coeff_one_pow_linear (d a b : ℕ) :
    ((C a * X + C b) ^ d).coeff 1 = d * a * b ^ (d - 1) := by
  induction d with
  | zero => simp [Polynomial.coeff_one]
  | succ d ih =>
    rw [pow_succ, Polynomial.mul_coeff_one, coeff_zero_pow_linear, ih]
    have hp1 : (C a * X + C b).coeff 1 = a := by simp
    have hp0 : (C a * X + C b).coeff 0 = b := by simp
    rw [hp1, hp0]
    have key : d * a * b ^ (d - 1) * b = d * a * b ^ d := by
      cases d with
      | zero => simp
      | succ e =>
        rw [Nat.succ_sub_one, show b ^ (e + 1) = b ^ e * b from pow_succ b e]
        ring
    rw [key, Nat.add_sub_cancel]
    ring

/-- Higher-degree classification: no monomial `c * x ^ d` with `d ≥ 2` maps
`K` into `K`. Otherwise `c * (10x + 3) ^ d` would be stable too, and reducing
to monomials forces `c * d * 3 ^ (d - 1) * 10` to be a power of ten, which is
impossible since it is divisible by `3`. -/
theorem not_stable_of_degree_two_le {c d : ℕ} (hc : c ≠ 0) (hd : 2 ≤ d)
    (hstab : ∀ m ∈ K, c * m ^ d ∈ K) : False := by
  have h10m3 : ∀ m ∈ K, 10 * m + 3 ∈ K := by
    intro m hm
    obtain ⟨hmpos, hm7⟩ := hm
    refine ⟨by omega, ?_⟩
    have h1 := digits_mul_pow_add (m := m) (a := 3) (k := 1) hmpos (by norm_num : 3 < 10 ^ 1)
    rw [pow_one, mul_comm m 10] at h1
    have h3 : Nat.digits 10 3 = [3] := Nat.digits_of_lt 10 3 (by norm_num) (by norm_num)
    rw [h1, h3]
    simp [hm7]
  set g : Polynomial ℕ := (C c * X ^ d).comp (C 10 * X + C 3) with hg
  have hg_stable : ∀ m ∈ K, g.eval m ∈ K := by
    intro m hm
    have h1 : g.eval m = c * (10 * m + 3) ^ d := by
      rw [hg, Polynomial.eval_comp]
      simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow]
    rw [h1]
    exact hstab _ (h10m3 m hm)
  have hcoeff : g.coeff 1 = c * (d * 10 * 3 ^ (d - 1)) := by
    rw [hg, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp,
      Polynomial.coeff_C_mul, coeff_one_pow_linear]
  have hne : g.coeff 1 ≠ 0 := by
    rw [hcoeff]
    exact mul_ne_zero hc (mul_ne_zero (mul_ne_zero (by omega) (by norm_num))
      (pow_ne_zero _ (by norm_num)))
  have hlin : ∀ m ∈ K, c * (d * 10 * 3 ^ (d - 1)) * m ∈ K := by
    intro m hm
    have h2 := coeff_stable hg_stable hm hne
    rwa [hcoeff, pow_one] at h2
  obtain ⟨t, ht⟩ := eq_ten_pow_of_stable
    (mul_ne_zero hc (mul_ne_zero (mul_ne_zero (by omega) (by norm_num)) (pow_ne_zero _ (by norm_num))))
    hlin
  have h3d : 3 ∣ 3 ^ (d - 1) := by
    have h1 : d - 1 = (d - 2) + 1 := by omega
    rw [h1]
    exact dvd_pow_self 3 (by norm_num)
  have h3a : 3 ∣ c * (d * 10 * 3 ^ (d - 1)) := by
    obtain ⟨u, hu⟩ := h3d
    exact ⟨c * d * 10 * u, by rw [hu]; ring⟩
  rw [ht] at h3a
  have h310 : 3 ∣ 10 := Nat.Prime.dvd_of_dvd_pow (by norm_num) h3a
  norm_num at h310

/-- If `x ↦ 10 ^ e * x + k` maps `K` into `K` and `k ≠ 0`, then `k < 10 ^ e`.
Otherwise, writing `k = q * 10 ^ e + r` with `q ≥ 1`, the input
`x = 7 * 10 ^ q - 1 ∈ K` makes `x + q` start with the digit `7`. -/
theorem const_lt_of_linear_stable {e k : ℕ}
    (hstab : ∀ n ∈ K, 10 ^ e * n + k ∈ K) : k < 10 ^ e := by
  by_contra hlt
  push Not at hlt
  have hP0 : 0 < 10 ^ e := pow_pos (by norm_num) e
  obtain ⟨q, r, hq, hr, hkr⟩ : ∃ q r : ℕ, 0 < q ∧ r < 10 ^ e ∧ k = q * 10 ^ e + r :=
    ⟨k / 10 ^ e, k % 10 ^ e, Nat.div_pos hlt hP0, Nat.mod_lt k hP0, by
      rw [mul_comm (k / 10 ^ e) (10 ^ e)]
      exact (Nat.div_add_mod k (10 ^ e)).symm⟩
  have h7 : ∀ n ∈ K, 7 ∉ Nat.digits 10 (n + q) := by
    intro n hn h7mem
    have hnpos : 0 < n := hn.1
    have h1 : 10 ^ e * n + k = (n + q) * 10 ^ e + r := by
      rw [hkr]
      ring
    have h2 := (hstab n hn).2
    rw [h1, digits_mul_pow_add (by omega : 0 < n + q) hr] at h2
    exact h2 (List.mem_append_right _ h7mem)
  have hn : 7 * 10 ^ q - 1 ∈ K := seven_pow_sub_one_mem_K q
  have h3 : 7 ∈ Nat.digits 10 (7 * 10 ^ q - 1 + q) := by
    have h4 : 7 * 10 ^ q - 1 + q = 7 * 10 ^ q + (q - 1) := by
      have h5 : 0 < 10 ^ q := pow_pos (by norm_num) q
      omega
    have h5 : q - 1 < 10 ^ q := by
      have h6 : q < 2 ^ q := Nat.lt_pow_self (by norm_num : 1 < 2)
      have h7' : 2 ^ q ≤ 10 ^ q := Nat.pow_le_pow_left (by norm_num) q
      omega
    rw [h4, digits_mul_pow_add (by norm_num : (0 : ℕ) < 7) h5]
    have h77 : Nat.digits 10 7 = [7] := Nat.digits_of_lt 10 7 (by norm_num) (by norm_num)
    rw [h77]
    exact List.mem_append_right _ (List.mem_singleton_self 7)
  exact h7 _ hn h3

/-- The polynomials `10 ^ e * x + k` with `k < 10 ^ e` and `k ∈ K ∪ {0}` do
map `K` into `K`: the decimal digits of `10 ^ e * n + k` are the digits of
`k` padded to width `e`, followed by the digits of `n`. -/
theorem stable_of_form {e k : ℕ} (hlt : k < 10 ^ e) (hk : k = 0 ∨ k ∈ K) :
    ∀ n ∈ K, (C (10 ^ e) * X + C k).eval n ∈ K := by
  intro n hn
  obtain ⟨hnpos, hn7⟩ := hn
  have heval : (C (10 ^ e) * X + C k).eval n = 10 ^ e * n + k := by
    simp [Polynomial.eval_add, Polynomial.eval_mul]
  rw [heval]
  have hk7 : 7 ∉ Nat.digits 10 k := by
    rcases hk with rfl | hkK
    · simp
    · exact hkK.2
  have h7 : 7 ∉ Nat.digits 10 (10 ^ e * n + k) := by
    rw [mul_comm, digits_mul_pow_add hnpos hlt]
    intro h
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · exact hk7 h
      · rw [List.mem_replicate] at h
        exact absurd h.2 (by norm_num)
    · exact hn7 h
  exact ⟨by
    have hpos : 0 < 10 ^ e * n := Nat.mul_pos (pow_pos (by norm_num) e) hnpos
    omega, h7⟩

snip end

problem usa2019_p3 (f : Polynomial ℕ) :
    (∀ n ∈ K, f.eval n ∈ K) ↔ f ∈ solution_set := by
  show (∀ n ∈ K, f.eval n ∈ K) ↔
    (∃ k : ℕ, k ∈ K ∧ f = C k) ∨
      (∃ e k : ℕ, k < 10 ^ e ∧ (k = 0 ∨ k ∈ K) ∧ f = C (10 ^ e) * X + C k)
  constructor
  · intro hf
    have hfne : f ≠ 0 := by
      rintro rfl
      have h1 := hf 1 one_mem_K
      rw [Polynomial.eval_zero] at h1
      exact absurd h1.1 (by norm_num)
    have hmono : ∀ i, f.coeff i ≠ 0 → ∀ m ∈ K, f.coeff i * m ^ i ∈ K :=
      fun i hi m hm => coeff_stable hf hm hi
    by_cases hdeg : f.natDegree = 0
    · -- constant polynomials: the constant must lie in `K`
      have h1 := hf 1 one_mem_K
      have h2 : f = C (f.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg
      left
      refine ⟨f.coeff 0, ?_, h2⟩
      rw [h2, Polynomial.eval_C] at h1
      exact h1
    · by_cases hdeg2 : f.natDegree = 1
      · -- linear polynomials: `f = C a * X + C b` with `a = 10 ^ e`, `b < 10 ^ e`
        obtain ⟨a, ha, b, hfab⟩ := Polynomial.natDegree_eq_one.mp hdeg2
        have hca : f.coeff 1 = a := by
          rw [← hfab]
          simp
        have hcb : f.coeff 0 = b := by
          rw [← hfab]
          simp
        have ha1 : ∀ m ∈ K, a * m ∈ K := by
          intro m hm
          have h2 := hmono 1 (by rw [hca]; exact ha) m hm
          rwa [hca, pow_one] at h2
        obtain ⟨e, he⟩ := eq_ten_pow_of_stable ha ha1
        right
        by_cases hb0 : b = 0
        · refine ⟨e, 0, pow_pos (by norm_num) e, Or.inl rfl, ?_⟩
          rw [← hfab, he, hb0]
        · have hbK : b ∈ K := by
            have h2 := hmono 0 (by rw [hcb]; exact hb0) 1 one_mem_K
            rwa [hcb, pow_zero, mul_one] at h2
          have hlt : b < 10 ^ e := by
            apply const_lt_of_linear_stable
            intro n hn
            have h2 := hf n hn
            rw [← hfab, he] at h2
            have h3 : (C (10 ^ e) * X + C b).eval n = 10 ^ e * n + b := by
              simp [Polynomial.eval_add, Polynomial.eval_mul]
            rwa [h3] at h2
          exact ⟨e, b, hlt, Or.inr hbK, by rw [← hfab, he]⟩
      · -- degrees `≥ 2` are impossible
        have hdeg3 : 2 ≤ f.natDegree := by omega
        have hlead : f.coeff f.natDegree ≠ 0 := by
          rw [Polynomial.coeff_natDegree]
          exact Polynomial.leadingCoeff_ne_zero.mpr hfne
        exact (not_stable_of_degree_two_le hlead hdeg3 fun m hm => hmono _ hlead m hm).elim
  · rintro (⟨k, hkK, rfl⟩ | ⟨e, k, hlt, hk, rfl⟩)
    · intro n _
      rw [Polynomial.eval_C]
      exact hkK
    · exact stable_of_form hlt hk

end Usa2019P3
