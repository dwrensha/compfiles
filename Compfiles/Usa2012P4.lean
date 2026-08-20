/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.Data.Int.NatAbs
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.NumberTheory]
  }

/-!
# USA Mathematical Olympiad 2012, Problem 4

Find all functions $f : \mathbb{N} \to \mathbb{N}$ such that $f(n!) = f(n)!$ for all
positive integers $n$ and such that $m - n$ divides $f(m) - f(n)$ for all distinct
positive integers $m, n$.
-/

namespace Usa2012P4

open Nat

/-- The conditions of the problem on a function `f : ℕ → ℕ`. Since the problem
is about functions on the positive integers, we require positivity of `f` on
positive inputs explicitly; the value `f 0` is irrelevant. -/
def IsSolution (f : ℕ → ℕ) : Prop :=
  (∀ n, 0 < n → 0 < f n) ∧
    (∀ n, 0 < n → f (n !) = (f n)!) ∧
      ∀ (m n : ℕ), 0 < m → 0 < n → m ≠ n → (m : ℤ) - n ∣ (f m : ℤ) - f n

snip begin

-- Solution formalized from https://web.evanchen.cc/exams/USAMO-2012-notes.pdf

/-- If a positive integer equals its own factorial, then it is `1` or `2`. -/
lemma eq_one_or_two_of_factorial_eq_self {x : ℕ} (hx : 0 < x) (h : x ! = x) :
    x = 1 ∨ x = 2 := by
  obtain ⟨y, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hx)
  simp only [Nat.succ_eq_add_one] at h ⊢
  rw [Nat.factorial_succ] at h
  have hy : y ! = 1 := by
    have h2 : (y + 1) * y ! = (y + 1) * 1 := by rw [h]; ring
    exact Nat.mul_left_cancel (Nat.succ_pos y) h2
  rw [Nat.factorial_eq_one] at hy
  interval_cases y
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- If `d ≥ 2` divides `(t ! : ℤ) - c` but does not divide `c`, then `t < d`,
because `d ∣ t !` as soon as `t ≥ d`. -/
lemma lt_of_dvd_factorial_sub {d t : ℕ} {c : ℤ} (h : (d : ℤ) ∣ (t ! : ℤ) - c)
    (hd : 2 ≤ d) (hdc : ¬(d : ℤ) ∣ c) : t < d := by
  by_contra htd
  replace htd : d ≤ t := not_lt.mp htd
  have h1 : (d : ℤ) ∣ (t ! : ℤ) :=
    Int.natCast_dvd_natCast.mpr (Nat.dvd_factorial (by lia) htd)
  have h2 : (d : ℤ) ∣ (t ! : ℤ) - ((t ! : ℤ) - c) := dvd_sub h1 h
  have h3 : (t ! : ℤ) - ((t ! : ℤ) - c) = c := by ring
  rw [h3] at h2
  exact hdc h2

/-- Iterated factorials starting at `3`: `iterFac 0 = 3` and
`iterFac (r + 1) = (iterFac r)!`. These are used to produce arbitrarily large
fixed points of `f` (Shankar Padmanabhan's argument). -/
def iterFac : ℕ → ℕ
  | 0 => 3
  | r + 1 => (iterFac r)!

lemma iterFac_ge (r : ℕ) : r + 3 ≤ iterFac r := by
  induction r with
  | zero => exact le_refl _
  | succ r ih =>
    have hlt : iterFac r < (iterFac r)! := Nat.lt_factorial_self (le_trans (by lia) ih)
    show (r + 1) + 3 ≤ (iterFac r)!
    lia

/-- Every iterated factorial of `3` is a fixed point of `f`, once `f 3 = 3`. -/
lemma f_iterFac {f : ℕ → ℕ} (hfact : ∀ n, 0 < n → f (n !) = (f n)!) (hf3 : f 3 = 3)
    (r : ℕ) : f (iterFac r) = iterFac r := by
  induction r with
  | zero => exact hf3
  | succ r ih =>
    have hpos : 0 < iterFac r := by have h := iterFac_ge r; lia
    show f ((iterFac r)!) = (iterFac r)!
    rw [hfact _ hpos, ih]

/-- Case `f 2 = 1`: then `f` is identically `1` on positive integers. -/
lemma eq_one_const_of_f_two_eq_one {f : ℕ → ℕ} (hpos : ∀ n, 0 < n → 0 < f n)
    (hfact : ∀ n, 0 < n → f (n !) = (f n)!)
    (hdiv : ∀ (m n : ℕ), 0 < m → 0 < n → m ≠ n → (m : ℤ) - n ∣ (f m : ℤ) - f n)
    (hf2 : f 2 = 1) (n : ℕ) (hn : 0 < n) : f n = 1 := by
  have key : ∀ m, 3 ≤ m → f m = 1 := by
    intro m hm
    have hne : m ! ≠ 2 := by
      have h6 : 3 ! ≤ m ! := Nat.factorial_le hm
      have h36 : (3 !) = 6 := rfl
      lia
    have h := hdiv (m !) 2 (Nat.factorial_pos m) (by norm_num) hne
    rw [hfact m (by lia), hf2] at h
    have h2m : ((2 : ℕ) : ℤ) ∣ (m ! : ℤ) :=
      Int.natCast_dvd_natCast.mpr (Nat.dvd_factorial (by norm_num) (by lia))
    have h22 : ((2 : ℕ) : ℤ) ∣ ((2 : ℕ) : ℤ) := by decide
    have h2 := dvd_trans (dvd_sub h2m h22) h
    have hlt : f m < 2 := lt_of_dvd_factorial_sub (d := 2) h2 (by norm_num) (by decide)
    have hp := hpos m (by lia)
    lia
  rcases lt_or_ge n 3 with h | h
  · interval_cases n
    · have hf1 : f 1 = (f 1)! := by
        have h1 := hfact 1 (by norm_num)
        rwa [Nat.factorial_one] at h1
      rcases eq_one_or_two_of_factorial_eq_self (hpos 1 (by norm_num)) hf1.symm with h1 | h1
      · exact h1
      · exfalso
        have h3 := hdiv 3 1 (by norm_num) (by norm_num) (by norm_num)
        rw [key 3 (le_refl 3), h1] at h3
        exact absurd h3 (by decide)
    · exact hf2
  · exact key n h

/-- Case `f 1 = f 2 = 2`: then `f` is identically `2` on positive integers. -/
lemma eq_two_const_of_f_one_two_eq_two {f : ℕ → ℕ} (hpos : ∀ n, 0 < n → 0 < f n)
    (hfact : ∀ n, 0 < n → f (n !) = (f n)!)
    (hdiv : ∀ (m n : ℕ), 0 < m → 0 < n → m ≠ n → (m : ℤ) - n ∣ (f m : ℤ) - f n)
    (hf1 : f 1 = 2) (hf2 : f 2 = 2) (n : ℕ) (hn : 0 < n) : f n = 2 := by
  have hf6 : f 6 = (f 3)! := by
    have h := hfact 3 (Nat.zero_lt_succ _)
    rwa [show 3 ! = 6 from rfl] at h
  have hf3 : f 3 = 2 := by
    have h := hdiv 6 1 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _) (by norm_num)
    rw [hf6, hf1] at h
    have hlt : f 3 < 5 := lt_of_dvd_factorial_sub (d := 5) h (by norm_num) (by decide)
    have hp : 0 < f 3 := hpos 3 (Nat.zero_lt_succ _)
    interval_cases f 3
    · exact absurd h (by decide)
    · rfl
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  have hf6' : f 6 = 2 := by rw [hf6, hf3]; exact Nat.factorial_two
  have key : ∀ m, 4 ≤ m → f m = 2 := by
    intro m hm
    have hne : m ! ≠ 6 := by
      have h24 : 4 ! ≤ m ! := Nat.factorial_le hm
      have h424 : (4 !) = 24 := rfl
      lia
    have h := hdiv (m !) 6 (Nat.factorial_pos m) (by norm_num) hne
    rw [hfact m (by lia), hf6'] at h
    have h3m : ((3 : ℕ) : ℤ) ∣ (m ! : ℤ) :=
      Int.natCast_dvd_natCast.mpr (Nat.dvd_factorial (by norm_num) (by lia))
    have h36 : ((3 : ℕ) : ℤ) ∣ ((6 : ℕ) : ℤ) := by decide
    have h3 := dvd_trans (dvd_sub h3m h36) h
    have hlt : f m < 3 := lt_of_dvd_factorial_sub (d := 3) h3 (by norm_num) (by decide)
    have hp : 0 < f m := hpos m (by lia)
    interval_cases f m
    · exact absurd h3 (by decide)
    · rfl
  rcases lt_or_ge n 4 with h | h
  · interval_cases n
    · exact hf1
    · exact hf2
    · exact hf3
  · exact key n h

/-- Case `f 1 = 1` and `f 2 = 2`: then `f` is the identity on positive integers. -/
lemma eq_id_of_f_one_eq_one {f : ℕ → ℕ} (hpos : ∀ n, 0 < n → 0 < f n)
    (hfact : ∀ n, 0 < n → f (n !) = (f n)!)
    (hdiv : ∀ (m n : ℕ), 0 < m → 0 < n → m ≠ n → (m : ℤ) - n ∣ (f m : ℤ) - f n)
    (hf1 : f 1 = 1) (hf2 : f 2 = 2) (n : ℕ) (hn : 0 < n) : f n = n := by
  have hf6 : f 6 = (f 3)! := hfact 3 (Nat.zero_lt_succ _)
  have hf3 : f 3 = 3 := by
    have h1 := hdiv 6 1 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _) (by norm_num)
    rw [hf6, hf1] at h1
    have h2 := hdiv 6 2 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _) (by norm_num)
    rw [hf6, hf2] at h2
    have hlt : f 3 < 5 := lt_of_dvd_factorial_sub (d := 5) h1 (by norm_num) (by decide)
    have hp : 0 < f 3 := hpos 3 (by norm_num)
    interval_cases f 3
    · exact absurd h2 (by decide)
    · exact absurd h1 (by decide)
    · rfl
    · exact absurd h1 (by decide)
  by_contra hne
  have hd : (n : ℤ) - (f n : ℤ) ≠ 0 := by
    rw [Ne, sub_eq_zero, Int.ofNat_inj]
    exact Ne.symm hne
  obtain ⟨r, hr⟩ : ∃ r, n + Int.natAbs ((n : ℤ) - (f n : ℤ)) + 1 ≤ iterFac r :=
    ⟨n + Int.natAbs ((n : ℤ) - (f n : ℤ)), by
      have h := iterFac_ge (n + Int.natAbs ((n : ℤ) - (f n : ℤ)))
      lia⟩
  have hMn : n < iterFac r := by lia
  have hfr : f (iterFac r) = iterFac r := f_iterFac hfact hf3 r
  have h := hdiv (iterFac r) n (by lia) hn (by lia)
  rw [hfr] at h
  have hdvd : ((iterFac r : ℤ) - (n : ℤ)) ∣ ((n : ℤ) - (f n : ℤ)) := by
    have h2 := dvd_sub h (dvd_refl _)
    have heq : ((iterFac r : ℤ) - (f n : ℤ)) - ((iterFac r : ℤ) - (n : ℤ)) =
        (n : ℤ) - (f n : ℤ) := by ring
    rwa [heq] at h2
  have hposd : 0 < Int.natAbs ((n : ℤ) - (f n : ℤ)) :=
    Nat.pos_of_ne_zero (mt Int.natAbs_eq_zero.mp hd)
  have hle : Int.natAbs ((iterFac r : ℤ) - (n : ℤ)) ≤ Int.natAbs ((n : ℤ) - (f n : ℤ)) :=
    Nat.le_of_dvd hposd (Int.natAbs_dvd_natAbs.mpr hdvd)
  rw [Int.natAbs_natCast_sub_natCast_of_ge (le_of_lt hMn)] at hle
  lia

snip end

/-- The answer: the constant functions `1` and `2`, and the identity
(on positive integers). -/
determine solution_set : Set (ℕ → ℕ) :=
  { f | (∀ n, 0 < n → f n = 1) ∨ (∀ n, 0 < n → f n = 2) ∨ (∀ n, 0 < n → f n = n) }

problem usa2012_p4 (f : ℕ → ℕ) :
    f ∈ solution_set ↔ IsSolution f := by
  constructor
  · rintro (h1 | h2 | hid)
    · refine ⟨?_, ?_, ?_⟩
      · intro n hn
        rw [h1 n hn]
        exact zero_lt_one
      · intro n hn
        rw [h1 _ (Nat.factorial_pos n), h1 n hn, Nat.factorial_one]
      · intro m n hm hn _
        rw [h1 m hm, h1 n hn, sub_self]
        exact dvd_zero _
    · refine ⟨?_, ?_, ?_⟩
      · intro n hn
        rw [h2 n hn]
        exact zero_lt_two
      · intro n hn
        rw [h2 _ (Nat.factorial_pos n), h2 n hn, Nat.factorial_two]
      · intro m n hm hn _
        rw [h2 m hm, h2 n hn, sub_self]
        exact dvd_zero _
    · refine ⟨?_, ?_, ?_⟩
      · intro n hn
        rw [hid n hn]
        exact hn
      · intro n hn
        rw [hid _ (Nat.factorial_pos n), hid n hn]
      · intro m n hm hn _
        rw [hid m hm, hid n hn]
  · rintro ⟨hpos, hfact, hdiv⟩
    have hf1 : f 1 = (f 1)! := by
      have h := hfact 1 (by norm_num)
      rwa [Nat.factorial_one] at h
    have hf2 : f 2 = (f 2)! := by
      have h := hfact 2 (by norm_num)
      rwa [Nat.factorial_two] at h
    have h1cases := eq_one_or_two_of_factorial_eq_self (hpos 1 (by norm_num)) hf1.symm
    have h2cases := eq_one_or_two_of_factorial_eq_self (hpos 2 (by norm_num)) hf2.symm
    rcases h1cases with hf1' | hf1' <;> rcases h2cases with hf2' | hf2'
    · exact Or.inl (eq_one_const_of_f_two_eq_one hpos hfact hdiv hf2')
    · exact Or.inr (Or.inr (eq_id_of_f_one_eq_one hpos hfact hdiv hf1' hf2'))
    · exact Or.inl (eq_one_const_of_f_two_eq_one hpos hfact hdiv hf2')
    · exact Or.inr (Or.inl (eq_two_const_of_f_one_two_eq_two hpos hfact hdiv hf1' hf2'))

end Usa2012P4
