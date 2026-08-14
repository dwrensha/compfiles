/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Tactic.IntervalCases
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2012, Problem 1

Find all integers n ≥ 3 such that among any n positive real numbers
a₁, a₂, ..., aₙ with

  max(a₁, a₂, ..., aₙ) ≤ n · min(a₁, a₂, ..., aₙ),

there exist three that are the side lengths of an acute triangle.
-/

namespace Usa2012P1

/-- Three real numbers are the side lengths of an acute triangle iff the strict
triangle inequalities hold and the sum of the squares of any two of them is strictly
greater than the square of the third one. -/
def IsAcuteTriple (x y z : ℝ) : Prop :=
  x + y > z ∧ y + z > x ∧ z + x > y ∧
  x ^ 2 + y ^ 2 > z ^ 2 ∧ y ^ 2 + z ^ 2 > x ^ 2 ∧ z ^ 2 + x ^ 2 > y ^ 2

/-- The property of `n` that the problem asks to characterize: among any `n` positive
real numbers whose maximum is at most `n` times their minimum (here expressed as
`a i ≤ n * a j` for all indices `i j`), some three are the side lengths of an acute
triangle. -/
def IsGood (n : ℕ) : Prop :=
  ∀ a : Fin n → ℝ,
    (∀ i, 0 < a i) →
    (∀ i j, a i ≤ (n : ℝ) * a j) →
    ∃ i j k, i ≠ j ∧ j ≠ k ∧ k ≠ i ∧ IsAcuteTriple (a i) (a j) (a k)

determine solution_set : Set ℕ := {n | 13 ≤ n}

snip begin

/-- For a sorted triple `x ≤ y ≤ z` of positive reals, failing to be the side lengths
of an acute triangle implies `z ^ 2 ≥ x ^ 2 + y ^ 2`. -/
lemma sq_add_sq_le_of_not_isAcuteTriple {x y z : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hxy : x ≤ y) (hyz : y ≤ z)
    (h : ¬ IsAcuteTriple x y z) : x ^ 2 + y ^ 2 ≤ z ^ 2 := by
  by_contra hlt
  rw [not_le] at hlt
  apply h
  have hxz : x ≤ z := hxy.trans hyz
  refine ⟨?_, by linarith, by linarith, hlt, ?_, ?_⟩
  · -- `x + y > z` follows from `(x + y) ^ 2 > z ^ 2`.
    have h2 : z ^ 2 < (x + y) ^ 2 := by nlinarith [hlt, mul_pos hx hy]
    exact lt_of_pow_lt_pow_left₀ 2 (le_of_lt (add_pos hx hy)) h2
  · have h3 : x ^ 2 ≤ z ^ 2 := pow_le_pow_left₀ (le_of_lt hx) hxz 2
    have h4 : 0 < y ^ 2 := pow_pos hy 2
    linarith
  · have h5 : y ^ 2 ≤ z ^ 2 := pow_le_pow_left₀ (le_of_lt hy) hyz 2
    have h6 : 0 < x ^ 2 := pow_pos hx 2
    linarith

/-- The Fibonacci numbers outgrow the squares from index 13 on. -/
lemma sq_lt_fib {m : ℕ} (hm : 13 ≤ m) : m ^ 2 < Nat.fib m := by
  suffices h : m ^ 2 < Nat.fib m ∧ (m + 1) ^ 2 < Nat.fib (m + 1) from h.1
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ m _hm ih =>
    refine ⟨ih.2, ?_⟩
    have hm2 : 2 * m + 3 ≤ m ^ 2 := by nlinarith [mul_le_mul_right _hm m]
    have hf : Nat.fib (m + 1 + 1) = Nat.fib m + Nat.fib (m + 1) := Nat.fib_add_two
    rw [hf]
    nlinarith [ih.1, ih.2, hm2]

/-- If a monotone tuple of positive reals contains no three terms that are the side
lengths of an acute triangle, then its squares grow at least as fast as the Fibonacci
numbers: `b i ^ 2 ≥ F_{i+1} * b 0 ^ 2`. -/
lemma fib_mul_sq_le {n : ℕ} {b : Fin n → ℝ} (hn : 0 < n)
    (hb_pos : ∀ i, 0 < b i) (hb_mono : Monotone b)
    (hsq : ∀ i j k : Fin n, i < j → j < k → b i ^ 2 + b j ^ 2 ≤ b k ^ 2) :
    ∀ i : ℕ, ∀ h : i < n, (Nat.fib (i + 1) : ℝ) * b ⟨0, hn⟩ ^ 2 ≤ b ⟨i, h⟩ ^ 2 := by
  intro i
  induction i using Nat.twoStepInduction with
  | zero =>
    intro h
    simp only [zero_add, Nat.fib_one, Nat.cast_one, one_mul]
    exact le_refl _
  | one =>
    intro h
    show (Nat.fib 2 : ℝ) * b ⟨0, hn⟩ ^ 2 ≤ b ⟨1, h⟩ ^ 2
    rw [Nat.fib_two, Nat.cast_one, one_mul]
    exact pow_le_pow_left₀ (le_of_lt (hb_pos ⟨0, hn⟩)) (hb_mono (by show (0 : ℕ) ≤ 1; lia)) 2
  | more i ih0 ih1 =>
    intro h
    have hi : i < n := by lia
    have hi1 : i + 1 < n := by lia
    have hf : (Nat.fib (i + 2 + 1) : ℝ) = (Nat.fib (i + 1) : ℝ) + (Nat.fib (i + 2) : ℝ) := by
      norm_cast
      exact Nat.fib_add_two
    have hs : b ⟨i, hi⟩ ^ 2 + b ⟨i + 1, hi1⟩ ^ 2 ≤ b ⟨i + 2, h⟩ ^ 2 :=
      hsq ⟨i, hi⟩ ⟨i + 1, hi1⟩ ⟨i + 2, h⟩ (by show i < i + 1; lia) (by show i + 1 < i + 2; lia)
    have e0 : (Nat.fib (i + 1) : ℝ) * b ⟨0, hn⟩ ^ 2 ≤ b ⟨i, hi⟩ ^ 2 := ih0 hi
    have e1 : (Nat.fib (i + 2) : ℝ) * b ⟨0, hn⟩ ^ 2 ≤ b ⟨i + 1, hi1⟩ ^ 2 := ih1 hi1
    rw [hf, add_mul]
    linarith

/-- Every `n ≥ 13` has the required property. -/
lemma isGood_of_thirteen_le {n : ℕ} (hn : 13 ≤ n) : IsGood n := by
  intro a hpos hmax
  by_contra h
  push Not at h
  -- Sort the numbers; both the hypothesis and the conclusion are permutation-invariant.
  let σ := Tuple.sort a
  let b := a ∘ σ
  have hb_mono : Monotone b := Tuple.monotone_sort a
  have hb_pos : ∀ i, 0 < b i := fun i ↦ hpos (σ i)
  have hσ_inj : Function.Injective σ := Equiv.injective σ
  -- No three consecutive terms of the sorted tuple form an acute triangle.
  have hsq : ∀ i j k : Fin n, i < j → j < k → b i ^ 2 + b j ^ 2 ≤ b k ^ 2 := by
    intro i j k hij hjk
    apply sq_add_sq_le_of_not_isAcuteTriple (hb_pos i) (hb_pos j) (hb_pos k)
      (hb_mono hij.le) (hb_mono hjk.le)
    exact h (σ i) (σ j) (σ k) (hσ_inj.ne (ne_of_lt hij)) (hσ_inj.ne (ne_of_lt hjk))
      (hσ_inj.ne (ne_of_lt (hij.trans hjk)).symm)
  have hn0' : 0 < n := by lia
  have hnl' : n - 1 < n := by lia
  have key := fib_mul_sq_le hn0' hb_pos hb_mono hsq
  have hlast : (Nat.fib (n - 1 + 1) : ℝ) * b ⟨0, hn0'⟩ ^ 2 ≤ b ⟨n - 1, hnl'⟩ ^ 2 :=
    key (n - 1) hnl'
  rw [Nat.sub_add_cancel (by lia : 1 ≤ n)] at hlast
  -- The `max ≤ n * min` condition, applied to the last and first sorted terms.
  have hmax' : b ⟨n - 1, hnl'⟩ ≤ (n : ℝ) * b ⟨0, hn0'⟩ := hmax _ _
  have h1 : b ⟨n - 1, hnl'⟩ ^ 2 ≤ ((n : ℝ) * b ⟨0, hn0'⟩) ^ 2 :=
    pow_le_pow_left₀ (le_of_lt (hb_pos ⟨n - 1, hnl'⟩)) hmax' 2
  rw [mul_pow] at h1
  -- Hence `b 0 ^ 2 * F_n ≤ b 0 ^ 2 * n ^ 2`, and cancelling gives `F_n ≤ n ^ 2`.
  have h2 : b ⟨0, hn0'⟩ ^ 2 * (Nat.fib n : ℝ) ≤ b ⟨0, hn0'⟩ ^ 2 * (n : ℝ) ^ 2 := by
    linarith
  have h3 : (Nat.fib n : ℝ) ≤ (n : ℝ) ^ 2 :=
    (mul_le_mul_iff_right₀ (pow_pos (hb_pos ⟨0, hn0'⟩) 2)).mp h2
  -- But `F_n > n ^ 2` for `n ≥ 13`, a contradiction.
  have h4 : (n : ℝ) ^ 2 < (Nat.fib n : ℝ) := by exact_mod_cast sq_lt_fib hn
  linarith

/-- The counterexample for `n ≤ 12`: the numbers `√F₁, √F₂, ...` where `F` is the
Fibonacci sequence. -/
noncomputable def counterexSeq (n : ℕ) : Fin n → ℝ := fun i ↦ √(Nat.fib (i.val + 1) : ℝ)

/-- No `n` with `3 ≤ n ≤ 12` has the required property. -/
lemma not_isGood_of_le_twelve {n : ℕ} (h3 : 3 ≤ n) (h12 : n ≤ 12) : ¬ IsGood n := by
  have hfib12 : Nat.fib n ≤ n ^ 2 := by
    interval_cases n <;> decide
  intro hg
  have hn0' : 0 < n := by lia
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0'
  have hnl' : n - 1 < n := by lia
  -- The terms are positive and monotone in the index.
  have ha_pos : ∀ i, 0 < counterexSeq n i := by
    intro i
    show 0 < √(Nat.fib (i.val + 1) : ℝ)
    exact Real.sqrt_pos.mpr (by exact_mod_cast Nat.fib_pos.mpr (Nat.succ_pos i.val))
  have ha_mono : ∀ i j : Fin n, i.val ≤ j.val → counterexSeq n i ≤ counterexSeq n j := by
    intro i j hij
    apply Real.sqrt_le_sqrt
    have h1 : Nat.fib (i.val + 1) ≤ Nat.fib (j.val + 1) := Nat.fib_mono (by lia)
    exact_mod_cast h1
  -- The first term is `1` and the last one is at most `n`, since `F_n ≤ n ^ 2`.
  have h0 : counterexSeq n ⟨0, hn0'⟩ = 1 := by
    show √(Nat.fib (0 + 1) : ℝ) = 1
    simp [Nat.fib_one]
  have hlast : counterexSeq n ⟨n - 1, hnl'⟩ ≤ (n : ℝ) := by
    show √(Nat.fib (n - 1 + 1) : ℝ) ≤ (n : ℝ)
    rw [Nat.sub_add_cancel (by lia : 1 ≤ n)]
    calc √(Nat.fib n : ℝ) ≤ √((n : ℝ) ^ 2) := by
          apply Real.sqrt_le_sqrt
          exact_mod_cast hfib12
      _ = (n : ℝ) := Real.sqrt_sq (le_of_lt hn0)
  -- Hence the sequence satisfies the `max ≤ n * min` condition.
  have ha_max : ∀ i j : Fin n, counterexSeq n i ≤ (n : ℝ) * counterexSeq n j := by
    intro i j
    calc counterexSeq n i ≤ counterexSeq n ⟨n - 1, hnl'⟩ :=
          ha_mono i _ (by show i.val ≤ n - 1; have := i.isLt; lia)
      _ ≤ (n : ℝ) := hlast
      _ = (n : ℝ) * 1 := by rw [mul_one]
      _ = (n : ℝ) * counterexSeq n ⟨0, hn0'⟩ := by rw [h0]
      _ ≤ (n : ℝ) * counterexSeq n j :=
          mul_le_mul_of_nonneg_left (ha_mono _ _ (by show (0 : ℕ) ≤ j.val; lia)) (le_of_lt hn0)
  -- But no three terms form an acute triangle: for `p < q < r` we have
  -- `a p ^ 2 + a q ^ 2 = F_{p+1} + F_{q+1} ≤ F_q + F_{q+1} = F_{q+2} ≤ F_{r+1} = a r ^ 2`.
  have key : ∀ p q r : Fin n, p < q → q < r →
      counterexSeq n p ^ 2 + counterexSeq n q ^ 2 ≤ counterexSeq n r ^ 2 := by
    intro p q r hpq hqr
    have hf : Nat.fib (p.val + 1) + Nat.fib (q.val + 1) ≤ Nat.fib (r.val + 1) := by
      have h1 : Nat.fib (p.val + 1) ≤ Nat.fib q.val := Nat.fib_mono (by lia)
      have h2 : Nat.fib (q.val + 2) ≤ Nat.fib (r.val + 1) := Nat.fib_mono (by lia)
      have h3 : Nat.fib (q.val + 2) = Nat.fib q.val + Nat.fib (q.val + 1) := Nat.fib_add_two
      lia
    have e1 : counterexSeq n p ^ 2 = (Nat.fib (p.val + 1) : ℝ) :=
      Real.sq_sqrt (by positivity)
    have e2 : counterexSeq n q ^ 2 = (Nat.fib (q.val + 1) : ℝ) :=
      Real.sq_sqrt (by positivity)
    have e3 : counterexSeq n r ^ 2 = (Nat.fib (r.val + 1) : ℝ) :=
      Real.sq_sqrt (by positivity)
    rw [e1, e2, e3]
    exact_mod_cast hf
  -- Therefore one of the three square conditions must fail for any distinct `i j k`.
  obtain ⟨i, j, k, hij, hjk, hki, hacute⟩ := hg (counterexSeq n) ha_pos ha_max
  rcases hacute with ⟨-, -, -, h1, h2, h3⟩
  have hfail : (counterexSeq n i ^ 2 + counterexSeq n j ^ 2 ≤ counterexSeq n k ^ 2) ∨
      (counterexSeq n j ^ 2 + counterexSeq n k ^ 2 ≤ counterexSeq n i ^ 2) ∨
      (counterexSeq n k ^ 2 + counterexSeq n i ^ 2 ≤ counterexSeq n j ^ 2) := by
    rcases lt_trichotomy i j with c | c | c
    · rcases lt_trichotomy j k with d | d | d
      · exact Or.inl (key i j k c d)
      · exact absurd d hjk
      · rcases lt_trichotomy i k with e | e | e
        · exact Or.inr (Or.inr (by linarith [key i k j e d]))
        · exact absurd e hki.symm
        · exact Or.inr (Or.inr (key k i j e c))
    · exact absurd c hij
    · rcases lt_trichotomy j k with d | d | d
      · rcases lt_trichotomy i k with e | e | e
        · exact Or.inl (by linarith [key j i k c e])
        · exact absurd e hki.symm
        · exact Or.inr (Or.inl (key j k i d e))
      · exact absurd d hjk
      · exact Or.inr (Or.inl (by linarith [key k j i d c]))
  rcases hfail with d | d | d <;> linarith

snip end

problem usa2012_p1 (n : ℕ) : 3 ≤ n ∧ IsGood n ↔ n ∈ solution_set := by
  constructor
  · rintro ⟨h3, hg⟩
    by_contra h
    have h13 : ¬ 13 ≤ n := h
    have h12 : n ≤ 12 := by lia
    exact not_isGood_of_le_twelve h3 h12 hg
  · intro h
    have h13 : 13 ≤ n := h
    exact ⟨by lia, isGood_of_thirteen_le h13⟩

end Usa2012P1
