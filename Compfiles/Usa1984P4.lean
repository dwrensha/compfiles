/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 1984, Problem 4

A maths exam has two papers, each with at least one question and 28 questions
in total. Each pupil attempted 7 questions. Each pair of questions was
attempted by just two pupils. Show that one pupil attempted either nil or at
least 4 questions in the first paper.
-/

namespace Usa1984P4

snip begin

/-!
The solution follows the classical double-counting argument (cf. kalva).
We count ordered pairs `(q₁, q₂)` of distinct questions attempted by the same
pupil in two ways.

* Counting over all pupils shows there are `36` pupils.
* Counting over all questions shows each question was attempted by `9` pupils.
* Assuming every pupil attempted 1, 2 or 3 questions of the first paper, and
  counting attempted questions and attempted pairs of questions of the first
  paper, we obtain that the sum over the pupils of `(k - 1)(k - 3)` (where `k`
  is the number of first-paper questions attempted) equals
  `2m² - 29m + 108`, where `m` is the number of questions in the first paper.
  Every summand is nonpositive, but the quadratic is strictly positive for
  every integer `m` (since `8(2m² - 29m + 108) = (4m - 29)² + 23`), a
  contradiction.
-/

/-- Number of ordered pairs `(q₁, q₂)` with `q₂ ∈ s` and `q₁ ≠ q₂`, for a
fixed question `q₁`, expressed as a sum of indicators over all questions. -/
lemma sum_ite_erase (s : Finset (Fin 28)) (q1 : Fin 28) :
    ∑ q2 : Fin 28, (if q1 ∈ s ∧ q2 ∈ s ∧ q1 ≠ q2 then (1 : ℕ) else 0)
      = if q1 ∈ s then s.card - 1 else 0 := by
  by_cases h1 : q1 ∈ s
  · rw [ite_eq_left h1]
    have hset : (Finset.univ.filter fun q2 : Fin 28 ↦ q1 ∈ s ∧ q2 ∈ s ∧ q1 ≠ q2)
        = s.erase q1 := by
      ext q2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      constructor
      · exact fun h ↦ ⟨h.2.2.symm, h.2.1⟩
      · exact fun h ↦ ⟨h1, h.2, h.1.symm⟩
    rw [← Finset.card_filter, hset, Finset.card_erase_of_mem h1]
  · rw [ite_eq_right h1]
    apply Finset.sum_eq_zero
    intro q2 _
    rw [ite_eq_right]
    exact fun h ↦ h1 h.1

/-- The number of ordered pairs of distinct questions in `s`, written as a
double sum of indicators over all questions. -/
lemma card_ordered_pairs (s : Finset (Fin 28)) :
    ∑ q1 : Fin 28, ∑ q2 : Fin 28, (if q1 ∈ s ∧ q2 ∈ s ∧ q1 ≠ q2 then (1 : ℕ) else 0)
      = s.card * (s.card - 1) := by
  rw [Finset.sum_congr rfl (fun q1 _ ↦ sum_ite_erase s q1)]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul]

/-- For fixed questions `q₁ ≠ q₂`, the number of pupils that attempted both
is `2`, expressed as a sum of indicators over all pupils. -/
lemma sum_pupils_pair {Pupil : Type} [Fintype Pupil] (attempt : Pupil → Finset (Fin 28))
    (hpair : ∀ q1 q2 : Fin 28, q1 ≠ q2 →
      (Finset.univ.filter fun p ↦ q1 ∈ attempt p ∧ q2 ∈ attempt p).card = 2)
    (q1 q2 : Fin 28) :
    (∑ p : Pupil, if q1 ∈ attempt p ∧ q2 ∈ attempt p ∧ q1 ≠ q2 then (1 : ℕ) else 0)
      = if q1 ≠ q2 then 2 else 0 := by
  by_cases h : q1 ≠ q2
  · rw [ite_eq_left h]
    have hset : (Finset.univ.filter fun p : Pupil ↦
          q1 ∈ attempt p ∧ q2 ∈ attempt p ∧ q1 ≠ q2)
        = Finset.univ.filter fun p : Pupil ↦ q1 ∈ attempt p ∧ q2 ∈ attempt p := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun hh ↦ ⟨hh.1, hh.2.1⟩
      · exact fun hh ↦ ⟨hh.1, hh.2, h⟩
    rw [← Finset.card_filter, hset, hpair q1 q2 h]
  · rw [ite_eq_right h]
    push Not at h
    subst h
    apply Finset.sum_eq_zero
    intro p _
    rw [ite_eq_right (fun hh ↦ hh.2.2 rfl)]

/-- For a fixed question `q₁`, the number of questions `q₂ ≠ q₁` is `27`,
so summing the constant `2` over them gives `54`. -/
lemma sum_two_distinct (q1 : Fin 28) :
    ∑ q2 : Fin 28, (if q1 ≠ q2 then (2 : ℕ) else 0) = 54 := by
  have hset : (Finset.univ.filter fun q2 : Fin 28 ↦ q1 ≠ q2) = Finset.univ.erase q1 := by
    ext q2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    exact ne_comm
  rw [← Finset.sum_filter, hset, Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ q1), Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]

/-- Double counting ordered pairs of distinct questions attempted by the same
pupil shows there are `36` pupils. -/
lemma card_pupils {Pupil : Type} [Fintype Pupil] (attempt : Pupil → Finset (Fin 28))
    (hattempt : ∀ p, (attempt p).card = 7)
    (hpair : ∀ q1 q2 : Fin 28, q1 ≠ q2 →
      (Finset.univ.filter fun p ↦ q1 ∈ attempt p ∧ q2 ∈ attempt p).card = 2) :
    Fintype.card Pupil = 36 := by
  have step1 : ∑ p : Pupil, ∑ q1 : Fin 28, ∑ q2 : Fin 28,
        (if q1 ∈ attempt p ∧ q2 ∈ attempt p ∧ q1 ≠ q2 then (1 : ℕ) else 0)
      = Fintype.card Pupil * 42 := by
    rw [Finset.sum_congr rfl (fun p _ ↦ card_ordered_pairs (attempt p))]
    have h1 : ∀ p : Pupil, (attempt p).card * ((attempt p).card - 1) = 42 := by
      intro p; rw [hattempt p]
    rw [Finset.sum_congr rfl (fun p _ ↦ h1 p), Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have step2 : ∑ p : Pupil, ∑ q1 : Fin 28, ∑ q2 : Fin 28,
        (if q1 ∈ attempt p ∧ q2 ∈ attempt p ∧ q1 ≠ q2 then (1 : ℕ) else 0)
      = ∑ q1 : Fin 28, ∑ q2 : Fin 28, ∑ p : Pupil,
        (if q1 ∈ attempt p ∧ q2 ∈ attempt p ∧ q1 ≠ q2 then (1 : ℕ) else 0) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun q1 _ ↦ Finset.sum_comm)
  have step3 : ∑ q1 : Fin 28, ∑ q2 : Fin 28, ∑ p : Pupil,
        (if q1 ∈ attempt p ∧ q2 ∈ attempt p ∧ q1 ≠ q2 then (1 : ℕ) else 0)
      = 28 * 27 * 2 := by
    rw [Finset.sum_congr rfl (fun q1 _ ↦ Finset.sum_congr rfl
      (fun q2 _ ↦ sum_pupils_pair attempt hpair q1 q2))]
    rw [Finset.sum_congr rfl (fun q1 _ ↦ sum_two_distinct q1)]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [step2, step3] at step1
  omega

/-- Double counting the pairs `(p, q₂)` with `q` and `q₂` both attempted by
`p` shows every question was attempted by exactly `9` pupils. -/
lemma card_attempters {Pupil : Type} [Fintype Pupil] (attempt : Pupil → Finset (Fin 28))
    (hattempt : ∀ p, (attempt p).card = 7)
    (hpair : ∀ q1 q2 : Fin 28, q1 ≠ q2 →
      (Finset.univ.filter fun p ↦ q1 ∈ attempt p ∧ q2 ∈ attempt p).card = 2)
    (q : Fin 28) :
    (Finset.univ.filter fun p ↦ q ∈ attempt p).card = 9 := by
  have w1 : ∑ p : Pupil, ∑ q2 : Fin 28,
        (if q ∈ attempt p ∧ q2 ∈ attempt p ∧ q ≠ q2 then (1 : ℕ) else 0)
      = (Finset.univ.filter fun p ↦ q ∈ attempt p).card * 6 := by
    rw [Finset.sum_congr rfl (fun p _ ↦ sum_ite_erase (attempt p) q)]
    have h6 : ∀ p : Pupil, (if q ∈ attempt p then (attempt p).card - 1 else (0 : ℕ))
        = if q ∈ attempt p then 6 else 0 := by
      intro p; rw [hattempt p]
    rw [Finset.sum_congr rfl (fun p _ ↦ h6 p), ← Finset.sum_filter, Finset.sum_const,
      smul_eq_mul]
  have w2 : ∑ p : Pupil, ∑ q2 : Fin 28,
        (if q ∈ attempt p ∧ q2 ∈ attempt p ∧ q ≠ q2 then (1 : ℕ) else 0)
      = ∑ q2 : Fin 28, ∑ p : Pupil,
        (if q ∈ attempt p ∧ q2 ∈ attempt p ∧ q ≠ q2 then (1 : ℕ) else 0) :=
    Finset.sum_comm
  have w3 : ∑ q2 : Fin 28, ∑ p : Pupil,
        (if q ∈ attempt p ∧ q2 ∈ attempt p ∧ q ≠ q2 then (1 : ℕ) else 0) = 54 := by
    rw [Finset.sum_congr rfl (fun q2 _ ↦ sum_pupils_pair attempt hpair q q2)]
    exact sum_two_distinct q
  rw [w2, w3] at w1
  omega

snip end

problem usa1984_p4 {Pupil : Type} [Fintype Pupil] (attempt : Pupil → Finset (Fin 28))
    (hattempt : ∀ p, (attempt p).card = 7)
    (hpair : ∀ q1 q2 : Fin 28, q1 ≠ q2 →
      (Finset.univ.filter fun p ↦ q1 ∈ attempt p ∧ q2 ∈ attempt p).card = 2)
    (paper1 : Finset (Fin 28)) (hpaper1 : paper1.Nonempty)
    (_hpaper2 : (Finset.univ \ paper1).Nonempty) :
    ∃ p, (attempt p ∩ paper1).card = 0 ∨ 4 ≤ (attempt p ∩ paper1).card := by
  by_contra hcon
  push Not at hcon
  -- Every pupil attempted between 1 and 3 questions of the first paper.
  have hk1 : ∀ p : Pupil, 1 ≤ (attempt p ∩ paper1).card :=
    fun p ↦ Nat.one_le_iff_ne_zero.mpr (hcon p).1
  have hk3 : ∀ p : Pupil, (attempt p ∩ paper1).card ≤ 3 := by
    intro p
    have h := (hcon p).2
    omega
  have N36 : Fintype.card Pupil = 36 := card_pupils attempt hattempt hpair
  have hm : 1 ≤ paper1.card := Finset.card_pos.mpr hpaper1
  -- Counting attempted first-paper questions in two ways.
  have countA : ∑ p : Pupil, (attempt p ∩ paper1).card = 9 * paper1.card := by
    have step : ∀ p : Pupil, (attempt p ∩ paper1).card
        = ∑ q ∈ paper1, (if q ∈ attempt p then (1 : ℕ) else 0) := by
      intro p
      rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.inter_comm]
    rw [Finset.sum_congr rfl (fun p _ ↦ step p), Finset.sum_comm]
    have h9 : ∀ q : Fin 28, (∑ p : Pupil, if q ∈ attempt p then (1 : ℕ) else 0) = 9 := by
      intro q
      rw [← Finset.card_filter]
      exact card_attempters attempt hattempt hpair q
    rw [Finset.sum_congr rfl (fun q _ ↦ h9 q), Finset.sum_const, smul_eq_mul, mul_comm]
  -- Counting ordered pairs of distinct attempted first-paper questions in two ways.
  have countB : ∑ p : Pupil, (attempt p ∩ paper1).card * ((attempt p ∩ paper1).card - 1)
      = 2 * (paper1.card * (paper1.card - 1)) := by
    have step : ∀ p : Pupil, (attempt p ∩ paper1).card * ((attempt p ∩ paper1).card - 1)
        = ∑ q1 : Fin 28, ∑ q2 : Fin 28,
            (if q1 ∈ attempt p ∩ paper1 ∧ q2 ∈ attempt p ∩ paper1 ∧ q1 ≠ q2
              then (1 : ℕ) else 0) :=
      fun p ↦ (card_ordered_pairs (attempt p ∩ paper1)).symm
    rw [Finset.sum_congr rfl (fun p _ ↦ step p), Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun q1 _ ↦ Finset.sum_comm)]
    have inner : ∀ q1 q2 : Fin 28,
        (∑ p : Pupil, if q1 ∈ attempt p ∩ paper1 ∧ q2 ∈ attempt p ∩ paper1 ∧ q1 ≠ q2
          then (1 : ℕ) else 0)
          = if q1 ∈ paper1 ∧ q2 ∈ paper1 ∧ q1 ≠ q2 then 2 else 0 := by
      intro q1 q2
      by_cases h : q1 ∈ paper1 ∧ q2 ∈ paper1 ∧ q1 ≠ q2
      · rw [ite_eq_left h]
        obtain ⟨h1p, h2p, h12⟩ := h
        have hset : (Finset.univ.filter fun p : Pupil ↦
              q1 ∈ attempt p ∩ paper1 ∧ q2 ∈ attempt p ∩ paper1 ∧ q1 ≠ q2)
            = Finset.univ.filter fun p : Pupil ↦ q1 ∈ attempt p ∧ q2 ∈ attempt p := by
          ext p
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
          constructor
          · exact fun hh ↦ ⟨hh.1.1, hh.2.1.1⟩
          · exact fun hh ↦ ⟨⟨hh.1, h1p⟩, ⟨hh.2, h2p⟩, h12⟩
        rw [← Finset.card_filter, hset, hpair q1 q2 h12]
      · rw [ite_eq_right h]
        apply Finset.sum_eq_zero
        intro p _
        rw [ite_eq_right]
        simp only [Finset.mem_inter]
        exact fun hh ↦ h ⟨hh.1.2, hh.2.1.2, hh.2.2⟩
    rw [Finset.sum_congr rfl (fun q1 _ ↦ Finset.sum_congr rfl (fun q2 _ ↦ inner q1 q2))]
    have h2 : ∀ q1 q2 : Fin 28, (if q1 ∈ paper1 ∧ q2 ∈ paper1 ∧ q1 ≠ q2 then (2 : ℕ) else 0)
        = 2 * (if q1 ∈ paper1 ∧ q2 ∈ paper1 ∧ q1 ≠ q2 then (1 : ℕ) else 0) := by
      intro q1 q2
      split_ifs <;> simp
    rw [Finset.sum_congr rfl (fun q1 _ ↦ Finset.sum_congr rfl (fun q2 _ ↦ h2 q1 q2))]
    simp only [← Finset.mul_sum]
    rw [card_ordered_pairs paper1]
  -- Move the two counts to ℤ, where subtraction behaves well.
  have countA' : ∑ p : Pupil, ((attempt p ∩ paper1).card : ℤ) = 9 * (paper1.card : ℤ) := by
    exact_mod_cast countA
  have countB' : ∑ p : Pupil,
        ((attempt p ∩ paper1).card : ℤ) * (((attempt p ∩ paper1).card : ℤ) - 1)
      = 2 * ((paper1.card : ℤ) * ((paper1.card : ℤ) - 1)) := by
    have e : ∀ p : Pupil,
        (((attempt p ∩ paper1).card * ((attempt p ∩ paper1).card - 1) : ℕ) : ℤ)
        = ((attempt p ∩ paper1).card : ℤ) * (((attempt p ∩ paper1).card : ℤ) - 1) := by
      intro p
      rw [Nat.cast_mul, Nat.cast_sub (hk1 p), Nat.cast_one]
    calc ∑ p : Pupil, ((attempt p ∩ paper1).card : ℤ) * (((attempt p ∩ paper1).card : ℤ) - 1)
        = ∑ p : Pupil,
            (((attempt p ∩ paper1).card * ((attempt p ∩ paper1).card - 1) : ℕ) : ℤ) :=
          Finset.sum_congr rfl (fun p _ ↦ (e p).symm)
      _ = ((∑ p : Pupil, (attempt p ∩ paper1).card * ((attempt p ∩ paper1).card - 1) : ℕ) : ℤ) :=
          (Nat.cast_sum _ _).symm
      _ = ((2 * (paper1.card * (paper1.card - 1)) : ℕ) : ℤ) := by rw [countB]
      _ = 2 * ((paper1.card : ℤ) * ((paper1.card : ℤ) - 1)) := by
          rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hm, Nat.cast_one, Nat.cast_two]
  -- For each pupil, `(k - 1)(k - 3) ≤ 0` since `1 ≤ k ≤ 3`.
  have hper : ∀ p : Pupil,
      (((attempt p ∩ paper1).card : ℤ) - 1) * (((attempt p ∩ paper1).card : ℤ) - 3) ≤ 0 := by
    intro p
    have h1 : (1 : ℤ) ≤ (attempt p ∩ paper1).card := by exact_mod_cast hk1 p
    have h3 : ((attempt p ∩ paper1).card : ℤ) ≤ 3 := by exact_mod_cast hk3 p
    nlinarith
  have hsum : ∑ p : Pupil,
        (((attempt p ∩ paper1).card : ℤ) - 1) * (((attempt p ∩ paper1).card : ℤ) - 3)
      ≤ 0 :=
    Finset.sum_nonpos fun p _ ↦ hper p
  -- But the same sum equals `2m² - 29m + 108`, which is strictly positive.
  have hexp : ∑ p : Pupil,
        (((attempt p ∩ paper1).card : ℤ) - 1) * (((attempt p ∩ paper1).card : ℤ) - 3)
      = 2 * (paper1.card : ℤ) ^ 2 - 29 * paper1.card + 108 := by
    have e : ∀ p : Pupil,
        (((attempt p ∩ paper1).card : ℤ) - 1) * (((attempt p ∩ paper1).card : ℤ) - 3)
        = ((attempt p ∩ paper1).card : ℤ) * (((attempt p ∩ paper1).card : ℤ) - 1)
            - 3 * ((attempt p ∩ paper1).card : ℤ) + 3 := fun p ↦ by ring
    rw [Finset.sum_congr rfl (fun p _ ↦ e p)]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, countA', countB',
      Finset.sum_const, Finset.card_univ, N36, nsmul_eq_mul]
    ring
  have hmz : (1 : ℤ) ≤ (paper1.card : ℤ) := by exact_mod_cast hm
  nlinarith [sq_nonneg (4 * (paper1.card : ℤ) - 29)]

end Usa1984P4
