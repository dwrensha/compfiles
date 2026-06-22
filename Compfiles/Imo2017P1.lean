/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roozbeh Yousefzadeh, David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file {
  tags := [.NumberTheory]
  solutionImportedFrom :=
    "https://github.com/roozbeh-yz/IMO-Steps/tree/main/Lean_v20/imo_proofs/imo_2017_p1.lean",
}

/-!
# International Mathematical Olympiad 2017, Problem 1

For any integer a₀ > 1, define the sequence

  aₙ₊₁ =   √aₙ, if aₙ is a perfect square
        or aₙ + 3 otherwise.

Find all values of a₀ for which there exists A such that aₙ = A for
infinitely many values of n.
-/

namespace Imo2017P1


determine solution_set : Set ℕ := {x | 0 < x ∧ 3 ∣ x}


snip begin

/-- The recurrence rule defining the sequence. -/
abbrev Rule (a : ℕ → ℕ → ℕ) : Prop :=
  ∀ x i, 1 < x → if IsSquare (a x i)
                 then a x (i + 1) = Nat.sqrt (a x i)
                 else a x (i + 1) = a x i + 3

variable {a : ℕ → ℕ → ℕ} {x : ℕ}

lemma step_sq (ha₁ : Rule a) (hx : 1 < x) {i : ℕ} (h : IsSquare (a x i)) :
    a x (i + 1) = (a x i).sqrt := by
  have := ha₁ x i hx
  rwa [if_pos h] at this

lemma step_nonsq (ha₁ : Rule a) (hx : 1 < x) {i : ℕ} (h : ¬IsSquare (a x i)) :
    a x (i + 1) = a x i + 3 := by
  have := ha₁ x i hx
  rwa [if_neg h] at this

lemma not_isSquare_of_mod_three {y : ℕ} (hy : y % 3 = 2) : ¬IsSquare y := by
  rintro ⟨r, rfl⟩
  rw [Nat.mul_mod] at hy
  obtain h | h | h : r % 3 = 0 ∨ r % 3 = 1 ∨ r % 3 = 2 := by lia
  all_goals rw [h] at hy; norm_num at hy

/-- Every term of the sequence is greater than 1. -/
lemma one_lt (ha₀ : ∀ x, a x 0 = x) (ha₁ : Rule a) (hx : 1 < x) :
    ∀ i, 1 < a x i := by
  intro i
  induction i with
  | zero => rw [ha₀]; exact hx
  | succ i ih =>
    by_cases h : IsSquare (a x i)
    · rw [step_sq ha₁ hx h]
      obtain ⟨r, hr⟩ := h
      have h1 : 1 < r * r := hr ▸ ih
      have h2 : 2 ≤ r := by nlinarith
      have h3 : 2 ≤ (a x i).sqrt := Nat.le_sqrt.mpr (by rw [hr]; nlinarith)
      lia
    · rw [step_nonsq ha₁ hx h]
      lia

/-- Divisibility by 3 is invariant along the sequence. -/
lemma three_dvd_iff (ha₀ : ∀ x, a x 0 = x) (ha₁ : Rule a) (hx : 1 < x) :
    ∀ i, (3 ∣ a x i ↔ 3 ∣ x) := by
  intro i
  induction i with
  | zero => rw [ha₀]
  | succ i ih =>
    by_cases h : IsSquare (a x i)
    · rw [step_sq ha₁ hx h, ← ih]
      obtain ⟨r, hr⟩ := h
      rw [hr, Nat.sqrt_eq, Nat.prime_three.dvd_mul]
      tauto
    · rw [step_nonsq ha₁ hx h, ← ih]
      lia

/-- Once the sequence is 2 mod 3, it never again hits a perfect square, so
it just increases by 3 forever. -/
lemma run_linear (ha₁ : Rule a) (hx : 1 < x) {i : ℕ} (hi : a x i % 3 = 2) :
    ∀ j, a x (i + j) = a x i + 3 * j := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have h2 : ¬IsSquare (a x (i + j)) := by
      apply not_isSquare_of_mod_three
      rw [ih]
      lia
    rw [show i + (j + 1) = (i + j) + 1 by ring, step_nonsq ha₁ hx h2, ih]
    ring

/-- If the sequence is ever 2 mod 3, then it takes each value only
finitely often. -/
lemma finite_visits (ha₁ : Rule a) (hx : 1 < x) {i : ℕ} (hi : a x i % 3 = 2)
    (A : ℕ) : {n | a x n = A}.Finite := by
  apply Set.Finite.subset (Set.finite_Icc 0 (i + A))
  intro n hn
  simp only [Set.mem_setOf_eq] at hn
  obtain h | h : n ≤ i ∨ i < n := by lia
  · exact Set.mem_Icc.mpr ⟨Nat.zero_le n, by lia⟩
  · have h1 := run_linear ha₁ hx hi (n - i)
    rw [show i + (n - i) = n by lia] at h1
    exact Set.mem_Icc.mpr ⟨Nat.zero_le n, by lia⟩

/-- From a value c that is not 2 mod 3, the sequence climbs to the *least*
perfect square in the progression c, c+3, c+6, ..., and the next step takes
it down to a value at most √c + 3.  (By minimality, no intermediate value of
the climb is a square; and the progression does contain a square r² with
√c < r ≤ √c + 3, where r is chosen with r² ≡ c (mod 3).) -/
lemma climb (ha₁ : Rule a) (hx : 1 < x) {i c : ℕ} (hi : a x i = c)
    (hc : c % 3 ≠ 2) : ∃ j, a x j ≤ c.sqrt + 3 := by
  classical
  obtain ⟨r, hr1, hr2, hr3⟩ : ∃ r, c.sqrt < r ∧ r ≤ c.sqrt + 3 ∧
      r * r % 3 = c % 3 := by
    obtain hs | hs | hs : c.sqrt % 3 = 0 ∨ c.sqrt % 3 = 1 ∨ c.sqrt % 3 = 2 := by
      lia
    all_goals obtain h | h : c % 3 = 0 ∨ c % 3 = 1 := by lia
    · exact ⟨c.sqrt + 3, by lia, by lia,
        by rw [Nat.mul_mod, show (c.sqrt + 3) % 3 = 0 by lia, h]⟩
    · exact ⟨c.sqrt + 1, by lia, by lia,
        by rw [Nat.mul_mod, show (c.sqrt + 1) % 3 = 1 by lia, h]⟩
    · exact ⟨c.sqrt + 2, by lia, by lia,
        by rw [Nat.mul_mod, show (c.sqrt + 2) % 3 = 0 by lia, h]⟩
    · exact ⟨c.sqrt + 1, by lia, by lia,
        by rw [Nat.mul_mod, show (c.sqrt + 1) % 3 = 2 by lia, h]⟩
    · exact ⟨c.sqrt + 1, by lia, by lia,
        by rw [Nat.mul_mod, show (c.sqrt + 1) % 3 = 0 by lia, h]⟩
    · exact ⟨c.sqrt + 2, by lia, by lia,
        by rw [Nat.mul_mod, show (c.sqrt + 2) % 3 = 1 by lia, h]⟩
  have hcr : c ≤ r * r := by
    have h1 : c < (c.sqrt + 1) * (c.sqrt + 1) := Nat.lt_succ_sqrt c
    have h2 : (c.sqrt + 1) * (c.sqrt + 1) ≤ r * r :=
      Nat.mul_le_mul (by lia) (by lia)
    lia
  have he : c + 3 * ((r * r - c) / 3) = r * r := by lia
  have hex : ∃ t, IsSquare (c + 3 * t) := ⟨(r * r - c) / 3, r, he⟩
  set t₀ := Nat.find hex with ht₀
  -- the sequence adds 3 at every step until it reaches c + 3 * t₀
  have hrun : ∀ s, s ≤ t₀ → a x (i + s) = c + 3 * s := by
    intro s
    induction s with
    | zero => intro _; simpa using hi
    | succ s ih =>
      intro hs
      have h1 : a x (i + s) = c + 3 * s := ih (by lia)
      have h2 : ¬IsSquare (a x (i + s)) := by
        rw [h1]
        exact Nat.find_min hex (by lia)
      rw [show i + (s + 1) = (i + s) + 1 by ring, step_nonsq ha₁ hx h2, h1]
      ring
  have ht₀r : c + 3 * t₀ ≤ r * r := by
    have h1 : t₀ ≤ (r * r - c) / 3 := Nat.find_min' hex ⟨r, he⟩
    lia
  obtain ⟨s, hs⟩ := Nat.find_spec hex
  have hsq : a x (i + t₀) = s * s := by rw [hrun t₀ le_rfl, ← hs]
  refine ⟨i + t₀ + 1, ?_⟩
  rw [step_sq ha₁ hx ⟨s, hsq⟩, hsq, Nat.sqrt_eq]
  -- s ≤ r ≤ √c + 3
  have h1 : s ≤ r := by
    have h2 : s * s ≤ r * r := by lia
    calc s = (s * s).sqrt := (Nat.sqrt_eq s).symm
    _ ≤ (r * r).sqrt := Nat.sqrt_le_sqrt h2
    _ = r := Nat.sqrt_eq r
  lia

/-- If the sequence never hits the class 2 mod 3, then its minimum value
is 3 (so that 3 divides every term, and in particular x). -/
lemma orbit_min_three (ha₀ : ∀ x, a x 0 = x) (ha₁ : Rule a) (hx : 1 < x)
    (hno2 : ∀ i, a x i % 3 ≠ 2) : 3 ∣ x ∧ ∃ i, a x i = 3 := by
  obtain ⟨c, ⟨i, hi⟩, hmin⟩ :
      ∃ c, c ∈ Set.range (a x) ∧ ∀ j, c ≤ a x j :=
    ⟨sInf (Set.range (a x)), Nat.sInf_mem (Set.range_nonempty (a x)),
     fun j ↦ Nat.sInf_le ⟨j, rfl⟩⟩
  have hc1 : 1 < c := hi ▸ one_lt ha₀ ha₁ hx i
  -- the minimum is not a square: otherwise its square root would be a
  -- smaller element of the orbit
  have hnsq : ¬IsSquare c := by
    rintro ⟨r, hr⟩
    have h1 : a x (i + 1) = r := by
      rw [step_sq ha₁ hx (by rw [hi]; exact ⟨r, hr⟩), hi, hr, Nat.sqrt_eq]
    have h2 : c ≤ r := h1 ▸ hmin (i + 1)
    nlinarith [hr ▸ hc1]
  -- by the climb lemma and minimality, c ≤ √c + 3, whence c ≤ 5
  obtain ⟨j, hj⟩ := climb ha₁ hx hi (by rw [← hi]; exact hno2 i)
  have h5 : c ≤ c.sqrt + 3 := le_trans (hmin j) hj
  have hc5 : c ≤ 5 := by
    by_contra h6
    obtain ⟨d, rfl⟩ : ∃ d, c = d + 6 := ⟨c - 6, by lia⟩
    have h7 : d + 3 ≤ (d + 6).sqrt := by lia
    have h8 := Nat.le_sqrt.mp h7
    nlinarith
  -- the only possible minimum is 3
  have h2 := hno2 i
  rw [hi] at h2
  have hc3 : c = 3 := by
    interval_cases c
    · lia
    · rfl
    · exact absurd ⟨2, rfl⟩ hnsq
    · lia
  rw [hc3] at hi
  exact ⟨(three_dvd_iff ha₀ ha₁ hx i).mp (by rw [hi]), i, hi⟩

/-- Once the sequence hits 3, it cycles 3 → 6 → 9 → 3 forever. -/
lemma cycle (ha₁ : Rule a) (hx : 1 < x) {i : ℕ} (h : a x i = 3) :
    ∀ j, a x (i + 3 * j) = 3 := by
  intro j
  induction j with
  | zero => simpa using h
  | succ j ih =>
    have h6 : a x (i + 3 * j + 1) = 6 := by
      rw [step_nonsq ha₁ hx (by rw [ih]; norm_num), ih]
    have h9 : a x (i + 3 * j + 2) = 9 := by
      rw [show i + 3 * j + 2 = (i + 3 * j + 1) + 1 by ring,
          step_nonsq ha₁ hx (by rw [h6]; norm_num), h6]
    rw [show i + 3 * (j + 1) = (i + 3 * j + 2) + 1 by ring,
        step_sq ha₁ hx (by rw [h9]; exact ⟨3, by norm_num⟩), h9,
        show (9 : ℕ) = 3 * 3 by norm_num, Nat.sqrt_eq]

snip end

problem imo2017_p1
    (a : ℕ → ℕ → ℕ)
    (ha₀: ∀ x, a x 0 = x)
    (ha₁: ∀ x i, 1 < x → if IsSquare (a x i)
                         then a x (i + 1) = Nat.sqrt (a x i)
                         else a x (i + 1) = a x i + 3) :
    ∀ x > 1, (∃ A, {n | a x n = A}.Infinite) ↔ x ∈ solution_set := by
  intro x hx₀
  simp only [solution_set, Set.mem_setOf_eq]
  constructor
  · -- If some value recurs infinitely often, the sequence never reaches the
    -- class 2 mod 3, and then its minimum is 3, so 3 ∣ x.
    rintro ⟨A, hA⟩
    refine ⟨by lia, ?_⟩
    by_cases hex : ∃ i, a x i % 3 = 2
    · obtain ⟨i, hi⟩ := hex
      exact absurd (finite_visits ha₁ hx₀ hi A) hA
    · push Not at hex
      exact (orbit_min_three ha₀ ha₁ hx₀ hex).1
  · -- If 3 ∣ x, every term is divisible by 3, so the minimum of the orbit
    -- is 3 and the sequence ends up cycling 3 → 6 → 9 → 3.
    rintro ⟨-, h3⟩
    have hno2 : ∀ i, a x i % 3 ≠ 2 := by
      intro i
      have h := (three_dvd_iff ha₀ ha₁ hx₀ i).mpr h3
      lia
    obtain ⟨-, i, hi⟩ := orbit_min_three ha₀ ha₁ hx₀ hno2
    refine ⟨3, Set.infinite_of_injective_forall_mem
      (f := fun j : ℕ ↦ i + 3 * j) (fun p q hpq ↦ by lia) fun j ↦ ?_⟩
    exact cycle ha₁ hx₀ hi j


end Imo2017P1
