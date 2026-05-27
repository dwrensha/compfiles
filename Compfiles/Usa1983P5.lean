/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Order

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 1983, Problem 5

Consider an open interval of length 1/n on the real number line, where
n is a positive integer. Prove that the number of irreducible fractions
p/q, with 1 ≤ q ≤ n, contained in the given interval is at most (n + 1) / 2.
-/

namespace Usa1983P5

snip begin

-- Rationals in the interval with reduced denominator at most `n`.
def fracs (x : ℝ) (n : ℕ) : Set ℚ :=
  { q : ℚ | q.den ≤ n ∧ ↑q ∈ Set.Ioo x (x + 1 / n)}

def OccursDen (x : ℝ) (n d : ℕ) : Prop :=
  ∃ q ∈ fracs x n, q.den = d

noncomputable def denoms (x : ℝ) (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 n).filter fun d => OccursDen x n d

-- Openness of the interval gives strict spacing.
lemma dist_lt_interval_length
    {x : ℝ} {n : ℕ} (_hn : 0 < n) {r s : ℚ}
    (hr : r ∈ fracs x n) (hs : s ∈ fracs x n) :
    |(r : ℝ) - (s : ℝ)| < 1 / (n : ℝ) := by
  rcases hr.2 with ⟨hrx, hxr⟩
  rcases hs.2 with ⟨hsx, hxs⟩
  rw [abs_sub_lt_iff]
  constructor <;> linarith

lemma one_div_den_le_abs_rat {q : ℚ} (hq : q ≠ 0) :
    1 / (q.den : ℝ) ≤ |(q : ℝ)| := by
  have hnum_real : (1 : ℝ) ≤ |(q.num : ℝ)| := by
    exact_mod_cast Int.one_le_abs (Rat.num_ne_zero.2 hq)
  have hden_pos : 0 < (q.den : ℝ) := by
    exact_mod_cast Rat.den_pos q
  rw [Rat.cast_def, abs_div, abs_of_pos hden_pos]
  exact (div_le_div_iff_of_pos_right hden_pos).2 hnum_real

-- Spacing for denominators related by divisibility.
lemma one_div_den_le_dist_of_dvd_den
    {r s : ℚ} {d e : ℕ}
    (hrd : r.den = d) (hse : s.den = e)
    (hdiv : d ∣ e) (hne : r ≠ s) :
    1 / (e : ℝ) ≤ |(r : ℝ) - (s : ℝ)| := by
  have hepos : 0 < e := by
    rw [← hse]
    exact Rat.den_pos s
  -- The denominator of `r - s` divides any common denominator of `r` and `s`.
  have hden_dvd_e : (r - s).den ∣ e := by
    have hden_dvd_lcm : (r - s).den ∣ r.den.lcm s.den := Rat.sub_den_dvd_lcm r s
    have hlcm : r.den.lcm s.den = e := by
      rw [hrd, hse]
      exact Nat.lcm_eq_right hdiv
    simpa [hlcm] using hden_dvd_lcm
  have hden_le_e : (r - s).den ≤ e := Nat.le_of_dvd hepos hden_dvd_e
  have hlower := one_div_den_le_abs_rat (q := r - s) (sub_ne_zero.mpr hne)
  have hmono : 1 / (e : ℝ) ≤ 1 / ((r - s).den : ℝ) := by
    exact one_div_le_one_div_of_le
      (by exact_mod_cast Rat.den_pos (r - s) : (0 : ℝ) < (r - s).den)
      (by exact_mod_cast hden_le_e : ((r - s).den : ℝ) ≤ e)
  exact hmono.trans (by simpa [Rat.cast_sub] using hlower)

lemma same_den_unique
    {x : ℝ} {n : ℕ} (hn : 0 < n) {r s : ℚ}
    (hr : r ∈ fracs x n) (hs : s ∈ fracs x n)
    (hden : r.den = s.den) :
    r = s := by
  by_contra hne
  have hle_dist : 1 / (s.den : ℝ) ≤ |(r : ℝ) - (s : ℝ)| := by
    apply one_div_den_le_dist_of_dvd_den (r := r) (s := s) (d := r.den) (e := s.den)
    · rfl
    · rfl
    · rw [hden]
    · exact hne
  have hinterval := dist_lt_interval_length hn hr hs
  have hsdenpos : 0 < s.den := Rat.den_pos s
  have hle_one : 1 / (n : ℝ) ≤ 1 / (s.den : ℝ) := by
    exact one_div_le_one_div_of_le (by exact_mod_cast hsdenpos : (0 : ℝ) < s.den)
      (by exact_mod_cast hs.1 : (s.den : ℝ) ≤ n)
  linarith

lemma den_mem_denoms {x : ℝ} {n : ℕ} {q : ℚ} (hq : q ∈ fracs x n) :
    q.den ∈ denoms x n := by
  classical
  rw [denoms]
  simp only [Finset.mem_filter, Finset.mem_Icc, OccursDen]
  exact ⟨⟨Rat.den_pos q, hq.1⟩, q, hq, rfl⟩

-- Occurring denominators form a divisibility antichain.
lemma no_dvd_between_occurring_denoms
    {x : ℝ} {n d e : ℕ} (hn : 0 < n)
    (hd : d ∈ denoms x n) (he : e ∈ denoms x n) (hne : d ≠ e) :
    ¬ d ∣ e := by
  classical
  intro hdiv
  rw [denoms] at hd he
  simp only [Finset.mem_filter, Finset.mem_Icc, OccursDen] at hd he
  rcases hd.2 with ⟨r, hr, hrd⟩
  rcases he.2 with ⟨s, hs, hse⟩
  have hrs : r ≠ s := by
    intro hrs
    apply hne
    calc
      d = r.den := hrd.symm
      _ = s.den := by rw [hrs]
      _ = e := hse
  have hle_dist : 1 / (e : ℝ) ≤ |(r : ℝ) - (s : ℝ)| :=
    one_div_den_le_dist_of_dvd_den hrd hse hdiv hrs
  have hinterval := dist_lt_interval_length hn hr hs
  have hepos : 0 < e := Nat.succ_le_iff.mp he.1.1
  have hle_one : 1 / (n : ℝ) ≤ 1 / (e : ℝ) := by
    exact one_div_le_one_div_of_le (by exact_mod_cast hepos : (0 : ℝ) < e)
      (by exact_mod_cast he.1.2 : (e : ℝ) ≤ n)
  linarith

lemma den_bijOn (x : ℝ) (n : ℕ) (hn : 0 < n) :
    Set.BijOn (fun q : ℚ => q.den) (fracs x n) (denoms x n : Set ℕ) := by
  classical
  refine ⟨?maps, ?inj, ?surj⟩
  · intro q hq
    exact den_mem_denoms hq
  · intro r hr s hs hden
    exact same_den_unique hn hr hs hden
  · intro d hd
    rw [denoms] at hd
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, OccursDen] at hd
    rcases hd.2 with ⟨q, hq, hqd⟩
    exact ⟨q, hq, hqd⟩

lemma fracs_ncard_eq_denoms_card (x : ℝ) (n : ℕ) (hn : 0 < n) :
    (fracs x n).ncard = (denoms x n).card := by
  simpa using (den_bijOn x n hn).ncard_eq

lemma fracs_finite (x : ℝ) (n : ℕ) (hn : 0 < n) :
    (fracs x n).Finite := by
  exact ((den_bijOn x n hn).finite_iff_finite).2 (denoms x n).finite_toSet

-- Decompose `a` into its power-of-two factor and the remaining odd factor.
-- For positive `a`, `oddPart a` is the largest odd divisor.
def twoPart (a : ℕ) : ℕ :=
  2 ^ a.factorization 2

def oddPart (a : ℕ) : ℕ :=
  ordCompl[2] a

lemma twoPart_mul_oddPart (a : ℕ) : twoPart a * oddPart a = a := by
  simpa [twoPart, oddPart] using Nat.ordProj_mul_ordCompl_eq_self a 2

lemma oddPart_odd {a : ℕ} (ha : a ≠ 0) :
    Odd (oddPart a) := by
  exact Nat.not_even_iff_odd.mp (by
    rw [even_iff_two_dvd]
    simpa [oddPart] using Nat.not_dvd_ordCompl Nat.prime_two ha)

lemma oddPart_le_self (a : ℕ) :
    oddPart a ≤ a := by
  simpa [oddPart] using Nat.ordCompl_le a 2

lemma pos_of_mem_Icc_one {a n : ℕ} (ha : a ∈ Finset.Icc 1 n) :
    0 < a := by
  exact Nat.succ_le_iff.mp (Finset.mem_Icc.mp ha).1

lemma odd_eq_of_half_eq {a b : ℕ} (ha : Odd a) (hb : Odd b) (h : a / 2 = b / 2) :
    a = b := by
  calc
    a = 2 * (a / 2) + 1 := (Nat.two_mul_div_two_add_one_of_odd ha).symm
    _ = 2 * (b / 2) + 1 := by rw [h]
    _ = b := Nat.two_mul_div_two_add_one_of_odd hb

lemma oddPart_index_lt_half {a n : ℕ} (ha : a ∈ Finset.Icc 1 n) :
    oddPart a / 2 < (n + 1) / 2 := by
  have han : a ≤ n := (Finset.mem_Icc.mp ha).2
  have ha0 : a ≠ 0 := (pos_of_mem_Icc_one ha).ne'
  have hodd := oddPart_odd ha0
  have hle : oddPart a ≤ n := (oddPart_le_self a).trans han
  have hdecomp : 2 * (oddPart a / 2) + 1 = oddPart a :=
    Nat.two_mul_div_two_add_one_of_odd hodd
  omega

lemma dvd_or_dvd_of_oddPart_eq {a b : ℕ} (h : oddPart a = oddPart b) :
    a ∣ b ∨ b ∣ a := by
  by_cases hle : a.factorization 2 ≤ b.factorization 2
  · left
    have hp : 2 ^ a.factorization 2 ∣ 2 ^ b.factorization 2 := pow_dvd_pow 2 hle
    rcases hp with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [← twoPart_mul_oddPart a, ← twoPart_mul_oddPart b, twoPart, h, hc]
    ac_rfl
  · right
    have hle' : b.factorization 2 ≤ a.factorization 2 := le_of_not_ge hle
    have hp : 2 ^ b.factorization 2 ∣ 2 ^ a.factorization 2 := pow_dvd_pow 2 hle'
    rcases hp with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [← twoPart_mul_oddPart a, ← twoPart_mul_oddPart b, twoPart, h, hc]
    ac_rfl

lemma oddIndex_injective_of_no_dvd
    {s : Finset ℕ} {n : ℕ}
    (hs : s ⊆ Finset.Icc 1 n)
    (hantichain : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ¬ a ∣ b) :
    Function.Injective (fun a : {a // a ∈ s} =>
      (⟨oddPart a.1 / 2, oddPart_index_lt_half (hs a.2)⟩ : Fin ((n + 1) / 2))) := by
  intro a b habFin
  apply Subtype.ext
  by_cases hab : a.1 = b.1
  · exact hab
  exfalso
  have haIcc : a.1 ∈ Finset.Icc 1 n := hs a.2
  have hbIcc : b.1 ∈ Finset.Icc 1 n := hs b.2
  have ha0 : a.1 ≠ 0 := (pos_of_mem_Icc_one haIcc).ne'
  have hb0 : b.1 ≠ 0 := (pos_of_mem_Icc_one hbIcc).ne'
  have hhalf : oddPart a.1 / 2 = oddPart b.1 / 2 := congrArg Fin.val habFin
  have hpart : oddPart a.1 = oddPart b.1 :=
    odd_eq_of_half_eq (oddPart_odd ha0) (oddPart_odd hb0) hhalf
  rcases dvd_or_dvd_of_oddPart_eq hpart with hdvd | hdvd
  · exact hantichain a.1 a.2 b.1 b.2 hab hdvd
  · exact hantichain b.1 b.2 a.1 a.2 (Ne.symm hab) hdvd

-- Largest-odd-divisor pigeonhole step.
lemma card_le_half_of_no_dvd
    {s : Finset ℕ} {n : ℕ}
    (hs : s ⊆ Finset.Icc 1 n)
    (hantichain : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ¬ a ∣ b) :
    s.card ≤ (n + 1) / 2 := by
  classical
  let oddIndex : {a // a ∈ s} → Fin ((n + 1) / 2) := fun a =>
    ⟨oddPart a.1 / 2, oddPart_index_lt_half (hs a.2)⟩
  have oddIndex_injective : Function.Injective oddIndex := by
    simpa [oddIndex] using oddIndex_injective_of_no_dvd hs hantichain
  simpa [oddIndex] using Fintype.card_le_of_injective oddIndex oddIndex_injective

lemma denoms_subset_Icc (x : ℝ) (n : ℕ) :
    denoms x n ⊆ Finset.Icc 1 n := by
  classical
  intro d hd
  rw [denoms] at hd
  simp only [Finset.mem_filter] at hd
  simpa [Finset.mem_Icc] using hd.1

snip end

problem usa1983_p5 (x : ℝ) (n : ℕ) (hn : 0 < n) :
    let fracs := { q : ℚ | q.den ≤ n ∧ ↑q ∈ Set.Ioo x (x + 1 / n)}
    fracs.Finite ∧ fracs.ncard ≤ (n + 1) / 2 := by
  change (fracs x n).Finite ∧ (fracs x n).ncard ≤ (n + 1) / 2
  refine ⟨fracs_finite x n hn, ?_⟩
  calc
    (fracs x n).ncard = (denoms x n).card := fracs_ncard_eq_denoms_card x n hn
    _ ≤ (n + 1) / 2 := by
      apply card_le_half_of_no_dvd (denoms_subset_Icc x n)
      intro a ha b hb hne
      exact no_dvd_between_occurring_denoms hn ha hb hne

end Usa1983P5
