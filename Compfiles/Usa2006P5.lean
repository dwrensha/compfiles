/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Zify
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics, .NumberTheory] }

/-!
# USA Mathematical Olympiad 2006, Problem 5

A mathematical frog jumps along the number line. The frog starts at 1,
and jumps according to the following rule: if the frog is at integer n,
then it can jump either to n + 1 or to n + 2 ^ (mₙ + 1), where 2 ^ mₙ is
the largest power of 2 that is a factor of n. Show that if k ≥ 2 is a
positive integer and i is a nonnegative integer, then the minimum number
of jumps needed to reach 2 ^ i * k is greater than the minimum number of
jumps needed to reach 2 ^ i.
-/

namespace Usa2006P5

/-- The exponent of the largest power of `2` dividing the integer `x`
(the 2-adic valuation of `x`). -/
noncomputable def nu (x : ℤ) : ℕ := x.natAbs.factorization 2

/-- `ValidPath x ss` holds when the list `ss` of jump lengths can legally be
performed by the frog starting at position `x`: each jump has length `1` or
length `2 ^ (ν₂ n + 1)`, where `n` is the position the frog jumps from. -/
def ValidPath : ℤ → List ℕ → Prop
  | _, [] => True
  | x, s :: ss => (s = 1 ∨ s = 2 ^ (nu x + 1)) ∧ ValidPath (x + (s : ℤ)) ss

/-- The frog can reach position `m` in exactly `j` jumps starting from `1`. -/
def Reachable (m : ℤ) (j : ℕ) : Prop :=
  ∃ ss : List ℕ, ValidPath 1 ss ∧ (1 : ℤ) + (ss.sum : ℤ) = m ∧ ss.length = j

/-- The minimum number of jumps the frog needs to reach position `m`. -/
noncomputable def minJumps (m : ℤ) : ℕ := sInf { j | Reachable m j }

snip begin

/-- `BigBound m c x ss` holds when every jump of `ss` (performed starting from
position `x`) that ends at a position greater than `c` has length at most
`2 ^ m`. -/
def BigBound (m : ℕ) (c : ℤ) : ℤ → List ℕ → Prop
  | _, [] => True
  | x, s :: ss => (c < x + (s : ℤ) → s ≤ 2 ^ m) ∧ BigBound m c (x + (s : ℤ)) ss

/-- `filt e c y ss` processes the list of jumps `ss` starting at position `y`,
deleting every jump whose length is divisible by `2 ^ (e + 1)` and which lands
at a position greater than `c`.  This is the deletion operation of the
official solution: deleting such jumps keeps the path valid. -/
def filt (e : ℕ) (c : ℤ) : ℤ → List ℕ → List ℕ
  | _, [] => []
  | y, s :: ss =>
    if (2 : ℤ) ^ (e + 1) ∣ (s : ℤ) ∧ c < y + (s : ℤ) then filt e c y ss
    else s :: filt e c (y + (s : ℤ)) ss

@[simp] lemma natAbs_two_pow (n : ℕ) : ((2 : ℤ) ^ n).natAbs = 2 ^ n := by
  rw [Int.natAbs_pow]
  norm_num

lemma two_pow_nu_dvd (x : ℤ) : (2 : ℤ) ^ nu x ∣ x := by
  rw [← Int.natAbs_dvd_natAbs, natAbs_two_pow]
  exact Nat.ordProj_dvd _ _

lemma not_two_pow_succ_nu_dvd {x : ℤ} (hx : x ≠ 0) : ¬ (2 : ℤ) ^ (nu x + 1) ∣ x := by
  rw [← Int.natAbs_dvd_natAbs, natAbs_two_pow]
  exact Nat.pow_succ_factorization_not_dvd (Int.natAbs_ne_zero.mpr hx) Nat.prime_two

/-- The 2-adic valuation is characterized by divisibility. -/
lemma nu_eq_of {x : ℤ} {a : ℕ} (hx : x ≠ 0) (h1 : (2 : ℤ) ^ a ∣ x)
    (h2 : ¬ (2 : ℤ) ^ (a + 1) ∣ x) : nu x = a := by
  rcases lt_trichotomy a (nu x) with h | h | h
  · exfalso
    exact h2 (dvd_trans (pow_dvd_pow (2 : ℤ) (by lia : a + 1 ≤ nu x)) (two_pow_nu_dvd x))
  · exact h.symm
  · exfalso
    exact not_two_pow_succ_nu_dvd hx
      (dvd_trans (pow_dvd_pow (2 : ℤ) (by lia : nu x + 1 ≤ a)) h1)

/-- Shifting by a multiple of `2 ^ e` does not change the 2-adic valuation,
as long as the valuation is smaller than `e`. -/
lemma nu_congr {y y' : ℤ} {e : ℕ} (hy : y ≠ 0) (hy' : y' ≠ 0)
    (hd : (2 : ℤ) ^ e ∣ y - y') (hlt : nu y < e) : nu y' = nu y := by
  refine nu_eq_of hy' ?_ ?_
  · have h1 : (2 : ℤ) ^ nu y ∣ y - y' := dvd_trans (pow_dvd_pow _ (by lia : nu y ≤ e)) hd
    have h2 : (2 : ℤ) ^ nu y ∣ y := two_pow_nu_dvd y
    have h3 : y' = y - (y - y') := by ring
    rw [h3]
    exact dvd_sub h2 h1
  · intro h
    have h1 : (2 : ℤ) ^ (nu y + 1) ∣ y - y' :=
      dvd_trans (pow_dvd_pow _ (by lia : nu y + 1 ≤ e)) hd
    have h2 : (2 : ℤ) ^ (nu y + 1) ∣ y := by
      have h3 : y = y' + (y - y') := by ring
      have h4 := dvd_add h h1
      rwa [← h3] at h4
    exact not_two_pow_succ_nu_dvd hy h2

lemma validPath_cons {x : ℤ} {s : ℕ} {ss : List ℕ} :
    ValidPath x (s :: ss) ↔ (s = 1 ∨ s = 2 ^ (nu x + 1)) ∧ ValidPath (x + (s : ℤ)) ss :=
  Iff.rfl

lemma ValidPath.append {x : ℤ} {l₁ l₂ : List ℕ} :
    ValidPath x (l₁ ++ l₂) ↔ ValidPath x l₁ ∧ ValidPath (x + (l₁.sum : ℤ)) l₂ := by
  induction l₁ generalizing x with
  | nil => simp [ValidPath]
  | cons s ss ih =>
    rw [List.cons_append, validPath_cons, ih]
    have h4 : (x : ℤ) + ((s :: ss).sum : ℤ) = (x + (s : ℤ)) + (ss.sum : ℤ) := by
      rw [List.sum_cons, Nat.cast_add]
      ring
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨validPath_cons.mpr ⟨h1, h2⟩, h4 ▸ h3⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨h1a, h1b⟩ := validPath_cons.mp h1
      exact ⟨h1a, h1b, h4 ▸ h2⟩

/-- Every jump of a valid path is a power of two. -/
lemma ValidPath.pow_two {x : ℤ} {ss : List ℕ} (h : ValidPath x ss) :
    ∀ s ∈ ss, ∃ t, s = 2 ^ t := by
  induction ss generalizing x with
  | nil => intro s hs; simp at hs
  | cons s ss ih =>
    intro t ht
    obtain ⟨h1, h2⟩ := validPath_cons.mp h
    rcases List.mem_cons.mp ht with rfl | ht
    · rcases h1 with rfl | h1
      · exact ⟨0, rfl⟩
      · exact ⟨nu x + 1, h1⟩
    · exact ih h2 t ht

lemma ValidPath.one_le_of_mem {x : ℤ} {ss : List ℕ} (h : ValidPath x ss) {s : ℕ}
    (hs : s ∈ ss) : 1 ≤ s := by
  obtain ⟨t, rfl⟩ := h.pow_two s hs
  exact Nat.one_le_two_pow

lemma bigBound_cons {m : ℕ} {c x : ℤ} {s : ℕ} {ss : List ℕ} :
    BigBound m c x (s :: ss) ↔ (c < x + (s : ℤ) → s ≤ 2 ^ m) ∧ BigBound m c (x + (s : ℤ)) ss :=
  Iff.rfl

lemma bigBound_of_forall {m : ℕ} {c x : ℤ} {ss : List ℕ} (h : ∀ s ∈ ss, s ≤ 2 ^ m) :
    BigBound m c x ss := by
  induction ss generalizing x with
  | nil => trivial
  | cons s ss ih =>
    rw [bigBound_cons]
    exact ⟨fun _ => h s (List.mem_cons_self (a := s) (l := ss)), ih (fun t ht => h t (List.mem_cons_of_mem s ht))⟩

/-- A jump that is deleted by `filt` (divisible by `2 ^ (e + 1)` and landing
beyond `c`) must have length exactly `2 ^ (e + 1)`, because all jumps landing
beyond `c` have length at most `2 ^ (e + 1)`. -/
lemma eq_two_pow_of {e : ℕ} {c y y' : ℤ} {s : ℕ}
    (hs1 : 1 ≤ s) (hdvd : (2 : ℤ) ^ (e + 1) ∣ (s : ℤ)) (hc : c < y' + (s : ℤ))
    (hyy' : y' ≤ y) (hbb1 : c < y + (s : ℤ) → s ≤ 2 ^ (e + 1)) :
    s = 2 ^ (e + 1) := by
  have h1 : s ≤ 2 ^ (e + 1) := hbb1 (by linarith)
  have h2 : 2 ^ (e + 1) ∣ s := by
    rw [← Int.natCast_dvd_natCast]
    push_cast
    exact hdvd
  have h3 : 2 ^ (e + 1) ≤ s := Nat.le_of_dvd (by lia) h2
  exact le_antisymm h1 h3

lemma filt_cons_delete {e : ℕ} {c y : ℤ} {s : ℕ} {ss : List ℕ}
    (h1 : (2 : ℤ) ^ (e + 1) ∣ (s : ℤ)) (h2 : c < y + (s : ℤ)) :
    filt e c y (s :: ss) = filt e c y ss := by
  simp [filt, h1, h2]

lemma filt_cons_keep {e : ℕ} {c y : ℤ} {s : ℕ} {ss : List ℕ}
    (h : ¬ ((2 : ℤ) ^ (e + 1) ∣ (s : ℤ) ∧ c < y + (s : ℤ))) :
    filt e c y (s :: ss) = s :: filt e c (y + (s : ℤ)) ss := by
  simp [filt, h]

/-- The key validity lemma: after deleting jumps divisible by `2 ^ (e + 1)`
that land beyond `c`, the remaining path is still valid.  The hypothesis
`hor` says that either no jump has been deleted so far (so the two positions
coincide), or the current filtered position is within `2 ^ (e + 1)` beyond
which no deletion can have occurred yet. -/
lemma filt_valid {e : ℕ} {c y y' : ℤ} {ss : List ℕ}
    (hv : ValidPath y ss) (hy : 1 ≤ y) (hy' : 1 ≤ y') (hyy' : y' ≤ y)
    (hdvd : (2 : ℤ) ^ (e + 1) ∣ y - y')
    (hor : y = y' ∨ c < y' + 2 ^ (e + 1))
    (hbb : BigBound (e + 1) c y ss) :
    ValidPath y' (filt e c y' ss) := by
  induction ss generalizing y y' with
  | nil => trivial
  | cons s ss ih =>
    obtain ⟨hs1, hs2⟩ := validPath_cons.mp hv
    obtain ⟨hbb1, hbb2⟩ := bigBound_cons.mp hbb
    have hsge : 1 ≤ s := by
      rcases hs1 with h | h
      · lia
      · rw [h]; exact Nat.one_le_two_pow
    have hsgez : (0 : ℤ) ≤ (s : ℤ) := Nat.cast_nonneg s
    by_cases hdel : (2 : ℤ) ^ (e + 1) ∣ (s : ℤ) ∧ c < y' + (s : ℤ)
    · rw [filt_cons_delete hdel.1 hdel.2]
      have hseq : s = 2 ^ (e + 1) := eq_two_pow_of hsge hdel.1 hdel.2 hyy' hbb1
      refine ih hs2 (by linarith) hy' (by linarith) ?_ ?_ hbb2
      · have h1 : (y + (s : ℤ)) - y' = (y - y') + (s : ℤ) := by ring
        rw [h1]
        exact dvd_add hdvd hdel.1
      · right
        have h2 := hdel.2
        rw [hseq, Nat.cast_pow, Nat.cast_ofNat] at h2
        exact h2
    · rw [filt_cons_keep hdel, validPath_cons]
      refine ⟨?_, ?_⟩
      · rcases hs1 with h | h
        · exact Or.inl h
        · right
          by_cases hd : (2 : ℤ) ^ (e + 1) ∣ (s : ℤ)
          · have hle : y' + (s : ℤ) ≤ c := by
              by_contra hcon
              push Not at hcon
              exact hdel ⟨hd, hcon⟩
            have hsge' : (2 : ℤ) ^ (e + 1) ≤ (s : ℤ) :=
              Int.le_of_dvd (by exact_mod_cast hsge) hd
            rcases hor with heq | hlt
            · rw [← heq]
              exact h
            · exfalso
              linarith
          · have hlt : nu y < e + 1 := by
              by_contra hcon
              push Not at hcon
              apply hd
              rw [h, Nat.cast_pow, Nat.cast_ofNat]
              exact pow_dvd_pow _ (by lia : e + 1 ≤ nu y + 1)
            rw [nu_congr (by linarith) (by linarith) hdvd hlt]
            exact h
      · refine ih hs2 (by linarith) (by linarith) (by linarith) ?_ ?_ hbb2
        · have h1 : (y + (s : ℤ)) - (y' + (s : ℤ)) = y - y' := by ring
          rw [h1]
          exact hdvd
        · rcases hor with heq | hlt
          · exact Or.inl (by rw [heq])
          · exact Or.inr (by linarith)

/-- Counting lemma: the total length deleted by `filt` is a multiple of
`2 ^ (e + 1)`, and the number of deleted jumps equals that multiple. -/
lemma filt_count {e : ℕ} {c y y' : ℤ} {ss : List ℕ}
    (hp2 : ∀ s ∈ ss, ∃ t, s = 2 ^ t) (hyy' : y' ≤ y) (hbb : BigBound (e + 1) c y ss) :
    ∃ r : ℕ, ((ss.sum : ℤ) - ((filt e c y' ss).sum : ℤ)) = (r : ℤ) * 2 ^ (e + 1) ∧
      ss.length = (filt e c y' ss).length + r := by
  induction ss generalizing y y' with
  | nil => exact ⟨0, by simp [filt]⟩
  | cons s ss ih =>
    obtain ⟨hbb1, hbb2⟩ := bigBound_cons.mp hbb
    have hsge : 1 ≤ s := by
      obtain ⟨t, rfl⟩ := hp2 s (List.mem_cons_self (a := s) (l := ss))
      exact Nat.one_le_two_pow
    by_cases hdel : (2 : ℤ) ^ (e + 1) ∣ (s : ℤ) ∧ c < y' + (s : ℤ)
    · rw [filt_cons_delete hdel.1 hdel.2]
      have hseq : s = 2 ^ (e + 1) := eq_two_pow_of hsge hdel.1 hdel.2 hyy' hbb1
      obtain ⟨r, hr1, hr2⟩ := ih (fun t ht => hp2 t (List.mem_cons_of_mem s ht))
        (by linarith [hyy', ((Nat.cast_nonneg s) : (0 : ℤ) ≤ (s : ℤ))] : y' ≤ y + (s : ℤ)) hbb2
      refine ⟨r + 1, ?_, ?_⟩
      · rw [List.sum_cons, Nat.cast_add, hseq, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add,
          Nat.cast_one]
        linarith [hr1]
      · rw [List.length_cons, hr2]
        lia
    · rw [filt_cons_keep hdel]
      obtain ⟨r, hr1, hr2⟩ := ih (fun t ht => hp2 t (List.mem_cons_of_mem s ht))
        (by linarith [((Nat.cast_nonneg s) : (0 : ℤ) ≤ (s : ℤ))] : y' + (s : ℤ) ≤ y + (s : ℤ)) hbb2
      refine ⟨r, ?_, ?_⟩
      · rw [List.sum_cons, List.sum_cons, Nat.cast_add, Nat.cast_add]
        linarith [hr1]
      · rw [List.length_cons, List.length_cons, hr2]
        lia

/-- Lower bound lemma: if `filt` deletes at least one jump, then the last
deleted jump starts at a position `p'` whose 2-adic valuation is exactly `e`,
which lands beyond `c`, and which is at most the final endpoint. -/
lemma filt_lower {e : ℕ} {c y y' : ℤ} {ss : List ℕ}
    (hv : ValidPath y ss) (hy : 1 ≤ y) (hy' : 1 ≤ y') (hyy' : y' ≤ y)
    (hdvd : (2 : ℤ) ^ (e + 1) ∣ y - y') (hbb : BigBound (e + 1) c y ss)
    (hlen : (filt e c y' ss).length < ss.length) :
    ∃ p' : ℤ, 1 ≤ p' ∧ nu p' = e ∧ c < p' + 2 ^ (e + 1) ∧
      p' ≤ y' + ((filt e c y' ss).sum : ℤ) := by
  induction ss generalizing y y' with
  | nil => simp at hlen
  | cons s ss ih =>
    obtain ⟨hs1, hs2⟩ := validPath_cons.mp hv
    obtain ⟨hbb1, hbb2⟩ := bigBound_cons.mp hbb
    have hsge : 1 ≤ s := by
      rcases hs1 with h | h
      · lia
      · rw [h]; exact Nat.one_le_two_pow
    by_cases hdel : (2 : ℤ) ^ (e + 1) ∣ (s : ℤ) ∧ c < y' + (s : ℤ)
    · rw [filt_cons_delete hdel.1 hdel.2] at hlen ⊢
      have hseq : s = 2 ^ (e + 1) := eq_two_pow_of hsge hdel.1 hdel.2 hyy' hbb1
      by_cases hlen2 : (filt e c y' ss).length < ss.length
      · refine ih hs2 (by linarith [hy, ((Nat.cast_nonneg s) : (0 : ℤ) ≤ (s : ℤ))]) hy'
          (by linarith [hyy', ((Nat.cast_nonneg s) : (0 : ℤ) ≤ (s : ℤ))] : y' ≤ y + (s : ℤ)) ?_ hbb2 hlen2
        have h1 : (y + (s : ℤ)) - y' = (y - y') + (s : ℤ) := by ring
        rw [h1]
        exact dvd_add hdvd hdel.1
      · refine ⟨y', hy', ?_, ?_, ?_⟩
        · have hnuy : nu y = e := by
            rcases hs1 with h | h
            · rw [h] at hseq
              have h2 : (1 : ℕ) < 2 ^ (e + 1) := one_lt_pow₀ (by norm_num : (1 : ℕ) < 2) (by lia : e + 1 ≠ 0)
              lia
            · rw [h] at hseq
              have h2 := Nat.pow_right_injective (by norm_num : 2 ≤ 2) hseq
              lia
          rw [← hnuy]
          exact nu_congr (by linarith) (by linarith) hdvd (by lia)
        · have h2 := hdel.2
          rw [hseq, Nat.cast_pow, Nat.cast_ofNat] at h2
          exact h2
        · have h3 : (0 : ℤ) ≤ ((filt e c y' ss).sum : ℤ) := Nat.cast_nonneg _
          linarith
    · rw [filt_cons_keep hdel] at hlen ⊢
      rw [List.length_cons, List.length_cons] at hlen
      obtain ⟨p', hp1, hpnu, hpc, hpT⟩ := ih hs2
        (by linarith [hy, ((Nat.cast_nonneg s) : (0 : ℤ) ≤ (s : ℤ))])
        (by linarith [hy', ((Nat.cast_nonneg s) : (0 : ℤ) ≤ (s : ℤ))] : 1 ≤ y' + (s : ℤ))
        (by linarith [hyy', ((Nat.cast_nonneg s) : (0 : ℤ) ≤ (s : ℤ))])
        (by
          have h1 : (y + (s : ℤ)) - (y' + (s : ℤ)) = y - y' := by ring
          rw [h1]
          exact hdvd)
        hbb2 (by lia)
      exact ⟨p', hp1, hpnu, hpc, by
        rw [List.sum_cons, Nat.cast_add]
        have h4 : (0 : ℤ) ≤ (s : ℤ) := Nat.cast_nonneg _
        linarith [hpT]⟩

/-- Transfer lemma: after `filt` has removed the jumps of length `2 ^ (e + 1)`,
every remaining jump landing beyond `c` has length at most `2 ^ e`. -/
lemma filt_bigbound {e : ℕ} {c y y' : ℤ} {ss : List ℕ}
    (hp2 : ∀ s ∈ ss, ∃ t, s = 2 ^ t) (hyy' : y' ≤ y) (hbb : BigBound (e + 1) c y ss) :
    BigBound e c y' (filt e c y' ss) := by
  induction ss generalizing y y' with
  | nil => trivial
  | cons s ss ih =>
    obtain ⟨hbb1, hbb2⟩ := bigBound_cons.mp hbb
    by_cases hdel : (2 : ℤ) ^ (e + 1) ∣ (s : ℤ) ∧ c < y' + (s : ℤ)
    · rw [filt_cons_delete hdel.1 hdel.2]
      exact ih (fun t ht => hp2 t (List.mem_cons_of_mem s ht))
        (by linarith [hyy', ((Nat.cast_nonneg s) : (0 : ℤ) ≤ (s : ℤ))] : y' ≤ y + (s : ℤ)) hbb2
    · rw [filt_cons_keep hdel, bigBound_cons]
      refine ⟨?_, ?_⟩
      · intro hc
        have hndvd : ¬ (2 : ℤ) ^ (e + 1) ∣ (s : ℤ) := fun h => hdel ⟨h, hc⟩
        have hle : s ≤ 2 ^ (e + 1) := hbb1 (by linarith)
        obtain ⟨t, rfl⟩ := hp2 s (List.mem_cons_self (a := s) (l := ss))
        have ht : t ≤ e := by
          by_contra hcon
          push Not at hcon
          apply hndvd
          rw [Nat.cast_pow, Nat.cast_ofNat]
          exact pow_dvd_pow _ (by lia : e + 1 ≤ t)
        exact Nat.pow_le_pow_right (by norm_num) ht
      · exact ih (fun t ht => hp2 t (List.mem_cons_of_mem s ht))
          (by linarith [((Nat.cast_nonneg s) : (0 : ℤ) ≤ (s : ℤ))] : y' + (s : ℤ) ≤ y + (s : ℤ)) hbb2

/-- Base case of the main induction: if every jump landing beyond `2 ^ i` has
length `1`, then some prefix of the path ends exactly at `2 ^ i`. -/
lemma base_prefix {x : ℤ} {i : ℕ} {ss : List ℕ} (hx1 : 1 ≤ x) (hx2 : x ≤ (2 : ℤ) ^ i)
    (hv : ValidPath x ss) (hbb : BigBound 0 ((2 : ℤ) ^ i) x ss)
    (hge : (2 : ℤ) ^ i ≤ x + (ss.sum : ℤ)) :
    ∃ ss' : List ℕ, ss' <+: ss ∧ x + (ss'.sum : ℤ) = (2 : ℤ) ^ i := by
  induction ss generalizing x with
  | nil =>
    have hx : x = (2 : ℤ) ^ i := by
      simp only [List.sum_nil, Nat.cast_zero, add_zero] at hge
      linarith
    exact ⟨[], ⟨[], rfl⟩, by simp only [List.sum_nil, Nat.cast_zero, add_zero]; exact hx⟩
  | cons s ss ih =>
    obtain ⟨hs1, hs2⟩ := validPath_cons.mp hv
    obtain ⟨hbb1, hbb2⟩ := bigBound_cons.mp hbb
    have hsge : 1 ≤ s := by
      rcases hs1 with h | h
      · lia
      · rw [h]; exact Nat.one_le_two_pow
    by_cases hcase : x + (s : ℤ) ≤ (2 : ℤ) ^ i
    · have hge' : (2 : ℤ) ^ i ≤ (x + (s : ℤ)) + (ss.sum : ℤ) := by
        have h1 : ((s :: ss).sum : ℤ) = (s : ℤ) + (ss.sum : ℤ) := by
          rw [List.sum_cons, Nat.cast_add]
        linarith [hge]
      obtain ⟨ss', hpre, hend⟩ := ih (by linarith [hx1, ((Nat.cast_nonneg s) : (0 : ℤ) ≤ (s : ℤ))]) hcase hs2 hbb2 hge'
      obtain ⟨t, ht⟩ := hpre
      refine ⟨s :: ss', ⟨t, by rw [List.cons_append, ht]⟩, ?_⟩
      rw [List.sum_cons, Nat.cast_add]
      linarith [hend]
    · push Not at hcase
      have hsle : s ≤ 2 ^ 0 := hbb1 hcase
      simp at hsle
      have hs1' : s = 1 := by lia
      refine ⟨[], ⟨s :: ss, rfl⟩, ?_⟩
      simp only [List.sum_nil, Nat.cast_zero, add_zero]
      have h2 : (s : ℤ) = 1 := by exact_mod_cast hs1'
      linarith

/-- The main induction.  From a valid path whose endpoint is at least `2 ^ i`
and divisible by `2 ^ min i e`, where every jump landing beyond `2 ^ i` has
length at most `2 ^ e`, we can extract a valid path to `2 ^ i` of at most the
same length, and strictly shorter if the original endpoint exceeds `2 ^ i`. -/
lemma key_lemma (i : ℕ) (e : ℕ) (ss : List ℕ)
    (hv : ValidPath 1 ss) (hbb : BigBound e ((2 : ℤ) ^ i) 1 ss)
    (hdiv : (2 : ℤ) ^ min i e ∣ (1 : ℤ) + (ss.sum : ℤ))
    (hge : (2 : ℤ) ^ i ≤ (1 : ℤ) + (ss.sum : ℤ)) :
    ∃ ss' : List ℕ, ValidPath 1 ss' ∧ (1 : ℤ) + (ss'.sum : ℤ) = (2 : ℤ) ^ i ∧
      ss'.length ≤ ss.length ∧ ((2 : ℤ) ^ i < (1 : ℤ) + (ss.sum : ℤ) → ss'.length < ss.length) := by
  induction e generalizing ss with
  | zero =>
    obtain ⟨ss', hpre, hend⟩ := base_prefix le_rfl
      (by have := pow_pos (by norm_num : (0 : ℤ) < 2) i; linarith) hv hbb hge
    obtain ⟨t, ht⟩ := hpre
    refine ⟨ss', ?_, hend, ?_, ?_⟩
    · rw [← ht] at hv
      exact (ValidPath.append.mp hv).1
    · rw [← ht, List.length_append]
      lia
    · intro hT
      rw [← ht, List.length_append]
      by_cases ht' : t = []
      · subst ht'
        rw [List.append_nil] at ht
        subst ht
        rw [hend] at hT
        exact absurd hT (lt_irrefl _)
      · have hpos : 0 < t.length := by
          cases t with
          | nil => contradiction
          | cons => simp
        lia
  | succ e ih =>
    have hp2 : ∀ s ∈ ss, ∃ t, s = 2 ^ t := hv.pow_two
    have hF1 : ValidPath 1 (filt e ((2 : ℤ) ^ i) 1 ss) :=
      filt_valid hv le_rfl le_rfl le_rfl (dvd_zero _) (Or.inl rfl) hbb
    obtain ⟨r, hr1, hr2⟩ := filt_count hp2 le_rfl hbb
    have hF4 : BigBound e ((2 : ℤ) ^ i) 1 (filt e ((2 : ℤ) ^ i) 1 ss) :=
      filt_bigbound hp2 le_rfl hbb
    have hdiv₁ : (2 : ℤ) ^ min i e ∣ (1 : ℤ) + ((filt e ((2 : ℤ) ^ i) 1 ss).sum : ℤ) := by
      have h1 : (2 : ℤ) ^ min i e ∣ (1 : ℤ) + (ss.sum : ℤ) :=
        dvd_trans (pow_dvd_pow _ (by lia : min i e ≤ min i (e + 1))) hdiv
      have h2 : (2 : ℤ) ^ min i e ∣ (r : ℤ) * 2 ^ (e + 1) :=
        dvd_trans (pow_dvd_pow _ (by lia : min i e ≤ e + 1)) (dvd_mul_left _ _)
      have h3 : (1 : ℤ) + ((filt e ((2 : ℤ) ^ i) 1 ss).sum : ℤ) =
          ((1 : ℤ) + (ss.sum : ℤ)) - (r : ℤ) * 2 ^ (e + 1) := by
        linarith [hr1]
      rw [h3]
      exact dvd_sub h1 h2
    have hge₁ : (2 : ℤ) ^ i ≤ (1 : ℤ) + ((filt e ((2 : ℤ) ^ i) 1 ss).sum : ℤ) := by
      by_cases hr0 : r = 0
      · have hr1' : (ss.sum : ℤ) = ((filt e ((2 : ℤ) ^ i) 1 ss).sum : ℤ) := by
          subst hr0
          simp only [Nat.cast_zero, zero_mul] at hr1
          linarith [hr1]
        linarith [hge, hr1']
      · have hrlen : (filt e ((2 : ℤ) ^ i) 1 ss).length < ss.length := by lia
        obtain ⟨p', hp1, hpnu, hpc, hpT⟩ :=
          filt_lower hv le_rfl le_rfl le_rfl (dvd_zero _) hbb hrlen
        by_cases hei : i ≤ e
        · have hpp : (2 : ℤ) ^ e ∣ p' := by
            rw [← hpnu]
            exact two_pow_nu_dvd p'
          have hge2 : (2 : ℤ) ^ e ≤ p' := Int.le_of_dvd (by linarith) hpp
          have hge3 : (2 : ℤ) ^ i ≤ (2 : ℤ) ^ e := pow_le_pow_right₀ (by norm_num) hei
          linarith [hpT]
        · push Not at hei
          by_contra hlt
          push Not at hlt
          have hmin : min i e = e := by lia
          rw [hmin] at hdiv₁
          obtain ⟨u, hu⟩ : (2 : ℤ) ^ e ∣ p' := by
            rw [← hpnu]
            exact two_pow_nu_dvd p'
          have hpow : (2 : ℤ) ^ i = (2 : ℤ) ^ e * (2 : ℤ) ^ (i - e) := by
            rw [← pow_add]
            congr 1
            lia
          have hpow2 : (2 : ℤ) ^ (e + 1) = (2 : ℤ) ^ e * 2 := pow_succ _ _
          have hub : (2 : ℤ) ^ (i - e) ≤ u + 1 := by
            rw [hpow, hu, hpow2] at hpc
            have h7 : (2 : ℤ) ^ e * u + (2 : ℤ) ^ e * 2 = (2 : ℤ) ^ e * (u + 2) := by ring
            rw [h7] at hpc
            have hpos : (0 : ℤ) < (2 : ℤ) ^ e := by positivity
            have h6 := lt_of_mul_lt_mul_left hpc (le_of_lt hpos)
            lia
          obtain ⟨v, hv⟩ := hdiv₁
          have huv : u ≤ v := by
            rw [hv, hu] at hpT
            have hpos : (0 : ℤ) < (2 : ℤ) ^ e := by positivity
            exact le_of_mul_le_mul_left hpT hpos
          have hvb : v < (2 : ℤ) ^ (i - e) := by
            rw [hv, hpow] at hlt
            have hpos : (0 : ℤ) < (2 : ℤ) ^ e := by positivity
            exact lt_of_mul_lt_mul_left hlt (le_of_lt hpos)
          have hveq : v = (2 : ℤ) ^ (i - e) - 1 := by lia
          have hmin2 : min i (e + 1) = e + 1 := by lia
          rw [hmin2] at hdiv
          have hT_eq : (1 : ℤ) + (ss.sum : ℤ) = (2 : ℤ) ^ e * v + (r : ℤ) * 2 ^ (e + 1) := by
            linarith [hr1, hv]
          have hdvd2 : (2 : ℤ) ^ (e + 1) ∣ (2 : ℤ) ^ e * v := by
            have h7 : (2 : ℤ) ^ (e + 1) ∣ (r : ℤ) * 2 ^ (e + 1) := dvd_mul_left _ _
            have h8 := dvd_sub hdiv h7
            rw [hT_eq] at h8
            have h9 : (2 : ℤ) ^ e * v + (r : ℤ) * 2 ^ (e + 1) - (r : ℤ) * 2 ^ (e + 1) =
                (2 : ℤ) ^ e * v := by ring
            rw [h9] at h8
            exact h8
          have h2v : (2 : ℤ) ∣ v := by
            rw [hpow2] at hdvd2
            exact (mul_dvd_mul_iff_left (by positivity : (2 : ℤ) ^ e ≠ 0)).mp hdvd2
          have hodd : ¬ (2 : ℤ) ∣ v := by
            intro h2v'
            have h10 : (2 : ℤ) ∣ (2 : ℤ) ^ (i - e) := by
              have h14 : (2 : ℤ) ^ (1 : ℕ) ∣ (2 : ℤ) ^ (i - e) := pow_dvd_pow _ (by lia : 1 ≤ i - e)
              rwa [pow_one] at h14
            have h11 := dvd_sub h10 h2v'
            have h12 : (2 : ℤ) ^ (i - e) - v = 1 := by lia
            rw [h12] at h11
            norm_num at h11
          exact hodd h2v
    obtain ⟨ss', hv', hend', hlen', hstrict'⟩ := ih _ hF1 hF4 hdiv₁ hge₁
    refine ⟨ss', hv', hend', le_trans hlen' (by lia), ?_⟩
    intro hT
    by_cases hr0 : r = 0
    · have hr1' : (ss.sum : ℤ) = ((filt e ((2 : ℤ) ^ i) 1 ss).sum : ℤ) := by
        subst hr0
        simp only [Nat.cast_zero, zero_mul] at hr1
        linarith [hr1]
      have h2 : (2 : ℤ) ^ i < (1 : ℤ) + ((filt e ((2 : ℤ) ^ i) 1 ss).sum : ℤ) := by
        linarith [hT, hr1']
      have h3 : (filt e ((2 : ℤ) ^ i) 1 ss).length = ss.length := by lia
      calc ss'.length < (filt e ((2 : ℤ) ^ i) 1 ss).length := hstrict' h2
        _ = ss.length := h3
    · have h4 : (filt e ((2 : ℤ) ^ i) 1 ss).length < ss.length := by lia
      exact lt_of_le_of_lt hlen' h4

lemma validPath_replicate_one (x : ℤ) (n : ℕ) : ValidPath x (List.replicate n 1) := by
  induction n generalizing x with
  | zero => trivial
  | succ n ih =>
    rw [List.replicate_succ, validPath_cons]
    exact ⟨Or.inl rfl, ih (x + 1)⟩

/-- Every position `m ≥ 1` is reachable, by jumping `+1` every time. -/
lemma reachable_all_ones {m : ℤ} (hm : 1 ≤ m) : Reachable m (m - 1).toNat := by
  refine ⟨List.replicate (m - 1).toNat 1, validPath_replicate_one _ _, ?_, ?_⟩
  · rw [List.sum_replicate, smul_eq_mul, mul_one,
      Int.toNat_of_nonneg (by linarith : (0 : ℤ) ≤ m - 1)]
    ring
  · rw [List.length_replicate]

lemma minJumps_mem {m : ℤ} (hm : 1 ≤ m) : minJumps m ∈ { j | Reachable m j } :=
  Nat.sInf_mem ⟨(m - 1).toNat, reachable_all_ones hm⟩

snip end

problem usa2006_p5 (k : ℕ) (hk : 2 ≤ k) (i : ℕ) :
    minJumps ((2 : ℤ) ^ i * (k : ℤ)) > minJumps ((2 : ℤ) ^ i) := by
  have hk2 : (2 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have h2i1 : (1 : ℤ) ≤ (2 : ℤ) ^ i := by
    have h := pow_pos (by norm_num : (0 : ℤ) < 2) i
    linarith
  have h2i0 : (0 : ℤ) < (2 : ℤ) ^ i := by positivity
  have hm1 : (1 : ℤ) ≤ (2 : ℤ) ^ i * (k : ℤ) := by nlinarith [h2i1, hk2]
  obtain ⟨ss, hv, hend, hlen⟩ := minJumps_mem hm1
  have hb : ∀ s ∈ ss, s ≤ 2 ^ (i + ss.sum) := by
    intro s hs
    have h1 : s ≤ ss.sum := List.single_le_sum (fun x _ => Nat.zero_le x) s hs
    have h2 : ss.sum ≤ 2 ^ (i + ss.sum) := by
      calc ss.sum ≤ 2 ^ ss.sum := (Nat.lt_two_pow_self).le
        _ ≤ 2 ^ (i + ss.sum) := Nat.pow_le_pow_right (by norm_num) (by lia)
    lia
  have hdiv : (2 : ℤ) ^ min i (i + ss.sum) ∣ (1 : ℤ) + (ss.sum : ℤ) := by
    rw [Nat.min_eq_left (by lia : i ≤ i + ss.sum), hend]
    exact dvd_mul_right _ _
  have hge : (2 : ℤ) ^ i ≤ (1 : ℤ) + (ss.sum : ℤ) := by
    rw [hend]
    exact le_mul_of_one_le_right (le_of_lt h2i0) (by linarith)
  obtain ⟨ss', hv', hend', hlen', hstrict'⟩ :=
    key_lemma i (i + ss.sum) ss hv (bigBound_of_forall hb) hdiv hge
  have hT : (2 : ℤ) ^ i < (1 : ℤ) + (ss.sum : ℤ) := by
    rw [hend]
    exact lt_mul_of_one_lt_right h2i0 (by linarith)
  have hlt : ss'.length < ss.length := hstrict' hT
  have hle : minJumps ((2 : ℤ) ^ i) ≤ ss'.length := Nat.sInf_le ⟨ss', hv', hend', rfl⟩
  rw [← hlen]
  lia
