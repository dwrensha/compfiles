/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 1992, Problem 5

A complex polynomial has degree 1992 and distinct zeros. Show that we can find
complex numbers zₙ, such that if p₁(z) = z - z₁ and pₙ(z) = pₙ₋₁(z)² - zₙ,
then the polynomial divides p₁₉₉₂(z).
-/

namespace Usa1992P5

open Polynomial

/-- The iterated polynomial sequence of the problem: `pseq [z₁, …, zₙ]` is the
polynomial `pₙ`, where `p₁(z) = z - z₁` and `pₖ(z) = pₖ₋₁(z)² - zₖ`. -/
noncomputable def pseq : List ℂ → ℂ[X]
  | [] => X
  | z :: zs => zs.foldl (fun P w => P ^ 2 - C w) (X - C z)

snip begin

-- Follows the solution at https://prase.cz/kalva/usa/usoln/usol925.html.
-- Starting from the set S of zeros of q, repeatedly replace S by the smaller
-- set {(s - m)² : s ∈ S}, where m is the midpoint of two distinct elements
-- of S; after at most |S| - 1 steps one reaches a set with a single element,
-- and choosing the next z to be that element makes p vanish on all of S.

lemma pseq_concat {zs : List ℂ} (hzs : zs ≠ []) (w : ℂ) :
    pseq (zs ++ [w]) = (pseq zs) ^ 2 - C w := by
  cases zs with
  | nil => exact absurd rfl hzs
  | cons z zs =>
    simp only [List.cons_append, pseq, List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma pseq_foldl_comp (R init : ℂ[X]) (zs : List ℂ) :
    (zs.foldl (fun P w => P ^ 2 - C w) init).comp R =
      zs.foldl (fun P w => P ^ 2 - C w) (init.comp R) := by
  induction zs generalizing init with
  | nil => rfl
  | cons z zs ih =>
    simp only [List.foldl_cons, ih]
    congr 1
    simp [sub_comp, pow_comp, C_comp]

lemma pseq_cons_comp (z w : ℂ) (zs : List ℂ) :
    pseq (z :: w :: zs) = (pseq (w :: zs)).comp ((X - C z) ^ 2) := by
  simp only [pseq, List.foldl_cons]
  rw [pseq_foldl_comp]
  congr 1
  simp [sub_comp, X_comp, C_comp]

lemma pseq_cons_eval (z : ℂ) {zs : List ℂ} (hzs : zs ≠ []) (x : ℂ) :
    (pseq (z :: zs)).eval x = (pseq zs).eval ((x - z) ^ 2) := by
  cases zs with
  | nil => exact absurd rfl hzs
  | cons w zs =>
    rw [pseq_cons_comp, eval_comp]
    simp

/-- The combinatorial heart of the solution: for any nonempty set `S` of at
most `n` complex numbers one can choose `z₁, …, zₙ` so that `pₙ` vanishes on
all of `S`. -/
lemma exists_pseq_eval_eq_zero :
    ∀ n : ℕ, ∀ S : Finset ℂ, S.Nonempty → S.card ≤ n →
      ∃ zs : List ℂ, zs.length = n ∧ ∀ w ∈ S, (pseq zs).eval w = 0 := by
  intro n
  induction n with
  | zero =>
    intro S hne hcard
    exfalso
    have hpos := Finset.card_pos.mpr hne
    lia
  | succ n ih =>
    intro S hne hcard
    rcases lt_or_ge n S.card with hgt | hle
    · have hcard' : S.card = n + 1 := by lia
      by_cases h1 : S.card ≤ 1
      · -- `S = {s}` is a singleton (so `n = 0`); take `z₁ = s`.
        obtain ⟨s, hs⟩ := hne
        have hn0 : n = 0 := by lia
        subst hn0
        refine ⟨[s], rfl, fun w hw => ?_⟩
        have hws : w = s := Finset.card_le_one.mp h1 w hw s hs
        subst hws
        simp [pseq]
      · -- Pick two distinct elements `a, b` of `S` and square around their
        -- midpoint `m`; the image has one element fewer.
        push Not at h1
        obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h1
        set m := (a + b) / 2 with hm
        have hfab : (a - m) ^ 2 = (b - m) ^ 2 := by
          have h : a - m = -(b - m) := by
            rw [hm]
            ring
          rw [h, neg_sq]
        have hb' : b ∈ S.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩
        have himg : S.image (fun s => (s - m) ^ 2) =
            (S.erase a).image (fun s => (s - m) ^ 2) := by
          conv_lhs => rw [← Finset.insert_erase ha]
          rw [Finset.image_insert,
            Finset.insert_eq_of_mem (Finset.mem_image.mpr ⟨b, hb', hfab.symm⟩)]
        have hTcard : (S.image fun s => (s - m) ^ 2).card ≤ n := by
          rw [himg]
          calc ((S.erase a).image fun s => (s - m) ^ 2).card
              ≤ (S.erase a).card := Finset.card_image_le
            _ = S.card - 1 := Finset.card_erase_of_mem ha
            _ = n := by lia
        obtain ⟨zs, hlen, hvan⟩ := ih _ (Finset.Nonempty.image hne _) hTcard
        have hzs : zs ≠ [] := by
          rintro rfl
          simp only [List.length_nil] at hlen
          lia
        refine ⟨m :: zs, by simp [hlen], fun w hw => ?_⟩
        rw [pseq_cons_eval m hzs]
        exact hvan _ (Finset.mem_image.mpr ⟨w, hw, rfl⟩)
    · -- `S` is small enough already; pad with a trailing zero.
      obtain ⟨zs, hlen, hvan⟩ := ih S hne hle
      have hpos := Finset.card_pos.mpr hne
      have hzs : zs ≠ [] := by
        rintro rfl
        simp only [List.length_nil] at hlen
        lia
      refine ⟨zs ++ [0], by simp [hlen], fun w hw => ?_⟩
      rw [pseq_concat hzs]
      simp [hvan w hw]

snip end

problem usa1992_p5 {q : ℂ[X]} (hq : q.natDegree = 1992) (hq' : q.roots.Nodup) :
    ∃ zs : List ℂ, zs.length = 1992 ∧ q ∣ pseq zs := by
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [natDegree_zero] at hq
    norm_num at hq
  have hsplit : q.Splits := IsAlgClosed.splits q
  have hcard : q.roots.card = 1992 := by
    rw [splits_iff_card_roots.mp hsplit, hq]
  have hSne : q.roots.toFinset.Nonempty := by
    rw [← Finset.card_pos, Multiset.toFinset_card_of_nodup hq', hcard]
    norm_num
  obtain ⟨zs, hlen, hvan⟩ :=
    exists_pseq_eval_eq_zero 1992 q.roots.toFinset hSne
      (le_of_eq (by rw [Multiset.toFinset_card_of_nodup hq', hcard]))
  have hprod : (∏ a ∈ q.roots.toFinset, (X - C a : ℂ[X])) ∣ pseq zs := by
    apply Finset.prod_dvd_of_coprime
    · intro a _ b _ hab
      exact isCoprime_X_sub_C_of_isUnit_sub
        (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hab))
    · intro a ha
      exact dvd_iff_isRoot.mpr (hvan a ha)
  have hprod' : (q.roots.map fun a => X - C a).prod ∣ pseq zs := by
    rw [Finset.prod_multiset_map_count]
    convert hprod using 1
    apply Finset.prod_congr rfl
    intro a ha
    have ha' : a ∈ q.roots := by simpa using ha
    rw [Multiset.count_eq_one_of_mem hq' ha', pow_one]
  refine ⟨zs, hlen, ?_⟩
  rw [hsplit.eq_prod_roots]
  exact (IsUnit.mul_left_dvd
    (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hq0)))).mpr
    hprod'

end Usa1992P5
