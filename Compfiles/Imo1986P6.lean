/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Combinatorics]
}

/-!
# International Mathematical Olympiad 1986, Problem 6

Given a finite set of points in the plane, each with integer coordinates,
is it always possible to color the points red or white so that for any
straight line L parallel to one of the coordinate axes the difference
(in absolute value) between the numbers of white and red points on L
is not greater than 1?
-/

namespace Imo1986P6

open Finset

snip begin

/-- A *signing* of a set of points of the plane: `ε p = 1` means that `p` is
colored white and `ε p = -1` means that `p` is colored red.  The difference
between the numbers of white and red points of `S` lying on a line then equals
the sum of `ε` over the points of `S` on that line, so the required property of
the coloring is that the sum of `ε` over every row and every column of `S` has
absolute value at most `1`. -/
def Balanced (S : Finset (ℤ × ℤ)) (ε : ℤ × ℤ → ℤ) : Prop :=
  (∀ p ∈ S, ε p = 1 ∨ ε p = -1) ∧
  (∀ x : ℤ, |∑ p ∈ S.filter (fun p => p.1 = x), ε p| ≤ 1) ∧
  (∀ y : ℤ, |∑ p ∈ S.filter (fun p => p.2 = y), ε p| ≤ 1)

lemma balanced_empty : Balanced ∅ (fun _ => 1) := by
  refine ⟨fun p hp => by simp at hp, fun x => ?_, fun y => ?_⟩ <;>
  · rw [Finset.filter_empty, Finset.sum_empty]
    simp

/-- The problem is symmetric under swapping the two coordinates. -/
lemma balanced_image_swap {S : Finset (ℤ × ℤ)} {ε : ℤ × ℤ → ℤ} (h : Balanced S ε) :
    Balanced (S.image Prod.swap) (ε ∘ Prod.swap) := by
  obtain ⟨hε, hx, hy⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    have := hε q hq
    simpa [Function.comp_apply] using this
  · intro x
    rw [Finset.filter_image, Finset.sum_image (Prod.swap_injective.injOn)]
    have := hy x
    simpa [Function.comp_apply] using this
  · intro y
    rw [Finset.filter_image, Finset.sum_image (Prod.swap_injective.injOn)]
    have := hx y
    simpa [Function.comp_apply] using this

/-- Case A: some point `P` is the only point of `S` in its column.  Then any
balanced signing of `S.erase P` can be extended to a balanced signing of `S`
by choosing the sign of `P` so as to balance the row of `P`. -/
lemma balanced_of_alone_col {S : Finset (ℤ × ℤ)} {P : ℤ × ℤ} (hP : P ∈ S)
    (hcol : ∀ Q ∈ S, Q.1 = P.1 → Q = P)
    {ε' : ℤ × ℤ → ℤ} (hε' : Balanced (S.erase P) ε') :
    ∃ ε, Balanced S ε := by
  obtain ⟨hε'1, hε'2, hε'3⟩ := hε'
  set d := ∑ p ∈ (S.erase P).filter (fun p => p.2 = P.2), ε' p with hd
  have hd_abs : |d| ≤ 1 := hε'3 P.2
  refine ⟨Function.update ε' P (if d = 1 then -1 else 1), ?_, ?_, ?_⟩
  · intro p hp
    by_cases hpp : p = P
    · subst hpp
      rw [Function.update_self]
      split_ifs <;> simp
    · rw [Function.update_of_ne hpp]
      exact hε'1 p (Finset.mem_erase.mpr ⟨hpp, hp⟩)
  · intro x
    by_cases hx : x = P.1
    · subst hx
      have hfilter : S.filter (fun p => p.1 = P.1) = {P} := by
        ext Q
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hQ, hQ1⟩
          exact hcol Q hQ hQ1
        · rintro rfl
          exact ⟨hP, rfl⟩
      rw [hfilter, Finset.sum_singleton, Function.update_self]
      split_ifs <;> simp
    · have hnotmem : P ∉ S.filter (fun p => p.1 = x) := by
        rw [Finset.mem_filter]
        exact fun h => hx h.2.symm
      have hfilter : S.filter (fun p => p.1 = x) = (S.erase P).filter (fun p => p.1 = x) := by
        rw [Finset.filter_erase, Finset.erase_eq_of_notMem hnotmem]
      rw [hfilter]
      convert hε'2 x using 2
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mem_filter] at hp
      exact Function.update_of_ne (Finset.mem_erase.mp hp.1).1 _ _
  · intro y
    by_cases hy : y = P.2
    · subst hy
      have hPmem : P ∈ S.filter (fun p => p.2 = P.2) := by
        rw [Finset.mem_filter]
        exact ⟨hP, rfl⟩
      rw [← Finset.insert_erase hPmem, Finset.sum_insert (Finset.notMem_erase P _),
        Function.update_self]
      have hsum : ∑ p ∈ (S.filter (fun p => p.2 = P.2)).erase P,
            Function.update ε' P (if d = 1 then -1 else 1) p = d := by
        rw [← Finset.filter_erase]
        exact Finset.sum_congr rfl fun p hp => by
          rw [Finset.mem_filter] at hp
          exact Function.update_of_ne (Finset.mem_erase.mp hp.1).1 _ _
      rw [hsum, add_comm]
      rw [abs_le] at hd_abs ⊢
      obtain ⟨hd1, hd2⟩ := hd_abs
      split_ifs with h <;> constructor <;> omega
    · have hnotmem : P ∉ S.filter (fun p => p.2 = y) := by
        rw [Finset.mem_filter]
        exact fun h => hy h.2.symm
      have hfilter : S.filter (fun p => p.2 = y) = (S.erase P).filter (fun p => p.2 = y) := by
        rw [Finset.filter_erase, Finset.erase_eq_of_notMem hnotmem]
      rw [hfilter]
      convert hε'3 y using 2
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mem_filter] at hp
      exact Function.update_of_ne (Finset.mem_erase.mp hp.1).1 _ _

/-- Case A, symmetric version: some point `P` is the only point of `S` in its
row.  Handled by swapping the coordinates and applying `balanced_of_alone_col`. -/
lemma balanced_of_alone_row {S : Finset (ℤ × ℤ)} {P : ℤ × ℤ} (hP : P ∈ S)
    (hrow : ∀ Q ∈ S, Q.2 = P.2 → Q = P)
    (n : ℕ) (IH : ∀ T : Finset (ℤ × ℤ), T.card ≤ n → ∃ ε, Balanced T ε)
    (hcard : S.card ≤ n + 1) :
    ∃ ε, Balanced S ε := by
  have hP' : Prod.swap P ∈ S.image Prod.swap := Finset.mem_image.mpr ⟨P, hP, rfl⟩
  have hcol' : ∀ Q ∈ S.image Prod.swap, Q.1 = (Prod.swap P).1 → Q = Prod.swap P := by
    intro Q hQ hQ1
    rw [Finset.mem_image] at hQ
    obtain ⟨R, hR, rfl⟩ := hQ
    have h2 : R.2 = P.2 := hQ1
    rw [hrow R hR h2]
  have herase : ((S.image Prod.swap).erase (Prod.swap P)).card ≤ n := by
    rw [Finset.card_erase_of_mem hP', Finset.card_image_of_injective S Prod.swap_injective]
    omega
  obtain ⟨ε', hε'⟩ := IH _ herase
  obtain ⟨ε₃, hε₃⟩ := balanced_of_alone_col hP' hcol' hε'
  have him : (S.image Prod.swap).image Prod.swap = S := by
    ext p
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨q, ⟨r, hr, rfl⟩, hqp⟩
      rw [← hqp, Prod.swap_swap]
      exact hr
    · intro hp
      exact ⟨Prod.swap p, ⟨p, hp, rfl⟩, Prod.swap_swap p⟩
  have h := balanced_image_swap hε₃
  rw [him] at h
  exact ⟨ε₃ ∘ Prod.swap, h⟩

/-- An *alternating path* in `S`: a list of at least two distinct points of `S`
such that the step from position `i` to position `i + 1` is horizontal (the two
points agree on their second coordinate) when `i` is even and vertical (the two
points agree on their first coordinate) when `i` is odd. -/
structure AltPath (S : Finset (ℤ × ℤ)) (L : List (ℤ × ℤ)) : Prop where
  nodup : L.Nodup
  mem : ∀ p ∈ L, p ∈ S
  len : 2 ≤ L.length
  step : ∀ i : ℕ, (h : i + 1 < L.length) →
    (Even i → (L[i]'(by omega)).2 = (L[i + 1]'h).2) ∧
    (Odd i → (L[i]'(by omega)).1 = (L[i + 1]'h).1)

/-- An alternating path can be extended by appending a fresh point, provided the
new last step has the required direction. -/
lemma AltPath.snoc {S : Finset (ℤ × ℤ)} {L : List (ℤ × ℤ)} (hL : AltPath S L)
    {Q : ℤ × ℤ} (hQ : Q ∈ S) (hQn : Q ∉ L)
    (hlast : (Even (L.length - 1) → ∀ h : L.length - 1 < L.length, (L[L.length - 1]'h).2 = Q.2) ∧
             (Odd (L.length - 1) → ∀ h : L.length - 1 < L.length, (L[L.length - 1]'h).1 = Q.1)) :
    AltPath S (L ++ [Q]) where
  nodup := by
    rw [List.nodup_append]
    refine ⟨hL.nodup, List.nodup_singleton Q, fun a ha b hb => ?_⟩
    rw [List.mem_singleton] at hb
    rintro rfl
    exact hQn (hb ▸ ha)
  mem := by
    intro p hp
    rw [List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact hL.mem p hp
    · exact hQ
  len := by
    have h2 := hL.len
    rw [List.length_append, List.length_singleton]
    omega
  step := by
    intro i h
    rw [List.length_append, List.length_singleton] at h
    by_cases hi : i + 1 < L.length
    · rw [List.getElem_append_left (show i < L.length by omega),
        List.getElem_append_left hi]
      exact hL.step i hi
    · have hi2 : i = L.length - 1 := by omega
      subst hi2
      have hlen := hL.len
      rw [List.getElem_append_left (show L.length - 1 < L.length by omega)]
      have h2 : ∀ hh : L.length - 1 + 1 < (L ++ [Q]).length,
          (L ++ [Q])[L.length - 1 + 1]'hh = Q := by
        intro hh
        rw [List.getElem_append_right (show L.length ≤ L.length - 1 + 1 by omega)]
        have e0 : L.length - 1 + 1 - L.length = 0 := by omega
        simp only [e0]
        rfl
      rw [h2]
      constructor
      · intro hev
        exact hlast.1 hev _
      · intro hodd
        exact hlast.2 hodd _

/-- The step condition of an alternating path, with the second index given
separately (useful when it is not literally `i + 1`). -/
lemma AltPath.step_at {S : Finset (ℤ × ℤ)} {L : List (ℤ × ℤ)} (hL : AltPath S L)
    (i j : ℕ) (hij : j = i + 1) (h : i + 1 < L.length) :
    (Even i → (L[i]'(by omega)).2 = (L[j]'(by omega)).2) ∧
    (Odd i → (L[i]'(by omega)).1 = (L[j]'(by omega)).1) := by
  subst hij
  exact hL.step i h

/-- The step condition of an alternating path is inherited by a tail of the
path, provided the tail starts at an even index. -/
lemma AltPath.drop_step {S : Finset (ℤ × ℤ)} {L : List (ℤ × ℤ)} (hL : AltPath S L)
    {j : ℕ} (hj : Even j) :
    ∀ t : ℕ, (h : t + 1 < (L.drop j).length) →
      (Even t → ((L.drop j)[t]'(by omega)).2 = ((L.drop j)[t + 1]'h).2) ∧
      (Odd t → ((L.drop j)[t]'(by omega)).1 = ((L.drop j)[t + 1]'h).1) := by
  intro t ht
  rw [List.getElem_drop, List.getElem_drop]
  have h1 := hL.step (j + t) (by rw [List.length_drop] at ht; omega)
  constructor
  · intro hev
    exact h1.1 (hj.add hev)
  · intro hodd
    exact h1.2 (hj.add_odd hodd)

/-- Among the alternating paths in `S` there is one of maximal length. -/
lemma AltPath.exists_max {S : Finset (ℤ × ℤ)} (hbase : ∃ L₀, AltPath S L₀) :
    ∃ L, AltPath S L ∧ ∀ L', AltPath S L' → L'.length ≤ L.length := by
  classical
  have hb : ∀ L : List (ℤ × ℤ), AltPath S L → L.length ≤ S.card := by
    intro L hL
    rw [← List.toFinset_card_of_nodup hL.nodup]
    apply Finset.card_le_card
    intro x hx
    rw [List.mem_toFinset] at hx
    exact hL.mem x hx
  let P : ℕ → Prop := fun n => ∃ L : List (ℤ × ℤ), AltPath S L ∧ L.length = n
  obtain ⟨L₀, hL₀⟩ := hbase
  have hP : P L₀.length := ⟨L₀, hL₀, rfl⟩
  have hspec := Nat.findGreatest_spec (hb L₀ hL₀) hP
  obtain ⟨L, hL, hlen⟩ := hspec
  refine ⟨L, hL, fun L' hL' => ?_⟩
  have hP' : P L'.length := ⟨L', hL', rfl⟩
  have hle := Nat.le_findGreatest (hb L' hL') hP'
  omega

/-- Helper: two elements of the same list at equal indices are equal. -/
lemma getElem_congr {α : Type*} (l : List α) {i j : ℕ} (hi : i < l.length) (hj : j < l.length)
    (h : i = j) : l[i]'hi = l[j]'hj :=
  congrArg l.get (Fin.ext h)

/-- If a list of points with no repetitions has even length and a sign function
alternates on each pair of consecutive elements while a "coordinate" function
is constant on each pair, then the sum of the signs over the points of the list
lying on any fixed level of the coordinate is zero.  This is the computation
showing that a correctly colored cycle contributes equally many white and red
points to every row and every column. -/
lemma pair_sum_zero : ∀ (C : List (ℤ × ℤ)) (f g : ℤ × ℤ → ℤ),
    C.Nodup → Even C.length →
    (∀ t : ℕ, 2 * t + 1 < C.length →
      f (C.getD (2 * t) (0, 0)) + f (C.getD (2 * t + 1) (0, 0)) = 0 ∧
      g (C.getD (2 * t) (0, 0)) = g (C.getD (2 * t + 1) (0, 0))) →
    ∀ c : ℤ, ∑ p ∈ C.toFinset.filter (fun p => g p = c), f p = 0 := by
  have aux : ∀ n : ℕ, ∀ (C : List (ℤ × ℤ)) (f g : ℤ × ℤ → ℤ),
      C.length ≤ n → C.Nodup → Even C.length →
      (∀ t : ℕ, 2 * t + 1 < C.length →
        f (C.getD (2 * t) (0, 0)) + f (C.getD (2 * t + 1) (0, 0)) = 0 ∧
        g (C.getD (2 * t) (0, 0)) = g (C.getD (2 * t + 1) (0, 0))) →
      ∀ c : ℤ, ∑ p ∈ C.toFinset.filter (fun p => g p = c), f p = 0 := by
    intro n
    induction n with
    | zero =>
      intro C f g hlen hnodup heven hcond c
      have hC : C = [] := by
        cases C with
        | nil => rfl
        | cons a t => simp at hlen
      subst hC
      simp
    | succ n IH =>
      intro C f g hlen hnodup heven hcond c
      cases C with
      | nil => simp
      | cons a t =>
        cases t with
        | nil =>
          simp only [List.length_singleton] at heven
          exact absurd heven (by decide)
        | cons b rest =>
          have hfa : f a + f b = 0 :=
            (hcond 0 (by simp only [List.length_cons]; omega)).1
          have hga : g a = g b :=
            (hcond 0 (by simp only [List.length_cons]; omega)).2
          have hrest : ∀ t : ℕ, 2 * t + 1 < rest.length →
              f (rest.getD (2 * t) (0, 0)) + f (rest.getD (2 * t + 1) (0, 0)) = 0 ∧
              g (rest.getD (2 * t) (0, 0)) = g (rest.getD (2 * t + 1) (0, 0)) := by
            intro t ht
            exact hcond (t + 1) (by simp only [List.length_cons]; omega)
          have h1 : a ∉ b :: rest := (List.nodup_cons.mp hnodup).1
          have h2 : rest.Nodup :=
            (List.nodup_cons.mp (List.nodup_cons.mp hnodup).2).2
          have h3 : b ∉ rest := (List.nodup_cons.mp (List.nodup_cons.mp hnodup).2).1
          rw [List.mem_cons, not_or] at h1
          obtain ⟨hane_b, harest⟩ := h1
          obtain ⟨k, hk⟩ := heven
          have hrest_even : Even rest.length := by
            refine ⟨k - 1, by simp only [List.length_cons] at hk; omega⟩
          have hrest_len : rest.length ≤ n := by
            simp only [List.length_cons] at hlen
            omega
          have IHres := IH rest f g hrest_len h2 hrest_even hrest c
          rw [List.toFinset_cons, List.toFinset_cons, Finset.filter_insert]
          by_cases hca : g a = c
          · rw [if_pos hca]
            have hcb : g b = c := hga ▸ hca
            rw [Finset.filter_insert, if_pos hcb]
            have hanot : a ∉ insert b (rest.toFinset.filter fun p => g p = c) := by
              rw [Finset.mem_insert, Finset.mem_filter, List.mem_toFinset]
              rintro (rfl | ⟨hr, -⟩)
              · exact hane_b rfl
              · exact harest hr
            have hbnot : b ∉ rest.toFinset.filter fun p => g p = c := by
              rw [Finset.mem_filter, List.mem_toFinset]
              exact fun hr => h3 hr.1
            rw [Finset.sum_insert hanot, Finset.sum_insert hbnot, IHres]
            omega
          · rw [if_neg hca]
            have hcb : g b ≠ c := hga ▸ hca
            rw [Finset.filter_insert, if_neg hcb]
            exact IHres
  intro C f g hnodup heven hcond c
  exact aux C.length C f g le_rfl hnodup heven hcond c

/- The sign function attached to an even-length cycle: `+1` at even positions,
`-1` at odd positions. -/
noncomputable def cycSign (C : List (ℤ × ℤ)) : ℤ × ℤ → ℤ :=
  fun p => if ∃ i : Fin C.length, C.get i = p ∧ Even i.val then 1 else -1

lemma cycSign_apply (C : List (ℤ × ℤ)) (hn : C.Nodup) (i : Fin C.length) :
    cycSign C (C.get i) = if Even i.val then (1 : ℤ) else -1 := by
  unfold cycSign
  by_cases h : Even i.val
  · rw [if_pos h, if_pos ⟨i, rfl, h⟩]
  · rw [if_neg h, if_neg (fun ⟨j, hji, hj⟩ => h (hn.get_inj_iff.mp hji ▸ hj))]

lemma cycSign_apply' (C : List (ℤ × ℤ)) (hn : C.Nodup) (i : ℕ) (h : i < C.length) :
    cycSign C (C[i]'h) = if Even i then (1 : ℤ) else -1 :=
  (congrArg (cycSign C) (List.get_eq_getElem (l := C) (i := ⟨i, h⟩)).symm).trans
    (cycSign_apply C hn ⟨i, h⟩)

/-- A cycle of even length, alternating horizontal and vertical steps and closed
by a vertical step, admits a signing that is balanced on every row and column. -/
lemma cycle_balanced (C : List (ℤ × ℤ)) (hnodup : C.Nodup) (hlen : Even C.length)
    (hstep : ∀ i : ℕ, (h : i + 1 < C.length) →
      (Even i → (C[i]'(by omega)).2 = (C[i + 1]'h).2) ∧
      (Odd i → (C[i]'(by omega)).1 = (C[i + 1]'h).1))
    (hclose : ∀ h : 0 < C.length, (C[C.length - 1]'(by omega)).1 = (C[0]'h).1) :
    ∃ ε : ℤ × ℤ → ℤ, (∀ p ∈ C.toFinset, ε p = 1 ∨ ε p = -1) ∧
      (∀ y : ℤ, ∑ p ∈ C.toFinset.filter (fun p => p.2 = y), ε p = 0) ∧
      (∀ x : ℤ, ∑ p ∈ C.toFinset.filter (fun p => p.1 = x), ε p = 0) := by
  refine ⟨cycSign C, ?_, ?_, ?_⟩
  · intro p hp
    unfold cycSign
    split_ifs <;> simp
  · intro y
    apply pair_sum_zero C (cycSign C) Prod.snd hnodup hlen _ y
    intro t ht
    have e0 : C.getD (2 * t) (0, 0) = C[2 * t]'(by omega) :=
      (List.getElem_eq_getD (0, 0)).symm
    have e0' : C.getD (2 * t + 1) (0, 0) = C[2 * t + 1]'ht :=
      (List.getElem_eq_getD (0, 0)).symm
    rw [e0, e0']
    constructor
    · rw [cycSign_apply' C hnodup (2 * t) (by omega),
        cycSign_apply' C hnodup (2 * t + 1) ht,
        if_pos ⟨t, by omega⟩,
        if_neg (Nat.not_even_iff_odd.mpr ⟨t, rfl⟩)]
      norm_num
    · exact (hstep (2 * t) ht).1 ⟨t, by omega⟩
  · intro x
    have hClen : (C.drop 1 ++ C.take 1).length = C.length := by
      rw [List.length_append, List.length_drop, List.length_take]
      by_cases h0 : C.length = 0
      · simp [h0]
      · rw [Nat.min_eq_left (by omega : 1 ≤ C.length)]
        omega
    have hnodup' : (C.drop 1 ++ C.take 1).Nodup := by
      rw [List.nodup_append]
      refine ⟨(List.drop_sublist 1 C).nodup hnodup, (List.take_sublist 1 C).nodup hnodup, ?_⟩
      intro a ha b hb hab
      have hdis := List.disjoint_take_drop hnodup (show (1 : ℕ) ≤ 1 from le_refl 1)
      exact hdis hb (hab ▸ ha)
    have hlen' : Even (C.drop 1 ++ C.take 1).length := hClen ▸ hlen
    have htF : (C.drop 1 ++ C.take 1).toFinset = C.toFinset := by
      rw [List.toFinset_append, Finset.union_comm]
      conv_rhs => rw [← List.take_append_drop 1 C, List.toFinset_append]
    rw [← htF]
    apply pair_sum_zero (C.drop 1 ++ C.take 1) (cycSign C) Prod.fst hnodup' hlen' _ x
    intro t ht
    rw [hClen] at ht
    have e0 : (C.drop 1 ++ C.take 1).getD (2 * t) (0, 0) =
        (C.drop 1 ++ C.take 1)[2 * t]'(by omega) :=
      (List.getElem_eq_getD (0, 0)).symm
    have e0' : (C.drop 1 ++ C.take 1).getD (2 * t + 1) (0, 0) =
        (C.drop 1 ++ C.take 1)[2 * t + 1]'(by omega) :=
      (List.getElem_eq_getD (0, 0)).symm
    rw [e0, e0']
    by_cases hcase : 2 * t + 1 < C.length - 1
    · have e1 : (C.drop 1 ++ C.take 1)[2 * t]'(by omega) = C[2 * t + 1]'(by omega) := by
        rw [List.getElem_append_left (show 2 * t < (C.drop 1).length by
          rw [List.length_drop]; omega), List.getElem_drop]
        exact getElem_congr C _ _ (by omega)
      have e2 : (C.drop 1 ++ C.take 1)[2 * t + 1]'(by omega) = C[2 * t + 2]'(by omega) := by
        rw [List.getElem_append_left (show 2 * t + 1 < (C.drop 1).length by
          rw [List.length_drop]; omega), List.getElem_drop]
        exact getElem_congr C _ _ (by omega)
      rw [e1, e2]
      constructor
      · rw [cycSign_apply' C hnodup (2 * t + 1) (by omega),
          cycSign_apply' C hnodup (2 * t + 2) (by omega),
          if_neg (Nat.not_even_iff_odd.mpr ⟨t, rfl⟩), if_pos ⟨t + 1, by omega⟩]
        norm_num
      · exact (hstep (2 * t + 1) (by omega)).2 ⟨t, rfl⟩
    · have hb : 2 * t + 1 = C.length - 1 := by omega
      have hCpos : 0 < C.length := by omega
      have hC2 : C.length = 2 * t + 2 := by omega
      have e1 : (C.drop 1 ++ C.take 1)[2 * t]'(by omega) = C[C.length - 1]'(by omega) := by
        rw [List.getElem_append_left (show 2 * t < (C.drop 1).length by
          rw [List.length_drop]; omega), List.getElem_drop]
        exact getElem_congr C _ _ (by omega)
      have e2 : (C.drop 1 ++ C.take 1)[2 * t + 1]'(by omega) = C[0]'(by omega) := by
        rw [List.getElem_append_right (show (C.drop 1).length ≤ 2 * t + 1 by
          rw [List.length_drop]; omega), List.getElem_take]
        exact getElem_congr C _ _ (by rw [List.length_drop]; omega)
      rw [e1, e2]
      constructor
      · have hodd : Odd (C.length - 1) := by
          rcases hlen with ⟨k, hk⟩
          exact ⟨k - 1, by omega⟩
        rw [cycSign_apply' C hnodup (C.length - 1) (by omega),
          cycSign_apply' C hnodup 0 hCpos,
          if_neg (Nat.not_even_iff_odd.mpr hodd), if_pos ⟨0, rfl⟩]
        norm_num
      · exact hclose hCpos

/-- Case B: every point of the nonempty set `S` has another point of `S` in its
row and another one in its column.  Then `S` contains an alternating cycle of
even length at least four, closed by a vertical step. -/
lemma exists_cycle (S : Finset (ℤ × ℤ)) (hne : S.Nonempty)
    (hrow : ∀ P ∈ S, ∃ Q ∈ S, Q ≠ P ∧ Q.2 = P.2)
    (hcol : ∀ P ∈ S, ∃ Q ∈ S, Q ≠ P ∧ Q.1 = P.1) :
    ∃ C : List (ℤ × ℤ), C.Nodup ∧ (∀ p ∈ C, p ∈ S) ∧ 4 ≤ C.length ∧ Even C.length ∧
      (∀ i : ℕ, (h : i + 1 < C.length) →
        (Even i → (C[i]'(by omega)).2 = (C[i + 1]'h).2) ∧
        (Odd i → (C[i]'(by omega)).1 = (C[i + 1]'h).1)) ∧
      (∀ h : 0 < C.length, (C[C.length - 1]'(by omega)).1 = (C[0]'h).1) := by
  obtain ⟨P₀, hP₀⟩ := hne
  obtain ⟨P₁, hP₁, hP₁ne, hP₁row⟩ := hrow P₀ hP₀
  have hbase : AltPath S [P₀, P₁] := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [List.nodup_cons]
      exact ⟨fun h => hP₁ne (List.mem_singleton.mp h).symm, List.nodup_singleton _⟩
    · intro p hp
      rw [List.mem_cons, List.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact hP₀
      · exact hP₁
    · simp
    · intro i h
      have hi : i = 0 := by
        simp only [List.length_cons, List.length_nil] at h
        omega
      subst hi
      constructor
      · intro _
        exact hP₁row.symm
      · intro hodd
        exact absurd hodd (by decide)
  obtain ⟨L, hL, hLmax⟩ := AltPath.exists_max ⟨[P₀, P₁], hbase⟩
  set k := L.length - 1 with hk
  have hLlen : 2 ≤ L.length := hL.len
  have hkn : k < L.length := by omega
  by_cases hke : Even k
  swap
  · -- CASE `k` ODD: the last step of `L` is a row step.
    have hko : Odd k := Nat.not_even_iff_odd.mp hke
    obtain ⟨Q, hQS, hQne, hQ1⟩ := hcol (L[k]'hkn) (hL.mem _ (List.getElem_mem hkn))
    by_cases hQin : Q ∈ L
    · -- The column of the last point meets the path again: close a cycle.
      rw [List.mem_iff_get] at hQin
      obtain ⟨⟨i, hi⟩, hQi⟩ := hQin
      have hQi' : L[i]'hi = Q :=
        (List.get_eq_getElem (l := L) (i := ⟨i, hi⟩)).symm.trans hQi
      have hik : i ≠ k := by
        rintro rfl
        exact hQne (by rw [← hQi'])
      have hik2 : i < k := by omega
      by_cases hie : Even i
      · -- sub-case: `i` even; the cycle is `L.drop i`
        refine ⟨L.drop i, (List.drop_sublist i L).nodup hL.nodup, ?_, ?_, ?_, ?_, ?_⟩
        · intro p hp
          exact hL.mem p ((List.drop_sublist i L).subset hp)
        · rw [List.length_drop]
          obtain ⟨a, ha⟩ := hko
          obtain ⟨b, hb⟩ := hie
          by_contra hlt
          have hik1 : i = k - 1 := by omega
          subst hik1
          have h1 : (L[k - 1]'(by omega)).1 = (L[k]'hkn).1 := by
            rw [hQi']
            exact hQ1
          have h2 : (L[k - 1]'(by omega)).2 = (L[k]'hkn).2 :=
            (hL.step_at (k - 1) k (by omega) (by omega)).1 ⟨a, by omega⟩
          have heq : (L[k - 1]'(by omega)) = (L[k]'hkn) := Prod.ext_iff.mpr ⟨h1, h2⟩
          have := hL.nodup.getElem_inj_iff.mp heq
          omega
        · rw [List.length_drop]
          obtain ⟨a, ha⟩ := hko
          obtain ⟨b, hb⟩ := hie
          exact ⟨a + 1 - b, by omega⟩
        · exact hL.drop_step hie
        · intro h0
          have e1 : (L.drop i)[(L.drop i).length - 1]'(by omega) = L[k]'hkn := by
            rw [List.getElem_drop]
            exact getElem_congr L _ _ (by rw [List.length_drop] at *; omega)
          have e2 : (L.drop i)[0]'(by omega) = L[i]'hi := by
            rw [List.getElem_drop]
            exact getElem_congr L _ _ (by omega)
          rw [e1, e2, hQi']
          exact hQ1.symm
      · -- sub-case: `i` odd; the cycle is `L.drop (i + 1)`
        have hio : Odd i := Nat.not_even_iff_odd.mp hie
        have hie2 : Even (i + 1) := hio.add_odd ⟨0, rfl⟩
        refine ⟨L.drop (i + 1), (List.drop_sublist (i + 1) L).nodup hL.nodup, ?_, ?_, ?_, ?_, ?_⟩
        · intro p hp
          exact hL.mem p ((List.drop_sublist (i + 1) L).subset hp)
        · rw [List.length_drop]
          obtain ⟨a, ha⟩ := hko
          obtain ⟨b, hb⟩ := hio
          by_contra hlt
          have hik1 : i = k - 2 := by omega
          subst hik1
          have h2 : (L[k - 1]'(by omega)).2 = (L[k]'hkn).2 :=
            (hL.step_at (k - 1) k (by omega) (by omega)).1 ⟨a, by omega⟩
          have h1 : (L[k - 1]'(by omega)).1 = (L[k]'hkn).1 := by
            have hs : (L[k - 2]'(by omega)).1 = (L[k - 1]'(by omega)).1 :=
              (hL.step_at (k - 2) (k - 1) (by omega) (by omega)).2 ⟨a - 1, by omega⟩
            rw [← hs, hQi']
            exact hQ1
          have heq : (L[k - 1]'(by omega)) = (L[k]'hkn) := Prod.ext_iff.mpr ⟨h1, h2⟩
          have := hL.nodup.getElem_inj_iff.mp heq
          omega
        · rw [List.length_drop]
          obtain ⟨a, ha⟩ := hko
          obtain ⟨b, hb⟩ := hio
          exact ⟨a - b, by omega⟩
        · exact hL.drop_step hie2
        · intro h0
          have e1 : (L.drop (i + 1))[(L.drop (i + 1)).length - 1]'(by omega) = L[k]'hkn := by
            rw [List.getElem_drop]
            exact getElem_congr L _ _ (by rw [List.length_drop] at *; omega)
          have e2 : (L.drop (i + 1))[0]'(by omega) = L[i + 1]'(by omega) := by
            rw [List.getElem_drop]
          rw [e1, e2]
          have hs : (L[i]'hi).1 = (L[i + 1]'(by omega)).1 := (hL.step i (by omega)).2 hio
          rw [← hs, hQi']
          exact hQ1.symm
    · -- The column of the last point contains a fresh point: extend the path,
      -- contradicting maximality.
      have hlast : (Even (L.length - 1) → ∀ h : L.length - 1 < L.length,
            (L[L.length - 1]'h).2 = Q.2) ∧
          (Odd (L.length - 1) → ∀ h : L.length - 1 < L.length,
            (L[L.length - 1]'h).1 = Q.1) :=
        ⟨fun hev => absurd hev (Nat.not_even_iff_odd.mpr hko), fun _ _ => hQ1.symm⟩
      have hsnoc := hL.snoc hQS hQin hlast
      have := hLmax (L ++ [Q]) hsnoc
      rw [List.length_append, List.length_singleton] at this
      omega
  · -- CASE `k` EVEN: the last step of `L` is a column step.
    obtain ⟨Q, hQS, hQne, hQ2⟩ := hrow (L[k]'hkn) (hL.mem _ (List.getElem_mem hkn))
    by_cases hQin : Q ∈ L
    · -- The row of the last point meets the path again: close a cycle.
      rw [List.mem_iff_get] at hQin
      obtain ⟨⟨i, hi⟩, hQi⟩ := hQin
      have hQi' : L[i]'hi = Q :=
        (List.get_eq_getElem (l := L) (i := ⟨i, hi⟩)).symm.trans hQi
      have hik : i ≠ k := by
        rintro rfl
        exact hQne (by rw [← hQi'])
      have hik2 : i < k := by omega
      by_cases hie : Even i
      · -- sub-case: `i` even; the cycle is `(L.drop (i + 2)) ++ [L[i + 1]]`
        have hi1 : i + 1 < L.length := by omega
        have hnotin : L[i + 1]'hi1 ∉ L.drop (i + 2) := by
          intro hin
          rw [List.mem_iff_get] at hin
          obtain ⟨⟨j, hj⟩, hje⟩ := hin
          rw [List.get_eq_getElem, List.getElem_drop] at hje
          have := hL.nodup.getElem_inj_iff.mp hje
          omega
        refine ⟨(L.drop (i + 2)) ++ [L[i + 1]'hi1], ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [List.nodup_append]
          refine ⟨(List.drop_sublist (i + 2) L).nodup hL.nodup, List.nodup_singleton _,
            fun a ha b hb hab => ?_⟩
          rw [List.mem_singleton] at hb
          exact hnotin (hb ▸ hab ▸ ha)
        · intro p hp
          rw [List.mem_append, List.mem_singleton] at hp
          rcases hp with hp | rfl
          · exact hL.mem p ((List.drop_sublist (i + 2) L).subset hp)
          · exact hL.mem _ (List.getElem_mem hi1)
        · rw [List.length_append, List.length_drop, List.length_singleton]
          obtain ⟨a, ha⟩ := hke
          obtain ⟨b, hb⟩ := hie
          by_contra hlt
          have hik1 : i = k - 2 := by omega
          subst hik1
          have h1 : (L[k - 1]'(by omega)).1 = (L[k]'hkn).1 :=
            (hL.step_at (k - 1) k (by omega) (by omega)).2 ⟨a - 1, by omega⟩
          have h2 : (L[k - 1]'(by omega)).2 = (L[k]'hkn).2 := by
            have hs : (L[k - 2]'(by omega)).2 = (L[k - 1]'(by omega)).2 :=
              (hL.step_at (k - 2) (k - 1) (by omega) (by omega)).1 ⟨a - 1, by omega⟩
            rw [← hs, hQi']
            exact hQ2
          have heq : (L[k - 1]'(by omega)) = (L[k]'hkn) := Prod.ext_iff.mpr ⟨h1, h2⟩
          have := hL.nodup.getElem_inj_iff.mp heq
          omega
        · rw [List.length_append, List.length_drop, List.length_singleton]
          obtain ⟨a, ha⟩ := hke
          obtain ⟨b, hb⟩ := hie
          exact ⟨a - b, by omega⟩
        · intro t ht
          rw [List.length_append, List.length_drop, List.length_singleton] at ht
          by_cases hin : t + 1 < L.length - (i + 2)
          · rw [List.getElem_append_left (show t < (L.drop (i + 2)).length by
              rw [List.length_drop]; omega),
              List.getElem_append_left (show t + 1 < (L.drop (i + 2)).length by
              rw [List.length_drop]; omega)]
            have hie2 : Even (i + 2) := hie.add ⟨1, rfl⟩
            rw [List.getElem_drop, List.getElem_drop]
            have h1 := hL.step (i + 2 + t) (by omega)
            constructor
            · intro hev
              exact h1.1 (hie2.add hev)
            · intro hodd
              exact h1.2 (hie2.add_odd hodd)
          · have ht2 : t = k - i - 2 := by omega
            have e1 : ((L.drop (i + 2)) ++ [L[i + 1]'hi1])[t]'(by omega) = L[k]'hkn := by
              rw [List.getElem_append_left (show t < (L.drop (i + 2)).length by
                rw [List.length_drop]; omega), List.getElem_drop]
              exact getElem_congr L _ _ (by omega)
            have e2 : ((L.drop (i + 2)) ++ [L[i + 1]'hi1])[t + 1]'(by omega) =
                L[i + 1]'hi1 := by
              rw [List.getElem_append_right (show (L.drop (i + 2)).length ≤ t + 1 by
                rw [List.length_drop]; omega)]
              exact List.getElem_singleton (by rw [List.length_drop]; omega)
            rw [e1, e2]
            constructor
            · intro hev
              have hs : (L[i]'hi).2 = (L[i + 1]'hi1).2 := (hL.step i (by omega)).1 hie
              rw [← hs, hQi']
              exact hQ2.symm
            · intro hodd
              obtain ⟨a, ha⟩ := hke
              obtain ⟨b, hb⟩ := hie
              obtain ⟨c, hc⟩ := hodd
              omega
        · intro h0
          obtain ⟨a, ha⟩ := hke
          obtain ⟨b, hb⟩ := hie
          have e1 : ((L.drop (i + 2)) ++ [L[i + 1]'hi1])[
              ((L.drop (i + 2)) ++ [L[i + 1]'hi1]).length - 1]'(by omega) = L[i + 1]'hi1 := by
            rw [List.getElem_append_right (show (L.drop (i + 2)).length ≤ _ by
              rw [List.length_append, List.length_drop, List.length_singleton]; omega)]
            exact List.getElem_singleton (by
              rw [List.length_append, List.length_drop, List.length_singleton]; omega)
          have e2 : ((L.drop (i + 2)) ++ [L[i + 1]'hi1])[0]'(by omega) =
              L[i + 2]'(by omega) := by
            rw [List.getElem_append_left (show 0 < (L.drop (i + 2)).length by
              rw [List.length_drop]; omega), List.getElem_drop]
          rw [e1, e2]
          exact (hL.step (i + 1) (by omega)).2 ⟨b, by omega⟩
      · -- sub-case: `i` odd; the cycle is `(L.drop (i + 1)) ++ [L[i]]`
        have hio : Odd i := Nat.not_even_iff_odd.mp hie
        have hnotin : L[i]'hi ∉ L.drop (i + 1) := by
          intro hin
          rw [List.mem_iff_get] at hin
          obtain ⟨⟨j, hj⟩, hje⟩ := hin
          rw [List.get_eq_getElem, List.getElem_drop] at hje
          have := hL.nodup.getElem_inj_iff.mp hje
          omega
        refine ⟨(L.drop (i + 1)) ++ [L[i]'hi], ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [List.nodup_append]
          refine ⟨(List.drop_sublist (i + 1) L).nodup hL.nodup, List.nodup_singleton _,
            fun a ha b hb hab => ?_⟩
          rw [List.mem_singleton] at hb
          exact hnotin (hb ▸ hab ▸ ha)
        · intro p hp
          rw [List.mem_append, List.mem_singleton] at hp
          rcases hp with hp | rfl
          · exact hL.mem p ((List.drop_sublist (i + 1) L).subset hp)
          · exact hL.mem _ (List.getElem_mem hi)
        · rw [List.length_append, List.length_drop, List.length_singleton]
          obtain ⟨a, ha⟩ := hke
          obtain ⟨b, hb⟩ := hio
          by_contra hlt
          have hik1 : i = k - 1 := by omega
          subst hik1
          have h1 : (L[k - 1]'(by omega)).1 = (L[k]'hkn).1 :=
            (hL.step_at (k - 1) k (by omega) (by omega)).2 ⟨a - 1, by omega⟩
          have h2 : (L[k - 1]'(by omega)).2 = (L[k]'hkn).2 := by
            rw [hQi']
            exact hQ2
          have heq : (L[k - 1]'(by omega)) = (L[k]'hkn) := Prod.ext_iff.mpr ⟨h1, h2⟩
          have := hL.nodup.getElem_inj_iff.mp heq
          omega
        · rw [List.length_append, List.length_drop, List.length_singleton]
          obtain ⟨a, ha⟩ := hke
          obtain ⟨b, hb⟩ := hio
          exact ⟨a - b, by omega⟩
        · intro t ht
          rw [List.length_append, List.length_drop, List.length_singleton] at ht
          by_cases hin : t + 1 < L.length - (i + 1)
          · rw [List.getElem_append_left (show t < (L.drop (i + 1)).length by
              rw [List.length_drop]; omega),
              List.getElem_append_left (show t + 1 < (L.drop (i + 1)).length by
              rw [List.length_drop]; omega)]
            have hie2 : Even (i + 1) := hio.add_odd ⟨0, rfl⟩
            rw [List.getElem_drop, List.getElem_drop]
            have h1 := hL.step (i + 1 + t) (by omega)
            constructor
            · intro hev
              exact h1.1 (hie2.add hev)
            · intro hodd
              exact h1.2 (hie2.add_odd hodd)
          · have ht2 : t = k - i - 1 := by omega
            have e1 : ((L.drop (i + 1)) ++ [L[i]'hi])[t]'(by omega) = L[k]'hkn := by
              rw [List.getElem_append_left (show t < (L.drop (i + 1)).length by
                rw [List.length_drop]; omega), List.getElem_drop]
              exact getElem_congr L _ _ (by omega)
            have e2 : ((L.drop (i + 1)) ++ [L[i]'hi])[t + 1]'(by omega) = L[i]'hi := by
              rw [List.getElem_append_right (show (L.drop (i + 1)).length ≤ t + 1 by
                rw [List.length_drop]; omega)]
              exact List.getElem_singleton (by rw [List.length_drop]; omega)
            rw [e1, e2]
            constructor
            · intro hev
              rw [hQi']
              exact hQ2.symm
            · intro hodd
              obtain ⟨a, ha⟩ := hke
              obtain ⟨b, hb⟩ := hio
              obtain ⟨c, hc⟩ := hodd
              omega
        · intro h0
          obtain ⟨a, ha⟩ := hke
          obtain ⟨b, hb⟩ := hio
          have e1 : ((L.drop (i + 1)) ++ [L[i]'hi])[
              ((L.drop (i + 1)) ++ [L[i]'hi]).length - 1]'(by omega) = L[i]'hi := by
            rw [List.getElem_append_right (show (L.drop (i + 1)).length ≤ _ by
              rw [List.length_append, List.length_drop, List.length_singleton]; omega)]
            exact List.getElem_singleton (by
              rw [List.length_append, List.length_drop, List.length_singleton]; omega)
          have e2 : ((L.drop (i + 1)) ++ [L[i]'hi])[0]'(by omega) = L[i + 1]'(by omega) := by
            rw [List.getElem_append_left (show 0 < (L.drop (i + 1)).length by
              rw [List.length_drop]; omega), List.getElem_drop]
          rw [e1, e2]
          exact (hL.step i (by omega)).2 ⟨b, hb⟩
    · -- The row of the last point contains a fresh point: extend the path,
      -- contradicting maximality.
      have hlast : (Even (L.length - 1) → ∀ h : L.length - 1 < L.length,
            (L[L.length - 1]'h).2 = Q.2) ∧
          (Odd (L.length - 1) → ∀ h : L.length - 1 < L.length,
            (L[L.length - 1]'h).1 = Q.1) :=
        ⟨fun _ _ => hQ2.symm, fun hodd => absurd hodd (Nat.not_odd_iff_even.mpr hke)⟩
      have hsnoc := hL.snoc hQS hQin hlast
      have := hLmax (L ++ [Q]) hsnoc
      rw [List.length_append, List.length_singleton] at this
      omega

/-- Main induction: every finite set of points with integer coordinates admits a
balanced signing. -/
lemma main_lemma : ∀ n : ℕ, ∀ S : Finset (ℤ × ℤ), S.card ≤ n → ∃ ε, Balanced S ε := by
  intro n
  induction n with
  | zero =>
    intro S hS
    rw [Nat.le_zero, Finset.card_eq_zero] at hS
    subst hS
    exact ⟨fun _ => 1, balanced_empty⟩
  | succ n IH =>
    intro S hS
    by_cases hne : S.Nonempty
    swap
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      subst hne
      exact ⟨fun _ => 1, balanced_empty⟩
    by_cases hsing : ∃ P ∈ S, (∀ Q ∈ S, Q.1 = P.1 → Q = P) ∨
        (∀ Q ∈ S, Q.2 = P.2 → Q = P)
    · obtain ⟨P, hP, hs⟩ := hsing
      rcases hs with hsc | hsr
      · have herase : (S.erase P).card ≤ n := by
          rw [Finset.card_erase_of_mem hP]
          omega
        obtain ⟨ε', hε'⟩ := IH _ herase
        exact balanced_of_alone_col hP hsc hε'
      · exact balanced_of_alone_row hP hsr n IH hS
    · have hsing' : ∀ P ∈ S,
          ((∀ Q ∈ S, Q.1 = P.1 → Q = P) ∨ (∀ Q ∈ S, Q.2 = P.2 → Q = P)) → False := by
        intro P hP h
        exact hsing ⟨P, hP, h⟩
      have hrow : ∀ P ∈ S, ∃ Q ∈ S, Q ≠ P ∧ Q.2 = P.2 := by
        intro P hP
        by_contra hc
        apply hsing' P hP
        right
        intro Q hQ hQ2
        by_contra hne
        exact hc ⟨Q, hQ, hne, hQ2⟩
      have hcol : ∀ P ∈ S, ∃ Q ∈ S, Q ≠ P ∧ Q.1 = P.1 := by
        intro P hP
        by_contra hc
        apply hsing' P hP
        left
        intro Q hQ hQ1
        by_contra hne
        exact hc ⟨Q, hQ, hne, hQ1⟩
      obtain ⟨C, hCnodup, hCmem, hClen4, hCleneven, hCstep, hCclose⟩ :=
        exists_cycle S hne hrow hcol
      have hsub : C.toFinset ⊆ S := by
        intro p hp
        rw [List.mem_toFinset] at hp
        exact hCmem p hp
      have hcard : (S \ C.toFinset).card ≤ n := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub,
          List.toFinset_card_of_nodup hCnodup]
        have hCle : C.length ≤ S.card := by
          rw [← List.toFinset_card_of_nodup hCnodup]
          exact Finset.card_le_card hsub
        omega
      obtain ⟨ε', hε'1, hε'2, hε'3⟩ := IH _ hcard
      obtain ⟨εC, hεC1, hεCrow, hεCcol⟩ := cycle_balanced C hCnodup hCleneven hCstep hCclose
      refine ⟨fun p => if p ∈ C.toFinset then εC p else ε' p, ?_, ?_, ?_⟩
      · intro p hp
        dsimp only
        by_cases hpc : p ∈ C.toFinset
        · rw [if_pos hpc]
          exact hεC1 p hpc
        · rw [if_neg hpc]
          exact hε'1 p (Finset.mem_sdiff.mpr ⟨hp, hpc⟩)
      · intro x
        have hsplit : S.filter (fun p => p.1 = x) =
            ((S \ C.toFinset).filter (fun p => p.1 = x)) ∪
              (C.toFinset.filter (fun p => p.1 = x)) := by
          conv_lhs => rw [← Finset.sdiff_union_of_subset hsub]
          rw [Finset.filter_union]
        rw [hsplit, Finset.sum_union]
        · have h1 : ∑ p ∈ (S \ C.toFinset).filter (fun p => p.1 = x),
                (if p ∈ C.toFinset then εC p else ε' p)
              = ∑ p ∈ (S \ C.toFinset).filter (fun p => p.1 = x), ε' p := by
            apply Finset.sum_congr rfl
            intro p hp
            rw [Finset.mem_filter] at hp
            exact if_neg (Finset.mem_sdiff.mp hp.1).2
          have h2 : ∑ p ∈ C.toFinset.filter (fun p => p.1 = x),
                (if p ∈ C.toFinset then εC p else ε' p)
              = ∑ p ∈ C.toFinset.filter (fun p => p.1 = x), εC p := by
            apply Finset.sum_congr rfl
            intro p hp
            rw [Finset.mem_filter] at hp
            exact if_pos hp.1
          rw [h1, h2, hεCcol x, add_zero]
          exact hε'2 x
        · rw [Finset.disjoint_left]
          intro p hp
          rw [Finset.mem_filter, Finset.mem_sdiff] at hp
          rw [Finset.mem_filter]
          exact fun hpc => hp.1.2 hpc.1
      · intro y
        have hsplit : S.filter (fun p => p.2 = y) =
            ((S \ C.toFinset).filter (fun p => p.2 = y)) ∪
              (C.toFinset.filter (fun p => p.2 = y)) := by
          conv_lhs => rw [← Finset.sdiff_union_of_subset hsub]
          rw [Finset.filter_union]
        rw [hsplit, Finset.sum_union]
        · have h1 : ∑ p ∈ (S \ C.toFinset).filter (fun p => p.2 = y),
                (if p ∈ C.toFinset then εC p else ε' p)
              = ∑ p ∈ (S \ C.toFinset).filter (fun p => p.2 = y), ε' p := by
            apply Finset.sum_congr rfl
            intro p hp
            rw [Finset.mem_filter] at hp
            exact if_neg (Finset.mem_sdiff.mp hp.1).2
          have h2 : ∑ p ∈ C.toFinset.filter (fun p => p.2 = y),
                (if p ∈ C.toFinset then εC p else ε' p)
              = ∑ p ∈ C.toFinset.filter (fun p => p.2 = y), εC p := by
            apply Finset.sum_congr rfl
            intro p hp
            rw [Finset.mem_filter] at hp
            exact if_pos hp.1
          rw [h1, h2, hεCrow y, add_zero]
          exact hε'3 y
        · rw [Finset.disjoint_left]
          intro p hp
          rw [Finset.mem_filter, Finset.mem_sdiff] at hp
          rw [Finset.mem_filter]
          exact fun hpc => hp.1.2 hpc.1

snip end

determine does_exist : Bool := true

/-- **IMO 1986, Problem 6.**  Given a finite set `S` of points in the plane with
integer coordinates, the points can be colored red or white so that on every
line parallel to one of the coordinate axes the numbers of white and red points
differ by at most one.

We encode the coloring by a sign function `ε : ℤ × ℤ → ℤ` with values in
`{1, -1}` (`1` = white, `-1` = red); the sum of `ε` over the points of `S` on a
line is then exactly the difference between the numbers of white and red points
on that line. -/
problem imo1986_p6 (S : Finset (ℤ × ℤ)) :
    if does_exist then
      ∃ ε : ℤ × ℤ → ℤ,
        (∀ p ∈ S, ε p = 1 ∨ ε p = -1) ∧
        (∀ x : ℤ, |∑ p ∈ S.filter (fun p => p.1 = x), ε p| ≤ 1) ∧
        (∀ y : ℤ, |∑ p ∈ S.filter (fun p => p.2 = y), ε p| ≤ 1)
    else
      ¬ ∃ ε : ℤ × ℤ → ℤ,
        (∀ p ∈ S, ε p = 1 ∨ ε p = -1) ∧
        (∀ x : ℤ, |∑ p ∈ S.filter (fun p => p.1 = x), ε p| ≤ 1) ∧
        (∀ y : ℤ, |∑ p ∈ S.filter (fun p => p.2 = y), ε p| ≤ 1) := by
  simp only [ite_true]
  obtain ⟨ε, hε⟩ := main_lemma S.card S (le_refl _)
  exact ⟨ε, hε⟩

end Imo1986P6
