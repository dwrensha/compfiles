/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.ModEq
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics, .NumberTheory] }

/-!
# International Mathematical Olympiad 1995, Problem 6

Let p be an odd prime number. How many p-element subsets A of
{1, 2, ..., 2p} are there, the sum of whose elements is
divisible by p?
-/

namespace Imo1995P6

snip begin

/-- The cyclic shift `x ↦ x + 1` on `{1, ..., p}` (sending `p` back to `1`),
extended by the identity on all other natural numbers. -/
def shift (p x : ℕ) : ℕ := if x ∈ Finset.Icc 1 p then x % p + 1 else x

/-- The action of `shift p` on sets of naturals: the elements of `A` lying in
`{1, ..., p}` are cyclically shifted and all other elements stay fixed. -/
def shiftSet (p : ℕ) (A : Finset ℕ) : Finset ℕ := A.image (shift p)

theorem shiftSet_eq (p : ℕ) (A : Finset ℕ) : shiftSet p A = A.image (shift p) := rfl

theorem shift_of_mem {p x : ℕ} (hx : x ∈ Finset.Icc 1 p) : shift p x = x % p + 1 := if_pos hx

theorem shift_of_not_mem {p x : ℕ} (hx : x ∉ Finset.Icc 1 p) : shift p x = x := if_neg hx

theorem shift_mem_Icc {p x : ℕ} (hp : 0 < p) (hx : x ∈ Finset.Icc 1 p) :
    shift p x ∈ Finset.Icc 1 p := by
  have h : shift p x = x % p + 1 := if_pos hx
  rw [Finset.mem_Icc] at hx ⊢
  rw [h]
  have hlt := Nat.mod_lt x hp
  omega

theorem shift_mem_iff {p x : ℕ} (hp : 0 < p) :
    shift p x ∈ Finset.Icc 1 p ↔ x ∈ Finset.Icc 1 p := by
  constructor
  · by_cases hx : x ∈ Finset.Icc 1 p
    · exact fun _ ↦ hx
    · rw [shift_of_not_mem hx]
      exact fun h ↦ absurd h hx
  · exact fun hx ↦ shift_mem_Icc hp hx

theorem shift_injective {p : ℕ} (hp : 0 < p) : Function.Injective (shift p) := by
  intro x y hxy
  by_cases hx : x ∈ Finset.Icc 1 p <;> by_cases hy : y ∈ Finset.Icc 1 p
  · have hxp : shift p x = x % p + 1 := if_pos hx
    have hyp : shift p y = y % p + 1 := if_pos hy
    rw [hxp, hyp] at hxy
    have hmod : x % p = y % p := by omega
    rw [Finset.mem_Icc] at hx hy
    by_cases hx2 : x = p
    · have h0 : y % p = 0 := by rw [← hmod, hx2, Nat.mod_self]
      have hd : p ∣ y := Nat.dvd_of_mod_eq_zero h0
      have hle : p ≤ y := Nat.le_of_dvd (by omega) hd
      omega
    · by_cases hy2 : y = p
      · have h0 : x % p = 0 := by rw [hmod, hy2, Nat.mod_self]
        have hd : p ∣ x := Nat.dvd_of_mod_eq_zero h0
        have hle : p ≤ x := Nat.le_of_dvd (by omega) hd
        omega
      · have hxm : x % p = x := Nat.mod_eq_of_lt (by omega)
        have hym : y % p = y := Nat.mod_eq_of_lt (by omega)
        omega
  · have hxp : shift p x = x % p + 1 := if_pos hx
    have hyp : shift p y = y := if_neg hy
    rw [hxp, hyp] at hxy
    have hxI : x % p + 1 ∈ Finset.Icc 1 p := by
      rw [Finset.mem_Icc] at hx ⊢
      have hlt := Nat.mod_lt x hp
      omega
    rw [hxy] at hxI
    exact absurd hxI hy
  · have hxp : shift p x = x := if_neg hx
    have hyp : shift p y = y % p + 1 := if_pos hy
    rw [hxp, hyp] at hxy
    have hyI : y % p + 1 ∈ Finset.Icc 1 p := by
      rw [Finset.mem_Icc] at hy ⊢
      have hlt := Nat.mod_lt y hp
      omega
    rw [← hxy] at hyI
    exact absurd hyI hx
  · have hxp : shift p x = x := if_neg hx
    have hyp : shift p y = y := if_neg hy
    rw [hxp, hyp] at hxy
    exact hxy

theorem shift_iterate_mem_Icc {p : ℕ} (hp : 0 < p) {x : ℕ} (hx : x ∈ Finset.Icc 1 p) (k : ℕ) :
    (shift p)^[k] x = (x - 1 + k) % p + 1 := by
  induction k with
  | zero =>
    simp only [Function.iterate_zero, id_eq, Nat.add_zero]
    rw [Finset.mem_Icc] at hx
    rw [Nat.mod_eq_of_lt (by omega : x - 1 < p), Nat.sub_add_cancel hx.1]
  | succ k ih =>
    have hmem : (x - 1 + k) % p + 1 ∈ Finset.Icc 1 p := by
      rw [Finset.mem_Icc] at hx ⊢
      have hlt := Nat.mod_lt (x - 1 + k) hp
      omega
    rw [Function.iterate_succ_apply', ih]
    have h : shift p ((x - 1 + k) % p + 1) = ((x - 1 + k) % p + 1) % p + 1 := if_pos hmem
    have hmod : ∀ a : ℕ, (a % p + 1) % p = (a + 1) % p := by
      intro a
      have e : a + 1 = a % p + 1 + p * (a / p) := by
        have hd := Nat.div_add_mod a p
        omega
      rw [e, Nat.add_mul_mod_self_left]
    rw [h, hmod]
    have hx' : 1 ≤ x := (Finset.mem_Icc.1 hx).1
    rw [show x - 1 + k + 1 = x - 1 + (k + 1) from by omega]

theorem shift_iterate_not_mem {p : ℕ} {x : ℕ} (hx : x ∉ Finset.Icc 1 p) (k : ℕ) :
    (shift p)^[k] x = x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih]; exact if_neg hx

theorem shift_iterate_mem_Icc' {p : ℕ} (hp : 0 < p) {x : ℕ} (hx : x ∈ Finset.Icc 1 p) (k : ℕ) :
    (shift p)^[k] x ∈ Finset.Icc 1 p := by
  rw [shift_iterate_mem_Icc hp hx k]
  rw [Finset.mem_Icc]
  have hlt := Nat.mod_lt (x - 1 + k) hp
  omega

theorem shift_iterate_p {p : ℕ} (hp : 0 < p) (x : ℕ) : (shift p)^[p] x = x := by
  by_cases hx : x ∈ Finset.Icc 1 p
  · rw [shift_iterate_mem_Icc hp hx p]
    rw [Finset.mem_Icc] at hx
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : x - 1 < p), Nat.sub_add_cancel hx.1]
  · exact shift_iterate_not_mem hx p

theorem shiftSet_iterate (p : ℕ) (A : Finset ℕ) (k : ℕ) :
    (shiftSet p)^[k] A = A.image ((shift p)^[k]) := by
  induction k with
  | zero => rw [Function.iterate_zero, Function.iterate_zero, Finset.image_id, id_eq]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ']
    show (A.image (shift p)^[k]).image (shift p) = A.image ((shift p) ∘ (shift p)^[k])
    rw [Finset.image_image]

theorem shiftSet_iterate_p {p : ℕ} (hp : 0 < p) (A : Finset ℕ) : (shiftSet p)^[p] A = A := by
  rw [shiftSet_iterate, show (shift p)^[p] = id from funext (shift_iterate_p hp), Finset.image_id]

theorem shiftSet_injective {p : ℕ} (hp : 0 < p) : Function.Injective (shiftSet p) :=
  Finset.image_injective (shift_injective hp)

/-- The key congruence: shifting a set once increases its sum by the number of
its elements lying in `{1, ..., p}`, modulo `p`. -/
theorem sum_shiftSet {p : ℕ} (hp : 0 < p) (A : Finset ℕ) :
    ∑ x ∈ shiftSet p A, x ≡ ∑ x ∈ A, x + (A.filter (· ∈ Finset.Icc 1 p)).card [MOD p] := by
  rw [shiftSet_eq, Finset.sum_image (fun x _ y _ h ↦ shift_injective hp h),
    ← Finset.sum_filter_add_sum_filter_not A (· ∈ Finset.Icc 1 p) (shift p)]
  have hL : ∀ x ∈ A.filter (· ∈ Finset.Icc 1 p), shift p x = x % p + 1 :=
    fun x hx ↦ if_pos (Finset.mem_filter.1 hx).2
  have hH : ∀ x ∈ A.filter (· ∉ Finset.Icc 1 p), shift p x = x :=
    fun x hx ↦ if_neg (Finset.mem_filter.1 hx).2
  rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hH]
  have h1 : (∑ x ∈ A.filter (· ∈ Finset.Icc 1 p), (x % p + 1)) ≡
      ∑ x ∈ A.filter (· ∈ Finset.Icc 1 p), x + (A.filter (· ∈ Finset.Icc 1 p)).card [MOD p] := by
    have e : (∑ x ∈ A.filter (· ∈ Finset.Icc 1 p), (x % p + 1)) =
        ∑ x ∈ A.filter (· ∈ Finset.Icc 1 p), x % p + (A.filter (· ∈ Finset.Icc 1 p)).card := by
      rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
    rw [e]
    exact Nat.ModEq.add (Nat.ModEq.sum fun x _ ↦ Nat.mod_modEq x p) (Nat.ModEq.refl _)
  have h2 := h1.add (Nat.ModEq.refl (∑ x ∈ A.filter (· ∉ Finset.Icc 1 p), x))
  have e2 : (∑ x ∈ A.filter (· ∈ Finset.Icc 1 p), x) + (A.filter (· ∈ Finset.Icc 1 p)).card
      + ∑ x ∈ A.filter (· ∉ Finset.Icc 1 p), x =
      ∑ x ∈ A, x + (A.filter (· ∈ Finset.Icc 1 p)).card := by
    rw [add_assoc, add_comm (A.filter (· ∈ Finset.Icc 1 p)).card _, ← add_assoc,
      Finset.sum_filter_add_sum_filter_not]
  rw [e2] at h2
  exact h2

theorem low_card_shiftSet {p : ℕ} (hp : 0 < p) (A : Finset ℕ) :
    ((shiftSet p A).filter (· ∈ Finset.Icc 1 p)).card = (A.filter (· ∈ Finset.Icc 1 p)).card := by
  have h : (shiftSet p A).filter (· ∈ Finset.Icc 1 p) =
      (A.filter (· ∈ Finset.Icc 1 p)).image (shift p) := by
    ext y
    simp only [shiftSet_eq, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨x, hxA, rfl⟩, hxI⟩
      exact ⟨x, ⟨hxA, (shift_mem_iff hp).1 hxI⟩, rfl⟩
    · rintro ⟨x, ⟨hxA, hxI⟩, rfl⟩
      exact ⟨⟨x, hxA, rfl⟩, (shift_mem_iff hp).2 hxI⟩
  rw [h, Finset.card_image_of_injective _ (shift_injective hp)]

theorem low_card_shiftSet_iterate {p : ℕ} (hp : 0 < p) (A : Finset ℕ) (k : ℕ) :
    (((shiftSet p)^[k] A).filter (· ∈ Finset.Icc 1 p)).card = (A.filter (· ∈ Finset.Icc 1 p)).card := by
  induction k with
  | zero => rw [Function.iterate_zero, id_eq]
  | succ k ih => rw [Function.iterate_succ_apply', low_card_shiftSet hp, ih]

theorem sum_shiftSet_iterate {p : ℕ} (hp : 0 < p) (A : Finset ℕ) (i : ℕ) :
    ∑ x ∈ (shiftSet p)^[i] A, x ≡
      ∑ x ∈ A, x + i * (A.filter (· ∈ Finset.Icc 1 p)).card [MOD p] := by
  induction i with
  | zero =>
    simp only [Function.iterate_zero, id_eq, Nat.zero_mul, Nat.add_zero]
    exact Nat.ModEq.refl _
  | succ k ih =>
    have h1 := sum_shiftSet hp ((shiftSet p)^[k] A)
    rw [low_card_shiftSet_iterate hp] at h1
    have h2 : ∑ x ∈ (shiftSet p)^[k + 1] A, x ≡
        (∑ x ∈ A, x + k * (A.filter (· ∈ Finset.Icc 1 p)).card) +
          (A.filter (· ∈ Finset.Icc 1 p)).card [MOD p] := by
      rw [Function.iterate_succ_apply']
      exact h1.trans (Nat.ModEq.add ih (Nat.ModEq.refl _))
    have e : (∑ x ∈ A, x) + k * (A.filter (· ∈ Finset.Icc 1 p)).card +
        (A.filter (· ∈ Finset.Icc 1 p)).card =
        (∑ x ∈ A, x) + (k + 1) * (A.filter (· ∈ Finset.Icc 1 p)).card := by ring
    rw [e] at h2
    exact h2

theorem shiftSet_iterate_mem {p : ℕ} (hp : 0 < p) {A : Finset ℕ}
    (hA : A ∈ (Finset.Icc 1 (2 * p)).powersetCard p) (i : ℕ) :
    (shiftSet p)^[i] A ∈ (Finset.Icc 1 (2 * p)).powersetCard p := by
  rw [Finset.mem_powersetCard] at hA ⊢
  obtain ⟨hsub, hcard⟩ := hA
  rw [shiftSet_iterate]
  refine ⟨?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    by_cases hxI : x ∈ Finset.Icc 1 p
    · have h1 := shift_iterate_mem_Icc' hp hxI i
      rw [Finset.mem_Icc] at h1 ⊢
      omega
    · rw [shift_iterate_not_mem hxI i]
      exact hsub hx
  · rw [Finset.card_image_of_injective _ (Function.Injective.iterate (shift_injective hp) i), hcard]

theorem shiftSet_iterate_Icc_left {p : ℕ} (hp : 0 < p) (i : ℕ) :
    (shiftSet p)^[i] (Finset.Icc 1 p) = Finset.Icc 1 p := by
  rw [shiftSet_iterate]
  have hcard : ((Finset.Icc 1 p).image ((shift p)^[i])).card = (Finset.Icc 1 p).card :=
    Finset.card_image_of_injective _ (Function.Injective.iterate (shift_injective hp) i)
  have hsub : (Finset.Icc 1 p).image ((shift p)^[i]) ⊆ Finset.Icc 1 p := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    exact shift_iterate_mem_Icc' hp hx i
  exact Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)

theorem shiftSet_iterate_Icc_right {p : ℕ} (i : ℕ) :
    (shiftSet p)^[i] (Finset.Icc (p + 1) (2 * p)) = Finset.Icc (p + 1) (2 * p) := by
  rw [shiftSet_iterate]
  ext y
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Finset.mem_Icc] at hx
    rw [shift_iterate_not_mem (show x ∉ Finset.Icc 1 p by rw [Finset.mem_Icc]; omega) i]
    exact Finset.mem_Icc.2 hx
  · intro hy
    refine ⟨y, hy, ?_⟩
    rw [Finset.mem_Icc] at hy
    exact shift_iterate_not_mem (show y ∉ Finset.Icc 1 p by rw [Finset.mem_Icc]; omega) i

theorem shiftSet_iterate_mem_U {p : ℕ} (hp : 0 < p) {A : Finset ℕ}
    (hA : A ∈ (Finset.Icc 1 (2 * p)).powersetCard p \
      {Finset.Icc 1 p, Finset.Icc (p + 1) (2 * p)}) (i : ℕ) :
    (shiftSet p)^[i] A ∈ (Finset.Icc 1 (2 * p)).powersetCard p \
      {Finset.Icc 1 p, Finset.Icc (p + 1) (2 * p)} := by
  rw [Finset.mem_sdiff] at hA ⊢
  obtain ⟨hT, hnot⟩ := hA
  rw [Finset.mem_insert, Finset.mem_singleton] at hnot ⊢
  push Not at hnot ⊢
  refine ⟨shiftSet_iterate_mem hp hT i, ?_, ?_⟩
  · intro h
    exact hnot.1 ((Function.Injective.iterate (shiftSet_injective hp) i)
      (by rw [h, shiftSet_iterate_Icc_left hp i]))
  · intro h
    exact hnot.2 ((Function.Injective.iterate (shiftSet_injective hp) i)
      (by rw [h, shiftSet_iterate_Icc_right i]))

/-- If `A` is a `p`-element subset of `{1, ..., 2p}` different from the two
"interval" subsets, then `A ∩ {1, ..., p}` has between `1` and `p - 1` elements. -/
theorem low_card_bounds {p : ℕ} (hp : 0 < p) {A : Finset ℕ}
    (hA : A ∈ (Finset.Icc 1 (2 * p)).powersetCard p \
      {Finset.Icc 1 p, Finset.Icc (p + 1) (2 * p)}) :
    1 ≤ (A.filter (· ∈ Finset.Icc 1 p)).card ∧
    (A.filter (· ∈ Finset.Icc 1 p)).card ≤ p - 1 := by
  rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, Finset.mem_powersetCard] at hA
  push Not at hA
  obtain ⟨⟨hsub, hcard⟩, hne1, hne2⟩ := hA
  have hsubf : A.filter (· ∈ Finset.Icc 1 p) ⊆ Finset.Icc 1 p :=
    fun x hx ↦ (Finset.mem_filter.1 hx).2
  have hle : (A.filter (· ∈ Finset.Icc 1 p)).card ≤ p := by
    calc (A.filter (· ∈ Finset.Icc 1 p)).card ≤ (Finset.Icc 1 p).card := Finset.card_le_card hsubf
      _ = p := by rw [Nat.card_Icc, Nat.add_sub_cancel]
  have hne_p : (A.filter (· ∈ Finset.Icc 1 p)).card ≠ p := by
    intro hcp
    have heq : A.filter (· ∈ Finset.Icc 1 p) = Finset.Icc 1 p :=
      Finset.eq_of_subset_of_card_le hsubf (by rw [Nat.card_Icc]; omega)
    have hsubA : Finset.Icc 1 p ⊆ A := by
      intro x hx
      rw [← heq] at hx
      exact (Finset.mem_filter.1 hx).1
    exact hne1 (Finset.eq_of_subset_of_card_le hsubA (by rw [Nat.card_Icc, hcard]; omega)).symm
  have hne_0 : (A.filter (· ∈ Finset.Icc 1 p)).card ≠ 0 := by
    intro hc0
    rw [Finset.card_eq_zero] at hc0
    have hsubA : A ⊆ Finset.Icc (p + 1) (2 * p) := by
      intro x hx
      have hxT := hsub hx
      have hxnot : x ∉ Finset.Icc 1 p := by
        intro hxI
        have hxm : x ∈ A.filter (· ∈ Finset.Icc 1 p) := Finset.mem_filter.2 ⟨hx, hxI⟩
        rw [hc0] at hxm
        simp at hxm
      rw [Finset.mem_Icc] at hxT hxnot ⊢
      omega
    exact hne2 (Finset.eq_of_subset_of_card_le hsubA (by rw [Nat.card_Icc]; omega))
  exact ⟨by omega, by omega⟩

/-- For `A` as above, among the `p` sets `A, σ A, ..., σ^{p-1} A` exactly one has
sum divisible by `p` (here `σ` is `shiftSet p`). -/
theorem card_range_filter_eq_one {p : ℕ} (hp : p.Prime) {A : Finset ℕ}
    (hA : A ∈ (Finset.Icc 1 (2 * p)).powersetCard p \
      {Finset.Icc 1 p, Finset.Icc (p + 1) (2 * p)}) :
    ((Finset.range p).filter (fun i ↦ p ∣ ∑ x ∈ (shiftSet p)^[i] A, x)).card = 1 := by
  have hp0 : 0 < p := hp.pos
  haveI : NeZero p := ⟨hp0.ne'⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hc1, hc2⟩ := low_card_bounds hp0 hA
  have key : ∀ i : ℕ, (p ∣ ∑ x ∈ (shiftSet p)^[i] A, x) ↔
      ((∑ x ∈ A, x : ZMod p) + (i : ZMod p) *
        ((A.filter (· ∈ Finset.Icc 1 p)).card : ZMod p)) = 0 := by
    intro i
    have hmod := sum_shiftSet_iterate hp0 A i
    have e : ((∑ x ∈ (shiftSet p)^[i] A, x : ℕ) : ZMod p) =
        (∑ x ∈ A, x : ZMod p) + (i : ZMod p) *
          ((A.filter (· ∈ Finset.Icc 1 p)).card : ZMod p) := by
      rw [← Nat.cast_sum, ← Nat.cast_mul, ← Nat.cast_add]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod
    rw [← ZMod.natCast_eq_zero_iff, e]
  have hc0 : (((A.filter (· ∈ Finset.Icc 1 p)).card : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdiv
    have hle := Nat.le_of_dvd (by omega) hdiv
    omega
  have hinj : Function.Injective
      (fun j : ZMod p ↦ (∑ x ∈ A, x : ZMod p) + j *
        ((A.filter (· ∈ Finset.Icc 1 p)).card : ZMod p)) := by
    intro j1 j2 h
    have h2 := add_left_cancel h
    exact mul_right_cancel₀ hc0 h2
  obtain ⟨j, hj⟩ := Finite.surjective_of_injective hinj 0
  have hval : ((ZMod.val j : ℕ) : ZMod p) = j := ZMod.natCast_rightInverse j
  have hi0 : p ∣ ∑ x ∈ (shiftSet p)^[ZMod.val j] A, x := by
    rw [key (ZMod.val j), hval]
    exact hj
  apply Finset.card_eq_one.2
  refine ⟨ZMod.val j, ?_⟩
  ext k
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨hk, hdk⟩
    rw [key k] at hdk
    have hkj : (k : ZMod p) = j := by
      have e0 : (∑ x ∈ A, x : ZMod p) + (k : ZMod p) *
          ((A.filter (· ∈ Finset.Icc 1 p)).card : ZMod p) = 0 := hdk
      have e1 : (∑ x ∈ A, x : ZMod p) + j *
          ((A.filter (· ∈ Finset.Icc 1 p)).card : ZMod p) = 0 := hj
      have e : (k : ZMod p) * ((A.filter (· ∈ Finset.Icc 1 p)).card : ZMod p) =
          j * ((A.filter (· ∈ Finset.Icc 1 p)).card : ZMod p) :=
        add_left_cancel (e0.trans e1.symm)
      exact mul_right_cancel₀ hc0 e
    have hmod : k ≡ ZMod.val j [MOD p] :=
      (ZMod.natCast_eq_natCast_iff _ _ _).1 (by rw [hval]; exact hkj)
    exact hmod.eq_of_lt_of_lt hk (ZMod.val_lt j)
  · intro hk
    rw [hk]
    exact ⟨ZMod.val_lt j, hi0⟩

/-- Shifting `i` times is a bijection on the good subsets, so for each fixed `i`
the number of good `A` with `p ∣ ∑ σⁱ A` equals the number of good `B` with
`p ∣ ∑ B`. -/
theorem card_U_filter_eq {p : ℕ} (hp : p.Prime) (i : ℕ) (hi : i ∈ Finset.range p) :
    (((Finset.Icc 1 (2 * p)).powersetCard p \
        {Finset.Icc 1 p, Finset.Icc (p + 1) (2 * p)}).filter
      (fun A ↦ p ∣ ∑ x ∈ (shiftSet p)^[i] A, x)).card =
    (((Finset.Icc 1 (2 * p)).powersetCard p \
        {Finset.Icc 1 p, Finset.Icc (p + 1) (2 * p)}).filter
      (fun A ↦ p ∣ ∑ x ∈ A, x)).card := by
  have hp0 : 0 < p := hp.pos
  apply Finset.card_bij (fun A _ ↦ (shiftSet p)^[i] A)
  · intro A hA
    rw [Finset.mem_filter] at hA ⊢
    exact ⟨shiftSet_iterate_mem_U hp0 hA.1 i, hA.2⟩
  · intro A _ B _ h
    exact Function.Injective.iterate (shiftSet_injective hp0) i h
  · intro B hB
    rw [Finset.mem_filter] at hB
    have hip : i ≤ p := Nat.le_of_lt (Finset.mem_range.1 hi)
    refine ⟨(shiftSet p)^[p - i] B, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨shiftSet_iterate_mem_U hp0 hB.1 (p - i), ?_⟩
      rw [← Function.iterate_add_apply, Nat.add_sub_cancel' hip, shiftSet_iterate_p hp0]
      exact hB.2
    · show (shiftSet p)^[i] ((shiftSet p)^[p - i] B) = B
      rw [← Function.iterate_add_apply, Nat.add_sub_cancel' hip, shiftSet_iterate_p hp0]

snip end

determine solution (p : ℕ) : ℕ := 2 + (Nat.choose (2 * p) p - 2) / p

problem imo1995_p6 (p : ℕ) (hp : p.Prime) (hodd : Odd p) :
    (((Finset.Icc 1 (2 * p)).powersetCard p).filter
      (fun A ↦ p ∣ ∑ x ∈ A, x)).card = solution p := by
  have hp0 : 0 < p := hp.pos
  -- The two "fixed" `p`-subsets `{1, ..., p}` and `{p + 1, ..., 2p}`.
  have hB1mem : Finset.Icc 1 p ∈ (Finset.Icc 1 (2 * p)).powersetCard p := by
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.Icc_subset_Icc (le_refl 1) (by omega), ?_⟩
    rw [Nat.card_Icc, Nat.add_sub_cancel]
  have hB2mem : Finset.Icc (p + 1) (2 * p) ∈ (Finset.Icc 1 (2 * p)).powersetCard p := by
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.Icc_subset_Icc (by omega) (le_refl _), ?_⟩
    rw [Nat.card_Icc]
    omega
  have hB1neB2 : Finset.Icc 1 p ≠ Finset.Icc (p + 1) (2 * p) := by
    intro h
    have h1 : (1 : ℕ) ∈ Finset.Icc (p + 1) (2 * p) := h ▸ by
      rw [Finset.mem_Icc]; exact ⟨le_refl 1, by omega⟩
    rw [Finset.mem_Icc] at h1
    omega
  have hsub2 : ({Finset.Icc 1 p, Finset.Icc (p + 1) (2 * p)} : Finset (Finset ℕ)) ⊆
      (Finset.Icc 1 (2 * p)).powersetCard p := by
    intro A hA
    rw [Finset.mem_insert, Finset.mem_singleton] at hA
    rcases hA with rfl | rfl
    · exact hB1mem
    · exact hB2mem
  have hUcard : ((Finset.Icc 1 (2 * p)).powersetCard p \
      {Finset.Icc 1 p, Finset.Icc (p + 1) (2 * p)}).card = Nat.choose (2 * p) p - 2 := by
    rw [Finset.card_sdiff, Finset.card_powersetCard, Nat.card_Icc, Nat.add_sub_cancel,
      Finset.inter_eq_left.2 hsub2,
      Finset.card_insert_of_notMem (by simp [hB1neB2]), Finset.card_singleton]
  -- Both fixed subsets have sum divisible by `p` (here we use that `p` is odd).
  obtain ⟨k, hk⟩ := hodd
  have hsumB1 : p ∣ ∑ x ∈ Finset.Icc 1 p, x := by
    have h0 : (0 : ℕ) ∉ Finset.Icc 1 p := by rw [Finset.mem_Icc]; omega
    have hIcc : Finset.range (p + 1) = insert 0 (Finset.Icc 1 p) := by
      ext x
      rw [Nat.range_succ_eq_Icc_zero, Finset.mem_insert, Finset.mem_Icc, Finset.mem_Icc]
      omega
    have h1 : ∑ x ∈ Finset.Icc 1 p, x = ∑ x ∈ Finset.range (p + 1), x := by
      rw [hIcc, Finset.sum_insert h0, zero_add]
    rw [h1, Finset.sum_range_id, Nat.add_sub_cancel, mul_comm (p + 1) p,
      Nat.mul_div_assoc _ ⟨k + 1, by omega⟩]
    exact ⟨(p + 1) / 2, by ring⟩
  have hsumB2 : p ∣ ∑ x ∈ Finset.Icc (p + 1) (2 * p), x := by
    have himg : (Finset.Icc 1 p).image (· + p) = Finset.Icc (p + 1) (2 * p) := by
      ext y
      simp only [Finset.mem_image, Finset.mem_Icc]
      constructor
      · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
        omega
      · intro hy
        exact ⟨y - p, ⟨by omega, by omega⟩, by omega⟩
    rw [← himg, Finset.sum_image (fun x _ y _ h ↦ by omega)]
    rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, smul_eq_mul]
    exact dvd_add hsumB1 (dvd_mul_right p p)
  -- The double count: pairs `(A, i)` with `A` a good subset, `i < p`, and
  -- `p ∣ ∑ σⁱ A`. Counting by rows gives `|U|`; counting by columns gives `p * M`.
  have hW1 : ((((Finset.Icc 1 (2 * p)).powersetCard p \
        {Finset.Icc 1 p, Finset.Icc (p + 1) (2 * p)}) ×ˢ Finset.range p).filter
      (fun Ai ↦ p ∣ ∑ x ∈ (shiftSet p)^[Ai.2] Ai.1, x)).card =
      ((Finset.Icc 1 (2 * p)).powersetCard p \
        {Finset.Icc 1 p, Finset.Icc (p + 1) (2 * p)}).card := by
    rw [Finset.card_filter, Finset.sum_product]
    trans ∑ A ∈ (Finset.Icc 1 (2 * p)).powersetCard p \
        {Finset.Icc 1 p, Finset.Icc (p + 1) (2 * p)}, (1 : ℕ)
    · refine Finset.sum_congr rfl fun A hA ↦ ?_
      rw [← Finset.card_filter]
      exact card_range_filter_eq_one hp hA
    · rw [Finset.sum_const, smul_eq_mul, mul_one]
  have hW2 : ((((Finset.Icc 1 (2 * p)).powersetCard p \
        {Finset.Icc 1 p, Finset.Icc (p + 1) (2 * p)}) ×ˢ Finset.range p).filter
      (fun Ai ↦ p ∣ ∑ x ∈ (shiftSet p)^[Ai.2] Ai.1, x)).card =
      p * (((Finset.Icc 1 (2 * p)).powersetCard p \
        {Finset.Icc 1 p, Finset.Icc (p + 1) (2 * p)}).filter
        (fun A ↦ p ∣ ∑ x ∈ A, x)).card := by
    rw [Finset.card_filter, Finset.sum_product_right]
    trans ∑ _i ∈ Finset.range p, (((Finset.Icc 1 (2 * p)).powersetCard p \
        {Finset.Icc 1 p, Finset.Icc (p + 1) (2 * p)}).filter
        (fun A ↦ p ∣ ∑ x ∈ A, x)).card
    · refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [← Finset.card_filter]
      exact card_U_filter_eq hp i hi
    · rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hEq : ((Finset.Icc 1 (2 * p)).powersetCard p \
        {Finset.Icc 1 p, Finset.Icc (p + 1) (2 * p)}).card =
      p * (((Finset.Icc 1 (2 * p)).powersetCard p \
        {Finset.Icc 1 p, Finset.Icc (p + 1) (2 * p)}).filter
        (fun A ↦ p ∣ ∑ x ∈ A, x)).card := hW1 ▸ hW2
  have hM : (Nat.choose (2 * p) p - 2) / p =
      (((Finset.Icc 1 (2 * p)).powersetCard p \
        {Finset.Icc 1 p, Finset.Icc (p + 1) (2 * p)}).filter
        (fun A ↦ p ∣ ∑ x ∈ A, x)).card := by
    have hdiv : p ∣ Nat.choose (2 * p) p - 2 := ⟨_, hUcard.symm.trans hEq⟩
    apply Nat.mul_right_cancel hp0
    rw [Nat.div_mul_cancel hdiv, ← hUcard, hEq, mul_comm]
  -- Assemble: the full collection splits into the good subsets and the two
  -- fixed subsets, both of which contribute.
  have hTU : (Finset.Icc 1 (2 * p)).powersetCard p =
      ((Finset.Icc 1 (2 * p)).powersetCard p \
        {Finset.Icc 1 p, Finset.Icc (p + 1) (2 * p)}) ∪
        {Finset.Icc 1 p, Finset.Icc (p + 1) (2 * p)} :=
    (Finset.sdiff_union_of_subset hsub2).symm
  have hfilter2 : ({Finset.Icc 1 p, Finset.Icc (p + 1) (2 * p)} : Finset (Finset ℕ)).filter
      (fun A ↦ p ∣ ∑ x ∈ A, x) = {Finset.Icc 1 p, Finset.Icc (p + 1) (2 * p)} := by
    apply Finset.filter_true_of_mem
    intro A hA
    rw [Finset.mem_insert, Finset.mem_singleton] at hA
    rcases hA with rfl | rfl
    · exact hsumB1
    · exact hsumB2
  have hdisj : Disjoint
      (((Finset.Icc 1 (2 * p)).powersetCard p \
        {Finset.Icc 1 p, Finset.Icc (p + 1) (2 * p)}).filter (fun A ↦ p ∣ ∑ x ∈ A, x))
      (({Finset.Icc 1 p, Finset.Icc (p + 1) (2 * p)} : Finset (Finset ℕ)).filter
        (fun A ↦ p ∣ ∑ x ∈ A, x)) :=
    Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
      (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) Finset.sdiff_disjoint)
  calc (((Finset.Icc 1 (2 * p)).powersetCard p).filter (fun A ↦ p ∣ ∑ x ∈ A, x)).card
      = ((((Finset.Icc 1 (2 * p)).powersetCard p \
            {Finset.Icc 1 p, Finset.Icc (p + 1) (2 * p)}) ∪
          {Finset.Icc 1 p, Finset.Icc (p + 1) (2 * p)}).filter
          (fun A ↦ p ∣ ∑ x ∈ A, x)).card := by conv_lhs => rw [hTU]
    _ = ((((Finset.Icc 1 (2 * p)).powersetCard p \
            {Finset.Icc 1 p, Finset.Icc (p + 1) (2 * p)}).filter (fun A ↦ p ∣ ∑ x ∈ A, x)) ∪
          (({Finset.Icc 1 p, Finset.Icc (p + 1) (2 * p)} : Finset (Finset ℕ)).filter
            (fun A ↦ p ∣ ∑ x ∈ A, x))).card := by rw [Finset.filter_union]
    _ = (((Finset.Icc 1 (2 * p)).powersetCard p \
            {Finset.Icc 1 p, Finset.Icc (p + 1) (2 * p)}).filter (fun A ↦ p ∣ ∑ x ∈ A, x)).card
          + 2 := by
        rw [Finset.card_union_of_disjoint hdisj, hfilter2,
          Finset.card_insert_of_notMem (by simp [hB1neB2]), Finset.card_singleton]
    _ = 2 + (Nat.choose (2 * p) p - 2) / p := by rw [hM]; omega

end Imo1995P6
