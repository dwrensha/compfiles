/-
Copyright (c) 2025 the Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Kimi K3
-/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.NumberTheory]
}

/-!
# International Mathematical Olympiad 2022, Problem 3

Let k be a positive integer and let S be a finite set of odd prime
integers. Prove that there is at most one way (up to rotation and reflection)
to place the elements of S around a circle such that the product of any
two neighbors is of the form x² + x + k for some positive integer x.

(formalization note: `S` is assumed to be nonempty; the statement would be
false for `S = ∅` because the rotations are indexed by the empty type `Fin #S`.)

-/

namespace Imo2022P3


open scoped Finset

open Fin.NatCast

/-- The condition of the problem on a placement of numbers round a circle. -/
def Condition (k : ℕ) (S : Finset ℕ) (p : Fin #S ≃ S) : Prop :=
  ∀ i, have : NeZero #S := ⟨i.pos.ne'⟩
  ∃ x : ℕ, 0 < x ∧ ((p i : ℕ) * (p (i + 1) : ℕ)) = x ^ 2 + x + k

-- snip begin

/-- Auxiliary condition: `m * n` is of the form `x ^ 2 + x + k` for a nonnegative
integer `x`.  The problem uses positive `x`, but uniqueness of placements for the
weaker (nonnegative) condition implies uniqueness for the stronger one. -/
def good (k m n : ℕ) : Prop := ∃ x : ℕ, m * n = x ^ 2 + x + k

/-- A product below `M ^ 2` that is good forces the witness `x` to be below `M`. -/
lemma lt_of_good_of_lt {k M q x : ℕ} (hM : Nat.Prime M) (hq : q < M)
    (hx : M * q = x ^ 2 + x + k) : x < M := by
  have hM0 : 0 < M := hM.pos
  have h1 : M * q < M * M := Nat.mul_lt_mul_of_pos_left hq hM0
  nlinarith [hx, h1]

/-- Two distinct roots of `T ^ 2 + T + k` below the prime `M` sum to `M - 1`. -/
lemma add_eq_of_dvd_of_dvd {k M x y : ℕ} (hM : Nat.Prime M) (hxM : x < M) (hyM : y < M)
    (hxy : x ≠ y) (hx : M ∣ x ^ 2 + x + k) (hy : M ∣ y ^ 2 + y + k) :
    x + y + 1 = M := by
  have hM0 : 0 < M := hM.pos
  haveI := Fact.mk hM
  have hx' : (x : ZMod M) ^ 2 + (x : ZMod M) + (k : ZMod M) = 0 := by
    have h : ((x ^ 2 + x + k : ℕ) : ZMod M) = 0 :=
      (ZMod.natCast_eq_zero_iff (x ^ 2 + x + k) M).mpr hx
    push_cast at h
    exact h
  have hy' : (y : ZMod M) ^ 2 + (y : ZMod M) + (k : ZMod M) = 0 := by
    have h : ((y ^ 2 + y + k : ℕ) : ZMod M) = 0 :=
      (ZMod.natCast_eq_zero_iff (y ^ 2 + y + k) M).mpr hy
    push_cast at h
    exact h
  have h3 : ((x : ZMod M) - y) * (x + y + 1) = 0 := by linear_combination hx' - hy'
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exfalso
    have h5 : (x : ZMod M) = y := sub_eq_zero.mp h4
    rw [ZMod.natCast_eq_natCast_iff] at h5
    exact hxy (h5.eq_of_lt_of_lt hxM hyM)
  · have h5 : ((x + y + 1 : ℕ) : ZMod M) = 0 := by
      push_cast
      linear_combination h4
    obtain ⟨t, ht⟩ := (ZMod.natCast_eq_zero_iff (x + y + 1) M).mp h5
    have hpos : 0 < x + y + 1 := by omega
    have hlt : x + y + 1 < 2 * M := by omega
    have ht1 : 1 ≤ t := by
      rcases t with _ | t
      · simp at ht
      · exact Nat.succ_le_succ (Nat.zero_le _)
    have ht2 : t ≤ 1 := by
      by_contra h
      have h' : 2 ≤ t := Nat.lt_of_not_le h
      have h4 : 2 * M ≤ x + y + 1 := by
        have h5' := Nat.mul_le_mul (le_refl M) h'
        omega
      omega
    have ht3 : t = 1 := by omega
    subst ht3
    simpa using ht

/-- Vieta for the two roots: their product is congruent to `k` modulo `M`. -/
lemma dvd_sub_of_good_of_good {k M q r x y : ℕ} (hM : Nat.Prime M)
    (hq : q < M) (hr : r < M) (hqr : q ≠ r)
    (hx : M * q = x ^ 2 + x + k) (hy : M * r = y ^ 2 + y + k) :
    x + y + 1 = M ∧ (M : ℤ) ∣ (x * y : ℤ) - k := by
  have hM0 : 0 < M := hM.pos
  haveI := Fact.mk hM
  have hxM : x < M := lt_of_good_of_lt hM hq hx
  have hyM : y < M := lt_of_good_of_lt hM hr hy
  have hxy : x ≠ y := by
    rintro rfl
    apply hqr
    have h : M * q = M * r := by rw [hx, hy]
    exact Nat.eq_of_mul_eq_mul_left hM0 h
  have hsum : x + y + 1 = M :=
    add_eq_of_dvd_of_dvd hM hxM hyM hxy ⟨q, hx.symm⟩ ⟨r, hy.symm⟩
  refine ⟨hsum, ?_⟩
  have hx' : (x : ZMod M) ^ 2 + (x : ZMod M) + (k : ZMod M) = 0 := by
    have h : ((x ^ 2 + x + k : ℕ) : ZMod M) = 0 :=
      (ZMod.natCast_eq_zero_iff (x ^ 2 + x + k) M).mpr ⟨q, hx.symm⟩
    push_cast at h
    exact h
  have hyz : (y : ZMod M) = -1 - x := by
    have h5 : ((x + y + 1 : ℕ) : ZMod M) = 0 := by
      rw [hsum]
      exact ZMod.natCast_self M
    push_cast at h5
    linear_combination h5
  have h6 : (((x * y : ℤ) - k : ℤ) : ZMod M) = 0 := by
    push_cast
    rw [hyz]
    linear_combination -hx'
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd ((x * y : ℤ) - k) M).mp h6

/-- The key multiplicativity lemma (Chen's Claim 2): if the prime `M` has two
distinct smaller good partners `q` and `r`, then `q * r` is itself good. -/
lemma good_of_good_of_good {k M q r : ℕ} (hM : Nat.Prime M) (hq : q < M) (hr : r < M)
    (hqr : q ≠ r) (h1 : good k M q) (h2 : good k M r) : good k q r := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  obtain ⟨hsum, z, hz⟩ := dvd_sub_of_good_of_good hM hq hr hqr hx hy
  have hM0 : (0 : ℤ) < M := by exact_mod_cast hM.pos
  have hid : ((x : ℤ) ^ 2 + x + k) * ((y : ℤ) ^ 2 + y + k)
      = ((x : ℤ) * y - k) ^ 2 + ((x : ℤ) * y - k) * (x + y + 1)
        + k * (x + y + 1) ^ 2 := by ring
  have hx' : (x : ℤ) ^ 2 + x + k = M * q := by exact_mod_cast hx.symm
  have hy' : (y : ℤ) ^ 2 + y + k = M * r := by exact_mod_cast hy.symm
  have hsum' : (x : ℤ) + y + 1 = M := by exact_mod_cast hsum
  rw [hx', hy', hsum', hz] at hid
  have h2 : (M : ℤ) ^ 2 * (q * r) = (M : ℤ) ^ 2 * (z ^ 2 + z + k) := by
    linear_combination hid
  have h3 : (q : ℤ) * r = z ^ 2 + z + k := by
    rcases mul_eq_mul_left_iff.mp h2 with h | h
    · exact h
    · exfalso
      have : (M : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 hM0.ne'
      exact this h
  have hw0 : 0 ≤ max z (-1 - z) := by
    by_cases h : 0 ≤ z
    · exact le_max_of_le_left h
    · exact le_max_of_le_right (by omega)
  have hww : max z (-1 - z) ^ 2 + max z (-1 - z) = z ^ 2 + z := by
    by_cases h : 0 ≤ z
    · rw [max_eq_left (by omega : -1 - z ≤ z)]
    · rw [max_eq_right (by omega : z ≤ -1 - z)]
      ring
  refine ⟨(max z (-1 - z)).toNat, ?_⟩
  have h4 : ((max z (-1 - z)).toNat : ℤ) ^ 2 + (max z (-1 - z)).toNat + k
      = (q : ℤ) * r := by
    rw [Int.toNat_of_nonneg hw0, hww]
    linear_combination h3.symm
  exact_mod_cast h4.symm

/-- A quadratic has at most two roots below a prime `M`: the set `T` of
solutions `x < M` to `M ∣ x ^ 2 + x + k` has at most two elements. -/
lemma card_roots_le_two {k M : ℕ} (hM : Nat.Prime M) (T : Finset ℕ)
    (hT1 : ∀ x ∈ T, x < M) (hT2 : ∀ x ∈ T, M ∣ x ^ 2 + x + k) : T.card ≤ 2 := by
  by_cases hT : T.Nonempty
  · by_cases hT2' : (T.erase (T.min' hT)).Nonempty
    · set m₁ := T.min' hT with hm₁
      set m₂ := (T.erase m₁).min' hT2' with hm₂
      have hm₁T : m₁ ∈ T := T.min'_mem hT
      have hm₂T : m₂ ∈ T := (T.erase m₁).min'_mem hT2' |> Finset.mem_of_mem_erase
      have hm₂ne : m₂ ≠ m₁ := by
        have h := (T.erase m₁).min'_mem hT2'
        rw [Finset.mem_erase] at h
        exact h.1
      have hsub : T ⊆ {m₁, m₂} := by
        intro x hx
        by_contra hnot
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
        have hm₁x : m₁ ≠ x := fun h => hnot.1 h.symm
        have hmx : m₂ ≠ x := fun h => hnot.2 h.symm
        have h1 : m₁ + x + 1 = M :=
          add_eq_of_dvd_of_dvd hM (hT1 m₁ hm₁T) (hT1 x hx) hm₁x
            (hT2 m₁ hm₁T) (hT2 x hx)
        have h2 : m₁ + m₂ + 1 = M :=
          add_eq_of_dvd_of_dvd hM (hT1 m₁ hm₁T) (hT1 m₂ hm₂T) hm₂ne.symm
            (hT2 m₁ hm₁T) (hT2 m₂ hm₂T)
        exact hmx (by omega)
      calc T.card ≤ ({m₁, m₂} : Finset ℕ).card := Finset.card_le_card hsub
        _ ≤ 2 := by simpa using Finset.card_insert_le m₁ ({m₂} : Finset ℕ)
    · have hsub : T ⊆ {T.min' hT} := by
        intro x hx
        by_contra hnot
        rw [Finset.mem_singleton] at hnot
        have hmem : x ∈ T.erase (T.min' hT) :=
          Finset.mem_erase.mpr ⟨hnot, hx⟩
        rw [Finset.not_nonempty_iff_eq_empty.mp hT2'] at hmem
        simp at hmem
      calc T.card ≤ ({T.min' hT} : Finset ℕ).card := Finset.card_le_card hsub
        _ = 1 := Finset.card_singleton _
        _ ≤ 2 := one_lt_two.le
  · rw [Finset.not_nonempty_iff_eq_empty.mp hT]
    simp

/-- Chen's Claim 1: a prime `M` has at most two good partners below it
inside any set of smaller numbers. -/
lemma card_good_le_two {k M : ℕ} (hM : Nat.Prime M) (S : Finset ℕ)
    [DecidablePred (good k M)] (hSM : ∀ q ∈ S, q < M) :
    (S.filter (good k M ·)).card ≤ 2 := by
  classical
  set f : ℕ → ℕ := fun q ↦ if h : good k M q then h.choose else 0 with hf_def
  have hf : ∀ q ∈ S.filter (good k M ·), M * q = (f q) ^ 2 + f q + k := by
    intro q hq
    rw [Finset.mem_filter] at hq
    have h := hq.2.choose_spec
    simp only [hf_def, dif_pos hq.2]
    exact h
  have hinj : Set.InjOn f (S.filter (good k M ·)) := by
    intro q₁ h1 q₂ h2 heq
    have e1 := hf q₁ h1
    have e2 := hf q₂ h2
    have h : M * q₁ = M * q₂ := by rw [e1, e2, heq]
    exact Nat.eq_of_mul_eq_mul_left hM.pos h
  rw [← Finset.card_image_of_injOn hinj]
  apply card_roots_le_two hM
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨q, hq, rfl⟩ := hx
    exact lt_of_good_of_lt hM (hSM q (Finset.mem_filter.mp hq).1) (hf q hq)
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨q, hq, rfl⟩ := hx
    exact ⟨q, (hf q hq).symm⟩

/-- `good` is symmetric in the two factors. -/
lemma good_comm {k m n : ℕ} (h : good k m n) : good k n m := by
  obtain ⟨x, hx⟩ := h
  exact ⟨x, by rw [mul_comm]; exact hx⟩

/-- Injectivity of the `ZMod n` cast on `Fin n`. -/
lemma zmod_inj {n : ℕ} {a b : Fin n} (h : (a.val : ZMod n) = b.val) : a = b := by
  rw [ZMod.natCast_eq_natCast_iff] at h
  exact Fin.ext (h.eq_of_lt_of_lt a.isLt b.isLt)

/-- The `ZMod n` cast of a sum in `Fin n`. -/
lemma zmod_add {n : ℕ} (a b : Fin n) : ((a + b).val : ZMod n) = a.val + b.val := by
  rw [Fin.val_add, ZMod.natCast_mod, Nat.cast_add]

/-- The `ZMod n` cast of `1 : Fin n`. -/
lemma zmod_one {n : ℕ} [NeZero n] : ((1 : Fin n).val : ZMod n) = 1 := by
  rw [Fin.val_one' n, ZMod.natCast_mod, Nat.cast_one]

/-- The `ZMod n` cast of `Fin.rev`. -/
lemma zmod_rev {n : ℕ} [NeZero n] (j : Fin n) :
    ((Fin.rev j).val : ZMod n) = -1 - j.val := by
  have hrv : (Fin.rev j).val = n - (j.val + 1) := rfl
  have hj : j.val + 1 ≤ n := j.isLt
  rw [hrv, Nat.cast_sub hj, ZMod.natCast_self]
  push_cast
  ring

/-- The successor permutation of a placement: sends each element to its
clockwise neighbor. -/
def succPerm {S : Finset ℕ} (p : Fin #S ≃ S) : Equiv.Perm S :=
  (p.symm.trans (finRotate #S)).trans p

lemma succPerm_apply {S : Finset ℕ} [NeZero #S] (p : Fin #S ≃ S) (j : Fin #S) :
    succPerm p (p j) = p (j + 1) := by
  simp [succPerm, finRotate_apply]

/-- Validity of a permutation of `S`: every element has a good product with its
successor. -/
def ValidPerm (k : ℕ) {S : Finset ℕ} (σ : Equiv.Perm S) : Prop :=
  ∀ s : S, good k (s : ℕ) (σ s : ℕ)

/-- Connectivity of a permutation of `S`: it is a single cycle. -/
def ConnectedP {S : Finset ℕ} (σ : Equiv.Perm S) : Prop :=
  ∀ s t : S, ∃ m : ℕ, σ^[m] s = t

lemma validPerm_succPerm {k : ℕ} {S : Finset ℕ} [NeZero #S] {p : Fin #S ≃ S}
    (hp : ∀ j, good k (p j : ℕ) (p (j + 1) : ℕ)) : ValidPerm k (succPerm p) := by
  intro s
  have h1 : succPerm p s = p (p.symm s + 1) := by simp [succPerm, finRotate_apply]
  rw [h1]
  have h := hp (p.symm s)
  rwa [Equiv.apply_symm_apply] at h

/-- Iteration of a conjugated map. -/
lemma iterate_conj {α β : Type*} (c : α ≃ β) (τ : α → α) (m : ℕ) :
    (⇑c ∘ τ ∘ ⇑c.symm)^[m] = ⇑c ∘ τ^[m] ∘ ⇑c.symm := by
  induction m with
  | zero =>
    funext x
    simp
  | succ m ih =>
    rw [Function.iterate_succ' , ih]
    funext x
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
    rw [Function.iterate_succ_apply']

lemma iterate_finRotate {n : ℕ} [NeZero n] (m : ℕ) (j : Fin n) :
    (finRotate n)^[m] j = j + (m : Fin n) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, finRotate_apply]
    apply zmod_inj
    simp only [zmod_add, Fin.val_natCast, ZMod.natCast_mod, Nat.cast_add, Nat.cast_one]
    ring

lemma succPerm_iterate {S : Finset ℕ} [NeZero #S] (p : Fin #S ≃ S)
    (m : ℕ) (j : Fin #S) :
    (succPerm p)^[m] (p j) = p (j + (m : Fin #S)) := by
  have hsucc : ⇑(succPerm p) = ⇑p ∘ ⇑(finRotate #S) ∘ ⇑p.symm := by
    funext x
    simp [succPerm]
  have h2 : (succPerm p)^[m] = ⇑p ∘ (finRotate #S)^[m] ∘ ⇑p.symm := by
    rw [hsucc]
    exact iterate_conj p (⇑(finRotate #S)) m
  rw [h2]
  simp only [Function.comp_apply, Equiv.symm_apply_apply]
  rw [iterate_finRotate]

lemma connectedP_succPerm {S : Finset ℕ} (hne : S.Nonempty) (p : Fin #S ≃ S) :
    ConnectedP (succPerm p) := by
  haveI : NeZero #S := ⟨(Finset.card_pos.mpr hne).ne'⟩
  intro s t
  set a := p.symm s
  set b := p.symm t
  have hs : p a = s := Equiv.apply_symm_apply p s
  have ht : p b = t := Equiv.apply_symm_apply p t
  refine ⟨(((b.val : ZMod #S) - a.val).val : ℕ), ?_⟩
  rw [← hs, succPerm_iterate p, ← ht]
  congr 1
  apply zmod_inj
  simp only [zmod_add, Fin.val_natCast, ZMod.natCast_mod, ZMod.natCast_zmod_val]
  ring

/-- `i.succ` in `Fin (m+1)` is `i.castSucc + 1`. -/
lemma fin_succ_eq {m : ℕ} (i : Fin m) : i.succ = i.castSucc + 1 := by
  have hm : 0 < m := i.pos
  apply Fin.ext
  rw [Fin.val_succ, Fin.val_add, Fin.val_one', Fin.val_castSucc,
    Nat.mod_eq_of_lt (by omega : 1 < m + 1), Nat.mod_eq_of_lt (by omega : i.val + 1 < m + 1)]

/-- A permutation of `Fin n` commuting with `+ 1` is a rotation. -/
lemma zmod_eq_of_add_key {n : ℕ} [NeZero n] (g : Equiv.Perm (Fin n))
    (key : ∀ j : Fin n, g (j + 1) = g j + 1) (j : Fin n) :
    ((g j).val : ZMod n) = ((g 0).val : ZMod n) + j.val := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  induction j using Fin.induction with
  | zero => simp
  | succ i ih =>
    rw [fin_succ_eq i, key _]
    simp only [zmod_add, zmod_one, ih, Fin.val_castSucc]
    ring

/-- A permutation of `Fin n` anti-commuting with `+ 1` is a reflection. -/
lemma zmod_eq_of_sub_key {n : ℕ} [NeZero n] (g : Equiv.Perm (Fin n))
    (key : ∀ j : Fin n, g (j + 1) + 1 = g j) (j : Fin n) :
    ((g j).val : ZMod n) = ((g 0).val : ZMod n) - j.val := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  induction j using Fin.induction with
  | zero => simp
  | succ i ih =>
    have e : ((g (i.castSucc + 1)).val : ZMod (m + 1))
        = ((g i.castSucc).val : ZMod (m + 1)) - 1 := by
      have h2 := key i.castSucc
      have h3 : ((g (i.castSucc + 1) + 1 : Fin (m + 1)).val : ZMod (m + 1))
          = ((g i.castSucc).val : ZMod (m + 1)) := by rw [h2]
      rw [zmod_add, zmod_one] at h3
      linear_combination h3
    rw [fin_succ_eq i, e]
    simp only [ih, Fin.val_castSucc, zmod_add, zmod_one]
    ring

/-- If two placements have the same successor permutation, they differ by a
rotation. -/
lemma rot_of_succPerm_eq {S : Finset ℕ} (hne : S.Nonempty) {p₁ p₂ : Fin #S ≃ S}
    (h : succPerm p₁ = succPerm p₂) :
    ∃ i, ∀ j, p₂ j = p₁ (j + i) := by
  haveI : NeZero #S := ⟨(Finset.card_pos.mpr hne).ne'⟩
  set g : Equiv.Perm (Fin #S) := p₂.trans p₁.symm with hg
  have key : ∀ j : Fin #S, g (j + 1) = g j + 1 := by
    intro j
    apply p₁.injective
    have e1 : p₁ (g (j + 1)) = p₂ (j + 1) := by simp [hg]
    have e4 : succPerm p₁ (p₂ j) = p₁ (g j + 1) := by
      have h2 := succPerm_apply p₁ (g j)
      rwa [show p₁ (g j) = p₂ j by simp [hg]] at h2
    have e3 : succPerm p₂ (p₂ j) = succPerm p₁ (p₂ j) := by rw [h]
    rw [e1, ← e4, ← e3, succPerm_apply]
  refine ⟨g 0, fun j => ?_⟩
  have hfin : g j = j + g 0 := by
    apply zmod_inj
    rw [zmod_eq_of_add_key g key j, zmod_add]
    ring
  calc p₂ j = p₁ (g j) := by simp [hg]
    _ = p₁ (j + g 0) := by rw [hfin]

/-- If the successor permutation of one placement is the inverse of the other's,
they differ by a reflection composed with a rotation. -/
lemma ref_of_succPerm_eq {S : Finset ℕ} (hne : S.Nonempty) {p₁ p₂ : Fin #S ≃ S}
    (h : succPerm p₁ = (succPerm p₂)⁻¹) :
    ∃ i, ∀ j, p₂ j = p₁ (Fin.rev j + i) := by
  haveI : NeZero #S := ⟨(Finset.card_pos.mpr hne).ne'⟩
  set g : Equiv.Perm (Fin #S) := p₂.trans p₁.symm with hg
  have key : ∀ j : Fin #S, g (j + 1) + 1 = g j := by
    intro j
    apply p₁.injective
    have e1 : p₁ (g (j + 1) + 1) = succPerm p₁ (p₁ (g (j + 1))) :=
      (succPerm_apply p₁ (g (j + 1))).symm
    have e2 : p₁ (g (j + 1)) = p₂ (j + 1) := by simp [hg]
    have e3 : succPerm p₁ (p₂ (j + 1)) = p₂ j := by
      rw [h]
      show (succPerm p₂)⁻¹ (p₂ (j + 1)) = p₂ j
      rw [← succPerm_apply p₂ j]
      exact Equiv.symm_apply_apply _ _
    rw [e1, e2, e3]
    simp [hg]
  refine ⟨g 0 + 1, fun j => ?_⟩
  have hfin : g j = Fin.rev j + (g 0 + 1) := by
    apply zmod_inj
    rw [zmod_eq_of_sub_key g key j, zmod_add, zmod_rev, zmod_add, zmod_one]
    ring
  calc p₂ j = p₁ (g j) := by simp [hg]
    _ = p₁ (Fin.rev j + (g 0 + 1)) := by rw [hfin]

/-- Deleting `M` from a permutation: the short-circuited permutation on
`S.erase M`, sending the predecessor of `M` to the successor of `M`. -/
noncomputable def delPerm {S : Finset ℕ} (τ : Equiv.Perm S) (M : S) (hrM : τ M ≠ M) :
    Equiv.Perm (S.erase M) :=
  have hfun : ∀ s : (S.erase M),
      (if τ ⟨s.1, Finset.mem_of_mem_erase s.2⟩ = M then (τ M).1
       else (τ ⟨s.1, Finset.mem_of_mem_erase s.2⟩).1) ∈ S.erase M := by
    intro s
    by_cases h : τ ⟨s.1, Finset.mem_of_mem_erase s.2⟩ = M
    · rw [if_pos h]
      exact Finset.mem_erase.mpr ⟨fun hval => hrM (Subtype.ext hval), (τ M).2⟩
    · rw [if_neg h]
      exact Finset.mem_erase.mpr ⟨fun hval => h (Subtype.ext hval), (τ _).2⟩
  have hinj : Function.Injective
      (fun s : (S.erase M) =>
        (⟨if τ ⟨s.1, Finset.mem_of_mem_erase s.2⟩ = M then (τ M).1
          else (τ ⟨s.1, Finset.mem_of_mem_erase s.2⟩).1, hfun s⟩ : (S.erase M))) := by
    intro s t hst
    have hst' := congrArg Subtype.val hst
    dsimp only [] at hst'
    by_cases hs : τ ⟨s.1, Finset.mem_of_mem_erase s.2⟩ = M
    · by_cases ht : τ ⟨t.1, Finset.mem_of_mem_erase t.2⟩ = M
      · have hsteq : (⟨s.1, Finset.mem_of_mem_erase s.2⟩ : S)
            = ⟨t.1, Finset.mem_of_mem_erase t.2⟩ :=
          τ.injective (hs.trans ht.symm)
        exact Subtype.ext (Subtype.mk_eq_mk.mp hsteq)
      · exfalso
        rw [if_pos hs, if_neg ht] at hst'
        have h2 : (⟨t.1, Finset.mem_of_mem_erase t.2⟩ : S) = M :=
          τ.injective (Subtype.ext hst'.symm)
        exact (Finset.mem_erase.mp t.2).1 (Subtype.mk_eq_mk.mp h2)
    · by_cases ht : τ ⟨t.1, Finset.mem_of_mem_erase t.2⟩ = M
      · exfalso
        rw [if_neg hs, if_pos ht] at hst'
        have h2 : (⟨s.1, Finset.mem_of_mem_erase s.2⟩ : S) = M :=
          τ.injective (Subtype.ext hst')
        exact (Finset.mem_erase.mp s.2).1 (Subtype.mk_eq_mk.mp h2)
      · rw [if_neg hs, if_neg ht] at hst'
        have hsteq : (⟨s.1, Finset.mem_of_mem_erase s.2⟩ : S)
            = ⟨t.1, Finset.mem_of_mem_erase t.2⟩ :=
          τ.injective (Subtype.ext hst')
        exact Subtype.ext (Subtype.mk_eq_mk.mp hsteq)
  Equiv.ofBijective
    (fun s : (S.erase M) =>
      (⟨if τ ⟨s.1, Finset.mem_of_mem_erase s.2⟩ = M then (τ M).1
        else (τ ⟨s.1, Finset.mem_of_mem_erase s.2⟩).1, hfun s⟩ : (S.erase M)))
    (Finite.injective_iff_bijective.mp hinj)

/-- The computation rule for `delPerm`. -/
lemma delPerm_val {S : Finset ℕ} {τ : Equiv.Perm S} {M : S} {hrM : τ M ≠ M}
    (s : S.erase M) :
    (delPerm τ M hrM s).1
      = if τ ⟨s.1, Finset.mem_of_mem_erase s.2⟩ = M then (τ M).1
        else (τ ⟨s.1, Finset.mem_of_mem_erase s.2⟩).1 := by
  unfold delPerm
  rw [Equiv.ofBijective_apply]

/-- The deleted permutation stays valid: the one new edge is good by
`good_of_good_of_good`. -/
lemma validPerm_delPerm {k : ℕ} {S : Finset ℕ} {τ : Equiv.Perm S} {M : S}
    {hrM : τ M ≠ M} (hv : ValidPerm k τ)
    (hMprime : Nat.Prime M.1)
    (hq : (τ⁻¹ M).1 < M.1) (hr : (τ M).1 < M.1) (hqr : τ⁻¹ M ≠ τ M)
    (hgq : good k M.1 (τ⁻¹ M).1) (hgr : good k M.1 (τ M).1) :
    ValidPerm k (delPerm τ M hrM) := by
  intro s
  rw [delPerm_val]
  by_cases h : τ ⟨s.1, Finset.mem_of_mem_erase s.2⟩ = M
  · rw [if_pos h]
    have hs : s.1 = (τ⁻¹ M).1 := by
      have h2 : (⟨s.1, Finset.mem_of_mem_erase s.2⟩ : S) = τ⁻¹ M := by
        have h3 : τ ⟨s.1, Finset.mem_of_mem_erase s.2⟩ = τ (τ⁻¹ M) := by
          rw [h]
          exact (Equiv.apply_symm_apply τ M).symm
        exact τ.injective h3
      exact Subtype.mk_eq_mk.mp h2
    rw [hs]
    exact good_of_good_of_good hMprime hq hr (fun hval => hqr (Subtype.ext hval)) hgq hgr
  · rw [if_neg h]
    exact hv ⟨s.1, Finset.mem_of_mem_erase s.2⟩

/-- The deleted permutation stays connected (the "skip `M`" argument). -/
lemma connectedP_delPerm {S : Finset ℕ} {τ : Equiv.Perm S} {M : S}
    {hrM : τ M ≠ M} (hc : ConnectedP τ) :
    ConnectedP (delPerm τ M hrM) := by
  classical
  set del := delPerm τ M hrM with hdeldef
  have seg : ∀ s : (S.erase M), ∀ L : ℕ,
      (∀ j, 1 ≤ j → j < L → τ^[j] ⟨s.1, Finset.mem_of_mem_erase s.2⟩ ≠ M) →
      τ^[L] ⟨s.1, Finset.mem_of_mem_erase s.2⟩ = M →
      ∃ pf, del^[L] s = ⟨(τ M).1, pf⟩ := by
    intro s L hmin hL
    have aux : ∀ m, m < L →
        ∃ pf, del^[m] s = ⟨(τ^[m] ⟨s.1, Finset.mem_of_mem_erase s.2⟩).1, pf⟩ := by
      intro m
      induction m with
      | zero =>
        intro hm
        exact ⟨s.2, rfl⟩
      | succ m ihm =>
        intro hm
        obtain ⟨pf, hpf⟩ := ihm (by omega)
        have hne : τ ⟨(τ^[m] ⟨s.1, Finset.mem_of_mem_erase s.2⟩).1,
            Finset.mem_of_mem_erase pf⟩
            = τ^[m+1] ⟨s.1, Finset.mem_of_mem_erase s.2⟩ := by
          have he : (⟨(τ^[m] ⟨s.1, Finset.mem_of_mem_erase s.2⟩).1,
              Finset.mem_of_mem_erase pf⟩ : S)
              = τ^[m] ⟨s.1, Finset.mem_of_mem_erase s.2⟩ := Subtype.ext rfl
          rw [he]
          exact (Function.iterate_succ_apply' _ _ _).symm
        have hneM : τ^[m+1] ⟨s.1, Finset.mem_of_mem_erase s.2⟩ ≠ M :=
          hmin (m+1) (by omega) hm
        have hmem : (τ^[m+1] ⟨s.1, Finset.mem_of_mem_erase s.2⟩).1 ∈ S.erase M :=
          Finset.mem_erase.mpr ⟨fun hval => hneM (Subtype.ext hval), (τ^[m+1] _).2⟩
        refine ⟨hmem, ?_⟩
        rw [Function.iterate_succ_apply', hpf]
        apply Subtype.ext
        show (del ⟨(τ^[m] ⟨s.1, Finset.mem_of_mem_erase s.2⟩).1, pf⟩).1
          = (τ^[m+1] ⟨s.1, Finset.mem_of_mem_erase s.2⟩).1
        rw [delPerm_val, hne, if_neg hneM]
    have hL0 : L ≠ 0 := by
      rintro rfl
      exact (Finset.mem_erase.mp s.2).1 (Subtype.mk_eq_mk.mp hL)
    obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hL0
    obtain ⟨pf, hpf⟩ := aux l (Nat.lt_succ_self l)
    have hif : τ ⟨(τ^[l] ⟨s.1, Finset.mem_of_mem_erase s.2⟩).1,
        Finset.mem_of_mem_erase pf⟩ = M := by
      have he : (⟨(τ^[l] ⟨s.1, Finset.mem_of_mem_erase s.2⟩).1,
          Finset.mem_of_mem_erase pf⟩ : S) = τ^[l] ⟨s.1, Finset.mem_of_mem_erase s.2⟩ :=
        Subtype.ext rfl
      rw [he, ← Function.iterate_succ_apply' (⇑τ) l ⟨s.1, Finset.mem_of_mem_erase s.2⟩]
      exact hL
    refine ⟨Finset.mem_erase.mpr ⟨fun hval => hrM (Subtype.ext hval), (τ M).2⟩, ?_⟩
    rw [Function.iterate_succ_apply', hpf]
    apply Subtype.ext
    show (del ⟨(τ^[l] ⟨s.1, Finset.mem_of_mem_erase s.2⟩).1, pf⟩).1 = (τ M).1
    rw [delPerm_val, hif, if_pos rfl]
  have P : ∀ T : ℕ, ∀ s t : (S.erase M),
      τ^[T] ⟨s.1, Finset.mem_of_mem_erase s.2⟩
        = ⟨t.1, Finset.mem_of_mem_erase t.2⟩ →
      ∃ m', del^[m'] s = t := by
    intro T
    induction T with
    | zero =>
      intro s t h
      have hst : s = t := Subtype.ext (Subtype.mk_eq_mk.mp h)
      exact ⟨0, hst⟩
    | succ T ihT =>
      intro s t h
      rw [Function.iterate_succ_apply'] at h
      set u := τ^[T] ⟨s.1, Finset.mem_of_mem_erase s.2⟩ with hudef
      by_cases hu : u = M
      · have ht1 : t.1 = (τ M).1 := by
          rw [hu] at h
          exact (Subtype.mk_eq_mk.mp h).symm
        obtain ⟨L, hLmin, hLhit⟩ : ∃ L,
            (∀ j, 1 ≤ j → j < L → τ^[j] ⟨s.1, Finset.mem_of_mem_erase s.2⟩ ≠ M) ∧
            τ^[L] ⟨s.1, Finset.mem_of_mem_erase s.2⟩ = M := by
          obtain ⟨m0, hm0⟩ := hc ⟨s.1, Finset.mem_of_mem_erase s.2⟩ M
          have hex : ∃ m, τ^[m] ⟨s.1, Finset.mem_of_mem_erase s.2⟩ = M := ⟨m0, hm0⟩
          exact ⟨Nat.find hex, fun j _ hj2 => Nat.find_min hex hj2, Nat.find_spec hex⟩
        obtain ⟨pf, hpf⟩ := seg s L hLmin hLhit
        refine ⟨L, ?_⟩
        rw [hpf]
        exact Subtype.ext ht1.symm
      · have huS : u.1 ∈ S.erase M :=
          Finset.mem_erase.mpr ⟨fun hval => hu (Subtype.ext hval), u.2⟩
        obtain ⟨m', hm'⟩ := ihT s ⟨u.1, huS⟩ rfl
        refine ⟨m' + 1, ?_⟩
        rw [Function.iterate_succ_apply', hm']
        have hτ : τ ⟨u.1, Finset.mem_of_mem_erase huS⟩
            = ⟨t.1, Finset.mem_of_mem_erase t.2⟩ := by
          have he : (⟨u.1, Finset.mem_of_mem_erase huS⟩ : S) = u := Subtype.ext rfl
          rw [he]
          exact h
        apply Subtype.ext
        show (del ⟨u.1, huS⟩).1 = t.1
        rw [delPerm_val, hτ,
          if_neg (fun hM => (Finset.mem_erase.mp t.2).1 (Subtype.mk_eq_mk.mp hM))]
  intro s t
  obtain ⟨m0, hm0⟩ := hc ⟨s.1, Finset.mem_of_mem_erase s.2⟩
    ⟨t.1, Finset.mem_of_mem_erase t.2⟩
  exact P m0 s t hm0

/-- If an orbit stays inside a set missing an element, the permutation is not
connected. -/
lemma not_connectedP_of_orbit_subset {S : Finset ℕ} {σ : Equiv.Perm S} (hc : ConnectedP σ)
    {x : S} {T : Finset S} (hT : ∀ m, σ^[m] x ∈ T) {y : S} (hy : y ∉ T) : False := by
  obtain ⟨m, hm⟩ := hc x y
  exact hy (hm ▸ hT m)

/-- Validity passes to the inverse permutation. -/
lemma validPerm_inv {k : ℕ} {S : Finset ℕ} {σ : Equiv.Perm S} (hv : ValidPerm k σ) :
    ValidPerm k σ⁻¹ := by
  intro s
  have h := hv (σ⁻¹ s)
  have h2 : (σ (σ⁻¹ s) : S) = s := Equiv.apply_symm_apply σ s
  rw [h2] at h
  exact good_comm h

/-- Connectivity passes to the inverse permutation. -/
lemma connectedP_inv {S : Finset ℕ} {σ : Equiv.Perm S} (hc : ConnectedP σ) :
    ConnectedP σ⁻¹ := by
  have hiter : ∀ m : ℕ, ∀ s t : S, (⇑(σ⁻¹))^[m] s = t ↔ σ^[m] t = s := by
    intro m
    induction m with
    | zero => intro s t; exact ⟨Eq.symm, Eq.symm⟩
    | succ m ihm =>
      intro s t
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have e1 : (σ⁻¹) ((⇑(σ⁻¹))^[m] s) = t ↔ (⇑(σ⁻¹))^[m] s = σ t := by
        constructor
        · intro h
          have h2 := congrArg σ h
          have h3 : σ (σ⁻¹ ((⇑(σ⁻¹))^[m] s)) = (⇑(σ⁻¹))^[m] s :=
            Equiv.apply_symm_apply _ _
          rw [h3] at h2
          exact h2
        · intro h
          rw [h]
          show (σ⁻¹) (σ t) = t
          exact Equiv.symm_apply_apply _ _
      rw [e1, ihm, ← Function.iterate_succ_apply σ m t,
        ← Function.iterate_succ_apply' σ m t]
  intro s t
  obtain ⟨m, hm⟩ := hc t s
  exact ⟨m, (hiter m s t).mpr hm⟩

/-- A connected permutation on at least two elements has no fixed point. -/
lemma ne_of_connectedP {S : Finset ℕ} {σ : Equiv.Perm S} (hc : ConnectedP σ)
    (h : 2 ≤ #S) (s : S) : σ s ≠ s := by
  intro hfix
  obtain ⟨t, hts⟩ : ∃ t : S, t ≠ s := by
    have hne : (S.erase s.1).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_erase_of_mem s.2]
      omega
    obtain ⟨x, hx⟩ := hne
    exact ⟨⟨x, Finset.mem_of_mem_erase hx⟩,
      fun he => (Finset.mem_erase.mp hx).1 (Subtype.mk_eq_mk.mp he)⟩
  obtain ⟨m, hm⟩ := hc s t
  have hiter : σ^[m] s = s := Function.iterate_fixed hfix m
  rw [hiter] at hm
  exact hts hm.symm

/-- The core uniqueness statement: two valid connected permutations of `S` are
equal or inverse to each other.  Proved by strong induction on `#S`. -/
lemma perm_unique {k : ℕ} (n : ℕ) :
    ∀ (S : Finset ℕ) (_ : #S = n) (_ : 1 ≤ #S) (_ : ∀ p ∈ S, Odd p ∧ Nat.Prime p)
    (σ₁ σ₂ : Equiv.Perm S), ValidPerm k σ₁ → ValidPerm k σ₂ →
    ConnectedP σ₁ → ConnectedP σ₂ → σ₁ = σ₂ ∨ σ₁ = σ₂⁻¹ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hcard hS1 hS2 σ₁ σ₂ hv1 hv2 hc1 hc2
    by_cases h1 : #S = 1
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
      left
      ext x
      have hxs : x = ⟨a, Finset.mem_singleton_self a⟩ :=
        Subtype.ext (Finset.mem_singleton.mp x.2)
      rw [hxs]
      show (σ₁ ⟨a, Finset.mem_singleton_self a⟩).1
        = (σ₂ ⟨a, Finset.mem_singleton_self a⟩).1
      have e1 : (σ₁ ⟨a, Finset.mem_singleton_self a⟩).1 = a :=
        Finset.mem_singleton.mp (σ₁ _).2
      have e2 : (σ₂ ⟨a, Finset.mem_singleton_self a⟩).1 = a :=
        Finset.mem_singleton.mp (σ₂ _).2
      rw [e1, e2]
    by_cases h2 : #S = 2
    · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h2
      have h2S : (2 : ℕ) ≤ #({a, b} : Finset ℕ) := by rw [Finset.card_pair hab]
      have hmem_a : a ∈ ({a, b} : Finset ℕ) := Finset.mem_insert_self a {b}
      have hmem_b : b ∈ ({a, b} : Finset ℕ) :=
        Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
      have val_a : ∀ σ : Equiv.Perm ↥({a, b} : Finset ℕ), ConnectedP σ →
          (σ ⟨a, hmem_a⟩).1 = b := by
        intro σ hc
        have hne : σ ⟨a, hmem_a⟩ ≠ ⟨a, hmem_a⟩ := ne_of_connectedP hc h2S _
        have hmem : (σ ⟨a, hmem_a⟩).1 = a ∨ (σ ⟨a, hmem_a⟩).1 = b := by
          have h2 := (σ ⟨a, hmem_a⟩).2
          simp only [Finset.mem_insert, Finset.mem_singleton] at h2
          exact h2
        rcases hmem with h | h
        · exact absurd (Subtype.ext h) hne
        · exact h
      have val_b : ∀ σ : Equiv.Perm ↥({a, b} : Finset ℕ), ConnectedP σ →
          (σ ⟨b, hmem_b⟩).1 = a := by
        intro σ hc
        have hne : σ ⟨b, hmem_b⟩ ≠ ⟨b, hmem_b⟩ := ne_of_connectedP hc h2S _
        have hmem : (σ ⟨b, hmem_b⟩).1 = a ∨ (σ ⟨b, hmem_b⟩).1 = b := by
          have h2 := (σ ⟨b, hmem_b⟩).2
          simp only [Finset.mem_insert, Finset.mem_singleton] at h2
          exact h2
        rcases hmem with h | h
        · exact h
        · exact absurd (Subtype.ext h) hne
      left
      ext x
      have hx' : x.1 = a ∨ x.1 = b := by
        have h2 := x.2
        simp only [Finset.mem_insert, Finset.mem_singleton] at h2
        exact h2
      rcases hx' with hxa | hxb
      · have hxs : x = ⟨a, hmem_a⟩ := Subtype.ext hxa
        rw [hxs]
        show (σ₁ ⟨a, hmem_a⟩).1 = (σ₂ ⟨a, hmem_a⟩).1
        rw [val_a σ₁ hc1, val_a σ₂ hc2]
      · have hxs : x = ⟨b, hmem_b⟩ := Subtype.ext hxb
        rw [hxs]
        show (σ₁ ⟨b, hmem_b⟩).1 = (σ₂ ⟨b, hmem_b⟩).1
        rw [val_b σ₁ hc1, val_b σ₂ hc2]
    -- #S ≥ 3
    have h3 : 3 ≤ #S := by omega
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    set M := S.max' hne with hMdef
    have hMmem : M ∈ S := S.max'_mem hne
    have hMprime : Nat.Prime M := (hS2 M hMmem).2
    set M' : ↥S := ⟨M, hMmem⟩ with hM'def
    have nbr : ∀ σ : Equiv.Perm S, ConnectedP σ → ValidPerm k σ →
        σ M' ≠ M' ∧ σ⁻¹ M' ≠ M' ∧ σ⁻¹ M' ≠ σ M' ∧
        good k M (σ M').1 ∧ good k M (σ⁻¹ M').1 ∧ (σ M').1 < M ∧ (σ⁻¹ M').1 < M := by
      intro σ hc hv
      have hne1 : σ M' ≠ M' := ne_of_connectedP hc (by omega) M'
      have hne2 : σ⁻¹ M' ≠ M' := by
        intro h
        have h2 : σ (σ⁻¹ M') = M' := Equiv.apply_symm_apply σ M'
        rw [h] at h2
        exact hne1 h2
      have hne3 : σ⁻¹ M' ≠ σ M' := by
        intro h
        have h2 : σ (σ M') = M' := by
          have h3 : σ (σ⁻¹ M') = M' := Equiv.apply_symm_apply σ M'
          rwa [h] at h3
        have horb : ∀ m : ℕ, σ^[m] M' ∈ ({M', σ M'} : Finset ↥S) := by
          intro m
          induction m with
          | zero => simp
          | succ m ihm =>
            rw [Function.iterate_succ_apply']
            simp only [Finset.mem_insert, Finset.mem_singleton] at ihm ⊢
            rcases ihm with h | h
            · rw [h]
              exact Or.inr rfl
            · rw [h]
              exact Or.inl h2
        obtain ⟨y, hy1, hy2⟩ : ∃ y : ↥S, y ≠ M' ∧ y ≠ σ M' := by
          have hne' : ((S.erase M).erase (σ M').1).Nonempty := by
            apply Finset.card_pos.mp
            have h1e : (σ M').1 ∈ S.erase M :=
              Finset.mem_erase.mpr ⟨fun hval => hne1 (Subtype.ext hval), (σ M').2⟩
            rw [Finset.card_erase_of_mem h1e, Finset.card_erase_of_mem hMmem]
            omega
          obtain ⟨x, hx⟩ := hne'
          have hx1 := (Finset.mem_erase.mp hx).1
          have hx2 := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hx)).1
          exact ⟨⟨x, Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)⟩,
            fun he => hx2 (Subtype.mk_eq_mk.mp he), fun he => hx1 (Subtype.mk_eq_mk.mp he)⟩
        exact not_connectedP_of_orbit_subset hc horb
          (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
              exact ⟨hy1, hy2⟩)
      have hg1 : good k M (σ M').1 := hv M'
      have hg2 : good k M (σ⁻¹ M').1 := by
        have h := hv (σ⁻¹ M')
        have h2 : (σ (σ⁻¹ M') : S) = M' := Equiv.apply_symm_apply σ M'
        rw [h2] at h
        exact good_comm h
      have hb1 : (σ M').1 < M :=
        lt_of_le_of_ne (S.le_max' _ (σ M').2) (fun hval => hne1 (Subtype.ext hval))
      have hb2 : (σ⁻¹ M').1 < M :=
        lt_of_le_of_ne (S.le_max' _ (σ⁻¹ M').2) (fun hval => hne2 (Subtype.ext hval))
      exact ⟨hne1, hne2, hne3, hg1, hg2, hb1, hb2⟩
    obtain ⟨hr1, hq1, hqr1, hgr1, hgq1, hbr1, hbq1⟩ := nbr σ₁ hc1 hv1
    obtain ⟨hr2, hq2, hqr2, hgr2, hgq2, hbr2, hbq2⟩ := nbr σ₂ hc2 hv2
    classical
    set F := (S.erase M).filter (good k M ·) with hFdef
    have hF2 : F.card ≤ 2 := by
      apply card_good_le_two hMprime
      intro q hq
      exact lt_of_le_of_ne (S.le_max' _ (Finset.mem_of_mem_erase hq))
        (Finset.mem_erase.mp hq).1
    have hpair : ∀ σ : Equiv.Perm S, σ M' ≠ M' → σ⁻¹ M' ≠ M' → σ⁻¹ M' ≠ σ M' →
        good k M (σ M').1 → good k M (σ⁻¹ M').1 → F = {(σ⁻¹ M').1, (σ M').1} := by
      intro σ h1 h2 h3 hg1 hg2
      have hsub : ({(σ⁻¹ M').1, (σ M').1} : Finset ℕ) ⊆ F := by
        intro x hx
        rw [hFdef, Finset.mem_filter]
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact ⟨Finset.mem_erase.mpr ⟨fun hval => h2 (Subtype.ext hval), (σ⁻¹ M').2⟩, hg2⟩
        · exact ⟨Finset.mem_erase.mpr ⟨fun hval => h1 (Subtype.ext hval), (σ M').2⟩, hg1⟩
      have hle : #F ≤ #({(σ⁻¹ M').1, (σ M').1} : Finset ℕ) := by
        rw [Finset.card_pair (fun hval => h3 (Subtype.ext hval))]
        exact hF2
      exact (Finset.eq_of_subset_of_card_le hsub hle).symm
    have hF1 := hpair σ₁ hr1 hq1 hqr1 hgr1 hgq1
    have hF2' := hpair σ₂ hr2 hq2 hqr2 hgr2 hgq2
    have hset : {(σ₁⁻¹ M').1, (σ₁ M').1} = {(σ₂⁻¹ M').1, (σ₂ M').1} := hF1.symm.trans hF2'
    have aux : ∀ τ₁ τ₂ : Equiv.Perm S, ValidPerm k τ₁ → ValidPerm k τ₂ →
        ConnectedP τ₁ → ConnectedP τ₂ → τ₁ M' = τ₂ M' → τ₁⁻¹ M' = τ₂⁻¹ M' →
        τ₁ = τ₂ ∨ τ₁ = τ₂⁻¹ := by
      intro τ₁ τ₂ hv1 hv2 hc1 hc2 hr hq
      obtain ⟨hrM, hqM, hqr, hgr, hgq, hbr, hbq⟩ := nbr τ₁ hc1 hv1
      set r := τ₁ M' with hrdef
      set q := τ₁⁻¹ M' with hqdef
      by_cases h3' : #S = 3
      · -- #S = 3: the permutation is determined by `M' ↦ r`
        left
        have hMq : M ≠ q.1 := fun h => hqM (Subtype.ext h.symm)
        have hMr : M ≠ r.1 := fun h => hrM (Subtype.ext h.symm)
        have hqr' : q.1 ≠ r.1 := fun h => hqr (Subtype.ext h)
        have hcard3 : #({M, q.1, r.1} : Finset ℕ) = 3 := by
          rw [Finset.card_insert_of_notMem
            (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                exact ⟨hMq, hMr⟩),
            Finset.card_pair hqr']
        have hS3 : S = {M, q.1, r.1} := by
          have hsub : ({M, q.1, r.1} : Finset ℕ) ⊆ S := by
            intro x hx
            rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl
            · exact hMmem
            · exact q.2
            · exact r.2
          exact (Finset.eq_of_subset_of_card_le hsub (by rw [h3', hcard3])).symm
        have hτ1M : τ₁ M' = r := hrdef.symm
        have hτ2M : τ₂ M' = r := hr.symm.trans hrdef.symm
        have hτ1q : τ₁ q = M' := by
          rw [hqdef]
          exact Equiv.apply_symm_apply τ₁ M'
        have hτ2q : τ₂ q = M' := by
          have hq2 : q = τ₂⁻¹ M' := hqdef.trans hq
          rw [hq2]
          exact Equiv.apply_symm_apply τ₂ M'
        have hqrM : ∀ τ : Equiv.Perm S, ConnectedP τ → τ M' = r → τ r = q := by
          intro τ hct hτM
          have hmem : (τ r).1 ∈ ({M, q.1, r.1} : Finset ℕ) := by rw [← hS3]; exact (τ r).2
          rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with h | h | h
          · exfalso
            have h1 : τ r = M' := Subtype.ext h
            have horb : ∀ m : ℕ, τ^[m] M' ∈ ({M', r} : Finset ↥S) := by
              intro m
              induction m with
              | zero => simp
              | succ m ihm =>
                rw [Function.iterate_succ_apply']
                simp only [Finset.mem_insert, Finset.mem_singleton] at ihm ⊢
                rcases ihm with h | h
                · rw [h]
                  exact Or.inr hτM
                · rw [h]
                  exact Or.inl h1
            exact not_connectedP_of_orbit_subset hct horb
              (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                  exact ⟨hqM, hqr⟩)
          · exact Subtype.ext h
          · exfalso
            exact hrM (τ.injective ((Subtype.ext h).trans hτM.symm))
        have hτ1r : τ₁ r = q := hqrM τ₁ hc1 hτ1M
        have hτ2r : τ₂ r = q := hqrM τ₂ hc2 hτ2M
        ext s
        have hsm : s.1 ∈ ({M, q.1, r.1} : Finset ℕ) := by rw [← hS3]; exact s.2
        rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hsm
        rcases hsm with h | h | h
        · have hs : s = M' := Subtype.ext h
          rw [hs, hτ1M, hτ2M]
        · have hs : s = q := Subtype.ext h
          rw [hs, hτ1q, hτ2q]
        · have hs : s = r := Subtype.ext h
          rw [hs, hτ1r, hτ2r]
      · -- #S ≥ 4: delete `M'` and apply the induction hypothesis
        have h4 : 4 ≤ #S := by omega
        have hrM2 : τ₂ M' ≠ M' := by
          rw [← hr]
          exact hrM
        set del₁ := delPerm τ₁ M' hrM with hdel1def
        set del₂ := delPerm τ₂ M' hrM2 with hdel2def
        have hbq2 : (τ₂⁻¹ M').1 < M := by rw [← hq]; exact hbq
        have hbr2 : (τ₂ M').1 < M := by rw [← hr]; exact hbr
        have hqr2 : τ₂⁻¹ M' ≠ τ₂ M' := by rw [← hq, ← hr]; exact hqr
        have hgq2 : good k M (τ₂⁻¹ M').1 := by rw [← hq]; exact hgq
        have hgr2 : good k M (τ₂ M').1 := by rw [← hr]; exact hgr
        have hv1' : ValidPerm k del₁ := validPerm_delPerm hv1 hMprime hbq hbr hqr hgq hgr
        have hv2' : ValidPerm k del₂ := validPerm_delPerm hv2 hMprime hbq2 hbr2 hqr2 hgq2 hgr2
        have hc1' : ConnectedP del₁ := connectedP_delPerm hc1
        have hc2' : ConnectedP del₂ := connectedP_delPerm hc2
        have hcard' : #(S.erase M) = n - 1 := by
          rw [Finset.card_erase_of_mem hMmem, hcard]
        have hS1' : 1 ≤ #(S.erase M) := by rw [hcard']; omega
        have hS2' : ∀ p ∈ S.erase M, Odd p ∧ Nat.Prime p := by
          intro p hp
          exact hS2 p (Finset.mem_of_mem_erase hp)
        rcases ih (n - 1) (by omega) (S.erase M) hcard' hS1' hS2' del₁ del₂
          hv1' hv2' hc1' hc2' with hdel | hdel
        · -- `del₁ = del₂` lifts to `τ₁ = τ₂`
          left
          ext s
          by_cases hsM : s = M'
          · rw [hsM]
            exact congrArg Subtype.val hr
          · have hs1 : s.1 ∈ S.erase M :=
              Finset.mem_erase.mpr ⟨fun hval => hsM (Subtype.ext hval), s.2⟩
            have hvals : (if τ₁ ⟨s.1, Finset.mem_of_mem_erase hs1⟩ = M' then (τ₁ M').1
                else (τ₁ ⟨s.1, Finset.mem_of_mem_erase hs1⟩).1)
              = (if τ₂ ⟨s.1, Finset.mem_of_mem_erase hs1⟩ = M' then (τ₂ M').1
                else (τ₂ ⟨s.1, Finset.mem_of_mem_erase hs1⟩).1) := by
              have hv1s := delPerm_val (τ := τ₁) (M := M') (hrM := hrM) ⟨s.1, hs1⟩
              have hv2s := delPerm_val (τ := τ₂) (M := M') (hrM := hrM2) ⟨s.1, hs1⟩
              have hdel' : delPerm τ₁ M' hrM = delPerm τ₂ M' hrM2 := by
                rw [← hdel1def, ← hdel2def]
                exact hdel
              rw [← hv1s, ← hv2s, hdel']
            have heta : (⟨s.1, Finset.mem_of_mem_erase hs1⟩ : S) = s := Subtype.ext rfl
            by_cases h1 : τ₁ ⟨s.1, Finset.mem_of_mem_erase hs1⟩ = M'
            · by_cases h2 : τ₂ ⟨s.1, Finset.mem_of_mem_erase hs1⟩ = M'
              · have e1 : τ₁ s = M' := by rwa [heta] at h1
                have e2 : τ₂ s = M' := by rwa [heta] at h2
                rw [e1, e2]
              · exfalso
                rw [if_pos h1, if_neg h2] at hvals
                have h2' : (τ₂ ⟨s.1, Finset.mem_of_mem_erase hs1⟩ : S) = τ₁ M' :=
                  Subtype.ext hvals.symm
                have h3'' : (⟨s.1, Finset.mem_of_mem_erase hs1⟩ : S) = M' :=
                  τ₂.injective (h2'.trans hr)
                exact hsM (heta.symm.trans h3'')
            · by_cases h2 : τ₂ ⟨s.1, Finset.mem_of_mem_erase hs1⟩ = M'
              · exfalso
                rw [if_neg h1, if_pos h2] at hvals
                have h1' : (τ₁ ⟨s.1, Finset.mem_of_mem_erase hs1⟩ : S) = τ₂ M' :=
                  Subtype.ext hvals
                have h3'' : (⟨s.1, Finset.mem_of_mem_erase hs1⟩ : S) = M' :=
                  τ₁.injective (h1'.trans hr.symm)
                exact hsM (heta.symm.trans h3'')
              · rw [if_neg h1, if_neg h2] at hvals
                have e : (τ₁ ⟨s.1, Finset.mem_of_mem_erase hs1⟩ : S)
                    = τ₂ ⟨s.1, Finset.mem_of_mem_erase hs1⟩ := Subtype.ext hvals
                rw [heta] at e
                exact congrArg Subtype.val e
        · -- `del₁ = del₂⁻¹` is impossible for `#S ≥ 4`
          exfalso
          have hqS : q.1 ∈ S.erase M :=
            Finset.mem_erase.mpr ⟨fun hval => hqM (Subtype.ext hval), q.2⟩
          have hrS : r.1 ∈ S.erase M :=
            Finset.mem_erase.mpr ⟨fun hval => hrM (Subtype.ext hval), r.2⟩
          have hτ1q : τ₁ q = M' := by
            rw [hqdef]
            exact Equiv.apply_symm_apply τ₁ M'
          have hd1 : del₁ ⟨q.1, hqS⟩ = ⟨r.1, hrS⟩ := by
            apply Subtype.ext
            show (del₁ ⟨q.1, hqS⟩).1 = r.1
            rw [delPerm_val, if_pos _, hrdef]
            have he : (⟨q.1, Finset.mem_of_mem_erase hqS⟩ : S) = q := Subtype.ext rfl
            rw [he]
            exact hτ1q
          have hτ2q : τ₂ q = M' := by
            have hq2 : q = τ₂⁻¹ M' := hqdef.trans hq
            rw [hq2]
            exact Equiv.apply_symm_apply τ₂ M'
          have hpf2 : (τ₂⁻¹ q).1 ∈ S.erase M := by
            apply Finset.mem_erase.mpr
            refine ⟨?_, (τ₂⁻¹ q).2⟩
            intro hval
            have h2 : (τ₂⁻¹ q : S) = M' := Subtype.ext hval
            have h3 : τ₂ (τ₂⁻¹ q) = q := Equiv.apply_symm_apply τ₂ q
            rw [h2] at h3
            exact hqr (h3.symm.trans hr.symm)
          have hd2 : (del₂⁻¹) ⟨q.1, hqS⟩ = ⟨(τ₂⁻¹ q).1, hpf2⟩ := by
            have h : del₂ ⟨(τ₂⁻¹ q).1, hpf2⟩ = ⟨q.1, hqS⟩ := by
              apply Subtype.ext
              show (del₂ ⟨(τ₂⁻¹ q).1, hpf2⟩).1 = q.1
              rw [delPerm_val]
              have hne2 : τ₂ ⟨(τ₂⁻¹ q).1, Finset.mem_of_mem_erase hpf2⟩ ≠ M' := by
                have he : (⟨(τ₂⁻¹ q).1, Finset.mem_of_mem_erase hpf2⟩ : S) = τ₂⁻¹ q :=
                  Subtype.ext rfl
                rw [he]
                intro h2
                have h3 : τ₂ (τ₂⁻¹ q) = q := Equiv.apply_symm_apply τ₂ q
                rw [h2] at h3
                exact hqM h3.symm
              rw [if_neg hne2]
              have he : (⟨(τ₂⁻¹ q).1, Finset.mem_of_mem_erase hpf2⟩ : S) = τ₂⁻¹ q :=
                Subtype.ext rfl
              rw [he]
              show (τ₂ (τ₂⁻¹ q)).1 = q.1
              have h3 : τ₂ (τ₂⁻¹ q) = q := Equiv.apply_symm_apply τ₂ q
              rw [h3]
            exact (Equiv.symm_apply_eq del₂).mpr h.symm
          have hval : (⟨r.1, hrS⟩ : ↥(S.erase M)) = ⟨(τ₂⁻¹ q).1, hpf2⟩ := by
            have h : del₁ ⟨q.1, hqS⟩ = (del₂⁻¹) ⟨q.1, hqS⟩ := by rw [hdel]
            rw [← hd1, h, hd2]
          have hreq : (τ₂⁻¹ q : S) = r := Subtype.ext (congrArg Subtype.val hval).symm
          have hτ2r : τ₂ r = q := by
            have h3 : τ₂ (τ₂⁻¹ q) = q := Equiv.apply_symm_apply τ₂ q
            rw [hreq] at h3
            exact h3
          have hτ2M : τ₂ M' = r := hr.symm.trans hrdef.symm
          have horb : ∀ m : ℕ, τ₂^[m] M' ∈ ({M', r, q} : Finset ↥S) := by
            intro m
            induction m with
            | zero => simp
            | succ m ihm =>
              rw [Function.iterate_succ_apply']
              simp only [Finset.mem_insert, Finset.mem_singleton] at ihm ⊢
              rcases ihm with h | h | h
              · rw [h]
                exact Or.inr (Or.inl hτ2M)
              · rw [h]
                exact Or.inr (Or.inr hτ2r)
              · rw [h]
                exact Or.inl hτ2q
          obtain ⟨y, hy1, hy2, hy3⟩ : ∃ y : ↥S, y ≠ M' ∧ y ≠ r ∧ y ≠ q := by
            have hne' : (((S.erase M).erase r.1).erase q.1).Nonempty := by
              apply Finset.card_pos.mp
              rw [Finset.card_erase_of_mem
                (Finset.mem_erase.mpr ⟨(fun hval => hqr (Subtype.ext hval)), hqS⟩),
                Finset.card_erase_of_mem hrS, Finset.card_erase_of_mem hMmem]
              omega
            obtain ⟨x, hx⟩ := hne'
            have hx1 := (Finset.mem_erase.mp hx).1
            have hx2 := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hx)).1
            have hx3 := (Finset.mem_erase.mp
              (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))).1
            exact ⟨⟨x, Finset.mem_of_mem_erase
                (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))⟩,
              fun he => hx3 (Subtype.mk_eq_mk.mp he),
              fun he => hx2 (Subtype.ext_iff.mp he),
              fun he => hx1 (Subtype.ext_iff.mp he)⟩
          exact not_connectedP_of_orbit_subset hc2 horb
            (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                exact ⟨hy1, hy2, hy3⟩)
    -- orientation
    have hcase : (σ₁ M').1 = (σ₂ M').1 ∨ (σ₁ M').1 = (σ₂⁻¹ M').1 := by
      have hmem : (σ₁ M').1 ∈ ({(σ₂⁻¹ M').1, (σ₂ M').1} : Finset ℕ) := by
        rw [← hset]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      rw [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h
      · exact Or.inr h
      · exact Or.inl h
    rcases hcase with hsame | hflip
    · have hrs : σ₁ M' = σ₂ M' := Subtype.ext hsame
      have hqs : σ₁⁻¹ M' = σ₂⁻¹ M' := by
        apply Subtype.ext
        have hmem : (σ₁⁻¹ M').1 ∈ ({(σ₂⁻¹ M').1, (σ₂ M').1} : Finset ℕ) := by
          rw [← hset]
          exact Finset.mem_insert_self _ _
        rw [Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with h | h
        · exact h
        · exfalso
          exact hqr1 (Subtype.ext (by rw [h, hsame]))
      exact aux σ₁ σ₂ hv1 hv2 hc1 hc2 hrs hqs
    · have hv2i : ValidPerm k σ₂⁻¹ := validPerm_inv hv2
      have hc2i : ConnectedP σ₂⁻¹ := connectedP_inv hc2
      have hrs : σ₁ M' = (σ₂⁻¹) M' := Subtype.ext hflip
      have hqs : σ₁⁻¹ M' = (σ₂⁻¹)⁻¹ M' := by
        rw [inv_inv]
        apply Subtype.ext
        have hmem : (σ₁⁻¹ M').1 ∈ ({(σ₂⁻¹ M').1, (σ₂ M').1} : Finset ℕ) := by
          rw [← hset]
          exact Finset.mem_insert_self _ _
        rw [Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with h | h
        · exfalso
          exact hqr1 (Subtype.ext (by rw [h, ← hflip]))
        · exact h
      rcases aux σ₁ σ₂⁻¹ hv1 hv2i hc1 hc2i hrs hqs with h | h
      · exact Or.inr h
      · rw [inv_inv] at h
        exact Or.inl h

-- snip end

problem imo2023_p3
    {k : ℕ} (hk : 0 < k) (S : Finset ℕ) (hne : S.Nonempty)
    (hS : ∀ p ∈ S, Odd p ∧ Nat.Prime p)
    {p₁ p₂ : Fin #S ≃ S} (hp₁ : Condition k S p₁) (hp₂ : Condition k S p₂) :
    (∃ i, ∀ j, p₂ j = p₁ (j + i)) ∨ ∃ i, ∀ j, p₂ j = p₁ (Fin.rev j + i) := by
  haveI : NeZero #S := ⟨(Finset.card_pos.mpr hne).ne'⟩
  have hp₁' : ∀ j, good k (p₁ j : ℕ) (p₁ (j + 1) : ℕ) := fun j ↦
    let ⟨_, _, h⟩ := hp₁ j; ⟨_, h⟩
  have hp₂' : ∀ j, good k (p₂ j : ℕ) (p₂ (j + 1) : ℕ) := fun j ↦
    let ⟨_, _, h⟩ := hp₂ j; ⟨_, h⟩
  obtain h | h := perm_unique #S S rfl (Finset.card_pos.mpr hne) hS
    (succPerm p₁) (succPerm p₂)
    (validPerm_succPerm hp₁') (validPerm_succPerm hp₂')
    (connectedP_succPerm hne p₁) (connectedP_succPerm hne p₂)
  · exact Or.inl (rot_of_succPerm_eq hne h)
  · exact Or.inr (ref_of_succPerm_eq hne h)

end Imo2022P3
